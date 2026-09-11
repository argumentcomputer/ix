import Ix.Compiler.Pipeline
import Ix.Compiler.LoweredCompilation
import Ix.Compiler.IxIR2.Lower
import Ix.Compiler.Ixon.Hash
import Ix.Compiler.IxIR1.Serialize
import Ix.Compiler.IxIR1.NoReuse

/-!
# Validated pipeline attachment for structured IxIR₂ lowering

This module consumes the proof-facing validated IxIR₁ pipeline result, carries
function-parameter worlds through its final address map, derives baseline
whole-value constructor schemas, and immediately runs the checked IxIR₂
lowerer while retaining its exact producer equation.

IxIR₁ erased exact constructor identities at projections, shallow frees, and
cases. Addressed IxIR₀ mutual-block provenance recovers recursor-case
identities exactly through the final IxIR₁ owner map. Checked HPT summaries
and path-local transfer replay recover exact projection/free identities when
their producers are precise; ambiguous facts still fail closed.
-/

namespace Ix.Compiler.IxIR2.Pipeline

open Ix.Compiler.Ixon (Address Owned)
open Ix.Compiler.IxIR
open Ix.Compiler.IxIR2

inductive Error where
  | pipeline (error : Ix.Compiler.Pipeline.Error)
  | hpt (message : String)
  | parameterArity (producer : Address) (expected actual : Nat)
  | parameterConflict (address : Address)
  | recursorOriginConflict (address : Address)
  | lowering (error : Lower.Error)
  deriving Repr

/-- Constructor information and exact mutual-block membership still present
in the addressed IxIR₀ graph. -/
structure ConstructorInfo where
  identity : CtorId
  arity : Nat
  group : Option Address := none
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

/-- Exact final IxIR₁ owner to addressed IxIR₀ mutual-block origin for a
compiler-produced recursor function. -/
structure RecursorOrigin where
  owner : Address
  group : Address
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

/-- Executable erased-information tables attached to one exact IxIR₁ input. -/
structure Sidecars where
  input : Lower.Input
  parameterEntries : List (Address × Array Owned)
  constructors : List ConstructorInfo
  recursorOrigins : List RecursorOrigin := []
  /-- Checked HPT claims for the exact addressed IxIR₁ graph.  Hand-built
  sidecars default to no interprocedural claims; path-local allocation facts
  remain available without them. -/
  hptCertificate : IxIR1.HPT.Certificate := { artifacts := [] }

private def lookupParameterWorlds
    (entries : List (Address × Array Owned)) (address : Address) :
    Option (Array Owned) :=
  (entries.find? fun entry => entry.1 == address).map (·.2)

private def sourceDeclAt?
    (declarations : List (Address × IxIR0.Decl)) (address : Address) :
    Option IxIR0.Decl :=
  (declarations.find? fun entry => entry.1 == address).map (·.2)

private def parameterWorldsFor
    (source : List (Address × IxIR0.Decl)) (producer : Address)
    (definition : IxIR1.FnDef) : Except Error (Array Owned) := do
  let worlds := match sourceDeclAt? source producer with
    | some (.defn _ body) =>
        (IxIR1.Lower.lamUses body).map IxIR1.Lower.worldOfUses |>.toArray
    | some (.recursor arguments _ _) =>
        Array.replicate (arguments + 1) .shared
    | some (.extern arity) => Array.replicate arity .shared
    | some (.ctor ..) | none => Array.replicate definition.arity .shared
  if worlds.size = definition.arity then
    return worlds
  else
    .error (.parameterArity producer definition.arity worlds.size)

private def insertParameterWorlds
    (entries : List (Address × Array Owned)) (address : Address)
    (worlds : Array Owned) : Except Error (List (Address × Array Owned)) :=
  match entries.find? fun entry => entry.1 == address with
  | none => .ok (entries ++ [(address, worlds)])
  | some entry =>
      if entry.2 == worlds then .ok entries
      else .error (.parameterConflict address)

private def buildParameterWorlds
    (source : List (Address × IxIR0.Decl))
    (raw : List (Address × IxIR1.Decl))
    (addressMap : IxIR1.ReaddressAll.Renaming) :
    Except Error (List (Address × Array Owned)) :=
  raw.foldlM (fun entries entry =>
    match entry.2 with
    | .extern _ => pure entries
    | .fn definition => do
        let worlds ← parameterWorldsFor source entry.1 definition
        let address := IxIR1.Readdress.Renaming.apply addressMap entry.1
        insertParameterWorlds entries address worlds) []

private def sourceGroup?
    (blocks : List IxIR0.MutualBlock.Result) (address : Address) :
    Option Address := do
  let block ← blocks.find? fun block =>
    block.members.any fun member => member.1 == address
  return block.blockAddress

private def constructorInfos
    (source : List (Address × IxIR0.Decl))
    (blocks : List IxIR0.MutualBlock.Result) : List ConstructorInfo :=
  source.filterMap fun
    | (address, .ctor tag arity) =>
        some
          { identity := IxIR1.Lower.ctorIdOf address tag
            arity
            group := sourceGroup? blocks address }
    | _ => none

private def insertRecursorOrigin (origins : List RecursorOrigin)
    (owner group : Address) : Except Error (List RecursorOrigin) :=
  match origins.find? fun origin => origin.owner == owner with
  | none => .ok (origins ++ [{ owner, group }])
  | some origin =>
      if origin.group == group then .ok origins
      else .error (.recursorOriginConflict owner)

/-- Derive exact recursor-owner origins from the addressed IxIR₀ block graph
and the complete raw-to-final IxIR₁ map. Incompatible origins collapsed to
one final owner fail closed. -/
def deriveRecursorOrigins
    (source : List (Address × IxIR0.Decl))
    (blocks : List IxIR0.MutualBlock.Result)
    (raw : List (Address × IxIR1.Decl))
    (addressMap : IxIR1.ReaddressAll.Renaming) :
    Except Error (List RecursorOrigin) :=
  raw.foldlM (fun origins entry =>
    match sourceDeclAt? source entry.1, entry.2,
        sourceGroup? blocks entry.1 with
    | some (.recursor ..), .fn _, some group =>
        let owner := IxIR1.Readdress.Renaming.apply addressMap entry.1
        insertRecursorOrigin origins owner group
    | _, _, _ => pure origins) []

/-- Baseline layouts are content-addressed independently by world and full
constructor identity. No reuse credit is emitted by this lowering, but using
the final representation key now prevents the two ownership worlds from being
accidentally conflated by later passes. -/
def baselineLayout (world : Owned) (identity : CtorId) : LayoutId :=
  Address.blake3
    (ByteArray.mk #[0x63, 0x78, 0x32, 0x6c, 0x61, 0x79, 0x30, 0x00] ++
      Encoding.tag world.toBits ++ identity.bytes)

private def schema? (constructors : List ConstructorInfo)
    (world : Owned) (identity : CtorId) : Option CtorSchema := do
  let info ← constructors.find? fun candidate =>
    candidate.identity == identity
  return { layout := baselineLayout world identity
           fields := Array.replicate info.arity world }

private def ownerCode? (input : Lower.Input) :
    Validate.Owner → Option IxIR1.Code
  | .main => some input.main
  | .declaration address => do
      let entry ← input.declarations.find? fun entry => entry.1 == address
      match entry.2 with
      | .fn definition => some definition.body
      | .extern _ => none

private def terminalCode : IxIR1.Code → IxIR1.Code
  | .letOp _ rest => terminalCode rest
  | code => code

private theorem terminalCode_mapAddresses (rename : Address → Address)
    (code : IxIR1.Code) :
    terminalCode (IxIR1.Readdress.Code.mapAddresses rename code) =
      IxIR1.Readdress.Code.mapAddresses rename (terminalCode code) := by
  cases code with
  | ret atom => rfl
  | letOp operation rest => exact terminalCode_mapAddresses rename rest
  | case scrutinee peelNat alternatives => rfl
termination_by sizeOf code

private def branchCode? : IxIR1.Code → List Nat → Option IxIR1.Code
  | code, [] => some code
  | code, alternative :: rest =>
      match terminalCode code with
      | .case _ _ alternatives => do
          let selected ← alternatives[alternative]?
          match selected with
          | .mk _ _ body => branchCode? body rest
      | _ => none
  termination_by _ branches => branches.length

private theorem branchCode?_mapAddresses (rename : Address → Address)
    (code : IxIR1.Code) (branches : List Nat) :
    branchCode? (IxIR1.Readdress.Code.mapAddresses rename code) branches =
      (branchCode? code branches).map
        (IxIR1.Readdress.Code.mapAddresses rename) := by
  induction branches generalizing code with
  | nil => simp [branchCode?]
  | cons alternative rest ih =>
      simp only [branchCode?]
      rw [terminalCode_mapAddresses]
      cases terminalEq : terminalCode code with
      | ret atom => simp [IxIR1.Readdress.Code.mapAddresses]
      | letOp operation next =>
          simp [IxIR1.Readdress.Code.mapAddresses]
      | case scrutinee peelNat alternatives =>
          simp only [IxIR1.Readdress.Code.mapAddresses]
          have mappedAlternatives :
              (IxIR1.Readdress.AltList.mapAddresses rename
                alternatives.toList).toArray =
                alternatives.map
                  (IxIR1.Readdress.Alt.mapAddresses rename) := by
            apply Array.toList_inj.mp
            simp only [Array.toList_map]
            change IxIR1.Readdress.AltList.mapAddresses rename
                alternatives.toList =
              List.map (IxIR1.Readdress.Alt.mapAddresses rename)
                alternatives.toList
            induction alternatives.toList with
            | nil => rfl
            | cons head tail ih =>
                simp only [IxIR1.Readdress.AltList.mapAddresses,
                  List.map_cons, ih]
          rw [mappedAlternatives, Array.getElem?_map]
          cases selectedEq : alternatives[alternative]? with
          | none => simp
          | some selected =>
              obtain ⟨cidx, fields, body⟩ := selected
              simp [IxIR1.Readdress.Alt.mapAddresses, ih]

/-- Syntax-only branch replay is likewise a fold over its path. -/
private theorem branchCode?_append (code : IxIR1.Code)
    (front back : List Nat) :
    branchCode? code (front ++ back) =
      (branchCode? code front).bind (fun suffix => branchCode? suffix back) := by
  induction front generalizing code with
  | nil =>
      simp only [List.nil_append, branchCode?, Option.bind]
  | cons alternative front ih =>
      simp only [List.cons_append, branchCode?]
      cases terminalEq : terminalCode code with
      | ret atom =>
          simp
      | letOp operation rest =>
          simp
      | case scrutinee peelNat alternatives =>
          cases selectedEq : alternatives[alternative]? with
          | none =>
              simp [selectedEq]
          | some selected =>
              cases selected with
              | mk cidx fields body =>
                  simp [selectedEq, ih]

private def codeAfter? : Nat → IxIR1.Code → Option IxIR1.Code
  | 0, code => some code
  | offset + 1, .letOp _ rest => codeAfter? offset rest
  | _ + 1, _ => none

private theorem codeAfter?_mapAddresses (rename : Address → Address)
    (offset : Nat) (code : IxIR1.Code) :
    codeAfter? offset (IxIR1.Readdress.Code.mapAddresses rename code) =
      (codeAfter? offset code).map
        (IxIR1.Readdress.Code.mapAddresses rename) := by
  induction offset generalizing code with
  | zero => rfl
  | succ offset ih =>
      cases code with
      | ret atom => rfl
      | letOp operation rest => exact ih rest
      | case scrutinee peelNat alternatives => rfl

private def codeAtSite? (input : Lower.Input) (site : Lower.SourceSite) :
    Option IxIR1.Code := do
  let owner ← ownerCode? input site.owner
  let branch ← branchCode? owner site.branches
  codeAfter? site.offset branch

/-- Literal IxIR₁ source suffix named by a lowering coordinate, independent
of HPT success. -/
def Sidecars.sourceCodeAt? (sidecars : Sidecars)
    (site : Lower.SourceSite) : Option IxIR1.Code :=
  codeAtSite? sidecars.input site

private theorem ownerCode?_addressImage (input : Lower.Input)
    (rename : Address → Address)
    (mainImage : ∃ rawMain,
      IxIR1.Readdress.Code.mapAddresses rename rawMain = input.main)
    (declarationImage : ∀ {address definition},
      IxIR1.Env.ofList input.declarations address = some (.fn definition) →
        ∃ rawDefinition,
          IxIR1.Readdress.FnDef.mapAddresses rename rawDefinition =
            definition)
    {owner : Validate.Owner} {code : IxIR1.Code}
    (found : ownerCode? input owner = some code) :
    ∃ rawCode,
      IxIR1.Readdress.Code.mapAddresses rename rawCode = code := by
  cases owner with
  | main =>
      simp only [ownerCode?, Option.some.injEq] at found
      subst code
      exact mainImage
  | declaration address =>
      cases entryEq : input.declarations.find?
          (fun entry => entry.1 == address) with
      | none => simp [ownerCode?, entryEq] at found
      | some entry =>
          cases declarationEq : entry.2 with
          | extern arity => simp [ownerCode?, entryEq, declarationEq] at found
          | fn definition =>
              have lookup : IxIR1.Env.ofList input.declarations address =
                  some (.fn definition) := by
                simp [IxIR1.Env.ofList, entryEq, declarationEq]
              obtain ⟨rawDefinition, definitionImage⟩ :=
                declarationImage lookup
              have codeEq : code = definition.body := by
                simpa [ownerCode?, entryEq, declarationEq] using found.symm
              subst code
              refine ⟨rawDefinition.body, ?_⟩
              have bodyImage := congrArg IxIR1.FnDef.body definitionImage
              simpa [IxIR1.Readdress.FnDef.mapAddresses] using bodyImage

/-- Every literal source suffix recovered from a sidecar remains in the
image of an address action whenever the sidecar's main and selected function
declarations are images. Branch selection and source offsets only select
subterms; neither can manufacture a new declaration identity. -/
theorem Sidecars.sourceCodeAt?_addressImage (sidecars : Sidecars)
    (rename : Address → Address)
    (mainImage : ∃ rawMain,
      IxIR1.Readdress.Code.mapAddresses rename rawMain = sidecars.input.main)
    (declarationImage : ∀ {address definition},
      IxIR1.Env.ofList sidecars.input.declarations address =
          some (.fn definition) →
        ∃ rawDefinition,
          IxIR1.Readdress.FnDef.mapAddresses rename rawDefinition =
            definition)
    {site : Lower.SourceSite} {code : IxIR1.Code}
    (found : sidecars.sourceCodeAt? site = some code) :
    ∃ rawCode,
      IxIR1.Readdress.Code.mapAddresses rename rawCode = code := by
  unfold Sidecars.sourceCodeAt? codeAtSite? at found
  cases ownerEq : ownerCode? sidecars.input site.owner with
  | none => simp [ownerEq] at found
  | some ownerCode =>
      simp only [ownerEq] at found
      cases branchEq : branchCode? ownerCode site.branches with
      | none => simp [branchEq] at found
      | some branchCode =>
          simp [branchEq] at found
          obtain ⟨rawOwner, ownerImage⟩ := ownerCode?_addressImage
            sidecars.input rename mainImage declarationImage ownerEq
          have branchTransport :=
            branchCode?_mapAddresses rename rawOwner site.branches
          rw [ownerImage, branchEq] at branchTransport
          cases rawBranchEq : branchCode? rawOwner site.branches with
          | none => simp [rawBranchEq] at branchTransport
          | some rawBranch =>
              simp only [rawBranchEq, Option.map_some,
                Option.some.injEq] at branchTransport
              have codeTransport :=
                codeAfter?_mapAddresses rename site.offset rawBranch
              rw [← branchTransport, found] at codeTransport
              cases rawCodeEq : codeAfter? site.offset rawBranch with
              | none => simp [rawCodeEq] at codeTransport
              | some rawCode =>
                  simp only [rawCodeEq, Option.map_some,
                    Option.some.injEq] at codeTransport
                  exact ⟨rawCode, codeTransport.symm⟩

private def nextSourceCode? : IxIR1.Code → Option IxIR1.Code
  | .letOp _ rest => some rest
  | _ => none

private theorem codeAfter?_succ (offset : Nat) (code : IxIR1.Code) :
    codeAfter? (offset + 1) code =
      (codeAfter? offset code).bind nextSourceCode? := by
  induction offset generalizing code with
  | zero =>
      cases code <;> rfl
  | succ offset ih =>
      cases code with
      | ret atom => rfl
      | case scrutinee peelNat alternatives => rfl
      | letOp operation rest =>
          exact ih rest

private theorem terminalCode_of_codeAfter_case (offset : Nat)
    (code : IxIR1.Code) (scrutinee : IxIR1.Atom) (peelNat : Bool)
    (alternatives : Array IxIR1.Alt)
    (found : codeAfter? offset code =
      some (.case scrutinee peelNat alternatives)) :
    terminalCode code = .case scrutinee peelNat alternatives := by
  induction offset generalizing code with
  | zero =>
      simp only [codeAfter?] at found
      cases found
      rfl
  | succ offset ih =>
      cases code with
      | ret atom =>
          simp [codeAfter?] at found
      | case scrutinee' peelNat' alternatives' =>
          simp [codeAfter?] at found
      | letOp operation rest =>
          simp only [codeAfter?] at found
          exact ih rest found

/-- Literal source coordinates advance in lockstep with a `letOp` trace. -/
theorem Sidecars.sourceCodeAt?_next (sidecars : Sidecars)
    {site : Lower.SourceSite} {operation : IxIR1.Op} {rest : IxIR1.Code}
    (sourceAt : sidecars.sourceCodeAt? site =
      some (.letOp operation rest)) :
    sidecars.sourceCodeAt? site.next = some rest := by
  unfold Sidecars.sourceCodeAt? codeAtSite? at sourceAt ⊢
  simp only [Lower.SourceSite.next]
  cases ownerEq : ownerCode? sidecars.input site.owner with
  | none =>
      simp [ownerEq] at sourceAt
  | some ownerCode =>
      simp [ownerEq] at sourceAt ⊢
      cases branchEq : branchCode? ownerCode site.branches with
      | none =>
          simp [branchEq] at sourceAt
      | some branchCode =>
          simp [branchEq] at sourceAt ⊢
          rw [codeAfter?_succ]
          cases offsetEq : codeAfter? site.offset branchCode with
          | none =>
              simp [offsetEq] at sourceAt
          | some currentCode =>
              simp [offsetEq] at sourceAt ⊢
              have currentEq : currentCode = .letOp operation rest :=
                sourceAt
              subst currentCode
              rfl

/-- Literal source coordinates select the exact body stored at an appended
case-alternative index. -/
theorem Sidecars.sourceCodeAt?_alternative (sidecars : Sidecars)
    {site : Lower.SourceSite} {scrutinee : IxIR1.Atom} {peelNat : Bool}
    {alternatives : Array IxIR1.Alt} {index cidx fields : Nat}
    {body : IxIR1.Code}
    (sourceAt : sidecars.sourceCodeAt? site =
      some (.case scrutinee peelNat alternatives))
    (selected : alternatives[index]? = some (.mk cidx fields body)) :
    sidecars.sourceCodeAt? (site.alternative index) = some body := by
  unfold Sidecars.sourceCodeAt? codeAtSite? at sourceAt ⊢
  simp only [Lower.SourceSite.alternative]
  cases ownerEq : ownerCode? sidecars.input site.owner with
  | none =>
      simp [ownerEq] at sourceAt
  | some ownerCode =>
      simp [ownerEq] at sourceAt ⊢
      cases branchEq : branchCode? ownerCode site.branches with
      | none =>
          simp [branchEq] at sourceAt
      | some branchCode =>
          simp [branchEq] at sourceAt
          have terminalEq := terminalCode_of_codeAfter_case site.offset
            branchCode scrutinee peelNat alternatives sourceAt
          rw [branchCode?_append, branchEq]
          simp [branchCode?, terminalEq, selected, codeAfter?]

/-! ## Path-local producer facts

`SourceSite` records exactly the branch path and `letOp` offset traversed by
the structured lowerer.  Replay the checked HPT transfer along only that path
to recover the abstract environment at the operation being lowered.  Every
lookup remains partial: invalid coordinates, missing call summaries, and an
HPT error all fail closed. -/

private def mainAnalysisOwner : Address := Address.replicate 0

private structure AnalysisRoot where
  owner : Address
  current : IxIR1.FnDef
  facts : List IxIR1.HPT.Fact
  code : IxIR1.Code

private def analysisRoot? (sidecars : Sidecars) :
    Validate.Owner → Option AnalysisRoot
  | .main =>
      -- A missing synthetic-owner summary makes `callSelf` fail closed and
      -- is the semantic owner-compatibility contract used for source main.
      match sidecars.hptCertificate.summaryEnv mainAnalysisOwner with
      | some _ => none
      | none => some
          { owner := mainAnalysisOwner
            current := sidecars.input.mainDefinition
            facts := []
            code := sidecars.input.main }
  | .declaration address => do
      let entry ← sidecars.input.declarations.find? fun entry =>
        entry.1 == address
      match entry.2 with
      | .extern _ => none
      | .fn current =>
          some
            ({ owner := address
               current
               facts := List.replicate current.arity IxIR1.HPT.Fact.top
               code := current.body } : AnalysisRoot)

/-- The exact source definition used by path-local analysis for one lowering
owner. A missing result is the same fail-closed condition as `siteFacts?`. -/
def Sidecars.analysisCurrent? (sidecars : Sidecars)
    (owner : Validate.Owner) : Option IxIR1.FnDef :=
  (analysisRoot? sidecars owner).map (fun root => root.current)

/-- One retained lowering trace resolves to the exact function definition
used by path-local HPT replay. A missing synthetic-main analysis is permitted
because all of its facts fail closed; a missing declaration analysis is not. -/
def Sidecars.functionTraceSourceMatches (sidecars : Sidecars)
    (trace : Lower.FunctionTrace) : Bool :=
  match sidecars.analysisCurrent? trace.owner with
  | some current => Lower.functionSourceEq current trace.source
  | none => trace.owner == .main

/-- Whole-trace source/HPT owner alignment checked at attachment time. -/
def Sidecars.traceSourcesMatch (sidecars : Sidecars)
    (trace : Lower.Trace) : Bool :=
  trace.functions.all sidecars.functionTraceSourceMatches

/-- Reuse-freedom check over the exact final declaration environment and
every source function retained by the lowering trace.  Checking the emitted
graph closes the content-deduplication gap between the raw compiler theorem
and the universally quantified evaluator context contract. -/
def Sidecars.sourceNoReuse (sidecars : Sidecars)
    (trace : Lower.Trace) : Bool :=
  IxIR1.NoReuse.checkDeclarations sidecars.input.declarations &&
    trace.functions.all fun functionTrace =>
      IxIR1.NoReuse.checkCode functionTrace.source.body

/-! Every constructor allocation retained by the producer must name a
sidecar constructor with the same field arity. This finite executable audit
is the static half of the runtime constructor-universe invariant used by
ambiguous switch coverage. -/

def Sidecars.constructorKnown (sidecars : Sidecars) (identity : CtorId)
    (arity : Nat) : Bool :=
  match sidecars.constructors.find? fun info => info.identity == identity with
  | some info => info.arity == arity
  | none => false

def Sidecars.operationConstructorsKnown (sidecars : Sidecars) :
    IxIR1.Op → Bool
  | .alloc _ identity arguments | .reuse _ identity arguments =>
      sidecars.constructorKnown identity arguments.size
  | _ => true

mutual

def Sidecars.codeConstructorsKnown (sidecars : Sidecars) :
    IxIR1.Code → Bool
  | .ret _ => true
  | .letOp operation rest =>
      sidecars.operationConstructorsKnown operation &&
        sidecars.codeConstructorsKnown rest
  | .case _ _ alternatives =>
      sidecars.alternativesConstructorsKnown alternatives.toList

private def Sidecars.alternativesConstructorsKnown (sidecars : Sidecars) :
    List IxIR1.Alt → Bool
  | [] => true
  | .mk _ _ body :: alternatives =>
      sidecars.codeConstructorsKnown body &&
        sidecars.alternativesConstructorsKnown alternatives

end

private theorem Sidecars.alternativesConstructorsKnown_of_mem
    (sidecars : Sidecars) {alternatives : List IxIR1.Alt}
    {cidx fields : Nat} {body : IxIR1.Code}
    (known : sidecars.alternativesConstructorsKnown alternatives = true)
    (member : (.mk cidx fields body : IxIR1.Alt) ∈ alternatives) :
    sidecars.codeConstructorsKnown body = true := by
  induction alternatives with
  | nil => simp at member
  | cons head tail ih =>
      cases head with
      | mk headTag headFields headBody =>
          simp only [Sidecars.alternativesConstructorsKnown,
            Bool.and_eq_true] at known
          simp only [List.mem_cons] at member
          cases member with
          | inl equal =>
              cases equal
              exact known.1
          | inr member => exact ih known.2 member

/-- A constructor-allocation audit over a case projects to every source
alternative body. -/
theorem Sidecars.codeConstructorsKnown_alternative (sidecars : Sidecars)
    {scrutinee : IxIR1.Atom} {peelNat : Bool}
    {alternatives : Array IxIR1.Alt} {cidx fields : Nat}
    {body : IxIR1.Code}
    (known : sidecars.codeConstructorsKnown
      (.case scrutinee peelNat alternatives) = true)
    (member : (.mk cidx fields body : IxIR1.Alt) ∈ alternatives) :
    sidecars.codeConstructorsKnown body = true := by
  exact sidecars.alternativesConstructorsKnown_of_mem known
    (by simpa using member)

mutual

/-- Constructor-producing operations retained by one recursive lowering trace
all belong to the producer's constructor universe.  This trace-shaped copy of
the source audit makes the fact project directly to any simulated suffix. -/
def Sidecars.codeTraceConstructorsKnown (sidecars : Sidecars) :
    Lower.CodeTrace → Bool
  | .ret .. | .tailCall .. | .tailCallSelf .. => true
  | .letOp _ _ _ _ _ operation _ _ next =>
      sidecars.operationConstructorsKnown operation &&
        sidecars.codeTraceConstructorsKnown next
  | .switchValue _ _ _ _ _ _ _ _ _ _ children =>
      sidecars.codeTraceConstructorListKnown children

private def Sidecars.codeTraceConstructorListKnown (sidecars : Sidecars) :
    List Lower.CodeTrace → Bool
  | [] => true
  | trace :: traces =>
      sidecars.codeTraceConstructorsKnown trace &&
        sidecars.codeTraceConstructorListKnown traces

end

def Sidecars.traceConstructorsKnown (sidecars : Sidecars)
    (trace : Lower.Trace) : Bool :=
  trace.functions.all fun functionTrace =>
    sidecars.codeConstructorsKnown functionTrace.source.body &&
      sidecars.codeTraceConstructorsKnown functionTrace.root

private theorem Sidecars.codeTraceConstructorListKnown_of_mem
    (sidecars : Sidecars) {traces : List Lower.CodeTrace}
    {trace : Lower.CodeTrace}
    (known : sidecars.codeTraceConstructorListKnown traces = true)
    (member : trace ∈ traces) :
    sidecars.codeTraceConstructorsKnown trace = true := by
  induction traces with
  | nil => simp at member
  | cons head tail ih =>
      simp only [Sidecars.codeTraceConstructorListKnown,
        Bool.and_eq_true] at known
      simp only [List.mem_cons] at member
      cases member with
      | inl equal => simpa [equal] using known.1
      | inr member => exact ih known.2 member

/-- The constructor-allocation audit is inherited by an immediate recursive
compiler call. -/
theorem Sidecars.codeTraceConstructorsKnown_of_child (sidecars : Sidecars)
    {parent child : Lower.CodeTrace}
    (known : sidecars.codeTraceConstructorsKnown parent = true)
    (member : child ∈ parent.children) :
    sidecars.codeTraceConstructorsKnown child = true := by
  cases parent with
  | ret _ _ _ _ _ _ _ | tailCall _ _ _ _ _ _ _
  | tailCallSelf _ _ _ _ _ _ =>
      simp [Lower.CodeTrace.children] at member
  | letOp site block input nextInput entryValueCount operation index
      instruction next =>
      simp [Lower.CodeTrace.children] at member
      subst child
      have both : sidecars.operationConstructorsKnown operation = true ∧
          sidecars.codeTraceConstructorsKnown next = true := by
        simpa only [Sidecars.codeTraceConstructorsKnown,
          Bool.and_eq_true] using known
      exact both.2
  | switchValue site block input entryValueCount sourceScrutinee peelNat
      alternatives targetScrutinee generated outgoing children =>
      exact sidecars.codeTraceConstructorListKnown_of_mem known member

/-- The constructor-allocation audit is inherited by every recursive
descendant of a retained compiler derivation. -/
theorem Sidecars.codeTraceConstructorsKnown_descendant (sidecars : Sidecars)
    {root child : Lower.CodeTrace}
    (known : sidecars.codeTraceConstructorsKnown root = true)
    (descendant : root.Descendant child) :
    sidecars.codeTraceConstructorsKnown child = true := by
  induction descendant with
  | refl => exact known
  | @step parent child parentDescendant childMember ih =>
      exact sidecars.codeTraceConstructorsKnown_of_child ih childMember

/-- Local PAP-safety check for the one source operation that can allocate a
partial-application node. Missing and non-function declarations fail closed. -/
private def Sidecars.pappOperationSafe (sidecars : Sidecars) :
    IxIR1.Op → Bool
  | .papp address _ =>
      match IxIR1.Env.ofList sidecars.input.declarations address with
      | some (.fn definition) => definition.papSafe
      | _ => false
  | _ => true

mutual

/-- Recursive PAP-safety check over one retained compiler derivation. -/
def Sidecars.pappSafeTrace (sidecars : Sidecars) : Lower.CodeTrace → Bool
  | .ret .. | .tailCall .. | .tailCallSelf .. => true
  | .letOp _ _ _ _ _ operation _ _ next =>
      sidecars.pappOperationSafe operation && sidecars.pappSafeTrace next
  | .switchValue _ _ _ _ _ _ _ _ _ _ children =>
      sidecars.pappSafeTraces children

/-- Structural list walk beneath switch children. -/
def Sidecars.pappSafeTraces (sidecars : Sidecars) :
    List Lower.CodeTrace → Bool
  | [] => true
  | trace :: rest =>
      sidecars.pappSafeTrace trace && sidecars.pappSafeTraces rest

end

/-- Whole-program PAP-safety check over all retained source derivations. -/
def Sidecars.tracePappsSafe (sidecars : Sidecars)
    (trace : Lower.Trace) : Bool :=
  trace.functions.all fun functionTrace =>
    sidecars.pappSafeTrace functionTrace.root

/-- A successful recursive check exposes the declaration flag required by a
local retained `papp`. -/
theorem Sidecars.pappSafe_of_traceMatch (sidecars : Sidecars)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount index : Nat}
    {address : Address} {arguments : Array IxIR1.Atom}
    {instruction : Instr} {next : Lower.CodeTrace}
    {definition : IxIR1.FnDef}
    (matched : sidecars.pappSafeTrace
      (.letOp site blockId input nextInput entryValueCount
        (.papp address arguments) index instruction next) = true)
    (lookup : IxIR1.Env.ofList sidecars.input.declarations address =
      some (.fn definition)) :
    definition.papSafe = true := by
  simp only [Sidecars.pappSafeTrace, Bool.and_eq_true] at matched
  simpa [Sidecars.pappOperationSafe, lookup] using matched.1

private theorem Sidecars.pappSafeTraces_of_mem (sidecars : Sidecars)
    {traces : List Lower.CodeTrace} {child : Lower.CodeTrace}
    (matched : sidecars.pappSafeTraces traces = true)
    (member : child ∈ traces) :
    sidecars.pappSafeTrace child = true := by
  induction traces with
  | nil => simp at member
  | cons head tail ih =>
      simp only [Sidecars.pappSafeTraces, Bool.and_eq_true] at matched
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact matched.1
      · exact ih matched.2 member

/-- PAP-safety is inherited by every immediate recursive compiler call. -/
theorem Sidecars.pappSafeTrace_of_child (sidecars : Sidecars)
    {parent child : Lower.CodeTrace}
    (matched : sidecars.pappSafeTrace parent = true)
    (member : child ∈ parent.children) :
    sidecars.pappSafeTrace child = true := by
  cases parent with
  | ret _ _ _ _ _ _ _ | tailCall _ _ _ _ _ _ _
  | tailCallSelf _ _ _ _ _ _ =>
      simp [Lower.CodeTrace.children] at member
  | letOp site block input nextInput count operation index instruction next =>
      simp [Lower.CodeTrace.children] at member
      subst child
      simp only [Sidecars.pappSafeTrace, Bool.and_eq_true] at matched
      exact matched.2
  | switchValue site block input count sourceScrutinee peel alternatives
      targetScrutinee generated outgoing children =>
      exact sidecars.pappSafeTraces_of_mem matched member

/-- Every recursive trace descendant inherits the root PAP-safety check. -/
theorem Sidecars.pappSafeTrace_descendant (sidecars : Sidecars)
    {root child : Lower.CodeTrace}
    (descendant : root.Descendant child)
    (matched : sidecars.pappSafeTrace root = true) :
    sidecars.pappSafeTrace child = true := by
  induction descendant with
  | refl => exact matched
  | @step parent child parentDescendant childMember ih =>
      exact sidecars.pappSafeTrace_of_child ih childMember

/-- Reflect whole-trace alignment for one retained function whose analysis
root is present. -/
theorem Sidecars.functionTraceSource_eq_of_match
    (sidecars : Sidecars) {trace : Lower.Trace}
    (matched : sidecars.traceSourcesMatch trace = true)
    {functionTrace : Lower.FunctionTrace}
    (member : functionTrace ∈ trace.functions)
    {current : IxIR1.FnDef}
    (currentAt : sidecars.analysisCurrent? functionTrace.owner =
      some current) :
    current = functionTrace.source := by
  have localMatch := List.all_eq_true.mp matched functionTrace member
  unfold Sidecars.functionTraceSourceMatches at localMatch
  rw [currentAt] at localMatch
  exact (Lower.functionSourceEq_eq_true_iff _ _).mp localMatch

/-- Every recovered analysis root satisfies the owner contract required by
operation soundness: declaration roots name their exact stored definition,
while the synthetic main owner has no summary. -/
private theorem analysisRoot_ownerCompatible (sidecars : Sidecars)
    {owner : Validate.Owner} {root : AnalysisRoot}
    (found : analysisRoot? sidecars owner = some root) :
    IxIR1.HPT.AnalysisOwnerCompatible
      (IxIR1.Env.ofList sidecars.input.declarations)
      sidecars.hptCertificate.summaryEnv root.owner root.current := by
  cases owner with
  | main =>
      cases summaryEq :
          sidecars.hptCertificate.summaryEnv mainAnalysisOwner with
      | none =>
          simp [analysisRoot?, summaryEq] at found
          subst root
          exact Or.inr summaryEq
      | some summary =>
          simp [analysisRoot?, summaryEq] at found
  | declaration address =>
      cases entryEq : sidecars.input.declarations.find?
          (fun entry => entry.1 == address) with
      | none =>
          simp [analysisRoot?, entryEq] at found
      | some entry =>
          cases declarationEq : entry.2 with
          | extern arity =>
              simp [analysisRoot?, entryEq, declarationEq] at found
          | fn current =>
              simp [analysisRoot?, entryEq, declarationEq] at found
              subst root
              exact Or.inl (by
                simp [IxIR1.Env.ofList, entryEq, declarationEq])

/-- Every recoverable analysis root starts from the standard top parameter
environment.  The synthetic main is the zero-arity instance. -/
private theorem analysisRoot_facts (sidecars : Sidecars)
    {owner : Validate.Owner} {root : AnalysisRoot}
    (found : analysisRoot? sidecars owner = some root) :
    root.facts =
      List.replicate root.current.arity IxIR1.HPT.Fact.top := by
  cases owner with
  | main =>
      cases summaryEq :
          sidecars.hptCertificate.summaryEnv mainAnalysisOwner with
      | none =>
          simp [analysisRoot?, summaryEq, Lower.Input.mainDefinition] at found
          subst root
          rfl
      | some summary =>
          simp [analysisRoot?, summaryEq] at found
  | declaration address =>
      cases entryEq : sidecars.input.declarations.find?
          (fun entry => entry.1 == address) with
      | none =>
          simp [analysisRoot?, entryEq] at found
      | some entry =>
          cases declarationEq : entry.2 with
          | extern arity =>
              simp [analysisRoot?, entryEq, declarationEq] at found
          | fn current =>
              simp [analysisRoot?, entryEq, declarationEq] at found
              subst root
              rfl

/-- HPT and syntax-only site replay start from the same owner body. -/
private theorem analysisRoot_sourceCode (sidecars : Sidecars)
    {owner : Validate.Owner} {root : AnalysisRoot}
    (found : analysisRoot? sidecars owner = some root) :
    ownerCode? sidecars.input owner = some root.code := by
  cases owner with
  | main =>
      cases summaryEq :
          sidecars.hptCertificate.summaryEnv mainAnalysisOwner with
      | none =>
          simp [analysisRoot?, summaryEq] at found
          subst root
          rfl
      | some summary =>
          simp [analysisRoot?, summaryEq] at found
  | declaration address =>
      cases entryEq : sidecars.input.declarations.find?
          (fun entry => entry.1 == address) with
      | none =>
          simp [analysisRoot?, entryEq] at found
      | some entry =>
          cases declarationEq : entry.2 with
          | extern arity =>
              simp [analysisRoot?, entryEq, declarationEq] at found
          | fn current =>
              simp [analysisRoot?, entryEq, declarationEq] at found
              subst root
              simp [ownerCode?, entryEq, declarationEq]

/-- The analysis root's retained syntax is exactly its retained definition
body. -/
private theorem analysisRoot_code (sidecars : Sidecars)
    {owner : Validate.Owner} {root : AnalysisRoot}
    (found : analysisRoot? sidecars owner = some root) :
    root.code = root.current.body := by
  cases owner with
  | main =>
      cases summaryEq :
          sidecars.hptCertificate.summaryEnv mainAnalysisOwner with
      | none =>
          simp [analysisRoot?, summaryEq, Lower.Input.mainDefinition] at found
          subst root
          rfl
      | some summary =>
          simp [analysisRoot?, summaryEq] at found
  | declaration address =>
      cases entryEq : sidecars.input.declarations.find?
          (fun entry => entry.1 == address) with
      | none =>
          simp [analysisRoot?, entryEq] at found
      | some entry =>
          cases declarationEq : entry.2 with
          | extern arity =>
              simp [analysisRoot?, entryEq, declarationEq] at found
          | fn current =>
              simp [analysisRoot?, entryEq, declarationEq] at found
              subst root
              rfl

/-- A recoverable function owner names its exact literal source body at the
empty branch path and zero offset. -/
theorem Sidecars.sourceCodeAt?_root (sidecars : Sidecars)
    {owner : Validate.Owner} {current : IxIR1.FnDef}
    (currentAt : sidecars.analysisCurrent? owner = some current) :
    sidecars.sourceCodeAt? ({ owner := owner } : Lower.SourceSite) =
      some current.body := by
  unfold Sidecars.analysisCurrent? at currentAt
  cases rootEq : analysisRoot? sidecars owner with
  | none =>
      simp [rootEq] at currentAt
  | some root =>
      rw [rootEq] at currentAt
      have currentEq : root.current = current := Option.some.inj currentAt
      have rootCode := analysisRoot_sourceCode sidecars rootEq
      have codeEq := analysisRoot_code sidecars rootEq
      unfold Sidecars.sourceCodeAt? codeAtSite?
      simp [rootCode, branchCode?, codeAfter?, codeEq, currentEq]

/-- The synthetic main coordinate always names the literal input main,
independently of whether HPT admits a root for its reserved analysis owner. -/
theorem Sidecars.sourceCodeAt?_main (sidecars : Sidecars) :
    sidecars.sourceCodeAt?
      ({ owner := .main } : Lower.SourceSite) = some sidecars.input.main := by
  simp [Sidecars.sourceCodeAt?, codeAtSite?, ownerCode?, branchCode?,
    codeAfter?]

private def advanceFacts (declarations : IxIR1.HPT.DeclEnv)
    (summaries : IxIR1.HPT.SummaryEnv) (root : AnalysisRoot)
    (facts : List IxIR1.HPT.Fact) (operation : IxIR1.Op) :
    Except String (List IxIR1.HPT.Fact) := do
  let bound ← IxIR1.HPT.analyzeOp declarations summaries root.owner
    root.current facts operation
  return bound :: facts.map IxIR1.HPT.Fact.forgetHeap

private def analyzeToTerminal (declarations : IxIR1.HPT.DeclEnv)
    (summaries : IxIR1.HPT.SummaryEnv) (root : AnalysisRoot) :
    List IxIR1.HPT.Fact → IxIR1.Code →
      Except String (List IxIR1.HPT.Fact × IxIR1.Code)
  | facts, .letOp operation rest => do
      let facts ← advanceFacts declarations summaries root facts operation
      analyzeToTerminal declarations summaries root facts rest
  | facts, code => .ok (facts, code)
  termination_by _ code => sizeOf code

/-- Successful abstract transfer does not alter the literal terminal suffix. -/
private theorem analyzeToTerminal_code
    (declarations : IxIR1.HPT.DeclEnv)
    (summaries : IxIR1.HPT.SummaryEnv) (root : AnalysisRoot)
    (facts : List IxIR1.HPT.Fact) (code : IxIR1.Code)
    (outputFacts : List IxIR1.HPT.Fact) (outputCode : IxIR1.Code)
    (found : analyzeToTerminal declarations summaries root facts code =
      .ok (outputFacts, outputCode)) :
    terminalCode code = outputCode := by
  cases code with
  | ret atom =>
      simp only [analyzeToTerminal] at found
      cases found
      rfl
  | case scrutinee peelNat alternatives =>
      simp only [analyzeToTerminal] at found
      cases found
      rfl
  | letOp operation rest =>
      simp only [analyzeToTerminal] at found
      cases advanced :
          advanceFacts declarations summaries root facts operation with
      | error error =>
          simp [advanced] at found
      | ok nextFacts =>
          rw [advanced] at found
          simp only [bind, Except.bind] at found
          exact analyzeToTerminal_code declarations summaries root nextFacts
            rest outputFacts outputCode found
termination_by sizeOf code

private def selectAlternative (facts : List IxIR1.HPT.Fact)
    (code : IxIR1.Code) (alternative : Nat) :
    Except String (List IxIR1.HPT.Fact × IxIR1.Code) :=
  match code with
  | .case scrutinee peelNat alternatives => do
      let scrutineeFact ← IxIR1.HPT.resolveAtomFact facts scrutinee
      let selected ← match alternatives[alternative]? with
        | some selected => pure selected
        | none => throw "IxIR₂ source-site alternative is absent"
      match selected with
      | .mk cidx fields body =>
          .ok (scrutineeFact.caseFields peelNat cidx fields ++ facts, body)
  | _ => throw "IxIR₂ source-site branch path does not reach a case"

private def enterAlternative (declarations : IxIR1.HPT.DeclEnv)
    (summaries : IxIR1.HPT.SummaryEnv) (root : AnalysisRoot)
    (facts : List IxIR1.HPT.Fact) (code : IxIR1.Code)
    (alternative : Nat) :
    Except String (List IxIR1.HPT.Fact × IxIR1.Code) := do
  let (facts, terminal) ←
    analyzeToTerminal declarations summaries root facts code
  selectAlternative facts terminal alternative

/-- Successful abstract branch entry selects the same literal child body as
syntax-only branch replay. -/
private theorem enterAlternative_code (declarations : IxIR1.HPT.DeclEnv)
    (summaries : IxIR1.HPT.SummaryEnv) (root : AnalysisRoot)
    (facts : List IxIR1.HPT.Fact) (code : IxIR1.Code)
    (alternative : Nat) (outputFacts : List IxIR1.HPT.Fact)
    (outputCode : IxIR1.Code)
    (found : enterAlternative declarations summaries root facts code
      alternative = .ok (outputFacts, outputCode)) :
    branchCode? code [alternative] = some outputCode := by
  unfold enterAlternative at found
  cases terminalEq :
      analyzeToTerminal declarations summaries root facts code with
  | error error =>
      simp [terminalEq] at found
  | ok terminalResult =>
      obtain ⟨terminalFacts, terminal⟩ := terminalResult
      rw [terminalEq] at found
      simp only [bind, Except.bind] at found
      have terminalCodeEq := analyzeToTerminal_code declarations summaries
        root facts code terminalFacts terminal terminalEq
      cases terminal with
      | ret atom =>
          simp [selectAlternative] at found
      | letOp operation rest =>
          simp [selectAlternative] at found
      | case scrutinee peelNat alternatives =>
          cases abstractEq :
              IxIR1.HPT.resolveAtomFact terminalFacts scrutinee with
          | error error =>
              simp [selectAlternative, abstractEq] at found
          | ok scrutineeFact =>
              cases selectedEq : alternatives[alternative]? with
              | none =>
                  simp [selectAlternative, abstractEq, selectedEq] at found
                  change Except.error
                    "IxIR₂ source-site alternative is absent" =
                      Except.ok (outputFacts, outputCode) at found
                  contradiction
              | some selected =>
                  cases selected with
                  | mk cidx fields body =>
                      simp [selectAlternative, abstractEq, selectedEq] at found
                      rw [← found.2]
                      simp [branchCode?, terminalCodeEq, selectedEq]

private def analyzeBranchPath (declarations : IxIR1.HPT.DeclEnv)
    (summaries : IxIR1.HPT.SummaryEnv) (root : AnalysisRoot) :
    List IxIR1.HPT.Fact → IxIR1.Code → List Nat →
      Except String (List IxIR1.HPT.Fact × IxIR1.Code)
  | facts, code, [] => .ok (facts, code)
  | facts, code, alternative :: branches => do
      let (facts, code) ← enterAlternative declarations summaries root facts
        code alternative
      analyzeBranchPath declarations summaries root facts code branches
  termination_by _ _ branches => branches.length

/-- Branch-path replay is a monadic fold over the recorded alternative
indices, so an appended path can be replayed from the prefix result. -/
private theorem analyzeBranchPath_append
    (declarations : IxIR1.HPT.DeclEnv)
    (summaries : IxIR1.HPT.SummaryEnv) (root : AnalysisRoot)
    (facts : List IxIR1.HPT.Fact) (code : IxIR1.Code)
    (front back : List Nat) :
    analyzeBranchPath declarations summaries root facts code
        (front ++ back) =
      (analyzeBranchPath declarations summaries root facts code front).bind
        (fun result => analyzeBranchPath declarations summaries root
          result.1 result.2 back) := by
  induction front generalizing facts code with
  | nil =>
      simp only [List.nil_append, analyzeBranchPath, Except.bind]
  | cons alternative front ih =>
      simp only [List.cons_append, analyzeBranchPath]
      cases entered : enterAlternative declarations summaries root facts code
          alternative with
      | error error => rfl
      | ok result =>
          obtain ⟨nextFacts, nextCode⟩ := result
          simp only [bind, Except.bind]
          exact ih nextFacts nextCode

/-- Successful HPT branch replay retains the exact syntax-only child suffix. -/
private theorem analyzeBranchPath_code
    (declarations : IxIR1.HPT.DeclEnv)
    (summaries : IxIR1.HPT.SummaryEnv) (root : AnalysisRoot)
    (facts : List IxIR1.HPT.Fact) (code : IxIR1.Code)
    (branches : List Nat) (outputFacts : List IxIR1.HPT.Fact)
    (outputCode : IxIR1.Code)
    (found : analyzeBranchPath declarations summaries root facts code
      branches = .ok (outputFacts, outputCode)) :
    branchCode? code branches = some outputCode := by
  induction branches generalizing facts code with
  | nil =>
      simp only [analyzeBranchPath] at found
      cases found
      simp only [branchCode?]
  | cons alternative branches ih =>
      simp only [analyzeBranchPath] at found
      cases entered : enterAlternative declarations summaries root facts code
          alternative with
      | error error =>
          simp [entered] at found
      | ok enteredResult =>
          obtain ⟨nextFacts, nextCode⟩ := enteredResult
          rw [entered] at found
          simp only [bind, Except.bind] at found
          have headCode := enterAlternative_code declarations summaries root
            facts code alternative nextFacts nextCode entered
          have tailCode := ih nextFacts nextCode found
          change branchCode? code ([alternative] ++ branches) = some outputCode
          rw [branchCode?_append, headCode]
          simp only [Option.bind]
          exact tailCode

private def analyzeOffset (declarations : IxIR1.HPT.DeclEnv)
    (summaries : IxIR1.HPT.SummaryEnv) (root : AnalysisRoot) :
    Nat → List IxIR1.HPT.Fact → IxIR1.Code →
      Except String (List IxIR1.HPT.Fact × IxIR1.Code)
  | 0, facts, code => .ok (facts, code)
  | offset + 1, facts, .letOp operation rest => do
      let facts ← advanceFacts declarations summaries root facts operation
      analyzeOffset declarations summaries root offset facts rest
  | _ + 1, _, _ => throw "IxIR₂ source-site offset exceeds its branch"

/-- Successful abstract offset replay retains the exact literal source
suffix selected by syntax-only replay. -/
private theorem analyzeOffset_code (declarations : IxIR1.HPT.DeclEnv)
    (summaries : IxIR1.HPT.SummaryEnv) (root : AnalysisRoot)
    (offset : Nat) (facts : List IxIR1.HPT.Fact) (code : IxIR1.Code)
    (outputFacts : List IxIR1.HPT.Fact) (outputCode : IxIR1.Code)
    (found : analyzeOffset declarations summaries root offset facts code =
      .ok (outputFacts, outputCode)) :
    codeAfter? offset code = some outputCode := by
  induction offset generalizing facts code with
  | zero =>
      simp only [analyzeOffset] at found
      cases found
      rfl
  | succ offset ih =>
      cases code with
      | ret atom =>
          simp [analyzeOffset] at found
      | case scrutinee peelNat alternatives =>
          simp [analyzeOffset] at found
      | letOp operation rest =>
          simp only [analyzeOffset] at found
          cases advanced :
              advanceFacts declarations summaries root facts operation with
          | error error =>
              simp [advanced] at found
          | ok nextFacts =>
              rw [advanced] at found
              simp only [bind, Except.bind] at found
              exact ih nextFacts rest found

/-- A syntactically valid offset splits whole-arm abstract replay at exactly
that suffix, including preservation of any abstract failure before it. -/
private theorem analyzeToTerminal_eq_analyzeOffset_bind
    (declarations : IxIR1.HPT.DeclEnv)
    (summaries : IxIR1.HPT.SummaryEnv) (root : AnalysisRoot)
    (offset : Nat) (facts : List IxIR1.HPT.Fact) (code suffix : IxIR1.Code)
    (codeAt : codeAfter? offset code = some suffix) :
    analyzeToTerminal declarations summaries root facts code =
      (analyzeOffset declarations summaries root offset facts code).bind
        (fun result => analyzeToTerminal declarations summaries root
          result.1 result.2) := by
  induction offset generalizing facts code with
  | zero =>
      simp only [analyzeOffset, Except.bind]
  | succ offset ih =>
      cases code with
      | ret atom =>
          simp [codeAfter?] at codeAt
      | case scrutinee peelNat alternatives =>
          simp [codeAfter?] at codeAt
      | letOp operation rest =>
          simp only [codeAfter?] at codeAt
          simp only [analyzeToTerminal, analyzeOffset]
          cases advanced :
              advanceFacts declarations summaries root facts operation with
          | error error =>
              simp only [bind, Except.bind]
          | ok nextFacts =>
              simp only [bind, Except.bind]
              exact ih nextFacts rest codeAt

/-- If a valid offset lands on a case, advancing the whole arm to its terminal
code produces exactly the same fact environment and case. -/
private theorem analyzeToTerminal_of_analyzeOffset_case
    (declarations : IxIR1.HPT.DeclEnv)
    (summaries : IxIR1.HPT.SummaryEnv) (root : AnalysisRoot)
    (offset : Nat) (facts : List IxIR1.HPT.Fact) (code : IxIR1.Code)
    (currentFacts : List IxIR1.HPT.Fact) (scrutinee : IxIR1.Atom)
    (peelNat : Bool) (alternatives : Array IxIR1.Alt)
    (found : analyzeOffset declarations summaries root offset facts code =
      .ok (currentFacts, .case scrutinee peelNat alternatives)) :
    analyzeToTerminal declarations summaries root facts code =
      .ok (currentFacts, .case scrutinee peelNat alternatives) := by
  induction offset generalizing facts code with
  | zero =>
      simp only [analyzeOffset] at found
      cases found
      simp only [analyzeToTerminal]
  | succ offset ih =>
      cases code with
      | ret atom =>
          simp [analyzeOffset] at found
      | case scrutinee' peelNat' alternatives' =>
          simp [analyzeOffset] at found
      | letOp operation rest =>
          simp only [analyzeOffset] at found
          cases advanced :
              advanceFacts declarations summaries root facts operation with
          | error error =>
              simp [advanced] at found
          | ok nextFacts =>
              rw [advanced] at found
              simp only [bind, Except.bind] at found
              simp only [analyzeToTerminal]
              rw [advanced]
              simp only [bind, Except.bind]
              exact ih nextFacts rest found

private def advanceAnalyzedPair (declarations : IxIR1.HPT.DeclEnv)
    (summaries : IxIR1.HPT.SummaryEnv) (root : AnalysisRoot) :
    List IxIR1.HPT.Fact × IxIR1.Code →
      Except String (List IxIR1.HPT.Fact × IxIR1.Code)
  | (facts, .letOp operation rest) => do
      let facts ← advanceFacts declarations summaries root facts operation
      return (facts, rest)
  | _ => throw "IxIR₂ source-site offset exceeds its branch"

/-- Replaying one additional source offset is exactly one transfer from the
already replayed pair. This is the executable recurrence used by the dynamic
site-environment invariant. -/
private theorem analyzeOffset_succ (declarations : IxIR1.HPT.DeclEnv)
    (summaries : IxIR1.HPT.SummaryEnv) (root : AnalysisRoot)
    (offset : Nat) (facts : List IxIR1.HPT.Fact) (code : IxIR1.Code) :
    analyzeOffset declarations summaries root (offset + 1) facts code =
      (analyzeOffset declarations summaries root offset facts code).bind
        (advanceAnalyzedPair declarations summaries root) := by
  induction offset generalizing facts code with
  | zero =>
      cases code <;> rfl
  | succ offset ih =>
      cases code with
      | ret atom => rfl
      | case scrutinee peelNat alternatives => rfl
      | letOp operation rest =>
          simp only [analyzeOffset]
          cases advanced :
              advanceFacts declarations summaries root facts operation with
          | error error => rfl
          | ok nextFacts =>
              simp only [bind, Except.bind]
              exact ih nextFacts rest

/-- Abstract environment and exact source suffix recovered at one lowering
coordinate by path-local HPT replay. -/
structure SiteFacts where
  facts : List IxIR1.HPT.Fact
  code : IxIR1.Code

/-- Select one case alternative from an already recovered terminal site.
This is the local transfer performed when the compiler changes from `site`
to `site.alternative index`. -/
def SiteFacts.alternative? (analyzed : SiteFacts)
    (index : Nat) : Option SiteFacts :=
  match selectAlternative analyzed.facts analyzed.code index with
  | .ok (facts, code) => some { facts, code }
  | .error _ => none

def Sidecars.siteFacts? (sidecars : Sidecars)
    (site : Lower.SourceSite) : Option SiteFacts := do
  let root ← analysisRoot? sidecars site.owner
  let declarations := IxIR1.Env.ofList sidecars.input.declarations
  let summaries := sidecars.hptCertificate.summaryEnv
  let (branchFacts, branchCode) ←
    match analyzeBranchPath declarations summaries root root.facts root.code
        site.branches with
    | .ok result => some result
    | .error _ => none
  let (facts, code) ←
    match analyzeOffset declarations summaries root site.offset branchFacts
        branchCode with
    | .ok result => some result
    | .error _ => none
  return { facts, code }

/-- Whenever HPT replay succeeds, its retained code is the literal source
suffix named by the same coordinate. -/
theorem Sidecars.siteFacts?_sourceCodeAt (sidecars : Sidecars)
    {site : Lower.SourceSite} {analyzed : SiteFacts}
    (found : sidecars.siteFacts? site = some analyzed) :
    sidecars.sourceCodeAt? site = some analyzed.code := by
  unfold Sidecars.siteFacts? at found
  cases rootEq : analysisRoot? sidecars site.owner with
  | none =>
      simp [rootEq] at found
  | some root =>
      rw [rootEq] at found
      have rootCode := analysisRoot_sourceCode sidecars rootEq
      cases branchEq : analyzeBranchPath
          (IxIR1.Env.ofList sidecars.input.declarations)
          sidecars.hptCertificate.summaryEnv root root.facts root.code
          site.branches with
      | error error =>
          simp [branchEq] at found
      | ok branchResult =>
          obtain ⟨branchFacts, branchCode⟩ := branchResult
          simp [branchEq] at found
          have branchSource := analyzeBranchPath_code
            (IxIR1.Env.ofList sidecars.input.declarations)
            sidecars.hptCertificate.summaryEnv root root.facts root.code
            site.branches branchFacts branchCode branchEq
          cases offsetEq : analyzeOffset
              (IxIR1.Env.ofList sidecars.input.declarations)
              sidecars.hptCertificate.summaryEnv root site.offset branchFacts
              branchCode with
          | error error =>
              simp [offsetEq] at found
          | ok offsetResult =>
              obtain ⟨outputFacts, outputCode⟩ := offsetResult
              simp [offsetEq] at found
              have analyzedEq :
                  ({ facts := outputFacts, code := outputCode } : SiteFacts) =
                    analyzed := found
              subst analyzed
              have offsetSource := analyzeOffset_code
                (IxIR1.Env.ofList sidecars.input.declarations)
                sidecars.hptCertificate.summaryEnv root site.offset branchFacts
                branchCode outputFacts outputCode offsetEq
              unfold Sidecars.sourceCodeAt? codeAtSite?
              simp [rootCode, branchSource, offsetSource]

/-- At a valid terminal case coordinate, appending one branch index to the
source site is exactly local alternative selection from the recovered pair. -/
theorem Sidecars.siteFacts?_alternative (sidecars : Sidecars)
    {site : Lower.SourceSite} {index : Nat} {current : SiteFacts}
    {scrutinee : IxIR1.Atom} {peelNat : Bool}
    {alternatives : Array IxIR1.Alt}
    (currentFound : sidecars.siteFacts? site = some current)
    (codeAt : current.code = .case scrutinee peelNat alternatives) :
    sidecars.siteFacts? (site.alternative index) =
      current.alternative? index := by
  unfold Sidecars.siteFacts? at currentFound ⊢
  simp only [Lower.SourceSite.alternative]
  cases rootEq : analysisRoot? sidecars site.owner with
  | none =>
      simp [rootEq] at currentFound
  | some root =>
      rw [rootEq] at currentFound
      cases branchEq : analyzeBranchPath
          (IxIR1.Env.ofList sidecars.input.declarations)
          sidecars.hptCertificate.summaryEnv root root.facts root.code
          site.branches with
      | error error =>
          simp [branchEq] at currentFound
      | ok branchResult =>
          obtain ⟨branchFacts, branchCode⟩ := branchResult
          simp [branchEq] at currentFound
          cases offsetEq : analyzeOffset
              (IxIR1.Env.ofList sidecars.input.declarations)
              sidecars.hptCertificate.summaryEnv root site.offset branchFacts
              branchCode with
          | error error =>
              simp [offsetEq] at currentFound
          | ok currentResult =>
              obtain ⟨currentFacts, currentCode⟩ := currentResult
              simp [offsetEq] at currentFound
              have currentEq :
                  ({ facts := currentFacts, code := currentCode } : SiteFacts) =
                    current := currentFound
              subst current
              have currentCodeEq : currentCode =
                  .case scrutinee peelNat alternatives := codeAt
              subst currentCode
              have terminalEq := analyzeToTerminal_of_analyzeOffset_case
                (IxIR1.Env.ofList sidecars.input.declarations)
                sidecars.hptCertificate.summaryEnv root site.offset branchFacts
                branchCode currentFacts scrutinee peelNat alternatives offsetEq
              simp only [bind, Option.bind]
              rw [analyzeBranchPath_append, branchEq]
              simp only [Except.bind]
              simp [analyzeBranchPath, enterAlternative, terminalEq,
                analyzeOffset, SiteFacts.alternative?]
              cases selectedEq : selectAlternative currentFacts
                  (.case scrutinee peelNat alternatives) index with
              | error error =>
                  simp
              | ok selected =>
                  obtain ⟨selectedFacts, selectedCode⟩ := selected
                  simp

/-- If replay has failed by a syntactically valid terminal case coordinate,
the appended branch also fails closed.  In particular, branch entry cannot
resurrect facts lost by an earlier abstract transfer. -/
theorem Sidecars.siteFacts?_alternative_eq_none (sidecars : Sidecars)
    {site : Lower.SourceSite} {index : Nat} {scrutinee : IxIR1.Atom}
    {peelNat : Bool} {alternatives : Array IxIR1.Alt}
    (sourceAt : sidecars.sourceCodeAt? site =
      some (.case scrutinee peelNat alternatives))
    (currentNone : sidecars.siteFacts? site = none) :
    sidecars.siteFacts? (site.alternative index) = none := by
  unfold Sidecars.sourceCodeAt? codeAtSite? at sourceAt
  unfold Sidecars.siteFacts? at currentNone ⊢
  simp only [Lower.SourceSite.alternative]
  cases rootEq : analysisRoot? sidecars site.owner with
  | none =>
      simp
  | some root =>
      rw [rootEq] at currentNone
      have rootCode := analysisRoot_sourceCode sidecars rootEq
      simp [rootCode] at sourceAt
      cases branchEq : analyzeBranchPath
          (IxIR1.Env.ofList sidecars.input.declarations)
          sidecars.hptCertificate.summaryEnv root root.facts root.code
          site.branches with
      | error error =>
          simp only [bind, Option.bind]
          rw [analyzeBranchPath_append, branchEq]
          simp only [Except.bind]
      | ok branchResult =>
          obtain ⟨branchFacts, branchCode⟩ := branchResult
          have branchSource := analyzeBranchPath_code
            (IxIR1.Env.ofList sidecars.input.declarations)
            sidecars.hptCertificate.summaryEnv root root.facts root.code
            site.branches branchFacts branchCode branchEq
          rw [branchSource] at sourceAt
          simp only [Option.bind] at sourceAt
          cases offsetEq : analyzeOffset
              (IxIR1.Env.ofList sidecars.input.declarations)
              sidecars.hptCertificate.summaryEnv root site.offset branchFacts
              branchCode with
          | ok currentResult =>
              obtain ⟨currentFacts, currentCode⟩ := currentResult
              simp [branchEq, offsetEq] at currentNone
          | error error =>
              have terminalEq := analyzeToTerminal_eq_analyzeOffset_bind
                (IxIR1.Env.ofList sidecars.input.declarations)
                sidecars.hptCertificate.summaryEnv root site.offset branchFacts
                branchCode (.case scrutinee peelNat alternatives) sourceAt
              rw [offsetEq] at terminalEq
              simp only [Except.bind] at terminalEq
              simp only [bind, Option.bind]
              rw [analyzeBranchPath_append, branchEq]
              simp only [Except.bind]
              simp [analyzeBranchPath, enterAlternative, terminalEq]

/-- At a syntactically valid case coordinate, branch replay is total as a
fail-closed recurrence: either the current query is already `none`, or the
selected local transfer determines the child query. -/
theorem Sidecars.siteFacts?_alternative_of_sourceCodeAt (sidecars : Sidecars)
    {site : Lower.SourceSite} {index : Nat} {scrutinee : IxIR1.Atom}
    {peelNat : Bool} {alternatives : Array IxIR1.Alt}
    (sourceAt : sidecars.sourceCodeAt? site =
      some (.case scrutinee peelNat alternatives)) :
    sidecars.siteFacts? (site.alternative index) =
      (sidecars.siteFacts? site).bind
        (fun current => current.alternative? index) := by
  cases currentEq : sidecars.siteFacts? site with
  | none =>
      rw [sidecars.siteFacts?_alternative_eq_none sourceAt currentEq]
      simp only [Option.bind]
  | some current =>
      have recoveredSource := sidecars.siteFacts?_sourceCodeAt currentEq
      have codeAt : current.code =
          .case scrutinee peelNat alternatives :=
        Option.some.inj (recoveredSource.symm.trans sourceAt)
      rw [sidecars.siteFacts?_alternative currentEq codeAt]
      simp only [Option.bind]

/-- Advance an already recovered site result by one linear source operation.
`none` is the fail-closed state for a terminal suffix, a missing analysis
root, or an abstract transfer error. -/
def Sidecars.advanceSiteFacts? (sidecars : Sidecars)
    (site : Lower.SourceSite) (analyzed : SiteFacts) : Option SiteFacts := do
  let root ← analysisRoot? sidecars site.owner
  let declarations := IxIR1.Env.ofList sidecars.input.declarations
  let summaries := sidecars.hptCertificate.summaryEnv
  let (facts, code) ←
    match advanceAnalyzedPair declarations summaries root
        (analyzed.facts, analyzed.code) with
    | .ok result => some result
    | .error _ => none
  return { facts, code }

/-- Path-local replay commutes with the compiler's linear source coordinate:
querying `site.next` is the same as querying `site` and advancing its recovered
pair once. -/
theorem Sidecars.siteFacts?_next (sidecars : Sidecars)
    (site : Lower.SourceSite) :
    sidecars.siteFacts? site.next =
      (sidecars.siteFacts? site).bind
        (sidecars.advanceSiteFacts? site) := by
  unfold Sidecars.siteFacts? Sidecars.advanceSiteFacts?
  simp only [Lower.SourceSite.next]
  cases rootEq : analysisRoot? sidecars site.owner with
  | none =>
      simp
  | some root =>
      cases branchEq : analyzeBranchPath
          (IxIR1.Env.ofList sidecars.input.declarations)
          sidecars.hptCertificate.summaryEnv root root.facts root.code
          site.branches with
      | error error =>
          simp [branchEq]
      | ok branchResult =>
          obtain ⟨branchFacts, branchCode⟩ := branchResult
          simp [branchEq]
          rw [analyzeOffset_succ]
          cases offsetEq : analyzeOffset
              (IxIR1.Env.ofList sidecars.input.declarations)
              sidecars.hptCertificate.summaryEnv root site.offset branchFacts
              branchCode with
          | error error =>
              simp only [Except.bind]
              simp only [Option.bind]
          | ok offsetResult =>
              obtain ⟨facts, code⟩ := offsetResult
              cases advancedEq : advanceAnalyzedPair
                  (IxIR1.Env.ofList sidecars.input.declarations)
                  sidecars.hptCertificate.summaryEnv root (facts, code) with
              | error error =>
                  simp only [Except.bind, Option.bind]
              | ok advanced =>
                  obtain ⟨nextFacts, nextCode⟩ := advanced
                  simp only [Except.bind, Option.bind]

/-- Concrete interpretation of every recovered fact environment at one
source coordinate. If replay has already failed closed, the predicate is
vacuous and remains so at later linear coordinates. -/
def Sidecars.SiteEnvironmentHolds (sidecars : Sidecars)
    (store : IxIR1.Store) (site : Lower.SourceSite)
    (values : List IxIR1.RVal) : Prop :=
  ∀ analyzed, sidecars.siteFacts? site = some analyzed →
    IxIR1.HPT.EnvironmentHolds
      (IxIR1.Env.ofList sidecars.input.declarations)
      store analyzed.facts values

/-- Any recoverable function root starts with a concrete environment matching
its top parameter facts.  This includes the closed synthetic main. -/
theorem Sidecars.siteEnvironmentHolds_root (sidecars : Sidecars)
    {owner : Validate.Owner} {current : IxIR1.FnDef}
    {store : IxIR1.Store} {values : List IxIR1.RVal}
    (currentAt : sidecars.analysisCurrent? owner = some current)
    (valueCount : values.length = current.arity) :
    sidecars.SiteEnvironmentHolds store
      ({ owner := owner } : Lower.SourceSite) values := by
  intro analyzed siteFound
  unfold Sidecars.analysisCurrent? at currentAt
  cases rootEq : analysisRoot? sidecars owner with
  | none =>
      simp [rootEq] at currentAt
  | some root =>
      rw [rootEq] at currentAt
      have currentEq : root.current = current := Option.some.inj currentAt
      subst current
      unfold Sidecars.siteFacts? at siteFound
      simp [rootEq, analyzeBranchPath, analyzeOffset] at siteFound
      cases siteFound
      rw [analysisRoot_facts sidecars rootEq, ← valueCount]
      exact IxIR1.HPT.EnvironmentHolds.top_replicate
        (IxIR1.Env.ofList sidecars.input.declarations) store values

/-- The closed synthetic main begins with the empty concrete environment.
If its reserved analysis owner collides with a summary, replay fails closed
and the predicate is vacuous. -/
theorem Sidecars.siteEnvironmentHolds_main (sidecars : Sidecars)
    {store : IxIR1.Store} :
    sidecars.SiteEnvironmentHolds store
      ({ owner := .main } : Lower.SourceSite) [] := by
  intro analyzed siteFound
  unfold Sidecars.siteFacts? at siteFound
  cases summaryEq :
      sidecars.hptCertificate.summaryEnv mainAnalysisOwner with
  | none =>
      simp [analysisRoot?, summaryEq, analyzeBranchPath, analyzeOffset]
        at siteFound
      cases siteFound
      exact IxIR1.HPT.EnvironmentHolds.nil
  | some summary =>
      simp [analysisRoot?, summaryEq] at siteFound

/-- Entering a selected constructor alternative prepends the concrete fields
in the evaluator's binder order and preserves the enclosing environment. -/
theorem Sidecars.siteEnvironmentHolds_alternative_ctor_of_siteFacts
    (sidecars : Sidecars)
    {store : IxIR1.Store} {site : Lower.SourceSite}
    {values : List IxIR1.RVal} {current : SiteFacts}
    {scrutinee : IxIR1.Atom} {peelNat : Bool}
    {alternatives : Array IxIR1.Alt} {index cidx fieldCount : Nat}
    {body : IxIR1.Code} {location : Nat} {box : IxIR1.NodeBox}
    {identity : CtorId} {fields : Array IxIR1.RVal}
    (currentFound : sidecars.siteFacts? site = some current)
    (codeAt : current.code = .case scrutinee peelNat alternatives)
    (selected : alternatives[index]? =
      some (.mk cidx fieldCount body))
    (environment : sidecars.SiteEnvironmentHolds store site values)
    (resolved : IxIR1.resolveAtom values scrutinee = .ok (.loc location))
    (sourceGet : store.get? location = some box)
    (node : box.node = .ctorN identity fields)
    (tag : identity.cidx = cidx)
    (fieldCountEq : fields.size = fieldCount) :
    sidecars.SiteEnvironmentHolds store (site.alternative index)
      (fields.toList.reverse ++ values) := by
  intro next nextFound
  rw [sidecars.siteFacts?_alternative currentFound codeAt] at nextFound
  unfold SiteFacts.alternative? at nextFound
  rw [codeAt] at nextFound
  cases abstractEq : IxIR1.HPT.resolveAtomFact current.facts scrutinee with
  | error error =>
      simp [selectAlternative, abstractEq] at nextFound
  | ok scrutineeFact =>
      simp [selectAlternative, abstractEq, selected] at nextFound
      cases nextFound
      have currentEnvironment := environment current currentFound
      have scrutineeHolds := IxIR1.HPT.resolveAtom_sound currentEnvironment
        abstractEq resolved
      exact
        (IxIR1.HPT.Fact.caseFields_ctor_holds peelNat cidx fieldCount
          scrutineeHolds sourceGet node tag fieldCountEq).append
          currentEnvironment

/-- The selected zero Nat alternative has no new binders, so its recovered
environment is exactly the enclosing one. -/
theorem Sidecars.siteEnvironmentHolds_alternative_natZero_of_siteFacts
    (sidecars : Sidecars)
    {store : IxIR1.Store} {site : Lower.SourceSite}
    {values : List IxIR1.RVal} {current : SiteFacts}
    {scrutinee : IxIR1.Atom} {alternatives : Array IxIR1.Alt}
    {index : Nat} {body : IxIR1.Code}
    (currentFound : sidecars.siteFacts? site = some current)
    (codeAt : current.code = .case scrutinee true alternatives)
    (selected : alternatives[index]? = some (.mk 0 0 body))
    (environment : sidecars.SiteEnvironmentHolds store site values) :
    sidecars.SiteEnvironmentHolds store (site.alternative index) values := by
  intro next nextFound
  rw [sidecars.siteFacts?_alternative currentFound codeAt] at nextFound
  unfold SiteFacts.alternative? at nextFound
  rw [codeAt] at nextFound
  cases abstractEq : IxIR1.HPT.resolveAtomFact current.facts scrutinee with
  | error error =>
      simp [selectAlternative, abstractEq] at nextFound
  | ok scrutineeFact =>
      simp [selectAlternative, abstractEq, selected] at nextFound
      cases nextFound
      have currentEnvironment := environment current currentFound
      have binders : IxIR1.HPT.EnvironmentHolds
          (IxIR1.Env.ofList sidecars.input.declarations) store
          (scrutineeFact.caseFields true 0 0) [] := by
        simpa [IxIR1.HPT.Fact.caseFields,
          IxIR1.HPT.Fact.joinFieldVectors] using
          (IxIR1.HPT.EnvironmentHolds.nil :
            IxIR1.HPT.EnvironmentHolds
              (IxIR1.Env.ofList sidecars.input.declarations) store [] [])
      exact binders.append currentEnvironment

/-- The selected successor Nat alternative prepends the exact predecessor
fact and value before the enclosing environment. -/
theorem Sidecars.siteEnvironmentHolds_alternative_natSucc_of_siteFacts
    (sidecars : Sidecars)
    {store : IxIR1.Store} {site : Lower.SourceSite}
    {values : List IxIR1.RVal} {current : SiteFacts}
    {scrutinee : IxIR1.Atom} {alternatives : Array IxIR1.Alt}
    {index predecessor : Nat} {body : IxIR1.Code}
    (currentFound : sidecars.siteFacts? site = some current)
    (codeAt : current.code = .case scrutinee true alternatives)
    (selected : alternatives[index]? = some (.mk 1 1 body))
    (environment : sidecars.SiteEnvironmentHolds store site values)
    (resolved : IxIR1.resolveAtom values scrutinee =
      .ok (.lit (.nat (predecessor + 1)))) :
    sidecars.SiteEnvironmentHolds store (site.alternative index)
      (.lit (.nat predecessor) :: values) := by
  intro next nextFound
  rw [sidecars.siteFacts?_alternative currentFound codeAt] at nextFound
  unfold SiteFacts.alternative? at nextFound
  rw [codeAt] at nextFound
  cases abstractEq : IxIR1.HPT.resolveAtomFact current.facts scrutinee with
  | error error =>
      simp [selectAlternative, abstractEq] at nextFound
  | ok scrutineeFact =>
      simp [selectAlternative, abstractEq, selected] at nextFound
      cases nextFound
      have currentEnvironment := environment current currentFound
      have scrutineeHolds := IxIR1.HPT.resolveAtom_sound currentEnvironment
        abstractEq resolved
      exact
        (IxIR1.HPT.Fact.caseFields_natSucc_holds scrutineeHolds).append
          currentEnvironment

/-- Source-facing constructor branch transport. Earlier HPT failure is
preserved as `none`; otherwise the concrete field vector satisfies the
selected branch facts. -/
theorem Sidecars.siteEnvironmentHolds_alternative_ctor (sidecars : Sidecars)
    {store : IxIR1.Store} {site : Lower.SourceSite}
    {values : List IxIR1.RVal} {scrutinee : IxIR1.Atom}
    {peelNat : Bool} {alternatives : Array IxIR1.Alt}
    {index cidx fieldCount : Nat} {body : IxIR1.Code}
    {location : Nat} {box : IxIR1.NodeBox} {identity : CtorId}
    {fields : Array IxIR1.RVal}
    (sourceAt : sidecars.sourceCodeAt? site =
      some (.case scrutinee peelNat alternatives))
    (selected : alternatives[index]? =
      some (.mk cidx fieldCount body))
    (environment : sidecars.SiteEnvironmentHolds store site values)
    (resolved : IxIR1.resolveAtom values scrutinee = .ok (.loc location))
    (sourceGet : store.get? location = some box)
    (node : box.node = .ctorN identity fields)
    (tag : identity.cidx = cidx)
    (fieldCountEq : fields.size = fieldCount) :
    sidecars.SiteEnvironmentHolds store (site.alternative index)
      (fields.toList.reverse ++ values) := by
  cases currentEq : sidecars.siteFacts? site with
  | none =>
      intro next nextFound
      rw [sidecars.siteFacts?_alternative_eq_none sourceAt currentEq]
        at nextFound
      contradiction
  | some current =>
      have recoveredSource := sidecars.siteFacts?_sourceCodeAt currentEq
      have codeAt : current.code =
          .case scrutinee peelNat alternatives :=
        Option.some.inj (recoveredSource.symm.trans sourceAt)
      exact sidecars.siteEnvironmentHolds_alternative_ctor_of_siteFacts
        currentEq codeAt selected environment resolved sourceGet node tag
        fieldCountEq

/-- Source-facing zero Nat branch transport, including the fail-closed HPT
case. -/
theorem Sidecars.siteEnvironmentHolds_alternative_natZero
    (sidecars : Sidecars)
    {store : IxIR1.Store} {site : Lower.SourceSite}
    {values : List IxIR1.RVal} {scrutinee : IxIR1.Atom}
    {alternatives : Array IxIR1.Alt} {index : Nat} {body : IxIR1.Code}
    (sourceAt : sidecars.sourceCodeAt? site =
      some (.case scrutinee true alternatives))
    (selected : alternatives[index]? = some (.mk 0 0 body))
    (environment : sidecars.SiteEnvironmentHolds store site values) :
    sidecars.SiteEnvironmentHolds store (site.alternative index) values := by
  cases currentEq : sidecars.siteFacts? site with
  | none =>
      intro next nextFound
      rw [sidecars.siteFacts?_alternative_eq_none sourceAt currentEq]
        at nextFound
      contradiction
  | some current =>
      have recoveredSource := sidecars.siteFacts?_sourceCodeAt currentEq
      have codeAt : current.code = .case scrutinee true alternatives :=
        Option.some.inj (recoveredSource.symm.trans sourceAt)
      exact sidecars.siteEnvironmentHolds_alternative_natZero_of_siteFacts
        currentEq codeAt selected environment

/-- Source-facing successor Nat branch transport, including the fail-closed
HPT case. -/
theorem Sidecars.siteEnvironmentHolds_alternative_natSucc
    (sidecars : Sidecars)
    {store : IxIR1.Store} {site : Lower.SourceSite}
    {values : List IxIR1.RVal} {scrutinee : IxIR1.Atom}
    {alternatives : Array IxIR1.Alt} {index predecessor : Nat}
    {body : IxIR1.Code}
    (sourceAt : sidecars.sourceCodeAt? site =
      some (.case scrutinee true alternatives))
    (selected : alternatives[index]? = some (.mk 1 1 body))
    (environment : sidecars.SiteEnvironmentHolds store site values)
    (resolved : IxIR1.resolveAtom values scrutinee =
      .ok (.lit (.nat (predecessor + 1)))) :
    sidecars.SiteEnvironmentHolds store (site.alternative index)
      (.lit (.nat predecessor) :: values) := by
  cases currentEq : sidecars.siteFacts? site with
  | none =>
      intro next nextFound
      rw [sidecars.siteFacts?_alternative_eq_none sourceAt currentEq]
        at nextFound
      contradiction
  | some current =>
      have recoveredSource := sidecars.siteFacts?_sourceCodeAt currentEq
      have codeAt : current.code = .case scrutinee true alternatives :=
        Option.some.inj (recoveredSource.symm.trans sourceAt)
      exact sidecars.siteEnvironmentHolds_alternative_natSucc_of_siteFacts
        currentEq codeAt selected environment resolved

/-- One successful concrete source operation transports the recovered HPT
environment to `site.next`. Abstract failure remains `none`; abstract success
uses operation soundness for the new head fact and forgets heap detail from
the preserved tail. -/
theorem Sidecars.siteEnvironmentHolds_next (sidecars : Sidecars)
    {sourceContext : IxIR1.Ctx} {sourceCurrent : IxIR1.FnDef}
    {sourceFuel : Nat} {sourceStore outputStore : IxIR1.Store}
    {source : List IxIR1.RVal} {operation : IxIR1.Op}
    {value : IxIR1.RVal} {site : Lower.SourceSite} {rest : IxIR1.Code}
    (postFixpoint : IxIR1.HPT.LocalPostFixpoint
      (IxIR1.Env.ofList sidecars.input.declarations)
      sidecars.hptCertificate.summaryEnv)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.Env.ofList sidecars.input.declarations)
    (currentAt : sidecars.analysisCurrent? site.owner = some sourceCurrent)
    (environment : sidecars.SiteEnvironmentHolds sourceStore site source)
    (sourceAt : sidecars.sourceCodeAt? site =
      some (.letOp operation rest))
    (sourceRun : IxIR1.runOp sourceContext sourceFuel sourceCurrent
      sourceStore source operation = .ok (outputStore, value)) :
    sidecars.SiteEnvironmentHolds outputStore site.next (value :: source) := by
  intro nextAnalyzed nextFound
  rw [sidecars.siteFacts?_next] at nextFound
  cases currentEq : sidecars.siteFacts? site with
  | none =>
      rw [currentEq] at nextFound
      contradiction
  | some current =>
      have currentEnvironment := environment current currentEq
      have recoveredSource := sidecars.siteFacts?_sourceCodeAt currentEq
      have codeEq : current.code = .letOp operation rest :=
        Option.some.inj (recoveredSource.symm.trans sourceAt)
      rw [currentEq] at nextFound
      simp only [Option.bind] at nextFound
      unfold Sidecars.advanceSiteFacts? at nextFound
      cases rootEq : analysisRoot? sidecars site.owner with
      | none =>
          simp [rootEq] at nextFound
      | some root =>
          have currentRoot : root.current = sourceCurrent := by
            unfold Sidecars.analysisCurrent? at currentAt
            rw [rootEq] at currentAt
            exact Option.some.inj currentAt
          subst sourceCurrent
          have ownerCompatible := analysisRoot_ownerCompatible sidecars rootEq
          rw [codeEq] at nextFound
          cases abstractEq : IxIR1.HPT.analyzeOp
              (IxIR1.Env.ofList sidecars.input.declarations)
              sidecars.hptCertificate.summaryEnv root.owner root.current
              current.facts operation with
          | error error =>
              simp [rootEq, advanceAnalyzedPair, advanceFacts, abstractEq]
                at nextFound
              change none = some nextAnalyzed at nextFound
              contradiction
          | ok bound =>
              simp [rootEq, advanceAnalyzedPair, advanceFacts, abstractEq]
                at nextFound
              change some
                ({
                  facts := bound ::
                    current.facts.map IxIR1.HPT.Fact.forgetHeap
                  code := rest
                } : SiteFacts) = some nextAnalyzed at nextFound
              cases nextFound
              exact IxIR1.HPT.EnvironmentHolds.cons
                (IxIR1.HPT.analyzeOp_sound_ownerCompatible postFixpoint
                  sourceDeclarations ownerCompatible currentEnvironment
                  abstractEq sourceRun)
                currentEnvironment.forgetHeap

/-- Linear transport only needs the concrete evaluator's current function to
agree when path-local analysis actually has a root. If analysis fails closed
for the owner, every site predicate is vacuous and remains so at `site.next`.
This form covers the synthetic main even when its reserved analysis address
collides with a declaration summary. -/
theorem Sidecars.siteEnvironmentHolds_next_of_currentCompatible
    (sidecars : Sidecars)
    {sourceContext : IxIR1.Ctx} {sourceCurrent : IxIR1.FnDef}
    {sourceFuel : Nat} {sourceStore outputStore : IxIR1.Store}
    {source : List IxIR1.RVal} {operation : IxIR1.Op}
    {value : IxIR1.RVal} {site : Lower.SourceSite} {rest : IxIR1.Code}
    (postFixpoint : IxIR1.HPT.LocalPostFixpoint
      (IxIR1.Env.ofList sidecars.input.declarations)
      sidecars.hptCertificate.summaryEnv)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.Env.ofList sidecars.input.declarations)
    (currentCompatible : ∀ current,
      sidecars.analysisCurrent? site.owner = some current →
        current = sourceCurrent)
    (environment : sidecars.SiteEnvironmentHolds sourceStore site source)
    (sourceAt : sidecars.sourceCodeAt? site =
      some (.letOp operation rest))
    (sourceRun : IxIR1.runOp sourceContext sourceFuel sourceCurrent
      sourceStore source operation = .ok (outputStore, value)) :
    sidecars.SiteEnvironmentHolds outputStore site.next
      (value :: source) := by
  cases currentEq : sidecars.analysisCurrent? site.owner with
  | some current =>
      have currentMatches := currentCompatible current currentEq
      subst current
      exact sidecars.siteEnvironmentHolds_next postFixpoint
        sourceDeclarations currentEq environment sourceAt sourceRun
  | none =>
      intro analyzed nextFound
      unfold Sidecars.analysisCurrent? at currentEq
      cases rootEq : analysisRoot? sidecars site.owner with
      | none =>
          unfold Sidecars.siteFacts? at nextFound
          simp [Lower.SourceSite.next, rootEq] at nextFound
      | some root =>
          rw [rootEq] at currentEq
          simp at currentEq

/-- Resolve one source operand in the recovered site environment and retain it
only when the abstract value has one exact constructor identity. -/
def Sidecars.exactConstructorAt? (sidecars : Sidecars)
    (site : Lower.SourceSite) (atom : IxIR1.Atom) :
    Option (IxIR1.HPT.Fact × CtorId) := do
  let analyzed ← sidecars.siteFacts? site
  let fact ← match IxIR1.HPT.resolveAtomFact analyzed.facts atom with
    | .ok fact => some fact
    | .error _ => none
  let identity ← fact.exactConstructor?
  return (fact, identity)

/-- Successful exact-constructor extraction exposes every checked executable
premise needed to connect the chosen identity to HPT soundness. -/
theorem Sidecars.exactConstructorAt?_eq_some (sidecars : Sidecars)
    {site : Lower.SourceSite} {atom : IxIR1.Atom}
    {fact : IxIR1.HPT.Fact} {identity : CtorId}
    (found : sidecars.exactConstructorAt? site atom = some (fact, identity)) :
    ∃ analyzed,
      sidecars.siteFacts? site = some analyzed ∧
        IxIR1.HPT.resolveAtomFact analyzed.facts atom = .ok fact ∧
        fact.exactConstructor? = some identity := by
  cases analyzedEq : sidecars.siteFacts? site with
  | none =>
      simp [Sidecars.exactConstructorAt?, analyzedEq] at found
  | some analyzed =>
      cases resolvedEq : IxIR1.HPT.resolveAtomFact analyzed.facts atom with
      | error error =>
          simp [Sidecars.exactConstructorAt?, analyzedEq, resolvedEq] at found
      | ok resolved =>
          cases exactEq : resolved.exactConstructor? with
          | none =>
              simp [Sidecars.exactConstructorAt?, analyzedEq, resolvedEq,
                exactEq] at found
          | some resolvedIdentity =>
              simp [Sidecars.exactConstructorAt?, analyzedEq, resolvedEq,
                exactEq] at found
              rcases found with ⟨rfl, rfl⟩
              exact ⟨analyzed, rfl, resolvedEq, exactEq⟩

/-- An exact constructor selected by a source-site sidecar is the constructor
stored at the concrete operand location whenever the replayed abstract
environment describes the current source environment. -/
theorem Sidecars.exactConstructorAt?_runtime (sidecars : Sidecars)
    {site : Lower.SourceSite} {atom : IxIR1.Atom}
    {fact : IxIR1.HPT.Fact} {identity : CtorId}
    {declarations : IxIR1.HPT.DeclEnv} {store : IxIR1.Store}
    {values : List IxIR1.RVal} {location : Nat}
    (found : sidecars.exactConstructorAt? site atom = some (fact, identity))
    (environment : ∀ analyzed,
      sidecars.siteFacts? site = some analyzed →
        IxIR1.HPT.EnvironmentHolds declarations store analyzed.facts values)
    (resolved : IxIR1.resolveAtom values atom = .ok (.loc location)) :
    ∃ box fields,
      store.get? location = some box ∧
        box.node = .ctorN identity fields := by
  obtain ⟨analyzed, siteFound, abstractResolved, exact⟩ :=
    sidecars.exactConstructorAt?_eq_some found
  have factHolds := IxIR1.HPT.resolveAtom_sound
    (environment analyzed siteFound) abstractResolved resolved
  exact IxIR1.HPT.Fact.exactConstructor?_holds_loc exact factHolds

/-- The constructor identity carried by any concrete node reached by the
selected operand agrees with the exact identity chosen by the sidecar. -/
theorem Sidecars.exactConstructorAt?_matches_node (sidecars : Sidecars)
    {site : Lower.SourceSite} {atom : IxIR1.Atom}
    {fact : IxIR1.HPT.Fact} {identity runtimeIdentity : CtorId}
    {declarations : IxIR1.HPT.DeclEnv} {store : IxIR1.Store}
    {values : List IxIR1.RVal} {location : Nat}
    {box : IxIR1.NodeBox} {fields : Array IxIR1.RVal}
    (found : sidecars.exactConstructorAt? site atom = some (fact, identity))
    (environment : ∀ analyzed,
      sidecars.siteFacts? site = some analyzed →
        IxIR1.HPT.EnvironmentHolds declarations store analyzed.facts values)
    (resolved : IxIR1.resolveAtom values atom = .ok (.loc location))
    (sourceGet : store.get? location = some box)
    (node : box.node = .ctorN runtimeIdentity fields) :
    runtimeIdentity = identity := by
  obtain ⟨exactBox, exactFields, exactGet, exactNode⟩ :=
    sidecars.exactConstructorAt?_runtime found environment resolved
  have boxEq : exactBox = box :=
    Option.some.inj (exactGet.symm.trans sourceGet)
  subst exactBox
  rw [node] at exactNode
  injection exactNode

/-- Resolve one source operand in the recovered site environment and retain it
only when HPT describes one exact constructor whose complete field vector is
scalar.  Unlike `exactConstructorAt?`, this is strong enough to justify the
target evaluator's shallow-free side condition. -/
def Sidecars.scalarLeafAt? (sidecars : Sidecars)
    (site : Lower.SourceSite) (atom : IxIR1.Atom) :
    Option (IxIR1.HPT.Fact × CtorId) := do
  let analyzed ← sidecars.siteFacts? site
  let fact ← match IxIR1.HPT.resolveAtomFact analyzed.facts atom with
    | .ok fact => some fact
    | .error _ => none
  let leaf ← IxIR1.HPT.Destroy.exactLeaf? fact
  return (fact, leaf.identity)

/-- Successful scalar-leaf extraction exposes the checked HPT premises used
by its concrete soundness theorem. -/
theorem Sidecars.scalarLeafAt?_eq_some (sidecars : Sidecars)
    {site : Lower.SourceSite} {atom : IxIR1.Atom}
    {fact : IxIR1.HPT.Fact} {identity : CtorId}
    (found : sidecars.scalarLeafAt? site atom = some (fact, identity)) :
    ∃ analyzed leaf,
      sidecars.siteFacts? site = some analyzed ∧
        IxIR1.HPT.resolveAtomFact analyzed.facts atom = .ok fact ∧
        IxIR1.HPT.Destroy.exactLeaf? fact = some leaf ∧
        leaf.identity = identity := by
  cases analyzedEq : sidecars.siteFacts? site with
  | none =>
      simp [Sidecars.scalarLeafAt?, analyzedEq] at found
  | some analyzed =>
      cases resolvedEq : IxIR1.HPT.resolveAtomFact analyzed.facts atom with
      | error error =>
          simp [Sidecars.scalarLeafAt?, analyzedEq, resolvedEq] at found
      | ok resolved =>
          cases leafEq : IxIR1.HPT.Destroy.exactLeaf? resolved with
          | none =>
              simp [Sidecars.scalarLeafAt?, analyzedEq, resolvedEq,
                leafEq] at found
          | some leaf =>
              simp [Sidecars.scalarLeafAt?, analyzedEq, resolvedEq,
                leafEq] at found
              rcases found with ⟨rfl, rfl⟩
              exact ⟨analyzed, leaf, rfl, resolvedEq, leafEq, rfl⟩

/-- A scalar leaf selected by a source-site sidecar determines both the
constructor and the all-scalar field condition of the concrete operand. -/
theorem Sidecars.scalarLeafAt?_runtime (sidecars : Sidecars)
    {site : Lower.SourceSite} {atom : IxIR1.Atom}
    {fact : IxIR1.HPT.Fact} {identity : CtorId}
    {declarations : IxIR1.HPT.DeclEnv} {store : IxIR1.Store}
    {values : List IxIR1.RVal} {location : Nat}
    (found : sidecars.scalarLeafAt? site atom = some (fact, identity))
    (environment : ∀ analyzed,
      sidecars.siteFacts? site = some analyzed →
        IxIR1.HPT.EnvironmentHolds declarations store analyzed.facts values)
    (resolved : IxIR1.resolveAtom values atom = .ok (.loc location)) :
    ∃ box fields,
      store.get? location = some box ∧
        box.node = .ctorN identity fields ∧
        fields.all IxIR1.RVal.isScalar = true := by
  obtain ⟨analyzed, leaf, siteFound, abstractResolved, exactLeaf,
      leafIdentity⟩ := sidecars.scalarLeafAt?_eq_some found
  have factHolds := IxIR1.HPT.resolveAtom_sound
    (environment analyzed siteFound) abstractResolved resolved
  obtain ⟨runtimeLocation, box, fields, valueEq, sourceGet, node,
      scalarFields⟩ :=
    IxIR1.HPT.Destroy.exactLeaf?_holds exactLeaf factHolds
  injection valueEq with locationEq
  subst runtimeLocation
  rw [leafIdentity] at node
  exact ⟨box, fields, sourceGet, node, by simpa using scalarFields⟩

/-- The stronger scalar-leaf lookup agrees with any concrete constructor node
at the selected operand and simultaneously proves its field vector scalar. -/
theorem Sidecars.scalarLeafAt?_matches_node (sidecars : Sidecars)
    {site : Lower.SourceSite} {atom : IxIR1.Atom}
    {fact : IxIR1.HPT.Fact} {identity runtimeIdentity : CtorId}
    {declarations : IxIR1.HPT.DeclEnv} {store : IxIR1.Store}
    {values : List IxIR1.RVal} {location : Nat}
    {box : IxIR1.NodeBox} {fields : Array IxIR1.RVal}
    (found : sidecars.scalarLeafAt? site atom = some (fact, identity))
    (environment : ∀ analyzed,
      sidecars.siteFacts? site = some analyzed →
        IxIR1.HPT.EnvironmentHolds declarations store analyzed.facts values)
    (resolved : IxIR1.resolveAtom values atom = .ok (.loc location))
    (sourceGet : store.get? location = some box)
    (node : box.node = .ctorN runtimeIdentity fields) :
    runtimeIdentity = identity ∧ fields.all IxIR1.RVal.isScalar = true := by
  obtain ⟨exactBox, exactFields, exactGet, exactNode, scalarFields⟩ :=
    sidecars.scalarLeafAt?_runtime found environment resolved
  have boxEq : exactBox = box :=
    Option.some.inj (exactGet.symm.trans sourceGet)
  subst exactBox
  have constructorEq :
      (.ctorN runtimeIdentity fields : IxIR1.Node) =
        .ctorN identity exactFields := node.symm.trans exactNode
  injection constructorEq with identityEq fieldsEq
  subst identity
  subst exactFields
  exact ⟨rfl, scalarFields⟩

private def constructorInfo? (sidecars : Sidecars) (identity : CtorId) :
    Option ConstructorInfo :=
  sidecars.constructors.find? fun info => info.identity == identity

def Sidecars.fetchCtor? (sidecars : Sidecars)
    (site : Lower.SourceSite) : Option CtorId := do
  let analyzed ← sidecars.siteFacts? site
  match analyzed.code with
  | .letOp (.fetch target field) _ => do
      let (_, identity) ← sidecars.exactConstructorAt? site target
      let info ← constructorInfo? sidecars identity
      if field < info.arity then some identity else none
  | _ => none

def Sidecars.scalarFreeCtor? (sidecars : Sidecars)
    (site : Lower.SourceSite) : Option CtorId := do
  let analyzed ← sidecars.siteFacts? site
  match analyzed.code with
  | .letOp (.free target) _ => do
      let (_, identity) ← sidecars.scalarLeafAt? site target
      let info ← constructorInfo? sidecars identity
      if info.arity == 0 then some identity else none
  | _ => none

def Sidecars.caseCtors (sidecars : Sidecars) (site : Lower.SourceSite)
    (alternative : Nat) : List CtorId :=
  match codeAtSite? sidecars.input site with
  | some (.case scrutinee _ alternatives) =>
      match alternatives[alternative]? with
      | some (.mk tag fields _) =>
          match sidecars.exactConstructorAt? site scrutinee with
          | some (_, identity) =>
              match constructorInfo? sidecars identity with
              | some info =>
                  if identity.cidx == tag && info.arity == fields then
                    [identity]
                  else
                    []
              | none => []
          | none =>
              (sidecars.constructors.filter fun info =>
                info.identity.cidx == tag && info.arity == fields).map
                  (·.identity) |>.eraseDups
      | none => []
  | _ => []

/-- The exact lowering context computed for this attachment. Case lowering
prefers an exact path-local HPT identity and otherwise emits every
producer-known full identity matching the erased source tag and arity.
Projection and shallow-free facts remain deliberately partial and fail closed
when their identity is ambiguous. -/
def Sidecars.context (sidecars : Sidecars) (maxDepth : Nat := 100000) :
    Lower.Context :=
  { parameterWorlds := lookupParameterWorlds sidecars.parameterEntries
    schemas := schema? sidecars.constructors
    fetchCtor := sidecars.fetchCtor?
    scalarFreeCtor := sidecars.scalarFreeCtor?
    caseCtors := sidecars.caseCtors
    allowExtern := false
    maxDepth }

/-! ## Extern-free trace coverage

The attachment's lowering context disables scalar extern boundaries.  Retain
that fail-closed decision as a recursive trace certificate so the semantic
worker can eliminate an apparent successful source `extern` branch without
replaying the compiler or validator. -/

mutual

/-- No recursive node in one compiler trace contains a source extern
operation. -/
def Sidecars.codeExternFree (_sidecars : Sidecars) : Lower.CodeTrace → Bool
  | .ret .. | .tailCall .. | .tailCallSelf .. => true
  | .letOp _ _ _ _ _ (.extern _ _) _ _ _ => false
  | .letOp _ _ _ _ _ _ _ _ next => _sidecars.codeExternFree next
  | .switchValue _ _ _ _ _ _ _ _ _ _ children =>
      _sidecars.codeExternFreeList children

private def Sidecars.codeExternFreeList (sidecars : Sidecars) :
    List Lower.CodeTrace → Bool
  | [] => true
  | trace :: traces =>
      sidecars.codeExternFree trace && sidecars.codeExternFreeList traces

end

/-- Whole-trace extern exclusion checked at attachment time. -/
def Sidecars.traceExternFree (sidecars : Sidecars)
    (trace : Lower.Trace) : Bool :=
  trace.functions.all fun functionTrace =>
    sidecars.codeExternFree functionTrace.root

private theorem Sidecars.codeExternFreeList_of_mem (sidecars : Sidecars)
    {traces : List Lower.CodeTrace} {trace : Lower.CodeTrace}
    (matched : sidecars.codeExternFreeList traces = true)
    (member : trace ∈ traces) :
    sidecars.codeExternFree trace = true := by
  induction traces with
  | nil => simp at member
  | cons head tail ih =>
      simp only [Sidecars.codeExternFreeList, Bool.and_eq_true] at matched
      simp only [List.mem_cons] at member
      cases member with
      | inl equal => simpa [equal] using matched.1
      | inr member => exact ih matched.2 member

/-- Extern exclusion is inherited by every immediate recursive child. -/
theorem Sidecars.codeExternFree_of_child (sidecars : Sidecars)
    {parent child : Lower.CodeTrace}
    (matched : sidecars.codeExternFree parent = true)
    (member : child ∈ parent.children) :
    sidecars.codeExternFree child = true := by
  cases parent with
  | ret _ _ _ _ _ _ _ | tailCall _ _ _ _ _ _ _
  | tailCallSelf _ _ _ _ _ _ =>
      simp [Lower.CodeTrace.children] at member
  | letOp site block input nextInput entryValueCount operation index
      instruction next =>
      simp [Lower.CodeTrace.children] at member
      subst child
      cases operation <;>
        simp_all [Sidecars.codeExternFree]
  | switchValue site block input entryValueCount scrutinee peel alternatives
      target generated outgoing children =>
      exact sidecars.codeExternFreeList_of_mem matched member

/-- Extern exclusion is inherited by every recursive descendant. -/
theorem Sidecars.codeExternFree_descendant (sidecars : Sidecars)
    {root child : Lower.CodeTrace}
    (matched : sidecars.codeExternFree root = true)
    (descendant : root.Descendant child) :
    sidecars.codeExternFree child = true := by
  induction descendant with
  | refl => exact matched
  | @step parent child parentDescendant childMember ih =>
      exact sidecars.codeExternFree_of_child ih childMember

/-- Whole-trace extern exclusion selects any retained function root. -/
theorem Sidecars.functionCodeExternFree (sidecars : Sidecars)
    {trace : Lower.Trace} {functionTrace : Lower.FunctionTrace}
    (matched : sidecars.traceExternFree trace = true)
    (member : functionTrace ∈ trace.functions) :
    sidecars.codeExternFree functionTrace.root = true :=
  List.all_eq_true.mp matched functionTrace member

/-! ## Scalar-leaf trace coverage

The lowerer records a validator fact for every emitted `freeUnique`.  The
following independent executable check ties every such recursive trace node
back to the stronger HPT scalar-leaf lookup used by `scalarFreeCtor?`.  Its
reflected descendant theorem lets simulation recover that semantic evidence
from attachment membership instead of accepting it from a caller. -/

private def Sidecars.scalarLeafInstructionMatches (sidecars : Sidecars)
    (site : Lower.SourceSite) : IxIR1.Op → Instr → Bool
  | .free source, .freeUnique _ identity =>
      match sidecars.scalarLeafAt? site source with
      | some (_, selectedIdentity) => selectedIdentity == identity
      | none => false
  | _, _ => true

mutual

/-- Every shallow-free node in one recursive compiler trace has exact
all-scalar HPT evidence at its literal source coordinate. -/
def Sidecars.codeScalarLeavesMatch (sidecars : Sidecars) :
    Lower.CodeTrace → Bool
  | .ret .. | .tailCall .. | .tailCallSelf .. => true
  | .letOp site _ _ _ _ operation _ instruction next =>
      sidecars.scalarLeafInstructionMatches site operation instruction &&
        sidecars.codeScalarLeavesMatch next
  | .switchValue _ _ _ _ _ _ _ _ _ _ children =>
      sidecars.codeScalarLeafListMatches children

private def Sidecars.codeScalarLeafListMatches (sidecars : Sidecars) :
    List Lower.CodeTrace → Bool
  | [] => true
  | trace :: traces =>
      sidecars.codeScalarLeavesMatch trace &&
        sidecars.codeScalarLeafListMatches traces

end

/-- Whole-trace scalar-leaf coverage checked at attachment time. -/
def Sidecars.traceScalarLeavesMatch (sidecars : Sidecars)
    (trace : Lower.Trace) : Bool :=
  trace.functions.all fun functionTrace =>
    sidecars.codeScalarLeavesMatch functionTrace.root

private theorem Sidecars.codeScalarLeafListMatch_of_mem
    (sidecars : Sidecars) {traces : List Lower.CodeTrace}
    {trace : Lower.CodeTrace}
    (matched : sidecars.codeScalarLeafListMatches traces = true)
    (member : trace ∈ traces) :
    sidecars.codeScalarLeavesMatch trace = true := by
  induction traces with
  | nil => simp at member
  | cons head tail ih =>
      simp only [Sidecars.codeScalarLeafListMatches, Bool.and_eq_true] at matched
      simp only [List.mem_cons] at member
      cases member with
      | inl equal => simpa [equal] using matched.1
      | inr member => exact ih matched.2 member

/-- Scalar-leaf coverage is inherited by every immediate recursive compiler
call. -/
theorem Sidecars.codeScalarLeavesMatch_of_child (sidecars : Sidecars)
    {parent child : Lower.CodeTrace}
    (matched : sidecars.codeScalarLeavesMatch parent = true)
    (member : child ∈ parent.children) :
    sidecars.codeScalarLeavesMatch child = true := by
  cases parent with
  | ret _ _ _ _ _ _ _ | tailCall _ _ _ _ _ _ _
  | tailCallSelf _ _ _ _ _ _ =>
      simp [Lower.CodeTrace.children] at member
  | letOp site block input nextInput entryValueCount operation index
      instruction next =>
      simp [Lower.CodeTrace.children] at member
      subst child
      simp only [Sidecars.codeScalarLeavesMatch, Bool.and_eq_true] at matched
      exact matched.2
  | switchValue site block input entryValueCount scrutinee peel alternatives
      target generated outgoing children =>
      exact sidecars.codeScalarLeafListMatch_of_mem matched member

/-- Scalar-leaf coverage is inherited by every recursive descendant. -/
theorem Sidecars.codeScalarLeavesMatch_descendant (sidecars : Sidecars)
    {root child : Lower.CodeTrace}
    (matched : sidecars.codeScalarLeavesMatch root = true)
    (descendant : root.Descendant child) :
    sidecars.codeScalarLeavesMatch child = true := by
  induction descendant with
  | refl => exact matched
  | @step parent child parentDescendant childMember ih =>
      exact sidecars.codeScalarLeavesMatch_of_child ih childMember

/-- Whole-trace coverage selects any retained function root. -/
theorem Sidecars.functionCodeScalarLeavesMatch (sidecars : Sidecars)
    {trace : Lower.Trace} {functionTrace : Lower.FunctionTrace}
    (matched : sidecars.traceScalarLeavesMatch trace = true)
    (member : functionTrace ∈ trace.functions) :
    sidecars.codeScalarLeavesMatch functionTrace.root = true :=
  List.all_eq_true.mp matched functionTrace member

/-- Reflection at one shallow-free trace node recovers the exact HPT fact and
constructor identity consumed by its target instruction. -/
theorem Sidecars.scalarLeafAt?_of_codeScalarLeavesMatch
    (sidecars : Sidecars)
    {site : Lower.SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount index : Nat}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {identity : CtorId}
    {next : Lower.CodeTrace}
    (matched : sidecars.codeScalarLeavesMatch
      (.letOp site block input nextInput entryValueCount
        (.free sourceAtom) index (.freeUnique targetAtom identity) next) = true) :
    ∃ fact,
      sidecars.scalarLeafAt? site sourceAtom = some (fact, identity) := by
  simp only [Sidecars.codeScalarLeavesMatch, Bool.and_eq_true] at matched
  have head := matched.1
  unfold Sidecars.scalarLeafInstructionMatches at head
  cases selected : sidecars.scalarLeafAt? site sourceAtom with
  | none => simp [selected] at head
  | some pair =>
      obtain ⟨fact, selectedIdentity⟩ := pair
      have identityEq : selectedIdentity = identity := by
        exact (beq_iff_eq.mp (by simpa [selected] using head))
      exact ⟨fact, by simp [identityEq]⟩

/-! ## Exact-fetch trace coverage

The lowering context selects source projections from exact HPT constructor
facts.  This independent recursive check records that every retained source
fetch uses that same identity, so attachment-facing simulation can recover the
erased constructor fact from trace membership alone. -/

private def Sidecars.exactFetchInstructionMatches (sidecars : Sidecars)
    (site : Lower.SourceSite) : IxIR1.Op → Instr → Bool
  | .fetch source _, .fetch _ identity _ =>
      match sidecars.exactConstructorAt? site source with
      | some (_, selectedIdentity) => selectedIdentity == identity
      | none => false
  | _, _ => true

mutual

/-- Every source-fetch node in one recursive compiler trace retains exact HPT
constructor evidence at its literal source coordinate. -/
def Sidecars.codeExactFetchesMatch (sidecars : Sidecars) :
    Lower.CodeTrace → Bool
  | .ret .. | .tailCall .. | .tailCallSelf .. => true
  | .letOp site _ _ _ _ operation _ instruction next =>
      sidecars.exactFetchInstructionMatches site operation instruction &&
        sidecars.codeExactFetchesMatch next
  | .switchValue _ _ _ _ _ _ _ _ _ _ children =>
      sidecars.codeExactFetchListMatches children

private def Sidecars.codeExactFetchListMatches (sidecars : Sidecars) :
    List Lower.CodeTrace → Bool
  | [] => true
  | trace :: traces =>
      sidecars.codeExactFetchesMatch trace &&
        sidecars.codeExactFetchListMatches traces

end

/-- Whole-trace exact-fetch coverage checked at attachment time. -/
def Sidecars.traceExactFetchesMatch (sidecars : Sidecars)
    (trace : Lower.Trace) : Bool :=
  trace.functions.all fun functionTrace =>
    sidecars.codeExactFetchesMatch functionTrace.root

private theorem Sidecars.codeExactFetchListMatch_of_mem
    (sidecars : Sidecars) {traces : List Lower.CodeTrace}
    {trace : Lower.CodeTrace}
    (matched : sidecars.codeExactFetchListMatches traces = true)
    (member : trace ∈ traces) :
    sidecars.codeExactFetchesMatch trace = true := by
  induction traces with
  | nil => simp at member
  | cons head tail ih =>
      simp only [Sidecars.codeExactFetchListMatches, Bool.and_eq_true] at matched
      simp only [List.mem_cons] at member
      cases member with
      | inl equal => simpa [equal] using matched.1
      | inr member => exact ih matched.2 member

/-- Exact-fetch coverage is inherited by every immediate recursive compiler
call. -/
theorem Sidecars.codeExactFetchesMatch_of_child (sidecars : Sidecars)
    {parent child : Lower.CodeTrace}
    (matched : sidecars.codeExactFetchesMatch parent = true)
    (member : child ∈ parent.children) :
    sidecars.codeExactFetchesMatch child = true := by
  cases parent with
  | ret _ _ _ _ _ _ _ | tailCall _ _ _ _ _ _ _
  | tailCallSelf _ _ _ _ _ _ =>
      simp [Lower.CodeTrace.children] at member
  | letOp site block input nextInput entryValueCount operation index
      instruction next =>
      simp [Lower.CodeTrace.children] at member
      subst child
      simp only [Sidecars.codeExactFetchesMatch, Bool.and_eq_true] at matched
      exact matched.2
  | switchValue site block input entryValueCount scrutinee peel alternatives
      target generated outgoing children =>
      exact sidecars.codeExactFetchListMatch_of_mem matched member

/-- Exact-fetch coverage is inherited by every recursive descendant. -/
theorem Sidecars.codeExactFetchesMatch_descendant (sidecars : Sidecars)
    {root child : Lower.CodeTrace}
    (matched : sidecars.codeExactFetchesMatch root = true)
    (descendant : root.Descendant child) :
    sidecars.codeExactFetchesMatch child = true := by
  induction descendant with
  | refl => exact matched
  | @step parent child parentDescendant childMember ih =>
      exact sidecars.codeExactFetchesMatch_of_child ih childMember

/-- Whole-trace exact-fetch coverage selects any retained function root. -/
theorem Sidecars.functionCodeExactFetchesMatch (sidecars : Sidecars)
    {trace : Lower.Trace} {functionTrace : Lower.FunctionTrace}
    (matched : sidecars.traceExactFetchesMatch trace = true)
    (member : functionTrace ∈ trace.functions) :
    sidecars.codeExactFetchesMatch functionTrace.root = true :=
  List.all_eq_true.mp matched functionTrace member

/-- Reflection at one source-fetch trace node recovers the exact HPT fact and
constructor identity consumed by its target instruction. -/
theorem Sidecars.exactConstructorAt?_of_codeExactFetchesMatch
    (sidecars : Sidecars)
    {site : Lower.SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount index : Nat}
    {sourceAtom : IxIR1.Atom} {sourceField : Nat}
    {targetAtom : Atom} {targetField : Nat} {identity : CtorId}
    {next : Lower.CodeTrace}
    (matched : sidecars.codeExactFetchesMatch
      (.letOp site block input nextInput entryValueCount
        (.fetch sourceAtom sourceField) index
        (.fetch targetAtom identity targetField) next) = true) :
    ∃ fact,
      sidecars.exactConstructorAt? site sourceAtom =
        some (fact, identity) := by
  simp only [Sidecars.codeExactFetchesMatch, Bool.and_eq_true] at matched
  have head := matched.1
  unfold Sidecars.exactFetchInstructionMatches at head
  cases selected : sidecars.exactConstructorAt? site sourceAtom with
  | none => simp [selected] at head
  | some pair =>
      obtain ⟨fact, selectedIdentity⟩ := pair
      have identityEq : selectedIdentity = identity := by
        exact (beq_iff_eq.mp (by simpa [selected] using head))
      exact ⟨fact, by simp [identityEq]⟩

/-! ## Exact-constructor switch coverage

When path-local HPT has already reduced a case scrutinee to one constructor,
the emitted switch must contain that exact identity.  This check is separate
from structural switch coherence: it connects the erased source operand fact
to the concrete constructor table retained by the target terminator.  Cases
whose HPT fact is not exact remain deliberately unconstrained here and are
handled by the residual dynamic coverage contract in `PipelineSim`.
-/

private def Sidecars.exactCaseTargetMatches (sidecars : Sidecars)
    (site : Lower.SourceSite) (sourceScrutinee : IxIR1.Atom)
    (generated : Block) : Bool :=
  match sidecars.exactConstructorAt? site sourceScrutinee with
  | none => true
  | some (_, identity) =>
      match generated.terminator with
      | .switchValue _ constructors _ =>
          (constructors.find? fun target => target.cid == identity).isSome
      | _ => false

mutual

/-- Every exact-HPT case in one recursive compiler trace has a target branch
for the selected constructor identity. -/
def Sidecars.codeExactCaseTargetsMatch (sidecars : Sidecars) :
    Lower.CodeTrace → Bool
  | .ret .. | .tailCall .. | .tailCallSelf .. => true
  | .letOp _ _ _ _ _ _ _ _ next =>
      sidecars.codeExactCaseTargetsMatch next
  | .switchValue site _ _ _ sourceScrutinee _ _ _ generated _ children =>
      sidecars.exactCaseTargetMatches site sourceScrutinee generated &&
        sidecars.codeExactCaseTargetListMatches children

private def Sidecars.codeExactCaseTargetListMatches (sidecars : Sidecars) :
    List Lower.CodeTrace → Bool
  | [] => true
  | trace :: traces =>
      sidecars.codeExactCaseTargetsMatch trace &&
        sidecars.codeExactCaseTargetListMatches traces

end

/-- Whole-trace exact-HPT constructor-switch coverage checked at attachment
time. -/
def Sidecars.traceExactCaseTargetsMatch (sidecars : Sidecars)
    (trace : Lower.Trace) : Bool :=
  trace.functions.all fun functionTrace =>
    sidecars.codeExactCaseTargetsMatch functionTrace.root

private theorem Sidecars.codeExactCaseTargetListMatch_of_mem
    (sidecars : Sidecars) {traces : List Lower.CodeTrace}
    {trace : Lower.CodeTrace}
    (matched : sidecars.codeExactCaseTargetListMatches traces = true)
    (member : trace ∈ traces) :
    sidecars.codeExactCaseTargetsMatch trace = true := by
  induction traces with
  | nil => simp at member
  | cons head tail ih =>
      simp only [Sidecars.codeExactCaseTargetListMatches,
        Bool.and_eq_true] at matched
      simp only [List.mem_cons] at member
      cases member with
      | inl equal => simpa [equal] using matched.1
      | inr member => exact ih matched.2 member

/-- Exact-case coverage is inherited by every immediate recursive compiler
call. -/
theorem Sidecars.codeExactCaseTargetsMatch_of_child (sidecars : Sidecars)
    {parent child : Lower.CodeTrace}
    (matched : sidecars.codeExactCaseTargetsMatch parent = true)
    (member : child ∈ parent.children) :
    sidecars.codeExactCaseTargetsMatch child = true := by
  cases parent with
  | ret _ _ _ _ _ _ _ | tailCall _ _ _ _ _ _ _
  | tailCallSelf _ _ _ _ _ _ =>
      simp [Lower.CodeTrace.children] at member
  | letOp site block input nextInput entryValueCount operation index
      instruction next =>
      simp [Lower.CodeTrace.children] at member
      subst child
      exact matched
  | switchValue site block input entryValueCount sourceScrutinee peelNat
      alternatives targetScrutinee generated outgoing children =>
      simp only [Sidecars.codeExactCaseTargetsMatch,
        Bool.and_eq_true] at matched
      exact sidecars.codeExactCaseTargetListMatch_of_mem matched.2 member

/-- Exact-case coverage is inherited by every recursive descendant. -/
theorem Sidecars.codeExactCaseTargetsMatch_descendant (sidecars : Sidecars)
    {root child : Lower.CodeTrace}
    (matched : sidecars.codeExactCaseTargetsMatch root = true)
    (descendant : root.Descendant child) :
    sidecars.codeExactCaseTargetsMatch child = true := by
  induction descendant with
  | refl => exact matched
  | @step parent child parentDescendant childMember ih =>
      exact sidecars.codeExactCaseTargetsMatch_of_child ih childMember

/-- Whole-trace exact-case coverage selects any retained function root. -/
theorem Sidecars.functionCodeExactCaseTargetsMatch (sidecars : Sidecars)
    {trace : Lower.Trace} {functionTrace : Lower.FunctionTrace}
    (matched : sidecars.traceExactCaseTargetsMatch trace = true)
    (member : functionTrace ∈ trace.functions) :
    sidecars.codeExactCaseTargetsMatch functionTrace.root = true :=
  List.all_eq_true.mp matched functionTrace member

/-- Reflection at one switch node recovers an emitted target for the exact
constructor selected by HPT. -/
theorem Sidecars.exactCaseTarget_of_codeExactCaseTargetsMatch
    (sidecars : Sidecars)
    {site : Lower.SourceSite} {block : BlockId}
    {input : Array (Option Atom)} {entryValueCount : Nat}
    {sourceScrutinee : IxIR1.Atom} {peelNat : Bool}
    {alternatives : Array IxIR1.Alt} {targetScrutinee : Atom}
    {generated : Block} {outgoing : List Lower.EdgeTrace}
    {children : List Lower.CodeTrace} {fact : IxIR1.HPT.Fact}
    {identity : CtorId} {constructors : Array CtorAlt}
    {natPeel : Option NatPeel}
    (matched : sidecars.codeExactCaseTargetsMatch
      (.switchValue site block input entryValueCount sourceScrutinee peelNat
        alternatives targetScrutinee generated outgoing children) = true)
    (selected : sidecars.exactConstructorAt? site sourceScrutinee =
      some (fact, identity))
    (terminator : generated.terminator =
      .switchValue targetScrutinee constructors natPeel) :
    ∃ target, constructors.find? (fun candidate =>
      candidate.cid == identity) = some target := by
  simp only [Sidecars.codeExactCaseTargetsMatch,
    Bool.and_eq_true] at matched
  have localMatch := matched.1
  unfold Sidecars.exactCaseTargetMatches at localMatch
  rw [selected, terminator] at localMatch
  cases found : constructors.find? (fun candidate =>
      candidate.cid == identity) with
  | none => simp [found] at localMatch
  | some target => exact ⟨target, rfl⟩

/-! ## Residual constructor-switch coverage

When path-local HPT is not exact, IxIR₁ may still select any producer-known
constructor with the alternative's erased tag and arity. The baseline lowerer
emits each of those full identities. This independent attachment check records
that coverage over the retained recursive trace. -/

private def Sidecars.residualConstructorTargetMatches
    (constructors : Array CtorAlt) (alternative : IxIR1.Alt)
    (info : ConstructorInfo) : Bool :=
  match alternative with
  | .mk tag fields _ =>
      if info.identity.cidx == tag && info.arity == fields then
        (constructors.find? fun target => target.cid == info.identity).isSome
      else
        true

private def Sidecars.residualCaseTargetsMatch (sidecars : Sidecars)
    (site : Lower.SourceSite) (sourceScrutinee : IxIR1.Atom)
    (alternatives : Array IxIR1.Alt) (generated : Block) : Bool :=
  match sidecars.exactConstructorAt? site sourceScrutinee with
  | some _ => true
  | none =>
      match generated.terminator with
      | .switchValue _ constructors _ =>
          alternatives.toList.all fun alternative =>
            sidecars.constructors.all fun info =>
              Sidecars.residualConstructorTargetMatches constructors
                alternative info
      | _ => false

mutual

/-- Every HPT-ambiguous case in one recursive compiler trace covers every
producer-known constructor compatible with its selected IxIR₁ arm. -/
def Sidecars.codeResidualCaseTargetsMatch (sidecars : Sidecars) :
    Lower.CodeTrace → Bool
  | .ret .. | .tailCall .. | .tailCallSelf .. => true
  | .letOp _ _ _ _ _ _ _ _ next =>
      sidecars.codeResidualCaseTargetsMatch next
  | .switchValue site _ _ _ sourceScrutinee _ alternatives _ generated _
      children =>
      sidecars.residualCaseTargetsMatch site sourceScrutinee alternatives
          generated &&
        sidecars.codeResidualCaseTargetListMatches children

private def Sidecars.codeResidualCaseTargetListMatches
    (sidecars : Sidecars) : List Lower.CodeTrace → Bool
  | [] => true
  | trace :: traces =>
      sidecars.codeResidualCaseTargetsMatch trace &&
        sidecars.codeResidualCaseTargetListMatches traces

end

/-- Whole-trace residual constructor-switch coverage checked at attachment
time. -/
def Sidecars.traceResidualCaseTargetsMatch (sidecars : Sidecars)
    (trace : Lower.Trace) : Bool :=
  trace.functions.all fun functionTrace =>
    sidecars.codeResidualCaseTargetsMatch functionTrace.root

private theorem Sidecars.codeResidualCaseTargetListMatch_of_mem
    (sidecars : Sidecars) {traces : List Lower.CodeTrace}
    {trace : Lower.CodeTrace}
    (matched : sidecars.codeResidualCaseTargetListMatches traces = true)
    (member : trace ∈ traces) :
    sidecars.codeResidualCaseTargetsMatch trace = true := by
  induction traces with
  | nil => simp at member
  | cons head tail ih =>
      simp only [Sidecars.codeResidualCaseTargetListMatches,
        Bool.and_eq_true] at matched
      simp only [List.mem_cons] at member
      cases member with
      | inl equal => simpa [equal] using matched.1
      | inr member => exact ih matched.2 member

/-- Residual-case coverage is inherited by every immediate recursive
compiler call. -/
theorem Sidecars.codeResidualCaseTargetsMatch_of_child (sidecars : Sidecars)
    {parent child : Lower.CodeTrace}
    (matched : sidecars.codeResidualCaseTargetsMatch parent = true)
    (member : child ∈ parent.children) :
    sidecars.codeResidualCaseTargetsMatch child = true := by
  cases parent with
  | ret _ _ _ _ _ _ _ | tailCall _ _ _ _ _ _ _
  | tailCallSelf _ _ _ _ _ _ =>
      simp [Lower.CodeTrace.children] at member
  | letOp site block input nextInput entryValueCount operation index
      instruction next =>
      simp [Lower.CodeTrace.children] at member
      subst child
      exact matched
  | switchValue site block input entryValueCount sourceScrutinee peelNat
      alternatives targetScrutinee generated outgoing children =>
      simp only [Sidecars.codeResidualCaseTargetsMatch,
        Bool.and_eq_true] at matched
      exact sidecars.codeResidualCaseTargetListMatch_of_mem matched.2 member

/-- Residual-case coverage is inherited by every recursive descendant. -/
theorem Sidecars.codeResidualCaseTargetsMatch_descendant
    (sidecars : Sidecars) {root child : Lower.CodeTrace}
    (matched : sidecars.codeResidualCaseTargetsMatch root = true)
    (descendant : root.Descendant child) :
    sidecars.codeResidualCaseTargetsMatch child = true := by
  induction descendant with
  | refl => exact matched
  | @step parent child parentDescendant childMember ih =>
      exact sidecars.codeResidualCaseTargetsMatch_of_child ih childMember

/-- Whole-trace residual coverage selects any retained function root. -/
theorem Sidecars.functionCodeResidualCaseTargetsMatch (sidecars : Sidecars)
    {trace : Lower.Trace} {functionTrace : Lower.FunctionTrace}
    (matched : sidecars.traceResidualCaseTargetsMatch trace = true)
    (member : functionTrace ∈ trace.functions) :
    sidecars.codeResidualCaseTargetsMatch functionTrace.root = true :=
  List.all_eq_true.mp matched functionTrace member

/-- Reflection at one HPT-ambiguous switch: any producer constructor matching
the concrete source arm has a corresponding emitted target. -/
theorem Sidecars.residualCaseTarget_of_codeResidualCaseTargetsMatch
    (sidecars : Sidecars)
    {site : Lower.SourceSite} {block : BlockId}
    {input : Array (Option Atom)} {entryValueCount : Nat}
    {sourceScrutinee : IxIR1.Atom} {peelNat : Bool}
    {alternatives : Array IxIR1.Alt} {targetScrutinee : Atom}
    {generated : Block} {outgoing : List Lower.EdgeTrace}
    {children : List Lower.CodeTrace} {identity : CtorId}
    {arity alternativeIndex : Nat} {body : IxIR1.Code}
    {constructors : Array CtorAlt} {natPeel : Option NatPeel}
    (matched : sidecars.codeResidualCaseTargetsMatch
      (.switchValue site block input entryValueCount sourceScrutinee peelNat
        alternatives targetScrutinee generated outgoing children) = true)
    (ambiguous : sidecars.exactConstructorAt? site sourceScrutinee = none)
    (known : ∃ info ∈ sidecars.constructors,
      info.identity = identity ∧ info.arity = arity)
    (sourceAlternative : Lower.sourceAlternativeAtTag? alternatives
      identity.cidx = some
        (.mk identity.cidx arity body, alternativeIndex))
    (terminator : generated.terminator =
      .switchValue targetScrutinee constructors natPeel) :
    ∃ target, constructors.find? (fun candidate =>
      candidate.cid == identity) = some target := by
  simp only [Sidecars.codeResidualCaseTargetsMatch,
    Bool.and_eq_true] at matched
  have localMatch := matched.1
  unfold Sidecars.residualCaseTargetsMatch at localMatch
  rw [ambiguous, terminator] at localMatch
  obtain ⟨info, infoMember, infoIdentity, infoArity⟩ := known
  have alternativeAt : alternatives[alternativeIndex]? =
      some (.mk identity.cidx arity body) :=
    Lower.sourceAlternativeAtTag?_getElem? sourceAlternative
  have alternativeMember : (.mk identity.cidx arity body : IxIR1.Alt) ∈
      alternatives.toList := by
    simpa using
      (Array.mem_iff_getElem?.mpr ⟨alternativeIndex, alternativeAt⟩)
  have alternativeMatch := List.all_eq_true.mp localMatch
    (.mk identity.cidx arity body) alternativeMember
  have infoMatch := List.all_eq_true.mp alternativeMatch info infoMember
  unfold Sidecars.residualConstructorTargetMatches at infoMatch
  rw [infoIdentity, infoArity] at infoMatch
  simp only [beq_self_eq_true, Bool.true_and, if_true] at infoMatch
  cases found : constructors.find? (fun candidate =>
      candidate.cid == identity) with
  | none => simp [found] at infoMatch
  | some target => exact ⟨target, rfl⟩

/-- Every constructor schema emitted by the baseline pipeline is uniform in
the ownership world used to look it up. This is the static fact consumed by
the allocation-simulation proof to discharge the evaluator's field checks. -/
theorem Sidecars.schema_fields_replicate (sidecars : Sidecars)
    {maxDepth : Nat} {world : Owned} {identity : CtorId}
    {schema : CtorSchema}
    (found : (sidecars.context maxDepth).schemas world identity =
      some schema) :
    ∃ count, schema.fields = Array.replicate count world := by
  change schema? sidecars.constructors world identity = some schema at found
  unfold schema? at found
  cases lookup : sidecars.constructors.find?
      (fun candidate => candidate.identity == identity) with
  | none => simp [lookup] at found
  | some info =>
      simp [lookup] at found
      subst schema
      exact ⟨info.arity, rfl⟩

/-- A constructor-universe witness and a schema lookup share the same
identity-indexed sidecar row, so the runtime node arity is the schema arity. -/
theorem Sidecars.schema_fields_of_constructorKnown (sidecars : Sidecars)
    {maxDepth : Nat} {world : Owned} {identity : CtorId} {arity : Nat}
    {schema : CtorSchema}
    (known : sidecars.constructorKnown identity arity = true)
    (found : (sidecars.context maxDepth).schemas world identity = some schema) :
    schema.fields = Array.replicate arity world := by
  change schema? sidecars.constructors world identity = some schema at found
  unfold schema? at found
  unfold Sidecars.constructorKnown at known
  cases lookup : sidecars.constructors.find?
      (fun candidate => candidate.identity == identity) with
  | none => simp [lookup] at known
  | some info =>
      simp [lookup] at found known
      subst schema
      simpa [known]

/-- Sidecars paired with the checked HPT production from which their
interprocedural facts were taken. -/
structure BuiltSidecars
    {constants : List (Address × Ixon.Constant)} {mainAddress : Address}
    {config : Ix.Compiler.Pipeline.Config} {mainWorld : Owned}
    {eraseFuel lowerFuel : Nat}
    (compilation : Ix.Compiler.Pipeline.ValidatedCompilation constants
      mainAddress config mainWorld eraseFuel lowerFuel) where
  sidecars : Sidecars
  hpt : IxIR1.HPT.Production IxIR1.HPT.defaultProducerLimits.checker
    compilation.lowering.result.artifacts
  certificateProduced : sidecars.hptCertificate = hpt.certificate
  inputProduced : sidecars.input =
    { declarations := compilation.artifact.targetDecls
      main := compilation.artifact.main
      mainResult := mainWorld }

/-- Build the sidecars for the exact addressed graph retained by validated
compilation. Parameter conflicts caused by IxIR₁ identities that erased
distinct ownership signatures fail closed before IxIR₂ lowering. The HPT
producer crosses its ordinary checked boundary before any summary is exposed
to a site query. -/
def buildSidecars
    {constants : List (Address × Ixon.Constant)} {mainAddress : Address}
    {config : Ix.Compiler.Pipeline.Config} {mainWorld : Owned}
    {eraseFuel lowerFuel : Nat}
    (compilation : Ix.Compiler.Pipeline.ValidatedCompilation constants
      mainAddress config mainWorld eraseFuel lowerFuel) :
    Except Error (BuiltSidecars compilation) := do
  let artifact := compilation.artifact
  let hpt ← match IxIR1.HPT.produce compilation.lowering.result.artifacts with
    | .ok production => pure production
    | .error message => .error (.hpt message)
  let parameterEntries ← buildParameterWorlds
    compilation.erasure.result.declarations compilation.lowering.raw
      compilation.lowering.result.addressMap
  let recursorOrigins ← deriveRecursorOrigins
    compilation.erasure.result.declarations
      compilation.erasure.result.addressed.blocks compilation.lowering.raw
      compilation.lowering.result.addressMap
  let sidecars : Sidecars :=
    { input :=
        { declarations := artifact.targetDecls
          main := artifact.main
          mainResult := mainWorld }
      parameterEntries
      constructors := constructorInfos
        compilation.erasure.result.declarations
        compilation.erasure.result.addressed.blocks
      recursorOrigins
      hptCertificate := hpt.certificate }
  return {
    sidecars
    hpt
    certificateProduced := rfl
    inputProduced := rfl
  }

/-- Common checked attachment for an exact ownership-lowered program. The
Ixon frontend and checked IxIR₀ transformations share this backend boundary. -/
structure CompiledAttachment (mainWorld : Owned) (lowerFuel : Nat) where
  source : Ix.Compiler.Pipeline.LoweredCompilation mainWorld lowerFuel
  sidecars : Sidecars
  hpt : IxIR1.HPT.Production IxIR1.HPT.defaultProducerLimits.checker
    source.lowering.result.artifacts
  hptCertificateProduced : sidecars.hptCertificate = hpt.certificate
  inputProduced : sidecars.input =
    { declarations := source.targetDecls
      main := source.lowering.result.main
      mainResult := mainWorld }
  maxDepth : Nat
  loweringContext : Lower.Context
  contextProduced : loweringContext = sidecars.context maxDepth
  target : Lower.Checked
  targetProduced : Lower.lower loweringContext sidecars.input = .ok target.artifact
  targetSchemasProduced : target.artifact.validationContext.schemas = loweringContext.schemas
  targetSourceProduced : target.artifact.source = sidecars.input
  traceSourcesProduced : sidecars.traceSourcesMatch target.artifact.trace = true
  traceExternFreeProduced : sidecars.traceExternFree target.artifact.trace = true
  traceExactFetchesProduced : sidecars.traceExactFetchesMatch target.artifact.trace = true
  traceExactCaseTargetsProduced : sidecars.traceExactCaseTargetsMatch target.artifact.trace = true
  traceResidualCaseTargetsProduced : sidecars.traceResidualCaseTargetsMatch target.artifact.trace = true
  traceScalarLeavesProduced : sidecars.traceScalarLeavesMatch target.artifact.trace = true
  sourceNoReuseProduced : sidecars.sourceNoReuse target.artifact.trace = true
  sourceConstructorsProduced : sidecars.traceConstructorsKnown target.artifact.trace = true
  pappSafeProduced : sidecars.tracePappsSafe target.artifact.trace = true

/-- A validated source/IxIR₁ compilation paired with the exact checked IxIR₂
artifact produced from it. -/
structure Attached
    (constants : List (Address × Ixon.Constant)) (mainAddress : Address)
    (config : Ix.Compiler.Pipeline.Config) (mainWorld : Owned)
    (eraseFuel lowerFuel : Nat) where
  source : Ix.Compiler.Pipeline.ValidatedCompilation constants mainAddress
    config mainWorld eraseFuel lowerFuel
  sidecars : Sidecars
  hpt : IxIR1.HPT.Production IxIR1.HPT.defaultProducerLimits.checker
    source.lowering.result.artifacts
  hptCertificateProduced : sidecars.hptCertificate = hpt.certificate
  inputProduced : sidecars.input =
    { declarations := source.artifact.targetDecls
      main := source.artifact.main
      mainResult := mainWorld }
  maxDepth : Nat
  loweringContext : Lower.Context
  contextProduced : loweringContext = sidecars.context maxDepth
  target : Lower.Checked
  targetProduced :
    Lower.lower loweringContext sidecars.input = .ok target.artifact
  targetSchemasProduced :
    target.artifact.validationContext.schemas = loweringContext.schemas
  targetSourceProduced : target.artifact.source = sidecars.input
  traceSourcesProduced :
    sidecars.traceSourcesMatch target.artifact.trace = true
  traceExternFreeProduced :
    sidecars.traceExternFree target.artifact.trace = true
  traceExactFetchesProduced :
    sidecars.traceExactFetchesMatch target.artifact.trace = true
  traceExactCaseTargetsProduced :
    sidecars.traceExactCaseTargetsMatch target.artifact.trace = true
  traceResidualCaseTargetsProduced :
    sidecars.traceResidualCaseTargetsMatch target.artifact.trace = true
  traceScalarLeavesProduced :
    sidecars.traceScalarLeavesMatch target.artifact.trace = true
  sourceNoReuseProduced :
    sidecars.sourceNoReuse target.artifact.trace = true
  sourceConstructorsProduced :
    sidecars.traceConstructorsKnown target.artifact.trace = true
  pappSafeProduced :
    sidecars.tracePappsSafe target.artifact.trace = true

/-- Preserve the public Ixon attachment while projecting the common backend
certificate. No compiler, analysis, or validator is rerun. -/
def Attached.compiled
    {constants : List (Address × Ixon.Constant)} {mainAddress : Address}
    {config : Ix.Compiler.Pipeline.Config} {mainWorld : Owned}
    {eraseFuel lowerFuel : Nat}
    (attached : Attached constants mainAddress config mainWorld eraseFuel lowerFuel) :
    CompiledAttachment mainWorld lowerFuel :=
  { source := attached.source.lowered
    sidecars := attached.sidecars
    hpt := attached.hpt
    hptCertificateProduced := attached.hptCertificateProduced
    inputProduced := attached.inputProduced
    maxDepth := attached.maxDepth
    loweringContext := attached.loweringContext
    contextProduced := attached.contextProduced
    target := attached.target
    targetProduced := attached.targetProduced
    targetSchemasProduced := attached.targetSchemasProduced
    targetSourceProduced := attached.targetSourceProduced
    traceSourcesProduced := attached.traceSourcesProduced
    traceExternFreeProduced := attached.traceExternFreeProduced
    traceExactFetchesProduced := attached.traceExactFetchesProduced
    traceExactCaseTargetsProduced := attached.traceExactCaseTargetsProduced
    traceResidualCaseTargetsProduced := attached.traceResidualCaseTargetsProduced
    traceScalarLeavesProduced := attached.traceScalarLeavesProduced
    sourceNoReuseProduced := attached.sourceNoReuseProduced
    sourceConstructorsProduced := attached.sourceConstructorsProduced
    pappSafeProduced := attached.pappSafeProduced }

instance {constants : List (Address × Ixon.Constant)} {mainAddress : Address}
    {config : Ix.Compiler.Pipeline.Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat} :
    CoeOut (Attached constants mainAddress config mainWorld eraseFuel lowerFuel)
      (CompiledAttachment mainWorld lowerFuel) := ⟨Attached.compiled⟩

/-- Whenever path-local HPT admits the synthetic main owner, its retained
definition is the exact main function named by the checked lowering trace.
If the reserved analysis address collides with a declaration summary, the
premise is impossible and linear transport remains fail closed. -/
theorem CompiledAttachment.mainAnalysisCurrentCompatible
     {mainWorld : Owned}
    {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel) :
    ∀ current,
      attached.sidecars.analysisCurrent? .main = some current →
        current = attached.target.artifact.mainTrace.source := by
  intro current currentAt
  unfold Sidecars.analysisCurrent? at currentAt
  cases summaryEq : attached.sidecars.hptCertificate.summaryEnv
      mainAnalysisOwner with
  | none =>
      simp [analysisRoot?, summaryEq] at currentAt
      rw [attached.target.artifact.mainSource,
        attached.targetSourceProduced]
      exact currentAt.symm
  | some summary =>
      simp [analysisRoot?, summaryEq] at currentAt

/-- Every retained declaration/function trace in an attachment agrees with
the function used by HPT replay whenever that replay root is present. -/
theorem CompiledAttachment.functionTraceAnalysisCurrentCompatible
     {mainWorld : Owned}
    {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {functionTrace : Lower.FunctionTrace}
    (member : functionTrace ∈ attached.target.artifact.trace.functions) :
    ∀ current,
      attached.sidecars.analysisCurrent? functionTrace.owner = some current →
        current = functionTrace.source := by
  intro current currentAt
  exact attached.sidecars.functionTraceSource_eq_of_match
    attached.traceSourcesProduced member currentAt

/-- Every retained non-main function has a recovered HPT analysis root naming
its exact retained source definition.  The whole-trace alignment check permits
a missing root only for the distinguished synthetic main. -/
theorem CompiledAttachment.functionTraceAnalysisCurrent
     {mainWorld : Owned}
    {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {functionTrace : Lower.FunctionTrace}
    (member : functionTrace ∈ attached.target.artifact.trace.functions)
    (notMain : functionTrace.owner ≠ .main) :
    attached.sidecars.analysisCurrent? functionTrace.owner =
      some functionTrace.source := by
  have localMatch := List.all_eq_true.mp attached.traceSourcesProduced
    functionTrace member
  cases currentEq : attached.sidecars.analysisCurrent? functionTrace.owner with
  | none =>
      unfold Sidecars.functionTraceSourceMatches at localMatch
      rw [currentEq] at localMatch
      exact False.elim (notMain (beq_iff_eq.mp localMatch))
  | some current =>
      have currentSource :=
        attached.functionTraceAnalysisCurrentCompatible member current currentEq
      exact congrArg some currentSource

/-- No retained descendant can be a source extern operation.  The executable
attachment check turns the lowerer's disabled extern boundary into the exact
contradiction used by the exhaustive evaluator inversion. -/
theorem CompiledAttachment.sourceExtern_impossible
     {mainWorld : Owned}
    {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {functionTrace : Lower.FunctionTrace}
    (member : functionTrace ∈ attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount index : Nat}
    {address : Address} {arguments : Array IxIR1.Atom}
    {instruction : Instr} {next : Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp site block input nextInput entryValueCount
        (.extern address arguments) index instruction next)) : False := by
  have rootMatch := attached.sidecars.functionCodeExternFree
    attached.traceExternFreeProduced member
  have localMatch := attached.sidecars.codeExternFree_descendant rootMatch
    descendant
  simp [Sidecars.codeExternFree] at localMatch

/-- Every retained source-fetch descendant of an attachment recovers the
exact constructor HPT evidence selected by the lowering context. -/
theorem CompiledAttachment.exactConstructorAt?_of_fetch_descendant
     {mainWorld : Owned}
    {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {functionTrace : Lower.FunctionTrace}
    (member : functionTrace ∈ attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount index : Nat}
    {sourceAtom : IxIR1.Atom} {sourceField : Nat}
    {targetAtom : Atom} {targetField : Nat} {identity : CtorId}
    {next : Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp site block input nextInput entryValueCount
        (.fetch sourceAtom sourceField) index
        (.fetch targetAtom identity targetField) next)) :
    ∃ fact,
      attached.sidecars.exactConstructorAt? site sourceAtom =
        some (fact, identity) := by
  have rootMatch := attached.sidecars.functionCodeExactFetchesMatch
    attached.traceExactFetchesProduced member
  have childMatch := attached.sidecars.codeExactFetchesMatch_descendant
    rootMatch descendant
  exact attached.sidecars.exactConstructorAt?_of_codeExactFetchesMatch
    childMatch

/-- Every exact constructor fact at a retained switch names an actual emitted
constructor target. Structural trace coherence supplies the parallel edge and
child coordinates later; this theorem supplies the formerly erased identity
lookup. -/
theorem CompiledAttachment.exactCaseTarget_of_switch_descendant
     {mainWorld : Owned}
    {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {functionTrace : Lower.FunctionTrace}
    (member : functionTrace ∈ attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {block : BlockId}
    {input : Array (Option Atom)} {entryValueCount : Nat}
    {sourceScrutinee : IxIR1.Atom} {peelNat : Bool}
    {alternatives : Array IxIR1.Alt} {targetScrutinee : Atom}
    {generated : Block} {outgoing : List Lower.EdgeTrace}
    {children : List Lower.CodeTrace} {fact : IxIR1.HPT.Fact}
    {identity : CtorId} {constructors : Array CtorAlt}
    {natPeel : Option NatPeel}
    (descendant : functionTrace.root.Descendant
      (.switchValue site block input entryValueCount sourceScrutinee peelNat
        alternatives targetScrutinee generated outgoing children))
    (selected : attached.sidecars.exactConstructorAt? site sourceScrutinee =
      some (fact, identity))
    (terminator : generated.terminator =
      .switchValue targetScrutinee constructors natPeel) :
    ∃ target, constructors.find? (fun candidate =>
      candidate.cid == identity) = some target := by
  have rootMatch := attached.sidecars.functionCodeExactCaseTargetsMatch
    attached.traceExactCaseTargetsProduced member
  have childMatch :=
    attached.sidecars.codeExactCaseTargetsMatch_descendant rootMatch descendant
  exact attached.sidecars.exactCaseTarget_of_codeExactCaseTargetsMatch
    childMatch selected terminator

/-- Every retained shallow-free descendant of an attachment recovers the
exact scalar-leaf HPT evidence selected by the lowering context. -/
theorem CompiledAttachment.scalarLeafAt?_of_free_descendant
     {mainWorld : Owned}
    {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {functionTrace : Lower.FunctionTrace}
    (member : functionTrace ∈ attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount index : Nat}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {identity : CtorId}
    {next : Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp site block input nextInput entryValueCount
        (.free sourceAtom) index (.freeUnique targetAtom identity) next)) :
    ∃ fact,
      attached.sidecars.scalarLeafAt? site sourceAtom =
        some (fact, identity) := by
  have rootMatch := attached.sidecars.functionCodeScalarLeavesMatch
    attached.traceScalarLeavesProduced member
  have childMatch := attached.sidecars.codeScalarLeavesMatch_descendant
    rootMatch descendant
  exact attached.sidecars.scalarLeafAt?_of_codeScalarLeavesMatch childMatch

/-- An attached artifact retains the exact sidecar-produced context, so its
schema lookups expose the pipeline's uniform ownership-world invariant. -/
theorem CompiledAttachment.schema_fields_replicate
     {mainWorld : Owned}
    {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {world : Owned} {identity : CtorId} {schema : CtorSchema}
    (found : attached.loweringContext.schemas world identity = some schema) :
    ∃ count, schema.fields = Array.replicate count world := by
  rw [attached.contextProduced] at found
  exact attached.sidecars.schema_fields_replicate found

/-- Attachment-facing form of the exact constructor/schema arity bridge. -/
theorem CompiledAttachment.schema_fields_of_constructorKnown
     {mainWorld : Owned}
    {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {world : Owned} {identity : CtorId} {arity : Nat}
    {schema : CtorSchema}
    (known : attached.sidecars.constructorKnown identity arity = true)
    (found : attached.loweringContext.schemas world identity = some schema) :
    schema.fields = Array.replicate arity world := by
  rw [attached.contextProduced] at found
  exact attached.sidecars.schema_fields_of_constructorKnown known found

/-- The HPT facts consulted by this attachment are the exact claims admitted
by the ordinary post-fixpoint checker for its retained IxIR₁ artifact graph. -/
theorem CompiledAttachment.hptPostFixpoint
     {mainWorld : Owned}
    {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel) :
    attached.sidecars.hptCertificate.postFixpoint
      attached.source.lowering.result.artifacts = true := by
  rw [attached.hptCertificateProduced]
  exact attached.hpt.postFixpoint

/-- Propositional local form consumed by operation and code soundness. -/
theorem CompiledAttachment.hptLocalPostFixpoint
     {mainWorld : Owned}
    {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel) :
    IxIR1.HPT.LocalPostFixpoint
      (IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
      attached.sidecars.hptCertificate.summaryEnv :=
  IxIR1.HPT.localPostFixpoint_of_postFixpoint attached.hptPostFixpoint

/-- The sidecar lookup environment is exactly the declaration environment
checked by its HPT production, not merely an extensionally compatible input. -/
theorem CompiledAttachment.sidecarDeclarationEnvironment
     {mainWorld : Owned}
    {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel) :
    IxIR1.Env.ofList attached.sidecars.input.declarations =
      IxIR1.HPT.programDeclEnv
        attached.source.lowering.result.artifacts := by
  rw [attached.inputProduced]
  change IxIR1.Env.ofList
      (IxIR1.HPT.declarationEntries
        attached.source.lowering.result.artifacts) =
    IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts
  exact IxIR1.HPT.OptimizeProgram.envOfList_declarationEntries
    attached.source.lowering.result.artifacts

/-- The fail-closed attachment check discharges reuse-freedom for any source
evaluator context pinned to the attached declaration environment. -/
theorem CompiledAttachment.sourceContextNoReuse
     {mainWorld : Owned}
    {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx}
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv
        attached.source.lowering.result.artifacts) :
    IxIR1.NoReuse.CtxNoReuse sourceContext := by
  have declarationCheck : IxIR1.NoReuse.checkDeclarations
      attached.sidecars.input.declarations = true := by
    have checked := attached.sourceNoReuseProduced
    simp only [Sidecars.sourceNoReuse, Bool.and_eq_true] at checked
    exact checked.1
  have declarationsNoReuse : IxIR1.NoReuse.DeclListNoReuse
      attached.sidecars.input.declarations :=
    (IxIR1.NoReuse.checkDeclarations_eq_true_iff _).mp declarationCheck
  have canonical : IxIR1.NoReuse.CtxNoReuse
      ({ decls := IxIR1.Env.ofList attached.sidecars.input.declarations
         oracle := sourceContext.oracle } : IxIR1.Ctx) :=
    IxIR1.NoReuse.ctxOfList_noReuse declarationsNoReuse
  intro address definition lookup
  apply canonical
  rw [attached.sidecarDeclarationEnvironment, ← sourceDeclarations]
  exact lookup

/-- Every retained source function has passed the executable reuse-freedom
check carried by the attachment. -/
theorem CompiledAttachment.functionTraceNoReuse
     {mainWorld : Owned}
    {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {functionTrace : Lower.FunctionTrace}
    (member : functionTrace ∈ attached.target.artifact.trace.functions) :
    IxIR1.NoReuse.CodeNoReuse functionTrace.source.body := by
  have traceCheck : attached.target.artifact.trace.functions.all
      (fun trace => IxIR1.NoReuse.checkCode trace.source.body) = true := by
    have checked := attached.sourceNoReuseProduced
    simp only [Sidecars.sourceNoReuse, Bool.and_eq_true] at checked
    exact checked.2
  have functionCheck := List.all_eq_true.mp traceCheck functionTrace member
  exact (IxIR1.NoReuse.checkCode_eq_true_iff _).mp functionCheck

/-- Every retained partial-application site resolves to a declaration whose
source PAP-safety flag is true. The context identity premise is the same one
used by the simulation worker. -/
theorem CompiledAttachment.pappSafe
     {mainWorld : Owned}
    {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx}
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv
        attached.source.lowering.result.artifacts)
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount index : Nat}
    {address : Address} {arguments : Array IxIR1.Atom}
    {instruction : Instr} {next : Lower.CodeTrace}
    {definition : IxIR1.FnDef}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.papp address arguments) index instruction next))
    (lookup : sourceContext.decls address = some (.fn definition)) :
    definition.papSafe = true := by
  have rootCheck : attached.sidecars.pappSafeTrace functionTrace.root = true :=
    List.all_eq_true.mp attached.pappSafeProduced functionTrace functionMember
  have localCheck := attached.sidecars.pappSafeTrace_descendant descendant
    rootCheck
  apply attached.sidecars.pappSafe_of_traceMatch localCheck
  rw [attached.sidecarDeclarationEnvironment, ← sourceDeclarations]
  exact lookup

/-- Local HPT post-fixpoint in the exact environment consumed by source-site
replay and its dynamic environment invariant. -/
theorem CompiledAttachment.hptSidecarLocalPostFixpoint
     {mainWorld : Owned}
    {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel) :
    IxIR1.HPT.LocalPostFixpoint
      (IxIR1.Env.ofList attached.sidecars.input.declarations)
      attached.sidecars.hptCertificate.summaryEnv := by
  rw [attached.sidecarDeclarationEnvironment]
  exact attached.hptLocalPostFixpoint

/-- Artifact-facing linear transport: the attachment discharges both the HPT
post-fixpoint and the identity of the declaration environment checked by it. -/
theorem CompiledAttachment.siteEnvironmentHolds_next
     {mainWorld : Owned}
    {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceCurrent : IxIR1.FnDef}
    {sourceFuel : Nat} {sourceStore outputStore : IxIR1.Store}
    {source : List IxIR1.RVal} {operation : IxIR1.Op}
    {value : IxIR1.RVal} {site : Lower.SourceSite} {rest : IxIR1.Code}
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (currentAt : attached.sidecars.analysisCurrent? site.owner =
      some sourceCurrent)
    (environment : attached.sidecars.SiteEnvironmentHolds sourceStore site
      source)
    (sourceAt : attached.sidecars.sourceCodeAt? site =
      some (.letOp operation rest))
    (sourceRun : IxIR1.runOp sourceContext sourceFuel sourceCurrent
      sourceStore source operation = .ok (outputStore, value)) :
    attached.sidecars.SiteEnvironmentHolds outputStore site.next
      (value :: source) := by
  exact attached.sidecars.siteEnvironmentHolds_next
    attached.hptSidecarLocalPostFixpoint
    (sourceDeclarations.trans attached.sidecarDeclarationEnvironment.symm)
    currentAt environment sourceAt sourceRun


/-! Existing theorem names remain available for direct application. -/
namespace Attached
export CompiledAttachment (
  mainAnalysisCurrentCompatible
  functionTraceAnalysisCurrentCompatible
  functionTraceAnalysisCurrent
  sourceExtern_impossible
  exactConstructorAt?_of_fetch_descendant
  exactCaseTarget_of_switch_descendant
  scalarLeafAt?_of_free_descendant
  schema_fields_replicate
  schema_fields_of_constructorKnown
  hptPostFixpoint
  hptLocalPostFixpoint
  sidecarDeclarationEnvironment
  sourceContextNoReuse
  functionTraceNoReuse
  pappSafe
  hptSidecarLocalPostFixpoint
  siteEnvironmentHolds_next)
end Attached

/-- Sidecars and HPT evidence for the common ownership-lowered boundary. -/
structure BuiltCompiledSidecars {mainWorld : Owned} {lowerFuel : Nat}
    (source : Ix.Compiler.Pipeline.LoweredCompilation mainWorld lowerFuel) where
  sidecars : Sidecars
  hpt : IxIR1.HPT.Production IxIR1.HPT.defaultProducerLimits.checker
    source.lowering.result.artifacts
  certificateProduced : sidecars.hptCertificate = hpt.certificate
  inputProduced : sidecars.input =
    { declarations := source.targetDecls
      main := source.lowering.result.main
      mainResult := mainWorld }

/-- The returned attachment names the exact checked compiler input supplied
to this invocation, even when a frontend has transformed the literal erasure. -/
abbrev CompiledRun {mainWorld : Owned} {lowerFuel : Nat}
    (source : Ix.Compiler.Pipeline.LoweredCompilation mainWorld lowerFuel) :=
  { attached : CompiledAttachment mainWorld lowerFuel // attached.source = source }

/-- Attach and validate structured baseline IxIR₂ in one fail-closed step. -/
def attachCompiled {mainWorld : Owned} {lowerFuel : Nat}
    (compilation : Ix.Compiler.Pipeline.LoweredCompilation mainWorld lowerFuel)
    (built : BuiltCompiledSidecars compilation)
    (maxDepth : Nat := 100000) :
    Except Error (CompiledRun compilation) := do
  let sidecars := built.sidecars
  let loweringContext := sidecars.context maxDepth
  let targetRun ← match Lower.lowerCheckedWithTrace loweringContext
      sidecars.input with
    | .ok checked => pure checked
    | .error error => .error (.lowering error)
  if traceSourcesCoherent :
      sidecars.traceSourcesMatch targetRun.checked.artifact.trace then
    if traceExternFree :
        sidecars.traceExternFree targetRun.checked.artifact.trace then
      if traceExactFetchesCoherent :
          sidecars.traceExactFetchesMatch targetRun.checked.artifact.trace then
        if traceExactCaseTargetsCoherent :
            sidecars.traceExactCaseTargetsMatch
              targetRun.checked.artifact.trace then
          if traceResidualCaseTargetsCoherent :
              sidecars.traceResidualCaseTargetsMatch
                targetRun.checked.artifact.trace then
            if traceScalarLeavesCoherent :
                sidecars.traceScalarLeavesMatch targetRun.checked.artifact.trace then
              if sourceNoReuse :
                  sidecars.sourceNoReuse targetRun.checked.artifact.trace then
                if sourceConstructorsKnown :
                    sidecars.traceConstructorsKnown
                      targetRun.checked.artifact.trace then
                  if pappsSafe :
                      sidecars.tracePappsSafe targetRun.checked.artifact.trace then
                    return ⟨
                      { source := compilation
                        sidecars
                        hpt := built.hpt
                        hptCertificateProduced := built.certificateProduced
                        inputProduced := built.inputProduced
                        maxDepth
                        loweringContext
                        contextProduced := rfl
                        target := targetRun.checked
                        targetProduced := targetRun.produced
                        targetSchemasProduced := Lower.validationSchemas_of_lower targetRun.produced
                        targetSourceProduced := targetRun.source
                        traceSourcesProduced := traceSourcesCoherent
                        traceExternFreeProduced := traceExternFree
                        traceExactFetchesProduced := traceExactFetchesCoherent
                        traceExactCaseTargetsProduced := traceExactCaseTargetsCoherent
                        traceResidualCaseTargetsProduced := traceResidualCaseTargetsCoherent
                        traceScalarLeavesProduced := traceScalarLeavesCoherent
                        sourceNoReuseProduced := sourceNoReuse
                        sourceConstructorsProduced := sourceConstructorsKnown
                        pappSafeProduced := pappsSafe }, rfl⟩
                  else
                    throw (.lowering (.internal
                      "partial application targets a PAP-unsafe declaration"))
                else
                  throw (.lowering (.internal
                    "source constructor allocation escaped the producer universe"))
              else
                throw (.lowering (.internal
                  "source artifact unexpectedly contains a reuse operation"))
            else
              throw (.lowering (.internal
                "shallow-free traces lack exact scalar-leaf HPT evidence"))
          else
            throw (.lowering (.internal
              "ambiguous-HPT case traces lack producer constructor coverage"))
        else
          throw (.lowering (.internal
            "exact-HPT case traces lack their constructor target"))
      else
        throw (.lowering (.internal
          "fetch traces lack exact-constructor HPT evidence"))
    else
      throw (.lowering (.internal
        "extern operation escaped the disabled lowering boundary"))
  else
    throw (.lowering (.internal
      "function traces do not match path-local HPT owners"))

/-- Restore the public source-facing record from the exact common attachment.
The identity proof transports only dependent certificates; executable fields
are the same compiler and analysis results. -/
def Attached.ofCompiled
    {constants : List (Address × Ixon.Constant)} {mainAddress : Address}
    {config : Ix.Compiler.Pipeline.Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (source : Ix.Compiler.Pipeline.ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel)
    (run : CompiledRun source.lowered) :
    Attached constants mainAddress config mainWorld eraseFuel lowerFuel := by
  rcases run with ⟨attached, produced⟩
  rcases attached with ⟨compiler, sidecars, hpt, hptProduced, inputProduced, maxDepth,
    loweringContext, contextProduced, target, targetProduced, targetSchemasProduced,
    targetSourceProduced, traceSourcesProduced, traceExternFreeProduced,
    traceExactFetchesProduced, traceExactCaseTargetsProduced, traceResidualCaseTargetsProduced,
    traceScalarLeavesProduced, sourceNoReuseProduced, sourceConstructorsProduced, pappSafeProduced⟩
  cases produced
  exact {
    source, sidecars, hpt, hptCertificateProduced := hptProduced, inputProduced,
    maxDepth, loweringContext, contextProduced, target, targetProduced, targetSchemasProduced,
    targetSourceProduced, traceSourcesProduced, traceExternFreeProduced, traceExactFetchesProduced,
    traceExactCaseTargetsProduced, traceResidualCaseTargetsProduced, traceScalarLeavesProduced,
    sourceNoReuseProduced, sourceConstructorsProduced, pappSafeProduced }

def attach
    {constants : List (Address × Ixon.Constant)} {mainAddress : Address}
    {config : Ix.Compiler.Pipeline.Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : Ix.Compiler.Pipeline.ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel)
    (maxDepth : Nat := 100000) :
    Except Error (Attached constants mainAddress config mainWorld eraseFuel lowerFuel) := do
  let built ← buildSidecars compilation
  let run ← attachCompiled compilation.lowered
    { sidecars := built.sidecars, hpt := built.hpt
      certificateProduced := built.certificateProduced, inputProduced := built.inputProduced }
    maxDepth
  return Attached.ofCompiled compilation run

/-- Validator-gated source compilation and checked structured IxIR₂
attachment as one executable endpoint. The ordinary production API remains
IxIR₁ while exact source-provenance coverage is still being generalized. -/
def compileValidated (constants : List (Address × Ixon.Constant))
    (mainAddress : Address) (config : Ix.Compiler.Pipeline.Config := {})
    (mainWorld : Owned := .shared)
    (checkFuel : Nat := Ixon.UsageCheck.defaultFuel)
    (eraseFuel : Nat := Erase.defaultFuel)
    (validateFuel : Nat := Erase.defaultFuel)
    (lowerFuel : Nat := 10000) (maxDepth : Nat := 100000) :
    Except Error (Attached constants mainAddress config mainWorld
      eraseFuel lowerFuel) := do
  let compilation ←
    match Ix.Compiler.Pipeline.compileValidatedWithTrace constants mainAddress
        config mainWorld checkFuel eraseFuel validateFuel lowerFuel with
    | .ok compilation => pure compilation
    | .error error => .error (.pipeline error)
  attach compilation maxDepth

end Ix.Compiler.IxIR2.Pipeline
