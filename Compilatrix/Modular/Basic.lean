import Compilatrix.Modular.Transport
import Compilatrix.Pipeline
import Compilatrix.IxIR.Bounded

/-! Finite inputs and exact lookup checks for modular source certification. -/

deriving instance DecidableEq for Compilatrix.Ixon.Axiom
deriving instance DecidableEq for Compilatrix.Ixon.Quotient
deriving instance DecidableEq for Compilatrix.Ixon.InductiveProj
deriving instance DecidableEq for Compilatrix.Ixon.ConstructorProj
deriving instance DecidableEq for Compilatrix.Ixon.RecursorProj
deriving instance DecidableEq for Compilatrix.Ixon.DefinitionProj
deriving instance DecidableEq for Compilatrix.Ixon.ConstantInfo
deriving instance DecidableEq for Compilatrix.Ixon.Constant
deriving instance DecidableEq for Compilatrix.Ixon.Eval.Blob
deriving instance DecidableEq for Compilatrix.Pipeline.Limits

namespace Compilatrix.Modular

open Ixon (Address Constant)
open IxIR

def schema : String := "compilatrix/source-unit/1"

/-- The strict, closed source semantics of the existing validated pipeline.
Every field is included in the certificate query. Bounds of the monolithic
entry point are unchanged. -/
structure Policy where
  unit : Pipeline.Limits := {}
  checkFuel : Nat := 10000
  eraseFuel : Nat := 10000
  validateFuel : Nat := 10000
  lowerFuel : Nat := 10000
  deriving DecidableEq, Repr

def Policy.bytes (policy : Policy) : ByteArray :=
  Encoding.string schema ++
  Encoding.string "ixon-v2/local-sharing/strict/no-extern/no-quotient/1" ++
  Encoding.string "PErase/MemberCoverage/1;SharingWF;OracleRel" ++
  Encoding.string "budget/public-candidates+executable-members/1" ++
  Encoding.list Encoding.nat [policy.checkFuel, policy.eraseFuel,
    policy.validateFuel, policy.lowerFuel,
    policy.unit.maxConstants, policy.unit.maxExpressionUnits,
    policy.unit.maxExpandedExpressionUnits, policy.unit.maxLayer1NodeVisits,
    policy.unit.maxErasedDeclarations, policy.unit.maxErasureAppendCells,
    policy.unit.maxCertificateCandidates,
    policy.unit.maxCertificateValidationAttempts,
    policy.unit.maxCertificateSourceNodeWork, policy.unit.maxUsageFuel,
    policy.unit.maxErasureFuel, policy.unit.maxValidationFuel,
    policy.unit.maxLoweringFuel]

/-- Aggregate bounds apply even when every individual unit fits. -/
structure Limits where
  maxUnits : Nat := 256
  maxConstants : Nat := 16384
  maxCandidates : Nat := 8192
  maxExpandedUnits : Nat := 1048576
  maxImportBindings : Nat := 1048576
  maxCertificateWork : Nat := 1073741824
  maxBytes : Nat := 67108864
  maxExprDepth : Nat := 512
  record : IxIR.Bounded.Limits := { maxBytes := 16777216 }
  deriving DecidableEq, Repr

def ensure (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

def checked (result : Except Pipeline.Error α) : Except String α :=
  result.mapError (fun error => reprStr error)

abbrev SourceEntries := List (Address × Constant)
abbrev BlobEntries := List (Address × Ixon.Eval.Blob)
abbrev TargetEntries := List (Address × IxIR0.Decl)

def sourceEntryBytes (entry : Address × Constant) : ByteArray :=
  Encoding.address entry.1 ++ Encoding.blob (Ixon.constantBytes entry.2)

def blobBytes : Ixon.Eval.Blob → ByteArray
  | .natB value => Encoding.tag 0 ++ Encoding.nat value
  | .strB value => Encoding.tag 1 ++ Encoding.string value

def blobEntryBytes (entry : Address × Ixon.Eval.Blob) : ByteArray :=
  Encoding.address entry.1 ++ blobBytes entry.2

def targetEntryBytes (entry : Address × IxIR0.Decl) : ByteArray :=
  Encoding.address entry.1 ++ Encoding.blob entry.2.preimage

def optionAddressBytes : Option Address → ByteArray
  | none => Encoding.tag 0
  | some value => Encoding.tag 1 ++ Encoding.address value

/-- A unit owns whole Ixon constants, including whole mutual blocks.
Imports name other units; exports are the exact public coverage candidates.
Literals are finite source inputs, not anonymous functions hidden in a key. -/
structure Input where
  name : String
  constants : SourceEntries
  blobs : BlobEntries := []
  natBlock : Option Address := none
  imports : List String := []
  deriving DecidableEq, Repr

def candidates (constants : SourceEntries) : List Address :=
  constants.filterMap fun entry => match entry.2.info with
    | .muts _ => none
    | _ => some entry.1

/-- Mutual members are proof obligations even when their owning constant has
no public coverage candidate. Charge them before certificate work begins. -/
def proofObligations (constants : SourceEntries) : Nat :=
  (Ixon.Work.programStats constants).certificateCandidates +
    (Pipeline.programMemberPlan constants).length

def proofAttempts (constants : SourceEntries) : Nat :=
  Ixon.Work.certificateAttempts (proofObligations constants)

def proofWork (owned context : SourceEntries) : Nat :=
  proofAttempts owned * (Ixon.Work.programStats context).expandedExpressionUnits

def preflightUnit (policy : Policy) (constants : SourceEntries) : Except String Unit := do
  let _ ← checked (Pipeline.preflightValidated policy.unit constants policy.checkFuel
    policy.eraseFuel policy.validateFuel policy.lowerFuel)
  ensure (proofObligations constants ≤ policy.unit.maxCertificateCandidates)
    "unit certificate proof-obligation limit"
  ensure (proofAttempts constants ≤ policy.unit.maxCertificateValidationAttempts)
    "unit certificate proof-attempt limit"
  ensure (proofWork constants constants ≤ policy.unit.maxCertificateSourceNodeWork)
    "unit certificate source-node work limit"

def Input.bytes (input : Input) : ByteArray :=
  Encoding.string input.name ++ Encoding.list sourceEntryBytes input.constants ++
  Encoding.list blobEntryBytes input.blobs ++ optionAddressBytes input.natBlock ++
  Encoding.list Encoding.string input.imports ++
  Encoding.list Encoding.address (candidates input.constants)

/-- All imported bindings are exact. Equal duplicates from a diamond are
coalesced; a conflicting source, blob, or target binding is an error. -/
def unionEntries [DecidableEq α] (entries : List (Address × α)) :
    Except String (List (Address × α)) := do
  let mut index : AddressEnv.Index α := {}
  let mut result := []
  for (address, value) in entries do
    match index.get? address with
    | none =>
        index := index.insert address value
        result := (address, value) :: result
    | some previous =>
        unless previous = value do throw "conflicting imported binding"
  return result.reverse

def lookup (entries : List (Address × α)) : Address → Option α :=
  AddressEnv.lookup (AddressEnv.build entries)

theorem lookup_supported (entries : List (Address × α))
    (resolve : Address → Option α)
    (bindings : ∀ entry ∈ entries, resolve entry.1 = some entry.2)
    {address value} (found : lookup entries address = some value) :
    resolve address = some value := by
  simp only [lookup, AddressEnv.lookup_build] at found
  cases h : entries.find? (fun entry => entry.1 == address) with
  | none => simp [h] at found
  | some entry =>
      have heq : entry.2 = value := by simpa [h] using found
      have hmem := List.mem_of_find?_eq_some h
      have hkey : entry.1 = address := by
        have predicate : (entry.1 == address) = true :=
          List.find?_some (p := fun (item : Address × α) => item.1 == address) h
        exact beq_iff_eq.mp predicate
      simpa [hkey, heq] using bindings entry hmem

/-- A finite exact comparison returns the logical environment extension.
Hash equality is never used to prove equality of source or target syntax. -/
def checkExtension [DecidableEq α] (entries : List (Address × α))
    (resolve : Address → Option α) :
    Except String (PLift (∀ {address value}, lookup entries address = some value →
      resolve address = some value)) :=
  if h : ∀ entry ∈ entries, resolve entry.1 = some entry.2 then
    .ok ⟨lookup_supported entries resolve h⟩
  else .error "stale or incompatible imported binding"

structure Context where
  constants : SourceEntries
  blobs : BlobEntries
  declarations : TargetEntries
  natBlock : Option Address

def Context.source (context : Context) : Ixon.Eval.EvalCtx :=
  let sourceIndex := AddressEnv.build context.constants
  let blobIndex := AddressEnv.build context.blobs
  { resolve := AddressEnv.lookup sourceIndex, blobs := AddressEnv.lookup blobIndex,
    natBlock := context.natBlock }

def Context.target (context : Context) : IxIR0.Ctx :=
  let index := AddressEnv.build context.declarations
  { env := AddressEnv.lookup index }

@[instance_reducible] def Context.scope (context : Context) : Sim.MemberScope :=
  { plan := Pipeline.programMemberPlan context.constants }

theorem Context.strict (context : Context) : context.source.Strict := ⟨rfl, rfl⟩

def Context.extension (before after : Context) : Except String
    (PLift (Sim.ContextExtension before.source before.target after.source after.target)) := do
  let source ← checkExtension before.constants after.source.resolve
  let blob ← checkExtension before.blobs after.source.blobs
  let decl ← checkExtension before.declarations after.target.env
  if hnat : before.natBlock = after.natBlock then
    return ⟨{
      source := source.down, blob := blob.down, declaration := decl.down
      externArity := fun h => by cases h
      quotientKind := fun h => by cases h
      natBlock := hnat, strict := fun _ => after.strict }⟩
  else throw "incompatible Nat identity"

def Context.scopeExtension (before after : Context) :
    Except String (PLift (before.scope.plan ⊆ after.scope.plan)) :=
  if h : before.scope.plan ⊆ after.scope.plan then .ok ⟨h⟩
  else .error "imported mutual group is not present in the destination scope"

/-- Bounded structural checks shared by typed and byte-level evidence ingress. -/
def exprFits (bounds : Bounded.Limits) : Nat → IxIR0.Expr → Bool
  | 0, _ => false
  | depth + 1, expr => match expr with
    | .var index => Bounded.natFits bounds index
    | .ref _ | .erased => true
    | .app fn arg => exprFits bounds depth fn && exprFits bounds depth arg
    | .lam _ body => exprFits bounds depth body
    | .letE _ value body => exprFits bounds depth value && exprFits bounds depth body
    | .proj index value => Bounded.natFits bounds index && exprFits bounds depth value
    | .lit (.nat value) => Bounded.natFits bounds value
    | .lit (.str value) => Bounded.stringFits bounds value

def declFits (limits : Limits) : IxIR0.Decl → Bool
  | .defn _ body => exprFits limits.record limits.maxExprDepth body
  | .ctor tag arity => Bounded.natFits limits.record tag && Bounded.natFits limits.record arity
  | .recursor arity _ rules => Bounded.natFits limits.record arity &&
      Bounded.arrayFits limits.record (fun rule => Bounded.natFits limits.record rule.fields &&
        exprFits limits.record limits.maxExprDepth rule.rhs) rules
  | .extern arity => Bounded.natFits limits.record arity

end Compilatrix.Modular
