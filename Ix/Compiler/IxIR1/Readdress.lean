import Ix.Compiler.IxIR1.Serialize

/-!
# IxIR₁ generated-declaration readdressing

The lowering proof works over transient names for lifted lambdas and
constructor wrappers.  This module is the compiled artifact boundary: it
rewrites those names to the BLAKE3 address of each finished declaration.

Generated declarations may refer to other generated declarations, so hashing
is dependency ordered.  `callSelf` contains no address and therefore does not
form a dependency.  A direct generated-address cycle fails closed, as do
temporary-name overlap with source declarations and an observed BLAKE3
collision between distinct preimages.  Identical generated declarations are
content-deduplicated deliberately.

The hash call is native.  Consequently `run` belongs in compiled entry points
and tests, not in elaboration-time `#guard`s.
-/

namespace Ix.Compiler.IxIR1

open Ix.Compiler.Ixon (Address)

namespace Readdress

/-- Old generated name to finished content address. -/
abbrev Renaming := List (Address × Address)

namespace Renaming

/-- Look up one transient generated name. -/
def lookup (mapping : Renaming) (address : Address) : Option Address :=
  (mapping.find? fun entry => entry.1 == address).map (·.2)

/-- Rewrite an address when it names a generated declaration. -/
def apply (mapping : Renaming) (address : Address) : Address :=
  (mapping.lookup address).getD address

/-- Whether the domain already contains this generated name. -/
def contains (mapping : Renaming) (address : Address) : Bool :=
  mapping.any fun entry => entry.1 == address

end Renaming

namespace CtorId

/-- Rewrite the block identity carried by a constructor identity. -/
def mapAddresses (rename : Address → Address) (constructor : CtorId) : CtorId :=
  { constructor with block := rename constructor.block }

end CtorId

namespace Op

/-- Apply an address renaming to every address-bearing operation field. -/
def mapAddresses (rename : Address → Address) : Op → Op
  | .pure atom => .pure atom
  | .alloc world cid args =>
      .alloc world (CtorId.mapAddresses rename cid) args
  | .reuse target cid args =>
      .reuse target (CtorId.mapAddresses rename cid) args
  | .free target => .free target
  | .dup target => .dup target
  | .drop target => .drop target
  | .dropU target => .dropU target
  | .fetch target field => .fetch target field
  | .call function args => .call (rename function) args
  | .callSelf args => .callSelf args
  | .papp function args => .papp (rename function) args
  | .apply function args => .apply function args
  | .extern function args => .extern (rename function) args

/-- Direct semantic address references carried by an operation. -/
def references : Op → List Address
  | .alloc _ cid _ | .reuse _ cid _ => [cid.block]
  | .call function _ | .papp function _ | .extern function _ => [function]
  | _ => []

end Op

mutual

/-- Apply an address renaming throughout code. -/
def Code.mapAddresses (rename : Address → Address) : Code → Code
  | .ret atom => .ret atom
  | .letOp op rest =>
      .letOp (Op.mapAddresses rename op) (Code.mapAddresses rename rest)
  | .case scrutinee peelNat alternatives =>
      .case scrutinee peelNat
        (AltList.mapAddresses rename alternatives.toList).toArray

/-- Apply an address renaming beneath one case alternative. -/
def Alt.mapAddresses (rename : Address → Address) : Alt → Alt
  | .mk constructor fields body =>
      .mk constructor fields (Code.mapAddresses rename body)

/-- Executable walk beneath an alternative array. -/
def AltList.mapAddresses (rename : Address → Address) : List Alt → List Alt
  | [] => []
  | alternative :: rest =>
      Alt.mapAddresses rename alternative :: AltList.mapAddresses rename rest

end

/-! ## Executable structural equality

The mutually nested `Code`/`Alt` syntax does not receive a lawful equality
instance from Lean's deriving machinery.  Readdressing needs a proof-reflecting
comparison at its final semantic audit, so keep the small comparison here
beside the complete address walk. -/

namespace Op

def structurallyEq : Op → Op → Bool
  | .pure left, .pure right => left == right
  | .alloc leftWorld leftCtor leftArgs,
      .alloc rightWorld rightCtor rightArgs =>
      leftWorld == rightWorld && leftCtor == rightCtor &&
        leftArgs == rightArgs
  | .reuse leftTarget leftCtor leftArgs,
      .reuse rightTarget rightCtor rightArgs =>
      leftTarget == rightTarget && leftCtor == rightCtor &&
        leftArgs == rightArgs
  | .free left, .free right
  | .dup left, .dup right
  | .drop left, .drop right
  | .dropU left, .dropU right => left == right
  | .fetch leftTarget leftField, .fetch rightTarget rightField =>
      leftTarget == rightTarget && leftField == rightField
  | .call leftFunction leftArgs, .call rightFunction rightArgs
  | .papp leftFunction leftArgs, .papp rightFunction rightArgs
  | .extern leftFunction leftArgs, .extern rightFunction rightArgs =>
      leftFunction == rightFunction && leftArgs == rightArgs
  | .callSelf left, .callSelf right => left == right
  | .apply leftFunction leftArgs, .apply rightFunction rightArgs =>
      leftFunction == rightFunction && leftArgs == rightArgs
  | _, _ => false

theorem structurallyEq_eq_true_iff (left right : Op) :
    structurallyEq left right = true ↔ left = right := by
  cases left <;> cases right <;>
    simp [structurallyEq, beq_iff_eq, and_assoc]

end Op

mutual

def Code.structurallyEq : Code → Code → Bool
  | .ret left, .ret right => left == right
  | .letOp leftOp leftRest, .letOp rightOp rightRest =>
      Op.structurallyEq leftOp rightOp &&
        Code.structurallyEq leftRest rightRest
  | .case leftScrutinee leftPeel leftAlternatives,
      .case rightScrutinee rightPeel rightAlternatives =>
      leftScrutinee == rightScrutinee && leftPeel == rightPeel &&
        AltList.structurallyEq leftAlternatives.toList
          rightAlternatives.toList
  | _, _ => false

def Alt.structurallyEq : Alt → Alt → Bool
  | .mk leftConstructor leftFields leftBody,
      .mk rightConstructor rightFields rightBody =>
      leftConstructor == rightConstructor && leftFields == rightFields &&
        Code.structurallyEq leftBody rightBody

def AltList.structurallyEq : List Alt → List Alt → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      Alt.structurallyEq left right &&
        AltList.structurallyEq leftRest rightRest
  | _, _ => false

end

mutual

theorem Code.structurallyEq_eq_true_iff (left right : Code) :
    Code.structurallyEq left right = true ↔ left = right := by
  cases left <;> cases right <;>
    simp [Code.structurallyEq, Op.structurallyEq_eq_true_iff,
      Code.structurallyEq_eq_true_iff,
      AltList.structurallyEq_eq_true_iff, beq_iff_eq, and_assoc]

theorem Alt.structurallyEq_eq_true_iff (left right : Alt) :
    Alt.structurallyEq left right = true ↔ left = right := by
  cases left
  cases right
  simp [Alt.structurallyEq, Code.structurallyEq_eq_true_iff,
    beq_iff_eq, and_assoc]

theorem AltList.structurallyEq_eq_true_iff (left right : List Alt) :
    AltList.structurallyEq left right = true ↔ left = right := by
  cases left with
  | nil => cases right <;> simp [AltList.structurallyEq]
  | cons left leftRest =>
      cases right with
      | nil => simp [AltList.structurallyEq]
      | cons right rightRest =>
          simp [AltList.structurallyEq,
            Alt.structurallyEq_eq_true_iff,
            AltList.structurallyEq_eq_true_iff]

end

mutual

/-- Direct and nested semantic address references carried by code. -/
def Code.references : Code → List Address
  | .ret _ => []
  | .letOp op rest => Op.references op ++ Code.references rest
  | .case _ _ alternatives => AltList.references alternatives.toList

/-- Semantic address references beneath one case alternative. -/
def Alt.references : Alt → List Address
  | .mk _ _ body => Code.references body

/-- Executable reference walk beneath an alternative array. -/
def AltList.references : List Alt → List Address
  | [] => []
  | alternative :: rest =>
      Alt.references alternative ++ AltList.references rest

end

namespace FnDef

/-- Apply an address renaming throughout a function declaration. -/
def mapAddresses (rename : Address → Address) (definition : FnDef) : FnDef :=
  { definition with body := Code.mapAddresses rename definition.body }

/-- Semantic address references carried by a function declaration. -/
def references (definition : FnDef) : List Address :=
  Code.references definition.body

def structurallyEq (left right : FnDef) : Bool :=
  left.arity == right.arity && left.result == right.result &&
    left.papSafe == right.papSafe &&
    Code.structurallyEq left.body right.body

theorem structurallyEq_eq_true_iff (left right : FnDef) :
    structurallyEq left right = true ↔ left = right := by
  cases left
  cases right
  simp [structurallyEq, Code.structurallyEq_eq_true_iff,
    beq_iff_eq, and_assoc]

end FnDef

namespace Decl

/-- Apply an address renaming throughout a declaration. -/
def mapAddresses (rename : Address → Address) : Decl → Decl
  | .fn definition => .fn (FnDef.mapAddresses rename definition)
  | .extern arity => .extern arity

/-- Semantic address references carried by a declaration. -/
def references : Decl → List Address
  | .fn definition => FnDef.references definition
  | .extern _ => []

def structurallyEq : Decl → Decl → Bool
  | .fn left, .fn right => FnDef.structurallyEq left right
  | .extern left, .extern right => left == right
  | _, _ => false

theorem structurallyEq_eq_true_iff (left right : Decl) :
    structurallyEq left right = true ↔ left = right := by
  cases left <;> cases right <;>
    simp [structurallyEq, FnDef.structurallyEq_eq_true_iff,
      beq_iff_eq]

end Decl

/-- One completely readdressed lowering result.  Source-backed declaration
keys stay stable, while their bodies are rewritten to the generated content
addresses.  `generated` contains only content-addressed declarations and may
be shorter than `addressMap` when identical declarations deduplicate. -/
structure Result where
  source : List (Address × Decl)
  generated : List (Address × Decl)
  main : Code
  addressMap : Renaming

/-- The environment spelling consumed by the evaluator and pipeline. -/
def Result.declarations (result : Result) : List (Address × Decl) :=
  result.source ++ result.generated

/-- Transient generated names, in dependency-resolution order. -/
def Result.transientAddresses (result : Result) : List Address :=
  result.addressMap.map (·.1)

/-- No emitted declaration key belongs to the transient namespace. -/
def Result.noTransientKeys (result : Result) : Bool :=
  let transient := result.transientAddresses
  !(result.declarations.map (·.1)).any transient.contains

/-- No transient generated name remains in any emitted reference. -/
def Result.noTransientReferences (result : Result) : Bool :=
  let transient := result.transientAddresses
  let declarationReferences :=
    (result.source ++ result.generated).flatMap fun entry =>
      Decl.references entry.2
  !(declarationReferences ++ Code.references result.main).any transient.contains

/-- Every emitted generated key is the canonical address of its declaration.
This audit executes BLAKE3 and therefore belongs in compiled tests. -/
def Result.generatedAreAddressed (result : Result) : Bool :=
  result.generated.all fun entry => entry.1 == entry.2.address

/-- Executable certificate that the emitted environment is the exact
declaration image of the pre-address environment at every raw key, and that
every emitted lookup is already stable under the completed renaming.  The
second clause supplies semantic aliases for newly introduced content keys
without requiring an inverse address map. -/
def Result.semanticAudit (result : Result)
    (raw : List (Address × Decl)) (rawMain : Code) : Bool :=
  let rename := Renaming.apply result.addressMap
  let emitted := Env.ofList result.declarations
  let original := Env.ofList raw
  Code.structurallyEq result.main (Code.mapAddresses rename rawMain) &&
    raw.all (fun entry =>
      match original entry.1, emitted (rename entry.1) with
      | some before, some after =>
          Decl.structurallyEq after (Decl.mapAddresses rename before)
      | _, _ => false) &&
    result.declarations.all (fun entry =>
      match emitted entry.1 with
      | some declaration =>
          Decl.structurallyEq
            (Decl.mapAddresses rename declaration) declaration
      | none => false)

/-- Every protected identity is fixed by the completed address map.  The
production lowerer protects all original IxIR₀ declaration addresses,
including constructors that have no source-backed IxIR₁ declaration entry. -/
def Result.protects (result : Result) (addresses : List Address) : Bool :=
  addresses.all fun address =>
    Renaming.apply result.addressMap address == address

/-- Reflect one member of an executable protection check into equality. -/
theorem Result.apply_eq_of_protects {result : Result}
    {addresses : List Address} (hprotects : result.protects addresses = true)
    {address : Address} (haddress : address ∈ addresses) :
    Renaming.apply result.addressMap address = address := by
  have hequal := (List.all_eq_true.mp hprotects) address haddress
  exact Address.eq_of_beq hequal

/-- A successful post-pass carries an erased proof of its semantic audit.
The subtype proof has no runtime representation in emitted artifacts. -/
abbrev CertifiedResult (raw : List (Address × Decl)) (rawMain : Code) :=
  { result : Result // result.semanticAudit raw rawMain = true }

private def certify (raw : List (Address × Decl)) (rawMain : Code)
    (result : Result) : Except String (CertifiedResult raw rawMain) :=
  if haudit : result.semanticAudit raw rawMain then
    .ok ⟨result, haudit⟩
  else
    .error "internal: generated readdressing failed semantic audit"

private def firstDuplicate? : List Address → Option Address
  | [] => none
  | address :: rest =>
      if rest.contains address then some address else firstDuplicate? rest

private def firstOverlap? (keys : List Address)
    (source : List (Address × Decl)) : Option Address :=
  keys.find? fun key => source.any fun entry => entry.1 == key

private def referencesResolved (keys : List Address)
    (mapping : Renaming) (declaration : Decl) : Bool :=
  (Decl.references declaration).all fun reference =>
    !keys.contains reference || mapping.contains reference

/-- Remove and return the first declaration whose generated dependencies are
already in the renaming.  The residual list preserves its original order. -/
private def takeReady (keys : List Address) (mapping : Renaming) :
    List (Address × Decl) →
      Option ((Address × Decl) × List (Address × Decl))
  | [] => none
  | entry :: rest =>
      if referencesResolved keys mapping entry.2 then
        some (entry, rest)
      else
        match takeReady keys mapping rest with
        | none => none
        | some (ready, residual) => some (ready, entry :: residual)

private def findDeclaration? (address : Address) :
    List (Address × Decl) → Option Decl
  | [] => none
  | entry :: rest =>
      if entry.1 == address then some entry.2
      else findDeclaration? address rest

private structure BuildState where
  addressMap : Renaming := []
  /-- Reverse dependency order while building; reversed once at the end. -/
  generatedRev : List (Address × Decl) := []

private def samePreimage (left right : Decl) : Bool :=
  left.preimage == right.preimage

/-- Record one finished declaration, content-deduplicating an identical
preimage and rejecting an observed address collision with different bytes. -/
private def install (keys : List Address)
    (source : List (Address × Decl)) (old : Address)
    (declaration : Decl) (state : BuildState) : Except String BuildState :=
  let address := declaration.address
  if keys.contains address then
    .error s!"generated content address overlaps temporary namespace {Address.toHex address}"
  else
    match findDeclaration? address source with
    | some _ =>
        .error s!"generated content address collides with source declaration key {Address.toHex address}"
    | none =>
        match findDeclaration? address state.generatedRev with
        | some found =>
            if samePreimage found declaration then
              .ok { state with
                addressMap := (old, address) :: state.addressMap }
            else
              .error s!"BLAKE3 collision while readdressing generated declaration {Address.toHex old}"
        | none =>
            .ok
              { addressMap := (old, address) :: state.addressMap
                generatedRev := (address, declaration) :: state.generatedRev }

private def build (keys : List Address) (source : List (Address × Decl)) :
    Nat → List (Address × Decl) → BuildState → Except String BuildState
  | 0, [], state => .ok state
  | 0, _ :: _, _ =>
      .error "generated declaration address dependency cycle"
  | _ + 1, [], state => .ok state
  | fuel + 1, pending, state =>
      match takeReady keys state.addressMap pending with
      | none => .error "generated declaration address dependency cycle"
      | some ((old, declaration), residual) => do
          let rewritten := Decl.mapAddresses
            (Renaming.apply state.addressMap) declaration
          let state ← install keys source old rewritten state
          build keys source fuel residual state

/-- Rewrite and content-address all generated declarations, retaining an
erased certificate that the resulting evaluator environment is the exact
semantic address image of the raw one.

`source` contains source-backed declarations whose keys must remain stable;
`generated` contains transiently keyed lifts/wrappers.  The result is
dependency ordered, exact-content deduplicated, and includes the complete
old-to-new provenance map. -/
def runCertified (source generated : List (Address × Decl)) (main : Code) :
    Except String (CertifiedResult (source ++ generated) main) := do
  if generated.isEmpty then
    return ← certify (source ++ generated) main
      { source, generated := [], main, addressMap := [] }
  let keys := generated.map (·.1)
  if let some duplicate := firstDuplicate? keys then
    throw s!"duplicate generated temporary address {Address.toHex duplicate}"
  if let some overlap := firstOverlap? keys source then
    throw s!"generated temporary address overlaps source declaration {Address.toHex overlap}"
  let state ← build keys source keys.length generated {}
  let addressMap := state.addressMap.reverse
  let rename := Renaming.apply addressMap
  let result : Result :=
    { source := source.map fun entry =>
        (entry.1, Decl.mapAddresses rename entry.2)
      generated := state.generatedRev.reverse
      main := Code.mapAddresses rename main
      addressMap }
  unless result.noTransientKeys do
    throw "internal: generated readdressing emitted a transient key"
  unless result.noTransientReferences do
    throw "internal: generated readdressing left a transient reference"
  certify (source ++ generated) main result

/-- Artifact-facing projection of `runCertified`. -/
def run (source generated : List (Address × Decl)) (main : Code) :
    Except String Result := do
  return (← runCertified source generated main).1

/-- Run the ordinary certified post-pass and additionally reject any result
whose renaming changes a caller-protected identity.  This closes the
constructor-address gap at the production lowering boundary: constructors
are absent from the IxIR₁ declaration environment but their IxIR₀ keys still
occur in `CtorId.block` and must remain stable. -/
def runProtected (reserved : List Address)
    (source generated : List (Address × Decl)) (main : Code) :
    Except String Result := do
  let result ← run source generated main
  if _hprotects : result.protects reserved then
    return result
  else
    throw "generated address map rewrites a protected source identity"

/-- A successful protected run is also a successful ordinary certified run
and carries the requested fixed-identity audit. -/
theorem run_and_protects_of_runProtected_eq_ok
    {reserved : List Address}
    {source generated : List (Address × Decl)} {main : Code}
    {result : Result}
    (hrun : runProtected reserved source generated main = .ok result) :
    run source generated main = .ok result ∧
      result.protects reserved = true := by
  unfold runProtected at hrun
  cases hbase : run source generated main with
  | error message =>
      rw [hbase] at hrun
      change Except.error message = Except.ok result at hrun
      contradiction
  | ok candidate =>
      rw [hbase] at hrun
      change
        (if candidate.protects reserved = true then
          Except.ok candidate
        else
          Except.error
            "generated address map rewrites a protected source identity") =
          Except.ok result at hrun
      by_cases hprotects : candidate.protects reserved = true
      · rw [if_pos hprotects] at hrun
        have hresult : candidate = result := by injection hrun
        subst result
        exact ⟨rfl, hprotects⟩
      · rw [if_neg hprotects] at hrun
        contradiction

/-- Every successful artifact-facing run retains the erased semantic
certificate constructed by `runCertified`. -/
theorem semanticAudit_of_run_eq_ok
    {source generated : List (Address × Decl)} {main : Code}
    {result : Result}
    (hrun : run source generated main = .ok result) :
    result.semanticAudit (source ++ generated) main = true := by
  unfold run at hrun
  cases hcertified : runCertified source generated main with
  | error message =>
      rw [hcertified] at hrun
      contradiction
  | ok certified =>
      rw [hcertified] at hrun
      have hvalue : certified.1 = result := by injection hrun
      subst result
      exact certified.2

/-- Protected runs retain the same semantic audit as ordinary runs. -/
theorem semanticAudit_of_runProtected_eq_ok
    {reserved : List Address}
    {source generated : List (Address × Decl)} {main : Code}
    {result : Result}
    (hrun : runProtected reserved source generated main = .ok result) :
    result.semanticAudit (source ++ generated) main = true :=
  semanticAudit_of_run_eq_ok
    (run_and_protects_of_runProtected_eq_ok hrun).1

/-! Pure structural format guards.  Hashing behavior is pinned by the compiled
test executable. -/

private def fixtureOldA : Address := Address.replicate 0xFA
private def fixtureOldB : Address := Address.replicate 0xFB
private def fixtureNewA : Address := Address.replicate 0x0A
private def fixtureNewB : Address := Address.replicate 0x0B

private def fixtureCode : Code :=
  .letOp (.call fixtureOldA #[])
    (.case (.var 0) false
      #[.mk 0 0 (.letOp (.papp fixtureOldB #[]) (.ret (.var 0)))])

private def fixtureOps : List Op :=
  [.alloc .shared ⟨fixtureOldA, 0, 0⟩ #[],
   .reuse .erased ⟨fixtureOldA, 0, 1⟩ #[],
   .call fixtureOldA #[],
   .papp fixtureOldB #[],
   .extern fixtureOldA #[]]

private def fixtureMap : Renaming :=
  [(fixtureOldA, fixtureNewA), (fixtureOldB, fixtureNewB)]

#guard Code.references fixtureCode == [fixtureOldA, fixtureOldB]
#guard fixtureOps.flatMap Op.references ==
  [fixtureOldA, fixtureOldA, fixtureOldA, fixtureOldB, fixtureOldA]
#guard (fixtureOps.map (Op.mapAddresses (Renaming.apply fixtureMap))).flatMap
    Op.references ==
  [fixtureNewA, fixtureNewA, fixtureNewA, fixtureNewB, fixtureNewA]
#guard
  Code.references
    (Code.mapAddresses
      (Renaming.apply fixtureMap)
      fixtureCode) == [fixtureNewA, fixtureNewB]

end Readdress

end Ix.Compiler.IxIR1
