import Tests.Ix.IxVM
import Tests.Ix.IxVM.GuardBatchDefs
import IxC.Kernel.Admission
import IxC.Kernel.Cached.Installed
import Ix.Address.Pure

/-! # The declaration checker's shape guards

Four guards narrow what the declaration checker accepts to shapes the certified compiler
writes. Each has cases that must now be refused and cases that must stay accepted.

* **One kind of member per inductive block.** A block that holds both an inductive and a
  recursor is refused at its inductive, whether the claim walks the block or assumes it
  and so checks the inductive alone. The same family as an inductive block and a recursor
  record of its own is accepted.
* **No later use of a recursive field.** A constructor whose later field names an earlier
  recursive field is refused when its type is claimed without its recursor, and when its
  recursor is claimed. Recursive and reflexive fields that nothing later uses are accepted.
* **A recursor's header is plain syntax.** A `let` in a motive's domain, an index's domain,
  the major premise's domain or the result is refused, on the native route and on the
  modeled route. A `let` in a parameter's or a minor premise's domain is accepted, and so
  is a type-annotation wrapper that the stored recursor dropped from a minor premise.
* **A stored `let` is the generated one.** A recursor whose type has a `let` where the
  generated recursor has none is refused (a rule under such a `let` is refused in
  `ixvm-claim-safety`). A `let` the family carries into its recursor, in a parameter's or
  a field's domain, is in both and is accepted.

`IX_GUARD_BATCH_BEFORE`, when set, expects the verdicts of a program without the guards:
each refused shape was accepted, or refused by a later check, which the case names. It
shows that every refusal here is the guard's own. Set to `lets`, it expects the verdicts of
a program with the first three guards and without the fourth. -/

namespace Tests.Ix.IxVM.GuardBatch

open Ix.Kernel Ix.Kernel.Reader Tests.Ix.IxVM IxVM.ClaimHarness

/-! ## Expectations -/

/-- A shape a guard refuses with `guard`. Without the guards it got `before`: an
acceptance (`none`), or a later check's refusal. -/
private def refused (guards : Bool) (guard : String) (before : Option String) (c : Case) : Case :=
  if guards then { c with accept := false, rejectsWith := some guard }
  else match before with
    | none => { c with accept := true, rejectsWith := none }
    | some message => { c with accept := false, rejectsWith := some message }

private def mixedMessage : String := "mutual block mixes inductives with recursors"
private def laterUseMessage : String :=
  "a later field or the constructor's result mentions a recursive field"

/-! ## Compiled fixtures -/

private def defs (n : String) : Lean.Name := `Tests.Ix.IxVM.GuardBatchDefs ++ n.toName

private partial def exprHasLet : Ixon.Expr → Bool
  | .letE _ _ _ _ _ => true
  | .app f a => exprHasLet f || exprHasLet a
  | .lam t b => exprHasLet t || exprHasLet b
  | .all t b => exprHasLet t || exprHasLet b
  | .prj _ _ e => exprHasLet e
  | _ => false

/-- Whether a standalone recursor record carries a `let` in its type. -/
private def recursorHasLet (c : Ixon.Constant) : Bool :=
  match c.info with
  | .recr r => exprHasLet r.typ || c.sharing.any exprHasLet
  | _ => false

/-- `build`, once the record of `name` has the shape the case is about. -/
private def shaped (env : Ixon.Env) (name : Lean.Name) (what : String)
    (shape : Ixon.Constant → Bool) (build : Builder) : Builder := fun u => do
  let some address := env.getAddr? (Ix.Name.fromLeanName name)
    | throw s!"{name} is not in the Ixon environment"
  let some record := env.getConst? address | throw s!"{name} has no record"
  unless shape record do throw s!"{name}: the fixture has no {what}"
  build u

/-- Whether the block of the inductive type recorded at `c` names the constant `wrapper`. -/
private def blockNames (env : Ixon.Env) (wrapper : Lean.Name) (c : Ixon.Constant) : Bool :=
  match c.info, env.getAddr? (Ix.Name.fromLeanName wrapper) with
  | .iPrj p, some w => match env.getConst? p.block with
    | some block => block.refs.contains w
    | none => false
  | _, _ => false

private def compiledCases (guards : Bool) (env : Ixon.Env) : Array Builder :=
  let accepted (n : String) : Builder := kernelCheckCase env (defs n) true
  let declined (n : String) : Builder := fun u => do
    return refused guards laterUseMessage (some "strict positivity: non-syntactic")
      (← kernelCheckCase env (defs n) true u)
  #[accepted "FieldLet",
    shaped env (defs "FieldLet.rec") "let" recursorHasLet (accepted "FieldLet.rec"),
    accepted "ParamLet",
    shaped env (defs "ParamLet.rec") "let" recursorHasLet (accepted "ParamLet.rec"),
    shaped env (defs "FieldWrapper") "wrapper" (blockNames env ``optParam) (accepted "FieldWrapper"),
    fun u => do
      return { (← accepted "FieldWrapper.rec" u) with
        exercises := some "KernelCheck::consume_wrapper" },
    shaped env (defs "ParamWrapper") "wrapper" (blockNames env ``outParam) (accepted "ParamWrapper"),
    fun u => do
      return { (← accepted "ParamWrapper.rec" u) with
        exercises := some "KernelCheck::consume_wrapper" },
    accepted "RecFirst", accepted "RecFirst.rec",
    accepted "ReflIdx", accepted "ReflIdx.rec",
    declined "UsedLater", declined "UsedLater.rec"]

private def compiledNames : List Lean.Name :=
  ["FieldLet", "FieldLet.rec", "ParamLet", "ParamLet.rec", "FieldWrapper", "FieldWrapper.rec",
    "ParamWrapper", "ParamWrapper.rec", "RecFirst", "RecFirst.rec", "ReflIdx", "ReflIdx.rec",
    "UsedLater", "UsedLater.rec"].map defs

/-! ## An inductive and its recursor in one block -/

private def address (c : Ixon.Constant) : _root_.Address := _root_.Address.blake3 (Ixon.ser c)

/-- A family in `Type` with no constructor. -/
private def emptyFamily : Ixon.Inductive :=
  { isUnsafe := false, lvls := 0, params := 0, indices := 0, typ := .sort 0, ctors := #[] }

/-- Its recursor, `(motive : T → Sort u) → (t : T) → motive t`, naming it by `carrier`. -/
private def emptyRecursor (carrier : Ixon.Expr) : Ixon.Recursor :=
  { k := false, isUnsafe := false, lvls := 1, params := 0, indices := 0, motives := 1, minors := 0,
    typ := .all (.all carrier (.sort 1)) (.all carrier (.app (.var 1) (.var 0))), rules := #[] }

/-- The family and its recursor in one block, claimed at the inductive. With `assumed` the
block is an assumption of the claim, so the claim walk checks the inductive alone: without
the guard that check passes. Otherwise the walk goes on into the block and, without the
guard, stops at the recursor member, whose type the program reads with no member of its
block in scope. -/
private def mixedCase (guards assumed : Bool) : Except String Case := do
  let env ← IxVM.ClaimHarness.withRoleTable {} (← defaultTableBytes)
  let block ← IxVM.RecordSections.withSection env
    ⟨.muts #[.indc emptyFamily, .recr (emptyRecursor (.recur 0 #[]))], #[], #[],
      #[.succ .zero, .var 0], #[]⟩
  let blockAddress := address block
  let type : Ixon.Constant := ⟨.iPrj ⟨0, blockAddress⟩, #[], #[], #[], #[]⟩
  let recursor : Ixon.Constant := ⟨.rPrj ⟨1, blockAddress⟩, #[], #[], #[], #[]⟩
  let env := ((env.storeConst blockAddress block).storeConst (address type) type).storeConst
    (address recursor) recursor
  let context ← Ix.ClaimContext.ofEnv env
  let tree? := if assumed then Ix.AssumptionTree.canonical #[blockAddress] else none
  let trees : Std.HashMap _root_.Address Ix.AssumptionTree := match tree? with
    | some tree => ({} : Std.HashMap _root_.Address Ix.AssumptionTree).insert tree.root tree
    | none => {}
  let witness ← IxVM.ClaimHarness.buildClaimWitness env
    (.check context (address type) (tree?.map (·.root))) trees
  return refused guards mixedMessage (if assumed then none else some "let pattern mismatch") {
    label := if assumed then "an inductive and its recursor in one block, the block assumed"
      else "an inductive and its recursor in one block, the block walked"
    accept := true
    witness := witness }

/-- The same family as an inductive block and a recursor record of its own. -/
private def separateCase : Except String Case := do
  let env ← IxVM.ClaimHarness.withRoleTable {} (← defaultTableBytes)
  let block ← IxVM.RecordSections.withSection env
    ⟨.muts #[.indc emptyFamily], #[], #[], #[.succ .zero], #[]⟩
  let blockAddress := address block
  let type : Ixon.Constant := ⟨.iPrj ⟨0, blockAddress⟩, #[], #[], #[], #[]⟩
  let env := (env.storeConst blockAddress block).storeConst (address type) type
  let recursor ← IxVM.RecordSections.withSection env
    ⟨.recr (emptyRecursor (.ref 0 #[])), #[], #[address type], #[.succ .zero, .var 0], #[]⟩
  let env := env.storeConst (address recursor) recursor
  let context ← Ix.ClaimContext.ofEnv env
  let witness ← IxVM.ClaimHarness.buildClaimWitness env (.check context (address recursor) none)
  return {
    label := "an inductive block and its recursor's own record"
    accept := true
    exercises := some "KernelCheck::nat_rec_check"
    witness := witness }

/-! ## A `let` in a recursor's header -/

/-- Where a recursor's stored type carries a `let`. -/
inductive LetAt where
  | nowhere | motive | index | major | result
  deriving BEq

private def LetAt.label : LetAt → String
  | .nowhere => "no let"
  | .motive => "a let in the motive's domain"
  | .index => "a let in the index's domain"
  | .major => "a let in the major premise's domain"
  | .result => "a let in the result"

/-- The guard's refusal, and the verdict without the guards. -/
private def LetAt.verdict (guards : Bool) (c : Case) : LetAt → Case
  | .nowhere => c
  | .motive => refused guards "recursor header: a let in a motive's domain" none c
  | .index => refused guards "recursor header: a let in an index's domain" none c
  | .major => refused guards "recursor header: a let in the major premise's domain"
      (some "recursor major premise is not its inductive at its own levels, parameters and indices") c
  | .result => refused guards "recursor header: a let in the result" none c

/-- The recursor type of a family `T : Nat → Sort 3` without constructors,
`(motive : (i : Nat) → T i → Sort u) → (i : Nat) → (t : T i) → motive i t`, with
`let z : Nat := Nat.zero` at `place`. References: the family, `Nat`, `Nat.zero`. -/
private def headerType (place : LetAt) : Ixon.Expr :=
  let nat : Ixon.Expr := .ref 1 #[]
  let bind (body : Ixon.Expr) : Ixon.Expr := .leanLet true nat (.ref 2 #[]) body
  let carrier (index : Ixon.Expr) : Ixon.Expr := .app (.ref 0 #[]) index
  let motiveTail : Ixon.Expr := if place == .motive then
    bind (.all (carrier (.var 1)) (.sort 1)) else .all (carrier (.var 0)) (.sort 1)
  let indexDomain : Ixon.Expr := if place == .index then bind nat else nat
  let majorDomain : Ixon.Expr := if place == .major then
    carrier (bind (.var 1)) else carrier (.var 0)
  let result : Ixon.Expr := if place == .result then
    bind (.app (.app (.var 3) (.var 2)) (.var 1)) else .app (.app (.var 2) (.var 1)) (.var 0)
  .all (.all nat motiveTail) (.all indexDomain (.all majorDomain result))

private def indexedRecursor (motives : UInt64) (typ : Ixon.Expr) : Ixon.Recursor :=
  { k := false, isUnsafe := false, lvls := 1, params := 0, indices := 1, motives := motives,
    minors := 0, typ := typ, rules := #[] }

/-- A native family's recursor with a `let` at `place`. -/
private def nativeHeaderCase (guards : Bool) (place : LetAt) : Except String Case := do
  let env ← IxVM.ClaimHarness.withRoleTable {} (← defaultTableBytes)
  let table ← defaultTable
  let some nat := table.addressOf? .nat | throw "missing Nat"
  let some zero := table.addressOf? .natZero | throw "missing Nat.zero"
  let family : Ixon.Inductive := {
    isUnsafe := false, lvls := 0, params := 0, indices := 1,
    typ := .all (.ref 0 #[]) (.sort 0), ctors := #[] }
  let block ← IxVM.RecordSections.withSection env
    ⟨.muts #[.indc family], #[], #[nat], #[.succ (.succ (.succ .zero))], #[]⟩
  let blockAddress := address block
  let type : Ixon.Constant := ⟨.iPrj ⟨0, blockAddress⟩, #[], #[], #[], #[]⟩
  let env := (env.storeConst blockAddress block).storeConst (address type) type
  let record ← IxVM.RecordSections.withSection env
    ⟨.recr (indexedRecursor 1 (headerType place)), #[], #[address type, nat, zero],
      #[.succ .zero, .var 0], #[]⟩
  let env := env.storeConst (address record) record
  let context ← Ix.ClaimContext.ofEnv env
  let witness ← IxVM.ClaimHarness.buildClaimWitness env (.check context (address record) none)
  return place.verdict guards {
    label := s!"native recursor: {place.label}"
    accept := true
    exercises := if place == .nowhere then some "KernelCheck::nat_rec_check" else none
    witness := witness }

/-- The recursor of member `member` of a two-type family `P Q : Nat → Sort 3` without
constructors, with a `let` in its index's domain when `wrapped`. References: `P`, `Q`,
`Nat`, `Nat.zero`. -/
private def modeledType (member : UInt64) (wrapped : Bool) : Ixon.Expr :=
  let nat : Ixon.Expr := .ref 2 #[]
  let carrier (member index : UInt64) : Ixon.Expr := .app (.ref member #[]) (.var index)
  let motive (member : UInt64) : Ixon.Expr := .all nat (.all (carrier member 0) (.sort 1))
  let indexDomain : Ixon.Expr := if wrapped then .leanLet true nat (.ref 3 #[]) nat else nat
  let result : Ixon.Expr := .app (.app (.var (3 - member)) (.var 1)) (.var 0)
  .all (motive 0) (.all (motive 1) (.all indexDomain (.all (carrier member 0) result)))

/-- A modeled family's recursors, the first with a `let` in its index's domain when
`wrapped`, claimed with the model advice generated for that family record. -/
private def modeledHeaderCase (guards wrapped : Bool) : Except String Case := do
  let env ← IxVM.ClaimHarness.withRoleTable {} (← defaultTableBytes)
  let table ← defaultTable
  let some nat := table.addressOf? .nat | throw "missing Nat"
  let some zero := table.addressOf? .natZero | throw "missing Nat.zero"
  let family : Ixon.Inductive := {
    isUnsafe := false, lvls := 0, params := 0, indices := 1,
    typ := .all (.ref 0 #[]) (.sort 0), ctors := #[] }
  let block ← IxVM.RecordSections.withSection env
    ⟨.muts #[.indc family, .indc family], #[], #[nat], #[.succ (.succ (.succ .zero))], #[]⟩
  let blockAddress := address block
  let p : Ixon.Constant := ⟨.iPrj ⟨0, blockAddress⟩, #[], #[], #[], #[]⟩
  let q : Ixon.Constant := ⟨.iPrj ⟨1, blockAddress⟩, #[], #[], #[], #[]⟩
  let env := ((env.storeConst blockAddress block).storeConst (address p) p).storeConst (address q) q
  let recursors ← IxVM.RecordSections.withSection env
    ⟨.muts #[.recr (indexedRecursor 2 (modeledType 0 wrapped)),
        .recr (indexedRecursor 2 (modeledType 1 false))],
      #[], #[address p, address q, nat, zero], #[.succ .zero, .var 0], #[]⟩
  let recursorsAddress := address recursors
  let env := env.storeConst recursorsAddress recursors
  let rp : Ixon.Constant := ⟨.rPrj ⟨0, recursorsAddress⟩, #[], #[], #[], #[]⟩
  let rq : Ixon.Constant := ⟨.rPrj ⟨1, recursorsAddress⟩, #[], #[], #[], #[]⟩
  let env := (env.storeConst (address rp) rp).storeConst (address rq) rq
  let (env, report) ← IxVM.Model.generateReport env
  unless report.advice.size > 0 do
    throw s!"no model advice: {reprStr (report.blocks.map (fun (_, answer) => answer))}"
  let context ← Ix.ClaimContext.ofEnv env
  let witness ← IxVM.ClaimHarness.buildClaimWitness env (.check context recursorsAddress none)
  let c : Case := {
    label := if wrapped then "modeled recursor: a let in the index's domain"
      else "modeled recursors: no let"
    accept := true
    witness := witness }
  return if wrapped then
    refused guards "recursor header: a let in an index's domain" none c else c

/-! ## The suite -/

/-! ## A `let` the stored recursor has and the generated one has not -/

/-- The recursor of a family `T : Nat → Nat → Sort 3` with one parameter and no constructor,
`(p : Nat) → (motive : (i : Nat) → T p i → Sort u) → (i : Nat) → (t : T p i) → motive i t`.
When `dead`, the stored parameter domain is `let z : Nat := Nat.zero; Nat`: the generated
recursor takes the family's own parameter domain, `Nat`, which has no `let`. Without the
structural comparison of `let`s (`lets = false`) the stored `let` was expanded and the
record accepted. -/
private def parameterLetCase (lets dead : Bool) : Except String Case := do
  let env ← IxVM.ClaimHarness.withRoleTable {} (← defaultTableBytes)
  let table ← defaultTable
  let some nat := table.addressOf? .nat | throw "missing Nat"
  let some zero := table.addressOf? .natZero | throw "missing Nat.zero"
  let family : Ixon.Inductive := {
    isUnsafe := false, lvls := 0, params := 1, indices := 1,
    typ := .all (.ref 0 #[]) (.all (.ref 0 #[]) (.sort 0)), ctors := #[] }
  let block ← IxVM.RecordSections.withSection env
    ⟨.muts #[.indc family], #[], #[nat], #[.succ (.succ (.succ .zero))], #[]⟩
  let blockAddress := address block
  let type : Ixon.Constant := ⟨.iPrj ⟨0, blockAddress⟩, #[], #[], #[], #[]⟩
  let env := (env.storeConst blockAddress block).storeConst (address type) type
  let natE : Ixon.Expr := .ref 1 #[]
  let carrier (p i : Ixon.Expr) : Ixon.Expr := .app (.app (.ref 0 #[]) p) i
  let parameter : Ixon.Expr := if dead then .leanLet true natE (.ref 2 #[]) natE else natE
  let typ : Ixon.Expr := .all parameter
    (.all (.all natE (.all (carrier (.var 1) (.var 0)) (.sort 1)))
      (.all natE (.all (carrier (.var 2) (.var 0)) (.app (.app (.var 2) (.var 1)) (.var 0)))))
  let recursor : Ixon.Recursor :=
    { k := false, isUnsafe := false, lvls := 1, params := 1, indices := 1, motives := 1,
      minors := 0, typ := typ, rules := #[] }
  let record ← IxVM.RecordSections.withSection env
    ⟨.recr recursor, #[], #[address type, nat, zero], #[.succ .zero, .var 0], #[]⟩
  let env := env.storeConst (address record) record
  let context ← Ix.ClaimContext.ofEnv env
  let witness ← IxVM.ClaimHarness.buildClaimWitness env (.check context (address record) none)
  let c : Case := {
    label := if dead then "native recursor: a let in a parameter's domain that its family does not have"
      else "native recursor: a parameter, no let"
    accept := true
    exercises := if dead then none else some "KernelCheck::nat_rec_check"
    witness := witness }
  return if dead then
    refused lets "native recursor: the stored type is not the generated one up to consumed wrappers"
      none c
  else c

def run (leanEnv : Lean.Environment) : IO UInt32 := do
  let before ← IO.getEnv "IX_GUARD_BATCH_BEFORE"
  let guards := before.isNone || before == some "lets"
  let lets := before.isNone
  let missing := compiledNames.filter (!leanEnv.constants.contains ·)
  unless missing.isEmpty do
    IO.eprintln s!"[ixvm-guard-batch] not in the environment: {missing}"
    return 1
  let env ← loadSharedIxonEnv compiledNames.toArray leanEnv
  let built : Array Builder := #[
    fun _ => mixedCase guards false, fun _ => mixedCase guards true, fun _ => separateCase,
    fun _ => nativeHeaderCase guards .nowhere, fun _ => nativeHeaderCase guards .motive,
    fun _ => nativeHeaderCase guards .index, fun _ => nativeHeaderCase guards .major,
    fun _ => nativeHeaderCase guards .result,
    fun _ => modeledHeaderCase guards false, fun _ => modeledHeaderCase guards true,
    fun _ => parameterLetCase lets false, fun _ => parameterLetCase lets true]
  runCases "ixvm-guard-batch" (compiledCases guards env ++ built) (jobs := 4)

end Tests.Ix.IxVM.GuardBatch
