module

public import LSpec
public import Ix.AuxGen.Recursor

/-!
The elimination decision of the canonical recursor
(`Ix.AuxGen.computeIsLargeAndK`) on explicit flat blocks: the kernels' rule
(Lean's `elim_only_at_universe_zero`) counts the nested auxiliaries as
members, so a result level that may be zero eliminates small whenever the
flat block is not a singleton, and that is decided before any field of the
original classes is probed (their fields can name an auxiliary the bridge's
kernel does not hold: WB-A7). The Rust twins are `compute_is_large_and_k`'s
`c1_*` tests (`aux_gen/recursor.rs`).

Ported from lane P's `Tests/Ix/Compile/C1/FlagControls.lean` (`6327e496`, on
`04732ad7`), a standalone executable there, over this tree's `AuxKernel`
interface (AuxGen M0). Registered in `aux-gen-unit`.
-/

public section

namespace Tests.AuxGen.ElimRule

open LSpec
open Ix.AuxGen
open Ix.CompileM (CompileM CompileEnv CompileError)
open Ix (Name Level Expr InductiveVal ConstructorVal)

private def nm (s : String) : Name := Name.mkStr .mkAnon s
private def prop : Level := Level.mkZero
private def cn (s : String) : Expr := Expr.mkConst (nm s) #[]

/-- A flat member with one constructor `mk` whose fields are `fields`, at
result level `level`; `aux` marks a nested auxiliary. -/
private def member (label : String) (level : Level) (fields : List Expr)
    (aux : Bool := false) (levels : Array Name := #[]) : FlatInfo := Id.run do
  let name := nm label
  let ctor := Name.mkStr name "mk"
  let result := Expr.mkConst name (levels.map Level.mkParam)
  let ty := fields.foldr (fun dom body => Expr.mkForallE (nm "field") dom body .default) result
  let ind : InductiveVal :=
    { cnst := ⟨name, levels, Expr.mkSort level⟩
      numParams := 0, numIndices := 0, all := #[name], ctors := #[ctor]
      numNested := 0, isRec := !fields.isEmpty
      isUnsafe := false, isReflexive := false }
  let cv : ConstructorVal :=
    { cnst := ⟨ctor, levels, ty⟩, induct := name, cidx := 0
      numParams := 0, numFields := fields.length, isUnsafe := false }
  return { name, ind, ctors := #[cv], allNames := #[name], isAux := aux
           specParams := #[], occurrenceLevelArgs := #[], ownParams := 0, nIndices := 0 }

private def kernel : AuxKernel := .tc { nameToAddr := fun _ => none }

private def runBridge (action : KBridgeM α) : Except CompileError α := do
  let ((value, _), _) ← CompileM.run (default : CompileEnv)
    { all := {}, current := nm "C1", mutCtx := default, univCtx := [] } {}
    (action.run AuxKernelCtx.new)
  return value

/-- The decision for a block of one original class (`nClasses = 1`, no
parameters) and the auxiliaries after it. -/
private def flags (xs : Array FlatInfo) : KBridgeM (Bool × Bool × Bool) :=
  computeIsLargeAndK xs 1 0 kernel

private def equalsFlags (xs : Array FlatInfo) (want : Bool × Bool × Bool) : Bool :=
  match runBridge (flags xs) with
  | .ok result => result == want
  | .error _ => false

private def errorsAt (xs : Array FlatInfo) (expectedPrefix : String) : Bool :=
  match runBridge (flags xs) with
  | .error (.invalidMutualBlock reason) => reason.startsWith expectedPrefix
  | _ => false

def checks : List (String × Bool) := Id.run do
  -- `C1Q` is an auxiliary of the flat block, but the kernel holds only the
  -- original `C1P`: its field names a constant the kernel does not have, so
  -- a probe of `C1P`'s fields fails. The rule decides first.
  let p := member "C1P" prop [cn "C1Q"]
  let q := member "C1Q" prop [cn "C1P"] true
  let zeroField := member "PlainK" prop []
  let empty := { zeroField with ctors := #[], ind := { zeroField.ind with ctors := #[] } }
  let proofField := member "PlainDrec" prop [cn "PlainDrec"]
  let t := member "C1T" (Level.mkSucc prop) [cn "C1U"]
  let a := member "C1U" (Level.mkSucc prop) [cn "C1T"] true
  let u := nm "u"
  let zeroSpelling := member "ZeroSpelling" (Level.mkIMax (Level.mkParam u) prop)
    [cn "MissingAux"] false #[u]
  let badTarget := { p with ind := { p.ind with cnst := { p.ind.cnst with type := cn "MissingResult" } } }
  -- `SortUDecl`'s shape: two constructors at a level that may be zero, so
  -- the probe itself selects small elimination.
  let su := member "SortU" (Level.mkParam u) [] false #[u]
  let secondName := Name.mkStr su.name "other"
  let first := su.ctors[0]!
  let other := { first with cnst := { first.cnst with name := secondName }, cidx := 1 }
  let su := { su with ctors := su.ctors.push other, ind := { su.ind with ctors := su.ind.ctors.push secondName } }
  -- `NestedSortU`'s shape: a `Sort u` original whose own constructor passes
  -- the singleton test, with one auxiliary. The expanded block is not a
  -- singleton and `u` may be zero, so elimination is small, as in the
  -- kernels; the former rule (small only at a semantically zero level)
  -- gave a large recursor.
  let nsu := member "NestedSortU" (Level.mkParam u) [] false #[u]
  let nsuAux := member "NestedSortUAux" (Level.mkParam u) [] true #[u]
  let sequence := runBridge do
    let first ← flags #[p, q]
    let second ← flags #[proofField]
    pure (first, second)
  return [
    ("nested singleton Prop: small before the missing-aux probe", equalsFlags #[p, q] (false, false, true)),
    ("the same missing field without an auxiliary still errors", errorsAt #[p]
      "compute_is_large_and_k: is_large_eliminator failed"),
    ("a semantic-zero spelling takes the rule", equalsFlags #[zeroSpelling, q] (false, false, true)),
    ("the rule does not bypass result-sort errors", errorsAt #[badTarget, q]
      "compute_is_large_and_k: TC failed"),
    ("empty Prop keeps large elimination without K", equalsFlags #[empty] (true, false, true)),
    ("zero-field singleton keeps K", equalsFlags #[zeroField] (true, true, true)),
    ("ordinary proof-only singleton keeps large elimination", equalsFlags #[proofField] (true, false, true)),
    ("nested Type stays large", equalsFlags #[t, a] (true, false, false)),
    ("Sort u two-constructor neighbour stays small", equalsFlags #[su] (false, false, false)),
    ("nested Sort u singleton is small", equalsFlags #[nsu, nsuAux] (false, false, false)),
    ("a later decision on the retained kernel keeps its result", match sequence with
      | .ok (first, second) => first == (false, false, true) && second == (true, false, true)
      | .error _ => false)]

def suite : List TestSeq :=
  checks.map fun (label, passed) => test s!"elimination rule: {label}" passed

end Tests.AuxGen.ElimRule

end
