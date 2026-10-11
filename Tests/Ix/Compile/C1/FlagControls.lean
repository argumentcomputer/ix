/- Direct controls for the production C1 flag helper on explicit flat metadata.
   The ordinary source/compiler controls are separate in KernelSpecC1.lean. -/
import Ix.AuxGen.Recursor

namespace KernelSpecC1Controls

open Ix (Name Level Expr InductiveVal ConstructorVal)
open Ix.AuxGen

private def nm (s : String) : Name := Name.mkStr .mkAnon s
private def prop : Level := Level.mkZero
private def cn (s : String) : Expr := Expr.mkConst (nm s) #[]

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

private def runBridge (action : KBridgeM α) : Except Ix.CompileM.CompileError α :=
  let cenv := Ix.CompileM.CompileEnv.new { consts := {} }
  let benv : Ix.CompileM.BlockEnv :=
    { all := {}, current := nm "C1", mutCtx := default, univCtx := [] }
  match Ix.CompileM.CompileM.run cenv benv {} (action AuxKernelCtx.new) with
  | .ok ((value, _), _) => .ok value
  | .error e => .error e

private def flags (xs : Array FlatInfo) : KBridgeM (Bool × Bool × Bool) :=
  computeIsLargeAndK xs 1 0 { nameToAddr := fun _ => none }

private def equalsFlags (xs : Array FlatInfo) (want : Bool × Bool × Bool) : Bool :=
  match runBridge (flags xs) with
  | .ok result => result == want
  | .error _ => false

private def errorsAt (xs : Array FlatInfo) (expectedPrefix : String) : Bool :=
  match runBridge (flags xs) with
  | .error (.invalidMutualBlock reason) => reason.startsWith expectedPrefix
  | _ => false

def checks : Array (String × Bool) := Id.run do
  -- Q is an explicit auxiliary in the full flat block, but the helper's
  -- original-only KEnv registers P alone. This isolates the failing probe.
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
  -- Same shape as SortUDecl: two constructors, Sort u may be Prop, so the
  -- non-C1 kernel rule must still select small elimination.
  let su := member "SortU" (Level.mkParam u) [] false #[u]
  let secondName := Name.mkStr su.name "other"
  let first := su.ctors[0]!
  let other := { first with cnst := { first.cnst with name := secondName }, cidx := 1 }
  let su := { su with ctors := su.ctors.push other, ind := { su.ind with ctors := su.ind.ctors.push secondName } }
  let sequence := runBridge do
    let first ← flags #[p, q]
    let second ← flags #[proofField]
    pure (first, second)
  return #[
    ("nested singleton Prop: small before missing-aux probe", equalsFlags #[p,q] (false,false,true)),
    ("same missing field without auxiliary still errors", errorsAt #[p]
      "compute_is_large_and_k: is_large_eliminator failed"),
    ("semantic-zero spelling still takes C1", equalsFlags #[zeroSpelling,q] (false,false,true)),
    ("C1 does not bypass result-sort errors", errorsAt #[badTarget,q]
      "compute_is_large_and_k: TC failed"),
    ("empty Prop retains large elimination without K", equalsFlags #[empty] (true,false,true)),
    ("zero-field singleton retains K", equalsFlags #[zeroField] (true,true,true)),
    ("ordinary proof-only singleton retains large elimination", equalsFlags #[proofField] (true,false,true)),
    ("nested Type remains large", equalsFlags #[t,a] (true,false,false)),
    ("Sort u two-constructor neighbour stays small", equalsFlags #[su] (false,false,false)),
    ("subsequent flag call on retained KEnv keeps its result", match sequence with
      | .ok (first,second) => first == (false,false,true) && second == (true,false,true)
      | .error _ => false)
  ]

end KernelSpecC1Controls

def main : IO UInt32 := do
  let mut failed := false
  for (name, ok) in KernelSpecC1Controls.checks do
    IO.println s!"[c1-control] {name}: {ok}"
    if !ok then failed := true
  return if failed then 1 else 0
