import Tests.Ix.CompileCert.Direct

namespace Tests.Ix.CompileCert.Groups

open _root_.Ix.CompileCert
open Tests.Ix.CompileCert.Direct
open Tests.Ix.Kernel.IxonFixtures (address)

def groupedSource (name : Lean.Name) (value : Lean.Expr) : Lean.ConstantInfo :=
  match sourceDef name value with
  | .defnInfo d => .defnInfo { d with all := [`first, `root, `alias] }
  | other => other

/-- Source order differs from wire member order; the first wire member
depends internally on the second. Two source members share its second slot. -/
def grouped : Input :=
  let typ := Ixon.Expr.leanAll (.sort 0) (.leanAll (.var 0) (.leanAll (.var 1) (.var 2)))
  let val := Ixon.Expr.leanLam (.sort 0) (.leanLam (.var 0) (.leanLam (.var 1) (.var 1)))
  let block : Ixon.Constant := ⟨.muts #[
    .defn ⟨.defn, .safe, 1, typ, .recur 1 #[0]⟩,
    .defn ⟨.defn, .safe, 1, typ, val⟩], #[], #[], #[.var 0]⟩
  let first : Ixon.Constant := ⟨.dPrj ⟨1, address 80⟩, #[], #[], #[]⟩
  let root : Ixon.Constant := ⟨.dPrj ⟨0, address 80⟩, #[], #[], #[]⟩
  { choiceInput with
    source := ⟨[groupedSource `first (sourceValue true),
      groupedSource `root (.const `first [.param `u]), groupedSource `alias (sourceValue true)]⟩
    roots := [`root]
    map := [⟨`first, address 81, .member (address 80) 1⟩,
      ⟨`root, address 82, .member (address 80) 0⟩,
      ⟨`alias, address 81, .member (address 80) 1⟩]
    records := [(address 80, Ixon.serConstant block),
      (address 81, Ixon.serConstant first), (address 82, Ixon.serConstant root)] }

def controls : List (String × (Unit → Bool)) := [
  ("group permutation, internal reference, and compatible alias", fun _ => accepted grouped),
  ("source group may split into singleton wire records", fun _ =>
    accepted { dependent with source := ⟨dependent.source.declarations.map fun
      | .defnInfo d => Lean.ConstantInfo.defnInfo { d with all := [`first, `root] }
      | ci => ci⟩ }),
  ("definition group image retains every alias row", fun _ =>
    match checkCompiled grouped with
    | .error _ => false
    | .ok a =>
      let cx : ExportContext := ⟨grouped.source, grouped.map, a.pins, noImages⟩
      (definitionGroupImage cx (groupedSource `first (sourceValue true))).map List.length == some 3),
  ("unmapped touched wire member is not hidden by source success", fun _ =>
    let input := { grouped with
      source := ⟨[sourceDef `first (sourceValue true)]⟩, roots := [`first]
      map := [⟨`first, address 81, .member (address 80) 1⟩] }
    match checkCompiled input with
    | .error .definitionGroupCorrespondence => true
    | _ => false),
  ("wrong internal source reference cannot borrow another group member", fun _ =>
    sourceMismatch { grouped with source := ⟨[groupedSource `first (sourceValue true),
      groupedSource `root (sourceValue false), groupedSource `alias (sourceValue true)]⟩ })]

def run : IO Unit := do
  let mut failed := 0
  for (label, control) in controls do
    let ok := control ()
    IO.println s!"{if ok then "PASS" else "FAIL"}: {label}"
    unless ok do failed := failed + 1
  unless failed == 0 do throw (IO.userError s!"{failed} definition group controls failed")

end Tests.Ix.CompileCert.Groups
