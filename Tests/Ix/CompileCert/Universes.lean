import Tests.Ix.CompileCert.Direct

namespace Tests.Ix.CompileCert.Universes

open _root_.Ix.CompileCert

def parameter : _root_.Ix.Kernel.Level := .param (.str .anonymous "target")

def controls : List (String × (Unit → Bool)) := [
  ("universe guard accepts non-syntactic semantic equality", fun _ =>
    (checkedLevelImage (.max parameter .zero) parameter).isOk),
  ("universe guard rejects changed value", fun _ =>
    !(checkedLevelImage (.succ .zero) .zero).isOk),
  ("universe guard distinguishes independent parameters", fun _ =>
    !(checkedLevelImage parameter (.param (.str .anonymous "different"))).isOk),
  ("imax zero branch is checked semantically", fun _ =>
    (checkedLevelImage (.imax parameter .zero) .zero).isOk),
  ("missing target universe slot explicitly declines", fun _ =>
    !(importUniv [] (.var 0)).isOk),
  ("missing source universe parameter explicitly declines", fun _ =>
    !(exportUniv [] (.param `u)).isOk),
  ("actual canonical export and target substitution", fun _ =>
    match _root_.Ix.Kernel.Reader.defaultPins with
    | .error _ => false
    | .ok pins =>
      let name := _root_.Ix.Kernel.Name.str .anonymous "target"
      let cx : TermContext := ⟨⟨⟨[]⟩, [], pins⟩, [`u], [name]⟩
      match exportLevel cx (.imax (.succ (.param `u)) (.param `u)) with
      | .error _ => false
      | .ok level =>
        _root_.Ix.Kernel.Level.eval (fun _ => 0)
          (_root_.Ix.Kernel.Level.subst [name] [.succ (.succ .zero)] level) == 3)]

open Ixon.CanonUniv in
/-- M3: `canonUniv` accumulated successor offsets in `UInt64`, so an
accumulator at `2^64 - 1` plus one successor wrapped to `0` and the level
lost its value (`normalizeAux (.succ .zero) [] (2^64 - 1)` had constant `0`).
Offsets are now `Nat`. The overflowing input, and ordinary inputs whose
canonical form must not change. -/
def offsetControls : List (String × (Unit → Bool)) := [
  ("canonUniv offset past 2^64 is kept, not wrapped", fun _ =>
    ((normalizeAux (.succ .zero) [] (2 ^ 64 - 1) ((∅ : CNorm).insert [] {})).findD [] {}).constant
      == 2 ^ 64),
  ("canonUniv offset past 2^64 on a variable is kept", fun _ =>
    ((normalizeAux (.succ (.var 0)) [] (2 ^ 64 - 1) ((∅ : CNorm).insert [] {})).findD [0] {}).vars
      == #[(0, 2 ^ 64)]),
  ("canonUniv of ordinary levels is unchanged", fun _ =>
    Ixon.canonUniv (.succ (.succ .zero)) == .succ (.succ .zero) &&
    Ixon.canonUniv (.max (.var 0) (.succ (.var 0))) == .succ (.var 0) &&
    Ixon.canonUniv (.imax (.succ (.var 0)) .zero) == .zero &&
    Ixon.canonUniv (.max (.succ (.succ (.var 1))) (.var 1)) == .succ (.succ (.var 1)))]

def run : IO Unit := do
  let mut failed := 0
  let all := controls ++ offsetControls
  for (label, control) in all do
    let ok := control ()
    IO.println s!"{if ok then "PASS" else "FAIL"}: {label}"
    unless ok do failed := failed + 1
  unless failed == 0 do throw (IO.userError s!"{failed} universe bridge controls failed")
  IO.println s!"universes: {all.length}/{all.length} controls passed"

end Tests.Ix.CompileCert.Universes
