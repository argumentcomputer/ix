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

def run : IO Unit := do
  let mut failed := 0
  for (label, control) in controls do
    let ok := control ()
    IO.println s!"{if ok then "PASS" else "FAIL"}: {label}"
    unless ok do failed := failed + 1
  unless failed == 0 do throw (IO.userError s!"{failed} universe bridge controls failed")

end Tests.Ix.CompileCert.Universes
