import Ix.CompileCert.Entry
import Tests.Ix.Kernel.IxonFixtures
import Tests.Ix.CompileCert.BlockDefs

namespace Tests.Ix.CompileCert.Blocks

open _root_.Ix.CompileCert
open Tests.Ix.Kernel.IxonFixtures

def input (ind recursor : Lean.ConstantInfo) : Input :=
  { source := ⟨[ind, recursor]⟩
    roots := [ind.name]
    map := [⟨ind.name, address 4, .member (address 3) 0⟩,
      ⟨recursor.name, address 5, .member (address 3) 1⟩]
    limits := ⟨1024, 1024, 1048576, 65536, 4096⟩
    records := falseStore.map (fun (a, c) => (a, Ixon.serConstant c))
    blobs := [] }

def blockDeclined (i : Input) : Bool :=
  match checkCompiled i with
  | .error .blockCorrespondence => true
  | _ => false

def outcome (i : Input) : String :=
  match checkCompiled i with
  | .ok _ => "accepted"
  | .error (.admission e) => s!"admission: {e}"
  | .error .sourceDomain => "source domain"
  | .error .correspondence => "entry correspondence"
  | .error .blockCorrespondence => "block correspondence"
  | .error .mapMismatch => "map mismatch"
  | .error _ => "other decline"

def run : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `Tests.Ix.CompileCert.BlockDefs }] {}
  let some (.inductInfo iv) := env.find? `Tests.Ix.CompileCert.BlockDefs.Void
    | throw (IO.userError "missing checked source inductive")
  let some (.recInfo rv) := env.find? `Tests.Ix.CompileCert.BlockDefs.Void.rec
    | throw (IO.userError "missing checked source recursor")
  let valid := input (.inductInfo iv) (.recInfo rv)
  let cases := [
    ("complete checked Lean block", (checkCompiled valid).isOk),
    ("same entries but wrong recursive shape", blockDeclined
      (input (.inductInfo { iv with isRec := !iv.isRec }) (.recInfo rv))),
    ("same entries but wrong index count", blockDeclined
      (input (.inductInfo { iv with numIndices := iv.numIndices + 1 }) (.recInfo rv))),
    ("same recursor sums but wrong individual counts", blockDeclined
      (input (.inductInfo iv) (.recInfo
        { rv with numParams := rv.numParams + 1, numMotives := rv.numMotives - 1 }))),
    ("wrong source recursor K flag", match checkCompiled
        (input (.inductInfo iv) (.recInfo { rv with k := !rv.k })) with
      | .error .mapMismatch => true
      | _ => false)]
  let mut failed := 0
  for (label, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {label}"
    unless ok do failed := failed + 1
  if failed != 0 then
    IO.println s!"positive outcome: {outcome valid}"
    throw (IO.userError s!"{failed}/{cases.length} block controls failed")

end Tests.Ix.CompileCert.Blocks

def main : IO Unit := Tests.Ix.CompileCert.Blocks.run
