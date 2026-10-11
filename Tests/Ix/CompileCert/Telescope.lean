import Ix.CompileCert.Entry

/-! Focused executable controls for the direct installed telescope check.
These synthetic environments test only telescope association; they are not
admission fixtures or evidence of full declaration/value correspondence. -/

namespace Tests.Ix.CompileCert.Telescope

open _root_.Ix.CompileCert
open _root_.Ix.Kernel (ConstantInfo Env Name)

def entry (name : Lean.Name) (parameters : List Lean.Name) : ConstantInfo :=
  .axiomInfo ⟨sourceName name, parameters.map sourceName, .sort .zero⟩

def aliases : Env := ⟨[entry `first [`u], entry `second [`v]]⟩
def target : Env := ⟨[entry `shared [`x]]⟩
def names (_ : Name) : Name := sourceName `shared

-- Every alias retains its own formal telescope.
example : checkTelescopes aliases target names = true := by decide

-- The second source cannot be hidden by an already valid target fiber.
example : checkTelescopes ⟨[entry `first [`u], entry `second [`v, `w]]⟩ target names = false := by decide

example : checkTelescopes aliases Env.empty names = false := by decide
example : checkTelescopes aliases target (fun _ => sourceName `missing) = false := by decide
example : checkTelescopes aliases ⟨[entry `shared []]⟩ names = false := by decide

-- Matching list lengths do not excuse duplicate formals on either side.
example : checkTelescopes ⟨[entry `first [`u, `u]]⟩ ⟨[entry `shared [`x, `y]]⟩ names = false := by decide
example : checkTelescopes ⟨[entry `first [`u, `v]]⟩ ⟨[entry `shared [`x, `x]]⟩ names = false := by decide

def levels (name : Name) : Nat := if name == sourceName `u then 3 else 7

-- The target formal takes its corresponding source value, including for
-- aliases whose original formal names differ.
example : (PullbackMap.fromEnvs aliases target names).levels (sourceName `first) levels (sourceName `x) = 3 := by decide
example : (PullbackMap.fromEnvs aliases target names).levels (sourceName `second) levels (sourceName `x) = 7 := by decide

def twoSource : Env := ⟨[entry `first [`u, `v]]⟩
def twoTarget : Env := ⟨[entry `shared [`y, `x]]⟩

-- Position, not lexical order of parameter names, determines selection.
example : checkTelescopes twoSource twoTarget names = true := by decide
example : (PullbackMap.fromEnvs twoSource twoTarget names).levels (sourceName `first) levels (sourceName `y) = 3 := by decide
example : (PullbackMap.fromEnvs twoSource twoTarget names).levels (sourceName `first) levels (sourceName `x) = 7 := by decide

end Tests.Ix.CompileCert.Telescope
