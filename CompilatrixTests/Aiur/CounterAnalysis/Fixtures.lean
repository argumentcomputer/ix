import CompilatrixTests.Aiur.Static.Fixtures

namespace CompilatrixTests.Aiur.CounterAnalysis

open _root_.Aiur.Bytecode (Block Function Toplevel)
open CompilatrixTests.Aiur.Execution (mkFunction)

/-- Two self-calls use the second input. Constant multiplication and
multiply-by-one are tracked; advice and memory outputs remain unknown. -/
def algebraFunction : Function := mkFunction 2
  ⟨#[.const 2, .const 3, .mul 2 3, .const 5, .sub 4 5,
      .const 1, .mul 1 7, .add 8 6, .unconstrainedGInverse 0, .store #[10],
      .call 0 #[0, 9] 2 false, .const 1, .sub 9 14, .add 15 6,
      .call 0 #[0, 16] 2 false], .return 0 #[17, 18]⟩

def algebraProgram : Toplevel := ⟨#[algebraFunction], #[], #[], #[]⟩

def markerReturn : Block :=
  ⟨#[.call 0 #[0] 2 false, .const 1, .mul 3 4, .const 2, .const 3,
      .sub 7 6, .add 5 8, .const 0], .return 1 #[10, 9]⟩

/-- The marker is the second output of the recursive call. -/
def markerFunction : Function := mkFunction 1
  ⟨#[.unconstrainedGInverse 0], .match 1
    #[(0, ⟨#[.const 0, .const 0], .return 0 #[2, 3]⟩)] (some markerReturn)⟩

def markerProgram : Toplevel := ⟨#[markerFunction], #[], #[], #[]⟩

/-- A leaf without a self-call need not return the selected output column.
The semantic theorem deliberately promises observations only on edges. -/
def shortLeafFunction : Function := mkFunction 1
  ⟨#[.unconstrainedGInverse 0], .match 1
    #[(0, ⟨#[.const 0, .const 0], .return 0 #[2, 3]⟩),
      (1, ⟨#[.const 0], .return 2 #[2]⟩)] (some markerReturn)⟩

def shortLeafProgram : Toplevel := ⟨#[shortLeafFunction], #[], #[], #[]⟩

def hintFunction : Function := mkFunction 1
  ⟨#[.unconstrainedGInverse 0, .call 0 #[1] 1 false], .return 0 #[2]⟩

def nonlinearFunction : Function := mkFunction 1
  ⟨#[.add 0 0, .call 0 #[1] 1 false], .return 0 #[2]⟩

def repeatedOutputFunction : Function := mkFunction 1
  ⟨#[.call 0 #[0] 1 false, .call 0 #[0] 1 false, .const 1, .add 2 3], .return 0 #[4]⟩

def missingArgumentFunction : Function := mkFunction 1
  ⟨#[.call 0 #[] 1 false], .return 0 #[1]⟩

def missingRegisterFunction : Function := mkFunction 1
  ⟨#[.call 0 #[99] 1 false], .return 0 #[1]⟩

def noOutputsFunction : Function := mkFunction 1
  ⟨#[.call 0 #[0] 0 false, .const 1], .return 0 #[1]⟩

def badBranchFunction : Function := mkFunction 1
  ⟨#[], .match 0
    #[(0, ⟨#[.const 1, .add 0 1, .call 0 #[2] 1 false], .return 0 #[3]⟩),
      (0, ⟨#[.call 0 #[0] 1 false], .return 0 #[1]⟩)] none⟩

def yieldFunction : Function := mkFunction 1 ⟨#[], .yield 0 #[0]⟩

def continuationFunction : Function := mkFunction 1
  ⟨#[], .matchContinue 0 #[(0, ⟨#[], .yield 0 #[0]⟩)] none 1 0 0 ⟨#[], .return 0 #[1]⟩⟩

end CompilatrixTests.Aiur.CounterAnalysis
