import CompilatrixTests.Aiur.Execution.Support

namespace CompilatrixTests.Aiur.Execution

open _root_.Aiur.Bytecode (Block Toplevel)

def emptyReturn : Toplevel := program 0 ⟨#[], .return 7 #[]⟩
def rootYield : Toplevel := program 1 ⟨#[], .yield 3 #[0]⟩

def eleven : Block := ⟨#[.const 11], .return 0 #[1]⟩
def twentyTwo : Block := ⟨#[.const 22], .return 1 #[1]⟩

def matched : Toplevel := program 1 ⟨#[], .match 0 #[(0, eleven)] (some twentyTwo)⟩
def duplicateCases : Toplevel := program 1 ⟨#[], .match 0 #[(0, eleven), (0, twentyTwo)] none⟩
def missingCase : Toplevel := program 1 ⟨#[], .match 0 #[(0, eleven)] none⟩

/-- Case-local 99 must not occupy the continuation's yielded-value slot. -/
def continuationScope : Toplevel := program 2 ⟨#[],
  .matchContinue 0 #[(0, ⟨#[.const 99, .const 7], .yield 4 #[3]⟩)] none 1 2 0
    ⟨#[.add 1 2], .return 6 #[3]⟩⟩

def bomb : Block := ⟨#[.assertEq #[999] #[] none], .return 0 #[]⟩

def earlyReturn : Toplevel := program 1 ⟨#[],
  .matchContinue 0 #[(0, ⟨#[.const 7], .return 2 #[1]⟩)] none 1 1 0 bomb⟩

/-- A two-value function return skips both one-value continuations. -/
def nestedEarlyReturn : Toplevel := program 1 ⟨#[],
  .matchContinue 0 #[(0, ⟨#[],
    .matchContinue 0 #[(0, ⟨#[.const 7, .const 8], .return 2 #[1, 2]⟩)] none 1 2 0 bomb⟩)]
    none 1 2 0 bomb⟩

def nestedYield : Toplevel := program 1 ⟨#[],
  .matchContinue 0 #[(0, ⟨#[.const 5],
    .matchContinue 0 #[(0, ⟨#[.const 9], .yield 1 #[2]⟩)] none 1 1 0
      ⟨#[.add 1 2], .yield 2 #[3]⟩⟩)] none 1 3 0
    ⟨#[.const 1, .add 1 2], .return 3 #[3]⟩⟩

def matchInsideContinuation : Toplevel := program 1 ⟨#[],
  .matchContinue 0 #[(0, ⟨#[], .match 0 #[(0, ⟨#[.const 9], .yield 1 #[1]⟩)] none⟩)]
    none 1 1 0 ⟨#[.const 1, .add 1 2], .return 2 #[3]⟩⟩

def wrongYieldSize : Toplevel := program 1 ⟨#[],
  .matchContinue 0 #[(0, ⟨#[], .yield 1 #[0, 0]⟩)] none 1 0 0 bomb⟩

def continuationMemory : Toplevel := program 2 ⟨#[],
  .matchContinue 0 #[(0, ⟨#[.load 1 1], .yield 1 #[2]⟩)] none 1 1 1
    ⟨#[.store #[2]], .return 2 #[3]⟩⟩

def inverseChecked : Toplevel := opsProgram 1
  #[.unconstrainedGInverse 0, .mul 0 1, .const 1, .assertEq #[2] #[3] none] #[1]

def repeatedAdvice : Toplevel := opsProgram 1
  #[.unconstrainedGInverse 0, .unconstrainedGInverse 0] #[1, 2]

def virtualCarry : Toplevel := opsProgram 8
  #[.unconstrainedU32Add #[0, 1, 2, 3] #[4, 5, 6, 7]] #[8, 9, 10, 11, 12]

end CompilatrixTests.Aiur.Execution
