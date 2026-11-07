import IxCCTests.Aiur.Execution.ControlFixtures
import IxCCTests.Aiur.WireFixtures
import IxCC.Aiur.Check
import IxCC.Aiur.WellFounded

namespace IxCCTests.Aiur.Execution

open IxCC.Aiur
open IxCC.Aiur.OracleEval
open _root_.Aiur (G)
open _root_.Aiur.Bytecode (Block Toplevel)

def provider (message : Message) (demands : List Message := []) (weight : G := 1)
    (active : Bool := true) : Row := ⟨active, message, weight, demands⟩

def ordinalStatic (trace : Trace)
    (forward : ∀ child parent : trace.RowId, trace.Requires child parent → parent.val < child.val) :
    StaticCertificate trace.RowId trace.Requires where
  facts := fun id => ⟨id.val, 0, 0⟩
  ranked := fun _ => false
  edge := fun child parent edge => .inl (forward child parent edge)

def counterProgram : Toplevel := IxCCTests.Aiur.WireFixtures.counter

def counterTrace : Trace :=
  ⟨[provider (.function 0 [2] [0]) [.function 0 [1] [0]],
    provider (.function 0 [1] [0]) [.function 0 [0] [0]],
    provider (.function 0 [0] [0])], [.function 0 [2] [0]]⟩

def counterReplies : Array (List Values) := #[[[0]], [[0]], []]

def counterStatic : StaticCertificate counterTrace.RowId counterTrace.Requires where
  facts := fun id => ⟨0, 0 - G.ofNat (2 - id.val), 0⟩
  ranked := fun _ => false
  edge := by decide

def mutualBody (callee : Nat) : Block :=
  ⟨#[], .match 0 #[(0, ⟨#[.const 0], .return 0 #[1]⟩)]
    (some ⟨#[.const 1, .sub 0 1, .call callee #[2] 1 false], .return 1 #[3]⟩)⟩

def rankedProgram : Toplevel :=
  ⟨#[mkFunction 1 (mutualBody 1), mkFunction 1 (mutualBody 0)], #[], #[], #[⟨0, true⟩, ⟨0, true⟩]⟩

def rankedTrace : Trace :=
  ⟨[provider (.function 0 [2] [0]) [.function 1 [1] [0]],
    provider (.function 1 [1] [0]) [.function 0 [0] [0]],
    provider (.function 0 [0] [0])], [.function 0 [2] [0]]⟩

def rankedStatic : StaticCertificate rankedTrace.RowId rankedTrace.Requires where
  facts := fun id => ⟨0, 0, id.val⟩
  ranked := fun _ => true
  edge := by decide

def storeProgram : Toplevel := opsProgram 1 #[.store #[0]] #[1]
def loadProgram : Toplevel := opsProgram 1 #[.load 1 0] #[1]
def doubleStoreProgram : Toplevel := opsProgram 1 #[.store #[0], .store #[0]] #[1, 2]

def storeTrace : Trace :=
  ⟨[provider (.function 0 [42] [7]) [.memory 1 7 [42]], provider (.memory 1 7 [42])],
    [.function 0 [42] [7]]⟩

def loadTrace : Trace :=
  ⟨[provider (.function 0 [7] [42]) [.memory 1 7 [42]], provider (.memory 1 7 [42])],
    [.function 0 [7] [42]]⟩

def selfPointerTrace : Trace :=
  ⟨[provider (.function 0 [7] [7]) [.memory 1 7 [7]], provider (.memory 1 7 [7])],
    [.function 0 [7] [7]]⟩

def doubleStoreTrace : Trace :=
  ⟨[provider (.function 0 [42] [7, 9]) [.memory 1 7 [42], .memory 1 9 [42]],
    provider (.memory 1 7 [42]), provider (.memory 1 9 [42])], [.function 0 [42] [7, 9]]⟩

def storeStatic := ordinalStatic storeTrace (by decide)
def loadStatic := ordinalStatic loadTrace (by decide)
def selfPointerStatic := ordinalStatic selfPointerTrace (by decide)
def doubleStoreStatic := ordinalStatic doubleStoreTrace (by decide)

def xorProgram : Toplevel := opsProgram 2 #[.u8Xor 0 1] #[2]

def xorTrace : Trace :=
  ⟨[provider (.function 0 [1, 2] [3]) [.gadget 3 [1, 2, 3]], provider (.gadget 3 [1, 2, 3])],
    [.function 0 [1, 2] [3]]⟩

def falseGadgetTrace : Trace :=
  ⟨[provider (.function 0 [1, 2] [9]) [.gadget 3 [1, 2, 9]], provider (.gadget 3 [1, 2, 9])],
    [.function 0 [1, 2] [9]]⟩

def xorStatic := ordinalStatic xorTrace (by decide)

def constantProgram : Toplevel := opsProgram 0 #[.const 5] #[0]
def falseClaimTrace : Trace := ⟨[provider (.function 0 [] [6])], [.function 0 [] [6]]⟩

def callProgram : Toplevel :=
  ⟨#[mkFunction 2 ⟨#[.call 1 #[0, 1] 1 false], .return 0 #[2]⟩,
      mkFunction 2 ⟨#[.add 0 1], .return 0 #[2]⟩], #[], #[], #[]⟩

def callTrace (output : G) : Trace :=
  ⟨[provider (.function 0 [20, 22] [output]) [.function 1 [20, 22] [output]],
    provider (.function 1 [20, 22] [output])], [.function 0 [20, 22] [output]]⟩

def callStatic := ordinalStatic (callTrace 42) (by decide)

/-- The callee loops forever when constrained. As a hint call, its result is
advice and no recursive function lookup is required. -/
def hintCallProgram : Toplevel :=
  ⟨#[mkFunction 0 ⟨#[.call 1 #[] 1 true], .return 0 #[0]⟩,
      mkFunction 0 ⟨#[.call 1 #[] 1 false], .return 0 #[0]⟩], #[], #[], #[]⟩

def hintCallTrace : Trace := ⟨[provider (.function 0 [] [99])], [.function 0 [] [99]]⟩
def hintCallStatic := ordinalStatic hintCallTrace (by decide)

def repeatedAdviceTrace : Trace := ⟨[provider (.function 0 [0] [7, 9])], [.function 0 [0] [7, 9]]⟩
def repeatedAdviceStatic := ordinalStatic repeatedAdviceTrace (by decide)

def selfLoopProgram : Toplevel := opsProgram 0 #[.call 0 #[] 1 false] #[0]
def selfLoopTrace : Trace :=
  ⟨[provider (.function 0 [] [99]) [.function 0 [] [99]] 2], [.function 0 [] [99]]⟩

def mutualLoopProgram : Toplevel := IxCCTests.Aiur.WireFixtures.rankedMutual
def mutualLoopTrace : Trace :=
  ⟨[provider (.function 0 [0] [99]) [.function 1 [0] [99]] 2,
    provider (.function 1 [0] [99]) [.function 0 [0] [99]]], [.function 0 [0] [99]]⟩

end IxCCTests.Aiur.Execution
