import IxCCTests.Aiur.Execution.TraceFixtures
import IxCC.Aiur.Static

namespace IxCCTests.Aiur.Static

open IxCC.Aiur
open _root_.IxCC.Vendor.Aiur (G)
open _root_.IxCC.Vendor.Aiur.Bytecode (Block Toplevel)
open IxCCTests.Aiur.Execution (mkFunction provider)

def need (count : IO.Ref Nat) (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"Aiur static certificate regression failed: {label}")
  count.modify (· + 1)

def failed {ε α : Type} [DecidableEq ε] (result : Except ε α) (expected : ε) : Bool :=
  match result with | .error actual => decide (actual = expected) | .ok _ => false

def inputBody (self : Nat) (increasing : Bool) : Block :=
  ⟨#[], .match 0 #[(0, ⟨#[.const 0], .return 0 #[1]⟩)]
    (some ⟨#[.const 1, if increasing then .add 0 1 else .sub 0 1,
      .call self #[2] 1 false], .return 1 #[3]⟩)⟩

def inputProgram (increasing : Bool) : Toplevel :=
  ⟨#[mkFunction 1 (inputBody 0 increasing)], #[], #[], #[⟨0, false⟩]⟩

def inputTrace (increasing : Bool) : Trace :=
  let value := fun n => if increasing then (0 : G) - G.ofNat n else G.ofNat n
  ⟨[provider (.function 0 [value 2] [0]) [.function 0 [value 1] [0]],
    provider (.function 0 [value 1] [0]) [.function 0 [0] [0]],
    provider (.function 0 [0] [0])], [.function 0 [value 2] [0]]⟩

def inputReplies : Array (List OracleEval.Values) := #[[[0]], [[0]], []]

/-- Advice chooses the base case; the input itself is unchanged on every
self-call. Only the output counter can certify these programs. -/
def outputBody (self : Nat) (increasing : Bool) : Block :=
  ⟨#[.unconstrainedGInverse 0],
    .match 1 #[(0, ⟨#[.const 0], .return 0 #[2]⟩)]
      (some ⟨#[.call self #[0] 1 false, .const 1,
        if increasing then .add 2 3 else .sub 2 3], .return 1 #[4]⟩)⟩

def outputProgram (increasing : Bool) : Toplevel :=
  ⟨#[mkFunction 1 (outputBody 0 increasing)], #[], #[], #[⟨0, false⟩]⟩

def outputValue (increasing : Bool) (n : Nat) : G :=
  if increasing then G.ofNat n else 0 - G.ofNat n

def outputTrace (increasing : Bool) : Trace :=
  ⟨[provider (.function 0 [7] [outputValue increasing 2])
      [.function 0 [7] [outputValue increasing 1]],
    provider (.function 0 [7] [outputValue increasing 1]) [.function 0 [7] [0]],
    provider (.function 0 [7] [0])], [.function 0 [7] [outputValue increasing 2]]⟩

def outputReplies (increasing : Bool) : Array (List OracleEval.Values) :=
  #[[[1], [outputValue increasing 1]], [[1], [0]], [[0]]]

/-- The same original component order is legal for these disconnected
ranked and counter functions. Row indices deliberately interleave them. -/
def mixedProgram : Toplevel :=
  ⟨#[mkFunction 1 (inputBody 0 false), mkFunction 1 (inputBody 1 false)],
    #[], #[], #[⟨0, true⟩, ⟨0, false⟩]⟩

def mixedTrace : Trace :=
  ⟨[provider (.function 1 [2] [0]) [.function 1 [1] [0]],
    provider (.function 0 [0] [0]),
    provider (.function 0 [2] [0]) [.function 0 [1] [0]],
    provider (.function 1 [1] [0]) [.function 1 [0] [0]],
    provider (.function 0 [1] [0]) [.function 0 [0] [0]],
    provider (.function 1 [0] [0])], [.function 1 [2] [0], .function 0 [2] [0]]⟩

def mixedRanks : Array Nat := #[9, 2, 0, 8, 1, 7]
def mixedReplies : Array (List OracleEval.Values) := #[[[0]], [], [[0]], [[0]], [[0]], []]

def duplicateTrace : Trace :=
  ⟨[provider (.function 0 [2] [0]) [.function 0 [1] [0]],
    provider (.function 0 [1] [0]) [.function 0 [0] [0]] 2,
    provider (.function 0 [1] [0]) [.function 0 [0] [0]] (0 - 1),
    provider (.function 0 [0] [0]) [] 2], [.function 0 [2] [0]]⟩

def duplicateReplies : Array (List OracleEval.Values) := #[[[0]], [[0]], [[0]], []]

def fallbackProgram : Toplevel := { inputProgram false with callComponents := #[] }

def orderedProgram : Toplevel :=
  { Execution.callProgram with callComponents := #[⟨0, false⟩, ⟨1, false⟩] }

def zeroJunkTrace : Trace :=
  ⟨[provider (.function 999 [] [123]) [.function 0 [2] [0]] 0,
    provider (.function 0 [2] [0]) [.function 0 [1] [0]] 2,
    provider (.function 0 [1] [0]) [.function 0 [0] [0]],
    provider (.function 0 [0] [0])], [.function 0 [2] [0]]⟩

def zeroJunkReplies : Array (List OracleEval.Values) := #[[], [[0]], [[0]], []]

def zeroTrace : Trace := ⟨[], []⟩

def certify (toplevel : Toplevel) (trace : Trace) (ranks : Array Nat)
    (replies : Array (List OracleEval.Values)) (limits : IxCC.Aiur.Static.Limits := {})
    (oracle : OracleEval.AdviceOracle := OracleEval.unrestrictedAdvice) :=
  IxCC.Aiur.Static.validate toplevel oracle trace limits ranks replies

end IxCCTests.Aiur.Static
