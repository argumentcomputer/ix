import IxCC.Aiur.OracleEval.Types

/-! Concrete primitive meanings for logical gadget messages. The tags below
belong to this semantic projection; they are not Rust AIR channel numbers.
An AIR adapter must establish that projection, including affine/compound
outputs and the u32 comparison's range lookups. -/

namespace IxCC.Aiur.OracleEval

open _root_.Aiur (G)

inductive Gadget where
  | bitDecomposition | shiftLeft | shiftRight | xor | add | mul | sub
  | and | or | lessThan | u32LessThan | xorSplit7 | xorSplit4 | rangeCheck
  deriving DecidableEq, BEq, Repr

namespace Gadget

def tag : Gadget → Nat
  | .bitDecomposition => 0 | .shiftLeft => 1 | .shiftRight => 2
  | .xor => 3 | .add => 4 | .mul => 5 | .sub => 6
  | .and => 7 | .or => 8 | .lessThan => 9 | .u32LessThan => 10
  | .xorSplit7 => 11 | .xorSplit4 => 12 | .rangeCheck => 13

def ofTag : Nat → Option Gadget
  | 0 => some .bitDecomposition | 1 => some .shiftLeft | 2 => some .shiftRight
  | 3 => some .xor | 4 => some .add | 5 => some .mul | 6 => some .sub
  | 7 => some .and | 8 => some .or | 9 => some .lessThan | 10 => some .u32LessThan
  | 11 => some .xorSplit7 | 12 => some .xorSplit4 | 13 => some .rangeCheck
  | _ => none

def inputSize : Gadget → Nat
  | .bitDecomposition | .shiftLeft | .shiftRight => 1
  | _ => 2

def outputSize : Gadget → Nat
  | .bitDecomposition => 8
  | .add | .mul | .sub | .xorSplit7 | .xorSplit4 => 2
  | .rangeCheck => 0
  | _ => 1

/-- Complete inputs followed by complete outputs; the tag fixes both arities. -/
def message (gadget : Gadget) (inputs outputs : Values) : Message :=
  .gadget gadget.tag (inputs ++ outputs)

/-- Input range is checked before any bit operation. No truncation licenses
an out-of-range byte or u32 input. -/
def eval (gadget : Gadget) (inputs : Values) : Option Values := do
  let bound := if gadget == .u32LessThan then 2 ^ 32 else 256
  if inputs.length != gadget.inputSize || !(inputs.all (fun value => value.n < bound)) then
    none
  else
    match gadget, inputs with
    | .bitDecomposition, [a] => some ((List.finRange 8).map (G.u8BitDecomposition a))
    | .shiftLeft, [a] => some [G.u8ShiftLeft a]
    | .shiftRight, [a] => some [G.u8ShiftRight a]
    | .xor, [a, b] => some [G.u8Xor a b]
    | .add, [a, b] => let result := G.u8Add a b; some [result.1, result.2]
    | .mul, [a, b] => let result := G.u8Mul a b; some [result.1, result.2]
    | .sub, [a, b] => let result := G.u8Sub a b; some [result.1, result.2]
    | .and, [a, b] => some [G.u8And a b]
    | .or, [a, b] => some [G.u8Or a b]
    | .lessThan, [a, b] => some [G.u8LessThan a b]
    | .u32LessThan, [a, b] => some [G.u32LessThan a b]
    | .xorSplit7, [a, b] =>
        let value := a.n ^^^ b.n
        some [G.ofNat (value / 128), G.ofNat ((value * 2) % 256)]
    | .xorSplit4, [a, b] =>
        let value := a.n ^^^ b.n
        some [G.ofNat (value / 16), G.ofNat ((value * 16) % 256)]
    | .rangeCheck, [_, _] => some []
    | _, _ => none

def check (channel : Nat) (payload : Values) : Bool :=
  match ofTag channel with
  | none => false
  | some gadget =>
      match eval gadget (payload.take gadget.inputSize) with
      | none => false
      | some outputs => decide (payload.drop gadget.inputSize = outputs)

theorem ofTag_tag (gadget : Gadget) : ofTag gadget.tag = some gadget := by
  cases gadget <;> rfl

theorem check_message (gadget : Gadget) (inputs outputs : Values)
    (arity : inputs.length = gadget.inputSize) (correct : eval gadget inputs = some outputs) :
    check gadget.tag (inputs ++ outputs) = true := by
  simp [check, ofTag_tag, ← arity, correct]

end Gadget
end IxCC.Aiur.OracleEval
