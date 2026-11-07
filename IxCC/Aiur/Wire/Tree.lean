import IxCC.Aiur.Wire.Op

/-! Complete control trees. The decoder consumes depth only when entering a
block. Its budget never changes the spelling or the meaning of control nodes.
Branch order, fallback presence, return/yield distinction, and all shared
continuation layout fields participate in identity. -/

namespace IxCC.Aiur.Wire

open _root_.Aiur (G)
open _root_.Aiur.Bytecode
open IxCC.Ixon
open IxCC.IxIR

private theorem block_ctrl_smaller (block : Block) : sizeOf block.ctrl < sizeOf block := by
  cases block
  simp only [Block.mk.sizeOf_spec]
  omega

mutual
def ctrlBytes (ctrl : Ctrl) : ByteArray := match ctrl with
  | .match value cases fallback =>
    Encoding.tag 0 ++ Encoding.nat value ++
      Encoding.array (fun ⟨(key, block), _⟩ => fieldBytes key ++ blockBytes block) cases.attach ++
      (match fallback with
        | none => Encoding.tag 0
        | some block => Encoding.tag 1 ++ blockBytes block)
  | .return selector values => Encoding.tag 1 ++ Encoding.nat selector ++ natArrayBytes values
  | .yield selector values => Encoding.tag 2 ++ Encoding.nat selector ++ natArrayBytes values
  | .matchContinue value cases fallback outputs auxiliaries lookups continuation =>
    Encoding.tag 3 ++ Encoding.nat value ++
      Encoding.array (fun ⟨(key, block), _⟩ => fieldBytes key ++ blockBytes block) cases.attach ++
      (match fallback with
        | none => Encoding.tag 0
        | some block => Encoding.tag 1 ++ blockBytes block) ++
      Encoding.nat outputs ++ Encoding.nat auxiliaries ++ Encoding.nat lookups ++ blockBytes continuation
termination_by (sizeOf ctrl, 0)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
    | grind

def blockBytes (block : Block) : ByteArray :=
  Encoding.array opBytes block.ops ++ ctrlBytes block.ctrl
termination_by (sizeOf block, 1)
decreasing_by
  apply Prod.Lex.left
  exact block_ctrl_smaller _
end

def caseBytes (encodeBlock : Block → ByteArray) (branch : G × Block) : ByteArray :=
  fieldBytes branch.1 ++ encodeBlock branch.2

def ctrlBytesWith (encodeBlock : Block → ByteArray) : Ctrl → ByteArray
  | .match value cases fallback => Encoding.tag 0 ++ Encoding.nat value ++
    Encoding.array (caseBytes encodeBlock) cases ++ optionBytes encodeBlock fallback
  | .return selector values => Encoding.tag 1 ++ Encoding.nat selector ++ natArrayBytes values
  | .yield selector values => Encoding.tag 2 ++ Encoding.nat selector ++ natArrayBytes values
  | .matchContinue value cases fallback outputs auxiliaries lookups continuation =>
    Encoding.tag 3 ++ Encoding.nat value ++ Encoding.array (caseBytes encodeBlock) cases ++
      optionBytes encodeBlock fallback ++ Encoding.nat outputs ++ Encoding.nat auxiliaries ++
      Encoding.nat lookups ++ encodeBlock continuation

def ctrlFitsWith (limits : Bounded.Limits) (fitsBlock : Block → Bool) : Ctrl → Bool
  | .match value cases fallback => Bounded.natFits limits value &&
    Bounded.arrayFits limits (fun branch => fitsBlock branch.2) cases && optionFits fitsBlock fallback
  | .return selector values | .yield selector values =>
    Bounded.natFits limits selector && natArrayFits limits values
  | .matchContinue value cases fallback outputs auxiliaries lookups continuation =>
    Bounded.natFits limits value &&
      Bounded.arrayFits limits (fun branch => fitsBlock branch.2) cases && optionFits fitsBlock fallback &&
      Bounded.natFits limits outputs && Bounded.natFits limits auxiliaries &&
      Bounded.natFits limits lookups && fitsBlock continuation

def getCase (readBlock : GetM Block) : GetM (G × Block) := do
  let value ← getField
  let block ← readBlock
  return (value, block)

def getCtrlTag (limits : Bounded.Limits) (readBlock : GetM Block) : UInt8 → GetM Ctrl
  | 0 => do
    let value ← Bounded.getNat limits
    let cases ← Bounded.getArray limits (getCase readBlock)
    let fallback ← getOption readBlock
    return .match value cases fallback
  | 1 => do
    let selector ← Bounded.getNat limits
    let values ← getNatArray limits
    return .return selector values
  | 2 => do
    let selector ← Bounded.getNat limits
    let values ← getNatArray limits
    return .yield selector values
  | 3 => do
    let value ← Bounded.getNat limits
    let cases ← Bounded.getArray limits (getCase readBlock)
    let fallback ← getOption readBlock
    let outputs ← Bounded.getNat limits
    let auxiliaries ← Bounded.getNat limits
    let lookups ← Bounded.getNat limits
    let continuation ← readBlock
    return .matchContinue value cases fallback outputs auxiliaries lookups continuation
  | _ => throw "Aiur control: invalid tag"

def getCtrl (limits : Bounded.Limits) (readBlock : GetM Block) : GetM Ctrl := do
  getCtrlTag limits readBlock (← getU8)

def blockFits (limits : Bounded.Limits) : Nat → Block → Bool
  | 0, _ => false
  | depth + 1, block => Bounded.arrayFits limits (opFits limits) block.ops &&
    ctrlFitsWith limits (blockFits limits depth) block.ctrl

def getBlock (limits : Bounded.Limits) : Nat → GetM Block
  | 0 => throw "Aiur control depth limit"
  | depth + 1 => do
    let ops ← Bounded.getArray limits (getOp limits)
    let ctrl ← getCtrl limits (getBlock limits depth)
    return ⟨ops, ctrl⟩

end IxCC.Aiur.Wire
