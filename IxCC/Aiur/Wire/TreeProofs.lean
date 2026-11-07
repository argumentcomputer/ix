import IxCC.Aiur.Wire.Tree
import IxCC.Aiur.Wire.OpProofs

namespace IxCC.Aiur.Wire

open _root_.IxCC.Vendor.Aiur (G)
open _root_.IxCC.Vendor.Aiur.Bytecode
open IxCC.Ixon
open IxCC.IxIR

private theorem arrayBytes_attach (encode : α → ByteArray) (values : Array α) :
    Encoding.array (fun value => encode value.val) values.attach = Encoding.array encode values := by
  unfold Encoding.array
  rw [Array.foldl_attach (f := fun output value => output ++ encode value)]
  simp

theorem ctrlBytes_eq (ctrl : Ctrl) : ctrlBytes ctrl = ctrlBytesWith blockBytes ctrl := by
  have branches (values : Array (G × Block)) :
      Encoding.array (fun value => fieldBytes value.val.1 ++ blockBytes value.val.2) values.attach =
        Encoding.array (caseBytes blockBytes) values :=
    arrayBytes_attach (caseBytes blockBytes) values
  cases ctrl with
  | «match» _ _ fallback | matchContinue _ _ fallback _ _ _ _ =>
    cases fallback <;> simp only [ctrlBytes, ctrlBytesWith, branches, optionBytes]
  | «return» _ _ | «yield» _ _ => simp only [ctrlBytes, ctrlBytesWith]

theorem getCase_spec (read : GetM Block) (encode : Block → ByteArray) (fits : Block → Bool)
    (spec : ∀ block, fits block = true → GetSpec read (encode block) block)
    (branch : G × Block) (admitted : fits branch.2 = true) :
    GetSpec (getCase read) (caseBytes encode branch) branch :=
  Decode.getSpecMap2 (getField_spec branch.1) (spec branch.2 admitted) Prod.mk

theorem getCtrl_spec (limits : Bounded.Limits) (read : GetM Block)
    (encode : Block → ByteArray) (fits : Block → Bool)
    (spec : ∀ block, fits block = true → GetSpec read (encode block) block)
    (ctrl : Ctrl) (admitted : ctrlFitsWith limits fits ctrl = true) :
    GetSpec (getCtrl limits read) (ctrlBytesWith encode ctrl) ctrl := by
  cases ctrl with
  | «match» value cases fallback =>
    have valueFit : Bounded.natFits limits value = true := by
      simp_all only [ctrlFitsWith, Bool.and_eq_true]
    have casesFit : Bounded.arrayFits limits (fun branch => fits branch.2) cases = true := by
      simp_all only [ctrlFitsWith, Bool.and_eq_true]
    have fallbackFit : optionFits fits fallback = true := by
      simp_all only [ctrlFitsWith, Bool.and_eq_true]
    have payload := Decode.getSpecMap3 (Bounded.getNat_spec limits value valueFit)
      (Bounded.getArray_spec limits (getCase read) (caseBytes encode) (fun branch => fits branch.2)
        (getCase_spec read encode fits spec) cases casesFit)
      (getOption_spec read encode fits spec fallback fallbackFit) Ctrl.match
    have total := GetSpec.bind (next := getCtrlTag limits read) (Decode.getU8_tag_spec 0) payload
    simpa only [getCtrl, ctrlBytesWith, ByteArray.append_assoc] using total
  | «return» selector values | «yield» selector values =>
    have selectorFit : Bounded.natFits limits selector = true := by
      simp_all only [ctrlFitsWith, Bool.and_eq_true]
    have valuesFit : natArrayFits limits values = true := by
      simp_all only [ctrlFitsWith, Bool.and_eq_true]
    first
    | have payload := Decode.getSpecMap2 (Bounded.getNat_spec limits selector selectorFit)
        (getNatArray_spec limits values valuesFit) Ctrl.return
      have total := GetSpec.bind (next := getCtrlTag limits read) (Decode.getU8_tag_spec 1) payload
      simpa only [getCtrl, ctrlBytesWith, ByteArray.append_assoc] using total
    | have payload := Decode.getSpecMap2 (Bounded.getNat_spec limits selector selectorFit)
        (getNatArray_spec limits values valuesFit) Ctrl.yield
      have total := GetSpec.bind (next := getCtrlTag limits read) (Decode.getU8_tag_spec 2) payload
      simpa only [getCtrl, ctrlBytesWith, ByteArray.append_assoc] using total
  | matchContinue value cases fallback outputs auxiliaries lookups continuation =>
    have valueFit : Bounded.natFits limits value = true := by
      simp_all only [ctrlFitsWith, Bool.and_eq_true]
    have casesFit : Bounded.arrayFits limits (fun branch => fits branch.2) cases = true := by
      simp_all only [ctrlFitsWith, Bool.and_eq_true]
    have fallbackFit : optionFits fits fallback = true := by
      simp_all only [ctrlFitsWith, Bool.and_eq_true]
    have outputsFit : Bounded.natFits limits outputs = true := by
      simp_all only [ctrlFitsWith, Bool.and_eq_true]
    have auxiliariesFit : Bounded.natFits limits auxiliaries = true := by
      simp_all only [ctrlFitsWith, Bool.and_eq_true]
    have lookupsFit : Bounded.natFits limits lookups = true := by
      simp_all only [ctrlFitsWith, Bool.and_eq_true]
    have continuationFit : fits continuation = true := by
      simp_all only [ctrlFitsWith, Bool.and_eq_true]
    have payload := Bounded.getSpecMap7 (Bounded.getNat_spec limits value valueFit)
      (Bounded.getArray_spec limits (getCase read) (caseBytes encode) (fun branch => fits branch.2)
        (getCase_spec read encode fits spec) cases casesFit)
      (getOption_spec read encode fits spec fallback fallbackFit)
      (Bounded.getNat_spec limits outputs outputsFit)
      (Bounded.getNat_spec limits auxiliaries auxiliariesFit)
      (Bounded.getNat_spec limits lookups lookupsFit)
      (spec continuation continuationFit) Ctrl.matchContinue
    have total := GetSpec.bind (next := getCtrlTag limits read) (Decode.getU8_tag_spec 3) payload
    simpa only [getCtrl, ctrlBytesWith, ByteArray.append_assoc] using total

theorem getBlock_spec (limits : Bounded.Limits) (depth : Nat) (block : Block)
    (admitted : blockFits limits depth block = true) :
    GetSpec (getBlock limits depth) (blockBytes block) block := by
  induction depth generalizing block with
  | zero => simp [blockFits] at admitted
  | succ depth ih =>
    have opsFit : Bounded.arrayFits limits (opFits limits) block.ops = true := by
      simp_all only [blockFits, Bool.and_eq_true]
    have ctrlFit : ctrlFitsWith limits (blockFits limits depth) block.ctrl = true := by
      simp_all only [blockFits, Bool.and_eq_true]
    have total := Decode.getSpecMap2
      (Bounded.getArray_spec limits (getOp limits) opBytes (opFits limits)
        (getOp_spec limits) block.ops opsFit)
      (getCtrl_spec limits (getBlock limits depth) blockBytes (blockFits limits depth)
        (fun block admitted => ih block admitted) block.ctrl ctrlFit) Block.mk
    cases block
    simpa only [getBlock, blockBytes, ctrlBytes_eq] using total

end IxCC.Aiur.Wire
