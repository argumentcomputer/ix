import IxCC.Aiur.Wire.Records
import IxCC.Aiur.Wire.TreeProofs

namespace IxCC.Aiur.Wire

open _root_.IxCC.Vendor.Aiur.Bytecode
open IxCC.Ixon
open IxCC.IxIR

theorem getLayout_spec (limits : Bounded.Limits) (value : FunctionLayout)
    (admitted : layoutFits limits value = true) :
    GetSpec (getLayout limits) (layoutBytes value) value := by
  simp only [layoutFits, Bool.and_eq_true] at admitted
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := admitted
  have total := Decode.getSpecMap4 (Bounded.getNat_spec limits value.inputSize h0)
    (Bounded.getNat_spec limits value.selectors h1)
    (Bounded.getNat_spec limits value.auxiliaries h2)
    (Bounded.getNat_spec limits value.lookups h3) FunctionLayout.mk
  simpa only [getLayout, layoutBytes] using total

theorem getFunction_spec (limits : Limits) (value : Function)
    (admitted : functionFits limits value = true) :
    GetSpec (getFunction limits) (functionBytes value) value := by
  simp only [functionFits, Bool.and_eq_true] at admitted
  have h := admitted
  have total := Decode.getSpecMap4
    (getBlock_spec limits.toLimits limits.maxDepth value.body h.1)
    (getLayout_spec limits.toLimits value.layout h.2)
    (Decode.getBool_spec value.entry) (Decode.getBool_spec value.constrained) Function.mk
  simpa only [getFunction, functionBytes] using total

theorem getCircuit_spec (limits : Bounded.Limits) (value : Circuit)
    (admitted : circuitFits limits value = true) :
    GetSpec (getCircuit limits) (circuitBytes value) value := by
  simp only [circuitFits, Bool.and_eq_true] at admitted
  have h := admitted
  have h' := h.1
  have total := Decode.getSpecMap3 (Bounded.getString_spec limits value.name h'.1)
    (getNatArray_spec limits value.members h'.2) (getLayout_spec limits value.layout h.2) Circuit.mk
  simpa only [getCircuit, circuitBytes] using total

theorem getComponent_spec (limits : Bounded.Limits) (value : CallComponent)
    (admitted : componentFits limits value = true) :
    GetSpec (getComponent limits) (componentBytes value) value := by
  have total := Decode.getSpecMap2 (Bounded.getNat_spec limits value.order admitted)
    (Decode.getBool_spec value.ranked) CallComponent.mk
  simpa only [getComponent, componentBytes] using total

theorem getToplevel_spec (limits : Limits) (value : Toplevel)
    (admitted : toplevelFits limits value = true) :
    GetSpec (getToplevel limits) (toplevelBytes value) value := by
  simp only [toplevelFits, Bool.and_eq_true] at admitted
  have h := admitted
  have h' := h.1
  have h'' := h'.1
  have total := Decode.getSpecMap4
    (Bounded.getArray_spec limits.toLimits (getFunction limits) functionBytes (functionFits limits)
      (getFunction_spec limits) value.functions h''.1)
    (getNatArray_spec limits.toLimits value.memorySizes h''.2)
    (Bounded.getArray_spec limits.toLimits (getCircuit limits.toLimits) circuitBytes
      (circuitFits limits.toLimits) (getCircuit_spec limits.toLimits) value.circuits h'.2)
    (Bounded.getArray_spec limits.toLimits (getComponent limits.toLimits) componentBytes
      (componentFits limits.toLimits) (getComponent_spec limits.toLimits) value.callComponents h.2)
    Toplevel.mk
  simpa only [getToplevel, toplevelBytes] using total

end IxCC.Aiur.Wire
