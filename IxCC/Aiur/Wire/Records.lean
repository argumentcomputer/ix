import IxCC.Aiur.Wire.Tree

/-! Every field of the pinned top-level bytecode records participates in the
wire identity, including layout-only metadata and ordered circuit members. -/

namespace IxCC.Aiur.Wire

open _root_.IxCC.Vendor.Aiur.Bytecode
open IxCC.Ixon
open IxCC.IxIR

def layoutBytes (value : FunctionLayout) : ByteArray :=
  Encoding.nat value.inputSize ++ Encoding.nat value.selectors ++
    Encoding.nat value.auxiliaries ++ Encoding.nat value.lookups

def layoutFits (limits : Bounded.Limits) (value : FunctionLayout) : Bool :=
  Bounded.natFits limits value.inputSize && Bounded.natFits limits value.selectors &&
    Bounded.natFits limits value.auxiliaries && Bounded.natFits limits value.lookups

def getLayout (limits : Bounded.Limits) : GetM FunctionLayout := do
  return ⟨← Bounded.getNat limits, ← Bounded.getNat limits,
    ← Bounded.getNat limits, ← Bounded.getNat limits⟩

def functionBytes (value : Function) : ByteArray :=
  blockBytes value.body ++ layoutBytes value.layout ++
    Encoding.bool value.entry ++ Encoding.bool value.constrained

def functionFits (limits : Limits) (value : Function) : Bool :=
  blockFits limits.toLimits limits.maxDepth value.body && layoutFits limits.toLimits value.layout

def getFunction (limits : Limits) : GetM Function := do
  return ⟨← getBlock limits.toLimits limits.maxDepth, ← getLayout limits.toLimits,
    ← Decode.getBool, ← Decode.getBool⟩

def circuitBytes (value : Circuit) : ByteArray :=
  Encoding.string value.name ++ natArrayBytes value.members ++ layoutBytes value.layout

def circuitFits (limits : Bounded.Limits) (value : Circuit) : Bool :=
  Bounded.stringFits limits value.name && natArrayFits limits value.members && layoutFits limits value.layout

def getCircuit (limits : Bounded.Limits) : GetM Circuit := do
  return ⟨← Bounded.getString limits, ← getNatArray limits, ← getLayout limits⟩

def componentBytes (value : CallComponent) : ByteArray :=
  Encoding.nat value.order ++ Encoding.bool value.ranked

def componentFits (limits : Bounded.Limits) (value : CallComponent) : Bool :=
  Bounded.natFits limits value.order

def getComponent (limits : Bounded.Limits) : GetM CallComponent := do
  return ⟨← Bounded.getNat limits, ← Decode.getBool⟩

def toplevelBytes (value : Toplevel) : ByteArray :=
  Encoding.array functionBytes value.functions ++ natArrayBytes value.memorySizes ++
    Encoding.array circuitBytes value.circuits ++ Encoding.array componentBytes value.callComponents

def toplevelFits (limits : Limits) (value : Toplevel) : Bool :=
  Bounded.arrayFits limits.toLimits (functionFits limits) value.functions &&
    natArrayFits limits.toLimits value.memorySizes &&
    Bounded.arrayFits limits.toLimits (circuitFits limits.toLimits) value.circuits &&
    Bounded.arrayFits limits.toLimits (componentFits limits.toLimits) value.callComponents

def getToplevel (limits : Limits) : GetM Toplevel := do
  return ⟨← Bounded.getArray limits.toLimits (getFunction limits), ← getNatArray limits.toLimits,
    ← Bounded.getArray limits.toLimits (getCircuit limits.toLimits),
    ← Bounded.getArray limits.toLimits (getComponent limits.toLimits)⟩

end IxCC.Aiur.Wire
