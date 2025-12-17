import Lean
import Ix.Address

namespace Ix

@[extern "c_rs_compile_consts"]
opaque compileConsts : @& Lean.Name →
  @& List (Lean.Name × Lean.ConstantInfo) → Address × Array (Address × ByteArray)

end Ix
