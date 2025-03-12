import Ix.Binius.Boundary
import Ix.Binius.Witness

namespace Binius

private opaque GenericNonempty : NonemptyType

def ConstraintSystem : Type := GenericNonempty.type

instance : Nonempty ConstraintSystem := GenericNonempty.property

namespace ConstraintSystem

@[extern "c_rs_constraint_system_validate_witness"]
opaque validateWitness : @& ConstraintSystem → @& Array Boundary → @& Witness → Bool

end ConstraintSystem

end Binius
