namespace Binius

private opaque GenericNonempty : NonemptyType

def ConstraintSystem : Type := GenericNonempty.type

instance : Nonempty ConstraintSystem := GenericNonempty.property

end Binius
