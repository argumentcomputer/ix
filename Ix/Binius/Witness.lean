namespace Binius

private opaque GenericNonempty : NonemptyType

def Witness : Type := GenericNonempty.type

instance : Nonempty Witness := GenericNonempty.property

end Binius
