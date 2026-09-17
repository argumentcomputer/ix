import Compilatrix.Ixby.Stage2.FriSound

namespace CompilatrixTests.Ixby.Fri.Examples

def original (n : Nat) : Nat := n + 0
def target (n : Nat) : Nat := n
def alternate (n : Nat) : Nat := n
def second (n : Nat) : Nat := 0 + n

theorem original_eq : original = target := rfl
theorem reverse_eq : target = original := rfl
theorem chain_eq : target = alternate := rfl
theorem second_eq : second = target := funext Nat.zero_add
theorem unchanged_eq : original = original := rfl
theorem conditional_eq (_condition : True) : original = target := rfl

def polymorphic {α : Type u} (a : α) : α := a
def polymorphicTarget {α : Type u} (a : α) : α := a
theorem polymorphic_eq : @polymorphic = @polymorphicTarget := rfl

def sameExtensionAdd (a b : Ix.Ixby.ExtGoldilocks) := a.add b
theorem protected_eq : Ix.Ixby.ExtGoldilocks.add = sameExtensionAdd := rfl

end CompilatrixTests.Ixby.Fri.Examples
