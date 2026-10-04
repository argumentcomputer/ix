namespace CorpusOwnership

private def helper (n : Nat) : Nat := n + 1
private theorem helper_zero : helper 0 = 1 := rfl
def exposed : Nat := helper 0
theorem exposed_one : exposed = 1 := helper_zero

end CorpusOwnership

namespace Nat
def corpusOwnershipControl : Nat := 1
end Nat
