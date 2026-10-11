/-
  Sources of the `adversarial-matrix` suite (imports only `Init`): two
  theorems with different statements of the same shape (a redirect target),
  and a definition with a library dependency (an omitted-dependency target).
-/
namespace Tests.Ix.Compile.AdversarialMatrix.Src

theorem addZero (n : Nat) : n + 0 = n := rfl

theorem zeroAdd (n : Nat) : 0 + n = n := Nat.zero_add n

def double (n : Nat) : Nat := n + n

end Tests.Ix.Compile.AdversarialMatrix.Src
