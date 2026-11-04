/-! # Fixtures of the `kernel-meta-names` oracle (IxC step 6b)

Well-typed declarations whose types and values the oracle prints at `.meta`
and `.source` against Lean's `ppExpr`, and the constants its ill-typed
declarations (built in `Tests.Ix.Kernel.MetaNames`) use. Binder names,
binder infos, lets, shadowing and dependent and non-dependent Π are the
point. -/

namespace MetaNamesFixtures

def idNamed {α : Type} (a : α) : α := a

def constFst (first _second : Nat) : Nat := first

def compose {α β γ : Type} (g : β → γ) (f : α → β) (x : α) : γ := g (f x)

set_option linter.unusedVariables false in
def shadow (x : Nat) : Nat → Nat := fun x => x

def withLet (n : Nat) : Nat :=
  let m := n + 1
  m * m

theorem symmNat (a b : Nat) (h : a = b) : b = a := h.symm

theorem forallProp : ∀ (n : Nat), n = n := fun _n => rfl

theorem depPair (P : Nat → Prop) (k : Nat) (hk : P k) : ∃ j, P j := ⟨k, hk⟩

/-- `needsSucc` wants a proof of a false statement, so an application to
`rfl` mismatches. -/
theorem needsSucc (_f : ∀ (k : Nat), k = k + 1) : True := trivial

theorem needsBool (_b : Bool) : True := trivial

/-- A type that unfolds (δ) to a Π with its own binder name. -/
def PiAlias : Type 1 := (γ : Type) → γ → γ

/-- A constant whose type unfolds, so it is no type itself. -/
def polyId : PiAlias := fun _ x => x

end MetaNamesFixtures
