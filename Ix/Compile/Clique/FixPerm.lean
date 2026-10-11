/-
  Ix.Compile.Clique.FixPerm: O16, the faithfulness of a transported
  `partial_fixpoint` clique (design document `docs/compiler-passes.md` §5.2,
  decision Q9).

  Lean packs a `partial_fixpoint` clique `f₀ … f_{n-1}` into one fixpoint
  over the right-nested product `γ = T₀ ×' (T₁ ×' …)` in its clique order
  (`PartialFixpoint/Main.lean`, `PProdN.pack`): `f₀.mutual := fix F hF`
  (`Lean.Order.fix`, `Init/Internal/Order/Basic.lean`) for a CCPO, or
  `lfp_monotone F hF` for the lattice-theoretic `inductive_fixpoint` and
  `coinductive_fixpoint`, and `f_i := (f₀.mutual).π_i`. The transport
  (`PartialFixpoint.lean`) emits the same construction over the canonical
  product `γ'` (the factors in the canonical order `σ`): the functional
  `F'` whose component `σ i` is `F_i` with every recursive path `x.π_j`
  replaced by `y.π'_{σ j}`, and the members `g_{σ i} := (fix F' hF').π'_{σ i}`.
  O16 is the statement that the canonical members are Lean's:
  `(fix F' hF').π'_{σ i} = (fix F hF).π_i`.

  **The lemma.** For CCPOs `α` and `β`, an order isomorphism `e : α ≃o β`
  (monotone both ways, mutually inverse) and a monotone `F : α → α`,
  `fix (e ∘ F ∘ e⁻¹) _ = e (fix F hF)` (`fix_iso`). The proof uses only
  that `fix F` is the *least* prefixed point of `F` (`fix_le_of_prefixed`,
  from `fix_induct` with the admissible predicate `· ⊑ x`) and a fixed point
  (`fix_eq`): `e (fix F)` is a fixed point of the conjugate, so the
  conjugate's fixpoint is below it; `e⁻¹` of the conjugate's fixpoint is a
  fixed point of `F`, so `fix F` is below it, and `e` is monotone. The
  lattice variant (`lfp_monotone_iso`) is the same argument with
  `lfp_le_of_le` and `lfp_fix`.

  **The instance.** Re-associating a right-nested `PProd` packing is an
  order isomorphism between the packed orders (the product orders Lean's
  `instCCPOPProd`/`instCompleteLatticePProd` carry): every permutation of
  the factors of `T₀ ×' (T₁ ×' … T_{n-1})` is a composition of adjacent
  transpositions, and the transposition at depth `k` is `pprodCongrRight`
  applied `k` times to `pprodSwap` (the last two factors) or to
  `pprodLeftComm` (two factors with a rest). Their composites are `trans`.
  Each map is a tuple of projections, so the composite `φ` satisfies
  `(φ x).π'_{σ i} ≡ x.π_i` by projection of a constructor.

  **From the lemma to O16.** The transported functional is not written as
  `φ ∘ F ∘ φ⁻¹`, but it is definitionally equal to it: `φ (F (φ⁻¹ y))`
  reduces by β and projection of a constructor to the tuple whose component
  `σ i` is `F_i[(φ⁻¹ y).π_j]`, and `(φ⁻¹ y).π_j ≡ y.π'_{σ j}`. The proofs of
  monotonicity are irrelevant (`fix` takes a `Prop`). So `fix_iso` gives
  `fix F' hF' = φ (fix F hF)` up to that conversion, and projecting at `σ i`
  (`fix_iso_proj`) gives O16 for every member, one conversion step away
  (`fix_swap` checks it on the two-factor transposition). The kernel performs
  the conversion; no further lemma is needed.

  Standard axioms only (`propext`, `Quot.sound`, `Classical.choice` through
  `Lean.Order.CCPO.csup`), no `sorry`.
-/
module
-- `admissible` and `fix` are not exposed by the order library; the proofs
-- below unfold `admissible` (statements mention only exposed constants)
import all Init.Internal.Order.Basic
public section

namespace Ix.Compile.Clique

open Lean.Order

universe u v w

/-- An order isomorphism: monotone maps both ways, mutually inverse. -/
structure OrderIso (α : Sort u) (β : Sort v) [PartialOrder α] [PartialOrder β] where
  toFun : α → β
  invFun : β → α
  mono_toFun : monotone toFun
  mono_invFun : monotone invFun
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

namespace OrderIso

variable {α : Sort u} {β : Sort v} {γ : Sort w}

/-- The conjugate `e ∘ F ∘ e⁻¹` of a monotone function is monotone. -/
theorem monotone_conj [PartialOrder α] [PartialOrder β] (e : OrderIso α β) {F : α → α}
    (hF : monotone F) : monotone (fun b => e.toFun (F (e.invFun b))) :=
  monotone_compose (f := e.invFun) (g := fun a => e.toFun (F a)) e.mono_invFun
    (monotone_compose (f := F) (g := e.toFun) hF e.mono_toFun)

def refl (α : Sort u) [PartialOrder α] : OrderIso α α where
  toFun a := a
  invFun a := a
  mono_toFun := monotone_id
  mono_invFun := monotone_id
  left_inv _ := rfl
  right_inv _ := rfl

def symm [PartialOrder α] [PartialOrder β] (e : OrderIso α β) : OrderIso β α where
  toFun := e.invFun
  invFun := e.toFun
  mono_toFun := e.mono_invFun
  mono_invFun := e.mono_toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

def trans [PartialOrder α] [PartialOrder β] [PartialOrder γ] (e₁ : OrderIso α β)
    (e₂ : OrderIso β γ) : OrderIso α γ where
  toFun a := e₂.toFun (e₁.toFun a)
  invFun c := e₁.invFun (e₂.invFun c)
  mono_toFun := monotone_compose e₁.mono_toFun e₂.mono_toFun
  mono_invFun := monotone_compose e₂.mono_invFun e₁.mono_invFun
  left_inv a := (congrArg e₁.invFun (e₂.left_inv _)).trans (e₁.left_inv a)
  right_inv c := (congrArg e₂.toFun (e₁.right_inv _)).trans (e₂.right_inv c)

end OrderIso

/-! ## The least-fixpoint property of `Lean.Order.fix` -/

/-- `fix f` is below every prefixed point of `f`. -/
theorem fix_le_of_prefixed {α : Sort u} [CCPO α] {f : α → α} (hf : monotone f) {x : α}
    (hx : f x ⊑ x) : fix f hf ⊑ x :=
  fix_induct hf (fun y => y ⊑ x) (fun _ hc h => csup_le hc h)
    (fun _ hy => PartialOrder.rel_trans (hf _ _ hy) hx)

/-- A fixed point below every prefixed point is `fix f`. -/
theorem fix_unique {α : Sort u} [CCPO α] {f : α → α} (hf : monotone f) {p : α}
    (hp : f p = p) (hle : ∀ x, f x ⊑ x → p ⊑ x) : p = fix f hf :=
  PartialOrder.rel_antisymm (hle _ (PartialOrder.rel_of_eq (fix_eq hf).symm))
    (fix_le_of_prefixed hf (PartialOrder.rel_of_eq hp))

/-! ## O16: `fix` commutes with an order isomorphism -/

/-- **O16's lemma.** The fixpoint of the conjugate `e ∘ F ∘ e⁻¹` is the
image of the fixpoint of `F`. -/
theorem fix_iso {α : Sort u} {β : Sort v} [CCPO α] [CCPO β] (e : OrderIso α β)
    {F : α → α} (hF : monotone F) :
    fix (fun b => e.toFun (F (e.invFun b))) (e.monotone_conj hF) = e.toFun (fix F hF) := by
  have hG := e.monotone_conj hF
  apply PartialOrder.rel_antisymm
  · apply fix_le_of_prefixed
    apply PartialOrder.rel_of_eq
    exact (congrArg (fun a => e.toFun (F a)) (e.left_inv _)).trans
      (congrArg e.toFun (fix_eq hF).symm)
  · have h1 : fix F hF ⊑ e.invFun (fix (fun b => e.toFun (F (e.invFun b))) hG) := by
      apply fix_le_of_prefixed
      apply PartialOrder.rel_of_eq
      exact ((congrArg e.invFun (fix_eq hG)).trans (e.left_inv _)).symm
    have h2 := e.mono_toFun _ _ h1
    rw [e.right_inv] at h2
    exact h2

/-- O16 per member: a projection `π` of Lean's fixpoint is the projection
`π'` of the canonical one, whenever `π' ∘ e = π` (for the re-association of
a `PProd` packing, by projection of a constructor). -/
theorem fix_iso_proj {α : Sort u} {β : Sort v} {γ : Sort w} [CCPO α] [CCPO β]
    (e : OrderIso α β) {F : α → α} (hF : monotone F) (π : α → γ) (π' : β → γ)
    (hπ : ∀ a, π' (e.toFun a) = π a) :
    π' (fix (fun b => e.toFun (F (e.invFun b))) (e.monotone_conj hF)) = π (fix F hF) := by
  rw [fix_iso, hπ]

/-! ## The lattice-theoretic variant (`inductive_fixpoint`, `coinductive_fixpoint`) -/

/-- `lfp_monotone` commutes with an order isomorphism between complete
lattices (`coinductive_fixpoint` is `lfp_monotone` in the reversed order,
`ReverseImplicationOrder`, so it is covered too). -/
theorem lfp_monotone_iso {α : Sort u} {β : Sort v} [CompleteLattice α] [CompleteLattice β]
    (e : OrderIso α β) {F : α → α} (hF : monotone F) :
    lfp_monotone (fun b => e.toFun (F (e.invFun b))) (e.monotone_conj hF)
      = e.toFun (lfp_monotone F hF) := by
  have hG := e.monotone_conj hF
  apply PartialOrder.rel_antisymm
  · apply lfp_le_of_le_monotone
    apply PartialOrder.rel_of_eq
    exact (congrArg (fun a => e.toFun (F a)) (e.left_inv _)).trans
      (congrArg e.toFun (lfp_monotone_fix (hm := hF)).symm)
  · have h1 : lfp_monotone F hF ⊑ e.invFun (lfp_monotone (fun b => e.toFun (F (e.invFun b))) hG) := by
      apply lfp_le_of_le_monotone
      apply PartialOrder.rel_of_eq
      exact ((congrArg e.invFun (lfp_monotone_fix (hm := hG))).trans (e.left_inv _)).symm
    have h2 := e.mono_toFun _ _ h1
    rw [e.right_inv] at h2
    exact h2

/-! ## Re-associating a right-nested `PProd` packing -/

section pprod

variable {α : Sort u} {β : Sort v} {γ : Sort w}

/-- The transposition of the last two factors. -/
def pprodSwap [PartialOrder α] [PartialOrder β] : OrderIso (α ×' β) (β ×' α) where
  toFun p := ⟨p.2, p.1⟩
  invFun q := ⟨q.2, q.1⟩
  mono_toFun _ _ h := And.intro (And.right h) (And.left h)
  mono_invFun _ _ h := And.intro (And.right h) (And.left h)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The transposition of the first two factors before a rest. -/
def pprodLeftComm [PartialOrder α] [PartialOrder β] [PartialOrder γ] :
    OrderIso (α ×' (β ×' γ)) (β ×' (α ×' γ)) where
  toFun p := ⟨p.2.1, ⟨p.1, p.2.2⟩⟩
  invFun q := ⟨q.2.1, ⟨q.1, q.2.2⟩⟩
  mono_toFun _ _ h := And.intro (And.left (And.right h)) (And.intro (And.left h) (And.right (And.right h)))
  mono_invFun _ _ h := And.intro (And.left (And.right h)) (And.intro (And.left h) (And.right (And.right h)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- A re-association of the rest, below the first factor. -/
def pprodCongrRight {β' : Sort w} [PartialOrder α] [PartialOrder β] [PartialOrder β']
    (e : OrderIso β β') : OrderIso (α ×' β) (α ×' β') where
  toFun p := ⟨p.1, e.toFun p.2⟩
  invFun q := ⟨q.1, e.invFun q.2⟩
  mono_toFun _ _ h := And.intro (And.left h) (e.mono_toFun _ _ (And.right h))
  mono_invFun _ _ h := And.intro (And.left h) (e.mono_invFun _ _ (And.right h))
  left_inv p := by
    show (⟨p.1, e.invFun (e.toFun p.2)⟩ : α ×' β) = p
    rw [e.left_inv]
  right_inv q := by
    show (⟨q.1, e.toFun (e.invFun q.2)⟩ : α ×' β') = q
    rw [e.right_inv]

/-- O16 on the two-factor transposition, with the functional written as the
transport writes it (each component's recursive paths replaced): it is the
conjugate up to β and projection of a constructor, so `fix_iso` applies as
it stands, and each canonical member is Lean's. -/
theorem fix_swap [CCPO α] [CCPO β] (F₀ : α ×' β → α) (F₁ : α ×' β → β)
    (hF : monotone (fun x => (⟨F₀ x, F₁ x⟩ : α ×' β)))
    (hF' : monotone (fun y : β ×' α => (⟨F₁ ⟨y.2, y.1⟩, F₀ ⟨y.2, y.1⟩⟩ : β ×' α))) :
    (fix (fun y : β ×' α => (⟨F₁ ⟨y.2, y.1⟩, F₀ ⟨y.2, y.1⟩⟩ : β ×' α)) hF').1
        = (fix (fun x => (⟨F₀ x, F₁ x⟩ : α ×' β)) hF).2 ∧
      (fix (fun y : β ×' α => (⟨F₁ ⟨y.2, y.1⟩, F₀ ⟨y.2, y.1⟩⟩ : β ×' α)) hF').2
        = (fix (fun x => (⟨F₀ x, F₁ x⟩ : α ×' β)) hF).1 :=
  have h := fix_iso (pprodSwap (α := α) (β := β)) hF
  ⟨congrArg PProd.fst h, congrArg PProd.snd h⟩

/-- A composite: the rotation of three factors (`σ = [2, 0, 1]`, family
`PF` P0 onto P1), the transposition of the first two and then of the last
two; each component lands where the permutation says, by projection of a
constructor. -/
def pprodRotate3 {δ : Sort w} [PartialOrder α] [PartialOrder β] [PartialOrder δ] :
    OrderIso (α ×' (β ×' δ)) (β ×' (δ ×' α)) :=
  pprodLeftComm.trans (pprodCongrRight pprodSwap)

theorem pprodRotate3_proj {δ : Sort w} [PartialOrder α] [PartialOrder β] [PartialOrder δ]
    (x : α ×' (β ×' δ)) :
    (pprodRotate3.toFun x).2.2 = x.1 ∧ (pprodRotate3.toFun x).1 = x.2.1 ∧
      (pprodRotate3.toFun x).2.1 = x.2.2 :=
  ⟨rfl, rfl, rfl⟩

end pprod

end Ix.Compile.Clique

end
