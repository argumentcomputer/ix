module

public import ConLeche.Semantics.WellDenoted
public import ConLeche.Semantics.Sat

@[expose] public section

/-!
# `SetBase/Hoist` — the `WellDenoted` hoist kit

The generation-four hoist kit, re-based out of
`SetR/Interp/Steps/Dispatch.lean` at THE SEPARATION's S2 (task #161).

Every lemma here is an implication between `∀ ρ, Sat V Δa ρ → …`
shapes: the splitters that take a hoisted node fact apart, the
converses that build one from its parts, the head transfer that moves a
hoisted fact across a domain equality, and the lift.  They mention no
fuel, no `denoteAnnot`, no run and no environment — the trap-check section
at the end of this file makes exactly that observation — and both
lanes' quarters consume them at every congruence.

The one thing left behind in `Dispatch` is the `CtxOk2.openCong`
satisfiability example, which is about `CtxOk2` and therefore 2U.

Statements verbatim, namespace (`ConLeche.SetR.Interp`) unchanged.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.Semantics (AnnotTerm)

universe w

variable {V : Type w} [SetTheory V]

/-- **The positive half: the hoist is self-propagating at a `∀`.**  A
hoisted `WellDenoted` of the node gives the domain's hoisted form and the
codomain's *in the extended context*, which is exactly the pair the
recursive call needs.  So paying the repair at the congruence costs
nothing beyond restating it. -/
theorem WellDenoted.hoist_pi {Δa : List AnnotTerm} {u v : Nat} {A B : AnnotTerm}
    (h : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ (.pi u v A B)) :
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ A) ∧
      (∀ ρ : Nat → V, Sat V (A :: Δa) ρ → WellDenoted V ρ B) := by
  refine ⟨fun ρ hρ => ((WellDenoted_pi V ρ u v A B) ▸ h ρ hρ).1,
    fun ρ hρ => ?_⟩
  have hcons : cons (ρ 0) (fun j => ρ (j + 1)) = ρ := by
    funext i; cases i with | zero => rfl | succ i => rfl
  have := ((WellDenoted_pi V _ u v A B) ▸ h _ (Sat_tail hρ)).2
    (ρ 0) (hρ 0 A rfl)
  rwa [hcons] at this

/-- The same at a `λ`, where the node's second component has the same
shape.  Together these cover all five congruence sites. -/
theorem WellDenoted.hoist_lam {Δa : List AnnotTerm} {v : Nat} {A b : AnnotTerm}
    (h : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ (.lam v A b)) :
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ A) ∧
      (∀ ρ : Nat → V, Sat V (A :: Δa) ρ → WellDenoted V ρ b) := by
  refine ⟨fun ρ hρ => ((WellDenoted_lam V ρ v A b) ▸ h ρ hρ).1,
    fun ρ hρ => ?_⟩
  have hcons : cons (ρ 0) (fun j => ρ (j + 1)) = ρ := by
    funext i; cases i with | zero => rfl | succ i => rfl
  have := ((WellDenoted_lam V _ v A b) ▸ h _ (Sat_tail hρ)).2.1
    (ρ 0) (hρ 0 A rfl)
  rwa [hcons] at this

/-! ## The hoist kit, generation four — the complete list

`hoist_pi`/`hoist_lam` above are the two shapes the congruences named,
and they are stated exactly as a consumer holding
`∀ ρ, Sat V Δa ρ → WellDenoted V ρ (.pi u v A B)` wants them: the
domain's hoisted form over `Δa`, and the codomain's hoisted form over
the **extended** context `A :: Δa`.  That is the pair a recursive call
into the claim family takes.

Audited against that use, three things were missing and are added
here.

1. **The non-binder splitters** (`hoist_app`, `hoist_fst`/`hoist_snd`,
   `hoist_eqE`) and the contraction form `hoist_beta_pos`.
   Mechanical, but a quarter that re-derives them re-derives them four
   times.
2. **The converses** (`of_pi`, `of_lam`, `of_app`,
   `of_fst`/`of_snd`, `of_eqE`).  `WhnfCoreClaims2C`/`WhnfClaims2C` and
   `InferClaims2C` now *deliver* a ρ-uniform `WellDenoted`, so assembling
   the node fact from its parts' hoisted forms is an obligation this
   generation created.  `Sat_cons` is the whole content of the binder
   ones; the semantic components (the `λ`'s fibre, the app's slot)
   stay per-valuation, because they are memberships and not gradings.
3. **The head transfer** (`Sat.head_congr`,
   `WellDenoted.hoist_head_congr`) — *the piece without which the split
   kit does not reach its own motivating site.*  `CtxOk2.openCong`
   extends the context with the **left** domain `ta₁`, while
   `hoist_pi`/`hoist_lam` deliver the right side's codomain fact over
   `ta₂ :: Δa`.  The two lists differ in their head and nothing else
   relates them; the bridge is the domains' own semantic agreement,
   which is `DefEqClaims2C`'s conclusion — already in hand at every
   congruence.

**Two shapes are deliberately absent, and the absence is a finding.**

* There is **no `letE` shape at all** — the syntax lost the former at
  task #241, and with it the splitter's original difficulty (the clause
  read the body at the *value's* point, which `Sat (T :: Δa)` cannot
  supply).
* There is **no unconditional `of_lam`**.  The `λ` clause's fibre
  component is a genuinely per-valuation semantic fact with no
  hereditary source, so the converse takes it as a premise. -/

/-- The application splits into its two parts, both hoisted.  The slot
component stays per-valuation: it is a membership, not a grading. -/
theorem WellDenoted.hoist_app {Δa : List AnnotTerm} {f a : AnnotTerm}
    (h : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ (.app f a)) :
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ f) ∧
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ a) :=
  ⟨fun ρ hρ => ((WellDenoted_app V ρ f a) ▸ h ρ hρ).1,
    fun ρ hρ => ((WellDenoted_app V ρ f a) ▸ h ρ hρ).2.1⟩


/-- The first projection's subject. -/
theorem WellDenoted.hoist_fst {Δa : List AnnotTerm} {e : AnnotTerm}
    (h : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ (.fst e)) :
    ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ e :=
  fun ρ hρ => ((WellDenoted_fst V ρ e) ▸ h ρ hρ).1

/-- The second projection's subject. -/
theorem WellDenoted.hoist_snd {Δa : List AnnotTerm} {e : AnnotTerm}
    (h : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ (.snd e)) :
    ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ e :=
  fun ρ hρ => ((WellDenoted_snd V ρ e) ▸ h ρ hρ).1

/-- The equality node's two sides. -/
theorem WellDenoted.hoist_eqE {Δa : List AnnotTerm} {a b : AnnotTerm}
    (h : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ (.eqE a b)) :
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ a) ∧
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ b) :=
  ⟨fun ρ hρ => ((WellDenoted_eqE V ρ a b) ▸ h ρ hρ).1,
    fun ρ hρ => ((WellDenoted_eqE V ρ a b) ▸ h ρ hρ).2⟩

/-- The β contractum, hoisted, at a positive codomain kind. -/
theorem WellDenoted.hoist_beta_pos {Δa : List AnnotTerm} {v : Nat}
    (hv : v ≠ 0) {A b a : AnnotTerm}
    (h : ∀ ρ : Nat → V, Sat V Δa ρ →
      WellDenoted V ρ (.app (.lam v A b) a)) :
    ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ (b.inst a) :=
  fun ρ hρ => (WellDenoted_beta_pos V hv (h ρ hρ)).2


/-! ### The converses -/

/-- **The converse at a `Π`.**  `Sat_cons` is the whole content: an
inhabitant of the domain extends the valuation into `A :: Δa`. -/
theorem WellDenoted.of_pi {Δa : List AnnotTerm} {u v : Nat} {A B : AnnotTerm}
    (hA : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ A)
    (hB : ∀ ρ : Nat → V, Sat V (A :: Δa) ρ → WellDenoted V ρ B) :
    ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ (.pi u v A B) := by
  intro ρ hρ
  rw [WellDenoted_pi]
  exact ⟨hA ρ hρ, fun x hx => hB _ (Sat_cons (V := V) hρ hx)⟩

/-- **The converse at a `λ`.**  The fibre component has no hereditary
source and is therefore a premise, stated per-valuation because that
is what it is. -/
theorem WellDenoted.of_lam {Δa : List AnnotTerm} {v : Nat} {A b : AnnotTerm}
    (hA : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ A)
    (hb : ∀ ρ : Nat → V, Sat V (A :: Δa) ρ → WellDenoted V ρ b)
    (hfib : ∀ ρ : Nat → V, Sat V Δa ρ → ∃ B : V → V,
      (∀ x, x ∈ˢ interp V ρ A → interp V (cons x ρ) b ∈ˢ B x) ∧
      (v = 0 → ∀ x, x ∈ˢ interp V ρ A →
        B x ∈ˢ (univZero : V))) :
    ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ (.lam v A b) := by
  intro ρ hρ
  rw [WellDenoted_lam]
  exact ⟨hA ρ hρ, fun x hx => hb _ (Sat_cons (V := V) hρ hx),
    hfib ρ hρ⟩

/-- **The converse at an application.**  The slot stays
per-valuation; `WellDenoted_app_of` (`Annot/WellDenoted.lean`) is the shape that
builds it from an annotated `Π`. -/
theorem WellDenoted.of_app {Δa : List AnnotTerm} {f a : AnnotTerm}
    (hf : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ f)
    (ha : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ a)
    (hslot : ∀ ρ : Nat → V, Sat V Δa ρ →
      ∃ (v : Nat) (A : V) (B : V → V),
        interp V ρ f ∈ˢ piR v A B ∧ interp V ρ a ∈ˢ A ∧
        (v = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V))) :
    ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ (.app f a) := by
  intro ρ hρ
  rw [WellDenoted_app]
  exact ⟨hf ρ hρ, ha ρ hρ, hslot ρ hρ⟩


/-- The converse at a first projection. -/
theorem WellDenoted.of_fst {Δa : List AnnotTerm} {e : AnnotTerm}
    (he : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ e)
    (hsig : ∀ ρ : Nat → V, Sat V Δa ρ → ∃ u v A Bf,
      interp V ρ e ∈ˢ sigmaSet (Nat.max u v) A Bf ∧
      A ∈ˢ (univ u : V) ∧ ∀ x, x ∈ˢ A → Bf x ∈ˢ (univ v : V)) :
    ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ (.fst e) := by
  intro ρ hρ
  rw [WellDenoted_fst]
  exact ⟨he ρ hρ, hsig ρ hρ⟩

/-- The converse at a second projection. -/
theorem WellDenoted.of_snd {Δa : List AnnotTerm} {e : AnnotTerm}
    (he : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ e)
    (hsig : ∀ ρ : Nat → V, Sat V Δa ρ → ∃ u v A Bf,
      interp V ρ e ∈ˢ sigmaSet (Nat.max u v) A Bf ∧
      A ∈ˢ (univ u : V) ∧ ∀ x, x ∈ˢ A → Bf x ∈ˢ (univ v : V)) :
    ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ (.snd e) := by
  intro ρ hρ
  rw [WellDenoted_snd]
  exact ⟨he ρ hρ, hsig ρ hρ⟩

/-- The converse at an equality node. -/
theorem WellDenoted.of_eqE {Δa : List AnnotTerm} {a b : AnnotTerm}
    (ha : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ a)
    (hb : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ b) :
    ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ (.eqE a b) := by
  intro ρ hρ
  rw [WellDenoted_eqE]
  exact ⟨ha ρ hρ, hb ρ hρ⟩

/-! ### The head transfer — what makes the kit reach `openCong`

Without these two the split kit stops one step short of the sites it
was built for: `hoist_pi`/`hoist_lam` hand the right side's codomain
fact over `ta₂ :: Δa`, and the recursive call runs in `ta₁ :: Δa`. -/

/-- **A satisfying valuation transfers across a head equality.**
`Sat` reads the head at the *tail* valuation, which is exactly where
the domains' agreement is stated, so the transfer is immediate. -/
theorem Sat.head_congr {Δa : List AnnotTerm} {A B : AnnotTerm}
    {ρ : Nat → V}
    (heq : ∀ ρ' : Nat → V, Sat V Δa ρ' →
      interp V ρ' A = interp V ρ' B)
    (hρ : Sat V (A :: Δa) ρ) : Sat V (B :: Δa) ρ := by
  intro i Aa hi
  cases i with
  | zero =>
    obtain rfl : B = Aa := by simpa using hi
    have h0 : ρ 0 ∈ˢ interp V (fun j => ρ (j + 1)) A := hρ 0 A rfl
    show ρ 0 ∈ˢ interp V (fun j => ρ (j + 1)) B
    rwa [heq _ (Sat_tail hρ)] at h0
  | succ i => exact hρ (i + 1) Aa (by simpa using hi)

/-- **A hoisted fact transfers with it.**  `heq` is
`DefEqClaims2C`'s conclusion; `h` is `hoist_pi.2`/`hoist_lam.2` on the
right side; the result is what the recursive call in `ta₁ :: Δa`
takes. -/
theorem WellDenoted.hoist_head_congr {Δa : List AnnotTerm} {A B e : AnnotTerm}
    (heq : ∀ ρ : Nat → V, Sat V Δa ρ →
      interp V ρ A = interp V ρ B)
    (h : ∀ ρ : Nat → V, Sat V (B :: Δa) ρ → WellDenoted V ρ e) :
    ∀ ρ : Nat → V, Sat V (A :: Δa) ρ → WellDenoted V ρ e :=
  fun ρ hρ => h ρ (Sat.head_congr heq hρ)

/-- **Weakening a hoisted fact under one more binder.**  The
annotation lifts and `Sat_tail` carries the valuation; the transpose
of `CtxOk2.weakenTop` for the grading. -/
theorem WellDenoted.hoist_lift {Δa : List AnnotTerm} {X e : AnnotTerm}
    (h : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ e) :
    ∀ ρ : Nat → V, Sat V (X :: Δa) ρ → WellDenoted V ρ e.lift := by
  intro ρ hρ
  refine (WellDenoted_liftN V 1 e 0 ρ).mpr ?_
  rw [shiftE_zero]
  exact h _ (Sat_tail hρ)

/-! ### Trap-check on the kit

Every lemma above is an implication between `∀ ρ, Sat → …` shapes and
mentions no fuel, no `denoteAnnot` and no run, so the smallest-fuel test
has nothing to bite on — and, per seal 11, that is *not* a clean bill
of health on its own.  The semantic check that matters is inhabitation
in a *non-vacuous* context, which the two examples below give: the
splitters and the converses are exercised at a `Δa` whose `Sat` is
satisfiable, so neither direction is a vacuous implication. -/

/-- `ρ ≡ ∅` satisfies `[⟪Sort 0⟫]`: the context used below is
genuinely inhabited. -/
private theorem sat_sort0_empty :
    Sat V [AnnotTerm.sort 0] (fun _ => (empty : V)) := by
  intro i Aa hi
  cases i with
  | zero =>
    obtain rfl : AnnotTerm.sort 0 = Aa := by simpa using hi
    simpa using empty_mem_univ (V := V) 0
  | succ i => simp at hi

/-- The converse builds a `Π` fact over that context and the splitter
takes it back apart, so neither direction of the kit is a vacuous
implication. -/
example :
    WellDenoted V (fun _ => (empty : V))
      (.pi 1 2 (.sort 0) (.sort 1)) ∧
    (∀ ρ : Nat → V, Sat V [AnnotTerm.sort 0] ρ →
      WellDenoted V ρ (AnnotTerm.sort 0)) := by
  have hpi : ∀ ρ : Nat → V, Sat V [AnnotTerm.sort 0] ρ →
      WellDenoted V ρ (.pi 1 2 (.sort 0) (.sort 1)) :=
    WellDenoted.of_pi (fun _ _ => by simp) (fun _ _ => by simp)
  exact ⟨hpi _ sat_sort0_empty, (WellDenoted.hoist_pi hpi).1⟩

end ConLeche.Semantics
