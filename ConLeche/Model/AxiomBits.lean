module

import ConLeche.Model.ErasePwInv
public import ConLeche.Model.Harvest
import ConLeche.Verify.BinderLoop
/- `ConLeche.Kernel.PropWhen` seals its representation on purpose (the
`Std.HashMap` pattern, task #194): the datum's module is `public` but not
`@[expose]`d, so a `cases`-then-`rfl` proof cannot see the reduct.
`import all` restores that view HERE only. -/
import all ConLeche.Kernel.PropWhen

public section

/-!
# The pin tier's bit lemmas (task #161, ENDGAME B, task 1a)

**The named fact of the ENDGAME A seal, mechanized.**  `AxiomPinP`'s
WALL record says what the pin tier cannot have — `denoteP_matchesPin`
is false, because `Expr.erasePw` normalizes every binder datum to
`.never` and `denoteMeta` *reads* those data.  What it can have, and what
this file supplies, is the bits themselves, taken where the ruling
says to take them: from `ConstantValR`'s own recorded
`inferTypeCore` run on the stored type.

## The three moves, per pinned family

1. **the shape** — `matchesPin` fixes the stored type up to binder
   names and binder metas, so a chain of `erasePw`
   inversions (`erasePwNames_*_invS`, below) recovers the telescope
   with exactly those free.  Every domain and body of the standard
   pins is binder-free, hence erasure-rigid, so the inversion is
   mechanical;
2. **the innermost codomain's sort** — executed symbolically off the
   recorded run.  For `propext` this is the `Eq`-spine, and it is
   computable rather than erasure-chased *because `stdAxiomOk` pins
   the stored `Eq` on the nose* (`env.find? eqName = some eqA`, an
   equality of `ConstantInfo`s — the ENDGAME A resume-here
   refinement): three `app` inversions peel the pinned
   `∀ (α : Sort 1) (a b : α), Prop` to `Prop` outright;
3. **the collapse** — `inferTypeCore_forall_inv`'s validation
   conjunct `Level.zeronessOf v = mb.pw` converts to the
   bit by `pwBit_zeronessOf`, and the *telescope collapse*
   `Level.eval φ (imax u v) = 0 ↔ Level.eval φ v = 0` makes it **one
   fact per pin rather than one per binder**: the ∀ clause's own
   result `.sort (.imax u v)` carries the innermost bit outward
   through every remaining binder.

`whnf_forallE_eq` (a `∀`-tower is its own whnf) and its sort twin
below are what make move 2 fuel-free: the run's fuel is whatever
`ConstantValR` recorded, and both identities hold at *any* fuel that
succeeds, by monotonicity.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  BinderMeta inferTypeCore whnf ensureSortCore)

variable {μ : CheckMode} {env : Env}

/-! ## The double-erasure inversions

`ConstantVal.matchesPin` compares through `erasePw` *and*
`eraseNames`.  `Install/Axiom.lean` has the two constant-head
inversions; the pinned telescopes need the four remaining heads, and
composing the two erasures once here keeps every consumer's chain one
step per node. -/

-- The five `erasePw` head inversions moved to
-- `Interp/ErasePwInv.lean` at ENDGAME D: the reduce-operation pin
-- (`Interp/ReduceOps.lean`) needs them and sits *below* `HarvestP`,
-- which this file imports.  Statements unchanged.

/-! ## Fuel-free run identities -/

/-- `whnf` is the identity on a sort, at whatever fuel the recorded
run used (`whnf_forallE_eq`'s twin, by the same monotonicity step). -/
theorem whnf_sort_eq {fuel d : Nat} {u : Level} {e' : Expr}
    (h : whnf μ env fuel d (.sort u) = .ok e') : e' = .sort u := by
  have h1 := ConLeche.whnf_mono (Nat.le_add_right fuel 2) h
  rw [ConLeche.whnf_sort env fuel d u] at h1
  exact (Except.ok.inj h1).symm

/-- `ensureSortCore` on a literal sort returns that level. -/
theorem ensureSortCore_sort_eq {fuel d : Nat} {u v : Level}
    (h : ensureSortCore μ env fuel d (.sort u) = .ok v) : v = u :=
  Expr.sort.inj (whnf_sort_eq (ConLeche.ensureSortCore_inv h))

/-! ## `propext` -/

/-- **`propext`'s pinned telescope, inverted through both erasures.**
Every domain and the innermost body is binder-free, so the pin fixes
the whole shape and leaves exactly the three binder names and the
three binder metas free — which is precisely the freedom the bit
lemma below removes. -/
theorem propext_shapeS {type' : Expr}
    (h : type'.erasePw
      = propextA.type.erasePw) :
    ∃ m₁ m₂ m₃,
      type' = .forallE (.sort .zero)
        (.forallE (.sort .zero)
          (.forallE
            (.app (.app (.const iffName []) (.bvar 1)) (.bvar 0))
            (.app (.app (.app (.const eqName [.succ .zero])
                (.sort .zero)) (.bvar 2)) (.bvar 1)) m₃) m₂) m₁ := by
  simp only [propextA, Expr.erasePw] at h
  obtain ⟨ty₁, b₁, m₁, rfl, hty₁, hb₁⟩ := erasePwNames_forallE_invS h
  obtain rfl := erasePwNames_sort_invS hty₁
  obtain ⟨ty₂, b₂, m₂, rfl, hty₂, hb₂⟩ := erasePwNames_forallE_invS hb₁
  obtain rfl := erasePwNames_sort_invS hty₂
  obtain ⟨ty₃, b₃, m₃, rfl, hty₃, hb₃⟩ := erasePwNames_forallE_invS hb₂
  obtain ⟨f, a, rfl, hf, ha⟩ := erasePwNames_app_invS hty₃
  obtain ⟨f', a', rfl, hf', ha'⟩ := erasePwNames_app_invS hf
  obtain rfl := erasePwNames_const_invS hf'
  obtain rfl := erasePwNames_bvar_invS ha'
  obtain rfl := erasePwNames_bvar_invS ha
  obtain ⟨g, c, rfl, hg, hc⟩ := erasePwNames_app_invS hb₃
  obtain ⟨g', c', rfl, hg', hc'⟩ := erasePwNames_app_invS hg
  obtain ⟨g'', c'', rfl, hg'', hc''⟩ := erasePwNames_app_invS hg'
  obtain rfl := erasePwNames_const_invS hg''
  obtain rfl := erasePwNames_sort_invS hc''
  obtain rfl := erasePwNames_bvar_invS hc'
  obtain rfl := erasePwNames_bvar_invS hc
  exact ⟨m₁, m₂, m₃, rfl⟩

/-- **The `Eq`-spine's inferred type, symbolically.**  `stdAxiomOk`
pins the stored `Eq` **on the nose**, so the spine's head carries the
pinned `∀ (α : Sort 1) (a b : α), Prop` outright and three `app`
inversions peel it to `Prop` — no erasure chase, and no assumption on
the three arguments. -/
theorem inferTypeCore_eqSpineS {fuel d : Nat} {X Y Z bt : Expr}
    (hEq : env.find? eqName = some eqA)
    (h : inferTypeCore μ env fuel d
      (.app (.app (.app (.const eqName [.succ .zero]) X) Y) Z)
      = .ok bt) : bt = .sort .zero := by
  obtain ⟨tf1, ty1, b1, m1, h1, hw1, rfl, -⟩ :=
    ConLeche.inferTypeCore_app_inv' h
  obtain ⟨tf2, ty2, b2, m2, h2, hw2, hb1, -⟩ :=
    ConLeche.inferTypeCore_app_inv' h1
  obtain ⟨tf3, ty3, b3, m3, h3, hw3, hb2, -⟩ :=
    ConLeche.inferTypeCore_app_inv' h2
  obtain ⟨ci, hci, -, hb3⟩ := ConLeche.inferTypeCore_const_inv h3
  rw [hEq] at hci
  obtain rfl := Option.some.inj hci
  subst hb3
  rw [show (Expr.instantiateLevelParams eqA.toConstantVal.levelParams
        [Level.zero.succ] eqA.toConstantVal.type)
      = .forallE (.sort (.succ .zero))
        (.forallE (.bvar 0)
          (.forallE (.bvar 1) (.sort .zero)
            ⟨.never⟩) ⟨.never⟩)
        ⟨.never⟩ from rfl] at hw3
  injection ConLeche.whnf_forallE_eq hw3 with e1 e2 e3
  subst e2
  subst hb2
  rw [show (Expr.forallE (.bvar 0)
        (.forallE (.bvar 1) (.sort .zero)
          ⟨.never⟩) ⟨.never⟩).instantiate1 X
      = .forallE X
        (.forallE X (.sort .zero)
          ⟨.never⟩) ⟨.never⟩ from rfl] at hw2
  injection ConLeche.whnf_forallE_eq hw2 with f1 f2 f3
  subst f2
  subst hb1
  rw [show (Expr.forallE X
        (.sort .zero) ⟨.never⟩).instantiate1 Y
      = .forallE (X.instantiate1 Y 0)
        (.sort .zero) ⟨.never⟩ from rfl] at hw1
  injection ConLeche.whnf_forallE_eq hw1 with g1 g2 g3
  subst g2
  rfl

/-- **THE NAMED FACT, at `propext`.**  Every binder of the stored
`propext` type carries bit `0`, at every assignment — the ENDGAME A
seal's item 1, discharged.  The innermost codomain is the `Eq`-spine
(`inferTypeCore_eqSpineS`: it infers to `Prop`), and the telescope
collapse carries that bit outward through the two remaining binders,
which is why this is one fact and not three. -/
theorem propext_bits (hμ : μ.verifiedChecks = true)
    (hEq : env.find? eqName = some eqA)
    {m₁ m₂ m₃ : BinderMeta}
    {F d : Nat} {stype : Expr}
    (hrun : inferTypeCore μ env F d
      (.forallE (.sort .zero)
        (.forallE (.sort .zero)
          (.forallE
            (.app (.app (.const iffName []) (.bvar 1)) (.bvar 0))
            (.app (.app (.app (.const eqName [.succ .zero])
                (.sort .zero)) (.bvar 2)) (.bvar 1)) m₃) m₂) m₁)
      = .ok stype) (φ : Name → Nat) :
    pwBit φ m₁.pw = 0 ∧ pwBit φ m₂.pw = 0 ∧ pwBit φ m₃.pw = 0 := by
  match F, hrun with
  | 0, hrun => rw [ConLeche.inferTypeCore_zero] at hrun; exact nomatch hrun
  | F1 + 1, hrun =>
  obtain ⟨tty1, u1, bt1, v1, -, -, hbt1, hens1, hpw1, rfl⟩ :=
    ConLeche.inferTypeCore_forall_inv hrun
  match F1, hbt1 with
  | 0, hbt1 => rw [ConLeche.inferTypeCore_zero] at hbt1; exact nomatch hbt1
  | F2 + 1, hbt1 =>
  obtain ⟨tty2, u2, bt2, v2, -, -, hbt2, hens2, hpw2, rfl⟩ :=
    ConLeche.inferTypeCore_forall_inv hbt1
  match F2, hbt2 with
  | 0, hbt2 => rw [ConLeche.inferTypeCore_zero] at hbt2; exact nomatch hbt2
  | F3 + 1, hbt2 =>
  obtain ⟨tty3, u3, bt3, v3, -, -, hbt3, hens3, hpw3, rfl⟩ :=
    ConLeche.inferTypeCore_forall_inv hbt2
  obtain rfl : bt3 = .sort .zero := inferTypeCore_eqSpineS hEq hbt3
  obtain rfl : v3 = .zero := ensureSortCore_sort_eq hens3
  have hb3 : pwBit φ m₃.pw = 0 := by
    rw [← hpw3 hμ]; exact (pwBit_zeronessOf φ _).mpr rfl
  obtain rfl : v2 = .imax u3 .zero := ensureSortCore_sort_eq hens2
  have hb2 : pwBit φ m₂.pw = 0 := by
    rw [← hpw2 hμ]; exact (pwBit_zeronessOf φ _).mpr (by simp [Level.eval])
  obtain rfl : v1 = .imax u2 (.imax u3 .zero) :=
    ensureSortCore_sort_eq hens1
  have hb1 : pwBit φ m₁.pw = 0 := by
    rw [← hpw1 hμ]; exact (pwBit_zeronessOf φ _).mpr (by simp [Level.eval])
  exact ⟨hb1, hb2, hb3⟩


/-! ## `Classical.choice`

The second standard axiom, and the *level-polymorphic* one: its bits
are not constantly zero but track the pin's own datum
(`PropWhen.ifAllZero [u]`), so the fact below is an equivalence rather
than an equation.  It is the same three moves — the innermost
codomain is the `α` binder's own variable, whose inferred type is its
stored annotation outright (`inferTypeCore_fvar_outS`), so move 2 is
one step rather than a spine peel. -/

/-- `inferTypeCore` returns an `fvar`'s stored annotation (a local
twin of `Annot/SortCoh/Discharge.lean`'s `inferTypeCore_fvar_out`,
transcribed here so this file's imports stay at the pin tier's). -/
theorem inferTypeCore_fvar_outS {f d : Nat} {i : Nat}
    {ty t : Expr}
    (h : inferTypeCore μ env f d (.fvar i ty) = .ok t) : t = ty := by
  cases f with
  | zero => exact nomatch h
  | succ f =>
    rw [ConLeche.inferTypeCore_succ] at h
    unfold ConLeche.inferBody at h
    simp only [
      pure, Except.pure] at h
    split at h
    · exact (Except.ok.inj h).symm
    · exact nomatch h

/-- **`Classical.choice`'s pinned telescope, inverted through both
erasures.**  Two binders; the domain `Nonempty α` and the body `α`
are binder-free, so only the two names and the two metas stay free.
The level argument is untouched by either erasure, so the stored
`Nonempty` reference is pinned to `[.param u]` on the nose. -/
theorem choice_shapeS {type' : Expr}
    (h : type'.erasePw = choiceA.type.erasePw) :
    ∃ m₁ m₂,
      type' = .forallE (.sort (.param uN))
        (.forallE
          (.app (.const nonemptyName [.param uN]) (.bvar 0))
          (.bvar 1) m₂) m₁ := by
  simp only [choiceA, Expr.erasePw] at h
  obtain ⟨ty₁, b₁, m₁, rfl, hty₁, hb₁⟩ := erasePwNames_forallE_invS h
  obtain rfl := erasePwNames_sort_invS hty₁
  obtain ⟨ty₂, b₂, m₂, rfl, hty₂, hb₂⟩ := erasePwNames_forallE_invS hb₁
  obtain ⟨f, a, rfl, hf, ha⟩ := erasePwNames_app_invS hty₂
  obtain rfl := erasePwNames_const_invS hf
  obtain rfl := erasePwNames_bvar_invS ha
  obtain rfl := erasePwNames_bvar_invS hb₂
  exact ⟨m₁, m₂, rfl⟩

/-- **THE NAMED FACT, at `Classical.choice`.**  Both binders of the
stored type carry the bit the pin's own datum computes — zero exactly
when the level parameter is.  The innermost codomain is the outer
binder's variable, whose sort is `Sort u`, and the telescope collapse
carries it to the outer binder. -/
theorem choice_bits (hμ : μ.verifiedChecks = true)
    {m₁ m₂ : BinderMeta} {F d : Nat} {stype : Expr}
    (hrun : inferTypeCore μ env F d
      (.forallE (.sort (.param uN))
        (.forallE
          (.app (.const nonemptyName [.param uN]) (.bvar 0))
          (.bvar 1) m₂) m₁) = .ok stype) (φ : Name → Nat) :
    (pwBit φ m₁.pw = 0 ↔ φ uN = 0) ∧ (pwBit φ m₂.pw = 0 ↔ φ uN = 0) := by
  match F, hrun with
  | 0, hrun => rw [ConLeche.inferTypeCore_zero] at hrun; exact nomatch hrun
  | F1 + 1, hrun =>
  obtain ⟨tty1, u1, bt1, v1, -, -, hbt1, hens1, hpw1, rfl⟩ :=
    ConLeche.inferTypeCore_forall_inv hrun
  match F1, hbt1 with
  | 0, hbt1 => rw [ConLeche.inferTypeCore_zero] at hbt1; exact nomatch hbt1
  | F2 + 1, hbt1 =>
  obtain ⟨tty2, u2, bt2, v2, -, -, hbt2, hens2, hpw2, rfl⟩ :=
    ConLeche.inferTypeCore_forall_inv hbt1
  -- the innermost codomain is the outer binder's own variable
  obtain rfl : bt2 = .sort (.param uN) := inferTypeCore_fvar_outS hbt2
  obtain rfl : v2 = .param uN := ensureSortCore_sort_eq hens2
  have hb2 : pwBit φ m₂.pw = 0 ↔ φ uN = 0 := by
    rw [← hpw2 hμ, pwBit_zeronessOf]; simp [Level.eval]
  obtain rfl : v1 = .imax u2 (.param uN) := ensureSortCore_sort_eq hens1
  have hb1 : pwBit φ m₁.pw = 0 ↔ φ uN = 0 := by
    rw [← hpw1 hμ, pwBit_zeronessOf]
    simp only [Level.eval]
    exact imax_eq_zero_iff _ _
  exact ⟨hb1, hb2⟩

end ConLeche.Model
