module

public import ConLeche.Model.NatEqs
import ConLeche.Semantics.LitStep
import ConLeche.Model.Annot.ValidSpine

public section

/-!
# The numeral transports at `interp` (task #161, literal tier)

`Sound/NatOps.lean`'s literal meta-inductions, re-proved at the
validated-annotation currency: the stored structural operations'
closed forms on `denoteMeta`'s own numeral spine, standing on the
`EnvModelM.nat_ops` recurrence law (the run-certificate product of
`NatEqsP.lean`) instead of the collapse-lane `EnvSHyp.nat_ops`.

The value environment plumbing is one degree simpler than v1's: every
head leaf is closed, so the two-slot extension collapses through
`acval_interp_closedC`, and the numeral spine is `denoteMeta`'s literal
clause verbatim (`natLit` below **is** `denoteMeta_natLit`'s output).

Worked example: `natOpV_add` (the lead-proved species).  The other
six structural operations follow the same recipe: read the two
recurrence clauses at values (`natEq_value` at computed `denoteMeta`
readings), close by the literal meta-induction
(`natOpV_bin_of_clauses` for the binary `(op x 0, op x (succ y))`
shape).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  ReducibilityHint natOpGuard natLitSupported)

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env} {φ : Name → Nat}

/-! ## The numeral spine, and its facts -/

/-- The numeral spine at an environment's `Nat` heads — exactly
`denoteMeta`'s `.lit (.natVal n)` clause. -/
@[expose] def natLit {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (n : Nat) : AnnotTerm :=
  natLitAV (m.acval ConLeche.natZeroName φ)
    (m.acval ConLeche.natSuccName φ) n

/-- The literal clause reads to the spine. -/
theorem denoteMeta_natLit_spine (m : EnvModel V env)
    (hs : natLitSupported env = true) (d n : Nat) :
    denoteMeta m.acval env φ d (.lit (.natVal n))
      = some (natLit m φ n) := by
  rw [denoteMeta_natLit hs, substFn_nil]
  rfl

/-- The successor unfolding is syntactic. -/
theorem natLit_succ (m : EnvModel V env) (n : Nat) :
    natLit m φ (n + 1)
      = .app (m.acval ConLeche.natSuccName φ) (natLit m φ n) := by rfl

/-- The zero numeral is the zero leaf (definitional). -/
theorem natLit_zero (m : EnvModel V env) :
    natLit m φ 0 = m.acval ConLeche.natZeroName φ := by rfl

/-- Numerals inhabit the stored `Nat` and are graded
(`natLit_factsAV` at the environment's heads). -/
theorem natLit_facts (m : EnvModel V env) (hnh : NatHeads m φ)
    (hval : AcvalValid m) (hs : natLitSupported env = true)
    (ρ : Nat → V) (n : Nat) :
    WellDenotedV V ρ (natLit m φ n) ∧
      interp V ρ (natLit m φ n)
        ∈ˢ interp V ρ (m.acval ConLeche.natName φ) := by
  obtain ⟨hz, hsucc⟩ := hnh hs ρ
  rw [substFn_nil] at hz hsucc
  have h := natLit_factsAV (V := V)
    (za := m.acval ConLeche.natZeroName φ)
    (sa := m.acval ConLeche.natSuccName φ)
    (natA := m.acval ConLeche.natName φ)
    (m.acval_wellDenoted _ _ ρ) (m.acval_wellDenoted _ _ ρ) hz hsucc n
  exact ⟨⟨h.1, AnnotValid_natLitAV (hval _ _ ρ) (hval _ _ ρ) n⟩, h.2⟩

/-- Numeral membership alone (the induction's staple). -/
theorem natLit_mem (m : EnvModel V env) (hnh : NatHeads m φ)
    (hval : AcvalValid m) (hs : natLitSupported env = true)
    (ρ : Nat → V) (n : Nat) :
    interp V ρ (natLit m φ n)
      ∈ˢ interp V ρ (m.acval ConLeche.natName φ) :=
  (natLit_facts m hnh hval hs ρ n).2

/-! ## Reading one recurrence at values -/

/-- One certified recurrence equation, read at value slots
(`natEq_value`'s mirror over `NatOps`). -/
theorem natEq_value (m : EnvModel V env) (hops : NatOps m φ)
    {c : Name} (hc : c ∈ ConLeche.natOpNames) {cv : ConstantVal}
    {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? c = some (.defnInfo cv v hint))
    {eq : Expr × Expr} (heq : eq ∈ ConLeche.natOpEquations 0 c)
    {L R : AnnotTerm}
    (hdL : denoteMeta m.acval env φ 2 eq.1 = some L)
    (hdR : denoteMeta m.acval env φ 2 eq.2 = some R)
    {ρ : Nat → V} {x y : V}
    (hx : x ∈ˢ interp V ρ (m.acval ConLeche.natName φ))
    (hy : y ∈ˢ interp V ρ (m.acval ConLeche.natName φ)) :
    interp V (cons y (cons x ρ)) L
      = interp V (cons y (cons x ρ)) R := by
  obtain ⟨L', R', hdL', hdR', hval⟩ :=
    (hops c hc cv v hint hf).2 eq heq
  obtain rfl : L' = L := Option.some.inj (hdL'.symm.trans hdL)
  obtain rfl : R' = R := Option.some.inj (hdR'.symm.trans hdR)
  exact hval ρ x y hx hy

/-! ## The binary meta-induction -/

/-- The common shape of the binary structural recurrences: a base
clause at `y = 0` and a successor clause, assembled by induction on
the second literal (`natOpV_bin_of_clauses`, transposed). -/
theorem natOpV_bin_of_clauses (m : EnvModel V env)
    {opv : V} {ρ : Nat → V} (res : Nat → Nat → Nat)
    (h0 : ∀ a : Nat,
      SetTheory.app (SetTheory.app opv
          (interp V ρ (natLit m φ a)))
        (interp V ρ (m.acval ConLeche.natZeroName φ))
      = interp V ρ (natLit m φ (res a 0)))
    (hSb : ∀ (a b : Nat),
      SetTheory.app (SetTheory.app opv
          (interp V ρ (natLit m φ a)))
          (interp V ρ (natLit m φ b))
        = interp V ρ (natLit m φ (res a b)) →
      SetTheory.app (SetTheory.app opv
          (interp V ρ (natLit m φ a)))
        (SetTheory.app
          (interp V ρ (m.acval ConLeche.natSuccName φ))
          (interp V ρ (natLit m φ b)))
      = interp V ρ (natLit m φ (res a (b + 1)))) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app opv
          (interp V ρ (natLit m φ a)))
        (interp V ρ (natLit m φ b))
      = interp V ρ (natLit m φ (res a b)) := by
  intro a b
  induction b with
  | zero => exact h0 a
  | succ b ih =>
    rw [natLit_succ, interp_app]
    exact hSb a b ih

/-! ## `Nat.add`, the worked example -/

/-- `Nat.add` on literal values (`natOpV_add`'s mirror). -/
theorem natOpV_add (m : EnvModel V env) (hops : NatOps m φ)
    (hnh : NatHeads m φ) (hval : AcvalValid m)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? ConLeche.natAddName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval ConLeche.natAddName φ))
          (interp V ρ (natLit m φ a)))
        (interp V ρ (natLit m φ b))
      = interp V ρ (natLit m φ (a + b)) := by
  obtain ⟨hg, -⟩ := hops ConLeche.natAddName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := ConLeche.natOpGuard_inv hg
  obtain ⟨cvc, vc, hcnt, hfc, hlpc⟩ := hdeps ConLeche.natAddName
    (by decide)
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := ConLeche.natLitSupported_inv hs
  have hKc : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const ConLeche.natAddName [])
      = some (m.acval ConLeche.natAddName φ) :=
    fun d => denoteMeta_levelless_const hfc
      (show (ConstantInfo.defnInfo cvc vc hcnt).toConstantVal.levelParams
        = [] from hlpc)
  have hKz : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const ConLeche.natZeroName [])
      = some (m.acval ConLeche.natZeroName φ) :=
    fun d => denoteMeta_levelless_const hfZ
      (show (ConstantInfo.ctorInfo cv0 i0 j0).toConstantVal.levelParams
        = [] from hlpZ)
  have hKs : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const ConLeche.natSuccName [])
      = some (m.acval ConLeche.natSuccName φ) :=
    fun d => denoteMeta_levelless_const hfS
      (show (ConstantInfo.ctorInfo cv1 i1 j1).toConstantVal.levelParams
        = [] from hlpS)
  have hzm := natLit_mem m hnh hval hs ρ 0
  -- base clause, read at values
  have h0 : ∀ x : V,
      x ∈ˢ interp V ρ (m.acval ConLeche.natName φ) →
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval ConLeche.natAddName φ)) x)
        (interp V ρ (m.acval ConLeche.natZeroName φ))
      = x := by
    intro x hx
    have h := natEq_value m hops (by decide) hf
      (eq := (.app (.app (.const ConLeche.natAddName [])
          (.fvar 0
            (.const ConLeche.natName [])))
        (.const ConLeche.natZeroName []),
        .fvar 0 (.const ConLeche.natName [])))
      (by decide)
      (L := .app (.app (m.acval ConLeche.natAddName φ) (.bvar 1))
        (m.acval ConLeche.natZeroName φ))
      (R := .bvar 1)
      (by rw [denoteMeta_app, denoteMeta_app, hKc 2, denoteMeta_fvar, hKz 2]
          rfl)
      (by rw [denoteMeta_fvar])
      hx hzm
    simp only [interp_app, interp_bvar, cons_succ, cons_zero,
      acval_interp_closedC m ConLeche.natAddName φ _ ρ,
      acval_interp_closedC m ConLeche.natZeroName φ _ ρ] at h
    exact h
  -- successor clause, read at values
  have hS : ∀ x y : V,
      x ∈ˢ interp V ρ (m.acval ConLeche.natName φ) →
      y ∈ˢ interp V ρ (m.acval ConLeche.natName φ) →
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval ConLeche.natAddName φ)) x)
        (SetTheory.app
          (interp V ρ (m.acval ConLeche.natSuccName φ)) y)
      = SetTheory.app
          (interp V ρ (m.acval ConLeche.natSuccName φ))
          (SetTheory.app (SetTheory.app
            (interp V ρ (m.acval ConLeche.natAddName φ)) x) y) := by
    intro x y hx hy
    have h := natEq_value m hops (by decide) hf
      (eq := (.app (.app (.const ConLeche.natAddName [])
          (.fvar 0
            (.const ConLeche.natName [])))
        (.app (.const ConLeche.natSuccName [])
          (.fvar 1
            (.const ConLeche.natName []))),
        .app (.const ConLeche.natSuccName [])
          (.app (.app (.const ConLeche.natAddName [])
            (.fvar 0
              (.const ConLeche.natName [])))
            (.fvar 1
              (.const ConLeche.natName [])))))
      (by decide)
      (L := .app (.app (m.acval ConLeche.natAddName φ) (.bvar 1))
        (.app (m.acval ConLeche.natSuccName φ) (.bvar 0)))
      (R := .app (m.acval ConLeche.natSuccName φ)
        (.app (.app (m.acval ConLeche.natAddName φ) (.bvar 1))
          (.bvar 0)))
      (by rw [denoteMeta_app, denoteMeta_app, hKc 2, denoteMeta_fvar,
            denoteMeta_app, hKs 2, denoteMeta_fvar]
          rfl)
      (by rw [denoteMeta_app, hKs 2, denoteMeta_app, denoteMeta_app, hKc 2,
            denoteMeta_fvar, denoteMeta_fvar]
          rfl)
      hx hy
    simp only [interp_app, interp_bvar, cons_succ, cons_zero,
      acval_interp_closedC m ConLeche.natAddName φ _ ρ,
      acval_interp_closedC m ConLeche.natSuccName φ _ ρ] at h
    exact h
  refine natOpV_bin_of_clauses m (fun a b => a + b) (fun a => ?_)
    (fun a b ih => ?_)
  · exact h0 (interp V ρ (natLit m φ a))
      (natLit_mem m hnh hval hs ρ a)
  · rw [hS (interp V ρ (natLit m φ a))
        (interp V ρ (natLit m φ b))
        (natLit_mem m hnh hval hs ρ a)
        (natLit_mem m hnh hval hs ρ b), ih]
    rw [Nat.add_succ, natLit_succ, interp_app]

/-! ## The remaining structural operations

Mechanical mirrors of `Sound/NatOps.lean`'s `natOpV_*`, at the
currencies the module docstring lists.  `sub` reads `pred`'s closed
form, `mul` reads `add`'s, `pow` reads `mul`'s — each dependency's
`find?` comes from `natOpGuard_inv`'s `hdeps`. -/

/-- `Nat.pred` on literal values (`natOpV_pred`'s mirror). -/
theorem natOpV_pred (m : EnvModel V env) (hops : NatOps m φ)
    (hnh : NatHeads m φ) (hval : AcvalValid m)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? ConLeche.natPredName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a : Nat,
      SetTheory.app (interp V ρ (m.acval ConLeche.natPredName φ))
        (interp V ρ (natLit m φ a))
      = interp V ρ (natLit m φ (a - 1)) := by
  obtain ⟨hg, -⟩ := hops ConLeche.natPredName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := ConLeche.natOpGuard_inv hg
  obtain ⟨cvp, vp, hp, hfp, hlpp⟩ := hdeps ConLeche.natPredName (by decide)
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := ConLeche.natLitSupported_inv hs
  have hKp : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const ConLeche.natPredName [])
      = some (m.acval ConLeche.natPredName φ) :=
    fun d => denoteMeta_levelless_const hfp
      (show (ConstantInfo.defnInfo cvp vp hp).toConstantVal.levelParams
        = [] from hlpp)
  have hKz : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const ConLeche.natZeroName [])
      = some (m.acval ConLeche.natZeroName φ) :=
    fun d => denoteMeta_levelless_const hfZ
      (show (ConstantInfo.ctorInfo cv0 i0 j0).toConstantVal.levelParams
        = [] from hlpZ)
  have hKs : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const ConLeche.natSuccName [])
      = some (m.acval ConLeche.natSuccName φ) :=
    fun d => denoteMeta_levelless_const hfS
      (show (ConstantInfo.ctorInfo cv1 i1 j1).toConstantVal.levelParams
        = [] from hlpS)
  have hzm := natLit_mem m hnh hval hs ρ 0
  -- base clause, read at values
  have h0 : SetTheory.app
      (interp V ρ (m.acval ConLeche.natPredName φ))
      (interp V ρ (m.acval ConLeche.natZeroName φ))
      = interp V ρ (m.acval ConLeche.natZeroName φ) := by
    have h := natEq_value m hops (by decide) hf
      (eq := (.app (.const ConLeche.natPredName [])
          (.const ConLeche.natZeroName []),
        .const ConLeche.natZeroName []))
      (by decide)
      (L := .app (m.acval ConLeche.natPredName φ)
        (m.acval ConLeche.natZeroName φ))
      (R := m.acval ConLeche.natZeroName φ)
      (by rw [denoteMeta_app, hKp 2, hKz 2]; rfl) (hKz 2) hzm hzm
    simp only [interp_app,
      acval_interp_closedC m ConLeche.natPredName φ _ ρ,
      acval_interp_closedC m ConLeche.natZeroName φ _ ρ] at h
    exact h
  -- successor clause, read at values
  have hS : ∀ x : V,
      x ∈ˢ interp V ρ (m.acval ConLeche.natName φ) →
      SetTheory.app (interp V ρ (m.acval ConLeche.natPredName φ))
        (SetTheory.app
          (interp V ρ (m.acval ConLeche.natSuccName φ)) x)
      = x := by
    intro x hx
    have h := natEq_value m hops (by decide) hf
      (eq := (.app (.const ConLeche.natPredName [])
          (.app (.const ConLeche.natSuccName [])
            (.fvar 0
              (.const ConLeche.natName []))),
        .fvar 0 (.const ConLeche.natName [])))
      (by decide)
      (L := .app (m.acval ConLeche.natPredName φ)
        (.app (m.acval ConLeche.natSuccName φ) (.bvar 1)))
      (R := .bvar 1)
      (by rw [denoteMeta_app, hKp 2, denoteMeta_app, hKs 2, denoteMeta_fvar]
          rfl)
      (by rw [denoteMeta_fvar])
      hx hzm
    simp only [interp_app, interp_bvar, cons_succ, cons_zero,
      acval_interp_closedC m ConLeche.natPredName φ _ ρ,
      acval_interp_closedC m ConLeche.natSuccName φ _ ρ] at h
    exact h
  intro a
  match a with
  | 0 => exact h0
  | a + 1 =>
    rw [natLit_succ, interp_app,
      hS _ (natLit_mem m hnh hval hs ρ a)]
    rfl

/-- `Nat.sub` on literal values (`natOpV_sub`'s mirror). -/
theorem natOpV_sub (m : EnvModel V env) (hops : NatOps m φ)
    (hnh : NatHeads m φ) (hval : AcvalValid m)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? ConLeche.natSubName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval ConLeche.natSubName φ))
          (interp V ρ (natLit m φ a)))
        (interp V ρ (natLit m φ b))
      = interp V ρ (natLit m φ (a - b)) := by
  obtain ⟨hg, -⟩ := hops ConLeche.natSubName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := ConLeche.natOpGuard_inv hg
  obtain ⟨cvc, vc, hcnt, hfc, hlpc⟩ := hdeps ConLeche.natSubName
    (by decide)
  obtain ⟨cvp, vp, hpnt, hfp, hlpp⟩ := hdeps ConLeche.natPredName
    (by decide)
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := ConLeche.natLitSupported_inv hs
  have hKc : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const ConLeche.natSubName [])
      = some (m.acval ConLeche.natSubName φ) :=
    fun d => denoteMeta_levelless_const hfc
      (show (ConstantInfo.defnInfo cvc vc hcnt).toConstantVal.levelParams
        = [] from hlpc)
  have hKp : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const ConLeche.natPredName [])
      = some (m.acval ConLeche.natPredName φ) :=
    fun d => denoteMeta_levelless_const hfp
      (show (ConstantInfo.defnInfo cvp vp hpnt).toConstantVal.levelParams
        = [] from hlpp)
  have hKz : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const ConLeche.natZeroName [])
      = some (m.acval ConLeche.natZeroName φ) :=
    fun d => denoteMeta_levelless_const hfZ
      (show (ConstantInfo.ctorInfo cv0 i0 j0).toConstantVal.levelParams
        = [] from hlpZ)
  have hKs : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const ConLeche.natSuccName [])
      = some (m.acval ConLeche.natSuccName φ) :=
    fun d => denoteMeta_levelless_const hfS
      (show (ConstantInfo.ctorInfo cv1 i1 j1).toConstantVal.levelParams
        = [] from hlpS)
  have hzm := natLit_mem m hnh hval hs ρ 0
  have h0 : ∀ x : V,
      x ∈ˢ interp V ρ (m.acval ConLeche.natName φ) →
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval ConLeche.natSubName φ)) x)
        (interp V ρ (m.acval ConLeche.natZeroName φ))
      = x := by
    intro x hx
    have h := natEq_value m hops (by decide) hf
      (eq := (.app (.app (.const ConLeche.natSubName [])
          (.fvar 0
            (.const ConLeche.natName [])))
        (.const ConLeche.natZeroName []),
        .fvar 0 (.const ConLeche.natName [])))
      (by decide)
      (L := .app (.app (m.acval ConLeche.natSubName φ) (.bvar 1))
        (m.acval ConLeche.natZeroName φ))
      (R := .bvar 1)
      (by rw [denoteMeta_app, denoteMeta_app, hKc 2, denoteMeta_fvar, hKz 2]
          rfl)
      (by rw [denoteMeta_fvar])
      hx hzm
    simp only [interp_app, interp_bvar, cons_succ, cons_zero,
      acval_interp_closedC m ConLeche.natSubName φ _ ρ,
      acval_interp_closedC m ConLeche.natZeroName φ _ ρ] at h
    exact h
  have hS : ∀ x y : V,
      x ∈ˢ interp V ρ (m.acval ConLeche.natName φ) →
      y ∈ˢ interp V ρ (m.acval ConLeche.natName φ) →
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval ConLeche.natSubName φ)) x)
        (SetTheory.app
          (interp V ρ (m.acval ConLeche.natSuccName φ)) y)
      = SetTheory.app
          (interp V ρ (m.acval ConLeche.natPredName φ))
          (SetTheory.app (SetTheory.app
            (interp V ρ (m.acval ConLeche.natSubName φ)) x) y) := by
    intro x y hx hy
    have h := natEq_value m hops (by decide) hf
      (eq := (.app (.app (.const ConLeche.natSubName [])
          (.fvar 0
            (.const ConLeche.natName [])))
        (.app (.const ConLeche.natSuccName [])
          (.fvar 1
            (.const ConLeche.natName []))),
        .app (.const ConLeche.natPredName [])
          (.app (.app (.const ConLeche.natSubName [])
            (.fvar 0
              (.const ConLeche.natName [])))
            (.fvar 1
              (.const ConLeche.natName [])))))
      (by decide)
      (L := .app (.app (m.acval ConLeche.natSubName φ) (.bvar 1))
        (.app (m.acval ConLeche.natSuccName φ) (.bvar 0)))
      (R := .app (m.acval ConLeche.natPredName φ)
        (.app (.app (m.acval ConLeche.natSubName φ) (.bvar 1))
          (.bvar 0)))
      (by rw [denoteMeta_app, denoteMeta_app, hKc 2, denoteMeta_fvar,
            denoteMeta_app, hKs 2, denoteMeta_fvar]
          rfl)
      (by rw [denoteMeta_app, hKp 2, denoteMeta_app, denoteMeta_app, hKc 2,
            denoteMeta_fvar, denoteMeta_fvar]
          rfl)
      hx hy
    simp only [interp_app, interp_bvar, cons_succ, cons_zero,
      acval_interp_closedC m ConLeche.natSubName φ _ ρ,
      acval_interp_closedC m ConLeche.natSuccName φ _ ρ,
      acval_interp_closedC m ConLeche.natPredName φ _ ρ] at h
    exact h
  refine natOpV_bin_of_clauses m (fun a b => a - b) (fun a => ?_)
    (fun a b ih => ?_)
  · exact h0 _ (natLit_mem m hnh hval hs ρ a)
  · rw [hS _ _ (natLit_mem m hnh hval hs ρ a)
        (natLit_mem m hnh hval hs ρ b), ih,
      natOpV_pred m hops hnh hval hfp ρ (a - b)]
    rfl

/-- `Nat.mul` on literal values (`natOpV_mul`'s mirror). -/
theorem natOpV_mul (m : EnvModel V env) (hops : NatOps m φ)
    (hnh : NatHeads m φ) (hval : AcvalValid m)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? ConLeche.natMulName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval ConLeche.natMulName φ))
          (interp V ρ (natLit m φ a)))
        (interp V ρ (natLit m φ b))
      = interp V ρ (natLit m φ (a * b)) := by
  obtain ⟨hg, -⟩ := hops ConLeche.natMulName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := ConLeche.natOpGuard_inv hg
  obtain ⟨cvc, vc, hcnt, hfc, hlpc⟩ := hdeps ConLeche.natMulName
    (by decide)
  obtain ⟨cva, va, hant, hfa, hlpa⟩ := hdeps ConLeche.natAddName
    (by decide)
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := ConLeche.natLitSupported_inv hs
  have hKc : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const ConLeche.natMulName [])
      = some (m.acval ConLeche.natMulName φ) :=
    fun d => denoteMeta_levelless_const hfc
      (show (ConstantInfo.defnInfo cvc vc hcnt).toConstantVal.levelParams
        = [] from hlpc)
  have hKa : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const ConLeche.natAddName [])
      = some (m.acval ConLeche.natAddName φ) :=
    fun d => denoteMeta_levelless_const hfa
      (show (ConstantInfo.defnInfo cva va hant).toConstantVal.levelParams
        = [] from hlpa)
  have hKz : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const ConLeche.natZeroName [])
      = some (m.acval ConLeche.natZeroName φ) :=
    fun d => denoteMeta_levelless_const hfZ
      (show (ConstantInfo.ctorInfo cv0 i0 j0).toConstantVal.levelParams
        = [] from hlpZ)
  have hKs : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const ConLeche.natSuccName [])
      = some (m.acval ConLeche.natSuccName φ) :=
    fun d => denoteMeta_levelless_const hfS
      (show (ConstantInfo.ctorInfo cv1 i1 j1).toConstantVal.levelParams
        = [] from hlpS)
  have hzm := natLit_mem m hnh hval hs ρ 0
  have h0 : ∀ x : V,
      x ∈ˢ interp V ρ (m.acval ConLeche.natName φ) →
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval ConLeche.natMulName φ)) x)
        (interp V ρ (m.acval ConLeche.natZeroName φ))
      = interp V ρ (m.acval ConLeche.natZeroName φ) := by
    intro x hx
    have h := natEq_value m hops (by decide) hf
      (eq := (.app (.app (.const ConLeche.natMulName [])
          (.fvar 0
            (.const ConLeche.natName [])))
        (.const ConLeche.natZeroName []),
        .const ConLeche.natZeroName []))
      (by decide)
      (L := .app (.app (m.acval ConLeche.natMulName φ) (.bvar 1))
        (m.acval ConLeche.natZeroName φ))
      (R := m.acval ConLeche.natZeroName φ)
      (by rw [denoteMeta_app, denoteMeta_app, hKc 2, denoteMeta_fvar, hKz 2]
          rfl)
      (hKz 2)
      hx hzm
    simp only [interp_app, interp_bvar, cons_succ, cons_zero,
      acval_interp_closedC m ConLeche.natMulName φ _ ρ,
      acval_interp_closedC m ConLeche.natZeroName φ _ ρ] at h
    exact h
  have hS : ∀ x y : V,
      x ∈ˢ interp V ρ (m.acval ConLeche.natName φ) →
      y ∈ˢ interp V ρ (m.acval ConLeche.natName φ) →
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval ConLeche.natMulName φ)) x)
        (SetTheory.app
          (interp V ρ (m.acval ConLeche.natSuccName φ)) y)
      = SetTheory.app (SetTheory.app
          (interp V ρ (m.acval ConLeche.natAddName φ))
          (SetTheory.app (SetTheory.app
            (interp V ρ (m.acval ConLeche.natMulName φ)) x) y)) x := by
    intro x y hx hy
    have h := natEq_value m hops (by decide) hf
      (eq := (.app (.app (.const ConLeche.natMulName [])
          (.fvar 0
            (.const ConLeche.natName [])))
        (.app (.const ConLeche.natSuccName [])
          (.fvar 1
            (.const ConLeche.natName []))),
        .app (.app (.const ConLeche.natAddName [])
          (.app (.app (.const ConLeche.natMulName [])
            (.fvar 0
              (.const ConLeche.natName [])))
            (.fvar 1
              (.const ConLeche.natName []))))
          (.fvar 0
            (.const ConLeche.natName []))))
      (by decide)
      (L := .app (.app (m.acval ConLeche.natMulName φ) (.bvar 1))
        (.app (m.acval ConLeche.natSuccName φ) (.bvar 0)))
      (R := .app (.app (m.acval ConLeche.natAddName φ)
        (.app (.app (m.acval ConLeche.natMulName φ) (.bvar 1))
          (.bvar 0))) (.bvar 1))
      (by rw [denoteMeta_app, denoteMeta_app, hKc 2, denoteMeta_fvar,
            denoteMeta_app, hKs 2, denoteMeta_fvar]
          rfl)
      (by simp only [denoteMeta_app, hKa 2, hKc 2, denoteMeta_fvar]; rfl)
      hx hy
    simp only [interp_app, interp_bvar, cons_succ, cons_zero,
      acval_interp_closedC m ConLeche.natMulName φ _ ρ,
      acval_interp_closedC m ConLeche.natSuccName φ _ ρ,
      acval_interp_closedC m ConLeche.natAddName φ _ ρ] at h
    exact h
  refine natOpV_bin_of_clauses m (fun a b => a * b) (fun a => ?_)
    (fun a b ih => ?_)
  · exact h0 _ (natLit_mem m hnh hval hs ρ a)
  · rw [hS _ _ (natLit_mem m hnh hval hs ρ a)
        (natLit_mem m hnh hval hs ρ b), ih,
      natOpV_add m hops hnh hval hfa ρ (a * b) a]
    rfl

/-- `Nat.pow` on literal values (`natOpV_pow`'s mirror). -/
theorem natOpV_pow (m : EnvModel V env) (hops : NatOps m φ)
    (hnh : NatHeads m φ) (hval : AcvalValid m)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? ConLeche.natPowName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval ConLeche.natPowName φ))
          (interp V ρ (natLit m φ a)))
        (interp V ρ (natLit m φ b))
      = interp V ρ (natLit m φ (a ^ b)) := by
  obtain ⟨hg, -⟩ := hops ConLeche.natPowName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := ConLeche.natOpGuard_inv hg
  obtain ⟨cvc, vc, hcnt, hfc, hlpc⟩ := hdeps ConLeche.natPowName
    (by decide)
  obtain ⟨cvm, vm, hmnt, hfm, hlpm⟩ := hdeps ConLeche.natMulName
    (by decide)
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := ConLeche.natLitSupported_inv hs
  have hKc : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const ConLeche.natPowName [])
      = some (m.acval ConLeche.natPowName φ) :=
    fun d => denoteMeta_levelless_const hfc
      (show (ConstantInfo.defnInfo cvc vc hcnt).toConstantVal.levelParams
        = [] from hlpc)
  have hKm : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const ConLeche.natMulName [])
      = some (m.acval ConLeche.natMulName φ) :=
    fun d => denoteMeta_levelless_const hfm
      (show (ConstantInfo.defnInfo cvm vm hmnt).toConstantVal.levelParams
        = [] from hlpm)
  have hKz : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const ConLeche.natZeroName [])
      = some (m.acval ConLeche.natZeroName φ) :=
    fun d => denoteMeta_levelless_const hfZ
      (show (ConstantInfo.ctorInfo cv0 i0 j0).toConstantVal.levelParams
        = [] from hlpZ)
  have hKs : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const ConLeche.natSuccName [])
      = some (m.acval ConLeche.natSuccName φ) :=
    fun d => denoteMeta_levelless_const hfS
      (show (ConstantInfo.ctorInfo cv1 i1 j1).toConstantVal.levelParams
        = [] from hlpS)
  have hzm := natLit_mem m hnh hval hs ρ 0
  have h0 : ∀ x : V,
      x ∈ˢ interp V ρ (m.acval ConLeche.natName φ) →
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval ConLeche.natPowName φ)) x)
        (interp V ρ (m.acval ConLeche.natZeroName φ))
      = SetTheory.app
          (interp V ρ (m.acval ConLeche.natSuccName φ))
          (interp V ρ (m.acval ConLeche.natZeroName φ)) := by
    intro x hx
    have h := natEq_value m hops (by decide) hf
      (eq := (.app (.app (.const ConLeche.natPowName [])
          (.fvar 0
            (.const ConLeche.natName [])))
        (.const ConLeche.natZeroName []),
        .app (.const ConLeche.natSuccName [])
          (.const ConLeche.natZeroName [])))
      (by decide)
      (L := .app (.app (m.acval ConLeche.natPowName φ) (.bvar 1))
        (m.acval ConLeche.natZeroName φ))
      (R := .app (m.acval ConLeche.natSuccName φ)
        (m.acval ConLeche.natZeroName φ))
      (by rw [denoteMeta_app, denoteMeta_app, hKc 2, denoteMeta_fvar, hKz 2]
          rfl)
      (by rw [denoteMeta_app, hKs 2, hKz 2]; rfl)
      hx hzm
    simp only [interp_app, interp_bvar, cons_succ, cons_zero,
      acval_interp_closedC m ConLeche.natPowName φ _ ρ,
      acval_interp_closedC m ConLeche.natZeroName φ _ ρ,
      acval_interp_closedC m ConLeche.natSuccName φ _ ρ] at h
    exact h
  have hS : ∀ x y : V,
      x ∈ˢ interp V ρ (m.acval ConLeche.natName φ) →
      y ∈ˢ interp V ρ (m.acval ConLeche.natName φ) →
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval ConLeche.natPowName φ)) x)
        (SetTheory.app
          (interp V ρ (m.acval ConLeche.natSuccName φ)) y)
      = SetTheory.app (SetTheory.app
          (interp V ρ (m.acval ConLeche.natMulName φ))
          (SetTheory.app (SetTheory.app
            (interp V ρ (m.acval ConLeche.natPowName φ)) x) y)) x := by
    intro x y hx hy
    have h := natEq_value m hops (by decide) hf
      (eq := (.app (.app (.const ConLeche.natPowName [])
          (.fvar 0
            (.const ConLeche.natName [])))
        (.app (.const ConLeche.natSuccName [])
          (.fvar 1
            (.const ConLeche.natName []))),
        .app (.app (.const ConLeche.natMulName [])
          (.app (.app (.const ConLeche.natPowName [])
            (.fvar 0
              (.const ConLeche.natName [])))
            (.fvar 1
              (.const ConLeche.natName []))))
          (.fvar 0
            (.const ConLeche.natName []))))
      (by decide)
      (L := .app (.app (m.acval ConLeche.natPowName φ) (.bvar 1))
        (.app (m.acval ConLeche.natSuccName φ) (.bvar 0)))
      (R := .app (.app (m.acval ConLeche.natMulName φ)
        (.app (.app (m.acval ConLeche.natPowName φ) (.bvar 1))
          (.bvar 0))) (.bvar 1))
      (by rw [denoteMeta_app, denoteMeta_app, hKc 2, denoteMeta_fvar,
            denoteMeta_app, hKs 2, denoteMeta_fvar]
          rfl)
      (by simp only [denoteMeta_app, hKm 2, hKc 2, denoteMeta_fvar]; rfl)
      hx hy
    simp only [interp_app, interp_bvar, cons_succ, cons_zero,
      acval_interp_closedC m ConLeche.natPowName φ _ ρ,
      acval_interp_closedC m ConLeche.natSuccName φ _ ρ,
      acval_interp_closedC m ConLeche.natMulName φ _ ρ] at h
    exact h
  refine natOpV_bin_of_clauses m (fun a b => a ^ b) (fun a => ?_)
    (fun a b ih => ?_)
  · exact h0 _ (natLit_mem m hnh hval hs ρ a)
  · rw [hS _ _ (natLit_mem m hnh hval hs ρ a)
        (natLit_mem m hnh hval hs ρ b), ih,
      natOpV_mul m hops hnh hval hfm ρ (a ^ b) a]
    rfl

/-- `Nat.beq` on literal values (`natOpV_beq`'s mirror). -/
theorem natOpV_beq (m : EnvModel V env) (hops : NatOps m φ)
    (hnh : NatHeads m φ) (hval : AcvalValid m)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? ConLeche.natBeqName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval ConLeche.natBeqName φ))
          (interp V ρ (natLit m φ a)))
        (interp V ρ (natLit m φ b))
      = interp V ρ (m.acval
          (if a = b then ConLeche.boolTrueName else ConLeche.boolFalseName)
          φ) := by
  obtain ⟨hg, -⟩ := hops ConLeche.natBeqName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, hbool⟩ := ConLeche.natOpGuard_inv hg
  obtain ⟨⟨ciT, hfT, hlpT⟩, ⟨ciF, hfF, hlpF⟩⟩ := hbool (Or.inl rfl)
  obtain ⟨cvc, vc, hcnt, hfc, hlpc⟩ := hdeps ConLeche.natBeqName
    (by decide)
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := ConLeche.natLitSupported_inv hs
  have hKc : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const ConLeche.natBeqName [])
      = some (m.acval ConLeche.natBeqName φ) :=
    fun d => denoteMeta_levelless_const hfc
      (show (ConstantInfo.defnInfo cvc vc hcnt).toConstantVal.levelParams
        = [] from hlpc)
  have hKz : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const ConLeche.natZeroName [])
      = some (m.acval ConLeche.natZeroName φ) :=
    fun d => denoteMeta_levelless_const hfZ
      (show (ConstantInfo.ctorInfo cv0 i0 j0).toConstantVal.levelParams
        = [] from hlpZ)
  have hKs : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const ConLeche.natSuccName [])
      = some (m.acval ConLeche.natSuccName φ) :=
    fun d => denoteMeta_levelless_const hfS
      (show (ConstantInfo.ctorInfo cv1 i1 j1).toConstantVal.levelParams
        = [] from hlpS)
  have hKT : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const ConLeche.boolTrueName [])
      = some (m.acval ConLeche.boolTrueName φ) :=
    fun d => denoteMeta_levelless_const hfT hlpT
  have hKF : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const ConLeche.boolFalseName [])
      = some (m.acval ConLeche.boolFalseName φ) :=
    fun d => denoteMeta_levelless_const hfF hlpF
  have hzm := natLit_mem m hnh hval hs ρ 0
  -- the four clauses at values
  have h00 : SetTheory.app (SetTheory.app
      (interp V ρ (m.acval ConLeche.natBeqName φ))
      (interp V ρ (m.acval ConLeche.natZeroName φ)))
      (interp V ρ (m.acval ConLeche.natZeroName φ))
      = interp V ρ (m.acval ConLeche.boolTrueName φ) := by
    have h := natEq_value m hops (by decide) hf
      (eq := (.app (.app (.const ConLeche.natBeqName [])
          (.const ConLeche.natZeroName []))
        (.const ConLeche.natZeroName []),
        .const ConLeche.boolTrueName []))
      (by decide)
      (L := .app (.app (m.acval ConLeche.natBeqName φ)
        (m.acval ConLeche.natZeroName φ))
        (m.acval ConLeche.natZeroName φ))
      (R := m.acval ConLeche.boolTrueName φ)
      (by rw [denoteMeta_app, denoteMeta_app, hKc 2, hKz 2]; rfl)
      (hKT 2) hzm hzm
    simp only [interp_app,
      acval_interp_closedC m ConLeche.natBeqName φ _ ρ,
      acval_interp_closedC m ConLeche.natZeroName φ _ ρ,
      acval_interp_closedC m ConLeche.boolTrueName φ _ ρ] at h
    exact h
  have h0S : ∀ y : V,
      y ∈ˢ interp V ρ (m.acval ConLeche.natName φ) →
      SetTheory.app (SetTheory.app
        (interp V ρ (m.acval ConLeche.natBeqName φ))
        (interp V ρ (m.acval ConLeche.natZeroName φ)))
        (SetTheory.app
          (interp V ρ (m.acval ConLeche.natSuccName φ)) y)
      = interp V ρ (m.acval ConLeche.boolFalseName φ) := by
    intro y hy
    have h := natEq_value m hops (by decide) hf
      (eq := (.app (.app (.const ConLeche.natBeqName [])
          (.const ConLeche.natZeroName []))
        (.app (.const ConLeche.natSuccName [])
          (.fvar 1 (.const ConLeche.natName []))),
        .const ConLeche.boolFalseName []))
      (by decide)
      (L := .app (.app (m.acval ConLeche.natBeqName φ)
        (m.acval ConLeche.natZeroName φ))
        (.app (m.acval ConLeche.natSuccName φ) (.bvar 0)))
      (R := m.acval ConLeche.boolFalseName φ)
      (by rw [denoteMeta_app, denoteMeta_app, hKc 2, hKz 2, denoteMeta_app,
            hKs 2, denoteMeta_fvar]
          rfl)
      (hKF 2) hzm hy
    simp only [interp_app, interp_bvar, cons_zero,
      acval_interp_closedC m ConLeche.natBeqName φ _ ρ,
      acval_interp_closedC m ConLeche.natZeroName φ _ ρ,
      acval_interp_closedC m ConLeche.natSuccName φ _ ρ,
      acval_interp_closedC m ConLeche.boolFalseName φ _ ρ] at h
    exact h
  have hS0 : ∀ x : V,
      x ∈ˢ interp V ρ (m.acval ConLeche.natName φ) →
      SetTheory.app (SetTheory.app
        (interp V ρ (m.acval ConLeche.natBeqName φ))
        (SetTheory.app
          (interp V ρ (m.acval ConLeche.natSuccName φ)) x))
        (interp V ρ (m.acval ConLeche.natZeroName φ))
      = interp V ρ (m.acval ConLeche.boolFalseName φ) := by
    intro x hx
    have h := natEq_value m hops (by decide) hf
      (eq := (.app (.app (.const ConLeche.natBeqName [])
          (.app (.const ConLeche.natSuccName [])
            (.fvar 0
              (.const ConLeche.natName []))))
        (.const ConLeche.natZeroName []),
        .const ConLeche.boolFalseName []))
      (by decide)
      (L := .app (.app (m.acval ConLeche.natBeqName φ)
        (.app (m.acval ConLeche.natSuccName φ) (.bvar 1)))
        (m.acval ConLeche.natZeroName φ))
      (R := m.acval ConLeche.boolFalseName φ)
      (by rw [denoteMeta_app, denoteMeta_app, hKc 2, denoteMeta_app, hKs 2,
            denoteMeta_fvar, hKz 2]
          rfl)
      (hKF 2) hx hzm
    simp only [interp_app, interp_bvar, cons_succ, cons_zero,
      acval_interp_closedC m ConLeche.natBeqName φ _ ρ,
      acval_interp_closedC m ConLeche.natZeroName φ _ ρ,
      acval_interp_closedC m ConLeche.natSuccName φ _ ρ,
      acval_interp_closedC m ConLeche.boolFalseName φ _ ρ] at h
    exact h
  have hSS : ∀ x y : V,
      x ∈ˢ interp V ρ (m.acval ConLeche.natName φ) →
      y ∈ˢ interp V ρ (m.acval ConLeche.natName φ) →
      SetTheory.app (SetTheory.app
        (interp V ρ (m.acval ConLeche.natBeqName φ))
        (SetTheory.app
          (interp V ρ (m.acval ConLeche.natSuccName φ)) x))
        (SetTheory.app
          (interp V ρ (m.acval ConLeche.natSuccName φ)) y)
      = SetTheory.app (SetTheory.app
          (interp V ρ (m.acval ConLeche.natBeqName φ)) x) y := by
    intro x y hx hy
    have h := natEq_value m hops (by decide) hf
      (eq := (.app (.app (.const ConLeche.natBeqName [])
          (.app (.const ConLeche.natSuccName [])
            (.fvar 0
              (.const ConLeche.natName []))))
        (.app (.const ConLeche.natSuccName [])
          (.fvar 1 (.const ConLeche.natName []))),
        .app (.app (.const ConLeche.natBeqName [])
          (.fvar 0 (.const ConLeche.natName [])))
          (.fvar 1 (.const ConLeche.natName []))))
      (by decide)
      (L := .app (.app (m.acval ConLeche.natBeqName φ)
        (.app (m.acval ConLeche.natSuccName φ) (.bvar 1)))
        (.app (m.acval ConLeche.natSuccName φ) (.bvar 0)))
      (R := .app (.app (m.acval ConLeche.natBeqName φ) (.bvar 1))
        (.bvar 0))
      (by rw [denoteMeta_app, denoteMeta_app, hKc 2, denoteMeta_app, hKs 2,
            denoteMeta_fvar, denoteMeta_app, hKs 2, denoteMeta_fvar]
          rfl)
      (by rw [denoteMeta_app, denoteMeta_app, hKc 2, denoteMeta_fvar,
            denoteMeta_fvar]
          rfl)
      hx hy
    simp only [interp_app, interp_bvar, cons_succ, cons_zero,
      acval_interp_closedC m ConLeche.natBeqName φ _ ρ,
      acval_interp_closedC m ConLeche.natSuccName φ _ ρ] at h
    exact h
  intro a
  induction a with
  | zero =>
    intro b
    match b with
    | 0 => rw [natLit_zero]; exact h00
    | b + 1 =>
      rw [natLit_zero, natLit_succ, interp_app,
        h0S _ (natLit_mem m hnh hval hs ρ b), if_neg (by omega)]
  | succ a ih =>
    intro b
    match b with
    | 0 =>
      rw [natLit_zero, natLit_succ, interp_app,
        hS0 _ (natLit_mem m hnh hval hs ρ a), if_neg (by omega)]
    | b + 1 =>
      rw [natLit_succ, natLit_succ, interp_app, interp_app,
        hSS _ _ (natLit_mem m hnh hval hs ρ a)
          (natLit_mem m hnh hval hs ρ b), ih b]
      by_cases hab : a = b
      · rw [if_pos hab, if_pos (by omega)]
      · rw [if_neg hab, if_neg (by omega)]

/-- `Nat.ble` on literal values (`natOpV_ble`'s mirror). -/
theorem natOpV_ble (m : EnvModel V env) (hops : NatOps m φ)
    (hnh : NatHeads m φ) (hval : AcvalValid m)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? ConLeche.natBleName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval ConLeche.natBleName φ))
          (interp V ρ (natLit m φ a)))
        (interp V ρ (natLit m φ b))
      = interp V ρ (m.acval
          (if a ≤ b then ConLeche.boolTrueName else ConLeche.boolFalseName)
          φ) := by
  obtain ⟨hg, -⟩ := hops ConLeche.natBleName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, hbool⟩ := ConLeche.natOpGuard_inv hg
  obtain ⟨⟨ciT, hfT, hlpT⟩, ⟨ciF, hfF, hlpF⟩⟩ :=
    hbool (Or.inr (Or.inl rfl))
  obtain ⟨cvc, vc, hcnt, hfc, hlpc⟩ := hdeps ConLeche.natBleName
    (by decide)
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := ConLeche.natLitSupported_inv hs
  have hKc : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const ConLeche.natBleName [])
      = some (m.acval ConLeche.natBleName φ) :=
    fun d => denoteMeta_levelless_const hfc
      (show (ConstantInfo.defnInfo cvc vc hcnt).toConstantVal.levelParams
        = [] from hlpc)
  have hKz : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const ConLeche.natZeroName [])
      = some (m.acval ConLeche.natZeroName φ) :=
    fun d => denoteMeta_levelless_const hfZ
      (show (ConstantInfo.ctorInfo cv0 i0 j0).toConstantVal.levelParams
        = [] from hlpZ)
  have hKs : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const ConLeche.natSuccName [])
      = some (m.acval ConLeche.natSuccName φ) :=
    fun d => denoteMeta_levelless_const hfS
      (show (ConstantInfo.ctorInfo cv1 i1 j1).toConstantVal.levelParams
        = [] from hlpS)
  have hKT : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const ConLeche.boolTrueName [])
      = some (m.acval ConLeche.boolTrueName φ) :=
    fun d => denoteMeta_levelless_const hfT hlpT
  have hKF : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const ConLeche.boolFalseName [])
      = some (m.acval ConLeche.boolFalseName φ) :=
    fun d => denoteMeta_levelless_const hfF hlpF
  have hzm := natLit_mem m hnh hval hs ρ 0
  have h0y : ∀ y : V,
      y ∈ˢ interp V ρ (m.acval ConLeche.natName φ) →
      SetTheory.app (SetTheory.app
        (interp V ρ (m.acval ConLeche.natBleName φ))
        (interp V ρ (m.acval ConLeche.natZeroName φ))) y
      = interp V ρ (m.acval ConLeche.boolTrueName φ) := by
    intro y hy
    have h := natEq_value m hops (by decide) hf
      (eq := (.app (.app (.const ConLeche.natBleName [])
          (.const ConLeche.natZeroName []))
        (.fvar 1 (.const ConLeche.natName [])),
        .const ConLeche.boolTrueName []))
      (by decide)
      (L := .app (.app (m.acval ConLeche.natBleName φ)
        (m.acval ConLeche.natZeroName φ)) (.bvar 0))
      (R := m.acval ConLeche.boolTrueName φ)
      (by rw [denoteMeta_app, denoteMeta_app, hKc 2, hKz 2, denoteMeta_fvar]
          rfl)
      (hKT 2) hzm hy
    simp only [interp_app, interp_bvar, cons_zero,
      acval_interp_closedC m ConLeche.natBleName φ _ ρ,
      acval_interp_closedC m ConLeche.natZeroName φ _ ρ,
      acval_interp_closedC m ConLeche.boolTrueName φ _ ρ] at h
    exact h
  have hS0 : ∀ x : V,
      x ∈ˢ interp V ρ (m.acval ConLeche.natName φ) →
      SetTheory.app (SetTheory.app
        (interp V ρ (m.acval ConLeche.natBleName φ))
        (SetTheory.app
          (interp V ρ (m.acval ConLeche.natSuccName φ)) x))
        (interp V ρ (m.acval ConLeche.natZeroName φ))
      = interp V ρ (m.acval ConLeche.boolFalseName φ) := by
    intro x hx
    have h := natEq_value m hops (by decide) hf
      (eq := (.app (.app (.const ConLeche.natBleName [])
          (.app (.const ConLeche.natSuccName [])
            (.fvar 0
              (.const ConLeche.natName []))))
        (.const ConLeche.natZeroName []),
        .const ConLeche.boolFalseName []))
      (by decide)
      (L := .app (.app (m.acval ConLeche.natBleName φ)
        (.app (m.acval ConLeche.natSuccName φ) (.bvar 1)))
        (m.acval ConLeche.natZeroName φ))
      (R := m.acval ConLeche.boolFalseName φ)
      (by rw [denoteMeta_app, denoteMeta_app, hKc 2, denoteMeta_app, hKs 2,
            denoteMeta_fvar, hKz 2]
          rfl)
      (hKF 2) hx hzm
    simp only [interp_app, interp_bvar, cons_succ, cons_zero,
      acval_interp_closedC m ConLeche.natBleName φ _ ρ,
      acval_interp_closedC m ConLeche.natZeroName φ _ ρ,
      acval_interp_closedC m ConLeche.natSuccName φ _ ρ,
      acval_interp_closedC m ConLeche.boolFalseName φ _ ρ] at h
    exact h
  have hSS : ∀ x y : V,
      x ∈ˢ interp V ρ (m.acval ConLeche.natName φ) →
      y ∈ˢ interp V ρ (m.acval ConLeche.natName φ) →
      SetTheory.app (SetTheory.app
        (interp V ρ (m.acval ConLeche.natBleName φ))
        (SetTheory.app
          (interp V ρ (m.acval ConLeche.natSuccName φ)) x))
        (SetTheory.app
          (interp V ρ (m.acval ConLeche.natSuccName φ)) y)
      = SetTheory.app (SetTheory.app
          (interp V ρ (m.acval ConLeche.natBleName φ)) x) y := by
    intro x y hx hy
    have h := natEq_value m hops (by decide) hf
      (eq := (.app (.app (.const ConLeche.natBleName [])
          (.app (.const ConLeche.natSuccName [])
            (.fvar 0
              (.const ConLeche.natName []))))
        (.app (.const ConLeche.natSuccName [])
          (.fvar 1 (.const ConLeche.natName []))),
        .app (.app (.const ConLeche.natBleName [])
          (.fvar 0 (.const ConLeche.natName [])))
          (.fvar 1 (.const ConLeche.natName []))))
      (by decide)
      (L := .app (.app (m.acval ConLeche.natBleName φ)
        (.app (m.acval ConLeche.natSuccName φ) (.bvar 1)))
        (.app (m.acval ConLeche.natSuccName φ) (.bvar 0)))
      (R := .app (.app (m.acval ConLeche.natBleName φ) (.bvar 1))
        (.bvar 0))
      (by rw [denoteMeta_app, denoteMeta_app, hKc 2, denoteMeta_app, hKs 2,
            denoteMeta_fvar, denoteMeta_app, hKs 2, denoteMeta_fvar]
          rfl)
      (by rw [denoteMeta_app, denoteMeta_app, hKc 2, denoteMeta_fvar,
            denoteMeta_fvar]
          rfl)
      hx hy
    simp only [interp_app, interp_bvar, cons_succ, cons_zero,
      acval_interp_closedC m ConLeche.natBleName φ _ ρ,
      acval_interp_closedC m ConLeche.natSuccName φ _ ρ] at h
    exact h
  intro a
  induction a with
  | zero =>
    intro b
    rw [natLit_zero, h0y _ (natLit_mem m hnh hval hs ρ b),
      if_pos (Nat.zero_le b)]
  | succ a ih =>
    intro b
    match b with
    | 0 =>
      rw [natLit_zero, natLit_succ, interp_app,
        hS0 _ (natLit_mem m hnh hval hs ρ a), if_neg (by omega)]
    | b + 1 =>
      rw [natLit_succ, natLit_succ, interp_app, interp_app,
        hSS _ _ (natLit_mem m hnh hval hs ρ a)
          (natLit_mem m hnh hval hs ρ b), ih b]
      by_cases hab : a ≤ b
      · rw [if_pos hab, if_pos (by omega)]
      · rw [if_neg hab, if_neg (by omega)]

end ConLeche.Model
