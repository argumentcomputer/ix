module

public import ConLeche.Verify.Shift

public section

/-!
# Substituting a free variable by a term

`substFvarAt p a e` replaces every reachable `fvar p` leaf by `a` and
lowers higher `fvar` indices by one — the syntactic side of
substitution, under the denotation's own substitution lemmas
(`ConLeche/Verify/Denote/Inst.lean`).  The key equation is the *beta
bridge*: opening a binder with a fresh variable and then substituting
that variable equals opening with the term directly.
-/

namespace ConLeche.Expr

/-- Instantiation is a no-op on terms without matching loose bvars. -/
theorem instantiate1_eq_self {v : Expr} :
    ∀ {e : Expr} {k : Nat}, looseBVarsBounded k e = true → e.instantiate1 v k = e := by
  intro e
  induction e with
  | bvar i =>
    intro k hb
    simp only [looseBVarsBounded, decide_eq_true_eq] at hb
    have h1 : ¬ i = k := by omega
    have h2 : ¬ i > k := by omega
    simp [instantiate1, h1, h2]
  | _ =>
    intro k hb
    simp_all [looseBVarsBounded, instantiate1]

/-- Two closed instantiations commute (the outer index below the
inner). -/
theorem instantiate1_instantiate1 {a b : Expr}
    (hba : a.looseBVarsBounded 0 = true)
    (hbb : b.looseBVarsBounded 0 = true) :
    ∀ (e : Expr) (j k : Nat), j ≤ k →
      (e.instantiate1 a (k + 1)).instantiate1 b j =
        (e.instantiate1 b j).instantiate1 a k := by
  intro e
  induction e with
  | bvar i =>
    intro j k hjk
    repeat' first
      | (exact instantiate1_eq_self
          (looseBVarsBounded_mono (Nat.zero_le _) hba))
      | (exact instantiate1_eq_self
          (looseBVarsBounded_mono (Nat.zero_le _) hbb))
      | (exact (instantiate1_eq_self
          (looseBVarsBounded_mono (Nat.zero_le _) hba)).symm)
      | (exact (instantiate1_eq_self
          (looseBVarsBounded_mono (Nat.zero_le _) hbb)).symm)
      | rfl
      | (exact congrArg Expr.bvar (by omega))
      | (exact absurd rfl (by omega))
      | omega
      | simp only [instantiate1]
      | split
  | fvar idx ty => intro j k hjk; simp [instantiate1]
  | sort u => intro j k hjk; simp [instantiate1]
  | const n us => intro j k hjk; simp [instantiate1]
  | app f g ihf ihg => intro j k hjk; simp [instantiate1, ihf _ _ hjk, ihg _ _ hjk]
  | lam ty body m ihty ihbody =>
    intro j k hjk
    simp [instantiate1, ihty _ _ hjk, ihbody _ _ (by omega : j + 1 ≤ k + 1)]
  | forallE ty body m ihty ihbody =>
    intro j k hjk
    simp [instantiate1, ihty _ _ hjk, ihbody _ _ (by omega : j + 1 ≤ k + 1)]
  | letE ty v body ihty ihv ihbody =>
    intro j k hjk
    simp [instantiate1, ihty _ _ hjk, ihv _ _ hjk,
      ihbody _ _ (by omega : j + 1 ≤ k + 1)]
  | lit l => intro j k hjk; simp [instantiate1]
  | proj s i e ih => intro j k hjk; simp [instantiate1, ih _ _ hjk]

/-- A stripped telescope's body stays loose-bvar-bounded by the strip
depth. -/
theorem stripPis_body_bounded :
    ∀ (k : Nat) {e : Expr} {bs : List (Expr × BinderMeta)}
      {body : Expr} {j : Nat},
      e.stripPis k = some (bs, body) → e.looseBVarsBounded j = true →
      body.looseBVarsBounded (j + k) = true := by
  intro k
  induction k with
  | zero =>
    intro e bs body j h hb
    simp only [stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact hb
  | succ k ih =>
    intro e bs body j h hb
    match e, h with
    | .forallE ty b m, h =>
      simp only [stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', body'⟩, hbstrip, heq⟩ := h
      obtain ⟨-, rfl⟩ : (ty, m) :: bs' = bs ∧ body' = body := by
        simpa using heq
      simp only [looseBVarsBounded, Bool.and_eq_true] at hb
      have := ih hbstrip hb.2
      rw [show j + 1 + k = j + (k + 1) from by omega] at this
      exact this

/-- Instantiation preserves a `∀`-telescope's arity. -/
theorem stripPis_instantiate1_isSome {v : Expr} :
    ∀ (k : Nat) {e : Expr} (j : Nat), (e.stripPis k).isSome →
      ((e.instantiate1 v j).stripPis k).isSome := by
  intro k
  induction k with
  | zero => intro e j _; simp [stripPis]
  | succ k ih =>
    intro e j h
    match e, h with
    | .forallE ty body m, h =>
      simp only [instantiate1, stripPis, Option.isSome_map] at h ⊢
      exact ih (j + 1) h

/-- Structural equality up to `fvar` names and annotations and binder
names — exactly what the interpretation never reads. -/
@[expose] def ErasedEq : Expr → Expr → Prop
  | .bvar i, .bvar j => i = j
  | .fvar i _, .fvar j _ => i = j
  | .sort u, .sort v => u = v
  | .const n us, .const n' us' => n = n' ∧ us = us'
  | .app f a, .app g b => ErasedEq f g ∧ ErasedEq a b
  | .lam ty b m, .lam ty' b' m' =>
    m = m' ∧ ErasedEq ty ty' ∧ ErasedEq b b'
  | .forallE ty b m, .forallE ty' b' m' =>
    m = m' ∧ ErasedEq ty ty' ∧ ErasedEq b b'
  | .letE ty v b, .letE ty' v' b' =>
    ErasedEq ty ty' ∧ ErasedEq v v' ∧ ErasedEq b b'
  | .lit l, .lit l' => l = l'
  | .proj s i e, .proj s' i' e' => s = s' ∧ i = i' ∧ ErasedEq e e'
  | _, _ => False

theorem ErasedEq.rfl : ∀ (e : Expr), ErasedEq e e := by
  intro e
  induction e <;> simp_all [ErasedEq]

/-- Equal terms are `ErasedEq` (the shape the `==` comparisons of the
kernel hand their consumers, `eq_of_beq` first). -/
theorem ErasedEq.of_eq {a b : Expr} (h : a = b) : ErasedEq a b :=
  h ▸ ErasedEq.rfl a

theorem ErasedEq.instantiate1 :
    ∀ {e e' v v' : Expr} {k : Nat}, ErasedEq e e' → ErasedEq v v' →
      ErasedEq (e.instantiate1 v k) (e'.instantiate1 v' k) := by
  intro e
  induction e with
  | bvar i =>
    intro e' v v' k he hv
    match e', he with
    | .bvar j, he =>
      obtain rfl : i = j := he
      simp only [Expr.instantiate1]
      split
      · exact hv
      · split <;> simp [ErasedEq]
  | fvar idx ty =>
    intro e' v v' k he hv
    match e', he with
    | .fvar j ty', he => simpa [Expr.instantiate1, ErasedEq] using he
  | sort u =>
    intro e' v v' k he hv
    match e', he with
    | .sort u', he => simpa [Expr.instantiate1, ErasedEq] using he
  | const n us =>
    intro e' v v' k he hv
    match e', he with
    | .const n' us', he => simpa [Expr.instantiate1, ErasedEq] using he
  | app f a ihf iha =>
    intro e' v v' k he hv
    match e', he with
    | .app g b, he =>
      exact ⟨ihf he.1 hv, iha he.2 hv⟩
  | lam ty body m ihty ihbody =>
    intro e' v v' k he hv
    match e', he with
    | .lam ty' body' m', he =>
      exact ⟨he.1, ihty he.2.1 hv, ihbody he.2.2 hv⟩
  | forallE ty body m ihty ihbody =>
    intro e' v v' k he hv
    match e', he with
    | .forallE ty' body' m', he =>
      exact ⟨he.1, ihty he.2.1 hv, ihbody he.2.2 hv⟩
  | letE ty vl body ihty ihv ihbody =>
    intro e' v v' k he hv
    match e', he with
    | .letE ty' vl' body', he =>
      exact ⟨ihty he.1 hv, ihv he.2.1 hv, ihbody he.2.2 hv⟩
  | lit l =>
    intro e' v v' k he hv
    match e', he with
    | .lit l', he => simpa [Expr.instantiate1, ErasedEq] using he
  | proj sn i pe ih =>
    intro e' v v' k he hv
    match e', he with
    | .proj sn' i' pe', he =>
      exact ⟨he.1, he.2.1, ih he.2.2 hv⟩

/-- The first `k` binder domains of a λ-tower and a `∀`-telescope agree
syntactically. -/
def LamPiDomsEq : Nat → Expr → Expr → Prop
  | 0, _, _ => True
  | k + 1, .lam d₁ b₁ _, .forallE d₂ b₂ _ => d₁ = d₂ ∧ LamPiDomsEq k b₁ b₂
  | _ + 1, _, _ => False

/-- Domain agreement survives instantiation (same argument on both
sides). -/
theorem LamPiDomsEq.instantiate1 {v : Expr} :
    ∀ (k : Nat) {e₁ e₂ : Expr} (j : Nat), LamPiDomsEq k e₁ e₂ →
      LamPiDomsEq k (e₁.instantiate1 v j) (e₂.instantiate1 v j) := by
  intro k
  induction k with
  | zero => intro e₁ e₂ j _; trivial
  | succ k ih =>
    intro e₁ e₂ j h
    match e₁, e₂, h with
    | .lam d₁ b₁ m₁, .forallE d₂ b₂ m₂, h =>
      exact ⟨by rw [h.1], ih (j + 1) h.2⟩

/-- Lifting a bvar-closed expression is the identity. -/
theorem liftLooseBVars_eq_self {k : Nat} :
    ∀ {e : Expr} {c : Nat}, e.looseBVarsBounded c = true →
      e.liftLooseBVars k c = e := by
  intro e
  induction e with
  | bvar i =>
    intro c hb
    simp only [looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [liftLooseBVars]
    rw [if_neg (by omega)]
  | _ =>
    intro c hb
    simp_all [looseBVarsBounded, liftLooseBVars]

/-- A zero lift is the identity. -/
theorem liftLooseBVars_zero : ∀ (e : Expr) (c : Nat),
    e.liftLooseBVars 0 c = e := by
  intro e
  induction e <;> intro c <;> simp_all [liftLooseBVars]

/-- Instantiating any freshly inserted slot of a lift eats one lift
level: the lifted expression never references the inserted range. -/
theorem instantiate1_liftLooseBVars {v : Expr} :
    ∀ {e : Expr} {k c j : Nat}, c ≤ j → j ≤ c + k →
      (e.liftLooseBVars (k + 1) c).instantiate1 v j =
        e.liftLooseBVars k c := by
  intro e
  induction e with
  | bvar i =>
    intro k c j hcj hjk
    simp only [liftLooseBVars]
    split
    · next h =>
      simp only [instantiate1]
      rw [if_neg (by omega), if_pos (by omega)]
      exact congrArg Expr.bvar (by omega)
    · next h =>
      simp only [instantiate1]
      rw [if_neg (by omega), if_neg (by omega)]
  | fvar idx ty => intro k c j hcj hjk; rfl
  | sort u => intro k c j hcj hjk; rfl
  | const n us => intro k c j hcj hjk; rfl
  | app f a ihf iha =>
    intro k c j hcj hjk
    simp only [liftLooseBVars, instantiate1, ihf hcj hjk, iha hcj hjk]
  | lam ty body m ihty ihbody =>
    intro k c j hcj hjk
    simp only [liftLooseBVars, instantiate1, ihty hcj hjk,
      ihbody (by omega : c + 1 ≤ j + 1) (by omega : j + 1 ≤ c + 1 + k)]
  | forallE ty body m ihty ihbody =>
    intro k c j hcj hjk
    simp only [liftLooseBVars, instantiate1, ihty hcj hjk,
      ihbody (by omega : c + 1 ≤ j + 1) (by omega : j + 1 ≤ c + 1 + k)]
  | letE ty vl body ihty ihv ihbody =>
    intro k c j hcj hjk
    simp only [liftLooseBVars, instantiate1, ihty hcj hjk, ihv hcj hjk,
      ihbody (by omega : c + 1 ≤ j + 1) (by omega : j + 1 ≤ c + 1 + k)]
  | lit l => intro k c j hcj hjk; rfl
  | proj sn i pe ih =>
    intro k c j hcj hjk
    simp only [liftLooseBVars, instantiate1, ih hcj hjk]

/-- Instantiation below the lift's cutoff commutes with the lift. -/
theorem liftLooseBVars_instantiate1 {v : Expr}
    (hbv : v.looseBVarsBounded 0 = true) :
    ∀ {e : Expr} {k c j : Nat}, j ≥ c →
      (e.liftLooseBVars k c).instantiate1 v (j + k) =
        (e.instantiate1 v j).liftLooseBVars k c := by
  intro e
  induction e with
  | bvar i =>
    intro k c j hjc
    simp only [liftLooseBVars]
    split
    · next h =>
      simp only [instantiate1]
      by_cases h1 : i = j
      · rw [if_pos (by omega : i + k = j + k), if_pos h1,
          liftLooseBVars_eq_self (looseBVarsBounded_mono (Nat.zero_le _) hbv)]
      · rw [if_neg (by omega : ¬ i + k = j + k), if_neg h1]
        by_cases h2 : i > j
        · rw [if_pos (by omega), if_pos h2]
          simp only [liftLooseBVars]
          rw [if_pos (by omega)]
          congr 1
          omega
        · rw [if_neg (by omega), if_neg h2]
          simp only [liftLooseBVars]
          rw [if_pos h]
    · next h =>
      simp only [instantiate1]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)]
      simp only [liftLooseBVars]
      rw [if_neg h]
  | fvar idx ty => intro k c j hjc; rfl
  | sort u => intro k c j hjc; rfl
  | const n us => intro k c j hjc; rfl
  | app f a ihf iha =>
    intro k c j hjc
    simp only [liftLooseBVars, instantiate1, ihf hjc, iha hjc]
  | lam ty body m ihty ihbody =>
    intro k c j hjc
    simp only [liftLooseBVars, instantiate1, ihty hjc]
    rw [show j + k + 1 = (j + 1) + k from by omega,
      ihbody (by omega : j + 1 ≥ c + 1)]
  | forallE ty body m ihty ihbody =>
    intro k c j hjc
    simp only [liftLooseBVars, instantiate1, ihty hjc]
    rw [show j + k + 1 = (j + 1) + k from by omega,
      ihbody (by omega : j + 1 ≥ c + 1)]
  | letE ty vl body ihty ihv ihbody =>
    intro k c j hjc
    simp only [liftLooseBVars, instantiate1, ihty hjc, ihv hjc]
    rw [show j + k + 1 = (j + 1) + k from by omega,
      ihbody (by omega : j + 1 ≥ c + 1)]
  | lit l => intro k c j hjc; rfl
  | proj sn i pe ih =>
    intro k c j hjc
    simp only [liftLooseBVars, instantiate1, ih hjc]

/-- Instantiation distributes over a `∀`-telescope's decomposition:
each domain is instantiated at its depth-shifted index, the body at
the telescope's arity. -/
theorem stripPis_instantiate1_eq {v : Expr} :
    ∀ (k : Nat) {e : Expr} {bs bs' : List (Expr × BinderMeta)}
      {body body' : Expr} (j : Nat),
      e.stripPis k = some (bs, body) →
      (e.instantiate1 v j).stripPis k = some (bs', body') →
      body' = body.instantiate1 v (j + k) ∧
      ∀ (i : Nat) (b b' : Expr × BinderMeta),
        bs[i]? = some b → bs'[i]? = some b' →
        b'.1 = b.1.instantiate1 v (j + i) := by
  intro k
  induction k with
  | zero =>
    intro e bs bs' body body' j h1 h2
    simp only [stripPis, Option.some.injEq, Prod.mk.injEq] at h1 h2
    obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨rfl, rfl⟩ := h2
    exact ⟨rfl, fun i b b' hb _ => by simp at hb⟩
  | succ k ih =>
    intro e bs bs' body body' j h1 h2
    match e, h1 with
    | .forallE d b m, h1 =>
      simp only [instantiate1, stripPis] at h1 h2
      cases hs1 : b.stripPis k with
      | none => rw [hs1] at h1; exact nomatch h1
      | some p1 =>
      cases hs2 : (b.instantiate1 v (j + 1)).stripPis k with
      | none => rw [hs2] at h2; exact nomatch h2
      | some p2 =>
      rw [hs1] at h1
      rw [hs2] at h2
      simp only [Option.map_some, Option.some.injEq] at h1 h2
      obtain ⟨hb1, hbody1⟩ : (d, m) :: p1.1 = bs ∧ p1.2 = body := by
        cases h1; exact ⟨rfl, rfl⟩
      obtain ⟨hb2, hbody2⟩ :
          (d.instantiate1 v j, m) :: p2.1 = bs' ∧ p2.2 = body' := by
        cases h2; exact ⟨rfl, rfl⟩
      subst hb1 hbody1 hb2 hbody2
      obtain ⟨hbody, hdoms⟩ := ih (j + 1) hs1 hs2
      refine ⟨by rw [hbody]; congr 1; omega, ?_⟩
      intro i bb bb' hbb hbb'
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hbb hbb'
        subst hbb hbb'
        simp
      | succ i =>
        simp only [List.getElem?_cons_succ] at hbb hbb'
        rw [hdoms i bb bb' hbb hbb']
        congr 1
        omega

/-- Instantiation distributes over an application spine. -/
theorem mkAppN_instantiate1 {v : Expr} :
    ∀ (args : List Expr) (h : Expr) (k : Nat),
      (Expr.mkAppN h args).instantiate1 v k =
        Expr.mkAppN (h.instantiate1 v k) (args.map (·.instantiate1 v k)) := by
  intro args
  induction args with
  | nil => intro h k; rfl
  | cons a args ih =>
    intro h k
    show (Expr.mkAppN (.app h a) args).instantiate1 v k = _
    rw [ih]
    rfl

/-- Erasure-equality is transitive. -/
theorem ErasedEq.symm : ∀ {e₁ e₂ : Expr}, ErasedEq e₁ e₂ → ErasedEq e₂ e₁
  | .bvar _, .bvar _, h => Eq.symm h
  | .fvar _ _, .fvar _ _, h => Eq.symm h
  | .sort _, .sort _, h => Eq.symm h
  | .const _ _, .const _ _, h => ⟨Eq.symm h.1, Eq.symm h.2⟩
  | .app _ _, .app _ _, h => ⟨ErasedEq.symm h.1, ErasedEq.symm h.2⟩
  | .lam _ _ _, .lam _ _ _, h =>
    ⟨Eq.symm h.1, ErasedEq.symm h.2.1, ErasedEq.symm h.2.2⟩
  | .forallE _ _ _, .forallE _ _ _, h =>
    ⟨Eq.symm h.1, ErasedEq.symm h.2.1, ErasedEq.symm h.2.2⟩
  | .letE _ _ _, .letE _ _ _, h =>
    ⟨ErasedEq.symm h.1, ErasedEq.symm h.2.1, ErasedEq.symm h.2.2⟩
  | .lit _, .lit _, h => Eq.symm h
  | .proj _ _ _, .proj _ _ _, h =>
    ⟨Eq.symm h.1, Eq.symm h.2.1, ErasedEq.symm h.2.2⟩

/-- Split a `∀`-telescope decomposition at a prefix length: the
residual of the prefix strips the remaining binders. -/
theorem ErasedEq.trans :
    ∀ {e₁ e₂ e₃ : Expr}, ErasedEq e₁ e₂ → ErasedEq e₂ e₃ → ErasedEq e₁ e₃ := by
  intro e₁
  induction e₁ with
  | bvar i =>
    intro e₂ e₃ h12 h23
    match e₂, h12 with
    | .bvar j, h12 =>
      match e₃, h23 with
      | .bvar l, h23 =>
        have a : i = j := h12
        have b : j = l := h23
        show i = l
        omega
  | fvar idx ty =>
    intro e₂ e₃ h12 h23
    match e₂, h12 with
    | .fvar j ty₂, h12 =>
      match e₃, h23 with
      | .fvar l ty₃, h23 =>
        have a : idx = j := h12
        have b : j = l := h23
        show idx = l
        omega
  | sort u =>
    intro e₂ e₃ h12 h23
    match e₂, h12 with
    | .sort u₂, h12 =>
      match e₃, h23 with
      | .sort u₃, h23 =>
        have a : u = u₂ := h12
        have b : u₂ = u₃ := h23
        show u = u₃
        exact a.trans b
  | const n us =>
    intro e₂ e₃ h12 h23
    match e₂, h12 with
    | .const n₂ us₂, h12 =>
      match e₃, h23 with
      | .const n₃ us₃, h23 =>
        have a : n = n₂ ∧ us = us₂ := h12
        have b : n₂ = n₃ ∧ us₂ = us₃ := h23
        exact show n = n₃ ∧ us = us₃ from
          ⟨a.1.trans b.1, a.2.trans b.2⟩
  | app fe a ihf iha =>
    intro e₂ e₃ h12 h23
    match e₂, h12 with
    | .app g b, h12 =>
      match e₃, h23 with
      | .app h c, h23 =>
        have x : ErasedEq fe g ∧ ErasedEq a b := h12
        have y : ErasedEq g h ∧ ErasedEq b c := h23
        exact show ErasedEq fe h ∧ ErasedEq a c from
          ⟨ihf x.1 y.1, iha x.2 y.2⟩
  | lam ty body m ihty ihbody =>
    intro e₂ e₃ h12 h23
    match e₂, h12 with
    | .lam ty₂ body₂ m₂, h12 =>
      match e₃, h23 with
      | .lam ty₃ body₃ m₃, h23 =>
        have x : m = m₂ ∧ ErasedEq ty ty₂ ∧ ErasedEq body body₂ := h12
        have y : m₂ = m₃ ∧ ErasedEq ty₂ ty₃ ∧ ErasedEq body₂ body₃ := h23
        exact show m = m₃ ∧ ErasedEq ty ty₃ ∧ ErasedEq body body₃ from
          ⟨x.1.trans y.1, ihty x.2.1 y.2.1, ihbody x.2.2 y.2.2⟩
  | forallE ty body m ihty ihbody =>
    intro e₂ e₃ h12 h23
    match e₂, h12 with
    | .forallE ty₂ body₂ m₂, h12 =>
      match e₃, h23 with
      | .forallE ty₃ body₃ m₃, h23 =>
        have x : m = m₂ ∧ ErasedEq ty ty₂ ∧ ErasedEq body body₂ := h12
        have y : m₂ = m₃ ∧ ErasedEq ty₂ ty₃ ∧ ErasedEq body₂ body₃ := h23
        exact show m = m₃ ∧ ErasedEq ty ty₃ ∧ ErasedEq body body₃ from
          ⟨x.1.trans y.1, ihty x.2.1 y.2.1, ihbody x.2.2 y.2.2⟩
  | letE ty vl body ihty ihv ihbody =>
    intro e₂ e₃ h12 h23
    match e₂, h12 with
    | .letE ty₂ vl₂ body₂, h12 =>
      match e₃, h23 with
      | .letE ty₃ vl₃ body₃, h23 =>
        have x : ErasedEq ty ty₂ ∧ ErasedEq vl vl₂ ∧ ErasedEq body body₂ :=
          h12
        have y : ErasedEq ty₂ ty₃ ∧ ErasedEq vl₂ vl₃ ∧
            ErasedEq body₂ body₃ := h23
        exact show ErasedEq ty ty₃ ∧ ErasedEq vl vl₃ ∧
            ErasedEq body body₃ from
          ⟨ihty x.1 y.1, ihv x.2.1 y.2.1, ihbody x.2.2 y.2.2⟩
  | lit l =>
    intro e₂ e₃ h12 h23
    match e₂, h12 with
    | .lit l₂, h12 =>
      match e₃, h23 with
      | .lit l₃, h23 =>
        have a : l = l₂ := h12
        have b : l₂ = l₃ := h23
        show l = l₃
        exact a.trans b
  | proj sn i pe ih =>
    intro e₂ e₃ h12 h23
    match e₂, h12 with
    | .proj sn₂ i₂ pe₂, h12 =>
      match e₃, h23 with
      | .proj sn₃ i₃ pe₃, h23 =>
        have x : sn = sn₂ ∧ i = i₂ ∧ ErasedEq pe pe₂ := h12
        have y : sn₂ = sn₃ ∧ i₂ = i₃ ∧ ErasedEq pe₂ pe₃ := h23
        exact show sn = sn₃ ∧ i = i₃ ∧ ErasedEq pe pe₃ from
          ⟨x.1.trans y.1, x.2.1.trans y.2.1, ih x.2.2 y.2.2⟩

/-- Invert `stripPis` across erasure: a strip of one side of an
`ErasedEq` pair comes from a strip of the other, with pointwise-erased
domains, equal binder metadata, and erased bodies. -/
theorem ErasedEq.stripPis_inv :
    ∀ (k : Nat) {e₁ e₂ : Expr} {bs₂ : List (Expr × BinderMeta)}
      {body₂ : Expr},
      ErasedEq e₁ e₂ → e₂.stripPis k = some (bs₂, body₂) →
      ∃ bs₁ body₁, e₁.stripPis k = some (bs₁, body₁) ∧
        bs₁.length = bs₂.length ∧
        (∀ (i : Nat) (b₁ b₂' : Expr × BinderMeta),
          bs₁[i]? = some b₁ → bs₂[i]? = some b₂' →
          ErasedEq b₁.1 b₂'.1 ∧ b₁.2 = b₂'.2) ∧
        ErasedEq body₁ body₂ := by
  intro k
  induction k with
  | zero =>
    intro e₁ e₂ bs₂ body₂ he h
    simp only [stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], e₁, by simp [stripPis], by simp,
      fun i b₁ b₂' hb₁ hb₂ => by simp at hb₁, he⟩
  | succ k ih =>
    intro e₁ e₂ bs₂ body₂ he h
    match e₂, h with
    | .forallE ty₂ b₂ m₂, h =>
      match e₁, he with
      | .forallE ty₁ b₁ m₁, he =>
        obtain ⟨rfl, hety, heb⟩ :
            m₁ = m₂ ∧ ErasedEq ty₁ ty₂ ∧ ErasedEq b₁ b₂ := he
        simp only [stripPis] at h
        cases hs : b₂.stripPis k with
        | none => rw [hs] at h; exact nomatch h
        | some pr =>
          rw [hs] at h
          obtain ⟨bs₀, body₀⟩ := pr
          simp only [Option.map_some, Option.some.injEq,
            Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨bs₁', body₁', hstrip, hlen, hdoms, hbody⟩ := ih heb hs
          refine ⟨(ty₁, m₁) :: bs₁', body₁', ?_, by simp [hlen],
            ?_, hbody⟩
          · simp only [stripPis, hstrip, Option.map_some]
          · intro i b₁' b₂'' hb₁ hb₂
            match i with
            | 0 =>
              obtain rfl : (ty₁, m₁) = b₁' := by simpa using hb₁
              obtain rfl : (ty₂, m₁) = b₂'' := by simpa using hb₂
              exact ⟨hety, Eq.refl _⟩
            | i + 1 =>
              exact hdoms i b₁' b₂'' (by simpa using hb₁)
                (by simpa using hb₂)

/-- Instantiate a sequence of arguments at descending indices (the
per-domain effect of peeling a telescope). -/
@[expose] def instSeq : List Expr → Nat → Expr → Expr
  | [], _, e => e
  | a :: as, t, e => instSeq as (t - 1) (e.instantiate1 a t)

/-- `instSeq` congruence under erasure (arguments erased to
themselves). -/
theorem instSeq_erasedEq :
    ∀ (args : List Expr) (t : Nat) {X Y : Expr}, ErasedEq X Y →
      ErasedEq (instSeq args t X) (instSeq args t Y) := by
  intro args
  induction args with
  | nil => intro t X Y h; exact h
  | cons a as ih =>
    intro t X Y h
    exact ih (t - 1) (ErasedEq.instantiate1 h (ErasedEq.rfl a))

/-- `instSeq` congruence under erasure across two argument spines
(pairwise erased-equal, e.g. the same-index free variables of two
frames). -/
theorem instSeq_erasedEq_args :
    ∀ (args₁ args₂ : List Expr) (t : Nat) {X Y : Expr},
      ErasedEq X Y →
      (∀ (k : Nat) (a₁ a₂ : Expr), args₁[k]? = some a₁ →
        args₂[k]? = some a₂ → ErasedEq a₁ a₂) →
      args₁.length = args₂.length →
      ErasedEq (instSeq args₁ t X) (instSeq args₂ t Y)
  | [], [], t, X, Y, hXY, _, _ => hXY
  | [], _ :: _, _, _, _, _, _, hlen => by simp at hlen
  | _ :: _, [], _, _, _, _, _, hlen => by simp at hlen
  | a₁ :: as₁, a₂ :: as₂, t, X, Y, hXY, hpt, hlen => by
    refine instSeq_erasedEq_args as₁ as₂ (t - 1)
      (ErasedEq.instantiate1 hXY (hpt 0 a₁ a₂ rfl rfl)) ?_
      (by simpa using hlen)
    intro k b₁ b₂ hb₁ hb₂
    exact hpt (k + 1) b₁ b₂ (by simpa using hb₁) (by simpa using hb₂)

/-- Instantiations strictly above a lift's inserted range drop past
it. -/
theorem instSeq_liftLooseBVars {kL c : Nat} :
    ∀ (args : List Expr) (t : Nat) {e : Expr},
      (∀ a ∈ args, a.looseBVarsBounded 0 = true) →
      t + 1 ≥ args.length + c + kL →
      instSeq args t (e.liftLooseBVars kL c) =
        (instSeq args (t - kL) e).liftLooseBVars kL c := by
  intro args
  induction args with
  | nil => intro t e _ _; rfl
  | cons a as ih =>
    intro t e hb ht
    simp only [List.length_cons] at ht
    obtain ⟨j, rfl⟩ : ∃ j, t = j + kL := ⟨t - kL, by omega⟩
    show instSeq as (j + kL - 1)
        ((e.liftLooseBVars kL c).instantiate1 a (j + kL)) =
      (instSeq as (j + kL - kL - 1)
        (e.instantiate1 a (j + kL - kL))).liftLooseBVars kL c
    rw [liftLooseBVars_instantiate1 (hb a List.mem_cons_self)
      (by omega : j ≥ c)]
    rw [show j + kL - kL = j from by omega]
    rw [ih (j + kL - 1) (fun x hx => hb x (List.mem_cons_of_mem _ hx))
      (by omega)]
    rw [show j + kL - 1 - kL = j - 1 from by omega]

/-- Instantiating every inserted slot of a lift, top down, restores the
original expression. -/
theorem instSeq_lift_eat {c : Nat} :
    ∀ (extras : List Expr) {e : Expr},
      instSeq extras (c + extras.length - 1)
        (e.liftLooseBVars extras.length c) = e := by
  intro extras
  induction extras with
  | nil => intro e; exact liftLooseBVars_zero e c
  | cons x xs ih =>
    intro e
    show instSeq xs (c + (xs.length + 1) - 1 - 1)
      ((e.liftLooseBVars (xs.length + 1) c).instantiate1 x
        (c + (xs.length + 1) - 1)) = e
    rw [instantiate1_liftLooseBVars (by omega) (by omega)]
    rw [show c + (xs.length + 1) - 1 - 1 = c + xs.length - 1 from by omega]
    exact ih

/-- A successful telescope decomposition has exactly `k` binders. -/
theorem stripPis_length :
    ∀ (k : Nat) {e : Expr} {bs : List (Expr × BinderMeta)}
      {body : Expr}, e.stripPis k = some (bs, body) → bs.length = k := by
  intro k
  induction k with
  | zero =>
    intro e bs body h
    simp only [stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | succ k ih =>
    intro e bs body h
    match e, h with
    | .forallE d b m, h =>
      simp only [stripPis] at h
      cases hs : b.stripPis k with
      | none => rw [hs] at h; exact nomatch h
      | some p =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨hb, -⟩ : (d, m) :: p.1 = bs ∧ p.2 = body := by
          cases h; exact ⟨rfl, rfl⟩
        subst hb
        have := ih (e := b) (bs := p.1) (body := p.2) (by rw [hs])
        simp [this]

/-- An instantiation sequence splits along list append. -/
theorem instSeq_append :
    ∀ (as bs : List Expr) (t : Nat) (X : Expr),
      instSeq (as ++ bs) t X = instSeq bs (t - as.length) (instSeq as t X) := by
  intro as
  induction as with
  | nil => intro bs t X; simp [instSeq]
  | cons a as ih =>
    intro bs t X
    show instSeq (as ++ bs) (t - 1) (X.instantiate1 a t) = _
    rw [ih bs (t - 1) (X.instantiate1 a t)]
    congr 1
    simp
    omega

/-- Pull an instantiation at the top index out of a closed-argument
sequence: the remaining substitutions shift its slot down by their
count. -/
theorem instSeq_instantiate1_out {b : Expr}
    (hbb : b.looseBVarsBounded 0 = true) :
    ∀ (args : List Expr) (t : Nat) (e : Expr),
      (∀ a ∈ args, a.looseBVarsBounded 0 = true) →
      args.length ≤ t →
      instSeq args (t - 1) (e.instantiate1 b t) =
        (instSeq args (t - 1) e).instantiate1 b (t - args.length) := by
  intro args
  induction args with
  | nil =>
    intro t e _ _
    simp [instSeq]
  | cons a as ih =>
    intro t e hcl hlen
    simp only [List.length_cons] at hlen
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    show instSeq as (t' + 1 - 1 - 1)
        ((e.instantiate1 b (t' + 1)).instantiate1 a (t' + 1 - 1)) = _
    rw [show t' + 1 - 1 = t' from rfl]
    rw [instantiate1_instantiate1 hbb (hcl a List.mem_cons_self) e t' t'
      (Nat.le_refl t')]
    have ih' := ih t' (e.instantiate1 a t')
      (fun x hx => hcl x (List.mem_cons_of_mem _ hx)) (by omega)
    rw [ih']
    show (instSeq as (t' - 1) (e.instantiate1 a t')).instantiate1 b
        (t' - as.length) =
      (instSeq as (t' - 1) (e.instantiate1 a t')).instantiate1 b
        (t' + 1 - (as.length + 1))
    congr 1
    omega

/-- Instantiating a middle segment of closed arguments through a lift
of its width collapses the lift: the parameters land above, the fields
below, and the middle slots eat the inserted range. -/
theorem instSeq_mid_collapse (A B C : List Expr) {X : Expr}
    (hA : ∀ a ∈ A, a.looseBVarsBounded 0 = true) :
    instSeq (A ++ B ++ C) (A.length + B.length + C.length - 1)
      (X.liftLooseBVars B.length C.length) =
    instSeq (A ++ C) (A.length + C.length - 1) X := by
  rw [instSeq_append (A ++ B) C, instSeq_append A B, instSeq_append A C]
  rw [instSeq_liftLooseBVars A _ hA (by simp; omega)]
  have h1 : A.length + B.length + C.length - 1 - B.length =
      A.length + C.length - 1 + B.length - B.length := by omega
  rw [h1, Nat.add_sub_cancel]
  have h2 : A.length + B.length + C.length - 1 - A.length =
      C.length + B.length - 1 := by omega
  rw [h2]
  rw [instSeq_lift_eat]
  congr 1
  simp only [List.length_append]
  omega

/-- A spine head is never an application. -/
theorem getAppFn_not_app : ∀ (e f a : Expr), e.getAppFn ≠ .app f a := by
  intro e
  induction e with
  | app g b ihg ihb => intro f a; exact ihg f a
  | _ => intro f a h; exact nomatch h

/-- An instantiation sequence is a no-op on bvar-closed expressions. -/
theorem instSeq_eq_self :
    ∀ (args : List Expr) (t : Nat) {e : Expr},
      e.looseBVarsBounded 0 = true → instSeq args t e = e := by
  intro args
  induction args with
  | nil => intro t e _; rfl
  | cons a as ih =>
    intro t e hb
    show instSeq as (t - 1) (e.instantiate1 a t) = e
    rw [instantiate1_eq_self (looseBVarsBounded_mono (Nat.zero_le t) hb)]
    exact ih (t - 1) hb

/-- Instantiating a full spine over a lifted prefix-context expression
only consumes the prefix: the lift skips the inner (index) slots, so
the trailing instantiations never touch the base.  This is how a
nested rule's stored pin (rule-prefix context, lifted past the index
binders into the major-domain context) evaluates at the recursor's
full argument spine to its evaluation at the leading arguments. -/
theorem instSeq_liftLooseBVars_prefix :
    ∀ (pre rest : List Expr) {q : Expr},
      (∀ a ∈ pre, a.looseBVarsBounded 0 = true) →
      q.looseBVarsBounded pre.length = true →
      instSeq (pre ++ rest) (pre.length + rest.length - 1)
        (q.liftLooseBVars rest.length 0) =
      instSeq pre (pre.length - 1) q := by
  intro pre
  induction pre with
  | nil =>
    intro rest q _ hq
    have hq0 : q.looseBVarsBounded 0 = true := by simpa using hq
    simp only [List.nil_append, List.length_nil, Nat.zero_add]
    show instSeq rest (rest.length - 1)
      (q.liftLooseBVars rest.length 0) = instSeq [] (0 - 1) q
    rw [liftLooseBVars_eq_self hq0, instSeq_eq_self _ _ hq0]
    rfl
  | cons a pre' ih =>
    intro rest q hpre hq
    have ha : a.looseBVarsBounded 0 = true := hpre a List.mem_cons_self
    have hq' : (q.instantiate1 a pre'.length).looseBVarsBounded
        pre'.length = true :=
      looseBVarsBounded_instantiate1_gen ha (by simpa using hq)
    show instSeq (pre' ++ rest) ((a :: pre').length + rest.length - 1 - 1)
        ((q.liftLooseBVars rest.length 0).instantiate1 a
          ((a :: pre').length + rest.length - 1)) =
      instSeq pre' ((a :: pre').length - 1 - 1)
        (q.instantiate1 a ((a :: pre').length - 1))
    rw [show (a :: pre').length + rest.length - 1 =
        pre'.length + rest.length from by simp,
      show (a :: pre').length - 1 = pre'.length from by simp,
      liftLooseBVars_instantiate1 ha (Nat.zero_le _)]
    exact ih rest (fun x hx => hpre x (List.mem_cons_of_mem _ hx)) hq'

/-- An instantiation sequence distributes over an application spine. -/
theorem instSeq_mkAppN :
    ∀ (args : List Expr) (t : Nat) (h : Expr) (xs : List Expr),
      instSeq args t (Expr.mkAppN h xs) =
        Expr.mkAppN (instSeq args t h) (xs.map (instSeq args t ·)) := by
  intro args
  induction args with
  | nil => intro t h xs; simp [instSeq]
  | cons a as ih =>
    intro t h xs
    show instSeq as (t - 1) ((Expr.mkAppN h xs).instantiate1 a t) = _
    rw [mkAppN_instantiate1, ih]
    congr 1
    simp only [List.map_map]
    rfl

/-- Resolving a bound variable through an instantiation sequence of
closed arguments: the variable becomes its slot's argument. -/
theorem instSeq_bvar :
    ∀ (args : List Expr) (t j : Nat),
      (∀ a ∈ args, a.looseBVarsBounded 0 = true) →
      j ≤ t → t - j < args.length →
      args[t - j]? = some (instSeq args t (.bvar j)) := by
  intro args
  induction args with
  | nil => intro t j _ _ h; simp at h
  | cons a as ih =>
    intro t j hb hj hr
    by_cases hjt : j = t
    · subst hjt
      show (a :: as)[j - j]? = some (instSeq as (j - 1)
        ((Expr.bvar j).instantiate1 a j))
      simp only [Expr.instantiate1, ↓reduceIte]
      rw [instSeq_eq_self as (j - 1) (hb a List.mem_cons_self)]
      simp [Nat.sub_self]
    · have hjlt : j < t := by omega
      show (a :: as)[t - j]? = some (instSeq as (t - 1)
        ((Expr.bvar j).instantiate1 a t))
      simp only [Expr.instantiate1]
      rw [if_neg hjt, if_neg (by omega)]
      rw [show t - j = (t - 1 - j) + 1 from by omega]
      rw [List.getElem?_cons_succ]
      exact ih (t - 1) j (fun x hx => hb x (List.mem_cons_of_mem _ hx))
        (by omega) (by simp at hr; omega)

/-! ### The capture-avoiding instantiation sequence

`Expr.instPisAtLift` (the opener behind `structProjTy`) substitutes
*open* arguments, so it lifts each inserted copy past the binders it
descends under.  What the model needs is that a subsequent **closed**
instantiation of the ambient variables collapses the whole thing onto
the plain `instSeq` at the already-substituted arguments — the
substitution lemma for `instantiate1Lift`. -/

/-- Instantiating a bvar-closed expression is the identity, also for
the capture-avoiding substitution. -/
theorem instantiate1Lift_eq_self {v : Expr} :
    ∀ {e : Expr} {k : Nat}, looseBVarsBounded k e = true →
      e.instantiate1Lift v k = e := by
  intro e
  induction e with
  | bvar i =>
    intro k hb
    simp only [looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [instantiate1Lift]
    rw [if_neg (by omega), if_neg (by omega)]
  | _ => intro k hb; simp_all [instantiate1Lift, looseBVarsBounded]

/-- At a bvar-closed argument the capture-avoiding substitution is the
plain one: there is nothing to lift. -/
theorem instantiate1Lift_eq_instantiate1 {v : Expr}
    (hbv : v.looseBVarsBounded 0 = true) :
    ∀ (e : Expr) (k : Nat), e.instantiate1Lift v k = e.instantiate1 v k := by
  intro e
  induction e with
  | bvar i =>
    intro k
    simp only [instantiate1Lift, instantiate1]
    by_cases h : i = k
    · rw [if_pos h, if_pos h,
        liftLooseBVars_eq_self (looseBVarsBounded_mono (Nat.zero_le _) hbv)]
    · rw [if_neg h, if_neg h]
  | _ => intro k; simp_all [instantiate1Lift, instantiate1]

/-- **The substitution lemma for `instantiate1Lift`.**  Instantiating
the ambient variable `k + u` by a *closed* term commutes with the
capture-avoiding substitution at `k`: the inserted copy's own ambient
variable is instantiated instead. -/
theorem instantiate1Lift_instantiate1 {a s : Expr}
    (hs : s.looseBVarsBounded 0 = true) :
    ∀ (e : Expr) (k u : Nat),
      (e.instantiate1Lift a k).instantiate1 s (k + u) =
        (e.instantiate1 s (k + 1 + u)).instantiate1Lift
          (a.instantiate1 s u) k := by
  intro e
  induction e with
  | bvar i =>
    intro k u
    by_cases hik : i = k
    · subst hik
      rw [show (Expr.bvar i).instantiate1Lift a i =
            Expr.liftLooseBVars i 0 a from by
          simp [instantiate1Lift],
        show (Expr.bvar i).instantiate1 s (i + 1 + u) = Expr.bvar i from by
          simp only [instantiate1]; rw [if_neg (by omega), if_neg (by omega)],
        show (Expr.bvar i).instantiate1Lift (a.instantiate1 s u) i =
            Expr.liftLooseBVars i 0 (a.instantiate1 s u) from by
          simp [instantiate1Lift],
        show i + u = u + i from by omega]
      exact liftLooseBVars_instantiate1 hs (Nat.zero_le u)
    · by_cases hgt : i > k
      · rw [show (Expr.bvar i).instantiate1Lift a k = Expr.bvar (i - 1) from by
            simp only [instantiate1Lift]; rw [if_neg hik, if_pos hgt]]
        by_cases h1 : i = k + 1 + u
        · rw [show (Expr.bvar (i - 1)).instantiate1 s (k + u) = s from by
              simp only [instantiate1]; rw [if_pos (by omega)],
            show (Expr.bvar i).instantiate1 s (k + 1 + u) = s from by
              simp only [instantiate1]; rw [if_pos h1]]
          exact (instantiate1Lift_eq_self
            (looseBVarsBounded_mono (Nat.zero_le k) hs)).symm
        · by_cases h2 : i > k + 1 + u
          · rw [show (Expr.bvar (i - 1)).instantiate1 s (k + u) =
                  Expr.bvar (i - 2) from by
                simp only [instantiate1]
                rw [if_neg (by omega), if_pos (by omega)]
                exact congrArg _ (by omega),
              show (Expr.bvar i).instantiate1 s (k + 1 + u) =
                  Expr.bvar (i - 1) from by
                simp only [instantiate1]; rw [if_neg h1, if_pos h2]]
            simp only [instantiate1Lift]
            rw [if_neg (by omega), if_pos (by omega)]
            exact (congrArg _ (by omega)).symm
          · rw [show (Expr.bvar (i - 1)).instantiate1 s (k + u) =
                  Expr.bvar (i - 1) from by
                simp only [instantiate1]
                rw [if_neg (by omega), if_neg (by omega)],
              show (Expr.bvar i).instantiate1 s (k + 1 + u) = Expr.bvar i from by
                simp only [instantiate1]; rw [if_neg h1, if_neg h2]]
            simp only [instantiate1Lift]
            rw [if_neg hik, if_pos hgt]
      · rw [show (Expr.bvar i).instantiate1Lift a k = Expr.bvar i from by
              simp only [instantiate1Lift]; rw [if_neg hik, if_neg hgt],
          show (Expr.bvar i).instantiate1 s (k + u) = Expr.bvar i from by
              simp only [instantiate1]
              rw [if_neg (by omega), if_neg (by omega)],
          show (Expr.bvar i).instantiate1 s (k + 1 + u) = Expr.bvar i from by
              simp only [instantiate1]
              rw [if_neg (by omega), if_neg (by omega)]]
        simp only [instantiate1Lift]
        rw [if_neg hik, if_neg hgt]
  | fvar idx ty => intro k u; rfl
  | sort v => intro k u; rfl
  | const n us => intro k u; rfl
  | lit l => intro k u; rfl
  | app f b ihf ihb =>
    intro k u
    simp only [instantiate1Lift, instantiate1, ihf, ihb]
  | proj sn i pe ih =>
    intro k u
    simp only [instantiate1Lift, instantiate1, ih]
  | lam ty body m ihty ihbody =>
    intro k u
    simp only [instantiate1Lift, instantiate1, ihty]
    rw [show k + u + 1 = (k + 1) + u from by omega,
      show k + 1 + u + 1 = (k + 1) + 1 + u from by omega, ihbody]
  | forallE ty body m ihty ihbody =>
    intro k u
    simp only [instantiate1Lift, instantiate1, ihty]
    rw [show k + u + 1 = (k + 1) + u from by omega,
      show k + 1 + u + 1 = (k + 1) + 1 + u from by omega, ihbody]
  | letE ty vl body ihty ihv ihbody =>
    intro k u
    simp only [instantiate1Lift, instantiate1, ihty, ihv]
    rw [show k + u + 1 = (k + 1) + u from by omega,
      show k + 1 + u + 1 = (k + 1) + 1 + u from by omega, ihbody]

/-- The substitution lemma folded over a closed argument spine: a
capture-avoiding substitution followed by the ambient spine is the
plain substitution at the already-instantiated argument. -/
theorem instSeq_instantiate1Lift :
    ∀ (sp : List Expr) (t : Nat),
      (∀ s ∈ sp, s.looseBVarsBounded 0 = true) → sp.length = t + 1 →
      ∀ {a : Expr}, a.looseBVarsBounded (t + 1) = true →
      ∀ (e : Expr) (k : Nat),
        instSeq sp (k + t) (e.instantiate1Lift a k) =
          (instSeq sp (k + t + 1) e).instantiate1 (instSeq sp t a) k := by
  intro sp
  induction sp with
  | nil => intro t _ hlen; exact absurd hlen (by simp)
  | cons s ss ih =>
    intro t hsp hlen a ha e k
    have hss : ss.length = t := by simpa using hlen
    have hs : s.looseBVarsBounded 0 = true := hsp s List.mem_cons_self
    have hsp' : ∀ x ∈ ss, x.looseBVarsBounded 0 = true :=
      fun x hx => hsp x (List.mem_cons_of_mem _ hx)
    show instSeq ss (k + t - 1)
      ((e.instantiate1Lift a k).instantiate1 s (k + t)) = _
    rw [instantiate1Lift_instantiate1 hs]
    cases t with
    | zero =>
      obtain rfl : ss = [] := List.eq_nil_of_length_eq_zero hss
      show (e.instantiate1 s (k + 1)).instantiate1Lift
        (a.instantiate1 s 0) k = _
      rw [instantiate1Lift_eq_instantiate1
        (looseBVarsBounded_instantiate1_gen hs ha)]
      rfl
    | succ t' =>
      have ha' : (a.instantiate1 s (t' + 1)).looseBVarsBounded (t' + 1) = true :=
        looseBVarsBounded_instantiate1_gen hs ha
      rw [show k + (t' + 1) - 1 = k + t' from by omega]
      rw [ih t' hsp' hss ha' (e.instantiate1 s (k + 1 + (t' + 1))) k]
      show _ = Expr.instantiate1 (instSeq ss (k + (t' + 1) + 1 - 1)
          (e.instantiate1 s (k + (t' + 1) + 1)))
        (instSeq ss (t' + 1 - 1) (a.instantiate1 s (t' + 1))) k
      rw [show k + (t' + 1) + 1 - 1 = k + t' + 1 from by omega,
        show k + (t' + 1) + 1 = k + 1 + (t' + 1) from by omega,
        show t' + 1 - 1 = t' from by omega]

/-- `instSeq` with the *capture-avoiding* substitution: the per-domain
effect of peeling a telescope at **open** arguments
(`Expr.instPisAtLift`, which is what a projection's generated type is
built with). -/
def instSeqLift : List Expr → Nat → Expr → Expr
  | [], _, e => e
  | a :: as, t, e => instSeqLift as (t - 1) (e.instantiate1Lift a t)

/-- **The collapse.**  A closed instantiation of the ambient variables
turns the capture-avoiding sequence into the plain one at the
already-instantiated arguments. -/
theorem instSeq_instSeqLift (sp : List Expr) (t : Nat)
    (hsp : ∀ s ∈ sp, s.looseBVarsBounded 0 = true) (hlen : sp.length = t + 1) :
    ∀ (args : List Expr), (∀ a ∈ args, a.looseBVarsBounded (t + 1) = true) →
      ∀ (e : Expr),
        instSeq sp t (instSeqLift args (args.length - 1) e) =
          instSeq (args.map (fun a => instSeq sp t a)) (args.length - 1)
            (instSeq sp (args.length + t) e) := by
  intro args
  induction args with
  | nil => intro _ e; simp [instSeqLift, instSeq]
  | cons a as ih =>
    intro hargs e
    show instSeq sp t (instSeqLift as (as.length + 1 - 1 - 1)
      (e.instantiate1Lift a (as.length + 1 - 1))) = _
    rw [show as.length + 1 - 1 - 1 = as.length - 1 from by omega,
      show as.length + 1 - 1 = as.length from by omega]
    rw [ih (fun x hx => hargs x (List.mem_cons_of_mem _ hx))
      (e.instantiate1Lift a as.length)]
    rw [instSeq_instantiate1Lift sp t hsp hlen
      (hargs a List.mem_cons_self) e as.length]
    show _ = instSeq ((fun x => instSeq sp t x) a ::
      as.map (fun x => instSeq sp t x)) (as.length + 1 - 1)
        (instSeq sp (as.length + 1 + t) e)
    rw [show as.length + 1 - 1 = as.length from by omega]
    show _ = instSeq (as.map (fun x => instSeq sp t x)) (as.length - 1)
      ((instSeq sp (as.length + 1 + t) e).instantiate1 (instSeq sp t a)
        as.length)
    rw [show as.length + 1 + t = as.length + t + 1 from by omega]

/-- Peel `instSeqLift` through a `∀`-binder (the shift index stays in
step with the remaining arguments), exactly as `instSeq_forallE`. -/
theorem instSeqLift_forallE :
    ∀ (args : List Expr) (t : Nat) (d b : Expr)
      (m : BinderMeta), args.length ≤ t + 1 →
      instSeqLift args t (.forallE d b m) =
        .forallE (instSeqLift args t d) (instSeqLift args (t + 1) b) m := by
  intro args
  induction args with
  | nil => intro t d b m _; rfl
  | cons a as ih =>
    intro t d b m hlen
    show instSeqLift as (t - 1)
      (.forallE (d.instantiate1Lift a t) (b.instantiate1Lift a (t + 1)) m)
      = _
    rw [ih (t - 1) (d.instantiate1Lift a t) (b.instantiate1Lift a (t + 1)) m
      (by simp only [List.length_cons] at hlen; omega)]
    show Expr.forallE (instSeqLift as (t - 1) (d.instantiate1Lift a t))
        (instSeqLift as (t - 1 + 1) (b.instantiate1Lift a (t + 1))) m =
      Expr.forallE (instSeqLift as (t - 1) (d.instantiate1Lift a t))
        (instSeqLift as (t + 1 - 1) (b.instantiate1Lift a (t + 1))) m
    cases as with
    | nil => rfl
    | cons a2 as2 =>
      have ht : t - 1 + 1 = t + 1 - 1 := by
        simp only [List.length_cons] at hlen
        omega
      rw [ht]

/-- `stripPis` commutes with the capture-avoiding substitution. -/
theorem stripPis_instantiate1Lift_full {v : Expr} :
    ∀ (k : Nat) {e : Expr} {bs : List (Expr × BinderMeta)}
      {body : Expr} (j : Nat),
      e.stripPis k = some (bs, body) →
      ∃ bs', (e.instantiate1Lift v j).stripPis k =
          some (bs', body.instantiate1Lift v (j + k)) ∧
        ∀ (i : Nat) (b : Expr × BinderMeta), bs[i]? = some b →
          bs'[i]? = some (b.1.instantiate1Lift v (j + i), b.2) := by
  intro k
  induction k with
  | zero =>
    intro e bs body j h
    simp only [stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp [stripPis], fun i b hb => by simp at hb⟩
  | succ k ih =>
    intro e bs body j h
    match e, h with
    | .forallE d bo m, h =>
      simp only [stripPis] at h
      cases hs : bo.stripPis k with
      | none => rw [hs] at h; exact nomatch h
      | some p =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨hb, hbody⟩ : (d, m) :: p.1 = bs ∧ p.2 = body := by
          cases h; exact ⟨rfl, rfl⟩
        subst hbody
        obtain ⟨bs', h1, h2⟩ := ih (j + 1) (by rw [hs])
        refine ⟨(d.instantiate1Lift v j, m) :: bs', ?_, ?_⟩
        · simp only [instantiate1Lift, stripPis, h1,
            show j + 1 + k = j + (k + 1) from by omega, Option.map_some]
        · intro i b hbi
          rw [← hb] at hbi
          cases i with
          | zero =>
            obtain rfl : (d, m) = b := by simpa using hbi
            rfl
          | succ i =>
            simp only [List.getElem?_cons_succ] at hbi ⊢
            rw [show j + (i + 1) = j + 1 + i from by omega]
            exact h2 i b hbi

/-- The head binder of a partial capture-avoiding `∀`-instantiation
walk, characterized by the raw telescope's binder list. -/
theorem instPisAtLift_head :
    ∀ (args : List Expr) {e : Expr} {rest : Expr} {mrem : Nat}
      {bs : List (Expr × BinderMeta)} {body : Expr}
      {b : Expr × BinderMeta},
      Expr.instPisAtLift args e = some rest →
      e.stripPis (args.length + (mrem + 1)) = some (bs, body) →
      bs[args.length]? = some b →
      ∃ bodyR, rest = .forallE
        (instSeqLift args (args.length - 1) b.1) bodyR b.2 := by
  intro args
  induction args with
  | nil =>
    intro e rest mrem bs body b h hstrip hb
    simp only [instPisAtLift, Option.some.injEq] at h
    subst h
    rw [show [].length + (mrem + 1) = mrem + 1 from by simp] at hstrip
    match e, hstrip with
    | .forallE d bo m, hstrip =>
      simp only [stripPis] at hstrip
      cases hs : bo.stripPis mrem with
      | none => rw [hs] at hstrip; exact nomatch hstrip
      | some p =>
        rw [hs] at hstrip
        simp only [Option.map_some, Option.some.injEq] at hstrip
        obtain ⟨hbs, -⟩ : (d, m) :: p.1 = bs ∧ p.2 = body := by
          cases hstrip; exact ⟨rfl, rfl⟩
        rw [← hbs] at hb
        obtain rfl : (d, m) = b := by simpa using hb
        exact ⟨bo, rfl⟩
  | cons a as ih =>
    intro e rest mrem bs body b h hstrip hb
    match e, h with
    | .forallE d bo m, h =>
      simp only [instPisAtLift] at h
      rw [show (a :: as).length + (mrem + 1) =
        (as.length + (mrem + 1)) + 1 from by simp; omega] at hstrip
      simp only [stripPis] at hstrip
      cases hs : bo.stripPis (as.length + (mrem + 1)) with
      | none => rw [hs] at hstrip; exact nomatch hstrip
      | some q =>
        rw [hs] at hstrip
        simp only [Option.map_some, Option.some.injEq] at hstrip
        obtain ⟨hbs, -⟩ : (d, m) :: q.1 = bs ∧ q.2 = body := by
          cases hstrip; exact ⟨rfl, rfl⟩
        rw [← hbs] at hb
        simp only [List.length_cons, List.getElem?_cons_succ] at hb
        obtain ⟨bs', hstrip', hpos⟩ :=
          stripPis_instantiate1Lift_full (v := a)
            (as.length + (mrem + 1)) 0 hs
        obtain ⟨bodyR, hhead⟩ := ih (b := (b.1.instantiate1Lift a as.length,
            b.2)) h hstrip'
          (by rw [hpos as.length b hb]; simp)
        exact ⟨bodyR, by rw [hhead]; rfl⟩

/-- A successful λ-tower decomposition has exactly `k` binders. -/
theorem stripLams_length :
    ∀ (k : Nat) {e : Expr} {bs : List (Expr × BinderMeta)}
      {body : Expr}, e.stripLams k = some (bs, body) → bs.length = k := by
  intro k
  induction k with
  | zero =>
    intro e bs body h
    simp only [stripLams, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | succ k ih =>
    intro e bs body h
    match e, h with
    | .lam d b m, h =>
      simp only [stripLams] at h
      cases hs : b.stripLams k with
      | none => rw [hs] at h; exact nomatch h
      | some p =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨hb, -⟩ : (d, m) :: p.1 = bs ∧ p.2 = body := by
          cases h; exact ⟨rfl, rfl⟩
        subst hb
        have := ih (e := b) (bs := p.1) (body := p.2) (by rw [hs])
        simp [this]

/-- Instantiation preserves a λ-tower's arity. -/
theorem stripLams_instantiate1_isSome {v : Expr} :
    ∀ (k : Nat) {e : Expr} (j : Nat), (e.stripLams k).isSome →
      ((e.instantiate1 v j).stripLams k).isSome := by
  intro k
  induction k with
  | zero => intro e j _; simp [stripLams]
  | succ k ih =>
    intro e j h
    match e, h with
    | .lam ty body m, h =>
      simp only [instantiate1, stripLams, Option.isSome_map] at h ⊢
      exact ih (j + 1) h

/-- Instantiation distributes over a λ-tower's decomposition. -/
theorem stripLams_instantiate1_eq {v : Expr} :
    ∀ (k : Nat) {e : Expr} {bs bs' : List (Expr × BinderMeta)}
      {body body' : Expr} (j : Nat),
      e.stripLams k = some (bs, body) →
      (e.instantiate1 v j).stripLams k = some (bs', body') →
      body' = body.instantiate1 v (j + k) ∧
      ∀ (i : Nat) (b b' : Expr × BinderMeta),
        bs[i]? = some b → bs'[i]? = some b' →
        b'.1 = b.1.instantiate1 v (j + i) := by
  intro k
  induction k with
  | zero =>
    intro e bs bs' body body' j h1 h2
    simp only [stripLams, Option.some.injEq, Prod.mk.injEq] at h1 h2
    obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨rfl, rfl⟩ := h2
    exact ⟨rfl, fun i b b' hb _ => by simp at hb⟩
  | succ k ih =>
    intro e bs bs' body body' j h1 h2
    match e, h1 with
    | .lam d b m, h1 =>
      simp only [instantiate1, stripLams] at h1 h2
      cases hs1 : b.stripLams k with
      | none => rw [hs1] at h1; exact nomatch h1
      | some p1 =>
      cases hs2 : (b.instantiate1 v (j + 1)).stripLams k with
      | none => rw [hs2] at h2; exact nomatch h2
      | some p2 =>
      rw [hs1] at h1
      rw [hs2] at h2
      simp only [Option.map_some, Option.some.injEq] at h1 h2
      obtain ⟨hb1, hbody1⟩ : (d, m) :: p1.1 = bs ∧ p1.2 = body := by
        cases h1; exact ⟨rfl, rfl⟩
      obtain ⟨hb2, hbody2⟩ :
          (d.instantiate1 v j, m) :: p2.1 = bs' ∧ p2.2 = body' := by
        cases h2; exact ⟨rfl, rfl⟩
      subst hb1 hbody1 hb2 hbody2
      obtain ⟨hbody, hdoms⟩ := ih (j + 1) hs1 hs2
      refine ⟨by rw [hbody]; congr 1; omega, ?_⟩
      intro i bb bb' hbb hbb'
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hbb hbb'
        subst hbb hbb'
        simp
      | succ i =>
        simp only [List.getElem?_cons_succ] at hbb hbb'
        rw [hdoms i bb bb' hbb hbb']
        congr 1
        omega

/-- Substituting a *free variable* cannot create λ-binders: a λ-tower
of the instantiated term certifies one of the term itself. -/
theorem stripLams_instantiate1_fvar_isSome_rev {i : Nat}
    {t : Expr} :
    ∀ (k : Nat) (e : Expr) (j : Nat),
      ((e.instantiate1 (.fvar i t) j).stripLams k).isSome = true →
      (e.stripLams k).isSome = true := by
  intro k
  induction k with
  | zero => intro e j _; rfl
  | succ k ih =>
    intro e j h
    match e with
    | .lam d b m =>
      simp only [instantiate1, stripLams, Option.isSome_map] at h ⊢
      exact ih b (j + 1) h
    | .bvar l =>
      simp only [instantiate1] at h
      split at h
      · simp [stripLams] at h
      · split at h <;> simp [stripLams] at h
    | .fvar _ _ => simp [instantiate1, stripLams] at h
    | .sort _ => simp [instantiate1, stripLams] at h
    | .const _ _ => simp [instantiate1, stripLams] at h
    | .app _ _ => simp [instantiate1, stripLams] at h
    | .forallE _ _ _ => simp [instantiate1, stripLams] at h
    | .letE _ _ _ => simp [instantiate1, stripLams] at h
    | .lit _ => simp [instantiate1, stripLams] at h
    | .proj _ _ _ => simp [instantiate1, stripLams] at h

/-- Peel `instSeq` through a `∀`-binder (the shift index stays in step
with the remaining arguments). -/
theorem instSeq_forallE :
    ∀ (args : List Expr) (t : Nat) (d b : Expr)
      (m : BinderMeta), args.length ≤ t + 1 →
      instSeq args t (.forallE d b m) =
        .forallE (instSeq args t d) (instSeq args (t + 1) b) m := by
  intro args
  induction args with
  | nil => intro t d b m _; rfl
  | cons a as ih =>
    intro t d b m hlen
    show instSeq as (t - 1)
      (.forallE (d.instantiate1 a t) (b.instantiate1 a (t + 1)) m) = _
    rw [ih (t - 1) (d.instantiate1 a t) (b.instantiate1 a (t + 1)) m
      (by simp only [List.length_cons] at hlen; omega)]
    show Expr.forallE (instSeq as (t - 1) (d.instantiate1 a t))
        (instSeq as (t - 1 + 1) (b.instantiate1 a (t + 1))) m =
      Expr.forallE (instSeq as (t - 1) (d.instantiate1 a t))
        (instSeq as (t + 1 - 1) (b.instantiate1 a (t + 1))) m
    cases as with
    | nil => rfl
    | cons a2 as2 =>
      have ht : t - 1 + 1 = t + 1 - 1 := by
        simp only [List.length_cons] at hlen
        omega
      rw [ht]

/-- An instantiation sequence distributes over a single application. -/
theorem instSeq_app :
    ∀ (args : List Expr) (t : Nat) (f a : Expr),
      instSeq args t (.app f a) =
        .app (instSeq args t f) (instSeq args t a) := by
  intro args
  induction args with
  | nil => intro t f a; rfl
  | cons x xs ih =>
    intro t f a
    show instSeq xs (t - 1) ((Expr.app f a).instantiate1 x t) = _
    show instSeq xs (t - 1)
      (.app (f.instantiate1 x t) (a.instantiate1 x t)) = _
    rw [ih]
    rfl

/-- Instantiating with a scoped term keeps reachable-`fvar` bounds. -/
theorem fvarsBelow_instantiate1_gen {d : Nat} {a : Expr} (ha : fvarsBelow d a) :
    ∀ {e : Expr} (k : Nat), fvarsBelow d e → fvarsBelow d (e.instantiate1 a k) := by
  intro e
  induction e <;> intro k hb <;> simp_all [instantiate1, fvarsBelow]
  case bvar i =>
    split
    · exact ha
    · split <;> simp [fvarsBelow]


/-- Replace `fvar p` by `a`, lowering higher `fvar` indices. -/
@[expose] def substFvarAt (p : Nat) (a : Expr) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar idx ty =>
    if idx = p then a
    else if idx > p then .fvar (idx - 1) (substFvarAt p a ty)
    else .fvar idx ty
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f b => .app (substFvarAt p a f) (substFvarAt p a b)
  | .lam ty body m => .lam (substFvarAt p a ty) (substFvarAt p a body) m
  | .forallE ty body m => .forallE (substFvarAt p a ty) (substFvarAt p a body) m
  | .letE ty val body =>
    .letE (substFvarAt p a ty) (substFvarAt p a val) (substFvarAt p a body)
  | .lit l => .lit l
  | .proj s i e => .proj s i (substFvarAt p a e)

/-- Substitution commutes with opening a binder at a higher index. -/
theorem substFvarAt_instantiate1 {p d : Nat} (hpd : p ≤ d) {ty a : Expr}
    (hba : a.looseBVarsBounded 0 = true) :
    ∀ (e : Expr) (k : Nat),
      substFvarAt p a (e.instantiate1 (.fvar (d + 1) ty) k) =
        (substFvarAt p a e).instantiate1 (.fvar d (substFvarAt p a ty)) k := by
  intro e
  induction e with
  | bvar i =>
    intro k
    simp only [instantiate1, substFvarAt]
    split
    · have h1 : ¬ (d + 1 = p) := by omega
      have h2 : d + 1 > p := by omega
      simp [substFvarAt, h1, h2]
    · split <;> simp [substFvarAt]
  | fvar idx ty' ih =>
    intro k
    simp only [instantiate1, substFvarAt]
    by_cases h1 : idx = p
    · simp only [h1, if_true]
      exact (instantiate1_eq_self (looseBVarsBounded_mono (Nat.zero_le k) hba)).symm
    · by_cases h2 : idx > p
      · simp [h1, h2, instantiate1]
      · simp [h1, h2, instantiate1]
  | _ =>
    intro k
    simp_all [instantiate1, substFvarAt]

/-- The beta bridge: opening with a fresh variable, then substituting it,
equals opening with the term directly. -/
theorem substFvarAt_instantiate1_self {d : Nat} {ty a : Expr} :
    ∀ (e : Expr) (k : Nat), fvarsBelow d e →
      substFvarAt d a (e.instantiate1 (.fvar d ty) k) = e.instantiate1 a k := by
  intro e
  induction e with
  | bvar i =>
    intro k hb
    simp only [instantiate1]
    split
    · simp [substFvarAt]
    · split <;> simp [substFvarAt]
  | fvar idx ty' ih =>
    intro k hb
    simp only [fvarsBelow] at hb
    have h1 : ¬ idx = d := by omega
    have h2 : ¬ idx > d := by omega
    simp [instantiate1, substFvarAt, h1, h2]
  | _ =>
    intro k hb
    simp_all [instantiate1, substFvarAt, fvarsBelow]


/-! ### `instantiate1`, constructor by constructor

`denote` opens every binder with `instantiate1` at cut `0`, so a basis
type's computation walks it once per node.  Unfolding the definition
leaves a decidable `if` at each `bvar`; these equations let `simp` take
the step without ever producing one. -/

@[simp] theorem instantiate1_bvar (i : Nat) (v : Expr) (d : Nat) :
    (Expr.bvar i).instantiate1 v d =
      if i = d then v else if i > d then .bvar (i - 1) else .bvar i := rfl
@[simp] theorem instantiate1_const (n : Name) (us : List Level)
    (v : Expr) (d : Nat) : (Expr.const n us).instantiate1 v d = .const n us :=
  rfl
@[simp] theorem instantiate1_sort (u : Level) (v : Expr) (d : Nat) :
    (Expr.sort u).instantiate1 v d = .sort u := rfl
@[simp] theorem instantiate1_fvar (i : Nat) (ty v : Expr)
    (d : Nat) : (Expr.fvar i ty).instantiate1 v d = .fvar i ty := rfl
@[simp] theorem instantiate1_app (f a v : Expr) (d : Nat) :
    (Expr.app f a).instantiate1 v d
      = .app (f.instantiate1 v d) (a.instantiate1 v d) := rfl
@[simp] theorem instantiate1_forallE (ty body v : Expr)
    (bi : BinderMeta) (d : Nat) :
    (Expr.forallE ty body bi).instantiate1 v d
      = .forallE (ty.instantiate1 v d) (body.instantiate1 v (d + 1)) bi := rfl
@[simp] theorem instantiate1_lam (ty body v : Expr)
    (bi : BinderMeta) (d : Nat) :
    (Expr.lam ty body bi).instantiate1 v d
      = .lam (ty.instantiate1 v d) (body.instantiate1 v (d + 1)) bi := rfl

end ConLeche.Expr
