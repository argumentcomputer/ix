module

import ConLeche.Verify.EnvBound
public import ConLeche.Verify.Cached.SimC
/- `withPtrEq` (`Init.Util`) is `public` but not `@[expose]`, and the
pointer-guarded `Expr.exprPtrBEq`/`beq` identities below are exactly the
`k ()` unfolding of it — the same escape `ConLeche/Kernel/Name.lean` and
`ConLeche/Kernel/Expr.lean` take at the definition sites. -/
import all Init.Util

public section

/-!
# Effect specs for the cached checker's state wrappers (task #163, batch 5)

One `CEff` lemma per `ConLeche/Cached/StateC.lean` wrapper — the port of
`SimI.lean`'s `Effects`/`LevelEffects`/`CacheFill` sections.

Almost every wrapper of the clone is a `pure`, so almost every lemma
here is a two-liner consuming the batch-3 commutation spec of the
underlying `Expr` operation.  The three that are *not* pure are the
persistent memos — the bulk-instantiation cache (`instListM`), the
level memos (`simplifyLM`/`isNonZeroLM`/`isEquivLM`) and the lazy
stored-constant caches (`constTyAtM`/`constValAtM`/`ruleRhsAtM`) — and
they carry their own insert lemmas against the matching `CSOK` clause,
in the erasure-function-of-key discipline: a memo hit's key is only
`BEq`-equal to the query, so what a collision transports is the
erasure, never the fields.
-/

namespace ConLeche.Cached

open ConLeche
open Expr

variable {mode : CheckMode}

/-! ## Key collisions

`Std.HashMap.getElem?_insert` splits on `storedKey == queryKey`; the
`Expr` halves of a colliding key have equal erasures
(`beq_sound`), and the rest is honest equality. -/

private theorem map_eraseC_of_beq : ∀ {a b : List Expr}, (a == b) = true →
    a = b := by
  intro a
  induction a with
  | nil =>
    intro b h
    cases b with
    | nil => rfl
    | cons y ys => exact nomatch h
  | cons x xs ih =>
    intro b h
    cases b with
    | nil => exact nomatch h
    | cons y ys =>
      have h' : ((x == y) && (xs == ys)) = true := h
      rw [Bool.and_eq_true] at h'
      rw [ih h'.2, beq_sound h'.1]

/-- The components of a `BEq`-equal `instC` key. -/
private theorem instKey_inv {a c : Expr} {vs vs' : List Expr} {d d' : Nat}
    (h : ((a, vs, d) == (c, vs', d')) = true) :
    a = c ∧ vs = vs' ∧ d = d' := by
  obtain ⟨h1, h2⟩ := pairKey_inv h
  have h2' : ((vs == vs') && (d == d')) = true := h2
  rw [Bool.and_eq_true] at h2'
  exact ⟨h1, map_eraseC_of_beq h2'.1, eq_of_beq h2'.2⟩

/-! ## Component replacements

The `CSOK` clauses are independent, so a wrapper that touches one cache
gets its invariant back by replacing that clause. -/

variable {env : Env}

/-- Replace the `Level.simplify` memo. -/
theorem CSOK.withLsimp {s : CState} (hs : CSOK mode env s)
    {m' : Std.HashMap Level Level}
    (hm : ∀ u v, m'[u]? = some v → v = Level.simplify u) :
    CSOK mode env { s with lsimpC := m' } :=
  ⟨hs.constTy, hs.constVal, hs.ruleRhs, hs.whnfCoreC, hs.whnfC,
    hs.inferC, hs.inferIOC, hs.annotC, hs.defeqC, hm, hs.lnz, hs.eqv, hs.ienv,
    hs.instC⟩

/-- Replace the `Level.simplify` memo and the equivalence result cache
together (the `isEquivLM` wrapper touches both). -/
theorem CSOK.withLsimpEqv {s : CState} (hs : CSOK mode env s)
    {m' : Std.HashMap Level Level} {ec' : Std.HashMap (Level × Level) Bool}
    (hm : ∀ u v, m'[u]? = some v → v = Level.simplify u)
    (he : ∀ l r b, ec'[(l, r)]? = some b → Level.isEquiv l r = some b) :
    CSOK mode env { s with lsimpC := m', eqvC := ec' } :=
  ⟨hs.constTy, hs.constVal, hs.ruleRhs, hs.whnfCoreC, hs.whnfC,
    hs.inferC, hs.inferIOC, hs.annotC, hs.defeqC, hm, hs.lnz, he, hs.ienv, hs.instC⟩

/-! ### The memo-insert closures -/

/-- Inserting the spec value at a key keeps the `lsimpC` clause. -/
theorem lsimpInv_insert {m : Std.HashMap Level Level}
    (hm : ∀ u v, m[u]? = some v → v = Level.simplify u) (k : Level) :
    ∀ u v, (m.insert k (Level.simplify k))[u]? = some v →
      v = Level.simplify u := by
  intro u v h
  rw [Std.HashMap.getElem?_insert] at h
  by_cases hk : k == u
  · rw [if_pos hk] at h
    cases h
    rw [eq_of_beq hk]
  · rw [if_neg (by simpa using hk)] at h
    exact hm u v h

/-- Inserting a certified verdict keeps the `eqvC` clause. -/
theorem eqvInv_insert {m : Std.HashMap (Level × Level) Bool}
    (hm : ∀ l r b, m[(l, r)]? = some b → Level.isEquiv l r = some b)
    {l r : Level} {b : Bool} (hb : Level.isEquiv l r = some b) :
    ∀ l' r' b', (m.insert (l, r) b)[(l', r')]? = some b' →
      Level.isEquiv l' r' = some b' := by
  intro l' r' b' h
  rw [Std.HashMap.getElem?_insert] at h
  by_cases hk : ((l, r) : Level × Level) == (l', r')
  · rw [if_pos hk] at h
    obtain ⟨rfl, rfl⟩ : l = l' ∧ r = r' := by
      have := eq_of_beq hk
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    cases h
    exact hb
  · rw [if_neg (by simpa using hk)] at h
    exact hm l' r' b' h

/-! ## The pure syntactic wrappers -/

section Effects

variable {s₀ : CState}

/-- Building one node: the cached core allocates it outright, so the
effect is the value's own reflexivity (task #198 -- this was
`internI_eff`, whose `internI` was a `pure` of the built node). -/
theorem pureC_eff (hs : CSOK mode env s₀) (x : Expr) :
    CEff mode env s₀ (fun i => RelC i x) (pure x) :=
  CEff.pure hs (RelC.refl x)

/-- The `bvar` allocation goes through `Expr.mkBvar` (the shared small
nodes), which is the constructor (`Expr.mkBvar_eq`). -/
theorem pureBvar_eff (hs : CSOK mode env s₀) (i : Nat) :
    CEff mode env s₀ (fun e => RelC e (Expr.bvar i)) (pure (Expr.mkBvar i)) :=
  CEff.pure hs (Expr.mkBvar_eq i)

theorem inst1M_eff (hs : CSOK mode env s₀) {e v : Expr} {d : Nat}
    {a w : Expr} (he : RelC e a) (hv : RelC v w) :
    CEff mode env s₀ (fun i => RelC i (a.instantiate1 w d)) (inst1M e v d) := by
  refine CEff.pure hs ?_
  show _ = _
  rw [instantiate1C_spec (d := d), he.erase, hv.erase]

theorem instListRevM_eff (hs : CSOK mode env s₀) {e : Expr}
    {vs : Array Expr} {d : Nat} {a : Expr} {ws : List Expr}
    (he : RelC e a) (hvs : RelCL vs.toList.reverse ws) :
    CEff mode env s₀ (fun i => RelC i (a.instantiateList ws d))
      (instListRevM e vs d) := by
  refine CEff.pure hs ?_
  show _ = _
  rw [instantiateRev_spec (d := d), he.erase, hvs.map]

theorem abstract1M_eff (hs : CSOK mode env s₀) {e : Expr} {d : Nat}
    {a : Expr} (he : RelC e a) :
    CEff mode env s₀ (fun i => RelC i (a.abstract1 d)) (abstract1M e d) := by
  refine CEff.pure hs ?_
  show _ = _
  rw [abstract1C_spec (d := d) (k := 0), he.erase]

theorem abstractRangeM_eff (hs : CSOK mode env s₀) {e : Expr} {d k : Nat}
    {a : Expr} (he : RelC e a) :
    CEff mode env s₀ (fun i => RelC i (a.abstractRange d k))
      (abstractRangeM e d k) := by
  refine CEff.pure hs ?_
  show _ = _
  rw [abstractRangeC_spec (d := d) (k := k) (c := 0), he.erase]

/-- The `O(1)` loose-bvar bound field is exact on the invariant, so the
value it returns bounds the erasure (the port of `bvarBoundM_eff`,
whose arena leg was `TWF.bvarBoundD_le2`). -/
theorem bvarBoundM_eff (hs : CSOK mode env s₀) {e : Expr} :
    CEff mode env s₀ (fun b => (Expr.looseBVarsBounded b e) = true)
      (bvarBoundM e) :=
  CEff.pure hs (bvarB_le (Nat.le_refl _))

theorem mkAppNM_eff (hs : CSOK mode env s₀) {f : Expr} {args : List Expr}
    {x : Expr} {xs : List Expr}
    (hf : RelC f x) (hargs : RelCL args xs) :
    CEff mode env s₀ (fun i => RelC i (Expr.mkAppN x xs)) (mkAppNM f args) := by
  refine CEff.pure hs ?_
  show _ = _
  rw [hf.erase, hargs.map]

theorem instSpineM_eff (hs : CSOK mode env s₀) {args : List Expr} {t : Nat}
    {e : Expr} {x : Expr} {xs : List Expr}
    (he : RelC e x) (hargs : RelCL args xs) :
    CEff mode env s₀ (fun i => RelC i (Expr.instSpine xs t x))
      (instSpineM args t e) := by
  refine CEff.pure hs ?_
  show _ = _
  rw [instSpineC_spec (t := t), he.erase, hargs.map]

theorem piResidualM_eff (hs : CSOK mode env s₀) {e : Expr}
    {args : List Expr} {x : Expr} {xs : List Expr}
    (he : RelC e x) (hargs : RelCL args xs) :
    CEff mode env s₀ (fun o => OptEr o (ConLeche.piResidual x xs))
      (piResidualM e args) := by
  refine CEff.pure hs ?_
  have h := piResidual_spec (e := e) (args := args)
  rw [← he.erase, ← hargs.map]
  exact h

theorem instLevelParamsM_eff (hs : CSOK mode env s₀) {ks : List Name}
    {us : List Level} {e : Expr} {a : Expr} (he : RelC e a) :
    CEff mode env s₀
      (fun i => RelC i (a.instantiateLevelParams ks us))
      (instLevelParamsM ks us e) := by
  refine CEff.pure hs ?_
  show _ = _
  rw [instLevelParams_spec (ks := ks) (us := us), he.erase]

/-- The binder-telescope peel fuel is a constant (the clone has no
arena node count to read). -/
theorem peelFuelM_eff (hs : CSOK mode env s₀) :
    CEff mode env s₀ (fun n => n = peelFuel) peelFuelM :=
  CEff.pure hs rfl

/-! ## Pure reads

The names and levels the core fabricates are ordinary values: the
cached checker's name/level "interning" and "readback" wrappers were
identities and went at task #198, so what the walks peel is a `pure`
and what they consume is its value equation. -/

/-- A `pure` read: the value is what was handed in. -/
theorem pureEq_eff {α : Type} (hs : CSOK mode env s₀) (x : α) :
    CEff mode env s₀ (fun v => v = x) (pure x) :=
  CEff.pure hs rfl

theorem substLevelTreesM_eff (hs : CSOK mode env s₀) (ks : List Name)
    (us : List Level) (ls : List Level) :
    CEff mode env s₀ (fun vs => vs = ls.map (Level.subst ks us))
      (substLevelTreesM ks us ls) :=
  CEff.pure hs rfl

end Effects

/-! ## The persistent level memos -/

section LevelEffects

variable {s₀ : CState}

/-- The inlined `simplify`-with-memo step of `isEquivLM` (the clone's
counterpart of the interned `simplifyLIGo` call). -/
private def simplifyMemo (mp : Std.HashMap Level Level) (u : Level) :
    Level × Std.HashMap Level Level :=
  match mp[u]? with
  | some x => (x, mp)
  | none => let x := Level.simplify u; (x, mp.insert u x)

private theorem simplifyMemo_spec {mp : Std.HashMap Level Level}
    (hmp : ∀ u v, mp[u]? = some v → v = Level.simplify u) (u : Level) :
    (simplifyMemo mp u).1 = Level.simplify u ∧
      ∀ a b, (simplifyMemo mp u).2[a]? = some b → b = Level.simplify a := by
  unfold simplifyMemo
  cases hc : mp[u]? with
  | some x => exact ⟨hmp u x hc, hmp⟩
  | none => exact ⟨rfl, lsimpInv_insert hmp u⟩

/-- The task-#176 P2 head test: syntactically equal levels answer
without touching the state or the cache. -/
private theorem isEquivLM_run_ptr {l r : Level} (h : (l == r) = true)
    (s : CState) : isEquivLM l r s = .ok (some true, s) := by
  unfold isEquivLM; rw [if_pos h]; rfl

private theorem isEquivLM_run {l r : Level} (h : ¬ (l == r) = true)
    (s : CState) :
    isEquivLM l r s = .ok
      (match s.eqvC[(l, r)]? with
       | some b => (some b, s)
       | none =>
         let (ls, mp) := simplifyMemo s.lsimpC l
         let (rs, mp) := simplifyMemo mp r
         if ls == rs then
           (some true,
             { s with lsimpC := mp, eqvC := s.eqvC.insert (l, r) true })
         else
           match Level.leqCore Level.defaultFuel ls rs 0 with
           | some false =>
             (some false,
               { s with lsimpC := mp, eqvC := s.eqvC.insert (l, r) false })
           | some true =>
             match Level.leqCore Level.defaultFuel rs ls 0 with
             | some b =>
               (some b,
                 { s with lsimpC := mp, eqvC := s.eqvC.insert (l, r) b })
             | none => (none, { s with lsimpC := mp })
           | none => (none, { s with lsimpC := mp })) := by
  unfold isEquivLM; rw [if_neg h]; rfl

/-- `Level.isEquiv` in the shape the cascade decides it: the
simplified-form test, then the two `leqCore` runs. -/
private theorem isEquiv_cascade (l r : Level)
    (hne : ¬ Level.simplify l = Level.simplify r) :
    Level.isEquiv l r =
      match Level.leqCore Level.defaultFuel (Level.simplify l)
          (Level.simplify r) 0 with
      | none => none
      | some false => some false
      | some true =>
        match Level.leqCore Level.defaultFuel (Level.simplify r)
            (Level.simplify l) 0 with
        | none => none
        | some b2 => some b2 := by
  rw [Level.isEquiv_eq_withoutPtr, if_neg hne]
  simp only [Level.leq, Bind.bind, Option.bind]
  cases Level.leqCore Level.defaultFuel (Level.simplify l) (Level.simplify r) 0
    with
  | none => rfl
  | some b1 =>
    cases b1 with
    | false => rfl
    | true =>
      cases Level.leqCore Level.defaultFuel (Level.simplify r)
          (Level.simplify l) 0 with
      | none => rfl
      | some b2 => rfl

/-- The `isEquiv` result cache: a hit is certified by the `eqvC`
clause, a miss runs the same `simplify`/`leqCore` cascade the interned
wrapper runs — through the `lsimpC` memo, whose entries are the spec
values by the `lsimp` clause.  Where the interned proof needed
`denoteL_inj` to turn index equality into level equality, the tree keys
are `LawfulBEq`, so `ls == rs` *is* `ls = rs`. -/
theorem isEquivLM_eff (hs : CSOK mode env s₀) (l r : Level) :
    CEff mode env s₀ (fun ob => ob = Level.isEquiv l r) (isEquivLM l r) := by
  intro v' s' hrun
  by_cases hlr : (l == r) = true
  · -- the task-#176 P2 head test: no cache touch, no state change
    rw [isEquivLM_run_ptr hlr] at hrun
    injection hrun with h1
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
    exact ⟨hs, (Level.isEquiv_of_beq hlr).symm⟩
  rw [isEquivLM_run hlr] at hrun
  cases hc : s₀.eqvC[(l, r)]? with
  | some b =>
    rw [hc] at hrun
    injection hrun with h1
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
    exact ⟨hs, (hs.eqv l r b hc).symm⟩
  | none =>
    rw [hc] at hrun
    rcases hm1 : simplifyMemo s₀.lsimpC l with ⟨ls, mp1⟩
    obtain ⟨hls, hmp1⟩ := simplifyMemo_spec hs.lsimp l
    simp only [hm1] at hls hmp1
    rcases hm2 : simplifyMemo mp1 r with ⟨rs, mp2⟩
    obtain ⟨hrs, hmp2⟩ := simplifyMemo_spec hmp1 r
    simp only [hm2] at hrs hmp2
    rw [hm1] at hrun
    dsimp only at hrun
    rw [hm2] at hrun
    dsimp only at hrun
    cases hbeq : ls == rs with
    | true =>
      rw [hbeq] at hrun
      injection hrun with h1
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
      have hss : Level.simplify l = Level.simplify r := by
        rw [← hls, ← hrs, eq_of_beq hbeq]
      have hob : (some true : Option Bool) = Level.isEquiv l r := by
        rw [Level.isEquiv_eq_withoutPtr, if_pos hss]; rfl
      exact ⟨hs.withLsimpEqv hmp2 (eqvInv_insert hs.eqv hob.symm), hob⟩
    | false =>
      rw [hbeq] at hrun
      have hss : ¬ Level.simplify l = Level.simplify r := by
        intro hE
        rw [← hls, ← hrs] at hE
        rw [hE, beq_self_eq_true] at hbeq
        exact Bool.true_eq_false ▸ hbeq
      have hcas := isEquiv_cascade l r hss
      rw [← hls, ← hrs] at hcas
      cases hb1 : Level.leqCore Level.defaultFuel ls rs 0 with
      | none =>
        rw [hb1] at hrun
        injection hrun with h1
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
        exact ⟨hs.withLsimp hmp2, by rw [hcas, hb1]⟩
      | some b1 =>
        cases b1 with
        | false =>
          rw [hb1] at hrun
          injection hrun with h1
          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
          have hob : (some false : Option Bool) = Level.isEquiv l r := by
            rw [hcas, hb1]
          exact ⟨hs.withLsimpEqv hmp2 (eqvInv_insert hs.eqv hob.symm), hob⟩
        | true =>
          cases hb2 : Level.leqCore Level.defaultFuel rs ls 0 with
          | none =>
            rw [hb1, hb2] at hrun
            injection hrun with h1
            obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
            exact ⟨hs.withLsimp hmp2, by rw [hcas, hb1, hb2]⟩
          | some b2 =>
            rw [hb1, hb2] at hrun
            injection hrun with h1
            obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
            have hob : (some b2 : Option Bool) = Level.isEquiv l r := by
              rw [hcas, hb1, hb2]
            exact ⟨hs.withLsimpEqv hmp2 (eqvInv_insert hs.eqv hob.symm), hob⟩

/-- Pointwise `isEquivLM`. -/
theorem isEquivListLM_eff :
    ∀ {ls rs : List Level} {s₀ : CState}, CSOK mode env s₀ →
      CEff mode env s₀ (fun ob => ob = Level.isEquivList ls rs)
        (isEquivListLM ls rs) := by
  intro ls
  induction ls with
  | nil =>
    intro rs s₀ hs
    cases rs with
    | nil => exact CEff.pure hs rfl
    | cons r rs' => exact CEff.pure hs rfl
  | cons l ls' ih =>
    intro rs s₀ hs
    cases rs with
    | nil => exact CEff.pure hs rfl
    | cons r rs' =>
      rw [show isEquivListLM (l :: ls') (r :: rs') = (do
        match ← isEquivLM l r with
        | none => pure none
        | some false => pure (some false)
        | some true => isEquivListLM ls' rs' :
        CheckCM (Option Bool)) from rfl]
      refine (isEquivLM_eff hs l r).bind ?_
      intro s₁ ob hs₁ hob
      subst hob
      cases hE : Level.isEquiv l r with
      | none =>
        refine CEff.pure hs₁ ?_
        simp [Level.isEquivList, hE]
      | some b =>
        cases b with
        | false =>
          refine CEff.pure hs₁ ?_
          simp [Level.isEquivList, hE]
        | true =>
          intro v' s' hrun2
          obtain ⟨hs₂, hobs⟩ := ih hs₁ v' s' hrun2
          exact ⟨hs₂, by simp [Level.isEquivList, hE, hobs]⟩

end LevelEffects

/-! ## The persistent bulk-instantiation memo -/

section InstMemo

variable {s₀ : CState}

/-- Inserting a backed entry into the bulk-instantiation memo preserves
the invariant (task #145).  The `instCCapC` overflow branch inserts into
the *empty* table instead, which is the same statement with a smaller
table — hence the `mp` generalisation.

The colliding-key case is where the erasure-function-of-key discipline
pays: a `BEq` collision pins the stored key to the query only through
`instKey_inv`, and that is exactly the datum the clause consumes. -/
theorem CSOK.insertInstC {s : CState} (hs : CSOK mode env s)
    {e r : Expr} {vs : List Expr} {d : Nat}
    {mp : Std.HashMap (Expr × List Expr × Nat) Expr}
    (hmp : ∀ (i : Expr) (vs' : List Expr) (d' : Nat) (r' : Expr),
      mp[(i, vs', d')]? = some r' →
        r' = (Expr.instantiateList i vs' d'))
    (hE : r = (Expr.instantiateList e vs d)) :
    CSOK mode env { s with instC := mp.insert (e, vs, d) r } := by
  refine ⟨hs.constTy, hs.constVal, hs.ruleRhs, hs.whnfCoreC, hs.whnfC,
    hs.inferC, hs.inferIOC, hs.annotC, hs.defeqC, hs.lsimp, hs.lnz, hs.eqv, hs.ienv, ?_⟩
  intro i' vs' d' r' hl
  simp only at hl
  rw [Std.HashMap.getElem?_insert] at hl
  by_cases hk : ((e, vs, d) : Expr × List Expr × Nat) == (i', vs', d')
  · rw [if_pos hk] at hl
    cases hl
    obtain ⟨h1, h2, rfl⟩ := instKey_inv hk
    rw [hE, h1, h2]
  · rw [if_neg hk] at hl
    exact hmp i' vs' d' r' hl

private theorem instListM_run (e : Expr) (vs : List Expr) (d : Nat)
    (s : CState) :
    instListM e vs d s = .ok
      (if e.bvarB ≤ d then (e, s)
       else
         match s.instC[(e, vs, d)]? with
         | some r => (r, s)
         | none =>
           let mp := if s.instC.size < instCCapC then s.instC else {}
           (Expr.instantiateListC e vs d,
             { s with instC :=
                 mp.insert (e, vs, d) (Expr.instantiateListC e vs d) })) := rfl

/-- Bulk instantiation through the persistent memo.  A hit is *exact*
here — the stored key is the query key, not merely an index denoting
the same term — so the interned proof's determinism step disappears. -/
theorem instListM_eff (hs : CSOK mode env s₀) {e : Expr} {vs : List Expr}
    {d : Nat} {a : Expr} {ws : List Expr}
    (he : RelC e a) (hvs : RelCL vs ws) :
    CEff mode env s₀ (fun i => RelC i (a.instantiateList ws d))
      (instListM e vs d) := by
  intro v' s' hr
  rw [instListM_run] at hr
  injection hr with h1
  by_cases hble : e.bvarB ≤ d
  · rw [if_pos hble] at h1
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1.symm
    refine ⟨hs, ?_⟩
    have hb : Expr.looseBVarsBounded d a = true := he.erase ▸ bvarB_le hble
    show _ = _
    rw [he.erase, Expr.instantiateList_eq_self hb]
  · rw [if_neg hble] at h1
    cases hhit : s₀.instC[(e, vs, d)]? with
    | some j =>
      rw [hhit] at h1
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1.symm
      have hE := hs.instC e vs d _ hhit
      exact ⟨hs, by show _ = _; rw [hE, he.erase, hvs.map]⟩
    | none =>
      rw [hhit] at h1
      dsimp only at h1
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1.symm
      have hE := instantiateListC_spec (e := e) (vs := vs) (d := d)
      refine ⟨?_, by show _ = _; rw [hE, he.erase, hvs.map]⟩
      refine hs.insertInstC ?_ hE
      -- the retained table is either the old one or empty, both backed
      split
      · exact hs.instC
      · intro i' vs' d' r' hl
        simp at hl

end InstMemo

/-! ## The converted-constant cache and the lazy stored-constant caches -/

section CacheFill

variable {s₀ : CState}

/-- Recording a converted constant preserves the invariant. -/
theorem CSOK.insertIEnv {s : CState} (hs : CSOK mode env s) {n : Name}
    {ent : CConstE} (hty : RelC ent.ty ent.tyE)
    (hval : ∀ vE vi, ent.val = some (vE, vi) → RelC vi vE) :
    CSOK mode env { s with ienv := s.ienv.insert n ent } := by
  refine ⟨hs.constTy, hs.constVal, hs.ruleRhs, hs.whnfCoreC, hs.whnfC,
    hs.inferC, hs.inferIOC, hs.annotC, hs.defeqC, hs.lsimp, hs.lnz, hs.eqv, ?_,
    hs.instC⟩
  intro nm ent' hl
  simp only at hl
  rw [Std.HashMap.getElem?_insert] at hl
  by_cases hk : n == nm
  · rw [if_pos hk] at hl
    cases hl
    exact ⟨hty, hval⟩
  · rw [if_neg hk] at hl
    exact hs.ienv nm ent' hl

/-- Inserting a backed entry into `constTyAt` preserves the
invariant. -/
theorem CSOK.insertConstTy {s : CState} (hs : CSOK mode env s)
    {n : Name} {us : List Level} {i : Expr} {ci : ConstantInfo}
    (hfind : env.find? n = some ci)
    (hrel : RelC i (ci.toConstantVal.type.instantiateLevelParams
      ci.toConstantVal.levelParams us)) :
    CSOK mode env { s with constTyAt := s.constTyAt.insert (n, us) i } := by
  refine ⟨?_, hs.constVal, hs.ruleRhs, hs.whnfCoreC, hs.whnfC, hs.inferC, hs.inferIOC,
    hs.annotC, hs.defeqC, hs.lsimp, hs.lnz, hs.eqv, hs.ienv, hs.instC⟩
  intro n' us' i' hl
  simp only at hl
  rw [Std.HashMap.getElem?_insert] at hl
  by_cases hk : ((n, us) : Name × List Level) == (n', us')
  · rw [if_pos hk] at hl
    obtain ⟨rfl, rfl⟩ : n = n' ∧ us = us' := by
      have h := eq_of_beq hk
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    cases hl
    exact ⟨ci, hfind, hrel⟩
  · rw [if_neg hk] at hl
    exact hs.constTy n' us' i' hl

/-- Inserting a backed entry into `constValAt` preserves the
invariant. -/
theorem CSOK.insertConstVal {s : CState} (hs : CSOK mode env s)
    {n : Name} {us : List Level} {i : Expr}
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hfind : env.find? n = some (.defnInfo cv v hint))
    (hrel : RelC i (v.instantiateLevelParams cv.levelParams us)) :
    CSOK mode env { s with constValAt := s.constValAt.insert (n, us) i } := by
  refine ⟨hs.constTy, ?_, hs.ruleRhs, hs.whnfCoreC, hs.whnfC, hs.inferC, hs.inferIOC,
    hs.annotC, hs.defeqC, hs.lsimp, hs.lnz, hs.eqv, hs.ienv, hs.instC⟩
  intro n' us' i' hl
  simp only at hl
  rw [Std.HashMap.getElem?_insert] at hl
  by_cases hk : ((n, us) : Name × List Level) == (n', us')
  · rw [if_pos hk] at hl
    obtain ⟨rfl, rfl⟩ : n = n' ∧ us = us' := by
      have h := eq_of_beq hk
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    cases hl
    exact ⟨cv, v, hint, hfind, hrel⟩
  · rw [if_neg hk] at hl
    exact hs.constVal n' us' i' hl

/-- Inserting a backed entry into `ruleRhsAt` preserves the
invariant. -/
theorem CSOK.insertRuleRhs {s : CState} (hs : CSOK mode env s)
    {c j : Name} {us : List Level} {i : Expr}
    {cv : ConstantVal} {mI rP : Nat} {rules : List RecRule} {rl : RecRule}
    (hfind : env.find? c = some (.recInfo cv mI rP rules))
    (hrl : rules.find? (fun r' => r'.ctor == j) = some rl)
    (hrel : RelC i (rl.rhs.instantiateLevelParams cv.levelParams us)) :
    CSOK mode env
      { s with ruleRhsAt := s.ruleRhsAt.insert (c, j, us) i } := by
  refine ⟨hs.constTy, hs.constVal, ?_, hs.whnfCoreC, hs.whnfC, hs.inferC, hs.inferIOC,
    hs.annotC, hs.defeqC, hs.lsimp, hs.lnz, hs.eqv, hs.ienv, hs.instC⟩
  intro c' j' us' i' hl
  simp only at hl
  rw [Std.HashMap.getElem?_insert] at hl
  by_cases hk : ((c, j, us) : Name × Name × List Level) == (c', j', us')
  · rw [if_pos hk] at hl
    obtain ⟨rfl, rfl, rfl⟩ : c = c' ∧ j = j' ∧ us = us' := by
      have h := eq_of_beq hk
      exact ⟨congrArg Prod.fst h, congrArg (·.2.1) h, congrArg (·.2.2) h⟩
    cases hl
    exact ⟨cv, mI, rP, rules, rl, hfind, hrl, hrel⟩
  · rw [if_neg hk] at hl
    exact hs.ruleRhs c' j' us' i' hl

/-- `storedTyIdxM` yields a term related to the given type — the
converted-constant hit path via the self-certifying `ienv` clause (the
pointer gate ties the tag to the argument), the miss paths via
`pureC_eff`. -/
theorem storedTyIdxM_eff (hs : CSOK mode env s₀) {n : Name} (x : Expr) :
    CEff mode env s₀ (fun i => RelC i x) (storedTyIdxM n x) := by
  intro v' s' hr
  rw [show storedTyIdxM n x = (do
      let ent? : Option CConstE ← modifyGet fun s => (s.ienv[n]?, s)
      match ent? with
      | some ent =>
        if Expr.exprPtrBEq ent.tyE x then pure ent.ty
        else pure x
      | none => pure x : CheckCM Expr) from rfl] at hr
  simp only [Bind.bind, StateT.bind, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, Except.bind, pure, Except.pure] at hr
  cases hl : s₀.ienv[n]? with
  | some ent =>
    rw [hl] at hr
    dsimp only at hr
    by_cases hgate : Expr.exprPtrBEq ent.tyE x
    · rw [if_pos hgate] at hr
      have hEq : ent.tyE = x := by
        have : (ent.tyE == x) = true := hgate
        simpa using this
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
      exact ⟨hs, hEq ▸ (hs.ienv n ent hl).1⟩
    · rw [if_neg hgate] at hr
      exact pureC_eff hs x v' s' hr
  | none =>
    rw [hl] at hr
    exact pureC_eff hs x v' s' hr

/-- `storedValIdxM` yields a term related to the given value (see
`storedTyIdxM_eff`). -/
theorem storedValIdxM_eff (hs : CSOK mode env s₀) {n : Name} (x : Expr) :
    CEff mode env s₀ (fun i => RelC i x) (storedValIdxM n x) := by
  intro v' s' hr
  rw [show storedValIdxM n x = (do
      let ent? : Option CConstE ← modifyGet fun s => (s.ienv[n]?, s)
      match ent? with
      | some ⟨_, _, some (vE, vi)⟩ =>
        if Expr.exprPtrBEq vE x then pure vi
        else pure x
      | _ => pure x : CheckCM Expr) from rfl] at hr
  simp only [Bind.bind, StateT.bind, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, Except.bind, pure, Except.pure] at hr
  cases hl : s₀.ienv[n]? with
  | some ent =>
    rw [hl] at hr
    obtain ⟨tyE, ty, val⟩ := ent
    cases hval : val with
    | some p =>
      obtain ⟨vE, vi⟩ := p
      subst hval
      dsimp only at hr
      by_cases hgate : Expr.exprPtrBEq vE x
      · rw [if_pos hgate] at hr
        have hEq : vE = x := by
          have : (vE == x) = true := hgate
          simpa using this
        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
        exact ⟨hs, hEq ▸ (hs.ienv n ⟨tyE, ty, some (vE, vi)⟩ hl).2 vE vi rfl⟩
      · rw [if_neg hgate] at hr
        exact pureC_eff hs x v' s' hr
    | none =>
      subst hval
      dsimp only at hr
      exact pureC_eff hs x v' s' hr
  | none =>
    rw [hl] at hr
    exact pureC_eff hs x v' s' hr

/-- `constTyAtM` under the index of `env`: the result is related to the
level-instantiated stored type. -/
theorem constTyAtM_eff (hs : CSOK mode env s₀) {nI n : Name}
    {us : List Level} {ci : ConstantInfo} (hfind : env.find? n = some ci) :
    CEff mode env s₀ (fun i => RelC i
        (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us))
      (constTyAtM (mkFEnv env) nI n us) := by
  intro v' s' hr
  rw [show constTyAtM (mkFEnv env) nI n us = (do
      let hit? ← modifyGet fun s => (s.constTyAt[(n, us)]?, s)
      match hit? with
      | some i => pure i
      | none =>
        match (mkFEnv env).find? n with
        | some ci =>
          let cv := ci.toConstantVal
          let raw ← storedTyIdxM n cv.type
          let i ← instLevelParamsM cv.levelParams us raw
          modify fun s =>
            let mp := s.constTyAt
            let s := { s with constTyAt := ∅ }
            { s with constTyAt := mp.insert (n, us) i }
          pure i
        | none => throw (.internal "constTyAtM: unknown constant") :
        CheckCM Expr) from rfl] at hr
  simp only [Bind.bind, StateT.bind, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, Except.bind, pure, Except.pure] at hr
  cases hl : s₀.constTyAt[(n, us)]? with
  | some i =>
    rw [hl] at hr
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
    obtain ⟨ci', hfind', hrel⟩ := hs.constTy n us _ hl
    rw [hfind] at hfind'
    cases hfind'
    exact ⟨hs, hrel⟩
  | none =>
    rw [hl] at hr
    rw [mkFEnv_find?, hfind] at hr
    dsimp only at hr
    simp only [Bind.bind, StateT.bind, Except.bind] at hr
    cases hrun : storedTyIdxM n ci.toConstantVal.type s₀ with
    | error he => rw [hrun] at hr; exact nomatch hr
    | ok pr =>
      obtain ⟨raw, s₁⟩ := pr
      rw [hrun] at hr
      dsimp only at hr
      obtain ⟨hs₁, hraw⟩ := storedTyIdxM_eff hs _ raw s₁ hrun
      cases hrun₂ : instLevelParamsM ci.toConstantVal.levelParams us raw s₁
          with
      | error he => rw [hrun₂] at hr; exact nomatch hr
      | ok pr₂ =>
        obtain ⟨i, s₂⟩ := pr₂
        rw [hrun₂] at hr
        dsimp only at hr
        obtain ⟨hs₂, hrel⟩ :=
          instLevelParamsM_eff hs₁ hraw i s₂ hrun₂
        simp only [modify, modifyGet, MonadStateOf.modifyGet,
          StateT.modifyGet, pure, StateT.pure, Except.pure,
          Except.ok.injEq] at hr
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
        exact ⟨hs₂.insertConstTy hfind hrel, hrel⟩

/-- `constValAtM` under the index of `env` (the head is a stored
definition). -/
theorem constValAtM_eff (hs : CSOK mode env s₀) {nI n : Name}
    {us : List Level} {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hfind : env.find? n = some (.defnInfo cv v hint)) :
    CEff mode env s₀
      (fun i => RelC i (v.instantiateLevelParams cv.levelParams us))
      (constValAtM (mkFEnv env) nI n us) := by
  intro v' s' hr
  rw [show constValAtM (mkFEnv env) nI n us = (do
      let hit? ← modifyGet fun s => (s.constValAt[(n, us)]?, s)
      match hit? with
      | some i => pure i
      | none =>
        match (mkFEnv env).find? n with
        | some (.defnInfo cv v _) =>
          let raw ← storedValIdxM n v
          let i ← instLevelParamsM cv.levelParams us raw
          modify fun s =>
            let mp := s.constValAt
            let s := { s with constValAt := ∅ }
            { s with constValAt := mp.insert (n, us) i }
          pure i
        | _ => throw (.internal "constValAtM: not a stored definition") :
        CheckCM Expr) from rfl] at hr
  simp only [Bind.bind, StateT.bind, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, Except.bind, pure, Except.pure] at hr
  cases hl : s₀.constValAt[(n, us)]? with
  | some i =>
    rw [hl] at hr
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
    obtain ⟨cv', v'', hint', hfind', hrel⟩ := hs.constVal n us _ hl
    rw [hfind] at hfind'
    cases hfind'
    exact ⟨hs, hrel⟩
  | none =>
    rw [hl] at hr
    · rw [mkFEnv_find?, hfind] at hr
      dsimp only at hr
      simp only [Bind.bind, StateT.bind, Except.bind] at hr
      cases hrun : storedValIdxM n v s₀ with
      | error he => rw [hrun] at hr; exact nomatch hr
      | ok pr =>
        obtain ⟨raw, s₁⟩ := pr
        rw [hrun] at hr
        dsimp only at hr
        obtain ⟨hs₁, hraw⟩ := storedValIdxM_eff hs _ raw s₁ hrun
        cases hrun₂ : instLevelParamsM cv.levelParams us raw s₁ with
        | error he => rw [hrun₂] at hr; exact nomatch hr
        | ok pr₂ =>
          obtain ⟨i, s₂⟩ := pr₂
          rw [hrun₂] at hr
          dsimp only at hr
          obtain ⟨hs₂, hrel⟩ := instLevelParamsM_eff hs₁ hraw i s₂ hrun₂
          simp only [modify, modifyGet, MonadStateOf.modifyGet,
            StateT.modifyGet, pure, StateT.pure, Except.pure,
            Except.ok.injEq] at hr
          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
          exact ⟨hs₂.insertConstVal hfind hrel, hrel⟩

/-- `ruleRhsAtM` under the index of `env`. -/
theorem ruleRhsAtM_eff (hs : CSOK mode env s₀) {cI jI c j : Name}
    {us : List Level} {cv : ConstantVal} {mI rP : Nat}
    {rules : List RecRule} {rl : RecRule}
    (hfind : env.find? c = some (.recInfo cv mI rP rules))
    (hrl : rules.find? (fun r' => r'.ctor == j) = some rl) :
    CEff mode env s₀
      (fun i => RelC i (rl.rhs.instantiateLevelParams cv.levelParams us))
      (ruleRhsAtM (mkFEnv env) cI jI c j us) := by
  intro v' s' hr
  rw [show ruleRhsAtM (mkFEnv env) cI jI c j us = (do
      let hit? ← modifyGet fun s => (s.ruleRhsAt[(c, j, us)]?, s)
      match hit? with
      | some i => pure i
      | none =>
        match (mkFEnv env).find? c with
        | some (.recInfo cv _ _ rules) =>
          match rules.find? (fun r' => r'.ctor == j) with
          | some rl =>
            let i ← instLevelParamsM cv.levelParams us rl.rhs
            modify fun s =>
              let mp := s.ruleRhsAt
              let s := { s with ruleRhsAt := ∅ }
              { s with ruleRhsAt := mp.insert (c, j, us) i }
            pure i
          | none => throw (.internal "ruleRhsAtM: no rule for constructor")
        | _ => throw (.internal "ruleRhsAtM: not a stored recursor") :
        CheckCM Expr) from rfl] at hr
  simp only [Bind.bind, StateT.bind, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, Except.bind, pure, Except.pure] at hr
  cases hl : s₀.ruleRhsAt[(c, j, us)]? with
  | some i =>
    rw [hl] at hr
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
    obtain ⟨cv', mI', rP', rules', rl', hfind', hrl', hrel⟩ :=
      hs.ruleRhs c j us _ hl
    rw [hfind] at hfind'
    cases hfind'
    rw [hrl] at hrl'
    cases hrl'
    exact ⟨hs, hrel⟩
  | none =>
    rw [hl] at hr
    rw [mkFEnv_find?, hfind] at hr
    dsimp only at hr
    rw [hrl] at hr
    dsimp only at hr
    simp only [Bind.bind, StateT.bind, Except.bind] at hr
    -- the raw right-hand side needs no conversion (task #198: what was
    -- a conversion of `rl.rhs` is the value itself)
    have hraw : RelC (rl.rhs : Expr) rl.rhs := rfl
    cases hrun₂ : instLevelParamsM cv.levelParams us rl.rhs s₀ with
    | error he => rw [hrun₂] at hr; exact nomatch hr
    | ok pr₂ =>
      obtain ⟨i, s₂⟩ := pr₂
      rw [hrun₂] at hr
      dsimp only at hr
      obtain ⟨hs₂, hrel⟩ := instLevelParamsM_eff hs hraw i s₂ hrun₂
      simp only [modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, pure, StateT.pure, Except.pure,
        Except.ok.injEq] at hr
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
      exact ⟨hs₂.insertRuleRhs hfind hrl hrel, hrel⟩

private theorem recordCConst_run (n : Name) (tyE : Expr) (ty : Expr)
    (val : Option (Expr × Expr)) (s : CState) :
    recordCConst n tyE ty val s =
      .ok ((), { s with ienv := s.ienv.insert n ⟨tyE, ty, val⟩ }) := rfl

/-- `recordCConst` as a state-only effect: the recorded conversions
must be related to the very `Expr` objects they are tagged with. -/
theorem recordCConst_eff (hs : CSOK mode env s₀) {n : Name} {tyE : Expr}
    {ty : Expr} {val : Option (Expr × Expr)}
    (hty : RelC ty tyE)
    (hval : ∀ vE vi, val = some (vE, vi) → RelC vi vE) :
    CEff mode env s₀ (fun _ => True) (recordCConst n tyE ty val) := by
  intro v' s' hr
  rw [recordCConst_run] at hr
  injection hr with h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
  exact ⟨hs.insertIEnv hty hval, trivial⟩

end CacheFill

end ConLeche.Cached
