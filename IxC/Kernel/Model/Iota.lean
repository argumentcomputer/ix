module

public import IxC.Kernel.Model.Denotes
public import IxC.Kernel.Model.IndFrame
public import IxC.Kernel.Model.IndGrade
public import IxC.Kernel.Model.IndFire
public import IxC.Kernel.Model.IndPointKit
public import IxC.Kernel.Verify.InstSpine
public import IxC.Kernel.Verify.InstLevels
import IxC.Kernel.Verify.InferLeaves
import IxC.Kernel.Verify.StrLitExpr
import IxC.Kernel.Verify.InferLemmas

public section

/-!
# ι, read off the invariant

`IotaRule` (`IxC/Kernel/Denotes.lean`) states a recursor rule's computation rule over
`Denotes`, with value-level arguments that fit the recursor's and the constructor's
types. The invariant states the same rule as `RecRuleLaw` (`Model/Annot/Laws.lean`),
over readings: annotated terms whose interpretation is the value. This module turns the
second into the first, for every rule the invariant covers.

The values become readings as bound variables: an environment `ρ'` holds the
recursor's arguments followed by the constructor's, and the readings are `bvar i`.

* **The fits** (`fits_teleFitPA`): a value-level fit of a stored (closed) type is a
  reading-level fit of its reading (`TeleFitPA`) at the bound-variable readings. Each
  domain is identified through the bridge `Denotes_of_denoteMeta` at the domain's
  depth and `Denotes_functional`; the domains' grading descends the type's
  (`wellDenotedV_tower_slot`), using the memberships of the outer domains.
* **The index pin** (`IotaIndexPin`): the constructor's residual reading is a spine
  whose index arguments interpret to the recursor's indices, by the same bridge at the
  residual's depth.
* **Parameters and levels**: a canonical rule's recorded shape (`RuleCtorOk`,
  `Expr.recRulePlain`) makes the major premise's parameter arguments the recursor's
  parameter variables, and its levels the constructor's level parameters, which is what
  the rule's comparands name.
-/

namespace Ix.Kernel

universe w

section
variable {V : Type w} [SetTheory V]

/-- Pushing a value keeps an agreement below a bound, one index higher. -/
theorem push_agree {k : Nat} {ρ ρ' : BVarIdx → V} (h : ∀ i, i < k → ρ i = ρ' i) (x : V) :
    ∀ i, i < k + 1 → push x ρ i = push x ρ' i
  | 0, _ => rfl
  | i + 1, hi => h i (by omega)

/-- **A term's denotation reads the variable environment only below the term's
bound.** -/
theorem Denotes.congr_below {cval : Key md → (LevelParam → Nat) → V} {env : Env md}
    {φ : LevelParam → Nat} {ρ : BVarIdx → V} {e : Expr md} {v : V}
    (h : Denotes cval env φ ρ e v) :
    ∀ {k : Nat} {ρ' : BVarIdx → V}, e.looseBVarsBounded k = true →
      (∀ i, i < k → ρ i = ρ' i) → Denotes cval env φ ρ' e v := by
  induction h with
  | @bvar ρ i =>
    intro k ρ' hb hag
    have hi : i < k := by simpa [Expr.looseBVarsBounded] using hb
    rw [hag i hi]
    exact .bvar
  | sort => intro _ _ _ _; exact .sort
  | const hf hlen => intro _ _ _ _; exact .const hf hlen
  | app _ _ ihf iha =>
    intro k ρ' hb hag
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact .app (ihf hb.1 hag) (iha hb.2 hag)
  | lam _ _ hP ihA ihF =>
    intro k ρ' hb hag
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact .lam (ihA hb.1 hag) (fun x hx => ihF x hx hb.2 (push_agree hag x)) hP
  | pi _ _ hP ihA ihB =>
    intro k ρ' hb hag
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact .pi (ihA hb.1 hag) (fun x hx => ihB x hx hb.2 (push_agree hag x)) hP
  | proj_table ht _ ih =>
    intro k ρ' hb hag
    exact .proj_table ht (ih (by simpa [Expr.looseBVarsBounded] using hb) hag)
  | proj_fst ht _ ih =>
    intro k ρ' hb hag
    exact .proj_fst ht (ih (by simpa [Expr.looseBVarsBounded] using hb) hag)
  | proj_snd ht _ ih =>
    intro k ρ' hb hag
    exact .proj_snd ht (ih (by simpa [Expr.looseBVarsBounded] using hb) hag)
  | natLit _ ih =>
    intro k ρ' _ hag
    exact .natLit (ih (natLitToConstructor_looseBVars _) hag)
  | strLit _ ih =>
    intro k ρ' _ hag
    exact .strLit (ih (strLitToConstructor_looseBVars _ _) hag)

theorem DenotesList.length_eq {cval : Key md → (LevelParam → Nat) → V} {env : Env md}
    {φ : LevelParam → Nat} {ρ : BVarIdx → V} {es : List (Expr md)} {vs : List V}
    (h : DenotesList cval env φ ρ es vs) : es.length = vs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem DenotesList.getD {cval : Key md → (LevelParam → Nat) → V} {env : Env md}
    {φ : LevelParam → Nat} {ρ : BVarIdx → V} {es : List (Expr md)} {vs : List V}
    (h : DenotesList cval env φ ρ es vs) (de : Expr md) (dv : V) :
    ∀ i, i < es.length → Denotes cval env φ ρ (es.getD i de) (vs.getD i dv) := by
  induction h with
  | nil => intro i hi; exact absurd hi (by simp)
  | cons hd _ ih =>
    intro i hi
    cases i with
    | zero => simpa using hd
    | succ i => simpa using ih i (by simp at hi; omega)

/-- The variable environment after binding `xs` in order (the last one innermost), as a
fit leaves it. -/
def pushVals (ρ : BVarIdx → V) : List V → BVarIdx → V
  | [] => ρ
  | x :: xs => pushVals (push x ρ) xs

theorem pushVals_ge : ∀ (xs : List V) (ρ : BVarIdx → V) (i : Nat), xs.length ≤ i →
    pushVals ρ xs i = ρ (i - xs.length)
  | [], ρ, i, _ => by simp [pushVals]
  | x :: xs, ρ, i, h => by
    simp only [List.length_cons] at h
    show pushVals (push x ρ) xs i = ρ (i - (xs.length + 1))
    rw [pushVals_ge xs _ i (by omega)]
    obtain ⟨j, hj⟩ : ∃ j, i - xs.length = j + 1 := ⟨i - xs.length - 1, by omega⟩
    rw [hj, show i - (xs.length + 1) = j by omega]
    rfl

theorem pushVals_lt : ∀ (xs : List V) (ρ : BVarIdx → V) (i : Nat) (d : V), i < xs.length →
    pushVals ρ xs i = xs.getD (xs.length - 1 - i) d
  | [], _, _, _, h => absurd h (by simp)
  | x :: xs, ρ, i, d, h => by
    simp only [List.length_cons] at h
    show pushVals (push x ρ) xs i = (x :: xs).getD (xs.length + 1 - 1 - i) d
    by_cases hi : i < xs.length
    · rw [pushVals_lt xs _ i d hi, show xs.length + 1 - 1 - i = (xs.length - 1 - i) + 1 by omega,
        List.getD_cons_succ]
    · rw [pushVals_ge xs _ i (by omega), show i - xs.length = 0 by omega,
        show xs.length + 1 - 1 - i = 0 by omega]
      rfl

/-- A fit extends by one more member of the next domain. -/
theorem Fits.snoc {cval : Key md → (LevelParam → Nat) → V} {env : Env md}
    {φ : LevelParam → Nat} {ρ σ : BVarIdx → V} {T R : Expr md} {xs : List V}
    (h : Fits cval env φ ρ T xs σ R) :
    ∀ {A B : Expr md} {m : BinderMeta} {X x : V}, R = .forallE A B m →
      Denotes cval env φ σ A X → x ∈ˢ X → Fits cval env φ ρ T (xs ++ [x]) (push x σ) B := by
  induction h with
  | nil =>
    intro A B m X x hR hA hx
    subst hR
    exact .cons hA hx .nil
  | cons hA' hx' _ ih =>
    intro A B m X x hR hA hx
    exact .cons hA' hx' (ih hR hA hx)

/-- **A fit, decomposed**: the telescope it walks, the environment it leaves, the
residual's bounds, and at each step the domain's denotation holding the member. -/
theorem Fits.strip {cval : Key md → (LevelParam → Nat) → V} {env : Env md}
    {φ : LevelParam → Nat} {ρ σ : BVarIdx → V} {T R : Expr md} {xs : List V}
    (h : Fits cval env φ ρ T xs σ R) :
    ∀ {j : Nat}, T.looseBVarsBounded j = true → T.hasFvar = false →
    ∃ bs, T.stripPis xs.length = some (bs, R) ∧ σ = pushVals ρ xs ∧
      R.looseBVarsBounded (j + xs.length) = true ∧ R.hasFvar = false ∧
      ∀ n, n < xs.length → ∃ (b : Expr md × BinderMeta) (X : V), bs[n]? = some b ∧
        b.1.looseBVarsBounded (j + n) = true ∧ b.1.hasFvar = false ∧
        Denotes cval env φ (pushVals ρ (xs.take n)) b.1 X ∧
        xs.getD n SetTheory.empty ∈ˢ X := by
  induction h with
  | @nil ρ T =>
    intro j hb hf
    exact ⟨[], rfl, rfl, by simpa using hb, hf, fun n hn => absurd hn (by simp)⟩
  | @cons ρ ρ' A B R m X x xs hA hx _ ih =>
    intro j hb hf
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    obtain ⟨bs, hs, hσ, hRb, hRf, hsteps⟩ := ih hb.2 hf.2
    refine ⟨(A, m) :: bs, ?_, hσ, ?_, hRf, ?_⟩
    · simp [Expr.stripPis, hs]
    · rw [List.length_cons, show j + (xs.length + 1) = j + 1 + xs.length by omega]
      exact hRb
    · intro n hn
      cases n with
      | zero => exact ⟨(A, m), X, rfl, by simpa using hb.1, hf.1, hA, hx⟩
      | succ n =>
        obtain ⟨b, X', hb', hbb, hbf, hd, hm⟩ := hsteps n (by simp at hn; omega)
        exact ⟨b, X', by simpa using hb',
          by rw [show j + (n + 1) = j + 1 + n by omega]; exact hbb, hbf, hd,
          by simpa using hm⟩

end

/-- Opening a body's `n` outer variables at depth `d` and closing at depth `d + n` is
closing the body at depth `d`, `n` binders in. -/
theorem closeN_instSeq_openFvars : ∀ (n d : Nat) (b : Expr md),
    b.looseBVarsBounded n = true → Expr.fvarsBelow d b →
    Expr.closeN (d + n) (Expr.instSeq (Verify.openFvars d n) (n - 1) b) 0 =
      Expr.closeN d b n
  | 0, _, _, _, _ => rfl
  | n + 1, d, b, hb, hf => by
    show Expr.closeN (d + (n + 1)) (Expr.instSeq (Verify.openFvars (d + 1) n) (n - 1)
      (b.instantiate1 (.fvar d (.sort .zero)) n)) 0 = _
    rw [show d + (n + 1) = d + 1 + n by omega,
      closeN_instSeq_openFvars n (d + 1) _ (looseBVarsBounded_instantiate1 b n hb)
        (Expr.fvarsBelow_instantiate1 n hf),
      Expr.closeN_instantiate1 b n hb hf]

/-- The opened body is scoped below its depth and has no loose variable. -/
theorem instSeq_openFvars_scoped : ∀ (n d : Nat) (b : Expr md),
    b.looseBVarsBounded n = true → Expr.fvarsBelow d b →
    Expr.fvarsBelow (d + n) (Expr.instSeq (Verify.openFvars d n) (n - 1) b) ∧
      (Expr.instSeq (Verify.openFvars d n) (n - 1) b).looseBVarsBounded 0 = true
  | 0, _, _, hb, hf => ⟨hf, hb⟩
  | n + 1, d, b, hb, hf => by
    show Expr.fvarsBelow (d + (n + 1)) (Expr.instSeq (Verify.openFvars (d + 1) n) (n - 1)
        (b.instantiate1 (.fvar d (.sort .zero)) n)) ∧
      (Expr.instSeq (Verify.openFvars (d + 1) n) (n - 1)
        (b.instantiate1 (.fvar d (.sort .zero)) n)).looseBVarsBounded 0 = true
    rw [show d + (n + 1) = d + 1 + n by omega]
    exact instSeq_openFvars_scoped n (d + 1) _ (looseBVarsBounded_instantiate1 b n hb)
      (Expr.fvarsBelow_instantiate1 n hf)

theorem fvarsBelow_zero_of_hasFvar_false : ∀ {e : Expr md}, e.hasFvar = false →
    Expr.fvarsBelow 0 e := by
  intro e
  induction e <;> simp_all [Expr.fvarsBelow, Expr.hasFvar]

end Ix.Kernel

namespace Ix.Kernel.Model

open Ix.Kernel.Semantics Ix.Kernel.SetModel Ix.Kernel.Verify SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel.Term
open Ix.Kernel (Env Expr Key Level ConstantInfo ConstantVal RecRule Denotes Fits
  DenotesList pushVals pushVals_lt pushVals_ge)

universe w

variable {V : Type w} [SetTheory V]

/-- A read spine's head and arguments are graded where the spine is. -/
theorem wellDenotedV_mkAppN_parts {ρ : Nat → V} :
    ∀ (as : List AnnotTerm) (f : AnnotTerm), WellDenotedV V ρ (AnnotTerm.mkAppN f as) →
      WellDenotedV V ρ f ∧ ∀ a ∈ as, WellDenotedV V ρ a
  | [], _, h => ⟨h, fun _ ha => nomatch ha⟩
  | b :: bs, f, h => by
    rw [AnnotTerm.mkAppN_cons] at h
    obtain ⟨hfb, hbs⟩ := wellDenotedV_mkAppN_parts bs (.app f b) h
    obtain ⟨h1, h2⟩ := hfb
    rw [WellDenoted_app] at h1
    rw [AnnotValid_app] at h2
    refine ⟨⟨h1.1, h2.1⟩, fun a ha => ?_⟩
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨h1.2.1, h2.2⟩
    · exact hbs a ha

theorem chain_take_lt {ρ : Nat → V} {ws : List AnnotTerm} {n i : Nat} (hn : n ≤ ws.length)
    (hi : i < n) :
    chain V ρ (ws.take n) i = interp V ρ (ws.getD (n - 1 - i) default) := by
  have hlen : (ws.take n).length = n := by rw [List.length_take]; omega
  rw [chain_lt (by rw [hlen]; exact hi), hlen]
  simp only [List.getD]
  rw [List.getElem?_take_of_lt (by omega)]

/-- **A value-level fit is a reading-level fit at readings of the values.** At a closed
type whose reading is graded everywhere, values that fit the type (`Fits`) have, at any
readings interpreting to them, the reading-level fit `TeleFitPA`; the residual's reading
is graded at the readings' chain, and the fit's environment agrees with that chain
below the telescope. -/
theorem fits_teleFitPA {acval : Key md → (LevelParam → Nat) → AnnotTerm}
    (hcl : ∀ n ψ, Term.Closed (acval n ψ).erase) {env : Env md} {φ : LevelParam → Nat}
    {T : Expr md} {TA : AnnotTerm}
    (hTf : T.hasFvar = false) (hTb : T.looseBVarsBounded 0 = true)
    (hT : denoteMeta acval env φ 0 T = some TA) (hTok : ∀ ρ : Nat → V, WellDenotedV V ρ TA)
    {ρ σ : Nat → V} {vs : List V} {R : Expr md}
    (hfit : Fits (cvalOf acval) env φ ρ T vs σ R)
    {ρ' : Nat → V} {ws : List AnnotTerm} (hlen : ws.length = vs.length)
    (hval : ∀ n, n < vs.length →
      interp V ρ' (ws.getD n default) = vs.getD n SetTheory.empty) :
    ∃ (bs : List (Expr md × BinderMeta)) (Γ : List AnnotTerm) (C : AnnotTerm),
      T.stripPis vs.length = some (bs, R) ∧ PiTeleAV vs.length TA Γ C ∧
      denoteMeta acval env φ vs.length
        (Expr.instSeq (openFvars 0 vs.length) (vs.length - 1) R) = some C ∧
      TeleFitPA V ρ' TA ws (Ix.Kernel.Model.AnnotTerm.instSeq ws (vs.length - 1) C) ∧
      WellDenotedV V (chain V ρ' ws) C ∧
      (∀ i, i < vs.length → σ i = chain V ρ' ws i) ∧
      R.looseBVarsBounded vs.length = true ∧ R.hasFvar = false := by
  obtain ⟨bs, hstrip, hσ, hRb, hRf, hsteps⟩ := hfit.strip (j := 0) hTb hTf
  rw [Nat.zero_add] at hRb
  obtain ⟨Γ, C, htower, hΓlen, hC, hdoms⟩ :=
    stripPis_denotePTele (acval := acval) (env := env) (φ := φ) vs.length hstrip hT
  rw [Nat.zero_add] at hC
  -- the fit's environments agree with the readings' chains below the telescope
  have hagree : ∀ n, n ≤ vs.length → ∀ i, i < n →
      pushVals ρ (vs.take n) i = chain V ρ' (ws.take n) i := by
    intro n hn i hi
    have htl : (vs.take n).length = n := by rw [List.length_take]; omega
    rw [pushVals_lt _ _ i SetTheory.empty (by rw [htl]; exact hi), htl,
      chain_take_lt (by omega) hi, hval (n - 1 - i) (by omega)]
    simp only [List.getD]
    rw [List.getElem?_take_of_lt (by omega)]
  -- the memberships, outermost first
  have hmem : ∀ n, n < vs.length →
      interp V ρ' (ws.getD n default)
        ∈ˢ interp V (chain V ρ' (ws.take n)) (Γ.getD (vs.length - 1 - n) default) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      obtain ⟨b, X, hb, hbB, hbF, hX, hx⟩ := hsteps n hn
      rw [Nat.zero_add] at hbB
      -- the domain's grading, from the type's and the outer memberships
      have hgr : WellDenotedV V (chain V ρ' (ws.take n)) (Γ.getD (vs.length - 1 - n) default) := by
        have h := wellDenotedV_tower_slot vs.length htower (ρ' := chain V ρ' ws)
          (hTok _) (vs.length - 1 - n) (by omega) (fun q hpq hqk => by
            have hq := ih (vs.length - 1 - q) (by omega) (by omega)
            rw [chain_lt (by rw [hlen]; exact hqk), hlen,
              chain_tail (by rw [hlen]; exact hqk), hlen]
            rw [show vs.length - 1 - (vs.length - 1 - q) = q by omega] at hq
            exact hq)
        rwa [chain_tail (by rw [hlen]; omega), hlen,
          show vs.length - 1 - (vs.length - 1 - n) = n by omega] at h
      -- the bridge at the domain's depth
      have hden := hdoms n b hb
      rw [Nat.zero_add] at hden
      obtain ⟨hfb, hlb0⟩ := Ix.Kernel.instSeq_openFvars_scoped n 0 b.1 hbB
        (Ix.Kernel.fvarsBelow_zero_of_hasFvar_false hbF)
      have hbr := Denotes_of_denoteMeta (V := V) hcl n _ hden (by simpa using hfb) hlb0
        (chain V ρ' (ws.take n)) hgr
      rw [show Expr.closeN n (Expr.instSeq (openFvars 0 n) (n - 1) b.1) 0 = b.1 by
        have h := Ix.Kernel.closeN_instSeq_openFvars n 0 b.1 hbB
          (Ix.Kernel.fvarsBelow_zero_of_hasFvar_false hbF)
        rw [Nat.zero_add] at h
        rw [h, Expr.closeN_of_hasFvar _ 0 n hbF]] at hbr
      have hX' := hX.congr_below hbB (hagree n (by omega))
      rw [hval n hn, Denotes_functional hbr hX']
      exact hx
  refine ⟨bs, Γ, C, hstrip, htower, hC,
    teleFitPA_of_tower vs.length htower hlen hmem, ?_, ?_, hRb, hRf⟩
  · exact wellDenotedV_tower_body_sat htower (hTok _) (sat_of_tower htower hlen hmem)
  · intro i hi
    have h := hagree vs.length (Nat.le_refl _) i hi
    rw [List.take_of_length_le (Nat.le_refl _),
      List.take_of_length_le (by omega : ws.length ≤ vs.length)] at h
    rw [hσ]
    exact h

/-! ## The canonical rules -/

/-- A list is the range of an environment that holds it from offset `c`. -/
theorem map_range_eq_of_getD {ρ' : Nat → V} {c : Nat} (l : List V)
    (h : ∀ j, j < l.length → ρ' (c + j) = l.getD j SetTheory.empty) :
    (List.range l.length).map (fun j => ρ' (c + j)) = l := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  rw [List.getElem_map, List.getElem_range, h j h2]
  simp [List.getD, List.getElem?_eq_getElem h2]

theorem hasFvar_getAppArgs_false : ∀ {e : Expr md}, e.hasFvar = false →
    ∀ x ∈ e.getAppArgs, x.hasFvar = false := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro h x hx
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact ihf h.1 x hx
    · exact h.2
  | _ => intro _ x hx; simp [Expr.getAppArgs] at hx

/-- **The computation rule of a canonical recursor rule**, from the invariant: its
fired law (`RecRuleLaw`) at bound-variable readings, with the recorded canonical shape
(`RuleCtorOk`) supplying the parameter agreement and the level link. -/
theorem iotaRule_plain {μ : Ix.Kernel.CheckMode} {env : Env md} (m : EnvModelM V μ env)
    {r : Key md} {cv : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)}
    {rl : RecRule md} (hf : env.find? r = some (.recInfo cv mI rP rules)) (hrl : rl ∈ rules)
    (hplain : RecRule.fire rl = .plain) :
    Ix.Kernel.IotaRule (cvalOf (V := V) m.base2.acval) env r cv mI rP rl := by
  intro cvC nP nF hC us φ ρ σ σC xs ys dom body RC mb D ls R K H X hus hxs hys hR hfitR
    hdomFn hX hK hfitC hmaj hpar hidx hH
  have hcl := m.base2.cval_closedL
  -- the rule's constructor, as the store records it
  obtain ⟨⟨cvj, hfj, hplainShape, -⟩, -, -⟩ := m.base2.rec_ctors r cv mI rP rules hf rl hrl
  rw [hC] at hfj
  obtain ⟨rfl, hnP, hnF⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hfj)
  subst hnP hnF
  have hfire : RecRule.fire rl ≠ .inert := by rw [hplain]; exact fun h => nomatch h
  obtain ⟨hrPmI, hlawU⟩ := m.rec_rules φ r cv mI rP rules hf rl hrl hfire
  obtain ⟨Ra, hRa, hRaok, -, hmain⟩ := hlawU us hus
  -- the constants' values
  have hRv : R = cvalOf m.base2.acval r (Level.substFn φ cv.levelParams us) := by
    cases hR with
    | const hfr _ => rw [hf] at hfr; cases hfr; rfl
  obtain ⟨hlsLen, hKv⟩ : ls.length = cvj.levelParams.length ∧
      K = cvalOf m.base2.acval rl.ctor (Level.substFn φ cvj.levelParams ls) := by
    cases hK with
    | const hfk hlen => rw [hC] at hfk; cases hfk; exact ⟨hlen, rfl⟩
  -- the stored types and the right-hand side are closed
  have hwfR := m.base2.wf _ (Ix.Kernel.Semantics.Env.find?_mem hf)
  have hwfC := m.base2.wf _ (Ix.Kernel.Semantics.Env.find?_mem hC)
  obtain ⟨hrhsF, -, -, hrhsB, -⟩ := hwfR.2.2.2.2.2.1 cv mI rP rules rfl rl hrl
  have hTf : (cv.type.instantiateLevelParams cv.levelParams us).hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]; exact hwfR.1
  have hTb : (cv.type.instantiateLevelParams cv.levelParams us).looseBVarsBounded 0 = true := by
    rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hwfR.2.2.2.1
  have hTCf : (cvj.type.instantiateLevelParams cvj.levelParams ls).hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]; exact hwfC.1
  have hTCb : (cvj.type.instantiateLevelParams cvj.levelParams ls).looseBVarsBounded 0 = true := by
    rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hwfC.2.2.2.1
  obtain ⟨TVa, hTVa, hTVaok, -⟩ := m.constType (φ := φ) 0 r _ us hf rfl hus
  obtain ⟨TVja, hTVja, hTVjaok, -⟩ := m.constType (φ := φ) 0 rl.ctor _ ls hC rfl hlsLen
  -- the arguments as bound-variable readings
  let ρ' : Nat → V := fun i => (xs ++ ys).getD i SetTheory.empty
  let xsA : List AnnotTerm := (List.range mI).map AnnotTerm.bvar
  let ysA : List AnnotTerm :=
    (List.range (rl.ctorParams + rl.nfields)).map (fun j => AnnotTerm.bvar (mI + j))
  have hρx : ∀ j, j < mI → ρ' j = xs.getD j SetTheory.empty := by
    intro j hj
    show (xs ++ ys).getD j _ = _
    simp only [List.getD, List.getElem?_append_left (by omega : j < xs.length)]
  have hρy : ∀ j, j < rl.ctorParams + rl.nfields →
      ρ' (mI + j) = ys.getD j SetTheory.empty := by
    intro j hj
    show (xs ++ ys).getD (mI + j) _ = _
    simp only [List.getD, List.getElem?_append_right (by omega : xs.length ≤ mI + j), hxs,
      Nat.add_sub_cancel_left]
  have hxsA_len : xsA.length = mI := by simp [xsA]
  have hysA_len : ysA.length = ys.length := by simp [ysA, hys]
  have hxsA_val : ∀ n, n < mI →
      interp V ρ' (xsA.getD n default) = xs.getD n SetTheory.empty := by
    intro n hn
    rw [show xsA.getD n default = AnnotTerm.bvar n by
      simp [xsA, List.getD, List.getElem?_range hn], interp_bvar]
    exact hρx n hn
  have hysA_val : ∀ n, n < ys.length →
      interp V ρ' (ysA.getD n default) = ys.getD n SetTheory.empty := by
    intro n hn
    rw [hys] at hn
    rw [show ysA.getD n default = AnnotTerm.bvar (mI + n) by
      simp [ysA, List.getD, List.getElem?_range hn], interp_bvar]
    exact hρy n hn
  have hxsMap : xsA.map (interp V ρ') = xs := by
    have h := map_range_eq_of_getD (ρ' := ρ') (c := 0) xs
      (fun j hj => by rw [Nat.zero_add]; exact hρx j (by omega))
    rw [hxs] at h
    rw [← h]
    simp [xsA, Function.comp_def]
  have hysMap : ysA.map (interp V ρ') = ys := by
    have h := map_range_eq_of_getD (ρ' := ρ') (c := mI) ys
      (fun j hj => hρy j (by omega))
    rw [hys] at h
    rw [← h]
    simp [ysA, Function.comp_def]
  -- the major premise
  let majA := AnnotTerm.mkAppN (m.base2.acval (RecRule.ctor rl)
    (Level.substFn φ cvj.levelParams ls)) ysA
  have hmajv : interp V ρ' majA = ys.foldl app K := by
    show interp V ρ' (AnnotTerm.mkAppN _ ysA) = _
    rw [interp_mkAppN, interp_cvalOf hcl, ← hKv]
    conv => rhs; rw [← hysMap]
    rw [List.foldl_map]
  -- the two fits, at the readings
  have hfitR' := hfitR.snoc rfl hX hmaj
  have hvalR : ∀ n, n < (xs ++ [ys.foldl app K]).length →
      interp V ρ' ((xsA ++ [majA]).getD n default)
        = (xs ++ [ys.foldl app K]).getD n SetTheory.empty := by
    intro n hn
    simp only [List.length_append, List.length_singleton] at hn
    by_cases hlt : n < mI
    · simp only [List.getD, List.getElem?_append_left (by omega : n < xsA.length),
        List.getElem?_append_left (by omega : n < xs.length)]
      have := hxsA_val n hlt
      simpa only [List.getD] using this
    · obtain rfl : n = mI := by omega
      simp only [List.getD, List.getElem?_append_right (by omega : xsA.length ≤ mI),
        List.getElem?_append_right (by omega : xs.length ≤ mI), hxsA_len, hxs, Nat.sub_self]
      simpa using hmajv
  obtain ⟨-, -, -, -, -, -, hteleR, -, -, -, -⟩ :=
    fits_teleFitPA (V := V) hcl hTf hTb hTVa hTVaok hfitR'
      (by simp [xsA, hxs]) hvalR
  obtain ⟨-, -, CC, -, -, hCC, hteleC, hCCok, hσC, hRCb, hRCf⟩ :=
    fits_teleFitPA (V := V) hcl hTCf hTCb hTVja hTVjaok hfitC hysA_len hysA_val
  -- the canonical shape: the major premise's levels and parameters
  obtain ⟨bsR, hstripR, hσ, -, -, -⟩ := hfitR.strip (j := 0) hTb hTf
  obtain ⟨pre0, dom0, body0, bm0, D0, hs0, hfn0, hargs0⟩ :=
    recRulePlain_shapeT (hplainShape hplain)
  rw [hxs] at hstripR
  obtain ⟨hbodyEq, -⟩ :=
    Expr.stripPis_instantiateLevelParams_eq cv.levelParams us mI hs0 hstripR
  simp only [Expr.instantiateLevelParams] at hbodyEq
  obtain ⟨hdomEq, -, -⟩ := Expr.forallE.inj hbodyEq
  have hls : ls = cvj.levelParams.map fun p => Level.subst cv.levelParams us (.param p) := by
    have h := hdomFn
    rw [hdomEq, Expr.getAppFn_instantiateLevelParams, hfn0] at h
    simp only [Expr.instantiateLevelParams, List.map_map] at h
    obtain ⟨-, h2⟩ := Expr.const.inj h
    rw [← h2]
    rfl
  have hargs : dom.getAppArgs.take rl.ctorParams =
      (List.range rl.ctorParams).map (fun k => Expr.bvar (mI - 1 - k)) := by
    rw [hdomEq, Expr.getAppArgs_instantiateLevelParams, ← List.map_take, hargs0]
    simp [Function.comp_def, Expr.instantiateLevelParams]
  have hparams : ∀ i, i < rl.ctorParams → i < mI →
      ys.getD i SetTheory.empty = xs.getD i SetTheory.empty := by
    intro i hi him
    have hd := hpar.getD (Expr.bvar 0) SetTheory.empty i (by rw [hargs]; simpa using hi)
    rw [show (dom.getAppArgs.take rl.ctorParams).getD i (Expr.bvar 0)
        = Expr.bvar (mI - 1 - i) by
      rw [hargs]; simp [List.getD, List.getElem?_range hi]] at hd
    have hv := Ix.Kernel.Denotes_functional hd
      (Ix.Kernel.Denotes.bvar (cval := cvalOf m.base2.acval) (env := env) (φ := φ))
    rw [hσ, pushVals_lt xs ρ (mI - 1 - i) SetTheory.empty (by omega), hxs,
      show mI - 1 - (mI - 1 - i) = i by omega] at hv
    rw [← hv]
    simp only [List.getD, List.getElem?_take_of_lt hi]
  -- the index pin: the constructor's residual is the family at its indices
  have hpin : IotaIndexPin (V := V) ρ'
      (Ix.Kernel.Model.AnnotTerm.instSeq ysA (ys.length - 1) CC)
      (RecRule.ctorParams rl) mI rP xsA := by
    have hRCeq := Expr.mkAppN_getApp RC
    rw [← hRCeq, Expr.instSeq_mkAppN] at hCC
    obtain ⟨fa, vs', -, hsp, rfl⟩ := denoteMeta_mkAppN_inv hCC
    have hl1 := hidx.length_eq
    have hl2 := hsp.length
    simp only [List.length_drop, List.length_map, hxs] at hl1 hl2
    refine ⟨_, vs'.map (Ix.Kernel.Model.AnnotTerm.instSeq ysA (ys.length - 1)),
      instSeqAV_mkAppN _ _ _ _, ?_, ?_⟩
    · rw [List.length_map]; omega
    · intro i hi
      have hargLen : rl.ctorParams + i < RC.getAppArgs.length := by omega
      obtain ⟨a, ha⟩ : ∃ a, RC.getAppArgs[rl.ctorParams + i]? = some a :=
        ⟨_, List.getElem?_eq_getElem hargLen⟩
      have hamem : a ∈ RC.getAppArgs := List.mem_of_getElem? ha
      have hab : a.looseBVarsBounded ys.length = true :=
        Expr.looseBVarsBounded_getAppArgs hRCb a hamem
      have haf : a.hasFvar = false := hasFvar_getAppArgs_false hRCf a hamem
      -- the argument's reading
      have hread := hsp.getD (Expr.bvar 0) (rl.ctorParams + i) (by simpa using hargLen)
      simp only [List.getD, List.getElem?_map, ha, Option.map_some, Option.getD_some] at hread
      obtain ⟨va, hva⟩ : ∃ va, vs'[rl.ctorParams + i]? = some va :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      rw [hva, Option.getD_some] at hread
      have hvamem : va ∈ vs' := List.mem_of_getElem? hva
      have hgr := (wellDenotedV_mkAppN_parts vs' fa hCCok).2 va hvamem
      obtain ⟨hfb, hlb0⟩ := Ix.Kernel.instSeq_openFvars_scoped ys.length 0 a hab
        (Ix.Kernel.fvarsBelow_zero_of_hasFvar_false haf)
      have hbr := Denotes_of_denoteMeta (V := V) hcl ys.length _ hread (by simpa using hfb)
        hlb0 (chain V ρ' ysA) hgr
      rw [show Expr.closeN ys.length (Expr.instSeq (openFvars 0 ys.length) (ys.length - 1) a) 0
          = a by
        have h := Ix.Kernel.closeN_instSeq_openFvars ys.length 0 a hab
          (Ix.Kernel.fvarsBelow_zero_of_hasFvar_false haf)
        rw [Nat.zero_add] at h
        rw [h, Expr.closeN_of_hasFvar _ 0 _ haf]] at hbr
      have hdi := hidx.getD (Expr.bvar 0) SetTheory.empty i (by simp; omega)
      simp only [List.getD, List.getElem?_drop, ha, Option.getD_some] at hdi
      have hdi' := hdi.congr_below hab hσC
      have heq := Ix.Kernel.Denotes_functional hbr hdi'
      simp only [List.getD, List.getElem?_map, hva, Option.map_some, Option.getD_some]
      rw [show (Ix.Kernel.Model.AnnotTerm.instSeq ysA (ys.length - 1) va)
          = Ix.Kernel.Model.AnnotTerm.instSeq ysA (ysA.length - 1) va by rw [hysA_len],
        interp_instSeq, heq]
      have := hxsA_val (rP + i) (by omega)
      simp only [List.getD] at this
      rw [this]
  -- the fired law
  have hlev : Level.substFn φ cvj.levelParams ls = Level.substFn φ cvj.levelParams
      (Ix.Kernel.recFireComparands rl cv.levelParams us cvj.levelParams [] rP).1 := by
    rw [Ix.Kernel.recFireComparands_plain hplain, hls]
  have hlawEq := (hmain cvj rl.ctorParams rl.nfields hC ls ρ' xsA ysA TVa TVja _ _
    hxsA_len (by rw [hysA_len, hys]) hlsLen hlev
    (fun _ _ i hi him => by
      rw [hysA_val i (by omega), hxsA_val i him]
      exact hparams i hi him)
    (fun lvls pins h => by rw [hplain] at h; exact nomatch h)
    hpin hTVa hTVja hteleR hteleC).1
  -- the right-hand side's value
  have hHv : H = interp V ρ' Ra := by
    have hnf : (rl.rhs.instantiateLevelParams cv.levelParams us).hasFvar = false := by
      rw [Expr.hasFvar_instantiateLevelParams]; exact hrhsF
    have hlb : (rl.rhs.instantiateLevelParams cv.levelParams us).looseBVarsBounded 0 = true := by
      rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hrhsB
    have hbr := Denotes_of_denoteMeta (V := V) hcl 0 _ hRa
      (Ix.Kernel.fvarsBelow_zero_of_hasFvar_false hnf) hlb ρ' (hRaok ρ')
    rw [Expr.closeN_of_hasFvar _ 0 0 hnf] at hbr
    exact Ix.Kernel.Denotes_functional (hH.congr_below hlb (fun i hi => absurd hi (by omega))) hbr
  calc (xs ++ [ys.foldl app K]).foldl app R
      = ((xsA ++ [majA]).map (interp V ρ')).foldl app
          (interp V ρ' (m.base2.acval r (Level.substFn φ cv.levelParams us))) := by
        rw [List.map_append, hxsMap, List.map_singleton, hmajv, interp_cvalOf hcl, hRv]
    _ = interp V ρ' (AnnotTerm.mkAppN
          (m.base2.acval r (Level.substFn φ cv.levelParams us)) (xsA ++ [majA])) := by
        rw [interp_mkAppN, List.foldl_map]
    _ = interp V ρ' (AnnotTerm.mkAppN Ra (xsA.take rP ++ ysA.drop rl.ctorParams)) := hlawEq
    _ = ((xsA.take rP ++ ysA.drop rl.ctorParams).map (interp V ρ')).foldl app
          (interp V ρ' Ra) := by
        rw [interp_mkAppN, List.foldl_map]
    _ = (xs.take rP ++ ys.drop rl.ctorParams).foldl app H := by
        rw [List.map_append, List.map_take, List.map_drop, hxsMap, hysMap, hHv]

end Ix.Kernel.Model
