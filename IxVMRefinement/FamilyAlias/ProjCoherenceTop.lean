import IxVMRefinement.FamilyAlias.ProjCoherenceMain
import IxC.Kernel.Model.JudgeRules

/-! # Top-level coherence theorems for modeled structure projections

Completes the set-model coherence proof for modeled structure projections:

* **Section 10**: `mbodyUnpackSpec`, `bodyUnpackSpec`, and `projPure_coherence` (handling both the
  squash regime `pwBit ψ_P fp.sbm.pw = 0` via `wp.hsort_poly` and the positive regime via
  `auxRec_fire`, `.direct`/`.viaDefn`, and `.bvar`/`.unpack` + `unpack_eval_induction`);
* **Section 11**: `field_chain_coherence`, unifying all three branches of `FieldProjFacts.hpure`
  (`nP = 0 ∧ bnl = 0`, unconditionally `Prop`, and `ProjPureWitness`) into a single closed,
  `ψ 0`-only, `WellDenotedV` chain term `A_chain` inhabiting `univ (ψ 0 + 1)` whose `chainApp`
  equals `proj_i`. -/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing.FamilyAlias

open IxVM.Refinement.Core
open IxVM.Consistency (lastBinderDom)
open IxVM.Refinement.Decl (ExprSemEq)
open IxVM.Refinement.KernelLevels (substLevel)
open Ix.Kernel (Expr Level ConstantInfo ConstantVal RecRule LevelParam BinderMeta Key Env SetTheory)
open Ix.Kernel.Semantics
open Ix.Kernel.SetTheory
open Ix.Kernel.SetTheory.Tower
open Ix.Kernel.SetModel
open Ix.Kernel.Model

private theorem map_getElem_eq {α β : Type _} {f : α → Nat} {g : β → Nat} {l1 : List α} {l2 : List β}
    (h : l1.map f = l2.map g) (i : Nat) (hi1 : i < l1.length) (hi2 : i < l2.length) :
    f l1[i] = g l2[i] := by
  have hget := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2,
    Option.map_some, Option.some.injEq] at hget
  exact hget

/-! ## Section 10: `bodyUnpackSpec`, sort-polymorphic telescope helpers, and `projPure_coherence` -/

/-- Unpack specification extracted deterministically from a `ProjMinorWitness` body `mbody`. -/
noncomputable def mbodyUnpackSpec {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {env : Env .anon}
    {auxKey auxRecKey : KKey} {auxRecLps : List LevelParam}
    {arules : List (RecRule .anon)} {auxCtorKeyAt : Nat → KKey}
    {nP bnl anc : Nat} (mbody : KExpr) : Ix.Kernel.Term.UnpackSpec :=
  open Classical in
  if h : Nonempty (UnpackSpecMatch t E env auxKey auxRecKey auxRecLps arules auxCtorKeyAt nP bnl anc mbody) then
    unpackSpecOf (Classical.choice h).hminors
  else []

theorem mbodyUnpackSpec_eq_minorUnpackSpec {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {env : Env .anon}
    {auxKey auxRecKey : KKey} {auxRecLps : List LevelParam}
    {arules : List (RecRule .anon)} {auxCtorKeyAt : Nat → KKey} {sbmPw : Ix.Kernel.PropWhen}
    {nP bnl anc nF nIhJ fidx : Nat} {mbody : KExpr}
    (hm : ProjMinorWitness t E env auxKey auxRecKey auxRecLps arules auxCtorKeyAt sbmPw nP bnl anc nF
      nIhJ fidx mbody) :
    mbodyUnpackSpec (t := t) (E := E) (env := env) (auxKey := auxKey) (auxRecKey := auxRecKey)
      (auxRecLps := auxRecLps) (arules := arules) (auxCtorKeyAt := auxCtorKeyAt)
      (nP := nP) (bnl := bnl) (anc := anc) mbody = minorUnpackSpec hm := rfl

/-- Deterministic `UnpackSpec` for a `ProjPureBodyWitness`, extracted from `pvalPos` and `arules[jIdx]`. -/
noncomputable def bodyUnpackSpec {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {env : Env .anon}
    {auxKey tagCKey auxRecKey : KKey} {auxRecLps : List LevelParam}
    {arules : List (RecRule .anon)} {auxCtorKeyAt : Nat → KKey} {sbmPw : Ix.Kernel.PropWhen}
    {nP bnl anc nF fidx jIdx : Nat} {pvalPos : KExpr}
    (_hb : ProjPureBodyWitness t E env auxKey tagCKey auxRecKey auxRecLps arules auxCtorKeyAt
      sbmPw nP bnl anc nF fidx jIdx pvalPos) : Ix.Kernel.Term.UnpackSpec :=
  match pvalPos.stripLams (nP + 1), arules[jIdx]? with
  | some (_, pbody), some rlJ =>
    match (Core.posOf auxRecLps rlJ.rhs).stripLams (nP + 1 + anc + nF) with
    | some (_, rbodyJ) =>
      let nIhJ := rbodyJ.getAppArgs.length - nF
      match pbody.getAppFn with
      | .const pheadKey _ =>
        let pargs := pbody.getAppArgs
        let minIdx :=
          match env.find? pheadKey with
          | some (.recInfo _ _ _ _) => nP + 1 + jIdx
          | _ => nP + (pargs.length - nP - (anc + 1)) + jIdx
        match (pargs.getD minIdx default).stripLams (nF + nIhJ) with
        | some (_, mbody) => mbodyUnpackSpec (t := t) (E := E) (env := env)
            (auxKey := auxKey) (auxRecKey := auxRecKey) (auxRecLps := auxRecLps)
            (arules := arules) (auxCtorKeyAt := auxCtorKeyAt) (nP := nP) (bnl := bnl)
            (anc := anc) mbody
        | none => []
      | _ => []
    | none => []
  | _, _ => []

private theorem getAppArgs_mkAppN_atom :
    ∀ {f : KExpr} (as : List KExpr), (∀ a b, f ≠ .app a b) →
      (Expr.mkAppN f as).getAppArgs = as
  | f, [], h => by
    cases f with
    | app _ _ => exact absurd rfl (h _ _)
    | _ => rfl
  | f, a :: as, h => by
    have hgo : ∀ (xs : List KExpr) (g : KExpr), (Expr.mkAppN g xs).getAppArgs = g.getAppArgs ++ xs := by
      intro xs
      induction xs with
      | nil => intro g; simp [Expr.mkAppN]
      | cons x xs ih =>
        intro g
        simp only [Expr.mkAppN, ih (.app g x), Expr.getAppArgs, List.append_assoc, List.singleton_append]
    rw [hgo (a :: as) f]
    have hnil : f.getAppArgs = [] := by
      cases f with
      | app _ _ => exact absurd rfl (h _ _)
      | _ => rfl
    rw [hnil, List.nil_append]

private theorem mbodyUnpackSpec_bvar {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {env : Env .anon}
    {auxKey auxRecKey : KKey} {auxRecLps : List LevelParam}
    {arules : List (RecRule .anon)} {auxCtorKeyAt : Nat → KKey}
    {nP bnl anc i : Nat} :
    mbodyUnpackSpec (t := t) (E := E) (env := env) (auxKey := auxKey) (auxRecKey := auxRecKey)
      (auxRecLps := auxRecLps) (arules := arules) (auxCtorKeyAt := auxCtorKeyAt)
      (nP := nP) (bnl := bnl) (anc := anc) (.bvar i) = [] := by
  have hne : ¬ Nonempty (UnpackSpecMatch t E env auxKey auxRecKey auxRecLps arules auxCtorKeyAt
      nP bnl anc (.bvar i)) := by
    rintro ⟨m⟩
    have hmb := m.hmbody
    cases hu : m.uargs using List.reverseRecOn with
    | nil => rw [hu] at hmb; simp [Expr.mkAppN] at hmb
    | append_singleton xs x =>
      rw [hu] at hmb
      have hgo : ∀ (f : KExpr) (ys : List KExpr) (y : KExpr),
          Expr.mkAppN f (ys ++ [y]) = .app (Expr.mkAppN f ys) y := by
        intro f ys
        induction ys generalizing f with
        | nil => intros; rfl
        | cons a ys ih => intro y; exact ih (.app f a) y
      rw [hgo] at hmb; exact nomatch hmb
  simp only [mbodyUnpackSpec, hne, ↓reduceDIte]

private theorem bodyUnpackSpec_direct {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {env : Env .anon}
    {auxKey tagCKey auxRecKey : KKey} {cvAuxRec : ConstantVal .anon} {auxRecLps : List LevelParam}
    {arules : List (RecRule .anon)} {auxCtorKeyAt : Nat → KKey} {sbmPw : Ix.Kernel.PropWhen}
    {nP bnl anc nF fidx jIdx : Nat} {pvalPos : KExpr}
    (hfindAuxRec : env.find? auxRecKey = some (.recInfo cvAuxRec (nP + 1 + anc + 1) (nP + 1 + anc) arules))
    {pbs pheadLvls pargs rbsJ rargsJ mbsJ mbody rlJ}
    (hp_strip : pvalPos.stripLams (nP + 1) = some (pbs, Expr.mkAppN (.const auxRecKey pheadLvls) pargs))
    (hrlJ : arules[jIdx]? = some rlJ)
    (hrlJ_strip : (Core.posOf auxRecLps rlJ.rhs).stripLams (nP + 1 + anc + nF) =
      some (rbsJ, Expr.mkAppN (.bvar (nF + anc - 1 - jIdx)) rargsJ))
    (hminJ_strip : (pargs.getD (nP + 1 + jIdx) default).stripLams (nF + (rargsJ.length - nF)) =
      some (mbsJ, mbody))
    (hminor : ProjMinorWitness t E env auxKey auxRecKey auxRecLps arules auxCtorKeyAt sbmPw nP bnl anc
      nF (rargsJ.length - nF) fidx mbody)
    (hb : ProjPureBodyWitness t E env auxKey tagCKey auxRecKey auxRecLps arules auxCtorKeyAt sbmPw
      nP bnl anc nF fidx jIdx pvalPos) :
    bodyUnpackSpec hb = minorUnpackSpec hminor := by
  unfold bodyUnpackSpec
  simp only [hp_strip, hrlJ, hrlJ_strip, Expr.getAppFn_mkAppN, Expr.getAppFn,
    getAppArgs_mkAppN_atom (f := .bvar (nF + anc - 1 - jIdx)) rargsJ (fun _ _ h => nomatch h),
    getAppArgs_mkAppN_atom (f := .const auxRecKey pheadLvls) pargs (fun _ _ h => nomatch h),
    hfindAuxRec, hminJ_strip]
  rfl

private theorem bodyUnpackSpec_viaDefn {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {env : Env .anon}
    {auxKey tagCKey auxRecKey : KKey} {auxRecLps : List LevelParam}
    {arules : List (RecRule .anon)} {auxCtorKeyAt : Nat → KKey} {sbmPw : Ix.Kernel.PropWhen}
    {nP bnl anc nF fidx jIdx : Nat} {pvalPos : KExpr}
    {pheadKey cvR rval rHint pbs pheadLvls pargs rbsJ rargsJ mbsJ mbody rlJ}
    (hfindR : env.find? pheadKey = some (.defnInfo cvR rval rHint))
    (hp_strip : pvalPos.stripLams (nP + 1) = some (pbs, Expr.mkAppN (.const pheadKey pheadLvls) pargs))
    (hrlJ : arules[jIdx]? = some rlJ)
    (hrlJ_strip : (Core.posOf auxRecLps rlJ.rhs).stripLams (nP + 1 + anc + nF) =
      some (rbsJ, Expr.mkAppN (.bvar (nF + anc - 1 - jIdx)) rargsJ))
    (hminJ_strip : (pargs.getD (nP + (pargs.length - nP - (anc + 1)) + jIdx) default).stripLams
      (nF + (rargsJ.length - nF)) = some (mbsJ, mbody))
    (hminor : ProjMinorWitness t E env auxKey auxRecKey auxRecLps arules auxCtorKeyAt sbmPw nP bnl anc
      nF (rargsJ.length - nF) fidx mbody)
    (hb : ProjPureBodyWitness t E env auxKey tagCKey auxRecKey auxRecLps arules auxCtorKeyAt sbmPw
      nP bnl anc nF fidx jIdx pvalPos) :
    bodyUnpackSpec hb = minorUnpackSpec hminor := by
  unfold bodyUnpackSpec
  simp only [hp_strip, hrlJ, hrlJ_strip, Expr.getAppFn_mkAppN, Expr.getAppFn,
    getAppArgs_mkAppN_atom (f := .bvar (nF + anc - 1 - jIdx)) rargsJ (fun _ _ h => nomatch h),
    getAppArgs_mkAppN_atom (f := .const pheadKey pheadLvls) pargs (fun _ _ h => nomatch h),
    hfindR, hminJ_strip]
  rfl

/-! ### Sort-polymorphic (`pwBit = 0`) telescope & `denoteMeta` depth-shift helpers -/

private theorem wscoped_openDummiesP {n : Nat} :
    ∀ (m d c : Nat) (e : KExpr), d + m ≤ n → Expr.WScoped n e →
      Expr.WScoped n (openDummiesP m d c e)
  | 0, _, _, _, _, h => h
  | m + 1, d, c, e, hle, h =>
    wscoped_openDummiesP m (d + 1) c _ (by omega)
      (Expr.WScoped.instantiate1_gen
        (show Expr.WScoped n (.fvar d (.sort .zero)) by simp [Expr.WScoped]; omega) (c + m) h)

private theorem looseBVarsBounded_exprSemEq {e₁ e₂ : KExpr} (he : ExprSemEq e₁ e₂) :
    ∀ k, e₁.looseBVarsBounded k = e₂.looseBVarsBounded k := by
  induction he with
  | bvar _ | sort _ | const _ | lit _ => intro _; rfl
  | fvar _ _ => intro _; rfl
  | app _ _ ihf iha => intro k; simp [Expr.looseBVarsBounded, ihf k, iha k]
  | lam _ _ _ iht ihb | forallE _ _ _ iht ihb =>
    intro k; simp [Expr.looseBVarsBounded, iht k, ihb (k + 1)]
  | letE _ _ _ iht ihv ihb =>
    intro k; simp [Expr.looseBVarsBounded, iht k, ihv k, ihb (k + 1)]
  | proj _ ihs => intro k; exact ihs k

private theorem hasLooseBVar_exprSemEq {e₁ e₂ : KExpr} (he : ExprSemEq e₁ e₂) :
    ∀ k, e₁.hasLooseBVar k = e₂.hasLooseBVar k := by
  induction he with
  | bvar _ | sort _ | const _ | lit _ => intro _; rfl
  | fvar _ _ => intro _; rfl
  | app _ _ ihf iha => intro k; simp [Expr.hasLooseBVar, ihf k, iha k]
  | lam _ _ _ iht ihb | forallE _ _ _ iht ihb =>
    intro k; simp [Expr.hasLooseBVar, iht k, ihb (k + 1)]
  | letE _ _ _ iht ihv ihb =>
    intro k; simp [Expr.hasLooseBVar, iht k, ihv k, ihb (k + 1)]
  | proj _ ihs => intro k; exact ihs k

private theorem instantiate1_of_looseBVarsBounded_le (v : KExpr) :
    ∀ (e : KExpr) (c k : Nat), e.looseBVarsBounded k = true → k ≤ c → e.instantiate1 v c = e
  | .bvar j, c, k, h, hle => by
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at h
    simp only [Expr.instantiate1]
    have h1 : j ≠ c := by omega
    have h2 : ¬ c < j := by omega
    simp [h1, h2]
  | .fvar _ _, _, _, _, _ | .sort _, _, _, _, _ | .const _ _, _, _, _, _ | .lit _, _, _, _, _ => rfl
  | .app f a, c, k, h, hle => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.instantiate1, instantiate1_of_looseBVarsBounded_le v f c k h.1 hle,
      instantiate1_of_looseBVarsBounded_le v a c k h.2 hle]
  | .lam t b _, c, k, h, hle | .forallE t b _, c, k, h, hle => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.instantiate1, instantiate1_of_looseBVarsBounded_le v t c k h.1 hle,
      instantiate1_of_looseBVarsBounded_le v b (c + 1) (k + 1) h.2 (by omega)]
  | .letE t val b _, c, k, h, hle => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.instantiate1, instantiate1_of_looseBVarsBounded_le v t c k h.1.1 hle,
      instantiate1_of_looseBVarsBounded_le v val c k h.1.2 hle,
      instantiate1_of_looseBVarsBounded_le v b (c + 1) (k + 1) h.2 (by omega)]
  | .proj _ _ s, c, k, h, hle => by
    simp only [Expr.instantiate1, instantiate1_of_looseBVarsBounded_le v s c k h hle]

private theorem openDummiesP_of_looseBVarsBounded_zero :
    ∀ (m d c : Nat) (e : KExpr), e.looseBVarsBounded 0 = true → openDummiesP m d c e = e
  | 0, _, _, _, _ => rfl
  | m + 1, d, c, e, h => by
    simp only [openDummiesP, instantiate1_of_looseBVarsBounded_le _ e (c + m) 0 h (Nat.zero_le _)]
    exact openDummiesP_of_looseBVarsBounded_zero m (d + 1) c e h

private theorem looseBVarsBounded_instantiate1_top {v : KExpr} (hv : ∀ k, v.looseBVarsBounded k = true) :
    ∀ (e : KExpr) (k : Nat), e.looseBVarsBounded (k + 1) = true →
      (e.instantiate1 v k).looseBVarsBounded k = true
  | .bvar j, k, h => by
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at h
    simp only [Expr.instantiate1]
    split
    · exact hv k
    · split
      · rename_i hne hgt; omega
      · simp only [Expr.looseBVarsBounded, decide_eq_true_eq]; omega
  | .fvar _ _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, k, h => by
    simp only [Expr.instantiate1, Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨looseBVarsBounded_instantiate1_top hv f k h.1, looseBVarsBounded_instantiate1_top hv a k h.2⟩
  | .lam t b _, k, h | .forallE t b _, k, h => by
    simp only [Expr.instantiate1, Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨looseBVarsBounded_instantiate1_top hv t k h.1, looseBVarsBounded_instantiate1_top hv b (k + 1) h.2⟩
  | .letE t val b _, k, h => by
    simp only [Expr.instantiate1, Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨⟨looseBVarsBounded_instantiate1_top hv t k h.1.1,
      looseBVarsBounded_instantiate1_top hv val k h.1.2⟩,
      looseBVarsBounded_instantiate1_top hv b (k + 1) h.2⟩
  | .proj _ _ s, k, h => looseBVarsBounded_instantiate1_top hv s k h

private theorem looseBVarsBounded_zero_of_no_lt :
    ∀ (e : KExpr) (c k : Nat),
      e.looseBVarsBounded (c + k) = true →
      (∀ i < c, e.hasLooseBVar (k + i) = false) →
      e.looseBVarsBounded k = true
  | .bvar j, c, k, hb, hno => by
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb ⊢
    by_contra hge
    have hlt : j - k < c := by omega
    have h := hno (j - k) hlt
    simp only [Expr.hasLooseBVar, show k + (j - k) = j by omega, beq_self_eq_true] at h
    cases h
  | .fvar _ _, _, _, _, _ | .sort _, _, _, _, _ | .const _ _, _, _, _, _ | .lit _, _, _, _, _ => rfl
  | .app f a, c, k, hb, hno => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    refine ⟨looseBVarsBounded_zero_of_no_lt f c k hb.1 fun i hi => ?_,
      looseBVarsBounded_zero_of_no_lt a c k hb.2 fun i hi => ?_⟩
    · have := hno i hi; simp [Expr.hasLooseBVar] at this; exact this.1
    · have := hno i hi; simp [Expr.hasLooseBVar] at this; exact this.2
  | .lam t b _, c, k, hb, hno | .forallE t b _, c, k, hb, hno => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    refine ⟨looseBVarsBounded_zero_of_no_lt t c k hb.1 fun i hi => ?_,
      looseBVarsBounded_zero_of_no_lt b c (k + 1)
        (by rw [show c + (k + 1) = c + k + 1 by omega]; exact hb.2) fun i hi => ?_⟩
    · have := hno i hi; simp [Expr.hasLooseBVar] at this; exact this.1
    · have h1 := hno i hi; simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at h1
      rw [show k + 1 + i = k + i + 1 by omega]; exact h1.2
  | .letE t val b _, c, k, hb, hno => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    refine ⟨⟨looseBVarsBounded_zero_of_no_lt t c k hb.1.1 fun i hi => ?_,
      looseBVarsBounded_zero_of_no_lt val c k hb.1.2 fun i hi => ?_⟩,
      looseBVarsBounded_zero_of_no_lt b c (k + 1)
        (by rw [show c + (k + 1) = c + k + 1 by omega]; exact hb.2) fun i hi => ?_⟩
    · have := hno i hi; simp [Expr.hasLooseBVar] at this; exact this.1.1
    · have := hno i hi; simp [Expr.hasLooseBVar] at this; exact this.1.2
    · have h1 := hno i hi; simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at h1
      rw [show k + 1 + i = k + i + 1 by omega]; exact h1.2
  | .proj _ _ s, c, k, hb, hno => looseBVarsBounded_zero_of_no_lt s c k hb hno

private theorem openDummiesP_looseBVarsBounded_zero :
    ∀ (m d c : Nat) (e : KExpr),
      e.looseBVarsBounded (c + m) = true →
      (∀ i < c, e.hasLooseBVar i = false) →
      (openDummiesP m d c e).looseBVarsBounded 0 = true
  | 0, _, c, e, hb, hno => by
    simpa [openDummiesP] using looseBVarsBounded_zero_of_no_lt e c 0 (by simpa using hb) (by simpa using hno)
  | m + 1, d, c, e, hb, hno => by
    simp only [openDummiesP]
    refine openDummiesP_looseBVarsBounded_zero m (d + 1) c _ ?_ ?_
    · exact looseBVarsBounded_instantiate1_top (fun _ => rfl) e (c + m) (by rwa [show c + m + 1 = c + (m + 1) by omega])
    · intro i hi
      rw [Ix.Kernel.Model.hasLooseBVar_instantiate1_lt (fun _ => rfl) e i (c + m) (by omega)]
      exact hno i hi

private theorem mkPisAV_append : ∀ (l1 l2 : List (Nat × Nat × AnnotTerm)) (b : AnnotTerm),
    mkPisAV (l1 ++ l2) b = mkPisAV l1 (mkPisAV l2 b)
  | [], _, _ => rfl
  | d :: l1, l2, b => by simp only [List.cons_append, mkPisAV, mkPisAV_append l1 l2 b]

private theorem looseBVarsBounded_stripPis_elem :
    ∀ (n k : Nat) {e rem : KExpr} {bs : List (KExpr × BinderMeta)},
      e.looseBVarsBounded k = true → e.stripPis n = some (bs, rem) →
      (∀ i (hi : i < bs.length), (bs[i]).1.looseBVarsBounded (k + i) = true) ∧
      rem.looseBVarsBounded (k + n) = true
  | 0, k, e, rem, bs, hb, hs => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨hbs, hrem⟩ := hs
    rw [← hbs, ← hrem]
    exact ⟨fun _ hi => (nomatch hi), by simpa using hb⟩
  | n + 1, k, .forallE ty b bm, rem, bs, hb, hs => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.stripPis, Option.map_eq_some_iff] at hs
    obtain ⟨⟨bs₀, rem₀⟩, hsb, hp⟩ := hs
    obtain ⟨hbs, hrem⟩ := Prod.mk.inj hp
    subst hrem
    obtain ⟨h1, h2⟩ := looseBVarsBounded_stripPis_elem n (k + 1) hb.2 hsb
    refine ⟨fun i hi => ?_, by rwa [show k + (n + 1) = k + 1 + n by omega]⟩
    subst hbs
    cases i with
    | zero => simpa using hb.1
    | succ i' => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h1 i' (by simpa using hi)
  | _ + 1, _, .bvar _, _, _, _, hs | _ + 1, _, .fvar _ _, _, _, _, hs
  | _ + 1, _, .sort _, _, _, _, hs | _ + 1, _, .const _ _, _, _, _, hs
  | _ + 1, _, .app _ _, _, _, _, hs | _ + 1, _, .lam _ _ _, _, _, _, hs
  | _ + 1, _, .letE _ _ _ _, _, _, _, hs | _ + 1, _, .lit _, _, _, _, hs
  | _ + 1, _, .proj _ _ _, _, _, _, hs => nomatch hs

private theorem hasFvar_stripPis_elem :
    ∀ (n : Nat) {e rem : KExpr} {bs : List (KExpr × BinderMeta)},
      e.hasFvar = false → e.stripPis n = some (bs, rem) →
      (∀ p ∈ bs, p.1.hasFvar = false) ∧ rem.hasFvar = false
  | 0, e, rem, bs, hf, hs => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨hbs, hrem⟩ := hs
    rw [← hbs, ← hrem]
    exact ⟨fun _ h => (nomatch h), hf⟩
  | n + 1, .forallE ty b bm, rem, bs, hf, hs => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.stripPis, Option.map_eq_some_iff] at hs
    obtain ⟨⟨bs₀, rem₀⟩, hsb, hp⟩ := hs
    obtain ⟨hbs, hrem⟩ := Prod.mk.inj hp
    subst hrem
    obtain ⟨h1, h2⟩ := hasFvar_stripPis_elem n hf.2 hsb
    refine ⟨fun p hp => ?_, h2⟩
    subst hbs
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact hf.1
    · exact h1 p hp'
  | _ + 1, .bvar _, _, _, _, hs | _ + 1, .fvar _ _, _, _, _, hs
  | _ + 1, .sort _, _, _, _, hs | _ + 1, .const _ _, _, _, _, hs
  | _ + 1, .app _ _, _, _, _, hs | _ + 1, .lam _ _ _, _, _, _, hs
  | _ + 1, .letE _ _ _ _, _, _, _, hs | _ + 1, .lit _, _, _, _, hs
  | _ + 1, .proj _ _ _, _, _, _, hs => nomatch hs

/-- Relating `instPisAt` on `List.range n` dummy fvars to `stripPis n` + `openDummiesP`. -/
private theorem instPisAt_range_fvars :
    ∀ (n d : Nat) {e rem : KExpr} {bs : List (KExpr × BinderMeta)},
      e.stripPis n = some (bs, rem) →
      (Expr.instPisAt ((List.range n).map fun m => .fvar (d + m) (.sort .zero)) e).map Prod.snd =
        some (openDummiesP n d 0 rem)
  | 0, _, e, rem, bs, hs => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨_, hrem⟩ := hs
    rw [← hrem]
    simp [Expr.instPisAt, openDummiesP]
  | n + 1, d, .forallE ty b bm, rem, bs, hs => by
    simp only [Expr.stripPis, Option.map_eq_some_iff] at hs
    obtain ⟨⟨bs₀, rem₀⟩, hsb, hp⟩ := hs
    obtain ⟨_, hrem⟩ := Prod.mk.inj hp
    subst hrem
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [Nat.add_zero, Expr.instPisAt]
    obtain ⟨bs', hsb'⟩ := stripPis_instantiate1 (.fvar d (.sort .zero)) n 0 hsb
    simp only [Nat.zero_add] at hsb'
    have hmap : List.map ((fun m => Expr.fvar (md := .anon) (d + m) (.sort .zero)) ∘ Nat.succ) (List.range n) =
        (List.range n).map fun m => Expr.fvar (md := .anon) (d + 1 + m) (.sort .zero) := by
      refine List.map_congr_left fun m _ => ?_
      simp only [Function.comp_def, show d + (m + 1) = d + 1 + m by omega]
    rw [hmap]
    have hih := instPisAt_range_fvars n (d + 1) hsb'
    cases hinst : Expr.instPisAt ((List.range n).map fun m => .fvar (d + 1 + m) (.sort .zero))
        (b.instantiate1 (.fvar d (.sort .zero)) 0) with
    | none => simp [hinst] at hih
    | some p =>
      rcases p with ⟨ds', body'⟩
      simp only [hinst, Option.map_some, Option.some.injEq] at hih
      simp only [Option.map_some, Option.some.injEq, openDummiesP, Nat.zero_add]
      exact hih
  | _ + 1, _, .bvar _, _, _, hs | _ + 1, _, .fvar _ _, _, _, hs
  | _ + 1, _, .sort _, _, _, hs | _ + 1, _, .const _ _, _, _, hs
  | _ + 1, _, .app _ _, _, _, hs | _ + 1, _, .lam _ _ _, _, _, hs
  | _ + 1, _, .letE _ _ _ _, _, _, hs | _ + 1, _, .lit _, _, _, hs
  | _ + 1, _, .proj _ _ _, _, _, hs => nomatch hs

private theorem stripPis_split {n1 n2 : Nat} {e rem : KExpr} {bs : List (KExpr × BinderMeta)}
    (hs : e.stripPis (n1 + n2) = some (bs, rem)) :
    ∃ bs1 rem1 bs2, e.stripPis n1 = some (bs1, rem1) ∧ rem1.stripPis n2 = some (bs2, rem) ∧
      bs = bs1 ++ bs2 := by
  induction n1 generalizing e bs with
  | zero =>
    simp only [Nat.zero_add] at hs
    exact ⟨[], e, bs, by simp [Expr.stripPis], hs, rfl⟩
  | succ n1 ih =>
    rw [show n1 + 1 + n2 = (n1 + n2) + 1 by omega] at hs
    cases e with
    | forallE ty b bm =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hs
      obtain ⟨⟨bs₀, rem₀⟩, hsb, hp⟩ := hs
      obtain ⟨hbs, hrem⟩ := Prod.mk.inj hp
      subst hrem
      obtain ⟨bs1, rem1, bs2, h1, h2, hcat⟩ := ih hsb
      refine ⟨(ty, bm) :: bs1, rem1, bs2, by simp [Expr.stripPis, h1], h2, ?_⟩
      rw [← hbs, hcat]; rfl
    | _ => simp [Expr.stripPis] at hs

private theorem stripPis_openDummiesP :
    ∀ (m d c n : Nat) {e rem : KExpr} {bs : List (KExpr × BinderMeta)},
      e.stripPis n = some (bs, rem) →
      ∃ (bs' : List (KExpr × BinderMeta)) (hlen : bs'.length = bs.length),
        (openDummiesP m d c e).stripPis n = some (bs', openDummiesP m d (c + n) rem) ∧
        ∀ i (hi : i < bs.length), (bs'[i]'(hlen.symm ▸ hi)).1 = openDummiesP m d (c + i) bs[i].1
  | 0, _, _, _, _, _, bs, hs => ⟨bs, rfl, hs, fun _ _ => rfl⟩
  | m + 1, d, c, n, e, rem, bs, hs => by
    have h1 : ∀ (v : KExpr) (n c : Nat) {e rem : KExpr} {bs : List (KExpr × BinderMeta)},
        e.stripPis n = some (bs, rem) →
        ∃ (bs' : List (KExpr × BinderMeta)) (hlen : bs'.length = bs.length),
          (e.instantiate1 v c).stripPis n = some (bs', rem.instantiate1 v (c + n)) ∧
          ∀ i (hi : i < bs.length), (bs'[i]'(hlen.symm ▸ hi)).1 = bs[i].1.instantiate1 v (c + i) := by
      intro v n
      induction n with
      | zero =>
        intro c e rem bs hs
        simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        exact ⟨[], rfl, by simp [Expr.stripPis], fun _ hi => nomatch hi⟩
      | succ n ihn =>
        intro c e rem bs hs
        cases e with
        | forallE ty b bm =>
          simp only [Expr.stripPis, Option.map_eq_some_iff] at hs
          obtain ⟨⟨bs₀, rem₀⟩, hsb, hp⟩ := hs
          obtain ⟨hbs, hrem⟩ := Prod.mk.inj hp
          subst hrem
          obtain ⟨bs', hlen', hbs', hdom'⟩ := ihn (c + 1) hsb
          refine ⟨(ty.instantiate1 v c, bm) :: bs', by rw [← hbs]; simp [hlen'], ?_, ?_⟩
          · simp only [Expr.instantiate1, Expr.stripPis, hbs', Option.map_some]
            rw [show c + 1 + n = c + (n + 1) by omega]
          · intro i hi
            subst hbs
            cases i with
            | zero => simp
            | succ i' =>
              simp only [List.getElem_cons_succ]
              rw [hdom' i' (by simpa using hi), show c + 1 + i' = c + (i' + 1) by omega]
        | _ => simp [Expr.stripPis] at hs
    obtain ⟨bs1, hlen1, hbs1, hdom1⟩ := h1 (.fvar d (.sort .zero)) n (c + m) hs
    obtain ⟨bs2, hlen2, hbs2, hdom2⟩ := stripPis_openDummiesP m (d + 1) c n hbs1
    refine ⟨bs2, hlen2.trans hlen1, ?_, fun i hi => ?_⟩
    · simpa [openDummiesP, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbs2
    · rw [hdom2 i (hlen1.symm ▸ hi), hdom1 i hi]
      simp only [openDummiesP, show c + i + m = c + m + i by omega]

/-- When `rawDom` at field `fidx` has no loose bvars `< fidx` and `looseBVarsBounded (nP + fidx)`,
`projFieldTeleAt` leaves `openDummiesP nP 0 fidx rawDom` untouched as `fdom`. -/
private theorem projFieldTeleAt_noLooseBVar {ctyMPos fdom frest rawDom remRaw : KExpr}
    {fbm : BinderMeta} {bsRaw : List (KExpr × BinderMeta)}
    {nP bnl nF fidx : Nat} {projKeyAt : Nat → KKey}
    (hfidx : fidx < nF)
    (hC_strip : ctyMPos.stripPis (nP + nF) = some (bsRaw, remRaw))
    (hraw : (bsRaw.map Prod.fst)[nP + fidx]? = some rawDom)
    (htele : projFieldTeleAt ctyMPos nP bnl projKeyAt fidx = some (.forallE fdom frest fbm))
    (hno_lt : ∀ i < fidx, rawDom.hasLooseBVar i = false)
    (hbnd : rawDom.looseBVarsBounded (nP + fidx) = true) :
    fdom = openDummiesP nP 0 fidx rawDom := by
  have hclosed : (openDummiesP nP 0 fidx rawDom).looseBVarsBounded 0 = true :=
    openDummiesP_looseBVarsBounded_zero nP 0 fidx rawDom (by rwa [Nat.add_comm]) hno_lt
  obtain ⟨bsP, remP, bsF, hP, hF, hcat⟩ := stripPis_split hC_strip
  have hlenP : bsP.length = nP := stripPis_length_p hP
  obtain ⟨bsF1, remF1, bsF2, hF1, hF2, hcatF⟩ := stripPis_split (show remP.stripPis (fidx + (nF - fidx)) = some (bsF, remRaw) by
    rwa [show fidx + (nF - fidx) = nF by omega])
  have hlenF1 : bsF1.length = fidx := stripPis_length_p hF1
  have hremF1_for : ∃ rawRest rawBm, remF1 = .forallE rawDom rawRest rawBm := by
    have hsub : nF - fidx = (nF - fidx - 1) + 1 := by omega
    rw [hsub] at hF2
    cases hrf : remF1 with
    | forallE d b m =>
      rw [hrf] at hF2
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hF2
      obtain ⟨⟨bs2', _⟩, _, hp⟩ := hF2
      injection hp with hbs2 _
      have hd_eq : d = rawDom := by
        rw [hcat, hcatF, ← hbs2] at hraw
        simp only [List.map_append, List.getElem?_append_right (by simp [hlenP] : (bsP.map Prod.fst).length ≤ nP + fidx),
          List.length_map, hlenP, Nat.add_sub_cancel_left,
          List.getElem?_append_right (by simp [hlenF1] : (bsF1.map Prod.fst).length ≤ fidx),
          hlenF1, Nat.sub_self, List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at hraw
        exact hraw
      subst hd_eq; exact ⟨b, m, rfl⟩
    | _ => rw [hrf] at hF2; simp [Expr.stripPis] at hF2
  obtain ⟨rawRest, rawBm, rfl⟩ := hremF1_for
  have h0_eq : projFieldTeleAt ctyMPos nP bnl projKeyAt 0 = some (openDummiesP nP 0 0 remP) := by
    simpa [projFieldTeleAt] using instPisAt_range_fvars nP 0 hP
  obtain ⟨bsO, -, hbsO, -⟩ := stripPis_openDummiesP nP 0 0 fidx hF1
  have hopen_for : ∀ (m d c : Nat) (t b : KExpr) (bm : BinderMeta),
      openDummiesP m d c (.forallE t b bm) =
        .forallE (openDummiesP m d c t) (openDummiesP m d (c + 1) b) bm := by
    intro m
    induction m with
    | zero => intros; rfl
    | succ m ih =>
      intro d c t b bm
      simp only [openDummiesP, Expr.instantiate1]
      rw [show c + m + 1 = c + 1 + m by omega]
      exact ih (d + 1) c _ _ bm
  rw [Nat.zero_add, hopen_for] at hbsO
  -- By induction on `k ≤ fidx`, `projFieldTeleAt ... k = some rem_k` with `rem_k.stripPis (fidx - k) = some (_, .forallE (openDummiesP nP 0 fidx rawDom) _ _)`
  have hind : ∀ k (hk : k ≤ fidx),
      ∃ rem_k bs_k rest_k bm_k,
        projFieldTeleAt ctyMPos nP bnl projKeyAt k = some rem_k ∧
        rem_k.stripPis (fidx - k) = some (bs_k, .forallE (openDummiesP nP 0 fidx rawDom) rest_k bm_k) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨openDummiesP nP 0 0 remP, bsO, openDummiesP nP 0 (fidx + 1) rawRest, rawBm, h0_eq, by simpa using hbsO⟩
    | succ k ih =>
      intro hk
      obtain ⟨rem_k, bs_k, rest_k, bm_k, htk, hsk⟩ := ih (by omega)
      have hpos : fidx - k = (fidx - (k + 1)) + 1 := by omega
      rw [hpos] at hsk
      cases hrem : rem_k with
      | forallE domK bodyK bmK =>
        rw [hrem] at hsk htk
        simp only [Expr.stripPis, Option.map_eq_some_iff] at hsk
        obtain ⟨⟨bs_k', rem_k'⟩, hsb', hp⟩ := hsk
        obtain ⟨_, hfor⟩ := Prod.mk.inj hp
        subst hfor
        let projApp := Expr.mkAppN (.const (projKeyAt k) ((List.range bnl).map .param))
          (((List.range nP).map fun m => .fvar m (.sort .zero)) ++ [.fvar nP (.sort .zero)])
        obtain ⟨bs_next, hnext⟩ := stripPis_instantiate1 projApp (fidx - (k + 1)) 0 hsb'
        simp only [Expr.instantiate1, Nat.zero_add,
          instantiate1_of_looseBVarsBounded_le projApp _ (fidx - (k + 1)) 0 hclosed (Nat.zero_le _)] at hnext
        refine ⟨bodyK.instantiate1 projApp 0, bs_next, rest_k.instantiate1 projApp (fidx - (k + 1) + 1), bm_k, ?_, hnext⟩
        simp [projFieldTeleAt, htk, projApp]
      | _ => rw [hrem] at hsk; simp [Expr.stripPis] at hsk
  obtain ⟨rem_f, bs_f, rest_f, bm_f, htf, hsf⟩ := hind fidx (Nat.le_refl _)
  rw [Nat.sub_self, Expr.stripPis] at hsf
  obtain ⟨_, hr⟩ := Prod.mk.inj (Option.some.inj hsf)
  rw [htf, hr] at htele
  exact (Expr.forallE.inj (Option.some.inj htele)).1.symm

/-! ### `projPure_coherence` -/

set_option maxHeartbeats 2400000 in
/-- Main coherence theorem for a checked `ProjPureWitness`: evaluating `fp.projKey` on `(vs_v, x_v)`
terminates under `treeUnpackOpt (bodyUnpackSpec wp.hbody)` on `projS (fidx + 1) x_v` and equals
`treeUnpack (bodyUnpackSpec wp.hbody) (projS (fidx + 1) x_v)`. -/
theorem projPure_coherence {V : Type u} [SetTheory V] {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Env .anon} {Reg : NativeFam .anon → Prop}
    (ht : t.check = .ok ())
    (hbasis : ∀ ci ∈ IxVM.Refinement.TableInhabit.basisEnv.consts, env.find? ci.name = some ci)
    (hreg : FamRegistryWith FormerOpenTraceAt t E env Reg)
    (mp : EnvModelM V .verified env)
    (hN : ∀ fam, Reg fam → NativeFamOk mp fam)
    {tModelKey cModelKey : KKey} {tyTPos ctyMPos fdom rawDom : KExpr}
    {nP bnl nF fidx : Nat}
    (fp : FieldProjFacts t E env tModelKey cModelKey tyTPos ctyMPos nP bnl nF fidx fdom rawDom)
    (wp : ProjPureWitness t E env tModelKey (Core.posOf fp.cvProj.levelParams fp.projVal)
      ctyMPos rawDom fp.sbm.pw nP bnl nF fidx)
    (hfidx : fidx < nF)
    (hprojTele : ∃ projKeyAt frest fbm,
      projFieldTeleAt ctyMPos nP bnl projKeyAt fidx = some (.forallE fdom frest fbm))
    (hrawDom_at : (fp.cbsI.map Prod.fst)[nP + fidx]? = some rawDom)
    (ψ_P : LevelParam → Nat) (ρ₀ : Nat → V) (vs_v : List V) (x_v : V)
    (hvs_len : vs_v.length = nP)
    (hApp_TM : AppChainOk (interp V ρ₀ (mp.base2.acval tModelKey (origVal wp.cvmT.levelParams ψ_P))) vs_v)
    (hx_mem : x_v ∈ˢ vs_v.foldl SetTheory.app
      (interp V ρ₀ (mp.base2.acval tModelKey (origVal wp.cvmT.levelParams ψ_P))))
    (hApp_proj : AppChainOk (interp V ρ₀ (mp.base2.acval fp.projKey (origVal fp.cvProj.levelParams ψ_P)))
      (vs_v ++ [x_v]))
    (hrdom_mem : ∀ rdomA,
      denoteMeta mp.base2.acval env ψ_P (nP + 1) (openDummiesP (nP + 1) 0 0 fp.rdom) = some rdomA →
      (vs_v ++ [x_v]).foldl SetTheory.app
        (interp V ρ₀ (mp.base2.acval fp.projKey (origVal fp.cvProj.levelParams ψ_P))) ∈ˢ
        interp V (consList (vs_v ++ [x_v]) ρ₀) rdomA ∧
      (pwBit ψ_P fp.sbm.pw = 0 →
        interp V (consList (vs_v ++ [x_v]) ρ₀) rdomA ∈ˢ (univZero : V))) :
    let spec := bodyUnpackSpec wp.hbody
    (∃ N, Ix.Kernel.SetModel.treeUnpackOpt spec N (projS (fidx + 1) x_v) =
      some (Ix.Kernel.SetModel.treeUnpack spec (projS (fidx + 1) x_v))) ∧
    (vs_v ++ [x_v]).foldl SetTheory.app
      (interp V ρ₀ (mp.base2.acval fp.projKey (origVal fp.cvProj.levelParams ψ_P))) =
      Ix.Kernel.SetModel.treeUnpack spec (projS (fidx + 1) x_v) := by
  intro spec
  -- 1. Recover registered `famAux` for `wp.auxKey` and unfold `tModelKey` via `wp.hTM_strip`!
  obtain ⟨famAux, hregAux, hnameAux⟩ :=
    hreg.complete wp.auxIndWit.addr wp.auxIndWit.cm wp.auxIndWit.ip wp.auxIndWit.cv wp.auxIndWit.caps
      (show env.find? (Core.keyOf t wp.auxIndWit.addr) = _ by
        rw [wp.auxIndWit.hkey]; exact wp.auxIndWit.hfind)
      (show Ix.Kernel.reservedBasisNames.contains (Core.keyOf t wp.auxIndWit.addr) = false by
        rw [wp.auxIndWit.hkey]; exact wp.auxIndWit.hnotRes)
      wp.auxIndWit.hrec wp.auxIndWit.hinfo wp.auxIndWit.hnat
  have hnameAux' : famAux.p.cvT.name = wp.auxKey := hnameAux.trans wp.auxIndWit.hkey
  obtain ⟨env₀, bsT, ppsAll, uAV, fssZ, idxF, dsF, esF, srcsF, ksF, fvsPF, xFvsF, xrestF,
    eissF, tssF, hAtAux⟩ := hN famAux hregAux
  have hreadAux := hreg.fams famAux hregAux
  have hreadAtAux := hreadAux.readAt ht (hnameAux'.trans wp.auxIndWit.hkey.symm)
    wp.auxIndWit.hrec wp.auxIndWit.hinfo
  obtain ⟨-, -, cbA, msA, indA, hcbA, hmsA, hindA, hnPA, hnIdxA, hlenA, hctorNameA⟩ := hreadAtAux
  obtain ⟨cb', ms', ind', hcb', hms', hind', hnP', hnIdx', hanc'⟩ := wp.hauxInd_rec
  have hcb_eq : cbA = cb' := Option.some.inj (hcbA.symm.trans hcb')
  subst hcb_eq
  have hms_eq : msA = ms' := Ixon.ConstantInfo.muts.inj (hmsA.symm.trans hms')
  subst hms_eq
  rw [wp.hauxInd_idx] at hindA hctorNameA
  have hind_eq : indA = ind' := Ixon.MutConst.indc.inj (Option.some.inj (hindA.symm.trans hind'))
  subst hind_eq
  have hfam_nP : famAux.p.nP = nP := hnPA.trans hnP'
  have hfam_nIdx : famAux.p.nIdx = 1 := hnIdxA.trans hnIdx'
  have hfam_ctors_len : famAux.ctorsA.length = wp.anc := hlenA.trans hanc'
  have hfam_lps : famAux.p.cvT.levelParams = List.range bnl := by
    have hcvS_eq : famAux.cvS = wp.auxIndWit.cv := famRead_cvS_eq hreadAux hnameAux' wp.auxIndWit.hfind
    have hlen_lps : famAux.p.cvT.levelParams.length = bnl := by
      rw [← hreadAux.lps, hcvS_eq]; exact wp.hauxInd_lvls
    exact famRead_lps_range hreadAux hlen_lps
  have horig_fam : origVal famAux.p.cvT.levelParams ψ_P = ψ_P := by
    unfold origVal Core.posLevels
    rw [hfam_lps, List.length_range]
    exact substFn_range_param bnl ψ_P
  -- Unfold `tModelKey`'s definition `mvalT` at `origVal wp.cvmT.levelParams ψ_P`!
  have hTM_den : denoteMeta mp.base2.acval env ψ_P 0 (Core.posOf wp.cvmT.levelParams wp.mvalT) =
      some (mp.base2.acval tModelKey (origVal wp.cvmT.levelParams ψ_P)) := by
    rw [posOf_denoteMeta]
    have h := mp.defn_reads (origVal wp.cvmT.levelParams ψ_P) wp.cvmT wp.mvalT
      ⟨wp.hintT, Ix.Kernel.Semantics.Env.find?_mem wp.hfindTM⟩
    have hn : wp.cvmT.name = tModelKey := Ix.Kernel.Semantics.Env.find?_name wp.hfindTM
    rwa [hn] at h
  obtain ⟨tmDs, tmBodyA, hTM_mk, htmDs_len, htmDs_bits, htmBodyA_den⟩ :=
    denoteMeta_stripLams nP 0 wp.hTM_strip hTM_den
  simp only [Nat.zero_add] at htmBodyA_den
  have hwd_TM : WellDenotedV V ρ₀ (mkLamsAV tmDs tmBodyA) := by
    rw [← hTM_mk]; exact ⟨mp.base2.acval_wellDenoted _ _ _, mp.acval_validV _ _ _⟩
  have hnz_tmDs : ∀ p ∈ tmDs, p.1 ≠ 0 := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    have hbi := map_getElem_eq htmDs_bits i hi (by rw [stripLams_length wp.hTM_strip]; omega)
    have hnev := wp.hTM_pw (wp.tmbs[i]'(by rw [stripLams_length wp.hTM_strip]; omega)) (List.getElem_mem _)
    rw [hbi, hnev]; simp [pwBit]
  rw [hTM_mk] at hApp_TM hx_mem
  obtain ⟨hTM_fold, -, hwd_tmBody⟩ := mkLamsAV_appChainOk_pos tmDs tmBodyA vs_v ρ₀ hnz_tmDs
    (by rw [htmDs_len, hvs_len]) hwd_TM hApp_TM
  rw [hTM_fold] at hx_mem
  -- Evaluate `tmBodyA = mkAppN (acval auxKey ψ_P) auxArgsA` with `auxArgsA` → `vs_v ++ [tagVal]`!
  rw [openDummiesP_mkAppN, openDummiesP_const] at htmBodyA_den
  obtain ⟨fauxA, auxArgsA, hfauxA, hsp_auxA, htmBodyA_eq⟩ := denoteMeta_mkAppN_inv htmBodyA_den
  have haux_lps : wp.auxIndWit.cv.levelParams = List.range bnl := by
    have hcvS_eq : famAux.cvS = wp.auxIndWit.cv := famRead_cvS_eq hreadAux hnameAux' wp.auxIndWit.hfind
    rw [← hcvS_eq, hreadAux.lps, hfam_lps]
  have hauxLvls_len : wp.auxLvls.length = wp.auxIndWit.cv.levelParams.length := by
    have h1 := (lvEqList_getElem wp.hauxLvls).1; rw [haux_lps]; simpa using h1
  simp only [denoteMeta, wp.auxIndWit.hfind, ConstantInfo.toConstantVal, hauxLvls_len, ↓reduceIte, Option.some.injEq] at hfauxA
  have hfauxA_eq : fauxA = mp.base2.acval wp.auxKey ψ_P := by
    rw [← hfauxA, haux_lps, substFn_eq_of_lvEqList wp.hauxLvls ψ_P, substFn_range_param]
  -- Evaluate `auxArgsA` to `vs_v ++ [tagVal]` and get `AppChainOk (acval tagCKey ψ_P) vs_v`!
  have hauxArgs_len := wp.hauxArgs_len
  have hauxArgsA_len : auxArgsA.length = nP + 1 := by
    have := denoteMetaSpine_length_eq hsp_auxA; simp only [List.length_map, hauxArgs_len] at this; exact this.symm
  rw [htmBodyA_eq, hfauxA_eq] at hwd_tmBody hx_mem
  obtain ⟨-, hwd_auxArgs, hApp_aux⟩ := appChainOk_of_wellDenotedV auxArgsA hwd_tmBody
  -- Identify `auxArgsA[nP]` = `mkAppN (acval tagCKey ψ_P) tcArgsA`
  have hden_tag := denoteMetaSpine_getElem hsp_auxA (i := nP) (by simp [hauxArgs_len])
  simp only [List.getElem_map] at hden_tag
  have htag_arg : wp.auxArgs[nP]'(by omega) = Expr.mkAppN (.const wp.tagCKey wp.tcLvls) wp.tcArgs := by
    have htag := wp.hauxArgs_tag
    rw [List.getElem?_eq_getElem (by omega : nP < wp.auxArgs.length)] at htag
    exact Option.some.inj htag
  rw [htag_arg, openDummiesP_mkAppN, openDummiesP_const] at hden_tag
  obtain ⟨ftcA, tcArgsA, hftcA, hsp_tc, htagA_eq⟩ := denoteMeta_mkAppN_inv hden_tag
  have htcLvls_len : wp.tcLvls.length = wp.tagCWit.cv.levelParams.length := by
    have h1 := (lvEqList_getElem wp.htcLvls).1; rw [wp.htagC_lvls]; simpa using h1
  simp only [denoteMeta, wp.tagCWit.hfind, ConstantInfo.toConstantVal, htcLvls_len, ↓reduceIte, Option.some.injEq] at hftcA
  have htagC_lps : wp.tagCWit.cv.levelParams = List.range bnl := by
    obtain ⟨famT, jT, cAT, hregT, -, hcAT, hcTName, -⟩ :=
      hreg.completeCtor wp.tagCWit.addr wp.tagCWit.cm wp.tagCWit.cp wp.tagCWit.cv wp.tagCWit.nP wp.tagCWit.nF
        (show env.find? (Core.keyOf t wp.tagCWit.addr) = _ by rw [wp.tagCWit.hkey]; exact wp.tagCWit.hfind)
        (show Ix.Kernel.reservedBasisNames.contains (Core.keyOf t wp.tagCWit.addr) = false by rw [wp.tagCWit.hkey]; exact wp.tagCWit.hnotRes)
        wp.tagCWit.hrec wp.tagCWit.hinfo wp.tagCWit.hnat
    have hfcT := ((hreg.fams famT hregT).stored.ctor jT cAT hcAT).1
    rw [hcTName.trans wp.tagCWit.hkey, wp.tagCWit.hfind] at hfcT
    have hcvT_eq : cAT.1 = wp.tagCWit.cv := ((ConstantInfo.ctorInfo.inj (Option.some.inj hfcT)).1).symm
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hAtT⟩ := hN famT hregT
    have hlT := hAtT.lpsA cAT (List.mem_of_getElem? hcAT)
    have hlenT : famT.p.cvT.levelParams.length = bnl := by
      rw [← hlT, hcvT_eq]; exact wp.htagC_lvls
    rw [← hcvT_eq, hlT]
    exact famRead_lps_range (hreg.fams famT hregT) hlenT
  have hftcA_eq : ftcA = mp.base2.acval wp.tagCKey ψ_P := by
    rw [← hftcA, htagC_lps, substFn_eq_of_lvEqList wp.htcLvls ψ_P, substFn_range_param]
  have htcArgsV_eq : tcArgsA.map (interp V (consList vs_v ρ₀)) = vs_v := by
    have htc_len : wp.tcArgs.length = nP := by
      have := wp.htcArgs.length_eq; simpa using this
    have htcA_len : tcArgsA.length = nP := by
      have := denoteMetaSpine_length_eq hsp_tc; simp only [List.length_map, htc_len] at this; exact this.symm
    refine List.ext_getElem (by simp [htcA_len, hvs_len]) fun i hi1 hi2 => ?_
    simp only [List.getElem_map]
    have hden_i := denoteMetaSpine_getElem hsp_tc (i := i) (by simp [htc_len]; omega)
    simp only [List.getElem_map] at hden_i
    have heq_i : ExprSemEq (wp.tcArgs[i]'(by omega)) (.bvar (nP - 1 - i)) := by
      have := forall₂_getElem wp.htcArgs i (by omega) (by simp; omega)
      simpa using this
    have hden_bv : denoteMeta mp.base2.acval env ψ_P nP (openDummiesP nP 0 0 (.bvar (nP - 1 - i))) =
        some (.bvar (nP - 1 - i)) := denoteMeta_openDummiesP_bvar0 (by omega)
    have hsame := (denoteMeta_exprSemEq (acval := mp.base2.acval) (env := env) (φ := ψ_P) (d := nP)
      (exprSemEq_openDummiesP heq_i nP 0 0)).symm.trans hden_i
    rw [hden_bv] at hsame
    rw [(Option.some.inj hsame).symm, interp_bvar, ← hvs_len, consList_bvar_desc vs_v ρ₀ (by omega)]
  have hwd_tagA : WellDenotedV V (consList vs_v ρ₀) (AnnotTerm.mkAppN (mp.base2.acval wp.tagCKey ψ_P) tcArgsA) := by
    rw [← hftcA_eq, ← htagA_eq]; exact hwd_auxArgs _ (List.getElem_mem _)
  obtain ⟨-, -, hApp_tagC_raw⟩ := appChainOk_of_wellDenotedV tcArgsA hwd_tagA
  have hcl_tagC : interp V (consList vs_v ρ₀) (mp.base2.acval wp.tagCKey ψ_P) =
      interp V ρ₀ (mp.base2.acval wp.tagCKey ψ_P) :=
    closed_interp_env (mp.base2.acval_closed wp.tagCKey ψ_P) _ _
  have hApp_tagC : AppChainOk (interp V ρ₀ (mp.base2.acval wp.tagCKey ψ_P)) vs_v := by
    have h1 : AppChainOk (interp V ρ₀ (mp.base2.acval wp.tagCKey ψ_P))
        (tcArgsA.map (interp V (consList vs_v ρ₀))) := hcl_tagC ▸ hApp_tagC_raw
    rwa [htcArgsV_eq] at h1
  let tagVal := vs_v.foldl SetTheory.app (interp V ρ₀ (mp.base2.acval wp.tagCKey ψ_P))
  have hauxArgsV_eq : auxArgsA.map (interp V (consList vs_v ρ₀)) = vs_v ++ [tagVal] := by
    refine List.ext_getElem (by simp [hauxArgsA_len, hvs_len]) fun i hi1 hi2 => ?_
    simp only [List.getElem_map]
    by_cases hiP : i < nP
    · have hden_i := denoteMetaSpine_getElem hsp_auxA (i := i) (by simp [hauxArgs_len]; omega)
      simp only [List.getElem_map] at hden_i
      have heq_i : ExprSemEq (wp.auxArgs[i]'(by omega)) (.bvar (nP - 1 - i)) := by
        have := forall₂_getElem wp.hauxArgs_pref i
          (by rw [List.length_take, hauxArgs_len]; omega) (by simp; omega)
        simpa [List.getElem_take] using this
      have hden_bv : denoteMeta mp.base2.acval env ψ_P nP (openDummiesP nP 0 0 (.bvar (nP - 1 - i))) =
          some (.bvar (nP - 1 - i)) := denoteMeta_openDummiesP_bvar0 (by omega)
      have hsame := (denoteMeta_exprSemEq (acval := mp.base2.acval) (env := env) (φ := ψ_P) (d := nP)
        (exprSemEq_openDummiesP heq_i nP 0 0)).symm.trans hden_i
      rw [hden_bv] at hsame
      rw [(Option.some.inj hsame).symm, interp_bvar, ← hvs_len, consList_bvar_desc vs_v ρ₀ (by omega),
        List.getElem_append_left (by omega : i < vs_v.length)]
    · have hi_eq : i = nP := by simp [hauxArgsA_len] at hi1; omega
      subst i
      rw [List.getElem_append_right (by omega : vs_v.length ≤ nP)]
      simp only [hvs_len, Nat.sub_self, List.getElem_cons_zero]
      rw [htagA_eq, hftcA_eq, interp_mkAppN_foldl, htcArgsV_eq, hcl_tagC]
  -- Fold `nativeTyAVI` at `vs_v ++ [tagVal]` to get `hsp_p`, `hsp_tag`, and `hx_mem_aux`!
  have hcl_aux : interp V (consList vs_v ρ₀) (mp.base2.acval wp.auxKey ψ_P) =
      interp V ρ₀ (mp.base2.acval wp.auxKey ψ_P) :=
    closed_interp_env (mp.base2.acval_closed wp.auxKey ψ_P) _ _
  rw [interp_mkAppN_foldl, hauxArgsV_eq, hcl_aux] at hx_mem
  rw [hauxArgsV_eq, hcl_aux] at hApp_aux
  have hokT₀ : WellDenotedV V ρ₀ (mp.base2.acval wp.auxKey ψ_P) :=
    ⟨mp.base2.acval_wellDenoted _ _ _, mp.acval_validV _ _ _⟩
  rw [← hnameAux', hAtAux.leafT ψ_P] at hx_mem hApp_aux hokT₀
  have hnz_T : ∀ p ∈ ((ppsAll ψ_P).map fun d => (famAux.p.resSort.eval ψ_P + 1, d.2.2)), p.1 ≠ 0 := by
    intro p hp; obtain ⟨d, -, rfl⟩ := List.mem_map.mp hp; omega
  have hfold_T := mkLamsAV_appChainOk_pos
    ((ppsAll ψ_P).map fun d => (famAux.p.resSort.eval ψ_P + 1, d.2.2)) _ (vs_v ++ [tagVal]) ρ₀ hnz_T
    (by simp [hAtAux.former.len ψ_P, hfam_nP, hfam_nIdx, hvs_len]) hokT₀ hApp_aux
  have hsp_allT : SpineFit ρ₀ ((ppsAll ψ_P).map (·.2.2)) (vs_v ++ [tagVal]) := by
    simpa [List.map_map, Function.comp_def] using hfold_T.2.1
  have hsplit_pT : (ppsAll ψ_P).map (·.2.2) =
      ((ppsAll ψ_P).take famAux.p.nP).map (·.2.2) ++ ((ppsAll ψ_P).drop famAux.p.nP).map (·.2.2) := by
    rw [← List.map_append, List.take_append_drop]
  have hlen_pT : (((ppsAll ψ_P).take famAux.p.nP).map (·.2.2)).length = vs_v.length := by
    rw [List.length_map, List.length_take, hAtAux.former.len ψ_P, hfam_nP, hvs_len]; omega
  obtain ⟨hsp_p, hsp_tag⟩ := (spineFit_append_iff hlen_pT).mp (hsplit_pT ▸ hsp_allT)
  have hIds_len : (((ppsAll ψ_P).drop famAux.p.nP).map (·.2.2)).length = 1 := by
    have := hAtAux.former.len ψ_P; rw [List.length_map, List.length_drop, this, hfam_nIdx]; omega
  have hsat_p : Sat V (((ppsAll ψ_P).take famAux.p.nP).map (·.2.2)).reverse (consList vs_v ρ₀) := by
    simpa using Ix.Kernel.Model.sat_of_spineFit (Δ₀ := []) (Ix.Kernel.Semantics.Sat_nil V ρ₀) hsp_p
  have hfrAux := hAtAux.frames ψ_P (consList vs_v ρ₀) hsat_p
  have hnat_eq := nativeTyAVI_fold_at hfrAux.1 hsp_p hsp_tag
  rw [hnat_eq, hIds_len] at hx_mem
  have hx_mem_aux : x_v ∈ˢ SetTheory.app (fixFamI (uAV ψ_P) (famAux.p.resSort.eval ψ_P) (consList vs_v ρ₀)
      (((ppsAll ψ_P).drop famAux.p.nP).map (·.2.2)) 1
      (Ix.Kernel.Model.rssOfK ksF famAux.ctorsA.length)
      (Ix.Kernel.Model.tlssOfR (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0))
      (Ix.Kernel.Model.eissOfR (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0))
      (fssZ ψ_P)
      (Ix.Kernel.Model.essOfR (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0)))
      (tupW (uAV ψ_P) [tagVal]) := by
    simpa [hfam_nP, hvs_len] using hx_mem
  -- 2. Apply `aux_elem_invert_unique` to invert `x_v = inj wp.jIdx (mkTower (fs ++ [pt]))`!
  obtain ⟨fs, hx_eq, hfs_len, hfitC_j⟩ :=
    aux_elem_invert_unique ht hreg mp hN wp.tagCWit wp.htagC_lvls wp.htagC_nP wp.htagC_nF
      wp.tagIndWit wp.htagInd_lvls wp.htagInd_idx ⟨wp.tagSortBs, wp.tagSortU, wp.htagInd_sort, wp.htagInd_nz⟩
      wp.auxIndWit wp.hauxInd_lvls wp.hauxInd_idx wp.hauxInd_rec
      ⟨wp.auxSortBs, wp.auxSortU, wp.hauxInd_sort, wp.hauxInd_nz⟩
      wp.hjIdx_lt (fun k hk => by
        obtain ⟨w, hw1, hw2, hw3⟩ := wp.hauxCtors k hk
        exact ⟨w, hw1.trans (wp.hauxCtorKeyAt k), hw2, hw3⟩)
      hregAux hnameAux' hAtAux ψ_P ρ₀ vs_v x_v hvs_len hApp_tagC hsp_p hsp_tag hx_mem_aux
  -- `projS (fidx + 1) x_v = fs[fidx]`!
  have hproj_x : projS (fidx + 1) x_v = fs[fidx]'(by omega) := by
    rw [hx_eq, Ix.Kernel.Model.projS_succ_inj]
    have h1 := projS_mkTower_getD (fs := fs) (i := fidx) (by omega)
    rw [h1, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega : fidx < fs.length), Option.getD_some]
  -- 3. Split on `pwBit ψ_P fp.sbm.pw = 0` vs `pwBit ψ_P fp.sbm.pw ≠ 0`!
  by_cases hpw0 : pwBit ψ_P fp.sbm.pw = 0
  · -- **SQUASH REGIME (`pwBit ψ_P fp.sbm.pw = 0`, sort-polymorphic field instantiated at `Prop`)**
    -- 3a. `spec = []` because `.unpack` requires `∀ φ, pwBit φ sbmPw > 0`!
    have hspec_nil : spec = [] := by
      cases wp.hbody with
      | direct pbs pheadLvls pargs rbsJ rargsJ mbsJ mbody rlJ hp_strip _ _ _ _ _ _ _ _ hrlJ _ hrlJ_strip _ _ hminJ_strip _ hminor =>
        have hb_eq := bodyUnpackSpec_direct wp.hfindAuxRec hp_strip hrlJ hrlJ_strip hminJ_strip hminor wp.hbody
        rw [show spec = bodyUnpackSpec wp.hbody from rfl, hb_eq, ← mbodyUnpackSpec_eq_minorUnpackSpec]
        cases hminor with
        | bvar hmbody => rw [hmbody]; exact mbodyUnpackSpec_bvar
        | unpack hsbl_nz => have := hsbl_nz ψ_P; omega
      | viaDefn pheadKey cvR rval rHint pbs pheadLvls pargs rbs arLvls rargs rbsJ rargsJ mbsJ mbody rlJ
          hp_strip _ _ _ _ _ hfindR _ _ _ _ _ _ _ _ _ _ _ _ _ hrlJ _ hrlJ_strip _ _ hminJ_strip _ hminor =>
        have hb_eq := bodyUnpackSpec_viaDefn hfindR hp_strip hrlJ hrlJ_strip hminJ_strip hminor wp.hbody
        rw [show spec = bodyUnpackSpec wp.hbody from rfl, hb_eq, ← mbodyUnpackSpec_eq_minorUnpackSpec]
        cases hminor with
        | bvar hmbody => rw [hmbody]; exact mbodyUnpackSpec_bvar
        | unpack hsbl_nz => have := hsbl_nz ψ_P; omega
    -- 3b. Extract `rdomA` from `fp.cvProj.type` and prove both `val = pt` and `fs[fidx] = pt`!
    have hmemP := Ix.Kernel.Semantics.Env.find?_mem fp.hfindProj
    obtain ⟨TPa, hTPa⟩ := mp.type_reads _ hmemP (origVal fp.cvProj.levelParams ψ_P)
    have hTPa_pos : denoteMeta mp.base2.acval env ψ_P 0 (Core.posOf fp.cvProj.levelParams fp.cvProj.type) = some TPa := by
      rw [posOf_denoteMeta]; exact hTPa
    obtain ⟨dsP, remP, -, -, -, hremP_den⟩ := denoteMeta_stripPis nP 0 fp.hProj_strip hTPa_pos
    simp only [Nat.zero_add] at hremP_den
    have hopen_for : ∀ (m d c : Nat) (t b : KExpr) (bm : BinderMeta),
        openDummiesP m d c (.forallE t b bm) =
          .forallE (openDummiesP m d c t) (openDummiesP m d (c + 1) b) bm := by
      intro m
      induction m with
      | zero => intros; rfl
      | succ m ih =>
        intro d c t b bm
        simp only [openDummiesP, Expr.instantiate1]
        rw [show c + m + 1 = c + 1 + m by omega]
        exact ih (d + 1) c _ _ bm
    rw [hopen_for] at hremP_den
    obtain ⟨sdomA, rdomA, -, hrdomA_den, -⟩ := denoteMeta_forallE_some hremP_den
    have hrdom_open_eq : openDummiesP (nP + 1) 0 0 fp.rdom =
        (openDummiesP nP 0 1 fp.rdom).instantiate1 (.fvar nP (.sort .zero)) 0 := by
      simpa [openDummiesP, Nat.zero_add] using openDummiesP_add nP 1 0 fp.rdom
    rw [← hrdom_open_eq] at hrdomA_den
    obtain ⟨hval_mem_rdom, hrdom_u0⟩ := hrdom_mem rdomA hrdomA_den
    have hrdom_zero : interp V (consList (vs_v ++ [x_v]) ρ₀) rdomA ∈ˢ (univZero : V) := hrdom_u0 hpw0
    have hval_pt : (vs_v ++ [x_v]).foldl SetTheory.app
        (interp V ρ₀ (mp.base2.acval fp.projKey (origVal fp.cvProj.levelParams ψ_P))) = pt :=
      eq_pt_of_mem_univZero hrdom_zero hval_mem_rdom
    -- Now prove `fs[fidx] = pt` via `wp.hsort_poly`!
    rcases wp.hsort_poly with hnz_all | ⟨hno_lt, cvAuxC, kbs, krest, cbs, crest, kfbs, kfdom, kfrest,
        kfbm, hfindAuxC, hAuxC_P, hC_P, -, hAuxC_F, hkfdom_eq⟩
    · have := hnz_all ψ_P; omega
    · -- Match `cvAuxC` with `famAux.ctorsA[wp.jIdx]`!
      obtain ⟨cAj, hcAj⟩ : ∃ cAj, famAux.ctorsA[wp.jIdx]? = some cAj :=
        ⟨_, List.getElem?_eq_getElem (by have := hfam_ctors_len; have := wp.hjIdx_lt; omega)⟩
      have hcj_name : cAj.1.name = wp.auxCtorKeyAt wp.jIdx :=
        (hctorNameA wp.jIdx cAj hcAj).trans (wp.hauxCtorKeyAt wp.jIdx).symm
      have hfcj := (hreadAux.stored.ctor wp.jIdx cAj hcAj).1
      rw [hcj_name, hfindAuxC] at hfcj
      obtain ⟨hcvAuxC_eq, -, hcAj_nf⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hfcj)
      have hcj_lps : cAj.1.levelParams = List.range bnl := by
        rw [hAtAux.lpsA cAj (List.mem_of_getElem? hcAj), hfam_lps]
      have hwf_cAj := mp.base2.wf _ (Ix.Kernel.Semantics.Env.find?_mem (hreadAux.stored.ctor wp.jIdx cAj hcAj).1)
      have hpos_cAj : Core.posOf cvAuxC.levelParams cvAuxC.type = cAj.1.type := by
        rw [hcvAuxC_eq, hcj_lps]
        exact posOf_range_eq bnl cAj.1.type (by rw [← hcj_lps]; exact hwf_cAj.2.1)
      rw [hpos_cAj] at hAuxC_P
      have hAuxC_all : cAj.1.type.stripPis (nP + fidx) = some (kbs ++ kfbs, .forallE kfdom kfrest kfbm) :=
        Ix.Kernel.stripPis_append nP hAuxC_P hAuxC_F
      -- `kfdom` has `looseBVarsBounded (nP + fidx)` and `hasFvar = false` (from `mp.base2.wf` on `cAj.1.type`)!
      have hkfdom_bnd : kfdom.looseBVarsBounded (nP + fidx) = true := by
        have h1 := (looseBVarsBounded_stripPis_elem (nP + fidx) 0 hwf_cAj.2.2.2.1 hAuxC_all).2
        simp only [Nat.zero_add, Expr.looseBVarsBounded, Bool.and_eq_true] at h1
        exact h1.1
      have hkfdom_nofv : kfdom.hasFvar = false := by
        have h1 := (hasFvar_stripPis_elem (nP + fidx) hwf_cAj.1 hAuxC_all).2
        simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h1
        exact h1.1
      have hraw_bnd : rawDom.looseBVarsBounded (nP + fidx) = true := by
        rw [← looseBVarsBounded_exprSemEq hkfdom_eq]; exact hkfdom_bnd
      obtain ⟨projKeyAt, frest, fbm, htele⟩ := hprojTele
      have hfdom_eq : fdom = openDummiesP nP 0 fidx rawDom :=
        projFieldTeleAt_noLooseBVar hfidx fp.hC_strip hrawDom_at htele hno_lt hraw_bnd
      have hkfdom_no_lt : ∀ i < fidx, kfdom.hasLooseBVar i = false := fun i hi => by
        rw [hasLooseBVar_exprSemEq hkfdom_eq]; exact hno_lt i hi
      have hkf_open_closed : (openDummiesP nP 0 fidx kfdom).looseBVarsBounded 0 = true :=
        openDummiesP_looseBVarsBounded_zero nP 0 fidx kfdom (by rwa [Nat.add_comm]) hkfdom_no_lt
      have hkf_wscoped : Expr.WScoped nP (openDummiesP nP 0 fidx kfdom) :=
        wscoped_openDummiesP nP 0 fidx kfdom (by omega) (Expr.WScoped.of_not_hasFvar hkfdom_nofv)
      -- Express `openDummiesP (nP + fidx) 0 0 kfdom` as `openDummiesP nP 0 fidx kfdom`!
      have hkf_full_open : openDummiesP (nP + fidx) 0 0 kfdom = openDummiesP nP 0 fidx kfdom := by
        -- `openDummiesP (nP + fidx) 0 0 kfdom = openDummiesP fidx nP 0 (openDummiesP nP 0 fidx kfdom)`!
        have hgo : ∀ (a b d c : Nat) (e : KExpr),
            openDummiesP (a + b) d c e = openDummiesP b (d + a) c (openDummiesP a d (c + b) e) := by
          intro a
          induction a with
          | zero => intro b d c e; simp [openDummiesP]
          | succ a iha =>
            intro b d c e
            rw [show a + 1 + b = (a + b) + 1 by omega]
            simp only [openDummiesP]
            rw [show c + (a + b) = c + b + a by omega, iha b (d + 1) c _,
              show d + 1 + a = d + (a + 1) by omega]
        rw [hgo nP fidx 0 0 kfdom, Nat.zero_add, Nat.zero_add]
        exact openDummiesP_of_looseBVarsBounded_zero fidx nP 0 _ hkf_open_closed
      -- Denote `cAj.1.type` via `hAtAux.ctor wp.jIdx cAj hcAj` and extract `(dsF wp.jIdx ψ_P)[nP + fidx].2.2`!
      have hctor_j := hAtAux.ctor wp.jIdx cAj hcAj
      obtain ⟨dsJ_pre, remJ_pre, hmkJ_pre, hdsJ_pre_len, -, hremJ_pre_den⟩ :=
        denoteMeta_stripPis (nP + fidx) 0 hAuxC_all (hctor_j.read ψ_P)
      simp only [Nat.zero_add] at hremJ_pre_den
      rw [hopen_for] at hremJ_pre_den
      obtain ⟨kfdomA, _, hkfdomA_den, -, hremJ_pi⟩ := denoteMeta_forallE_some hremJ_pre_den
      have hkfdomA_eq_ds : ((dsF wp.jIdx ψ_P)[nP + fidx]'(by rw [hctor_j.len ψ_P, hfam_nP, ← hcAj_nf]; omega)).2.2 = kfdomA := by
        have hds_split : dsF wp.jIdx ψ_P = (dsF wp.jIdx ψ_P).take (nP + fidx) ++ (dsF wp.jIdx ψ_P).drop (nP + fidx) :=
          (List.take_append_drop _ _).symm
        have hdrop_cons : (dsF wp.jIdx ψ_P).drop (nP + fidx) =
            (dsF wp.jIdx ψ_P)[nP + fidx]'(by rw [hctor_j.len ψ_P, hfam_nP, ← hcAj_nf]; omega) ::
            (dsF wp.jIdx ψ_P).drop (nP + fidx + 1) := by
          rw [List.drop_eq_getElem_cons]
        rw [hds_split, hdrop_cons, mkPisAV_append, mkPisAV] at hmkJ_pre
        have hgo : ∀ (l1 l2 : List (Nat × Nat × AnnotTerm)) (b1 b2 : AnnotTerm),
            l1.length = l2.length → mkPisAV l1 b1 = mkPisAV l2 b2 → b1 = b2 := by
          intro l1
          induction l1 with
          | nil => intro l2 _ _ hl h; cases l2 with | nil => exact h | cons _ _ => simp at hl
          | cons _ l1 ih =>
            intro l2 b1 b2 hl h; cases l2 with
            | nil => simp at hl
            | cons _ l2 => simp only [mkPisAV] at h; exact ih l2 b1 b2 (by simpa using hl) (AnnotTerm.pi.inj h).2.2.2
        have hb_eq := hgo dsJ_pre ((dsF wp.jIdx ψ_P).take (nP + fidx)) remJ_pre _
          (by rw [hdsJ_pre_len, List.length_take, hctor_j.len ψ_P, hfam_nP, ← hcAj_nf]; omega) hmkJ_pre.symm
        rw [← hremJ_pi] at hb_eq
        exact (AnnotTerm.pi.inj hb_eq).2.2.1.symm
      -- Show `interp (consList (fs.take fidx) (consList vs_v ρ₀)) kfdomA = interp (consList (vs_v ++ [x_v]) ρ₀) rdomA`!
      rw [hkf_full_open] at hkfdomA_den
      have hkf_base : ∃ fdomA, denoteMeta mp.base2.acval env ψ_P nP (openDummiesP nP 0 fidx kfdom) = some fdomA ∧
          kfdomA = AnnotTerm.liftN fidx fdomA 0 ∧ rdomA = AnnotTerm.liftN 1 fdomA 0 := by
        have hshift_kf := Ix.Kernel.Model.denoteMeta_lift (env := env) (φ := ψ_P) mp.base2.acval_closed
          hkf_wscoped (nP + fidx) (by omega)
        simp only [Nat.add_sub_cancel_left] at hshift_kf
        rw [hshift_kf] at hkfdomA_den
        cases hb0 : denoteMeta mp.base2.acval env ψ_P nP (openDummiesP nP 0 fidx kfdom) with
        | none => simp [hb0] at hkfdomA_den
        | some fdomA =>
          simp only [hb0, Option.map_some, Option.some.injEq] at hkfdomA_den
          -- Relate `rdomA` to `fdomA` via `fp.hProj_rdom` + `hfdom_eq` + `hkfdom_eq`!
          have hr1 := (denoteMeta_exprSemEq (acval := mp.base2.acval) (env := env) (φ := ψ_P)
            (d := nP + 1) (show ExprSemEq (openDummiesP (nP + 1) 0 0 fp.rdom) (openDummiesP nP 0 fidx rawDom) from
              hfdom_eq ▸ fp.hProj_rdom)).symm.trans hrdomA_den
          have hr_same := (denoteMeta_exprSemEq (acval := mp.base2.acval) (env := env) (φ := ψ_P)
            (d := nP + 1) (exprSemEq_openDummiesP hkfdom_eq nP 0 fidx)).trans hr1
          have hshift_r := Ix.Kernel.Model.denoteMeta_lift (env := env) (φ := ψ_P) mp.base2.acval_closed
            hkf_wscoped (nP + 1) (by omega)
          simp only [Nat.add_sub_cancel_left, hb0, Option.map_some] at hshift_r
          rw [hshift_r] at hr_same
          exact ⟨fdomA, rfl, hkfdomA_den.symm, (Option.some.inj hr_same).symm⟩
      obtain ⟨fdomA, -, hkf_lift, hr_lift⟩ := hkf_base
      -- Extract `fs[fidx] ∈ˢ interp (consList (fs.take fidx) (consList vs_v ρ₀)) kfdomA` from `hfitC_j`!
      have hfs_mem_kf : fs[fidx]'(by omega) ∈ˢ
          interp V (consList (fs.take fidx) (consList vs_v ρ₀)) kfdomA := by
        have hsp_get : ∀ (As : List AnnotTerm) (ys : List V) (ρ : Nat → V) (i : Nat)
            (hsp : SpineFit ρ As ys) (hi : i < ys.length),
              ys[i] ∈ˢ interp V (consList (ys.take i) ρ) (As[i]'(by
                have hlen := Ix.Kernel.Semantics.SpineFit.length_eq hsp; omega)) := by
          intro As
          induction As with
          | nil => intro ys ρ i hsp hi; cases ys with | nil => nomatch hi | cons _ _ => exact hsp.elim
          | cons A As ih =>
            intro ys ρ i hsp hi
            cases ys with
            | nil => exact hsp.elim
            | cons y ys =>
              cases i with
              | zero => exact hsp.1
              | succ i' => simpa [consList] using ih ys (cons y ρ) i' hsp.2 (by simpa using hi)
        have hm := hsp_get ((dsF wp.jIdx ψ_P).map (·.2.2)) (vs_v ++ fs) ρ₀ (nP + fidx) hfitC_j
          (by simp [hvs_len, hfs_len]; omega)
        simp only [List.getElem_append_right (by omega : vs_v.length ≤ nP + fidx), hvs_len,
          Nat.add_sub_cancel_left, List.getElem_map] at hm
        have htk : (vs_v ++ fs).take (nP + fidx) = vs_v ++ fs.take fidx := by
          rw [List.take_append, hvs_len, List.take_of_length_le (by omega), Nat.add_sub_cancel_left]
        rw [htk, consList_append, hkfdomA_eq_ds] at hm
        exact hm
      -- Cancel `liftN` on both sides to show `interp ... kfdomA = interp ... rdomA ∈ˢ univZero`!
      have hl_cancel : ∀ (ys : List V) (ρ' : Nat → V) (a : AnnotTerm),
          interp V (consList ys ρ') (AnnotTerm.liftN ys.length a 0) = interp V ρ' a := by
        have hshift : ∀ (ys : List V) (ρ' : Nat → V) (i : Nat),
            shiftE ys.length 0 (consList ys ρ') i = ρ' i := by
          intro ys
          induction ys with
          | nil => intro ρ' i; simp [shiftE, consList]
          | cons y ys ih =>
            intro ρ' i
            simp only [List.length_cons, consList, shiftE, Nat.not_lt_zero, ↓reduceIte]
            rw [show i + (ys.length + 1) = (i + 1) + ys.length by omega]
            have h1 := ih (cons y ρ') (i + 1)
            simp only [shiftE, Nat.not_lt_zero, ↓reduceIte] at h1
            rw [h1]; rfl
        intro ys ρ' a
        rw [interp_liftN, funext (hshift ys ρ')]
      have hset_eq : interp V (consList (fs.take fidx) (consList vs_v ρ₀)) kfdomA =
          interp V (consList (vs_v ++ [x_v]) ρ₀) rdomA := by
        rw [hkf_lift, hr_lift, consList_append]
        have hlen_tk : (fs.take fidx).length = fidx := by rw [List.length_take]; omega
        have h1 := hl_cancel (fs.take fidx) (consList vs_v ρ₀) fdomA
        rw [hlen_tk] at h1
        rw [h1]
        exact (hl_cancel [x_v] (consList vs_v ρ₀) fdomA).symm
      rw [hset_eq] at hfs_mem_kf
      have hfs_pt : fs[fidx]'(by omega) = pt := eq_pt_of_mem_univZero hrdom_zero hfs_mem_kf
      -- Conclude both sides equal `pt`!
      rw [hspec_nil, hproj_x, hfs_pt, hval_pt, Ix.Kernel.SetModel.treeUnpack_nil]
      refine ⟨⟨1, ?_⟩, rfl⟩
      simp only [Ix.Kernel.SetModel.treeUnpackOpt]
      split <;> simp
  · -- **POSITIVE REGIME (`pwBit ψ_P fp.sbm.pw ≠ 0`)**
    -- Unfold `fp.projKey`'s definition `fp.projVal` at `origVal fp.cvProj.levelParams ψ_P`!
    have hP_den : denoteMeta mp.base2.acval env ψ_P 0 (Core.posOf fp.cvProj.levelParams fp.projVal) =
        some (mp.base2.acval fp.projKey (origVal fp.cvProj.levelParams ψ_P)) := by
      rw [posOf_denoteMeta]
      have h := mp.defn_reads (origVal fp.cvProj.levelParams ψ_P) fp.cvProj fp.projVal
        ⟨fp.projHint, Ix.Kernel.Semantics.Env.find?_mem fp.hfindProj⟩
      have hn : fp.cvProj.name = fp.projKey := Ix.Kernel.Semantics.Env.find?_name fp.hfindProj
      rwa [hn] at h
    -- Handle `.direct` and `.viaDefn` cases of `wp.hbody`!
    have hhandle_minor :
        ∀ {pheadLvls : List KLevel} {rbsJ : List (KExpr × BinderMeta)} {rargsJ : List KExpr}
          {mbsJ : List (KExpr × BinderMeta)} {mbody minorJ : KExpr} {minorJA : AnnotTerm}
          {rlJ : RecRule .anon} {xs_v : List V},
          pheadLvls.length = bnl + 1 →
          (∀ φ, (pheadLvls.getD 0 .zero).eval φ = 0 ↔ pwBit φ fp.sbm.pw = 0) →
          LvEqList (pheadLvls.drop 1) ((List.range bnl).map .param) →
          wp.arules[wp.jIdx]? = some rlJ →
          rlJ.nfields = nF →
          (Core.posOf wp.cvAuxRec.levelParams rlJ.rhs).stripLams (nP + 1 + wp.anc + nF) =
            some (rbsJ, Expr.mkAppN (.bvar (nF + wp.anc - 1 - wp.jIdx)) rargsJ) →
          nF ≤ rargsJ.length →
          List.Forall₂ ExprSemEq (rargsJ.take nF) ((List.range nF).map fun m => .bvar (nF - 1 - m)) →
          minorJ.stripLams (nF + (rargsJ.length - nF)) = some (mbsJ, mbody) →
          (∀ bm ∈ mbsJ, bm.2.pw = fp.sbm.pw) →
          (hminor : ProjMinorWitness t E env wp.auxKey wp.auxRecKey wp.cvAuxRec.levelParams
            wp.arules wp.auxCtorKeyAt fp.sbm.pw nP bnl wp.anc nF (rargsJ.length - nF) fidx mbody) →
          spec = minorUnpackSpec hminor →
          denoteMeta mp.base2.acval env ψ_P (nP + 1) (openDummiesP (nP + 1) 0 0 minorJ) = some minorJA →
          WellDenotedV V (consList (vs_v ++ [x_v]) ρ₀) minorJA →
          (hxs_len : xs_v.length = nP + 1 + wp.anc + 1) →
          xs_v.take nP = vs_v →
          xs_v[nP + 1 + wp.jIdx]'(by have := wp.hjIdx_lt; omega) =
            interp V (consList (vs_v ++ [x_v]) ρ₀) minorJA →
          (vs_v ++ [x_v]).foldl SetTheory.app
            (interp V ρ₀ (mp.base2.acval fp.projKey (origVal fp.cvProj.levelParams ψ_P))) =
            (xs_v ++ [x_v]).foldl SetTheory.app
              (interp V ρ₀ (mp.base2.acval wp.auxRecKey (origVal wp.cvAuxRec.levelParams (ψ_rec pheadLvls bnl ψ_P)))) →
          AppChainOk (interp V ρ₀ (mp.base2.acval wp.auxRecKey
            (origVal wp.cvAuxRec.levelParams (ψ_rec pheadLvls bnl ψ_P)))) (xs_v ++ [x_v]) →
          (∃ N, Ix.Kernel.SetModel.treeUnpackOpt spec N (projS (fidx + 1) x_v) =
            some (Ix.Kernel.SetModel.treeUnpack spec (projS (fidx + 1) x_v))) ∧
          (vs_v ++ [x_v]).foldl SetTheory.app
            (interp V ρ₀ (mp.base2.acval fp.projKey (origVal fp.cvProj.levelParams ψ_P))) =
            Ix.Kernel.SetModel.treeUnpack spec (projS (fidx + 1) x_v) := by
      intro pheadLvls rbsJ rargsJ mbsJ mbody minorJ minorJA rlJ xs_v
        hpl_len hpl_elim hpl_drop hrlJ hrlJ_nf hrlJ_strip hrargsJ_ge hrargsJ_fields
        hminJ_strip hminJ_pw hminor hspec_eq hden_minJ hwd_minJ hxs_len hxs_pref hxs_minJ hval_rec hApp_rec
      -- Fire `auxRec_fire` on `(xs_v, vs_v, fs)` at `wp.jIdx`!
      have helim_pos : (pheadLvls.getD 0 .zero).eval ψ_P > 0 := by
        have hne : (pheadLvls.getD 0 .zero).eval ψ_P ≠ 0 := fun h => hpw0 ((hpl_elim ψ_P).mp h)
        omega
      have hfitC_orig : SpineFit ρ₀ ((dsF wp.jIdx (origVal famAux.p.cvT.levelParams ψ_P)).map (·.2.2)) (vs_v ++ fs) := by
        rwa [horig_fam]
      have hApp_rec' : AppChainOk (interp V ρ₀ (mp.base2.acval wp.auxRecKey
          (origVal wp.cvAuxRec.levelParams (ψ_rec pheadLvls bnl ψ_P))))
          (xs_v ++ [inj wp.jIdx (mkTower (fs ++ [pt]))]) := hx_eq ▸ hApp_rec
      obtain ⟨rbodyJA, rargsJA, -, hrbodyJA_eq, hsp_rargsJ, hfireJ_eq, hwd_rbodyJ⟩ :=
        auxRec_fire ht hbasis hreg mp hN wp.auxIndWit wp.hauxInd_lvls wp.hauxInd_idx wp.hauxInd_rec
          ⟨wp.auxSortBs, wp.auxSortU, wp.hauxInd_sort, wp.hauxInd_nz⟩
          wp.hfindAuxRec wp.hAuxRec_lvls wp.hAuxRec_perm wp.hauxRec_famBlk
          ⟨wp.majBs, wp.majDom, wp.majBody, wp.majBm, wp.majLvls, wp.majArgs,
            wp.hAuxRec_maj, wp.hmajDom, wp.hmajLvls, wp.hmajArgs_len, wp.hmajArgs_pref, wp.hmajArgs_idx⟩
          (fun j rl h => (wp.hrecCtor j rl h).trans (wp.hauxCtorKeyAt j))
          hregAux hnameAux' hAtAux wp.hjIdx_lt hrlJ (by rwa [hrlJ_nf])
          ψ_P pheadLvls hpl_len hpl_drop helim_pos xs_v vs_v fs ρ₀ hxs_len hvs_len (by omega)
          hxs_pref hfitC_orig hApp_rec'
      rw [hrbodyJA_eq] at hfireJ_eq hwd_rbodyJ
      obtain ⟨-, -, hApp_minJ⟩ := appChainOk_of_wellDenotedV rargsJA hwd_rbodyJ
      rw [interp_mkAppN_foldl] at hfireJ_eq
      have hminJ_lookup : interp V (consList (xs_v.take (nP + 1 + wp.anc) ++ fs) ρ₀)
          (.bvar (rlJ.nfields + wp.anc - 1 - wp.jIdx)) =
          interp V (consList (vs_v ++ [x_v]) ρ₀) minorJA := by
        rw [interp_bvar, ← hxs_minJ]
        have hlen_tk : (xs_v.take (nP + 1 + wp.anc)).length = nP + 1 + wp.anc := by
          rw [List.length_take, hxs_len]; omega
        rw [show rlJ.nfields + wp.anc - 1 - wp.jIdx =
            (xs_v.take (nP + 1 + wp.anc) ++ fs).length - 1 - (nP + 1 + wp.jIdx) by
          rw [List.length_append, hlen_tk, hfs_len, hrlJ_nf]; have := wp.hjIdx_lt; omega]
        rw [consList_bvar_desc _ ρ₀ (by rw [List.length_append, hlen_tk]; have := wp.hjIdx_lt; omega),
          List.getElem_append_left (by rw [hlen_tk]; have := wp.hjIdx_lt; omega), List.getElem_take]
      rw [hminJ_lookup] at hfireJ_eq hApp_minJ
      let rargsJV := rargsJA.map (interp V (consList (xs_v.take (nP + 1 + wp.anc) ++ fs) ρ₀))
      have hrargsJA_len : rargsJA.length = rargsJ.length := by
        have := denoteMetaSpine_length_eq hsp_rargsJ; simpa using this.symm
      have hrargsJV_take : rargsJV.take nF = fs := by
        refine List.ext_getElem (by rw [List.length_take, List.length_map, hrargsJA_len, hfs_len]; omega) fun m hm1 hm2 => ?_
        rw [List.getElem_take]; simp only [rargsJV, List.getElem_map]
        have hden_m := denoteMetaSpine_getElem hsp_rargsJ (i := m) (by simp; omega)
        simp only [List.getElem_map] at hden_m
        have heq_m : ExprSemEq (rargsJ[m]'(by omega)) (.bvar (nF - 1 - m)) := by
          have := forall₂_getElem hrargsJ_fields m
            (by rw [List.length_take]; omega) (by simp; omega)
          simpa [List.getElem_take] using this
        have hden_bv : denoteMeta mp.base2.acval env (ψ_rec pheadLvls bnl ψ_P) (nP + 1 + wp.anc + rlJ.nfields)
            (openDummiesP (nP + 1 + wp.anc + rlJ.nfields) 0 0 (.bvar (nF - 1 - m))) =
            some (.bvar (nF - 1 - m)) := denoteMeta_openDummiesP_bvar0 (by rw [hrlJ_nf]; omega)
        have hsame := (denoteMeta_exprSemEq (acval := mp.base2.acval) (env := env)
          (φ := ψ_rec pheadLvls bnl ψ_P) (d := nP + 1 + wp.anc + rlJ.nfields)
          (exprSemEq_openDummiesP heq_m _ 0 0)).symm.trans hden_m
        rw [hden_bv] at hsame
        rw [(Option.some.inj hsame).symm, interp_bvar, consList_append,
          show nF - 1 - m = fs.length - 1 - m by omega]
        exact consList_bvar_desc fs _ (by omega)
      -- Strip `nF + (rargsJ.length - nF)` positive lambdas from `minorJ`!
      have hminJ_open : ∃ (mbsJO : List (KExpr × BinderMeta)) (hlen : mbsJO.length = mbsJ.length),
          (openDummiesP (nP + 1) 0 0 minorJ).stripLams (nF + (rargsJ.length - nF)) =
          some (mbsJO, openDummiesP (nP + 1) 0 (nF + (rargsJ.length - nF)) mbody) ∧
          ∀ i (hi : i < mbsJ.length), (mbsJO[i]'(hlen.symm ▸ hi)).2.pw = mbsJ[i].2.pw := by
        have hgo : ∀ (m d c n : Nat) {e body : KExpr} {bs : List (KExpr × BinderMeta)},
            e.stripLams n = some (bs, body) →
            ∃ (bs' : List (KExpr × BinderMeta)) (hlen : bs'.length = bs.length),
              (openDummiesP m d c e).stripLams n = some (bs', openDummiesP m d (c + n) body) ∧
              ∀ i (hi : i < bs.length), (bs'[i]'(hlen.symm ▸ hi)).2.pw = bs[i].2.pw := by
          intro m
          induction m with
          | zero => intro d c n e body bs hs; exact ⟨bs, rfl, hs, fun _ _ => rfl⟩
          | succ m ih =>
            intro d c n e body bs hs
            have h1 : ∀ (v : KExpr) (n c : Nat) {e body : KExpr} {bs : List (KExpr × BinderMeta)},
                e.stripLams n = some (bs, body) →
                ∃ (bs' : List (KExpr × BinderMeta)) (hlen : bs'.length = bs.length),
                  (e.instantiate1 v c).stripLams n = some (bs', body.instantiate1 v (c + n)) ∧
                  ∀ i (hi : i < bs.length), (bs'[i]'(hlen.symm ▸ hi)).2.pw = bs[i].2.pw := by
              intro v n
              induction n with
              | zero =>
                intro c e body bs hs; simp only [Expr.stripLams, Option.some.injEq, Prod.mk.injEq] at hs
                obtain ⟨rfl, rfl⟩ := hs; exact ⟨[], rfl, by simp [Expr.stripLams], fun _ hi => nomatch hi⟩
              | succ n ihn =>
                intro c e body bs hs
                cases e with
                | lam ty b bm =>
                  simp only [Expr.stripLams, Option.map_eq_some_iff] at hs
                  obtain ⟨⟨bs₀, b₀⟩, hsb, hp⟩ := hs; obtain ⟨hbs, hb0⟩ := Prod.mk.inj hp; subst hb0
                  obtain ⟨bs', hlen', hbs', hpw'⟩ := ihn (c + 1) hsb
                  refine ⟨(ty.instantiate1 v c, bm) :: bs', by rw [← hbs]; simp [hlen'], ?_, ?_⟩
                  · simp only [Expr.instantiate1, Expr.stripLams, hbs', Option.map_some]
                    rw [show c + 1 + n = c + (n + 1) by omega]
                  · intro i hi; subst hbs; cases i with
                    | zero => rfl
                    | succ i' => exact hpw' i' (by simpa using hi)
                | _ => simp [Expr.stripLams] at hs
            obtain ⟨bs1, hlen1, hbs1, hpw1⟩ := h1 (.fvar d (.sort .zero)) n (c + m) hs
            obtain ⟨bs2, hlen2, hbs2, hpw2⟩ := ih (d + 1) c n hbs1
            refine ⟨bs2, hlen2.trans hlen1, ?_, fun i hi => (hpw2 i (hlen1.symm ▸ hi)).trans (hpw1 i hi)⟩
            simpa [openDummiesP, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbs2
        simpa [Nat.zero_add] using hgo (nP + 1) 0 0 (nF + (rargsJ.length - nF)) hminJ_strip
      obtain ⟨mbsJO, hmbsJO_len, hminJ_stripO, hmbsJO_pw⟩ := hminJ_open
      obtain ⟨mdsJ, mbodyJA, hminJ_mk, hmdsJ_len, hmdsJ_bits, hmbodyJA_den⟩ :=
        denoteMeta_stripLams (nF + (rargsJ.length - nF)) (nP + 1) hminJ_stripO hden_minJ
      have hmbsJ_len : mbsJ.length = nF + (rargsJ.length - nF) := stripLams_length hminJ_strip
      have hnz_mdsJ : ∀ p ∈ mdsJ, p.1 ≠ 0 := by
        intro p hp
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
        have hbi := map_getElem_eq hmdsJ_bits i hi (by omega)
        have hpwi := hmbsJO_pw i (by omega)
        have hs := hminJ_pw (mbsJ[i]'(by omega)) (List.getElem_mem _)
        rw [hbi, hpwi, hs]; exact hpw0
      rw [hminJ_mk] at hwd_minJ hApp_minJ hfireJ_eq
      have hrargsJV_len : rargsJV.length = nF + (rargsJ.length - nF) := by
        simp [rargsJV, hrargsJA_len]; omega
      obtain ⟨hfold_minJ, -, hwd_mbodyJ⟩ := mkLamsAV_appChainOk_pos mdsJ mbodyJA rargsJV
        (consList (vs_v ++ [x_v]) ρ₀) hnz_mdsJ (by rw [hmdsJ_len, hrargsJV_len]) hwd_minJ hApp_minJ
      have hval_mbody : (vs_v ++ [x_v]).foldl SetTheory.app
          (interp V ρ₀ (mp.base2.acval fp.projKey (origVal fp.cvProj.levelParams ψ_P))) =
          interp V (consList rargsJV (consList (vs_v ++ [x_v]) ρ₀)) mbodyJA := by
        rw [hval_rec]
        conv_lhs => rw [hx_eq]
        rw [hfireJ_eq, hfold_minJ]
      -- Case split on `hminor` (`.bvar` vs `.unpack`)!
      have hspec_mbody : spec = mbodyUnpackSpec (t := t) (E := E) (env := env) (auxKey := wp.auxKey)
          (auxRecKey := wp.auxRecKey) (auxRecLps := wp.cvAuxRec.levelParams) (arules := wp.arules)
          (auxCtorKeyAt := wp.auxCtorKeyAt) (nP := nP) (bnl := bnl) (anc := wp.anc) mbody :=
        hspec_eq.trans (mbodyUnpackSpec_eq_minorUnpackSpec hminor).symm
      cases hminor with
      | bvar hmbody =>
        have hsp_nil : spec = [] := by
          rw [hspec_mbody, hmbody]; exact mbodyUnpackSpec_bvar
        rw [hsp_nil, hproj_x, Ix.Kernel.SetModel.treeUnpack_nil]
        refine ⟨⟨1, by simp only [Ix.Kernel.SetModel.treeUnpackOpt]; split <;> simp⟩, ?_⟩
        rw [hmbody, show openDummiesP (nF + (rargsJ.length - nF)) (nP + 1) 0
            (openDummiesP (nP + 1) 0 (nF + (rargsJ.length - nF)) (.bvar (rargsJ.length - nF + nF - 1 - fidx))) =
            openDummiesP ((nP + 1) + (nF + (rargsJ.length - nF))) 0 0 (.bvar (rargsJ.length - nF + nF - 1 - fidx)) by
          simpa [Nat.zero_add] using
            (openDummiesP_add (nP + 1) (nF + (rargsJ.length - nF)) 0
              (.bvar (rargsJ.length - nF + nF - 1 - fidx))).symm] at hmbodyJA_den
        have hden_bv : denoteMeta mp.base2.acval env ψ_P ((nP + 1) + (nF + (rargsJ.length - nF)))
            (openDummiesP ((nP + 1) + (nF + (rargsJ.length - nF))) 0 0
              (.bvar (rargsJ.length - nF + nF - 1 - fidx))) =
            some (.bvar (rargsJ.length - nF + nF - 1 - fidx)) :=
          denoteMeta_openDummiesP_bvar0 (by omega)
        rw [hden_bv] at hmbodyJA_den
        rw [hval_mbody, ← Option.some.inj hmbodyJA_den, interp_bvar,
          show rargsJ.length - nF + nF - 1 - fidx = rargsJV.length - 1 - fidx by omega,
          consList_bvar_desc rargsJV _ (by omega)]
        have hget := congrArg (fun l => l[fidx]?) hrargsJV_take
        rw [List.getElem?_take_of_lt hfidx, List.getElem?_eq_getElem (by omega : fidx < rargsJV.length),
          List.getElem?_eq_getElem (by omega : fidx < fs.length)] at hget
        exact Option.some.inj hget
      | unpack hsbl_nz uKey cvU uval uHint uLvls uargs uaKey cvUA uaval uaHint ubs uaLvls uaArgs
          uabs uarLvls uarArgs hmbody hU_nonAux hfindU hU_lvls hU_perm huLvls huargs_gt huargs_pref
          huargs_last hu_strip hu_pw hUA_nonAux hfindUA hUA_lvls hUA_perm huaLvls hua_len hua_pref
          hua_last hua_strip hua_pw huar_lvls_len huar_elim_nz huar_lvls_drop huar_len huar_pref
          hminors =>
        have hminors_key : ∀ k (hk : k < wp.anc), ∃ rl, wp.arules[k]? = some rl ∧
            Nonempty (UnpackMinorWitness t E env wp.auxKey wp.auxRecKey wp.cvAuxRec.levelParams
              (Core.keyOf t (Core.cprjAddr wp.auxIndWit.ip.block 0 k)) nP bnl wp.anc k
              (uarArgs.drop (nP + 1) |>.getD k default) rl) := by
          intro k hk; simpa [wp.hauxCtorKeyAt k] using hminors k hk
        have hsp_eq : spec = unpackSpecOf hminors_key := by
          rw [hspec_mbody]
          have hminor' : ProjMinorWitness t E env wp.auxKey wp.auxRecKey wp.cvAuxRec.levelParams
              wp.arules wp.auxCtorKeyAt fp.sbm.pw nP bnl wp.anc nF (rargsJ.length - nF) fidx mbody :=
            .unpack hsbl_nz uKey cvU uval uHint uLvls uargs uaKey cvUA uaval uaHint ubs uaLvls uaArgs
              uabs uarLvls uarArgs hmbody hU_nonAux hfindU hU_lvls hU_perm huLvls huargs_gt huargs_pref
              huargs_last hu_strip hu_pw hUA_nonAux hfindUA hUA_lvls hUA_perm huaLvls hua_len hua_pref
              hua_last hua_strip hua_pw huar_lvls_len huar_elim_nz huar_lvls_drop huar_len huar_pref
              hminors
          have h1 := (mbodyUnpackSpec_eq_minorUnpackSpec hminor').trans
            (minorUnpackSpec_unpack hminor' hmbody hfindU hu_strip hfindUA hua_strip hminors)
          rw [h1]
          have hcongr : ∀ (f1 f2 : Nat → KKey)
              (hf1 : ∀ k (hk : k < wp.anc), ∃ rl, wp.arules[k]? = some rl ∧
                Nonempty (UnpackMinorWitness t E env wp.auxKey wp.auxRecKey wp.cvAuxRec.levelParams
                  (f1 k) nP bnl wp.anc k (uarArgs.drop (nP + 1) |>.getD k default) rl))
              (hf2 : ∀ k (hk : k < wp.anc), ∃ rl, wp.arules[k]? = some rl ∧
                Nonempty (UnpackMinorWitness t E env wp.auxKey wp.auxRecKey wp.cvAuxRec.levelParams
                  (f2 k) nP bnl wp.anc k (uarArgs.drop (nP + 1) |>.getD k default) rl)),
              f1 = f2 → unpackSpecOf hf1 = unpackSpecOf hf2 := by
            rintro f1 _ hf1 hf2 rfl; rfl
          exact hcongr _ _ hminors hminors_key (funext wp.hauxCtorKeyAt)
        -- 1. Evaluate `mbodyJA = mkAppN (acval uKey (origVal cvU.levelParams ψ_P)) uargsA`!
        rw [hmbody, show openDummiesP (nF + (rargsJ.length - nF)) (nP + 1) 0
            (openDummiesP (nP + 1) 0 (nF + (rargsJ.length - nF)) (Expr.mkAppN (.const uKey uLvls) uargs)) =
            openDummiesP ((nP + 1) + (nF + (rargsJ.length - nF))) 0 0 (Expr.mkAppN (.const uKey uLvls) uargs) by
          simpa [Nat.zero_add] using
            (openDummiesP_add (nP + 1) (nF + (rargsJ.length - nF)) 0
              (Expr.mkAppN (.const uKey uLvls) uargs)).symm,
          openDummiesP_mkAppN, openDummiesP_const] at hmbodyJA_den
        obtain ⟨fuA, uargsA, hfuA, hsp_uargs, hmbodyJA_eq⟩ := denoteMeta_mkAppN_inv hmbodyJA_den
        have huLvls_len : uLvls.length = cvU.levelParams.length := by
          have h1 := (lvEqList_getElem huLvls).1; rw [hU_lvls]; simpa using h1
        simp only [denoteMeta, hfindU, ConstantInfo.toConstantVal, huLvls_len, ↓reduceIte, Option.some.injEq] at hfuA
        have hfuA_eq : fuA = mp.base2.acval uKey (origVal cvU.levelParams ψ_P) := by
          rw [← hfuA, substFn_eq_of_lvEqList huLvls ψ_P]
          refine mp.base2.acval_params uKey _ hfindU _ _ fun q _ => ?_
          simp [origVal, Core.posLevels, hU_lvls]
        rw [hmbodyJA_eq, hfuA_eq] at hval_mbody hwd_mbodyJ
        obtain ⟨-, -, hApp_u_raw⟩ := appChainOk_of_wellDenotedV uargsA hwd_mbodyJ
        let uargsV := uargsA.map (interp V (consList rargsJV (consList (vs_v ++ [x_v]) ρ₀)))
        have huargsA_len : uargsA.length = uargs.length := by
          have := denoteMetaSpine_length_eq hsp_uargs; simpa using this.symm
        have huargsV_len : uargsV.length = uargs.length := by simp [uargsV, huargsA_len]
        have huargsV_pref : uargsV.take nP = vs_v := by
          refine List.ext_getElem (by rw [List.length_take, huargsV_len, hvs_len]; omega) fun m hm1 hm2 => ?_
          rw [List.getElem_take]; simp only [uargsV, List.getElem_map]
          have hden_m := denoteMetaSpine_getElem hsp_uargs (i := m) (by simp; omega)
          simp only [List.getElem_map] at hden_m
          have heq_m : ExprSemEq (uargs[m]'(by omega))
              (.bvar (nP + 1 + nF + (rargsJ.length - nF) - 1 - m)) := by
            have := forall₂_getElem huargs_pref m
              (by rw [List.length_take]; omega) (by simp; omega)
            simpa [List.getElem_take] using this
          have hden_bv : denoteMeta mp.base2.acval env ψ_P ((nP + 1) + (nF + (rargsJ.length - nF)))
              (openDummiesP ((nP + 1) + (nF + (rargsJ.length - nF))) 0 0
                (.bvar (nP + 1 + nF + (rargsJ.length - nF) - 1 - m))) =
              some (.bvar (nP + 1 + nF + (rargsJ.length - nF) - 1 - m)) :=
            denoteMeta_openDummiesP_bvar0 (by omega)
          have hsame := (denoteMeta_exprSemEq (acval := mp.base2.acval) (env := env) (φ := ψ_P)
            (d := (nP + 1) + (nF + (rargsJ.length - nF)))
            (exprSemEq_openDummiesP heq_m _ 0 0)).symm.trans hden_m
          rw [hden_bv] at hsame
          rw [(Option.some.inj hsame).symm, interp_bvar, ← consList_append,
            show nP + 1 + nF + (rargsJ.length - nF) - 1 - m = ((vs_v ++ [x_v]) ++ rargsJV).length - 1 - m by
              simp [hvs_len, hrargsJV_len]; omega,
            consList_bvar_desc ((vs_v ++ [x_v]) ++ rargsJV) ρ₀ (by simp [hvs_len]; omega),
            List.getElem_append_left (by simp [hvs_len]; omega),
            List.getElem_append_left (by omega : m < vs_v.length)]
        have huargsV_last : uargsV[uargsV.length - 1]'(by omega) = fs[fidx]'(by omega) := by
          simp only [uargsV, List.getElem_map, List.length_map]
          have hden_last := denoteMetaSpine_getElem hsp_uargs (i := uargs.length - 1) (by simp; omega)
          simp only [List.getElem_map] at hden_last
          have hlast_eq : uargs[uargs.length - 1]'(by omega) = .bvar (rargsJ.length - nF + nF - 1 - fidx) := by
            rw [List.getElem?_eq_getElem (by omega : uargs.length - 1 < uargs.length)] at huargs_last
            exact Option.some.inj huargs_last
          rw [hlast_eq] at hden_last
          have hden_bv : denoteMeta mp.base2.acval env ψ_P ((nP + 1) + (nF + (rargsJ.length - nF)))
              (openDummiesP ((nP + 1) + (nF + (rargsJ.length - nF))) 0 0
                (.bvar (rargsJ.length - nF + nF - 1 - fidx))) =
              some (.bvar (rargsJ.length - nF + nF - 1 - fidx)) :=
            denoteMeta_openDummiesP_bvar0 (by omega)
          rw [hden_bv] at hden_last
          have hidx_last : uargsA.length - 1 = uargs.length - 1 := by omega
          simp only [hidx_last]
          rw [(Option.some.inj hden_last).symm, interp_bvar,
            show rargsJ.length - nF + nF - 1 - fidx = rargsJV.length - 1 - fidx by omega,
            consList_bvar_desc rargsJV _ (by omega)]
          have hget := congrArg (fun l => l[fidx]?) hrargsJV_take
          rw [List.getElem?_take_of_lt hfidx, List.getElem?_eq_getElem (by omega : fidx < rargsJV.length),
            List.getElem?_eq_getElem (by omega : fidx < fs.length)] at hget
          exact Option.some.inj hget
        -- 2. Peel `uval`'s `uargs.length` positive lambdas (`hu_strip` + `hu_pw`)!
        have hU_den : denoteMeta mp.base2.acval env ψ_P 0 (Core.posOf cvU.levelParams uval) =
            some (mp.base2.acval uKey (origVal cvU.levelParams ψ_P)) := by
          rw [posOf_denoteMeta]
          have h := mp.defn_reads (origVal cvU.levelParams ψ_P) cvU uval
            ⟨uHint, Ix.Kernel.Semantics.Env.find?_mem hfindU⟩
          have hn : cvU.name = uKey := Ix.Kernel.Semantics.Env.find?_name hfindU
          rwa [hn] at h
        obtain ⟨uDs, uBodyA, hU_mk, huDs_len, huDs_bits, huBodyA_den⟩ :=
          denoteMeta_stripLams uargs.length 0 hu_strip hU_den
        simp only [Nat.zero_add] at huBodyA_den
        have hnz_uDs : ∀ p ∈ uDs, p.1 ≠ 0 := by
          intro p hp
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
          have hbi := map_getElem_eq huDs_bits i hi (by rw [stripLams_length hu_strip]; omega)
          have hnev := hu_pw (ubs[i]'(by rw [stripLams_length hu_strip]; omega)) (List.getElem_mem _)
          rw [hbi, hnev]; simp [pwBit]
        have hcl_u : interp V (consList rargsJV (consList (vs_v ++ [x_v]) ρ₀))
            (mp.base2.acval uKey (origVal cvU.levelParams ψ_P)) =
            interp V ρ₀ (mp.base2.acval uKey (origVal cvU.levelParams ψ_P)) :=
          closed_interp_env (mp.base2.acval_closed _ _) _ _
        rw [interp_mkAppN_foldl, hcl_u, hU_mk] at hval_mbody
        rw [hcl_u, hU_mk] at hApp_u_raw
        have hwd_U : WellDenotedV V ρ₀ (mkLamsAV uDs uBodyA) := by
          rw [← hU_mk]; exact ⟨mp.base2.acval_wellDenoted _ _ _, mp.acval_validV _ _ _⟩
        obtain ⟨hfold_U, -, hwd_uBody⟩ := mkLamsAV_appChainOk_pos uDs uBodyA uargsV ρ₀ hnz_uDs
          (by rw [huDs_len, huargsV_len]) hwd_U hApp_u_raw
        rw [hfold_U] at hval_mbody
        -- 3. Evaluate `uBodyA = mkAppN (acval uaKey (origVal cvUA.levelParams ψ_P)) uaArgsA`!
        rw [openDummiesP_mkAppN, openDummiesP_const] at huBodyA_den
        obtain ⟨fuaA, uaArgsA, hfuaA, hsp_uaArgs, huBodyA_eq⟩ := denoteMeta_mkAppN_inv huBodyA_den
        have huaLvls_len : uaLvls.length = cvUA.levelParams.length := by
          have h1 := (lvEqList_getElem huaLvls).1; rw [hUA_lvls]; simpa using h1
        simp only [denoteMeta, hfindUA, ConstantInfo.toConstantVal, huaLvls_len, ↓reduceIte, Option.some.injEq] at hfuaA
        have hfuaA_eq : fuaA = mp.base2.acval uaKey (origVal cvUA.levelParams ψ_P) := by
          rw [← hfuaA, substFn_eq_of_lvEqList huaLvls ψ_P]
          refine mp.base2.acval_params uaKey _ hfindUA _ _ fun q _ => ?_
          simp [origVal, Core.posLevels, hUA_lvls]
        rw [huBodyA_eq, hfuaA_eq] at hval_mbody hwd_uBody
        obtain ⟨-, -, hApp_ua_raw⟩ := appChainOk_of_wellDenotedV uaArgsA hwd_uBody
        let uaArgsV := uaArgsA.map (interp V (consList uargsV ρ₀))
        have huaArgsA_len : uaArgsA.length = nP + 2 := by
          have := denoteMetaSpine_length_eq hsp_uaArgs; simp only [List.length_map, hua_len] at this; exact this.symm
        let t_ua := uaArgsV[nP]'(by simp [uaArgsV, huaArgsA_len])
        have huaArgsV_eq : uaArgsV = vs_v ++ [t_ua, fs[fidx]'(by omega)] := by
          refine List.ext_getElem (by simp [uaArgsV, huaArgsA_len, hvs_len]) fun m hm1 hm2 => ?_
          by_cases hmP : m < nP
          · simp only [uaArgsV, List.getElem_map]
            have hden_m := denoteMetaSpine_getElem hsp_uaArgs (i := m) (by simp [hua_len]; omega)
            simp only [List.getElem_map] at hden_m
            have heq_m : ExprSemEq (uaArgs[m]'(by omega)) (.bvar (uargs.length - 1 - m)) := by
              have := forall₂_getElem hua_pref m
                (by rw [List.length_take, hua_len]; omega) (by simp; omega)
              simpa [List.getElem_take] using this
            have hden_bv : denoteMeta mp.base2.acval env ψ_P uargs.length
                (openDummiesP uargs.length 0 0 (.bvar (uargs.length - 1 - m))) =
                some (.bvar (uargs.length - 1 - m)) := denoteMeta_openDummiesP_bvar0 (by omega)
            have hsame := (denoteMeta_exprSemEq (acval := mp.base2.acval) (env := env) (φ := ψ_P)
              (d := uargs.length) (exprSemEq_openDummiesP heq_m _ 0 0)).symm.trans hden_m
            rw [hden_bv] at hsame
            rw [(Option.some.inj hsame).symm, interp_bvar, show uargs.length - 1 - m = uargsV.length - 1 - m by omega,
              consList_bvar_desc uargsV ρ₀ (by omega), List.getElem_append_left (by omega : m < vs_v.length)]
            have hget := congrArg (fun l => l[m]?) huargsV_pref
            rw [List.getElem?_take_of_lt hmP, List.getElem?_eq_getElem (by omega : m < uargsV.length),
              List.getElem?_eq_getElem (by omega : m < vs_v.length)] at hget
            exact Option.some.inj hget
          · by_cases hm_idx : m = nP
            · subst m
              rw [List.getElem_append_right (by omega : vs_v.length ≤ nP)]
              simp [hvs_len, t_ua]
            · have hm_last : m = nP + 1 := by simp [uaArgsV, huaArgsA_len] at hm1; omega
              subst m
              rw [List.getElem_append_right (by omega : vs_v.length ≤ nP + 1)]
              simp only [hvs_len, show nP + 1 - nP = 1 by omega, List.getElem_cons_succ, List.getElem_cons_zero]
              simp only [uaArgsV, List.getElem_map]
              have hden_l := denoteMetaSpine_getElem hsp_uaArgs (i := nP + 1) (by simp [hua_len])
              simp only [List.getElem_map] at hden_l
              have hlast_eq : uaArgs[nP + 1]'(by omega) = .bvar 0 := by
                rw [List.getElem?_eq_getElem (by omega : nP + 1 < uaArgs.length)] at hua_last
                exact Option.some.inj hua_last
              rw [hlast_eq] at hden_l
              have hden_bv : denoteMeta mp.base2.acval env ψ_P uargs.length
                  (openDummiesP uargs.length 0 0 (.bvar 0)) = some (.bvar 0) :=
                denoteMeta_openDummiesP_bvar0 (by omega)
              rw [hden_bv] at hden_l
              rw [(Option.some.inj hden_l).symm, interp_bvar,
                show 0 = uargsV.length - 1 - (uargsV.length - 1) by omega,
                consList_bvar_desc uargsV ρ₀ (by omega)]
              exact huargsV_last
        -- 4. Peel `uaval`'s `nP` positive lambdas (`hua_strip` + `hua_pw`)!
        have hUA_den : denoteMeta mp.base2.acval env ψ_P 0 (Core.posOf cvUA.levelParams uaval) =
            some (mp.base2.acval uaKey (origVal cvUA.levelParams ψ_P)) := by
          rw [posOf_denoteMeta]
          have h := mp.defn_reads (origVal cvUA.levelParams ψ_P) cvUA uaval
            ⟨uaHint, Ix.Kernel.Semantics.Env.find?_mem hfindUA⟩
          have hn : cvUA.name = uaKey := Ix.Kernel.Semantics.Env.find?_name hfindUA
          rwa [hn] at h
        obtain ⟨uaDs, uaBodyA, hUA_mk, huaDs_len, huaDs_bits, huaBodyA_den⟩ :=
          denoteMeta_stripLams nP 0 hua_strip hUA_den
        simp only [Nat.zero_add] at huaBodyA_den
        have hnz_uaDs : ∀ p ∈ uaDs, p.1 ≠ 0 := by
          intro p hp
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
          have hbi := map_getElem_eq huaDs_bits i hi (by rw [stripLams_length hua_strip]; omega)
          have hnev := hua_pw (uabs[i]'(by rw [stripLams_length hua_strip]; omega)) (List.getElem_mem _)
          rw [hbi, hnev]; simp [pwBit]
        have hcl_ua : interp V (consList uargsV ρ₀) (mp.base2.acval uaKey (origVal cvUA.levelParams ψ_P)) =
            interp V ρ₀ (mp.base2.acval uaKey (origVal cvUA.levelParams ψ_P)) :=
          closed_interp_env (mp.base2.acval_closed _ _) _ _
        rw [interp_mkAppN_foldl] at hval_mbody
        change _ = uaArgsV.foldl SetTheory.app _ at hval_mbody
        change AppChainOk _ uaArgsV at hApp_ua_raw
        rw [huaArgsV_eq, hcl_ua, hUA_mk] at hval_mbody hApp_ua_raw
        have hApp_ua_split := (AppChainOk.append (F := interp V ρ₀ (mkLamsAV uaDs uaBodyA))
          (xs := vs_v) (ys := [t_ua, fs[fidx]'(by omega)])).mp hApp_ua_raw
        have hwd_UA : WellDenotedV V ρ₀ (mkLamsAV uaDs uaBodyA) := by
          rw [← hUA_mk]; exact ⟨mp.base2.acval_wellDenoted _ _ _, mp.acval_validV _ _ _⟩
        obtain ⟨hfold_UA, -, hwd_uaBody⟩ := mkLamsAV_appChainOk_pos uaDs uaBodyA vs_v ρ₀ hnz_uaDs
          (by rw [huaDs_len, hvs_len]) hwd_UA hApp_ua_split.1
        conv_rhs at hval_mbody => rw [List.foldl_append, hfold_UA]
        have hApp_ua_tail : AppChainOk (interp V (consList vs_v ρ₀) uaBodyA) [t_ua, fs[fidx]'(by omega)] := by
          rw [← hfold_UA]; exact hApp_ua_split.2
        -- 5. Unpack `uaBodyA = mkAppN (acval auxRecKey ψ_rec_ua) uarArgsA`!
        rw [openDummiesP_mkAppN, openDummiesP_const] at huaBodyA_den
        obtain ⟨fuarA, uarArgsA, hfuarA, hsp_uar, huaBodyA_eq⟩ := denoteMeta_mkAppN_inv huaBodyA_den
        have huar_len_lps : uarLvls.length = wp.cvAuxRec.levelParams.length := by
          have := wp.hAuxRec_lvls; omega
        simp only [denoteMeta, wp.hfindAuxRec, ConstantInfo.toConstantVal, huar_len_lps, ↓reduceIte, Option.some.injEq] at hfuarA
        let ψ_rec_ua := origVal wp.cvAuxRec.levelParams (ψ_rec uarLvls bnl ψ_P)
        have hfuarA_eq : fuarA = mp.base2.acval wp.auxRecKey ψ_rec_ua := by
          rw [← hfuarA]
          have hsub := substFn_eq_origVal_rec wp.hAuxRec_lvls wp.hAuxRec_perm huar_lvls_len huar_lvls_drop ψ_P
          exact mp.base2.acval_params wp.auxRecKey _ wp.hfindAuxRec _ _ fun q hq => hsub q hq
        rw [huaBodyA_eq, hfuarA_eq] at hval_mbody hwd_uaBody hApp_ua_tail
        obtain ⟨-, hwd_uar, hApp_uar_head⟩ := appChainOk_of_wellDenotedV uarArgsA hwd_uaBody
        let uarVals := uarArgsA.map (interp V (consList vs_v ρ₀))
        have hcl_rec_ua : interp V (consList vs_v ρ₀) (mp.base2.acval wp.auxRecKey ψ_rec_ua) =
            interp V ρ₀ (mp.base2.acval wp.auxRecKey ψ_rec_ua) :=
          closed_interp_env (mp.base2.acval_closed _ _) _ _
        rw [interp_mkAppN_foldl, hcl_rec_ua] at hval_mbody hApp_ua_tail
        rw [hcl_rec_ua] at hApp_uar_head
        have hApp_rec_ua : AppChainOk (interp V ρ₀ (mp.base2.acval wp.auxRecKey ψ_rec_ua))
            (uarVals ++ [t_ua, fs[fidx]'(by omega)]) :=
          (AppChainOk.append).mpr ⟨hApp_uar_head, hApp_ua_tail⟩
        -- 6. Invoke `unpack_eval_induction` on `(tupW (uAV ψ_P) [t_ua], fs[fidx])`!
        -- First get `fs[fidx] ∈ˢ app μ_aux (tupW (uAV ψ_P) [t_ua])` and `tupW (uAV ψ_P) [t_ua] ∈ˢ I`
        -- from `hApp_rec_ua` + `wp.hAuxRec_maj` (same 5-line check via `lfpFamSet_mem`)!
        -- Actually, `unpack_eval_induction` ALREADY proves `hmem_aux_of_appRec` internally — let's check:
        -- we need `tupW (uAV ψ_P) [t_ua] ∈ˢ I` and `fs[fidx] ∈ˢ app μ_aux (tupW (uAV ψ_P) [t_ua])`!
        -- Derive both cleanly from `hApp_rec_ua` via `teleFitPA_of_mkPisAV_appChainOk_pos` on `wp.hAuxRec_maj`!
        have hmem_ua : tupW (uAV ψ_P) [t_ua] ∈ˢ Ix.Kernel.Semantics.idxSet (uAV ψ_P) (consList vs_v ρ₀)
            (((ppsAll ψ_P).drop famAux.p.nP).map (·.2.2)) ∧
            fs[fidx]'(by omega) ∈ˢ SetTheory.app (fixFamI (uAV ψ_P) (famAux.p.resSort.eval ψ_P) (consList vs_v ρ₀)
              (((ppsAll ψ_P).drop famAux.p.nP).map (·.2.2)) 1
              (Ix.Kernel.Model.rssOfK ksF famAux.ctorsA.length)
              (Ix.Kernel.Model.tlssOfR (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0))
              (Ix.Kernel.Model.eissOfR (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0))
              (fssZ ψ_P)
              (Ix.Kernel.Model.essOfR (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0)))
              (tupW (uAV ψ_P) [t_ua]) := by
          -- Reuse `wp.hAuxRec_maj` + `RecRhsPwNoModel` + `hAtAux.leafT ψ_P`!
          have hnotResRec := auxRec_not_reserved wp.hfindAuxRec wp.auxIndWit.hnotRes hbasis
            wp.hAuxRec_maj wp.hmajDom
          have hnoModelRec : ¬ HasModel env wp.auxRecKey := by
            intro hm
            obtain ⟨aR, cHost, rcR, nf, p0, cm0, ip0, haR, hrcR, hmc, hcm0, hip0, hblk0⟩ :=
              wp.hauxRec_famBlk
            have hfindR' : env.find? (Core.keyOf t aR) =
                some (.recInfo wp.cvAuxRec (nP + 1 + wp.anc + 1) (nP + 1 + wp.anc) wp.arules) := by
              rw [haR]; exact wp.hfindAuxRec
            have hm' : HasModel env (Core.keyOf t aR) := haR.symm ▸ hm
            have := hreg.recModelNotNative aR wp.cvAuxRec (nP + 1 + wp.anc + 1) (nP + 1 + wp.anc) wp.arules
              cHost rcR nf p0 cm0 ip0 hfindR' hm' hrcR hmc hcm0 hip0
            rw [hblk0] at this; exact this wp.auxIndWit.hnat
          obtain ⟨pre0, rem0, hstrip0, hrem0⟩ := stripPis_posOf_inv wp.hAuxRec_maj
          cases rem0 with
          | forallE dom0 body0 majBm0 =>
            obtain ⟨hpre0_pw, hlarge0, -⟩ :=
              hreg.recRhsPw wp.auxRecKey wp.cvAuxRec (nP + 1 + wp.anc + 1) (nP + 1 + wp.anc) wp.arules
                wp.hfindAuxRec hnotResRec hnoModelRec pre0 dom0 body0 majBm0 hstrip0
            have hdom0_eq : Core.posOf wp.cvAuxRec.levelParams dom0 = wp.majDom := by
              simp only [Core.posOf, Expr.instantiateLevelParams] at hrem0
              exact (Expr.forallE.inj hrem0).1.symm
            have hdom0_fn : ∃ us0, dom0.getAppFn = .const wp.auxKey us0 ∧ us0.length = bnl := by
              have hfn_pos : (Core.posOf wp.cvAuxRec.levelParams dom0).getAppFn = .const wp.auxKey wp.majLvls := by
                rw [hdom0_eq, wp.hmajDom, Expr.getAppFn_mkAppN]; rfl
              have hgo : ∀ (e : KExpr), (Core.posOf wp.cvAuxRec.levelParams e).getAppFn = .const wp.auxKey wp.majLvls →
                  ∃ us0, e.getAppFn = .const wp.auxKey us0 ∧ us0.length = wp.majLvls.length := by
                intro e
                induction e with
                | app f a ihf _ =>
                  intro h; simp only [Core.posOf, Expr.instantiateLevelParams, Expr.getAppFn] at h ⊢; exact ihf h
                | const n us =>
                  intro h; simp only [Core.posOf, Expr.instantiateLevelParams, Expr.getAppFn] at h ⊢
                  injection h with hn hus
                  exact ⟨us, by rw [hn], by have := congrArg List.length hus; simpa using this⟩
                | _ => intro h; simp [Core.posOf, Expr.instantiateLevelParams, Expr.getAppFn] at h
              obtain ⟨us0, hfn0, hlen0⟩ := hgo dom0 hfn_pos
              have hmlen : wp.majLvls.length = bnl := by
                have h1 := (lvEqList_getElem wp.hmajLvls).1; simpa using h1
              exact ⟨us0, hfn0, hlen0.trans hmlen⟩
            obtain ⟨us0, hdom0_fn, hus0_len⟩ := hdom0_fn
            obtain ⟨elim, restLps, hcvLps_cons, hmaj0_pw, -⟩ := hlarge0 wp.auxKey us0 hdom0_fn (by omega)
            have hmemR := Ix.Kernel.Semantics.Env.find?_mem wp.hfindAuxRec
            obtain ⟨TVa, hTVa⟩ := mp.type_reads _ hmemR ψ_rec_ua
            have hTVa_mem := mp.mem_type _ hmemR ψ_rec_ua TVa hTVa ρ₀
            have hTVa_wd := mp.type_wellDenotedV _ hmemR ψ_rec_ua TVa hTVa ρ₀
            have hTVa_pos : denoteMeta mp.base2.acval env (ψ_rec uarLvls bnl ψ_P) 0
                (Core.posOf wp.cvAuxRec.levelParams wp.cvAuxRec.type) = some TVa := by
              rw [posOf_denoteMeta]; exact hTVa
            have hstrip_all : (Core.posOf wp.cvAuxRec.levelParams wp.cvAuxRec.type).stripPis (nP + 1 + wp.anc + 2) =
                some (wp.majBs ++ [(wp.majDom, wp.majBm)], wp.majBody) :=
              Ix.Kernel.stripPis_append (nP + 1 + wp.anc + 1) wp.hAuxRec_maj
                (show (wp.majDom.forallE wp.majBody wp.majBm).stripPis 1 =
                  some ([(wp.majDom, wp.majBm)], wp.majBody) from rfl)
            obtain ⟨dsR, bodyR, hTVa_mk, hdsR_len, -, -⟩ :=
              denoteMeta_stripPis (nP + 1 + wp.anc + 2) 0 hstrip_all hTVa_pos
            have helim_nz_orig : ψ_rec_ua elim ≠ 0 := by
              have hnd : wp.cvAuxRec.levelParams.Nodup := wp.hAuxRec_perm.nodup_iff.mpr List.nodup_range
              have hs0 := substFn_getElem (ψ := ψ_rec uarLvls bnl ψ_P) wp.cvAuxRec.levelParams
                (Core.posLevels wp.cvAuxRec.levelParams) hnd (by simp [Core.posLevels]) 0
                (by rw [hcvLps_cons]; simp)
              change Level.substFn (ψ_rec uarLvls bnl ψ_P) wp.cvAuxRec.levelParams
                (Core.posLevels wp.cvAuxRec.levelParams) elim ≠ 0
              rw [show elim = wp.cvAuxRec.levelParams[0]'(by rw [hcvLps_cons]; simp) by simp [hcvLps_cons], hs0]
              simp only [Core.posLevels, List.getElem_map, List.getElem_range, Level.eval, ψ_rec, ↓reduceIte]
              have := huar_elim_nz ψ_P; omega
            have hpos_dsR : ∀ d ∈ dsR, d.2.1 ≠ 0 := by
              have hstrip0_all : wp.cvAuxRec.type.stripPis (nP + 1 + wp.anc + 2) =
                  some (pre0 ++ [(dom0, majBm0)], body0) :=
                Ix.Kernel.stripPis_append (nP + 1 + wp.anc + 1) hstrip0
                  (show (dom0.forallE body0 majBm0).stripPis 1 = some ([(dom0, majBm0)], body0) from rfl)
              obtain ⟨dsR0, bodyR0, hTVa_mk0, hdsR0_len, hdsR0_bits, -⟩ :=
                denoteMeta_stripPis (nP + 1 + wp.anc + 2) 0 hstrip0_all hTVa
              have hds_eq : dsR = dsR0 := by
                have hgo : ∀ (l1 l2 : List (Nat × Nat × AnnotTerm)) (b1 b2 : AnnotTerm),
                    l1.length = l2.length → mkPisAV l1 b1 = mkPisAV l2 b2 → l1 = l2 := by
                  intro l1; induction l1 with
                  | nil => intro l2 _ _ hl _; cases l2 with | nil => rfl | cons _ _ => simp at hl
                  | cons d1 l1 ih =>
                    intro l2 b1 b2 hl hmk; cases l2 with
                    | nil => simp at hl
                    | cons d2 l2 =>
                      simp only [mkPisAV] at hmk
                      obtain ⟨h1, h2, h3, h4⟩ := AnnotTerm.pi.inj hmk
                      have hd : d1 = d2 := by rcases d1 with ⟨_, _, _⟩; rcases d2 with ⟨_, _, _⟩; exact Prod.ext h1 (Prod.ext h2 h3)
                      rw [hd, ih l2 b1 b2 (by simpa using hl) h4]
                exact hgo dsR dsR0 bodyR bodyR0 (by omega) (hTVa_mk.symm.trans hTVa_mk0)
              rw [hds_eq]; intro d hd; obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
              have hbi := map_getElem_eq hdsR0_bits i hi (by rw [stripPis_length_p hstrip0_all]; omega)
              have hpw_i : ((pre0 ++ [(dom0, majBm0)])[i]'(by rw [stripPis_length_p hstrip0_all, ← hdsR0_len]; exact hi)).2.pw =
                  .ifAllZero [elim] := by
                rcases List.mem_append.mp (List.getElem_mem (l := pre0 ++ [(dom0, majBm0)]) (n := i)
                  (by rw [stripPis_length_p hstrip0_all, ← hdsR0_len]; exact hi)) with hp | hm
                · rw [hpre0_pw _ hp, hmaj0_pw]
                · rw [List.mem_singleton.mp hm]; exact hmaj0_pw
              rw [hbi, hpw_i]
              unfold pwBit
              split_ifs with h0
              · exact absurd (by simpa [Ix.Kernel.PropWhen.holds_ifAllZero] using h0) helim_nz_orig
              · exact Nat.one_ne_zero
            have huarArgsA_len : uarArgsA.length = nP + 1 + wp.anc := by
              have := denoteMetaSpine_length_eq hsp_uar; simp only [List.length_map, huar_len] at this; exact this.symm
            have huarVals_len : uarVals.length = nP + 1 + wp.anc := by simp [uarVals, huarArgsA_len]
            have huarVals_pref : uarVals.take nP = vs_v := by
              refine List.ext_getElem (by rw [List.length_take, huarVals_len, hvs_len]; omega) fun i hi1 hi2 => ?_
              rw [List.getElem_take]; simp only [uarVals, List.getElem_map]
              have hden_i := denoteMetaSpine_getElem hsp_uar (i := i) (by simp [huar_len]; omega)
              simp only [List.getElem_map] at hden_i
              have heq_i : ExprSemEq (uarArgs[i]'(by omega)) (.bvar (nP - 1 - i)) := by
                have := forall₂_getElem huar_pref i
                  (by rw [List.length_take, huar_len]; omega) (by simp; omega)
                simpa [List.getElem_take] using this
              have hden_bv : denoteMeta mp.base2.acval env ψ_P nP (openDummiesP nP 0 0 (.bvar (nP - 1 - i))) =
                  some (.bvar (nP - 1 - i)) := denoteMeta_openDummiesP_bvar0 (by omega)
              have hsame := (denoteMeta_exprSemEq (acval := mp.base2.acval) (env := env) (φ := ψ_P) (d := nP)
                (exprSemEq_openDummiesP heq_i nP 0 0)).symm.trans hden_i
              rw [hden_bv] at hsame
              rw [(Option.some.inj hsame).symm, interp_bvar, ← hvs_len, consList_bvar_desc vs_v ρ₀ (by omega)]
            rw [hTVa_mk] at hTVa_mem hTVa_wd
            rw [Ix.Kernel.Semantics.Env.find?_name wp.hfindAuxRec] at hTVa_mem
            have hsp_rec := spineFit_of_mkPisAV_appChainOk_pos dsR bodyR (uarVals ++ [t_ua, fs[fidx]'(by omega)]) ρ₀
              hpos_dsR (by simp [hdsR_len, huarVals_len]) hTVa_mem hApp_rec_ua
            have hdsR_split : dsR.map (·.2.2) =
                (dsR.take (nP + 1 + wp.anc + 1)).map (·.2.2) ++ [((dsR[nP + 1 + wp.anc + 1]'(by omega)).2.2)] := by
              have htake : dsR = dsR.take (nP + 1 + wp.anc + 1) ++ [dsR[nP + 1 + wp.anc + 1]'(by omega)] := by
                have := List.take_append_drop (nP + 1 + wp.anc + 1) dsR
                have hdrop : dsR.drop (nP + 1 + wp.anc + 1) = [dsR[nP + 1 + wp.anc + 1]'(by omega)] := by
                  refine List.ext_getElem (by simp [hdsR_len]) fun i _ hi2 => ?_
                  have hi0 : i = 0 := by simp at hi2; omega
                  subst hi0; simp
                rw [hdrop] at this; exact this.symm
              have hmap := congrArg (List.map fun d : Nat × Nat × AnnotTerm => d.2.2) htake
              rw [List.map_append, List.map_cons, List.map_nil] at hmap
              exact hmap
            rw [hdsR_split, show uarVals ++ [t_ua, fs[fidx]'(by omega)] = (uarVals ++ [t_ua]) ++ [fs[fidx]'(by omega)] by simp] at hsp_rec
            obtain ⟨hsp_pre, hsp_last⟩ := (spineFit_append_iff (by simp [hdsR_len, huarVals_len])).mp hsp_rec
            obtain ⟨dsR1, remR1, hTVa_mk1, hdsR1_len, -, hremR1_den⟩ :=
              denoteMeta_stripPis (nP + 1 + wp.anc + 1) 0 wp.hAuxRec_maj hTVa_pos
            simp only [Nat.zero_add] at hremR1_den
            have hopen_for : ∀ (m d c : Nat) (t b : KExpr) (bm : BinderMeta),
                openDummiesP m d c (.forallE t b bm) =
                  .forallE (openDummiesP m d c t) (openDummiesP m d (c + 1) b) bm := by
              intro m; induction m with
              | zero => intros; rfl
              | succ m ih =>
                intro d c t b bm; simp only [openDummiesP, Expr.instantiate1]
                rw [show c + m + 1 = c + 1 + m by omega]; exact ih (d + 1) c _ _ bm
            rw [hopen_for] at hremR1_den
            obtain ⟨majDomA, _, hmajDomA_den, -, hremR1_eq⟩ := denoteMeta_forallE_some hremR1_den
            have hds_prefix_eq : dsR1 = dsR.take (nP + 1 + wp.anc + 1) ∧
                (dsR[nP + 1 + wp.anc + 1]'(by omega)).2.2 = majDomA := by
              have htake_ds : dsR = dsR.take (nP + 1 + wp.anc + 1) ++ [dsR[nP + 1 + wp.anc + 1]'(by omega)] := by
                have := List.take_append_drop (nP + 1 + wp.anc + 1) dsR
                have hdrop : dsR.drop (nP + 1 + wp.anc + 1) = [dsR[nP + 1 + wp.anc + 1]'(by omega)] := by
                  refine List.ext_getElem (by simp [hdsR_len]) fun i _ hi2 => ?_
                  have hi0 : i = 0 := by simp at hi2; omega
                  subst hi0; simp
                rw [hdrop] at this; exact this.symm
              have hmk_both : mkPisAV dsR1 remR1 =
                  mkPisAV (dsR.take (nP + 1 + wp.anc + 1)) (.pi (dsR[nP + 1 + wp.anc + 1]'(by omega)).1
                    (dsR[nP + 1 + wp.anc + 1]'(by omega)).2.1 (dsR[nP + 1 + wp.anc + 1]'(by omega)).2.2 bodyR) := by
                have hmk_ds : mkPisAV dsR bodyR =
                    mkPisAV (dsR.take (nP + 1 + wp.anc + 1)) (.pi (dsR[nP + 1 + wp.anc + 1]'(by omega)).1
                      (dsR[nP + 1 + wp.anc + 1]'(by omega)).2.1 (dsR[nP + 1 + wp.anc + 1]'(by omega)).2.2 bodyR) := by
                  conv_lhs => rw [htake_ds]
                  rw [mkPisAV_append]; rfl
                rw [← hTVa_mk1, hTVa_mk]; exact hmk_ds
              have hgo : ∀ (l1 l2 : List (Nat × Nat × AnnotTerm)) (b1 b2 : AnnotTerm),
                  l1.length = l2.length → mkPisAV l1 b1 = mkPisAV l2 b2 → l1 = l2 ∧ b1 = b2 := by
                intro l1; induction l1 with
                | nil => intro l2 _ _ hl h; cases l2 with | nil => exact ⟨rfl, h⟩ | cons _ _ => simp at hl
                | cons d1 l1 ih =>
                  intro l2 b1 b2 hl h; cases l2 with
                  | nil => simp at hl
                  | cons d2 l2 =>
                    simp only [mkPisAV] at h; obtain ⟨h1, h2, h3, h4⟩ := AnnotTerm.pi.inj h
                    have hd : d1 = d2 := by rcases d1 with ⟨_, _, _⟩; rcases d2 with ⟨_, _, _⟩; exact Prod.ext h1 (Prod.ext h2 h3)
                    obtain ⟨htl, hb⟩ := ih l2 b1 b2 (by simpa using hl) h4; exact ⟨by rw [hd, htl], hb⟩
              obtain ⟨hl_eq, hb_eq⟩ := hgo dsR1 (dsR.take (nP + 1 + wp.anc + 1)) remR1 _
                (by simp [hdsR1_len, hdsR_len]) hmk_both
              rw [← hremR1_eq] at hb_eq
              exact ⟨hl_eq, (AnnotTerm.pi.inj hb_eq).2.2.1.symm⟩
            have hwd_mkPis : ∀ (ds : List (Nat × Nat × AnnotTerm)) (b : AnnotTerm) (xs : List V) (ρ : Nat → V),
                ds.length = xs.length → WellDenotedV V ρ (mkPisAV ds b) →
                SpineFit ρ (ds.map (·.2.2)) xs → WellDenotedV V (consList xs ρ) b := by
              intro ds; induction ds with
              | nil => intro b xs ρ hl hwd _; cases xs with | nil => exact hwd | cons _ _ => simp at hl
              | cons d ds ih =>
                intro b xs ρ hl hwd hsp; cases xs with
                | nil => simp at hl
                | cons x xs =>
                  simp only [mkPisAV, WellDenotedV, WellDenoted_pi, AnnotValid_pi] at hwd
                  simp only [List.map_cons, SpineFit] at hsp
                  simpa [consList] using ih b xs (cons x ρ) (by simpa using hl)
                    ⟨hwd.1.2 x hsp.1, hwd.2.2.1 x hsp.1⟩ hsp.2
            have hwd_remR1 := hwd_mkPis dsR1 remR1 (uarVals ++ [t_ua]) ρ₀
              (by simp [hdsR1_len, huarVals_len]) (by rw [← hTVa_mk1, hTVa_mk]; exact hTVa_wd)
              (by rw [hds_prefix_eq.1]; exact hsp_pre)
            rw [← hremR1_eq] at hwd_remR1
            have hwd_majDom : WellDenotedV V (consList (uarVals ++ [t_ua]) ρ₀) majDomA :=
              ⟨hwd_remR1.1.1, hwd_remR1.2.1⟩
            rw [wp.hmajDom, openDummiesP_mkAppN, openDummiesP_const] at hmajDomA_den
            obtain ⟨faM, margsA, hfaM, hspM, hmajDomA_eq⟩ := denoteMeta_mkAppN_inv hmajDomA_den
            have hml_len : wp.majLvls.length = wp.auxIndWit.cv.levelParams.length := by
              have h1 := (lvEqList_getElem wp.hmajLvls).1; rw [haux_lps]; simpa using h1
            simp only [denoteMeta, wp.auxIndWit.hfind, ConstantInfo.toConstantVal, hml_len, ↓reduceIte, Option.some.injEq] at hfaM
            have hfaM_eq : faM = mp.base2.acval wp.auxKey ψ_P := by
              rw [← hfaM]
              exact mp.base2.acval_params wp.auxKey _ wp.auxIndWit.hfind _ _ fun q hq => by
                simp only [ConstantInfo.toConstantVal] at hq
                rw [haux_lps, List.mem_range] at hq
                rw [haux_lps, substFn_eq_of_lvEqList wp.hmajLvls (ψ_rec uarLvls bnl ψ_P)]
                have hsub := substFn_getElem (ψ := ψ_rec uarLvls bnl ψ_P) (List.range bnl)
                  ((List.range bnl).map fun m => .param (1 + m)) List.nodup_range (by simp) q (by simp [hq])
                have hne0 : (1 + q = 0) = False := eq_false (Nat.one_add q ▸ Nat.succ_ne_zero q)
                have hlt1 : (1 + q < bnl + 1) = True := eq_true (Nat.add_comm 1 q ▸ Nat.add_lt_add_right hq 1)
                simp only [List.getElem_range, List.getElem_map, Level.eval, ψ_rec,
                  hne0, hlt1, ↓reduceIte, Nat.add_sub_cancel_left] at hsub
                exact hsub
            have hmargsA_len : margsA.length = nP + 1 := by
              have := denoteMetaSpine_length_eq hspM; simp only [List.length_map, wp.hmajArgs_len] at this; exact this.symm
            have hmargsV_eq : margsA.map (interp V (consList (uarVals ++ [t_ua]) ρ₀)) = vs_v ++ [t_ua] := by
              have hmajArgs_len := wp.hmajArgs_len
              refine List.ext_getElem (by simp [hmargsA_len, hvs_len]) fun i hi1 hi2 => ?_
              simp only [List.length_map, hmargsA_len] at hi1
              simp only [List.getElem_map]
              have hden_i := denoteMetaSpine_getElem hspM (i := i) (by simp [hmajArgs_len]; omega)
              simp only [List.getElem_map] at hden_i
              by_cases hiP : i < nP
              · have heq_i : ExprSemEq (wp.majArgs[i]'(by omega)) (.bvar (nP + 1 + wp.anc + 1 - 1 - i)) := by
                  have := forall₂_getElem wp.hmajArgs_pref i
                    (by rw [List.length_take, hmajArgs_len]; omega) (by simp; omega)
                  simpa [List.getElem_take] using this
                have hden_bv : denoteMeta mp.base2.acval env (ψ_rec uarLvls bnl ψ_P) (nP + 1 + wp.anc + 1)
                    (openDummiesP (nP + 1 + wp.anc + 1) 0 0 (.bvar (nP + 1 + wp.anc + 1 - 1 - i))) =
                    some (.bvar (nP + 1 + wp.anc + 1 - 1 - i)) := denoteMeta_openDummiesP_bvar0 (by omega)
                have hsame := (denoteMeta_exprSemEq (acval := mp.base2.acval) (env := env)
                  (φ := ψ_rec uarLvls bnl ψ_P) (d := nP + 1 + wp.anc + 1)
                  (exprSemEq_openDummiesP heq_i _ 0 0)).symm.trans hden_i
                rw [hden_bv] at hsame
                rw [(Option.some.inj hsame).symm, interp_bvar,
                  show nP + 1 + wp.anc + 1 - 1 - i = (uarVals ++ [t_ua]).length - 1 - i by simp [huarVals_len],
                  consList_bvar_desc (uarVals ++ [t_ua]) ρ₀ (by simp [huarVals_len]; omega),
                  List.getElem_append_left (by omega : i < uarVals.length),
                  List.getElem_append_left (by omega : i < vs_v.length)]
                have hget := congrArg (fun l => l[i]?) huarVals_pref
                rw [List.getElem?_take_of_lt hiP, List.getElem?_eq_getElem (by omega : i < uarVals.length),
                  List.getElem?_eq_getElem (by omega : i < vs_v.length)] at hget
                exact Option.some.inj hget
              · have hi_eq : i = nP := by omega
                subst i
                have hidx_eq : wp.majArgs[nP]'(by omega) = .bvar 0 := by
                  have hidx := wp.hmajArgs_idx
                  rw [List.getElem?_eq_getElem (by omega : nP < wp.majArgs.length)] at hidx
                  exact Option.some.inj hidx
                rw [hidx_eq] at hden_i
                have hden_bv : denoteMeta mp.base2.acval env (ψ_rec uarLvls bnl ψ_P) (nP + 1 + wp.anc + 1)
                    (openDummiesP (nP + 1 + wp.anc + 1) 0 0 (.bvar 0)) = some (.bvar 0) :=
                  denoteMeta_openDummiesP_bvar0 (by omega)
                rw [hden_bv] at hden_i
                rw [(Option.some.inj hden_i).symm, interp_bvar]
                simp only [consList_append, consList, cons]
                rw [List.getElem_append_right (by omega : vs_v.length ≤ nP)]
                simp [hvs_len]
            have hz_mem_maj := hsp_last.1
            rw [hds_prefix_eq.2, hmajDomA_eq, hfaM_eq, interp_mkAppN_foldl, hmargsV_eq,
              closed_interp_env (mp.base2.acval_closed wp.auxKey ψ_P) _ ρ₀] at hz_mem_maj
            rw [hmajDomA_eq, hfaM_eq] at hwd_majDom
            obtain ⟨-, -, hApp_aux_ua⟩ := appChainOk_of_wellDenotedV margsA hwd_majDom
            rw [hmargsV_eq, closed_interp_env (mp.base2.acval_closed wp.auxKey ψ_P) _ ρ₀] at hApp_aux_ua
            rw [← hnameAux', hAtAux.leafT ψ_P] at hz_mem_maj hApp_aux_ua
            have hfold_uaT := mkLamsAV_appChainOk_pos
              ((ppsAll ψ_P).map fun d => (famAux.p.resSort.eval ψ_P + 1, d.2.2)) _ (vs_v ++ [t_ua]) ρ₀ hnz_T
              (by simp [hAtAux.former.len ψ_P, hfam_nP, hfam_nIdx, hvs_len]) hokT₀ hApp_aux_ua
            have hsp_uaT : SpineFit ρ₀ ((ppsAll ψ_P).map (·.2.2)) (vs_v ++ [t_ua]) := by
              simpa [List.map_map, Function.comp_def] using hfold_uaT.2.1
            obtain ⟨hsp_p_ua, hsp_tua⟩ := (spineFit_append_iff hlen_pT).mp (hsplit_pT ▸ hsp_uaT)
            have hnat_ua := nativeTyAVI_fold_at hfrAux.1 hsp_p_ua hsp_tua
            rw [hnat_ua, hIds_len] at hz_mem_maj
            exact ⟨Ix.Kernel.Semantics.tupW_mem hsp_tua, hz_mem_maj⟩
          | _ => simp [Core.posOf, Expr.instantiateLevelParams] at hrem0
        -- Fire `unpack_eval_induction`!
        have hind_res := unpack_eval_induction ht hbasis hreg mp hN
          wp.auxIndWit wp.hauxInd_lvls wp.hauxInd_idx wp.hauxInd_rec
          ⟨wp.auxSortBs, wp.auxSortU, wp.hauxInd_sort, wp.hauxInd_nz⟩
          wp.hfindAuxRec wp.hAuxRec_lvls wp.hAuxRec_perm wp.hauxRec_famBlk
          ⟨wp.majBs, wp.majDom, wp.majBody, wp.majBm, wp.majLvls, wp.majArgs,
            wp.hAuxRec_maj, wp.hmajDom, wp.hmajLvls, wp.hmajArgs_len, wp.hmajArgs_pref, wp.hmajArgs_idx⟩
          (fun j rl h => (wp.hrecCtor j rl h).trans (wp.hauxCtorKeyAt j))
          hregAux hnameAux' hAtAux huar_lvls_len huar_elim_nz huar_lvls_drop huar_len huar_pref
          hminors_key ψ_P ρ₀ vs_v hvs_len hsp_p hsp_uar hwd_uar
          (tupW (uAV ψ_P) [t_ua]) (fs[fidx]'(by omega)) hmem_ua.1 hmem_ua.2 t_ua rfl hApp_rec_ua
        rw [hsp_eq, hproj_x]
        refine ⟨hind_res.1, ?_⟩
        rw [hval_mbody, ← List.foldl_append]
        exact hind_res.2
    -- Dispatch `wp.hbody` (`.direct` vs `.viaDefn`) into `hhandle_minor`!
    cases wp.hbody with
    | direct pbs pheadLvls pargs rbsJ rargsJ mbsJ mbody rlJ hp_strip hp_pw hpl_len hpl_elim hpl_drop
        hpargs_len hpargs_pref hpargs_tag hpargs_subj hrlJ hrlJ_nf hrlJ_strip hrargsJ_ge
        hrargsJ_fields hminJ_strip hminJ_pw hminor =>
      obtain ⟨pDs, pBodyA, hP_mk, hpDs_len, hpDs_bits, hpBodyA_den⟩ :=
        denoteMeta_stripLams (nP + 1) 0 hp_strip hP_den
      simp only [Nat.zero_add] at hpBodyA_den
      have hnz_pDs : ∀ p ∈ pDs, p.1 ≠ 0 := by
        intro p hp; obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
        have hbi := map_getElem_eq hpDs_bits i hi (by rw [stripLams_length hp_strip]; omega)
        have hs := hp_pw (pbs[i]'(by rw [stripLams_length hp_strip]; omega)) (List.getElem_mem _)
        rw [hbi, hs]; exact hpw0
      have hwd_P : WellDenotedV V ρ₀ (mkLamsAV pDs pBodyA) := by
        rw [← hP_mk]; exact ⟨mp.base2.acval_wellDenoted _ _ _, mp.acval_validV _ _ _⟩
      have hApp_P' : AppChainOk (interp V ρ₀ (mkLamsAV pDs pBodyA)) (vs_v ++ [x_v]) := by
        rw [← hP_mk]; exact hApp_proj
      obtain ⟨hfold_P, -, hwd_pBody⟩ := mkLamsAV_appChainOk_pos pDs pBodyA (vs_v ++ [x_v]) ρ₀ hnz_pDs
        (by rw [hpDs_len, List.length_append, hvs_len]; rfl) hwd_P hApp_P'
      rw [openDummiesP_mkAppN, openDummiesP_const] at hpBodyA_den
      obtain ⟨frecA, pargsA, hfrecA, hsp_pargs, hpBodyA_eq⟩ := denoteMeta_mkAppN_inv hpBodyA_den
      have hpl_lps : pheadLvls.length = wp.cvAuxRec.levelParams.length := by
        have := wp.hAuxRec_lvls; omega
      simp only [denoteMeta, wp.hfindAuxRec, ConstantInfo.toConstantVal, hpl_lps, ↓reduceIte, Option.some.injEq] at hfrecA
      let ψ_rec_p := origVal wp.cvAuxRec.levelParams (ψ_rec pheadLvls bnl ψ_P)
      have hfrecA_eq : frecA = mp.base2.acval wp.auxRecKey ψ_rec_p := by
        rw [← hfrecA]
        have hsub := substFn_eq_origVal_rec wp.hAuxRec_lvls wp.hAuxRec_perm hpl_len hpl_drop ψ_P
        exact mp.base2.acval_params wp.auxRecKey _ wp.hfindAuxRec _ _ fun q hq => hsub q hq
      rw [hpBodyA_eq, hfrecA_eq] at hwd_pBody hfold_P
      obtain ⟨-, hwd_pargs, hApp_rec_raw⟩ := appChainOk_of_wellDenotedV pargsA hwd_pBody
      let pargsV := pargsA.map (interp V (consList (vs_v ++ [x_v]) ρ₀))
      have hpargsA_len : pargsA.length = nP + 1 + wp.anc + 2 := by
        have := denoteMetaSpine_length_eq hsp_pargs; simp only [List.length_map, hpargs_len] at this; exact this.symm
      have hpargsV_last : pargsV[nP + 1 + wp.anc + 1]'(by simp [pargsV, hpargsA_len]) = x_v := by
        simp only [pargsV, List.getElem_map]
        have hden_s := denoteMetaSpine_getElem hsp_pargs (i := nP + 1 + wp.anc + 1) (by simp [hpargs_len])
        simp only [List.getElem_map] at hden_s
        have hsubj : pargs[nP + 1 + wp.anc + 1]'(by omega) = .bvar 0 := by
          rw [List.getElem?_eq_getElem (by omega : nP + 1 + wp.anc + 1 < pargs.length)] at hpargs_subj
          exact Option.some.inj hpargs_subj
        rw [hsubj] at hden_s
        have hden_bv : denoteMeta mp.base2.acval env ψ_P (nP + 1) (openDummiesP (nP + 1) 0 0 (.bvar 0)) =
            some (.bvar 0) := denoteMeta_openDummiesP_bvar0 (by omega)
        rw [hden_bv] at hden_s
        rw [(Option.some.inj hden_s).symm, interp_bvar]
        simp only [consList_append, consList, cons]
      have hpargsV_split : pargsV = pargsV.take (nP + 1 + wp.anc + 1) ++ [x_v] := by
        have := List.take_append_drop (nP + 1 + wp.anc + 1) pargsV
        have hdrop : pargsV.drop (nP + 1 + wp.anc + 1) = [x_v] := by
          refine List.ext_getElem (by simp [pargsV, hpargsA_len]) fun i _ hi2 => ?_
          have hi0 : i = 0 := by simp at hi2; omega
          subst hi0; simpa using hpargsV_last
        rw [hdrop] at this; exact this.symm
      have hxs_pref : (pargsV.take (nP + 1 + wp.anc + 1)).take nP = vs_v := by
        rw [List.take_take, Nat.min_eq_left (by omega)]
        refine List.ext_getElem (by rw [List.length_take, List.length_map, hpargsA_len, hvs_len]; omega) fun m hm1 hm2 => ?_
        rw [List.getElem_take]; simp only [pargsV, List.getElem_map]
        have hden_m := denoteMetaSpine_getElem hsp_pargs (i := m) (by simp [hpargs_len]; omega)
        simp only [List.getElem_map] at hden_m
        have heq_m : ExprSemEq (pargs[m]'(by omega)) (.bvar (nP + 1 - 1 - m)) := by
          have := forall₂_getElem hpargs_pref m
            (by rw [List.length_take, hpargs_len]; omega) (by simp; omega)
          simpa [List.getElem_take] using this
        have hden_bv : denoteMeta mp.base2.acval env ψ_P (nP + 1) (openDummiesP (nP + 1) 0 0 (.bvar (nP + 1 - 1 - m))) =
            some (.bvar (nP + 1 - 1 - m)) := denoteMeta_openDummiesP_bvar0 (by omega)
        have hsame := (denoteMeta_exprSemEq (acval := mp.base2.acval) (env := env) (φ := ψ_P) (d := nP + 1)
          (exprSemEq_openDummiesP heq_m _ 0 0)).symm.trans hden_m
        rw [hden_bv] at hsame
        rw [(Option.some.inj hsame).symm, interp_bvar,
          show nP + 1 - 1 - m = (vs_v ++ [x_v]).length - 1 - m by simp [hvs_len],
          consList_bvar_desc (vs_v ++ [x_v]) ρ₀ (by simp [hvs_len]; omega),
          List.getElem_append_left (by omega : m < vs_v.length)]
      have hminJ_den : denoteMeta mp.base2.acval env ψ_P (nP + 1)
          (openDummiesP (nP + 1) 0 0 (pargs.getD (nP + 1 + wp.jIdx) default)) =
          some (pargsA[nP + 1 + wp.jIdx]'(by have := wp.hjIdx_lt; omega)) := by
        have hget : pargs.getD (nP + 1 + wp.jIdx) default = pargs[nP + 1 + wp.jIdx]'(by have := wp.hjIdx_lt; omega) := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by have := wp.hjIdx_lt; omega), Option.getD_some]
        rw [hget]
        have h1 := denoteMetaSpine_getElem hsp_pargs (i := nP + 1 + wp.jIdx) (by simp [hpargs_len]; have := wp.hjIdx_lt; omega)
        simpa only [List.getElem_map] using h1
      have hcl_rec_p : interp V (consList (vs_v ++ [x_v]) ρ₀) (mp.base2.acval wp.auxRecKey ψ_rec_p) =
          interp V ρ₀ (mp.base2.acval wp.auxRecKey ψ_rec_p) :=
        closed_interp_env (mp.base2.acval_closed _ _) _ _
      exact hhandle_minor hpl_len hpl_elim hpl_drop hrlJ hrlJ_nf hrlJ_strip hrargsJ_ge hrargsJ_fields
        hminJ_strip hminJ_pw hminor
        (bodyUnpackSpec_direct wp.hfindAuxRec hp_strip hrlJ hrlJ_strip hminJ_strip hminor wp.hbody)
        hminJ_den (hwd_pargs _ (List.getElem_mem _))
        (by rw [List.length_take, List.length_map, hpargsA_len]; omega)
        hxs_pref (by simp [pargsV])
        (by
          rw [hP_mk, hpBodyA_eq, hfrecA_eq, hfold_P, interp_mkAppN_foldl, hcl_rec_p]
          change pargsV.foldl SetTheory.app _ = _
          conv_lhs => rw [hpargsV_split])
        (by
          have h1 : AppChainOk (interp V ρ₀ (mp.base2.acval wp.auxRecKey ψ_rec_p)) pargsV :=
            hcl_rec_p ▸ hApp_rec_raw
          rwa [hpargsV_split] at h1)
    | viaDefn pheadKey cvR rval rHint pbs pheadLvls pargs rbs arLvls rargs rbsJ rargsJ mbsJ mbody rlJ
        hp_strip hp_pw hpl_len hpl_elim hpl_drop hR_nonAux hfindR hR_lvls hR_perm hplen_gt
        hpargs_pref hpargs_subj hr_strip hr_pw harLvls hrargs_len hrargs_pref hrargs_minors
        hrargs_tag hrargs_subj hrlJ hrlJ_nf hrlJ_strip hrargsJ_ge hrargsJ_fields hminJ_strip
        hminJ_pw hminor =>
      -- 1. Peel `pval`'s `nP + 1` positive lambdas!
      obtain ⟨pDs, pBodyA, hP_mk, hpDs_len, hpDs_bits, hpBodyA_den⟩ :=
        denoteMeta_stripLams (nP + 1) 0 hp_strip hP_den
      simp only [Nat.zero_add] at hpBodyA_den
      have hnz_pDs : ∀ p ∈ pDs, p.1 ≠ 0 := by
        intro p hp; obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
        have hbi := map_getElem_eq hpDs_bits i hi (by rw [stripLams_length hp_strip]; omega)
        have hs := hp_pw (pbs[i]'(by rw [stripLams_length hp_strip]; omega)) (List.getElem_mem _)
        rw [hbi, hs]; exact hpw0
      have hwd_P : WellDenotedV V ρ₀ (mkLamsAV pDs pBodyA) := by
        rw [← hP_mk]; exact ⟨mp.base2.acval_wellDenoted _ _ _, mp.acval_validV _ _ _⟩
      have hApp_P' : AppChainOk (interp V ρ₀ (mkLamsAV pDs pBodyA)) (vs_v ++ [x_v]) := by
        rw [← hP_mk]; exact hApp_proj
      obtain ⟨hfold_P, -, hwd_pBody⟩ := mkLamsAV_appChainOk_pos pDs pBodyA (vs_v ++ [x_v]) ρ₀ hnz_pDs
        (by rw [hpDs_len, List.length_append, hvs_len]; rfl) hwd_P hApp_P'
      rw [openDummiesP_mkAppN, openDummiesP_const] at hpBodyA_den
      obtain ⟨fRA, pargsA, hfRA, hsp_pargs, hpBodyA_eq⟩ := denoteMeta_mkAppN_inv hpBodyA_den
      have hpl_R : pheadLvls.length = cvR.levelParams.length := by
        have := hR_lvls; omega
      simp only [denoteMeta, hfindR, ConstantInfo.toConstantVal, hpl_R, ↓reduceIte, Option.some.injEq] at hfRA
      let ψ_R_pos := ψ_rec pheadLvls bnl ψ_P
      let ψ_R_orig := origVal cvR.levelParams ψ_R_pos
      have hfRA_eq : fRA = mp.base2.acval pheadKey ψ_R_orig := by
        rw [← hfRA]
        have hsub := substFn_eq_origVal_rec hR_lvls hR_perm hpl_len hpl_drop ψ_P
        exact mp.base2.acval_params pheadKey _ hfindR _ _ fun q hq => hsub q hq
      rw [hpBodyA_eq, hfRA_eq] at hwd_pBody hfold_P
      obtain ⟨-, hwd_pargs, hApp_R_raw⟩ := appChainOk_of_wellDenotedV pargsA hwd_pBody
      let pargsV := pargsA.map (interp V (consList (vs_v ++ [x_v]) ρ₀))
      have hpargsA_len : pargsA.length = pargs.length := by
        have := denoteMetaSpine_length_eq hsp_pargs; simpa using this.symm
      have hpargsV_len : pargsV.length = pargs.length := by simp [pargsV, hpargsA_len]
      have hpargsV_pref : pargsV.take nP = vs_v := by
        refine List.ext_getElem (by rw [List.length_take, hpargsV_len, hvs_len]; omega) fun m hm1 hm2 => ?_
        rw [List.getElem_take]; simp only [pargsV, List.getElem_map]
        have hden_m := denoteMetaSpine_getElem hsp_pargs (i := m) (by simp; omega)
        simp only [List.getElem_map] at hden_m
        have heq_m : ExprSemEq (pargs[m]'(by omega)) (.bvar (nP + 1 - 1 - m)) := by
          have := forall₂_getElem hpargs_pref m
            (by rw [List.length_take]; omega) (by simp; omega)
          simpa [List.getElem_take] using this
        have hden_bv : denoteMeta mp.base2.acval env ψ_P (nP + 1) (openDummiesP (nP + 1) 0 0 (.bvar (nP + 1 - 1 - m))) =
            some (.bvar (nP + 1 - 1 - m)) := denoteMeta_openDummiesP_bvar0 (by omega)
        have hsame := (denoteMeta_exprSemEq (acval := mp.base2.acval) (env := env) (φ := ψ_P) (d := nP + 1)
          (exprSemEq_openDummiesP heq_m _ 0 0)).symm.trans hden_m
        rw [hden_bv] at hsame
        rw [(Option.some.inj hsame).symm, interp_bvar,
          show nP + 1 - 1 - m = (vs_v ++ [x_v]).length - 1 - m by simp [hvs_len],
          consList_bvar_desc (vs_v ++ [x_v]) ρ₀ (by simp [hvs_len]; omega),
          List.getElem_append_left (by omega : m < vs_v.length)]
      have hpargsV_last : pargsV[pargsV.length - 1]'(by omega) = x_v := by
        simp only [pargsV, List.getElem_map, List.length_map]
        have hden_s := denoteMetaSpine_getElem hsp_pargs (i := pargs.length - 1) (by simp; omega)
        simp only [List.getElem_map] at hden_s
        have hsubj : pargs[pargs.length - 1]'(by omega) = .bvar 0 := by
          rw [List.getElem?_eq_getElem (by omega : pargs.length - 1 < pargs.length)] at hpargs_subj
          exact Option.some.inj hpargs_subj
        rw [hsubj] at hden_s
        have hden_bv : denoteMeta mp.base2.acval env ψ_P (nP + 1) (openDummiesP (nP + 1) 0 0 (.bvar 0)) =
            some (.bvar 0) := denoteMeta_openDummiesP_bvar0 (by omega)
        rw [hden_bv] at hden_s
        have hidx_last : pargsA.length - 1 = pargs.length - 1 := by omega
        simp only [hidx_last]
        rw [(Option.some.inj hden_s).symm, interp_bvar]
        simp only [consList_append, consList, cons]
      -- 2. Peel `rval`'s `pargs.length` positive lambdas (`hr_strip` + `hr_pw`)!
      have hR_den : denoteMeta mp.base2.acval env ψ_R_pos 0 (Core.posOf cvR.levelParams rval) =
          some (mp.base2.acval pheadKey ψ_R_orig) := by
        rw [posOf_denoteMeta]
        have h := mp.defn_reads ψ_R_orig cvR rval ⟨rHint, Ix.Kernel.Semantics.Env.find?_mem hfindR⟩
        have hn : cvR.name = pheadKey := Ix.Kernel.Semantics.Env.find?_name hfindR
        rwa [hn] at h
      obtain ⟨rDs, rBodyA, hR_mk, hrDs_len, hrDs_bits, hrBodyA_den⟩ :=
        denoteMeta_stripLams pargs.length 0 hr_strip hR_den
      simp only [Nat.zero_add] at hrBodyA_den
      have helim_nz : ψ_R_pos 0 ≠ 0 := by
        simp only [ψ_R_pos, ψ_rec, ↓reduceIte]
        exact fun h => hpw0 ((hpl_elim ψ_P).mp h)
      have hnz_rDs : ∀ p ∈ rDs, p.1 ≠ 0 := by
        intro p hp; obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
        have hbi := map_getElem_eq hrDs_bits i hi (by rw [stripLams_length hr_strip]; omega)
        have hpw := hr_pw (rbs[i]'(by rw [stripLams_length hr_strip]; omega)) (List.getElem_mem _)
        rw [hbi, hpw]
        unfold pwBit
        split_ifs with h0
        · exact absurd (by simpa [Ix.Kernel.PropWhen.holds_ifAllZero] using h0) helim_nz
        · exact Nat.one_ne_zero
      have hcl_R : interp V (consList (vs_v ++ [x_v]) ρ₀) (mp.base2.acval pheadKey ψ_R_orig) =
          interp V ρ₀ (mp.base2.acval pheadKey ψ_R_orig) :=
        closed_interp_env (mp.base2.acval_closed _ _) _ _
      rw [interp_mkAppN_foldl, hcl_R, hR_mk] at hfold_P
      rw [hcl_R, hR_mk] at hApp_R_raw
      have hwd_R : WellDenotedV V ρ₀ (mkLamsAV rDs rBodyA) := by
        rw [← hR_mk]; exact ⟨mp.base2.acval_wellDenoted _ _ _, mp.acval_validV _ _ _⟩
      obtain ⟨hfold_R, -, hwd_rBody⟩ := mkLamsAV_appChainOk_pos rDs rBodyA pargsV ρ₀ hnz_rDs
        (by rw [hrDs_len, hpargsV_len]) hwd_R hApp_R_raw
      rw [hfold_R] at hfold_P
      -- 3. Unpack `rBodyA = mkAppN (acval auxRecKey ψ_rec_p) rargsA`!
      rw [openDummiesP_mkAppN, openDummiesP_const] at hrBodyA_den
      obtain ⟨frecA, rargsA, hfrecA, hsp_rargs, hrBodyA_eq⟩ := denoteMeta_mkAppN_inv hrBodyA_den
      have har_lps : arLvls.length = wp.cvAuxRec.levelParams.length := by
        have h1 := (lvEqList_getElem harLvls).1; rw [wp.hAuxRec_lvls]; simpa using h1
      simp only [denoteMeta, wp.hfindAuxRec, ConstantInfo.toConstantVal, har_lps, ↓reduceIte, Option.some.injEq] at hfrecA
      let ψ_rec_p := origVal wp.cvAuxRec.levelParams (ψ_rec pheadLvls bnl ψ_P)
      have hfrecA_eq : frecA = mp.base2.acval wp.auxRecKey ψ_rec_p := by
        rw [← hfrecA, substFn_eq_of_lvEqList harLvls ψ_R_pos]
        refine mp.base2.acval_params wp.auxRecKey _ wp.hfindAuxRec _ _ fun _ _ => ?_
        simp [ψ_rec_p, ψ_R_pos, origVal, Core.posLevels, wp.hAuxRec_lvls]
      rw [hrBodyA_eq, hfrecA_eq] at hwd_rBody hfold_P
      obtain ⟨-, -, hApp_rec_raw⟩ := appChainOk_of_wellDenotedV rargsA hwd_rBody
      let rargsV := rargsA.map (interp V (consList pargsV ρ₀))
      have hrargsA_len : rargsA.length = nP + 1 + wp.anc + 2 := by
        have := denoteMetaSpine_length_eq hsp_rargs; simp only [List.length_map, hrargs_len] at this; exact this.symm
      have hrargsV_last : rargsV[nP + 1 + wp.anc + 1]'(by simp [rargsV, hrargsA_len]) = x_v := by
        simp only [rargsV, List.getElem_map]
        have hden_s := denoteMetaSpine_getElem hsp_rargs (i := nP + 1 + wp.anc + 1) (by simp [hrargs_len])
        simp only [List.getElem_map] at hden_s
        have hsubj : rargs[nP + 1 + wp.anc + 1]'(by omega) = .bvar 0 := by
          rw [List.getElem?_eq_getElem (by omega : nP + 1 + wp.anc + 1 < rargs.length)] at hrargs_subj
          exact Option.some.inj hrargs_subj
        rw [hsubj] at hden_s
        have hden_bv : denoteMeta mp.base2.acval env ψ_R_pos pargs.length (openDummiesP pargs.length 0 0 (.bvar 0)) =
            some (.bvar 0) := denoteMeta_openDummiesP_bvar0 (by omega)
        rw [hden_bv] at hden_s
        rw [(Option.some.inj hden_s).symm, interp_bvar,
          show 0 = pargsV.length - 1 - (pargsV.length - 1) by omega,
          consList_bvar_desc pargsV ρ₀ (by omega)]
        exact hpargsV_last
      have hrargsV_split : rargsV = rargsV.take (nP + 1 + wp.anc + 1) ++ [x_v] := by
        have := List.take_append_drop (nP + 1 + wp.anc + 1) rargsV
        have hdrop : rargsV.drop (nP + 1 + wp.anc + 1) = [x_v] := by
          refine List.ext_getElem (by simp [rargsV, hrargsA_len]) fun i _ hi2 => ?_
          have hi0 : i = 0 := by simp at hi2; omega
          subst hi0; simpa using hrargsV_last
        rw [hdrop] at this; exact this.symm
      have hxs_pref : (rargsV.take (nP + 1 + wp.anc + 1)).take nP = vs_v := by
        rw [List.take_take, Nat.min_eq_left (by omega)]
        refine List.ext_getElem (by rw [List.length_take, List.length_map, hrargsA_len, hvs_len]; omega) fun m hm1 hm2 => ?_
        rw [List.getElem_take]; simp only [rargsV, List.getElem_map]
        have hden_m := denoteMetaSpine_getElem hsp_rargs (i := m) (by simp [hrargs_len]; omega)
        simp only [List.getElem_map] at hden_m
        have heq_m : ExprSemEq (rargs[m]'(by omega)) (.bvar (pargs.length - 1 - m)) := by
          have := forall₂_getElem hrargs_pref m
            (by rw [List.length_take, hrargs_len]; omega) (by simp; omega)
          simpa [List.getElem_take] using this
        have hden_bv : denoteMeta mp.base2.acval env ψ_R_pos pargs.length
            (openDummiesP pargs.length 0 0 (.bvar (pargs.length - 1 - m))) =
            some (.bvar (pargs.length - 1 - m)) := denoteMeta_openDummiesP_bvar0 (by omega)
        have hsame := (denoteMeta_exprSemEq (acval := mp.base2.acval) (env := env) (φ := ψ_R_pos)
          (d := pargs.length) (exprSemEq_openDummiesP heq_m _ 0 0)).symm.trans hden_m
        rw [hden_bv] at hsame
        rw [(Option.some.inj hsame).symm, interp_bvar, show pargs.length - 1 - m = pargsV.length - 1 - m by omega,
          consList_bvar_desc pargsV ρ₀ (by omega)]
        have hget := congrArg (fun l => l[m]?) hpargsV_pref
        rw [List.getElem?_take_of_lt (by omega : m < nP),
          List.getElem?_eq_getElem (by omega : m < pargsV.length),
          List.getElem?_eq_getElem (by omega : m < vs_v.length)] at hget
        exact Option.some.inj hget
      let minIdx := nP + (pargs.length - nP - (wp.anc + 1)) + wp.jIdx
      have hminIdx_lt : minIdx < pargs.length := by have := wp.hjIdx_lt; omega
      have hxs_minJ : (rargsV.take (nP + 1 + wp.anc + 1))[nP + 1 + wp.jIdx]'(by
          rw [List.length_take, List.length_map, hrargsA_len]; have := wp.hjIdx_lt; omega) =
          interp V (consList (vs_v ++ [x_v]) ρ₀) (pargsA[minIdx]'(by omega)) := by
        rw [List.getElem_take]; simp only [rargsV, List.getElem_map]
        have hden_j := denoteMetaSpine_getElem hsp_rargs (i := nP + 1 + wp.jIdx) (by simp [hrargs_len]; have := wp.hjIdx_lt; omega)
        simp only [List.getElem_map] at hden_j
        have heq_j : ExprSemEq (rargs[nP + 1 + wp.jIdx]'(by have := wp.hjIdx_lt; omega))
            (.bvar (wp.anc + 1 - 1 - wp.jIdx)) := by
          have := forall₂_getElem hrargs_minors wp.jIdx
            (by rw [List.length_take, List.length_drop, hrargs_len]; have := wp.hjIdx_lt; omega)
            (by simp [wp.hjIdx_lt])
          simpa [List.getElem_take, List.getElem_drop] using this
        have hden_bv : denoteMeta mp.base2.acval env ψ_R_pos pargs.length
            (openDummiesP pargs.length 0 0 (.bvar (wp.anc + 1 - 1 - wp.jIdx))) =
            some (.bvar (wp.anc + 1 - 1 - wp.jIdx)) := denoteMeta_openDummiesP_bvar0 (by omega)
        have hsame := (denoteMeta_exprSemEq (acval := mp.base2.acval) (env := env) (φ := ψ_R_pos)
          (d := pargs.length) (exprSemEq_openDummiesP heq_j _ 0 0)).symm.trans hden_j
        rw [hden_bv] at hsame
        rw [(Option.some.inj hsame).symm, interp_bvar,
          show wp.anc + 1 - 1 - wp.jIdx = pargsV.length - 1 - minIdx by omega,
          consList_bvar_desc pargsV ρ₀ (by omega)]
        simp [pargsV]
      have hminJ_den : denoteMeta mp.base2.acval env ψ_P (nP + 1)
          (openDummiesP (nP + 1) 0 0 (pargs.getD minIdx default)) =
          some (pargsA[minIdx]'(by omega)) := by
        have hget : pargs.getD minIdx default = pargs[minIdx]'hminIdx_lt := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hminIdx_lt, Option.getD_some]
        rw [hget]
        have h1 := denoteMetaSpine_getElem hsp_pargs (i := minIdx) (by simp [hminIdx_lt])
        simpa only [List.getElem_map] using h1
      have hcl_rec_p : interp V (consList pargsV ρ₀) (mp.base2.acval wp.auxRecKey ψ_rec_p) =
          interp V ρ₀ (mp.base2.acval wp.auxRecKey ψ_rec_p) :=
        closed_interp_env (mp.base2.acval_closed _ _) _ _
      exact hhandle_minor hpl_len hpl_elim hpl_drop hrlJ hrlJ_nf hrlJ_strip hrargsJ_ge hrargsJ_fields
        hminJ_strip hminJ_pw hminor
        (bodyUnpackSpec_viaDefn hfindR hp_strip hrlJ hrlJ_strip hminJ_strip hminor wp.hbody)
        hminJ_den (hwd_pargs _ (List.getElem_mem _))
        (by rw [List.length_take, List.length_map, hrargsA_len]; omega)
        hxs_pref hxs_minJ
        (by
          rw [hP_mk, hpBodyA_eq, hfRA_eq, hR_mk, hrBodyA_eq, hfrecA_eq, hfold_P, interp_mkAppN_foldl, hcl_rec_p]
          change rargsV.foldl SetTheory.app _ = _
          conv_lhs => rw [hrargsV_split])
        (by
          have h1 : AppChainOk (interp V ρ₀ (mp.base2.acval wp.auxRecKey ψ_rec_p)) rargsV :=
            hcl_rec_p ▸ hApp_rec_raw
          rwa [hrargsV_split] at h1)

/-! ## Section 11: `field_chain_coherence` -/

set_option maxHeartbeats 1600000 in
/-- Unified chain-term construction and coherence theorem for one field `fidx < nF` of an eligible
modeled structure: produces a single closed, `ψ 0`-only, `WellDenotedV` chain term `A_chain`
inhabiting `univ (ψ 0 + 1)` whose `chainApp` agrees with `fp.projKey` on every valid `(vs_v, x_v)`
across all three branches of `fp.hpure` (`nP = 0 ∧ bnl = 0`, unconditionally `Prop`, and
`ProjPureWitness`). -/
theorem field_chain_coherence {V : Type u} [SetTheory V] {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Env .anon} {Reg : NativeFam .anon → Prop}
    (ht : t.check = .ok ())
    (hbasis : ∀ ci ∈ IxVM.Refinement.TableInhabit.basisEnv.consts, env.find? ci.name = some ci)
    (hreg : FamRegistryWith FormerOpenTraceAt t E env Reg)
    (hDefnTyped : Decl.DefnTyped env)
    (mp : EnvModelM V .verified env)
    (hN : ∀ fam, Reg fam → NativeFamOk mp fam)
    {tModelKey cModelKey : KKey} {tyTPos ctyMPos fdom rawDom : KExpr}
    {nP bnl nF fidx : Nat}
    {bsT : List (KExpr × BinderMeta)} {structSort : KLevel}
    (hT_sort : tyTPos.stripPis nP = some (bsT, .sort structSort))
    (hT_sort_nz : structSort.isNeverZero = true)
    (hT_pw : ∀ bm ∈ bsT, bm.2.pw = .never)
    (hTM_find : ∃ cvTM mvalTM hintTM, env.find? tModelKey = some (.defnInfo cvTM mvalTM hintTM) ∧
      cvTM.levelParams.length = bnl ∧ cvTM.levelParams.Perm (List.range bnl) ∧
      ExprSemEq (Core.posOf cvTM.levelParams cvTM.type) tyTPos)
    (fp : FieldProjFacts t E env tModelKey cModelKey tyTPos ctyMPos nP bnl nF fidx fdom rawDom)
    (hfidx : fidx < nF)
    (hprojTele : ∃ projKeyAt frest fbm,
      projFieldTeleAt ctyMPos nP bnl projKeyAt fidx = some (.forallE fdom frest fbm))
    (hrawDom_at : (fp.cbsI.map Prod.fst)[nP + fidx]? = some rawDom) :
    ∃ A_chain : (LevelParam → Nat) → AnnotTerm,
      (∀ ψ k, (A_chain ψ).liftN 1 k = A_chain ψ) ∧
      (∀ ψ₁ ψ₂, ψ₁ 0 = ψ₂ 0 → A_chain ψ₁ = A_chain ψ₂) ∧
      (∀ ψ ρ, WellDenotedV V ρ (A_chain ψ)) ∧
      (∀ ψ ρ, interp V ρ (A_chain ψ) ∈ˢ (univ (ψ 0 + 1) : V)) ∧
      (∀ (ψ_P : LevelParam → Nat) (ρ₀ : Nat → V) (vs_v : List V) (x_v : V),
        vs_v.length = nP →
        (∀ cvTM mvalTM hintTM, env.find? tModelKey = some (.defnInfo cvTM mvalTM hintTM) →
          AppChainOk (interp V ρ₀ (mp.base2.acval tModelKey (origVal cvTM.levelParams ψ_P))) vs_v ∧
          x_v ∈ˢ vs_v.foldl SetTheory.app
            (interp V ρ₀ (mp.base2.acval tModelKey (origVal cvTM.levelParams ψ_P)))) →
        Ix.Kernel.chainApp (fun n => interp V ρ₀ (A_chain (fun _ => n))) x_v =
          (vs_v ++ [x_v]).foldl SetTheory.app
            (interp V ρ₀ (mp.base2.acval fp.projKey (origVal fp.cvProj.levelParams ψ_P))) ∧
        ∀ rdomA,
          denoteMeta mp.base2.acval env ψ_P (nP + 1) (openDummiesP (nP + 1) 0 0 fp.rdom) = some rdomA →
          (vs_v ++ [x_v]).foldl SetTheory.app
            (interp V ρ₀ (mp.base2.acval fp.projKey (origVal fp.cvProj.levelParams ψ_P))) ∈ˢ
            interp V (consList (vs_v ++ [x_v]) ρ₀) rdomA) := by
  obtain ⟨cvTM, mvalTM, hintTM, hfindTM, hTM_lvls, hTM_perm, hTM_ty⟩ := hTM_find
  -- Shared setup: from `hApp_TM` + `hx_mem`, derive:
  -- 1. `x_v ∈ˢ univ (structSort.eval ψ_P + 1)`
  -- 2. `AppChainOk (acval fp.projKey (origVal fp.cvProj.levelParams ψ_P)) (vs_v ++ [x_v])`
  -- 3. `∀ rdomA, ... → val ∈ˢ interp (consList (vs_v ++ [x_v]) ρ₀) rdomA ∧ (pwBit ψ_P fp.sbm.pw = 0 → ... ∈ˢ univZero)`
  have hsetup : ∀ (ψ_P : LevelParam → Nat) (ρ₀ : Nat → V) (vs_v : List V) (x_v : V),
      vs_v.length = nP →
      AppChainOk (interp V ρ₀ (mp.base2.acval tModelKey (origVal cvTM.levelParams ψ_P))) vs_v →
      x_v ∈ˢ vs_v.foldl SetTheory.app
        (interp V ρ₀ (mp.base2.acval tModelKey (origVal cvTM.levelParams ψ_P))) →
      x_v ∈ˢ (univ (structSort.eval ψ_P + 1) : V) ∧
      AppChainOk (interp V ρ₀ (mp.base2.acval fp.projKey (origVal fp.cvProj.levelParams ψ_P)))
        (vs_v ++ [x_v]) ∧
      ∀ rdomA,
        denoteMeta mp.base2.acval env ψ_P (nP + 1) (openDummiesP (nP + 1) 0 0 fp.rdom) = some rdomA →
        (vs_v ++ [x_v]).foldl SetTheory.app
          (interp V ρ₀ (mp.base2.acval fp.projKey (origVal fp.cvProj.levelParams ψ_P))) ∈ˢ
          interp V (consList (vs_v ++ [x_v]) ρ₀) rdomA ∧
        (pwBit ψ_P fp.sbm.pw = 0 →
          interp V (consList (vs_v ++ [x_v]) ρ₀) rdomA ∈ˢ (univZero : V)) := by
    intro ψ_P ρ₀ vs_v x_v hvs_len hApp_TM hx_mem
    -- (a) Strip `nP` Pis from `cvTM.type` (`tyTPos`), getting `SpineFit` for `vs_v` and `x_v ∈ˢ univ (structSort.eval ψ_P + 1)`!
    have hmemTM := Ix.Kernel.Semantics.Env.find?_mem hfindTM
    obtain ⟨TTM_a, hTTM_a⟩ := mp.type_reads _ hmemTM (origVal cvTM.levelParams ψ_P)
    have hTTM_mem := mp.mem_type _ hmemTM (origVal cvTM.levelParams ψ_P) TTM_a hTTM_a ρ₀
    have hTTM_wd := mp.type_wellDenotedV _ hmemTM (origVal cvTM.levelParams ψ_P) TTM_a hTTM_a ρ₀
    have hTTM_pos : denoteMeta mp.base2.acval env ψ_P 0 tyTPos = some TTM_a := by
      rw [← denoteMeta_exprSemEq hTM_ty, posOf_denoteMeta]; exact hTTM_a
    obtain ⟨dsT, bodyT, hTTM_mk, hdsT_len, hdsT_bits, hbodyT_den⟩ := denoteMeta_stripPis nP 0 hT_sort hTTM_pos
    simp only [Nat.zero_add] at hbodyT_den
    have hbodyT_eq : bodyT = .sort (structSort.eval ψ_P) := by
      have hopen_s : ∀ (m d c : Nat) (l : KLevel), openDummiesP m d c (.sort l) = .sort l := by
        intro m; induction m with | zero => intros; rfl | succ m ih => intros; exact ih _ _ _
      rw [hopen_s, denoteMeta_sort] at hbodyT_den
      exact (Option.some.inj hbodyT_den).symm
    have hpos_dsT : ∀ d ∈ dsT, d.2.1 ≠ 0 := by
      intro d hd
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
      have hbi := map_getElem_eq hdsT_bits i hi (by rw [stripPis_length_p hT_sort]; omega)
      have hnev := hT_pw (bsT[i]'(by rw [stripPis_length_p hT_sort]; omega)) (List.getElem_mem _)
      rw [hbi, hnev]; simp [pwBit]
    rw [hTTM_mk, hbodyT_eq] at hTTM_mem hTTM_wd
    rw [Ix.Kernel.Semantics.Env.find?_name hfindTM] at hTTM_mem
    have hsp_T : SpineFit ρ₀ (dsT.map (·.2.2)) vs_v :=
      spineFit_of_mkPisAV_appChainOk_pos dsT (.sort (structSort.eval ψ_P)) vs_v ρ₀ hpos_dsT
        (by rw [hdsT_len, hvs_len]) hTTM_mem hApp_TM
    have hTM_u : vs_v.foldl SetTheory.app
        (interp V ρ₀ (mp.base2.acval tModelKey (origVal cvTM.levelParams ψ_P))) ∈ˢ
        (univ (structSort.eval ψ_P) : V) :=
      (appChainOk_and_mem_of_mkPisAV_spineFit dsT (.sort (structSort.eval ψ_P)) vs_v ρ₀
        (by rw [hdsT_len, hvs_len]) hTTM_wd.2 hTTM_mem hsp_T).2.1
    have hx_univ : x_v ∈ˢ (univ (structSort.eval ψ_P + 1) : V) :=
      (univ_isTGUniverse (Nat.succ_ne_zero _)).transitive
        ((univ_isTGUniverse (Nat.succ_ne_zero _)).transitive (univ_mem_univ _) hTM_u) hx_mem
    -- (b) Strip `nP` Pis + 1 subject Pi from `fp.cvProj.type`, transfer `hsp_T` via `fp.hProj_pdoms`
    --     and `hx_mem` via `fp.hProj_sdom`, and apply `appChainOk_and_mem_of_mkPisAV_spineFit`!
    have hmemP := Ix.Kernel.Semantics.Env.find?_mem fp.hfindProj
    obtain ⟨TPa, hTPa⟩ := mp.type_reads _ hmemP (origVal fp.cvProj.levelParams ψ_P)
    have hTPa_mem := mp.mem_type _ hmemP (origVal fp.cvProj.levelParams ψ_P) TPa hTPa ρ₀
    rw [Ix.Kernel.Semantics.Env.find?_name fp.hfindProj] at hTPa_mem
    have hTPa_wd := mp.type_wellDenotedV _ hmemP (origVal fp.cvProj.levelParams ψ_P) TPa hTPa ρ₀
    have hTPa_pos : denoteMeta mp.base2.acval env ψ_P 0 (Core.posOf fp.cvProj.levelParams fp.cvProj.type) = some TPa := by
      rw [posOf_denoteMeta]; exact hTPa
    obtain ⟨dsP, remP, hTPa_mk, hdsP_len, -, hremP_den⟩ :=
      denoteMeta_stripPis nP 0 fp.hProj_strip hTPa_pos
    simp only [Nat.zero_add] at hremP_den
    have hopen_for : ∀ (m d c : Nat) (t b : KExpr) (bm : BinderMeta),
        openDummiesP m d c (.forallE t b bm) =
          .forallE (openDummiesP m d c t) (openDummiesP m d (c + 1) b) bm := by
      intro m; induction m with
      | zero => intros; rfl
      | succ m ih =>
        intro d c t b bm; simp only [openDummiesP, Expr.instantiate1]
        rw [show c + m + 1 = c + 1 + m by omega]; exact ih (d + 1) c _ _ bm
    rw [hopen_for] at hremP_den
    obtain ⟨sdomA, rdomA₀, hsdomA_den, hrdomA₀_den, hremP_eq⟩ := denoteMeta_forallE_some hremP_den
    have hrdom_open_eq : openDummiesP (nP + 1) 0 0 fp.rdom =
        (openDummiesP nP 0 1 fp.rdom).instantiate1 (.fvar nP (.sort .zero)) 0 := by
      simpa [openDummiesP, Nat.zero_add] using openDummiesP_add nP 1 0 fp.rdom
    rw [← hrdom_open_eq] at hrdomA₀_den
    -- Show `dsP.map (·.2.2) = dsT.map (·.2.2)` via `fp.hProj_pdoms`!
    have hdsPT_eq : dsP.map (·.2.2) = dsT.map (·.2.2) := by
      have hlen_tb : fp.tbsP = bsT := by
        have h := Option.some.inj (fp.hT_strip.symm.trans hT_sort)
        exact (Prod.mk.inj h).1
      -- Compare each domain `i < nP` of `fp.hProj_strip` and `hT_sort` via `denoteMeta_stripPis`!
      have hget_dom : ∀ {n : Nat} {e rem : KExpr} {bs : List (KExpr × BinderMeta)} {a : AnnotTerm}
          {ds : List (Nat × Nat × AnnotTerm)} {b : AnnotTerm}
          (hs : e.stripPis n = some (bs, rem)),
          denoteMeta mp.base2.acval env ψ_P 0 e = some a →
          a = mkPisAV ds b → (hlen : ds.length = n) →
          ∀ i (hi : i < n),
            denoteMeta mp.base2.acval env ψ_P i (openDummiesP i 0 0 (bs[i]'(by rw [stripPis_length_p hs]; exact hi)).1) =
              some (ds[i]'(by omega)).2.2 := by
        intro n
        induction n with
        | zero => intro _ _ _ _ _ _ _ _ _ _ i hi; exact nomatch hi
        | succ n ihn =>
          intro e rem bs a ds b hs hden hmk hlen i hi
          -- Strip first `i` Pis and inspect the `i`-th domain!
          obtain ⟨bs1, rem1, bs2, h1, h2, hcat⟩ := stripPis_split (show e.stripPis (i + (n + 1 - i)) = some (bs, rem) by
            rwa [show i + (n + 1 - i) = n + 1 by omega])
          have hsub : n + 1 - i = (n - i) + 1 := by omega
          rw [hsub] at h2
          cases hrm : rem1 with
          | forallE d_i b_i bm_i =>
            rw [hrm] at h2 h1
            simp only [Expr.stripPis, Option.map_eq_some_iff] at h2
            obtain ⟨⟨bs2', _⟩, _, hp⟩ := h2
            injection hp with hbs2 _
            obtain ⟨ds1, remA1, hmk1, hds1_len, -, hremA1_den⟩ := denoteMeta_stripPis i 0 h1 hden
            simp only [Nat.zero_add] at hremA1_den
            rw [hopen_for] at hremA1_den
            obtain ⟨dA_i, _, hdA_i, -, hremA1_eq⟩ := denoteMeta_forallE_some hremA1_den
            have hbi_eq : (bs[i]'(by rw [stripPis_length_p hs]; exact hi)).1 = d_i := by
              have hlen1 : bs1.length = i := stripPis_length_p h1
              simp only [hcat, ← hbs2, List.getElem_append_right (by omega : bs1.length ≤ i), hlen1,
                Nat.sub_self, List.getElem_cons_zero]
            rw [hbi_eq, hdA_i]
            congr 1
            have hds_split : ds = ds.take i ++ ds[i]'(by omega) :: ds.drop (i + 1) := by
              rw [← List.drop_eq_getElem_cons, List.take_append_drop]
            rw [hds_split, mkPisAV_append, mkPisAV] at hmk
            have hgo : ∀ (l1 l2 : List (Nat × Nat × AnnotTerm)) (b1 b2 : AnnotTerm),
                l1.length = l2.length → mkPisAV l1 b1 = mkPisAV l2 b2 → b1 = b2 := by
              intro l1; induction l1 with
              | nil => intro l2 _ _ hl h; cases l2 with | nil => exact h | cons _ _ => simp at hl
              | cons _ l1 ih =>
                intro l2 b1 b2 hl h; cases l2 with
                | nil => simp at hl
                | cons _ l2 => simp only [mkPisAV] at h; exact ih l2 b1 b2 (by simpa using hl) (AnnotTerm.pi.inj h).2.2.2
            have hb_eq := hgo ds1 (ds.take i) remA1 _ (by rw [hds1_len, List.length_take]; omega)
              (hmk1.symm.trans hmk)
            rw [← hremA1_eq] at hb_eq
            exact (AnnotTerm.pi.inj hb_eq).2.2.1
          | _ => rw [hrm] at h2; simp [Expr.stripPis] at h2
      refine List.ext_getElem (by simp [hdsP_len, hdsT_len]) fun i hi1 hi2 => ?_
      simp only [List.getElem_map]
      have hi : i < nP := by simp [hdsP_len] at hi1; exact hi1
      have h1 := hget_dom fp.hProj_strip hTPa_pos hTPa_mk hdsP_len i hi
      have h2 := hget_dom hT_sort hTTM_pos hTTM_mk hdsT_len i hi
      have heq_i : ExprSemEq (fp.pbsP[i]'(by rw [stripPis_length_p fp.hProj_strip]; exact hi)).1
          (bsT[i]'(by rw [stripPis_length_p hT_sort]; exact hi)).1 := by
        have h := forall₂_getElem fp.hProj_pdoms i
          (by rw [List.length_map, stripPis_length_p fp.hProj_strip]; exact hi)
          (by rw [List.length_map, hlen_tb, stripPis_length_p hT_sort]; exact hi)
        simpa [hlen_tb] using h
      have hsame := (denoteMeta_exprSemEq (acval := mp.base2.acval) (env := env) (φ := ψ_P) (d := i)
        (exprSemEq_openDummiesP heq_i i 0 0)).symm.trans h1
      rw [h2] at hsame
      exact (Option.some.inj hsame).symm
    -- Show `interp (consList vs_v ρ₀) sdomA = vs_v.foldl app (interp ρ₀ (acval tModelKey (origVal cvTM.levelParams ψ_P)))`!
    have hsdom_val : interp V (consList vs_v ρ₀) sdomA =
        vs_v.foldl SetTheory.app (interp V ρ₀ (mp.base2.acval tModelKey (origVal cvTM.levelParams ψ_P))) := by
      have hsame := (denoteMeta_exprSemEq (acval := mp.base2.acval) (env := env) (φ := ψ_P) (d := nP)
        (exprSemEq_openDummiesP fp.hProj_sdom nP 0 0)).symm.trans hsdomA_den
      rw [openDummiesP_mkAppN, openDummiesP_const] at hsame
      obtain ⟨ftmA, sargsA, hftmA, hsp_sa, hsdomA_eq⟩ := denoteMeta_mkAppN_inv hsame
      have hlen_l : ((List.range bnl).map Level.param).length = cvTM.levelParams.length := by simp [hTM_lvls]
      simp only [denoteMeta, hfindTM, ConstantInfo.toConstantVal, hlen_l, ↓reduceIte, Option.some.injEq] at hftmA
      have hftmA_eq : ftmA = mp.base2.acval tModelKey (origVal cvTM.levelParams ψ_P) := by
        rw [← hftmA]
        refine mp.base2.acval_params tModelKey _ hfindTM _ _ fun _ _ => ?_
        simp [origVal, Core.posLevels, hTM_lvls]
      have hsargsV_eq : sargsA.map (interp V (consList vs_v ρ₀)) = vs_v := by
        have hsA_len : sargsA.length = nP := by
          have := denoteMetaSpine_length_eq hsp_sa; simpa using this.symm
        refine List.ext_getElem (by simp [hsA_len, hvs_len]) fun i hi1 hi2 => ?_
        simp only [List.getElem_map]
        have hden_i := denoteMetaSpine_getElem hsp_sa (i := i) (by simp; omega)
        simp only [List.getElem_map, List.getElem_range] at hden_i
        have hden_bv : denoteMeta mp.base2.acval env ψ_P nP (openDummiesP nP 0 0 (.bvar (nP - 1 - i))) =
            some (.bvar (nP - 1 - i)) := denoteMeta_openDummiesP_bvar0 (by omega)
        rw [hden_bv] at hden_i
        rw [(Option.some.inj hden_i).symm, interp_bvar, ← hvs_len, consList_bvar_desc vs_v ρ₀ (by omega)]
      rw [hsdomA_eq, hftmA_eq, interp_mkAppN_foldl, hsargsV_eq,
        closed_interp_env (mp.base2.acval_closed tModelKey _) _ ρ₀]
    -- Combine `hsp_T` + `hx_mem` into `SpineFit ρ₀ ((dsP ++ [(0, pwBit ψ_P fp.sbm.pw, sdomA)]).map (·.2.2)) (vs_v ++ [x_v])`!
    have hTPa_all : TPa = mkPisAV (dsP ++ [(0, pwBit ψ_P fp.sbm.pw, sdomA)]) rdomA₀ := by
      simp only [hTPa_mk, mkPisAV_append, mkPisAV, ← hremP_eq]
    have hsp_all : SpineFit ρ₀
        ((dsP ++ [(0, pwBit ψ_P fp.sbm.pw, sdomA)]).map fun d : Nat × Nat × AnnotTerm => d.2.2)
        (vs_v ++ [x_v]) := by
      rw [List.map_append]
      refine (spineFit_append_iff (by simp [hdsP_len, hvs_len])).mpr ⟨?_, ?_⟩
      · rw [hdsPT_eq]; exact hsp_T
      · simp only [List.map_cons, List.map_nil, SpineFit]
        exact ⟨by rwa [hsdom_val], trivial⟩
    rw [hTPa_all] at hTPa_mem hTPa_wd
    obtain ⟨hApp_P, hmem_r0, _⟩ := appChainOk_and_mem_of_mkPisAV_spineFit
      (dsP ++ [(0, pwBit ψ_P fp.sbm.pw, sdomA)]) rdomA₀ (vs_v ++ [x_v]) ρ₀
      (by simp [hdsP_len, hvs_len]) hTPa_wd.2 hTPa_mem hsp_all
    -- Also extract `AnnotValid` at the subject Pi (`dsP` peeled) for `pwBit ψ_P fp.sbm.pw = 0 → rdomA₀ ∈ˢ univZero`!
    have hval_sub : AnnotValid V (consList vs_v ρ₀) (.pi 0 (pwBit ψ_P fp.sbm.pw) sdomA rdomA₀) := by
      have hTPa_wd_pre : AnnotValid V ρ₀ (mkPisAV dsP (.pi 0 (pwBit ψ_P fp.sbm.pw) sdomA rdomA₀)) := by
        simpa only [mkPisAV_append, mkPisAV] using hTPa_wd.2
      have hTPa_mem_pre : interp V ρ₀ (mp.base2.acval fp.projKey (origVal fp.cvProj.levelParams ψ_P)) ∈ˢ
          interp V ρ₀ (mkPisAV dsP (.pi 0 (pwBit ψ_P fp.sbm.pw) sdomA rdomA₀)) := by
        simpa only [mkPisAV_append, mkPisAV] using hTPa_mem
      exact (appChainOk_and_mem_of_mkPisAV_spineFit dsP _ vs_v ρ₀ (by rw [hdsP_len, hvs_len])
        hTPa_wd_pre hTPa_mem_pre (by rw [hdsPT_eq]; exact hsp_T)).2.2
    refine ⟨hx_univ, hApp_P, fun rdomA hrdomA => ?_⟩
    have hr_eq : rdomA = rdomA₀ := Option.some.inj (hrdomA.symm.trans hrdomA₀_den)
    subst hr_eq
    refine ⟨hmem_r0, fun hpw0 => ?_⟩
    rw [AnnotValid_pi] at hval_sub
    rw [consList_append, consList]
    exact hval_sub.2.2 hpw0 x_v (by rwa [hsdom_val])
  -- Now dispatch on the 3 branches of `fp.hpure`!
  rcases fp.hpure with ⟨hnP0, hbnl0⟩ | hall0 | hwp
  · -- **BRANCH 1 (`nP = 0 ∧ bnl = 0`):** `A_chain ψ := .bgraph (ψ 0) (mp.base2.acval fp.projKey (fun _ => 0))`
    refine ⟨fun ψ => .bgraph (ψ 0) (mp.base2.acval fp.projKey (fun _ => 0)),
      fun ψ k => by simp [AnnotTerm.liftN, mp.base2.acval_closed],
      fun ψ₁ ψ₂ h0 => by simp [h0],
      fun ψ ρ => ⟨by rw [WellDenoted_bgraph]; exact mp.base2.acval_wellDenoted _ _ _,
        by rw [AnnotValid_bgraph]; exact mp.acval_validV _ _ _⟩,
      fun ψ ρ => by
        rw [interp_bgraph]
        exact Ix.Kernel.SetModel.boundedGraph_mem_univ _ (ψ 0),
      fun ψ_P ρ₀ vs_v x_v hvs_len hTM_all => ?_⟩
    obtain ⟨hApp_TM, hx_mem⟩ := hTM_all cvTM mvalTM hintTM hfindTM
    obtain ⟨hx_univ, hApp_P, hrdom_mem⟩ := hsetup ψ_P ρ₀ vs_v x_v hvs_len hApp_TM hx_mem
    have hvs_nil : vs_v = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hvs_nil
    -- Since `bnl = 0`, `fp.cvProj.levelParams = []`, so `origVal fp.cvProj.levelParams ψ_P = fun _ => 0` up to `acval_params`!
    have hac_eq : mp.base2.acval fp.projKey (origVal fp.cvProj.levelParams ψ_P) =
        mp.base2.acval fp.projKey (fun _ => 0) :=
      mp.base2.acval_params fp.projKey _ fp.hfindProj _ _ fun q hq => by
        have := fp.hProj_lvls
        have hlen0 : fp.cvProj.levelParams.length = 0 := by omega
        simp only [ConstantInfo.toConstantVal] at hq
        rw [List.eq_nil_of_length_eq_zero hlen0] at hq; exact nomatch hq
    -- Prove `interp ρ₀ (acval fp.projKey (fun _ => 0)) ∈ˢ univ (U + 1)` via `hDefnTyped`!
    have hF_univ : ∃ W : Nat, W ≠ 0 ∧
        interp V ρ₀ (mp.base2.acval fp.projKey (fun _ => 0)) ∈ˢ (univ W : V) := by
      obtain ⟨⟨stype, uT, hinfT, hredT⟩, -⟩ :=
        hDefnTyped fp.projKey fp.cvProj fp.projVal fp.projHint fp.hProj_nonAux fp.hfindProj
      have hmemP := Ix.Kernel.Semantics.Env.find?_mem fp.hfindProj
      obtain ⟨TPa, hTPa⟩ := mp.type_reads _ hmemP (fun _ => 0)
      have hTPa_mem := mp.mem_type _ hmemP (fun _ => 0) TPa hTPa ρ₀
      rw [Ix.Kernel.Semantics.Env.find?_name fp.hfindProj] at hTPa_mem
      have hwfP := mp.base2.wf _ hmemP
      have hsc := Ix.Kernel.Model.sortClaim_rulesJ_of mp (fun _ => 0) (Δa := [])
        hinfT hredT (Expr.WScoped.of_not_hasFvar hwfP.1) hwfP.2.2.2.1
        (Ix.Kernel.Expr.LeavesBounded.of_not_hasFvar hwfP.1)
        (CtxOk.nil (Ix.Kernel.Expr.fvarLeaves_eq_nil_of_not_hasFvar hwfP.1)) hTPa ρ₀
        (Ix.Kernel.Semantics.Sat_nil V ρ₀)
      have hTPa_u : interp V ρ₀ TPa ∈ˢ (univ (uT.eval (fun _ => 0)) : V) := hsc.2
      refine ⟨uT.eval (fun _ => 0) + 1, Nat.succ_ne_zero _, ?_⟩
      exact (univ_isTGUniverse (Nat.succ_ne_zero _)).transitive
        ((univ_isTGUniverse (Nat.succ_ne_zero _)).transitive (univ_mem_univ _) hTPa_u) hTPa_mem
    obtain ⟨W, hW, hFW⟩ := hF_univ
    have happ_univ : SetTheory.app (interp V ρ₀ (mp.base2.acval fp.projKey (fun _ => 0))) x_v ∈ˢ (univ W : V) := by
      unfold SetTheory.app
      split
      · exact (univ_isTGUniverse hW).pt_mem (empty_mem_univ W)
      · have hU := univ_isTGUniverse (V := V) hW
        exact hU.sUnion_mem (hU.mem_of_subset_mem (hU.sUnion_mem (hU.sUnion_mem hFW)) sep_subset)
    have hch : Ix.Kernel.chainApp
        (fun n => interp V ρ₀ (.bgraph n (mp.base2.acval fp.projKey (fun _ => 0)))) x_v =
        SetTheory.app (interp V ρ₀ (mp.base2.acval fp.projKey (fun _ => 0))) x_v := by
      simp only [interp_bgraph]
      refine Ix.Kernel.SetModel.chainApp_boundedGraph ⟨Nat.max (structSort.eval ψ_P + 1) W, ?_, ?_⟩
      · exact univ_mono (Nat.le_max_left _ _) _ hx_univ
      · exact univ_mono (Nat.le_max_right _ _) _ happ_univ
    refine ⟨?_, fun rdomA hr => (hrdom_mem rdomA hr).1⟩
    simpa [hac_eq] using hch
  · -- **BRANCH 2 (`∀ φ, pwBit φ fp.sbm.pw = 0`):** `A_chain ψ := .bgraph (ψ 0) .prf`
    refine ⟨fun ψ => .bgraph (ψ 0) .prf,
      fun _ _ => rfl,
      fun _ _ h0 => by simp [h0],
      fun _ _ => ⟨by rw [WellDenoted_bgraph, WellDenoted_prf]; trivial,
        by rw [AnnotValid_bgraph, AnnotValid_prf]; trivial⟩,
      fun ψ ρ => by
        rw [interp_bgraph]
        exact Ix.Kernel.SetModel.boundedGraph_mem_univ _ (ψ 0),
      fun ψ_P ρ₀ vs_v x_v hvs_len hTM_all => ?_⟩
    obtain ⟨hApp_TM, hx_mem⟩ := hTM_all cvTM mvalTM hintTM hfindTM
    obtain ⟨hx_univ, -, hrdom_mem⟩ := hsetup ψ_P ρ₀ vs_v x_v hvs_len hApp_TM hx_mem
    -- Show `val = pt` from `hrdom_mem` + `hall0 ψ_P`!
    have hmemP := Ix.Kernel.Semantics.Env.find?_mem fp.hfindProj
    obtain ⟨TPa, hTPa⟩ := mp.type_reads _ hmemP (origVal fp.cvProj.levelParams ψ_P)
    have hTPa_pos : denoteMeta mp.base2.acval env ψ_P 0 (Core.posOf fp.cvProj.levelParams fp.cvProj.type) = some TPa := by
      rw [posOf_denoteMeta]; exact hTPa
    obtain ⟨_, _, -, -, -, hremP_den⟩ := denoteMeta_stripPis nP 0 fp.hProj_strip hTPa_pos
    simp only [Nat.zero_add] at hremP_den
    have hopen_for : ∀ (m d c : Nat) (t b : KExpr) (bm : BinderMeta),
        openDummiesP m d c (.forallE t b bm) =
          .forallE (openDummiesP m d c t) (openDummiesP m d (c + 1) b) bm := by
      intro m; induction m with
      | zero => intros; rfl
      | succ m ih =>
        intro d c t b bm; simp only [openDummiesP, Expr.instantiate1]
        rw [show c + m + 1 = c + 1 + m by omega]; exact ih (d + 1) c _ _ bm
    rw [hopen_for] at hremP_den
    obtain ⟨_, rdomA₀, -, hrdomA₀_den, -⟩ := denoteMeta_forallE_some hremP_den
    have hrdom_open_eq : openDummiesP (nP + 1) 0 0 fp.rdom =
        (openDummiesP nP 0 1 fp.rdom).instantiate1 (.fvar nP (.sort .zero)) 0 := by
      simpa [openDummiesP, Nat.zero_add] using openDummiesP_add nP 1 0 fp.rdom
    rw [← hrdom_open_eq] at hrdomA₀_den
    obtain ⟨hval_mem, hr0⟩ := hrdom_mem rdomA₀ hrdomA₀_den
    have hval_pt : (vs_v ++ [x_v]).foldl SetTheory.app
        (interp V ρ₀ (mp.base2.acval fp.projKey (origVal fp.cvProj.levelParams ψ_P))) = pt :=
      eq_pt_of_mem_univZero (hr0 (hall0 ψ_P)) hval_mem
    have hch : Ix.Kernel.chainApp (fun n => interp V ρ₀ (.bgraph n .prf)) x_v = pt := by
      simp only [interp_bgraph, interp_prf]
      have happ_pt : SetTheory.app (pt : V) x_v = pt := by
        simpa using foldl_app_pt (V := V) [x_v]
      have h1 : Ix.Kernel.chainApp
          (Ix.Kernel.SetModel.boundedGraph (fun x => SetTheory.app (pt : V) x)) x_v =
          SetTheory.app (pt : V) x_v := by
        refine Ix.Kernel.SetModel.chainApp_boundedGraph ⟨structSort.eval ψ_P + 1, hx_univ, ?_⟩
        rw [happ_pt]; exact (univ_isTGUniverse (Nat.succ_ne_zero _)).pt_mem (empty_mem_univ _)
      rw [h1, happ_pt]
    exact ⟨by rw [hch, hval_pt], fun rdomA hr => (hrdom_mem rdomA hr).1⟩
  · -- **BRANCH 3 (`ProjPureWitness`):** `A_chain ψ := .const (.unpackGraph (bodyUnpackSpec wp.hbody)) [ψ 0, fidx + 1]`
    obtain ⟨wp⟩ := hwp
    let spec := bodyUnpackSpec wp.hbody
    refine ⟨fun ψ => .const (.unpackGraph spec) [ψ 0, fidx + 1],
      fun _ _ => rfl,
      fun _ _ h0 => by simp [h0],
      fun _ _ => ⟨by rw [WellDenoted_const]; trivial, by rw [AnnotValid_const]; trivial⟩,
      fun ψ ρ => by
        simp only [interp_const, Ix.Kernel.SetModel.bval, Ix.Kernel.Term.lv, List.getD_cons_zero]
        exact Ix.Kernel.SetModel.boundedGraph_mem_univ _ (ψ 0),
      fun ψ_P ρ₀ vs_v x_v hvs_len hTM_all => ?_⟩
    obtain ⟨hApp_TM, hx_mem⟩ := hTM_all cvTM mvalTM hintTM hfindTM
    obtain ⟨hx_univ, hApp_P, hrdom_mem⟩ := hsetup ψ_P ρ₀ vs_v x_v hvs_len hApp_TM hx_mem
    have hcvTM_eq : wp.cvmT = cvTM := by
      have := Option.some.inj (wp.hfindTM.symm.trans hfindTM)
      exact (ConstantInfo.defnInfo.inj this).1
    obtain ⟨⟨N, hopt⟩, hval_eq⟩ := projPure_coherence ht hbasis hreg mp hN fp wp hfidx hprojTele
      hrawDom_at ψ_P ρ₀ vs_v x_v hvs_len (by rw [hcvTM_eq]; exact hApp_TM)
      (by rw [hcvTM_eq]; exact hx_mem) hApp_P hrdom_mem
    have hproj_u : projS (fidx + 1) x_v ∈ˢ (univ (structSort.eval ψ_P + 1) : V) :=
      projS_mem_univ (Nat.succ_ne_zero _) (fidx + 1) hx_univ
    have htu_u : Ix.Kernel.SetModel.treeUnpack spec (projS (fidx + 1) x_v) ∈ˢ
        (univ (structSort.eval ψ_P + 1) : V) :=
      treeUnpackOpt_mem_univ (Nat.succ_ne_zero _) spec N hproj_u hopt
    have hch : Ix.Kernel.chainApp
        (fun n => interp V ρ₀ (.const (.unpackGraph spec) [n, fidx + 1])) x_v =
        Ix.Kernel.SetModel.treeUnpack spec (projS (fidx + 1) x_v) := by
      simp only [interp_const, Ix.Kernel.SetModel.bval, Ix.Kernel.Term.lv, List.getD_cons_zero,
        List.getD_cons_succ]
      exact Ix.Kernel.SetModel.chainApp_boundedGraph ⟨structSort.eval ψ_P + 1, hx_univ, htu_u⟩
    exact ⟨hch.trans hval_eq.symm, fun rdomA hr => (hrdom_mem rdomA hr).1⟩

end IxVM.Refinement.Typing.FamilyAlias