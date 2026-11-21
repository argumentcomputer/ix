import IxVMRefinement.FamilyAlias.ProjCoherenceEval

/-! # Coherence theorems for modeled structure projections

Completes the set-model coherence proof linking a checked modeled structure projection advice
definition (`proj_i`) to a level- and parameter-independent graph chain:

* **Section 9**: `unpackSpecOf`, `unpack_eval_induction` (via `lfpFamSet_induction` on `aux`),
  and `projPure_coherence` (handling both the positive and squash regimes, both `.direct` and
  `.viaDefn`, and both `.bvar` and `.unpack`);
* **Section 10**: `field_chain_coherence`, unifying all three branches of `FieldProjFacts.hpure`
  (`nP = 0 ∧ bnl = 0`, unconditionally `Prop`, and `ProjPureWitness`) into one closed,
  `ψ 0`-only, `WellDenotedV` chain term `A_chain` whose `chainApp` equals `proj_i`. -/

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

/-! ## Section 9: `UnpackSpec` construction, `unpack_eval_induction`, and `projPure_coherence` -/

/-- Helper: extract `ks.getD l .ordinary = .recursive` from `classifyFixKinds = .ok` when field
`l`'s domain is `Expr.mkAppN (.const T _) _`. -/
private theorem kind_recursive_of_head_eq {T : KKey} {lps : List LevelParam} {nP nIdx : Nat}
    {ctorsA : List (ConstantVal .anon × Nat)} {kinds : List (List Ix.Kernel.RecFieldKind)}
    (hcls : Ix.Kernel.classifyFixKinds (m := Ix.Kernel.CheckM .anon) T lps nP nIdx ctorsA = .ok kinds)
    {k : Nat} {cA : ConstantVal .anon × Nat} {ks : List Ix.Kernel.RecFieldKind}
    (hcA : ctorsA[k]? = some cA) (hks : kinds[k]? = some ks)
    {bsP bsF : List (KExpr × BinderMeta)} {remP remF : KExpr}
    (hP : cA.1.type.stripPis nP = some (bsP, remP))
    (hF : remP.stripPis cA.2 = some (bsF, remF))
    {l : Nat} (hl : l < cA.2) {kfLvls : List KLevel} {kfArgs : List KExpr}
    (hdom : (bsF.map Prod.fst).getD l default = Expr.mkAppN (.const T kfLvls) kfArgs) :
    ks.getD l .ordinary = .recursive := by
  unfold Ix.Kernel.classifyFixKinds at hcls
  cases hmap : ctorsA.mapM (Ix.Kernel.recCtorKinds T lps nP nIdx) with
  | none => simp [hmap, Ix.Kernel.unwrapOr, bind, Except.bind] at hcls
  | some kss =>
    simp only [hmap, Ix.Kernel.unwrapOr, bind, Except.bind, pure, Except.pure] at hcls
    by_cases hneg : kss.any (fun ks => ks.any (· == .negative)) = true
    · simp [hneg, throw, throwThe, MonadExceptOf.throw] at hcls
    · by_cases huns : kss.any (fun ks => ks.any (· == .unsupported)) = true
      · simp [hneg, huns, throw, throwThe, MonadExceptOf.throw] at hcls
      · simp only [hneg, huns, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hcls
        have hnoNeg : ¬ kss.any (fun ks => ks.any (· == .negative)) = true := hneg
        have hnoUnsup : ¬ kss.any (fun ks => ks.any (· == .unsupported)) = true := huns
        subst hcls
        -- Retrieve `recCtorKinds ... cA = some ks` from `mapM`
        have hrecK : Ix.Kernel.recCtorKinds T lps nP nIdx cA = some ks := by
          have hgo : ∀ (xs : List (ConstantVal .anon × Nat)) (ys : List (List Ix.Kernel.RecFieldKind)) (idx : Nat),
              xs.mapM (Ix.Kernel.recCtorKinds T lps nP nIdx) = some ys →
              xs[idx]? = some cA → ys[idx]? = some ks →
              Ix.Kernel.recCtorKinds T lps nP nIdx cA = some ks := by
            intro xs
            induction xs with
            | nil => intro _ _ _ hx _; simp at hx
            | cons x xs ih =>
              intro ys idx hm hx hy
              simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hm
              obtain ⟨y, hy0, ys', hys', hys_eq⟩ := hm
              subst hys_eq
              cases idx with
              | zero =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
                subst hx hy; exact hy0
              | succ idx' =>
                simp only [List.getElem?_cons_succ] at hx hy
                exact ih ys' idx' hys' hx hy
          exact hgo ctorsA kss k hmap hcA hks
        have hks_mem : ks ∈ kss := List.mem_of_getElem? hks
        have hnoN : ∀ x ∈ ks, x ≠ .negative := by
          intro x hx heq; subst heq
          apply hnoNeg
          simp only [List.any_eq_true, beq_iff_eq]
          exact ⟨ks, hks_mem, _, hx, rfl⟩
        have hnoU : ∀ x ∈ ks, x ≠ .unsupported := by
          intro x hx heq; subst heq
          apply hnoUnsup
          simp only [List.any_eq_true, beq_iff_eq]
          exact ⟨ks, hks_mem, _, hx, rfl⟩
        have hstAll : cA.1.type.stripPis (nP + cA.2) = some (bsP ++ bsF, remF) :=
          Ix.Kernel.stripPis_append nP hP hF
        unfold Ix.Kernel.recCtorKinds at hrecK
        rw [hstAll] at hrecK
        dsimp only at hrecK
        split at hrecK
        · injection hrecK with hks_eq
          have hl_mem : ks[l]'(by rw [← hks_eq]; simp [hl]) ∈ ks := List.getElem_mem _
          have hget : ks.getD l .ordinary = ks[l]'(by rw [← hks_eq]; simp [hl]) := by
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show l < ks.length by rw [← hks_eq]; simp [hl])]
          rw [hget]
          have hval : ks[l]'(by rw [← hks_eq]; simp [hl]) =
              match Ix.Kernel.recFieldKind T lps nP nIdx l ((bsP ++ bsF).getD (nP + l) default).1 with
              | .recursive => if Ix.Kernel.structUsedLater cA.1.type nP l then .unsupported else .recursive
              | .reflexive => if Ix.Kernel.structUsedLater cA.1.type nP l then .unsupported else .reflexive
              | k => k := by
            simp only [← hks_eq, List.getElem_map, List.getElem_range]
            rfl
          have hlenP : bsP.length = nP := stripPis_length_p hP
          have hlenF : bsF.length = cA.2 := stripPis_length_p hF
          have hdom_eq : ((bsP ++ bsF).getD (nP + l) default).1 = Expr.mkAppN (.const T kfLvls) kfArgs := by
            rw [← hdom]
            simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : bsP.length ≤ nP + l),
              hlenP, Nat.add_sub_cancel_left, List.getElem?_map,
              List.getElem?_eq_getElem (show l < bsF.length by omega), Option.map_some, Option.getD_some]
          rw [hdom_eq] at hval
          -- `mkAppN (.const T kfLvls) kfArgs` mentions `T` and is not `.forallE`
          have hment : (Expr.mkAppN (.const T kfLvls) kfArgs).mentionsConst T = true := by
            have hgo : ∀ (as : List KExpr) (f : KExpr), f.mentionsConst T = true →
                (Expr.mkAppN f as).mentionsConst T = true := by
              intro as
              induction as with
              | nil => intro f hf; exact hf
              | cons a as ih =>
                intro f hf
                exact ih (.app f a) (by simp [Ix.Kernel.Expr.mentionsConst, hf])
            exact hgo kfArgs (.const T kfLvls) (by simp [Ix.Kernel.Expr.mentionsConst])
          have hnotFor : ∀ t b m, Expr.mkAppN (.const T kfLvls) kfArgs ≠ .forallE t b m := by
            have hgo : ∀ (as : List KExpr) (f : KExpr), (∀ t b m, f ≠ .forallE t b m) →
                ∀ t b m, Expr.mkAppN f as ≠ .forallE t b m := by
              intro as
              induction as with
              | nil => intro f hf; exact hf
              | cons a as ih =>
                intro f _
                exact ih (.app f a) (fun _ _ _ h => nomatch h)
            exact hgo kfArgs (.const T kfLvls) (fun _ _ _ h => nomatch h)
          -- Inspect `recFieldKind` = `recPositivity ... 0`
          have hrfk : Ix.Kernel.recFieldKind T lps nP nIdx l (Expr.mkAppN (.const T kfLvls) kfArgs) = .recursive ∨
              Ix.Kernel.recFieldKind T lps nP nIdx l (Expr.mkAppN (.const T kfLvls) kfArgs) = .negative ∨
              Ix.Kernel.recFieldKind T lps nP nIdx l (Expr.mkAppN (.const T kfLvls) kfArgs) = .unsupported := by
            unfold Ix.Kernel.recFieldKind
            simp only [hment, ↓reduceIte]
            cases he : Expr.mkAppN (.const T kfLvls) kfArgs with
            | forallE t b m => exact absurd he (hnotFor t b m)
            | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _ | lit _
            | proj _ _ _ =>
              rw [he] at hment
              simp only [Ix.Kernel.recPositivity, hment, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              split
              · split
                · split
                  · exact Or.inl rfl
                  · exact Or.inr (Or.inl rfl)
                · exact Or.inr (Or.inl rfl)
              · split
                · split
                  · exact Or.inr (Or.inl rfl)
                  · exact Or.inr (Or.inr rfl)
                · exact Or.inr (Or.inr rfl)
          have hneN := hnoN _ hl_mem
          have hneU := hnoU _ hl_mem
          rcases hrfk with hr | hn | hu
          · rw [hr] at hval
            dsimp only at hval
            split at hval
            · exact absurd hval hneU
            · exact hval
          · rw [hn] at hval; exact absurd hval hneN
          · rw [hu] at hval; exact absurd hval hneU
        · injection hrecK with hks_eq
          have h0 : ks[l]'(by rw [← hks_eq]; simp [hl]) = .negative := by simp [← hks_eq]
          exact absurd h0 (hnoN _ (List.getElem_mem _))

/-- Helper: evaluate a `substLevel l us` when `us.length = n`. -/
theorem eval_substLevel_eq_substFn {n : Nat} {us : List KLevel} (hus : us.length = n)
    (φ : LevelParam → Nat) (l : KLevel) :
    (substLevel l us).eval φ = l.eval (Level.substFn φ (List.range n) us) := by
  rw [IxVM.Refinement.KernelLevels.eval_substLevel_eq_subst, Ix.Kernel.Level.eval_subst, hus]

private theorem map_getElem_eq {α β : Type _} {f : α → Nat} {g : β → Nat} {l1 : List α} {l2 : List β}
    (h : l1.map f = l2.map g) (i : Nat) (hi1 : i < l1.length) (hi2 : i < l2.length) :
    f l1[i] = g l2[i] := by
  have hget := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2,
    Option.map_some, Option.some.injEq] at hget
  exact hget

private theorem mkLamsC_eq_mkLamsAV (w : Nat) :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (body : AnnotTerm),
      mkLamsC w ds body = mkLamsAV (ds.map fun d => (w, d.2.2)) body
  | [], _ => rfl
  | d :: ds, body => congrArg (AnnotTerm.lam w d.2.2) (mkLamsC_eq_mkLamsAV w ds body)

private theorem mkAppN_append (f : KExpr) (xs ys : List KExpr) :
    Expr.mkAppN f (xs ++ ys) = Expr.mkAppN (Expr.mkAppN f xs) ys := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih => exact ih (.app f x)

/-- Bundled witness for the rebuild branch of an `UnpackMinorWitness` (allows a single
`Classical.choice` in `unpackRuleOf`). -/
structure UnpackRebuildMatch {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {env : Env .anon}
    {auxKey auxRecKey auxCtorKey : KKey} {auxRecLps : List LevelParam}
    {nP bnl anc k : Nat} {minorK : KExpr} {rl : RecRule .anon}
    (umw : UnpackMinorWitness t E env auxKey auxRecKey auxRecLps auxCtorKey nP bnl anc k minorK rl) where
  cvMC : ConstantVal .anon
  cnp : Nat
  mcIndKey : KKey
  cvMCI : ConstantVal .anon
  capsMCI : Ix.Kernel.IndCaps .anon
  ini : Nat
  sortL : KLevel
  cvAuxC : ConstantVal .anon
  bsP : List (KExpr × BinderMeta)
  bsF : List (KExpr × BinderMeta)
  remP : KExpr
  remF : KExpr
  hmc_ne : umw.mcKey ≠ auxCtorKey
  hfindMC : env.find? umw.mcKey = some (.ctorInfo cvMC cnp umw.rnf)
  hcnp_pos : 0 < cnp
  hmcLvls_len : umw.mcLvls.length = cvMC.levelParams.length
  hmargs_len : umw.margs.length = cnp + umw.rnf
  hfindMCI : env.find? mcIndKey = some (.indInfo cvMCI capsMCI)
  hMCI_lvls : cvMCI.levelParams.length = cvMC.levelParams.length
  hmc_kind : (umw.mcKey = Ix.Kernel.eqReflName ∧ umw.rnf = 0 ∧
      env.find? Ix.Kernel.eqName = some Ix.Kernel.eqA ∧
      env.find? Ix.Kernel.eqReflName = some Ix.Kernel.eqReflA) ∨
    ∃ cidx, Nonempty (NativeCtorWitness t E env umw.mcKey mcIndKey cidx)
  hMCI_sort : StripPisZetaSort (cnp + ini) 0 (Core.posOf cvMCI.levelParams cvMCI.type) sortL
  hsort_cases : ((∀ φ, (substLevel sortL umw.mcLvls).eval φ > 0) ∧ ∀ bm ∈ umw.mbs, bm.2.pw = .never) ∨
    ((∀ φ, (substLevel sortL umw.mcLvls).eval φ = 0) ∧ ∀ bm ∈ umw.mbs, bm.2.pw = .ifAllZero [])
  hfindAuxC : env.find? auxCtorKey = some (.ctorInfo cvAuxC nP umw.rnf)
  hAuxC_P : (Core.posOf cvAuxC.levelParams cvAuxC.type).stripPis nP = some (bsP, remP)
  hAuxC_F : remP.stripPis umw.rnf = some (bsF, remF)
  hargWits : ∀ l (hl : l < umw.rnf),
    UnpackRebuildArgWitness auxKey auxRecKey nP bnl anc umw.rnf (umw.rargs.length - umw.rnf)
      (umw.rargs.drop umw.rnf) l (umw.margs.drop cnp |>.getD l default)
      (bsF.map Prod.fst |>.getD l default)

/-- Extract the single `UnpackRule` from one `UnpackMinorWitness`. -/
noncomputable def unpackRuleOf {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {env : Env .anon}
    {auxKey auxRecKey auxCtorKey : KKey} {auxRecLps : List LevelParam}
    {nP bnl anc k : Nat} {minorK : KExpr} {rl : RecRule .anon}
    (umw : UnpackMinorWitness t E env auxKey auxRecKey auxRecLps auxCtorKey nP bnl anc k minorK rl) :
    Ix.Kernel.Term.UnpackRule :=
  open Classical in
  if _ : umw.mcKey = auxCtorKey then
    .passthrough
  else if hreb : Nonempty (UnpackRebuildMatch umw) then
    let rm := Classical.choice hreb
    let nIh := umw.rargs.length - umw.rnf
    if _ : ∀ φ, (substLevel rm.sortL umw.mcLvls).eval φ > 0 then
      if hnat : ∃ cidx, Nonempty (NativeCtorWitness t E env umw.mcKey rm.mcIndKey cidx) then
        let recFlags : List Bool := (List.range umw.rnf).map fun l =>
          decide (∃ bv < nIh, (umw.margs.drop rm.cnp).getD l default = .bvar bv)
        .rebuild (.sumMk (Classical.choose hnat)) recFlags
      else .rebuild .propMk []
    else .rebuild .propMk []
  else .passthrough

/-- Construct the `UnpackSpec` for an unpack minor witness family. Depends only on the syntactic
witness `hminors`, completely independent of set-model valuations, parameters, or subjects. -/
noncomputable def unpackSpecOf {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {env : Env .anon}
    {auxKey auxRecKey : KKey} {auxRecLps : List LevelParam} {arules : List (RecRule .anon)}
    {auxCtorKeyAt : Nat → KKey} {nP bnl anc : Nat} {uarArgs : List KExpr}
    (hminors : ∀ k (hk : k < anc),
      ∃ rl, arules[k]? = some rl ∧
        Nonempty (UnpackMinorWitness t E env auxKey auxRecKey auxRecLps (auxCtorKeyAt k) nP bnl anc k
          (uarArgs.drop (nP + 1) |>.getD k default) rl)) :
    Ix.Kernel.Term.UnpackSpec :=
  (List.range anc).map fun k =>
    if hk : k < anc then
      unpackRuleOf (Classical.choice (Classical.choose_spec (hminors k hk)).2)
    else .passthrough

/-- Bundled witness matching a `ProjMinorWitness` body `mbody` to its unpack definitions and
minor witnesses (allows a single `Classical.choice` in `minorUnpackSpec`). -/
structure UnpackSpecMatch (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (env : Env .anon)
    (auxKey auxRecKey : KKey) (auxRecLps : List LevelParam)
    (arules : List (RecRule .anon)) (auxCtorKeyAt : Nat → KKey)
    (nP bnl anc : Nat) (mbody : KExpr) where
  uKey : KKey
  cvU : ConstantVal .anon
  uval : KExpr
  uHint : Ix.Kernel.ReducibilityHint
  uLvls : List KLevel
  uargs : List KExpr
  uaKey : KKey
  cvUA : ConstantVal .anon
  uaval : KExpr
  uaHint : Ix.Kernel.ReducibilityHint
  ubs : List (KExpr × BinderMeta)
  uaLvls : List KLevel
  uaArgs : List KExpr
  uabs : List (KExpr × BinderMeta)
  uarLvls : List KLevel
  uarArgs : List KExpr
  hmbody : mbody = Expr.mkAppN (.const uKey uLvls) uargs
  hfindU : env.find? uKey = some (.defnInfo cvU uval uHint)
  hu_strip : (Core.posOf cvU.levelParams uval).stripLams uargs.length =
    some (ubs, Expr.mkAppN (.const uaKey uaLvls) uaArgs)
  hfindUA : env.find? uaKey = some (.defnInfo cvUA uaval uaHint)
  hua_strip : (Core.posOf cvUA.levelParams uaval).stripLams nP =
    some (uabs, Expr.mkAppN (.const auxRecKey uarLvls) uarArgs)
  hminors : ∀ k (hk : k < anc),
    ∃ rl, arules[k]? = some rl ∧
      Nonempty (UnpackMinorWitness t E env auxKey auxRecKey auxRecLps (auxCtorKeyAt k) nP bnl anc k
        (uarArgs.drop (nP + 1) |>.getD k default) rl)

/-- The `UnpackSpec` for a `ProjMinorWitness`: empty `[]` for `.bvar`, `unpackSpecOf` for
`.unpack`. -/
noncomputable def minorUnpackSpec {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {env : Env .anon}
    {auxKey auxRecKey : KKey} {auxRecLps : List LevelParam}
    {arules : List (RecRule .anon)} {auxCtorKeyAt : Nat → KKey} {sbmPw : Ix.Kernel.PropWhen}
    {nP bnl anc nF nIhJ fidx : Nat} {mbody : KExpr}
    (_hm : ProjMinorWitness t E env auxKey auxRecKey auxRecLps arules auxCtorKeyAt sbmPw nP bnl anc nF
      nIhJ fidx mbody) : Ix.Kernel.Term.UnpackSpec :=
  open Classical in
  if h : Nonempty (UnpackSpecMatch t E env auxKey auxRecKey auxRecLps arules auxCtorKeyAt nP bnl anc mbody) then
    unpackSpecOf (Classical.choice h).hminors
  else []

private theorem expr_mkAppN_const_inj {k1 k2 : KKey} {u1 u2 : List KLevel} :
    ∀ {a1 a2 : List KExpr},
      Expr.mkAppN (.const k1 u1) a1 = Expr.mkAppN (.const k2 u2) a2 →
      k1 = k2 ∧ u1 = u2 ∧ a1 = a2 := by
  intro a1
  induction a1 using List.reverseRecOn with
  | nil =>
    intro a2 h
    cases a2 using List.reverseRecOn with
    | nil =>
      simp only [Expr.mkAppN] at h
      obtain ⟨rfl, rfl⟩ := Expr.const.inj h
      exact ⟨rfl, rfl, rfl⟩
    | append_singleton ys y =>
      simp [mkAppN_append, Expr.mkAppN] at h
  | append_singleton xs x ih =>
    intro a2 h
    cases a2 using List.reverseRecOn with
    | nil => simp [mkAppN_append, Expr.mkAppN] at h
    | append_singleton ys y =>
      simp only [mkAppN_append, Expr.mkAppN] at h
      obtain ⟨hpre, rfl⟩ := Expr.app.inj h
      obtain ⟨rfl, rfl, rfl⟩ := ih hpre
      exact ⟨rfl, rfl, rfl⟩

theorem minorUnpackSpec_bvar {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {env : Env .anon}
    {auxKey auxRecKey : KKey} {auxRecLps : List LevelParam}
    {arules : List (RecRule .anon)} {auxCtorKeyAt : Nat → KKey} {sbmPw : Ix.Kernel.PropWhen}
    {nP bnl anc nF nIhJ fidx i : Nat}
    (hm : ProjMinorWitness t E env auxKey auxRecKey auxRecLps arules auxCtorKeyAt sbmPw nP bnl anc nF
      nIhJ fidx (.bvar i)) :
    minorUnpackSpec hm = [] := by
  have hne : ¬ Nonempty (UnpackSpecMatch t E env auxKey auxRecKey auxRecLps arules auxCtorKeyAt nP bnl anc (.bvar i)) := by
    rintro ⟨m⟩
    have hmb := m.hmbody
    cases hu : m.uargs using List.reverseRecOn with
    | nil => rw [hu] at hmb; simp [Expr.mkAppN] at hmb
    | append_singleton _ _ => rw [hu] at hmb; simp [mkAppN_append, Expr.mkAppN] at hmb
  simp only [minorUnpackSpec, hne, ↓reduceDIte]

private theorem unpackSpecOf_eq_of_match {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {env : Env .anon}
    {auxKey auxRecKey : KKey} {auxRecLps : List LevelParam}
    {arules : List (RecRule .anon)} {auxCtorKeyAt : Nat → KKey}
    {nP bnl anc : Nat} {mbody : KExpr}
    (m : UnpackSpecMatch t E env auxKey auxRecKey auxRecLps arules auxCtorKeyAt nP bnl anc mbody)
    {uKey : KKey} {cvU : ConstantVal .anon} {uval : KExpr} {uHint : Ix.Kernel.ReducibilityHint}
    {uLvls : List KLevel} {uargs : List KExpr}
    {uaKey : KKey} {cvUA : ConstantVal .anon} {uaval : KExpr} {uaHint : Ix.Kernel.ReducibilityHint}
    {ubs : List (KExpr × BinderMeta)} {uaLvls : List KLevel} {uaArgs : List KExpr}
    {uabs : List (KExpr × BinderMeta)} {uarLvls : List KLevel} {uarArgs : List KExpr}
    (hmbody : mbody = Expr.mkAppN (.const uKey uLvls) uargs)
    (hfindU : env.find? uKey = some (.defnInfo cvU uval uHint))
    (hu_strip : (Core.posOf cvU.levelParams uval).stripLams uargs.length =
      some (ubs, Expr.mkAppN (.const uaKey uaLvls) uaArgs))
    (hfindUA : env.find? uaKey = some (.defnInfo cvUA uaval uaHint))
    (hua_strip : (Core.posOf cvUA.levelParams uaval).stripLams nP =
      some (uabs, Expr.mkAppN (.const auxRecKey uarLvls) uarArgs))
    (hminors : ∀ k (hk : k < anc),
      ∃ rl, arules[k]? = some rl ∧
        Nonempty (UnpackMinorWitness t E env auxKey auxRecKey auxRecLps (auxCtorKeyAt k) nP bnl anc k
          (uarArgs.drop (nP + 1) |>.getD k default) rl)) :
    unpackSpecOf m.hminors = unpackSpecOf hminors := by
  cases m with
  | mk uKey' cvU' uval' uHint' uLvls' uargs' uaKey' cvUA' uaval' uaHint' ubs' uaLvls' uaArgs'
      uabs' uarLvls' uarArgs' hmb' hfU' hu' hfUA' hua' hmin' =>
    obtain ⟨rfl, rfl, rfl⟩ := expr_mkAppN_const_inj (hmb'.symm.trans hmbody)
    obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.defnInfo.inj (Option.some.inj (hfU'.symm.trans hfindU))
    obtain ⟨-, hma1⟩ := Prod.mk.inj (Option.some.inj (hu'.symm.trans hu_strip))
    obtain ⟨rfl, rfl, rfl⟩ := expr_mkAppN_const_inj hma1
    obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.defnInfo.inj (Option.some.inj (hfUA'.symm.trans hfindUA))
    obtain ⟨-, hma2⟩ := Prod.mk.inj (Option.some.inj (hua'.symm.trans hua_strip))
    obtain ⟨-, rfl, rfl⟩ := expr_mkAppN_const_inj hma2
    rfl

theorem minorUnpackSpec_unpack {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {env : Env .anon}
    {auxKey auxRecKey : KKey} {auxRecLps : List LevelParam}
    {arules : List (RecRule .anon)} {auxCtorKeyAt : Nat → KKey} {sbmPw : Ix.Kernel.PropWhen}
    {nP bnl anc nF nIhJ fidx : Nat} {mbody : KExpr}
    (hm : ProjMinorWitness t E env auxKey auxRecKey auxRecLps arules auxCtorKeyAt sbmPw nP bnl anc nF
      nIhJ fidx mbody)
    {uKey : KKey} {cvU : ConstantVal .anon} {uval : KExpr} {uHint : Ix.Kernel.ReducibilityHint}
    {uLvls : List KLevel} {uargs : List KExpr}
    {uaKey : KKey} {cvUA : ConstantVal .anon} {uaval : KExpr} {uaHint : Ix.Kernel.ReducibilityHint}
    {ubs : List (KExpr × BinderMeta)} {uaLvls : List KLevel} {uaArgs : List KExpr}
    {uabs : List (KExpr × BinderMeta)} {uarLvls : List KLevel} {uarArgs : List KExpr}
    (hmbody : mbody = Expr.mkAppN (.const uKey uLvls) uargs)
    (hfindU : env.find? uKey = some (.defnInfo cvU uval uHint))
    (hu_strip : (Core.posOf cvU.levelParams uval).stripLams uargs.length =
      some (ubs, Expr.mkAppN (.const uaKey uaLvls) uaArgs))
    (hfindUA : env.find? uaKey = some (.defnInfo cvUA uaval uaHint))
    (hua_strip : (Core.posOf cvUA.levelParams uaval).stripLams nP =
      some (uabs, Expr.mkAppN (.const auxRecKey uarLvls) uarArgs))
    (hminors : ∀ k (hk : k < anc),
      ∃ rl, arules[k]? = some rl ∧
        Nonempty (UnpackMinorWitness t E env auxKey auxRecKey auxRecLps (auxCtorKeyAt k) nP bnl anc k
          (uarArgs.drop (nP + 1) |>.getD k default) rl)) :
    minorUnpackSpec hm = unpackSpecOf hminors := by
  have hex : Nonempty (UnpackSpecMatch t E env auxKey auxRecKey auxRecLps arules auxCtorKeyAt nP bnl anc mbody) :=
    ⟨⟨uKey, cvU, uval, uHint, uLvls, uargs, uaKey, cvUA, uaval, uaHint, ubs, uaLvls, uaArgs,
      uabs, uarLvls, uarArgs, hmbody, hfindU, hu_strip, hfindUA, hua_strip, hminors⟩⟩
  simp only [minorUnpackSpec, hex, ↓reduceDIte]
  exact unpackSpecOf_eq_of_match (Classical.choice hex) hmbody hfindU hu_strip hfindUA hua_strip hminors

/-! ### Helper: `nativeCtor_fold_pos`, `nativeCtor_fold_zero`, and `aux_elem_invert_unique` -/

/-- Any non-`Prop` native constructor `cKey` (`NativeCtorWitness` with index `cidx`) applied to an
`AppChainOk` argument list `args` of length `nP + nF` evaluates to
`inj cidx (mkTower (args.drop nP ++ [pt]))`. -/
theorem nativeCtor_fold_pos {V : Type u} [SetTheory V] {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Env .anon} {Reg : NativeFam .anon → Prop}
    (hreg : FamRegistryWith FormerOpenTraceAt t E env Reg)
    (mp : EnvModelM V .verified env)
    (hN : ∀ fam, Reg fam → NativeFamOk mp fam)
    {cKey iKey : KKey} {cidx : Nat}
    (cwit : NativeCtorWitness t E env cKey iKey cidx)
    {ψ : LevelParam → Nat} {ρ : Nat → V} {args : List V}
    (hsort_nz : ∀ fam, Reg fam → fam.p.cvT.name = iKey → fam.p.resSort.eval ψ ≠ 0)
    (hlen : args.length = cwit.nP + cwit.nF)
    (hApp : AppChainOk (interp V ρ (mp.base2.acval cKey ψ)) args) :
    args.foldl SetTheory.app (interp V ρ (mp.base2.acval cKey ψ)) =
      inj cidx (mkTower (args.drop cwit.nP ++ [pt])) := by
  obtain ⟨fam, j, cA, hregF, hfamName, hcA, hcName, hcidxEq⟩ :=
    hreg.completeCtor cwit.addr cwit.cm cwit.cp cwit.cv cwit.nP cwit.nF
      (show env.find? (Core.keyOf t cwit.addr) = _ by rw [cwit.hkey]; exact cwit.hfind)
      (show Ix.Kernel.reservedBasisNames.contains (Core.keyOf t cwit.addr) = false by rw [cwit.hkey]; exact cwit.hnotRes)
      cwit.hrec cwit.hinfo cwit.hnat
  obtain ⟨env₀, bsT, ppsAll, uAV, fssZ, idxF, dsF, esF, srcsF, ksF, fvsPF, xFvsF, xrestF,
    eissF, tssF, hAt⟩ := hN fam hregF
  have hread := hreg.fams fam hregF
  have hnameI : fam.p.cvT.name = iKey := hfamName.trans cwit.hindKey
  have hw : fam.p.resSort.eval ψ ≠ 0 := hsort_nz fam hregF hnameI
  have hcA_name : cA.1.name = cKey := hcName.trans cwit.hkey
  have hj_eq : j = cidx := hcidxEq.symm.trans cwit.hcidx
  have hfind_cA := (hread.stored.ctor j cA hcA).1
  rw [hcA_name, cwit.hfind] at hfind_cA
  obtain ⟨-, hnP_eq, hnF_eq⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hfind_cA)
  have hleaf := hAt.leafC j cA hcA ψ
  rw [hcA_name] at hleaf
  have hokC : WellDenotedV V ρ (mp.base2.acval cKey ψ) :=
    ⟨mp.base2.acval_wellDenoted cKey ψ ρ, mp.acval_validV cKey ψ ρ⟩
  rw [hleaf] at hApp hokC ⊢
  have hds_len : (dsF j ψ).length = cwit.nP + cwit.nF := by
    rw [(hAt.ctor j cA hcA).len ψ, hnP_eq, hnF_eq]
  have hnz_lams : ∀ p ∈ ((dsF j ψ).map fun d => (fam.p.resSort.eval ψ, d.2.2)), p.1 ≠ 0 := by
    intro p hp; obtain ⟨d, -, rfl⟩ := List.mem_map.mp hp; exact hw
  let bodyC := sumInjAtAV (fam.p.resSort.eval ψ)
    (Ix.Kernel.Semantics.uChains (Ix.Kernel.Model.fssOfR fam.p.nP
      (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ fam.ctorsA 0)))
    (((dsF j ψ).drop fam.p.nP).map (·.2.2)).length
    (Ix.Kernel.Semantics.numeralAV j)
    (Ix.Kernel.Semantics.mkTowerGoU (fam.p.resSort.eval ψ) (((dsF j ψ).drop fam.p.nP).map (·.2.2))
      (Ix.Kernel.Semantics.idxEqAV []))
  have hokC' : WellDenotedV V ρ (mkLamsAV ((dsF j ψ).map fun d => (fam.p.resSort.eval ψ, d.2.2)) bodyC) := by
    rwa [sumMkAV, mkLamsC_eq_mkLamsAV] at hokC
  have hApp' : AppChainOk (interp V ρ (mkLamsAV ((dsF j ψ).map fun d => (fam.p.resSort.eval ψ, d.2.2)) bodyC)) args := by
    rwa [sumMkAV, mkLamsC_eq_mkLamsAV] at hApp
  have hsp_all := (mkLamsAV_appChainOk_pos
    ((dsF j ψ).map fun d => (fam.p.resSort.eval ψ, d.2.2)) bodyC args ρ hnz_lams
    (by simp [hds_len, hlen]) hokC' hApp').2.1
  have hmap_eq : (((dsF j ψ).map fun d => (fam.p.resSort.eval ψ, d.2.2)).map Prod.snd) =
      ((dsF j ψ).take fam.p.nP).map (·.2.2) ++ ((dsF j ψ).drop fam.p.nP).map (·.2.2) := by
    rw [List.map_map, ← List.map_append, List.take_append_drop]; rfl
  rw [hmap_eq, ← List.take_append_drop cwit.nP args] at hsp_all
  have hlen_take_d : (((dsF j ψ).take fam.p.nP).map (·.2.2)).length = (args.take cwit.nP).length := by
    rw [List.length_map, List.length_take, List.length_take, hds_len, hnP_eq, hlen]; omega
  obtain ⟨hsp1, hsp2⟩ := (spineFit_append_iff hlen_take_d).mp hsp_all
  have hsat_p : Sat V (((ppsAll ψ).take fam.p.nP).map (·.2.2)).reverse
      (consList (args.take cwit.nP) ρ) := by
    rw [hAt.paramsIff j cA hcA ψ]
    have hs := Ix.Kernel.Model.sat_of_spineFit (Δ₀ := []) (Ix.Kernel.Semantics.Sat_nil V ρ) hsp1
    simpa using hs
  have hfr := hAt.frames ψ (consList (args.take cwit.nP) ρ) hsat_p
  have hokFss : SumFieldsOkB (fam.p.resSort.eval ψ) (consList (args.take cwit.nP) ρ)
      (Ix.Kernel.Model.fssOfR fam.p.nP
        (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ fam.ctorsA 0)) := by
    intro Fs hFs
    obtain ⟨j', hjlt, rfl⟩ := List.mem_iff_getElem.mp hFs
    have hjlt' : j' < fam.ctorsA.length := by
      simpa [Ix.Kernel.Model.fssOfR, Ix.Kernel.Model.fixCtorDataList_length] using hjlt
    have hget : (Ix.Kernel.Model.fssOfR fam.p.nP
        (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ fam.ctorsA 0)).getD j' [] =
        (Ix.Kernel.Model.fssOfR fam.p.nP
          (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ fam.ctorsA 0))[j'] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjlt]
    rw [← hget]
    exact (hfr.2.2.1 j' hjlt').1
  have hokU := Ix.Kernel.Semantics.SumFieldsOkB_uChains hokFss
  have hjU : (Ix.Kernel.Semantics.uChains (Ix.Kernel.Model.fssOfR fam.p.nP
      (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ fam.ctorsA 0)))[j]? =
      some (((dsF j ψ).drop fam.p.nP).map (·.2.2) ++ [Ix.Kernel.Semantics.idxEqAV []]) := by
    rw [Ix.Kernel.Semantics.uChains_getElem?, Ix.Kernel.Model.fssOfR_getElem?,
      Ix.Kernel.Model.fixCtorDataList_getElem? dsF esF ksF eissF tssF ψ fam.ctorsA 0 j, hcA]
    simp
  have hfold := sumMkAV_fold hw hsp1 hsp2 hokU hjU
  rw [List.take_append_drop, List.take_append_drop] at hfold
  exact hfold.trans (by rw [hj_eq, hnP_eq])

/-- Any `Prop` native constructor (`fam.p.resSort.eval ψ = 0`) applied to any arguments evaluates
to `pt`. -/
theorem nativeCtor_fold_zero {V : Type u} [SetTheory V] {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Env .anon} {Reg : NativeFam .anon → Prop}
    (hreg : FamRegistryWith FormerOpenTraceAt t E env Reg)
    (mp : EnvModelM V .verified env)
    (hN : ∀ fam, Reg fam → NativeFamOk mp fam)
    {cKey iKey : KKey} {cidx : Nat}
    (cwit : NativeCtorWitness t E env cKey iKey cidx)
    {ψ : LevelParam → Nat} {ρ : Nat → V} (args : List V)
    (hsort_zero : ∀ fam, Reg fam → fam.p.cvT.name = iKey → fam.p.resSort.eval ψ = 0) :
    args.foldl SetTheory.app (interp V ρ (mp.base2.acval cKey ψ)) = (pt : V) := by
  obtain ⟨fam, j, cA, hregF, hfamName, hcA, hcName, -⟩ :=
    hreg.completeCtor cwit.addr cwit.cm cwit.cp cwit.cv cwit.nP cwit.nF
      (show env.find? (Core.keyOf t cwit.addr) = _ by rw [cwit.hkey]; exact cwit.hfind)
      (show Ix.Kernel.reservedBasisNames.contains (Core.keyOf t cwit.addr) = false by rw [cwit.hkey]; exact cwit.hnotRes)
      cwit.hrec cwit.hinfo cwit.hnat
  obtain ⟨env₀, bsT, ppsAll, uAV, fssZ, idxF, dsF, esF, srcsF, ksF, fvsPF, xFvsF, xrestF,
    eissF, tssF, hAt⟩ := hN fam hregF
  have hnameI : fam.p.cvT.name = iKey := hfamName.trans cwit.hindKey
  have hw0 : fam.p.resSort.eval ψ = 0 := hsort_zero fam hregF hnameI
  have hleaf := hAt.leafC j cA hcA ψ
  rw [hcName.trans cwit.hkey, hw0] at hleaf
  rw [hleaf, sumMkAV_zero]
  exact foldl_app_pt args

set_option maxHeartbeats 1600000 in
/-- In a non-Prop indexed auxiliary family `aux` with tag family `tag` (`w_tag > 0`), any element
`x ∈ˢ app μ_aux (tupW u_aux [tagC vs])` has constructor index `jIdx` (the unique constructor
tagged with `tagCidx`), field vector `fs` of length `nF`, and `SpineFit` against `dsF jIdx`. -/
theorem aux_elem_invert_unique {V : Type u} [SetTheory V] {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Env .anon} {Reg : NativeFam .anon → Prop}
    (ht : t.check = .ok ())
    (hreg : FamRegistryWith FormerOpenTraceAt t E env Reg)
    (mp : EnvModelM V .verified env)
    (hN : ∀ fam, Reg fam → NativeFamOk mp fam)
    {auxKey tagKey tagCKey : KKey} {tagCidx nP bnl anc nF jIdx : Nat}
    (tagCWit : NativeCtorWitness t E env tagCKey tagKey tagCidx)
    (htagC_lvls : tagCWit.cv.levelParams.length = bnl)
    (htagC_nP : tagCWit.nP = nP)
    (htagC_nF : tagCWit.nF = 0)
    (tagIndWit : NativeIndWitness t E env tagKey)
    (htagInd_lvls : tagIndWit.cv.levelParams.length = bnl)
    (htagInd_idx : tagIndWit.ip.idx.toNat = 0)
    (htagInd_sort : ∃ bs u, (Core.posOf tagIndWit.cv.levelParams tagIndWit.cv.type).stripPis nP =
      some (bs, .sort u) ∧ ∀ φ, (substLevel u ((List.range bnl).map .param)).eval φ > 0)
    (auxIndWit : NativeIndWitness t E env auxKey)
    (hauxInd_lvls : auxIndWit.cv.levelParams.length = bnl)
    (hauxInd_idx : auxIndWit.ip.idx.toNat = 0)
    (hauxInd_rec : ∃ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (ind : Ixon.Inductive),
      Ix.Cert.recordAt E auxIndWit.ip.block = some cb ∧ cb.info = .muts ms ∧
      ms[0]? = some (.indc ind) ∧ ind.params.toNat = nP ∧ ind.indices.toNat = 1 ∧
      ind.ctors.size = anc)
    (hauxInd_sort : ∃ bs u, (Core.posOf auxIndWit.cv.levelParams auxIndWit.cv.type).stripPis (nP + 1) =
      some (bs, .sort u) ∧ ∀ φ, (substLevel u ((List.range bnl).map .param)).eval φ > 0)
    (hjIdx_lt : jIdx < anc)
    (hauxCtors : ∀ k < anc, ∃ w : AuxCtorTagWitness t E env auxKey tagKey nP bnl k,
      w.ctorKey = Core.keyOf t (Core.cprjAddr auxIndWit.ip.block 0 k) ∧
      (k = jIdx → w.ktcCidx = tagCidx ∧ w.knf = nF) ∧
      (k ≠ jIdx → w.ktcCidx ≠ tagCidx))
    -- Registered `famAux`
    {famAux : NativeFam .anon} {env₀ : Env .anon} {bsT : List (KExpr × BinderMeta)}
    {ppsAll : (LevelParam → Nat) → List (Nat × Nat × AnnotTerm)}
    {uAV : (LevelParam → Nat) → Nat} {fssZ : (LevelParam → Nat) → List (List AnnotTerm)}
    {idxF : Nat → List KExpr}
    {dsF : Nat → (LevelParam → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (LevelParam → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
    {ksF : Nat → List Ix.Kernel.RecFieldKind} {fvsPF xFvsF : Nat → List KExpr}
    {xrestF : Nat → KExpr}
    {eissF : Nat → (LevelParam → Nat) → List (List AnnotTerm)}
    {tssF : Nat → (LevelParam → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (hregAux : Reg famAux) (hnameAux : famAux.p.cvT.name = auxKey)
    (hAtAux : NativeFamAt mp famAux.p famAux.cvS famAux.cvTa famAux.ctorsA env₀ bsT ppsAll
      uAV fssZ idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF)
    (ψ_P : LevelParam → Nat) (ρ : Nat → V) (vs : List V) (x : V)
    (hvs_len : vs.length = nP)
    (hApp_tagC : AppChainOk (interp V ρ (mp.base2.acval tagCKey ψ_P)) vs)
    (hsp_p : SpineFit ρ (((ppsAll ψ_P).take famAux.p.nP).map (·.2.2)) vs)
    (hsp_tag : SpineFit (consList vs ρ) (((ppsAll ψ_P).drop famAux.p.nP).map (·.2.2))
      [vs.foldl SetTheory.app (interp V ρ (mp.base2.acval tagCKey ψ_P))])
    (hx_mem : x ∈ˢ SetTheory.app (fixFamI (uAV ψ_P) (famAux.p.resSort.eval ψ_P) (consList vs ρ)
      (((ppsAll ψ_P).drop famAux.p.nP).map (·.2.2)) 1
      (Ix.Kernel.Model.rssOfK ksF famAux.ctorsA.length)
      (Ix.Kernel.Model.tlssOfR (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0))
      (Ix.Kernel.Model.eissOfR (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0))
      (fssZ ψ_P)
      (Ix.Kernel.Model.essOfR (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0)))
      (tupW (uAV ψ_P) [vs.foldl SetTheory.app (interp V ρ (mp.base2.acval tagCKey ψ_P))])) :
    ∃ fs : List V,
      x = inj jIdx (mkTower (fs ++ [pt])) ∧
      fs.length = nF ∧
      SpineFit ρ ((dsF jIdx ψ_P).map (·.2.2)) (vs ++ fs) := by
  -- 1. Establish `famAux` metadata & `w_aux ≠ 0`
  have hreadAux := hreg.fams famAux hregAux
  have hreadAtAux := hreadAux.readAt ht (hnameAux.trans auxIndWit.hkey.symm) auxIndWit.hrec auxIndWit.hinfo
  obtain ⟨-, -, cbA, msA, indA, hcbA, hmsA, hindA, hnPA, hnIdxA, hlenA, hctorNameA⟩ := hreadAtAux
  have ⟨cb', ms', ind', hcb', hms', hind', hnP', hnIdx', hanc'⟩ := hauxInd_rec
  have hcb_eq : cbA = cb' := Option.some.inj (hcbA.symm.trans hcb')
  subst hcb_eq
  have hms_eq : msA = ms' := Ixon.ConstantInfo.muts.inj (hmsA.symm.trans hms')
  subst hms_eq
  rw [hauxInd_idx] at hindA hctorNameA
  have hind_eq : indA = ind' := Ixon.MutConst.indc.inj (Option.some.inj (hindA.symm.trans hind'))
  subst hind_eq
  have hfam_nP : famAux.p.nP = nP := hnPA.trans hnP'
  have hfam_nIdx : famAux.p.nIdx = 1 := hnIdxA.trans hnIdx'
  have hfam_ctors_len : famAux.ctorsA.length = anc := hlenA.trans hanc'
  have hIds_len : (((ppsAll ψ_P).drop famAux.p.nP).map (·.2.2)).length = 1 := by
    have := hAtAux.former.len ψ_P
    rw [List.length_map, List.length_drop, this, hfam_nIdx]; omega
  -- Helper: any `fam` registered at `tagKey` has `resSort.eval φ ≠ 0` for ALL `φ`!
  have htag_sort_nz_all : ∀ (famT : NativeFam .anon), Reg famT → famT.p.cvT.name = tagKey →
      ∀ φ : LevelParam → Nat, famT.p.resSort.eval φ ≠ 0 := by
    intro famT hregT hnameT φ
    have hreadT := hreg.fams famT hregT
    obtain ⟨bsS, uS, hstS, huS⟩ := htagInd_sort
    have hcvS_eq : famT.cvS = tagIndWit.cv := famRead_cvS_eq hreadT hnameT tagIndWit.hfind
    rw [← hcvS_eq] at hstS
    obtain ⟨-, hlv⟩ := famRead_resSort_of_stripPisZetaSort mp.base2.wf hreadT
      (stripPis_to_stripPisZetaSort hstS)
    have h1 := huS φ
    rw [eval_substLevel_eq_substFn (n := bnl) (by simp) φ uS, substFn_range_param] at h1
    rw [← hlv φ]; omega
  have hw_aux : famAux.p.resSort.eval ψ_P ≠ 0 := by
    obtain ⟨bsS, uS, hstS, huS⟩ := hauxInd_sort
    have hcvS_eq : famAux.cvS = auxIndWit.cv := famRead_cvS_eq hreadAux hnameAux auxIndWit.hfind
    rw [← hcvS_eq] at hstS
    obtain ⟨-, hlv⟩ := famRead_resSort_of_stripPisZetaSort mp.base2.wf hreadAux
      (stripPis_to_stripPisZetaSort hstS)
    have h1 := huS ψ_P
    rw [eval_substLevel_eq_substFn (n := bnl) (by simp) ψ_P uS, substFn_range_param] at h1
    rw [← hlv ψ_P]; omega
  -- 2. Unfold `fixFamI_app_eq` and `fixStepI_elim` on `hx_mem`!
  have hsat_p : Sat V (((ppsAll ψ_P).take famAux.p.nP).map (·.2.2)).reverse
      (consList vs ρ) := by
    have hs := Ix.Kernel.Model.sat_of_spineFit (Δ₀ := []) (Ix.Kernel.Semantics.Sat_nil V ρ) hsp_p
    simpa using hs
  have hfr := hAtAux.frames ψ_P (consList vs ρ) hsat_p
  let tagVal := vs.foldl SetTheory.app (interp V ρ (mp.base2.acval tagCKey ψ_P))
  have ht_mem : tupW (uAV ψ_P) [tagVal] ∈ˢ Ix.Kernel.Semantics.idxSet (uAV ψ_P) (consList vs ρ)
      (((ppsAll ψ_P).drop famAux.p.nP).map (·.2.2)) :=
    Ix.Kernel.Semantics.tupW_mem hsp_tag
  rw [← hIds_len, ← fixFamI_app_eq hfr.1 ht_mem] at hx_mem
  obtain ⟨k, fs, hx_eq, hk_lt, hfs_len, hsp_XI, heqAll⟩ := fixStepI_elim hw_aux hx_mem
  have hlenZ : (fssZ ψ_P).length = anc := by
    have := hfr.2.1.1; simp [Ix.Kernel.Model.fssOfR, Ix.Kernel.Model.fixCtorDataList_length, hfam_ctors_len] at this
    exact this
  have hk_anc : k < anc := by omega
  obtain ⟨cAk, hcAk⟩ : ∃ cAk, famAux.ctorsA[k]? = some cAk := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  -- `fs` fits `dsF k ψ_P`'s fields via `spineFit_real_of_XI`
  have hsp_fields : SpineFit (consList vs ρ) (((dsF k ψ_P).drop famAux.p.nP).map (·.2.2)) fs := by
    have hreal_k := hfr.2.1.2.2.2.2 k (by simp [Ix.Kernel.Model.fssOfR, Ix.Kernel.Model.fixCtorDataList_length]; omega)
    have hgetF : (Ix.Kernel.Model.fssOfR famAux.p.nP
        (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0)).getD k [] =
        ((dsF k ψ_P).drop famAux.p.nP).map (·.2.2) := by
      rw [List.getD_eq_getElem?_getD, Ix.Kernel.Model.fssOfR_getElem?,
        Ix.Kernel.Model.fixCtorDataList_getElem? dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0 k, hcAk]
      simp
    rw [hgetF, hfam_nIdx, ← hIds_len] at hreal_k
    have hfixMem := Ix.Kernel.Semantics.fixFamI_mem (V := V) (uAV ψ_P) (famAux.p.resSort.eval ψ_P)
      (consList vs ρ) (((ppsAll ψ_P).drop famAux.p.nP).map (·.2.2))
      (Ix.Kernel.Model.rssOfK ksF famAux.ctorsA.length)
      (Ix.Kernel.Model.tlssOfR (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0))
      (Ix.Kernel.Model.eissOfR (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0))
      (fssZ ψ_P)
      (Ix.Kernel.Model.essOfR (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0))
    exact spineFit_real_of_XI hfr.1.hI (fun _ _ _ h => h) _ _ 0 [] fs rfl hreal_k
      (hfr.1.hfit _ hfixMem _ ht_mem k hk_lt) hsp_XI
  -- 3. Prove `k = jIdx` by comparing `sfst tagVal` via `nativeCtor_fold_pos`!
  obtain ⟨w_k, hw_k_name, hw_k_eq, hw_k_ne⟩ := hauxCtors k hk_anc
  have heget : (Ix.Kernel.Model.essOfR
      (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0)).getD k [] =
      esF k ψ_P := by
    rw [List.getD_eq_getElem?_getD, Ix.Kernel.Model.essOfR_getElem?,
      Ix.Kernel.Model.fixCtorDataList_getElem? dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0 k, hcAk]
    simp
  have hEs_k_len : ((Ix.Kernel.Model.essOfR
      (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0)).getD k []).length =
      (((ppsAll ψ_P).drop famAux.p.nP).map (·.2.2)).length := by
    rw [heget, (hAtAux.ctor k cAk hcAk).lenE ψ_P, hfam_nIdx, hIds_len]
  have htag_eq_idx := idxValsAt_of_eqsXI hfr.1.hI hsp_tag hEs_k_len (hfs_len ▸ heqAll)
  rw [heget] at htag_eq_idx
  -- 3a. `sfst tagVal = vnat tagCidx` directly from `nativeCtor_fold_pos` on `tagCWit`!
  have htag_val_eq : tagVal = inj tagCidx (mkTower (vs.drop tagCWit.nP ++ [pt])) :=
    nativeCtor_fold_pos hreg mp hN tagCWit
      (fun famT hregT hnameT => htag_sort_nz_all famT hregT hnameT ψ_P)
      (by omega) hApp_tagC
  have htag_sfst : sfst tagVal = vnat tagCidx := by
    rw [htag_val_eq, inj, sfst_spair]
  -- 3b. `sfst tagVal = vnat w_k.ktcCidx` from `nativeCtor_fold_pos` on `w_k.hktc`!
  have hk_sfst : sfst tagVal = vnat w_k.ktcCidx := by
    -- Identify `w_k.cv = cAk.1` and `w_k.knf = cAk.2`
    have hname_k : cAk.1.name = w_k.ctorKey := (hctorNameA k cAk hcAk).trans hw_k_name.symm
    have hfc := (hreadAux.stored.ctor k cAk hcAk).1
    rw [hname_k, w_k.hfind] at hfc
    obtain ⟨hcv_eq, -, hknf_eq⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hfc)
    -- `cAk.1.type` has `stripPis (nP + cAk.2)` via `hAtAux.ctor k cAk hcAk`
    have hctor_k := hAtAux.ctor k cAk hcAk
    have hcv_lps : cAk.1.levelParams = List.range bnl := by
      rw [hAtAux.lpsA cAk (List.mem_of_getElem? hcAk)]
      exact famRead_lps_range hreadAux (by rw [← hreadAux.lps, famRead_cvS_eq hreadAux hnameAux auxIndWit.hfind]; exact hauxInd_lvls)
    have hpos_k : Core.posOf w_k.cv.levelParams w_k.cv.type = cAk.1.type := by
      rw [hcv_eq, hcv_lps]
      have hwf_c := mp.base2.wf _ (Ix.Kernel.Semantics.Env.find?_mem (hreadAux.stored.ctor k cAk hcAk).1)
      exact posOf_range_eq bnl cAk.1.type (by rw [← hcv_lps]; exact hwf_c.2.1)
    -- Compare `w_k.hstrip` with `cAk.1.type.stripPis (nP + cAk.2)`!
    have hstrip_k := hctor_k.resid
    rw [hfam_nP, ← hknf_eq] at hstrip_k
    obtain ⟨bsC_k, esC_k, hstC_k, -⟩ := hstrip_k
    have hwk_strip : StripPisZeta (nP + w_k.knf) 0 cAk.1.type w_k.kres := by
      rw [← hpos_k]; exact w_k.hstrip
    have hkres_eq : w_k.kres = openDummiesP (nP + w_k.knf) 0 0 _ :=
      stripPisZeta_eq_of_stripPis hstC_k hwk_strip
    -- `denoteMeta` of `cAk.1.type` strips `nP + w_k.knf` Pis to `ctorBodyAVI`!
    obtain ⟨ds_k, bodyA_k, hmk_eq, hds_k_len, -, hbodyA_den⟩ :=
      denoteMeta_stripPis (nP + w_k.knf) 0 hstC_k (hctor_k.read ψ_P)
    -- Equate `bodyA_k` with `ctorBodyAVI mp.base2 famAux.p.cvT.name famAux.p.nP cAk.2 ψ_P (esF k ψ_P)`!
    have hbody_eq : bodyA_k = ctorBodyAVI mp.base2 famAux.p.cvT.name famAux.p.nP cAk.2 ψ_P (esF k ψ_P) := by
      have hgo : ∀ (l1 l2 : List (Nat × Nat × AnnotTerm)) (b1 b2 : AnnotTerm),
          l1.length = l2.length → mkPisAV l1 b1 = mkPisAV l2 b2 → b1 = b2 := by
        intro l1
        induction l1 with
        | nil => intro l2 b1 b2 hlen hmk; cases l2 with | nil => exact hmk | cons _ _ => simp at hlen
        | cons _ l1 ih =>
          intro l2 b1 b2 hlen hmk
          cases l2 with
          | nil => simp at hlen
          | cons _ l2 =>
            simp only [mkPisAV] at hmk
            exact ih l2 b1 b2 (by simpa using hlen) (AnnotTerm.pi.inj hmk).2.2.2
      exact hgo ds_k (dsF k ψ_P) bodyA_k _ (by rw [hds_k_len, hctor_k.len ψ_P, hfam_nP, hknf_eq]) hmk_eq.symm
    rw [← hkres_eq, w_k.hkres, hbody_eq] at hbodyA_den
    obtain ⟨faK, kargsA, -, hspK, hmkK_eq⟩ := denoteMeta_mkAppN_inv hbodyA_den
    -- Extract `(esF k ψ_P)[0]` = `kargsA[nP]`!
    have hkargsA_len : kargsA.length = nP + 1 := by
      have := denoteMetaSpine_length_eq hspK; rw [w_k.hkargs_len] at this; exact this.symm
    have hpb_len : (Ix.Kernel.Model.paramBvarsAt famAux.p.nP (famAux.p.nP + cAk.2)).length = nP := by
      simp [Ix.Kernel.Model.paramBvarsAt, hfam_nP]
    have hes0_eq : (esF k ψ_P).getD 0 default = kargsA[nP]'(by omega) := by
      -- Compare `mkAppN faK kargsA = mkAppN (acval auxKey ψ_P) (paramBvarsAt nP (nP + cAk.2) ++ esF k ψ_P)`
      have hgo : ∀ (a1 a2 : List AnnotTerm) (h1 h2 : AnnotTerm),
          a1.length = a2.length → AnnotTerm.mkAppN h1 a1 = AnnotTerm.mkAppN h2 a2 → a1 = a2 := by
        intro a1
        induction a1 using List.reverseRecOn with
        | nil =>
          intro a2 h1 h2 hlen _; cases a2 with | nil => rfl | cons _ _ => simp at hlen
        | append_singleton xs x ih =>
          intro a2 h1 h2 hlen hmk
          cases a2 using List.reverseRecOn with
          | nil => simp at hlen
          | append_singleton ys y =>
            simp only [AnnotTerm.mkAppN_append, AnnotTerm.mkAppN_cons, AnnotTerm.mkAppN_nil] at hmk
            obtain ⟨hpre, hlast⟩ := AnnotTerm.app.inj hmk
            rw [ih ys h1 h2 (by simpa using hlen) hpre, hlast]
      have hargs_eq := hgo kargsA (Ix.Kernel.Model.paramBvarsAt famAux.p.nP (famAux.p.nP + cAk.2) ++ esF k ψ_P)
        faK (mp.base2.acval famAux.p.cvT.name ψ_P)
        (by rw [hkargsA_len, List.length_append, hpb_len, hctor_k.lenE ψ_P, hfam_nIdx]) hmkK_eq.symm
      have h0 := congrArg (fun l => l.getD nP default) hargs_eq
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : nP < kargsA.length),
        Option.getD_some, List.getElem?_append_right (by rw [hpb_len]),
        hpb_len, Nat.sub_self] at h0
      exact h0.symm
    -- Read `denoteMeta` of `w_k.kargs[nP] = mkAppN (.const w_k.ktcKey w_k.ktLvls) w_k.ktArgs`!
    have hkargs_len := w_k.hkargs_len
    have hden_idx := denoteMetaSpine_getElem hspK (i := nP) (by omega)
    have hidx_kargs : w_k.kargs[nP]'(by omega) = Expr.mkAppN (.const w_k.ktcKey w_k.ktLvls) w_k.ktArgs := by
      have := w_k.hkidx
      rw [List.getElem?_eq_getElem (by omega : nP < w_k.kargs.length)] at this
      exact Option.some.inj this
    rw [hidx_kargs] at hden_idx
    obtain ⟨fktA, ktArgsA, hfktA, hspKt, hktA_eq⟩ := denoteMeta_mkAppN_inv hden_idx
    -- Identify `fktA = mp.base2.acval w_k.ktcKey ψ_ktc`
    simp only [denoteMeta, w_k.hktc.hfind, ConstantInfo.toConstantVal, w_k.hktLvls_len,
      ↓reduceIte, Option.some.injEq] at hfktA
    let ψ_ktc := Level.substFn ψ_P w_k.hktc.cv.levelParams w_k.ktLvls
    have hfktA_eq : fktA = mp.base2.acval w_k.ktcKey ψ_ktc := hfktA.symm
    -- Obtain `WellDenotedV` of `(esF k ψ_P).getD 0 default` at `consList fs (consList vs ρ)` from `hfr`!
    have hgetF : (Ix.Kernel.Model.fssOfR famAux.p.nP
        (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0)).getD k [] =
        ((dsF k ψ_P).drop famAux.p.nP).map (·.2.2) := by
      rw [List.getD_eq_getElem?_getD, Ix.Kernel.Model.fssOfR_getElem?,
        Ix.Kernel.Model.fixCtorDataList_getElem? dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0 k, hcAk]
      simp
    have hes0_mem : (esF k ψ_P).getD 0 default ∈ esF k ψ_P := by
      have hlen1 : (esF k ψ_P).length = 1 := by rw [hctor_k.lenE ψ_P, hfam_nIdx]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : 0 < (esF k ψ_P).length)]
      exact List.getElem_mem _
    have hwd_es0 : WellDenotedV V (consList fs (consList vs ρ)) ((esF k ψ_P).getD 0 default) := by
      refine ⟨?_, ?_⟩
      · have h1 := ((hfr.2.2.1 k (by omega)).2 fs (by rwa [hgetF])).1
        rw [heget] at h1
        exact h1 _ hes0_mem
      · have h2 := hfr.2.2.2.2.2 k (by omega) fs (by rwa [hgetF])
        rw [heget] at h2
        exact h2 _ hes0_mem
    rw [hes0_eq, hktA_eq, hfktA_eq] at hwd_es0
    obtain ⟨-, -, hApp_kt⟩ := appChainOk_of_wellDenotedV ktArgsA hwd_es0
    have hkt_fold := nativeCtor_fold_pos hreg mp hN w_k.hktc
      (fun famT hregT hnameT => htag_sort_nz_all famT hregT hnameT ψ_ktc)
      (by rw [List.length_map, ← denoteMetaSpine_length_eq hspKt, w_k.hktArgs_len])
      hApp_kt
    -- Connect `tagVal = interp (consList fs (consList vs ρ)) ((esF k ψ_P).getD 0 default)`!
    have htag_eq_es0 : tagVal = interp V (consList fs (consList vs ρ)) ((esF k ψ_P).getD 0 default) := by
      have h0 := congrArg (fun l => l[0]?) htag_eq_idx
      have hlen1 : (esF k ψ_P).length = 1 := by rw [hctor_k.lenE ψ_P, hfam_nIdx]
      cases he : esF k ψ_P with
      | nil => rw [he] at hlen1; cases hlen1
      | cons e0 er =>
        cases er with
        | cons _ _ => rw [he] at hlen1; simp at hlen1
        | nil =>
          rw [he] at h0
          simpa [idxValsAt] using h0.symm
    rw [htag_eq_es0, hes0_eq, hktA_eq, hfktA_eq, interp_mkAppN_foldl, hkt_fold, inj, sfst_spair]
  have hcidx_eq : w_k.ktcCidx = tagCidx := vnat_inj (hk_sfst.symm.trans htag_sfst)
  have hk_eq_jIdx : k = jIdx := by
    by_contra hne
    exact hw_k_ne hne hcidx_eq
  subst hk_eq_jIdx
  have hnf_eq : w_k.knf = nF := (hw_k_eq rfl).2
  have hcAk_nf : cAk.2 = nF := by
    have hf1 := (hreadAux.stored.ctor k cAk hcAk).1
    have hname_k : cAk.1.name = w_k.ctorKey := (hctorNameA k cAk hcAk).trans hw_k_name.symm
    rw [hname_k, w_k.hfind] at hf1
    have := (ConstantInfo.ctorInfo.inj (Option.some.inj hf1)).2.2
    exact this.symm.trans hnf_eq
  have hfs_len_nF : fs.length = nF := by
    have hlen_f : ((fssZ ψ_P).getD k []).length = cAk.2 := by
      have hlen1 := hfr.2.1.2.2.2.1 k (by simp [Ix.Kernel.Model.fssOfR, Ix.Kernel.Model.fixCtorDataList_length]; omega)
      have hgetF : (Ix.Kernel.Model.fssOfR famAux.p.nP
          (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0)).getD k [] =
          ((dsF k ψ_P).drop famAux.p.nP).map (·.2.2) := by
        rw [List.getD_eq_getElem?_getD, Ix.Kernel.Model.fssOfR_getElem?,
          Ix.Kernel.Model.fixCtorDataList_getElem? dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0 k, hcAk]
        simp
      rw [hgetF] at hlen1
      rw [hlen1, List.length_map, List.length_drop, (hAtAux.ctor k cAk hcAk).len ψ_P]
      omega
    omega
  have hsp_p_k : SpineFit ρ (((dsF k ψ_P).take famAux.p.nP).map (·.2.2)) vs := by
    have hsat_k : Sat V (((dsF k ψ_P).take famAux.p.nP).map (·.2.2)).reverse (consList vs ρ) :=
      (hAtAux.paramsIff k cAk hcAk ψ_P (consList vs ρ)).mp hsat_p
    have hlenP : (((dsF k ψ_P).take famAux.p.nP).map (·.2.2)).length = vs.length := by
      rw [List.length_map, List.length_take, (hAtAux.ctor k cAk hcAk).len ψ_P, hfam_nP, hvs_len]; omega
    exact spineFit_of_sat_consList hlenP hsat_k
  have hsp_all : SpineFit ρ ((dsF k ψ_P).map (·.2.2)) (vs ++ fs) := by
    have hsplit : (dsF k ψ_P).map (·.2.2) =
        ((dsF k ψ_P).take famAux.p.nP).map (·.2.2) ++ ((dsF k ψ_P).drop famAux.p.nP).map (·.2.2) := by
      rw [← List.map_append, List.take_append_drop]
    rw [hsplit]
    exact hsp_p_k.append hsp_fields
  exact ⟨fs, hx_eq, hfs_len_nF, hsp_all⟩

/-! ### Helper: `AppChainOk` from `mkPisAV` + `SpineFit`, and universe closure of `treeUnpackOpt` -/

/-- Applying a function inhabiting `mkPisAV ds body` to a `SpineFit` list `xs` satisfies
`AppChainOk`, lands in `interp (consList xs ρ) body`, and preserves `AnnotValid`. -/
theorem appChainOk_and_mem_of_mkPisAV_spineFit {V : Type u} [SetTheory V] :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (body : AnnotTerm) (xs : List V) (ρ : Nat → V) {F : V},
      ds.length = xs.length →
      AnnotValid V ρ (mkPisAV ds body) →
      F ∈ˢ interp V ρ (mkPisAV ds body) →
      SpineFit ρ (ds.map (·.2.2)) xs →
      AppChainOk F xs ∧
      xs.foldl SetTheory.app F ∈ˢ interp V (consList xs ρ) body ∧
      AnnotValid V (consList xs ρ) body
  | [], body, [], ρ, F, _, hval, hmem, _ => ⟨trivial, hmem, hval⟩
  | [], _, _ :: _, _, _, hlen, _, _, _ => by simp at hlen
  | _ :: _, _, [], _, _, hlen, _, _, _ => by simp at hlen
  | (u, v, A) :: ds, body, x :: xs, ρ, F, hlen, hval, hmem, hsp => by
    simp only [mkPisAV, AnnotValid_pi, interp_pi] at hval hmem
    simp only [List.map_cons, SpineFit] at hsp
    obtain ⟨hxA, hsp'⟩ := hsp
    have happ : SetTheory.app F x ∈ˢ interp V (cons x ρ) (mkPisAV ds body) :=
      app_mem_piR hmem hxA (fun hv0 y hy => hval.2.2 hv0 y hy)
    have hval' : AnnotValid V (cons x ρ) (mkPisAV ds body) := hval.2.1 x hxA
    obtain ⟨hApp', hmem', hval''⟩ :=
      appChainOk_and_mem_of_mkPisAV_spineFit ds body xs (cons x ρ) (by simpa using hlen) hval' happ hsp'
    refine ⟨⟨⟨v, interp V ρ A, fun y => interp V (cons y ρ) (mkPisAV ds body),
        hmem, hxA, fun hv0 y hy => hval.2.2 hv0 y hy⟩, hApp'⟩,
      ?_, ?_⟩
    · simpa [consList, List.foldl_cons] using hmem'
    · simpa [consList] using hval''

/-- Applying a function inhabiting `mkPisAV ds body` with all positive binder bits to an
`AppChainOk` list `xs` yields `SpineFit ρ (ds.map (·.2.2)) xs`. -/
theorem spineFit_of_mkPisAV_appChainOk_pos {V : Type u} [SetTheory V] :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (body : AnnotTerm) (xs : List V) (ρ : Nat → V) {F : V},
      (∀ d ∈ ds, d.2.1 ≠ 0) →
      ds.length = xs.length →
      F ∈ˢ interp V ρ (mkPisAV ds body) →
      AppChainOk F xs →
      SpineFit ρ (ds.map (·.2.2)) xs
  | [], _, [], _, _, _, _, _, _ => trivial
  | [], _, _ :: _, _, _, _, hl, _, _ => by simp at hl
  | _ :: _, _, [], _, _, _, hl, _, _ => by simp at hl
  | d :: ds, body, x :: xs, ρ, F, hpos, hl, hmem, hApp => by
    have hd_nz : d.2.1 ≠ 0 := hpos d List.mem_cons_self
    simp only [mkPisAV, interp_pi] at hmem
    obtain ⟨⟨v', A', B', hFpi', hxA', -⟩, hApp'⟩ := hApp
    have hv'_ne : v' ≠ 0 := fun hv'0 => by
      rw [hv'0] at hFpi'
      have hFpt := eq_pt_of_mem_piR_zero hFpi'
      rw [hFpt] at hmem
      exact not_pt_mem_piR_pos hd_nz hmem
    have hA_eq : interp V ρ d.2.2 = A' := piR_dom_unique hd_nz hv'_ne hmem hFpi'
    have hxA : x ∈ˢ interp V ρ d.2.2 := hA_eq ▸ hxA'
    have happ : SetTheory.app F x ∈ˢ interp V (cons x ρ) (mkPisAV ds body) := app_mem_piR_pos hd_nz hmem hxA
    exact ⟨hxA, spineFit_of_mkPisAV_appChainOk_pos ds body xs (cons x ρ)
      (fun d' hd' => hpos d' (List.mem_cons_of_mem _ hd')) (by simpa using hl) happ hApp'⟩

/-- `pt` lives in `univ W` for every `W ≠ 0`. -/
theorem pt_mem_univ {V : Type u} [SetTheory V] {W : Nat} (hW : W ≠ 0) :
    (pt : V) ∈ˢ (univ W : V) :=
  (univ_isTGUniverse (V := V) hW).pt_mem (empty_mem_univ W)

/-- `sfst` stays inside any nonempty Grothendieck universe `univ W` (`W ≠ 0`). -/
private theorem sfst_mem_univ {V : Type u} [SetTheory V] {W : Nat} (hW : W ≠ 0) {x : V}
    (hx : x ∈ˢ (univ W : V)) : sfst x ∈ˢ (univ W : V) := by
  unfold sfst
  split
  · rename_i h
    have hsp := Classical.choose_spec (Classical.choose_spec h)
    rw [hsp, ← spair_eq_kpair] at hx
    exact (Ix.Kernel.Model.spair_comp_mem hW hx).1
  · exact pt_mem_univ hW

/-- `ssnd` stays inside any nonempty Grothendieck universe `univ W` (`W ≠ 0`). -/
private theorem ssnd_mem_univ {V : Type u} [SetTheory V] {W : Nat} (hW : W ≠ 0) {x : V}
    (hx : x ∈ˢ (univ W : V)) : ssnd x ∈ˢ (univ W : V) := by
  unfold ssnd
  split
  · rename_i h
    have hsp := Classical.choose_spec (Classical.choose_spec h)
    rw [hsp, ← spair_eq_kpair] at hx
    exact (Ix.Kernel.Model.spair_comp_mem hW hx).2
  · exact pt_mem_univ hW

/-- `projS` stays inside any nonempty Grothendieck universe `univ W` (`W ≠ 0`). -/
theorem projS_mem_univ {V : Type u} [SetTheory V] {W : Nat} (hW : W ≠ 0) :
    ∀ (k : Nat) {x : V}, x ∈ˢ (univ W : V) → projS k x ∈ˢ (univ W : V)
  | 0, _, hx => sfst_mem_univ hW hx
  | k + 1, _, hx => projS_mem_univ hW k (ssnd_mem_univ hW hx)

theorem denoteMeta_forallE_some {acval : KKey → (LevelParam → Nat) → AnnotTerm}
    {env : Env .anon} {ψ : LevelParam → Nat} {d : Nat} {t b : KExpr} {bm : BinderMeta} {a : AnnotTerm}
    (h : denoteMeta acval env ψ d (.forallE t b bm) = some a) :
    ∃ ta ba, denoteMeta acval env ψ d t = some ta ∧
      denoteMeta acval env ψ (d + 1) (b.instantiate1 (.fvar d (.sort .zero)) 0) = some ba ∧
      AnnotTerm.pi 0 (pwBit ψ bm.pw) ta ba = a := by
  simp only [denoteMeta] at h
  cases ht : denoteMeta acval env ψ d t with
  | none => simp [ht] at h
  | some ta =>
    rw [ht] at h
    cases hb : denoteMeta acval env ψ (d + 1) (b.instantiate1 (.fvar d t) 0) with
    | none => simp [hb] at h
    | some ba =>
      rw [hb] at h
      have hirr : FvarTypeIrrel (b.instantiate1 (.fvar d t) 0) (b.instantiate1 (.fvar d (.sort .zero)) 0) :=
        (FvarTypeIrrel.refl b).instantiate1 (.fvar d t (.sort .zero)) 0
      rw [denoteMeta_fvarTypeIrrel hirr] at hb
      exact ⟨ta, ba, rfl, hb, Option.some.inj h⟩

/-- `rebuildCtor` stays inside `univ W` (`W ≠ 0`) when all field values lie in `univ W`. -/
private theorem rebuildCtor_mem_univ {V : Type u} [SetTheory V] {W : Nat} (hW : W ≠ 0)
    (kind : Ix.Kernel.Term.UnpackCtorKind) {args : List V}
    (hargs : ∀ a ∈ args, a ∈ˢ (univ W : V)) :
    Ix.Kernel.SetModel.rebuildCtor kind args ∈ˢ (univ W : V) := by
  cases kind with
  | structMk => exact Ix.Kernel.Model.mkTower_mem_univ hW hargs
  | sumMk c =>
    refine Ix.Kernel.Model.spair_mem_univ hW (Ix.Kernel.Model.vnat_mem_univ hW c)
      (Ix.Kernel.Model.mkTower_mem_univ hW fun a ha => ?_)
    rcases List.mem_append.mp ha with h1 | h2
    · exact hargs a h1
    · rw [List.mem_singleton.mp h2]; exact pt_mem_univ hW
  | psigmaMk =>
    cases args with
    | nil => exact pt_mem_univ hW
    | cons a rest =>
      cases rest with
      | nil => exact pt_mem_univ hW
      | cons b _ =>
        exact Ix.Kernel.Model.spair_mem_univ hW (hargs a List.mem_cons_self)
          (hargs b (List.mem_cons_of_mem _ List.mem_cons_self))
  | propMk => exact pt_mem_univ hW

/-- Finite-fuel `treeUnpackOpt` preserves membership in any nonempty Grothendieck universe `univ W`. -/
theorem treeUnpackOpt_mem_univ {V : Type u} [SetTheory V] {W : Nat} (hW : W ≠ 0)
    (spec : Ix.Kernel.Term.UnpackSpec) :
    ∀ (N : Nat) {y v : V}, y ∈ˢ (univ W : V) →
      Ix.Kernel.SetModel.treeUnpackOpt spec N y = some v → v ∈ˢ (univ W : V)
  | 0, _, _, _, h => by simp [Ix.Kernel.SetModel.treeUnpackOpt] at h
  | N + 1, y, v, hy, h => by
    simp only [Ix.Kernel.SetModel.treeUnpackOpt] at h
    split at h
    · cases hsp : spec[Classical.choose ‹_›]? with
      | none => simp [hsp] at h; subst h; exact hy
      | some rule =>
        cases rule with
        | passthrough => simp [hsp] at h; subst h; exact hy
        | rebuild kind recFlags =>
          simp only [hsp] at h
          cases hf : Ix.Kernel.SetModel.treeUnpackFields
              (Ix.Kernel.SetModel.treeUnpackOpt spec N) (ssnd y) 0 recFlags with
          | none => simp [hf] at h
          | some args =>
            simp only [hf, Option.some.injEq] at h
            subst h
            have hss : ssnd y ∈ˢ (univ W : V) := ssnd_mem_univ hW hy
            have hargs : ∀ a ∈ args, a ∈ˢ (univ W : V) := by
              have hgo : ∀ (idx : Nat) (flags : List Bool) (as : List V),
                  Ix.Kernel.SetModel.treeUnpackFields
                    (Ix.Kernel.SetModel.treeUnpackOpt spec N) (ssnd y) idx flags = some as →
                  ∀ a ∈ as, a ∈ˢ (univ W : V) := by
                intro idx flags
                induction flags generalizing idx with
                | nil =>
                  intro as h0 a ha
                  simp [Ix.Kernel.SetModel.treeUnpackFields] at h0
                  subst h0; simp at ha
                | cons isRec rest ih =>
                  intro as h0 a ha
                  simp only [Ix.Kernel.SetModel.treeUnpackFields] at h0
                  cases h1 : (if isRec then Ix.Kernel.SetModel.treeUnpackOpt spec N (projS idx (ssnd y))
                      else some (projS idx (ssnd y))) with
                  | none => simp [h1] at h0
                  | some v0 =>
                    cases h2 : Ix.Kernel.SetModel.treeUnpackFields
                        (Ix.Kernel.SetModel.treeUnpackOpt spec N) (ssnd y) (idx + 1) rest with
                    | none => simp [h1, h2] at h0
                    | some vs =>
                      simp only [h1, h2, Option.some.injEq] at h0
                      subst h0
                      rcases List.mem_cons.mp ha with rfl | ha'
                      · cases isRec
                        · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h1
                          subst h1; exact projS_mem_univ hW idx hss
                        · simp only [↓reduceIte] at h1
                          exact treeUnpackOpt_mem_univ hW spec N (projS_mem_univ hW idx hss) h1
                      · exact ih (idx + 1) vs h2 a ha'
              exact hgo 0 recFlags args hf
            exact rebuildCtor_mem_univ hW kind hargs
    · injection h with hv; subst hv; exact hy

/-! ### `unpack_eval_induction` -/

set_option maxHeartbeats 2400000 in
/-- Structural induction on `famAux`'s fixed point proving that applying `aux.rec` at the
checked unpack recursor arguments `uarVals` terminates under `treeUnpackOpt (unpackSpecOf hminors)`
and computes `treeUnpack (unpackSpecOf hminors) y`. -/
theorem unpack_eval_induction {V : Type u} [SetTheory V] {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Env .anon} {Reg : NativeFam .anon → Prop}
    (ht : t.check = .ok ())
    (hbasis : ∀ ci ∈ IxVM.Refinement.TableInhabit.basisEnv.consts, env.find? ci.name = some ci)
    (hreg : FamRegistryWith FormerOpenTraceAt t E env Reg)
    (mp : EnvModelM V .verified env)
    (hN : ∀ fam, Reg fam → NativeFamOk mp fam)
    {auxKey auxRecKey : KKey} {cvAuxRec : ConstantVal .anon} {arules : List (RecRule .anon)}
    {nP bnl anc : Nat}
    (auxIndWit : NativeIndWitness t E env auxKey)
    (hauxInd_lvls : auxIndWit.cv.levelParams.length = bnl)
    (hauxInd_idx : auxIndWit.ip.idx.toNat = 0)
    (hauxInd_rec : ∃ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (ind : Ixon.Inductive),
      Ix.Cert.recordAt E auxIndWit.ip.block = some cb ∧ cb.info = .muts ms ∧
      ms[0]? = some (.indc ind) ∧ ind.params.toNat = nP ∧ ind.indices.toNat = 1 ∧
      ind.ctors.size = anc)
    (hauxInd_sort : ∃ bs u, (Core.posOf auxIndWit.cv.levelParams auxIndWit.cv.type).stripPis (nP + 1) =
      some (bs, .sort u) ∧ ∀ φ, (substLevel u ((List.range bnl).map .param)).eval φ > 0)
    (hfindAuxRec : env.find? auxRecKey =
      some (.recInfo cvAuxRec (nP + 1 + anc + 1) (nP + 1 + anc) arules))
    (hAuxRec_lvls : cvAuxRec.levelParams.length = bnl + 1)
    (hAuxRec_perm : cvAuxRec.levelParams.Perm (List.range (bnl + 1)))
    (hauxRec_famBlk : ∃ (aR : _root_.Address) (cHost : Ixon.Constant) (rcR : Ixon.Recursor)
        (nf : Nat) (p0 : _root_.Address) (cm0 : Ixon.Constant) (ip0 : Ixon.InductiveProj),
      Core.keyOf t aR = auxRecKey ∧ RecHostAt E aR cHost rcR ∧
      recMotiveCarrierAt cHost rcR 0 nf = some p0 ∧
      Ix.Cert.recordAt E p0 = some cm0 ∧ cm0.info = .iPrj ip0 ∧ ip0.block = auxIndWit.ip.block)
    (hAuxRec_maj : ∃ majBs majDom majBody majBm majLvls majArgs,
      (Core.posOf cvAuxRec.levelParams cvAuxRec.type).stripPis (nP + 1 + anc + 1) =
        some (majBs, .forallE majDom majBody majBm) ∧
      majDom = Expr.mkAppN (.const auxKey majLvls) majArgs ∧
      LvEqList majLvls ((List.range bnl).map fun m => .param (1 + m)) ∧
      majArgs.length = nP + 1 ∧
      List.Forall₂ ExprSemEq (majArgs.take nP)
        ((List.range nP).map fun m => .bvar (nP + 1 + anc + 1 - 1 - m)) ∧
      majArgs[nP]? = some (.bvar 0))
    (hrecCtor : ∀ j rl, arules[j]? = some rl →
      rl.ctor = Core.keyOf t (Core.cprjAddr auxIndWit.ip.block 0 j))
    -- Registered native family `famAux`
    {famAux : NativeFam .anon} {env₀ : Env .anon} {bsT : List (KExpr × BinderMeta)}
    {ppsAll : (LevelParam → Nat) → List (Nat × Nat × AnnotTerm)}
    {uAV : (LevelParam → Nat) → Nat} {fssZ : (LevelParam → Nat) → List (List AnnotTerm)}
    {idxF : Nat → List KExpr}
    {dsF : Nat → (LevelParam → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (LevelParam → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
    {ksF : Nat → List Ix.Kernel.RecFieldKind} {fvsPF xFvsF : Nat → List KExpr}
    {xrestF : Nat → KExpr}
    {eissF : Nat → (LevelParam → Nat) → List (List AnnotTerm)}
    {tssF : Nat → (LevelParam → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (hregAux : Reg famAux) (hnameAux : famAux.p.cvT.name = auxKey)
    (hAtAux : NativeFamAt mp famAux.p famAux.cvS famAux.cvTa famAux.ctorsA env₀ bsT ppsAll
      uAV fssZ idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF)
    -- Unpack recursor call arguments
    {uarLvls : List KLevel} {uarArgs : List KExpr}
    (huar_lvls_len : uarLvls.length = bnl + 1)
    (huar_elim_nz : ∀ φ, (uarLvls.getD 0 .zero).eval φ > 0)
    (huar_lvls_drop : LvEqList (uarLvls.drop 1) ((List.range bnl).map .param))
    (huar_len : uarArgs.length = nP + 1 + anc)
    (huar_pref : List.Forall₂ ExprSemEq (uarArgs.take nP)
      ((List.range nP).map fun m => .bvar (nP - 1 - m)))
    (hminors : ∀ k (hk : k < anc),
      ∃ rl, arules[k]? = some rl ∧
        Nonempty (UnpackMinorWitness t E env auxKey auxRecKey cvAuxRec.levelParams
          (Core.keyOf t (Core.cprjAddr auxIndWit.ip.block 0 k)) nP bnl anc k
          (uarArgs.drop (nP + 1) |>.getD k default) rl))
    -- Valuation, parameter spine, and denoted `uarArgsA`
    (ψ_P : LevelParam → Nat) (ρ₀ : Nat → V) (vs_v : List V)
    (hvs_len : vs_v.length = nP)
    (hsp_p : SpineFit ρ₀ (((ppsAll ψ_P).take famAux.p.nP).map (·.2.2)) vs_v)
    {uarArgsA : List AnnotTerm}
    (hsp_uar : DenoteMetaSpine mp.base2.acval env ψ_P nP
      (uarArgs.map (openDummiesP nP 0 0)) uarArgsA)
    (hwd_uar : ∀ a ∈ uarArgsA, WellDenotedV V (consList vs_v ρ₀) a) :
    let uarVals := uarArgsA.map (interp V (consList vs_v ρ₀))
    let ψ_rec_ua := origVal cvAuxRec.levelParams (ψ_rec uarLvls bnl ψ_P)
    let spec := unpackSpecOf hminors
    ∀ (t_tup y : V),
      t_tup ∈ˢ Ix.Kernel.Semantics.idxSet (uAV ψ_P) (consList vs_v ρ₀)
        (((ppsAll ψ_P).drop famAux.p.nP).map (·.2.2)) →
      y ∈ˢ SetTheory.app (fixFamI (uAV ψ_P) (famAux.p.resSort.eval ψ_P) (consList vs_v ρ₀)
        (((ppsAll ψ_P).drop famAux.p.nP).map (·.2.2)) 1
        (Ix.Kernel.Model.rssOfK ksF famAux.ctorsA.length)
        (Ix.Kernel.Model.tlssOfR (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0))
        (Ix.Kernel.Model.eissOfR (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0))
        (fssZ ψ_P)
        (Ix.Kernel.Model.essOfR (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0)))
        t_tup →
      ∀ t_real : V, t_tup = tupW (uAV ψ_P) [t_real] →
        AppChainOk (interp V ρ₀ (mp.base2.acval auxRecKey ψ_rec_ua)) (uarVals ++ [t_real, y]) →
        (∃ N, Ix.Kernel.SetModel.treeUnpackOpt spec N y =
          some (Ix.Kernel.SetModel.treeUnpack spec y)) ∧
        (uarVals ++ [t_real, y]).foldl SetTheory.app
          (interp V ρ₀ (mp.base2.acval auxRecKey ψ_rec_ua)) =
          Ix.Kernel.SetModel.treeUnpack spec y := by
  intro uarVals ψ_rec_ua spec
  -- 1. Establish `famAux` metadata & `hw_aux : famAux.p.resSort.eval ψ_P ≠ 0`
  have hreadAux := hreg.fams famAux hregAux
  have hreadAtAux := hreadAux.readAt ht (hnameAux.trans auxIndWit.hkey.symm) auxIndWit.hrec auxIndWit.hinfo
  obtain ⟨-, -, cbA, msA, indA, hcbA, hmsA, hindA, hnPA, hnIdxA, hlenA, hctorNameA⟩ := hreadAtAux
  have ⟨cb', ms', ind', hcb', hms', hind', hnP', hnIdx', hanc'⟩ := hauxInd_rec
  have hcb_eq : cbA = cb' := Option.some.inj (hcbA.symm.trans hcb')
  subst hcb_eq
  have hms_eq : msA = ms' := Ixon.ConstantInfo.muts.inj (hmsA.symm.trans hms')
  subst hms_eq
  rw [hauxInd_idx] at hindA hctorNameA
  have hind_eq : indA = ind' := Ixon.MutConst.indc.inj (Option.some.inj (hindA.symm.trans hind'))
  subst hind_eq
  have hfam_nP : famAux.p.nP = nP := hnPA.trans hnP'
  have hfam_nIdx : famAux.p.nIdx = 1 := hnIdxA.trans hnIdx'
  have hfam_ctors_len : famAux.ctorsA.length = anc := hlenA.trans hanc'
  have hfam_lps : famAux.p.cvT.levelParams = List.range bnl :=
    famRead_lps_range hreadAux (by rw [← hreadAux.lps, famRead_cvS_eq hreadAux hnameAux auxIndWit.hfind]; exact hauxInd_lvls)
  have horig_fam : origVal famAux.p.cvT.levelParams ψ_P = ψ_P := by
    unfold origVal Core.posLevels
    rw [hfam_lps, List.length_range]
    exact substFn_range_param bnl ψ_P
  have hIds_len : (((ppsAll ψ_P).drop famAux.p.nP).map (·.2.2)).length = 1 := by
    have := hAtAux.former.len ψ_P
    rw [List.length_map, List.length_drop, this, hfam_nIdx]; omega
  have hw_aux : famAux.p.resSort.eval ψ_P ≠ 0 := by
    obtain ⟨bsS, uS, hstS, huS⟩ := hauxInd_sort
    have hcvS_eq : famAux.cvS = auxIndWit.cv := famRead_cvS_eq hreadAux hnameAux auxIndWit.hfind
    rw [← hcvS_eq] at hstS
    obtain ⟨-, hlv⟩ := famRead_resSort_of_stripPisZetaSort mp.base2.wf hreadAux
      (stripPis_to_stripPisZetaSort hstS)
    have h1 := huS ψ_P
    rw [eval_substLevel_eq_substFn (n := bnl) (by simp) ψ_P uS, substFn_range_param] at h1
    rw [← hlv ψ_P]; omega
  -- 2. Useful properties of `uarVals`
  have huarArgsA_len : uarArgsA.length = nP + 1 + anc := by
    have := denoteMetaSpine_length_eq hsp_uar; simp only [List.length_map, huar_len] at this; exact this.symm
  have huarVals_len : uarVals.length = nP + 1 + anc := by
    simp [uarVals, huarArgsA_len]
  have huarVals_pref : uarVals.take nP = vs_v := by
    refine List.ext_getElem (by rw [List.length_take, huarVals_len, hvs_len]; omega) fun i hi1 hi2 => ?_
    rw [List.getElem_take]
    simp only [uarVals, List.getElem_map]
    have hden := denoteMetaSpine_getElem hsp_uar (i := i) (by simp [huar_len]; omega)
    simp only [List.getElem_map] at hden
    have heq_i : ExprSemEq (uarArgs[i]'(by omega)) (.bvar (nP - 1 - i)) := by
      have := forall₂_getElem huar_pref i (by rw [List.length_take, huar_len]; omega) (by simp; omega)
      simpa [List.getElem_take] using this
    have hden_bv : denoteMeta mp.base2.acval env ψ_P nP
        (openDummiesP nP 0 0 (.bvar (nP - 1 - i))) = some (.bvar (nP - 1 - i)) :=
      denoteMeta_openDummiesP_bvar0 (by omega)
    have hsame := (denoteMeta_exprSemEq (acval := mp.base2.acval) (env := env) (φ := ψ_P) (d := nP)
      (exprSemEq_openDummiesP heq_i nP 0 0)).symm.trans hden
    rw [hden_bv] at hsame
    have ha_eq : uarArgsA[i]'(by omega) = .bvar (nP - 1 - i) := (Option.some.inj hsame).symm
    rw [ha_eq, interp_bvar, ← hvs_len, consList_bvar_desc vs_v ρ₀ (by omega)]
  -- 3. `hfr` for `famAux` at `consList vs_v ρ₀`
  have hsat_p : Sat V (((ppsAll ψ_P).take famAux.p.nP).map (·.2.2)).reverse
      (consList vs_v ρ₀) := by
    have hs := Ix.Kernel.Model.sat_of_spineFit (Δ₀ := []) (Ix.Kernel.Semantics.Sat_nil V ρ₀) hsp_p
    simpa using hs
  have hfr := hAtAux.frames ψ_P (consList vs_v ρ₀) hsat_p
  -- 4. Prepare `aux.rec`'s major domain typing once (for `aux_fibre_disjoint` on recursive fields)
  have hnotResRec : Ix.Kernel.reservedBasisNames.contains auxRecKey = false := by
    obtain ⟨majBs, majDom, majBody, majBm, majLvls, majArgs, hmajStrip, hmajDom, -⟩ := hAuxRec_maj
    exact auxRec_not_reserved hfindAuxRec auxIndWit.hnotRes hbasis hmajStrip hmajDom
  have hnoModelRec : ¬ HasModel env auxRecKey := by
    intro hm
    obtain ⟨aR, cHost, rcR, nf, p0, cm0, ip0, haR, hrcR, hmc, hcm0, hip0, hblk0⟩ :=
      hauxRec_famBlk
    subst haR
    have hnotNat := hreg.recModelNotNative aR cvAuxRec (nP + 1 + anc + 1) (nP + 1 + anc) arules
      cHost rcR nf p0 cm0 ip0 hfindAuxRec hm hrcR hmc hcm0 hip0
    rw [hblk0] at hnotNat
    exact hnotNat auxIndWit.hnat
  -- Helper: from `AppChainOk (acval auxRecKey ψ_rec_ua) (uarVals ++ [t', z])`, deduce
  -- `SpineFit (consList vs_v ρ₀) Ids [t'] ∧ z ∈ˢ app μ_aux (tupW (uAV ψ_P) [t'])`!
  have hmem_aux_of_appRec : ∀ t' z : V,
      AppChainOk (interp V ρ₀ (mp.base2.acval auxRecKey ψ_rec_ua)) (uarVals ++ [t', z]) →
      SpineFit (consList vs_v ρ₀) (((ppsAll ψ_P).drop famAux.p.nP).map (·.2.2)) [t'] ∧
      z ∈ˢ SetTheory.app (fixFamI (uAV ψ_P) (famAux.p.resSort.eval ψ_P) (consList vs_v ρ₀)
        (((ppsAll ψ_P).drop famAux.p.nP).map (·.2.2)) 1
        (Ix.Kernel.Model.rssOfK ksF famAux.ctorsA.length)
        (Ix.Kernel.Model.tlssOfR (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0))
        (Ix.Kernel.Model.eissOfR (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0))
        (fssZ ψ_P)
        (Ix.Kernel.Model.essOfR (Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0)))
        (tupW (uAV ψ_P) [t']) := by
    intro t' z hApp_tz
    obtain ⟨majBs, majDom, majBody, majBm, majLvls, majArgs, hmajStrip, hmajDom, hmajLvls,
      hmajArgs_len, hmajArgs_pref, hmajArgs_idx⟩ := hAuxRec_maj
    obtain ⟨pre0, rem0, hstrip0, hrem0⟩ := stripPis_posOf_inv hmajStrip
    cases rem0 with
    | forallE dom0 body0 majBm0 =>
      obtain ⟨hpre0_pw, hlarge0, -⟩ :=
        hreg.recRhsPw auxRecKey cvAuxRec (nP + 1 + anc + 1) (nP + 1 + anc) arules
          hfindAuxRec hnotResRec hnoModelRec pre0 dom0 body0 majBm0 hstrip0
      have hdom0_eq : Core.posOf cvAuxRec.levelParams dom0 = majDom := by
        simp only [Core.posOf, Expr.instantiateLevelParams] at hrem0
        exact (Expr.forallE.inj hrem0).1.symm
      have hdom0_fn : ∃ us0, dom0.getAppFn = .const auxKey us0 ∧ us0.length = bnl := by
        have hfn_pos : (Core.posOf cvAuxRec.levelParams dom0).getAppFn = .const auxKey majLvls := by
          rw [hdom0_eq, hmajDom, Expr.getAppFn_mkAppN]; rfl
        have hgo : ∀ (e : KExpr), (Core.posOf cvAuxRec.levelParams e).getAppFn = .const auxKey majLvls →
            ∃ us0, e.getAppFn = .const auxKey us0 ∧ us0.length = majLvls.length := by
          intro e
          induction e with
          | app f a ihf _ =>
            intro h; simp only [Core.posOf, Expr.instantiateLevelParams, Expr.getAppFn] at h ⊢; exact ihf h
          | const n us =>
            intro h; simp only [Core.posOf, Expr.instantiateLevelParams, Expr.getAppFn] at h ⊢
            injection h with hn hus; subst hn hus; exact ⟨us, rfl, by simp⟩
          | bvar _ | fvar _ _ | sort _ | lam _ _ _ | forallE _ _ _ | letE _ _ _ _ | lit _
          | proj _ _ _ => intro h; simp [Core.posOf, Expr.instantiateLevelParams, Expr.getAppFn] at h
        obtain ⟨us0, hfn0, hlen0⟩ := hgo dom0 hfn_pos
        have hmlen : majLvls.length = bnl := by
          have h1 := (lvEqList_getElem hmajLvls).1; simpa using h1
        exact ⟨us0, hfn0, hlen0.trans hmlen⟩
      obtain ⟨us0, hdom0_fn, hus0_len⟩ := hdom0_fn
      obtain ⟨elim, restLps, hcvLps_cons, hmaj0_pw, -⟩ := hlarge0 auxKey us0 hdom0_fn (by omega)
      have hmemR := Ix.Kernel.Semantics.Env.find?_mem hfindAuxRec
      obtain ⟨TVa, hTVa⟩ := mp.type_reads _ hmemR ψ_rec_ua
      have hTVa_mem := mp.mem_type _ hmemR ψ_rec_ua TVa hTVa ρ₀
      have hTVa_wd := mp.type_wellDenotedV _ hmemR ψ_rec_ua TVa hTVa ρ₀
      have hTVa_pos : denoteMeta mp.base2.acval env (ψ_rec uarLvls bnl ψ_P) 0
          (Core.posOf cvAuxRec.levelParams cvAuxRec.type) = some TVa := by
        rw [posOf_denoteMeta]; exact hTVa
      -- Strip `nP + 1 + anc + 1` Pis + 1 more Pi (`majDom`) from `cvAuxRec.type`
      have hstrip_all : (Core.posOf cvAuxRec.levelParams cvAuxRec.type).stripPis (nP + 1 + anc + 2) =
          some (majBs ++ [(majDom, majBm)], majBody) := by
        have h1 : (Expr.forallE majDom majBody majBm).stripPis 1 = some ([(majDom, majBm)], majBody) := by
          simp [Expr.stripPis]
        exact Ix.Kernel.stripPis_append (nP + 1 + anc + 1) hmajStrip h1
      obtain ⟨dsR, bodyR, hTVa_mk, hdsR_len, hdsR_bits, -⟩ :=
        denoteMeta_stripPis (nP + 1 + anc + 2) 0 hstrip_all hTVa_pos
      -- Check `dsR` bits are all nonzero!
      have helim_nz_orig : ψ_rec_ua elim ≠ 0 := by
        have hnd : cvAuxRec.levelParams.Nodup := hAuxRec_perm.nodup_iff.mpr List.nodup_range
        have hs0 := substFn_getElem (ψ := ψ_rec uarLvls bnl ψ_P) cvAuxRec.levelParams
          (Core.posLevels cvAuxRec.levelParams) hnd (by simp [Core.posLevels]) 0 (by rw [hcvLps_cons]; simp)
        change Level.substFn (ψ_rec uarLvls bnl ψ_P) cvAuxRec.levelParams
          (Core.posLevels cvAuxRec.levelParams) elim ≠ 0
        rw [show elim = cvAuxRec.levelParams[0]'(by rw [hcvLps_cons]; simp) by simp [hcvLps_cons], hs0]
        simp only [Core.posLevels, List.getElem_map, List.getElem_range, Level.eval, ψ_rec, ↓reduceIte]
        have := huar_elim_nz ψ_P; omega
      have hpos_dsR : ∀ d ∈ dsR, d.2.1 ≠ 0 := by
        have hstrip0_all : cvAuxRec.type.stripPis (nP + 1 + anc + 2) =
            some (pre0 ++ [(dom0, majBm0)], body0) :=
          Ix.Kernel.stripPis_append (nP + 1 + anc + 1) hstrip0
            (show (dom0.forallE body0 majBm0).stripPis 1 = some ([(dom0, majBm0)], body0) from rfl)
        obtain ⟨dsR0, bodyR0, hTVa_mk0, hdsR0_len, hdsR0_bits, -⟩ :=
          denoteMeta_stripPis (nP + 1 + anc + 2) 0 hstrip0_all hTVa
        have hds_eq : dsR = dsR0 := by
          have hgo : ∀ (l1 l2 : List (Nat × Nat × AnnotTerm)) (b1 b2 : AnnotTerm),
              l1.length = l2.length → mkPisAV l1 b1 = mkPisAV l2 b2 → l1 = l2 := by
            intro l1
            induction l1 with
            | nil => intro l2 _ _ hl _; cases l2 with | nil => rfl | cons _ _ => simp at hl
            | cons d1 l1 ih =>
              intro l2 b1 b2 hl hmk
              cases l2 with
              | nil => simp at hl
              | cons d2 l2 =>
                simp only [mkPisAV] at hmk
                obtain ⟨h1, h2, h3, h4⟩ := AnnotTerm.pi.inj hmk
                have hd : d1 = d2 := by rcases d1 with ⟨a1, b1', c1⟩; rcases d2 with ⟨a2, b2', c2⟩; exact Prod.ext h1 (Prod.ext h2 h3)
                rw [hd, ih l2 b1 b2 (by simpa using hl) h4]
          exact hgo dsR dsR0 bodyR bodyR0 (by omega) (hTVa_mk.symm.trans hTVa_mk0)
        rw [hds_eq]
        intro d hd
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
        have hbi := map_getElem_eq hdsR0_bits i hi (by rw [stripPis_length_p hstrip0_all]; omega)
        have hpw_i : ((pre0 ++ [(dom0, majBm0)])[i]'(by rw [stripPis_length_p hstrip0_all, ← hdsR0_len]; exact hi)).2.pw =
            .ifAllZero [elim] := by
          have hmem_i : (pre0 ++ [(dom0, majBm0)])[i]'(by rw [stripPis_length_p hstrip0_all, ← hdsR0_len]; exact hi) ∈
              pre0 ++ [(dom0, majBm0)] := List.getElem_mem _
          rcases List.mem_append.mp hmem_i with hp | hm
          · rw [hpre0_pw _ hp, hmaj0_pw]
          · rw [List.mem_singleton.mp hm]; exact hmaj0_pw
        rw [hbi, hpw_i]
        simp only [pwBit, Ix.Kernel.PropWhen.holds_ifAllZero, List.all_cons, List.all_nil,
          Bool.and_true, beq_iff_eq]
        split_ifs with h0
        · exact absurd h0 helim_nz_orig
        · exact Nat.one_ne_zero
      -- Extract `SpineFit` on `uarVals ++ [t', z]` from `spineFit_of_mkPisAV_appChainOk_pos`!
      rw [hTVa_mk] at hTVa_mem hTVa_wd
      rw [Ix.Kernel.Semantics.Env.find?_name hfindAuxRec] at hTVa_mem
      have hsp_rec := spineFit_of_mkPisAV_appChainOk_pos dsR bodyR (uarVals ++ [t', z]) ρ₀
        hpos_dsR (by simp [hdsR_len, huarVals_len]) hTVa_mem hApp_tz
      -- Read the last element `majDomA = dsR[nP + 1 + anc + 1].2.2`!
      have hdsR_split : dsR.map (·.2.2) =
          (dsR.take (nP + 1 + anc + 1)).map (·.2.2) ++ [((dsR[nP + 1 + anc + 1]'(by omega)).2.2)] := by
        have htake : dsR = dsR.take (nP + 1 + anc + 1) ++ [dsR[nP + 1 + anc + 1]'(by omega)] := by
          have := List.take_append_drop (nP + 1 + anc + 1) dsR
          have hdrop : dsR.drop (nP + 1 + anc + 1) = [dsR[nP + 1 + anc + 1]'(by omega)] := by
            refine List.ext_getElem (by simp [hdsR_len]) fun i hi1 hi2 => ?_
            have hi0 : i = 0 := by simp at hi2; omega
            subst hi0; simp
          rw [hdrop] at this; exact this.symm
        conv_lhs => rw [htake]
        rw [List.map_append]; rfl
      have hargs_split : uarVals ++ [t', z] = (uarVals ++ [t']) ++ [z] := by simp
      rw [hdsR_split, hargs_split] at hsp_rec
      obtain ⟨hsp_pre, hsp_last⟩ := (spineFit_append_iff
        (by simp [hdsR_len, huarVals_len])).mp hsp_rec
      have hz_mem_maj : z ∈ˢ interp V (consList (uarVals ++ [t']) ρ₀)
          (dsR[nP + 1 + anc + 1]'(by omega)).2.2 := hsp_last.1
      -- Identify `(dsR[nP + 1 + anc + 1]).2.2` with `denoteMeta ... majDom` AND get its `WellDenotedV`!
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
      obtain ⟨dsR1, remR1, hTVa_mk1, hdsR1_len, -, hremR1_den⟩ :=
        denoteMeta_stripPis (nP + 1 + anc + 1) 0 hmajStrip hTVa_pos
      rw [hopen_for] at hremR1_den
      obtain ⟨majDomA, _, hmajDomA_den, -, hremR1_eq⟩ := denoteMeta_forallE_some hremR1_den
      have hds_prefix_eq : dsR1 = dsR.take (nP + 1 + anc + 1) ∧
          (dsR[nP + 1 + anc + 1]'(by omega)).2.2 = majDomA := by
        have htake_ds : dsR = dsR.take (nP + 1 + anc + 1) ++ [dsR[nP + 1 + anc + 1]'(by omega)] := by
          have := List.take_append_drop (nP + 1 + anc + 1) dsR
          have hdrop : dsR.drop (nP + 1 + anc + 1) = [dsR[nP + 1 + anc + 1]'(by omega)] := by
            refine List.ext_getElem (by simp [hdsR_len]) fun i hi1 hi2 => ?_
            have hi0 : i = 0 := by simp at hi2; omega
            subst hi0; simp
          rw [hdrop] at this; exact this.symm
        have hmk_both : mkPisAV dsR1 remR1 =
            mkPisAV (dsR.take (nP + 1 + anc + 1)) (.pi (dsR[nP + 1 + anc + 1]'(by omega)).1
              (dsR[nP + 1 + anc + 1]'(by omega)).2.1 (dsR[nP + 1 + anc + 1]'(by omega)).2.2 bodyR) := by
          have hmk_ds : mkPisAV dsR bodyR =
              mkPisAV (dsR.take (nP + 1 + anc + 1)) (.pi (dsR[nP + 1 + anc + 1]'(by omega)).1
                (dsR[nP + 1 + anc + 1]'(by omega)).2.1 (dsR[nP + 1 + anc + 1]'(by omega)).2.2 bodyR) := by
            have hmk_app : ∀ (l1 l2 : List (Nat × Nat × AnnotTerm)) (b : AnnotTerm),
                mkPisAV (l1 ++ l2) b = mkPisAV l1 (mkPisAV l2 b) := by
              intro l1; induction l1 with
              | nil => intro _ _; rfl
              | cons d l1 ih => intro l2 b; simp only [List.cons_append, mkPisAV, ih]
            conv_lhs => rw [htake_ds]
            rw [hmk_app]; rfl
          rw [← hTVa_mk1, hTVa_mk]
          exact hmk_ds
        have hgo : ∀ (l1 l2 : List (Nat × Nat × AnnotTerm)) (b1 b2 : AnnotTerm),
            l1.length = l2.length → mkPisAV l1 b1 = mkPisAV l2 b2 → l1 = l2 ∧ b1 = b2 := by
          intro l1
          induction l1 with
          | nil =>
            intro l2 b1 b2 hl hmk; cases l2 with
            | nil => exact ⟨rfl, hmk⟩
            | cons _ _ => simp at hl
          | cons d1 l1 ih =>
            intro l2 b1 b2 hl hmk
            cases l2 with
            | nil => simp at hl
            | cons d2 l2 =>
              simp only [mkPisAV] at hmk
              obtain ⟨h1, h2, h3, h4⟩ := AnnotTerm.pi.inj hmk
              have hd : d1 = d2 := by rcases d1 with ⟨a1, b1', c1⟩; rcases d2 with ⟨a2, b2', c2⟩; exact Prod.ext h1 (Prod.ext h2 h3)
              obtain ⟨htl, hb⟩ := ih l2 b1 b2 (by simpa using hl) h4
              exact ⟨by rw [hd, htl], hb⟩
        obtain ⟨hl_eq, hb_eq⟩ := hgo dsR1 (dsR.take (nP + 1 + anc + 1)) remR1 _
          (by simp [hdsR1_len, hdsR_len]) hmk_both
        rw [← hremR1_eq] at hb_eq
        exact ⟨hl_eq, (AnnotTerm.pi.inj hb_eq).2.2.1.symm⟩
      -- Obtain `WellDenotedV` of `majDomA` at `consList (uarVals ++ [t']) ρ₀` from `hTVa_wd` + `hsp_pre`
      have hwd_mkPis : ∀ (ds : List (Nat × Nat × AnnotTerm)) (b : AnnotTerm) (xs : List V) (ρ : Nat → V),
          ds.length = xs.length → WellDenotedV V ρ (mkPisAV ds b) →
          SpineFit ρ (ds.map (·.2.2)) xs → WellDenotedV V (consList xs ρ) b := by
        intro ds
        induction ds with
        | nil =>
          intro b xs ρ hl hwd _
          cases xs with | nil => exact hwd | cons _ _ => simp at hl
        | cons d ds ih =>
          intro b xs ρ hl hwd hsp
          cases xs with
          | nil => simp at hl
          | cons x xs =>
            simp only [mkPisAV, WellDenotedV, WellDenoted_pi, AnnotValid_pi] at hwd
            simp only [List.map_cons, SpineFit] at hsp
            simpa [consList] using ih b xs (cons x ρ) (by simpa using hl)
              ⟨hwd.1.2 x hsp.1, hwd.2.2.1 x hsp.1⟩ hsp.2
      have hTVa_wd1 : WellDenotedV V ρ₀ (mkPisAV dsR1 remR1) := by
        rw [← hTVa_mk1, hTVa_mk]; exact hTVa_wd
      have hwd_remR1 := hwd_mkPis dsR1 remR1 (uarVals ++ [t']) ρ₀
        (by simp [hdsR1_len, huarVals_len]) hTVa_wd1 (by rw [hds_prefix_eq.1]; exact hsp_pre)
      rw [← hremR1_eq] at hwd_remR1
      have hwd_majDom : WellDenotedV V (consList (uarVals ++ [t']) ρ₀) majDomA :=
        ⟨hwd_remR1.1.1, hwd_remR1.2.1⟩
      -- Evaluate `majDomA = mkAppN (acval auxKey ψ_P) majArgsA`!
      rw [hmajDom, openDummiesP_mkAppN, openDummiesP_const] at hmajDomA_den
      obtain ⟨faM, margsA, hfaM, hspM, hmajDomA_eq⟩ := denoteMeta_mkAppN_inv hmajDomA_den
      simp only [denoteMeta, auxIndWit.hfind] at hfaM
      have hml_len : majLvls.length = auxIndWit.cv.levelParams.length := by
        have h1 := (lvEqList_getElem hmajLvls).1; simp only [List.length_map, List.length_range] at h1
        omega
      simp only [ConstantInfo.toConstantVal, hml_len, ↓reduceIte, Option.some.injEq] at hfaM
      have hfaM_eq : faM = mp.base2.acval auxKey ψ_P := by
        rw [← hfaM]
        have hcv_aux_lps : auxIndWit.cv.levelParams = List.range bnl := by
          rw [← famRead_cvS_eq hreadAux hnameAux auxIndWit.hfind, hreadAux.lps, hfam_lps]
        exact mp.base2.acval_params auxKey (.indInfo auxIndWit.cv auxIndWit.caps) auxIndWit.hfind _ _ (fun q hq => by
          simp only [ConstantInfo.toConstantVal] at hq
          rw [hcv_aux_lps, List.mem_range] at hq
          rw [hcv_aux_lps, substFn_eq_of_lvEqList hmajLvls (ψ_rec uarLvls bnl ψ_P)]
          have hsub := substFn_getElem (ψ := ψ_rec uarLvls bnl ψ_P) (List.range bnl)
            ((List.range bnl).map fun m => .param (1 + m)) List.nodup_range (by simp) q (by simp [hq])
          have hne0 : (1 + q = 0) = False := eq_false (Nat.one_add q ▸ Nat.succ_ne_zero q)
          have hlt1 : (1 + q < bnl + 1) = True := eq_true (Nat.add_comm 1 q ▸ Nat.add_lt_add_right hq 1)
          simp only [List.getElem_range, List.getElem_map, Level.eval, ψ_rec,
            hne0, hlt1, ↓reduceIte, Nat.add_sub_cancel_left] at hsub
          exact hsub)
      -- Evaluate `margsA` at `consList (uarVals ++ [t']) ρ₀` to `vs_v ++ [t']`
      have hmargsA_len : margsA.length = nP + 1 := by
        have := denoteMetaSpine_length_eq hspM; simp only [List.length_map, hmajArgs_len] at this; exact this.symm
      have hmargsV_eq : margsA.map (interp V (consList (uarVals ++ [t']) ρ₀)) = vs_v ++ [t'] := by
        refine List.ext_getElem (by simp [hmargsA_len, hvs_len]) fun i hi1 hi2 => ?_
        have hi_lt : i < nP + 1 := by simp [hmargsA_len] at hi1; omega
        simp only [List.getElem_map]
        have hden_i := denoteMetaSpine_getElem hspM (i := i) (by simp [hmajArgs_len]; omega)
        simp only [List.getElem_map, Nat.zero_add] at hden_i
        by_cases hiP : i < nP
        · have heq_i : ExprSemEq (majArgs[i]'(by omega)) (.bvar (nP + 1 + anc + 1 - 1 - i)) := by
            have := forall₂_getElem hmajArgs_pref i
              (by rw [List.length_take, hmajArgs_len]; omega) (by simp; omega)
            simpa [List.getElem_take] using this
          have hden_bv : denoteMeta mp.base2.acval env (ψ_rec uarLvls bnl ψ_P) (nP + 1 + anc + 1)
              (openDummiesP (nP + 1 + anc + 1) 0 0 (.bvar (nP + 1 + anc + 1 - 1 - i))) =
              some (.bvar (nP + 1 + anc + 1 - 1 - i)) :=
            denoteMeta_openDummiesP_bvar0 (by omega)
          have hsame := (denoteMeta_exprSemEq (acval := mp.base2.acval) (env := env)
            (φ := ψ_rec uarLvls bnl ψ_P) (d := nP + 1 + anc + 1)
            (exprSemEq_openDummiesP heq_i (nP + 1 + anc + 1) 0 0)).symm.trans hden_i
          rw [hden_bv] at hsame
          have ha_eq : margsA[i]'(by omega) = .bvar (nP + 1 + anc + 1 - 1 - i) := (Option.some.inj hsame).symm
          rw [ha_eq, interp_bvar]
          have hlen_u : (uarVals ++ [t']).length = nP + 1 + anc + 1 := by simp [huarVals_len]
          rw [show nP + 1 + anc + 1 - 1 - i = (uarVals ++ [t']).length - 1 - i by omega]
          rw [consList_bvar_desc (uarVals ++ [t']) ρ₀ (by omega)]
          rw [List.getElem_append_left (by omega : i < uarVals.length)]
          rw [List.getElem_append_left (by omega : i < vs_v.length)]
          have hget_pref := congrArg (fun l => l[i]?) huarVals_pref
          rw [List.getElem?_take_of_lt hiP, List.getElem?_eq_getElem (by omega : i < uarVals.length),
            List.getElem?_eq_getElem (by omega : i < vs_v.length)] at hget_pref
          exact Option.some.inj hget_pref
        · have hi_eq : i = nP := by omega
          subst i
          have hidx_eq : majArgs[nP]'(by omega) = .bvar 0 := by
            rw [List.getElem?_eq_getElem (by omega : nP < majArgs.length)] at hmajArgs_idx
            exact Option.some.inj hmajArgs_idx
          rw [hidx_eq] at hden_i
          have hden_bv : denoteMeta mp.base2.acval env (ψ_rec uarLvls bnl ψ_P) (nP + 1 + anc + 1)
              (openDummiesP (nP + 1 + anc + 1) 0 0 (.bvar 0)) = some (.bvar 0) :=
            denoteMeta_openDummiesP_bvar0 (by omega)
          rw [hden_bv] at hden_i
          have ha_eq : margsA[nP]'(by omega) = .bvar 0 := (Option.some.inj hden_i).symm
          rw [ha_eq, interp_bvar, consList_append]
          simp [consList, cons, hvs_len]
      -- Fold `majDomA = mkAppN (acval auxKey ψ_P) margsA` via `hAtAux.leafT ψ_P`!
      rw [hds_prefix_eq.2, hmajDomA_eq, hfaM_eq] at hz_mem_maj
      rw [hmajDomA_eq, hfaM_eq] at hwd_majDom
      obtain ⟨-, -, hApp_aux⟩ := appChainOk_of_wellDenotedV margsA hwd_majDom
      have hcl_aux := closed_interp_env (mp.base2.acval_closed auxKey ψ_P) (consList (uarVals ++ [t']) ρ₀) ρ₀
      rw [interp_mkAppN_foldl, hmargsV_eq, hcl_aux, ← hnameAux, hAtAux.leafT ψ_P] at hz_mem_maj
      rw [hmargsV_eq, hcl_aux, ← hnameAux, hAtAux.leafT ψ_P] at hApp_aux
      have hokT₀ : WellDenotedV V ρ₀ (mp.base2.acval auxKey ψ_P) :=
        ⟨mp.base2.acval_wellDenoted _ _ _, mp.acval_validV _ _ _⟩
      rw [← hnameAux, hAtAux.leafT ψ_P] at hokT₀
      have hnz_T : ∀ p ∈ ((ppsAll ψ_P).map fun d => (famAux.p.resSort.eval ψ_P + 1, d.2.2)), p.1 ≠ 0 := by
        intro p hp; obtain ⟨d, -, rfl⟩ := List.mem_map.mp hp; omega
      have hfold_T₀ := mkLamsAV_appChainOk_pos
        ((ppsAll ψ_P).map fun d => (famAux.p.resSort.eval ψ_P + 1, d.2.2)) _ (vs_v ++ [t'])
        ρ₀ hnz_T (by simp [hAtAux.former.len ψ_P, hfam_nP, hfam_nIdx, hvs_len]) hokT₀ hApp_aux
      have hsp_allT₀ : SpineFit ρ₀ ((ppsAll ψ_P).map (·.2.2)) (vs_v ++ [t']) := by
        simpa [List.map_map, Function.comp_def] using hfold_T₀.2.1
      have hlen_pT : (((ppsAll ψ_P).take famAux.p.nP).map (·.2.2)).length = vs_v.length := by
        rw [List.length_map, List.length_take, hAtAux.former.len ψ_P, hfam_nP, hvs_len]; omega
      have hsplit_pT : (ppsAll ψ_P).map (·.2.2) =
          ((ppsAll ψ_P).take famAux.p.nP).map (·.2.2) ++ ((ppsAll ψ_P).drop famAux.p.nP).map (·.2.2) := by
        rw [← List.map_append, List.take_append_drop]
      rw [hsplit_pT] at hsp_allT₀
      obtain ⟨hsp_pT₀, hsp_iT₀⟩ := (spineFit_append_iff hlen_pT).mp hsp_allT₀
      have hnat_eq := nativeTyAVI_fold_at hfr.1 hsp_pT₀ hsp_iT₀
      rw [hnat_eq, hIds_len] at hz_mem_maj
      exact ⟨hsp_iT₀, hz_mem_maj⟩
    | _ => simp [Core.posOf, Expr.instantiateLevelParams] at hrem0
  -- 5. Now run `lfpFamSet_induction` on `famAux`'s fixed point!
  let Ids := ((ppsAll ψ_P).drop famAux.p.nP).map (·.2.2)
  let rss := Ix.Kernel.Model.rssOfK ksF famAux.ctorsA.length
  let cds := Ix.Kernel.Model.fixCtorDataList dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0
  let tlss := Ix.Kernel.Model.tlssOfR cds
  let Eiss := Ix.Kernel.Model.eissOfR cds
  let Ess := Ix.Kernel.Model.essOfR cds
  let μ := fixFamI (uAV ψ_P) (famAux.p.resSort.eval ψ_P) (consList vs_v ρ₀) Ids Ids.length rss tlss Eiss (fssZ ψ_P) Ess
  let I := Ix.Kernel.Semantics.idxSet (uAV ψ_P) (consList vs_v ρ₀) Ids
  let Fop := fixFunVI (uAV ψ_P) (famAux.p.resSort.eval ψ_P) (consList vs_v ρ₀) Ids Ids.length rss tlss Eiss (fssZ ψ_P) Ess
  let P : V → V → Prop := fun t_tup y =>
    ∀ t_real : V, t_tup = tupW (uAV ψ_P) [t_real] →
      AppChainOk (interp V ρ₀ (mp.base2.acval auxRecKey ψ_rec_ua)) (uarVals ++ [t_real, y]) →
      (∃ N, Ix.Kernel.SetModel.treeUnpackOpt spec N y =
        some (Ix.Kernel.SetModel.treeUnpack spec y)) ∧
      (uarVals ++ [t_real, y]).foldl SetTheory.app
        (interp V ρ₀ (mp.base2.acval auxRecKey ψ_rec_ua)) =
        Ix.Kernel.SetModel.treeUnpack spec y
  have hX : Ix.Kernel.Semantics.XChainsOk (uAV ψ_P) (famAux.p.resSort.eval ψ_P) (consList vs_v ρ₀)
      Ids rss tlss Eiss (fssZ ψ_P) Ess := hfr.1
  have hind := lfpFamSet_induction (w := famAux.p.resSort.eval ψ_P) (I := I) (F := Fop)
    (fixFunVI_closed_exists hX) (fixFunVI_mono hX) P ?_
  · intro t_tup y ht_mem hy_mem
    have hy_lfp : y ∈ˢ SetTheory.app (lfpFamSet (famAux.p.resSort.eval ψ_P) I Fop) t_tup := by
      change y ∈ˢ SetTheory.app μ t_tup
      have hμ_eq : μ = fixFamI (uAV ψ_P) (famAux.p.resSort.eval ψ_P) (consList vs_v ρ₀)
          Ids 1 rss tlss Eiss (fssZ ψ_P) Ess := by
        simp only [μ]
        rw [hIds_len]
      rw [hμ_eq]
      exact hy_mem
    exact hind t_tup ht_mem y hy_lfp
  -- Inductive step: given `t_tup ∈ˢ I`, `y ∈ˢ app (app Fop S) t_tup`, prove `P t_tup y`!
  intro t_tup ht_mem y hy_step t_real ht_eq hApp_y
  let S := graph (fun i => sep (SetTheory.app (lfpFamSet (famAux.p.resSort.eval ψ_P) I Fop) i) (P i)) I
  have hSmem : S ∈ˢ lfpFamSpace V (famAux.p.resSort.eval ψ_P) I := by
    rw [lfpFamSpace_eq]
    exact graph_mem_famSpace fun i hi => univ_sep_mem (famSpace_app (lfpFamSet_mem _ _ _) hi)
  have hSle : Ix.Kernel.SetTheory.FamLe I S μ := by
    intro i hi z hz
    rw [app_graph hi] at hz
    exact (mem_sep.mp hz).1
  rw [fixFunVI_app hSmem, famFI_app ht_mem] at hy_step
  obtain ⟨k, fs, rfl, hk_lt, hfs_len, hsp_XI, heqAll⟩ := fixStepI_elim hw_aux hy_step
  have hlenZ : (fssZ ψ_P).length = anc := by
    have := hfr.2.1.1; simp [Ix.Kernel.Model.fssOfR, Ix.Kernel.Model.fixCtorDataList_length, hfam_ctors_len] at this
    exact this
  have hk_anc : k < anc := by omega
  obtain ⟨cAk, hcAk⟩ : ∃ cAk, famAux.ctorsA[k]? = some cAk := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  -- `fs` fits `dsF k ψ_P`'s fields and `vs_v ++ fs` fits `dsF k ψ_P`!
  have hgetF : (Ix.Kernel.Model.fssOfR famAux.p.nP cds).getD k [] =
      ((dsF k ψ_P).drop famAux.p.nP).map (·.2.2) := by
    rw [List.getD_eq_getElem?_getD, Ix.Kernel.Model.fssOfR_getElem?,
      Ix.Kernel.Model.fixCtorDataList_getElem? dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0 k, hcAk]
    simp
  have hfit_S := hX.hfit S hSmem t_tup ht_mem k hk_lt
  have hsp_fields : SpineFit (consList vs_v ρ₀) (((dsF k ψ_P).drop famAux.p.nP).map (·.2.2)) fs := by
    have hreal_k := hfr.2.1.2.2.2.2 k (by simp [Ix.Kernel.Model.fssOfR, Ix.Kernel.Model.fixCtorDataList_length]; omega)
    rw [hgetF, hfam_nIdx, ← hIds_len] at hreal_k
    exact spineFit_real_of_XI hX.hI hSle _ _ 0 [] fs rfl hreal_k hfit_S hsp_XI
  have hsp_p_k : SpineFit ρ₀ (((dsF k ψ_P).take famAux.p.nP).map (·.2.2)) vs_v := by
    have hsat_k := (hAtAux.paramsIff k cAk hcAk ψ_P (consList vs_v ρ₀)).mp hsat_p
    have hlenP : (((dsF k ψ_P).take famAux.p.nP).map (·.2.2)).length = vs_v.length := by
      rw [List.length_map, List.length_take, (hAtAux.ctor k cAk hcAk).len ψ_P, hfam_nP, hvs_len]; omega
    exact spineFit_of_sat_consList hlenP hsat_k
  have hfitC : SpineFit ρ₀ ((dsF k (origVal famAux.p.cvT.levelParams ψ_P)).map (·.2.2)) (vs_v ++ fs) := by
    rw [horig_fam]
    have hsplit : (dsF k ψ_P).map (·.2.2) =
        ((dsF k ψ_P).take famAux.p.nP).map (·.2.2) ++ ((dsF k ψ_P).drop famAux.p.nP).map (·.2.2) := by
      rw [← List.map_append, List.take_append_drop]
    rw [hsplit]
    exact hsp_p_k.append hsp_fields
  -- Extract the canonical `rl` and `umw` (matching `unpackSpecOf hminors`!)
  let hex_k := hminors k hk_anc
  let rl := Classical.choose hex_k
  have hrl_k : arules[k]? = some rl := (Classical.choose_spec hex_k).1
  let umw := Classical.choice (Classical.choose_spec hex_k).2
  have hrl_rnf : rl.nfields = umw.rnf := umw.hrnf
  have hfs_len_rnf : fs.length = rl.nfields := by
    have hlen1 := hfr.2.1.2.2.2.1 k (by simp [Ix.Kernel.Model.fssOfR, Ix.Kernel.Model.fixCtorDataList_length]; omega)
    rw [hgetF] at hlen1
    have hlen_cAk : fs.length = cAk.2 := by
      rw [hfs_len, hlen1, List.length_map, List.length_drop, (hAtAux.ctor k cAk hcAk).len ψ_P]; omega
    -- Match `rl.nfields = cAk.2` via `mp.base2.rec_ctors` + `hrecCtor`!
    have hrl_ctor : rl.ctor = cAk.1.name := (hrecCtor k rl hrl_k).trans (hctorNameA k cAk hcAk).symm
    have hc_find := (hreadAux.stored.ctor k cAk hcAk).1
    obtain ⟨⟨cvj, hc_rl, -⟩, -, -⟩ := mp.base2.rec_ctors auxRecKey cvAuxRec
      (nP + 1 + anc + 1) (nP + 1 + anc) arules hfindAuxRec rl (List.mem_of_getElem? hrl_k)
    rw [hrl_ctor, hc_find] at hc_rl
    have hrl_nf_eq := (ConstantInfo.ctorInfo.inj (Option.some.inj hc_rl)).2.2
    omega
  -- 6. Fire `auxRec_fire` on `(uarVals ++ [t_real], vs_v, fs)`!
  obtain ⟨rbodyA, rargsA, -, hrbodyA_eq, hsp_rargs, hfire_eq, hwd_rbody⟩ :=
    auxRec_fire ht hbasis hreg mp hN auxIndWit hauxInd_lvls hauxInd_idx hauxInd_rec hauxInd_sort
      hfindAuxRec hAuxRec_lvls hAuxRec_perm hauxRec_famBlk hAuxRec_maj hrecCtor
      hregAux hnameAux hAtAux hk_anc hrl_k
      (umw.hrnf ▸ umw.hr_strip) ψ_P uarLvls huar_lvls_len huar_lvls_drop (huar_elim_nz ψ_P)
      (uarVals ++ [t_real]) vs_v fs ρ₀
      (by simp [huarVals_len]) hvs_len hfs_len_rnf
      (by rw [List.take_append_of_le_length (by omega)]; exact huarVals_pref)
      hfitC (by simpa [List.append_assoc] using hApp_y)
  have htake_uar : (uarVals ++ [t_real]).take (nP + 1 + anc) = uarVals := by
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  rw [htake_uar] at hfire_eq hwd_rbody
  have hfire_eq' : (uarVals ++ [t_real, inj k (mkTower (fs ++ [pt]))]).foldl SetTheory.app
      (interp V ρ₀ (mp.base2.acval auxRecKey ψ_rec_ua)) =
      interp V (consList (uarVals ++ fs) ρ₀) rbodyA := by
    simpa [List.append_assoc] using hfire_eq
  -- Unpack `rbodyA = mkAppN (.bvar (rnf + anc - 1 - k)) rargsA`!
  rw [hrbodyA_eq] at hfire_eq' hwd_rbody
  obtain ⟨-, hwd_rargs, hApp_min⟩ := appChainOk_of_wellDenotedV rargsA hwd_rbody
  rw [interp_mkAppN_foldl] at hfire_eq'
  have hmin_lookup : interp V (consList (uarVals ++ fs) ρ₀) (.bvar (rl.nfields + anc - 1 - k)) =
      uarVals[nP + 1 + k]'(by omega) := by
    rw [interp_bvar]
    have hidx_eq : rl.nfields + anc - 1 - k = (uarVals ++ fs).length - 1 - (nP + 1 + k) := by
      rw [List.length_append, huarVals_len, hfs_len_rnf]; omega
    rw [hidx_eq, consList_bvar_desc (uarVals ++ fs) ρ₀ (by rw [List.length_append, huarVals_len]; omega)]
    rw [List.getElem_append_left (by omega : nP + 1 + k < uarVals.length)]
  rw [hmin_lookup] at hfire_eq' hApp_min
  let rargsV := rargsA.map (interp V (consList (uarVals ++ fs) ρ₀))
  have hrargsA_len : rargsA.length = umw.rargs.length := by
    have := denoteMetaSpine_length_eq hsp_rargs; simpa using this.symm
  have hrargsV_take : rargsV.take umw.rnf = fs := by
    have hrargs_ge := umw.hrargs_ge
    refine List.ext_getElem (by simp only [rargsV, List.length_take, List.length_map, hrargsA_len, hfs_len_rnf]; omega) fun m hm1 hm2 => ?_
    have hm_rnf : m < umw.rnf := by omega
    have hm_rargs : m < umw.rargs.length := by omega
    rw [List.getElem_take]
    simp only [rargsV, List.getElem_map]
    have hden_m := denoteMetaSpine_getElem hsp_rargs (i := m) (by simp [hm_rargs])
    simp only [List.getElem_map] at hden_m
    have heq_m : ExprSemEq (umw.rargs[m]'hm_rargs) (.bvar (umw.rnf - 1 - m)) := by
      have := forall₂_getElem umw.hrargs_fields m
        (by rw [List.length_take]; omega) (by simp [hm_rnf])
      simpa [List.getElem_take] using this
    have hden_bv : denoteMeta mp.base2.acval env (ψ_rec uarLvls bnl ψ_P) (nP + 1 + anc + rl.nfields)
        (openDummiesP (nP + 1 + anc + rl.nfields) 0 0 (.bvar (umw.rnf - 1 - m))) =
        some (.bvar (umw.rnf - 1 - m)) :=
      denoteMeta_openDummiesP_bvar0 (by omega)
    have hsame := (denoteMeta_exprSemEq (acval := mp.base2.acval) (env := env)
      (φ := ψ_rec uarLvls bnl ψ_P) (d := nP + 1 + anc + rl.nfields)
      (exprSemEq_openDummiesP heq_m (nP + 1 + anc + rl.nfields) 0 0)).symm.trans hden_m
    rw [hden_bv] at hsame
    have ha_eq : rargsA[m]'(by rw [hrargsA_len]; exact hm_rargs) = .bvar (umw.rnf - 1 - m) := (Option.some.inj hsame).symm
    rw [ha_eq, interp_bvar, consList_append]
    rw [show umw.rnf - 1 - m = fs.length - 1 - m by omega]
    exact consList_bvar_desc fs (consList uarVals ρ₀) (by omega)
  let ihV := rargsV.drop umw.rnf
  have hrargsV_split : rargsV = fs ++ ihV := by
    rw [← hrargsV_take, List.take_append_drop]
  -- 7. Denote `minor_k = uarArgs[nP + 1 + k]` via `umw.hmin_strip`!
  have hminor_getD : (uarArgs.drop (nP + 1)).getD k default = uarArgs[nP + 1 + k]'(by omega) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_drop,
      List.getElem?_eq_getElem (by omega : nP + 1 + k < uarArgs.length), Option.getD_some]
  have hden_min : denoteMeta mp.base2.acval env ψ_P nP
      (openDummiesP nP 0 0 ((uarArgs.drop (nP + 1)).getD k default)) =
      some (uarArgsA[nP + 1 + k]'(by omega)) := by
    rw [hminor_getD]
    have h1 := denoteMetaSpine_getElem hsp_uar (i := nP + 1 + k) (by simp [huar_len]; omega)
    simpa only [List.getElem_map] using h1
  have hwd_min : WellDenotedV V (consList vs_v ρ₀) (uarArgsA[nP + 1 + k]'(by omega)) :=
    hwd_uar _ (List.getElem_mem _)
  -- Strip `umw.rnf + (umw.rargs.length - umw.rnf)` lambdas from `openDummiesP nP 0 0 minor_k`!
  have hmin_strip_open : ∃ (mbsO : List (KExpr × BinderMeta)) (hlen : mbsO.length = umw.mbs.length),
      (openDummiesP nP 0 0 ((uarArgs.drop (nP + 1)).getD k default)).stripLams
        (umw.rnf + (umw.rargs.length - umw.rnf)) =
      some (mbsO, openDummiesP nP 0 (umw.rnf + (umw.rargs.length - umw.rnf))
        (Expr.mkAppN (.const umw.mcKey umw.mcLvls) umw.margs)) ∧
      ∀ i (hi : i < umw.mbs.length), (mbsO[i]'(hlen.symm ▸ hi)).2.pw = umw.mbs[i].2.pw := by
    have hgo : ∀ (m d c n : Nat) {e body : KExpr} {bs : List (KExpr × BinderMeta)},
        e.stripLams n = some (bs, body) →
        ∃ (bs' : List (KExpr × BinderMeta)) (hlen : bs'.length = bs.length),
          (openDummiesP m d c e).stripLams n = some (bs', openDummiesP m d (c + n) body) ∧
          ∀ i (hi : i < bs.length), (bs'[i]'(hlen.symm ▸ hi)).2.pw = bs[i].2.pw := by
      intro m
      induction m with
      | zero =>
        intro d c n e body bs hs
        exact ⟨bs, rfl, hs, fun _ _ => rfl⟩
      | succ m ih =>
        intro d c n e body bs hs
        -- Peel one `instantiate1` via `stripLams_instantiate1`, tracking `pw` preservation!
        have h1 : ∀ (v : KExpr) (n c : Nat) {e body : KExpr} {bs : List (KExpr × BinderMeta)},
            e.stripLams n = some (bs, body) →
            ∃ (bs' : List (KExpr × BinderMeta)) (hlen : bs'.length = bs.length),
              (e.instantiate1 v c).stripLams n = some (bs', body.instantiate1 v (c + n)) ∧
              ∀ i (hi : i < bs.length), (bs'[i]'(hlen.symm ▸ hi)).2.pw = bs[i].2.pw := by
          intro v n
          induction n with
          | zero =>
            intro c e body bs hs
            simp only [Expr.stripLams, Option.some.injEq, Prod.mk.injEq] at hs
            obtain ⟨rfl, rfl⟩ := hs
            exact ⟨[], rfl, by simp [Expr.stripLams], fun _ hi => nomatch hi⟩
          | succ n ihn =>
            intro c e body bs hs
            cases e with
            | lam ty b bm =>
              simp only [Expr.stripLams, Option.map_eq_some_iff] at hs
              obtain ⟨⟨bs0, b0⟩, hsb, hp⟩ := hs
              obtain ⟨hbs, hb0⟩ := Prod.mk.inj hp
              subst hb0
              obtain ⟨bs', hlen', hbs', hpw'⟩ := ihn (c + 1) hsb
              refine ⟨(ty.instantiate1 v c, bm) :: bs', by rw [← hbs]; simp [hlen'], ?_, ?_⟩
              · simp only [Expr.instantiate1, Expr.stripLams, hbs', Option.map_some]
                rw [show c + 1 + n = c + (n + 1) by omega]
              · intro i hi
                subst hbs
                cases i with
                | zero => rfl
                | succ i' => exact hpw' i' (by simpa using hi)
            | _ => simp [Expr.stripLams] at hs
        obtain ⟨bs1, hlen1, hbs1, hpw1⟩ := h1 (.fvar d (.sort .zero)) n (c + m) hs
        obtain ⟨bs2, hlen2, hbs2, hpw2⟩ := ih (d + 1) c n hbs1
        refine ⟨bs2, hlen2.trans hlen1, ?_, fun i hi => (hpw2 i (hlen1.symm ▸ hi)).trans (hpw1 i hi)⟩
        simpa [openDummiesP, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbs2
    simpa [Nat.zero_add] using hgo nP 0 0 (umw.rnf + (umw.rargs.length - umw.rnf)) umw.hmin_strip
  obtain ⟨mbsO, hmbsO_len, hmin_stripO, hmbsO_pw⟩ := hmin_strip_open
  obtain ⟨mds, mbodyA, hmin_mk, hmds_len, hmds_bits, hmbodyA_den⟩ :=
    denoteMeta_stripLams (umw.rnf + (umw.rargs.length - umw.rnf)) nP hmin_stripO hden_min
  -- Helper: check `spec[k]?`
  have hspec_get : spec[k]? = some (unpackRuleOf umw) := by
    simp only [spec, unpackSpecOf, List.getElem?_map, List.getElem?_range hk_anc, Option.map_some,
      hk_anc, ↓reduceDIte]
    rfl
  -- 8. Case split on `umw.hbranch` (passthrough vs rebuild)!
  rcases umw.hbranch with
    ⟨hmc_eq, hmbs_pw, hmcLvls, hmargs_len, hmargs_pref, hmargs_fields⟩ | hreb
  · -- **CASE A: PASSTHROUGH (`umw.mcKey = auxCtorKeyAt k`)**
    have hsp_pass : spec[k]? = some .passthrough := by
      rw [hspec_get]; simp only [unpackRuleOf, hmc_eq, ↓reduceDIte]
    have hopt := Ix.Kernel.SetModel.treeUnpackOpt_passthrough (spec := spec) (j := k)
      (mkTower (fs ++ [pt])) (Or.inl hsp_pass)
    have htu := Ix.Kernel.SetModel.treeUnpack_of_opt hopt
    refine ⟨⟨1, by rw [htu]; exact hopt⟩, ?_⟩
    rw [htu, hfire_eq']
    -- Peel all `umw.rnf + (umw.rargs.length - umw.rnf)` positive lambdas of `minor_k`!
    have hmin_val_eq : uarVals[nP + 1 + k]'(by omega) =
        interp V (consList vs_v ρ₀) (mkLamsAV mds mbodyA) := by
      simp only [uarVals, List.getElem_map, hmin_mk]
    rw [hmin_val_eq] at hApp_min ⊢
    rw [hmin_mk] at hwd_min
    have hnz_mds : ∀ p ∈ mds, p.1 ≠ 0 := by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
      have hmbs_len := stripLams_length umw.hmin_strip
      have hbi := map_getElem_eq hmds_bits i hi (by rw [hmbsO_len]; omega)
      have hpwi := hmbsO_pw i (by omega)
      have hnev := hmbs_pw (umw.mbs[i]'(by omega)) (List.getElem_mem _)
      rw [hbi, hpwi, hnev]; simp [pwBit]
    have hrargsV_len : rargsV.length = umw.rnf + (umw.rargs.length - umw.rnf) := by
      have := umw.hrargs_ge; simp [rargsV, hrargsA_len]; omega
    obtain ⟨hfold_min, -, hwd_mbody⟩ := mkLamsAV_appChainOk_pos mds mbodyA rargsV (consList vs_v ρ₀)
      hnz_mds (by rw [hmds_len, hrargsV_len]) hwd_min hApp_min
    rw [hfold_min]
    -- `mbodyA = mkAppN (acval (auxCtorKeyAt k) ψ_P) margsA`!
    rw [show openDummiesP (umw.rnf + (umw.rargs.length - umw.rnf)) nP 0
        (openDummiesP nP 0 (umw.rnf + (umw.rargs.length - umw.rnf))
          (Expr.mkAppN (.const umw.mcKey umw.mcLvls) umw.margs)) =
        openDummiesP (nP + (umw.rnf + (umw.rargs.length - umw.rnf))) 0 0
          (Expr.mkAppN (.const umw.mcKey umw.mcLvls) umw.margs) by
      simpa [Nat.zero_add] using
        (openDummiesP_add nP (umw.rnf + (umw.rargs.length - umw.rnf)) 0
          (Expr.mkAppN (.const umw.mcKey umw.mcLvls) umw.margs)).symm] at hmbodyA_den
    rw [openDummiesP_mkAppN, openDummiesP_const] at hmbodyA_den
    obtain ⟨fmcA, margsA, hfmcA, hsp_margs, hmbodyA_eq⟩ := denoteMeta_mkAppN_inv hmbodyA_den
    have hck_name : cAk.1.name = Core.keyOf t (Core.cprjAddr auxIndWit.ip.block 0 k) :=
      hctorNameA k cAk hcAk
    have hck_find := (hreadAux.stored.ctor k cAk hcAk).1
    rw [hck_name] at hck_find
    rw [hmc_eq] at hfmcA
    simp only [denoteMeta, hck_find, ConstantInfo.toConstantVal] at hfmcA
    have hck_lps : cAk.1.levelParams = List.range bnl := by
      rw [hAtAux.lpsA cAk (List.mem_of_getElem? hcAk), hfam_lps]
    have hmcl_len : umw.mcLvls.length = cAk.1.levelParams.length := by
      have h1 := (lvEqList_getElem hmcLvls).1; rw [hck_lps]; simpa using h1
    simp only [hmcl_len, ↓reduceIte, Option.some.injEq] at hfmcA
    have hfmcA_eq : fmcA = mp.base2.acval cAk.1.name ψ_P := by
      have h1 : fmcA = mp.base2.acval (Core.keyOf t (Core.cprjAddr auxIndWit.ip.block 0 k))
          (Level.substFn ψ_P cAk.1.levelParams umw.mcLvls) := hfmcA.symm
      rw [h1, hck_lps, substFn_eq_of_lvEqList hmcLvls ψ_P, substFn_range_param, hck_name]
    -- Show `margsA` evaluates at `consList rargsV (consList vs_v ρ₀)` to `vs_v ++ fs`!
    have hmargsA_len : margsA.length = nP + umw.rnf := by
      have := denoteMetaSpine_length_eq hsp_margs; simp only [List.length_map, hmargs_len] at this; exact this.symm
    have htot_m : nP + (umw.rnf + (umw.rargs.length - umw.rnf)) = (vs_v ++ rargsV).length := by
      rw [List.length_append, hvs_len, hrargsV_len]
    have hmargsV_eq : margsA.map (interp V (consList rargsV (consList vs_v ρ₀))) = vs_v ++ fs := by
      rw [← consList_append]
      refine List.ext_getElem (by simp [hmargsA_len, hvs_len, hfs_len_rnf, hrl_rnf]) fun i hi1 hi2 => ?_
      have hi_lt : i < nP + umw.rnf := by simp [hmargsA_len] at hi1; exact hi1
      simp only [List.getElem_map]
      have hden_i := denoteMetaSpine_getElem hsp_margs (i := i) (by simp [hmargs_len]; omega)
      simp only [List.getElem_map] at hden_i
      by_cases hiP : i < nP
      · have heq_i : ExprSemEq (umw.margs[i]'(by omega))
            (.bvar (nP + umw.rnf + (umw.rargs.length - umw.rnf) - 1 - i)) := by
          have := forall₂_getElem hmargs_pref i
            (by rw [List.length_take, hmargs_len]; omega) (by simp; omega)
          simpa [List.getElem_take] using this
        have hden_bv : denoteMeta mp.base2.acval env ψ_P (nP + (umw.rnf + (umw.rargs.length - umw.rnf)))
            (openDummiesP (nP + (umw.rnf + (umw.rargs.length - umw.rnf))) 0 0
              (.bvar (nP + umw.rnf + (umw.rargs.length - umw.rnf) - 1 - i))) =
            some (.bvar (nP + umw.rnf + (umw.rargs.length - umw.rnf) - 1 - i)) :=
          denoteMeta_openDummiesP_bvar0 (by omega)
        have hsame := (denoteMeta_exprSemEq (acval := mp.base2.acval) (env := env) (φ := ψ_P)
          (d := nP + (umw.rnf + (umw.rargs.length - umw.rnf)))
          (exprSemEq_openDummiesP heq_i _ 0 0)).symm.trans hden_i
        rw [hden_bv] at hsame
        have ha_eq := (Option.some.inj hsame).symm
        rw [ha_eq, interp_bvar]
        rw [show nP + umw.rnf + (umw.rargs.length - umw.rnf) - 1 - i = (vs_v ++ rargsV).length - 1 - i by omega]
        rw [consList_bvar_desc (vs_v ++ rargsV) ρ₀ (by omega),
          List.getElem_append_left (by omega : i < vs_v.length),
          List.getElem_append_left (by omega : i < vs_v.length)]
      · have hsub_lt : i - nP < umw.rnf := by omega
        have heq_i : ExprSemEq (umw.margs[i]'(by omega))
            (.bvar (umw.rnf + (umw.rargs.length - umw.rnf) - 1 - (i - nP))) := by
          have := forall₂_getElem hmargs_fields (i - nP)
            (by rw [List.length_drop, hmargs_len]; omega) (by simp; omega)
          simp only [List.getElem_drop, List.getElem_map, List.getElem_range] at this
          have hidx_eq : nP + (i - nP) = i := by omega
          simpa [hidx_eq] using this
        have hden_bv : denoteMeta mp.base2.acval env ψ_P (nP + (umw.rnf + (umw.rargs.length - umw.rnf)))
            (openDummiesP (nP + (umw.rnf + (umw.rargs.length - umw.rnf))) 0 0
              (.bvar (umw.rnf + (umw.rargs.length - umw.rnf) - 1 - (i - nP)))) =
            some (.bvar (umw.rnf + (umw.rargs.length - umw.rnf) - 1 - (i - nP))) :=
          denoteMeta_openDummiesP_bvar0 (by omega)
        have hsame := (denoteMeta_exprSemEq (acval := mp.base2.acval) (env := env) (φ := ψ_P)
          (d := nP + (umw.rnf + (umw.rargs.length - umw.rnf)))
          (exprSemEq_openDummiesP heq_i _ 0 0)).symm.trans hden_i
        rw [hden_bv] at hsame
        have ha_eq := (Option.some.inj hsame).symm
        rw [ha_eq, interp_bvar, consList_append]
        rw [show umw.rnf + (umw.rargs.length - umw.rnf) - 1 - (i - nP) = rargsV.length - 1 - (i - nP) by omega]
        rw [consList_bvar_desc rargsV (consList vs_v ρ₀) (by omega)]
        rw [List.getElem_append_right (by omega : vs_v.length ≤ i)]
        have hr_get : rargsV[i - nP]'(by omega) = fs[i - nP]'(by omega) := by
          simp only [hrargsV_split, List.getElem_append_left (by omega : i - nP < fs.length)]
        simpa [hvs_len] using hr_get
    -- Fold `mbodyA = mkAppN (acval cAk.1.name ψ_P) margsA` via `sumMkAV_fold`!
    rw [hmbodyA_eq, hfmcA_eq, interp_mkAppN_foldl, hmargsV_eq]
    have hcl_cAk : interp V (consList rargsV (consList vs_v ρ₀)) (mp.base2.acval cAk.1.name ψ_P) =
        interp V ρ₀ (mp.base2.acval cAk.1.name ψ_P) :=
      closed_interp_env (mp.base2.acval_closed cAk.1.name ψ_P) _ _
    rw [hcl_cAk, hAtAux.leafC k cAk hcAk ψ_P]
    have hokFss : SumFieldsOkB (famAux.p.resSort.eval ψ_P) (consList vs_v ρ₀)
        (Ix.Kernel.Model.fssOfR famAux.p.nP cds) := by
      intro Fs hFs
      obtain ⟨j', hjlt, rfl⟩ := List.mem_iff_getElem.mp hFs
      have hjlt' : j' < famAux.ctorsA.length := by
        simpa [Ix.Kernel.Model.fssOfR, cds, Ix.Kernel.Model.fixCtorDataList_length] using hjlt
      have hget : (Ix.Kernel.Model.fssOfR famAux.p.nP cds).getD j' [] =
          (Ix.Kernel.Model.fssOfR famAux.p.nP cds)[j'] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjlt]
      rw [← hget]; exact (hfr.2.2.1 j' hjlt').1
    have hjU : (Ix.Kernel.Semantics.uChains (Ix.Kernel.Model.fssOfR famAux.p.nP cds))[k]? =
        some (((dsF k ψ_P).drop famAux.p.nP).map (·.2.2) ++ [Ix.Kernel.Semantics.idxEqAV []]) := by
      rw [Ix.Kernel.Semantics.uChains_getElem?, Ix.Kernel.Model.fssOfR_getElem?,
        Ix.Kernel.Model.fixCtorDataList_getElem? dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0 k, hcAk]
      simp
    have hfold := sumMkAV_fold hw_aux hsp_p_k hsp_fields (Ix.Kernel.Semantics.SumFieldsOkB_uChains hokFss) hjU
    rwa [List.take_append_drop] at hfold
  · -- **CASE B: REBUILD (`hreb`)**
    have hrm_ne : Nonempty (UnpackRebuildMatch umw) := by
      obtain ⟨cvMC, cnp, mcIndKey, cvMCI, capsMCI, ini, sortL, cvAuxC, bsP, bsF, remP, remF,
        hmc_ne, hfindMC, hcnp_pos, hmcLvls_len, hmargs_len, hfindMCI, hMCI_lvls, hmc_kind,
        hMCI_sort, hsort_cases, hfindAuxC, hAuxC_P, hAuxC_F, hargWits⟩ := hreb
      exact ⟨⟨cvMC, cnp, mcIndKey, cvMCI, capsMCI, ini, sortL, cvAuxC, bsP, bsF, remP, remF,
        hmc_ne, hfindMC, hcnp_pos, hmcLvls_len, hmargs_len, hfindMCI, hMCI_lvls, hmc_kind,
        hMCI_sort, hsort_cases, hfindAuxC, hAuxC_P, hAuxC_F, hargWits⟩⟩
    let rm := Classical.choice hrm_ne
    have hmc_ne : umw.mcKey ≠ Core.keyOf t (Core.cprjAddr auxIndWit.ip.block 0 k) := rm.hmc_ne
    let cvMC := rm.cvMC; let cnp := rm.cnp; let mcIndKey := rm.mcIndKey
    let cvMCI := rm.cvMCI; let capsMCI := rm.capsMCI; let ini := rm.ini; let sortL := rm.sortL
    let cvAuxC := rm.cvAuxC; let bsP := rm.bsP; let bsF := rm.bsF; let remP := rm.remP; let remF := rm.remF
    have hfindMC := rm.hfindMC; have hcnp_pos := rm.hcnp_pos; have hmcLvls_len := rm.hmcLvls_len
    have hmargs_len := rm.hmargs_len; have hfindMCI := rm.hfindMCI; have hMCI_lvls := rm.hMCI_lvls
    have hmc_kind := rm.hmc_kind; have hMCI_sort := rm.hMCI_sort; have hsort_cases := rm.hsort_cases
    have hfindAuxC := rm.hfindAuxC; have hAuxC_P := rm.hAuxC_P; have hAuxC_F := rm.hAuxC_F
    have hargWits := rm.hargWits
    by_cases hnz : ∀ φ, (substLevel sortL umw.mcLvls).eval φ > 0
    · -- **Subcase B1: non-`Prop` rebuild (`∀ φ, (substLevel sortL umw.mcLvls).eval φ > 0`)**
      have hmbs_nev : ∀ bm ∈ umw.mbs, bm.2.pw = .never := by
        rcases hsort_cases with ⟨-, h1⟩ | ⟨hz, -⟩
        · exact h1
        · have hgt := hnz (fun _ => 0)
          have heq0 : (substLevel sortL umw.mcLvls).eval (fun _ => 0) = 0 := hz (fun _ => 0)
          omega
      by_cases hnat : ∃ cidx, Nonempty (NativeCtorWitness t E env umw.mcKey mcIndKey cidx)
      · -- Standard non-`Prop` native container constructor rebuild!
        set cidx := Classical.choose hnat
        let cwit := Classical.choice (Classical.choose_spec hnat)
        set nIh := umw.rargs.length - umw.rnf
        let recFlags : List Bool := (List.range umw.rnf).map fun l =>
          decide (∃ bv < nIh, (umw.margs.drop cnp).getD l default = .bvar bv)
        have hsp_reb : spec[k]? = some (.rebuild (.sumMk cidx) recFlags) := by
          rw [hspec_get]; unfold unpackRuleOf
          rw [dite_eq_right_of_eq_false (eq_false hmc_ne), dite_eq_left_of_eq_true (eq_true hrm_ne),
            dite_eq_left_of_eq_true (eq_true hnz), dite_eq_left_of_eq_true (eq_true hnat)]
        -- Peel `minor_k`'s `umw.rnf + nIh` positive lambdas!
        have hmin_val_eq : uarVals[nP + 1 + k]'(by omega) =
            interp V (consList vs_v ρ₀) (mkLamsAV mds mbodyA) := by
          simp only [uarVals, List.getElem_map, hmin_mk]
        rw [hmin_val_eq] at hApp_min
        rw [hmin_mk] at hwd_min
        have hnz_mds : ∀ p ∈ mds, p.1 ≠ 0 := by
          intro p hp
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
          have hmbs_len := stripLams_length umw.hmin_strip
          have hbi := map_getElem_eq hmds_bits i hi (by rw [hmbsO_len]; omega)
          have hpwi := hmbsO_pw i (by omega)
          have hnev := hmbs_nev (umw.mbs[i]'(by omega)) (List.getElem_mem _)
          rw [hbi, hpwi, hnev]; simp [pwBit]
        have hrargsV_len : rargsV.length = umw.rnf + nIh := by
          have := umw.hrargs_ge; simp [rargsV, hrargsA_len, nIh]; omega
        obtain ⟨hfold_min, -, hwd_mbody⟩ := mkLamsAV_appChainOk_pos mds mbodyA rargsV (consList vs_v ρ₀)
          hnz_mds (by rw [hmds_len, hrargsV_len]) hwd_min hApp_min
        -- Unpack `mbodyA = mkAppN (acval umw.mcKey ψ_mc) margsA`!
        rw [show openDummiesP (umw.rnf + nIh) nP 0
            (openDummiesP nP 0 (umw.rnf + nIh)
              (Expr.mkAppN (.const umw.mcKey umw.mcLvls) umw.margs)) =
            openDummiesP (nP + (umw.rnf + nIh)) 0 0
              (Expr.mkAppN (.const umw.mcKey umw.mcLvls) umw.margs) by
          simpa [Nat.zero_add] using
            (openDummiesP_add nP (umw.rnf + nIh) 0
              (Expr.mkAppN (.const umw.mcKey umw.mcLvls) umw.margs)).symm] at hmbodyA_den
        rw [openDummiesP_mkAppN, openDummiesP_const] at hmbodyA_den
        obtain ⟨fmcA, margsA, hfmcA, hsp_margs, hmbodyA_eq⟩ := denoteMeta_mkAppN_inv hmbodyA_den
        simp only [denoteMeta, hfindMC, ConstantInfo.toConstantVal, hmcLvls_len, ↓reduceIte, Option.some.injEq] at hfmcA
        let ψ_mc := Level.substFn ψ_P cvMC.levelParams umw.mcLvls
        have hfmcA_eq : fmcA = mp.base2.acval umw.mcKey ψ_mc := hfmcA.symm
        rw [hmbodyA_eq, hfmcA_eq] at hwd_mbody
        obtain ⟨-, -, hApp_mc⟩ := appChainOk_of_wellDenotedV margsA hwd_mbody
        -- Prove `∀ fam, Reg fam → fam.p.cvT.name = mcIndKey → fam.p.resSort.eval ψ_mc ≠ 0`!
        have hmc_sort_nz : ∀ fam, Reg fam → fam.p.cvT.name = mcIndKey → fam.p.resSort.eval ψ_mc ≠ 0 := by
          intro famM hregM hnameM
          have hreadM := hreg.fams famM hregM
          have hcvM_eq : famM.cvS = cvMCI := famRead_cvS_eq hreadM hnameM hfindMCI
          have hstM : StripPisZetaSort (cnp + ini) 0 (Core.posOf famM.cvS.levelParams famM.cvS.type) sortL := by
            rw [hcvM_eq]; exact hMCI_sort
          obtain ⟨-, hlvM⟩ := famRead_resSort_of_stripPisZetaSort mp.base2.wf hreadM hstM
          have hlps_cvMC : cvMC.levelParams = List.range cvMC.levelParams.length := by
            obtain ⟨famC, jC, cAC, hregC, -, hcAC, hcCName, -⟩ :=
              hreg.completeCtor cwit.addr cwit.cm cwit.cp cwit.cv cwit.nP cwit.nF
                (show env.find? (Core.keyOf t cwit.addr) = _ by rw [cwit.hkey]; exact cwit.hfind)
                (show Ix.Kernel.reservedBasisNames.contains (Core.keyOf t cwit.addr) = false by rw [cwit.hkey]; exact cwit.hnotRes)
                cwit.hrec cwit.hinfo cwit.hnat
            have hreadC := hreg.fams famC hregC
            have hfcC := (hreadC.stored.ctor jC cAC hcAC).1
            rw [hcCName.trans cwit.hkey, hfindMC] at hfcC
            have hcvC_eq : cAC.1 = cvMC := ((ConstantInfo.ctorInfo.inj (Option.some.inj hfcC)).1).symm
            obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hAtC⟩ := hN famC hregC
            have hlC := hAtC.lpsA cAC (List.mem_of_getElem? hcAC)
            rw [← hcvC_eq, hlC]
            exact famRead_lps_range hreadC (by rw [← hlC, hcvC_eq])
          have heval_eq : sortL.eval ψ_mc = (substLevel sortL umw.mcLvls).eval ψ_P := by
            rw [eval_substLevel_eq_substFn hmcLvls_len ψ_P sortL]
            dsimp only [ψ_mc]
            conv_lhs => rw [hlps_cvMC]
          rw [← hlvM ψ_mc, heval_eq]
          have := hnz ψ_P; omega
        -- Check `cwit.nP = cnp` and `cwit.nF = umw.rnf`
        have hcwit_eq : cwit.nP = cnp ∧ cwit.nF = umw.rnf := by
          have := Option.some.inj (cwit.hfind.symm.trans hfindMC)
          obtain ⟨-, h1, h2⟩ := ConstantInfo.ctorInfo.inj this
          exact ⟨h1, h2⟩
        have hmargsA_len : margsA.length = cnp + umw.rnf := by
          have := denoteMetaSpine_length_eq hsp_margs; simp only [List.length_map, hmargs_len] at this; exact this.symm
        let margsV := margsA.map (interp V (consList rargsV (consList vs_v ρ₀)))
        have hmc_fold : margsV.foldl SetTheory.app (interp V (consList rargsV (consList vs_v ρ₀))
            (mp.base2.acval umw.mcKey ψ_mc)) =
            inj cidx (mkTower (margsV.drop cnp ++ [pt])) := by
          have h := nativeCtor_fold_pos hreg mp hN cwit hmc_sort_nz
            (by simp [hmargsA_len, hcwit_eq.1, hcwit_eq.2]) hApp_mc
          rwa [hcwit_eq.1] at h
        -- Now prove for EVERY `l < umw.rnf`:
        have hfield_match : ∀ l (hl : l < umw.rnf),
            (recFlags.getD l false = true →
              ∃ n v, Ix.Kernel.SetModel.treeUnpackOpt spec n (projS l (mkTower (fs ++ [pt]))) = some v) ∧
            (margsV.drop cnp)[l]'(by simp [margsV, hmargsA_len]; omega) =
              if recFlags.getD l false then
                Ix.Kernel.SetModel.treeUnpack spec (projS l (mkTower (fs ++ [pt])))
              else projS l (mkTower (fs ++ [pt])) := by
          have hrnf_eq := umw.hrnf
          have hck_name : cAk.1.name = Core.keyOf t (Core.cprjAddr auxIndWit.ip.block 0 k) :=
            hctorNameA k cAk hcAk
          have hfc_aux := (hreadAux.stored.ctor k cAk hcAk).1
          rw [hck_name, hfindAuxC] at hfc_aux
          have hcvAuxC_eq : cvAuxC = cAk.1 := (ConstantInfo.ctorInfo.inj (Option.some.inj hfc_aux)).1
          have hcAk_nf : cAk.2 = umw.rnf := ((ConstantInfo.ctorInfo.inj (Option.some.inj hfc_aux)).2.2).symm
          intro l hl
          have hproj_l : projS l (mkTower (fs ++ [pt])) = fs[l]'(by omega) := by
            have h1 := projS_mkTower_getD (fs := fs) (i := l) (by omega)
            rw [h1, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (by omega : l < fs.length), Option.getD_some]
          have hrec_get : recFlags.getD l false =
              decide (∃ bv < nIh, (umw.margs.drop cnp).getD l default = .bvar bv) := by
            simp [recFlags, List.getD_eq_getElem?_getD, List.getElem?_range hl]
          have harg_getD : (umw.margs.drop cnp).getD l default = umw.margs[cnp + l]'(by omega) := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_drop,
              List.getElem?_eq_getElem (by omega : cnp + l < umw.margs.length), Option.getD_some]
          have hden_l := denoteMetaSpine_getElem hsp_margs (i := cnp + l) (by simp [hmargs_len]; omega)
          simp only [List.getElem_map] at hden_l
          cases hargWits l hl with
          | nonRec harg_bv =>
            have hrf_false : recFlags.getD l false = false := by
              rw [hrec_get, harg_bv, decide_eq_false_iff_not]
              rintro ⟨bv, hbv, heq⟩; injection heq; omega
            simp only [hrf_false, Bool.false_eq_true, ↓reduceIte, hproj_l, false_implies, true_and]
            rw [harg_getD] at harg_bv
            rw [harg_bv] at hden_l
            have hden_bv : denoteMeta mp.base2.acval env ψ_P (nP + (umw.rnf + nIh))
                (openDummiesP (nP + (umw.rnf + nIh)) 0 0 (.bvar (nIh + umw.rnf - 1 - l))) =
                some (.bvar (nIh + umw.rnf - 1 - l)) :=
              denoteMeta_openDummiesP_bvar0 (by omega)
            rw [hden_bv] at hden_l
            have ha_eq : margsA[cnp + l]'(by omega) = .bvar (nIh + umw.rnf - 1 - l) := (Option.some.inj hden_l).symm
            rw [List.getElem_drop]
            simp only [margsV, List.getElem_map]
            rw [ha_eq, interp_bvar]
            rw [show nIh + umw.rnf - 1 - l = rargsV.length - 1 - l by omega]
            rw [consList_bvar_desc rargsV (consList vs_v ρ₀) (by omega)]
            simp only [hrargsV_split, List.getElem_append_left (by omega : l < fs.length)]
          | recField bv ihLvls ihSargs kfLvls kfArgs harg_bv hbv_lt hih_get hih_lvls hih_len
              hih_pref hih_maj hkfdom =>
            have hrf_true : recFlags.getD l false = true := by
              rw [hrec_get, harg_bv, decide_eq_true_eq]; exact ⟨bv, hbv_lt, rfl⟩
            simp only [hrf_true, ↓reduceIte, hproj_l]
            -- Step 1: `(margsV.drop cnp)[l] = ihV[nIh - 1 - bv]`
            rw [harg_getD] at harg_bv
            rw [harg_bv] at hden_l
            have hden_bv : denoteMeta mp.base2.acval env ψ_P (nP + (umw.rnf + nIh))
                (openDummiesP (nP + (umw.rnf + nIh)) 0 0 (.bvar bv)) = some (.bvar bv) :=
              denoteMeta_openDummiesP_bvar0 (by omega)
            rw [hden_bv] at hden_l
            have ha_eq : margsA[cnp + l]'(by omega) = .bvar bv := (Option.some.inj hden_l).symm
            have hmargs_l_eq : (margsV.drop cnp)[l]'(by simp [margsV, hmargsA_len]; omega) =
                ihV[nIh - 1 - bv]'(by simp [ihV, hrargsV_len]; omega) := by
              rw [List.getElem_drop]
              simp only [margsV, List.getElem_map]
              rw [ha_eq, interp_bvar]
              conv_lhs => rw [show bv = rargsV.length - 1 - (umw.rnf + (nIh - 1 - bv)) by omega]
              rw [consList_bvar_desc rargsV (consList vs_v ρ₀) (by omega)]
              simp [ihV]
            -- Step 2: Evaluate `ihV[nIh - 1 - bv]` and get `AppChainOk F_rec (uarVals ++ [t_ih, fs[l]])`!
            have hidx_ih : umw.rnf + (nIh - 1 - bv) < umw.rargs.length := by have := umw.hrargs_ge; omega
            have hih_rargs : umw.rargs[umw.rnf + (nIh - 1 - bv)]'hidx_ih =
                Expr.mkAppN (.const auxRecKey ihLvls) ihSargs := by
              rw [List.getElem?_drop, List.getElem?_eq_getElem hidx_ih] at hih_get
              exact Option.some.inj hih_get
            have hden_ih := denoteMetaSpine_getElem hsp_rargs (i := umw.rnf + (nIh - 1 - bv)) (by simp [hidx_ih])
            simp only [List.getElem_map, hih_rargs, openDummiesP_mkAppN, openDummiesP_const] at hden_ih
            obtain ⟨fihA, ihSargsA, hfihA, hsp_ihS, hihA_eq⟩ := denoteMeta_mkAppN_inv hden_ih
            have hihLvls_len : ihLvls.length = cvAuxRec.levelParams.length := by
              have h1 := (lvEqList_getElem hih_lvls).1; simp only [List.length_map, List.length_range] at h1
              omega
            simp only [denoteMeta, hfindAuxRec, ConstantInfo.toConstantVal, hihLvls_len,
              ↓reduceIte, Option.some.injEq] at hfihA
            have hfihA_eq : fihA = mp.base2.acval auxRecKey ψ_rec_ua := by
              rw [← hfihA, substFn_eq_of_lvEqList hih_lvls (ψ_rec uarLvls bnl ψ_P)]
              refine mp.base2.acval_params auxRecKey _ hfindAuxRec _ _ fun q _ => ?_
              have hpos : Core.posLevels cvAuxRec.levelParams = (List.range (bnl + 1)).map .param := by
                simp [Core.posLevels, hAuxRec_lvls]
              simp only [ψ_rec_ua, origVal, hpos]
            have hwd_ih : WellDenotedV V (consList (uarVals ++ fs) ρ₀)
                (AnnotTerm.mkAppN (mp.base2.acval auxRecKey ψ_rec_ua) ihSargsA) := by
              rw [← hfihA_eq, ← hihA_eq]
              exact hwd_rargs _ (List.getElem_mem _)
            obtain ⟨-, -, hApp_ih_raw⟩ := appChainOk_of_wellDenotedV ihSargsA hwd_ih
            let ihSvals := ihSargsA.map (interp V (consList (uarVals ++ fs) ρ₀))
            have hihSargsA_len : ihSargsA.length = nP + 1 + anc + 2 := by
              have := denoteMetaSpine_length_eq hsp_ihS; simp only [List.length_map, hih_len] at this; exact this.symm
            -- Show `ihSvals = uarVals ++ [ihSvals[nP + 1 + anc], fs[l]]`!
            let t_ih := ihSvals[nP + 1 + anc]'(by simp [ihSvals, hihSargsA_len])
            have hihSvals_eq : ihSvals = uarVals ++ [t_ih, fs[l]'(by omega)] := by
              refine List.ext_getElem (by simp [ihSvals, hihSargsA_len, huarVals_len]) fun m hm1 hm2 => ?_
              by_cases hm_pre : m < nP + 1 + anc
              · simp only [ihSvals, List.getElem_map]
                have hden_m := denoteMetaSpine_getElem hsp_ihS (i := m) (by simp [hih_len]; omega)
                simp only [List.getElem_map] at hden_m
                have heq_m : ExprSemEq (ihSargs[m]'(by omega))
                    (.bvar (nP + 1 + anc + umw.rnf - 1 - m)) := by
                  have := forall₂_getElem hih_pref m
                    (by rw [List.length_take, hih_len]; omega) (by simp; omega)
                  simpa [List.getElem_take] using this
                have hden_bv : denoteMeta mp.base2.acval env (ψ_rec uarLvls bnl ψ_P)
                    (nP + 1 + anc + rl.nfields)
                    (openDummiesP (nP + 1 + anc + rl.nfields) 0 0
                      (.bvar (nP + 1 + anc + umw.rnf - 1 - m))) =
                    some (.bvar (nP + 1 + anc + umw.rnf - 1 - m)) :=
                  denoteMeta_openDummiesP_bvar0 (by rw [hrnf_eq]; omega)
                have hsame := (denoteMeta_exprSemEq (acval := mp.base2.acval) (env := env)
                  (φ := ψ_rec uarLvls bnl ψ_P) (d := nP + 1 + anc + rl.nfields)
                  (exprSemEq_openDummiesP heq_m _ 0 0)).symm.trans hden_m
                rw [hden_bv] at hsame
                have ha_eq := (Option.some.inj hsame).symm
                rw [ha_eq, interp_bvar]
                rw [show nP + 1 + anc + umw.rnf - 1 - m = (uarVals ++ fs).length - 1 - m by
                  rw [List.length_append, huarVals_len, hfs_len_rnf, hrnf_eq]]
                rw [consList_bvar_desc (uarVals ++ fs) ρ₀ (by rw [List.length_append, huarVals_len]; omega),
                  List.getElem_append_left (by omega : m < uarVals.length),
                  List.getElem_append_left (by omega : m < uarVals.length)]
              · by_cases hm_idx : m = nP + 1 + anc
                · subst m
                  rw [List.getElem_append_right (by omega : uarVals.length ≤ nP + 1 + anc)]
                  simp [huarVals_len, t_ih]
                · have hm_maj : m = nP + 1 + anc + 1 := by simp [ihSvals, hihSargsA_len] at hm1; omega
                  subst m
                  rw [List.getElem_append_right (by omega : uarVals.length ≤ nP + 1 + anc + 1)]
                  simp only [huarVals_len, show nP + 1 + anc + 1 - (nP + 1 + anc) = 1 by omega,
                    List.getElem_cons_succ, List.getElem_cons_zero]
                  simp only [ihSvals, List.getElem_map]
                  have hden_m := denoteMetaSpine_getElem hsp_ihS (i := nP + 1 + anc + 1) (by simp [hih_len])
                  simp only [List.getElem_map] at hden_m
                  have hmaj_eq : ihSargs[nP + 1 + anc + 1]'(by omega) = .bvar (umw.rnf - 1 - l) := by
                    rw [List.getElem?_eq_getElem (by omega : nP + 1 + anc + 1 < ihSargs.length)] at hih_maj
                    exact Option.some.inj hih_maj
                  rw [hmaj_eq] at hden_m
                  have hden_bv : denoteMeta mp.base2.acval env (ψ_rec uarLvls bnl ψ_P)
                      (nP + 1 + anc + rl.nfields)
                      (openDummiesP (nP + 1 + anc + rl.nfields) 0 0 (.bvar (umw.rnf - 1 - l))) =
                      some (.bvar (umw.rnf - 1 - l)) :=
                    denoteMeta_openDummiesP_bvar0 (by rw [hrnf_eq]; omega)
                  rw [hden_bv] at hden_m
                  have ha_eq := (Option.some.inj hden_m).symm
                  rw [ha_eq, interp_bvar, consList_append]
                  rw [show umw.rnf - 1 - l = fs.length - 1 - l by omega]
                  exact consList_bvar_desc fs (consList uarVals ρ₀) (by omega)
            have hcl_rec : interp V (consList (uarVals ++ fs) ρ₀) (mp.base2.acval auxRecKey ψ_rec_ua) =
                interp V ρ₀ (mp.base2.acval auxRecKey ψ_rec_ua) :=
              closed_interp_env (mp.base2.acval_closed auxRecKey ψ_rec_ua) _ _
            have hApp_ih : AppChainOk (interp V ρ₀ (mp.base2.acval auxRecKey ψ_rec_ua))
                (uarVals ++ [t_ih, fs[l]'(by omega)]) := by
              rw [← hcl_rec, ← hihSvals_eq]; exact hApp_ih_raw
            have hihV_val : ihV[nIh - 1 - bv]'(by simp [ihV, hrargsV_len]; omega) =
                (uarVals ++ [t_ih, fs[l]'(by omega)]).foldl SetTheory.app
                  (interp V ρ₀ (mp.base2.acval auxRecKey ψ_rec_ua)) := by
              simp only [ihV, rargsV, List.getElem_drop, List.getElem_map]
              rw [hihA_eq, hfihA_eq, interp_mkAppN_foldl, hcl_rec]
              exact congrArg (fun args => args.foldl SetTheory.app (interp V ρ₀ (mp.base2.acval auxRecKey ψ_rec_ua))) hihSvals_eq
            -- Step 3: `(ksF k).getD l .ordinary = .recursive`, so `fitsXI_slot_mem` gives `P t_slot (fs[l])`!
            have hck_lps : cAk.1.levelParams = List.range bnl := by
              rw [hAtAux.lpsA cAk (List.mem_of_getElem? hcAk), hfam_lps]
            have hpos_auxC : Core.posOf cvAuxC.levelParams cvAuxC.type = cAk.1.type := by
              rw [hcvAuxC_eq, hck_lps]
              have hwf_c := mp.base2.wf _ (Ix.Kernel.Semantics.Env.find?_mem (hreadAux.stored.ctor k cAk hcAk).1)
              exact posOf_range_eq bnl cAk.1.type (by rw [← hck_lps]; exact hwf_c.2.1)
            rw [hpos_auxC] at hAuxC_P
            have hks_k : famAux.p.kinds[k]? = some (ksF k) := hAtAux.ks k (by omega)
            have hrec_l : (ksF k).getD l .ordinary = .recursive := by
              have hcls := hreadAux.kinds
              rw [hfam_nP, hfam_nIdx, hnameAux] at hcls
              exact kind_recursive_of_head_eq hcls hcAk hks_k hAuxC_P
                (by rwa [hcAk_nf]) (by omega) hkfdom
            have hrs_l : (rss.getD k []).getD l false = true := by
              simp only [rss, Ix.Kernel.Model.rssOfK_getD (by omega : k < famAux.ctorsA.length)]
              rw [Ix.Kernel.Model.rsOf_getD_iff (by rw [(hAtAux.ctor k cAk hcAk).ksLen]; omega)]
              exact Or.inl hrec_l
            have htl_l : (tlss.getD k []).getD l [] = [] := by
              have htl_k : tlss.getD k [] = tssF k ψ_P := by
                simp only [tlss, cds, List.getD_eq_getElem?_getD, Ix.Kernel.Model.tlssOfR_getElem?,
                  Ix.Kernel.Model.fixCtorDataList_getElem? dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0 k, hcAk]
                simp
              rw [htl_k]
              exact (hAtAux.ctor k cAk hcAk).tssNone ψ_P l (by rw [hrec_l]; exact fun h => nomatch h)
            have hslot := fitsXI_slot_mem hX.hI ((fssZ ψ_P).getD k []) 0 [] fs rfl hfit_S hsp_XI l
              (by omega) (by simpa using hrs_l)
            simp only [Nat.zero_add, List.nil_append, htl_l] at hslot
            obtain ⟨hslotF, hfs_mem_slot⟩ := hslot
            rw [Ix.Kernel.Semantics.slotSet_nil] at hfs_mem_slot
            obtain ⟨-, hvsp_slot⟩ := hslotF.2.2 [] trivial
            simp only [List.append_nil] at hvsp_slot
            let slotVals := ((Eiss.getD k []).getD l []).map (interp V (consList (fs.take l) (consList vs_v ρ₀)))
            let t_slot := tupW (uAV ψ_P) slotVals
            have ht_slot_mem : t_slot ∈ˢ I := Ix.Kernel.Semantics.tupW_mem hvsp_slot
            rw [app_graph ht_slot_mem, mem_sep] at hfs_mem_slot
            have hfs_getD : fs.getD l pt = fs[l]'(by omega) := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : l < fs.length), Option.getD_some]
            rw [hfs_getD] at hfs_mem_slot
            -- Step 4: `aux_fibre_disjoint` identifies `t_slot = tupW (uAV ψ_P) [t_ih]`!
            obtain ⟨hsp_ih, hfs_mem_ih⟩ := hmem_aux_of_appRec t_ih (fs[l]'(by omega)) hApp_ih
            have hfs_mem_slot_μ : fs[l]'(by omega) ∈ˢ SetTheory.app μ t_slot := hfs_mem_slot.1
            have hslotVals_len : slotVals.length = 1 := hvsp_slot.length_eq.trans hIds_len
            obtain ⟨t_s, hslotVals_eq⟩ : ∃ t_s, slotVals = [t_s] := by
              cases hsv : slotVals with
              | nil => rw [hsv] at hslotVals_len; cases hslotVals_len
              | cons a r =>
                cases r with
                | cons _ _ => rw [hsv] at hslotVals_len; simp at hslotVals_len
                | nil => exact ⟨a, rfl⟩
            have ht_s_eq : t_s = t_ih :=
              aux_fibre_disjoint hw_aux hX
                (by
                  intro j' hj'
                  have hj_lt : j' < famAux.ctorsA.length := by rw [hfam_ctors_len]; rw [hlenZ] at hj'; omega
                  obtain ⟨cAj', hcAj'⟩ : ∃ c, famAux.ctorsA[j']? = some c := ⟨_, List.getElem?_eq_getElem hj_lt⟩
                  have hej : Ess.getD j' [] = esF j' ψ_P := by
                    simp only [Ess, cds, List.getD_eq_getElem?_getD, Ix.Kernel.Model.essOfR_getElem?,
                      Ix.Kernel.Model.fixCtorDataList_getElem? dsF esF ksF eissF tssF ψ_P famAux.ctorsA 0 j', hcAj']
                    simp
                  rw [hej, (hAtAux.ctor j' cAj' hcAj').lenE ψ_P, hfam_nIdx, hIds_len])
                hIds_len (hslotVals_eq ▸ hvsp_slot) hsp_ih
                (by
                  have hμ_fix : μ = fixFamI (uAV ψ_P) (famAux.p.resSort.eval ψ_P) (consList vs_v ρ₀)
                      Ids 1 rss tlss Eiss (fssZ ψ_P) Ess := by
                    dsimp only [μ]
                    rw [hIds_len]
                  rw [← hslotVals_eq]
                  change fs[l]'(by omega) ∈ˢ SetTheory.app _ t_slot
                  rwa [← hμ_fix])
                (by simpa only [Ids, List.map_drop] using hfs_mem_ih)
            have ht_eq_slot : t_slot = tupW (uAV ψ_P) [t_ih] := by
              simp only [t_slot, hslotVals_eq, ht_s_eq]
            -- Step 5: Fire IH `P t_slot (fs[l])`!
            obtain ⟨⟨N_l, hopt_l⟩, heval_l⟩ := hfs_mem_slot.2 t_ih ht_eq_slot hApp_ih
            refine ⟨fun _ => ⟨N_l, _, hopt_l⟩, ?_⟩
            rw [hmargs_l_eq, hihV_val, heval_l]
        -- Apply `treeUnpackOpt_rebuild` and combine!
        have hrecFlags_len : recFlags.length = umw.rnf := by simp [recFlags]
        have hall_reb : ∀ l (hl : l < recFlags.length), recFlags[l] = true →
            ∃ n v, Ix.Kernel.SetModel.treeUnpackOpt spec n (projS l (mkTower (fs ++ [pt]))) = some v := by
          intro l hl htrue
          have hl' : l < umw.rnf := by omega
          have hget : recFlags.getD l false = true := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]; exact htrue
          exact (hfield_match l hl').1 hget
        obtain ⟨N, hopt⟩ := Ix.Kernel.SetModel.treeUnpackOpt_rebuild (mkTower (fs ++ [pt])) hsp_reb hall_reb
        have hlist_eq : ((List.range recFlags.length).map fun l =>
            if recFlags.getD l false then
              Ix.Kernel.SetModel.treeUnpack spec (projS l (mkTower (fs ++ [pt])))
            else projS l (mkTower (fs ++ [pt]))) = margsV.drop cnp := by
          refine List.ext_getElem (by simp [hrecFlags_len, margsV, hmargsA_len]) fun l hl1 hl2 => ?_
          simp only [List.getElem_map, List.getElem_range]
          exact ((hfield_match l (by simp [hrecFlags_len] at hl1; exact hl1)).2).symm
        rw [hlist_eq] at hopt
        have htu := Ix.Kernel.SetModel.treeUnpack_of_opt hopt
        refine ⟨⟨N + 1, by rw [htu]; exact hopt⟩, ?_⟩
        rw [htu, hfire_eq', hmin_val_eq, hfold_min, hmbodyA_eq, hfmcA_eq, interp_mkAppN_foldl]
        exact hmc_fold
      · -- `hnz` holds AND `¬ hnat`: MUST be `.inl` (`eqReflName`) in `hmc_kind`!
        rcases hmc_kind with ⟨heqR, hrnf0, hfeq, hfeqR⟩ | hnat'
        · have hsp_prop : spec[k]? = some (.rebuild .propMk []) := by
            rw [hspec_get]; unfold unpackRuleOf
            rw [dite_eq_right_of_eq_false (eq_false hmc_ne), dite_eq_left_of_eq_true (eq_true hrm_ne),
              dite_eq_left_of_eq_true (eq_true hnz), dite_eq_right_of_eq_false (eq_false hnat)]
          obtain ⟨N, hopt⟩ := Ix.Kernel.SetModel.treeUnpackOpt_rebuild (mkTower (fs ++ [pt])) hsp_prop
            (fun _ hl => nomatch hl)
          have htu := Ix.Kernel.SetModel.treeUnpack_of_opt hopt
          refine ⟨⟨N + 1, by rw [htu]; exact hopt⟩, ?_⟩
          rw [htu, hfire_eq']
          have hmin_val_eq : uarVals[nP + 1 + k]'(by omega) =
              interp V (consList vs_v ρ₀) (mkLamsAV mds mbodyA) := by
            simp only [uarVals, List.getElem_map, hmin_mk]
          rw [hmin_val_eq] at hApp_min ⊢
          rw [hmin_mk] at hwd_min
          have hnz_mds : ∀ p ∈ mds, p.1 ≠ 0 := by
            intro p hp
            obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
            have hmbs_len := stripLams_length umw.hmin_strip
            have hbi := map_getElem_eq hmds_bits i hi (by rw [hmbsO_len]; omega)
            have hpwi := hmbsO_pw i (by omega)
            have hnev := hmbs_nev (umw.mbs[i]'(by omega)) (List.getElem_mem _)
            rw [hbi, hpwi, hnev]; simp [pwBit]
          have hrargsV_len : rargsV.length = umw.rnf + (umw.rargs.length - umw.rnf) := by
            have := umw.hrargs_ge; simp [rargsV, hrargsA_len]; omega
          obtain ⟨hfold_min, -, -⟩ := mkLamsAV_appChainOk_pos mds mbodyA rargsV (consList vs_v ρ₀)
            hnz_mds (by rw [hmds_len, hrargsV_len]) hwd_min hApp_min
          rw [hfold_min]
          rw [show openDummiesP (umw.rnf + (umw.rargs.length - umw.rnf)) nP 0
              (openDummiesP nP 0 (umw.rnf + (umw.rargs.length - umw.rnf))
                (Expr.mkAppN (.const umw.mcKey umw.mcLvls) umw.margs)) =
              openDummiesP (nP + (umw.rnf + (umw.rargs.length - umw.rnf))) 0 0
                (Expr.mkAppN (.const umw.mcKey umw.mcLvls) umw.margs) by
            simpa [Nat.zero_add] using
              (openDummiesP_add nP (umw.rnf + (umw.rargs.length - umw.rnf)) 0
                (Expr.mkAppN (.const umw.mcKey umw.mcLvls) umw.margs)).symm,
            openDummiesP_mkAppN, openDummiesP_const] at hmbodyA_den
          obtain ⟨fmcA, margsA, hfmcA, -, hmbodyA_eq⟩ := denoteMeta_mkAppN_inv hmbodyA_den
          simp only [denoteMeta, hfindMC, ConstantInfo.toConstantVal, hmcLvls_len, ↓reduceIte, Option.some.injEq] at hfmcA
          rw [hmbodyA_eq, ← hfmcA, heqR]
          exact eqRefl_interp_pt mp hfeq hfeqR
            (Level.substFn ψ_P cvMC.levelParams umw.mcLvls) (consList rargsV (consList vs_v ρ₀)) margsA
        · exact absurd hnat' hnat
    · -- **Subcase B2: `Prop` rebuild (`¬ ∀ φ, (substLevel sortL umw.mcLvls).eval φ > 0`)**
      have hsp_prop : spec[k]? = some (.rebuild .propMk []) := by
        rw [hspec_get]; unfold unpackRuleOf
        rw [dite_eq_right_of_eq_false (eq_false hmc_ne), dite_eq_left_of_eq_true (eq_true hrm_ne),
          dite_eq_right_of_eq_false (eq_false hnz)]
      have hprop_branch : (∀ φ, (substLevel sortL umw.mcLvls).eval φ = 0) ∧
          ∀ bm ∈ umw.mbs, bm.2.pw = .ifAllZero [] := by
        rcases hsort_cases with ⟨h1, -⟩ | h2
        · exact absurd h1 hnz
        · exact h2
      obtain ⟨N, hopt⟩ := Ix.Kernel.SetModel.treeUnpackOpt_rebuild (mkTower (fs ++ [pt])) hsp_prop
        (fun _ hl => nomatch hl)
      have htu := Ix.Kernel.SetModel.treeUnpack_of_opt hopt
      refine ⟨⟨N + 1, by rw [htu]; exact hopt⟩, ?_⟩
      rw [htu, hfire_eq']
      have hmin_val_eq : uarVals[nP + 1 + k]'(by omega) =
          interp V (consList vs_v ρ₀) (mkLamsAV mds mbodyA) := by
        simp only [uarVals, List.getElem_map, hmin_mk]
      rw [hmin_val_eq]
      cases hmds_c : mds with
      | cons d0 mds' =>
        -- Nonempty λ-prefix with `d0.1 = 0` → `mkLamsAV_zero_head_foldl` gives `pt`!
        have hd0_zero : d0.1 = 0 := by
          have h0_lt : 0 < umw.mbs.length := by
            have h1 := hmds_len; rw [hmds_c] at h1
            have h2 := stripLams_length umw.hmin_strip
            simp only [List.length_cons] at h1; omega
          have hb0 := map_getElem_eq hmds_bits 0 (by rw [hmds_c]; simp) (by rw [hmbsO_len]; exact h0_lt)
          simp only [hmds_c, List.getElem_cons_zero] at hb0
          have hpw0 := hmbsO_pw 0 h0_lt
          have hzero0 := hprop_branch.2 (umw.mbs[0]'h0_lt) (List.getElem_mem _)
          rw [hb0, hpw0, hzero0]; simp [pwBit]
        rcases d0 with ⟨v0, A0⟩
        simp only at hd0_zero; subst hd0_zero
        exact mkLamsAV_zero_head_foldl (consList vs_v ρ₀) rargsV
      | nil =>
        -- Zero lambdas (`rnf = 0, nIh = 0`): `minor_k = mkAppN (.const mcKey mcLvls) margs`!
        have hrargs_nil : rargsV = [] := by
          have hlen_z : umw.rnf + (umw.rargs.length - umw.rnf) = 0 := by
            rw [← hmds_len, hmds_c]; rfl
          have : rargsV.length = 0 := by
            have := umw.hrargs_ge; simp only [rargsV, List.length_map, hrargsA_len]; omega
          exact List.eq_nil_of_length_eq_zero this
        change rargsV.foldl SetTheory.app _ = _
        rw [hrargs_nil, List.foldl_nil, mkLamsAV]
        rw [show openDummiesP (umw.rnf + (umw.rargs.length - umw.rnf)) nP 0
            (openDummiesP nP 0 (umw.rnf + (umw.rargs.length - umw.rnf))
              (Expr.mkAppN (.const umw.mcKey umw.mcLvls) umw.margs)) =
            openDummiesP (nP + (umw.rnf + (umw.rargs.length - umw.rnf))) 0 0
              (Expr.mkAppN (.const umw.mcKey umw.mcLvls) umw.margs) by
          simpa [Nat.zero_add] using
            (openDummiesP_add nP (umw.rnf + (umw.rargs.length - umw.rnf)) 0
              (Expr.mkAppN (.const umw.mcKey umw.mcLvls) umw.margs)).symm,
          openDummiesP_mkAppN, openDummiesP_const] at hmbodyA_den
        obtain ⟨fmcA, margsA, hfmcA, -, hmbodyA_eq⟩ := denoteMeta_mkAppN_inv hmbodyA_den
        simp only [denoteMeta, hfindMC, ConstantInfo.toConstantVal, hmcLvls_len,
          ↓reduceIte, Option.some.injEq] at hfmcA
        let ψ_mc := Level.substFn ψ_P cvMC.levelParams umw.mcLvls
        rw [hmbodyA_eq, ← hfmcA]
        rcases hmc_kind with ⟨heqR, -, hfeq, hfeqR⟩ | ⟨cidx, ⟨cwit⟩⟩
        · rw [heqR]
          exact eqRefl_interp_pt mp hfeq hfeqR ψ_mc (consList vs_v ρ₀) margsA
        · rw [interp_mkAppN_foldl]
          refine nativeCtor_fold_zero hreg mp hN cwit _ fun famM hregM hnameM => ?_
          have hreadM := hreg.fams famM hregM
          have hcvM_eq : famM.cvS = cvMCI := famRead_cvS_eq hreadM hnameM hfindMCI
          have hstM : StripPisZetaSort (cnp + ini) 0 (Core.posOf famM.cvS.levelParams famM.cvS.type) sortL := by
            rw [hcvM_eq]; exact hMCI_sort
          obtain ⟨-, hlvM⟩ := famRead_resSort_of_stripPisZetaSort mp.base2.wf hreadM hstM
          have hlps_cvMC : cvMC.levelParams = List.range cvMC.levelParams.length := by
            obtain ⟨famC, jC, cAC, hregC, -, hcAC, hcCName, -⟩ :=
              hreg.completeCtor cwit.addr cwit.cm cwit.cp cwit.cv cwit.nP cwit.nF
                (show env.find? (Core.keyOf t cwit.addr) = _ by rw [cwit.hkey]; exact cwit.hfind)
                (show Ix.Kernel.reservedBasisNames.contains (Core.keyOf t cwit.addr) = false by rw [cwit.hkey]; exact cwit.hnotRes)
                cwit.hrec cwit.hinfo cwit.hnat
            have hreadC := hreg.fams famC hregC
            have hfcC := (hreadC.stored.ctor jC cAC hcAC).1
            rw [hcCName.trans cwit.hkey, hfindMC] at hfcC
            have hcvC_eq : cAC.1 = cvMC := ((ConstantInfo.ctorInfo.inj (Option.some.inj hfcC)).1).symm
            obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hAtC⟩ := hN famC hregC
            have hlC := hAtC.lpsA cAC (List.mem_of_getElem? hcAC)
            rw [← hcvC_eq, hlC]
            exact famRead_lps_range hreadC (by rw [← hlC, hcvC_eq])
          have heval_eq : sortL.eval ψ_mc = (substLevel sortL umw.mcLvls).eval ψ_P := by
            rw [eval_substLevel_eq_substFn hmcLvls_len ψ_P sortL]
            dsimp only [ψ_mc]
            conv_lhs => rw [hlps_cvMC]
          rw [← hlvM ψ_mc, heval_eq]
          exact hprop_branch.1 ψ_P

end IxVM.Refinement.Typing.FamilyAlias
