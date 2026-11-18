import IxVMRefinement.Binding.FamilyRecon
import IxVMRefinement.Binding.FamilyFlatLocal

/-! # The reconstruction reads only a closed set of addresses

`recTypeAt` and `ruleBodiesAt` read a store through a `ReconView`: the inductive types at the
flattened family's entries (their types, counts, blocks), the constructors of those blocks, and the
definitions that head normalization unfolds at the head constants of the terms it normalizes.
Every answer is `none` where a load fails, so a view that answers as the first wherever the first
answers, on a set of addresses closed under what is read (`ReconView.ClosedOn`), reconstructs the
same (`recTypeAt_leOn`, `ruleBodiesAt_leOn`).

* `RKeysAt`, `REntryAt`, `ReconView.LeOn`, `ReconView.ClosedOn`;
* the keys of the terms normalized stay in the set (`isForall_keys`, `lamBody_keys`, the keys of
  an instantiation, a lift, a level instantiation, a substituted parameter);
* `headStep_leOn`, `hnf_leOn`, `binderOf_leOn`, `collectDoms_leOn`, `peelMotiveParams_keys`,
  `peelCtorParams_leOn`, `whnfTele_leOn`, `isRecField_congr`, `fieldsClassify_leOn`,
  `minorAt_leOn`, `minorDoms_leOn`, `allMinors_leOn`, `motiveType_leOn`, `allMotives_leOn`,
  `flatOwnParams_leOn`, `ctorsBefore_leOn`, **`recTypeAt_leOn`**, `applyIhs_congr`,
  `ruleBody_leOn`, `ruleBodies_leOn`, **`ruleBodiesAt_leOn`**. -/

namespace IxVM.Refinement.Binding.FamilyRecon

open IxVM.Consistency
open IxVM.Refinement.Binding.FamilyFlat
open IxVM.Refinement.Core (KExpr KLevel KKey bmeta ExprLvEq)

set_option linter.unusedVariables false

/-! ## A view that answers as the first on a closed set -/

/-- **Every key of the term names, through the view, an address of `S`.** -/
abbrev RKeysAt (V : ReconView) (S : _root_.Address → Prop) (e : KExpr) : Prop :=
  ∀ k, KeyIn k e → ∀ a, V.addr k = some a → S a

/-- **An entry at an address of `S`, whose parameters' keys name addresses of `S`.** -/
structure REntryAt (V : ReconView) (S : _root_.Address → Prop) (e : FlatEntry) : Prop where
  addr : S e.addr
  params : ∀ p ∈ e.params, RKeysAt V S p

/-- **`V'` answers as `V` wherever `V` answers at the addresses of `S`**, and reads keys and
constructor addresses alike. -/
structure ReconView.LeOn (S : _root_.Address → Prop) (V V' : ReconView) : Prop where
  ind : ∀ a x, S a → V.ind a = some x → V'.ind a = some x
  ctor : ∀ b i c x, S b → V.ctor b i c = some x → V'.ctor b i c = some x
  ctorAddr : V'.ctorAddr = V.ctorAddr
  key : V'.key = V.key
  addr : V'.addr = V.addr
  unfold : ∀ k us x, (∀ a, V.addr k = some a → S a) → V.unfold k us = some x →
    V'.unfold k us = some x

/-- **What `V` answers at the addresses of `S` stays in `S`**: an inductive type's block, the keys
of an inductive's type, of a constructor's type and of a definition's value. -/
structure ReconView.ClosedOn (S : _root_.Address → Prop) (V : ReconView) : Prop where
  indBlk : ∀ a i, S a → V.ind a = some i → S i.blk
  indTy : ∀ a i, S a → V.ind a = some i → RKeysAt V S i.ty
  ctorTy : ∀ b i c ty np, S b → V.ctor b i c = some (ty, np) → RKeysAt V S ty
  unfold : ∀ k us v, (∀ a, V.addr k = some a → S a) → V.unfold k us = some (some v) →
    RKeysAt V S v

section Keys

variable {V : ReconView} {S : _root_.Address → Prop}

theorem rk_inst1Lift {b a : KExpr} (hb : RKeysAt V S b) (ha : RKeysAt V S a) :
    RKeysAt V S (Ix.Kernel.Expr.instantiate1Lift b a 0) := fun k hk =>
  (keyIn_instantiate1Lift a b 0 hk).elim (hb k) (ha k)

theorem rk_lift {e : KExpr} (n c : Nat) (h : RKeysAt V S e) :
    RKeysAt V S (e.liftLooseBVars n c) :=
  fun k hk => h k (keyIn_liftLooseBVars n e c hk)

theorem rk_ilp {e : KExpr} (ks : List Ix.Kernel.LevelParam) (us : List KLevel)
    (h : RKeysAt V S e) : RKeysAt V S (e.instantiateLevelParams ks us) :=
  fun k hk => h k (keyIn_instantiateLevelParams e hk)

theorem rk_bvar (i : Nat) : RKeysAt V S (.bvar i) := fun k hk => by cases hk

theorem isForall_keys {e d b : KExpr} {m : Ix.Kernel.BinderMeta}
    (h : isForall e = some (d, b, m)) (hk : RKeysAt V S e) : RKeysAt V S d ∧ RKeysAt V S b := by
  cases e <;> simp [isForall] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨fun k h' => hk k (.allTy h'), fun k h' => hk k (.allBody h')⟩

theorem lamBody_keys {e b : KExpr} (h : lamBody e = some b) (hk : RKeysAt V S e) :
    RKeysAt V S b := by
  cases e <;> simp [lamBody] at h
  subst h
  exact fun k h' => hk k (.lamBody h')

theorem rk_substParamFor {j nrp : Nat} {aux : Bool} {sp : List KExpr}
    (hsp : ∀ p ∈ sp, RKeysAt V S p) : RKeysAt V S (substParamFor j nrp aux sp) := by
  unfold substParamFor
  cases aux with
  | false => exact rk_bvar _
  | true =>
    cases hj : sp[j]? with
    | none => exact rk_bvar _
    | some s => exact hsp s (List.mem_of_getElem? hj)

theorem rk_ctorSubstParamFor {j depth specLift : Nat} {aux : Bool} {sp : List KExpr}
    (hsp : ∀ p ∈ sp, RKeysAt V S p) :
    RKeysAt V S (ctorSubstParamFor j depth specLift aux sp) := by
  unfold ctorSubstParamFor
  cases aux with
  | false => exact rk_bvar _
  | true =>
    cases hj : sp[j]? with
    | none => exact rk_bvar _
    | some s => exact rk_lift _ _ (hsp s (List.mem_of_getElem? hj))

end Keys

/-! ## Head normalization -/

section LeOn

variable {S : _root_.Address → Prop} {V V' : ReconView}

theorem headStep_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) :
    ∀ (e : KExpr) (x : Option KExpr), RKeysAt V S e → headStep V e = some x →
      headStep V' e = some x ∧ ∀ e', x = some e' → RKeysAt V S e' := by
  intro e
  induction e with
  | const k us =>
    intro x hK h
    simp only [headStep] at h ⊢
    have hk : ∀ a, V.addr k = some a → S a := hK k (.const _)
    exact ⟨hV.unfold k us x hk h, fun e' he' => hC.unfold k us e' hk (he' ▸ h)⟩
  | app f a ihf iha =>
    intro x hK h
    simp only [headStep] at h ⊢
    cases hl : lamBody f with
    | some b =>
      simp only [hl, Option.some.injEq] at h ⊢
      subst h
      refine ⟨rfl, fun e' he' => ?_⟩
      simp only [Option.some.injEq] at he'
      subst he'
      exact rk_inst1Lift (lamBody_keys hl fun k hk => hK k (.appFn hk))
        fun k hk => hK k (.appArg hk)
    | none =>
      simp only [hl] at h ⊢
      cases hf : headStep V f with
      | none => simp [hf] at h
      | some y =>
        obtain ⟨hf', hky⟩ := ihf y (fun k hk => hK k (.appFn hk)) hf
        rw [hf']
        rw [hf, Option.map_some, Option.some.injEq] at h
        subst h
        refine ⟨rfl, fun e' he' => ?_⟩
        cases y with
        | none => simp at he'
        | some f' =>
          simp only [Option.map_some, Option.some.injEq] at he'
          subst he'
          intro k hk a' ha'
          cases hk with
          | appFn h1 => exact hky f' rfl k h1 a' ha'
          | appArg h1 => exact hK k (.appArg h1) a' ha'
  | bvar i =>
    intro x _ h
    simp [headStep] at h
    subst h
    simp [headStep]
  | fvar i ty _ =>
    intro x _ h
    simp [headStep] at h
    subst h
    simp [headStep]
  | sort u =>
    intro x _ h
    simp [headStep] at h
    subst h
    simp [headStep]
  | lam t b m _ _ =>
    intro x _ h
    simp [headStep] at h
    subst h
    simp [headStep]
  | forallE t b m _ _ =>
    intro x _ h
    simp [headStep] at h
    subst h
    simp [headStep]
  | letE t v b l _ _ _ =>
    intro x _ h
    simp [headStep] at h
    subst h
    simp [headStep]
  | lit l =>
    intro x _ h
    simp [headStep] at h
    subst h
    simp [headStep]
  | proj s i e _ =>
    intro x _ h
    simp [headStep] at h
    subst h
    simp [headStep]

theorem hnf_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) :
    ∀ (n : Nat) (e r : KExpr), RKeysAt V S e → hnf V n e = some r →
      hnf V' n e = some r ∧ RKeysAt V S r := by
  intro n
  induction n with
  | zero => intro e r _ h; simp [hnf] at h
  | succ n ih =>
    intro e r hK h
    cases hs : headStep V e with
    | none => simp [hnf, hs] at h
    | some x =>
      obtain ⟨hs', hk⟩ := headStep_leOn hV hC e x hK hs
      cases x with
      | none =>
        simp only [hnf, hs, hs', Option.some.injEq] at h ⊢
        subst h
        exact ⟨rfl, hK⟩
      | some e' =>
        simp only [hnf, hs, hs'] at h ⊢
        exact ih e' r (hk e' rfl) h

theorem binderOf_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) (f : Nat) (ty : KExpr)
    (x : Option (KExpr × KExpr × Ix.Kernel.BinderMeta)) (hK : RKeysAt V S ty)
    (h : binderOf V f ty = some x) :
    binderOf V' f ty = some x ∧
      ∀ d b m, x = some (d, b, m) → RKeysAt V S d ∧ RKeysAt V S b := by
  unfold binderOf at h ⊢
  cases hi : isForall ty with
  | some p =>
    simp only [hi, Option.some.injEq] at h ⊢
    subst h
    refine ⟨rfl, fun d b m hp => ?_⟩
    simp only [Option.some.injEq] at hp
    subst hp
    exact isForall_keys hi hK
  | none =>
    simp only [hi] at h ⊢
    cases hh : hnf V f ty with
    | none => simp [hh] at h
    | some w =>
      obtain ⟨hh', hkw⟩ := hnf_leOn hV hC f ty w hK hh
      rw [hh, Option.map_some, Option.some.injEq] at h
      rw [hh', Option.map_some, Option.some.injEq]
      subst h
      exact ⟨rfl, fun d b m hp => isForall_keys hp hkw⟩

theorem collectDoms_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) (f : Nat) :
    ∀ (n : Nat) (ty : KExpr) (r : List KExpr × KExpr), RKeysAt V S ty →
      collectDoms V f n ty = some r → collectDoms V' f n ty = some r := by
  intro n
  induction n with
  | zero => intro ty r _ h; simpa only [collectDoms] using h
  | succ n ih =>
    intro ty r hK h
    cases hb : binderOf V f ty with
    | none => simp [collectDoms, hb] at h
    | some x =>
      obtain ⟨hb', hk⟩ := binderOf_leOn hV hC f ty x hK hb
      cases x with
      | none =>
        simp only [collectDoms, hb, hb'] at h ⊢
        exact h
      | some p =>
        obtain ⟨d, b, m⟩ := p
        simp only [collectDoms, hb, hb'] at h ⊢
        cases hc : collectDoms V f n b with
        | none => simp [hc] at h
        | some q =>
          rw [ih b q (hk d b m rfl).2 hc]
          rw [hc] at h
          exact h

/-! ## Parameters and fields -/

theorem peelMotiveParams_keys {nrp : Nat} {aux : Bool} {sp : List KExpr}
    (hsp : ∀ p ∈ sp, RKeysAt V S p) :
    ∀ (n j : Nat) (ty r : KExpr), RKeysAt V S ty → peelMotiveParams nrp aux sp n j ty = some r →
      RKeysAt V S r := by
  intro n
  induction n with
  | zero =>
    intro j ty r hK h
    simp only [peelMotiveParams, Option.some.injEq] at h
    subst h
    exact hK
  | succ n ih =>
    intro j ty r hK h
    simp only [peelMotiveParams] at h
    cases hi : isForall ty with
    | none => simp [hi] at h
    | some p =>
      obtain ⟨d, b, m⟩ := p
      simp only [hi] at h
      exact ih (j + 1) _ r (rk_inst1Lift (isForall_keys hi hK).2 (rk_substParamFor hsp)) h

theorem peelCtorParams_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) {f depth specLift : Nat}
    {aux : Bool} {sp : List KExpr} (hsp : ∀ p ∈ sp, RKeysAt V S p) :
    ∀ (n j : Nat) (ty r : KExpr), RKeysAt V S ty →
      peelCtorParams V f depth specLift aux sp n j ty = some r →
      peelCtorParams V' f depth specLift aux sp n j ty = some r ∧ RKeysAt V S r := by
  intro n
  induction n with
  | zero =>
    intro j ty r hK h
    simp only [peelCtorParams, Option.some.injEq] at h ⊢
    subst h
    exact ⟨rfl, hK⟩
  | succ n ih =>
    intro j ty r hK h
    cases hb : binderOf V f ty with
    | none => simp [peelCtorParams, hb] at h
    | some x =>
      obtain ⟨hb', hk⟩ := binderOf_leOn hV hC f ty x hK hb
      cases x with
      | none => simp [peelCtorParams, hb] at h
      | some p =>
        obtain ⟨d, b, m⟩ := p
        simp only [peelCtorParams, hb, hb'] at h ⊢
        exact ih (j + 1) _ r (rk_inst1Lift (hk d b m rfl).2 (rk_ctorSubstParamFor hsp)) h

theorem whnfTele_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) (f : Nat) :
    ∀ (n : Nat) (e r : KExpr), RKeysAt V S e → whnfTele V f n e = some r →
      whnfTele V' f n e = some r := by
  intro n
  induction n with
  | zero => intro e r _ h; simp [whnfTele] at h
  | succ n ih =>
    intro e r hK h
    cases hh : hnf V f e with
    | none => simp [whnfTele, hh] at h
    | some w =>
      obtain ⟨hh', hkw⟩ := hnf_leOn hV hC f e w hK hh
      cases hi : isForall w with
      | none =>
        simp only [whnfTele, hh, hh', hi] at h ⊢
        exact h
      | some p =>
        obtain ⟨d, b, m⟩ := p
        simp only [whnfTele, hh, hh', hi] at h ⊢
        cases ht : whnfTele V f n b with
        | none => simp [ht] at h
        | some q =>
          rw [ih b q (isForall_keys hi hkw).2 ht]
          rw [ht] at h
          exact h

theorem isRecField_congr (hV : V.LeOn S V') (es : List FlatEntry) (liftBy : Nat) (e : KExpr) :
    isRecField V' es liftBy e = isRecField V es liftBy e := by
  simp only [isRecField, hV.addr]

theorem fieldsClassify_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) (f : Nat)
    (es : List FlatEntry) (liftBy : Nat) :
    ∀ (ty : KExpr) (fidx : Nat) (r : List KExpr × List Nat × List Nat × KExpr × List KExpr),
      RKeysAt V S ty → fieldsClassify V f es liftBy fidx ty = some r →
      fieldsClassify V' f es liftBy fidx ty = some r := by
  intro ty
  induction ty with
  | forallE d b m ihd ihb =>
    intro fidx r hK h
    simp only [fieldsClassify] at h ⊢
    cases hw : whnfTele V f f d with
    | none => simp [hw] at h
    | some nd =>
      rw [whnfTele_leOn hV hC f f d nd (fun k hk => hK k (.allTy hk)) hw]
      rw [hw] at h
      simp only at h ⊢
      cases hr : fieldsClassify V f es liftBy (fidx + 1) b with
      | none => simp [hr] at h
      | some q =>
        rw [ihb (fidx + 1) q (fun k hk => hK k (.allBody hk)) hr]
        rw [hr] at h
        simp only [isRecField_congr hV] at h ⊢
        exact h
  | bvar _ => intro fidx r _ h; simpa [fieldsClassify] using h
  | fvar _ _ _ => intro fidx r _ h; simpa [fieldsClassify] using h
  | sort _ => intro fidx r _ h; simpa [fieldsClassify] using h
  | const _ _ => intro fidx r _ h; simpa [fieldsClassify] using h
  | app _ _ _ _ => intro fidx r _ h; simpa [fieldsClassify] using h
  | lam _ _ _ _ _ => intro fidx r _ h; simpa [fieldsClassify] using h
  | letE _ _ _ _ _ _ _ => intro fidx r _ h; simpa [fieldsClassify] using h
  | lit _ => intro fidx r _ h; simpa [fieldsClassify] using h
  | proj _ _ _ _ => intro fidx r _ h; simpa [fieldsClassify] using h

/-! ## Minor premises and motives -/

theorem minorAt_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) {f : Nat} {es : List FlatEntry}
    {fop : List Nat} {ck : KKey} {cty : KExpr} {nOwn : Nat} {aux : Bool} {sp : List KExpr}
    {us : List KLevel} {nrp nMot prev motiveBase selfMemIdx : Nat} {elim : KLevel}
    (hK : RKeysAt V S cty) (hsp : ∀ p ∈ sp, RKeysAt V S p) {r : KExpr}
    (h : minorAt V f es fop ck cty nOwn aux sp us nrp nMot prev motiveBase selfMemIdx elim =
      some r) :
    minorAt V' f es fop ck cty nOwn aux sp us nrp nMot prev motiveBase selfMemIdx elim =
      some r := by
  simp only [minorAt] at h ⊢
  cases hp : peelCtorParams V f nrp 0 aux sp nOwn 0
      (cty.instantiateLevelParams (List.range us.length) us) with
  | none => simp [hp] at h
  | some after =>
    obtain ⟨hp', hka⟩ := peelCtorParams_leOn hV hC hsp nOwn 0 _ after (rk_ilp _ _ hK) hp
    rw [hp']
    rw [hp] at h
    simp only at h ⊢
    cases hc : fieldsClassify V f es 0 0 after with
    | none => simp [hc] at h
    | some q =>
      rw [fieldsClassify_leOn hV hC f es 0 after 0 q hka hc]
      rw [hc] at h
      exact h

theorem minorDoms_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) {f : Nat} {es : List FlatEntry}
    {fop : List Nat} {aux : Bool} {sp : List KExpr} {us : List KLevel}
    {nrp nMot motiveBase selfMemIdx : Nat} {blk : _root_.Address} {idx : Nat} {elim : KLevel}
    (hblk : S blk) (hsp : ∀ p ∈ sp, RKeysAt V S p) :
    ∀ (cs : List Nat) (prev : Nat) (r : List KExpr),
      minorDoms V f es fop aux sp us nrp nMot motiveBase selfMemIdx blk idx elim prev cs =
        some r →
      minorDoms V' f es fop aux sp us nrp nMot motiveBase selfMemIdx blk idx elim prev cs =
        some r := by
  intro cs
  induction cs with
  | nil => intro prev r h; simpa only [minorDoms] using h
  | cons c cs ih =>
    intro prev r h
    simp only [minorDoms] at h ⊢
    cases hc : V.ctor blk idx c with
    | none => simp [hc] at h
    | some p =>
      obtain ⟨cty, np⟩ := p
      rw [hV.ctor blk idx c _ hblk hc, hV.key, hV.ctorAddr]
      rw [hc] at h
      simp only at h ⊢
      cases hm : minorAt V f es fop (V.key (V.ctorAddr blk idx c)) cty np aux sp us nrp nMot
          prev motiveBase selfMemIdx elim with
      | none => simp [hm] at h
      | some m =>
        rw [minorAt_leOn hV hC (hC.ctorTy blk idx c cty np hblk hc) hsp hm]
        rw [hm] at h
        simp only at h ⊢
        cases hr : minorDoms V f es fop aux sp us nrp nMot motiveBase selfMemIdx blk idx elim
            (prev + 1) cs with
        | none => simp [hr] at h
        | some q =>
          rw [ih (prev + 1) q hr]
          rw [hr] at h
          exact h

theorem allMinors_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) {f : Nat}
    {fullEs : List FlatEntry} {fop : List Nat} {nrp nMot motiveBase : Nat} {elim : KLevel} :
    ∀ (es : List FlatEntry) (prev pos : Nat) (r : List KExpr), (∀ e ∈ es, REntryAt V S e) →
      allMinors V f fullEs fop nrp nMot motiveBase elim es prev pos = some r →
      allMinors V' f fullEs fop nrp nMot motiveBase elim es prev pos = some r := by
  intro es
  induction es with
  | nil => intro prev pos r _ h; simpa only [allMinors] using h
  | cons e es ih =>
    intro prev pos r hE h
    have he := hE e List.mem_cons_self
    simp only [allMinors] at h ⊢
    cases hi : V.ind e.addr with
    | none => simp [hi] at h
    | some i =>
      rw [hV.ind e.addr i he.addr hi]
      rw [hi] at h
      simp only at h ⊢
      cases hm : minorDoms V f fullEs fop e.aux e.params e.levels nrp nMot motiveBase pos i.blk
          i.idx elim prev (List.range i.nctors) with
      | none => simp [hm] at h
      | some ms =>
        rw [minorDoms_leOn hV hC (hC.indBlk e.addr i he.addr hi) he.params _ prev ms hm]
        rw [hm] at h
        simp only at h ⊢
        cases hr : allMinors V f fullEs fop nrp nMot motiveBase elim es (prev + ms.length)
            (pos + 1) with
        | none => simp [hr] at h
        | some q =>
          rw [ih (prev + ms.length) (pos + 1) q (fun x hx => hE x (List.mem_cons_of_mem _ hx)) hr]
          rw [hr] at h
          exact h

theorem motiveType_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) {f : Nat}
    {memberAddr : _root_.Address} {indTy : KExpr} {nOwn nIdx : Nat} {us : List KLevel}
    {elim : KLevel} {nrp : Nat} {aux : Bool} {sp : List KExpr} (hK : RKeysAt V S indTy)
    (hsp : ∀ p ∈ sp, RKeysAt V S p) {r : KExpr}
    (h : motiveType V f memberAddr indTy nOwn nIdx us elim nrp aux sp = some r) :
    motiveType V' f memberAddr indTy nOwn nIdx us elim nrp aux sp = some r := by
  simp only [motiveType] at h ⊢
  cases hp : peelMotiveParams nrp aux sp nOwn 0
      (indTy.instantiateLevelParams (List.range us.length) us) with
  | none => simp [hp] at h
  | some after =>
    have hka := peelMotiveParams_keys hsp nOwn 0 _ after (rk_ilp _ _ hK) hp
    rw [hp] at h
    simp only at h ⊢
    cases hc : collectDoms V f nIdx after with
    | none => simp [hc] at h
    | some q =>
      rw [collectDoms_leOn hV hC f nIdx after q hka hc, hV.key]
      rw [hc] at h
      exact h

theorem allMotives_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) {f : Nat} {elim : KLevel}
    {nrp : Nat} :
    ∀ (es : List FlatEntry) (j : Nat) (r : List KExpr), (∀ e ∈ es, REntryAt V S e) →
      allMotives V f elim nrp es j = some r → allMotives V' f elim nrp es j = some r := by
  intro es
  induction es with
  | nil => intro j r _ h; simpa only [allMotives] using h
  | cons e es ih =>
    intro j r hE h
    have he := hE e List.mem_cons_self
    simp only [allMotives] at h ⊢
    cases hi : V.ind e.addr with
    | none => simp [hi] at h
    | some i =>
      rw [hV.ind e.addr i he.addr hi]
      rw [hi] at h
      simp only at h ⊢
      cases hm : motiveType V f e.addr i.ty i.np i.ni e.levels elim nrp e.aux e.params with
      | none => simp [hm] at h
      | some mt =>
        rw [motiveType_leOn hV hC (hC.indTy e.addr i he.addr hi) he.params hm]
        rw [hm] at h
        simp only at h ⊢
        cases hr : allMotives V f elim nrp es (j + 1) with
        | none => simp [hr] at h
        | some q =>
          rw [ih (j + 1) q (fun x hx => hE x (List.mem_cons_of_mem _ hx)) hr]
          rw [hr] at h
          exact h

theorem flatOwnParams_leOn (hV : V.LeOn S V') :
    ∀ (es : List FlatEntry) (r : List Nat), (∀ e ∈ es, REntryAt V S e) →
      flatOwnParams V es = some r → flatOwnParams V' es = some r := by
  intro es
  induction es with
  | nil => intro r _ h; simpa only [flatOwnParams] using h
  | cons e es ih =>
    intro r hE h
    simp only [flatOwnParams] at h ⊢
    cases hi : V.ind e.addr with
    | none => simp [hi] at h
    | some i =>
      cases hr : flatOwnParams V es with
      | none => simp [hi, hr] at h
      | some q =>
        rw [hV.ind e.addr i (hE e List.mem_cons_self).addr hi,
          ih q (fun x hx => hE x (List.mem_cons_of_mem _ hx)) hr]
        rw [hi, hr] at h
        exact h

theorem ctorsBefore_leOn (hV : V.LeOn S V') :
    ∀ (es : List FlatEntry) (k r : Nat), (∀ e ∈ es, REntryAt V S e) →
      ctorsBefore V es k = some r → ctorsBefore V' es k = some r := by
  intro es
  induction es with
  | nil =>
    intro k r _ h
    cases k with
    | zero => simpa only [ctorsBefore] using h
    | succ k => simpa only [ctorsBefore] using h
  | cons e es ih =>
    intro k r hE h
    cases k with
    | zero => simpa only [ctorsBefore] using h
    | succ k =>
      simp only [ctorsBefore] at h ⊢
      cases hi : V.ind e.addr with
      | none => simp [hi] at h
      | some i =>
        cases hr : ctorsBefore V es k with
        | none => simp [hi, hr] at h
        | some q =>
          rw [hV.ind e.addr i (hE e List.mem_cons_self).addr hi,
            ih k q (fun x hx => hE x (List.mem_cons_of_mem _ hx)) hr]
          rw [hi, hr] at h
          exact h

/-! ## The recursor type -/

/-- **A view that answers as the first on a closed set holding the entries reconstructs the same
recursor type.** -/
theorem recTypeAt_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) {f : Nat} {es : List FlatEntry}
    (hE : ∀ e ∈ es, REntryAt V S e) {off nP k : Nat} {R : KExpr}
    (h : recTypeAt V f es off nP k = some R) : recTypeAt V' f es off nP k = some R := by
  simp only [recTypeAt] at h ⊢
  cases h0 : es[0]? with
  | none => simp [h0] at h
  | some e0 =>
  cases hk : es[k]? with
  | none => simp [h0, hk] at h
  | some ek =>
  have he0 := hE e0 (List.mem_of_getElem? h0)
  have hek := hE ek (List.mem_of_getElem? hk)
  simp only [h0, hk] at h ⊢
  cases hp : V.ind e0.addr with
  | none => simp [hp] at h
  | some prim =>
  cases hs : V.ind ek.addr with
  | none => simp [hp, hs] at h
  | some self =>
  rw [hV.ind _ _ he0.addr hp, hV.ind _ _ hek.addr hs, hV.key]
  rw [hp, hs] at h
  simp only at h ⊢
  split at h
  · simp at h
  · next paramDoms rest hc1 =>
    rw [collectDoms_leOn hV hC f nP _ _ (rk_ilp _ _ (hC.indTy _ _ he0.addr hp)) hc1]
    simp only
    split at h
    · next motDoms fop hm hf =>
      rw [allMotives_leOn hV hC es 0 motDoms hE hm, flatOwnParams_leOn hV es fop hE hf]
      simp only
      split at h
      · simp at h
      · next minDoms hmin =>
        rw [allMinors_leOn hV hC es 0 0 minDoms hE hmin]
        simp only
        split at h
        · simp at h
        · next selfAfter hsa =>
          rw [hsa]
          simp only
          have hka := peelMotiveParams_keys hek.params _ 0 _ selfAfter
            (rk_ilp _ _ (hC.indTy _ _ hek.addr hs)) hsa
          split at h
          · simp at h
          · next idxRaw rest' hci =>
            rw [collectDoms_leOn hV hC f _ selfAfter _ hka hci]
            exact h
    · simp at h

/-! ## The rules -/

theorem applyIhs_congr (hV : V.LeOn S V') (rm : List Nat) (norm : List KExpr)
    (peers : List _root_.Address) (fop : List Nat) (nP nMot nMin nFields : Nat)
    (recLvls : List KLevel) (elim : KLevel) :
    ∀ (ri : List Nat) (head : KExpr) (k : Nat),
      applyIhs V' rm norm peers fop nP nMot nMin nFields recLvls elim head k ri =
        applyIhs V rm norm peers fop nP nMot nMin nFields recLvls elim head k ri := by
  intro ri
  induction ri with
  | nil => intro head k; simp only [applyIhs]
  | cons fi ri ih =>
    intro head k
    simp only [applyIhs, hV.key, ih]

theorem ruleBody_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) {f : Nat} {es : List FlatEntry}
    {fop : List Nat} {peers : List _root_.Address} {cty : KExpr}
    {minorIdx nP nMot nMin nOwn : Nat} {us recLvls : List KLevel} {aux : Bool}
    {sp : List KExpr} {elim : KLevel} (hK : RKeysAt V S cty) (hsp : ∀ p ∈ sp, RKeysAt V S p)
    {r : KExpr}
    (h : ruleBody V f es fop peers cty minorIdx nP nMot nMin nOwn us recLvls aux sp elim =
      some r) :
    ruleBody V' f es fop peers cty minorIdx nP nMot nMin nOwn us recLvls aux sp elim =
      some r := by
  simp only [ruleBody] at h ⊢
  split at h
  · simp at h
  · next raw hraw =>
    rw [hraw]
    simp only
    split at h
    · simp at h
    · next after hp =>
      obtain ⟨hp', hka⟩ := peelCtorParams_leOn hV hC hsp nOwn 0 _ after (rk_ilp _ _ hK) hp
      rw [hp']
      simp only
      split at h
      · simp at h
      · next fds ri rm ret norm hc =>
        rw [fieldsClassify_leOn hV hC f es 0 after 0 _ hka hc]
        simp only [applyIhs_congr hV]
        exact h

theorem ruleBodies_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) {f : Nat} {es : List FlatEntry}
    {fop : List Nat} {peers : List _root_.Address} {nP nMot nMin : Nat}
    {us recLvls : List KLevel} {aux : Bool} {sp : List KExpr} {elim : KLevel}
    {blk : _root_.Address} {idx off : Nat} (hblk : S blk) (hsp : ∀ p ∈ sp, RKeysAt V S p) :
    ∀ (cs : List Nat) (r : List KExpr),
      ruleBodies V f es fop peers nP nMot nMin us recLvls aux sp elim blk idx off cs = some r →
      ruleBodies V' f es fop peers nP nMot nMin us recLvls aux sp elim blk idx off cs =
        some r := by
  intro cs
  induction cs with
  | nil => intro r h; simpa only [ruleBodies] using h
  | cons c cs ih =>
    intro r h
    simp only [ruleBodies] at h ⊢
    cases hc : V.ctor blk idx c with
    | none => simp [hc] at h
    | some p =>
      obtain ⟨cty, np⟩ := p
      rw [hV.ctor blk idx c _ hblk hc]
      rw [hc] at h
      simp only at h ⊢
      cases hb : ruleBody V f es fop peers cty (off + c) nP nMot nMin np us recLvls aux sp
          elim with
      | none => simp [hb] at h
      | some b =>
        rw [ruleBody_leOn hV hC (hC.ctorTy blk idx c cty np hblk hc) hsp hb]
        rw [hb] at h
        simp only at h ⊢
        cases hr : ruleBodies V f es fop peers nP nMot nMin us recLvls aux sp elim blk idx off
            cs with
        | none => simp [hr] at h
        | some q =>
          rw [ih q hr]
          rw [hr] at h
          exact h

/-- **A view that answers as the first on a closed set holding the entries reconstructs the same
rule bodies.** -/
theorem ruleBodiesAt_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) {f : Nat}
    {es : List FlatEntry} (hE : ∀ e ∈ es, REntryAt V S e) {off nP nMot nMin nl k : Nat}
    {peers : List _root_.Address} {r : List KExpr}
    (h : ruleBodiesAt V f es off nP nMot nMin nl k peers = some r) :
    ruleBodiesAt V' f es off nP nMot nMin nl k peers = some r := by
  simp only [ruleBodiesAt] at h ⊢
  cases hk : es[k]? with
  | none => simp [hk] at h
  | some ek =>
  have hek := hE ek (List.mem_of_getElem? hk)
  simp only [hk] at h ⊢
  cases hs : V.ind ek.addr with
  | none => simp [hs] at h
  | some self =>
  cases hf : flatOwnParams V es with
  | none => simp [hs, hf] at h
  | some fop =>
  cases hc : ctorsBefore V es k with
  | none => simp [hs, hf, hc] at h
  | some cb =>
  rw [hV.ind _ _ hek.addr hs, flatOwnParams_leOn hV es fop hE hf, ctorsBefore_leOn hV es k cb hE hc]
  rw [hs, hf, hc] at h
  simp only at h ⊢
  exact ruleBodies_leOn hV hC (hC.indBlk _ _ hek.addr hs) hek.params _ r h

end LeOn

end IxVM.Refinement.Binding.FamilyRecon
