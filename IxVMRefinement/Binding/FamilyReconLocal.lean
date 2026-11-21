import IxVMRefinement.Binding.FamilyRecon
import IxVMRefinement.Binding.FamilyFlatLocal

/-! # The reconstruction reads only a closed set of addresses

`recTypeAt` and `ruleBodiesAt` read a store through a `ReconView`: the inductive types at the
flattened family's entries (their types, counts, blocks), the constructors of those blocks, and the
definitions that head normalization unfolds at the head constants of the terms it normalizes.
Every answer is `none` where a load fails, so a view that answers as the first wherever the first
answers, on a set of addresses closed under what is read (`ReconView.ClosedOn`), reconstructs the
same, at any larger fuel (`recTypeAt_leOn`, `ruleBodiesAt_leOn`); so does the same view at a larger
fuel (`recTypeAt_fuel_mono`, `ruleBodiesAt_fuel_mono`, `MemberRecon.fuel_mono`), and recursors each
against the reconstruction at a fuel of their own give the record-level form at one
(`recordReconWith_of_members`).

* `RKeysAt`, `REntryAt`, `ReconView.LeOn`, `ReconView.ClosedOn`;
* the keys of the terms normalized stay in the set (`isForall_keys`, `lamBody_keys`, the keys of
  an instantiation, a lift, a level instantiation, a substituted parameter);
* `rk_mkAppN`, `hnfSpine_leOn`, `hnf_leOn`, `binderOf_leOn`, `collectDoms_leOn`,
  `peelMotiveParams_keys`, `peelCtorParams_leOn`, `whnfTele_leOn`, `isRecField_congr`,
  `fieldsClassify_leOn`, `minorAt_leOn`, `minorDoms_leOn`, `allMinors_leOn`, `motiveType_leOn`,
  `allMotives_leOn`, `flatOwnParams_leOn`, `ctorsBefore_leOn`, **`recTypeAt_leOn`**,
  `applyIhs_congr`, `ruleBody_leOn`, `ruleBodies_leOn`, **`ruleBodiesAt_leOn`**;
* `ReconView.LeOn.refl`, `ReconView.closedOn_univ`, **`recTypeAt_fuel_mono`**,
  **`ruleBodiesAt_fuel_mono`**, `MemberRecon.fuel_mono`, `exists_fuel_bound`,
  **`recordReconWith_of_members`**. -/

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
  ctorOf : ∀ a x, S a → V.ctorOf a = some x → V'.ctorOf a = some x
  modeled : ∀ b x, S b → V.modeled b = some x → V'.modeled b = some x

/-- **What `V` answers at the addresses of `S` stays in `S`**: an inductive type's block, the keys
of an inductive's type, of a constructor's type and of a definition's value. -/
structure ReconView.ClosedOn (S : _root_.Address → Prop) (V : ReconView) : Prop where
  indBlk : ∀ a i, S a → V.ind a = some (some i) → S i.blk
  indTy : ∀ a i, S a → V.ind a = some (some i) → RKeysAt V S i.ty
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

theorem rk_exprInstLevels {e : KExpr} (us : List KLevel)
    (h : RKeysAt V S e) : RKeysAt V S (exprInstLevels us e) :=
  fun k hk => h k (keyIn_exprInstLevels e hk)

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

/-- **`red_proj` reads the store at the constructor's and the structure's addresses and at the
structure's block**, which a closed set holding the projection's keys holds. -/
theorem projStep_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) {s : KKey} {i : Nat} {e : KExpr}
    {x : Option KExpr} (hK : RKeysAt V S (.proj s i e)) (h : projStep V s i e = some x) :
    projStep V' s i e = some x := by
  unfold projStep at h ⊢
  rw [hV.addr]
  cases hf : Ix.Kernel.Expr.getAppFn e with
  | const ck cus =>
    rw [hf] at h
    have hkck : ∀ a, V.addr ck = some a → S a := fun a ha =>
      hK ck (.projBody (keyIn_getAppFn (by rw [hf]; exact .const cus))) a ha
    have hks : ∀ a, V.addr s = some a → S a := fun a ha => hK s (.proj i e) a ha
    simp only at h ⊢
    cases ha : V.addr ck with
    | none => rw [ha] at h; exact h
    | some ca =>
      rw [ha] at h
      simp only at h ⊢
      cases hco : V.ctorOf ca with
      | none => rw [hco] at h; simp at h
      | some co =>
        rw [hV.ctorOf ca co (hkck ca ha) hco]
        rw [hco] at h
        cases co with
        | none => exact h
        | some cd =>
          simp only at h ⊢
          cases hsa : V.addr s with
          | none => rw [hsa] at h; exact h
          | some sa =>
            rw [hsa] at h
            simp only at h ⊢
            cases hsd : V.ind sa with
            | none => rw [hsd] at h; simp at h
            | some sdo =>
              rw [hV.ind sa sdo (hks sa hsa) hsd]
              rw [hsd] at h
              cases sdo with
              | none => exact h
              | some sd =>
                simp only at h ⊢
                by_cases hg : projGate cd sd cus (Ix.Kernel.Expr.getAppArgs e) i = true
                · rw [ite_eq_left hg] at h
                  rw [ite_eq_left hg]
                  cases hm : V.modeled sd.blk with
                  | none => rw [hm] at h; simp at h
                  | some mb =>
                    rw [hV.modeled sd.blk mb (hC.indBlk sa sd (hks sa hsa) hsd) hm]
                    rw [hm] at h
                    exact h
                · rw [ite_eq_right hg] at h
                  rw [ite_eq_right hg]
                  exact h
  | _ => rw [hf] at h; exact h

/-- **A field `red_proj` projects is an argument of the projected term.** -/
theorem projStep_mem {s : KKey} {i : Nat} {e e' : KExpr}
    (h : projStep V s i e = some (some e')) : e' ∈ Ix.Kernel.Expr.getAppArgs e := by
  unfold projStep at h
  cases hf : Ix.Kernel.Expr.getAppFn e with
  | const ck cus =>
    rw [hf] at h
    simp only at h
    cases ha : V.addr ck with
    | none => rw [ha] at h; simp at h
    | some ca =>
      rw [ha] at h
      simp only at h
      cases hco : V.ctorOf ca with
      | none => rw [hco] at h; simp at h
      | some co =>
        rw [hco] at h
        cases co with
        | none => simp at h
        | some cd =>
          simp only at h
          cases hsa : V.addr s with
          | none => rw [hsa] at h; simp at h
          | some sa =>
            rw [hsa] at h
            simp only at h
            cases hsd : V.ind sa with
            | none => rw [hsd] at h; simp at h
            | some sdo =>
              rw [hsd] at h
              cases sdo with
              | none => simp at h
              | some sd =>
                simp only at h
                by_cases hg : projGate cd sd cus (Ix.Kernel.Expr.getAppArgs e) i = true
                · rw [ite_eq_left hg] at h
                  cases hm : V.modeled sd.blk with
                  | none => rw [hm] at h; simp at h
                  | some mb =>
                    rw [hm] at h
                    cases mb with
                    | true => simp at h
                    | false =>
                      simp only at h
                      by_cases ht : typeSortNever sd.ty sd.np cus = true
                      · rw [ite_eq_left ht] at h
                        exact List.mem_of_getElem? (Option.some.inj h)
                      · rw [ite_eq_right ht] at h
                        simp at h
                · rw [ite_eq_right hg] at h
                  simp at h
  | _ => rw [hf] at h; simp at h


/-- The keys of a head applied to a spine. -/
theorem rk_mkAppN : ∀ (sp : List KExpr) (e : KExpr), RKeysAt V S e → (∀ a ∈ sp, RKeysAt V S a) →
    RKeysAt V S (Ix.Kernel.Expr.mkAppN e sp)
  | [], e, he, _ => he
  | a :: sp, e, he, hs => by
    simp only [Ix.Kernel.Expr.mkAppN]
    refine rk_mkAppN sp (.app e a) (fun k hk => ?_) (fun b hb => hs b (List.mem_cons_of_mem _ hb))
    cases hk with
    | appFn h => exact he k h
    | appArg h => exact hs a List.mem_cons_self k h

/-- **The spine machine at a larger fuel, through a view that answers as the first on a closed
set holding the head's and the spine's keys, normalizes to the same term**, whose keys stay in the
set. -/
theorem hnfSpine_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) :
    ∀ (n n' : Nat) (e : KExpr) (sp : List KExpr) (r : KExpr), n ≤ n' → RKeysAt V S e →
      (∀ a ∈ sp, RKeysAt V S a) → hnfSpine V n e sp = some r →
      hnfSpine V' n' e sp = some r ∧ RKeysAt V S r := by
  intro n
  induction n with
  | zero => intro n' e sp r _ _ _ h; simp [hnfSpine] at h
  | succ n ih =>
    intro n' e sp r hn hK hsp h
    obtain ⟨m, rfl⟩ : ∃ m, n' = m + 1 := ⟨n' - 1, by omega⟩
    have hnm : n ≤ m := by omega
    cases e with
    | app f a =>
      simp only [hnfSpine] at h ⊢
      refine ih m f (a :: sp) r hnm (fun k hk => hK k (.appFn hk)) (fun b hb => ?_) h
      rcases List.mem_cons.mp hb with rfl | hb
      · exact fun k hk => hK k (.appArg hk)
      · exact hsp b hb
    | lam d b mm =>
      cases sp with
      | nil =>
        simp only [hnfSpine, Option.some.injEq] at h ⊢
        subst h
        exact ⟨rfl, hK⟩
      | cons a sp' =>
        simp only [hnfSpine] at h ⊢
        exact ih m _ sp' r hnm
          (rk_inst1Lift (fun k hk => hK k (.lamBody hk)) (hsp a List.mem_cons_self))
          (fun x hx => hsp x (List.mem_cons_of_mem _ hx)) h
    | const k us =>
      have hk : ∀ a, V.addr k = some a → S a := hK k (.const _)
      simp only [hnfSpine] at h ⊢
      cases hu : V.unfold k us with
      | none => rw [hu] at h; simp at h
      | some x =>
        rw [hV.unfold k us x hk hu]
        rw [hu] at h
        cases x with
        | none =>
          simp only [Option.some.injEq] at h ⊢
          subst h
          exact ⟨rfl, rk_mkAppN sp _ hK hsp⟩
        | some v =>
          simp only at h ⊢
          exact ih m v sp r hnm (hC.unfold k us v hk hu) hsp h
    | proj s i x =>
      have hKx : RKeysAt V S x := fun k hk => hK k (.projBody hk)
      simp only [hnfSpine] at h ⊢
      cases hw : hnfSpine V n x [] with
      | none => rw [hw] at h; simp at h
      | some w =>
        obtain ⟨hw', hkw⟩ := ih m x [] w hnm hKx (by simp) hw
        rw [hw']
        rw [hw] at h
        simp only at h ⊢
        have hKp : RKeysAt V S (.proj s i w) := by
          intro k hk a ha
          cases hk with
          | proj => exact hK _ (.proj i x) a ha
          | projBody h1 => exact hkw k h1 a ha
        cases hp : projStep V s i w with
        | none => rw [hp] at h; simp at h
        | some y =>
          rw [projStep_leOn hV hC hKp hp]
          rw [hp] at h
          cases y with
          | none =>
            simp only [Option.some.injEq] at h ⊢
            subst h
            exact ⟨rfl, rk_mkAppN sp _ hKp hsp⟩
          | some y =>
            simp only at h ⊢
            exact ih m y sp r hnm
              (fun k hk a ha => hkw k (keyIn_of_mem_getAppArgs w (projStep_mem hp) hk) a ha) hsp h
    | bvar _ | fvar _ _ | sort _ | forallE _ _ _ | letE _ _ _ _ | lit _ =>
      simp only [hnfSpine, Option.some.injEq] at h ⊢
      subst h
      exact ⟨rfl, rk_mkAppN sp _ hK hsp⟩

/-- **Head normalization at a larger fuel, through a view that answers as the first on a closed
set holding the term's keys, gives the same term**, whose keys stay in the set. -/
theorem hnf_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) {n n' : Nat} (hn : n ≤ n') {e r : KExpr}
    (hK : RKeysAt V S e) (h : hnf V n e = some r) : hnf V' n' e = some r ∧ RKeysAt V S r :=
  hnfSpine_leOn hV hC n n' e [] r hn hK (by simp) h

theorem binderOf_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) {f f' : Nat} (hf : f ≤ f')
    (ty : KExpr) (x : Option (KExpr × KExpr × Ix.Kernel.BinderMeta)) (hK : RKeysAt V S ty)
    (h : binderOf V f ty = some x) :
    binderOf V' f' ty = some x ∧
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
      obtain ⟨hh', hkw⟩ := hnf_leOn hV hC hf hK hh
      rw [hh, Option.map_some, Option.some.injEq] at h
      rw [hh', Option.map_some, Option.some.injEq]
      subst h
      exact ⟨rfl, fun d b m hp => isForall_keys hp hkw⟩

theorem collectDoms_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) {f f' : Nat} (hf : f ≤ f') :
    ∀ (n : Nat) (ty : KExpr) (r : List KExpr × KExpr), RKeysAt V S ty →
      collectDoms V f n ty = some r → collectDoms V' f' n ty = some r := by
  intro n
  induction n with
  | zero => intro ty r _ h; simpa only [collectDoms] using h
  | succ n ih =>
    intro ty r hK h
    cases hb : binderOf V f ty with
    | none => simp [collectDoms, hb] at h
    | some x =>
      obtain ⟨hb', hk⟩ := binderOf_leOn hV hC hf ty x hK hb
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

theorem peelCtorParams_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) {f f' depth specLift : Nat}
    (hf : f ≤ f') {aux : Bool} {sp : List KExpr} (hsp : ∀ p ∈ sp, RKeysAt V S p) :
    ∀ (n j : Nat) (ty r : KExpr), RKeysAt V S ty →
      peelCtorParams V f depth specLift aux sp n j ty = some r →
      peelCtorParams V' f' depth specLift aux sp n j ty = some r ∧ RKeysAt V S r := by
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
      obtain ⟨hb', hk⟩ := binderOf_leOn hV hC hf ty x hK hb
      cases x with
      | none => simp [peelCtorParams, hb] at h
      | some p =>
        obtain ⟨d, b, m⟩ := p
        simp only [peelCtorParams, hb, hb'] at h ⊢
        exact ih (j + 1) _ r (rk_inst1Lift (hk d b m rfl).2 (rk_ctorSubstParamFor hsp)) h

theorem whnfTele_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) {f f' : Nat} (hf : f ≤ f') :
    ∀ (n n' : Nat) (e r : KExpr), n ≤ n' → RKeysAt V S e → whnfTele V f n e = some r →
      whnfTele V' f' n' e = some r := by
  intro n
  induction n with
  | zero => intro n' e r _ _ h; simp [whnfTele] at h
  | succ n ih =>
    intro n' e r hn hK h
    obtain ⟨m, rfl⟩ : ∃ m, n' = m + 1 := ⟨n' - 1, by omega⟩
    have hnm : n ≤ m := by omega
    cases hh : hnf V f e with
    | none => simp [whnfTele, hh] at h
    | some w =>
      obtain ⟨hh', hkw⟩ := hnf_leOn hV hC hf hK hh
      cases hi : isForall w with
      | none =>
        simp only [whnfTele, hh, hh', hi] at h ⊢
        exact h
      | some p =>
        obtain ⟨d, b, mm⟩ := p
        simp only [whnfTele, hh, hh', hi] at h ⊢
        cases ht : whnfTele V f n b with
        | none => simp [ht] at h
        | some q =>
          rw [ih m b q hnm (isForall_keys hi hkw).2 ht]
          rw [ht] at h
          exact h

theorem isRecField_congr (hV : V.LeOn S V') (es : List FlatEntry) (liftBy : Nat) (e : KExpr) :
    isRecField V' es liftBy e = isRecField V es liftBy e := by
  simp only [isRecField, hV.addr]

theorem fieldsClassify_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) {f f' : Nat} (hf : f ≤ f')
    (es : List FlatEntry) (liftBy : Nat) :
    ∀ (ty : KExpr) (fidx : Nat) (r : List KExpr × List Nat × List Nat × KExpr × List KExpr),
      RKeysAt V S ty → fieldsClassify V f es liftBy fidx ty = some r →
      fieldsClassify V' f' es liftBy fidx ty = some r := by
  intro ty
  induction ty with
  | forallE d b m ihd ihb =>
    intro fidx r hK h
    simp only [fieldsClassify] at h ⊢
    cases hw : whnfTele V f f d with
    | none => simp [hw] at h
    | some nd =>
      rw [whnfTele_leOn hV hC hf f f' d nd hf (fun k hk => hK k (.allTy hk)) hw]
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

theorem minorAt_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) {f f' : Nat} (hfu : f ≤ f')
    {es : List FlatEntry}
    {fop : List Nat} {ck : KKey} {cty : KExpr} {nOwn : Nat} {aux : Bool} {sp : List KExpr}
    {us : List KLevel} {nrp nMot prev motiveBase selfMemIdx : Nat} {elim : KLevel}
    (hK : RKeysAt V S cty) (hsp : ∀ p ∈ sp, RKeysAt V S p) {r : KExpr}
    (h : minorAt V f es fop ck cty nOwn aux sp us nrp nMot prev motiveBase selfMemIdx elim =
      some r) :
    minorAt V' f' es fop ck cty nOwn aux sp us nrp nMot prev motiveBase selfMemIdx elim =
      some r := by
  simp only [minorAt] at h ⊢
  cases hp : peelCtorParams V f nrp 0 aux sp nOwn 0 (exprInstLevels us cty) with
  | none => simp [hp] at h
  | some after =>
    obtain ⟨hp', hka⟩ := peelCtorParams_leOn hV hC hfu hsp nOwn 0 _ after (rk_exprInstLevels _ hK) hp
    rw [hp']
    rw [hp] at h
    simp only at h ⊢
    cases hc : fieldsClassify V f es 0 0 after with
    | none => simp [hc] at h
    | some q =>
      rw [fieldsClassify_leOn hV hC hfu es 0 after 0 q hka hc]
      rw [hc] at h
      exact h

theorem minorDoms_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) {f f' : Nat} (hfu : f ≤ f')
    {es : List FlatEntry}
    {fop : List Nat} {aux : Bool} {sp : List KExpr} {us : List KLevel}
    {nrp nMot motiveBase selfMemIdx : Nat} {blk : _root_.Address} {idx : Nat} {elim : KLevel}
    (hblk : S blk) (hsp : ∀ p ∈ sp, RKeysAt V S p) :
    ∀ (cs : List Nat) (prev : Nat) (r : List KExpr),
      minorDoms V f es fop aux sp us nrp nMot motiveBase selfMemIdx blk idx elim prev cs =
        some r →
      minorDoms V' f' es fop aux sp us nrp nMot motiveBase selfMemIdx blk idx elim prev cs =
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
        rw [minorAt_leOn hV hC hfu (hC.ctorTy blk idx c cty np hblk hc) hsp hm]
        rw [hm] at h
        simp only at h ⊢
        cases hr : minorDoms V f es fop aux sp us nrp nMot motiveBase selfMemIdx blk idx elim
            (prev + 1) cs with
        | none => simp [hr] at h
        | some q =>
          rw [ih (prev + 1) q hr]
          rw [hr] at h
          exact h

theorem allMinors_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) {f f' : Nat} (hfu : f ≤ f')
    {fullEs : List FlatEntry} {fop : List Nat} {nrp nMot motiveBase : Nat} {elim : KLevel} :
    ∀ (es : List FlatEntry) (prev pos : Nat) (r : List KExpr), (∀ e ∈ es, REntryAt V S e) →
      allMinors V f fullEs fop nrp nMot motiveBase elim es prev pos = some r →
      allMinors V' f' fullEs fop nrp nMot motiveBase elim es prev pos = some r := by
  intro es
  induction es with
  | nil => intro prev pos r _ h; simpa only [allMinors] using h
  | cons e es ih =>
    intro prev pos r hE h
    have he := hE e List.mem_cons_self
    simp only [allMinors] at h ⊢
    cases hi : V.ind e.addr with
    | none => simp [hi] at h
    | some io =>
      cases io with
      | none => simp [hi] at h
      | some i =>
        rw [hV.ind e.addr (some i) he.addr hi]
        rw [hi] at h
        simp only at h ⊢
        cases hm : minorDoms V f fullEs fop e.aux e.params e.levels nrp nMot motiveBase pos i.blk
            i.idx elim prev (List.range i.nctors) with
        | none => simp [hm] at h
        | some ms =>
          rw [minorDoms_leOn hV hC hfu (hC.indBlk e.addr i he.addr hi) he.params _ prev ms hm]
          rw [hm] at h
          simp only at h ⊢
          cases hr : allMinors V f fullEs fop nrp nMot motiveBase elim es (prev + ms.length)
              (pos + 1) with
          | none => simp [hr] at h
          | some q =>
            rw [ih (prev + ms.length) (pos + 1) q (fun x hx => hE x (List.mem_cons_of_mem _ hx)) hr]
            rw [hr] at h
            exact h

theorem motiveType_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) {f f' : Nat} (hfu : f ≤ f')
    {memberAddr : _root_.Address} {indTy : KExpr} {nOwn nIdx : Nat} {us : List KLevel}
    {elim : KLevel} {nrp : Nat} {aux : Bool} {sp : List KExpr} (hK : RKeysAt V S indTy)
    (hsp : ∀ p ∈ sp, RKeysAt V S p) {r : KExpr}
    (h : motiveType V f memberAddr indTy nOwn nIdx us elim nrp aux sp = some r) :
    motiveType V' f' memberAddr indTy nOwn nIdx us elim nrp aux sp = some r := by
  simp only [motiveType] at h ⊢
  cases hp : peelMotiveParams nrp aux sp nOwn 0 (exprInstLevels us indTy) with
  | none => simp [hp] at h
  | some after =>
    have hka := peelMotiveParams_keys hsp nOwn 0 _ after (rk_exprInstLevels _ hK) hp
    rw [hp] at h
    simp only at h ⊢
    cases hc : collectDoms V f nIdx after with
    | none => simp [hc] at h
    | some q =>
      rw [collectDoms_leOn hV hC hfu nIdx after q hka hc, hV.key]
      rw [hc] at h
      exact h

theorem allMotives_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) {f f' : Nat} (hfu : f ≤ f')
    {elim : KLevel}
    {nrp : Nat} :
    ∀ (es : List FlatEntry) (j : Nat) (r : List KExpr), (∀ e ∈ es, REntryAt V S e) →
      allMotives V f elim nrp es j = some r → allMotives V' f' elim nrp es j = some r := by
  intro es
  induction es with
  | nil => intro j r _ h; simpa only [allMotives] using h
  | cons e es ih =>
    intro j r hE h
    have he := hE e List.mem_cons_self
    simp only [allMotives] at h ⊢
    cases hi : V.ind e.addr with
    | none => simp [hi] at h
    | some io =>
      cases io with
      | none => simp [hi] at h
      | some i =>
        rw [hV.ind e.addr (some i) he.addr hi]
        rw [hi] at h
        simp only at h ⊢
        cases hm : motiveType V f e.addr i.ty i.np i.ni e.levels elim nrp e.aux e.params with
        | none => simp [hm] at h
        | some mt =>
          rw [motiveType_leOn hV hC hfu (hC.indTy e.addr i he.addr hi) he.params hm]
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
    | some io =>
      cases io with
      | none => simp [hi] at h
      | some i =>
        cases hr : flatOwnParams V es with
        | none => simp [hi, hr] at h
        | some q =>
          rw [hV.ind e.addr (some i) (hE e List.mem_cons_self).addr hi,
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
      | some io =>
        cases io with
        | none => simp [hi] at h
        | some i =>
          cases hr : ctorsBefore V es k with
          | none => simp [hi, hr] at h
          | some q =>
            rw [hV.ind e.addr (some i) (hE e List.mem_cons_self).addr hi,
              ih k q (fun x hx => hE x (List.mem_cons_of_mem _ hx)) hr]
            rw [hi, hr] at h
            exact h

/-! ## The recursor type -/

/-- **A view that answers as the first on a closed set holding the entries reconstructs the same
recursor type.** -/
theorem recTypeAt_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) {f f' : Nat} (hfu : f ≤ f')
    {es : List FlatEntry}
    (hE : ∀ e ∈ es, REntryAt V S e) {off nP k : Nat} {R : KExpr}
    (h : recTypeAt V f es off nP k = some R) : recTypeAt V' f' es off nP k = some R := by
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
  | some po =>
  cases po with
  | none => simp [hp] at h
  | some prim =>
  cases hs : V.ind ek.addr with
  | none => simp [hp, hs] at h
  | some so =>
  cases so with
  | none => simp [hp, hs] at h
  | some self =>
  rw [hV.ind _ _ he0.addr hp, hV.ind _ _ hek.addr hs, hV.key]
  rw [hp, hs] at h
  simp only at h ⊢
  split at h
  · simp at h
  · next paramDoms rest hc1 =>
    rw [collectDoms_leOn hV hC hfu nP _ _ (rk_exprInstLevels _ (hC.indTy _ _ he0.addr hp)) hc1]
    simp only
    split at h
    · next motDoms fop hm hf =>
      rw [allMotives_leOn hV hC hfu es 0 motDoms hE hm, flatOwnParams_leOn hV es fop hE hf]
      simp only
      split at h
      · simp at h
      · next minDoms hmin =>
        rw [allMinors_leOn hV hC hfu es 0 0 minDoms hE hmin]
        simp only
        split at h
        · simp at h
        · next selfAfter hsa =>
          have hka := peelMotiveParams_keys hek.params _ 0 _ selfAfter
            (rk_exprInstLevels _ (hC.indTy _ _ hek.addr hs)) hsa
          split at h
          · simp at h
          · next idxRaw rest' hci =>
            rw [collectDoms_leOn hV hC hfu _ selfAfter _ hka hci]
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

theorem ruleBody_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) {f f' : Nat} (hfu : f ≤ f')
    {es : List FlatEntry}
    {fop : List Nat} {peers : List _root_.Address} {cty : KExpr}
    {minorIdx nP nMot nMin nOwn : Nat} {us recLvls : List KLevel} {aux : Bool}
    {sp : List KExpr} {elim : KLevel} (hK : RKeysAt V S cty) (hsp : ∀ p ∈ sp, RKeysAt V S p)
    {r : KExpr}
    (h : ruleBody V f es fop peers cty minorIdx nP nMot nMin nOwn us recLvls aux sp elim =
      some r) :
    ruleBody V' f' es fop peers cty minorIdx nP nMot nMin nOwn us recLvls aux sp elim =
      some r := by
  simp only [ruleBody] at h ⊢
  split at h
  · simp at h
  · next raw hraw =>
    split at h
    · simp at h
    · next after hp =>
      obtain ⟨hp', hka⟩ := peelCtorParams_leOn hV hC hfu hsp nOwn 0 _ after (rk_exprInstLevels _ hK) hp
      rw [hp']
      simp only
      split at h
      · simp at h
      · next fds ri rm ret norm hc =>
        rw [fieldsClassify_leOn hV hC hfu es 0 after 0 _ hka hc]
        simp only [applyIhs_congr hV]
        exact h

theorem ruleBodies_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) {f f' : Nat} (hfu : f ≤ f')
    {es : List FlatEntry}
    {fop : List Nat} {peers : List _root_.Address} {nP nMot nMin : Nat}
    {us recLvls : List KLevel} {aux : Bool} {sp : List KExpr} {elim : KLevel}
    {blk : _root_.Address} {idx off : Nat} (hblk : S blk) (hsp : ∀ p ∈ sp, RKeysAt V S p) :
    ∀ (cs : List Nat) (r : List KExpr),
      ruleBodies V f es fop peers nP nMot nMin us recLvls aux sp elim blk idx off cs = some r →
      ruleBodies V' f' es fop peers nP nMot nMin us recLvls aux sp elim blk idx off cs =
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
        rw [ruleBody_leOn hV hC hfu (hC.ctorTy blk idx c cty np hblk hc) hsp hb]
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
theorem ruleBodiesAt_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) {f f' : Nat} (hfu : f ≤ f')
    {es : List FlatEntry} (hE : ∀ e ∈ es, REntryAt V S e) {off nP nMot nMin nl k : Nat}
    {peers : List _root_.Address} {r : List KExpr}
    (h : ruleBodiesAt V f es off nP nMot nMin nl k peers = some r) :
    ruleBodiesAt V' f' es off nP nMot nMin nl k peers = some r := by
  simp only [ruleBodiesAt] at h ⊢
  cases hk : es[k]? with
  | none => simp [hk] at h
  | some ek =>
  have hek := hE ek (List.mem_of_getElem? hk)
  simp only [hk] at h ⊢
  cases hs : V.ind ek.addr with
  | none => simp [hs] at h
  | some so =>
  cases so with
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
  exact ruleBodies_leOn hV hC hfu (hC.indBlk _ _ hek.addr hs) hek.params _ r h

end LeOn

/-! ## More fuel -/

/-- A view answers as itself on any set. -/
theorem ReconView.LeOn.refl (V : ReconView) (S : _root_.Address → Prop) : V.LeOn S V :=
  ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h, rfl, rfl, rfl, fun _ _ _ _ h => h,
    fun _ _ _ h => h, fun _ _ _ h => h⟩

/-- Every key of a term names, through the view, one of all addresses. -/
theorem rKeysAt_univ (V : ReconView) (e : KExpr) : RKeysAt V (fun _ => True) e :=
  fun _ _ _ _ => True.intro

/-- Every answer of a view stays among all addresses. -/
theorem ReconView.closedOn_univ (V : ReconView) : V.ClosedOn (fun _ => True) where
  indBlk := fun _ _ _ _ => True.intro
  indTy := fun _ i _ _ => rKeysAt_univ V i.ty
  ctorTy := fun _ _ _ ty _ _ _ => rKeysAt_univ V ty
  unfold := fun _ _ v _ _ => rKeysAt_univ V v

/-- Every entry is at an address among all addresses, its parameters' keys too. -/
theorem rEntryAt_univ (V : ReconView) (e : FlatEntry) : REntryAt V (fun _ => True) e :=
  ⟨True.intro, fun p _ => rKeysAt_univ V p⟩

/-- **The reconstructed recursor type at a larger fuel is the same.** -/
theorem recTypeAt_fuel_mono {V : ReconView} {f f' : Nat} (hfu : f ≤ f') {es : List FlatEntry}
    {off nP k : Nat} {R : KExpr} (h : recTypeAt V f es off nP k = some R) :
    recTypeAt V f' es off nP k = some R :=
  recTypeAt_leOn (ReconView.LeOn.refl V _) (ReconView.closedOn_univ V) hfu
    (fun e _ => rEntryAt_univ V e) h

/-- **The reconstructed rule bodies at a larger fuel are the same.** -/
theorem ruleBodiesAt_fuel_mono {V : ReconView} {f f' : Nat} (hfu : f ≤ f') {es : List FlatEntry}
    {off nP nMot nMin nl k : Nat} {peers : List _root_.Address} {r : List KExpr}
    (h : ruleBodiesAt V f es off nP nMot nMin nl k peers = some r) :
    ruleBodiesAt V f' es off nP nMot nMin nl k peers = some r :=
  ruleBodiesAt_leOn (ReconView.LeOn.refl V _) (ReconView.closedOn_univ V) hfu
    (fun e _ => rEntryAt_univ V e) h

/-- **A recursor against the reconstruction at one fuel is so at every larger fuel.** -/
theorem MemberRecon.fuel_mono {TyRel : KExpr → KExpr → Prop} {t : Ix.Kernel.RoleTable}
    {E : Ixon.Env} {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    {es : List FlatEntry} {off fuel fuel' k : Nat} {r : Ixon.Recursor} (hle : fuel ≤ fuel')
    (h : MemberRecon TyRel t E rb crb rs es off fuel k r) :
    MemberRecon TyRel t E rb crb rs es off fuel' k r := by
  obtain ⟨ty, R, bodies, cbk, hty, hR, hrel, hb, hcb, hrules⟩ := h
  exact ⟨ty, R, bodies, cbk, hty, recTypeAt_fuel_mono hle hR, hrel,
    ruleBodiesAt_fuel_mono hle hb, hcb, hrules⟩

/-- Finitely many facts each holding from some fuel on hold together from one fuel on. -/
theorem exists_fuel_bound {P : Nat → Nat → Prop} (hP : ∀ k f f', f ≤ f' → P k f → P k f') :
    ∀ n : Nat, (∀ k, k < n → ∃ f, P k f) → ∃ N, ∀ k, k < n → P k N
  | 0, _ => ⟨0, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩
  | n + 1, h => by
    obtain ⟨N, hN⟩ := exists_fuel_bound hP n (fun k hk => h k (by omega))
    obtain ⟨f, hf⟩ := h n (by omega)
    refine ⟨max N f, fun k hk => ?_⟩
    by_cases hkn : k < n
    · exact hP k N _ (Nat.le_max_left _ _) (hN k hkn)
    · have hk' : k = n := by omega
      subst hk'
      exact hP k f _ (Nat.le_max_right _ _) hf

/-- **The family record's reconstruction from its recursors one by one**: each recursor against
the reconstruction at a fuel of its own gives the record-level form at one fuel. -/
theorem recordReconWith_of_members {TyRel : KExpr → KExpr → Prop} {t : Ix.Kernel.RoleTable}
    {E : Ixon.Env} {B rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    {es : List FlatEntry} {off : Nat} (hrb : recordOf E rb = some crb) (hrs : crb.info = .muts rs)
    (hflat : RecordFlat t E rb crb rs es) (hder : BlockDerivedFlat t E B off es)
    (hm : ∀ (k : Nat) (r : Ixon.Recursor), rs[k]? = some (.recr r) →
      ∃ fuel, MemberRecon TyRel t E rb crb rs es off fuel k r) :
    RecordReconWith TyRel t E B rb := by
  have hall : ∀ k, k < rs.size → ∃ f, ∀ r : Ixon.Recursor, rs[k]? = some (.recr r) →
      MemberRecon TyRel t E rb crb rs es off f k r := by
    intro k _
    by_cases hex : ∃ r : Ixon.Recursor, rs[k]? = some (.recr r)
    · obtain ⟨r, hr⟩ := hex
      obtain ⟨f, hf⟩ := hm k r hr
      refine ⟨f, fun r' hr' => ?_⟩
      rw [hr] at hr'
      cases hr'
      exact hf
    · exact ⟨0, fun r hr => absurd ⟨r, hr⟩ hex⟩
  obtain ⟨N, hN⟩ := exists_fuel_bound
    (P := fun k f => ∀ r : Ixon.Recursor, rs[k]? = some (.recr r) →
      MemberRecon TyRel t E rb crb rs es off f k r)
    (fun k f f' hle h r hr => (h r hr).fuel_mono hle) rs.size hall
  exact ⟨crb, rs, es, off, N, hrb, hrs, hflat, hder, fun k r hr =>
    hN k (Array.getElem?_eq_some_iff.mp hr).1 r hr⟩

end IxVM.Refinement.Binding.FamilyRecon
