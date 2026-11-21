import IxVMRefinement.Assembly.NativeBlockFinalRetHead
import IxC.Kernel.Model.Inductives.NativeAtRecLate

/-! # Recursor rule `PropWhen` regime alignment for non-modeled recursors

Establishes two model-free invariants carried alongside `FamRegistryWith`:

* `RecRhsPwNoModel env`: every stored non-basis recursor without a model companion
  (`¬ HasModel env k`) has its leading `rP + rl.nfields` rule-RHS λ-binders carrying the same
  `PropWhen` datum as the recursor type's major-premise binder (`bm.2.pw = majBm.pw`).
  Holds vacuously on `basisEnv` (every basis constant is reserved), directly on native recursors
  (`DeclNativeRecLateRunJ`, via `structRecTyR`/`structRecRhsR` and `WrapRel`), and vacuously on
  modeled and twin recursors (which carry `HasModel`).
* `RecHasModelNotNative t E env`: no stored recursor carrying `HasModel` has its first-motive
  carrier (`recMotiveCarrierAt cHost rc 0 n`) naming an inductive projection of a
  native block (`NativeAt E ipP.block`). Together with `RecRhsPwNoModel`, this ensures every
  recursor of a native auxiliary family (`aux.rec`) has `¬ HasModel` and aligned rule `PropWhen`. -/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal Key RecRule Expr PropWhen)
open Ix.Kernel.Semantics (NativeFam DeclNativeRecLateRunJ NativeRecRunJ RecStoredJ NativeRecJ WrapRel)
open Ix.Kernel.Model (HasModel)

/-! ## Definitions -/

/-- Every stored non-basis recursor without a model companion has:
* all `mI` leading Π-binders of `cv.type` sharing its major-premise `PropWhen` (`majBm.pw`);
* when its level parameter list is one longer than the major premise's family level spine (large
  elimination), `cv.levelParams = elim :: rest` and `majBm.pw = .ifAllZero [elim]`;
* every rule having `.plain` or `.inert` fire mode and its leading `rP + rl.nfields` λ-binders
  sharing `majBm.pw`. -/
def RecRhsPwNoModel (env : Ix.Kernel.Env .anon) : Prop :=
  ∀ (k : Key .anon) (cv : ConstantVal .anon) (mI rP : Nat) (rls : List (RecRule .anon)),
    env.find? k = some (.recInfo cv mI rP rls) →
    Ix.Kernel.reservedBasisNames.contains k = false →
    ¬ HasModel env k →
    ∀ pre dom body majBm,
      cv.type.stripPis mI = some (pre, .forallE dom body majBm) →
      (∀ bm ∈ pre, bm.2.pw = majBm.pw) ∧
      (∀ K us, dom.getAppFn = .const K us → cv.levelParams.length = us.length + 1 →
        ∃ elim rest, cv.levelParams = elim :: rest ∧ majBm.pw = .ifAllZero [elim] ∧
          ∀ rl ∈ rls, ∃ cvC nP nF, env.find? rl.ctor = some (.ctorInfo cvC nP nF) ∧
            cvC.levelParams = rest) ∧
      ∀ rl ∈ rls, (rl.fire = .plain ∨ rl.fire = .inert) ∧
        ∃ bs rbody, rl.rhs.stripLams (rP + rl.nfields) = some (bs, rbody) ∧
          ∀ bm ∈ bs, bm.2.pw = majBm.pw

/-- `a` names a recursor record `rc` in `E`, either standalone (`.recr`) or as a mutual recursor
projection (`.rPrj`). -/
def RecRecordAt (E : Ixon.Env) (a : _root_.Address) (rc : Ixon.Recursor) : Prop :=
  (∃ c, Ix.Cert.recordAt E a = some c ∧ c.info = .recr rc) ∨
  (∃ c rp cb rs, Ix.Cert.recordAt E a = some c ∧ c.info = .rPrj rp ∧
    Ix.Cert.recordAt E rp.block = some cb ∧ cb.info = .muts rs ∧
    rs[rp.idx.toNat]? = some (.recr rc))

/-- `a` names a recursor `rc` hosted in record `cHost` in `E`, either standalone (`.recr`) or
as a mutual recursor projection (`.rPrj`) whose mutual block is `cHost`. -/
def RecHostAt (E : Ixon.Env) (a : _root_.Address) (cHost : Ixon.Constant)
    (rc : Ixon.Recursor) : Prop :=
  (Ix.Cert.recordAt E a = some cHost ∧ cHost.info = .recr rc) ∨
  (∃ c rp rs, Ix.Cert.recordAt E a = some c ∧ c.info = .rPrj rp ∧
    Ix.Cert.recordAt E rp.block = some cHost ∧ cHost.info = .muts rs ∧
    rs[rp.idx.toNat]? = some (.recr rc))

theorem recHostAt_unique {E : Ixon.Env} {a : _root_.Address}
    {c₁ c₂ : Ixon.Constant} {rc₁ rc₂ : Ixon.Recursor}
    (h₁ : RecHostAt E a c₁ rc₁) (h₂ : RecHostAt E a c₂ rc₂) :
    c₁ = c₂ ∧ rc₁ = rc₂ := by
  rcases h₁ with ⟨ha1, hi1⟩ | ⟨c1, rp1, rs1, ha1, hi1, hb1, hm1, hr1⟩
  · rcases h₂ with ⟨ha2, hi2⟩ | ⟨c2, rp2, rs2, ha2, hi2, -, -, -⟩
    · have hc : c₁ = c₂ := Option.some.inj (ha1.symm.trans ha2)
      subst hc
      rw [hi1] at hi2
      exact ⟨rfl, Ixon.ConstantInfo.recr.inj hi2⟩
    · have hc : c₁ = c2 := Option.some.inj (ha1.symm.trans ha2)
      subst hc
      rw [hi1] at hi2
      cases hi2
  · rcases h₂ with ⟨ha2, hi2⟩ | ⟨c2, rp2, rs2, ha2, hi2, hb2, hm2, hr2⟩
    · have hc : c1 = c₂ := Option.some.inj (ha1.symm.trans ha2)
      subst hc
      rw [hi1] at hi2
      cases hi2
    · have hc : c1 = c2 := Option.some.inj (ha1.symm.trans ha2)
      subst hc
      rw [hi1] at hi2
      obtain rfl := Ixon.ConstantInfo.rPrj.inj hi2
      have hcb : c₁ = c₂ := Option.some.inj (hb1.symm.trans hb2)
      subst hcb
      rw [hm1] at hm2
      obtain rfl := Ixon.ConstantInfo.muts.inj hm2
      have hrc := Option.some.inj (hr1.symm.trans hr2)
      exact ⟨rfl, Ixon.MutConst.recr.inj hrc⟩

/-- A sharing reference followed at most `n` times (matching `Binding.FamilyOf.unshare`). -/
def recUnshare (c : Ixon.Constant) : Nat → Ixon.Expr → Ixon.Expr
  | 0, e => e
  | n + 1, .share i =>
    match c.sharing[i.toNat]? with
    | some e' => recUnshare c n e'
    | none => .share i
  | _ + 1, e => e

/-- The node of an `Ixon.Expr`, sharing followed (matching `Binding.FamilyOf.node`). -/
def recNode (c : Ixon.Constant) (e : Ixon.Expr) : Ixon.Expr :=
  recUnshare c (c.sharing.size + 1) e

/-- The body after `n` leading binders (matching `Binding.FamilyOf.peel`). -/
def recPeel (c : Ixon.Constant) : Nat → Ixon.Expr → Option Ixon.Expr
  | 0, e => some e
  | n + 1, e =>
    match recNode c e with
    | .all _ b => recPeel c n b
    | _ => none

/-- The domain of the leading binder (matching `Binding.FamilyOf.domOf`). -/
def recDomOf (c : Ixon.Constant) (e : Ixon.Expr) : Option Ixon.Expr :=
  match recNode c e with
  | .all d _ => some d
  | _ => none

/-- The domain of the last leading binder, at fuel `n` (matching `Binding.FamilyOf.lastDom`). -/
def recLastDom (c : Ixon.Constant) : Nat → Ixon.Expr → Option Ixon.Expr
  | 0, _ => none
  | n + 1, e =>
    match recNode c e with
    | .all d b =>
      match recNode c b with
      | .all _ _ => recLastDom c n b
      | _ => some d
    | _ => none

/-- The head of an application spine, at fuel `n` (matching `Binding.FamilyOf.spineHead`). -/
def recSpineHead (c : Ixon.Constant) : Nat → Ixon.Expr → Ixon.Expr
  | 0, e => recNode c e
  | n + 1, e =>
    match recNode c e with
    | .app f _ => recSpineHead c n f
    | h => h

/-- The constant reference at the head of a spine, at fuel `n` (matching `Binding.FamilyOf.refHeadAt`). -/
def recRefHeadAt (c : Ixon.Constant) (n : Nat) (e : Ixon.Expr) : Option _root_.Address :=
  match recSpineHead c n e with
  | .ref i _ => c.refs[i.toNat]?
  | _ => none

/-- The carrier of motive `i` of recursor `r` in record `c` at fuel `n`
(matching `Binding.FamilyOf.motiveCarrierAt`). -/
def recMotiveCarrierAt (c : Ixon.Constant) (r : Ixon.Recursor) (i n : Nat) :
    Option _root_.Address := do
  let e ← recPeel c (r.params.toNat + i) r.typ
  let m ← recDomOf c e
  let d ← recLastDom c n m
  recRefHeadAt c n d

theorem recLastDom_mono (c : Ixon.Constant) (d : Ixon.Expr) :
    ∀ (n m : Nat) (e : Ixon.Expr), recLastDom c n e = some d → n ≤ m →
      recLastDom c m e = some d := by
  intro n
  induction n with
  | zero =>
    intro m e h _
    simp [recLastDom] at h
  | succ n ih =>
    intro m e h hle
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [recLastDom] at h ⊢
    cases hn : recNode c e with
    | all d' b =>
      simp only [hn] at h ⊢
      cases hb : recNode c b with
      | all x y =>
        simp only [hb] at h ⊢
        exact ih m b h (by omega)
      | sort _ | var _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _ | app _ _ | lam _ _
      | letE _ _ _ _ _ | share _ =>
        simp only [hb] at h ⊢
        exact h
    | sort _ | var _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _ | app _ _ | lam _ _
    | letE _ _ _ _ _ | share _ =>
      simp only [hn] at h
      cases h

theorem recSpineHead_mono (c : Ixon.Constant) :
    ∀ (n m : Nat) (e : Ixon.Expr), (∀ f a, recSpineHead c n e ≠ .app f a) → n ≤ m →
      recSpineHead c m e = recSpineHead c n e := by
  intro n
  induction n with
  | zero =>
    intro m e hna _
    cases m with
    | zero => rfl
    | succ m =>
      simp only [recSpineHead] at hna ⊢
  | succ n ih =>
    intro m e hna hle
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [recSpineHead] at hna ⊢
    cases hn : recNode c e with
    | app f a =>
      simp only [hn] at hna ⊢
      exact ih m f hna (by omega)
    | sort _ | var _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _ | lam _ _ | all _ _
    | letE _ _ _ _ _ | share _ => rfl

theorem recRefHeadAt_mono {c : Ixon.Constant} {n m : Nat} {e : Ixon.Expr} {a : _root_.Address}
    (h : recRefHeadAt c n e = some a) (hle : n ≤ m) : recRefHeadAt c m e = some a := by
  have hna : ∀ f x, recSpineHead c n e ≠ .app f x := by
    intro f x hfx
    unfold recRefHeadAt at h
    rw [hfx] at h
    simp at h
  unfold recRefHeadAt at h ⊢
  rw [recSpineHead_mono c n m e hna hle]
  exact h

theorem recMotiveCarrierAt_mono {c : Ixon.Constant} {r : Ixon.Recursor} {i n m : Nat}
    {a : _root_.Address} (h : recMotiveCarrierAt c r i n = some a) (hle : n ≤ m) :
    recMotiveCarrierAt c r i m = some a := by
  unfold recMotiveCarrierAt at h ⊢
  cases hp : recPeel c (r.params.toNat + i) r.typ with
  | none => simp [hp] at h
  | some e =>
    cases hd : recDomOf c e with
    | none => simp [hp, hd] at h
    | some mm =>
      cases hl : recLastDom c n mm with
      | none => simp [hp, hd, hl] at h
      | some d =>
        have hl' : recLastDom c m mm = some d := recLastDom_mono c d n m mm hl hle
        simp [hp, hd, hl] at h
        simp [hd, hl']
        exact recRefHeadAt_mono h hle

theorem recMotiveCarrierAt_unique {c : Ixon.Constant} {r : Ixon.Recursor} {i n n' : Nat}
    {a a' : _root_.Address} (h : recMotiveCarrierAt c r i n = some a)
    (h' : recMotiveCarrierAt c r i n' = some a') : a = a' := by
  have e1 := recMotiveCarrierAt_mono h (Nat.le_max_left n n')
  have e2 := recMotiveCarrierAt_mono h' (Nat.le_max_right n n')
  exact Option.some.inj (e1.symm.trans e2)

/-- No stored recursor with a model companion has its first-motive carrier (`recMotiveCarrierAt`
at motive `0`) naming an inductive projection of a native block. -/
def RecHasModelNotNative (t : Ix.Kernel.RoleTable) (E : Ixon.Env)
    (env : Ix.Kernel.Env .anon) : Prop :=
  ∀ (a : _root_.Address) (cv : ConstantVal .anon) (mI rP : Nat) (rls : List (RecRule .anon))
    (cHost : Ixon.Constant) (rc : Ixon.Recursor) (n : Nat) (p : _root_.Address)
    (cmP : Ixon.Constant) (ipP : Ixon.InductiveProj),
    env.find? (keyOf t a) = some (.recInfo cv mI rP rls) →
    HasModel env (keyOf t a) →
    RecHostAt E a cHost rc →
    recMotiveCarrierAt cHost rc 0 n = some p →
    Ix.Cert.recordAt E p = some cmP → cmP.info = .iPrj ipP →
    ¬ NativeAt E ipP.block

/-! ## Basis environment -/

private theorem basisEnv_rec_reserved :
    IxVM.Refinement.TableInhabit.basisEnv.consts.all (fun ci => match ci with
      | .recInfo cv _ _ _ => Ix.Kernel.reservedBasisNames.contains cv.name
      | _ => true) = true := by
  decide +kernel

private theorem basisEnv_no_model :
    IxVM.Refinement.TableInhabit.basisEnv.consts.all (fun ci => match ci.name with
      | .aux _ .model => false
      | _ => true) = true := by
  decide +kernel

theorem recRhsPwNoModel_of_reserved {env : Ix.Kernel.Env .anon}
    (hres : ∀ k cv mI rP rls, env.find? k = some (.recInfo cv mI rP rls) →
      Ix.Kernel.reservedBasisNames.contains k = true) :
    RecRhsPwNoModel env := by
  intro k cv mI rP rls hf hnr
  rw [hres k cv mI rP rls hf] at hnr
  cases hnr

theorem recRhsPwNoModel_basisEnv : RecRhsPwNoModel IxVM.Refinement.TableInhabit.basisEnv := by
  refine recRhsPwNoModel_of_reserved fun k cv mI rP rls hf => ?_
  obtain ⟨hmem, hname⟩ := basisEnv_find_mem hf
  have hall := List.all_eq_true.mp basisEnv_rec_reserved _ hmem
  have hcv : Ix.Kernel.reservedBasisNames.contains cv.name = true := hall
  have hk : cv.name = k := hname
  rw [← hk]
  exact hcv

theorem recHasModelNotNative_of_noModel {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Ix.Kernel.Env .anon}
    (hno : ∀ k cv v hint, env.find? (Ix.Kernel.auxKey k .model) ≠ some (.defnInfo cv v hint)) :
    RecHasModelNotNative t E env := by
  intro a cv mI rP rls cHost rc n p cmP ipP _ hmod
  obtain ⟨cvm, mv, hint, hfm⟩ := hmod
  exact absurd hfm (hno _ cvm mv hint)

theorem recHasModelNotNative_basisEnv (t : Ix.Kernel.RoleTable) (E : Ixon.Env) :
    RecHasModelNotNative t E IxVM.Refinement.TableInhabit.basisEnv := by
  refine recHasModelNotNative_of_noModel fun k cv v hint hf => ?_
  obtain ⟨hmem, hname⟩ := basisEnv_find_mem hf
  have hall := List.all_eq_true.mp basisEnv_no_model _ hmem
  rw [hname] at hall
  cases hall

/-! ## Generic step preservation -/

theorem recRhsPwNoModel_step {env env₂ : Ix.Kernel.Env .anon}
    (hext : Ix.Kernel.EnvExt env env₂) (h : RecRhsPwNoModel env)
    (hnew : ∀ k cv mI rP rls, env₂.find? k = some (.recInfo cv mI rP rls) →
      env.find? k = none → Ix.Kernel.reservedBasisNames.contains k = false →
      ¬ HasModel env₂ k →
      ∀ pre dom body majBm,
        cv.type.stripPis mI = some (pre, .forallE dom body majBm) →
        (∀ bm ∈ pre, bm.2.pw = majBm.pw) ∧
        (∀ K us, dom.getAppFn = .const K us → cv.levelParams.length = us.length + 1 →
          ∃ elim rest, cv.levelParams = elim :: rest ∧ majBm.pw = .ifAllZero [elim] ∧
            ∀ rl ∈ rls, ∃ cvC nP nF, env₂.find? rl.ctor = some (.ctorInfo cvC nP nF) ∧
              cvC.levelParams = rest) ∧
        ∀ rl ∈ rls, (rl.fire = .plain ∨ rl.fire = .inert) ∧
          ∃ bs rbody, rl.rhs.stripLams (rP + rl.nfields) = some (bs, rbody) ∧
            ∀ bm ∈ bs, bm.2.pw = majBm.pw) :
    RecRhsPwNoModel env₂ := by
  intro k cv mI rP rls hf hnr hnm pre dom body majBm hst
  cases hold : env.find? k with
  | none => exact hnew k cv mI rP rls hf hold hnr hnm pre dom body majBm hst
  | some ci =>
    have h₂ := hext.find hold
    rw [hf] at h₂
    obtain rfl := Option.some.inj h₂
    have hnm₀ : ¬ HasModel env k := fun hm => hnm (hm.mono (fun hfm => hext.find hfm))
    obtain ⟨hpre, hlg, hrls⟩ := h k cv mI rP rls hold hnr hnm₀ pre dom body majBm hst
    refine ⟨hpre, fun K us hfn hlen => ?_, hrls⟩
    obtain ⟨elim, rest, hlps, hpw, hctors⟩ := hlg K us hfn hlen
    refine ⟨elim, rest, hlps, hpw, fun rl hrl => ?_⟩
    obtain ⟨cvC, nP, nF, hfc, hclps⟩ := hctors rl hrl
    exact ⟨cvC, nP, nF, hext.find hfc, hclps⟩

theorem recRhsPwNoModel_noNewRec {env env₂ : Ix.Kernel.Env .anon}
    (hext : Ix.Kernel.EnvExt env env₂) (h : RecRhsPwNoModel env)
    (hno : ∀ k cv mI rP rls, env₂.find? k = some (.recInfo cv mI rP rls) →
      env.find? k = none → False) :
    RecRhsPwNoModel env₂ :=
  recRhsPwNoModel_step hext h fun k cv mI rP rls hf hold _ _ _ _ _ _ _ =>
    (hno k cv mI rP rls hf hold).elim

theorem recHasModelNotNative_step {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env env₂ : Ix.Kernel.Env .anon}
    (hext : Ix.Kernel.EnvExt env env₂) (h : RecHasModelNotNative t E env)
    (hnew : ∀ a cv mI rP rls cHost rc n p cmP ipP,
      env₂.find? (keyOf t a) = some (.recInfo cv mI rP rls) →
      HasModel env₂ (keyOf t a) →
      (env.find? (keyOf t a) = none ∨ ¬ HasModel env (keyOf t a)) →
      RecHostAt E a cHost rc →
      recMotiveCarrierAt cHost rc 0 n = some p →
      Ix.Cert.recordAt E p = some cmP → cmP.info = .iPrj ipP →
      ¬ NativeAt E ipP.block) :
    RecHasModelNotNative t E env₂ := by
  intro a cv mI rP rls cHost rc n p cmP ipP hf hm hrc hmc hcmP hipP
  cases hold : env.find? (keyOf t a) with
  | none =>
    exact hnew a cv mI rP rls cHost rc n p cmP ipP hf hm (Or.inl hold) hrc hmc hcmP hipP
  | some ci =>
    have h₂ := hext.find hold
    rw [hf] at h₂
    obtain rfl := Option.some.inj h₂
    by_cases hm₀ : HasModel env (keyOf t a)
    · exact h a cv mI rP rls cHost rc n p cmP ipP hold hm₀ hrc hmc hcmP hipP
    · exact hnew a cv mI rP rls cHost rc n p cmP ipP hf hm (Or.inr hm₀) hrc hmc hcmP hipP

theorem recHasModelNotNative_noNewModel {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env env₂ : Ix.Kernel.Env .anon}
    (hext : Ix.Kernel.EnvExt env env₂) (haux : Decl.AuxRootSynced env)
    (h : RecHasModelNotNative t E env)
    (hno : ∀ k cv v hint, env₂.find? (Ix.Kernel.auxKey k .model) = some (.defnInfo cv v hint) →
      env.find? (Ix.Kernel.auxKey k .model) = none → False) :
    RecHasModelNotNative t E env₂ := by
  refine recHasModelNotNative_step hext h ?_
  intro a cv mI rP rls cHost rc n p cmP ipP hf hm hcase
  obtain ⟨cvm, mv, hint, hfm⟩ := hm
  cases hfm₀ : env.find? (Ix.Kernel.auxKey (keyOf t a) .model) with
  | none => exact (hno _ cvm mv hint hfm hfm₀).elim
  | some ci =>
    have h₂ := hext.find hfm₀
    rw [hfm] at h₂
    obtain rfl := Option.some.inj h₂
    rcases hcase with hold | hnm₀
    · have hroot := haux (Ix.Kernel.auxKey (keyOf t a) .model) (by rw [hfm₀]; rfl)
      have hrk : (Ix.Kernel.auxKey (keyOf t a) .model).base = keyOf t a :=
        Decl.base_of_isBaseKey (Decl.isBaseKey_keyOf t a)
      rw [hrk, hold] at hroot
      exact nomatch hroot
    · exact (hnm₀ ⟨cvm, mv, hint, hfm₀⟩).elim

/-! ## `structRecTyR` / `structRecRhsR` / `WrapRel` `PropWhen` alignment -/

private theorem stripPis_replacePisPw {pw : PropWhen} :
    ∀ (k : Nat) {e b r : Expr .anon},
      Expr.replacePisPw pw k e b = some r →
      ∃ bs, r.stripPis k = some (bs, b) ∧ ∀ bm ∈ bs, bm.2.pw = pw
  | 0, _, b, r, h => by
    simp only [Expr.replacePisPw, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl, fun _ hm => nomatch hm⟩
  | k + 1, .forallE ty rest _, b, r, h => by
    simp only [Expr.replacePisPw, Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    obtain ⟨bs, hbs, hpw⟩ := stripPis_replacePisPw k hr'
    refine ⟨(ty, { pw }) :: bs, ?_, ?_⟩
    · simp [Expr.stripPis, hbs]
    · intro bm hbm
      rcases List.mem_cons.mp hbm with rfl | hbm'
      · rfl
      · exact hpw bm hbm'
  | _ + 1, .bvar _, _, _, h | _ + 1, .fvar _ _, _, _, h | _ + 1, .sort _, _, _, h
  | _ + 1, .const _ _, _, _, h | _ + 1, .app _ _, _, _, h | _ + 1, .lam _ _ _, _, _, h
  | _ + 1, .letE _ _ _ _, _, _, h | _ + 1, .lit _, _, _, h | _ + 1, .proj _ _ _, _, _, h =>
    nomatch h

private theorem stripPis_structMinorsPisR {lps : List Ix.Kernel.LevelParam} {nP : Nat}
    {pw : PropWhen} :
    ∀ (cs : List (Key .anon × Nat × Expr .anon × List Nat)) (o : Nat) {body r : Expr .anon},
      Ix.Kernel.structMinorsPisR lps nP pw cs o body = some r →
      ∃ bs, r.stripPis cs.length = some (bs, body) ∧ ∀ bm ∈ bs, bm.2.pw = pw
  | [], _, body, r, h => by
    simp only [Ix.Kernel.structMinorsPisR, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl, fun _ hm => nomatch hm⟩
  | (C, nF, cty, recIdx) :: cs, o, body, r, h => by
    simp only [Ix.Kernel.structMinorsPisR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨mty, -, r', hr', rfl⟩ := h
    obtain ⟨bs, hbs, hpw⟩ := stripPis_structMinorsPisR cs (o + 1) hr'
    refine ⟨(mty, { pw }) :: bs, ?_, ?_⟩
    · simp [Expr.stripPis, hbs]
    · intro bm hbm
      rcases List.mem_cons.mp hbm with rfl | hbm'
      · rfl
      · exact hpw bm hbm'

private theorem stripLams_pisToLamsPw {pw : PropWhen} :
    ∀ (k : Nat) {e b r : Expr .anon},
      Expr.pisToLamsPw pw k e b = some r →
      ∃ bs, r.stripLams k = some (bs, b) ∧ ∀ bm ∈ bs, bm.2.pw = pw
  | 0, _, b, r, h => by
    simp only [Expr.pisToLamsPw, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl, fun _ hm => nomatch hm⟩
  | k + 1, .forallE ty rest _, b, r, h => by
    simp only [Expr.pisToLamsPw, Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    obtain ⟨bs, hbs, hpw⟩ := stripLams_pisToLamsPw k hr'
    refine ⟨(ty, { pw }) :: bs, ?_, ?_⟩
    · simp [Expr.stripLams, hbs]
    · intro bm hbm
      rcases List.mem_cons.mp hbm with rfl | hbm'
      · rfl
      · exact hpw bm hbm'
  | _ + 1, .bvar _, _, _, h | _ + 1, .fvar _ _, _, _, h | _ + 1, .sort _, _, _, h
  | _ + 1, .const _ _, _, _, h | _ + 1, .app _ _, _, _, h | _ + 1, .lam _ _ _, _, _, h
  | _ + 1, .letE _ _ _ _, _, _, h | _ + 1, .lit _, _, _, h | _ + 1, .proj _ _ _, _, _, h =>
    nomatch h

private theorem stripLams_structMinorsLamsR {lps : List Ix.Kernel.LevelParam} {nP : Nat}
    {pw : PropWhen} :
    ∀ (cs : List (Key .anon × Nat × Expr .anon × List Nat)) (o : Nat) {body r : Expr .anon},
      Ix.Kernel.structMinorsLamsR lps nP pw cs o body = some r →
      ∃ bs, r.stripLams cs.length = some (bs, body) ∧ ∀ bm ∈ bs, bm.2.pw = pw
  | [], _, body, r, h => by
    simp only [Ix.Kernel.structMinorsLamsR, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl, fun _ hm => nomatch hm⟩
  | (C, nF, cty, recIdx) :: cs, o, body, r, h => by
    simp only [Ix.Kernel.structMinorsLamsR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨mty, -, r', hr', rfl⟩ := h
    obtain ⟨bs, hbs, hpw⟩ := stripLams_structMinorsLamsR cs (o + 1) hr'
    refine ⟨(mty, { pw }) :: bs, ?_, ?_⟩
    · simp [Expr.stripLams, hbs]
    · intro bm hbm
      rcases List.mem_cons.mp hbm with rfl | hbm'
      · rfl
      · exact hpw bm hbm'

private theorem stripLams_append :
    ∀ {m n : Nat} {e mid r : Expr .anon} {bs₁ bs₂ : List (Expr .anon × Ix.Kernel.BinderMeta)},
      e.stripLams m = some (bs₁, mid) → mid.stripLams n = some (bs₂, r) →
      e.stripLams (m + n) = some (bs₁ ++ bs₂, r)
  | 0, n, e, mid, r, bs₁, bs₂, h1, h2 => by
    simp only [Expr.stripLams, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    simpa using h2
  | m + 1, n, .lam ty b bm, mid, r, bs₁, bs₂, h1, h2 => by
    simp only [Expr.stripLams, Option.map_eq_some_iff] at h1
    obtain ⟨⟨bs₁', mid'⟩, h1', hpair⟩ := h1
    injection hpair with hbl hmid
    subst hbl hmid
    have hrec := stripLams_append h1' h2
    rw [show m + 1 + n = (m + n) + 1 by omega]
    simp [Expr.stripLams, hrec]
  | _ + 1, _, .bvar _, _, _, _, _, h1, _ | _ + 1, _, .fvar _ _, _, _, _, _, h1, _
  | _ + 1, _, .sort _, _, _, _, _, h1, _ | _ + 1, _, .const _ _, _, _, _, _, h1, _
  | _ + 1, _, .app _ _, _, _, _, _, h1, _ | _ + 1, _, .forallE _ _ _, _, _, _, _, h1, _
  | _ + 1, _, .letE _ _ _ _, _, _, _, _, h1, _ | _ + 1, _, .lit _, _, _, _, _, h1, _
  | _ + 1, _, .proj _ _ _, _, _, _, _, h1, _ => nomatch h1

private theorem structRecTyR_majPw {T : Key .anon} {lps : List Ix.Kernel.LevelParam}
    {elim : Ix.Kernel.LevelParam} {large : Bool} {nP nIdx : Nat} {tty : Expr .anon}
    {ctors : List (Key .anon × Nat × Expr .anon × List Nat)} {recTy : Expr .anon}
    (h : Ix.Kernel.structRecTyR T lps elim large nP nIdx tty ctors = some recTy) :
    ∃ pre body,
      recTy.stripPis (nP + 1 + ctors.length + nIdx) =
        some (pre, .forallE (Ix.Kernel.structFamI T lps nP nIdx (ctors.length + 1) 0) body
          { pw := Ix.Kernel.Level.zeronessOf (Ix.Kernel.structElimLevel elim large) }) ∧
      ∀ bm ∈ pre, bm.2.pw = Ix.Kernel.Level.zeronessOf (Ix.Kernel.structElimLevel elim large) := by
  unfold Ix.Kernel.structRecTyR at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨q, -, motiveTy, -, major, hmaj, minors, hmin, htop⟩ := h
  obtain ⟨bsP, hbsP, hpwP⟩ := stripPis_replacePisPw nP htop
  obtain ⟨bsM, hbsM, hpwM⟩ := stripPis_structMinorsPisR ctors 1 hmin
  obtain ⟨bsI, hbsI, hpwI⟩ := stripPis_replacePisPw nIdx hmaj
  have h1 : recTy.stripPis (nP + 1) = some (bsP ++ [(motiveTy, _)], minors) :=
    Ix.Kernel.stripPis_append nP hbsP (show (Expr.forallE motiveTy minors _).stripPis 1 = some (_, minors) from rfl)
  have h2 : recTy.stripPis (nP + 1 + ctors.length) = some ((bsP ++ [(motiveTy, _)]) ++ bsM, major) :=
    Ix.Kernel.stripPis_append (nP + 1) h1 hbsM
  have h3 := Ix.Kernel.stripPis_append (nP + 1 + ctors.length) h2 hbsI
  refine ⟨_, _, h3, fun bm hbm => ?_⟩
  rcases List.mem_append.mp hbm with h12 | hi
  · rcases List.mem_append.mp h12 with h1m | hm
    · rcases List.mem_append.mp h1m with hp | hmot
      · exact hpwP bm hp
      · obtain rfl := List.mem_singleton.mp hmot; rfl
    · exact hpwM bm hm
  · exact hpwI bm hi

private theorem structRecRhsR_lamsPw {T : Key .anon} {lps : List Ix.Kernel.LevelParam}
    {elim : Ix.Kernel.LevelParam} {large : Bool} {nP nIdx : Nat} {tty : Expr .anon}
    {ctors : List (Key .anon × Nat × Expr .anon × List Nat)} {recC : Key .anon}
    {rlvls : List Ix.Kernel.Level} {j : Nat} {cC : Key .anon} {nF : Nat} {cty : Expr .anon}
    {recIdx : List Nat} {rhs : Expr .anon}
    (hc : ctors[j]? = some (cC, nF, cty, recIdx))
    (h : Ix.Kernel.structRecRhsR T lps elim large nP nIdx tty ctors recC rlvls j = some rhs) :
    ∃ bs rbody,
      rhs.stripLams (nP + 1 + ctors.length + nF) = some (bs, rbody) ∧
      ∀ bm ∈ bs, bm.2.pw = Ix.Kernel.Level.zeronessOf (Ix.Kernel.structElimLevel elim large) := by
  unfold Ix.Kernel.structRecRhsR at h
  rw [hc] at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨tq, -, motiveTy, -, q, -, inner, hinn, minors, hmin, htop⟩ := h
  obtain ⟨bsP, hbsP, hpwP⟩ := stripLams_pisToLamsPw nP htop
  obtain ⟨bsM, hbsM, hpwM⟩ := stripLams_structMinorsLamsR ctors 1 hmin
  obtain ⟨bsF, hbsF, hpwF⟩ := stripLams_pisToLamsPw nF hinn
  have h1 : rhs.stripLams (nP + 1) = some (bsP ++ [(motiveTy, _)], minors) :=
    stripLams_append hbsP (show (Expr.lam motiveTy minors _).stripLams 1 = some (_, minors) from rfl)
  have h2 : rhs.stripLams (nP + 1 + ctors.length) = some ((bsP ++ [(motiveTy, _)]) ++ bsM, inner) :=
    stripLams_append h1 hbsM
  have h3 := stripLams_append h2 hbsF
  refine ⟨_, _, h3, ?_⟩
  intro bm hbm
  rcases List.mem_append.mp hbm with h12 | hf
  · rcases List.mem_append.mp h12 with h1m | hm
    · rcases List.mem_append.mp h1m with hp | hmot
      · exact hpwP bm hp
      · obtain rfl := List.mem_singleton.mp hmot; rfl
    · exact hpwM bm hm
  · exact hpwF bm hf

private theorem checkNativeRules_getElem? {envR : Ix.Kernel.Env .anon}
    {rlps : List Ix.Kernel.LevelParam} {T : Key .anon} {lps : List Ix.Kernel.LevelParam}
    {elim : Ix.Kernel.LevelParam} {large : Bool} {nP nIdx : Nat} {tty : Expr .anon}
    {ctors : List (Key .anon × Nat × Expr .anon × List Nat)} {recC : Key .anon}
    {rlvls : List Ix.Kernel.Level} :
    ∀ (k j : Nat) {rhss : List (Expr .anon)},
      Ix.Kernel.checkNativeRules (m := Ix.Kernel.CheckM .anon) envR rlps T lps elim large nP nIdx
        tty ctors recC rlvls k j = .ok rhss →
      rhss.length = k ∧
      ∀ idx rhs, rhss[idx]? = some rhs →
        Ix.Kernel.structRecRhsR T lps elim large nP nIdx tty ctors recC rlvls (j + idx) = some rhs
  | 0, _, rhss, h => by
    simp only [Ix.Kernel.checkNativeRules, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun _ _ hx => by simp at hx⟩
  | k + 1, j, rhss, h => by
    unfold Ix.Kernel.checkNativeRules at h
    cases hr : Ix.Kernel.structRecRhsR T lps elim large nP nIdx tty ctors recC rlvls j with
    | none => simp [hr, Ix.Kernel.unwrapOr, bind, Except.bind] at h
    | some rhs₀ =>
      simp only [hr, Ix.Kernel.unwrapOr, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases hrest : Ix.Kernel.checkNativeRules (m := Ix.Kernel.CheckM .anon) envR rlps T lps
            elim large nP nIdx tty ctors recC rlvls k (j + 1) with
        | error _ => simp [hrest] at h
        | ok rest =>
          simp only [hrest, Except.ok.injEq] at h
          subst h
          obtain ⟨hlen, hall⟩ := checkNativeRules_getElem? k (j + 1) hrest
          refine ⟨by simp [hlen], ?_⟩
          intro idx rhs hidx
          cases idx with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hidx
            subst hidx
            simpa using hr
          | succ idx' =>
            simp only [List.getElem?_cons_succ] at hidx
            rw [show j + (idx' + 1) = (j + 1) + idx' by omega]
            exact hall idx' rhs hidx
      · simp [throw, throwThe, MonadExceptOf.throw] at h

private theorem wrapRel_stripPis_majPw {find? : Key .anon → Option (ConstantInfo .anon)} :
    ∀ (m : Nat) {g d : Expr .anon} {preG domG bodyG majG preD domD bodyD majD},
      WrapRel find? g d →
      g.stripPis m = some (preG, .forallE domG bodyG majG) →
      d.stripPis m = some (preD, .forallE domD bodyD majD) →
      majG.pw = majD.pw ∧ preD.map (·.2.pw) = preG.map (·.2.pw)
  | 0, g, d, _, _, _, _, _, _, _, _, hw, hg, hd => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hg hd
    obtain ⟨rfl, rfl⟩ := hg
    obtain ⟨rfl, rfl⟩ := hd
    cases hw with
    | forallE hpw _ _ => exact ⟨hpw, rfl⟩
  | m + 1, .forallE tg bg mg, .forallE td bd md, _, _, _, _, _, _, _, _, hw, hg, hd => by
    simp only [Expr.stripPis, Option.map_eq_some_iff] at hg hd
    obtain ⟨⟨pG, rG⟩, hg', hpairG⟩ := hg
    obtain ⟨⟨pD, rD⟩, hd', hpairD⟩ := hd
    injection hpairG with hpG hrG
    injection hpairD with hpD hrD
    subst hpG hrG hpD hrD
    cases hw with
    | forallE hpw _ hwb =>
      obtain ⟨hmaj, hmap⟩ := wrapRel_stripPis_majPw m hwb hg' hd'
      exact ⟨hmaj, by simp [hpw, hmap]⟩
  | _ + 1, .bvar _, _, _, _, _, _, _, _, _, _, _, hg, _
  | _ + 1, .fvar _ _, _, _, _, _, _, _, _, _, _, _, hg, _
  | _ + 1, .sort _, _, _, _, _, _, _, _, _, _, _, hg, _
  | _ + 1, .const _ _, _, _, _, _, _, _, _, _, _, _, hg, _
  | _ + 1, .app _ _, _, _, _, _, _, _, _, _, _, _, hg, _
  | _ + 1, .lam _ _ _, _, _, _, _, _, _, _, _, _, _, hg, _
  | _ + 1, .letE _ _ _ _, _, _, _, _, _, _, _, _, _, _, hg, _
  | _ + 1, .lit _, _, _, _, _, _, _, _, _, _, _, hg, _
  | _ + 1, .proj _ _ _, _, _, _, _, _, _, _, _, _, _, hg, _ => nomatch hg
  | _ + 1, .forallE _ _ _, .bvar _, _, _, _, _, _, _, _, _, _, _, hd
  | _ + 1, .forallE _ _ _, .fvar _ _, _, _, _, _, _, _, _, _, _, _, hd
  | _ + 1, .forallE _ _ _, .sort _, _, _, _, _, _, _, _, _, _, _, hd
  | _ + 1, .forallE _ _ _, .const _ _, _, _, _, _, _, _, _, _, _, _, hd
  | _ + 1, .forallE _ _ _, .app _ _, _, _, _, _, _, _, _, _, _, _, hd
  | _ + 1, .forallE _ _ _, .lam _ _ _, _, _, _, _, _, _, _, _, _, _, hd
  | _ + 1, .forallE _ _ _, .letE _ _ _ _, _, _, _, _, _, _, _, _, _, _, hd
  | _ + 1, .forallE _ _ _, .lit _, _, _, _, _, _, _, _, _, _, _, hd
  | _ + 1, .forallE _ _ _, .proj _ _ _, _, _, _, _, _, _, _, _, _, _, hd => nomatch hd

private theorem wrapRel_stripLams_of_letFree {find? : Key .anon → Option (ConstantInfo .anon)} :
    ∀ (m : Nat) {g d : Expr .anon} {bsG : List (Expr .anon × Ix.Kernel.BinderMeta)} {rG : Expr .anon},
      WrapRel find? g d → Ix.Kernel.Semantics.letFree d = true →
      g.stripLams m = some (bsG, rG) →
      ∃ bsD rD, d.stripLams m = some (bsD, rD) ∧
        bsD.map (·.2.pw) = bsG.map (·.2.pw)
  | 0, _, d, bsG, _, _, _, hg => by
    simp only [Expr.stripLams, Option.some.injEq, Prod.mk.injEq] at hg
    obtain ⟨rfl, -⟩ := hg
    exact ⟨[], d, rfl, rfl⟩
  | m + 1, .lam tg bg mg, d, bsG, rG, hw, hlf, hg => by
    simp only [Expr.stripLams, Option.map_eq_some_iff] at hg
    obtain ⟨⟨bsG', rG'⟩, hg', hpair⟩ := hg
    injection hpair with hbs hr
    subst hbs hr
    match d, hw with
    | .lam t' b' m', .lam hpw _ hwb =>
      simp only [Ix.Kernel.Semantics.letFree, Bool.and_eq_true] at hlf
      obtain ⟨bsD', rD', hd', hmap⟩ := wrapRel_stripLams_of_letFree m hwb hlf.2 hg'
      refine ⟨(t', m') :: bsD', rD', by simp [Expr.stripLams, hd'], ?_⟩
      simp [hpw, hmap]
    | .letE _ _ _ _, .zeta _ =>
      simp [Ix.Kernel.Semantics.letFree] at hlf
  | _ + 1, .bvar _, _, _, _, _, _, hg | _ + 1, .fvar _ _, _, _, _, _, _, hg
  | _ + 1, .sort _, _, _, _, _, _, hg | _ + 1, .const _ _, _, _, _, _, _, hg
  | _ + 1, .app _ _, _, _, _, _, _, hg | _ + 1, .forallE _ _ _, _, _, _, _, _, hg
  | _ + 1, .letE _ _ _ _, _, _, _, _, _, hg | _ + 1, .lit _, _, _, _, _, _, hg
  | _ + 1, .proj _ _ _, _, _, _, _, _, hg => nomatch hg

private theorem sumRules_getElem? {find? : Key .anon → Option (ConstantInfo .anon)}
    {recName : Key .anon} {nP mI rP : Nat} {recTy : Expr .anon} :
    ∀ (ctorsA : List (ConstantVal .anon × Nat)) (rhss : List (Expr .anon)) (j : Nat)
      {rl : RecRule .anon},
      (Ix.Kernel.sumRules find? recName nP mI rP recTy ctorsA rhss)[j]? = some rl →
      ∃ cA rhs, ctorsA[j]? = some cA ∧ rhss[j]? = some rhs ∧
        rl.ctor = cA.1.name ∧ rl.nfields = cA.2 ∧ rl.rhs = rhs ∧
        (rl.fire = .plain ∨ rl.fire = .inert)
  | [], _, _, _, h => by simp [Ix.Kernel.sumRules] at h
  | _ :: _, [], _, _, h => by simp [Ix.Kernel.sumRules] at h
  | c :: cs, rhs :: rhss, 0, rl, h => by
    simp only [Ix.Kernel.sumRules, List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    refine ⟨c, rhs, rfl, rfl, rfl, rfl, rfl, ?_⟩
    simp only [Ix.Kernel.recRuleBits]
    split <;> [exact Or.inl rfl; exact Or.inr rfl]
  | _ :: cs, _ :: rhss, j + 1, rl, h => by
    simp only [Ix.Kernel.sumRules, List.getElem?_cons_succ] at h
    exact sumRules_getElem? cs rhss j h

private theorem zipWith_getElem? {α β γ : Type} (f : α → β → γ) :
    ∀ (xs : List α) (ys : List β) (j : Nat) {a : α} {b : β},
      xs[j]? = some a → ys[j]? = some b → (List.zipWith f xs ys)[j]? = some (f a b)
  | [], _, _, _, _, hx, _ => by simp at hx
  | _, [], _, _, _, _, hy => by simp at hy
  | x :: xs, y :: ys, 0, a, b, hx, hy => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
    subst hx hy
    rfl
  | _ :: xs, _ :: ys, j + 1, a, b, hx, hy => by
    simp only [List.getElem?_cons_succ] at hx hy ⊢
    exact zipWith_getElem? f xs ys j hx hy

private theorem forall₂_getElem?_right {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β} (j : Nat) {b : β},
      Ix.Kernel.Semantics.Forall₂ R xs ys → ys[j]? = some b →
      ∃ a, xs[j]? = some a ∧ R a b
  | _, _, _, _, .nil, hy => by simp at hy
  | _, _, 0, _, .cons hr _, hy => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
    subst hy
    exact ⟨_, rfl, hr⟩
  | _, _, j + 1, _, .cons _ ht, hy => by
    simp only [List.getElem?_cons_succ] at hy
    exact forall₂_getElem?_right j ht hy

private theorem forall₂_length_eq {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Ix.Kernel.Semantics.Forall₂ R xs ys → xs.length = ys.length
  | _, _, .nil => rfl
  | _, _, .cons _ ht => congrArg Nat.succ (forall₂_length_eq ht)

/-- **A late native recursor keeps `RecRhsPwNoModel`.** -/
theorem recRhsPwNoModel_late {env env₂ : Ix.Kernel.Env .anon}
    {fam : NativeFam .anon} {cvR : ConstantVal .anon} {mI rP : Nat}
    {rules : List (RecRule .anon)}
    (h : RecRhsPwNoModel env)
    (hext : Ix.Kernel.EnvExt env env₂)
    (hrun : DeclNativeRecLateRunJ Ix.Kernel.Model.rulesJ env fam cvR mI rP rules env₂) :
    RecRhsPwNoModel env₂ := by
  obtain ⟨elim, large, pR, cvRa, rhss, hpR, -, -, -, -, hstored, -, -, hRec, henv₂⟩ := hrun
  obtain ⟨cvRg, rhsG, hNatRec, hRecSt⟩ := hRec
  obtain ⟨hlpsOk, -, cvRi₀, recTy, -, hRecTy, -, -, -, -, -, hChkRules, hcvRg⟩ := hNatRec
  refine recRhsPwNoModel_step hext h ?_
  intro k cv' mI' rP' rls' hf hold _ _ pre dom body majBm hst
  rw [henv₂, Ix.Kernel.Env.find?_cons] at hf
  split at hf
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := ConstantInfo.recInfo.inj (Option.some.inj hf)
    have hlenK : fam.ctorsA.length = fam.p.kinds.length := hstored.lenK
    have hpR_nP : pR.nP = fam.p.nP := by rw [hpR]; rfl
    have hpR_nIdx : pR.nIdx = fam.p.nIdx := by rw [hpR]; rfl
    have hpR_kinds : pR.kinds = fam.p.kinds := by rw [hpR]; rfl
    have hctorsLen : (Ix.Kernel.nativeCtors4 fam.ctorsA pR.kinds).length = fam.ctorsA.length := by
      simp [Ix.Kernel.nativeCtors4, hpR_kinds, ← hlenK]
    have hpR_ctors : pR.ctors.length = fam.ctorsA.length := by
      have hlenA : fam.ctorsA.length = fam.p.ctors.length := hstored.lenA
      rw [hpR]
      exact hlenA.symm
    have hrP_eq : pR.rulePrefix = pR.nP + 1 + (Ix.Kernel.nativeCtors4 fam.ctorsA pR.kinds).length := by
      rw [hctorsLen, ← hpR_ctors]
      rfl
    have hmI_eq : pR.majorIdx = pR.nP + 1 + (Ix.Kernel.nativeCtors4 fam.ctorsA pR.kinds).length + pR.nIdx := by
      rw [← hrP_eq]
      rfl
    obtain ⟨preG, bodyG, hstG, hpreG⟩ := structRecTyR_majPw hRecTy
    obtain ⟨-, hrulesG⟩ := checkNativeRules_getElem? _ 0 hChkRules
    have hlargeOf : ∀ {lpsR : List Ix.Kernel.LevelParam},
        lpsR = pR.cvR.levelParams → lpsR.length = pR.cvT.levelParams.length + 1 →
        pR.large = true ∧ lpsR = pR.elim :: pR.cvT.levelParams := by
      intro lpsR hlps hlen
      unfold Ix.Kernel.nativeRecLpsOk at hlpsOk
      cases hlg : pR.large with
      | false =>
        simp only [hlg, Bool.false_eq_true, ↓reduceIte, beq_iff_eq] at hlpsOk
        rw [hlps, hlpsOk] at hlen
        omega
      | true =>
        simp only [hlg, ↓reduceIte, beq_iff_eq] at hlpsOk
        exact ⟨rfl, hlps.trans hlpsOk⟩
    rcases hRecSt with ⟨rfl, rfl⟩ | ⟨cvRi, -, hcvRa, hWrapTy, hWrapRhs, hlfRhs, -, -, -, hdomFn⟩
    · -- Stored directly as generated
      rw [hcvRg] at hst
      rw [hmI_eq] at hst
      rw [hstG] at hst
      injection Option.some.inj hst with hpreEq hfor
      injection hfor with hdomEq _ hmajEq
      subst hpreEq; subst hdomEq
      refine ⟨fun bm hbm => (hpreG bm hbm).trans (by rw [← hmajEq]), ?_, ?_⟩
      · intro K us hfn hlen
        have hfnG : (Ix.Kernel.structFamI pR.cvT.name pR.cvT.levelParams pR.nP pR.nIdx
            ((Ix.Kernel.nativeCtors4 fam.ctorsA pR.kinds).length + 1) 0).getAppFn =
            .const pR.cvT.name (pR.cvT.levelParams.map .param) := by
          simp [Ix.Kernel.structFamI, Ix.Kernel.Expr.getAppFn_mkAppN, Ix.Kernel.Expr.getAppFn]
        rw [hfnG] at hfn
        injection hfn with _ hus
        subst hus
        simp only [List.length_map] at hlen
        obtain ⟨hlg, hlps⟩ := hlargeOf (by rw [hcvRg]) hlen
        refine ⟨pR.elim, pR.cvT.levelParams, hlps, ?_, ?_⟩
        · rw [← hmajEq, hlg]; rfl
        · intro rl hrl
          obtain ⟨j, hj⟩ := List.getElem?_of_mem hrl
          obtain ⟨cA, _, hcA, _, hrlctor, -, -, -⟩ := sumRules_getElem? _ _ j hj
          obtain ⟨hfc, hclps, -⟩ := hstored.ctor j cA hcA
          exact ⟨cA.1, fam.p.nP, cA.2, hrlctor ▸ hext.find hfc, hclps.trans (by rw [hpR]; rfl)⟩
      · intro rl hrl
        obtain ⟨j, hj⟩ := List.getElem?_of_mem hrl
        obtain ⟨cA, rhs, hcA, hrhs, _, hrnf, hrlrhs, hfire⟩ := sumRules_getElem? _ _ j hj
        have hj_lt : j < fam.ctorsA.length := (List.getElem?_eq_some_iff.mp hcA).1
        have hks_j : pR.kinds[j]? = some (pR.kinds[j]'(by rw [hpR_kinds, ← hlenK]; exact hj_lt)) :=
          List.getElem?_eq_getElem (by rw [hpR_kinds, ← hlenK]; exact hj_lt)
        have hct4_j : (Ix.Kernel.nativeCtors4 fam.ctorsA pR.kinds)[j]? =
            some (cA.1.name, cA.2, cA.1.type, Ix.Kernel.recIdxOf (pR.kinds[j]'(by rw [hpR_kinds, ← hlenK]; exact hj_lt))) :=
          zipWith_getElem? _ _ _ j hcA hks_j
        have hrhsG := hrulesG j rhs hrhs
        rw [Nat.zero_add] at hrhsG
        obtain ⟨bs, rbody, hsl, hpw⟩ := structRecRhsR_lamsPw hct4_j hrhsG
        refine ⟨hfire, bs, rbody, ?_, fun bm hbm => (hpw bm hbm).trans (by rw [← hmajEq])⟩
        rw [hrP_eq, hrnf, hrlrhs]
        exact hsl
    · -- Stored as declared, related to generated by `WrapRel`
      have hst_orig : cvRi.type.stripPis pR.majorIdx = some (pre, .forallE dom body majBm) := by
        rw [hcvRa] at hst; exact hst
      rw [hcvRa] at hst
      rw [hmI_eq] at hst
      rw [hcvRg] at hWrapTy
      obtain ⟨hmajEq, hpreMap⟩ := wrapRel_stripPis_majPw _ hWrapTy hstG hst
      refine ⟨?_, ?_, ?_⟩
      · intro bm hbm
        have hmem : bm.2.pw ∈ pre.map (·.2.pw) := List.mem_map.mpr ⟨bm, hbm, rfl⟩
        rw [hpreMap] at hmem
        obtain ⟨bmG, hbmG, hpwEq⟩ := List.mem_map.mp hmem
        exact hpwEq.symm.trans ((hpreG bmG hbmG).trans hmajEq)
      · intro K us hfn hlen
        obtain ⟨K', hfn'⟩ := hdomFn pre dom body majBm hst_orig
        rw [hfn'] at hfn
        injection hfn with _ hus
        subst hus
        simp only [List.length_map] at hlen
        obtain ⟨hlg, hlps⟩ := hlargeOf (by rw [hcvRa]) hlen
        refine ⟨pR.elim, pR.cvT.levelParams, hlps, ?_, ?_⟩
        · rw [← hmajEq, hlg]; rfl
        · intro rl hrl
          obtain ⟨j, hj⟩ := List.getElem?_of_mem hrl
          obtain ⟨cA, _, hcA, _, hrlctor, -, -, -⟩ := sumRules_getElem? _ _ j hj
          obtain ⟨hfc, hclps, -⟩ := hstored.ctor j cA hcA
          exact ⟨cA.1, fam.p.nP, cA.2, hrlctor ▸ hext.find hfc, hclps.trans (by rw [hpR]; rfl)⟩
      · intro rl hrl
        obtain ⟨j, hj⟩ := List.getElem?_of_mem hrl
        obtain ⟨cA, rhs, hcA, hrhs, _, hrnf, hrlrhs, hfire⟩ := sumRules_getElem? _ _ j hj
        have hj_lt : j < fam.ctorsA.length := (List.getElem?_eq_some_iff.mp hcA).1
        have hks_j : pR.kinds[j]? = some (pR.kinds[j]'(by rw [hpR_kinds, ← hlenK]; exact hj_lt)) :=
          List.getElem?_eq_getElem (by rw [hpR_kinds, ← hlenK]; exact hj_lt)
        have hct4_j : (Ix.Kernel.nativeCtors4 fam.ctorsA pR.kinds)[j]? =
            some (cA.1.name, cA.2, cA.1.type, Ix.Kernel.recIdxOf (pR.kinds[j]'(by rw [hpR_kinds, ← hlenK]; exact hj_lt))) :=
          zipWith_getElem? _ _ _ j hcA hks_j
        obtain ⟨rhsG_j, hrhsG_j, hwrap_j⟩ := forall₂_getElem?_right j hWrapRhs hrhs
        have hrhsG := hrulesG j rhsG_j hrhsG_j
        rw [Nat.zero_add] at hrhsG
        obtain ⟨bsG, rbodyG, hslG, hpwG⟩ := structRecRhsR_lamsPw hct4_j hrhsG
        have hlf_j : Ix.Kernel.Semantics.letFree rhs = true := hlfRhs rhs (List.mem_of_getElem? hrhs)
        obtain ⟨bsD, rbodyD, hslD, hmap⟩ := wrapRel_stripLams_of_letFree _ hwrap_j hlf_j hslG
        refine ⟨hfire, bsD, rbodyD, ?_, ?_⟩
        · rw [hrP_eq, hrnf, hrlrhs]
          exact hslD
        · intro bm hbm
          have hmem : bm.2.pw ∈ bsD.map (·.2.pw) := List.mem_map.mpr ⟨bm, hbm, rfl⟩
          rw [hmap] at hmem
          obtain ⟨bmG, hbmG, hpwEq⟩ := List.mem_map.mp hmem
          exact hpwEq.symm.trans ((hpwG bmG hbmG).trans hmajEq)
  · rw [hf] at hold
    exact nomatch hold

/-! ## Convenience preservation helpers -/

theorem recRhsPwNoModel_cons_noRec {env : Ix.Kernel.Env .anon} {ci : ConstantInfo .anon}
    (hext : Ix.Kernel.EnvExt env ⟨ci :: env.consts⟩) (h : RecRhsPwNoModel env)
    (hrec : ∀ cv mI rP rls, ci ≠ .recInfo cv mI rP rls) :
    RecRhsPwNoModel ⟨ci :: env.consts⟩ :=
  recRhsPwNoModel_noNewRec hext h fun k cv mI rP rls hf hold => by
    rw [Ix.Kernel.Env.find?_cons] at hf
    split at hf
    · exact hrec cv mI rP rls (Option.some.inj hf)
    · rw [hf] at hold; cases hold

theorem recHasModelNotNative_cons_noRecNoModel {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {ci : ConstantInfo .anon}
    (hext : Ix.Kernel.EnvExt env ⟨ci :: env.consts⟩) (h : RecHasModelNotNative t E env)
    (hrec : ∀ cv mI rP rls, ci ≠ .recInfo cv mI rP rls)
    (hmod : ∀ k, ci.name ≠ Ix.Kernel.auxKey k .model) :
    RecHasModelNotNative t E ⟨ci :: env.consts⟩ :=
  recHasModelNotNative_step hext h fun a cv mI rP rls _ _ _ _ _ _ hf hm hcase => by
    exfalso
    rcases hcase with hold | hnm₀
    · rw [Ix.Kernel.Env.find?_cons] at hf
      split at hf
      · exact hrec cv mI rP rls (Option.some.inj hf)
      · rw [hf] at hold; cases hold
    · obtain ⟨cvm, mv, hint, hfm⟩ := hm
      rw [Ix.Kernel.Env.find?_cons] at hfm
      split at hfm
      · rename_i heq
        have hname : ci.name = Ix.Kernel.auxKey (keyOf t a) .model := by simpa using heq
        exact hmod (keyOf t a) hname
      · exact hnm₀ ⟨cvm, mv, hint, hfm⟩

theorem recRhsPwNoModel_append_noRec {env env₂ : Ix.Kernel.Env .anon}
    (hext : Ix.Kernel.EnvExt env env₂) (h : RecRhsPwNoModel env)
    (hno : ∃ new : List (ConstantInfo .anon), env₂ = ⟨new ++ env.consts⟩ ∧
      ∀ ci ∈ new, ∀ cv mI rP rls, ci ≠ .recInfo cv mI rP rls) :
    RecRhsPwNoModel env₂ := by
  obtain ⟨new, rfl, hno⟩ := hno
  refine recRhsPwNoModel_noNewRec hext h fun k cv mI rP rls hf hold => ?_
  rcases find?_append_cases new hf with hm | ho
  · exact hno _ hm cv mI rP rls rfl
  · rw [hold] at ho; cases ho

theorem recHasModelNotNative_append_noRecNoDefn {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env env₂ : Ix.Kernel.Env .anon}
    (hext : Ix.Kernel.EnvExt env env₂) (h : RecHasModelNotNative t E env)
    (hno : ∃ new : List (ConstantInfo .anon), env₂ = ⟨new ++ env.consts⟩ ∧
      ∀ ci ∈ new, (∀ cv mI rP rls, ci ≠ .recInfo cv mI rP rls) ∧
        (∀ cv v hint, ci ≠ .defnInfo cv v hint)) :
    RecHasModelNotNative t E env₂ := by
  obtain ⟨new, rfl, hno⟩ := hno
  refine recHasModelNotNative_step hext h fun a cv mI rP rls _ _ _ _ _ _ hf hm hcase => by
    exfalso
    rcases hcase with hold | hnm₀
    · rcases find?_append_cases new hf with hm' | ho
      · exact (hno _ hm').1 cv mI rP rls rfl
      · rw [hold] at ho; cases ho
    · obtain ⟨cvm, mv, hint, hfm⟩ := hm
      rcases find?_append_cases new hfm with hm' | ho
      · exact (hno _ hm').2 cvm mv hint rfl
      · exact hnm₀ ⟨cvm, mv, hint, ho⟩

/-- Every newly stored recursor of `env₂` has non-native first-motive carrier at `E`. -/
def NewRecNotNative (t : Ix.Kernel.RoleTable) (E : Ixon.Env)
    (env env₂ : Ix.Kernel.Env .anon) : Prop :=
  ∀ (a : _root_.Address) (cv : ConstantVal .anon) (mI rP : Nat) (rls : List (RecRule .anon))
    (cHost : Ixon.Constant) (rc : Ixon.Recursor) (n : Nat) (p : _root_.Address)
    (cmP : Ixon.Constant) (ipP : Ixon.InductiveProj),
    env₂.find? (keyOf t a) = some (.recInfo cv mI rP rls) →
    env.find? (keyOf t a) = none →
    RecHostAt E a cHost rc →
    recMotiveCarrierAt cHost rc 0 n = some p →
    Ix.Cert.recordAt E p = some cmP → cmP.info = .iPrj ipP →
    ¬ NativeAt E ipP.block

theorem recNotNative_of_motiveCarrierAt {E : Ixon.Env}
    {B p₀ p : _root_.Address} {cHost : Ixon.Constant} {rc : Ixon.Recursor}
    {n₀ n : Nat} {cm0 cmP : Ixon.Constant} {ip0 ipP : Ixon.InductiveProj}
    (hmc₀ : recMotiveCarrierAt cHost rc 0 n₀ = some p₀)
    (hmc : recMotiveCarrierAt cHost rc 0 n = some p)
    (hcm0 : Ix.Cert.recordAt E p₀ = some cm0) (hip0 : cm0.info = .iPrj ip0)
    (hblk0 : ip0.block = B)
    (hcmP : Ix.Cert.recordAt E p = some cmP) (hipP : cmP.info = .iPrj ipP)
    (hnotNatB : ¬ NativeAt E B) :
    ¬ NativeAt E ipP.block := by
  have hp : p = p₀ := recMotiveCarrierAt_unique hmc hmc₀
  subst hp
  have hcm : cmP = cm0 := Option.some.inj (hcmP.symm.trans hcm0)
  rw [hcm, hip0] at hipP
  have hip : ipP = ip0 := (Ixon.ConstantInfo.iPrj.inj hipP).symm
  rw [hip, hblk0]
  exact hnotNatB

theorem recNotNative_of_familyKey {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {B p : _root_.Address} {rc : Ixon.Recursor} {ty mdom dom : Core.KExpr}
    {cmP : Ixon.Constant} {ipP : Ixon.InductiveProj} {us : List Core.KLevel}
    (htwf : t.wf = true)
    (hfk : familyKey rc ty = some (keyOf t (Core.iprjAddr B 0)))
    (hpi : Core.piDomAt rc.params.toNat ty = some mdom)
    (hld : lastBinderDom mdom = some dom)
    (hfn : dom.getAppFn = .const (keyOf t p) us)
    (hrecB0 : ∃ cm0 ip0, Ix.Cert.recordAt E (Core.iprjAddr B 0) = some cm0 ∧
      cm0.info = .iPrj ip0 ∧ ip0.block = B)
    (hcmP : Ix.Cert.recordAt E p = some cmP) (hipP : cmP.info = .iPrj ipP)
    (hnotNatB : ¬ NativeAt E B) :
    ¬ NativeAt E ipP.block := by
  obtain ⟨bs, B', m', hst⟩ := (Decl.piDomAt_eq_some_iff _ _ _).mp hpi
  unfold familyKey binderDom headKey at hfk
  rw [hst] at hfk
  simp only [Option.bind_some] at hfk
  rw [hld] at hfk
  simp only [Option.bind_some] at hfk
  rw [hfn] at hfk
  simp only [Option.some.injEq] at hfk
  have hp : p = Core.iprjAddr B 0 := Core.keyOf_inj htwf hfk
  subst hp
  obtain ⟨cm0, ip0, hcm0, hip0, hblk0⟩ := hrecB0
  have hcm : cmP = cm0 := Option.some.inj (hcmP.symm.trans hcm0)
  rw [hcm, hip0] at hipP
  have hip : ipP = ip0 := (Ixon.ConstantInfo.iPrj.inj hipP).symm
  rw [hip, hblk0]
  exact hnotNatB

end IxVM.Refinement.Typing
