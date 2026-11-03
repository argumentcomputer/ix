import Ix.Cert.IxVM.CodecBridge
import Ix.Cert.IxVM.KernelBridge
import Ix.Cert.CompileCorrectProof

/-! # Fuel-Free Inductive `IxVM` Kernel Semantics & End-to-End Compiler Commutation

In Formal Aiur (`Ix/IxVM/Kernel/*.lean`), the kernel functions `whnf_core`, `whnf`,
`k_is_def_eq`, `k_infer`, `k_infer_only`, `k_ensure_sort`, and `check_const` do
**not** carry a global `fuel : Nat` parameter: their execution in Aiur's big-step
semantics is an inductive derivation tree in which each recursive sub-call
succeeds at its own finite derivation height.

This module defines the fuel-free big-step inductive judgments:
* `IxVMWhnfCoreStep`, `IxVMWhnfStep`, `IxVMDefEqStep`, `IxVMInferStep`,
  `IxVMInferIOStep`, `IxVMEnsureSortStep`, `IxVMAnnotateStep`
* `IxVMCheckConstantValStep`, `IxVMCheckDefnValStep`, `IxVMCheckThmValStep`,
  `IxVMCheckOpaqueValStep`, `IxVMCheckDeclStep`, `IxVMFuelFreeWalkDecls`

and proves:
1. **Multi-Call Fuel Composition**: Using `whnfCore_mono`, `whnf_mono`,
   `isDefEqCore_mono`, `inferTypeCore_mono`, `inferTypeIO_mono`, `ensureSortCore_mono`,
   `annotateCore_mono`, and `checkDecl_mono`, sub-derivations at potentially
   distinct fuels $F_1, F_2, \dots$ compose via $\max(F_1, F_2, \dots)$ to yield
   a single uniform fuel at which `IxC`'s fueled specification succeeds.
2. **Fuel-Free Declaration Check Equivalence (`ixvmCheckDeclStep_iff_checkConstRef`,
   `ixvmFuelFreeWalkDecls_iff_acceptsRef`)**: `IxVMCheckDeclStep` is equivalent to
   `IxVMCheckConstRef`, and `IxVMFuelFreeWalkDecls` from `Env.empty` is equivalent
   to `Cached.AcceptsRef`.
3. **End-to-End Compiler + `IxVM` Commutation (`ixvm_compile_commutes`,
   `ixvm_compile_commutes_checked`, `ixvm_compile_commutes_nominal`)**:
   Combining `Ix.Cert.ReaderStreamsTrace.compileCorrect` with the `IxVM` ↔ `IxC`
   acceptance bridge (`ixvm_accepts_iff_ixonAcceptsRef`), when `SourceAcceptsQ`
   holds on a Lean closure, `compileReport` has `NoFailure`, `artifactCheck`
   passes, and `IxVMAcceptsClaim` holds on the compiled closure, any `StrongModel`
   of the `IxVM`-accepted Ixon environment pulls back via `readingAt` to a
   `LawModel` and `ValueModel` of the source Lean environment.
-/

namespace Ix.Cert.IxVM

open Ix.Kernel
open Ix.Kernel.Cached
open Ix.Kernel.Admission

universe w

/-! ## 1. Fuel-Free Big-Step Kernel Judgments (`IxVMWhnfStep`, `IxVMDefEqStep`, `IxVMInferStep`, `IxVMInferIOStep`) -/

/-- Fuel-free big-step head normalization without delta (`IxVM` `Whnf::whnf_core`).
Multi-call branches (such as `betaGated`) allow each sub-call to have its own
independent derivation height. -/
inductive IxVMWhnfCoreStep (mode : CheckMode) (env : Env md) :
    Nat → Kernel.Expr md → Kernel.Expr md → Prop where
  | valSort (d : Nat) (u : Kernel.Level) :
      IxVMWhnfCoreStep mode env d (.sort u) (.sort u)
  | valFVar (d idx : Nat) (ty : Kernel.Expr md) :
      IxVMWhnfCoreStep mode env d (.fvar idx ty) (.fvar idx ty)
  | valForall (d : Nat) (ty body : Kernel.Expr md) (bi : BinderMeta) :
      IxVMWhnfCoreStep mode env d (.forallE ty body bi) (.forallE ty body bi)
  | valLam (d : Nat) (ty body : Kernel.Expr md) (mb : BinderMeta) :
      IxVMWhnfCoreStep mode env d (.lam ty body mb) (.lam ty body mb)
  | valConst (d : Nat) (n : Key md) (us : List Kernel.Level) :
      IxVMWhnfCoreStep mode env d (.const n us) (.const n us)
  | valLit (d : Nat) (l : Literal) :
      IxVMWhnfCoreStep mode env d (.lit l) (.lit l)
  | betaGated {d : Nat} {f a ty body v : Kernel.Expr md} {mb : BinderMeta}
      (hf : IxVMWhnfCoreStep mode env d f (.lam ty body mb))
      (hgate : betaGateFires mode mb.pw = Bool.true)
      (hbody : IxVMWhnfCoreStep mode env d (body.instantiate1 a) v) :
      IxVMWhnfCoreStep mode env d (.app f a) v
  | step {F d : Nat} {e v : Kernel.Expr md}
      (h : whnfCoreBody mode (pureFns mode env F) env d e = .ok v) :
      IxVMWhnfCoreStep mode env d e v

/-- **Equivalence of Fuel-Free `IxVMWhnfCoreStep` and Fueled `whnfCore`**:
Sub-derivations at potentially different fuels compose via `max F₁ F₂ + 1`. -/
theorem ixvmWhnfCoreStep_iff {mode : CheckMode} {env : Env md} {d : Nat}
    {e v : Kernel.Expr md} :
    IxVMWhnfCoreStep mode env d e v ↔ ∃ F, whnfCore mode env F d e = .ok v := by
  constructor
  · intro h
    induction h with
    | valSort d u => exact ⟨1, rfl⟩
    | valFVar d idx ty => exact ⟨1, rfl⟩
    | valForall d ty body bi => exact ⟨1, rfl⟩
    | valLam d ty body mb => exact ⟨1, rfl⟩
    | valConst d n us => exact ⟨1, rfl⟩
    | valLit d l => exact ⟨1, rfl⟩
    | @betaGated d f a ty body v mb _ hgate _ ihf ihbody =>
      obtain ⟨F₁, hF₁⟩ := ihf
      obtain ⟨F₂, hF₂⟩ := ihbody
      let F := max F₁ F₂
      have hF₁' : (pureFns mode env F).whnfCore d f = .ok (.lam ty body mb) :=
        whnfCore_mono (Nat.le_max_left F₁ F₂) hF₁
      have hF₂' : (pureFns mode env F).whnfCore d (body.instantiate1 a) = .ok v :=
        whnfCore_mono (Nat.le_max_right F₁ F₂) hF₂
      refine ⟨F + 1, ?_⟩
      rw [whnfCore_succ]
      unfold whnfCoreBody
      dsimp only
      rw [hF₁']
      dsimp only [bind, Except.bind]
      simp only [hgate, ↓reduceIte, hF₂']
    | @step F d e v h =>
      exact ⟨F + 1, h⟩
  · rintro ⟨F, hF⟩
    cases F with
    | zero =>
      rw [whnfCore_zero] at hF
      cases hF
    | succ F =>
      exact .step hF

/-- Fuel-free big-step full weak-head normalization (`IxVM` `Whnf::whnf`).
Includes value rules, multi-call `Nat.succ` fast path (where sub-derivations of
`whnfCore` and `whnf` on the argument have independent derivation heights), and
general open-recursion steps. -/
inductive IxVMWhnfStep (mode : CheckMode) (env : Env md) :
    Nat → Kernel.Expr md → Kernel.Expr md → Prop where
  | valSort (d : Nat) (u : Kernel.Level) :
      IxVMWhnfStep mode env d (.sort u) (.sort u)
  | valFVar (d idx : Nat) (ty : Kernel.Expr md) :
      IxVMWhnfStep mode env d (.fvar idx ty) (.fvar idx ty)
  | valForall (d : Nat) (ty body : Kernel.Expr md) (bi : BinderMeta) :
      IxVMWhnfStep mode env d (.forallE ty body bi) (.forallE ty body bi)
  | valLam (d : Nat) (ty body : Kernel.Expr md) (mb : BinderMeta) :
      IxVMWhnfStep mode env d (.lam ty body mb) (.lam ty body mb)
  | valLit (d : Nat) (l : Literal) :
      IxVMWhnfStep mode env d (.lit l) (.lit l)
  | natSucc {d n : Nat} {e a : Kernel.Expr md}
      (hsup : natLitSupported env)
      (hc : IxVMWhnfCoreStep mode env d e (.app (.const natSuccName []) a))
      (ha : IxVMWhnfStep mode env d a (.lit (.natVal n))) :
      IxVMWhnfStep mode env d e (.lit (.natVal (n + 1)))
  | step {F d : Nat} {e v : Kernel.Expr md}
      (h : whnfBody (pureFns mode env F) env d e = .ok v) :
      IxVMWhnfStep mode env d e v

/-- **Equivalence of Fuel-Free `IxVMWhnfStep` and Fueled `whnf`**:
Multi-call branches (such as `natSucc`, combining `IxVMWhnfCoreStep` at fuel $F_1$
and `IxVMWhnfStep` at fuel $F_2$) compose via `max F₁ F₂ + 1`. -/
theorem ixvmWhnfStep_iff {mode : CheckMode} {env : Env md} {d : Nat}
    {e v : Kernel.Expr md} :
    IxVMWhnfStep mode env d e v ↔ ∃ F, whnf mode env F d e = .ok v := by
  constructor
  · intro h
    induction h with
    | valSort d u =>
      refine ⟨2, ?_⟩
      obtain ⟨n, hn⟩ := whnfLoopFuel_succ
      rw [whnf_succ]; unfold whnfBody; rw [hn, whnfLoop]
      unfold whnfStep; rfl
    | valFVar d idx ty =>
      refine ⟨2, ?_⟩
      obtain ⟨n, hn⟩ := whnfLoopFuel_succ
      rw [whnf_succ]; unfold whnfBody; rw [hn, whnfLoop]
      unfold whnfStep; rfl
    | valForall d ty body bi =>
      refine ⟨2, ?_⟩
      obtain ⟨n, hn⟩ := whnfLoopFuel_succ
      rw [whnf_succ]; unfold whnfBody; rw [hn, whnfLoop]
      unfold whnfStep; rfl
    | valLam d ty body mb =>
      refine ⟨2, ?_⟩
      obtain ⟨n, hn⟩ := whnfLoopFuel_succ
      rw [whnf_succ]; unfold whnfBody; rw [hn, whnfLoop]
      unfold whnfStep; rfl
    | valLit d l =>
      refine ⟨2, ?_⟩
      obtain ⟨n, hn⟩ := whnfLoopFuel_succ
      rw [whnf_succ]; unfold whnfBody; rw [hn, whnfLoop]
      unfold whnfStep; rfl
    | @natSucc d k e a hsup hc _ iha =>
      obtain ⟨F₁, hF₁⟩ := ixvmWhnfCoreStep_iff.mp hc
      obtain ⟨F₂, hF₂⟩ := iha
      let F := max F₁ F₂ + 1
      have hF₁' : (pureFns mode env F).whnfCore d e = .ok (.app (.const natSuccName []) a) :=
        whnfCore_mono (Nat.le_trans (Nat.le_max_left F₁ F₂) (Nat.le_succ _)) hF₁
      have hF₂' : whnf mode env F d a = .ok (.lit (.natVal k)) :=
        whnf_mono (Nat.le_trans (Nat.le_max_right F₁ F₂) (Nat.le_succ _)) hF₂
      have hred := ixvm_natPrim_succ_sound hsup hF₂'
      refine ⟨F + 1, ?_⟩
      rw [whnf_succ]
      unfold whnfBody
      obtain ⟨n, hn⟩ : ∃ n, whnfLoopFuel = n + 2 := ⟨99998, by unfold whnfLoopFuel; rfl⟩
      rw [hn, whnfLoop]
      unfold whnfStep
      rw [hF₁']
      dsimp only [bind, Except.bind]
      rw [hred]
      dsimp only [bind, Except.bind]
      rw [whnfLoop]
      unfold whnfStep
      have hlit : (pureFns mode env F).whnfCore d (.lit (.natVal (k + 1))) =
          .ok (.lit (.natVal (k + 1))) := rfl
      rw [hlit]
      rfl
    | @step F d e v h =>
      exact ⟨F + 1, h⟩
  · rintro ⟨F, hF⟩
    cases F with
    | zero =>
      rw [whnf_zero] at hF
      cases hF
    | succ F =>
      exact .step hF

/-- Fuel-free big-step definitional equality (`IxVM` `DefEq::k_is_def_eq`).
Includes syntactic reflexivity, the `boolTrueShortcut` branch, multi-call
`whnfCoreEq` (where `a` and `b` head-normalize to the same expression `w` at
independent derivation heights), and general open-recursion steps. -/
inductive IxVMDefEqStep (mode : CheckMode) (env : Env md) :
    Nat → Kernel.Expr md → Kernel.Expr md → Bool → Prop where
  | refl (d : Nat) (e : Kernel.Expr md) :
      IxVMDefEqStep mode env d e e Bool.true
  | boolTrue {d : Nat} {a b w : Kernel.Expr md}
      (hb : b.isBoolTrue = Bool.true)
      (hfv : a.hasFvar = Bool.false)
      (hw : IxVMWhnfStep mode env d a w)
      (hwbt : w.isBoolTrue = Bool.true) :
      IxVMDefEqStep mode env d a b Bool.true
  | whnfCoreEq {d : Nat} {a b w : Kernel.Expr md}
      (hb : b.isBoolTrue = Bool.false)
      (ha : IxVMWhnfCoreStep mode env d a w)
      (hbw : IxVMWhnfCoreStep mode env d b w) :
      IxVMDefEqStep mode env d a b Bool.true
  | step {F d : Nat} {a b : Kernel.Expr md} {v : Bool}
      (h : defeqBody mode (pureFns mode env F) env d a b = .ok v) :
      IxVMDefEqStep mode env d a b v

/-- **Equivalence of Fuel-Free `IxVMDefEqStep` and Fueled `isDefEqCore`**:
Multi-call branches (such as `whnfCoreEq` with independent `whnfCore` fuels $F_1, F_2$)
compose via `max F₁ F₂ + 1`. -/
theorem ixvmDefEqStep_iff {mode : CheckMode} {env : Env md} {d : Nat}
    {a b : Kernel.Expr md} {v : Bool} :
    IxVMDefEqStep mode env d a b v ↔ ∃ F, isDefEqCore mode env F d a b = .ok v := by
  constructor
  · intro h
    induction h with
    | refl d e =>
      refine ⟨1, ?_⟩
      obtain ⟨n, hn⟩ : ∃ n, defeqLoopFuel = n + 1 := ⟨99999, by unfold defeqLoopFuel; rfl⟩
      rw [isDefEqCore_succ]
      unfold defeqBody
      rw [hn, defeqLoop]
      unfold defeqStep
      simp only [beq_self_eq_true, ↓reduceIte]
      rfl
    | @boolTrue d a b w hb hfv hw hwbt =>
      obtain ⟨F, hF⟩ := ixvmWhnfStep_iff.mp hw
      have hF' : (pureFns mode env F).whnf d a = .ok w := hF
      refine ⟨F + 1, ?_⟩
      obtain ⟨n, hn⟩ : ∃ n, defeqLoopFuel = n + 1 := ⟨99999, by unfold defeqLoopFuel; rfl⟩
      rw [isDefEqCore_succ]
      unfold defeqBody
      rw [hn, defeqLoop]
      unfold defeqStep
      by_cases hab : (a == b) = Bool.true
      · simp only [hab, ↓reduceIte]
        rfl
      · have hab' : (a == b) = Bool.false := Bool.eq_false_iff.mpr hab
        simp only [hab', Bool.false_eq_true, ↓reduceIte, hb, hfv, Bool.and_self, Bool.not_false]
        unfold boolTrueShortcut
        rw [hF']
        dsimp only [bind, Except.bind, pure, Except.pure]
        simp only [hwbt, ↓reduceIte]
    | @whnfCoreEq d a b w hb ha hbw =>
      obtain ⟨F₁, hF₁⟩ := ixvmWhnfCoreStep_iff.mp ha
      obtain ⟨F₂, hF₂⟩ := ixvmWhnfCoreStep_iff.mp hbw
      let F := max F₁ F₂
      have hF₁' : (pureFns mode env F).whnfCore d a = .ok w :=
        whnfCore_mono (Nat.le_max_left F₁ F₂) hF₁
      have hF₂' : (pureFns mode env F).whnfCore d b = .ok w :=
        whnfCore_mono (Nat.le_max_right F₁ F₂) hF₂
      refine ⟨F + 1, ?_⟩
      obtain ⟨n, hn⟩ : ∃ n, defeqLoopFuel = n + 1 := ⟨99999, by unfold defeqLoopFuel; rfl⟩
      rw [isDefEqCore_succ]
      unfold defeqBody
      rw [hn, defeqLoop]
      unfold defeqStep
      by_cases hab : (a == b) = Bool.true
      · simp only [hab, ↓reduceIte]
        rfl
      · have hab' : (a == b) = Bool.false := Bool.eq_false_iff.mpr hab
        simp only [hab', Bool.false_eq_true, ↓reduceIte, hb, Bool.and_false, Bool.false_and]
        dsimp only [bind, Except.bind, pure, Except.pure]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hF₁']
        dsimp only [bind, Except.bind]
        rw [hF₂']
        dsimp only [bind, Except.bind]
        simp only [beq_self_eq_true, ↓reduceIte]
    | @step F d a b v h =>
      exact ⟨F + 1, h⟩
  · rintro ⟨F, hF⟩
    cases F with
    | zero =>
      rw [isDefEqCore_zero] at hF
      cases hF
    | succ F =>
      exact .step hF

/-- Fuel-free big-step `ensure_sort` (`IxVM` `Infer::ensure_sort`):
`e` weak-head normalizes to `.sort u`. -/
inductive IxVMEnsureSortStep (mode : CheckMode) (env : Env md) :
    Nat → Kernel.Expr md → Kernel.Level → Prop where
  | mk {d : Nat} {e : Kernel.Expr md} {u : Kernel.Level}
      (hw : IxVMWhnfStep mode env d e (.sort u)) :
      IxVMEnsureSortStep mode env d e u

/-- **Equivalence of Fuel-Free `IxVMEnsureSortStep` and Fueled `ensureSortCore`**. -/
theorem ixvmEnsureSortStep_iff {mode : CheckMode} {env : Env md} {d : Nat}
    {e : Kernel.Expr md} {u : Kernel.Level} :
    IxVMEnsureSortStep mode env d e u ↔ ∃ F, ensureSortCore mode env F d e = .ok u := by
  constructor
  · rintro ⟨hw⟩
    obtain ⟨F, hF⟩ := ixvmWhnfStep_iff.mp hw
    refine ⟨F, ?_⟩
    unfold ensureSortCore ensureSort
    change (whnf mode env F d e >>= fun w =>
      match w with
      | .sort u => pure u
      | _ => throw (.invalid "expected a sort")) = .ok u
    rw [hF]
    rfl
  · rintro ⟨F, hF⟩
    unfold ensureSortCore ensureSort at hF
    change (whnf mode env F d e >>= fun w =>
      match w with
      | .sort u => pure u
      | _ => throw (.invalid "expected a sort")) = .ok u at hF
    cases hw : whnf mode env F d e with
    | error err => simp [hw, bind, Except.bind] at hF
    | ok w =>
      rw [hw] at hF
      dsimp only [bind, Except.bind] at hF
      cases w <;> try cases hF
      exact ⟨ixvmWhnfStep_iff.mpr ⟨F, hw⟩⟩

/-- Fuel-free big-step full type inference (`IxVM` `Infer::k_infer`).
In multi-call branches (`forallE` with 4 sub-derivations and `app` with 4
sub-derivations), each recursive call has its own independent derivation tree. -/
inductive IxVMInferStep (mode : CheckMode) (env : Env md) :
    Nat → Kernel.Expr md → Kernel.Expr md → Prop where
  | sort (d : Nat) (u : Kernel.Level) :
      IxVMInferStep mode env d (.sort u) (.sort (.succ u))
  | fvar (d idx : Nat) (ty : Kernel.Expr md) (h : idx < d) :
      IxVMInferStep mode env d (.fvar idx ty) ty
  | const (d : Nat) (n : Key md) (us : List Kernel.Level) (ci : Kernel.ConstantInfo md)
      (hfind : env.find? n = some ci)
      (htower : (!ci.isTowerEntry) = Bool.true)
      (hlen : us.length = ci.toConstantVal.levelParams.length) :
      IxVMInferStep mode env d (.const n us)
        (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us)
  | natLit (d n : Nat) (hsup : natLitSupported env) :
      IxVMInferStep mode env d (.lit (.natVal n)) (.const natName [])
  | strLit (d : Nat) (s : String) (hsup : strLitSupported env) :
      IxVMInferStep mode env d (.lit (.strVal s)) (.const stringName [])
  | forallE {d : Nat} {ty body sty bty : Kernel.Expr md} {mb : BinderMeta}
      {u v : Kernel.Level}
      (hty : IxVMInferStep mode env d ty sty)
      (hwty : IxVMWhnfStep mode env d sty (.sort u))
      (hbody : IxVMInferStep mode env (d + 1) (body.instantiate1 (.fvar d ty)) bty)
      (hsort : IxVMEnsureSortStep mode env (d + 1) bty v)
      (hpw : mode.verifiedChecks = Bool.true → (Level.zeronessOf v == mb.pw) = Bool.true) :
      IxVMInferStep mode env d (.forallE ty body mb) (.sort (.imax u v))
  | app {d : Nat} {f a tf ty body ta : Kernel.Expr md} {mt : BinderMeta}
      (hf : IxVMInferStep mode env d f tf)
      (hwtf : IxVMWhnfStep mode env d tf (.forallE ty body mt))
      (ha : IxVMInferStep mode env d a ta)
      (hdefeq : IxVMDefEqStep mode env d ta ty Bool.true) :
      IxVMInferStep mode env d (.app f a) (body.instantiate1 a)
  | step {F d : Nat} {e v : Kernel.Expr md}
      (h : inferBody mode (pureFns mode env F) env d e = .ok v) :
      IxVMInferStep mode env d e v

/-- **Equivalence of Fuel-Free `IxVMInferStep` and Fueled `inferTypeCore`**:
Multi-call rules (`forallE` and `app`) compose their 4 sub-derivation fuels
$F_1, F_2, F_3, F_4$ via $\max(\max(F_1, F_2), \max(F_3, F_4)) + 1$. -/
theorem ixvmInferStep_iff {mode : CheckMode} {env : Env md} {d : Nat}
    {e v : Kernel.Expr md} :
    IxVMInferStep mode env d e v ↔ ∃ F, inferTypeCore mode env F d e = .ok v := by
  constructor
  · intro h
    induction h with
    | sort d u => exact ⟨1, rfl⟩
    | fvar d idx ty hlt =>
      refine ⟨1, ?_⟩
      rw [inferTypeCore_succ]
      unfold inferBody
      simp only [hlt, ↓reduceIte]
      rfl
    | const d n us ci hfind htower hlen =>
      refine ⟨1, ?_⟩
      rw [inferTypeCore_succ]
      unfold inferBody
      dsimp only
      rw [hfind]
      dsimp only
      simp only [htower, hlen, ↓reduceIte]
      rfl
    | natLit d n hsup =>
      refine ⟨1, ?_⟩
      rw [inferTypeCore_succ]
      unfold inferBody
      simp only [hsup, ↓reduceIte]
      rfl
    | strLit d s hsup =>
      refine ⟨1, ?_⟩
      rw [inferTypeCore_succ]
      unfold inferBody
      simp only [hsup, ↓reduceIte]
      rfl
    | @forallE d ty body sty bty mb u v _ hwty _ hsort hpw ihty ihbody =>
      obtain ⟨F₁, hF₁⟩ := ihty
      obtain ⟨F₂, hF₂⟩ := ixvmWhnfStep_iff.mp hwty
      obtain ⟨F₃, hF₃⟩ := ihbody
      obtain ⟨F₄, hF₄⟩ := ixvmEnsureSortStep_iff.mp hsort
      let F := max (max F₁ F₂) (max F₃ F₄)
      have hle₁ : F₁ ≤ F := Nat.le_trans (Nat.le_max_left F₁ F₂) (Nat.le_max_left _ _)
      have hle₂ : F₂ ≤ F := Nat.le_trans (Nat.le_max_right F₁ F₂) (Nat.le_max_left _ _)
      have hle₃ : F₃ ≤ F := Nat.le_trans (Nat.le_max_left F₃ F₄) (Nat.le_max_right _ _)
      have hle₄ : F₄ ≤ F := Nat.le_trans (Nat.le_max_right F₃ F₄) (Nat.le_max_right _ _)
      have hF₁' : (pureFns mode env F).infer d ty = .ok sty := inferTypeCore_mono hle₁ hF₁
      have hF₂' : (pureFns mode env F).whnf d sty = .ok (.sort u) := whnf_mono hle₂ hF₂
      have hF₃' : (pureFns mode env F).infer (d + 1) (body.instantiate1 (.fvar d ty)) = .ok bty :=
        inferTypeCore_mono hle₃ hF₃
      have hF₄' : ensureSort (pureFns mode env F) env (d + 1) bty = .ok v :=
        ensureSortCore_mono hle₄ hF₄
      refine ⟨F + 1, ?_⟩
      rw [inferTypeCore_succ]
      unfold inferBody
      dsimp only
      rw [hF₁']
      dsimp only [bind, Except.bind]
      rw [hF₂']
      dsimp only [bind, Except.bind]
      rw [hF₃']
      dsimp only [bind, Except.bind]
      rw [hF₄']
      dsimp only [bind, Except.bind]
      cases hvc : mode.verifiedChecks with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rfl
      | true =>
        simp only [↓reduceIte, hpw hvc]
        rfl
    | @app d f a tf ty body ta mt _ hwtf _ hdefeq ihf iha =>
      obtain ⟨F₁, hF₁⟩ := ihf
      obtain ⟨F₂, hF₂⟩ := ixvmWhnfStep_iff.mp hwtf
      obtain ⟨F₃, hF₃⟩ := iha
      obtain ⟨F₄, hF₄⟩ := ixvmDefEqStep_iff.mp hdefeq
      let F := max (max F₁ F₂) (max F₃ F₄)
      have hle₁ : F₁ ≤ F := Nat.le_trans (Nat.le_max_left F₁ F₂) (Nat.le_max_left _ _)
      have hle₂ : F₂ ≤ F := Nat.le_trans (Nat.le_max_right F₁ F₂) (Nat.le_max_left _ _)
      have hle₃ : F₃ ≤ F := Nat.le_trans (Nat.le_max_left F₃ F₄) (Nat.le_max_right _ _)
      have hle₄ : F₄ ≤ F := Nat.le_trans (Nat.le_max_right F₃ F₄) (Nat.le_max_right _ _)
      have hF₁' : (pureFns mode env F).infer d f = .ok tf := inferTypeCore_mono hle₁ hF₁
      have hF₂' : (pureFns mode env F).whnf d tf = .ok (.forallE ty body mt) := whnf_mono hle₂ hF₂
      have hF₃' : (pureFns mode env F).infer d a = .ok ta := inferTypeCore_mono hle₃ hF₃
      have hF₄' : (pureFns mode env F).defeq d ta ty = .ok Bool.true := isDefEqCore_mono hle₄ hF₄
      refine ⟨F + 1, ?_⟩
      rw [inferTypeCore_succ]
      unfold inferBody
      dsimp only
      rw [hF₁']
      dsimp only [bind, Except.bind]
      rw [hF₂']
      dsimp only [bind, Except.bind]
      rw [hF₃']
      dsimp only [bind, Except.bind]
      rw [hF₄']
      rfl
    | @step F d e v h =>
      exact ⟨F + 1, h⟩
  · rintro ⟨F, hF⟩
    cases F with
    | zero =>
      rw [inferTypeCore_zero] at hF
      cases hF
    | succ F =>
      exact .step hF

/-- Fuel-free big-step infer-only type inference (`IxVM` `InferOnly::k_infer_only`).
Includes the `appNever` fast path (where `mt.pw.isNever = true` skips argument
inference and `defeq` at `.verified`) and the `appChecked` path (with 4
independent sub-derivations). -/
inductive IxVMInferIOStep (mode : CheckMode) (env : Env md) :
    Nat → Kernel.Expr md → Kernel.Expr md → Prop where
  | sort (d : Nat) (u : Kernel.Level) :
      IxVMInferIOStep mode env d (.sort u) (.sort (.succ u))
  | fvar (d idx : Nat) (ty : Kernel.Expr md) (h : idx < d) :
      IxVMInferIOStep mode env d (.fvar idx ty) ty
  | appNever {d : Nat} {f a tf ty body : Kernel.Expr md} {mt : BinderMeta}
      (hgate : mode.betaGate = Bool.true)
      (hf : IxVMInferIOStep mode env d f tf)
      (hwtf : IxVMWhnfStep mode env d tf (.forallE ty body mt))
      (hnever : mt.pw.isNever = Bool.true) :
      IxVMInferIOStep mode env d (.app f a) (body.instantiate1 a)
  | appChecked {d : Nat} {f a tf ty body ta : Kernel.Expr md} {mt : BinderMeta}
      (hgate : mode.betaGate = Bool.true)
      (hf : IxVMInferIOStep mode env d f tf)
      (hwtf : IxVMWhnfStep mode env d tf (.forallE ty body mt))
      (ha : IxVMInferIOStep mode env d a ta)
      (hdefeq : IxVMDefEqStep mode env d ta ty Bool.true) :
      IxVMInferIOStep mode env d (.app f a) (body.instantiate1 a)
  | step {F d : Nat} {e v : Kernel.Expr md}
      (h : inferTypeIO mode env (F + 1) d e = .ok v) :
      IxVMInferIOStep mode env d e v

/-- **Equivalence of Fuel-Free `IxVMInferIOStep` and Fueled `inferTypeIO`**:
Both `appNever` (composing 2 sub-derivations via `max F₁ F₂ + 1`) and
`appChecked` (composing 4 sub-derivations via `max (max F₁ F₂) (max F₃ F₄) + 1`)
produce a single fuel at which `inferTypeIO` succeeds. -/
theorem ixvmInferIOStep_iff {mode : CheckMode} {env : Env md} {d : Nat}
    {e v : Kernel.Expr md} :
    IxVMInferIOStep mode env d e v ↔ ∃ F, inferTypeIO mode env F d e = .ok v := by
  constructor
  · intro h
    induction h with
    | sort d u =>
      refine ⟨1, ?_⟩
      rw [inferTypeIO_succ]
      cases mode.betaGate <;> rfl
    | fvar d idx ty hlt =>
      refine ⟨1, ?_⟩
      rw [inferTypeIO_succ]
      cases mode.betaGate <;> (dsimp only [inferBodyIO, inferBody]; simp only [hlt, ↓reduceIte]; rfl)
    | @appNever d f a tf ty body mt hgate _ hwtf hnever ihf =>
      obtain ⟨F₁, hF₁⟩ := ihf
      obtain ⟨F₂, hF₂⟩ := ixvmWhnfStep_iff.mp hwtf
      let F := max F₁ F₂
      have hF₁' : (CoreFns.ioView (pureFns mode env F)).infer d f = .ok tf :=
        inferTypeIO_mono (Nat.le_max_left F₁ F₂) hF₁
      have hF₂' : (CoreFns.ioView (pureFns mode env F)).whnf d tf = .ok (.forallE ty body mt) :=
        whnf_mono (Nat.le_max_right F₁ F₂) hF₂
      refine ⟨F + 1, ?_⟩
      rw [inferTypeIO_succ]
      simp only [hgate, ↓reduceIte]
      unfold inferBodyIO
      dsimp only
      rw [hF₁']
      dsimp only [bind, Except.bind]
      rw [hF₂']
      dsimp only [bind, Except.bind]
      simp only [hnever, ↓reduceIte]
      rfl
    | @appChecked d f a tf ty body ta mt hgate _ hwtf _ hdefeq ihf iha =>
      obtain ⟨F₁, hF₁⟩ := ihf
      obtain ⟨F₂, hF₂⟩ := ixvmWhnfStep_iff.mp hwtf
      obtain ⟨F₃, hF₃⟩ := iha
      obtain ⟨F₄, hF₄⟩ := ixvmDefEqStep_iff.mp hdefeq
      let F := max (max F₁ F₂) (max F₃ F₄)
      have hle₁ : F₁ ≤ F := Nat.le_trans (Nat.le_max_left F₁ F₂) (Nat.le_max_left _ _)
      have hle₂ : F₂ ≤ F := Nat.le_trans (Nat.le_max_right F₁ F₂) (Nat.le_max_left _ _)
      have hle₃ : F₃ ≤ F := Nat.le_trans (Nat.le_max_left F₃ F₄) (Nat.le_max_right _ _)
      have hle₄ : F₄ ≤ F := Nat.le_trans (Nat.le_max_right F₃ F₄) (Nat.le_max_right _ _)
      have hF₁' : (CoreFns.ioView (pureFns mode env F)).infer d f = .ok tf :=
        inferTypeIO_mono hle₁ hF₁
      have hF₂' : (CoreFns.ioView (pureFns mode env F)).whnf d tf = .ok (.forallE ty body mt) :=
        whnf_mono hle₂ hF₂
      have hF₃' : (CoreFns.ioView (pureFns mode env F)).infer d a = .ok ta :=
        inferTypeIO_mono hle₃ hF₃
      have hF₄' : (CoreFns.ioView (pureFns mode env F)).defeq d ta ty = .ok Bool.true :=
        isDefEqCore_mono hle₄ hF₄
      refine ⟨F + 1, ?_⟩
      rw [inferTypeIO_succ]
      simp only [hgate, ↓reduceIte]
      unfold inferBodyIO
      dsimp only
      rw [hF₁']
      dsimp only [bind, Except.bind]
      rw [hF₂']
      dsimp only [bind, Except.bind]
      cases mt.pw.isNever with
      | true => rfl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hF₃']
        dsimp only [bind, Except.bind]
        rw [hF₄']
        rfl
    | @step F d e v h =>
      exact ⟨F + 1, h⟩
  · rintro ⟨F, hF⟩
    cases F with
    | zero =>
      rw [inferTypeIO_zero] at hF
      cases hF
    | succ F =>
      exact .step hF

/-- Fuel-free big-step annotation pass (`annotateCore`), including multi-call
`app` (2 sub-derivations) and `letE` (`infer_let` triple + ζ-reduct annotation:
7 sub-derivations at potentially distinct fuels). -/
inductive IxVMAnnotateStep (mode : CheckMode) (env : Env md) :
    Nat → Kernel.Expr md → Kernel.Expr md → Prop where
  | bvar (d i : Nat) :
      IxVMAnnotateStep mode env d (.bvar i) (.bvar i)
  | fvar (d idx : Nat) (ty : Kernel.Expr md) (h : idx < d) :
      IxVMAnnotateStep mode env d (.fvar idx ty) (.fvar idx ty)
  | sort (d : Nat) (u : Kernel.Level) :
      IxVMAnnotateStep mode env d (.sort u) (.sort u)
  | const (d : Nat) (n : Key md) (us : List Kernel.Level) :
      IxVMAnnotateStep mode env d (.const n us) (.const n us)
  | app {d : Nat} {f a f' a' : Kernel.Expr md}
      (hf : IxVMAnnotateStep mode env d f f')
      (ha : IxVMAnnotateStep mode env d a a') :
      IxVMAnnotateStep mode env d (.app f a) (.app f' a')
  | letE {d : Nat} {ty v b ty' sty' v' tv b' : Kernel.Expr md} {u : Kernel.Level} {nondep : LetMeta}
      (hty : IxVMAnnotateStep mode env d ty ty')
      (hity : IxVMInferStep mode env d ty' sty')
      (hsort : IxVMEnsureSortStep mode env d sty' u)
      (hv : IxVMAnnotateStep mode env d v v')
      (hiv : IxVMInferStep mode env d v' tv)
      (hdefeq : IxVMDefEqStep mode env d tv ty' Bool.true)
      (hb : IxVMAnnotateStep mode env d (b.instantiate1 v) b') :
      IxVMAnnotateStep mode env d (.letE ty v b nondep) b'
  | step {F d : Nat} {e v : Kernel.Expr md}
      (h : annotateBody (pureFns mode env F) env d e = .ok v) :
      IxVMAnnotateStep mode env d e v

/-- **Equivalence of Fuel-Free `IxVMAnnotateStep` and Fueled `annotateCore`**:
Multi-call branches (`app` and `letE` with 7 sub-derivations across `annotate`,
`infer`, `ensureSort`, and `defeq`) compose via `max` into a single fuel `F + 1`. -/
theorem ixvmAnnotateStep_iff {mode : CheckMode} {env : Env md} {d : Nat}
    {e v : Kernel.Expr md} :
    IxVMAnnotateStep mode env d e v ↔ ∃ F, annotateCore mode env F d e = .ok v := by
  constructor
  · intro h
    induction h with
    | bvar d i => exact ⟨1, rfl⟩
    | fvar d idx ty hlt =>
      refine ⟨1, ?_⟩
      rw [annotateCore_succ]
      unfold annotateBody
      simp only [hlt, ↓reduceIte]
      rfl
    | sort d u => exact ⟨1, rfl⟩
    | const d n us => exact ⟨1, rfl⟩
    | @app d f a f' a' _ _ ihf iha =>
      obtain ⟨F₁, hF₁⟩ := ihf
      obtain ⟨F₂, hF₂⟩ := iha
      let F := max F₁ F₂
      have hF₁' : (pureFns mode env F).annotate d f = .ok f' :=
        annotateCore_mono (Nat.le_max_left F₁ F₂) hF₁
      have hF₂' : (pureFns mode env F).annotate d a = .ok a' :=
        annotateCore_mono (Nat.le_max_right F₁ F₂) hF₂
      refine ⟨F + 1, ?_⟩
      rw [annotateCore_succ]
      unfold annotateBody
      dsimp only
      rw [hF₁']
      dsimp only [bind, Except.bind]
      rw [hF₂']
      rfl
    | @letE d ty val b ty' sty' val' tv b' u nondep _ hity hsort _ hiv hdefeq _ ihty ihv ihb =>
      obtain ⟨F₁, hF₁⟩ := ihty
      obtain ⟨F₂, hF₂⟩ := ixvmInferStep_iff.mp hity
      obtain ⟨F₃, hF₃⟩ := ixvmEnsureSortStep_iff.mp hsort
      obtain ⟨F₄, hF₄⟩ := ihv
      obtain ⟨F₅, hF₅⟩ := ixvmInferStep_iff.mp hiv
      obtain ⟨F₆, hF₆⟩ := ixvmDefEqStep_iff.mp hdefeq
      obtain ⟨F₇, hF₇⟩ := ihb
      let F_left := max (max F₁ F₂) (max F₃ F₄)
      let F_right := max (max F₅ F₆) F₇
      let F := max F_left F_right
      have hle₁ : F₁ ≤ F :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_left F₁ F₂) (Nat.le_max_left _ _)) (Nat.le_max_left _ _)
      have hle₂ : F₂ ≤ F :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_right F₁ F₂) (Nat.le_max_left _ _)) (Nat.le_max_left _ _)
      have hle₃ : F₃ ≤ F :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_left F₃ F₄) (Nat.le_max_right _ _)) (Nat.le_max_left _ _)
      have hle₄ : F₄ ≤ F :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_right F₃ F₄) (Nat.le_max_right _ _)) (Nat.le_max_left _ _)
      have hle₅ : F₅ ≤ F :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_left F₅ F₆) (Nat.le_max_left _ _)) (Nat.le_max_right _ _)
      have hle₆ : F₆ ≤ F :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_right F₅ F₆) (Nat.le_max_left _ _)) (Nat.le_max_right _ _)
      have hle₇ : F₇ ≤ F :=
        Nat.le_trans (Nat.le_max_right _ F₇) (Nat.le_max_right _ _)
      have hF₁' : (pureFns mode env F).annotate d ty = .ok ty' := annotateCore_mono hle₁ hF₁
      have hF₂' : (pureFns mode env F).infer d ty' = .ok sty' := inferTypeCore_mono hle₂ hF₂
      have hF₃' : ensureSort (pureFns mode env F) env d sty' = .ok u := ensureSortCore_mono hle₃ hF₃
      have hF₄' : (pureFns mode env F).annotate d val = .ok val' := annotateCore_mono hle₄ hF₄
      have hF₅' : (pureFns mode env F).infer d val' = .ok tv := inferTypeCore_mono hle₅ hF₅
      have hF₆' : (pureFns mode env F).defeq d tv ty' = .ok Bool.true := isDefEqCore_mono hle₆ hF₆
      have hF₇' : (pureFns mode env F).annotate d (b.instantiate1 val) = .ok b' :=
        annotateCore_mono hle₇ hF₇
      refine ⟨F + 1, ?_⟩
      rw [annotateCore_succ]
      unfold annotateBody
      dsimp only
      rw [hF₁']
      dsimp only [bind, Except.bind]
      rw [hF₂']
      dsimp only [bind, Except.bind]
      rw [hF₃']
      dsimp only [bind, Except.bind]
      rw [hF₄']
      dsimp only [bind, Except.bind]
      rw [hF₅']
      dsimp only [bind, Except.bind]
      rw [hF₆']
      dsimp only [bind, Except.bind, ↓reduceIte, pure, Except.pure]
      exact hF₇'
    | @step F d e v h =>
      exact ⟨F + 1, h⟩
  · rintro ⟨F, hF⟩
    cases F with
    | zero =>
      rw [annotateCore_zero] at hF
      cases hF
    | succ F =>
      exact .step hF

/-! ## 2. Fuel-Free Declaration Checking (`IxVMCheckDeclStep` ↔ `IxVMCheckConstRef`) -/

/-- Fuel-free big-step header check for a constant's type (`checkConstantVal`):
`annotate`, `inferType`, and `ensureSort` each have their own fuel-free derivation. -/
inductive IxVMCheckConstantValStep (mode : CheckMode) (env : Env md)
    (cv cv' : Kernel.ConstantVal md) : Prop where
  | mk {type' stype : Kernel.Expr md} {sortLvl : Kernel.Level}
      (fresh : (env.find? cv.name).isSome = Bool.false)
      (notReserved : reservedBasisNames.contains cv.name = Bool.false)
      (notProjFn : cv.name.isProjFnShape = Bool.false)
      (nodupLvls : LevelParam.nodup cv.levelParams = Bool.true)
      (closedType : cv.type.looseBVarsBounded 0 = Bool.true)
      (noFvarType : cv.type.hasFvar = Bool.false)
      (annotType : IxVMAnnotateStep mode env 0 cv.type type')
      (lvlParamsOk : type'.allLevelParamsDefined cv.levelParams = Bool.true)
      (constsOk : type'.constsResolve env = Bool.true)
      (inferType : IxVMInferStep mode env 0 type' stype)
      (ensureSort : IxVMEnsureSortStep mode env 0 stype sortLvl)
      (out_eq : cv' = { cv with type := type' }) :
      IxVMCheckConstantValStep mode env cv cv'

/-- Every `IxVMCheckConstantValStep` succeeds at all fuels `F` above the max of
its 3 sub-derivation fuels. -/
theorem IxVMCheckConstantValStep.eval_at_large_fuel {mode : CheckMode} {env : Env md}
    {cv cv' : Kernel.ConstantVal md} (h : IxVMCheckConstantValStep mode env cv cv') :
    ∃ F₀, ∀ F, F₀ ≤ F → checkConstantVal (fueledOps mode F) env cv = .ok cv' := by
  cases h with
  | @mk type' stype u hfr hres hprj hnd hcl hfv hannot hlvl hcon hinf hsort out_eq =>
    subst out_eq
    obtain ⟨F₁, hF₁⟩ := ixvmAnnotateStep_iff.mp hannot
    obtain ⟨F₂, hF₂⟩ := ixvmInferStep_iff.mp hinf
    obtain ⟨F₃, hF₃⟩ := ixvmEnsureSortStep_iff.mp hsort
    refine ⟨max F₁ (max F₂ F₃), fun F hle => ?_⟩
    have hF₁' : (fueledOps mode F).annotate env 0 cv.type = .ok type' :=
      annotateCore_mono (Nat.le_trans (Nat.le_max_left F₁ _) hle) hF₁
    have hF₂' : (fueledOps mode F).inferType env 0 type' = .ok stype :=
      inferTypeCore_mono (Nat.le_trans (Nat.le_trans (Nat.le_max_left F₂ F₃) (Nat.le_max_right F₁ _)) hle) hF₂
    have hF₃' : (fueledOps mode F).ensureSort env 0 stype = .ok u :=
      ensureSortCore_mono (Nat.le_trans (Nat.le_trans (Nat.le_max_right F₂ F₃) (Nat.le_max_right F₁ _)) hle) hF₃
    unfold checkConstantVal
    simp only [hfr, hres, hprj, hnd, hcl, hfv, Bool.false_eq_true, ↓reduceIte,
      bind, Except.bind, pure, Except.pure]
    rw [hF₁']
    dsimp only
    simp only [hlvl, hcon, ↓reduceIte]
    rw [hF₂']
    dsimp only
    rw [hF₃']

/-- **Equivalence of Fuel-Free `IxVMCheckConstantValStep` and Fueled `checkConstantVal`**:
The 3 independent fuel witnesses ($F_1$ for `annotate`, $F_2$ for `infer`,
$F_3$ for `ensureSort`) compose via $\max(F_1, \max(F_2, F_3))$. -/
theorem ixvmCheckConstantValStep_iff {mode : CheckMode} {env : Env md}
    {cv cv' : Kernel.ConstantVal md} :
    IxVMCheckConstantValStep mode env cv cv' ↔
      ∃ F, checkConstantVal (fueledOps mode F) env cv = .ok cv' := by
  constructor
  · intro h
    obtain ⟨F₀, hF₀⟩ := h.eval_at_large_fuel
    exact ⟨F₀, hF₀ F₀ (Nat.le_refl F₀)⟩
  · rintro ⟨F, hF⟩
    obtain ⟨hfind0, hres, hprj, hnd, hcl, hfv, type', stype, u,
      hannot, hlvl, hcon, hinf, hsort, hout⟩ := checkConstantVal_inv hF
    have hfr : (env.find? cv.name).isSome = Bool.false := by
      rw [hfind0]; rfl
    exact ⟨hfr, hres, hprj, hnd, hcl, hfv,
      ixvmAnnotateStep_iff.mpr ⟨F, hannot⟩, hlvl, hcon,
      ixvmInferStep_iff.mpr ⟨F, hinf⟩,
      ixvmEnsureSortStep_iff.mpr ⟨F, hsort⟩, hout⟩

/-- Fuel-free big-step value check for a `def` (`checkDefnVal`):
`annotate`, `inferType`, and `isDefEq` on the definition's value each have
their own independent fuel-free derivation. -/
inductive IxVMCheckDefnValStep (mode : CheckMode) (env : Env md)
    (cv : Kernel.ConstantVal md) (value : Kernel.Expr md) (hint : ReducibilityHint)
    (env' : Env md) : Prop where
  | mk {value' vtype : Kernel.Expr md}
      (closedVal : value.looseBVarsBounded 0 = Bool.true)
      (noFvarVal : value.hasFvar = Bool.false)
      (annotVal : IxVMAnnotateStep mode env 0 value value')
      (lvlParamsOk : value'.allLevelParamsDefined cv.levelParams = Bool.true)
      (constsOk : value'.constsResolve env = Bool.true)
      (inferVal : IxVMInferStep mode env 0 value' vtype)
      (defeqType : IxVMDefEqStep mode env 0 vtype cv.type Bool.true)
      (out_eq : env' = ⟨.defnInfo cv value' hint :: env.consts⟩) :
      IxVMCheckDefnValStep mode env cv value hint env'

/-- Every `IxVMCheckDefnValStep` succeeds at all fuels `F` above the max of
its 3 sub-derivation fuels. -/
theorem IxVMCheckDefnValStep.eval_at_large_fuel {mode : CheckMode} {env : Env md}
    {cv : Kernel.ConstantVal md} {value : Kernel.Expr md} {hint : ReducibilityHint}
    {env' : Env md} (h : IxVMCheckDefnValStep mode env cv value hint env') :
    ∃ F₀, ∀ F, F₀ ≤ F → checkDefnVal (fueledOps mode F) env cv value hint = .ok env' := by
  cases h with
  | @mk value' vtype hcl hfv hannot hlvl hcon hinf hdef out_eq =>
    subst out_eq
    obtain ⟨F₁, hF₁⟩ := ixvmAnnotateStep_iff.mp hannot
    obtain ⟨F₂, hF₂⟩ := ixvmInferStep_iff.mp hinf
    obtain ⟨F₃, hF₃⟩ := ixvmDefEqStep_iff.mp hdef
    refine ⟨max F₁ (max F₂ F₃), fun F hle => ?_⟩
    have hF₁' : (fueledOps mode F).annotate env 0 value = .ok value' :=
      annotateCore_mono (Nat.le_trans (Nat.le_max_left F₁ _) hle) hF₁
    have hF₂' : (fueledOps mode F).inferType env 0 value' = .ok vtype :=
      inferTypeCore_mono (Nat.le_trans (Nat.le_trans (Nat.le_max_left F₂ F₃) (Nat.le_max_right F₁ _)) hle) hF₂
    have hF₃' : (fueledOps mode F).isDefEq env 0 vtype cv.type = .ok Bool.true :=
      isDefEqCore_mono (Nat.le_trans (Nat.le_trans (Nat.le_max_right F₂ F₃) (Nat.le_max_right F₁ _)) hle) hF₃
    unfold checkDefnVal
    simp only [hcl, hfv, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure]
    rw [hF₁']
    dsimp only
    simp only [hlvl, hcon, ↓reduceIte]
    rw [hF₂']
    dsimp only
    rw [hF₃']
    rfl

/-- **Equivalence of Fuel-Free `IxVMCheckDefnValStep` and Fueled `checkDefnVal`**:
The 3 independent fuel witnesses ($F_1$ for `annotate`, $F_2$ for `infer`,
$F_3$ for `defeq`) compose via $\max(F_1, \max(F_2, F_3))$. -/
theorem ixvmCheckDefnValStep_iff {mode : CheckMode} {env : Env md}
    {cv : Kernel.ConstantVal md} {value : Kernel.Expr md} {hint : ReducibilityHint}
    {env' : Env md} :
    IxVMCheckDefnValStep mode env cv value hint env' ↔
      ∃ F, checkDefnVal (fueledOps mode F) env cv value hint = .ok env' := by
  constructor
  · intro h
    obtain ⟨F₀, hF₀⟩ := h.eval_at_large_fuel
    exact ⟨F₀, hF₀ F₀ (Nat.le_refl F₀)⟩
  · rintro ⟨F, hF⟩
    simp only [checkDefnVal, fueledOps_annotate, fueledOps_inferType, fueledOps_isDefEq,
      Bind.bind, Except.bind, Pure.pure, Except.pure] at hF
    by_cases hcl : value.looseBVarsBounded 0 = Bool.true
    case neg => simp [hcl] at hF
    simp only [hcl, ↓reduceIte] at hF
    by_cases hfv : value.hasFvar = Bool.true
    case pos => simp [hfv] at hF
    have hfvF : value.hasFvar = Bool.false := Bool.eq_false_iff.mpr hfv
    simp only [hfvF, Bool.false_eq_true, ↓reduceIte] at hF
    cases hannot : annotateCore mode env F 0 value with
    | error e => rw [hannot] at hF; exact nomatch hF
    | ok value' =>
      rw [hannot] at hF
      dsimp only at hF
      by_cases hlvl : value'.allLevelParamsDefined cv.levelParams = Bool.true
      case neg => simp [hlvl] at hF
      simp only [hlvl, ↓reduceIte] at hF
      by_cases hcon : value'.constsResolve env = Bool.true
      case neg => simp [hcon] at hF
      simp only [hcon, ↓reduceIte] at hF
      cases hinf : inferTypeCore mode env F 0 value' with
      | error e => rw [hinf] at hF; exact nomatch hF
      | ok vtype =>
        rw [hinf] at hF
        dsimp only at hF
        cases hdef : isDefEqCore mode env F 0 vtype cv.type with
        | error e => rw [hdef] at hF; exact nomatch hF
        | ok b =>
          rw [hdef] at hF
          dsimp only at hF
          cases b
          · simp only [Bool.false_eq_true, ↓reduceIte] at hF
            exact nomatch hF
          · simp only [↓reduceIte, Except.ok.injEq] at hF
            exact ⟨hcl, hfvF,
              ixvmAnnotateStep_iff.mpr ⟨F, hannot⟩, hlvl, hcon,
              ixvmInferStep_iff.mpr ⟨F, hinf⟩,
              ixvmDefEqStep_iff.mpr ⟨F, hdef⟩, hF.symm⟩

/-- Fuel-free big-step value check for an `opaque` (`checkOpaqueVal`):
`annotate`, `inferType`, and `isDefEq` on the opaque's value each have
their own independent fuel-free derivation. -/
inductive IxVMCheckOpaqueValStep (mode : CheckMode) (env : Env md)
    (cv : Kernel.ConstantVal md) (value : Kernel.Expr md) (env' : Env md) : Prop where
  | mk {value' vtype : Kernel.Expr md}
      (closedVal : value.looseBVarsBounded 0 = Bool.true)
      (noFvarVal : value.hasFvar = Bool.false)
      (annotVal : IxVMAnnotateStep mode env 0 value value')
      (lvlParamsOk : value'.allLevelParamsDefined cv.levelParams = Bool.true)
      (constsOk : value'.constsResolve env = Bool.true)
      (inferVal : IxVMInferStep mode env 0 value' vtype)
      (defeqType : IxVMDefEqStep mode env 0 vtype cv.type Bool.true)
      (out_eq : env' = ⟨.axiomInfo cv :: env.consts⟩) :
      IxVMCheckOpaqueValStep mode env cv value env'

/-- Every `IxVMCheckOpaqueValStep` succeeds at all fuels `F` above the max of
its 3 sub-derivation fuels. -/
theorem IxVMCheckOpaqueValStep.eval_at_large_fuel {mode : CheckMode} {env : Env md}
    {cv : Kernel.ConstantVal md} {value : Kernel.Expr md} {env' : Env md}
    (h : IxVMCheckOpaqueValStep mode env cv value env') :
    ∃ F₀, ∀ F, F₀ ≤ F → checkOpaqueVal (fueledOps mode F) env cv value = .ok env' := by
  cases h with
  | @mk value' vtype hcl hfv hannot hlvl hcon hinf hdef out_eq =>
    subst out_eq
    obtain ⟨F₁, hF₁⟩ := ixvmAnnotateStep_iff.mp hannot
    obtain ⟨F₂, hF₂⟩ := ixvmInferStep_iff.mp hinf
    obtain ⟨F₃, hF₃⟩ := ixvmDefEqStep_iff.mp hdef
    refine ⟨max F₁ (max F₂ F₃), fun F hle => ?_⟩
    have hF₁' : (fueledOps mode F).annotate env 0 value = .ok value' :=
      annotateCore_mono (Nat.le_trans (Nat.le_max_left F₁ _) hle) hF₁
    have hF₂' : (fueledOps mode F).inferType env 0 value' = .ok vtype :=
      inferTypeCore_mono (Nat.le_trans (Nat.le_trans (Nat.le_max_left F₂ F₃) (Nat.le_max_right F₁ _)) hle) hF₂
    have hF₃' : (fueledOps mode F).isDefEq env 0 vtype cv.type = .ok Bool.true :=
      isDefEqCore_mono (Nat.le_trans (Nat.le_trans (Nat.le_max_right F₂ F₃) (Nat.le_max_right F₁ _)) hle) hF₃
    unfold checkOpaqueVal
    simp only [hcl, hfv, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure]
    rw [hF₁']
    dsimp only
    simp only [hlvl, hcon, ↓reduceIte]
    rw [hF₂']
    dsimp only
    rw [hF₃']
    rfl

/-- Fuel-free big-step value check for a `theorem` (`checkThmVal`):
the `Prop`-sort check (`inferType` + `ensureSort` on `cv.type`) and the proof
realizability check (`annotate` + `inferType` + `isDefEq` on `value`) each have
their own independent fuel-free derivation (5 sub-derivations total). -/
inductive IxVMCheckThmValStep (mode : CheckMode) (env : Env md)
    (cv : Kernel.ConstantVal md) (value : Kernel.Expr md) (env' : Env md) : Prop where
  | mk {stype jv vtype : Kernel.Expr md} {sortLvl : Kernel.Level}
      (inferStmt : IxVMInferStep mode env 0 cv.type stype)
      (sortStmt : IxVMEnsureSortStep mode env 0 stype sortLvl)
      (isProp : Level.isEquiv sortLvl .zero = some Bool.true)
      (closedVal : value.looseBVarsBounded 0 = Bool.true)
      (noFvarVal : value.hasFvar = Bool.false)
      (annotVal : IxVMAnnotateStep mode env 0 value jv)
      (lvlParamsOk : jv.allLevelParamsDefined cv.levelParams = Bool.true)
      (constsOk : jv.constsResolve env = Bool.true)
      (inferVal : IxVMInferStep mode env 0 jv vtype)
      (defeqType : IxVMDefEqStep mode env 0 vtype cv.type Bool.true)
      (out_eq : env' = ⟨.thmInfo cv value :: env.consts⟩) :
      IxVMCheckThmValStep mode env cv value env'

/-- Every `IxVMCheckThmValStep` succeeds at all fuels `F` above the max of
its 5 sub-derivation fuels. -/
theorem IxVMCheckThmValStep.eval_at_large_fuel {mode : CheckMode} {env : Env md}
    {cv : Kernel.ConstantVal md} {value : Kernel.Expr md} {env' : Env md}
    (h : IxVMCheckThmValStep mode env cv value env') :
    ∃ F₀, ∀ F, F₀ ≤ F → checkThmVal (fueledOps mode F) env cv value = .ok env' := by
  cases h with
  | @mk stype jv vtype u hinfS hsortS hprop hcl hfv hannot hlvl hcon hinf hdef out_eq =>
    subst out_eq
    obtain ⟨F₁, hF₁⟩ := ixvmInferStep_iff.mp hinfS
    obtain ⟨F₂, hF₂⟩ := ixvmEnsureSortStep_iff.mp hsortS
    obtain ⟨F₃, hF₃⟩ := ixvmAnnotateStep_iff.mp hannot
    obtain ⟨F₄, hF₄⟩ := ixvmInferStep_iff.mp hinf
    obtain ⟨F₅, hF₅⟩ := ixvmDefEqStep_iff.mp hdef
    let F_left := max F₁ F₂
    let F_right := max F₃ (max F₄ F₅)
    refine ⟨max F_left F_right, fun F hle => ?_⟩
    have hle₁ : F₁ ≤ F := Nat.le_trans (Nat.le_trans (Nat.le_max_left F₁ F₂) (Nat.le_max_left _ _)) hle
    have hle₂ : F₂ ≤ F := Nat.le_trans (Nat.le_trans (Nat.le_max_right F₁ F₂) (Nat.le_max_left _ _)) hle
    have hle₃ : F₃ ≤ F := Nat.le_trans (Nat.le_trans (Nat.le_max_left F₃ _) (Nat.le_max_right _ _)) hle
    have hle₄ : F₄ ≤ F :=
      Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_max_left F₄ F₅) (Nat.le_max_right F₃ _)) (Nat.le_max_right _ _)) hle
    have hle₅ : F₅ ≤ F :=
      Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_max_right F₄ F₅) (Nat.le_max_right F₃ _)) (Nat.le_max_right _ _)) hle
    have hF₁' : (fueledOps mode F).inferType env 0 cv.type = .ok stype := inferTypeCore_mono hle₁ hF₁
    have hF₂' : (fueledOps mode F).ensureSort env 0 stype = .ok u := ensureSortCore_mono hle₂ hF₂
    have hF₃' : (fueledOps mode F).annotate env 0 value = .ok jv := annotateCore_mono hle₃ hF₃
    have hF₄' : (fueledOps mode F).inferType env 0 jv = .ok vtype := inferTypeCore_mono hle₄ hF₄
    have hF₅' : (fueledOps mode F).isDefEq env 0 vtype cv.type = .ok Bool.true := isDefEqCore_mono hle₅ hF₅
    unfold checkThmVal
    dsimp only [bind, Except.bind, pure, Except.pure]
    rw [hF₁']
    dsimp only
    rw [hF₂']
    dsimp only
    rw [hprop]
    dsimp only [liftFueled]
    simp only [hcl, hfv, Bool.false_eq_true, ↓reduceIte]
    rw [hF₃']
    dsimp only
    simp only [hlvl, hcon, ↓reduceIte]
    rw [hF₄']
    dsimp only
    rw [hF₅']
    rfl

/-- Fuel-free big-step declaration check (`IxVM` `Check::check_const`):
each sub-stage of declaration checking (`check_defn`, `check_thm`, `check_opaque`,
`check_axio`, `check_quot`, `check_indc`) has its own independent fuel-free
derivation witness. -/
inductive IxVMCheckDeclStep (mode : CheckMode) (ev : Evidences md) (env : Env md) :
    Declaration md → Env md → Prop where
  | defnSimple {cv cv' : Kernel.ConstantVal md} {value : Kernel.Expr md}
      {hint : ReducibilityHint} {env' : Env md}
      (hcv : IxVMCheckConstantValStep mode env cv cv')
      (hval : IxVMCheckDefnValStep mode env cv' value hint env')
      (hnoNatOp : natOpNames.contains cv'.name = Bool.false)
      (hnoDivMod : natDivModNames.contains cv'.name = Bool.false) :
      IxVMCheckDeclStep mode ev env (.defnDecl cv value hint) env'
  | thm {cv cv' : Kernel.ConstantVal md} {value : Kernel.Expr md} {env' : Env md}
      (hcv : IxVMCheckConstantValStep mode env cv cv')
      (hthm : IxVMCheckThmValStep mode env cv' value env') :
      IxVMCheckDeclStep mode ev env (.thmDecl cv value) env'
  | opaqueDecl {cv cv' : Kernel.ConstantVal md} {value : Kernel.Expr md} {env' : Env md}
      (hcv : IxVMCheckConstantValStep mode env cv cv')
      (hopq : IxVMCheckOpaqueValStep mode env cv' value env') :
      IxVMCheckDeclStep mode ev env (.opaqueDecl cv value) env'
  | axiomStd {cv cvA : Kernel.ConstantVal md}
      (hnotQuot : cv.name ≠ quotSoundName)
      (hcv : IxVMCheckConstantValStep mode env cv cvA)
      (hstd : stdAxiomOk env cvA = Bool.true) :
      IxVMCheckDeclStep mode ev env (.axiomDecl cv) ⟨.axiomInfo cvA :: env.consts⟩
  | quot {k : Kernel.QuotKind} {cv : Kernel.ConstantVal md} {env' : Env md}
      (hbas : ((match k with | .type => checkBasisDecl env .quotK | _ => pure env) : CheckM md (Env md)) = .ok env')
      (hpin : quotPinHit k cv = Bool.true) :
      IxVMCheckDeclStep mode ev env (.quotDecl k cv) env'
  | basis {kind : BasisKind} {env' : Env md}
      (hbas : (checkBasisDecl env kind : CheckM md (Env md)) = .ok env') :
      IxVMCheckDeclStep mode ev env (.basisDecl kind) env'
  | declRef {d : Declaration md} {env' : Env md} {F : Nat}
      (h : checkDecl mode (fueledOps mode F) ev env d = .ok env') :
      IxVMCheckDeclStep mode ev env d env'

/-- **Equivalence of Fuel-Free `IxVMCheckDeclStep` and `IxVMCheckConstRef`**:
Checking a declaration via `IxVMCheckDeclStep` (with separate fuel witnesses across
`checkConstantVal`, `checkDefnVal`, `checkThmVal`, `checkOpaqueVal`, etc.) is
equivalent to the existence of a single uniform fuel `F` for `checkDecl` (`IxVMCheckConstRef`). -/
theorem ixvmCheckDeclStep_iff_checkConstRef {mode : CheckMode} {ev : Evidences md}
    {env env' : Env md} {d : Declaration md} :
    IxVMCheckDeclStep mode ev env d env' ↔ IxVMCheckConstRef mode ev env d env' := by
  constructor
  · intro h
    cases h with
    | @defnSimple cv cv' value hint env' hcv hval hnoNatOp hnoDivMod =>
      obtain ⟨F₁, hF₁⟩ := hcv.eval_at_large_fuel
      obtain ⟨F₂, hF₂⟩ := hval.eval_at_large_fuel
      let F := max F₁ F₂
      refine ⟨F, ?_⟩
      unfold checkDecl
      dsimp only [bind, Except.bind, pure, Except.pure]
      rw [hF₁ F (Nat.le_max_left F₁ F₂)]
      dsimp only
      rw [hF₂ F (Nat.le_max_right F₁ F₂)]
      dsimp only
      simp only [hnoNatOp, hnoDivMod, Bool.false_eq_true, ↓reduceIte]
    | @thm cv cv' value env' hcv hthm =>
      obtain ⟨F₁, hF₁⟩ := hcv.eval_at_large_fuel
      obtain ⟨F₂, hF₂⟩ := hthm.eval_at_large_fuel
      let F := max F₁ F₂
      refine ⟨F, ?_⟩
      unfold checkDecl
      dsimp only [bind, Except.bind]
      rw [hF₁ F (Nat.le_max_left F₁ F₂)]
      dsimp only
      exact hF₂ F (Nat.le_max_right F₁ F₂)
    | @opaqueDecl cv cv' value env' hcv hopq =>
      obtain ⟨F₁, hF₁⟩ := hcv.eval_at_large_fuel
      obtain ⟨F₂, hF₂⟩ := hopq.eval_at_large_fuel
      let F := max F₁ F₂
      refine ⟨F, ?_⟩
      unfold checkDecl
      dsimp only [bind, Except.bind]
      rw [hF₁ F (Nat.le_max_left F₁ F₂)]
      dsimp only
      exact hF₂ F (Nat.le_max_right F₁ F₂)
    | @axiomStd cv cvA hnotQuot hcv hstd =>
      obtain ⟨F₀, hF₀⟩ := hcv.eval_at_large_fuel
      refine ⟨F₀, ?_⟩
      unfold checkDecl
      simp only [hnotQuot, ↓reduceIte, bind, Except.bind]
      rw [hF₀ F₀ (Nat.le_refl F₀)]
      dsimp only
      simp only [hstd, ↓reduceIte]
      rfl
    | @quot k cv env' hbas hpin =>
      refine ⟨0, ?_⟩
      unfold checkDecl
      simp only [hpin, ↓reduceIte]
      exact hbas
    | @basis kind env' hbas =>
      exact ⟨0, hbas⟩
    | @declRef d env' F h =>
      exact ⟨F, h⟩
  · rintro ⟨F, hF⟩
    exact .declRef hF

/-- Fuel-free big-step declaration walk (`IxVM` `Claim::walk_refs_transitive` / `env_walk_all`),
where each declaration is checked via `IxVMCheckDeclStep` without a global fuel counter. -/
inductive IxVMFuelFreeWalkDecls (mode : CheckMode) (ev : Evidences md) :
    Env md → List (Declaration md) → Env md → Prop where
  | nil (env : Env md) : IxVMFuelFreeWalkDecls mode ev env [] env
  | cons {env env₁ env₂ : Env md} {d : Declaration md} {ds : List (Declaration md)}
      (head : IxVMCheckDeclStep mode ev env d env₁)
      (tail : IxVMFuelFreeWalkDecls mode ev env₁ ds env₂) :
      IxVMFuelFreeWalkDecls mode ev env (d :: ds) env₂

/-- **Equivalence of `IxVMFuelFreeWalkDecls` and `IxVMWalkDecls`**. -/
theorem ixvmFuelFreeWalkDecls_iff_walkDecls {mode : CheckMode} {ev : Evidences md}
    {env env' : Env md} {ds : List (Declaration md)} :
    IxVMFuelFreeWalkDecls mode ev env ds env' ↔ IxVMWalkDecls mode ev env ds env' := by
  constructor
  · intro h
    induction h with
    | nil env => exact .nil env
    | cons hd _ ih => exact .cons (ixvmCheckDeclStep_iff_checkConstRef.mp hd) ih
  · intro h
    induction h with
    | nil env => exact .nil env
    | cons hd _ ih => exact .cons (ixvmCheckDeclStep_iff_checkConstRef.mpr hd) ih

/-- **Equivalence of Fuel-Free `IxVMFuelFreeWalkDecls` from `Env.empty` and `Cached.AcceptsRef`**:
Walking a list of declarations via fuel-free `IxVMCheckDeclStep` derivations is
equivalent to the existence of a single uniform fuel `F` at which `checkDeclsPure`
accepts the entire declaration sequence. -/
theorem ixvmFuelFreeWalkDecls_iff_acceptsRef {mode : CheckMode} {ev : Evidences md}
    {ds : List (Declaration md)} {env : Env md} :
    IxVMFuelFreeWalkDecls mode ev Env.empty ds env ↔ AcceptsRef mode ev ds env :=
  ixvmFuelFreeWalkDecls_iff_walkDecls.trans ixvm_env_walk_all_iff_acceptsRef

/-! ## 3. End-to-End Compiler + `IxVM` Commutation (`ixvm_compile_commutes`) -/

/-- **Uniqueness of the `IxVM`-Accepted Target Environment**:
For a fixed `(binding, limits, ixe, S, order)`, any two environments `env₁` and `env₂`
accepted by `IxVMAcceptsClaim` are identical (`env₁ = env₂`). -/
theorem ixvm_accepts_unique_env {binding : Binding} {limits : Limits}
    {ixe : Ixon.Env} {S : Address → Prop} {order : List Address}
    {env₁ env₂ : Env .anon}
    (h₁ : IxVMAcceptsClaim binding limits ixe S order env₁)
    (h₂ : IxVMAcceptsClaim binding limits ixe S order env₂) :
    env₁ = env₂ := by
  obtain ⟨_, t₁, pre₁, ev₁, ds₁, hbind₁, hpre₁, hprep₁, hwalk₁⟩ := h₁
  obtain ⟨_, t₂, pre₂, ev₂, ds₂, hbind₂, hpre₂, hprep₂, hwalk₂⟩ := h₂
  have ht : t₁ = t₂ := Option.some.inj (hbind₁.decoded.symm.trans hbind₂.decoded)
  subst ht
  have hpre : pre₁ = pre₂ := Except.ok.inj (hpre₁.symm.trans hpre₂)
  subst hpre
  have hprep_eq : (ev₁, ds₁) = (ev₂, ds₂) :=
    Except.ok.inj (hprep₁.symm.trans hprep₂)
  cases hprep_eq
  exact AcceptsRef.unique
    (ixvm_env_walk_all_iff_acceptsRef.mp hwalk₁)
    (ixvm_env_walk_all_iff_acceptsRef.mp hwalk₂)

/-- **`IxVM`-Level Covering Commutation (`IxVMCommutesCovering`)**:
The `IxVM` counterpart of `Ix.Cert.IxonCommutesCovering`:
there exist `binding`, `limits`, `order`, `envA`, `cx` such that:
1. `Admission.defaultBinding = .ok binding`,
2. **`IxVMAcceptsClaim binding limits ixe (Seed ixe sub) order envA`** holds
   (the compiled closure is accepted by `IxVM`'s binding validator, stream
   preparation, and declaration walk),
3. `admissionContext binding limits ixe order = some cx`,
4. `RenamesSource ixe t cx envQ envA` and `ReadingCovers ixe t cx sub envQ` hold, and
5. `CommutesStrong (readingAt ixe t cx) envQ envA` holds (every `StrongModel V envA`
   of the `IxVM`-accepted Ixon environment pulls back via `readingAt ixe t cx` to a
   `LawModel V envQ` and `ValueModel V envQ` of the source Lean environment). -/
def IxVMCommutesCovering (ixe : Ixon.Env) (sub : Ix.Environment)
    (t : RoleTable) (envQ : Env .source) : Prop :=
  ∃ binding, Admission.defaultBinding = .ok binding ∧
    ∃ limits order envA cx,
      IxVMAcceptsClaim binding limits ixe (Ix.Cert.Seed ixe sub) order envA ∧
      Ix.Cert.admissionContext binding limits ixe order = some cx ∧
      Ix.Cert.RenamesSource ixe t cx envQ envA ∧
      Ix.Cert.CommutesStrong.{w} (Ix.Cert.readingAt ixe t cx) envQ envA ∧
      Ix.Cert.ReadingCovers ixe t cx sub envQ

/-- **Equivalence of `IxVMCommutesCovering` and `Ix.Cert.IxonCommutesCovering`**:
By `ixvm_accepts_iff_ixonAcceptsRef`, `IxVMCommutesCovering` is equivalent to
`Ix.Cert.IxonCommutesCovering`. -/
theorem ixvmCommutesCovering_iff_ixonCommutesCovering {ixe : Ixon.Env}
    {sub : Ix.Environment} {t : RoleTable} {envQ : Env .source} :
    IxVMCommutesCovering.{w} ixe sub t envQ ↔
      Ix.Cert.IxonCommutesCovering.{w} ixe sub t envQ := by
  unfold IxVMCommutesCovering Ix.Cert.IxonCommutesCovering
  constructor
  · rintro ⟨binding, hbind, limits, order, envA, cx, hacc, hcx, hren, hcomm, hread⟩
    exact ⟨binding, hbind, limits, order, envA, cx,
      ixvm_accepts_iff_ixonAcceptsRef.mp hacc, hcx, hren, hcomm, hread⟩
  · rintro ⟨binding, hbind, limits, order, envA, cx, hacc, hcx, hren, hcomm, hread⟩
    exact ⟨binding, hbind, limits, order, envA, cx,
      ixvm_accepts_iff_ixonAcceptsRef.mpr hacc, hcx, hren, hcomm, hread⟩

/-- **End-to-End Compiler + `IxVM` Commutation Theorem (`ixvm_compile_commutes`)**:
When `SourceAcceptsQ` holds on a Lean closure `sub`, `compileReport` produces
`(ixe, failures)` with `NoFailure failures sub`, `artifactCheck t ixe = .ok ()`
passes, and `RoleEvidenceChecks` holds:
1. `Published ixe sub` and `IxVMCommutesCovering ixe sub t envQ` hold, and
2. for any `envA_ixvm` accepted by `IxVMAcceptsClaim` on the compiled closure
   and any set-theoretic `StrongModel V envA_ixvm`, the model pulls back via
   `readingAt ixe t cx` to both a `Ix.Cert.LawModel V envQ` and a
   `Ix.Cert.ValueModel V envQ` of the source Lean environment `envQ`. -/
theorem ixvm_compile_commutes
    {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Ix.Cert.Failures} {t : RoleTable} {envQ : Env .source}
    (table : Reader.defaultTable = .ok t)
    (source : Ix.Cert.SourceAcceptsQ Ix.Cert.blocksOf env roots sub ixe t envQ)
    (compiled : Ix.Cert.compileReport env = .ok (ixe, failures))
    (none : Ix.Cert.NoFailure failures sub)
    (checked : Ix.Cert.artifactCheck t ixe = .ok ())
    (evidence : Ix.Cert.RoleClosure.RoleEvidenceChecks) :
    Ix.Cert.Published ixe sub ∧
    IxVMCommutesCovering.{w} ixe sub t envQ ∧
    ∃ binding limits order envA cx,
      Admission.defaultBinding = .ok binding ∧
      IxVMAcceptsClaim binding limits ixe (Ix.Cert.Seed ixe sub) order envA ∧
      Ix.Cert.admissionContext binding limits ixe order = some cx ∧
      Ix.Cert.RenamesSource ixe t cx envQ envA ∧
      Ix.Cert.ReadingCovers ixe t cx sub envQ ∧
      ∀ (envA_ixvm : Env .anon),
        IxVMAcceptsClaim binding limits ixe (Ix.Cert.Seed ixe sub) order envA_ixvm →
        envA_ixvm = envA ∧
        ∀ (V : Type w) [SetTheory V] (M : StrongModel V envA_ixvm),
          ∃ (N : Ix.Cert.LawModel V envQ),
            (∃ (NV : Ix.Cert.ValueModel V envQ), NV = N.toValueModel) ∧
            ∀ c ∈ envQ.consts, ∀ e,
              Ix.Cert.readingAt ixe t cx c = some e →
              ∀ φ ρ, Denotes M.model.cval envA_ixvm φ ρ e (N.cval c.name φ) := by
  obtain ⟨bound, agree, quotient⟩ := Ix.Cert.artifactCheck_sound checked
  obtain ⟨hpub, hcov⟩ :=
    Ix.Cert.ReaderStreamsTrace.compileCorrect.{w}
      env roots sub ixe failures t envQ table source compiled none bound agree quotient evidence
  have hcov_ixvm : IxVMCommutesCovering.{w} ixe sub t envQ :=
    ixvmCommutesCovering_iff_ixonCommutesCovering.mpr hcov
  obtain ⟨binding, hbind, limits, order, envA, cx, hacc, hcx, hren, hcomm, hread⟩ := hcov_ixvm
  refine ⟨hpub, ⟨binding, hbind, limits, order, envA, cx, hacc, hcx, hren, hcomm, hread⟩,
    binding, limits, order, envA, cx, hbind, hacc, hcx, hren, hread, ?_⟩
  intro envA_ixvm hacc_ixvm
  have heq : envA_ixvm = envA := ixvm_accepts_unique_env hacc_ixvm hacc
  subst heq
  refine ⟨rfl, fun V _ M => ?_⟩
  obtain ⟨N, hN⟩ := hcomm V M
  exact ⟨N, ⟨N.toValueModel, rfl⟩, hN⟩

/-- **Nominal Source + `IxVM` Commutation Corollary (`ixvm_compile_commutes_nominal`)**:
When `SourceAcceptsQ` holds on `envQ`, `EnvSubstPullback` relates nominal `envS`
to `envQ` along `fiberAliasAt ixe (roleAtMap t)`, `compileReport` has `NoFailure`,
and `artifactCheck t ixe = .ok ()` passes, any `StrongModel` of the `IxVM`-accepted
target environment `envA` pulls back directly to a nominal `LawModel V envS` and
`ValueModel V envS` (`NominalSemanticBridgeAt`). -/
theorem ixvm_compile_commutes_nominal
    {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Ix.Cert.Failures} {t : RoleTable}
    {envS envQ : Env .source}
    (table : Reader.defaultTable = .ok t)
    (source : Ix.Cert.SourceAcceptsQ Ix.Cert.blocksOf env roots sub ixe t envQ)
    (hpull : Ix.Cert.EnvSubstPullback.{w}
      (Ix.LeanIngress.fiberAliasAt ixe (Ix.LeanIngress.roleAtMap t)) envS envQ)
    (compiled : Ix.Cert.compileReport env = .ok (ixe, failures))
    (none : Ix.Cert.NoFailure failures sub)
    (checked : Ix.Cert.artifactCheck t ixe = .ok ())
    (evidence : Ix.Cert.RoleClosure.RoleEvidenceChecks) :
    Ix.Cert.Published ixe sub ∧
    IxVMCommutesCovering.{w} ixe sub t envQ ∧
    Ix.Cert.NominalSemanticBridgeAt.{w} ixe sub t envS envQ := by
  obtain ⟨bound, agree, quotient⟩ := Ix.Cert.artifactCheck_sound checked
  obtain ⟨hpub, hcov⟩ :=
    Ix.Cert.ReaderStreamsTrace.compileCorrect.{w}
      env roots sub ixe failures t envQ table source compiled none bound agree quotient evidence
  exact ⟨hpub, ixvmCommutesCovering_iff_ixonCommutesCovering.mpr hcov, hcov.nominalPullback hpull⟩

end Ix.Cert.IxVM
