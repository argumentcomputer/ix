import Ix.Cert.IxVM.RoleAdmission
import Ix.Cert.IxVM.ConvertBridge
import Ix.Cert.Statement

/-! # Kernel Evaluator, Typechecker & Claim Walk Bridge (`IxVM` ↔ `IxC`)

This module establishes the fuel-existence and simulation bridge connecting
`IxVM`'s operational kernel checks (`whnf`, `NatPrim`, `k_is_def_eq`, `k_infer`,
`k_infer_only`, `check_const`, `walk_refs_transitive`, `env_walk_all`) to `IxC`'s
pure fueled specification (`Ix.Kernel.CoreFns`, `Ix.Kernel.checkDecl`,
`Ix.Kernel.Cached.AcceptsRef .verified`, and `Ix.Cert.IxonAcceptsRef`), culminating
in `StrongModel`, `ValueModel`, and `No Proof of False` for any environment
accepted by `IxVM`.

## Key Results
1. **Fuel Monotonicity & Step Unfolding (`ixvm_whnf_mono`, `ixvm_defeq_mono`,
   `ixvm_infer_mono`, `ixvm_infer_only_mono`, `ixvm_whnf_step`, `ixvm_defeq_step`,
   `ixvm_infer_step`, `ixvm_infer_only_step`)**:
   Every operational check in `Ix.Kernel.CoreFns` (`whnfCore`, `whnf`, `defeq`,
   `infer`, `inferIO`, `annotate`, `ensureSort`) is monotone in fuel and unfolds
   in one fuel step to its open-recursion body (`whnfBody`, `defeqBody`, `inferBody`,
   `inferBodyIO`).
2. **`NatPrim` Fast-Path Bridge (`ixvm_natPrim_succ_sound`, `ixvm_natPrim_binOp_sound`)**:
   Whenever `whnf` reduces the argument(s) of `Nat.succ` or a stored binary `Nat`
   operation (`natAdd`, `natSub`, `natMul`, `natPow`, `natBeq`, `natBle`, `natDiv`,
   `natMod`, `natGcd`, `natLand`, `natLor`, `natXor`, `natShiftLeft`, `natShiftRight`)
   to `Nat` literals at fuels `F₁, F₂`, `reduceNat` at fuel `max F₁ F₂` computes
   `natOpResult c n₁ n₂`.
3. **Per-Constant Check & Transitive Walk Bridge (`IxVMCheckConstRef`, `IxVMWalkDecls`,
   `ixvm_walk_decls_iff_foldlM`, `ixvm_env_walk_all_iff_acceptsRef`)**:
   Checking a sequence of declarations one by one at possibly distinct per-constant
   fuels (`check_const` along `walk_refs_transitive` / `env_walk_all`) is equivalent
   to the existence of a single uniform fuel `F` at which `checkDeclsPure` accepts
   the entire sequence (`Cached.AcceptsRef .verified`).
4. **End-to-End Soundness (`ixvm_accepts_iff_ixonAcceptsRef`, `ixvm_accepts_strongModel`,
   `ixvm_accepts_valueModel`, `ixvm_accepts_no_proof_of_False`)**:
   An `IxVM` claim/environment walk (`IxVMAcceptsClaim`) is equivalent to
   `Ix.Cert.IxonAcceptsRef`, and therefore guarantees a `StrongModel`, a `ValueModel`,
   and that no accepted constant proves `False` (`roleKey .false`).
-/

namespace Ix.Cert.IxVM

open Ix.Kernel
open Ix.Kernel.Cached
open Ix.Kernel.Admission

universe w

/-! ## 1. Fuel Monotonicity & Step Unfolding for `CoreFns` (`whnf`, `defeq`, `infer`, `inferIO`) -/

/-- Fuel monotonicity for `whnfCore` (`IxVM` `Whnf::whnf_core`). -/
theorem ixvm_whnfCore_mono {mode : CheckMode} {env : Env md} {F₁ F₂ d : Nat}
    {e v : Kernel.Expr md} (hle : F₁ ≤ F₂) (h : whnfCore mode env F₁ d e = .ok v) :
    whnfCore mode env F₂ d e = .ok v :=
  whnfCore_mono hle h

/-- Fuel monotonicity for `whnf` (`IxVM` `Whnf::whnf`). -/
theorem ixvm_whnf_mono {mode : CheckMode} {env : Env md} {F₁ F₂ d : Nat}
    {e v : Kernel.Expr md} (hle : F₁ ≤ F₂) (h : whnf mode env F₁ d e = .ok v) :
    whnf mode env F₂ d e = .ok v :=
  whnf_mono hle h

/-- Fuel monotonicity for `isDefEqCore` (`IxVM` `DefEq::k_is_def_eq`). -/
theorem ixvm_defeq_mono {mode : CheckMode} {env : Env md} {F₁ F₂ d : Nat}
    {a b : Kernel.Expr md} {v : Bool} (hle : F₁ ≤ F₂) (h : isDefEqCore mode env F₁ d a b = .ok v) :
    isDefEqCore mode env F₂ d a b = .ok v :=
  isDefEqCore_mono hle h

/-- Fuel monotonicity for `inferTypeCore` (`IxVM` `Infer::k_infer`). -/
theorem ixvm_infer_mono {mode : CheckMode} {env : Env md} {F₁ F₂ d : Nat}
    {e v : Kernel.Expr md} (hle : F₁ ≤ F₂) (h : inferTypeCore mode env F₁ d e = .ok v) :
    inferTypeCore mode env F₂ d e = .ok v :=
  inferTypeCore_mono hle h

/-- Fuel monotonicity for `inferTypeIO` (`IxVM` `InferOnly::k_infer_only`). -/
theorem ixvm_infer_only_mono {mode : CheckMode} {env : Env md} {F₁ F₂ d : Nat}
    {e v : Kernel.Expr md} (hle : F₁ ≤ F₂) (h : inferTypeIO mode env F₁ d e = .ok v) :
    inferTypeIO mode env F₂ d e = .ok v :=
  inferTypeIO_mono hle h

/-- Fuel monotonicity for `annotateCore`. -/
theorem ixvm_annotate_mono {mode : CheckMode} {env : Env md} {F₁ F₂ d : Nat}
    {e v : Kernel.Expr md} (hle : F₁ ≤ F₂) (h : annotateCore mode env F₁ d e = .ok v) :
    annotateCore mode env F₂ d e = .ok v :=
  annotateCore_mono hle h

/-- Fuel monotonicity for `ensureSortCore` (`IxVM` `Infer::ensure_sort`). -/
theorem ixvm_ensureSort_mono {mode : CheckMode} {env : Env md} {F₁ F₂ d : Nat}
    {e : Kernel.Expr md} {u : Kernel.Level} (hle : F₁ ≤ F₂) (h : ensureSortCore mode env F₁ d e = .ok u) :
    ensureSortCore mode env F₂ d e = .ok u :=
  ensureSortCore_mono hle h

/-- One-step fuel unfolding of `whnf` (`Whnf::whnf`). -/
theorem ixvm_whnf_step (mode : CheckMode) (env : Env md) (F d : Nat) (e : Kernel.Expr md) :
    whnf mode env (F + 1) d e = whnfBody (pureFns mode env F) env d e :=
  whnf_succ env F d e

/-- One-step fuel unfolding of `isDefEqCore` (`DefEq::k_is_def_eq`). -/
theorem ixvm_defeq_step (mode : CheckMode) (env : Env md) (F d : Nat) (a b : Kernel.Expr md) :
    isDefEqCore mode env (F + 1) d a b = defeqBody mode (pureFns mode env F) env d a b :=
  isDefEqCore_succ env F d a b

/-- One-step fuel unfolding of `inferTypeCore` (`Infer::k_infer`). -/
theorem ixvm_infer_step (mode : CheckMode) (env : Env md) (F d : Nat) (e : Kernel.Expr md) :
    inferTypeCore mode env (F + 1) d e = inferBody mode (pureFns mode env F) env d e :=
  inferTypeCore_succ env F d e

/-- One-step fuel unfolding of `inferTypeIO` at `.verified` (`InferOnly::k_infer_only`). -/
theorem ixvm_infer_only_step (env : Env md) (F d : Nat) (e : Kernel.Expr md) :
    inferTypeIO .verified env (F + 1) d e =
      inferBodyIO .verified (CoreFns.ioView (pureFns .verified env F)) env d e := by
  rw [inferTypeIO_succ]
  rfl

/-! ## 2. `NatPrim` Fast-Path Bridge (`KernelNatPrim` ↔ `Ix.Kernel.reduceNat`) -/

/-- **`Nat.succ` Fast-Path Soundness (`NatPrim` ↔ `reduceNat`)**:
When `natLitSupported env` holds and `whnf mode env F d a` reduces `a` to a `Nat`
literal `.lit (.natVal n)`, `reduceNat (pureFns mode env F) env d (.app (.const natSuccName []) a)`
evaluates to `.ok (some (.lit (.natVal (n + 1))))`. -/
theorem ixvm_natPrim_succ_sound {mode : CheckMode} {env : Env md} {F d n : Nat}
    {a : Kernel.Expr md}
    (hsup : natLitSupported env)
    (ha : whnf mode env F d a = .ok (.lit (.natVal n))) :
    reduceNat (pureFns mode env F) env d (.app (.const natSuccName []) a) =
      .ok (some (.lit (.natVal (n + 1)))) := by
  unfold reduceNat
  simp only [hsup, and_self]
  change (whnf mode env F d a >>= fun w =>
    match rawNatLit? w with
    | some n => pure (some (Kernel.Expr.lit (.natVal (n + 1))))
    | none => pure none) = _
  rw [ha]
  rfl

/-- **Binary `Nat` Operation Fast-Path Soundness (`NatPrim` ↔ `reduceNat`)**:
For any certified binary `Nat` operation `c` (`natAdd`, `natSub`, `natMul`, `natPow`,
`natBeq`, `natBle`, `natDiv`, `natMod`, `natGcd`, `natLand`, `natLor`, `natXor`,
`natShiftLeft`, `natShiftRight`) stored in `env` (`natOpStored env c = true`),
if `whnf` reduces `a` to `.lit (.natVal n₁)` at fuel `F₁` and `b` to `.lit (.natVal n₂)`
at fuel `F₂`, then at fuel `max F₁ F₂`,
`reduceNat (pureFns mode env (max F₁ F₂)) env d (.app (.app (.const c []) a) b)`
evaluates to `.ok (natOpResult c n₁ n₂)`. -/
theorem ixvm_natPrim_binOp_sound {mode : CheckMode} {env : Env md} {F₁ F₂ d n₁ n₂ : Nat}
    {c : Key md} {a b : Kernel.Expr md}
    (hop : c = natAddName ∨ c = natSubName ∨ c = natMulName ∨
           c = natPowName ∨ c = natBeqName ∨ c = natBleName ∨
           c = natDivName ∨ c = natModName ∨ c = natGcdName ∨
           c = natLandName ∨ c = natLorName ∨ c = natXorName ∨
           c = natShiftLeftName ∨ c = natShiftRightName)
    (hstored : natOpStored env c = true)
    (ha : whnf mode env F₁ d a = .ok (.lit (.natVal n₁)))
    (hb : whnf mode env F₂ d b = .ok (.lit (.natVal n₂))) :
    reduceNat (pureFns mode env (max F₁ F₂)) env d (.app (.app (.const c []) a) b) =
      .ok (natOpResult c n₁ n₂) := by
  have ha' : whnf mode env (max F₁ F₂) d a = .ok (.lit (.natVal n₁)) :=
    whnf_mono (Nat.le_max_left F₁ F₂) ha
  have hb' : whnf mode env (max F₁ F₂) d b = .ok (.lit (.natVal n₂)) :=
    whnf_mono (Nat.le_max_right F₁ F₂) hb
  unfold reduceNat
  have hcond := And.intro hop hstored
  simp only [hcond]
  change (whnf mode env (max F₁ F₂) d a >>= fun wa =>
    match rawNatLit? wa with
    | some n₁ =>
      whnf mode env (max F₁ F₂) d b >>= fun wb =>
        match rawNatLit? wb with
        | some n₂ => pure (natOpResult c n₁ n₂)
        | none => pure none
    | none => pure none) = _
  rw [ha']
  dsimp only [bind, Except.bind, rawNatLit?]
  rw [hb']
  rfl

/-! ## 3. Per-Constant Checking & Transitive Walk Bridge (`check_const` / `walk_refs_transitive` ↔ `AcceptsRef`) -/

/-- Reference-level single-declaration check (`IxVM` `Check::check_const`):
there exists a fuel `F` at which `Ix.Kernel.checkDecl` accepts declaration `d`
in environment `env`, producing `env'`. -/
def IxVMCheckConstRef (mode : CheckMode) (ev : Evidences md)
    (env : Env md) (d : Declaration md) (env' : Env md) : Prop :=
  ∃ F, checkDecl mode (fueledOps mode F) ev env d = .ok env'

/-- `IxVMCheckConstRef` is deterministic: if `d` checks from `env` to both `e₁` and `e₂`,
then `e₁ = e₂`. -/
theorem IxVMCheckConstRef.deterministic {mode : CheckMode} {ev : Evidences md}
    {env e₁ e₂ : Env md} {d : Declaration md}
    (h₁ : IxVMCheckConstRef mode ev env d e₁)
    (h₂ : IxVMCheckConstRef mode ev env d e₂) : e₁ = e₂ := by
  obtain ⟨F₁, h₁⟩ := h₁
  obtain ⟨F₂, h₂⟩ := h₂
  exact checkDecl_deterministic h₁ h₂

/-- Step-by-step declaration walk (`IxVM` `Claim::walk_refs_transitive` / `env_walk_all`),
where each declaration in topological order is checked at its own fuel budget. -/
inductive IxVMWalkDecls (mode : CheckMode) (ev : Evidences md) :
    Env md → List (Declaration md) → Env md → Prop where
  | nil (env : Env md) : IxVMWalkDecls mode ev env [] env
  | cons {env env₁ env₂ : Env md} {d : Declaration md} {ds : List (Declaration md)}
      (head : IxVMCheckConstRef mode ev env d env₁)
      (tail : IxVMWalkDecls mode ev env₁ ds env₂) :
      IxVMWalkDecls mode ev env (d :: ds) env₂

/-- `IxVMWalkDecls` composes under list concatenation (`++`), modeling transitive
reference walk composition across dependency subgraphs. -/
theorem IxVMWalkDecls.append {mode : CheckMode} {ev : Evidences md}
    {env₁ env₂ env₃ : Env md} {ds₁ ds₂ : List (Declaration md)}
    (h₁ : IxVMWalkDecls mode ev env₁ ds₁ env₂)
    (h₂ : IxVMWalkDecls mode ev env₂ ds₂ env₃) :
    IxVMWalkDecls mode ev env₁ (ds₁ ++ ds₂) env₃ := by
  induction h₁ with
  | nil _ => exact h₂
  | cons hd _ ih => exact .cons hd (ih h₂)

/-- **Uniform Fuel Existence for `IxVMWalkDecls`**:
A step-by-step declaration walk `IxVMWalkDecls mode ev env ds env'` (where each
declaration `d ∈ ds` is checked at its own fuel `F_i`) holds if and only if there
exists a single uniform fuel `F` at which `ds.foldlM (checkDecl mode (fueledOps mode F) ev) env`
accepts the entire list and produces `env'`. -/
theorem ixvm_walk_decls_iff_foldlM {mode : CheckMode} {ev : Evidences md}
    {env env' : Env md} {ds : List (Declaration md)} :
    IxVMWalkDecls mode ev env ds env' ↔
      ∃ F, ds.foldlM (checkDecl mode (fueledOps mode F) ev) env = .ok env' := by
  constructor
  · intro h
    induction h with
    | nil env => exact ⟨0, rfl⟩
    | @cons env₀ env₁ env₂ d rest hd _ ih =>
      obtain ⟨F₁, hF₁⟩ := hd
      obtain ⟨F₂, hF₂⟩ := ih
      refine ⟨max F₁ F₂, ?_⟩
      rw [List.foldlM_cons, checkDecl_mono (Nat.le_max_left F₁ F₂) hF₁]
      exact checkDeclsFrom_mono (Nat.le_max_right F₁ F₂) hF₂
  · rintro ⟨F, hF⟩
    induction ds generalizing env with
    | nil =>
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hF
      subst hF
      exact .nil env
    | cons d rest ih =>
      rw [List.foldlM_cons] at hF
      cases hd : checkDecl mode (fueledOps mode F) ev env d with
      | error e => simp [hd, bind, Except.bind] at hF
      | ok env₁ =>
        rw [hd] at hF
        dsimp only [bind, Except.bind] at hF
        exact .cons ⟨F, hd⟩ (ih hF)

/-- **Equivalence of `IxVMWalkDecls` from `Env.empty` and `Cached.AcceptsRef`**:
Walking all declarations `ds` from `Env.empty` in `IxVM` (`env_walk_all` /
`walk_refs_transitive`) is equivalent to `Ix.Kernel.Cached.AcceptsRef mode ev ds env`. -/
theorem ixvm_env_walk_all_iff_acceptsRef {mode : CheckMode} {ev : Evidences md}
    {ds : List (Declaration md)} {env : Env md} :
    IxVMWalkDecls mode ev Env.empty ds env ↔ AcceptsRef mode ev ds env :=
  ixvm_walk_decls_iff_foldlM

/-! ## 4. End-to-End `IxVM` Claim Acceptance Bridge (`IxVMAcceptsClaim` ↔ `IxonAcceptsRef`) -/

/-- **End-to-End `IxVM` Acceptance of a Compiled Closure**:
Given a role binding `binding`, resource limits `limits`, an artifact `ixe`,
seed predicate `S`, and topological address order `order`:
1. `order` is a valid `Ix.Cert.ClosureOrder ixe S order`,
2. `IxVM`'s binding header validation `IxVMValidateBindingHeader Address.blake3Pure binding t`
   succeeds for some `RoleTable` `t`,
3. the committed prelude `Reader.preludeFor t = .ok pre` and stream preparation
   `Admission.prepareWith Address.admissionHash binding pre limits (recordsOf ixe order) (blobsOf ixe order) (hintsOf ixe) = .ok (ev, ds)` succeed, and
4. `IxVM`'s declaration walk `IxVMWalkDecls .verified ev Env.empty ds.toList envA`
   accepts `ds.toList` and installs `envA`. -/
def IxVMAcceptsClaim (binding : Binding) (limits : Limits) (ixe : Ixon.Env)
    (S : Address → Prop) (order : List Address) (envA : Env .anon) : Prop :=
  Ix.Cert.ClosureOrder ixe S order ∧
    ∃ t pre ev ds,
      IxVMValidateBindingHeader Address.blake3Pure binding t ∧
      Reader.preludeFor t = .ok pre ∧
      prepareWith Address.admissionHash binding pre limits
        (Ix.Cert.recordsOf ixe order) (Ix.Cert.blobsOf ixe order) (Ix.Cert.hintsOf ixe) = .ok (ev, ds) ∧
      IxVMWalkDecls .verified ev Env.empty ds.toList envA

/-- **Master Equivalence Theorem (`IxVMAcceptsClaim` ↔ `Ix.Cert.IxonAcceptsRef`)**:
`IxVM` claim acceptance `IxVMAcceptsClaim` holds if and only if `IxC`'s reference-level
acceptance `Ix.Cert.IxonAcceptsRef` holds. -/
theorem ixvm_accepts_iff_ixonAcceptsRef {binding : Binding} {limits : Limits}
    {ixe : Ixon.Env} {S : Address → Prop} {order : List Address} {envA : Env .anon} :
    IxVMAcceptsClaim binding limits ixe S order envA ↔
      Ix.Cert.IxonAcceptsRef binding limits ixe S order envA := by
  unfold IxVMAcceptsClaim Ix.Cert.IxonAcceptsRef
  constructor
  · rintro ⟨hclos, t, pre, ev, ds, hbind, hpre, hprep, hwalk⟩
    have hadm := (ixvm_validate_binding_blake3 binding t hbind).2.1
    have href := ixvm_env_walk_all_iff_acceptsRef.mp hwalk
    exact ⟨hclos, t, pre, ev, ds, hadm, hpre, hprep, href⟩
  · rintro ⟨hclos, t, pre, ev, ds, hadm, hpre, hprep, href⟩
    rw [Address.admissionHash_eq] at hadm
    have hbind := (ixvm_validate_binding_admitBinding Address.blake3Pure binding t).mpr hadm
    have hwalk := ixvm_env_walk_all_iff_acceptsRef.mpr href
    exact ⟨hclos, t, pre, ev, ds, hbind, hpre, hprep, hwalk⟩

/-- **`StrongModel` Existence for `IxVM`-Accepted Environments**:
Every environment `envA` accepted by `IxVMAcceptsClaim` has a `StrongModel V envA`
in every set theory `V`. -/
theorem ixvm_accepts_strongModel (V : Type w) [SetTheory V]
    {binding : Binding} {limits : Limits} {ixe : Ixon.Env}
    {S : Address → Prop} {order : List Address} {envA : Env .anon}
    (h : IxVMAcceptsClaim binding limits ixe S order envA) :
    Nonempty (StrongModel V envA) := by
  obtain ⟨_, _, _, _, _, _, _, _, hwalk⟩ := h
  exact (ixvm_env_walk_all_iff_acceptsRef.mp hwalk).strongModel V

/-- **`ValueModel` Existence for `IxVM`-Accepted Environments**:
Every environment `envA` accepted by `IxVMAcceptsClaim` has a `Ix.Cert.ValueModel V envA`
in every set theory `V`. -/
theorem ixvm_accepts_valueModel (V : Type w) [SetTheory V]
    {binding : Binding} {limits : Limits} {ixe : Ixon.Env}
    {S : Address → Prop} {order : List Address} {envA : Env .anon}
    (h : IxVMAcceptsClaim binding limits ixe S order envA) :
    Nonempty (Ix.Cert.ValueModel V envA) :=
  Ix.Cert.ixonValueSoundRef binding limits ixe S order envA
    (ixvm_accepts_iff_ixonAcceptsRef.mp h) V

/-- **No Proof of `False` for `IxVM`-Accepted Environments**:
In any environment `envA` accepted by `IxVMAcceptsClaim`, no constant has
`False`'s role key (`.const falseName []`) as its type. -/
theorem ixvm_accepts_no_proof_of_False (V : Type w) [SetTheory V]
    {binding : Binding} {limits : Limits} {ixe : Ixon.Env}
    {S : Address → Prop} {order : List Address} {envA : Env .anon}
    (h : IxVMAcceptsClaim binding limits ixe S order envA) :
    ∀ ci ∈ envA.consts, ci.toConstantVal.type = .const falseName [] → False :=
  Ix.Cert.ixonConsistentRef V binding limits ixe S order envA
    (ixvm_accepts_iff_ixonAcceptsRef.mp h)

end Ix.Cert.IxVM
