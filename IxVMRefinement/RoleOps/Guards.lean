import IxVMRefinement.Decl.DeclWalkedConst
import IxC.Kernel.Verify.EnvGuards
import IxC.Kernel.Verify.DivModInv
import IxC.Kernel.Checker
import IxC.Kernel.Roles

/-! # Stored-shape guards at the install of a `Nat` operation

The kernel's judgement-level record of a definition stored at the key of one of the fifteen
`Nat` operations (`Ix.Kernel.Semantics.DeclDefnRunJ`) asks, beside the typing of the definition,
for guards on what the environment stores once the operation is in it: `natOpGuard`, the pinned
types of the operation and of its dependencies (`natOpStoredOk`), and for a well-founded
operation `divModEnvGuard`. This file derives those guards from facts about the environment
*before* the operation is stored and the syntactic shape of the operation's type.

* `OpPrefix env c`, `WfPrefix env c`: what the prefix holds when `c` is installed. Every field
  is a lookup in the prefix: literal support, the operations `c` depends on stored as pinned,
  the `Bool` constants, the pinned `Eq`. They fix an install order (`natOpDeps`).
* `OpTyShape c ty`: the operation's type is the pinned one up to its binders' data.
* `OpsPinned env`: every operation key the environment stores is stored as pinned. It is kept by
  an install at another key and extended by an operation's own install, so a fold can carry it and
  read the dependency clause of `OpPrefix` off it (`OpPrefix.of_pinned`).
-/

namespace IxVM.Refinement.RoleOps

open IxVM.Refinement.Core (KExpr KKey)
open IxVM.Refinement.Decl (isBaseKey ne_projTableName_of_isBaseKey)
open Ix.Kernel (Env Expr ConstantInfo ConstantVal BinderMeta ReducibilityHint EnvExt
  natOpNames natDivModNames natOpDeps natOpGuard natOpStoredOk natOpTyPinned natOpCod
  natOpStored natLitSupported natName natZeroName natSuccName boolName boolTrueName
  boolFalseName eqName eqA natPredName natAddName natBeqName natBleName divModEnvGuard
  reservedBasisNames)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## The operation keys -/

/-- The fifteen operation keys: the seven structural operations, then the eight well-founded
ones. -/
def opNames : List KKey := natOpNames ++ natDivModNames

theorem mem_opNames {c : KKey} : c ∈ opNames ↔ c ∈ natOpNames ∨ c ∈ natDivModNames :=
  List.mem_append

private theorem opNames_all_base : opNames.all (fun c => isBaseKey c) = true := by decide

private theorem opNames_all_notReserved :
    opNames.all (fun c => !(reservedBasisNames : List KKey).contains c) = true := by decide

private theorem opNames_all_selfDep :
    opNames.all (fun c => (natOpDeps c).contains c) = true := by decide

private theorem opNames_all_depsOps :
    opNames.all (fun c => (natOpDeps c).all (fun n => opNames.contains n)) = true := by decide

private theorem natOpNames_all_notDivMod :
    (natOpNames : List KKey).all (fun c => !(natDivModNames : List KKey).contains c) = true := by
  decide

private theorem natDivModNames_all_notOp :
    (natDivModNames : List KKey).all (fun c => !(natOpNames : List KKey).contains c) = true := by
  decide

private theorem natDivModNames_all_notCmp :
    (natDivModNames : List KKey).all (fun c => c != natBeqName && c != natBleName) = true := by
  decide

/-- An operation key is a role key, not a derived one. -/
theorem isBaseKey_of_mem_opNames {c : KKey} (hc : c ∈ opNames) : isBaseKey c = true :=
  List.all_eq_true.mp opNames_all_base c hc

/-- An operation key is not reserved for a basis block. -/
theorem notReserved_of_mem_opNames {c : KKey} (hc : c ∈ opNames) :
    (reservedBasisNames : List KKey).contains c = false := by
  have h : (!(reservedBasisNames : List KKey).contains c) = true :=
    List.all_eq_true.mp opNames_all_notReserved c hc
  cases hb : (reservedBasisNames : List KKey).contains c with
  | false => rfl
  | true => rw [hb] at h; exact absurd h (by decide)

/-- An operation is among its own dependencies (`natOpDeps`). -/
theorem self_mem_natOpDeps {c : KKey} (hc : c ∈ opNames) : c ∈ natOpDeps c := by
  have h : (natOpDeps c).contains c = true := List.all_eq_true.mp opNames_all_selfDep c hc
  exact List.contains_iff_mem.mp h

/-- An operation's dependencies are operations. -/
theorem natOpDeps_sub_opNames {c : KKey} (hc : c ∈ opNames) {n : KKey} (hn : n ∈ natOpDeps c) :
    n ∈ opNames := by
  have h : (natOpDeps c).all (fun n => opNames.contains n) = true :=
    List.all_eq_true.mp opNames_all_depsOps c hc
  have h2 : opNames.contains n = true := List.all_eq_true.mp h n hn
  exact List.contains_iff_mem.mp h2

/-- A structural operation is not a well-founded one. -/
theorem not_divMod_of_natOp {c : KKey} (hc : c ∈ natOpNames) :
    (natDivModNames : List KKey).contains c = false := by
  have h : (!(natDivModNames : List KKey).contains c) = true :=
    List.all_eq_true.mp natOpNames_all_notDivMod c hc
  cases hb : (natDivModNames : List KKey).contains c with
  | false => rfl
  | true => rw [hb] at h; exact absurd h (by decide)

/-- A well-founded operation is not a structural one. -/
theorem not_natOp_of_divMod {c : KKey} (hc : c ∈ natDivModNames) :
    (natOpNames : List KKey).contains c = false := by
  have h : (!(natOpNames : List KKey).contains c) = true :=
    List.all_eq_true.mp natDivModNames_all_notOp c hc
  cases hb : (natOpNames : List KKey).contains c with
  | false => rfl
  | true => rw [hb] at h; exact absurd h (by decide)

/-- A well-founded operation is neither comparison. -/
theorem not_cmp_of_divMod {c : KKey} (hc : c ∈ natDivModNames) :
    ¬ (c = natBeqName ∨ c = natBleName) := by
  have h : (c != natBeqName && c != natBleName) = true :=
    List.all_eq_true.mp natDivModNames_all_notCmp c hc
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  rintro (h1 | h2)
  · exact h.1 h1
  · exact h.2 h2

/-! ## The environment after the install -/

/-- **The environment after the operation is stored**: the definition, with no level
parameters, at the front. -/
abbrev installed (env : Env .anon) (c : KKey) (ty val : KExpr) (hint : ReducibilityHint) :
    Env .anon :=
  ⟨.defnInfo ⟨c, [], ty⟩ val hint :: env.consts⟩

theorem installed_find_self (env : Env .anon) (c : KKey) (ty val : KExpr)
    (hint : ReducibilityHint) :
    (installed env c ty val hint).find? c = some (.defnInfo ⟨c, [], ty⟩ val hint) :=
  Ix.Kernel.Env.find?_cons_self (.defnInfo ⟨c, [], ty⟩ val hint) env

/-- Storing the operation at a fresh role key extends the environment. -/
theorem installed_ext {env : Env .anon} {c : KKey} (hfresh : env.find? c = none)
    (hbase : isBaseKey c = true) (ty val : KExpr) (hint : ReducibilityHint) :
    EnvExt env (installed env c ty val hint) :=
  Ix.Kernel.EnvExt.cons (c := .defnInfo ⟨c, [], ty⟩ val hint) hfresh
    (fun _ => ne_projTableName_of_isBaseKey hbase)

/-! ## The `Bool` constants, as the guards read them -/

/-- **`Bool` is stored as a comparison's codomain reads it** (`natOpCod`): no level parameters
and the type `Sort 1`. -/
def BoolPinned (env : Env .anon) : Prop :=
  ∃ ci, env.find? boolName = some ci ∧ ci.toConstantVal.levelParams = [] ∧
    ci.toConstantVal.type = .sort (.succ .zero)

/-- **The `Bool` constructors are stored with no level parameters** (`natOpGuard`). -/
def BoolCtorsStored (env : Env .anon) : Prop :=
  (∃ ci, env.find? boolTrueName = some ci ∧ ci.toConstantVal.levelParams = []) ∧
    ∃ ci, env.find? boolFalseName = some ci ∧ ci.toConstantVal.levelParams = []

/-- **The `Bool` constructors are stored at the type `Bool`** (`divModEnvGuard`). -/
def BoolCtorsTyped (env : Env .anon) : Prop :=
  (∃ ci, env.find? boolTrueName = some ci ∧ ci.toConstantVal.type = .const boolName []) ∧
    ∃ ci, env.find? boolFalseName = some ci ∧ ci.toConstantVal.type = .const boolName []

theorem BoolPinned.mono {env env' : Env .anon} (h : EnvExt env env') (hb : BoolPinned env) :
    BoolPinned env' := by
  obtain ⟨ci, hf, hl, ht⟩ := hb
  exact ⟨ci, h.find hf, hl, ht⟩

theorem BoolCtorsStored.mono {env env' : Env .anon} (h : EnvExt env env')
    (hb : BoolCtorsStored env) : BoolCtorsStored env' := by
  obtain ⟨⟨a, ha, hla⟩, ⟨b, hb', hlb⟩⟩ := hb
  exact ⟨⟨a, h.find ha, hla⟩, ⟨b, h.find hb', hlb⟩⟩

theorem BoolCtorsTyped.mono {env env' : Env .anon} (h : EnvExt env env')
    (hb : BoolCtorsTyped env) : BoolCtorsTyped env' := by
  obtain ⟨⟨a, ha, hla⟩, ⟨b, hb', hlb⟩⟩ := hb
  exact ⟨⟨a, h.find ha, hla⟩, ⟨b, h.find hb', hlb⟩⟩

/-! ## The pinned type -/

/-- The codomain of operation `c`: `Bool` for the two comparisons, `Nat` otherwise. -/
def opCod (c : KKey) : KKey := if c = natBeqName ∨ c = natBleName then boolName else natName

/-- **The operation's type is the pinned one, up to its binders' data**: `Nat → Nat` for
`Nat.pred`, `Nat → Nat → Bool` for the comparisons, `Nat → Nat → Nat` otherwise. The syntactic
half of `natOpTyPinned`; its other half is the stored shape of `Bool` (`BoolPinned`). -/
def OpTyShape (c : KKey) (ty : KExpr) : Prop :=
  if c = natPredName then
    ∃ mb, ty = .forallE (.const natName []) (.const natName []) mb
  else
    ∃ mb₁ mb₂, ty = .forallE (.const natName [])
      (.forallE (.const natName []) (.const (opCod c) []) mb₂) mb₁

theorem natOpCod_opCod {env : Env .anon} {c : KKey}
    (hbool : (c = natBeqName ∨ c = natBleName) → BoolPinned env) :
    natOpCod env c (.const (opCod c) []) = true := by
  unfold Ix.Kernel.natOpCod
  by_cases hc : c = natBeqName ∨ c = natBleName
  · obtain ⟨ci, hf, hlp, hty⟩ := hbool hc
    have hcb : (c = natBeqName || c = natBleName) = true := by
      rcases hc with h | h <;> simp [h]
    have hop : opCod c = boolName := if_pos hc
    rw [if_pos hcb, hop, hf]
    simp [hlp, hty]
  · have hcb : ¬ ((c = natBeqName || c = natBleName) = true) := by
      intro h
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h
      exact hc h
    have hop : opCod c = natName := if_neg hc
    rw [if_neg hcb, hop]
    simp

/-- The pinned type, from its syntactic shape and the stored shape of `Bool`. -/
theorem natOpTyPinned_of_shape {env : Env .anon} {c : KKey} {ty : KExpr}
    (hsh : OpTyShape c ty) (hbool : (c = natBeqName ∨ c = natBleName) → BoolPinned env) :
    natOpTyPinned env c ty = true := by
  unfold OpTyShape at hsh
  unfold Ix.Kernel.natOpTyPinned
  by_cases hp : c = natPredName
  · rw [if_pos hp] at hsh
    obtain ⟨mb, rfl⟩ := hsh
    rw [if_pos hp]
    have hne : ¬ (c = natBeqName ∨ c = natBleName) := by
      rw [hp]; decide
    have hop : opCod c = natName := if_neg hne
    have hcod := natOpCod_opCod (env := env) (c := c) hbool
    rw [hop] at hcod
    simp [hcod]
  · rw [if_neg hp] at hsh
    obtain ⟨mb₁, mb₂, rfl⟩ := hsh
    rw [if_neg hp]
    simp [natOpCod_opCod hbool]

theorem natOpCod_mono {env env' : Env .anon} (h : EnvExt env env') {c : KKey} {e : KExpr}
    (hc : natOpCod env c e = true) : natOpCod env' c e = true := by
  unfold Ix.Kernel.natOpCod at hc ⊢
  by_cases hcb : (c = natBeqName || c = natBleName) = true
  · rw [if_pos hcb] at hc ⊢
    simp only [Bool.and_eq_true] at hc ⊢
    refine ⟨hc.1, ?_⟩
    have h2 := hc.2
    cases hf : env.find? boolName with
    | none => rw [hf] at h2; exact nomatch h2
    | some ci => rw [h.find hf]; rw [hf] at h2; exact h2
  · rw [if_neg hcb] at hc ⊢
    exact hc

theorem natOpTyPinned_mono {env env' : Env .anon} (h : EnvExt env env') {c : KKey} {ty : KExpr}
    (hp : natOpTyPinned env c ty = true) : natOpTyPinned env' c ty = true := by
  unfold Ix.Kernel.natOpTyPinned at hp ⊢
  by_cases hc : c = natPredName
  · rw [if_pos hc] at hp ⊢
    cases ty with
    | forallE dom body mb =>
      have hp' : (dom == .const natName [] && natOpCod env c body) = true := hp
      show (dom == .const natName [] && natOpCod env' c body) = true
      simp only [Bool.and_eq_true] at hp' ⊢
      exact ⟨hp'.1, natOpCod_mono h hp'.2⟩
    | _ => exact nomatch hp
  · rw [if_neg hc] at hp ⊢
    cases ty with
    | forallE dom b mb =>
      cases b with
      | forallE dom2 body mb2 =>
        have hp' : (dom == .const natName [] && dom2 == .const natName [] &&
            natOpCod env c body) = true := hp
        show (dom == .const natName [] && dom2 == .const natName [] &&
            natOpCod env' c body) = true
        simp only [Bool.and_eq_true] at hp' ⊢
        exact ⟨hp'.1, natOpCod_mono h hp'.2⟩
      | _ => exact nomatch hp
    | _ => exact nomatch hp

/-! ## A stored operation -/

/-- `natOpStoredOk`, as facts. -/
theorem natOpStoredOk_inv {env : Env .anon} {n : KKey} (h : natOpStoredOk env n = true) :
    ∃ cv v hint, env.find? n = some (.defnInfo cv v hint) ∧ cv.levelParams = [] ∧
      natOpTyPinned env n cv.type = true := by
  unfold Ix.Kernel.natOpStoredOk at h
  cases hf : env.find? n with
  | none => rw [hf] at h; exact nomatch h
  | some ci =>
    rw [hf] at h
    cases ci with
    | defnInfo cv v hint =>
      have h' : (cv.levelParams.isEmpty && natOpTyPinned env n cv.type) = true := h
      simp only [Bool.and_eq_true, List.isEmpty_iff] at h'
      exact ⟨cv, v, hint, rfl, h'.1, h'.2⟩
    | _ => exact nomatch h

theorem natOpStoredOk_intro {env : Env .anon} {n : KKey} {cv : ConstantVal .anon} {v : KExpr}
    {hint : ReducibilityHint} (hf : env.find? n = some (.defnInfo cv v hint))
    (hlp : cv.levelParams = []) (hp : natOpTyPinned env n cv.type = true) :
    natOpStoredOk env n = true := by
  unfold Ix.Kernel.natOpStoredOk
  rw [hf]
  show (cv.levelParams.isEmpty && natOpTyPinned env n cv.type) = true
  simp [hlp, hp]

/-- A stored, pinned operation stays so along an extension. -/
theorem natOpStoredOk_mono {env env' : Env .anon} (h : EnvExt env env') {n : KKey}
    (hs : natOpStoredOk env n = true) : natOpStoredOk env' n = true := by
  obtain ⟨cv, v, hint, hf, hlp, hp⟩ := natOpStoredOk_inv hs
  exact natOpStoredOk_intro (h.find hf) hlp (natOpTyPinned_mono h hp)

theorem natOpStored_of_storedOk {env : Env .anon} {n : KKey} (hs : natOpStoredOk env n = true) :
    natOpStored env n = true := by
  obtain ⟨cv, v, hint, hf, -, -⟩ := natOpStoredOk_inv hs
  simp [Ix.Kernel.natOpStored, hf]

/-! ## What the prefix holds when an operation is installed -/

/-- **The prefix at the install of operation `c`**: `c` is not stored; `Nat` literals are
supported; every other operation `c`'s recurrences involve (`natOpDeps`) is stored as pinned;
for a comparison or a well-founded operation the `Bool` constructors are stored with no level
parameters; for a comparison `Bool` is stored as its codomain reads it. -/
structure OpPrefix (env : Env .anon) (c : KKey) : Prop where
  fresh : env.find? c = none
  natLit : natLitSupported env = true
  deps : ∀ n ∈ natOpDeps c, n ≠ c → natOpStoredOk env n = true
  boolCtors : (c = natBeqName ∨ c = natBleName ∨ c ∈ natDivModNames) → BoolCtorsStored env
  bool : (c = natBeqName ∨ c = natBleName) → BoolPinned env

/-- **The prefix at the install of a well-founded operation**: `OpPrefix`, the pinned `Eq`
(the certificates are equations in it), `Bool` stored, and its constructors stored at the type
`Bool`. -/
structure WfPrefix (env : Env .anon) (c : KKey) : Prop where
  op : OpPrefix env c
  eq : env.find? eqName = some eqA
  boolStored : (env.find? boolName).isSome = true
  boolCtorsTyped : BoolCtorsTyped env

/-- `natOpGuard` once the operation is stored. -/
theorem natOpGuard_installed {env : Env .anon} {c : KKey} (hp : OpPrefix env c)
    (hbase : isBaseKey c = true) (ty val : KExpr) (hint : ReducibilityHint) :
    natOpGuard (installed env c ty val hint) c = true := by
  have hext := installed_ext hp.fresh hbase ty val hint
  refine Ix.Kernel.natOpGuard_intro (hext.natLitSupported_mono hp.natLit) ?_ ?_
  · intro n hn
    by_cases hnc : n = c
    · rw [hnc]
      exact ⟨⟨c, [], ty⟩, val, hint, installed_find_self env c ty val hint, rfl⟩
    · obtain ⟨cvn, vn, hn', hf, hlp, -⟩ := natOpStoredOk_inv (hp.deps n hn hnc)
      exact ⟨cvn, vn, hn', hext.find hf, hlp⟩
  · intro hc
    obtain ⟨⟨ciT, hT, hlT⟩, ⟨ciF, hF, hlF⟩⟩ := hp.boolCtors hc
    exact ⟨⟨ciT, hext.find hT, hlT⟩, ⟨ciF, hext.find hF, hlF⟩⟩

/-- The operation is stored as pinned once it is stored with a type of the pinned shape. -/
theorem natOpStoredOk_installed {env : Env .anon} {c : KKey} {ty : KExpr} (hp : OpPrefix env c)
    (hbase : isBaseKey c = true) (hsh : OpTyShape c ty) (val : KExpr) (hint : ReducibilityHint) :
    natOpStoredOk (installed env c ty val hint) c = true := by
  have hext := installed_ext hp.fresh hbase ty val hint
  exact natOpStoredOk_intro (installed_find_self env c ty val hint) rfl
    (natOpTyPinned_of_shape hsh (fun h => (hp.bool h).mono hext))

/-- The pinned types of the operation and of its dependencies, once it is stored. -/
theorem natOpDeps_storedOk_installed {env : Env .anon} {c : KKey} {ty : KExpr}
    (hp : OpPrefix env c) (hbase : isBaseKey c = true) (hsh : OpTyShape c ty) (val : KExpr)
    (hint : ReducibilityHint) :
    (natOpDeps c).all (natOpStoredOk (installed env c ty val hint)) = true := by
  have hext := installed_ext hp.fresh hbase ty val hint
  refine List.all_eq_true.mpr ?_
  intro n hn
  by_cases hnc : n = c
  · rw [hnc]
    exact natOpStoredOk_installed hp hbase hsh val hint
  · exact natOpStoredOk_mono hext (hp.deps n hn hnc)

/-- `divModEnvGuard` once a well-founded operation is stored. -/
theorem divModEnvGuard_installed {env : Env .anon} {c : KKey} {ty : KExpr} (hp : WfPrefix env c)
    (hbase : isBaseKey c = true) (hsh : OpTyShape c ty) (val : KExpr) (hint : ReducibilityHint) :
    divModEnvGuard (installed env c ty val hint) c = true := by
  have hext := installed_ext hp.op.fresh hbase ty val hint
  obtain ⟨⟨ciT, hfT, htT⟩, ⟨ciF, hfF, htF⟩⟩ := hp.boolCtorsTyped.mono hext
  unfold Ix.Kernel.divModEnvGuard
  rw [natOpGuard_installed hp.op hbase ty val hint,
    natOpDeps_storedOk_installed hp.op hbase hsh val hint, hext.find hp.eq, hfT, hfF]
  simp [htT, htF]

/-! ## Every stored operation is stored as pinned -/

/-- **Every operation key the environment stores is stored as pinned**: a level-monomorphic
definition of the pinned type. A store-level fact a fold can carry: it holds where no operation
is stored, an install at another key keeps it, and an operation's own install extends it. -/
def OpsPinned (env : Env .anon) : Prop :=
  ∀ n ∈ opNames, (env.find? n).isSome = true → natOpStoredOk env n = true

theorem OpsPinned.of_none {env : Env .anon} (h : ∀ n ∈ opNames, env.find? n = none) :
    OpsPinned env := by
  intro n hn hs
  rw [h n hn] at hs
  exact nomatch hs

/-- An extension that stores no new operation key keeps `OpsPinned`. -/
theorem OpsPinned.ext {env env' : Env .anon} (h : OpsPinned env) (hext : EnvExt env env')
    (hnew : ∀ n ∈ opNames, (env'.find? n).isSome = true → (env.find? n).isSome = true) :
    OpsPinned env' :=
  fun n hn hs => natOpStoredOk_mono hext (h n hn (hnew n hn hs))

/-- A fresh constant at a key that is no operation's keeps `OpsPinned`. -/
theorem OpsPinned.cons_other {env : Env .anon} (h : OpsPinned env) {ci : ConstantInfo .anon}
    (hext : EnvExt env ⟨ci :: env.consts⟩) (hnot : ci.name ∉ opNames) :
    OpsPinned ⟨ci :: env.consts⟩ := by
  refine h.ext hext ?_
  intro n hn hs
  rw [Ix.Kernel.Env.find?_cons] at hs
  split at hs
  · next heq => exact absurd (by rw [heq]; exact hn) hnot
  · exact hs

/-- An operation's own install extends `OpsPinned`. -/
theorem OpsPinned.install_op {env : Env .anon} {c : KKey} {ty : KExpr} (h : OpsPinned env)
    (hp : OpPrefix env c) (hbase : isBaseKey c = true) (hsh : OpTyShape c ty) (val : KExpr)
    (hint : ReducibilityHint) : OpsPinned (installed env c ty val hint) := by
  have hext := installed_ext hp.fresh hbase ty val hint
  intro n hn hs
  by_cases hnc : n = c
  · rw [hnc]
    exact natOpStoredOk_installed hp hbase hsh val hint
  · refine natOpStoredOk_mono hext (h n hn ?_)
    rw [Ix.Kernel.Env.find?_cons] at hs
    split at hs
    · next heq => exact absurd heq.symm hnc
    · exact hs

/-- **The dependency clause of `OpPrefix`, from `OpsPinned`**: it is enough that the operations
`c` depends on are stored. This is the install order `natOpDeps` forces. -/
theorem OpPrefix.of_pinned {env : Env .anon} {c : KKey} (hpin : OpsPinned env) (hc : c ∈ opNames)
    (hfresh : env.find? c = none) (hnat : natLitSupported env = true)
    (hdeps : ∀ n ∈ natOpDeps c, n ≠ c → (env.find? n).isSome = true)
    (hbc : (c = natBeqName ∨ c = natBleName ∨ c ∈ natDivModNames) → BoolCtorsStored env)
    (hb : (c = natBeqName ∨ c = natBleName) → BoolPinned env) : OpPrefix env c where
  fresh := hfresh
  natLit := hnat
  deps := fun n hn hne => hpin n (natOpDeps_sub_opNames hc hn) (hdeps n hn hne)
  boolCtors := hbc
  bool := hb

end IxVM.Refinement.RoleOps
