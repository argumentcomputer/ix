import IxVMRefinement.Assembly.NativeAliasRunTrace
import IxVMRefinement.Assembly.NativeAliasTeleWalk

/-! # What the head traces of a former's telescope keep

The telescope the circuit builds for a former declared at a definition is registered as the
term its walk builds on kernel terms (`OpenBinderTrace`, `OpenSortTrace`). That term is not
read off the heap exactly, so the facts IxC's check of the telescope constant asks of its type
come from the walk and not from the heap:

* `Trace.allLevelParamsDefined`: a head trace keeps the level parameters of its term within
  a given list, where every stored definition's value mentions only its own level parameters
  (`DefnLevelsClosed`): a definition is unfolded at the levels of the constant, and a beta step
  moves an argument into a body.
* `OpenBinderTrace.allLevelParamsDefined`, `OpenSortTrace.allParamsDefined`: so do the
  telescope walk and the result-sort walk.
* `tracedTele_allLevelParamsDefined`: a telescope into a sort that has the traced binders of a
  term and ends in its traced sort mentions only the level parameters of that term.
* `OpenBinderTrace.prefixEq_of_openPis`: the walk keeps the leading binders its term already
  has syntactically, so a term with the traced binders of `S` opens its first binders to the
  same free variables as `S` wherever `S` opens them (`TracedBinders.openPisAtFvars`). This is
  what the constructors' stage reads of the telescope constant (its parameters).
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Decl

open Ix.Kernel
open IxVM.Refinement.Core
open Ix.Kernel.HeadDeltaBeta (Trace Step DefnLevelsClosed)

/-! ## Level parameters along a head trace -/

/-- Substituting a term within `ps` for a bound variable keeps the level parameters within
`ps`. -/
theorem allLevelParamsDefined_instantiate1_of {ps : List LevelParam} {a : KExpr}
    (ha : a.allLevelParamsDefined ps = true) :
    ∀ {e : KExpr} (k : Nat), e.allLevelParamsDefined ps = true →
      (e.instantiate1 a k).allLevelParamsDefined ps = true := by
  intro e
  induction e <;> intro k h <;> simp_all [Expr.instantiate1, Expr.allLevelParamsDefined]
  case bvar i =>
    split
    · exact ha
    · split <;> simp [Expr.allLevelParamsDefined]

/-- A head step keeps the level parameters of its term within `ps`. -/
theorem Step.allLevelParamsDefined {env : Env .anon} (hdef : DefnLevelsClosed env)
    {ps : List LevelParam} {e r : KExpr} (h : Step env e r) :
    e.allLevelParamsDefined ps = true → r.allLevelParamsDefined ps = true := by
  induction h with
  | @delta n us e hd =>
    intro he
    obtain ⟨n', us', cv, value, hint, hfn, hfind, hlen, rfl⟩ :=
      Ix.Kernel.Open.unfoldDefinition_inv hd
    simp only [Expr.getAppFn, Expr.const.injEq] at hfn
    obtain ⟨rfl, rfl⟩ := hfn
    simp only [Expr.getAppArgs, Expr.mkAppN]
    simp only [Expr.allLevelParamsDefined, List.all_eq_true] at he
    exact allLevelParamsDefined_instantiateLevelParams (fun u hu => he u hu) hlen
      (hdef _ cv value hint hfind)
  | @beta ty body a mb =>
    intro he
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at he
    exact allLevelParamsDefined_instantiate1_of he.2 0 he.1.1.2
  | @appFn f f' a _ ih =>
    intro he
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at he ⊢
    exact ⟨ih he.1, he.2⟩

/-- A head trace keeps the level parameters of its term within `ps`. -/
theorem Trace.allLevelParamsDefined {env : Env .anon} (hdef : DefnLevelsClosed env)
    {ps : List LevelParam} {e r : KExpr} (h : Trace env e r) :
    e.allLevelParamsDefined ps = true → r.allLevelParamsDefined ps = true := by
  induction h with
  | refl => exact id
  | cons hs _ ih => exact fun he => ih (Step.allLevelParamsDefined hdef hs he)

/-- Closing a free variable keeps the level parameters within `ps`. -/
theorem allLevelParamsDefined_abstract1 {ps : List LevelParam} (d : Nat) :
    ∀ {e : KExpr} (k : Nat), e.allLevelParamsDefined ps = true →
      (e.abstract1 d k).allLevelParamsDefined ps = true
  | .bvar _, _, _ => by simp only [Expr.abstract1, Expr.allLevelParamsDefined]
  | .fvar idx ty, k, h => by
    simp only [Expr.abstract1]
    split
    · simp only [Expr.allLevelParamsDefined]
    · exact h
  | .sort _, _, h => by simpa only [Expr.abstract1] using h
  | .const _ _, _, h => by simpa only [Expr.abstract1] using h
  | .lit _, _, _ => by simp only [Expr.abstract1, Expr.allLevelParamsDefined]
  | .app f a, k, h => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.abstract1, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨allLevelParamsDefined_abstract1 d k h.1, allLevelParamsDefined_abstract1 d k h.2⟩
  | .lam t b m, k, h => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.abstract1, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨allLevelParamsDefined_abstract1 d k h.1.1,
      allLevelParamsDefined_abstract1 d (k + 1) h.1.2⟩, h.2⟩
  | .forallE t b m, k, h => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.abstract1, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨allLevelParamsDefined_abstract1 d k h.1.1,
      allLevelParamsDefined_abstract1 d (k + 1) h.1.2⟩, h.2⟩
  | .letE t v b _, k, h => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.abstract1, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨allLevelParamsDefined_abstract1 d k h.1.1, allLevelParamsDefined_abstract1 d k h.1.2⟩,
      allLevelParamsDefined_abstract1 d (k + 1) h.2⟩
  | .proj _ _ e, k, h => by
    simp only [Expr.allLevelParamsDefined] at h
    simp only [Expr.abstract1, Expr.allLevelParamsDefined]
    exact allLevelParamsDefined_abstract1 d k h

/-- **The telescope walk keeps the level parameters of its term within `ps`.** -/
theorem OpenBinderTrace.allLevelParamsDefined {env : Env .anon} (hdef : DefnLevelsClosed env)
    {ps : List LevelParam} {d n : Nat} {E X : KExpr} (h : OpenBinderTrace env d n E X) :
    E.allLevelParamsDefined ps = true → X.allLevelParamsDefined ps = true := by
  induction h with
  | done => exact id
  | @step d n E T B R bm ht _ ih =>
    intro hE
    have hF := Trace.allLevelParamsDefined hdef ht hE
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hF
    have hR := ih (Ix.Kernel.Expr.allLevelParamsDefined_instantiate1 hF.1.1 0 hF.1.2)
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨hF.1.1, allLevelParamsDefined_abstract1 d 0 hR⟩, hF.2⟩

/-- **The result-sort walk ends in a level within the level parameters of its term.** -/
theorem OpenSortTrace.allParamsDefined {env : Env .anon} (hdef : DefnLevelsClosed env)
    {ps : List LevelParam} {d n : Nat} {E : KExpr} {s : Level} (h : OpenSortTrace env d n E s) :
    E.allLevelParamsDefined ps = true → s.allParamsDefined ps = true := by
  induction h with
  | done ht =>
    intro hE
    have h := Trace.allLevelParamsDefined hdef ht hE
    simpa only [Expr.allLevelParamsDefined] using h
  | @step d n E T B bm s ht _ ih =>
    intro hE
    have hF := Trace.allLevelParamsDefined hdef ht hE
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hF
    exact ih (Ix.Kernel.Expr.allLevelParamsDefined_instantiate1 hF.1.1 0 hF.1.2)

/-- A telescope into a sort within `ps`, whose binder prefix is that of a term within `ps`, is
within `ps`. -/
theorem PrefixEq.allLevelParamsDefined_of_sort {ps : List LevelParam} {s : Level}
    (hs : s.allParamsDefined ps = true) :
    ∀ (n : Nat) {Y Z : KExpr} {bs : List (KExpr × BinderMeta)}, PrefixEq n Y Z →
      Z.stripPis n = some (bs, .sort s) → Y.allLevelParamsDefined ps = true →
      Z.allLevelParamsDefined ps = true
  | 0, Y, Z, bs, _, hz, _ => by
    simp only [Ix.Kernel.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hz
    rw [hz.2]
    simpa only [Expr.allLevelParamsDefined] using hs
  | n + 1, Y, Z, bs, h, hz, hY => by
    obtain ⟨T, B, B', bm, rfl, rfl, hr⟩ := h.succ_view
    simp only [Ix.Kernel.Expr.stripPis, Option.map_eq_some_iff] at hz
    obtain ⟨⟨bs', R'⟩, hz', heq⟩ := hz
    obtain ⟨-, rfl⟩ := Prod.mk.inj heq
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hY ⊢
    exact ⟨⟨hY.1.1, PrefixEq.allLevelParamsDefined_of_sort hs n hr hz' hY.1.2⟩, hY.2⟩

/-- **The traced telescope mentions only the level parameters of the term it is traced from**:
a telescope `Z` into `Sort s` with the traced binders of `S`, where `s` is the level the
result-sort walk reaches from `S`. -/
theorem tracedTele_allLevelParamsDefined {env : Env .anon} (hdef : DefnLevelsClosed env)
    {ps : List LevelParam} {n : Nat} {S Z : KExpr} {s : Level}
    {bs : List (KExpr × BinderMeta)} (hS : S.allLevelParamsDefined ps = true)
    (hb : TracedBinders env n S Z) (hsort : OpenSortTrace env 0 n S s)
    (hz : Z.stripPis n = some (bs, .sort s)) : Z.allLevelParamsDefined ps = true := by
  obtain ⟨X, hX, hpre⟩ := hb
  exact PrefixEq.allLevelParamsDefined_of_sort (OpenSortTrace.allParamsDefined hdef hsort hS) n
    hpre hz (OpenBinderTrace.allLevelParamsDefined hdef hX hS)

/-! ## The binders a term already has -/

/-- **The walk keeps the leading binders its term has syntactically**: where the term opens
its first `k` binders, the built term has the same first `k` binders. -/
theorem OpenBinderTrace.prefixEq_of_openPis {env : Env .anon} :
    ∀ (k : Nat) {d n : Nat} {S X : KExpr} {tfvs : List KExpr} {r : KExpr}, k ≤ n →
      OpenBinderTrace env d n S X → fvarIdxLt d S = true → S.looseBVarsBounded 0 = true →
      Ix.Kernel.openPisAtFvars k S d = some (tfvs, r) → PrefixEq k S X
  | 0, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | k + 1, d, n, S, X, tfvs, r, hk, h, hf, hb, hop => by
    cases h with
    | done => exact absurd hk (by omega)
    | @step _ n' _ T B R bm ht hrest =>
      cases S with
      | forallE dom body bm₀ =>
        obtain ⟨rfl, rfl, rfl⟩ :=
          (Trace.refl (env := env) (e := Expr.forallE dom body bm₀)).forall_unique
            (fun _ _ hx => hx) ht
        simp only [fvarIdxLt, Bool.and_eq_true] at hf
        simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at hb
        cases hin : Ix.Kernel.openPisAtFvars k (body.instantiate1 (.fvar d dom)) (d + 1) with
        | none =>
          exact absurd hop (by simp [Ix.Kernel.openPisAtFvars, hin])
        | some pr =>
          have hrec : PrefixEq k (body.instantiate1 (.fvar d dom)) R :=
            OpenBinderTrace.prefixEq_of_openPis k (tfvs := pr.1) (r := pr.2) (by omega) hrest
              (fvarIdxLt_instantiate1_open dom 0 hf.2)
              (Ix.Kernel.looseBVarsBounded_instantiate1 body 0 hb.2) hin
          have hcl := PrefixEq.abstract1 d k 0 hrec
          rw [abstract1_instantiate1_cancel dom 0 hf.2 hb.2] at hcl
          exact ⟨rfl, rfl, hcl⟩
      | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _
      | lit _ | proj _ _ _ =>
        exact absurd hop (by simp [Ix.Kernel.openPisAtFvars])

/-- **A term with the traced binders of `S` opens its first `k` binders as `S` does**, where
`S` is closed and opens them at all. -/
theorem TracedBinders.openPisAtFvars {env : Env .anon} {k m : Nat} {S Z : KExpr}
    {tfvs : List KExpr} {r₁ : KExpr} (h : TracedBinders env (k + m) S Z)
    (hf : fvarIdxLt 0 S = true) (hb : S.looseBVarsBounded 0 = true)
    (hop : Ix.Kernel.openPisAtFvars k S 0 = some (tfvs, r₁)) :
    ∃ r₂, Ix.Kernel.openPisAtFvars k Z 0 = some (tfvs, r₂) := by
  obtain ⟨X, hX, hpre⟩ := h
  have h1 : PrefixEq k S X :=
    OpenBinderTrace.prefixEq_of_openPis k (Nat.le_add_right k m) hX hf hb hop
  exact PrefixEq.openPisAtFvars k (h1.trans (PrefixEq.take k m hpre)) hop

end IxVM.Refinement.Decl
