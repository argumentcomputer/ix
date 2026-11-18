import IxVMRefinement.Decl.NativeRec
import IxVMRefinement.Assembly.NativeAliasRecPrefix
import IxC.Kernel.Model.HeadDeltaBetaLevels

/-! # Head traces of a former's telescope, stepping under opened binders

An inductive may be declared at a type that only head-reduces to a telescope into a sort. The
circuit rebuilds that telescope twice: when it checks the block (`former_tele_at`, with the
result-sort walk `get_result_sort_level`) and when it checks a recursor of the family
(`nat_former_tele`). Each builder keeps a `∀` node, head-normalizes any other node to a `∀`
(`KernelGuard::head`: definitions, beta; a `let` is already read away by the term seam), and
recurses into the body.

`OpenBinderTrace env d n E X` is that walk on kernel terms. It records a head trace
(`HeadDeltaBeta.Trace`) at each of `n` binders and steps under a binder on the body opened with
the free variable of the current depth `d`, closing it again on the way out. Opening is what
makes the non-lifting beta step of `HeadDeltaBeta` agree with the circuit's lifting
substitution: on an opened term a beta argument has no loose bound variable. The walk keeps
the residual after the `n` binders unreduced, as `nat_former_tele` does, so it is a function
of its input (`OpenBinderTrace.unique`). `OpenSortTrace` is the separate result-sort walk.

Both commute with every instantiation of level parameters
(`OpenBinderTrace.instantiateLevelParams`), given that stored definitions mention only their
own level parameters. This is what links a recursor run that instantiates the levels of the
stored type before it rebuilds the telescope to the block run that did not.

`FormerOpenTraceAt` is what a registered family records for a later recursor run: the first
`nP + nIdx` binders of the telescope constant are the traced binders of the stored former's
type (`TracedBinders`), and the result-sort walk ends in a sort level-equivalent to the
family's (`TracedSort`). A family whose stored type is syntactically its telescope produces it
with empty traces (`FormerOpenTraceAt.of_syntactic`). -/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Decl

open Ix.Kernel
open IxVM.Refinement.Core
open Ix.Kernel.HeadDeltaBeta (Trace DefnLevelsClosed)

/-! ## The two walks -/

/-- The telescope builder on kernel terms: `n` binders, each reached by a head trace, the body
of each opened with the free variable of the depth `d` and closed again; the residual after
the last binder is kept as it is. -/
inductive OpenBinderTrace (env : Env .anon) : Nat → Nat → KExpr → KExpr → Prop
  | done {d : Nat} {E : KExpr} : OpenBinderTrace env d 0 E E
  | step {d n : Nat} {E T B R : KExpr} {bm : BinderMeta} :
      Trace env E (.forallE T B bm) →
      OpenBinderTrace env (d + 1) n (B.instantiate1 (.fvar d T)) R →
      OpenBinderTrace env d (n + 1) E (.forallE T (R.abstract1 d 0) bm)

/-- The result-sort walk on kernel terms: the same `n` binders, then a head trace of the
opened residual to a sort. -/
inductive OpenSortTrace (env : Env .anon) : Nat → Nat → KExpr → Level → Prop
  | done {d : Nat} {E : KExpr} {s : Level} : Trace env E (.sort s) → OpenSortTrace env d 0 E s
  | step {d n : Nat} {E T B : KExpr} {bm : BinderMeta} {s : Level} :
      Trace env E (.forallE T B bm) →
      OpenSortTrace env (d + 1) n (B.instantiate1 (.fvar d T)) s →
      OpenSortTrace env d (n + 1) E s

/-! ## Lookup-preserving extensions and determinism -/

theorem OpenBinderTrace.mono {env env' : Env .anon}
    (hext : ∀ k ci, env.find? k = some ci → env'.find? k = some ci)
    {d n : Nat} {E R : KExpr} (h : OpenBinderTrace env d n E R) :
    OpenBinderTrace env' d n E R := by
  induction h with
  | done => exact .done
  | step ht _ ih => exact .step (ht.mono hext) ih

theorem OpenSortTrace.mono {env env' : Env .anon}
    (hext : ∀ k ci, env.find? k = some ci → env'.find? k = some ci)
    {d n : Nat} {E : KExpr} {s : Level} (h : OpenSortTrace env d n E s) :
    OpenSortTrace env' d n E s := by
  induction h with
  | done ht => exact .done (ht.mono hext)
  | step ht _ ih => exact .step (ht.mono hext) ih

/-- The builder is a function of its input: two walks from one term, the second in an
environment that keeps the first one's lookups, build the same term. -/
theorem OpenBinderTrace.unique {env env' : Env .anon}
    (hext : ∀ k ci, env.find? k = some ci → env'.find? k = some ci)
    {d n : Nat} {E A : KExpr} (ha : OpenBinderTrace env d n E A) :
    ∀ {B : KExpr}, OpenBinderTrace env' d n E B → A = B := by
  induction ha with
  | done =>
    intro B hb
    cases hb
    rfl
  | step hh _ ih =>
    intro B hb
    cases hb with
    | step hh' hb' =>
      obtain ⟨rfl, rfl, rfl⟩ := hh.forall_unique hext hh'
      rw [ih hb']

/-- Two result-sort walks from one term end in the same level. -/
theorem OpenSortTrace.unique {env env' : Env .anon}
    (hext : ∀ k ci, env.find? k = some ci → env'.find? k = some ci)
    {d n : Nat} {E : KExpr} {s : Level} (ha : OpenSortTrace env d n E s) :
    ∀ {s' : Level}, OpenSortTrace env' d n E s' → s = s' := by
  induction ha with
  | done ht =>
    intro s' hb
    cases hb with
    | done ht' => exact ht.sort_unique hext ht'
  | step hh _ ih =>
    intro s' hb
    cases hb with
    | step hh' hb' =>
      obtain ⟨rfl, rfl, rfl⟩ := hh.forall_unique hext hh'
      exact ih hb'

/-! ## The built term is a telescope -/

theorem stripPis_isSome_abstract1 (d : Nat) :
    ∀ (n : Nat) (e : KExpr) (k : Nat), (e.stripPis n).isSome = true →
      ((e.abstract1 d k).stripPis n).isSome = true := by
  intro n
  induction n with
  | zero => intro e k _; simp [Ix.Kernel.Expr.stripPis]
  | succ n ih =>
    intro e k he
    cases e with
    | forallE ty b m =>
      simp only [Ix.Kernel.Expr.stripPis, Option.isSome_map] at he
      simp only [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.stripPis, Option.isSome_map]
      exact ih b (k + 1) he
    | _ => simp [Ix.Kernel.Expr.stripPis] at he

/-- The built term has `n` leading `∀`s. -/
theorem OpenBinderTrace.stripPis_isSome {env : Env .anon} {d n : Nat} {E X : KExpr}
    (h : OpenBinderTrace env d n E X) : (X.stripPis n).isSome = true := by
  induction h with
  | done => simp [Ix.Kernel.Expr.stripPis]
  | @step d n E T B R bm _ _ ih =>
    simp only [Ix.Kernel.Expr.stripPis, Option.isSome_map]
    exact stripPis_isSome_abstract1 d n R 0 ih

/-! ## Syntactic telescopes need no head step -/

/-- Opening a binder body keeps free-variable indices below the new depth. -/
theorem fvarIdxLt_instantiate1_open {d : Nat} (T : KExpr) :
    ∀ {e : KExpr} (j : Nat), fvarIdxLt d e = true →
      fvarIdxLt (d + 1) (e.instantiate1 (.fvar d T) j) = true
  | .bvar i, j, _ => by
    simp only [Expr.instantiate1]
    split
    · simp [fvarIdxLt]
    · split <;> rfl
  | .fvar idx ty, _, h => by
    simp only [fvarIdxLt, decide_eq_true_eq] at h
    simp only [Expr.instantiate1, fvarIdxLt, decide_eq_true_eq]
    omega
  | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, j, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h
    simp [Expr.instantiate1, fvarIdxLt,
      fvarIdxLt_instantiate1_open T j h.1, fvarIdxLt_instantiate1_open T j h.2]
  | .lam t b _, j, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h
    simp [Expr.instantiate1, fvarIdxLt,
      fvarIdxLt_instantiate1_open T j h.1, fvarIdxLt_instantiate1_open T (j + 1) h.2]
  | .forallE t b _, j, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h
    simp [Expr.instantiate1, fvarIdxLt,
      fvarIdxLt_instantiate1_open T j h.1, fvarIdxLt_instantiate1_open T (j + 1) h.2]
  | .letE t v b _, j, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h
    simp [Expr.instantiate1, fvarIdxLt,
      fvarIdxLt_instantiate1_open T j h.1.1, fvarIdxLt_instantiate1_open T j h.1.2,
      fvarIdxLt_instantiate1_open T (j + 1) h.2]
  | .proj _ _ e, j, h => by
    simp only [fvarIdxLt] at h
    simpa [Expr.instantiate1, fvarIdxLt] using fvarIdxLt_instantiate1_open T j h

/-- A closed term whose first `n` nodes are `∀`s is its own built telescope. -/
theorem OpenBinderTrace.of_strip (env : Env .anon) :
    ∀ (n : Nat) {d : Nat} {E : KExpr}, (E.stripPis n).isSome = true →
      fvarIdxLt d E = true → E.looseBVarsBounded 0 = true → OpenBinderTrace env d n E E
  | 0, _, _, _, _, _ => .done
  | n + 1, d, E, hs, hf, hb => by
    obtain ⟨T, B, bm, rfl⟩ : ∃ T B bm, E = .forallE T B bm := by
      cases E with
      | forallE T B bm => exact ⟨T, B, bm, rfl⟩
      | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _
      | lit _ | proj _ _ _ => simp [Ix.Kernel.Expr.stripPis] at hs
    have hsB : (B.stripPis n).isSome = true := by
      simpa only [Ix.Kernel.Expr.stripPis, Option.isSome_map] using hs
    simp only [fvarIdxLt, Bool.and_eq_true] at hf
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    have hrec : OpenBinderTrace env (d + 1) n (B.instantiate1 (.fvar d T))
        (B.instantiate1 (.fvar d T)) :=
      OpenBinderTrace.of_strip env n
        (Specs.Whnf.stripPis_isSome_instantiate1 _ n B 0 hsB)
        (fvarIdxLt_instantiate1_open T 0 hf.2)
        (Ix.Kernel.looseBVarsBounded_instantiate1 B 0 hb.2)
    have hstep : OpenBinderTrace env d (n + 1) (.forallE T B bm)
        (.forallE T ((B.instantiate1 (.fvar d T)).abstract1 d 0) bm) :=
      .step .refl hrec
    rw [abstract1_instantiate1_cancel T 0 hf.2 hb.2] at hstep
    exact hstep

/-- Substitution keeps a telescope into a sort. -/
theorem stripPis_sort_instantiate1 (v : KExpr) (s : Level) :
    ∀ (n : Nat) (e : KExpr) (k : Nat), (∃ bs, e.stripPis n = some (bs, .sort s)) →
      ∃ bs, (e.instantiate1 v k).stripPis n = some (bs, .sort s) := by
  intro n
  induction n with
  | zero =>
    intro e k ⟨bs, he⟩
    simp only [Ix.Kernel.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at he
    rw [he.2]
    exact ⟨[], rfl⟩
  | succ n ih =>
    intro e k ⟨bs, he⟩
    cases e <;> simp only [Ix.Kernel.Expr.stripPis, Option.map_eq_some_iff, reduceCtorEq] at he
    rename_i ty b m
    obtain ⟨⟨bs', R'⟩, hr, heq⟩ := he
    obtain ⟨-, rfl⟩ := Prod.mk.inj heq
    obtain ⟨bs'', hr'⟩ := ih b (k + 1) ⟨bs', hr⟩
    exact ⟨(ty.instantiate1 v k, m) :: bs'', by
      simp [Ix.Kernel.Expr.instantiate1, Ix.Kernel.Expr.stripPis, hr']⟩

/-- A telescope into a sort is its own result-sort walk. -/
theorem OpenSortTrace.of_strip (env : Env .anon) (s : Level) :
    ∀ (n : Nat) {d : Nat} {E : KExpr}, (∃ bs, E.stripPis n = some (bs, .sort s)) →
      OpenSortTrace env d n E s
  | 0, _, E, ⟨bs, h⟩ => by
    simp only [Ix.Kernel.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.2]
    exact .done .refl
  | n + 1, d, E, ⟨bs, h⟩ => by
    cases E <;> simp only [Ix.Kernel.Expr.stripPis, Option.map_eq_some_iff, reduceCtorEq] at h
    rename_i T B bm
    obtain ⟨⟨bs', R'⟩, hr, heq⟩ := h
    obtain ⟨-, rfl⟩ := Prod.mk.inj heq
    exact .step .refl (OpenSortTrace.of_strip env s n
      (stripPis_sort_instantiate1 (.fvar d T) s n B 0 ⟨bs', hr⟩))

/-! ## Level instantiation -/

/-- **The telescope builder commutes with level instantiation.** The walk from the instance of
a term builds the instance of the term the walk builds. -/
theorem OpenBinderTrace.instantiateLevelParams {env : Env .anon} (hdef : DefnLevelsClosed env)
    (ks : List LevelParam) (ws : List Level) {d n : Nat} {E X : KExpr}
    (h : OpenBinderTrace env d n E X) :
    OpenBinderTrace env d n (E.instantiateLevelParams ks ws)
      (X.instantiateLevelParams ks ws) := by
  induction h with
  | done => exact .done
  | @step d n E T B R bm ht _ ih =>
    rw [Ix.Kernel.LevelRen.inst_instantiate1 ks ws (.fvar d T) B 0] at ih
    have hstep := OpenBinderTrace.step (env := env) (d := d) (n := n)
      (E := E.instantiateLevelParams ks ws)
      (T := T.instantiateLevelParams ks ws) (B := B.instantiateLevelParams ks ws)
      (R := R.instantiateLevelParams ks ws)
      (bm := { bm with pw := Level.substPW ks ws bm.pw })
      (ht.instantiateLevelParams hdef ks ws) ih
    rw [← Ix.Kernel.LevelRen.inst_abstract1 ks ws d R 0] at hstep
    exact hstep

/-- The result-sort walk commutes with level instantiation. -/
theorem OpenSortTrace.instantiateLevelParams {env : Env .anon} (hdef : DefnLevelsClosed env)
    (ks : List LevelParam) (ws : List Level) {d n : Nat} {E : KExpr} {s : Level}
    (h : OpenSortTrace env d n E s) :
    OpenSortTrace env d n (E.instantiateLevelParams ks ws) (Level.subst ks ws s) := by
  induction h with
  | done ht => exact .done (ht.instantiateLevelParams hdef ks ws)
  | @step d n E T B bm s ht _ ih =>
    rw [Ix.Kernel.LevelRen.inst_instantiate1 ks ws (.fvar d T) B 0] at ih
    exact OpenSortTrace.step (env := env) (d := d) (n := n)
      (E := E.instantiateLevelParams ks ws)
      (T := T.instantiateLevelParams ks ws) (B := B.instantiateLevelParams ks ws)
      (bm := { bm with pw := Level.substPW ks ws bm.pw })
      (ht.instantiateLevelParams hdef ks ws) ih

/-! ## Binder prefixes -/

theorem PrefixEq.symm : ∀ {n : Nat} {E R : KExpr}, PrefixEq n E R → PrefixEq n R E
  | 0, _, _, _ => trivial
  | n + 1, E, R, h => by
    obtain ⟨T, B, B', bm, rfl, rfl, hr⟩ := h.succ_view
    exact ⟨rfl, rfl, hr.symm⟩

theorem PrefixEq.trans : ∀ {n : Nat} {E R S : KExpr},
    PrefixEq n E R → PrefixEq n R S → PrefixEq n E S
  | 0, _, _, _, _, _ => trivial
  | n + 1, E, R, S, h, h' => by
    obtain ⟨T, B, B', bm, rfl, rfl, hr⟩ := h.succ_view
    obtain ⟨T', C, C', bm', hRC, rfl, hr'⟩ := h'.succ_view
    obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj hRC
    exact ⟨rfl, rfl, hr.trans hr'⟩

/-- A term with `n` leading `∀`s has its own binder prefix. -/
theorem PrefixEq.of_strip : ∀ (n : Nat) {E : KExpr}, (E.stripPis n).isSome = true →
    PrefixEq n E E
  | 0, _, _ => trivial
  | n + 1, E, h => by
    cases E with
    | forallE T B bm =>
      simp only [Ix.Kernel.Expr.stripPis, Option.isSome_map] at h
      exact ⟨rfl, rfl, PrefixEq.of_strip n h⟩
    | _ => simp [Ix.Kernel.Expr.stripPis] at h

/-- **The first `n` binders of `A` are the binders the head reduction builds from `S`.**
Exact on domains and binder data; the residual of `A` after the prefix is free. -/
def TracedBinders (env : Env .anon) (n : Nat) (S A : KExpr) : Prop :=
  ∃ X, OpenBinderTrace env 0 n S X ∧ PrefixEq n X A

/-- **The result-sort walk from `S` ends in a sort level-equivalent to `s`.** -/
def TracedSort (env : Env .anon) (n : Nat) (S : KExpr) (s : Level) : Prop :=
  ∃ s', OpenSortTrace env 0 n S s' ∧ LvEq s' s

/-- Introduction: a walk and a common prefix. -/
theorem TracedBinders.intro {env : Env .anon} {n : Nat} {S A X : KExpr}
    (hX : OpenBinderTrace env 0 n S X) (hA : PrefixEq n X A) : TracedBinders env n S A := by
  unfold TracedBinders
  exact ⟨X, hX, hA⟩

/-- Introduction: a walk and a level equivalence. -/
theorem TracedSort.intro {env : Env .anon} {n : Nat} {S : KExpr} {s s' : Level}
    (hs : OpenSortTrace env 0 n S s') (hl : LvEq s' s) : TracedSort env n S s := by
  unfold TracedSort
  exact ⟨s', hs, hl⟩

theorem TracedBinders.mono {env env' : Env .anon}
    (hext : ∀ k ci, env.find? k = some ci → env'.find? k = some ci)
    {n : Nat} {S A : KExpr} (h : TracedBinders env n S A) : TracedBinders env' n S A := by
  obtain ⟨X, hX, hA⟩ := h
  exact .intro (hX.mono hext) hA

theorem TracedSort.mono {env env' : Env .anon}
    (hext : ∀ k ci, env.find? k = some ci → env'.find? k = some ci)
    {n : Nat} {S : KExpr} {s : Level} (h : TracedSort env n S s) : TracedSort env' n S s := by
  obtain ⟨s', hs', hl⟩ := h
  exact .intro (hs'.mono hext) hl

/-- Two terms that carry the traced binders of one term agree on the binder prefix. -/
theorem TracedBinders.prefixEq {env env' : Env .anon}
    (hext : ∀ k ci, env.find? k = some ci → env'.find? k = some ci)
    {n : Nat} {S A B : KExpr} (ha : TracedBinders env n S A) (hb : TracedBinders env' n S B) :
    PrefixEq n A B := by
  obtain ⟨X, hX, hA⟩ := ha
  obtain ⟨Y, hY, hB⟩ := hb
  have hXY : X = Y := hX.unique hext hY
  subst hXY
  exact hA.symm.trans hB

/-- Two levels that the result-sort walk of one term reaches are level-equivalent. -/
theorem TracedSort.lvEq {env env' : Env .anon}
    (hext : ∀ k ci, env.find? k = some ci → env'.find? k = some ci)
    {n : Nat} {S : KExpr} {s t : Level} (ha : TracedSort env n S s) (hb : TracedSort env' n S t) :
    LvEq s t := by
  obtain ⟨s', hs', hs⟩ := ha
  obtain ⟨t', ht', ht⟩ := hb
  have hst : s' = t' := hs'.unique hext ht'
  subst hst
  exact fun φ => (hs φ).symm.trans (ht φ)

/-- A closed syntactic telescope carries its own traced binders. -/
theorem TracedBinders.of_strip (env : Env .anon) {n : Nat} {S : KExpr}
    (hs : (S.stripPis n).isSome = true) (hf : fvarIdxLt 0 S = true)
    (hb : S.looseBVarsBounded 0 = true) : TracedBinders env n S S :=
  .intro (OpenBinderTrace.of_strip env n hs hf hb) (PrefixEq.of_strip n hs)

/-- **A builder run on the instantiated term, read at the registered telescope.** If `A`
carries the traced binders of `S`, any walk from an instance of `S` builds the instance of one
telescope `X` with the binder prefix of `A`. The telescope `X` does not depend on the walk. -/
theorem TracedBinders.instantiated {env : Env .anon} (hdef : DefnLevelsClosed env)
    (ks : List LevelParam) (ws : List Level) {n : Nat} {S A : KExpr}
    (h : TracedBinders env n S A) :
    ∃ X, (X.stripPis n).isSome = true ∧ PrefixEq n X A ∧
      ∀ {Y : KExpr}, OpenBinderTrace env 0 n (S.instantiateLevelParams ks ws) Y →
        Y = X.instantiateLevelParams ks ws := by
  obtain ⟨X, hX, hA⟩ := h
  exact ⟨X, hX.stripPis_isSome, hA, fun hY =>
    hY.unique (fun _ _ hf => hf) (hX.instantiateLevelParams hdef ks ws)⟩

end IxVM.Refinement.Decl

namespace IxVM.Refinement.Typing

open Ix.Kernel
open Ix.Kernel.Semantics
open Ix.Kernel.Model

/-- **What a registered family records for a later recursor run**, beside its stored data: the
telescope constant has the traced binders of the stored former's type, and the result-sort walk
from the stored former's type ends in a sort level-equivalent to the family's. Equality of the
telescope constant and the stored former is not asked. -/
structure FormerOpenTraceAt (env : Env .anon) (fam : NativeFam .anon) : Prop where
  binders : Decl.TracedBinders env (fam.p.nP + fam.p.nIdx) fam.cvS.type fam.cvTa.type
  result : Decl.TracedSort env (fam.p.nP + fam.p.nIdx) fam.cvS.type fam.p.resSort

/-- The record is kept by every extension that preserves lookups. -/
theorem FormerOpenTraceAt.mono {env env' : Env .anon} {fam : NativeFam .anon}
    (hext : ∀ k ci, env.find? k = some ci → env'.find? k = some ci)
    (h : FormerOpenTraceAt env fam) : FormerOpenTraceAt env' fam :=
  ⟨h.binders.mono hext, h.result.mono hext⟩

/-- A family whose stored former is its telescope constant, with a closed type that is
syntactically a telescope into the family's sort, has the record with no head step. -/
theorem FormerOpenTraceAt.of_syntactic {env : Env .anon} {fam : NativeFam .anon}
    {bs : List (Expr .anon × BinderMeta)} (htele : fam.cvTa = fam.cvS)
    (hsort : fam.cvTa.type.stripPis (fam.p.nP + fam.p.nIdx) = some (bs, .sort fam.p.resSort))
    (hfv : Decl.fvarIdxLt 0 fam.cvS.type = true)
    (hbv : fam.cvS.type.looseBVarsBounded 0 = true) : FormerOpenTraceAt env fam := by
  rw [htele] at hsort
  have hs : (fam.cvS.type.stripPis (fam.p.nP + fam.p.nIdx)).isSome = true := by
    rw [hsort]; rfl
  refine ⟨?_, Decl.TracedSort.intro (Decl.OpenSortTrace.of_strip env _ _ ⟨bs, hsort⟩)
    (Core.LvEq.refl _)⟩
  rw [htele]
  exact Decl.TracedBinders.of_strip env hs hfv hbv

/-- A recursor generated from any telescope with the traced binders of the stored former's type
is the recursor generated from the registered telescope constant. -/
theorem FormerOpenTraceAt.recCheck {env : Env .anon} {fam : NativeFam .anon}
    {J : Judgements .anon} {cvR cvTb cvRa : ConstantVal .anon}
    {elim : LevelParam} {large : Bool} {rhs₀ rhss : List (Expr .anon)}
    (h : FormerOpenTraceAt env fam)
    (htrace : Decl.TracedBinders env (fam.p.nP + fam.p.nIdx) fam.cvS.type cvTb.type)
    (hrun : NativeRecJ J env (fam.recParts cvR elim large rhs₀) cvTb fam.ctorsA cvRa rhss) :
    NativeRecJ J env (fam.recParts cvR elim large rhs₀) fam.cvTa fam.ctorsA cvRa rhss := by
  have hp := htrace.prefixEq (fun _ _ hf => hf) h.binders
  exact Decl.NativeRecJ.of_prefix hp hrun

/-- A level reached by a result-sort walk from the stored former's type is level-equivalent to
the family's sort. -/
theorem FormerOpenTraceAt.result_lvEq {env : Env .anon} {fam : NativeFam .anon} {s : Level}
    (h : FormerOpenTraceAt env fam)
    (htrace : Decl.OpenSortTrace env 0 (fam.p.nP + fam.p.nIdx) fam.cvS.type s) :
    Core.LvEq s fam.p.resSort :=
  Decl.TracedSort.lvEq (fun _ _ hf => hf) (Decl.TracedSort.intro htrace (Core.LvEq.refl s))
    h.result

end IxVM.Refinement.Typing
