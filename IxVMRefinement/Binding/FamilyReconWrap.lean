import IxVMRefinement.Binding.FamilyReconBuilders
import IxVMRefinement.Binding.FamilyReconCons
import IxVMRefinement.Obs.KernelCheck7
import IxVMRefinement.Obs.KernelCheck8

/-! # Wrapper consumption, rule comparison, flat search, and raw-carrier bridges on `TmOExact`

Refines the circuit's comparison and search helpers used by `KernelModeled::check_recs` and
`KernelCheck::canonical_rules_at_pos`:

* `kexpr_struct_eq_oexact`: syntactic equality on `TmOExact` from `KernelCheck::kexpr_struct_eq = 1`.
* `WrapperObserved`, `ConsumesObs`, `WrapConsEqObs`, `WrapConsObs`: observed wrapper consumption
  under `wrapAt t E₀`, commuting with `Expr.liftLooseBVars` and `Expr.instantiate1Lift`, and
  refining `KernelCheck::lam_first_arity`, `KernelCheck::consume_wrapper`, `KernelCheck::wrap_dom`,
  `KernelCheck::wrap_binder`, and `KernelCheck::wrap_rel` (at any strictness mode, including
  `Let`-against-`Let` zeta expansion).
* `rule_lam_doms_spec` and `compare_rules_spec`: refine `KernelCheck::rule_lam_doms` and
  `KernelCheck::compare_rules` to `LamsAlong` and `RuleFollows`.
* `flat_find_pos_spec`, `flat_find_pos_kind_spec`, `flat_find_pos_kind_complete`: exact lookup
  and completeness on `FlatEntryRepExact` lists.
* `rawConvExpr_tmOExact_majorHeadAt` and `rawConvExpr_tmOExact_motiveCarrierAt`: connect
  `TmOExact` + `L1.RawConvExpr` on a recursor's heap type directly to `FamilyOf.majorHeadAt` and
  `FamilyOf.motiveCarrierAt`. -/

namespace IxVM.Refinement.Binding.FamilyRecon

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Consistency
open IxVM.Refinement.Binding.FamilyFlat
open IxVM.Refinement.Core (W KExpr KLevel KKey ExprLvEq LvEq LvEqList bmeta
  kexprEnum kexprListEnum kciEnum krrEnum krrListEnum addrTy addrListEnum ixAddr)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList klevelEnum klevelListEnum)

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Fast call-list membership and `kexpr_struct_eq` on `TmOExact` -/

local syntax "call_mem" : tactic
local macro_rules
  | `(tactic| call_mem) =>
    `(tactic| repeat first
      | assumption
      | exact List.mem_cons_self
      | exact List.mem_append_left _ (by assumption)
      | exact List.mem_append_left _ List.mem_cons_self
      | apply List.mem_cons_of_mem
      | apply List.mem_append_right)

private theorem repList_length_lt_wrap {en : String} {α : Type*}
    {R : Heap F → α → SourceValue F → Prop} {xs : List α} {p : SourceValue F}
    {nm : String} {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    {cs cs' rootCalls : List (Call F)}
    (hbd : Bounded rootCalls) (hsub : ∀ c ∈ cs, c ∈ rootCalls)
    (_ev : ObsFn W nm args h r h' cs')
    (hmem : (⟨nm, args, h⟩ : Call F) ∈ cs) (hp : p ∈ args)
    (hrep : RepList en R h xs p) : xs.length < 2 ^ 39 :=
  RomBound.bounded_length_lt hbd (hsub ⟨nm, args, h⟩ hmem) hp hrep

/-- **`KernelCheck::kexpr_struct_eq` returning `1` on two `TmOExact` heap terms** yields exact
syntactic equality `Ea = Eb`. -/
theorem kexpr_struct_eq_oexact {κ : _root_.Address → KKey} {Ea Eb : KExpr}
    {pa pb : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ha : TmOExact κ h Ea pa) (hb : TmOExact κ h Eb pb)
    (ev : ObsFn W "KernelCheck::kexpr_struct_eq" [pa, pb] h (.field 1) h' cs) :
    Ea = Eb := by
  obtain ⟨ka, ra⟩ := ha
  obtain ⟨kb, rb⟩ := hb
  exact Decl.kexpr_struct_eq_one
    (tmExact_depth_le ra (max ka kb) (Nat.le_max_left _ _))
    (tmExact_depth_le rb (max ka kb) (Nat.le_max_right _ _)) ev

/-! ## Observed wrapper consumption (`WrapConsEqObs` and `WrapConsObs`) -/

/-- A wrapper key `w` was observed at arity `n` by `Ingress::get_ci` (returning a `Defn` value)
and `KernelCheck::lam_first_arity` (returning `(1, n)`) in `calls`. -/
def WrapperObserved (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (w : KKey) (n : Nat) : Prop :=
  ∃ (a : Bytes.Address) (addr ptr nl ty val saf hint : SourceValue F)
    (h h_ci h_la : Heap F) (cs_ci cs_la : List (Call F)),
    Core.keyOf t (Core.ixAddr a) = w ∧
    Bytes.RepAddressRef Core.addrTy h a addr ∧
    ObsFn Core.W "Ingress::get_ci" [addr] h ptr h_ci cs_ci ∧
    (∀ cl ∈ cs_ci, cl ∈ calls) ∧
    loadValue h_ci ptr = .ok (.construct Core.kciEnum "Defn" [nl, ty, val, saf, hint]) ∧
    (⟨"KernelCheck::lam_first_arity", [val, .field 0], h_ci⟩ : Call F) ∈ calls ∧
    ObsFn Core.W "KernelCheck::lam_first_arity" [val, .field 0] h_ci
      (.tuple [.field 1, .field (n : F)]) h_la cs_la ∧
    (∀ cl ∈ cs_la, cl ∈ calls) ∧
    n < 549755813888

theorem WrapperObserved.mono {calls calls' : List (Call F)} {t : Ix.Kernel.RoleTable}
    {w : KKey} {n : Nat} (hsub : ∀ cl ∈ calls, cl ∈ calls')
    (h : WrapperObserved calls t w n) : WrapperObserved calls' t w n := by
  obtain ⟨a, addr, ptr, nl, ty, val, saf, hint, h0, h_ci, h_la, cs_ci, cs_la,
    hk, ha, ev_ci, hs_ci, hld, hcl_la, ev_la, hs_la, hn⟩ := h
  exact ⟨a, addr, ptr, nl, ty, val, saf, hint, h0, h_ci, h_la, cs_ci, cs_la,
    hk, ha, ev_ci, fun cl hcl => hsub cl (hs_ci cl hcl), hld, hsub _ hcl_la,
    ev_la, fun cl hcl => hsub cl (hs_la cl hcl), hn⟩

/-- Wrapper consumption carrying an observation predicate `ObsW` on every consumed wrapper. -/
inductive ConsumesObs (W : KKey → Option (Option Nat)) (ObsW : KKey → Nat → Prop) :
    KExpr → KExpr → Prop
  | refl (t : KExpr) : ConsumesObs W ObsW t t
  | step {t a c : KExpr} {w : KKey} {n : Nat} :
      consumeAt W t = some (some a) →
      appHead t = some w → W w = some (some n) → ObsW w n →
      ConsumesObs W ObsW a c → ConsumesObs W ObsW t c

theorem ConsumesObs.mono {W W' : KKey → Option (Option Nat)} {ObsW ObsW' : KKey → Nat → Prop}
    (hW : ∀ w x, W w = some x → W' w = some x)
    (hO : ∀ w n, ObsW w n → ObsW' w n) {t c : KExpr}
    (h : ConsumesObs W ObsW t c) : ConsumesObs W' ObsW' t c := by
  induction h with
  | refl t => exact .refl t
  | step hc hd hw ho _ ih =>
    exact .step (consumeAt_mono hW hc) hd (hW _ _ hw) (hO _ _ ho) ih

theorem ConsumesObs.toConsumes {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop}
    {t c : KExpr} (h : ConsumesObs W ObsW t c) : Consumes W t c := by
  induction h with
  | refl t => exact .refl t
  | step hc _ _ _ _ ih => exact .step hc ih

theorem ConsumesObs.of_wrap_none {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop}
    {t c : KExpr} {w : KKey} (h : ConsumesObs W ObsW t c)
    (hd : appHead t = some w) (hw : W w = some none) : c = t := by
  cases h with
  | refl => rfl
  | step _ hd' hw' _ _ =>
    have hw_eq := Option.some.inj (hd.symm.trans hd')
    subst hw_eq
    rw [hw] at hw'
    cases hw'

theorem ConsumesObs.of_appHead_none {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop}
    {t c : KExpr} (h : ConsumesObs W ObsW t c) (hd : appHead t = none) : c = t := by
  cases h with
  | refl => rfl
  | step _ hd' _ _ _ => rw [hd] at hd'; cases hd'

/-- Observed wrapper relation with syntactic equality at sort, constant, and free-variable leaves
(produced directly by `KernelCheck::wrap_rel` on `TmOExact`). -/
inductive WrapConsEqObs (W : KKey → Option (Option Nat)) (ObsW : KKey → Nat → Prop) :
    KExpr → KExpr → Prop
  | bvar (i : Nat) : WrapConsEqObs W ObsW (.bvar i) (.bvar i)
  | fvar (i : Nat) (t : KExpr) : WrapConsEqObs W ObsW (.fvar i t) (.fvar i t)
  | sort (u : KLevel) : WrapConsEqObs W ObsW (.sort u) (.sort u)
  | const (n : KKey) (us : List KLevel) : WrapConsEqObs W ObsW (.const n us) (.const n us)
  | lit (l : Ix.Kernel.Literal) : WrapConsEqObs W ObsW (.lit l) (.lit l)
  | app {f a f' a' : KExpr} :
      WrapConsEqObs W ObsW f f' → WrapConsEqObs W ObsW a a' →
      WrapConsEqObs W ObsW (.app f a) (.app f' a')
  | lam {t c b t' b' : KExpr} {m m' : Ix.Kernel.BinderMeta} :
      m.pw = m'.pw → ConsumesObs W ObsW t c →
      WrapConsEqObs W ObsW c t' → WrapConsEqObs W ObsW b b' →
      WrapConsEqObs W ObsW (.lam t b m) (.lam t' b' m')
  | forallE {t c b t' b' : KExpr} {m m' : Ix.Kernel.BinderMeta} :
      m.pw = m'.pw → ConsumesObs W ObsW t c →
      WrapConsEqObs W ObsW c t' → WrapConsEqObs W ObsW b b' →
      WrapConsEqObs W ObsW (.forallE t b m) (.forallE t' b' m')
  | letE {t v b t' v' b' : KExpr} {l l' : Ix.Kernel.LetMeta} :
      WrapConsEqObs W ObsW t t' → WrapConsEqObs W ObsW v v' → WrapConsEqObs W ObsW b b' →
      WrapConsEqObs W ObsW (.letE t v b l) (.letE t' v' b' l')
  | proj {s : KKey} {i : Nat} {e e' : KExpr} :
      WrapConsEqObs W ObsW e e' → WrapConsEqObs W ObsW (.proj s i e) (.proj s i e')

/-- Observed wrapper relation up to semantic level equality (matching `Ix.Kernel.Semantics.WrapRel`
with `ObsW` recorded at every consumed wrapper). -/
inductive WrapConsObs (W : KKey → Option (Option Nat)) (ObsW : KKey → Nat → Prop) :
    KExpr → KExpr → Prop
  | bvar (i : Nat) : WrapConsObs W ObsW (.bvar i) (.bvar i)
  | fvar {i : Nat} {t t' : KExpr} : ExprLvEq t t' → WrapConsObs W ObsW (.fvar i t) (.fvar i t')
  | sort {u v : KLevel} : LvEq u v → WrapConsObs W ObsW (.sort u) (.sort v)
  | const {n : KKey} {us vs : List KLevel} :
      LvEqList us vs → WrapConsObs W ObsW (.const n us) (.const n vs)
  | lit (l : Ix.Kernel.Literal) : WrapConsObs W ObsW (.lit l) (.lit l)
  | app {f a f' a' : KExpr} :
      WrapConsObs W ObsW f f' → WrapConsObs W ObsW a a' →
      WrapConsObs W ObsW (.app f a) (.app f' a')
  | lam {t c b t' b' : KExpr} {m m' : Ix.Kernel.BinderMeta} :
      m.pw = m'.pw → ConsumesObs W ObsW t c →
      WrapConsObs W ObsW c t' → WrapConsObs W ObsW b b' →
      WrapConsObs W ObsW (.lam t b m) (.lam t' b' m')
  | forallE {t c b t' b' : KExpr} {m m' : Ix.Kernel.BinderMeta} :
      m.pw = m'.pw → ConsumesObs W ObsW t c →
      WrapConsObs W ObsW c t' → WrapConsObs W ObsW b b' →
      WrapConsObs W ObsW (.forallE t b m) (.forallE t' b' m')
  | letE {t v b t' v' b' : KExpr} {l l' : Ix.Kernel.LetMeta} :
      WrapConsObs W ObsW t t' → WrapConsObs W ObsW v v' → WrapConsObs W ObsW b b' →
      WrapConsObs W ObsW (.letE t v b l) (.letE t' v' b' l')
  | proj {s : KKey} {i : Nat} {e e' : KExpr} :
      WrapConsObs W ObsW e e' → WrapConsObs W ObsW (.proj s i e) (.proj s i e')

theorem WrapConsEqObs.refl {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop} :
    ∀ e : KExpr, WrapConsEqObs W ObsW e e
  | .bvar i => .bvar i
  | .fvar i t => .fvar i t
  | .sort u => .sort u
  | .const n us => .const n us
  | .lit l => .lit l
  | .app f a => .app (refl f) (refl a)
  | .lam t b _ => .lam rfl (.refl t) (refl t) (refl b)
  | .forallE t b _ => .forallE rfl (.refl t) (refl t) (refl b)
  | .letE t v b _ => .letE (refl t) (refl v) (refl b)
  | .proj _ _ e => .proj (refl e)

theorem WrapConsEqObs.mono {W W' : KKey → Option (Option Nat)} {ObsW ObsW' : KKey → Nat → Prop}
    (hW : ∀ w x, W w = some x → W' w = some x) (hO : ∀ w n, ObsW w n → ObsW' w n)
    {g d : KExpr} (h : WrapConsEqObs W ObsW g d) : WrapConsEqObs W' ObsW' g d := by
  induction h with
  | bvar i => exact .bvar i
  | fvar i t => exact .fvar i t
  | sort u => exact .sort u
  | const n us => exact .const n us
  | lit l => exact .lit l
  | app _ _ ihf iha => exact .app ihf iha
  | lam hpw hcs _ _ ihd ihb => exact .lam hpw (hcs.mono hW hO) ihd ihb
  | forallE hpw hcs _ _ ihd ihb => exact .forallE hpw (hcs.mono hW hO) ihd ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | proj _ ihe => exact .proj ihe

theorem WrapConsEqObs.toWrapConsObs {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop}
    {g d : KExpr} (h : WrapConsEqObs W ObsW g d) : WrapConsObs W ObsW g d := by
  induction h with
  | bvar i => exact .bvar i
  | fvar _ t => exact .fvar (Core.exprLvEq_refl t)
  | sort u => exact .sort (fun _ => rfl)
  | const _ us => exact .const (Core.lvEqList_refl us)
  | lit l => exact .lit l
  | app _ _ ihf iha => exact .app ihf iha
  | lam hpw hcs _ _ ihd ihb => exact .lam hpw hcs ihd ihb
  | forallE hpw hcs _ _ ihd ihb => exact .forallE hpw hcs ihd ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | proj _ ihe => exact .proj ihe

theorem WrapConsObs.mono {W W' : KKey → Option (Option Nat)} {ObsW ObsW' : KKey → Nat → Prop}
    (hW : ∀ w x, W w = some x → W' w = some x) (hO : ∀ w n, ObsW w n → ObsW' w n)
    {g d : KExpr} (h : WrapConsObs W ObsW g d) : WrapConsObs W' ObsW' g d := by
  induction h with
  | bvar i => exact .bvar i
  | fvar ht => exact .fvar ht
  | sort hu => exact .sort hu
  | const hus => exact .const hus
  | lit l => exact .lit l
  | app _ _ ihf iha => exact .app ihf iha
  | lam hpw hcs _ _ ihd ihb => exact .lam hpw (hcs.mono hW hO) ihd ihb
  | forallE hpw hcs _ _ ihd ihb => exact .forallE hpw (hcs.mono hW hO) ihd ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | proj _ ihe => exact .proj ihe

theorem WrapConsObs.of_exprLvEq {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop}
    {g d : KExpr} (h : ExprLvEq g d) : WrapConsObs W ObsW g d := by
  induction h with
  | bvar => exact .bvar _
  | fvar ht => exact .fvar ht
  | sort hu => exact .sort hu
  | const hus => exact .const hus
  | lit => exact .lit _
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ ihd ihb => exact .lam rfl (.refl _) ihd ihb
  | forallE _ _ ihd ihb => exact .forallE rfl (.refl _) ihd ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | proj _ ihe => exact .proj ihe

/-! ### Spine, lifting, and substitution commutation for `ConsumesObs` and `WrapConsEqObs` -/

private theorem getAppFn_mkAppN_of_nonApp {hd : KExpr}
    (hna : ∀ f a, hd ≠ .app f a) :
    ∀ (args : List KExpr), (Ix.Kernel.Expr.mkAppN hd args).getAppFn = hd
  | [] => by
    cases hd with
    | app f a => exact absurd rfl (hna f a)
    | bvar _ | fvar _ _ | sort _ | const _ _ | lit _ | lam _ _ _ | forallE _ _ _
    | letE _ _ _ _ | proj _ _ _ => rfl
  | a :: as => by
    simp only [Ix.Kernel.Expr.mkAppN]
    have hrec : ∀ (l : List KExpr) (e : KExpr),
        (Ix.Kernel.Expr.mkAppN e l).getAppFn = e.getAppFn := by
      intro l
      induction l with
      | nil => intro _; rfl
      | cons x xs ih => intro e; simpa [Ix.Kernel.Expr.mkAppN, Ix.Kernel.Expr.getAppFn] using ih (.app e x)
    rw [hrec as (.app hd a)]
    simpa [Ix.Kernel.Expr.getAppFn] using getAppFn_mkAppN_of_nonApp hna []

private theorem getAppArgs_mkAppN_of_nonApp {hd : KExpr}
    (hna : ∀ f a, hd ≠ .app f a) :
    ∀ (args : List KExpr), (Ix.Kernel.Expr.mkAppN hd args).getAppArgs = args := by
  have hgo : ∀ (l acc : List KExpr) (e : KExpr),
      Ix.Kernel.Expr.getAppArgsAux (Ix.Kernel.Expr.mkAppN e l) acc =
        Ix.Kernel.Expr.getAppArgsAux e (l ++ acc) := by
    intro l
    induction l with
    | nil => intro _ _; rfl
    | cons x xs ih =>
      intro acc e
      simp only [Ix.Kernel.Expr.mkAppN, ih (acc := acc) (.app e x),
        Ix.Kernel.Expr.getAppArgsAux, List.cons_append]
  intro args
  unfold Ix.Kernel.Expr.getAppArgs
  rw [hgo args [] hd, List.append_nil]
  cases hd with
  | app f a => exact absurd rfl (hna f a)
  | bvar _ | fvar _ _ | sort _ | const _ _ | lit _ | lam _ _ _ | forallE _ _ _
  | letE _ _ _ _ | proj _ _ _ => rfl

private theorem mkAppN_getAppFn_getAppArgs (e : KExpr) :
    Ix.Kernel.Expr.mkAppN e.getAppFn e.getAppArgs = e := by
  have hgo : ∀ (e : KExpr) (acc : List KExpr),
      Ix.Kernel.Expr.mkAppN e.getAppFn (Ix.Kernel.Expr.getAppArgsAux e acc) =
        Ix.Kernel.Expr.mkAppN e acc := by
    intro e
    induction e with
    | app f a ihf _ =>
      intro acc
      simpa [Ix.Kernel.Expr.getAppFn, Ix.Kernel.Expr.getAppArgsAux, Ix.Kernel.Expr.mkAppN] using
        ihf (a :: acc)
    | bvar _ | fvar _ _ | sort _ | const _ _ | lit _ | lam _ _ _ | forallE _ _ _
    | letE _ _ _ _ | proj _ _ _ => intro _; rfl
  simpa [Ix.Kernel.Expr.getAppArgs] using hgo e []

private theorem mkAppN_liftLooseBVars_w (amount cutoff : Nat) :
    ∀ (args : List KExpr) (f : KExpr),
      (Ix.Kernel.Expr.mkAppN f args).liftLooseBVars amount cutoff =
        Ix.Kernel.Expr.mkAppN (f.liftLooseBVars amount cutoff)
          (args.map (Ix.Kernel.Expr.liftLooseBVars amount cutoff))
  | [], _ => rfl
  | a :: as, f => by
    simp only [Ix.Kernel.Expr.mkAppN, List.map_cons]
    exact mkAppN_liftLooseBVars_w amount cutoff as (.app f a)

private theorem mkAppN_instantiate1Lift_w (v : KExpr) (d : Nat) :
    ∀ (args : List KExpr) (f : KExpr),
      (Ix.Kernel.Expr.mkAppN f args).instantiate1Lift v d =
        Ix.Kernel.Expr.mkAppN (f.instantiate1Lift v d)
          (args.map (fun a => a.instantiate1Lift v d))
  | [], _ => rfl
  | a :: as, f => by
    simp only [Ix.Kernel.Expr.mkAppN, List.map_cons]
    exact mkAppN_instantiate1Lift_w v d as (.app f a)

private theorem consumeAt_some_some_inv {W : KKey → Option (Option Nat)} {t a : KExpr}
    (h : consumeAt W t = some (some a)) :
    ∃ (w : KKey) (us : List KLevel) (rest : List KExpr),
      t.getAppFn = .const w us ∧
      t.getAppArgs = a :: rest ∧
      W w = some (some (rest.length + 1)) := by
  have hc : consumeOf W (appHead t) t.getAppArgs = some (some a) := h
  cases hd : appHead t with
  | none => rw [hd] at hc; simp [consumeOf] at hc
  | some w =>
    rw [hd] at hc
    obtain ⟨us, hfn⟩ := appHead_some hd
    cases hl : t.getAppArgs with
    | nil => rw [hl] at hc; simp [consumeOf] at hc
    | cons a' rest =>
      rw [hl] at hc
      simp only [consumeOf] at hc
      cases hw : W w with
      | none => rw [hw] at hc; simp at hc
      | some k =>
        rw [hw] at hc
        simp only [Option.map_some, Option.some.injEq] at hc
        by_cases hk : k = some (rest.length + 1)
        · rw [ite_eq_left hk] at hc
          obtain rfl := Option.some.inj hc
          subst hk
          exact ⟨w, us, rest, hfn, hl, hw⟩
        · rw [ite_eq_right hk] at hc; cases hc

theorem ConsumesObs.liftLooseBVars {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop}
    (amount cutoff : Nat) {t c : KExpr} (h : ConsumesObs W ObsW t c) :
    ConsumesObs W ObsW (t.liftLooseBVars amount cutoff) (c.liftLooseBVars amount cutoff) := by
  induction h with
  | refl t => exact .refl _
  | @step t a c w n hc hd hw ho _ ih =>
    obtain ⟨w', us, rest, hfn, hargs, hw'⟩ := consumeAt_some_some_inv hc
    have hweq : w' = w := by
      unfold appHead at hd; rw [hfn] at hd; exact Option.some.inj hd
    subst hweq
    have ht_eq : t = Ix.Kernel.Expr.mkAppN (.const w' us) (a :: rest) := by
      rw [← hfn, ← hargs, mkAppN_getAppFn_getAppArgs]
    have htl : t.liftLooseBVars amount cutoff =
        Ix.Kernel.Expr.mkAppN (.const w' us)
          (a.liftLooseBVars amount cutoff :: rest.map (Ix.Kernel.Expr.liftLooseBVars amount cutoff)) := by
      rw [ht_eq, mkAppN_liftLooseBVars_w]; rfl
    have hfn' : (t.liftLooseBVars amount cutoff).getAppFn = .const w' us := by
      rw [htl]; exact getAppFn_mkAppN_of_nonApp (fun _ _ h => by cases h) _
    have hargs' : (t.liftLooseBVars amount cutoff).getAppArgs =
        a.liftLooseBVars amount cutoff :: rest.map (Ix.Kernel.Expr.liftLooseBVars amount cutoff) := by
      rw [htl]; exact getAppArgs_mkAppN_of_nonApp (fun _ _ h => by cases h) _
    have hhd' : appHead (t.liftLooseBVars amount cutoff) = some w' := by
      unfold appHead; rw [hfn']
    have hc' : consumeAt W (t.liftLooseBVars amount cutoff) =
        some (some (a.liftLooseBVars amount cutoff)) := by
      unfold consumeAt
      rw [hhd', hargs']
      simp [consumeOf, hw']
    exact .step hc' hhd' hw ho ih

theorem ConsumesObs.instantiate1Lift {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop}
    (v : KExpr) (d : Nat) {t c : KExpr} (h : ConsumesObs W ObsW t c) :
    ConsumesObs W ObsW (t.instantiate1Lift v d) (c.instantiate1Lift v d) := by
  induction h with
  | refl t => exact .refl _
  | @step t a c w n hc hd hw ho _ ih =>
    obtain ⟨w', us, rest, hfn, hargs, hw'⟩ := consumeAt_some_some_inv hc
    have hweq : w' = w := by
      unfold appHead at hd; rw [hfn] at hd; exact Option.some.inj hd
    subst hweq
    have ht_eq : t = Ix.Kernel.Expr.mkAppN (.const w' us) (a :: rest) := by
      rw [← hfn, ← hargs, mkAppN_getAppFn_getAppArgs]
    have hti : t.instantiate1Lift v d =
        Ix.Kernel.Expr.mkAppN (.const w' us)
          (a.instantiate1Lift v d :: rest.map (fun e => e.instantiate1Lift v d)) := by
      rw [ht_eq, mkAppN_instantiate1Lift_w]; rfl
    have hfn' : (t.instantiate1Lift v d).getAppFn = .const w' us := by
      rw [hti]; exact getAppFn_mkAppN_of_nonApp (fun _ _ h => by cases h) _
    have hargs' : (t.instantiate1Lift v d).getAppArgs =
        a.instantiate1Lift v d :: rest.map (fun e => e.instantiate1Lift v d) := by
      rw [hti]; exact getAppArgs_mkAppN_of_nonApp (fun _ _ h => by cases h) _
    have hhd' : appHead (t.instantiate1Lift v d) = some w' := by
      unfold appHead; rw [hfn']
    have hc' : consumeAt W (t.instantiate1Lift v d) =
        some (some (a.instantiate1Lift v d)) := by
      unfold consumeAt
      rw [hhd', hargs']
      simp [consumeOf, hw']
    exact .step hc' hhd' hw ho ih

theorem WrapConsEqObs.liftLooseBVars {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop}
    {g d : KExpr} (h : WrapConsEqObs W ObsW g d) :
    ∀ amount cutoff,
      WrapConsEqObs W ObsW (g.liftLooseBVars amount cutoff) (d.liftLooseBVars amount cutoff) := by
  induction h with
  | bvar i =>
    intro amount cutoff
    simp only [Ix.Kernel.Expr.liftLooseBVars]
    split <;> exact .bvar _
  | fvar i t => intro _ _; exact .fvar i t
  | sort u => intro _ _; exact .sort u
  | const n us => intro _ _; exact .const n us
  | lit l => intro _ _; exact .lit l
  | app _ _ ihf iha =>
    intro amount cutoff
    exact .app (ihf amount cutoff) (iha amount cutoff)
  | lam hpw hcs _ _ ihd ihb =>
    intro amount cutoff
    exact .lam hpw (hcs.liftLooseBVars amount cutoff) (ihd amount cutoff) (ihb amount (cutoff + 1))
  | forallE hpw hcs _ _ ihd ihb =>
    intro amount cutoff
    exact .forallE hpw (hcs.liftLooseBVars amount cutoff) (ihd amount cutoff) (ihb amount (cutoff + 1))
  | letE _ _ _ iht ihv ihb =>
    intro amount cutoff
    exact .letE (iht amount cutoff) (ihv amount cutoff) (ihb amount (cutoff + 1))
  | proj _ ihe =>
    intro amount cutoff
    exact .proj (ihe amount cutoff)

theorem WrapConsEqObs.instantiate1Lift {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop}
    {Vg Vd Bg Bd : KExpr}
    (hV : WrapConsEqObs W ObsW Vg Vd) (hB : WrapConsEqObs W ObsW Bg Bd) :
    ∀ d : Nat,
      WrapConsEqObs W ObsW (Bg.instantiate1Lift Vg d) (Bd.instantiate1Lift Vd d) := by
  induction hB with
  | bvar i =>
    intro d
    simp only [Ix.Kernel.Expr.instantiate1Lift]
    by_cases h1 : i = d
    · simp only [h1, ↓reduceIte]
      exact hV.liftLooseBVars d 0
    · simp only [h1, ↓reduceIte]
      split <;> exact .bvar _
  | fvar i t => intro _; exact .fvar i t
  | sort u => intro _; exact .sort u
  | const n us => intro _; exact .const n us
  | lit l => intro _; exact .lit l
  | app _ _ ihf iha => intro d; exact .app (ihf d) (iha d)
  | lam hpw hcs _ _ ihd ihb =>
    intro d
    exact .lam hpw (hcs.instantiate1Lift Vg d) (ihd d) (ihb (d + 1))
  | forallE hpw hcs _ _ ihd ihb =>
    intro d
    exact .forallE hpw (hcs.instantiate1Lift Vg d) (ihd d) (ihb (d + 1))
  | letE _ _ _ iht ihv ihb =>
    intro d
    exact .letE (iht d) (ihv d) (ihb (d + 1))
  | proj _ ihe =>
    intro d
    exact .proj (ihe d)

private def hasBVarAt (d : Nat) : KExpr → Bool
  | .bvar i => i == d
  | .fvar _ _ | .sort _ | .const _ _ | .lit _ => false
  | .app f a => hasBVarAt d f || hasBVarAt d a
  | .lam t b _ | .forallE t b _ => hasBVarAt d t || hasBVarAt (d + 1) b
  | .letE t v b _ => hasBVarAt d t || hasBVarAt d v || hasBVarAt (d + 1) b
  | .proj _ _ e => hasBVarAt d e

private theorem hasBVarAt_mkAppN_false {d : Nat} :
    ∀ {f : KExpr} {args : List KExpr},
      hasBVarAt d (Ix.Kernel.Expr.mkAppN f args) = false →
      hasBVarAt d f = false ∧ ∀ a ∈ args, hasBVarAt d a = false
  | f, [], h => ⟨h, fun _ hm => nomatch hm⟩
  | f, a :: as, h => by
    obtain ⟨hfa, has⟩ := hasBVarAt_mkAppN_false (f := .app f a) (args := as) h
    simp only [hasBVarAt, Bool.or_eq_false_iff] at hfa
    refine ⟨hfa.1, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hfa.2
    · exact has x hx'

private theorem hasBVarAt_false_instantiate1Lift :
    ∀ (e v₁ v₂ : KExpr) (d : Nat),
      hasBVarAt d e = false → e.instantiate1Lift v₁ d = e.instantiate1Lift v₂ d
  | .bvar i, v₁, v₂, d, h => by
    simp only [hasBVarAt, beq_eq_false_iff_ne] at h
    simp [Ix.Kernel.Expr.instantiate1Lift, h]
  | .fvar _ _, _, _, _, _ | .sort _, _, _, _, _ | .const _ _, _, _, _, _ | .lit _, _, _, _, _ => rfl
  | .app f a, v₁, v₂, d, h => by
    simp only [hasBVarAt, Bool.or_eq_false_iff] at h
    simp [Ix.Kernel.Expr.instantiate1Lift,
      hasBVarAt_false_instantiate1Lift f v₁ v₂ d h.1,
      hasBVarAt_false_instantiate1Lift a v₁ v₂ d h.2]
  | .lam t b m, v₁, v₂, d, h => by
    simp only [hasBVarAt, Bool.or_eq_false_iff] at h
    simp [Ix.Kernel.Expr.instantiate1Lift,
      hasBVarAt_false_instantiate1Lift t v₁ v₂ d h.1,
      hasBVarAt_false_instantiate1Lift b v₁ v₂ (d + 1) h.2]
  | .forallE t b m, v₁, v₂, d, h => by
    simp only [hasBVarAt, Bool.or_eq_false_iff] at h
    simp [Ix.Kernel.Expr.instantiate1Lift,
      hasBVarAt_false_instantiate1Lift t v₁ v₂ d h.1,
      hasBVarAt_false_instantiate1Lift b v₁ v₂ (d + 1) h.2]
  | .letE t v b l, v₁, v₂, d, h => by
    simp only [hasBVarAt, Bool.or_eq_false_iff] at h
    simp [Ix.Kernel.Expr.instantiate1Lift,
      hasBVarAt_false_instantiate1Lift t v₁ v₂ d h.1.1,
      hasBVarAt_false_instantiate1Lift v v₁ v₂ d h.1.2,
      hasBVarAt_false_instantiate1Lift b v₁ v₂ (d + 1) h.2]
  | .proj s i e, v₁, v₂, d, h => by
    simp [Ix.Kernel.Expr.instantiate1Lift, hasBVarAt_false_instantiate1Lift e v₁ v₂ d h]

private theorem ConsumesObs.hasBVarAt_false {W : KKey → Option (Option Nat)}
    {ObsW : KKey → Nat → Prop} {t c : KExpr} {d : Nat}
    (h : ConsumesObs W ObsW t c) (hb : hasBVarAt d t = false) : hasBVarAt d c = false := by
  induction h with
  | refl _ => exact hb
  | @step t a c _ _ hc _ _ _ _ ih =>
    obtain ⟨w, us, rest, hfn, hargs, -⟩ := consumeAt_some_some_inv hc
    have ht_eq : t = Ix.Kernel.Expr.mkAppN (.const w us) (a :: rest) := by
      rw [← hfn, ← hargs, mkAppN_getAppFn_getAppArgs]
    rw [ht_eq] at hb
    exact ih ((hasBVarAt_mkAppN_false hb).2 a List.mem_cons_self)

private theorem WrapConsEqObs.hasBVarAt_false {W : KKey → Option (Option Nat)}
    {ObsW : KKey → Nat → Prop} {g d : KExpr} (h : WrapConsEqObs W ObsW g d) :
    ∀ k, hasBVarAt k g = false → hasBVarAt k d = false := by
  induction h with
  | bvar _ | fvar _ _ | sort _ | const _ _ | lit _ => intro _ hk; exact hk
  | app _ _ ihf iha =>
    intro k hk
    simp only [hasBVarAt, Bool.or_eq_false_iff] at hk ⊢
    exact ⟨ihf k hk.1, iha k hk.2⟩
  | lam _ hcs _ _ ihd ihb =>
    intro k hk
    simp only [hasBVarAt, Bool.or_eq_false_iff] at hk ⊢
    exact ⟨ihd k (hcs.hasBVarAt_false hk.1), ihb (k + 1) hk.2⟩
  | forallE _ hcs _ _ ihd ihb =>
    intro k hk
    simp only [hasBVarAt, Bool.or_eq_false_iff] at hk ⊢
    exact ⟨ihd k (hcs.hasBVarAt_false hk.1), ihb (k + 1) hk.2⟩
  | letE _ _ _ iht ihv ihb =>
    intro k hk
    simp only [hasBVarAt, Bool.or_eq_false_iff] at hk ⊢
    exact ⟨⟨iht k hk.1.1, ihv k hk.1.2⟩, ihb (k + 1) hk.2⟩
  | proj _ ihe => intro k hk; exact ihe k hk

private theorem addrIn_liftLooseBVars_inv {S : _root_.Address → Prop} {κ : _root_.Address → KKey}
    (amount cutoff : Nat) :
    ∀ {E : KExpr}, AddrIn S κ (E.liftLooseBVars amount cutoff) → AddrIn S κ E
  | .bvar _, _ | .sort _, _ | .lit _, _ => trivial
  | .fvar _ _, h => h
  | .const _ _, h => h
  | .app f a, ⟨hf, ha⟩ =>
    ⟨addrIn_liftLooseBVars_inv amount cutoff hf, addrIn_liftLooseBVars_inv amount cutoff ha⟩
  | .lam t b _, ⟨ht, hb⟩ =>
    ⟨addrIn_liftLooseBVars_inv amount cutoff ht, addrIn_liftLooseBVars_inv amount (cutoff + 1) hb⟩
  | .forallE t b _, ⟨ht, hb⟩ =>
    ⟨addrIn_liftLooseBVars_inv amount cutoff ht, addrIn_liftLooseBVars_inv amount (cutoff + 1) hb⟩
  | .letE t v b _, ⟨ht, hv, hb⟩ =>
    ⟨addrIn_liftLooseBVars_inv amount cutoff ht, addrIn_liftLooseBVars_inv amount cutoff hv,
      addrIn_liftLooseBVars_inv amount (cutoff + 1) hb⟩
  | .proj _ _ e, ⟨hk, he⟩ => ⟨hk, addrIn_liftLooseBVars_inv amount cutoff he⟩

private theorem addrIn_of_instantiate1Lift_body {S : _root_.Address → Prop} {κ : _root_.Address → KKey}
    (V : KExpr) :
    ∀ {B : KExpr} (d : Nat), AddrIn S κ (B.instantiate1Lift V d) → AddrIn S κ B
  | .bvar _, _, _ | .sort _, _, _ | .lit _, _, _ => trivial
  | .fvar _ _, _, h => h
  | .const _ _, _, h => h
  | .app f a, d, ⟨hf, ha⟩ =>
    ⟨addrIn_of_instantiate1Lift_body V d hf, addrIn_of_instantiate1Lift_body V d ha⟩
  | .lam t b _, d, ⟨ht, hb⟩ =>
    ⟨addrIn_of_instantiate1Lift_body V d ht, addrIn_of_instantiate1Lift_body V (d + 1) hb⟩
  | .forallE t b _, d, ⟨ht, hb⟩ =>
    ⟨addrIn_of_instantiate1Lift_body V d ht, addrIn_of_instantiate1Lift_body V (d + 1) hb⟩
  | .letE t v b _, d, ⟨ht, hv, hb⟩ =>
    ⟨addrIn_of_instantiate1Lift_body V d ht, addrIn_of_instantiate1Lift_body V d hv,
      addrIn_of_instantiate1Lift_body V (d + 1) hb⟩
  | .proj _ _ e, d, ⟨hk, he⟩ => ⟨hk, addrIn_of_instantiate1Lift_body V d he⟩

private theorem addrIn_of_instantiate1Lift_val {S : _root_.Address → Prop} {κ : _root_.Address → KKey}
    (V : KExpr) :
    ∀ {B : KExpr} (d : Nat),
      hasBVarAt d B = true → AddrIn S κ (B.instantiate1Lift V d) → AddrIn S κ V
  | .bvar i, d, hb, h => by
    simp only [hasBVarAt, beq_iff_eq] at hb
    subst hb
    simp only [Ix.Kernel.Expr.instantiate1Lift, ↓reduceIte] at h
    exact addrIn_liftLooseBVars_inv i 0 h
  | .fvar _ _, _, hb, _ | .sort _, _, hb, _ | .const _ _, _, hb, _ | .lit _, _, hb, _ => by
    simp [hasBVarAt] at hb
  | .app f a, d, hb, ⟨hf, ha⟩ => by
    simp only [hasBVarAt, Bool.or_eq_true] at hb
    rcases hb with h1 | h2
    · exact addrIn_of_instantiate1Lift_val V d h1 hf
    · exact addrIn_of_instantiate1Lift_val V d h2 ha
  | .lam t b _, d, hb, ⟨ht, hbb⟩ => by
    simp only [hasBVarAt, Bool.or_eq_true] at hb
    rcases hb with h1 | h2
    · exact addrIn_of_instantiate1Lift_val V d h1 ht
    · exact addrIn_of_instantiate1Lift_val V (d + 1) h2 hbb
  | .forallE t b _, d, hb, ⟨ht, hbb⟩ => by
    simp only [hasBVarAt, Bool.or_eq_true] at hb
    rcases hb with h1 | h2
    · exact addrIn_of_instantiate1Lift_val V d h1 ht
    · exact addrIn_of_instantiate1Lift_val V (d + 1) h2 hbb
  | .letE t v b _, d, hb, ⟨ht, hv, hbb⟩ => by
    simp only [hasBVarAt, Bool.or_eq_true] at hb
    rcases hb with (h1 | h2) | h3
    · exact addrIn_of_instantiate1Lift_val V d h1 ht
    · exact addrIn_of_instantiate1Lift_val V d h2 hv
    · exact addrIn_of_instantiate1Lift_val V (d + 1) h3 hbb
  | .proj _ _ e, d, hb, ⟨_, he⟩ =>
    addrIn_of_instantiate1Lift_val V d hb he

/-! ### Shape preservation lemmas on `WrapConsEqObs` and `wrapAt` on inductives -/

theorem WrapConsEqObs.forallE_inv {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop}
    {t b d : KExpr} {m : Ix.Kernel.BinderMeta}
    (h : WrapConsEqObs W ObsW (.forallE t b m) d) :
    ∃ (c t' b' : KExpr) (m' : Ix.Kernel.BinderMeta),
      d = .forallE t' b' m' ∧ m.pw = m'.pw ∧
      ConsumesObs W ObsW t c ∧ WrapConsEqObs W ObsW c t' ∧ WrapConsEqObs W ObsW b b' := by
  cases h with
  | forallE hpw hcs ht hb => exact ⟨_, _, _, _, rfl, hpw, hcs, ht, hb⟩

theorem WrapConsEqObs.peelForalls {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop} :
    ∀ (n : Nat) {g d g' : KExpr},
      WrapConsEqObs W ObsW g d →
      FamilyFlat.peelForalls n g = some g' →
      ∃ d', FamilyFlat.peelForalls n d = some d' ∧ WrapConsEqObs W ObsW g' d'
  | 0, _, d, _, h, hp => by
    simp only [FamilyFlat.peelForalls, Option.some.injEq] at hp
    subst hp
    exact ⟨d, rfl, h⟩
  | n + 1, g, d, g', h, hp => by
    cases g with
    | forallE t b m =>
      obtain ⟨_, _, b', _, rfl, -, -, -, hb⟩ := h.forallE_inv
      exact WrapConsEqObs.peelForalls n hb hp
    | bvar _ | fvar _ _ | sort _ | const _ _ | lit _ | app _ _ | lam _ _ _
    | letE _ _ _ _ | proj _ _ _ =>
      simp [FamilyFlat.peelForalls] at hp

theorem WrapConsEqObs.not_forallE {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop}
    {g d : KExpr} (h : WrapConsEqObs W ObsW g d)
    (hng : ∀ t b m, g ≠ .forallE t b m) : ∀ t' b' m', d ≠ .forallE t' b' m' := by
  cases h with
  | forallE _ _ _ _ => exact absurd rfl (hng _ _ _)
  | bvar _ | fvar _ _ | sort _ | const _ _ | lit _ | app _ _ | lam _ _ _ _
  | letE _ _ _ | proj _ => intro _ _ _ he; cases he

theorem WrapConsEqObs.bvar_inv {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop}
    {i : Nat} {d : KExpr} (h : WrapConsEqObs W ObsW (.bvar i) d) : d = .bvar i := by
  cases h; rfl

theorem WrapConsEqObs.sort_inv {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop}
    {u : KLevel} {d : KExpr} (h : WrapConsEqObs W ObsW (.sort u) d) : d = .sort u := by
  cases h; rfl

theorem WrapConsEqObs.const_inv {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop}
    {n : KKey} {us : List KLevel} {d : KExpr}
    (h : WrapConsEqObs W ObsW (.const n us) d) : d = .const n us := by
  cases h; rfl

theorem WrapConsEqObs.app_inv {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop}
    {f a d : KExpr} (h : WrapConsEqObs W ObsW (.app f a) d) :
    ∃ f' a', d = .app f' a' ∧ WrapConsEqObs W ObsW f f' ∧ WrapConsEqObs W ObsW a a' := by
  cases h with
  | app hf ha => exact ⟨_, _, rfl, hf, ha⟩

theorem WrapConsEqObs.getAppFn_const_eq {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop}
    {g d : KExpr} {k : KKey} {us : List KLevel}
    (h : WrapConsEqObs W ObsW g d) (hfn : g.getAppFn = .const k us) :
    d.getAppFn = .const k us ∧ d.getAppArgs.length = g.getAppArgs.length := by
  induction h with
  | const n vs =>
    simp only [Ix.Kernel.Expr.getAppFn, Ix.Kernel.Expr.const.injEq] at hfn
    obtain ⟨rfl, rfl⟩ := hfn
    exact ⟨rfl, rfl⟩
  | app _ _ ihf _ =>
    simp only [Ix.Kernel.Expr.getAppFn] at hfn ⊢
    obtain ⟨h1, h2⟩ := ihf hfn
    refine ⟨h1, ?_⟩
    rw [Ix.Kernel.Expr.getAppArgs_app, Ix.Kernel.Expr.getAppArgs_app]
    simp [h2]
  | bvar _ | fvar _ _ | sort _ | lit _ | lam _ _ _ _ | forallE _ _ _ _ | letE _ _ _ | proj _ =>
    simp [Ix.Kernel.Expr.getAppFn] at hfn

theorem WrapConsEqObs.getAppFn_bvar_eq {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop}
    {g d : KExpr} {i : Nat}
    (h : WrapConsEqObs W ObsW g d) (hfn : g.getAppFn = .bvar i) :
    d.getAppFn = .bvar i ∧ d.getAppArgs.length = g.getAppArgs.length := by
  induction h with
  | bvar j =>
    simp only [Ix.Kernel.Expr.getAppFn, Ix.Kernel.Expr.bvar.injEq] at hfn
    subst hfn
    exact ⟨rfl, rfl⟩
  | app _ _ ihf _ =>
    simp only [Ix.Kernel.Expr.getAppFn] at hfn ⊢
    obtain ⟨h1, h2⟩ := ihf hfn
    refine ⟨h1, ?_⟩
    rw [Ix.Kernel.Expr.getAppArgs_app, Ix.Kernel.Expr.getAppArgs_app]
    simp [h2]
  | fvar _ _ | sort _ | const _ _ | lit _ | lam _ _ _ _ | forallE _ _ _ _ | letE _ _ _ | proj _ =>
    simp [Ix.Kernel.Expr.getAppFn] at hfn

/-- An inductive projection address is never a definition, so `wrapAt` returns `some none`. -/
theorem wrapAt_ind_none {t : Ix.Kernel.RoleTable} {E : Ixon.Env} (hwf : t.wf = true)
    {a : _root_.Address} {c : Ixon.Constant} {p : Ixon.InductProj}
    (hc : recordOf E a = some c) (hi : c.info = .iPrj p) :
    wrapAt t E (Core.keyOf t a) = some none := by
  unfold wrapAt
  rw [keyAddr_keyOf hwf a]
  unfold defnAt
  rw [hc, hi]

theorem wrapAt_of_indDataAt_some {t : Ix.Kernel.RoleTable} {E : Ixon.Env} (hwf : t.wf = true)
    {a : _root_.Address} {id : IndData}
    (hind : indDataAt t E a = some (some id)) :
    wrapAt t E (Core.keyOf t a) = some none := by
  unfold indDataAt at hind
  cases hc : recordOf E a with
  | none => rw [hc] at hind; cases hind
  | some c =>
    rw [hc] at hind
    cases hi : c.info with
    | iPrj p => exact wrapAt_ind_none hwf hc hi
    | _ => rw [hi] at hind; cases hind

/-! ## `KernelCheck::lam_first_arity` and `KernelCheck::consume_wrapper` on `TmOExact` -/

private theorem tmExact_lam_descent {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {E : KExpr} {p w20 xb xm : SourceValue F} {steps : Nat}
    (hE : Decl.TmExact κ d Γ h k E p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Lam" [w20, xb, xm]))
    (hdesc : RomBound.HeapDescent h (.enum kexprEnum) xb steps) :
    RomBound.HeapDescent h (.enum kexprEnum) p (steps + 1) := by
  cases hE with
  | lam cell _ _ _ =>
    obtain ⟨_, hxs⟩ := Core.load_cell cell ld
    injection hxs with _ hxs; injection hxs with h2 _
    subst h2
    exact .down cell (by simp [Value.type]) (by simp [RomBound.cellArgs]) hdesc
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ | const cell _ _
  | app cell _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _
  | litStr cell _ _ | proj cell _ _ =>
    exact False.elim (Core.load_cell_ne cell ld (by decide))

private theorem tmExact_ptr_descent_zero {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {E : KExpr} {p : SourceValue F}
    (hE : Decl.TmExact κ d Γ h k E p) :
    RomBound.HeapDescent h (.enum kexprEnum) p 0 := by
  cases hE with
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ | const cell _ _
  | app cell _ _ | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _
  | litNat cell _ _ | litStr cell _ _ | proj cell _ _ =>
    exact .here cell (by simp [Value.type])

private theorem lam_first_arity_go_oexact {κ : _root_.Address → KKey} :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → fname = "KernelCheck::lam_first_arity" →
      ∀ (n : Nat) (E : KExpr) (xv xk : SourceValue F),
        args = [xv, .field (n : F)] → r = .tuple [.field 1, xk] →
        (∀ steps, RomBound.HeapDescent h (.enum kexprEnum) xv steps →
          n + steps < 549755813888) →
        TmOExact κ h E xv →
        ∃ k_out steps : Nat,
          xk = .field (k_out : F) ∧
          k_out = n + steps ∧
          RomBound.HeapDescent h (.enum kexprEnum) xv steps ∧
          Ix.Kernel.Semantics.lamFirstArity E n = some k_out ∧
          h' = h :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' cs => fname = "KernelCheck::lam_first_arity" →
      ∀ (n : Nat) (E : KExpr) (xv xk : SourceValue F),
        args = [xv, .field (n : F)] → r = .tuple [.field 1, xk] →
        (∀ steps, RomBound.HeapDescent h (.enum kexprEnum) xv steps →
          n + steps < 549755813888) →
        TmOExact κ h E xv →
        ∃ k_out steps : Nat,
          xk = .field (k_out : F) ∧
          k_out = n + steps ∧
          RomBound.HeapDescent h (.enum kexprEnum) xv steps ∧
          Ix.Kernel.Semantics.lamFirstArity E n = some k_out ∧
          h' = h)
    (fun fname args h r h' cs ev ih hfn n E xv xk hargs hr hbnd_desc hE => by
      subst hfn hargs hr
      match Obs.«KernelCheck::lam_first_arity».obs ev with
      | .Lam_Succ_other (he118 := he) ..
      | .Lam_other (he141 := he) ..
      | .BVar_n0 (he186 := he) ..
      | .BVar_other_other (he264 := he) ..
      | .other (he287 := he) .. =>
        injection he with hxs; injection hxs with h01 _
        exact absurd (Value.field.inj h01) one_ne_zero
      | .Lam_Succ_Zero (w20 := w20) (x_b := xb) (x_m := xm) (x_z := xz)
          (cs82 := cs82) (v86 := v86)
          (ld12 := ld12) (ld47 := ld47) (ld71 := ld71)
          (op107 := op107) (ev84 := ev84) (hc109 := hc109) =>
        subst hc109
        obtain ⟨k_d, hEd⟩ := hE
        obtain ⟨T, B, ℓ, rfl, _, hB, hℓ⟩ := hEd.lam_of_load ld12
        obtain ⟨u, rfl, hu⟩ := IxVM.Refinement.Levels.rep_succ_of_load hℓ ld47
        obtain rfl := IxVM.Refinement.Levels.rep_zero_of_load hu ld71
        have hv86 : v86 = .field ((n + 1 : Nat) : F) := Decl.evalBinOp_add_one n op107
        rw [hv86] at ev84
        have hbnd_b : ∀ steps, RomBound.HeapDescent h (.enum kexprEnum) xb steps →
            (n + 1) + steps < 549755813888 := by
          intro steps hdb
          have hlt := hbnd_desc (steps + 1) (tmExact_lam_descent hEd ld12 hdb)
          omega
        obtain ⟨k_out, steps, hxk, hk_eq, hdb, hlam, hh⟩ :=
          ih _ _ _ _ _ _ (by simp only [List.length_cons, List.length_append]; omega)
            ev84 rfl (n + 1) B xb xk rfl rfl hbnd_b ⟨k_d + 1, hB⟩
        refine ⟨k_out, steps + 1, hxk, by omega, tmExact_lam_descent hEd ld12 hdb, ?_, hh⟩
        simpa [Ix.Kernel.Semantics.lamFirstArity, bmeta, Ix.Kernel.Level.zeronessOf] using hlam
      | .BVar_other_n0 (x_i := xi) (y215 := y215)
          (ld12 := ld12) (hne201 := hne201) (op230 := op230) (op221 := op221)
          (he240 := he240) (he254 := he254) .. =>
        injection he240 with hxs; injection hxs with _ hxs; injection hxs with hxk _
        have hxk' : xk = .field (n : F) := hxk
        obtain ⟨k_d, hEd⟩ := hE
        cases n with
        | zero => exact absurd rfl hne201
        | succ m =>
          have hy215 : y215 = .field (m : F) := Decl.evalBinOp_sub_succ m op230
          obtain ⟨i_f, rfl, _, rfl⟩ := TmOExact.bvar_of_load ⟨k_d, hEd⟩ ld12
          rw [hy215] at op221
          simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
            Except.ok.injEq, Value.field.injEq] at op221
          have hif : i_f = (m : F) := sub_eq_zero.mp op221
          have hn_lt : m + 1 < 549755813888 := by
            have := hbnd_desc 0 (tmExact_ptr_descent_zero hEd)
            omega
          have hval_i : ZMod.val i_f = m := by
            rw [hif]
            exact ZMod.val_natCast_of_lt (Nat.lt_trans (by omega : m < 549755813888) (by decide))
          refine ⟨m + 1, 0, hxk', by omega, tmExact_ptr_descent_zero hEd, ?_, he254⟩
          simp [Ix.Kernel.Semantics.lamFirstArity, hval_i])

/-- **`KernelCheck::consume_wrapper` returning `(1, xa)` on `TmOExact` + `AddrIn (Held R)`**
consumes one observed wrapper under `wrapAt t E₀` and records `WrapperObserved rootCalls t w n`. -/
theorem consume_wrapper_one_oexact {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    {E : KExpr} {xt xa : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hsub : ∀ cl ∈ cs, cl ∈ rootCalls)
    (hE : TmOExact (Core.keyOf t) h E xt)
    (hEin : AddrIn (Held R) (Core.keyOf t) E)
    (ev : ObsFn W "KernelCheck::consume_wrapper" [xt] h (.tuple [.field 1, xa]) h' cs) :
    ∃ (A : KExpr) (w : KKey) (n : Nat),
      consumeAt (wrapAt t E₀) E = some (some A) ∧
      appHead E = some w ∧
      wrapAt t E₀ w = some (some n) ∧
      WrapperObserved rootCalls t w n ∧
      TmOExact (Core.keyOf t) h' A xa ∧
      AddrIn (Held R) (Core.keyOf t) A := by
  match Obs.«KernelCheck::consume_wrapper».obs ev with
  | .Const_Cons_Defn_n1_bind_other (he276 := he) ..
  | .Const_Cons_Defn_other (he299 := he) ..
  | .Const_Cons_other (he323 := he) ..
  | .Const_other (he347 := he) ..
  | .other (he371 := he) .. =>
    injection he with hxs; injection hxs with h01 _
    exact absurd (Value.field.inj h01) one_ne_zero
  | .Const_Cons_Defn_n1_bind_n0 (m2 := m2) (cs12 := cs12) (x_h := xh) (x_args := xargs)
      (x_w := xw) (w55 := w55) (x_a := xa') (x_rest := xrest) (m96 := m96) (p104 := p104)
      (cs110 := cs110) (w127 := w127) (w128 := w128) (x_v := xv) (w129 := w129) (w130 := w130)
      (m157 := m157) (cs168 := cs168) (x_k := xk) (y214 := y214) (x222 := x222)
      (m224 := m224) (cs233 := cs233)
      (ev14 := ev14) (ld47 := ld47) (ld77 := ld77) (ev112 := ev112) (ld106 := ld106)
      (ev170 := ev170) (ev235 := ev235) (op229 := op229) (op220 := op220)
      (he252 := he252) (he266 := he266) (hc267 := hc) .. =>
    injection he252 with hxs; injection hxs with _ hxs; injection hxs with hxa _
    subst hxa he266
    obtain ⟨xh', xargs', hd, args, hr_sp, hhd, hargs_rep, hmk_eq, hhd_nonapp⟩ :=
      collect_spine_tmOExact ev14 hE
    injection hr_sp with hsp; injection hsp with hx1 hsp; injection hsp with hx2 _
    subst hx1 hx2
    obtain ⟨wa, us, rfl, rwa, -⟩ := TmOExact.const_of_load hhd ld47
    obtain ⟨A, rest, rfl, hA_m2, hrest_m2⟩ := Core.RepList.cons_of_load hargs_rep ld77
    have hE_eq : E = Ix.Kernel.Expr.mkAppN (.const (Core.keyOf t (ixAddr wa)) us) (A :: rest) :=
      hmk_eq.symm
    have hfn_E : E.getAppFn = .const (Core.keyOf t (ixAddr wa)) us := by
      rw [hE_eq]; exact getAppFn_mkAppN_of_nonApp (fun _ _ h => by cases h) _
    have hargs_E : E.getAppArgs = A :: rest := by
      rw [hE_eq]; exact getAppArgs_mkAppN_of_nonApp (fun _ _ h => by cases h) _
    have hmk_in : ∀ {f : KExpr} {xs : List KExpr},
        AddrIn (Held R) (Core.keyOf t) (Ix.Kernel.Expr.mkAppN f xs) →
        AddrIn (Held R) (Core.keyOf t) f ∧ ∀ x ∈ xs, AddrIn (Held R) (Core.keyOf t) x := by
      intro f xs
      induction xs generalizing f with
      | nil => intro hf; exact ⟨hf, fun _ hx => nomatch hx⟩
      | cons x xs ih =>
        intro hfx
        obtain ⟨hfa, hxs⟩ := ih hfx
        obtain ⟨hf, hx⟩ := hfa
        exact ⟨hf, fun y hy => by
          rcases List.mem_cons.mp hy with rfl | hy'
          · exact hx
          · exact hxs y hy'⟩
    have hEin_mk := hE_eq ▸ hEin
    obtain ⟨hconst_in, hargs_in⟩ := hmk_in hEin_mk
    have hSwa : Held R (ixAddr wa) := hconst_in (ixAddr wa) rfl
    have hA_in : AddrIn (Held R) (Core.keyOf t) A := hargs_in A List.mem_cons_self
    have sub_ci : ∀ cl ∈ cs110, cl ∈ rootCalls := fun cl hcl' => hsub cl (by rw [hc]; call_mem)
    obtain ⟨hyes, -⟩ := defnLoad_ofStore ht hwf hS hH hbd hRsub hcl hlv sub_ci hSwa rwa ev112 ld106
    obtain ⟨nl, V, -, -, hV, -, hdefnAt, -⟩ := hyes w127 w128 xv w129 w130 rfl
    have hcl_la : (⟨"KernelCheck::lam_first_arity", [xv, .field 0], m96⟩ : Call F) ∈ rootCalls :=
      hsub _ (by rw [hc]; call_mem)
    have sub_la : ∀ cl ∈ cs168, cl ∈ rootCalls := fun cl hcl' => hsub cl (by rw [hc]; call_mem)
    have hbnd_la : ∀ steps, RomBound.HeapDescent m96 (.enum kexprEnum) xv steps →
        0 + steps < 549755813888 := by
      intro steps hdesc
      simpa using RomBound.bounded_descent_lt hbd hcl_la List.mem_cons_self hdesc
    obtain ⟨k_out, steps, hxk, hk_steps, hdesc_v, hlam_V, hm157⟩ :=
      lam_first_arity_go_oexact _ _ _ _ _ _ ev170 rfl 0 V xv xk rfl rfl hbnd_la hV
    subst hxk hm157
    have hk_lt : k_out < 549755813888 := by
      have := hbnd_la steps hdesc_v; omega
    have ext_ci : Heap.Extends m2 m96 := ev112.heap_extends
    have hrest_m96 := tmOExactList_mono ext_ci hrest_m2
    obtain ⟨hx222, hm224⟩ := kexpr_length_spec ev235 hrest_m96
    subst hx222 hm224
    have hrest_lt : rest.length < 2 ^ 39 :=
      repList_length_lt_wrap hbd hsub ev235 (by rw [hc]; call_mem) (by simp) hrest_m96
    have hy214 : y214 = .field ((rest.length + 1 : Nat) : F) := Decl.evalBinOp_add_one rest.length op229
    rw [hy214] at op220
    simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
      Except.ok.injEq, Value.field.injEq] at op220
    have hkf_eq : (k_out : F) = ((rest.length + 1 : Nat) : F) := sub_eq_zero.mp op220
    have hk_eq : k_out = rest.length + 1 := by
      have h1 : (k_out : F).val = k_out :=
        ZMod.val_natCast_of_lt (Nat.lt_trans hk_lt (by decide))
      have h2 : ((rest.length + 1 : Nat) : F).val = rest.length + 1 :=
        ZMod.val_natCast_of_lt (Nat.lt_trans (by omega : rest.length + 1 < 549755813889) (by decide))
      have hv := congrArg ZMod.val hkf_eq
      omega
    subst hk_eq
    have hwrap : wrapAt t E₀ (Core.keyOf t (ixAddr wa)) = some (some (rest.length + 1)) := by
      unfold wrapAt
      rw [keyAddr_keyOf hwf (ixAddr wa), hdefnAt, hlam_V]
    have hhd_E : appHead E = some (Core.keyOf t (ixAddr wa)) := by
      unfold appHead; rw [hfn_E]
    have hcons : consumeAt (wrapAt t E₀) E = some (some A) := by
      unfold consumeAt
      rw [hhd_E, hargs_E]
      simp [consumeOf, hwrap]
    have hobs : WrapperObserved rootCalls t (Core.keyOf t (ixAddr wa)) (rest.length + 1) :=
      ⟨wa, xw, p104, w127, w128, xv, w129, w130, m2, m96, m96, cs110, cs168,
        rfl, rwa, ev112, sub_ci, ld106, hcl_la, ev170, sub_la, hk_lt⟩
    exact ⟨A, Core.keyOf t (ixAddr wa), rest.length + 1, hcons, hhd_E, hwrap, hobs,
      hA_m2.mono ext_ci, hA_in⟩

/-! ## `KernelCheck::wrap_rel`, `wrap_dom`, and `wrap_binder` on `TmOExact` -/

private theorem wrap_rel_family_oexact {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R)) :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → r = .field 1 →
      (∀ cl ∈ cs, cl ∈ rootCalls) →
      ((fname = "KernelCheck::wrap_rel" →
        ∀ (xsm xg xd : SourceValue F) (G D : KExpr),
          args = [xsm, xg, xd] →
          TmOExact (Core.keyOf t) h G xg → TmOExact (Core.keyOf t) h D xd →
          AddrIn (Held R) (Core.keyOf t) G →
          WrapConsEqObs (wrapAt t E₀) (WrapperObserved rootCalls t) G D) ∧
       (fname = "KernelCheck::wrap_dom" →
        ∀ (xsm xt xt2 : SourceValue F) (T T2 : KExpr),
          args = [xsm, xt, xt2] →
          TmOExact (Core.keyOf t) h T xt → TmOExact (Core.keyOf t) h T2 xt2 →
          AddrIn (Held R) (Core.keyOf t) T →
          ∃ C : KExpr,
            ConsumesObs (wrapAt t E₀) (WrapperObserved rootCalls t) T C ∧
            WrapConsEqObs (wrapAt t E₀) (WrapperObserved rootCalls t) C T2) ∧
       (fname = "KernelCheck::wrap_binder" →
        ∀ (xsm xt xb xm xt2 xb2 xm2 : SourceValue F) (T B T2 B2 : KExpr) (ℓ ℓ2 : KLevel),
          args = [xsm, xt, xb, xm, xt2, xb2, xm2] →
          TmOExact (Core.keyOf t) h T xt → TmOExact (Core.keyOf t) h B xb →
          RepKLevel h ℓ xm →
          TmOExact (Core.keyOf t) h T2 xt2 → TmOExact (Core.keyOf t) h B2 xb2 →
          RepKLevel h ℓ2 xm2 →
          AddrIn (Held R) (Core.keyOf t) T → AddrIn (Held R) (Core.keyOf t) B →
          (bmeta ℓ).pw = (bmeta ℓ2).pw ∧
          (∃ C : KExpr,
            ConsumesObs (wrapAt t E₀) (WrapperObserved rootCalls t) T C ∧
            WrapConsEqObs (wrapAt t E₀) (WrapperObserved rootCalls t) C T2) ∧
          WrapConsEqObs (wrapAt t E₀) (WrapperObserved rootCalls t) B B2)) :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' cs => r = .field 1 → (∀ cl ∈ cs, cl ∈ rootCalls) →
      ((fname = "KernelCheck::wrap_rel" →
        ∀ (xsm xg xd : SourceValue F) (G D : KExpr),
          args = [xsm, xg, xd] →
          TmOExact (Core.keyOf t) h G xg → TmOExact (Core.keyOf t) h D xd →
          AddrIn (Held R) (Core.keyOf t) G →
          WrapConsEqObs (wrapAt t E₀) (WrapperObserved rootCalls t) G D) ∧
       (fname = "KernelCheck::wrap_dom" →
        ∀ (xsm xt xt2 : SourceValue F) (T T2 : KExpr),
          args = [xsm, xt, xt2] →
          TmOExact (Core.keyOf t) h T xt → TmOExact (Core.keyOf t) h T2 xt2 →
          AddrIn (Held R) (Core.keyOf t) T →
          ∃ C : KExpr,
            ConsumesObs (wrapAt t E₀) (WrapperObserved rootCalls t) T C ∧
            WrapConsEqObs (wrapAt t E₀) (WrapperObserved rootCalls t) C T2) ∧
       (fname = "KernelCheck::wrap_binder" →
        ∀ (xsm xt xb xm xt2 xb2 xm2 : SourceValue F) (T B T2 B2 : KExpr) (ℓ ℓ2 : KLevel),
          args = [xsm, xt, xb, xm, xt2, xb2, xm2] →
          TmOExact (Core.keyOf t) h T xt → TmOExact (Core.keyOf t) h B xb →
          RepKLevel h ℓ xm →
          TmOExact (Core.keyOf t) h T2 xt2 → TmOExact (Core.keyOf t) h B2 xb2 →
          RepKLevel h ℓ2 xm2 →
          AddrIn (Held R) (Core.keyOf t) T → AddrIn (Held R) (Core.keyOf t) B →
          (bmeta ℓ).pw = (bmeta ℓ2).pw ∧
          (∃ C : KExpr,
            ConsumesObs (wrapAt t E₀) (WrapperObserved rootCalls t) T C ∧
            WrapConsEqObs (wrapAt t E₀) (WrapperObserved rootCalls t) C T2) ∧
          WrapConsEqObs (wrapAt t E₀) (WrapperObserved rootCalls t) B B2)))
    (fun fname args h r h' cs ev ih hr hsub => by
      subst hr
      refine ⟨fun hfn xsm xg xd G D hargs hG hD hGin => ?_,
        fun hfn xsm xt xt2 T T2 hargs hT hT2 hTin => ?_,
        fun hfn xsm xt xb xm xt2 xb2 xm2 T B T2 B2 ℓ ℓ2 hargs hT hB hℓ hT2 hB2 hℓ2 hTin hBin => ?_⟩
      · -- `KernelCheck::wrap_rel`
        subst hfn hargs
        match Obs.«KernelCheck::wrap_rel».obs ev with
        | .Let_Let_n1_other (he166 := he) ..
        | .Let_Let_other (he173 := he) ..
        | .Let_other (he180 := he) ..
        | .other_Let (he224 := he) ..
        | .other_other_App_App_other (he351 := he) ..
        | .other_other_App_other (he358 := he) ..
        | .other_other_Lam_other (he476 := he) ..
        | .other_other_Forall_other (he594 := he) ..
        | .other_other_Proj_Proj_other (he746 := he) ..
        | .other_other_Proj_other (he753 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .Let_Let_n1_n1 (x_t := xt) (x_v := xv) (x_b := xb)
            (x_t2 := xt2) (x_v2 := xv2) (x_b2 := xb2)
            (m70 := m70) (cs81 := cs81) (m105 := m105) (cs116 := cs116) (cs142 := cs142)
            (ld12 := ld12) (ld46 := ld46) (ev83 := ev83) (ev118 := ev118) (ev144 := ev144)
            (hc161 := hc) .. =>
          obtain ⟨_, Vg, Bg, rfl, -, hVg, hBg⟩ := TmOExact.letE_of_load hG ld12
          obtain ⟨_, Vd, Bd, rfl, -, hVd, hBd⟩ := TmOExact.letE_of_load hD ld46
          have e1 := ev83.heap_extends
          have e2 := ev118.heap_extends
          have hBg_in : AddrIn (Held R) (Core.keyOf t) Bg :=
            addrIn_of_instantiate1Lift_body Vg 0 hGin
          have hBB := (ih _ _ _ _ _ _ (by rw [hc]; simp only [List.length_cons, List.length_append]; omega)
            ev144 rfl (fun cl hcl' => hsub cl (by rw [hc]; call_mem))).1
            rfl xsm xb xb2 Bg Bd rfl (hBg.mono (e1.trans e2)) (hBd.mono (e1.trans e2)) hBg_in
          cases huse : hasBVarAt 0 Bg with
          | true =>
            have hVg_in : AddrIn (Held R) (Core.keyOf t) Vg :=
              addrIn_of_instantiate1Lift_val Vg 0 huse hGin
            have hVV := (ih _ _ _ _ _ _ (by rw [hc]; simp only [List.length_cons, List.length_append]; omega)
              ev118 rfl (fun cl hcl' => hsub cl (by rw [hc]; call_mem))).1
              rfl xsm xv xv2 Vg Vd rfl (hVg.mono e1) (hVd.mono e1) hVg_in
            exact WrapConsEqObs.instantiate1Lift hVV hBB 0
          | false =>
            have huse_d : hasBVarAt 0 Bd = false := hBB.hasBVarAt_false 0 huse
            rw [hasBVarAt_false_instantiate1Lift Bg Vg (.sort .zero) 0 huse,
                hasBVarAt_false_instantiate1Lift Bd Vd (.sort .zero) 0 huse_d]
            exact WrapConsEqObs.instantiate1Lift (.sort .zero) hBB 0
        | .other_other_App_App_n1 (x_f := xf) (x_a := xa) (x_f2 := xf2) (x_a2 := xa2)
            (m290 := m290) (cs301 := cs301) (cs327 := cs327)
            (ld242 := ld242) (ld271 := ld271) (ev303 := ev303) (ev329 := ev329)
            (hc346 := hc) .. =>
          obtain ⟨Ef, Ea, rfl, hEf, hEa⟩ := TmOExact.app_of_load hG ld242
          obtain ⟨Ef2, Ea2, rfl, hEf2, hEa2⟩ := TmOExact.app_of_load hD ld271
          obtain ⟨hEf_in, hEa_in⟩ := hGin
          have e1 := ev303.heap_extends
          have hf := (ih _ _ _ _ _ _ (by rw [hc]; simp only [List.length_cons, List.length_append]; omega)
            ev303 rfl (fun cl hcl' => hsub cl (by rw [hc]; call_mem))).1
            rfl xsm xf xf2 Ef Ef2 rfl hEf hEf2 hEf_in
          have ha := (ih _ _ _ _ _ _ (by rw [hc]; simp only [List.length_cons, List.length_append]; omega)
            ev329 rfl (fun cl hcl' => hsub cl (by rw [hc]; call_mem))).1
            rfl xsm xa xa2 Ea Ea2 rfl (hEa.mono e1) (hEa2.mono e1) hEa_in
          exact .app hf ha
        | .other_other_Lam_Lam (x_t := xt) (x_b := xb) (x_m := xm)
            (x_t2 := xt2) (x_b2 := xb2) (x_m2 := xm2) (cs420 := cs420)
            (ld242 := ld242) (ld394 := ld394) (ev422 := ev422) (hc471 := hc) .. =>
          obtain ⟨T, B, ℓ, rfl, hT, hB, hℓ⟩ := TmOExact.lam_of_load hG ld242
          obtain ⟨T2, B2, ℓ2, rfl, hT2, hB2, hℓ2⟩ := TmOExact.lam_of_load hD ld394
          obtain ⟨hT_in, hB_in⟩ := hGin
          obtain ⟨hpw, ⟨C, hcs, hCT⟩, hBB⟩ :=
            (ih _ _ _ _ _ _ (by rw [hc]; simp only [List.length_cons, List.length_append]; omega)
              ev422 rfl (fun cl hcl' => hsub cl (by rw [hc]; call_mem))).2.2
              rfl xsm xt xb xm xt2 xb2 xm2 T B T2 B2 ℓ ℓ2 rfl hT hB hℓ hT2 hB2 hℓ2 hT_in hB_in
          exact .lam hpw hcs hCT hBB
        | .other_other_Forall_Forall (x_t := xt) (x_b := xb) (x_m := xm)
            (x_t2 := xt2) (x_b2 := xb2) (x_m2 := xm2) (cs538 := cs538)
            (ld242 := ld242) (ld512 := ld512) (ev540 := ev540) (hc589 := hc) .. =>
          obtain ⟨T, B, ℓ, rfl, hT, hB, hℓ⟩ := TmOExact.forallE_of_load hG ld242
          obtain ⟨T2, B2, ℓ2, rfl, hT2, hB2, hℓ2⟩ := TmOExact.forallE_of_load hD ld512
          obtain ⟨hT_in, hB_in⟩ := hGin
          obtain ⟨hpw, ⟨C, hcs, hCT⟩, hBB⟩ :=
            (ih _ _ _ _ _ _ (by rw [hc]; simp only [List.length_cons, List.length_append]; omega)
              ev540 rfl (fun cl hcl' => hsub cl (by rw [hc]; call_mem))).2.2
              rfl xsm xt xb xm xt2 xb2 xm2 T B T2 B2 ℓ ℓ2 rfl hT hB hℓ hT2 hB2 hℓ2 hT_in hB_in
          exact .forallE hpw hcs hCT hBB
        | .other_other_Proj_Proj_n1 (x_s := xs) (x_i := xi) (x_e := xe)
            (x_s2 := xs2) (x_i2 := xi2) (x_e2 := xe2)
            (m654 := m654) (x662 := x662) (y663 := y663) (m664 := m664)
            (cs673 := cs673) (cs695 := cs695) (v698 := v698) (cs722 := cs722)
            (ld242 := ld242) (ld630 := ld630) (ev675 := ev675) (op712 := op712)
            (ev697 := ev697) (op669 := op669) (ev724 := ev724) (hc741 := hc) .. =>
          obtain ⟨ag, ig, Eg, rfl, rfl, rag, hEg⟩ := TmOExact.proj_of_load hG ld242
          obtain ⟨ad, id_, Ed, rfl, rfl, rad, hEd⟩ := TmOExact.proj_of_load hD ld630
          obtain ⟨-, hEg_in⟩ := hGin
          obtain ⟨hx662, rfl⟩ := Lib.address_eq_spec ev675 rag rad
          simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
            Except.ok.injEq] at op712
          subst op712
          obtain ⟨hy663, rfl⟩ := Lib.is_zero_spec ev697
          rw [hx662, hy663] at op669
          simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
            Except.ok.injEq, Value.field.injEq] at op669
          have hag_eq : ag = ad := by
            by_contra hne
            rw [if_neg hne] at op669
            simp at op669
          subst hag_eq
          have hig_eq : ig = id_ := by
            by_contra hne
            have hsub0 : ig - id_ ≠ 0 := sub_ne_zero.mpr hne
            rw [if_neg hsub0] at op669
            simp at op669
          subst hig_eq
          have he := (ih _ _ _ _ _ _ (by rw [hc]; simp only [List.length_cons, List.length_append]; omega)
            ev724 rfl (fun cl hcl' => hsub cl (by rw [hc]; call_mem))).1
            rfl xsm xe xe2 Eg Ed rfl hEg hEd hEg_in
          exact .proj he
        | .other_other_other (cs763 := cs763) (ev765 := ev765) .. =>
          have heq := kexpr_struct_eq_oexact hG hD ev765
          subst heq
          exact .refl _
      · -- `KernelCheck::wrap_dom`
        subst hfn hargs
        match Obs.«KernelCheck::wrap_dom».obsx ev with
        | .other_n0_other_other (he_vjzsmrqa := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .Let (cs41 := cs41) (ev43 := ev43) (hc60 := hc) .. =>
          have hw := (ih _ _ _ _ _ _ (by rw [hc]; simp only [List.length_cons]; omega)
            ev43 rfl (fun cl hcl' => hsub cl (by rw [hc]; call_mem))).1
            rfl xsm xt xt2 T T2 rfl hT hT2 hTin
          exact ⟨T, .refl T, hw⟩
        | .other_n0_n1 (cs_inoibkuh := cs1) (ev_teknbelh := ev1) (hc_mhrqvtgu := hc) .. =>
          have hw := (ih _ _ _ _ _ _ (by rw [hc]; simp only [List.length_cons]; omega)
            ev1 rfl (fun cl hcl' => hsub cl (by rw [hc]; call_mem))).1
            rfl xsm xt xt2 T T2 rfl hT hT2 hTin
          exact ⟨T, .refl T, hw⟩
        | .other_n0_other_n1_bind (m_fwvfxwkq := m1) (cs_inoibkuh := cs1) (m_iludgrvx := m2)
            (cs_szysaksf := cs2) (x_a := xa) (cs_bhijnlkz := cs3)
            (ev_teknbelh := ev1) (ev_tyrbnlfr := ev2) (ev_jqflmfnr := ev3)
            (hc_uuoaavue := hc) .. =>
          have e1 := ev1.heap_extends
          have e2 := ev2.heap_extends
          obtain ⟨A, w, n, hcons, hhd, hwrap, hobs, hA, hAin⟩ :=
            consume_wrapper_one_oexact ht hwf hS hH hbd hRsub hcl hlv
              (fun cl hcl' => hsub cl (by rw [hc]; call_mem)) (hT.mono e1) hTin ev2
          obtain ⟨C, hcs, hCT2⟩ :=
            (ih _ _ _ _ _ _ (by rw [hc]; simp only [List.length_cons, List.length_append]; omega)
              ev3 rfl (fun cl hcl' => hsub cl (by rw [hc]; call_mem))).2.1
              rfl xsm xa xt2 A T2 rfl hA (hT2.mono (e1.trans e2)) hAin
          exact ⟨C, .step hcons hhd hwrap hobs hcs, hCT2⟩
        | .other_other_n1_bind (m108 := m1) (cs119 := cs1) (x_a := xa) (cs151 := cs2)
            (ev121 := ev1) (ev153 := ev2) (hc170 := hc) .. =>
          have e1 := ev1.heap_extends
          obtain ⟨A, w, n, hcons, hhd, hwrap, hobs, hA, hAin⟩ :=
            consume_wrapper_one_oexact ht hwf hS hH hbd hRsub hcl hlv
              (fun cl hcl' => hsub cl (by rw [hc]; call_mem)) hT hTin ev1
          obtain ⟨C, hcs, hCT2⟩ :=
            (ih _ _ _ _ _ _ (by rw [hc]; simp only [List.length_cons, List.length_append]; omega)
              ev2 rfl (fun cl hcl' => hsub cl (by rw [hc]; call_mem))).2.1
              rfl xsm xa xt2 A T2 rfl hA (hT2.mono e1) hAin
          exact ⟨C, .step hcons hhd hwrap hobs hcs, hCT2⟩
        | .other_other_other (m108 := m1) (cs119 := cs1) (cs_lzopkfda := cs2)
            (ev121 := ev1) (ev_sarmpwvb := ev2) (hc176 := hc) .. =>
          have e1 := ev1.heap_extends
          have hw := (ih _ _ _ _ _ _ (by rw [hc]; simp only [List.length_cons, List.length_append]; omega)
            ev2 rfl (fun cl hcl' => hsub cl (by rw [hc]; call_mem))).1
            rfl xsm xt xt2 T T2 rfl (hT.mono e1) (hT2.mono e1) hTin
          exact ⟨T, .refl T, hw⟩
      · -- `KernelCheck::wrap_binder`
        subst hfn hargs
        match Obs.«KernelCheck::wrap_binder».obs ev with
        | .n1_other (he98 := he) .. | .other (he105 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .n1_n1 (m2 := m2) (cs13 := cs13) (m37 := m37) (cs48 := cs48) (cs74 := cs74)
            (ev15 := ev15) (ev50 := ev50) (ev76 := ev76) (hc93 := hc) .. =>
          have hpw_f := pw_eq_exact hℓ hℓ2 ev15
          have hpw : (bmeta ℓ).pw = (bmeta ℓ2).pw := by
            unfold bmeta
            by_contra hne
            rw [if_neg hne] at hpw_f
            exact absurd (Value.field.inj hpw_f) one_ne_zero
          have e1 := ev15.heap_extends
          have e2 := ev50.heap_extends
          obtain ⟨C, hcs, hCT2⟩ :=
            (ih _ _ _ _ _ _ (by rw [hc]; simp only [List.length_cons, List.length_append]; omega)
              ev50 rfl (fun cl hcl' => hsub cl (by rw [hc]; call_mem))).2.1
              rfl xsm xt xt2 T T2 rfl (hT.mono e1) (hT2.mono e1) hTin
          have hBB :=
            (ih _ _ _ _ _ _ (by rw [hc]; simp only [List.length_cons, List.length_append]; omega)
              ev76 rfl (fun cl hcl' => hsub cl (by rw [hc]; call_mem))).1
              rfl xsm xb xb2 B B2 rfl (hB.mono (e1.trans e2)) (hB2.mono (e1.trans e2)) hBin
          exact ⟨hpw, ⟨C, hcs, hCT2⟩, hBB⟩)

/-- **`KernelCheck::wrap_rel` returning `1` on two `TmOExact` heap terms** (with `AddrIn (Held R)`
on the generated left side) certifies `WrapConsEqObs (wrapAt t E₀) (WrapperObserved rootCalls t) G D`,
at any strictness mode `xsm`. -/
theorem wrap_rel_one_oexact {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    {xsm xg xd : SourceValue F} {G D : KExpr} {h h' : Heap F} {cs : List (Call F)}
    (hsub : ∀ cl ∈ cs, cl ∈ rootCalls)
    (hG : TmOExact (Core.keyOf t) h G xg) (hD : TmOExact (Core.keyOf t) h D xd)
    (hGin : AddrIn (Held R) (Core.keyOf t) G)
    (ev : ObsFn W "KernelCheck::wrap_rel" [xsm, xg, xd] h (.field 1) h' cs) :
    WrapConsEqObs (wrapAt t E₀) (WrapperObserved rootCalls t) G D :=
  (wrap_rel_family_oexact ht hwf hS hH hbd hRsub hcl hlv _ _ _ _ _ _ ev rfl hsub).1
    rfl xsm xg xd G D rfl hG hD hGin

/-- Weakened to `WrapConsObs` (semantic level equality at leaves). -/
theorem wrap_rel_one_wrapConsObs {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    {xsm xg xd : SourceValue F} {G D : KExpr} {h h' : Heap F} {cs : List (Call F)}
    (hsub : ∀ cl ∈ cs, cl ∈ rootCalls)
    (hG : TmOExact (Core.keyOf t) h G xg) (hD : TmOExact (Core.keyOf t) h D xd)
    (hGin : AddrIn (Held R) (Core.keyOf t) G)
    (ev : ObsFn W "KernelCheck::wrap_rel" [xsm, xg, xd] h (.field 1) h' cs) :
    WrapConsObs (wrapAt t E₀) (WrapperObserved rootCalls t) G D :=
  (wrap_rel_one_oexact ht hwf hS hH hbd hRsub hcl hlv hsub hG hD hGin ev).toWrapConsObs

/-- **`ConsumesObs` converts to IxC's `WrapDom`** whenever every observed wrapper has matching
`wrapperArity find?`. -/
theorem ConsumesObs.toWrapDom_obs {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop}
    {find? : KKey → Option (Ix.Kernel.ConstantInfo .anon)}
    (hW : ∀ w n, W w = some (some n) → ObsW w n → Ix.Kernel.Semantics.wrapperArity find? w = some n)
    {t c : KExpr} (h : ConsumesObs W ObsW t c) :
    ∀ {t' : KExpr}, Ix.Kernel.Semantics.WrapRel find? c t' →
      Ix.Kernel.Semantics.WrapDom find? t t' := by
  induction h with
  | refl _ => intro _ hr; exact .keep hr
  | @step t a c w n hc hd hw ho _ ih =>
    intro t' hr
    obtain ⟨w', us, rest, hfn, hargs, hw'⟩ := consumeAt_some_some_inv hc
    have hweq : w' = w := by
      unfold appHead at hd; rw [hfn] at hd; exact Option.some.inj hd
    subst hweq
    have hneq : rest.length + 1 = n := Option.some.inj (Option.some.inj (hw'.symm.trans hw))
    subst hneq
    have hcw : Ix.Kernel.Semantics.consumeWrapper find? t = some a := by
      simp [Ix.Kernel.Semantics.consumeWrapper, hfn, hargs, hW w' (rest.length + 1) hw ho]
    exact .consume hcw (ih hr)

/-- **`WrapConsObs` converts to IxC's `WrapRel`** whenever every observed wrapper has matching
`wrapperArity find?`. -/
theorem WrapConsObs.toWrapRel_obs {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop}
    {find? : KKey → Option (Ix.Kernel.ConstantInfo .anon)}
    (hW : ∀ w n, W w = some (some n) → ObsW w n → Ix.Kernel.Semantics.wrapperArity find? w = some n)
    {g d : KExpr} (h : WrapConsObs W ObsW g d) :
    Ix.Kernel.Semantics.WrapRel find? g d := by
  induction h with
  | bvar i => exact .bvar i
  | fvar ht => exact .fvar (exprLvEq_wrapRel find? ht)
  | sort hu => exact .sort hu
  | const hus => exact .const (wrapLevels_of_lvEqList hus)
  | lit l => exact .lit l
  | app _ _ ihf iha => exact .app ihf iha
  | lam hpw hcs _ _ ihd ihb => exact .lam hpw (hcs.toWrapDom_obs hW ihd) ihb
  | forallE hpw hcs _ _ ihd ihb => exact .forallE hpw (hcs.toWrapDom_obs hW ihd) ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | proj _ ihe => exact .proj ihe

/-! ## `KernelCheck::rule_lam_doms` and `KernelCheck::compare_rules` on `TmOExact` -/

private theorem evalBinOp_add_nat_wrap {a b : Nat} {v : SourceValue F}
    (op : evalBinOp .add (.field (a : F)) (.field (b : F)) = .ok v) :
    v = .field (((a + b : Nat) : F)) := by
  simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
    Except.ok.injEq] at op
  rw [← op, Nat.cast_add]

private theorem evalBinOp_sub_nat_wrap {a b : Nat} {v : SourceValue F}
    (hle : b ≤ a) (op : evalBinOp .sub (.field (a : F)) (.field (b : F)) = .ok v) :
    v = .field (((a - b : Nat) : F)) := by
  simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
    Except.ok.injEq] at op
  rw [← op, Nat.cast_sub hle]

/-- **`KernelCheck::rule_lam_doms` on `TmOExact`** certifies `LamsAlong elim n L P R` and
returns `R` represented on `TmOExact`. -/
theorem rule_lam_doms_spec {κ : _root_.Address → KKey} {elim : KLevel} {xelim : SourceValue F} :
    ∀ (n : Nat) {L P : KExpr} {xl xp r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      n < 4611686018427387904 →
      TmOExact κ h L xl → TmOExact κ h P xp → RepKLevel h elim xelim →
      ObsFn W "KernelCheck::rule_lam_doms" [xl, xp, .field (n : F), xelim] h r h' cs →
      ∃ R : KExpr, LamsAlong elim n L P R ∧ TmOExact κ h' R r := by
  intro n
  induction n with
  | zero =>
    intro L P xl xp r h h' cs _ hL _ _ ev
    match Obs.«KernelCheck::rule_lam_doms».obs ev with
    | .n0 (he16 := hr) (he17 := hh) .. =>
      subst hr hh
      exact ⟨L, .zero, hL⟩
    | .other (hne19 := hne) .. => exact absurd rfl hne
  | succ n ih =>
    intro L P xl xp r h h' cs hn hL hP helim ev
    match Obs.«KernelCheck::rule_lam_doms».obs ev with
    | .n0 (hv14 := hv) .. =>
      have h0 : ((n + 1 : Nat) : F) = 0 := Value.field.inj hv
      have hval : ((n + 1 : Nat) : F).val = n + 1 :=
        ZMod.val_natCast_of_lt (Nat.lt_trans hn (by decide))
      have hz := congrArg ZMod.val h0
      simp only [hval, ZMod.val_zero] at hz
      omega
    | .other (x_dl := xdl) (x_bl := xbl) (x_ll := xll) (v68 := v68) (m71 := m71) (cs79 := cs79)
        (x_dp := xdp) (x_bp := xbp) (w124 := w124) (v151 := v151) (m154 := m154) (cs162 := cs162)
        (cs191 := cs191) (v196 := v196)
        (ld34 := ld34) (ev81 := ev81) (heq104 := heq104) (ld116 := ld116)
        (ev164 := ev164) (heq187 := heq187) (op225 := op225) (ev193 := ev193) .. =>
      subst heq104 heq187
      obtain ⟨dl, bl, ll, rfl, hdl, hbl, hll⟩ := TmOExact.lam_of_load hL ld34
      have hpw_f := pw_eq_exact hll helim ev81
      have hpw : (bmeta ll).pw = elim.zeronessOf := by
        unfold bmeta
        by_contra hne
        rw [if_neg hne] at hpw_f
        exact absurd (Value.field.inj hpw_f) one_ne_zero
      have e1 := ev81.heap_extends
      obtain ⟨dp, bp, lp, rfl, hdp, hbp, -⟩ := TmOExact.forallE_of_load (hP.mono e1) ld116
      have hdom_eq : dl = dp := kexpr_struct_eq_oexact (hdl.mono e1) hdp ev164
      subst hdom_eq
      have e2 := ev164.heap_extends
      have hv196 : v196 = .field (n : F) := Decl.evalBinOp_sub_succ n op225
      rw [hv196] at ev193
      obtain ⟨R, hlam, hR⟩ := ih (by omega)
        (hbl.mono (e1.trans e2)) (hbp.mono e2) (helim.mono (e1.trans e2)) ev193
      exact ⟨R, .succ hpw (Core.exprLvEq_refl dl) hlam, hR⟩

/-- **`KernelCheck::compare_rules` on `RecRulesRep` and canonical body list** certifies
`RuleFollows` for every rule in `rus`, matching `MemberRecon`'s rule clause. -/
theorem compare_rules_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {S : _root_.Address → Prop} {rb : _root_.Address} {crb : Ixon.Constant}
    {rs : Array Ixon.MutConst} {nl : Nat} {base : F}
    {nP nMot nMin numCtors minorOff : Nat} {elim : KLevel} {ty : KExpr}
    {xblk xidx xelim xty : SourceValue F}
    (hbd : Bounded rootCalls)
    (hsum_lt : nP + nMot + nMin < 4611686018427387904) :
    ∀ (rus : List Ixon.RecursorRule) (cbs : List KExpr) (pos : Nat)
      {xst xcan r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      rus.length ≤ cbs.length →
      minorOff + pos + rus.length ≤ nMin →
      (∀ cl ∈ cs, cl ∈ rootCalls) →
      RecRulesRep t E₀ S rb crb rs nl base h pos rus xst →
      RepList kexprListEnum (TmOExact (Core.keyOf t)) h cbs xcan →
      TmOExact (Core.keyOf t) h ty xty →
      RepKLevel h elim xelim →
      ObsFn W "KernelCheck::compare_rules"
        [xst, xcan, .field (nP : F), .field (nMot : F), .field (nMin : F),
          xblk, xidx, .field (numCtors : F), .field (pos : F), xelim, xty, .field (minorOff : F)]
        h r h' cs →
      ∀ (i : Nat) (ru : Ixon.RecursorRule), rus[i]? = some ru →
        ∃ rhs cb,
          loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) nl
            (base + 1 + ((pos + i : Nat) : F)) ru.rhs = some rhs ∧
          cbs[i]? = some cb ∧
          RuleFollows ty nP nMot nMin (minorOff + (pos + i)) ru.fields.toNat elim rhs cb := by
  intro rus
  induction rus with
  | nil =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i ru hi
    cases hi
  | cons ru rest ih =>
    intro cbs pos xst xcan r h h' cs hlen hmin hsub hrrep hcbs hty helim ev
    match Obs.«KernelCheck::compare_rules».obs ev with
    | .Nil (ld12 := ld12) .. =>
      cases hrrep with
      | cons cell _ _ => exact absurd (Core.load_cell cell ld12).1 (by decide)
    | .Cons_Nil (ld302 := ld302) (ev125 := ev125) (ev165 := ev165) .. =>
      have e0 := ev125.heap_extends.trans ev165.heap_extends
      have hcbs_nil := Core.RepList.nil_of_load (tmOExactList_mono e0 hcbs) ld302
      subst hcbs_nil
      simp at hlen
    | .Cons_Cons (x_rest := xrest) (x_cidx := xcidx) (x_nf := xnf) (x_rhs := xrhs)
        (v112 := v112) (m115 := m115) (cs123 := cs123) (m150 := m150) (p157 := p157)
        (cs163 := cs163) (x_cbody := xcbody) (x_crest := xcrest) (v332 := v332) (x340 := x340)
        (v359 := v359) (v377 := v377) (m378 := m378) (cs388 := cs388) (m424 := m424)
        (p431 := p431) (cs437 := cs437) (v441 := v441) (x455 := x455) (x_mdom := xmdom)
        (w477 := w477) (w478 := w478) (v494 := v494) (m495 := m495) (cs505 := cs505)
        (v509 := v509) (v540 := v540) (m541 := m541) (cs551 := cs551) (v597 := v597)
        (m600 := m600) (cs608 := cs608) (cs637 := cs637) (v648 := v648)
        (ld12 := ld12) (ev125 := ev125) (ev165 := ev165) (ld302 := ld302)
        (op355 := op355) (op347 := op347) (op374 := op374) (ev390 := ev390)
        (op470 := op470) (op462 := op462) (ev439 := ev439) (ld433 := ld433)
        (op531 := op531) (ev507 := ev507) (ev553 := ev553) (ev610 := ev610)
        (heq633 := heq633) (op721 := op721) (ev639 := ev639) (hc744 := hc) .. =>
      subst heq633
      cases hrrep with
      | cons cell hhead htail =>
        obtain ⟨_, hxs⟩ := Core.load_cell cell ld12
        injection hxs with hv_eq hxs; injection hxs with hrest_eq _
        subst hrest_eq
        obtain ⟨rhs, rhsPtr, hv_mk, hnf_lt, hloaded, hrhs_tm, -⟩ := hhead
        rw [hv_mk] at hv_eq
        injection hv_eq with _ _ hmk_args
        injection hmk_args with hcidx_eq hmk_args
        injection hmk_args with hnf_eq hmk_args
        injection hmk_args with hrhs_eq _
        subst hcidx_eq hnf_eq hrhs_eq
        have e_150 : Heap.Extends h m150 := ev125.heap_extends.trans ev165.heap_extends
        obtain ⟨cb, cbs_rest, rfl, hcb_tm, hcbs_rest⟩ :=
          Core.RepList.cons_of_load (tmOExactList_mono e_150 hcbs) ld302
        have hx340 : x340 = .field (((nP + nMot : Nat) : F)) := evalBinOp_add_nat_wrap op355
        rw [hx340] at op347
        have hv332 : v332 = .field (((nP + nMot + nMin : Nat) : F)) := evalBinOp_add_nat_wrap op347
        rw [hv332] at ev390
        have hv359 : v359 = .field (((minorOff + pos : Nat) : F)) := evalBinOp_add_nat_wrap op374
        obtain ⟨afterPre, hlams1, hafterPre_tm⟩ :=
          rule_lam_doms_spec (nP + nMot + nMin) (by omega)
            (hrhs_tm.mono e_150) (hty.mono e_150) (helim.mono e_150) ev390
        have e_378 : Heap.Extends m150 m378 := ev390.heap_extends
        have hx455 : x455 = .field (((nP + nMot : Nat) : F)) := evalBinOp_add_nat_wrap op470
        rw [hx455, hv359] at op462
        have hv441 : v441 = .field (((nP + nMot + (minorOff + pos) : Nat) : F)) :=
          evalBinOp_add_nat_wrap op462
        rw [hv441] at ev439
        have hpeel_lt : nP + nMot + (minorOff + pos) < 9223372036854775808 := by
          simp at hmin; omega
        obtain ⟨hm424, peeled, hpeel_eq, hpeeled_tm⟩ :=
          peel_n_foralls_tmOExact (nP + nMot + (minorOff + pos)) hpeel_lt ev439
            (hty.mono (e_150.trans e_378))
        subst hm424
        obtain ⟨mdom, mrest, ml, rfl, hmdom_tm, -, -⟩ := TmOExact.forallE_of_load hpeeled_tm ld433
        rw [hv359] at op531
        have hmo_le : minorOff + pos ≤ nMin := by simp at hmin; omega
        have hv509 : v509 = .field (((nMin - (minorOff + pos) : Nat) : F)) :=
          evalBinOp_sub_nat_wrap hmo_le op531
        rw [hv509] at ev507
        have hbd505 : Bounded cs505 :=
          RomBound.bounded_mono hbd (fun cl hcl' => hsub cl (by rw [hc]; call_mem))
        have hlift_tm : TmOExact (Core.keyOf t) m495
            (mdom.liftLooseBVars (nMin - (minorOff + pos)) 0) v494 :=
          expr_lift_tmOExact (by omega) (by omega) hbd505 hmdom_tm ev507
        have e_495 : Heap.Extends m378 m495 := ev507.heap_extends
        obtain ⟨sb, hlams2, hsb_tm⟩ :=
          rule_lam_doms_spec ru.fields.toNat (by omega)
            (hafterPre_tm.mono e_495) hlift_tm
            (helim.mono (e_150.trans (e_378.trans e_495))) ev553
        have e_541 : Heap.Extends m495 m541 := ev553.heap_extends
        have hsb_cb : sb = cb :=
          kexpr_struct_eq_oexact hsb_tm (hcb_tm.mono (e_378.trans (e_495.trans e_541))) ev610
        have e_600 : Heap.Extends h m600 :=
          e_150.trans (e_378.trans (e_495.trans (e_541.trans ev610.heap_extends)))
        have hv648 : v648 = .field (((pos + 1 : Nat) : F)) := Decl.evalBinOp_add_one pos op721
        rw [hv648] at ev639
        have hrest_res := ih cbs_rest (pos + 1)
          (by simp at hlen; omega) (by simp at hmin ⊢; omega)
          (fun cl hcl' => hsub cl (by rw [hc]; call_mem))
          (htail.mono e_600)
          (tmOExactList_mono (e_378.trans (e_495.trans (e_541.trans ev610.heap_extends))) hcbs_rest)
          (hty.mono e_600) (helim.mono e_600) ev639
        intro i ru' hi
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst hi
          refine ⟨rhs, cb, by simpa using hloaded, rfl, afterPre, mdom, mrest, sb, bmeta ml,
            hlams1, hpeel_eq, hlams2, hsb_cb ▸ Core.exprLvEq_refl cb⟩
        | succ i =>
          simp only [List.getElem?_cons_succ] at hi
          obtain ⟨rhs', cb', hld', hcb', hrf'⟩ := hrest_res i ru' hi
          have hidx_eq : pos + 1 + i = pos + (i + 1) := by omega
          rw [hidx_eq] at hld' hrf'
          exact ⟨rhs', cb', hld', hcb', hrf'⟩

/-! ## `KernelCheck::flat_find_pos` and `KernelCheck::flat_find_pos_kind` -/

/-- **`KernelCheck::flat_find_pos` on a `FlatEntryRepExact` list**: returns `(1, pos + i)` at the
first matching entry with `e.addr = ixAddr target`, or `(0, 0)` iff no entry matches. -/
theorem flat_find_pos_spec {κ : _root_.Address → KKey} {target : Bytes.Address}
    {xtarget : SourceValue F} :
    ∀ (es : List FlatEntry) (pos : Nat) {xflat r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      RepList flatListEnum (FlatEntryRepExact κ) h es xflat →
      Bytes.RepAddressRef addrTy h target xtarget →
      ObsFn W "KernelCheck::flat_find_pos" [xflat, xtarget, .field (pos : F)] h r h' cs →
      h' = h ∧
      ((∃ i e, es[i]? = some e ∧ e.addr = ixAddr target ∧
          r = .tuple [.field 1, .field (((pos + i : Nat) : F))]) ∨
       ((∀ e ∈ es, e.addr ≠ ixAddr target) ∧ r = .tuple [.field 0, .field 0])) := by
  intro es
  induction es with
  | nil =>
    intro pos xflat r h h' cs hflat _ ev
    match Obs.«KernelCheck::flat_find_pos».obs ev with
    | .Nil (he24 := hr) (he37 := hh) .. =>
      subst hr hh
      exact ⟨rfl, Or.inr ⟨fun _ hm => nomatch hm, rfl⟩⟩
    | .Cons_n1 (ld12 := ld12) .. | .Cons_other (ld12 := ld12) .. =>
      obtain ⟨_, _, hne, _, _⟩ := Core.RepList.cons_of_load hflat ld12
      cases hne
  | cons e rest ih =>
    intro pos xflat r h h' cs hflat rtarget ev
    match Obs.«KernelCheck::flat_find_pos».obs ev with
    | .Nil (ld12 := ld12) .. =>
      cases Core.RepList.nil_of_load hflat ld12
    | .Cons_n1 (x_rest := xrest) (x_member_addr := xma) (m93 := m93)
        (ld12 := ld12) (ev106 := ev106) (he131 := hr) (he145 := hh) .. =>
      subst hr hh
      obtain ⟨e', rest', heq, he_rep, hrest_rep⟩ := Core.RepList.cons_of_load hflat ld12
      injection heq with h1 h2; subst h1 h2
      obtain ⟨xa, xps, xls, a, htup, ra, ha_eq, -, -⟩ := he_rep
      injection htup with hts; injection hts with hxma _
      subst hxma
      obtain ⟨hva, hm93⟩ := Lib.address_eq_spec ev106 ra rtarget
      subst hm93
      have ha_t : a = target := by
        by_contra hne
        rw [if_neg hne] at hva
        exact absurd (Value.field.inj hva) one_ne_zero
      subst ha_t
      exact ⟨rfl, Or.inl ⟨0, e, rfl, ha_eq.symm, by simp⟩⟩
    | .Cons_other (x_rest := xrest) (x_member_addr := xma) (v92 := v92) (m93 := m93)
        (v159 := v159) (ld12 := ld12) (ev106 := ev106) (hne147 := hne147)
        (op187 := op187) (ev156 := ev156) .. =>
      obtain ⟨e', rest', heq, he_rep, hrest_rep⟩ := Core.RepList.cons_of_load hflat ld12
      injection heq with h1 h2; subst h1 h2
      obtain ⟨xa, xps, xls, a, htup, ra, ha_eq, -, -⟩ := he_rep
      injection htup with hts; injection hts with hxma _
      subst hxma
      obtain ⟨hva, hm93⟩ := Lib.address_eq_spec ev106 ra rtarget
      subst hm93
      have ha_ne : a ≠ target := by
        intro heq_a
        rw [if_pos heq_a] at hva
        exact hne147 hva.symm
      have he_ne : e.addr ≠ ixAddr target := by
        intro heq_e
        rw [← ha_eq] at heq_e
        exact ha_ne (Core.ixAddr_inj heq_e)
      have hv159 : v159 = .field (((pos + 1 : Nat) : F)) := Decl.evalBinOp_add_one pos op187
      rw [hv159] at ev156
      obtain ⟨hh', hres⟩ := ih (pos + 1) hrest_rep rtarget ev156
      refine ⟨hh', ?_⟩
      rcases hres with ⟨i, e₁, hi, ha₁, hr₁⟩ | ⟨hall, hr₀⟩
      · refine Or.inl ⟨i + 1, e₁, hi, ha₁, ?_⟩
        rwa [show pos + 1 + i = pos + (i + 1) by omega] at hr₁
      · refine Or.inr ⟨fun x hx => ?_, hr₀⟩
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact he_ne
        · exact hall x hx'

/-- **`KernelCheck::flat_find_pos_kind` on a `FlatEntryRepExact` list**: returns `(1, pos + i)`
at the first matching entry (matching `addr`, `aux`, and when `wantAux = true` also exact
`params` and `levels`), or `(0, 0)` iff no entry matches. -/
theorem flat_find_pos_kind_spec {κ : _root_.Address → KKey} (hinj : Function.Injective κ)
    {target : Bytes.Address} {wantAux : Bool} {wantSp : List KExpr} {wantUs : List KLevel}
    {xtarget xwsp xwus : SourceValue F} :
    ∀ (es : List FlatEntry) (pos : Nat) {xflat r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      Bounded cs →
      RepList flatListEnum (FlatEntryRepExact κ) h es xflat →
      Bytes.RepAddressRef addrTy h target xtarget →
      RepList kexprListEnum (TmOExact κ) h wantSp xwsp →
      RepKLevelList h wantUs xwus →
      ObsFn W "KernelCheck::flat_find_pos_kind"
        [xflat, xtarget, auxVal wantAux, xwsp, xwus, .field (pos : F)] h r h' cs →
      (∃ i e, es[i]? = some e ∧ e.addr = ixAddr target ∧ e.aux = wantAux ∧
          (wantAux = true → e.params = wantSp ∧ e.levels = wantUs) ∧
          r = .tuple [.field 1, .field (((pos + i : Nat) : F))]) ∨
      ((∀ e ∈ es, ¬ (e.addr = ixAddr target ∧ e.aux = wantAux ∧
          (wantAux = true → e.params = wantSp ∧ e.levels = wantUs))) ∧
        r = .tuple [.field 0, .field 0]) := by
  have eval_match :
      ∀ {e : FlatEntry} {xma xis xsp xou xm xrest xfl v92 v155 v208 : SourceValue F}
        {h0 m93 m156 m209 : Heap F} {cs103 cs158 cs211 : List (Call F)} {a : Bytes.Address},
        Bounded cs211 →
        Bytes.RepAddressRef addrTy h0 a xma → ixAddr a = e.addr →
        xis = auxVal e.aux →
        RepList kexprListEnum (TmOExact κ) h0 e.params xsp →
        RepKLevelList h0 e.levels xou →
        Bytes.RepAddressRef addrTy h0 target xtarget →
        RepList kexprListEnum (TmOExact κ) h0 wantSp xwsp →
        RepKLevelList h0 wantUs xwus →
        ObsFn W "Bytes::address_eq" [xma, xtarget] h0 v92 m93 cs103 →
        Obs.«KernelCheck::flat_find_pos_kind».Seg1 v92 xma xis xsp xou xm xrest xfl xtarget
          (auxVal wantAux) xwsp xwus (.field (pos : F)) m93 v155 m156 cs158 →
        Obs.«KernelCheck::flat_find_pos_kind».Seg2 v155 v92 xma xis xsp xou xm xrest xfl xtarget
          (auxVal wantAux) xwsp xwus (.field (pos : F)) m156 v208 m209 cs211 →
        ∃ (b1 b2 b3 : Bool),
          v92 = .field (if b1 then 1 else 0) ∧
          v155 = .field (if b2 then 1 else 0) ∧
          v208 = .field (if b3 then 1 else 0) ∧
          (b1 = true ↔ e.addr = ixAddr target) ∧
          (b2 = true ↔ e.aux = wantAux) ∧
          (b3 = true ↔ (wantAux = true → e.params = wantSp ∧ e.levels = wantUs)) ∧
          Heap.Extends h0 m209 := by
    intro e xma xis xsp xou xm xrest xfl v92 v155 v208 h0 m93 m156 m209 cs103 cs158 cs211 a
      hbd211 ra ha hxis hsp hou rtarget hwsp hwus ev105 sg1 sg2
    obtain ⟨hv92, hm93⟩ := Lib.address_eq_spec ev105 ra rtarget
    subst hm93
    have hb1 : (decide (a = target) = true) ↔ e.addr = ixAddr target := by
      simp only [decide_eq_true_eq]
      exact ⟨fun h => by rw [← ha, h], fun h => Core.ixAddr_inj (ha.trans h)⟩
    have hv92' : v92 = .field (if decide (a = target) then 1 else 0) := by
      rw [hv92]; by_cases h : a = target <;> simp [h]
    have hsg1 : ∃ b2 : Bool, v155 = .field (if b2 then 1 else 0) ∧
        (b2 = true ↔ e.aux = wantAux) ∧ m156 = h0 := by
      cases sg1 with
      | n0 op138 he145 he146 _ =>
        subst he145 he146 hxis
        refine ⟨true, rfl, ?_, rfl⟩
        simp only [true_iff]
        simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
          Except.ok.injEq, Value.field.injEq] at op138
        have hfeq := sub_eq_zero.mp op138
        cases e.aux <;> cases wantAux <;> simp [auxVal] at hfeq ⊢
      | other v122 op138 hne148 he152 he153 _ =>
        subst he152 he153 hxis
        refine ⟨false, rfl, ?_, rfl⟩
        simp only [Bool.false_eq_true, false_iff]
        intro heq_aux
        rw [heq_aux] at op138
        cases wantAux <;> simp [auxVal, evalBinOp, bind, Except.bind, pure, Except.pure] at op138 <;>
          exact hne148 (by rw [← op138]; simp)
    obtain ⟨b2, hv155', hb2, hm156⟩ := hsg1
    subst hm156
    have hsg2 : ∃ b3 : Bool, v208 = .field (if b3 then 1 else 0) ∧
        (b3 = true ↔ (wantAux = true → e.params = wantSp ∧ e.levels = wantUs)) ∧
        Heap.Extends h0 m209 := by
      cases sg2 with
      | n1 x_p y_l m_j cs_p cs_l hv177 ev_sp ev_us op_mul hc_s2 =>
        have hwa : wantAux = true := by
          cases wantAux <;> simp [auxVal] at hv177 ⊢
        have hbd_p : Bounded cs_p :=
          RomBound.bounded_mono hbd211 (fun cl hcl' => by rw [hc_s2]; call_mem)
        have hxp := spec_params_zeta_eq_exact hinj hsp hwsp hbd_p ev_sp
        have ext_p := ev_sp.heap_extends
        obtain ⟨hyl, hm209⟩ := level_list_struct_eq_exact (hou.mono ext_p) (hwus.mono ext_p) ev_us
        subst hm209
        rw [hxp, hyl] at op_mul
        simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
          Except.ok.injEq] at op_mul
        by_cases hp : e.params = wantSp <;> by_cases hl : e.levels = wantUs
        · refine ⟨true, ?_, by simp [hwa, hp, hl], ext_p⟩
          rw [← op_mul]; simp [hp, hl]
        · refine ⟨false, ?_, by simp [hwa, hp, hl], ext_p⟩
          rw [← op_mul]; simp [hp, hl]
        · refine ⟨false, ?_, by simp [hwa, hp, hl], ext_p⟩
          rw [← op_mul]; simp [hp, hl]
        · refine ⟨false, ?_, by simp [hwa, hp, hl], ext_p⟩
          rw [← op_mul]; simp [hp, hl]
      | other hne201 he205 he206 _ =>
        subst he205 he206
        have hwa : wantAux = false := by
          cases wantAux
          · rfl
          · exact absurd rfl hne201
        exact ⟨true, rfl, by simp [hwa], Heap.Extends.refl _⟩
    obtain ⟨b3, hv208', hb3, ext_m209⟩ := hsg2
    exact ⟨decide (a = target), b2, b3, hv92', hv155', hv208', hb1, hb2, hb3, ext_m209⟩
  intro es
  induction es with
  | nil =>
    intro pos xflat r h h' cs _ hflat _ _ _ ev
    match Obs.«KernelCheck::flat_find_pos_kind».obs ev with
    | .Nil (he24 := hr) .. =>
      subst hr
      exact Or.inr ⟨fun _ hm => nomatch hm, rfl⟩
    | .Cons_n1 (ld12 := ld12) .. | .Cons_other (ld12 := ld12) .. =>
      obtain ⟨_, _, hne, _, _⟩ := Core.RepList.cons_of_load hflat ld12
      cases hne
  | cons e rest ih =>
    intro pos xflat r h h' cs hbd hflat rtarget hwsp hwus ev
    match Obs.«KernelCheck::flat_find_pos_kind».obs ev with
    | .Nil (ld12 := ld12) .. =>
      cases Core.RepList.nil_of_load hflat ld12
    | .Cons_n1 (x_rest := xrest) (x_member_addr := xma) (x_is_aux := xis) (x_sp := xsp)
        (x_ou := xou) (v92 := v92) (m93 := m93) (cs103 := cs103) (v155 := v155) (m156 := m156)
        (cs158 := cs158) (v208 := v208) (m209 := m209) (cs211 := cs211) (x226 := x226)
        (ld12 := ld12) (ev105 := ev105) (sg163 := sg1) (sg216 := sg2) (op241 := op241)
        (op233 := op233) (he253 := hr) (hc268 := hc) .. =>
      subst hr
      obtain ⟨e', rest', heq, he_rep, hrest_rep⟩ := Core.RepList.cons_of_load hflat ld12
      injection heq with h1 h2; subst h1 h2
      obtain ⟨xa, xps, xls, a, htup, ra, ha_eq, hsp, hou⟩ := he_rep
      injection htup with hts
      injection hts with h1 hts; injection hts with h2 hts
      injection hts with h3 hts; injection hts with h4 _
      subst h1 h2 h3 h4
      have hbd211 : Bounded cs211 :=
        RomBound.bounded_mono hbd (fun cl hcl' => by rw [hc]; call_mem)
      obtain ⟨b1, b2, b3, hv92, hv155, hv208, hb1, hb2, hb3, -⟩ :=
        eval_match hbd211 ra ha_eq rfl hsp hou rtarget hwsp hwus ev105 sg1 sg2
      rw [hv92, hv155] at op241
      simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
        Except.ok.injEq] at op241
      rw [← op241, hv208] at op233
      simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
        Except.ok.injEq, Value.field.injEq] at op233
      have hall_true : b1 = true ∧ b2 = true ∧ b3 = true := by
        cases b1 <;> cases b2 <;> cases b3 <;> simp at op233 ⊢
      exact Or.inl ⟨0, e, rfl, hb1.mp hall_true.1, hb2.mp hall_true.2.1, hb3.mp hall_true.2.2,
        by simp⟩
    | .Cons_other (x_rest := xrest) (x_member_addr := xma) (x_is_aux := xis) (x_sp := xsp)
        (x_ou := xou) (v92 := v92) (m93 := m93) (cs103 := cs103) (v155 := v155) (m156 := m156)
        (cs158 := cs158) (v208 := v208) (m209 := m209) (cs211 := cs211) (v217 := v217)
        (x226 := x226) (cs276 := cs276) (v_elqqwgaw := vnext)
        (ld12 := ld12) (ev105 := ev105) (sg163 := sg1) (sg216 := sg2) (op241 := op241)
        (op233 := op233) (hne269 := hne269) (op_epyjxidj := op_inc) (ev278 := ev278)
        (hc327 := hc) .. =>
      obtain ⟨e', rest', heq, he_rep, hrest_rep⟩ := Core.RepList.cons_of_load hflat ld12
      injection heq with h1 h2; subst h1 h2
      obtain ⟨xa, xps, xls, a, htup, ra, ha_eq, hsp, hou⟩ := he_rep
      injection htup with hts
      injection hts with h1 hts; injection hts with h2 hts
      injection hts with h3 hts; injection hts with h4 _
      subst h1 h2 h3 h4
      have hbd211 : Bounded cs211 :=
        RomBound.bounded_mono hbd (fun cl hcl' => by rw [hc]; call_mem)
      obtain ⟨b1, b2, b3, hv92, hv155, hv208, hb1, hb2, hb3, ext_209⟩ :=
        eval_match hbd211 ra ha_eq rfl hsp hou rtarget hwsp hwus ev105 sg1 sg2
      rw [hv92, hv155] at op241
      simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
        Except.ok.injEq] at op241
      rw [← op241, hv208] at op233
      simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
        Except.ok.injEq] at op233
      have hnot_all : ¬ (b1 = true ∧ b2 = true ∧ b3 = true) := by
        rintro ⟨rfl, rfl, rfl⟩
        simp at op233
        exact hne269 op233.symm
      have he_not : ¬ (e.addr = ixAddr target ∧ e.aux = wantAux ∧
          (wantAux = true → e.params = wantSp ∧ e.levels = wantUs)) := by
        rintro ⟨h1, h2, h3⟩
        exact hnot_all ⟨hb1.mpr h1, hb2.mpr h2, hb3.mpr h3⟩
      have hvnext : vnext = .field (((pos + 1 : Nat) : F)) := Decl.evalBinOp_add_one pos op_inc
      rw [hvnext] at ev278
      have hbd276 : Bounded cs276 :=
        RomBound.bounded_mono hbd (fun cl hcl' => by rw [hc]; call_mem)
      have hrest_res := ih (pos + 1) hbd276
        (repList_heapMono₂ flatListEnum flatEntryRepExact_heapMono₂ ext_209 hrest_rep)
        (Bytes.repAddressRef_heapMono₂ addrTy ext_209 rtarget)
        (tmOExactList_mono ext_209 hwsp) (hwus.mono ext_209) ev278
      rcases hrest_res with ⟨i, e₁, hi, ha₁, haux₁, hsp₁, hr₁⟩ | ⟨hall, hr₀⟩
      · refine Or.inl ⟨i + 1, e₁, hi, ha₁, haux₁, hsp₁, ?_⟩
        rwa [show pos + 1 + i = pos + (i + 1) by omega] at hr₁
      · refine Or.inr ⟨fun x hx => ?_, hr₀⟩
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact he_not
        · exact hall x hx'

/-! ## `L1.RawConvExpr` + `TmOExact` → `FamilyOf.majorHeadAt` and `FamilyOf.motiveCarrierAt` -/

private theorem unshare_nonshare_wrap (c : Ixon.Constant) :
    ∀ (n : Nat) {e : Ixon.Expr}, (∀ i, e ≠ .share i) → FamilyOf.unshare c n e = e
  | 0, _, _ => rfl
  | _ + 1, .share i, h => absurd rfl (h i)
  | _ + 1, .var _, _ | _ + 1, .sort _, _ | _ + 1, .ref _ _, _ | _ + 1, .recur _ _, _
  | _ + 1, .str _, _ | _ + 1, .nat _, _ | _ + 1, .prj _ _ _, _ | _ + 1, .app _ _, _
  | _ + 1, .lam _ _, _ | _ + 1, .all _ _, _ | _ + 1, .letE _ _ _ _ _, _ => rfl

private theorem unshare_ge_wrap (c : Ixon.Constant) {recurAddrs : List _root_.Address}
    {blobs : List (_root_.Address × ByteArray)} {h : Heap F} {bound : Nat} {e : Ixon.Expr}
    {kp : SourceValue F}
    (raw : L1.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h bound e kp) :
    ∀ n, min bound c.sharing.size + 1 ≤ n →
      ∃ b', L1.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h b'
          (FamilyOf.unshare c n e) kp ∧
        ∀ i, FamilyOf.unshare c n e ≠ .share i := by
  induction raw with
  | @share bound idx s kp hlt hs _ ih =>
    intro n hn
    cases n with
    | zero => omega
    | succ m =>
      have hidx_sz : idx.toNat < c.sharing.size := by
        simpa [Array.getElem?_eq_some_iff] using (List.getElem?_eq_some_iff.mp hs).1
      have hidx_arr : c.sharing[idx.toNat]? = some s := by
        simpa [Array.getElem?_toList] using hs
      simp only [FamilyOf.unshare, hidx_arr]
      exact ih m (by omega)
  | var _ _ | sort _ _ _ _ | ref _ _ _ _ _ _ _ | recur _ _ _ _ _ _ _ | prj _ _ _ _ _ _ _
  | str _ _ _ _ _ _ | nat _ _ _ _ _ _ _ _ | app _ _ _ | lam _ _ _ _ | all _ _ _ _
  | letE _ _ _ _ =>
    rename_i bound _
    intro n _
    have hns : ∀ i, _ ≠ Ixon.Expr.share i := by intro i he; cases he
    rw [unshare_nonshare_wrap c n hns]
    exact ⟨bound, by assumption, hns⟩

private theorem rawConvExpr_node_wrap {c : Ixon.Constant} {recurAddrs : List _root_.Address}
    {blobs : List (_root_.Address × ByteArray)} {h : Heap F} {bound : Nat} {e : Ixon.Expr}
    {kp : SourceValue F}
    (raw : L1.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h bound e kp) :
    ∃ b', L1.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h b'
        (FamilyOf.node c e) kp ∧
      ∀ i, FamilyOf.node c e ≠ .share i :=
  unshare_ge_wrap c raw (c.sharing.size + 1) (by omega)

private theorem rawConvExpr_forall_inv_wrap {c : Ixon.Constant} {recurAddrs : List _root_.Address}
    {blobs : List (_root_.Address × ByteArray)} {h : Heap F} {bound : Nat} {e : Ixon.Expr}
    {kp dp bp lp : SourceValue F}
    (raw : L1.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h bound e kp)
    (ld : loadValue h kp = .ok (.construct kexprEnum "Forall" [dp, bp, lp])) :
    ∃ b' ed eb, FamilyOf.node c e = .all ed eb ∧
      L1.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h b' ed dp ∧
      L1.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h b' eb bp := by
  obtain ⟨b', raw', hns⟩ := rawConvExpr_node_wrap raw
  generalize he' : FamilyOf.node c e = e' at raw' hns
  cases raw' with
  | all _ rt rb cell =>
    have hxs := (Core.load_cell cell ld).2
    simp only [List.cons.injEq, and_true] at hxs
    obtain ⟨rfl, rfl, rfl⟩ := hxs
    exact ⟨b', _, _, rfl, rt, rb⟩
  | share _ _ _ => exact (hns _ rfl).elim
  | var _ cell | sort _ _ _ cell | ref _ _ _ _ _ _ cell | recur _ _ _ _ _ _ cell
  | prj _ _ _ _ _ _ cell | str _ _ _ _ _ cell | nat _ _ _ _ _ _ _ cell
  | app _ _ cell | lam _ _ _ cell | letE _ _ _ cell =>
    exact False.elim (Core.load_cell_ne cell ld (by decide))

private theorem rawConvExpr_not_forall_of_nonForall {c : Ixon.Constant}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {h : Heap F} {bound : Nat} {e : Ixon.Expr} {kp : SourceValue F} {v : SourceValue F}
    (raw : L1.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h bound e kp)
    (ld : loadValue h kp = .ok v)
    (hne : ∀ dp bp lp, v ≠ .construct kexprEnum "Forall" [dp, bp, lp]) :
    ∀ ed eb, FamilyOf.node c e ≠ .all ed eb := by
  obtain ⟨b', raw', hns⟩ := rawConvExpr_node_wrap raw
  generalize he' : FamilyOf.node c e = e' at raw' hns
  cases raw' with
  | all _ _ _ cell =>
    have hv := Except.ok.inj ((Core.load_enum_cell cell).symm.trans ld)
    exact False.elim (hne _ _ _ hv.symm)
  | share _ _ _ => exact (hns _ rfl).elim
  | var _ _ | sort _ _ _ _ | ref _ _ _ _ _ _ _ | recur _ _ _ _ _ _ _ | prj _ _ _ _ _ _ _
  | str _ _ _ _ _ _ | nat _ _ _ _ _ _ _ _ | app _ _ _ | lam _ _ _ _ | letE _ _ _ _ =>
    intro _ _ hbad; cases hbad

private theorem rawConvExpr_app_inv_wrap {c : Ixon.Constant} {recurAddrs : List _root_.Address}
    {blobs : List (_root_.Address × ByteArray)} {h : Heap F} {bound : Nat} {e : Ixon.Expr}
    {kp fp ap : SourceValue F}
    (raw : L1.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h bound e kp)
    (ld : loadValue h kp = .ok (.construct kexprEnum "App" [fp, ap])) :
    ∃ b' ef ea, FamilyOf.node c e = .app ef ea ∧
      L1.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h b' ef fp ∧
      L1.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h b' ea ap := by
  obtain ⟨b', raw', hns⟩ := rawConvExpr_node_wrap raw
  generalize he' : FamilyOf.node c e = e' at raw' hns
  cases raw' with
  | app rf ra cell =>
    have hxs := (Core.load_cell cell ld).2
    simp only [List.cons.injEq, and_true] at hxs
    obtain ⟨rfl, rfl⟩ := hxs
    exact ⟨b', _, _, rfl, rf, ra⟩
  | share _ _ _ => exact (hns _ rfl).elim
  | var _ cell | sort _ _ _ cell | ref _ _ _ _ _ _ cell | recur _ _ _ _ _ _ cell
  | prj _ _ _ _ _ _ cell | str _ _ _ _ _ cell | nat _ _ _ _ _ _ _ cell
  | lam _ _ _ cell | all _ _ _ cell | letE _ _ _ cell =>
    exact False.elim (Core.load_cell_ne cell ld (by decide))

private theorem rawConvExpr_const_inv_any_wrap {c : Ixon.Constant}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {h : Heap F} {bound : Nat} {e : Ixon.Expr} {kp xa xus : SourceValue F}
    (raw : L1.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h bound e kp)
    (ld : loadValue h kp = .ok (.construct kexprEnum "Const" [xa, xus])) :
    (∃ rIdx uIdxs a d, FamilyOf.node c e = .ref rIdx uIdxs ∧
      c.refs[rIdx.toNat]? = some a ∧ ixAddr d = a ∧ Bytes.RepAddressRef addrTy h d xa) ∨
    (∃ recIdx uIdxs a d, FamilyOf.node c e = .recur recIdx uIdxs ∧
      recurAddrs[recIdx.toNat]? = some a ∧ ixAddr d = a ∧ Bytes.RepAddressRef addrTy h d xa) := by
  obtain ⟨b', raw', hns⟩ := rawConvExpr_node_wrap raw
  generalize he' : FamilyOf.node c e = e' at raw' hns
  cases raw' with
  | ref _ href hd ra _ _ cell =>
    have hxs := (Core.load_cell cell ld).2
    simp only [List.cons.injEq, and_true] at hxs
    obtain ⟨rfl, rfl⟩ := hxs
    exact Or.inl ⟨_, _, _, _, rfl, by simpa only [Array.getElem?_toList] using href, hd, ra⟩
  | recur _ hrec hd ra _ _ cell =>
    have hxs := (Core.load_cell cell ld).2
    simp only [List.cons.injEq, and_true] at hxs
    obtain ⟨rfl, rfl⟩ := hxs
    exact Or.inr ⟨_, _, _, _, rfl, hrec, hd, ra⟩
  | share _ _ _ => exact (hns _ rfl).elim
  | var _ cell | sort _ _ _ cell | prj _ _ _ _ _ _ cell | str _ _ _ _ _ cell
  | nat _ _ _ _ _ _ _ cell | app _ _ cell | lam _ _ _ cell | all _ _ _ cell | letE _ _ _ cell =>
    exact False.elim (Core.load_cell_ne cell ld (by decide))

/-- Literal chain of `n` heap `"Forall"` cells from `p` to `q`. -/
inductive HeapForalls (h : Heap F) : Nat → SourceValue F → SourceValue F → Prop
  | zero (p : SourceValue F) : HeapForalls h 0 p p
  | succ {n : Nat} {p dp bp lp q : SourceValue F} :
      loadValue h p = .ok (.construct kexprEnum "Forall" [dp, bp, lp]) →
      HeapForalls h n bp q → HeapForalls h (n + 1) p q

theorem HeapForalls.mono {h h' : Heap F} {n : Nat} {p q : SourceValue F}
    (ext : Heap.Extends h h') (hf : HeapForalls h n p q) : HeapForalls h' n p q := by
  induction hf with
  | zero p => exact .zero p
  | succ ld _ ih => exact .succ (loadValue_mono ext ld) ih

theorem HeapForalls.trans {h : Heap F} {m n : Nat} {p q r : SourceValue F}
    (h1 : HeapForalls h m p q) (h2 : HeapForalls h n q r) : HeapForalls h (m + n) p r := by
  induction h1 with
  | zero => simpa using h2
  | succ ld _ ih =>
    rw [Nat.succ_add]
    exact .succ ld (ih h2)

/-- Literal chain of heap `"App"` cells down to a `"Const"` head at address `a`. -/
inductive HeapAppConst (h : Heap F) : SourceValue F → _root_.Address → Prop
  | const {p xa xus : SourceValue F} {da : Bytes.Address} :
      loadValue h p = .ok (.construct kexprEnum "Const" [xa, xus]) →
      Bytes.RepAddressRef addrTy h da xa →
      HeapAppConst h p (ixAddr da)
  | app {p fp ap : SourceValue F} {a : _root_.Address} :
      loadValue h p = .ok (.construct kexprEnum "App" [fp, ap]) →
      HeapAppConst h fp a →
      HeapAppConst h p a

theorem HeapAppConst.mono {h h' : Heap F} {p : SourceValue F} {a : _root_.Address}
    (ext : Heap.Extends h h') (hc : HeapAppConst h p a) : HeapAppConst h' p a := by
  induction hc with
  | const ld ra => exact .const (loadValue_mono ext ld) (Bytes.repAddressRef_heapMono₂ addrTy ext ra)
  | app ld _ ih => exact .app (loadValue_mono ext ld) ih

/-- Literal chain of ≥ 1 heap `"Forall"` cells ending in a non-`"Forall"` cell, whose last
`"Forall"` domain satisfies `HeapAppConst h _ a`. -/
inductive HeapMotiveCarrier (h : Heap F) : SourceValue F → _root_.Address → Prop
  | last {p dp bp lp v : SourceValue F} {a : _root_.Address} :
      loadValue h p = .ok (.construct kexprEnum "Forall" [dp, bp, lp]) →
      loadValue h bp = .ok v →
      (∀ d b l, v ≠ .construct kexprEnum "Forall" [d, b, l]) →
      HeapAppConst h dp a →
      HeapMotiveCarrier h p a
  | step {p dp bp lp dp' bp' lp' : SourceValue F} {a : _root_.Address} :
      loadValue h p = .ok (.construct kexprEnum "Forall" [dp, bp, lp]) →
      loadValue h bp = .ok (.construct kexprEnum "Forall" [dp', bp', lp']) →
      HeapMotiveCarrier h bp a →
      HeapMotiveCarrier h p a

theorem HeapMotiveCarrier.mono {h h' : Heap F} {p : SourceValue F} {a : _root_.Address}
    (ext : Heap.Extends h h') (hm : HeapMotiveCarrier h p a) : HeapMotiveCarrier h' p a := by
  induction hm with
  | last ld ldb hne hac =>
    exact .last (loadValue_mono ext ld) (loadValue_mono ext ldb) hne (hac.mono ext)
  | step ld ldb _ ih =>
    exact .step (loadValue_mono ext ld) (loadValue_mono ext ldb) ih

/-- Uniform heap-level equality/wrap relation satisfied by `canonical_rules_at_pos`
(`kexpr_struct_eq = 1` or `wrap_rel = 1`). -/
def HeapEqOrWrap (rootCalls : List (Call F)) (h : Heap F) (xg xd : SourceValue F) : Prop :=
  (∃ h' cs, (∀ cl ∈ cs, cl ∈ rootCalls) ∧
      ObsFn W "KernelCheck::kexpr_struct_eq" [xg, xd] h (.field 1) h' cs) ∨
  (∃ xsm h' cs, (∀ cl ∈ cs, cl ∈ rootCalls) ∧
      ObsFn W "KernelCheck::wrap_rel" [xsm, xg, xd] h (.field 1) h' cs)

/-- Uniform domain relation (`HeapEqOrWrap` or `wrap_dom = 1`). -/
def HeapDomRel (rootCalls : List (Call F)) (h : Heap F) (xg xd : SourceValue F) : Prop :=
  HeapEqOrWrap rootCalls h xg xd ∨
  (∃ xsm h' cs, (∀ cl ∈ cs, cl ∈ rootCalls) ∧
      ObsFn W "KernelCheck::wrap_dom" [xsm, xg, xd] h (.field 1) h' cs)

theorem collect_spine_heapAppConst :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → fname = "KernelTypes::collect_spine" →
      ∀ (p xh xargs : SourceValue F) (a : _root_.Address),
        args = [p] → r = .tuple [xh, xargs] → HeapAppConst h p a →
        ∃ (xa xus : SourceValue F) (da : Bytes.Address),
          loadValue h' xh = .ok (.construct kexprEnum "Const" [xa, xus]) ∧
          Bytes.RepAddressRef addrTy h' da xa ∧ ixAddr da = a :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' cs => fname = "KernelTypes::collect_spine" →
      ∀ (p xh xargs : SourceValue F) (a : _root_.Address),
        args = [p] → r = .tuple [xh, xargs] → HeapAppConst h p a →
        ∃ (xa xus : SourceValue F) (da : Bytes.Address),
          loadValue h' xh = .ok (.construct kexprEnum "Const" [xa, xus]) ∧
          Bytes.RepAddressRef addrTy h' da xa ∧ ixAddr da = a)
    (fun fname args h r h' cs ev ih hfn p xh xargs a hargs hr hac => by
      subst hfn hargs hr
      match Obs.«KernelTypes::collect_spine».obs ev with
      | .App (x_f := xf) (m31 := m31) (cs41 := cs41) (x_head := xhead) (x_args := xargs')
          (ld12 := ld12) (ev43 := ev43) (he69 := he69) (ev88 := ev88) (he105 := he105)
          (hc106 := hc) .. =>
        injection he69 with hxs; injection hxs with hxh _
        subst hxh he105
        cases hac with
        | const ld _ =>
          have hv := Except.ok.inj (ld.symm.trans ld12)
          simp [kexprEnum] at hv
        | app ld hac_f =>
          have hv := Except.ok.inj (ld.symm.trans ld12)
          simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hv
          obtain ⟨rfl, rfl⟩ := hv
          obtain ⟨xa, xus, da, ldc, ra, ha⟩ :=
            ih _ _ _ _ _ _ (by rw [hc]; simp only [List.length_cons, List.length_append]; omega)
              ev43 rfl _ _ _ _ rfl rfl hac_f
          have ext := ev88.heap_extends
          exact ⟨xa, xus, da, loadValue_mono ext ldc,
            Bytes.repAddressRef_heapMono₂ addrTy ext ra, ha⟩
      | .other (ld12 := ld12) (hne140 := hne140) (he122 := he122) (he139 := he139) .. =>
        injection he122 with hxs; injection hxs with hxh _
        subst hxh he139
        cases hac with
        | app ld _ =>
          have hv := Except.ok.inj (ld.symm.trans ld12)
          exact False.elim (hne140 [_, _] rfl hv.symm)
        | const ld ra =>
          have ext := Heap.Extends.snoc h (.construct kexprListEnum "Nil" [])
          exact ⟨_, _, _, loadValue_mono ext ld,
            Bytes.repAddressRef_heapMono₂ addrTy ext ra, rfl⟩)

/-- `KernelCheck::consume_wrapper` cannot succeed on a `HeapAppConst` headed by an inductive
projection (`c.info = .iPrj _`) in `E₀`. -/
theorem consume_wrapper_not_one_of_iprj {rootCalls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    {a : _root_.Address} {c : Ixon.Constant} {p : Ixon.InductProj}
    (hcE : recordOf E₀ a = some c) (hi : c.info = .iPrj p)
    {xg xa : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hsub : ∀ cl ∈ cs, cl ∈ rootCalls)
    (hac : HeapAppConst h xg a)
    (ev : ObsFn W "KernelCheck::consume_wrapper" [xg] h (.tuple [.field 1, xa]) h' cs) : False := by
  match Obs.«KernelCheck::consume_wrapper».obs ev with
  | .Const_Cons_Defn_n1_bind_other (he276 := he) ..
  | .Const_Cons_Defn_other (he299 := he) ..
  | .Const_Cons_other (he323 := he) ..
  | .Const_other (he347 := he) ..
  | .other (he371 := he) .. =>
    injection he with hxs; injection hxs with h01 _
    exact absurd (Value.field.inj h01) one_ne_zero
  | .Const_Cons_Defn_n1_bind_n0 (x_w := xw) (ev14 := ev14) (ld47 := ld47) (ev112 := ev112)
      (ld106 := ld106) (hc267 := hc) .. =>
    obtain ⟨xa', xus', da, ldc, ra, ha_eq⟩ :=
      collect_spine_heapAppConst _ _ _ _ _ _ ev14 rfl _ _ _ _ rfl rfl hac
    have hv := Except.ok.inj (ldc.symm.trans ld47)
    simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hv
    obtain ⟨rfl, rfl⟩ := hv
    have sub_ci : ∀ cl ∈ _, cl ∈ rootCalls := fun cl hcl' => hsub cl (by rw [hc]; call_mem)
    have hbd_ci : Bounded _ := RomBound.bounded_mono hbd sub_ci
    obtain ⟨-, rawBytes, c', blobs', hh', ha', hex', -, -, -, hrawRes⟩ :=
      L1.get_ci_spec hbd_ci ra ev112
    have hc_eq : c' = c :=
      record_eq_of_hashed hS sub_ci (ha_eq.symm ▸ hcE) hh' ha' hex'
    subst hc_eq
    simp only [L1.GetCIRawResult, hi] at hrawRes
    obtain ⟨_, _, _, _, _, v, -, -, -, -, -, -, hld, -, -, -, -, -, _, _, _, -, -, rfl, -⟩ :=
      hrawRes
    rw [hld] at ld106
    injection ld106 with hbad
    simp [kciEnum] at hbad

/-- `KernelCheck::consume_wrapper` cannot succeed on a pointer that loads as `"Forall"`. -/
theorem consume_wrapper_not_one_of_forall {xg dp bp lp xa : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ld : loadValue h xg = .ok (.construct kexprEnum "Forall" [dp, bp, lp]))
    (ev : ObsFn W "KernelCheck::consume_wrapper" [xg] h (.tuple [.field 1, xa]) h' cs) : False := by
  match Obs.«KernelCheck::consume_wrapper».obs ev with
  | .Const_Cons_Defn_n1_bind_other (he276 := he) ..
  | .Const_Cons_Defn_other (he299 := he) ..
  | .Const_Cons_other (he323 := he) ..
  | .Const_other (he347 := he) ..
  | .other (he371 := he) .. =>
    injection he with hxs; injection hxs with h01 _
    exact absurd (Value.field.inj h01) one_ne_zero
  | .Const_Cons_Defn_n1_bind_n0 (ev14 := ev14) (ld47 := ld47) .. =>
    match Obs.«KernelTypes::collect_spine».obs ev14 with
    | .App (ld12 := ld12) .. =>
      have hv := Except.ok.inj (ld.symm.trans ld12)
      simp [kexprEnum] at hv
    | .other (he122 := he122) (he139 := he139) .. =>
      injection he122 with hxs; injection hxs with hxh _
      subst hxh he139
      have ld' := loadValue_mono (Heap.Extends.snoc h (.construct kexprListEnum "Nil" [])) ld
      have hv := Except.ok.inj (ld'.symm.trans ld47)
      simp [kexprEnum] at hv

/-- Stepping one `"Forall"` cell through `HeapEqOrWrap` gives a matching `"Forall"` cell on the
right, with `HeapDomRel` on the domains and `HeapEqOrWrap` on the bodies. -/
theorem heapEqOrWrap_forall_step {rootCalls : List (Call F)} {h : Heap F}
    {xg xd dp bp lp : SourceValue F}
    (hrel : HeapEqOrWrap rootCalls h xg xd)
    (ld : loadValue h xg = .ok (.construct kexprEnum "Forall" [dp, bp, lp])) :
    ∃ dp2 bp2 lp2 h_d h_b,
      Heap.Extends h h_d ∧ Heap.Extends h h_b ∧
      loadValue h xd = .ok (.construct kexprEnum "Forall" [dp2, bp2, lp2]) ∧
      HeapDomRel rootCalls h_d dp dp2 ∧
      HeapEqOrWrap rootCalls h_b bp bp2 := by
  rcases hrel with ⟨h', cs, hsub, ev⟩ | ⟨xsm, h', cs, hsub, ev⟩
  · match Obs.«KernelCheck::kexpr_struct_eq».obs ev with
    | .Forall_Forall (x_da := xda) (x_xa := xxa) (x_la := xla)
        (x_db := xdb) (x_xb := xxb) (x_lb := xlb) (cs568 := csb)
        (ld12 := ld12) (ld542 := ld542) (ev570 := evb) (hc619 := hc) .. =>
      have hv := Except.ok.inj (ld.symm.trans ld12)
      simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      match Obs.«KernelCheck::kexpr_binder_struct_eq».obs evb with
      | .n1_other (he98 := he) .. | .other (he105 := he) .. =>
        exact absurd (Value.field.inj he) one_ne_zero
      | .n1_n1 (m2 := m2) (m37 := m37) (ev15 := ev15) (ev50 := ev50) (ev76 := ev76)
          (hc93 := hcb) .. =>
        have e1 := ev15.heap_extends
        have e2 := ev50.heap_extends
        have sub_b : ∀ cl ∈ csb, cl ∈ rootCalls := fun cl hcl' => hsub cl (by rw [hc]; call_mem)
        exact ⟨xdb, xxb, xlb, m2, m37, e1, e1.trans e2, ld542,
          Or.inl (Or.inl ⟨m37, _, fun cl hcl' => sub_b cl (by rw [hcb]; call_mem), ev50⟩),
          Or.inl ⟨h', _, fun cl hcl' => sub_b cl (by rw [hcb]; call_mem), ev76⟩⟩
    | .Forall_other (he624 := he) .. => exact absurd (Value.field.inj he) one_ne_zero
    | .BVar_BVar_n0 (ld12 := ld12) .. | .BVar_BVar_other (ld12 := ld12) ..
    | .BVar_other (ld12 := ld12) .. | .Srt_Srt (ld12 := ld12) ..
    | .Srt_other (ld12 := ld12) .. | .Const_Const_n1 (ld12 := ld12) ..
    | .Const_Const_other (ld12 := ld12) .. | .Const_other (ld12 := ld12) ..
    | .App_App_n1 (ld12 := ld12) .. | .App_App_other (ld12 := ld12) ..
    | .App_other (ld12 := ld12) .. | .Lam_Lam (ld12 := ld12) ..
    | .Lam_other (ld12 := ld12) .. | .Let_Let_n1_n1 (ld12 := ld12) ..
    | .Let_Let_n1_other (ld12 := ld12) .. | .Let_Let_other (ld12 := ld12) ..
    | .Let_other (ld12 := ld12) .. | .Lit_Lit (ld12 := ld12) ..
    | .Lit_other (ld12 := ld12) .. | .Proj_Proj_n1 (ld12 := ld12) ..
    | .Proj_Proj_other (ld12 := ld12) .. | .Proj_other (ld12 := ld12) .. =>
      have hv := Except.ok.inj (ld.symm.trans ld12)
      simp [kexprEnum] at hv
    | .other (ld12 := ld12) (hne627 := hne) .. =>
      have hv := Except.ok.inj (ld.symm.trans ld12)
      exact False.elim (hne [_, _, _] rfl hv.symm)
  · match Obs.«KernelCheck::wrap_rel».obs ev with
    | .other_other_Forall_Forall (x_t := xt) (x_b := xb) (x_m := xm)
        (x_t2 := xt2) (x_b2 := xb2) (x_m2 := xm2) (cs538 := csb)
        (ld242 := ld242) (ld512 := ld512) (ev540 := evb) (hc589 := hc) .. =>
      have hv := Except.ok.inj (ld.symm.trans ld242)
      simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      match Obs.«KernelCheck::wrap_binder».obs evb with
      | .n1_other (he98 := he) .. | .other (he105 := he) .. =>
        exact absurd (Value.field.inj he) one_ne_zero
      | .n1_n1 (m2 := m2) (m37 := m37) (ev15 := ev15) (ev50 := ev50) (ev76 := ev76)
          (hc93 := hcb) .. =>
        have e1 := ev15.heap_extends
        have e2 := ev50.heap_extends
        have sub_b : ∀ cl ∈ csb, cl ∈ rootCalls := fun cl hcl' => hsub cl (by rw [hc]; call_mem)
        exact ⟨xt2, xb2, xm2, m2, m37, e1, e1.trans e2, ld512,
          Or.inr ⟨xsm, m37, _, fun cl hcl' => sub_b cl (by rw [hcb]; call_mem), ev50⟩,
          Or.inr ⟨xsm, h', _, fun cl hcl' => sub_b cl (by rw [hcb]; call_mem), ev76⟩⟩
    | .other_other_Forall_other (he594 := he) ..
    | .other_Let (he224 := he) ..
    | .Let_Let_n1_other (he166 := he) .. | .Let_Let_other (he173 := he) ..
    | .Let_other (he180 := he) .. =>
      exact absurd (Value.field.inj he) one_ne_zero
    | .Let_Let_n1_n1 (ld12 := ld12) .. =>
      have hv := Except.ok.inj (ld.symm.trans ld12)
      simp [kexprEnum] at hv
    | .other_other_App_App_n1 (ld242 := ld242) ..
    | .other_other_App_App_other (ld242 := ld242) ..
    | .other_other_App_other (ld242 := ld242) ..
    | .other_other_Lam_Lam (ld242 := ld242) ..
    | .other_other_Lam_other (ld242 := ld242) ..
    | .other_other_Proj_Proj_n1 (ld242 := ld242) ..
    | .other_other_Proj_Proj_other (ld242 := ld242) ..
    | .other_other_Proj_other (ld242 := ld242) .. =>
      have hv := Except.ok.inj (ld.symm.trans ld242)
      simp [kexprEnum] at hv
    | .other_other_other (ld242 := ld242) (hne597 := hne) .. =>
      have hv := Except.ok.inj (ld.symm.trans ld242)
      exact False.elim (hne [_, _, _] rfl hv.symm)

/-- A non-`"Forall"` pointer related by `HeapEqOrWrap` stays non-`"Forall"` on the right. -/
theorem heapEqOrWrap_not_forall {rootCalls : List (Call F)} {h : Heap F}
    {xg xd v : SourceValue F}
    (hrel : HeapEqOrWrap rootCalls h xg xd)
    (ld : loadValue h xg = .ok v)
    (hne : ∀ d b l, v ≠ .construct kexprEnum "Forall" [d, b, l]) :
    ∃ v2, loadValue h xd = .ok v2 ∧ ∀ d b l, v2 ≠ .construct kexprEnum "Forall" [d, b, l] := by
  rcases hrel with ⟨h', cs, _, ev⟩ | ⟨xsm, h', cs, _, ev⟩
  · match Obs.«KernelCheck::kexpr_struct_eq».obs ev with
    | .BVar_BVar_n0 (ld36 := ld2) .. => exact ⟨_, ld2, by intro _ _ _ he; simp [kexprEnum] at he⟩
    | .Srt_Srt (ld112 := ld2) .. => exact ⟨_, ld2, by intro _ _ _ he; simp [kexprEnum] at he⟩
    | .Const_Const_n1 (ld183 := ld2) .. => exact ⟨_, ld2, by intro _ _ _ he; simp [kexprEnum] at he⟩
    | .App_App_n1 (ld301 := ld2) .. => exact ⟨_, ld2, by intro _ _ _ he; simp [kexprEnum] at he⟩
    | .Lam_Lam (ld424 := ld2) .. => exact ⟨_, ld2, by intro _ _ _ he; simp [kexprEnum] at he⟩
    | .Let_Let_n1_n1 (ld660 := ld2) .. => exact ⟨_, ld2, by intro _ _ _ he; simp [kexprEnum] at he⟩
    | .Lit_Lit (ld820 := ld2) .. => exact ⟨_, ld2, by intro _ _ _ he; simp [kexprEnum] at he⟩
    | .Proj_Proj_n1 (ld896 := ld2) .. => exact ⟨_, ld2, by intro _ _ _ he; simp [kexprEnum] at he⟩
    | .Forall_Forall (ld12 := ld12) .. =>
      have hv := Except.ok.inj (ld.symm.trans ld12)
      exact False.elim (hne _ _ _ hv)
    | .BVar_BVar_other (he79 := he) .. | .BVar_other (he86 := he) ..
    | .Srt_other (he152 := he) .. | .Const_Const_other (he263 := he) ..
    | .Const_other (he270 := he) .. | .App_App_other (he381 := he) ..
    | .App_other (he388 := he) .. | .Lam_other (he506 := he) ..
    | .Forall_other (he624 := he) .. | .Let_Let_n1_other (he782 := he) ..
    | .Let_Let_other (he789 := he) .. | .Let_other (he796 := he) ..
    | .Lit_other (he860 := he) .. | .Proj_Proj_other (he1004 := he) ..
    | .Proj_other (he1011 := he) .. | .other (he1018 := he) .. =>
      exact absurd (Value.field.inj he) one_ne_zero
  · match Obs.«KernelCheck::wrap_rel».obs ev with
    | .Let_Let_n1_n1 (ld46 := ld2) .. => exact ⟨_, ld2, by intro _ _ _ he; simp [kexprEnum] at he⟩
    | .other_other_App_App_n1 (ld271 := ld2) .. =>
      exact ⟨_, ld2, by intro _ _ _ he; simp [kexprEnum] at he⟩
    | .other_other_Lam_Lam (ld394 := ld2) .. =>
      exact ⟨_, ld2, by intro _ _ _ he; simp [kexprEnum] at he⟩
    | .other_other_Proj_Proj_n1 (ld630 := ld2) .. =>
      exact ⟨_, ld2, by intro _ _ _ he; simp [kexprEnum] at he⟩
    | .other_other_Forall_Forall (ld242 := ld242) .. =>
      have hv := Except.ok.inj (ld.symm.trans ld242)
      exact False.elim (hne _ _ _ hv)
    | .other_other_other (ev765 := evk) (hc782 := hc) .. =>
      exact heapEqOrWrap_not_forall (Or.inl ⟨h', _, fun _ _ => by trivial, evk⟩) ld hne
    | .Let_Let_n1_other (he166 := he) .. | .Let_Let_other (he173 := he) ..
    | .Let_other (he180 := he) .. | .other_Let (he224 := he) ..
    | .other_other_App_App_other (he351 := he) .. | .other_other_App_other (he358 := he) ..
    | .other_other_Lam_other (he476 := he) .. | .other_other_Forall_other (he594 := he) ..
    | .other_other_Proj_Proj_other (he746 := he) .. | .other_other_Proj_other (he753 := he) .. =>
      exact absurd (Value.field.inj he) one_ne_zero

/-- Transfer `HeapForalls` + `HeapEqOrWrap` directly into `FamilyOf.peel` on a `RawConvExpr` right
side. -/
theorem heapForalls_rawConvExpr_peel {rootCalls : List (Call F)}
    {c : Ixon.Constant} {recurAddrs : List _root_.Address}
    {blobs : List (_root_.Address × ByteArray)} :
    ∀ {n bound : Nat} {h : Heap F} {e : Ixon.Expr} {xg yg xd : SourceValue F},
      HeapForalls h n xg yg →
      HeapEqOrWrap rootCalls h xg xd →
      L1.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h bound e xd →
      ∃ (yd : SourceValue F) (h_out : Heap F) (b' : Nat) (e' : Ixon.Expr),
        Heap.Extends h h_out ∧
        FamilyOf.peel c n e = some e' ∧
        L1.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h_out b' e' yd ∧
        HeapEqOrWrap rootCalls h_out yg yd := by
  intro n
  induction n with
  | zero =>
    intro bound h e xg yg xd hf hrel raw
    cases hf
    exact ⟨xd, h, bound, e, Heap.Extends.refl h, rfl, raw, hrel⟩
  | succ n ih =>
    intro bound h e xg yg xd hf hrel raw
    cases hf with
    | succ ld hf' =>
      obtain ⟨dp2, bp2, lp2, _, h_b, _, ext_b, ld2, -, hrel_b⟩ := heapEqOrWrap_forall_step hrel ld
      obtain ⟨b', ed, eb, hnd, -, raw_b⟩ := rawConvExpr_forall_inv_wrap raw ld2
      obtain ⟨yd, h_out, b'', e', ext_out, hpeel, raw_y, hrel_y⟩ :=
        ih (hf'.mono ext_b) hrel_b (raw_b.mono ext_b)
      refine ⟨yd, h_out, b'', e', ext_b.trans ext_out, ?_, raw_y, hrel_y⟩
      simp only [FamilyOf.peel, hnd]
      exact hpeel

/-- Transfer `HeapAppConst` + `HeapEqOrWrap` directly into `FamilyOf.refHeadAt` on a `RawConvExpr`
right side (for any target address `a ∉ recurAddrs`). -/
theorem heapAppConst_rawConvExpr_refHeadAt {rootCalls : List (Call F)}
    {c : Ixon.Constant} {recurAddrs : List _root_.Address}
    {blobs : List (_root_.Address × ByteArray)} {a : _root_.Address}
    (hnot_rec : a ∉ recurAddrs) :
    ∀ {bound : Nat} {h : Heap F} {e : Ixon.Expr} {xg xd : SourceValue F},
      HeapAppConst h xg a →
      HeapEqOrWrap rootCalls h xg xd →
      L1.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h bound e xd →
      ∃ fuel, FamilyOf.refHeadAt c fuel e = some a := by
  intro bound h e xg xd hac
  induction hac generalizing bound e xd with
  | @const p xa xus da ld ra =>
    intro hrel raw
    have hkeq : ∀ {h' : Heap F} {cs : List (Call F)},
        ObsFn W "KernelCheck::kexpr_struct_eq" [p, xd] h (.field 1) h' cs →
        ∃ fuel, FamilyOf.refHeadAt c fuel e = some (ixAddr da) := by
      intro h' cs evk
      match Obs.«KernelCheck::kexpr_struct_eq».obs evk with
      | .Const_Const_n1 (x_ca := xca) (x_cb := xcb) (ld12 := ld12) (ld183 := ld183)
          (ev215 := ev215) .. =>
        have hv := Except.ok.inj (ld.symm.trans ld12)
        simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hv
        obtain ⟨rfl, rfl⟩ := hv
        rcases rawConvExpr_const_inv_any_wrap raw ld183 with
          ⟨rIdx, uIdxs, a', db, hnd, href, hdb, rb⟩ |
          ⟨recIdx, uIdxs, a', db, hnd, hrec, hdb, rb⟩
        · obtain ⟨hva, -⟩ := Lib.address_eq_spec ev215 ra rb
          have hd_eq : da = db := by
            by_contra hne
            rw [if_neg hne] at hva
            exact absurd (Value.field.inj hva) one_ne_zero
          subst hd_eq hdb
          exact ⟨0, by simp [FamilyOf.refHeadAt, FamilyOf.spineHead, hnd, href]⟩
        · obtain ⟨hva, -⟩ := Lib.address_eq_spec ev215 ra rb
          have hd_eq : da = db := by
            by_contra hne
            rw [if_neg hne] at hva
            exact absurd (Value.field.inj hva) one_ne_zero
          subst hd_eq hdb
          exact absurd (List.mem_of_getElem? hrec) hnot_rec
      | .Const_Const_other (he263 := he) .. | .Const_other (he270 := he) .. =>
        exact absurd (Value.field.inj he) one_ne_zero
      | .BVar_BVar_n0 (ld12 := ld12) .. | .BVar_BVar_other (ld12 := ld12) ..
      | .BVar_other (ld12 := ld12) .. | .Srt_Srt (ld12 := ld12) ..
      | .Srt_other (ld12 := ld12) .. | .App_App_n1 (ld12 := ld12) ..
      | .App_App_other (ld12 := ld12) .. | .App_other (ld12 := ld12) ..
      | .Lam_Lam (ld12 := ld12) .. | .Lam_other (ld12 := ld12) ..
      | .Forall_Forall (ld12 := ld12) .. | .Forall_other (ld12 := ld12) ..
      | .Let_Let_n1_n1 (ld12 := ld12) .. | .Let_Let_n1_other (ld12 := ld12) ..
      | .Let_Let_other (ld12 := ld12) .. | .Let_other (ld12 := ld12) ..
      | .Lit_Lit (ld12 := ld12) .. | .Lit_other (ld12 := ld12) ..
      | .Proj_Proj_n1 (ld12 := ld12) .. | .Proj_Proj_other (ld12 := ld12) ..
      | .Proj_other (ld12 := ld12) .. =>
        have hv := Except.ok.inj (ld.symm.trans ld12)
        simp [kexprEnum] at hv
      | .other (ld12 := ld12) (hne273 := hne) .. =>
        have hv := Except.ok.inj (ld.symm.trans ld12)
        exact False.elim (hne [_, _] rfl hv.symm)
    rcases hrel with ⟨h', cs, _, ev⟩ | ⟨xsm, h', cs, _, ev⟩
    · exact hkeq ev
    · match Obs.«KernelCheck::wrap_rel».obs ev with
      | .other_other_other (ev765 := evk) .. => exact hkeq evk
      | .Let_Let_n1_n1 (ld12 := ld12) .. =>
        have hv := Except.ok.inj (ld.symm.trans ld12); simp [kexprEnum] at hv
      | .other_other_App_App_n1 (ld242 := ld242) ..
      | .other_other_App_App_other (ld242 := ld242) ..
      | .other_other_App_other (ld242 := ld242) ..
      | .other_other_Lam_Lam (ld242 := ld242) ..
      | .other_other_Lam_other (ld242 := ld242) ..
      | .other_other_Forall_Forall (ld242 := ld242) ..
      | .other_other_Forall_other (ld242 := ld242) ..
      | .other_other_Proj_Proj_n1 (ld242 := ld242) ..
      | .other_other_Proj_Proj_other (ld242 := ld242) ..
      | .other_other_Proj_other (ld242 := ld242) .. =>
        have hv := Except.ok.inj (ld.symm.trans ld242); simp [kexprEnum] at hv
      | .Let_Let_n1_other (he166 := he) .. | .Let_Let_other (he173 := he) ..
      | .Let_other (he180 := he) .. | .other_Let (he224 := he) .. =>
        exact absurd (Value.field.inj he) one_ne_zero
  | @app p fp ap a ld hac_f ih =>
    intro hrel raw
    rcases hrel with ⟨h', cs, hsub, ev⟩ | ⟨xsm, h', cs, hsub, ev⟩
    · match Obs.«KernelCheck::kexpr_struct_eq».obs ev with
      | .App_App_n1 (x_fa := xfa) (x_fb := xfb) (ld12 := ld12) (ld301 := ld301)
          (ev333 := evf) (hc376 := hc) .. =>
        have hv := Except.ok.inj (ld.symm.trans ld12)
        simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hv
        obtain ⟨rfl, rfl⟩ := hv
        obtain ⟨b', ef, ea, hnd, raw_f, -⟩ := rawConvExpr_app_inv_wrap raw ld301
        obtain ⟨fuel, href⟩ :=
          ih (Or.inl ⟨_, _, fun cl hcl' => hsub cl (by rw [hc]; call_mem), evf⟩) raw_f
        exact ⟨fuel + 1, by simp only [FamilyOf.refHeadAt, FamilyOf.spineHead, hnd]; exact href⟩
      | .App_App_other (he381 := he) .. | .App_other (he388 := he) .. =>
        exact absurd (Value.field.inj he) one_ne_zero
      | .BVar_BVar_n0 (ld12 := ld12) .. | .BVar_BVar_other (ld12 := ld12) ..
      | .BVar_other (ld12 := ld12) .. | .Srt_Srt (ld12 := ld12) ..
      | .Srt_other (ld12 := ld12) .. | .Const_Const_n1 (ld12 := ld12) ..
      | .Const_Const_other (ld12 := ld12) .. | .Const_other (ld12 := ld12) ..
      | .Lam_Lam (ld12 := ld12) .. | .Lam_other (ld12 := ld12) ..
      | .Forall_Forall (ld12 := ld12) .. | .Forall_other (ld12 := ld12) ..
      | .Let_Let_n1_n1 (ld12 := ld12) .. | .Let_Let_n1_other (ld12 := ld12) ..
      | .Let_Let_other (ld12 := ld12) .. | .Let_other (ld12 := ld12) ..
      | .Lit_Lit (ld12 := ld12) .. | .Lit_other (ld12 := ld12) ..
      | .Proj_Proj_n1 (ld12 := ld12) .. | .Proj_Proj_other (ld12 := ld12) ..
      | .Proj_other (ld12 := ld12) .. =>
        have hv := Except.ok.inj (ld.symm.trans ld12); simp [kexprEnum] at hv
      | .other (ld12 := ld12) (hne391 := hne) .. =>
        have hv := Except.ok.inj (ld.symm.trans ld12)
        exact False.elim (hne [_, _] rfl hv.symm)
    · match Obs.«KernelCheck::wrap_rel».obs ev with
      | .other_other_App_App_n1 (x_f := xf) (x_f2 := xf2) (ld242 := ld242) (ld271 := ld271)
          (ev303 := evf) (hc346 := hc) .. =>
        have hv := Except.ok.inj (ld.symm.trans ld242)
        simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hv
        obtain ⟨rfl, rfl⟩ := hv
        obtain ⟨b', ef, ea, hnd, raw_f, -⟩ := rawConvExpr_app_inv_wrap raw ld271
        obtain ⟨fuel, href⟩ :=
          ih (Or.inr ⟨xsm, _, _, fun cl hcl' => hsub cl (by rw [hc]; call_mem), evf⟩) raw_f
        exact ⟨fuel + 1, by simp only [FamilyOf.refHeadAt, FamilyOf.spineHead, hnd]; exact href⟩
      | .other_other_App_App_other (he351 := he) .. | .other_other_App_other (he358 := he) ..
      | .Let_Let_n1_other (he166 := he) .. | .Let_Let_other (he173 := he) ..
      | .Let_other (he180 := he) .. | .other_Let (he224 := he) .. =>
        exact absurd (Value.field.inj he) one_ne_zero
      | .Let_Let_n1_n1 (ld12 := ld12) .. =>
        have hv := Except.ok.inj (ld.symm.trans ld12); simp [kexprEnum] at hv
      | .other_other_Lam_Lam (ld242 := ld242) .. | .other_other_Lam_other (ld242 := ld242) ..
      | .other_other_Forall_Forall (ld242 := ld242) .. | .other_other_Forall_other (ld242 := ld242) ..
      | .other_other_Proj_Proj_n1 (ld242 := ld242) .. | .other_other_Proj_Proj_other (ld242 := ld242) ..
      | .other_other_Proj_other (ld242 := ld242) .. =>
        have hv := Except.ok.inj (ld.symm.trans ld242); simp [kexprEnum] at hv
      | .other_other_other (ld242 := ld242) (hne361 := hne) .. =>
        have hv := Except.ok.inj (ld.symm.trans ld242)
        exact False.elim (hne [_, _] rfl hv.symm)

/-- Transfer `HeapAppConst` + `HeapDomRel` directly into `FamilyOf.refHeadAt` on a `RawConvExpr`
right side when `a` is an `.iPrj` in `E₀` and `a ∉ recurAddrs`. -/
theorem heapAppConst_rawConvExpr_refHeadAt_dom {rootCalls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    {c : Ixon.Constant} {recurAddrs : List _root_.Address}
    {blobs : List (_root_.Address × ByteArray)}
    {a : _root_.Address} {ca : Ixon.Constant} {p : Ixon.InductProj}
    (hcE : recordOf E₀ a = some ca) (hi : ca.info = .iPrj p) (hnot_rec : a ∉ recurAddrs)
    {bound : Nat} {h : Heap F} {e : Ixon.Expr} {xg xd : SourceValue F}
    (hac : HeapAppConst h xg a) (hrel : HeapDomRel rootCalls h xg xd)
    (raw : L1.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h bound e xd) :
    ∃ fuel, FamilyOf.refHeadAt c fuel e = some a := by
  rcases hrel with hrel_eq | ⟨xsm, h', cs, hsub, ev⟩
  · exact heapAppConst_rawConvExpr_refHeadAt hnot_rec hac hrel_eq raw
  · match Obs.«KernelCheck::wrap_dom».obsx ev with
    | .other_n0_other_other (he_vjzsmrqa := he) .. =>
      exact absurd (Value.field.inj he) one_ne_zero
    | .Let (ev43 := ev43) (hc60 := hc) .. =>
      exact heapAppConst_rawConvExpr_refHeadAt hnot_rec hac
        (Or.inr ⟨xsm, h', _, fun cl hcl' => hsub cl (by rw [hc]; call_mem), ev43⟩) raw
    | .other_n0_n1 (ev_teknbelh := ev1) (hc_mhrqvtgu := hc) .. =>
      exact heapAppConst_rawConvExpr_refHeadAt hnot_rec hac
        (Or.inr ⟨xsm, _, _, fun cl hcl' => hsub cl (by rw [hc]; call_mem), ev1⟩) raw
    | .other_n0_other_n1_bind (ev_teknbelh := ev1) (ev_tyrbnlfr := ev2) (hc_uuoaavue := hc) .. =>
      exact False.elim (consume_wrapper_not_one_of_iprj hS hH hbd hcE hi
        (fun cl hcl' => hsub cl (by rw [hc]; call_mem)) (hac.mono ev1.heap_extends) ev2)
    | .other_other_n1_bind (ev121 := ev1) (hc170 := hc) .. =>
      exact False.elim (consume_wrapper_not_one_of_iprj hS hH hbd hcE hi
        (fun cl hcl' => hsub cl (by rw [hc]; call_mem)) hac ev1)
    | .other_other_other (ev121 := ev1) (ev_sarmpwvb := ev2) (hc176 := hc) .. =>
      have ext1 := ev1.heap_extends
      exact heapAppConst_rawConvExpr_refHeadAt hnot_rec (hac.mono ext1)
        (Or.inr ⟨xsm, h', _, fun cl hcl' => hsub cl (by rw [hc]; call_mem), ev2⟩) (raw.mono ext1)

/-- Transfer `HeapMotiveCarrier` + `HeapDomRel` directly into `FamilyOf.lastDom` + `refHeadAt` on
a `RawConvExpr` right side when `a` is an `.iPrj` in `E₀` and `a ∉ recurAddrs`. -/
theorem heapMotiveCarrier_rawConvExpr_lastDom {rootCalls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    {c : Ixon.Constant} {recurAddrs : List _root_.Address}
    {blobs : List (_root_.Address × ByteArray)}
    {a : _root_.Address} {ca : Ixon.Constant} {p : Ixon.InductProj}
    (hcE : recordOf E₀ a = some ca) (hi : ca.info = .iPrj p) (hnot_rec : a ∉ recurAddrs) :
    ∀ {bound : Nat} {h : Heap F} {e : Ixon.Expr} {xg xd : SourceValue F},
      HeapMotiveCarrier h xg a →
      HeapDomRel rootCalls h xg xd →
      L1.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h bound e xd →
      ∃ ed n_dom n_ref, FamilyOf.lastDom c n_dom e = some ed ∧
        FamilyOf.refHeadAt c n_ref ed = some a := by
  have to_eq : ∀ {h : Heap F} {xg xd dp bp lp : SourceValue F},
      loadValue h xg = .ok (.construct kexprEnum "Forall" [dp, bp, lp]) →
      HeapDomRel rootCalls h xg xd →
      ∃ h1, Heap.Extends h h1 ∧ HeapEqOrWrap rootCalls h1 xg xd := by
    intro h xg xd dp bp lp ld hrel
    rcases hrel with heq | ⟨xsm, h', cs, hsub, ev⟩
    · exact ⟨h, Heap.Extends.refl h, heq⟩
    · match Obs.«KernelCheck::wrap_dom».obsx ev with
      | .other_n0_other_other (he_vjzsmrqa := he) .. =>
        exact absurd (Value.field.inj he) one_ne_zero
      | .Let (ld12 := ld12) .. =>
        have hv := Except.ok.inj (ld.symm.trans ld12); simp [kexprEnum] at hv
      | .other_n0_n1 (ev_teknbelh := ev1) (hc_mhrqvtgu := hc) .. =>
        exact ⟨h, Heap.Extends.refl h,
          Or.inr ⟨xsm, _, _, fun cl hcl' => hsub cl (by rw [hc]; call_mem), ev1⟩⟩
      | .other_n0_other_n1_bind (ev_teknbelh := ev1) (ev_tyrbnlfr := ev2) .. =>
        exact False.elim (consume_wrapper_not_one_of_forall (loadValue_mono ev1.heap_extends ld) ev2)
      | .other_other_n1_bind (ev121 := ev1) .. =>
        exact False.elim (consume_wrapper_not_one_of_forall ld ev1)
      | .other_other_other (ev121 := ev1) (ev_sarmpwvb := ev2) (hc176 := hc) .. =>
        exact ⟨_, ev1.heap_extends,
          Or.inr ⟨xsm, h', _, fun cl hcl' => hsub cl (by rw [hc]; call_mem), ev2⟩⟩
  intro bound h e xg xd hm
  induction hm generalizing bound e xd with
  | last ld ldb hne hac =>
    intro hdom raw
    obtain ⟨h1, ext1, heq1⟩ := to_eq ld hdom
    obtain ⟨dp2, bp2, lp2, h_d, h_b, ext_d, ext_b, ld2, hrel_d, hrel_b⟩ :=
      heapEqOrWrap_forall_step heq1 (loadValue_mono ext1 ld)
    obtain ⟨b', ed, eb, hnd, raw_d, raw_b⟩ := rawConvExpr_forall_inv_wrap (raw.mono ext1) ld2
    obtain ⟨v2, ldb2, hne2⟩ :=
      heapEqOrWrap_not_forall hrel_b (loadValue_mono (ext1.trans ext_b) ldb) hne
    have hnb := rawConvExpr_not_forall_of_nonForall (raw_b.mono ext_b) ldb2 hne2
    obtain ⟨n_ref, href⟩ := heapAppConst_rawConvExpr_refHeadAt_dom hS hH hbd hcE hi hnot_rec
      (hac.mono (ext1.trans ext_d)) hrel_d (raw_d.mono ext_d)
    refine ⟨ed, 1, n_ref, ?_, href⟩
    simp only [FamilyOf.lastDom, hnd]
    cases hnb' : FamilyOf.node c eb with
    | all _ _ => exact absurd hnb' (hnb _ _)
    | _ => rfl
  | step ld ldb _ ih =>
    intro hdom raw
    obtain ⟨h1, ext1, heq1⟩ := to_eq ld hdom
    obtain ⟨dp2, bp2, lp2, _, h_b, _, ext_b, ld2, -, hrel_b⟩ :=
      heapEqOrWrap_forall_step heq1 (loadValue_mono ext1 ld)
    obtain ⟨b', ed, eb, hnd, -, raw_b⟩ := rawConvExpr_forall_inv_wrap (raw.mono ext1) ld2
    obtain ⟨dp3, bp3, lp3, _, _, _, _, ld3, -, -⟩ :=
      heapEqOrWrap_forall_step hrel_b (loadValue_mono (ext1.trans ext_b) ldb)
    obtain ⟨b'', ed', eb', hnd_b, -, -⟩ := rawConvExpr_forall_inv_wrap (raw_b.mono ext_b) ld3
    obtain ⟨ed_out, n_dom, n_ref, hld, href⟩ := ih (Or.inl hrel_b) (raw_b.mono ext_b)
    refine ⟨ed_out, n_dom + 1, n_ref, ?_, href⟩
    simp only [FamilyOf.lastDom, hnd, hnd_b]
    exact hld

/-- End-to-end `HeapForalls` + `HeapMotiveCarrier` + `HeapEqOrWrap` + `RawConvExpr` →
`∃ fuel, FamilyOf.motiveCarrierAt crb rc j fuel = some a`. -/
theorem heapEqOrWrap_motiveCarrierAt {rootCalls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    {crb : Ixon.Constant} {rc : Ixon.Recursor} {recurAddrs : List _root_.Address}
    {blobs : List (_root_.Address × ByteArray)} {h : Heap F} {j : Nat}
    {a : _root_.Address} {ca : Ixon.Constant} {p : Ixon.InductProj}
    {xg q dp bp lp xd : SourceValue F}
    (hcE : recordOf E₀ a = some ca) (hi : ca.info = .iPrj p) (hnot_rec : a ∉ recurAddrs)
    (hf : HeapForalls h (rc.params.toNat + j) xg q)
    (ld : loadValue h q = .ok (.construct kexprEnum "Forall" [dp, bp, lp]))
    (hm : HeapMotiveCarrier h dp a)
    (hrel : HeapEqOrWrap rootCalls h xg xd)
    (raw : L1.RawConvExpr crb.refs.toList recurAddrs crb.univs.toList crb.sharing.toList
      blobs h 4294967295 rc.typ xd) :
    ∃ fuel, FamilyOf.motiveCarrierAt crb rc j fuel = some a := by
  obtain ⟨yd, h_out, b', e', ext_out, hpeel, raw_y, hrel_y⟩ :=
    heapForalls_rawConvExpr_peel hf hrel raw
  obtain ⟨dp2, bp2, lp2, h_d, _, ext_d, _, ld2, hrel_d, -⟩ :=
    heapEqOrWrap_forall_step hrel_y (loadValue_mono ext_out ld)
  obtain ⟨b'', ed, eb, hnd, raw_d, -⟩ := rawConvExpr_forall_inv_wrap raw_y ld2
  obtain ⟨ed_out, n_dom, n_ref, hlast, href⟩ :=
    heapMotiveCarrier_rawConvExpr_lastDom hS hH hbd hcE hi hnot_rec
      (hm.mono (ext_out.trans ext_d)) hrel_d (raw_d.mono ext_d)
  refine ⟨max n_dom n_ref, ?_⟩
  unfold FamilyOf.motiveCarrierAt
  simp only [Bind.bind, Option.bind, hpeel, FamilyOf.domOf, hnd]
  rw [FamilyOf.lastDom_mono crb ed n_dom (max n_dom n_ref) (Nat.le_max_left _ _) hlast]
  exact FamilyOf.refHeadAt_mono (Nat.le_max_right _ _) href

/-- End-to-end `HeapForalls` + `HeapAppConst` + `HeapEqOrWrap` + `RawConvExpr` →
`∃ fuel, FamilyOf.majorHeadAt crb rc fuel = some a`. -/
theorem heapEqOrWrap_majorHeadAt {rootCalls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    {crb : Ixon.Constant} {rc : Ixon.Recursor} {recurAddrs : List _root_.Address}
    {blobs : List (_root_.Address × ByteArray)} {h : Heap F}
    {a : _root_.Address} {ca : Ixon.Constant} {p : Ixon.InductProj}
    {xg q dp bp lp xd : SourceValue F}
    (hcE : recordOf E₀ a = some ca) (hi : ca.info = .iPrj p) (hnot_rec : a ∉ recurAddrs)
    (hf : HeapForalls h (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
      xg q)
    (ld : loadValue h q = .ok (.construct kexprEnum "Forall" [dp, bp, lp]))
    (hac : HeapAppConst h dp a)
    (hrel : HeapEqOrWrap rootCalls h xg xd)
    (raw : L1.RawConvExpr crb.refs.toList recurAddrs crb.univs.toList crb.sharing.toList
      blobs h 4294967295 rc.typ xd) :
    ∃ fuel, FamilyOf.majorHeadAt crb rc fuel = some a := by
  obtain ⟨yd, h_out, b', e', ext_out, hpeel, raw_y, hrel_y⟩ :=
    heapForalls_rawConvExpr_peel hf hrel raw
  obtain ⟨dp2, bp2, lp2, h_d, _, ext_d, _, ld2, hrel_d, -⟩ :=
    heapEqOrWrap_forall_step hrel_y (loadValue_mono ext_out ld)
  obtain ⟨b'', ed, eb, hnd, raw_d, -⟩ := rawConvExpr_forall_inv_wrap raw_y ld2
  obtain ⟨fuel, href⟩ :=
    heapAppConst_rawConvExpr_refHeadAt_dom hS hH hbd hcE hi hnot_rec
      (hac.mono (ext_out.trans ext_d)) hrel_d (raw_d.mono ext_d)
  refine ⟨fuel, ?_⟩
  unfold FamilyOf.majorHeadAt
  simp only [Bind.bind, Option.bind, hpeel, FamilyOf.domOf, hnd]
  exact href

end IxVM.Refinement.Binding.FamilyRecon
