import Ix.CompileCert.Opt.RewriteTotal
import Ix.Compile.Pass.Driver
import Ix.CompileCert.Opt.R2FuelDiagnostic

/-!
UNCOMPILED R-2 proof slice. No production source or theorem endpoint changes.

Successful producer runs can have different sufficient fuel. Their exact
expansion results nevertheless agree, and the existing conversion theorem
applies at the producer's fuel. These facts do not identify the current
runtime's result/error with a pure run at the current fuel.

`PureProduced` is an intermediate witness to be constructed by the actual
runtime/cache induction, not a new premise of the final compiler theorem.
That construction, structural-key confirmation, and environment-snapshot
transport remain open. The actual Driver hit equation below keeps the fresh
header and type rewrite: cached data supplies only the value.
-/

namespace Ix.CompileCert.Opt.ExpansionProvenance

open Ix (Name Level Expr DefinitionVal)
open Ix.Compile.Pass (Expansion RwState RwM BlockView)
open Ix.CompileCert.Conv
open Ix.Compile.Canon (substLevels)

/-- Evidence of an exact successful pure producer at its own fuel. -/
def PureProduced (lookup : Name → Except String (Option Expansion)) (hook : Hook)
    (name : Name) (value : Expansion) : Prop :=
  ∃ fuel, expansionOfP lookup hook false fuel name = .ok (some value)

theorem produced_of_run {lookup : Name → Except String (Option Expansion)}
    {hook : Hook} {name : Name} {value : Expansion} {fuel : Nat}
    (run : expansionOfP lookup hook false fuel name = .ok (some value)) :
    PureProduced lookup hook name value := ⟨fuel, run⟩

/-- A larger pure bound is used only to compare two completed producers.
It does not replace the fuel of either actual runtime call. -/
theorem produced_unique {lookup : Name → Except String (Option Expansion)}
    {hook : Hook} {name : Name} {left right : Expansion}
    (hl : PureProduced lookup hook name left)
    (hr : PureProduced lookup hook name right) : left = right := by
  obtain ⟨fl, hl⟩ := hl
  obtain ⟨fr, hr⟩ := hr
  have leftRun := (rwP_mono (expansion? := lookup) (opt? := hook)
    (inPlace := false) fl (max fl fr) (Nat.le_max_left _ _)).1 name (some left) hl
  have rightRun := (rwP_mono (expansion? := lookup) (opt? := hook)
    (inPlace := false) fr (max fl fr) (Nat.le_max_right _ _)).1 name (some right) hr
  rw [leftRun] at rightRun
  cases rightRun
  rfl

/-- The original laws yield the raw source expansion and its unchanged
universe-parameter/arity fields; no current-fuel replay is needed. -/
theorem produced_origin {Γ : Env}
    {lookup : Name → Except String (Option Expansion)} {hook : Hook}
    (heads : HeadLaws Γ lookup) (levels : LevelClosed Γ)
    (faithful : HookFaithful Γ hook) (stable : HookSiteStable hook)
    {name : Name} {value : Expansion} (made : PureProduced lookup hook name value) :
    ∃ raw, lookup name = .ok (some raw) ∧
      value.levelParams = raw.levelParams ∧ value.arity = raw.arity ∧
      ExprConv Γ value.value raw.value := by
  obtain ⟨fuel, run⟩ := made
  exact (rwP_faithful heads levels faithful stable fuel).1 name value run

/-- The producer's converted value still denotes the same head at every
universe instance, using exactly the pre-existing HeadLaws/LevelClosed. -/
theorem produced_head {Γ : Env}
    {lookup : Name → Except String (Option Expansion)} {hook : Hook}
    (heads : HeadLaws Γ lookup) (levels : LevelClosed Γ)
    (faithful : HookFaithful Γ hook) (stable : HookSiteStable hook)
    {name : Name} {value : Expansion} (made : PureProduced lookup hook name value)
    (us : Array Level) :
    ExprConv Γ (substLevels value.levelParams us value.value) (Expr.mkConst name us) := by
  obtain ⟨raw, source, parameters, _, converts⟩ :=
    produced_origin heads levels faithful stable made
  rw [parameters]
  have rewritten := conv_substLevels levels raw.levelParams us converts
  change Conv Γ (er (substLevels raw.levelParams us value.value)) (.const name us)
  exact .trans rewritten (.symm (.step (.ax (heads name raw source us))))

/-- When the actual lookup has been identified with the freshly built
source expansion, the producer witness gives all three required fields.
Discharging that lookup identity across actual snapshots remains required. -/
theorem produced_against_fresh {Γ : Env}
    {lookup : Name → Except String (Option Expansion)} {hook : Hook}
    (heads : HeadLaws Γ lookup) (levels : LevelClosed Γ)
    (faithful : HookFaithful Γ hook) (stable : HookSiteStable hook)
    {name : Name} {value fresh : Expansion}
    (made : PureProduced lookup hook name value)
    (current : lookup name = .ok (some fresh)) :
    value.levelParams = fresh.levelParams ∧ value.arity = fresh.arity ∧
      ExprConv Γ value.value fresh.value := by
  obtain ⟨raw, source, parameters, arity, converts⟩ :=
    produced_origin heads levels faithful stable made
  rw [current] at source
  cases source
  exact ⟨parameters, arity, converts⟩

private theorem run_bind {α β : Type} (m : RwM α) (k : α → RwM β) (st : RwState) :
    (m >>= k).run st = (m.run st >>= fun p => (k p.1).run p.2) := rfl

private theorem run_pure {α : Type} (value : α) (st : RwState) :
    (pure value : RwM α).run st = .ok (value, st) := rfl

private theorem run_get (st : RwState) :
    (get : RwM RwState).run st = .ok (st, st) := rfl

/-- An actual hit retains the complete input state and never invokes the
lookup. The hit equation alone makes no semantic-validity claim. -/
theorem expansion_hit (lookup : Name → Except String (Option Expansion))
    (fuel : Nat) (name : Name) (st : RwState) (value : Expansion)
    (found : st.exps.get? name = some value) :
    (Ix.Compile.Pass.expansionOf lookup (fuel + 1) name).run st =
      .ok (some value, st) := by
  rw [Ix.Compile.Pass.expansionOf.eq_def]
  simp only [run_bind, run_pure, run_get, found, Except.bind]

/-- Proof-side spelling of the exact DefinitionVal assembled by imageDeclWith.
The fresh expansion supplies the header; the cache supplies only the value. -/
def assembled (cenv : Ix.CompileM.CompileEnv) (name : Name) (fresh : Expansion)
    (value type : Expr) : DefinitionVal :=
  { cnst := { name, levelParams := fresh.levelParams, type }
    value, hints := .abbrev
    safety := match (Ix.Compile.Pass.viewInput cenv).const? name with
      | some (.defnInfo d) => d.safety
      | some (.recInfo r) => if r.isUnsafe then .unsafe else .safe
      | _ => .safe
    all := #[name] }

/-- Factor the real cached-value branch, including the type callback's
error and full output state. The hypotheses name only the executed branches. -/
theorem imageDecl_hit_eq (cenv : Ix.CompileM.CompileEnv) (views : Std.HashMap Name BlockView)
    (name key : Name)
    (table : Std.HashMap Name (Thunk (Except String (Option Expansion))))
    (st : RwState) (view : BlockView) (fresh cached : Expansion) (type : Expr)
    (head : cenv.p3Heads.get? name = some key)
    (viewRead : Ix.Compile.Pass.viewOf cenv views key = .ok view)
    (expanded : view.expansion (Ix.Compile.Pass.viewInput cenv) name = .ok (fresh, type))
    (found : st.exps.get? name = some cached) :
    Ix.Compile.Pass.imageDeclWith cenv views name table st =
      ((Ix.Compile.Pass.rw (Ix.Compile.Pass.expansionLookupIn table cenv views)
        Ix.Compile.Pass.rewriteFuel false type).run st >>= fun (type', out) =>
          .ok (assembled cenv name fresh cached.value type', out)) := by
  unfold Ix.Compile.Pass.imageDeclWith
  simp only [head, viewRead, expanded, Except.bind, found]
  simp only [run_bind, run_pure, Except.bind]
  cases typed : (Ix.Compile.Pass.rw
    (Ix.Compile.Pass.expansionLookupIn table cenv views)
    Ix.Compile.Pass.rewriteFuel false type).run st with
  | error error => rfl
  | ok pair =>
    obtain ⟨type', out⟩ := pair
    rfl

/-- Success does not hide a stale header: this retains the complete result,
including its fresh levelParams and the type rewrite's entire state. -/
theorem imageDecl_hit_success (cenv : Ix.CompileM.CompileEnv) (views : Std.HashMap Name BlockView)
    (name key : Name)
    (table : Std.HashMap Name (Thunk (Except String (Option Expansion))))
    (st out : RwState) (view : BlockView) (fresh cached : Expansion) (type type' : Expr)
    (head : cenv.p3Heads.get? name = some key)
    (viewRead : Ix.Compile.Pass.viewOf cenv views key = .ok view)
    (expanded : view.expansion (Ix.Compile.Pass.viewInput cenv) name = .ok (fresh, type))
    (found : st.exps.get? name = some cached)
    (typed : (Ix.Compile.Pass.rw (Ix.Compile.Pass.expansionLookupIn table cenv views)
      Ix.Compile.Pass.rewriteFuel false type).run st = .ok (type', out)) :
    Ix.Compile.Pass.imageDeclWith cenv views name table st =
      .ok (assembled cenv name fresh cached.value type', out) := by
  rw [imageDecl_hit_eq cenv views name key table st view fresh cached type
    head viewRead expanded found, typed]
  rfl

theorem imageDecl_hit_error (cenv : Ix.CompileM.CompileEnv) (views : Std.HashMap Name BlockView)
    (name key : Name)
    (table : Std.HashMap Name (Thunk (Except String (Option Expansion))))
    (st : RwState) (view : BlockView) (fresh cached : Expansion) (type : Expr) (error : String)
    (head : cenv.p3Heads.get? name = some key)
    (viewRead : Ix.Compile.Pass.viewOf cenv views key = .ok view)
    (expanded : view.expansion (Ix.Compile.Pass.viewInput cenv) name = .ok (fresh, type))
    (found : st.exps.get? name = some cached)
    (typed : (Ix.Compile.Pass.rw (Ix.Compile.Pass.expansionLookupIn table cenv views)
      Ix.Compile.Pass.rewriteFuel false type).run st = .error error) :
    Ix.Compile.Pass.imageDeclWith cenv views name table st = .error error := by
  rw [imageDecl_hit_eq cenv views name key table st view fresh cached type
    head viewRead expanded found, typed]
  rfl

/-- The actual cached branch and semantic producer elimination join here.
The lookup/fresh identity is an explicit internal source-adapter obligation;
this conditional component is not a replacement for the compiler endpoint. -/
theorem imageDecl_hit_produced {Γ : Env}
    (cenv : Ix.CompileM.CompileEnv) (views : Std.HashMap Name BlockView)
    (name key : Name)
    (table : Std.HashMap Name (Thunk (Except String (Option Expansion))))
    (st out : RwState) (view : BlockView) (fresh cached : Expansion) (type type' : Expr)
    (head : cenv.p3Heads.get? name = some key)
    (viewRead : Ix.Compile.Pass.viewOf cenv views key = .ok view)
    (expanded : view.expansion (Ix.Compile.Pass.viewInput cenv) name = .ok (fresh, type))
    (found : st.exps.get? name = some cached)
    (typed : (Ix.Compile.Pass.rw (Ix.Compile.Pass.expansionLookupIn table cenv views)
      Ix.Compile.Pass.rewriteFuel false type).run st = .ok (type', out))
    (heads : HeadLaws Γ (Ix.Compile.Pass.expansionLookupIn table cenv views))
    (levels : LevelClosed Γ) (faithful : HookFaithful Γ st.opt?)
    (stable : HookSiteStable st.opt?)
    (made : PureProduced (Ix.Compile.Pass.expansionLookupIn table cenv views)
      st.opt? name cached)
    (current : Ix.Compile.Pass.expansionLookupIn table cenv views name = .ok (some fresh)) :
    ∃ result, Ix.Compile.Pass.imageDeclWith cenv views name table st = .ok (result, out) ∧
      result.cnst.levelParams = fresh.levelParams ∧ result.cnst.type = type' ∧
      ExprConv Γ result.value fresh.value := by
  refine ⟨assembled cenv name fresh cached.value type',
    imageDecl_hit_success cenv views name key table st out view fresh cached type type'
      head viewRead expanded found typed, rfl, rfl, ?_⟩
  exact (produced_against_fresh heads levels faithful stable made current).2.2

/-- For the concrete cold-reachable fuel witness, the warmed low-fuel hit
still keeps exactly the raw value. Thus the error mismatch is not by itself
a conversion counterexample. No semantic cache validity is assumed here. -/
theorem reachable_fuel_value_neighbor (Γ : Env) (name : Name)
    (literal : Lean.Literal) (address : Address) :
    ∃ value : Expansion,
      (Ix.Compile.Pass.expansionOf (ReachableFuel.lookup literal address) 2 name).run
          ReachableFuel.cold = .ok (some value, ReachableFuel.warm name literal address) ∧
      (Ix.Compile.Pass.expansionOf (ReachableFuel.lookup literal address) 1 name).run
          (ReachableFuel.warm name literal address) =
        .ok (some value, ReachableFuel.warm name literal address) ∧
      ExprConv Γ value.value (ReachableFuel.input literal address).value := by
  exact ⟨ReachableFuel.ready literal address,
    ReachableFuel.cold_high_run name literal address,
    ReachableFuel.warm_low_run name literal address, Conv.refl _⟩

end Ix.CompileCert.Opt.ExpansionProvenance
