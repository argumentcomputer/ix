import Compilatrix.IxIR1.LowerStateBase
import Compilatrix.IxIR1.Sim

/-!
# Proof interface for the IxIR₀ → IxIR₁ lowering

This file begins the compiler induction proper. `IxIR1.Sim` proves exact
ownership interfaces for evaluator operations; here those interfaces are
lifted to the continuation-building shape used by `Lower.Emit` and tied to
the lowerer's absolute-slot environment.

The central judgment is `EmitSound`: an emitter transforms any continuation
valid under its output state predicate into code valid under its input state
predicate. This is a weakest-precondition presentation of the existing
`Code → Code` difference-list representation, so emitter composition becomes
the compiler induction's sequencing rule.
-/

namespace Compilatrix.IxIR1.LowerSim

open Compilatrix.Ixon (Owned Uses)
open Compilatrix.IxIR1.Lower
open Compilatrix.IxIR1.Sim

/-! ## Runtime realization of the compile-time environment -/

/-- Realize the held entries of a compile-time `VEnv` as an ordered root
list. Released slots and the synthetic recursor-self entry own no runtime
root. Absolute slots are interpreted with the same `VEnv.rel` calculation
used by code emission. -/
inductive EntriesRealize (Γ : VEnv) (env : List RVal) :
    List VEntry → List Root → Prop where
  | nil : EntriesRealize Γ env [] []
  | released {abs remaining uses entries roots} :
      abs < Γ.depth →
      EntriesRealize Γ env entries roots →
      EntriesRealize Γ env
        (.slot abs remaining uses false :: entries) roots
  | held {abs remaining uses entries roots value} :
      abs < Γ.depth →
      env[Γ.rel abs]? = some value →
      EntriesRealize Γ env entries roots →
      EntriesRealize Γ env
        (.slot abs remaining uses true :: entries)
        (⟨worldOfUses uses, value⟩ :: roots)
  | recSelf {arity entries roots} :
      EntriesRealize Γ env entries roots →
      EntriesRealize Γ env (.recSelf arity :: entries) roots

theorem EntriesRealize.append {Γ : VEnv} {env : List RVal}
    {left right : List VEntry} {leftRoots rightRoots : List Root}
    (hleft : EntriesRealize Γ env left leftRoots)
    (hright : EntriesRealize Γ env right rightRoots) :
    EntriesRealize Γ env (left ++ right) (leftRoots ++ rightRoots) := by
  induction hleft with
  | nil => simpa using hright
  | released habs _ ih =>
    simpa using EntriesRealize.released habs ih
  | held habs hslot _ ih =>
    simpa using EntriesRealize.held habs hslot ih
  | recSelf _ ih =>
    simpa using EntriesRealize.recSelf ih

/-- A runtime environment realizes a `VEnv` when its physical depth agrees
and its held entries realize exactly the listed logical roots. -/
structure VEnvRealizes (Γ : VEnv) (env : List RVal)
    (roots : List Root) : Prop where
  depth_eq : env.length = Γ.depth
  entries : EntriesRealize Γ env Γ.entries roots

/-! ## Companion source-environment graph

The ownership induction above deliberately forgets source values. The
semantic induction instead layers the following graph over the same `VEnv`
and exact root order. Held entries relate their source value to the runtime
slot through `ValueGraph`; released entries retain only the source-list
shape; and the synthetic recursor-self entry is described by a separate
static relation because it emits `callSelf` without occupying a runtime
slot. -/

/-- Correspondence for the synthetic source recursor value represented by a
`VEntry.recSelf`. The enclosing recursor theorem will instantiate the source
address as well as the shared target function contract. -/
abbrev RecSelfRel := IxIR0.Value → Nat → Prop

/-! ## Lifted closures and their stored pap prefixes -/

/-- The outer de Bruijn entries captured by lambda lifting, in the exact
order used by `lowerLam`. -/
def liftCaptureIndices (entryCount : Nat) (expr : IxIR0.Expr) : List Nat :=
  (List.range entryCount).filter (fun index => countUses index expr > 0)

/-- `values` are the source-environment values at `indices`, in order.
Making lookup success proof-relevant avoids a default source value and gives
the capture-lowering induction exactly the relation it has to construct. -/
inductive ValuesAt (sourceEnv : List IxIR0.Value) :
    List Nat → List IxIR0.Value → Prop where
  | nil : ValuesAt sourceEnv [] []
  | cons {index : Nat} {value : IxIR0.Value}
      {indices : List Nat} {values : List IxIR0.Value} :
      sourceEnv[index]? = some value →
      ValuesAt sourceEnv indices values →
      ValuesAt sourceEnv (index :: indices) (value :: values)

@[simp] theorem ValuesAt.length {sourceEnv : List IxIR0.Value}
    {indices : List Nat} {values : List IxIR0.Value}
    (h : ValuesAt sourceEnv indices values) :
    values.length = indices.length := by
  induction h <;> simp_all

theorem ValuesAt.exists_of_forall_lt
    (sourceEnv : List IxIR0.Value) (indices : List Nat)
    (hbound : ∀ index, index ∈ indices → index < sourceEnv.length) :
    ∃ values, ValuesAt sourceEnv indices values := by
  induction indices with
  | nil => exact ⟨[], .nil⟩
  | cons index rest ih =>
    have hindex : index < sourceEnv.length :=
      hbound index (by simp)
    obtain ⟨values, hvalues⟩ := ih (fun candidate hmember =>
      hbound candidate (by simp [hmember]))
    let value := sourceEnv[index]
    refine ⟨value :: values, .cons ?_ hvalues⟩
    exact List.getElem?_eq_some_iff.mpr ⟨hindex, rfl⟩

/-- Every compiler-selected capture index is valid when the source and
lowering environments have the same logical length. -/
theorem ValuesAt.exists_liftCaptureIndices
    (sourceEnv : List IxIR0.Value) (entryCount : Nat)
    (expr : IxIR0.Expr) (hlength : sourceEnv.length = entryCount) :
    ∃ values,
      ValuesAt sourceEnv (liftCaptureIndices entryCount expr) values := by
  apply ValuesAt.exists_of_forall_lt
  intro index hmember
  obtain ⟨hrange, _⟩ := List.mem_filter.mp hmember
  have hindex := List.mem_range.mp hrange
  omega

/-- A source closure after zero or more applications from the leading lambda
run. Arguments are stored in application order, while the evaluator closure
environment grows in reverse order. Requiring the residual expression to be
a lambda makes every represented prefix strictly under-saturated. -/
inductive LambdaPrefix :
    List IxIR0.Value → IxIR0.Expr →
    List IxIR0.Value → IxIR0.Value → Prop where
  | nil {sourceEnv : List IxIR0.Value} {uses : Uses}
      {body : IxIR0.Expr} :
      LambdaPrefix sourceEnv (.lam uses body) []
        (.clos uses sourceEnv body)
  | cons {sourceEnv : List IxIR0.Value} {uses : Uses}
      {body : IxIR0.Expr} {argument : IxIR0.Value}
      {arguments : List IxIR0.Value} {value : IxIR0.Value} :
      LambdaPrefix (argument :: sourceEnv) body arguments value →
      LambdaPrefix sourceEnv (.lam uses body)
        (argument :: arguments) value

/-- A represented closure prefix contains fewer supplied parameters than the
leading lambda arity, matching the target evaluator's pap invariant. -/
theorem LambdaPrefix.length_lt_lamArity
    {sourceEnv : List IxIR0.Value} {expr : IxIR0.Expr}
    {arguments : List IxIR0.Value} {value : IxIR0.Value}
    (h : LambdaPrefix sourceEnv expr arguments value) :
    arguments.length < lamArity expr := by
  induction h with
  | nil => simp [lamArity]
  | cons _ ih =>
      simp only [List.length_cons, lamArity]
      omega

/-- Provenance boundary for one generated lifted declaration. The concrete
compiler relation below supplies this from an exact `lowerFnBody` run and a
declaration in the accumulated lowering state. -/
abbrev LiftCodeRel :=
  Ixon.Address → Nat → IxIR0.Expr → Prop

/-- Function correspondence for lifted paps. The pap stores selected outer
captures followed by already supplied parameters; the related source value
is precisely the residual closure after that parameter prefix. -/
def LiftedFunctionRel (liftRel : LiftCodeRel) : Sim.FunctionRel :=
  fun value address arity captures =>
    ∃ sourceEnv expr selected supplied,
      liftRel address sourceEnv.length expr ∧
      ValuesAt sourceEnv (liftCaptureIndices sourceEnv.length expr) selected ∧
      captures = selected ++ supplied ∧
      arity = selected.length + lamArity expr ∧
      LambdaPrefix sourceEnv expr supplied value

theorem LiftedFunctionRel.initial {liftRel : LiftCodeRel}
    {sourceEnv : List IxIR0.Value} {uses : Uses} {body : IxIR0.Expr}
    {selected : List IxIR0.Value} {address : Ixon.Address}
    (hlift : liftRel address sourceEnv.length (.lam uses body))
    (hselected : ValuesAt sourceEnv
      (liftCaptureIndices sourceEnv.length (.lam uses body)) selected) :
    LiftedFunctionRel liftRel (.clos uses sourceEnv body) address
      (selected.length + lamArity (.lam uses body)) selected := by
  refine ⟨sourceEnv, .lam uses body, selected, [], hlift, hselected,
    ?_, rfl, .nil⟩
  simp

theorem LiftedFunctionRel.underfilled {liftRel : LiftCodeRel}
    {value : IxIR0.Value} {address : Ixon.Address} {arity : Nat}
    {captures : List IxIR0.Value}
    (h : LiftedFunctionRel liftRel value address arity captures) :
    captures.length < arity := by
  obtain ⟨sourceEnv, expr, selected, supplied, _, _, rfl, rfl,
    hprefix⟩ := h
  have hunder := hprefix.length_lt_lamArity
  simp only [List.length_append]
  omega

/-- Lifted function correspondence is monotone in its declaration-provenance
relation. This lets a local lowering result be transported to the final
whole-program accumulation. -/
theorem LiftedFunctionRel.mono {before after : LiftCodeRel}
    (hmono : ∀ address entryCount expr,
      before address entryCount expr → after address entryCount expr)
    {value : IxIR0.Value} {address : Ixon.Address} {arity : Nat}
    {captures : List IxIR0.Value}
    (h : LiftedFunctionRel before value address arity captures) :
    LiftedFunctionRel after value address arity captures := by
  obtain ⟨sourceEnv, expr, selected, supplied, hlift, hselected,
    hcaptures, harity, hprefix⟩ := h
  exact ⟨sourceEnv, expr, selected, supplied,
    hmono address sourceEnv.length expr hlift,
    hselected, hcaptures, harity, hprefix⟩

/-- Pointwise semantic realization of a source evaluator environment by a
lowering environment and its runtime stack. The root list has exactly the
same order as `EntriesRealize`, so it can be consumed directly by
`RootsGraph` and `RootOwnership`. -/
inductive EntriesValueGraph (funRel : Sim.FunctionRel)
    (recSelfRel : RecSelfRel) (store : Store) (Γ : VEnv)
    (env : List RVal) :
    List VEntry → List IxIR0.Value → List Root → Prop where
  | nil : EntriesValueGraph funRel recSelfRel store Γ env [] [] []
  | released {abs remaining : Nat} {uses : Uses}
      {entries : List VEntry} {source : IxIR0.Value}
      {sources : List IxIR0.Value} {roots : List Root} :
      abs < Γ.depth →
      EntriesValueGraph funRel recSelfRel store Γ env
        entries sources roots →
      EntriesValueGraph funRel recSelfRel store Γ env
        (.slot abs remaining uses false :: entries)
        (source :: sources) roots
  | held {abs remaining : Nat} {uses : Uses}
      {entries : List VEntry} {source : IxIR0.Value}
      {sources : List IxIR0.Value} {value : RVal}
      {roots : List Root} :
      abs < Γ.depth →
      env[Γ.rel abs]? = some value →
      HasWorld store (worldOfUses uses) value →
      Sim.ValueGraph funRel store source value →
      EntriesValueGraph funRel recSelfRel store Γ env
        entries sources roots →
      EntriesValueGraph funRel recSelfRel store Γ env
        (.slot abs remaining uses true :: entries)
        (source :: sources)
        (⟨worldOfUses uses, value⟩ :: roots)
  | recSelf {arity : Nat} {entries : List VEntry}
      {source : IxIR0.Value} {sources : List IxIR0.Value}
      {roots : List Root} :
      recSelfRel source arity →
      EntriesValueGraph funRel recSelfRel store Γ env
        entries sources roots →
      EntriesValueGraph funRel recSelfRel store Γ env
        (.recSelf arity :: entries) (source :: sources) roots

/-- A complete source environment realized by a lowering environment. -/
structure VEnvValueGraph (funRel : Sim.FunctionRel)
    (recSelfRel : RecSelfRel) (store : Store) (Γ : VEnv)
    (sourceEnv : List IxIR0.Value) (env : List RVal)
    (roots : List Root) : Prop where
  depth_eq : env.length = Γ.depth
  entries : EntriesValueGraph funRel recSelfRel store Γ env
    Γ.entries sourceEnv roots

/-- The companion graph forgets to the existing target-stack realization. -/
theorem EntriesValueGraph.entriesRealize {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {store : Store} {Γ : VEnv}
    {env : List RVal} {entries : List VEntry}
    {sourceEnv : List IxIR0.Value} {roots : List Root}
    (h : EntriesValueGraph funRel recSelfRel store Γ env
      entries sourceEnv roots) :
    EntriesRealize Γ env entries roots := by
  induction h with
  | nil => exact .nil
  | released hbound _ ih => exact .released hbound ih
  | held hbound hslot _ _ _ ih => exact .held hbound hslot ih
  | recSelf _ _ ih => exact .recSelf ih

/-- The exact root order carried by the environment graph is a semantic
`RootsGraph`; this is the bridge from logical compiler slots to pure source
values. -/
theorem EntriesValueGraph.rootsGraph {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {store : Store} {Γ : VEnv}
    {env : List RVal} {entries : List VEntry}
    {sourceEnv : List IxIR0.Value} {roots : List Root}
    (h : EntriesValueGraph funRel recSelfRel store Γ env
      entries sourceEnv roots) :
    ∃ sourceRoots : List (Owned × IxIR0.Value),
      Sim.RootsGraph funRel store sourceRoots roots := by
  induction h with
  | nil => exact ⟨[], .nil⟩
  | released _ _ ih => exact ih
  | @held _ _ uses _ source _ value _ _ _ hworld hvalue _ ih =>
      obtain ⟨sourceRoots, hroots⟩ := ih
      exact ⟨(worldOfUses uses, source) :: sourceRoots,
        .cons rfl hworld hvalue hroots⟩
  | recSelf _ _ ih => exact ih

@[simp] theorem EntriesValueGraph.source_length {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {store : Store} {Γ : VEnv}
    {env : List RVal} {entries : List VEntry}
    {sourceEnv : List IxIR0.Value} {roots : List Root}
    (h : EntriesValueGraph funRel recSelfRel store Γ env
      entries sourceEnv roots) :
    sourceEnv.length = entries.length := by
  induction h <;> simp_all

/-- Looking up a held compiler entry recovers the related source and target
values needed by the variable case of the semantic induction. -/
theorem EntriesValueGraph.getHeld {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {store : Store} {Γ : VEnv}
    {env : List RVal} {entries : List VEntry}
    {sourceEnv : List IxIR0.Value} {roots : List Root}
    {i abs remaining : Nat} {uses : Uses}
    (h : EntriesValueGraph funRel recSelfRel store Γ env
      entries sourceEnv roots)
    (hentry : entries[i]? = some (.slot abs remaining uses true)) :
    ∃ source value,
      sourceEnv[i]? = some source ∧
      env[Γ.rel abs]? = some value ∧
      HasWorld store (worldOfUses uses) value ∧
      Sim.ValueGraph funRel store source value := by
  induction h generalizing i with
  | nil => simp at hentry
  | released _ _ ih =>
    cases i with
    | zero => simp at hentry
    | succ i =>
      rw [List.getElem?_cons_succ] at hentry
      obtain ⟨source, value, hsource, hslot, hworld, hvalue⟩ :=
        ih hentry
      exact ⟨source, value, by simpa using hsource,
        hslot, hworld, hvalue⟩
  | @held curAbs curRemaining curUses tail source sources value
      tailRoots hbound hslot hworld hvalue htail ih =>
    cases i with
    | zero =>
      rw [List.getElem?_cons_zero] at hentry
      have heqs : curAbs = abs ∧ curRemaining = remaining ∧
          curUses = uses := by simpa using hentry
      obtain ⟨rfl, rfl, rfl⟩ := heqs
      exact ⟨source, value, rfl, hslot, hworld, hvalue⟩
    | succ i =>
      rw [List.getElem?_cons_succ] at hentry
      obtain ⟨foundSource, foundValue, hsource, hfoundSlot,
          hfoundWorld, hfoundValue⟩ := ih hentry
      exact ⟨foundSource, foundValue, by simpa using hsource,
        hfoundSlot, hfoundWorld, hfoundValue⟩
  | recSelf _ _ ih =>
    cases i with
    | zero => simp at hentry
    | succ i =>
      rw [List.getElem?_cons_succ] at hentry
      obtain ⟨source, value, hsource, hslot, hworld, hvalue⟩ :=
        ih hentry
      exact ⟨source, value, by simpa using hsource,
        hslot, hworld, hvalue⟩

/-- Looking up the synthetic self entry recovers the statically related
source recursor value; it intentionally has no target runtime slot. -/
theorem EntriesValueGraph.getRecSelf {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {store : Store} {Γ : VEnv}
    {env : List RVal} {entries : List VEntry}
    {sourceEnv : List IxIR0.Value} {roots : List Root}
    {i arity : Nat}
    (h : EntriesValueGraph funRel recSelfRel store Γ env
      entries sourceEnv roots)
    (hentry : entries[i]? = some (.recSelf arity)) :
    ∃ source,
      sourceEnv[i]? = some source ∧ recSelfRel source arity := by
  induction h generalizing i with
  | nil => simp at hentry
  | released _ _ ih =>
    cases i with
    | zero => simp at hentry
    | succ i =>
      rw [List.getElem?_cons_succ] at hentry
      obtain ⟨source, hsource, hself⟩ := ih hentry
      exact ⟨source, by simpa using hsource, hself⟩
  | held _ _ _ _ _ ih =>
    cases i with
    | zero => simp at hentry
    | succ i =>
      rw [List.getElem?_cons_succ] at hentry
      obtain ⟨source, hsource, hself⟩ := ih hentry
      exact ⟨source, by simpa using hsource, hself⟩
  | @recSelf currentArity tail source sources tailRoots
      hself htail ih =>
    cases i with
    | zero =>
      rw [List.getElem?_cons_zero] at hentry
      have harity : currentArity = arity := by simpa using hentry
      subst arity
      exact ⟨source, rfl, hself⟩
    | succ i =>
      rw [List.getElem?_cons_succ] at hentry
      obtain ⟨found, hsource, hfound⟩ := ih hentry
      exact ⟨found, by simpa using hsource, hfound⟩

theorem VEnvValueGraph.vEnvRealizes {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {store : Store} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value} {env : List RVal}
    {roots : List Root}
    (h : VEnvValueGraph funRel recSelfRel store Γ sourceEnv env roots) :
    VEnvRealizes Γ env roots :=
  ⟨h.depth_eq, h.entries.entriesRealize⟩

theorem VEnvValueGraph.rootsGraph {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {store : Store} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value} {env : List RVal}
    {roots : List Root}
    (h : VEnvValueGraph funRel recSelfRel store Γ sourceEnv env roots) :
    ∃ sourceRoots : List (Owned × IxIR0.Value),
      Sim.RootsGraph funRel store sourceRoots roots :=
  h.entries.rootsGraph

theorem VEnvValueGraph.getHeld {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {store : Store} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value} {env : List RVal}
    {roots : List Root} {i abs remaining : Nat} {uses : Uses}
    (h : VEnvValueGraph funRel recSelfRel store Γ sourceEnv env roots)
    (hentry : Γ.entries[i]? = some (.slot abs remaining uses true)) :
    ∃ source value,
      sourceEnv[i]? = some source ∧
      env[Γ.rel abs]? = some value ∧
      HasWorld store (worldOfUses uses) value ∧
      Sim.ValueGraph funRel store source value :=
  h.entries.getHeld hentry

theorem VEnvValueGraph.getRecSelf {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {store : Store} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value} {env : List RVal}
    {roots : List Root} {i arity : Nat}
    (h : VEnvValueGraph funRel recSelfRel store Γ sourceEnv env roots)
    (hentry : Γ.entries[i]? = some (.recSelf arity)) :
    ∃ source,
      sourceEnv[i]? = some source ∧ recSelfRel source arity :=
  h.entries.getRecSelf hentry

/-- Runtime realization of the lowerer's returned value descriptor. -/
inductive AValRealizes (Γ : VEnv) (env : List RVal) :
    AVal → RVal → Prop where
  | slot {abs value} :
      abs < Γ.depth →
      env[Γ.rel abs]? = some value →
      AValRealizes Γ env (.slotA abs) value
  | const {atom value} :
      resolveAtom env atom = .ok value →
      AValRealizes Γ env (.constA atom) value

theorem AValRealizes.resolveAtom {Γ : VEnv} {env : List RVal}
    {av : AVal} {value : RVal} (h : AValRealizes Γ env av value) :
    resolveAtom env (av.toAtom Γ) = .ok value := by
  cases h with
  | slot _ hslot =>
    change (match env[Γ.rel _]? with
      | some found => (Except.ok found : Except Err RVal)
      | none => Except.error (.stuck s!"unbound variable {Γ.rel _}")) =
        Except.ok value
    rw [hslot]
  | const hconst => simpa [AVal.toAtom] using hconst

/-- Returned descriptors depend on a compile-time environment only through
its runtime depth. This is the transport used when a released logical binder
is popped without changing the physical runtime stack. -/
theorem AValRealizes.of_depth_eq {Γ Δ : VEnv} {env : List RVal}
    {av : AVal} {value : RVal} (hdepth : Γ.depth = Δ.depth)
    (h : AValRealizes Γ env av value) :
    AValRealizes Δ env av value := by
  cases h with
  | slot hbound hslot =>
    apply AValRealizes.slot
    · simpa [hdepth] using hbound
    · simpa [VEnv.rel, hdepth] using hslot
  | const hresolve => exact AValRealizes.const hresolve

/-- Returned `AVal`s are either absolute slots or environment-independent
scalar atoms. The lowerer never stores a relative variable in `constA`; this
fact is what lets argument results survive later runtime pushes. -/
inductive AValStable : AVal → Prop where
  | slot {abs : Nat} : AValStable (.slotA abs)
  | lit {literal : IxIR0.Literal} : AValStable (.constA (.lit literal))
  | erased : AValStable (.constA .erased)

/-- Absolute slots whose values must remain resolvable while a later
lowering derivation pushes additional runtime results. -/
def SlotsRealize (Γ : VEnv) (env : List RVal)
    (slots : List (Nat × RVal)) : Prop :=
  ∀ abs value, (abs, value) ∈ slots →
    abs < Γ.depth ∧ env[Γ.rel abs]? = some value

theorem SlotsRealize.nil {Γ : VEnv} {env : List RVal} :
    SlotsRealize Γ env [] := by
  simp [SlotsRealize]

theorem SlotsRealize.mono {Γ : VEnv} {env : List RVal}
    {left right : List (Nat × RVal)} (hsub : ∀ item, item ∈ left → item ∈ right)
    (h : SlotsRealize Γ env right) : SlotsRealize Γ env left := by
  intro abs value hmem
  exact h abs value (hsub _ hmem)

theorem SlotsRealize.append {Γ : VEnv} {env : List RVal}
    {left right : List (Nat × RVal)}
    (hleft : SlotsRealize Γ env left)
    (hright : SlotsRealize Γ env right) :
    SlotsRealize Γ env (left ++ right) := by
  intro abs value hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hleft abs value hmem
  · exact hright abs value hmem

theorem SlotsRealize.left_of_append {Γ : VEnv} {env : List RVal}
    {left right : List (Nat × RVal)}
    (h : SlotsRealize Γ env (left ++ right)) : SlotsRealize Γ env left :=
  h.mono (fun _ hmem => List.mem_append_left right hmem)

theorem SlotsRealize.right_of_append {Γ : VEnv} {env : List RVal}
    {left right : List (Nat × RVal)}
    (h : SlotsRealize Γ env (left ++ right)) : SlotsRealize Γ env right :=
  h.mono (fun _ hmem => List.mem_append_right left hmem)

theorem SlotsRealize.bump {Γ : VEnv} {env : List RVal}
    {slots : List (Nat × RVal)} (pushed : RVal)
    (h : SlotsRealize Γ env slots) :
    SlotsRealize Γ.bump (pushed :: env) slots := by
  intro abs value hmem
  obtain ⟨hbound, hslot⟩ := h abs value hmem
  constructor
  · simpa [VEnv.bump] using Nat.lt_succ_of_lt hbound
  · have hrel : Γ.bump.rel abs = Γ.rel abs + 1 := by
      simp only [VEnv.bump, VEnv.rel]
      omega
    rw [hrel]
    simpa using hslot

theorem SlotsRealize.setEntry {Γ : VEnv} {env : List RVal}
    {slots : List (Nat × RVal)} {i : Nat} {entry : VEntry}
    (h : SlotsRealize Γ env slots) :
    SlotsRealize (Γ.setEntry i entry) env slots := by
  intro abs value hmem
  simpa [VEnv.setEntry, VEnv.rel] using h abs value hmem

/-- Protected absolute slots depend only on the runtime depth, not on the
logical entries tracked alongside it. -/
theorem SlotsRealize.of_depth_eq {Γ Δ : VEnv} {env : List RVal}
    {slots : List (Nat × RVal)} (hdepth : Γ.depth = Δ.depth)
    (h : SlotsRealize Γ env slots) : SlotsRealize Δ env slots := by
  intro abs value hmem
  simpa [VEnv.rel, hdepth] using h abs value hmem

/-- The one absolute slot needed to preserve a returned slot value; stable
constants need no protected runtime position. -/
def aValProtection : AVal → RVal → List (Nat × RVal)
  | .slotA abs, value => [(abs, value)]
  | .constA _, _ => []

theorem AValStable.protection_realized {Γ : VEnv} {env : List RVal}
    {av : AVal} {value : RVal} (stable : AValStable av)
    (h : AValRealizes Γ env av value) :
    SlotsRealize Γ env (aValProtection av value) := by
  cases stable with
  | slot =>
    cases h with
    | slot hbound hslot =>
      intro abs found hmem
      simp only [aValProtection, List.mem_singleton, Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      exact ⟨hbound, hslot⟩
  | lit => exact SlotsRealize.nil
  | erased => exact SlotsRealize.nil

theorem AValStable.realize_of_protection {Γ Δ : VEnv}
    {env env' : List RVal} {av : AVal} {value : RVal}
    (stable : AValStable av) (h : AValRealizes Γ env av value)
    (hslots : SlotsRealize Δ env' (aValProtection av value)) :
    AValRealizes Δ env' av value := by
  cases stable with
  | @slot abs =>
    cases h with
    | slot _ _ =>
      obtain ⟨hbound, hslot⟩ :=
        hslots abs value (by simp [aValProtection])
      exact .slot hbound hslot
  | lit =>
    cases h with
    | const hresolve =>
      simp only [resolveAtom, Except.ok.injEq] at hresolve
      subst value
      exact .const rfl
  | erased =>
    cases h with
    | const hresolve =>
      simp only [resolveAtom, Except.ok.injEq] at hresolve
      subst value
      exact .const rfl

/-- Stable descriptors remain realized after an unrelated runtime push. -/
theorem AValStable.realize_bump {Γ : VEnv} {env : List RVal}
    {av : AVal} {value : RVal} (stable : AValStable av)
    (h : AValRealizes Γ env av value) (pushed : RVal) :
    AValRealizes Γ.bump (pushed :: env) av value := by
  exact stable.realize_of_protection h
    ((stable.protection_realized h).bump pushed)

/-- A stable constant descriptor can realize only an ownership-inert scalar.
This excludes the unstable `.constA (.var _)` shape by construction. -/
theorem AValStable.const_noLocation {Γ : VEnv} {env : List RVal}
    {atom : Atom} {value : RVal}
    (stable : AValStable (.constA atom))
    (h : AValRealizes Γ env (.constA atom) value) :
    rvalLocation? value = none := by
  cases stable with
  | lit =>
    cases h with
    | const hresolve =>
      simp only [resolveAtom, Except.ok.injEq] at hresolve
      subst value
      rfl
  | erased =>
    cases h with
    | const hresolve =>
      simp only [resolveAtom, Except.ok.injEq] at hresolve
      subst value
      rfl

theorem VEnv.rel_bump {Γ : VEnv} {abs : Nat} (habs : abs < Γ.depth) :
    Γ.bump.rel abs = Γ.rel abs + 1 := by
  simp only [VEnv.bump, VEnv.rel]
  omega

/-- Pushing one runtime result preserves realization of every older absolute
slot. The explicit slot bound is what rules out a malformed absolute address
from aliasing the newly pushed head. -/
theorem EntriesRealize.bump {Γ : VEnv} {env : List RVal}
    {entries : List VEntry} {roots : List Root} (value : RVal)
    (h : EntriesRealize Γ env entries roots) :
    EntriesRealize Γ.bump (value :: env) entries roots := by
  induction h with
  | nil => exact .nil
  | released habs _ ih =>
    apply EntriesRealize.released
    · simpa [VEnv.bump] using Nat.lt_succ_of_lt habs
    · exact ih
  | held habs hslot _ ih =>
    apply EntriesRealize.held
    · simpa [VEnv.bump] using Nat.lt_succ_of_lt habs
    · rw [VEnv.rel_bump habs]
      simpa using hslot
    · exact ih
  | recSelf _ ih => exact .recSelf ih

theorem VEnvRealizes.bump {Γ : VEnv} {env : List RVal}
    {roots : List Root} (value : RVal) (h : VEnvRealizes Γ env roots) :
    VEnvRealizes Γ.bump (value :: env) roots := by
  constructor
  · simpa [VEnv.bump] using h.depth_eq
  · exact h.entries.bump value

/-- A runtime push preserves the companion source graph for all older
logical entries. The source evaluator environment is unchanged. -/
theorem EntriesValueGraph.bump {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {store : Store} {Γ : VEnv}
    {env : List RVal} {entries : List VEntry}
    {sourceEnv : List IxIR0.Value} {roots : List Root}
    (value : RVal)
    (h : EntriesValueGraph funRel recSelfRel store Γ env
      entries sourceEnv roots) :
    EntriesValueGraph funRel recSelfRel store Γ.bump (value :: env)
      entries sourceEnv roots := by
  induction h with
  | nil => exact .nil
  | released hbound _ ih =>
    apply EntriesValueGraph.released
    · simpa [VEnv.bump] using Nat.lt_succ_of_lt hbound
    · exact ih
  | held hbound hslot hworld hvalue _ ih =>
    apply EntriesValueGraph.held
    · simpa [VEnv.bump] using Nat.lt_succ_of_lt hbound
    · rw [VEnv.rel_bump hbound]
      simpa using hslot
    · exact hworld
    · exact hvalue
    · exact ih
  | recSelf hself _ ih => exact .recSelf hself ih

theorem VEnvValueGraph.bump {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {store : Store} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value} {env : List RVal}
    {roots : List Root} (value : RVal)
    (h : VEnvValueGraph funRel recSelfRel store Γ sourceEnv env roots) :
    VEnvValueGraph funRel recSelfRel store Γ.bump sourceEnv
      (value :: env) roots := by
  constructor
  · simpa [VEnv.bump] using h.depth_eq
  · exact h.entries.bump value

/-- The semantic entry graph, like `EntriesRealize`, observes the enclosing
`VEnv` only through its physical depth. -/
theorem EntriesValueGraph.of_depth_eq {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {store : Store} {Γ Δ : VEnv}
    {env : List RVal} {entries : List VEntry}
    {sourceEnv : List IxIR0.Value} {roots : List Root}
    (hdepth : Γ.depth = Δ.depth)
    (h : EntriesValueGraph funRel recSelfRel store Γ env
      entries sourceEnv roots) :
    EntriesValueGraph funRel recSelfRel store Δ env
      entries sourceEnv roots := by
  induction h with
  | nil => exact .nil
  | released hbound _ ih =>
    apply EntriesValueGraph.released
    · simpa [hdepth] using hbound
    · exact ih
  | held hbound hslot hworld hvalue _ ih =>
    apply EntriesValueGraph.held
    · simpa [hdepth] using hbound
    · simpa [VEnv.rel, hdepth] using hslot
    · exact hworld
    · exact hvalue
    · exact ih
  | recSelf hself _ ih => exact .recSelf hself ih

/-- Transport the source-environment graph through a store update that keeps
all existing live node shapes. Runtime slots and logical roots are unchanged. -/
theorem EntriesValueGraph.monoStore {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {before after : Store} {Γ : VEnv}
    {env : List RVal} {entries : List VEntry}
    {sourceEnv : List IxIR0.Value} {roots : List Root}
    (hstore : Sim.StoreGraphExtends before after)
    (h : EntriesValueGraph funRel recSelfRel before Γ env
      entries sourceEnv roots) :
    EntriesValueGraph funRel recSelfRel after Γ env
      entries sourceEnv roots := by
  induction h with
  | nil => exact .nil
  | released hbound _ ih => exact .released hbound ih
  | held hbound hslot hworld hvalue _ ih =>
    exact .held hbound hslot (hworld.monoStore hstore)
      (hvalue.monoStore hstore) ih
  | recSelf hself _ ih => exact .recSelf hself ih

theorem VEnvValueGraph.monoStore {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {before after : Store} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value} {env : List RVal}
    {roots : List Root}
    (hstore : Sim.StoreGraphExtends before after)
    (h : VEnvValueGraph funRel recSelfRel before Γ sourceEnv env roots) :
    VEnvValueGraph funRel recSelfRel after Γ sourceEnv env roots :=
  ⟨h.depth_eq, h.entries.monoStore hstore⟩

/-- Destructive store restriction preserves every held environment graph
whose logical root survives in the post-state ownership set. -/
theorem EntriesValueGraph.ofRestricts {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {before after : Store} {Γ : VEnv}
    {env : List RVal} {entries : List VEntry}
    {sourceEnv : List IxIR0.Value} {roots allRoots : List Root}
    (hstore : Sim.StoreGraphRestricts before after)
    (hown : RootOwnership after allRoots)
    (hsubset : ∀ root, root ∈ roots → root ∈ allRoots)
    (h : EntriesValueGraph funRel recSelfRel before Γ env
      entries sourceEnv roots) :
    EntriesValueGraph funRel recSelfRel after Γ env
      entries sourceEnv roots := by
  induction h with
  | nil => exact .nil
  | released hbound _ ih =>
    exact .released hbound (ih hsubset)
  | @held abs remaining uses tail source sources value tailRoots
      hbound hslot _ hvalue htail ih =>
    have hrootLive : HasWorld after (worldOfUses uses) value := by
      apply hown.roots_world ⟨worldOfUses uses, value⟩
      exact hsubset _ (by simp)
    apply EntriesValueGraph.held hbound hslot hrootLive
    · exact hvalue.ofRestricts hstore hown hrootLive
    · exact ih (fun root hmember =>
        hsubset root (by simp [hmember]))
  | recSelf hself _ ih =>
    exact .recSelf hself (ih hsubset)

theorem VEnvValueGraph.ofRestricts {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {before after : Store} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value} {env : List RVal}
    {roots allRoots : List Root}
    (hstore : Sim.StoreGraphRestricts before after)
    (hown : RootOwnership after allRoots)
    (hsubset : ∀ root, root ∈ roots → root ∈ allRoots)
    (h : VEnvValueGraph funRel recSelfRel before Γ sourceEnv env roots) :
    VEnvValueGraph funRel recSelfRel after Γ sourceEnv env roots :=
  ⟨h.depth_eq, h.entries.ofRestricts hstore hown hsubset⟩

/-- Rebuild the enclosing semantic environment after changing one logical
entry while leaving the runtime stack and source environment fixed. -/
theorem VEnvValueGraph.setEntry {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {store : Store} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value} {env : List RVal}
    {roots roots' : List Root} {i : Nat} {entry : VEntry}
    (h : VEnvValueGraph funRel recSelfRel store Γ sourceEnv env roots)
    (hentries : EntriesValueGraph funRel recSelfRel store Γ env
      (Γ.entries.set i entry) sourceEnv roots') :
    VEnvValueGraph funRel recSelfRel store (Γ.setEntry i entry)
      sourceEnv env roots' := by
  constructor
  · simpa [VEnv.setEntry] using h.depth_eq
  · exact hentries.of_depth_eq (by simp [VEnv.setEntry])

/-- Increase only the physical runtime depth of a compile-time environment. -/
def addVEnvDepth (Γ : VEnv) (count : Nat) : VEnv :=
  { Γ with depth := Γ.depth + count }

/-- Repeated runtime pushes preserve all existing logical entries and roots. -/
theorem VEnvRealizes.bumpList {Γ : VEnv} {env : List RVal}
    {roots : List Root} (values : List RVal)
    (h : VEnvRealizes Γ env roots) :
    VEnvRealizes (addVEnvDepth Γ values.length)
      (values.reverse ++ env) roots := by
  induction values generalizing Γ env with
  | nil => simpa [addVEnvDepth] using h
  | cons value values ih =>
    have htail := ih (h.bump value)
    simpa [addVEnvDepth, VEnv.bump, List.reverse_cons,
      List.append_assoc, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using htail

/-- A block of released placeholder slots contributes no logical roots. -/
theorem EntriesRealize.replicateReleased {Γ : VEnv} {env : List RVal}
    (count : Nat) (hbound : 0 < Γ.depth) :
    EntriesRealize Γ env
      (List.replicate count (.slot 0 0 .many false)) [] := by
  induction count with
  | zero => exact EntriesRealize.nil
  | succ count ih =>
    simpa [List.replicate_succ] using
      EntriesRealize.released hbound ih

/-- `EntriesRealize` observes only a `VEnv`'s depth (through `rel`), so it
transports between compile-time environments with the same runtime depth. -/
theorem EntriesRealize.of_depth_eq {Γ Δ : VEnv} {env : List RVal}
    {entries : List VEntry} {roots : List Root} (hdepth : Γ.depth = Δ.depth)
    (h : EntriesRealize Γ env entries roots) :
    EntriesRealize Δ env entries roots := by
  induction h with
  | nil => exact .nil
  | released habs _ ih =>
    apply EntriesRealize.released
    · simpa [hdepth] using habs
    · exact ih
  | held habs hslot _ ih =>
    apply EntriesRealize.held
    · simpa [hdepth] using habs
    · simpa [VEnv.rel, hdepth] using hslot
    · exact ih
  | recSelf _ ih => exact .recSelf ih

/-- Rebuild a realized `VEnv` after changing one source-entry descriptor.
The caller supplies the corresponding entry-list realization. -/
theorem VEnvRealizes.setEntry {Γ : VEnv} {env : List RVal}
    {roots roots' : List Root} {i : Nat} {entry : VEntry}
    (h : VEnvRealizes Γ env roots)
    (hentries : EntriesRealize Γ env (Γ.entries.set i entry) roots') :
    VEnvRealizes (Γ.setEntry i entry) env roots' := by
  constructor
  · simpa [VEnv.setEntry] using h.depth_eq
  · exact hentries.of_depth_eq (by simp [VEnv.setEntry])

/-- Locate a held entry in its exact logical-root list and release it. This
is the proof-relevant state transition for a variable's final (moving) use. -/
theorem EntriesRealize.releaseAt {Γ : VEnv} {env : List RVal}
    {entries : List VEntry} {roots : List Root} {i abs remaining : Nat}
    {uses : Uses} (hreal : EntriesRealize Γ env entries roots)
    (hentry : entries[i]? = some (.slot abs remaining uses true)) :
    ∃ value before after,
      abs < Γ.depth ∧
      env[Γ.rel abs]? = some value ∧
      roots = before ++ ⟨worldOfUses uses, value⟩ :: after ∧
      EntriesRealize Γ env
        (entries.set i (.slot abs 0 uses false)) (before ++ after) := by
  induction hreal generalizing i with
  | nil => simp at hentry
  | @released curAbs curRemaining curUses tail tailRoots habs htail ih =>
    cases i with
    | zero => simp at hentry
    | succ i =>
      rw [List.getElem?_cons_succ] at hentry
      obtain ⟨value, before, after, hbound, hslot, hroots, hout⟩ :=
        ih hentry
      refine ⟨value, before, after, hbound, hslot, hroots, ?_⟩
      simpa using EntriesRealize.released habs hout
  | @held curAbs curRemaining curUses tail tailRoots current
      habs hslot htail ih =>
    cases i with
    | zero =>
      rw [List.getElem?_cons_zero] at hentry
      have heqs : curAbs = abs ∧ curRemaining = remaining ∧
          curUses = uses := by simpa using hentry
      obtain ⟨habsEq, hremainingEq, huses⟩ := heqs
      subst abs
      subst remaining
      subst uses
      refine ⟨current, [], tailRoots, habs, hslot, rfl, ?_⟩
      simpa using EntriesRealize.released habs htail
    | succ i =>
      rw [List.getElem?_cons_succ] at hentry
      obtain ⟨value, before, after, hbound, hselected, hroots, hout⟩ :=
        ih hentry
      refine ⟨value, ⟨worldOfUses curUses, current⟩ :: before, after,
        hbound, hselected, ?_, ?_⟩
      · simp [hroots]
      · simpa using EntriesRealize.held habs hslot hout
  | @recSelf arity tail tailRoots htail ih =>
    cases i with
    | zero => simp at hentry
    | succ i =>
      rw [List.getElem?_cons_succ] at hentry
      obtain ⟨value, before, after, hbound, hslot, hroots, hout⟩ :=
        ih hentry
      refine ⟨value, before, after, hbound, hslot, hroots, ?_⟩
      simpa using EntriesRealize.recSelf hout

/-- Semantic counterpart of `EntriesRealize.releaseAt`. Besides transferring
the exact target root, it preserves the full source environment and exposes
the `ValueGraph` witness for the moved result. -/
theorem EntriesValueGraph.releaseAt {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {store : Store} {Γ : VEnv}
    {env : List RVal} {entries : List VEntry}
    {sourceEnv : List IxIR0.Value} {roots : List Root}
    {i abs remaining : Nat} {uses : Uses}
    (hreal : EntriesValueGraph funRel recSelfRel store Γ env
      entries sourceEnv roots)
    (hentry : entries[i]? = some (.slot abs remaining uses true)) :
    ∃ source value before after,
      sourceEnv[i]? = some source ∧
      abs < Γ.depth ∧
      env[Γ.rel abs]? = some value ∧
      HasWorld store (worldOfUses uses) value ∧
      Sim.ValueGraph funRel store source value ∧
      roots = before ++ ⟨worldOfUses uses, value⟩ :: after ∧
      EntriesValueGraph funRel recSelfRel store Γ env
        (entries.set i (.slot abs 0 uses false)) sourceEnv
        (before ++ after) := by
  induction hreal generalizing i with
  | nil => simp at hentry
  | @released curAbs curRemaining curUses tail currentSource sources
      tailRoots hbound htail ih =>
    cases i with
    | zero => simp at hentry
    | succ i =>
      rw [List.getElem?_cons_succ] at hentry
      obtain ⟨source, value, before, after, hsource, habs, hslot,
          hworld, hvalue, hroots, hout⟩ := ih hentry
      refine ⟨source, value, before, after, by simpa using hsource,
        habs, hslot, hworld, hvalue, hroots, ?_⟩
      simpa using EntriesValueGraph.released hbound hout
  | @held curAbs curRemaining curUses tail currentSource sources
      currentValue tailRoots hbound hslot hworld hvalue htail ih =>
    cases i with
    | zero =>
      rw [List.getElem?_cons_zero] at hentry
      have heqs : curAbs = abs ∧ curRemaining = remaining ∧
          curUses = uses := by simpa using hentry
      obtain ⟨rfl, rfl, rfl⟩ := heqs
      exact ⟨currentSource, currentValue, [], tailRoots, rfl,
        hbound, hslot, hworld, hvalue, rfl,
        by simpa using EntriesValueGraph.released hbound htail⟩
    | succ i =>
      rw [List.getElem?_cons_succ] at hentry
      obtain ⟨source, value, before, after, hsource, habs,
          hselected, hfoundWorld, hfoundValue, hroots, hout⟩ :=
        ih hentry
      refine ⟨source, value,
        ⟨worldOfUses curUses, currentValue⟩ :: before, after,
        by simpa using hsource, habs, hselected, hfoundWorld,
        hfoundValue, ?_, ?_⟩
      · simp [hroots]
      · simpa using EntriesValueGraph.held hbound hslot hworld hvalue hout
  | @recSelf arity tail currentSource sources tailRoots hself htail ih =>
    cases i with
    | zero => simp at hentry
    | succ i =>
      rw [List.getElem?_cons_succ] at hentry
      obtain ⟨source, value, before, after, hsource, habs, hslot,
          hworld, hvalue, hroots, hout⟩ := ih hentry
      refine ⟨source, value, before, after, by simpa using hsource,
        habs, hslot, hworld, hvalue, hroots, ?_⟩
      simpa using EntriesValueGraph.recSelf hself hout

/-- Activate a released entry at a newly available absolute slot. The new
owner is inserted at the entry's structural position in the exact root list;
this is the proof-side transition for retaining a borrowed case field. -/
theorem EntriesRealize.holdAt {Γ : VEnv} {env : List RVal}
    {entries : List VEntry} {roots : List Root}
    {i oldAbs oldRemaining newAbs newRemaining : Nat} {uses : Uses}
    {value : RVal}
    (hreal : EntriesRealize Γ env entries roots)
    (hentry : entries[i]? =
      some (.slot oldAbs oldRemaining uses false))
    (hbound : newAbs < Γ.depth)
    (hslot : env[Γ.rel newAbs]? = some value) :
    ∃ before after,
      roots = before ++ after ∧
      EntriesRealize Γ env
        (entries.set i (.slot newAbs newRemaining uses true))
        (before ++ ⟨worldOfUses uses, value⟩ :: after) := by
  induction hreal generalizing i with
  | nil => simp at hentry
  | @released curAbs curRemaining curUses tail tailRoots habs htail ih =>
    cases i with
    | zero =>
      refine ⟨[], tailRoots, rfl, ?_⟩
      simpa using EntriesRealize.held hbound hslot htail
    | succ i =>
      rw [List.getElem?_cons_succ] at hentry
      obtain ⟨before, after, hroots, hout⟩ :=
        ih hentry
      refine ⟨before, after, hroots, ?_⟩
      simpa using EntriesRealize.released habs hout
  | @held curAbs curRemaining curUses tail tailRoots current
      habs hcurrent htail ih =>
    cases i with
    | zero => simp at hentry
    | succ i =>
      rw [List.getElem?_cons_succ] at hentry
      obtain ⟨before, after, hroots, hout⟩ :=
        ih hentry
      refine ⟨⟨worldOfUses curUses, current⟩ :: before, after, ?_, ?_⟩
      · simp [hroots]
      · simpa using EntriesRealize.held habs hcurrent hout
  | @recSelf arity tail tailRoots htail ih =>
    cases i with
    | zero => simp at hentry
    | succ i =>
      rw [List.getElem?_cons_succ] at hentry
      obtain ⟨before, after, hroots, hout⟩ :=
        ih hentry
      refine ⟨before, after, hroots, ?_⟩
      simpa using EntriesRealize.recSelf hout

/-- Update the remaining-use counter of a held entry without changing its
existing root. The selected value and its root membership are exposed for
the following shared retain operation. -/
theorem EntriesRealize.updateHeldAt {Γ : VEnv} {env : List RVal}
    {entries : List VEntry} {roots : List Root} {i abs remaining : Nat}
    {uses : Uses} (newRemaining : Nat)
    (hreal : EntriesRealize Γ env entries roots)
    (hentry : entries[i]? = some (.slot abs remaining uses true)) :
    ∃ value,
      abs < Γ.depth ∧
      env[Γ.rel abs]? = some value ∧
      ⟨worldOfUses uses, value⟩ ∈ roots ∧
      EntriesRealize Γ env
        (entries.set i (.slot abs newRemaining uses true)) roots := by
  induction hreal generalizing i with
  | nil => simp at hentry
  | @released curAbs curRemaining curUses tail tailRoots habs htail ih =>
    cases i with
    | zero => simp at hentry
    | succ i =>
      rw [List.getElem?_cons_succ] at hentry
      obtain ⟨value, hbound, hslot, hmem, hout⟩ := ih hentry
      refine ⟨value, hbound, hslot, hmem, ?_⟩
      simpa using EntriesRealize.released habs hout
  | @held curAbs curRemaining curUses tail tailRoots current
      habs hslot htail ih =>
    cases i with
    | zero =>
      rw [List.getElem?_cons_zero] at hentry
      have heqs : curAbs = abs ∧ curRemaining = remaining ∧
          curUses = uses := by simpa using hentry
      obtain ⟨habsEq, hremainingEq, huses⟩ := heqs
      subst abs
      subst remaining
      subst uses
      refine ⟨current, habs, hslot, by simp, ?_⟩
      simpa using EntriesRealize.held habs hslot htail
    | succ i =>
      rw [List.getElem?_cons_succ] at hentry
      obtain ⟨value, hbound, hselected, hmem, hout⟩ := ih hentry
      refine ⟨value, hbound, hselected, List.mem_cons_of_mem _ hmem, ?_⟩
      simpa using EntriesRealize.held habs hslot hout
  | @recSelf arity tail tailRoots htail ih =>
    cases i with
    | zero => simp at hentry
    | succ i =>
      rw [List.getElem?_cons_succ] at hentry
      obtain ⟨value, hbound, hslot, hmem, hout⟩ := ih hentry
      refine ⟨value, hbound, hslot, hmem, ?_⟩
      simpa using EntriesRealize.recSelf hout

/-- Semantic held-entry update. The target root stays in place while the
compiler-side use counter changes, and the selected source/value graph is
exposed for a following retain. -/
theorem EntriesValueGraph.updateHeldAt {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {store : Store} {Γ : VEnv}
    {env : List RVal} {entries : List VEntry}
    {sourceEnv : List IxIR0.Value} {roots : List Root}
    {i abs remaining : Nat} {uses : Uses} (newRemaining : Nat)
    (hreal : EntriesValueGraph funRel recSelfRel store Γ env
      entries sourceEnv roots)
    (hentry : entries[i]? = some (.slot abs remaining uses true)) :
    ∃ source value,
      sourceEnv[i]? = some source ∧
      abs < Γ.depth ∧
      env[Γ.rel abs]? = some value ∧
      HasWorld store (worldOfUses uses) value ∧
      Sim.ValueGraph funRel store source value ∧
      ⟨worldOfUses uses, value⟩ ∈ roots ∧
      EntriesValueGraph funRel recSelfRel store Γ env
        (entries.set i (.slot abs newRemaining uses true))
        sourceEnv roots := by
  induction hreal generalizing i with
  | nil => simp at hentry
  | @released curAbs curRemaining curUses tail currentSource sources
      tailRoots hbound htail ih =>
    cases i with
    | zero => simp at hentry
    | succ i =>
      rw [List.getElem?_cons_succ] at hentry
      obtain ⟨source, value, hsource, habs, hslot, hworld, hvalue,
          hmem, hout⟩ := ih hentry
      refine ⟨source, value, by simpa using hsource, habs, hslot,
        hworld, hvalue, hmem, ?_⟩
      simpa using EntriesValueGraph.released hbound hout
  | @held curAbs curRemaining curUses tail currentSource sources
      currentValue tailRoots hbound hslot hworld hvalue htail ih =>
    cases i with
    | zero =>
      rw [List.getElem?_cons_zero] at hentry
      have heqs : curAbs = abs ∧ curRemaining = remaining ∧
          curUses = uses := by simpa using hentry
      obtain ⟨rfl, rfl, rfl⟩ := heqs
      exact ⟨currentSource, currentValue, rfl, hbound, hslot,
        hworld, hvalue, by simp,
        (by
          simpa using
            (EntriesValueGraph.held hbound hslot hworld hvalue htail))⟩
    | succ i =>
      rw [List.getElem?_cons_succ] at hentry
      obtain ⟨source, value, hsource, habs, hselected, hfoundWorld,
          hfoundValue, hmem, hout⟩ := ih hentry
      refine ⟨source, value, by simpa using hsource, habs, hselected,
        hfoundWorld, hfoundValue, List.mem_cons_of_mem _ hmem, ?_⟩
      simpa using EntriesValueGraph.held hbound hslot hworld hvalue hout
  | @recSelf arity tail currentSource sources tailRoots hself htail ih =>
    cases i with
    | zero => simp at hentry
    | succ i =>
      rw [List.getElem?_cons_succ] at hentry
      obtain ⟨source, value, hsource, habs, hslot, hworld, hvalue,
          hmem, hout⟩ := ih hentry
      refine ⟨source, value, by simpa using hsource, habs, hslot,
        hworld, hvalue, hmem, ?_⟩
      simpa using EntriesValueGraph.recSelf hself hout

private theorem perm_extract_root (root : Root) (before after rest : List Root) :
    ((before ++ root :: after) ++ rest).Perm
      (root :: (before ++ after) ++ rest) := by
  induction before with
  | nil => rfl
  | cons head before ih =>
    simp only [List.cons_append]
    exact (ih.cons head).trans (List.Perm.swap root head _)

private theorem perm_extract_root_front
    (root : Root) (before rest : List Root) :
    (before ++ root :: rest).Perm (root :: before ++ rest) := by
  induction before with
  | nil => rfl
  | cons head before ih =>
    simp only [List.cons_append]
    exact (ih.cons head).trans (List.Perm.swap root head _)

/-- Compile-time environments in which no source slot still owns a value.
This is the condition needed when a function closes its emitter with `ret`. -/
inductive EntriesReleased : List VEntry → Prop where
  | nil : EntriesReleased []
  | slot {abs remaining uses entries} :
      EntriesReleased entries →
      EntriesReleased (.slot abs remaining uses false :: entries)
  | recSelf {arity entries} :
      EntriesReleased entries →
      EntriesReleased (.recSelf arity :: entries)

/-- The structural fact needed at a let boundary: the installed source
binder is still the first logical entry and no longer owns its slot. -/
def FirstEntryReleased (Γ : VEnv) : Prop :=
  ∃ abs remaining uses tail,
    Γ.entries = .slot abs remaining uses false :: tail

/-- Reachable let-body entry shape: the first logical entry carries exactly
the syntactic use count of the body and is held precisely when that count is
nonzero. This is the compile-state fact needed to justify the lowerer's
post-body `VEnv.pop`. -/
def FirstEntryTracks (Γ : VEnv) (uses : Uses) (remaining : Nat) : Prop :=
  ∃ abs tail,
    Γ.entries =
      .slot abs remaining uses (remaining != 0) :: tail

/-- Removing a released first logical entry preserves the exact environment
roots. `VEnv.pop` changes no runtime depth or physical stack position. -/
theorem VEnvRealizes.pop_firstReleased {Γ : VEnv} {env : List RVal}
    {roots : List Root} (hfirst : FirstEntryReleased Γ)
    (h : VEnvRealizes Γ env roots) :
    VEnvRealizes Γ.pop env roots := by
  obtain ⟨abs, remaining, uses, tail, hentries⟩ := hfirst
  refine ⟨by simpa [VEnv.pop] using h.depth_eq, ?_⟩
  have hreal := h.entries
  rw [hentries] at hreal
  cases hreal with
  | released _ htail =>
    have htransport := htail.of_depth_eq (Γ := Γ) (Δ := Γ.pop)
      (by simp [VEnv.pop])
    simpa [VEnv.pop, hentries] using htransport

/-- Semantic let-pop counterpart: removing the released leading logical
binder removes exactly the leading source-environment value. Runtime slots,
roots, and all remaining value graphs are unchanged. -/
theorem VEnvValueGraph.pop_firstReleased
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {store : Store} {Γ : VEnv} {source : IxIR0.Value}
    {sourceEnv : List IxIR0.Value} {env : List RVal}
    {roots : List Root} (hfirst : FirstEntryReleased Γ)
    (h : VEnvValueGraph funRel recSelfRel store Γ
      (source :: sourceEnv) env roots) :
    VEnvValueGraph funRel recSelfRel store Γ.pop sourceEnv env roots := by
  obtain ⟨abs, remaining, uses, tail, hentries⟩ := hfirst
  refine ⟨by simpa [VEnv.pop] using h.depth_eq, ?_⟩
  have hreal := h.entries
  rw [hentries] at hreal
  cases hreal with
  | released _ htail =>
    have htransport := htail.of_depth_eq (Γ := Γ) (Δ := Γ.pop)
      (by simp [VEnv.pop])
    simpa [VEnv.pop, hentries] using htransport

theorem EntriesRealize.eq_nil_of_released {Γ : VEnv} {env : List RVal} :
    ∀ {entries roots}, EntriesReleased entries →
      EntriesRealize Γ env entries roots → roots = [] := by
  intro entries roots hreleased hrealize
  induction hreleased with
  | nil => cases hrealize; rfl
  | slot _ ih =>
    cases hrealize with
    | released _ htail => exact ih htail
  | recSelf _ ih =>
    cases hrealize with
    | recSelf htail => exact ih htail

/-! ## Hoare-style continuation semantics -/

abbrev StatePred := Store → List RVal → Prop
abbrev ResultPred := Store → RVal → Prop

/-- Partial-correctness judgment for an IxIR₁ code sequence. -/
def CodeOwns (ctx : Ctx) (cur : FnDef) (pre : StatePred)
    (post : ResultPred) (code : Code) : Prop :=
  ∀ {fuel store env store' value}, pre store env →
    runCode ctx fuel cur store env code = .ok (store', value) →
    post store' value

/-- An emitter is sound from `pre` to `mid` when it transports every
ownership-valid continuation under `mid` back to one under `pre`. -/
def EmitSound (ctx : Ctx) (cur : FnDef) (emit : Emit)
    (pre mid : StatePred) : Prop :=
  ∀ (post : ResultPred) (code : Code),
    CodeOwns ctx cur mid post code →
    CodeOwns ctx cur pre post (emit code)

/-- One operation's state-transformer judgment. The operation result is
prepended to the runtime environment exactly as `Code.letOp` specifies. -/
def OpSound (ctx : Ctx) (cur : FnDef) (op : Op)
    (pre post : StatePred) : Prop :=
  ∀ {fuel store env store' value}, pre store env →
    runOp ctx fuel cur store env op = .ok (store', value) →
    post store' (value :: env)

/-- `CodeOwns` restricted to evaluator indices through `limit`. The outer
`runCode` step lowers every operation and continuation to a strictly smaller
index, so this judgment can cover the exact index being sealed while consuming
only operation/callee contracts below it. -/
def CodeOwnsBelow (ctx : Ctx) (cur : FnDef) (limit : Nat)
    (pre : StatePred) (post : ResultPred) (code : Code) : Prop :=
  ∀ {fuel store env store' value}, fuel ≤ limit → pre store env →
    runCode ctx fuel cur store env code = .ok (store', value) →
    post store' value

/-- Fuel-bounded emitter soundness. Keeping the same
continuation-transformer shape as `EmitSound` preserves composition. -/
def EmitSoundBelow (ctx : Ctx) (cur : FnDef) (limit : Nat)
    (emit : Emit) (pre mid : StatePred) : Prop :=
  ∀ bound, bound ≤ limit → ∀ (post : ResultPred) (code : Code),
    CodeOwnsBelow ctx cur bound mid post code →
    CodeOwnsBelow ctx cur bound pre post (emit code)

/-- One operation's state-transformer judgment below a fuel bound. -/
def OpSoundBelow (ctx : Ctx) (cur : FnDef) (limit : Nat) (op : Op)
    (pre post : StatePred) : Prop :=
  ∀ {fuel store env store' value}, fuel < limit → pre store env →
    runOp ctx fuel cur store env op = .ok (store', value) →
    post store' (value :: env)

private theorem bindOk {error α β : Type} (value : α)
    (next : α → Except error β) :
    (Except.ok value >>= next) = next value := rfl

private theorem estateBindRun {error state α β : Type}
    (action : EStateM error state α) (next : α → EStateM error state β)
    (initial : state) :
    (action >>= next).run initial =
      match action.run initial with
      | .ok value nextState => (next value).run nextState
      | .error err nextState => .error err nextState := rfl

private theorem estatePureRun {error state α : Type}
    (value : α) (initial : state) :
    (pure value : EStateM error state α).run initial =
      .ok value initial := rfl

private theorem estateThrowRun_not_ok {error state α : Type}
    {err : error} {initial final : state} {value : α}
    (h : (throw err : EStateM error state α).run initial =
      .ok value final) : False := by
  change EStateM.Result.error err initial = .ok value final at h
  contradiction

/-- A successful declared-result world check certifies exact agreement and
leaves the lowering state unchanged. -/
theorem requireResultWorld_run_ok_inv
    {actual demand : Owned} {initial final : LowSt}
    (hrun : (requireResultWorld actual demand).run initial =
      .ok () final) : actual = demand ∧ initial = final := by
  have hssEq : (Owned.shared == Owned.shared) = true := by decide
  have huuEq : (Owned.unique == Owned.unique) = true := by decide
  have hsuEq : (Owned.shared == Owned.unique) = false := by decide
  have husEq : (Owned.unique == Owned.shared) = false := by decide
  cases actual <;> cases demand <;>
    simp [requireResultWorld, hssEq, huuEq, hsuEq, husEq] at hrun ⊢
  all_goals assumption

/-- Successful state-monad bind inversion, used to recover the two recursive
compiler runs from a successful `do` block. -/
private theorem estateBindRun_ok_inv {error state α β : Type}
    {action : EStateM error state α} {next : α → EStateM error state β}
    {initial final : state} {result : β}
    (h : (action >>= next).run initial = .ok result final) :
    ∃ value middle,
      action.run initial = .ok value middle ∧
      (next value).run middle = .ok result final := by
  rw [estateBindRun] at h
  cases haction : action.run initial with
  | ok value middle =>
    rw [haction] at h
    exact ⟨value, middle, rfl, h⟩
  | error err middle =>
    rw [haction] at h
    contradiction

theorem EmitSound.id {ctx : Ctx} {cur : FnDef} {pre : StatePred} :
    EmitSound ctx cur (_root_.id : Emit) pre pre := by
  intro post code hcode fuel store env store' value hpre hrun
  exact hcode hpre hrun

theorem EmitSound.strengthen {ctx : Ctx} {cur : FnDef}
    {pre mid : StatePred}
    (himp : ∀ {store env}, pre store env → mid store env) :
    EmitSound ctx cur (_root_.id : Emit) pre mid := by
  intro post code hcode fuel store env store' value hpre hrun
  exact hcode (himp hpre) hrun

theorem EmitSound.comp {ctx : Ctx} {cur : FnDef} {emit₁ emit₂ : Emit}
    {pre mid post : StatePred}
    (h₁ : EmitSound ctx cur emit₁ pre mid)
    (h₂ : EmitSound ctx cur emit₂ mid post) :
    EmitSound ctx cur (emit₁ ∘ emit₂) pre post := by
  intro result code hcode
  exact h₁ result (emit₂ code) (h₂ result code hcode)

/-- An emitter whose precondition no execution can satisfy transports every
postcondition. Vacuous compiler branches use this to skip the remainder of
their emitted sequence once one operation is known to fail. -/
theorem EmitSound.ofFalse {ctx : Ctx} {cur : FnDef} {emit : Emit}
    {mid : StatePred} :
    EmitSound ctx cur emit (fun _ _ => False) mid := by
  intro post code hcode fuel store env store' value hpre hrun
  exact hpre.elim

/-- An emitter proved to reach an unsatisfiable midpoint reaches any
midpoint. This is the terminal step of a vacuous branch, where the emitted
code is exactly the prefix already shown to fail. -/
theorem EmitSound.ofFalseMid {ctx : Ctx} {cur : FnDef} {emit : Emit}
    {pre mid : StatePred}
    (hfalse : EmitSound ctx cur emit pre (fun _ _ => False)) :
    EmitSound ctx cur emit pre mid := by
  intro post code _
  exact hfalse post code (fun hpre _ => hpre.elim)

/-- Unbounded code ownership restricts to any fuel prefix. -/
theorem CodeOwns.below {ctx : Ctx} {cur : FnDef} {pre : StatePred}
    {post : ResultPred} {code : Code}
    (hcode : CodeOwns ctx cur pre post code) (limit : Nat) :
    CodeOwnsBelow ctx cur limit pre post code := by
  intro fuel store env store' value _ hpre hrun
  exact hcode hpre hrun

/-- Unbounded operation soundness restricts to any fuel prefix. -/
theorem OpSound.below {ctx : Ctx} {cur : FnDef} {op : Op}
    {pre post : StatePred}
    (hop : OpSound ctx cur op pre post) (limit : Nat) :
    OpSoundBelow ctx cur limit op pre post := by
  intro fuel store env store' value _ hpre hrun
  exact hop hpre hrun

theorem EmitSoundBelow.id {ctx : Ctx} {cur : FnDef} {limit : Nat}
    {pre : StatePred} :
    EmitSoundBelow ctx cur limit (_root_.id : Emit) pre pre := by
  intro bound _ post code hcode
  exact hcode

theorem EmitSoundBelow.strengthen {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {pre mid : StatePred}
    (himp : ∀ {store env}, pre store env → mid store env) :
    EmitSoundBelow ctx cur limit (_root_.id : Emit) pre mid := by
  intro bound _ post code hcode fuel store env store' value hfuel hpre hrun
  exact hcode hfuel (himp hpre) hrun

theorem EmitSoundBelow.comp {ctx : Ctx} {cur : FnDef} {limit : Nat}
    {emit₁ emit₂ : Emit} {pre mid post : StatePred}
    (h₁ : EmitSoundBelow ctx cur limit emit₁ pre mid)
    (h₂ : EmitSoundBelow ctx cur limit emit₂ mid post) :
    EmitSoundBelow ctx cur limit (emit₁ ∘ emit₂) pre post := by
  intro bound hbound result code hcode
  exact h₁ bound hbound result (emit₂ code)
    (h₂ bound hbound result code hcode)

/-- Closing a bounded emitter proof at every evaluator limit recovers the
unbounded judgment. This is the bridge used to keep one bounded compiler
induction and expose the legacy exact interface only at its boundary. -/
theorem EmitSound.of_below {ctx : Ctx} {cur : FnDef} {emit : Emit}
    {pre mid : StatePred}
    (hsound : ∀ limit, EmitSoundBelow ctx cur limit emit pre mid) :
    EmitSound ctx cur emit pre mid := by
  intro post code hcode fuel store env store' value hpre hrun
  have hbounded : CodeOwnsBelow ctx cur fuel mid post code :=
    hcode.below fuel
  exact hsound fuel fuel (Nat.le_refl fuel) post code hbounded
    (Nat.le_refl fuel) hpre hrun

/-- Lift one bounded operation through `Code.letOp`. Both the operation and
its continuation run at the predecessor of the enclosing code fuel, hence
remain below the same bound. -/
theorem OpSoundBelow.emit {ctx : Ctx} {cur : FnDef} {limit : Nat}
    {op : Op} {pre post : StatePred}
    (hop : OpSoundBelow ctx cur limit op pre post) :
    EmitSoundBelow ctx cur limit (emitOp op) pre post := by
  intro bound hbound result code hcode fuel store env finalStore finalValue
    hfuel hpre hrun
  cases fuel with
  | zero => simp [runCode] at hrun
  | succ fuel =>
    have hinner : fuel < bound :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self fuel) hfuel
    have hinnerLimit : fuel < limit := Nat.lt_of_lt_of_le hinner hbound
    rw [runCode.eq_def] at hrun
    dsimp only [emitOp] at hrun
    cases hopEval : runOp ctx fuel cur store env op with
    | error err =>
      rw [hopEval] at hrun
      change (Except.error err : Except Err (Store × RVal)) =
        .ok (finalStore, finalValue) at hrun
      contradiction
    | ok out =>
      rcases out with ⟨store', value⟩
      rw [hopEval] at hrun
      change runCode ctx fuel cur store' (value :: env) code =
        .ok (finalStore, finalValue) at hrun
      exact hcode (Nat.le_of_lt hinner) (hop hinnerLimit hpre hopEval) hrun

theorem OpSound.emit {ctx : Ctx} {cur : FnDef} {op : Op}
    {pre post : StatePred} (hop : OpSound ctx cur op pre post) :
    EmitSound ctx cur (emitOp op) pre post := by
  intro result code hcode fuel store env finalStore finalValue hpre hrun
  cases fuel with
  | zero => simp [runCode] at hrun
  | succ fuel =>
    rw [runCode.eq_def] at hrun
    dsimp only [emitOp] at hrun
    cases hopEval : runOp ctx fuel cur store env op with
    | error err =>
      rw [hopEval] at hrun
      change (Except.error err : Except Err (Store × RVal)) =
        .ok (finalStore, finalValue) at hrun
      contradiction
    | ok out =>
      rcases out with ⟨store', value⟩
      rw [hopEval] at hrun
      change runCode ctx fuel cur store' (value :: env) code =
        .ok (finalStore, finalValue) at hrun
      exact hcode (hop hpre hopEval) hrun

/-! ## Emitter rules backed by the exact evaluator interfaces -/

/-- A state after one operation has pushed a physical environment slot while
leaving the stated logical roots. The pushed value itself is ownership-inert
or has already been accounted for elsewhere. -/
def OwnsAfterPush (frame : List RVal → Prop) (roots : List Root) : StatePred :=
  fun store env' => ∃ value env,
    env' = value :: env ∧ frame env ∧ RootOwnership store roots

/-- A stronger pushed-state predicate in which the new value is exactly one
owned root. -/
def OwnsPushedRoot (frame : List RVal → Prop) (world : Owned)
    (rest : List Root) : StatePred :=
  fun store env' => ∃ value env,
    env' = value :: env ∧ frame env ∧
    RootOwnership store (⟨world, value⟩ :: rest)

/-- The pushed operation result is a borrow, not a new owner. -/
def BorrowsPushed (frame : List RVal → Prop) (world : Owned)
    (roots : List Root) : StatePred :=
  fun store env' => ∃ value env,
    env' = value :: env ∧ frame env ∧ HasWorld store world value ∧
    RootOwnership store roots

private theorem emit_pure_scalar_owned_at {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {frame : List RVal → Prop} {atom : Atom}
    {value : RVal} {world : Owned} {rest : List Root}
    (hnone : rvalLocation? value = none) :
    EmitSoundBelow ctx cur limit (emitOp (.pure atom))
      (fun store env => frame env ∧ resolveAtom env atom = .ok value ∧
        RootOwnership store rest)
      (OwnsPushedRoot frame world rest) := by
  apply OpSoundBelow.emit
  intro fuel store env store' result _ hpre hrun
  obtain ⟨hframe, hresolve, hown⟩ := hpre
  cases fuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    have hop := runOp_pure_scalar_owned (ctx := ctx) (cur := cur)
      (fuel := fuel) (world := world) (roots := rest)
      hresolve hnone hown
    have hpair : (store, value) = (store', result) :=
      Except.ok.inj (hop.1.symm.trans hrun)
    cases hpair
    exact ⟨value, env, rfl, hframe, hop.2⟩

theorem emit_pure_scalar_owned {ctx : Ctx} {cur : FnDef}
    {frame : List RVal → Prop} {atom : Atom} {value : RVal}
    {world : Owned} {rest : List Root}
    (hnone : rvalLocation? value = none) :
    EmitSound ctx cur (emitOp (.pure atom))
      (fun store env => frame env ∧ resolveAtom env atom = .ok value ∧
        RootOwnership store rest)
      (OwnsPushedRoot frame world rest) := by
  exact EmitSound.of_below fun limit =>
    emit_pure_scalar_owned_at (limit := limit) hnone

/-- Fuel-bounded scalar materialization. -/
theorem emit_pure_scalar_owned_below {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {frame : List RVal → Prop} {atom : Atom}
    {value : RVal} {world : Owned} {rest : List Root}
    (hnone : rvalLocation? value = none) :
    EmitSoundBelow ctx cur limit (emitOp (.pure atom))
      (fun store env => frame env ∧ resolveAtom env atom = .ok value ∧
        RootOwnership store rest)
      (OwnsPushedRoot frame world rest) := by
  exact emit_pure_scalar_owned_at hnone

private theorem emit_alloc_owned_at {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {frame : List RVal → Prop} {world : Owned}
    {cid : CtorId} {atoms : Array Atom} {values : List RVal}
    {rest : List Root} :
    EmitSoundBelow ctx cur limit (emitOp (.alloc world cid atoms))
      (fun store env => frame env ∧ resolveAtoms env atoms = .ok values ∧
        RootOwnership store (rootsFor world values ++ rest))
      (OwnsPushedRoot frame world rest) := by
  apply OpSoundBelow.emit
  intro fuel store env store' result _ hpre hrun
  obtain ⟨hframe, hresolve, hown⟩ := hpre
  cases fuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    have hop := runOp_alloc_owned (ctx := ctx) (cur := cur)
      (fuel := fuel) (cid := cid) (args := atoms) (values := values)
      (rest := rest) hresolve hown
    have hpair :
        ((store.allocNode world (.ctorN cid values.toArray)).1,
          .loc (store.allocNode world (.ctorN cid values.toArray)).2) =
        (store', result) := by
      exact Except.ok.inj (hop.1.symm.trans hrun)
    have hstore := congrArg Prod.fst hpair
    have hresult := congrArg Prod.snd hpair
    dsimp only at hstore hresult
    subst store'
    subst result
    exact ⟨.loc (store.allocNode world (.ctorN cid values.toArray)).2,
      env, rfl, hframe, hop.2⟩

theorem emit_alloc_owned {ctx : Ctx} {cur : FnDef}
    {frame : List RVal → Prop} {world : Owned} {cid : CtorId}
    {atoms : Array Atom} {values : List RVal} {rest : List Root} :
    EmitSound ctx cur (emitOp (.alloc world cid atoms))
      (fun store env => frame env ∧ resolveAtoms env atoms = .ok values ∧
        RootOwnership store (rootsFor world values ++ rest))
      (OwnsPushedRoot frame world rest) := by
  exact EmitSound.of_below fun limit =>
    emit_alloc_owned_at (limit := limit)

/-- Fuel-bounded constructor allocation. -/
theorem emit_alloc_owned_below {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {frame : List RVal → Prop} {world : Owned}
    {cid : CtorId} {atoms : Array Atom} {values : List RVal}
    {rest : List Root} :
    EmitSoundBelow ctx cur limit (emitOp (.alloc world cid atoms))
      (fun store env => frame env ∧ resolveAtoms env atoms = .ok values ∧
        RootOwnership store (rootsFor world values ++ rest))
      (OwnsPushedRoot frame world rest) := by
  exact emit_alloc_owned_at

/-- Partial application packages a shared argument prefix into one fresh
shared pap root. -/
private theorem emit_papp_owned_at {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {f : Ixon.Address} {d : Decl}
    {frame : List RVal → Prop} {atoms : Array Atom}
    {values : List RVal} {rest : List Root}
    (hdecl : ctx.decls f = some d)
    (hunder : values.length < declArity d) :
    EmitSoundBelow ctx cur limit (emitOp (.papp f atoms))
      (fun store env => frame env ∧ resolveAtoms env atoms = .ok values ∧
        RootOwnership store (rootsFor .shared values ++ rest))
      (OwnsPushedRoot frame .shared rest) := by
  apply OpSoundBelow.emit
  intro fuel store env store' result _ hpre hrun
  obtain ⟨hframe, hresolve, hown⟩ := hpre
  cases fuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    have hop := runOp_papp_owned (ctx := ctx) (cur := cur)
      (fuel := fuel) hresolve hdecl hunder hown
    have hpair :
        ((store.allocNode .shared
          (.papN f (declArity d) values.toArray)).1,
          .loc (store.allocNode .shared
            (.papN f (declArity d) values.toArray)).2) =
        (store', result) := Except.ok.inj (hop.1.symm.trans hrun)
    cases hpair
    exact ⟨.loc (store.allocNode .shared
      (.papN f (declArity d) values.toArray)).2,
      env, rfl, hframe, hop.2⟩

theorem emit_papp_owned {ctx : Ctx} {cur : FnDef} {f : Ixon.Address}
    {d : Decl} {frame : List RVal → Prop} {atoms : Array Atom}
    {values : List RVal} {rest : List Root}
    (hdecl : ctx.decls f = some d)
    (hunder : values.length < declArity d) :
    EmitSound ctx cur (emitOp (.papp f atoms))
      (fun store env => frame env ∧ resolveAtoms env atoms = .ok values ∧
        RootOwnership store (rootsFor .shared values ++ rest))
      (OwnsPushedRoot frame .shared rest) := by
  exact EmitSound.of_below fun limit =>
    emit_papp_owned_at (limit := limit) hdecl hunder

/-- Fuel-bounded partial-application allocation. -/
theorem emit_papp_owned_below {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {f : Ixon.Address} {d : Decl}
    {frame : List RVal → Prop} {atoms : Array Atom}
    {values : List RVal} {rest : List Root}
    (hdecl : ctx.decls f = some d)
    (hunder : values.length < declArity d) :
    EmitSoundBelow ctx cur limit (emitOp (.papp f atoms))
      (fun store env => frame env ∧ resolveAtoms env atoms = .ok values ∧
        RootOwnership store (rootsFor .shared values ++ rest))
      (OwnsPushedRoot frame .shared rest) := by
  exact emit_papp_owned_at hdecl hunder

private theorem emit_retain_borrowed_at {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {frame : List RVal → Prop} {atom : Atom}
    {value : RVal} {rest : List Root} :
    EmitSoundBelow ctx cur limit (emitOp (.dup atom))
      (fun store env => frame env ∧ resolveAtom env atom = .ok value ∧
        HasWorld store .shared value ∧ RootOwnership store rest)
      (OwnsPushedRoot frame .shared rest) := by
  apply OpSoundBelow.emit
  intro fuel store env store' result _ hpre hrun
  obtain ⟨hframe, hresolve, hworld, hown⟩ := hpre
  cases fuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    obtain ⟨middle, heval, hmiddle⟩ :=
      runOp_retain_borrowed (ctx := ctx) (cur := cur) (fuel := fuel)
        hresolve hworld hown
    have hpair : (middle, value) = (store', result) :=
      Except.ok.inj (heval.symm.trans hrun)
    cases hpair
    exact ⟨value, env, rfl, hframe, hmiddle⟩

theorem emit_retain_borrowed {ctx : Ctx} {cur : FnDef}
    {frame : List RVal → Prop} {atom : Atom} {value : RVal}
    {rest : List Root} :
    EmitSound ctx cur (emitOp (.dup atom))
      (fun store env => frame env ∧ resolveAtom env atom = .ok value ∧
        HasWorld store .shared value ∧ RootOwnership store rest)
      (OwnsPushedRoot frame .shared rest) := by
  exact EmitSound.of_below fun limit =>
    emit_retain_borrowed_at (limit := limit)

/-- Fuel-bounded counterpart of `emit_retain_borrowed`. Retain itself is
call-free, so the only fuel obligation is the enclosing operation bound. -/
theorem emit_retain_borrowed_below {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {frame : List RVal → Prop} {atom : Atom}
    {value : RVal} {rest : List Root} :
    EmitSoundBelow ctx cur limit (emitOp (.dup atom))
      (fun store env => frame env ∧ resolveAtom env atom = .ok value ∧
        HasWorld store .shared value ∧ RootOwnership store rest)
      (OwnsPushedRoot frame .shared rest) := by
  exact emit_retain_borrowed_at

/-- A known direct call plugs the declaration contract into the emitter
induction: argument roots disappear, the declared result root is pushed, and
the caller's continuation roots remain exact. -/
private theorem emit_call_owned_at {ctx : Ctx} {cur d : FnDef}
    {limit : Nat} {f : Ixon.Address} {frame : List RVal → Prop}
    {atoms : Array Atom} {args : List RVal} {argWorlds : List Owned}
    {rest : List Root}
    (hdecl : ctx.decls f = some (.fn d))
    (hcontract : FnOwnershipContractBelow ctx d argWorlds limit) :
    EmitSoundBelow ctx cur limit (emitOp (.call f atoms))
      (fun store env => frame env ∧ resolveAtoms env atoms = .ok args ∧
        RootOwnership store (rootsForWorlds argWorlds args ++ rest))
      (OwnsPushedRoot frame d.result rest) := by
  apply OpSoundBelow.emit
  intro opFuel store env store' result hopFuel hpre hrun
  obtain ⟨hframe, hargs, hown⟩ := hpre
  cases opFuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    have hcallee : FnOwnershipContractBelow ctx d argWorlds fuel :=
      hcontract.mono (by omega)
    have hresult := runOp_call_owned_below (ctx := ctx) (cur := cur)
      (fuel := fuel) hargs hdecl hcallee hown hrun
    exact ⟨result, env, rfl, hframe, hresult⟩

theorem emit_call_owned {ctx : Ctx} {cur d : FnDef} {f : Ixon.Address}
    {frame : List RVal → Prop} {atoms : Array Atom} {args : List RVal}
    {argWorlds : List Owned} {rest : List Root}
    (hdecl : ctx.decls f = some (.fn d))
    (hcontract : FnOwnershipContract ctx d argWorlds) :
    EmitSound ctx cur (emitOp (.call f atoms))
      (fun store env => frame env ∧ resolveAtoms env atoms = .ok args ∧
        RootOwnership store (rootsForWorlds argWorlds args ++ rest))
      (OwnsPushedRoot frame d.result rest) := by
  exact EmitSound.of_below fun limit =>
    emit_call_owned_at hdecl (hcontract.below limit)

/-- Recursive self-call counterpart of `emit_call_owned`. The current
function's contract consumes the argument prefix and supplies one root in
its declared result world. -/
private theorem emit_callSelf_owned_at {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {frame : List RVal → Prop} {atoms : Array Atom}
    {args : List RVal} {argWorlds : List Owned} {rest : List Root}
    (hcontract : FnOwnershipContractBelow ctx cur argWorlds limit) :
    EmitSoundBelow ctx cur limit (emitOp (.callSelf atoms))
      (fun store env => frame env ∧ resolveAtoms env atoms = .ok args ∧
        RootOwnership store (rootsForWorlds argWorlds args ++ rest))
      (OwnsPushedRoot frame cur.result rest) := by
  apply OpSoundBelow.emit
  intro opFuel store env store' result hopFuel hpre hrun
  obtain ⟨hframe, hargs, hown⟩ := hpre
  cases opFuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    have hself : FnOwnershipContractBelow ctx cur argWorlds (fuel + 1) :=
      hcontract.mono (Nat.le_of_lt hopFuel)
    have hresult := runOp_callSelf_owned_below (ctx := ctx) (cur := cur)
      (fuel := fuel) hargs hself hown hrun
    exact ⟨result, env, rfl, hframe, hresult⟩

theorem emit_callSelf_owned {ctx : Ctx} {cur : FnDef}
    {frame : List RVal → Prop} {atoms : Array Atom} {args : List RVal}
    {argWorlds : List Owned} {rest : List Root}
    (hcontract : FnOwnershipContract ctx cur argWorlds) :
    EmitSound ctx cur (emitOp (.callSelf atoms))
      (fun store env => frame env ∧ resolveAtoms env atoms = .ok args ∧
        RootOwnership store (rootsForWorlds argWorlds args ++ rest))
      (OwnsPushedRoot frame cur.result rest) := by
  exact EmitSound.of_below fun limit =>
    emit_callSelf_owned_at (hcontract.below limit)

/-- Successful scalar-only extern calls consume their inert shared argument
roots and push one scalar result root at the caller's demanded world. -/
private theorem emit_extern_owned_at {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {f : Ixon.Address} {frame : List RVal → Prop}
    {atoms : Array Atom} {args : List RVal} {resultWorld : Owned}
    {rest : List Root} :
    EmitSoundBelow ctx cur limit (emitOp (.extern f atoms))
      (fun store env => frame env ∧ resolveAtoms env atoms = .ok args ∧
        RootOwnership store (rootsFor .shared args ++ rest))
      (OwnsPushedRoot frame resultWorld rest) := by
  apply OpSoundBelow.emit
  intro fuel store env store' result _ hpre hrun
  obtain ⟨hframe, hargs, hown⟩ := hpre
  cases fuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    have hresult := runOp_extern_owned (ctx := ctx) (cur := cur)
      (fuel := fuel) (resultWorld := resultWorld) hargs hown hrun
    exact ⟨result, env, rfl, hframe, hresult⟩

theorem emit_extern_owned {ctx : Ctx} {cur : FnDef} {f : Ixon.Address}
    {frame : List RVal → Prop} {atoms : Array Atom} {args : List RVal}
    {resultWorld : Owned} {rest : List Root} :
    EmitSound ctx cur (emitOp (.extern f atoms))
      (fun store env => frame env ∧ resolveAtoms env atoms = .ok args ∧
        RootOwnership store (rootsFor .shared args ++ rest))
      (OwnsPushedRoot frame resultWorld rest) := by
  exact EmitSound.of_below fun limit =>
    emit_extern_owned_at (limit := limit)

/-- Fuel-bounded scalar-only extern operation. -/
theorem emit_extern_owned_below {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {f : Ixon.Address} {frame : List RVal → Prop}
    {atoms : Array Atom} {args : List RVal} {resultWorld : Owned}
    {rest : List Root} :
    EmitSoundBelow ctx cur limit (emitOp (.extern f atoms))
      (fun store env => frame env ∧ resolveAtoms env atoms = .ok args ∧
        RootOwnership store (rootsFor .shared args ++ rest))
      (OwnsPushedRoot frame resultWorld rest) := by
  exact emit_extern_owned_at

/-- Unknown application consumes the shared pap/function root together with
all supplied shared argument roots. Pap saturation and recursive
over-application are encapsulated by the context's callable contract. -/
private theorem emit_apply_owned_at {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {frame : List RVal → Prop}
    {functionAtom : Atom} {function : RVal} {atoms : Array Atom}
    {args : List RVal} {rest : List Root}
    (hcontract : ApplyOwnershipContractBelow ctx limit) :
    EmitSoundBelow ctx cur limit (emitOp (.apply functionAtom atoms))
      (fun store env => frame env ∧
        resolveAtom env functionAtom = .ok function ∧
        resolveAtoms env atoms = .ok args ∧
        RootOwnership store
          (⟨.shared, function⟩ :: rootsFor .shared args ++ rest))
      (OwnsPushedRoot frame .shared rest) := by
  apply OpSoundBelow.emit
  intro opFuel store env store' result hopFuel hpre hrun
  obtain ⟨hframe, hfunction, hargs, hown⟩ := hpre
  cases opFuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    have happly : ApplyOwnershipContractBelow ctx (fuel + 1) :=
      hcontract.mono (Nat.le_of_lt hopFuel)
    have hresult := runOp_apply_owned_below (ctx := ctx) (cur := cur)
      (fuel := fuel) hfunction hargs happly hown hrun
    exact ⟨result, env, rfl, hframe, hresult⟩

theorem emit_apply_owned {ctx : Ctx} {cur : FnDef}
    {frame : List RVal → Prop} {functionAtom : Atom} {function : RVal}
    {atoms : Array Atom} {args : List RVal} {rest : List Root}
    (hcontract : ApplyOwnershipContract ctx) :
    EmitSound ctx cur (emitOp (.apply functionAtom atoms))
      (fun store env => frame env ∧
        resolveAtom env functionAtom = .ok function ∧
        resolveAtoms env atoms = .ok args ∧
        RootOwnership store
          (⟨.shared, function⟩ :: rootsFor .shared args ++ rest))
      (OwnsPushedRoot frame .shared rest) := by
  exact EmitSound.of_below fun limit =>
    emit_apply_owned_at (hcontract.below limit)

/-- Bounded direct-call emitter rule for the mutual compiler induction. -/
theorem emit_call_owned_below {ctx : Ctx} {cur d : FnDef}
    {limit : Nat} {f : Ixon.Address} {frame : List RVal → Prop}
    {atoms : Array Atom} {args : List RVal} {argWorlds : List Owned}
    {rest : List Root}
    (hdecl : ctx.decls f = some (.fn d))
    (hcontract : FnOwnershipContractBelow ctx d argWorlds limit) :
    EmitSoundBelow ctx cur limit (emitOp (.call f atoms))
      (fun store env => frame env ∧ resolveAtoms env atoms = .ok args ∧
        RootOwnership store (rootsForWorlds argWorlds args ++ rest))
      (OwnsPushedRoot frame d.result rest) := by
  exact emit_call_owned_at hdecl hcontract

/-- Bounded recursive-self emitter rule. Only the strictly smaller body
contract exposed by the enclosing fuel prefix is consumed. -/
theorem emit_callSelf_owned_below {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {frame : List RVal → Prop} {atoms : Array Atom}
    {args : List RVal} {argWorlds : List Owned} {rest : List Root}
    (hcontract : FnOwnershipContractBelow ctx cur argWorlds limit) :
    EmitSoundBelow ctx cur limit (emitOp (.callSelf atoms))
      (fun store env => frame env ∧ resolveAtoms env atoms = .ok args ∧
        RootOwnership store (rootsForWorlds argWorlds args ++ rest))
      (OwnsPushedRoot frame cur.result rest) := by
  exact emit_callSelf_owned_at hcontract

/-- Bounded unknown-application emitter rule. Saturation and
over-application recurse only through the smaller application prefix. -/
theorem emit_apply_owned_below {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {frame : List RVal → Prop}
    {functionAtom : Atom} {function : RVal} {atoms : Array Atom}
    {args : List RVal} {rest : List Root}
    (hcontract : ApplyOwnershipContractBelow ctx limit) :
    EmitSoundBelow ctx cur limit (emitOp (.apply functionAtom atoms))
      (fun store env => frame env ∧
        resolveAtom env functionAtom = .ok function ∧
        resolveAtoms env atoms = .ok args ∧
        RootOwnership store
          (⟨.shared, function⟩ :: rootsFor .shared args ++ rest))
      (OwnsPushedRoot frame .shared rest) := by
  exact emit_apply_owned_at hcontract

/-- Dropping a shared value consumes its logical root whether the resolved
value is a location or an ownership-inert scalar. This is the generic rule
needed by `releaseAll`, whose slot descriptors may hold either kind. -/
private theorem emit_drop_value_owned_at {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {frame : List RVal → Prop} {target : Atom} {value : RVal}
    {rest : List Root} :
    EmitSoundBelow ctx cur limit (emitOp (.drop target))
      (fun store env => frame env ∧
        resolveAtom env target = .ok value ∧
        RootOwnership store (⟨.shared, value⟩ :: rest))
      (OwnsAfterPush frame rest) := by
  apply OpSoundBelow.emit
  intro fuel store env store' result _ hpre hrun
  obtain ⟨hframe, hresolve, hown⟩ := hpre
  cases fuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    rw [runOp.eq_def] at hrun
    dsimp only at hrun
    rw [hresolve, bindOk] at hrun
    cases value with
    | lit literal =>
      change (Except.ok (store, RVal.erased) :
        Except Err (Store × RVal)) = .ok (store', result) at hrun
      have hpair : (store, RVal.erased) = (store', result) :=
        Except.ok.inj hrun
      cases hpair
      exact ⟨.erased, env, rfl, hframe,
        hown.dropNoLocation (by rfl)⟩
    | erased =>
      change (Except.ok (store, RVal.erased) :
        Except Err (Store × RVal)) = .ok (store', result) at hrun
      have hpair : (store, RVal.erased) = (store', result) :=
        Except.ok.inj hrun
      cases hpair
      exact ⟨.erased, env, rfl, hframe,
        hown.dropNoLocation (by rfl)⟩
    | loc loc =>
      dsimp only at hrun
      cases hdrop : dropVal ctx fuel store (.loc loc) with
      | error err =>
        rw [hdrop] at hrun
        change (Except.error err : Except Err (Store × RVal)) =
          .ok (store', result) at hrun
        contradiction
      | ok dropped =>
        rw [hdrop] at hrun
        change (Except.ok (dropped, RVal.erased) :
          Except Err (Store × RVal)) = .ok (store', result) at hrun
        have hpair : (dropped, RVal.erased) = (store', result) :=
          Except.ok.inj hrun
        cases hpair
        exact ⟨.erased, env, rfl, hframe,
          dropVal_preserves hown hdrop⟩

theorem emit_drop_value_owned {ctx : Ctx} {cur : FnDef}
    {frame : List RVal → Prop} {target : Atom} {value : RVal}
    {rest : List Root} :
    EmitSound ctx cur (emitOp (.drop target))
      (fun store env => frame env ∧
        resolveAtom env target = .ok value ∧
        RootOwnership store (⟨.shared, value⟩ :: rest))
      (OwnsAfterPush frame rest) := by
  exact EmitSound.of_below fun limit =>
    emit_drop_value_owned_at (limit := limit)

/-- Fuel-bounded shared release for a value of arbitrary runtime shape. -/
theorem emit_drop_value_owned_below {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {frame : List RVal → Prop} {target : Atom}
    {value : RVal} {rest : List Root} :
    EmitSoundBelow ctx cur limit (emitOp (.drop target))
      (fun store env => frame env ∧
        resolveAtom env target = .ok value ∧
        RootOwnership store (⟨.shared, value⟩ :: rest))
      (OwnsAfterPush frame rest) := by
  exact emit_drop_value_owned_at

theorem emit_drop_owned {ctx : Ctx} {cur : FnDef}
    {frame : List RVal → Prop} {target : Atom} {loc : Nat}
    {rest : List Root} :
    EmitSound ctx cur (emitOp (.drop target))
      (fun store env => frame env ∧
        resolveAtom env target = .ok (.loc loc) ∧
        RootOwnership store (⟨.shared, .loc loc⟩ :: rest))
      (OwnsAfterPush frame rest) := by
  apply OpSound.emit
  intro fuel store env store' result hpre hrun
  obtain ⟨hframe, hresolve, hown⟩ := hpre
  cases fuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    rw [runOp.eq_def] at hrun
    dsimp only at hrun
    rw [hresolve, bindOk] at hrun
    dsimp only at hrun
    cases hdrop : dropVal ctx fuel store (.loc loc) with
    | error err =>
      rw [hdrop] at hrun
      change (Except.error err : Except Err (Store × RVal)) =
        .ok (store', result) at hrun
      contradiction
    | ok dropped =>
      rw [hdrop] at hrun
      change (Except.ok (dropped, .erased) : Except Err (Store × RVal)) =
        .ok (store', result) at hrun
      have hpair : (dropped, RVal.erased) = (store', result) :=
        Except.ok.inj hrun
      cases hpair
      exact ⟨.erased, env, rfl, hframe,
        dropVal_preserves hown hdrop⟩

theorem emit_dropU_owned {ctx : Ctx} {cur : FnDef}
    {frame : List RVal → Prop} {target : Atom} {loc : Nat}
    {rest : List Root} :
    EmitSound ctx cur (emitOp (.dropU target))
      (fun store env => frame env ∧
        resolveAtom env target = .ok (.loc loc) ∧
        RootOwnership store (⟨.unique, .loc loc⟩ :: rest))
      (OwnsAfterPush frame rest) := by
  apply OpSound.emit
  intro fuel store env store' result hpre hrun
  obtain ⟨hframe, hresolve, hown⟩ := hpre
  cases fuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    rw [runOp.eq_def] at hrun
    dsimp only at hrun
    rw [hresolve, bindOk] at hrun
    dsimp only at hrun
    cases hdrop : dropUVal ctx fuel store (.loc loc) with
    | error err =>
      rw [hdrop] at hrun
      change (Except.error err : Except Err (Store × RVal)) =
        .ok (store', result) at hrun
      contradiction
    | ok dropped =>
      rw [hdrop] at hrun
      change (Except.ok (dropped, .erased) : Except Err (Store × RVal)) =
        .ok (store', result) at hrun
      have hpair : (dropped, RVal.erased) = (store', result) :=
        Except.ok.inj hrun
      cases hpair
      exact ⟨.erased, env, rfl, hframe,
        dropUVal_preserves hown hdrop⟩

/-- Generic affine release, including ownership-inert scalar values. -/
private theorem emit_dropU_value_owned_at {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {frame : List RVal → Prop} {target : Atom} {value : RVal}
    {rest : List Root} :
    EmitSoundBelow ctx cur limit (emitOp (.dropU target))
      (fun store env => frame env ∧
        resolveAtom env target = .ok value ∧
        RootOwnership store (⟨.unique, value⟩ :: rest))
      (OwnsAfterPush frame rest) := by
  apply OpSoundBelow.emit
  intro fuel store env store' result _ hpre hrun
  obtain ⟨hframe, hresolve, hown⟩ := hpre
  cases fuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    rw [runOp.eq_def] at hrun
    dsimp only at hrun
    rw [hresolve, bindOk] at hrun
    cases value with
    | lit literal =>
      change (Except.ok (store, RVal.erased) :
        Except Err (Store × RVal)) = .ok (store', result) at hrun
      have hpair : (store, RVal.erased) = (store', result) :=
        Except.ok.inj hrun
      cases hpair
      exact ⟨.erased, env, rfl, hframe,
        hown.dropNoLocation (by rfl)⟩
    | erased =>
      change (Except.ok (store, RVal.erased) :
        Except Err (Store × RVal)) = .ok (store', result) at hrun
      have hpair : (store, RVal.erased) = (store', result) :=
        Except.ok.inj hrun
      cases hpair
      exact ⟨.erased, env, rfl, hframe,
        hown.dropNoLocation (by rfl)⟩
    | loc loc =>
      dsimp only at hrun
      cases hdrop : dropUVal ctx fuel store (.loc loc) with
      | error err =>
        rw [hdrop] at hrun
        change (Except.error err : Except Err (Store × RVal)) =
          .ok (store', result) at hrun
        contradiction
      | ok dropped =>
        rw [hdrop] at hrun
        change (Except.ok (dropped, RVal.erased) :
          Except Err (Store × RVal)) = .ok (store', result) at hrun
        have hpair : (dropped, RVal.erased) = (store', result) :=
          Except.ok.inj hrun
        cases hpair
        exact ⟨.erased, env, rfl, hframe,
          dropUVal_preserves hown hdrop⟩

theorem emit_dropU_value_owned {ctx : Ctx} {cur : FnDef}
    {frame : List RVal → Prop} {target : Atom} {value : RVal}
    {rest : List Root} :
    EmitSound ctx cur (emitOp (.dropU target))
      (fun store env => frame env ∧
        resolveAtom env target = .ok value ∧
        RootOwnership store (⟨.unique, value⟩ :: rest))
      (OwnsAfterPush frame rest) := by
  exact EmitSound.of_below fun limit =>
    emit_dropU_value_owned_at (limit := limit)

/-- Fuel-bounded affine release for a value of arbitrary runtime shape. -/
theorem emit_dropU_value_owned_below {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {frame : List RVal → Prop} {target : Atom}
    {value : RVal} {rest : List Root} :
    EmitSoundBelow ctx cur limit (emitOp (.dropU target))
      (fun store env => frame env ∧
        resolveAtom env target = .ok value ∧
        RootOwnership store (⟨.unique, value⟩ :: rest))
      (OwnsAfterPush frame rest) := by
  exact emit_dropU_value_owned_at

theorem emit_free_owned {ctx : Ctx} {cur : FnDef}
    {frame : List RVal → Prop} {target : Atom} {loc : Nat}
    {node : Node} {rest : List Root} :
    EmitSound ctx cur (emitOp (.free target))
      (fun store env => frame env ∧
        resolveAtom env target = .ok (.loc loc) ∧
        store.get? loc = some ⟨.unique, 1, node⟩ ∧
        RootOwnership store (⟨.unique, .loc loc⟩ :: rest))
      (OwnsAfterPush frame (rootsFor .unique (nodeChildren node) ++ rest)) := by
  apply OpSound.emit
  intro fuel store env store' result hpre hrun
  obtain ⟨hframe, hresolve, hbox, hown⟩ := hpre
  cases fuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    have hop := runOp_free_owned (ctx := ctx) (cur := cur)
      (fuel := fuel) hresolve hbox hown
    have hpair : (store.kill loc, RVal.erased) = (store', result) :=
      Except.ok.inj (hop.1.symm.trans hrun)
    cases hpair
    exact ⟨.erased, env, rfl, hframe, hop.2⟩

private theorem emit_fetch_borrowed_at {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {frame : List RVal → Prop} {target : Atom} {loc rc i : Nat}
    {cid : CtorId} {fields : Array RVal}
    {value : RVal} {roots : List Root}
    (hfield : fields[i]? = some value) :
    EmitSoundBelow ctx cur limit (emitOp (.fetch target i))
      (fun store env => frame env ∧
        resolveAtom env target = .ok (.loc loc) ∧
        store.get? loc = some ⟨.shared, rc, .ctorN cid fields⟩ ∧
        RootOwnership store roots)
      (BorrowsPushed frame .shared roots) := by
  apply OpSoundBelow.emit
  intro fuel store env store' result _ hpre hrun
  obtain ⟨hframe, hresolve, hbox, hown⟩ := hpre
  cases fuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    have hop := runOp_fetch_borrowed (ctx := ctx) (cur := cur)
      (fuel := fuel) hresolve hbox hfield hown
    have hpair : (store, value) = (store', result) :=
      Except.ok.inj (hop.1.symm.trans hrun)
    cases hpair
    exact ⟨value, env, rfl, hframe, hop.2, hown⟩

theorem emit_fetch_borrowed {ctx : Ctx} {cur : FnDef}
    {frame : List RVal → Prop} {target : Atom} {loc rc i : Nat}
    {cid : CtorId} {fields : Array RVal}
    {value : RVal} {roots : List Root}
    (hfield : fields[i]? = some value) :
    EmitSound ctx cur (emitOp (.fetch target i))
      (fun store env => frame env ∧
        resolveAtom env target = .ok (.loc loc) ∧
        store.get? loc = some ⟨.shared, rc, .ctorN cid fields⟩ ∧
        RootOwnership store roots)
      (BorrowsPushed frame .shared roots) := by
  exact EmitSound.of_below fun limit =>
    emit_fetch_borrowed_at (limit := limit) hfield

/-- Fuel-bounded borrowed-field fetch. The operation pushes only a borrow;
the parent's root and the complete root multiset remain unchanged. -/
theorem emit_fetch_borrowed_below {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {frame : List RVal → Prop} {target : Atom}
    {loc rc i : Nat} {cid : CtorId} {fields : Array RVal}
    {value : RVal} {roots : List Root}
    (hfield : fields[i]? = some value) :
    EmitSoundBelow ctx cur limit (emitOp (.fetch target i))
      (fun store env => frame env ∧
        resolveAtom env target = .ok (.loc loc) ∧
        store.get? loc = some ⟨.shared, rc, .ctorN cid fields⟩ ∧
        RootOwnership store roots)
      (BorrowsPushed frame .shared roots) := by
  exact emit_fetch_borrowed_at hfield

/-! ## Exact-root predicates used by expression lowering -/

/-- The held source slots plus an arbitrary caller continuation own the
entire input heap. -/
def OwnsVEnv (Γ : VEnv) (rest : List Root) : StatePred :=
  fun store env => ∃ roots,
    VEnvRealizes Γ env roots ∧
    RootOwnership store (roots ++ rest)

/-- The lowered result owns one root in `world`, alongside the roots still
held by the output `VEnv` and the caller continuation. -/
def OwnsResult (Γ : VEnv) (world : Owned) (av : AVal)
    (rest : List Root) : StatePred :=
  fun store env => ∃ roots value,
    VEnvRealizes Γ env roots ∧
    AValRealizes Γ env av value ∧
    RootOwnership store (⟨world, value⟩ :: roots ++ rest)

/-- Semantic companion of `OwnsVEnv`: each held logical root additionally
realizes the corresponding source evaluator value, and the caller's framed
roots carry their own source correspondence. The latter is essential when an
earlier argument is framed across the lowering of later arguments. -/
def GraphOwnsVEnv (funRel : Sim.FunctionRel)
    (recSelfRel : RecSelfRel) (Γ : VEnv)
    (sourceEnv : List IxIR0.Value)
    (sourceRest : List (Owned × IxIR0.Value))
    (rest : List Root) : StatePred :=
  fun store env => ∃ roots,
    VEnvValueGraph funRel recSelfRel store Γ sourceEnv env roots ∧
    Sim.RootsGraph funRel store sourceRest rest ∧
    RootOwnership store (roots ++ rest)

/-- Semantic companion of `OwnsResult`: the returned `AVal` realizes both
the target root and the successful pure source result. -/
def GraphOwnsResult (funRel : Sim.FunctionRel)
    (recSelfRel : RecSelfRel) (Γ : VEnv)
    (sourceEnv : List IxIR0.Value) (sourceValue : IxIR0.Value)
    (world : Owned) (av : AVal)
    (sourceRest : List (Owned × IxIR0.Value))
    (rest : List Root) : StatePred :=
  fun store env => ∃ roots value,
    VEnvValueGraph funRel recSelfRel store Γ sourceEnv env roots ∧
    AValRealizes Γ env av value ∧
    Sim.ValueGraph funRel store sourceValue value ∧
    Sim.RootsGraph funRel store sourceRest rest ∧
    RootOwnership store (⟨world, value⟩ :: roots ++ rest)

/-- Forgetting source values recovers the ownership precondition used by the
existing lowering proof. -/
theorem GraphOwnsVEnv.toOwnsVEnv {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value}
    {sourceRest : List (Owned × IxIR0.Value)} {rest : List Root}
    {store : Store} {env : List RVal}
    (h : GraphOwnsVEnv funRel recSelfRel Γ sourceEnv
      sourceRest rest store env) :
    OwnsVEnv Γ rest store env := by
  obtain ⟨roots, hgraph, _, hown⟩ := h
  exact ⟨roots, hgraph.vEnvRealizes, hown⟩

/-- Forgetting the result graph recovers the ownership postcondition. -/
theorem GraphOwnsResult.toOwnsResult {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value} {sourceValue : IxIR0.Value}
    {world : Owned} {av : AVal}
    {sourceRest : List (Owned × IxIR0.Value)} {rest : List Root}
    {store : Store} {env : List RVal}
    (h : GraphOwnsResult funRel recSelfRel Γ sourceEnv sourceValue
      world av sourceRest rest store env) :
    OwnsResult Γ world av rest store env := by
  obtain ⟨roots, value, hgraph, hav, _, _, hown⟩ := h
  exact ⟨roots, value, hgraph.vEnvRealizes, hav, hown⟩

/-- Input ownership plus an arbitrary frame of older absolute slots that a
later argument/result must not invalidate. -/
def OwnsVEnvProtected (Γ : VEnv) (rest : List Root)
    (slots : List (Nat × RVal)) : StatePred :=
  fun store env => OwnsVEnv Γ rest store env ∧
    SlotsRealize Γ env slots

/-- A protected lowering environment together with shared-world facts for
borrowed case fields that later prefix steps may retain. -/
def OwnsVEnvBorrowed (Γ : VEnv) (rest : List Root)
    (slots : List (Nat × RVal)) (borrowed : List RVal) : StatePred :=
  fun store env => OwnsVEnvProtected Γ rest slots store env ∧
    ∀ value ∈ borrowed, HasWorld store .shared value

/-- Result ownership while preserving every protected absolute slot. -/
def OwnsResultProtected (Γ : VEnv) (world : Owned) (av : AVal)
    (rest : List Root) (slots : List (Nat × RVal)) : StatePred :=
  fun store env => OwnsResult Γ world av rest store env ∧
    SlotsRealize Γ env slots

def GraphOwnsVEnvProtected (funRel : Sim.FunctionRel)
    (recSelfRel : RecSelfRel) (Γ : VEnv)
    (sourceEnv : List IxIR0.Value)
    (sourceRest : List (Owned × IxIR0.Value)) (rest : List Root)
    (slots : List (Nat × RVal)) : StatePred :=
  fun store env =>
    GraphOwnsVEnv funRel recSelfRel Γ sourceEnv sourceRest rest store env ∧
    SlotsRealize Γ env slots

def GraphOwnsResultProtected (funRel : Sim.FunctionRel)
    (recSelfRel : RecSelfRel) (Γ : VEnv)
    (sourceEnv : List IxIR0.Value) (sourceValue : IxIR0.Value)
    (world : Owned) (av : AVal)
    (sourceRest : List (Owned × IxIR0.Value)) (rest : List Root)
    (slots : List (Nat × RVal)) : StatePred :=
  fun store env =>
    GraphOwnsResult funRel recSelfRel Γ sourceEnv sourceValue
      world av sourceRest rest store env ∧
    SlotsRealize Γ env slots

/-- The soundness proposition attached to one successful `lowerE` result.
Besides exact ownership it records that the returned descriptor is stable and
preserves any older absolute slots. The latter is the frame rule required by
left-to-right `lowerArgs` sequencing. -/
structure LowerResultSound (ctx : Ctx) (cur : FnDef)
    (input output : VEnv) (world : Owned) (emit : Emit) (av : AVal) : Prop where
  stable : AValStable av
  emits : ∀ rest slots,
    EmitSound ctx cur emit (OwnsVEnvProtected input rest slots)
      (OwnsResultProtected output world av rest slots)

/-- Companion semantic refinement for one expression result. It retains the
complete ownership theorem as a parent field and separately transports a
source-environment graph to a graph-related source result. Keeping the two
transformers separate prevents source values from entering primitive RC and
frame lemmas. -/
structure LowerResultValueSound (funRel : Sim.FunctionRel)
    (recSelfRel : RecSelfRel) (ctx : Ctx) (cur : FnDef)
    (input output : VEnv)
    (sourceInput sourceOutput : List IxIR0.Value)
    (sourceValue : IxIR0.Value) (world : Owned)
    (emit : Emit) (av : AVal) : Prop
    extends LowerResultSound ctx cur input output world emit av where
  graphEmits : ∀ sourceRest rest slots,
    EmitSound ctx cur emit
      (GraphOwnsVEnvProtected funRel recSelfRel input
        sourceInput sourceRest rest slots)
      (GraphOwnsResultProtected funRel recSelfRel output
        sourceOutput sourceValue world av sourceRest rest slots)

/-- Fuel-bounded expression-lowering soundness used before recursive
context contracts have been sealed. -/
structure LowerResultSoundBelow (ctx : Ctx) (cur : FnDef)
    (limit : Nat) (input output : VEnv) (world : Owned)
    (emit : Emit) (av : AVal) : Prop where
  stable : AValStable av
  emits : ∀ rest slots,
    EmitSoundBelow ctx cur limit emit
      (OwnsVEnvProtected input rest slots)
      (OwnsResultProtected output world av rest slots)

/-- An expression result proved uniformly at every fuel bound satisfies the
unbounded ownership interface. The stable descriptor is fuel-independent;
only its continuation transformer needs closure through `EmitSound.of_below`.
-/
theorem LowerResultSound.of_below {ctx : Ctx} {cur : FnDef}
    {input output : VEnv} {world : Owned} {emit : Emit} {av : AVal}
    (hsound : ∀ limit,
      LowerResultSoundBelow ctx cur limit input output world emit av) :
    LowerResultSound ctx cur input output world emit av := by
  refine ⟨(hsound 0).stable, ?_⟩
  intro rest slots
  exact EmitSound.of_below fun limit =>
    (hsound limit).emits rest slots

/-- Logical roots supplied by a borrowing result. A temporary or final-use
slot still owns one shared root that the projection must release; a repeated
variable borrow is already owned by the returned `VEnv`. -/
def borrowResultRoots (release : Bool) (value : RVal) : List Root :=
  if release then [⟨.shared, value⟩] else []

/-- Successful `lowerBorrow` output: the descriptor resolves to a shared
borrow, and `release` states whether its owner sits outside the output
environment and must be consumed by the caller. -/
def OwnsBorrowResult (Γ : VEnv) (av : AVal) (release : Bool)
    (rest : List Root) : StatePred :=
  fun store env => ∃ roots value,
    VEnvRealizes Γ env roots ∧
    AValRealizes Γ env av value ∧
    HasWorld store .shared value ∧
    RootOwnership store
      (borrowResultRoots release value ++ roots ++ rest)

def OwnsBorrowResultProtected (Γ : VEnv) (av : AVal)
    (release : Bool) (rest : List Root)
    (slots : List (Nat × RVal)) : StatePred :=
  fun store env => OwnsBorrowResult Γ av release rest store env ∧
    SlotsRealize Γ env slots

/-- State after `fetch`: the original target and newly pushed field are both
shared borrows, and no root multiplicity has changed. -/
def OwnsFetchedBorrowProtected (Γ : VEnv) (target field : AVal)
    (release : Bool) (rest : List Root)
    (slots : List (Nat × RVal)) : StatePred :=
  fun store env => ∃ roots targetValue fieldValue,
    VEnvRealizes Γ env roots ∧
    AValRealizes Γ env target targetValue ∧
    AValRealizes Γ env field fieldValue ∧
    HasWorld store .shared targetValue ∧
    HasWorld store .shared fieldValue ∧
    RootOwnership store
      (borrowResultRoots release targetValue ++ roots ++ rest) ∧
    SlotsRealize Γ env slots

/-- State after retaining the fetched field: the field is now the distinct
owned result root, while a final-use target owner remains pending exactly
when `release` is true. -/
def OwnsRetainedProjectionProtected (Γ : VEnv) (target result : AVal)
    (release : Bool) (rest : List Root)
    (slots : List (Nat × RVal)) : StatePred :=
  fun store env => ∃ roots targetValue resultValue,
    VEnvRealizes Γ env roots ∧
    AValRealizes Γ env target targetValue ∧
    AValRealizes Γ env result resultValue ∧
    HasWorld store .shared targetValue ∧
    RootOwnership store
      (⟨.shared, resultValue⟩ ::
        borrowResultRoots release targetValue ++ roots ++ rest) ∧
    SlotsRealize Γ env slots

/-- Semantic borrowing result: the borrowed runtime value still realizes the
source value, while the source environment and caller frame keep their graph
witnesses. -/
def GraphOwnsBorrowResultProtected (funRel : Sim.FunctionRel)
    (recSelfRel : RecSelfRel) (Γ : VEnv)
    (sourceEnv : List IxIR0.Value) (sourceValue : IxIR0.Value)
    (av : AVal) (release : Bool)
    (sourceRest : List (Owned × IxIR0.Value)) (rest : List Root)
    (slots : List (Nat × RVal)) : StatePred :=
  fun store env => ∃ roots value,
    VEnvValueGraph funRel recSelfRel store Γ sourceEnv env roots ∧
    AValRealizes Γ env av value ∧
    HasWorld store .shared value ∧
    Sim.ValueGraph funRel store sourceValue value ∧
    Sim.RootsGraph funRel store sourceRest rest ∧
    RootOwnership store
      (borrowResultRoots release value ++ roots ++ rest) ∧
    SlotsRealize Γ env slots

/-- Semantic state after `fetch`: both the constructor target and selected
field retain their source graphs, while the field remains only a borrow. -/
def GraphOwnsFetchedBorrowProtected (funRel : Sim.FunctionRel)
    (recSelfRel : RecSelfRel) (Γ : VEnv)
    (sourceEnv : List IxIR0.Value)
    (sourceTarget sourceField : IxIR0.Value)
    (target field : AVal) (release : Bool)
    (sourceRest : List (Owned × IxIR0.Value)) (rest : List Root)
    (slots : List (Nat × RVal)) : StatePred :=
  fun store env => ∃ roots targetValue fieldValue,
    VEnvValueGraph funRel recSelfRel store Γ sourceEnv env roots ∧
    AValRealizes Γ env target targetValue ∧
    AValRealizes Γ env field fieldValue ∧
    HasWorld store .shared targetValue ∧
    HasWorld store .shared fieldValue ∧
    Sim.ValueGraph funRel store sourceTarget targetValue ∧
    Sim.ValueGraph funRel store sourceField fieldValue ∧
    Sim.RootsGraph funRel store sourceRest rest ∧
    RootOwnership store
      (borrowResultRoots release targetValue ++ roots ++ rest) ∧
    SlotsRealize Γ env slots

/-- Semantic state after retaining the fetched field as the owned result. -/
def GraphOwnsRetainedProjectionProtected (funRel : Sim.FunctionRel)
    (recSelfRel : RecSelfRel) (Γ : VEnv)
    (sourceEnv : List IxIR0.Value)
    (sourceTarget sourceField : IxIR0.Value)
    (target result : AVal) (release : Bool)
    (sourceRest : List (Owned × IxIR0.Value)) (rest : List Root)
    (slots : List (Nat × RVal)) : StatePred :=
  fun store env => ∃ roots targetValue resultValue,
    VEnvValueGraph funRel recSelfRel store Γ sourceEnv env roots ∧
    AValRealizes Γ env target targetValue ∧
    AValRealizes Γ env result resultValue ∧
    HasWorld store .shared targetValue ∧
    Sim.ValueGraph funRel store sourceTarget targetValue ∧
    Sim.ValueGraph funRel store sourceField resultValue ∧
    Sim.RootsGraph funRel store sourceRest rest ∧
    RootOwnership store
      (⟨.shared, resultValue⟩ ::
        borrowResultRoots release targetValue ++ roots ++ rest) ∧
    SlotsRealize Γ env slots

/-- Fuel-bounded soundness package for one successful borrowing-position
lowering run. -/
structure LowerBorrowSoundBelow (ctx : Ctx) (cur : FnDef)
    (limit : Nat) (input output : VEnv) (emit : Emit) (av : AVal)
    (release : Bool) : Prop where
  stable : AValStable av
  emits : ∀ rest slots,
    EmitSoundBelow ctx cur limit emit
      (OwnsVEnvProtected input rest slots)
      (OwnsBorrowResultProtected output av release rest slots)

/-- Unbounded ownership interface for borrowing-position lowering. -/
structure LowerBorrowSound (ctx : Ctx) (cur : FnDef)
    (input output : VEnv) (emit : Emit) (av : AVal)
    (release : Bool) : Prop where
  stable : AValStable av
  emits : ∀ rest slots,
    EmitSound ctx cur emit
      (OwnsVEnvProtected input rest slots)
      (OwnsBorrowResultProtected output av release rest slots)

theorem LowerBorrowSound.of_below {ctx : Ctx} {cur : FnDef}
    {input output : VEnv} {emit : Emit} {av : AVal} {release : Bool}
    (hsound : ∀ limit,
      LowerBorrowSoundBelow ctx cur limit input output emit av release) :
    LowerBorrowSound ctx cur input output emit av release := by
  refine ⟨(hsound 0).stable, ?_⟩
  intro rest slots
  exact EmitSound.of_below fun limit =>
    (hsound limit).emits rest slots

/-- Companion semantic refinement for a borrowing-position result. -/
structure LowerBorrowValueSound (funRel : Sim.FunctionRel)
    (recSelfRel : RecSelfRel) (ctx : Ctx) (cur : FnDef)
    (input output : VEnv)
    (sourceInput sourceOutput : List IxIR0.Value)
    (sourceValue : IxIR0.Value) (emit : Emit) (av : AVal)
    (release : Bool) : Prop
    extends LowerBorrowSound ctx cur input output emit av release where
  graphEmits : ∀ sourceRest rest slots,
    EmitSound ctx cur emit
      (GraphOwnsVEnvProtected funRel recSelfRel input
        sourceInput sourceRest rest slots)
      (GraphOwnsBorrowResultProtected funRel recSelfRel output
        sourceOutput sourceValue av release sourceRest rest slots)

/-- Bounded expression proofs are contravariant in their fuel bound. -/
theorem LowerResultSoundBelow.mono {ctx : Ctx} {cur : FnDef}
    {smaller larger : Nat} {input output : VEnv} {world : Owned}
    {emit : Emit} {av : AVal}
    (hsound : LowerResultSoundBelow ctx cur larger input output world emit av)
    (hbound : smaller ≤ larger) :
    LowerResultSoundBelow ctx cur smaller input output world emit av := by
  refine ⟨hsound.stable, ?_⟩
  intro rest slots bound hsmall
  exact hsound.emits rest slots bound (Nat.le_trans hsmall hbound)

/-- Forget a released first logical binder from a bounded expression result.
The physical stack and absolute-slot interpretation are unchanged. -/
theorem LowerResultSoundBelow.popFirstReleased
    {ctx : Ctx} {cur : FnDef} {limit : Nat}
    {input output : VEnv} {world : Owned} {emit : Emit} {av : AVal}
    (hsound : LowerResultSoundBelow ctx cur limit input output world emit av)
    (hfirst : FirstEntryReleased output) :
    LowerResultSoundBelow ctx cur limit input output.pop world emit av := by
  refine ⟨hsound.stable, ?_⟩
  intro rest slots
  have hpop : EmitSoundBelow ctx cur limit (_root_.id : Emit)
      (OwnsResultProtected output world av rest slots)
      (OwnsResultProtected output.pop world av rest slots) := by
    apply EmitSoundBelow.strengthen
    intro store env hpre
    obtain ⟨⟨roots, value, houtput, hav, hown⟩, hslots⟩ := hpre
    refine ⟨⟨roots, value, houtput.pop_firstReleased hfirst,
      hav.of_depth_eq (by simp [VEnv.pop]), hown⟩, ?_⟩
    exact SlotsRealize.of_depth_eq (by simp [VEnv.pop]) hslots
  have hcomposed := EmitSoundBelow.comp (hsound.emits rest slots) hpop
  simpa [Function.comp_def] using hcomposed

/-- Forget a released first logical binder from an unbounded expression
result. This is the continuation-level counterpart of `VEnv.pop`. -/
theorem LowerResultSound.popFirstReleased
    {ctx : Ctx} {cur : FnDef} {input output : VEnv}
    {world : Owned} {emit : Emit} {av : AVal}
    (hsound : LowerResultSound ctx cur input output world emit av)
    (hfirst : FirstEntryReleased output) :
    LowerResultSound ctx cur input output.pop world emit av := by
  refine ⟨hsound.stable, ?_⟩
  intro rest slots
  have hpop : EmitSound ctx cur (_root_.id : Emit)
      (OwnsResultProtected output world av rest slots)
      (OwnsResultProtected output.pop world av rest slots) := by
    apply EmitSound.strengthen
    intro store env hpre
    obtain ⟨⟨roots, value, houtput, hav, hown⟩, hslots⟩ := hpre
    refine ⟨⟨roots, value, houtput.pop_firstReleased hfirst,
      hav.of_depth_eq (by simp [VEnv.pop]), hown⟩, ?_⟩
    exact SlotsRealize.of_depth_eq (by simp [VEnv.pop]) hslots
  have hcomposed := EmitSound.comp (hsound.emits rest slots) hpop
  simpa [Function.comp_def] using hcomposed

/-- The semantic companion removes the corresponding leading source value
when a let body's released first logical entry is popped. -/
theorem LowerResultValueSound.popFirstReleased
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {input output : VEnv}
    {sourceInput sourceOutput : List IxIR0.Value}
    {boundSource sourceValue : IxIR0.Value}
    {world : Owned} {emit : Emit} {av : AVal}
    (hsound : LowerResultValueSound funRel recSelfRel ctx cur
      input output sourceInput (boundSource :: sourceOutput)
      sourceValue world emit av)
    (hfirst : FirstEntryReleased output) :
    LowerResultValueSound funRel recSelfRel ctx cur input output.pop
      sourceInput sourceOutput sourceValue world emit av := by
  refine
    { toLowerResultSound :=
        hsound.toLowerResultSound.popFirstReleased hfirst
      graphEmits := ?_ }
  intro sourceRest rest slots
  have hpop : EmitSound ctx cur (_root_.id : Emit)
      (GraphOwnsResultProtected funRel recSelfRel output
        (boundSource :: sourceOutput) sourceValue world av
        sourceRest rest slots)
      (GraphOwnsResultProtected funRel recSelfRel output.pop
        sourceOutput sourceValue world av sourceRest rest slots) := by
    apply EmitSound.strengthen
    intro store env hpre
    obtain ⟨⟨roots, value, houtput, hav, hvalueGraph,
        hrestGraph, hown⟩, hslots⟩ := hpre
    refine ⟨⟨roots, value, houtput.pop_firstReleased hfirst,
      hav.of_depth_eq (by simp [VEnv.pop]), hvalueGraph,
      hrestGraph, hown⟩, ?_⟩
    exact SlotsRealize.of_depth_eq (by simp [VEnv.pop]) hslots
  have hcomposed := EmitSound.comp
    (hsound.graphEmits sourceRest rest slots) hpop
  simpa [Function.comp_def] using hcomposed

/-- Bounded borrow proofs are contravariant in their evaluator bound. -/
theorem LowerBorrowSoundBelow.mono {ctx : Ctx} {cur : FnDef}
    {smaller larger : Nat} {input output : VEnv} {emit : Emit}
    {av : AVal} {release : Bool}
    (hsound : LowerBorrowSoundBelow ctx cur larger input output emit av
      release)
    (hbound : smaller ≤ larger) :
    LowerBorrowSoundBelow ctx cur smaller input output emit av release := by
  refine ⟨hsound.stable, ?_⟩
  intro rest slots bound hsmall
  exact hsound.emits rest slots bound (Nat.le_trans hsmall hbound)

/-- Reinterpret an owned shared slot result as a borrowing result whose
separate owner must be released by the projection caller. -/
theorem LowerResultSoundBelow.asBorrowSlot
    {ctx : Ctx} {cur : FnDef} {limit : Nat}
    {input output : VEnv} {emit : Emit} {abs : Nat}
    (hsound : LowerResultSoundBelow ctx cur limit input output .shared emit
      (.slotA abs)) :
    LowerBorrowSoundBelow ctx cur limit input output emit (.slotA abs)
      true := by
  refine ⟨hsound.stable, ?_⟩
  intro rest slots
  have hconvert : EmitSoundBelow ctx cur limit (_root_.id : Emit)
      (OwnsResultProtected output .shared (.slotA abs) rest slots)
      (OwnsBorrowResultProtected output (.slotA abs) true rest slots) := by
    apply EmitSoundBelow.strengthen
    intro store env hpre
    obtain ⟨⟨roots, value, houtput, hav, hown⟩, hslots⟩ := hpre
    have hworld : HasWorld store .shared value :=
      hown.roots_world ⟨.shared, value⟩ (by simp)
    refine ⟨⟨roots, value, houtput, hav, hworld, ?_⟩, hslots⟩
    simpa [borrowResultRoots] using hown
  have hcomposed := EmitSoundBelow.comp (hsound.emits rest slots) hconvert
  simpa [Function.comp_def] using hcomposed

/-- Stable scalar results carry no heap owner, so their logical result root
can be forgotten and the value exposed as a non-releasing shared borrow. -/
theorem LowerResultSoundBelow.asBorrowConst
    {ctx : Ctx} {cur : FnDef} {limit : Nat}
    {input output : VEnv} {emit : Emit} {atom : Atom}
    (hsound : LowerResultSoundBelow ctx cur limit input output .shared emit
      (.constA atom)) :
    LowerBorrowSoundBelow ctx cur limit input output emit (.constA atom)
      false := by
  refine ⟨hsound.stable, ?_⟩
  intro rest slots
  have hconvert : EmitSoundBelow ctx cur limit (_root_.id : Emit)
      (OwnsResultProtected output .shared (.constA atom) rest slots)
      (OwnsBorrowResultProtected output (.constA atom) false rest slots) := by
    apply EmitSoundBelow.strengthen
    intro store env hpre
    obtain ⟨⟨roots, value, houtput, hav, hown⟩, hslots⟩ := hpre
    have hworld : HasWorld store .shared value :=
      hown.roots_world ⟨.shared, value⟩ (by simp)
    refine ⟨⟨roots, value, houtput, hav, hworld, ?_⟩, hslots⟩
    simpa [borrowResultRoots] using
      hown.dropNoLocation (hsound.stable.const_noLocation hav)
  have hcomposed := EmitSoundBelow.comp (hsound.emits rest slots) hconvert
  simpa [Function.comp_def] using hcomposed

/-- Unbounded counterpart of `asBorrowSlot`: the expression result's shared
owner becomes the explicit owner that a borrowing caller must eventually
release. -/
theorem LowerResultSound.asBorrowSlot
    {ctx : Ctx} {cur : FnDef}
    {input output : VEnv} {emit : Emit} {abs : Nat}
    (hsound : LowerResultSound ctx cur input output .shared emit
      (.slotA abs)) :
    LowerBorrowSound ctx cur input output emit (.slotA abs) true := by
  refine ⟨hsound.stable, ?_⟩
  intro rest slots
  have hconvert : EmitSound ctx cur (_root_.id : Emit)
      (OwnsResultProtected output .shared (.slotA abs) rest slots)
      (OwnsBorrowResultProtected output (.slotA abs) true rest slots) := by
    apply EmitSound.strengthen
    intro store env hpre
    obtain ⟨⟨roots, value, houtput, hav, hown⟩, hslots⟩ := hpre
    have hworld : HasWorld store .shared value :=
      hown.roots_world ⟨.shared, value⟩ (by simp)
    refine ⟨⟨roots, value, houtput, hav, hworld, ?_⟩, hslots⟩
    simpa [borrowResultRoots] using hown
  have hcomposed := EmitSound.comp (hsound.emits rest slots) hconvert
  simpa [Function.comp_def] using hcomposed

/-- Unbounded scalar adapter. A stable constant has no heap location, so its
distinguished logical result owner can be forgotten. -/
theorem LowerResultSound.asBorrowConst
    {ctx : Ctx} {cur : FnDef}
    {input output : VEnv} {emit : Emit} {atom : Atom}
    (hsound : LowerResultSound ctx cur input output .shared emit
      (.constA atom)) :
    LowerBorrowSound ctx cur input output emit (.constA atom) false := by
  refine ⟨hsound.stable, ?_⟩
  intro rest slots
  have hconvert : EmitSound ctx cur (_root_.id : Emit)
      (OwnsResultProtected output .shared (.constA atom) rest slots)
      (OwnsBorrowResultProtected output (.constA atom) false rest slots) := by
    apply EmitSound.strengthen
    intro store env hpre
    obtain ⟨⟨roots, value, houtput, hav, hown⟩, hslots⟩ := hpre
    have hworld : HasWorld store .shared value :=
      hown.roots_world ⟨.shared, value⟩ (by simp)
    refine ⟨⟨roots, value, houtput, hav, hworld, ?_⟩, hslots⟩
    simpa [borrowResultRoots] using
      hown.dropNoLocation (hsound.stable.const_noLocation hav)
  have hcomposed := EmitSound.comp (hsound.emits rest slots) hconvert
  simpa [Function.comp_def] using hcomposed

/-- Semantic slot adapter: the result graph is preserved while its shared
root is reclassified as the borrowing caller's pending owner. -/
theorem LowerResultValueSound.asBorrowSlot
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef}
    {input output : VEnv}
    {sourceInput sourceOutput : List IxIR0.Value}
    {sourceValue : IxIR0.Value} {emit : Emit} {abs : Nat}
    (hsound : LowerResultValueSound funRel recSelfRel ctx cur
      input output sourceInput sourceOutput sourceValue .shared emit
      (.slotA abs)) :
    LowerBorrowValueSound funRel recSelfRel ctx cur
      input output sourceInput sourceOutput sourceValue emit
      (.slotA abs) true := by
  refine
    { toLowerBorrowSound :=
        hsound.toLowerResultSound.asBorrowSlot
      graphEmits := ?_ }
  intro sourceRest rest slots
  have hconvert : EmitSound ctx cur (_root_.id : Emit)
      (GraphOwnsResultProtected funRel recSelfRel output sourceOutput
        sourceValue .shared (.slotA abs) sourceRest rest slots)
      (GraphOwnsBorrowResultProtected funRel recSelfRel output sourceOutput
        sourceValue (.slotA abs) true sourceRest rest slots) := by
    apply EmitSound.strengthen
    intro store env hpre
    obtain ⟨⟨roots, value, houtput, hav, hvalueGraph,
        hrestGraph, hown⟩, hslots⟩ := hpre
    have hworld : HasWorld store .shared value :=
      hown.roots_world ⟨.shared, value⟩ (by simp)
    refine ⟨roots, value, houtput, hav, hworld, hvalueGraph,
      hrestGraph, ?_, hslots⟩
    simpa [borrowResultRoots] using hown
  have hcomposed := EmitSound.comp
    (hsound.graphEmits sourceRest rest slots) hconvert
  simpa [Function.comp_def] using hcomposed

/-- Semantic scalar adapter: dropping the ownership-inert result root leaves
the source/result graph and caller-frame graph unchanged. -/
theorem LowerResultValueSound.asBorrowConst
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef}
    {input output : VEnv}
    {sourceInput sourceOutput : List IxIR0.Value}
    {sourceValue : IxIR0.Value} {emit : Emit} {atom : Atom}
    (hsound : LowerResultValueSound funRel recSelfRel ctx cur
      input output sourceInput sourceOutput sourceValue .shared emit
      (.constA atom)) :
    LowerBorrowValueSound funRel recSelfRel ctx cur
      input output sourceInput sourceOutput sourceValue emit
      (.constA atom) false := by
  refine
    { toLowerBorrowSound :=
        hsound.toLowerResultSound.asBorrowConst
      graphEmits := ?_ }
  intro sourceRest rest slots
  have hconvert : EmitSound ctx cur (_root_.id : Emit)
      (GraphOwnsResultProtected funRel recSelfRel output sourceOutput
        sourceValue .shared (.constA atom) sourceRest rest slots)
      (GraphOwnsBorrowResultProtected funRel recSelfRel output sourceOutput
        sourceValue (.constA atom) false sourceRest rest slots) := by
    apply EmitSound.strengthen
    intro store env hpre
    obtain ⟨⟨roots, value, houtput, hav, hvalueGraph,
        hrestGraph, hown⟩, hslots⟩ := hpre
    have hworld : HasWorld store .shared value :=
      hown.roots_world ⟨.shared, value⟩ (by simp)
    refine ⟨roots, value, houtput, hav, hworld, hvalueGraph,
      hrestGraph, ?_, hslots⟩
    simpa [borrowResultRoots] using
      hown.dropNoLocation (hsound.stable.const_noLocation hav)
  have hcomposed := EmitSound.comp
    (hsound.graphEmits sourceRest rest slots) hconvert
  simpa [Function.comp_def] using hcomposed

/-- Fetch a field through a slot-backed shared borrow. Successful execution
itself identifies a live shared constructor and in-bounds field; the pushed
field is tracked as a borrow while every root remains unchanged. -/
theorem fetchBorrowSlot_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {Γ : VEnv}
    {targetAbs index : Nat} {release : Bool}
    {rest : List Root} {slots : List (Nat × RVal)} :
    EmitSoundBelow ctx cur limit
      (emitOp (.fetch (.var (Γ.rel targetAbs)) index))
      (OwnsBorrowResultProtected Γ (.slotA targetAbs) release rest slots)
      (OwnsFetchedBorrowProtected Γ.bump (.slotA targetAbs)
        (.slotA Γ.depth) release rest slots) := by
  apply OpSoundBelow.emit
  intro fuel store env store' result _ hpre hrun
  obtain ⟨⟨roots, targetValue, hΓ, htarget, htargetWorld, hown⟩,
    hslots⟩ := hpre
  have hresolve :
      resolveAtom env (.var (Γ.rel targetAbs)) = .ok targetValue := by
    simpa [AVal.toAtom] using htarget.resolveAtom
  cases fuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    rw [runOp.eq_def] at hrun
    dsimp only at hrun
    rw [hresolve, bindOk] at hrun
    cases targetValue with
    | lit literal => contradiction
    | erased => contradiction
    | loc loc =>
      obtain ⟨box, hget, hboxWorld⟩ := htargetWorld
      cases box with
      | mk boxWorld rc node =>
        dsimp only [NodeBox.world] at hboxWorld
        subst boxWorld
        dsimp only at hrun
        rw [hget] at hrun
        dsimp only at hrun
        cases node with
        | papN f arity args => contradiction
        | ctorN cid fields =>
          dsimp only at hrun
          cases hfield : fields[index]? with
          | none =>
            rw [hfield] at hrun
            contradiction
          | some fieldValue =>
            rw [hfield] at hrun
            have hpair : (store, fieldValue) = (store', result) :=
              Except.ok.inj hrun
            cases hpair
            refine ⟨roots, .loc loc, result, hΓ.bump result,
              AValStable.slot.realize_bump htarget result, ?_,
              ⟨⟨.shared, rc, .ctorN cid fields⟩, hget, rfl⟩,
              hown.fetchBorrowed hget hfield, hown, hslots.bump result⟩
            apply AValRealizes.slot
            · simp [VEnv.bump]
            · simp [VEnv.bump, VEnv.rel]

theorem fetchBorrowSlot
    {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {targetAbs index : Nat} {release : Bool}
    {rest : List Root} {slots : List (Nat × RVal)} :
    EmitSound ctx cur
      (emitOp (.fetch (.var (Γ.rel targetAbs)) index))
      (OwnsBorrowResultProtected Γ (.slotA targetAbs) release rest slots)
      (OwnsFetchedBorrowProtected Γ.bump (.slotA targetAbs)
        (.slotA Γ.depth) release rest slots) :=
  EmitSound.of_below fun limit =>
    fetchBorrowSlot_below (ctx := ctx) (cur := cur) (limit := limit)

/-- Semantic fetch selects the runtime field graph at the same index as the
successful source constructor projection. -/
theorem fetchBorrowSlot_value
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value} {address : Ixon.Address}
    {tag : Nat} {sourceFields : List IxIR0.Value}
    {sourceField : IxIR0.Value} {targetAbs index : Nat}
    {release : Bool} {sourceRest : List (Owned × IxIR0.Value)}
    {rest : List Root} {slots : List (Nat × RVal)}
    (hsourceField : sourceFields[index]? = some sourceField) :
    EmitSound ctx cur
      (emitOp (.fetch (.var (Γ.rel targetAbs)) index))
      (GraphOwnsBorrowResultProtected funRel recSelfRel Γ sourceEnv
        (.ctor address tag sourceFields) (.slotA targetAbs) release
        sourceRest rest slots)
      (GraphOwnsFetchedBorrowProtected funRel recSelfRel Γ.bump sourceEnv
        (.ctor address tag sourceFields) sourceField
        (.slotA targetAbs) (.slotA Γ.depth) release
        sourceRest rest slots) := by
  apply OpSound.emit
  intro fuel store env store' result hpre hrun
  obtain ⟨roots, targetValue, hΓ, htarget, htargetWorld,
      htargetGraph, hrestGraph, hown, hslots⟩ := hpre
  have hresolve :
      resolveAtom env (.var (Γ.rel targetAbs)) = .ok targetValue := by
    simpa [AVal.toAtom] using htarget.resolveAtom
  cases fuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    rw [runOp.eq_def] at hrun
    dsimp only at hrun
    rw [hresolve, bindOk] at hrun
    cases targetValue with
    | lit literal => contradiction
    | erased => contradiction
    | loc loc =>
      obtain ⟨box, hget, hboxWorld⟩ := htargetWorld
      cases box with
      | mk boxWorld rc node =>
        dsimp only [NodeBox.world] at hboxWorld
        subst boxWorld
        dsimp only at hrun
        rw [hget] at hrun
        dsimp only at hrun
        cases node with
        | papN f arity args => contradiction
        | ctorN cid fields =>
          dsimp only at hrun
          cases hfield : fields[index]? with
          | none =>
            rw [hfield] at hrun
            contradiction
          | some fieldValue =>
            rw [hfield] at hrun
            have hpair : (store, fieldValue) = (store', result) :=
              Except.ok.inj hrun
            cases hpair
            obtain ⟨_, _, hfieldsGraph⟩ :=
              htargetGraph.ctor_fields_of_get hget
            obtain ⟨relatedField, hrelatedSlot, hfieldGraph⟩ :=
              hfieldsGraph.get? hsourceField
            have hrelatedArray :
                fields[index]? = some relatedField := by
              simpa using hrelatedSlot
            have hfieldEq : relatedField = result :=
              Option.some.inj (hrelatedArray.symm.trans hfield)
            subst relatedField
            refine ⟨roots, .loc loc, result, hΓ.bump result,
              AValStable.slot.realize_bump htarget result, ?_,
              ⟨⟨.shared, rc, .ctorN cid fields⟩, hget, rfl⟩,
              hown.fetchBorrowed hget hfield, htargetGraph,
              hfieldGraph, hrestGraph, hown, hslots.bump result⟩
            apply AValRealizes.slot
            · simp [VEnv.bump]
            · simp [VEnv.bump, VEnv.rel]

/-- Retain the fetched field into a fresh owned result slot while preserving
the original target borrow across the refcount update. -/
theorem retainFetchedBorrow_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {Γ : VEnv}
    {targetAbs fieldAbs : Nat} {release : Bool}
    {rest : List Root} {slots : List (Nat × RVal)} :
    EmitSoundBelow ctx cur limit
      (emitOp (.dup (.var (Γ.rel fieldAbs))))
      (OwnsFetchedBorrowProtected Γ (.slotA targetAbs)
        (.slotA fieldAbs) release rest slots)
      (OwnsRetainedProjectionProtected Γ.bump (.slotA targetAbs)
        (.slotA Γ.depth) release rest slots) := by
  apply OpSoundBelow.emit
  intro fuel store env store' result _ hpre hrun
  obtain ⟨roots, targetValue, fieldValue, hΓ, htarget, hfield,
    htargetWorld, hfieldWorld, hown, hslots⟩ := hpre
  have hresolve :
      resolveAtom env (.var (Γ.rel fieldAbs)) = .ok fieldValue := by
    simpa [AVal.toAtom] using hfield.resolveAtom
  cases fuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    obtain ⟨nextStore, heval, hownNext, hborrowedNext⟩ :=
      runOp_retain_borrowed_preserves_hasWorlds
        (ctx := ctx) (cur := cur) (fuel := fuel)
        hresolve hfieldWorld hown (borrowed := [targetValue])
        (by
          intro candidate hmem
          simp only [List.mem_singleton] at hmem
          subst candidate
          exact htargetWorld)
    have hpair : (nextStore, fieldValue) = (store', result) :=
      Except.ok.inj (heval.symm.trans hrun)
    cases hpair
    refine ⟨roots, targetValue, result, hΓ.bump result,
      AValStable.slot.realize_bump htarget result, ?_,
      hborrowedNext targetValue (by simp), hownNext,
      hslots.bump result⟩
    apply AValRealizes.slot
    · simp [VEnv.bump]
    · simp [VEnv.bump, VEnv.rel]

theorem retainFetchedBorrow
    {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {targetAbs fieldAbs : Nat} {release : Bool}
    {rest : List Root} {slots : List (Nat × RVal)} :
    EmitSound ctx cur
      (emitOp (.dup (.var (Γ.rel fieldAbs))))
      (OwnsFetchedBorrowProtected Γ (.slotA targetAbs)
        (.slotA fieldAbs) release rest slots)
      (OwnsRetainedProjectionProtected Γ.bump (.slotA targetAbs)
        (.slotA Γ.depth) release rest slots) :=
  EmitSound.of_below fun limit =>
    retainFetchedBorrow_below (ctx := ctx) (cur := cur) (limit := limit)

/-- Semantic retain turns the fetched field graph into a separately owned
result graph and transports all other witnesses through the RC-only update. -/
theorem retainFetchedBorrow_value
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value}
    {sourceTarget sourceField : IxIR0.Value}
    {targetAbs fieldAbs : Nat} {release : Bool}
    {sourceRest : List (Owned × IxIR0.Value)} {rest : List Root}
    {slots : List (Nat × RVal)} :
    EmitSound ctx cur
      (emitOp (.dup (.var (Γ.rel fieldAbs))))
      (GraphOwnsFetchedBorrowProtected funRel recSelfRel Γ sourceEnv
        sourceTarget sourceField (.slotA targetAbs) (.slotA fieldAbs)
        release sourceRest rest slots)
      (GraphOwnsRetainedProjectionProtected funRel recSelfRel Γ.bump
        sourceEnv sourceTarget sourceField (.slotA targetAbs)
        (.slotA Γ.depth) release sourceRest rest slots) := by
  apply OpSound.emit
  intro fuel store env store' result hpre hrun
  obtain ⟨roots, targetValue, fieldValue, hΓ, htarget, hfield,
      htargetWorld, hfieldWorld, htargetGraph, hfieldGraph,
      hrestGraph, hown, hslots⟩ := hpre
  have hresolve :
      resolveAtom env (.var (Γ.rel fieldAbs)) = .ok fieldValue := by
    simpa [AVal.toAtom] using hfield.resolveAtom
  cases fuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    obtain ⟨nextStore, heval, hstore, hfieldGraphNext, hownNext⟩ :=
      runOp_retain_borrowed_valueGraph
        (ctx := ctx) (cur := cur) (fuel := fuel)
        hresolve hfieldWorld hfieldGraph hown
    have hpair : (nextStore, fieldValue) = (store', result) :=
      Except.ok.inj (heval.symm.trans hrun)
    cases hpair
    refine ⟨roots, targetValue, result,
      (hΓ.monoStore hstore).bump result,
      AValStable.slot.realize_bump htarget result, ?_,
      htargetWorld.monoStore hstore, htargetGraph.monoStore hstore,
      hfieldGraphNext, hrestGraph.monoStore hstore,
      hownNext, hslots.bump result⟩
    apply AValRealizes.slot
    · simp [VEnv.bump]
    · simp [VEnv.bump, VEnv.rel]

/-- When the projection target remains owned by the output environment, the
retained field is already the complete expression result. -/
theorem retainedProjection_kept_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {Γ : VEnv}
    {target result : AVal} {rest : List Root}
    {slots : List (Nat × RVal)} :
    EmitSoundBelow ctx cur limit (_root_.id : Emit)
      (OwnsRetainedProjectionProtected Γ target result false rest slots)
      (OwnsResultProtected Γ .shared result rest slots) := by
  apply EmitSoundBelow.strengthen
  intro store env hpre
  obtain ⟨roots, targetValue, resultValue, hΓ, htarget, hresult,
    htargetWorld, hown, hslots⟩ := hpre
  refine ⟨⟨roots, resultValue, hΓ, hresult, ?_⟩, hslots⟩
  simpa [borrowResultRoots] using hown

theorem retainedProjection_kept
    {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {target result : AVal} {rest : List Root}
    {slots : List (Nat × RVal)} :
    EmitSound ctx cur (_root_.id : Emit)
      (OwnsRetainedProjectionProtected Γ target result false rest slots)
      (OwnsResultProtected Γ .shared result rest slots) :=
  EmitSound.of_below fun limit =>
    retainedProjection_kept_below
      (ctx := ctx) (cur := cur) (limit := limit)

/-- Semantic kept-target finish: the separately retained field already has
the graph and exact owner required for the source projection result. -/
theorem retainedProjection_kept_value
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value}
    {sourceTarget sourceField : IxIR0.Value}
    {target result : AVal}
    {sourceRest : List (Owned × IxIR0.Value)} {rest : List Root}
    {slots : List (Nat × RVal)} :
    EmitSound ctx cur (_root_.id : Emit)
      (GraphOwnsRetainedProjectionProtected funRel recSelfRel Γ
        sourceEnv sourceTarget sourceField target result false
        sourceRest rest slots)
      (GraphOwnsResultProtected funRel recSelfRel Γ
        sourceEnv sourceField .shared result sourceRest rest slots) := by
  apply EmitSound.strengthen
  intro store env hpre
  obtain ⟨roots, targetValue, resultValue, hΓ, htarget, hresult,
      htargetWorld, htargetGraph, hresultGraph, hrestGraph,
      hown, hslots⟩ := hpre
  refine ⟨⟨roots, resultValue, hΓ, hresult, hresultGraph,
    hrestGraph, ?_⟩, hslots⟩
  simpa [borrowResultRoots] using hown

/-- Release a final-use projection target after retaining its field. The
inert drop result pushes one slot, while the retained field root and result
descriptor survive as the expression output. -/
theorem releaseRetainedProjection_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {Γ : VEnv}
    {targetAbs resultAbs : Nat} {rest : List Root}
    {slots : List (Nat × RVal)} :
    EmitSoundBelow ctx cur limit
      (emitOp (.drop (.var (Γ.rel targetAbs))))
      (OwnsRetainedProjectionProtected Γ (.slotA targetAbs)
        (.slotA resultAbs) true rest slots)
      (OwnsResultProtected Γ.bump .shared (.slotA resultAbs) rest slots) := by
  intro bound hbound post code hcode
  intro fuel store env finalStore finalValue hfuel hpre hrun
  obtain ⟨roots, targetValue, resultValue, hΓ, htarget, hresult,
    htargetWorld, hown, hslots⟩ := hpre
  let frame : List RVal → Prop := fun oldEnv =>
    VEnvRealizes Γ oldEnv roots ∧
      AValRealizes Γ oldEnv (.slotA resultAbs) resultValue ∧
      SlotsRealize Γ oldEnv slots
  let remainingRoots := ⟨Owned.shared, resultValue⟩ :: roots ++ rest
  have howned : RootOwnership store
      (⟨.shared, targetValue⟩ :: remainingRoots) := by
    apply hown.perm
    simpa [remainingRoots, borrowResultRoots] using
      (List.Perm.swap ⟨Owned.shared, targetValue⟩
        ⟨Owned.shared, resultValue⟩ (roots ++ rest))
  have hnext : CodeOwnsBelow ctx cur bound
      (OwnsAfterPush frame remainingRoots) post code := by
    intro nextFuel nextStore nextEnv resultStore resultValue' hnextFuel
      hpushed hcodeRun
    obtain ⟨pushed, oldEnv, rfl, ⟨hΓOld, hresultOld, hslotsOld⟩,
      hownRest⟩ := hpushed
    apply hcode hnextFuel
    · refine ⟨⟨roots, resultValue, hΓOld.bump pushed,
        AValStable.slot.realize_bump hresultOld pushed, ?_⟩,
        hslotsOld.bump pushed⟩
      simpa [remainingRoots] using hownRest
    · exact hcodeRun
  have hdrop : CodeOwnsBelow ctx cur bound
      (fun dropStore dropEnv =>
        frame dropEnv ∧
          resolveAtom dropEnv (.var (Γ.rel targetAbs)) =
            .ok targetValue ∧
          RootOwnership dropStore
            (⟨.shared, targetValue⟩ :: remainingRoots))
      post (emitOp (.drop (.var (Γ.rel targetAbs))) code) :=
    (emit_drop_value_owned_below (ctx := ctx) (cur := cur)
      (limit := limit) (target := .var (Γ.rel targetAbs))
      (value := targetValue) (rest := remainingRoots) (frame := frame))
      bound hbound post code hnext
  apply hdrop hfuel
  · refine ⟨⟨hΓ, hresult, hslots⟩, ?_, howned⟩
    simpa [AVal.toAtom] using htarget.resolveAtom
  · exact hrun

theorem releaseRetainedProjection
    {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {targetAbs resultAbs : Nat} {rest : List Root}
    {slots : List (Nat × RVal)} :
    EmitSound ctx cur
      (emitOp (.drop (.var (Γ.rel targetAbs))))
      (OwnsRetainedProjectionProtected Γ (.slotA targetAbs)
        (.slotA resultAbs) true rest slots)
      (OwnsResultProtected Γ.bump .shared (.slotA resultAbs) rest slots) :=
  EmitSound.of_below fun limit =>
    releaseRetainedProjection_below
      (ctx := ctx) (cur := cur) (limit := limit)

/-- Semantic final-use finish: after retaining the projected field, dropping
the target restricts the heap without changing surviving node shapes. The
result, environment, and caller-frame graphs therefore transport to the
post-state. -/
theorem releaseRetainedProjection_value
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value}
    {sourceTarget sourceField : IxIR0.Value}
    {targetAbs resultAbs : Nat}
    {sourceRest : List (Owned × IxIR0.Value)} {rest : List Root}
    {slots : List (Nat × RVal)} :
    EmitSound ctx cur
      (emitOp (.drop (.var (Γ.rel targetAbs))))
      (GraphOwnsRetainedProjectionProtected funRel recSelfRel Γ
        sourceEnv sourceTarget sourceField (.slotA targetAbs)
        (.slotA resultAbs) true sourceRest rest slots)
      (GraphOwnsResultProtected funRel recSelfRel Γ.bump
        sourceEnv sourceField .shared (.slotA resultAbs)
        sourceRest rest slots) := by
  apply OpSound.emit
  intro fuel store env store' result hpre hrun
  obtain ⟨roots, targetValue, resultValue, hΓ, htarget, hresult,
      htargetWorld, htargetGraph, hresultGraph, hrestGraph,
      hown, hslots⟩ := hpre
  have hresolve :
      resolveAtom env (.var (Γ.rel targetAbs)) = .ok targetValue := by
    simpa [AVal.toAtom] using htarget.resolveAtom
  cases fuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    let remainingRoots :=
      ⟨Owned.shared, resultValue⟩ :: roots ++ rest
    have howned : RootOwnership store
        (⟨.shared, targetValue⟩ :: remainingRoots) := by
      apply hown.perm
      simpa [remainingRoots, borrowResultRoots] using
        (List.Perm.swap ⟨Owned.shared, targetValue⟩
          ⟨Owned.shared, resultValue⟩ (roots ++ rest))
    obtain ⟨rfl, hrestrict, hownAfter⟩ :=
      runOp_drop_value_owned_restricts hresolve howned hrun
    have hresultWorld : HasWorld store' .shared resultValue :=
      hownAfter.roots_world ⟨.shared, resultValue⟩
        (by simp [remainingRoots])
    have hΓAfter : VEnvValueGraph funRel recSelfRel store'
        Γ sourceEnv env roots :=
      hΓ.ofRestricts hrestrict hownAfter
        (fun root hmember => by
          simp [remainingRoots, hmember])
    have hresultAfter : Sim.ValueGraph funRel store'
        sourceField resultValue :=
      hresultGraph.ofRestricts hrestrict hownAfter hresultWorld
    have hrestAfter : Sim.RootsGraph funRel store'
        sourceRest rest :=
      hrestGraph.ofRestrictsIn hrestrict hownAfter
        (fun root hmember => by
          simp [remainingRoots, hmember])
    refine ⟨⟨roots, resultValue, hΓAfter.bump .erased,
      AValStable.slot.realize_bump hresult .erased,
      hresultAfter, hrestAfter, ?_⟩, hslots.bump .erased⟩
    simpa [remainingRoots] using hownAfter

/-- Finish an erased borrowing result as an ordinary shared expression
result. Erased values have no heap location, so adding the distinguished
result root does not change the ownership accounting. -/
theorem LowerBorrowSoundBelow.returnErased
    {ctx : Ctx} {cur : FnDef} {limit : Nat}
    {input output : VEnv} {emit : Emit} {release : Bool}
    (hsound : LowerBorrowSoundBelow ctx cur limit input output emit
      (.constA .erased) release) :
    LowerResultSoundBelow ctx cur limit input output .shared emit
      (.constA .erased) := by
  refine ⟨.erased, ?_⟩
  intro rest slots
  have hconvert : EmitSoundBelow ctx cur limit (_root_.id : Emit)
      (OwnsBorrowResultProtected output (.constA .erased) release rest slots)
      (OwnsResultProtected output .shared (.constA .erased) rest slots) := by
    apply EmitSoundBelow.strengthen
    intro store env hpre
    obtain ⟨⟨roots, value, houtput, hav, _, hown⟩, hslots⟩ := hpre
    refine ⟨⟨roots, value, houtput, hav, ?_⟩, hslots⟩
    cases release with
    | false =>
      simpa [borrowResultRoots] using
        hown.addNoLocation (hsound.stable.const_noLocation hav)
    | true => simpa [borrowResultRoots] using hown
  have hcomposed := EmitSoundBelow.comp (hsound.emits rest slots) hconvert
  simpa [Function.comp_def] using hcomposed

/-- Unbounded erased-borrow finish. Whether or not the borrowing result
carried a pending logical owner, erased has no heap location and can be
returned at shared world without changing the store. -/
theorem LowerBorrowSound.returnErased
    {ctx : Ctx} {cur : FnDef}
    {input output : VEnv} {emit : Emit} {release : Bool}
    (hsound : LowerBorrowSound ctx cur input output emit
      (.constA .erased) release) :
    LowerResultSound ctx cur input output .shared emit
      (.constA .erased) := by
  refine ⟨.erased, ?_⟩
  intro rest slots
  have hconvert : EmitSound ctx cur (_root_.id : Emit)
      (OwnsBorrowResultProtected output (.constA .erased) release rest slots)
      (OwnsResultProtected output .shared (.constA .erased) rest slots) := by
    apply EmitSound.strengthen
    intro store env hpre
    obtain ⟨⟨roots, value, houtput, hav, _, hown⟩, hslots⟩ := hpre
    refine ⟨⟨roots, value, houtput, hav, ?_⟩, hslots⟩
    cases release with
    | false =>
      simpa [borrowResultRoots] using
        hown.addNoLocation (hsound.stable.const_noLocation hav)
    | true => simpa [borrowResultRoots] using hown
  have hcomposed := EmitSound.comp (hsound.emits rest slots) hconvert
  simpa [Function.comp_def] using hcomposed

/-- Semantic erased-borrow finish. The erased value graph and all framed
graphs are preserved while the ownership-inert result root is exposed. -/
theorem LowerBorrowValueSound.returnErased
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef}
    {input output : VEnv}
    {sourceInput sourceOutput : List IxIR0.Value}
    {emit : Emit} {release : Bool}
    (hsound : LowerBorrowValueSound funRel recSelfRel ctx cur
      input output sourceInput sourceOutput .erased emit
      (.constA .erased) release) :
    LowerResultValueSound funRel recSelfRel ctx cur
      input output sourceInput sourceOutput .erased .shared emit
      (.constA .erased) := by
  refine
    { toLowerResultSound :=
        hsound.toLowerBorrowSound.returnErased
      graphEmits := ?_ }
  intro sourceRest rest slots
  have hconvert : EmitSound ctx cur (_root_.id : Emit)
      (GraphOwnsBorrowResultProtected funRel recSelfRel output
        sourceOutput .erased (.constA .erased) release
        sourceRest rest slots)
      (GraphOwnsResultProtected funRel recSelfRel output
        sourceOutput .erased .shared (.constA .erased)
        sourceRest rest slots) := by
    apply EmitSound.strengthen
    intro store env hpre
    obtain ⟨roots, value, houtput, hav, hworld, hvalueGraph,
        hrestGraph, hown, hslots⟩ := hpre
    refine ⟨⟨roots, value, houtput, hav, hvalueGraph,
      hrestGraph, ?_⟩, hslots⟩
    cases release with
    | false =>
      simpa [borrowResultRoots] using
        hown.addNoLocation (hsound.stable.const_noLocation hav)
    | true => simpa [borrowResultRoots] using hown
  have hcomposed := EmitSound.comp
    (hsound.graphEmits sourceRest rest slots) hconvert
  simpa [Function.comp_def] using hcomposed

/-- Project through a retained slot borrow while keeping its original owner
in the output environment. Fetch adds a borrow and `dup` turns that field
into the owned shared expression result. -/
theorem LowerBorrowSoundBelow.projectSlotKept
    {ctx : Ctx} {cur : FnDef} {limit : Nat}
    {input output : VEnv} {emit : Emit} {targetAbs index : Nat}
    (hsound : LowerBorrowSoundBelow ctx cur limit input output emit
      (.slotA targetAbs) false) :
    LowerResultSoundBelow ctx cur limit input output.bump.bump .shared
      (emit ∘ emitOp (.fetch (.var (output.rel targetAbs)) index) ∘
        emitOp (.dup (.var (output.bump.rel output.depth))))
      (.slotA output.bump.depth) := by
  refine ⟨.slot, ?_⟩
  intro rest slots
  have hfetch := fetchBorrowSlot_below
    (ctx := ctx) (cur := cur) (limit := limit) (Γ := output)
    (targetAbs := targetAbs) (index := index) (release := false)
    (rest := rest) (slots := slots)
  have hretain := retainFetchedBorrow_below
    (ctx := ctx) (cur := cur) (limit := limit) (Γ := output.bump)
    (targetAbs := targetAbs) (fieldAbs := output.depth)
    (release := false) (rest := rest) (slots := slots)
  have hfinish := retainedProjection_kept_below
    (ctx := ctx) (cur := cur) (limit := limit) (Γ := output.bump.bump)
    (target := .slotA targetAbs) (result := .slotA output.bump.depth)
    (rest := rest) (slots := slots)
  have hcomposed := EmitSoundBelow.comp (hsound.emits rest slots)
    (EmitSoundBelow.comp hfetch (EmitSoundBelow.comp hretain hfinish))
  simpa [Function.comp_def] using hcomposed

/-- Project through a final-use slot borrow, retaining the field before
dropping the now-consumed target owner. -/
theorem LowerBorrowSoundBelow.projectSlotReleased
    {ctx : Ctx} {cur : FnDef} {limit : Nat}
    {input output : VEnv} {emit : Emit} {targetAbs index : Nat}
    (hsound : LowerBorrowSoundBelow ctx cur limit input output emit
      (.slotA targetAbs) true) :
    LowerResultSoundBelow ctx cur limit input output.bump.bump.bump .shared
      (emit ∘ emitOp (.fetch (.var (output.rel targetAbs)) index) ∘
        emitOp (.dup (.var (output.bump.rel output.depth))) ∘
        emitOp (.drop (.var (output.bump.bump.rel targetAbs))))
      (.slotA output.bump.depth) := by
  refine ⟨.slot, ?_⟩
  intro rest slots
  have hfetch := fetchBorrowSlot_below
    (ctx := ctx) (cur := cur) (limit := limit) (Γ := output)
    (targetAbs := targetAbs) (index := index) (release := true)
    (rest := rest) (slots := slots)
  have hretain := retainFetchedBorrow_below
    (ctx := ctx) (cur := cur) (limit := limit) (Γ := output.bump)
    (targetAbs := targetAbs) (fieldAbs := output.depth)
    (release := true) (rest := rest) (slots := slots)
  have hfinish := releaseRetainedProjection_below
    (ctx := ctx) (cur := cur) (limit := limit) (Γ := output.bump.bump)
    (targetAbs := targetAbs) (resultAbs := output.bump.depth)
    (rest := rest) (slots := slots)
  have hcomposed := EmitSoundBelow.comp (hsound.emits rest slots)
    (EmitSoundBelow.comp hfetch (EmitSoundBelow.comp hretain hfinish))
  simpa [Function.comp_def] using hcomposed

theorem LowerBorrowSound.projectSlotKept
    {ctx : Ctx} {cur : FnDef}
    {input output : VEnv} {emit : Emit} {targetAbs index : Nat}
    (hsound : LowerBorrowSound ctx cur input output emit
      (.slotA targetAbs) false) :
    LowerResultSound ctx cur input output.bump.bump .shared
      (emit ∘ emitOp (.fetch (.var (output.rel targetAbs)) index) ∘
        emitOp (.dup (.var (output.bump.rel output.depth))))
      (.slotA output.bump.depth) := by
  refine ⟨.slot, ?_⟩
  intro rest slots
  have hfetch := fetchBorrowSlot
    (ctx := ctx) (cur := cur) (Γ := output)
    (targetAbs := targetAbs) (index := index) (release := false)
    (rest := rest) (slots := slots)
  have hretain := retainFetchedBorrow
    (ctx := ctx) (cur := cur) (Γ := output.bump)
    (targetAbs := targetAbs) (fieldAbs := output.depth)
    (release := false) (rest := rest) (slots := slots)
  have hfinish := retainedProjection_kept
    (ctx := ctx) (cur := cur) (Γ := output.bump.bump)
    (target := .slotA targetAbs) (result := .slotA output.bump.depth)
    (rest := rest) (slots := slots)
  have hcomposed := EmitSound.comp (hsound.emits rest slots)
    (EmitSound.comp hfetch (EmitSound.comp hretain hfinish))
  simpa [Function.comp_def] using hcomposed

theorem LowerBorrowSound.projectSlotReleased
    {ctx : Ctx} {cur : FnDef}
    {input output : VEnv} {emit : Emit} {targetAbs index : Nat}
    (hsound : LowerBorrowSound ctx cur input output emit
      (.slotA targetAbs) true) :
    LowerResultSound ctx cur input output.bump.bump.bump .shared
      (emit ∘ emitOp (.fetch (.var (output.rel targetAbs)) index) ∘
        emitOp (.dup (.var (output.bump.rel output.depth))) ∘
        emitOp (.drop (.var (output.bump.bump.rel targetAbs))))
      (.slotA output.bump.depth) := by
  refine ⟨.slot, ?_⟩
  intro rest slots
  have hfetch := fetchBorrowSlot
    (ctx := ctx) (cur := cur) (Γ := output)
    (targetAbs := targetAbs) (index := index) (release := true)
    (rest := rest) (slots := slots)
  have hretain := retainFetchedBorrow
    (ctx := ctx) (cur := cur) (Γ := output.bump)
    (targetAbs := targetAbs) (fieldAbs := output.depth)
    (release := true) (rest := rest) (slots := slots)
  have hfinish := releaseRetainedProjection
    (ctx := ctx) (cur := cur) (Γ := output.bump.bump)
    (targetAbs := targetAbs) (resultAbs := output.bump.depth)
    (rest := rest) (slots := slots)
  have hcomposed := EmitSound.comp (hsound.emits rest slots)
    (EmitSound.comp hfetch (EmitSound.comp hretain hfinish))
  simpa [Function.comp_def] using hcomposed

/-! ### The source evaluator's projection outcomes

Target-side projection is one syntactic form with four descriptor branches,
while the source evaluator distinguishes only constructor data and the
erased absorber. `SourceProject` names that source-side dichotomy so a
single dispatch theorem covers both, and `of_eval` pins it to the real
evaluator rather than to a hand-written reading of it. -/

/-- The two successful outcomes of `IxIR0.eval`'s `.proj` arm: select a
constructor field, or absorb into `◻`. -/
inductive SourceProject (index : Nat) : IxIR0.Value → IxIR0.Value → Prop where
  | ctor {address : Ixon.Address} {tag : Nat}
      {fields : List IxIR0.Value} {value : IxIR0.Value} :
      fields[index]? = some value →
      SourceProject index (.ctor address tag fields) value
  | erased : SourceProject index .erased .erased

/-- Every successful source projection over a successful target evaluation
is one of the two `SourceProject` outcomes. -/
theorem SourceProject.of_eval {srcCtx : IxIR0.Ctx} {sourceFuel : Nat}
    {sourceEnv : List IxIR0.Value} {index : Nat} {source : IxIR0.Expr}
    {sourceTarget sourceValue : IxIR0.Value}
    (htarget : IxIR0.eval srcCtx sourceFuel sourceEnv source =
      .ok sourceTarget)
    (hproject : IxIR0.eval srcCtx (sourceFuel + 1) sourceEnv
      (.proj index source) = .ok sourceValue) :
    SourceProject index sourceTarget sourceValue := by
  rw [IxIR0.eval.eq_def] at hproject
  dsimp only at hproject
  rw [htarget, bindOk] at hproject
  cases sourceTarget with
  | clos uses env body => exact absurd hproject (by simp)
  | pap head args => exact absurd hproject (by simp)
  | lit literal => exact absurd hproject (by simp)
  | erased =>
    dsimp only at hproject
    have hvalue : IxIR0.Value.erased = sourceValue :=
      Except.ok.inj hproject
    subst hvalue
    exact .erased
  | ctor address tag fields =>
    dsimp only at hproject
    cases hfield : fields[index]? with
    | none =>
      rw [hfield] at hproject
      exact absurd hproject (by simp)
    | some field =>
      rw [hfield] at hproject
      have hvalue : field = sourceValue := Except.ok.inj hproject
      subst hvalue
      exact .ctor hfield

/-- Semantic projection through a retained slot. The source constructor-field
lookup selects the same field graph that `fetch` returns, and `dup` gives it
the distinguished shared result owner. -/
theorem LowerBorrowValueSound.projectSlotKept
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef}
    {input output : VEnv}
    {sourceInput sourceOutput : List IxIR0.Value}
    {address : Ixon.Address} {tag : Nat}
    {sourceFields : List IxIR0.Value} {sourceField : IxIR0.Value}
    {emit : Emit} {targetAbs index : Nat}
    (hsound : LowerBorrowValueSound funRel recSelfRel ctx cur
      input output sourceInput sourceOutput
      (.ctor address tag sourceFields) emit (.slotA targetAbs) false)
    (hsourceField : sourceFields[index]? = some sourceField) :
    LowerResultValueSound funRel recSelfRel ctx cur
      input output.bump.bump sourceInput sourceOutput sourceField .shared
      (emit ∘ emitOp (.fetch (.var (output.rel targetAbs)) index) ∘
        emitOp (.dup (.var (output.bump.rel output.depth))))
      (.slotA output.bump.depth) := by
  refine
    { toLowerResultSound :=
        hsound.toLowerBorrowSound.projectSlotKept
      graphEmits := ?_ }
  intro sourceRest rest slots
  have hfetch := fetchBorrowSlot_value
    (funRel := funRel) (recSelfRel := recSelfRel)
    (ctx := ctx) (cur := cur) (Γ := output)
    (sourceEnv := sourceOutput) (address := address) (tag := tag)
    (targetAbs := targetAbs) (index := index) (release := false)
    (sourceRest := sourceRest) (rest := rest) (slots := slots)
    hsourceField
  have hretain := retainFetchedBorrow_value
    (funRel := funRel) (recSelfRel := recSelfRel)
    (ctx := ctx) (cur := cur) (Γ := output.bump)
    (sourceEnv := sourceOutput)
    (sourceTarget := .ctor address tag sourceFields)
    (sourceField := sourceField) (targetAbs := targetAbs)
    (fieldAbs := output.depth) (release := false)
    (sourceRest := sourceRest) (rest := rest) (slots := slots)
  have hfinish := retainedProjection_kept_value
    (funRel := funRel) (recSelfRel := recSelfRel)
    (ctx := ctx) (cur := cur) (Γ := output.bump.bump)
    (sourceEnv := sourceOutput)
    (sourceTarget := .ctor address tag sourceFields)
    (sourceField := sourceField) (target := .slotA targetAbs)
    (result := .slotA output.bump.depth)
    (sourceRest := sourceRest) (rest := rest) (slots := slots)
  have hcomposed := EmitSound.comp
    (hsound.graphEmits sourceRest rest slots)
    (EmitSound.comp hfetch (EmitSound.comp hretain hfinish))
  simpa [Function.comp_def] using hcomposed

/-- Semantic projection through a final-use slot. The retained field remains
graph-related after the target's destructive release because the release
proof transports every surviving root through the resulting store
restriction. -/
theorem LowerBorrowValueSound.projectSlotReleased
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef}
    {input output : VEnv}
    {sourceInput sourceOutput : List IxIR0.Value}
    {address : Ixon.Address} {tag : Nat}
    {sourceFields : List IxIR0.Value} {sourceField : IxIR0.Value}
    {emit : Emit} {targetAbs index : Nat}
    (hsound : LowerBorrowValueSound funRel recSelfRel ctx cur
      input output sourceInput sourceOutput
      (.ctor address tag sourceFields) emit (.slotA targetAbs) true)
    (hsourceField : sourceFields[index]? = some sourceField) :
    LowerResultValueSound funRel recSelfRel ctx cur
      input output.bump.bump.bump sourceInput sourceOutput sourceField .shared
      (emit ∘ emitOp (.fetch (.var (output.rel targetAbs)) index) ∘
        emitOp (.dup (.var (output.bump.rel output.depth))) ∘
        emitOp (.drop (.var (output.bump.bump.rel targetAbs))))
      (.slotA output.bump.depth) := by
  refine
    { toLowerResultSound :=
        hsound.toLowerBorrowSound.projectSlotReleased
      graphEmits := ?_ }
  intro sourceRest rest slots
  have hfetch := fetchBorrowSlot_value
    (funRel := funRel) (recSelfRel := recSelfRel)
    (ctx := ctx) (cur := cur) (Γ := output)
    (sourceEnv := sourceOutput) (address := address) (tag := tag)
    (targetAbs := targetAbs) (index := index) (release := true)
    (sourceRest := sourceRest) (rest := rest) (slots := slots)
    hsourceField
  have hretain := retainFetchedBorrow_value
    (funRel := funRel) (recSelfRel := recSelfRel)
    (ctx := ctx) (cur := cur) (Γ := output.bump)
    (sourceEnv := sourceOutput)
    (sourceTarget := .ctor address tag sourceFields)
    (sourceField := sourceField) (targetAbs := targetAbs)
    (fieldAbs := output.depth) (release := true)
    (sourceRest := sourceRest) (rest := rest) (slots := slots)
  have hfinish := releaseRetainedProjection_value
    (funRel := funRel) (recSelfRel := recSelfRel)
    (ctx := ctx) (cur := cur) (Γ := output.bump.bump)
    (sourceEnv := sourceOutput)
    (sourceTarget := .ctor address tag sourceFields)
    (sourceField := sourceField) (targetAbs := targetAbs)
    (resultAbs := output.bump.depth)
    (sourceRest := sourceRest) (rest := rest) (slots := slots)
  have hcomposed := EmitSound.comp
    (hsound.graphEmits sourceRest rest slots)
    (EmitSound.comp hfetch (EmitSound.comp hretain hfinish))
  simpa [Function.comp_def] using hcomposed

/-! ### Projection branches unreachable at their source shape

The compiler chooses a projection branch from the borrow *descriptor*, which
is independent of the source target's shape. The two mismatched pairings
below are therefore genuine proof obligations rather than syntactic
impossibilities, and both are discharged by showing that no execution
reaches them. -/

/-- Fetching a field from an erased source target can never succeed. The
borrowed runtime value is either the erased scalar itself or — through the
abstract function relation — a pap node, and `fetch` rejects both. -/
theorem fetchErasedSlot_false
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value} {targetAbs index : Nat}
    {release : Bool} {sourceRest : List (Owned × IxIR0.Value)}
    {rest : List Root} {slots : List (Nat × RVal)} :
    EmitSound ctx cur
      (emitOp (.fetch (.var (Γ.rel targetAbs)) index))
      (GraphOwnsBorrowResultProtected funRel recSelfRel Γ sourceEnv
        .erased (.slotA targetAbs) release sourceRest rest slots)
      (fun _ _ => False) := by
  apply OpSound.emit
  intro fuel store env store' result hpre hrun
  obtain ⟨roots, targetValue, hΓ, htarget, htargetWorld,
      htargetGraph, hrestGraph, hown, hslots⟩ := hpre
  have hresolve :
      resolveAtom env (.var (Γ.rel targetAbs)) = .ok targetValue := by
    simpa [AVal.toAtom] using htarget.resolveAtom
  cases fuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    rw [runOp.eq_def] at hrun
    dsimp only at hrun
    rw [hresolve, bindOk] at hrun
    cases htargetGraph with
    | erased => contradiction
    | function hget _ _ =>
      dsimp only at hrun
      rw [hget] at hrun
      dsimp only at hrun
      contradiction

/-- A constructor-shaped source target is never realized by the erased
scalar, so the descriptor-absorbing branch is unreachable with constructor
data. The ownership half is the ordinary erased finish. -/
theorem LowerBorrowValueSound.projectCtorErased
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef}
    {input output : VEnv}
    {sourceInput sourceOutput : List IxIR0.Value}
    {address : Ixon.Address} {tag : Nat}
    {sourceFields : List IxIR0.Value} {sourceValue : IxIR0.Value}
    {emit : Emit} {release : Bool}
    (hsound : LowerBorrowValueSound funRel recSelfRel ctx cur
      input output sourceInput sourceOutput
      (.ctor address tag sourceFields) emit (.constA .erased) release) :
    LowerResultValueSound funRel recSelfRel ctx cur
      input output sourceInput sourceOutput sourceValue .shared emit
      (.constA .erased) := by
  refine
    { toLowerResultSound := hsound.toLowerBorrowSound.returnErased
      graphEmits := ?_ }
  intro sourceRest rest slots
  apply EmitSound.ofFalseMid
  apply EmitSound.comp (hsound.graphEmits sourceRest rest slots)
  apply EmitSound.strengthen
  intro store env hpre
  obtain ⟨roots, value, _, hav, _, hgraph, _, _, _⟩ := hpre
  cases hav with
  | const hresolve =>
    simp only [resolveAtom] at hresolve
    have hvalue : RVal.erased = value := Except.ok.inj hresolve
    subst hvalue
    cases hgraph

/-- Erased-target projection through a retained slot. The emitted `fetch`
cannot succeed, so the branch transports the source projection result
whatever it is. -/
theorem LowerBorrowValueSound.projectSlotKeptErased
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef}
    {input output : VEnv}
    {sourceInput sourceOutput : List IxIR0.Value}
    {sourceValue : IxIR0.Value}
    {emit : Emit} {targetAbs index : Nat}
    (hsound : LowerBorrowValueSound funRel recSelfRel ctx cur
      input output sourceInput sourceOutput .erased emit
      (.slotA targetAbs) false) :
    LowerResultValueSound funRel recSelfRel ctx cur
      input output.bump.bump sourceInput sourceOutput sourceValue .shared
      (emit ∘ emitOp (.fetch (.var (output.rel targetAbs)) index) ∘
        emitOp (.dup (.var (output.bump.rel output.depth))))
      (.slotA output.bump.depth) := by
  refine
    { toLowerResultSound :=
        hsound.toLowerBorrowSound.projectSlotKept
      graphEmits := ?_ }
  intro sourceRest rest slots
  exact EmitSound.comp (hsound.graphEmits sourceRest rest slots)
    (EmitSound.comp
      (fetchErasedSlot_false (funRel := funRel) (recSelfRel := recSelfRel)
        (ctx := ctx) (cur := cur) (Γ := output) (sourceEnv := sourceOutput)
        (targetAbs := targetAbs) (index := index) (release := false)
        (sourceRest := sourceRest) (rest := rest) (slots := slots))
      EmitSound.ofFalse)

/-- Erased-target projection through a final-use slot: the same unreachable
`fetch`, one emitted `drop` further along. -/
theorem LowerBorrowValueSound.projectSlotReleasedErased
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef}
    {input output : VEnv}
    {sourceInput sourceOutput : List IxIR0.Value}
    {sourceValue : IxIR0.Value}
    {emit : Emit} {targetAbs index : Nat}
    (hsound : LowerBorrowValueSound funRel recSelfRel ctx cur
      input output sourceInput sourceOutput .erased emit
      (.slotA targetAbs) true) :
    LowerResultValueSound funRel recSelfRel ctx cur
      input output.bump.bump.bump sourceInput sourceOutput sourceValue
      .shared
      (emit ∘ emitOp (.fetch (.var (output.rel targetAbs)) index) ∘
        emitOp (.dup (.var (output.bump.rel output.depth))) ∘
        emitOp (.drop (.var (output.bump.bump.rel targetAbs))))
      (.slotA output.bump.depth) := by
  refine
    { toLowerResultSound :=
        hsound.toLowerBorrowSound.projectSlotReleased
      graphEmits := ?_ }
  intro sourceRest rest slots
  exact EmitSound.comp (hsound.graphEmits sourceRest rest slots)
    (EmitSound.comp
      (fetchErasedSlot_false (funRel := funRel) (recSelfRel := recSelfRel)
        (ctx := ctx) (cur := cur) (Γ := output) (sourceEnv := sourceOutput)
        (targetAbs := targetAbs) (index := index) (release := true)
        (sourceRest := sourceRest) (rest := rest) (slots := slots))
      EmitSound.ofFalse)

/-- A stable constant cannot successfully act as a constructor target.
Consequently the faithfully emitted scalar `fetch` branch is sound by
vacuity for every successful target execution. -/
theorem LowerBorrowSoundBelow.projectConst
    {ctx : Ctx} {cur : FnDef} {limit : Nat}
    {input output : VEnv} {emit : Emit} {atom : Atom} {index : Nat}
    {release : Bool}
    (hsound : LowerBorrowSoundBelow ctx cur limit input output emit
      (.constA atom) release) :
    LowerResultSoundBelow ctx cur limit input output.bump .shared
      (emit ∘ emitOp (.fetch atom index)) (.slotA output.depth) := by
  refine ⟨.slot, ?_⟩
  intro rest slots
  have hfetch : EmitSoundBelow ctx cur limit
      (emitOp (.fetch atom index))
      (OwnsBorrowResultProtected output (.constA atom) release rest slots)
      (OwnsResultProtected output.bump .shared (.slotA output.depth)
        rest slots) := by
    apply OpSoundBelow.emit
    intro fuel store env store' result _ _ hrun
    cases hsound.stable <;> cases fuel with
    | zero => simp [runOp] at hrun
    | succ fuel =>
      rw [runOp.eq_def] at hrun
      simp [resolveAtom, bindOk] at hrun
  have hcomposed := EmitSoundBelow.comp (hsound.emits rest slots) hfetch
  simpa [Function.comp_def] using hcomposed

/-- Unbounded scalar-target projection. -/
theorem LowerBorrowSound.projectConst
    {ctx : Ctx} {cur : FnDef}
    {input output : VEnv} {emit : Emit} {atom : Atom} {index : Nat}
    {release : Bool}
    (hsound : LowerBorrowSound ctx cur input output emit
      (.constA atom) release) :
    LowerResultSound ctx cur input output.bump .shared
      (emit ∘ emitOp (.fetch atom index)) (.slotA output.depth) := by
  refine ⟨.slot, ?_⟩
  intro rest slots
  have hfetch : EmitSound ctx cur (emitOp (.fetch atom index))
      (OwnsBorrowResultProtected output (.constA atom) release rest slots)
      (OwnsResultProtected output.bump .shared (.slotA output.depth)
        rest slots) := by
    apply OpSound.emit
    intro fuel store env store' result _ hrun
    cases hsound.stable <;> cases fuel with
    | zero => simp [runOp] at hrun
    | succ fuel =>
      rw [runOp.eq_def] at hrun
      simp [resolveAtom, bindOk] at hrun
  have hcomposed := EmitSound.comp (hsound.emits rest slots) hfetch
  simpa [Function.comp_def] using hcomposed

/-- Semantic scalar-target projection. Vacuity is independent of the source
side, so the branch transports whatever the source evaluator produced. -/
theorem LowerBorrowValueSound.projectConst
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef}
    {input output : VEnv}
    {sourceInput sourceOutput : List IxIR0.Value}
    {sourceTarget sourceValue : IxIR0.Value}
    {emit : Emit} {atom : Atom} {index : Nat} {release : Bool}
    (hsound : LowerBorrowValueSound funRel recSelfRel ctx cur
      input output sourceInput sourceOutput sourceTarget emit
      (.constA atom) release) :
    LowerResultValueSound funRel recSelfRel ctx cur
      input output.bump sourceInput sourceOutput sourceValue .shared
      (emit ∘ emitOp (.fetch atom index)) (.slotA output.depth) := by
  refine
    { toLowerResultSound := hsound.toLowerBorrowSound.projectConst
      graphEmits := ?_ }
  intro sourceRest rest slots
  have hfetch : EmitSound ctx cur (emitOp (.fetch atom index))
      (GraphOwnsBorrowResultProtected funRel recSelfRel output
        sourceOutput sourceTarget (.constA atom) release
        sourceRest rest slots)
      (GraphOwnsResultProtected funRel recSelfRel output.bump
        sourceOutput sourceValue .shared (.slotA output.depth)
        sourceRest rest slots) := by
    apply OpSound.emit
    intro fuel store env store' result _ hrun
    cases hsound.stable <;> cases fuel with
    | zero => simp [runOp] at hrun
    | succ fuel =>
      rw [runOp.eq_def] at hrun
      simp [resolveAtom, bindOk] at hrun
  have hcomposed := EmitSound.comp
    (hsound.graphEmits sourceRest rest slots) hfetch
  simpa [Function.comp_def] using hcomposed

/-! ## Left-to-right argument sequencing -/

/-- Pointwise realization of lowered arguments. The world list is carried in
lockstep so `rootsForWorlds` is exact rather than truncating. -/
inductive AValsRealize (Γ : VEnv) (env : List RVal) :
    List Owned → List AVal → List RVal → Prop where
  | nil : AValsRealize Γ env [] [] []
  | cons {world : Owned} {worlds : List Owned} {av : AVal}
      {avs : List AVal} {value : RVal} {values : List RVal} :
      AValRealizes Γ env av value →
      AValsRealize Γ env worlds avs values →
      AValsRealize Γ env (world :: worlds) (av :: avs) (value :: values)

theorem AValsRealize.lengths {Γ : VEnv} {env : List RVal} :
    ∀ {worlds : List Owned} {avs : List AVal} {values : List RVal},
      AValsRealize Γ env worlds avs values →
      worlds.length = avs.length ∧ avs.length = values.length := by
  intro worlds avs values h
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ ih => exact ⟨by simp [ih.1], by simp [ih.2]⟩

private theorem AValsRealize.resolveAtomsFrom {Γ : VEnv} {env : List RVal} :
    ∀ {worlds : List Owned} {avs : List AVal} {values : List RVal},
      AValsRealize Γ env worlds avs values →
      ∀ accum,
        (avs.map (·.toAtom Γ)).toArray.foldlM
          (fun acc atom => do pure (acc ++ [← resolveAtom env atom])) accum =
        .ok (accum ++ values) := by
  intro worlds avs values h
  induction h with
  | nil =>
    intro accum
    simp only [List.map_nil, List.foldlM_toArray, List.foldlM_nil,
      List.append_nil]
    rfl
  | @cons world worlds av avs value values hav htail ih =>
    intro accum
    simp only [List.map_cons, List.foldlM_toArray, List.foldlM_cons]
    rw [hav.resolveAtom]
    simp only [bindOk]
    simpa [List.append_assoc] using ih (accum ++ [value])

/-- The atom array emitted by `knownCall` resolves to exactly the values
tracked by `AValsRealize`, in source argument order. -/
theorem AValsRealize.resolveAtoms {Γ : VEnv} {env : List RVal}
    {worlds : List Owned} {avs : List AVal} {values : List RVal}
    (h : AValsRealize Γ env worlds avs values) :
    resolveAtoms env (avs.map (·.toAtom Γ)).toArray = .ok values := by
  unfold Compilatrix.IxIR1.resolveAtoms
  simpa using h.resolveAtomsFrom []

theorem rootsForWorlds_replicate_eq_rootsFor (world : Owned) :
    ∀ {values : List RVal} {count : Nat}, values.length = count →
      rootsForWorlds (List.replicate count world) values =
        rootsFor world values := by
  intro values count hlength
  induction values generalizing count with
  | nil =>
    cases count <;> simp_all [rootsFor, rootsForWorlds]
  | cons value values ih =>
    cases count with
    | zero => simp at hlength
    | succ count =>
      simp only [List.length_cons, Nat.succ.injEq] at hlength
      simp [List.replicate_succ, rootsFor, ih hlength]

/-- Exact state after lowering an argument list: argument roots precede the
still-held source-environment roots, ready for allocation or a known call. -/
def OwnsArgsResult (Γ : VEnv) (worlds : List Owned) (avs : List AVal)
    (rest : List Root) : StatePred :=
  fun store env => ∃ roots values,
    VEnvRealizes Γ env roots ∧
    AValsRealize Γ env worlds avs values ∧
    RootOwnership store (rootsForWorlds worlds values ++ roots ++ rest)

def OwnsArgsResultProtected (Γ : VEnv) (worlds : List Owned)
    (avs : List AVal) (rest : List Root)
    (slots : List (Nat × RVal)) : StatePred :=
  fun store env => OwnsArgsResult Γ worlds avs rest store env ∧
    SlotsRealize Γ env slots

/-- Semantic argument-list postcondition. It relates each lowered argument
to its pure source value and keeps the caller's semantic root frame intact. -/
def GraphOwnsArgsResult (funRel : Sim.FunctionRel)
    (recSelfRel : RecSelfRel) (Γ : VEnv)
    (sourceEnv sourceValues : List IxIR0.Value)
    (worlds : List Owned) (avs : List AVal)
    (sourceRest : List (Owned × IxIR0.Value))
    (rest : List Root) : StatePred :=
  fun store env => ∃ roots values,
    VEnvValueGraph funRel recSelfRel store Γ sourceEnv env roots ∧
    AValsRealize Γ env worlds avs values ∧
    Sim.ValuesGraph funRel store sourceValues values ∧
    Sim.RootsGraph funRel store sourceRest rest ∧
    RootOwnership store (rootsForWorlds worlds values ++ roots ++ rest)

def GraphOwnsArgsResultProtected (funRel : Sim.FunctionRel)
    (recSelfRel : RecSelfRel) (Γ : VEnv)
    (sourceEnv sourceValues : List IxIR0.Value)
    (worlds : List Owned) (avs : List AVal)
    (sourceRest : List (Owned × IxIR0.Value))
    (rest : List Root) (slots : List (Nat × RVal)) : StatePred :=
  fun store env =>
    GraphOwnsArgsResult funRel recSelfRel Γ sourceEnv sourceValues
      worlds avs sourceRest rest store env ∧
    SlotsRealize Γ env slots

inductive AValsStable : List AVal → Prop where
  | nil : AValsStable []
  | cons {av : AVal} {avs : List AVal} :
      AValStable av → AValsStable avs → AValsStable (av :: avs)

/-- Stable argument descriptors remain valid after an unrelated operation
pushes one runtime value. Absolute slots are re-indexed through the bumped
`VEnv`; constants are environment-independent. -/
theorem AValsStable.realize_bump {Γ : VEnv} {env : List RVal} :
    ∀ {worlds : List Owned} {avs : List AVal} {values : List RVal},
      AValsStable avs →
      AValsRealize Γ env worlds avs values →
      ∀ pushed, AValsRealize Γ.bump (pushed :: env) worlds avs values := by
  intro worlds avs values hstable hreal pushed
  induction hstable generalizing worlds values with
  | nil =>
    cases hreal
    exact .nil
  | cons hhead htail ih =>
    cases hreal with
    | cons hav havs =>
      apply AValsRealize.cons
      · exact hhead.realize_of_protection hav
          ((hhead.protection_realized hav).bump pushed)
      · exact ih havs

/-- Soundness package for one successful `lowerArgs` result. -/
structure LowerArgsSound (ctx : Ctx) (cur : FnDef)
    (input output : VEnv) (worlds : List Owned)
    (emit : Emit) (avs : List AVal) : Prop where
  stable : AValsStable avs
  emits : ∀ rest slots,
    EmitSound ctx cur emit (OwnsVEnvProtected input rest slots)
      (OwnsArgsResultProtected output worlds avs rest slots)

/-- Companion semantic refinement for left-to-right argument lowering. -/
structure LowerArgsValueSound (funRel : Sim.FunctionRel)
    (recSelfRel : RecSelfRel) (ctx : Ctx) (cur : FnDef)
    (input output : VEnv)
    (sourceInput sourceOutput sourceValues : List IxIR0.Value)
    (worlds : List Owned) (emit : Emit) (avs : List AVal) : Prop
    extends LowerArgsSound ctx cur input output worlds emit avs where
  graphEmits : ∀ sourceRest rest slots,
    EmitSound ctx cur emit
      (GraphOwnsVEnvProtected funRel recSelfRel input
        sourceInput sourceRest rest slots)
      (GraphOwnsArgsResultProtected funRel recSelfRel output
        sourceOutput sourceValues worlds avs sourceRest rest slots)

/-- Fuel-bounded left-to-right argument-lowering soundness. -/
structure LowerArgsSoundBelow (ctx : Ctx) (cur : FnDef)
    (limit : Nat) (input output : VEnv) (worlds : List Owned)
    (emit : Emit) (avs : List AVal) : Prop where
  stable : AValsStable avs
  emits : ∀ rest slots,
    EmitSoundBelow ctx cur limit emit
      (OwnsVEnvProtected input rest slots)
      (OwnsArgsResultProtected output worlds avs rest slots)

/-- Uniform bounded argument soundness closes to the unbounded interface. -/
theorem LowerArgsSound.of_below {ctx : Ctx} {cur : FnDef}
    {input output : VEnv} {worlds : List Owned}
    {emit : Emit} {avs : List AVal}
    (hsound : ∀ limit,
      LowerArgsSoundBelow ctx cur limit input output worlds emit avs) :
    LowerArgsSound ctx cur input output worlds emit avs := by
  refine ⟨(hsound 0).stable, ?_⟩
  intro rest slots
  exact EmitSound.of_below fun limit =>
    (hsound limit).emits rest slots

/-- Bounded argument proofs are contravariant in their fuel bound. -/
theorem LowerArgsSoundBelow.mono {ctx : Ctx} {cur : FnDef}
    {smaller larger : Nat} {input output : VEnv}
    {worlds : List Owned} {emit : Emit} {avs : List AVal}
    (hsound : LowerArgsSoundBelow ctx cur larger input output worlds emit avs)
    (hbound : smaller ≤ larger) :
    LowerArgsSoundBelow ctx cur smaller input output worlds emit avs := by
  refine ⟨hsound.stable, ?_⟩
  intro rest slots bound hsmall
  exact hsound.emits rest slots bound (Nat.le_trans hsmall hbound)

/-- Every compiler-generated declaration and every memoized constructor
wrapper accumulated in a lowering state is present verbatim in the target
evaluator context. The wrapper clause is deliberately indexed by the shape
stored in `WrapperMemo`: it is the layout fact needed by partial constructor
applications, while callable body contracts remain a separate obligation. -/
structure ExtraRepresented (ctx : Ctx) (state : LowSt) : Prop where
  decl : ∀ {address decl}, (address, decl) ∈ state.extra →
    ctx.decls address = some decl
  wrapper : ∀ {memo : WrapperMemo}, memo ∈ state.wrappers →
    ctx.decls memo.wrapper =
      some (ctorWrapperDecl memo.source memo.tag memo.arity)

/-- Exact evaluator contract required only when a logical environment can
actually expose the synthetic recursor-self entry. -/
def CurrentSelfContractBelow (ctx : Ctx) (cur : FnDef)
    (limit : Nat) : Prop :=
  cur.result = .shared ∧
    FnOwnershipContractBelow ctx cur
      (List.replicate cur.arity .shared) limit

/-- The current-function contract is available either substantively, for a
recursor-rule environment, or vacuously because the logical environment has
no `recSelf` entry. This is the boundary used by ordinary generated bodies. -/
def SelfAvailableBelow (ctx : Ctx) (cur : FnDef) (limit : Nat)
    (input : VEnv) : Prop :=
  CurrentSelfContractBelow ctx cur limit ∨ NoRecSelf input

theorem SelfAvailableBelow.of_contract {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {input : VEnv}
    (hcontract : CurrentSelfContractBelow ctx cur limit) :
    SelfAvailableBelow ctx cur limit input :=
  Or.inl hcontract

theorem SelfAvailableBelow.of_noRecSelf {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {input : VEnv} (hno : NoRecSelf input) :
    SelfAvailableBelow ctx cur limit input :=
  Or.inr hno

/-- Transport self availability through any state-only transformation known
not to synthesize a recursor-self entry. -/
theorem SelfAvailableBelow.mapNoRecSelf
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {input output : VEnv}
    (havailable : SelfAvailableBelow ctx cur limit input)
    (hpreserve : NoRecSelf input → NoRecSelf output) :
    SelfAvailableBelow ctx cur limit output := by
  cases havailable with
  | inl hcontract => exact Or.inl hcontract
  | inr hno => exact Or.inr (hpreserve hno)

theorem SelfAvailableBelow.bump
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {input : VEnv}
    (havailable : SelfAvailableBelow ctx cur limit input) :
    SelfAvailableBelow ctx cur limit input.bump :=
  havailable.mapNoRecSelf NoRecSelf.bump

theorem SelfAvailableBelow.pop
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {input : VEnv}
    (havailable : SelfAvailableBelow ctx cur limit input) :
    SelfAvailableBelow ctx cur limit input.pop :=
  havailable.mapNoRecSelf NoRecSelf.pop

theorem SelfAvailableBelow.setSlot
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {input : VEnv}
    (havailable : SelfAvailableBelow ctx cur limit input)
    (changed abs remaining : Nat) (uses : Uses) (held : Bool) :
    SelfAvailableBelow ctx cur limit
      (input.setEntry changed (.slot abs remaining uses held)) :=
  havailable.mapNoRecSelf
    (fun hno => hno.setSlot changed abs remaining uses held)

theorem SelfAvailableBelow.consSlot
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {input : VEnv}
    (havailable : SelfAvailableBelow ctx cur limit input)
    (abs remaining : Nat) (uses : Uses) (held : Bool) :
    SelfAvailableBelow ctx cur limit
      { input with
        entries := .slot abs remaining uses held :: input.entries } :=
  havailable.mapNoRecSelf
    (fun hno => hno.consSlot abs remaining uses held)

theorem SelfAvailableBelow.lowerE
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat} {input output : VEnv} {world : Owned}
    {expr : IxIR0.Expr} {state finalState : LowSt}
    {emit : Emit} {value : AVal}
    (havailable : SelfAvailableBelow ctx cur limit input)
    (hrun : (lowerE src fuel input world expr).run state =
      .ok (output, emit, value) finalState) :
    SelfAvailableBelow ctx cur limit output :=
  havailable.mapNoRecSelf
    (fun hno => (lowerPreservesNoRecSelf src fuel).expr hrun hno)

theorem SelfAvailableBelow.lowerBorrow
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat} {input output : VEnv} {expr : IxIR0.Expr}
    {state finalState : LowSt} {emit : Emit} {value : AVal}
    {release : Bool}
    (havailable : SelfAvailableBelow ctx cur limit input)
    (hrun : (lowerBorrow src fuel input expr).run state =
      .ok (output, emit, value, release) finalState) :
    SelfAvailableBelow ctx cur limit output :=
  havailable.mapNoRecSelf
    (fun hno => (lowerPreservesNoRecSelf src fuel).borrow hrun hno)

theorem SelfAvailableBelow.lowerArgs
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat} {input output : VEnv}
    {args : List (IxIR0.Expr × Owned)} {state finalState : LowSt}
    {emit : Emit} {values : List AVal}
    (havailable : SelfAvailableBelow ctx cur limit input)
    (hrun : (lowerArgs src fuel input args).run state =
      .ok (output, emit, values) finalState) :
    SelfAvailableBelow ctx cur limit output :=
  havailable.mapNoRecSelf
    (fun hno => (lowerPreservesNoRecSelf src fuel).args hrun hno)

theorem SelfAvailableBelow.applyRest
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat} {input output : VEnv} {resultWorld : Owned}
    {pre : Emit} {function : AVal} {args : List IxIR0.Expr}
    {state finalState : LowSt} {emit : Emit} {value : AVal}
    (havailable : SelfAvailableBelow ctx cur limit input)
    (hrun : (applyRest src fuel input resultWorld pre function args).run state =
      .ok (output, emit, value) finalState) :
    SelfAvailableBelow ctx cur limit output :=
  havailable.mapNoRecSelf
    (fun hno => (lowerPreservesNoRecSelf src fuel).applyRest hrun hno)

/-- Lowering only prepends generated declarations and wrapper memos. Besides
the two exact suffix equations, the relation records that every newly cached
memo was installed together with its exact eta-wrapper declaration. This
turns wrapper-cache reachability into a compositional compiler-state fact. -/
def ExtraExtends (initial final : LowSt) : Prop :=
  ∃ (addedExtra : List (Ixon.Address × Decl))
      (addedWrappers : List WrapperMemo),
    final.extra = addedExtra ++ initial.extra ∧
    final.wrappers = addedWrappers ++ initial.wrappers ∧
    ∀ memo, memo ∈ addedWrappers →
      (memo.wrapper,
        ctorWrapperDecl memo.source memo.tag memo.arity) ∈ final.extra

theorem ExtraExtends.refl (state : LowSt) : ExtraExtends state state := by
  refine ⟨[], [], by simp, by simp, ?_⟩
  simp

theorem ExtraExtends.trans {first middle final : LowSt}
    (hfirst : ExtraExtends first middle)
    (hsecond : ExtraExtends middle final) :
    ExtraExtends first final := by
  obtain ⟨leftExtra, leftWrappers, hleftExtra, hleftWrappers,
    hleftSound⟩ := hfirst
  obtain ⟨rightExtra, rightWrappers, hrightExtra, hrightWrappers,
    hrightSound⟩ := hsecond
  refine ⟨rightExtra ++ leftExtra, rightWrappers ++ leftWrappers,
    ?_, ?_, ?_⟩
  · simp [hrightExtra, hleftExtra, List.append_assoc]
  · simp [hrightWrappers, hleftWrappers, List.append_assoc]
  · intro memo hmember
    rw [List.mem_append] at hmember
    cases hmember with
    | inl hright => exact hrightSound memo hright
    | inr hleft =>
      rw [hrightExtra]
      exact List.mem_append_right _ (hleftSound memo hleft)

/-- Wrapper memos, like generated declarations, are never removed. -/
theorem ExtraExtends.wrapper_mem {initial final : LowSt}
    (hextends : ExtraExtends initial final) {memo : WrapperMemo}
    (hmember : memo ∈ initial.wrappers) : memo ∈ final.wrappers := by
  obtain ⟨_, addedWrappers, _, hwrappers, _⟩ := hextends
  rw [hwrappers]
  exact List.mem_append_right addedWrappers hmember

/-- Generated declarations, like wrapper memos, are never removed. -/
theorem ExtraExtends.extra_mem {initial final : LowSt}
    (hextends : ExtraExtends initial final)
    {item : Ixon.Address × Decl}
    (hmember : item ∈ initial.extra) : item ∈ final.extra := by
  obtain ⟨addedExtra, _, hextra, _, _⟩ := hextends
  rw [hextra]
  exact List.mem_append_right addedExtra hmember

/-- A final generated-declaration layout also represents every earlier
state whose extras are a suffix of that final accumulation. -/
theorem ExtraRepresented.of_extends {ctx : Ctx} {initial final : LowSt}
    (hfinal : ExtraRepresented ctx final)
    (hextends : ExtraExtends initial final) :
    ExtraRepresented ctx initial := by
  obtain ⟨addedExtra, addedWrappers, hextra, hwrappers, _⟩ := hextends
  constructor
  · intro address decl hmember
    apply hfinal.decl
    rw [hextra]
    exact List.mem_append_right addedExtra hmember
  · intro memo hmember
    apply hfinal.wrapper
    rw [hwrappers]
    exact List.mem_append_right addedWrappers hmember

/-- A run beginning at the empty compiler state automatically satisfies the
wrapper half of `ExtraRepresented`: every final memo belongs to the added
prefix and `ExtraExtends.wrapper_extra` supplies its declaration. -/
theorem ExtraExtends.represented_of_empty {ctx : Ctx} {final : LowSt}
    (hextends : ExtraExtends ({} : LowSt) final)
    (hdecls : ∀ {address decl}, (address, decl) ∈ final.extra →
      ctx.decls address = some decl) :
    ExtraRepresented ctx final := by
  obtain ⟨addedExtra, addedWrappers, _, hwrappers, hwrapperExtra⟩ :=
    hextends
  constructor
  · exact hdecls
  · intro memo hmember
    have hwrappers' : final.wrappers = addedWrappers := by
      simpa using hwrappers
    have hadded : memo ∈ addedWrappers := by
      rw [hwrappers'] at hmember
      exact hmember
    exact hdecls (hwrapperExtra memo hadded)

/-- Every represented successful expression-lowering run at one compiler
fuel produces a bounded ownership transformer. Requiring representation only
for the run's final state keeps the induction valid for the reachable prefix
of one whole-program lowering trajectory without quantifying over unrelated
synthetic-address histories. -/
def LowerEPreservesBelow (ctx : Ctx) (cur : FnDef) (limit : Nat)
    (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {world : Owned} {expr : IxIR0.Expr}
      {state finalState : LowSt} {output : VEnv} {emit : Emit} {av : AVal},
    (lowerE src fuel input world expr).run state =
      .ok (output, emit, av) finalState →
    ExtraRepresented ctx finalState →
    SelfAvailableBelow ctx cur limit input →
    LowerResultSoundBelow ctx cur limit input output world emit av

/-- `freshAddr` changes only the counter. -/
theorem freshAddr_extraExtends {initial final : LowSt}
    {address : Ixon.Address}
    (hrun : freshAddr.run initial = .ok address final) :
    ExtraExtends initial final := by
  change EStateM.Result.ok (synthAddr initial.fresh)
      { initial with fresh := initial.fresh + 1 } =
    .ok address final at hrun
  have hstate : { initial with fresh := initial.fresh + 1 } = final :=
    congrArg
      (fun result : EStateM.Result String LowSt Ixon.Address =>
        match result with
        | .ok _ state | .error _ state => state)
      hrun
  subst final
  refine ⟨[], [], by simp, by simp, ?_⟩
  simp

/-- Installing one generated declaration prepends exactly one extra. -/
theorem pushExtra_extraExtends {initial final : LowSt}
    {item : Ixon.Address × Decl}
    (hrun : (pushExtra item).run initial = .ok () final) :
    ExtraExtends initial final := by
  simp [pushExtra] at hrun
  subst final
  refine ⟨[item], [], by simp, by simp, ?_⟩
  simp

/-- Constructor-wrapper lookup either preserves the extra list (cache hit)
or prepends the freshly synthesized wrapper declaration (cache miss). -/
theorem wrapperFor_extraExtends {initial final : LowSt}
    {source wrapper : Ixon.Address} {tag arity : Nat}
    (hrun : (wrapperFor source tag arity).run initial =
      .ok wrapper final) :
    ExtraExtends initial final := by
  cases hcached : initial.wrappers.find?
      (·.matches source tag arity) with
  | none =>
    simp [wrapperFor, hcached] at hrun
    have hstate :
        { initial with
            fresh := initial.fresh + 1
            wrappers :=
              ⟨source, tag, arity, synthAddr initial.fresh⟩ ::
                initial.wrappers
            extra :=
              (synthAddr initial.fresh,
                ctorWrapperDecl source tag arity) ::
                initial.extra } = final := by
      exact congrArg
        (fun result : EStateM.Result String LowSt Ixon.Address =>
          match result with
          | .ok _ state | .error _ state => state)
        hrun
    subst final
    refine ⟨[(synthAddr initial.fresh,
        ctorWrapperDecl source tag arity)],
      [⟨source, tag, arity, synthAddr initial.fresh⟩], rfl, rfl, ?_⟩
    simp
  | some memo =>
    simp [wrapperFor, hcached] at hrun
    obtain ⟨_, hstate⟩ := hrun
    subst final
    exact ExtraExtends.refl _

/-- Every successful wrapper lookup returns the exact shape-indexed memo in
its output state, on both cache hits and misses. -/
theorem wrapperFor_memo_mem {initial final : LowSt}
    {source wrapper : Ixon.Address} {tag arity : Nat}
    (hrun : (wrapperFor source tag arity).run initial =
      .ok wrapper final) :
    (⟨source, tag, arity, wrapper⟩ : WrapperMemo) ∈ final.wrappers := by
  cases hcached : initial.wrappers.find?
      (·.matches source tag arity) with
  | none =>
    dsimp [wrapperFor] at hrun
    rw [hcached] at hrun
    dsimp at hrun
    injection hrun with _ hstate
    subst wrapper
    subst final
    simp
  | some memo =>
    have hmember := List.mem_of_find?_eq_some hcached
    have hmatch := List.find?_some hcached
    dsimp [wrapperFor] at hrun
    rw [hcached] at hrun
    dsimp at hrun
    injection hrun with _ hstate
    subst wrapper
    subst final
    rw [WrapperMemo.matches, Bool.and_eq_true, Bool.and_eq_true] at hmatch
    have hsource := Ixon.Address.eq_of_beq hmatch.1.1
    have htag : memo.tag = tag := by simpa using hmatch.1.2
    have harity : memo.arity = arity := by simpa using hmatch.2
    cases memo
    simp_all

/-- A lowering-monad action is monotone in the generated-declaration list
when every successful run only prepends extras. -/
def ExtraMonotone {α : Type} (action : LowerM α) : Prop :=
  ∀ {initial final result}, action.run initial = .ok result final →
    ExtraExtends initial final

theorem ExtraMonotone.pure {α : Type} (value : α) :
    ExtraMonotone (pure value : LowerM α) := by
  intro initial final result hrun
  have hpure : value = result ∧ initial = final := by
    simpa using hrun
  obtain ⟨_, hstate⟩ := hpure
  subst final
  exact ExtraExtends.refl _

theorem ExtraMonotone.throw {α : Type} (message : String) :
    ExtraMonotone (throw message : LowerM α) := by
  intro initial final result hrun
  exact (estateThrowRun_not_ok hrun).elim

theorem ExtraMonotone.throwBind {α β : Type} (message : String)
    (next : α → LowerM β) :
    ExtraMonotone ((EStateM.throw message : LowerM α) >>= next) := by
  intro initial final result hrun
  change EStateM.Result.error message initial = .ok result final at hrun
  contradiction

theorem ExtraMonotone.get :
    ExtraMonotone (get : LowerM LowSt) := by
  intro initial final result hrun
  change EStateM.Result.ok initial initial = .ok result final at hrun
  injection hrun with _ hstate
  subst final
  exact ExtraExtends.refl _

theorem ExtraMonotone.bind {α β : Type}
    {action : LowerM α} {next : α → LowerM β}
    (haction : ExtraMonotone action)
    (hnext : ∀ value, ExtraMonotone (next value)) :
    ExtraMonotone (action >>= next) := by
  intro initial final result hrun
  obtain ⟨value, middle, hfirst, hsecond⟩ :=
    estateBindRun_ok_inv hrun
  exact (haction hfirst).trans (hnext value hsecond)

theorem ExtraMonotone.map {α β : Type} {action : LowerM α}
    (haction : ExtraMonotone action) (f : α → β) :
    ExtraMonotone (f <$> action) := by
  have hbind : ExtraMonotone
      (action >>= fun value => (Pure.pure (f value) : LowerM β)) :=
    ExtraMonotone.bind (action := action)
      (next := fun value => (Pure.pure (f value) : LowerM β)) haction
      (fun value => ExtraMonotone.pure (f value))
  intro initial final result hrun
  apply hbind
  simpa only [bind_pure_comp] using hrun

/-- Left-to-right monadic traversal preserves generated-state extension
when every element action does. -/
theorem ExtraMonotone.listMapM {α β : Type} (f : α → LowerM β)
    (hf : ∀ value, ExtraMonotone (f value)) :
    ∀ values : List α, ExtraMonotone (values.mapM f)
  | [] => by
      simpa using (ExtraMonotone.pure ([] : List β))
  | value :: rest => by
      rw [List.mapM_cons]
      apply ExtraMonotone.bind (hf value)
      intro head
      apply ExtraMonotone.bind (ExtraMonotone.listMapM f hf rest)
      intro tail
      exact ExtraMonotone.pure (head :: tail)

/-- Filtering monadic traversal has the same extension law; discarding a
`none` result does not affect the threaded compiler state. -/
theorem ExtraMonotone.listFilterMapM {α β : Type}
    (f : α → LowerM (Option β))
    (hf : ∀ value, ExtraMonotone (f value)) :
    ∀ values : List α, ExtraMonotone (values.filterMapM f)
  | [] => by
      simpa using (ExtraMonotone.pure ([] : List β))
  | value :: rest => by
      rw [List.filterMapM_cons]
      apply ExtraMonotone.bind (hf value)
      intro head
      cases head with
      | none => exact ExtraMonotone.listFilterMapM f hf rest
      | some head =>
        apply ExtraMonotone.bind
          (ExtraMonotone.listFilterMapM f hf rest)
        intro tail
        exact ExtraMonotone.pure (head :: tail)

/-- Recover the exact element action corresponding to any input member of a
successful filtering traversal. The suffix extension and optional output
membership are retained for declaration-level contract proofs. -/
theorem listFilterMapM_trace {α β : Type}
    (f : α → LowerM (Option β))
    (hmono : ∀ item, ExtraMonotone (f item)) :
    ∀ (items : List α) {initial final : LowSt} {results : List β},
      (items.filterMapM f).run initial = .ok results final →
      ∀ {item}, item ∈ items →
      ∃ itemInitial itemFinal output,
        (f item).run itemInitial = .ok output itemFinal ∧
        ExtraExtends itemFinal final ∧
        ∀ value, output = some value → value ∈ results := by
  intro items
  induction items with
  | nil =>
    intro initial final results hrun item hmember
    simp at hmember
  | cons head tail ih =>
    intro initial final results hrun item hmember
    rw [List.filterMapM_cons] at hrun
    obtain ⟨headOutput, middle, hheadRun, hafterHead⟩ :=
      estateBindRun_ok_inv hrun
    cases headOutput with
    | none =>
      simp only at hafterHead
      rw [List.mem_cons] at hmember
      cases hmember with
      | inl hitem =>
        subst item
        refine ⟨initial, middle, none, hheadRun,
          ExtraMonotone.listFilterMapM f hmono tail hafterHead, ?_⟩
        intro value hnone
        contradiction
      | inr htail =>
        exact ih hafterHead htail
    | some headValue =>
      obtain ⟨tailResults, tailState, htailRun, hpureRun⟩ :=
        estateBindRun_ok_inv hafterHead
      have hpure : headValue :: tailResults = results ∧
          tailState = final := by
        simpa using hpureRun
      obtain ⟨hresults, hstate⟩ := hpure
      subst results
      subst final
      rw [List.mem_cons] at hmember
      cases hmember with
      | inl hitem =>
        subst item
        refine ⟨initial, middle, some headValue, hheadRun,
          ExtraMonotone.listFilterMapM f hmono tail htailRun, ?_⟩
        intro value hvalue
        have : value = headValue := Option.some.inj hvalue.symm
        subst value
        simp
      | inr htail =>
        obtain ⟨itemInitial, itemFinal, output, hitemRun, hextends,
            houtput⟩ := ih htailRun htail
        refine ⟨itemInitial, itemFinal, output, hitemRun, hextends, ?_⟩
        intro value hvalue
        exact List.mem_cons_of_mem _ (houtput value hvalue)

theorem freshAddr_extraMonotone : ExtraMonotone freshAddr :=
  fun hrun => freshAddr_extraExtends hrun

theorem pushExtra_extraMonotone (item : Ixon.Address × Decl) :
    ExtraMonotone (pushExtra item) :=
  fun hrun => pushExtra_extraExtends hrun

theorem wrapperFor_extraMonotone (source : Ixon.Address)
    (tag arity : Nat) : ExtraMonotone (wrapperFor source tag arity) :=
  fun hrun => wrapperFor_extraExtends hrun

/-- Entry cleanup emits code and rewrites `VEnv`, but cannot add generated
declarations. -/
theorem releaseSlots_extraMonotone (input : VEnv) :
    ∀ drops : List SlotDrop, ExtraMonotone (releaseSlots input drops) := by
  intro drops
  induction drops generalizing input with
  | nil =>
    change ExtraMonotone
      (pure (input, (_root_.id : Emit)) : LowerM (VEnv × Emit))
    exact ExtraMonotone.pure _
  | cons drop rest ih =>
    simp only [releaseSlots]
    cases drop.uses with
    | erased => exact ExtraMonotone.throwBind _ _
    | linear => exact ExtraMonotone.throwBind _ _
    | affine =>
      apply ExtraMonotone.bind (ExtraMonotone.pure _)
      intro headEmit
      apply ExtraMonotone.bind
        (ih (input.setEntry drop.entry
          (.slot drop.abs 0 .affine false)).bump)
      intro tailResult
      rcases tailResult with ⟨output, tailEmit⟩
      exact ExtraMonotone.pure (output, headEmit ∘ tailEmit)
    | many =>
      apply ExtraMonotone.bind (ExtraMonotone.pure _)
      intro headEmit
      apply ExtraMonotone.bind
        (ih (input.setEntry drop.entry
          (.slot drop.abs 0 .many false)).bump)
      intro tailResult
      rcases tailResult with ⟨output, tailEmit⟩
      exact ExtraMonotone.pure (output, headEmit ∘ tailEmit)

/-- Generated-declaration monotonicity for every expression action at one
compiler-fuel index. This is intentionally independent of evaluator
ownership soundness. -/
def LowerEExtraMonotone (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ input world expr, ExtraMonotone (lowerE src fuel input world expr)

/-- Generated-declaration monotonicity for every closed-body action at one
compiler-fuel index. -/
def LowerFnBodyExtraMonotone (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ input drops world body,
    ExtraMonotone (lowerFnBody src fuel input drops world body)

def LowerLamExtraMonotone (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ input expr, ExtraMonotone (lowerLam src fuel input expr)

def LowerBorrowExtraMonotone (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ input expr, ExtraMonotone (lowerBorrow src fuel input expr)

def LowerSpineExtraMonotone (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ input world head args,
    ExtraMonotone (lowerSpine src fuel input world head args)

def KnownCallExtraMonotone (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ input build count argWorlds resultWorld args,
    ExtraMonotone
      (knownCall src fuel input build count argWorlds resultWorld args)

def LowerArgsExtraMonotone (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ input args, ExtraMonotone (lowerArgs src fuel input args)

def ApplyRestExtraMonotone (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ input resultWorld pre function args,
    ExtraMonotone
      (applyRest src fuel input resultWorld pre function args)

/-- The complete state-only invariant for the mutually recursive lowering
cluster at one compiler-fuel index. -/
structure LowerExtraMonotone (src : IxIR0.Env) (fuel : Nat) : Prop where
  expr : LowerEExtraMonotone src fuel
  borrow : LowerBorrowExtraMonotone src fuel
  spine : LowerSpineExtraMonotone src fuel
  knownCall : KnownCallExtraMonotone src fuel
  args : LowerArgsExtraMonotone src fuel
  applyRest : ApplyRestExtraMonotone src fuel
  lam : LowerLamExtraMonotone src fuel
  fnBody : LowerFnBodyExtraMonotone src fuel

/-- Result-world checks inspect no compiler state. -/
theorem requireResultWorld_extraMonotone (actual demand : Owned) :
    ExtraMonotone (requireResultWorld actual demand) := by
  cases actual <;> cases demand <;>
    simp [requireResultWorld] <;>
    first | exact ExtraMonotone.pure _ | exact ExtraMonotone.throw _

theorem lowerFnBodyExtraMonotone_zero (src : IxIR0.Env) :
    LowerFnBodyExtraMonotone src 0 := by
  intro input drops world body
  simp only [lowerFnBody]
  exact ExtraMonotone.throw _

/-- A body action only sequences entry cleanup, predecessor-fuel expression
lowering, and a pure `ret` closure. -/
theorem lowerFnBodyExtraMonotone_succ {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEExtraMonotone src fuel) :
    LowerFnBodyExtraMonotone src (fuel + 1) := by
  intro input drops world body
  simp only [lowerFnBody]
  apply ExtraMonotone.bind (releaseSlots_extraMonotone input drops)
  intro releaseResult
  rcases releaseResult with ⟨middle, releaseEmit⟩
  apply ExtraMonotone.bind (hexpr middle world body)
  intro bodyResult
  rcases bodyResult with ⟨output, bodyEmit, value⟩
  exact ExtraMonotone.pure
    (releaseEmit (bodyEmit (.ret (value.toAtom output))))

theorem lowerExtraMonotone_zero (src : IxIR0.Env) :
    LowerExtraMonotone src 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro input world expr
    simp only [lowerE]
    exact ExtraMonotone.throw _
  · intro input expr
    simp only [lowerBorrow]
    exact ExtraMonotone.throw _
  · intro input world head args
    simp only [lowerSpine]
    exact ExtraMonotone.throw _
  · intro input build count argWorlds resultWorld args
    simp only [knownCall]
    exact ExtraMonotone.throw _
  · intro input args
    simp only [lowerArgs]
    exact ExtraMonotone.throw _
  · intro input resultWorld pre function args
    simp only [applyRest]
    exact ExtraMonotone.throw _
  · intro input expr
    simp only [lowerLam]
    exact ExtraMonotone.throw _
  · exact lowerFnBodyExtraMonotone_zero src

/-- Compile-state companion to semantic expression preservation. A body
started with a correctly counted first binder releases that binder on every
successful lowering run. Keeping this obligation separate avoids weakening
`LowerResultSoundBelow` with compiler-internal entry arithmetic. -/
def LowerEReleasesTrackedFirst (src : IxIR0.Env) (fuel : Nat)
    (expr : IxIR0.Expr) : Prop :=
  ∀ {input output : VEnv} {world : Owned}
      {uses : Uses} {state finalState : LowSt} {emit : Emit} {av : AVal},
    FirstEntryTracks input uses (countUses 0 expr) →
    (lowerE src fuel input world expr).run state =
      .ok (output, emit, av) finalState →
    FirstEntryReleased output

/-- Every successful borrowing-position run at one compiler fuel produces a
shared borrowed descriptor and records whether its owner must be released. -/
def LowerBorrowPreservesBelow (ctx : Ctx) (cur : FnDef) (limit : Nat)
    (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {expr : IxIR0.Expr}
      {state finalState : LowSt} {output : VEnv} {emit : Emit}
      {av : AVal} {release : Bool},
    (lowerBorrow src fuel input expr).run state =
      .ok (output, emit, av, release) finalState →
    ExtraRepresented ctx finalState →
    SelfAvailableBelow ctx cur limit input →
    LowerBorrowSoundBelow ctx cur limit input output emit av release

/-- Every successful argument-lowering run at one compiler fuel produces the
bounded left-to-right argument transformer. -/
def LowerArgsPreservesBelow (ctx : Ctx) (cur : FnDef) (limit : Nat)
    (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {args : List (IxIR0.Expr × Owned)}
      {state finalState : LowSt} {output : VEnv}
      {emit : Emit} {avs : List AVal},
    (lowerArgs src fuel input args).run state =
      .ok (output, emit, avs) finalState →
    ExtraRepresented ctx finalState →
    SelfAvailableBelow ctx cur limit input →
    LowerArgsSoundBelow ctx cur limit input output
      (args.map Prod.snd) emit avs

/-- Successful `applyRest` runs preserve a previously produced shared
function result. This premise-parametric form composes both syntactic erased
absorption and genuine higher-order application. -/
def ApplyRestPreservesBelow (ctx : Ctx) (cur : FnDef) (limit : Nat)
    (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {start input : VEnv} {resultWorld : Owned} {pre : Emit}
      {function : AVal} {args : List IxIR0.Expr}
      {state finalState : LowSt} {output : VEnv}
      {emit : Emit} {av : AVal},
    LowerResultSoundBelow ctx cur limit start input .shared pre function →
    (applyRest src fuel input resultWorld pre function args).run state =
      .ok (output, emit, av) finalState →
    ExtraRepresented ctx finalState →
    SelfAvailableBelow ctx cur limit input →
    LowerResultSoundBelow ctx cur limit start output resultWorld emit av

/-- Successful `knownCall` runs preserve ownership for one fixed operation
builder and argument telescope. Operation-specific dispatch supplies the
builder's result-world rule. -/
def KnownCallPreservesBelow (ctx : Ctx) (cur : FnDef) (limit : Nat)
    (src : IxIR0.Env) (fuel : Nat) (build : Array Atom → Op)
    (count : Nat) (argWorlds : List Owned) (resultWorld : Owned) : Prop :=
  ∀ {input : VEnv} {args : List IxIR0.Expr}
      {state finalState : LowSt} {output : VEnv}
      {emit : Emit} {av : AVal},
    (knownCall src fuel input build count argWorlds resultWorld args).run
      state = .ok (output, emit, av) finalState →
    ExtraRepresented ctx finalState →
    SelfAvailableBelow ctx cur limit input →
    LowerResultSoundBelow ctx cur limit input output resultWorld emit av

/-- Successful application-spine lowering at one compiler fuel. -/
def LowerSpinePreservesBelow (ctx : Ctx) (cur : FnDef) (limit : Nat)
    (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {world : Owned} {head : IxIR0.Expr}
      {args : List IxIR0.Expr} {state finalState : LowSt}
      {output : VEnv} {emit : Emit} {av : AVal},
    (lowerSpine src fuel input world head args).run state =
      .ok (output, emit, av) finalState →
    ExtraRepresented ctx finalState →
    SelfAvailableBelow ctx cur limit input →
    LowerResultSoundBelow ctx cur limit input output world emit av

private theorem lowerArgs_nil_sound_at {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {Γ : VEnv} :
    LowerArgsSoundBelow ctx cur limit Γ Γ [] (_root_.id : Emit) [] := by
  refine ⟨AValsStable.nil, ?_⟩
  intro rest slots
  apply EmitSoundBelow.strengthen
  intro store env hpre
  obtain ⟨⟨roots, hΓ, hown⟩, hslots⟩ := hpre
  exact ⟨⟨roots, [], hΓ, .nil, by simpa [rootsForWorlds] using hown⟩,
    hslots⟩

theorem lowerArgs_nil_sound {ctx : Ctx} {cur : FnDef} {Γ : VEnv} :
    LowerArgsSound ctx cur Γ Γ [] (_root_.id : Emit) [] := by
  apply LowerArgsSound.of_below
  intro limit
  exact lowerArgs_nil_sound_at (limit := limit)

theorem lowerArgs_nil_value_sound {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value} :
    LowerArgsValueSound funRel recSelfRel ctx cur Γ Γ
      sourceEnv sourceEnv [] [] (_root_.id : Emit) [] := by
  refine
    { toLowerArgsSound := lowerArgs_nil_sound
      graphEmits := ?_ }
  intro sourceRest rest slots
  apply EmitSound.strengthen
  intro store env hpre
  obtain ⟨⟨roots, hΓ, hrestGraph, hown⟩, hslots⟩ := hpre
  exact ⟨⟨roots, [], hΓ, .nil, .nil, hrestGraph,
    by simpa [rootsForWorlds] using hown⟩, hslots⟩

/-- Bounded base case for left-to-right argument lowering. -/
theorem lowerArgs_nil_sound_below {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {Γ : VEnv} :
    LowerArgsSoundBelow ctx cur limit Γ Γ [] (_root_.id : Emit) [] := by
  exact lowerArgs_nil_sound_at

/-- The central `lowerArgs` cons rule. The head result becomes a protected
absolute slot while the tail is emitted; on completion it is realized again
and moved from the tail continuation into the argument-root prefix. -/
theorem LowerResultSound.consArgs {ctx : Ctx} {cur : FnDef}
    {input middle output : VEnv} {world : Owned} {worlds : List Owned}
    {emitHead emitTail : Emit} {av : AVal} {avs : List AVal}
    (head : LowerResultSound ctx cur input middle world emitHead av)
    (tail : LowerArgsSound ctx cur middle output worlds emitTail avs) :
    LowerArgsSound ctx cur input output (world :: worlds)
      (emitHead ∘ emitTail) (av :: avs) := by
  refine ⟨AValsStable.cons head.stable tail.stable, ?_⟩
  intro rest slots
  apply EmitSound.comp (head.emits rest slots)
  intro post code hcode
  intro fuel store env finalStore finalValue hmid hrun
  obtain ⟨⟨envRoots, value, hmiddle, hav, hown⟩, hslots⟩ := hmid
  let root : Root := ⟨world, value⟩
  have hprotect : SlotsRealize middle env (aValProtection av value) :=
    head.stable.protection_realized hav
  have htailOwn : RootOwnership store (envRoots ++ root :: rest) := by
    apply hown.perm
    simpa [root] using
      (perm_extract_root root envRoots [] rest).symm
  have htailPre : OwnsVEnvProtected middle (root :: rest)
      (aValProtection av value ++ slots) store env :=
    ⟨⟨envRoots, hmiddle, htailOwn⟩, hprotect.append hslots⟩
  have htailCont : CodeOwns ctx cur
      (OwnsArgsResultProtected output worlds avs (root :: rest)
        (aValProtection av value ++ slots)) post code := by
    intro innerFuel innerStore innerEnv resultStore resultValue htailPost hcodeRun
    obtain ⟨⟨outRoots, values, houtput, havs, hownTail⟩,
      hslotsTail⟩ := htailPost
    have havFinal : AValRealizes output innerEnv av value :=
      head.stable.realize_of_protection hav hslotsTail.left_of_append
    have hownFinal : RootOwnership innerStore
        (rootsForWorlds (world :: worlds) (value :: values) ++
          outRoots ++ rest) := by
      apply hownTail.perm
      simpa [root, List.append_assoc] using
        (perm_extract_root root
          (rootsForWorlds worlds values ++ outRoots) [] rest)
    apply hcode
    · exact ⟨⟨outRoots, value :: values, houtput,
        .cons havFinal havs, hownFinal⟩, hslotsTail.right_of_append⟩
    · exact hcodeRun
  have htailCode : CodeOwns ctx cur
      (OwnsVEnvProtected middle (root :: rest)
        (aValProtection av value ++ slots)) post (emitTail code) :=
    tail.emits (root :: rest) (aValProtection av value ++ slots)
      post code htailCont
  exact htailCode htailPre hrun

/-- Semantic argument sequencing. The head result is framed for the tail as
one related source/target root; the tail postcondition returns that
`RootsGraph`, so the head `ValueGraph` remains available in the final store. -/
theorem LowerResultValueSound.consArgs {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {ctx : Ctx} {cur : FnDef}
    {input middle output : VEnv}
    {sourceInput sourceMiddle sourceOutput : List IxIR0.Value}
    {sourceValue : IxIR0.Value} {sourceValues : List IxIR0.Value}
    {world : Owned} {worlds : List Owned}
    {emitHead emitTail : Emit} {av : AVal} {avs : List AVal}
    (head : LowerResultValueSound funRel recSelfRel ctx cur input middle
      sourceInput sourceMiddle sourceValue world emitHead av)
    (tail : LowerArgsValueSound funRel recSelfRel ctx cur middle output
      sourceMiddle sourceOutput sourceValues worlds emitTail avs) :
    LowerArgsValueSound funRel recSelfRel ctx cur input output
      sourceInput sourceOutput (sourceValue :: sourceValues)
      (world :: worlds) (emitHead ∘ emitTail) (av :: avs) := by
  refine
    { toLowerArgsSound := head.toLowerResultSound.consArgs
        tail.toLowerArgsSound
      graphEmits := ?_ }
  intro sourceRest rest slots
  apply EmitSound.comp (head.graphEmits sourceRest rest slots)
  intro post code hcode
  intro fuel store env finalStore finalValue hmid hrun
  obtain ⟨⟨envRoots, value, hmiddle, hav, hvalueGraph,
      hrestGraph, hown⟩, hslots⟩ := hmid
  let root : Root := ⟨world, value⟩
  have hrootWorld : HasWorld store world value := by
    apply hown.roots_world root
    simp [root]
  have hframeGraph : Sim.RootsGraph funRel store
      ((world, sourceValue) :: sourceRest) (root :: rest) :=
    .cons rfl hrootWorld hvalueGraph hrestGraph
  have hprotect : SlotsRealize middle env (aValProtection av value) :=
    head.stable.protection_realized hav
  have htailOwn : RootOwnership store (envRoots ++ root :: rest) := by
    apply hown.perm
    simpa [root] using
      (perm_extract_root root envRoots [] rest).symm
  have htailPre : GraphOwnsVEnvProtected funRel recSelfRel middle
      sourceMiddle ((world, sourceValue) :: sourceRest) (root :: rest)
      (aValProtection av value ++ slots) store env :=
    ⟨⟨envRoots, hmiddle, hframeGraph, htailOwn⟩,
      hprotect.append hslots⟩
  have htailCont : CodeOwns ctx cur
      (GraphOwnsArgsResultProtected funRel recSelfRel output
        sourceOutput sourceValues worlds avs
        ((world, sourceValue) :: sourceRest) (root :: rest)
        (aValProtection av value ++ slots)) post code := by
    intro innerFuel innerStore innerEnv resultStore resultValue
      htailPost hcodeRun
    obtain ⟨⟨outRoots, values, houtput, havs, hvalueGraphs,
        hframeGraphFinal, hownTail⟩, hslotsTail⟩ := htailPost
    cases hframeGraphFinal with
    | cons _ _ hheadGraph hrestGraphFinal =>
      have havFinal : AValRealizes output innerEnv av value :=
        head.stable.realize_of_protection hav
          hslotsTail.left_of_append
      have hheadGraph' :
          Sim.ValueGraph funRel innerStore sourceValue value := by
        simpa [root] using hheadGraph
      have hownFinal : RootOwnership innerStore
          (rootsForWorlds (world :: worlds) (value :: values) ++
            outRoots ++ rest) := by
        apply hownTail.perm
        simpa [root, List.append_assoc] using
          (perm_extract_root root
            (rootsForWorlds worlds values ++ outRoots) [] rest)
      apply hcode
      · exact ⟨⟨outRoots, value :: values, houtput,
          .cons havFinal havs, .cons hheadGraph' hvalueGraphs,
          hrestGraphFinal, hownFinal⟩,
          hslotsTail.right_of_append⟩
      · exact hcodeRun
  have htailCode : CodeOwns ctx cur
      (GraphOwnsVEnvProtected funRel recSelfRel middle sourceMiddle
        ((world, sourceValue) :: sourceRest) (root :: rest)
        (aValProtection av value ++ slots)) post (emitTail code) :=
    tail.graphEmits ((world, sourceValue) :: sourceRest) (root :: rest)
      (aValProtection av value ++ slots) post code htailCont
  exact htailCode htailPre hrun

/-- Fuel-bounded argument sequencing. The hereditary emitter bound lets the
head protect its result slot across the recursively emitted tail exactly as
in `LowerResultSound.consArgs`. -/
theorem LowerResultSoundBelow.consArgs {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {input middle output : VEnv}
    {world : Owned} {worlds : List Owned}
    {emitHead emitTail : Emit} {av : AVal} {avs : List AVal}
    (head : LowerResultSoundBelow ctx cur limit input middle world
      emitHead av)
    (tail : LowerArgsSoundBelow ctx cur limit middle output worlds
      emitTail avs) :
    LowerArgsSoundBelow ctx cur limit input output (world :: worlds)
      (emitHead ∘ emitTail) (av :: avs) := by
  refine ⟨AValsStable.cons head.stable tail.stable, ?_⟩
  intro rest slots
  apply EmitSoundBelow.comp (head.emits rest slots)
  intro bound hbound post code hcode
  intro fuel store env finalStore finalValue hfuel hmid hrun
  obtain ⟨⟨envRoots, value, hmiddle, hav, hown⟩, hslots⟩ := hmid
  let root : Root := ⟨world, value⟩
  have hprotect : SlotsRealize middle env (aValProtection av value) :=
    head.stable.protection_realized hav
  have htailOwn : RootOwnership store (envRoots ++ root :: rest) := by
    apply hown.perm
    simpa [root] using
      (perm_extract_root root envRoots [] rest).symm
  have htailPre : OwnsVEnvProtected middle (root :: rest)
      (aValProtection av value ++ slots) store env :=
    ⟨⟨envRoots, hmiddle, htailOwn⟩, hprotect.append hslots⟩
  have htailCont : CodeOwnsBelow ctx cur bound
      (OwnsArgsResultProtected output worlds avs (root :: rest)
        (aValProtection av value ++ slots)) post code := by
    intro innerFuel innerStore innerEnv resultStore resultValue hinnerFuel
      htailPost hcodeRun
    obtain ⟨⟨outRoots, values, houtput, havs, hownTail⟩,
      hslotsTail⟩ := htailPost
    have havFinal : AValRealizes output innerEnv av value :=
      head.stable.realize_of_protection hav hslotsTail.left_of_append
    have hownFinal : RootOwnership innerStore
        (rootsForWorlds (world :: worlds) (value :: values) ++
          outRoots ++ rest) := by
      apply hownTail.perm
      simpa [root, List.append_assoc] using
        (perm_extract_root root
          (rootsForWorlds worlds values ++ outRoots) [] rest)
    apply hcode hinnerFuel
    · exact ⟨⟨outRoots, value :: values, houtput,
        .cons havFinal havs, hownFinal⟩, hslotsTail.right_of_append⟩
    · exact hcodeRun
  have htailCode : CodeOwnsBelow ctx cur bound
      (OwnsVEnvProtected middle (root :: rest)
        (aValProtection av value ++ slots)) post (emitTail code) :=
    tail.emits (root :: rest) (aValProtection av value ++ slots)
      bound hbound post code htailCont
  exact htailCode hfuel htailPre hrun

/-- One compiler-fuel step of the `lowerArgs` induction. Both recursive
calls use the predecessor fuel, so this theorem is the exact bridge consumed
by the eventual joint strong induction over the lowering cluster. -/
theorem lowerArgsPreservesBelow_succ
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat}
    (hexpr : LowerEPreservesBelow ctx cur limit src fuel)
    (hargs : LowerArgsPreservesBelow ctx cur limit src fuel)
    (hargsExtra : LowerArgsExtraMonotone src fuel) :
    LowerArgsPreservesBelow ctx cur limit src (fuel + 1) := by
  intro input args state finalState output emit avs hrun hrepresented
    havailable
  cases args with
  | nil =>
    have hpure :
        (input, (_root_.id : Emit), []) = (output, emit, avs) ∧
          state = finalState := by
      simpa [lowerArgs] using hrun
    obtain ⟨hvalue, hstate⟩ := hpure
    cases hvalue
    subst finalState
    exact lowerArgs_nil_sound_below
  | cons head rest =>
    rcases head with ⟨expr, world⟩
    simp only [lowerArgs] at hrun
    obtain ⟨headResult, middleState, hheadRun, hafterHead⟩ :=
      estateBindRun_ok_inv hrun
    rcases headResult with ⟨middle, emitHead, av⟩
    dsimp only at hafterHead
    obtain ⟨tailResult, tailState, htailRun, hpureRun⟩ :=
      estateBindRun_ok_inv hafterHead
    rcases tailResult with ⟨actualOutput, emitTail, tailAvs⟩
    have hpure :
        (actualOutput, emitHead ∘ emitTail, av :: tailAvs) =
            (output, emit, avs) ∧
          tailState = finalState := by
      simpa using hpureRun
    obtain ⟨hvalue, hstate⟩ := hpure
    cases hvalue
    subst finalState
    have hmiddleRepresented : ExtraRepresented ctx middleState :=
      hrepresented.of_extends
      (hargsExtra middle rest htailRun)
    have hmiddleAvailable := havailable.lowerE hheadRun
    exact (hexpr hheadRun hmiddleRepresented havailable).consArgs
      (hargs htailRun hrepresented hmiddleAvailable)

/-- `lowerArgs` is not an independent mutual-induction obligation: at fuel
`n` it follows from expression soundness at every strictly smaller compiler
fuel. The tail recursion is discharged internally by ordinary induction. -/
theorem lowerArgsPreservesBelow_of_expr
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    (fuel : Nat)
    (hexpr : ∀ prior, prior < fuel →
      LowerEPreservesBelow ctx cur limit src prior)
    (hextra : ∀ prior, prior < fuel →
      LowerArgsExtraMonotone src prior) :
    LowerArgsPreservesBelow ctx cur limit src fuel := by
  induction fuel with
  | zero =>
    intro input args state finalState output emit avs hrun hrepresented _
    simp only [lowerArgs] at hrun
    exact (estateThrowRun_not_ok hrun).elim
  | succ fuel ih =>
    apply lowerArgsPreservesBelow_succ
    · exact hexpr fuel (Nat.lt_succ_self fuel)
    · apply ih
      intro prior hprior
      exact hexpr prior (Nat.lt_trans hprior (Nat.lt_succ_self fuel))
      intro prior hprior
      exact hextra prior (Nat.lt_trans hprior (Nat.lt_succ_self fuel))
    · exact hextra fuel (Nat.lt_succ_self fuel)

/-- Successful argument lowering preserves list length independently of its
semantic proof. This supplies the homogeneous-world equalities needed by
`applyRest` and `knownCall`. -/
theorem lowerArgs_success_length (src : IxIR0.Env) :
    ∀ {fuel : Nat} {input : VEnv}
      {args : List (IxIR0.Expr × Owned)} {state finalState : LowSt}
      {output : VEnv} {emit : Emit} {avs : List AVal},
    (lowerArgs src fuel input args).run state =
      .ok (output, emit, avs) finalState →
    avs.length = args.length := by
  intro fuel
  induction fuel with
  | zero =>
    intro input args state finalState output emit avs hrun
    simp only [lowerArgs] at hrun
    exact (estateThrowRun_not_ok hrun).elim
  | succ fuel ih =>
    intro input args state finalState output emit avs hrun
    cases args with
    | nil =>
      have hpure :
          (input, (_root_.id : Emit), []) = (output, emit, avs) ∧
            state = finalState := by
        simpa [lowerArgs] using hrun
      obtain ⟨hvalue, _⟩ := hpure
      cases hvalue
      rfl
    | cons head rest =>
      rcases head with ⟨expr, world⟩
      simp only [lowerArgs] at hrun
      obtain ⟨headResult, middleState, _, hafterHead⟩ :=
        estateBindRun_ok_inv hrun
      rcases headResult with ⟨middle, emitHead, av⟩
      dsimp only at hafterHead
      obtain ⟨tailResult, tailState, htailRun, hpureRun⟩ :=
        estateBindRun_ok_inv hafterHead
      rcases tailResult with ⟨actualOutput, emitTail, tailAvs⟩
      have hpure :
          (actualOutput, emitHead ∘ emitTail, av :: tailAvs) =
              (output, emit, avs) ∧
            tailState = finalState := by
        simpa using hpureRun
      obtain ⟨hvalue, _⟩ := hpure
      cases hvalue
      simp [ih htailRun]

theorem map_shared_arg_worlds (args : List IxIR0.Expr) :
    (args.map (fun arg => (arg, Owned.shared))).map Prod.snd =
      List.replicate args.length .shared := by
  induction args with
  | nil => rfl
  | cons arg args ih =>
    simp [List.replicate_succ, ih]

/-- Once a known call has enough source arguments for its requested prefix,
zipping with a complete world telescope preserves that telescope exactly. -/
theorem knownCall_prefix_worlds_eq (args : List IxIR0.Expr)
    (worlds : List Owned) (count : Nat)
    (hworlds : worlds.length = count) (hcount : count ≤ args.length) :
    (((args.take count).zip (padWorlds worlds count)).map Prod.snd) =
      worlds := by
  rw [show padWorlds worlds count = worlds by
    simp [padWorlds, ← hworlds]]
  apply List.map_snd_zip
  simp [hworlds, hcount]

/-- The corresponding executable prefix has exactly the requested length. -/
theorem knownCall_prefix_length_eq (args : List IxIR0.Expr)
    (worlds : List Owned) (count : Nat)
    (hworlds : worlds.length = count) (hcount : count ≤ args.length) :
    ((args.take count).zip (padWorlds worlds count)).length = count := by
  have hshape := knownCall_prefix_worlds_eq args worlds count hworlds hcount
  simpa [hworlds] using congrArg List.length hshape

/-- Repackage the common output of a result-producing operation as the
lowerer's fresh absolute result slot while preserving its `VEnv` and slot
frame. -/
theorem ownsPushedRoot_result {Γ : VEnv} {envRoots rest : List Root}
    {slots : List (Nat × RVal)} {world : Owned} :
    ∀ {store env},
      OwnsPushedRoot
        (fun oldEnv => VEnvRealizes Γ oldEnv envRoots ∧
          SlotsRealize Γ oldEnv slots)
        world (envRoots ++ rest) store env →
      OwnsResultProtected Γ.bump world (.slotA Γ.depth)
        rest slots store env := by
  intro store env hpush
  obtain ⟨value, oldEnv, rfl, hΓ, hown⟩ := hpush
  refine ⟨⟨envRoots, value, hΓ.1.bump value, ?_, hown⟩,
    hΓ.2.bump value⟩
  apply AValRealizes.slot
  · simp [VEnv.bump]
  · simp [VEnv.bump, VEnv.rel]

/-- Generic bounded consumer for a lowered argument list followed by one
operation that consumes its roots and pushes a result. The operation-specific
rules supply only their expected root shape. -/
theorem LowerArgsSoundBelow.finishPushed
    {ctx : Ctx} {cur : FnDef} {limit : Nat}
    {input output : VEnv} {worlds : List Owned}
    {emit : Emit} {avs : List AVal} {op : Op}
    {resultWorld : Owned} {opRoots : List RVal → List Root}
    (hargs : LowerArgsSoundBelow ctx cur limit input output worlds emit avs)
    (hrootShape : ∀ {values : List RVal}, values.length = avs.length →
      rootsForWorlds worlds values = opRoots values)
    (hop : ∀ {frame : List RVal → Prop} {values : List RVal}
        {tailRoots : List Root},
      values.length = avs.length →
      EmitSoundBelow ctx cur limit (emitOp op)
        (fun store env => frame env ∧
          resolveAtoms env (avs.map (·.toAtom output)).toArray = .ok values ∧
          RootOwnership store (opRoots values ++ tailRoots))
        (OwnsPushedRoot frame resultWorld tailRoots)) :
    LowerResultSoundBelow ctx cur limit input output.bump resultWorld
      (emit ∘ emitOp op) (.slotA output.depth) := by
  refine ⟨.slot, ?_⟩
  intro rest slots
  apply EmitSoundBelow.comp (hargs.emits rest slots)
  intro bound hbound post code hcode
  intro fuel store env finalStore finalValue hfuel hpre hrun
  obtain ⟨⟨envRoots, values, houtput, havs, hown⟩, hslots⟩ := hpre
  let frame : List RVal → Prop := fun oldEnv =>
    VEnvRealizes output oldEnv envRoots ∧ SlotsRealize output oldEnv slots
  have hnext : CodeOwnsBelow ctx cur bound
      (OwnsPushedRoot frame resultWorld (envRoots ++ rest)) post code := by
    intro nextFuel nextStore nextEnv resultStore resultValue hnextFuel
      hpushed hcodeRun
    apply hcode hnextFuel
    · exact ownsPushedRoot_result hpushed
    · exact hcodeRun
  have hvaluesLength : values.length = avs.length := havs.lengths.2.symm
  have hopCode : CodeOwnsBelow ctx cur bound
      (fun opStore opEnv => frame opEnv ∧
        resolveAtoms opEnv (avs.map (·.toAtom output)).toArray = .ok values ∧
        RootOwnership opStore (opRoots values ++ (envRoots ++ rest)))
      post (emitOp op code) :=
    (hop hvaluesLength) bound hbound post code hnext
  apply hopCode hfuel
  · refine ⟨⟨houtput, hslots⟩, havs.resolveAtoms, ?_⟩
    simpa [hrootShape hvaluesLength, List.append_assoc] using hown
  · exact hrun

/-- Bounded direct-call consumer for a heterogeneous argument telescope. -/
theorem LowerArgsSoundBelow.call_owned {ctx : Ctx} {cur d : FnDef}
    {limit : Nat} {input output : VEnv} {worlds : List Owned}
    {emit : Emit} {avs : List AVal} {f : Ixon.Address}
    (hargs : LowerArgsSoundBelow ctx cur limit input output worlds emit avs)
    (hdecl : ctx.decls f = some (.fn d))
    (hcontract : FnOwnershipContractBelow ctx d worlds limit) :
    LowerResultSoundBelow ctx cur limit input output.bump d.result
      (emit ∘ emitOp (.call f (avs.map (·.toAtom output)).toArray))
      (.slotA output.depth) := by
  apply hargs.finishPushed (opRoots := rootsForWorlds worlds)
  · intro values _
    rfl
  · intro frame values tailRoots _
    exact emit_call_owned_below hdecl hcontract

/-- Bounded recursive-self-call consumer. -/
theorem LowerArgsSoundBelow.callSelf_owned
    {ctx : Ctx} {cur : FnDef} {limit : Nat}
    {input output : VEnv} {worlds : List Owned}
    {emit : Emit} {avs : List AVal}
    (hargs : LowerArgsSoundBelow ctx cur limit input output worlds emit avs)
    (hcontract : FnOwnershipContractBelow ctx cur worlds limit) :
    LowerResultSoundBelow ctx cur limit input output.bump cur.result
      (emit ∘ emitOp (.callSelf (avs.map (·.toAtom output)).toArray))
      (.slotA output.depth) := by
  apply hargs.finishPushed (opRoots := rootsForWorlds worlds)
  · intro values _
    rfl
  · intro frame values tailRoots _
    exact emit_callSelf_owned_below hcontract

/-- A malformed compiler environment may advertise the wrong recursive-self
arity. The emitted operation is nevertheless ownership-safe because the
target evaluator rejects that call before entering the current body. This
lets the compiler proof require a contract only at `cur.arity`; reachable
environments later rule out the malformed case altogether. -/
theorem LowerArgsSoundBelow.callSelf_arity_mismatch
    {ctx : Ctx} {cur : FnDef} {limit : Nat}
    {input output : VEnv} {worlds : List Owned}
    {emit : Emit} {avs : List AVal}
    (hargs : LowerArgsSoundBelow ctx cur limit input output worlds emit avs)
    (harity : avs.length ≠ cur.arity) :
    LowerResultSoundBelow ctx cur limit input output.bump cur.result
      (emit ∘ emitOp (.callSelf (avs.map (·.toAtom output)).toArray))
      (.slotA output.depth) := by
  apply hargs.finishPushed (opRoots := rootsForWorlds worlds)
  · intro values _
    rfl
  · intro frame values tailRoots hvaluesLength
    apply OpSoundBelow.emit
    intro opFuel store env store' result hopFuel hpre hrun
    obtain ⟨hframe, hresolve, hown⟩ := hpre
    cases opFuel with
    | zero => simp [runOp] at hrun
    | succ fuel =>
      rw [runOp.eq_def] at hrun
      dsimp only at hrun
      rw [hresolve] at hrun
      have hne : values.length ≠ cur.arity := by
        intro heq
        exact harity (hvaluesLength.symm.trans heq)
      change (if (values.length != cur.arity) = true then
          .error (.stuck "callSelf arity mismatch")
        else
          (do
            let out ← runCode ctx fuel cur store values.reverse cur.body
            checkResultWorld cur.result out)) =
          .ok (store', result) at hrun
      have hbne : (values.length != cur.arity) = true := by
        simp [hne]
      rw [if_pos hbne] at hrun
      contradiction

/-- Bounded homogeneous constructor allocation. -/
theorem LowerArgsSoundBelow.alloc_owned
    {ctx : Ctx} {cur : FnDef} {limit : Nat}
    {input output : VEnv} {world : Owned} {emit : Emit}
    {avs : List AVal} {cid : CtorId}
    (hargs : LowerArgsSoundBelow ctx cur limit input output
      (List.replicate avs.length world) emit avs) :
    LowerResultSoundBelow ctx cur limit input output.bump world
      (emit ∘ emitOp
        (.alloc world cid (avs.map (·.toAtom output)).toArray))
      (.slotA output.depth) := by
  apply hargs.finishPushed (opRoots := rootsFor world)
  · intro values hlength
    exact rootsForWorlds_replicate_eq_rootsFor world hlength
  · intro frame values tailRoots _
    exact emit_alloc_owned_below

/-- Bounded homogeneous partial-application allocation. -/
theorem LowerArgsSoundBelow.papp_owned
    {ctx : Ctx} {cur : FnDef} {limit : Nat}
    {input output : VEnv} {emit : Emit} {avs : List AVal}
    {f : Ixon.Address} {d : Decl}
    (hargs : LowerArgsSoundBelow ctx cur limit input output
      (List.replicate avs.length .shared) emit avs)
    (hdecl : ctx.decls f = some d)
    (hunder : avs.length < declArity d) :
    LowerResultSoundBelow ctx cur limit input output.bump .shared
      (emit ∘ emitOp (.papp f (avs.map (·.toAtom output)).toArray))
      (.slotA output.depth) := by
  apply hargs.finishPushed (opRoots := rootsFor .shared)
  · intro values hlength
    exact rootsForWorlds_replicate_eq_rootsFor .shared hlength
  · intro frame values tailRoots hlength
    apply emit_papp_owned_below hdecl
    simpa [hlength] using hunder

/-- Bounded scalar-only extern consumer. -/
theorem LowerArgsSoundBelow.extern_owned
    {ctx : Ctx} {cur : FnDef} {limit : Nat}
    {input output : VEnv} {emit : Emit} {avs : List AVal}
    {f : Ixon.Address} {resultWorld : Owned}
    (hargs : LowerArgsSoundBelow ctx cur limit input output
      (List.replicate avs.length .shared) emit avs) :
    LowerResultSoundBelow ctx cur limit input output.bump resultWorld
      (emit ∘ emitOp (.extern f (avs.map (·.toAtom output)).toArray))
      (.slotA output.depth) := by
  apply hargs.finishPushed (opRoots := rootsFor .shared)
  · intro values hlength
    exact rootsForWorlds_replicate_eq_rootsFor .shared hlength
  · intro frame values tailRoots _
    exact emit_extern_owned_below

/-- Consume a proved heterogeneous argument prefix with a direct call. The
callee contract removes every argument owner and produces one root in the
declaration's result world. -/
theorem LowerArgsSound.call_owned {ctx : Ctx} {cur d : FnDef}
    {input output : VEnv} {worlds : List Owned} {emit : Emit}
    {avs : List AVal} {f : Ixon.Address}
    (hargs : LowerArgsSound ctx cur input output worlds emit avs)
    (hdecl : ctx.decls f = some (.fn d))
    (hcontract : FnOwnershipContract ctx d worlds) :
    LowerResultSound ctx cur input output.bump d.result
      (emit ∘ emitOp (.call f (avs.map (·.toAtom output)).toArray))
      (.slotA output.depth) := by
  refine ⟨.slot, ?_⟩
  intro rest slots
  apply EmitSound.comp (hargs.emits rest slots)
  intro post code hcode
  intro fuel store env finalStore finalValue hpre hrun
  obtain ⟨⟨envRoots, values, houtput, havs, hown⟩, hslots⟩ := hpre
  let frame : List RVal → Prop := fun oldEnv =>
    VEnvRealizes output oldEnv envRoots ∧ SlotsRealize output oldEnv slots
  have hnext : CodeOwns ctx cur
      (OwnsPushedRoot frame d.result (envRoots ++ rest)) post code := by
    intro nextFuel nextStore nextEnv resultStore resultValue hpushed hcodeRun
    apply hcode
    · exact ownsPushedRoot_result hpushed
    · exact hcodeRun
  have hcall : CodeOwns ctx cur
      (fun callStore callEnv =>
        frame callEnv ∧
        resolveAtoms callEnv (avs.map (·.toAtom output)).toArray =
          .ok values ∧
        RootOwnership callStore
          (rootsForWorlds worlds values ++ (envRoots ++ rest)))
      post (emitOp (.call f (avs.map (·.toAtom output)).toArray) code) :=
    (emit_call_owned hdecl hcontract) post code hnext
  apply hcall
  · exact ⟨⟨houtput, hslots⟩, havs.resolveAtoms,
      by simpa [List.append_assoc] using hown⟩
  · exact hrun

/-- Consume a proved heterogeneous argument prefix with a recursive call to
the current function. -/
theorem LowerArgsSound.callSelf_owned {ctx : Ctx} {cur : FnDef}
    {input output : VEnv} {worlds : List Owned} {emit : Emit}
    {avs : List AVal}
    (hargs : LowerArgsSound ctx cur input output worlds emit avs)
    (hcontract : FnOwnershipContract ctx cur worlds) :
    LowerResultSound ctx cur input output.bump cur.result
      (emit ∘ emitOp (.callSelf (avs.map (·.toAtom output)).toArray))
      (.slotA output.depth) := by
  refine ⟨.slot, ?_⟩
  intro rest slots
  apply EmitSound.comp (hargs.emits rest slots)
  intro post code hcode
  intro fuel store env finalStore finalValue hpre hrun
  obtain ⟨⟨envRoots, values, houtput, havs, hown⟩, hslots⟩ := hpre
  let frame : List RVal → Prop := fun oldEnv =>
    VEnvRealizes output oldEnv envRoots ∧ SlotsRealize output oldEnv slots
  have hnext : CodeOwns ctx cur
      (OwnsPushedRoot frame cur.result (envRoots ++ rest)) post code := by
    intro nextFuel nextStore nextEnv resultStore resultValue hpushed hcodeRun
    apply hcode
    · exact ownsPushedRoot_result hpushed
    · exact hcodeRun
  have hcall : CodeOwns ctx cur
      (fun callStore callEnv =>
        frame callEnv ∧
        resolveAtoms callEnv (avs.map (·.toAtom output)).toArray =
          .ok values ∧
        RootOwnership callStore
          (rootsForWorlds worlds values ++ (envRoots ++ rest)))
      post
      (emitOp (.callSelf (avs.map (·.toAtom output)).toArray) code) :=
    emit_callSelf_owned hcontract post code hnext
  apply hcall
  · exact ⟨⟨houtput, hslots⟩, havs.resolveAtoms,
      by simpa [List.append_assoc] using hown⟩
  · exact hrun

/-- Consume a homogeneous argument prefix as the fields of a fresh
constructor. This is the whole-value ownership rule used by saturated
constructor spines in `knownCall`. -/
theorem LowerArgsSound.alloc_owned {ctx : Ctx} {cur : FnDef}
    {input output : VEnv} {world : Owned} {emit : Emit}
    {avs : List AVal} {cid : CtorId}
    (hargs : LowerArgsSound ctx cur input output
      (List.replicate avs.length world) emit avs) :
    LowerResultSound ctx cur input output.bump world
      (emit ∘ emitOp
        (.alloc world cid (avs.map (·.toAtom output)).toArray))
      (.slotA output.depth) := by
  refine ⟨.slot, ?_⟩
  intro rest slots
  apply EmitSound.comp (hargs.emits rest slots)
  intro post code hcode
  intro fuel store env finalStore finalValue hpre hrun
  obtain ⟨⟨envRoots, values, houtput, havs, hown⟩, hslots⟩ := hpre
  let frame : List RVal → Prop := fun oldEnv =>
    VEnvRealizes output oldEnv envRoots ∧ SlotsRealize output oldEnv slots
  have hnext : CodeOwns ctx cur
      (OwnsPushedRoot frame world (envRoots ++ rest)) post code := by
    intro nextFuel nextStore nextEnv resultStore resultValue hpushed hcodeRun
    apply hcode
    · exact ownsPushedRoot_result hpushed
    · exact hcodeRun
  have halloc : CodeOwns ctx cur
      (fun allocStore allocEnv =>
        frame allocEnv ∧
        resolveAtoms allocEnv (avs.map (·.toAtom output)).toArray =
          .ok values ∧
        RootOwnership allocStore
          (rootsFor world values ++ (envRoots ++ rest)))
      post
      (emitOp (.alloc world cid (avs.map (·.toAtom output)).toArray)
        code) :=
    emit_alloc_owned post code hnext
  have hvaluesLength : values.length = avs.length := havs.lengths.2.symm
  have hroots : rootsForWorlds (List.replicate avs.length world) values =
      rootsFor world values :=
    rootsForWorlds_replicate_eq_rootsFor world hvaluesLength
  apply halloc
  · exact ⟨⟨houtput, hslots⟩, havs.resolveAtoms,
      by simpa [hroots, List.append_assoc] using hown⟩
  · exact hrun

/-- Semantic constructor allocation. The related source arguments become
the fields of the fresh constructor graph, while the output environment and
caller frame transport through the allocation unchanged. -/
theorem LowerArgsValueSound.alloc_graph
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef}
    {input output : VEnv}
    {sourceInput sourceOutput sourceValues : List IxIR0.Value}
    {sourceAddress : Ixon.Address} {sourceTag : Nat}
    {world : Owned} {emit : Emit} {avs : List AVal} {cid : CtorId}
    (hargs : LowerArgsValueSound funRel recSelfRel ctx cur input output
      sourceInput sourceOutput sourceValues
      (List.replicate avs.length world) emit avs)
    (haddress : cid.block = sourceAddress)
    (htag : cid.cidx = sourceTag) :
    LowerResultValueSound funRel recSelfRel ctx cur input output.bump
      sourceInput sourceOutput (.ctor sourceAddress sourceTag sourceValues)
      world
      (emit ∘ emitOp
        (.alloc world cid (avs.map (·.toAtom output)).toArray))
      (.slotA output.depth) := by
  refine
    { toLowerResultSound := hargs.toLowerArgsSound.alloc_owned
      graphEmits := ?_ }
  intro sourceRest rest slots
  apply EmitSound.comp (hargs.graphEmits sourceRest rest slots)
  apply OpSound.emit
  intro fuel store env store' result hpre hrun
  obtain ⟨⟨envRoots, values, houtput, havs, hvalueGraphs,
      hrestGraph, hown⟩, hslots⟩ := hpre
  have hvaluesLength : values.length = avs.length :=
    havs.lengths.2.symm
  have hroots :
      rootsForWorlds (List.replicate avs.length world) values =
        rootsFor world values :=
    rootsForWorlds_replicate_eq_rootsFor world hvaluesLength
  have hown' : RootOwnership store
      (rootsFor world values ++ (envRoots ++ rest)) := by
    simpa [hroots, List.append_assoc] using hown
  cases fuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    obtain ⟨heval, hstore, hresultGraph, hresultOwn⟩ :=
      runOp_alloc_owned_valueGraph
        (ctx := ctx) (cur := cur) (fuel := fuel)
        havs.resolveAtoms haddress htag hvalueGraphs hown'
    have hpair :
        ((store.allocNode world (.ctorN cid values.toArray)).1,
          .loc (store.allocNode world (.ctorN cid values.toArray)).2) =
            (store', result) :=
      Except.ok.inj (heval.symm.trans hrun)
    cases hpair
    have houtput' := houtput.monoStore hstore
    have hrestGraph' := hrestGraph.monoStore hstore
    let ctorValue : RVal := .loc
      (store.allocNode world (.ctorN cid values.toArray)).2
    refine ⟨⟨envRoots, ctorValue, houtput'.bump ctorValue, ?_,
      hresultGraph, hrestGraph', hresultOwn⟩, hslots.bump ctorValue⟩
    apply AValRealizes.slot
    · simp [VEnv.bump]
    · simp [ctorValue, VEnv.bump, VEnv.rel]

/-- Fold a homogeneous shared argument prefix into a fresh partial-
application node. -/
theorem LowerArgsSound.papp_owned {ctx : Ctx} {cur : FnDef}
    {input output : VEnv} {emit : Emit} {avs : List AVal}
    {f : Ixon.Address} {d : Decl}
    (hargs : LowerArgsSound ctx cur input output
      (List.replicate avs.length .shared) emit avs)
    (hdecl : ctx.decls f = some d)
    (hunder : avs.length < declArity d) :
    LowerResultSound ctx cur input output.bump .shared
      (emit ∘ emitOp (.papp f (avs.map (·.toAtom output)).toArray))
      (.slotA output.depth) := by
  refine ⟨.slot, ?_⟩
  intro rest slots
  apply EmitSound.comp (hargs.emits rest slots)
  intro post code hcode
  intro fuel store env finalStore finalValue hpre hrun
  obtain ⟨⟨envRoots, values, houtput, havs, hown⟩, hslots⟩ := hpre
  let frame : List RVal → Prop := fun oldEnv =>
    VEnvRealizes output oldEnv envRoots ∧ SlotsRealize output oldEnv slots
  have hnext : CodeOwns ctx cur
      (OwnsPushedRoot frame .shared (envRoots ++ rest)) post code := by
    intro nextFuel nextStore nextEnv resultStore resultValue hpushed hcodeRun
    apply hcode
    · exact ownsPushedRoot_result hpushed
    · exact hcodeRun
  have hvaluesLength : values.length = avs.length := havs.lengths.2.symm
  have hunderValues : values.length < declArity d := by
    simpa [hvaluesLength] using hunder
  have hpapp : CodeOwns ctx cur
      (fun pappStore pappEnv =>
        frame pappEnv ∧
        resolveAtoms pappEnv (avs.map (·.toAtom output)).toArray =
          .ok values ∧
        RootOwnership pappStore
          (rootsFor .shared values ++ (envRoots ++ rest)))
      post
      (emitOp (.papp f (avs.map (·.toAtom output)).toArray) code) :=
    emit_papp_owned hdecl hunderValues post code hnext
  have hroots :
      rootsForWorlds (List.replicate avs.length .shared) values =
        rootsFor .shared values :=
    rootsForWorlds_replicate_eq_rootsFor .shared hvaluesLength
  apply hpapp
  · exact ⟨⟨houtput, hslots⟩, havs.resolveAtoms,
      by simpa [hroots, List.append_assoc] using hown⟩
  · exact hrun

/-- Semantic pap allocation. Besides conserving roots, the fresh shared node
realizes a source function value whose complete stored prefix is the related
source argument vector produced by `LowerArgsValueSound`. -/
theorem LowerArgsValueSound.papp_graph
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef}
    {input output : VEnv}
    {sourceInput sourceOutput sourceValues : List IxIR0.Value}
    {sourceValue : IxIR0.Value} {emit : Emit} {avs : List AVal}
    {f : Ixon.Address} {d : Decl}
    (hargs : LowerArgsValueSound funRel recSelfRel ctx cur input output
      sourceInput sourceOutput sourceValues
      (List.replicate avs.length .shared) emit avs)
    (hdecl : ctx.decls f = some d)
    (hfun : funRel sourceValue f (declArity d) sourceValues)
    (hunder : avs.length < declArity d) :
    LowerResultValueSound funRel recSelfRel ctx cur input output.bump
      sourceInput sourceOutput sourceValue .shared
      (emit ∘ emitOp (.papp f (avs.map (·.toAtom output)).toArray))
      (.slotA output.depth) := by
  refine
    { toLowerResultSound :=
        hargs.toLowerArgsSound.papp_owned hdecl hunder
      graphEmits := ?_ }
  intro sourceRest rest slots
  apply EmitSound.comp (hargs.graphEmits sourceRest rest slots)
  apply OpSound.emit
  intro fuel store env store' result hpre hrun
  obtain ⟨⟨envRoots, values, houtput, havs, hvalueGraphs,
      hrestGraph, hown⟩, hslots⟩ := hpre
  have hvaluesLength : values.length = avs.length :=
    havs.lengths.2.symm
  have hunderValues : values.length < declArity d := by
    simpa [hvaluesLength] using hunder
  have hroots :
      rootsForWorlds (List.replicate avs.length .shared) values =
        rootsFor .shared values :=
    rootsForWorlds_replicate_eq_rootsFor .shared hvaluesLength
  have hown' : RootOwnership store
      (rootsFor .shared values ++ (envRoots ++ rest)) := by
    simpa [hroots, List.append_assoc] using hown
  cases fuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    obtain ⟨heval, hstore, hresultGraph, hresultOwn⟩ :=
      runOp_papp_owned_valueGraph
        (ctx := ctx) (cur := cur) (fuel := fuel)
        havs.resolveAtoms hdecl hunderValues hfun hvalueGraphs hown'
    have hpair :
        ((store.allocNode .shared
            (.papN f (declArity d) values.toArray)).1,
          .loc (store.allocNode .shared
            (.papN f (declArity d) values.toArray)).2) =
            (store', result) :=
      Except.ok.inj (heval.symm.trans hrun)
    cases hpair
    have houtput' := houtput.monoStore hstore
    have hrestGraph' := hrestGraph.monoStore hstore
    let papValue : RVal := .loc (store.allocNode .shared
      (.papN f (declArity d) values.toArray)).2
    refine ⟨⟨envRoots, papValue, houtput'.bump papValue, ?_,
      hresultGraph, hrestGraph', hresultOwn⟩, hslots.bump papValue⟩
    apply AValRealizes.slot
    · simp [VEnv.bump]
    · simp [papValue, VEnv.bump, VEnv.rel]

/-- Consume a homogeneous shared argument prefix through the scalar-only
extern ABI and package its scalar result at the demanded world. -/
theorem LowerArgsSound.extern_owned {ctx : Ctx} {cur : FnDef}
    {input output : VEnv} {emit : Emit} {avs : List AVal}
    {f : Ixon.Address} {resultWorld : Owned}
    (hargs : LowerArgsSound ctx cur input output
      (List.replicate avs.length .shared) emit avs) :
    LowerResultSound ctx cur input output.bump resultWorld
      (emit ∘ emitOp (.extern f (avs.map (·.toAtom output)).toArray))
      (.slotA output.depth) := by
  refine ⟨.slot, ?_⟩
  intro rest slots
  apply EmitSound.comp (hargs.emits rest slots)
  intro post code hcode
  intro fuel store env finalStore finalValue hpre hrun
  obtain ⟨⟨envRoots, values, houtput, havs, hown⟩, hslots⟩ := hpre
  let frame : List RVal → Prop := fun oldEnv =>
    VEnvRealizes output oldEnv envRoots ∧ SlotsRealize output oldEnv slots
  have hnext : CodeOwns ctx cur
      (OwnsPushedRoot frame resultWorld (envRoots ++ rest)) post code := by
    intro nextFuel nextStore nextEnv resultStore resultValue hpushed hcodeRun
    apply hcode
    · exact ownsPushedRoot_result hpushed
    · exact hcodeRun
  have hextern : CodeOwns ctx cur
      (fun externStore externEnv =>
        frame externEnv ∧
        resolveAtoms externEnv (avs.map (·.toAtom output)).toArray =
          .ok values ∧
        RootOwnership externStore
          (rootsFor .shared values ++ (envRoots ++ rest)))
      post
      (emitOp (.extern f (avs.map (·.toAtom output)).toArray) code) :=
    emit_extern_owned post code hnext
  have hvaluesLength : values.length = avs.length := havs.lengths.2.symm
  have hroots :
      rootsForWorlds (List.replicate avs.length .shared) values =
        rootsFor .shared values :=
    rootsForWorlds_replicate_eq_rootsFor .shared hvaluesLength
  apply hextern
  · exact ⟨⟨houtput, hslots⟩, havs.resolveAtoms,
      by simpa [hroots, List.append_assoc] using hown⟩
  · exact hrun

/-- Lower shared arguments while protecting an already-produced function
descriptor, then consume the function root and argument prefix together via
the context's higher-order apply contract. -/
theorem LowerArgsSound.apply_owned {ctx : Ctx} {cur : FnDef}
    {input output : VEnv} {emit : Emit} {avs : List AVal}
    {function : AVal}
    (hargs : LowerArgsSound ctx cur input output
      (List.replicate avs.length .shared) emit avs)
    (hfunctionStable : AValStable function)
    (hcontract : ApplyOwnershipContract ctx) :
    ∀ rest slots,
      EmitSound ctx cur
        (emit ∘ emitOp (.apply (function.toAtom output)
          (avs.map (·.toAtom output)).toArray))
        (OwnsResultProtected input .shared function rest slots)
        (OwnsResultProtected output.bump .shared (.slotA output.depth)
          rest slots) := by
  intro rest slots post code hcode
  intro fuel store env finalStore finalValue hfunctionPre hrun
  obtain ⟨⟨envRoots, functionValue, hinput, hfunction, hownFunction⟩,
    hslots⟩ := hfunctionPre
  let functionRoot : Root := ⟨.shared, functionValue⟩
  have hfunctionProtection :
      SlotsRealize input env (aValProtection function functionValue) :=
    hfunctionStable.protection_realized hfunction
  have hargsOwn : RootOwnership store (envRoots ++ functionRoot :: rest) := by
    apply hownFunction.perm
    simpa [functionRoot] using
      (perm_extract_root functionRoot envRoots [] rest).symm
  have hargsPre : OwnsVEnvProtected input (functionRoot :: rest)
      (aValProtection function functionValue ++ slots) store env :=
    ⟨⟨envRoots, hinput, hargsOwn⟩, hfunctionProtection.append hslots⟩
  have hargsCont : CodeOwns ctx cur
      (OwnsArgsResultProtected output
        (List.replicate avs.length .shared) avs (functionRoot :: rest)
        (aValProtection function functionValue ++ slots))
      post
      (emitOp (.apply (function.toAtom output)
        (avs.map (·.toAtom output)).toArray) code) := by
    intro argsFuel argsStore argsEnv resultStore resultValue hargsPost happlyRun
    obtain ⟨⟨outRoots, values, houtput, havs, hownArgs⟩,
      hslotsOut⟩ := hargsPost
    have hfunctionFinal : AValRealizes output argsEnv function functionValue :=
      hfunctionStable.realize_of_protection hfunction
        hslotsOut.left_of_append
    have hvaluesLength : values.length = avs.length := havs.lengths.2.symm
    have hroots :
        rootsForWorlds (List.replicate avs.length .shared) values =
          rootsFor .shared values :=
      rootsForWorlds_replicate_eq_rootsFor .shared hvaluesLength
    have hownApply : RootOwnership argsStore
        (functionRoot :: rootsFor .shared values ++ (outRoots ++ rest)) := by
      apply hownArgs.perm
      simpa [functionRoot, hroots, List.append_assoc] using
        (perm_extract_root functionRoot
          (rootsForWorlds (List.replicate avs.length .shared) values ++
            outRoots) [] rest)
    let frame : List RVal → Prop := fun oldEnv =>
      VEnvRealizes output oldEnv outRoots ∧
        SlotsRealize output oldEnv slots
    have hnext : CodeOwns ctx cur
        (OwnsPushedRoot frame .shared (outRoots ++ rest)) post code := by
      intro nextFuel nextStore nextEnv endStore endValue hpushed hcodeRun
      apply hcode
      · exact ownsPushedRoot_result hpushed
      · exact hcodeRun
    have happly : CodeOwns ctx cur
        (fun applyStore applyEnv =>
          frame applyEnv ∧
          resolveAtom applyEnv (function.toAtom output) =
            .ok functionValue ∧
          resolveAtoms applyEnv (avs.map (·.toAtom output)).toArray =
            .ok values ∧
          RootOwnership applyStore
            (functionRoot :: rootsFor .shared values ++ (outRoots ++ rest)))
        post
        (emitOp (.apply (function.toAtom output)
          (avs.map (·.toAtom output)).toArray) code) :=
      emit_apply_owned hcontract post code hnext
    apply happly
    · exact ⟨⟨houtput, hslotsOut.right_of_append⟩,
        hfunctionFinal.resolveAtom, havs.resolveAtoms, hownApply⟩
    · exact happlyRun
  have hargsCode : CodeOwns ctx cur
      (OwnsVEnvProtected input (functionRoot :: rest)
        (aValProtection function functionValue ++ slots)) post
      (emit (emitOp (.apply (function.toAtom output)
        (avs.map (·.toAtom output)).toArray) code)) :=
    hargs.emits (functionRoot :: rest)
      (aValProtection function functionValue ++ slots)
      post _ hargsCont
  exact hargsCode hargsPre hrun

/-- Full non-erased `applyRest` semantic composition, abstracting only the
executable recursive calls: first produce a shared function, lower all
supplied shared arguments, then apply under the context contract. -/
theorem LowerResultSound.applyArgs {ctx : Ctx} {cur : FnDef}
    {start input output : VEnv} {emitFunction emitArgs : Emit}
    {function : AVal} {avs : List AVal}
    (hfunction : LowerResultSound ctx cur start input .shared
      emitFunction function)
    (hargs : LowerArgsSound ctx cur input output
      (List.replicate avs.length .shared) emitArgs avs)
    (hcontract : ApplyOwnershipContract ctx) :
    LowerResultSound ctx cur start output.bump .shared
      ((emitFunction ∘ emitArgs) ∘
        emitOp (.apply (function.toAtom output)
          (avs.map (·.toAtom output)).toArray))
      (.slotA output.depth) := by
  refine ⟨.slot, ?_⟩
  intro rest slots
  have hcomposed := EmitSound.comp (hfunction.emits rest slots)
    (hargs.apply_owned hfunction.stable hcontract rest slots)
  simpa [Function.comp_def] using hcomposed

/-- Bounded higher-order application after shared argument lowering. -/
theorem LowerArgsSoundBelow.apply_owned
    {ctx : Ctx} {cur : FnDef} {limit : Nat}
    {input output : VEnv} {emit : Emit} {avs : List AVal}
    {function : AVal}
    (hargs : LowerArgsSoundBelow ctx cur limit input output
      (List.replicate avs.length .shared) emit avs)
    (hfunctionStable : AValStable function)
    (hcontract : ApplyOwnershipContractBelow ctx limit) :
    ∀ rest slots,
      EmitSoundBelow ctx cur limit
        (emit ∘ emitOp (.apply (function.toAtom output)
          (avs.map (·.toAtom output)).toArray))
        (OwnsResultProtected input .shared function rest slots)
        (OwnsResultProtected output.bump .shared (.slotA output.depth)
          rest slots) := by
  intro rest slots bound hbound post code hcode
  intro fuel store env finalStore finalValue hfuel hfunctionPre hrun
  obtain ⟨⟨envRoots, functionValue, hinput, hfunction, hownFunction⟩,
    hslots⟩ := hfunctionPre
  let functionRoot : Root := ⟨.shared, functionValue⟩
  have hfunctionProtection :
      SlotsRealize input env (aValProtection function functionValue) :=
    hfunctionStable.protection_realized hfunction
  have hargsOwn : RootOwnership store (envRoots ++ functionRoot :: rest) := by
    apply hownFunction.perm
    simpa [functionRoot] using
      (perm_extract_root functionRoot envRoots [] rest).symm
  have hargsPre : OwnsVEnvProtected input (functionRoot :: rest)
      (aValProtection function functionValue ++ slots) store env :=
    ⟨⟨envRoots, hinput, hargsOwn⟩, hfunctionProtection.append hslots⟩
  have hargsCont : CodeOwnsBelow ctx cur bound
      (OwnsArgsResultProtected output
        (List.replicate avs.length .shared) avs (functionRoot :: rest)
        (aValProtection function functionValue ++ slots))
      post
      (emitOp (.apply (function.toAtom output)
        (avs.map (·.toAtom output)).toArray) code) := by
    intro argsFuel argsStore argsEnv resultStore resultValue hargsFuel
      hargsPost happlyRun
    obtain ⟨⟨outRoots, values, houtput, havs, hownArgs⟩,
      hslotsOut⟩ := hargsPost
    have hfunctionFinal : AValRealizes output argsEnv function functionValue :=
      hfunctionStable.realize_of_protection hfunction
        hslotsOut.left_of_append
    have hvaluesLength : values.length = avs.length := havs.lengths.2.symm
    have hroots :
        rootsForWorlds (List.replicate avs.length .shared) values =
          rootsFor .shared values :=
      rootsForWorlds_replicate_eq_rootsFor .shared hvaluesLength
    have hownApply : RootOwnership argsStore
        (functionRoot :: rootsFor .shared values ++ (outRoots ++ rest)) := by
      apply hownArgs.perm
      simpa [functionRoot, hroots, List.append_assoc] using
        (perm_extract_root functionRoot
          (rootsForWorlds (List.replicate avs.length .shared) values ++
            outRoots) [] rest)
    let frame : List RVal → Prop := fun oldEnv =>
      VEnvRealizes output oldEnv outRoots ∧
        SlotsRealize output oldEnv slots
    have hnext : CodeOwnsBelow ctx cur bound
        (OwnsPushedRoot frame .shared (outRoots ++ rest)) post code := by
      intro nextFuel nextStore nextEnv endStore endValue hnextFuel
        hpushed hcodeRun
      apply hcode hnextFuel
      · exact ownsPushedRoot_result hpushed
      · exact hcodeRun
    have happly : CodeOwnsBelow ctx cur bound
        (fun applyStore applyEnv =>
          frame applyEnv ∧
          resolveAtom applyEnv (function.toAtom output) =
            .ok functionValue ∧
          resolveAtoms applyEnv (avs.map (·.toAtom output)).toArray =
            .ok values ∧
          RootOwnership applyStore
            (functionRoot :: rootsFor .shared values ++ (outRoots ++ rest)))
        post
        (emitOp (.apply (function.toAtom output)
          (avs.map (·.toAtom output)).toArray) code) :=
      (emit_apply_owned_below hcontract) bound hbound post code hnext
    apply happly hargsFuel
    · exact ⟨⟨houtput, hslotsOut.right_of_append⟩,
        hfunctionFinal.resolveAtom, havs.resolveAtoms, hownApply⟩
    · exact happlyRun
  have hargsCode : CodeOwnsBelow ctx cur bound
      (OwnsVEnvProtected input (functionRoot :: rest)
        (aValProtection function functionValue ++ slots)) post
      (emit (emitOp (.apply (function.toAtom output)
        (avs.map (·.toAtom output)).toArray) code)) :=
    hargs.emits (functionRoot :: rest)
      (aValProtection function functionValue ++ slots)
      bound hbound post _ hargsCont
  exact hargsCode hfuel hargsPre hrun

/-- Bounded semantic composition for the non-erased `applyRest` path. -/
theorem LowerResultSoundBelow.applyArgs
    {ctx : Ctx} {cur : FnDef} {limit : Nat}
    {start input output : VEnv} {emitFunction emitArgs : Emit}
    {function : AVal} {avs : List AVal}
    (hfunction : LowerResultSoundBelow ctx cur limit start input .shared
      emitFunction function)
    (hargs : LowerArgsSoundBelow ctx cur limit input output
      (List.replicate avs.length .shared) emitArgs avs)
    (hcontract : ApplyOwnershipContractBelow ctx limit) :
    LowerResultSoundBelow ctx cur limit start output.bump .shared
      ((emitFunction ∘ emitArgs) ∘
        emitOp (.apply (function.toAtom output)
          (avs.map (·.toAtom output)).toArray))
      (.slotA output.depth) := by
  refine ⟨.slot, ?_⟩
  intro rest slots
  have hcomposed := EmitSoundBelow.comp (hfunction.emits rest slots)
    (hargs.apply_owned hfunction.stable hcontract rest slots)
  simpa [Function.comp_def] using hcomposed

/-! ## Erased-result argument release -/

/-- Skipping a stable constant argument consumes its scalar logical root
without changing the store or runtime environment. -/
theorem discard_const_arg {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {atom : Atom} {worlds : List Owned} {avs : List AVal}
    (hstable : AValStable (.constA atom)) :
    ∀ rest slots,
      EmitSound ctx cur (_root_.id : Emit)
        (OwnsArgsResultProtected Γ (.shared :: worlds)
          (.constA atom :: avs) rest slots)
        (OwnsArgsResultProtected Γ worlds avs rest slots) := by
  intro rest slots
  apply EmitSound.strengthen
  intro store env hpre
  obtain ⟨⟨roots, values, hΓ, havs, hown⟩, hslots⟩ := hpre
  cases havs with
  | @cons headWorld tailWorlds headAV tailAVs value tailValues hav htail =>
    have howned : RootOwnership store
        (⟨.shared, value⟩ ::
          (rootsForWorlds worlds tailValues ++ roots ++ rest)) := by
      simpa [rootsForWorlds] using hown
    exact ⟨⟨roots, tailValues, hΓ, htail,
      howned.dropNoLocation (hstable.const_noLocation hav)⟩, hslots⟩

/-- Semantic constant discard removes the inert head argument and its source
value while leaving every remaining graph and the store unchanged. -/
theorem discard_const_arg_value
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value} {source : IxIR0.Value}
    {sources : List IxIR0.Value} {atom : Atom}
    {worlds : List Owned} {avs : List AVal}
    (hstable : AValStable (.constA atom)) :
    ∀ sourceRest rest slots,
      EmitSound ctx cur (_root_.id : Emit)
        (GraphOwnsArgsResultProtected funRel recSelfRel Γ
          sourceEnv (source :: sources) (.shared :: worlds)
          (.constA atom :: avs) sourceRest rest slots)
        (GraphOwnsArgsResultProtected funRel recSelfRel Γ
          sourceEnv sources worlds avs sourceRest rest slots) := by
  intro sourceRest rest slots
  apply EmitSound.strengthen
  intro store env hpre
  obtain ⟨⟨roots, values, hΓ, havs, hvalueGraphs,
      hrestGraph, hown⟩, hslots⟩ := hpre
  cases havs with
  | @cons headWorld tailWorlds headAV tailAVs value tailValues hav htail =>
    cases hvalueGraphs with
    | cons hvalueGraph htailGraphs =>
      have howned : RootOwnership store
          (⟨.shared, value⟩ ::
            (rootsForWorlds worlds tailValues ++ roots ++ rest)) := by
        simpa [rootsForWorlds] using hown
      exact ⟨⟨roots, tailValues, hΓ, htail, htailGraphs,
        hrestGraph,
        howned.dropNoLocation (hstable.const_noLocation hav)⟩,
        hslots⟩

theorem discard_const_arg_below {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {Γ : VEnv} {atom : Atom}
    {worlds : List Owned} {avs : List AVal}
    (hstable : AValStable (.constA atom)) :
    ∀ rest slots,
      EmitSoundBelow ctx cur limit (_root_.id : Emit)
        (OwnsArgsResultProtected Γ (.shared :: worlds)
          (.constA atom :: avs) rest slots)
        (OwnsArgsResultProtected Γ worlds avs rest slots) := by
  intro rest slots
  apply EmitSoundBelow.strengthen
  intro store env hpre
  obtain ⟨⟨roots, values, hΓ, havs, hown⟩, hslots⟩ := hpre
  cases havs with
  | @cons headWorld tailWorlds headAV tailAVs value tailValues hav htail =>
    have howned : RootOwnership store
        (⟨.shared, value⟩ ::
          (rootsForWorlds worlds tailValues ++ roots ++ rest)) := by
      simpa [rootsForWorlds] using hown
    exact ⟨⟨roots, tailValues, hΓ, htail,
      howned.dropNoLocation (hstable.const_noLocation hav)⟩, hslots⟩

/-- Forget an ownership-inert constant result before continuing with a
consumer that needs only the surrounding source environment. -/
theorem discard_const_result {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {world : Owned} {atom : Atom} (hstable : AValStable (.constA atom)) :
    ∀ rest slots,
      EmitSound ctx cur (_root_.id : Emit)
        (OwnsResultProtected Γ world (.constA atom) rest slots)
        (OwnsVEnvProtected Γ rest slots) := by
  intro rest slots
  apply EmitSound.strengthen
  intro store env hpre
  obtain ⟨⟨roots, value, hΓ, hav, hown⟩, hslots⟩ := hpre
  exact ⟨⟨roots, hΓ,
    hown.dropNoLocation (hstable.const_noLocation hav)⟩, hslots⟩

/-- Semantic constant-result discard removes an ownership-inert result root
before a continuation that needs only the related source environment. -/
theorem discard_const_result_value
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value} {sourceValue : IxIR0.Value}
    {world : Owned} {atom : Atom}
    (hstable : AValStable (.constA atom)) :
    ∀ sourceRest rest slots,
      EmitSound ctx cur (_root_.id : Emit)
        (GraphOwnsResultProtected funRel recSelfRel Γ sourceEnv
          sourceValue world (.constA atom) sourceRest rest slots)
        (GraphOwnsVEnvProtected funRel recSelfRel Γ sourceEnv
          sourceRest rest slots) := by
  intro sourceRest rest slots
  apply EmitSound.strengthen
  intro store env hpre
  obtain ⟨⟨roots, value, hΓ, hav, _, hrestGraph, hown⟩,
      hslots⟩ := hpre
  exact ⟨⟨roots, hΓ, hrestGraph,
    hown.dropNoLocation (hstable.const_noLocation hav)⟩, hslots⟩

theorem discard_const_result_below {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {Γ : VEnv} {world : Owned} {atom : Atom}
    (hstable : AValStable (.constA atom)) :
    ∀ rest slots,
      EmitSoundBelow ctx cur limit (_root_.id : Emit)
        (OwnsResultProtected Γ world (.constA atom) rest slots)
        (OwnsVEnvProtected Γ rest slots) := by
  intro rest slots
  apply EmitSoundBelow.strengthen
  intro store env hpre
  obtain ⟨⟨roots, value, hΓ, hav, hown⟩, hslots⟩ := hpre
  exact ⟨⟨roots, hΓ,
    hown.dropNoLocation (hstable.const_noLocation hav)⟩, hslots⟩

/-! ## Let-binder installation -/

/-- Install a logical binder that aliases an already existing absolute slot;
no runtime value is pushed. -/
def installAliasBinder (Γ : VEnv) (abs remaining : Nat)
    (uses : Uses) (held : Bool) : VEnv :=
  { Γ with entries := .slot abs remaining uses held :: Γ.entries }

/-- Install a logical binder for the result of a runtime operation that has
just pushed a fresh slot. -/
def installPushedBinder (Γ : VEnv) (remaining : Nat)
    (uses : Uses) (held : Bool) : VEnv :=
  { entries := .slot Γ.depth remaining uses held :: Γ.entries,
    depth := Γ.depth + 1 }

/-- Ownership interface shared by alias and materialized let-binder
installation. -/
def InstallBinderSound (ctx : Ctx) (cur : FnDef)
    (input output : VEnv) (boundWorld : Owned)
    (boundValue : AVal) (emit : Emit) : Prop :=
  ∀ rest slots,
    EmitSound ctx cur emit
      (OwnsResultProtected input boundWorld boundValue rest slots)
      (OwnsVEnvProtected output rest slots)

/-- Semantic binder installation moves the source result into the leading
source-environment entry consumed by the let body. -/
structure InstallBinderValueSound (funRel : Sim.FunctionRel)
    (recSelfRel : RecSelfRel) (ctx : Ctx) (cur : FnDef)
    (input output : VEnv) (sourceEnv : List IxIR0.Value)
    (boundSource : IxIR0.Value) (boundWorld : Owned)
    (boundValue : AVal) (emit : Emit) : Prop where
  toInstallBinderSound : InstallBinderSound ctx cur input output
    boundWorld boundValue emit
  graphEmits : ∀ sourceRest rest slots,
    EmitSound ctx cur emit
      (GraphOwnsResultProtected funRel recSelfRel input sourceEnv
        boundSource boundWorld boundValue sourceRest rest slots)
      (GraphOwnsVEnvProtected funRel recSelfRel output
        (boundSource :: sourceEnv) sourceRest rest slots)

/-- Move a slot-backed expression result into a live let binder without an
operation. The distinguished result root becomes the binder's environment
root at the same physical slot. -/
theorem installAliasBinder_held_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {Γ : VEnv}
    {abs remaining : Nat} {uses : Uses} :
    ∀ rest slots,
      EmitSoundBelow ctx cur limit (_root_.id : Emit)
        (OwnsResultProtected Γ (worldOfUses uses) (.slotA abs) rest slots)
        (OwnsVEnvProtected
          (installAliasBinder Γ abs remaining uses true) rest slots) := by
  intro rest slots
  apply EmitSoundBelow.strengthen
  intro store env hpre
  obtain ⟨⟨roots, value, hΓ, hav, hown⟩, hslots⟩ := hpre
  cases hav with
  | slot hbound hslot =>
    let output := installAliasBinder Γ abs remaining uses true
    have htail : EntriesRealize output env Γ.entries roots :=
      hΓ.entries.of_depth_eq (by simp [output, installAliasBinder])
    have houtput : VEnvRealizes output env
        (⟨worldOfUses uses, value⟩ :: roots) := by
      refine ⟨by simpa [output, installAliasBinder] using hΓ.depth_eq, ?_⟩
      exact EntriesRealize.held
        (by simpa [output, installAliasBinder] using hbound)
        (by simpa [output, installAliasBinder, VEnv.rel] using hslot)
        htail
    refine ⟨⟨⟨worldOfUses uses, value⟩ :: roots, houtput, ?_⟩, ?_⟩
    · simpa using hown
    · exact SlotsRealize.of_depth_eq
        (by simp [output, installAliasBinder]) hslots

theorem installAliasBinder_held
    {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {abs remaining : Nat} {uses : Uses} :
    ∀ rest slots,
      EmitSound ctx cur (_root_.id : Emit)
        (OwnsResultProtected Γ (worldOfUses uses) (.slotA abs) rest slots)
        (OwnsVEnvProtected
          (installAliasBinder Γ abs remaining uses true) rest slots) := by
  intro rest slots
  exact EmitSound.of_below fun limit =>
    installAliasBinder_held_below
      (ctx := ctx) (cur := cur) (limit := limit)
      (Γ := Γ) (abs := abs) (remaining := remaining) (uses := uses)
      rest slots

/-- Semantic alias installation moves the bound result graph into a new
leading held environment entry without changing the runtime stack. -/
theorem installAliasBinder_held_value
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value} {boundSource : IxIR0.Value}
    {abs remaining : Nat} {uses : Uses} :
    ∀ sourceRest rest slots,
      EmitSound ctx cur (_root_.id : Emit)
        (GraphOwnsResultProtected funRel recSelfRel Γ sourceEnv
          boundSource (worldOfUses uses) (.slotA abs)
          sourceRest rest slots)
        (GraphOwnsVEnvProtected funRel recSelfRel
          (installAliasBinder Γ abs remaining uses true)
          (boundSource :: sourceEnv) sourceRest rest slots) := by
  intro sourceRest rest slots
  apply EmitSound.strengthen
  intro store env hpre
  obtain ⟨⟨roots, value, hΓ, hav, hvalueGraph,
      hrestGraph, hown⟩, hslots⟩ := hpre
  cases hav with
  | slot hbound hslot =>
    let output := installAliasBinder Γ abs remaining uses true
    have htail : EntriesValueGraph funRel recSelfRel store output env
        Γ.entries sourceEnv roots :=
      hΓ.entries.of_depth_eq (by simp [output, installAliasBinder])
    have hvalueWorld : HasWorld store (worldOfUses uses) value :=
      hown.roots_world ⟨worldOfUses uses, value⟩ (by simp)
    have houtput : VEnvValueGraph funRel recSelfRel store output
        (boundSource :: sourceEnv) env
        (⟨worldOfUses uses, value⟩ :: roots) := by
      refine ⟨by simpa [output, installAliasBinder] using hΓ.depth_eq, ?_⟩
      exact EntriesValueGraph.held
        (by simpa [output, installAliasBinder] using hbound)
        (by simpa [output, installAliasBinder, VEnv.rel] using hslot)
        hvalueWorld hvalueGraph htail
    refine ⟨⟨⟨worldOfUses uses, value⟩ :: roots,
      houtput, hrestGraph, ?_⟩, ?_⟩
    · simpa using hown
    · exact SlotsRealize.of_depth_eq
        (by simp [output, installAliasBinder]) hslots

theorem installAliasBinder_held_value_sound
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value} {boundSource : IxIR0.Value}
    {abs remaining : Nat} {uses : Uses} :
    InstallBinderValueSound funRel recSelfRel ctx cur Γ
      (installAliasBinder Γ abs remaining uses true)
      sourceEnv boundSource (worldOfUses uses) (.slotA abs)
      (_root_.id : Emit) :=
  { toInstallBinderSound := installAliasBinder_held
    graphEmits := installAliasBinder_held_value }

/-- Materialize a stable constant into the fresh physical slot used by a let
binder. A live binder owns the scalar root; a dead binder records only the
released entry, since scalar roots are ownership-inert. -/
theorem materializeConstBinder_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {Γ : VEnv}
    {atom : Atom} {remaining : Nat} {uses : Uses} {held : Bool}
    (hstable : AValStable (.constA atom)) :
    ∀ rest slots,
      EmitSoundBelow ctx cur limit (emitOp (.pure atom))
        (OwnsResultProtected Γ (worldOfUses uses) (.constA atom) rest slots)
        (OwnsVEnvProtected
          (installPushedBinder Γ remaining uses held) rest slots) := by
  intro rest slots
  apply OpSoundBelow.emit
  intro fuel store env store' result _ hpre hrun
  obtain ⟨⟨roots, value, hΓ, hav, hown⟩, hslots⟩ := hpre
  cases fuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    have hpure := runOp_pure (ctx := ctx) (cur := cur) (fuel := fuel)
      (store := store) hav.resolveAtom
    have hpair : (store, value) = (store', result) :=
      Except.ok.inj (hpure.symm.trans hrun)
    cases hpair
    let output := installPushedBinder Γ remaining uses held
    have htail : EntriesRealize output (result :: env) Γ.entries roots :=
      (hΓ.entries.bump result).of_depth_eq
        (by simp [output, installPushedBinder, VEnv.bump])
    have hdepth : (result :: env).length = output.depth := by
      simpa [output, installPushedBinder] using congrArg Nat.succ hΓ.depth_eq
    cases held with
    | false =>
      have houtput : VEnvRealizes output (result :: env) roots := by
        refine ⟨hdepth, ?_⟩
        exact EntriesRealize.released
          (by simp [output, installPushedBinder]) htail
      refine ⟨⟨roots, houtput, ?_⟩, ?_⟩
      · exact hown.dropNoLocation (hstable.const_noLocation hav)
      · exact SlotsRealize.of_depth_eq
          (by simp [output, installPushedBinder, VEnv.bump])
          (hslots.bump result)

    | true =>
      have houtput : VEnvRealizes output (result :: env)
          (⟨worldOfUses uses, result⟩ :: roots) := by
        refine ⟨hdepth, ?_⟩
        exact EntriesRealize.held
          (by simp [output, installPushedBinder])
          (by simp [output, installPushedBinder, VEnv.rel]) htail
      refine ⟨⟨⟨worldOfUses uses, result⟩ :: roots, houtput, ?_⟩, ?_⟩
      · simpa using hown
      · exact SlotsRealize.of_depth_eq
          (by simp [output, installPushedBinder, VEnv.bump])
          (hslots.bump result)

theorem materializeConstBinder
    {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {atom : Atom} {remaining : Nat} {uses : Uses} {held : Bool}
    (hstable : AValStable (.constA atom)) :
    ∀ rest slots,
      EmitSound ctx cur (emitOp (.pure atom))
        (OwnsResultProtected Γ (worldOfUses uses) (.constA atom) rest slots)
        (OwnsVEnvProtected
          (installPushedBinder Γ remaining uses held) rest slots) := by
  intro rest slots
  exact EmitSound.of_below fun limit =>
    materializeConstBinder_below
      (ctx := ctx) (cur := cur) (limit := limit)
      (Γ := Γ) (atom := atom) (remaining := remaining)
      (uses := uses) (held := held) hstable rest slots

/-- Semantic constant materialization installs the bound source value as a
leading held or released entry, matching the compile-time `held` flag. -/
theorem materializeConstBinder_value
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value} {boundSource : IxIR0.Value}
    {atom : Atom} {remaining : Nat} {uses : Uses} {held : Bool}
    (hstable : AValStable (.constA atom)) :
    ∀ sourceRest rest slots,
      EmitSound ctx cur (emitOp (.pure atom))
        (GraphOwnsResultProtected funRel recSelfRel Γ sourceEnv
          boundSource (worldOfUses uses) (.constA atom)
          sourceRest rest slots)
        (GraphOwnsVEnvProtected funRel recSelfRel
          (installPushedBinder Γ remaining uses held)
          (boundSource :: sourceEnv) sourceRest rest slots) := by
  intro sourceRest rest slots
  apply OpSound.emit
  intro fuel store env store' result hpre hrun
  obtain ⟨⟨roots, value, hΓ, hav, hvalueGraph,
      hrestGraph, hown⟩, hslots⟩ := hpre
  cases fuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    have hpure := runOp_pure (ctx := ctx) (cur := cur) (fuel := fuel)
      (store := store) hav.resolveAtom
    have hpair : (store, value) = (store', result) :=
      Except.ok.inj (hpure.symm.trans hrun)
    cases hpair
    let output := installPushedBinder Γ remaining uses held
    have htail : EntriesValueGraph funRel recSelfRel store output
        (result :: env) Γ.entries sourceEnv roots :=
      (hΓ.entries.bump result).of_depth_eq
        (by simp [output, installPushedBinder, VEnv.bump])
    have hdepth : (result :: env).length = output.depth := by
      simpa [output, installPushedBinder] using
        congrArg Nat.succ hΓ.depth_eq
    cases held with
    | false =>
      have houtput : VEnvValueGraph funRel recSelfRel store output
          (boundSource :: sourceEnv) (result :: env) roots := by
        refine ⟨hdepth, ?_⟩
        exact EntriesValueGraph.released
          (by simp [output, installPushedBinder]) htail
      refine ⟨⟨roots, houtput, hrestGraph, ?_⟩, ?_⟩
      · exact hown.dropNoLocation (hstable.const_noLocation hav)
      · exact SlotsRealize.of_depth_eq
          (by simp [output, installPushedBinder, VEnv.bump])
          (hslots.bump result)
    | true =>
      have hvalueWorld : HasWorld store (worldOfUses uses) result :=
        hown.roots_world ⟨worldOfUses uses, result⟩ (by simp)
      have houtput : VEnvValueGraph funRel recSelfRel store output
          (boundSource :: sourceEnv) (result :: env)
          (⟨worldOfUses uses, result⟩ :: roots) := by
        refine ⟨hdepth, ?_⟩
        exact EntriesValueGraph.held
          (by simp [output, installPushedBinder])
          (by simp [output, installPushedBinder, VEnv.rel])
          hvalueWorld hvalueGraph htail
      refine ⟨⟨⟨worldOfUses uses, result⟩ :: roots,
        houtput, hrestGraph, ?_⟩, ?_⟩
      · simpa using hown
      · exact SlotsRealize.of_depth_eq
          (by simp [output, installPushedBinder, VEnv.bump])
          (hslots.bump result)

theorem materializeConstBinder_value_sound
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value} {boundSource : IxIR0.Value}
    {atom : Atom} {remaining : Nat} {uses : Uses} {held : Bool}
    (hstable : AValStable (.constA atom)) :
    InstallBinderValueSound funRel recSelfRel ctx cur Γ
      (installPushedBinder Γ remaining uses held) sourceEnv boundSource
      (worldOfUses uses) (.constA atom) (emitOp (.pure atom)) :=
  { toInstallBinderSound := materializeConstBinder hstable
    graphEmits := materializeConstBinder_value hstable }

/-- Unbounded let sequencing through binder installation and the final
logical pop. -/
theorem LowerResultSound.installThen
    {ctx : Ctx} {cur : FnDef}
    {input middle installed output : VEnv}
    {boundWorld resultWorld : Owned}
    {boundEmit installEmit bodyEmit : Emit}
    {boundValue result : AVal}
    (hbound : LowerResultSound ctx cur input middle boundWorld
      boundEmit boundValue)
    (hinstall : InstallBinderSound ctx cur middle installed
      boundWorld boundValue installEmit)
    (hbody : LowerResultSound ctx cur installed output resultWorld
      bodyEmit result)
    (hreleased : FirstEntryReleased output) :
    LowerResultSound ctx cur input output.pop resultWorld
      ((boundEmit ∘ installEmit) ∘ bodyEmit) result := by
  have hpopped := hbody.popFirstReleased hreleased
  refine ⟨hpopped.stable, ?_⟩
  intro rest slots
  have hcomposed := EmitSound.comp (hbound.emits rest slots)
    (EmitSound.comp (hinstall rest slots) (hpopped.emits rest slots))
  simpa [Function.comp_def] using hcomposed

/-- Semantic let sequencing. The bound result becomes the leading source
environment value for the body; after the body releases that entry, `pop`
returns to the body's tail source environment. -/
theorem LowerResultValueSound.installThen
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef}
    {input middle installed output : VEnv}
    {sourceInput sourceMiddle sourceOutput : List IxIR0.Value}
    {boundSource sourceResult : IxIR0.Value}
    {boundWorld resultWorld : Owned}
    {boundEmit installEmit bodyEmit : Emit}
    {boundValue result : AVal}
    (hbound : LowerResultValueSound funRel recSelfRel ctx cur
      input middle sourceInput sourceMiddle boundSource boundWorld
      boundEmit boundValue)
    (hinstall : InstallBinderValueSound funRel recSelfRel ctx cur
      middle installed sourceMiddle boundSource boundWorld boundValue
      installEmit)
    (hbody : LowerResultValueSound funRel recSelfRel ctx cur
      installed output (boundSource :: sourceMiddle)
      (boundSource :: sourceOutput) sourceResult resultWorld
      bodyEmit result)
    (hreleased : FirstEntryReleased output) :
    LowerResultValueSound funRel recSelfRel ctx cur input output.pop
      sourceInput sourceOutput sourceResult resultWorld
      ((boundEmit ∘ installEmit) ∘ bodyEmit) result := by
  have hpopped := hbody.popFirstReleased hreleased
  refine
    { toLowerResultSound := hbound.toLowerResultSound.installThen
        hinstall.toInstallBinderSound hbody.toLowerResultSound hreleased
      graphEmits := ?_ }
  intro sourceRest rest slots
  have hcomposed := EmitSound.comp
    (hbound.graphEmits sourceRest rest slots)
    (EmitSound.comp (hinstall.graphEmits sourceRest rest slots)
      (hpopped.graphEmits sourceRest rest slots))
  simpa [Function.comp_def] using hcomposed

/-- Sequence an already proved bound value, its binder-installation emitter,
and a body that has consumed the installed first entry. The final logical
`pop` is justified by `FirstEntryReleased`; no runtime slot is removed. -/
theorem LowerResultSoundBelow.installThen
    {ctx : Ctx} {cur : FnDef} {limit : Nat}
    {input middle installed output : VEnv}
    {boundWorld resultWorld : Owned}
    {boundEmit installEmit bodyEmit : Emit}
    {boundValue result : AVal}
    (hbound : LowerResultSoundBelow ctx cur limit input middle boundWorld
      boundEmit boundValue)
    (hinstall : ∀ rest slots,
      EmitSoundBelow ctx cur limit installEmit
        (OwnsResultProtected middle boundWorld boundValue rest slots)
        (OwnsVEnvProtected installed rest slots))
    (hbody : LowerResultSoundBelow ctx cur limit installed output resultWorld
      bodyEmit result)
    (hreleased : FirstEntryReleased output) :
    LowerResultSoundBelow ctx cur limit input output.pop resultWorld
      ((boundEmit ∘ installEmit) ∘ bodyEmit) result := by
  have hpopped := hbody.popFirstReleased hreleased
  refine ⟨hpopped.stable, ?_⟩
  intro rest slots
  have hcomposed := EmitSoundBelow.comp (hbound.emits rest slots)
    (EmitSoundBelow.comp (hinstall rest slots) (hpopped.emits rest slots))
  simpa [Function.comp_def] using hcomposed

/-- Releasing a slot-backed shared argument emits one `drop`. Its inert
result slot bumps the `VEnv`, all remaining stable argument descriptors, and
the protected-slot frame while consuming exactly the head argument root. -/
theorem discard_slot_arg {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {abs : Nat} {worlds : List Owned} {avs : List AVal}
    (htailStable : AValsStable avs) :
    ∀ rest slots,
      EmitSound ctx cur (emitOp (.drop (.var (Γ.rel abs))))
        (OwnsArgsResultProtected Γ (.shared :: worlds)
          (.slotA abs :: avs) rest slots)
        (OwnsArgsResultProtected Γ.bump worlds avs rest slots) := by
  intro rest slots post code hcode
  intro fuel store env finalStore finalValue hpre hrun
  obtain ⟨⟨roots, values, hΓ, havs, hown⟩, hslots⟩ := hpre
  cases havs with
  | @cons headWorld tailWorlds headAV tailAVs value tailValues hav htail =>
    let frame : List RVal → Prop := fun oldEnv =>
      VEnvRealizes Γ oldEnv roots ∧
        AValsRealize Γ oldEnv worlds avs tailValues ∧
        SlotsRealize Γ oldEnv slots
    let remainingRoots := rootsForWorlds worlds tailValues ++ roots ++ rest
    have howned : RootOwnership store
        (⟨.shared, value⟩ :: remainingRoots) := by
      simpa [remainingRoots, rootsForWorlds] using hown
    have hnext : CodeOwns ctx cur
        (OwnsAfterPush frame remainingRoots) post code := by
      intro nextFuel nextStore nextEnv resultStore resultValue hpushed hcodeRun
      obtain ⟨pushed, oldEnv, rfl, ⟨hΓOld, htailOld, hslotsOld⟩,
        hownRest⟩ := hpushed
      apply hcode
      · exact ⟨⟨roots, tailValues, hΓOld.bump pushed,
          htailStable.realize_bump htailOld pushed, hownRest⟩,
          hslotsOld.bump pushed⟩
      · exact hcodeRun
    have hdrop : CodeOwns ctx cur
        (fun dropStore dropEnv =>
          frame dropEnv ∧
          resolveAtom dropEnv (.var (Γ.rel abs)) = .ok value ∧
          RootOwnership dropStore (⟨.shared, value⟩ :: remainingRoots))
        post (emitOp (.drop (.var (Γ.rel abs))) code) :=
      emit_drop_value_owned post code hnext
    apply hdrop
    · exact ⟨⟨hΓ, htail, hslots⟩, hav.resolveAtom, howned⟩
    · exact hrun

/-- Semantic slot discard transports the environment, remaining argument
vector, and caller frame through the destructive shared drop. -/
theorem discard_slot_arg_value
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value} {source : IxIR0.Value}
    {sources : List IxIR0.Value} {abs : Nat}
    {worlds : List Owned} {avs : List AVal}
    (htailStable : AValsStable avs) :
    ∀ sourceRest rest slots,
      EmitSound ctx cur (emitOp (.drop (.var (Γ.rel abs))))
        (GraphOwnsArgsResultProtected funRel recSelfRel Γ
          sourceEnv (source :: sources) (.shared :: worlds)
          (.slotA abs :: avs) sourceRest rest slots)
        (GraphOwnsArgsResultProtected funRel recSelfRel Γ.bump
          sourceEnv sources worlds avs sourceRest rest slots) := by
  intro sourceRest rest slots
  apply OpSound.emit
  intro fuel store env store' result hpre hrun
  cases fuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    obtain ⟨⟨roots, values, hΓ, havs, hvalueGraphs,
        hrestGraph, hown⟩, hslots⟩ := hpre
    cases havs with
    | @cons headWorld tailWorlds headAV tailAVs value tailValues hav htail =>
      cases hvalueGraphs with
      | cons hvalueGraph htailGraphs =>
        let remainingRoots :=
          rootsForWorlds worlds tailValues ++ roots ++ rest
        have howned : RootOwnership store
            (⟨.shared, value⟩ :: remainingRoots) := by
          simpa [remainingRoots, rootsForWorlds] using hown
        obtain ⟨rfl, hrestrict, hownAfter⟩ :=
          runOp_drop_value_owned_restricts hav.resolveAtom howned hrun
        have hΓAfter : VEnvValueGraph funRel recSelfRel store'
            Γ sourceEnv env roots :=
          hΓ.ofRestricts hrestrict hownAfter
            (fun root hmember => by
              simp [remainingRoots, hmember])
        have hlength : worlds.length = tailValues.length :=
          htail.lengths.1.trans htail.lengths.2
        have htailGraphsAfter :
            Sim.ValuesGraph funRel store' sources tailValues :=
          htailGraphs.ofRestrictsIn hrestrict hownAfter
            (fun runtime hmember => by
              obtain ⟨runtimeWorld, hroot⟩ :=
                exists_root_mem_rootsForWorlds hlength hmember
              exact ⟨runtimeWorld, by
                simp [remainingRoots, hroot]⟩)
        have hrestAfter : Sim.RootsGraph funRel store'
            sourceRest rest :=
          hrestGraph.ofRestrictsIn hrestrict hownAfter
            (fun root hmember => by
              simp [remainingRoots, hmember])
        exact ⟨⟨roots, tailValues, hΓAfter.bump .erased,
          htailStable.realize_bump htail .erased,
          htailGraphsAfter, hrestAfter, hownAfter⟩,
          hslots.bump .erased⟩

theorem discard_slot_arg_below {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {Γ : VEnv} {abs : Nat}
    {worlds : List Owned} {avs : List AVal}
    (htailStable : AValsStable avs) :
    ∀ rest slots,
      EmitSoundBelow ctx cur limit
        (emitOp (.drop (.var (Γ.rel abs))))
        (OwnsArgsResultProtected Γ (.shared :: worlds)
          (.slotA abs :: avs) rest slots)
        (OwnsArgsResultProtected Γ.bump worlds avs rest slots) := by
  intro rest slots bound hbound post code hcode
  intro fuel store env finalStore finalValue hfuel hpre hrun
  obtain ⟨⟨roots, values, hΓ, havs, hown⟩, hslots⟩ := hpre
  cases havs with
  | @cons headWorld tailWorlds headAV tailAVs value tailValues hav htail =>
    let frame : List RVal → Prop := fun oldEnv =>
      VEnvRealizes Γ oldEnv roots ∧
        AValsRealize Γ oldEnv worlds avs tailValues ∧
        SlotsRealize Γ oldEnv slots
    let remainingRoots := rootsForWorlds worlds tailValues ++ roots ++ rest
    have howned : RootOwnership store
        (⟨.shared, value⟩ :: remainingRoots) := by
      simpa [remainingRoots, rootsForWorlds] using hown
    have hnext : CodeOwnsBelow ctx cur bound
        (OwnsAfterPush frame remainingRoots) post code := by
      intro nextFuel nextStore nextEnv resultStore resultValue hnextFuel
        hpushed hcodeRun
      obtain ⟨pushed, oldEnv, rfl, ⟨hΓOld, htailOld, hslotsOld⟩,
        hownRest⟩ := hpushed
      apply hcode hnextFuel
      · exact ⟨⟨roots, tailValues, hΓOld.bump pushed,
          htailStable.realize_bump htailOld pushed, hownRest⟩,
          hslotsOld.bump pushed⟩
      · exact hcodeRun
    have hdrop : CodeOwnsBelow ctx cur bound
        (fun dropStore dropEnv =>
          frame dropEnv ∧
          resolveAtom dropEnv (.var (Γ.rel abs)) = .ok value ∧
          RootOwnership dropStore (⟨.shared, value⟩ :: remainingRoots))
        post (emitOp (.drop (.var (Γ.rel abs))) code) :=
      emit_drop_value_owned_below bound hbound post code hnext
    apply hdrop hfuel
    · exact ⟨⟨hΓ, htail, hslots⟩, hav.resolveAtom, howned⟩
    · exact hrun

/-- Semantic result of `releaseAll`: every shared argument owner is consumed,
the source-environment roots and protected slots survive, and the returned
`VEnv` records exactly the inert slots pushed by slot-backed drops. -/
def ReleaseAllSound (ctx : Ctx) (cur : FnDef) (input output : VEnv)
    (emit : Emit) (avs : List AVal) : Prop :=
  ∀ rest slots,
    EmitSound ctx cur emit
      (OwnsArgsResultProtected input
        (List.replicate avs.length .shared) avs rest slots)
      (OwnsVEnvProtected output rest slots)

/-- Semantic refinement of `releaseAll`. Its argument source values are
consumed together with their temporary roots, while the source environment
and arbitrary caller frame remain graph-related. -/
structure ReleaseAllValueSound (funRel : Sim.FunctionRel)
    (recSelfRel : RecSelfRel) (ctx : Ctx) (cur : FnDef)
    (input output : VEnv) (sourceEnv sourceValues : List IxIR0.Value)
    (emit : Emit) (avs : List AVal) : Prop where
  toReleaseAllSound : ReleaseAllSound ctx cur input output emit avs
  graphEmits : ∀ sourceRest rest slots,
    EmitSound ctx cur emit
      (GraphOwnsArgsResultProtected funRel recSelfRel input
        sourceEnv sourceValues (List.replicate avs.length .shared)
        avs sourceRest rest slots)
      (GraphOwnsVEnvProtected funRel recSelfRel output
        sourceEnv sourceRest rest slots)

def ReleaseAllSoundBelow (ctx : Ctx) (cur : FnDef) (limit : Nat)
    (input output : VEnv) (emit : Emit) (avs : List AVal) : Prop :=
  ∀ rest slots,
    EmitSoundBelow ctx cur limit emit
      (OwnsArgsResultProtected input
        (List.replicate avs.length .shared) avs rest slots)
      (OwnsVEnvProtected output rest slots)

theorem releaseAll_sound {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {avs : List AVal} (hstable : AValsStable avs) :
    ReleaseAllSound ctx cur Γ (releaseAll Γ avs).1
      (releaseAll Γ avs).2 avs := by
  induction hstable generalizing Γ with
  | nil =>
    intro rest slots
    apply EmitSound.strengthen
    intro store env hpre
    obtain ⟨⟨roots, values, hΓ, havs, hown⟩, hslots⟩ := hpre
    cases havs
    exact ⟨⟨roots, hΓ, by simpa [rootsForWorlds] using hown⟩, hslots⟩
  | @cons av avs hhead htail ih =>
    cases hhead with
    | @slot abs =>
      intro rest slots
      have hcomposed := EmitSound.comp
        (discard_slot_arg (ctx := ctx) (cur := cur) (Γ := Γ)
          (abs := abs) (worlds := List.replicate avs.length .shared)
          (avs := avs) htail rest slots)
        (ih (Γ := Γ.bump) rest slots)
      simpa [releaseAll, List.replicate_succ] using hcomposed
    | @lit literal =>
      intro rest slots
      have hcomposed := EmitSound.comp
        (discard_const_arg (ctx := ctx) (cur := cur) (Γ := Γ)
          (atom := .lit literal)
          (worlds := List.replicate avs.length .shared) (avs := avs)
          AValStable.lit rest slots)
        (ih (Γ := Γ) rest slots)
      simpa [releaseAll, List.replicate_succ, Function.comp_def] using
        hcomposed
    | erased =>
      intro rest slots
      have hcomposed := EmitSound.comp
        (discard_const_arg (ctx := ctx) (cur := cur) (Γ := Γ)
          (atom := .erased)
          (worlds := List.replicate avs.length .shared) (avs := avs)
          AValStable.erased rest slots)
        (ih (Γ := Γ) rest slots)
      simpa [releaseAll, List.replicate_succ, Function.comp_def] using
        hcomposed

/-- Stable argument descriptors and an equally sized source vector determine
the complete semantic `releaseAll` transformer. -/
theorem releaseAll_value_sound
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {sourceEnv sourceValues : List IxIR0.Value} {avs : List AVal}
    (hstable : AValsStable avs)
    (hsourceLength : sourceValues.length = avs.length) :
    ReleaseAllValueSound funRel recSelfRel ctx cur Γ
      (releaseAll Γ avs).1 sourceEnv sourceValues
      (releaseAll Γ avs).2 avs := by
  refine
    { toReleaseAllSound := releaseAll_sound hstable
      graphEmits := ?_ }
  induction hstable generalizing Γ sourceValues with
  | nil =>
    cases sourceValues with
    | nil =>
      intro sourceRest rest slots
      apply EmitSound.strengthen
      intro store env hpre
      obtain ⟨⟨roots, values, hΓ, havs, hvalueGraphs,
          hrestGraph, hown⟩, hslots⟩ := hpre
      cases havs
      cases hvalueGraphs
      exact ⟨⟨roots, hΓ, hrestGraph,
        by simpa [rootsForWorlds] using hown⟩, hslots⟩
    | cons source sources => simp at hsourceLength
  | @cons av avs hhead htail ih =>
    cases sourceValues with
    | nil => simp at hsourceLength
    | cons source sources =>
      have htailLength : sources.length = avs.length := by
        simpa using hsourceLength
      cases hhead with
      | @slot abs =>
        intro sourceRest rest slots
        have hcomposed := EmitSound.comp
          (discard_slot_arg_value
            (funRel := funRel) (recSelfRel := recSelfRel)
            (ctx := ctx) (cur := cur) (Γ := Γ)
            (sourceEnv := sourceEnv) (source := source)
            (sources := sources) (abs := abs)
            (worlds := List.replicate avs.length .shared)
            (avs := avs) htail sourceRest rest slots)
          (ih (Γ := Γ.bump) htailLength sourceRest rest slots)
        simpa [releaseAll, List.replicate_succ] using hcomposed
      | @lit literal =>
        intro sourceRest rest slots
        have hcomposed := EmitSound.comp
          (discard_const_arg_value
            (funRel := funRel) (recSelfRel := recSelfRel)
            (ctx := ctx) (cur := cur) (Γ := Γ)
            (sourceEnv := sourceEnv) (source := source)
            (sources := sources) (atom := .lit literal)
            (worlds := List.replicate avs.length .shared)
            (avs := avs) AValStable.lit sourceRest rest slots)
          (ih (Γ := Γ) htailLength sourceRest rest slots)
        simpa [releaseAll, List.replicate_succ, Function.comp_def] using
          hcomposed
      | erased =>
        intro sourceRest rest slots
        have hcomposed := EmitSound.comp
          (discard_const_arg_value
            (funRel := funRel) (recSelfRel := recSelfRel)
            (ctx := ctx) (cur := cur) (Γ := Γ)
            (sourceEnv := sourceEnv) (source := source)
            (sources := sources) (atom := .erased)
            (worlds := List.replicate avs.length .shared)
            (avs := avs) AValStable.erased sourceRest rest slots)
          (ih (Γ := Γ) htailLength sourceRest rest slots)
        simpa [releaseAll, List.replicate_succ, Function.comp_def] using
          hcomposed

theorem releaseAll_sound_below {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {Γ : VEnv} {avs : List AVal}
    (hstable : AValsStable avs) :
    ReleaseAllSoundBelow ctx cur limit Γ (releaseAll Γ avs).1
      (releaseAll Γ avs).2 avs := by
  induction hstable generalizing Γ with
  | nil =>
    intro rest slots
    apply EmitSoundBelow.strengthen
    intro store env hpre
    obtain ⟨⟨roots, values, hΓ, havs, hown⟩, hslots⟩ := hpre
    cases havs
    exact ⟨⟨roots, hΓ, by simpa [rootsForWorlds] using hown⟩, hslots⟩
  | @cons av avs hhead htail ih =>
    cases hhead with
    | @slot abs =>
      intro rest slots
      have hcomposed := EmitSoundBelow.comp
        (discard_slot_arg_below (ctx := ctx) (cur := cur)
          (limit := limit) (Γ := Γ) (abs := abs)
          (worlds := List.replicate avs.length .shared)
          (avs := avs) htail rest slots)
        (ih (Γ := Γ.bump) rest slots)
      simpa [releaseAll, List.replicate_succ] using hcomposed
    | @lit literal =>
      intro rest slots
      have hcomposed := EmitSoundBelow.comp
        (discard_const_arg_below (ctx := ctx) (cur := cur)
          (limit := limit) (Γ := Γ) (atom := .lit literal)
          (worlds := List.replicate avs.length .shared) (avs := avs)
          AValStable.lit rest slots)
        (ih (Γ := Γ) rest slots)
      simpa [releaseAll, List.replicate_succ, Function.comp_def] using
        hcomposed
    | erased =>
      intro rest slots
      have hcomposed := EmitSoundBelow.comp
        (discard_const_arg_below (ctx := ctx) (cur := cur)
          (limit := limit) (Γ := Γ) (atom := .erased)
          (worlds := List.replicate avs.length .shared) (avs := avs)
          AValStable.erased rest slots)
        (ih (Γ := Γ) rest slots)
      simpa [releaseAll, List.replicate_succ, Function.comp_def] using
        hcomposed

/-! ## Source-variable transitions -/

/-- Retain one protected borrowed field into a previously released entry.
The exact `dup` result occupies the old `VEnv.depth`, the entry becomes held,
and all original field slots plus all borrow facts survive for the remaining
field-fold iterations. -/
theorem retain_borrowed_into_entry_owned
    {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {i placeholderAbs fieldAbs remaining : Nat} {value : RVal}
    {rest : List Root} {slots : List (Nat × RVal)}
    {borrowed : List RVal}
    (hentry : Γ.entries[i]? =
      some (.slot placeholderAbs 0 .many false))
    (hslotMem : (fieldAbs, value) ∈ slots)
    (hborrowMem : value ∈ borrowed) :
    EmitSound ctx cur (emitOp (.dup (.var (Γ.rel fieldAbs))))
      (OwnsVEnvBorrowed Γ rest slots borrowed)
      (OwnsVEnvBorrowed
        ((Γ.setEntry i (.slot Γ.depth remaining .many true)).bump)
        rest slots borrowed) := by
  apply OpSound.emit
  intro fuel store env store' result hpre hrun
  obtain ⟨⟨⟨roots, hΓ, hown⟩, hslots⟩, hborrowed⟩ := hpre
  obtain ⟨hfieldBound, hfieldSlot⟩ :=
    hslots fieldAbs value hslotMem
  have hresolve :
      resolveAtom env (.var (Γ.rel fieldAbs)) = .ok value :=
    (AValRealizes.slot hfieldBound hfieldSlot).resolveAtom
  have hworld : HasWorld store .shared value :=
    hborrowed value hborrowMem
  cases fuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    obtain ⟨nextStore, heval, hownNext, hborrowedNext⟩ :=
      runOp_retain_borrowed_preserves_hasWorlds
        (ctx := ctx) (cur := cur) (fuel := fuel)
        hresolve hworld (show RootOwnership store (roots ++ rest) from hown)
        hborrowed
    have hpair : (nextStore, value) = (store', result) :=
      Except.ok.inj (heval.symm.trans hrun)
    cases hpair
    have hΓbump : VEnvRealizes Γ.bump (value :: env) roots :=
      hΓ.bump value
    have hentryBump : Γ.bump.entries[i]? =
        some (.slot placeholderAbs 0 .many false) := by
      simpa [VEnv.bump] using hentry
    have hnewBound : Γ.depth < Γ.bump.depth := by simp [VEnv.bump]
    have hnewSlot :
        (value :: env)[Γ.bump.rel Γ.depth]? = some value := by
      simp [VEnv.bump, VEnv.rel]
    obtain ⟨before, after, hroots, hentries⟩ :=
      hΓbump.entries.holdAt hentryBump hnewBound hnewSlot
    have hset : VEnvRealizes
        (Γ.bump.setEntry i (.slot Γ.depth remaining .many true))
        (value :: env)
        (before ++ ⟨.shared, value⟩ :: after) :=
      hΓbump.setEntry hentries
    have henvEq :
        Γ.bump.setEntry i (.slot Γ.depth remaining .many true) =
        ((Γ.setEntry i (.slot Γ.depth remaining .many true)).bump) := by
      cases Γ
      rfl
    rw [henvEq] at hset
    have howned : RootOwnership store'
        ((before ++ ⟨.shared, value⟩ :: after) ++ rest) := by
      rw [hroots] at hownNext
      exact hownNext.perm
        (perm_extract_root ⟨.shared, value⟩ before after rest).symm
    refine ⟨⟨⟨before ++ ⟨.shared, value⟩ :: after,
      hset, howned⟩, ?_⟩, hborrowedNext⟩
    exact (hslots.setEntry).bump value

/-- Fuel-bounded retained-field transition used by the recursive compiler
induction. The transition is call-free and preserves the same protected
slots and borrow facts as its unbounded counterpart. -/
theorem retain_borrowed_into_entry_owned_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {Γ : VEnv}
    {i placeholderAbs fieldAbs remaining : Nat} {value : RVal}
    {rest : List Root} {slots : List (Nat × RVal)}
    {borrowed : List RVal}
    (hentry : Γ.entries[i]? =
      some (.slot placeholderAbs 0 .many false))
    (hslotMem : (fieldAbs, value) ∈ slots)
    (hborrowMem : value ∈ borrowed) :
    EmitSoundBelow ctx cur limit
      (emitOp (.dup (.var (Γ.rel fieldAbs))))
      (OwnsVEnvBorrowed Γ rest slots borrowed)
      (OwnsVEnvBorrowed
        ((Γ.setEntry i (.slot Γ.depth remaining .many true)).bump)
        rest slots borrowed) := by
  apply OpSoundBelow.emit
  intro fuel store env store' result _ hpre hrun
  obtain ⟨⟨⟨roots, hΓ, hown⟩, hslots⟩, hborrowed⟩ := hpre
  obtain ⟨hfieldBound, hfieldSlot⟩ :=
    hslots fieldAbs value hslotMem
  have hresolve :
      resolveAtom env (.var (Γ.rel fieldAbs)) = .ok value :=
    (AValRealizes.slot hfieldBound hfieldSlot).resolveAtom
  have hworld : HasWorld store .shared value :=
    hborrowed value hborrowMem
  cases fuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    obtain ⟨nextStore, heval, hownNext, hborrowedNext⟩ :=
      runOp_retain_borrowed_preserves_hasWorlds
        (ctx := ctx) (cur := cur) (fuel := fuel)
        hresolve hworld (show RootOwnership store (roots ++ rest) from hown)
        hborrowed
    have hpair : (nextStore, value) = (store', result) :=
      Except.ok.inj (heval.symm.trans hrun)
    cases hpair
    have hΓbump : VEnvRealizes Γ.bump (value :: env) roots :=
      hΓ.bump value
    have hentryBump : Γ.bump.entries[i]? =
        some (.slot placeholderAbs 0 .many false) := by
      simpa [VEnv.bump] using hentry
    have hnewBound : Γ.depth < Γ.bump.depth := by simp [VEnv.bump]
    have hnewSlot :
        (value :: env)[Γ.bump.rel Γ.depth]? = some value := by
      simp [VEnv.bump, VEnv.rel]
    obtain ⟨before, after, hroots, hentries⟩ :=
      hΓbump.entries.holdAt hentryBump hnewBound hnewSlot
    have hset : VEnvRealizes
        (Γ.bump.setEntry i (.slot Γ.depth remaining .many true))
        (value :: env)
        (before ++ ⟨.shared, value⟩ :: after) :=
      hΓbump.setEntry hentries
    have henvEq :
        Γ.bump.setEntry i (.slot Γ.depth remaining .many true) =
        ((Γ.setEntry i (.slot Γ.depth remaining .many true)).bump) := by
      cases Γ
      rfl
    rw [henvEq] at hset
    have howned : RootOwnership store'
        ((before ++ ⟨.shared, value⟩ :: after) ++ rest) := by
      rw [hroots] at hownNext
      exact hownNext.perm
        (perm_extract_root ⟨.shared, value⟩ before after rest).symm
    refine ⟨⟨⟨before ++ ⟨.shared, value⟩ :: after,
      hset, howned⟩, ?_⟩, hborrowedNext⟩
    exact (hslots.setEntry).bump value

/-- Drop the recursor major after every needed constructor field has been
retained. The major is the first external root, while retained fields and
pre-major parameters are represented by `VEnv` roots. Borrow facts are no
longer promised after destroying the scrutinee. -/
theorem drop_major_owned {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {majorAbs : Nat} {major : RVal} {rest : List Root}
    {slots : List (Nat × RVal)} {borrowed : List RVal}
    (hmajor : (majorAbs, major) ∈ slots) :
    EmitSound ctx cur (emitOp (.drop (.var (Γ.rel majorAbs))))
      (OwnsVEnvBorrowed Γ (⟨.shared, major⟩ :: rest) slots borrowed)
      (OwnsVEnvProtected Γ.bump rest slots) := by
  intro post code hcode
  intro fuel store env finalStore finalValue hpre hrun
  obtain ⟨⟨⟨roots, hΓ, hown⟩, hslots⟩, _⟩ := hpre
  obtain ⟨hmajorBound, hmajorSlot⟩ :=
    hslots majorAbs major hmajor
  let frame : List RVal → Prop := fun oldEnv =>
    VEnvRealizes Γ oldEnv roots ∧ SlotsRealize Γ oldEnv slots
  have hnext : CodeOwns ctx cur
      (OwnsAfterPush frame (roots ++ rest)) post code := by
    intro nextFuel nextStore nextEnv resultStore resultValue hpushed hcodeRun
    obtain ⟨pushed, oldEnv, rfl, ⟨hrealize, hslotsOld⟩,
      hownRest⟩ := hpushed
    apply hcode
    · exact ⟨⟨roots, hrealize.bump pushed, hownRest⟩,
        hslotsOld.bump pushed⟩
    · exact hcodeRun
  apply (emit_drop_value_owned (ctx := ctx) (cur := cur)
    (frame := frame) (target := .var (Γ.rel majorAbs))
    (value := major) (rest := roots ++ rest)) post code hnext
  · refine ⟨⟨hΓ, hslots⟩,
      (AValRealizes.slot hmajorBound hmajorSlot).resolveAtom, ?_⟩
    exact hown.perm
      (perm_extract_root_front ⟨.shared, major⟩ roots rest)
  · exact hrun

/-- Fuel-bounded major release. This is the middle transition of the
generated recursor prefix. -/
theorem drop_major_owned_below {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {Γ : VEnv} {majorAbs : Nat} {major : RVal}
    {rest : List Root} {slots : List (Nat × RVal)}
    {borrowed : List RVal}
    (hmajor : (majorAbs, major) ∈ slots) :
    EmitSoundBelow ctx cur limit
      (emitOp (.drop (.var (Γ.rel majorAbs))))
      (OwnsVEnvBorrowed Γ (⟨.shared, major⟩ :: rest) slots borrowed)
      (OwnsVEnvProtected Γ.bump rest slots) := by
  intro bound hbound post code hcode
  intro fuel store env finalStore finalValue hfuel hpre hrun
  obtain ⟨⟨⟨roots, hΓ, hown⟩, hslots⟩, _⟩ := hpre
  obtain ⟨hmajorBound, hmajorSlot⟩ :=
    hslots majorAbs major hmajor
  let frame : List RVal → Prop := fun oldEnv =>
    VEnvRealizes Γ oldEnv roots ∧ SlotsRealize Γ oldEnv slots
  have hnext : CodeOwnsBelow ctx cur bound
      (OwnsAfterPush frame (roots ++ rest)) post code := by
    intro nextFuel nextStore nextEnv resultStore resultValue hnextFuel
      hpushed hcodeRun
    obtain ⟨pushed, oldEnv, rfl, ⟨hrealize, hslotsOld⟩,
      hownRest⟩ := hpushed
    apply hcode hnextFuel
    · exact ⟨⟨roots, hrealize.bump pushed, hownRest⟩,
        hslotsOld.bump pushed⟩
    · exact hcodeRun
  apply (emit_drop_value_owned_below (ctx := ctx) (cur := cur)
    (limit := limit) (frame := frame)
    (target := .var (Γ.rel majorAbs)) (value := major)
    (rest := roots ++ rest)) bound hbound post code hnext hfuel
  · refine ⟨⟨hΓ, hslots⟩,
      (AValRealizes.slot hmajorBound hmajorSlot).resolveAtom, ?_⟩
    exact hown.perm
      (perm_extract_root_front ⟨.shared, major⟩ roots rest)
  · exact hrun

/-- Common proof for releasing one held entry, abstracted over shared versus
affine destruction. The operation consumes the selected root, pushes its
inert result, and marks the compile-time entry released. -/
private theorem release_slot_owned {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {i abs : Nat} {uses : Uses} {world : Owned} {releaseEmit : Emit}
    (hworld : worldOfUses uses = world)
    (hentry : Γ.entries[i]? = some (.slot abs 0 uses true))
    (hop : ∀ {frame : List RVal → Prop} {value : RVal}
        {tailRoots : List Root},
      EmitSound ctx cur releaseEmit
        (fun store env => frame env ∧
          resolveAtom env (.var (Γ.rel abs)) = .ok value ∧
          RootOwnership store (⟨world, value⟩ :: tailRoots))
        (OwnsAfterPush frame tailRoots)) :
    ∀ rest slots,
      EmitSound ctx cur releaseEmit
        (OwnsVEnvProtected Γ rest slots)
        (OwnsVEnvProtected
          ((Γ.setEntry i (.slot abs 0 uses false)).bump) rest slots) := by
  intro rest slots post code hcode
  intro fuel store env finalStore finalValue hpre hrun
  obtain ⟨⟨roots, hΓ, hown⟩, hslots⟩ := hpre
  obtain ⟨value, before, after, hbound, hslot, hroots, hreleased⟩ :=
    hΓ.entries.releaseAt hentry
  let Γreleased := Γ.setEntry i (.slot abs 0 uses false)
  let tailRoots := before ++ after ++ rest
  let frame : List RVal → Prop := fun oldEnv =>
    VEnvRealizes Γreleased oldEnv (before ++ after) ∧
      SlotsRealize Γreleased oldEnv slots
  have hΓreleased : VEnvRealizes Γreleased env (before ++ after) :=
    hΓ.setEntry hreleased
  have howned : RootOwnership store (⟨world, value⟩ :: tailRoots) := by
    rw [hroots] at hown
    have hfront := hown.perm
      (perm_extract_root ⟨worldOfUses uses, value⟩ before after rest)
    simpa [tailRoots, hworld] using hfront
  have hnext : CodeOwns ctx cur (OwnsAfterPush frame tailRoots) post code := by
    intro nextFuel nextStore nextEnv resultStore resultValue hpushed hcodeRun
    obtain ⟨pushed, oldEnv, rfl, ⟨hrealize, hslotsOld⟩,
      hownRest⟩ := hpushed
    apply hcode
    · refine ⟨⟨before ++ after, hrealize.bump pushed, ?_⟩,
        hslotsOld.bump pushed⟩
      simpa [tailRoots, List.append_assoc] using hownRest
    · exact hcodeRun
  apply hop post code hnext
  · refine ⟨⟨hΓreleased, hslots.setEntry⟩, ?_, howned⟩
    exact (AValRealizes.slot hbound hslot).resolveAtom
  · exact hrun

/-- Bounded common proof for releasing one held entry. -/
private theorem release_slot_owned_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {Γ : VEnv}
    {i abs : Nat} {uses : Uses} {world : Owned} {releaseEmit : Emit}
    (hworld : worldOfUses uses = world)
    (hentry : Γ.entries[i]? = some (.slot abs 0 uses true))
    (hop : ∀ {frame : List RVal → Prop} {value : RVal}
        {tailRoots : List Root},
      EmitSoundBelow ctx cur limit releaseEmit
        (fun store env => frame env ∧
          resolveAtom env (.var (Γ.rel abs)) = .ok value ∧
          RootOwnership store (⟨world, value⟩ :: tailRoots))
        (OwnsAfterPush frame tailRoots)) :
    ∀ rest slots,
      EmitSoundBelow ctx cur limit releaseEmit
        (OwnsVEnvProtected Γ rest slots)
        (OwnsVEnvProtected
          ((Γ.setEntry i (.slot abs 0 uses false)).bump) rest slots) := by
  intro rest slots bound hbound post code hcode
  intro fuel store env finalStore finalValue hfuel hpre hrun
  obtain ⟨⟨roots, hΓ, hown⟩, hslots⟩ := hpre
  obtain ⟨value, before, after, hboundSlot, hslot, hroots, hreleased⟩ :=
    hΓ.entries.releaseAt hentry
  let Γreleased := Γ.setEntry i (.slot abs 0 uses false)
  let tailRoots := before ++ after ++ rest
  let frame : List RVal → Prop := fun oldEnv =>
    VEnvRealizes Γreleased oldEnv (before ++ after) ∧
      SlotsRealize Γreleased oldEnv slots
  have hΓreleased : VEnvRealizes Γreleased env (before ++ after) :=
    hΓ.setEntry hreleased
  have howned : RootOwnership store (⟨world, value⟩ :: tailRoots) := by
    rw [hroots] at hown
    have hfront := hown.perm
      (perm_extract_root ⟨worldOfUses uses, value⟩ before after rest)
    simpa [tailRoots, hworld] using hfront
  have hnext : CodeOwnsBelow ctx cur bound
      (OwnsAfterPush frame tailRoots) post code := by
    intro nextFuel nextStore nextEnv resultStore resultValue hnextFuel
      hpushed hcodeRun
    obtain ⟨pushed, oldEnv, rfl, ⟨hrealize, hslotsOld⟩,
      hownRest⟩ := hpushed
    apply hcode hnextFuel
    · refine ⟨⟨before ++ after, hrealize.bump pushed, ?_⟩,
        hslotsOld.bump pushed⟩
      simpa [tailRoots, List.append_assoc] using hownRest
    · exact hcodeRun
  apply hop bound hbound post code hnext hfuel
  · refine ⟨⟨hΓreleased, hslots.setEntry⟩, ?_, howned⟩
    exact (AValRealizes.slot hboundSlot hslot).resolveAtom
  · exact hrun

/-- Semantic common proof for one release slot. The selected environment
root is consumed, while the reverse shape inclusion returned by the evaluator
rebuilds every surviving environment and caller-frame value graph. -/
private theorem release_slot_value_sound
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {i abs : Nat} {uses : Uses} {world : Owned} {releaseOp : Op}
    (hworld : worldOfUses uses = world)
    (hentry : Γ.entries[i]? = some (.slot abs 0 uses true))
    (hop : ∀ {fuel : Nat} {store store' : Store} {env : List RVal}
        {value result : RVal} {tailRoots : List Root},
      resolveAtom env (.var (Γ.rel abs)) = .ok value →
      RootOwnership store (⟨world, value⟩ :: tailRoots) →
      runOp ctx (fuel + 1) cur store env releaseOp =
        .ok (store', result) →
      result = .erased ∧ Sim.StoreGraphRestricts store store' ∧
        RootOwnership store' tailRoots) :
    ∀ sourceEnv sourceRest rest slots,
      EmitSound ctx cur (emitOp releaseOp)
        (GraphOwnsVEnvProtected funRel recSelfRel Γ
          sourceEnv sourceRest rest slots)
        (GraphOwnsVEnvProtected funRel recSelfRel
          ((Γ.setEntry i (.slot abs 0 uses false)).bump)
          sourceEnv sourceRest rest slots) := by
  intro sourceEnv sourceRest rest slots
  apply OpSound.emit
  intro fuel store env store' result hpre hrun
  cases fuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    obtain ⟨⟨roots, hΓ, hrestGraph, hown⟩, hslots⟩ := hpre
    obtain ⟨_, value, before, after, _, hbound, hslot, _, _,
        hroots, hreleased⟩ := hΓ.entries.releaseAt hentry
    let Γreleased := Γ.setEntry i (.slot abs 0 uses false)
    let tailRoots := before ++ after ++ rest
    have hΓreleased : VEnvValueGraph funRel recSelfRel store
        Γreleased sourceEnv env (before ++ after) :=
      hΓ.setEntry hreleased
    have howned : RootOwnership store
        (⟨world, value⟩ :: tailRoots) := by
      rw [hroots] at hown
      have hfront := hown.perm
        (perm_extract_root
          ⟨worldOfUses uses, value⟩ before after rest)
      simpa [tailRoots, hworld] using hfront
    have hresolve :
        resolveAtom env (.var (Γ.rel abs)) = .ok value :=
      (AValRealizes.slot hbound hslot).resolveAtom
    obtain ⟨rfl, hrestrict, hownAfter⟩ :=
      hop hresolve howned hrun
    have hΓafter : VEnvValueGraph funRel recSelfRel store'
        Γreleased sourceEnv env (before ++ after) :=
      hΓreleased.ofRestricts hrestrict hownAfter
        (fun root hmember => by
          simpa [tailRoots] using
            List.mem_append_left rest hmember)
    have hrestAfter : Sim.RootsGraph funRel store' sourceRest rest :=
      hrestGraph.ofRestrictsIn hrestrict hownAfter
        (fun root hmember => by
          simpa [tailRoots] using
            List.mem_append_right (before ++ after) hmember)
    refine ⟨⟨before ++ after, ?_, hrestAfter, ?_⟩, ?_⟩
    · exact hΓafter.bump .erased
    · simpa [tailRoots] using hownAfter
    · exact (hslots.setEntry).bump .erased

theorem release_slot_many_owned {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {i abs : Nat}
    (hentry : Γ.entries[i]? = some (.slot abs 0 .many true)) :
    ∀ rest slots,
      EmitSound ctx cur (emitOp (.drop (.var (Γ.rel abs))))
        (OwnsVEnvProtected Γ rest slots)
        (OwnsVEnvProtected
          ((Γ.setEntry i (.slot abs 0 .many false)).bump) rest slots) := by
  apply release_slot_owned (world := .shared) rfl hentry
  exact emit_drop_value_owned

theorem release_slot_affine_owned {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {i abs : Nat}
    (hentry : Γ.entries[i]? = some (.slot abs 0 .affine true)) :
    ∀ rest slots,
      EmitSound ctx cur (emitOp (.dropU (.var (Γ.rel abs))))
        (OwnsVEnvProtected Γ rest slots)
        (OwnsVEnvProtected
          ((Γ.setEntry i (.slot abs 0 .affine false)).bump) rest slots) := by
  apply release_slot_owned (world := .unique) rfl hentry
  exact emit_dropU_value_owned

/-- Releasing a dead shared entry preserves the source graph of every other
logical entry and every caller-framed root. -/
theorem release_slot_many_value_sound
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {Γ : VEnv} {i abs : Nat}
    (hentry : Γ.entries[i]? = some (.slot abs 0 .many true)) :
    ∀ sourceEnv sourceRest rest slots,
      EmitSound ctx cur (emitOp (.drop (.var (Γ.rel abs))))
        (GraphOwnsVEnvProtected funRel recSelfRel Γ
          sourceEnv sourceRest rest slots)
        (GraphOwnsVEnvProtected funRel recSelfRel
          ((Γ.setEntry i (.slot abs 0 .many false)).bump)
          sourceEnv sourceRest rest slots) := by
  apply release_slot_value_sound (world := .shared) rfl hentry
  exact runOp_drop_value_owned_restricts

/-- Releasing a dead affine entry has the same graph-preserving interface,
using unique deep destruction underneath. -/
theorem release_slot_affine_value_sound
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {Γ : VEnv} {i abs : Nat}
    (hentry : Γ.entries[i]? = some (.slot abs 0 .affine true)) :
    ∀ sourceEnv sourceRest rest slots,
      EmitSound ctx cur (emitOp (.dropU (.var (Γ.rel abs))))
        (GraphOwnsVEnvProtected funRel recSelfRel Γ
          sourceEnv sourceRest rest slots)
        (GraphOwnsVEnvProtected funRel recSelfRel
          ((Γ.setEntry i (.slot abs 0 .affine false)).bump)
          sourceEnv sourceRest rest slots) := by
  apply release_slot_value_sound (world := .unique) rfl hentry
  exact runOp_dropU_value_owned_restricts

theorem release_slot_many_owned_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {Γ : VEnv}
    {i abs : Nat}
    (hentry : Γ.entries[i]? = some (.slot abs 0 .many true)) :
    ∀ rest slots,
      EmitSoundBelow ctx cur limit
        (emitOp (.drop (.var (Γ.rel abs))))
        (OwnsVEnvProtected Γ rest slots)
        (OwnsVEnvProtected
          ((Γ.setEntry i (.slot abs 0 .many false)).bump) rest slots) := by
  apply release_slot_owned_below (world := .shared) rfl hentry
  exact emit_drop_value_owned_below

theorem release_slot_affine_owned_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {Γ : VEnv}
    {i abs : Nat}
    (hentry : Γ.entries[i]? = some (.slot abs 0 .affine true)) :
    ∀ rest slots,
      EmitSoundBelow ctx cur limit
        (emitOp (.dropU (.var (Γ.rel abs))))
        (OwnsVEnvProtected Γ rest slots)
        (OwnsVEnvProtected
          ((Γ.setEntry i (.slot abs 0 .affine false)).bump) rest slots) := by
  apply release_slot_owned_below (world := .unique) rfl hentry
  exact emit_dropU_value_owned_below

/-- Proof-relevant successful execution plan for `releaseSlots`. Linear and
erased dead parameters have no constructor because the executable lowerer
rejects them. -/
inductive ReleasePlan : VEnv → List SlotDrop → VEnv → Emit → Prop where
  | nil {Γ : VEnv} :
      ReleasePlan Γ [] Γ (_root_.id : Emit)
  | many {Γ output : VEnv} {i abs : Nat} {drops : List SlotDrop}
      {tailEmit : Emit}
      (hentry : Γ.entries[i]? = some (.slot abs 0 .many true))
      (tail : ReleasePlan
        ((Γ.setEntry i (.slot abs 0 .many false)).bump)
        drops output tailEmit) :
      ReleasePlan Γ (⟨i, abs, .many⟩ :: drops) output
        (emitOp (.drop (.var (Γ.rel abs))) ∘ tailEmit)
  | affine {Γ output : VEnv} {i abs : Nat} {drops : List SlotDrop}
      {tailEmit : Emit}
      (hentry : Γ.entries[i]? = some (.slot abs 0 .affine true))
      (tail : ReleasePlan
        ((Γ.setEntry i (.slot abs 0 .affine false)).bump)
        drops output tailEmit) :
      ReleasePlan Γ (⟨i, abs, .affine⟩ :: drops) output
        (emitOp (.dropU (.var (Γ.rel abs))) ∘ tailEmit)

/-- Append untouched logical entries without changing runtime depth. This is
the frame needed to prove parameter releases inside lifted-function
environments that also contain capture/source entries. -/
def frameVEnvEntries (Γ : VEnv) (frame : List VEntry) : VEnv :=
  { Γ with entries := Γ.entries ++ frame }

/-- Prepend unrelated logical entries without changing runtime depth. Release
descriptor indices must be shifted by the prefix length. -/
def prependVEnvEntries (leading : List VEntry) (Γ : VEnv) : VEnv :=
  { Γ with entries := leading ++ Γ.entries }

theorem ReleasePlan.entries_length {input output : VEnv}
    {drops : List SlotDrop} {emit : Emit}
    (hplan : ReleasePlan input drops output emit) :
    output.entries.length = input.entries.length := by
  induction hplan with
  | nil => rfl
  | many hentry tail ih =>
    simpa [VEnv.setEntry, VEnv.bump] using ih
  | affine hentry tail ih =>
    simpa [VEnv.setEntry, VEnv.bump] using ih

/-- Release plans preserve an appended suffix of entries. All generated drop
indices point into the original prefix, and entry updates commute with this
frame. -/
theorem ReleasePlan.frameEntries {input output : VEnv}
    {drops : List SlotDrop} {emit : Emit}
    (hplan : ReleasePlan input drops output emit) (frame : List VEntry) :
    ReleasePlan (frameVEnvEntries input frame) drops
      (frameVEnvEntries output frame) emit := by
  induction hplan with
  | nil => exact ReleasePlan.nil
  | @many Γ output i abs drops tailEmit hentry tail ih =>
    obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hentry
    have hentryFrame : (frameVEnvEntries Γ frame).entries[i]? =
        some (.slot abs 0 .many true) := by
      simpa [frameVEnvEntries,
        List.getElem?_append_left hi] using hentry
    have hnext :
        ((frameVEnvEntries Γ frame).setEntry i
          (.slot abs 0 .many false)).bump =
        (frameVEnvEntries
          ((Γ.setEntry i (.slot abs 0 .many false)).bump) frame) := by
      cases Γ
      simp [frameVEnvEntries, VEnv.setEntry, VEnv.bump,
        List.set_append_left _ _ hi]
    apply ReleasePlan.many hentryFrame
    rw [hnext]
    simpa [frameVEnvEntries, VEnv.rel] using ih
  | @affine Γ output i abs drops tailEmit hentry tail ih =>
    obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hentry
    have hentryFrame : (frameVEnvEntries Γ frame).entries[i]? =
        some (.slot abs 0 .affine true) := by
      simpa [frameVEnvEntries,
        List.getElem?_append_left hi] using hentry
    have hnext :
        ((frameVEnvEntries Γ frame).setEntry i
          (.slot abs 0 .affine false)).bump =
        (frameVEnvEntries
          ((Γ.setEntry i (.slot abs 0 .affine false)).bump) frame) := by
      cases Γ
      simp [frameVEnvEntries, VEnv.setEntry, VEnv.bump,
        List.set_append_left _ _ hi]
    apply ReleasePlan.affine hentryFrame
    rw [hnext]
    simpa [frameVEnvEntries, VEnv.rel] using ih

/-- A leading logical-entry frame preserves a release plan after shifting
every descriptor's entry index. Absolute runtime slots and emitted relative
indices are unchanged because the frame does not alter runtime depth. -/
theorem ReleasePlan.prependEntries {input output : VEnv}
    {drops : List SlotDrop} {emit : Emit}
    (hplan : ReleasePlan input drops output emit)
    (leading : List VEntry) :
    ReleasePlan (prependVEnvEntries leading input)
      (drops.map (SlotDrop.offsetEntry leading.length))
      (prependVEnvEntries leading output) emit := by
  induction hplan with
  | nil => exact ReleasePlan.nil
  | @many Γ output i abs drops tailEmit hentry tail ih =>
    have hentryPrefix :
        (prependVEnvEntries leading Γ).entries[leading.length + i]? =
          some (.slot abs 0 .many true) := by
      rw [show (prependVEnvEntries leading Γ).entries =
          leading ++ Γ.entries by rfl]
      rw [List.getElem?_append_right (Nat.le_add_right _ _)]
      simpa using hentry
    have hnext :
        ((prependVEnvEntries leading Γ).setEntry (leading.length + i)
          (.slot abs 0 .many false)).bump =
        prependVEnvEntries leading
          ((Γ.setEntry i (.slot abs 0 .many false)).bump) := by
      cases Γ
      simp [prependVEnvEntries, VEnv.setEntry, VEnv.bump,
        List.set_append_right]
    apply ReleasePlan.many hentryPrefix
    rw [hnext]
    simpa [SlotDrop.offsetEntry] using ih
  | @affine Γ output i abs drops tailEmit hentry tail ih =>
    have hentryPrefix :
        (prependVEnvEntries leading Γ).entries[leading.length + i]? =
          some (.slot abs 0 .affine true) := by
      rw [show (prependVEnvEntries leading Γ).entries =
          leading ++ Γ.entries by rfl]
      rw [List.getElem?_append_right (Nat.le_add_right _ _)]
      simpa using hentry
    have hnext :
        ((prependVEnvEntries leading Γ).setEntry (leading.length + i)
          (.slot abs 0 .affine false)).bump =
        prependVEnvEntries leading
          ((Γ.setEntry i (.slot abs 0 .affine false)).bump) := by
      cases Γ
      simp [prependVEnvEntries, VEnv.setEntry, VEnv.bump,
        List.set_append_right]
    apply ReleasePlan.affine hentryPrefix
    rw [hnext]
    simpa [SlotDrop.offsetEntry] using ih

/-- Proof-relevant execution plan for the recursor's canonical borrowed-field
retain list. Each step activates one released field entry at the fresh slot
pushed by `dup`. -/
inductive FieldRetainPlan :
    VEnv → List RecursorFieldRetain → VEnv → Emit → Prop where
  | nil {Γ : VEnv} :
      FieldRetainPlan Γ [] Γ (_root_.id : Emit)
  | retain {Γ output : VEnv} {i placeholderAbs fieldAbs remaining : Nat}
      {retains : List RecursorFieldRetain} {tailEmit : Emit}
      (hentry : Γ.entries[i]? =
        some (.slot placeholderAbs 0 .many false))
      (tail : FieldRetainPlan
        ((Γ.setEntry i (.slot Γ.depth remaining .many true)).bump)
        retains output tailEmit) :
      FieldRetainPlan Γ
        (⟨i, fieldAbs, remaining⟩ :: retains) output
        (emitOp (.dup (.var (Γ.rel fieldAbs))) ∘ tailEmit)

/-- Later field retains address only the original field-entry block, so an
appended logical frame commutes with the whole plan. -/
theorem FieldRetainPlan.frameEntries {input output : VEnv}
    {retains : List RecursorFieldRetain} {emit : Emit}
    (hplan : FieldRetainPlan input retains output emit)
    (frame : List VEntry) :
    FieldRetainPlan (frameVEnvEntries input frame) retains
      (frameVEnvEntries output frame) emit := by
  induction hplan with
  | nil => exact FieldRetainPlan.nil
  | @retain Γ output i placeholderAbs fieldAbs remaining retains tailEmit
      hentry tail ih =>
    obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hentry
    have hentryFrame : (frameVEnvEntries Γ frame).entries[i]? =
        some (.slot placeholderAbs 0 .many false) := by
      simpa [frameVEnvEntries, List.getElem?_append_left hi] using hentry
    have hnext :
        ((frameVEnvEntries Γ frame).setEntry i
          (.slot Γ.depth remaining .many true)).bump =
        frameVEnvEntries
          ((Γ.setEntry i (.slot Γ.depth remaining .many true)).bump)
          frame := by
      cases Γ
      simp [frameVEnvEntries, VEnv.setEntry, VEnv.bump,
        List.set_append_left _ _ hi]
    apply FieldRetainPlan.retain hentryFrame
    rw [show (frameVEnvEntries Γ frame).depth = Γ.depth by rfl]
    rw [hnext]
    simpa [frameVEnvEntries, VEnv.rel] using ih

/-- A field-retain plan computes the exact pure interpreter result. -/
theorem FieldRetainPlan.run {input output : VEnv}
    {retains : List RecursorFieldRetain} {emit : Emit}
    (hplan : FieldRetainPlan input retains output emit) :
    applyRecursorFieldRetains input retains = (output, emit) := by
  induction hplan with
  | nil => rfl
  | retain hentry tail ih =>
    simp only [applyRecursorFieldRetains]
    rw [ih]

/-- The compiler-generated retain list always has a concrete plan from its
all-released field-entry block, at any ambient runtime depth. The induction
mirrors constructor order: the current field occupies the last source entry,
then the remaining fields recurse under that appended entry. -/
theorem recursorFieldRetains_plan
    (fieldAbs depth fieldCount : Nat) (rhs : IxIR0.Expr) :
    let dead : VEntry := .slot 0 0 .many false
    ∃ output emit,
      FieldRetainPlan
        ⟨List.replicate fieldCount dead, depth⟩
        (recursorFieldRetains fieldAbs rhs fieldCount)
        output emit := by
  dsimp only
  induction fieldCount generalizing fieldAbs depth with
  | zero =>
    exact ⟨⟨[], depth⟩, (_root_.id : Emit), FieldRetainPlan.nil⟩
  | succ fieldCount ih =>
    let dead : VEntry := .slot 0 0 .many false
    let uses := countUses fieldCount rhs
    have hrep : List.replicate (fieldCount + 1) dead =
        List.replicate fieldCount dead ++ [dead] := by
      symm
      simpa using (List.replicate_append_replicate
        (n := fieldCount) (m := 1) (a := dead))
    by_cases hzero : uses = 0
    · obtain ⟨tailOutput, tailEmit, htail⟩ :=
        ih (fieldAbs + 1) depth
      have hframed := htail.frameEntries [dead]
      refine ⟨frameVEnvEntries tailOutput [dead], tailEmit, ?_⟩
      rw [hrep]
      simpa [recursorFieldRetains, uses, hzero, dead,
        frameVEnvEntries] using hframed
    · obtain ⟨tailOutput, tailEmit, htail⟩ :=
        ih (fieldAbs + 1) (depth + 1)
      let held : VEntry := .slot depth uses .many true
      have hframed := htail.frameEntries [held]
      let input : VEnv :=
        ⟨List.replicate (fieldCount + 1) dead, depth⟩
      have hentry : input.entries[fieldCount]? = some dead := by
        simp [input, dead]
      have hnext :
          ((input.setEntry fieldCount held).bump) =
            frameVEnvEntries
              ⟨List.replicate fieldCount dead, depth + 1⟩ [held] := by
        simp only [input, VEnv.setEntry, VEnv.bump]
        rw [hrep]
        simp [held, dead, frameVEnvEntries, List.set_append_right]
      have htailFull : FieldRetainPlan
          ((input.setEntry fieldCount held).bump)
          (recursorFieldRetains (fieldAbs + 1) rhs fieldCount)
          (frameVEnvEntries tailOutput [held]) tailEmit := by
        rw [hnext]
        exact hframed
      have hfirst := FieldRetainPlan.retain
        (fieldAbs := fieldAbs) hentry htailFull
      refine ⟨frameVEnvEntries tailOutput [held],
        emitOp (.dup (.var (input.rel fieldAbs))) ∘ tailEmit, ?_⟩
      simpa [input, recursorFieldRetains, uses, hzero, dead, held]
        using hfirst

/-- Original borrowed field slots in constructor order. The first field is at
`fieldAbs`; each following field occupies the next older absolute position. -/
def recursorFieldSlots : Nat → List RVal → List (Nat × RVal)
  | _, [] => []
  | fieldAbs, value :: values =>
    (fieldAbs, value) :: recursorFieldSlots (fieldAbs + 1) values

private theorem List.foldl_cons_eq_reverse_append (values env : List RVal) :
    values.foldl (fun current value => value :: current) env =
      values.reverse ++ env := by
  induction values generalizing env with
  | nil => rfl
  | cons value values ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp [List.reverse_cons, List.append_assoc]

theorem Array.foldl_cons_eq_reverse_append
    (fields : Array RVal) (env : List RVal) :
    fields.foldl (fun current field => field :: current) env =
      fields.toList.reverse ++ env := by
  rw [← Array.foldl_toList]
  exact List.foldl_cons_eq_reverse_append fields.toList env

/-- Constructor fields pushed from left to right occupy consecutive absolute
slots, starting immediately outside the pre-major argument prefix. -/
theorem recursorFieldSlots_realize_list (env values : List RVal) :
    SlotsRealize ⟨[], env.length + values.length⟩
      (values.reverse ++ env)
      (recursorFieldSlots env.length values) := by
  induction values generalizing env with
  | nil => exact SlotsRealize.nil
  | cons value values ih =>
    intro abs found hmem
    simp only [recursorFieldSlots, List.mem_cons] at hmem
    rcases hmem with hpair | htail
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
      constructor
      · simp
      · simp [VEnv.rel, List.reverse_cons, List.append_assoc]
    · have hrest := ih (value :: env) abs found htail
      simpa [VEnv.rel, List.reverse_cons, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest

/-- Every static retain descriptor resolves to one protected borrowed value. -/
def FieldRetainsCovered (retains : List RecursorFieldRetain)
    (slots : List (Nat × RVal)) (borrowed : List RVal) : Prop :=
  ∀ retain ∈ retains, ∃ value,
    (retain.fieldAbs, value) ∈ slots ∧ value ∈ borrowed

theorem FieldRetainPlan.entries_length {input output : VEnv}
    {retains : List RecursorFieldRetain} {emit : Emit}
    (hplan : FieldRetainPlan input retains output emit) :
    output.entries.length = input.entries.length := by
  induction hplan with
  | nil => rfl
  | retain hentry tail ih =>
    simpa [VEnv.setEntry, VEnv.bump] using ih

/-- Semantic induction for an arbitrary field-retain plan. Each `dup`
activates its released field entry, while protected original slots and all
borrow facts remain available to the tail. -/
theorem FieldRetainPlan.sound {ctx : Ctx} {cur : FnDef}
    {input output : VEnv} {retains : List RecursorFieldRetain}
    {emit : Emit} (hplan : FieldRetainPlan input retains output emit)
    (slots : List (Nat × RVal)) (borrowed : List RVal)
    (hcovered : FieldRetainsCovered retains slots borrowed) :
    ∀ rest,
      EmitSound ctx cur emit
        (OwnsVEnvBorrowed input rest slots borrowed)
        (OwnsVEnvBorrowed output rest slots borrowed) := by
  induction hplan with
  | nil =>
    intro rest
    exact EmitSound.id
  | @retain Γ output i placeholderAbs fieldAbs remaining retains tailEmit
      hentry tail ih =>
    intro rest
    obtain ⟨value, hslot, hborrow⟩ :=
      hcovered ⟨i, fieldAbs, remaining⟩ (by simp)
    have htailCovered : FieldRetainsCovered retains slots borrowed := by
      intro retain hmem
      exact hcovered retain (by simp [hmem])
    exact EmitSound.comp
      (retain_borrowed_into_entry_owned hentry hslot hborrow)
      (ih htailCovered rest)

/-- Fuel-bounded semantic induction for a field-retain plan. -/
theorem FieldRetainPlan.soundBelow {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {input output : VEnv}
    {retains : List RecursorFieldRetain} {emit : Emit}
    (hplan : FieldRetainPlan input retains output emit)
    (slots : List (Nat × RVal)) (borrowed : List RVal)
    (hcovered : FieldRetainsCovered retains slots borrowed) :
    ∀ rest,
      EmitSoundBelow ctx cur limit emit
        (OwnsVEnvBorrowed input rest slots borrowed)
        (OwnsVEnvBorrowed output rest slots borrowed) := by
  induction hplan with
  | nil =>
    intro rest
    exact EmitSoundBelow.id
  | @retain Γ output i placeholderAbs fieldAbs remaining retains tailEmit
      hentry tail ih =>
    intro rest
    obtain ⟨value, hslot, hborrow⟩ :=
      hcovered ⟨i, fieldAbs, remaining⟩ (by simp)
    have htailCovered : FieldRetainsCovered retains slots borrowed := by
      intro retain hmem
      exact hcovered retain (by simp [hmem])
    exact EmitSoundBelow.comp
      (retain_borrowed_into_entry_owned_below hentry hslot hborrow)
      (ih htailCovered rest)

/-- The canonical retain generator is covered by constructor-order runtime
field values of the declared width. -/
theorem recursorFieldRetains_covered
    (fieldAbs fieldCount : Nat) (rhs : IxIR0.Expr) (values : List RVal)
    (hlength : values.length = fieldCount) :
    FieldRetainsCovered
      (recursorFieldRetains fieldAbs rhs fieldCount)
      (recursorFieldSlots fieldAbs values) values := by
  induction fieldCount generalizing fieldAbs values with
  | zero =>
    cases values with
    | nil =>
      intro retain hmem
      simp [recursorFieldRetains] at hmem
    | cons value values => simp at hlength
  | succ fieldCount ih =>
    cases values with
    | nil => simp at hlength
    | cons value values =>
      have htailLength : values.length = fieldCount := by
        simpa using hlength
      have htail := ih (fieldAbs + 1) values htailLength
      by_cases hzero : countUses fieldCount rhs = 0
      · intro retain hmem
        have hmemTail :
            retain ∈ recursorFieldRetains (fieldAbs + 1) rhs fieldCount := by
          simpa [recursorFieldRetains, hzero] using hmem
        obtain ⟨found, hslot, hborrow⟩ := htail retain hmemTail
        exact ⟨found, by simp [recursorFieldSlots, hslot],
          by simp [hborrow]⟩
      · intro retain hmem
        have hcases : retain =
              ⟨fieldCount, fieldAbs, countUses fieldCount rhs⟩ ∨
            retain ∈
              recursorFieldRetains (fieldAbs + 1) rhs fieldCount := by
          simpa [recursorFieldRetains, hzero] using hmem
        rcases hcases with rfl | hmemTail
        · exact ⟨value, by simp [recursorFieldSlots], by simp⟩
        · obtain ⟨found, hslot, hborrow⟩ := htail retain hmemTail
          exact ⟨found, by simp [recursorFieldSlots, hslot],
            by simp [hborrow]⟩

/-- End-to-end executable/semantic certificate for the arbitrary borrowed-
field fold used by `lowerRecursor`, before the major and parameter releases. -/
theorem recursorFieldRetains_verified {ctx : Ctx} {cur : FnDef}
    (fieldAbs depth fieldCount : Nat) (rhs : IxIR0.Expr)
    (values : List RVal) (hlength : values.length = fieldCount) :
    let dead : VEntry := .slot 0 0 .many false
    let input : VEnv := ⟨List.replicate fieldCount dead, depth⟩
    ∃ output emit,
      applyRecursorFieldRetains input
          (recursorFieldRetains fieldAbs rhs fieldCount) =
        (output, emit) ∧
      ∀ rest,
        EmitSound ctx cur emit
          (OwnsVEnvBorrowed input rest
            (recursorFieldSlots fieldAbs values) values)
          (OwnsVEnvBorrowed output rest
            (recursorFieldSlots fieldAbs values) values) := by
  dsimp only
  obtain ⟨output, emit, hplan⟩ :=
    recursorFieldRetains_plan fieldAbs depth fieldCount rhs
  have hcovered :=
    recursorFieldRetains_covered fieldAbs fieldCount rhs values hlength
  exact ⟨output, emit, hplan.run, hplan.sound _ _ hcovered⟩

/-- Sequential release plans compose, matching list append and emitter
composition. -/
theorem ReleasePlan.comp {input middle output : VEnv}
    {firstDrops secondDrops : List SlotDrop} {firstEmit secondEmit : Emit}
    (hfirst : ReleasePlan input firstDrops middle firstEmit)
    (hsecond : ReleasePlan middle secondDrops output secondEmit) :
    ReleasePlan input (firstDrops ++ secondDrops) output
      (firstEmit ∘ secondEmit) := by
  induction hfirst with
  | nil => simpa [Function.comp_def] using hsecond
  | many hentry tail ih =>
    simpa [Function.comp_def] using ReleasePlan.many hentry (ih hsecond)
  | affine hentry tail ih =>
    simpa [Function.comp_def] using ReleasePlan.affine hentry (ih hsecond)

/-- Exactly the mode-side condition under which `parameterDrops` can
succeed. Live parameters need no release restriction; a dead parameter must
be shared (`many`) or affine. -/
def ParameterDropsAdmissible : List Uses → (Nat → Nat) → Prop
  | [], _ => True
  | mode :: modes, remaining =>
    ParameterDropsAdmissible modes remaining ∧
      (remaining modes.length = 0 → mode = .many ∨ mode = .affine)

private theorem frameVEnvEntries_parameterEntries_cons
    (base depth : Nat) (mode : Uses) (modes : List Uses)
    (remaining : Nat → Nat) :
    frameVEnvEntries
        ⟨parameterEntries (base + 1) modes remaining, depth⟩
        [.slot base (remaining modes.length) mode true] =
      ⟨parameterEntries base (mode :: modes) remaining, depth⟩ := by
  simp [frameVEnvEntries, parameterEntries]

/-- Canonical parameter entries and drops generate a concrete release plan at
any ambient runtime depth whenever their dead modes are admissible. This is
the form needed after a recursor has pushed field retains and the major-drop
result before releasing its parameters. -/
theorem parameterDrops_releasePlan_atDepth (base depth : Nat)
    (modes : List Uses)
    (remaining : Nat → Nat)
    (hadmissible : ParameterDropsAdmissible modes remaining) :
    ∃ output emit,
      ReleasePlan
        ⟨parameterEntries base modes remaining, depth⟩
        (parameterDrops base modes remaining) output emit := by
  induction modes generalizing base depth with
  | nil =>
    exact ⟨⟨[], depth⟩, (_root_.id : Emit), ReleasePlan.nil⟩
  | cons mode modes ih =>
    obtain ⟨htail, hmode⟩ := hadmissible
    obtain ⟨innerOutput, innerEmit, hinner⟩ :=
      ih (base + 1) depth htail
    let outerEntry : VEntry :=
      .slot base (remaining modes.length) mode true
    let framedOutput := frameVEnvEntries innerOutput [outerEntry]
    have hinnerFull : ReleasePlan
        ⟨parameterEntries base (mode :: modes) remaining, depth⟩
        (parameterDrops (base + 1) modes remaining)
        framedOutput innerEmit := by
      have hframed := hinner.frameEntries [outerEntry]
      rw [frameVEnvEntries_parameterEntries_cons] at hframed
      simpa [framedOutput, outerEntry] using hframed
    by_cases hzero : remaining modes.length = 0
    · rcases hmode hzero with rfl | rfl
      · have hlen : innerOutput.entries.length = modes.length := by
          calc
            innerOutput.entries.length =
                (parameterEntries (base + 1) modes remaining).length :=
              hinner.entries_length
            _ = modes.length := parameterEntries_length _ _ _
        have hentry : framedOutput.entries[modes.length]? =
            some (.slot base 0 .many true) := by
          simp [framedOutput, frameVEnvEntries, outerEntry, hlen, hzero]
        let finalOutput :=
          (framedOutput.setEntry modes.length
            (.slot base 0 .many false)).bump
        have houter : ReleasePlan framedOutput
            [⟨modes.length, base, .many⟩] finalOutput
            (emitOp (.drop (.var (framedOutput.rel base))) ∘
              (_root_.id : Emit)) := by
          exact ReleasePlan.many hentry ReleasePlan.nil
        refine ⟨finalOutput, innerEmit ∘
          (emitOp (.drop (.var (framedOutput.rel base))) ∘
            (_root_.id : Emit)), ?_⟩
        simpa [parameterDrops, hzero] using hinnerFull.comp houter
      · have hlen : innerOutput.entries.length = modes.length := by
          calc
            innerOutput.entries.length =
                (parameterEntries (base + 1) modes remaining).length :=
              hinner.entries_length
            _ = modes.length := parameterEntries_length _ _ _
        have hentry : framedOutput.entries[modes.length]? =
            some (.slot base 0 .affine true) := by
          simp [framedOutput, frameVEnvEntries, outerEntry, hlen, hzero]
        let finalOutput :=
          (framedOutput.setEntry modes.length
            (.slot base 0 .affine false)).bump
        have houter : ReleasePlan framedOutput
            [⟨modes.length, base, .affine⟩] finalOutput
            (emitOp (.dropU (.var (framedOutput.rel base))) ∘
              (_root_.id : Emit)) := by
          exact ReleasePlan.affine hentry ReleasePlan.nil
        refine ⟨finalOutput, innerEmit ∘
          (emitOp (.dropU (.var (framedOutput.rel base))) ∘
            (_root_.id : Emit)), ?_⟩
        simpa [parameterDrops, hzero] using hinnerFull.comp houter
    · refine ⟨framedOutput, innerEmit, ?_⟩
      simpa [parameterDrops, hzero] using hinnerFull

/-- Declaration-entry specialization of
`parameterDrops_releasePlan_atDepth` at the canonical telescope depth. -/
theorem parameterDrops_releasePlan (base : Nat) (modes : List Uses)
    (remaining : Nat → Nat)
    (hadmissible : ParameterDropsAdmissible modes remaining) :
    ∃ output emit,
      ReleasePlan
        ⟨parameterEntries base modes remaining, base + modes.length⟩
        (parameterDrops base modes remaining) output emit :=
  parameterDrops_releasePlan_atDepth base (base + modes.length)
    modes remaining hadmissible

/-- The generated release certificate is stable under the trailing entries
used for a lambda-lifted function's capture environment. The runtime depth is
already accounted for by `base`; framing adds only proof-side entries. -/
theorem parameterDrops_releasePlan_framed (base : Nat) (modes : List Uses)
    (remaining : Nat → Nat) (frame : List VEntry)
    (hadmissible : ParameterDropsAdmissible modes remaining) :
    ∃ output emit,
      ReleasePlan
        ⟨parameterEntries base modes remaining ++ frame,
          base + modes.length⟩
        (parameterDrops base modes remaining) output emit := by
  obtain ⟨output, emit, hplan⟩ :=
    parameterDrops_releasePlan base modes remaining hadmissible
  exact ⟨frameVEnvEntries output frame, emit,
    by simpa [frameVEnvEntries] using hplan.frameEntries frame⟩

/-- Generated parameter releases remain valid when the parameter telescope
sits between unrelated leading and trailing entries. Leading entries shift
only `SlotDrop.entry`; trailing entries require no descriptor change. -/
theorem parameterDrops_releasePlan_between
    (base depth : Nat) (modes : List Uses) (remaining : Nat → Nat)
    (leading trailing : List VEntry)
    (hadmissible : ParameterDropsAdmissible modes remaining) :
    ∃ output emit,
      ReleasePlan
        ⟨leading ++ parameterEntries base modes remaining ++ trailing,
          depth⟩
        ((parameterDrops base modes remaining).map
          (SlotDrop.offsetEntry leading.length))
        output emit := by
  obtain ⟨output, emit, hplan⟩ :=
    parameterDrops_releasePlan_atDepth base depth modes remaining hadmissible
  have hframed := hplan.frameEntries trailing
  have hbetween := hframed.prependEntries leading
  exact ⟨prependVEnvEntries leading (frameVEnvEntries output trailing),
    emit, by
      simpa [prependVEnvEntries, frameVEnvEntries, List.append_assoc]
        using hbetween⟩

@[simp] theorem parameterDropsAdmissible_replicate_many
    (count : Nat) (remaining : Nat → Nat) :
    ParameterDropsAdmissible (List.replicate count .many) remaining := by
  induction count with
  | zero => simp [ParameterDropsAdmissible]
  | succ count ih =>
    simp [List.replicate_succ, ParameterDropsAdmissible, ih]

/-- The exact arbitrary pre-major release shape used by `lowerRecursor`:
field entries lead, the canonical all-shared parameter telescope occupies the
middle, and `recSelf` trails. -/
theorem recursorParameterDrops_releasePlan
    (numArgs nf depth : Nat) (rhs : IxIR0.Expr)
    (fieldEntries : List VEntry) (hfields : fieldEntries.length = nf) :
    ∃ output emit,
      ReleasePlan
        ⟨fieldEntries ++
            parameterEntries 0 (List.replicate numArgs .many)
              (fun i => countUses (nf + i) rhs) ++
            [.recSelf (numArgs + 1)],
          depth⟩
        ((parameterDrops 0 (List.replicate numArgs .many)
            (fun i => countUses (nf + i) rhs)).map
          (SlotDrop.offsetEntry nf))
        output emit := by
  have hplan := parameterDrops_releasePlan_between
    0 depth (List.replicate numArgs .many)
    (fun i => countUses (nf + i) rhs)
    fieldEntries [.recSelf (numArgs + 1)]
    (parameterDropsAdmissible_replicate_many numArgs _)
  simpa [hfields] using hplan

/-- A release plan computes the exact successful `releaseSlots` result and
does not mutate the lowering monad state. -/
theorem ReleasePlan.run {input output : VEnv} {drops : List SlotDrop}
    {emit : Emit} (hplan : ReleasePlan input drops output emit)
    (state : LowSt) :
    (releaseSlots input drops).run state = .ok (output, emit) state := by
  induction hplan with
  | nil => simp [releaseSlots]
  | many hentry tail ih =>
    simp only [releaseSlots]
    rw [estateBindRun]
    rw [estatePureRun]
    simp only
    rw [estateBindRun, ih]
    rfl
  | affine hentry tail ih =>
    simp only [releaseSlots]
    rw [estateBindRun]
    rw [estatePureRun]
    simp only
    rw [estateBindRun, ih]
    rfl

/-- Semantic half of a release plan: every dead parameter root is consumed,
all unrelated roots/protected slots survive, and the returned `VEnv` exactly
tracks the pushed inert results. -/
def ReleaseSlotsSound (ctx : Ctx) (cur : FnDef)
    (input output : VEnv) (emit : Emit) : Prop :=
  ∀ rest slots,
    EmitSound ctx cur emit
      (OwnsVEnvProtected input rest slots)
      (OwnsVEnvProtected output rest slots)

/-- Semantic refinement of a successful release sequence. The logical source
environment is unchanged even though its dead target entries become released;
all still-held values and every caller-framed root retain their `ValueGraph`.
-/
structure ReleaseSlotsValueSound (funRel : Sim.FunctionRel)
    (recSelfRel : RecSelfRel) (ctx : Ctx) (cur : FnDef)
    (input output : VEnv) (sourceEnv : List IxIR0.Value)
    (emit : Emit) : Prop where
  toReleaseSlotsSound : ReleaseSlotsSound ctx cur input output emit
  graphEmits : ∀ sourceRest rest slots,
    EmitSound ctx cur emit
      (GraphOwnsVEnvProtected funRel recSelfRel input
        sourceEnv sourceRest rest slots)
      (GraphOwnsVEnvProtected funRel recSelfRel output
        sourceEnv sourceRest rest slots)

/-- Fuel-bounded semantic result of `releaseSlots`. -/
def ReleaseSlotsSoundBelow (ctx : Ctx) (cur : FnDef) (limit : Nat)
    (input output : VEnv) (emit : Emit) : Prop :=
  ∀ rest slots,
    EmitSoundBelow ctx cur limit emit
      (OwnsVEnvProtected input rest slots)
      (OwnsVEnvProtected output rest slots)

theorem ReleasePlan.sound {ctx : Ctx} {cur : FnDef}
    {input output : VEnv} {drops : List SlotDrop} {emit : Emit}
    (hplan : ReleasePlan input drops output emit) :
    ReleaseSlotsSound ctx cur input output emit := by
  induction hplan with
  | nil =>
    intro rest slots
    exact EmitSound.id
  | many hentry tail ih =>
    intro rest slots
    exact EmitSound.comp (release_slot_many_owned hentry rest slots)
      (ih rest slots)
  | affine hentry tail ih =>
    intro rest slots
    exact EmitSound.comp (release_slot_affine_owned hentry rest slots)
      (ih rest slots)

/-- Every proof-relevant release plan preserves the complete semantic graph
of its unchanged source environment and of the arbitrary caller frame. -/
theorem ReleasePlan.valueSound {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {ctx : Ctx} {cur : FnDef}
    {input output : VEnv} {drops : List SlotDrop} {emit : Emit}
    (hplan : ReleasePlan input drops output emit)
    (sourceEnv : List IxIR0.Value) :
    ReleaseSlotsValueSound funRel recSelfRel ctx cur
      input output sourceEnv emit := by
  refine { toReleaseSlotsSound := hplan.sound, graphEmits := ?_ }
  intro sourceRest rest slots
  induction hplan with
  | nil => exact EmitSound.id
  | many hentry tail ih =>
    exact EmitSound.comp
      (release_slot_many_value_sound hentry
        sourceEnv sourceRest rest slots)
      ih
  | affine hentry tail ih =>
    exact EmitSound.comp
      (release_slot_affine_value_sound hentry
        sourceEnv sourceRest rest slots)
      ih

/-- Fuel-bounded semantic half of a release plan. -/
theorem ReleasePlan.soundBelow {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {input output : VEnv} {drops : List SlotDrop}
    {emit : Emit} (hplan : ReleasePlan input drops output emit) :
    ReleaseSlotsSoundBelow ctx cur limit input output emit := by
  induction hplan with
  | nil =>
    intro rest slots
    exact EmitSoundBelow.id
  | many hentry tail ih =>
    intro rest slots
    exact EmitSoundBelow.comp
      (release_slot_many_owned_below hentry rest slots)
      (ih rest slots)
  | affine hentry tail ih =>
    intro rest slots
    exact EmitSoundBelow.comp
      (release_slot_affine_owned_below hentry rest slots)
      (ih rest slots)

/-- The canonical declaration-entry releases execute successfully and carry
their ownership transformer without any caller-supplied `ReleasePlan`. -/
theorem parameterDrops_verified {ctx : Ctx} {cur : FnDef}
    (base : Nat) (modes : List Uses) (remaining : Nat → Nat)
    (state : LowSt)
    (hadmissible : ParameterDropsAdmissible modes remaining) :
    ∃ output emit,
      (releaseSlots
        ⟨parameterEntries base modes remaining, base + modes.length⟩
        (parameterDrops base modes remaining)).run state =
          .ok (output, emit) state ∧
      ReleaseSlotsSound ctx cur
        ⟨parameterEntries base modes remaining, base + modes.length⟩
        output emit := by
  obtain ⟨output, emit, hplan⟩ :=
    parameterDrops_releasePlan base modes remaining hadmissible
  exact ⟨output, emit, hplan.run state, hplan.sound⟩

/-- Executable/sound generated releases also cover the trailing entry frame
of a lifted local function. -/
theorem parameterDrops_framed_verified {ctx : Ctx} {cur : FnDef}
    (base : Nat) (modes : List Uses) (remaining : Nat → Nat)
    (frame : List VEntry) (state : LowSt)
    (hadmissible : ParameterDropsAdmissible modes remaining) :
    ∃ output emit,
      (releaseSlots
        ⟨parameterEntries base modes remaining ++ frame,
          base + modes.length⟩
        (parameterDrops base modes remaining)).run state =
          .ok (output, emit) state ∧
      ReleaseSlotsSound ctx cur
        ⟨parameterEntries base modes remaining ++ frame,
          base + modes.length⟩
        output emit := by
  obtain ⟨output, emit, hplan⟩ :=
    parameterDrops_releasePlan_framed base modes remaining frame hadmissible
  exact ⟨output, emit, hplan.run state, hplan.sound⟩

/-- Arbitrary pre-major cleanup in the refactored recursor executes through
the real `releaseSlots` definition and preserves the exact ownership state.
The only structural premise is that the preceding field-entry block has the
constructor's declared width. -/
theorem recursorParameterDrops_verified {ctx : Ctx} {cur : FnDef}
    (numArgs nf depth : Nat) (rhs : IxIR0.Expr)
    (fieldEntries : List VEntry) (hfields : fieldEntries.length = nf)
    (state : LowSt) :
    ∃ output emit,
      (releaseSlots
        ⟨fieldEntries ++
            parameterEntries 0 (List.replicate numArgs .many)
              (fun i => countUses (nf + i) rhs) ++
            [.recSelf (numArgs + 1)],
          depth⟩
        ((parameterDrops 0 (List.replicate numArgs .many)
            (fun i => countUses (nf + i) rhs)).map
          (SlotDrop.offsetEntry nf))).run state =
          .ok (output, emit) state ∧
      ReleaseSlotsSound ctx cur
        ⟨fieldEntries ++
            parameterEntries 0 (List.replicate numArgs .many)
              (fun i => countUses (nf + i) rhs) ++
            [.recSelf (numArgs + 1)],
          depth⟩
        output emit := by
  obtain ⟨output, emit, hplan⟩ :=
    recursorParameterDrops_releasePlan numArgs nf depth rhs
      fieldEntries hfields
  exact ⟨output, emit, hplan.run state, hplan.sound⟩

/-- Prefix a lowered expression proof with a verified dead-parameter release
plan. -/
theorem LowerResultSound.afterRelease {ctx : Ctx} {cur : FnDef}
    {input middle output : VEnv} {releaseEmit emit : Emit}
    {world : Owned} {av : AVal}
    (hbody : LowerResultSound ctx cur middle output world emit av)
    (hrelease : ReleaseSlotsSound ctx cur input middle releaseEmit) :
    LowerResultSound ctx cur input output world (releaseEmit ∘ emit) av := by
  refine ⟨hbody.stable, ?_⟩
  intro rest slots
  exact EmitSound.comp (hrelease rest slots) (hbody.emits rest slots)

/-- Semantic release-prefix composition. Because release plans leave the
logical source environment intact, their graph transformer feeds directly
into the companion judgment for the following expression. -/
theorem LowerResultValueSound.afterRelease
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {input middle output : VEnv}
    {sourceInput sourceOutput : List IxIR0.Value}
    {sourceValue : IxIR0.Value} {releaseEmit emit : Emit}
    {world : Owned} {av : AVal}
    (hbody : LowerResultValueSound funRel recSelfRel ctx cur
      middle output sourceInput sourceOutput sourceValue world emit av)
    (hrelease : ReleaseSlotsValueSound funRel recSelfRel ctx cur
      input middle sourceInput releaseEmit) :
    LowerResultValueSound funRel recSelfRel ctx cur input output
      sourceInput sourceOutput sourceValue world
      (releaseEmit ∘ emit) av := by
  refine
    { toLowerResultSound := hbody.toLowerResultSound.afterRelease
        hrelease.toReleaseSlotsSound
      graphEmits := ?_ }
  intro sourceRest rest slots
  exact EmitSound.comp (hrelease.graphEmits sourceRest rest slots)
    (hbody.graphEmits sourceRest rest slots)

/-- Fuel-bounded release-prefix composition. -/
theorem LowerResultSoundBelow.afterRelease {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {input middle output : VEnv}
    {releaseEmit emit : Emit} {world : Owned} {av : AVal}
    (hbody : LowerResultSoundBelow ctx cur limit middle output world emit av)
    (hrelease : ReleaseSlotsSoundBelow ctx cur limit
      input middle releaseEmit) :
    LowerResultSoundBelow ctx cur limit input output world
      (releaseEmit ∘ emit) av := by
  refine ⟨hbody.stable, ?_⟩
  intro rest slots
  exact EmitSoundBelow.comp (hrelease rest slots) (hbody.emits rest slots)

/-- Generic executable/proof rule for `lowerFnBody`: first execute a
`ReleasePlan`, then reuse an already verified `lowerE` result, and finally
close with the exact `ret` emitted by the lowerer. -/
theorem lowerFnBody_verified {ctx : Ctx} {cur : FnDef}
    (src : IxIR0.Env) (fuel : Nat)
    (input middle output : VEnv) (drops : List SlotDrop)
    (world : Owned) (body : IxIR0.Expr)
    (releaseEmit emit : Emit) (av : AVal)
    (state finalState : LowSt)
    (hplan : ReleasePlan input drops middle releaseEmit)
    (hbodyRun : (lowerE src fuel middle world body).run state =
      .ok (output, emit, av) finalState)
    (hbody : LowerResultSound ctx cur middle output world emit av) :
    (lowerFnBody src (Nat.succ fuel) input drops world body).run state =
        .ok ((releaseEmit ∘ emit) (.ret (av.toAtom output))) finalState ∧
      LowerResultSound ctx cur input output world (releaseEmit ∘ emit) av := by
  constructor
  · simp only [lowerFnBody]
    rw [estateBindRun, hplan.run state]
    simp only
    rw [estateBindRun, hbodyRun]
    rfl
  · exact hbody.afterRelease hplan.sound

/-- A final variable occurrence moves its existing owner from an arbitrary
held `VEnv` entry to the distinguished expression-result root. This one rule
covers shared, affine, and linear moves; no target operation is emitted. -/
theorem lower_var_move_sound {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {i abs : Nat} {uses : Uses}
    (hentry : Γ.entries[i]? = some (.slot abs 1 uses true)) :
    LowerResultSound ctx cur Γ
      (Γ.setEntry i (.slot abs 0 uses false)) (worldOfUses uses)
      (_root_.id : Emit) (.slotA abs) := by
  refine ⟨.slot, ?_⟩
  intro rest slots
  apply EmitSound.strengthen
  intro store env hpre
  obtain ⟨⟨roots, hΓ, hown⟩, hslots⟩ := hpre
  obtain ⟨value, before, after, hbound, hslot, hroots, hout⟩ :=
    hΓ.entries.releaseAt hentry
  refine ⟨⟨before ++ after, value, hΓ.setEntry hout, ?_, ?_⟩,
    hslots.setEntry⟩
  · apply AValRealizes.slot
    · simpa [VEnv.setEntry] using hbound
    · simpa [VEnv.setEntry, VEnv.rel] using hslot
  · rw [hroots] at hown
    exact hown.perm
      (perm_extract_root ⟨worldOfUses uses, value⟩ before after rest)

/-- Semantic final-use variable rule. The source evaluator lookup and the
held target slot identify the same value through `ValueGraph`, while the
existing ownership theorem remains the parent refinement. -/
theorem lower_var_move_value_sound {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value} {sourceValue : IxIR0.Value}
    {i abs : Nat} {uses : Uses}
    (hsource : sourceEnv[i]? = some sourceValue)
    (hentry : Γ.entries[i]? = some (.slot abs 1 uses true)) :
    LowerResultValueSound funRel recSelfRel ctx cur Γ
      (Γ.setEntry i (.slot abs 0 uses false))
      sourceEnv sourceEnv sourceValue (worldOfUses uses)
      (_root_.id : Emit) (.slotA abs) := by
  refine
    { toLowerResultSound := lower_var_move_sound hentry
      graphEmits := ?_ }
  intro sourceRest rest slots
  apply EmitSound.strengthen
  intro store env hpre
  obtain ⟨⟨roots, hΓ, hrestGraph, hown⟩, hslots⟩ := hpre
  obtain ⟨foundSource, value, before, after, hfoundSource, hbound,
      hslot, _, hvalue, hroots, hout⟩ :=
    hΓ.entries.releaseAt hentry
  have hsourceEq : foundSource = sourceValue :=
    Option.some.inj (hfoundSource.symm.trans hsource)
  subst foundSource
  refine ⟨⟨before ++ after, value, hΓ.setEntry hout, ?_, hvalue,
    hrestGraph, ?_⟩, hslots.setEntry⟩
  · apply AValRealizes.slot
    · simpa [VEnv.setEntry] using hbound
    · simpa [VEnv.setEntry, VEnv.rel] using hslot
  · rw [hroots] at hown
    exact hown.perm
      (perm_extract_root ⟨worldOfUses uses, value⟩ before after rest)

/-- Fuel-bounded move of a held entry. The compiler-side remaining counter is
irrelevant to the ownership transfer; local-lambda capture uses this generic
form to discharge several syntactic occurrences at once. -/
theorem lower_held_move_sound_below {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {Γ : VEnv} {i abs remaining : Nat} {uses : Uses}
    (hentry : Γ.entries[i]? = some (.slot abs remaining uses true)) :
    LowerResultSoundBelow ctx cur limit Γ
      (Γ.setEntry i (.slot abs 0 uses false)) (worldOfUses uses)
      (_root_.id : Emit) (.slotA abs) := by
  refine ⟨.slot, ?_⟩
  intro rest slots
  apply EmitSoundBelow.strengthen
  intro store env hpre
  obtain ⟨⟨roots, hΓ, hown⟩, hslots⟩ := hpre
  obtain ⟨value, before, after, hbound, hslot, hroots, hout⟩ :=
    hΓ.entries.releaseAt hentry
  refine ⟨⟨before ++ after, value, hΓ.setEntry hout, ?_, ?_⟩,
    hslots.setEntry⟩
  · apply AValRealizes.slot
    · simpa [VEnv.setEntry] using hbound
    · simpa [VEnv.setEntry, VEnv.rel] using hslot
  · rw [hroots] at hown
    exact hown.perm
      (perm_extract_root ⟨worldOfUses uses, value⟩ before after rest)

/-- Unbounded ownership interface for moving an arbitrary held entry. -/
theorem lower_held_move_sound {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {i abs remaining : Nat} {uses : Uses}
    (hentry : Γ.entries[i]? = some (.slot abs remaining uses true)) :
    LowerResultSound ctx cur Γ
      (Γ.setEntry i (.slot abs 0 uses false)) (worldOfUses uses)
      (_root_.id : Emit) (.slotA abs) := by
  apply LowerResultSound.of_below
  intro limit
  exact lower_held_move_sound_below (limit := limit) hentry

/-- Semantic counterpart of an arbitrary held-entry move. This is the
capture case in which all remaining source occurrences move into the pap. -/
theorem lower_held_move_value_sound {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value} {sourceValue : IxIR0.Value}
    {i abs remaining : Nat} {uses : Uses}
    (hsource : sourceEnv[i]? = some sourceValue)
    (hentry : Γ.entries[i]? = some (.slot abs remaining uses true)) :
    LowerResultValueSound funRel recSelfRel ctx cur Γ
      (Γ.setEntry i (.slot abs 0 uses false))
      sourceEnv sourceEnv sourceValue (worldOfUses uses)
      (_root_.id : Emit) (.slotA abs) := by
  refine
    { toLowerResultSound := lower_held_move_sound hentry
      graphEmits := ?_ }
  intro sourceRest rest slots
  apply EmitSound.strengthen
  intro store env hpre
  obtain ⟨⟨roots, hΓ, hrestGraph, hown⟩, hslots⟩ := hpre
  obtain ⟨foundSource, value, before, after, hfoundSource, hbound,
      hslot, _, hvalue, hroots, hout⟩ :=
    hΓ.entries.releaseAt hentry
  have hsourceEq : foundSource = sourceValue :=
    Option.some.inj (hfoundSource.symm.trans hsource)
  subst foundSource
  refine ⟨⟨before ++ after, value, hΓ.setEntry hout, ?_, hvalue,
    hrestGraph, ?_⟩, hslots.setEntry⟩
  · apply AValRealizes.slot
    · simpa [VEnv.setEntry] using hbound
    · simpa [VEnv.setEntry, VEnv.rel] using hslot
  · rw [hroots] at hown
    exact hown.perm
      (perm_extract_root ⟨worldOfUses uses, value⟩ before after rest)

/-- Ordinary final variable use specializes the generic held-entry move to
remaining count one. -/
theorem lower_var_move_sound_below {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {Γ : VEnv} {i abs : Nat} {uses : Uses}
    (hentry : Γ.entries[i]? = some (.slot abs 1 uses true)) :
    LowerResultSoundBelow ctx cur limit Γ
      (Γ.setEntry i (.slot abs 0 uses false)) (worldOfUses uses)
      (_root_.id : Emit) (.slotA abs) :=
  lower_held_move_sound_below hentry

/-- A final shared variable occurrence in borrowing position moves its owner
out of the environment and records that the projection caller must release
that owner after fetching the field. -/
theorem lower_var_shared_move_borrow_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {Γ : VEnv}
    {i abs : Nat} {uses : Uses}
    (hworld : worldOfUses uses = .shared)
    (hentry : Γ.entries[i]? = some (.slot abs 1 uses true)) :
    LowerBorrowSoundBelow ctx cur limit Γ
      (Γ.setEntry i (.slot abs 0 uses false)) (_root_.id : Emit)
      (.slotA abs) true := by
  have hmove := lower_var_move_sound_below
    (ctx := ctx) (cur := cur) (limit := limit) hentry
  have hshared : LowerResultSoundBelow ctx cur limit Γ
      (Γ.setEntry i (.slot abs 0 uses false)) .shared
      (_root_.id : Emit) (.slotA abs) := by
    simpa [hworld] using hmove
  exact hshared.asBorrowSlot

/-- Unbounded ownership interface for a final shared variable borrow. -/
theorem lower_var_shared_move_borrow_sound
    {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {i abs : Nat} {uses : Uses}
    (hworld : worldOfUses uses = .shared)
    (hentry : Γ.entries[i]? = some (.slot abs 1 uses true)) :
    LowerBorrowSound ctx cur Γ
      (Γ.setEntry i (.slot abs 0 uses false)) (_root_.id : Emit)
      (.slotA abs) true := by
  have hmove := lower_var_move_sound
    (ctx := ctx) (cur := cur) hentry
  have hshared : LowerResultSound ctx cur Γ
      (Γ.setEntry i (.slot abs 0 uses false)) .shared
      (_root_.id : Emit) (.slotA abs) := by
    simpa [hworld] using hmove
  exact hshared.asBorrowSlot

/-- Semantic final shared-variable borrow. The moved result graph becomes the
pending borrow owner consumed by the projection caller. -/
theorem lower_var_shared_move_borrow_value_sound
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value} {sourceValue : IxIR0.Value}
    {i abs : Nat} {uses : Uses}
    (hsource : sourceEnv[i]? = some sourceValue)
    (hworld : worldOfUses uses = .shared)
    (hentry : Γ.entries[i]? = some (.slot abs 1 uses true)) :
    LowerBorrowValueSound funRel recSelfRel ctx cur Γ
      (Γ.setEntry i (.slot abs 0 uses false))
      sourceEnv sourceEnv sourceValue (_root_.id : Emit)
      (.slotA abs) true := by
  have hmove := lower_var_move_value_sound
    (funRel := funRel) (recSelfRel := recSelfRel)
    (ctx := ctx) (cur := cur) hsource hentry
  have hshared : LowerResultValueSound funRel recSelfRel ctx cur Γ
      (Γ.setEntry i (.slot abs 0 uses false))
      sourceEnv sourceEnv sourceValue .shared
      (_root_.id : Emit) (.slotA abs) := by
    simpa [hworld] using hmove
  exact hshared.asBorrowSlot

/-- A repeated shared variable borrow decrements its remaining-use counter
without duplicating the owner. The owner remains in the output `VEnv`, while
the returned descriptor carries only a shared borrow. -/
theorem lower_var_shared_borrow_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {Γ : VEnv}
    {i abs remaining : Nat} {uses : Uses}
    (hworld : worldOfUses uses = .shared)
    (hentry : Γ.entries[i]? =
      some (.slot abs (Nat.succ (Nat.succ remaining)) uses true)) :
    let Γ' := Γ.setEntry i (.slot abs (Nat.succ remaining) uses true)
    LowerBorrowSoundBelow ctx cur limit Γ Γ' (_root_.id : Emit)
      (.slotA abs) false := by
  dsimp only
  refine ⟨.slot, ?_⟩
  intro rest slots
  apply EmitSoundBelow.strengthen
  intro store env hpre
  obtain ⟨⟨roots, hΓ, hown⟩, hslots⟩ := hpre
  obtain ⟨value, hbound, hslot, hmem, hupdated⟩ :=
    hΓ.entries.updateHeldAt (Nat.succ remaining) hentry
  let Γ' := Γ.setEntry i (.slot abs (Nat.succ remaining) uses true)
  have hΓ' : VEnvRealizes Γ' env roots := hΓ.setEntry hupdated
  have hav : AValRealizes Γ' env (.slotA abs) value := by
    apply AValRealizes.slot
    · simpa [Γ', VEnv.setEntry] using hbound
    · simpa [Γ', VEnv.setEntry, VEnv.rel] using hslot
  have hvalueWorld : HasWorld store .shared value := by
    apply hown.roots_world ⟨.shared, value⟩
    exact List.mem_append_left rest (by simpa [hworld] using hmem)
  refine ⟨⟨roots, value, hΓ', hav, hvalueWorld, ?_⟩,
    hslots.setEntry⟩
  simpa [borrowResultRoots] using hown

/-- Unbounded ownership interface for a repeated shared variable borrow. -/
theorem lower_var_shared_borrow_sound
    {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {i abs remaining : Nat} {uses : Uses}
    (hworld : worldOfUses uses = .shared)
    (hentry : Γ.entries[i]? =
      some (.slot abs (Nat.succ (Nat.succ remaining)) uses true)) :
    let Γ' := Γ.setEntry i (.slot abs (Nat.succ remaining) uses true)
    LowerBorrowSound ctx cur Γ Γ' (_root_.id : Emit)
      (.slotA abs) false := by
  apply LowerBorrowSound.of_below
  intro limit
  exact lower_var_shared_borrow_sound_below
    (limit := limit) hworld hentry

/-- Semantic repeated shared-variable borrow. Updating the static use count
leaves the runtime owner in the environment, and the returned descriptor
reuses its existing source graph without an RC operation. -/
theorem lower_var_shared_borrow_value_sound
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value} {sourceValue : IxIR0.Value}
    {i abs remaining : Nat} {uses : Uses}
    (hsource : sourceEnv[i]? = some sourceValue)
    (hworld : worldOfUses uses = .shared)
    (hentry : Γ.entries[i]? =
      some (.slot abs (Nat.succ (Nat.succ remaining)) uses true)) :
    let Γ' := Γ.setEntry i (.slot abs (Nat.succ remaining) uses true)
    LowerBorrowValueSound funRel recSelfRel ctx cur Γ Γ'
      sourceEnv sourceEnv sourceValue (_root_.id : Emit)
      (.slotA abs) false := by
  dsimp only
  refine
    { toLowerBorrowSound :=
        lower_var_shared_borrow_sound hworld hentry
      graphEmits := ?_ }
  intro sourceRest rest slots
  apply EmitSound.strengthen
  intro store env hpre
  obtain ⟨⟨roots, hΓ, hrestGraph, hown⟩, hslots⟩ := hpre
  obtain ⟨foundSource, value, hfoundSource, hbound, hslot,
      hvalueWorld, hvalueGraph, _, hupdated⟩ :=
    hΓ.entries.updateHeldAt (Nat.succ remaining) hentry
  have hsourceEq : foundSource = sourceValue :=
    Option.some.inj (hfoundSource.symm.trans hsource)
  subst foundSource
  let Γ' := Γ.setEntry i
    (.slot abs (Nat.succ remaining) uses true)
  have hΓ' : VEnvValueGraph funRel recSelfRel store Γ'
      sourceEnv env roots := hΓ.setEntry hupdated
  have hav : AValRealizes Γ' env (.slotA abs) value := by
    apply AValRealizes.slot
    · simpa [Γ', VEnv.setEntry] using hbound
    · simpa [Γ', VEnv.setEntry, VEnv.rel] using hslot
  have hshared : HasWorld store .shared value := by
    simpa [hworld] using hvalueWorld
  refine ⟨roots, value, hΓ', hav, hshared, hvalueGraph,
    hrestGraph, ?_, hslots.setEntry⟩
  simpa [borrowResultRoots] using hown

/-- A non-final `many` occurrence retains the selected shared owner, pushes
the duplicate into a fresh absolute slot, and leaves the original entry held
with one fewer remaining source use. -/
theorem lower_var_many_dup_sound {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {i abs remaining : Nat}
    (hentry : Γ.entries[i]? =
      some (.slot abs (Nat.succ (Nat.succ remaining)) .many true)) :
    let Γ' := Γ.setEntry i (.slot abs (Nat.succ remaining) .many true)
    LowerResultSound ctx cur Γ Γ'.bump .shared
      (emitOp (.dup (.var (Γ'.rel abs)))) (.slotA Γ'.depth) := by
  dsimp only
  refine ⟨.slot, ?_⟩
  intro rest slots
  apply OpSound.emit
  intro fuel store env store' result hpre hrun
  obtain ⟨⟨roots, hΓ, hown⟩, hslots⟩ := hpre
  obtain ⟨value, hbound, hslot, hmem, hupdated⟩ :=
    hΓ.entries.updateHeldAt (Nat.succ remaining) hentry
  let Γ' := Γ.setEntry i (.slot abs (Nat.succ remaining) .many true)
  have hΓ' : VEnvRealizes Γ' env roots := hΓ.setEntry hupdated
  have hav : AValRealizes Γ' env (.slotA abs) value := by
    apply AValRealizes.slot
    · simpa [Γ', VEnv.setEntry] using hbound
    · simpa [Γ', VEnv.setEntry, VEnv.rel] using hslot
  have hworld : HasWorld store .shared value := by
    have hroot := hown.roots_world ⟨Owned.shared, value⟩
      (List.mem_append_left _ (by simpa [worldOfUses] using hmem))
    exact hroot
  cases fuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    obtain ⟨middle, heval, hmiddle⟩ :=
      runOp_retain_borrowed (ctx := ctx) (cur := cur) (fuel := fuel)
        hav.resolveAtom hworld hown
    have hpair : (middle, value) = (store', result) :=
      Except.ok.inj (heval.symm.trans hrun)
    cases hpair
    refine ⟨⟨roots, result, hΓ'.bump result, ?_, hmiddle⟩,
      hslots.setEntry.bump result⟩
    · apply AValRealizes.slot
      · simp [VEnv.bump]
      · simp [VEnv.bump, VEnv.rel]

/-- Semantic non-final shared-variable rule. `dup` changes only one
reference count, so `StoreGraphExtends` transports every older environment
graph while the returned owner realizes the same source variable. -/
theorem lower_var_many_dup_value_sound {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value} {sourceValue : IxIR0.Value}
    {i abs remaining : Nat}
    (hsource : sourceEnv[i]? = some sourceValue)
    (hentry : Γ.entries[i]? =
      some (.slot abs (Nat.succ (Nat.succ remaining)) .many true)) :
    let Γ' := Γ.setEntry i
      (.slot abs (Nat.succ remaining) .many true)
    LowerResultValueSound funRel recSelfRel ctx cur Γ Γ'.bump
      sourceEnv sourceEnv sourceValue .shared
      (emitOp (.dup (.var (Γ'.rel abs)))) (.slotA Γ'.depth) := by
  dsimp only
  refine
    { toLowerResultSound := lower_var_many_dup_sound hentry
      graphEmits := ?_ }
  intro sourceRest rest slots
  apply OpSound.emit
  intro fuel store env store' result hpre hrun
  obtain ⟨⟨roots, hΓ, hrestGraph, hown⟩, hslots⟩ := hpre
  obtain ⟨foundSource, value, hfoundSource, hbound, hslot,
      hworld, hvalue, _, hupdated⟩ :=
    hΓ.entries.updateHeldAt (Nat.succ remaining) hentry
  have hsourceEq : foundSource = sourceValue :=
    Option.some.inj (hfoundSource.symm.trans hsource)
  subst foundSource
  let Γ' := Γ.setEntry i
    (.slot abs (Nat.succ remaining) .many true)
  have hΓ' : VEnvValueGraph funRel recSelfRel store Γ'
      sourceEnv env roots := hΓ.setEntry hupdated
  have hav : AValRealizes Γ' env (.slotA abs) value := by
    apply AValRealizes.slot
    · simpa [Γ', VEnv.setEntry] using hbound
    · simpa [Γ', VEnv.setEntry, VEnv.rel] using hslot
  have hshared : HasWorld store .shared value := by
    simpa [worldOfUses] using hworld
  cases fuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    obtain ⟨middle, heval, hstore, hresultGraph, hmiddle⟩ :=
      runOp_retain_borrowed_valueGraph
        (ctx := ctx) (cur := cur) (fuel := fuel)
        hav.resolveAtom hshared hvalue hown
    have hpair : (middle, value) = (store', result) :=
      Except.ok.inj (heval.symm.trans hrun)
    cases hpair
    have hΓmiddle : VEnvValueGraph funRel recSelfRel store' Γ'
        sourceEnv env roots := hΓ'.monoStore hstore
    have hrestGraph' : Sim.RootsGraph funRel store' sourceRest rest :=
      hrestGraph.monoStore hstore
    refine ⟨⟨roots, result, hΓmiddle.bump result, ?_, hresultGraph,
      hrestGraph', hmiddle⟩, hslots.setEntry.bump result⟩
    apply AValRealizes.slot
    · simp [VEnv.bump]
    · simp [VEnv.bump, VEnv.rel]

/-- Retain a held shared entry while replacing its compiler-side remaining
counter by an arbitrary smaller count. Ordinary variable duplication lowers
it by one; lambda capture lowers it by the whole captured occurrence count. -/
theorem lower_held_retain_sound_below {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {Γ : VEnv} {i abs remaining newRemaining : Nat}
    {uses : Uses}
    (hworldOfUses : worldOfUses uses = .shared)
    (hentry : Γ.entries[i]? =
      some (.slot abs remaining uses true)) :
    let Γ' := Γ.setEntry i (.slot abs newRemaining uses true)
    LowerResultSoundBelow ctx cur limit Γ Γ'.bump .shared
      (emitOp (.dup (.var (Γ'.rel abs)))) (.slotA Γ'.depth) := by
  dsimp only
  refine ⟨.slot, ?_⟩
  intro rest slots
  apply OpSoundBelow.emit
  intro fuel store env store' result _ hpre hrun
  obtain ⟨⟨roots, hΓ, hown⟩, hslots⟩ := hpre
  obtain ⟨value, hbound, hslot, hmem, hupdated⟩ :=
    hΓ.entries.updateHeldAt newRemaining hentry
  let Γ' := Γ.setEntry i (.slot abs newRemaining uses true)
  have hΓ' : VEnvRealizes Γ' env roots := hΓ.setEntry hupdated
  have hav : AValRealizes Γ' env (.slotA abs) value := by
    apply AValRealizes.slot
    · simpa [Γ', VEnv.setEntry] using hbound
    · simpa [Γ', VEnv.setEntry, VEnv.rel] using hslot
  have hworld : HasWorld store .shared value := by
    have hroot := hown.roots_world ⟨Owned.shared, value⟩
      (List.mem_append_left _ (by simpa [hworldOfUses] using hmem))
    exact hroot
  cases fuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    obtain ⟨middle, heval, hmiddle⟩ :=
      runOp_retain_borrowed (ctx := ctx) (cur := cur) (fuel := fuel)
        hav.resolveAtom hworld hown
    have hpair : (middle, value) = (store', result) :=
      Except.ok.inj (heval.symm.trans hrun)
    cases hpair
    refine ⟨⟨roots, result, hΓ'.bump result, ?_, hmiddle⟩,
      hslots.setEntry.bump result⟩
    · apply AValRealizes.slot
      · simp [VEnv.bump]
      · simp [VEnv.bump, VEnv.rel]

/-- Unbounded ownership interface for retaining a held shared entry while
installing an arbitrary residual source-use count. -/
theorem lower_held_retain_sound {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {i abs remaining newRemaining : Nat} {uses : Uses}
    (hworldOfUses : worldOfUses uses = .shared)
    (hentry : Γ.entries[i]? = some (.slot abs remaining uses true)) :
    let Γ' := Γ.setEntry i (.slot abs newRemaining uses true)
    LowerResultSound ctx cur Γ Γ'.bump .shared
      (emitOp (.dup (.var (Γ'.rel abs)))) (.slotA Γ'.depth) := by
  apply LowerResultSound.of_below
  intro limit
  exact lower_held_retain_sound_below
    (limit := limit) hworldOfUses hentry

/-- Semantic arbitrary-count retain. Allocation and all older value graphs
survive the single RC increment through `StoreGraphExtends`. -/
theorem lower_held_retain_value_sound {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value} {sourceValue : IxIR0.Value}
    {i abs remaining newRemaining : Nat} {uses : Uses}
    (hsource : sourceEnv[i]? = some sourceValue)
    (hworldOfUses : worldOfUses uses = .shared)
    (hentry : Γ.entries[i]? = some (.slot abs remaining uses true)) :
    let Γ' := Γ.setEntry i (.slot abs newRemaining uses true)
    LowerResultValueSound funRel recSelfRel ctx cur Γ Γ'.bump
      sourceEnv sourceEnv sourceValue .shared
      (emitOp (.dup (.var (Γ'.rel abs)))) (.slotA Γ'.depth) := by
  dsimp only
  refine
    { toLowerResultSound := lower_held_retain_sound hworldOfUses hentry
      graphEmits := ?_ }
  intro sourceRest rest slots
  apply OpSound.emit
  intro fuel store env store' result hpre hrun
  obtain ⟨⟨roots, hΓ, hrestGraph, hown⟩, hslots⟩ := hpre
  obtain ⟨foundSource, value, hfoundSource, hbound, hslot,
      hvalueWorld, hvalue, _, hupdated⟩ :=
    hΓ.entries.updateHeldAt newRemaining hentry
  have hsourceEq : foundSource = sourceValue :=
    Option.some.inj (hfoundSource.symm.trans hsource)
  subst foundSource
  let Γ' := Γ.setEntry i (.slot abs newRemaining uses true)
  have hΓ' : VEnvValueGraph funRel recSelfRel store Γ'
      sourceEnv env roots := hΓ.setEntry hupdated
  have hav : AValRealizes Γ' env (.slotA abs) value := by
    apply AValRealizes.slot
    · simpa [Γ', VEnv.setEntry] using hbound
    · simpa [Γ', VEnv.setEntry, VEnv.rel] using hslot
  have hshared : HasWorld store .shared value := by
    simpa [hworldOfUses] using hvalueWorld
  cases fuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    obtain ⟨middle, heval, hstore, hresultGraph, hmiddle⟩ :=
      runOp_retain_borrowed_valueGraph
        (ctx := ctx) (cur := cur) (fuel := fuel)
        hav.resolveAtom hshared hvalue hown
    have hpair : (middle, value) = (store', result) :=
      Except.ok.inj (heval.symm.trans hrun)
    cases hpair
    have hΓmiddle : VEnvValueGraph funRel recSelfRel store' Γ'
        sourceEnv env roots := hΓ'.monoStore hstore
    have hrestGraph' : Sim.RootsGraph funRel store' sourceRest rest :=
      hrestGraph.monoStore hstore
    refine ⟨⟨roots, result, hΓmiddle.bump result, ?_, hresultGraph,
      hrestGraph', hmiddle⟩, hslots.setEntry.bump result⟩
    apply AValRealizes.slot
    · simp [VEnv.bump]
    · simp [VEnv.bump, VEnv.rel]

/-- Fuel-bounded non-final use in the shared world. This also covers an
erased-use entry should one appear in an arbitrary input `VEnv`; generated
environments normally eliminate those entries before lowering. -/
theorem lower_var_shared_dup_sound_below {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {Γ : VEnv} {i abs remaining : Nat} {uses : Uses}
    (hworldOfUses : worldOfUses uses = .shared)
    (hentry : Γ.entries[i]? =
      some (.slot abs (Nat.succ (Nat.succ remaining)) uses true)) :
    let Γ' := Γ.setEntry i (.slot abs (Nat.succ remaining) uses true)
    LowerResultSoundBelow ctx cur limit Γ Γ'.bump .shared
      (emitOp (.dup (.var (Γ'.rel abs)))) (.slotA Γ'.depth) := by
  exact lower_held_retain_sound_below hworldOfUses hentry

/-- The ordinary `.many` specialization of shared duplication. -/
theorem lower_var_many_dup_sound_below {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {Γ : VEnv} {i abs remaining : Nat}
    (hentry : Γ.entries[i]? =
      some (.slot abs (Nat.succ (Nat.succ remaining)) .many true)) :
    let Γ' := Γ.setEntry i (.slot abs (Nat.succ remaining) .many true)
    LowerResultSoundBelow ctx cur limit Γ Γ'.bump .shared
      (emitOp (.dup (.var (Γ'.rel abs)))) (.slotA Γ'.depth) := by
  exact lower_var_shared_dup_sound_below (by rfl) hentry

/-! ## Lambda-capture lowering -/

/-- Canonical entry environment of a generated lifted function, factored
from `lowerLam` so compiler provenance can name the exact body-lowering run. -/
def liftedBodyVEnv (entryCount : Nat) (expr : IxIR0.Expr) : VEnv :=
  let parameterCount := lamArity expr
  let modes := lamUses expr
  let body := stripLams expr
  let captures := liftCaptureIndices entryCount expr
  ⟨parameterEntries captures.length modes (fun index =>
      countUses index body) ++
    selectedEntriesFrom
      (fun index => countUses index expr > 0)
      (fun index => countUses (parameterCount + index) body)
      (List.range entryCount) 0,
    captures.length + parameterCount⟩

/-- Canonical dead-parameter release plan paired with `liftedBodyVEnv`. -/
def liftedBodyDrops (entryCount : Nat) (expr : IxIR0.Expr) :
    List SlotDrop :=
  let body := stripLams expr
  let captures := liftCaptureIndices entryCount expr
  parameterDrops captures.length (lamUses expr)
    (fun index => countUses index body)

/-- Concrete provenance of a lifted declaration in an accumulated compiler
state. Its code must be the exact result of lowering the canonical stripped
lambda body, and the matching declaration must occur in `state.extra`. -/
def CompilerLiftCodeRel (src : IxIR0.Env) (state : LowSt) : LiftCodeRel :=
  fun address entryCount expr =>
    ∃ fuel initial generated code,
      (lowerFnBody src fuel (liftedBodyVEnv entryCount expr)
          (liftedBodyDrops entryCount expr) .shared (stripLams expr)).run
          initial = .ok code generated ∧
      (address, .fn
        ⟨(liftCaptureIndices entryCount expr).length + lamArity expr,
          .shared, code⟩) ∈ state.extra

/-- The lowering-specific function oracle for generated lifted paps in one
final compiler state. -/
abbrev CompilerLiftedFunctionRel (src : IxIR0.Env) (state : LowSt) :
    Sim.FunctionRel :=
  LiftedFunctionRel (CompilerLiftCodeRel src state)

/-- Exact lifted-body provenance survives later declaration generation. -/
theorem CompilerLiftCodeRel.monoState {src : IxIR0.Env}
    {initial final : LowSt} (hextends : ExtraExtends initial final)
    {address : Ixon.Address} {entryCount : Nat} {expr : IxIR0.Expr}
    (h : CompilerLiftCodeRel src initial address entryCount expr) :
    CompilerLiftCodeRel src final address entryCount expr := by
  obtain ⟨fuel, bodyInitial, generated, code, hrun, hmember⟩ := h
  exact ⟨fuel, bodyInitial, generated, code, hrun,
    hextends.extra_mem hmember⟩

theorem CompilerLiftedFunctionRel.monoState {src : IxIR0.Env}
    {initial final : LowSt} (hextends : ExtraExtends initial final)
    {value : IxIR0.Value} {address : Ixon.Address} {arity : Nat}
    {captures : List IxIR0.Value}
    (h : CompilerLiftedFunctionRel src initial value address arity captures) :
    CompilerLiftedFunctionRel src final value address arity captures := by
  apply h.mono
  intro generatedAddress entryCount expr hlift
  exact hlift.monoState hextends

/-- Capture bookkeeping never changes `LowSt`; it only rewrites the logical
`VEnv` and emitter returned as the action's value. -/
theorem lowerCapture_extraMonotone (e : IxIR0.Expr) (input : VEnv)
    (index : Nat) : ExtraMonotone (lowerCapture e input index) := by
  intro state finalState result hrun
  cases hentry : input.entries[index]? with
  | none =>
    exact (estateThrowRun_not_ok (by
      simpa [lowerCapture, hentry] using hrun)).elim
  | some entry =>
    cases entry with
    | recSelf arity =>
      exact (estateThrowRun_not_ok (by
        simpa [lowerCapture, hentry] using hrun)).elim
    | slot abs remaining uses held =>
      cases held with
      | false =>
        exact (estateThrowRun_not_ok (by
          simpa [lowerCapture, hentry] using hrun)).elim
      | true =>
        by_cases hunique : worldOfUses uses = .unique
        · have huuEq : (Owned.unique == Owned.unique) = true := by decide
          exact (estateThrowRun_not_ok (by
            simpa [lowerCapture, hentry, hunique, huuEq] using hrun)).elim
        · have huniqueEq :
              (worldOfUses uses == Owned.unique) = false := by
            cases uses <;> simp_all [worldOfUses] <;> decide
          by_cases hmore : remaining > countUses index e
          · have hpure : state = finalState := by
              have hresult :
                  (input.setEntry index
                      (.slot abs (remaining - countUses index e) uses true)).bump =
                      result.1 ∧
                    state = finalState := by
                have hfull :
                    ((input.setEntry index
                        (.slot abs (remaining - countUses index e) uses true)).bump,
                      emitOp (.dup (.var
                        ((input.setEntry index
                          (.slot abs (remaining - countUses index e) uses true)).rel abs))),
                      AVal.slotA
                        (input.setEntry index
                          (.slot abs (remaining - countUses index e) uses true)).depth) =
                        result ∧ state = finalState := by
                  simpa [lowerCapture, hentry, huniqueEq, hmore] using hrun
                exact ⟨congrArg (fun value : VEnv × Emit × AVal => value.1)
                  hfull.1, hfull.2⟩
              exact hresult.2
            subst finalState
            exact ExtraExtends.refl _
          · by_cases hequal : remaining = countUses index e
            · have hpure : state = finalState := by
                have hfull :
                    (input.setEntry index (.slot abs 0 uses false),
                      (_root_.id : Emit), AVal.slotA abs) = result ∧
                      state = finalState := by
                  simpa [lowerCapture, hentry, huniqueEq, hmore, hequal]
                    using hrun
                exact hfull.2
              subst finalState
              exact ExtraExtends.refl _
            · exact (estateThrowRun_not_ok (by
                simpa [lowerCapture, hentry, huniqueEq, hmore, hequal]
                  using hrun)).elim

/-- A whole capture traversal likewise preserves `LowSt.extra`. The generic
bind rule records this structurally rather than relying on an opaque fold. -/
theorem lowerCaptures_extraMonotone (e : IxIR0.Expr) :
    ∀ (input : VEnv) (caps : List Nat),
      ExtraMonotone (lowerCaptures e input caps) := by
  intro input caps
  induction caps generalizing input with
  | nil =>
    change ExtraMonotone
      (pure (input, (_root_.id : Emit), ([] : List AVal)) :
        LowerM (VEnv × Emit × List AVal))
    exact ExtraMonotone.pure _
  | cons index rest ih =>
    simp only [lowerCaptures]
    apply ExtraMonotone.bind (lowerCapture_extraMonotone e input index)
    intro headResult
    rcases headResult with ⟨middle, headEmit, headValue⟩
    apply ExtraMonotone.bind (ih middle)
    intro tailResult
    rcases tailResult with ⟨output, tailEmit, tailValues⟩
    exact ExtraMonotone.pure
      (output, headEmit ∘ tailEmit, headValue :: tailValues)

theorem lowerLam_extraMonotone_zero (src : IxIR0.Env)
    (input : VEnv) (e : IxIR0.Expr) :
    ExtraMonotone (lowerLam src 0 input e) := by
  simp only [lowerLam]
  exact ExtraMonotone.throw _

/-- Lambda lifting composes the state-preserving capture traversal, counter-
only fresh allocation, recursively monotone body lowering, and one explicit
extra-list prepend. -/
theorem lowerLam_extraMonotone_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hfn : LowerFnBodyExtraMonotone src fuel)
    (input : VEnv) (e : IxIR0.Expr) :
    ExtraMonotone (lowerLam src (fuel + 1) input e) := by
  simp only [lowerLam]
  cases hp : papSafe e with
  | false =>
    simp only [Bool.false_eq_true, if_false]
    exact ExtraMonotone.throwBind _ _
  | true =>
    simp only [↓reduceIte, bind_pure_comp]
    let caps := (List.range input.entries.length).filter
      (fun i => countUses i e > 0)
    have hcaps : caps = (List.range input.entries.length).filter
        (fun i => countUses i e > 0) := rfl
    rw [← hcaps]
    apply ExtraMonotone.bind (lowerCaptures_extraMonotone e input caps)
    intro captureResult
    rcases captureResult with ⟨captureOutput, captureEmit, captureValues⟩
    apply ExtraMonotone.bind freshAddr_extraMonotone
    intro fnAddr
    apply ExtraMonotone.bind (hfn _ _ _ _)
    intro code
    exact ExtraMonotone.map (pushExtra_extraMonotone _)
      (fun _ => (captureOutput.bump,
        captureEmit ∘ emitOp (.papp fnAddr
          (captureValues.map (·.toAtom captureOutput)).toArray),
        AVal.slotA captureOutput.depth))

theorem lowerArgsExtraMonotone_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEExtraMonotone src fuel)
    (hargs : LowerArgsExtraMonotone src fuel) :
    LowerArgsExtraMonotone src (fuel + 1) := by
  intro input args
  cases args with
  | nil =>
    simp only [lowerArgs]
    exact ExtraMonotone.pure _
  | cons head rest =>
    rcases head with ⟨expr, world⟩
    simp only [lowerArgs]
    apply ExtraMonotone.bind (hexpr input world expr)
    intro headResult
    rcases headResult with ⟨middle, headEmit, value⟩
    apply ExtraMonotone.bind (hargs middle rest)
    intro tailResult
    rcases tailResult with ⟨output, tailEmit, values⟩
    exact ExtraMonotone.pure
      (output, headEmit ∘ tailEmit, value :: values)

theorem applyRestExtraMonotone_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hargs : LowerArgsExtraMonotone src fuel) :
    ApplyRestExtraMonotone src (fuel + 1) := by
  intro input resultWorld pre function args
  cases function with
  | slotA abs =>
    simp only [applyRest]
    apply ExtraMonotone.bind
      (requireResultWorld_extraMonotone .shared resultWorld)
    intro unitValue
    cases unitValue
    apply ExtraMonotone.bind
      (hargs input (args.map (fun arg => (arg, Owned.shared))))
    intro argsResult
    rcases argsResult with ⟨output, argsEmit, values⟩
    exact ExtraMonotone.pure
      (output.bump,
        pre ∘ argsEmit ∘ emitOp (.apply
          ((AVal.slotA abs).toAtom output)
          (values.map (·.toAtom output)).toArray),
        AVal.slotA output.depth)
  | constA atom =>
    cases atom with
    | erased =>
      simp only [applyRest]
      apply ExtraMonotone.bind
        (hargs input (args.map (fun arg => (arg, Owned.shared))))
      intro argsResult
      rcases argsResult with ⟨output, argsEmit, values⟩
      exact ExtraMonotone.pure
        ((releaseAll output values).1,
          pre ∘ argsEmit ∘ (releaseAll output values).2,
          AVal.constA .erased)
    | var relative =>
      simp only [applyRest]
      apply ExtraMonotone.bind
        (requireResultWorld_extraMonotone .shared resultWorld)
      intro unitValue
      cases unitValue
      apply ExtraMonotone.bind
        (hargs input (args.map (fun arg => (arg, Owned.shared))))
      intro argsResult
      rcases argsResult with ⟨output, argsEmit, values⟩
      exact ExtraMonotone.pure
        (output.bump,
          pre ∘ argsEmit ∘ emitOp (.apply
            ((AVal.constA (.var relative)).toAtom output)
            (values.map (·.toAtom output)).toArray),
          AVal.slotA output.depth)
    | lit literal =>
      simp only [applyRest]
      apply ExtraMonotone.bind
        (requireResultWorld_extraMonotone .shared resultWorld)
      intro unitValue
      cases unitValue
      apply ExtraMonotone.bind
        (hargs input (args.map (fun arg => (arg, Owned.shared))))
      intro argsResult
      rcases argsResult with ⟨output, argsEmit, values⟩
      exact ExtraMonotone.pure
        (output.bump,
          pre ∘ argsEmit ∘ emitOp (.apply
            ((AVal.constA (.lit literal)).toAtom output)
            (values.map (·.toAtom output)).toArray),
          AVal.slotA output.depth)

theorem knownCallExtraMonotone_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hargs : LowerArgsExtraMonotone src fuel)
    (hrest : ApplyRestExtraMonotone src fuel) :
    KnownCallExtraMonotone src (fuel + 1) := by
  intro input build count argWorlds resultWorld args
  simp only [knownCall]
  apply ExtraMonotone.bind
    (hargs input ((args.take count).zip (padWorlds argWorlds count)))
  intro argsResult
  rcases argsResult with ⟨output, argsEmit, values⟩
  by_cases hterminal : args.length ≤ count
  · simp only [if_pos hterminal]
    exact ExtraMonotone.pure
      (output.bump,
        argsEmit ∘ emitOp
          (build (values.map (·.toAtom output)).toArray),
        AVal.slotA output.depth)
  · simp only [if_neg hterminal]
    exact hrest output.bump resultWorld
      (argsEmit ∘ emitOp
        (build (values.map (·.toAtom output)).toArray))
      (.slotA output.depth) (args.drop count)

/-- Variable borrowing never touches the generated-declaration state. The
case split mirrors the executable rejection/move/borrow branches. -/
theorem lowerBorrow_var_extraMonotone
    (src : IxIR0.Env) (fuel : Nat) (input : VEnv) (index : Nat) :
    ExtraMonotone
      (lowerBorrow src (fuel + 1) input (.var index)) := by
  simp only [lowerBorrow]
  cases hentry : input.entries[index]? with
  | none => exact ExtraMonotone.throw _
  | some entry =>
    cases entry with
    | recSelf arity => exact ExtraMonotone.throw _
    | slot abs remaining uses held =>
      cases held with
      | false => exact ExtraMonotone.throw _
      | true =>
        cases uses with
        | linear => exact ExtraMonotone.throw _
        | affine => exact ExtraMonotone.throw _
        | erased =>
          cases remaining with
          | zero => exact ExtraMonotone.throw _
          | succ remaining =>
            cases remaining with
            | zero => exact ExtraMonotone.pure _
            | succ remaining => exact ExtraMonotone.pure _
        | many =>
          cases remaining with
          | zero => exact ExtraMonotone.throw _
          | succ remaining =>
            cases remaining with
            | zero => exact ExtraMonotone.pure _
            | succ remaining => exact ExtraMonotone.pure _

/-- Variable consumption is state-only trivial even though its ownership
branching distinguishes demand, binder mode, and remaining-use count. -/
theorem lowerE_var_extraMonotone
    (src : IxIR0.Env) (fuel : Nat) (input : VEnv)
    (world : Owned) (index : Nat) :
    ExtraMonotone (lowerE src (fuel + 1) input world (.var index)) := by
  simp only [lowerE]
  cases hentry : input.entries[index]? with
  | none => exact ExtraMonotone.throw _
  | some entry =>
    cases entry with
    | recSelf arity => exact ExtraMonotone.throw _
    | slot abs remaining uses held =>
      cases held with
      | false => exact ExtraMonotone.throw _
      | true =>
        cases remaining with
        | zero =>
          cases uses <;> cases world <;>
            first
            | exact ExtraMonotone.pure _
            | exact ExtraMonotone.throw _
        | succ remaining =>
          cases remaining with
          | zero =>
            cases uses <;> cases world <;>
              first
              | exact ExtraMonotone.pure _
              | exact ExtraMonotone.throw _
          | succ remaining =>
            cases uses <;> cases world <;>
              first
              | exact ExtraMonotone.pure _
              | exact ExtraMonotone.throw _

theorem lowerE_ref_extraMonotone
    (src : IxIR0.Env) (fuel : Nat) (input : VEnv)
    (world : Owned) (address : Ixon.Address) :
    ExtraMonotone (lowerE src (fuel + 1) input world (.ref address)) := by
  simp only [lowerE]
  cases hsource : src address with
  | none =>
    simp only
    exact ExtraMonotone.throw _
  | some decl =>
    cases decl with
    | defn result body =>
      simp only
      cases harity : lamArity body with
      | zero =>
        apply ExtraMonotone.bind
          (requireResultWorld_extraMonotone result world)
        intro unitValue
        cases unitValue
        exact ExtraMonotone.pure _
      | succ arity =>
        cases result <;> cases world <;> cases hp : papSafe body <;>
          first
          | exact ExtraMonotone.pure _
          | exact ExtraMonotone.throw _
    | ctor tag arity =>
      simp only
      cases arity with
      | zero => exact ExtraMonotone.pure _
      | succ arity =>
        cases world with
        | unique => exact ExtraMonotone.throw _
        | shared =>
          apply ExtraMonotone.bind
            (wrapperFor_extraMonotone address tag (arity + 1))
          intro wrapper
          exact ExtraMonotone.pure _
    | recursor numArgs natLit rules =>
      simp only
      cases world <;> first
        | exact ExtraMonotone.pure _
        | exact ExtraMonotone.throw _
    | extern arity =>
      simp only
      cases arity with
      | zero => exact ExtraMonotone.pure _
      | succ arity =>
        cases world <;> first
          | exact ExtraMonotone.pure _
          | exact ExtraMonotone.throw _

theorem lowerE_lam_extraMonotone
    {src : IxIR0.Env} {fuel : Nat}
    (hlam : LowerLamExtraMonotone src fuel)
    (input : VEnv) (world : Owned) (uses : Uses)
    (body : IxIR0.Expr) :
    ExtraMonotone
      (lowerE src (fuel + 1) input world (.lam uses body)) := by
  cases world with
  | unique =>
    simp only [lowerE]
    exact ExtraMonotone.throw _
  | shared =>
    have hsuEq : (Owned.shared == Owned.unique) = false := by decide
    intro initial final result hrun
    apply hlam input (.lam uses body)
    simpa only [lowerE, hsuEq, Bool.false_eq_true, if_false] using hrun

theorem lowerE_proj_extraMonotone
    {src : IxIR0.Env} {fuel : Nat}
    (hborrow : LowerBorrowExtraMonotone src fuel)
    (input : VEnv) (world : Owned) (index : Nat)
    (source : IxIR0.Expr) :
    ExtraMonotone
      (lowerE src (fuel + 1) input world (.proj index source)) := by
  cases world with
  | unique =>
    simp only [lowerE]
    exact ExtraMonotone.throw _
  | shared =>
    simp only [lowerE]
    apply ExtraMonotone.bind (hborrow input source)
    intro borrowResult
    rcases borrowResult with ⟨output, emit, value, release⟩
    cases value with
    | slotA abs => cases release <;> exact ExtraMonotone.pure _
    | constA atom => cases atom <;> exact ExtraMonotone.pure _

theorem lowerE_let_extraMonotone
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEExtraMonotone src fuel)
    (input : VEnv) (world : Owned) (uses : Uses)
    (value body : IxIR0.Expr) :
    ExtraMonotone
      (lowerE src (fuel + 1) input world (.letE uses value body)) := by
  simp only [lowerE]
  apply ExtraMonotone.bind (hexpr input (worldOfUses uses) value)
  intro valueResult
  rcases valueResult with ⟨middle, valueEmit, boundValue⟩
  cases boundValue with
  | slotA abs =>
    by_cases hzero : countUses 0 body = 0
    · simp only [hzero, beq_self_eq_true, if_true]
      cases uses with
      | erased => exact ExtraMonotone.throwBind _ _
      | linear => exact ExtraMonotone.throwBind _ _
      | affine =>
        apply ExtraMonotone.bind (ExtraMonotone.pure _)
        intro releaseEmit
        apply ExtraMonotone.bind (hexpr _ world body)
        intro bodyResult
        rcases bodyResult with ⟨output, bodyEmit, result⟩
        exact ExtraMonotone.pure
          (output.pop, valueEmit ∘ releaseEmit ∘ bodyEmit, result)
      | many =>
        apply ExtraMonotone.bind (ExtraMonotone.pure _)
        intro releaseEmit
        apply ExtraMonotone.bind (hexpr _ world body)
        intro bodyResult
        rcases bodyResult with ⟨output, bodyEmit, result⟩
        exact ExtraMonotone.pure
          (output.pop, valueEmit ∘ releaseEmit ∘ bodyEmit, result)
    · simp [hzero]
      apply ExtraMonotone.bind (hexpr _ world body)
      intro bodyResult
      rcases bodyResult with ⟨output, bodyEmit, result⟩
      exact ExtraMonotone.pure
        (output.pop, valueEmit ∘ bodyEmit, result)
  | constA atom =>
    by_cases hzero : countUses 0 body = 0
    · simp only [hzero, beq_self_eq_true, if_true]
      apply ExtraMonotone.bind (hexpr _ world body)
      intro bodyResult
      rcases bodyResult with ⟨output, bodyEmit, result⟩
      exact ExtraMonotone.pure
        (output.pop,
          valueEmit ∘ emitOp (.pure atom) ∘ bodyEmit, result)
    · simp [hzero]
      apply ExtraMonotone.bind (hexpr _ world body)
      intro bodyResult
      rcases bodyResult with ⟨output, bodyEmit, result⟩
      exact ExtraMonotone.pure
        (output.pop,
          valueEmit ∘ emitOp (.pure atom) ∘ bodyEmit, result)

theorem lowerEExtraMonotone_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEExtraMonotone src fuel)
    (hspine : LowerSpineExtraMonotone src fuel)
    (hborrow : LowerBorrowExtraMonotone src fuel)
    (hlam : LowerLamExtraMonotone src fuel) :
    LowerEExtraMonotone src (fuel + 1) := by
  intro input world expr
  cases expr with
  | var index => exact (lowerE_var_extraMonotone
      src fuel input world index)
  | ref address => exact (lowerE_ref_extraMonotone
      src fuel input world address)
  | lit literal =>
    simp only [lowerE]
    exact ExtraMonotone.pure _
  | erased =>
    simp only [lowerE]
    exact ExtraMonotone.pure _
  | lam uses body => exact (lowerE_lam_extraMonotone
      hlam input world uses body)
  | letE uses value body => exact (lowerE_let_extraMonotone
      hexpr input world uses value body)
  | app function argument =>
    simp only [lowerE]
    exact hspine input world function [argument]
  | proj index source => exact (lowerE_proj_extraMonotone
      hborrow input world index source)

theorem lowerSpine_dynamic_extraMonotone
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEExtraMonotone src fuel)
    (hrest : ApplyRestExtraMonotone src fuel)
    (input : VEnv) (world : Owned) (head : IxIR0.Expr)
    (args : List IxIR0.Expr) :
    ExtraMonotone (do
      let (output, emit, function) ← lowerE src fuel input .shared head
      applyRest src fuel output world emit function args) := by
  apply ExtraMonotone.bind (hexpr input .shared head)
  intro headResult
  rcases headResult with ⟨output, emit, function⟩
  exact hrest output world emit function args

theorem lowerSpine_var_extraMonotone
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEExtraMonotone src fuel)
    (hknown : KnownCallExtraMonotone src fuel)
    (hrest : ApplyRestExtraMonotone src fuel)
    (input : VEnv) (world : Owned) (index : Nat)
    (args : List IxIR0.Expr) :
    ExtraMonotone
      (lowerSpine src (fuel + 1) input world (.var index) args) := by
  simp only [lowerSpine]
  cases hentry : input.entries[index]? with
  | none =>
    simp only
    exact lowerSpine_dynamic_extraMonotone
      hexpr hrest input world (.var index) args
  | some entry =>
    cases entry with
    | slot abs remaining uses held =>
      simp only
      exact lowerSpine_dynamic_extraMonotone
        hexpr hrest input world (.var index) args
    | recSelf arity =>
      simp only
      by_cases hunder : args.length < arity
      · simp only [if_pos hunder]
        exact ExtraMonotone.throw _
      · simp only [if_neg hunder]
        apply ExtraMonotone.bind
          (requireResultWorld_extraMonotone .shared world)
        intro unitValue
        cases unitValue
        exact hknown input (.callSelf ·) arity
          (List.replicate arity .shared) world args

theorem lowerSpine_ref_extraMonotone
    {src : IxIR0.Env} {fuel : Nat}
    (hknown : KnownCallExtraMonotone src fuel)
    (input : VEnv) (world : Owned) (address : Ixon.Address)
    (args : List IxIR0.Expr) :
    ExtraMonotone
      (lowerSpine src (fuel + 1) input world (.ref address) args) := by
  simp only [lowerSpine]
  cases hsource : src address with
  | none =>
    simp only
    exact ExtraMonotone.throw _
  | some decl =>
    cases decl with
    | defn result body =>
      simp only
      by_cases hunder : args.length < lamArity body
      · simp only [if_pos hunder]
        cases world with
        | unique => exact ExtraMonotone.throw _
        | shared =>
          cases result with
          | unique => exact ExtraMonotone.throw _
          | shared =>
            cases hp : papSafe body with
            | false => exact ExtraMonotone.throw _
            | true =>
              exact hknown input (.papp address ·) args.length
                (List.replicate args.length .shared) .shared args
      · simp only [if_neg hunder]
        apply ExtraMonotone.bind
          (requireResultWorld_extraMonotone result
            (if args.length == lamArity body then world else .shared))
        intro unitValue
        cases unitValue
        exact hknown input (.call address ·) (lamArity body)
          ((lamUses body).map worldOfUses) world args
    | ctor tag arity =>
      simp only
      by_cases hunder : args.length < arity
      · simp only [if_pos hunder]
        cases world with
        | unique => exact ExtraMonotone.throw _
        | shared =>
          apply ExtraMonotone.bind
            (wrapperFor_extraMonotone address tag arity)
          intro wrapper
          exact hknown input (.papp wrapper ·) args.length
            (List.replicate args.length .shared) .shared args
      · simp only [if_neg hunder]
        exact hknown input (.alloc world (ctorIdOf address tag) ·) arity
          (List.replicate arity world) world args
    | recursor numArgs natLit rules =>
      simp only
      by_cases hunder : args.length < numArgs + 1
      · simp only [if_pos hunder]
        cases world with
        | unique => exact ExtraMonotone.throw _
        | shared =>
          exact hknown input (.papp address ·) args.length
            (List.replicate args.length .shared) .shared args
      · simp only [if_neg hunder]
        apply ExtraMonotone.bind
          (requireResultWorld_extraMonotone .shared world)
        intro unitValue
        cases unitValue
        exact hknown input (.call address ·) (numArgs + 1)
          (List.replicate (numArgs + 1) .shared) world args
    | extern arity =>
      simp only
      by_cases hunder : args.length < arity
      · simp only [if_pos hunder]
        cases world with
        | unique => exact ExtraMonotone.throw _
        | shared =>
          exact hknown input (.papp address ·) args.length
            (List.replicate args.length .shared) .shared args
      · simp only [if_neg hunder]
        exact hknown input (.extern address ·) arity
          (List.replicate arity .shared) world args

theorem lowerSpineExtraMonotone_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEExtraMonotone src fuel)
    (hspine : LowerSpineExtraMonotone src fuel)
    (hknown : KnownCallExtraMonotone src fuel)
    (hrest : ApplyRestExtraMonotone src fuel) :
    LowerSpineExtraMonotone src (fuel + 1) := by
  intro input world head args
  cases head with
  | app function argument =>
    simp only [lowerSpine]
    exact hspine input world function (argument :: args)
  | erased =>
    simp only [lowerSpine]
    exact hrest input world (_root_.id : Emit) (.constA .erased) args
  | var index => exact (lowerSpine_var_extraMonotone
      hexpr hknown hrest input world index args)
  | ref address => exact (lowerSpine_ref_extraMonotone
      hknown input world address args)
  | lam uses body =>
    simp only [lowerSpine]
    exact lowerSpine_dynamic_extraMonotone
      hexpr hrest input world (.lam uses body) args
  | letE uses value body =>
    simp only [lowerSpine]
    exact lowerSpine_dynamic_extraMonotone
      hexpr hrest input world (.letE uses value body) args
  | proj index source =>
    simp only [lowerSpine]
    exact lowerSpine_dynamic_extraMonotone
      hexpr hrest input world (.proj index source) args
  | lit literal =>
    simp only [lowerSpine]
    exact lowerSpine_dynamic_extraMonotone
      hexpr hrest input world (.lit literal) args

/-- Every successful one-capture compiler step transfers one shared owner:
it retains into a fresh slot when later source uses remain, and otherwise
moves the existing slot owner. Unique/released/recursive entries and capture
overcounts cannot produce a successful run. -/
theorem lowerCapture_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat}
    {e : IxIR0.Expr} {input output : VEnv} {i : Nat}
    {emit : Emit} {av : AVal} {state finalState : LowSt}
    (hrun : (lowerCapture e input i).run state =
      .ok (output, emit, av) finalState) :
    LowerResultSoundBelow ctx cur limit input output .shared emit av := by
  cases hentry : input.entries[i]? with
  | none =>
    apply False.elim
    apply estateThrowRun_not_ok
    simpa [lowerCapture, hentry] using hrun
  | some entry =>
    cases entry with
    | recSelf arity =>
      apply False.elim
      apply estateThrowRun_not_ok
      simpa [lowerCapture, hentry] using hrun
    | slot abs remaining uses held =>
      cases held with
      | false =>
        apply False.elim
        apply estateThrowRun_not_ok
        simpa [lowerCapture, hentry] using hrun
      | true =>
        by_cases hunique : worldOfUses uses = .unique
        · apply False.elim
          apply estateThrowRun_not_ok
          have huuEq : (Owned.unique == Owned.unique) = true := by decide
          simpa [lowerCapture, hentry, hunique, huuEq] using hrun
        · have hshared : worldOfUses uses = .shared := by
            cases uses <;> simp_all [worldOfUses]
          have huniqueEq : (worldOfUses uses == Owned.unique) = false := by
            cases uses <;> simp_all [worldOfUses] <;> decide
          by_cases hmore : remaining > countUses i e
          · let next := input.setEntry i
              (.slot abs (remaining - countUses i e) uses true)
            have hpure :
                (next.bump, emitOp (.dup (.var (next.rel abs))),
                    AVal.slotA next.depth) = (output, emit, av) ∧
                  state = finalState := by
              simpa [lowerCapture, hentry, huniqueEq, hmore, next]
                using hrun
            obtain ⟨hresult, hstate⟩ := hpure
            cases hresult
            subst finalState
            have hsound := lower_held_retain_sound_below
              (ctx := ctx) (cur := cur) (limit := limit)
              (newRemaining := remaining - countUses i e) hshared hentry
            simpa [next] using hsound
          · by_cases hequal : remaining = countUses i e
            · let next := input.setEntry i (.slot abs 0 uses false)
              have hpure :
                  (next, (_root_.id : Emit), AVal.slotA abs) =
                      (output, emit, av) ∧ state = finalState := by
                simpa [lowerCapture, hentry, huniqueEq, hmore, hequal,
                  next] using hrun
              obtain ⟨hresult, hstate⟩ := hpure
              have houtput : next = output :=
                congrArg (fun p : VEnv × Emit × AVal => p.1) hresult
              have hemit : (_root_.id : Emit) = emit :=
                congrArg (fun p : VEnv × Emit × AVal => p.2.1) hresult
              have hvalue : AVal.slotA abs = av :=
                congrArg (fun p : VEnv × Emit × AVal => p.2.2) hresult
              subst output
              subst emit
              subst av
              subst finalState
              have hsound := lower_held_move_sound_below
                (ctx := ctx) (cur := cur) (limit := limit) hentry
              simpa [next, hshared] using hsound
            · apply False.elim
              apply estateThrowRun_not_ok
              simpa [lowerCapture, hentry, huniqueEq, hmore, hequal]
                using hrun

/-- Semantic one-capture compiler step. A successful capture selects the
source value at the same de Bruijn index and either moves or retains its
related shared root according to the compiler's remaining-use test. -/
theorem lowerCapture_run_value_sound
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef}
    {e : IxIR0.Expr} {input output : VEnv} {i : Nat}
    {sourceEnv : List IxIR0.Value} {sourceValue : IxIR0.Value}
    {emit : Emit} {av : AVal} {state finalState : LowSt}
    (hsource : sourceEnv[i]? = some sourceValue)
    (hrun : (lowerCapture e input i).run state =
      .ok (output, emit, av) finalState) :
    LowerResultValueSound funRel recSelfRel ctx cur input output
      sourceEnv sourceEnv sourceValue .shared emit av := by
  cases hentry : input.entries[i]? with
  | none =>
    exact (estateThrowRun_not_ok (by
      simpa [lowerCapture, hentry] using hrun)).elim
  | some entry =>
    cases entry with
    | recSelf arity =>
      exact (estateThrowRun_not_ok (by
        simpa [lowerCapture, hentry] using hrun)).elim
    | slot abs remaining uses held =>
      cases held with
      | false =>
        exact (estateThrowRun_not_ok (by
          simpa [lowerCapture, hentry] using hrun)).elim
      | true =>
        by_cases hunique : worldOfUses uses = .unique
        · have huuEq : (Owned.unique == Owned.unique) = true := by decide
          exact (estateThrowRun_not_ok (by
            simpa [lowerCapture, hentry, hunique, huuEq] using hrun)).elim
        · have hshared : worldOfUses uses = .shared := by
            cases uses <;> simp_all [worldOfUses]
          have huniqueEq :
              (worldOfUses uses == Owned.unique) = false := by
            cases uses <;> simp_all [worldOfUses] <;> decide
          by_cases hmore : remaining > countUses i e
          · let next := input.setEntry i
                (.slot abs (remaining - countUses i e) uses true)
            have hpure :
                (next.bump, emitOp (.dup (.var (next.rel abs))),
                    AVal.slotA next.depth) = (output, emit, av) ∧
                  state = finalState := by
              simpa [lowerCapture, hentry, huniqueEq, hmore, next]
                using hrun
            obtain ⟨hresult, hstate⟩ := hpure
            cases hresult
            subst finalState
            have hsound := lower_held_retain_value_sound
              (funRel := funRel) (recSelfRel := recSelfRel)
              (ctx := ctx) (cur := cur)
              (newRemaining := remaining - countUses i e)
              hsource hshared hentry
            simpa [next] using hsound
          · by_cases hequal : remaining = countUses i e
            · let next := input.setEntry i (.slot abs 0 uses false)
              have hpure :
                  (next, (_root_.id : Emit), AVal.slotA abs) =
                      (output, emit, av) ∧ state = finalState := by
                simpa [lowerCapture, hentry, huniqueEq, hmore, hequal,
                  next] using hrun
              obtain ⟨hresult, hstate⟩ := hpure
              have houtput : next = output :=
                congrArg (fun p : VEnv × Emit × AVal => p.1) hresult
              have hemit : (_root_.id : Emit) = emit :=
                congrArg (fun p : VEnv × Emit × AVal => p.2.1) hresult
              have hvalue : AVal.slotA abs = av :=
                congrArg (fun p : VEnv × Emit × AVal => p.2.2) hresult
              subst output
              subst emit
              subst av
              subst finalState
              have hsound := lower_held_move_value_sound
                (funRel := funRel) (recSelfRel := recSelfRel)
                (ctx := ctx) (cur := cur) hsource hentry
              simpa [next, hshared] using hsound
            · exact (estateThrowRun_not_ok (by
                simpa [lowerCapture, hentry, huniqueEq, hmore, hequal]
                  using hrun)).elim

/-- The structurally recursive capture traversal is a homogeneous shared
argument prefix. This is exactly the input expected by the existing verified
`papp` allocation rule. -/
theorem lowerCaptures_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat}
    (e : IxIR0.Expr) (caps : List Nat)
    {input output : VEnv} {emit : Emit} {values : List AVal}
    {state finalState : LowSt}
    (hrun : (lowerCaptures e input caps).run state =
      .ok (output, emit, values) finalState) :
    LowerArgsSoundBelow ctx cur limit input output
      (List.replicate caps.length .shared) emit values := by
  induction caps generalizing input output emit values state finalState with
  | nil =>
    have hpure :
        (input, (_root_.id : Emit), []) = (output, emit, values) ∧
          state = finalState := by
      simpa [lowerCaptures] using hrun
    obtain ⟨hresult, hstate⟩ := hpure
    cases hresult
    subst finalState
    exact lowerArgs_nil_sound_below
  | cons index rest ih =>
    simp only [lowerCaptures] at hrun
    obtain ⟨headResult, middleState, hheadRun, hafterHead⟩ :=
      estateBindRun_ok_inv hrun
    rcases headResult with ⟨middle, headEmit, headValue⟩
    obtain ⟨tailResult, tailState, htailRun, hafterTail⟩ :=
      estateBindRun_ok_inv hafterHead
    rcases tailResult with ⟨tailOutput, tailEmit, tailValues⟩
    have hpure :
        (tailOutput, headEmit ∘ tailEmit, headValue :: tailValues) =
            (output, emit, values) ∧ tailState = finalState := by
      simpa using hafterTail
    obtain ⟨hresult, hstate⟩ := hpure
    cases hresult
    subst finalState
    have hhead := lowerCapture_run_sound_below
      (ctx := ctx) (cur := cur) (limit := limit) hheadRun
    have htail := ih htailRun
    simpa [List.replicate_succ] using hhead.consArgs htail

/-- Semantic capture traversal. The returned pap arguments realize exactly
the selected source-environment values, in the compiler's capture order. -/
theorem lowerCaptures_run_value_sound
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef}
    (e : IxIR0.Expr) (caps : List Nat)
    {sourceEnv sourceValues : List IxIR0.Value}
    {input output : VEnv} {emit : Emit} {values : List AVal}
    {state finalState : LowSt}
    (hselected : ValuesAt sourceEnv caps sourceValues)
    (hrun : (lowerCaptures e input caps).run state =
      .ok (output, emit, values) finalState) :
    LowerArgsValueSound funRel recSelfRel ctx cur input output
      sourceEnv sourceEnv sourceValues
      (List.replicate caps.length .shared) emit values := by
  induction hselected generalizing input output emit values state finalState with
  | nil =>
    have hpure :
        (input, (_root_.id : Emit), []) = (output, emit, values) ∧
          state = finalState := by
      simpa [lowerCaptures] using hrun
    obtain ⟨hresult, hstate⟩ := hpure
    cases hresult
    subst finalState
    exact lowerArgs_nil_value_sound
  | @cons index sourceValue rest sourceValues hsource htailSelected ih =>
    simp only [lowerCaptures] at hrun
    obtain ⟨headResult, middleState, hheadRun, hafterHead⟩ :=
      estateBindRun_ok_inv hrun
    rcases headResult with ⟨middle, headEmit, headValue⟩
    obtain ⟨tailResult, tailState, htailRun, hafterTail⟩ :=
      estateBindRun_ok_inv hafterHead
    rcases tailResult with ⟨tailOutput, tailEmit, tailValues⟩
    have hpure :
        (tailOutput, headEmit ∘ tailEmit, headValue :: tailValues) =
            (output, emit, values) ∧ tailState = finalState := by
      simpa using hafterTail
    obtain ⟨hresult, hstate⟩ := hpure
    cases hresult
    subst finalState
    have hhead := lowerCapture_run_value_sound
      (funRel := funRel) (recSelfRel := recSelfRel)
      (ctx := ctx) (cur := cur) hsource hheadRun
    have htail := ih htailRun
    simpa [List.replicate_succ] using hhead.consArgs htail

/-- Successful capture lowering preserves the statically selected capture
count. Besides documenting the shape of `lowerCaptures`, this lets the
ownership proof index its homogeneous shared prefix by the returned values,
as required by the verified `papp` rule. -/
theorem lowerCaptures_success_length (e : IxIR0.Expr) :
    ∀ {caps : List Nat} {input output : VEnv} {emit : Emit}
      {values : List AVal} {state finalState : LowSt},
    (lowerCaptures e input caps).run state =
      .ok (output, emit, values) finalState →
    values.length = caps.length := by
  intro caps
  induction caps with
  | nil =>
    intro input output emit values state finalState hrun
    have hpure :
        (input, (_root_.id : Emit), []) = (output, emit, values) ∧
          state = finalState := by
      simpa [lowerCaptures] using hrun
    obtain ⟨hresult, _⟩ := hpure
    cases hresult
    rfl
  | cons index rest ih =>
    intro input output emit values state finalState hrun
    simp only [lowerCaptures] at hrun
    obtain ⟨headResult, middleState, _, hafterHead⟩ :=
      estateBindRun_ok_inv hrun
    rcases headResult with ⟨middle, headEmit, headValue⟩
    obtain ⟨tailResult, tailState, htailRun, hafterTail⟩ :=
      estateBindRun_ok_inv hafterHead
    rcases tailResult with ⟨tailOutput, tailEmit, tailValues⟩
    have hpure :
        (tailOutput, headEmit ∘ tailEmit, headValue :: tailValues) =
            (output, emit, values) ∧ tailState = finalState := by
      simpa using hafterTail
    obtain ⟨hresult, _⟩ := hpure
    cases hresult
    simp [ih htailRun]

/-- A successful local-lambda lowering consumes its captures as shared
arguments and installs them in a fresh partial-application node. The nested
lifted body may itself extend `LowSt`; only the final declaration-layout fact
is needed for ownership of the allocation performed at the lambda site. -/
theorem lowerLam_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat} {input output : VEnv} {e : IxIR0.Expr}
    {emit : Emit} {av : AVal} {state finalState : LowSt}
    (hpositive : 0 < lamArity e)
    (hrepresented : ExtraRepresented ctx finalState)
    (hrun : (lowerLam src fuel input e).run state =
      .ok (output, emit, av) finalState) :
    LowerResultSoundBelow ctx cur limit input output .shared emit av := by
  cases fuel with
  | zero =>
    simp [lowerLam] at hrun
    exact (estateThrowRun_not_ok hrun).elim
  | succ fuel =>
    cases hp : papSafe e with
    | false =>
      simp [lowerLam, hp] at hrun
    | true =>
      simp only [lowerLam] at hrun
      simp only [hp, ↓reduceIte, bind_pure_comp] at hrun
      let caps := (List.range input.entries.length).filter
        (fun i => countUses i e > 0)
      have hcaps : caps = (List.range input.entries.length).filter
          (fun i => countUses i e > 0) := rfl
      rw [← hcaps] at hrun
      obtain ⟨captureResult, captureState, hcaptureRun, hafterCapture⟩ :=
        estateBindRun_ok_inv hrun
      rcases captureResult with ⟨captureOutput, captureEmit, captureValues⟩
      dsimp only at hafterCapture
      obtain ⟨fnAddr, addressState, hfreshRun, hafterFresh⟩ :=
        estateBindRun_ok_inv hafterCapture
      obtain ⟨code, bodyState, hbodyRun, hafterBody⟩ :=
        estateBindRun_ok_inv hafterFresh
      change
        (pushExtra
            (fnAddr, .fn
              ⟨caps.length + lamArity e, .shared, code⟩) >>= fun _ =>
          pure (captureOutput.bump,
            captureEmit ∘ emitOp (.papp fnAddr
              (captureValues.map (·.toAtom captureOutput)).toArray),
            .slotA captureOutput.depth)).run bodyState =
          .ok (output, emit, av) finalState at hafterBody
      obtain ⟨unitValue, pushedState, hpushRun, hpureRun⟩ :=
        estateBindRun_ok_inv hafterBody
      cases unitValue
      have hpure :
          (captureOutput.bump,
              captureEmit ∘ emitOp (.papp fnAddr
                (captureValues.map (·.toAtom captureOutput)).toArray),
              AVal.slotA captureOutput.depth) =
              (output, emit, av) ∧
            pushedState = finalState := by
        simpa using hpureRun
      obtain ⟨hresult, hstate⟩ := hpure
      cases hresult
      subst finalState
      simp [pushExtra] at hpushRun
      subst pushedState
      have hdecl : ctx.decls fnAddr = some (.fn
          ⟨caps.length + lamArity e, .shared, code⟩) := by
        apply hrepresented.decl
        simp
      have hlength := lowerCaptures_success_length e hcaptureRun
      have hcaptures := lowerCaptures_run_sound_below
        (ctx := ctx) (cur := cur) (limit := limit) e caps hcaptureRun
      have hargs : LowerArgsSoundBelow ctx cur limit input captureOutput
          (List.replicate captureValues.length .shared)
          captureEmit captureValues := by
        simpa [hlength] using hcaptures
      apply hargs.papp_owned hdecl
      simp only [declArity]
      omega

/-- Semantic local-lambda lowering. The capture traversal constructs the
selected source-value prefix, the exact generated body run establishes
compiler provenance for the fresh address, and pap allocation yields a
`ValueGraph` for the source closure. `hinclude` embeds this lifted-only
relation into the whole-program function relation used by surrounding code. -/
theorem lowerLam_run_value_sound
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {src : IxIR0.Env}
    {fuel : Nat} {input output : VEnv} {e : IxIR0.Expr}
    {sourceEnv : List IxIR0.Value} {sourceValue : IxIR0.Value}
    {emit : Emit} {av : AVal} {state finalState : LowSt}
    (hsourceLength : sourceEnv.length = input.entries.length)
    (hprefix : LambdaPrefix sourceEnv e [] sourceValue)
    (hinclude : ∀ value address arity captures,
      CompilerLiftedFunctionRel src finalState value address arity captures →
      funRel value address arity captures)
    (hrepresented : ExtraRepresented ctx finalState)
    (hrun : (lowerLam src fuel input e).run state =
      .ok (output, emit, av) finalState) :
    LowerResultValueSound funRel recSelfRel ctx cur input output
      sourceEnv sourceEnv sourceValue .shared emit av := by
  have hpositive : 0 < lamArity e := by
    have hunder := hprefix.length_lt_lamArity
    simpa using hunder
  cases fuel with
  | zero =>
    simp [lowerLam] at hrun
    exact (estateThrowRun_not_ok hrun).elim
  | succ fuel =>
    cases hp : papSafe e with
    | false =>
      simp [lowerLam, hp] at hrun
    | true =>
      simp only [lowerLam] at hrun
      simp only [hp, ↓reduceIte, bind_pure_comp] at hrun
      let caps := (List.range input.entries.length).filter
        (fun index => countUses index e > 0)
      have hcaps : caps = (List.range input.entries.length).filter
          (fun index => countUses index e > 0) := rfl
      rw [← hcaps] at hrun
      obtain ⟨captureResult, captureState, hcaptureRun, hafterCapture⟩ :=
        estateBindRun_ok_inv hrun
      rcases captureResult with ⟨captureOutput, captureEmit, captureValues⟩
      dsimp only at hafterCapture
      obtain ⟨fnAddr, addressState, hfreshRun, hafterFresh⟩ :=
        estateBindRun_ok_inv hafterCapture
      obtain ⟨code, bodyState, hbodyRun, hafterBody⟩ :=
        estateBindRun_ok_inv hafterFresh
      change
        (pushExtra
            (fnAddr, .fn
              ⟨caps.length + lamArity e, .shared, code⟩) >>= fun _ =>
          pure (captureOutput.bump,
            captureEmit ∘ emitOp (.papp fnAddr
              (captureValues.map (·.toAtom captureOutput)).toArray),
            .slotA captureOutput.depth)).run bodyState =
          .ok (output, emit, av) finalState at hafterBody
      obtain ⟨unitValue, pushedState, hpushRun, hpureRun⟩ :=
        estateBindRun_ok_inv hafterBody
      cases unitValue
      have hpure :
          (captureOutput.bump,
              captureEmit ∘ emitOp (.papp fnAddr
                (captureValues.map (·.toAtom captureOutput)).toArray),
              AVal.slotA captureOutput.depth) =
              (output, emit, av) ∧
            pushedState = finalState := by
        simpa using hpureRun
      obtain ⟨hresult, hstate⟩ := hpure
      cases hresult
      subst finalState
      simp [pushExtra] at hpushRun
      subst pushedState
      let ambient : LowSt :=
        { bodyState with
          extra := (fnAddr, .fn
            ⟨caps.length + lamArity e, .shared, code⟩) ::
              bodyState.extra }
      have hincludeAmbient : ∀ value address arity captures,
          CompilerLiftedFunctionRel src ambient value address arity captures →
          funRel value address arity captures := by
        simpa [ambient] using hinclude
      have hdecl : ctx.decls fnAddr = some (.fn
          ⟨caps.length + lamArity e, .shared, code⟩) := by
        apply hrepresented.decl
        simp
      have hentryCount : captureOutput.entries.length =
          input.entries.length :=
        lowerCaptures_preservesEntryCount e hcaptureRun
      have hbodyRun' := hbodyRun
      rw [hentryCount] at hbodyRun'
      have hliftCode : CompilerLiftCodeRel src ambient fnAddr
          input.entries.length e := by
        refine ⟨fuel, addressState, bodyState, code, ?_, ?_⟩
        · simpa [liftedBodyVEnv, liftedBodyDrops, liftCaptureIndices,
            caps] using hbodyRun'
        · simp [ambient, liftCaptureIndices, caps]
      obtain ⟨selected, hselected⟩ :=
        ValuesAt.exists_liftCaptureIndices sourceEnv
          input.entries.length e hsourceLength
      have hselectedCaps : ValuesAt sourceEnv caps selected := by
        simpa [caps, liftCaptureIndices] using hselected
      have hselectedLength : selected.length = caps.length :=
        hselectedCaps.length
      have hlength := lowerCaptures_success_length e hcaptureRun
      have hcaptures := lowerCaptures_run_value_sound
        (funRel := funRel) (recSelfRel := recSelfRel)
        (ctx := ctx) (cur := cur) e caps hselectedCaps hcaptureRun
      have hargs : LowerArgsValueSound funRel recSelfRel ctx cur
          input captureOutput sourceEnv sourceEnv selected
          (List.replicate captureValues.length .shared)
          captureEmit captureValues := by
        simpa [hlength] using hcaptures
      have hlifted : CompilerLiftedFunctionRel src ambient sourceValue
          fnAddr (caps.length + lamArity e) selected := by
        refine ⟨sourceEnv, e, selected, [], ?_, ?_, ?_, ?_, hprefix⟩
        · simpa [hsourceLength] using hliftCode
        · simpa [hsourceLength] using hselected
        · simp
        · simp [hselectedLength]
      have hfun : funRel sourceValue fnAddr
          (caps.length + lamArity e) selected :=
        hincludeAmbient sourceValue fnAddr _ selected hlifted
      apply hargs.papp_graph hdecl
      · simpa only [declArity] using hfun
      · simp only [declArity]
        omega

/-- The lambda branch of `lowerE`: unique demand cannot succeed, while a
shared demand delegates to the verified capture-and-`papp` lowering above. -/
theorem lowerE_lam_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat} {input output : VEnv} {world : Owned} {uses : Uses}
    {body : IxIR0.Expr} {emit : Emit} {av : AVal}
    {state finalState : LowSt}
    (hrepresented : ExtraRepresented ctx finalState)
    (hrun : (lowerE src (fuel + 1) input world (.lam uses body)).run state =
      .ok (output, emit, av) finalState) :
    LowerResultSoundBelow ctx cur limit input output world emit av := by
  have huuEq : (Owned.unique == Owned.unique) = true := by decide
  have hsuEq : (Owned.shared == Owned.unique) = false := by decide
  cases world with
  | unique =>
    apply False.elim
    apply estateThrowRun_not_ok
    simpa [lowerE, huuEq] using hrun
  | shared =>
    have hlam : (lowerLam src fuel input (.lam uses body)).run state =
        .ok (output, emit, av) finalState := by
      simpa [lowerE, hsuEq] using hrun
    exact lowerLam_run_sound_below (by simp [lamArity])
      hrepresented hlam

/-- Semantic lambda branch of `lowerE`. The source evaluator returns its
closure immediately; successful shared lowering realizes that closure by the
fresh compiler-provenanced pap constructed above. -/
theorem lowerE_lam_run_value_sound
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {src : IxIR0.Env}
    {fuel : Nat} {input output : VEnv} {world : Owned} {uses : Uses}
    {body : IxIR0.Expr} {sourceEnv : List IxIR0.Value}
    {emit : Emit} {av : AVal} {state finalState : LowSt}
    (hsourceLength : sourceEnv.length = input.entries.length)
    (hinclude : ∀ value address arity captures,
      CompilerLiftedFunctionRel src finalState value address arity captures →
      funRel value address arity captures)
    (hrepresented : ExtraRepresented ctx finalState)
    (hrun : (lowerE src (fuel + 1) input world (.lam uses body)).run state =
      .ok (output, emit, av) finalState) :
    LowerResultValueSound funRel recSelfRel ctx cur input output
      sourceEnv sourceEnv (.clos uses sourceEnv body) world emit av := by
  have huuEq : (Owned.unique == Owned.unique) = true := by decide
  have hsuEq : (Owned.shared == Owned.unique) = false := by decide
  cases world with
  | unique =>
    exact (estateThrowRun_not_ok (by
      simpa [lowerE, huuEq] using hrun)).elim
  | shared =>
    have hlam : (lowerLam src fuel input (.lam uses body)).run state =
        .ok (output, emit, av) finalState := by
      simpa [lowerE, hsuEq] using hrun
    exact lowerLam_run_value_sound hsourceLength .nil hinclude
      hrepresented hlam

/-- Returning a lowered value is ownership-correct once every source entry
has been released or moved. -/
theorem ret_owns {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {world : Owned} {av : AVal} {rest : List Root}
    (hreleased : EntriesReleased Γ.entries) :
    CodeOwns ctx cur (OwnsResult Γ world av rest)
      (fun store value => RootOwnership store (⟨world, value⟩ :: rest))
      (.ret (av.toAtom Γ)) := by
  intro fuel store runtimeEnv store' value hpre hrun
  obtain ⟨roots, result, hΓ, hav, hown⟩ := hpre
  have hroots : roots = [] :=
    EntriesRealize.eq_nil_of_released hreleased hΓ.entries
  subst roots
  cases fuel with
  | zero => simp [runCode] at hrun
  | succ fuel =>
    rw [Nat.add_one] at hrun
    rw [runCode.eq_def] at hrun
    dsimp only at hrun
    rw [hav.resolveAtom] at hrun
    change (Except.ok (store, result) : Except Err (Store × RVal)) =
      .ok (store', value) at hrun
    have hpair : (store, result) = (store', value) := Except.ok.inj hrun
    cases hpair
    simpa using hown

/-- Close a sound expression emitter with the actual `ret` used by
`lowerFnBody`. This is the base shape of the eventual function-contract
construction. -/
theorem LowerResultSound.close {ctx : Ctx} {cur : FnDef}
    {input output : VEnv} {world : Owned} {emit : Emit} {av : AVal}
    (hsound : LowerResultSound ctx cur input output world emit av)
    (hreleased : EntriesReleased output.entries) (rest : List Root) :
    CodeOwns ctx cur (OwnsVEnv input rest)
      (fun store value => RootOwnership store (⟨world, value⟩ :: rest))
      (emit (.ret (av.toAtom output))) := by
  intro fuel store env store' value hpre hrun
  have hret : CodeOwns ctx cur
      (OwnsResultProtected output world av rest [])
      (fun store value => RootOwnership store (⟨world, value⟩ :: rest))
      (.ret (av.toAtom output)) := by
    intro innerFuel innerStore innerEnv finalStore finalValue hprotected hretRun
    exact ret_owns hreleased hprotected.1 hretRun
  have hcode : CodeOwns ctx cur (OwnsVEnvProtected input rest [])
      (fun store value => RootOwnership store (⟨world, value⟩ :: rest))
      (emit (.ret (av.toAtom output))) :=
    hsound.emits rest [] _ _ hret
  exact hcode ⟨hpre, SlotsRealize.nil⟩ hrun

/-- Fuel-bounded counterpart of `LowerResultSound.close`. -/
theorem LowerResultSoundBelow.close {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {input output : VEnv} {world : Owned}
    {emit : Emit} {av : AVal}
    (hsound : LowerResultSoundBelow ctx cur limit input output world emit av)
    (hreleased : EntriesReleased output.entries) (rest : List Root) :
    CodeOwnsBelow ctx cur limit (OwnsVEnv input rest)
      (fun store value => RootOwnership store (⟨world, value⟩ :: rest))
      (emit (.ret (av.toAtom output))) := by
  have hret : CodeOwnsBelow ctx cur limit
      (OwnsResultProtected output world av rest [])
      (fun store value => RootOwnership store (⟨world, value⟩ :: rest))
      (.ret (av.toAtom output)) := by
    intro fuel store env store' value _ hprotected hrun
    exact ret_owns hreleased hprotected.1 hrun
  have hcode : CodeOwnsBelow ctx cur limit
      (OwnsVEnvProtected input rest [])
      (fun store value => RootOwnership store (⟨world, value⟩ :: rest))
      (emit (.ret (av.toAtom output))) :=
    hsound.emits rest [] limit (Nat.le_refl _) _ _ hret
  intro fuel store env store' value hfuel hpre hrun
  exact hcode hfuel ⟨hpre, SlotsRealize.nil⟩ hrun

/-! ## Function-entry contracts -/

/-- Relate a lowerer's absolute-slot environment to the source-order
argument telescope of a function contract. `runCode` enters a function with
`args.reverse`, while `EntriesRealize` follows the lowerer's source-variable
order, so the realized roots need only be a permutation of the public
source-order roots. -/
def FnEntryRealizes (input : VEnv) (argWorlds : List Owned) : Prop :=
  ∀ {args : List RVal}, args.length = argWorlds.length →
    ∃ roots,
      VEnvRealizes input args.reverse roots ∧
      roots.Perm (rootsForWorlds argWorlds args)

theorem FnEntryRealizes.empty :
    FnEntryRealizes ⟨[], 0⟩ [] := by
  intro args hlength
  cases args with
  | nil => exact ⟨[], ⟨rfl, EntriesRealize.nil⟩, List.Perm.refl []⟩
  | cons arg tail => simp at hlength

/-- The canonical one-parameter entry layout used by `lowerDecl`. The
remaining-use count is irrelevant at entry; it affects only subsequent
lowering transitions. -/
theorem FnEntryRealizes.singleton (uses : Uses) (remaining : Nat) :
    FnEntryRealizes
      ⟨[.slot 0 remaining uses true], 1⟩
      [worldOfUses uses] := by
  intro args hlength
  cases args with
  | nil => simp at hlength
  | cons arg tail =>
    cases tail with
    | nil =>
      refine ⟨[⟨worldOfUses uses, arg⟩], ?_, List.Perm.refl _⟩
      constructor
      · rfl
      · exact EntriesRealize.held (by simp) rfl EntriesRealize.nil
    | cons next tail => simp at hlength

/-- Canonical parameter entries realize the reversed runtime argument stack
even in the presence of `base` older slots below the telescope. The extra
`suffix` is precisely those older slots. -/
theorem parameterEntries_entriesRealize (remaining : Nat → Nat) :
    ∀ (base : Nat) (modes : List Uses) {args suffix : List RVal},
      args.length = modes.length → suffix.length = base →
        let Γ : VEnv :=
          ⟨parameterEntries base modes remaining, base + modes.length⟩
        EntriesRealize Γ (args.reverse ++ suffix) Γ.entries
          (rootsForWorlds (modes.map worldOfUses) args).reverse := by
  intro base modes
  induction modes generalizing base with
  | nil =>
    intro args suffix hargs hsuffix
    cases args with
    | nil => exact EntriesRealize.nil
    | cons arg tail => simp at hargs
  | cons mode modes ih =>
    intro args suffix hargs hsuffix
    cases args with
    | nil => simp at hargs
    | cons arg args =>
      have htail : args.length = modes.length := by simpa using hargs
      let Γ : VEnv :=
        ⟨parameterEntries base (mode :: modes) remaining,
          base + (mode :: modes).length⟩
      let Δ : VEnv :=
        ⟨parameterEntries (base + 1) modes remaining,
          (base + 1) + modes.length⟩
      have hinner₀ := ih (base + 1) (args := args)
        (suffix := arg :: suffix) htail (by simp [hsuffix])
      have hdepth : Δ.depth = Γ.depth := by
        simp [Δ, Γ]
        omega
      have hinner : EntriesRealize Γ
          ((arg :: args).reverse ++ suffix)
          (parameterEntries (base + 1) modes remaining)
          (rootsForWorlds (modes.map worldOfUses) args).reverse := by
        have htransport := hinner₀.of_depth_eq hdepth
        simpa [List.reverse_cons, List.append_assoc, Δ, Γ] using htransport
      have houter : EntriesRealize Γ
          ((arg :: args).reverse ++ suffix)
          [.slot base (remaining modes.length) mode true]
          [⟨worldOfUses mode, arg⟩] := by
        apply EntriesRealize.held
        · simp [Γ]
        · simp [Γ, VEnv.rel, List.reverse_cons, htail]
        · exact EntriesRealize.nil
      simpa [Γ, parameterEntries, List.reverse_cons] using
        hinner.append houter

/-- Every canonical direct-function parameter layout realizes the public
source-order argument telescope. -/
theorem FnEntryRealizes.parameterEntries (modes : List Uses)
    (remaining : Nat → Nat) :
    FnEntryRealizes
      ⟨parameterEntries 0 modes remaining, modes.length⟩
      (modes.map worldOfUses) := by
  intro args hlength
  have hmodes : args.length = modes.length := by simpa using hlength
  refine ⟨(rootsForWorlds (modes.map worldOfUses) args).reverse, ?_,
    List.reverse_perm _⟩
  constructor
  · simpa using hmodes
  · simpa using parameterEntries_entriesRealize remaining 0 modes
      (args := args) (suffix := []) hmodes rfl

/-- A bounded closed-body emitter yields ownership preservation at the exact
evaluator index forming its bound. This is the declaration-level step used by
the mutual source-context contract induction. -/
theorem LowerResultSoundBelow.fnOwnershipPreservesAt
    {ctx : Ctx} {d : FnDef} {limit : Nat}
    {input output : VEnv} {argWorlds : List Owned}
    {emit : Emit} {av : AVal}
    (hsound : LowerResultSoundBelow ctx d limit input output d.result emit av)
    (hentry : FnEntryRealizes input argWorlds)
    (harity : argWorlds.length = d.arity)
    (hreleased : EntriesReleased output.entries)
    (hbody : d.body = emit (.ret (av.toAtom output))) :
    FnOwnershipPreservesAt ctx d argWorlds limit := by
  intro store store' args value rest hlength hown hrun
  obtain ⟨roots, hinput, hperm⟩ := hentry hlength
  have hcode : CodeOwnsBelow ctx d limit (OwnsVEnv input rest)
      (fun finalStore finalValue =>
        RootOwnership finalStore (⟨d.result, finalValue⟩ :: rest))
      (emit (.ret (av.toAtom output))) :=
    hsound.close hreleased rest
  rw [hbody] at hrun
  apply hcode (Nat.le_refl limit)
  · refine ⟨roots, hinput, ?_⟩
    exact hown.perm (hperm.symm.append_right rest)
  · exact hrun

/-- Body-level ownership invariant used to construct a callable function
contract. It separates the mechanical entry-layout proof from the compiler
induction that proves the emitted body code. -/
structure FnBodySound (ctx : Ctx) (d : FnDef) (input : VEnv)
    (argWorlds : List Owned) : Prop where
  arity_eq : argWorlds.length = d.arity
  entry_realizes : FnEntryRealizes input argWorlds
  body_owns : ∀ rest,
    CodeOwns ctx d (OwnsVEnv input rest)
      (fun store value =>
        RootOwnership store (⟨d.result, value⟩ :: rest))
      d.body

/-- A body proof whose entry slots realize the source argument telescope is
exactly the externally callable `FnOwnershipContract`. -/
theorem FnBodySound.contract {ctx : Ctx} {d : FnDef} {input : VEnv}
    {argWorlds : List Owned}
    (h : FnBodySound ctx d input argWorlds) :
    FnOwnershipContract ctx d argWorlds := by
  refine ⟨h.arity_eq, ?_⟩
  intro fuel store store' args value rest hlength hown hrun
  obtain ⟨roots, hinput, hperm⟩ := h.entry_realizes hlength
  apply h.body_owns rest
  · refine ⟨roots, hinput, ?_⟩
    exact hown.perm (hperm.symm.append_right rest)
  · exact hrun

/-- Package a closed expression-lowering derivation as a body invariant for
the actual emitted `FnDef`. This is the reusable bridge from the compiler
induction to declaration contracts. -/
theorem LowerResultSound.fnBodySound {ctx : Ctx} {d : FnDef}
    {input output : VEnv} {argWorlds : List Owned}
    {emit : Emit} {av : AVal}
    (hsound : LowerResultSound ctx d input output d.result emit av)
    (hentry : FnEntryRealizes input argWorlds)
    (harity : argWorlds.length = d.arity)
    (hreleased : EntriesReleased output.entries)
    (hbody : d.body = emit (.ret (av.toAtom output))) :
    FnBodySound ctx d input argWorlds := by
  refine ⟨harity, hentry, ?_⟩
  intro rest
  rw [hbody]
  exact hsound.close hreleased rest

/-- Direct constructor for the contract of a successfully lowered and
closed function body. -/
theorem LowerResultSound.fnOwnershipContract {ctx : Ctx} {d : FnDef}
    {input output : VEnv} {argWorlds : List Owned}
    {emit : Emit} {av : AVal}
    (hsound : LowerResultSound ctx d input output d.result emit av)
    (hentry : FnEntryRealizes input argWorlds)
    (harity : argWorlds.length = d.arity)
    (hreleased : EntriesReleased output.entries)
    (hbody : d.body = emit (.ret (av.toAtom output))) :
    FnOwnershipContract ctx d argWorlds :=
  (hsound.fnBodySound hentry harity hreleased hbody).contract

/-- Verified `.defn` declaration rule. The mutual compiler induction supplies
the concrete release plan and recursive body proof; this theorem runs the
actual `lowerDecl` branch and packages its emitted function as a callable
ownership contract. -/
theorem lowerDecl_defn_verified {ctx : Ctx}
    (src : IxIR0.Env) (fuel : Nat) (address : Ixon.Address)
    (result : Owned) (body : IxIR0.Expr)
    (middle output : VEnv) (releaseEmit emit : Emit) (av : AVal)
    (state finalState : LowSt) (d : FnDef)
    (hplan : ReleasePlan
      ⟨parameterEntries 0 (lamUses body)
          (fun i => countUses i (stripLams body)), lamArity body⟩
      (parameterDrops 0 (lamUses body)
        (fun i => countUses i (stripLams body)))
      middle releaseEmit)
    (hbodyRun : (lowerE src fuel middle result (stripLams body)).run state =
      .ok (output, emit, av) finalState)
    (hd : d =
      ⟨lamArity body, result,
        (releaseEmit ∘ emit) (.ret (av.toAtom output))⟩)
    (hbody : LowerResultSound ctx d middle output result emit av)
    (hreleased : EntriesReleased output.entries) :
    (lowerDecl src (Nat.succ fuel) (address, .defn result body)).run state =
        .ok (some (address, .fn d)) finalState ∧
      FnOwnershipContract ctx d ((lamUses body).map worldOfUses) := by
  subst d
  let remaining : Nat → Nat := fun i => countUses i (stripLams body)
  let input : VEnv :=
    ⟨parameterEntries 0 (lamUses body) remaining, lamArity body⟩
  let drops := parameterDrops 0 (lamUses body) remaining
  have hfn := lowerFnBody_verified (ctx := ctx)
    (cur := ⟨lamArity body, result,
      (releaseEmit ∘ emit) (.ret (av.toAtom output))⟩)
    src fuel input middle output drops result (stripLams body)
    releaseEmit emit av state finalState (by simpa [input, drops, remaining]
      using hplan) hbodyRun hbody
  constructor
  · simp only [lowerDecl]
    rw [estateBindRun]
    have hrun := hfn.1
    simp only [input, drops, remaining] at hrun
    rw [hrun]
    rfl
  · have hentry : FnEntryRealizes input
        ((lamUses body).map worldOfUses) := by
      have hinput : input =
          ⟨parameterEntries 0 (lamUses body) remaining,
            (lamUses body).length⟩ := by
        simp [input]
      rw [hinput]
      intro args hlength
      exact (FnEntryRealizes.parameterEntries (lamUses body) remaining)
        hlength
    apply hfn.2.fnOwnershipContract hentry
    · simp
    · exact hreleased
    · rfl

/-- Definition-level rule with compiler-generated parameter releases. The
caller proves only the mode admissibility condition and continues from the
actual successful `releaseSlots` result; the indexed `ReleasePlan` is
constructed internally. This is the interface expected by the eventual
mutual lowering proof. -/
theorem lowerDecl_defn_generated_verified {ctx : Ctx}
    (src : IxIR0.Env) (fuel : Nat) (address : Ixon.Address)
    (result : Owned) (body : IxIR0.Expr) (state : LowSt)
    (hadmissible : ParameterDropsAdmissible (lamUses body)
      (fun i => countUses i (stripLams body)))
    (hbody : ∀ middle releaseEmit,
      (releaseSlots
        ⟨parameterEntries 0 (lamUses body)
            (fun i => countUses i (stripLams body)), lamArity body⟩
        (parameterDrops 0 (lamUses body)
          (fun i => countUses i (stripLams body)))).run state =
          .ok (middle, releaseEmit) state →
      ∃ output emit av finalState,
        (lowerE src fuel middle result (stripLams body)).run state =
          .ok (output, emit, av) finalState ∧
        LowerResultSound ctx
          ⟨lamArity body, result,
            (releaseEmit ∘ emit) (.ret (av.toAtom output))⟩
          middle output result emit av ∧
        EntriesReleased output.entries) :
    ∃ finalState d,
      (lowerDecl src (Nat.succ fuel) (address, .defn result body)).run state =
        .ok (some (address, .fn d)) finalState ∧
      FnOwnershipContract ctx d ((lamUses body).map worldOfUses) := by
  let remaining : Nat → Nat := fun i => countUses i (stripLams body)
  let input : VEnv :=
    ⟨parameterEntries 0 (lamUses body) remaining, lamArity body⟩
  let drops := parameterDrops 0 (lamUses body) remaining
  obtain ⟨middle, releaseEmit, rawPlan⟩ :=
    parameterDrops_releasePlan 0 (lamUses body) remaining
      (by simpa [remaining] using hadmissible)
  have hplan : ReleasePlan input drops middle releaseEmit := by
    simpa [input, drops, remaining] using rawPlan
  obtain ⟨output, emit, av, finalState, hbodyRun, hsound, hreleased⟩ :=
    hbody middle releaseEmit
      (by simpa [input, drops, remaining] using hplan.run state)
  let d : FnDef :=
    ⟨lamArity body, result,
      (releaseEmit ∘ emit) (.ret (av.toAtom output))⟩
  refine ⟨finalState, d, ?_⟩
  have hdecl := lowerDecl_defn_verified (ctx := ctx)
    src fuel address result body middle output releaseEmit emit av
    state finalState d hplan hbodyRun rfl hsound hreleased
  simpa [d] using hdecl

/-! ## Case-alternative contracts -/

/-- Runtime shape of a recursor alternative before the dispatcher pushes its
constructor fields. `pre` is in source argument order; the function runtime
environment is reversed and headed by the major premise. -/
def RecursorEntryValid (numArgs : Nat)
    (env : List RVal) (_fields : Array RVal) : Prop :=
  ∃ (pre : List RVal) (major : RVal),
    pre.length = numArgs ∧ env = major :: pre.reverse

/-- Public function-argument roots consumed by a recursor alternative. The
runtime environment is reversed, so reversing it recovers source order. -/
def recursorEntryRoots
    (env : List RVal) (_fields : Array RVal) : List Root :=
  rootsFor .shared env.reverse

/-- Canonical logical entry layout at the start of a recursor alternative:
released field placeholders, all-shared pre-major parameters, and synthetic
recursive self. -/
def recursorInitialVEnv (numArgs nf : Nat) (rhs : IxIR0.Expr) : VEnv :=
  let dead : VEntry := .slot 0 0 .many false
  ⟨List.replicate nf dead ++
      parameterEntries 0 (List.replicate numArgs .many)
        (fun i => countUses (nf + i) rhs) ++
      [.recSelf (numArgs + 1)],
    (numArgs + 1) + nf⟩

/-- Protected major and constructor-field positions at alternative entry.
The major lies immediately above the `numArgs` older parameters; fields
then occupy consecutive absolute positions in constructor order. -/
def recursorEntrySlots (numArgs : Nat) (major : RVal)
    (fields : Array RVal) : List (Nat × RVal) :=
  recursorFieldSlots numArgs (major :: fields.toList)

/-- Relate a selected alternative's physical entry environment to the roots
owned by that branch. `entryValid` carries arity/layout side conditions;
borrowed field evidence remains separate because fields are not roots until
the emitted prefix explicitly retains them. -/
def AltEntryRealizes (input : VEnv) (fieldCount : Nat)
    (entryValid : List RVal → Array RVal → Prop)
    (entryRoots : List RVal → Array RVal → List Root) : Prop :=
  ∀ {env : List RVal} {fields : Array RVal},
    fields.size = fieldCount → entryValid env fields →
      ∃ roots,
        VEnvRealizes input
          (fields.foldl (fun branchEnv field => field :: branchEnv) env)
          roots ∧
        roots.Perm (entryRoots env fields)

/-- State at the start of a selected case alternative: its physical field
bindings, exact owned roots, and the non-owning field-world facts exposed by
the dispatcher. -/
def OwnsAltEntry (fieldWorld : Owned)
    (entryRoots : List RVal → Array RVal → List Root)
    (env : List RVal) (fields : Array RVal) (rest : List Root) : StatePred :=
  fun store branchEnv =>
    branchEnv =
        fields.foldl (fun current field => field :: current) env ∧
      RootOwnership store (entryRoots env fields ++ rest) ∧
      ∀ field ∈ fields.toList, HasWorld store fieldWorld field

/-- Convert the public recursor alternative entry state into the exact
logical split expected by the generated field-retain fold. Pre-major
parameters are owned by the `VEnv`; the major remains the first external
root; fields remain borrowed, with every original absolute slot protected. -/
theorem recursorAltEntry_borrowed_state
    (numArgs nf : Nat) (rhs : IxIR0.Expr)
    (pre : List RVal) (major : RVal) (fields : Array RVal)
    (hpreLength : pre.length = numArgs) (hfields : fields.size = nf)
    (rest : List Root) :
    ∀ {store branchEnv},
      OwnsAltEntry .shared recursorEntryRoots
          (major :: pre.reverse) fields rest store branchEnv →
      OwnsVEnvBorrowed (recursorInitialVEnv numArgs nf rhs)
        (⟨.shared, major⟩ :: rest)
        (recursorEntrySlots numArgs major fields) fields.toList
        store branchEnv := by
  intro store branchEnv hentry
  obtain ⟨hbranch, hown, hborrowed⟩ := hentry
  rw [Array.foldl_cons_eq_reverse_append] at hbranch
  subst branchEnv
  let modes := List.replicate numArgs Uses.many
  let remaining : Nat → Nat := fun i => countUses (nf + i) rhs
  have hargs : pre.length = (modes.map worldOfUses).length := by
    simp [modes, hpreLength]
  obtain ⟨preRoots, hpreRealize, hprePerm⟩ :=
    (FnEntryRealizes.parameterEntries modes remaining) hargs
  have hpushed := hpreRealize.bumpList (major :: fields.toList)
  let input := recursorInitialVEnv numArgs nf rhs
  have hfieldsLength : fields.toList.length = nf := by
    simpa using hfields
  have hpushedDepth :
      (addVEnvDepth
        ⟨parameterEntries 0 modes remaining, modes.length⟩
        (major :: fields.toList).length).depth = input.depth := by
    simp [addVEnvDepth, input, recursorInitialVEnv, modes,
      hfieldsLength]
    omega
  have hparams : EntriesRealize input
      (fields.toList.reverse ++ major :: pre.reverse)
      (parameterEntries 0 modes remaining) preRoots := by
    have htransport := hpushed.entries.of_depth_eq hpushedDepth
    simpa [addVEnvDepth, List.reverse_cons, List.append_assoc]
      using htransport
  let dead : VEntry := .slot 0 0 .many false
  have hdead : EntriesRealize input
      (fields.toList.reverse ++ major :: pre.reverse)
      (List.replicate nf dead) [] := by
    apply EntriesRealize.replicateReleased
    simp [input, recursorInitialVEnv]
    omega
  have hentries : EntriesRealize input
      (fields.toList.reverse ++ major :: pre.reverse)
      input.entries preRoots := by
    have hself : EntriesRealize input
        (fields.toList.reverse ++ major :: pre.reverse)
        [.recSelf (numArgs + 1)] [] :=
      EntriesRealize.recSelf EntriesRealize.nil
    have hall := hdead.append (hparams.append hself)
    simpa [input, recursorInitialVEnv, modes, remaining, dead,
      List.append_assoc] using hall
  have hdepth :
      (fields.toList.reverse ++ major :: pre.reverse).length =
        input.depth := by
    simp [input, recursorInitialVEnv, hfieldsLength, hpreLength]
    omega
  have hslotDepth :
      (⟨[], pre.reverse.length + (major :: fields.toList).length⟩ :
          VEnv).depth = input.depth := by
    simp [input, recursorInitialVEnv, hfieldsLength, hpreLength]
    omega
  have hslots : SlotsRealize input
      (fields.toList.reverse ++ major :: pre.reverse)
      (recursorEntrySlots numArgs major fields) := by
    have hraw := recursorFieldSlots_realize_list
      pre.reverse (major :: fields.toList)
    have htransport := hraw.of_depth_eq hslotDepth
    simpa [recursorEntrySlots, hpreLength, List.reverse_cons,
      List.append_assoc] using htransport
  have hworlds :
      rootsForWorlds (modes.map worldOfUses) pre =
        rootsFor .shared pre := by
    have hrep : modes.map worldOfUses =
        List.replicate numArgs Owned.shared := by
      simp [modes, worldOfUses]
    rw [hrep]
    exact rootsForWorlds_replicate_eq_rootsFor .shared hpreLength
  rw [hworlds] at hprePerm
  have howned : RootOwnership store
      (preRoots ++ ⟨.shared, major⟩ :: rest) := by
    apply hown.perm
    simpa [recursorEntryRoots, rootsFor, List.reverse_cons,
      List.append_assoc] using
      hprePerm.symm.append_right (⟨.shared, major⟩ :: rest)
  exact ⟨⟨⟨preRoots, ⟨hdepth, hentries⟩, howned⟩, hslots⟩,
    hborrowed⟩

/-- Identity-emitter wrapper for the recursor entry-state conversion. -/
theorem recursorAltEntry_borrowed {ctx : Ctx} {cur : FnDef}
    (numArgs nf : Nat) (rhs : IxIR0.Expr)
    (pre : List RVal) (major : RVal) (fields : Array RVal)
    (hpreLength : pre.length = numArgs) (hfields : fields.size = nf)
    (rest : List Root) :
    EmitSound ctx cur (_root_.id : Emit)
      (OwnsAltEntry .shared recursorEntryRoots
        (major :: pre.reverse) fields rest)
      (OwnsVEnvBorrowed (recursorInitialVEnv numArgs nf rhs)
        (⟨.shared, major⟩ :: rest)
        (recursorEntrySlots numArgs major fields) fields.toList) := by
  apply EmitSound.strengthen
  exact recursorAltEntry_borrowed_state numArgs nf rhs pre major fields
    hpreLength hfields rest

/-- Fuel-bounded identity-emitter wrapper for recursor entry conversion. -/
theorem recursorAltEntry_borrowed_below {ctx : Ctx} {cur : FnDef}
    {limit : Nat} (numArgs nf : Nat) (rhs : IxIR0.Expr)
    (pre : List RVal) (major : RVal) (fields : Array RVal)
    (hpreLength : pre.length = numArgs) (hfields : fields.size = nf)
    (rest : List Root) :
    EmitSoundBelow ctx cur limit (_root_.id : Emit)
      (OwnsAltEntry .shared recursorEntryRoots
        (major :: pre.reverse) fields rest)
      (OwnsVEnvBorrowed (recursorInitialVEnv numArgs nf rhs)
        (⟨.shared, major⟩ :: rest)
        (recursorEntrySlots numArgs major fields) fields.toList) := by
  apply EmitSoundBelow.strengthen
  exact recursorAltEntry_borrowed_state numArgs nf rhs pre major fields
    hpreLength hfields rest

/-- End-to-end certificate for the complete generated recursor prefix at an
arbitrary branch width: retain every used borrowed field, release the major,
then execute the canonical dead-parameter release plan. The returned
`VEnv` is exactly the input expected by lowering the rule RHS. -/
theorem recursorPrefix_generated_verified {ctx : Ctx} {cur : FnDef}
    (numArgs nf : Nat) (rhs : IxIR0.Expr) (state : LowSt) :
    let dead : VEntry := .slot 0 0 .many false
    let fieldInput : VEnv :=
      ⟨List.replicate nf dead, (numArgs + 1) + nf⟩
    let retains := recursorFieldRetains (numArgs + 1) rhs nf
    let frame :=
      parameterEntries 0 (List.replicate numArgs .many)
          (fun i => countUses (nf + i) rhs) ++
        [.recSelf (numArgs + 1)]
    let drops :=
      (parameterDrops 0 (List.replicate numArgs .many)
          (fun i => countUses (nf + i) rhs)).map
        (SlotDrop.offsetEntry nf)
    ∃ fieldOutput fieldEmit rhsInput parameterEmit,
      applyRecursorFieldRetains fieldInput retains =
        (fieldOutput, fieldEmit) ∧
      (releaseSlots
          ⟨fieldOutput.entries ++ frame, fieldOutput.depth + 1⟩
          drops).run state = .ok (rhsInput, parameterEmit) state ∧
      ∀ {pre : List RVal} {major : RVal} {fields : Array RVal}
          {rest : List Root},
        pre.length = numArgs → fields.size = nf →
          EmitSound ctx cur
            (fieldEmit ∘
              emitOp (.drop (.var (fieldOutput.rel numArgs))) ∘
              parameterEmit)
            (OwnsAltEntry .shared recursorEntryRoots
              (major :: pre.reverse) fields rest)
            (OwnsVEnv rhsInput rest) := by
  dsimp only
  let dead : VEntry := .slot 0 0 .many false
  let fieldInput : VEnv :=
    ⟨List.replicate nf dead, (numArgs + 1) + nf⟩
  let retains := recursorFieldRetains (numArgs + 1) rhs nf
  let frame :=
    parameterEntries 0 (List.replicate numArgs .many)
        (fun i => countUses (nf + i) rhs) ++
      [.recSelf (numArgs + 1)]
  let drops :=
    (parameterDrops 0 (List.replicate numArgs .many)
        (fun i => countUses (nf + i) rhs)).map
      (SlotDrop.offsetEntry nf)
  obtain ⟨fieldOutput, fieldEmit, hfieldPlan⟩ :=
    recursorFieldRetains_plan (numArgs + 1) ((numArgs + 1) + nf) nf rhs
  have hfieldEntriesLength : fieldOutput.entries.length = nf := by
    calc
      fieldOutput.entries.length =
          (⟨List.replicate nf dead,
            (numArgs + 1) + nf⟩ : VEnv).entries.length :=
        hfieldPlan.entries_length
      _ = nf := by simp
  obtain ⟨rhsInput, parameterEmit, hparameterPlan⟩ :=
    recursorParameterDrops_releasePlan numArgs nf
      (fieldOutput.depth + 1) rhs fieldOutput.entries
      hfieldEntriesLength
  refine ⟨fieldOutput, fieldEmit, rhsInput, parameterEmit,
    ?_, ?_, ?_⟩
  · simpa [fieldInput, retains, dead] using hfieldPlan.run
  · simpa [frame, drops, List.append_assoc] using
      hparameterPlan.run state
  · intro pre major fields rest hpreLength hfields
    have hfieldsLength : fields.toList.length = nf := by
      simpa using hfields
    have hcoveredBase := recursorFieldRetains_covered
      (numArgs + 1) nf rhs fields.toList hfieldsLength
    have hcovered : FieldRetainsCovered
        (recursorFieldRetains (numArgs + 1) rhs nf)
        (recursorEntrySlots numArgs major fields) fields.toList := by
      intro retain hmem
      obtain ⟨value, hslot, hborrowed⟩ :=
        hcoveredBase retain hmem
      exact ⟨value, by
        simp [recursorEntrySlots, recursorFieldSlots, hslot], hborrowed⟩
    have hentry := recursorAltEntry_borrowed
      (ctx := ctx) (cur := cur) numArgs nf rhs pre major fields
      hpreLength hfields rest
    have hfieldFramed := hfieldPlan.frameEntries frame
    have hfield : EmitSound ctx cur fieldEmit
        (OwnsVEnvBorrowed (recursorInitialVEnv numArgs nf rhs)
          (⟨.shared, major⟩ :: rest)
          (recursorEntrySlots numArgs major fields) fields.toList)
        (OwnsVEnvBorrowed (frameVEnvEntries fieldOutput frame)
          (⟨.shared, major⟩ :: rest)
          (recursorEntrySlots numArgs major fields) fields.toList) := by
      have hsound := hfieldFramed.sound (ctx := ctx) (cur := cur)
        (recursorEntrySlots numArgs major fields) fields.toList
        hcovered (⟨.shared, major⟩ :: rest)
      simpa [fieldInput, retains, frame, dead, recursorInitialVEnv,
        frameVEnvEntries, List.append_assoc] using hsound
    have hmajor : EmitSound ctx cur
        (emitOp (.drop (.var
          ((frameVEnvEntries fieldOutput frame).rel numArgs))))
        (OwnsVEnvBorrowed (frameVEnvEntries fieldOutput frame)
          (⟨.shared, major⟩ :: rest)
          (recursorEntrySlots numArgs major fields) fields.toList)
        (OwnsVEnvProtected (frameVEnvEntries fieldOutput frame).bump
          rest (recursorEntrySlots numArgs major fields)) :=
      drop_major_owned (by
        simp [recursorEntrySlots, recursorFieldSlots])
    have hparameters : EmitSound ctx cur parameterEmit
        (OwnsVEnvProtected (frameVEnvEntries fieldOutput frame).bump
          rest (recursorEntrySlots numArgs major fields))
        (OwnsVEnvProtected rhsInput rest
          (recursorEntrySlots numArgs major fields)) := by
      have hsound := hparameterPlan.sound (ctx := ctx) (cur := cur) rest
        (recursorEntrySlots numArgs major fields)
      simpa [frameVEnvEntries, VEnv.bump, frame, List.append_assoc]
        using hsound
    have hforget : EmitSound ctx cur (_root_.id : Emit)
        (OwnsVEnvProtected rhsInput rest
          (recursorEntrySlots numArgs major fields))
        (OwnsVEnv rhsInput rest) :=
      EmitSound.strengthen (fun h => h.1)
    have hcomposed := EmitSound.comp hentry
      (EmitSound.comp hfield
        (EmitSound.comp hmajor
          (EmitSound.comp hparameters hforget)))
    simpa [frameVEnvEntries, VEnv.rel, Function.comp_def] using hcomposed

/-- Fuel-bounded end-to-end certificate for the generated recursor prefix.
All prefix operations are call-free; the hereditary bound is carried solely
to compose with the recursively proved rule body. -/
theorem recursorPrefix_generated_verified_below
    {ctx : Ctx} {cur : FnDef} (limit numArgs nf : Nat)
    (rhs : IxIR0.Expr) (state : LowSt) :
    let dead : VEntry := .slot 0 0 .many false
    let fieldInput : VEnv :=
      ⟨List.replicate nf dead, (numArgs + 1) + nf⟩
    let retains := recursorFieldRetains (numArgs + 1) rhs nf
    let frame :=
      parameterEntries 0 (List.replicate numArgs .many)
          (fun i => countUses (nf + i) rhs) ++
        [.recSelf (numArgs + 1)]
    let drops :=
      (parameterDrops 0 (List.replicate numArgs .many)
          (fun i => countUses (nf + i) rhs)).map
        (SlotDrop.offsetEntry nf)
    ∃ fieldOutput fieldEmit rhsInput parameterEmit,
      applyRecursorFieldRetains fieldInput retains =
        (fieldOutput, fieldEmit) ∧
      (releaseSlots
          ⟨fieldOutput.entries ++ frame, fieldOutput.depth + 1⟩
          drops).run state = .ok (rhsInput, parameterEmit) state ∧
      ∀ {pre : List RVal} {major : RVal} {fields : Array RVal}
          {rest : List Root},
        pre.length = numArgs → fields.size = nf →
          EmitSoundBelow ctx cur limit
            (fieldEmit ∘
              emitOp (.drop (.var (fieldOutput.rel numArgs))) ∘
              parameterEmit)
            (OwnsAltEntry .shared recursorEntryRoots
              (major :: pre.reverse) fields rest)
            (OwnsVEnv rhsInput rest) := by
  dsimp only
  let dead : VEntry := .slot 0 0 .many false
  let fieldInput : VEnv :=
    ⟨List.replicate nf dead, (numArgs + 1) + nf⟩
  let retains := recursorFieldRetains (numArgs + 1) rhs nf
  let frame :=
    parameterEntries 0 (List.replicate numArgs .many)
        (fun i => countUses (nf + i) rhs) ++
      [.recSelf (numArgs + 1)]
  let drops :=
    (parameterDrops 0 (List.replicate numArgs .many)
        (fun i => countUses (nf + i) rhs)).map
      (SlotDrop.offsetEntry nf)
  obtain ⟨fieldOutput, fieldEmit, hfieldPlan⟩ :=
    recursorFieldRetains_plan (numArgs + 1) ((numArgs + 1) + nf) nf rhs
  have hfieldEntriesLength : fieldOutput.entries.length = nf := by
    calc
      fieldOutput.entries.length =
          (⟨List.replicate nf dead,
            (numArgs + 1) + nf⟩ : VEnv).entries.length :=
        hfieldPlan.entries_length
      _ = nf := by simp
  obtain ⟨rhsInput, parameterEmit, hparameterPlan⟩ :=
    recursorParameterDrops_releasePlan numArgs nf
      (fieldOutput.depth + 1) rhs fieldOutput.entries
      hfieldEntriesLength
  refine ⟨fieldOutput, fieldEmit, rhsInput, parameterEmit,
    ?_, ?_, ?_⟩
  · simpa [fieldInput, retains, dead] using hfieldPlan.run
  · simpa [frame, drops, List.append_assoc] using
      hparameterPlan.run state
  · intro pre major fields rest hpreLength hfields
    have hfieldsLength : fields.toList.length = nf := by
      simpa using hfields
    have hcoveredBase := recursorFieldRetains_covered
      (numArgs + 1) nf rhs fields.toList hfieldsLength
    have hcovered : FieldRetainsCovered
        (recursorFieldRetains (numArgs + 1) rhs nf)
        (recursorEntrySlots numArgs major fields) fields.toList := by
      intro retain hmem
      obtain ⟨value, hslot, hborrowed⟩ :=
        hcoveredBase retain hmem
      exact ⟨value, by
        simp [recursorEntrySlots, recursorFieldSlots, hslot], hborrowed⟩
    have hentry := recursorAltEntry_borrowed_below
      (ctx := ctx) (cur := cur) (limit := limit)
      numArgs nf rhs pre major fields hpreLength hfields rest
    have hfieldFramed := hfieldPlan.frameEntries frame
    have hfield : EmitSoundBelow ctx cur limit fieldEmit
        (OwnsVEnvBorrowed (recursorInitialVEnv numArgs nf rhs)
          (⟨.shared, major⟩ :: rest)
          (recursorEntrySlots numArgs major fields) fields.toList)
        (OwnsVEnvBorrowed (frameVEnvEntries fieldOutput frame)
          (⟨.shared, major⟩ :: rest)
          (recursorEntrySlots numArgs major fields) fields.toList) := by
      have hsound := hfieldFramed.soundBelow
        (ctx := ctx) (cur := cur) (limit := limit)
        (recursorEntrySlots numArgs major fields) fields.toList
        hcovered (⟨.shared, major⟩ :: rest)
      simpa [fieldInput, retains, frame, dead, recursorInitialVEnv,
        frameVEnvEntries, List.append_assoc] using hsound
    have hmajor : EmitSoundBelow ctx cur limit
        (emitOp (.drop (.var
          ((frameVEnvEntries fieldOutput frame).rel numArgs))))
        (OwnsVEnvBorrowed (frameVEnvEntries fieldOutput frame)
          (⟨.shared, major⟩ :: rest)
          (recursorEntrySlots numArgs major fields) fields.toList)
        (OwnsVEnvProtected (frameVEnvEntries fieldOutput frame).bump
          rest (recursorEntrySlots numArgs major fields)) :=
      drop_major_owned_below (limit := limit) (by
        simp [recursorEntrySlots, recursorFieldSlots])
    have hparameters : EmitSoundBelow ctx cur limit parameterEmit
        (OwnsVEnvProtected (frameVEnvEntries fieldOutput frame).bump
          rest (recursorEntrySlots numArgs major fields))
        (OwnsVEnvProtected rhsInput rest
          (recursorEntrySlots numArgs major fields)) := by
      have hsound := hparameterPlan.soundBelow
        (ctx := ctx) (cur := cur) (limit := limit) rest
        (recursorEntrySlots numArgs major fields)
      simpa [frameVEnvEntries, VEnv.bump, frame, List.append_assoc]
        using hsound
    have hforget : EmitSoundBelow ctx cur limit (_root_.id : Emit)
        (OwnsVEnvProtected rhsInput rest
          (recursorEntrySlots numArgs major fields))
        (OwnsVEnv rhsInput rest) :=
      EmitSoundBelow.strengthen (fun h => h.1)
    have hcomposed := EmitSoundBelow.comp hentry
      (EmitSoundBelow.comp hfield
        (EmitSoundBelow.comp hmajor
          (EmitSoundBelow.comp hparameters hforget)))
    simpa [frameVEnvEntries, VEnv.rel, Function.comp_def] using hcomposed

/-- When the lowered body starts directly at branch entry, an entry-layout
realization turns the case predicate into the ordinary `OwnsVEnv` predicate
used by expression lowering. -/
theorem AltEntryRealizes.emitId {ctx : Ctx} {cur : FnDef}
    {input : VEnv} {fieldCount : Nat}
    {fieldWorld : Owned}
    {entryValid : List RVal → Array RVal → Prop}
    {entryRoots : List RVal → Array RVal → List Root}
    (hentry : AltEntryRealizes input fieldCount entryValid entryRoots)
    {env : List RVal} {fields : Array RVal}
    (hsize : fields.size = fieldCount) (hvalid : entryValid env fields)
    (rest : List Root) :
    EmitSound ctx cur (_root_.id : Emit)
      (OwnsAltEntry fieldWorld entryRoots env fields rest)
      (OwnsVEnv input rest) := by
  apply EmitSound.strengthen
  intro store branchEnv hpre
  obtain ⟨henv, hown, _⟩ := hpre
  subst branchEnv
  obtain ⟨roots, hrealize, hperm⟩ := hentry hsize hvalid
  refine ⟨roots, hrealize, ?_⟩
  exact hown.perm (hperm.symm.append_right rest)

/-- Fuel-bounded entry-layout adapter. -/
theorem AltEntryRealizes.emitIdBelow {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {input : VEnv} {fieldCount : Nat}
    {fieldWorld : Owned}
    {entryValid : List RVal → Array RVal → Prop}
    {entryRoots : List RVal → Array RVal → List Root}
    (hentry : AltEntryRealizes input fieldCount entryValid entryRoots)
    {env : List RVal} {fields : Array RVal}
    (hsize : fields.size = fieldCount) (hvalid : entryValid env fields)
    (rest : List Root) :
    EmitSoundBelow ctx cur limit (_root_.id : Emit)
      (OwnsAltEntry fieldWorld entryRoots env fields rest)
      (OwnsVEnv input rest) := by
  apply EmitSoundBelow.strengthen
  intro store branchEnv hpre
  obtain ⟨henv, hown, _⟩ := hpre
  subst branchEnv
  obtain ⟨roots, hrealize, hperm⟩ := hentry hsize hvalid
  refine ⟨roots, hrealize, ?_⟩
  exact hown.perm (hperm.symm.append_right rest)

/-- Close a lowered alternative body behind its case-entry prefix. This is
the branch analogue of `LowerResultSound.fnOwnershipContract`: the prefix
may retain borrowed fields and release the scrutinee/dead parameters before
the ordinary expression proof begins. -/
theorem LowerResultSound.altOwnershipContractWithPrefix
    {ctx : Ctx} {cur : FnDef} {input output : VEnv}
    {fieldWorld : Owned} {entryValid : List RVal → Array RVal → Prop}
    {entryRoots : List RVal → Array RVal → List Root}
    {entryEmit emit : Emit} {av : AVal} {tag fieldCount : Nat}
    (hsound : LowerResultSound ctx cur input output cur.result emit av)
    (hprefix : ∀ {env : List RVal} {fields : Array RVal}
        {rest : List Root},
      fields.size = fieldCount → entryValid env fields →
        EmitSound ctx cur entryEmit
          (OwnsAltEntry fieldWorld entryRoots env fields rest)
          (OwnsVEnv input rest))
    (hreleased : EntriesReleased output.entries) :
    AltOwnershipContract ctx cur
      (.mk tag fieldCount (entryEmit (emit (.ret (av.toAtom output)))))
      fieldWorld entryValid entryRoots := by
  refine ⟨?_⟩
  intro fuel store store' env fields value rest hsize hvalid hown
    hborrow hrun
  exact (hprefix hsize hvalid _ _ (hsound.close hreleased rest))
    ⟨rfl, hown, hborrow⟩ hrun

/-- Prefix-free specialization for alternatives whose entry layout already
matches the input `VEnv`. -/
theorem LowerResultSound.altOwnershipContract
    {ctx : Ctx} {cur : FnDef} {input output : VEnv}
    {fieldWorld : Owned} {entryValid : List RVal → Array RVal → Prop}
    {entryRoots : List RVal → Array RVal → List Root}
    {emit : Emit} {av : AVal} {tag fieldCount : Nat}
    (hsound : LowerResultSound ctx cur input output cur.result emit av)
    (hentry : AltEntryRealizes input fieldCount entryValid entryRoots)
    (hreleased : EntriesReleased output.entries) :
    AltOwnershipContract ctx cur
      (.mk tag fieldCount (emit (.ret (av.toAtom output))))
      fieldWorld entryValid entryRoots := by
  simpa using hsound.altOwnershipContractWithPrefix
    (entryEmit := (_root_.id : Emit))
    (fun hsize hvalid => hentry.emitId hsize hvalid _) hreleased

/-- Close a bounded lowered alternative behind a bounded generated prefix. -/
theorem LowerResultSoundBelow.altOwnershipContractWithPrefix
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {input output : VEnv}
    {fieldWorld : Owned} {entryValid : List RVal → Array RVal → Prop}
    {entryRoots : List RVal → Array RVal → List Root}
    {entryEmit emit : Emit} {av : AVal} {tag fieldCount : Nat}
    (hsound : LowerResultSoundBelow ctx cur limit input output
      cur.result emit av)
    (hprefix : ∀ {env : List RVal} {fields : Array RVal}
        {rest : List Root},
      fields.size = fieldCount → entryValid env fields →
        EmitSoundBelow ctx cur limit entryEmit
          (OwnsAltEntry fieldWorld entryRoots env fields rest)
          (OwnsVEnv input rest))
    (hreleased : EntriesReleased output.entries) :
    AltOwnershipContractBelow ctx cur
      (.mk tag fieldCount (entryEmit (emit (.ret (av.toAtom output)))))
      fieldWorld entryValid entryRoots limit := by
  refine ⟨?_⟩
  intro fuel store store' env fields value rest hfuel hsize hvalid hown
    hborrow hrun
  have hcode : CodeOwnsBelow ctx cur limit
      (OwnsAltEntry fieldWorld entryRoots env fields rest)
      (fun store value =>
        RootOwnership store (⟨cur.result, value⟩ :: rest))
      (entryEmit (emit (.ret (av.toAtom output)))) :=
    hprefix hsize hvalid limit (Nat.le_refl _) _ _
      (hsound.close hreleased rest)
  exact hcode (Nat.le_of_lt hfuel) ⟨rfl, hown, hborrow⟩ hrun

/-- Prefix-free bounded alternative specialization. -/
theorem LowerResultSoundBelow.altOwnershipContract
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {input output : VEnv}
    {fieldWorld : Owned} {entryValid : List RVal → Array RVal → Prop}
    {entryRoots : List RVal → Array RVal → List Root}
    {emit : Emit} {av : AVal} {tag fieldCount : Nat}
    (hsound : LowerResultSoundBelow ctx cur limit input output
      cur.result emit av)
    (hentry : AltEntryRealizes input fieldCount entryValid entryRoots)
    (hreleased : EntriesReleased output.entries) :
    AltOwnershipContractBelow ctx cur
      (.mk tag fieldCount (emit (.ret (av.toAtom output))))
      fieldWorld entryValid entryRoots limit := by
  simpa using hsound.altOwnershipContractWithPrefix
    (entryEmit := (_root_.id : Emit))
    (fun hsize hvalid => hentry.emitIdBelow hsize hvalid _) hreleased

/-- Recursive compiler premise for one recursor-rule RHS, stated against the
actual field-retain and parameter-release results consumed by
`lowerRecursorRule`. -/
def RecursorRuleBodySound (ctx : Ctx) (cur : FnDef) (src : IxIR0.Env)
    (fuel numArgs : Nat) (rule : IxIR0.RecRule) (state : LowSt) : Prop :=
  ∀ {fieldOutput : VEnv} {fieldEmit : Emit}
      {rhsInput : VEnv} {parameterEmit : Emit},
    applyRecursorFieldRetains
        ⟨List.replicate rule.fields (.slot 0 0 .many false),
          (numArgs + 1) + rule.fields⟩
        (recursorFieldRetains (numArgs + 1) rule.rhs rule.fields) =
      (fieldOutput, fieldEmit) →
    (releaseSlots
        ⟨fieldOutput.entries ++
            parameterEntries 0 (List.replicate numArgs .many)
              (fun i => countUses (rule.fields + i) rule.rhs) ++
            [.recSelf (numArgs + 1)],
          fieldOutput.depth + 1⟩
        ((parameterDrops 0 (List.replicate numArgs .many)
            (fun i => countUses (rule.fields + i) rule.rhs)).map
          (SlotDrop.offsetEntry rule.fields))).run state =
      .ok (rhsInput, parameterEmit) state →
    ∃ output bodyEmit av finalState,
      (lowerE src fuel rhsInput .shared rule.rhs).run state =
        .ok (output, bodyEmit, av) finalState ∧
      LowerResultSound ctx cur rhsInput output .shared bodyEmit av ∧
      EntriesReleased output.entries

/-- Fuel-bounded recursive compiler premise for one recursor-rule RHS. -/
def RecursorRuleBodySoundBelow (ctx : Ctx) (cur : FnDef)
    (limit : Nat) (src : IxIR0.Env) (fuel numArgs : Nat)
    (rule : IxIR0.RecRule) (state : LowSt) : Prop :=
  ∀ {fieldOutput : VEnv} {fieldEmit : Emit}
      {rhsInput : VEnv} {parameterEmit : Emit},
    applyRecursorFieldRetains
        ⟨List.replicate rule.fields (.slot 0 0 .many false),
          (numArgs + 1) + rule.fields⟩
        (recursorFieldRetains (numArgs + 1) rule.rhs rule.fields) =
      (fieldOutput, fieldEmit) →
    (releaseSlots
        ⟨fieldOutput.entries ++
            parameterEntries 0 (List.replicate numArgs .many)
              (fun i => countUses (rule.fields + i) rule.rhs) ++
            [.recSelf (numArgs + 1)],
          fieldOutput.depth + 1⟩
        ((parameterDrops 0 (List.replicate numArgs .many)
            (fun i => countUses (rule.fields + i) rule.rhs)).map
          (SlotDrop.offsetEntry rule.fields))).run state =
      .ok (rhsInput, parameterEmit) state →
    ∃ output bodyEmit av finalState,
      (lowerE src fuel rhsInput .shared rule.rhs).run state =
        .ok (output, bodyEmit, av) finalState ∧
      LowerResultSoundBelow ctx cur limit rhsInput output .shared
        bodyEmit av ∧
      EntriesReleased output.entries

/-- Bounded ownership transformer for the exact generated retain/major/
parameter prefix of one recursor rule. -/
def RecursorRulePrefixSoundBelow (ctx : Ctx) (cur : FnDef)
    (limit numArgs : Nat) (rule : IxIR0.RecRule) (state : LowSt) : Prop :=
  ∀ {fieldOutput : VEnv} {fieldEmit : Emit}
      {rhsInput : VEnv} {parameterEmit : Emit},
    applyRecursorFieldRetains
        ⟨List.replicate rule.fields (.slot 0 0 .many false),
          (numArgs + 1) + rule.fields⟩
        (recursorFieldRetains (numArgs + 1) rule.rhs rule.fields) =
      (fieldOutput, fieldEmit) →
    (releaseSlots
        ⟨fieldOutput.entries ++
            parameterEntries 0 (List.replicate numArgs .many)
              (fun i => countUses (rule.fields + i) rule.rhs) ++
            [.recSelf (numArgs + 1)],
          fieldOutput.depth + 1⟩
        ((parameterDrops 0 (List.replicate numArgs .many)
            (fun i => countUses (rule.fields + i) rule.rhs)).map
          (SlotDrop.offsetEntry rule.fields))).run state =
      .ok (rhsInput, parameterEmit) state →
    ∀ {pre : List RVal} {major : RVal} {fields : Array RVal}
        {rest : List Root},
      pre.length = numArgs → fields.size = rule.fields →
        EmitSoundBelow ctx cur limit
          (fieldEmit ∘
            emitOp (.drop (.var (fieldOutput.rel numArgs))) ∘
            parameterEmit)
          (OwnsAltEntry .shared recursorEntryRoots
            (major :: pre.reverse) fields rest)
          (OwnsVEnv rhsInput rest)

/-- The executable retain/release prefix itself supplies the bounded prefix
premise; callers need only identify its deterministic interpreter results. -/
theorem recursorRulePrefixSound_generated_below
    {ctx : Ctx} {cur : FnDef} (limit numArgs : Nat)
    (rule : IxIR0.RecRule) (state : LowSt) :
    RecursorRulePrefixSoundBelow ctx cur limit numArgs rule state := by
  intro fieldOutput fieldEmit rhsInput parameterEmit
    hfieldRun hparameterRun
  intro pre major fields rest hpreLength hfields
  obtain ⟨generatedFieldOutput, generatedFieldEmit,
      generatedRhsInput, generatedParameterEmit,
      generatedFieldRun, generatedParameterRun, hsound⟩ :=
    recursorPrefix_generated_verified_below (ctx := ctx) (cur := cur)
      limit numArgs rule.fields rule.rhs state
  have hfieldEq :
      (fieldOutput, fieldEmit) =
        (generatedFieldOutput, generatedFieldEmit) :=
    hfieldRun.symm.trans generatedFieldRun
  cases hfieldEq
  simp only [List.append_assoc] at hparameterRun
  have hparameterResultEq :=
    hparameterRun.symm.trans generatedParameterRun
  have hparameterEq :
      (rhsInput, parameterEmit) =
        (generatedRhsInput, generatedParameterEmit) := by
    simpa using hparameterResultEq
  cases hparameterEq
  exact hsound hpreLength hfields

/-- The executable lowering of one arbitrary recursor rule produces an
alternative satisfying the generic public entry contract. -/
theorem lowerRecursorRule_generated_verified {ctx : Ctx} {cur : FnDef}
    (hresult : cur.result = .shared)
    (src : IxIR0.Env) (fuel numArgs : Nat) (rule : IxIR0.RecRule)
    (tag : Nat) (state : LowSt)
    (hbody : RecursorRuleBodySound ctx cur src fuel numArgs rule state) :
    ∃ finalState alt,
      (lowerRecursorRule src fuel numArgs (rule, tag)).run state =
        .ok alt finalState ∧
      AltOwnershipContract ctx cur alt .shared
        (RecursorEntryValid numArgs) recursorEntryRoots := by
  obtain ⟨fieldOutput, fieldEmit, rhsInput, parameterEmit,
      hfieldRun, hparameterRun, hprefix⟩ :=
    recursorPrefix_generated_verified (ctx := ctx) (cur := cur)
      numArgs rule.fields rule.rhs state
  obtain ⟨output, bodyEmit, av, finalState,
      hbodyRun, hsound, hreleased⟩ :=
    hbody hfieldRun (by
      simpa [List.append_assoc] using hparameterRun)
  let alt : Alt :=
    .mk tag rule.fields
      (fieldEmit
        (emitOp (.drop (.var (fieldOutput.rel numArgs)))
          (parameterEmit (bodyEmit (.ret (av.toAtom output))))))
  refine ⟨finalState, alt, ?_, ?_⟩
  · simp only [lowerRecursorRule]
    rw [hfieldRun]
    simp only
    rw [estateBindRun]
    simp only [VEnv.bump, List.append_assoc]
    rw [hparameterRun]
    simp only
    rw [estateBindRun, hbodyRun]
    rfl
  · have hsoundCur : LowerResultSound ctx cur rhsInput output
        cur.result bodyEmit av := by
      simpa [hresult] using hsound
    have hprefixValid : ∀ {env : List RVal} {fields : Array RVal}
        {rest : List Root},
      fields.size = rule.fields → RecursorEntryValid numArgs env fields →
        EmitSound ctx cur
          (fieldEmit ∘
            emitOp (.drop (.var (fieldOutput.rel numArgs))) ∘
            parameterEmit)
          (OwnsAltEntry .shared recursorEntryRoots env fields rest)
          (OwnsVEnv rhsInput rest) := by
      intro env fields rest hfields hvalid
      obtain ⟨pre, major, hpreLength, rfl⟩ := hvalid
      exact hprefix hpreLength hfields
    have hcontract := hsoundCur.altOwnershipContractWithPrefix
      (fieldWorld := .shared)
      (entryValid := RecursorEntryValid numArgs)
      (entryRoots := recursorEntryRoots)
      (entryEmit := fieldEmit ∘
        emitOp (.drop (.var (fieldOutput.rel numArgs))) ∘ parameterEmit)
      (tag := tag) (fieldCount := rule.fields) hprefixValid hreleased
    simpa [alt, Function.comp_def] using hcontract

/-- Exact-fuel version of `lowerRecursorRule_generated_verified`. The
recursive RHS and the generated prefix both carry only bounded Hoare proofs,
and the produced alternative is correspondingly bounded. -/
theorem lowerRecursorRule_generated_verified_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat}
    (hresult : cur.result = .shared)
    (src : IxIR0.Env) (fuel numArgs : Nat) (rule : IxIR0.RecRule)
    (tag : Nat) (state : LowSt)
    (hbody : RecursorRuleBodySoundBelow ctx cur limit src fuel numArgs
      rule state) :
    ∃ finalState alt,
      (lowerRecursorRule src fuel numArgs (rule, tag)).run state =
        .ok alt finalState ∧
      AltOwnershipContractBelow ctx cur alt .shared
        (RecursorEntryValid numArgs) recursorEntryRoots limit := by
  obtain ⟨fieldOutput, fieldEmit, rhsInput, parameterEmit,
      hfieldRun, hparameterRun, hprefix⟩ :=
    recursorPrefix_generated_verified_below (ctx := ctx) (cur := cur)
      limit numArgs rule.fields rule.rhs state
  have hparameterRun' :
      (releaseSlots
        ⟨fieldOutput.entries ++
            parameterEntries 0 (List.replicate numArgs .many)
              (fun i => countUses (rule.fields + i) rule.rhs) ++
            [.recSelf (numArgs + 1)],
          fieldOutput.depth + 1⟩
        ((parameterDrops 0 (List.replicate numArgs .many)
            (fun i => countUses (rule.fields + i) rule.rhs)).map
          (SlotDrop.offsetEntry rule.fields))).run state =
        .ok (rhsInput, parameterEmit) state := by
    simpa [List.append_assoc] using hparameterRun
  obtain ⟨output, bodyEmit, av, finalState,
      hbodyRun, hsound, hreleased⟩ :=
    hbody hfieldRun hparameterRun'
  let alt : Alt :=
    .mk tag rule.fields
      (fieldEmit
        (emitOp (.drop (.var (fieldOutput.rel numArgs)))
          (parameterEmit (bodyEmit (.ret (av.toAtom output))))))
  refine ⟨finalState, alt, ?_, ?_⟩
  · simp only [lowerRecursorRule]
    rw [hfieldRun]
    simp only
    rw [estateBindRun]
    simp only [VEnv.bump, List.append_assoc]
    rw [hparameterRun]
    simp only
    rw [estateBindRun, hbodyRun]
    rfl
  · have hsoundCur : LowerResultSoundBelow ctx cur limit rhsInput output
        cur.result bodyEmit av := by
      simpa [hresult] using hsound
    have hprefixValid : ∀ {env : List RVal} {fields : Array RVal}
        {rest : List Root},
      fields.size = rule.fields → RecursorEntryValid numArgs env fields →
        EmitSoundBelow ctx cur limit
          (fieldEmit ∘
            emitOp (.drop (.var (fieldOutput.rel numArgs))) ∘
            parameterEmit)
          (OwnsAltEntry .shared recursorEntryRoots env fields rest)
          (OwnsVEnv rhsInput rest) := by
      intro env fields rest hfields hvalid
      obtain ⟨pre, major, hpreLength, rfl⟩ := hvalid
      exact hprefix hpreLength hfields
    have hcontract := hsoundCur.altOwnershipContractWithPrefix
      (fieldWorld := .shared)
      (entryValid := RecursorEntryValid numArgs)
      (entryRoots := recursorEntryRoots)
      (entryEmit := fieldEmit ∘
        emitOp (.drop (.var (fieldOutput.rel numArgs))) ∘ parameterEmit)
      (tag := tag) (fieldCount := rule.fields) hprefixValid hreleased
    simpa [alt, Function.comp_def] using hcontract

/-- Proof-relevant state-threaded traversal of all indexed recursor rules.
It mirrors the executable `List.mapM` and records a contract for every
generated alternative. -/
inductive RecursorRulesPlan (ctx : Ctx) (cur : FnDef) (src : IxIR0.Env)
    (fuel numArgs : Nat) :
    LowSt → List (IxIR0.RecRule × Nat) → LowSt → List Alt → Prop where
  | nil (state : LowSt) :
      RecursorRulesPlan ctx cur src fuel numArgs state [] state []
  | cons {state middleState finalState : LowSt}
      {rule : IxIR0.RecRule} {tag : Nat}
      {rules : List (IxIR0.RecRule × Nat)} {alt : Alt} {alts : List Alt}
      (hhead : (lowerRecursorRule src fuel numArgs (rule, tag)).run state =
        .ok alt middleState)
      (hcontract : AltOwnershipContract ctx cur alt .shared
        (RecursorEntryValid numArgs) recursorEntryRoots)
      (tail : RecursorRulesPlan ctx cur src fuel numArgs
        middleState rules finalState alts) :
      RecursorRulesPlan ctx cur src fuel numArgs state
        ((rule, tag) :: rules) finalState (alt :: alts)

/-- A rule traversal computes the exact successful `mapM` result. -/
theorem RecursorRulesPlan.run {ctx : Ctx} {cur : FnDef}
    {src : IxIR0.Env} {fuel numArgs : Nat}
    {state finalState : LowSt} {rules : List (IxIR0.RecRule × Nat)}
    {alts : List Alt}
    (hplan : RecursorRulesPlan ctx cur src fuel numArgs
      state rules finalState alts) :
    (rules.mapM (lowerRecursorRule src fuel numArgs)).run state =
      .ok alts finalState := by
  induction hplan with
  | nil => rfl
  | cons hhead hcontract tail ih =>
    simp only [List.mapM_cons]
    rw [estateBindRun, hhead]
    simp only
    rw [estateBindRun, ih]
    rfl

/-- Every output of a rule traversal carries its alternative contract. -/
theorem RecursorRulesPlan.forall_mem {ctx : Ctx} {cur : FnDef}
    {src : IxIR0.Env} {fuel numArgs : Nat}
    {state finalState : LowSt} {rules : List (IxIR0.RecRule × Nat)}
    {alts : List Alt}
    (hplan : RecursorRulesPlan ctx cur src fuel numArgs
      state rules finalState alts) :
    ∀ alt ∈ alts,
      AltOwnershipContract ctx cur alt .shared
        (RecursorEntryValid numArgs) recursorEntryRoots := by
  induction hplan with
  | nil => simp
  | cons hhead hcontract tail ih =>
    intro selected hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | htail
    · exact hcontract
    · exact ih selected htail

/-- Ownership contracts for every alternative that the evaluator can select.
Indexing by the successful `Array.find?` equation mirrors `runCode` exactly
and avoids imposing a separate uniqueness or array-membership invariant. -/
def RecursorAltContracts (ctx : Ctx) (cur : FnDef) (numArgs : Nat)
    (alts : Array Alt) : Prop :=
  ∀ {cidx tag fieldCount : Nat} {body : Code},
    alts.find? (fun alt => alt.cidx == cidx) =
        some (.mk tag fieldCount body) →
      AltOwnershipContract ctx cur (.mk tag fieldCount body) .shared
        (RecursorEntryValid numArgs) recursorEntryRoots

/-- Pointwise contracts collect into the evaluator-selection-indexed bundle. -/
theorem RecursorAltContracts.of_forall_mem {ctx : Ctx} {cur : FnDef}
    {numArgs : Nat} {alts : Array Alt}
    (hall : ∀ alt ∈ alts,
      AltOwnershipContract ctx cur alt .shared
        (RecursorEntryValid numArgs) recursorEntryRoots) :
    RecursorAltContracts ctx cur numArgs alts := by
  intro cidx tag fieldCount body hfind
  exact hall (.mk tag fieldCount body)
    (Array.mem_of_find?_eq_some hfind)

/-- A completed rule traversal supplies the selection-indexed bundle used by
the `case` evaluator. -/
theorem RecursorRulesPlan.altContracts {ctx : Ctx} {cur : FnDef}
    {src : IxIR0.Env} {fuel numArgs : Nat}
    {state finalState : LowSt} {rules : List (IxIR0.RecRule × Nat)}
    {alts : List Alt}
    (hplan : RecursorRulesPlan ctx cur src fuel numArgs
      state rules finalState alts) :
    RecursorAltContracts ctx cur numArgs alts.toArray := by
  apply RecursorAltContracts.of_forall_mem
  intro alt hmem
  apply hplan.forall_mem alt
  simpa using hmem

/-- Selection-indexed alternative contracts available below one evaluator
fuel bound. -/
def RecursorAltContractsBelow (ctx : Ctx) (cur : FnDef)
    (numArgs : Nat) (alts : Array Alt) (limit : Nat) : Prop :=
  ∀ {cidx tag fieldCount : Nat} {body : Code},
    alts.find? (fun alt => alt.cidx == cidx) =
        some (.mk tag fieldCount body) →
      AltOwnershipContractBelow ctx cur (.mk tag fieldCount body) .shared
        (RecursorEntryValid numArgs) recursorEntryRoots limit

/-- Restrict a completed recursor alternative bundle to a fuel prefix. -/
theorem RecursorAltContracts.below {ctx : Ctx} {cur : FnDef}
    {numArgs : Nat} {alts : Array Alt}
    (hcontracts : RecursorAltContracts ctx cur numArgs alts)
    (limit : Nat) :
    RecursorAltContractsBelow ctx cur numArgs alts limit := by
  intro cidx tag fieldCount body hfind
  exact (hcontracts hfind).below limit

/-- Bounded recursor alternative bundles are contravariant in their bound. -/
theorem RecursorAltContractsBelow.mono {ctx : Ctx} {cur : FnDef}
    {numArgs : Nat} {alts : Array Alt} {smaller larger : Nat}
    (hcontracts : RecursorAltContractsBelow ctx cur numArgs alts larger)
    (hbound : smaller ≤ larger) :
    RecursorAltContractsBelow ctx cur numArgs alts smaller := by
  intro cidx tag fieldCount body hfind
  exact (hcontracts hfind).mono hbound

/-- State-threaded traversal of generated recursor rules carrying bounded
alternative contracts. -/
inductive RecursorRulesPlanBelow (ctx : Ctx) (cur : FnDef)
    (limit : Nat) (src : IxIR0.Env) (fuel numArgs : Nat) :
    LowSt → List (IxIR0.RecRule × Nat) → LowSt → List Alt → Prop where
  | nil (state : LowSt) :
      RecursorRulesPlanBelow ctx cur limit src fuel numArgs
        state [] state []
  | cons {state middleState finalState : LowSt}
      {rule : IxIR0.RecRule} {tag : Nat}
      {rules : List (IxIR0.RecRule × Nat)} {alt : Alt} {alts : List Alt}
      (hhead : (lowerRecursorRule src fuel numArgs (rule, tag)).run state =
        .ok alt middleState)
      (hcontract : AltOwnershipContractBelow ctx cur alt .shared
        (RecursorEntryValid numArgs) recursorEntryRoots limit)
      (tail : RecursorRulesPlanBelow ctx cur limit src fuel numArgs
        middleState rules finalState alts) :
      RecursorRulesPlanBelow ctx cur limit src fuel numArgs state
        ((rule, tag) :: rules) finalState (alt :: alts)

/-- A bounded rule traversal computes the same exact `mapM` result. -/
theorem RecursorRulesPlanBelow.run {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {src : IxIR0.Env} {fuel numArgs : Nat}
    {state finalState : LowSt} {rules : List (IxIR0.RecRule × Nat)}
    {alts : List Alt}
    (hplan : RecursorRulesPlanBelow ctx cur limit src fuel numArgs
      state rules finalState alts) :
    (rules.mapM (lowerRecursorRule src fuel numArgs)).run state =
      .ok alts finalState := by
  induction hplan with
  | nil => rfl
  | cons hhead hcontract tail ih =>
    simp only [List.mapM_cons]
    rw [estateBindRun, hhead]
    simp only
    rw [estateBindRun, ih]
    rfl

/-- Every result of a bounded traversal carries its bounded contract. -/
theorem RecursorRulesPlanBelow.forall_mem {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {src : IxIR0.Env} {fuel numArgs : Nat}
    {state finalState : LowSt} {rules : List (IxIR0.RecRule × Nat)}
    {alts : List Alt}
    (hplan : RecursorRulesPlanBelow ctx cur limit src fuel numArgs
      state rules finalState alts) :
    ∀ alt ∈ alts,
      AltOwnershipContractBelow ctx cur alt .shared
        (RecursorEntryValid numArgs) recursorEntryRoots limit := by
  induction hplan with
  | nil => simp
  | cons hhead hcontract tail ih =>
    intro selected hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | htail
    · exact hcontract
    · exact ih selected htail

/-- A bounded traversal supplies every selection-indexed alternative
contract used by the exact-fuel recursor collector. -/
theorem RecursorRulesPlanBelow.altContracts {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {src : IxIR0.Env} {fuel numArgs : Nat}
    {state finalState : LowSt} {rules : List (IxIR0.RecRule × Nat)}
    {alts : List Alt}
    (hplan : RecursorRulesPlanBelow ctx cur limit src fuel numArgs
      state rules finalState alts) :
    RecursorAltContractsBelow ctx cur numArgs alts.toArray limit := by
  intro cidx tag fieldCount body hfind
  apply hplan.forall_mem (.mk tag fieldCount body)
  simpa using Array.mem_of_find?_eq_some hfind

private theorem lowerSimExceptBindOk {error α β : Type} (value : α)
    (next : α → Except error β) :
    (Except.ok value >>= next) = next value := rfl

/-- At one exact evaluator index, bounded contracts for every selectable
alternative preserve the public all-shared recursor boundary. -/
theorem recursorFnOwnershipPreservesAt (ctx : Ctx) (numArgs : Nat)
    (natLit : Bool) (alts : Array Alt) (fuel : Nat) :
    let d : FnDef :=
      ⟨numArgs + 1, .shared, .case (.var 0) natLit alts⟩
    RecursorAltContractsBelow ctx d numArgs alts fuel →
      FnOwnershipPreservesAt ctx d
        (List.replicate (numArgs + 1) .shared) fuel := by
  dsimp only
  let d : FnDef :=
    ⟨numArgs + 1, .shared, .case (.var 0) natLit alts⟩
  intro hcontracts
  intro store store' args value rest hargsLength hown hrun
  have hargsArity : args.length = numArgs + 1 := by
    simpa using hargsLength
  have hrootShape :
      rootsForWorlds (List.replicate (numArgs + 1) .shared) args =
        rootsFor .shared args :=
    rootsForWorlds_replicate_eq_rootsFor .shared hargsArity
  rw [hrootShape] at hown
  cases fuel with
  | zero => simp [runCode] at hrun
  | succ branchFuel =>
    cases hreverse : args.reverse with
    | nil =>
      have hargsNil : args = [] := by
        have h := congrArg List.reverse hreverse
        simpa using h
      simp [hargsNil] at hargsArity
    | cons major runtimePre =>
      have hargsForm : args = runtimePre.reverse ++ [major] := by
        have h := congrArg List.reverse hreverse
        simpa [List.reverse_cons] using h
      have hruntimePreLength : runtimePre.length = numArgs := by
        rw [hargsForm] at hargsArity
        simp only [List.length_append, List.length_reverse,
          List.length_singleton] at hargsArity
        omega
      have hvalid (fields : Array RVal) :
          RecursorEntryValid numArgs (major :: runtimePre) fields := by
        exact ⟨runtimePre.reverse, major, by simpa using hruntimePreLength,
          by simp⟩
      have hentryOwn (fields : Array RVal) : RootOwnership store
          (recursorEntryRoots (major :: runtimePre) fields ++ rest) := by
        simpa [recursorEntryRoots, hargsForm, List.reverse_cons] using hown
      have hmajorWorld : HasWorld store .shared major := by
        apply hown.roots_world ⟨.shared, major⟩
        apply List.mem_append_left rest
        simp [rootsFor, hargsForm]
      rw [hreverse] at hrun
      change runCode ctx (branchFuel + 1) d store
          (major :: runtimePre) (.case (.var 0) natLit alts) =
        .ok (store', value) at hrun
      have hdispatch := hrun
      rw [runCode.eq_def] at hdispatch
      dsimp only at hdispatch
      rw [show resolveAtom (major :: runtimePre) (.var 0) = .ok major
        from rfl, lowerSimExceptBindOk] at hdispatch
      cases major with
      | erased => contradiction
      | lit literal =>
        cases literal with
        | str string => contradiction
        | nat n =>
          cases hpeel : natLit with
          | false => simp [hpeel] at hdispatch
          | true =>
            cases n with
            | zero =>
              cases halt : alts.find? (fun alt => alt.cidx == 0) with
              | none => simp [hpeel, halt] at hdispatch
              | some alt =>
                cases alt with
                | mk tag fieldCount body =>
                  cases fieldCount with
                  | zero =>
                    exact runCode_case_nat_zero_contract_owned_below
                      (ctx := ctx) (fuel := branchFuel) (cur := d)
                      (store := store) (store' := store')
                      (env := .lit (.nat 0) :: runtimePre)
                      (scrut := .var 0)
                      (alts := alts) (tag := tag) (body := body)
                      (value := value) (rest := rest)
                      (fieldWorld := .shared)
                      (entryValid := RecursorEntryValid numArgs)
                      (entryRoots := recursorEntryRoots)
                      rfl halt (hcontracts halt) (hvalid #[])
                      (hentryOwn #[]) (by simpa [hpeel] using hrun)
                  | succ fieldCount =>
                    simp [hpeel, halt] at hdispatch
            | succ n =>
              cases halt : alts.find? (fun alt => alt.cidx == 1) with
              | none => simp [hpeel, halt] at hdispatch
              | some alt =>
                cases alt with
                | mk tag fieldCount body =>
                  by_cases hfieldCount : fieldCount = 1
                  · subst fieldCount
                    exact runCode_case_nat_succ_contract_owned_below
                      (ctx := ctx) (fuel := branchFuel) (cur := d)
                      (store := store) (store' := store')
                      (env := .lit (.nat (n + 1)) :: runtimePre)
                      (scrut := .var 0)
                      (alts := alts) (n := n) (tag := tag) (body := body)
                      (value := value) (rest := rest)
                      (fieldWorld := .shared)
                      (entryValid := RecursorEntryValid numArgs)
                      (entryRoots := recursorEntryRoots)
                      rfl halt (hcontracts halt)
                      (hvalid #[.lit (.nat n)])
                      (hentryOwn #[.lit (.nat n)])
                      (by simpa [hpeel] using hrun)
                  · simp [hpeel, halt, hfieldCount] at hdispatch
      | loc loc =>
        obtain ⟨ownedBox, hownedBox, hownedWorld⟩ := hmajorWorld
        cases hget : store.get? loc with
        | none =>
          rw [hget] at hownedBox
          contradiction
        | some box =>
          rw [hget] at hownedBox
          have hboxEq : box = ownedBox := Option.some.inj hownedBox
          subst ownedBox
          cases box with
          | mk boxWorld rc node =>
            dsimp only [NodeBox.world] at hownedWorld
            subst boxWorld
            cases node with
            | papN fn arity papArgs =>
              simp [hget] at hdispatch
            | ctorN cid fields =>
              cases halt : alts.find?
                  (fun alt => alt.cidx == cid.cidx) with
              | none => simp [hget, halt] at hdispatch
              | some alt =>
                cases alt with
                | mk tag fieldCount body =>
                  by_cases hsize : fields.size = fieldCount
                  · exact runCode_case_ctor_contract_owned_below
                      (ctx := ctx) (fuel := branchFuel) (cur := d)
                      (store := store) (store' := store')
                      (env := .loc loc :: runtimePre) (scrut := .var 0)
                      (peelNat := natLit) (alts := alts) (loc := loc)
                      (rc := rc) (world := .shared) (cid := cid)
                      (fields := fields) (tag := tag)
                      (nf := fieldCount) (body := body) (value := value)
                      (rest := rest)
                      (entryValid := RecursorEntryValid numArgs)
                      (entryRoots := recursorEntryRoots)
                      rfl hget halt hsize (hcontracts halt)
                      (hvalid fields) (hentryOwn fields) hrun
                  · simp [hget, halt, hsize] at hdispatch

/-- Collecting completed contracts for every selectable alternative yields
the public unbounded recursor contract. The implementation now seals the
exact-fuel collector above, so recursive alternatives need only smaller-fuel
self contracts when constructed by the mutual compiler proof. -/
theorem recursorFnOwnershipContract (ctx : Ctx) (numArgs : Nat)
    (natLit : Bool) (alts : Array Alt) :
    let d : FnDef :=
      ⟨numArgs + 1, .shared, .case (.var 0) natLit alts⟩
    RecursorAltContracts ctx d numArgs alts →
      FnOwnershipContract ctx d
        (List.replicate (numArgs + 1) .shared) := by
  dsimp only
  let d : FnDef :=
    ⟨numArgs + 1, .shared, .case (.var 0) natLit alts⟩
  intro hcontracts
  apply fnOwnershipContract_of_below_step (by simp)
  intro limit _
  exact recursorFnOwnershipPreservesAt ctx numArgs natLit alts limit
    (hcontracts.below limit)

/-- Complete generated-recursors rule: an exact state-threaded traversal of
the compiler's indexed rule list yields both the executable `lowerRecursor`
result and its public `FnOwnershipContract`. -/
theorem lowerRecursor_generated_verified {ctx : Ctx}
    (src : IxIR0.Env) (fuel numArgs : Nat) (natLit : Bool)
    (rules : Array IxIR0.RecRule) (state finalState : LowSt)
    (alts : List Alt) (d : FnDef)
    (hd : d = ⟨numArgs + 1, .shared,
      .case (.var 0) natLit alts.toArray⟩)
    (hplan : RecursorRulesPlan ctx d src fuel numArgs state
      rules.toList.zipIdx finalState alts) :
    (lowerRecursor src fuel numArgs natLit rules).run state =
        .ok d finalState ∧
      FnOwnershipContract ctx d
        (List.replicate (numArgs + 1) .shared) := by
  subst d
  constructor
  · simp only [lowerRecursor]
    rw [estateBindRun, hplan.run]
    rfl
  · apply recursorFnOwnershipContract ctx numArgs natLit alts.toArray
    exact hplan.altContracts

/-- Exact-fuel generated-recursors rule. A bounded state-threaded rule plan
produces both the executable recursor and its one-index ownership theorem;
`compilerContracts_of_below_step` later seals these results globally. -/
theorem lowerRecursor_generated_verified_below {ctx : Ctx}
    (limit : Nat) (src : IxIR0.Env) (fuel numArgs : Nat) (natLit : Bool)
    (rules : Array IxIR0.RecRule) (state finalState : LowSt)
    (alts : List Alt) (d : FnDef)
    (hd : d = ⟨numArgs + 1, .shared,
      .case (.var 0) natLit alts.toArray⟩)
    (hplan : RecursorRulesPlanBelow ctx d limit src fuel numArgs state
      rules.toList.zipIdx finalState alts) :
    (lowerRecursor src fuel numArgs natLit rules).run state =
        .ok d finalState ∧
      FnOwnershipPreservesAt ctx d
        (List.replicate (numArgs + 1) .shared) limit := by
  subst d
  constructor
  · simp only [lowerRecursor]
    rw [estateBindRun, hplan.run]
    rfl
  · exact recursorFnOwnershipPreservesAt ctx numArgs natLit
      alts.toArray limit hplan.altContracts

/-! ## Source/target declaration-contract environment -/

/-- The callable target signature determined by a source declaration.
Constructors lower directly at use sites and externs remain target externs,
so only definitions and recursors contribute function contracts. -/
def sourceCallableSignature : IxIR0.Decl →
    Option (List Owned × Owned)
  | .defn result body =>
      some ((lamUses body).map worldOfUses, result)
  | .recursor numArgs _ _ =>
      some (List.replicate (numArgs + 1) .shared, .shared)
  | .ctor _ _ | .extern _ => none

/-- Callable source branches of `lowerDecl` always emit a function at the
same address; constructors and externs have no source callable signature. -/
theorem lowerDecl_output_fn_of_callable
    {src : IxIR0.Env} {fuel : Nat} {address : Ixon.Address}
    {source : IxIR0.Decl} {worlds : List Owned}
    {resultWorld : Owned} {initial final : LowSt}
    {output : Option (Ixon.Address × Decl)}
    (hsignature : sourceCallableSignature source =
      some (worlds, resultWorld))
    (hrun : (lowerDecl src fuel (address, source)).run initial =
      .ok output final) :
    ∃ d, output = some (address, .fn d) := by
  cases source with
  | defn result body =>
    simp only [lowerDecl] at hrun
    obtain ⟨code, bodyState, hbodyRun, hpureRun⟩ :=
      estateBindRun_ok_inv hrun
    have hpure : some (address, Decl.fn
        ⟨lamArity body, result, code⟩) = output ∧
        bodyState = final := by
      simpa using hpureRun
    exact ⟨⟨lamArity body, result, code⟩, hpure.1.symm⟩
  | ctor tag arity => simp [sourceCallableSignature] at hsignature
  | recursor numArgs natLit rules =>
    simp only [lowerDecl] at hrun
    obtain ⟨d, recursorState, hrecursorRun, hpureRun⟩ :=
      estateBindRun_ok_inv hrun
    have hpure : some (address, Decl.fn d) = output ∧
        recursorState = final := by
      simpa using hpureRun
    exact ⟨d, hpure.1.symm⟩
  | extern arity => simp [sourceCallableSignature] at hsignature

/-- Fuel-independent correspondence between the source declaration map and
the target context. The semantic contract is kept separate so all functions
can be closed simultaneously by evaluator-fuel induction. -/
structure SourceDeclLayout (src : IxIR0.Env) (ctx : Ctx) : Prop where
  fn : ∀ {address source worlds result},
    src address = some source →
    sourceCallableSignature source = some (worlds, result) →
    ∃ d, ctx.decls address = some (.fn d) ∧
      d.arity = worlds.length ∧ d.result = result
  extern : ∀ {address arity},
    src address = some (.extern arity) →
    ctx.decls address = some (.extern arity)

/-- Pointwise ownership preservation of every source-backed target function
at one exact evaluator-fuel index. -/
def SourceFnPreservesAt (src : IxIR0.Env) (ctx : Ctx)
    (fuel : Nat) : Prop :=
  ∀ {address source worlds result d},
    src address = some source →
    sourceCallableSignature source = some (worlds, result) →
    ctx.decls address = some (.fn d) →
    FnOwnershipPreservesAt ctx d worlds fuel

/-- The declaration environment's contracts restricted to evaluator indices
strictly below `limit`. This is the mutual-call induction hypothesis used
while proving every function at the exact index `limit`. -/
structure SourceDeclContractsBelow (src : IxIR0.Env) (ctx : Ctx)
    (limit : Nat) extends SourceDeclLayout src ctx where
  fn_preserves : ∀ {fuel}, fuel < limit →
    SourceFnPreservesAt src ctx fuel

/-- Public, unbounded ownership contracts for every source-backed target
function, together with exact declaration-layout correspondence. -/
structure SourceDeclContracts (src : IxIR0.Env) (ctx : Ctx)
    extends SourceDeclLayout src ctx where
  fn_contract : ∀ {address source worlds result d},
    src address = some source →
    sourceCallableSignature source = some (worlds, result) →
    ctx.decls address = some (.fn d) →
    FnOwnershipContract ctx d worlds

/-- Restrict a completed declaration environment to a fuel prefix. -/
theorem SourceDeclContracts.below {src : IxIR0.Env} {ctx : Ctx}
    (hcontracts : SourceDeclContracts src ctx) (limit : Nat) :
    SourceDeclContractsBelow src ctx limit := by
  refine { toSourceDeclLayout := hcontracts.toSourceDeclLayout, fn_preserves := ?_ }
  intro fuel _ address source worlds result d hsrc hsignature hdecl
  exact (hcontracts.fn_contract hsrc hsignature hdecl).preserves

/-- Fuel-prefix declaration environments are contravariant in the bound. -/
theorem SourceDeclContractsBelow.mono {src : IxIR0.Env} {ctx : Ctx}
    {smaller larger : Nat}
    (hcontracts : SourceDeclContractsBelow src ctx larger)
    (hbound : smaller ≤ larger) :
    SourceDeclContractsBelow src ctx smaller := by
  refine { toSourceDeclLayout := hcontracts.toSourceDeclLayout, fn_preserves := ?_ }
  intro fuel hfuel
  exact hcontracts.fn_preserves (Nat.lt_of_lt_of_le hfuel hbound)

/-- Recover the unique target function and its bounded contract from a
callable source declaration. This is the lookup rule used by recursive
`ref` lowering at one mutual-induction step. -/
theorem SourceDeclContractsBelow.fnContract {src : IxIR0.Env} {ctx : Ctx}
    {limit : Nat}
    (hcontracts : SourceDeclContractsBelow src ctx limit)
    {address : Ixon.Address} {source : IxIR0.Decl}
    {worlds : List Owned} {result : Owned}
    (hsrc : src address = some source)
    (hsignature : sourceCallableSignature source =
      some (worlds, result)) :
    ∃ d, ctx.decls address = some (.fn d) ∧
      d.arity = worlds.length ∧ d.result = result ∧
      FnOwnershipContractBelow ctx d worlds limit := by
  obtain ⟨d, hdecl, harity, hresult⟩ :=
    hcontracts.fn hsrc hsignature
  refine ⟨d, hdecl, harity, hresult, ⟨harity.symm, ?_⟩⟩
  intro fuel hfuel
  exact hcontracts.fn_preserves hfuel hsrc hsignature hdecl

/-- Bounded definition lookup in the source/target declaration environment. -/
theorem SourceDeclContractsBelow.defn {src : IxIR0.Env} {ctx : Ctx}
    {limit : Nat}
    (hcontracts : SourceDeclContractsBelow src ctx limit)
    {address : Ixon.Address} {result : Owned} {body : IxIR0.Expr}
    (hsrc : src address = some (.defn result body)) :
    ∃ d, ctx.decls address = some (.fn d) ∧
      d.arity = lamArity body ∧ d.result = result ∧
      FnOwnershipContractBelow ctx d
        ((lamUses body).map worldOfUses) limit := by
  obtain ⟨d, hdecl, harity, hresult, hcontract⟩ :=
    hcontracts.fnContract hsrc (by rfl)
  exact ⟨d, hdecl, by simpa using harity, hresult, hcontract⟩

/-- Bounded recursor lookup in the source/target declaration environment. -/
theorem SourceDeclContractsBelow.recursor {src : IxIR0.Env} {ctx : Ctx}
    {limit : Nat}
    (hcontracts : SourceDeclContractsBelow src ctx limit)
    {address : Ixon.Address} {numArgs : Nat} {natLit : Bool}
    {rules : Array IxIR0.RecRule}
    (hsrc : src address = some (.recursor numArgs natLit rules)) :
    ∃ d, ctx.decls address = some (.fn d) ∧
      d.arity = numArgs + 1 ∧ d.result = .shared ∧
      FnOwnershipContractBelow ctx d
        (List.replicate (numArgs + 1) .shared) limit := by
  obtain ⟨d, hdecl, harity, hresult, hcontract⟩ :=
    hcontracts.fnContract hsrc (by rfl)
  exact ⟨d, hdecl, by simpa using harity, hresult, hcontract⟩

/-- Seal an exact-fuel mutual compiler proof into contracts for the whole
declaration environment. At each index the proof producer may call any
source-backed target function only through the strictly smaller environment;
strong induction closes self recursion and mutually recursive calls alike. -/
theorem sourceDeclContracts_of_below_step {src : IxIR0.Env} {ctx : Ctx}
    (hlayout : SourceDeclLayout src ctx)
    (hstep : ∀ limit,
      SourceDeclContractsBelow src ctx limit →
      SourceFnPreservesAt src ctx limit) :
    SourceDeclContracts src ctx := by
  have hall : ∀ fuel, SourceFnPreservesAt src ctx fuel := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | ind fuel ih =>
      apply hstep fuel
      refine { toSourceDeclLayout := hlayout, fn_preserves := ?_ }
      intro prior hprior
      exact ih prior hprior
  refine { toSourceDeclLayout := hlayout, fn_contract := ?_ }
  intro address source worlds result d hsrc hsignature hdecl
  obtain ⟨d', hdecl', harity, _⟩ := hlayout.fn hsrc hsignature
  have hd : d' = d := by
    have hsame : some (Decl.fn d') = some (Decl.fn d) :=
      hdecl'.symm.trans hdecl
    exact Decl.fn.inj (Option.some.inj hsame)
  subst d'
  refine ⟨harity.symm, ?_⟩
  intro fuel
  exact hall fuel hsrc hsignature hdecl

/-- Definition lookup specialized from the generic declaration contract
environment. -/
theorem SourceDeclContracts.defn {src : IxIR0.Env} {ctx : Ctx}
    (hcontracts : SourceDeclContracts src ctx)
    {address : Ixon.Address} {result : Owned} {body : IxIR0.Expr}
    (hsrc : src address = some (.defn result body)) :
    ∃ d, ctx.decls address = some (.fn d) ∧
      d.arity = lamArity body ∧ d.result = result ∧
      FnOwnershipContract ctx d ((lamUses body).map worldOfUses) := by
  obtain ⟨d, hdecl, harity, hresult⟩ :=
    hcontracts.fn hsrc (by rfl)
  refine ⟨d, hdecl, ?_, hresult, ?_⟩
  · simpa using harity
  · exact hcontracts.fn_contract hsrc (by rfl) hdecl

/-- Recursor lookup specialized from the generic declaration contract
environment. -/
theorem SourceDeclContracts.recursor {src : IxIR0.Env} {ctx : Ctx}
    (hcontracts : SourceDeclContracts src ctx)
    {address : Ixon.Address} {numArgs : Nat} {natLit : Bool}
    {rules : Array IxIR0.RecRule}
    (hsrc : src address = some (.recursor numArgs natLit rules)) :
    ∃ d, ctx.decls address = some (.fn d) ∧
      d.arity = numArgs + 1 ∧ d.result = .shared ∧
      FnOwnershipContract ctx d
        (List.replicate (numArgs + 1) .shared) := by
  obtain ⟨d, hdecl, harity, hresult⟩ :=
    hcontracts.fn hsrc (by rfl)
  exact ⟨d, hdecl, by simpa using harity, hresult,
    hcontracts.fn_contract hsrc (by rfl) hdecl⟩

/-- The two recursive semantic obligations of a closed lowering context:
source-backed direct calls and higher-order pap application. -/
def CompilerPreservesAt (src : IxIR0.Env) (ctx : Ctx)
    (fuel : Nat) : Prop :=
  SourceFnPreservesAt src ctx fuel ∧ ApplyOwnershipPreservesAt ctx fuel

/-- Mutual compiler contracts available below one evaluator-fuel bound. -/
structure CompilerContractsBelow (src : IxIR0.Env) (ctx : Ctx)
    (limit : Nat) : Prop where
  decls : SourceDeclContractsBelow src ctx limit
  apply : ApplyOwnershipContractBelow ctx limit

/-- Completed direct-call and higher-order-application contracts for a
closed lowering context. -/
structure CompilerContracts (src : IxIR0.Env) (ctx : Ctx) : Prop where
  decls : SourceDeclContracts src ctx
  apply : ApplyOwnershipContract ctx

/-- Restrict all completed compiler contracts to a fuel prefix. -/
theorem CompilerContracts.below {src : IxIR0.Env} {ctx : Ctx}
    (hcontracts : CompilerContracts src ctx) (limit : Nat) :
    CompilerContractsBelow src ctx limit :=
  ⟨hcontracts.decls.below limit, hcontracts.apply.below limit⟩

/-- The combined bounded environment is contravariant in its bound. -/
theorem CompilerContractsBelow.mono {src : IxIR0.Env} {ctx : Ctx}
    {smaller larger : Nat}
    (hcontracts : CompilerContractsBelow src ctx larger)
    (hbound : smaller ≤ larger) :
    CompilerContractsBelow src ctx smaller :=
  ⟨hcontracts.decls.mono hbound, hcontracts.apply.mono hbound⟩

/-- Seal the exact-fuel output of the mutual compiler proof into both public
context contracts at once. The producer at `limit` receives only contracts
below `limit`, so direct recursion, cross-declaration calls, and `applyGo`
cycles are all justified by the evaluator's strict fuel decrease. -/
theorem compilerContracts_of_below_step {src : IxIR0.Env} {ctx : Ctx}
    (hlayout : SourceDeclLayout src ctx)
    (hstep : ∀ limit,
      CompilerContractsBelow src ctx limit →
      CompilerPreservesAt src ctx limit) :
    CompilerContracts src ctx := by
  have hall : ∀ fuel, CompilerPreservesAt src ctx fuel := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | ind fuel ih =>
      apply hstep fuel
      refine ⟨?_, ?_⟩
      · refine { toSourceDeclLayout := hlayout, fn_preserves := ?_ }
        intro prior hprior
        exact (ih prior hprior).1
      · refine ⟨?_⟩
        intro prior hprior
        exact (ih prior hprior).2
  refine ⟨?_, ?_⟩
  · apply sourceDeclContracts_of_below_step hlayout
    intro limit _
    exact (hall limit).1
  · apply applyOwnershipContract_of_below_step
    intro limit _
    exact (hall limit).2

/-! ## Closing source-backed and generated declarations together -/

/-- Exact-index ownership preservation for every function accumulated in a
successful lowering state. Generated functions are all-shared at their public
capture-plus-parameter boundary. -/
def ExtraFnPreservesAt (ctx : Ctx) (state : LowSt) (fuel : Nat) : Prop :=
  ∀ {address d}, (address, .fn d) ∈ state.extra →
    d.result = .shared ∧
      FnOwnershipPreservesAt ctx d
        (List.replicate d.arity .shared) fuel

/-- The result-world half of the generated-function invariant is independent
of evaluator fuel. -/
def ExtraFnResultsShared (state : LowSt) : Prop :=
  ∀ {address d}, (address, .fn d) ∈ state.extra →
    d.result = .shared

structure ExtraFnContractsBelow (ctx : Ctx) (state : LowSt)
    (limit : Nat) : Prop where
  fn_result : ExtraFnResultsShared state
  fn_preserves : ∀ {fuel}, fuel < limit →
    ExtraFnPreservesAt ctx state fuel

structure ExtraFnContracts (ctx : Ctx) (state : LowSt) : Prop where
  fn_contract : ∀ {address d}, (address, .fn d) ∈ state.extra →
    d.result = .shared ∧
      FnOwnershipContract ctx d (List.replicate d.arity .shared)

theorem ExtraFnContracts.below {ctx : Ctx} {state : LowSt}
    (hcontracts : ExtraFnContracts ctx state) (limit : Nat) :
    ExtraFnContractsBelow ctx state limit := by
  refine ⟨fun hmember => (hcontracts.fn_contract hmember).1, ?_⟩
  intro fuel _ address d hmember
  obtain ⟨hresult, hcontract⟩ := hcontracts.fn_contract hmember
  exact ⟨hresult, hcontract.preserves⟩

theorem ExtraFnContractsBelow.mono {ctx : Ctx} {state : LowSt}
    {smaller larger : Nat}
    (hcontracts : ExtraFnContractsBelow ctx state larger)
    (hbound : smaller ≤ larger) :
    ExtraFnContractsBelow ctx state smaller := by
  refine ⟨hcontracts.fn_result, ?_⟩
  intro fuel hfuel
  exact hcontracts.fn_preserves (Nat.lt_of_lt_of_le hfuel hbound)

/-- Every source-backed callable has the homogeneous shared signature needed
for it to be a legal target of an arbitrary pap. -/
def SourceAllShared (src : IxIR0.Env) : Prop :=
  ∀ {address source worlds result},
    src address = some source →
    sourceCallableSignature source = some (worlds, result) →
    result = .shared ∧
      worlds = List.replicate worlds.length .shared

/-- Every target function is either the lowering of the same-address source
callable or an exact generated-state member. -/
def FnDeclCovered (src : IxIR0.Env) (ctx : Ctx) (state : LowSt) : Prop :=
  ∀ {address d}, ctx.decls address = some (.fn d) →
    (∃ source worlds result,
      src address = some source ∧
      sourceCallableSignature source = some (worlds, result)) ∨
    (address, .fn d) ∈ state.extra

/-- Source and generated contracts cover the generic all-shared declaration
premise used by the evaluator's application theorem. -/
theorem sharedDeclContractsBelow_of_source_extra
    {src : IxIR0.Env} {ctx : Ctx} {state : LowSt} {limit : Nat}
    (hsource : SourceDeclContractsBelow src ctx limit)
    (hextra : ExtraFnContractsBelow ctx state limit)
    (hshared : SourceAllShared src)
    (hcovered : FnDeclCovered src ctx state) :
    SharedDeclContractsBelow ctx limit := by
  refine ⟨?_⟩
  intro address d hdecl
  cases hcovered hdecl with
  | inl hsourceMember =>
    obtain ⟨source, worlds, result, hsrc, hsignature⟩ := hsourceMember
    obtain ⟨target, htargetDecl, harity, hresult, hcontract⟩ :=
      hsource.fnContract hsrc hsignature
    have htarget : target = d := by
      have heq : some (Decl.fn target) = some (Decl.fn d) :=
        htargetDecl.symm.trans hdecl
      exact Decl.fn.inj (Option.some.inj heq)
    subst target
    obtain ⟨hsourceResult, hworlds⟩ := hshared hsrc hsignature
    have hresultShared : d.result = .shared :=
      hresult.trans hsourceResult
    have hworlds' : worlds = List.replicate d.arity .shared := by
      rw [hworlds, harity]
    rw [hworlds'] at hcontract
    exact ⟨hresultShared, hcontract⟩
  | inr hextraMember =>
    have hpreserves := fun {fuel} (hfuel : fuel < limit) =>
      hextra.fn_preserves hfuel hextraMember
    refine ⟨hextra.fn_result hextraMember, ⟨by simp, ?_⟩⟩
    intro fuel hfuel
    exact (hpreserves hfuel).2

/-- Jointly seal source declarations, generated declarations, and pap
application. At the current evaluator index the producer receives only the
three strictly smaller environments, so the cycle remains contractive. -/
theorem compilerContracts_of_source_extra_below_step
    {src : IxIR0.Env} {ctx : Ctx} {state : LowSt}
    (hlayout : SourceDeclLayout src ctx)
    (hshared : SourceAllShared src)
    (hextraResults : ExtraFnResultsShared state)
    (hcovered : FnDeclCovered src ctx state)
    (hstep : ∀ limit,
      SourceDeclContractsBelow src ctx limit →
      ExtraFnContractsBelow ctx state limit →
      ApplyOwnershipContractBelow ctx limit →
      SourceFnPreservesAt src ctx limit ∧
        ExtraFnPreservesAt ctx state limit) :
    CompilerContracts src ctx ∧ ExtraFnContracts ctx state := by
  have hall : ∀ fuel,
      SourceFnPreservesAt src ctx fuel ∧
        ExtraFnPreservesAt ctx state fuel ∧
        ApplyOwnershipPreservesAt ctx fuel := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | ind fuel ih =>
      let hsourceBelow : SourceDeclContractsBelow src ctx fuel :=
        { toSourceDeclLayout := hlayout
          fn_preserves := fun hprior => (ih _ hprior).1 }
      let hextraBelow : ExtraFnContractsBelow ctx state fuel :=
        ⟨hextraResults, fun hprior => (ih _ hprior).2.1⟩
      let happlyBelow : ApplyOwnershipContractBelow ctx fuel :=
        ⟨fun hprior => (ih _ hprior).2.2⟩
      have hfunctions := hstep fuel hsourceBelow hextraBelow happlyBelow
      have hdecls := sharedDeclContractsBelow_of_source_extra
        hsourceBelow hextraBelow hshared hcovered
      exact ⟨hfunctions.1, hfunctions.2,
        applyOwnershipPreservesAt_of_sharedDeclsBelow hdecls happlyBelow⟩
  have hsourceContracts : SourceDeclContracts src ctx :=
    sourceDeclContracts_of_below_step hlayout fun limit _ => (hall limit).1
  have hextraContracts : ExtraFnContracts ctx state := by
    refine ⟨?_⟩
    intro address d hmember
    have hresult := (hall 0).2.1 hmember |>.1
    refine ⟨hresult, ⟨by simp, ?_⟩⟩
    intro fuel
    exact (hall fuel).2.1 hmember |>.2
  have happlyContract : ApplyOwnershipContract ctx :=
    applyOwnershipContract_of_below_step fun limit _ => (hall limit).2.2
  exact ⟨⟨hsourceContracts, happlyContract⟩, hextraContracts⟩

/-! ## Whole-pass target statements

These definitions make the four independently checkable M2b claims concrete.
They are deliberately separate: semantic value correspondence does not hide
memory progress, reclamation, or counter obligations. -/

/-! ## Semantic call and application contracts -/

/-- Source-side n-ary application, fuel-free at the interface: each step is
one `IxIR0.apply` at some fuel of its own. Currying makes this the exact
source counterpart of the target's `applyGo` argument list. -/
inductive SourceApplies (sourceCtx : IxIR0.Ctx) :
    IxIR0.Value → List IxIR0.Value → IxIR0.Value → Prop where
  | nil {value : IxIR0.Value} : SourceApplies sourceCtx value [] value
  | cons {function argument middle result : IxIR0.Value}
      {arguments : List IxIR0.Value} {fuel : Nat} :
      IxIR0.apply sourceCtx fuel function argument = .ok middle →
      SourceApplies sourceCtx middle arguments result →
      SourceApplies sourceCtx function (argument :: arguments) result

/-- Applying a prefix and then the rest is applying the concatenation. -/
theorem SourceApplies.append {sourceCtx : IxIR0.Ctx}
    {function middle result : IxIR0.Value}
    {left right : List IxIR0.Value}
    (hleft : SourceApplies sourceCtx function left middle)
    (hright : SourceApplies sourceCtx middle right result) :
    SourceApplies sourceCtx function (left ++ right) result := by
  induction hleft with
  | nil => simpa using hright
  | cons hstep _ ih => exact .cons hstep (ih hright)

/-- One more argument after a completed spine. -/
theorem SourceApplies.snoc {sourceCtx : IxIR0.Ctx}
    {function middle result argument : IxIR0.Value}
    {arguments : List IxIR0.Value} {fuel : Nat}
    (hspine : SourceApplies sourceCtx function arguments middle)
    (hstep : IxIR0.apply sourceCtx fuel middle argument = .ok result) :
    SourceApplies sourceCtx function (arguments ++ [argument]) result :=
  hspine.append (.cons hstep .nil)

/-- Splitting a spine at any point exposes the intermediate source value. -/
theorem SourceApplies.split {sourceCtx : IxIR0.Ctx}
    {function result : IxIR0.Value} :
    ∀ {left right : List IxIR0.Value},
      SourceApplies sourceCtx function (left ++ right) result →
      ∃ middle, SourceApplies sourceCtx function left middle ∧
        SourceApplies sourceCtx middle right result := by
  intro left
  induction left generalizing function with
  | nil => intro right h; exact ⟨function, .nil, by simpa using h⟩
  | cons argument rest ih =>
    intro right h
    cases h with
    | cons hstep htail =>
      obtain ⟨middle, hleft, hright⟩ := ih htail
      exact ⟨middle, .cons hstep hleft, hright⟩

/-- The source value a global reference denotes, at some source fuel. This
is the callee's source identity: a `.defn` denotes its closure, while
constructors, recursors, and externs denote their zero-argument paps. -/
def SourceRefValue (sourceCtx : IxIR0.Ctx) (address : Ixon.Address)
    (value : IxIR0.Value) : Prop :=
  ∃ fuel, IxIR0.eval sourceCtx fuel [] (.ref address) = .ok value

/-- Exact-fuel semantic preservation for one compiled declaration body.

Two conclusions, not one. The result clause is the obvious half. The *frame*
clause is the half that makes the contract usable at a call site at all: a
caller's post-state predicate (`GraphOwnsResult` and friends) demands
`RootsGraph` for its framed roots in the store the callee returns, and that
does not follow from ownership. A general callee both frees and allocates,
so neither `StoreGraphExtends` nor `StoreGraphRestricts` covers it, and the
obligation has to be discharged by the callee rather than reconstructed by
the caller. The argument worlds are carried in lockstep with
`FnOwnershipContract` so the two contracts share one call-site premise. -/
def FnValuePreservesAt (funRel : Sim.FunctionRel) (sourceCtx : IxIR0.Ctx)
    (ctx : Ctx) (d : FnDef) (argWorlds : List Owned)
    (sourceFunction : IxIR0.Value) (fuel : Nat) : Prop :=
  ∀ {store store' : Store} {args : List RVal} {value : RVal}
      {sourceArgs : List IxIR0.Value} {sourceResult : IxIR0.Value}
      {sourceRest : List (Owned × IxIR0.Value)} {rest : List Root},
    args.length = argWorlds.length →
    Sim.ValuesGraph funRel store sourceArgs args →
    SourceApplies sourceCtx sourceFunction sourceArgs sourceResult →
    Sim.RootsGraph funRel store sourceRest rest →
    RootOwnership store (rootsForWorlds argWorlds args ++ rest) →
    runCode ctx fuel d store args.reverse d.body = .ok (store', value) →
    Sim.ValueGraph funRel store' sourceResult value ∧
      Sim.RootsGraph funRel store' sourceRest rest

/-- Semantic contract for one compiled function declaration: entered on
arguments realizing source values, its body returns a value realizing the
source evaluator's own result for that saturated application, without
disturbing the caller's framed graphs. -/
structure FnValueContract (funRel : Sim.FunctionRel)
    (sourceCtx : IxIR0.Ctx) (ctx : Ctx) (d : FnDef)
    (argWorlds : List Owned) (sourceFunction : IxIR0.Value) : Prop where
  arity_eq : argWorlds.length = d.arity
  preserves : ∀ {fuel : Nat},
    FnValuePreservesAt funRel sourceCtx ctx d argWorlds sourceFunction fuel

/-- Exact-fuel semantic preservation for higher-order application, with the
same two-clause shape and the same frame obligation as the direct-call
contract. `applyGo` consumes one shared function root and all supplied
shared argument roots, matching `ApplyOwnershipContract`. -/
def ApplyValuePreservesAt (funRel : Sim.FunctionRel)
    (sourceCtx : IxIR0.Ctx) (ctx : Ctx) (fuel : Nat) : Prop :=
  ∀ {store store' : Store} {function : RVal} {args : List RVal}
      {value : RVal} {sourceFunction : IxIR0.Value}
      {sourceArgs : List IxIR0.Value} {sourceResult : IxIR0.Value}
      {sourceRest : List (Owned × IxIR0.Value)} {rest : List Root},
    Sim.ValueGraph funRel store sourceFunction function →
    Sim.ValuesGraph funRel store sourceArgs args →
    SourceApplies sourceCtx sourceFunction sourceArgs sourceResult →
    Sim.RootsGraph funRel store sourceRest rest →
    RootOwnership store
      (⟨.shared, function⟩ :: rootsFor .shared args ++ rest) →
    applyGo ctx fuel store function args = .ok (store', value) →
    Sim.ValueGraph funRel store' sourceResult value ∧
      Sim.RootsGraph funRel store' sourceRest rest

/-- Whole-context semantic application contract. This is where `FunctionRel`
stops being an assumption and becomes an obligation: an abstract relation
that merely *claims* a pap realizes a source function must additionally make
that pap compute the source function. -/
structure ApplyValueContract (funRel : Sim.FunctionRel)
    (sourceCtx : IxIR0.Ctx) (ctx : Ctx) : Prop where
  preserves : ∀ {fuel : Nat},
    ApplyValuePreservesAt funRel sourceCtx ctx fuel

/-- Higher-order semantic application below an evaluator-fuel bound.
Saturating and over-applied paps re-enter declarations at strictly smaller
fuel, so this belongs in the same mutual induction as the call contract. -/
structure ApplyValueContractBelow (funRel : Sim.FunctionRel)
    (sourceCtx : IxIR0.Ctx) (ctx : Ctx) (limit : Nat) : Prop where
  preserves : ∀ {fuel : Nat}, fuel < limit →
    ApplyValuePreservesAt funRel sourceCtx ctx fuel

theorem ApplyValueContract.below {funRel : Sim.FunctionRel}
    {sourceCtx : IxIR0.Ctx} {ctx : Ctx}
    (hcontract : ApplyValueContract funRel sourceCtx ctx) (limit : Nat) :
    ApplyValueContractBelow funRel sourceCtx ctx limit :=
  ⟨fun _ => hcontract.preserves⟩

theorem ApplyValueContractBelow.mono {funRel : Sim.FunctionRel}
    {sourceCtx : IxIR0.Ctx} {ctx : Ctx} {smaller larger : Nat}
    (hcontract : ApplyValueContractBelow funRel sourceCtx ctx larger)
    (hbound : smaller ≤ larger) :
    ApplyValueContractBelow funRel sourceCtx ctx smaller :=
  ⟨fun hfuel => hcontract.preserves (Nat.lt_of_lt_of_le hfuel hbound)⟩

/-- Pointwise semantic preservation of every source-backed target function at
one exact evaluator-fuel index. The source identity of the callee is pinned
by `SourceRefValue` at the same address the layout relation uses, so a
declaration cannot be related to a source function it was not compiled
from. -/
def SourceFnValuePreservesAt (funRel : Sim.FunctionRel)
    (sourceCtx : IxIR0.Ctx) (src : IxIR0.Env) (ctx : Ctx)
    (fuel : Nat) : Prop :=
  ∀ {address : Ixon.Address} {source : IxIR0.Decl}
      {worlds : List Owned} {result : Owned} {d : FnDef}
      {sourceFunction : IxIR0.Value},
    src address = some source →
    sourceCallableSignature source = some (worlds, result) →
    ctx.decls address = some (.fn d) →
    SourceRefValue sourceCtx address sourceFunction →
    FnValuePreservesAt funRel sourceCtx ctx d worlds sourceFunction fuel

/-- Semantic declaration contracts below an evaluator-fuel bound: the mutual
induction hypothesis for cross-declaration and self calls. -/
structure SourceDeclValueContractsBelow (funRel : Sim.FunctionRel)
    (sourceCtx : IxIR0.Ctx) (src : IxIR0.Env) (ctx : Ctx)
    (limit : Nat) : Prop where
  fn_preserves : ∀ {fuel : Nat}, fuel < limit →
    SourceFnValuePreservesAt funRel sourceCtx src ctx fuel

/-- Public, unbounded semantic contracts for every source-backed target
function. -/
structure SourceDeclValueContracts (funRel : Sim.FunctionRel)
    (sourceCtx : IxIR0.Ctx) (src : IxIR0.Env) (ctx : Ctx) : Prop where
  fn_preserves : ∀ {fuel : Nat},
    SourceFnValuePreservesAt funRel sourceCtx src ctx fuel

theorem SourceDeclValueContracts.below {funRel : Sim.FunctionRel}
    {sourceCtx : IxIR0.Ctx} {src : IxIR0.Env} {ctx : Ctx}
    (hcontracts : SourceDeclValueContracts funRel sourceCtx src ctx)
    (limit : Nat) :
    SourceDeclValueContractsBelow funRel sourceCtx src ctx limit :=
  ⟨fun _ => hcontracts.fn_preserves⟩

theorem SourceDeclValueContractsBelow.mono {funRel : Sim.FunctionRel}
    {sourceCtx : IxIR0.Ctx} {src : IxIR0.Env} {ctx : Ctx}
    {smaller larger : Nat}
    (hcontracts : SourceDeclValueContractsBelow funRel sourceCtx src ctx
      larger) (hbound : smaller ≤ larger) :
    SourceDeclValueContractsBelow funRel sourceCtx src ctx smaller :=
  ⟨fun hfuel => hcontracts.fn_preserves (Nat.lt_of_lt_of_le hfuel hbound)⟩

/-- Semantic twin of `CompilerContracts`: direct calls and higher-order
application both carry their source result. -/
structure CompilerValueContracts (funRel : Sim.FunctionRel)
    (sourceCtx : IxIR0.Ctx) (src : IxIR0.Env) (ctx : Ctx) : Prop where
  decls : SourceDeclValueContracts funRel sourceCtx src ctx
  apply : ApplyValueContract funRel sourceCtx ctx

structure CompilerValueContractsBelow (funRel : Sim.FunctionRel)
    (sourceCtx : IxIR0.Ctx) (src : IxIR0.Env) (ctx : Ctx)
    (limit : Nat) : Prop where
  decls : SourceDeclValueContractsBelow funRel sourceCtx src ctx limit
  apply : ApplyValueContractBelow funRel sourceCtx ctx limit

theorem CompilerValueContracts.below {funRel : Sim.FunctionRel}
    {sourceCtx : IxIR0.Ctx} {src : IxIR0.Env} {ctx : Ctx}
    (hcontracts : CompilerValueContracts funRel sourceCtx src ctx)
    (limit : Nat) :
    CompilerValueContractsBelow funRel sourceCtx src ctx limit :=
  ⟨hcontracts.decls.below limit, hcontracts.apply.below limit⟩

theorem CompilerValueContractsBelow.mono {funRel : Sim.FunctionRel}
    {sourceCtx : IxIR0.Ctx} {src : IxIR0.Env} {ctx : Ctx}
    {smaller larger : Nat}
    (hcontracts : CompilerValueContractsBelow funRel sourceCtx src ctx
      larger) (hbound : smaller ≤ larger) :
    CompilerValueContractsBelow funRel sourceCtx src ctx smaller :=
  ⟨hcontracts.decls.mono hbound, hcontracts.apply.mono hbound⟩

/-! ### Semantic call primitives at the operation level -/

/-- Semantic transfer across a direct invocation, from a contract available
strictly below the invocation fuel. A successful invocation at `fuel + 1`
enters the callee body at `fuel`, which is exactly where the mutual
declaration induction needs the strict decrease. -/
theorem invoke_fn_value_below {funRel : Sim.FunctionRel}
    {sourceCtx : IxIR0.Ctx} {ctx : Ctx} {fuel : Nat} {f : Ixon.Address}
    {args : List RVal} {store store' : Store} {value : RVal} {d : FnDef}
    {argWorlds : List Owned} {sourceFunction sourceResult : IxIR0.Value}
    {sourceArgs : List IxIR0.Value}
    {sourceRest : List (Owned × IxIR0.Value)} {rest : List Root}
    (hdecl : ctx.decls f = some (.fn d))
    (harity : argWorlds.length = d.arity)
    (hcontract : ∀ {smaller : Nat}, smaller < fuel →
      FnValuePreservesAt funRel sourceCtx ctx d argWorlds sourceFunction
        smaller)
    (hargs : Sim.ValuesGraph funRel store sourceArgs args)
    (hsource : SourceApplies sourceCtx sourceFunction sourceArgs sourceResult)
    (hframe : Sim.RootsGraph funRel store sourceRest rest)
    (hown : RootOwnership store (rootsForWorlds argWorlds args ++ rest))
    (hinvoke : invoke ctx fuel f args store = .ok (store', value)) :
    Sim.ValueGraph funRel store' sourceResult value ∧
      Sim.RootsGraph funRel store' sourceRest rest := by
  cases fuel with
  | zero => simp [invoke] at hinvoke
  | succ fuel =>
    simp only [invoke, hdecl] at hinvoke
    split at hinvoke
    · contradiction
    next hlen =>
      have hargsLength : args.length = argWorlds.length := by
        have hd : args.length = d.arity := by simpa using hlen
        exact hd.trans harity.symm
      cases hrun : runCode ctx fuel d store args.reverse d.body with
      | error e =>
        rw [hrun] at hinvoke
        change (.error e : Except Err (Store × RVal)) =
          .ok (store', value) at hinvoke
        contradiction
      | ok out =>
        rw [hrun] at hinvoke
        change checkResultWorld d.result out = .ok (store', value) at hinvoke
        obtain ⟨hpair, _⟩ := checkResultWorld_ok hinvoke
        subst out
        exact hcontract (Nat.lt_succ_self fuel) hargsLength hargs hsource
          hframe hown hrun

/-- Operation-level semantic direct call. -/
theorem runOp_call_value_below {funRel : Sim.FunctionRel}
    {sourceCtx : IxIR0.Ctx} {ctx : Ctx} {fuel : Nat} {cur d : FnDef}
    {store store' : Store} {env : List RVal} {f : Ixon.Address}
    {atoms : Array Atom} {args : List RVal} {value : RVal}
    {argWorlds : List Owned} {sourceFunction sourceResult : IxIR0.Value}
    {sourceArgs : List IxIR0.Value}
    {sourceRest : List (Owned × IxIR0.Value)} {rest : List Root}
    (hatoms : resolveAtoms env atoms = .ok args)
    (hdecl : ctx.decls f = some (.fn d))
    (harity : argWorlds.length = d.arity)
    (hcontract : ∀ {smaller : Nat}, smaller < fuel →
      FnValuePreservesAt funRel sourceCtx ctx d argWorlds sourceFunction
        smaller)
    (hargs : Sim.ValuesGraph funRel store sourceArgs args)
    (hsource : SourceApplies sourceCtx sourceFunction sourceArgs sourceResult)
    (hframe : Sim.RootsGraph funRel store sourceRest rest)
    (hown : RootOwnership store (rootsForWorlds argWorlds args ++ rest))
    (hrun : runOp ctx (fuel + 1) cur store env (.call f atoms) =
      .ok (store', value)) :
    Sim.ValueGraph funRel store' sourceResult value ∧
      Sim.RootsGraph funRel store' sourceRest rest := by
  rw [runOp.eq_def] at hrun
  dsimp only at hrun
  rw [hatoms, bindOk] at hrun
  exact invoke_fn_value_below hdecl harity hcontract hargs hsource hframe
    hown hrun

/-- Operation-level semantic recursive self call. The current function's own
contract is available at the enclosing index, since the body re-enters at
`fuel` while the operation runs at `fuel + 1`. -/
theorem runOp_callSelf_value_below {funRel : Sim.FunctionRel}
    {sourceCtx : IxIR0.Ctx} {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store store' : Store} {env : List RVal} {atoms : Array Atom}
    {args : List RVal} {value : RVal}
    {argWorlds : List Owned} {sourceFunction sourceResult : IxIR0.Value}
    {sourceArgs : List IxIR0.Value}
    {sourceRest : List (Owned × IxIR0.Value)} {rest : List Root}
    (hatoms : resolveAtoms env atoms = .ok args)
    (harity : argWorlds.length = cur.arity)
    (hcontract : ∀ {smaller : Nat}, smaller < fuel + 1 →
      FnValuePreservesAt funRel sourceCtx ctx cur argWorlds sourceFunction
        smaller)
    (hargs : Sim.ValuesGraph funRel store sourceArgs args)
    (hsource : SourceApplies sourceCtx sourceFunction sourceArgs sourceResult)
    (hframe : Sim.RootsGraph funRel store sourceRest rest)
    (hown : RootOwnership store (rootsForWorlds argWorlds args ++ rest))
    (hrun : runOp ctx (fuel + 1) cur store env (.callSelf atoms) =
      .ok (store', value)) :
    Sim.ValueGraph funRel store' sourceResult value ∧
      Sim.RootsGraph funRel store' sourceRest rest := by
  rw [runOp.eq_def] at hrun
  dsimp only at hrun
  rw [hatoms, bindOk] at hrun
  split at hrun
  · contradiction
  next hlen =>
    have hargsLength : args.length = argWorlds.length := by
      have hd : args.length = cur.arity := by simpa using hlen
      exact hd.trans harity.symm
    cases hcode : runCode ctx fuel cur store args.reverse cur.body with
    | error e =>
      rw [hcode] at hrun
      change (.error e : Except Err (Store × RVal)) =
        .ok (store', value) at hrun
      contradiction
    | ok out =>
      rw [hcode] at hrun
      change checkResultWorld cur.result out = .ok (store', value) at hrun
      obtain ⟨hpair, _⟩ := checkResultWorld_ok hrun
      subst out
      exact hcontract (Nat.lt_succ_self fuel) hargsLength hargs hsource
        hframe hown hcode

/-! The semantic proof is intentionally a companion refinement over the
ownership development above. `LowerResultSound` remains the reusable
ownership/frame judgment; the semantic induction may consume it, but does not
add source values to each of its existing operation and continuation lemmas. -/

/-- Successful source evaluation has some target execution with a graph-
related result. `funRel` is the lambda-lifting/pap correspondence that the
generated-environment proof must instantiate. -/
def SemanticForwardSimulation (sourceCtx : IxIR0.Ctx) (targetCtx : Ctx)
    (source : IxIR0.Expr) (target : Code) (funRel : Sim.FunctionRel) : Prop :=
  ∀ {sourceFuel sourceValue},
    IxIR0.eval sourceCtx sourceFuel [] source = .ok sourceValue →
    ∃ targetFuel targetStore targetValue,
      runMain targetCtx target targetFuel = .ok (targetStore, targetValue) ∧
        Sim.ValueGraph funRel targetStore sourceValue targetValue

/-- No evaluator fuel may expose a dynamic memory-discipline failure. Fuel,
ordinary stuckness, and closed-world failures remain separate claims. -/
def MemoryErrorUnreachable (targetCtx : Ctx) (target : Code) : Prop :=
  ∀ fuel message, runMain targetCtx target fuel ≠ .error (.mem message)

/-- Release the final result root according to the statically requested
world. Scalars are inert under either release operation. -/
def releaseResult (targetCtx : Ctx) (world : Owned) (fuel : Nat)
    (store : Store) (value : RVal) : Except Err Store :=
  match world with
  | .shared => dropVal targetCtx fuel store value
  | .unique => dropUVal targetCtx fuel store value

/-- A closed successful run can release its final result and leave no live
nodes. The current ownership invariant is intentionally not yet strong
enough to prove this in the presence of rootless cycles; this proposition is
the exact target of that pending invariant decision. -/
def Reclamation (targetCtx : Ctx) (target : Code)
    (resultWorld : Owned) : Prop :=
  ∀ {runFuel store value},
    runMain targetCtx target runFuel = .ok (store, value) →
    ∃ releaseFuel released,
      releaseResult targetCtx resultWorld releaseFuel store value =
          .ok released ∧
        released.live = 0

/-- The four instruction-level counters observed independently of semantic
heap equality. -/
structure CostObservation where
  allocs : Nat
  reuses : Nat
  frees : Nat
  rcops : Nat
  deriving BEq, Repr

def costObservation (store : Store) : CostObservation :=
  ⟨store.allocs, store.reuses, store.frees, store.rcops⟩

/-- A caller-supplied cost specification relates the source result to the
target's counter observation whenever related successful runs are compared.
Keeping `spec` abstract permits exact equations and asymptotic inequalities
without mixing either into semantic equality. -/
def CostRefinement (sourceCtx : IxIR0.Ctx) (targetCtx : Ctx)
    (source : IxIR0.Expr) (target : Code) (funRel : Sim.FunctionRel)
    (spec : IxIR0.Value → CostObservation → Prop) : Prop :=
  ∀ {sourceFuel sourceValue targetFuel targetStore targetValue},
    IxIR0.eval sourceCtx sourceFuel [] source = .ok sourceValue →
    runMain targetCtx target targetFuel = .ok (targetStore, targetValue) →
    Sim.ValueGraph funRel targetStore sourceValue targetValue →
    spec sourceValue (costObservation targetStore)

/-! ## First executable lowering cases -/

private theorem scalar_id_sound_at {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {Γ : VEnv} {world : Owned} {atom : Atom}
    {value : RVal}
    (hstable : AValStable (.constA atom))
    (hresolve : ∀ env, resolveAtom env atom = .ok value)
    (hnone : rvalLocation? value = none) :
    LowerResultSoundBelow ctx cur limit Γ Γ world (_root_.id : Emit)
      (.constA atom) := by
  refine ⟨hstable, ?_⟩
  intro rest slots
  apply EmitSoundBelow.strengthen
  intro store env hpre
  obtain ⟨⟨roots, hΓ, hown⟩, hslots⟩ := hpre
  exact ⟨⟨roots, value, hΓ, .const (hresolve env),
    hown.addNoLocation hnone⟩, hslots⟩

theorem scalar_id_sound {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {world : Owned} {atom : Atom} {value : RVal}
    (hstable : AValStable (.constA atom))
    (hresolve : ∀ env, resolveAtom env atom = .ok value)
    (hnone : rvalLocation? value = none) :
    LowerResultSound ctx cur Γ Γ world (_root_.id : Emit)
      (.constA atom) := by
  apply LowerResultSound.of_below
  intro limit
  exact scalar_id_sound_at (limit := limit) hstable hresolve hnone

/-- Semantic scalar identity rule. The source/result graph premise is
store-polymorphic because literals and erased values do not inspect the heap. -/
theorem scalar_id_value_sound {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value} {sourceValue : IxIR0.Value}
    {world : Owned} {atom : Atom} {value : RVal}
    (hstable : AValStable (.constA atom))
    (hresolve : ∀ env, resolveAtom env atom = .ok value)
    (hnone : rvalLocation? value = none)
    (hvalue : ∀ store,
      Sim.ValueGraph funRel store sourceValue value) :
    LowerResultValueSound funRel recSelfRel ctx cur Γ Γ
      sourceEnv sourceEnv sourceValue world (_root_.id : Emit)
      (.constA atom) := by
  refine
    { toLowerResultSound := scalar_id_sound hstable hresolve hnone
      graphEmits := ?_ }
  intro sourceRest rest slots
  apply EmitSound.strengthen
  intro store env hpre
  obtain ⟨⟨roots, hΓ, hrestGraph, hown⟩, hslots⟩ := hpre
  exact ⟨⟨roots, value, hΓ, .const (hresolve env), hvalue store,
    hrestGraph, hown.addNoLocation hnone⟩, hslots⟩

/-- Fuel-bounded ownership rule for an environment-independent scalar. -/
theorem scalar_id_sound_below {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {Γ : VEnv} {world : Owned} {atom : Atom} {value : RVal}
    (hstable : AValStable (.constA atom))
    (hresolve : ∀ env, resolveAtom env atom = .ok value)
    (hnone : rvalLocation? value = none) :
    LowerResultSoundBelow ctx cur limit Γ Γ world (_root_.id : Emit)
      (.constA atom) := by
  exact scalar_id_sound_at hstable hresolve hnone

theorem lower_lit_sound {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {world : Owned} {literal : IxIR0.Literal} :
    LowerResultSound ctx cur Γ Γ world (_root_.id : Emit)
      (.constA (.lit literal)) := by
  apply scalar_id_sound .lit
  · intro env; rfl
  · rfl

theorem lower_lit_value_sound {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value} {world : Owned}
    {literal : IxIR0.Literal} :
    LowerResultValueSound funRel recSelfRel ctx cur Γ Γ
      sourceEnv sourceEnv (.lit literal) world (_root_.id : Emit)
      (.constA (.lit literal)) := by
  apply scalar_id_value_sound .lit
  · intro env
    rfl
  · rfl
  · intro store
    exact .lit

theorem lower_lit_sound_below {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {Γ : VEnv} {world : Owned}
    {literal : IxIR0.Literal} :
    LowerResultSoundBelow ctx cur limit Γ Γ world (_root_.id : Emit)
      (.constA (.lit literal)) := by
  apply scalar_id_sound_below .lit
  · intro env
    rfl
  · rfl

theorem lower_erased_sound {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {world : Owned} :
    LowerResultSound ctx cur Γ Γ world (_root_.id : Emit)
      (.constA .erased) := by
  apply scalar_id_sound .erased
  · intro env; rfl
  · rfl

theorem lower_erased_value_sound {funRel : Sim.FunctionRel}
    {recSelfRel : RecSelfRel} {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {sourceEnv : List IxIR0.Value} {world : Owned} :
    LowerResultValueSound funRel recSelfRel ctx cur Γ Γ
      sourceEnv sourceEnv .erased world (_root_.id : Emit)
      (.constA .erased) := by
  apply scalar_id_value_sound .erased
  · intro env
    rfl
  · rfl
  · intro store
    exact .erased

theorem lower_erased_sound_below {ctx : Ctx} {cur : FnDef}
    {limit : Nat} {Γ : VEnv} {world : Owned} :
    LowerResultSoundBelow ctx cur limit Γ Γ world (_root_.id : Emit)
      (.constA .erased) := by
  apply scalar_id_sound_below .erased
  · intro env
    rfl
  · rfl

/-- Evaluate shared arguments to an erased function, release every produced
owner, and return the erased scalar at the caller's demanded result world. -/
theorem LowerResultSound.discardArgs {ctx : Ctx} {cur : FnDef}
    {start input output : VEnv} {resultWorld : Owned}
    {emitFunction emitArgs : Emit} {avs : List AVal}
    (hfunction : LowerResultSound ctx cur start input .shared
      emitFunction (.constA .erased))
    (hargs : LowerArgsSound ctx cur input output
      (List.replicate avs.length .shared) emitArgs avs) :
    LowerResultSound ctx cur start (releaseAll output avs).1 resultWorld
      ((emitFunction ∘ emitArgs) ∘ (releaseAll output avs).2)
      (.constA .erased) := by
  refine ⟨.erased, ?_⟩
  intro rest slots
  have hrelease := releaseAll_sound (ctx := ctx) (cur := cur)
    (Γ := output) hargs.stable
  have hcomposed := EmitSound.comp (hfunction.emits rest slots)
    (EmitSound.comp (discard_const_result AValStable.erased rest slots)
      (EmitSound.comp (hargs.emits rest slots)
        (EmitSound.comp (hrelease rest slots)
          ((lower_erased_sound (ctx := ctx) (cur := cur)
            (Γ := (releaseAll output avs).1)
            (world := resultWorld)).emits rest slots))))
  simpa [Function.comp_def] using hcomposed

/-- Semantic erased-application composition. The erased function result is
ownership-inert, every argument is still evaluated and graph-related, and
`releaseAll` consumes those temporary argument values before producing the
source evaluator's erased result. -/
theorem LowerResultValueSound.discardArgs
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef}
    {start input output : VEnv}
    {sourceStart sourceMiddle sourceOutput sourceValues :
      List IxIR0.Value}
    {resultWorld : Owned} {emitFunction emitArgs : Emit}
    {avs : List AVal}
    (hfunction : LowerResultValueSound funRel recSelfRel ctx cur
      start input sourceStart sourceMiddle .erased .shared
      emitFunction (.constA .erased))
    (hargs : LowerArgsValueSound funRel recSelfRel ctx cur input output
      sourceMiddle sourceOutput sourceValues
      (List.replicate avs.length .shared) emitArgs avs)
    (hsourceLength : sourceValues.length = avs.length) :
    LowerResultValueSound funRel recSelfRel ctx cur start
      (releaseAll output avs).1 sourceStart sourceOutput .erased
      resultWorld
      ((emitFunction ∘ emitArgs) ∘ (releaseAll output avs).2)
      (.constA .erased) := by
  refine
    { toLowerResultSound := hfunction.toLowerResultSound.discardArgs
        hargs.toLowerArgsSound
      graphEmits := ?_ }
  intro sourceRest rest slots
  have hrelease := releaseAll_value_sound
    (funRel := funRel) (recSelfRel := recSelfRel)
    (ctx := ctx) (cur := cur) (Γ := output)
    (sourceEnv := sourceOutput) hargs.stable hsourceLength
  have hcomposed := EmitSound.comp
    (hfunction.graphEmits sourceRest rest slots)
    (EmitSound.comp
      (discard_const_result_value
        (funRel := funRel) (recSelfRel := recSelfRel)
        (ctx := ctx) (cur := cur) (Γ := input)
        (sourceEnv := sourceMiddle) (sourceValue := IxIR0.Value.erased)
        AValStable.erased sourceRest rest slots)
      (EmitSound.comp (hargs.graphEmits sourceRest rest slots)
        (EmitSound.comp (hrelease.graphEmits sourceRest rest slots)
          ((lower_erased_value_sound
            (funRel := funRel) (recSelfRel := recSelfRel)
            (ctx := ctx) (cur := cur)
            (Γ := (releaseAll output avs).1)
            (sourceEnv := sourceOutput) (world := resultWorld)).graphEmits
              sourceRest rest slots))))
  simpa [Function.comp_def] using hcomposed

/-- Bounded erased-function path: evaluate and release every shared
argument, then return the ownership-inert erased value. -/
theorem LowerResultSoundBelow.discardArgs
    {ctx : Ctx} {cur : FnDef} {limit : Nat}
    {start input output : VEnv} {resultWorld : Owned}
    {emitFunction emitArgs : Emit} {avs : List AVal}
    (hfunction : LowerResultSoundBelow ctx cur limit start input .shared
      emitFunction (.constA .erased))
    (hargs : LowerArgsSoundBelow ctx cur limit input output
      (List.replicate avs.length .shared) emitArgs avs) :
    LowerResultSoundBelow ctx cur limit start (releaseAll output avs).1
      resultWorld ((emitFunction ∘ emitArgs) ∘ (releaseAll output avs).2)
      (.constA .erased) := by
  refine ⟨.erased, ?_⟩
  intro rest slots
  have hrelease := releaseAll_sound_below
    (ctx := ctx) (cur := cur) (limit := limit)
    (Γ := output) hargs.stable
  have hcomposed := EmitSoundBelow.comp (hfunction.emits rest slots)
    (EmitSoundBelow.comp
      (discard_const_result_below AValStable.erased rest slots)
      (EmitSoundBelow.comp (hargs.emits rest slots)
        (EmitSoundBelow.comp (hrelease rest slots)
          ((lower_erased_sound_below (ctx := ctx) (cur := cur)
            (limit := limit) (Γ := (releaseAll output avs).1)
            (world := resultWorld)).emits rest slots))))
  simpa [Function.comp_def] using hcomposed

/-- The first sequencing case of the compiler induction: a scalar literal is
materialized for a `many` binder, its sole variable occurrence moves that
slot into the result, and the old source environment remains realized under
the newly pushed runtime slot. -/
theorem lower_let_lit_var_sound {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {literal : IxIR0.Literal} :
    LowerResultSound ctx cur Γ Γ.bump .shared
      (emitOp (.pure (.lit literal))) (.slotA Γ.depth) := by
  refine ⟨.slot, ?_⟩
  intro rest slots
  apply OpSound.emit
  intro fuel store env store' result hpre hrun
  obtain ⟨⟨roots, hΓ, hown⟩, hslots⟩ := hpre
  cases fuel with
  | zero => simp [runOp] at hrun
  | succ fuel =>
    have hop := runOp_pure_scalar_owned (ctx := ctx) (cur := cur)
      (fuel := fuel) (world := Owned.shared) (roots := roots ++ rest)
      (env := env) (target := .lit literal) (value := .lit literal)
      rfl rfl hown
    have hpair : (store, RVal.lit literal) = (store', result) :=
      Except.ok.inj (hop.1.symm.trans hrun)
    cases hpair
    refine ⟨⟨roots, .lit literal, hΓ.bump (.lit literal), ?_, hop.2⟩,
      hslots.bump (.lit literal)⟩
    · apply AValRealizes.slot
      · simp [VEnv.bump]
      · simp [VEnv.bump, VEnv.rel]

/-- Executable/proof base case for the actual `lowerArgs` definition. -/
theorem lowerArgs_nil_verified {ctx : Ctx} {cur : FnDef}
    (src : IxIR0.Env) (fuel : Nat) (Γ : VEnv) (state : LowSt) :
    (lowerArgs src (Nat.succ fuel) Γ []).run state =
        .ok (Γ, (_root_.id : Emit), []) state ∧
      LowerArgsSound ctx cur Γ Γ [] (_root_.id : Emit) [] := by
  exact ⟨by simp [lowerArgs], lowerArgs_nil_sound⟩

/-- Generic executable/proof cons rule. This is the constructor used by the
eventual mutual induction once its head `lowerE` and tail `lowerArgs`
recursive calls have returned. -/
theorem lowerArgs_cons_verified {ctx : Ctx} {cur : FnDef}
    (src : IxIR0.Env) (fuel : Nat) (input middle output : VEnv)
    (expr : IxIR0.Expr) (world : Owned)
    (args : List (IxIR0.Expr × Owned))
    (emitHead emitTail : Emit) (av : AVal) (avs : List AVal)
    (state middleState finalState : LowSt)
    (hheadRun : (lowerE src fuel input world expr).run state =
      .ok (middle, emitHead, av) middleState)
    (htailRun : (lowerArgs src fuel middle args).run middleState =
      .ok (output, emitTail, avs) finalState)
    (hhead : LowerResultSound ctx cur input middle world emitHead av)
    (htail : LowerArgsSound ctx cur middle output (args.map Prod.snd)
      emitTail avs) :
    (lowerArgs src (Nat.succ fuel) input ((expr, world) :: args)).run state =
        .ok (output, emitHead ∘ emitTail, av :: avs) finalState ∧
      LowerArgsSound ctx cur input output
        (world :: args.map Prod.snd) (emitHead ∘ emitTail) (av :: avs) := by
  constructor
  · simp only [lowerArgs]
    rw [estateBindRun, hheadRun]
    simp only
    rw [estateBindRun, htailRun]
    rfl
  · exact hhead.consArgs htail

/-- Bounded executable/proof cons rule for the mutual induction. -/
theorem lowerArgs_cons_verified_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat}
    (src : IxIR0.Env) (fuel : Nat) (input middle output : VEnv)
    (expr : IxIR0.Expr) (world : Owned)
    (args : List (IxIR0.Expr × Owned))
    (emitHead emitTail : Emit) (av : AVal) (avs : List AVal)
    (state middleState finalState : LowSt)
    (hheadRun : (lowerE src fuel input world expr).run state =
      .ok (middle, emitHead, av) middleState)
    (htailRun : (lowerArgs src fuel middle args).run middleState =
      .ok (output, emitTail, avs) finalState)
    (hhead : LowerResultSoundBelow ctx cur limit input middle world
      emitHead av)
    (htail : LowerArgsSoundBelow ctx cur limit middle output
      (args.map Prod.snd) emitTail avs) :
    (lowerArgs src (Nat.succ fuel) input ((expr, world) :: args)).run state =
        .ok (output, emitHead ∘ emitTail, av :: avs) finalState ∧
      LowerArgsSoundBelow ctx cur limit input output
        (world :: args.map Prod.snd) (emitHead ∘ emitTail)
        (av :: avs) := by
  constructor
  · simp only [lowerArgs]
    rw [estateBindRun, hheadRun]
    simp only
    rw [estateBindRun, htailRun]
    rfl
  · exact hhead.consArgs htail

/-- The executable erased branch of `applyRest`, paired with argument
evaluation and exact release of every shared argument owner. No result-world
guard is needed because the returned erased scalar inhabits either world. -/
theorem applyRest_erased_verified {ctx : Ctx} {cur : FnDef}
    (src : IxIR0.Env) (fuel : Nat) (start input output : VEnv)
    (resultWorld : Owned) (emitFunction emitArgs : Emit)
    (args : List IxIR0.Expr) (avs : List AVal)
    (state finalState : LowSt)
    (hargsRun :
      (lowerArgs src fuel input
        (args.map (fun arg => (arg, Owned.shared)))).run state =
        .ok (output, emitArgs, avs) finalState)
    (hargsSound : LowerArgsSound ctx cur input output
      ((args.map (fun arg => (arg, Owned.shared))).map Prod.snd)
      emitArgs avs)
    (hworldsHomogeneous :
      ((args.map (fun arg => (arg, Owned.shared))).map Prod.snd) =
        List.replicate avs.length .shared)
    (hfunction : LowerResultSound ctx cur start input .shared
      emitFunction (.constA .erased)) :
    (applyRest src (Nat.succ fuel) input resultWorld emitFunction
      (.constA .erased) args).run state =
        .ok ((releaseAll output avs).1,
          (emitFunction ∘ emitArgs) ∘ (releaseAll output avs).2,
          .constA .erased) finalState ∧
      LowerResultSound ctx cur start (releaseAll output avs).1 resultWorld
        ((emitFunction ∘ emitArgs) ∘ (releaseAll output avs).2)
        (.constA .erased) := by
  constructor
  · simp only [applyRest]
    rw [estateBindRun, hargsRun]
    rfl
  · have hhomogeneous : LowerArgsSound ctx cur input output
        (List.replicate avs.length .shared) emitArgs avs := by
      simpa [hworldsHomogeneous] using hargsSound
    exact hfunction.discardArgs hhomogeneous

/-- The executable non-erased branch of `applyRest`, paired with the
ownership proof for the exact emitter it returns. Unknown callees are
shared-only in v1, so both the supplied arguments and the result use the
shared world. -/
theorem applyRest_shared_verified {ctx : Ctx} {cur : FnDef}
    (src : IxIR0.Env) (fuel : Nat) (start input output : VEnv)
    (emitFunction emitArgs : Emit) (function : AVal)
    (args : List IxIR0.Expr) (avs : List AVal)
    (state finalState : LowSt)
    (hfunctionNe : function ≠ .constA .erased)
    (hargsRun :
      (lowerArgs src fuel input
        (args.map (fun arg => (arg, Owned.shared)))).run state =
        .ok (output, emitArgs, avs) finalState)
    (hargsSound : LowerArgsSound ctx cur input output
      ((args.map (fun arg => (arg, Owned.shared))).map Prod.snd)
      emitArgs avs)
    (hworldsHomogeneous :
      ((args.map (fun arg => (arg, Owned.shared))).map Prod.snd) =
        List.replicate avs.length .shared)
    (hfunction : LowerResultSound ctx cur start input .shared
      emitFunction function)
    (hcontract : ApplyOwnershipContract ctx) :
    (applyRest src (Nat.succ fuel) input .shared emitFunction function
      args).run state =
        .ok (output.bump,
          (emitFunction ∘ emitArgs) ∘
            emitOp (.apply (function.toAtom output)
              (avs.map (·.toAtom output)).toArray),
          .slotA output.depth) finalState ∧
      LowerResultSound ctx cur start output.bump .shared
        ((emitFunction ∘ emitArgs) ∘
          emitOp (.apply (function.toAtom output)
            (avs.map (·.toAtom output)).toArray))
        (.slotA output.depth) := by
  constructor
  · simp only [applyRest]
    have hrequire :
        (requireResultWorld .shared .shared).run state =
          .ok () state := by
      rfl
    rw [estateBindRun, hrequire]
    simp only
    rw [estateBindRun, hargsRun]
    rfl
  · have hhomogeneous : LowerArgsSound ctx cur input output
        (List.replicate avs.length .shared) emitArgs avs := by
      simpa [hworldsHomogeneous] using hargsSound
    exact hfunction.applyArgs hhomogeneous hcontract

/-- Bounded erased `applyRest` branch. The executable length invariant
derives the homogeneous shared-world telescope internally. -/
theorem applyRest_erased_verified_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat}
    (src : IxIR0.Env) (fuel : Nat) (start input output : VEnv)
    (resultWorld : Owned) (emitFunction emitArgs : Emit)
    (args : List IxIR0.Expr) (avs : List AVal)
    (state finalState : LowSt)
    (hargsRun :
      (lowerArgs src fuel input
        (args.map (fun arg => (arg, Owned.shared)))).run state =
        .ok (output, emitArgs, avs) finalState)
    (hargsSound : LowerArgsSoundBelow ctx cur limit input output
      ((args.map (fun arg => (arg, Owned.shared))).map Prod.snd)
      emitArgs avs)
    (hfunction : LowerResultSoundBelow ctx cur limit start input .shared
      emitFunction (.constA .erased)) :
    (applyRest src (Nat.succ fuel) input resultWorld emitFunction
      (.constA .erased) args).run state =
        .ok ((releaseAll output avs).1,
          (emitFunction ∘ emitArgs) ∘ (releaseAll output avs).2,
          .constA .erased) finalState ∧
      LowerResultSoundBelow ctx cur limit start (releaseAll output avs).1
        resultWorld
        ((emitFunction ∘ emitArgs) ∘ (releaseAll output avs).2)
        (.constA .erased) := by
  constructor
  · simp only [applyRest]
    rw [estateBindRun, hargsRun]
    rfl
  · have havsLength : avs.length = args.length := by
      simpa using lowerArgs_success_length src hargsRun
    have hworldsHomogeneous :
        ((args.map (fun arg => (arg, Owned.shared))).map Prod.snd) =
          List.replicate avs.length .shared := by
      simpa [havsLength] using map_shared_arg_worlds args
    have hhomogeneous : LowerArgsSoundBelow ctx cur limit input output
        (List.replicate avs.length .shared) emitArgs avs := by
      simpa [hworldsHomogeneous] using hargsSound
    exact hfunction.discardArgs hhomogeneous

/-- Bounded non-erased `applyRest` branch. -/
theorem applyRest_shared_verified_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat}
    (src : IxIR0.Env) (fuel : Nat) (start input output : VEnv)
    (emitFunction emitArgs : Emit) (function : AVal)
    (args : List IxIR0.Expr) (avs : List AVal)
    (state finalState : LowSt)
    (hfunctionNe : function ≠ .constA .erased)
    (hargsRun :
      (lowerArgs src fuel input
        (args.map (fun arg => (arg, Owned.shared)))).run state =
        .ok (output, emitArgs, avs) finalState)
    (hargsSound : LowerArgsSoundBelow ctx cur limit input output
      ((args.map (fun arg => (arg, Owned.shared))).map Prod.snd)
      emitArgs avs)
    (hfunction : LowerResultSoundBelow ctx cur limit start input .shared
      emitFunction function)
    (hcontract : ApplyOwnershipContractBelow ctx limit) :
    (applyRest src (Nat.succ fuel) input .shared emitFunction function
      args).run state =
        .ok (output.bump,
          (emitFunction ∘ emitArgs) ∘
            emitOp (.apply (function.toAtom output)
              (avs.map (·.toAtom output)).toArray),
          .slotA output.depth) finalState ∧
      LowerResultSoundBelow ctx cur limit start output.bump .shared
        ((emitFunction ∘ emitArgs) ∘
          emitOp (.apply (function.toAtom output)
            (avs.map (·.toAtom output)).toArray))
        (.slotA output.depth) := by
  constructor
  · simp only [applyRest]
    have hrequire :
        (requireResultWorld .shared .shared).run state =
          .ok () state := by
      rfl
    rw [estateBindRun, hrequire]
    simp only
    rw [estateBindRun, hargsRun]
    rfl
  · have havsLength : avs.length = args.length := by
      simpa using lowerArgs_success_length src hargsRun
    have hworldsHomogeneous :
        ((args.map (fun arg => (arg, Owned.shared))).map Prod.snd) =
          List.replicate avs.length .shared := by
      simpa [havsLength] using map_shared_arg_worlds args
    have hhomogeneous : LowerArgsSoundBelow ctx cur limit input output
        (List.replicate avs.length .shared) emitArgs avs := by
      simpa [hworldsHomogeneous] using hargsSound
    exact hfunction.applyArgs hhomogeneous hcontract

/-- One compiler-fuel step for `applyRest`, derived from predecessor-fuel
argument lowering and the bounded higher-order application contract. -/
theorem applyRestPreservesBelow_succ
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat}
    (hargs : LowerArgsPreservesBelow ctx cur limit src fuel)
    (happly : ApplyOwnershipContractBelow ctx limit) :
    ApplyRestPreservesBelow ctx cur limit src (fuel + 1) := by
  intro start input resultWorld pre function args state finalState
    output emit av hfunction hrun hrepresented havailable
  by_cases herased : function = .constA .erased
  · subst function
    simp only [applyRest] at hrun
    obtain ⟨argsResult, argsState, hargsRun, hpureRun⟩ :=
      estateBindRun_ok_inv hrun
    rcases argsResult with ⟨argsOutput, emitArgs, avs⟩
    have hpure :
        ((releaseAll argsOutput avs).1,
          pre ∘ emitArgs ∘ (releaseAll argsOutput avs).2,
          AVal.constA .erased) = (output, emit, av) ∧
          argsState = finalState := by
      simpa using hpureRun
    obtain ⟨hvalue, hstate⟩ := hpure
    cases hvalue
    subst finalState
    have hargsSound := hargs hargsRun hrepresented havailable
    have havsLength : avs.length = args.length := by
      simpa using lowerArgs_success_length src hargsRun
    have hworldsHomogeneous :
        ((args.map (fun arg => (arg, Owned.shared))).map Prod.snd) =
          List.replicate avs.length .shared := by
      simpa [havsLength] using map_shared_arg_worlds args
    have hhomogeneous : LowerArgsSoundBelow ctx cur limit input argsOutput
        (List.replicate avs.length .shared) emitArgs avs := by
      simpa [hworldsHomogeneous] using hargsSound
    simpa [Function.comp_def] using hfunction.discardArgs hhomogeneous
  · cases resultWorld with
    | shared =>
      simp only [applyRest] at hrun
      have hrequire :
          (requireResultWorld .shared .shared).run state =
            .ok () state := by
        rfl
      rw [estateBindRun, hrequire] at hrun
      simp only at hrun
      obtain ⟨argsResult, argsState, hargsRun, hpureRun⟩ :=
        estateBindRun_ok_inv hrun
      rcases argsResult with ⟨argsOutput, emitArgs, avs⟩
      have hpure :
          (argsOutput.bump,
            pre ∘ emitArgs ∘
              emitOp (.apply (function.toAtom argsOutput)
                (avs.map (·.toAtom argsOutput)).toArray),
            AVal.slotA argsOutput.depth) = (output, emit, av) ∧
            argsState = finalState := by
        simpa using hpureRun
      obtain ⟨hvalue, hstate⟩ := hpure
      cases hvalue
      subst finalState
      have hargsSound := hargs hargsRun hrepresented havailable
      have havsLength : avs.length = args.length := by
        simpa using lowerArgs_success_length src hargsRun
      have hworldsHomogeneous :
          ((args.map (fun arg => (arg, Owned.shared))).map Prod.snd) =
            List.replicate avs.length .shared := by
        simpa [havsLength] using map_shared_arg_worlds args
      have hhomogeneous : LowerArgsSoundBelow ctx cur limit input argsOutput
          (List.replicate avs.length .shared) emitArgs avs := by
        simpa [hworldsHomogeneous] using hargsSound
      simpa [Function.comp_def] using
        hfunction.applyArgs hhomogeneous happly
    | unique =>
      simp only [applyRest] at hrun
      have hrequire :
          (requireResultWorld .shared .unique).run state =
            .error "call result is shared at unique demand" state := by
        rfl
      rw [estateBindRun, hrequire] at hrun
      contradiction

/-- Like `lowerArgs`, `applyRest` follows from strictly smaller expression
soundness. Higher-order evaluator recursion is supplied separately by the
bounded compiler contract. -/
theorem applyRestPreservesBelow_of_expr
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    (fuel : Nat)
    (hexpr : ∀ prior, prior < fuel →
      LowerEPreservesBelow ctx cur limit src prior)
    (hextra : ∀ prior, prior < fuel →
      LowerArgsExtraMonotone src prior)
    (happly : ApplyOwnershipContractBelow ctx limit) :
    ApplyRestPreservesBelow ctx cur limit src fuel := by
  cases fuel with
  | zero =>
    intro start input resultWorld pre function args state finalState
      output emit av hfunction hrun hrepresented _
    simp only [applyRest] at hrun
    exact (estateThrowRun_not_ok hrun).elim
  | succ fuel =>
    apply applyRestPreservesBelow_succ
    · apply lowerArgsPreservesBelow_of_expr fuel
      intro prior hprior
      exact hexpr prior (Nat.lt_trans hprior (Nat.lt_succ_self fuel))
      intro prior hprior
      exact hextra prior (Nat.lt_trans hprior (Nat.lt_succ_self fuel))
    · exact happly

/-- A successful non-erased `applyRest` run necessarily passed its shared
result-world guard. This executable fact is independent of semantic
contracts and is used to classify over-applied static producers. -/
theorem applyRest_slot_run_world_shared
    {src : IxIR0.Env} {fuel : Nat} {input output : VEnv}
    {resultWorld : Owned} {pre emit : Emit} {abs : Nat}
    {args : List IxIR0.Expr} {av : AVal}
    {state finalState : LowSt}
    (hrun : (applyRest src fuel input resultWorld pre (.slotA abs)
      args).run state = .ok (output, emit, av) finalState) :
    resultWorld = .shared := by
  cases fuel with
  | zero =>
    simp only [applyRest] at hrun
    exact (estateThrowRun_not_ok hrun).elim
  | succ fuel =>
    simp only [applyRest] at hrun
    obtain ⟨checked, nextState, hrequireRun, _⟩ :=
      estateBindRun_ok_inv hrun
    cases checked
    exact (requireResultWorld_run_ok_inv hrequireRun).1.symm

/-- In the excess-tail branch of `knownCall`, successful execution forces
the requested result world to be shared before higher-order application. -/
theorem knownCall_over_run_world_shared
    {src : IxIR0.Env} {fuel count : Nat} {build : Array Atom → Op}
    {argWorlds : List Owned} {resultWorld : Owned} {input output : VEnv}
    {args : List IxIR0.Expr} {emit : Emit} {av : AVal}
    {state finalState : LowSt}
    (hover : count < args.length)
    (hrun : (knownCall src (fuel + 1) input build count argWorlds
      resultWorld args).run state = .ok (output, emit, av) finalState) :
    resultWorld = .shared := by
  simp only [knownCall] at hrun
  obtain ⟨prefixResult, prefixState, _, hafterPrefix⟩ :=
    estateBindRun_ok_inv hrun
  rcases prefixResult with ⟨prefixOutput, emitPrefix, prefixAVals⟩
  dsimp only at hafterPrefix
  rw [if_neg (Nat.not_le.mpr hover)] at hafterPrefix
  exact applyRest_slot_run_world_shared hafterPrefix

/-- One successful compiler-fuel `knownCall` step, factored uniformly across
call, self-call, allocation, pap, and extern builders. -/
theorem knownCall_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel count : Nat} {build : Array Atom → Op}
    {argWorlds : List Owned} {resultWorld buildWorld : Owned}
    {input : VEnv} {args : List IxIR0.Expr}
    {state finalState : LowSt} {output : VEnv}
    {emit : Emit} {av : AVal}
    (hargs : LowerArgsPreservesBelow ctx cur limit src fuel)
    (hrest : ApplyRestPreservesBelow ctx cur limit src fuel)
    (hrestExtra : ApplyRestExtraMonotone src fuel)
    (hbuild : ∀ {prefixOutput : VEnv}
        {emitPrefix : Emit} {prefixAVals : List AVal},
      LowerArgsSoundBelow ctx cur limit input prefixOutput
          (((args.take count).zip (padWorlds argWorlds count)).map Prod.snd)
          emitPrefix prefixAVals →
      prefixAVals.length =
          ((args.take count).zip (padWorlds argWorlds count)).length →
      LowerResultSoundBelow ctx cur limit input prefixOutput.bump buildWorld
        (emitPrefix ∘ emitOp
          (build (prefixAVals.map (·.toAtom prefixOutput)).toArray))
        (.slotA prefixOutput.depth))
    (hterminalWorld : args.length ≤ count → buildWorld = resultWorld)
    (hoverWorld : count < args.length → buildWorld = .shared)
    (hrun : (knownCall src (fuel + 1) input build count argWorlds
      resultWorld args).run state = .ok (output, emit, av) finalState) :
    ExtraRepresented ctx finalState →
    SelfAvailableBelow ctx cur limit input →
    LowerResultSoundBelow ctx cur limit input output resultWorld emit av := by
  intro hrepresented havailable
  simp only [knownCall] at hrun
  obtain ⟨prefixResult, prefixState, hprefixRun, hafterPrefix⟩ :=
    estateBindRun_ok_inv hrun
  rcases prefixResult with ⟨prefixOutput, emitPrefix, prefixAVals⟩
  dsimp only at hafterPrefix
  have hprefixLength := lowerArgs_success_length src hprefixRun
  by_cases hle : args.length ≤ count
  · rw [if_pos hle] at hafterPrefix
    have hpure :
        (prefixOutput.bump,
          emitPrefix ∘ emitOp
            (build (prefixAVals.map (·.toAtom prefixOutput)).toArray),
          AVal.slotA prefixOutput.depth) = (output, emit, av) ∧
          prefixState = finalState := by
      simpa using hafterPrefix
    obtain ⟨hvalue, hstate⟩ := hpure
    cases hvalue
    subst finalState
    have hprefixSound := hargs hprefixRun hrepresented havailable
    have hbuilt := hbuild hprefixSound hprefixLength
    simpa [hterminalWorld hle] using hbuilt
  · have hover : count < args.length := Nat.lt_of_not_ge hle
    rw [if_neg hle] at hafterPrefix
    have hprefixRepresented : ExtraRepresented ctx prefixState :=
      hrepresented.of_extends
      (hrestExtra prefixOutput.bump resultWorld
        (emitPrefix ∘ emitOp
          (build (prefixAVals.map (·.toAtom prefixOutput)).toArray))
        (.slotA prefixOutput.depth) (args.drop count) hafterPrefix)
    have hprefixSound := hargs hprefixRun hprefixRepresented havailable
    have hbuilt := hbuild hprefixSound hprefixLength
    have hbuiltShared : LowerResultSoundBelow ctx cur limit input
        prefixOutput.bump .shared
        (emitPrefix ∘ emitOp
          (build (prefixAVals.map (·.toAtom prefixOutput)).toArray))
        (.slotA prefixOutput.depth) := by
      simpa [hoverWorld hover] using hbuilt
    have hprefixAvailable := havailable.lowerArgs hprefixRun
    exact hrest hbuiltShared hafterPrefix hrepresented hprefixAvailable.bump

/-- Uniform wrapper for operation builders whose world law holds for every
argument list. -/
theorem knownCallPreservesBelow_succ
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel count : Nat} {build : Array Atom → Op}
    {argWorlds : List Owned} {resultWorld buildWorld : Owned}
    (hargs : LowerArgsPreservesBelow ctx cur limit src fuel)
    (hrest : ApplyRestPreservesBelow ctx cur limit src fuel)
    (hrestExtra : ApplyRestExtraMonotone src fuel)
    (hbuild : ∀ {input output : VEnv} {args : List IxIR0.Expr}
        {emit : Emit} {avs : List AVal},
      LowerArgsSoundBelow ctx cur limit input output
          (((args.take count).zip (padWorlds argWorlds count)).map Prod.snd)
          emit avs →
      LowerResultSoundBelow ctx cur limit input output.bump buildWorld
        (emit ∘ emitOp (build (avs.map (·.toAtom output)).toArray))
        (.slotA output.depth))
    (hterminalWorld : ∀ {args : List IxIR0.Expr},
      args.length ≤ count → buildWorld = resultWorld)
    (hoverWorld : ∀ {args : List IxIR0.Expr},
      count < args.length → buildWorld = .shared) :
    KnownCallPreservesBelow ctx cur limit src (fuel + 1) build count
      argWorlds resultWorld := by
  intro input args state finalState output emit av hrun hrepresented
    havailable
  exact knownCall_run_sound_below hargs hrest hrestExtra
    (fun hsound _ => hbuild (args := args) hsound)
    (fun hle => hterminalWorld hle) (fun hover => hoverWorld hover) hrun
    hrepresented havailable

/-- A partial application consumes every supplied shared argument into a
fresh shared pap. Choosing the known-call prefix length to be the whole
argument list makes the over-application branch impossible. -/
theorem knownCall_papp_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat}
    (hargs : LowerArgsPreservesBelow ctx cur limit src fuel)
    (hrest : ApplyRestPreservesBelow ctx cur limit src fuel)
    (hrestExtra : ApplyRestExtraMonotone src fuel)
    {input output : VEnv} {f : Ixon.Address} {d : Decl}
    {args : List IxIR0.Expr} {emit : Emit} {av : AVal}
    {state finalState : LowSt}
    (hdecl : ctx.decls f = some d)
    (hunder : args.length < declArity d)
    (hrun : (knownCall src (fuel + 1) input (.papp f ·) args.length
      (List.replicate args.length .shared) .shared args).run state =
        .ok (output, emit, av) finalState)
    (hrepresented : ExtraRepresented ctx finalState)
    (havailable : SelfAvailableBelow ctx cur limit input) :
    LowerResultSoundBelow ctx cur limit input output .shared emit av := by
  refine knownCall_run_sound_below
    (build := .papp f) (count := args.length)
    (argWorlds := List.replicate args.length .shared)
    (resultWorld := .shared) (buildWorld := .shared)
    (args := args) hargs hrest hrestExtra ?_ ?_ ?_ hrun hrepresented
      havailable
  · intro prefixOutput emitPrefix prefixAVals hprefixSound hprefixLength
    have hshape := knownCall_prefix_worlds_eq args
      (List.replicate args.length .shared) args.length (by simp)
      (Nat.le_refl _)
    have hzipLength := knownCall_prefix_length_eq args
      (List.replicate args.length .shared) args.length (by simp)
      (Nat.le_refl _)
    have havsLength : prefixAVals.length = args.length :=
      hprefixLength.trans hzipLength
    have hsound : LowerArgsSoundBelow ctx cur limit input prefixOutput
        (List.replicate prefixAVals.length .shared)
        emitPrefix prefixAVals := by
      simpa only [hshape, havsLength] using hprefixSound
    apply hsound.papp_owned hdecl
    simpa [havsLength] using hunder
  · intro _
    rfl
  · intro hover
    omega

/-- A saturated extern prefix consumes homogeneous shared scalar arguments.
Terminal calls return at the demanded world; an excess tail is necessarily
shared by executable `applyRest` inversion. -/
theorem knownCall_extern_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel count : Nat}
    (hargs : LowerArgsPreservesBelow ctx cur limit src fuel)
    (hrest : ApplyRestPreservesBelow ctx cur limit src fuel)
    (hrestExtra : ApplyRestExtraMonotone src fuel)
    {input output : VEnv} {world : Owned} {f : Ixon.Address}
    {args : List IxIR0.Expr} {emit : Emit} {av : AVal}
    {state finalState : LowSt}
    (hcount : count ≤ args.length)
    (hrun : (knownCall src (fuel + 1) input (.extern f ·) count
      (List.replicate count .shared) world args).run state =
        .ok (output, emit, av) finalState)
    (hrepresented : ExtraRepresented ctx finalState)
    (havailable : SelfAvailableBelow ctx cur limit input) :
    LowerResultSoundBelow ctx cur limit input output world emit av := by
  refine knownCall_run_sound_below
    (build := .extern f) (count := count)
    (argWorlds := List.replicate count .shared)
    (resultWorld := world) (buildWorld := world)
    (args := args) hargs hrest hrestExtra ?_ ?_ ?_ hrun hrepresented
      havailable
  · intro prefixOutput emitPrefix prefixAVals hprefixSound hprefixLength
    have hshape := knownCall_prefix_worlds_eq args
      (List.replicate count .shared) count (by simp) hcount
    have hzipLength := knownCall_prefix_length_eq args
      (List.replicate count .shared) count (by simp) hcount
    have havsLength : prefixAVals.length = count :=
      hprefixLength.trans hzipLength
    have hsound : LowerArgsSoundBelow ctx cur limit input prefixOutput
        (List.replicate prefixAVals.length .shared)
        emitPrefix prefixAVals := by
      simpa only [hshape, havsLength] using hprefixSound
    exact hsound.extern_owned
  · intro _
    rfl
  · intro hover
    exact knownCall_over_run_world_shared hover hrun

/-- A saturated constructor prefix consumes a homogeneous telescope in the
node's whole-value world. If an excess application tail exists, successful
execution forces that node world to be shared. -/
theorem knownCall_alloc_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel count : Nat}
    (hargs : LowerArgsPreservesBelow ctx cur limit src fuel)
    (hrest : ApplyRestPreservesBelow ctx cur limit src fuel)
    (hrestExtra : ApplyRestExtraMonotone src fuel)
    {input output : VEnv} {world : Owned} {cid : CtorId}
    {args : List IxIR0.Expr} {emit : Emit} {av : AVal}
    {state finalState : LowSt}
    (hcount : count ≤ args.length)
    (hrun : (knownCall src (fuel + 1) input (.alloc world cid ·) count
      (List.replicate count world) world args).run state =
        .ok (output, emit, av) finalState)
    (hrepresented : ExtraRepresented ctx finalState)
    (havailable : SelfAvailableBelow ctx cur limit input) :
    LowerResultSoundBelow ctx cur limit input output world emit av := by
  refine knownCall_run_sound_below
    (build := .alloc world cid) (count := count)
    (argWorlds := List.replicate count world)
    (resultWorld := world) (buildWorld := world)
    (args := args) hargs hrest hrestExtra ?_ ?_ ?_ hrun hrepresented
      havailable
  · intro prefixOutput emitPrefix prefixAVals hprefixSound hprefixLength
    have hshape := knownCall_prefix_worlds_eq args
      (List.replicate count world) count (by simp) hcount
    have hzipLength := knownCall_prefix_length_eq args
      (List.replicate count world) count (by simp) hcount
    have havsLength : prefixAVals.length = count :=
      hprefixLength.trans hzipLength
    have hsound : LowerArgsSoundBelow ctx cur limit input prefixOutput
        (List.replicate prefixAVals.length world)
        emitPrefix prefixAVals := by
      simpa only [hshape, havsLength] using hprefixSound
    exact hsound.alloc_owned
  · intro _
    rfl
  · intro hover
    exact knownCall_over_run_world_shared hover hrun

/-! ## Executable `lowerSpine` dispatch -/

/-- Flattening one more source application is exactly the recursive
`lowerSpine` judgment on the extended argument list. -/
theorem lowerSpine_app_verified {ctx : Ctx} {cur : FnDef}
    (src : IxIR0.Env) (fuel : Nat) (Γ output : VEnv)
    (world : Owned) (function argument : IxIR0.Expr)
    (args : List IxIR0.Expr) (emit : Emit) (av : AVal)
    (state finalState : LowSt)
    (hrun : (lowerSpine src fuel Γ world function (argument :: args)).run
      state = .ok (output, emit, av) finalState)
    (hsound : LowerResultSound ctx cur Γ output world emit av) :
    (lowerSpine src (Nat.succ fuel) Γ world (.app function argument)
      args).run state = .ok (output, emit, av) finalState ∧
      LowerResultSound ctx cur Γ output world emit av := by
  exact ⟨by simpa [lowerSpine] using hrun, hsound⟩

/-- A syntactic erased spine head evaluates all shared arguments, releases
their owners, and returns erased at either demanded result world. -/
theorem lowerSpine_erased_verified {ctx : Ctx} {cur : FnDef}
    (src : IxIR0.Env) (fuel : Nat) (Γ output : VEnv)
    (world : Owned) (args : List IxIR0.Expr)
    (emitArgs : Emit) (avs : List AVal)
    (state finalState : LowSt)
    (hargsRun :
      (lowerArgs src fuel Γ
        (args.map (fun arg => (arg, Owned.shared)))).run state =
        .ok (output, emitArgs, avs) finalState)
    (hargsSound : LowerArgsSound ctx cur Γ output
      ((args.map (fun arg => (arg, Owned.shared))).map Prod.snd)
      emitArgs avs)
    (hworldsHomogeneous :
      ((args.map (fun arg => (arg, Owned.shared))).map Prod.snd) =
        List.replicate avs.length .shared) :
    (lowerSpine src (Nat.succ (Nat.succ fuel)) Γ world .erased args).run
        state =
        .ok ((releaseAll output avs).1,
          ((_root_.id : Emit) ∘ emitArgs) ∘ (releaseAll output avs).2,
          .constA .erased) finalState ∧
      LowerResultSound ctx cur Γ (releaseAll output avs).1 world
        (((_root_.id : Emit) ∘ emitArgs) ∘ (releaseAll output avs).2)
        (.constA .erased) := by
  have happly := applyRest_erased_verified (ctx := ctx) (cur := cur)
    src fuel Γ Γ output world (_root_.id : Emit) emitArgs args avs
    state finalState hargsRun hargsSound hworldsHomogeneous
    (lower_erased_sound (ctx := ctx) (cur := cur) (Γ := Γ)
      (world := .shared))
  constructor
  · simpa only [lowerSpine] using happly.1
  · exact happly.2

/-- An ordinary source variable (as opposed to `recSelf`) is lowered as a
shared function value and then enters the proved non-erased `applyRest`
path. -/
theorem lowerSpine_var_apply_verified {ctx : Ctx} {cur : FnDef}
    (src : IxIR0.Env) (fuel : Nat)
    (input functionOutput output : VEnv)
    (i abs remaining : Nat) (uses : Uses) (held : Bool)
    (args : List IxIR0.Expr) (emitFunction emitArgs : Emit)
    (function : AVal) (avs : List AVal)
    (state middleState finalState : LowSt)
    (hentry : input.entries[i]? =
      some (.slot abs remaining uses held))
    (hfunctionRun :
      (lowerE src (Nat.succ fuel) input .shared (.var i)).run state =
        .ok (functionOutput, emitFunction, function) middleState)
    (hfunction : LowerResultSound ctx cur input functionOutput .shared
      emitFunction function)
    (hfunctionNe : function ≠ .constA .erased)
    (hargsRun :
      (lowerArgs src fuel functionOutput
        (args.map (fun arg => (arg, Owned.shared)))).run middleState =
        .ok (output, emitArgs, avs) finalState)
    (hargsSound : LowerArgsSound ctx cur functionOutput output
      ((args.map (fun arg => (arg, Owned.shared))).map Prod.snd)
      emitArgs avs)
    (hworldsHomogeneous :
      ((args.map (fun arg => (arg, Owned.shared))).map Prod.snd) =
        List.replicate avs.length .shared)
    (hcontract : ApplyOwnershipContract ctx) :
    (lowerSpine src (Nat.succ (Nat.succ fuel)) input .shared (.var i)
      args).run state =
        .ok (output.bump,
          (emitFunction ∘ emitArgs) ∘
            emitOp (.apply (function.toAtom output)
              (avs.map (·.toAtom output)).toArray),
          .slotA output.depth) finalState ∧
      LowerResultSound ctx cur input output.bump .shared
        ((emitFunction ∘ emitArgs) ∘
          emitOp (.apply (function.toAtom output)
            (avs.map (·.toAtom output)).toArray))
        (.slotA output.depth) := by
  have happly := applyRest_shared_verified (ctx := ctx) (cur := cur)
    src fuel input functionOutput output emitFunction emitArgs function
    args avs middleState finalState hfunctionNe hargsRun hargsSound
    hworldsHomogeneous hfunction hcontract
  constructor
  · simp only [lowerSpine]
    rw [hentry]
    simp only
    rw [estateBindRun, hfunctionRun]
    exact happly.1
  · exact happly.2

/-- Source heads handled by `lowerSpine`'s final dynamic fallback: lower the
head expression normally, then pass its descriptor to `applyRest`. -/
inductive DynamicSpineHead : IxIR0.Expr → Prop where
  | lam (uses : Uses) (body : IxIR0.Expr) :
      DynamicSpineHead (.lam uses body)
  | letE (uses : Uses) (value body : IxIR0.Expr) :
      DynamicSpineHead (.letE uses value body)
  | proj (index : Nat) (value : IxIR0.Expr) :
      DynamicSpineHead (.proj index value)
  | lit (literal : IxIR0.Literal) :
      DynamicSpineHead (.lit literal)

/-- One flattened application node delegates to the predecessor-fuel spine
proof. -/
theorem lowerSpine_app_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat}
    (hspine : LowerSpinePreservesBelow ctx cur limit src fuel)
    {input output : VEnv} {world : Owned}
    {function argument : IxIR0.Expr} {args : List IxIR0.Expr}
    {emit : Emit} {av : AVal} {state finalState : LowSt}
    (hrun : (lowerSpine src (fuel + 1) input world
      (.app function argument) args).run state =
        .ok (output, emit, av) finalState)
    (hrepresented : ExtraRepresented ctx finalState)
    (havailable : SelfAvailableBelow ctx cur limit input) :
    LowerResultSoundBelow ctx cur limit input output world emit av := by
  apply hspine
  · simpa [lowerSpine] using hrun
  · exact hrepresented
  · exact havailable

/-- The syntactic erased spine head is handled entirely by bounded
`applyRest` absorption. -/
theorem lowerSpine_erased_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat}
    (hrest : ApplyRestPreservesBelow ctx cur limit src fuel)
    {input output : VEnv} {world : Owned} {args : List IxIR0.Expr}
    {emit : Emit} {av : AVal} {state finalState : LowSt}
    (hrun : (lowerSpine src (fuel + 1) input world .erased args).run state =
      .ok (output, emit, av) finalState)
    (hrepresented : ExtraRepresented ctx finalState)
    (havailable : SelfAvailableBelow ctx cur limit input) :
    LowerResultSoundBelow ctx cur limit input output world emit av := by
  apply hrest (lower_erased_sound_below (ctx := ctx) (cur := cur)
    (limit := limit) (Γ := input) (world := .shared))
  · simpa [lowerSpine] using hrun
  · exact hrepresented
  · exact havailable

/-- Dynamic fallback heads first use predecessor-fuel `lowerE`, then the
already-derived predecessor-fuel `applyRest` transformer. -/
theorem lowerSpine_dynamic_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat}
    (hexpr : LowerEPreservesBelow ctx cur limit src fuel)
    (hrest : ApplyRestPreservesBelow ctx cur limit src fuel)
    (hrestExtra : ApplyRestExtraMonotone src fuel)
    {input output : VEnv} {world : Owned} {head : IxIR0.Expr}
    {args : List IxIR0.Expr} {emit : Emit} {av : AVal}
    {state finalState : LowSt}
    (hshape : DynamicSpineHead head)
    (hrun : (lowerSpine src (fuel + 1) input world head args).run state =
      .ok (output, emit, av) finalState)
    (hrepresented : ExtraRepresented ctx finalState)
    (havailable : SelfAvailableBelow ctx cur limit input) :
    LowerResultSoundBelow ctx cur limit input output world emit av := by
  cases hshape <;> simp only [lowerSpine] at hrun
  all_goals
    obtain ⟨functionResult, functionState, hfunctionRun, hafterFunction⟩ :=
      estateBindRun_ok_inv hrun
    rcases functionResult with ⟨functionOutput, emitFunction, function⟩
    have hfunctionRepresented : ExtraRepresented ctx functionState :=
      hrepresented.of_extends
      (hrestExtra functionOutput world emitFunction function args
        hafterFunction)
    exact hrest (hexpr hfunctionRun hfunctionRepresented havailable)
      hafterFunction hrepresented (havailable.lowerE hfunctionRun)

/-- An ordinary variable spine head follows the same lower-then-apply path
as the syntactic dynamic fallback. The side condition excludes only the
dedicated `recSelf` entry handled by the static self-call rule. -/
theorem lowerSpine_var_dynamic_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat}
    (hexpr : LowerEPreservesBelow ctx cur limit src fuel)
    (hrest : ApplyRestPreservesBelow ctx cur limit src fuel)
    (hrestExtra : ApplyRestExtraMonotone src fuel)
    {input output : VEnv} {world : Owned} {i : Nat}
    {args : List IxIR0.Expr} {emit : Emit} {av : AVal}
    {state finalState : LowSt}
    (hnotSelf : ∀ arity,
      input.entries[i]? ≠ some (.recSelf arity))
    (hrun : (lowerSpine src (fuel + 1) input world (.var i) args).run
      state = .ok (output, emit, av) finalState)
    (hrepresented : ExtraRepresented ctx finalState)
    (havailable : SelfAvailableBelow ctx cur limit input) :
    LowerResultSoundBelow ctx cur limit input output world emit av := by
  simp only [lowerSpine] at hrun
  cases hentry : input.entries[i]? with
  | none =>
    obtain ⟨functionResult, functionState, hfunctionRun, hafterFunction⟩ :=
      estateBindRun_ok_inv (by simpa [hentry] using hrun)
    rcases functionResult with ⟨functionOutput, emitFunction, function⟩
    have hfunctionRepresented : ExtraRepresented ctx functionState :=
      hrepresented.of_extends
      (hrestExtra functionOutput world emitFunction function args
        hafterFunction)
    exact hrest (hexpr hfunctionRun hfunctionRepresented havailable)
      hafterFunction hrepresented (havailable.lowerE hfunctionRun)
  | some entry =>
    cases entry with
    | recSelf arity => exact (hnotSelf arity hentry).elim
    | slot abs remaining uses held =>
      obtain ⟨functionResult, functionState, hfunctionRun, hafterFunction⟩ :=
        estateBindRun_ok_inv (by simpa [hentry] using hrun)
      rcases functionResult with ⟨functionOutput, emitFunction, function⟩
      have hfunctionRepresented : ExtraRepresented ctx functionState :=
        hrepresented.of_extends
        (hrestExtra functionOutput world emitFunction function args
          hafterFunction)
      exact hrest (hexpr hfunctionRun hfunctionRepresented havailable)
        hafterFunction hrepresented (havailable.lowerE hfunctionRun)

/-- Saturated or over-applied recursive-self dispatch is bounded-sound in
one rule. The successful result-world guard forces the all-shared recursor
boundary, while `knownCall` handles both the terminal and tail-application
shapes. -/
theorem lowerSpine_recSelf_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat}
    (hargs : LowerArgsPreservesBelow ctx cur limit src fuel)
    (hrest : ApplyRestPreservesBelow ctx cur limit src fuel)
    (hrestExtra : ApplyRestExtraMonotone src fuel)
    {input output : VEnv} {world : Owned} {i arity : Nat}
    {args : List IxIR0.Expr} {emit : Emit} {av : AVal}
    {state finalState : LowSt}
    (hentry : input.entries[i]? = some (.recSelf arity))
    (hself : FnOwnershipContractBelow ctx cur
      (List.replicate cur.arity .shared) limit)
    (hresult : cur.result = .shared)
    (hrun : (lowerSpine src (fuel + 2) input world (.var i) args).run
      state = .ok (output, emit, av) finalState)
    (hrepresented : ExtraRepresented ctx finalState)
    (havailable : SelfAvailableBelow ctx cur limit input) :
    LowerResultSoundBelow ctx cur limit input output world emit av := by
  simp only [lowerSpine] at hrun
  rw [hentry] at hrun
  simp only at hrun
  by_cases hunder : args.length < arity
  · rw [if_pos hunder] at hrun
    exact (estateThrowRun_not_ok hrun).elim
  · rw [if_neg hunder] at hrun
    have hcount : arity ≤ args.length := Nat.le_of_not_gt hunder
    cases world with
    | unique =>
      have hrequire :
          (requireResultWorld .shared .unique).run state =
            .error "call result is shared at unique demand" state := by
        rfl
      rw [estateBindRun, hrequire] at hrun
      contradiction
    | shared =>
      have hrequire :
          (requireResultWorld .shared .shared).run state = .ok () state := by
        rfl
      rw [estateBindRun, hrequire] at hrun
      simp only at hrun
      refine knownCall_run_sound_below
        (build := .callSelf) (count := arity)
        (argWorlds := List.replicate arity .shared)
        (resultWorld := .shared) (buildWorld := .shared)
        (args := args) hargs hrest hrestExtra ?_ ?_ ?_ hrun hrepresented
          havailable
      · intro prefixOutput emitPrefix prefixAVals hprefixSound
          hprefixLength
        have hshape := knownCall_prefix_worlds_eq args
          (List.replicate arity .shared) arity (by simp) hcount
        have hzipLength := knownCall_prefix_length_eq args
          (List.replicate arity .shared) arity (by simp) hcount
        have havsLength : prefixAVals.length = arity :=
          hprefixLength.trans hzipLength
        have hsound : LowerArgsSoundBelow ctx cur limit input prefixOutput
            (List.replicate arity .shared) emitPrefix prefixAVals := by
          simpa only [hshape] using hprefixSound
        by_cases harity : arity = cur.arity
        · have hself' : FnOwnershipContractBelow ctx cur
              (List.replicate arity .shared) limit := by
            simpa [harity] using hself
          simpa [hresult] using hsound.callSelf_owned hself'
        · have hmismatch : prefixAVals.length ≠ cur.arity := by
            intro heq
            exact harity (havsLength.symm.trans heq)
          simpa [hresult] using
            hsound.callSelf_arity_mismatch hmismatch
      · intro _
        rfl
      · intro _
        rfl

/-- Saturated and over-applied source definitions share one bounded direct-
call proof. The executable world guard supplies the terminal result equality
or the shared intermediate world required before applying an excess tail. -/
theorem lowerSpine_ref_defn_call_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat}
    (hargs : LowerArgsPreservesBelow ctx cur limit src fuel)
    (hrest : ApplyRestPreservesBelow ctx cur limit src fuel)
    (hrestExtra : ApplyRestExtraMonotone src fuel)
    (hdecls : SourceDeclContractsBelow src ctx limit)
    {input output : VEnv} {world result : Owned} {f : Ixon.Address}
    {body : IxIR0.Expr} {args : List IxIR0.Expr}
    {emit : Emit} {av : AVal} {state finalState : LowSt}
    (hsrc : src f = some (.defn result body))
    (hcount : lamArity body ≤ args.length)
    (hrun : (lowerSpine src (fuel + 2) input world (.ref f) args).run
      state = .ok (output, emit, av) finalState)
    (hrepresented : ExtraRepresented ctx finalState)
    (havailable : SelfAvailableBelow ctx cur limit input) :
    LowerResultSoundBelow ctx cur limit input output world emit av := by
  obtain ⟨d, hdecl, harity, hresult, hcontract⟩ := hdecls.defn hsrc
  simp only [lowerSpine] at hrun
  rw [hsrc] at hrun
  simp only at hrun
  rw [if_neg (Nat.not_lt.mpr hcount)] at hrun
  obtain ⟨checked, nextState, hrequireRun, hknownRun⟩ :=
    estateBindRun_ok_inv hrun
  cases checked
  obtain ⟨hguard, _⟩ := requireResultWorld_run_ok_inv hrequireRun
  refine knownCall_run_sound_below
    (build := .call f) (count := lamArity body)
    (argWorlds := (lamUses body).map worldOfUses)
    (resultWorld := world) (buildWorld := result)
    (args := args) hargs hrest hrestExtra ?_ ?_ ?_ hknownRun hrepresented
      havailable
  · intro prefixOutput emitPrefix prefixAVals hprefixSound _
    have hshape := knownCall_prefix_worlds_eq args
      ((lamUses body).map worldOfUses) (lamArity body)
      (by simp) hcount
    have hsound : LowerArgsSoundBelow ctx cur limit input prefixOutput
        ((lamUses body).map worldOfUses) emitPrefix prefixAVals := by
      simpa only [hshape] using hprefixSound
    simpa [hresult] using hsound.call_owned hdecl hcontract
  · intro hterminal
    have heq : args.length = lamArity body :=
      Nat.le_antisymm hterminal hcount
    simpa [heq] using hguard
  · intro hover
    have hne : args.length ≠ lamArity body := Nat.ne_of_gt hover
    simpa [hne] using hguard

/-- Under-applied source definitions that successfully pass the shared-
function guards consume all supplied arguments into a bounded pap node. -/
theorem lowerSpine_ref_defn_partial_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat}
    (hargs : LowerArgsPreservesBelow ctx cur limit src fuel)
    (hrest : ApplyRestPreservesBelow ctx cur limit src fuel)
    (hrestExtra : ApplyRestExtraMonotone src fuel)
    (hdecls : SourceDeclContractsBelow src ctx limit)
    {input output : VEnv} {world result : Owned} {f : Ixon.Address}
    {body : IxIR0.Expr} {args : List IxIR0.Expr}
    {emit : Emit} {av : AVal} {state finalState : LowSt}
    (hsrc : src f = some (.defn result body))
    (hunder : args.length < lamArity body)
    (hrun : (lowerSpine src (fuel + 2) input world (.ref f) args).run
      state = .ok (output, emit, av) finalState)
    (hrepresented : ExtraRepresented ctx finalState)
    (havailable : SelfAvailableBelow ctx cur limit input) :
    LowerResultSoundBelow ctx cur limit input output world emit av := by
  obtain ⟨d, hdecl, harity, _, _⟩ := hdecls.defn hsrc
  simp only [lowerSpine] at hrun
  rw [hsrc] at hrun
  simp only at hrun
  rw [if_pos hunder] at hrun
  have huuEq : (Owned.unique == Owned.unique) = true := by decide
  have hsuEq : (Owned.shared == Owned.unique) = false := by decide
  cases world with
  | unique =>
    apply False.elim
    apply estateThrowRun_not_ok
    simpa [huuEq] using hrun
  | shared =>
    cases result with
    | unique =>
      apply False.elim
      apply estateThrowRun_not_ok
      simpa [hsuEq, huuEq] using hrun
    | shared =>
      cases hp : papSafe body with
      | false =>
        apply False.elim
        apply estateThrowRun_not_ok
        simpa [hsuEq, hp] using hrun
      | true =>
        have hknown :
            (knownCall src (fuel + 1) input (.papp f ·) args.length
              (List.replicate args.length .shared) .shared args).run state =
              .ok (output, emit, av) finalState := by
          simpa [hsuEq, hp] using hrun
        exact knownCall_papp_run_sound_below
          (f := f) (d := .fn d) (args := args) hargs hrest hrestExtra
          hdecl (by simpa [declArity, harity] using hunder) hknown
          hrepresented havailable

/-- Saturated and over-applied recursor references are ordinary bounded
all-shared direct calls once the generated recursor declaration is recovered
from the source/target contract environment. -/
theorem lowerSpine_ref_recursor_call_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat}
    (hargs : LowerArgsPreservesBelow ctx cur limit src fuel)
    (hrest : ApplyRestPreservesBelow ctx cur limit src fuel)
    (hrestExtra : ApplyRestExtraMonotone src fuel)
    (hdecls : SourceDeclContractsBelow src ctx limit)
    {input output : VEnv} {world : Owned} {f : Ixon.Address}
    {numArgs : Nat} {natLit : Bool} {rules : Array IxIR0.RecRule}
    {args : List IxIR0.Expr} {emit : Emit} {av : AVal}
    {state finalState : LowSt}
    (hsrc : src f = some (.recursor numArgs natLit rules))
    (hcount : numArgs + 1 ≤ args.length)
    (hrun : (lowerSpine src (fuel + 2) input world (.ref f) args).run
      state = .ok (output, emit, av) finalState)
    (hrepresented : ExtraRepresented ctx finalState)
    (havailable : SelfAvailableBelow ctx cur limit input) :
    LowerResultSoundBelow ctx cur limit input output world emit av := by
  obtain ⟨d, hdecl, harity, hresult, hcontract⟩ :=
    hdecls.recursor hsrc
  simp only [lowerSpine] at hrun
  rw [hsrc] at hrun
  simp only at hrun
  rw [if_neg (Nat.not_lt.mpr hcount)] at hrun
  obtain ⟨checked, nextState, hrequireRun, hknownRun⟩ :=
    estateBindRun_ok_inv hrun
  cases checked
  obtain ⟨hguard, _⟩ := requireResultWorld_run_ok_inv hrequireRun
  refine knownCall_run_sound_below
    (build := .call f) (count := numArgs + 1)
    (argWorlds := List.replicate (numArgs + 1) .shared)
    (resultWorld := world) (buildWorld := .shared)
    (args := args) hargs hrest hrestExtra ?_ ?_ ?_ hknownRun hrepresented
      havailable
  · intro prefixOutput emitPrefix prefixAVals hprefixSound _
    have hshape := knownCall_prefix_worlds_eq args
      (List.replicate (numArgs + 1) .shared) (numArgs + 1)
      (by simp) hcount
    have hsound : LowerArgsSoundBelow ctx cur limit input prefixOutput
        (List.replicate (numArgs + 1) .shared)
        emitPrefix prefixAVals := by
      simpa only [hshape] using hprefixSound
    simpa [hresult] using hsound.call_owned hdecl hcontract
  · intro hterminal
    have heq : args.length = numArgs + 1 :=
      Nat.le_antisymm hterminal hcount
    simpa [heq] using hguard
  · intro _
    rfl

/-- An under-applied recursor is a shared pap over all supplied arguments;
its target declaration and strict under-application bound come from the
bounded generated-recursor contract. -/
theorem lowerSpine_ref_recursor_partial_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat}
    (hargs : LowerArgsPreservesBelow ctx cur limit src fuel)
    (hrest : ApplyRestPreservesBelow ctx cur limit src fuel)
    (hrestExtra : ApplyRestExtraMonotone src fuel)
    (hdecls : SourceDeclContractsBelow src ctx limit)
    {input output : VEnv} {world : Owned} {f : Ixon.Address}
    {numArgs : Nat} {natLit : Bool} {rules : Array IxIR0.RecRule}
    {args : List IxIR0.Expr} {emit : Emit} {av : AVal}
    {state finalState : LowSt}
    (hsrc : src f = some (.recursor numArgs natLit rules))
    (hunder : args.length < numArgs + 1)
    (hrun : (lowerSpine src (fuel + 2) input world (.ref f) args).run
      state = .ok (output, emit, av) finalState)
    (hrepresented : ExtraRepresented ctx finalState)
    (havailable : SelfAvailableBelow ctx cur limit input) :
    LowerResultSoundBelow ctx cur limit input output world emit av := by
  obtain ⟨d, hdecl, harity, _, _⟩ := hdecls.recursor hsrc
  simp only [lowerSpine] at hrun
  rw [hsrc] at hrun
  simp only at hrun
  rw [if_pos hunder] at hrun
  have huuEq : (Owned.unique == Owned.unique) = true := by decide
  have hsuEq : (Owned.shared == Owned.unique) = false := by decide
  cases world with
  | unique =>
    apply False.elim
    apply estateThrowRun_not_ok
    simpa [huuEq] using hrun
  | shared =>
    have hknown :
        (knownCall src (fuel + 1) input (.papp f ·) args.length
          (List.replicate args.length .shared) .shared args).run state =
          .ok (output, emit, av) finalState := by
      simpa [hsuEq] using hrun
    exact knownCall_papp_run_sound_below
      (f := f) (d := .fn d) (args := args) hargs hrest hrestExtra hdecl
      (by simpa [declArity, harity] using hunder) hknown hrepresented
      havailable

/-- Saturated and over-applied extern references use the homogeneous bounded
extern consumer; the excess-tail shared-world fact is recovered from the
successful run itself. -/
theorem lowerSpine_ref_extern_call_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat}
    (hargs : LowerArgsPreservesBelow ctx cur limit src fuel)
    (hrest : ApplyRestPreservesBelow ctx cur limit src fuel)
    (hrestExtra : ApplyRestExtraMonotone src fuel)
    {input output : VEnv} {world : Owned} {f : Ixon.Address}
    {arity : Nat} {args : List IxIR0.Expr} {emit : Emit} {av : AVal}
    {state finalState : LowSt}
    (hsrc : src f = some (.extern arity))
    (hcount : arity ≤ args.length)
    (hrun : (lowerSpine src (fuel + 2) input world (.ref f) args).run
      state = .ok (output, emit, av) finalState)
    (hrepresented : ExtraRepresented ctx finalState)
    (havailable : SelfAvailableBelow ctx cur limit input) :
    LowerResultSoundBelow ctx cur limit input output world emit av := by
  have hknown :
      (knownCall src (fuel + 1) input (.extern f ·) arity
        (List.replicate arity .shared) world args).run state =
        .ok (output, emit, av) finalState := by
    simpa [lowerSpine, hsrc, Nat.not_lt.mpr hcount] using hrun
  exact knownCall_extern_run_sound_below
    (count := arity) hargs hrest hrestExtra hcount hknown hrepresented
      havailable

/-- Under-applied extern references are shared paps backed by the extern
declaration supplied by the source/target layout. -/
theorem lowerSpine_ref_extern_partial_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat}
    (hargs : LowerArgsPreservesBelow ctx cur limit src fuel)
    (hrest : ApplyRestPreservesBelow ctx cur limit src fuel)
    (hrestExtra : ApplyRestExtraMonotone src fuel)
    (hdecls : SourceDeclContractsBelow src ctx limit)
    {input output : VEnv} {world : Owned} {f : Ixon.Address}
    {arity : Nat} {args : List IxIR0.Expr} {emit : Emit} {av : AVal}
    {state finalState : LowSt}
    (hsrc : src f = some (.extern arity))
    (hunder : args.length < arity)
    (hrun : (lowerSpine src (fuel + 2) input world (.ref f) args).run
      state = .ok (output, emit, av) finalState)
    (hrepresented : ExtraRepresented ctx finalState)
    (havailable : SelfAvailableBelow ctx cur limit input) :
    LowerResultSoundBelow ctx cur limit input output world emit av := by
  have hdecl := hdecls.extern hsrc
  simp only [lowerSpine] at hrun
  rw [hsrc] at hrun
  simp only at hrun
  rw [if_pos hunder] at hrun
  have huuEq : (Owned.unique == Owned.unique) = true := by decide
  have hsuEq : (Owned.shared == Owned.unique) = false := by decide
  cases world with
  | unique =>
    apply False.elim
    apply estateThrowRun_not_ok
    simpa [huuEq] using hrun
  | shared =>
    have hknown :
        (knownCall src (fuel + 1) input (.papp f ·) args.length
          (List.replicate args.length .shared) .shared args).run state =
          .ok (output, emit, av) finalState := by
      simpa [hsuEq] using hrun
    exact knownCall_papp_run_sound_below
      (f := f) (d := .extern arity) (args := args) hargs hrest hrestExtra
      hdecl (by simpa [declArity] using hunder) hknown hrepresented
      havailable

/-- Saturated and over-applied constructors lower through the bounded
homogeneous allocation rule at the demanded whole-value world. -/
theorem lowerSpine_ref_ctor_alloc_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat}
    (hargs : LowerArgsPreservesBelow ctx cur limit src fuel)
    (hrest : ApplyRestPreservesBelow ctx cur limit src fuel)
    (hrestExtra : ApplyRestExtraMonotone src fuel)
    {input output : VEnv} {world : Owned} {f : Ixon.Address}
    {tag arity : Nat} {args : List IxIR0.Expr} {emit : Emit} {av : AVal}
    {state finalState : LowSt}
    (hsrc : src f = some (.ctor tag arity))
    (hcount : arity ≤ args.length)
    (hrun : (lowerSpine src (fuel + 2) input world (.ref f) args).run
      state = .ok (output, emit, av) finalState)
    (hrepresented : ExtraRepresented ctx finalState)
    (havailable : SelfAvailableBelow ctx cur limit input) :
    LowerResultSoundBelow ctx cur limit input output world emit av := by
  have hknown :
      (knownCall src (fuel + 1) input
        (.alloc world (ctorIdOf f tag) ·) arity
        (List.replicate arity world) world args).run state =
        .ok (output, emit, av) finalState := by
    simpa [lowerSpine, hsrc, Nat.not_lt.mpr hcount] using hrun
  exact knownCall_alloc_run_sound_below
    (count := arity) hargs hrest hrestExtra hcount hknown hrepresented
      havailable

/-- Under-applied constructors use the statefully memoized eta-wrapper. The
whole-program layout need only certify the declaration and arity of the
wrapper actually returned by that successful lookup. -/
theorem lowerSpine_ref_ctor_partial_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat}
    (hargs : LowerArgsPreservesBelow ctx cur limit src fuel)
    (hrest : ApplyRestPreservesBelow ctx cur limit src fuel)
    (hrestExtra : ApplyRestExtraMonotone src fuel)
    (hknownExtra : KnownCallExtraMonotone src (fuel + 1))
    {input output : VEnv} {world : Owned} {f : Ixon.Address}
    {tag arity : Nat} {args : List IxIR0.Expr} {emit : Emit} {av : AVal}
    {state finalState : LowSt}
    (hsrc : src f = some (.ctor tag arity))
    (hunder : args.length < arity)
    (hrun : (lowerSpine src (fuel + 2) input world (.ref f) args).run
      state = .ok (output, emit, av) finalState)
    (hrepresented : ExtraRepresented ctx finalState)
    (havailable : SelfAvailableBelow ctx cur limit input) :
    LowerResultSoundBelow ctx cur limit input output world emit av := by
  simp only [lowerSpine] at hrun
  rw [hsrc] at hrun
  simp only at hrun
  rw [if_pos hunder] at hrun
  have huuEq : (Owned.unique == Owned.unique) = true := by decide
  have hsuEq : (Owned.shared == Owned.unique) = false := by decide
  cases world with
  | unique =>
    apply False.elim
    apply estateThrowRun_not_ok
    simpa [huuEq] using hrun
  | shared =>
    have hrun' :
        ((wrapperFor f tag arity) >>= fun wrapper =>
          knownCall src (fuel + 1) input (.papp wrapper ·) args.length
            (List.replicate args.length .shared) .shared args).run state =
          .ok (output, emit, av) finalState := by
      simpa [hsuEq] using hrun
    obtain ⟨wrapper, wrapperState, hwrapperRun, hknownRun⟩ :=
      estateBindRun_ok_inv hrun'
    have hmemo : (⟨f, tag, arity, wrapper⟩ : WrapperMemo) ∈
        finalState.wrappers :=
      (hknownExtra input (.papp wrapper ·) args.length
        (List.replicate args.length .shared) .shared args
        hknownRun).wrapper_mem (wrapperFor_memo_mem hwrapperRun)
    have hdecl := hrepresented.wrapper hmemo
    exact knownCall_papp_run_sound_below
      (f := wrapper) (d := ctorWrapperDecl f tag arity) (args := args)
      hargs hrest hrestExtra hdecl
      (by simpa [ctorWrapperDecl, declArity] using hunder) hknownRun
      hrepresented havailable

/-- Complete bounded `.ref` spine dispatch. Source declarations select the
proved definition, constructor, recursor, or extern family; unknown
references cannot produce a successful lowering run. -/
theorem lowerSpine_ref_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat}
    (hargs : LowerArgsPreservesBelow ctx cur limit src fuel)
    (hargsExtra : LowerArgsExtraMonotone src fuel)
    (hrest : ApplyRestPreservesBelow ctx cur limit src fuel)
    (hrestExtra : ApplyRestExtraMonotone src fuel)
    (hdecls : SourceDeclContractsBelow src ctx limit)
    {input output : VEnv} {world : Owned} {f : Ixon.Address}
    {args : List IxIR0.Expr} {emit : Emit} {av : AVal}
    {state finalState : LowSt}
    (hrun : (lowerSpine src (fuel + 2) input world (.ref f) args).run
      state = .ok (output, emit, av) finalState)
    (hrepresented : ExtraRepresented ctx finalState)
    (havailable : SelfAvailableBelow ctx cur limit input) :
    LowerResultSoundBelow ctx cur limit input output world emit av := by
  cases hsrc : src f with
  | none =>
    apply False.elim
    apply estateThrowRun_not_ok
    simpa [lowerSpine, hsrc] using hrun
  | some source =>
    cases source with
    | defn result body =>
      by_cases hunder : args.length < lamArity body
      · exact lowerSpine_ref_defn_partial_run_sound_below
          hargs hrest hrestExtra hdecls hsrc hunder hrun hrepresented
          havailable
      · exact lowerSpine_ref_defn_call_run_sound_below
          hargs hrest hrestExtra hdecls hsrc (Nat.le_of_not_gt hunder)
          hrun hrepresented havailable
    | ctor tag arity =>
      by_cases hunder : args.length < arity
      · exact lowerSpine_ref_ctor_partial_run_sound_below
          hargs hrest hrestExtra
          (knownCallExtraMonotone_succ hargsExtra hrestExtra)
          hsrc hunder hrun hrepresented havailable
      · exact lowerSpine_ref_ctor_alloc_run_sound_below
          hargs hrest hrestExtra hsrc (Nat.le_of_not_gt hunder) hrun
          hrepresented havailable
    | recursor numArgs natLit rules =>
      by_cases hunder : args.length < numArgs + 1
      · exact lowerSpine_ref_recursor_partial_run_sound_below
          hargs hrest hrestExtra hdecls hsrc hunder hrun hrepresented
          havailable
      · exact lowerSpine_ref_recursor_call_run_sound_below
          hargs hrest hrestExtra hdecls hsrc (Nat.le_of_not_gt hunder)
          hrun hrepresented havailable
    | extern arity =>
      by_cases hunder : args.length < arity
      · exact lowerSpine_ref_extern_partial_run_sound_below
          hargs hrest hrestExtra hdecls hsrc hunder hrun hrepresented
          havailable
      · exact lowerSpine_ref_extern_call_run_sound_below
          hargs hrest hrestExtra hsrc (Nat.le_of_not_gt hunder) hrun
          hrepresented havailable

/-- One complete bounded `lowerSpine` step. All syntactic dispatch families
are now connected; the two generated-environment obligations are explicit:
`recSelf` entries must name the current shared contract, and a state-created
constructor wrapper must be represented in the final target context. -/
theorem lowerSpine_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat}
    (hspine : LowerSpinePreservesBelow ctx cur limit src (fuel + 1))
    (hexpr : LowerEPreservesBelow ctx cur limit src (fuel + 1))
    (hargs : LowerArgsPreservesBelow ctx cur limit src fuel)
    (hargsExtra : LowerArgsExtraMonotone src fuel)
    (hrest : ApplyRestPreservesBelow ctx cur limit src fuel)
    (hrestNext : ApplyRestPreservesBelow ctx cur limit src (fuel + 1))
    (hrestExtra : ApplyRestExtraMonotone src fuel)
    (hrestNextExtra : ApplyRestExtraMonotone src (fuel + 1))
    (hdecls : SourceDeclContractsBelow src ctx limit)
    {input output : VEnv} {world : Owned} {head : IxIR0.Expr}
    {args : List IxIR0.Expr} {emit : Emit} {av : AVal}
    {state finalState : LowSt}
    (hrun : (lowerSpine src (fuel + 2) input world head args).run state =
      .ok (output, emit, av) finalState)
    (hrepresented : ExtraRepresented ctx finalState)
    (havailable : SelfAvailableBelow ctx cur limit input) :
    LowerResultSoundBelow ctx cur limit input output world emit av := by
  cases head with
  | var i =>
    cases hentry : input.entries[i]? with
    | none =>
      apply lowerSpine_var_dynamic_run_sound_below hexpr hrestNext
        hrestNextExtra
      · intro arity hrecSelf
        rw [hentry] at hrecSelf
        contradiction
      · exact hrun
      · exact hrepresented
      · exact havailable
    | some entry =>
      cases entry with
      | recSelf arity =>
        cases havailable with
        | inl hself =>
          obtain ⟨hresult, hcontract⟩ := hself
          exact lowerSpine_recSelf_run_sound_below
            hargs hrest hrestExtra hentry hcontract hresult hrun hrepresented
            (SelfAvailableBelow.of_contract ⟨hresult, hcontract⟩)
        | inr hno => exact (hno i arity hentry).elim
      | slot abs remaining uses held =>
        apply lowerSpine_var_dynamic_run_sound_below hexpr hrestNext
          hrestNextExtra
        · intro arity hrecSelf
          rw [hentry] at hrecSelf
          simp at hrecSelf
        · exact hrun
        · exact hrepresented
        · exact havailable
  | ref f =>
    exact lowerSpine_ref_run_sound_below
      hargs hargsExtra hrest hrestExtra hdecls hrun hrepresented havailable
  | app function argument =>
    exact lowerSpine_app_run_sound_below hspine hrun hrepresented havailable
  | lam uses body =>
    exact lowerSpine_dynamic_run_sound_below hexpr hrestNext hrestNextExtra
      (.lam uses body) hrun hrepresented havailable
  | letE uses value body =>
    exact lowerSpine_dynamic_run_sound_below hexpr hrestNext hrestNextExtra
      (.letE uses value body) hrun hrepresented havailable
  | proj index value =>
    exact lowerSpine_dynamic_run_sound_below hexpr hrestNext hrestNextExtra
      (.proj index value) hrun hrepresented havailable
  | lit literal =>
    exact lowerSpine_dynamic_run_sound_below hexpr hrestNext hrestNextExtra
      (.lit literal) hrun hrepresented havailable
  | erased =>
    exact lowerSpine_erased_run_sound_below hrestNext hrun hrepresented
      havailable

/-- Standalone reference lowering is the empty-argument spine dispatch with
two extra administrative compiler-fuel steps for `knownCall` and its empty
`lowerArgs` prefix. -/
theorem lowerE_ref_run_to_lowerSpine_nil
    {src : IxIR0.Env} {fuel : Nat} {input output : VEnv}
    {world : Owned} {f : Ixon.Address} {emit : Emit} {av : AVal}
    {state finalState : LowSt}
    (hrun : (lowerE src (fuel + 1) input world (.ref f)).run state =
      .ok (output, emit, av) finalState) :
    (lowerSpine src (fuel + 3) input world (.ref f) []).run state =
      .ok (output, emit, av) finalState := by
  cases hsrc : src f with
  | none =>
    apply False.elim
    apply estateThrowRun_not_ok
    simpa [lowerE, hsrc] using hrun
  | some source =>
    cases source with
    | defn result body =>
      cases hn : lamArity body with
      | zero =>
        simpa [lowerE, lowerSpine, knownCall, lowerArgs, hsrc, hn,
          padWorlds, Function.comp_def] using hrun
      | succ n =>
        simpa [lowerE, lowerSpine, knownCall, lowerArgs, hsrc, hn,
          padWorlds, Function.comp_def] using hrun
    | ctor tag arity =>
      cases arity with
      | zero =>
        simpa [lowerE, lowerSpine, knownCall, lowerArgs, hsrc,
          padWorlds, Function.comp_def] using hrun
      | succ arity =>
        simpa [lowerE, lowerSpine, knownCall, lowerArgs, hsrc,
          padWorlds, Function.comp_def] using hrun
    | recursor numArgs natLit rules =>
      simpa [lowerE, lowerSpine, knownCall, lowerArgs, hsrc,
        padWorlds, Function.comp_def] using hrun
    | extern arity =>
      cases arity with
      | zero =>
        simpa [lowerE, lowerSpine, knownCall, lowerArgs, hsrc,
          padWorlds, Function.comp_def] using hrun
      | succ arity =>
        simpa [lowerE, lowerSpine, knownCall, lowerArgs, hsrc,
          padWorlds, Function.comp_def] using hrun

/-- Every successful standalone source reference inherits bounded soundness
from complete empty-spine dispatch. -/
theorem lowerE_ref_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat}
    (hargs : LowerArgsPreservesBelow ctx cur limit src (fuel + 1))
    (hargsExtra : LowerArgsExtraMonotone src (fuel + 1))
    (hrest : ApplyRestPreservesBelow ctx cur limit src (fuel + 1))
    (hrestExtra : ApplyRestExtraMonotone src (fuel + 1))
    (hdecls : SourceDeclContractsBelow src ctx limit)
    {input output : VEnv} {world : Owned} {f : Ixon.Address}
    {emit : Emit} {av : AVal} {state finalState : LowSt}
    (hrun : (lowerE src (fuel + 1) input world (.ref f)).run state =
      .ok (output, emit, av) finalState)
    (hrepresented : ExtraRepresented ctx finalState)
    (havailable : SelfAvailableBelow ctx cur limit input) :
    LowerResultSoundBelow ctx cur limit input output world emit av := by
  apply lowerSpine_ref_run_sound_below hargs hargsExtra hrest hrestExtra
    hdecls
  · exact lowerE_ref_run_to_lowerSpine_nil hrun
  · exact hrepresented
  · exact havailable

/-- Successful literal lowering is bounded-sound at every contract limit. -/
theorem lowerE_lit_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat} {input output : VEnv} {world : Owned}
    {literal : IxIR0.Literal} {emit : Emit} {av : AVal}
    {state finalState : LowSt}
    (hrun : (lowerE src (fuel + 1) input world (.lit literal)).run state =
      .ok (output, emit, av) finalState) :
    LowerResultSoundBelow ctx cur limit input output world emit av := by
  have hpure :
      (input, (_root_.id : Emit), AVal.constA (.lit literal)) =
          (output, emit, av) ∧
        state = finalState := by
    simpa [lowerE] using hrun
  obtain ⟨hvalue, hstate⟩ := hpure
  cases hvalue
  subst finalState
  exact lower_lit_sound_below

/-- Semantic literal branch: the source evaluator returns the same literal
the target lowers to an environment-independent scalar. -/
theorem lowerE_lit_run_value_sound
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {src : IxIR0.Env}
    {fuel : Nat} {input output : VEnv} {world : Owned}
    {literal : IxIR0.Literal} {emit : Emit} {av : AVal}
    {state finalState : LowSt} {sourceEnv : List IxIR0.Value}
    (hrun : (lowerE src (fuel + 1) input world (.lit literal)).run state =
      .ok (output, emit, av) finalState) :
    LowerResultValueSound funRel recSelfRel ctx cur input output
      sourceEnv sourceEnv (.lit literal) world emit av := by
  have hpure :
      (input, (_root_.id : Emit), AVal.constA (.lit literal)) =
          (output, emit, av) ∧
        state = finalState := by
    simpa [lowerE] using hrun
  obtain ⟨hvalue, hstate⟩ := hpure
  cases hvalue
  subst finalState
  exact lower_lit_value_sound

/-- Successful erased lowering is bounded-sound at every contract limit. -/
theorem lowerE_erased_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat} {input output : VEnv} {world : Owned}
    {emit : Emit} {av : AVal} {state finalState : LowSt}
    (hrun : (lowerE src (fuel + 1) input world .erased).run state =
      .ok (output, emit, av) finalState) :
    LowerResultSoundBelow ctx cur limit input output world emit av := by
  have hpure :
      (input, (_root_.id : Emit), AVal.constA .erased) =
          (output, emit, av) ∧
        state = finalState := by
    simpa [lowerE] using hrun
  obtain ⟨hvalue, hstate⟩ := hpure
  cases hvalue
  subst finalState
  exact lower_erased_sound_below

/-- Semantic erased branch: `◻` on both sides, with no heap participation. -/
theorem lowerE_erased_run_value_sound
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {src : IxIR0.Env}
    {fuel : Nat} {input output : VEnv} {world : Owned}
    {emit : Emit} {av : AVal} {state finalState : LowSt}
    {sourceEnv : List IxIR0.Value}
    (hrun : (lowerE src (fuel + 1) input world .erased).run state =
      .ok (output, emit, av) finalState) :
    LowerResultValueSound funRel recSelfRel ctx cur input output
      sourceEnv sourceEnv .erased world emit av := by
  have hpure :
      (input, (_root_.id : Emit), AVal.constA .erased) =
          (output, emit, av) ∧
        state = finalState := by
    simpa [lowerE] using hrun
  obtain ⟨hvalue, hstate⟩ := hpure
  cases hvalue
  subst finalState
  exact lower_erased_value_sound

/-- Every successful variable lowering branch is bounded-sound. Impossible
entry states and ownership mismatches are discharged from the successful
monadic run; final uses move an owner and repeated shared uses retain it. -/
theorem lowerE_var_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat} {input output : VEnv} {world : Owned} {i : Nat}
    {emit : Emit} {av : AVal} {state finalState : LowSt}
    (hrun : (lowerE src (fuel + 1) input world (.var i)).run state =
      .ok (output, emit, av) finalState) :
    LowerResultSoundBelow ctx cur limit input output world emit av := by
  have hssNe : (Owned.shared != Owned.shared) = false := by decide
  have huuNe : (Owned.unique != Owned.unique) = false := by decide
  have hsuNe : (Owned.shared != Owned.unique) = true := by decide
  have husNe : (Owned.unique != Owned.shared) = true := by decide
  have hsuEq : (Owned.shared == Owned.unique) = false := by decide
  have huuEq : (Owned.unique == Owned.unique) = true := by decide
  cases hentry : input.entries[i]? with
  | none =>
    apply False.elim
    apply estateThrowRun_not_ok
    simpa [lowerE, hentry] using hrun
  | some entry =>
    cases entry with
    | recSelf arity =>
      apply False.elim
      apply estateThrowRun_not_ok
      simpa [lowerE, hentry] using hrun
    | slot abs remaining uses held =>
      cases held with
      | false =>
        apply False.elim
        apply estateThrowRun_not_ok
        simpa [lowerE, hentry] using hrun
      | true =>
        by_cases hworld : worldOfUses uses = world
        · subst world
          have hsame :
              (worldOfUses uses != worldOfUses uses) = false := by
            cases uses <;> decide
          cases remaining with
          | zero =>
            apply False.elim
            apply estateThrowRun_not_ok
            simpa [lowerE, hentry, hsame] using hrun
          | succ remaining =>
            cases remaining with
            | zero =>
              have hpure :
                  (input.setEntry i (.slot abs 0 uses false),
                    (_root_.id : Emit), AVal.slotA abs) =
                      (output, emit, av) ∧ state = finalState := by
                simpa [lowerE, hentry, hsame] using hrun
              obtain ⟨hvalue, hstate⟩ := hpure
              cases hvalue
              subst finalState
              exact lower_var_move_sound_below hentry
            | succ remaining =>
              cases uses with
              | erased =>
                have heq :
                    (Owned.shared == Owned.unique) = false := by decide
                have hpure :
                    let input' := input.setEntry i
                      (.slot abs (Nat.succ remaining) .erased true)
                    (input'.bump,
                      emitOp (.dup (.var (input'.rel abs))),
                      AVal.slotA input'.depth) = (output, emit, av) ∧
                      state = finalState := by
                  simpa [lowerE, hentry, worldOfUses, hsame, heq,
                    hssNe, huuNe, hsuNe, husNe, hsuEq, huuEq]
                    using hrun
                dsimp only at hpure
                obtain ⟨hvalue, hstate⟩ := hpure
                cases hvalue
                subst finalState
                exact lower_var_shared_dup_sound_below (by rfl) hentry
              | linear =>
                have heq :
                    (Owned.unique == Owned.unique) = true := by decide
                apply False.elim
                apply estateThrowRun_not_ok
                simpa [lowerE, hentry, worldOfUses, hsame, heq,
                  hssNe, huuNe, hsuNe, husNe, hsuEq, huuEq]
                  using hrun
              | affine =>
                have heq :
                    (Owned.unique == Owned.unique) = true := by decide
                apply False.elim
                apply estateThrowRun_not_ok
                simpa [lowerE, hentry, worldOfUses, hsame, heq,
                  hssNe, huuNe, hsuNe, husNe, hsuEq, huuEq]
                  using hrun
              | many =>
                have heq :
                    (Owned.shared == Owned.unique) = false := by decide
                have hpure :
                    let input' := input.setEntry i
                      (.slot abs (Nat.succ remaining) .many true)
                    (input'.bump,
                      emitOp (.dup (.var (input'.rel abs))),
                      AVal.slotA input'.depth) = (output, emit, av) ∧
                      state = finalState := by
                  simpa [lowerE, hentry, worldOfUses, hsame, heq,
                    hssNe, huuNe, hsuNe, husNe, hsuEq, huuEq]
                    using hrun
                dsimp only at hpure
                obtain ⟨hvalue, hstate⟩ := hpure
                cases hvalue
                subst finalState
                exact lower_var_shared_dup_sound_below (by rfl) hentry
        · have hdiff : (worldOfUses uses != world) = true := by
            cases uses <;> cases world <;>
              simp_all [worldOfUses] <;> decide
          cases uses <;> cases world
          all_goals
            try { exact (hworld (by rfl)).elim }
          all_goals
            apply False.elim
            apply estateThrowRun_not_ok
            simpa [lowerE, hentry, worldOfUses, hdiff, hssNe, huuNe,
              hsuNe, husNe, hsuEq, huuEq] using hrun

/-- Semantic variable branch of `lowerE`. A final use moves the source
value's owner out of the environment; a repeated shared use retains it and
returns a fresh owner for the same graph. Every other entry state and every
world mismatch is unreachable in a successful run. -/
theorem lowerE_var_run_value_sound
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {src : IxIR0.Env}
    {fuel : Nat} {input output : VEnv} {world : Owned} {i : Nat}
    {emit : Emit} {av : AVal} {state finalState : LowSt}
    {sourceEnv : List IxIR0.Value} {sourceValue : IxIR0.Value}
    (hsource : sourceEnv[i]? = some sourceValue)
    (hrun : (lowerE src (fuel + 1) input world (.var i)).run state =
      .ok (output, emit, av) finalState) :
    LowerResultValueSound funRel recSelfRel ctx cur input output
      sourceEnv sourceEnv sourceValue world emit av := by
  have hssNe : (Owned.shared != Owned.shared) = false := by decide
  have huuNe : (Owned.unique != Owned.unique) = false := by decide
  have hsuNe : (Owned.shared != Owned.unique) = true := by decide
  have husNe : (Owned.unique != Owned.shared) = true := by decide
  have hsuEq : (Owned.shared == Owned.unique) = false := by decide
  have huuEq : (Owned.unique == Owned.unique) = true := by decide
  cases hentry : input.entries[i]? with
  | none =>
    apply False.elim
    apply estateThrowRun_not_ok
    simpa [lowerE, hentry] using hrun
  | some entry =>
    cases entry with
    | recSelf arity =>
      apply False.elim
      apply estateThrowRun_not_ok
      simpa [lowerE, hentry] using hrun
    | slot abs remaining uses held =>
      cases held with
      | false =>
        apply False.elim
        apply estateThrowRun_not_ok
        simpa [lowerE, hentry] using hrun
      | true =>
        by_cases hworld : worldOfUses uses = world
        · subst world
          have hsame :
              (worldOfUses uses != worldOfUses uses) = false := by
            cases uses <;> decide
          cases remaining with
          | zero =>
            apply False.elim
            apply estateThrowRun_not_ok
            simpa [lowerE, hentry, hsame] using hrun
          | succ remaining =>
            cases remaining with
            | zero =>
              have hpure :
                  (input.setEntry i (.slot abs 0 uses false),
                    (_root_.id : Emit), AVal.slotA abs) =
                      (output, emit, av) ∧ state = finalState := by
                simpa [lowerE, hentry, hsame] using hrun
              obtain ⟨hvalue, hstate⟩ := hpure
              cases hvalue
              subst finalState
              exact lower_var_move_value_sound hsource hentry
            | succ remaining =>
              cases uses with
              | erased =>
                have heq :
                    (Owned.shared == Owned.unique) = false := by decide
                have hpure :
                    let input' := input.setEntry i
                      (.slot abs (Nat.succ remaining) .erased true)
                    (input'.bump,
                      emitOp (.dup (.var (input'.rel abs))),
                      AVal.slotA input'.depth) = (output, emit, av) ∧
                      state = finalState := by
                  simpa [lowerE, hentry, worldOfUses, hsame, heq,
                    hssNe, huuNe, hsuNe, husNe, hsuEq, huuEq]
                    using hrun
                dsimp only at hpure
                obtain ⟨hvalue, hstate⟩ := hpure
                cases hvalue
                subst finalState
                exact lower_held_retain_value_sound hsource (by rfl) hentry
              | linear =>
                have heq :
                    (Owned.unique == Owned.unique) = true := by decide
                apply False.elim
                apply estateThrowRun_not_ok
                simpa [lowerE, hentry, worldOfUses, hsame, heq,
                  hssNe, huuNe, hsuNe, husNe, hsuEq, huuEq]
                  using hrun
              | affine =>
                have heq :
                    (Owned.unique == Owned.unique) = true := by decide
                apply False.elim
                apply estateThrowRun_not_ok
                simpa [lowerE, hentry, worldOfUses, hsame, heq,
                  hssNe, huuNe, hsuNe, husNe, hsuEq, huuEq]
                  using hrun
              | many =>
                have heq :
                    (Owned.shared == Owned.unique) = false := by decide
                have hpure :
                    let input' := input.setEntry i
                      (.slot abs (Nat.succ remaining) .many true)
                    (input'.bump,
                      emitOp (.dup (.var (input'.rel abs))),
                      AVal.slotA input'.depth) = (output, emit, av) ∧
                      state = finalState := by
                  simpa [lowerE, hentry, worldOfUses, hsame, heq,
                    hssNe, huuNe, hsuNe, husNe, hsuEq, huuEq]
                    using hrun
                dsimp only at hpure
                obtain ⟨hvalue, hstate⟩ := hpure
                cases hvalue
                subst finalState
                exact lower_held_retain_value_sound hsource (by rfl) hentry
        · have hdiff : (worldOfUses uses != world) = true := by
            cases uses <;> cases world <;>
              simp_all [worldOfUses] <;> decide
          cases uses <;> cases world
          all_goals
            try { exact (hworld (by rfl)).elim }
          all_goals
            apply False.elim
            apply estateThrowRun_not_ok
            simpa [lowerE, hentry, worldOfUses, hdiff, hssNe, huuNe,
              hsuNe, husNe, hsuEq, huuEq] using hrun

/-- Every successful variable borrow is bounded-sound. Unique entries,
released entries, and overcounted entries cannot reach a successful run;
final shared uses transfer an owner and repeated shared uses retain it in the
environment. -/
theorem lowerBorrow_var_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat} {input output : VEnv} {i : Nat}
    {emit : Emit} {av : AVal} {release : Bool}
    {state finalState : LowSt}
    (hrun : (lowerBorrow src (fuel + 1) input (.var i)).run state =
      .ok (output, emit, av, release) finalState) :
    LowerBorrowSoundBelow ctx cur limit input output emit av release := by
  have hsuEq : (Owned.shared == Owned.unique) = false := by decide
  have huuEq : (Owned.unique == Owned.unique) = true := by decide
  cases hentry : input.entries[i]? with
  | none =>
    apply False.elim
    apply estateThrowRun_not_ok
    simpa [lowerBorrow, hentry] using hrun
  | some entry =>
    cases entry with
    | recSelf arity =>
      apply False.elim
      apply estateThrowRun_not_ok
      simpa [lowerBorrow, hentry] using hrun
    | slot abs remaining uses held =>
      cases held with
      | false =>
        apply False.elim
        apply estateThrowRun_not_ok
        simpa [lowerBorrow, hentry] using hrun
      | true =>
        cases uses with
        | erased =>
          cases remaining with
          | zero =>
            apply False.elim
            apply estateThrowRun_not_ok
            simpa [lowerBorrow, hentry, worldOfUses, hsuEq] using hrun
          | succ remaining =>
            cases remaining with
            | zero =>
              have hpure :
                  (input.setEntry i (.slot abs 0 .erased false),
                    (_root_.id : Emit), AVal.slotA abs, true) =
                      (output, emit, av, release) ∧
                    state = finalState := by
                simpa [lowerBorrow, hentry, worldOfUses, hsuEq] using hrun
              obtain ⟨hvalue, hstate⟩ := hpure
              cases hvalue
              subst finalState
              exact lower_var_shared_move_borrow_sound_below (by rfl) hentry
            | succ remaining =>
              have hpure :
                  (input.setEntry i
                      (.slot abs (Nat.succ remaining) .erased true),
                    (_root_.id : Emit), AVal.slotA abs, false) =
                      (output, emit, av, release) ∧
                    state = finalState := by
                simpa [lowerBorrow, hentry, worldOfUses, hsuEq] using hrun
              obtain ⟨hvalue, hstate⟩ := hpure
              cases hvalue
              subst finalState
              exact lower_var_shared_borrow_sound_below (by rfl) hentry
        | linear =>
          apply False.elim
          apply estateThrowRun_not_ok
          simpa [lowerBorrow, hentry, worldOfUses, huuEq] using hrun
        | affine =>
          apply False.elim
          apply estateThrowRun_not_ok
          simpa [lowerBorrow, hentry, worldOfUses, huuEq] using hrun
        | many =>
          cases remaining with
          | zero =>
            apply False.elim
            apply estateThrowRun_not_ok
            simpa [lowerBorrow, hentry, worldOfUses, hsuEq] using hrun
          | succ remaining =>
            cases remaining with
            | zero =>
              have hpure :
                  (input.setEntry i (.slot abs 0 .many false),
                    (_root_.id : Emit), AVal.slotA abs, true) =
                      (output, emit, av, release) ∧
                    state = finalState := by
                simpa [lowerBorrow, hentry, worldOfUses, hsuEq] using hrun
              obtain ⟨hvalue, hstate⟩ := hpure
              cases hvalue
              subst finalState
              exact lower_var_shared_move_borrow_sound_below (by rfl) hentry
            | succ remaining =>
              have hpure :
                  (input.setEntry i
                      (.slot abs (Nat.succ remaining) .many true),
                    (_root_.id : Emit), AVal.slotA abs, false) =
                      (output, emit, av, release) ∧
                    state = finalState := by
                simpa [lowerBorrow, hentry, worldOfUses, hsuEq] using hrun
              obtain ⟨hvalue, hstate⟩ := hpure
              cases hvalue
              subst finalState
              exact lower_var_shared_borrow_sound_below (by rfl) hentry

/-- Semantic variable-borrow branch of the executable lowerer. Successful
final shared uses move the source-related owner to the caller, while repeated
shared uses keep that owner in the updated semantic environment. -/
theorem lowerBorrow_var_run_value_sound
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {src : IxIR0.Env}
    {fuel : Nat} {input output : VEnv} {i : Nat}
    {sourceEnv : List IxIR0.Value} {sourceValue : IxIR0.Value}
    {emit : Emit} {av : AVal} {release : Bool}
    {state finalState : LowSt}
    (hsource : sourceEnv[i]? = some sourceValue)
    (hrun : (lowerBorrow src (fuel + 1) input (.var i)).run state =
      .ok (output, emit, av, release) finalState) :
    LowerBorrowValueSound funRel recSelfRel ctx cur
      input output sourceEnv sourceEnv sourceValue emit av release := by
  have hsuEq : (Owned.shared == Owned.unique) = false := by decide
  have huuEq : (Owned.unique == Owned.unique) = true := by decide
  cases hentry : input.entries[i]? with
  | none =>
    exact (estateThrowRun_not_ok (by
      simpa [lowerBorrow, hentry] using hrun)).elim
  | some entry =>
    cases entry with
    | recSelf arity =>
      exact (estateThrowRun_not_ok (by
        simpa [lowerBorrow, hentry] using hrun)).elim
    | slot abs remaining uses held =>
      cases held with
      | false =>
        exact (estateThrowRun_not_ok (by
          simpa [lowerBorrow, hentry] using hrun)).elim
      | true =>
        cases uses with
        | erased =>
          cases remaining with
          | zero =>
            exact (estateThrowRun_not_ok (by
              simpa [lowerBorrow, hentry, worldOfUses, hsuEq]
                using hrun)).elim
          | succ remaining =>
            cases remaining with
            | zero =>
              have hpure :
                  (input.setEntry i (.slot abs 0 .erased false),
                    (_root_.id : Emit), AVal.slotA abs, true) =
                      (output, emit, av, release) ∧
                    state = finalState := by
                simpa [lowerBorrow, hentry, worldOfUses, hsuEq]
                  using hrun
              obtain ⟨hvalue, hstate⟩ := hpure
              cases hvalue
              subst finalState
              exact lower_var_shared_move_borrow_value_sound
                hsource (by rfl) hentry
            | succ remaining =>
              have hpure :
                  (input.setEntry i
                      (.slot abs (Nat.succ remaining) .erased true),
                    (_root_.id : Emit), AVal.slotA abs, false) =
                      (output, emit, av, release) ∧
                    state = finalState := by
                simpa [lowerBorrow, hentry, worldOfUses, hsuEq]
                  using hrun
              obtain ⟨hvalue, hstate⟩ := hpure
              cases hvalue
              subst finalState
              exact lower_var_shared_borrow_value_sound
                hsource (by rfl) hentry
        | linear =>
          exact (estateThrowRun_not_ok (by
            simpa [lowerBorrow, hentry, worldOfUses, huuEq]
              using hrun)).elim
        | affine =>
          exact (estateThrowRun_not_ok (by
            simpa [lowerBorrow, hentry, worldOfUses, huuEq]
              using hrun)).elim
        | many =>
          cases remaining with
          | zero =>
            exact (estateThrowRun_not_ok (by
              simpa [lowerBorrow, hentry, worldOfUses, hsuEq]
                using hrun)).elim
          | succ remaining =>
            cases remaining with
            | zero =>
              have hpure :
                  (input.setEntry i (.slot abs 0 .many false),
                    (_root_.id : Emit), AVal.slotA abs, true) =
                      (output, emit, av, release) ∧
                    state = finalState := by
                simpa [lowerBorrow, hentry, worldOfUses, hsuEq]
                  using hrun
              obtain ⟨hvalue, hstate⟩ := hpure
              cases hvalue
              subst finalState
              exact lower_var_shared_move_borrow_value_sound
                hsource (by rfl) hentry
            | succ remaining =>
              have hpure :
                  (input.setEntry i
                      (.slot abs (Nat.succ remaining) .many true),
                    (_root_.id : Emit), AVal.slotA abs, false) =
                      (output, emit, av, release) ∧
                    state = finalState := by
                simpa [lowerBorrow, hentry, worldOfUses, hsuEq]
                  using hrun
              obtain ⟨hvalue, hstate⟩ := hpure
              cases hvalue
              subst finalState
              exact lower_var_shared_borrow_value_sound
                hsource (by rfl) hentry

/-- Every non-variable expression uses `lowerBorrow`'s ordinary
shared-expression fallback. -/
inductive DynamicBorrowHead : IxIR0.Expr → Prop where
  | ref (address : Ixon.Address) : DynamicBorrowHead (.ref address)
  | app (function argument : IxIR0.Expr) :
      DynamicBorrowHead (.app function argument)
  | lam (uses : Uses) (body : IxIR0.Expr) :
      DynamicBorrowHead (.lam uses body)
  | letE (uses : Uses) (value body : IxIR0.Expr) :
      DynamicBorrowHead (.letE uses value body)
  | proj (index : Nat) (value : IxIR0.Expr) :
      DynamicBorrowHead (.proj index value)
  | lit (literal : IxIR0.Literal) : DynamicBorrowHead (.lit literal)
  | erased : DynamicBorrowHead .erased

theorem lowerBorrow_dynamic_extraMonotone
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEExtraMonotone src fuel)
    {input : VEnv} {expr : IxIR0.Expr}
    (hshape : DynamicBorrowHead expr) :
    ExtraMonotone (lowerBorrow src (fuel + 1) input expr) := by
  cases hshape <;> simp only [lowerBorrow]
  all_goals
    apply ExtraMonotone.bind (hexpr input .shared _)
    intro exprResult
    rcases exprResult with ⟨output, emit, value⟩
    exact ExtraMonotone.pure
      (output, emit, value,
        match value with | .slotA _ => true | .constA _ => false)

theorem lowerBorrowExtraMonotone_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEExtraMonotone src fuel) :
    LowerBorrowExtraMonotone src (fuel + 1) := by
  intro input expr
  cases expr with
  | var index => exact lowerBorrow_var_extraMonotone src fuel input index
  | ref address =>
    exact lowerBorrow_dynamic_extraMonotone hexpr (.ref address)
  | app function argument =>
    exact lowerBorrow_dynamic_extraMonotone hexpr
      (.app function argument)
  | lam uses body =>
    exact lowerBorrow_dynamic_extraMonotone hexpr (.lam uses body)
  | letE uses value body =>
    exact lowerBorrow_dynamic_extraMonotone hexpr
      (.letE uses value body)
  | proj index value =>
    exact lowerBorrow_dynamic_extraMonotone hexpr (.proj index value)
  | lit literal =>
    exact lowerBorrow_dynamic_extraMonotone hexpr (.lit literal)
  | erased => exact lowerBorrow_dynamic_extraMonotone hexpr .erased

/-- One fuel step for the entire state-only lowering cluster. Every recursive
compiler call is at predecessor fuel; the only generated declarations come
from the wrapper and lambda rules already isolated above. -/
theorem lowerExtraMonotone_succ {src : IxIR0.Env} {fuel : Nat}
    (hprev : LowerExtraMonotone src fuel) :
    LowerExtraMonotone src (fuel + 1) where
  expr := lowerEExtraMonotone_succ
    hprev.expr hprev.spine hprev.borrow hprev.lam
  borrow := lowerBorrowExtraMonotone_succ hprev.expr
  spine := lowerSpineExtraMonotone_succ
    hprev.expr hprev.spine hprev.knownCall hprev.applyRest
  knownCall := knownCallExtraMonotone_succ hprev.args hprev.applyRest
  args := lowerArgsExtraMonotone_succ hprev.expr hprev.args
  applyRest := applyRestExtraMonotone_succ hprev.args
  lam := fun input expr =>
    lowerLam_extraMonotone_succ hprev.fnBody input expr
  fnBody := lowerFnBodyExtraMonotone_succ hprev.expr

/-- All successful lowering-cluster actions prepend (and never discard)
generated declarations. -/
theorem lowerExtraMonotone (src : IxIR0.Env) :
    ∀ fuel, LowerExtraMonotone src fuel
  | 0 => lowerExtraMonotone_zero src
  | fuel + 1 => lowerExtraMonotone_succ (lowerExtraMonotone src fuel)

theorem lowerE_extraExtends
    {src : IxIR0.Env} {fuel : Nat} {input : VEnv} {world : Owned}
    {expr : IxIR0.Expr} {state finalState : LowSt}
    {output : VEnv} {emit : Emit} {value : AVal}
    (hrun : (lowerE src fuel input world expr).run state =
      .ok (output, emit, value) finalState) :
    ExtraExtends state finalState :=
  (lowerExtraMonotone src fuel).expr input world expr hrun

theorem lowerBorrow_extraExtends
    {src : IxIR0.Env} {fuel : Nat} {input : VEnv}
    {expr : IxIR0.Expr} {state finalState : LowSt}
    {result : VEnv × Emit × AVal × Bool}
    (hrun : (lowerBorrow src fuel input expr).run state =
      .ok result finalState) :
    ExtraExtends state finalState :=
  (lowerExtraMonotone src fuel).borrow input expr hrun

theorem lowerSpine_extraExtends
    {src : IxIR0.Env} {fuel : Nat} {input : VEnv} {world : Owned}
    {head : IxIR0.Expr} {args : List IxIR0.Expr}
    {state finalState : LowSt} {result : VEnv × Emit × AVal}
    (hrun : (lowerSpine src fuel input world head args).run state =
      .ok result finalState) :
    ExtraExtends state finalState :=
  (lowerExtraMonotone src fuel).spine input world head args hrun

theorem lowerArgs_extraExtends
    {src : IxIR0.Env} {fuel : Nat} {input : VEnv}
    {args : List (IxIR0.Expr × Owned)} {state finalState : LowSt}
    {result : VEnv × Emit × List AVal}
    (hrun : (lowerArgs src fuel input args).run state =
      .ok result finalState) :
    ExtraExtends state finalState :=
  (lowerExtraMonotone src fuel).args input args hrun

theorem knownCall_extraExtends
    {src : IxIR0.Env} {fuel : Nat} {input : VEnv}
    {build : Array Atom → Op} {count : Nat}
    {argWorlds : List Owned} {resultWorld : Owned}
    {args : List IxIR0.Expr} {state finalState : LowSt}
    {result : VEnv × Emit × AVal}
    (hrun : (knownCall src fuel input build count argWorlds resultWorld
      args).run state = .ok result finalState) :
    ExtraExtends state finalState :=
  (lowerExtraMonotone src fuel).knownCall input build count argWorlds
    resultWorld args hrun

theorem applyRest_extraExtends
    {src : IxIR0.Env} {fuel : Nat} {input : VEnv}
    {resultWorld : Owned} {pre : Emit} {function : AVal}
    {args : List IxIR0.Expr} {state finalState : LowSt}
    {result : VEnv × Emit × AVal}
    (hrun : (applyRest src fuel input resultWorld pre function args).run
      state = .ok result finalState) :
    ExtraExtends state finalState :=
  (lowerExtraMonotone src fuel).applyRest input resultWorld pre function
    args hrun

theorem lowerLam_extraExtends
    {src : IxIR0.Env} {fuel : Nat} {input : VEnv}
    {expr : IxIR0.Expr} {state finalState : LowSt}
    {result : VEnv × Emit × AVal}
    (hrun : (lowerLam src fuel input expr).run state =
      .ok result finalState) :
    ExtraExtends state finalState :=
  (lowerExtraMonotone src fuel).lam input expr hrun

theorem lowerFnBody_extraExtends
    {src : IxIR0.Env} {fuel : Nat} {input : VEnv}
    {drops : List SlotDrop} {world : Owned} {body : IxIR0.Expr}
    {state finalState : LowSt} {code : Code}
    (hrun : (lowerFnBody src fuel input drops world body).run state =
      .ok code finalState) :
    ExtraExtends state finalState :=
  (lowerExtraMonotone src fuel).fnBody input drops world body hrun

/-- One recursor alternative sequences only canonical entry cleanup and an
ordinary expression-lowering action, so it preserves the generated-state
extension invariant. -/
theorem lowerRecursorRule_extraMonotone (src : IxIR0.Env) (fuel numArgs : Nat)
    (ruleTag : IxIR0.RecRule × Nat) :
    ExtraMonotone (lowerRecursorRule src fuel numArgs ruleTag) := by
  rcases ruleTag with ⟨rule, tag⟩
  simp only [lowerRecursorRule]
  apply ExtraMonotone.bind (releaseSlots_extraMonotone _ _)
  intro releaseResult
  rcases releaseResult with ⟨input, releaseEmit⟩
  apply ExtraMonotone.bind
    ((lowerExtraMonotone src fuel).expr input .shared rule.rhs)
  intro bodyResult
  rcases bodyResult with ⟨output, bodyEmit, value⟩
  exact ExtraMonotone.pure _

/-- Traversing all recursor alternatives preserves generated state. -/
theorem lowerRecursor_extraMonotone (src : IxIR0.Env) (fuel numArgs : Nat)
    (natLit : Bool) (rules : Array IxIR0.RecRule) :
    ExtraMonotone (lowerRecursor src fuel numArgs natLit rules) := by
  simp only [lowerRecursor]
  apply ExtraMonotone.bind
    (ExtraMonotone.listMapM (lowerRecursorRule src fuel numArgs)
      (lowerRecursorRule_extraMonotone src fuel numArgs)
      rules.toList.zipIdx)
  intro alts
  exact ExtraMonotone.pure
    (⟨numArgs + 1, .shared, .case (.var 0) natLit alts.toArray⟩ : FnDef)

/-- Every declaration-lowering branch preserves generated state. -/
theorem lowerDecl_extraMonotone (src : IxIR0.Env) (fuel : Nat) :
    ∀ item, ExtraMonotone (lowerDecl src fuel item)
  | (address, .defn result body) => by
      simp only [lowerDecl]
      apply ExtraMonotone.bind
        ((lowerExtraMonotone src fuel).fnBody _ _ result _)
      intro code
      exact ExtraMonotone.pure
        (some (address, Decl.fn ⟨lamArity body, result, code⟩))
  | (_, .ctor tag arity) => by
      simp only [lowerDecl]
      exact ExtraMonotone.pure
        (none : Option (Ixon.Address × Decl))
  | (address, .recursor numArgs natLit rules) => by
      simp only [lowerDecl]
      apply ExtraMonotone.bind
        (lowerRecursor_extraMonotone src fuel numArgs natLit rules)
      intro d
      exact ExtraMonotone.pure (some (address, Decl.fn d))
  | (address, .extern arity) => by
      simp only [lowerDecl]
      exact ExtraMonotone.pure (some (address, Decl.extern arity))

/-- The full declaration traversal preserves generated state. -/
theorem lowerDecls_extraMonotone (src : IxIR0.Env) (fuel : Nat)
    (decls : List (Ixon.Address × IxIR0.Decl)) :
    ExtraMonotone (decls.filterMapM (lowerDecl src fuel)) :=
  ExtraMonotone.listFilterMapM (lowerDecl src fuel)
    (lowerDecl_extraMonotone src fuel) decls

/-- Whole-program lowering extends the empty generated-state trajectory;
the final `get` merely exposes the accumulated declarations in the result. -/
theorem lowerAllAction_extraMonotone
    (decls : List (Ixon.Address × IxIR0.Decl)) (main : IxIR0.Expr)
    (mainWorld : Owned) (fuel : Nat) :
    ExtraMonotone (lowerAllAction decls main mainWorld fuel) := by
  let src := IxIR0.Env.ofList decls
  simp only [lowerAllAction]
  apply ExtraMonotone.bind (lowerDecls_extraMonotone src fuel decls)
  intro base
  apply ExtraMonotone.bind
    ((lowerExtraMonotone src fuel).fnBody ⟨[], 0⟩ [] mainWorld main)
  intro mainCode
  apply ExtraMonotone.bind ExtraMonotone.get
  intro state
  exact ExtraMonotone.pure (base ++ state.extra, mainCode)

/-- Every final generated declaration exposed by a successful whole-program
action occurs verbatim in the returned target declaration list. -/
theorem lowerAllAction_extra_mem_result
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {fuel : Nat}
    {initial finalState : LowSt}
    {targetDecls : List (Ixon.Address × Decl)} {mainCode : Code}
    (hrun : (lowerAllAction decls main mainWorld fuel).run initial =
      .ok (targetDecls, mainCode) finalState) :
    ∀ {item}, item ∈ finalState.extra → item ∈ targetDecls := by
  intro item hmember
  simp only [lowerAllAction] at hrun
  obtain ⟨base, baseState, hbase, hafterBase⟩ :=
    estateBindRun_ok_inv hrun
  obtain ⟨compiledMain, mainState, hmain, hafterMain⟩ :=
    estateBindRun_ok_inv hafterBase
  obtain ⟨observed, getState, hget, hpure⟩ :=
    estateBindRun_ok_inv hafterMain
  have hget' : mainState = observed ∧ mainState = getState := by
    simpa using hget
  obtain ⟨hobserved, hgetState⟩ := hget'
  subst observed
  subst getState
  have hpure' :
      (base ++ mainState.extra, compiledMain) =
          (targetDecls, mainCode) ∧ mainState = finalState := by
    simpa using hpure
  obtain ⟨hresult, hstate⟩ := hpure'
  subst finalState
  have hdecls : base ++ mainState.extra = targetDecls :=
    congrArg Prod.fst hresult
  rw [← hdecls]
  exact List.mem_append_right base hmember

/-- Recover the exact `lowerDecl` sub-run for any source-list member of a
successful whole-program action. Its final state is a represented suffix of
the whole trajectory, and any emitted base declaration occurs in the returned
target list. -/
theorem lowerAllAction_decl_trace
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {fuel : Nat} {initial finalState : LowSt}
    {targetDecls : List (Ixon.Address × Decl)} {mainCode : Code}
    (hrun : (lowerAllAction decls main mainWorld fuel).run initial =
      .ok (targetDecls, mainCode) finalState)
    {item : Ixon.Address × IxIR0.Decl} (hitem : item ∈ decls) :
    ∃ itemInitial itemFinal output,
      (lowerDecl (IxIR0.Env.ofList decls) fuel item).run itemInitial =
        .ok output itemFinal ∧
      ExtraExtends itemFinal finalState ∧
      ∀ value, output = some value → value ∈ targetDecls := by
  let src := IxIR0.Env.ofList decls
  simp only [lowerAllAction] at hrun
  obtain ⟨base, baseState, hbase, hafterBase⟩ :=
    estateBindRun_ok_inv hrun
  obtain ⟨compiledMain, mainState, hmain, hafterMain⟩ :=
    estateBindRun_ok_inv hafterBase
  obtain ⟨observed, getState, hget, hpure⟩ :=
    estateBindRun_ok_inv hafterMain
  have hget' : mainState = observed ∧ mainState = getState := by
    simpa using hget
  obtain ⟨hobserved, hgetState⟩ := hget'
  subst observed
  subst getState
  have hpure' :
      (base ++ mainState.extra, compiledMain) =
          (targetDecls, mainCode) ∧ mainState = finalState := by
    simpa using hpure
  obtain ⟨hresult, hstate⟩ := hpure'
  subst finalState
  obtain ⟨itemInitial, itemFinal, output, hitemRun, hitemExtends,
      houtput⟩ := listFilterMapM_trace (lowerDecl src fuel)
        (lowerDecl_extraMonotone src fuel) decls hbase hitem
  refine ⟨itemInitial, itemFinal, output, ?_,
    hitemExtends.trans (lowerFnBody_extraExtends hmain), ?_⟩
  · simpa [src] using hitemRun
  · intro value hvalue
    have hbaseMember := houtput value hvalue
    have hdecls : base ++ mainState.extra = targetDecls :=
      congrArg Prod.fst hresult
    rw [← hdecls]
    exact List.mem_append_left _ hbaseMember

/-- A successful whole-program action from the default state carries the
exact cache/declaration reachability witness needed to construct the final
`ExtraRepresented` layout. -/
theorem lowerAllAction_extraExtends_empty
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {fuel : Nat} {result : List (Ixon.Address × Decl) × Code}
    {finalState : LowSt}
    (hrun : (lowerAllAction decls main mainWorld fuel).run {} =
      .ok result finalState) :
    ExtraExtends ({} : LowSt) finalState :=
  lowerAllAction_extraMonotone decls main mainWorld fuel hrun

/-- Once the target context represents the final `extra` list, a successful
whole-program run from the default state also represents every memoized
constructor wrapper. No arbitrary-state wrapper oracle remains. -/
theorem lowerAllAction_extraRepresented
    {ctx : Ctx} {decls : List (Ixon.Address × IxIR0.Decl)}
    {main : IxIR0.Expr} {mainWorld : Owned} {fuel : Nat}
    {result : List (Ixon.Address × Decl) × Code} {finalState : LowSt}
    (hrun : (lowerAllAction decls main mainWorld fuel).run {} =
      .ok result finalState)
    (hdecls : ∀ {address decl}, (address, decl) ∈ finalState.extra →
      ctx.decls address = some decl) :
    ExtraRepresented ctx finalState :=
  (lowerAllAction_extraExtends_empty hrun).represented_of_empty hdecls

/-- Non-variable borrowing is derived directly from predecessor-fuel
expression soundness. Slot results carry a releasable temporary owner;
stable constants are ownership-inert non-releasing borrows. -/
theorem lowerBorrow_dynamic_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat}
    (hexpr : LowerEPreservesBelow ctx cur limit src fuel)
    {input output : VEnv} {expr : IxIR0.Expr}
    {emit : Emit} {av : AVal} {release : Bool}
    {state finalState : LowSt}
    (hshape : DynamicBorrowHead expr)
    (hrun : (lowerBorrow src (fuel + 1) input expr).run state =
      .ok (output, emit, av, release) finalState)
    (hrepresented : ExtraRepresented ctx finalState)
    (havailable : SelfAvailableBelow ctx cur limit input) :
    LowerBorrowSoundBelow ctx cur limit input output emit av release := by
  cases hshape <;> simp only [lowerBorrow] at hrun
  all_goals
    obtain ⟨exprResult, exprState, hexprRun, hafterExpr⟩ :=
      estateBindRun_ok_inv hrun
    rcases exprResult with ⟨exprOutput, exprEmit, exprValue⟩
    cases exprValue with
    | slotA abs =>
      have hpure :
          (exprOutput, exprEmit, AVal.slotA abs, true) =
              (output, emit, av, release) ∧
            exprState = finalState := by
        simpa using hafterExpr
      obtain ⟨hvalue, hstate⟩ := hpure
      cases hvalue
      subst finalState
      exact (hexpr hexprRun hrepresented havailable).asBorrowSlot
    | constA atom =>
      have hpure :
          (exprOutput, exprEmit, AVal.constA atom, false) =
              (output, emit, av, release) ∧
            exprState = finalState := by
        simpa using hafterExpr
      obtain ⟨hvalue, hstate⟩ := hpure
      cases hvalue
      subst finalState
      exact (hexpr hexprRun hrepresented havailable).asBorrowConst

/-- Semantic dynamic-borrow branch. Every non-variable borrowing position is
lowered as an ordinary shared expression and adapted by the two borrow
adapters, so the source graph passes through unchanged and only the release
obligation is recomputed from the descriptor. -/
theorem lowerBorrow_dynamic_run_value_sound
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {src : IxIR0.Env} {fuel : Nat}
    {input output : VEnv} {expr : IxIR0.Expr}
    {emit : Emit} {av : AVal} {release : Bool}
    {state finalState : LowSt}
    {sourceEnv : List IxIR0.Value} {sourceValue : IxIR0.Value}
    (hexpr : ∀ {exprOutput : VEnv} {exprEmit : Emit} {exprAv : AVal}
      {exprState : LowSt},
      (lowerE src fuel input .shared expr).run state =
        .ok (exprOutput, exprEmit, exprAv) exprState →
      LowerResultValueSound funRel recSelfRel ctx cur input exprOutput
        sourceEnv sourceEnv sourceValue .shared exprEmit exprAv)
    (hshape : DynamicBorrowHead expr)
    (hrun : (lowerBorrow src (fuel + 1) input expr).run state =
      .ok (output, emit, av, release) finalState) :
    LowerBorrowValueSound funRel recSelfRel ctx cur input output
      sourceEnv sourceEnv sourceValue emit av release := by
  cases hshape <;> simp only [lowerBorrow] at hrun
  all_goals
    obtain ⟨exprResult, exprState, hexprRun, hafterExpr⟩ :=
      estateBindRun_ok_inv hrun
    rcases exprResult with ⟨exprOutput, exprEmit, exprValue⟩
    cases exprValue with
    | slotA abs =>
      have hpure :
          (exprOutput, exprEmit, AVal.slotA abs, true) =
              (output, emit, av, release) ∧
            exprState = finalState := by
        simpa using hafterExpr
      obtain ⟨hvalue, hstate⟩ := hpure
      cases hvalue
      subst finalState
      exact (hexpr hexprRun).asBorrowSlot
    | constA atom =>
      have hpure :
          (exprOutput, exprEmit, AVal.constA atom, false) =
              (output, emit, av, release) ∧
            exprState = finalState := by
        simpa using hafterExpr
      obtain ⟨hvalue, hstate⟩ := hpure
      cases hvalue
      subst finalState
      exact (hexpr hexprRun).asBorrowConst

/-- A complete bounded `lowerBorrow` step follows from predecessor-fuel
expression soundness plus the direct variable-borrow rule. -/
theorem lowerBorrowPreservesBelow_succ
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat}
    (hexpr : LowerEPreservesBelow ctx cur limit src fuel) :
    LowerBorrowPreservesBelow ctx cur limit src (fuel + 1) := by
  intro input expr state finalState output emit av release hrun hrepresented
    havailable
  cases expr with
  | var i => exact lowerBorrow_var_run_sound_below hrun
  | ref address =>
    exact lowerBorrow_dynamic_run_sound_below hexpr (.ref address) hrun
      hrepresented havailable
  | app function argument =>
    exact lowerBorrow_dynamic_run_sound_below hexpr
      (.app function argument) hrun hrepresented havailable
  | lam uses body =>
    exact lowerBorrow_dynamic_run_sound_below hexpr (.lam uses body) hrun
      hrepresented havailable
  | letE uses value body =>
    exact lowerBorrow_dynamic_run_sound_below hexpr
      (.letE uses value body) hrun hrepresented havailable
  | proj index value =>
    exact lowerBorrow_dynamic_run_sound_below hexpr (.proj index value) hrun
      hrepresented havailable
  | lit literal =>
    exact lowerBorrow_dynamic_run_sound_below hexpr (.lit literal) hrun
      hrepresented havailable
  | erased =>
    exact lowerBorrow_dynamic_run_sound_below hexpr .erased hrun
      hrepresented havailable

/-- Every successful shared projection lowering is bounded-sound. The
borrowing sub-run determines whether the target owner remains in the output
environment or is released after retaining the fetched field; erased values
absorb projection, while other stable constants make target execution stuck. -/
theorem lowerE_proj_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat}
    (hborrow : LowerBorrowPreservesBelow ctx cur limit src fuel)
    {input output : VEnv} {world : Owned} {index : Nat}
    {source : IxIR0.Expr} {emit : Emit} {av : AVal}
    {state finalState : LowSt}
    (hrun : (lowerE src (fuel + 1) input world
      (.proj index source)).run state =
        .ok (output, emit, av) finalState)
    (hrepresented : ExtraRepresented ctx finalState)
    (havailable : SelfAvailableBelow ctx cur limit input) :
    LowerResultSoundBelow ctx cur limit input output world emit av := by
  cases world with
  | unique =>
    have huuEq : (Owned.unique == Owned.unique) = true := by decide
    simp only [lowerE, huuEq, if_true] at hrun
    exact (estateThrowRun_not_ok hrun).elim
  | shared =>
    have hsuEq : (Owned.shared == Owned.unique) = false := by decide
    simp only [lowerE, hsuEq, Bool.false_eq_true, if_false] at hrun
    obtain ⟨borrowResult, middleState, hborrowRun, hafterBorrow⟩ :=
      estateBindRun_ok_inv hrun
    rcases borrowResult with
      ⟨borrowOutput, borrowEmit, borrowed, release⟩
    cases borrowed with
    | constA atom =>
      cases atom with
      | var relative =>
        have hpure :
            (borrowOutput.bump,
              borrowEmit ∘ emitOp (.fetch (.var relative) index),
              AVal.slotA borrowOutput.depth) =
                (output, emit, av) ∧ middleState = finalState := by
          simpa using hafterBorrow
        obtain ⟨hvalue, hstate⟩ := hpure
        cases hvalue
        subst finalState
        cases (hborrow hborrowRun hrepresented havailable).stable
      | lit literal =>
        have hpure :
            (borrowOutput.bump,
              borrowEmit ∘ emitOp (.fetch (.lit literal) index),
              AVal.slotA borrowOutput.depth) =
                (output, emit, av) ∧ middleState = finalState := by
          simpa using hafterBorrow
        obtain ⟨hvalue, hstate⟩ := hpure
        cases hvalue
        subst finalState
        exact (hborrow hborrowRun hrepresented havailable).projectConst
      | erased =>
        have hpure :
            (borrowOutput, borrowEmit, AVal.constA .erased) =
                (output, emit, av) ∧ middleState = finalState := by
          simpa using hafterBorrow
        obtain ⟨hvalue, hstate⟩ := hpure
        cases hvalue
        subst finalState
        exact (hborrow hborrowRun hrepresented havailable).returnErased
    | slotA targetAbs =>
      cases release with
      | false =>
        have hpure :
            (borrowOutput.bump.bump,
              borrowEmit ∘
                emitOp (.fetch (.var (borrowOutput.rel targetAbs)) index) ∘
                emitOp (.dup
                  (.var (borrowOutput.bump.rel borrowOutput.depth))),
              AVal.slotA borrowOutput.bump.depth) =
                (output, emit, av) ∧ middleState = finalState := by
          simpa using hafterBorrow
        obtain ⟨hvalue, hstate⟩ := hpure
        cases hvalue
        subst finalState
        exact (hborrow hborrowRun hrepresented havailable).projectSlotKept
      | true =>
        have hpure :
            (borrowOutput.bump.bump.bump,
              borrowEmit ∘
                emitOp (.fetch (.var (borrowOutput.rel targetAbs)) index) ∘
                emitOp (.dup
                  (.var (borrowOutput.bump.rel borrowOutput.depth))) ∘
                emitOp (.drop
                  (.var (borrowOutput.bump.bump.rel targetAbs))),
              AVal.slotA borrowOutput.bump.depth) =
                (output, emit, av) ∧ middleState = finalState := by
          simpa using hafterBorrow
        obtain ⟨hvalue, hstate⟩ := hpure
        cases hvalue
        subst finalState
        exact (hborrow hborrowRun hrepresented havailable).projectSlotReleased

/-- Semantic projection branch of the executable lowerer. The four target
descriptors are dispatched against the two source outcomes: a slot borrow
selects the corresponding constructor field, the erased descriptor absorbs
an erased target, and the remaining two pairings are unreachable. The
compiler-induction hypothesis is supplied for the exact borrow run, so this
theorem carries no fuel bound of its own. -/
theorem lowerE_proj_run_value_sound
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {src : IxIR0.Env} {fuel : Nat}
    {input output : VEnv} {world : Owned} {index : Nat}
    {source : IxIR0.Expr} {emit : Emit} {av : AVal}
    {state finalState : LowSt} {sourceEnv : List IxIR0.Value}
    {sourceTarget sourceValue : IxIR0.Value}
    (hborrow : ∀ {borrowOutput : VEnv} {borrowEmit : Emit}
      {borrowed : AVal} {release : Bool} {middleState : LowSt},
      (lowerBorrow src fuel input source).run state =
        .ok (borrowOutput, borrowEmit, borrowed, release) middleState →
      LowerBorrowValueSound funRel recSelfRel ctx cur input borrowOutput
        sourceEnv sourceEnv sourceTarget borrowEmit borrowed release)
    (hproject : SourceProject index sourceTarget sourceValue)
    (hrun : (lowerE src (fuel + 1) input world
      (.proj index source)).run state =
        .ok (output, emit, av) finalState) :
    LowerResultValueSound funRel recSelfRel ctx cur input output
      sourceEnv sourceEnv sourceValue world emit av := by
  cases world with
  | unique =>
    have huuEq : (Owned.unique == Owned.unique) = true := by decide
    simp only [lowerE, huuEq, if_true] at hrun
    exact (estateThrowRun_not_ok hrun).elim
  | shared =>
    have hsuEq : (Owned.shared == Owned.unique) = false := by decide
    simp only [lowerE, hsuEq, Bool.false_eq_true, if_false] at hrun
    obtain ⟨borrowResult, middleState, hborrowRun, hafterBorrow⟩ :=
      estateBindRun_ok_inv hrun
    rcases borrowResult with
      ⟨borrowOutput, borrowEmit, borrowed, release⟩
    cases borrowed with
    | constA atom =>
      cases atom with
      | var relative =>
        have hpure :
            (borrowOutput.bump,
              borrowEmit ∘ emitOp (.fetch (.var relative) index),
              AVal.slotA borrowOutput.depth) =
                (output, emit, av) ∧ middleState = finalState := by
          simpa using hafterBorrow
        obtain ⟨hvalue, hstate⟩ := hpure
        cases hvalue
        subst finalState
        cases (hborrow hborrowRun).stable
      | lit literal =>
        have hpure :
            (borrowOutput.bump,
              borrowEmit ∘ emitOp (.fetch (.lit literal) index),
              AVal.slotA borrowOutput.depth) =
                (output, emit, av) ∧ middleState = finalState := by
          simpa using hafterBorrow
        obtain ⟨hvalue, hstate⟩ := hpure
        cases hvalue
        subst finalState
        exact (hborrow hborrowRun).projectConst
      | erased =>
        have hpure :
            (borrowOutput, borrowEmit, AVal.constA .erased) =
                (output, emit, av) ∧ middleState = finalState := by
          simpa using hafterBorrow
        obtain ⟨hvalue, hstate⟩ := hpure
        cases hvalue
        subst finalState
        cases hproject with
        | ctor hfield => exact (hborrow hborrowRun).projectCtorErased
        | erased => exact (hborrow hborrowRun).returnErased
    | slotA targetAbs =>
      cases release with
      | false =>
        have hpure :
            (borrowOutput.bump.bump,
              borrowEmit ∘
                emitOp (.fetch (.var (borrowOutput.rel targetAbs)) index) ∘
                emitOp (.dup
                  (.var (borrowOutput.bump.rel borrowOutput.depth))),
              AVal.slotA borrowOutput.bump.depth) =
                (output, emit, av) ∧ middleState = finalState := by
          simpa using hafterBorrow
        obtain ⟨hvalue, hstate⟩ := hpure
        cases hvalue
        subst finalState
        cases hproject with
        | ctor hfield =>
          exact (hborrow hborrowRun).projectSlotKept hfield
        | erased => exact (hborrow hborrowRun).projectSlotKeptErased
      | true =>
        have hpure :
            (borrowOutput.bump.bump.bump,
              borrowEmit ∘
                emitOp (.fetch (.var (borrowOutput.rel targetAbs)) index) ∘
                emitOp (.dup
                  (.var (borrowOutput.bump.rel borrowOutput.depth))) ∘
                emitOp (.drop
                  (.var (borrowOutput.bump.bump.rel targetAbs))),
              AVal.slotA borrowOutput.bump.depth) =
                (output, emit, av) ∧ middleState = finalState := by
          simpa using hafterBorrow
        obtain ⟨hvalue, hstate⟩ := hpure
        cases hvalue
        subst finalState
        cases hproject with
        | ctor hfield =>
          exact (hborrow hborrowRun).projectSlotReleased hfield
        | erased => exact (hborrow hborrowRun).projectSlotReleasedErased

/-- Fully instantiated semantic projection: with a source variable as the
projection target the borrow hypothesis is discharged by the variable-borrow
theorem, so this carries no compiler-induction premise at all. -/
theorem lowerE_proj_var_run_value_sound
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {src : IxIR0.Env} {fuel : Nat}
    {input output : VEnv} {world : Owned} {index i : Nat}
    {emit : Emit} {av : AVal} {state finalState : LowSt}
    {sourceEnv : List IxIR0.Value}
    {sourceTarget sourceValue : IxIR0.Value}
    (hsource : sourceEnv[i]? = some sourceTarget)
    (hproject : SourceProject index sourceTarget sourceValue)
    (hrun : (lowerE src (fuel + 2) input world
      (.proj index (.var i))).run state =
        .ok (output, emit, av) finalState) :
    LowerResultValueSound funRel recSelfRel ctx cur input output
      sourceEnv sourceEnv sourceValue world emit av := by
  refine lowerE_proj_run_value_sound (fuel := fuel + 1) ?_ hproject hrun
  intro borrowOutput borrowEmit borrowed release middleState hborrowRun
  exact lowerBorrow_var_run_value_sound hsource hborrowRun

/-- The expression-level application constructor delegates exactly to the
predecessor-fuel spine proof. -/
theorem lowerE_app_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat}
    (hspine : LowerSpinePreservesBelow ctx cur limit src fuel)
    {input output : VEnv} {world : Owned} {function argument : IxIR0.Expr}
    {emit : Emit} {av : AVal} {state finalState : LowSt}
    (hrun : (lowerE src (fuel + 1) input world
      (.app function argument)).run state =
        .ok (output, emit, av) finalState)
    (hrepresented : ExtraRepresented ctx finalState)
    (havailable : SelfAvailableBelow ctx cur limit input) :
    LowerResultSoundBelow ctx cur limit input output world emit av := by
  apply hspine
  · simpa [lowerE] using hrun
  · exact hrepresented
  · exact havailable

/-- Expression constructors that neither install a local binder nor create a
lifted local declaration. These are exactly the cases already closed by the
bounded compiler induction's variable, spine, borrow, and scalar layers. -/
inductive NonbindingLowerEHead : IxIR0.Expr → Prop where
  | var (index : Nat) : NonbindingLowerEHead (.var index)
  | ref (address : Ixon.Address) : NonbindingLowerEHead (.ref address)
  | app (function argument : IxIR0.Expr) :
      NonbindingLowerEHead (.app function argument)
  | proj (index : Nat) (source : IxIR0.Expr) :
      NonbindingLowerEHead (.proj index source)
  | lit (literal : IxIR0.Literal) : NonbindingLowerEHead (.lit literal)
  | erased : NonbindingLowerEHead .erased

/-- Consolidated bounded `lowerE` step for every nonbinding constructor.
Lambda lifting and let installation are supplied by their adjacent dedicated
rules. -/
theorem lowerE_nonbinding_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat}
    (hspine : LowerSpinePreservesBelow ctx cur limit src fuel)
    (hargsNext : LowerArgsPreservesBelow ctx cur limit src (fuel + 1))
    (hargsNextExtra : LowerArgsExtraMonotone src (fuel + 1))
    (hrestNext : ApplyRestPreservesBelow ctx cur limit src (fuel + 1))
    (hrestNextExtra : ApplyRestExtraMonotone src (fuel + 1))
    (hborrow : LowerBorrowPreservesBelow ctx cur limit src fuel)
    (hdecls : SourceDeclContractsBelow src ctx limit)
    {input output : VEnv} {world : Owned} {expr : IxIR0.Expr}
    {emit : Emit} {av : AVal} {state finalState : LowSt}
    (hshape : NonbindingLowerEHead expr)
    (hrun : (lowerE src (fuel + 1) input world expr).run state =
      .ok (output, emit, av) finalState)
    (hrepresented : ExtraRepresented ctx finalState)
    (havailable : SelfAvailableBelow ctx cur limit input) :
    LowerResultSoundBelow ctx cur limit input output world emit av := by
  cases hshape with
  | var index => exact lowerE_var_run_sound_below hrun
  | ref address =>
    exact lowerE_ref_run_sound_below hargsNext hargsNextExtra hrestNext
      hrestNextExtra hdecls hrun hrepresented havailable
  | app function argument =>
    exact lowerE_app_run_sound_below hspine hrun hrepresented havailable
  | proj index source =>
    exact lowerE_proj_run_sound_below hborrow hrun hrepresented havailable
  | lit literal => exact lowerE_lit_run_sound_below hrun
  | erased => exact lowerE_erased_run_sound_below hrun

/-- Every successful let installation is bounded-sound once the companion
compile-state induction proves that the body consumes its counted first
entry. Slot values alias their existing owner; dead shared/affine aliases are
released before the body; stable constants are materialized in the physical
slot the executable lowerer installs. -/
theorem lowerE_let_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat}
    (hexpr : LowerEPreservesBelow ctx cur limit src fuel)
    {input output : VEnv} {world : Owned} {uses : Uses}
    {value body : IxIR0.Expr} {emit : Emit} {av : AVal}
    {state finalState : LowSt}
    (hreleases : LowerEReleasesTrackedFirst src fuel body)
    (hrun : (lowerE src (fuel + 1) input world
      (.letE uses value body)).run state =
        .ok (output, emit, av) finalState)
    (hrepresented : ExtraRepresented ctx finalState)
    (havailable : SelfAvailableBelow ctx cur limit input) :
    LowerResultSoundBelow ctx cur limit input output world emit av := by
  simp only [lowerE] at hrun
  obtain ⟨valueResult, valueState, hvalueRun, hafterValue⟩ :=
    estateBindRun_ok_inv hrun
  rcases valueResult with ⟨middle, valueEmit, boundValue⟩
  have hmiddleAvailable := havailable.lowerE hvalueRun
  cases boundValue with
  | slotA abs =>
    by_cases hzero : countUses 0 body = 0
    · cases uses with
      | erased =>
        obtain ⟨_, _, hthrow, _⟩ := estateBindRun_ok_inv
          (by simpa [hzero] using hafterValue)
        exact (estateThrowRun_not_ok hthrow).elim
      | linear =>
        obtain ⟨_, _, hthrow, _⟩ := estateBindRun_ok_inv
          (by simpa [hzero] using hafterValue)
        exact (estateThrowRun_not_ok hthrow).elim
      | affine =>
        let heldInput :=
          installAliasBinder middle abs 0 Uses.affine true
        let bodyInput :=
          (heldInput.setEntry 0 (.slot abs 0 .affine false)).bump
        have hcontinue :
            ((lowerE src fuel bodyInput world body) >>= fun result =>
              let (bodyOutput, bodyEmit, resultValue) := result
              pure (bodyOutput.pop,
                valueEmit ∘ emitOp (.dropU (.var (middle.rel abs))) ∘
                  bodyEmit,
                resultValue)).run valueState =
              .ok (output, emit, av) finalState := by
          simpa [hzero, heldInput, bodyInput, installAliasBinder,
            VEnv.setEntry, VEnv.bump] using hafterValue
        obtain ⟨bodyResult, bodyState, hbodyRun, hafterBody⟩ :=
          estateBindRun_ok_inv hcontinue
        rcases bodyResult with ⟨bodyOutput, bodyEmit, resultValue⟩
        have hpure :
            (bodyOutput.pop,
              valueEmit ∘ emitOp (.dropU (.var (middle.rel abs))) ∘
                bodyEmit,
              resultValue) = (output, emit, av) ∧
              bodyState = finalState := by
          simpa using hafterBody
        obtain ⟨hresult, hstate⟩ := hpure
        cases hresult
        subst finalState
        have hbodyAvailable : SelfAvailableBelow ctx cur limit bodyInput := by
          have hinstalled :=
            (hmiddleAvailable.consSlot abs 0 .affine true).setSlot
              0 abs 0 .affine false
          simpa [bodyInput, heldInput, installAliasBinder] using
            hinstalled.bump
        have hbodySound := hexpr hbodyRun hrepresented hbodyAvailable
        have hvalueSound := hexpr hvalueRun
          (hrepresented.of_extends (lowerE_extraExtends hbodyRun))
          havailable
        have htracked : FirstEntryTracks bodyInput .affine
            (countUses 0 body) := by
          refine ⟨abs, middle.entries, ?_⟩
          simp [bodyInput, heldInput,
            installAliasBinder, VEnv.setEntry, VEnv.bump, hzero]
        have hreleased := hreleases htracked hbodyRun
        have hinstall : ∀ rest slots,
            EmitSoundBelow ctx cur limit
              (emitOp (.dropU (.var (middle.rel abs))))
              (OwnsResultProtected middle .unique (.slotA abs) rest slots)
              (OwnsVEnvProtected bodyInput rest slots) := by
          intro rest slots
          have halias := installAliasBinder_held_below
            (ctx := ctx) (cur := cur) (limit := limit)
            (Γ := middle) (abs := abs) (remaining := 0)
            (uses := .affine) rest slots
          have hdrop := release_slot_affine_owned_below
            (ctx := ctx) (cur := cur) (limit := limit)
            (Γ := heldInput) (i := 0) (abs := abs)
            (by simp [heldInput, installAliasBinder]) rest slots
          have hcomposed := EmitSoundBelow.comp halias hdrop
          simpa [bodyInput, heldInput, installAliasBinder, VEnv.rel,
            worldOfUses, Function.comp_def] using hcomposed
        have hsound := hvalueSound.installThen hinstall hbodySound hreleased
        simpa [worldOfUses, Function.comp_def] using hsound
      | many =>
        let heldInput := installAliasBinder middle abs 0 Uses.many true
        let bodyInput :=
          (heldInput.setEntry 0 (.slot abs 0 .many false)).bump
        have hcontinue :
            ((lowerE src fuel bodyInput world body) >>= fun result =>
              let (bodyOutput, bodyEmit, resultValue) := result
              pure (bodyOutput.pop,
                valueEmit ∘ emitOp (.drop (.var (middle.rel abs))) ∘
                  bodyEmit,
                resultValue)).run valueState =
              .ok (output, emit, av) finalState := by
          simpa [hzero, heldInput, bodyInput, installAliasBinder,
            VEnv.setEntry, VEnv.bump] using hafterValue
        obtain ⟨bodyResult, bodyState, hbodyRun, hafterBody⟩ :=
          estateBindRun_ok_inv hcontinue
        rcases bodyResult with ⟨bodyOutput, bodyEmit, resultValue⟩
        have hpure :
            (bodyOutput.pop,
              valueEmit ∘ emitOp (.drop (.var (middle.rel abs))) ∘
                bodyEmit,
              resultValue) = (output, emit, av) ∧
              bodyState = finalState := by
          simpa using hafterBody
        obtain ⟨hresult, hstate⟩ := hpure
        cases hresult
        subst finalState
        have hbodyAvailable : SelfAvailableBelow ctx cur limit bodyInput := by
          have hinstalled :=
            (hmiddleAvailable.consSlot abs 0 .many true).setSlot
              0 abs 0 .many false
          simpa [bodyInput, heldInput, installAliasBinder] using
            hinstalled.bump
        have hbodySound := hexpr hbodyRun hrepresented hbodyAvailable
        have hvalueSound := hexpr hvalueRun
          (hrepresented.of_extends (lowerE_extraExtends hbodyRun))
          havailable
        have htracked : FirstEntryTracks bodyInput .many
            (countUses 0 body) := by
          refine ⟨abs, middle.entries, ?_⟩
          simp [bodyInput, heldInput,
            installAliasBinder, VEnv.setEntry, VEnv.bump, hzero]
        have hreleased := hreleases htracked hbodyRun
        have hinstall : ∀ rest slots,
            EmitSoundBelow ctx cur limit
              (emitOp (.drop (.var (middle.rel abs))))
              (OwnsResultProtected middle .shared (.slotA abs) rest slots)
              (OwnsVEnvProtected bodyInput rest slots) := by
          intro rest slots
          have halias := installAliasBinder_held_below
            (ctx := ctx) (cur := cur) (limit := limit)
            (Γ := middle) (abs := abs) (remaining := 0)
            (uses := .many) rest slots
          have hdrop := release_slot_many_owned_below
            (ctx := ctx) (cur := cur) (limit := limit)
            (Γ := heldInput) (i := 0) (abs := abs)
            (by simp [heldInput, installAliasBinder]) rest slots
          have hcomposed := EmitSoundBelow.comp halias hdrop
          simpa [bodyInput, heldInput, installAliasBinder, VEnv.rel,
            worldOfUses, Function.comp_def] using hcomposed
        have hsound := hvalueSound.installThen hinstall hbodySound hreleased
        simpa [worldOfUses, Function.comp_def] using hsound
    · let bodyInput := installAliasBinder middle abs
          (countUses 0 body) uses true
      have hcontinue :
          ((lowerE src fuel bodyInput world body) >>= fun result =>
            let (bodyOutput, bodyEmit, resultValue) := result
            pure (bodyOutput.pop, valueEmit ∘ bodyEmit, resultValue)).run
            valueState = .ok (output, emit, av) finalState := by
        simpa [hzero, bodyInput, installAliasBinder] using hafterValue
      obtain ⟨bodyResult, bodyState, hbodyRun, hafterBody⟩ :=
        estateBindRun_ok_inv hcontinue
      rcases bodyResult with ⟨bodyOutput, bodyEmit, resultValue⟩
      have hpure :
          (bodyOutput.pop, valueEmit ∘ bodyEmit, resultValue) =
              (output, emit, av) ∧ bodyState = finalState := by
        simpa using hafterBody
      obtain ⟨hresult, hstate⟩ := hpure
      cases hresult
      subst finalState
      have hbodyAvailable : SelfAvailableBelow ctx cur limit bodyInput := by
        simpa [bodyInput, installAliasBinder] using
          hmiddleAvailable.consSlot abs (countUses 0 body) uses true
      have hbodySound := hexpr hbodyRun hrepresented hbodyAvailable
      have hvalueSound := hexpr hvalueRun
        (hrepresented.of_extends (lowerE_extraExtends hbodyRun))
        havailable
      have htracked : FirstEntryTracks bodyInput uses
          (countUses 0 body) := by
        refine ⟨abs, middle.entries, ?_⟩
        simp [bodyInput, installAliasBinder, hzero]
      have hreleased := hreleases htracked hbodyRun
      have hinstall := installAliasBinder_held_below
        (ctx := ctx) (cur := cur) (limit := limit)
        (Γ := middle) (abs := abs) (remaining := countUses 0 body)
        (uses := uses)
      have hsound := hvalueSound.installThen hinstall hbodySound hreleased
      simpa [Function.comp_def] using hsound
  | constA atom =>
    by_cases hzero : countUses 0 body = 0
    · let bodyInput := installPushedBinder middle 0 uses false
      have hcontinue :
          ((lowerE src fuel bodyInput world body) >>= fun result =>
            let (bodyOutput, bodyEmit, resultValue) := result
            pure (bodyOutput.pop,
              valueEmit ∘ emitOp (.pure atom) ∘ bodyEmit,
              resultValue)).run valueState =
            .ok (output, emit, av) finalState := by
        simpa [hzero, bodyInput, installPushedBinder] using hafterValue
      obtain ⟨bodyResult, bodyState, hbodyRun, hafterBody⟩ :=
        estateBindRun_ok_inv hcontinue
      rcases bodyResult with ⟨bodyOutput, bodyEmit, resultValue⟩
      have hpure :
          (bodyOutput.pop, valueEmit ∘ emitOp (.pure atom) ∘ bodyEmit,
            resultValue) = (output, emit, av) ∧
            bodyState = finalState := by
        simpa using hafterBody
      obtain ⟨hresult, hstate⟩ := hpure
      cases hresult
      subst finalState
      have hbodyAvailable : SelfAvailableBelow ctx cur limit bodyInput := by
        simpa [bodyInput, installPushedBinder, VEnv.bump] using
          (hmiddleAvailable.consSlot middle.depth 0 uses false).bump
      have hbodySound := hexpr hbodyRun hrepresented hbodyAvailable
      have hvalueSound := hexpr hvalueRun
        (hrepresented.of_extends (lowerE_extraExtends hbodyRun))
        havailable
      have htracked : FirstEntryTracks bodyInput uses
          (countUses 0 body) := by
        refine ⟨middle.depth, middle.entries, ?_⟩
        simp [bodyInput, installPushedBinder, hzero]
      have hreleased := hreleases htracked hbodyRun
      have hinstall := materializeConstBinder_below
        (ctx := ctx) (cur := cur) (limit := limit)
        (Γ := middle) (atom := atom) (remaining := 0)
        (uses := uses) (held := false) hvalueSound.stable
      have hsound := hvalueSound.installThen hinstall hbodySound hreleased
      simpa [worldOfUses, Function.comp_def] using hsound
    · let bodyInput := installPushedBinder middle (countUses 0 body)
          uses true
      have hcontinue :
          ((lowerE src fuel bodyInput world body) >>= fun result =>
            let (bodyOutput, bodyEmit, resultValue) := result
            pure (bodyOutput.pop,
              valueEmit ∘ emitOp (.pure atom) ∘ bodyEmit,
              resultValue)).run valueState =
            .ok (output, emit, av) finalState := by
        simpa [hzero, bodyInput, installPushedBinder] using hafterValue
      obtain ⟨bodyResult, bodyState, hbodyRun, hafterBody⟩ :=
        estateBindRun_ok_inv hcontinue
      rcases bodyResult with ⟨bodyOutput, bodyEmit, resultValue⟩
      have hpure :
          (bodyOutput.pop, valueEmit ∘ emitOp (.pure atom) ∘ bodyEmit,
            resultValue) = (output, emit, av) ∧
            bodyState = finalState := by
        simpa using hafterBody
      obtain ⟨hresult, hstate⟩ := hpure
      cases hresult
      subst finalState
      have hbodyAvailable : SelfAvailableBelow ctx cur limit bodyInput := by
        simpa [bodyInput, installPushedBinder, VEnv.bump] using
          (hmiddleAvailable.consSlot middle.depth (countUses 0 body) uses
            true).bump
      have hbodySound := hexpr hbodyRun hrepresented hbodyAvailable
      have hvalueSound := hexpr hvalueRun
        (hrepresented.of_extends (lowerE_extraExtends hbodyRun))
        havailable
      have htracked : FirstEntryTracks bodyInput uses
          (countUses 0 body) := by
        refine ⟨middle.depth, middle.entries, ?_⟩
        simp [bodyInput, installPushedBinder, hzero]
      have hreleased := hreleases htracked hbodyRun
      have hinstall := materializeConstBinder_below
        (ctx := ctx) (cur := cur) (limit := limit)
        (Γ := middle) (atom := atom) (remaining := countUses 0 body)
        (uses := uses) (held := true) hvalueSound.stable
      have hsound := hvalueSound.installThen hinstall hbodySound hreleased
      simpa [worldOfUses, Function.comp_def] using hsound

/-- Semantic let branch of `lowerE`. The bound expression's source value is
installed as the body's leading environment entry — as an alias for a
slot-backed result, materialized for a scalar, and immediately released when
the body never mentions it — and the body's source result is returned after
the logical pop. -/
theorem lowerE_let_run_value_sound
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} {src : IxIR0.Env} {fuel : Nat}
    {input output : VEnv} {world : Owned} {uses : Uses}
    {value body : IxIR0.Expr} {emit : Emit} {av : AVal}
    {state finalState : LowSt} {sourceEnv : List IxIR0.Value}
    {boundSource sourceValue : IxIR0.Value}
    (hvalueExpr : ∀ {middle : VEnv} {valueEmit : Emit} {boundValue : AVal}
      {valueState : LowSt},
      (lowerE src fuel input (worldOfUses uses) value).run state =
        .ok (middle, valueEmit, boundValue) valueState →
      LowerResultValueSound funRel recSelfRel ctx cur input middle
        sourceEnv sourceEnv boundSource (worldOfUses uses)
        valueEmit boundValue)
    (hbodyExpr : ∀ {bodyInput bodyOutput : VEnv} {bodyEmit : Emit}
      {resultValue : AVal} {bodyState bodyFinal : LowSt},
      (lowerE src fuel bodyInput world body).run bodyState =
        .ok (bodyOutput, bodyEmit, resultValue) bodyFinal →
      LowerResultValueSound funRel recSelfRel ctx cur bodyInput bodyOutput
        (boundSource :: sourceEnv) (boundSource :: sourceEnv)
        sourceValue world bodyEmit resultValue)
    (hreleases : LowerEReleasesTrackedFirst src fuel body)
    (hrun : (lowerE src (fuel + 1) input world
      (.letE uses value body)).run state =
        .ok (output, emit, av) finalState) :
    LowerResultValueSound funRel recSelfRel ctx cur input output
      sourceEnv sourceEnv sourceValue world emit av := by
  simp only [lowerE] at hrun
  obtain ⟨valueResult, valueState, hvalueRun, hafterValue⟩ :=
    estateBindRun_ok_inv hrun
  rcases valueResult with ⟨middle, valueEmit, boundValue⟩
  have hvalueSound := hvalueExpr hvalueRun
  cases boundValue with
  | slotA abs =>
    by_cases hzero : countUses 0 body = 0
    · cases uses with
      | erased =>
        obtain ⟨_, _, hthrow, _⟩ := estateBindRun_ok_inv
          (by simpa [hzero] using hafterValue)
        exact (estateThrowRun_not_ok hthrow).elim
      | linear =>
        obtain ⟨_, _, hthrow, _⟩ := estateBindRun_ok_inv
          (by simpa [hzero] using hafterValue)
        exact (estateThrowRun_not_ok hthrow).elim
      | affine =>
        let heldInput :=
          installAliasBinder middle abs 0 Uses.affine true
        let bodyInput :=
          (heldInput.setEntry 0 (.slot abs 0 .affine false)).bump
        have hcontinue :
            ((lowerE src fuel bodyInput world body) >>= fun result =>
              let (bodyOutput, bodyEmit, resultValue) := result
              pure (bodyOutput.pop,
                valueEmit ∘ emitOp (.dropU (.var (middle.rel abs))) ∘
                  bodyEmit,
                resultValue)).run valueState =
              .ok (output, emit, av) finalState := by
          simpa [hzero, heldInput, bodyInput, installAliasBinder,
            VEnv.setEntry, VEnv.bump] using hafterValue
        obtain ⟨bodyResult, bodyState, hbodyRun, hafterBody⟩ :=
          estateBindRun_ok_inv hcontinue
        rcases bodyResult with ⟨bodyOutput, bodyEmit, resultValue⟩
        have hpure :
            (bodyOutput.pop,
              valueEmit ∘ emitOp (.dropU (.var (middle.rel abs))) ∘
                bodyEmit,
              resultValue) = (output, emit, av) ∧
              bodyState = finalState := by
          simpa using hafterBody
        obtain ⟨hresult, hstate⟩ := hpure
        cases hresult
        subst finalState
        have hbodySound := hbodyExpr hbodyRun
        have htracked : FirstEntryTracks bodyInput .affine
            (countUses 0 body) := by
          refine ⟨abs, middle.entries, ?_⟩
          simp [bodyInput, heldInput,
            installAliasBinder, VEnv.setEntry, VEnv.bump, hzero]
        have hreleased := hreleases htracked hbodyRun
        have hentry : heldInput.entries[0]? =
            some (.slot abs 0 Uses.affine true) := by
          simp [heldInput, installAliasBinder]
        have hinstall : InstallBinderValueSound funRel recSelfRel ctx cur
            middle bodyInput sourceEnv boundSource .unique (.slotA abs)
            (emitOp (.dropU (.var (middle.rel abs)))) := by
          refine { toInstallBinderSound := ?_, graphEmits := ?_ }
          · intro rest slots
            have halias := installAliasBinder_held
              (ctx := ctx) (cur := cur) (Γ := middle) (abs := abs)
              (remaining := 0) (uses := Uses.affine) rest slots
            have hdrop := release_slot_affine_owned
              (ctx := ctx) (cur := cur) (Γ := heldInput) (i := 0)
              (abs := abs) hentry rest slots
            have hcomposed := EmitSound.comp halias hdrop
            simpa [bodyInput, heldInput, installAliasBinder, VEnv.rel,
              worldOfUses, Function.comp_def] using hcomposed
          · intro sourceRest rest slots
            have halias := installAliasBinder_held_value_sound
              (funRel := funRel) (recSelfRel := recSelfRel)
              (ctx := ctx) (cur := cur) (Γ := middle)
              (sourceEnv := sourceEnv) (boundSource := boundSource)
              (abs := abs) (remaining := 0) (uses := Uses.affine)
            have hdrop := release_slot_affine_value_sound
              (funRel := funRel) (recSelfRel := recSelfRel)
              (ctx := ctx) (cur := cur) (Γ := heldInput) (i := 0)
              (abs := abs) hentry
              (boundSource :: sourceEnv) sourceRest rest slots
            have hcomposed := EmitSound.comp
              (halias.graphEmits sourceRest rest slots) hdrop
            simpa [bodyInput, heldInput, installAliasBinder, VEnv.rel,
              worldOfUses, Function.comp_def] using hcomposed
        have hsound := hvalueSound.installThen hinstall hbodySound hreleased
        simpa [worldOfUses, Function.comp_def] using hsound
      | many =>
        let heldInput := installAliasBinder middle abs 0 Uses.many true
        let bodyInput :=
          (heldInput.setEntry 0 (.slot abs 0 .many false)).bump
        have hcontinue :
            ((lowerE src fuel bodyInput world body) >>= fun result =>
              let (bodyOutput, bodyEmit, resultValue) := result
              pure (bodyOutput.pop,
                valueEmit ∘ emitOp (.drop (.var (middle.rel abs))) ∘
                  bodyEmit,
                resultValue)).run valueState =
              .ok (output, emit, av) finalState := by
          simpa [hzero, heldInput, bodyInput, installAliasBinder,
            VEnv.setEntry, VEnv.bump] using hafterValue
        obtain ⟨bodyResult, bodyState, hbodyRun, hafterBody⟩ :=
          estateBindRun_ok_inv hcontinue
        rcases bodyResult with ⟨bodyOutput, bodyEmit, resultValue⟩
        have hpure :
            (bodyOutput.pop,
              valueEmit ∘ emitOp (.drop (.var (middle.rel abs))) ∘
                bodyEmit,
              resultValue) = (output, emit, av) ∧
              bodyState = finalState := by
          simpa using hafterBody
        obtain ⟨hresult, hstate⟩ := hpure
        cases hresult
        subst finalState
        have hbodySound := hbodyExpr hbodyRun
        have htracked : FirstEntryTracks bodyInput .many
            (countUses 0 body) := by
          refine ⟨abs, middle.entries, ?_⟩
          simp [bodyInput, heldInput,
            installAliasBinder, VEnv.setEntry, VEnv.bump, hzero]
        have hreleased := hreleases htracked hbodyRun
        have hentry : heldInput.entries[0]? =
            some (.slot abs 0 Uses.many true) := by
          simp [heldInput, installAliasBinder]
        have hinstall : InstallBinderValueSound funRel recSelfRel ctx cur
            middle bodyInput sourceEnv boundSource .shared (.slotA abs)
            (emitOp (.drop (.var (middle.rel abs)))) := by
          refine { toInstallBinderSound := ?_, graphEmits := ?_ }
          · intro rest slots
            have halias := installAliasBinder_held
              (ctx := ctx) (cur := cur) (Γ := middle) (abs := abs)
              (remaining := 0) (uses := Uses.many) rest slots
            have hdrop := release_slot_many_owned
              (ctx := ctx) (cur := cur) (Γ := heldInput) (i := 0)
              (abs := abs) hentry rest slots
            have hcomposed := EmitSound.comp halias hdrop
            simpa [bodyInput, heldInput, installAliasBinder, VEnv.rel,
              worldOfUses, Function.comp_def] using hcomposed
          · intro sourceRest rest slots
            have halias := installAliasBinder_held_value_sound
              (funRel := funRel) (recSelfRel := recSelfRel)
              (ctx := ctx) (cur := cur) (Γ := middle)
              (sourceEnv := sourceEnv) (boundSource := boundSource)
              (abs := abs) (remaining := 0) (uses := Uses.many)
            have hdrop := release_slot_many_value_sound
              (funRel := funRel) (recSelfRel := recSelfRel)
              (ctx := ctx) (cur := cur) (Γ := heldInput) (i := 0)
              (abs := abs) hentry
              (boundSource :: sourceEnv) sourceRest rest slots
            have hcomposed := EmitSound.comp
              (halias.graphEmits sourceRest rest slots) hdrop
            simpa [bodyInput, heldInput, installAliasBinder, VEnv.rel,
              worldOfUses, Function.comp_def] using hcomposed
        have hsound := hvalueSound.installThen hinstall hbodySound hreleased
        simpa [worldOfUses, Function.comp_def] using hsound
    · let bodyInput := installAliasBinder middle abs
          (countUses 0 body) uses true
      have hcontinue :
          ((lowerE src fuel bodyInput world body) >>= fun result =>
            let (bodyOutput, bodyEmit, resultValue) := result
            pure (bodyOutput.pop, valueEmit ∘ bodyEmit, resultValue)).run
            valueState = .ok (output, emit, av) finalState := by
        simpa [hzero, bodyInput, installAliasBinder] using hafterValue
      obtain ⟨bodyResult, bodyState, hbodyRun, hafterBody⟩ :=
        estateBindRun_ok_inv hcontinue
      rcases bodyResult with ⟨bodyOutput, bodyEmit, resultValue⟩
      have hpure :
          (bodyOutput.pop, valueEmit ∘ bodyEmit, resultValue) =
              (output, emit, av) ∧ bodyState = finalState := by
        simpa using hafterBody
      obtain ⟨hresult, hstate⟩ := hpure
      cases hresult
      subst finalState
      have hbodySound := hbodyExpr hbodyRun
      have htracked : FirstEntryTracks bodyInput uses
          (countUses 0 body) := by
        refine ⟨abs, middle.entries, ?_⟩
        simp [bodyInput, installAliasBinder, hzero]
      have hreleased := hreleases htracked hbodyRun
      have hinstall := installAliasBinder_held_value_sound
        (funRel := funRel) (recSelfRel := recSelfRel)
        (ctx := ctx) (cur := cur) (Γ := middle)
        (sourceEnv := sourceEnv) (boundSource := boundSource)
        (abs := abs) (remaining := countUses 0 body) (uses := uses)
      have hsound := hvalueSound.installThen hinstall hbodySound hreleased
      simpa [Function.comp_def] using hsound
  | constA atom =>
    by_cases hzero : countUses 0 body = 0
    · let bodyInput := installPushedBinder middle 0 uses false
      have hcontinue :
          ((lowerE src fuel bodyInput world body) >>= fun result =>
            let (bodyOutput, bodyEmit, resultValue) := result
            pure (bodyOutput.pop,
              valueEmit ∘ emitOp (.pure atom) ∘ bodyEmit,
              resultValue)).run valueState =
            .ok (output, emit, av) finalState := by
        simpa [hzero, bodyInput, installPushedBinder] using hafterValue
      obtain ⟨bodyResult, bodyState, hbodyRun, hafterBody⟩ :=
        estateBindRun_ok_inv hcontinue
      rcases bodyResult with ⟨bodyOutput, bodyEmit, resultValue⟩
      have hpure :
          (bodyOutput.pop, valueEmit ∘ emitOp (.pure atom) ∘ bodyEmit,
            resultValue) = (output, emit, av) ∧
            bodyState = finalState := by
        simpa using hafterBody
      obtain ⟨hresult, hstate⟩ := hpure
      cases hresult
      subst finalState
      have hbodySound := hbodyExpr hbodyRun
      have htracked : FirstEntryTracks bodyInput uses
          (countUses 0 body) := by
        refine ⟨middle.depth, middle.entries, ?_⟩
        simp [bodyInput, installPushedBinder, hzero]
      have hreleased := hreleases htracked hbodyRun
      have hinstall := materializeConstBinder_value_sound
        (funRel := funRel) (recSelfRel := recSelfRel)
        (ctx := ctx) (cur := cur) (Γ := middle)
        (sourceEnv := sourceEnv) (boundSource := boundSource)
        (atom := atom) (remaining := 0)
        (uses := uses) (held := false) hvalueSound.stable
      have hsound := hvalueSound.installThen hinstall hbodySound hreleased
      simpa [worldOfUses, Function.comp_def] using hsound
    · let bodyInput := installPushedBinder middle (countUses 0 body)
          uses true
      have hcontinue :
          ((lowerE src fuel bodyInput world body) >>= fun result =>
            let (bodyOutput, bodyEmit, resultValue) := result
            pure (bodyOutput.pop,
              valueEmit ∘ emitOp (.pure atom) ∘ bodyEmit,
              resultValue)).run valueState =
            .ok (output, emit, av) finalState := by
        simpa [hzero, bodyInput, installPushedBinder] using hafterValue
      obtain ⟨bodyResult, bodyState, hbodyRun, hafterBody⟩ :=
        estateBindRun_ok_inv hcontinue
      rcases bodyResult with ⟨bodyOutput, bodyEmit, resultValue⟩
      have hpure :
          (bodyOutput.pop, valueEmit ∘ emitOp (.pure atom) ∘ bodyEmit,
            resultValue) = (output, emit, av) ∧
            bodyState = finalState := by
        simpa using hafterBody
      obtain ⟨hresult, hstate⟩ := hpure
      cases hresult
      subst finalState
      have hbodySound := hbodyExpr hbodyRun
      have htracked : FirstEntryTracks bodyInput uses
          (countUses 0 body) := by
        refine ⟨middle.depth, middle.entries, ?_⟩
        simp [bodyInput, installPushedBinder, hzero]
      have hreleased := hreleases htracked hbodyRun
      have hinstall := materializeConstBinder_value_sound
        (funRel := funRel) (recSelfRel := recSelfRel)
        (ctx := ctx) (cur := cur) (Γ := middle)
        (sourceEnv := sourceEnv) (boundSource := boundSource)
        (atom := atom) (remaining := countUses 0 body)
        (uses := uses) (held := true) hvalueSound.stable
      have hsound := hvalueSound.installThen hinstall hbodySound hreleased
      simpa [worldOfUses, Function.comp_def] using hsound

/-- One complete bounded expression step. The semantic recursive premises
are separated from the two compiler-state facts they cannot express:
successful let bodies release their counted binder, and the final target
context represents declarations accumulated by lambda lifting. -/
theorem lowerE_run_sound_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat} {src : IxIR0.Env}
    {fuel : Nat}
    (hexpr : LowerEPreservesBelow ctx cur limit src fuel)
    (hspine : LowerSpinePreservesBelow ctx cur limit src fuel)
    (hargsNext : LowerArgsPreservesBelow ctx cur limit src (fuel + 1))
    (hargsNextExtra : LowerArgsExtraMonotone src (fuel + 1))
    (hrestNext : ApplyRestPreservesBelow ctx cur limit src (fuel + 1))
    (hrestNextExtra : ApplyRestExtraMonotone src (fuel + 1))
    (hborrow : LowerBorrowPreservesBelow ctx cur limit src fuel)
    (hdecls : SourceDeclContractsBelow src ctx limit)
    (hreleases : ∀ body, LowerEReleasesTrackedFirst src fuel body)
    {input output : VEnv} {world : Owned} {expr : IxIR0.Expr}
    {emit : Emit} {av : AVal} {state finalState : LowSt}
    (hrepresented : ExtraRepresented ctx finalState)
    (hrun : (lowerE src (fuel + 1) input world expr).run state =
      .ok (output, emit, av) finalState)
    (havailable : SelfAvailableBelow ctx cur limit input) :
    LowerResultSoundBelow ctx cur limit input output world emit av := by
  cases expr with
  | var index =>
    exact lowerE_nonbinding_run_sound_below hspine hargsNext hargsNextExtra
      hrestNext hrestNextExtra hborrow hdecls (.var index) hrun
      hrepresented havailable
  | ref address =>
    exact lowerE_nonbinding_run_sound_below hspine hargsNext hargsNextExtra
      hrestNext hrestNextExtra hborrow hdecls (.ref address) hrun
      hrepresented havailable
  | app function argument =>
    exact lowerE_nonbinding_run_sound_below hspine hargsNext hargsNextExtra
      hrestNext hrestNextExtra hborrow hdecls (.app function argument)
      hrun hrepresented havailable
  | lam uses body =>
    exact lowerE_lam_run_sound_below hrepresented hrun
  | letE uses value body =>
    exact lowerE_let_run_sound_below hexpr (hreleases body) hrun
      hrepresented havailable
  | proj index source =>
    exact lowerE_nonbinding_run_sound_below hspine hargsNext hargsNextExtra
      hrestNext hrestNextExtra hborrow hdecls (.proj index source) hrun
      hrepresented havailable
  | lit literal =>
    exact lowerE_nonbinding_run_sound_below hspine hargsNext hargsNextExtra
      hrestNext hrestNextExtra hborrow hdecls (.lit literal) hrun
      hrepresented havailable
  | erased =>
    exact lowerE_nonbinding_run_sound_below hspine hargsNext hargsNextExtra
      hrestNext hrestNextExtra hborrow hdecls .erased hrun hrepresented
      havailable

/-- Non-erased dynamic heads compose their proved `lowerE` result with the
shared `applyRest` branch. -/
theorem lowerSpine_dynamic_apply_verified {ctx : Ctx} {cur : FnDef}
    (src : IxIR0.Env) (fuel : Nat)
    (input functionOutput output : VEnv) (head : IxIR0.Expr)
    (args : List IxIR0.Expr) (emitFunction emitArgs : Emit)
    (function : AVal) (avs : List AVal)
    (state middleState finalState : LowSt)
    (hshape : DynamicSpineHead head)
    (hfunctionRun :
      (lowerE src (Nat.succ fuel) input .shared head).run state =
        .ok (functionOutput, emitFunction, function) middleState)
    (hfunction : LowerResultSound ctx cur input functionOutput .shared
      emitFunction function)
    (hfunctionNe : function ≠ .constA .erased)
    (hargsRun :
      (lowerArgs src fuel functionOutput
        (args.map (fun arg => (arg, Owned.shared)))).run middleState =
        .ok (output, emitArgs, avs) finalState)
    (hargsSound : LowerArgsSound ctx cur functionOutput output
      ((args.map (fun arg => (arg, Owned.shared))).map Prod.snd)
      emitArgs avs)
    (hworldsHomogeneous :
      ((args.map (fun arg => (arg, Owned.shared))).map Prod.snd) =
        List.replicate avs.length .shared)
    (hcontract : ApplyOwnershipContract ctx) :
    (lowerSpine src (Nat.succ (Nat.succ fuel)) input .shared head
      args).run state =
        .ok (output.bump,
          (emitFunction ∘ emitArgs) ∘
            emitOp (.apply (function.toAtom output)
              (avs.map (·.toAtom output)).toArray),
          .slotA output.depth) finalState ∧
      LowerResultSound ctx cur input output.bump .shared
        ((emitFunction ∘ emitArgs) ∘
          emitOp (.apply (function.toAtom output)
            (avs.map (·.toAtom output)).toArray))
        (.slotA output.depth) := by
  have happly := applyRest_shared_verified (ctx := ctx) (cur := cur)
    src fuel input functionOutput output emitFunction emitArgs function
    args avs middleState finalState hfunctionNe hargsRun hargsSound
    hworldsHomogeneous hfunction hcontract
  constructor
  · cases hshape <;>
      simp only [lowerSpine] <;>
      rw [estateBindRun, hfunctionRun] <;>
      exact happly.1
  · exact happly.2

/-- If the dynamically lowered head is erased, its arguments are evaluated
and released through the erased `applyRest` branch at either result world. -/
theorem lowerSpine_dynamic_erased_verified {ctx : Ctx} {cur : FnDef}
    (src : IxIR0.Env) (fuel : Nat)
    (input functionOutput output : VEnv) (resultWorld : Owned)
    (head : IxIR0.Expr) (args : List IxIR0.Expr)
    (emitFunction emitArgs : Emit) (avs : List AVal)
    (state middleState finalState : LowSt)
    (hshape : DynamicSpineHead head)
    (hfunctionRun :
      (lowerE src (Nat.succ fuel) input .shared head).run state =
        .ok (functionOutput, emitFunction, .constA .erased) middleState)
    (hfunction : LowerResultSound ctx cur input functionOutput .shared
      emitFunction (.constA .erased))
    (hargsRun :
      (lowerArgs src fuel functionOutput
        (args.map (fun arg => (arg, Owned.shared)))).run middleState =
        .ok (output, emitArgs, avs) finalState)
    (hargsSound : LowerArgsSound ctx cur functionOutput output
      ((args.map (fun arg => (arg, Owned.shared))).map Prod.snd)
      emitArgs avs)
    (hworldsHomogeneous :
      ((args.map (fun arg => (arg, Owned.shared))).map Prod.snd) =
        List.replicate avs.length .shared) :
    (lowerSpine src (Nat.succ (Nat.succ fuel)) input resultWorld head
      args).run state =
        .ok ((releaseAll output avs).1,
          (emitFunction ∘ emitArgs) ∘ (releaseAll output avs).2,
          .constA .erased) finalState ∧
      LowerResultSound ctx cur input (releaseAll output avs).1 resultWorld
        ((emitFunction ∘ emitArgs) ∘ (releaseAll output avs).2)
        (.constA .erased) := by
  have happly := applyRest_erased_verified (ctx := ctx) (cur := cur)
    src fuel input functionOutput output resultWorld emitFunction emitArgs
    args avs middleState finalState hargsRun hargsSound
    hworldsHomogeneous hfunction
  constructor
  · cases hshape <;>
      simp only [lowerSpine] <;>
      rw [estateBindRun, hfunctionRun] <;>
      exact happly.1
  · exact happly.2

/-- The terminal direct-call branch of the executable `knownCall`: once the
proved argument prefix has no over-application tail, it is consumed by the
callee contract and the fresh result slot is returned. -/
theorem knownCall_call_terminal_verified {ctx : Ctx} {cur d : FnDef}
    (src : IxIR0.Env) (fuel : Nat) (input output : VEnv)
    (f : Ixon.Address) (n : Nat) (argWorlds : List Owned)
    (resultDemand : Owned) (args : List IxIR0.Expr)
    (emit : Emit) (avs : List AVal) (state finalState : LowSt)
    (hargsRun :
      (lowerArgs src fuel input
        ((args.take n).zip (padWorlds argWorlds n))).run state =
        .ok (output, emit, avs) finalState)
    (hargsSound : LowerArgsSound ctx cur input output
      (((args.take n).zip (padWorlds argWorlds n)).map Prod.snd)
      emit avs)
    (hle : args.length ≤ n)
    (hdecl : ctx.decls f = some (.fn d))
    (hcontract : FnOwnershipContract ctx d
      (((args.take n).zip (padWorlds argWorlds n)).map Prod.snd)) :
    (knownCall src (Nat.succ fuel) input (.call f ·) n argWorlds
      resultDemand args).run state =
        .ok (output.bump,
          emit ∘ emitOp
            (.call f (avs.map (·.toAtom output)).toArray),
          .slotA output.depth) finalState ∧
      LowerResultSound ctx cur input output.bump d.result
        (emit ∘ emitOp
          (.call f (avs.map (·.toAtom output)).toArray))
        (.slotA output.depth) := by
  constructor
  · simp only [knownCall]
    rw [estateBindRun, hargsRun]
    simp [hle]
  · exact hargsSound.call_owned hdecl hcontract

/-- Terminal recursive-self branch of `knownCall`, paired with the current
function's ownership contract. -/
theorem knownCall_callSelf_terminal_verified {ctx : Ctx} {cur : FnDef}
    (src : IxIR0.Env) (fuel : Nat) (input output : VEnv)
    (n : Nat) (argWorlds : List Owned) (resultDemand : Owned)
    (args : List IxIR0.Expr) (emit : Emit) (avs : List AVal)
    (state finalState : LowSt)
    (hargsRun :
      (lowerArgs src fuel input
        ((args.take n).zip (padWorlds argWorlds n))).run state =
        .ok (output, emit, avs) finalState)
    (hargsSound : LowerArgsSound ctx cur input output
      (((args.take n).zip (padWorlds argWorlds n)).map Prod.snd)
      emit avs)
    (hle : args.length ≤ n)
    (hcontract : FnOwnershipContract ctx cur
      (((args.take n).zip (padWorlds argWorlds n)).map Prod.snd)) :
    (knownCall src (Nat.succ fuel) input (.callSelf ·) n argWorlds
      resultDemand args).run state =
        .ok (output.bump,
          emit ∘ emitOp
            (.callSelf (avs.map (·.toAtom output)).toArray),
          .slotA output.depth) finalState ∧
      LowerResultSound ctx cur input output.bump cur.result
        (emit ∘ emitOp
          (.callSelf (avs.map (·.toAtom output)).toArray))
        (.slotA output.depth) := by
  constructor
  · simp only [knownCall]
    rw [estateBindRun, hargsRun]
    simp [hle]
  · exact hargsSound.callSelf_owned hcontract

/-- Exact-saturation `recSelf` dispatch in `lowerSpine`. The v1 source
restriction supplies an all-shared telescope and the current function
contract closes the recursive call. -/
theorem lowerSpine_recSelf_terminal_verified {ctx : Ctx} {cur : FnDef}
    (src : IxIR0.Env) (fuel : Nat) (input output : VEnv)
    (i arity : Nat) (args : List IxIR0.Expr)
    (emit : Emit) (avs : List AVal) (state finalState : LowSt)
    (hentry : input.entries[i]? = some (.recSelf arity))
    (hargsLength : args.length = arity)
    (hargsRun :
      (lowerArgs src fuel input
        ((args.take arity).zip
          (padWorlds (List.replicate arity .shared) arity))).run state =
        .ok (output, emit, avs) finalState)
    (hargsSound : LowerArgsSound ctx cur input output
      (((args.take arity).zip
        (padWorlds (List.replicate arity .shared) arity)).map Prod.snd)
      emit avs)
    (hcontract : FnOwnershipContract ctx cur
      (((args.take arity).zip
        (padWorlds (List.replicate arity .shared) arity)).map Prod.snd))
    (hresult : cur.result = .shared) :
    (lowerSpine src (Nat.succ (Nat.succ fuel)) input .shared (.var i)
      args).run state =
        .ok (output.bump,
          emit ∘ emitOp
            (.callSelf (avs.map (·.toAtom output)).toArray),
          .slotA output.depth) finalState ∧
      LowerResultSound ctx cur input output.bump .shared
        (emit ∘ emitOp
          (.callSelf (avs.map (·.toAtom output)).toArray))
        (.slotA output.depth) := by
  have hknown := knownCall_callSelf_terminal_verified
    (ctx := ctx) (cur := cur) src fuel input output arity
    (List.replicate arity .shared) .shared args emit avs state finalState
    hargsRun hargsSound (by omega) hcontract
  constructor
  · simp only [lowerSpine]
    rw [hentry]
    simp only
    rw [if_neg (by omega)]
    have hrequire :
        (requireResultWorld .shared .shared).run state = .ok () state := by
      rfl
    rw [estateBindRun, hrequire]
    simp only
    exact hknown.1
  · simpa [hresult] using hknown.2

/-- Over-applied recursive-self branch of `knownCall`: call the current
function on its saturated prefix, protect the shared recursive result, then
apply the remaining shared arguments. -/
theorem knownCall_callSelf_overapplied_verified
    {ctx : Ctx} {cur : FnDef}
    (src : IxIR0.Env) (fuel : Nat)
    (input prefixOutput output : VEnv)
    (n : Nat) (argWorlds : List Owned) (args : List IxIR0.Expr)
    (emitPrefix emitTail : Emit) (prefixAVals tailAVals : List AVal)
    (state middleState finalState : LowSt)
    (hprefixRun :
      (lowerArgs src (Nat.succ fuel) input
        ((args.take n).zip (padWorlds argWorlds n))).run state =
        .ok (prefixOutput, emitPrefix, prefixAVals) middleState)
    (hprefixSound : LowerArgsSound ctx cur input prefixOutput
      (((args.take n).zip (padWorlds argWorlds n)).map Prod.snd)
      emitPrefix prefixAVals)
    (hover : n < args.length)
    (hcallContract : FnOwnershipContract ctx cur
      (((args.take n).zip (padWorlds argWorlds n)).map Prod.snd))
    (hresult : cur.result = .shared)
    (htailRun :
      (lowerArgs src fuel prefixOutput.bump
        ((args.drop n).map (fun arg => (arg, Owned.shared)))).run
          middleState =
        .ok (output, emitTail, tailAVals) finalState)
    (htailSound : LowerArgsSound ctx cur prefixOutput.bump output
      (((args.drop n).map (fun arg => (arg, Owned.shared))).map Prod.snd)
      emitTail tailAVals)
    (htailWorlds :
      (((args.drop n).map (fun arg => (arg, Owned.shared))).map Prod.snd) =
        List.replicate tailAVals.length .shared)
    (happlyContract : ApplyOwnershipContract ctx) :
    (knownCall src (Nat.succ (Nat.succ fuel)) input (.callSelf ·) n
      argWorlds .shared args).run state =
        .ok (output.bump,
          ((emitPrefix ∘ emitOp (.callSelf
              (prefixAVals.map (·.toAtom prefixOutput)).toArray)) ∘
            emitTail) ∘
            emitOp (.apply
              ((AVal.slotA prefixOutput.depth).toAtom output)
              (tailAVals.map (·.toAtom output)).toArray),
          .slotA output.depth) finalState ∧
      LowerResultSound ctx cur input output.bump .shared
        (((emitPrefix ∘ emitOp (.callSelf
            (prefixAVals.map (·.toAtom prefixOutput)).toArray)) ∘
          emitTail) ∘
          emitOp (.apply
            ((AVal.slotA prefixOutput.depth).toAtom output)
            (tailAVals.map (·.toAtom output)).toArray))
        (.slotA output.depth) := by
  have hcall : LowerResultSound ctx cur input prefixOutput.bump .shared
      (emitPrefix ∘ emitOp (.callSelf
        (prefixAVals.map (·.toAtom prefixOutput)).toArray))
      (.slotA prefixOutput.depth) := by
    simpa [hresult] using hprefixSound.callSelf_owned hcallContract
  have happly := applyRest_shared_verified (ctx := ctx) (cur := cur)
    src fuel input prefixOutput.bump output
    (emitPrefix ∘ emitOp (.callSelf
      (prefixAVals.map (·.toAtom prefixOutput)).toArray))
    emitTail (.slotA prefixOutput.depth) (args.drop n) tailAVals
    middleState finalState (by simp) htailRun htailSound htailWorlds
    hcall happlyContract
  constructor
  · simp only [knownCall]
    rw [estateBindRun, hprefixRun]
    simp only
    rw [if_neg (Nat.not_le.mpr hover)]
    exact happly.1
  · exact happly.2

/-- Over-applied `recSelf` dispatch in `lowerSpine`, including the recursive
prefix call and higher-order application of the tail. -/
theorem lowerSpine_recSelf_overapplied_verified
    {ctx : Ctx} {cur : FnDef}
    (src : IxIR0.Env) (fuel : Nat)
    (input prefixOutput output : VEnv)
    (i arity : Nat) (args : List IxIR0.Expr)
    (emitPrefix emitTail : Emit) (prefixAVals tailAVals : List AVal)
    (state middleState finalState : LowSt)
    (hentry : input.entries[i]? = some (.recSelf arity))
    (hprefixRun :
      (lowerArgs src (Nat.succ fuel) input
        ((args.take arity).zip
          (padWorlds (List.replicate arity .shared) arity))).run state =
        .ok (prefixOutput, emitPrefix, prefixAVals) middleState)
    (hprefixSound : LowerArgsSound ctx cur input prefixOutput
      (((args.take arity).zip
        (padWorlds (List.replicate arity .shared) arity)).map Prod.snd)
      emitPrefix prefixAVals)
    (hover : arity < args.length)
    (hcallContract : FnOwnershipContract ctx cur
      (((args.take arity).zip
        (padWorlds (List.replicate arity .shared) arity)).map Prod.snd))
    (hresult : cur.result = .shared)
    (htailRun :
      (lowerArgs src fuel prefixOutput.bump
        ((args.drop arity).map (fun arg => (arg, Owned.shared)))).run
          middleState =
        .ok (output, emitTail, tailAVals) finalState)
    (htailSound : LowerArgsSound ctx cur prefixOutput.bump output
      (((args.drop arity).map
        (fun arg => (arg, Owned.shared))).map Prod.snd)
      emitTail tailAVals)
    (htailWorlds :
      (((args.drop arity).map
        (fun arg => (arg, Owned.shared))).map Prod.snd) =
        List.replicate tailAVals.length .shared)
    (happlyContract : ApplyOwnershipContract ctx) :
    (lowerSpine src (Nat.succ (Nat.succ (Nat.succ fuel))) input .shared
      (.var i) args).run state =
        .ok (output.bump,
          ((emitPrefix ∘ emitOp (.callSelf
              (prefixAVals.map (·.toAtom prefixOutput)).toArray)) ∘
            emitTail) ∘
            emitOp (.apply
              ((AVal.slotA prefixOutput.depth).toAtom output)
              (tailAVals.map (·.toAtom output)).toArray),
          .slotA output.depth) finalState ∧
      LowerResultSound ctx cur input output.bump .shared
        (((emitPrefix ∘ emitOp (.callSelf
            (prefixAVals.map (·.toAtom prefixOutput)).toArray)) ∘
          emitTail) ∘
          emitOp (.apply
            ((AVal.slotA prefixOutput.depth).toAtom output)
            (tailAVals.map (·.toAtom output)).toArray))
        (.slotA output.depth) := by
  have hknown := knownCall_callSelf_overapplied_verified
    (ctx := ctx) (cur := cur) src fuel input prefixOutput output arity
    (List.replicate arity .shared) args emitPrefix emitTail prefixAVals
    tailAVals state middleState finalState hprefixRun hprefixSound hover
    hcallContract hresult htailRun htailSound htailWorlds happlyContract
  constructor
  · simp only [lowerSpine]
    rw [hentry]
    simp only
    rw [if_neg (by omega)]
    have hrequire :
        (requireResultWorld .shared .shared).run state = .ok () state := by
      rfl
    rw [estateBindRun, hrequire]
    simp only
    exact hknown.1
  · exact hknown.2

/-- Exact-saturation definition dispatch in `lowerSpine`, reducing its
source declaration/world checks to the terminal direct-call `knownCall`
rule. -/
theorem lowerSpine_ref_call_terminal_verified {ctx : Ctx} {cur d : FnDef}
    (src : IxIR0.Env) (fuel : Nat) (input output : VEnv)
    (f : Ixon.Address) (result : Owned) (body : IxIR0.Expr)
    (args : List IxIR0.Expr) (emit : Emit) (avs : List AVal)
    (state finalState : LowSt)
    (hsrc : src f = some (.defn result body))
    (hargsLength : args.length = lamArity body)
    (hargsRun :
      (lowerArgs src fuel input
        ((args.take (lamArity body)).zip
          (padWorlds ((lamUses body).map worldOfUses)
            (lamArity body)))).run state =
        .ok (output, emit, avs) finalState)
    (hargsSound : LowerArgsSound ctx cur input output
      (((args.take (lamArity body)).zip
        (padWorlds ((lamUses body).map worldOfUses)
          (lamArity body))).map Prod.snd)
      emit avs)
    (hdecl : ctx.decls f = some (.fn d))
    (hcontract : FnOwnershipContract ctx d
      (((args.take (lamArity body)).zip
        (padWorlds ((lamUses body).map worldOfUses)
          (lamArity body))).map Prod.snd))
    (hresult : d.result = result) :
    (lowerSpine src (Nat.succ (Nat.succ fuel)) input result (.ref f)
      args).run state =
        .ok (output.bump,
          emit ∘ emitOp (.call f
            (avs.map (·.toAtom output)).toArray),
          .slotA output.depth) finalState ∧
      LowerResultSound ctx cur input output.bump result
        (emit ∘ emitOp (.call f
          (avs.map (·.toAtom output)).toArray))
        (.slotA output.depth) := by
  have hknown := knownCall_call_terminal_verified (ctx := ctx) (cur := cur)
    src fuel input output f (lamArity body)
    ((lamUses body).map worldOfUses) result args emit avs state finalState
    hargsRun hargsSound (by omega) hdecl hcontract
  constructor
  · simp only [lowerSpine]
    rw [hsrc]
    simp only
    rw [if_neg (by omega)]
    have hrequire :
        (requireResultWorld result
          (if args.length == lamArity body then result else .shared)).run
            state = .ok () state := by
      simp [hargsLength, requireResultWorld]
    rw [estateBindRun, hrequire]
    simp only
    exact hknown.1
  · simpa [hresult] using hknown.2

/-- Exact-saturation recursor dispatch. Once the recursor has been lowered
to a target function, its all-shared firing telescope is an ordinary direct
call under that declaration's contract. -/
theorem lowerSpine_ref_recursor_terminal_verified
    {ctx : Ctx} {cur d : FnDef}
    (src : IxIR0.Env) (fuel : Nat) (input output : VEnv)
    (f : Ixon.Address) (numArgs : Nat) (natLit : Bool)
    (rules : Array IxIR0.RecRule) (args : List IxIR0.Expr)
    (emit : Emit) (avs : List AVal) (state finalState : LowSt)
    (hsrc : src f = some (.recursor numArgs natLit rules))
    (hargsLength : args.length = numArgs + 1)
    (hargsRun :
      (lowerArgs src fuel input
        ((args.take (numArgs + 1)).zip
          (padWorlds (List.replicate (numArgs + 1) .shared)
            (numArgs + 1)))).run state =
        .ok (output, emit, avs) finalState)
    (hargsSound : LowerArgsSound ctx cur input output
      (((args.take (numArgs + 1)).zip
        (padWorlds (List.replicate (numArgs + 1) .shared)
          (numArgs + 1))).map Prod.snd)
      emit avs)
    (hdecl : ctx.decls f = some (.fn d))
    (hcontract : FnOwnershipContract ctx d
      (((args.take (numArgs + 1)).zip
        (padWorlds (List.replicate (numArgs + 1) .shared)
          (numArgs + 1))).map Prod.snd))
    (hresult : d.result = .shared) :
    (lowerSpine src (Nat.succ (Nat.succ fuel)) input .shared (.ref f)
      args).run state =
        .ok (output.bump,
          emit ∘ emitOp (.call f
            (avs.map (·.toAtom output)).toArray),
          .slotA output.depth) finalState ∧
      LowerResultSound ctx cur input output.bump .shared
        (emit ∘ emitOp (.call f
          (avs.map (·.toAtom output)).toArray))
        (.slotA output.depth) := by
  have hknown := knownCall_call_terminal_verified (ctx := ctx) (cur := cur)
    src fuel input output f (numArgs + 1)
    (List.replicate (numArgs + 1) .shared) .shared args emit avs
    state finalState hargsRun hargsSound (by omega) hdecl hcontract
  constructor
  · simp only [lowerSpine]
    rw [hsrc]
    simp only
    rw [if_neg (by omega)]
    have hrequire :
        (requireResultWorld .shared .shared).run state = .ok () state := by
      rfl
    rw [estateBindRun, hrequire]
    simp only
    exact hknown.1
  · simpa [hresult] using hknown.2

/-- The over-applied direct-call branch of `knownCall`. The saturated prefix
is consumed by the callee contract, its shared result is protected while the
remaining shared arguments are lowered, and the resulting prefix is consumed
by `apply`. -/
theorem knownCall_call_overapplied_verified {ctx : Ctx} {cur d : FnDef}
    (src : IxIR0.Env) (fuel : Nat)
    (input prefixOutput output : VEnv)
    (f : Ixon.Address) (n : Nat) (argWorlds : List Owned)
    (args : List IxIR0.Expr)
    (emitPrefix emitTail : Emit) (prefixAVals tailAVals : List AVal)
    (state middleState finalState : LowSt)
    (hprefixRun :
      (lowerArgs src (Nat.succ fuel) input
        ((args.take n).zip (padWorlds argWorlds n))).run state =
        .ok (prefixOutput, emitPrefix, prefixAVals) middleState)
    (hprefixSound : LowerArgsSound ctx cur input prefixOutput
      (((args.take n).zip (padWorlds argWorlds n)).map Prod.snd)
      emitPrefix prefixAVals)
    (hover : n < args.length)
    (hdecl : ctx.decls f = some (.fn d))
    (hcallContract : FnOwnershipContract ctx d
      (((args.take n).zip (padWorlds argWorlds n)).map Prod.snd))
    (hresult : d.result = .shared)
    (htailRun :
      (lowerArgs src fuel prefixOutput.bump
        ((args.drop n).map (fun arg => (arg, Owned.shared)))).run
          middleState =
        .ok (output, emitTail, tailAVals) finalState)
    (htailSound : LowerArgsSound ctx cur prefixOutput.bump output
      (((args.drop n).map (fun arg => (arg, Owned.shared))).map Prod.snd)
      emitTail tailAVals)
    (htailWorlds :
      (((args.drop n).map (fun arg => (arg, Owned.shared))).map Prod.snd) =
        List.replicate tailAVals.length .shared)
    (happlyContract : ApplyOwnershipContract ctx) :
    (knownCall src (Nat.succ (Nat.succ fuel)) input (.call f ·) n
      argWorlds .shared args).run state =
        .ok (output.bump,
          ((emitPrefix ∘ emitOp (.call f
              (prefixAVals.map (·.toAtom prefixOutput)).toArray)) ∘
            emitTail) ∘
            emitOp (.apply
              ((AVal.slotA prefixOutput.depth).toAtom output)
              (tailAVals.map (·.toAtom output)).toArray),
          .slotA output.depth) finalState ∧
      LowerResultSound ctx cur input output.bump .shared
        (((emitPrefix ∘ emitOp (.call f
            (prefixAVals.map (·.toAtom prefixOutput)).toArray)) ∘
          emitTail) ∘
          emitOp (.apply
            ((AVal.slotA prefixOutput.depth).toAtom output)
            (tailAVals.map (·.toAtom output)).toArray))
        (.slotA output.depth) := by
  have hcall : LowerResultSound ctx cur input prefixOutput.bump .shared
      (emitPrefix ∘ emitOp (.call f
        (prefixAVals.map (·.toAtom prefixOutput)).toArray))
      (.slotA prefixOutput.depth) := by
    simpa [hresult] using hprefixSound.call_owned hdecl hcallContract
  have happly := applyRest_shared_verified (ctx := ctx) (cur := cur)
    src fuel input prefixOutput.bump output
    (emitPrefix ∘ emitOp (.call f
      (prefixAVals.map (·.toAtom prefixOutput)).toArray))
    emitTail (.slotA prefixOutput.depth) (args.drop n) tailAVals
    middleState finalState (by simp) htailRun htailSound htailWorlds
    hcall happlyContract
  constructor
  · simp only [knownCall]
    rw [estateBindRun, hprefixRun]
    simp only
    rw [if_neg (Nat.not_le.mpr hover)]
    exact happly.1
  · exact happly.2

/-- Over-applied definition dispatch in `lowerSpine`: the source declaration
check selects a shared saturated prefix call, after which `knownCall` lowers
and applies the remaining shared arguments. -/
theorem lowerSpine_ref_call_overapplied_verified
    {ctx : Ctx} {cur d : FnDef}
    (src : IxIR0.Env) (fuel : Nat)
    (input prefixOutput output : VEnv)
    (f : Ixon.Address) (body : IxIR0.Expr) (args : List IxIR0.Expr)
    (emitPrefix emitTail : Emit) (prefixAVals tailAVals : List AVal)
    (state middleState finalState : LowSt)
    (hsrc : src f = some (.defn .shared body))
    (hprefixRun :
      (lowerArgs src (Nat.succ fuel) input
        ((args.take (lamArity body)).zip
          (padWorlds ((lamUses body).map worldOfUses)
            (lamArity body)))).run state =
        .ok (prefixOutput, emitPrefix, prefixAVals) middleState)
    (hprefixSound : LowerArgsSound ctx cur input prefixOutput
      (((args.take (lamArity body)).zip
        (padWorlds ((lamUses body).map worldOfUses)
          (lamArity body))).map Prod.snd)
      emitPrefix prefixAVals)
    (hover : lamArity body < args.length)
    (hdecl : ctx.decls f = some (.fn d))
    (hcallContract : FnOwnershipContract ctx d
      (((args.take (lamArity body)).zip
        (padWorlds ((lamUses body).map worldOfUses)
          (lamArity body))).map Prod.snd))
    (hresult : d.result = .shared)
    (htailRun :
      (lowerArgs src fuel prefixOutput.bump
        ((args.drop (lamArity body)).map
          (fun arg => (arg, Owned.shared)))).run middleState =
        .ok (output, emitTail, tailAVals) finalState)
    (htailSound : LowerArgsSound ctx cur prefixOutput.bump output
      (((args.drop (lamArity body)).map
        (fun arg => (arg, Owned.shared))).map Prod.snd)
      emitTail tailAVals)
    (htailWorlds :
      (((args.drop (lamArity body)).map
        (fun arg => (arg, Owned.shared))).map Prod.snd) =
        List.replicate tailAVals.length .shared)
    (happlyContract : ApplyOwnershipContract ctx) :
    (lowerSpine src (Nat.succ (Nat.succ (Nat.succ fuel))) input .shared
      (.ref f) args).run state =
        .ok (output.bump,
          ((emitPrefix ∘ emitOp (.call f
              (prefixAVals.map (·.toAtom prefixOutput)).toArray)) ∘
            emitTail) ∘
            emitOp (.apply
              ((AVal.slotA prefixOutput.depth).toAtom output)
              (tailAVals.map (·.toAtom output)).toArray),
          .slotA output.depth) finalState ∧
      LowerResultSound ctx cur input output.bump .shared
        (((emitPrefix ∘ emitOp (.call f
            (prefixAVals.map (·.toAtom prefixOutput)).toArray)) ∘
          emitTail) ∘
          emitOp (.apply
            ((AVal.slotA prefixOutput.depth).toAtom output)
            (tailAVals.map (·.toAtom output)).toArray))
        (.slotA output.depth) := by
  have hknown := knownCall_call_overapplied_verified
    (ctx := ctx) (cur := cur) src fuel input prefixOutput output f
    (lamArity body) ((lamUses body).map worldOfUses) args
    emitPrefix emitTail prefixAVals tailAVals state middleState finalState
    hprefixRun hprefixSound hover hdecl hcallContract hresult htailRun
    htailSound htailWorlds happlyContract
  constructor
  · simp only [lowerSpine]
    rw [hsrc]
    simp only
    rw [if_neg (by omega)]
    have hrequire :
        (requireResultWorld .shared
          (if args.length == lamArity body then .shared else .shared)).run
            state = .ok () state := by
      simp [requireResultWorld]
    rw [estateBindRun, hrequire]
    simp only
    exact hknown.1
  · exact hknown.2

/-- Over-applied recursor dispatch is the all-shared recursor analogue of
over-applied definition dispatch: direct-call the firing prefix, then apply
the remaining arguments to its shared result. -/
theorem lowerSpine_ref_recursor_overapplied_verified
    {ctx : Ctx} {cur d : FnDef}
    (src : IxIR0.Env) (fuel : Nat)
    (input prefixOutput output : VEnv)
    (f : Ixon.Address) (numArgs : Nat) (natLit : Bool)
    (rules : Array IxIR0.RecRule) (args : List IxIR0.Expr)
    (emitPrefix emitTail : Emit) (prefixAVals tailAVals : List AVal)
    (state middleState finalState : LowSt)
    (hsrc : src f = some (.recursor numArgs natLit rules))
    (hprefixRun :
      (lowerArgs src (Nat.succ fuel) input
        ((args.take (numArgs + 1)).zip
          (padWorlds (List.replicate (numArgs + 1) .shared)
            (numArgs + 1)))).run state =
        .ok (prefixOutput, emitPrefix, prefixAVals) middleState)
    (hprefixSound : LowerArgsSound ctx cur input prefixOutput
      (((args.take (numArgs + 1)).zip
        (padWorlds (List.replicate (numArgs + 1) .shared)
          (numArgs + 1))).map Prod.snd)
      emitPrefix prefixAVals)
    (hover : numArgs + 1 < args.length)
    (hdecl : ctx.decls f = some (.fn d))
    (hcallContract : FnOwnershipContract ctx d
      (((args.take (numArgs + 1)).zip
        (padWorlds (List.replicate (numArgs + 1) .shared)
          (numArgs + 1))).map Prod.snd))
    (hresult : d.result = .shared)
    (htailRun :
      (lowerArgs src fuel prefixOutput.bump
        ((args.drop (numArgs + 1)).map
          (fun arg => (arg, Owned.shared)))).run middleState =
        .ok (output, emitTail, tailAVals) finalState)
    (htailSound : LowerArgsSound ctx cur prefixOutput.bump output
      (((args.drop (numArgs + 1)).map
        (fun arg => (arg, Owned.shared))).map Prod.snd)
      emitTail tailAVals)
    (htailWorlds :
      (((args.drop (numArgs + 1)).map
        (fun arg => (arg, Owned.shared))).map Prod.snd) =
        List.replicate tailAVals.length .shared)
    (happlyContract : ApplyOwnershipContract ctx) :
    (lowerSpine src (Nat.succ (Nat.succ (Nat.succ fuel))) input .shared
      (.ref f) args).run state =
        .ok (output.bump,
          ((emitPrefix ∘ emitOp (.call f
              (prefixAVals.map (·.toAtom prefixOutput)).toArray)) ∘
            emitTail) ∘
            emitOp (.apply
              ((AVal.slotA prefixOutput.depth).toAtom output)
              (tailAVals.map (·.toAtom output)).toArray),
          .slotA output.depth) finalState ∧
      LowerResultSound ctx cur input output.bump .shared
        (((emitPrefix ∘ emitOp (.call f
            (prefixAVals.map (·.toAtom prefixOutput)).toArray)) ∘
          emitTail) ∘
          emitOp (.apply
            ((AVal.slotA prefixOutput.depth).toAtom output)
            (tailAVals.map (·.toAtom output)).toArray))
        (.slotA output.depth) := by
  have hknown := knownCall_call_overapplied_verified
    (ctx := ctx) (cur := cur) src fuel input prefixOutput output f
    (numArgs + 1) (List.replicate (numArgs + 1) .shared) args
    emitPrefix emitTail prefixAVals tailAVals state middleState finalState
    hprefixRun hprefixSound hover hdecl hcallContract hresult htailRun
    htailSound htailWorlds happlyContract
  constructor
  · simp only [lowerSpine]
    rw [hsrc]
    simp only
    rw [if_neg (by omega)]
    have hrequire :
        (requireResultWorld .shared .shared).run state = .ok () state := by
      rfl
    rw [estateBindRun, hrequire]
    simp only
    exact hknown.1
  · exact hknown.2

/-- The homogeneous constructor counterpart of
`knownCall_call_terminal_verified`. Whole-value mode scoping makes every
field world equal to the newly allocated node's world. -/
theorem knownCall_alloc_terminal_verified {ctx : Ctx} {cur : FnDef}
    (src : IxIR0.Env) (fuel : Nat) (input output : VEnv)
    (world : Owned) (cid : CtorId) (n : Nat)
    (argWorlds : List Owned) (resultDemand : Owned)
    (args : List IxIR0.Expr) (emit : Emit) (avs : List AVal)
    (state finalState : LowSt)
    (hargsRun :
      (lowerArgs src fuel input
        ((args.take n).zip (padWorlds argWorlds n))).run state =
        .ok (output, emit, avs) finalState)
    (hargsSound : LowerArgsSound ctx cur input output
      (((args.take n).zip (padWorlds argWorlds n)).map Prod.snd)
      emit avs)
    (hworldsHomogeneous :
      ((args.take n).zip (padWorlds argWorlds n)).map Prod.snd =
        List.replicate avs.length world)
    (hle : args.length ≤ n) :
    (knownCall src (Nat.succ fuel) input (.alloc world cid ·) n
      argWorlds resultDemand args).run state =
        .ok (output.bump,
          emit ∘ emitOp (.alloc world cid
            (avs.map (·.toAtom output)).toArray),
          .slotA output.depth) finalState ∧
      LowerResultSound ctx cur input output.bump world
        (emit ∘ emitOp (.alloc world cid
          (avs.map (·.toAtom output)).toArray))
        (.slotA output.depth) := by
  constructor
  · simp only [knownCall]
    rw [estateBindRun, hargsRun]
    simp [hle]
  · have hhomogeneous : LowerArgsSound ctx cur input output
        (List.replicate avs.length world) emit avs := by
      simpa [hworldsHomogeneous] using hargsSound
    exact hhomogeneous.alloc_owned

/-- Over-applied shared-constructor branch of `knownCall`: allocate the
saturated field prefix, protect the fresh constructor root, then emit the
remaining higher-order application. -/
theorem knownCall_alloc_overapplied_verified {ctx : Ctx} {cur : FnDef}
    (src : IxIR0.Env) (fuel : Nat)
    (input prefixOutput output : VEnv)
    (cid : CtorId) (n : Nat) (argWorlds : List Owned)
    (args : List IxIR0.Expr)
    (emitPrefix emitTail : Emit) (prefixAVals tailAVals : List AVal)
    (state middleState finalState : LowSt)
    (hprefixRun :
      (lowerArgs src (Nat.succ fuel) input
        ((args.take n).zip (padWorlds argWorlds n))).run state =
        .ok (prefixOutput, emitPrefix, prefixAVals) middleState)
    (hprefixSound : LowerArgsSound ctx cur input prefixOutput
      (((args.take n).zip (padWorlds argWorlds n)).map Prod.snd)
      emitPrefix prefixAVals)
    (hprefixWorlds :
      ((args.take n).zip (padWorlds argWorlds n)).map Prod.snd =
        List.replicate prefixAVals.length .shared)
    (hover : n < args.length)
    (htailRun :
      (lowerArgs src fuel prefixOutput.bump
        ((args.drop n).map (fun arg => (arg, Owned.shared)))).run
          middleState =
        .ok (output, emitTail, tailAVals) finalState)
    (htailSound : LowerArgsSound ctx cur prefixOutput.bump output
      (((args.drop n).map (fun arg => (arg, Owned.shared))).map Prod.snd)
      emitTail tailAVals)
    (htailWorlds :
      (((args.drop n).map (fun arg => (arg, Owned.shared))).map Prod.snd) =
        List.replicate tailAVals.length .shared)
    (happlyContract : ApplyOwnershipContract ctx) :
    (knownCall src (Nat.succ (Nat.succ fuel)) input
      (.alloc .shared cid ·) n argWorlds .shared args).run state =
        .ok (output.bump,
          ((emitPrefix ∘ emitOp (.alloc .shared cid
              (prefixAVals.map (·.toAtom prefixOutput)).toArray)) ∘
            emitTail) ∘
            emitOp (.apply
              ((AVal.slotA prefixOutput.depth).toAtom output)
              (tailAVals.map (·.toAtom output)).toArray),
          .slotA output.depth) finalState ∧
      LowerResultSound ctx cur input output.bump .shared
        (((emitPrefix ∘ emitOp (.alloc .shared cid
            (prefixAVals.map (·.toAtom prefixOutput)).toArray)) ∘
          emitTail) ∘
          emitOp (.apply
            ((AVal.slotA prefixOutput.depth).toAtom output)
            (tailAVals.map (·.toAtom output)).toArray))
        (.slotA output.depth) := by
  have hhomogeneous : LowerArgsSound ctx cur input prefixOutput
      (List.replicate prefixAVals.length .shared)
      emitPrefix prefixAVals := by
    simpa [hprefixWorlds] using hprefixSound
  have halloc : LowerResultSound ctx cur input prefixOutput.bump .shared
      (emitPrefix ∘ emitOp (.alloc .shared cid
        (prefixAVals.map (·.toAtom prefixOutput)).toArray))
      (.slotA prefixOutput.depth) := hhomogeneous.alloc_owned
  have happly := applyRest_shared_verified (ctx := ctx) (cur := cur)
    src fuel input prefixOutput.bump output
    (emitPrefix ∘ emitOp (.alloc .shared cid
      (prefixAVals.map (·.toAtom prefixOutput)).toArray))
    emitTail (.slotA prefixOutput.depth) (args.drop n) tailAVals
    middleState finalState (by simp) htailRun htailSound htailWorlds
    halloc happlyContract
  constructor
  · simp only [knownCall]
    rw [estateBindRun, hprefixRun]
    simp only
    rw [if_neg (Nat.not_le.mpr hover)]
    exact happly.1
  · exact happly.2

/-- Over-applied constructor dispatch in `lowerSpine`. Only the shared world
can reach the emitted tail `apply`; unique over-application is rejected by
`applyRest`'s world guard. -/
theorem lowerSpine_ref_ctor_overapplied_verified
    {ctx : Ctx} {cur : FnDef}
    (src : IxIR0.Env) (fuel : Nat)
    (input prefixOutput output : VEnv)
    (f : Ixon.Address) (tag arity : Nat) (args : List IxIR0.Expr)
    (emitPrefix emitTail : Emit) (prefixAVals tailAVals : List AVal)
    (state middleState finalState : LowSt)
    (hsrc : src f = some (.ctor tag arity))
    (hprefixRun :
      (lowerArgs src (Nat.succ fuel) input
        ((args.take arity).zip
          (padWorlds (List.replicate arity .shared) arity))).run state =
        .ok (prefixOutput, emitPrefix, prefixAVals) middleState)
    (hprefixSound : LowerArgsSound ctx cur input prefixOutput
      (((args.take arity).zip
        (padWorlds (List.replicate arity .shared) arity)).map Prod.snd)
      emitPrefix prefixAVals)
    (hprefixWorlds :
      ((args.take arity).zip
        (padWorlds (List.replicate arity .shared) arity)).map Prod.snd =
        List.replicate prefixAVals.length .shared)
    (hover : arity < args.length)
    (htailRun :
      (lowerArgs src fuel prefixOutput.bump
        ((args.drop arity).map (fun arg => (arg, Owned.shared)))).run
          middleState =
        .ok (output, emitTail, tailAVals) finalState)
    (htailSound : LowerArgsSound ctx cur prefixOutput.bump output
      (((args.drop arity).map
        (fun arg => (arg, Owned.shared))).map Prod.snd)
      emitTail tailAVals)
    (htailWorlds :
      (((args.drop arity).map
        (fun arg => (arg, Owned.shared))).map Prod.snd) =
        List.replicate tailAVals.length .shared)
    (happlyContract : ApplyOwnershipContract ctx) :
    (lowerSpine src (Nat.succ (Nat.succ (Nat.succ fuel))) input .shared
      (.ref f) args).run state =
        .ok (output.bump,
          ((emitPrefix ∘ emitOp (.alloc .shared (ctorIdOf f tag)
              (prefixAVals.map (·.toAtom prefixOutput)).toArray)) ∘
            emitTail) ∘
            emitOp (.apply
              ((AVal.slotA prefixOutput.depth).toAtom output)
              (tailAVals.map (·.toAtom output)).toArray),
          .slotA output.depth) finalState ∧
      LowerResultSound ctx cur input output.bump .shared
        (((emitPrefix ∘ emitOp (.alloc .shared (ctorIdOf f tag)
            (prefixAVals.map (·.toAtom prefixOutput)).toArray)) ∘
          emitTail) ∘
          emitOp (.apply
            ((AVal.slotA prefixOutput.depth).toAtom output)
            (tailAVals.map (·.toAtom output)).toArray))
        (.slotA output.depth) := by
  have hknown := knownCall_alloc_overapplied_verified
    (ctx := ctx) (cur := cur) src fuel input prefixOutput output
    (ctorIdOf f tag) arity (List.replicate arity .shared) args
    emitPrefix emitTail prefixAVals tailAVals state middleState finalState
    hprefixRun hprefixSound hprefixWorlds hover htailRun htailSound
    htailWorlds happlyContract
  constructor
  · simp only [lowerSpine]
    rw [hsrc]
    simp only
    rw [if_neg (by omega)]
    exact hknown.1
  · exact hknown.2

/-- Terminal partial-application branch of `knownCall`: all supplied shared
arguments become captures of one fresh pap node. -/
theorem knownCall_papp_terminal_verified {ctx : Ctx} {cur : FnDef}
    (src : IxIR0.Env) (fuel : Nat) (input output : VEnv)
    (f : Ixon.Address) (d : Decl) (n : Nat)
    (argWorlds : List Owned) (resultDemand : Owned)
    (args : List IxIR0.Expr) (emit : Emit) (avs : List AVal)
    (state finalState : LowSt)
    (hargsRun :
      (lowerArgs src fuel input
        ((args.take n).zip (padWorlds argWorlds n))).run state =
        .ok (output, emit, avs) finalState)
    (hargsSound : LowerArgsSound ctx cur input output
      (((args.take n).zip (padWorlds argWorlds n)).map Prod.snd)
      emit avs)
    (hworldsHomogeneous :
      ((args.take n).zip (padWorlds argWorlds n)).map Prod.snd =
        List.replicate avs.length .shared)
    (hle : args.length ≤ n)
    (hdecl : ctx.decls f = some d)
    (hunder : avs.length < declArity d) :
    (knownCall src (Nat.succ fuel) input (.papp f ·) n argWorlds
      resultDemand args).run state =
        .ok (output.bump,
          emit ∘ emitOp (.papp f
            (avs.map (·.toAtom output)).toArray),
          .slotA output.depth) finalState ∧
      LowerResultSound ctx cur input output.bump .shared
        (emit ∘ emitOp (.papp f
          (avs.map (·.toAtom output)).toArray))
        (.slotA output.depth) := by
  constructor
  · simp only [knownCall]
    rw [estateBindRun, hargsRun]
    simp [hle]
  · have hhomogeneous : LowerArgsSound ctx cur input output
        (List.replicate avs.length .shared) emit avs := by
      simpa [hworldsHomogeneous] using hargsSound
    exact hhomogeneous.papp_owned hdecl hunder

/-- Terminal scalar-extern branch of `knownCall`. Successful evaluation
certifies all argument descriptors and the result scalar, so the result may
inhabit the requested world. -/
theorem knownCall_extern_terminal_verified {ctx : Ctx} {cur : FnDef}
    (src : IxIR0.Env) (fuel : Nat) (input output : VEnv)
    (f : Ixon.Address) (n : Nat) (argWorlds : List Owned)
    (resultDemand : Owned) (args : List IxIR0.Expr)
    (emit : Emit) (avs : List AVal) (state finalState : LowSt)
    (hargsRun :
      (lowerArgs src fuel input
        ((args.take n).zip (padWorlds argWorlds n))).run state =
        .ok (output, emit, avs) finalState)
    (hargsSound : LowerArgsSound ctx cur input output
      (((args.take n).zip (padWorlds argWorlds n)).map Prod.snd)
      emit avs)
    (hworldsHomogeneous :
      ((args.take n).zip (padWorlds argWorlds n)).map Prod.snd =
        List.replicate avs.length .shared)
    (hle : args.length ≤ n) :
    (knownCall src (Nat.succ fuel) input (.extern f ·) n argWorlds
      resultDemand args).run state =
        .ok (output.bump,
          emit ∘ emitOp (.extern f
            (avs.map (·.toAtom output)).toArray),
          .slotA output.depth) finalState ∧
      LowerResultSound ctx cur input output.bump resultDemand
        (emit ∘ emitOp (.extern f
          (avs.map (·.toAtom output)).toArray))
        (.slotA output.depth) := by
  constructor
  · simp only [knownCall]
    rw [estateBindRun, hargsRun]
    simp [hle]
  · have hhomogeneous : LowerArgsSound ctx cur input output
        (List.replicate avs.length .shared) emit avs := by
      simpa [hworldsHomogeneous] using hargsSound
    exact hhomogeneous.extern_owned

/-- Exact-saturation extern dispatch in `lowerSpine`. -/
theorem lowerSpine_ref_extern_terminal_verified
    {ctx : Ctx} {cur : FnDef}
    (src : IxIR0.Env) (fuel : Nat) (input output : VEnv)
    (world : Owned) (f : Ixon.Address) (arity : Nat)
    (args : List IxIR0.Expr) (emit : Emit) (avs : List AVal)
    (state finalState : LowSt)
    (hsrc : src f = some (.extern arity))
    (hargsLength : args.length = arity)
    (hargsRun :
      (lowerArgs src fuel input
        ((args.take arity).zip
          (padWorlds (List.replicate arity .shared) arity))).run state =
        .ok (output, emit, avs) finalState)
    (hargsSound : LowerArgsSound ctx cur input output
      (((args.take arity).zip
        (padWorlds (List.replicate arity .shared) arity)).map Prod.snd)
      emit avs)
    (hworldsHomogeneous :
      ((args.take arity).zip
        (padWorlds (List.replicate arity .shared) arity)).map Prod.snd =
          List.replicate avs.length .shared) :
    (lowerSpine src (Nat.succ (Nat.succ fuel)) input world (.ref f)
      args).run state =
        .ok (output.bump,
          emit ∘ emitOp (.extern f
            (avs.map (·.toAtom output)).toArray),
          .slotA output.depth) finalState ∧
      LowerResultSound ctx cur input output.bump world
        (emit ∘ emitOp (.extern f
          (avs.map (·.toAtom output)).toArray))
        (.slotA output.depth) := by
  have hknown := knownCall_extern_terminal_verified
    (ctx := ctx) (cur := cur) src fuel input output f arity
    (List.replicate arity .shared) world args emit avs state finalState
    hargsRun hargsSound hworldsHomogeneous (by omega)
  constructor
  · simp only [lowerSpine]
    rw [hsrc]
    simp only
    rw [if_neg (by omega)]
    exact hknown.1
  · exact hknown.2

/-- Over-applied scalar-extern branch of `knownCall`. The scalar prefix
result is ownership-inert but may still be framed as a shared result while
the remaining arguments are lowered and passed to `apply`. -/
theorem knownCall_extern_overapplied_verified
    {ctx : Ctx} {cur : FnDef}
    (src : IxIR0.Env) (fuel : Nat)
    (input prefixOutput output : VEnv)
    (f : Ixon.Address) (n : Nat) (argWorlds : List Owned)
    (args : List IxIR0.Expr)
    (emitPrefix emitTail : Emit) (prefixAVals tailAVals : List AVal)
    (state middleState finalState : LowSt)
    (hprefixRun :
      (lowerArgs src (Nat.succ fuel) input
        ((args.take n).zip (padWorlds argWorlds n))).run state =
        .ok (prefixOutput, emitPrefix, prefixAVals) middleState)
    (hprefixSound : LowerArgsSound ctx cur input prefixOutput
      (((args.take n).zip (padWorlds argWorlds n)).map Prod.snd)
      emitPrefix prefixAVals)
    (hprefixWorlds :
      ((args.take n).zip (padWorlds argWorlds n)).map Prod.snd =
        List.replicate prefixAVals.length .shared)
    (hover : n < args.length)
    (htailRun :
      (lowerArgs src fuel prefixOutput.bump
        ((args.drop n).map (fun arg => (arg, Owned.shared)))).run
          middleState =
        .ok (output, emitTail, tailAVals) finalState)
    (htailSound : LowerArgsSound ctx cur prefixOutput.bump output
      (((args.drop n).map (fun arg => (arg, Owned.shared))).map Prod.snd)
      emitTail tailAVals)
    (htailWorlds :
      (((args.drop n).map (fun arg => (arg, Owned.shared))).map Prod.snd) =
        List.replicate tailAVals.length .shared)
    (happlyContract : ApplyOwnershipContract ctx) :
    (knownCall src (Nat.succ (Nat.succ fuel)) input (.extern f ·) n
      argWorlds .shared args).run state =
        .ok (output.bump,
          ((emitPrefix ∘ emitOp (.extern f
              (prefixAVals.map (·.toAtom prefixOutput)).toArray)) ∘
            emitTail) ∘
            emitOp (.apply
              ((AVal.slotA prefixOutput.depth).toAtom output)
              (tailAVals.map (·.toAtom output)).toArray),
          .slotA output.depth) finalState ∧
      LowerResultSound ctx cur input output.bump .shared
        (((emitPrefix ∘ emitOp (.extern f
            (prefixAVals.map (·.toAtom prefixOutput)).toArray)) ∘
          emitTail) ∘
          emitOp (.apply
            ((AVal.slotA prefixOutput.depth).toAtom output)
            (tailAVals.map (·.toAtom output)).toArray))
        (.slotA output.depth) := by
  have hhomogeneous : LowerArgsSound ctx cur input prefixOutput
      (List.replicate prefixAVals.length .shared)
      emitPrefix prefixAVals := by
    simpa [hprefixWorlds] using hprefixSound
  have hextern : LowerResultSound ctx cur input prefixOutput.bump .shared
      (emitPrefix ∘ emitOp (.extern f
        (prefixAVals.map (·.toAtom prefixOutput)).toArray))
      (.slotA prefixOutput.depth) := hhomogeneous.extern_owned
  have happly := applyRest_shared_verified (ctx := ctx) (cur := cur)
    src fuel input prefixOutput.bump output
    (emitPrefix ∘ emitOp (.extern f
      (prefixAVals.map (·.toAtom prefixOutput)).toArray))
    emitTail (.slotA prefixOutput.depth) (args.drop n) tailAVals
    middleState finalState (by simp) htailRun htailSound htailWorlds
    hextern happlyContract
  constructor
  · simp only [knownCall]
    rw [estateBindRun, hprefixRun]
    simp only
    rw [if_neg (Nat.not_le.mpr hover)]
    exact happly.1
  · exact happly.2

/-- Over-applied extern dispatch in `lowerSpine`, pairing the saturated
scalar oracle prefix with the emitted tail `apply`. -/
theorem lowerSpine_ref_extern_overapplied_verified
    {ctx : Ctx} {cur : FnDef}
    (src : IxIR0.Env) (fuel : Nat)
    (input prefixOutput output : VEnv)
    (f : Ixon.Address) (arity : Nat) (args : List IxIR0.Expr)
    (emitPrefix emitTail : Emit) (prefixAVals tailAVals : List AVal)
    (state middleState finalState : LowSt)
    (hsrc : src f = some (.extern arity))
    (hprefixRun :
      (lowerArgs src (Nat.succ fuel) input
        ((args.take arity).zip
          (padWorlds (List.replicate arity .shared) arity))).run state =
        .ok (prefixOutput, emitPrefix, prefixAVals) middleState)
    (hprefixSound : LowerArgsSound ctx cur input prefixOutput
      (((args.take arity).zip
        (padWorlds (List.replicate arity .shared) arity)).map Prod.snd)
      emitPrefix prefixAVals)
    (hprefixWorlds :
      ((args.take arity).zip
        (padWorlds (List.replicate arity .shared) arity)).map Prod.snd =
        List.replicate prefixAVals.length .shared)
    (hover : arity < args.length)
    (htailRun :
      (lowerArgs src fuel prefixOutput.bump
        ((args.drop arity).map (fun arg => (arg, Owned.shared)))).run
          middleState =
        .ok (output, emitTail, tailAVals) finalState)
    (htailSound : LowerArgsSound ctx cur prefixOutput.bump output
      (((args.drop arity).map
        (fun arg => (arg, Owned.shared))).map Prod.snd)
      emitTail tailAVals)
    (htailWorlds :
      (((args.drop arity).map
        (fun arg => (arg, Owned.shared))).map Prod.snd) =
        List.replicate tailAVals.length .shared)
    (happlyContract : ApplyOwnershipContract ctx) :
    (lowerSpine src (Nat.succ (Nat.succ (Nat.succ fuel))) input .shared
      (.ref f) args).run state =
        .ok (output.bump,
          ((emitPrefix ∘ emitOp (.extern f
              (prefixAVals.map (·.toAtom prefixOutput)).toArray)) ∘
            emitTail) ∘
            emitOp (.apply
              ((AVal.slotA prefixOutput.depth).toAtom output)
              (tailAVals.map (·.toAtom output)).toArray),
          .slotA output.depth) finalState ∧
      LowerResultSound ctx cur input output.bump .shared
        (((emitPrefix ∘ emitOp (.extern f
            (prefixAVals.map (·.toAtom prefixOutput)).toArray)) ∘
          emitTail) ∘
          emitOp (.apply
            ((AVal.slotA prefixOutput.depth).toAtom output)
            (tailAVals.map (·.toAtom output)).toArray))
        (.slotA output.depth) := by
  have hknown := knownCall_extern_overapplied_verified
    (ctx := ctx) (cur := cur) src fuel input prefixOutput output f arity
    (List.replicate arity .shared) args emitPrefix emitTail prefixAVals
    tailAVals state middleState finalState hprefixRun hprefixSound
    hprefixWorlds hover htailRun htailSound htailWorlds happlyContract
  constructor
  · simp only [lowerSpine]
    rw [hsrc]
    simp only
    rw [if_neg (by omega)]
    exact hknown.1
  · exact hknown.2

/-- Under-applied all-`many` definition dispatch in `lowerSpine`. The source
checks select `papp`; target arity agreement establishes that the emitted
capture prefix is strictly under-saturating. -/
theorem lowerSpine_ref_def_partial_verified {ctx : Ctx} {cur d : FnDef}
    (src : IxIR0.Env) (fuel : Nat) (input output : VEnv)
    (f : Ixon.Address) (body : IxIR0.Expr) (args : List IxIR0.Expr)
    (emit : Emit) (avs : List AVal) (state finalState : LowSt)
    (hsrc : src f = some (.defn .shared body))
    (hunderSource : args.length < lamArity body)
    (hpapSafe : papSafe body = true)
    (hargsRun :
      (lowerArgs src fuel input
        ((args.take args.length).zip
          (padWorlds (List.replicate args.length .shared)
            args.length))).run state =
        .ok (output, emit, avs) finalState)
    (hargsSound : LowerArgsSound ctx cur input output
      (((args.take args.length).zip
        (padWorlds (List.replicate args.length .shared)
          args.length)).map Prod.snd)
      emit avs)
    (hworldsHomogeneous :
      ((args.take args.length).zip
        (padWorlds (List.replicate args.length .shared)
          args.length)).map Prod.snd =
        List.replicate avs.length .shared)
    (hdecl : ctx.decls f = some (.fn d))
    (harity : d.arity = lamArity body) :
    (lowerSpine src (Nat.succ (Nat.succ fuel)) input .shared (.ref f)
      args).run state =
        .ok (output.bump,
          emit ∘ emitOp (.papp f
            (avs.map (·.toAtom output)).toArray),
          .slotA output.depth) finalState ∧
      LowerResultSound ctx cur input output.bump .shared
        (emit ∘ emitOp (.papp f
          (avs.map (·.toAtom output)).toArray))
        (.slotA output.depth) := by
  have havsLength : avs.length = args.length := by
    have hlength := congrArg List.length hworldsHomogeneous
    simp [padWorlds] at hlength
    omega
  have hunderTarget : avs.length < declArity (.fn d) := by
    simp only [declArity]
    omega
  have hknown := knownCall_papp_terminal_verified
    (ctx := ctx) (cur := cur) src fuel input output f (.fn d)
    args.length (List.replicate args.length .shared) .shared args emit avs
    state finalState hargsRun hargsSound hworldsHomogeneous
    (Nat.le_refl _) hdecl hunderTarget
  constructor
  · simp only [lowerSpine]
    rw [hsrc]
    simp [hunderSource, hpapSafe]
    exact hknown.1
  · exact hknown.2

/-- Under-applied recursor dispatch shares the same pap ownership rule. The
target declaration's arity is tied to the source recursor firing arity. -/
theorem lowerSpine_ref_recursor_partial_verified
    {ctx : Ctx} {cur : FnDef}
    (src : IxIR0.Env) (fuel : Nat) (input output : VEnv)
    (f : Ixon.Address) (numArgs : Nat) (natLit : Bool)
    (rules : Array IxIR0.RecRule) (targetDecl : Decl)
    (args : List IxIR0.Expr) (emit : Emit) (avs : List AVal)
    (state finalState : LowSt)
    (hsrc : src f = some (.recursor numArgs natLit rules))
    (hunderSource : args.length < numArgs + 1)
    (hargsRun :
      (lowerArgs src fuel input
        ((args.take args.length).zip
          (padWorlds (List.replicate args.length .shared)
            args.length))).run state =
        .ok (output, emit, avs) finalState)
    (hargsSound : LowerArgsSound ctx cur input output
      (((args.take args.length).zip
        (padWorlds (List.replicate args.length .shared)
          args.length)).map Prod.snd)
      emit avs)
    (hworldsHomogeneous :
      ((args.take args.length).zip
        (padWorlds (List.replicate args.length .shared)
          args.length)).map Prod.snd =
        List.replicate avs.length .shared)
    (hdecl : ctx.decls f = some targetDecl)
    (harity : declArity targetDecl = numArgs + 1) :
    (lowerSpine src (Nat.succ (Nat.succ fuel)) input .shared (.ref f)
      args).run state =
        .ok (output.bump,
          emit ∘ emitOp (.papp f
            (avs.map (·.toAtom output)).toArray),
          .slotA output.depth) finalState ∧
      LowerResultSound ctx cur input output.bump .shared
        (emit ∘ emitOp (.papp f
          (avs.map (·.toAtom output)).toArray))
        (.slotA output.depth) := by
  have havsLength : avs.length = args.length := by
    have hlength := congrArg List.length hworldsHomogeneous
    simp [padWorlds] at hlength
    omega
  have hunderTarget : avs.length < declArity targetDecl := by omega
  have hknown := knownCall_papp_terminal_verified
    (ctx := ctx) (cur := cur) src fuel input output f targetDecl
    args.length (List.replicate args.length .shared) .shared args emit avs
    state finalState hargsRun hargsSound hworldsHomogeneous
    (Nat.le_refl _) hdecl hunderTarget
  constructor
  · simp only [lowerSpine]
    rw [hsrc]
    simp [hunderSource]
    exact hknown.1
  · exact hknown.2

/-- Under-applied extern dispatch also builds a shared pap; no oracle call is
made until later saturation. -/
theorem lowerSpine_ref_extern_partial_verified
    {ctx : Ctx} {cur : FnDef}
    (src : IxIR0.Env) (fuel : Nat) (input output : VEnv)
    (f : Ixon.Address) (arity : Nat) (args : List IxIR0.Expr)
    (emit : Emit) (avs : List AVal) (state finalState : LowSt)
    (hsrc : src f = some (.extern arity))
    (hunderSource : args.length < arity)
    (hargsRun :
      (lowerArgs src fuel input
        ((args.take args.length).zip
          (padWorlds (List.replicate args.length .shared)
            args.length))).run state =
        .ok (output, emit, avs) finalState)
    (hargsSound : LowerArgsSound ctx cur input output
      (((args.take args.length).zip
        (padWorlds (List.replicate args.length .shared)
          args.length)).map Prod.snd)
      emit avs)
    (hworldsHomogeneous :
      ((args.take args.length).zip
        (padWorlds (List.replicate args.length .shared)
          args.length)).map Prod.snd =
        List.replicate avs.length .shared)
    (hdecl : ctx.decls f = some (.extern arity)) :
    (lowerSpine src (Nat.succ (Nat.succ fuel)) input .shared (.ref f)
      args).run state =
        .ok (output.bump,
          emit ∘ emitOp (.papp f
            (avs.map (·.toAtom output)).toArray),
          .slotA output.depth) finalState ∧
      LowerResultSound ctx cur input output.bump .shared
        (emit ∘ emitOp (.papp f
          (avs.map (·.toAtom output)).toArray))
        (.slotA output.depth) := by
  have havsLength : avs.length = args.length := by
    have hlength := congrArg List.length hworldsHomogeneous
    simp [padWorlds] at hlength
    omega
  have hunderTarget : avs.length < declArity (.extern arity) := by
    simp only [declArity]
    omega
  have hknown := knownCall_papp_terminal_verified
    (ctx := ctx) (cur := cur) src fuel input output f (.extern arity)
    args.length (List.replicate args.length .shared) .shared args emit avs
    state finalState hargsRun hargsSound hworldsHomogeneous
    (Nat.le_refl _) hdecl hunderTarget
  constructor
  · simp only [lowerSpine]
    rw [hsrc]
    simp [hunderSource]
    exact hknown.1
  · exact hknown.2

/-- Under-applied constructor dispatch, including the stateful eta-wrapper
lookup/creation step. The eventual whole-program proof supplies the generated
wrapper declaration in `ctx`; its arity makes the following `papp` strictly
under-saturated. -/
theorem lowerSpine_ref_ctor_partial_verified
    {ctx : Ctx} {cur wrapperDef : FnDef}
    (src : IxIR0.Env) (fuel : Nat) (input output : VEnv)
    (f wrapper : Ixon.Address) (tag arity : Nat)
    (args : List IxIR0.Expr) (emit : Emit) (avs : List AVal)
    (state wrapperState finalState : LowSt)
    (hsrc : src f = some (.ctor tag arity))
    (hunderSource : args.length < arity)
    (hwrapperRun : (wrapperFor f tag arity).run state =
      .ok wrapper wrapperState)
    (hargsRun :
      (lowerArgs src fuel input
        ((args.take args.length).zip
          (padWorlds (List.replicate args.length .shared)
            args.length))).run wrapperState =
        .ok (output, emit, avs) finalState)
    (hargsSound : LowerArgsSound ctx cur input output
      (((args.take args.length).zip
        (padWorlds (List.replicate args.length .shared)
          args.length)).map Prod.snd)
      emit avs)
    (hworldsHomogeneous :
      ((args.take args.length).zip
        (padWorlds (List.replicate args.length .shared)
          args.length)).map Prod.snd =
        List.replicate avs.length .shared)
    (hdecl : ctx.decls wrapper = some (.fn wrapperDef))
    (harity : wrapperDef.arity = arity) :
    (lowerSpine src (Nat.succ (Nat.succ fuel)) input .shared (.ref f)
      args).run state =
        .ok (output.bump,
          emit ∘ emitOp (.papp wrapper
            (avs.map (·.toAtom output)).toArray),
          .slotA output.depth) finalState ∧
      LowerResultSound ctx cur input output.bump .shared
        (emit ∘ emitOp (.papp wrapper
          (avs.map (·.toAtom output)).toArray))
        (.slotA output.depth) := by
  have havsLength : avs.length = args.length := by
    have hlength := congrArg List.length hworldsHomogeneous
    simp [padWorlds] at hlength
    omega
  have hunderTarget : avs.length < declArity (.fn wrapperDef) := by
    simp only [declArity]
    omega
  have hknown := knownCall_papp_terminal_verified
    (ctx := ctx) (cur := cur) src fuel input output wrapper
    (.fn wrapperDef) args.length (List.replicate args.length .shared)
    .shared args emit avs wrapperState finalState hargsRun hargsSound
    hworldsHomogeneous (Nat.le_refl _) hdecl hunderTarget
  constructor
  · simp only [lowerSpine]
    rw [hsrc]
    simp only
    rw [if_pos hunderSource]
    rw [if_neg (by decide)]
    rw [estateBindRun, hwrapperRun]
    exact hknown.1
  · exact hknown.2

/-- Exact-saturation constructor dispatch in `lowerSpine`, including its
whole-value field-world telescope and concrete constructor identity. -/
theorem lowerSpine_ref_ctor_terminal_verified {ctx : Ctx} {cur : FnDef}
    (src : IxIR0.Env) (fuel : Nat) (input output : VEnv)
    (world : Owned) (f : Ixon.Address) (tag arity : Nat)
    (args : List IxIR0.Expr) (emit : Emit) (avs : List AVal)
    (state finalState : LowSt)
    (hsrc : src f = some (.ctor tag arity))
    (hargsLength : args.length = arity)
    (hargsRun :
      (lowerArgs src fuel input
        ((args.take arity).zip
          (padWorlds (List.replicate arity world) arity))).run state =
        .ok (output, emit, avs) finalState)
    (hargsSound : LowerArgsSound ctx cur input output
      (((args.take arity).zip
        (padWorlds (List.replicate arity world) arity)).map Prod.snd)
      emit avs)
    (hworldsHomogeneous :
      ((args.take arity).zip
        (padWorlds (List.replicate arity world) arity)).map Prod.snd =
          List.replicate avs.length world) :
    (lowerSpine src (Nat.succ (Nat.succ fuel)) input world (.ref f)
      args).run state =
        .ok (output.bump,
          emit ∘ emitOp (.alloc world (ctorIdOf f tag)
            (avs.map (·.toAtom output)).toArray),
          .slotA output.depth) finalState ∧
      LowerResultSound ctx cur input output.bump world
        (emit ∘ emitOp (.alloc world (ctorIdOf f tag)
          (avs.map (·.toAtom output)).toArray))
        (.slotA output.depth) := by
  have hknown := knownCall_alloc_terminal_verified
    (ctx := ctx) (cur := cur) src fuel input output world
    (ctorIdOf f tag) arity (List.replicate arity world) world args
    emit avs state finalState hargsRun hargsSound hworldsHomogeneous
    (by omega)
  constructor
  · simp only [lowerSpine]
    rw [hsrc]
    simp only
    rw [if_neg (by omega)]
    exact hknown.1
  · exact hknown.2

/-- The executable compiler equations for the first two induction cases,
paired with their semantic proofs. -/
theorem lowerE_lit_verified {ctx : Ctx} {cur : FnDef} (src : IxIR0.Env)
    (fuel : Nat) (Γ : VEnv) (world : Owned) (literal : IxIR0.Literal)
    (state : LowSt) :
    (lowerE src (Nat.succ fuel) Γ world (.lit literal)).run state =
        .ok (Γ, (_root_.id : Emit), .constA (.lit literal)) state ∧
      LowerResultSound ctx cur Γ Γ world (_root_.id : Emit)
        (.constA (.lit literal)) := by
  constructor
  · simp [lowerE]
  · exact lower_lit_sound

theorem lowerE_lit_verified_below {ctx : Ctx} {cur : FnDef}
    {limit : Nat} (src : IxIR0.Env) (fuel : Nat) (Γ : VEnv)
    (world : Owned) (literal : IxIR0.Literal) (state : LowSt) :
    (lowerE src (Nat.succ fuel) Γ world (.lit literal)).run state =
        .ok (Γ, (_root_.id : Emit), .constA (.lit literal)) state ∧
      LowerResultSoundBelow ctx cur limit Γ Γ world (_root_.id : Emit)
        (.constA (.lit literal)) := by
  constructor
  · simp [lowerE]
  · exact lower_lit_sound_below

theorem lowerE_erased_verified {ctx : Ctx} {cur : FnDef}
    (src : IxIR0.Env) (fuel : Nat) (Γ : VEnv) (world : Owned)
    (state : LowSt) :
    (lowerE src (Nat.succ fuel) Γ world .erased).run state =
        .ok (Γ, (_root_.id : Emit), .constA .erased) state ∧
      LowerResultSound ctx cur Γ Γ world (_root_.id : Emit)
        (.constA .erased) := by
  constructor
  · simp [lowerE]
  · exact lower_erased_sound

theorem lowerE_erased_verified_below {ctx : Ctx} {cur : FnDef}
    {limit : Nat} (src : IxIR0.Env) (fuel : Nat) (Γ : VEnv)
    (world : Owned) (state : LowSt) :
    (lowerE src (Nat.succ fuel) Γ world .erased).run state =
        .ok (Γ, (_root_.id : Emit), .constA .erased) state ∧
      LowerResultSoundBelow ctx cur limit Γ Γ world (_root_.id : Emit)
        (.constA .erased) := by
  constructor
  · simp [lowerE]
  · exact lower_erased_sound_below

/-- The executable final-use branch and its generic semantic move theorem. -/
theorem lowerE_var_move_verified {ctx : Ctx} {cur : FnDef}
    (src : IxIR0.Env) (fuel : Nat) (Γ : VEnv) (i abs : Nat)
    (uses : Uses) (state : LowSt)
    (hentry : Γ.entries[i]? = some (.slot abs 1 uses true)) :
    (lowerE src (Nat.succ fuel) Γ (worldOfUses uses) (.var i)).run state =
        .ok (Γ.setEntry i (.slot abs 0 uses false),
          (_root_.id : Emit), .slotA abs) state ∧
      LowerResultSound ctx cur Γ
        (Γ.setEntry i (.slot abs 0 uses false)) (worldOfUses uses)
        (_root_.id : Emit) (.slotA abs) := by
  constructor
  · have hshared : (Owned.shared != Owned.shared) = false := by decide
    have hunique : (Owned.unique != Owned.unique) = false := by decide
    cases uses <;>
      simp [lowerE, hentry, worldOfUses, hshared, hunique]
  · exact lower_var_move_sound hentry

theorem lowerE_var_move_verified_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat}
    (src : IxIR0.Env) (fuel : Nat) (Γ : VEnv) (i abs : Nat)
    (uses : Uses) (state : LowSt)
    (hentry : Γ.entries[i]? = some (.slot abs 1 uses true)) :
    (lowerE src (Nat.succ fuel) Γ (worldOfUses uses) (.var i)).run state =
        .ok (Γ.setEntry i (.slot abs 0 uses false),
          (_root_.id : Emit), .slotA abs) state ∧
      LowerResultSoundBelow ctx cur limit Γ
        (Γ.setEntry i (.slot abs 0 uses false)) (worldOfUses uses)
        (_root_.id : Emit) (.slotA abs) := by
  constructor
  · have hshared : (Owned.shared != Owned.shared) = false := by decide
    have hunique : (Owned.unique != Owned.unique) = false := by decide
    cases uses <;>
      simp [lowerE, hentry, worldOfUses, hshared, hunique]
  · exact lower_var_move_sound_below hentry

/-- The executable shared-dup branch and its exact retain proof. -/
theorem lowerE_var_many_dup_verified {ctx : Ctx} {cur : FnDef}
    (src : IxIR0.Env) (fuel : Nat) (Γ : VEnv) (i abs remaining : Nat)
    (state : LowSt)
    (hentry : Γ.entries[i]? =
      some (.slot abs (Nat.succ (Nat.succ remaining)) .many true)) :
    let Γ' := Γ.setEntry i (.slot abs (Nat.succ remaining) .many true)
    (lowerE src (Nat.succ fuel) Γ .shared (.var i)).run state =
        .ok (Γ'.bump, emitOp (.dup (.var (Γ'.rel abs))),
          .slotA Γ'.depth) state ∧
      LowerResultSound ctx cur Γ Γ'.bump .shared
        (emitOp (.dup (.var (Γ'.rel abs)))) (.slotA Γ'.depth) := by
  dsimp only
  constructor
  · have hsame : (Owned.shared != Owned.shared) = false := by decide
    have hunique : (Owned.shared == Owned.unique) = false := by decide
    simp [lowerE, hentry, worldOfUses, hsame, hunique]
  · exact lower_var_many_dup_sound hentry

theorem lowerE_var_many_dup_verified_below
    {ctx : Ctx} {cur : FnDef} {limit : Nat}
    (src : IxIR0.Env) (fuel : Nat) (Γ : VEnv)
    (i abs remaining : Nat) (state : LowSt)
    (hentry : Γ.entries[i]? =
      some (.slot abs (Nat.succ (Nat.succ remaining)) .many true)) :
    let Γ' := Γ.setEntry i (.slot abs (Nat.succ remaining) .many true)
    (lowerE src (Nat.succ fuel) Γ .shared (.var i)).run state =
        .ok (Γ'.bump, emitOp (.dup (.var (Γ'.rel abs))),
          .slotA Γ'.depth) state ∧
      LowerResultSoundBelow ctx cur limit Γ Γ'.bump .shared
        (emitOp (.dup (.var (Γ'.rel abs)))) (.slotA Γ'.depth) := by
  dsimp only
  constructor
  · have hsame : (Owned.shared != Owned.shared) = false := by decide
    have hunique : (Owned.shared == Owned.unique) = false := by decide
    simp [lowerE, hentry, worldOfUses, hsame, hunique]
  · exact lower_var_many_dup_sound_below hentry

/-- Executable lowering and semantic ownership agree for the first
nontrivial `let`/variable derivation. -/
theorem lowerE_let_lit_var_verified {ctx : Ctx} {cur : FnDef}
    (src : IxIR0.Env) (fuel : Nat) (Γ : VEnv) (literal : IxIR0.Literal)
    (state : LowSt) :
    (lowerE src (Nat.succ (Nat.succ fuel)) Γ .shared
      (.letE .many (.lit literal) (.var 0))).run state =
        .ok (Γ.bump, emitOp (.pure (.lit literal)), .slotA Γ.depth) state ∧
      LowerResultSound ctx cur Γ Γ.bump .shared
        (emitOp (.pure (.lit literal))) (.slotA Γ.depth) := by
  constructor
  · have hsame : (Owned.shared != Owned.shared) = false := by decide
    simp [lowerE, countUses, worldOfUses, VEnv.bump, VEnv.pop,
      VEnv.setEntry, Function.comp_def, hsame]
  · exact lower_let_lit_var_sound

/-- A non-head linear entry exercises root extraction and permutation: the
preceding shared source root remains in the environment while the selected
unique root becomes the expression result. -/
theorem fixture_nonhead_unique_move_sound {ctx : Ctx} {cur : FnDef} :
    let Γ : VEnv :=
      ⟨[.slot 1 1 .many true, .slot 0 1 .linear true], 2⟩
    LowerResultSound ctx cur Γ
      (Γ.setEntry 1 (.slot 0 0 .linear false)) .unique
      (_root_.id : Emit) (.slotA 0) := by
  dsimp only
  apply lower_var_move_sound
  rfl

/-- Two argument expressions each push a runtime slot. The cons proof keeps
the first absolute slot protected while the second push changes its relative
index, then realizes both descriptors in source order. -/
theorem fixture_two_pushed_args_sound {ctx : Ctx} {cur : FnDef}
    {Γ : VEnv} {first second : IxIR0.Literal} :
    LowerArgsSound ctx cur Γ Γ.bump.bump [.shared, .shared]
      (emitOp (.pure (.lit first)) ∘ emitOp (.pure (.lit second)))
      [.slotA Γ.depth, .slotA Γ.bump.depth] := by
  exact (lower_let_lit_var_sound (ctx := ctx) (cur := cur)
    (Γ := Γ) (literal := first)).consArgs
      ((lower_let_lit_var_sound (ctx := ctx) (cur := cur)
        (Γ := Γ.bump) (literal := second)).consArgs
        (lowerArgs_nil_sound (ctx := ctx) (cur := cur) (Γ := Γ.bump.bump)))

/-- The two protected argument slots become fields of one shared
constructor, leaving exactly the fresh node as the expression result. -/
theorem fixture_two_pushed_alloc_sound {ctx : Ctx} {cur : FnDef}
    {Γ : VEnv} {first second : IxIR0.Literal} {cid : CtorId} :
    LowerResultSound ctx cur Γ Γ.bump.bump.bump .shared
      ((emitOp (.pure (.lit first)) ∘ emitOp (.pure (.lit second))) ∘
        emitOp (.alloc .shared cid
          (([AVal.slotA Γ.depth, AVal.slotA Γ.bump.depth] : List AVal).map
            (·.toAtom Γ.bump.bump)).toArray))
      (.slotA Γ.bump.bump.depth) := by
  exact (fixture_two_pushed_args_sound (ctx := ctx) (cur := cur)
    (Γ := Γ) (first := first) (second := second)).alloc_owned

/-- The same protected two-argument prefix becomes the captures of a fresh
shared pap when the target declaration still expects more arguments. -/
theorem fixture_two_pushed_papp_sound {ctx : Ctx} {cur : FnDef}
    {Γ : VEnv} {first second : IxIR0.Literal}
    {f : Ixon.Address} {d : Decl}
    (hdecl : ctx.decls f = some d)
    (hunder : 2 < declArity d) :
    LowerResultSound ctx cur Γ Γ.bump.bump.bump .shared
      ((emitOp (.pure (.lit first)) ∘ emitOp (.pure (.lit second))) ∘
        emitOp (.papp f
          (([AVal.slotA Γ.depth, AVal.slotA Γ.bump.depth] : List AVal).map
            (·.toAtom Γ.bump.bump)).toArray))
      (.slotA Γ.bump.bump.depth) := by
  have hargs : LowerArgsSound ctx cur Γ Γ.bump.bump
      (List.replicate
        ([AVal.slotA Γ.depth, AVal.slotA Γ.bump.depth] : List AVal).length
        .shared)
      (emitOp (.pure (.lit first)) ∘ emitOp (.pure (.lit second)))
      [AVal.slotA Γ.depth, AVal.slotA Γ.bump.depth] := by
    simpa using (fixture_two_pushed_args_sound (ctx := ctx) (cur := cur)
      (Γ := Γ) (first := first) (second := second))
  exact hargs.papp_owned hdecl (by simpa using hunder)

/-- A scalar extern consumes the same two shared argument owners on every
successful run and returns an ownership-inert scalar at either result world. -/
theorem fixture_two_pushed_extern_sound {ctx : Ctx} {cur : FnDef}
    {Γ : VEnv} {world : Owned} {first second : IxIR0.Literal}
    {f : Ixon.Address} :
    LowerResultSound ctx cur Γ Γ.bump.bump.bump world
      ((emitOp (.pure (.lit first)) ∘ emitOp (.pure (.lit second))) ∘
        emitOp (.extern f
          (([AVal.slotA Γ.depth, AVal.slotA Γ.bump.depth] : List AVal).map
            (·.toAtom Γ.bump.bump)).toArray))
      (.slotA Γ.bump.bump.depth) := by
  have hargs : LowerArgsSound ctx cur Γ Γ.bump.bump
      (List.replicate
        ([AVal.slotA Γ.depth, AVal.slotA Γ.bump.depth] : List AVal).length
        .shared)
      (emitOp (.pure (.lit first)) ∘ emitOp (.pure (.lit second)))
      [AVal.slotA Γ.depth, AVal.slotA Γ.bump.depth] := by
    simpa using (fixture_two_pushed_args_sound (ctx := ctx) (cur := cur)
      (Γ := Γ) (first := first) (second := second))
  exact hargs.extern_owned

/-- The direct-call dual: an abstract two-shared-argument contract consumes
both protected roots and supplies the declaration's result root. -/
theorem fixture_two_pushed_call_sound {ctx : Ctx} {cur d : FnDef}
    {Γ : VEnv} {first second : IxIR0.Literal} {f : Ixon.Address}
    (hdecl : ctx.decls f = some (.fn d))
    (hcontract : FnOwnershipContract ctx d [.shared, .shared]) :
    LowerResultSound ctx cur Γ Γ.bump.bump.bump d.result
      ((emitOp (.pure (.lit first)) ∘ emitOp (.pure (.lit second))) ∘
        emitOp (.call f
          (([AVal.slotA Γ.depth, AVal.slotA Γ.bump.depth] : List AVal).map
            (·.toAtom Γ.bump.bump)).toArray))
      (.slotA Γ.bump.bump.depth) := by
  exact (fixture_two_pushed_args_sound (ctx := ctx) (cur := cur)
    (Γ := Γ) (first := first) (second := second)).call_owned
      hdecl hcontract

/-- A previously produced shared function survives both argument pushes;
the final `apply` consumes that function root and both argument roots and
returns one fresh shared result root. -/
theorem fixture_two_pushed_apply_sound {ctx : Ctx} {cur : FnDef}
    {start Γ : VEnv} {emitFunction : Emit} {function : AVal}
    {first second : IxIR0.Literal}
    (hfunction : LowerResultSound ctx cur start Γ .shared
      emitFunction function)
    (hcontract : ApplyOwnershipContract ctx) :
    LowerResultSound ctx cur start Γ.bump.bump.bump .shared
      ((emitFunction ∘
        (emitOp (.pure (.lit first)) ∘ emitOp (.pure (.lit second)))) ∘
        emitOp (.apply (function.toAtom Γ.bump.bump)
          (([AVal.slotA Γ.depth, AVal.slotA Γ.bump.depth] : List AVal).map
            (·.toAtom Γ.bump.bump)).toArray))
      (.slotA Γ.bump.bump.depth) := by
  exact hfunction.applyArgs
    (fixture_two_pushed_args_sound (ctx := ctx) (cur := cur)
      (Γ := Γ) (first := first) (second := second))
    hcontract

/-- `releaseAll` drops both slot-backed arguments in order. Each drop pushes
an inert slot, so both absolute arguments resolve at relative index one when
their respective operation is emitted. -/
theorem fixture_two_pushed_releaseAll_eq {Γ : VEnv} :
    releaseAll Γ.bump.bump
      [AVal.slotA Γ.depth, AVal.slotA Γ.bump.depth] =
      (Γ.bump.bump.bump.bump,
        emitOp (.drop (.var (Γ.bump.bump.rel Γ.depth))) ∘
          emitOp (.drop (.var (Γ.bump.bump.bump.rel Γ.bump.depth)))) := by
  rfl

/-- Erased application evaluates the same two pushing arguments, consumes
both resulting shared owners via `releaseAll`, and leaves only the erased
scalar result. -/
theorem fixture_two_pushed_erased_release_sound
    {ctx : Ctx} {cur : FnDef} {Γ : VEnv}
    {world : Owned} {first second : IxIR0.Literal} :
    LowerResultSound ctx cur Γ Γ.bump.bump.bump.bump world
      (((_root_.id : Emit) ∘
        (emitOp (.pure (.lit first)) ∘ emitOp (.pure (.lit second)))) ∘
        (emitOp (.drop (.var (Γ.bump.bump.rel Γ.depth))) ∘
          emitOp (.drop (.var (Γ.bump.bump.bump.rel Γ.bump.depth)))))
      (.constA .erased) := by
  have hargs : LowerArgsSound ctx cur Γ Γ.bump.bump
      (List.replicate
        ([AVal.slotA Γ.depth, AVal.slotA Γ.bump.depth] : List AVal).length
        .shared)
      (emitOp (.pure (.lit first)) ∘ emitOp (.pure (.lit second)))
      [AVal.slotA Γ.depth, AVal.slotA Γ.bump.depth] := by
    simpa using (fixture_two_pushed_args_sound (ctx := ctx) (cur := cur)
      (Γ := Γ) (first := first) (second := second))
  have hsound := (lower_erased_sound (ctx := ctx) (cur := cur)
    (Γ := Γ) (world := .shared)).discardArgs
      (resultWorld := world) hargs
  rw [fixture_two_pushed_releaseAll_eq] at hsound
  exact hsound

/-- Closed proof fixture for the exact code emitted by
`let many x := literal; x`. -/
theorem fixture_closed_let_lit_owned {ctx : Ctx} {cur : FnDef}
    {literal : IxIR0.Literal} :
    CodeOwns ctx cur (OwnsVEnv ⟨[], 0⟩ [])
      (fun store value =>
        RootOwnership store [⟨Owned.shared, value⟩])
      (.letOp (.pure (.lit literal)) (.ret (.var 0))) := by
  let Γ₀ : VEnv := ⟨[], 0⟩
  have h : CodeOwns ctx cur (OwnsVEnv Γ₀ [])
      (fun store value =>
        RootOwnership store (⟨Owned.shared, value⟩ :: []))
      ((emitOp (.pure (.lit literal)))
        (.ret ((AVal.slotA Γ₀.depth).toAtom Γ₀.bump))) :=
    LowerResultSound.close
      (lower_let_lit_var_sound (ctx := ctx) (cur := cur)
        (Γ := Γ₀) (literal := literal))
      EntriesReleased.nil []
  change CodeOwns ctx cur (OwnsVEnv Γ₀ [])
    (fun store value =>
      RootOwnership store (⟨Owned.shared, value⟩ :: []))
    ((emitOp (.pure (.lit literal)))
      (.ret ((AVal.slotA Γ₀.depth).toAtom Γ₀.bump)))
  exact h

/-- Generated releases handle several dead parameters in canonical
inner-to-outer order, mixing shared `drop` with affine `dropU`. -/
theorem parameterDrops_mixed_generated_verified {ctx : Ctx} {cur : FnDef}
    (state : LowSt) :
    ∃ output emit,
      (releaseSlots
        ⟨parameterEntries 0 [.many, .affine, .many] (fun _ => 0), 3⟩
        (parameterDrops 0 [.many, .affine, .many] (fun _ => 0))).run state =
          .ok (output, emit) state ∧
      ReleaseSlotsSound ctx cur
        ⟨parameterEntries 0 [.many, .affine, .many] (fun _ => 0), 3⟩
        output emit := by
  exact parameterDrops_verified (ctx := ctx) (cur := cur)
    0 [.many, .affine, .many] (fun _ => 0) state
      (by simp [ParameterDropsAdmissible])

/-- A declaration-level generated-release fixture: three unused parameters
mix shared and affine ownership, while the scalar body leaves every entry
released and therefore yields a callable contract. -/
theorem lowerDecl_all_dead_mixed_generated_verified {ctx : Ctx}
    (src : IxIR0.Env) (fuel : Nat) (address : Ixon.Address)
    (literal : IxIR0.Literal) (state : LowSt) :
    let sourceBody : IxIR0.Expr :=
      .lam .many (.lam .affine (.lam .many (.lit literal)))
    ∃ finalState d,
      (lowerDecl src (Nat.succ (Nat.succ fuel))
        (address, .defn .shared sourceBody)).run state =
          .ok (some (address, .fn d)) finalState ∧
      FnOwnershipContract ctx d [.shared, .unique, .shared] := by
  dsimp only
  apply lowerDecl_defn_generated_verified (ctx := ctx)
    src (Nat.succ fuel) address .shared
      (.lam .many (.lam .affine (.lam .many (.lit literal)))) state
  · simp [ParameterDropsAdmissible, lamUses, stripLams, countUses]
  · intro middle releaseEmit hrelease
    simp [releaseSlots, parameterEntries, parameterDrops, lamUses,
      stripLams, lamArity, countUses, VEnv.rel, VEnv.setEntry,
      VEnv.bump, Function.comp_def] at hrelease
    obtain ⟨hmiddle, hemit⟩ := hrelease
    have hreleased : EntriesReleased middle.entries := by
      rw [← hmiddle]
      exact EntriesReleased.slot
        (EntriesReleased.slot (EntriesReleased.slot EntriesReleased.nil))
    refine ⟨middle, (_root_.id : Emit), .constA (.lit literal), state,
      ?_, ?_, ?_⟩
    · exact (lowerE_lit_verified (ctx := ctx)
        (cur := ⟨3, .shared,
          (releaseEmit ∘ (_root_.id : Emit)) (.ret (.lit literal))⟩)
        src fuel middle .shared literal state).1
    · exact (lowerE_lit_verified (ctx := ctx)
        (cur := ⟨3, .shared,
          (releaseEmit ∘ (_root_.id : Emit)) (.ret (.lit literal))⟩)
        src fuel middle .shared literal state).2
    · exact hreleased

/-- `lowerFnBody` and the contract constructor agree on the smallest real
function body: a single parameter used exactly once. This covers both shared
and unique parameter worlds through `worldOfUses`. -/
theorem lowerFnBody_single_var_verified {ctx : Ctx}
    (src : IxIR0.Env) (fuel : Nat) (uses : Uses) (state : LowSt) :
    let input : VEnv := ⟨[.slot 0 1 uses true], 1⟩
    let d : FnDef :=
      ⟨1, worldOfUses uses, .ret (.var 0)⟩
    (lowerFnBody src (Nat.succ (Nat.succ fuel)) input []
      (worldOfUses uses) (.var 0)).run state =
        .ok d.body state ∧
      FnOwnershipContract ctx d [worldOfUses uses] := by
  dsimp only
  constructor
  · have hsame : (worldOfUses uses != worldOfUses uses) = false := by
      cases uses <;> decide
    simp [lowerFnBody, releaseSlots, lowerE, hsame, VEnv.setEntry,
      VEnv.rel, AVal.toAtom]
  · let input : VEnv := ⟨[.slot 0 1 uses true], 1⟩
    let output := input.setEntry 0 (.slot 0 0 uses false)
    let d : FnDef := ⟨1, worldOfUses uses, .ret (.var 0)⟩
    have hsound : LowerResultSound ctx d input output
        (worldOfUses uses) (_root_.id : Emit) (.slotA 0) := by
      apply lower_var_move_sound
      rfl
    apply hsound.fnOwnershipContract (FnEntryRealizes.singleton uses 1)
    · rfl
    · exact EntriesReleased.slot EntriesReleased.nil
    · rfl

/-- A real two-parameter function-body run with one dead shared parameter.
The entry release emits `drop`, records that owner as released, and the live
inner parameter is then moved to the result. -/
theorem lowerFnBody_dead_many_verified {ctx : Ctx}
    (src : IxIR0.Env) (fuel : Nat) (state : LowSt) :
    let input : VEnv :=
      ⟨[.slot 1 1 .many true, .slot 0 0 .many true], 2⟩
    let d : FnDef :=
      ⟨2, .shared, .letOp (.drop (.var 1)) (.ret (.var 1))⟩
    (lowerFnBody src (Nat.succ (Nat.succ fuel)) input
      [⟨1, 0, .many⟩] .shared (.var 0)).run state =
        .ok d.body state ∧
      FnOwnershipContract ctx d [.shared, .shared] := by
  dsimp only
  let remaining : Nat → Nat := fun i => if i = 0 then 1 else 0
  let input : VEnv :=
    ⟨parameterEntries 0 [.many, .many] remaining, 2⟩
  let middle :=
    (input.setEntry 1 (.slot 0 0 .many false)).bump
  let output := middle.setEntry 0 (.slot 1 0 .many false)
  let releaseEmit : Emit :=
    emitOp (.drop (.var (input.rel 0))) ∘ (_root_.id : Emit)
  let d : FnDef :=
    ⟨2, .shared, .letOp (.drop (.var 1)) (.ret (.var 1))⟩
  have hplan : ReleasePlan input [⟨1, 0, .many⟩] middle releaseEmit := by
    apply ReleasePlan.many
    · rfl
    · exact ReleasePlan.nil
  have hvar := lowerE_var_move_verified (ctx := ctx) (cur := d)
    src fuel middle 0 1 .many state (by rfl)
  have hfn := lowerFnBody_verified (ctx := ctx) (cur := d)
    src (Nat.succ fuel) input middle output [⟨1, 0, .many⟩]
    .shared (.var 0) releaseEmit (_root_.id : Emit) (.slotA 1)
    state state hplan hvar.1 hvar.2
  constructor
  · simpa [input, middle, output, releaseEmit, d, VEnv.rel,
      VEnv.setEntry, VEnv.bump, parameterEntries, remaining,
      AVal.toAtom, emitOp, Function.comp_def] using hfn.1
  · have hentry : FnEntryRealizes input [.shared, .shared] := by
      exact FnEntryRealizes.parameterEntries [.many, .many] remaining
    have hreleased : EntriesReleased output.entries := by
      exact EntriesReleased.slot (EntriesReleased.slot EntriesReleased.nil)
    apply hfn.2.fnOwnershipContract hentry rfl hreleased
    rfl

/-- The corresponding real `lowerDecl` branch: a two-argument definition
whose outer shared parameter is dead lowers to the verified drop/return
function and immediately receives its callable contract. -/
theorem lowerDecl_dead_many_verified {ctx : Ctx}
    (src : IxIR0.Env) (fuel : Nat) (address : Ixon.Address)
    (state : LowSt) :
    let sourceBody : IxIR0.Expr :=
      .lam .many (.lam .many (.var 0))
    let d : FnDef :=
      ⟨2, .shared, .letOp (.drop (.var 1)) (.ret (.var 1))⟩
    (lowerDecl src (Nat.succ (Nat.succ fuel))
      (address, .defn .shared sourceBody)).run state =
        .ok (some (address, .fn d)) state ∧
      FnOwnershipContract ctx d [.shared, .shared] := by
  dsimp only
  let sourceBody : IxIR0.Expr := .lam .many (.lam .many (.var 0))
  let remaining : Nat → Nat := fun i => countUses i (.var 0)
  let input : VEnv :=
    ⟨parameterEntries 0 [.many, .many] remaining, 2⟩
  let middle := (input.setEntry 1 (.slot 0 0 .many false)).bump
  let output := middle.setEntry 0 (.slot 1 0 .many false)
  let releaseEmit : Emit :=
    emitOp (.drop (.var (input.rel 0))) ∘ (_root_.id : Emit)
  let d : FnDef :=
    ⟨2, .shared, .letOp (.drop (.var 1)) (.ret (.var 1))⟩
  have hplan : ReleasePlan input [⟨1, 0, .many⟩] middle releaseEmit := by
    apply ReleasePlan.many
    · rfl
    · exact ReleasePlan.nil
  have hvar := lowerE_var_move_verified (ctx := ctx) (cur := d)
    src fuel middle 0 1 .many state (by rfl)
  have hreleased : EntriesReleased output.entries :=
    EntriesReleased.slot (EntriesReleased.slot EntriesReleased.nil)
  have hdecl := lowerDecl_defn_verified (ctx := ctx)
    src (Nat.succ fuel) address .shared sourceBody middle output
    releaseEmit (_root_.id : Emit) (.slotA 1) state state d
    (by simpa [sourceBody, input, remaining, parameterDrops, lamUses,
      stripLams, lamArity, countUses] using hplan)
    (by simpa [sourceBody, output, stripLams, worldOfUses] using hvar.1)
    (by simp [d, sourceBody, releaseEmit, input, output, middle,
      remaining, parameterEntries, VEnv.rel, VEnv.setEntry, VEnv.bump,
      lamArity, AVal.toAtom, emitOp, Function.comp_def])
    hvar.2 hreleased
  simpa [sourceBody, d, lamUses, worldOfUses] using hdecl

private def NullaryRecursorEntryValid
    (env : List RVal) (fields : Array RVal) : Prop :=
  ∃ major, env = [major] ∧ fields = #[]

private def nullaryRecursorEntryRoots
    (env : List RVal) (_ : Array RVal) : List Root :=
  match env with
  | major :: _ => [⟨.shared, major⟩]
  | [] => []

/-- Entry shape for the first nontrivial recursor-prefix fixture. The
function receives one pre-major parameter and the major; dispatch exposes one
borrowed constructor field. -/
private def OneFieldDeadParamEntryValid
    (env : List RVal) (fields : Array RVal) : Prop :=
  ∃ pre major field, env = [major, pre] ∧ fields = #[field]

/-- Function-argument root order for `OneFieldDeadParamEntryValid`. This
matches the source argument vector (`pre`, then `major`), independently of
the reversed runtime environment. -/
private def oneFieldDeadParamEntryRoots
    (env : List RVal) (_ : Array RVal) : List Root :=
  match env with
  | major :: pre :: _ => [⟨.shared, pre⟩, ⟨.shared, major⟩]
  | _ => []

/-- A complete non-nullary recursor prefix: retain one borrowed field, drop
the major, drop one dead pre-major parameter, then move the retained field to
the result. This isolates all three ownership transitions generated by the
corresponding `lowerRecursor` fold. -/
theorem lowerRecursor_one_field_dead_param_alt_contract
    {ctx : Ctx} {cur : FnDef} (hresult : cur.result = .shared) :
    AltOwnershipContract ctx cur
      (.mk 0 1
        (.letOp (.dup (.var 0))
          (.letOp (.drop (.var 2))
            (.letOp (.drop (.var 4)) (.ret (.var 2))))))
      .shared OneFieldDeadParamEntryValid
        oneFieldDeadParamEntryRoots := by
  let input : VEnv :=
    ⟨[.slot 3 1 .many true, .slot 0 0 .many false, .recSelf 2], 6⟩
  let output := input.setEntry 0 (.slot 3 0 .many false)
  have hbody : LowerResultSound ctx cur input output cur.result
      (_root_.id : Emit) (.slotA 3) := by
    rw [hresult]
    apply lower_var_move_sound
    rfl
  have hprefix : ∀ {env : List RVal} {fields : Array RVal}
      {rest : List Root},
      fields.size = 1 → OneFieldDeadParamEntryValid env fields →
        EmitSound ctx cur
          (emitOp (.dup (.var 0)) ∘
            emitOp (.drop (.var 2)) ∘
            emitOp (.drop (.var 4)))
          (OwnsAltEntry .shared oneFieldDeadParamEntryRoots env fields rest)
          (OwnsVEnv input rest) := by
    intro env fields rest _ hvalid
    obtain ⟨pre, major, field, rfl, rfl⟩ := hvalid
    intro post code hcode
    let entryFrame : List RVal → Prop :=
      fun oldEnv => oldEnv = [field, major, pre]
    have hafterDup : CodeOwns ctx cur
        (OwnsPushedRoot entryFrame .shared
          ([⟨.shared, pre⟩, ⟨.shared, major⟩] ++ rest))
        post
        ((emitOp (.drop (.var 2)) ∘ emitOp (.drop (.var 4))) code) := by
      intro nextFuel nextStore nextEnv resultStore resultValue hpushed hrun
      obtain ⟨ownedField, oldEnv, rfl, hold, hown⟩ := hpushed
      subst oldEnv
      let majorFrame : List RVal → Prop :=
        fun current => current = [ownedField, field, major, pre]
      have hafterMajor : CodeOwns ctx cur
          (OwnsAfterPush majorFrame
            (⟨.shared, ownedField⟩ :: ⟨.shared, pre⟩ :: rest))
          post (emitOp (.drop (.var 4)) code) := by
        intro majorFuel majorStore majorEnv finalStore finalValue
          hpushedMajor hrunMajor
        obtain ⟨majorResult, oldEnv, rfl, holdMajor, hownMajor⟩ :=
          hpushedMajor
        subst oldEnv
        let paramFrame : List RVal → Prop :=
          fun current =>
            current = [majorResult, ownedField, field, major, pre]
        have hafterParam : CodeOwns ctx cur
            (OwnsAfterPush paramFrame ([⟨.shared, ownedField⟩] ++ rest))
            post code := by
          intro paramFuel paramStore paramEnv finalStore finalValue
            hpushedParam hrunParam
          obtain ⟨paramResult, oldEnv, rfl, holdParam, hownParam⟩ :=
            hpushedParam
          subst oldEnv
          have hrealize : VEnvRealizes input
              [paramResult, majorResult, ownedField, field, major, pre]
              [⟨.shared, ownedField⟩] := by
            refine ⟨by simp [input], ?_⟩
            apply EntriesRealize.held
            · simp [input]
            · simp [input, VEnv.rel]
            · apply EntriesRealize.released
              · simp [input]
              · exact EntriesRealize.recSelf EntriesRealize.nil
          apply hcode
          · exact ⟨[⟨.shared, ownedField⟩], hrealize,
              by simpa using hownParam⟩
          · exact hrunParam
        apply (emit_drop_value_owned (ctx := ctx) (cur := cur)
          (target := .var 4) (value := pre) (frame := paramFrame)
          (rest := ⟨.shared, ownedField⟩ :: rest))
          post code hafterParam
        · refine ⟨rfl, rfl, ?_⟩
          exact hownMajor.perm
            (perm_extract_root ⟨.shared, pre⟩
              [⟨.shared, ownedField⟩] [] rest)
        · exact hrunMajor
      apply (emit_drop_value_owned (ctx := ctx) (cur := cur)
        (target := .var 2) (value := major) (frame := majorFrame)
        (rest := ⟨.shared, ownedField⟩ :: ⟨.shared, pre⟩ :: rest))
        post (emitOp (.drop (.var 4)) code) hafterMajor
      · refine ⟨rfl, rfl, ?_⟩
        exact hown.perm
          (perm_extract_root ⟨.shared, major⟩
            [⟨.shared, ownedField⟩, ⟨.shared, pre⟩] [] rest)
      · simpa [Function.comp_def] using hrun
    intro startFuel startStore branchEnv endStore endValue hentry hrun
    have hpre :
        entryFrame branchEnv ∧
          resolveAtom branchEnv (.var 0) = .ok field ∧
          HasWorld startStore .shared field ∧
          RootOwnership startStore
            ([⟨.shared, pre⟩, ⟨.shared, major⟩] ++ rest) := by
      obtain ⟨henv, hown, hborrow⟩ := hentry
      have hbranch : branchEnv = [field, major, pre] := by
        simpa using henv
      refine ⟨hbranch, ?_, hborrow field (by simp), ?_⟩
      · rw [hbranch]
        rfl
      · simpa [oneFieldDeadParamEntryRoots] using hown
    exact (emit_retain_borrowed (ctx := ctx) (cur := cur)
      (atom := .var 0) (value := field) (frame := entryFrame)
      (rest := [⟨.shared, pre⟩, ⟨.shared, major⟩] ++ rest))
      post ((emitOp (.drop (.var 2)) ∘ emitOp (.drop (.var 4))) code)
      hafterDup (fuel := startFuel) (store := startStore)
      (env := branchEnv) (store' := endStore) (value := endValue) hpre
      (by simpa [Function.comp_def] using hrun)
  have hcontract := hbody.altOwnershipContractWithPrefix
    (fieldWorld := .shared)
    (entryValid := OneFieldDeadParamEntryValid)
    (entryRoots := oneFieldDeadParamEntryRoots)
    (entryEmit := emitOp (.dup (.var 0)) ∘
      emitOp (.drop (.var 2)) ∘ emitOp (.drop (.var 4)))
    (tag := 0) (fieldCount := 1) hprefix
    (EntriesReleased.slot
      (EntriesReleased.slot
        (EntriesReleased.recSelf EntriesReleased.nil)))
  simpa [input, output, VEnv.setEntry, VEnv.rel, AVal.toAtom,
    emitOp, Function.comp_def] using hcontract

/-- Exact contract for the first concrete `lowerRecursor` prefix shape:
a nullary rule with no pre-major parameters. The alternative owns the shared
major, exposes no fields, drops the major, and then returns a scalar literal. -/
theorem lowerRecursor_nullary_lit_alt_contract {ctx : Ctx} {cur : FnDef}
    (literal : IxIR0.Literal) :
    AltOwnershipContract ctx cur
      (.mk 0 0 (.letOp (.drop (.var 0)) (.ret (.lit literal))))
      .shared NullaryRecursorEntryValid nullaryRecursorEntryRoots := by
  let input : VEnv := ⟨[.recSelf 1], 2⟩
  have hbody : LowerResultSound ctx cur input input cur.result
      (_root_.id : Emit) (.constA (.lit literal)) := lower_lit_sound
  have hprefix : ∀ {env : List RVal} {fields : Array RVal}
      {rest : List Root},
      fields.size = 0 → NullaryRecursorEntryValid env fields →
        EmitSound ctx cur (emitOp (.drop (.var 0)))
          (OwnsAltEntry .shared nullaryRecursorEntryRoots env fields rest)
          (OwnsVEnv input rest) := by
    intro env fields rest hsize hvalid
    obtain ⟨major, rfl, rfl⟩ := hvalid
    intro post code hcode
    intro fuel store branchEnv store' value hpre hrun
    obtain ⟨henv, hown, _⟩ := hpre
    have hbranch : branchEnv = [major] := by simpa using henv
    subst branchEnv
    let frame : List RVal → Prop := fun oldEnv => oldEnv = [major]
    have hnext : CodeOwns ctx cur (OwnsAfterPush frame rest) post code := by
      intro nextFuel nextStore nextEnv resultStore resultValue hpushed
        hcodeRun
      obtain ⟨pushed, oldEnv, rfl, hold, hownRest⟩ := hpushed
      subst oldEnv
      apply hcode
      · have hrealize : VEnvRealizes input (pushed :: [major]) [] := by
          exact ⟨by simp [input], EntriesRealize.recSelf EntriesRealize.nil⟩
        refine ⟨[], hrealize, ?_⟩
        · simpa using hownRest
      · exact hcodeRun
    apply emit_drop_value_owned (target := .var 0) (value := major)
      (frame := frame) (rest := rest) post code hnext
    · exact ⟨rfl, rfl, by simpa [nullaryRecursorEntryRoots] using hown⟩
    · exact hrun
  have hcontract := hbody.altOwnershipContractWithPrefix
    (fieldWorld := .shared)
    (entryValid := NullaryRecursorEntryValid)
    (entryRoots := nullaryRecursorEntryRoots)
    (entryEmit := emitOp (.drop (.var 0))) (tag := 0) (fieldCount := 0)
    hprefix (EntriesReleased.recSelf EntriesReleased.nil)
  simpa [input, AVal.toAtom, emitOp, Function.comp_def] using hcontract

/-- The executable `lowerRecursor` equation paired with the contract of its
generated nullary alternative. -/
theorem lowerRecursor_nullary_lit_verified {ctx : Ctx}
    (src : IxIR0.Env) (fuel : Nat) (literal : IxIR0.Literal)
    (state : LowSt) :
    let alt : Alt :=
      .mk 0 0 (.letOp (.drop (.var 0)) (.ret (.lit literal)))
    let d : FnDef := ⟨1, .shared, .case (.var 0) false #[alt]⟩
    (lowerRecursor src (Nat.succ fuel) 0 false
      #[⟨0, .lit literal⟩]).run state = .ok d state ∧
      AltOwnershipContract ctx d alt .shared
        NullaryRecursorEntryValid nullaryRecursorEntryRoots := by
  dsimp only
  constructor
  · simp [lowerRecursor, lowerRecursorRule, recursorFieldRetains,
      applyRecursorFieldRetains, releaseSlots, parameterEntries,
      parameterDrops, lowerE, AVal.toAtom, emitOp, VEnv.rel]
  · exact lowerRecursor_nullary_lit_alt_contract literal

/-- The non-nullary prefix contract is paired with the real recursor fold.
The generated code retains field zero, drops the major at relative index two,
drops the dead pre-major parameter at index four, and returns the retained
field at index two. -/
theorem lowerRecursor_one_field_dead_param_verified {ctx : Ctx}
    (src : IxIR0.Env) (fuel : Nat) (state : LowSt) :
    let alt : Alt :=
      .mk 0 1
        (.letOp (.dup (.var 0))
          (.letOp (.drop (.var 2))
            (.letOp (.drop (.var 4)) (.ret (.var 2)))))
    let d : FnDef := ⟨2, .shared, .case (.var 0) false #[alt]⟩
    (lowerRecursor src (Nat.succ fuel) 1 false
      #[⟨1, .var 0⟩]).run state = .ok d state ∧
      AltOwnershipContract ctx d alt .shared
        OneFieldDeadParamEntryValid oneFieldDeadParamEntryRoots := by
  dsimp only
  constructor
  · have hsame : (Owned.shared != Owned.shared) = false := by decide
    simp [lowerRecursor, lowerRecursorRule, recursorFieldRetains,
      applyRecursorFieldRetains, releaseSlots, parameterEntries,
      parameterDrops, SlotDrop.offsetEntry, lowerE, countUses, worldOfUses,
      hsame, VEnv.rel, VEnv.setEntry, VEnv.bump, AVal.toAtom, emitOp,
      Function.comp_def]
  · exact lowerRecursor_one_field_dead_param_alt_contract rfl

/-- Canonical recursor parameter cleanup with more than one release. The
innermost and outermost pre-major parameters are dead while the middle one is
returned, so the shared drops occur at changing relative indices two and
five after the major has first been dropped. -/
theorem lowerRecursor_three_params_release_order_verified
    (src : IxIR0.Env) (fuel : Nat) (state : LowSt) :
    let alt : Alt :=
      .mk 0 0
        (.letOp (.drop (.var 0))
          (.letOp (.drop (.var 2))
            (.letOp (.drop (.var 5)) (.ret (.var 5)))))
    let d : FnDef := ⟨4, .shared, .case (.var 0) false #[alt]⟩
    (lowerRecursor src (Nat.succ fuel) 3 false
      #[⟨0, .var 1⟩]).run state = .ok d state := by
  dsimp only
  have hsame : (Owned.shared != Owned.shared) = false := by decide
  simp [lowerRecursor, lowerRecursorRule, recursorFieldRetains,
    applyRecursorFieldRetains,
    releaseSlots, parameterEntries, parameterDrops, SlotDrop.offsetEntry,
    lowerE, countUses, worldOfUses, hsame, VEnv.rel, VEnv.setEntry,
    VEnv.bump, AVal.toAtom, emitOp, Function.comp_def]

/-- A unary Nat alternative whose result is a scalar exercises the complete
alternative constructor. The predecessor is exposed as a borrow, the entry
layout records its physical slot, and the branch itself owns no input roots. -/
theorem fixture_nat_succ_alt_contract {ctx : Ctx} {cur : FnDef}
    (n : Nat) (literal : IxIR0.Literal) :
    AltOwnershipContract ctx cur
      (.mk 1 1 (.ret (.lit literal))) .shared
      (fun env fields =>
        env = [] ∧ fields = #[RVal.lit (.nat n)])
      (fun _ _ => []) := by
  let input : VEnv := ⟨[], 1⟩
  have hentry : AltEntryRealizes input 1
      (fun env fields =>
        env = [] ∧ fields = #[RVal.lit (.nat n)])
      (fun _ _ => []) := by
    intro env fields hsize hvalid
    obtain ⟨rfl, rfl⟩ := hvalid
    exact ⟨[], ⟨rfl, EntriesRealize.nil⟩, List.Perm.refl []⟩
  have hsound : LowerResultSound ctx cur input input cur.result
      (_root_.id : Emit) (.constA (.lit literal)) :=
    lower_lit_sound
  simpa [AVal.toAtom] using hsound.altOwnershipContract
    (fieldWorld := .shared) (tag := 1) hentry EntriesReleased.nil

/-- The alternative fixture plugs into peeled-successor dispatch and yields
the exact result root while starting from the empty store/root set. -/
theorem fixture_nat_succ_alt_dispatch_owned {ctx : Ctx} {cur : FnDef}
    (fuel n : Nat) (literal : IxIR0.Literal) {store' : Store}
    {value : RVal}
    (hrun : runCode ctx (fuel + 1) cur {} []
      (.case (.lit (.nat (n + 1))) true
        #[.mk 1 1 (.ret (.lit literal))]) = .ok (store', value)) :
    RootOwnership store' [⟨cur.result, value⟩] := by
  apply runCode_case_nat_succ_contract_owned
    (ctx := ctx) (fuel := fuel) (cur := cur) (store := ({} : Store))
    (store' := store') (env := [])
    (scrut := .lit (.nat (n + 1)))
    (alts := #[.mk 1 1 (.ret (.lit literal))])
    (n := n) (tag := 1) (body := .ret (.lit literal))
    (value := value) (rest := [])
    (entryValid := fun env fields =>
      env = [] ∧ fields = #[RVal.lit (.nat n)])
    (entryRoots := fun _ _ => [])
  · rfl
  · simp [Alt.cidx]
  · exact fixture_nat_succ_alt_contract n literal
  · exact ⟨rfl, rfl⟩
  · exact RootOwnership.empty
  · exact hrun

/-! ## Contentful semantic-projection instances

Both fixtures run the real lowerer on a real expression and apply the
semantic projection theorem to that exact output, so neither the run nor the
`SourceProject` premise is assumed. The source environment holds a
two-field constructor, and the selected field is the *second* one, so a
field-index-blind proof could not close them. -/

/-- Final-use projection: the single source occurrence is consumed, so the
compiler emits `fetch`, `dup`, and the destructive `drop` of the pair, and
the theorem still returns the selected field's graph after the release. -/
theorem fixture_proj_var_final_use_value_sound
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} (src : IxIR0.Env) (fuel : Nat)
    (state : LowSt) (address : Ixon.Address) (tag : Nat)
    (first second : IxIR0.Value) :
    ∃ output emit av,
      (lowerE src (fuel + 2) ⟨[.slot 0 1 .many true], 1⟩ .shared
        (.proj 1 (.var 0))).run state = .ok (output, emit, av) state ∧
      LowerResultValueSound funRel recSelfRel ctx cur
        ⟨[.slot 0 1 .many true], 1⟩ output
        [.ctor address tag [first, second]]
        [.ctor address tag [first, second]] second .shared emit av := by
  obtain ⟨output, emit, av, hrun⟩ :
      ∃ output emit av,
        (lowerE src (fuel + 2) ⟨[.slot 0 1 .many true], 1⟩ .shared
          (.proj 1 (.var 0))).run state = .ok (output, emit, av) state := by
    simp [lowerE, lowerBorrow, worldOfUses, VEnv.setEntry, VEnv.bump,
      VEnv.rel, Function.comp_def, emitOp]
  exact ⟨output, emit, av, hrun,
    lowerE_proj_var_run_value_sound (i := 0) rfl (.ctor rfl) hrun⟩

/-- Repeated-use projection: one source occurrence survives, so the pair
stays owned by the output environment and no `drop` is emitted. -/
theorem fixture_proj_var_kept_value_sound
    {funRel : Sim.FunctionRel} {recSelfRel : RecSelfRel}
    {ctx : Ctx} {cur : FnDef} (src : IxIR0.Env) (fuel : Nat)
    (state : LowSt) (address : Ixon.Address) (tag : Nat)
    (first second : IxIR0.Value) :
    ∃ output emit av,
      (lowerE src (fuel + 2) ⟨[.slot 0 2 .many true], 1⟩ .shared
        (.proj 1 (.var 0))).run state = .ok (output, emit, av) state ∧
      LowerResultValueSound funRel recSelfRel ctx cur
        ⟨[.slot 0 2 .many true], 1⟩ output
        [.ctor address tag [first, second]]
        [.ctor address tag [first, second]] second .shared emit av := by
  obtain ⟨output, emit, av, hrun⟩ :
      ∃ output emit av,
        (lowerE src (fuel + 2) ⟨[.slot 0 2 .many true], 1⟩ .shared
          (.proj 1 (.var 0))).run state = .ok (output, emit, av) state := by
    simp [lowerE, lowerBorrow, worldOfUses, VEnv.setEntry, VEnv.bump,
      VEnv.rel, Function.comp_def, emitOp]
  exact ⟨output, emit, av, hrun,
    lowerE_proj_var_run_value_sound (i := 0) rfl (.ctor rfl) hrun⟩

end Compilatrix.IxIR1.LowerSim
