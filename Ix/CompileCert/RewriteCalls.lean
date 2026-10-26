import Ix.CompileCert.DevelopmentState
import Ix.Compile.Pass.Translate

/-! Ordered development calls extracted from actual successful rewrite runs.
Calls carry literal helper equations, without input or output frame premises.
This chain is not the semantic `DevelopmentFrames.History`. -/
namespace Ix.CompileCert.RewriteCalls
open Ix (Name Expr)
open Ix.Compile.Image Ix.Compile.Pass
open DevelopmentFrames

structure Call where
  before : DevState
  fn : Expr
  args : Array Expr
  result : Expr
  after : DevState
  actual : instantiateWith before fn args = .ok (result, after)

inductive Chain : DevState → List Call → DevState → Prop where
  | nil (state : DevState) : Chain state [] state
  | cons (call : Call) {calls : List Call} {after : DevState}
      (tail : Chain call.after calls after) : Chain call.before (call :: calls) after

theorem Chain.append {before middle after : DevState} {first second : List Call}
    (head : Chain before first middle) (tail : Chain middle second after) :
    Chain before (first ++ second) after := by
  induction head with
  | nil => exact tail
  | cons call rest ih => exact .cons call (ih tail)

theorem Chain.preserves {before after : DevState} {calls : List Call}
    (chain : Chain before calls after) : InstFrames before → InstFrames after := by
  induction chain with
  | nil => exact id
  | cons call rest ih =>
    intro good
    exact ih (DevelopmentState.instantiateWith_state call.fn call.args good call.actual)

private def Traced (action : RwM α) : Prop :=
  ∀ cfg before out after, (action cfg).run before = .ok (out, after) →
    ∃ calls, Chain before.dev calls after.dev

private theorem pureT (value : α) : Traced (pure value) := by
  intro cfg before out after run
  cases Except.ok.inj run; exact ⟨[], .nil _⟩

private theorem bindT {first : RwM α} {next : α → RwM β}
    (head : Traced first) (tail : ∀ value, Traced (next value)) : Traced (first >>= next) := by
  intro cfg before out after run
  change ((first cfg).run before >>= fun result => (next result.1 cfg).run result.2) = .ok (out, after) at run
  obtain ⟨⟨value, middle⟩, firstRun, nextRun⟩ := Loop.except_bind_ok.mp run
  obtain ⟨firstCalls, firstChain⟩ := head cfg before value middle firstRun
  obtain ⟨nextCalls, nextChain⟩ := tail value cfg middle out after nextRun
  exact ⟨firstCalls ++ nextCalls, firstChain.append nextChain⟩

private theorem getT : Traced (get : RwM RwState) := by
  intro cfg before out after run
  cases Except.ok.inj run; exact ⟨[], .nil _⟩

private theorem readT : Traced (read : RwM RwConfig) := by
  intro cfg before out after run
  cases Except.ok.inj run; exact ⟨[], .nil _⟩

private theorem modifyT (update : RwState → RwState)
    (same : ∀ state, (update state).dev = state.dev) : Traced (modify update) := by
  intro cfg before out after run
  cases Except.ok.inj run
  exact ⟨[], same before ▸ Chain.nil before.dev⟩

private theorem liftT (action : Except String α) : Traced (liftM action) := by
  intro cfg before out after run
  dsimp [StateT.run, _root_.liftM, monadLift, MonadLift.monadLift, StateT.lift] at run
  obtain ⟨value, _, same⟩ := Loop.except_bind_ok.mp run
  cases Except.ok.inj same; exact ⟨[], .nil _⟩

private theorem throwT (error : String) : Traced (throw error : RwM α) := by
  intro cfg before out after run; cases run

private theorem withReaderT (update : RwConfig → RwConfig) {action : RwM α}
    (traced : Traced action) : Traced (withReader update action) :=
  fun cfg before out after run => traced (update cfg) before out after run

private theorem mapT (f : α → β) {action : RwM α} (traced : Traced action) : Traced (f <$> action) := by
  rw [← bind_pure_comp]
  exact bindT traced (fun value => pureT (f value))

private theorem iteT {condition : Prop} [Decidable condition] {yes no : RwM α}
    (left : condition → Traced yes) (right : ¬ condition → Traced no) :
    Traced (if condition then yes else no) := by
  split
  · exact left (by assumption)
  · exact right (by assumption)

private theorem forInT (xs : List α) (f : α → β → RwM (ForInStep β))
    (step : ∀ x ∈ xs, ∀ b, Traced (f x b)) : ∀ b, Traced (forIn xs b f) := by
  induction xs with
  | nil => intro b; exact pureT b
  | cons x xs ih =>
    intro b
    rw [List.forIn_cons]
    apply bindT (step x (by simp) b)
    intro result
    cases result with
    | done value => exact pureT value
    | yield value => exact ih (fun x hx => step x (by simp [hx])) value

private theorem arrayForInT (xs : Array α) (f : α → β → RwM (ForInStep β))
    (step : ∀ x ∈ xs, ∀ b, Traced (f x b)) (b : β) : Traced (forIn xs b f) := by
  rw [← Array.forIn_toList]
  exact forInT xs.toList f (by simpa using step) b

/-- A captured state immediately reinstalled with only non-dev fields changed. -/
private theorem getSetT (update : RwState → RwState) (next : RwState → RwM α)
    (same : ∀ state, (update state).dev = state.dev) (tail : ∀ state, Traced (next state)) :
    Traced (do let state ← get; set (update state); next state) := by
  intro cfg before out after run
  change (next before cfg).run (update before) = .ok (out, after) at run
  obtain ⟨calls, chain⟩ := tail before cfg (update before) out after run
  exact ⟨calls, (same before) ▸ chain⟩

/-- Keep the helper pair intact when the elaborated continuation projects it.
The actual captured dev0/reset/call/reinstall contributes exactly one call. -/
private theorem callContinueT (f : Expr) (args : Array Expr)
    (next : Expr × DevState → RwM α) (tail : ∀ result, Traced (next result)) : Traced (do
      let dev0 := (← get).dev
      modify fun st => { st with dev := {} }
      let result ← liftM (instantiateWith dev0 f args)
      modify fun st => { st with dev := result.2 }
      next result) := by
  intro cfg before out after run
  dsimp [StateT.run, bind, ReaderT.bind, StateT.bind, pure, ReaderT.pure,
    StateT.pure, get, getThe, MonadStateOf.get, MonadStateOf.modifyGet,
    modify, modifyGet, _root_.liftM, monadLift, MonadLift.monadLift, StateT.get,
    StateT.modifyGet, StateT.lift, Except.bind, Except.pure] at run
  cases actual : instantiateWith before.dev f args with
  | error error => simp only [actual] at run; cases run
  | ok result =>
    simp only [actual] at run
    obtain ⟨calls, chain⟩ := tail result cfg { before with dev := result.2 } out after run
    let call : Call := ⟨before.dev, f, args, result.1, result.2, actual⟩
    exact ⟨call :: calls, .cons call chain⟩

local macro "trace_step" smallerExp:term "," smallerRw:term : tactic => `(tactic|
  first
    | simp (config := { failIfUnchanged := true }) only [pure_bind]
    | contradiction
    | apply iteT <;> intro condition
    | exact pureT _
    | apply callContinueT; intro body
    | exact getT
    | apply getSetT; · intro state; rfl
      intro state
    | exact readT
    | exact liftT _
    | exact $smallerExp _
    | exact $smallerRw _ _
    | apply modifyT; intro state; rfl
    | apply arrayForInT; intro value member acc
    | apply withReaderT
    | apply mapT
    | refine bindT ?_ (fun _ => ?_)
    | split
    | dsimp (config := { failIfUnchanged := true }) only)

local macro "trace_rw" smallerExp:term "," smallerRw:term : tactic => `(tactic|
  with_reducible repeat' trace_step $smallerExp, $smallerRw)

private theorem app_step (expansion? : Name → Except String (Option Expansion)) (fuel : Nat)
    (smallExp : ∀ name, Traced (expansionOf expansion? fuel name))
    (smallRw : ∀ record e, Traced (Ix.Compile.Pass.rw expansion? fuel record e))
    (record : Bool) (f a : Expr) (hash : Address) :
    Traced (Ix.Compile.Pass.rw expansion? (fuel + 1) record (.app f a hash)) := by
  rw [Ix.Compile.Pass.rw]
  trace_rw smallExp, smallRw

private theorem const_step (expansion? : Name → Except String (Option Expansion)) (fuel : Nat)
    (smallExp : ∀ name, Traced (expansionOf expansion? fuel name))
    (smallRw : ∀ record e, Traced (Ix.Compile.Pass.rw expansion? fuel record e))
    (record : Bool) (name : Name) (levels : Array Ix.Level) (hash : Address) :
    Traced (Ix.Compile.Pass.rw expansion? (fuel + 1) record (.const name levels hash)) := by
  rw [Ix.Compile.Pass.rw]
  trace_rw smallExp, smallRw

private theorem workers (expansion? : Name → Except String (Option Expansion)) (fuel : Nat) :
    (∀ name, Traced (expansionOf expansion? fuel name)) ∧
    (∀ record e, Traced (Ix.Compile.Pass.rw expansion? fuel record e)) := by
  induction fuel with
  | zero =>
    constructor
    · intro name; rw [expansionOf]; exact throwT _
    · intro record e; rw [Ix.Compile.Pass.rw]; exact throwT _
  | succ fuel ih =>
    constructor
    · intro name
      rw [expansionOf]
      with_reducible repeat' first
        | exact pureT _
        | exact getT
        | exact readT
        | exact liftT _
        | exact ih.2 _ _
        | apply modifyT; intro state; rfl
        | apply withReaderT
        | apply mapT
        | refine bindT ?_ (fun _ => ?_)
        | split
    · intro record e
      cases e
      case app f a hash => exact app_step expansion? fuel ih.1 ih.2 record f a hash
      case const name levels hash => exact const_step expansion? fuel ih.1 ih.2 record name levels hash
      all_goals rw [Ix.Compile.Pass.rw]; trace_rw ih.1, ih.2

theorem expansionOf_calls (expansion? : Name → Except String (Option Expansion))
    (fuel : Nat) (name : Name) (cfg : RwConfig) (before after : RwState) (out : Option Expansion)
    (run : ((expansionOf expansion? fuel name) cfg).run before = .ok (out, after)) :
    ∃ calls, Chain before.dev calls after.dev :=
  (workers expansion? fuel).1 name cfg before out after run

theorem rw_calls (expansion? : Name → Except String (Option Expansion))
    (fuel : Nat) (record : Bool) (e : Expr) (cfg : RwConfig) (before after : RwState) (out : Expr × Bool)
    (run : ((Ix.Compile.Pass.rw expansion? fuel record e) cfg).run before = .ok (out, after)) :
    ∃ calls, Chain before.dev calls after.dev :=
  (workers expansion? fuel).2 record e cfg before out after run

theorem expansionOf_state (expansion? : Name → Except String (Option Expansion))
    (fuel : Nat) (name : Name) (cfg : RwConfig) (before after : RwState) (out : Option Expansion)
    (good : InstFrames before.dev)
    (run : ((expansionOf expansion? fuel name) cfg).run before = .ok (out, after)) :
    InstFrames after.dev := by
  obtain ⟨_, chain⟩ := expansionOf_calls expansion? fuel name cfg before after out run
  exact chain.preserves good

theorem rw_state (expansion? : Name → Except String (Option Expansion))
    (fuel : Nat) (record : Bool) (e : Expr) (cfg : RwConfig) (before after : RwState) (out : Expr × Bool)
    (good : InstFrames before.dev)
    (run : ((Ix.Compile.Pass.rw expansion? fuel record e) cfg).run before = .ok (out, after)) :
    InstFrames after.dev := by
  obtain ⟨_, chain⟩ := rw_calls expansion? fuel record e cfg before after out run
  exact chain.preserves good

end Ix.CompileCert.RewriteCalls
