import Ix.Compiler.IxIR1.Mono
import Ix.Compiler.IxIR1.EvalRewrite

/-!
# Composable source execution history

A machine proof visits a callee before it knows the callee's eventual result.
`ExecutionHistory` records enough source execution to reconstruct that result
later. Its completion implication composes across ordinary operations, case
selection, and tail calls, while keeping the result ownership check explicit.
Fuel is existential: independent prefixes and suffixes are joined by raising
their successful runs to a common bound.
-/

namespace Ix.Compiler.IxIR1

open Ix.Compiler.Ixon (Owned Address)

/-- A source evaluator position, including its dynamic self-call frame. -/
structure CodePoint where
  current : FnDef
  store : Store
  environment : List RVal
  code : Code

/-- Successful completion at some finite evaluator fuel. -/
def CodePoint.Runs (ctx : Ctx) (point : CodePoint) (out : Store × RVal) : Prop :=
  ∃ fuel, runCode ctx fuel point.current point.store point.environment
    point.code = .ok out

/-- A completed suffix reconstructs the earlier source computation. Result
ownership is preserved across frame replacement, including tail calls. -/
structure ExecutionHistory (ctx : Ctx) (before after : CodePoint) : Prop where
  resultWorld : before.current.result = after.current.result
  complete : ∀ {out : Store × RVal}, after.Runs ctx out →
    Sim.HasWorld out.1 after.current.result out.2 → before.Runs ctx out

namespace ExecutionHistory

theorem refl (ctx : Ctx) (point : CodePoint) :
    ExecutionHistory ctx point point := ⟨rfl, fun run _ => run⟩

theorem trans {ctx : Ctx} {before middle after : CodePoint}
    (earlier : ExecutionHistory ctx before middle)
    (suffix : ExecutionHistory ctx middle after) :
    ExecutionHistory ctx before after := by
  refine ⟨earlier.resultWorld.trans suffix.resultWorld, ?_⟩
  intro out run world
  exact earlier.complete (suffix.complete run world)
    (suffix.resultWorld.symm ▸ world)

/-- Consume one successful operation without fixing the suffix fuel. -/
theorem stepOp {ctx : Ctx} {current : FnDef}
    {store nextStore : Store} {environment : List RVal}
    {operation : Op} {next : Code} {value : RVal} {fuel : Nat}
    (run : runOp ctx fuel current store environment operation =
      .ok (nextStore, value)) :
    ExecutionHistory ctx ⟨current, store, environment, .letOp operation next⟩
      ⟨current, nextStore, value :: environment, next⟩ := by
  refine ⟨rfl, ?_⟩
  rintro out ⟨suffixFuel, suffix⟩ _world
  let bound := max fuel suffixFuel
  have prefixRun := runOp_mono (Nat.le_max_left fuel suffixFuel) run
  have suffixRun := runCode_mono (Nat.le_max_right fuel suffixFuel) suffix
  exact ⟨bound + 1, by simpa [bind, Except.bind, runCode, bound, prefixRun] using suffixRun⟩

theorem caseCtor {ctx : Ctx} {current : FnDef} {store : Store}
    {environment : List RVal} {scrutinee : Atom} {peelNat : Bool}
    {alternatives : Array Alt} {location : Nat} {box : NodeBox}
    {identity : CtorId} {fields : Array RVal} {tag fieldCount : Nat}
    {body : Code}
    (resolved : resolveAtom environment scrutinee = .ok (.loc location))
    (found : store.get? location = some box)
    (node : box.node = .ctorN identity fields)
    (selected : alternatives.find? (fun alt => alt.cidx == identity.cidx) =
      some (.mk tag fieldCount body))
    (count : fields.size = fieldCount) :
    ExecutionHistory ctx
      ⟨current, store, environment, .case scrutinee peelNat alternatives⟩
      ⟨current, store, fields.foldl (fun env value => value :: env) environment,
        body⟩ := by
  refine ⟨rfl, ?_⟩
  rintro out ⟨fuel, run⟩ _world
  exact ⟨fuel + 1, by
    simpa [bind, Except.bind, runCode, resolved, found, node, selected, count] using run⟩

theorem caseNatZero {ctx : Ctx} {current : FnDef} {store : Store}
    {environment : List RVal} {scrutinee : Atom} {alternatives : Array Alt}
    {tag : Nat} {body : Code}
    (resolved : resolveAtom environment scrutinee = .ok (.lit (.nat 0)))
    (selected : alternatives.find? (fun alt => alt.cidx == 0) =
      some (.mk tag 0 body)) :
    ExecutionHistory ctx
      ⟨current, store, environment, .case scrutinee true alternatives⟩
      ⟨current, store, environment, body⟩ := by
  refine ⟨rfl, ?_⟩
  rintro out ⟨fuel, run⟩ _world
  exact ⟨fuel + 1, by simpa [bind, Except.bind, runCode, resolved, selected] using run⟩

theorem caseNatSucc {ctx : Ctx} {current : FnDef} {store : Store}
    {environment : List RVal} {scrutinee : Atom} {alternatives : Array Alt}
    {predecessor tag : Nat} {body : Code}
    (resolved : resolveAtom environment scrutinee =
      .ok (.lit (.nat (predecessor + 1))))
    (selected : alternatives.find? (fun alt => alt.cidx == 1) =
      some (.mk tag 1 body)) :
    ExecutionHistory ctx
      ⟨current, store, environment, .case scrutinee true alternatives⟩
      ⟨current, store, .lit (.nat predecessor) :: environment, body⟩ := by
  refine ⟨rfl, ?_⟩
  rintro out ⟨fuel, run⟩ _world
  exact ⟨fuel + 1, by simpa [bind, Except.bind, runCode, resolved, selected] using run⟩

end ExecutionHistory

/-- Reassemble a function invocation from its completed body and the checked
result world. -/
theorem invoke_of_body_run {ctx : Ctx} {address : Address}
    {definition : FnDef} {store : Store} {arguments : List RVal}
    {fuel : Nat} {out : Store × RVal}
    (declaration : ctx.decls address = some (.fn definition))
    (arity : arguments.length = definition.arity)
    (run : runCode ctx fuel definition store arguments.reverse definition.body =
      .ok out)
    (world : Sim.HasWorld out.1 definition.result out.2) :
    invoke ctx (fuel + 1) address arguments store = .ok out := by
  have checked := Sim.rval_hasWorld_eq_true_iff.mpr world
  simp [bind, Except.bind, invoke, declaration, arity, run, checkResultWorld, checked]

theorem runOp_call_of_body_run {ctx : Ctx} {current definition : FnDef}
    {store : Store} {environment arguments : List RVal} {address : Address}
    {atoms : Array Atom} {fuel : Nat} {out : Store × RVal}
    (resolved : resolveAtoms environment atoms = .ok arguments)
    (declaration : ctx.decls address = some (.fn definition))
    (arity : arguments.length = definition.arity)
    (run : runCode ctx fuel definition store arguments.reverse definition.body =
      .ok out)
    (world : Sim.HasWorld out.1 definition.result out.2) :
    runOp ctx (fuel + 2) current store environment (.call address atoms) =
      .ok out := by
  simpa [bind, Except.bind, runOp, resolved] using invoke_of_body_run declaration arity run world

theorem runOp_callSelf_of_body_run {ctx : Ctx} {current : FnDef}
    {store : Store} {environment arguments : List RVal}
    {atoms : Array Atom} {fuel : Nat} {out : Store × RVal}
    (resolved : resolveAtoms environment atoms = .ok arguments)
    (arity : arguments.length = current.arity)
    (run : runCode ctx fuel current store arguments.reverse current.body =
      .ok out)
    (world : Sim.HasWorld out.1 current.result out.2) :
    runOp ctx (fuel + 1) current store environment (.callSelf atoms) =
      .ok out := by
  have checked := Sim.rval_hasWorld_eq_true_iff.mpr world
  simp [bind, Except.bind, runOp, resolved, arity, run, checkResultWorld, checked]

namespace ExecutionHistory

theorem tailCall {ctx : Ctx} {current definition : FnDef}
    {store : Store} {environment arguments : List RVal} {address : Address}
    {atoms : Array Atom}
    (resolved : resolveAtoms environment atoms = .ok arguments)
    (declaration : ctx.decls address = some (.fn definition))
    (arity : arguments.length = definition.arity)
    (resultWorld : current.result = definition.result) :
    ExecutionHistory ctx
      ⟨current, store, environment, .letOp (.call address atoms) (.ret (.var 0))⟩
      ⟨definition, store, arguments.reverse, definition.body⟩ := by
  refine ⟨resultWorld, ?_⟩
  rintro out ⟨fuel, run⟩ world
  have call := runOp_call_of_body_run (current := current) resolved declaration
    arity run world
  exact ⟨fuel + 3, by
    simp [bind, Except.bind, runCode, call, resolveAtom]⟩

theorem tailCallSelf {ctx : Ctx} {current : FnDef}
    {store : Store} {environment arguments : List RVal} {atoms : Array Atom}
    (resolved : resolveAtoms environment atoms = .ok arguments)
    (arity : arguments.length = current.arity) :
    ExecutionHistory ctx
      ⟨current, store, environment, .letOp (.callSelf atoms) (.ret (.var 0))⟩
      ⟨current, store, arguments.reverse, current.body⟩ := by
  refine ⟨rfl, ?_⟩
  rintro out ⟨fuel, run⟩ world
  have call := runOp_callSelf_of_body_run resolved arity run world
  exact ⟨fuel + 2, by simp [bind, Except.bind, runCode, call, resolveAtom]⟩

end ExecutionHistory

/-- A saturated PAP prefix and its eventual invocation can use different
fuel bounds. Retaining captures and consuming the PAP are replayed exactly. -/
theorem applyGo_exact_of_invoke {ctx : Ctx}
    {store retained released : Store} {arguments : List RVal}
    {location : Nat} {box : NodeBox}
    {address : Address} {arity : Nat} {captured : Array RVal}
    {declaration : Decl} {releaseFuel invokeFuel : Nat} {out : Store × RVal}
    (found : store.get? location = some box)
    (node : box.node = .papN address arity captured)
    (retain : dupVals store captured.toList = .ok retained)
    (release : dropVal ctx releaseFuel retained (.loc location) = .ok released)
    (exactCount : (captured.toList ++ arguments).length = arity)
    (declared : ctx.decls address = some declaration)
    (papSafe : declPapSafe declaration = true)
    (called : invoke ctx invokeFuel address (captured.toList ++ arguments)
      released = .ok out) :
    ∃ fuel, applyGo ctx (fuel + 1) store (.loc location) arguments = .ok out := by
  let bound := max releaseFuel invokeFuel
  have releasedAtBound := dropVal_mono
    (Nat.le_max_left releaseFuel invokeFuel) release
  have calledAtBound := invoke_mono
    (Nat.le_max_right releaseFuel invokeFuel) called
  refine ⟨bound, ?_⟩
  simp [applyGo, found, node,
    retain, releasedAtBound, exactCount, declared, papSafe, calledAtBound,
    bound, bind, Except.bind]

/-- Reconstruct the suspended source operation after joining the PAP prefix
with its successful application. -/
theorem runOp_apply_exact_of_invoke {ctx : Ctx} {current : FnDef}
    {store retained released : Store} {environment arguments : List RVal}
    {function : Atom} {atoms : Array Atom} {location : Nat} {box : NodeBox}
    {address : Address} {arity : Nat} {captured : Array RVal}
    {declaration : Decl} {releaseFuel invokeFuel : Nat} {out : Store × RVal}
    (functionResolved : resolveAtom environment function = .ok (.loc location))
    (argumentsResolved : resolveAtoms environment atoms = .ok arguments)
    (found : store.get? location = some box)
    (node : box.node = .papN address arity captured)
    (retain : dupVals store captured.toList = .ok retained)
    (release : dropVal ctx releaseFuel retained (.loc location) = .ok released)
    (exactCount : (captured.toList ++ arguments).length = arity)
    (declared : ctx.decls address = some declaration)
    (papSafe : declPapSafe declaration = true)
    (called : invoke ctx invokeFuel address (captured.toList ++ arguments)
      released = .ok out) :
    ∃ fuel, runOp ctx (fuel + 2) current store environment
      (.apply function atoms) = .ok out := by
  obtain ⟨fuel, applied⟩ := applyGo_exact_of_invoke
    found node retain release exactCount declared papSafe called
  exact ⟨fuel, by simp [runOp, functionResolved, argumentsResolved,
    applied, bind, Except.bind]⟩

/-- An over-applied PAP prefix composes with the first callee and the whole
residual application. Repeated use handles arbitrary over-application depth. -/
theorem applyGo_over_of_invoke {ctx : Ctx}
    {store retained released : Store} {arguments : List RVal}
    {location : Nat} {box : NodeBox}
    {address : Address} {arity : Nat} {captured : Array RVal}
    {declaration : Decl} {releaseFuel invokeFuel residualFuel : Nat}
    {middle out : Store × RVal}
    (found : store.get? location = some box)
    (node : box.node = .papN address arity captured)
    (retain : dupVals store captured.toList = .ok retained)
    (release : dropVal ctx releaseFuel retained (.loc location) = .ok released)
    (overCount : arity < (captured.toList ++ arguments).length)
    (declared : ctx.decls address = some declaration)
    (papSafe : declPapSafe declaration = true)
    (called : invoke ctx invokeFuel address
      ((captured.toList ++ arguments).take arity) released = .ok middle)
    (residual : applyGo ctx residualFuel middle.1 middle.2
      ((captured.toList ++ arguments).drop arity) = .ok out) :
    ∃ fuel, applyGo ctx (fuel + 1) store (.loc location) arguments = .ok out := by
  let bound := max releaseFuel (max invokeFuel residualFuel)
  have releasedAtBound := dropVal_mono
    (Nat.le_max_left releaseFuel (max invokeFuel residualFuel)) release
  have calledAtBound := invoke_mono (Nat.le_trans
    (Nat.le_max_left invokeFuel residualFuel)
    (Nat.le_max_right releaseFuel (max invokeFuel residualFuel))) called
  have residualAtBound := applyGo_mono (Nat.le_trans
    (Nat.le_max_right invokeFuel residualFuel)
    (Nat.le_max_right releaseFuel (max invokeFuel residualFuel))) residual
  have notUnder : ¬ captured.size + arguments.length < arity := by
    simpa using Nat.not_lt.mpr (Nat.le_of_lt overCount)
  have notExact : ¬ captured.size + arguments.length = arity := by
    simpa using Nat.ne_of_gt overCount
  refine ⟨bound, ?_⟩
  simp [applyGo, found, node,
    retain, releasedAtBound, notUnder, notExact, declared, papSafe,
    calledAtBound, residualAtBound, bound, bind, Except.bind]

/-- Reconstruct the suspended source operation after joining the PAP prefix
with its successful application. -/
theorem runOp_apply_over_of_invoke {ctx : Ctx} {current : FnDef}
    {store retained released : Store} {environment arguments : List RVal}
    {function : Atom} {atoms : Array Atom} {location : Nat} {box : NodeBox}
    {address : Address} {arity : Nat} {captured : Array RVal}
    {declaration : Decl} {releaseFuel invokeFuel residualFuel : Nat}
    {middle out : Store × RVal}
    (functionResolved : resolveAtom environment function = .ok (.loc location))
    (argumentsResolved : resolveAtoms environment atoms = .ok arguments)
    (found : store.get? location = some box)
    (node : box.node = .papN address arity captured)
    (retain : dupVals store captured.toList = .ok retained)
    (release : dropVal ctx releaseFuel retained (.loc location) = .ok released)
    (overCount : arity < (captured.toList ++ arguments).length)
    (declared : ctx.decls address = some declaration)
    (papSafe : declPapSafe declaration = true)
    (called : invoke ctx invokeFuel address
      ((captured.toList ++ arguments).take arity) released = .ok middle)
    (residual : applyGo ctx residualFuel middle.1 middle.2
      ((captured.toList ++ arguments).drop arity) = .ok out) :
    ∃ fuel, runOp ctx (fuel + 2) current store environment
      (.apply function atoms) = .ok out := by
  obtain ⟨fuel, applied⟩ := applyGo_over_of_invoke
    found node retain release overCount declared papSafe called residual
  exact ⟨fuel, by simp [runOp, functionResolved, argumentsResolved,
    applied, bind, Except.bind]⟩

/-- Operations which cannot call source code or the scalar oracle. PAP
allocation is included: it inspects declarations but does not enter them. -/
def Op.isImmediate : Op → Bool
  | .call .. | .callSelf .. | .apply .. | .extern .. => false
  | _ => true

/-- Immediate source steps can be recorded in the canonical compiler
context, independently of the ambient oracle. -/
theorem runOp_immediate_ctx_eq (before after : Ctx)
    (declarations : after.decls = before.decls) (fuel : Nat)
    (current : FnDef) (store : Store) (environment : List RVal)
    (operation : Op) (immediate : operation.isImmediate = true) :
    runOp after fuel current store environment operation =
      runOp before fuel current store environment operation := by
  cases fuel with
  | zero => simp [runOp]
  | succ fuel =>
      cases operation <;> simp only [Op.isImmediate] at immediate
      all_goals try contradiction
      all_goals simp only [runOp]
      all_goals try rfl
      · simp only [Sim.dropVal_ctx_eq before after]
      · simp only [Sim.dropUVal_ctx_eq before after]
      · rw [declarations]

/-- Erased application only consumes its arguments, so its oracle is inert. -/
theorem runOp_apply_erased_ctx_eq (before after : Ctx) (fuel : Nat)
    (current : FnDef) (store : Store) (environment : List RVal)
    (function : Atom) (atoms : Array Atom)
    (resolved : resolveAtom environment function = .ok .erased) :
    runOp after fuel current store environment (.apply function atoms) =
      runOp before fuel current store environment (.apply function atoms) := by
  cases fuel with
  | zero => simp [runOp]
  | succ fuel =>
      simp only [runOp, resolved, bind, Except.bind]
      cases fuel with
      | zero => simp [applyGo]
      | succ fuel => simp only [applyGo, Sim.dropMany_ctx_eq before after]

/-- Under-application only rebuilds a PAP after retaining and releasing its
captures; declaration lookup and the oracle are both inert. -/
theorem runOp_apply_under_ctx_eq (before after : Ctx) (fuel : Nat)
    (current : FnDef) (store : Store) (environment : List RVal)
    (function : Atom) (atoms : Array Atom)
    {location : Nat} {box : NodeBox} {address : Address} {arity : Nat}
    {captured : Array RVal} {arguments : List RVal}
    (functionResolved : resolveAtom environment function = .ok (.loc location))
    (argumentsResolved : resolveAtoms environment atoms = .ok arguments)
    (found : store.get? location = some box)
    (node : box.node = .papN address arity captured)
    (under : (captured.toList ++ arguments).length < arity) :
    runOp after fuel current store environment (.apply function atoms) =
      runOp before fuel current store environment (.apply function atoms) := by
  cases fuel with
  | zero => simp [runOp]
  | succ fuel =>
      simp only [runOp, functionResolved, argumentsResolved, bind, Except.bind]
      cases fuel with
      | zero => simp [applyGo]
      | succ fuel =>
          simp only [applyGo, found, node, under, if_true,
            Sim.dropVal_ctx_eq before after]

end Ix.Compiler.IxIR1
