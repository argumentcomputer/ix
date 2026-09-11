import Ix.Compiler.UniqueReuse.Heap
import Ix.Compiler.IxIR1.EvalHistory

namespace Ix.Compiler.UniqueReuse

open Ix.Compiler.IxIR1
open Ix.Compiler.IxIR1.Sim
open Ix.Compiler.IxIR0.UniqueReverse (Schema Plan)

theorem lets_append (first second : List Op) (code : Code) :
    lets (first ++ second) code = lets first (lets second code) := by
  induction first with
  | nil => rfl
  | cons operation rest ih => simp only [List.cons_append, lets, ih]

theorem inputOperations_nil (schema : Schema) :
    inputOperations schema [] = [.alloc .unique (nilId schema) #[]] := rfl

theorem inputOperations_cons (schema : Schema) (head : Nat) (tail : List Nat) :
    inputOperations schema (head :: tail) = inputOperations schema tail ++
      [.alloc .unique (consId schema) #[.lit (.nat head), .var 0]] := by
  simp [inputOperations, List.reverse_cons]

private theorem consumingConsHistory (ctx : Ctx) (schema : Schema) (store : Store)
    (location head : Nat) (tail accumulator : RVal)
    (found : store.get? location = some ⟨.unique, 1, .ctorN (consId schema) #[.lit (.nat head), tail]⟩) :
    let allocated := (store.kill location).allocNode .unique
      (.ctorN (consId schema) #[.lit (.nat head), accumulator])
    ExecutionHistory ctx
      ⟨consumingFunction schema, store, [.loc location, accumulator], consumingBody schema⟩
      ⟨consumingFunction schema, allocated.1, [tail, .loc allocated.2], consumingBody schema⟩ := by
  dsimp only
  let current := consumingFunction schema
  let allocated := (store.kill location).allocNode .unique
    (.ctorN (consId schema) #[.lit (.nat head), accumulator])
  have branch : ExecutionHistory ctx
      ⟨current, store, [.loc location, accumulator], consumingBody schema⟩
      ⟨current, store, [tail, .lit (.nat head), .loc location, accumulator],
        lets [.free (.var 2), .alloc .unique (consId schema) #[.var 2, .var 4],
          .callSelf #[.var 0, .var 2]] (.ret (.var 0))⟩ :=
    ExecutionHistory.caseCtor rfl found rfl rfl rfl
  have freed := ExecutionHistory.stepOp (next := lets
      [.alloc .unique (consId schema) #[.var 2, .var 4], .callSelf #[.var 0, .var 2]] (.ret (.var 0)))
    (runOp_free (ctx := ctx) (cur := current) (fuel := 0)
      (env := [tail, .lit (.nat head), .loc location, accumulator]) (target := .var 2) rfl found)
  have built := ExecutionHistory.stepOp (next := .letOp (.callSelf #[.var 0, .var 2]) (.ret (.var 0)))
    (runOp_alloc (ctx := ctx) (cur := current) (fuel := 0) (store := store.kill location)
      (env := [.erased, tail, .lit (.nat head), .loc location, accumulator]) (world := .unique)
      (cid := consId schema) (args := #[.var 2, .var 4]) (by rfl))
  have called : ExecutionHistory ctx
      ⟨current, allocated.1, [.loc allocated.2, .erased, tail, .lit (.nat head), .loc location, accumulator],
        .letOp (.callSelf #[.var 0, .var 2]) (.ret (.var 0))⟩
      ⟨current, allocated.1, [tail, .loc allocated.2], consumingBody schema⟩ :=
    ExecutionHistory.tailCallSelf (arguments := [.loc allocated.2, tail]) rfl rfl
  exact ((branch.trans freed).trans built).trans called

structure LoopResult (schema : Schema) (before after : Store)
    (values accumulator : List Nat) (value : RVal) : Prop where
  owned : RootOwnership after [⟨.unique, value⟩]
  list : ListAt schema after (values.reverse ++ accumulator) value
  allocs : after.allocs = before.allocs + values.length
  frees : after.frees = before.frees + values.length + 1
  reuses : after.reuses = before.reuses
  rcops : after.rcops = before.rcops

theorem consumingLoop (ctx : Ctx) (schema : Schema) (values : List Nat)
    (store : Store) (major accumulator : RVal) (accValues : List Nat)
    (owned : RootOwnership store [⟨.unique, major⟩, ⟨.unique, accumulator⟩])
    (input : ListAt schema store values major) (acc : ListAt schema store accValues accumulator) :
    ∃ output value,
      CodePoint.Runs ctx ⟨consumingFunction schema, store, [major, accumulator], consumingBody schema⟩ (output, value) ∧
      LoopResult schema store output values accValues value := by
  induction values generalizing store major accumulator accValues with
  | nil =>
      cases input with
      | @nil location found =>
          obtain ⟨afterOwned, afterList⟩ := nilConsumed found owned acc
          refine ⟨store.kill location, accumulator, ?_, afterOwned, ?_, ?_, ?_, rfl, rfl⟩
          · exact ⟨3, by simp [consumingBody, runCode, runOp, resolveAtom, found, nilId, IxIR1.Lower.ctorIdOf, Alt.cidx]⟩
          · simpa using afterList
          · simp [Store.kill]
          · simp [Store.kill]
  | cons head tail ih =>
      cases input with
      | @cons _ _ location tailValue found next =>
          let allocated := (store.kill location).allocNode .unique
            (.ctorN (consId schema) #[.lit (.nat head), accumulator])
          have taken := consTaken found owned next acc
          obtain ⟨afterOwned, tailAt, accAt⟩ := taken.allocate
          obtain ⟨output, value, run, result⟩ := ih allocated.1 tailValue (.loc allocated.2)
            (head :: accValues) afterOwned tailAt accAt
          refine ⟨output, value,
            (consumingConsHistory ctx schema store location head tailValue accumulator found).complete
              run result.list.hasWorld, ?_⟩
          refine ⟨result.owned, ?_, ?_, ?_, ?_, ?_⟩
          · simpa [List.reverse_cons, List.append_assoc] using result.list
          · simpa [allocated, Store.kill, Store.allocNode, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result.allocs
          · simpa [allocated, Store.kill, Store.allocNode, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result.frees
          · exact result.reuses
          · exact result.rcops

structure InputResult (schema : Schema) (before after : Store)
    (values : List Nat) (value : RVal) (rest : List Root) : Prop where
  owned : RootOwnership after (⟨.unique, value⟩ :: rest)
  list : ListAt schema after values value
  allocs : after.allocs = before.allocs + values.length + 1
  frees : after.frees = before.frees
  reuses : after.reuses = before.reuses
  rcops : after.rcops = before.rcops

theorem inputHistory (ctx : Ctx) (current : FnDef) (schema : Schema) (values : List Nat)
    (store : Store) (environment : List RVal) (rest : List Root) (code : Code)
    (owned : RootOwnership store rest) :
    ∃ output value remaining,
      ExecutionHistory ctx ⟨current, store, environment, lets (inputOperations schema values) code⟩
        ⟨current, output, value :: remaining, code⟩ ∧
      InputResult schema store output values value rest := by
  induction values generalizing store environment code with
  | nil =>
      let output := store.allocNode .unique (.ctorN (nilId schema) #[])
      refine ⟨output.1, .loc output.2, environment, ?_, ownedNilAllocation owned schema, nilAllocated store schema,
        ?_, rfl, rfl, rfl⟩
      · exact ExecutionHistory.stepOp (runOp_alloc (ctx := ctx) (cur := current) (fuel := 0)
          (store := store) (env := environment) (world := .unique) (cid := nilId schema) (args := #[]) rfl)
      · simp [output, Store.allocNode]
  | cons head tail ih =>
      let operation := Op.alloc .unique (consId schema) #[.lit (.nat head), .var 0]
      obtain ⟨middle, tailValue, remaining, history, result⟩ :=
        ih store environment (.letOp operation code) owned
      let output := middle.allocNode .unique (.ctorN (consId schema) #[.lit (.nat head), tailValue])
      have ready : RootOwnership middle
          (rootsFor .unique (nodeChildren (.ctorN (consId schema) #[.lit (.nat head), tailValue])) ++ rest) :=
        RootOwnership.addNoLocation (value := .lit (.nat head)) rfl result.owned
      refine ⟨output.1, .loc output.2, tailValue :: remaining, ?_, ready.allocNode trivial,
        consAllocated result.list head, ?_, ?_, ?_, ?_⟩
      · have built := ExecutionHistory.stepOp (next := code) (runOp_alloc (ctx := ctx) (cur := current)
          (fuel := 0) (store := middle) (env := tailValue :: remaining)
          (world := .unique) (cid := consId schema) (args := #[.lit (.nat head), .var 0]) rfl)
        simpa [inputOperations_cons, lets_append, lets, operation, output] using history.trans built
      · have count := result.allocs
        simp only [output, Store.allocNode, List.length_cons]
        omega
      · exact result.frees
      · exact result.reuses
      · exact result.rcops

structure MainResult (plan : Plan) (store : Store) (value : RVal) : Prop where
  owned : RootOwnership store [⟨.unique, value⟩]
  list : ListAt plan.schema store plan.values.reverse value
  allocs : store.allocs = 2 * plan.values.length + 2
  frees : store.frees = plan.values.length + 1
  reuses : store.reuses = 0
  rcops : store.rcops = 0
  live : store.live = plan.values.length + 1

theorem mainExists (plan : Plan) :
    ∃ fuel store value,
      runOwnedMain { decls := Env.ofList (declarations plan.schema) } .unique (mainCode plan) fuel = .ok (store, value) ∧
      MainResult plan store value := by
  let ctx : Ctx := { decls := Env.ofList (declarations plan.schema) }
  let current : FnDef := ⟨0, .unique, false, mainCode plan⟩
  let suffix := lets [.alloc .unique (nilId plan.schema) #[],
    .call (functionAddress plan.schema) #[.var 0, .var 1]] (.ret (.var 0))
  obtain ⟨built, inputValue, remaining, history, inputResult⟩ :=
    inputHistory ctx current plan.schema plan.values {} [] [] suffix RootOwnership.empty
  let initialized := built.allocNode .unique (.ctorN (nilId plan.schema) #[])
  have initializedOwned : RootOwnership initialized.1 [⟨.unique, inputValue⟩, ⟨.unique, .loc initialized.2⟩] :=
    (ownedNilAllocation inputResult.owned plan.schema).perm (List.Perm.swap _ _ [])
  obtain ⟨store, value, loopRun, loopResult⟩ := consumingLoop ctx plan.schema plan.values initialized.1
    inputValue (.loc initialized.2) [] initializedOwned (inputResult.list.allocNode .unique _) (nilAllocated built plan.schema)
  have accumulatorHistory := ExecutionHistory.stepOp (next := .letOp
      (.call (functionAddress plan.schema) #[.var 0, .var 1]) (.ret (.var 0)))
    (runOp_alloc (ctx := ctx) (cur := current) (fuel := 0) (store := built)
      (env := inputValue :: remaining) (world := .unique) (cid := nilId plan.schema) (args := #[]) rfl)
  have call : ExecutionHistory ctx
      ⟨current, initialized.1, .loc initialized.2 :: inputValue :: remaining,
        .letOp (.call (functionAddress plan.schema) #[.var 0, .var 1]) (.ret (.var 0))⟩
      ⟨consumingFunction plan.schema, initialized.1, [inputValue, .loc initialized.2], consumingBody plan.schema⟩ :=
    ExecutionHistory.tailCall (arguments := [.loc initialized.2, inputValue]) rfl
      (by simp [ctx, declarations, Env.ofList]) rfl rfl
  have complete := ((history.trans accumulatorHistory).trans call).complete loopRun loopResult.list.hasWorld
  obtain ⟨fuel, run⟩ := complete
  have bodyRun : runCode ctx fuel current {} [] (mainCode plan) = .ok (store, value) := by
    simpa only [mainCode, lets_append, suffix] using run
  have world := rval_hasWorld_eq_true_iff.mpr loopResult.list.hasWorld
  have ownedRun : runOwnedMain ctx .unique (mainCode plan) fuel = .ok (store, value) := by
    simp [runOwnedMain, bodyRun, current, checkResultWorld, world]
  have hallocs : store.allocs = 2 * plan.values.length + 2 := by
    have ih := inputResult.allocs
    have lh := loopResult.allocs
    simp only [initialized, Store.allocNode] at lh
    change built.allocs = 0 + plan.values.length + 1 at ih
    omega
  have hfrees : store.frees = plan.values.length + 1 := by
    simpa [initialized, Store.allocNode, inputResult.frees] using loopResult.frees
  have footprint := (IxIR1.Reclamation.runCode_footprint bodyRun).live_balance
  refine ⟨fuel, store, value, ownedRun, loopResult.owned, ?_, hallocs, hfrees, ?_, ?_, ?_⟩
  · simpa using loopResult.list
  · exact loopResult.reuses.trans inputResult.reuses
  · exact loopResult.rcops.trans inputResult.rcops
  · change store.live + store.frees + 0 = 0 + 0 + store.allocs at footprint
    omega

end Ix.Compiler.UniqueReuse
