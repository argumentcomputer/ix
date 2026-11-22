import Aiur.Tiling.IxaTrace

/-!
# `putFunctionOf` writes `IPlan.of`

`Trace.putFunctionOf` writes a function's population plan after comparing its
replay with the certified layout. `IPlan.of` is the plan record it writes, and
`putFunctionOf_eq` proves that, after the compiler's checks (`planChecks`), the
compiler's writer *is* `putIPlan encode (IPlan.of …)`, provided every hint
step's site has an execution program counter (`HintsResolve`).

A hint step's operation is written with `hintPCs[site]`, the program counter of
the `site`-th hint instruction of the function's bytecode, and `putOperation`
throws when there is none. That throw happens mid-record, after earlier
polynomials have been interned, so it cannot be moved in front of the record
without changing which error is reported. `HintsResolve` is therefore a
hypothesis of `putFunctionOf_eq`, and `putFunctionOf_resolves` proves it holds
whenever `putFunctionOf` succeeds: on every successful run the two writers
produce the same bytes and pool (`putFunctionOf_ok`).
-/

namespace Aiur.Tiling.Ixa

open Aiur.Ixon Aiur.Circuit Aiur.Trace Aiur.Execution Aiur.Optimized

section Plan

variable {F : Type} [Field F] [DecidableEq F] (encode : F → Nat)

/-- The program counter of every hint instruction of `bytecode`, in order. -/
def hintPCsOf (bytecode : Execution.Function F) : List Nat :=
  bytecode.code.toList.zipIdx.filterMap fun (op, pc) =>
    match op with | .hint .. => some pc | _ => none

/-- The written form of an operation; a hint site without a program counter
gets `0`, which `HintsResolve` excludes. -/
def IOp.of (hintPCs : List Nat) : Trace.Operation F → IOp F
  | .assign dest values => .assign dest values
  | .inverse dest value => .inverse dest value
  | .choose dest tests => .choose dest tests
  | .failure dest differences => .failure dest differences
  | .call name args dest => .call name args dest
  | .store type values dest => .store type values dest
  | .load type address dest => .load type address dest
  | .hint site type keyType key dest channel => .hint channel (hintPCs.getD site 0) type keyType key dest

/-- The hint site of `op`, if any, has a program counter. -/
def Operation.Resolves (hintPCs : List Nat) : Trace.Operation F → Bool
  | .hint site .. => site < hintPCs.length
  | _ => true

/-- The steps `putFunctionOf` writes: the replay's companion steps, then one
assignment per degree-bounding cache entry. -/
def planSteps (replay : Replay F) : Array (Step F) :=
  replay.source.steps ++ (replay.degree.cache.reverse.map fun (scope, value, dest) =>
    Step.mk scope (.assign [dest] [value])).toArray

/-- The column writes `putFunctionOf` writes. -/
def planWrites (replay : Replay F) (layout : LaidOutChip F) : List (Nat × Nat × ArithExpr F) :=
  replay.columns.zipIdx.flatMap fun (old, column) =>
    (layout.layout.occupants[old]?.getD []).map fun id =>
      let guard := match replay.degree.chip.roles[id]? with
        | some (.auxiliary scope) => replay.source.chip.activation scope
        | _ => .const 1
      (column, id, guard)

/-- Every hint step of the plan has a program counter in `bytecode`. -/
def HintsResolve (replay : Replay F) (bytecode : Execution.Function F) : Prop :=
  ∀ step ∈ (planSteps replay).toList, Operation.Resolves (hintPCsOf bytecode) step.operation = true

/-- The plan record `putFunctionOf` writes. -/
def IPlan.of (fn : Function F) (replay : Replay F) (layout : LaidOutChip F)
    (representative : String) (bytecode : Execution.Function F) : IPlan F where
  name := fn.name
  representative := representative
  roles := replay.degree.chip.roles.size
  inputs := replay.source.chip.inputs.flatMap WireValue.words
  outputs := replay.source.chip.output.words
  steps := (planSteps replay).toList.map fun step =>
    (replay.source.chip.activation step.scope, IOp.of (hintPCsOf bytecode) step.operation)
  writes := planWrites replay layout

/-- The checks `putFunctionOf` makes before writing: the replay reproduces the
certified logical chip, column allocation and final chip, and its source has
exactly as many hint sites as the bytecode has hint instructions. -/
def planChecks (config : Config) (fn : Function F) (replay : Replay F) (layout : LaidOutChip F)
    (bytecode : Execution.Function F) : PoolM Unit := do
  unless replay.degree.chip == layout.logical do throw s!"trace logical layout mismatch in {fn.name}"
  unless replay.layout == layout.layout do throw s!"trace column allocation mismatch in {fn.name}"
  unless replay.chip == layout.chip do
    throw (if config.propagateValues then s!"trace final compaction mismatch in {fn.name}"
      else s!"trace final layout mismatch in {fn.name}")
  unless replay.source.hints == (hintPCsOf bytecode).length do
    throw s!"trace hint occurrence mismatch in {fn.name}"

theorem putOperation_eq (hintPCs : List Nat) (op : Trace.Operation F)
    (h : Operation.Resolves hintPCs op = true) :
    putOperation encode hintPCs op = putIOp encode (IOp.of hintPCs op) := by
  cases op with
  | hint site type keyType key dest channel =>
    simp only [Operation.Resolves, decide_eq_true_eq] at h
    have pc : hintPCs.getD site 0 = hintPCs[site] := by simp [List.getD, List.getElem?_eq_getElem h]
    simp only [putOperation, putIOp, IOp.of, List.getElem?_eq_getElem h, pc]
    rfl
  | _ => rfl

theorem putOperation_unresolved (hintPCs : List Nat) (op : Trace.Operation F)
    (h : Operation.Resolves hintPCs op = false) :
    putOperation encode hintPCs op = throw "missing execution hint site" := by
  cases op with
  | hint site type keyType key dest channel =>
    simp only [Operation.Resolves, decide_eq_false_iff_not, Nat.not_lt] at h
    simp only [putOperation, List.getElem?_eq_none h]
  | _ => simp [Operation.Resolves] at h

private theorem forIn_yield_congr {α : Type} (xs : List α) (f g : α → PoolM PUnit)
    (h : ∀ x ∈ xs, f x = g x) :
    forIn xs PUnit.unit (fun x _ => (do f x; pure (ForInStep.yield PUnit.unit))) =
      forIn xs PUnit.unit (fun x _ => (do g x; pure (ForInStep.yield PUnit.unit))) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.forIn_cons]
    rw [h x List.mem_cons_self]
    congr 1
    funext r
    cases r with
    | done b => rfl
    | yield b => cases b; exact ih fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- `putFunctionOf` with its checks first and its records named. -/
theorem putFunctionOf_unfold (config : Config) (fn : Function F) (replay : Replay F)
    (layout : LaidOutChip F) (representative : String) (bytecode : Execution.Function F) :
    putFunctionOf encode config fn replay layout representative bytecode = (do
      planChecks config fn replay layout bytecode
      str fn.name
      str representative
      nat replay.degree.chip.roles.size
      nats (replay.source.chip.inputs.flatMap WireValue.words)
      nats replay.source.chip.output.words
      arrayP (planSteps replay) fun step => do
        putPolynomial encode (replay.source.chip.activation step.scope)
        putOperation encode (hintPCsOf bytecode) step.operation
      listP (planWrites replay layout) fun (column, id, guard) => do
        nat column; nat id; putPolynomial encode guard) := by
  obtain ⟨source, degree, replayed, chip, columns⟩ := replay
  simp only [putFunctionOf, planChecks, hintPCsOf, planSteps, planWrites]
  split_ifs <;> first
    | (rename_i a b; exact absurd a b)
    | (rename_i a b; exact absurd b a)
    | (simp only [bind_assoc, pure_bind]; rfl)
    | rfl

theorem planSteps_eq (fn : Function F) (replay : Replay F) (layout : LaidOutChip F)
    (representative : String) (bytecode : Execution.Function F)
    (hints : HintsResolve replay bytecode) :
    (arrayP (planSteps replay) fun step => do
        putPolynomial encode (replay.source.chip.activation step.scope)
        putOperation encode (hintPCsOf bytecode) step.operation) =
      listP (IPlan.of fn replay layout representative bytecode).steps
        (fun (guard, op) => do putPolynomial encode guard; putIOp encode op) := by
  simp only [arrayP, listP, IPlan.of, List.length_map, Array.length_toList, List.forIn_map]
  rw [← Array.forIn_toList]
  rw [forIn_yield_congr _ _ _ fun step mem => by rw [putOperation_eq encode _ _ (hints step mem)]]

/-- After its checks, the compiler's plan writer is `putIPlan` of
`IPlan.of`, when every hint site resolves. -/
theorem putFunctionOf_eq (config : Config) (fn : Function F) (replay : Replay F)
    (layout : LaidOutChip F) (representative : String) (bytecode : Execution.Function F)
    (hints : HintsResolve replay bytecode) :
    putFunctionOf encode config fn replay layout representative bytecode = (do
      planChecks config fn replay layout bytecode
      putIPlan encode (IPlan.of fn replay layout representative bytecode)) := by
  rw [putFunctionOf_unfold, planSteps_eq encode fn replay layout representative bytecode hints]
  rfl

/-- `m` fails from every state. -/
def Fails {α : Type} (m : PoolM α) : Prop :=
  ∀ pool bytes, ∃ e bytes', (m.run pool).run bytes = .error e bytes'

private theorem bind_apply {α β : Type} (m : PoolM α) (f : α → PoolM β) (pool : NodePool)
    (bytes : ByteArray) :
    ((m >>= f).run pool).run bytes = match (m.run pool).run bytes with
      | .ok p b => ((f p.1).run p.2).run b
      | .error e b => .error e b := by
  simp only [StateT.run, EStateM.run, bind, StateT.bind, EStateM.bind]
  cases m pool bytes <;> rfl

private theorem Fails.bind {α β : Type} {m : PoolM α} (h : Fails m) (f : α → PoolM β) :
    Fails (m >>= f) := by
  intro pool bytes
  obtain ⟨e, bytes', hm⟩ := h pool bytes
  exact ⟨e, bytes', by rw [bind_apply, hm]⟩

private theorem Fails.bind_right {α β : Type} (m : PoolM α) {f : α → PoolM β}
    (h : ∀ a, Fails (f a)) : Fails (m >>= f) := by
  intro pool bytes
  rw [bind_apply]
  split
  · next p b _ => exact h p.1 p.2 b
  · next e b _ => exact ⟨e, b, rfl⟩

private theorem Fails.throw {α : Type} (e : String) : Fails (throw e : PoolM α) :=
  fun _ bytes => ⟨e, bytes, rfl⟩

private theorem forIn_fails {α : Type} (xs : List α) (f : α → PoolM PUnit) (x : α) (mem : x ∈ xs)
    (h : Fails (f x)) :
    Fails (forIn xs PUnit.unit (fun x _ => (do f x; pure (ForInStep.yield PUnit.unit)))) := by
  induction xs with
  | nil => cases mem
  | cons y ys ih =>
    simp only [List.forIn_cons, bind_assoc, pure_bind]
    rcases List.mem_cons.mp mem with rfl | mem
    · exact h.bind _
    · exact Fails.bind_right _ fun _ => ih mem

/-- A hint site without a program counter makes `putFunctionOf` fail. -/
theorem putFunctionOf_fails (config : Config) (fn : Function F) (replay : Replay F)
    (layout : LaidOutChip F) (representative : String) (bytecode : Execution.Function F)
    (hints : ¬ HintsResolve replay bytecode) :
    Fails (putFunctionOf encode config fn replay layout representative bytecode) := by
  simp only [HintsResolve, not_forall, Bool.not_eq_true] at hints
  obtain ⟨step, mem, bad⟩ := hints
  have loop : Fails (arrayP (planSteps replay) fun step => do
      putPolynomial encode (replay.source.chip.activation step.scope)
      putOperation encode (hintPCsOf bytecode) step.operation) := by
    unfold arrayP
    refine Fails.bind_right _ fun _ => ?_
    rw [← Array.forIn_toList]
    refine Fails.bind (forIn_fails _ _ step mem ?_) _
    rw [putOperation_unresolved encode _ _ bad]
    exact Fails.bind_right _ fun _ => Fails.throw _
  rw [putFunctionOf_unfold]
  iterate 6 refine Fails.bind_right _ fun _ => ?_
  exact loop.bind _

/-- Every successful run of `putFunctionOf` resolves every hint site. -/
theorem putFunctionOf_resolves (config : Config) (fn : Function F) (replay : Replay F)
    (layout : LaidOutChip F) (representative : String) (bytecode : Execution.Function F)
    (pool : NodePool) (bytes : ByteArray) (r : Unit × NodePool) (bytes' : ByteArray)
    (ok : ((putFunctionOf encode config fn replay layout representative bytecode).run pool).run bytes =
      .ok r bytes') :
    HintsResolve replay bytecode := by
  refine Classical.byContradiction fun hints => ?_
  obtain ⟨e, bytes'', h⟩ := putFunctionOf_fails encode config fn replay layout representative
    bytecode hints pool bytes
  rw [ok] at h
  cases h

/-- Every successful run of the compiler's plan writer is a run of the checks
followed by `putIPlan` of `IPlan.of`, with the same bytes and pool. -/
theorem putFunctionOf_ok (config : Config) (fn : Function F) (replay : Replay F)
    (layout : LaidOutChip F) (representative : String) (bytecode : Execution.Function F)
    (pool : NodePool) (bytes : ByteArray) (r : Unit × NodePool) (bytes' : ByteArray)
    (ok : ((putFunctionOf encode config fn replay layout representative bytecode).run pool).run bytes =
      .ok r bytes') :
    ((planChecks config fn replay layout bytecode >>= fun _ =>
        putIPlan encode (IPlan.of fn replay layout representative bytecode)).run pool).run bytes =
      .ok r bytes' := by
  rw [← putFunctionOf_eq encode config fn replay layout representative bytecode
    (putFunctionOf_resolves encode config fn replay layout representative bytecode pool bytes r
      bytes' ok)]
  exact ok

end Plan

end Aiur.Tiling.Ixa
