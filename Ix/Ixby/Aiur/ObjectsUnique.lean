module
public import Ix.Ixby.Aiur.ObjectsEquality
import all Ix.Aiur.Goldilocks

/-! Compiled bounded duplicate-ID traversal. The checked body and its callees
are linked in the same bytecode toplevel. Semantic table decoding remains an
explicit premise here; `ObjectsDeclarations.lean` establishes it while proving
the bounded recursive parser. Admission and whole-program binding are separate.
-/

namespace Ix.Ixby.AiurBackend.ObjectsUnique

-- Keep diagnostic structural equality and the proved semantic BEq laws local.
deriving instance DecidableEq for Aiur.Bytecode.Op
deriving instance ReflBEq, LawfulBEq for Ix.Ixby.CtorId

public section
@[expose] section

open Aiur Aiur.Bytecode Aiur.Bytecode.Eval
open Ix.Ixby
open ObjectsMemory ObjectsRefinement ObjectsTable ObjectsParser ObjectsIdentity ObjectsEquality

structure RawDecl where
  id : RawId
  fields : G

def RawDecl.cell (decl : RawDecl) (tail : G) : Array G :=
  #[0] ++ decl.id.flat ++ #[decl.fields, tail]

/-- A finite concrete declaration spine with the exact padded terminal Nil.
Payload range/semantic validity is deliberately separate from raw traversal. -/
inductive DeclSpine (memory : RawMemory) : G → List RawDecl → Prop where
  | nil {pointer : G} (loaded : memory 13 pointer.n = some tableNil) :
      DeclSpine memory pointer []
  | cons {pointer tail : G} {decl : RawDecl} {decls : List RawDecl}
      (loaded : memory 13 pointer.n = some (decl.cell tail))
      (rest : DeclSpine memory tail decls) : DeclSpine memory pointer (decl :: decls)

def uniqueZero (selector : Nat) : Aiur.Bytecode.Block := {
  ops := #[.load 13 10, .const 1, .const 1,
    .assertEq #[12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]
      #[25, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26] (some "IxBy extra constructors")],
  ctrl := .return selector #[] }

def compareArgs : Array Nat := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]
def recurseArgs : Array Nat := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 24, 28]

def stepAdvanceOps : Array Aiur.Bytecode.Op :=
  #[.const 0, .assertEq #[25] #[26] (some "IxBy duplicate constructor ID"), .const 1, .sub 11 27]

def uniqueStep (comparer self selector : Nat) : Aiur.Bytecode.Block := {
  ops := #[.call comparer compareArgs 1 false, .const 0,
    .assertEq #[25] #[26] (some "IxBy duplicate constructor ID"),
    .const 1, .sub 11 27, .call self recurseArgs 0 false],
  ctrl := .return selector #[] }

theorem unique_step_ops (comparer self selector : Nat) :
    (uniqueStep comparer self selector).ops =
      #[.call comparer compareArgs 1 false] ++ (stepAdvanceOps ++ #[.call self recurseArgs 0 false]) := by
  simp [uniqueStep, stepAdvanceOps]

def uniqueTagless (step : Aiur.Bytecode.Block) : Aiur.Bytecode.Block :=
  ⟨#[], .match 13 #[] (some step)⟩
def uniqueNonzero (step : Aiur.Bytecode.Block) : Aiur.Bytecode.Block :=
  ⟨#[.load 13 10], .match 12 #[(0, uniqueTagless step)] none⟩
def uniqueDispatch (zeroSelector : Nat) (step : Aiur.Bytecode.Block) : Aiur.Bytecode.Block :=
  ⟨#[], .match 11 #[(0, uniqueZero zeroSelector)] (some (uniqueNonzero step))⟩
def uniqueBody (comparer self zeroSelector consSelector : Nat) : Aiur.Bytecode.Block :=
  uniqueDispatch zeroSelector (uniqueStep comparer self consSelector)

def checkReturnBlock (body : Aiur.Bytecode.Block) (ops : Array Aiur.Bytecode.Op)
    (selector : Nat) (outputs : Array Nat) : Bool :=
  match body.ctrl with
  | .return found outs => decide (body.ops = ops ∧ found = selector ∧ outs = outputs)
  | _ => false

theorem return_block_checked (body : Aiur.Bytecode.Block) (ops : Array Aiur.Bytecode.Op)
    (selector : Nat) (outputs : Array Nat)
    (checked : checkReturnBlock body ops selector outputs = true) :
    body = ⟨ops, .return selector outputs⟩ := by
  unfold checkReturnBlock at checked
  split at checked
  · rename_i found outs ctrl
    obtain ⟨opsEq, selectorEq, outsEq⟩ := of_decide_eq_true checked
    cases body; simp_all
  · simp at checked

/-- All three match layers, both terminal blocks, and both call indices are
checked. The tagless-constructor match is part of the emitted shape. -/
def checkUnique (f : Aiur.Bytecode.Function) (comparer self zeroSelector consSelector : Nat) : Bool :=
  match f.body.ctrl with
  | .match count zeros (some nonzero) =>
    match zeros.toList, nonzero.ctrl with
    | [(zeroTag, zero)], .match cellTag consCases none =>
      match consCases.toList with
      | [(consTag, tagless)] =>
        match tagless.ctrl with
        | .match dummy noCases (some step) =>
          decide (f.layout.inputSize = 12 ∧ f.body.ops = #[] ∧ count = 11 ∧ zeroTag = 0 ∧
            nonzero.ops = #[.load 13 10] ∧ cellTag = 12 ∧ consTag = 0 ∧ tagless.ops = #[] ∧
            dummy = 13 ∧ noCases = #[]) &&
          checkReturnBlock zero (uniqueZero zeroSelector).ops zeroSelector #[] &&
          checkReturnBlock step (uniqueStep comparer self consSelector).ops consSelector #[]
        | _ => false
      | _ => false
    | _, _ => false
  | _ => false

theorem unique_checked (f : Aiur.Bytecode.Function) (comparer self zeroSelector consSelector : Nat)
    (checked : checkUnique f comparer self zeroSelector consSelector = true) :
    f.layout.inputSize = 12 ∧ f.body = uniqueBody comparer self zeroSelector consSelector := by
  unfold checkUnique at checked
  split at checked
  · rename_i count zeros nonzero ctrl
    split at checked
    · rename_i zeroTag zero cellTag consCases zerosList nonzeroCtrl
      split at checked
      · rename_i consTag tagless consList
        split at checked
        · rename_i dummy noCases step taglessCtrl
          simp only [Bool.and_eq_true, decide_eq_true_eq] at checked
          obtain ⟨⟨⟨input, ops, countEq, zeroEq, nonzeroOps, cellEq, consEq, taglessOps, dummyEq, empty⟩,
            zeroChecked⟩, stepChecked⟩ := checked
          have zeroBody := return_block_checked _ _ _ _ zeroChecked
          have stepBody := return_block_checked _ _ _ _ stepChecked
          have zeroArray : zeros = #[(zeroTag, zero)] := Array.toList_inj.mp zerosList
          have consArray : consCases = #[(consTag, tagless)] := Array.toList_inj.mp consList
          have taglessBody : tagless = uniqueTagless (uniqueStep comparer self consSelector) := by
            cases tagless; simp_all [uniqueTagless, uniqueStep]
          have nonzeroBody : nonzero = uniqueNonzero (uniqueStep comparer self consSelector) := by
            cases nonzero; simp_all [uniqueNonzero]
          refine ⟨input, ?_⟩
          cases f with
          | mk b layout entry constrained => cases b; simp_all [uniqueBody, uniqueDispatch, uniqueZero]
        · simp at checked
      · simp at checked
    · simp at checked
  · simp at checked

theorem raw_load (st : EvalState) (width : Nat) (pointer : G) (flat : Array G)
    (loaded : bytecodeMemory st width pointer.n = some flat) :
    memLoad st width pointer.n = .ok flat := by
  unfold bytecodeMemory at loaded
  cases actual : memLoad st width pointer.n with
  | error error => simp [actual] at loaded
  | ok values => simpa [actual] using loaded

theorem unique_nil_eval (t : Bytecode.Toplevel) (fuel selector : Nat) (step : Aiur.Bytecode.Block)
    (st : EvalState) (needle : RawId) (pointer : G)
    (loaded : memLoad st 13 pointer.n = .ok tableNil) :
    ∃ after, evalBlock t fuel (uniqueDispatch selector step) { st with map := needle.flat ++ #[pointer, 0] } =
      .error (.earlyReturn #[] after) ∧ after.memory = st.memory ∧ after.ioBuffer = st.ioBuffer := by
  simp [uniqueDispatch, uniqueZero, RawId.flat, tableNil, evalBlock, run_ops_list,
    Aiur.Bytecode.Eval.evalOp, readIdx, readIdxs, evalCtrl, evalMatchArm, loaded,
    pushMap, appendMap, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem unique_cons_enter (t : Bytecode.Toplevel) (fuel selector : Nat) (step : Aiur.Bytecode.Block)
    (st : EvalState) (needle : RawId) (decl : RawDecl) (pointer tail count : G)
    (nonzero : count ≠ 0) (loaded : memLoad st 13 pointer.n = .ok (decl.cell tail)) :
    evalBlock t fuel (uniqueDispatch selector step) { st with map := needle.flat ++ #[pointer, count] } =
      evalBlock t fuel step { st with map := (needle.flat ++ #[pointer, count]) ++ decl.cell tail } := by
  have nonzeroVal : (0 : G).val ≠ count.val := fun equal => nonzero (Subtype.ext equal.symm)
  simp [uniqueDispatch, uniqueNonzero, uniqueTagless, RawDecl.cell, RawId.flat, evalBlock, run_ops_list,
    Aiur.Bytecode.Eval.evalOp, readIdx, evalCtrl, evalMatchArm, evalDefaultBlock, loaded, nonzeroVal,
    appendMap, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem field_succ_nonzero (n : Nat) (bounded : n + 1 < goldilocksModulus) : G.ofNat (n + 1) ≠ 0 := by
  intro zero
  have equal := congrArg G.n zero
  rw [field_of_nat_exact _ bounded] at equal
  change n + 1 = 0 at equal
  omega

theorem field_pred (n : Nat) (bounded : n + 1 < goldilocksModulus) :
    G.ofNat (n + 1) - 1 = G.ofNat n := by
  apply field_n_injective
  change (G.ofNat ((G.ofNat (n + 1)).n + goldilocksModulus - 1)).n = (G.ofNat n).n
  rw [field_of_nat_exact _ bounded, field_of_nat_mod, field_of_nat_exact _ (by omega)]
  have arithmetic : n + 1 + goldilocksModulus - 1 = n + goldilocksModulus := by omega
  rw [arithmetic, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- Lift an empty-return/error body contract through the evaluator's actual
Call boundary. Caller registers are restored, and no output is appended. -/
theorem call_empty_result (t : Bytecode.Toplevel) (fuel callee : Nat) (st : EvalState)
    (f : Aiur.Bytecode.Function) (function : t.functions[callee]? = some f)
    (args : Array Nat) (values : Array G) (arguments : readIdxs st args = .ok values)
    (arity : f.layout.inputSize = values.size) (rejected : Prop) [Decidable rejected]
    (after : EvalState)
    (executed : evalBlock t fuel f.body { st with map := values } =
      if rejected then .error .assertFailed else .error (.earlyReturn #[] after))
    (memory : after.memory = st.memory) (io : after.ioBuffer = st.ioBuffer) (unconstrained : Bool) :
    Aiur.Bytecode.Eval.evalOp t (fuel + 1) (.call callee args 0 unconstrained) st =
      if rejected then .error .assertFailed else .ok st := by
  obtain ⟨bound, found⟩ := Array.getElem?_eq_some_iff.mp function
  by_cases reject : rejected <;>
    simp [Aiur.Bytecode.Eval.evalOp, arguments, bound, found, arity, executed, reject,
      memory, io, appendMap, setIoBuffer, Bind.bind, Except.bind, Pure.pure, Except.pure]

def stepState (st : EvalState) (needle : RawId) (decl : RawDecl) (pointer tail count : G) : EvalState :=
  { st with map := (needle.flat ++ #[pointer, count]) ++ decl.cell tail }

def recursiveState (st : EvalState) (needle : RawId) (decl : RawDecl) (pointer tail count : G) : EvalState :=
  { st with map := ((needle.flat ++ #[pointer, count]) ++ decl.cell tail) ++ #[0, 0, 1, count - 1] }

@[simp] theorem bytecode_memory_map (st : EvalState) (map : Array G) :
    bytecodeMemory { st with map } = bytecodeMemory st := rfl

theorem read_idxs_of_all₂ (st : EvalState) (indices : List Nat) (values : List G)
    (found : All₂ (fun idx value => st.map[idx]? = some value) indices values) :
    readIdxs st indices.toArray = .ok values.toArray := by
  induction found with
  | nil => simp [readIdxs, Pure.pure, Except.pure]
  | @cons idx value indices values head rest ih =>
    have left : (idx :: indices).toArray = #[idx] ++ indices.toArray := (List.append_toArray [idx] indices).symm
    have right : (value :: values).toArray = #[value] ++ values.toArray := (List.append_toArray [value] values).symm
    rw [left, right, read_idxs_append, read_idxs_single _ _ _ head, Except.bind, ih]
    rfl

theorem step_compare_arguments (st : EvalState) (needle : RawId) (decl : RawDecl) (pointer tail count : G) :
    readIdxs (stepState st needle decl pointer tail count) compareArgs = .ok (needle.flat ++ decl.id.flat) := by
  have found : All₂ (fun idx value => (stepState st needle decl pointer tail count).map[idx]? = some value)
      compareArgs.toList (needle.flat ++ decl.id.flat).toList := by
    simp only [compareArgs, RawId.flat, Array.toList_append]
    repeat' first | apply All₂.cons | exact All₂.nil
    all_goals simp [stepState, RawDecl.cell, RawId.flat]
  simpa only [Array.toArray_toList] using read_idxs_of_all₂ _ _ _ found

theorem step_recurse_arguments (st : EvalState) (needle : RawId) (decl : RawDecl) (pointer tail count : G) :
    readIdxs (recursiveState st needle decl pointer tail count) recurseArgs =
      .ok (needle.flat ++ #[tail, count - 1]) := by
  have found : All₂ (fun idx value => (recursiveState st needle decl pointer tail count).map[idx]? = some value)
      recurseArgs.toList (needle.flat ++ #[tail, count - 1]).toList := by
    simp only [recurseArgs, RawId.flat, Array.toList_append]
    repeat' first | apply All₂.cons | exact All₂.nil
    all_goals simp [recursiveState, RawDecl.cell, RawId.flat]
  simpa only [Array.toArray_toList] using read_idxs_of_all₂ _ _ _ found

private theorem advance_zero (t : Bytecode.Toplevel) (fuel : Nat) (st : EvalState) (count : G)
    (size : st.map.size = 26) (compared : st.map[25]? = some 0) (counter : st.map[11]? = some count) :
    runOps t fuel stepAdvanceOps st 0 = .ok { st with map := st.map ++ #[0, 1, count - 1] } := by
  obtain ⟨_, comparedValue⟩ := Array.getElem?_eq_some_iff.mp compared
  obtain ⟨_, counterValue⟩ := Array.getElem?_eq_some_iff.mp counter
  simp +arith [stepAdvanceOps, run_ops_list, Aiur.Bytecode.Eval.evalOp, readIdxs, readIdx,
    size, comparedValue, counterValue, Array.getElem?_push, Array.getElem_push,
    pushMap, Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact (Array.append_push (xs := st.map) (ys := #[0, 1]) (a := count - 1)).symm.trans
    (congrArg (·.push (count - 1)) (Array.append_push (xs := st.map) (ys := #[0]) (a := 1))).symm

private theorem advance_one (t : Bytecode.Toplevel) (fuel : Nat) (st : EvalState)
    (size : st.map.size = 26) (compared : st.map[25]? = some 1) :
    runOps t fuel stepAdvanceOps st 0 = .error .assertFailed := by
  have unequal : (1 : G).val ≠ (0 : G).val := by decide
  obtain ⟨_, comparedValue⟩ := Array.getElem?_eq_some_iff.mp compared
  simp +arith [stepAdvanceOps, run_ops_list, Aiur.Bytecode.Eval.evalOp, readIdxs, readIdx,
    size, comparedValue, unequal, Array.getElem?_push, pushMap, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem unique_step_duplicate (t : Bytecode.Toplevel) (fuel comparer self compareSelector consSelector : Nat)
    (st : EvalState) (needle : RawId) (decl : RawDecl) (pointer tail count : G)
    (cmp : Aiur.Bytecode.Function) (function : t.functions[comparer]? = some cmp)
    (checked : checkIdEq cmp compareSelector = true) (duplicate : needle = decl.id) :
    evalBlock t (fuel + 1) (uniqueStep comparer self consSelector) (stepState st needle decl pointer tail count) =
      .error .assertFailed := by
  have compared := id_eq_call t fuel compareSelector comparer (stepState st needle decl pointer tail count)
    cmp function checked needle decl.id compareArgs (step_compare_arguments st needle decl pointer tail count) false
  have comparedOps : runOps t (fuel + 1) #[.call comparer compareArgs 1 false]
      (stepState st needle decl pointer tail count) 0 =
      .ok { (stepState st needle decl pointer tail count) with
        map := (stepState st needle decl pointer tail count).map.push 1 } := by
    simp only [if_pos duplicate] at compared
    simp [run_ops_list, compared, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have rejected : runOps t (fuel + 1) stepAdvanceOps
      { (stepState st needle decl pointer tail count) with
        map := (stepState st needle decl pointer tail count).map.push 1 } 0 = .error .assertFailed := by
    apply advance_one t (fuel + 1)
    · simp [stepState, RawDecl.cell, RawId.flat]
    · simp [stepState, RawDecl.cell, RawId.flat]
  simp only [evalBlock, unique_step_ops, run_ops_append, comparedOps, Except.bind, rejected]

theorem unique_step_fresh (t : Bytecode.Toplevel) (fuel comparer self compareSelector consSelector : Nat)
    (st : EvalState) (needle : RawId) (decl : RawDecl) (pointer tail count : G)
    (cmp : Aiur.Bytecode.Function) (function : t.functions[comparer]? = some cmp)
    (checked : checkIdEq cmp compareSelector = true) (fresh : needle ≠ decl.id)
    (rejected : Prop) [Decidable rejected]
    (recursive : Aiur.Bytecode.Eval.evalOp t (fuel + 1) (.call self recurseArgs 0 false)
      (recursiveState st needle decl pointer tail count) =
        if rejected then .error .assertFailed else .ok (recursiveState st needle decl pointer tail count)) :
    evalBlock t (fuel + 1) (uniqueStep comparer self consSelector) (stepState st needle decl pointer tail count) =
      if rejected then .error .assertFailed else
        .error (.earlyReturn #[] (recursiveState st needle decl pointer tail count)) := by
  have compared := id_eq_call t fuel compareSelector comparer (stepState st needle decl pointer tail count)
    cmp function checked needle decl.id compareArgs (step_compare_arguments st needle decl pointer tail count) false
  have comparedOps : runOps t (fuel + 1) #[.call comparer compareArgs 1 false]
      (stepState st needle decl pointer tail count) 0 =
      .ok { (stepState st needle decl pointer tail count) with
        map := (stepState st needle decl pointer tail count).map.push 0 } := by
    simp [run_ops_list, compared, fresh]
  have advanced : runOps t (fuel + 1) stepAdvanceOps
      { (stepState st needle decl pointer tail count) with
        map := (stepState st needle decl pointer tail count).map.push 0 } 0 =
      .ok (recursiveState st needle decl pointer tail count) := by
    have moved := advance_zero t (fuel + 1)
      { (stepState st needle decl pointer tail count) with
        map := (stepState st needle decl pointer tail count).map.push 0 } count
      (by simp [stepState, RawDecl.cell, RawId.flat])
      (by simp [stepState, RawDecl.cell, RawId.flat])
      (by simp [stepState, RawDecl.cell, RawId.flat])
    simpa [recursiveState, stepState, Array.append_assoc] using moved
  simp only [evalBlock, unique_step_ops, run_ops_append, comparedOps, Except.bind, advanced]
  by_cases reject : rejected <;>
    simp [run_ops_list, recursive, reject, uniqueStep, evalCtrl, readIdxs, Bind.bind, Except.bind, Pure.pure, Except.pure]

set_option maxHeartbeats 1000000 in
/-- Exact-length finite traversal with sufficient call fuel. It returns no
values exactly for a fresh raw ID; any duplicate produces `assertFailed`.
The successful state has identical memory and I/O. No limb range is assumed. -/
theorem unique_spine_eval (t : Bytecode.Toplevel) (fuel comparer self compareSelector zeroSelector consSelector : Nat)
    (cmp unique : Aiur.Bytecode.Function)
    (compareFunction : t.functions[comparer]? = some cmp) (uniqueFunction : t.functions[self]? = some unique)
    (compareChecked : checkIdEq cmp compareSelector = true)
    (uniqueChecked : checkUnique unique comparer self zeroSelector consSelector = true)
    (st : EvalState) (needle : RawId) (pointer : G) (decls : List RawDecl)
    (spine : DeclSpine (bytecodeMemory st) pointer decls) (bounded : decls.length < goldilocksModulus) :
    ∃ after, evalBlock t (fuel + decls.length + 1) unique.body
        { st with map := needle.flat ++ #[pointer, G.ofNat decls.length] } =
      (if needle ∈ decls.map RawDecl.id then .error .assertFailed else .error (.earlyReturn #[] after)) ∧
      after.memory = st.memory ∧ after.ioBuffer = st.ioBuffer := by
  obtain ⟨input, body⟩ := unique_checked unique comparer self zeroSelector consSelector uniqueChecked
  induction decls generalizing st pointer with
  | nil =>
    cases spine with
    | nil loaded =>
      obtain ⟨after, executed, memory, io⟩ := unique_nil_eval t (fuel + 1) zeroSelector
        (uniqueStep comparer self consSelector) st needle pointer (raw_load st 13 pointer tableNil loaded)
      exact ⟨after, by simpa [body, uniqueBody, show G.ofNat 0 = (0 : G) from rfl] using executed, memory, io⟩
  | cons decl decls ih =>
    cases spine with
    | @cons _ tail _ _ loaded rest =>
      have entered := unique_cons_enter t (fuel + (decls.length + 1) + 1) zeroSelector
        (uniqueStep comparer self consSelector) st needle decl pointer tail (G.ofNat (decls.length + 1))
        (field_succ_nonzero decls.length bounded) (raw_load st 13 pointer (decl.cell tail) loaded)
      simp only [List.length_cons]
      rw [body, uniqueBody, entered]
      change ∃ after, evalBlock t ((fuel + decls.length + 1) + 1) (uniqueStep comparer self consSelector)
          (stepState st needle decl pointer tail (G.ofNat (decls.length + 1))) = _ ∧ _ ∧ _
      by_cases duplicate : needle = decl.id
      · refine ⟨st, ?_, rfl, rfl⟩
        rw [unique_step_duplicate t (fuel + decls.length + 1) comparer self compareSelector consSelector
          st needle decl pointer tail _ cmp compareFunction compareChecked duplicate]
        simp [duplicate]
      · let caller := recursiveState st needle decl pointer tail (G.ofNat (decls.length + 1))
        have tailBound : decls.length < goldilocksModulus := by
          simp only [List.length_cons] at bounded
          omega
        have tailSpine : DeclSpine (bytecodeMemory caller) tail decls := by
          simpa only [caller, recursiveState, bytecode_memory_map] using rest
        obtain ⟨after, executed, memory, io⟩ := ih caller tail tailSpine tailBound
        have arguments := step_recurse_arguments st needle decl pointer tail (G.ofNat (decls.length + 1))
        rw [field_pred decls.length bounded] at arguments
        have recursive := call_empty_result t (fuel + decls.length + 1) self caller unique uniqueFunction
          recurseArgs (needle.flat ++ #[tail, G.ofNat decls.length]) arguments
          (by simpa only [RawId.flat, Array.size_append, List.size_toArray, List.length_cons,
            List.length_nil, Nat.add_zero] using input)
          (needle ∈ decls.map RawDecl.id) after executed memory io false
        refine ⟨caller, ?_, ?_, ?_⟩
        · have result := unique_step_fresh t (fuel + decls.length + 1) comparer self compareSelector consSelector
            st needle decl pointer tail _ cmp compareFunction compareChecked duplicate
            (needle ∈ decls.map RawDecl.id) recursive
          simpa only [List.map_cons, List.mem_cons, duplicate, false_or] using result
        · simp only [caller, recursiveState]
        · simp only [caller, recursiveState]

def DeclDecodes (raw : RawDecl) (decl : CtorDecl) : Prop :=
  raw.id.decode = some decl.id ∧ raw.fields.n = decl.fields

theorem decode_decl_cons (flat : Array G) (decl : CtorDecl) (tailNat : Nat)
    (decoded : decodeDeclCell flat = some (.cons decl tailNat)) :
    ∃ raw : RawDecl, ∃ tail : G, flat = raw.cell tail ∧ DeclDecodes raw decl ∧ tail.n = tailNat := by
  unfold decodeDeclCell at decoded
  split at decoded
  · rename_i tag a b c d e f g h member ctorTag fields tail shape
    split at decoded
    · rename_i tagValue
      obtain ⟨id, idDecoded, decoded⟩ := Option.bind_eq_some_iff.mp decoded
      split at decoded
      · simp at decoded
      · have equal := Option.some.inj decoded
        cases equal
        have tagEq : tag = (0 : G) := field_n_injective tagValue
        subst tag
        refine ⟨⟨⟨a, b, c, d, e, f, g, h, member, ctorTag⟩, fields⟩, tail, ?_, ⟨idDecoded, rfl⟩, rfl⟩
        simpa [RawDecl.cell, RawId.flat] using Array.toList_inj.mp shape
    · split at decoded <;> simp at decoded
    · simp at decoded
  · simp at decoded

theorem decode_decl_nil (flat : Array G) (decoded : decodeDeclCell flat = some .nil) : flat = tableNil := by
  unfold decodeDeclCell at decoded
  split at decoded
  · rename_i tag a b c d e f g h member ctorTag fields tail shape
    split at decoded
    · obtain ⟨id, _, decoded⟩ := Option.bind_eq_some_iff.mp decoded
      split at decoded <;> simp at decoded
    · rename_i tagValue
      split at decoded
      · rename_i allOnes
        have padding : a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 ∧ e = 1 ∧ f = 1 ∧ g = 1 ∧ h = 1 ∧
            member = 1 ∧ ctorTag = 1 ∧ fields = 1 ∧ tail = 1 := by
          simpa only [List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true, beq_iff_eq] using allOnes
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := padding
        have tagEq : tag = (1 : G) := field_n_injective tagValue
        subst tag
        exact Array.toList_inj.mp shape
      · simp at decoded
    · simp at decoded
  · simp at decoded

/-- Successful existing table decoding supplies the raw finite spine, with
each complete semantic ID tied to the actual loaded limbs. -/
theorem read_declarations_spine (memory : RawMemory) (count : Nat) (pointer : G) (decls : List CtorDecl)
    (read : readDeclarations memory count pointer.n = some decls) :
    ∃ raws, DeclSpine memory pointer raws ∧ All₂ DeclDecodes raws decls := by
  induction count generalizing pointer decls with
  | zero =>
    cases loaded : declarationHeap memory pointer.n with
    | none => simp [readDeclarations, loaded] at read
    | some cell =>
      cases cell with
      | cons _ _ => simp [readDeclarations, loaded] at read
      | nil =>
        have empty : decls = [] := by simpa [readDeclarations, loaded] using read.symm
        subst decls
        obtain ⟨flat, raw, decoded⟩ := Option.bind_eq_some_iff.mp loaded
        rw [decode_decl_nil flat decoded] at raw
        exact ⟨[], .nil raw, .nil⟩
  | succ count ih =>
    cases loaded : declarationHeap memory pointer.n with
    | none => simp [readDeclarations, loaded] at read
    | some cell =>
      cases cell with
      | nil => simp [readDeclarations, loaded] at read
      | cons decl tailNat =>
        cases tailRead : readDeclarations memory count tailNat with
        | none => simp [readDeclarations, loaded, tailRead] at read
        | some tailDecls =>
          have equal : decls = decl :: tailDecls := by simpa [readDeclarations, loaded, tailRead] using read.symm
          subst decls
          obtain ⟨flat, raw, decoded⟩ := Option.bind_eq_some_iff.mp loaded
          obtain ⟨head, tail, flatEq, decoded, tailEq⟩ := decode_decl_cons flat decl tailNat decoded
          obtain ⟨raws, spine, related⟩ := ih tail tailDecls (by simpa only [tailEq] using tailRead)
          exact ⟨head :: raws, .cons (by simpa only [flatEq] using raw) spine, .cons decoded related⟩

theorem semantic_membership (needle : RawId) (id : CtorId) (decoded : needle.decode = some id)
    (raws : List RawDecl) (decls : List CtorDecl) (related : All₂ DeclDecodes raws decls) :
    needle ∈ raws.map RawDecl.id ↔ id ∈ decls.map CtorDecl.id := by
  induction related with
  | nil => simp
  | @cons raw decl raws decls head rest ih =>
    simp only [List.map_cons, List.mem_cons, raw_semantic_eq needle raw.id id decl.id decoded head.1, ih]

/-- Semantic freshness/duplicate rejection for a table accepted by the existing
decoder. Its constructor limit supplies the no-wrap counter bound.
The query's freshness is a conclusion, not a premise. -/
theorem checked_unique_table (t : Bytecode.Toplevel) (fuel comparer self compareSelector zeroSelector consSelector : Nat)
    (cmp unique : Aiur.Bytecode.Function)
    (compareFunction : t.functions[comparer]? = some cmp) (uniqueFunction : t.functions[self]? = some unique)
    (compareChecked : checkIdEq cmp compareSelector = true)
    (uniqueChecked : checkUnique unique comparer self zeroSelector consSelector = true)
    (st : EvalState) (needle : RawId) (id : CtorId) (decoded : needle.decode = some id)
    (pointer : G) (count : Nat) (table : Array CtorDecl)
    (read : readTable (bytecodeMemory st) pointer.n count = some table) :
    ∃ after, evalBlock t (fuel + count + 1) unique.body
        { st with map := needle.flat ++ #[pointer, G.ofNat count] } =
      (if id ∈ table.toList.map CtorDecl.id then .error .assertFailed else .error (.earlyReturn #[] after)) ∧
      after.memory = st.memory ∧ after.ioBuffer = st.ioBuffer := by
  obtain ⟨declsRead, size, _, capacity⟩ := read_table_sound read
  obtain ⟨raws, spine, related⟩ := read_declarations_spine _ count pointer table.toList declsRead
  have length : raws.length = count := (all₂_length related).trans (by simpa using size)
  obtain ⟨after, executed, memory, io⟩ := unique_spine_eval t fuel comparer self compareSelector zeroSelector consSelector
    cmp unique compareFunction uniqueFunction compareChecked uniqueChecked st needle pointer raws spine (by
      rw [length]
      change count ≤ 16 at capacity
      change count < 18446744069414584321
      omega)
  exact ⟨after, by simpa only [length, semantic_membership needle id decoded raws table.toList related] using executed,
    memory, io⟩

/-- At the public Call boundary, freshness is an exact no-op on caller state;
a duplicate is an assertion failure. Both constraint flags have the same
Lean evaluator behavior, without asserting any unconstrained AIR relation. -/
theorem checked_unique_call (t : Bytecode.Toplevel) (fuel comparer self compareSelector zeroSelector consSelector : Nat)
    (cmp unique : Aiur.Bytecode.Function)
    (compareFunction : t.functions[comparer]? = some cmp) (uniqueFunction : t.functions[self]? = some unique)
    (compareChecked : checkIdEq cmp compareSelector = true)
    (uniqueChecked : checkUnique unique comparer self zeroSelector consSelector = true)
    (st : EvalState) (needle : RawId) (id : CtorId) (decoded : needle.decode = some id)
    (pointer : G) (count : Nat) (table : Array CtorDecl)
    (read : readTable (bytecodeMemory st) pointer.n count = some table)
    (args : Array Nat) (arguments : readIdxs st args = .ok (needle.flat ++ #[pointer, G.ofNat count]))
    (unconstrained : Bool) :
    Aiur.Bytecode.Eval.evalOp t (fuel + count + 2) (.call self args 0 unconstrained) st =
      if id ∈ table.toList.map CtorDecl.id then .error .assertFailed else .ok st := by
  obtain ⟨after, executed, memory, io⟩ := checked_unique_table t fuel comparer self compareSelector zeroSelector consSelector
    cmp unique compareFunction uniqueFunction compareChecked uniqueChecked st needle id decoded pointer count table read
  have arity : unique.layout.inputSize = (needle.flat ++ #[pointer, G.ofNat count]).size := by
    simpa [RawId.flat] using (unique_checked unique comparer self zeroSelector consSelector uniqueChecked).1
  exact call_empty_result t (fuel + count + 1) self st unique uniqueFunction args _ arguments arity
    (id ∈ table.toList.map CtorDecl.id) after executed memory io unconstrained

end
end
end Ix.Ixby.AiurBackend.ObjectsUnique
