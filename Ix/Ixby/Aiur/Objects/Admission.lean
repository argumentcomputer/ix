module
public import Ix.Ixby.Aiur.Objects.Declarations
import all Ix.Aiur.Goldilocks
import all Ix.Aiur.Semantics.BytecodeFfi

/-! The actual advice loader establishes the parser's genuine-byte premise.

Certificates cover both branches of `ib_read_advice` and the complete `ib_load`
body. Metadata/address ranges and finite readable advice remain explicit;
neither arbitrary host metadata nor authenticated whole-program admission is
assumed to have been validated. This is a Lean evaluator theorem, not AIR.
-/

namespace Ix.Ixby.AiurBackend.Objects.Admission

deriving instance DecidableEq for Aiur.Bytecode.Op

public section
@[expose] section

open Aiur Aiur.Bytecode Aiur.Bytecode.Eval Ix.Ixby
open Objects.Refinement Objects.Memory Objects.Store Objects.Table Objects.Parser
open Objects.Identity Objects.Equality Objects.Unique Objects.Declarations

/-- Finite raw, field-valued advice at successive natural-number addresses.
No byte-range assumption is built into this relation. The empty slice reads
nothing, including at the end of an arena. -/
inductive AdviceSlice (io : IOBuffer) (channel : G) : Nat → List G → Prop where
  | nil (start : Nat) : AdviceSlice io channel start []
  | cons {start : Nat} {value : G} {values : List G}
      (head : (io.data.getD channel #[])[start]? = some value)
      (tail : AdviceSlice io channel (start + 1) values) :
      AdviceSlice io channel start (value :: values)

def ByteFields (values : List G) : Prop := ∀ value ∈ values, value.n < 256
instance (values : List G) : Decidable (ByteFields values) := by
  unfold ByteFields
  infer_instance

theorem byte_fields_cons (value : G) (values : List G) :
    ByteFields (value :: values) ↔ value.n < 256 ∧ ByteFields values := by
  simp only [ByteFields, List.mem_cons, forall_eq_or_imp]

def adviceBytes (values : List G) : List UInt8 := values.map (fun value => value.val.toUInt8)

/-- The exact content-deduplicating store order: Nil, then reverse Cons order. -/
def storeAdvice (st : EvalState) : List G → EvalState × G
  | [] => let stored := memStore st #[1, 1, 1]; (stored.1, G.ofNat stored.2)
  | value :: values =>
    let tail := storeAdvice st values
    let stored := memStore tail.1 #[0, value, tail.2]
    (stored.1, G.ofNat stored.2)

theorem store_advice_map (st : EvalState) (map : Array G) (values : List G) :
    storeAdvice { st with map } values =
      ({ (storeAdvice st values).1 with map }, (storeAdvice st values).2) := by
  induction values with
  | nil => simp [storeAdvice, mem_store_map]
  | cons value values ih => simp [storeAdvice, ih, mem_store_map]

theorem store_advice_io (st : EvalState) (values : List G) :
    (storeAdvice st values).1.ioBuffer = st.ioBuffer := by
  induction values with
  | nil => exact mem_store_io st _
  | cons value values ih => exact (mem_store_io _ _).trans ih

theorem store_advice_size (st : EvalState) (values : List G) :
    bucketSize (storeAdvice st values).1 3 ≤ bucketSize st 3 + values.length + 1 := by
  induction values with
  | nil => exact (mem_store_bounds st #[1, 1, 1]).2
  | cons value values ih =>
    have next := (mem_store_bounds (storeAdvice st values).1 #[0, value, (storeAdvice st values).2]).2
    change bucketSize (storeAdvice st (value :: values)).1 3 ≤ bucketSize (storeAdvice st values).1 3 + 1 at next
    simp only [List.length_cons]
    omega

theorem store_advice_other_bucket (st : EvalState) (values : List G) (width : Nat)
    (different : 3 ≠ width) :
    bucketSize (storeAdvice st values).1 width = bucketSize st width := by
  induction values with
  | nil => exact mem_store_other_bucket st _ width different
  | cons value values ih =>
    exact (mem_store_other_bucket (storeAdvice st values).1 #[0, value, (storeAdvice st values).2] width different).trans ih

theorem store_advice_preserves (st : EvalState) (values : List G)
    {width pointer : Nat} {flat : Array G} (read : memLoad st width pointer = .ok flat) :
    memLoad (storeAdvice st values).1 width pointer = .ok flat := by
  induction values with
  | nil => exact mem_store_preserves st _ read
  | cons value values ih => exact mem_store_preserves _ _ ih

theorem store_advice_prefix (st : EvalState) (values : List G)
    {pointer finish : G} {bytes : List UInt8}
    (read : BytePrefix (bytecodeMemory st) pointer bytes finish) :
    BytePrefix (bytecodeMemory (storeAdvice st values).1) pointer bytes finish := by
  induction values with
  | nil => exact byte_prefix_store st _ read
  | cons value values ih => exact byte_prefix_store _ _ ih

theorem field_byte_exact (value : G) (range : value.n < 256) :
    G.ofUInt8 value.val.toUInt8 = value := by
  apply field_n_injective
  simp only [byte_field_exact, UInt64.toNat_toUInt8]
  exact Nat.mod_eq_of_lt range

/-- A complete byte stream includes its actual Nil cell, not merely an
arbitrary suffix pointer. -/
def ByteStream (memory : RawMemory) (pointer : G) (bytes : List UInt8) : Prop :=
  ∃ finish, BytePrefix memory pointer bytes finish ∧ memory 3 finish.n = some #[1, 1, 1]

theorem store_advice_stream (st : EvalState) (values : List G) (valid : ByteFields values)
    (space : bucketSize st 3 + values.length + 1 ≤ goldilocksModulus) :
    ByteStream (bytecodeMemory (storeAdvice st values).1) (storeAdvice st values).2 (adviceBytes values) := by
  induction values with
  | nil =>
    have bound := (mem_store_bounds st #[1, 1, 1]).1
    have pointerBound : (memStore st #[1, 1, 1]).2 < goldilocksModulus := by
      change (memStore st #[1, 1, 1]).2 ≤ bucketSize st 3 at bound
      simp only [List.length_nil] at space
      omega
    have exactRead := stored_field_pointer st #[1, 1, 1] pointerBound
    refine ⟨_, .nil _, ?_⟩
    change memLoad (memStore st #[1, 1, 1]).1 3 (G.ofNat (memStore st #[1, 1, 1]).2).n = .ok #[1, 1, 1] at exactRead
    simp only [bytecodeMemory, storeAdvice]
    rw [exactRead]
  | cons value values ih =>
    obtain ⟨range, validTail⟩ := (byte_fields_cons value values).mp valid
    obtain ⟨finish, bytesRead, terminal⟩ := ih validTail (by simp only [List.length_cons] at space; omega)
    have size := store_advice_size st values
    have bound := (mem_store_bounds (storeAdvice st values).1 #[0, value, (storeAdvice st values).2]).1
    change (memStore (storeAdvice st values).1 #[0, value, (storeAdvice st values).2]).2 ≤
      bucketSize (storeAdvice st values).1 3 at bound
    have pointerBound : (memStore (storeAdvice st values).1 #[0, value, (storeAdvice st values).2]).2 < goldilocksModulus := by
      simp only [List.length_cons] at space
      omega
    have cell := stored_byte_prefix (storeAdvice st values).1 value.val.toUInt8
      (storeAdvice st values).2 finish (adviceBytes values) bytesRead (by simpa only [field_byte_exact value range] using pointerBound)
    refine ⟨finish, by simpa only [storeAdvice, adviceBytes, List.map_cons, field_byte_exact value range] using cell, ?_⟩
    have terminalRead := raw_load (storeAdvice st values).1 3 finish _ terminal
    simp only [storeAdvice, bytecodeMemory]
    rw [mem_store_preserves _ _ terminalRead]

theorem advice_slice_of_lookup (io : IOBuffer) (channel : G) (start : Nat) (values : List G)
    (lookup : ∀ i value, values[i]? = some value → (io.data.getD channel #[])[start + i]? = some value) :
    AdviceSlice io channel start values := by
  induction values generalizing start with
  | nil => exact .nil _
  | cons value values ih =>
    refine .cons (by simpa using lookup 0 value (by simp)) (ih (start + 1) ?_)
    intro i value found
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lookup (i + 1) value (by simpa using found)

theorem advice_slice_array (io : IOBuffer) (channel : G) (before values after : Array G)
    (arena : io.data.getD channel #[] = before ++ values ++ after) :
    AdviceSlice io channel before.size values.toList := by
  apply advice_slice_of_lookup
  intro i value found
  have asArray : values[i]? = some value := by simpa using found
  obtain ⟨bound, valueAt⟩ := Array.getElem?_eq_some_iff.mp asArray
  simp [arena, Array.getElem?_append, bound, show ¬ before.size + i < before.size by omega, valueAt]

private theorem extract_single (arena : Array G) (start : Nat) (value : G)
    (lookup : arena[start]? = some value) : arena.extract start (start + 1) = #[value] := by
  obtain ⟨bound, found⟩ := Array.getElem?_eq_some_iff.mp lookup
  apply Array.ext (by simp [Array.size_extract, Nat.min_eq_left (by omega : start + 1 ≤ arena.size)])
  intro i hi hj
  have zero : i = 0 := by change i < 1 at hj; omega
  subst i
  simpa using found

private theorem field_add_one (n : Nat) (range : n < goldilocksModulus) :
    G.ofNat n + 1 = G.ofNat (n + 1) := by
  change G.ofNat ((G.ofNat n).n + 1) = _
  rw [field_of_nat_exact _ range]

def adviceZero (selector : Nat) : Aiur.Bytecode.Block := {
  ops := #[.const 1, .const 1, .store #[3, 4, 4]], ctrl := .return selector #[5] }
def adviceHead : Array Aiur.Bytecode.Op :=
  #[.ioRead 0 1 1, .const 0, .u8RangeCheck 3 4, .const 1, .add 1 5,
    .const 1, .sub 2 7]
def adviceFinish (selector : Nat) : Aiur.Bytecode.Block := {
  ops := #[.const 0, .store #[10, 3, 9]], ctrl := .return selector #[11] }
def adviceStep (self selector : Nat) : Aiur.Bytecode.Block := {
  ops := adviceHead ++ #[.call self #[0, 6, 8] 1 false] ++ (adviceFinish selector).ops,
  ctrl := (adviceFinish selector).ctrl }
def adviceBody (self zeroSelector consSelector : Nat) : Aiur.Bytecode.Block :=
  ⟨#[], .match 2 #[(0, adviceZero zeroSelector)] (some (adviceStep self consSelector))⟩

def checkAdviceReader (f : Aiur.Bytecode.Function) (self zeroSelector consSelector : Nat) : Bool :=
  match f.body.ctrl with
  | .match count zeros (some step) =>
    match zeros.toList with
    | [(tag, zero)] =>
      decide (f.layout.inputSize = 3 ∧ f.body.ops = #[] ∧ count = 2 ∧ tag = 0) &&
        checkReturnBlock zero (adviceZero zeroSelector).ops zeroSelector #[5] &&
        checkReturnBlock step (adviceStep self consSelector).ops consSelector #[11]
    | _ => false
  | _ => false

theorem advice_reader_checked (f : Aiur.Bytecode.Function) (self zeroSelector consSelector : Nat)
    (checked : checkAdviceReader f self zeroSelector consSelector = true) :
    f.layout.inputSize = 3 ∧ f.body = adviceBody self zeroSelector consSelector := by
  unfold checkAdviceReader at checked
  split at checked
  · rename_i count zeros step ctrl
    split at checked
    · rename_i tag zero arms
      simp only [Bool.and_eq_true] at checked
      obtain ⟨⟨basic, zeroChecked⟩, stepChecked⟩ := checked
      obtain ⟨input, ops, countEq, tagEq⟩ := of_decide_eq_true basic
      have zerosEq : zeros = #[(tag, zero)] := Array.toList_inj.mp arms
      have zeroEq := return_block_checked zero _ _ _ zeroChecked
      have stepEq := return_block_checked step _ _ _ stepChecked
      refine ⟨input, ?_⟩
      cases f with
      | mk b layout entry constrained => cases b; simp_all [adviceBody, adviceZero, adviceStep, adviceFinish]
    · simp at checked
  · simp at checked

def loadHead : Array Aiur.Bytecode.Op :=
  #[.const 0, .ioGetInfo 0 #[2], .const 1, .add 1 5, .u32LessThan 4 6,
    .const 1, .assertEq #[7] #[8] (some "IxBy artifact byte limit")]
def loadBody (reader selector : Nat) : Aiur.Bytecode.Block := {
  ops := loadHead ++ #[.call reader #[0, 3, 4] 1 false], ctrl := .return selector #[9] }
def checkLoader (f : Aiur.Bytecode.Function) (reader selector : Nat) : Bool :=
  decide (f.layout.inputSize = 2) && checkReturnBlock f.body (loadBody reader selector).ops selector #[9]

theorem loader_checked (f : Aiur.Bytecode.Function) (reader selector : Nat)
    (checked : checkLoader f reader selector = true) :
    f.layout.inputSize = 2 ∧ f.body = loadBody reader selector := by
  simp only [checkLoader, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact ⟨checked.1, return_block_checked f.body _ _ _ checked.2⟩

structure LoaderCode where
  reader : Nat
  loader : Nat
  zeroSelector : Nat := 0
  consSelector : Nat := 1
  loadSelector : Nat := 0

structure CheckedLoader (t : Bytecode.Toplevel) (code : LoaderCode) where
  readFn : Aiur.Bytecode.Function
  loadFn : Aiur.Bytecode.Function
  readFunction : t.functions[code.reader]? = some readFn
  loadFunction : t.functions[code.loader]? = some loadFn
  readChecked : checkAdviceReader readFn code.reader code.zeroSelector code.consSelector = true
  loadChecked : checkLoader loadFn code.reader code.loadSelector = true

def checkLoaderCode (t : Bytecode.Toplevel) (code : LoaderCode) : Bool :=
  match t.functions[code.reader]?, t.functions[code.loader]? with
  | some reader, some loader =>
    checkAdviceReader reader code.reader code.zeroSelector code.consSelector &&
      checkLoader loader code.reader code.loadSelector
  | _, _ => false

theorem loader_code_checked (t : Bytecode.Toplevel) (code : LoaderCode)
    (checked : checkLoaderCode t code = true) : Nonempty (CheckedLoader t code) := by
  unfold checkLoaderCode at checked
  split at checked
  · rename_i reader loader readFunction loadFunction
    simp only [Bool.and_eq_true] at checked
    exact ⟨⟨reader, loader, readFunction, loadFunction, checked.1, checked.2⟩⟩
  · simp at checked

private theorem run_single (t : Bytecode.Toplevel) (fuel : Nat) (op : Aiur.Bytecode.Op) (st : EvalState) :
    runOps t fuel #[op] st 0 = Aiur.Bytecode.Eval.evalOp t fuel op st := by
  simp [run_ops_list, Bind.bind, Except.bind, Pure.pure, Except.pure]
  cases Aiur.Bytecode.Eval.evalOp t fuel op st <;> rfl

private theorem eval_block_append (t : Bytecode.Toplevel) (fuel : Nat)
    (left right : Array Aiur.Bytecode.Op) (ctrl : Aiur.Bytecode.Ctrl) (st : EvalState) :
    evalBlock t fuel ⟨left ++ right, ctrl⟩ st =
      (runOps t fuel left st 0).bind (fun next => evalBlock t fuel ⟨right, ctrl⟩ next) := by
  simp only [evalBlock, run_ops_append]
  cases runOps t fuel left st 0 <;> rfl

def adviceRegisters (channel : G) (start count : Nat) (value : G) : Array G :=
  #[channel, G.ofNat start, G.ofNat (count + 1), value, 0, 1, G.ofNat (start + 1), 1, G.ofNat count]

private theorem io_read_single (t : Bytecode.Toplevel) (fuel : Nat) (st : EvalState)
    (channelIndex addressIndex : Nat) (channel address value : G)
    (channelArg : st.map[channelIndex]? = some channel) (addressArg : st.map[addressIndex]? = some address)
    (lookup : (st.ioBuffer.data.getD channel #[])[address.n]? = some value) :
    Aiur.Bytecode.Eval.evalOp t fuel (.ioRead channelIndex addressIndex 1) st =
      .ok { st with map := st.map ++ #[value] } := by
  have bound := (Array.getElem?_eq_some_iff.mp lookup).1
  have extract := extract_single _ _ _ lookup
  simp only [G.n] at bound extract
  simp only [Aiur.Bytecode.Eval.evalOp, readIdx, channelArg, addressArg,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [if_neg (by omega), extract]
  rfl

private theorem advice_check_eval (t : Bytecode.Toplevel) (fuel : Nat) (st : EvalState)
    (size : st.map.size = 4) (value : G) (found : st.map[3]? = some value) :
    runOps t fuel #[.const 0, .u8RangeCheck 3 4] st 0 =
      if value.n < 256 then .ok { st with map := st.map.push 0 } else .error .u8RangeCheckFailed := by
  have zeroRange : (0 : G).n < 256 := by decide
  have valueAt := (Array.getElem?_eq_some_iff.mp found).2
  by_cases valid : value.n < 256 <;>
    simp +arith [run_ops_list, Aiur.Bytecode.Eval.evalOp, readIdx, pushMap, size,
      Array.getElem_push, valueAt, UInt64.lt_iff_toNat_lt, zeroRange, valid,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem advice_advance_eval (t : Bytecode.Toplevel) (fuel : Nat) (st : EvalState)
    (size : st.map.size = 5) (start count : Nat)
    (address : start < goldilocksModulus) (length : count + 1 < goldilocksModulus)
    (addressAt : st.map[1]? = some (G.ofNat start)) (countAt : st.map[2]? = some (G.ofNat (count + 1))) :
    runOps t fuel #[.const 1, .add 1 5, .const 1, .sub 2 7] st 0 =
      .ok { st with map := st.map ++ #[1, G.ofNat (start + 1), 1, G.ofNat count] } := by
  have addressValue := (Array.getElem?_eq_some_iff.mp addressAt).2
  have countValue := (Array.getElem?_eq_some_iff.mp countAt).2
  simp [run_ops_list, Aiur.Bytecode.Eval.evalOp, readIdx, pushMap, size,
    Array.getElem_push, addressValue, countValue, field_add_one start address, field_pred count length,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  apply Array.toList_inj.mp
  simp [List.append_assoc]

private theorem advice_head_eval (t : Bytecode.Toplevel) (fuel : Nat) (st : EvalState)
    (channel value : G) (start count : Nat)
    (address : start < goldilocksModulus) (length : count + 1 < goldilocksModulus)
    (lookup : (st.ioBuffer.data.getD channel #[])[start]? = some value) :
    runOps t fuel adviceHead { st with map := #[channel, G.ofNat start, G.ofNat (count + 1)] } 0 =
      if value.n < 256 then .ok { st with map := adviceRegisters channel start count value }
      else .error .u8RangeCheckFailed := by
  have input := io_read_single t fuel { st with map := #[channel, G.ofNat start, G.ofNat (count + 1)] }
    0 1 channel (G.ofNat start) value (by simp) (by simp) (by simpa only [field_of_nat_exact start address] using lookup)
  change runOps t fuel (#[.ioRead 0 1 1] ++ (#[.const 0, .u8RangeCheck 3 4] ++ #[.const 1, .add 1 5, .const 1, .sub 2 7])) _ 0 = _
  rw [run_ops_append, run_single, input]
  have checkRun := advice_check_eval t fuel
    { st with map := #[channel, G.ofNat start, G.ofNat (count + 1)] ++ #[value] } (by simp) value (by simp)
  have advanceRun := advice_advance_eval t fuel
    { st with map := (#[channel, G.ofNat start, G.ofNat (count + 1)] ++ #[value]).push 0 }
    (by simp) start count address length (by simp) (by simp)
  simp only [Except.bind]
  rw [run_ops_append, checkRun]
  by_cases valid : value.n < 256
  · simp only [if_pos valid, Except.bind, advanceRun]
    rfl
  · simp only [if_neg valid, Except.bind]

private theorem advice_zero_eval (t : Bytecode.Toplevel) (fuel self zeroSelector consSelector : Nat)
    (st : EvalState) (channel address : G) :
    ∃ after, evalBlock t fuel (adviceBody self zeroSelector consSelector) { st with map := #[channel, address, 0] } =
      .error (.earlyReturn #[(storeAdvice st []).2] after) ∧
      after.memory = (storeAdvice st []).1.memory ∧ after.ioBuffer = st.ioBuffer := by
  simp [adviceBody, adviceZero, storeAdvice, evalBlock, runOps,
    Aiur.Bytecode.Eval.evalOp, readIdx, readIdxs, pushMap, evalCtrl, evalMatchArm,
    Bind.bind, Except.bind, Pure.pure, Except.pure, mem_store_io]

private theorem advice_nonzero (t : Bytecode.Toplevel) (fuel self zeroSelector consSelector : Nat)
    (st : EvalState) (channel address count : G) (nonzero : count ≠ 0) :
    evalBlock t fuel (adviceBody self zeroSelector consSelector) { st with map := #[channel, address, count] } =
      evalBlock t fuel (adviceStep self consSelector) { st with map := #[channel, address, count] } := by
  have nonzeroVal : (0 : G).val ≠ count.val := fun equal => nonzero (Subtype.ext equal.symm)
  simp [adviceBody, evalBlock, run_ops_list, readIdx, evalCtrl, evalMatchArm, evalDefaultBlock,
    nonzeroVal, Pure.pure, Except.pure]

private theorem call_single_result (t : Bytecode.Toplevel) (fuel callee : Nat) (st : EvalState)
    (f : Aiur.Bytecode.Function) (function : t.functions[callee]? = some f)
    (args : Array Nat) (values : Array G) (arguments : readIdxs st args = .ok values)
    (arity : f.layout.inputSize = values.size) (accepted : Prop) [Decidable accepted]
    (pointer : G) (after : EvalState)
    (executed : evalBlock t fuel f.body { st with map := values } =
      if accepted then .error (.earlyReturn #[pointer] after) else .error .u8RangeCheckFailed) (unconstrained : Bool) :
    Aiur.Bytecode.Eval.evalOp t (fuel + 1) (.call callee args 1 unconstrained) st =
      if accepted then .ok { st with map := st.map ++ #[pointer], memory := after.memory, ioBuffer := after.ioBuffer }
      else .error .u8RangeCheckFailed := by
  obtain ⟨bound, found⟩ := Array.getElem?_eq_some_iff.mp function
  by_cases accept : accepted <;>
    simp [Aiur.Bytecode.Eval.evalOp, arguments, bound, found, arity, executed, accept,
      appendMap, setIoBuffer, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem advice_finish_eval (t : Bytecode.Toplevel) (fuel selector : Nat) (st : EvalState)
    (channel value tail : G) (start count : Nat) :
    ∃ after, evalBlock t fuel (adviceFinish selector)
        { st with map := adviceRegisters channel start count value ++ #[tail] } =
      .error (.earlyReturn #[G.ofNat (memStore st #[0, value, tail]).2] after) ∧
      after.memory = (memStore st #[0, value, tail]).1.memory ∧ after.ioBuffer = st.ioBuffer := by
  simp [adviceFinish, adviceRegisters, evalBlock, run_ops_list, Aiur.Bytecode.Eval.evalOp,
    readIdx, readIdxs, pushMap, evalCtrl, Bind.bind, Except.bind, Pure.pure, Except.pure, mem_store_io]

/-- Exact recursive behavior on available, field-valued advice. Byte ranges
are checked, not premises. Invalid values fail at the actual range check.
Address/length non-wrap is explicit; no allocation assumption is needed just
to describe the stores (it is needed below to interpret their field pointers). -/
theorem checked_advice_eval (t : Bytecode.Toplevel) (code : LoaderCode) (checked : CheckedLoader t code)
    (fuel : Nat) (st : EvalState) (channel : G) (start : Nat) (values : List G)
    (available : AdviceSlice st.ioBuffer channel start values)
    (address : start + values.length < goldilocksModulus) :
    ∃ after, evalBlock t (fuel + values.length) checked.readFn.body
        { st with map := #[channel, G.ofNat start, G.ofNat values.length] } =
      (if ByteFields values then .error (.earlyReturn #[(storeAdvice st values).2] after)
        else .error .u8RangeCheckFailed) ∧
      (ByteFields values → after.memory = (storeAdvice st values).1.memory ∧ after.ioBuffer = st.ioBuffer) := by
  induction values generalizing st start with
  | nil =>
    obtain ⟨after, executed, memory, io⟩ := advice_zero_eval t fuel code.reader code.zeroSelector code.consSelector st channel (G.ofNat start)
    refine ⟨after, ?_, fun _ => ⟨memory, io⟩⟩
    rw [(advice_reader_checked checked.readFn _ _ _ checked.readChecked).2]
    simpa [ByteFields, show G.ofNat 0 = 0 from rfl] using executed
  | cons value values ih =>
    cases available with
    | cons lookup rest =>
      simp only [List.length_cons] at address ⊢
      rw [show fuel + (values.length + 1) = fuel + values.length + 1 by omega,
        (advice_reader_checked checked.readFn _ _ _ checked.readChecked).2,
        advice_nonzero t _ _ _ _ _ _ _ _ (field_succ_nonzero values.length (by omega))]
      have headRun := advice_head_eval t (fuel + values.length + 1) st channel value start values.length (by omega) (by omega) lookup
      by_cases range : value.n < 256
      · rw [if_pos range] at headRun
        let registers := adviceRegisters channel start values.length value
        obtain ⟨afterTail, tailRun, tailState⟩ := ih { st with map := registers } (start + 1) rest (by omega)
        simp only [store_advice_map] at tailRun tailState
        have arguments : readIdxs { st with map := registers } #[0, 6, 8] =
            .ok #[channel, G.ofNat (start + 1), G.ofNat values.length] := by
          simp [registers, adviceRegisters, readIdxs, readIdx, Bind.bind, Except.bind, Pure.pure, Except.pure]
        have callRun := call_single_result t (fuel + values.length) code.reader { st with map := registers }
          checked.readFn checked.readFunction _ _ arguments
          (advice_reader_checked checked.readFn _ _ _ checked.readChecked).1
          (ByteFields values) (storeAdvice st values).2 afterTail tailRun false
        dsimp only [registers] at callRun
        by_cases validTail : ByteFields values
        · obtain ⟨memory, io⟩ := tailState validTail
          rw [if_pos validTail, memory, io] at callRun
          obtain ⟨after, finishRun, finishMemory, finishIo⟩ := advice_finish_eval t (fuel + values.length + 1) code.consSelector
            (storeAdvice st values).1 channel value (storeAdvice st values).2 start values.length
          have valid := (byte_fields_cons value values).mpr ⟨range, validTail⟩
          refine ⟨after, ?_, fun _ => ⟨finishMemory, finishIo.trans (store_advice_io st values)⟩⟩
          simp only [if_pos valid, adviceStep, eval_block_append, run_ops_append, run_single,
            headRun, callRun, Except.bind]
          simpa only [adviceFinish, registers, storeAdvice, store_advice_io] using finishRun
        · rw [if_neg validTail] at callRun
          have invalid : ¬ ByteFields (value :: values) := fun valid => validTail ((byte_fields_cons value values).mp valid).2
          refine ⟨st, ?_, fun valid => False.elim (invalid valid)⟩
          simp only [if_neg invalid, adviceStep, eval_block_append, run_ops_append, run_single,
            headRun, callRun, Except.bind]
      · rw [if_neg range] at headRun
        have invalid : ¬ ByteFields (value :: values) := fun valid => range ((byte_fields_cons value values).mp valid).1
        refine ⟨st, ?_, fun valid => False.elim (invalid valid)⟩
        simp only [if_neg invalid, adviceStep, eval_block_append, run_ops_append, headRun, Except.bind]

/-- Actual Call contract, including register restoration and exact stores. -/
theorem checked_advice_call (t : Bytecode.Toplevel) (code : LoaderCode) (checked : CheckedLoader t code)
    (fuel : Nat) (st : EvalState) (channel : G) (start : Nat) (values : List G)
    (available : AdviceSlice st.ioBuffer channel start values)
    (address : start + values.length < goldilocksModulus)
    (args : Array Nat) (arguments : readIdxs st args = .ok #[channel, G.ofNat start, G.ofNat values.length])
    (unconstrained : Bool) :
    Aiur.Bytecode.Eval.evalOp t (fuel + values.length + 1) (.call code.reader args 1 unconstrained) st =
      if ByteFields values then .ok { (storeAdvice st values).1 with map := st.map ++ #[(storeAdvice st values).2] }
      else .error .u8RangeCheckFailed := by
  obtain ⟨after, executed, state⟩ := checked_advice_eval t code checked fuel st channel start values available address
  have called := call_single_result t (fuel + values.length) code.reader st checked.readFn checked.readFunction
    args _ arguments (advice_reader_checked checked.readFn _ _ _ checked.readChecked).1
    (ByteFields values) (storeAdvice st values).2 after executed unconstrained
  by_cases valid : ByteFields values
  · obtain ⟨memory, io⟩ := state valid
    simpa only [if_pos valid, memory, io, store_advice_io] using called
  · simpa only [if_neg valid] using called

/-- The actual UInt32 comparison agrees with the natural byte limit only
under these non-wrapping metadata and limit bounds. -/
theorem load_u32_limit (length limit : Nat) (lengthRange : length < 2 ^ 32)
    (limitRange : limit + 1 < 2 ^ 32) :
    (G.ofNat length).val.toUInt32 < (G.ofNat limit + 1).val.toUInt32 ↔ length ≤ limit := by
  have lengthField : length < goldilocksModulus := by change length < 18446744069414584321; omega
  have limitField : limit + 1 < goldilocksModulus := by change limit + 1 < 18446744069414584321; omega
  rw [field_add_one limit (by omega), UInt32.lt_iff_toNat_lt, UInt64.toNat_toUInt32,
    UInt64.toNat_toUInt32]
  change (G.ofNat length).n % 2 ^ 32 < (G.ofNat (limit + 1)).n % 2 ^ 32 ↔ length ≤ limit
  rw [field_of_nat_exact length lengthField, field_of_nat_exact (limit + 1) limitField,
    Nat.mod_eq_of_lt lengthRange, Nat.mod_eq_of_lt limitRange]
  omega

def loadRegisters (channel : G) (start length limit : Nat) : Array G :=
  #[channel, G.ofNat limit, 0, G.ofNat start, G.ofNat length, 1, G.ofNat (limit + 1), 1, 1]

private theorem load_head_eval (t : Bytecode.Toplevel) (fuel : Nat) (st : EvalState)
    (channel : G) (start length limit : Nat)
    (metadata : st.ioBuffer.map[(channel, (#[0] : Array G))]? = some ⟨start, length⟩)
    (lengthRange : length < 2 ^ 32) (limitRange : limit + 1 < 2 ^ 32) :
    runOps t fuel loadHead { st with map := #[channel, G.ofNat limit] } 0 =
      if length ≤ limit then .ok { st with map := loadRegisters channel start length limit }
      else .error .assertFailed := by
  have comparison := load_u32_limit length limit lengthRange limitRange
  have limitField : limit < goldilocksModulus := by change limit < 18446744069414584321; omega
  rw [field_add_one limit limitField] at comparison
  simp at comparison
  have different : (0 : G).val ≠ (1 : G).val := by decide
  by_cases limitOk : length ≤ limit <;>
    simp [loadHead, run_ops_list, Aiur.Bytecode.Eval.evalOp, readIdx, readIdxs, metadata,
      pushMap, comparison, limitOk, different, field_add_one limit limitField,
      loadRegisters, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- The precise returned state of the complete loader body. -/
def loadedState (st : EvalState) (channel : G) (start limit : Nat) (values : List G) : EvalState :=
  { (storeAdvice st values).1 with map := loadRegisters channel start values.length limit ++ #[(storeAdvice st values).2] }

/-- Complete checked loader behavior: limit rejection precedes reading and
range checking. Under the stated metadata/address bounds, acceptance is exactly
the natural byte limit together with every consumed raw field being a byte. -/
theorem checked_load_eval (t : Bytecode.Toplevel) (code : LoaderCode) (checked : CheckedLoader t code)
    (fuel : Nat) (st : EvalState) (channel : G) (start limit : Nat) (values : List G)
    (metadata : st.ioBuffer.map[(channel, (#[0] : Array G))]? = some ⟨start, values.length⟩)
    (available : AdviceSlice st.ioBuffer channel start values)
    (address : start + values.length < goldilocksModulus)
    (lengthRange : values.length < 2 ^ 32) (limitRange : limit + 1 < 2 ^ 32) :
    evalBlock t (fuel + values.length + 1) checked.loadFn.body { st with map := #[channel, G.ofNat limit] } =
      if values.length ≤ limit then
        if ByteFields values then .error (.earlyReturn #[(storeAdvice st values).2] (loadedState st channel start limit values))
        else .error .u8RangeCheckFailed
      else .error .assertFailed := by
  rw [(loader_checked checked.loadFn _ _ checked.loadChecked).2]
  have headerRun := load_head_eval t (fuel + values.length + 1) st channel start values.length limit metadata lengthRange limitRange
  by_cases limitOk : values.length ≤ limit
  · rw [if_pos limitOk] at headerRun ⊢
    let registers := loadRegisters channel start values.length limit
    have arguments : readIdxs { st with map := registers } #[0, 3, 4] =
        .ok #[channel, G.ofNat start, G.ofNat values.length] := by
      simp [registers, loadRegisters, readIdxs, readIdx, Bind.bind, Except.bind, Pure.pure, Except.pure]
    have callRun := checked_advice_call t code checked fuel { st with map := registers }
      channel start values available address #[0, 3, 4] arguments false
    simp only [store_advice_map] at callRun
    dsimp only [registers] at callRun
    by_cases valid : ByteFields values
    · rw [if_pos valid] at callRun ⊢
      simp only [loadBody, eval_block_append, headerRun, Except.bind, evalBlock, run_single, callRun]
      simp [evalCtrl, readIdxs, readIdx, loadRegisters, loadedState, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · rw [if_neg valid] at callRun ⊢
      simp only [loadBody, eval_block_append, headerRun, Except.bind, evalBlock, run_single, callRun]
  · rw [if_neg limitOk] at headerRun ⊢
    simp only [loadBody, eval_block_append, headerRun, Except.bind]

/-- Complete actual Call behavior, with both caller constraint flags. -/
theorem checked_load_call (t : Bytecode.Toplevel) (code : LoaderCode) (checked : CheckedLoader t code)
    (fuel : Nat) (st : EvalState) (channel : G) (start limit : Nat) (values : List G)
    (metadata : st.ioBuffer.map[(channel, (#[0] : Array G))]? = some ⟨start, values.length⟩)
    (available : AdviceSlice st.ioBuffer channel start values)
    (address : start + values.length < goldilocksModulus)
    (lengthRange : values.length < 2 ^ 32) (limitRange : limit + 1 < 2 ^ 32)
    (args : Array Nat) (arguments : readIdxs st args = .ok #[channel, G.ofNat limit]) (unconstrained : Bool) :
    Aiur.Bytecode.Eval.evalOp t (fuel + values.length + 2) (.call code.loader args 1 unconstrained) st =
      if values.length ≤ limit then
        if ByteFields values then .ok { (storeAdvice st values).1 with map := st.map ++ #[(storeAdvice st values).2] }
        else .error .u8RangeCheckFailed
      else .error .assertFailed := by
  obtain ⟨bound, found⟩ := Array.getElem?_eq_some_iff.mp checked.loadFunction
  have arity := (loader_checked checked.loadFn _ _ checked.loadChecked).1
  have executed := checked_load_eval t code checked fuel st channel start limit values metadata available address lengthRange limitRange
  rw [show fuel + values.length + 2 = (fuel + values.length + 1) + 1 by omega]
  by_cases limitOk : values.length ≤ limit <;> by_cases valid : ByteFields values <;>
    simp [Aiur.Bytecode.Eval.evalOp, arguments, bound, found, arity, executed, limitOk, valid,
      loadedState, store_advice_io, appendMap, setIoBuffer, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Limit failure does not require any readable arena or recursive-call fuel. -/
theorem checked_load_limit_reject (t : Bytecode.Toplevel) (code : LoaderCode) (checked : CheckedLoader t code)
    (fuel : Nat) (st : EvalState) (channel : G) (start length limit : Nat)
    (metadata : st.ioBuffer.map[(channel, (#[0] : Array G))]? = some ⟨start, length⟩)
    (lengthRange : length < 2 ^ 32) (limitRange : limit + 1 < 2 ^ 32) (tooLong : limit < length) :
    evalBlock t fuel checked.loadFn.body { st with map := #[channel, G.ofNat limit] } = .error .assertFailed := by
  have headerRun := load_head_eval t fuel st channel start length limit metadata lengthRange limitRange
  rw [if_neg (by omega)] at headerRun
  rw [(loader_checked checked.loadFn _ _ checked.loadChecked).2]
  simp only [loadBody, eval_block_append, headerRun, Except.bind]

/-- A non-byte at the next address fails before looking at any tail advice. -/
theorem checked_advice_head_reject (t : Bytecode.Toplevel) (code : LoaderCode) (checked : CheckedLoader t code)
    (fuel : Nat) (st : EvalState) (channel value : G) (start count : Nat)
    (address : start < goldilocksModulus) (length : count + 1 < goldilocksModulus)
    (lookup : (st.ioBuffer.data.getD channel #[])[start]? = some value) (invalid : ¬ value.n < 256) :
    evalBlock t fuel checked.readFn.body { st with map := #[channel, G.ofNat start, G.ofNat (count + 1)] } =
      .error .u8RangeCheckFailed := by
  have headerRun := advice_head_eval t fuel st channel value start count address length lookup
  rw [if_neg invalid] at headerRun
  rw [(advice_reader_checked checked.readFn _ _ _ checked.readChecked).2,
    advice_nonzero t _ _ _ _ _ _ _ _ (field_succ_nonzero count length)]
  simp only [adviceStep, eval_block_append, run_ops_append, headerRun, Except.bind]

/-- Success establishes the genuine-byte stream and preserves the resources
needed by the declaration parser. Byte validity is a conclusion, not a premise.
No state rollback is claimed for failures, whose error type carries no state. -/
theorem checked_load_admission (t : Bytecode.Toplevel) (code : LoaderCode) (checked : CheckedLoader t code)
    (fuel : Nat) (st : EvalState) (channel : G) (start limit : Nat) (values : List G)
    (metadata : st.ioBuffer.map[(channel, (#[0] : Array G))]? = some ⟨start, values.length⟩)
    (available : AdviceSlice st.ioBuffer channel start values)
    (address : start + values.length < goldilocksModulus)
    (lengthRange : values.length < 2 ^ 32) (limitRange : limit + 1 < 2 ^ 32)
    (space : bucketSize st 3 + values.length + 1 ≤ goldilocksModulus)
    (outputs : Array G) (after : EvalState)
    (executed : evalBlock t (fuel + values.length + 1) checked.loadFn.body { st with map := #[channel, G.ofNat limit] } =
      .error (.earlyReturn outputs after)) :
    values.length ≤ limit ∧ ByteFields values ∧ outputs = #[(storeAdvice st values).2] ∧
      ByteStream (bytecodeMemory after) (storeAdvice st values).2 (adviceBytes values) ∧
      after.ioBuffer = st.ioBuffer ∧
      bucketSize after 3 ≤ bucketSize st 3 + values.length + 1 ∧
      (∀ width, 3 ≠ width → bucketSize after width = bucketSize st width) ∧
      (∀ width pointer flat, memLoad st width pointer = .ok flat → memLoad after width pointer = .ok flat) := by
  rw [checked_load_eval t code checked fuel st channel start limit values metadata available address lengthRange limitRange] at executed
  by_cases limitOk : values.length ≤ limit
  · rw [if_pos limitOk] at executed
    by_cases valid : ByteFields values
    · rw [if_pos valid] at executed
      have same := BytecodeError.earlyReturn.inj (Except.error.inj executed)
      obtain ⟨rfl, rfl⟩ := same
      refine ⟨limitOk, valid, rfl, ?_, store_advice_io st values, store_advice_size st values,
        store_advice_other_bucket st values, ?_⟩
      · simpa only [loadedState, bytecode_memory_map] using store_advice_stream st values valid space
      · intro width pointer flat read
        exact store_advice_preserves st values read
    · simp only [if_neg valid] at executed
      cases executed
  · simp only [if_neg limitOk] at executed
    cases executed

/-- The standard append-and-register operation supplies exactly this metadata,
even when other data already occupies the same channel. -/
theorem extend_advice_metadata (io : IOBuffer) (channel : G) (values : Array G) :
    (io.extend channel #[0] values).map[(channel, (#[0] : Array G))]? =
      some ⟨(io.data.getD channel #[]).size, values.size⟩ := by
  simp [IOBuffer.extend]

theorem extend_advice_slice (io : IOBuffer) (channel : G) (values : Array G) :
    AdviceSlice (io.extend channel #[0] values) channel (io.data.getD channel #[]).size values.toList := by
  apply advice_slice_array _ _ _ _ #[]
  simp [IOBuffer.extend]

theorem byte_fields_bytes (bytes : List UInt8) : ByteFields (bytes.map G.ofUInt8) := by
  intro value member
  obtain ⟨byte, _, rfl⟩ := List.mem_map.mp member
  simpa using byte.toNat_lt

theorem advice_bytes_exact (bytes : List UInt8) : adviceBytes (bytes.map G.ofUInt8) = bytes := by
  have element : ∀ byte : UInt8, (G.ofUInt8 byte).val.toUInt8 = byte := by
    intro byte
    apply UInt8.toNat_inj.mp
    rw [UInt64.toNat_toUInt8]
    change (G.ofUInt8 byte).n % 256 = byte.toNat
    rw [byte_field_exact, Nat.mod_eq_of_lt byte.toNat_lt]
  simp [adviceBytes, List.map_map, Function.comp_def, element]

/-- Direct instantiation for the actual `IOBuffer.extend` constructor. This
does not assume that untrusted fields were already converted to UInt8. -/
theorem checked_extended_load (t : Bytecode.Toplevel) (code : LoaderCode) (checked : CheckedLoader t code)
    (fuel : Nat) (st : EvalState) (channel : G) (limit : Nat) (values : Array G)
    (address : (st.ioBuffer.data.getD channel #[]).size + values.size < goldilocksModulus)
    (lengthRange : values.size < 2 ^ 32) (limitRange : limit + 1 < 2 ^ 32) :
    let ready := { st with ioBuffer := st.ioBuffer.extend channel #[0] values }
    evalBlock t (fuel + values.size + 1) checked.loadFn.body { ready with map := #[channel, G.ofNat limit] } =
      if values.size ≤ limit then
        if ByteFields values.toList then .error (.earlyReturn #[(storeAdvice ready values.toList).2]
          (loadedState ready channel (st.ioBuffer.data.getD channel #[]).size limit values.toList))
        else .error .u8RangeCheckFailed
      else .error .assertFailed := by
  simpa using checked_load_eval t code checked fuel { st with ioBuffer := st.ioBuffer.extend channel #[0] values }
    channel (st.ioBuffer.data.getD channel #[]).size limit values.toList
    (by simpa using extend_advice_metadata st.ioBuffer channel values)
    (extend_advice_slice st.ioBuffer channel values) (by simpa using address) (by simpa using lengthRange) limitRange

/-- Composition at an identified declaration prefix in the loaded bytes. The
loader supplies genuine bytes and preserves the width-13 capacity premise.
This does NOT certify the `is_run` header/count prefix, function table, digest
binding, or whole canonical program decoder; the count is still explicit. -/
theorem loaded_declarations (t : Bytecode.Toplevel) (loaderCode : LoaderCode) (loader : CheckedLoader t loaderCode)
    (declarationCode : DeclarationCode) (declarations : Objects.Declarations.CheckedCode t declarationCode)
    (loadFuel parseFuel : Nat) (st : EvalState) (channel : G) (start limit : Nat) (values : List G)
    (metadata : st.ioBuffer.map[(channel, (#[0] : Array G))]? = some ⟨start, values.length⟩)
    (available : AdviceSlice st.ioBuffer channel start values)
    (address : start + values.length < goldilocksModulus)
    (lengthRange : values.length < 2 ^ 32) (limitRange : limit + 1 < 2 ^ 32)
    (byteSpace : bucketSize st 3 + values.length + 1 ≤ goldilocksModulus)
    (decls : List DeclarationBytes) (suffix : List UInt8)
    (bytes : adviceBytes values = decls.flatMap DeclarationBytes.bytes ++ suffix)
    (capacity : decls.length ≤ 16) (tableSpace : bucketSize st 13 + decls.length + 1 ≤ goldilocksModulus)
    (outputs : Array G) (loaded : EvalState)
    (executed : evalBlock t (loadFuel + values.length + 1) loader.loadFn.body { st with map := #[channel, G.ofNat limit] } =
      .error (.earlyReturn outputs loaded)) :
    ∃ finish parsed, outputs = #[(storeAdvice st values).2] ∧
      ByteStream (bytecodeMemory loaded) finish suffix ∧
      evalBlock t (parseFuel + decls.length + 2) declarations.parserFn.body
          { loaded with map := #[(storeAdvice st values).2, G.ofNat decls.length] } =
        (if Valid decls then .error (.earlyReturn #[(storeDeclarations loaded decls).2, finish] parsed)
          else .error .assertFailed) ∧
      (Valid decls →
        readTable (bytecodeMemory parsed) (storeDeclarations loaded decls).2.n decls.length =
          some (decls.map DeclarationBytes.declaration).toArray ∧
        parsed.ioBuffer = st.ioBuffer ∧
        (∀ width pointer flat, memLoad st width pointer = .ok flat → memLoad parsed width pointer = .ok flat)) := by
  obtain ⟨_, _, outputsEq, stream, io, _, other, preserved⟩ := checked_load_admission t loaderCode loader
    loadFuel st channel start limit values metadata available address lengthRange limitRange byteSpace outputs loaded executed
  obtain ⟨terminal, whole, nilRead⟩ := stream
  rw [bytes] at whole
  obtain ⟨finish, declBytes, suffixBytes⟩ := byte_prefix_split whole
  have space : bucketSize loaded 13 + decls.length + 1 ≤ goldilocksModulus := by
    rw [other 13 (by decide)]
    exact tableSpace
  obtain ⟨parsed, parsedRun, state⟩ := checked_declarations_eval t declarationCode declarations parseFuel loaded decls
    capacity space (storeAdvice st values).2 finish declBytes
  refine ⟨finish, parsed, outputsEq, ⟨terminal, suffixBytes, nilRead⟩, parsedRun, ?_⟩
  intro valid
  obtain ⟨memory, parserIo⟩ := state valid
  refine ⟨?_, parserIo.trans io, ?_⟩
  · rw [bytecode_memory_congr parsed (storeDeclarations loaded decls).1 memory]
    exact store_declarations_table loaded decls valid capacity space
  · intro width pointer flat read
    simpa only [memLoad, memory] using store_declarations_preserves loaded decls (preserved width pointer flat read)

end
end
end Ix.Ixby.AiurBackend.Objects.Admission
