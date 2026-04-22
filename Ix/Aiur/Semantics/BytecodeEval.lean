module
public import Ix.Aiur.Stages.Bytecode
public import Ix.Aiur.Semantics.BytecodeFfi
public import Ix.IndexMap

/-!
Lean-native bytecode reference evaluator.

Mirrors `src/aiur/execute.rs` in big-step form:
- No `QueryRecord` (trace-side bookkeeping).
- No call cache.
- No `unconstrained` branching (both branches of every `if unconstrained` produce
  the same value; they differ only in whether a query is logged).
- No stack machine — direct big-step.
- Call-only fuel decrement at `Op.call`.
- Errors return, never panic.

Per-width memory buckets mirror Rust's `QueryRecord.memory_queries`
(`execute.rs:36-40`). Each `Op.store values` uses `values.size` as the width key.
-/

public section
@[expose] section

namespace Aiur

namespace Bytecode.Eval

/-- Tagged errors — small enum, no messages, for proof statements. -/
inductive BytecodeError
  | outOfFuel
  | invalidValIdx (v : ValIdx)
  | invalidFunIdx (f : FunIdx)
  | arityMismatch (f : FunIdx)
  | assertFailed
  | invalidPointer (w i : Nat)
  | ioKeyAlreadySet
  | ioKeyNotFound
  | ioReadOoB
  | callOutputSizeMismatch
  | unreachableAfterLayout
  deriving Repr, Inhabited

/-- Width-bucketed memory, matching Rust's `QueryRecord.memory_queries`.
Outer key is the width; each bucket is an ordered map from flat-width arrays of
field elements to unit (the index within the bucket is its insertion order). -/
abbrev MemoryBuckets := IndexMap Nat (IndexMap (Array G) Unit)

structure EvalState where
  map      : Array G := #[]
  memory   : MemoryBuckets := default
  ioBuffer : IOBuffer
  deriving Inhabited

/-! ## ValIdx access -/

def readIdx (st : EvalState) (v : ValIdx) : Except BytecodeError G :=
  match st.map[v]? with
  | some g => .ok g
  | none   => .error (.invalidValIdx v)

def readIdxs (st : EvalState) (vs : Array ValIdx) : Except BytecodeError (Array G) :=
  vs.foldlM (init := #[]) fun acc v => do
    let g ← readIdx st v
    pure (acc.push g)

/-! ## Memory ops -/

/-- Insert/retrieve at a specific width bucket; returns the insertion index. -/
def memStore (st : EvalState) (vals : Array G) : EvalState × Nat :=
  let width := vals.size
  let bucket := st.memory.getByKey width |>.getD default
  if let some idx := bucket.getIdxOf vals then
    (st, idx)
  else
    let idx := bucket.size
    let newBucket := bucket.insert vals ()
    let newMem := st.memory.insert width newBucket
    ({ st with memory := newMem }, idx)

/-- Load from the width-`size` bucket at index `ptr`. -/
def memLoad (st : EvalState) (size : Nat) (ptr : Nat) :
    Except BytecodeError (Array G) :=
  match st.memory.getByKey size with
  | none        => .error (.invalidPointer size ptr)
  | some bucket =>
    match bucket.getByIdx ptr with
    | some (vs, _) => .ok vs
    | none         => .error (.invalidPointer size ptr)

def pushMap (st : EvalState) (g : G) : EvalState :=
  { st with map := st.map.push g }

def appendMap (st : EvalState) (gs : Array G) : EvalState :=
  { st with map := st.map ++ gs }

def setIoBuffer (st : EvalState) (ioBuffer : IOBuffer) : EvalState :=
  { st with ioBuffer }

/-! ## Termination helpers

Lemmas proving that a `Block`'s sub-parts have strictly smaller `sizeOf`.
Used by the `decreasing_by` of the mutual block to discharge the
evalBlock → runOps (`sizeOf b.ops < sizeOf b`) and
evalBlock → evalCtrl (`sizeOf b.ctrl < sizeOf b`) obligations. -/

private theorem Block.sizeOf_ops_lt (b : Block) : sizeOf b.ops < sizeOf b := by
  rcases b with ⟨ops, ctrl⟩
  show sizeOf ops < 1 + sizeOf ops + sizeOf ctrl
  omega

private theorem Block.sizeOf_ctrl_lt (b : Block) : sizeOf b.ctrl < sizeOf b := by
  rcases b with ⟨ops, ctrl⟩
  show sizeOf ctrl < 1 + sizeOf ops + sizeOf ctrl
  omega

/-- For a match-case `(g, block)` drawn from `cases`, the block's `sizeOf` is
strictly less than `sizeOf cases + sizeOf defaultBlock`. -/
private theorem sizeOf_caseBlock_lt
    (cases : Array (G × Block)) (defaultBlock : Option Block) (i : Nat)
    (h : i < cases.size) :
    sizeOf cases[i].snd < sizeOf cases + sizeOf defaultBlock := by
  have h1 : sizeOf cases[i] < sizeOf cases := Array.sizeOf_get cases i h
  have h2 : sizeOf cases[i].snd < sizeOf cases[i] := by
    rcases cases[i] with ⟨g, block⟩
    show sizeOf block < 1 + sizeOf g + sizeOf block
    omega
  omega

/-- For `defaultBlock = some block`, the block's `sizeOf` is less than
`sizeOf cases + sizeOf defaultBlock`. -/
private theorem sizeOf_defaultBlock_lt
    (cases : Array (G × Block)) {block : Block} :
    sizeOf block < sizeOf cases + sizeOf (some block : Option Block) := by
  show sizeOf block < sizeOf cases + (1 + sizeOf block)
  omega

/-! ## Evaluator — mutual block over block/ctrl/ops recursion

Fuel decrements only at `.call` (call-only accounting). Other
recursive calls use structural decrease on the block/ctrl/ops tree. Measure is
lex `(fuel, priority, sizeOf)`.
-/

mutual

/-- Evaluate a single `Op`, returning the new state. `call` is the only op that
consumes fuel. -/
def evalOp (t : Bytecode.Toplevel) (fuel : Nat) (op : Op) (st : EvalState) :
    Except BytecodeError EvalState :=
  match op with
  | .const g => .ok (pushMap st g)
  | .add a b => do
    let x ← readIdx st a
    let y ← readIdx st b
    pure (pushMap st (x + y))
  | .sub a b => do
    let x ← readIdx st a
    let y ← readIdx st b
    pure (pushMap st (x - y))
  | .mul a b => do
    let x ← readIdx st a
    let y ← readIdx st b
    pure (pushMap st (x * y))
  | .eqZero a => do
    let x ← readIdx st a
    pure (pushMap st (if x.val == 0 then 1 else 0))
  | .call fi args outputSize _unconstrained => do
    let argGs ← readIdxs st args
    if h : fi < t.functions.size then
      let f := t.functions[fi]
      if f.layout.inputSize != argGs.size then
        .error (.arityMismatch fi)
      else
        let innerSt : EvalState := { ioBuffer := st.ioBuffer
                                     memory   := st.memory
                                     map      := argGs }
        match fuel with
        | 0 => .error .outOfFuel
        | fuel+1 =>
          match evalBlock t fuel f.body innerSt with
          | .error e => .error e
          | .ok (outs, innerSt') =>
            if outs.size != outputSize then
              .error .callOutputSizeMismatch
            else
              pure (appendMap (setIoBuffer { st with memory := innerSt'.memory }
                                            innerSt'.ioBuffer) outs)
    else .error (.invalidFunIdx fi)
  | .store vals => do
    let argGs ← readIdxs st vals
    let (st', idx) := memStore st argGs
    pure (pushMap st' (.ofNat idx))
  | .load size ptr => do
    let ptrG ← readIdx st ptr
    let vs ← memLoad st size ptrG.val.toNat
    pure (appendMap st vs)
  | .assertEq as bs => do
    let aGs ← readIdxs st as
    let bGs ← readIdxs st bs
    if aGs == bGs then .ok st else .error .assertFailed
  | .ioGetInfo keyIdxs => do
    let keyGs ← readIdxs st keyIdxs
    match st.ioBuffer.map[keyGs]? with
    | some info =>
      let st1 := pushMap st (.ofNat info.idx)
      pure (pushMap st1 (.ofNat info.len))
    | none => .error .ioKeyNotFound
  | .ioSetInfo keyIdxs idxIdx lenIdx => do
    let keyGs ← readIdxs st keyIdxs
    let iG ← readIdx st idxIdx
    let lG ← readIdx st lenIdx
    if st.ioBuffer.map.contains keyGs then
      .error .ioKeyAlreadySet
    else
      let info : IOKeyInfo := ⟨iG.val.toNat, lG.val.toNat⟩
      let newMap := st.ioBuffer.map.insert keyGs info
      pure (setIoBuffer st { st.ioBuffer with map := newMap })
  | .ioRead idxIdx len => do
    let iG ← readIdx st idxIdx
    let start := iG.val.toNat
    if start + len > st.ioBuffer.data.size then
      .error .ioReadOoB
    else
      pure (appendMap st (st.ioBuffer.data.extract start (start + len)))
  | .ioWrite dataIdxs => do
    let dataGs ← readIdxs st dataIdxs
    let newData := st.ioBuffer.data ++ dataGs
    pure (setIoBuffer st { st.ioBuffer with data := newData })
  | .u8BitDecomposition idx => do
    let g ← readIdx st idx
    let byte := g.val.toUInt8
    let bits := Array.ofFn fun (i : Fin 8) =>
      G.ofUInt8 ((byte >>> i.val.toUInt8) &&& 1)
    pure (appendMap st bits)
  | .u8ShiftLeft idx => do
    let g ← readIdx st idx
    pure (pushMap st (G.ofUInt8 (g.val.toUInt8 <<< 1)))
  | .u8ShiftRight idx => do
    let g ← readIdx st idx
    pure (pushMap st (G.ofUInt8 (g.val.toUInt8 >>> 1)))
  | .u8Xor a b => do
    let x ← readIdx st a; let y ← readIdx st b
    pure (pushMap st (G.ofUInt8 (x.val.toUInt8 ^^^ y.val.toUInt8)))
  | .u8Add a b => do
    let x ← readIdx st a; let y ← readIdx st b
    let sum := x.val.toUInt8.toNat + y.val.toUInt8.toNat
    let st1 := pushMap st (G.ofUInt8 sum.toUInt8)
    pure (pushMap st1 (if sum ≥ 256 then 1 else 0))
  | .u8Sub a b => do
    let x ← readIdx st a; let y ← readIdx st b
    let i := x.val.toUInt8; let j := y.val.toUInt8
    let st1 := pushMap st (G.ofUInt8 (i - j))
    pure (pushMap st1 (if j > i then 1 else 0))
  | .u8And a b => do
    let x ← readIdx st a; let y ← readIdx st b
    pure (pushMap st (G.ofUInt8 (x.val.toUInt8 &&& y.val.toUInt8)))
  | .u8Or a b => do
    let x ← readIdx st a; let y ← readIdx st b
    pure (pushMap st (G.ofUInt8 (x.val.toUInt8 ||| y.val.toUInt8)))
  | .u8LessThan a b => do
    let x ← readIdx st a; let y ← readIdx st b
    pure (pushMap st (if x.val.toUInt8 < y.val.toUInt8 then 1 else 0))
  | .u32LessThan a b => do
    let x ← readIdx st a; let y ← readIdx st b
    pure (pushMap st (if x.val.toUInt32 < y.val.toUInt32 then 1 else 0))
  | .debug _ _ => .ok st
termination_by (fuel, sizeOf op, 0)
decreasing_by all_goals first | decreasing_tactic | omega

/-- Run an ordered sequence of ops. -/
def runOps (t : Bytecode.Toplevel) (fuel : Nat) (ops : Array Op)
    (st : EvalState) (i : Nat) : Except BytecodeError EvalState :=
  if h : i < ops.size then
    match evalOp t fuel ops[i] st with
    | .error e => .error e
    | .ok st' => runOps t fuel ops st' (i+1)
  else .ok st
termination_by (fuel, sizeOf ops, 1 + (ops.size - i))
decreasing_by all_goals first | decreasing_tactic | omega

/-- Evaluate a `Block`: run all ops, then dispatch on the control. -/
def evalBlock (t : Bytecode.Toplevel) (fuel : Nat)
    (b : Block) (st : EvalState) : Except BytecodeError (Array G × EvalState) :=
  match runOps t fuel b.ops st 0 with
  | .error e => .error e
  | .ok st' => evalCtrl t fuel b.ctrl st'
termination_by (fuel, sizeOf b, 4)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (apply Prod.Lex.right; apply Prod.Lex.left; exact Block.sizeOf_ops_lt _)
    | (apply Prod.Lex.right; apply Prod.Lex.left; exact Block.sizeOf_ctrl_lt _)
    | omega

def evalCtrl (t : Bytecode.Toplevel) (fuel : Nat)
    (ctrl : Ctrl) (st : EvalState) : Except BytecodeError (Array G × EvalState) :=
  match ctrl with
  | .return _ outs =>
    match readIdxs st outs with
    | .error e => .error e
    | .ok gs   => .ok (gs, st)
  | .yield _ outs =>
    match readIdxs st outs with
    | .error e => .error e
    | .ok gs   => .ok (gs, st)
  | .match scrutIdx cases defaultBlock =>
    match readIdx st scrutIdx with
    | .error e => .error e
    | .ok scrut =>
      evalMatchArm t fuel cases defaultBlock scrut st
  | .matchContinue scrutIdx cases defaultBlock _outputSize _sharedAux _sharedLookups cont =>
    match readIdx st scrutIdx with
    | .error e => .error e
    | .ok scrut =>
      match evalMatchArm t fuel cases defaultBlock scrut st with
      | .error e => .error e
      | .ok (gs, st') =>
        -- The match acts as an atomic operation from the continuation's
        -- perspective: any values a case pushed onto `map` are local to the
        -- case and must not leak into the continuation's namespace. Restore
        -- the pre-match `map` and append only the yield outputs.
        let stMerged : EvalState := { st' with map := st.map ++ gs }
        evalBlock t fuel cont stMerged
termination_by (fuel, sizeOf ctrl, 3)
decreasing_by all_goals first | decreasing_tactic | omega

/-- Walk match cases structurally; picks the first arm whose discriminant
equals `scrut`, falling back to `defaultBlock` if none match. Structured as a
separate helper so each recursive step is structurally smaller than `cases`,
which lets `Array.sizeOf_get` discharge the termination goal when we call
`evalBlock` on an arm's `Block`. -/
def evalMatchArm (t : Bytecode.Toplevel) (fuel : Nat)
    (cases : Array (G × Block)) (defaultBlock : Option Block)
    (scrut : G) (st : EvalState) (i : Nat := 0) :
    Except BytecodeError (Array G × EvalState) :=
  if h : i < cases.size then
    if cases[i].fst == scrut then evalBlock t fuel cases[i].snd st
    else evalMatchArm t fuel cases defaultBlock scrut st (i + 1)
  else evalDefaultBlock t fuel defaultBlock st
termination_by (fuel, sizeOf cases + sizeOf defaultBlock, 2 + (cases.size - i))
decreasing_by
  all_goals (
    clean_wf
    first
    | decreasing_tactic
    | (apply Prod.Lex.right
       apply Prod.Lex.left
       first
         | exact sizeOf_caseBlock_lt cases defaultBlock i ‹_›
         | (cases cases with | mk l => show sizeOf defaultBlock < 1 + sizeOf l + sizeOf defaultBlock; omega))
    | omega)

/-- Dispatch on the optional default block at the end of a `.match` arm. -/
def evalDefaultBlock (t : Bytecode.Toplevel) (fuel : Nat)
    (defaultBlock : Option Block) (st : EvalState) :
    Except BytecodeError (Array G × EvalState) :=
  match defaultBlock with
  | some block => evalBlock t fuel block st
  | none       => .error .unreachableAfterLayout
termination_by (fuel, sizeOf defaultBlock, 1)
decreasing_by
  all_goals simp_wf
  all_goals first
    | decreasing_tactic
    | (simp_arith; omega)
    | omega

end

/-! ## Top-level entry -/

/-- Run a function by index with the given flat args and IO buffer. -/
def runFunction (t : Bytecode.Toplevel) (funIdx : FunIdx) (args : Array G)
    (ioBuffer : IOBuffer) (fuel : Nat) :
    Except BytecodeError (Array G × IOBuffer) :=
  if h : funIdx < t.functions.size then
    let f := t.functions[funIdx]
    if f.layout.inputSize != args.size then
      .error (.arityMismatch funIdx)
    else
      let st : EvalState := { map := args, ioBuffer }
      match evalBlock t fuel f.body st with
      | .error e => .error e
      | .ok (outs, st') => .ok (outs, st'.ioBuffer)
  else .error (.invalidFunIdx funIdx)

end Bytecode.Eval

end Aiur

end -- @[expose] section
end
