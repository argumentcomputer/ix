module
public import Ix.Aiur.Stages.Bytecode
public import Ix.Aiur.Semantics.BytecodeFfi
public import Ix.IndexMap

/-!
Lean-native bytecode reference evaluator.

Mirrors `crates/aiur/src/execute.rs` in big-step form:
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

/-- Width-bucketed memory, matching Rust's `QueryRecord.memory_queries`.
Outer key is the width; each bucket is an ordered map from flat-width arrays of
field elements to unit (the index within the bucket is its insertion order). -/
abbrev MemoryBuckets := IndexMap Nat (IndexMap (Array G) Unit)

structure EvalState where
  map      : Array G := #[]
  memory   : MemoryBuckets := default
  ioBuffer : IOBuffer
  deriving Inhabited

/-- Opaque `Repr` so `BytecodeError` (whose `earlyReturn` sentinel carries
the state) can keep its derived instance; the state itself is not printable. -/
instance : Repr EvalState := ⟨fun _ _ => .text "<EvalState>"⟩

/-- Tagged errors — small enum, no messages, for proof statements.

The `earlyReturn` case is NOT an error: it is the escape channel for
`Ctrl.return`, which exits the enclosing FUNCTION — unwinding past any
pending `matchContinue` continuations — while `Ctrl.yield` feeds the
nearest continuation. It rides the `Except` error track so every
intermediate frame propagates it for free, and is unwrapped back into a
normal result at the function boundary (`evalOp .call` and
`runFunction`) — mirroring the Rust executor's continuation-stack
truncation on `Ctrl::Return`. -/
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
  | u8RangeCheckFailed
  | unconstrainedBigUintDivModFailed
  | earlyReturn (outs : Array G) (st : EvalState)
  deriving Repr, Inhabited

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

/-! ## `List<U64>` limb chains (`unconstrainedBigUintDivMod`)

Mirrors `read_klimbs_u64` / `build_klimbs_u64` in `crates/aiur/src/execute.rs`:
nodes live in the width-10 memory bucket with the standard tagged-enum
layout `[tag, byte0..byte7, next_ptr]` — tag 0 = Cons, tag 1 = Nil, bytes
little-endian within the u64 limb. -/

/-- Walk a limb chain from `ptr`, returning the limbs head-first. `steps`
bounds the walk: a chain longer than the width-10 bucket must revisit a
pointer, i.e. a malformed cycle. -/
def readLimbChain (st : EvalState) : Nat → Nat →
    Except BytecodeError (List (Array G))
  | 0, _ => .error .unconstrainedBigUintDivModFailed
  | steps+1, ptr => do
    let vs ← memLoad st 11 ptr
    -- Slot 0 is the store-site type id, skipped unverified (input and
    -- advice lists carry different ids by design).
    match vs[0]?, vs[1]?, vs[10]? with
    | some _nodeTid, some tag, some next =>
      if tag == 1 then pure []
      else if tag == 0 then
        let bytes := vs.extract 2 10
        if bytes.size == 8 && bytes.all (·.val < 256) then do
          let rest ← readLimbChain st steps next.val.toNat
          pure (bytes :: rest)
        else .error .unconstrainedBigUintDivModFailed
      else .error .unconstrainedBigUintDivModFailed
    | _, _, _ => .error .unconstrainedBigUintDivModFailed

/-- Build a limb chain from head-first `limbs`, returning the head pointer.
Same insertion order as the Rust builder (Nil first, then limbs in reverse),
so freshly-created pointer indices agree; `memStore` content-dedups like
`QueryMap` does. -/
def buildLimbChain (st : EvalState) (tid : G) : List (Array G) → EvalState × Nat
  | [] => memStore st (#[tid, 1] ++ Array.replicate 9 0)
  | limb :: rest =>
    let (st', restPtr) := buildLimbChain st tid rest
    memStore st' (#[tid, 0] ++ limb ++ #[.ofNat restPtr])

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
          -- Function boundary: an `earlyReturn` escaping the callee's body
          -- is its normal return value.
          match evalBlock t fuel f.body innerSt with
          | .error (.earlyReturn outs innerSt') | .ok (outs, innerSt') =>
            if outs.size != outputSize then
              .error .callOutputSizeMismatch
            else
              pure (appendMap (setIoBuffer { st with memory := innerSt'.memory }
                                            innerSt'.ioBuffer) outs)
          | .error e => .error e
    else .error (.invalidFunIdx fi)
  | .store vals => do
    let argGs ← readIdxs st vals
    let (st', idx) := memStore st argGs
    pure (pushMap st' (.ofNat idx))
  | .load size ptr => do
    let ptrG ← readIdx st ptr
    let vs ← memLoad st size ptrG.val.toNat
    pure (appendMap st vs)
  | .assertEq as bs _ => do
    let aGs ← readIdxs st as
    let bGs ← readIdxs st bs
    if aGs == bGs then .ok st else .error .assertFailed
  | .ioGetInfo channelIdx keyIdxs => do
    let channelG ← readIdx st channelIdx
    let keyGs ← readIdxs st keyIdxs
    match st.ioBuffer.map[(channelG, keyGs)]? with
    | some info =>
      let st1 := pushMap st (.ofNat info.idx)
      pure (pushMap st1 (.ofNat info.len))
    | none => .error .ioKeyNotFound
  | .ioSetInfo channelIdx keyIdxs idxIdx lenIdx => do
    let channelG ← readIdx st channelIdx
    let keyGs ← readIdxs st keyIdxs
    let iG ← readIdx st idxIdx
    let lG ← readIdx st lenIdx
    if st.ioBuffer.map.contains (channelG, keyGs) then
      .error .ioKeyAlreadySet
    else
      let info : IOKeyInfo := ⟨iG.val.toNat, lG.val.toNat⟩
      let newMap := st.ioBuffer.map.insert (channelG, keyGs) info
      pure (setIoBuffer st { st.ioBuffer with map := newMap })
  | .ioRead channelIdx idxIdx len => do
    let channelG ← readIdx st channelIdx
    let iG ← readIdx st idxIdx
    let start := iG.val.toNat
    let arena := st.ioBuffer.data.getD channelG #[]
    if start + len > arena.size then
      .error .ioReadOoB
    else
      pure (appendMap st (arena.extract start (start + len)))
  | .ioWrite channelIdx dataIdxs => do
    let channelG ← readIdx st channelIdx
    let dataGs ← readIdxs st dataIdxs
    let arena := st.ioBuffer.data.getD channelG #[]
    let newData := st.ioBuffer.data.insert channelG (arena ++ dataGs)
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
  | .u8Mul a b => do
    let x ← readIdx st a; let y ← readIdx st b
    let prod := x.val.toUInt8.toNat * y.val.toUInt8.toNat
    let st1 := pushMap st (G.ofUInt8 prod.toUInt8)
    pure (pushMap st1 (G.ofUInt8 (prod / 256).toUInt8))
  | .u8XorSplit7 a b => do
    let x ← readIdx st a; let y ← readIdx st b; let z := x.val.toUInt8 ^^^ y.val.toUInt8
    pure (pushMap (pushMap st (G.ofUInt8 (z >>> 7))) (G.ofUInt8 (z <<< 1)))
  | .u8XorSplit4 a b => do
    let x ← readIdx st a; let y ← readIdx st b; let z := x.val.toUInt8 ^^^ y.val.toUInt8
    pure (pushMap (pushMap st (G.ofUInt8 (z >>> 4))) (G.ofUInt8 (z <<< 4)))
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
  | .unconstrainedU32Add a b => do
    let pack (idxs : Array Nat) := idxs.toList.zipIdx.foldl
      (fun n (idx, i) => n + (st.map[idx]?.getD 0).val.toNat * 256 ^ i) 0
    let sum := pack a + pack b
    let bytes := #[0, 1, 2, 3].map fun i => G.ofNat ((sum / 256 ^ i) % 256)
    pure (pushMap (appendMap st bytes) (.ofNat (sum / 0x100000000)))
  | .unconstrainedU32Add3 a b c => do
    let pack (idxs : Array Nat) := idxs.toList.zipIdx.foldl
      (fun n (idx, i) => n + (st.map[idx]?.getD 0).val.toNat * 256 ^ i) 0
    let sum := pack a + pack b + pack c
    let bytes := #[0, 1, 2, 3].map fun i => G.ofNat ((sum / 256 ^ i) % 256)
    pure (pushMap (appendMap st bytes) (.ofNat (sum / 0x100000000)))
  | .u32ToField bytes => do
    let word := bytes.toList.zipIdx.foldl
      (fun n (idx, i) => n + (st.map[idx]?.getD 0).val.toNat * 256 ^ i) 0
    pure (pushMap st (.ofNat word))
  | .u8RangeCheck a b => do
    -- No value pushed: the `u8` results alias the inputs. Fails if either is
    -- outside `[0, 256)` (exactly what the byte-chip lookup enforces).
    let x ← readIdx st a; let y ← readIdx st b
    if x.val < 256 && y.val < 256 then .ok st else .error .u8RangeCheckFailed
  | .unconstrainedBigUintDivMod tag a b => do
    let tid ← readIdx st tag
    let aPtr ← readIdx st a
    let bPtr ← readIdx st b
    -- Walk bound: the width-11 bucket size plus one (see `readLimbChain`).
    let bound := (st.memory.getByKey 11 |>.map (·.size) |>.getD 0) + 1
    let aLimbs ← readLimbChain st bound aPtr.val.toNat
    let bLimbs ← readLimbChain st bound bPtr.val.toNat
    let aVal := limbsVal aLimbs
    let bVal := limbsVal bLimbs
    -- `Nat` division matches the runtime's `b = 0 → (0, a)` convention.
    let (st1, qPtr) := buildLimbChain st tid (natToLimbsLE (aVal / bVal))
    let (st2, rPtr) := buildLimbChain st1 tid (natToLimbsLE (aVal % bVal))
    pure (pushMap (pushMap st2 (.ofNat qPtr)) (.ofNat rPtr))
  | .unconstrainedGToBytes idx => do
    let g ← readIdx st idx
    pure (appendMap st (Array.ofFn g.toLeBytes))
  | .unconstrainedGInverse idx => do
    let g ← readIdx st idx
    pure (pushMap st g.inverse)
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
    -- Function-level return: escape via the `earlyReturn` sentinel so a
    -- pending `matchContinue` continuation is skipped (Rust truncates the
    -- continuation stack here). Unwrapped at the function boundary.
    match readIdxs st outs with
    | .error e => .error e
    | .ok gs   => .error (.earlyReturn gs st)
  | .yield _ outs =>
    -- Continuation-level yield: normal result, consumed by the nearest
    -- enclosing `matchContinue`.
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
      | .error (.earlyReturn outs st') | .ok (outs, st') => .ok (outs, st'.ioBuffer)
      | .error e => .error e
  else .error (.invalidFunIdx funIdx)

end Bytecode.Eval

end Aiur

end -- @[expose] section
end
