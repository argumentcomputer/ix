import Std.Data.HashMap
import Ix.Aiur.Ir -- Assuming the IR module contains Ctrl, FuncIdx, etc.

/-- `Value` defines actual primitive types supported by Eiur -/
inductive Value
  | u64 : UInt64 → Value
  | bool : Bool → Value
deriving BEq, Hashable, Repr

instance : Inhabited Value where
  default := Value.u64 0

/--
`QueryResult` is an output of the particular function. The `TopLevel` may contain multiple
functions, and for each one executed, it generates one `QueryResult` objects that contains
output for a given function
-/
structure QueryResult where
  values : Array Value
  multiplicity : Nat
deriving BEq, Repr

instance : Inhabited QueryResult where
  default := { values := Array.empty, multiplicity := 0 }

/--
`QueryRecord` is a collection of `QueryResult` objects that can be referenced by the input tuple
used while invoking `TopLevel` execution algorithm
-/
structure QueryRecord where
  queries : Array (Std.HashMap (Array Value) QueryResult)
deriving Inhabited

structure ExecutionState where
  map : Array Value
  record : QueryRecord
deriving Inhabited

inductive ExecutionError where
  | custom : String → ExecutionError
  | expectedU64 : ExecutionError
  | expectedBool : ExecutionError
deriving Inhabited

abbrev ExecutionM a := StateT ExecutionState (Except ExecutionError) a

def Value.add (a: Value) (b: Value): Except ExecutionError Value :=
  match a, b with
  | .u64 a, .u64 b => pure $ .u64 (a + b)
  | _, _ => throw .expectedU64
def Value.sub (a: Value) (b: Value): Except ExecutionError Value :=
  match a, b with
  | .u64 a, .u64 b => pure $ .u64 (a - b)
  | _, _ => throw .expectedU64
def Value.mul (a: Value) (b: Value): Except ExecutionError Value :=
  match a, b with
  | .u64 a, .u64 b => pure $ .u64 (a * b)
  | _, _ => throw .expectedU64
def Value.lt (a: Value) (b: Value): Except ExecutionError Value :=
  match a, b with
  | .u64 a, .u64 b => pure $ .bool (a < b)
  | _, _ => throw .expectedU64
def Value.and (a: Value) (b: Value): Except ExecutionError Value :=
  match a, b with
  | .bool a, .bool b => pure $ .bool (a.and b)
  | _, _ => throw .expectedU64
def Value.xor (a: Value) (b: Value): Except ExecutionError Value :=
  match a, b with
  | .bool a, .bool b => pure $ .bool (a.xor b)
  | _, _ => throw .expectedU64

def Op.execute (toplevel: Toplevel) (op: Op) : ExecutionM Unit :=
  match op with
  | .call f args size =>
    modify (fun s =>
      let args := args.map (fun arg => s.map[arg.toNat]!)
      -- let query? := s.record.queries[f.toNat]!.get? args
      s
    )
    -- let query? := state.record.queries[f.toNat]!.get? args
    -- match query? with
    -- | .some query => 
    --   let query := { query with multiplicity := query.multiplicity + 1 }
    --   -- modify (fun s => { s with record := s.record.queries[f.toNat]!.get? })
    --   pure ()
    -- | .none => pure ()
  | .prim (.u64 p) => modify (fun s => { s with map := s.map.push (.u64 p) })
  | .prim (.bool p) => modify (fun s => { s with map := s.map.push (.bool p) })
  | .add a b => do
    let map := (← get).map
    let a := map[a.toNat]!
    let b := map[b.toNat]!
    let c ← a.add b
    modify (fun s => { s with map := s.map.push c })
  | .sub a b => do
    let map := (← get).map
    let a := map[a.toNat]!
    let b := map[b.toNat]!
    let c ← a.sub b
    modify (fun s => { s with map := s.map.push c })
  | .mul a b => do
    let map := (← get).map
    let a := map[a.toNat]!
    let b := map[b.toNat]!
    let c ← a.mul b
    modify (fun s => { s with map := s.map.push c })
  | .lt a b => do
    let map := (← get).map
    let a := map[a.toNat]!
    let b := map[b.toNat]!
    let c ← a.lt b
    modify (fun s => { s with map := s.map.push c })
  | .and a b => do
    let map := (← get).map
    let a := map[a.toNat]!
    let b := map[b.toNat]!
    let c ← a.and b
    modify (fun s => { s with map := s.map.push c })
  | .xor a b => do
    let map := (← get).map
    let a := map[a.toNat]!
    let b := map[b.toNat]!
    let c ← a.xor b
    modify (fun s => { s with map := s.map.push c })

def Block.execute (block: Block) (toplevel: Toplevel) : ExecutionM Unit := do
  block.ops.forM (Op.execute toplevel) 
  match block.ctrl with
  | .if _ _ _ => sorry
  | .return _ _ => sorry

def execute (toplevel: Toplevel) (func_idx: Nat) (input: Array Value) : Except ExecutionError ExecutionState :=
  let func := toplevel.functions[func_idx]!
  let record := default
  let state := ExecutionState.mk input record
  (·.2) <$> StateT.run (Block.execute func.body toplevel) state

