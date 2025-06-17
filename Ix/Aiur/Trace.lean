import Ix.Archon.TowerField
import Ix.Aiur.Term
import Ix.Aiur.Execute
import Ix.Aiur.Bytecode

-- TODO: generic definition
def Aiur.MultiplicativeGenerator : UInt64 := 0x070f870dcd9c1d88

namespace Aiur.Circuit


structure FunctionTrace where
  numQueries : Nat
  inputs: Array (Array UInt64)
  outputs: Array (Array UInt64)
  u1Auxiliaries: Array (Array Bool)
  u8Auxiliaries: Array (Array UInt8)
  u64Auxiliaries: Array (Array UInt64)
  selectors: Array (Array Bool)
  multiplicity: Array UInt64
  deriving Inhabited

structure MemoryTrace where
  numQueries : Nat
  multiplicity: Array UInt64
  values: Array (Array UInt64)
  deriving Inhabited

structure ColumnIndex where
  u1Auxiliary : Nat
  u8Auxiliary : Nat
  u64Auxiliary : Nat
  input : Nat
  output : Nat
  deriving Inhabited

inductive Query where
| Func : FuncIdx → Array UInt64 → Query
| Mem : Nat → Array UInt64 → Query
deriving BEq, Hashable

structure AiurTrace where
  functions : Array FunctionTrace
  add : Array UInt64 × Array UInt64
  mul : Array UInt64 × Array UInt64
  mem : Array MemoryTrace

def FunctionTrace.blank (layout : Layout) (height : Nat := 0) : FunctionTrace :=
  let arr1 := Array.mkArray height false
  let arr8 := Array.mkArray height 0
  let arr64 := Array.mkArray height 0
  let inputs := Array.mkArray layout.inputs arr64
  let outputs := Array.mkArray layout.outputs arr64
  let u1Auxiliaries := Array.mkArray layout.u1Auxiliaries arr1
  let u8Auxiliaries := Array.mkArray layout.u8Auxiliaries arr8
  let u64Auxiliaries := Array.mkArray layout.u64Auxiliaries arr64
  let selectors := Array.mkArray layout.selectors arr1
  let multiplicity := arr64
  let numQueries := 0
  { numQueries, inputs, outputs, u1Auxiliaries, u8Auxiliaries, u64Auxiliaries, selectors, multiplicity }

end Aiur.Circuit

namespace Aiur.Bytecode

structure TraceState where
  row : Nat
  trace : Circuit.FunctionTrace
  map : Array UInt64
  col : Circuit.ColumnIndex
  prevCounts : Std.HashMap Circuit.Query UInt64
  deriving Inhabited

abbrev TraceM := ReaderT QueryRecord (StateM TraceState)

def TraceM.run (query : QueryRecord) (initialState : TraceState) (action : TraceM A) : A × TraceState :=
  StateT.run (ReaderT.run action query) initialState

def TraceM.pushVar (c : UInt64) : TraceM Unit :=
  modify fun s => { s with map := s.map.push c }

def TraceM.pushU1 (b : Bool) : TraceM Unit :=
  modify fun s =>
    let trace := { s.trace with u1Auxiliaries := s.trace.u1Auxiliaries.modify s.col.u1Auxiliary fun col => col.set! s.row b }
    let col := { s.col with u1Auxiliary := s.col.u1Auxiliary + 1 }
    { s with trace, col }

def TraceM.pushU64 (b : UInt64) : TraceM Unit :=
  modify fun s =>
    let trace := { s.trace with u64Auxiliaries := s.trace.u64Auxiliaries.modify s.col.u64Auxiliary fun col => col.set! s.row b }
    let col := { s.col with u64Auxiliary := s.col.u64Auxiliary + 1 }
    { s with trace, col }

def TraceM.pushInput (b : UInt64) : TraceM Unit :=
  modify fun s =>
    let trace := { s.trace with inputs := s.trace.inputs.modify s.col.input fun col => col.set! s.row b }
    let col := { s.col with u64Auxiliary := s.col.input + 1 }
    { s with trace, col }

def TraceM.pushOutput (b : UInt64) : TraceM Unit :=
  modify fun s =>
    let trace := { s.trace with outputs := s.trace.outputs.modify s.col.output fun col => col.set! s.row b }
    let col := { s.col with u64Auxiliary := s.col.output + 1 }
    { s with trace, col }

def TraceM.pushCount (query : Circuit.Query) : TraceM Unit := do
  modify fun s =>
    let update maybe := match maybe with
      | .none => .some 1
      | .some prev =>
        .some $ Archon.mulUInt64InBinaryField prev MultiplicativeGenerator
    let prevCounts := s.prevCounts.alter query update
    { s with prevCounts }

def TraceM.loadMemMap (len : Nat) : TraceM QueryMap := do
  let queries := (← read).memQueries
  let idx := (queries.findIdx? (·.fst == len)).get!
  pure queries[idx]!.snd

def TraceM.setSelector (sel : SelIdx) : TraceM Unit :=
  modify fun s =>
    let trace := { s.trace with selectors := s.trace.selectors.modify sel fun col => col.set! s.row true }
    { s with trace }

def TraceM.populateIO
  (inputValues : Array UInt64)
  (result : QueryResult)
: TraceM Unit := do
  inputValues.forM pushInput
  result.values.forM pushOutput
  modify fun s =>
    let m := Archon.powUInt64InBinaryField MultiplicativeGenerator result.multiplicity
    let trace := { s.trace with multiplicity := s.trace.multiplicity.set! s.row m }
    { s with trace }

mutual
partial def Block.populateRow (block : Block) : TraceM Unit := do
  block.ops.forM fun op => op.populateRow
  block.ctrl.populateRow

partial def Ctrl.populateRow : Ctrl → TraceM Unit
| .ret sel _ => TraceM.setSelector sel
| .if b t f => do
  let val := (← get).map[b]!
  if val != 0
  then
    TraceM.pushU64 $ Archon.invUInt64InBinaryField val
    t.populateRow
  else f.populateRow
| .match v branches defaultBranch => do
  let val := (← get).map[v]!
  match branches.find? fun branch => branch.fst == val with
  | some branch => branch.snd.populateRow
  | none =>
    branches.forM fun (case, _) =>
      TraceM.pushU64 $ Archon.invUInt64InBinaryField (val.xor case)
    defaultBranch.get!.populateRow

partial def Op.populateRow : Op → TraceM Unit
| .prim a => TraceM.pushVar a.toU64
| .xor a b => do
  let map := (← get).map
  let c := map[a]!.xor map[b]!
  TraceM.pushVar c
| .and a b => do
  let map := (← get).map
  let c := map[a]!.land map[b]!
  TraceM.pushU1 (c == 1)
  TraceM.pushVar c
| .add a b => do
  let map := (← get).map
  let a := map[a]!
  let c := a + map[b]!
  let overflow := c < a
  TraceM.pushU64 c
  TraceM.pushU1 overflow
  TraceM.pushVar c
| .sub c b => do
  let map := (← get).map
  let c := map[c]!
  let a := c - map[b]!
  let overflow := c < a
  TraceM.pushU64 c
  TraceM.pushU1 overflow
  TraceM.pushVar c
| .mul a b => do
  let map := (← get).map
  let c := map[a]! * map[b]!
  TraceM.pushU64 c
  TraceM.pushVar c
| .lt  c b => do
  let map := (← get).map
  let c := map[c]!
  let a := c.sub map[b]!
  let overflow := c < a
  TraceM.pushU64 c
  TraceM.pushU1 overflow
  TraceM.pushVar (if overflow then 1 else 0)
| .store values => do
  let len := values.size
  let mem ← TraceM.loadMemMap len
  let map := (← get).map
  let values := values.map fun value => map[value]!
  let result := (mem.getByKey values).get!
  result.values.forM fun value => do
    TraceM.pushU64 value
    TraceM.pushVar value
  TraceM.pushCount (.Mem len values)
| .load len ptr => do
  let mem ← TraceM.loadMemMap len
  let map := (← get).map
  let ptr := map[ptr]!
  let (values, _) := (mem.getByIdx ptr.toNat).get!
  values.forM fun value => do
    TraceM.pushU64 value
    TraceM.pushVar value
  TraceM.pushCount (.Mem len values)
| .call fIdx args _ => do
  let map := (← get).map
  let args := args.map fun arg => map[arg]!
  let output := ((← read).getFuncResult fIdx args).get!
  output.forM fun value => do
    TraceM.pushU64 value
    TraceM.pushVar value
  TraceM.pushCount (.Func fIdx args)
| .trace _ _ => pure ()
| _ => panic! "TODO"
end

def Function.populateTrace
  (function : Function)
  (funcMap : QueryMap)
  (layout : Circuit.Layout)
: TraceM Unit := do
  let height := if funcMap.size == 0 then 0 else funcMap.size.nextPowerOfTwo.max 128
  modify fun s => { s with trace := Circuit.FunctionTrace.blank layout height }
  funcMap.foldlM (init := ()) fun _ (inputs, result) => do
    modify fun s => { s with map := inputs }
    TraceM.populateIO inputs result
    function.body.populateRow

def QueryMap.generateTrace (map : QueryMap) : Circuit.MemoryTrace :=
  let trace := map.foldl (init := default) fun acc (_, result) =>
    let multiplicity := acc.multiplicity.push (Archon.powUInt64InBinaryField MultiplicativeGenerator result.multiplicity)
    let values := acc.values.push result.values
    let numQueries := acc.numQueries + 1
    { multiplicity, values, numQueries }
  trace

def Toplevel.generateTraces
  (toplevel : Toplevel)
  (queries : QueryRecord)
: Circuit.AiurTrace :=
  let action := do
    let mut traces := #[]
    for i in [0:toplevel.functions.size] do
      let function := toplevel.functions[i]!
      let functionMap := queries.funcQueries[i]!
      let layout := toplevel.layouts[i]!
      function.populateTrace functionMap layout
      let trace := (← get).trace
      traces := traces.push trace
    pure traces
  let functions := (action.run queries default).fst
  let add := queries.addQueries.unzip
  let mul := queries.mulQueries.unzip
  let mem := queries.memQueries.map fun (_, map) => map.generateTrace
  { functions, add, mul, mem }

end Aiur.Bytecode
