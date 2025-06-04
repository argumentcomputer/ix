import Ix.Archon.TowerField
import Ix.Aiur.Term
import Ix.Aiur.Execute
import Ix.Aiur.Bytecode

namespace Aiur

-- TODO: generic definition
def MultiplicativeGenerator : UInt64 := 0x070f870dcd9c1d88

namespace Circuit

structure Row where
  inputs: Array UInt64
  outputs: Array UInt64
  u1Auxiliaries: Array Bool
  u8Auxiliaries: Array UInt8
  u64Auxiliaries: Array UInt64
  selectors: Array Bool
  multiplicity: UInt64
  deriving Inhabited


def Row.blank
  (layout : Layout)
  (inputs : Array UInt64)
  (outputs : Array UInt64)
  (mult : UInt64)
: Row :=
  let u1Auxiliaries := Array.mkArray layout.u1Auxiliaries false
  let u8Auxiliaries := Array.mkArray layout.u8Auxiliaries 0
  let u64Auxiliaries := Array.mkArray layout.u64Auxiliaries 0
  let selectors := Array.mkArray layout.selectors false
  let multiplicity := Archon.powUInt64InBinaryField MultiplicativeGenerator mult
  {
    inputs,
    outputs,
    u1Auxiliaries,
    u8Auxiliaries,
    u64Auxiliaries,
    selectors,
    multiplicity
  }

structure Trace where
  numQueries : Nat
  rows : Array Row
  deriving Inhabited

structure ColumnIndex where
  u1Auxiliary : Nat
  u8Auxiliary : Nat
  u64Auxiliary : Nat
  deriving Inhabited

inductive Query where
| Func : FuncIdx → Array UInt64 → Query
| Mem : Nat → Array UInt64 → Query
deriving BEq, Hashable

end Circuit

namespace Bytecode

structure TraceState where
  row : Circuit.Row
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
    let row := { s.row with u1Auxiliaries := s.row.u1Auxiliaries.set! s.col.u1Auxiliary b }
    let col := { s.col with u1Auxiliary := s.col.u1Auxiliary + 1 }
    { s with row, col }

def TraceM.pushU64 (b : UInt64) : TraceM Unit :=
  modify fun s =>
    let row := { s.row with u64Auxiliaries := s.row.u64Auxiliaries.set! s.col.u64Auxiliary b }
    let col := { s.col with u64Auxiliary := s.col.u64Auxiliary + 1 }
    { s with row, col }

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
    let row := { s.row with selectors := s.row.selectors.set! sel true }
    { s with row }

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
: TraceM Circuit.Trace := do
  let numQueries := funcMap.size;
  let rows: Array Circuit.Row ← funcMap.foldlM (init := #[]) fun acc (inputs, result) => do
    modify fun s =>
      let map := inputs
      let row := .blank layout inputs result.values result.multiplicity
      { s with map, row }
    function.body.populateRow
    pure $ acc.push (← get).row
  pure { rows, numQueries }

def Toplevel.generateTraces
  (toplevel : Toplevel)
  (queries : QueryRecord)
: Array Circuit.Trace :=
  let action := (do
  let mut traces := #[]
  for i in [0:toplevel.functions.size] do
    let function := toplevel.functions[i]!
    let functionMap := queries.funcQueries[i]!
    let layout := toplevel.layouts[i]!
    let trace ← function.populateTrace functionMap layout
    traces := traces.push trace
  pure traces)
  (action.run queries default).fst

end Bytecode

end Aiur
