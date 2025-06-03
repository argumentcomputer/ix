import Ix.Aiur.Term
import Ix.Aiur.Execute
import Ix.Aiur.Bytecode

namespace Aiur
namespace Circuit

structure Row where
  numQueries : Nat
  inputs: Array UInt64
  outputs: Array UInt64
  u1Auxiliaries: Array Bool
  u8Auxiliaries: Array UInt8
  u64Auxiliaries: Array UInt64
  selectors: Array Bool
  multiplicity: UInt64

structure Trace where
  numQueries : Nat
  rows : Array Row

structure ColumnIndex where
  u1Auxiliary : Nat
  u8Auxiliary : Nat
  u64Auxiliary : Nat

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

abbrev TraceM := ReaderT QueryRecord (StateM TraceState)

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
      | .some prev => panic! "TODO"
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
    let inv := panic! "TODO"
    TraceM.pushU64 inv
    t.populateRow
  else f.populateRow
| .match v branches defaultBranch => do
  let val := (← get).map[v]!
  match branches.find? fun branch => branch.fst == val with
  | some branch => branch.snd.populateRow
  | none =>
    branches.forM fun (case, _) =>
      let inv := panic! "TODO"
      TraceM.pushU64 inv
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

end Bytecode
end Aiur
