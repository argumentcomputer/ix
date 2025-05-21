import Ix.IndexMap
import Ix.Aiur.Bytecode

namespace Aiur.Bytecode

structure QueryResult where
  values : Array UInt64
  multiplicity : UInt64
  deriving Inhabited

instance : ToString QueryResult where
  toString x := s!"{x.multiplicity}×{x.values}"

@[inline] def QueryResult.bumpMultiplicity (res : QueryResult) : QueryResult :=
  { res with multiplicity := res.multiplicity + 1 }

abbrev QueryMap := IndexMap (Array UInt64) QueryResult

structure QueryRecord where
  funcQueries : Array QueryMap
  memQueries : Array $ Nat × QueryMap
  addQueries : Array $ UInt64 × UInt64
  mulQueries : Array $ UInt64 × UInt64

namespace QueryRecord

def new (toplevel : Toplevel) : QueryRecord :=
  let funcQueries := toplevel.functions.map fun _ => default
  let memQueries := toplevel.memWidths.map fun width => (width, default)
  ⟨funcQueries, memQueries, #[], #[]⟩

def getFuncResult (record : QueryRecord) (funcIdx : FuncIdx) (input : Array UInt64) :
    Option (Array UInt64) := do
  let queryMap ← record.funcQueries[funcIdx.toNat]?
  let queryResult ← queryMap.getByKey input
  some queryResult.values

end QueryRecord

structure ExecuteCtx where
  toplevel : Toplevel
  funcIdx : Nat
  args : Array UInt64

structure ExecuteState where
  record : QueryRecord
  map : Array UInt64

namespace ExecuteState

def updateForFunc (stt : ExecuteState) (funcIdx : Nat) (newQueryMap : QueryMap)
    (mapFn : Array UInt64 → Array UInt64) : ExecuteState :=
  let newFuncQueries := stt.record.funcQueries.set! funcIdx newQueryMap
  { stt with
      record := { stt.record with funcQueries := newFuncQueries }
      map := mapFn stt.map }

def updateForMem (stt : ExecuteState) (memMapIdx : MemIdx) (len : Nat) (newQueryMap : QueryMap)
    (mapFn : Array UInt64 → Array UInt64) : ExecuteState :=
  let newMemQueries := stt.record.memQueries.set! memMapIdx (len, newQueryMap)
  { stt with
      record := { stt.record with memQueries := newMemQueries }
      map := mapFn stt.map }

end ExecuteState

abbrev ExecuteM := ReaderT ExecuteCtx $ StateM ExecuteState

@[inline] def pushVal (x : UInt64) : ExecuteM Unit :=
  modify fun stt => { stt with map := stt.map.push x }

@[inline] def getVal (i : ValIdx) : ExecuteM UInt64 :=
  get >>= (pure ·.map[i]!)

@[inline] def modifyRecord (f : QueryRecord → QueryRecord) : ExecuteM Unit :=
  modify fun stt => { stt with record := f stt.record }

@[inline] def getMemMapIdx (len : Nat) : ExecuteM $ Nat × QueryMap := do
  let stt ← get
  let idxOpt := stt.record.memQueries.findIdx? (·.fst == len)
  let idx := idxOpt.get!
  let queryMap := stt.record.memQueries[idx]!.snd
  pure (idx, queryMap)

mutual

partial def Block.execute (block : Block) : ExecuteM Unit := do
  block.ops.forM Op.execute
  block.ctrl.execute

partial def Op.execute : Op → ExecuteM Unit
  | .prim (.u1 u) | .prim (.u8 u) | .prim (.u16 u) | .prim (.u32 u) => pushVal u.toUInt64
  | .prim (.u64 u) => pushVal u
  | .add a b => do
    let a ← getVal a
    let b ← getVal b
    pushVal (a + b)
    modifyRecord fun r => { r with addQueries := r.addQueries.push (a, b) }
  | .sub c b => do
    let c ← getVal c
    let b ← getVal b
    let a := c - b
    pushVal a
    modifyRecord fun r => { r with addQueries := r.addQueries.push (a, b) }
  | .lt c b => do
    let c ← getVal c
    let b ← getVal b
    let a := c - b
    let underflow := decide (c < b)
    pushVal underflow.toUInt64
    modifyRecord fun r => { r with addQueries := r.addQueries.push (a, b) }
  | .mul a b => do
    let a ← getVal a
    let b ← getVal b
    pushVal (a * b)
    modifyRecord fun r => { r with mulQueries := r.mulQueries.push (a, b) }
  | .and a b => do
    let a ← getVal a
    let b ← getVal b
    pushVal (a &&& b)
  | .xor a b => do
    let a ← getVal a
    let b ← getVal b
    pushVal (a ^^^ b)
  | .store values => do
    let len := values.size
    let (memMapIdx, memMap) ← getMemMapIdx len
    let values ← values.mapM getVal
    match memMap.getByKey values with
    | some res =>
      let newRes := res.bumpMultiplicity
      let newMemMap := memMap.insert values newRes
      modify (·.updateForMem memMapIdx len newMemMap (·.append newRes.values))
    | none =>
      let ptr := memMap.size.toUInt64
      let newRes := QueryResult.mk #[ptr] 1
      let newMemMap := memMap.insert values newRes
      modify (·.updateForMem memMapIdx len newMemMap (·.push ptr))
  | .load len ptr => do
    let stt ← get
    let ptr := stt.map[ptr]!
    let (memMapIdx, memMap) ← getMemMapIdx len
    let (values, res) := memMap.getByIdx ptr.toNat |>.get!
    let newRes := res.bumpMultiplicity
    let newMemMap := memMap.insert values newRes
    modify (·.updateForMem memMapIdx len newMemMap (·.append values))
  | .call funcIdx args _ => do
    let stt ← get
    let args := args.map (stt.map[·]!)
    let funcIdx := funcIdx.toNat
    let funcQueryMap := stt.record.funcQueries[funcIdx]!
    match funcQueryMap.getByKey args with
    | some res =>
      let newRes := res.bumpMultiplicity
      let newFuncQueryMap := funcQueryMap.insert args newRes
      modify (·.updateForFunc funcIdx newFuncQueryMap (·.append res.values))
    | none => do
      let map := stt.map
      set { stt with map := args }
      let ctx ← read
      let func := ctx.toplevel.functions[funcIdx]!
      withReader (fun ctx => { ctx with funcIdx, args }) func.body.execute
      let out := (← get).map
      let out := out.extract (start := out.size - func.outputSize)
      modify fun stt => { stt with map := map.append out }
  | .trace str args => do
    let stt ← get
    let args := args.map (stt.map[·]!)
    dbg_trace s!"{str}{args}"
  | _ => panic! "TODO"

partial def Ctrl.execute : Ctrl → ExecuteM Unit
  | .ret _ out => do
    let ctx ← read
    let funcIdx := ctx.funcIdx
    let stt ← get
    let funcQueryMap := stt.record.funcQueries[funcIdx]!
    let newRes := ⟨out.map (stt.map[·]!), 1⟩
    let newFuncQueryMap := funcQueryMap.insert ctx.args newRes
    let newFuncQueries := stt.record.funcQueries.set! funcIdx newFuncQueryMap
    set { stt with record := { stt.record with funcQueries := newFuncQueries } }
  | .if v tt ff => do if (← getVal v) != 0 then tt.execute else ff.execute
  | .match v branches defaultBranch => do
    let v ← getVal v
    match branches.find? fun branch => branch.fst == v with
    | some branch => branch.snd.execute
    | none => defaultBranch.get!.execute

end

def Toplevel.execute (toplevel : Toplevel) (funcIdx : FuncIdx) (input : Array UInt64) : QueryRecord :=
  let funcIdx := funcIdx.toNat
  let block := toplevel.functions[funcIdx]!.body
  let (_, stt) := block.execute.run ⟨toplevel, funcIdx, input⟩ |>.run ⟨.new toplevel, input⟩
  stt.record

end Aiur.Bytecode
