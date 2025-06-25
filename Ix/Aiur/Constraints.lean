import Ix.Aiur.Bytecode
import Ix.Archon.Circuit

namespace Aiur.Circuit

open Archon

structure Columns where
  inputs : Array OracleIdx
  outputs : Array OracleIdx
  u1Auxiliaries : Array OracleIdx
  u8Auxiliaries : Array OracleIdx
  u64Auxiliaries : Array OracleIdx
  multiplicity : OracleIdx
  selectors : Array OracleIdx

@[inline] def Columns.getSelector (columns : Columns) (selIdx : SelIdx) : OracleIdx :=
  columns.selectors[selIdx]!

def Columns.ofLayout (circuitModule : CircuitModule) (layout : Layout) : Columns × CircuitModule :=
  let (inputs, circuitModule) := foldCommit layout.inputs circuitModule (s!"input-{·}") .b64
  let (outputs, circuitModule) := foldCommit layout.outputs circuitModule (s!"output-{·}") .b64
  let (u1Auxiliaries, circuitModule) := foldCommit layout.u1Auxiliaries circuitModule (s!"u1-auxiliary-{·}") .b1
  let (u8Auxiliaries, circuitModule) := foldCommit layout.u8Auxiliaries circuitModule (s!"u8-auxiliary-{·}") .b8
  let (u64Auxiliaries, circuitModule) := foldCommit layout.u64Auxiliaries circuitModule (s!"u64-auxiliary-{·}") .b64
  let (multiplicity, circuitModule) := circuitModule.addCommitted "multiplicity" .b64 .base
  let (selectors, circuitModule) := foldCommit layout.selectors circuitModule (s!"selector-{·}") .b1
  let columns := { inputs, outputs, u1Auxiliaries, u8Auxiliaries, u64Auxiliaries, multiplicity, selectors }
  (columns, circuitModule)
where
  foldCommit n circuitModule nameFn tf :=
    n.fold (init := (#[], circuitModule)) fun i _ (oracles, circuitModule) =>
      let (oracleIdx, circuitModule) := circuitModule.addCommitted (nameFn i) tf .base
      (oracles.push oracleIdx, circuitModule)

inductive Channel
  | add
  | mul
  | func : FuncIdx → Channel
  | mem : Nat → Channel
  | gadget : GadgetIdx → Channel

structure Constraints where
  sharedConstraints : Array ArithExpr
  uniqueConstraints : Array ArithExpr
  sends : Array (Channel × ArithExpr × Array ArithExpr)
  requires : Array (Channel × ArithExpr × OracleIdx × Array ArithExpr)
  topmostSelector : ArithExpr
  io : Array OracleIdx
  multiplicity : OracleIdx

def blockSelector (block : Bytecode.Block) (columns : Columns) : ArithExpr :=
  let (min, max) := block.returnIdents
  match List.range' min (max - min) |>.map columns.getSelector with
  | [] => panic! s!"Invalid block identifiers: ({min}, {max})"
  | o :: os => os.foldl (init := o) fun acc o => acc + (.oracle o)

namespace Constraints

def new (function : Bytecode.Function) (layout : Layout) (columns : Columns) : Constraints :=
  { sharedConstraints := .mkArray layout.sharedConstraints 0
    uniqueConstraints := #[]
    sends := #[]
    requires := #[]
    topmostSelector := blockSelector function.body columns
    io := columns.inputs ++ columns.outputs
    multiplicity := columns.multiplicity }

@[inline] def pushUnique (constraints : Constraints) (expr : ArithExpr) : Constraints :=
  { constraints with uniqueConstraints := constraints.uniqueConstraints.push expr }

@[inline] def send (constraints : Constraints) (channel : Channel)
    (sel : ArithExpr) (args : Array ArithExpr) : Constraints :=
  { constraints with sends := constraints.sends.push (channel, sel, args) }

@[inline] def require (constraints : Constraints) (channel : Channel)
    (sel : ArithExpr) (prevIdx : OracleIdx) (args : Array ArithExpr) : Constraints :=
  { constraints with requires := constraints.requires.push (channel, sel, prevIdx, args) }

end Constraints

structure ConstraintState where
  constraintIndex : Nat
  u1AuxiliaryIndex : Nat
  u8AuriliaryIndex : Nat
  u64AuxiliaryIndex : Nat
  varMap : Array ArithExpr
  deriving Inhabited

namespace ConstraintState

@[inline] def pushVar (constraintState : ConstraintState) (expr : ArithExpr) : ConstraintState :=
  { constraintState with varMap := constraintState.varMap.push expr }

@[inline] def getVar (constraintState : ConstraintState) (idx : ValIdx) : ArithExpr :=
  constraintState.varMap[idx]!

def nextU1Column (constraintState : ConstraintState) (columns : Columns) : OracleIdx × ConstraintState :=
  let col := columns.u1Auxiliaries[constraintState.u1AuxiliaryIndex]!
  let constraintState' := { constraintState with
    u1AuxiliaryIndex := constraintState.u1AuxiliaryIndex + 1 }
  (col, constraintState')

def nextU64Column (constraintState : ConstraintState) (columns : Columns) : OracleIdx × ConstraintState :=
  let col := columns.u64Auxiliaries[constraintState.u64AuxiliaryIndex]!
  let constraintState' := { constraintState with
    u64AuxiliaryIndex := constraintState.u64AuxiliaryIndex + 1 }
  (col, constraintState')

def bindU1Column (constraintState : ConstraintState) (columns : Columns) : OracleIdx × ConstraintState :=
  let (col, constraintState') := constraintState.nextU1Column columns
  let constraintState'' := { constraintState' with varMap := constraintState'.varMap.push col }
  (col, constraintState'')

def bindU64Column (constraintState : ConstraintState) (columns : Columns) : OracleIdx × ConstraintState :=
  let (col, constraintState') := constraintState.nextU64Column columns
  let constraintState'' := { constraintState' with varMap := constraintState'.varMap.push col }
  (col, constraintState'')

end ConstraintState

structure CollectMState where
  constraints : Constraints
  constraintState : ConstraintState

namespace CollectMState

def addSharedConstraint (stt : CollectMState) (expr : ArithExpr) : CollectMState :=
  let constraintIndex := stt.constraintState.constraintIndex
  let sharedConstraints := stt.constraints.sharedConstraints.modify constraintIndex (· + expr)
  let constraintIndex := constraintIndex + 1
  { stt with
    constraints := { stt.constraints with sharedConstraints }
    constraintState := { stt.constraintState with constraintIndex } }

end CollectMState

abbrev CollectM := StateM CollectMState

@[inline] def modifyConstraintState (f : ConstraintState → ConstraintState) : CollectM Unit :=
  modify fun stt => { stt with constraintState := f stt.constraintState }

def collectOpConstraints (columns : Columns) (sel : ArithExpr) : Bytecode.Op → CollectM Unit
  | .prim (.u1 x)
  | .prim (.u8 x)
  | .prim (.u16 x)
  | .prim (.u32 x)
  | .prim (.u64 x) => modifyConstraintState (·.pushVar (.const (.ofNatWrap x.toNat)))
  | .add a b => modify fun stt =>
    let a := stt.constraintState.getVar a
    let b := stt.constraintState.getVar b
    -- 8 bytes of result
    let (c, constraintState) := stt.constraintState.bindU64Column columns
    -- 1 byte of carry, which is not bound
    let (carry, constraintState) := constraintState.nextU1Column columns
    let args := #[a, b, c, carry]
    let constraints := stt.constraints.send .add sel args
    ⟨constraints, constraintState⟩
  | .sub c b => modify fun stt =>
    -- `c - b = a` is equivalent to `a + b = c`.
    let c := stt.constraintState.getVar c
    let b := stt.constraintState.getVar b
    let (a, constraintState) := stt.constraintState.bindU64Column columns
    let (carry, constraintState) := constraintState.nextU1Column columns
    let args := #[.oracle a, b, c, carry]
    let constraints := stt.constraints.send .add sel args
    ⟨constraints, constraintState⟩
  | .lt c b => modify fun stt =>
    -- `c < b` is equivalent to `c - b` underflowing, which is
    -- equivalent to the addition in `a + b = c` overflowing
    -- Note that the result of the subtraction is not bound
    let c := stt.constraintState.getVar c
    let b := stt.constraintState.getVar b
    let (a, constraintState) := stt.constraintState.bindU64Column columns
    -- The carry is bound
    let (carry, constraintState) := constraintState.bindU1Column columns
    let args := #[.oracle a, b, c, carry]
    let constraints := stt.constraints.send .add sel args
    ⟨constraints, constraintState⟩
  | .mul a b => modify fun stt =>
    let a := stt.constraintState.getVar a
    let b := stt.constraintState.getVar b
    -- 8 bytes of result
    let (c, constraintState) := stt.constraintState.bindU64Column columns
    let args := #[a, b, c]
    let constraints := stt.constraints.send .mul sel args
    ⟨constraints, constraintState⟩
  | .xor a b => modify fun stt =>
    let a := stt.constraintState.getVar a
    let b := stt.constraintState.getVar b
    { stt with constraintState := stt.constraintState.pushVar (a + b) }
  | .and a b => modify fun stt =>
    let a := stt.constraintState.getVar a
    let b := stt.constraintState.getVar b
    let (c, constraintState) := stt.constraintState.bindU1Column columns
    let constraintState := constraintState.pushVar c
    let stt' := { stt with constraintState }
    stt'.addSharedConstraint $ sel * (c - a * b)
  | .store values => modify fun stt =>
    let (start, constraintState) := stt.constraintState.bindU64Column columns
    let args := #[.oracle start] ++ values.map constraintState.getVar
    let (req, constraintState) := constraintState.nextU64Column columns
    let constraints := stt.constraints.require (.mem values.size) sel req args
    ⟨constraints, constraintState⟩
  | .load len ptr => modify fun stt =>
    pushAndRequireArgs #[stt.constraintState.getVar ptr] stt len (.mem len)
  | .call f args outSize => modify fun stt =>
    pushAndRequireArgs (args.map stt.constraintState.getVar) stt outSize (.func f)
  | .ffi g args outSize => modify fun stt =>
    pushAndRequireArgs (args.map stt.constraintState.getVar) stt outSize (.gadget g)
  | _ => panic! "TODO"
where
  pushAndRequireArgs args stt n channel :=
    let (args, constraintState) := n.fold (init := (args, stt.constraintState))
      fun _ _ (args, constraintState) =>
        let (x, constraintState) := constraintState.bindU64Column columns
        (args.push x, constraintState)
    let (req, constraintState) := constraintState.nextU64Column columns
    let constraints := stt.constraints.require channel sel req args
    ⟨constraints, constraintState⟩

partial def collectBlockConstraints (block : Bytecode.Block) (columns : Columns) : CollectM Unit := do
  let sel := blockSelector block columns
  block.ops.forM (collectOpConstraints columns sel)
  match block.ctrl with
  | .if b t f =>
    let stt ← get
    let b := stt.constraintState.getVar b
    let saved := stt.constraintState
    let tSel := blockSelector t columns
    let (d, constraintState) := stt.constraintState.nextU64Column columns
    let constraints := stt.constraints.pushUnique (tSel * (b * d - .one))
    set (CollectMState.mk constraints constraintState)
    collectBlockConstraints t columns
    let fSel := blockSelector f columns
    modify fun stt => { stt with
      constraints := stt.constraints.pushUnique (fSel * b)
      constraintState := saved }
    collectBlockConstraints f columns
  | .match v branches defaultBranch =>
    let stt ← get
    let v := stt.constraintState.getVar v
    let saved := stt.constraintState
    branches.forM fun (value, branch) => do
      let value := ArithExpr.const (UInt128.ofLoHi value 0)
      let sel := blockSelector branch columns
      modify fun stt => { stt with constraints := stt.constraints.pushUnique (sel * (v - value)) }
      collectBlockConstraints branch columns
      modify fun stt => { stt with constraintState := saved }
    match defaultBranch with
    | none => pure ()
    | some defaultBranch =>
      let sel := blockSelector defaultBranch columns
      branches.forM fun (value, _) => do
        let value := ArithExpr.const (UInt128.ofLoHi value 0)
        modify fun stt =>
          let (d, constraintState) := stt.constraintState.nextU64Column columns
          let constraints := stt.constraints.pushUnique (sel * ((v - value) * d - .one))
          { stt with constraintState, constraints }
      collectBlockConstraints defaultBranch columns
  | .ret id rs =>
    let selCol := columns.getSelector id
    modify fun stt =>
      rs.zip columns.outputs |>.foldl (init := stt) fun acc (r, o) =>
        let r := stt.constraintState.getVar r
        acc.addSharedConstraint $ selCol * (r - o)

def buildFuncionConstraints (function : Bytecode.Function) (layout : Layout)
    (columns : Columns) : Constraints :=
  let constraintState := columns.inputs.foldl (init := default)
    fun acc input => acc.pushVar input
  let (_, constraintState) := collectBlockConstraints function.body columns
    |>.run ⟨.new function layout columns, constraintState⟩
  constraintState.constraints

end Aiur.Circuit
