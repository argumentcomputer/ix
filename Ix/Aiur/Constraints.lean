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
  let (multiplicity, circuitModule) := circuitModule.addCommitted "multiplicity" .b64
  let (selectors, circuitModule) := foldCommit layout.selectors circuitModule (s!"selector-{·}") .b1
  let columns := { inputs, outputs, u1Auxiliaries, u8Auxiliaries, u64Auxiliaries, multiplicity, selectors }
  (columns, circuitModule)
where
  foldCommit n circuitModule nameFn tf :=
    n.fold (init := (#[], circuitModule)) fun i _ (oracles, circuitModule) =>
      let (oracleIdx, circuitModule) := circuitModule.addCommitted (nameFn i) tf
      (oracles.push oracleIdx, circuitModule)

inductive Channel
  | add
  | mul
  | fun : FuncIdx → Channel
  | mem : Nat → Channel

structure Constraints where
  sharedConstraints : Array ArithExpr
  uniqueConstraints : Array ArithExpr
  sends : Array (Channel × ArithExpr × Array ArithExpr)
  requires : Array (Channel × ArithExpr × OracleIdx × Array ArithExpr)
  topmostSelector : ArithExpr
  io : Array OracleIdx
  multiplicity : OracleIdx

end Aiur.Circuit
