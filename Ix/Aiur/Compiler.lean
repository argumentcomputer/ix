module
public import Ix.Aiur.Compiler.Lower
public import Ix.Aiur.Compiler.Dedup
public import Ix.Aiur.Compiler.Concretize
public import Ix.Aiur.Compiler.Simple

/-!
Aiur compiler pipeline: type-check, simplify, lower to bytecode and deduplicate.

Exposes `CompiledToplevel` as the single entry point for compilation. Callers use
`Toplevel.compile` and then access `compiled.bytecode` and `compiled.getFuncIdx`.
-/

public section

namespace Aiur

structure CompiledToplevel where
  private mk ::
  source : Toplevel
  bytecode : Bytecode.Toplevel
  nameMap : Std.HashMap Global Bytecode.FunIdx

@[inline] def CompiledToplevel.getFuncIdx (ct : CompiledToplevel) (name : Lean.Name) :
    Option Bytecode.FunIdx :=
  ct.nameMap[Global.mk name]?

/-- Collect all callee `FunIdx` values from constrained `Op.call` nodes in a
block tree. Unconstrained calls (`call _ _ _ true`) are skipped because once
execution enters unconstrained mode it cascades to all sub-calls, so those
callees do not need their own circuits. -/
private partial def Bytecode.Block.collectConstrainedCallees
    (b : Bytecode.Block) (acc : Array Bytecode.FunIdx) : Array Bytecode.FunIdx :=
  -- Collect from ops: only `call idx _ _ false` (constrained)
  let acc := b.ops.foldl (init := acc) fun acc op =>
    match op with
    | .call idx _ _ false => acc.push idx
    | _ => acc
  -- Recurse into sub-blocks of match control flow
  match b.ctrl with
  | .match _ cases default? =>
    let acc := cases.foldl (init := acc) fun acc (_, block) =>
      block.collectConstrainedCallees acc
    match default? with
    | some block => block.collectConstrainedCallees acc
    | none => acc
  | .matchContinue _ cases default? _ _ _ continuation =>
    let acc := cases.foldl (init := acc) fun acc (_, block) =>
      block.collectConstrainedCallees acc
    let acc := match default? with
      | some block => block.collectConstrainedCallees acc
      | none => acc
    continuation.collectConstrainedCallees acc
  | .return _ _ | .yield _ _ => acc

/-- Compute which functions need a circuit. A function needs a circuit iff it is
reachable from an entry point through a chain of constrained call edges.
Returns an array of `Bool` indexed by `FunIdx`. -/
private def Bytecode.Toplevel.needsCircuit (t : Bytecode.Toplevel) :
    Array Bool := Id.run do
  let n := t.functions.size
  let mut needs := Array.replicate n false
  let mut stack : Array Bytecode.FunIdx := #[]
  -- Seed: every entry function needs a circuit
  for i in [:n] do
    if t.functions[i]!.entry then
      needs := needs.set! i true
      stack := stack.push i
  -- BFS along constrained call edges
  while h : 0 < stack.size do
    let fi := stack.back
    stack := stack.pop
    let callees := t.functions[fi]!.body.collectConstrainedCallees #[]
    for callee in callees do
      if !needs[callee]! then
        needs := needs.set! callee true
        stack := stack.push callee
  needs

def Toplevel.compile (t : Toplevel) : Except String CompiledToplevel := do
  let typedDecls ← t.checkAndSimplify.mapError toString
  let typedDecls ← typedDecls.concretize
  let (bytecodeRaw, preNameMap) ← typedDecls.toBytecode
  let (bytecodeDedup, remap) := bytecodeRaw.deduplicate
  let needs := bytecodeDedup.needsCircuit
  let bytecode := { bytecodeDedup with
    functions := bytecodeDedup.functions.mapIdx fun i f =>
      { f with constrained := needs[i]! } }
  let nameMap := preNameMap.fold (init := (∅ : Std.HashMap Global Bytecode.FunIdx))
    fun acc name idx => acc.insert name (remap idx)
  pure (CompiledToplevel.mk t bytecode nameMap)

end Aiur

end
