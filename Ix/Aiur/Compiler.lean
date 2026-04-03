module
public import Ix.Aiur.Compiler.Lower
public import Ix.Aiur.Compiler.Dedup
public import Ix.Aiur.Compiler.Concretize
public import Ix.Aiur.Compiler.Infer
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

def Toplevel.compile (t : Toplevel) : Except String CompiledToplevel := do
  let t := t.expandAllAliases
  let t ← t.infer
  let t ← t.concretize
  let typedDecls ← t.checkAndSimplify.mapError toString
  let (bytecodeRaw, preNameMap) ← typedDecls.toBytecode
  let (bytecode, remap) := bytecodeRaw.deduplicate
  let nameMap := preNameMap.fold (init := (∅ : Std.HashMap Global Bytecode.FunIdx))
    fun acc name idx => acc.insert name (remap idx)
  pure (CompiledToplevel.mk t bytecode nameMap)

end Aiur

end
