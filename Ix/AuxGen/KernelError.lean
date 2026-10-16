/-
  Ix.AuxGen.KernelError: the AuxGen kernel bridge's refusals as one type.

  Every way the bridge (`Ix.AuxGen.Kernel`) refuses instead of inventing a
  term (D-12, CQ2.7) is one constructor of `AuxKernelError`. `render` gives
  the exact text the bridge emits (the texts CQ2.7 landed, prefix included),
  and `toCompileError` the compiler error the refusal becomes, so failure
  reports do not move. This is the specification the `AuxKernel` interface
  (`Ix.AuxGen.AuxKernel`) states its refusals in; a backend that refuses
  natively (IxC, AuxGen M1) raises the same constructors.
-/
module
public import Ix.Common
public import Ix.Address
public import Ix.Environment
public import Ix.CompileM
public section

namespace Ix.AuxGen

open Ix.CompileM (CompileError)

/-- Where a kernel's own failure stopped a fail-closed query. -/
inductive KernelSite where
  /-- `getLevel`: inference met a constant the kernel does not know, after
      the fault-in retry. -/
  | inferUnknownConst (addr : Address)
  /-- `getLevel`: inference failed. -/
  | infer
  /-- `getLevel`: the inferred type is not a sort. -/
  | ensureSort
  /-- The elimination decision: the WHNF-peeled result sort of the block
      named `block`. -/
  | resultSort (block : String)
  /-- The elimination decision: `isLargeEliminator` on the block named
      `block`. -/
  | largeElim (block : String)
  deriving BEq, Inhabited

/-- D-12's refusals, one constructor each. Converter refusals (terms in,
    results out) cross into the compiler with the prefix
    `aux kernel bridge: `; `render` includes it. -/
inductive AuxKernelError where
  -- terms in (Lean → kernel), levels
  | unknownLevelParam (name : Name) (params : Array Name)
  | levelMVar
  -- terms in, closed ingress (`leanExprToKexprCached`)
  | closedFVar (name : Name)
  | closedMVar
  | outerMData
  | closedBVarIndex (idx : Nat)
  | closedProjIndex (struct : Name) (idx : Nat)
  -- terms in, open ingress (`toKexprStatic`)
  | unknownFVar (name : Name)
  | fvarOutsideDepth (name : Name) (depth : Nat)
  | openMVar
  | openBVarIndex (idx : Nat)
  | openProjIndex (struct : Name) (idx : Nat)
  -- results out (kernel → Lean)
  | varOutOfRange
  | missingFVarAt (level : Nat)
  | duplicateFVarAt (level : Nat)
  | leakedKernelFVar (id : Nat)
  | levelParamIndex (idx : Nat)
  | constLevelArgIndex (idx : Nat)
  -- scopes
  | duplicateLevelParam (name : Name)
  | duplicateOuterFVar (name : Name)
  | duplicatePushedFVar (name : Name)
  /-- CQ2.7's depth check before `op` (`pushLocals` or `popLocals`). -/
  | staleDepth (op : String)
  /-- A scope value superseded before `op` (`AuxScope.live?`, AuxGen M0). -/
  | staleScope (op : String)
  | popExceedsPushed
  | popNotLifo (name : Name)
  -- environment (the `Ix.Tc` backend's fault-in)
  | noProvenance (addr : Address)
  | provenanceChanged (name : Name)
  /-- The kernel's own failure of a fail-closed query; `detail` is the
      kernel's text (unused for `inferUnknownConst`). -/
  | kernel (site : KernelSite) (detail : String)
  /-- A broken internal invariant of the bridge. -/
  | internal (what : String)
  deriving BEq, Inhabited

namespace AuxKernelError

/-- The exact text the bridge emits for a refusal. -/
def render : AuxKernelError → String
  | .unknownLevelParam name params =>
    s!"aux kernel bridge: unknown level param `{name.pretty}` not found in param_names \
{params.toList.map (·.pretty)}"
  | .levelMVar => "aux kernel bridge: leanLevelToKuniv: level metavariable"
  | .closedFVar name => s!"aux kernel bridge: free variable {name.pretty} in closed ingress"
  | .closedMVar => "aux kernel bridge: expression metavariable in closed ingress"
  | .outerMData => "aux kernel bridge: metadata stripping left an outer metadata layer"
  | .closedBVarIndex idx =>
    s!"aux kernel bridge: bound variable index {idx} exceeds u64 in closed ingress"
  | .closedProjIndex struct idx =>
    s!"aux kernel bridge: projection index {idx} of {struct.pretty} exceeds u64 in closed ingress"
  | .unknownFVar name => s!"aux kernel bridge: toKexprStatic: unknown free variable {name.pretty}"
  | .fvarOutsideDepth name depth =>
    s!"aux kernel bridge: toKexprStatic: free variable {name.pretty} outside context depth {depth}"
  | .openMVar => "aux kernel bridge: toKexprStatic: expression metavariable"
  | .openBVarIndex idx => s!"aux kernel bridge: toKexprStatic: bound variable index {idx} exceeds u64"
  | .openProjIndex struct idx =>
    s!"aux kernel bridge: toKexprStatic: projection index {idx} of {struct.pretty} exceeds u64"
  | .varOutOfRange => "aux kernel bridge: kexprToLean: Var index out of range of outer context"
  | .missingFVarAt level =>
    s!"aux kernel bridge: kexprToLean: missing free variable at outer level {level}"
  | .duplicateFVarAt level =>
    s!"aux kernel bridge: kexprToLean: duplicate free variable identities at outer level {level}"
  | .leakedKernelFVar id => s!"aux kernel bridge: kexprToLean: leaked kernel free variable {id}"
  | .levelParamIndex idx =>
    s!"aux kernel bridge: kunivToLevel: universe parameter index {idx} out of range"
  | .constLevelArgIndex idx =>
    s!"aux kernel bridge: kunivToLevelWithConstLevels: constant universe argument index {idx} \
out of range"
  | .duplicateLevelParam name => s!"aux kernel bridge: duplicate universe parameter '{name}'"
  | .duplicateOuterFVar name => s!"aux kernel bridge: duplicate outer free variable '{name}'"
  | .duplicatePushedFVar name => s!"aux kernel bridge: duplicate pushed free variable '{name}'"
  | .staleDepth op => s!"aux kernel bridge: stale scope depth before {op}"
  | .staleScope op => s!"aux kernel: scope value superseded before {op}"
  | .popExceedsPushed => "aux kernel bridge: popLocals exceeds pushed local count"
  | .popNotLifo name => s!"aux kernel bridge: popLocals is not LIFO at '{name}'"
  | .noProvenance addr => s!"bridge fault: no forward source provenance for {addr}"
  | .provenanceChanged name => s!"bridge fault: source address changed for {name.pretty}"
  | .kernel (.inferUnknownConst addr) _ =>
    s!"TcScope::get_level: tc.infer failed: unknown constant {(toString addr).take 12}"
  | .kernel .infer detail => s!"TcScope::get_level: tc.infer failed: {detail}"
  | .kernel .ensureSort detail => s!"TcScope::get_level: ensure_sort failed: {detail}"
  | .kernel (.resultSort block) detail => s!"compute_is_large_and_k: TC failed for {block}: {detail}"
  | .kernel (.largeElim block) detail =>
    s!"compute_is_large_and_k: is_large_eliminator failed for {block}: {detail}"
  | .internal what => s!"aux kernel bridge: {what}"

instance : ToString AuxKernelError := ⟨render⟩

/-- The compiler error a refusal becomes: the elimination decision's kernel
    failures are `invalidMutualBlock` (the block cannot be given a
    recursor), every other refusal `unsupportedExpr`. -/
def toCompileError (e : AuxKernelError) : CompileError :=
  match e with
  | .kernel (.resultSort _) _ | .kernel (.largeElim _) _ => .invalidMutualBlock e.render
  | _ => .unsupportedExpr e.render

end AuxKernelError

end Ix.AuxGen
