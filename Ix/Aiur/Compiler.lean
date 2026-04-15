module
public import Ix.Aiur.Compiler.Lower
public import Ix.Aiur.Compiler.Dedup
public import Ix.Aiur.Compiler.Concretize
public import Ix.Aiur.Compiler.Simple

/-!
Aiur compiler pipeline: type-check, simplify, concretize, lower, deduplicate.

The pipeline in `Aiur` uses staged IRs:
```
Source.Toplevel
  └─ checkAndSimplify    (Check + Simple)
       ↓
Typed.Decls
  └─ concretize          (Concretize)
       ↓
Concrete.Decls
  └─ toBytecode          (Lower + Layout)
       ↓
Bytecode.Toplevel
  ├─ deduplicate         (Dedup)
  └─ needsCircuit        (this file)
       ↓
CompiledToplevel
```
-/

public section
@[expose] section

namespace Aiur

structure CompiledToplevel where
  mk ::
  source : Source.Toplevel
  bytecode : Bytecode.Toplevel
  nameMap : Std.HashMap Global Bytecode.FunIdx

@[inline, expose]
def CompiledToplevel.getFuncIdx (ct : CompiledToplevel) (name : Lean.Name) :
    Option Bytecode.FunIdx :=
  ct.nameMap[Global.mk name]?

/-- Termination helper for the `Block`/`Ctrl` traversal below. -/
private theorem Bytecode.Block.sizeOf_ctrl_lt'' (b : Bytecode.Block) :
    sizeOf b.ctrl < sizeOf b := by
  rcases b with ⟨ops, ctrl⟩
  show sizeOf ctrl < 1 + sizeOf ops + sizeOf ctrl
  omega

mutual
/-- Collect all callee `FunIdx` values from constrained `Op.call` nodes in a
block tree. Unconstrained calls are skipped because cascading into unconstrained
mode removes the need for the callee's own circuit. -/
def Bytecode.Ctrl.collectConstrainedCallees (c : Bytecode.Ctrl) :
    Array Bytecode.FunIdx := match c with
  | .match _ cases default? =>
    let branchCallees := cases.attach.foldl (init := #[]) fun acc ⟨(_, block), _⟩ =>
      acc ++ block.collectConstrainedCallees
    match default? with
    | some block => branchCallees ++ block.collectConstrainedCallees
    | none => branchCallees
  | .matchContinue _ cases default? _ _ _ continuation =>
    let branchCallees := cases.attach.foldl (init := #[]) fun acc ⟨(_, block), _⟩ =>
      acc ++ block.collectConstrainedCallees
    let withDefault := match default? with
      | some block => branchCallees ++ block.collectConstrainedCallees
      | none => branchCallees
    withDefault ++ continuation.collectConstrainedCallees
  | .return _ _ | .yield _ _ => #[]
termination_by (sizeOf c, 0)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
    | grind

def Bytecode.Block.collectConstrainedCallees (b : Bytecode.Block) :
    Array Bytecode.FunIdx :=
  let opCallees := b.ops.foldl (init := #[]) fun acc op =>
    match op with
    | .call idx _ _ false => acc.push idx
    | _ => acc
  opCallees ++ b.ctrl.collectConstrainedCallees
termination_by (sizeOf b, 1)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (apply Prod.Lex.left; exact Bytecode.Block.sizeOf_ctrl_lt'' _)
end

/-- Compute which functions need a circuit. A function needs a circuit iff it is
reachable from an entry point through a chain of constrained call edges. -/
def Bytecode.Toplevel.needsCircuit (t : Bytecode.Toplevel) : Array Bool := Id.run do
  let n := t.functions.size
  let mut needs := Array.replicate n false
  let mut stack : Array Bytecode.FunIdx := #[]
  for i in [:n] do
    if t.functions[i]!.entry then
      needs := needs.set! i true
      stack := stack.push i
  while h : 0 < stack.size do
    let fi := stack.back
    stack := stack.pop
    let callees := t.functions[fi]!.body.collectConstrainedCallees
    for callee in callees do
      if !needs[callee]! then
        needs := needs.set! callee true
        stack := stack.push callee
  needs

/-- Full compilation pipeline. -/
def Source.Toplevel.compile (t : Source.Toplevel) : Except String CompiledToplevel := do
  let typedDecls ← t.checkAndSimplify.mapError toString
  let concDecls ← typedDecls.concretize.mapError toString
  let (bytecodeRaw, preNameMap) ← concDecls.toBytecode
  let (bytecodeDedup, remap) := bytecodeRaw.deduplicate
  let needs := bytecodeDedup.needsCircuit
  let bytecode := { bytecodeDedup with
    functions := bytecodeDedup.functions.mapIdx fun i f =>
      { f with constrained := needs[i]! } }
  let nameMap := preNameMap.fold (init := (∅ : Std.HashMap Global Bytecode.FunIdx))
    fun acc name idx => acc.insert name (remap idx)
  pure (CompiledToplevel.mk t bytecode nameMap)

/-- Progress helper: given success of the three `Except`-returning stages,
`compile` as a whole returns `.ok` (the remaining stages — `deduplicate`,
`needsCircuit`, the field-setter `mapIdx`, the name-map `fold`, and the
terminating `pure` — are all total). -/
theorem Source.Toplevel.compile_ok_of_stages
    {t : Source.Toplevel} {typedDecls concDecls bytecodeRaw preNameMap}
    (hts : t.checkAndSimplify = .ok typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls)
    (hbc : concDecls.toBytecode = .ok (bytecodeRaw, preNameMap)) :
    ∃ ct, t.compile = .ok ct := by
  simp only [Source.Toplevel.compile, hts, hconc, hbc, Except.mapError, bind,
             Except.bind, pure, Except.pure]
  exact ⟨_, rfl⟩

/-- Inverse of `compile_ok_of_stages`: unpack a successful `compile` into
stage witnesses. Used by `compile_preservation` to thread stage-local
lemmas through the composition. -/
theorem Source.Toplevel.compile_stages_of_ok
    {t : Source.Toplevel} {ct : CompiledToplevel}
    (_hct : t.compile = .ok ct) :
    ∃ typedDecls concDecls bytecodeRaw preNameMap,
      t.checkAndSimplify = .ok typedDecls ∧
      typedDecls.concretize = .ok concDecls ∧
      concDecls.toBytecode = .ok (bytecodeRaw, preNameMap) := by
  -- Case on each stage result; `mapError` on `.ok` is definitionally `.ok`.
  cases hts : t.checkAndSimplify with
  | error e => simp [Source.Toplevel.compile, hts, bind, Except.bind, Except.mapError] at _hct
  | ok typedDecls =>
    cases hconc : typedDecls.concretize with
    | error e =>
      simp [Source.Toplevel.compile, hts, hconc, bind, Except.bind, Except.mapError] at _hct
    | ok concDecls =>
      cases hbc : concDecls.toBytecode with
      | error e =>
        simp [Source.Toplevel.compile, hts, hconc, hbc, bind, Except.bind, Except.mapError] at _hct
      | ok bc =>
        obtain ⟨bytecodeRaw, preNameMap⟩ := bc
        -- `checkAndSimplify`/`concretize` are unfolded; `toBytecode` is not
        -- (private module), so the first two equalities reduce to `rfl` but
        -- the third still mentions `concDecls.toBytecode` — supply `hbc`.
        exact ⟨typedDecls, concDecls, bytecodeRaw, preNameMap, rfl, hconc, hbc⟩

-- Compile post-conditions moved to `Proofs/StructCompatible.lean`.

end Aiur

end -- @[expose] section
end
