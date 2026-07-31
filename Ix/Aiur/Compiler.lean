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

/-- Regroup the circuit partition: each `(name, members)` in `groups` becomes
ONE circuit proving all the listed functions (branching on the member; see
`Bytecode.Circuit`), positioned where its first member's singleton circuit
was; every other constrained function keeps its singleton circuit. Grouping
is a circuit-level choice — the function "library", its bytecode, execution,
and the query record are untouched, and callers still target function
indices on the function channel.

Grouping is favorable for RARELY-CALLED functions of similar shape: the
merged circuit sums the members' selector columns but takes the max of their
auxiliary columns, so each (rare) row pays the group's selector count, while
the system sheds one circuit (vk entry, commitment matrix, verifier work)
per absorbed member.

Errors if a name is unknown, unconstrained (it has no circuit to group), an
entry function, listed twice, or if a group is empty. -/
def CompiledToplevel.groupFunctions (ct : CompiledToplevel)
    (groups : Array (String × Array Lean.Name)) :
    Except String CompiledToplevel := do
  let t := ct.bytecode
  -- Resolve and validate the groups into member-index arrays.
  let mut grouped : Std.HashMap Bytecode.FunIdx Nat := {}
  let mut resolved : Array (String × Array Bytecode.FunIdx) := #[]
  for (gname, names) in groups do
    if names.isEmpty then
      throw s!"group {gname} is empty"
    let mut members := #[]
    for name in names do
      let some i := ct.getFuncIdx name
        | throw s!"group {gname}: unknown function {name}"
      let f := t.functions[i]!
      unless f.constrained do
        throw s!"group {gname}: {name} is unconstrained (it has no circuit)"
      if f.entry then
        throw s!"group {gname}: {name} is an entry function"
      if grouped.contains i then
        throw s!"group {gname}: {name} is already grouped"
      grouped := grouped.insert i resolved.size
      members := members.push i
    resolved := resolved.push (gname, members)
  -- Rebuild the partition in first-occurrence order over the existing
  -- (singleton-ordered) circuits.
  let mut circuits : Array Bytecode.Circuit := #[]
  let mut placed : Array Bool := .replicate resolved.size false
  for c in t.circuits do
    let members := c.members
    if h : members.size = 1 then
      let i := members[0]
      match grouped[i]? with
      | none => circuits := circuits.push c
      | some g =>
        unless placed[g]! do
          placed := placed.set! g true
          let (gname, ms) := resolved[g]!
          let layout := ms.foldl (init := t.functions[ms[0]!]!.layout)
            fun acc m => if m == ms[0]! then acc
              else acc.merge t.functions[m]!.layout
          circuits := circuits.push { name := gname, members := ms, layout }
    else
      throw "groupFunctions: partition already grouped; group from a freshly compiled toplevel"
  pure { ct with bytecode := { t with circuits } }

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

/-- The default circuit partition: one singleton circuit per constrained
function, in function-index order, named by `nameOf`. -/
def Bytecode.Toplevel.singletonCircuits (t : Bytecode.Toplevel)
    (nameOf : Bytecode.FunIdx → String) : Array Bytecode.Circuit := Id.run do
  let mut circuits : Array Bytecode.Circuit := #[]
  for h : i in [:t.functions.size] do
    let f := t.functions[i]
    if f.constrained then
      circuits := circuits.push
        { name := nameOf i, members := #[i], layout := f.layout }
  pure circuits

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
  let t ← t.inlineCalls
  let typedDecls ← t.checkAndSimplify.mapError toString
  let concDecls ← typedDecls.concretize.mapError toString
  let (bytecodeRaw, preNameMap) ← concDecls.toBytecode
  let (bytecodeDedup, remap) := bytecodeRaw.deduplicate
  let needs := bytecodeDedup.needsCircuit
  let bytecode : Bytecode.Toplevel := { bytecodeDedup with
    functions := bytecodeDedup.functions.mapIdx fun i f =>
      { f with constrained := needs[i]! } }
  let nameMap := preNameMap.fold (init := (∅ : Std.HashMap Global Bytecode.FunIdx))
    fun acc name idx => acc.insert name (remap idx)
  -- Singleton circuits are labeled with (one of) the function's source names.
  let reverseMap := nameMap.fold (init := (∅ : Std.HashMap Bytecode.FunIdx String))
    fun acc global idx => if acc.contains idx then acc else acc.insert idx (toString global)
  let bytecode := { bytecode with
    circuits := bytecode.singletonCircuits fun i => reverseMap[i]?.getD s!"<fn {i}>" }
  pure (CompiledToplevel.mk t bytecode nameMap)

/-- Progress helper: given success of the three `Except`-returning stages,
`compile` as a whole returns `.ok` (the remaining stages — `deduplicate`,
`needsCircuit`, the field-setter `mapIdx`, the name-map `fold`, and the
terminating `pure` — are all total). -/
theorem Source.Toplevel.compile_ok_of_stages
    {t inlined : Source.Toplevel} {typedDecls concDecls bytecodeRaw preNameMap}
    (hinline : t.inlineCalls = .ok inlined)
    (hts : inlined.checkAndSimplify = .ok typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls)
    (hbc : concDecls.toBytecode = .ok (bytecodeRaw, preNameMap)) :
    ∃ ct, t.compile = .ok ct := by
  simp only [Source.Toplevel.compile, hinline, hts, hconc, hbc, Except.mapError,
             bind, Except.bind, pure, Except.pure]
  exact ⟨_, rfl⟩

/-- Inverse of `compile_ok_of_stages`: unpack a successful `compile` into
stage witnesses. Used by `compile_preservation` to thread stage-local
lemmas through the composition. -/
theorem Source.Toplevel.compile_stages_of_ok
    {t : Source.Toplevel} {ct : CompiledToplevel}
    (_hct : t.compile = .ok ct) :
    ∃ inlined typedDecls concDecls bytecodeRaw preNameMap,
      t.inlineCalls = .ok inlined ∧
      inlined.checkAndSimplify = .ok typedDecls ∧
      typedDecls.concretize = .ok concDecls ∧
      concDecls.toBytecode = .ok (bytecodeRaw, preNameMap) := by
  -- Case on each stage result; `mapError` on `.ok` is definitionally `.ok`.
  cases hinline : t.inlineCalls with
  | error e => simp [Source.Toplevel.compile, hinline, bind, Except.bind] at _hct
  | ok inlined =>
    cases hts : inlined.checkAndSimplify with
    | error e => simp [Source.Toplevel.compile, hinline, hts, bind, Except.bind, Except.mapError] at _hct
    | ok typedDecls =>
      cases hconc : typedDecls.concretize with
      | error e =>
        simp [Source.Toplevel.compile, hinline, hts, hconc, bind, Except.bind, Except.mapError] at _hct
      | ok concDecls =>
        cases hbc : concDecls.toBytecode with
        | error e =>
          simp [Source.Toplevel.compile, hinline, hts, hconc, hbc, bind, Except.bind, Except.mapError] at _hct
        | ok bc =>
          obtain ⟨bytecodeRaw, preNameMap⟩ := bc
          exact ⟨inlined, typedDecls, concDecls, bytecodeRaw, preNameMap, rfl, hts, hconc, hbc⟩

-- Compile post-conditions moved to `Proofs/StructCompatible.lean`.

end Aiur

end -- @[expose] section
end
