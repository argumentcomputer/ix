module
public meta import Ix.Aiur.Term
public meta import Lean.Elab
public meta import Lean.Elab.Command

/-!
# Aiur Formal Verification — `#aiur_gen` Command

Generates Lean source files from an `Aiur.Toplevel`, containing:

- **Sem types**: Lean `inductive`s mirroring Aiur enums, with pointers (`&T`)
  erased to `T`. Type aliases become `abbrev`s. Generic type parameters
  (`enum Foo‹T›`) become explicit Lean type parameters (`(T : Type)`).

- **Semantic propositions**: one `inductive` per Aiur function, with one
  constructor per control-flow path. `assertEq` becomes a `Prop` conjunct,
  function calls become premises, `store`/`load` are erased, and u8/u32
  operations carry range constraints. Generic function parameters become
  implicit Lean type parameters (`{T : Type}`). Unconstrained calls (`#fn(…)`)
  produce universally quantified variables with no premises, reflecting the
  absence of any guarantee on how the result was computed.

Functions are topologically sorted by their call graph. Mutually recursive
clusters are wrapped in `mutual ... end`; acyclic dependencies are emitted
in dependency order.

## Syntax

```
#aiur_gen myTypes "TypesSem.lean" #
#aiur_gen myFuns  "FunsSem.lean"  importing Ix.Foo.TypesSem opening myTypes #
```

- `importing` adds `public import` lines to the generated file.
- `opening` adds `open` declarations for namespaces from those imports.
- `#` at the end completes the syntax and marks the user intent to write the file.
-/

public meta section

namespace Aiur.Formal

open Aiur
open Lean Elab Command Meta

-- ════════════════════════════════════════════════════════════
-- Toplevel evaluation
-- ════════════════════════════════════════════════════════════

/-- Evaluate a `Toplevel` constant by name at elaboration time.
    Uses `evalConstCheck` (native evaluation), which requires
    `precompileModules := true` on the library. -/
unsafe def evalToplevelImpl (name : Name) : CommandElabM Toplevel := do
  let env ← getEnv
  let opts ← getOptions
  ofExcept <| env.evalConstCheck Toplevel opts ``Toplevel name

@[implemented_by evalToplevelImpl]
opaque evalToplevel (name : Name) : CommandElabM Toplevel

-- ════════════════════════════════════════════════════════════
-- Generated file IR
--
-- The code generator builds this intermediate representation,
-- then a single `render` pass converts it to a `.lean` file.
-- ════════════════════════════════════════════════════════════

/-- A constructor of a generated Lean `inductive`. -/
structure GenCtor where
  name     : String
  argTypes : List String

/-- A generated Lean `inductive` (from an Aiur `enum`). -/
structure GenInductive where
  name   : String
  params : List String
  ctors  : List GenCtor

/-- A generated Lean `abbrev` (from an Aiur `type` alias). -/
structure GenAlias where
  name   : String
  params : List String
  typ    : String

/-- A constructor of an semantic proposition.
    Each one represents a single complete execution path through
    the corresponding Aiur function. -/
structure GenEvalCtor where
  /-- Constructor name, e.g. `"path0"`. -/
  name      : String
  /-- Premises from sub-function calls, e.g. `["eval a r0 P0"]`. -/
  premises  : List String
  /-- Input patterns (possibly refined by match), e.g. `[".Nil"]`. -/
  inputPats : List String
  /-- The output expression, e.g. `"(r0 + r1)"`. -/
  output    : String
  /-- The accumulated `Prop` constraint, e.g. `"(P0 ∧ P1)"` or `"True"`. -/
  prop      : String

/-- An semantic proposition for one Aiur function. -/
structure GenEvalRel where
  /-- Relation name, e.g. `"eval"`. -/
  name   : String
  /-- Type parameters from the Aiur function template. -/
  params : List String
  /-- Type signature, e.g. `"Expr → G → Prop → Prop"`. -/
  sig    : String
  ctors  : List GenEvalCtor
  deriving Inhabited

/-- A group of sem types. Mutually recursive data types share
    a `mutual` block; acyclic ones are standalone. -/
inductive GenTypeBlock where
  | single : GenInductive → GenTypeBlock
  | mutual : List GenInductive → GenTypeBlock

/-- A group of semantic propositions. Mutually recursive functions share
    a `mutual` block; all others are standalone. -/
inductive GenEvalBlock where
  | single : GenEvalRel → GenEvalBlock
  | mutual : List GenEvalRel → GenEvalBlock

/-- The complete IR for a generated `.lean` file. -/
structure GenFile where
  ns         : String
  imports    : List String
  opens      : List String
  aliases    : List GenAlias
  typeBlocks : List GenTypeBlock
  evalBlocks : List GenEvalBlock

-- ════════════════════════════════════════════════════════════
-- Rendering IR → String
-- ════════════════════════════════════════════════════════════

def renderExplicitParams (params : List String) : String :=
  if params.isEmpty then ""
  else " " ++ " ".intercalate (params.map fun p => s!"({p} : Type)")

def renderImplicitParams (params : List String) : String :=
  if params.isEmpty then ""
  else " " ++ " ".intercalate (params.map fun p => s!"\{{p} : Type}")

def GenAlias.render (a : GenAlias) : String :=
  s!"abbrev {a.name}{renderExplicitParams a.params} := {a.typ}\n"

def GenInductive.render (ind : GenInductive) : String :=
  let appliedName := if ind.params.isEmpty then ind.name
    else s!"{ind.name} {" ".intercalate ind.params}"
  let ctors := ind.ctors.map fun c =>
    if c.argTypes.isEmpty then s!"  | {c.name}"
    else s!"  | {c.name} : {" → ".intercalate c.argTypes} → {appliedName}"
  s!"inductive {ind.name}{renderExplicitParams ind.params} where\n{"\n".intercalate ctors}\n"

def GenEvalCtor.render (relName : String) (c : GenEvalCtor) : String :=
  let premises := c.premises.map fun p => s!"      {p} →\n"
  let inputPats := " ".intercalate c.inputPats
  s!"  | {c.name} :\n{String.join premises}      {relName} {inputPats} {c.output} {c.prop}"

def GenEvalRel.render (r : GenEvalRel) : String :=
  let ctors := r.ctors.map (GenEvalCtor.render r.name)
  s!"inductive {r.name}{renderImplicitParams r.params} : {r.sig} where\n{"\n".intercalate ctors}\n"

def GenTypeBlock.render : GenTypeBlock → String
  | .single ind => ind.render
  | .mutual inds => "mutual\n\n" ++ "\n".intercalate (inds.map GenInductive.render) ++ "\nend\n"

def GenEvalBlock.render : GenEvalBlock → String
  | .single r => r.render
  | .mutual rs => "mutual\n\n" ++ "\n".intercalate (rs.map GenEvalRel.render) ++ "\nend\n"

def GenFile.render (f : GenFile) : String :=
  let imports := "public import Ix.Aiur.Goldilocks\n" ++
    String.join (f.imports.map fun i => s!"public import {i}\n")
  let opens := "open Aiur" ++
    (if f.opens.isEmpty then "" else " " ++ " ".intercalate f.opens)
  String.join [
    "-- Auto-generated by #aiur_gen. Regenerate, don't edit.\nmodule\n",
    imports,
    "\npublic section\n\n",
    s!"namespace {f.ns}\n\n",
    s!"{opens}\n\n",
    "-- ══════ Semantic types ══════\n\n",
    String.join (f.aliases.map (·.render ++ "\n")),
    "\n".intercalate (f.typeBlocks.map (·.render)),
    "\n-- ══════ Semantic propositions ══════\n\n",
    "\n".intercalate (f.evalBlocks.map (·.render)),
    s!"\nend {f.ns}\n\nend\n"
  ]

-- ════════════════════════════════════════════════════════════
-- Expression-level helpers
--
-- These produce Lean syntax *fragments* (not whole declarations).
-- Used by the Eval path enumerator below.
-- ════════════════════════════════════════════════════════════

/-- Map an Aiur `Typ` to the corresponding Lean type expression.
    Pointers are erased: `&T` becomes `T`.
    Type parameters are resolved by name via the `params` list. -/
partial def typToSem (params : List String := []) : Typ → String
  | .unit => "Unit"
  | .field => "G"
  | .pointer t => typToSem params t
  | .ref g => g.toName.toString (escape := false)
  | .app g args =>
    let base := g.toName.toString (escape := false)
    if args.isEmpty then base
    else s!"({base} {" ".intercalate (args.toList.map (typToSem params))})"
  | .mvar n => params.getD n s!"T{n}"
  | .tuple ts => s!"({" × ".intercalate (ts.toList.map (typToSem params))})"
  | .array t n => s!"(Fin {n} → {typToSem params t})"
  | .function _ _ => "sorry /- function type -/"

/-- Render a Goldilocks field element as a Lean numeric literal. -/
def renderG (g : G) : String := s!"({g.val.toNat} : G)"

/-- Render an Aiur local variable name as a Lean identifier. -/
def renderLocal : Local → String
  | .str s => s
  | .idx n => s!"_v{n}"

-- ════════════════════════════════════════════════════════════
-- Sem type construction
-- ════════════════════════════════════════════════════════════

def mkGenInductive (dt : DataType) : GenInductive :=
  { name := dt.name.toName.toString (escape := false)
    params := dt.params
    ctors := dt.constructors.map fun c =>
      { name := c.nameHead, argTypes := c.argTypes.map (typToSem dt.params) } }

def mkGenAlias (ta : TypeAlias) : GenAlias :=
  { name := ta.name.toName.toString (escape := false)
    params := ta.params
    typ := typToSem ta.params ta.expansion }

-- ════════════════════════════════════════════════════════════
-- Eval path enumeration
--
-- Walks an Aiur `Term` and enumerates all complete execution
-- paths through it. Each path accumulates:
--
-- - **Premises**: from function calls (`f.Eval args result P`)
-- - **Prop parts**: from `assertEq` (`a = b`) and match conditions
--   on intermediate values (`G.eqZero n = (1 : G)`)
-- - **Sub-props**: the `P` variables from sub-call premises
-- - **Match bindings**: when the scrutinee is a function input,
--   records `(input, pattern)` to refine the Eval signature
--
-- The result for each path is a `(outputExpr, GenState)` pair.
-- ════════════════════════════════════════════════════════════

/-- A premise in an Eval constructor, e.g. `"eval a r0 P0"`.
    Wrapped for clarity; will appear as `premise → ...` in the output. -/
structure Premise where
  text : String
  deriving Inhabited

/-- Mutable state threaded through path enumeration. -/
structure GenState where
  freshVarIdx   : Nat := 0
  freshPropIdx  : Nat := 0
  premises      : Array Premise := #[]
  /-- Prop conjuncts from `assertEq` and field-match conditions. -/
  propParts     : Array String := #[]
  /-- Prop variables introduced by sub-call premises (`P0`, `P1`, ...). -/
  subProps      : Array String := #[]
  /-- Local variable bindings: name → expression. -/
  bindings      : List (String × String) := []
  /-- Match bindings: `(scrutinee, pattern)` for input-level matches. -/
  matchBindings : Array (String × String) := #[]
  /-- Named variables (function params + pattern-bound), used to distinguish
      input/variable matches (which refine the Eval signature) from
      intermediate expression matches (which add Prop constraints). -/
  namedVars    : List String := []
  /-- Constructor names from the toplevel's data types. When `app` references
      one of these, it emits a constructor expression instead of a premise. -/
  ctorNames    : Std.HashSet String := {}

def GenState.fresh (s : GenState) (prefix_ : String := "r") : String × GenState :=
  (s!"{prefix_}{s.freshVarIdx}", { s with freshVarIdx := s.freshVarIdx + 1 })

def GenState.freshProp (s : GenState) : String × GenState :=
  let name := s!"P{s.freshPropIdx}"
  (name, { s with freshPropIdx := s.freshPropIdx + 1 })

def GenState.addPremise (s : GenState) (p : String) : GenState :=
  { s with premises := s.premises.push ⟨p⟩ }

def GenState.addProp (s : GenState) (p : String) : GenState :=
  { s with propParts := s.propParts.push p }

def GenState.addSubProp (s : GenState) (p : String) : GenState :=
  { s with subProps := s.subProps.push p }

def GenState.bind (s : GenState) (name expr : String) : GenState :=
  { s with bindings := (name, expr) :: s.bindings }

def GenState.resolve (s : GenState) (name : String) : String :=
  match s.bindings.find? (·.1 == name) with
  | some (_, e) => e
  | none => name

/-- Render the accumulated Prop as a single expression.
    Empty → `True`. Single → parenthesized. Multiple → conjoined. -/
def GenState.renderProp (s : GenState) : String :=
  let all := s.subProps ++ s.propParts
  if all.isEmpty then "True"
  else if all.size == 1 then s!"({all[0]!})"
  else s!"({" ∧ ".intercalate all.toList})"

/-- Collect variable names introduced by a pattern. -/
partial def patternVarNames : Pattern → List String
  | .var l => [renderLocal l]
  | .pointer p => patternVarNames p
  | .or p1 _ => patternVarNames p1
  | .ref _ pats => pats.flatMap patternVarNames
  | .tuple ps => ps.toList.flatMap patternVarNames
  | .array ps => ps.toList.flatMap patternVarNames
  | _ => []

/-- Render an Aiur `Pattern` to Lean expression(s).
    Returns multiple results when `or` patterns appear at any nesting
    level, since each alternative is a distinct execution path. -/
partial def renderPatExprs (s : GenState) : Pattern → List (String × GenState)
  | .var l => [(renderLocal l, s)]
  | .wildcard => [("_", s)]
  | .field g => [(renderG g, s)]
  | .pointer p => renderPatExprs s p
  | .or p1 p2 => renderPatExprs s p1 ++ renderPatExprs s p2
  | .ref g pats =>
    let fullName := g.toName.toString (escape := false)
    let init : List (List String × GenState) := [([], s)]
    let results := pats.foldl (init := init) fun acc pat =>
      acc.flatMap fun (strs, s) =>
        (renderPatExprs s pat).map fun (str, s) => (strs ++ [str], s)
    results.map fun (argStrs, s) =>
      if argStrs.isEmpty then (fullName, s)
      else (s!"({fullName} {" ".intercalate argStrs})", s)
  | .tuple ps =>
    let init : List (Array String × GenState) := [(#[], s)]
    let results := ps.foldl (init := init) fun acc pat =>
      acc.flatMap fun (strs, s) =>
        (renderPatExprs s pat).map fun (str, s) => (strs.push str, s)
    results.map fun (strs, s) => (s!"({", ".intercalate strs.toList})", s)
  | .array ps =>
    let init : List (Array String × GenState) := [(#[], s)]
    let results := ps.foldl (init := init) fun acc pat =>
      acc.flatMap fun (strs, s) =>
        (renderPatExprs s pat).map fun (str, s) => (strs.push str, s)
    results.map fun (strs, s) => (s!"#[{", ".intercalate strs.toList}]", s)

/-- Enumerate all execution paths through a `Term`.
    Each path produces an output expression and accumulated state.
    IO operations produce unconstrained fresh variables (loose semantics). -/
partial def termPaths (s : GenState) (t : Term) : List (String × GenState)
  := match t with
  -- Atoms
  | .unit => [("()", s)]
  | .var l => [(s.resolve (renderLocal l), s)]
  | .ref g => [(g.toName.toString (escape := false), s)]
  | .data (.field g) => [(renderG g, s)]
  | .data (.tuple ts) =>
    (evalArgs s ts.toList).map fun (strs, s) =>
      (s!"({", ".intercalate strs})", s)
  | .data (.array ts) =>
    (evalArgs s ts.toList).map fun (strs, s) =>
      (s!"#[{", ".intercalate strs}]", s)
  -- Control flow: transparent wrappers
  | .ret t => termPaths s t
  | .ann _ t => termPaths s t
  | .debug _ _ ret => termPaths s ret
  -- Control flow: let binding
  | .let pat val body =>
    (termPaths s val).flatMap fun (vval, s) =>
      (renderPatExprs s pat).flatMap fun (patExpr, s) =>
        let s := if patExpr == "_" then s else s.bind patExpr vval
        let s := { s with namedVars := s.namedVars ++ patternVarNames pat }
        termPaths s body
  -- Control flow: match (branches multiply paths)
  | .match scrut branches =>
    (termPaths s scrut).flatMap fun (vscrut, s) =>
      branches.flatMap fun (pat, body) =>
        (renderPatExprs s pat).flatMap fun (patStr, s) =>
          let s := if s.namedVars.contains vscrut then
            { s with matchBindings := s.matchBindings.push (vscrut, patStr) }
          else
            s.addProp s!"{vscrut} = {patStr}"
          let s := { s with namedVars := s.namedVars ++ patternVarNames pat }
          termPaths s body
  -- Field arithmetic
  | .add a b => binOp s a b " + "
  | .sub a b => binOp s a b " - "
  | .mul a b => binOp s a b " * "
  | .eqZero a =>
    (termPaths s a).map fun (va, s) => (s!"(G.eqZero {va})", s)
  -- Pointer operations (erased in the semantic domain)
  | .store t => termPaths s t
  | .load t  => termPaths s t
  | .ptrVal _ => let (v, s) := s.fresh "io"; [(v, s)]
  -- Aggregate operations
  | .proj t n =>  -- Aiur 0-indexed; Lean Prod 1-indexed
    (termPaths s t).map fun (vt, s) => (s!"({vt}).{n + 1}", s)
  | .get t n =>
    (termPaths s t).map fun (vt, s) => (s!"({vt})[{n}]", s)
  | .slice t i j =>
    (termPaths s t).map fun (vt, s) => (s!"({vt}).extract {i} {j}", s)
  | .set t i val =>
    (termPaths s t).flatMap fun (vt, s) =>
      (termPaths s val).map fun (vv, s) => (s!"({vt}).set {i} {vv}", s)
  -- Function calls → premise. Data constructors → direct expression.
  -- Unconstrained calls produce fresh variables with no premises.
  | .app g args unconstrained =>
    let fname := g.toName.toString (escape := false)
    if s.ctorNames.contains fname then
      (evalArgs s args).map fun (argStrs, s) =>
        (s!"({fname} {" ".intercalate argStrs})", s)
    else if unconstrained then
      (evalArgs s args).map fun (_, s) =>
        let (result, s) := s.fresh "u"
        (result, s)
    else
      (evalArgs s args).map fun (argStrs, s) =>
        let (result, s) := s.fresh "r"
        let (prop, s) := s.freshProp
        let premise := s!"{fname} {" ".intercalate argStrs} {result} {prop}"
        let s := s.addPremise premise |>.addSubProp prop
        (result, s)
  -- Assertions → Prop conjunct
  | .assertEq a b ret =>
    (termPaths s a).flatMap fun (va, s) =>
      (termPaths s b).flatMap fun (vb, s) =>
        termPaths (s.addProp s!"{va} = {vb}") ret
  -- u8 operations: result + range constraints (`G.isU8`) on inputs
  | .u8And a b       => u8BinOp s a b "G.u8And"
  | .u8Or a b        => u8BinOp s a b "G.u8Or"
  | .u8Xor a b       => u8BinOp s a b "G.u8Xor"
  | .u8LessThan a b  => u8BinOp s a b "G.u8LessThan"
  | .u8Add a b       => u8BinOp s a b "G.u8Add"
  | .u8Sub a b       => u8BinOp s a b "G.u8Sub"
  | .u8ShiftLeft a   => u8UnOp s a "G.u8ShiftLeft"
  | .u8ShiftRight a  => u8UnOp s a "G.u8ShiftRight"
  | .u8BitDecomposition a => u8UnOp s a "G.u8BitDecomposition"
  -- u32 operations: result + range constraints (`G.isU32`) on inputs
  | .u32LessThan a b =>
    (termPaths s a).flatMap fun (va, s) =>
      (termPaths s b).map fun (vb, s) =>
        let s := s.addProp s!"G.isU32 {va}" |>.addProp s!"G.isU32 {vb}"
        (s!"(G.u32LessThan {va} {vb})", s)
  -- IO: unconstrained fresh variables (loose semantics)
  | .ioGetInfo _ =>
    let (v1, s) := s.fresh "io"
    let (v2, s) := s.fresh "io"
    [(s!"({v1}, {v2})", s)]
  | .ioRead _ len =>
    let (vars, s) := List.range len |>.foldl (init := ([], s)) fun (vars, s) _ =>
      let (v, s) := s.fresh "io"; (vars ++ [v], s)
    [(s!"#[{", ".intercalate vars}]", s)]
  | .ioWrite _ ret => termPaths s ret
  | .ioSetInfo _ _ _ ret => termPaths s ret
where
  binOp (s : GenState) (a b : Term) (op : String) : List (String × GenState) :=
    (termPaths s a).flatMap fun (va, s) =>
      (termPaths s b).map fun (vb, s) => (s!"({va}{op}{vb})", s)
  u8BinOp (s : GenState) (a b : Term) (fn : String) : List (String × GenState) :=
    (termPaths s a).flatMap fun (va, s) =>
      (termPaths s b).map fun (vb, s) =>
        let s := s.addProp s!"G.isU8 {va}" |>.addProp s!"G.isU8 {vb}"
        (s!"({fn} {va} {vb})", s)
  u8UnOp (s : GenState) (a : Term) (fn : String) : List (String × GenState) :=
    (termPaths s a).map fun (va, s) =>
      let s := s.addProp s!"G.isU8 {va}"
      (s!"({fn} {va})", s)
  evalArgs (s : GenState) (args : List Term) : List (List String × GenState) :=
    args.foldl (init := [([], s)]) fun acc arg =>
      acc.flatMap fun (strs, s) =>
        (termPaths s arg).map fun (str, s) => (strs ++ [str], s)

-- ════════════════════════════════════════════════════════════
-- Function → GenEvalRel
-- ════════════════════════════════════════════════════════════

/-- Build the semantic proposition IR for a single Aiur function. -/
def mkGenEvalRel (f : Function) (ctorNames : Std.HashSet String) : GenEvalRel :=
  let fname := f.name.toName.toString (escape := false)
  let inputTypes := f.inputs.map fun (_, ty) => typToSem f.params ty
  let outputType := typToSem f.params f.output
  let sig := " → ".intercalate (inputTypes ++ [outputType, "Prop", "Prop"])
  let namedVars := f.inputs.map fun (l, _) => renderLocal l
  let initState : GenState := {
    bindings := namedVars.map fun n => (n, n)
    namedVars
    ctorNames
  }
  let paths := termPaths initState f.body
  let ctors := paths.zipIdx.map fun ((output, gs), i) =>
    -- Resolve match bindings transitively. E.g. if we have:
    --   e → (.Neg inner)   and   inner → (.Neg x)
    -- then `e` should resolve to `(.Neg (.Neg x))`.
    -- We do this by resolving the binding map itself: for each binding
    -- `v → pat`, replace occurrences of other bound variables in `pat`.
    -- We pad parens with spaces to tokenize cleanly.
    let bindings := gs.matchBindings
    let pad (s : String) := s.replace "(" "( " |>.replace ")" " )"
    let unpad (s : String) := s.replace "( " "(" |>.replace " )" ")"
    let resolvedBindings := Id.run do
      let mut m : Array (String × String) := bindings
      for _ in List.range (bindings.size + 1) do
        m := m.map fun (var, pat) =>
          let padded := pad pat
          let tokens := padded.splitOn " "
          let tokens := tokens.map fun tok =>
            match m.find? (·.1 == tok) with
            | some (_, p) => pad p
            | none => tok
          (var, unpad (" ".intercalate tokens))
      m
    let inputPats := namedVars.map fun name =>
      match resolvedBindings.find? (·.1 == name) with
      | some (_, pat) => pat
      | none => name
    { name := s!"path{i}"
      premises := gs.premises.toList.map (·.text)
      inputPats
      output
      prop := gs.renderProp : GenEvalCtor }
  { name := fname, params := f.params, sig, ctors }

-- ════════════════════════════════════════════════════════════
-- Dependency graph analysis
--
-- Computes strongly connected components of a dependency
-- graph and topologically sorts them. SCCs with >1 node
-- become `mutual` blocks; singletons are standalone.
-- Used for both type and function dependency graphs.
-- ════════════════════════════════════════════════════════════

/-- Collect all type names referenced (via `ref` / `app`) in a `Typ`. -/
partial def collectTypeRefs : Typ → List String
  | .ref g => [g.toName.toString (escape := false)]
  | .app g args => g.toName.toString (escape := false) ::
      args.toList.flatMap collectTypeRefs
  | .pointer t | .array t _ => collectTypeRefs t
  | .tuple ts => ts.toList.flatMap collectTypeRefs
  | .function args ret => args.flatMap collectTypeRefs ++ collectTypeRefs ret
  | _ => []

/-- Collect all function names called (via `app`) in a `Term`.
    Unconstrained calls are excluded since they generate no semantic premises. -/
partial def collectCalls : Term → List String
  | .app g args false => g.toName.toString (escape := false) ::
      args.flatMap collectCalls
  | .app _ args true => args.flatMap collectCalls
  | .add a b | .sub a b | .mul a b | .u8Xor a b | .u8Add a b | .u8Sub a b
  | .u8And a b | .u8Or a b | .u8LessThan a b | .u32LessThan a b =>
      collectCalls a ++ collectCalls b
  | .eqZero a | .store a | .load a | .ptrVal a | .ret a
  | .u8BitDecomposition a | .u8ShiftLeft a | .u8ShiftRight a =>
      collectCalls a
  | .ann _ t | .debug _ _ t => collectCalls t
  | .assertEq a b ret => collectCalls a ++ collectCalls b ++ collectCalls ret
  | .let _ val body => collectCalls val ++ collectCalls body
  | .match scrut branches =>
      collectCalls scrut ++ branches.flatMap fun (_, body) => collectCalls body
  | .data (.tuple ts) => ts.toList.flatMap collectCalls
  | .data (.array ts) => ts.toList.flatMap collectCalls
  | .proj t _ | .get t _ => collectCalls t
  | .slice t _ _ => collectCalls t
  | .set t _ v => collectCalls t ++ collectCalls v
  | .ioSetInfo a b c d =>
      collectCalls a ++ collectCalls b ++ collectCalls c ++ collectCalls d
  | .ioWrite a b => collectCalls a ++ collectCalls b
  | .ioGetInfo a | .ioRead a _ => collectCalls a
  | _ => []

/-- Compute SCCs of a dependency graph and return them in
    topological order (dependencies before dependents). -/
def topoSortSCCs (items : List α) (nameOf : α → String)
    (depsOf : α → List String) : List (List α) :=
  let names := items.map nameOf
  let localSet : Std.HashSet String := .ofList names
  -- Adjacency: only cross-references to other local items (self-refs excluded)
  let adj : Std.HashMap String (List String) := .ofList <|
    items.map fun item =>
      let self := nameOf item
      (self, (depsOf item |>.filter fun c =>
        c != self && localSet.contains c) |>.eraseDups)
  let nameToItem : Std.HashMap String α :=
    .ofList <| items.map fun item => (nameOf item, item)
  -- BFS reachability from a given start node
  let reachFrom (start : String) : Std.HashSet String := Id.run do
    let mut visited : Std.HashSet String := {}
    let mut queue := [start]
    for _ in List.range (names.length * names.length + 1) do
      match queue with
      | [] => break
      | n :: rest =>
        queue := rest
        if visited.contains n then continue
        visited := visited.insert n
        queue := queue ++ (adj.getD n [])
    return visited
  let reachMap : Std.HashMap String (Std.HashSet String) := .ofList <|
    names.map fun n => (n, reachFrom n)
  -- SCC: A and B are in the same SCC iff A reaches B and B reaches A
  let sccOf (name : String) : List String :=
    names.filter fun other =>
      (reachMap.getD name {}).contains other &&
      (reachMap.getD other {}).contains name
  -- Collect SCCs in source order, deduplicating
  let (sccs, _) := names.foldl (init := ([], ({} : Std.HashSet String)))
    fun (sccs, assigned) name =>
      if assigned.contains name then (sccs, assigned)
      else
        let cluster := sccOf name
        let assigned := cluster.foldl (init := assigned) fun s n => s.insert n
        (sccs ++ [cluster], assigned)
  -- Topological sort: emit an SCC only after all its dependencies are emitted
  let sccIdx : Std.HashMap String Nat := .ofList <|
    sccs.zipIdx.flatMap fun (cluster, i) => cluster.map fun n => (n, i)
  let sccDeps (cluster : List String) : Std.HashSet Nat :=
    let myIdx := sccIdx.getD cluster.head! 0
    cluster.foldl (init := {}) fun deps name =>
      (adj.getD name []).foldl (init := deps) fun deps callee =>
        let calleeIdx := sccIdx.getD callee myIdx
        if calleeIdx != myIdx then deps.insert calleeIdx else deps
  Id.run do
    let mut remaining : Std.HashSet Nat := .ofList (List.range sccs.length)
    let mut result : List (List α) := []
    for _ in List.range (sccs.length + 1) do
      if remaining.isEmpty then break
      for (cluster, i) in sccs.zipIdx do
        if !remaining.contains i then continue
        if (sccDeps cluster).toList.all fun d => !remaining.contains d then
          remaining := remaining.erase i
          result := result ++ [cluster.filterMap nameToItem.get?]
    return result

-- ════════════════════════════════════════════════════════════
-- Toplevel → GenFile
-- ════════════════════════════════════════════════════════════

/-- Build the complete file IR from an Aiur `Toplevel`. -/
def mkGenFile (top : Toplevel) (ns : String)
    (extraImports : List String) (openNs : List String) : GenFile :=
  let aliases := top.typeAliases.toList.map mkGenAlias
  let dts := top.dataTypes.toList
  let dtNameOf (dt : DataType) := dt.name.toName.toString (escape := false)
  let dtDepsOf (dt : DataType) :=
    dt.constructors.flatMap fun c => c.argTypes.flatMap collectTypeRefs
  let typeGroups := topoSortSCCs dts dtNameOf dtDepsOf
  let typeBlocks := typeGroups.map fun group =>
    let inds := group.map mkGenInductive
    match inds with
    | [ind] => GenTypeBlock.single ind
    | inds => GenTypeBlock.mutual inds
  let ctorNames : Std.HashSet String := .ofList <|
    dts.flatMap fun dt =>
      dt.constructors.map fun c =>
        s!"{dtNameOf dt}.{c.nameHead}"
  let funs := top.functions.toList
  let funNameOf (f : Function) := f.name.toName.toString (escape := false)
  let funDepsOf (f : Function) := collectCalls f.body
  let funGroups := topoSortSCCs funs funNameOf funDepsOf
  let evalBlocks := funGroups.map fun group =>
    let rels := group.map (mkGenEvalRel · ctorNames)
    match rels with
    | [r] => GenEvalBlock.single r
    | rs => GenEvalBlock.mutual rs
  { ns, imports := extraImports, opens := openNs,
    aliases, typeBlocks, evalBlocks }

-- ════════════════════════════════════════════════════════════
-- #aiur_gen command
-- ════════════════════════════════════════════════════════════

def currentFileDir : CommandElabM System.FilePath := do
  let fileName ← getFileName
  pure (System.FilePath.mk fileName |>.parent.getD ".")

syntax "#aiur_gen " ident str (" importing " ident+)? (" opening " ident+)? " #" : command

elab_rules : command
  | `(command| #aiur_gen $topId:ident $file:str
      $[ importing $imports*]? $[ opening $opens*]? #) => do
  let topName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo topId
  let fileName := file.getString
  let top ← evalToplevel topName
  let ns := topId.getId.toString (escape := false)
  let extraImports := match imports with
    | some ids => ids.toList.map fun id => id.getId.toString (escape := false)
    | none => []
  let openNs := match opens with
    | some ids => ids.toList.map fun id => id.getId.toString (escape := false)
    | none => []
  let genFile := mkGenFile top ns extraImports openNs
  let dir ← currentFileDir
  let outPath := dir / fileName
  IO.FS.writeFile outPath genFile.render
  logInfo m!"#aiur_gen: wrote {top.dataTypes.size} types, {top.functions.size} functions to {outPath}"

end Aiur.Formal

end
