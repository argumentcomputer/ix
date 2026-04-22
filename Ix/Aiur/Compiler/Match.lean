module
public import Ix.Aiur.Compiler.Check
public import Ix.Aiur.Stages.Simple
public import Ix.SmallMap

/-!
Match compiler: `Typed.Term` → `Simple.Term`.

Consumes `Typed.Term` and produces `Simple.Term` directly. The double
`checkFunction` pass goes away because we no longer round-trip through
untyped `Term`.

Decision-tree style with Maranget's heuristics:
- `.or` subpatterns → duplicated rows via DNF-product.
- Nested subpatterns → bare `Local` with guard rows for the children.
- `.pointer` subpatterns → `.letLoad` to materialise the dereferenced value, then
  match on that value.
- Non-exhaustive matches: the diagnostics flag `missing` is set; downstream
  (`Simple.lean`) converts this into `CheckError.nonExhaustiveMatch`.

`Simple.Term`'s `.match` admits matches in `letVar`-RHS positions
only; this is exactly what `findNonTailMatch` detects in `Lower`.
-/

public section

namespace Aiur

namespace MatchCompiler

open Typed

abbrev TermId := Nat
/-- A term plus a unique id — used so we can share a value across multiple
guards without re-evaluating. -/
abbrev UniqTerm := TermId × Term

/-- The patterns that `Simple.Pattern` admits directly, plus a `pointer` form
that the match compiler lowers to a `letLoad`. -/
inductive SPattern
  | field : G → SPattern
  | ref : Global → Array Local → SPattern
  | tuple : Array Local → SPattern
  | array : Array Local → SPattern
  /-- `pointer v t` binds `v` to the dereferenced value; `t` is the element type
      (the `inner` of the pointer type), needed so `Simple.TermInner.letLoad`
      can be produced with its required type annotation. -/
  | pointer : Local → Typ → SPattern
  deriving BEq, Hashable, Inhabited

structure Clause where
  pat : SPattern
  guards : Array (Pattern × UniqTerm)
  body : UniqTerm
  deriving Inhabited

structure ExtTerm where
  renames : Array (Local × Term)
  value : Term
  deriving Inhabited

structure Row where
  clauses : Array Clause
  body : ExtTerm
  uniqId : TermId
  deriving Inhabited

structure Diagnostics where
  missing : Bool
  reachable : List Term
  deriving Inhabited

structure Compiler where
  uniqId : TermId
  decls : Source.Decls
  diagnostics : Diagnostics

abbrev CompilerM := StateM Compiler

def setId (id : TermId) : CompilerM Unit :=
  modify fun stt => { stt with uniqId := id }

def newId : CompilerM TermId := do
  let varId ← Compiler.uniqId <$> get
  modify fun stt => { stt with uniqId := stt.uniqId + 1 }
  pure varId

/-- Look up the constructor's argument types in `decls`, with template
parameters substituted according to the scrutinee's concrete type arguments.
Returns an empty array if the global isn't a constructor.

For a templated constructor like `TList.TCons : G → &TList‹A› → TList‹A›`,
calling this with `scrutTyp = .app TList [.field]` returns
`[.field, .pointer (.app TList [.field])]` — A has been substituted with G.
Without this substitution, fresh vars introduced by the match compiler would
carry stale `.ref A` annotations that downstream passes can't resolve. -/
private def constructorArgTypes (decls : Source.Decls) (g : Global)
    (scrutTyp : Typ) : Array Typ :=
  match decls.getByKey g with
  | some (.constructor dt ctor) =>
    let subst : Global → Option Typ :=
      match scrutTyp with
      | .app _ args => mkParamSubst dt.params args
      | _ => fun _ => none
    (ctor.argTypes.map (Typ.instantiate subst)).toArray
  | _ => #[]

/-- Convert a source-language `Pattern` into a guarded `SPattern` clause set via
DNF-product rewriting. Does not enter nested patterns — those become guard rows.

Each fresh per-arg `Local` is bound at the *correct* type — pulled from the
parent constructor/tuple/array — so downstream passes (e.g. `.pointer` arms
of `decisionToTyped`) can read the right type off the bound `.var` term. -/
def dnfProd (branches: List $ Pattern × UniqTerm) (body : ExtTerm) : CompilerM (Array Row) := do
  let initId ← Compiler.uniqId <$> get
  let stt ← get
  let decls := stt.decls
  let rec aux := fun renames clauses branches body => match branches with
    | [] => do
      let id ← Compiler.uniqId <$> get
      let row := ⟨clauses, { body with renames := body.renames ++ renames }, id⟩
      setId initId
      pure #[row]
    | (.or patL patR, term) :: rest => do
      let rowsL ← aux renames clauses ((patL, term) :: rest) body
      let rowsR ← aux renames clauses ((patR, term) :: rest) body
      pure $ rowsL ++ rowsR
    | (.wildcard, _) :: rest => aux renames clauses rest body
    | (.var var, (_, term)) :: rest => aux (renames.push (var, term)) clauses rest body
    | (.field g, term) :: rest => aux renames (clauses.push ⟨.field g, #[], term⟩) rest body
    | (.tuple args, term) :: rest => do
      let argTypes := match term.snd.typ with
        | .tuple ts => ts
        | _ => Array.replicate args.size .unit
      let (vars, guards) ← flattenArgs args argTypes
      let clause := ⟨.tuple vars, guards, term⟩
      aux renames (clauses.push clause) rest body
    | (.array args, term) :: rest => do
      let eltTyp := match term.snd.typ with
        | .array t _ => t
        | _ => .unit
      let argTypes := Array.replicate args.size eltTyp
      let (vars, guards) ← flattenArgs args argTypes
      let clause := ⟨.array vars, guards, term⟩
      aux renames (clauses.push clause) rest body
    | (.ref global args, term) :: rest => do
      let argTypes := constructorArgTypes decls global term.snd.typ
      let (vars, guards) ← flattenArgs args.toArray argTypes
      let clause := ⟨.ref global vars, guards, term⟩
      aux renames (clauses.push clause) rest body
    | (.pointer arg, term) :: rest => do
      let id ← newId
      let var := .idx id
      let innerTyp := match term.snd.typ with
        | .pointer t => t
        | _ => .unit
      let guards := #[(arg, (id, (Typed.Term.var innerTyp false var : Term)))]
      let clause := ⟨.pointer var innerTyp, guards, term⟩
      aux renames (clauses.push clause) rest body
  aux Array.empty Array.empty branches body
where
  flattenArgs (args : Array Pattern) (argTypes : Array Typ) := do
    let varIds ← args.mapM fun _ => newId
    let guards := args.zip varIds |>.mapIdx fun i (arg, id) =>
      let typ := argTypes[i]?.getD .unit
      (arg, (id, (Typed.Term.var typ false (.idx id) : Term)))
    pure (varIds.map .idx, guards)

inductive Decision
  | success : ExtTerm → Decision
  | failure
  /-- `switch scrutVar scrutTyp cases fallback` — `scrutTyp` is the type of
  `scrutVar` at the point of the switch. Preserving it is necessary so
  `decisionToTyped` can emit each nested `.match` with the correct scrutinee
  type annotation; downstream `Concretize.rewritePattern` consults that type
  to pick the right monomorphic constructor name (e.g. `List.Nil` →
  `List.G.Nil` when the scrutinee is `List<G>`). -/
  | switch : Local → Typ → List (SPattern × Decision) → Decision → Decision
  | letLoad : (dst : Local) → (dstTyp : Typ) → (src : Local) → Decision → Decision
  | let : Local → Term → Decision → Decision
  deriving Inhabited

def modifyDiagnostics (f : Diagnostics → Diagnostics) : CompilerM Unit :=
  modify fun stt => { stt with diagnostics := f stt.diagnostics }

def patTypeLength (decls : Source.Decls) : SPattern → Nat
  | .field _ => gSize.toNat
  | .tuple _ => 1
  | .array _ => 1
  | .ref global _ => typeLookup global |>.constructors.length
  | .pointer _ _ => 1
where
  typeLookup (global : Global) :=
    match global.popNamespace with
    | some (_, enum) => match decls.getByKey enum with
      | some (.dataType typ) => typ
      | _ => ⟨⟨.anonymous⟩, [], []⟩
    | none => ⟨⟨.anonymous⟩, [], []⟩

def extractSPatterns (rows : Array Row) (term : UniqTerm) : SmallMap SPattern (Array Row) :=
  rows.foldl (init := default) processRow
where
  processRow map row := row.clauses.foldl (init := map) processClause
  processClause map clause :=
    if term.fst == clause.body.fst then map.insert clause.pat #[] else map

def removeFirstInstance (find : α → Bool) (vec : Array α) : Option (α × Array α) :=
  match h : vec.findIdx? find with
  | none => none
  | some i =>
    let filtered := vec.extract 0 i ++ vec.extract (i + 1) vec.size
    have := Array.findIdx?_eq_some_iff_findIdx_eq.mp h |>.left
    some (vec[i], filtered)

def rowRemoveClause (row : Row) (term : UniqTerm) : Option (Clause × Row) :=
  let id := term.fst
  match removeFirstInstance (·.body.fst == id) row.clauses with
  | some (deletedClause, restClauses) => some (deletedClause, { row with clauses := restClauses })
  | none => none

def switch (cases : List (SPattern × Decision)) (fallback : Decision) : UniqTerm → Decision
  | (_, .var typ _ var) => .switch var typ cases fallback
  | (id, term) => let var := .idx id; .let var term (.switch var term.typ cases fallback)

/-! Maranget's decision-tree algorithm terminates on well-formed inputs via
a measure on row-matrices, but reducing that measure to a Lean `Nat` is
delicate. We use a fuel bound threaded through the mutual block; the outer
`compileRows` entry picks a generous bound computed from the row matrix.

When fuel runs out we return `.failure` (surfaced as nonExhaustive downstream),
which would be a bug for well-formed inputs — the bound is chosen to be
unreachable on any practical Aiur program. -/

/-- Row dispatcher used by `compileSwitchBound`. Pulled out as a top-level
function (rather than a `where`) to avoid an implicit mutual cycle. -/
private def processRow (term : UniqTerm) : SmallMap SPattern (Array Row) × Array Row →
    Row → CompilerM (SmallMap SPattern (Array Row) × Array Row) :=
  fun (rowMap, fallbackRows) row =>
    match rowRemoveClause row term with
    | some (clause, row') => do
      setId row.uniqId
      let newRows ← dnfProd clause.guards.toList row'.body
      let newRows := newRows.map (fun r => { r with clauses := r.clauses ++ row'.clauses })
      let updatedMap := rowMap.update clause.pat (· ++ newRows)
      pure (updatedMap, fallbackRows)
    | none => pure (rowMap.map (·.push row), fallbackRows.push row)

mutual

def compileSwitchBound : Nat → Array Row → UniqTerm → CompilerM Decision
  | 0, _, _ => pure .failure
  | bound+1, rows, term => do
    let stt ← get
    let numCases := patTypeLength stt.decls rows[0]!.clauses[0]!.pat
    let spatMap := extractSPatterns rows term
    let size := spatMap.size
    if size == numCases then
      let (rowMap, _) ← rows.foldlM (init := (spatMap, #[])) (processRow term)
      let cases ← rowMap.toList.mapM fun (pat, rows) =>
        Prod.mk pat <$> compileRowsBound bound rows
      setId stt.uniqId
      pure $ switch cases .failure term
    else
      let (rowMap, fallbackRows) ← rows.foldlM (init := (spatMap, #[])) (processRow term)
      let cases ← rowMap.toList.mapM fun (pat, rows) =>
        Prod.mk pat <$> compileRowsBound bound rows
      let fallback ← compileRowsBound bound fallbackRows
      setId stt.uniqId
      pure $ switch cases fallback term
termination_by bound _ _ => (bound, 0)

def compileRowsBound : Nat → Array Row → CompilerM Decision
  | 0, _ => do
    modifyDiagnostics fun d => { d with missing := true }
    pure .failure
  | bound+1, rows =>
    match rows[0]? with
    | some row => match row.clauses[0]? with
      | some clause => compileSwitchBound bound rows clause.body
      | none => do
        modifyDiagnostics fun d => { d with reachable := row.body.value :: d.reachable }
        pure $ .success row.body
    | none => do
      modifyDiagnostics fun d => { d with missing := true }
      pure .failure
termination_by bound _ => (bound, 1)

end

/-- Estimated bound on the compile-matrix recursion depth. Conservative:
twice the sum of (rows × max-clauses-per-row), plus 1024 slack. -/
private def rowBound (rows : Array Row) : Nat :=
  let maxClauses := rows.foldl (init := 0) fun acc row => max acc row.clauses.size
  rows.size * (1 + maxClauses) * 2 + 1024

def compileSwitch (rows : Array Row) (term : UniqTerm) : CompilerM Decision :=
  compileSwitchBound (rowBound rows) rows term

def compileRows (rows : Array Row) : CompilerM Decision :=
  compileRowsBound (rowBound rows) rows

def compile (term : Term) (rules : List (Pattern × Term)) : CompilerM (Decision × Diagnostics) := do
  let id ← newId
  let rows ← rules.foldlM (init := #[]) fun acc rule => do
    let newRows ← fromRule id rule
    pure $ acc ++ newRows
  let tree ← compileRows rows
  let diagnostics ← Compiler.diagnostics <$> get
  pure (tree, diagnostics)
where
  fromRule id rule :=
    let (pat, bod) := rule
    dnfProd [(pat, (id, term))] ⟨#[], bod⟩

def runWithNewCompiler (decls : Source.Decls) (f : CompilerM α) : α :=
  StateT.run' f ⟨0, decls, ⟨false, []⟩⟩

def runMatchCompiler (decls : Source.Decls) (term : Term) (rules : List (Pattern × Term)) :
    Decision × Diagnostics :=
  runWithNewCompiler decls (compile term rules)

/-! ## Decision tree → Simple.Term

The decision tree is lowered into `Simple.Term` directly, preserving types from
the input `Typed.Term`s. `pointer`-guard rows become `.letLoad` nodes.

Non-exhaustive matches produce `none` on the `Decision.failure` branch; the caller
(`Compiler/Simple.lean`) surfaces this as `CheckError.nonExhaustiveMatch`.
-/

def sPatternToSimple : SPattern → Option Simple.Pattern
  | .field g => some (.field g)
  | .ref global vars => some (.ref global vars)
  | .tuple vars => some (.tuple vars)
  | .array vars => some (.array vars)
  /- pointer patterns are converted into a `.letLoad` before emission -/
  | .pointer _ _ => none

/-- Translate a typed term to a simple term, traversing the new plain-inductive
shape: pattern-match on each `Typed.Term` constructor and rebuild as the
matching `Simple.Term` constructor. Pulled out of the `decisionToSimple`
mutual block since it doesn't recurse on `Decision`. -/
def typedToSimple : Term → Simple.Term
  | .unit τ e => .unit τ e
  | .var τ e l => .var τ e l
  | .ref τ e g tArgs => .ref τ e g tArgs
  | .field τ e g => .field τ e g
  | .tuple τ e ts => .tuple τ e (ts.attach.map fun ⟨t, _⟩ => typedToSimple t)
  | .array τ e ts => .array τ e (ts.attach.map fun ⟨t, _⟩ => typedToSimple t)
  | .ret τ e sub => .ret τ e (typedToSimple sub)
  | .let τ e _pat v b =>
    -- Post-simplify, non-trivial `let`s were rewritten. Treat any survivor as
    -- a wildcard let.
    .letWild τ e (typedToSimple v) (typedToSimple b)
  | .match τ e _scrut _bs =>
    -- Post-simplify, matches are re-compiled by `runMatchCompiler`. A raw
    -- `match` here means it didn't pass through `simplifyTerm`; default to unit.
    .unit τ e
  | .app τ e g tArgs args u =>
    .app τ e g tArgs (args.attach.map fun ⟨t, _⟩ => typedToSimple t) u
  | .add τ e a b => .add τ e (typedToSimple a) (typedToSimple b)
  | .sub τ e a b => .sub τ e (typedToSimple a) (typedToSimple b)
  | .mul τ e a b => .mul τ e (typedToSimple a) (typedToSimple b)
  | .eqZero τ e a => .eqZero τ e (typedToSimple a)
  | .proj τ e a n => .proj τ e (typedToSimple a) n
  | .get τ e a n => .get τ e (typedToSimple a) n
  | .slice τ e a i j => .slice τ e (typedToSimple a) i j
  | .set τ e a n v => .set τ e (typedToSimple a) n (typedToSimple v)
  | .store τ e a => .store τ e (typedToSimple a)
  | .load τ e a => .load τ e (typedToSimple a)
  | .ptrVal τ e a => .ptrVal τ e (typedToSimple a)
  | .assertEq τ e a b r => .assertEq τ e (typedToSimple a) (typedToSimple b) (typedToSimple r)
  | .ioGetInfo τ e k => .ioGetInfo τ e (typedToSimple k)
  | .ioSetInfo τ e k i l r =>
    .ioSetInfo τ e (typedToSimple k) (typedToSimple i) (typedToSimple l) (typedToSimple r)
  | .ioRead τ e i n => .ioRead τ e (typedToSimple i) n
  | .ioWrite τ e d r => .ioWrite τ e (typedToSimple d) (typedToSimple r)
  | .u8BitDecomposition τ e a => .u8BitDecomposition τ e (typedToSimple a)
  | .u8ShiftLeft τ e a => .u8ShiftLeft τ e (typedToSimple a)
  | .u8ShiftRight τ e a => .u8ShiftRight τ e (typedToSimple a)
  | .u8Xor τ e a b => .u8Xor τ e (typedToSimple a) (typedToSimple b)
  | .u8Add τ e a b => .u8Add τ e (typedToSimple a) (typedToSimple b)
  | .u8Sub τ e a b => .u8Sub τ e (typedToSimple a) (typedToSimple b)
  | .u8And τ e a b => .u8And τ e (typedToSimple a) (typedToSimple b)
  | .u8Or τ e a b => .u8Or τ e (typedToSimple a) (typedToSimple b)
  | .u8LessThan τ e a b => .u8LessThan τ e (typedToSimple a) (typedToSimple b)
  | .u32LessThan τ e a b => .u32LessThan τ e (typedToSimple a) (typedToSimple b)
  | .debug τ e l t r =>
    let t' := match t with | none => none | some sub => some (typedToSimple sub)
    .debug τ e l t' (typedToSimple r)
termination_by t => sizeOf t
decreasing_by all_goals first | decreasing_tactic | grind

def decisionToSimple (retTyp : Typ) : Decision → Option Simple.Term
  | .failure => none
  | .success ⟨renames, value⟩ =>
    let base := typedToSimple value
    some (renames.foldr (init := base) fun (x, term) acc =>
      let rhs := typedToSimple term
      Simple.Term.letVar acc.typ acc.escapes x rhs acc)
  | .switch ptr _ [(.pointer val innerTyp, body)] _ =>
    match decisionToSimple retTyp body with
    | none => none
    | some body' =>
      some (Simple.Term.letLoad body'.typ body'.escapes val innerTyp ptr body')
  | .switch var _ branches dflt => do
    -- `.failure → none` is exactly what `decisionToSimple retTyp .failure`
    -- returns, so we can skip the outer case-split on `dflt`.
    let defaultOpt : Option Simple.Term := decisionToSimple retTyp dflt
    let cases ← branches.attach.foldlM (init := #[]) fun acc ⟨(spat, tree), _⟩ => do
      match sPatternToSimple spat with
      | none       => none
      | some sPat  =>
        let body ← decisionToSimple retTyp tree
        pure (acc.push (sPat, body))
    some (Simple.Term.match retTyp false var cases defaultOpt)
  | .letLoad dst dstTyp src body =>
    match decisionToSimple retTyp body with
    | none => none
    | some body' =>
      some (Simple.Term.letLoad body'.typ body'.escapes dst dstTyp src body')
  | .let var term body =>
    match decisionToSimple retTyp body with
    | none => none
    | some body' =>
      let rhs := typedToSimple term
      some (Simple.Term.letVar body'.typ body'.escapes var rhs body')
termination_by d => sizeOf d
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
    | grind

/-! ## Decision → Typed.Term

`decisionToTyped` is the direct analogue of `decisionToSimple` that stays in
`Typed.Term` form so the downstream `Concretize` pass can consume it. Every
output `.match` has a single-level pattern shape (`.field`, `.ref _ vars`,
`.tuple vars`, `.array vars`, or top-level `.var` / `.wildcard`), so the
simplified matches land in the subset that `Concretize.termToConcrete`
already handles natively.

`.pointer` in the source is modelled here as `.let x = load ptr in ...`
plus a matching `.switch` on the loaded value. -/

/-- Convert a decision-tree `SPattern` back to a `Source.Pattern`, where
each sub-`Local` becomes a top-level `.var` binding. Returns `none` for
`.pointer` (handled one level up by emitting a `let load` before the match). -/
def sPatternToTypedPattern : SPattern → Option Pattern
  | .field g => some (.field g)
  | .ref g vars => some (.ref g (vars.toList.map (.var)))
  | .tuple vars => some (.tuple (vars.map (.var)))
  | .array vars => some (.array (vars.map (.var)))
  | .pointer _ _ => none

/-- Convert a decision tree to a `Typed.Term`. `retTyp` is the match's return
type; `scrutTyp` is the *outermost* scrutinee's type — used for the `.var`
node we emit at the top-level `.match` so downstream passes see the correct
type. Sub-`.switch` nodes (introduced by nested patterns) inherit their
scrutinee type from the parent's pattern arg, but those types aren't
needed by the `Concretize`/`Lower` path (which only inspects the top
scrut), so we re-use `scrutTyp` recursively as a placeholder. -/
def decisionToTyped (retTyp : Typ) (scrutTyp : Typ) : Decision → Option Term
  | .failure => none
  | .success ⟨renames, value⟩ =>
    -- Apply renames as a chain of `.let`s with simple `.var` patterns.
    some (renames.foldr (init := value) fun (x, term) acc =>
      Term.let acc.typ acc.escapes (.var x) term acc)
  | .switch ptr _ [(.pointer val innerTyp, body)] _ =>
    -- Single pointer-pattern case: `let val = load ptr in body`.
    match decisionToTyped retTyp innerTyp body with
    | none => none
    | some body' =>
      let loadTerm : Term := .load innerTyp false (.var (.pointer innerTyp) false ptr)
      some (.let body'.typ body'.escapes (.var val) loadTerm body')
  | .switch var switchTyp branches dflt => do
    let defaultOpt : Option Term := decisionToTyped retTyp switchTyp dflt
    let cases ← branches.attach.foldlM (init := #[]) fun acc ⟨(spat, tree), _⟩ => do
      match sPatternToTypedPattern spat with
      | none      => none
      | some pat  =>
        let body ← decisionToTyped retTyp switchTyp tree
        pure (acc.push (pat, body))
    -- `Typed.Term.match` expects `List (Pattern × Term)`; add a wildcard
    -- default case at the end so coverage is explicit.
    let casesList : List (Pattern × Term) := cases.toList
    let casesList := match defaultOpt with
      | some d => casesList ++ [(.wildcard, d)]
      | none   => casesList
    some (.match retTyp false (.var switchTyp false var) casesList)
  | .letLoad dst dstTyp src body =>
    match decisionToTyped retTyp scrutTyp body with
    | none => none
    | some body' =>
      let loadTerm : Term := .load dstTyp false (.var (.pointer dstTyp) false src)
      some (.let body'.typ body'.escapes (.var dst) loadTerm body')
  | .let var term body =>
    match decisionToTyped retTyp scrutTyp body with
    | none => none
    | some body' =>
      some (.let body'.typ body'.escapes (.var var) term body')
termination_by d => sizeOf d
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
    | grind

end MatchCompiler

end Aiur

end
