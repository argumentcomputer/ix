module
public import Ix.Aiur.Stages.Typed
public import Std.Data.HashSet
public import Std.Data.HashMap

/-!
Type checker: `Source.Toplevel` → `Typed.Decls`.

The output `Typed.Term` has the flattened `.tuple` / `.array` constructors.
`Match.lean` consumes `Typed.Term` directly, which eliminates the double
`checkFunction` pass.

Totality requires an `Ix.Array.Induction` helper library.
-/

public section
@[expose] section

namespace Aiur

inductive CheckError
  | duplicatedDefinition : Global → CheckError
  | unboundGlobal : Global → CheckError
  | unboundLocal : Local → CheckError
  | notAConstructor : Global → CheckError
  | notAValue : Global → CheckError
  | notAFunction : Global → CheckError
  | cannotApply : Global → CheckError
  | notADataType : Global → CheckError
  | wrongNumTypeArgs : Global → Nat → Nat → CheckError
  | duplicatedTypeParam : Global → String → CheckError
  | typeMismatch : Typ → Typ → CheckError
  | illegalReturn : CheckError
  | wrongNumArgs : Global → Nat → Nat → CheckError
  | notATuple : Typ → CheckError
  | notAnArray : Typ → CheckError
  | emptyArray : CheckError
  | indexOoB : Nat → CheckError
  | negativeRange : Nat → Nat → CheckError
  | rangeOoB : Nat → Nat → CheckError
  | incompatiblePattern : Pattern → Typ → CheckError
  | differentBindings : List (Local × Typ) → List (Local × Typ) → CheckError
  | emptyMatch
  | branchMismatch : Typ → Typ → CheckError
  | notAPointer : Typ → CheckError
  | duplicatedBind : Pattern → CheckError
  | typeAliasCycle : Global → CheckError
  | unconstrainedConstructor : Global → CheckError
  | infiniteType : Nat → Typ → CheckError
  | unresolvedMVar : Nat → CheckError
  -- Non-exhaustive match becomes a CheckError instead of bubbling to
  -- `unreachable!` in the match compiler.
  | nonExhaustiveMatch : CheckError
  deriving Repr

instance : ToString CheckError where
  toString e := repr e |>.pretty

open Source

/-- Apply a type-parameter substitution to a type. -/
def Typ.instantiate (subst : Global → Option Typ) : Typ → Typ
  | .unit => .unit
  | .field => .field
  | .tuple ts => .tuple (ts.attach.map (fun ⟨t, _⟩ => Typ.instantiate subst t))
  | .array t n => .array (Typ.instantiate subst t) n
  | .pointer t => .pointer (Typ.instantiate subst t)
  | .ref g => (subst g).getD (.ref g)
  | .app g args => .app g (args.attach.map (fun ⟨t, _⟩ => Typ.instantiate subst t))
  | .function ins out =>
      .function (ins.attach.map (fun ⟨t, _⟩ => Typ.instantiate subst t)) (Typ.instantiate subst out)
  | .mvar n => .mvar n
termination_by t => sizeOf t

def mkParamSubst (params : List String) (args : Array Typ) : Global → Option Typ :=
  let m : Std.HashMap Global Typ := (params.zip args.toList).foldl
    (fun m (p, t) => m.insert (Global.init p) t) {}
  fun g => m[g]?

/-- Bounded alias-expansion. The `bound` caps how many times we can re-enter
via a `.app`/`.ref` alias expansion; the outer interface uses
`toplevelAliases.size + 1`, which the monotonic growth of `visited` (capped
at `toplevelAliases.size`) guarantees is never exhausted on well-formed
inputs. -/
def expandTypeMBound : Nat → Std.HashSet Global → Array TypeAlias →
    Typ → StateT (Std.HashMap Global Typ) (Except CheckError) Typ
  | _, _, _, .unit => pure .unit
  | _, _, _, .field => pure .field
  | bound, visited, tops, .pointer t => do
    pure $ .pointer (← expandTypeMBound bound visited tops t)
  | bound, visited, tops, .function inputs output => do
    let inputs' ← inputs.attach.mapM fun ⟨t, _⟩ =>
      expandTypeMBound bound visited tops t
    let output' ← expandTypeMBound bound visited tops output
    pure $ .function inputs' output'
  | bound, visited, tops, .tuple ts => do
    let ts' ← ts.attach.mapM fun ⟨t, _⟩ =>
      expandTypeMBound bound visited tops t
    pure $ .tuple ts'
  | bound, visited, tops, .array t n => do
    let t' ← expandTypeMBound bound visited tops t
    pure $ .array t' n
  | bound, visited, tops, .app g args => do
    let args' ← args.attach.mapM fun ⟨t, _⟩ =>
      expandTypeMBound bound visited tops t
    if let some alias := tops.find? (·.name == g) then
      if visited.contains g then
        throw $ .typeAliasCycle g
      if alias.params.length != args'.size then
        throw $ .wrongNumTypeArgs g alias.params.length args'.size
      let subst := mkParamSubst alias.params args'
      let instantiated := Typ.instantiate subst alias.expansion
      match bound with
      | 0 => pure $ .app g args'  -- bound exhausted; fall back
      | bound+1 =>
        expandTypeMBound bound (visited.insert g) tops instantiated
    else
      pure $ .app g args'
  | bound, visited, tops, .ref g => do
    let aliasMap ← get
    if let some expanded := aliasMap[g]? then
      return expanded
    if let some (alias : TypeAlias) := tops.find? (·.name == g) then
      if visited.contains g then
        throw $ .typeAliasCycle g
      if !alias.params.isEmpty then
        throw $ .wrongNumTypeArgs g alias.params.length 0
      match bound with
      | 0 => pure $ .ref g  -- bound exhausted; fall back
      | bound+1 =>
        let expanded ← expandTypeMBound bound (visited.insert g)
          tops alias.expansion
        set (aliasMap.insert g expanded)
        return expanded
    else
      pure $ .ref g
  | _, _, _, .mvar n => pure $ .mvar n
termination_by bound _ _ t => (bound, sizeOf t)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right
       first
         | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; simp +arith; omega)
         | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp +arith; omega)
         | (simp +arith; omega)
         | grind)

/-- Outer interface. Uses `toplevelAliases.size + 1` as the bound. -/
def expandTypeM (visited : Std.HashSet Global) (toplevelAliases : Array TypeAlias)
    (t : Typ) : StateT (Std.HashMap Global Typ) (Except CheckError) Typ :=
  expandTypeMBound (toplevelAliases.size + 1) visited toplevelAliases t

/-- Constructs a map of declarations from a toplevel, expanding all type aliases. -/
def Source.Toplevel.mkDecls (toplevel : Source.Toplevel) : Except CheckError Source.Decls := do
  let mut allNames : Std.HashSet Global := {}
  for alias in toplevel.typeAliases do
    if allNames.contains alias.name then
      throw $ .duplicatedDefinition alias.name
    allNames := allNames.insert alias.name

  let initAliasMap := {}
  let (_, finalAliasMap) ← (toplevel.typeAliases.mapM fun (alias : TypeAlias) => do
    let expanded ← expandTypeM {} toplevel.typeAliases alias.expansion
    modify fun (aliasMap : Std.HashMap Global Typ) => aliasMap.insert alias.name expanded
  ).run initAliasMap

  let expandTyp (typ : Typ) : Except CheckError Typ :=
    (expandTypeM {} toplevel.typeAliases typ).run' finalAliasMap

  let mut decls : Decls := default
  for function in toplevel.functions do
    if allNames.contains function.name then
      throw $ .duplicatedDefinition function.name
    allNames := allNames.insert function.name
    let inputs' ← function.inputs.mapM fun (loc, typ) => do
      let typ' ← expandTyp typ
      pure (loc, typ')
    let output' ← expandTyp function.output
    let function' := { function with inputs := inputs', output := output' }
    decls := decls.insert function.name (.function function')

  for dataType in toplevel.dataTypes do
    if allNames.contains dataType.name then
      throw $ .duplicatedDefinition dataType.name
    allNames := allNames.insert dataType.name
    let mut constructors : List Constructor := []
    for ctor in dataType.constructors do
      let argTypes' ← ctor.argTypes.mapM expandTyp
      constructors := constructors.concat { ctor with argTypes := argTypes' }
    let dataType' := { dataType with constructors }
    decls := decls.insert dataType.name (.dataType dataType')
    for ctor in constructors do
      let ctorName := dataType.name.pushNamespace ctor.nameHead
      if allNames.contains ctorName then
        throw $ .duplicatedDefinition ctorName
      allNames := allNames.insert ctorName
      decls := decls.insert ctorName (.constructor dataType' ctor)

  pure decls

/-! ## Inference monad and unification -/

structure CheckContext where
  decls : Decls
  varTypes : Std.HashMap Local Typ
  returnType : Typ
  typeParams : List String

structure CheckState where
  nextMVar : Nat := 0
  mvarSubst : Std.HashMap Nat Typ := {}

abbrev CheckM := ReaderT CheckContext (StateT CheckState (Except CheckError))

def freshMVar : CheckM Typ := do
  let idx := (← get).nextMVar
  modify fun s => { s with nextMVar := s.nextMVar + 1 }
  pure $ .mvar idx

/-! ## mvar-chain helpers

`walkTyp` follows the mvar substitution chain until it hits a non-mvar or an
unbound mvar. With the occurs check maintained by `bindMVar`, the chain is
acyclic in practice; the `visited` set makes the function total regardless,
and the `bound` parameter caps the Nat-termination measure.

Outer interface `walkTyp` uses `CheckState.nextMVar + 1` as the bound —
every mvar id is `< nextMVar`, and the visited set ensures no id is visited
twice, so the chain length is at most `nextMVar`. -/

/-- Bounded walk; see `walkTyp` for the outer interface. -/
def walkTypBound : Nat → Std.HashSet Nat → Typ → CheckM Typ
  | bound, visited, .mvar id => do
    if visited.contains id then pure (.mvar id)
    else match bound with
      | 0 => pure (.mvar id)
      | bound+1 =>
        match (← get).mvarSubst[id]? with
        | some t => walkTypBound bound (visited.insert id) t
        | none   => pure (.mvar id)
  | _, _, t => pure t
termination_by bound _ _ => bound

/-- Outer interface. The bound is `nextMVar + 1`, which cannot be exhausted
because the visited set grows by one on each step and is capped at `nextMVar`.
Returns the original type if the chain bound runs out (defensive). -/
def walkTyp (t : Typ) : CheckM Typ := do
  let s ← get
  walkTypBound (s.nextMVar + 1) {} t

/-- Bounded occurs check. Follows both mvar chains and the structural
recursion through `Typ`. -/
def occursInBound : Nat → Nat → Std.HashSet Nat → Typ → CheckM Bool
  | id, bound, visited, .mvar id' => do
    if id == id' then pure true
    else if visited.contains id' then pure false
    else match bound with
      | 0 => pure false
      | bound+1 =>
        match (← get).mvarSubst[id']? with
        | some t => occursInBound id bound (visited.insert id') t
        | none   => pure false
  | id, bound, visited, .tuple ts =>
    ts.attach.anyM fun ⟨t, _⟩ => occursInBound id bound visited t
  | id, bound, visited, .array t _ => occursInBound id bound visited t
  | id, bound, visited, .pointer t => occursInBound id bound visited t
  | id, bound, visited, .function ins out => do
    if ← ins.attach.anyM fun ⟨t, _⟩ => occursInBound id bound visited t then
      pure true
    else occursInBound id bound visited out
  | id, bound, visited, .app _ args =>
    args.attach.anyM fun ⟨t, _⟩ => occursInBound id bound visited t
  | _, _, _, _ => pure false
termination_by _ bound _ t => (bound, sizeOf t)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right
       first
         | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; simp +arith; omega)
         | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp +arith; omega)
         | (simp +arith; omega)
         | grind)

/-- Outer interface for the occurs check. -/
def occursIn (id : Nat) (t : Typ) : CheckM Bool := do
  let s ← get
  occursInBound id (s.nextMVar + 1) {} t

def bindMVar (id : Nat) (t : Typ) : CheckM Unit := do
  if ← occursIn id t then throw $ .infiniteType id t
  modify fun s => { s with mvarSubst := s.mvarSubst.insert id t }

/-- Bounded unification. The `bound` caps the structural recursion depth after
each `walkTyp` call — each recursive step consumes one unit of `bound`. On
well-formed inputs, `sizeOf t1 + sizeOf t2 + nextMVar + 1` is always enough,
which is what the outer `unifyTyp` uses.

When `bound` runs out we return `false` (defensive) rather than diverging. -/
def unifyTypBound : Nat → Typ → Typ → CheckM Bool
  | 0, _, _ => pure false
  | bound+1, t1, t2 => do
    let t1 ← walkTyp t1
    let t2 ← walkTyp t2
    match t1, t2 with
    | .mvar a, .mvar b =>
      if a == b then pure true else do bindMVar a (.mvar b); pure true
    | .mvar a, _ => do bindMVar a t2; pure true
    | _, .mvar b => do bindMVar b t1; pure true
    | .unit, .unit | .field, .field => pure true
    | .tuple ts1, .tuple ts2 =>
      if ts1.size != ts2.size then pure false else
        ts1.zip ts2 |>.allM fun (x, y) => unifyTypBound bound x y
    | .array t1' n1, .array t2' n2 =>
      if n1 != n2 then pure false else unifyTypBound bound t1' t2'
    | .pointer t1', .pointer t2' => unifyTypBound bound t1' t2'
    | .ref g1, .ref g2 => pure (g1 == g2)
    | .function ins1 out1, .function ins2 out2 => do
      if ins1.length != ins2.length then pure false else
      let inOk ← ins1.zip ins2 |>.allM fun (x, y) => unifyTypBound bound x y
      if !inOk then pure false else unifyTypBound bound out1 out2
    | .app g1 a1, .app g2 a2 =>
      if g1 != g2 || a1.size != a2.size then pure false else
        a1.zip a2 |>.allM fun (x, y) => unifyTypBound bound x y
    | _, _ => pure false
termination_by bound _ _ => bound

/-- Computable structural "node count" on `Typ`. Used as a finite, runtime-
available proxy for `sizeOf` in `unifyTyp`'s bound. -/
def Typ.nodeCount : Typ → Nat
  | .unit        => 1
  | .field       => 1
  | .mvar _      => 1
  | .ref _       => 1
  | .pointer t   => 1 + Typ.nodeCount t
  | .array t _   => 1 + Typ.nodeCount t
  | .tuple ts    => 1 + ts.attach.foldl (init := 0) fun acc ⟨t, _⟩ => acc + Typ.nodeCount t
  | .function ins out =>
      1 + Typ.nodeCount out + ins.foldl (fun acc t => acc + Typ.nodeCount t) 0
  | .app _ args  => 1 + args.attach.foldl (init := 0) fun acc ⟨t, _⟩ => acc + Typ.nodeCount t
termination_by t => sizeOf t
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
    | grind

/-- Outer interface. Uses `nextMVar + Typ.nodeCount t1 + Typ.nodeCount t2 + 1`
as a bound, which is guaranteed large enough for any well-formed pair of
types under any valid mvar substitution. -/
def unifyTyp (t1 t2 : Typ) : CheckM Bool := do
  let s ← get
  unifyTypBound (s.nextMVar + t1.nodeCount + t2.nodeCount + 1) t1 t2

/-- Bounded zonk. Follows mvar chains via the `bound`/`visited` pattern, and
structurally recurses through `Typ`. -/
def zonkTypBound : Nat → Std.HashSet Nat → Typ → CheckM Typ
  | bound, visited, .mvar id => do
    if visited.contains id then pure (.mvar id)
    else match bound with
      | 0 => pure (.mvar id)
      | bound+1 =>
        match (← get).mvarSubst[id]? with
        | some t => zonkTypBound bound (visited.insert id) t
        | none   => pure (.mvar id)
  | bound, visited, .tuple ts => do
    pure $ .tuple (← ts.attach.mapM fun ⟨t, _⟩ => zonkTypBound bound visited t)
  | bound, visited, .array t n => do
    pure $ .array (← zonkTypBound bound visited t) n
  | bound, visited, .pointer t => do
    pure $ .pointer (← zonkTypBound bound visited t)
  | bound, visited, .function ins out => do
    pure $ .function (← ins.attach.mapM fun ⟨t, _⟩ => zonkTypBound bound visited t)
                     (← zonkTypBound bound visited out)
  | bound, visited, .app g args => do
    pure $ .app g (← args.attach.mapM fun ⟨t, _⟩ => zonkTypBound bound visited t)
  | _, _, t => pure t
termination_by bound _ t => (bound, sizeOf t)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right
       first
         | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; simp +arith; omega)
         | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp +arith; omega)
         | (simp +arith; omega)
         | grind)

/-- Outer interface. Uses `nextMVar + 1` as a safe bound on the mvar chain
length. -/
def zonkTyp (t : Typ) : CheckM Typ := do
  let s ← get
  zonkTypBound (s.nextMVar + 1) {} t

def instantiateParams (params : List String) : CheckM (Array Typ × (Global → Option Typ)) := do
  let mvars ← (params.toArray.mapM fun _ => freshMVar)
  pure (mvars, mkParamSubst params mvars)

/-! ## Type inference — produces Typed.Term -/

def refLookup (global : Global) : CheckM (Typ × Array Typ) := do
  let ctx ← read
  match ctx.decls.getByKey global with
  | some (.function function) =>
    if function.params.isEmpty then
      pure (.function (function.inputs.map Prod.snd) function.output, #[])
    else
      let (mvars, subst) ← instantiateParams function.params
      let inputs := function.inputs.map (Typ.instantiate subst ∘ Prod.snd)
      let output := Typ.instantiate subst function.output
      pure (.function inputs output, mvars)
  | some (.constructor dataType constructor) =>
    let args := constructor.argTypes
    unless args.isEmpty do (throw $ .wrongNumArgs global args.length 0)
    if dataType.params.isEmpty then
      pure (.ref dataType.name, #[])
    else
      let (mvars, _) ← instantiateParams dataType.params
      pure (.app dataType.name mvars, mvars)
  | some _ => throw $ .notAValue global
  | none => throw $ .unboundGlobal global

def bindIdents (bindings : List (Local × Typ)) (ctx : CheckContext) : CheckContext :=
  { ctx with varTypes := ctx.varTypes.insertMany bindings }

/-- Convenience: wrap an `Aiur.Typ`-typed `Term` constructor for the unop family. -/
abbrev TypedUnop := Typ → Bool → Typed.Term → Typed.Term
abbrev TypedBinop := Typ → Bool → Typed.Term → Typed.Term → Typed.Term

/-! ## Pattern checker

`checkPatternAux` / `checkPattern` are total and live outside the inferTerm
mutual block — they never call into it, only the other direction. -/

mutual

/-- Pattern-recursive worker for `checkPattern`. Recursion is delegated to
`checkPatternsArr` / `checkPatternsList` / `checkPatternsArrUniform` so the
termination of each arm is visible structurally: the helpers recurse on
sub-`Array`/`List` of the matched constructor. -/
def checkPatternAux (pat : Pattern) (typ : Typ) : CheckM (List (Local × Typ)) := do
  let typ ← walkTyp typ
  match pat with
  | .var var => pure [(var, typ)]
  | .wildcard => pure []
  | .field _ =>
    match typ with
    | .field => pure []
    | _ => throw $ .incompatiblePattern pat typ
  | .tuple pats =>
    match typ with
    | .tuple typs => do
      unless pats.size == typs.size do throw $ .incompatiblePattern pat typ
      checkPatternsArr pats typs
    | _ => throw $ .incompatiblePattern pat typ
  | .array pats =>
    match typ with
    | .array innerTyp n => do
      unless pats.size == n do throw $ .incompatiblePattern pat typ
      checkPatternsArrUniform pats innerTyp
    | _ => throw $ .incompatiblePattern pat typ
  | .ref refName pats =>
    match typ with
    | tFn@(.function ..) =>
      if pats.isEmpty then do
        let ctx ← read
        let some (.function function) := ctx.decls.getByKey refName
          | throw $ .incompatiblePattern pat typ
        let typ' := .function (function.inputs.map Prod.snd) function.output
        unless ← unifyTyp tFn typ' do throw $ .typeMismatch tFn typ'
        pure []
      else throw $ .incompatiblePattern pat typ
    | .ref dataTypeRef => do
      let ctx ← read
      let some (.dataType dataType) := ctx.decls.getByKey dataTypeRef
        | throw $ .unboundGlobal dataTypeRef
      let some (.constructor dataType' constr) := ctx.decls.getByKey refName
        | throw $ .notAConstructor refName
      unless dataType == dataType' do throw $ .incompatiblePattern pat typ
      let typs := constr.argTypes
      unless pats.length == typs.length do throw $ .wrongNumArgs refName pats.length typs.length
      checkPatternsList pats typs
    | .app dataTypeRef args => do
      let ctx ← read
      let some (.dataType dataType) := ctx.decls.getByKey dataTypeRef
        | throw $ .unboundGlobal dataTypeRef
      let some (.constructor dataType' constr) := ctx.decls.getByKey refName
        | throw $ .notAConstructor refName
      unless dataType == dataType' do throw $ .incompatiblePattern pat typ
      let subst := mkParamSubst dataType.params args
      let typs := constr.argTypes.map (Typ.instantiate subst)
      unless pats.length == typs.length do throw $ .wrongNumArgs refName pats.length typs.length
      checkPatternsList pats typs
    | _ => throw $ .incompatiblePattern pat typ
  | .or p1 p2 => do
    let bind ← checkPatternAux p1 typ
    let bind' ← checkPatternAux p2 typ
    if bind != bind' then throw $ .differentBindings bind bind' else pure bind
  | .pointer p =>
    match typ with
    | .pointer innerTyp => checkPatternAux p innerTyp
    | _ => throw $ .incompatiblePattern pat typ
termination_by (sizeOf pat, 0)

/-- Pair-up `pats` and `typs` (both `Array`) and run `checkPatternAux` on each,
concatenating bindings. The per-element recursion decreases on `sizeOf pats`. -/
def checkPatternsArr (pats : Array Pattern) (typs : Array Typ) :
    CheckM (List (Local × Typ)) :=
  pats.attach.zip typs |>.foldlM (init := []) fun acc (⟨pat, hmem⟩, typ) => do
    have : sizeOf pat < sizeOf pats := Array.sizeOf_lt_of_mem hmem
    let sub ← checkPatternAux pat typ
    pure (acc.append sub)
termination_by (sizeOf pats, 1)
decreasing_by all_goals first | decreasing_tactic | omega

/-- Like `checkPatternsArr`, but every pattern is matched against the same
element type `innerTyp` (used for `.array` patterns). -/
def checkPatternsArrUniform (pats : Array Pattern) (innerTyp : Typ) :
    CheckM (List (Local × Typ)) :=
  pats.attach.foldlM (init := []) fun acc ⟨pat, hmem⟩ => do
    have : sizeOf pat < sizeOf pats := Array.sizeOf_lt_of_mem hmem
    let sub ← checkPatternAux pat innerTyp
    pure (acc.append sub)
termination_by (sizeOf pats, 1)
decreasing_by all_goals first | decreasing_tactic | omega

/-- List version of `checkPatternsArr`. -/
def checkPatternsList (pats : List Pattern) (typs : List Typ) :
    CheckM (List (Local × Typ)) :=
  pats.attach.zip typs |>.foldlM (init := []) fun acc (⟨pat, hmem⟩, typ) => do
    have : sizeOf pat < sizeOf pats := List.sizeOf_lt_of_mem hmem
    let sub ← checkPatternAux pat typ
    pure (acc.append sub)
termination_by (sizeOf pats, 1)
decreasing_by all_goals first | decreasing_tactic | omega

end

def checkPattern (pat : Pattern) (typ : Typ) : CheckM (List (Local × Typ)) := do
  let binds ← checkPatternAux pat typ
  let locals := binds.map Prod.fst
  unless (locals == locals.eraseDups) do throw $ .duplicatedBind pat
  pure binds

/-! ## Type inference

All the old helper functions (`inferAssertEq`, `inferLet`, `inferProj`,
`inferApplication` and its chain, etc.) have been inlined into `inferTerm`'s
big match. The only surviving mutual-block members are:
- `inferTerm` — the dispatcher, recurses structurally on sub-`Term`s.
- `checkNoEscape` / `inferNoEscape` — wrap `inferTerm` on the same `Term`.
- `checkArgsAndInputs` — one-level helper for `.app`; recurses via
  `checkNoEscape` on each arg, which is a `∈` subterm of the caller.
- `checkMatchBranch` — one-level helper for `.match`; recurses via
  `inferTerm` on the branch body, a subterm of the `branchData` pair.

Lex measure `(sizeOf input, prio)`:
- `inferTerm` at prio 0 (callees go "upward" via `Lex.right`)
- the rest at prio 1
This works because every `inferTerm → X` call decreases `sizeOf` strictly
(sub-`Term` of `t`), and every `X → inferTerm` call either stays same
size with priority decrease (`checkNoEscape`, `inferNoEscape`) or decreases
size strictly (`checkMatchBranch`, `checkArgsAndInputs` via member args). -/

mutual

def inferTerm (t : Term) : CheckM Typed.Term := match t with
  | .unit => pure (.unit .unit false)
  | .var x => do
    let ctx ← read
    match (ctx.varTypes[x]?, x) with
    | (some t, _) => pure (.var t false x)
    | (none, Local.str localName) =>
      let (typ, _) ← refLookup (Global.init localName)
      pure (.var typ false x)
    | (none, _) => throw $ .unboundLocal x
  | .ref x => do
    let (typ, tArgs) ← refLookup x
    pure (.ref typ false x tArgs)
  | .ret term => do
    let ctx ← read
    let term' ← checkNoEscape term ctx.returnType
    pure (Typed.Term.ret ctx.returnType true term')
  | .field g => pure (.field .field false g)
  | .tuple ts => do
    let typedTerms ← ts.attach.mapM fun ⟨t, _⟩ => inferNoEscape t
    let typs := typedTerms.map (·.typ)
    pure (Typed.Term.tuple (.tuple typs) false typedTerms)
  | .array ts => do
    if h : ts.size > 0 then
      let first ← inferNoEscape ts[0]
      -- Check every element against first.typ (re-checks ts[0] trivially).
      let typedTerms ← ts.attach.mapM fun ⟨t, _⟩ => checkNoEscape t first.typ
      pure (Typed.Term.array (.array first.typ ts.size) false typedTerms)
    else throw .emptyArray
  | .let pat expr body => do
    let expr' ← inferNoEscape expr
    let bindings ← checkPattern pat expr'.typ
    let body' ← withReader (bindIdents bindings) (inferTerm body)
    pure (Typed.Term.let body'.typ body'.escapes pat expr' body')
  | .match term branches => do
    let term' ← inferNoEscape term
    let init := ([], none)
    let (branches', typOpt) ← branches.attach.foldrM (init := init)
      (fun ⟨branchData, _⟩ acc => checkMatchBranch term'.typ branchData acc)
    match typOpt with
    | some (typ, escapes) => pure (Typed.Term.match typ escapes term' branches')
    | none => throw .emptyMatch
  | .app func args u => do
    let ctx ← read
    -- Local function lookup (only for unqualified names); returns
    -- `some (.ok …)` on hit, `some (.error …)` on wrong-type local, `none` to
    -- fall through to global lookup.
    let localLookup : Option (Except CheckError (Typ × List Typ)) :=
      match func.toName with
      | .str .anonymous s =>
        match ctx.varTypes[Local.str s]? with
        | some (.function ins out) => some (.ok (out, ins))
        | some _                   => some (.error (.notAFunction func))
        | none                     => none
      | _ => none
    match localLookup with
    | some (.error e) => throw e
    | some (.ok (output, inputs)) =>
      let args' ← checkArgsAndInputs func args inputs
      pure (Typed.Term.app output false func #[] args' u)
    | none =>
      match ctx.decls.getByKey func with
      | some (.function function) =>
        if function.params.isEmpty then
          let args' ← checkArgsAndInputs func args (function.inputs.map Prod.snd)
          pure (Typed.Term.app function.output false func #[] args' u)
        else
          let (mvars, subst) ← instantiateParams function.params
          let inputTypes := function.inputs.map (Typ.instantiate subst ∘ Prod.snd)
          let output := Typ.instantiate subst function.output
          let args' ← checkArgsAndInputs func args inputTypes
          pure (Typed.Term.app output false func mvars args' u)
      | some (.constructor dataType constr) =>
        if u then throw $ .unconstrainedConstructor func
        if dataType.params.isEmpty then
          let args' ← checkArgsAndInputs func args constr.argTypes
          pure (Typed.Term.app (.ref dataType.name) false func #[] args' u)
        else
          let (mvars, subst) ← instantiateParams dataType.params
          let argTypes := constr.argTypes.map (Typ.instantiate subst)
          let args' ← checkArgsAndInputs func args argTypes
          pure (Typed.Term.app (.app dataType.name mvars) false func mvars args' u)
      | _ => throw $ .cannotApply func
  | .ann typ term => checkNoEscape term typ
  | .proj tup i => do
    let tup' ← inferNoEscape tup
    match ← walkTyp tup'.typ with
    | .tuple typs =>
      if h : i < typs.size then
        pure (Typed.Term.proj typs[i] false tup' i)
      else throw $ .indexOoB i
    | typ' => throw $ .notATuple typ'
  | .get arr i => do
    let arr' ← inferNoEscape arr
    match ← walkTyp arr'.typ with
    | .array typ n =>
      if i ≥ n then throw $ .indexOoB i
      else pure (Typed.Term.get typ false arr' i)
    | typ' => throw $ .notAnArray typ'
  | .slice arr i j =>
    if j < i then throw $ .negativeRange i j else do
      let arr' ← inferNoEscape arr
      match ← walkTyp arr'.typ with
      | .array typ n =>
        if j ≤ n then
          pure (Typed.Term.slice (.array typ (j - i)) false arr' i j)
        else throw $ .rangeOoB i j
      | typ' => throw $ .notAnArray typ'
  | .set arr i val => do
    let arr' ← inferNoEscape arr
    match ← walkTyp arr'.typ with
    | .array typ n =>
      if i ≥ n then throw $ .indexOoB i
      else
        let val' ← checkNoEscape val typ
        pure (Typed.Term.set (.array typ n) false arr' i val')
    | typ' => throw $ .notAnArray typ'
  | .store term => do
    let term' ← inferNoEscape term
    pure (Typed.Term.store (.pointer term'.typ) false term')
  | .load term => do
    let term' ← inferNoEscape term
    match ← walkTyp term'.typ with
    | .pointer innerTyp => pure (Typed.Term.load innerTyp false term')
    | typ' => throw $ .notAPointer typ'
  | .ptrVal term => do
    let term' ← inferNoEscape term
    match ← walkTyp term'.typ with
    | .pointer _ => pure (Typed.Term.ptrVal .field false term')
    | typ' => throw $ .notAPointer typ'
  | .eqZero a => do
    let a' ← checkNoEscape a .field
    pure (Typed.Term.eqZero .field false a')
  | .add a b => do
    let a' ← checkNoEscape a .field
    let b' ← checkNoEscape b .field
    pure (Typed.Term.add .field false a' b')
  | .sub a b => do
    let a' ← checkNoEscape a .field
    let b' ← checkNoEscape b .field
    pure (Typed.Term.sub .field false a' b')
  | .mul a b => do
    let a' ← checkNoEscape a .field
    let b' ← checkNoEscape b .field
    pure (Typed.Term.mul .field false a' b')
  | .u8ShiftLeft a => do
    let a' ← checkNoEscape a .field
    pure (Typed.Term.u8ShiftLeft .field false a')
  | .u8ShiftRight a => do
    let a' ← checkNoEscape a .field
    pure (Typed.Term.u8ShiftRight .field false a')
  | .u8BitDecomposition a => do
    let a' ← checkNoEscape a .field
    pure (Typed.Term.u8BitDecomposition (.array .field 8) false a')
  | .u8Xor a b => do
    let a' ← checkNoEscape a .field
    let b' ← checkNoEscape b .field
    pure (Typed.Term.u8Xor .field false a' b')
  | .u8And a b => do
    let a' ← checkNoEscape a .field
    let b' ← checkNoEscape b .field
    pure (Typed.Term.u8And .field false a' b')
  | .u8Or a b => do
    let a' ← checkNoEscape a .field
    let b' ← checkNoEscape b .field
    pure (Typed.Term.u8Or .field false a' b')
  | .u8Add a b => do
    let a' ← checkNoEscape a .field
    let b' ← checkNoEscape b .field
    pure (Typed.Term.u8Add (.tuple #[.field, .field]) false a' b')
  | .u8Sub a b => do
    let a' ← checkNoEscape a .field
    let b' ← checkNoEscape b .field
    pure (Typed.Term.u8Sub (.tuple #[.field, .field]) false a' b')
  | .u8LessThan a b => do
    let a' ← checkNoEscape a .field
    let b' ← checkNoEscape b .field
    pure (Typed.Term.u8LessThan .field false a' b')
  | .u32LessThan a b => do
    let a' ← checkNoEscape a .field
    let b' ← checkNoEscape b .field
    pure (Typed.Term.u32LessThan .field false a' b')
  | .ioGetInfo key => do
    let key' ← inferNoEscape key
    match ← walkTyp key'.typ with
    | .array .. =>
      pure (Typed.Term.ioGetInfo (.tuple #[.field, .field]) false key')
    | typ' => throw $ .notAnArray typ'
  | .ioSetInfo key idx len ret => do
    let key' ← inferNoEscape key
    match ← walkTyp key'.typ with
    | .array keyEltTyp _ =>
      unless ← unifyTyp keyEltTyp .field do throw $ .typeMismatch .field keyEltTyp
      let idx' ← checkNoEscape idx .field
      let len' ← checkNoEscape len .field
      let ret' ← inferTerm ret
      pure (Typed.Term.ioSetInfo ret'.typ ret'.escapes key' idx' len' ret')
    | typ' => throw $ .notAnArray typ'
  | .ioRead idx len => do
    if len = 0 then throw .emptyArray
    let idx' ← checkNoEscape idx .field
    pure (Typed.Term.ioRead (.array .field len) false idx' len)
  | .ioWrite data ret => do
    let data' ← inferNoEscape data
    match ← walkTyp data'.typ with
    | .array dataEltTyp _ =>
      unless ← unifyTyp dataEltTyp .field do throw $ .typeMismatch .field dataEltTyp
      let ret' ← inferTerm ret
      pure (Typed.Term.ioWrite ret'.typ ret'.escapes data' ret')
    | typ' => throw $ .notAnArray typ'
  | .assertEq a b ret => do
    let a' ← inferNoEscape a
    let b' ← checkNoEscape b a'.typ
    let ret' ← inferTerm ret
    pure (Typed.Term.assertEq ret'.typ ret'.escapes a' b' ret')
  | .debug label term ret => do
    let term' ← match term with
      | none => pure none
      | some sub => do pure (some (← inferTerm sub))
    let ret' ← inferTerm ret
    pure (Typed.Term.debug ret'.typ ret'.escapes label term' ret')
termination_by (sizeOf t, 0)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
    | (cases term <;> simp_all +arith)
    | grind

def checkNoEscape (term : Term) (typ : Typ) : CheckM Typed.Term := do
  let typedTerm ← inferTerm term
  if typedTerm.escapes then throw .illegalReturn
  unless ← unifyTyp typ typedTerm.typ do throw $ .typeMismatch typ typedTerm.typ
  pure typedTerm
termination_by (sizeOf term, 1)

def inferNoEscape (term : Term) : CheckM Typed.Term := do
  let typedTerm ← inferTerm term
  if typedTerm.escapes then throw .illegalReturn
  pure typedTerm
termination_by (sizeOf term, 1)

/-- Arg/input checker extracted from the `.app` arm. Recurses into
`checkNoEscape` once per arg; each `arg ∈ args` so `sizeOf arg < sizeOf args`.
Sharing `args` with the caller is fine because `sizeOf args < sizeOf (.app ...)`
at the inferTerm call site. -/
def checkArgsAndInputs (func : Global) (args : List Term) (inputs : List Typ) :
    CheckM (List Typed.Term) := do
  let lenArgs := args.length
  let lenInputs := inputs.length
  unless lenArgs == lenInputs do throw $ .wrongNumArgs func lenArgs lenInputs
  args.attach.zip inputs |>.mapM (fun (⟨arg, _⟩, input) => checkNoEscape arg input)
termination_by (sizeOf args, 1)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
    | grind

/-- Branch checker for one match arm. Recurses into `inferTerm` on the branch
body, which is `branchData.snd` — a sub-sizeOf of `branchData`. -/
def checkMatchBranch
    (patTyp : Typ) (branchData : Pattern × Term)
    (acc : List (Pattern × Typed.Term) × Option (Typ × Bool)) :
    CheckM (List (Pattern × Typed.Term) × Option (Typ × Bool)) := do
  let (pat, branch) := branchData
  let (typedBranches, currentTypOpt) := acc
  let bindings ← checkPattern pat patTyp
  withReader (bindIdents bindings) (match currentTypOpt with
    | none => do
      let typedBranch ← inferTerm branch
      pure (typedBranches.cons (pat, typedBranch), some (typedBranch.typ, typedBranch.escapes))
    | some (matchTyp, matchEscapes) => do
      let typedBranch ← inferTerm branch
      let typedBranches := typedBranches.cons (pat, typedBranch)
      if typedBranch.escapes then
        pure (typedBranches, currentTypOpt)
      else if matchEscapes then
        pure (typedBranches, some (typedBranch.typ, false))
      else
        unless ← unifyTyp matchTyp typedBranch.typ do
          throw $ .branchMismatch matchTyp typedBranch.typ
        pure (typedBranches, currentTypOpt))
termination_by (sizeOf branchData, 1)

end

/-! ## Zonking — applies the mvar substitution through every typed sub-term. -/

def zonkTypedTerm (t : Typed.Term) : CheckM Typed.Term := match t with
  | .unit τ e => do pure (.unit (← zonkTyp τ) e)
  | .var τ e l => do pure (.var (← zonkTyp τ) e l)
  | .ref τ e g tArgs => do pure (.ref (← zonkTyp τ) e g (← tArgs.mapM zonkTyp))
  | .field τ e g => do pure (.field (← zonkTyp τ) e g)
  | .tuple τ e ts => do
      pure (.tuple (← zonkTyp τ) e (← ts.attach.mapM fun ⟨t, _⟩ => zonkTypedTerm t))
  | .array τ e ts => do
      pure (.array (← zonkTyp τ) e (← ts.attach.mapM fun ⟨t, _⟩ => zonkTypedTerm t))
  | .ret τ e sub => do pure (.ret (← zonkTyp τ) e (← zonkTypedTerm sub))
  | .let τ e pat v b => do
      pure (.let (← zonkTyp τ) e pat (← zonkTypedTerm v) (← zonkTypedTerm b))
  | .match τ e scrut bs => do
      let scrut' ← zonkTypedTerm scrut
      let bs' ← bs.attach.mapM fun ⟨(p, b), _⟩ => do return (p, ← zonkTypedTerm b)
      pure (.match (← zonkTyp τ) e scrut' bs')
  | .app τ e g tArgs args u => do
      pure (.app (← zonkTyp τ) e g (← tArgs.mapM zonkTyp)
            (← args.attach.mapM fun ⟨a, _⟩ => zonkTypedTerm a) u)
  | .add τ e a b => do pure (.add (← zonkTyp τ) e (← zonkTypedTerm a) (← zonkTypedTerm b))
  | .sub τ e a b => do pure (.sub (← zonkTyp τ) e (← zonkTypedTerm a) (← zonkTypedTerm b))
  | .mul τ e a b => do pure (.mul (← zonkTyp τ) e (← zonkTypedTerm a) (← zonkTypedTerm b))
  | .eqZero τ e a => do pure (.eqZero (← zonkTyp τ) e (← zonkTypedTerm a))
  | .proj τ e a n => do pure (.proj (← zonkTyp τ) e (← zonkTypedTerm a) n)
  | .get τ e a n => do pure (.get (← zonkTyp τ) e (← zonkTypedTerm a) n)
  | .slice τ e a i j => do pure (.slice (← zonkTyp τ) e (← zonkTypedTerm a) i j)
  | .set τ e a n v => do
      pure (.set (← zonkTyp τ) e (← zonkTypedTerm a) n (← zonkTypedTerm v))
  | .store τ e a => do pure (.store (← zonkTyp τ) e (← zonkTypedTerm a))
  | .load τ e a => do pure (.load (← zonkTyp τ) e (← zonkTypedTerm a))
  | .ptrVal τ e a => do pure (.ptrVal (← zonkTyp τ) e (← zonkTypedTerm a))
  | .assertEq τ e a b r => do
      pure (.assertEq (← zonkTyp τ) e (← zonkTypedTerm a) (← zonkTypedTerm b) (← zonkTypedTerm r))
  | .ioGetInfo τ e k => do pure (.ioGetInfo (← zonkTyp τ) e (← zonkTypedTerm k))
  | .ioSetInfo τ e k i l r => do
      pure (.ioSetInfo (← zonkTyp τ) e (← zonkTypedTerm k) (← zonkTypedTerm i)
                       (← zonkTypedTerm l) (← zonkTypedTerm r))
  | .ioRead τ e i n => do pure (.ioRead (← zonkTyp τ) e (← zonkTypedTerm i) n)
  | .ioWrite τ e d r => do pure (.ioWrite (← zonkTyp τ) e (← zonkTypedTerm d) (← zonkTypedTerm r))
  | .u8BitDecomposition τ e a => do
      pure (.u8BitDecomposition (← zonkTyp τ) e (← zonkTypedTerm a))
  | .u8ShiftLeft τ e a => do pure (.u8ShiftLeft (← zonkTyp τ) e (← zonkTypedTerm a))
  | .u8ShiftRight τ e a => do pure (.u8ShiftRight (← zonkTyp τ) e (← zonkTypedTerm a))
  | .u8Xor τ e a b => do pure (.u8Xor (← zonkTyp τ) e (← zonkTypedTerm a) (← zonkTypedTerm b))
  | .u8Add τ e a b => do pure (.u8Add (← zonkTyp τ) e (← zonkTypedTerm a) (← zonkTypedTerm b))
  | .u8Sub τ e a b => do pure (.u8Sub (← zonkTyp τ) e (← zonkTypedTerm a) (← zonkTypedTerm b))
  | .u8And τ e a b => do pure (.u8And (← zonkTyp τ) e (← zonkTypedTerm a) (← zonkTypedTerm b))
  | .u8Or τ e a b => do pure (.u8Or (← zonkTyp τ) e (← zonkTypedTerm a) (← zonkTypedTerm b))
  | .u8LessThan τ e a b => do
      pure (.u8LessThan (← zonkTyp τ) e (← zonkTypedTerm a) (← zonkTypedTerm b))
  | .u32LessThan τ e a b => do
      pure (.u32LessThan (← zonkTyp τ) e (← zonkTypedTerm a) (← zonkTypedTerm b))
  | .debug τ e label t r => do
      let t' ← match t with
        | none => pure none
        | some sub => do pure (some (← zonkTypedTerm sub))
      pure (.debug (← zonkTyp τ) e label t' (← zonkTypedTerm r))
termination_by sizeOf t
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
    | grind

def getFunctionContext (function : Function) (decls : Decls) : CheckContext :=
  { decls
    varTypes := .ofList function.inputs
    returnType := function.output
    typeParams := function.params }

def wellFormedDecls (decls : Decls) : Except CheckError Unit := do
  let mut visited := default
  for (_, decl) in decls.pairs do
    match EStateM.run (wellFormedDecl decl) visited with
    | .error e _ => throw e
    | .ok () visited' => visited := visited'
where
  checkUniqueParams (name : Global) (params : List String) :
      EStateM CheckError (Std.HashSet Global) Unit :=
    let rec go : List String → Std.HashSet String → EStateM CheckError (Std.HashSet Global) Unit
      | [], _ => pure ()
      | p :: ps, seen =>
        if seen.contains p then throw $ .duplicatedTypeParam name p
        else go ps (seen.insert p)
    go params {}
  wellFormedDecl : Declaration → EStateM CheckError (Std.HashSet Global) Unit
    | .dataType dataType => do
      let map ← get
      if !map.contains dataType.name then
        set $ map.insert dataType.name
        checkUniqueParams dataType.name dataType.params
        dataType.constructors.flatMap (·.argTypes) |>.forM (wellFormedType dataType.params)
    | .function function => do
      checkUniqueParams function.name function.params
      wellFormedType function.params function.output
      function.inputs.forM fun (_, typ) => wellFormedType function.params typ
    | .constructor .. => pure ()
  wellFormedType (params : List String) : Typ → EStateM CheckError (Std.HashSet Global) Unit
    | .tuple typs =>
        typs.attach.forM (fun ⟨t, _⟩ => wellFormedType params t)
    | .pointer pointerTyp => wellFormedType params pointerTyp
    | .array t _ => wellFormedType params t
    | .ref ref =>
      if params.any (· == ref.toName.toString) then pure ()
      else match decls.getByKey ref with
      | some (.dataType dt) =>
        unless dt.params.isEmpty do throw $ .wrongNumTypeArgs ref 0 dt.params.length
      | some _ => throw $ .notADataType ref
      | none => throw $ .unboundGlobal ref
    | .app g args => match decls.getByKey g with
      | some (.dataType dt) => do
        unless args.size == dt.params.length do
          throw $ .wrongNumTypeArgs g args.size dt.params.length
        args.attach.forM (fun ⟨t, _⟩ => wellFormedType params t)
      | some _ => throw $ .notADataType g
      | none => throw $ .unboundGlobal g
    | _ => pure ()
  termination_by t => sizeOf t

/-- Check a function (infer + zonk). -/
def checkFunction (function : Function) : CheckM Typed.Function := do
  let body ← inferTerm function.body
  unless body.escapes do
    unless ← unifyTyp body.typ function.output do
      throw $ .typeMismatch body.typ function.output
  let body ← zonkTypedTerm body
  pure ⟨function.name, function.params, function.inputs, function.output, body, function.entry⟩

end Aiur

end -- @[expose] section
end
