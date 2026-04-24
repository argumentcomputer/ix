module
public import Ix.Aiur.Proofs.Lib
public import Ix.Aiur.Compiler.Simple
public import Ix.Aiur.Stages.Concrete

/-!
Monomorphization: `Typed.Decls` (after simplify) → `Concrete.Decls`.

The static check rejecting polymorphic recursion is enforced by bounding the
worklist: every new (template, type-args) pair must be
structurally simpler than the pair that triggered it, where "simpler" is
measured on the DAG of type-argument references. A violation throws
`.polymorphicRecursion`.
-/

public section
@[expose] section

namespace Aiur

open Source

/-- Errors surfacing during monomorphization. Separate enum from `CheckError`. -/
inductive ConcretizeError
  | unresolvedMVar : Nat → ConcretizeError
  | templateNotFound : Global → ConcretizeError
  | wrongNumArgs : Global → Nat → Nat → ConcretizeError
  | polymorphicRecursion : Global → Array Typ → ConcretizeError
  | fuelExhausted : ConcretizeError
  /-- Pattern shape not supported by the direct `Source → Concrete` path.
  Nested patterns (like `.tuple [.ref _ [...], ...]`), `.or`, and `.pointer`
  currently require running the match compiler; today only single-level
  patterns where every sub-pattern is `.var` or `.wildcard` are translated
  directly. -/
  | unsupportedPattern : ConcretizeError
  /-- A `.match` whose scrutinee isn't already a `.var` needs a fresh local
  to bind it, which requires state threading not yet wired here. -/
  | unsupportedMatchScrutinee : ConcretizeError
  deriving Repr

instance : ToString ConcretizeError where
  toString e := repr e |>.pretty

/-! ## Type flattening to `Concrete.Typ` -/


/-- Convert a `Typ` (from the source IR) into a `Concrete.Typ` using a mono map
that knows the concrete name for each `(template, args)` pair. -/
def typToConcrete (mono : Std.HashMap (Global × Array Typ) Global) :
    Typ → Except ConcretizeError Concrete.Typ
  | .unit => pure .unit
  | .field => pure .field
  | .tuple ts => do
      pure (.tuple (← ts.attach.mapM fun ⟨t, _⟩ => typToConcrete mono t))
  | .array t n => do pure (.array (← typToConcrete mono t) n)
  | .pointer t => do pure (.pointer (← typToConcrete mono t))
  | .function ins out => do
    let ins' ← ins.attach.mapM fun ⟨t, _⟩ => typToConcrete mono t
    let out' ← typToConcrete mono out
    pure (.function ins' out')
  | .ref g => pure (.ref g)
  | .app g args => do
    match mono[(g, args)]? with
    | some concName => pure (.ref concName)
    | none => pure (.ref g)
  | .mvar n => .error (.unresolvedMVar n)
termination_by t => sizeOf t

-- `List.mapM_except_ok` moved to `Proofs/ConcretizeProgress.lean`.


-- `Typed.Term.MvarFree`, `Pattern.Simple`, `Typed.Term.ConcretizeReady`
-- moved to `Proofs/ConcretizeProgress.lean`.


/-! ## Name mangling. -/

def Typ.toFlatName : Typ → String
  | .field => "G"
  | .unit => "Unit"
  | Typ.ref g => g.toName.toString (escape := false)
  | .pointer t => "Ptr_" ++ t.toFlatName
  | .tuple ts => "Tup_" ++ "_".intercalate
      (ts.attach.map fun ⟨t, _⟩ => Typ.toFlatName t).toList
  | .array t n => t.toFlatName ++ "_" ++ toString n
  | .function .. => "Fn"
  | .app name args =>
      name.toName.toString (escape := false) ++ "_" ++
        "_".intercalate (args.attach.map fun ⟨t, _⟩ => Typ.toFlatName t).toList
  | .mvar id => s!"?{id}"
termination_by t => sizeOf t
decreasing_by all_goals first | decreasing_tactic | grind

@[expose, reducible] def Typ.appendNameLimbs (g : Global) : Typ → Global
  | .field => g.pushNamespace "G"
  | .unit => g.pushNamespace "Unit"
  | Typ.ref g' =>
    let rec pushAll (g : Global) : Lean.Name → Global
      | .str parent s => (pushAll g parent).pushNamespace s
      | _ => g
    pushAll g g'.toName
  | .pointer t => Typ.appendNameLimbs (g.pushNamespace "Ptr") t
  | .tuple ts =>
      ts.attach.foldl (init := g.pushNamespace "Tup")
        (fun acc ⟨t, _⟩ => Typ.appendNameLimbs acc t)
  | .array t n => g.pushNamespace (toFlatName t ++ "_" ++ toString n)
  | .function .. => g.pushNamespace "Fn"
  | .app name args =>
      args.attach.foldl (init := Typ.appendNameLimbs g (.ref name))
        (fun acc ⟨t, _⟩ => Typ.appendNameLimbs acc t)
  | .mvar id => g.pushNamespace s!"?{id}"
termination_by t => sizeOf t
decreasing_by
  all_goals first
    | decreasing_tactic
    | (-- For .app→.ref cross-call: need sizeOf (.ref name) < sizeOf (.app name args).
       -- sizeOf (.ref name) = 1 + sizeOf name, sizeOf (.app name args) =
       -- 1 + sizeOf name + sizeOf args, so we need sizeOf args > 0.
       have := Array.two_le_sizeOf ‹Array Typ›; grind)

@[expose] def concretizeName (templateName : Global) (args : Array Typ) : Global :=
  args.foldl Typ.appendNameLimbs templateName

/-! ## Source → Concrete pattern translation — direct, non-nested subset only.

A full match compiler lives in `Compiler/Match.lean` (produces `Simple.Term`
decision trees). The Aiur pipeline doesn't yet wire that through, so here we
handle only the patterns that map 1:1 to `Concrete.Pattern`:
- `.wildcard` / `.var x` at top level → `Concrete.Pattern.wildcard` (a
  top-level `.var x` additionally requires binding `x` to the scrutinee,
  which the caller handles by prepending a `.letVar`)
- `.field g` → `Concrete.Pattern.field g`
- `.ref g [var_1, ..., var_n]` → `Concrete.Pattern.ref g #[var_1, ..., var_n]`
- `.tuple [var_1, ..., var_n]` → `Concrete.Pattern.tuple #[var_1, ..., var_n]`
- `.array [var_1, ..., var_n]` → `Concrete.Pattern.array #[var_1, ..., var_n]`

Everything else throws `.unsupportedPattern`. -/

/-- Base tag for wildcard `.idx` locals introduced when translating a
sub-pattern. Chosen large enough to avoid colliding with any `.idx` used
elsewhere in the pipeline (`Simple.tmpVar = .idx 0`, the match compiler
allocates `.idx id` with `id` starting at 0 too — so we reserve a
dedicated high range here). -/
def concretizeWildcardBase : Nat := 1 <<< 20

/-- Extract a list of `Local`s from a list of sub-patterns, demanding each is
`.var x` or `.wildcard`. Wildcards are turned into a fresh-named local of
the form `.idx (concretizeWildcardBase + offset)` — this doesn't collide
with user names (which are `.str _`) or with the other reserved `.idx`
slots used elsewhere. -/
def subPatternsToLocals (pats : List Pattern) :
    Except ConcretizeError (Array Local) := do
  let (locals, _) ← pats.foldlM (init := (#[], concretizeWildcardBase))
    fun (acc, tag) p => do
      match p with
      | .var x => pure (acc.push x, tag)
      | .wildcard => pure (acc.push (.idx tag), tag + 1)
      | _ => throw .unsupportedPattern
  pure locals

def subPatternsToLocalsArr (pats : Array Pattern) :
    Except ConcretizeError (Array Local) :=
  subPatternsToLocals pats.toList

/-- Expand a match-branch pattern into one or more `Concrete.Pattern` cases.

Each arm dispatches on a single-level constructor shape over `.var`/`.wildcard`
sub-patterns. Top-level `.var x` produces a wildcard case that rebinds the
scrutinee to `x` via a `.letVar` at the top of the body. `.or` flattens
recursively by concatenating both expansions. Any shape outside this subset
throws `.unsupportedPattern`. -/
def expandPattern (scrutTyp : Concrete.Typ) (scrutLocal : Local) :
    Pattern → Concrete.Term →
    Except ConcretizeError (Array (Concrete.Pattern × Concrete.Term))
  | .wildcard, cb => pure #[(.wildcard, cb)]
  | .var x, cb => pure #[(.wildcard,
      .letVar cb.typ cb.escapes x (.var scrutTyp false scrutLocal) cb)]
  | .field g, cb => pure #[(.field g, cb)]
  | .ref g pats, cb => do
      let locals ← subPatternsToLocals pats
      pure #[(.ref g locals, cb)]
  | .tuple pats, cb => do
      let locals ← subPatternsToLocalsArr pats
      pure #[(.tuple locals, cb)]
  | .array pats, cb => do
      let locals ← subPatternsToLocalsArr pats
      pure #[(.array locals, cb)]
  | .or p1 p2, cb => do
      pure ((← expandPattern scrutTyp scrutLocal p1 cb)
              ++ (← expandPattern scrutTyp scrutLocal p2 cb))
  | _, _ => throw .unsupportedPattern

/-- Irrefutable tuple destructuring: given a scrutinee term whose type is a
tuple, a list of sub-patterns (one per field), the element types, and a
body `cb`, produce the nested `.letVar`/`.letWild` + `.proj` sequence. Used
by the single-arm tuple pattern special case of `termToConcrete`'s `.match`. -/
def destructureTuple (scrutTerm : Concrete.Term) (pats : Array Pattern)
    (ts : Array Concrete.Typ) (cb : Concrete.Term) : Concrete.Term :=
  (List.range pats.size).foldl (init := cb) fun acc i =>
    let j := pats.size - 1 - i
    let p := pats[j]?.getD .wildcard
    let eltTyp := ts[j]?.getD .unit
    let projTerm : Concrete.Term := .proj eltTyp false scrutTerm j
    match p with
    | .var x => .letVar acc.typ acc.escapes x projTerm acc
    | _ => .letWild acc.typ acc.escapes projTerm acc

/-- Irrefutable array destructuring: analogous to `destructureTuple` but over
a homogeneous array scrutinee, using `.get` for each element. -/
def destructureArray (scrutTerm : Concrete.Term) (pats : Array Pattern)
    (eltTyp : Concrete.Typ) (cb : Concrete.Term) : Concrete.Term :=
  (List.range pats.size).foldl (init := cb) fun acc i =>
    let j := pats.size - 1 - i
    let p := pats[j]?.getD .wildcard
    let getTerm : Concrete.Term := .get eltTyp false scrutTerm j
    match p with
    | .var x => .letVar acc.typ acc.escapes x getTerm acc
    | _ => .letWild acc.typ acc.escapes getTerm acc

/-! ## The main pass

`termToConcrete` walks a `Typed.Term` and produces a `Concrete.Term`. The only
failure modes are `.mvar` types (ruled out by the checker's zonking step) and
pattern shapes that haven't been flattened by `simplify`'s decision-tree
rewrite (`.pointer` sub-patterns in `.ref`, and non-`.var` scrutinees). -/

def termToConcrete
    (mono : Std.HashMap (Global × Array Typ) Global) :
    Typed.Term → Except ConcretizeError Concrete.Term
  | .unit τ e => do pure (.unit (← typToConcrete mono τ) e)
  | .var τ e x => do pure (.var (← typToConcrete mono τ) e x)
  | .ref τ e g _tArgs => do pure (.ref (← typToConcrete mono τ) e g)
  | .field τ e g => do pure (.field (← typToConcrete mono τ) e g)
  | .tuple τ e ts => do
      pure (.tuple (← typToConcrete mono τ) e (← ts.mapM (termToConcrete mono)))
  | .array τ e ts => do
      pure (.array (← typToConcrete mono τ) e (← ts.mapM (termToConcrete mono)))
  | .ret τ e r => do pure (.ret (← typToConcrete mono τ) e (← termToConcrete mono r))
  | .let τ e pat v b => do
      -- After simplify, patterns are `.var x` or `.wildcard`. Preserve the
      -- variable binding when present; fall back to wildcard otherwise.
      let τ' ← typToConcrete mono τ
      let v' ← termToConcrete mono v
      let b' ← termToConcrete mono b
      match pat with
      | .var x => pure (.letVar τ' e x v' b')
      | _      => pure (.letWild τ' e v' b')
  | .match τ e scrut bs => do
      -- Handle the direct subset: scrutinee is already a `.var` and every
      -- branch pattern is a single-level constructor over `.var`/`.wildcard`
      -- sub-patterns. Tuple/array patterns at the top level are
      -- *irrefutable* — when the match has exactly one such case, we
      -- destructure via `.letVar`/`.letWild` + `.proj`/`.get` instead of
      -- emitting a `Concrete.Term.match` (which `Lower` doesn't support
      -- for tuple/array patterns).
      let τ' ← typToConcrete mono τ
      let scrut' ← termToConcrete mono scrut
      match scrut' with
      | .var scrutTyp _ scrutLocal => do
        let scrutTerm : Concrete.Term := .var scrutTyp false scrutLocal
        -- Single-arm tuple pattern destructuring (irrefutable).
        if let [(Pattern.tuple pats, body)] := bs then
          if let .tuple ts := scrutTyp then
            let cb ← termToConcrete mono body
            return destructureTuple scrutTerm pats ts cb
        -- Single-arm array pattern destructuring (irrefutable, homogeneous).
        if let [(Pattern.array pats, body)] := bs then
          if let .array eltTyp _ := scrutTyp then
            let cb ← termToConcrete mono body
            return destructureArray scrutTerm pats eltTyp cb
        -- General match path: every branch's pattern expands to one or
        -- more single-level `Concrete` cases that `Lower` can dispatch.
        let cases ← bs.toArray.attach.foldlM (init := #[])
          fun acc ⟨(p, b), _⟩ => do
            let cb ← termToConcrete mono b
            pure (acc ++ (← expandPattern scrutTyp scrutLocal p cb))
        pure (.match τ' e scrutLocal cases none)
      | _ => throw .unsupportedMatchScrutinee
  | .app τ e g _tArgs args u => do
      pure (.app (← typToConcrete mono τ) e g (← args.mapM (termToConcrete mono)) u)
  | .add τ e a b => do
      pure (.add (← typToConcrete mono τ) e
                 (← termToConcrete mono a) (← termToConcrete mono b))
  | .sub τ e a b => do
      pure (.sub (← typToConcrete mono τ) e
                 (← termToConcrete mono a) (← termToConcrete mono b))
  | .mul τ e a b => do
      pure (.mul (← typToConcrete mono τ) e
                 (← termToConcrete mono a) (← termToConcrete mono b))
  | .eqZero τ e a => do pure (.eqZero (← typToConcrete mono τ) e (← termToConcrete mono a))
  | .proj τ e a n => do pure (.proj (← typToConcrete mono τ) e (← termToConcrete mono a) n)
  | .get τ e a n => do pure (.get (← typToConcrete mono τ) e (← termToConcrete mono a) n)
  | .slice τ e a i j => do pure (.slice (← typToConcrete mono τ) e (← termToConcrete mono a) i j)
  | .set τ e a n v => do
      pure (.set (← typToConcrete mono τ) e
                 (← termToConcrete mono a) n (← termToConcrete mono v))
  | .store τ e a => do pure (.store (← typToConcrete mono τ) e (← termToConcrete mono a))
  | .load τ e a => do pure (.load (← typToConcrete mono τ) e (← termToConcrete mono a))
  | .ptrVal τ e a => do pure (.ptrVal (← typToConcrete mono τ) e (← termToConcrete mono a))
  | .assertEq τ e a b r => do
      pure (.assertEq (← typToConcrete mono τ) e
                      (← termToConcrete mono a) (← termToConcrete mono b) (← termToConcrete mono r))
  | .ioGetInfo τ e k => do pure (.ioGetInfo (← typToConcrete mono τ) e (← termToConcrete mono k))
  | .ioSetInfo τ e k i l r => do
      pure (.ioSetInfo (← typToConcrete mono τ) e
                       (← termToConcrete mono k) (← termToConcrete mono i)
                       (← termToConcrete mono l) (← termToConcrete mono r))
  | .ioRead τ e i n => do pure (.ioRead (← typToConcrete mono τ) e (← termToConcrete mono i) n)
  | .ioWrite τ e d r => do
      pure (.ioWrite (← typToConcrete mono τ) e
                     (← termToConcrete mono d) (← termToConcrete mono r))
  | .u8BitDecomposition τ e a => do
      pure (.u8BitDecomposition (← typToConcrete mono τ) e (← termToConcrete mono a))
  | .u8ShiftLeft τ e a => do
      pure (.u8ShiftLeft (← typToConcrete mono τ) e (← termToConcrete mono a))
  | .u8ShiftRight τ e a => do
      pure (.u8ShiftRight (← typToConcrete mono τ) e (← termToConcrete mono a))
  | .u8Xor τ e a b => do
      pure (.u8Xor (← typToConcrete mono τ) e
                   (← termToConcrete mono a) (← termToConcrete mono b))
  | .u8Add τ e a b => do
      pure (.u8Add (← typToConcrete mono τ) e
                   (← termToConcrete mono a) (← termToConcrete mono b))
  | .u8Sub τ e a b => do
      pure (.u8Sub (← typToConcrete mono τ) e
                   (← termToConcrete mono a) (← termToConcrete mono b))
  | .u8And τ e a b => do
      pure (.u8And (← typToConcrete mono τ) e
                   (← termToConcrete mono a) (← termToConcrete mono b))
  | .u8Or τ e a b => do
      pure (.u8Or (← typToConcrete mono τ) e
                  (← termToConcrete mono a) (← termToConcrete mono b))
  | .u8LessThan τ e a b => do
      pure (.u8LessThan (← typToConcrete mono τ) e
                        (← termToConcrete mono a) (← termToConcrete mono b))
  | .u32LessThan τ e a b => do
      pure (.u32LessThan (← typToConcrete mono τ) e
                         (← termToConcrete mono a) (← termToConcrete mono b))
  | .debug τ e l t r => do
      -- Inline the Option.mapM case-split so termination sees the sub-Term.
      let t' ← match t with
        | none => pure none
        | some sub => do pure (some (← termToConcrete mono sub))
      pure (.debug (← typToConcrete mono τ) e l t' (← termToConcrete mono r))
termination_by t => sizeOf t
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have : ∀ {α} [SizeOf α] (a : α), sizeOf a < sizeOf (some a) := by
         intros; show _ < 1 + _; omega
       grind)
    | (-- Branch bodies in `.match`: `(p, b) ∈ bs.toArray` ⇒ `sizeOf b < sizeOf bs`
       have hmem : _ ∈ _ := ‹_ ∈ _›
       have := Array.sizeOf_lt_of_mem hmem
       grind)

/-! ## Progress lemmas moved to `Proofs/ConcretizeProgress.lean`. -/


/-! ## Monomorphization — worklist + rewriting (port of `Ix/Aiur/Compiler/Concretize.lean`) -/

abbrev MonoMap := Std.HashMap (Global × Array Typ) Global

/-- Apply a type-parameter substitution + mono-map rewrite to a `Typ`.
An `.app g args` whose `(g, args)` is in `mono` is replaced by `.ref (mono[(g, args)]!)`;
otherwise the `.app` persists with args recursively rewritten. -/
def rewriteTyp (subst : Global → Option Typ) (mono : MonoMap) : Typ → Typ
  | .ref g => (subst g).getD (.ref g)
  | .app g args =>
    match mono[(g, args)]? with
    | some concName => .ref concName
    | none => .app g (args.attach.map fun ⟨t, _⟩ => rewriteTyp subst mono t)
  | .tuple ts => .tuple (ts.attach.map fun ⟨t, _⟩ => rewriteTyp subst mono t)
  | .array t n => .array (rewriteTyp subst mono t) n
  | .pointer t => .pointer (rewriteTyp subst mono t)
  | .function ins out =>
    .function (ins.attach.map fun ⟨t, _⟩ => rewriteTyp subst mono t)
              (rewriteTyp subst mono out)
  | t => t
termination_by t => sizeOf t
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

/-- Rewrite a reference to a function or a constructor's global name, using the
type-args from the site that referenced it. Returns the monomorphic name when
available, otherwise the original global. -/
def rewriteGlobal (decls : Typed.Decls) (mono : MonoMap)
    (g : Global) (tArgs : Array Typ) : Global :=
  if tArgs.isEmpty then g
  else match decls.getByKey g with
    | some (.function _) =>
      match mono[(g, tArgs)]? with
      | some concName => concName
      | none => g
    | some (.constructor dt _) =>
      match g.popNamespace with
      | some (ctorName, _) =>
        match mono[(dt.name, tArgs)]? with
        | some concDTName => concDTName.pushNamespace ctorName
        | none => g
      | none => g
    | _ => g

/-- Rewrite constructor names in patterns, using the expected (unrewritten)
scrutinee type to determine which monomorphic instance to use. -/
def rewritePattern (decls : Typed.Decls) (mono : MonoMap)
    (expectedTyp : Typ) : Pattern → Pattern
  | .ref g pats =>
    let tArgs : Array Typ := match expectedTyp with
      | .app _ args => args
      | _ => #[]
    let g' := rewriteGlobal decls mono g tArgs
    -- Post-simplify, sub-patterns of a `.ref` are all `.var` / `.wildcard`
    -- (the match compiler flattens nested patterns into a chain of switches).
    -- Inner `rewritePattern` calls are therefore no-ops; passing `.unit` as the
    -- expected type is sound because the no-op arms never consult `expectedTyp`.
    let pats' := pats.attach.map fun ⟨p, _⟩ => rewritePattern decls mono .unit p
    .ref g' pats'
  | .tuple pats =>
    -- Sub-patterns of a tuple pattern are flattened to simple vars by simplify;
    -- same justification as above for passing `.unit`.
    .tuple (pats.attach.map fun ⟨p, _⟩ => rewritePattern decls mono .unit p)
  | .array pats =>
    let innerTyp : Typ := match expectedTyp with
      | .array t _ => t
      | _ => .unit
    .array (pats.attach.map fun ⟨p, _⟩ => rewritePattern decls mono innerTyp p)
  | .or a b =>
    .or (rewritePattern decls mono expectedTyp a) (rewritePattern decls mono expectedTyp b)
  | .pointer p =>
    match expectedTyp with
    | .pointer inner => .pointer (rewritePattern decls mono inner p)
    | _ => .pointer p
  | p => p
termination_by p => sizeOf p
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

/-- Rewrite a `Typed.Term`: rewrites type annotations, function/constructor
names via `.app`/`.ref`, and branch patterns (via `rewritePattern`). -/
def rewriteTypedTerm (decls : Typed.Decls)
    (subst : Global → Option Typ) (mono : MonoMap) : Typed.Term → Typed.Term
  | .unit τ e => .unit (rewriteTyp subst mono τ) e
  | .var τ e x => .var (rewriteTyp subst mono τ) e x
  | .ref τ e g tArgs =>
    let g' := rewriteGlobal decls mono g tArgs
    .ref (rewriteTyp subst mono τ) e g' (tArgs.map (rewriteTyp subst mono))
  | .field τ e v => .field (rewriteTyp subst mono τ) e v
  | .tuple τ e ts =>
    .tuple (rewriteTyp subst mono τ) e
      (ts.attach.map fun ⟨t, _⟩ => rewriteTypedTerm decls subst mono t)
  | .array τ e ts =>
    .array (rewriteTyp subst mono τ) e
      (ts.attach.map fun ⟨t, _⟩ => rewriteTypedTerm decls subst mono t)
  | .ret τ e r =>
    .ret (rewriteTyp subst mono τ) e (rewriteTypedTerm decls subst mono r)
  | .let τ e p v b =>
    let vTyp := v.typ
    .let (rewriteTyp subst mono τ) e
         (rewritePattern decls mono vTyp p)
         (rewriteTypedTerm decls subst mono v)
         (rewriteTypedTerm decls subst mono b)
  | .match τ e scrut bs =>
    let scrutTyp := scrut.typ
    .match (rewriteTyp subst mono τ) e
           (rewriteTypedTerm decls subst mono scrut)
           (bs.attach.map fun ⟨(p, b), _⟩ =>
             (rewritePattern decls mono scrutTyp p,
              rewriteTypedTerm decls subst mono b))
  | .app τ e g tArgs args u =>
    let g' := rewriteGlobal decls mono g tArgs
    .app (rewriteTyp subst mono τ) e g' #[]
         (args.attach.map fun ⟨a, _⟩ => rewriteTypedTerm decls subst mono a) u
  | .add τ e a b => .add (rewriteTyp subst mono τ) e
      (rewriteTypedTerm decls subst mono a) (rewriteTypedTerm decls subst mono b)
  | .sub τ e a b => .sub (rewriteTyp subst mono τ) e
      (rewriteTypedTerm decls subst mono a) (rewriteTypedTerm decls subst mono b)
  | .mul τ e a b => .mul (rewriteTyp subst mono τ) e
      (rewriteTypedTerm decls subst mono a) (rewriteTypedTerm decls subst mono b)
  | .eqZero τ e a => .eqZero (rewriteTyp subst mono τ) e (rewriteTypedTerm decls subst mono a)
  | .proj τ e a n => .proj (rewriteTyp subst mono τ) e (rewriteTypedTerm decls subst mono a) n
  | .get τ e a n => .get (rewriteTyp subst mono τ) e (rewriteTypedTerm decls subst mono a) n
  | .slice τ e a i j => .slice (rewriteTyp subst mono τ) e (rewriteTypedTerm decls subst mono a) i j
  | .set τ e a n v =>
    .set (rewriteTyp subst mono τ) e
         (rewriteTypedTerm decls subst mono a) n
         (rewriteTypedTerm decls subst mono v)
  | .store τ e a => .store (rewriteTyp subst mono τ) e (rewriteTypedTerm decls subst mono a)
  | .load τ e a => .load (rewriteTyp subst mono τ) e (rewriteTypedTerm decls subst mono a)
  | .ptrVal τ e a => .ptrVal (rewriteTyp subst mono τ) e (rewriteTypedTerm decls subst mono a)
  | .assertEq τ e a b r =>
    .assertEq (rewriteTyp subst mono τ) e
              (rewriteTypedTerm decls subst mono a) (rewriteTypedTerm decls subst mono b)
              (rewriteTypedTerm decls subst mono r)
  | .ioGetInfo τ e k =>
    .ioGetInfo (rewriteTyp subst mono τ) e (rewriteTypedTerm decls subst mono k)
  | .ioSetInfo τ e k i l r =>
    .ioSetInfo (rewriteTyp subst mono τ) e
      (rewriteTypedTerm decls subst mono k) (rewriteTypedTerm decls subst mono i)
      (rewriteTypedTerm decls subst mono l) (rewriteTypedTerm decls subst mono r)
  | .ioRead τ e i n => .ioRead (rewriteTyp subst mono τ) e (rewriteTypedTerm decls subst mono i) n
  | .ioWrite τ e d r =>
    .ioWrite (rewriteTyp subst mono τ) e
             (rewriteTypedTerm decls subst mono d) (rewriteTypedTerm decls subst mono r)
  | .u8BitDecomposition τ e a =>
    .u8BitDecomposition (rewriteTyp subst mono τ) e (rewriteTypedTerm decls subst mono a)
  | .u8ShiftLeft τ e a =>
    .u8ShiftLeft (rewriteTyp subst mono τ) e (rewriteTypedTerm decls subst mono a)
  | .u8ShiftRight τ e a =>
    .u8ShiftRight (rewriteTyp subst mono τ) e (rewriteTypedTerm decls subst mono a)
  | .u8Xor τ e a b => .u8Xor (rewriteTyp subst mono τ) e
      (rewriteTypedTerm decls subst mono a) (rewriteTypedTerm decls subst mono b)
  | .u8Add τ e a b => .u8Add (rewriteTyp subst mono τ) e
      (rewriteTypedTerm decls subst mono a) (rewriteTypedTerm decls subst mono b)
  | .u8Sub τ e a b => .u8Sub (rewriteTyp subst mono τ) e
      (rewriteTypedTerm decls subst mono a) (rewriteTypedTerm decls subst mono b)
  | .u8And τ e a b => .u8And (rewriteTyp subst mono τ) e
      (rewriteTypedTerm decls subst mono a) (rewriteTypedTerm decls subst mono b)
  | .u8Or τ e a b => .u8Or (rewriteTyp subst mono τ) e
      (rewriteTypedTerm decls subst mono a) (rewriteTypedTerm decls subst mono b)
  | .u8LessThan τ e a b => .u8LessThan (rewriteTyp subst mono τ) e
      (rewriteTypedTerm decls subst mono a) (rewriteTypedTerm decls subst mono b)
  | .u32LessThan τ e a b => .u32LessThan (rewriteTyp subst mono τ) e
      (rewriteTypedTerm decls subst mono a) (rewriteTypedTerm decls subst mono b)
  | .debug τ e l t r =>
    let t' := match t with
      | none => none
      | some sub => some (rewriteTypedTerm decls subst mono sub)
    .debug (rewriteTyp subst mono τ) e l t' (rewriteTypedTerm decls subst mono r)
termination_by t => sizeOf t
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have : ∀ {α} [SizeOf α] (a : α), sizeOf a < sizeOf (some a) := by
         intros; show _ < 1 + _; omega
       grind)
    | (have hmem : _ ∈ _ := ‹_ ∈ _›
       have := List.sizeOf_lt_of_mem hmem
       grind)
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)


/-- Collect every `(Global, Array Typ)` instantiation reachable from a type. -/
def collectInTyp (seen : Std.HashSet (Global × Array Typ)) :
    Typ → Std.HashSet (Global × Array Typ)
  | .app g args =>
    let seen := args.attach.foldl (fun s ⟨t, _⟩ => collectInTyp s t) seen
    seen.insert (g, args)
  | .tuple ts => ts.attach.foldl (fun s ⟨t, _⟩ => collectInTyp s t) seen
  | .array t _ => collectInTyp seen t
  | .pointer t => collectInTyp seen t
  | .function ins out =>
    let seen := ins.attach.foldl (fun s ⟨t, _⟩ => collectInTyp s t) seen
    collectInTyp seen out
  | _ => seen
termination_by t => sizeOf t
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

/-- Collect `(Global, Array Typ)` instantiations reachable from types embedded
in a `Typed.Term`. -/
def collectInTypedTerm (seen : Std.HashSet (Global × Array Typ)) :
    Typed.Term → Std.HashSet (Global × Array Typ)
  | .unit τ _ => collectInTyp seen τ
  | .var τ _ _ => collectInTyp seen τ
  | .ref τ _ _ tArgs =>
    let seen := collectInTyp seen τ
    tArgs.foldl collectInTyp seen
  | .field τ _ _ => collectInTyp seen τ
  | .tuple τ _ ts =>
    let seen := collectInTyp seen τ
    ts.attach.foldl (fun s ⟨t, _⟩ => collectInTypedTerm s t) seen
  | .array τ _ ts =>
    let seen := collectInTyp seen τ
    ts.attach.foldl (fun s ⟨t, _⟩ => collectInTypedTerm s t) seen
  | .ret τ _ r => collectInTypedTerm (collectInTyp seen τ) r
  | .let τ _ _ v b =>
    let seen := collectInTyp seen τ
    collectInTypedTerm (collectInTypedTerm seen v) b
  | .match τ _ scrut bs =>
    let seen := collectInTyp seen τ
    let seen := collectInTypedTerm seen scrut
    bs.attach.foldl (fun s ⟨(_, b), _⟩ => collectInTypedTerm s b) seen
  | .app τ _ _ tArgs args _ =>
    let seen := collectInTyp seen τ
    let seen := tArgs.foldl collectInTyp seen
    args.attach.foldl (fun s ⟨a, _⟩ => collectInTypedTerm s a) seen
  | .add τ _ a b | .sub τ _ a b | .mul τ _ a b
  | .u8Xor τ _ a b | .u8Add τ _ a b | .u8Sub τ _ a b
  | .u8And τ _ a b | .u8Or τ _ a b
  | .u8LessThan τ _ a b | .u32LessThan τ _ a b =>
    collectInTypedTerm (collectInTypedTerm (collectInTyp seen τ) a) b
  | .eqZero τ _ a | .store τ _ a | .load τ _ a | .ptrVal τ _ a
  | .u8BitDecomposition τ _ a | .u8ShiftLeft τ _ a | .u8ShiftRight τ _ a
  | .ioGetInfo τ _ a => collectInTypedTerm (collectInTyp seen τ) a
  | .proj τ _ a _ | .get τ _ a _ | .slice τ _ a _ _ =>
    collectInTypedTerm (collectInTyp seen τ) a
  | .set τ _ a _ v => collectInTypedTerm (collectInTypedTerm (collectInTyp seen τ) a) v
  | .assertEq τ _ a b r =>
    collectInTypedTerm
      (collectInTypedTerm (collectInTypedTerm (collectInTyp seen τ) a) b) r
  | .ioSetInfo τ _ k i l r =>
    collectInTypedTerm
      (collectInTypedTerm
        (collectInTypedTerm (collectInTypedTerm (collectInTyp seen τ) k) i) l) r
  | .ioRead τ _ i _ => collectInTypedTerm (collectInTyp seen τ) i
  | .ioWrite τ _ d r => collectInTypedTerm (collectInTypedTerm (collectInTyp seen τ) d) r
  | .debug τ _ _ t r =>
    let seen := collectInTyp seen τ
    let seen := match t with | some t => collectInTypedTerm seen t | none => seen
    collectInTypedTerm seen r
termination_by t => sizeOf t
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have : ∀ {α} [SizeOf α] (a : α), sizeOf a < sizeOf (some a) := by
         intros; show _ < 1 + _; omega
       grind)
    | (have hmem : _ ∈ _ := ‹_ ∈ _›
       have := List.sizeOf_lt_of_mem hmem
       grind)
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

/-- Collect call instantiations from `.app`/`.ref` `tArgs` in a `Typed.Term`,
resolving them against the declaration kind (function vs. constructor). -/
def collectCalls (decls : Typed.Decls)
    (seen : Std.HashSet (Global × Array Typ)) :
    Typed.Term → Std.HashSet (Global × Array Typ)
  | .app _ _ g tArgs args _ =>
    let seen := args.attach.foldl (fun s ⟨a, _⟩ => collectCalls decls s a) seen
    if tArgs.isEmpty then seen
    else match decls.getByKey g with
      | some (.function _) => seen.insert (g, tArgs)
      | some (.constructor dt _) => seen.insert (dt.name, tArgs)
      | _ => seen
  | .ref _ _ g tArgs =>
    if tArgs.isEmpty then seen
    else match decls.getByKey g with
      | some (.function _) => seen.insert (g, tArgs)
      | some (.constructor dt _) => seen.insert (dt.name, tArgs)
      | _ => seen
  | .unit _ _ | .var _ _ _ | .field _ _ _ => seen
  | .tuple _ _ ts | .array _ _ ts =>
    ts.attach.foldl (fun s ⟨t, _⟩ => collectCalls decls s t) seen
  | .ret _ _ r => collectCalls decls seen r
  | .let _ _ _ v b => collectCalls decls (collectCalls decls seen v) b
  | .match _ _ scrut bs =>
    let seen := collectCalls decls seen scrut
    bs.attach.foldl (fun s ⟨(_, b), _⟩ => collectCalls decls s b) seen
  | .add _ _ a b | .sub _ _ a b | .mul _ _ a b
  | .u8Xor _ _ a b | .u8Add _ _ a b | .u8Sub _ _ a b
  | .u8And _ _ a b | .u8Or _ _ a b
  | .u8LessThan _ _ a b | .u32LessThan _ _ a b =>
    collectCalls decls (collectCalls decls seen a) b
  | .eqZero _ _ a | .store _ _ a | .load _ _ a | .ptrVal _ _ a
  | .u8BitDecomposition _ _ a | .u8ShiftLeft _ _ a | .u8ShiftRight _ _ a
  | .ioGetInfo _ _ a => collectCalls decls seen a
  | .proj _ _ a _ | .get _ _ a _ | .slice _ _ a _ _ => collectCalls decls seen a
  | .set _ _ a _ v => collectCalls decls (collectCalls decls seen a) v
  | .assertEq _ _ a b r =>
    collectCalls decls (collectCalls decls (collectCalls decls seen a) b) r
  | .ioSetInfo _ _ k i l r =>
    collectCalls decls
      (collectCalls decls (collectCalls decls (collectCalls decls seen k) i) l) r
  | .ioRead _ _ i _ => collectCalls decls seen i
  | .ioWrite _ _ d r => collectCalls decls (collectCalls decls seen d) r
  | .debug _ _ _ t r =>
    let seen := match t with | some t => collectCalls decls seen t | none => seen
    collectCalls decls seen r
termination_by t => sizeOf t
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have : ∀ {α} [SizeOf α] (a : α), sizeOf a < sizeOf (some a) := by
         intros; show _ < 1 + _; omega
       grind)
    | (have hmem : _ ∈ _ := ‹_ ∈ _›
       have := List.sizeOf_lt_of_mem hmem
       grind)
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

/-- Substitute type parameters throughout a `Typed.Term`, leaving function and
constructor names unchanged (name rewriting is done later by `rewriteTypedTerm`). -/
def substInTypedTerm (subst : Global → Option Typ) : Typed.Term → Typed.Term
  | .unit τ e => .unit (Typ.instantiate subst τ) e
  | .var τ e x => .var (Typ.instantiate subst τ) e x
  | .ref τ e g tArgs =>
    .ref (Typ.instantiate subst τ) e g (tArgs.map (Typ.instantiate subst))
  | .field τ e v => .field (Typ.instantiate subst τ) e v
  | .tuple τ e ts =>
    .tuple (Typ.instantiate subst τ) e
      (ts.attach.map fun ⟨t, _⟩ => substInTypedTerm subst t)
  | .array τ e ts =>
    .array (Typ.instantiate subst τ) e
      (ts.attach.map fun ⟨t, _⟩ => substInTypedTerm subst t)
  | .ret τ e r => .ret (Typ.instantiate subst τ) e (substInTypedTerm subst r)
  | .let τ e p v b =>
    .let (Typ.instantiate subst τ) e p (substInTypedTerm subst v) (substInTypedTerm subst b)
  | .match τ e scrut bs =>
    .match (Typ.instantiate subst τ) e (substInTypedTerm subst scrut)
      (bs.attach.map fun ⟨(p, b), _⟩ => (p, substInTypedTerm subst b))
  | .app τ e g tArgs args u =>
    .app (Typ.instantiate subst τ) e g (tArgs.map (Typ.instantiate subst))
         (args.attach.map fun ⟨a, _⟩ => substInTypedTerm subst a) u
  | .add τ e a b => .add (Typ.instantiate subst τ) e
      (substInTypedTerm subst a) (substInTypedTerm subst b)
  | .sub τ e a b => .sub (Typ.instantiate subst τ) e
      (substInTypedTerm subst a) (substInTypedTerm subst b)
  | .mul τ e a b => .mul (Typ.instantiate subst τ) e
      (substInTypedTerm subst a) (substInTypedTerm subst b)
  | .eqZero τ e a => .eqZero (Typ.instantiate subst τ) e (substInTypedTerm subst a)
  | .proj τ e a n => .proj (Typ.instantiate subst τ) e (substInTypedTerm subst a) n
  | .get τ e a n => .get (Typ.instantiate subst τ) e (substInTypedTerm subst a) n
  | .slice τ e a i j => .slice (Typ.instantiate subst τ) e (substInTypedTerm subst a) i j
  | .set τ e a n v =>
    .set (Typ.instantiate subst τ) e (substInTypedTerm subst a) n (substInTypedTerm subst v)
  | .store τ e a => .store (Typ.instantiate subst τ) e (substInTypedTerm subst a)
  | .load τ e a => .load (Typ.instantiate subst τ) e (substInTypedTerm subst a)
  | .ptrVal τ e a => .ptrVal (Typ.instantiate subst τ) e (substInTypedTerm subst a)
  | .assertEq τ e a b r =>
    .assertEq (Typ.instantiate subst τ) e (substInTypedTerm subst a)
              (substInTypedTerm subst b) (substInTypedTerm subst r)
  | .ioGetInfo τ e k => .ioGetInfo (Typ.instantiate subst τ) e (substInTypedTerm subst k)
  | .ioSetInfo τ e k i l r =>
    .ioSetInfo (Typ.instantiate subst τ) e
      (substInTypedTerm subst k) (substInTypedTerm subst i)
      (substInTypedTerm subst l) (substInTypedTerm subst r)
  | .ioRead τ e i n => .ioRead (Typ.instantiate subst τ) e (substInTypedTerm subst i) n
  | .ioWrite τ e d r => .ioWrite (Typ.instantiate subst τ) e
      (substInTypedTerm subst d) (substInTypedTerm subst r)
  | .u8BitDecomposition τ e a =>
    .u8BitDecomposition (Typ.instantiate subst τ) e (substInTypedTerm subst a)
  | .u8ShiftLeft τ e a =>
    .u8ShiftLeft (Typ.instantiate subst τ) e (substInTypedTerm subst a)
  | .u8ShiftRight τ e a =>
    .u8ShiftRight (Typ.instantiate subst τ) e (substInTypedTerm subst a)
  | .u8Xor τ e a b => .u8Xor (Typ.instantiate subst τ) e
      (substInTypedTerm subst a) (substInTypedTerm subst b)
  | .u8Add τ e a b => .u8Add (Typ.instantiate subst τ) e
      (substInTypedTerm subst a) (substInTypedTerm subst b)
  | .u8Sub τ e a b => .u8Sub (Typ.instantiate subst τ) e
      (substInTypedTerm subst a) (substInTypedTerm subst b)
  | .u8And τ e a b => .u8And (Typ.instantiate subst τ) e
      (substInTypedTerm subst a) (substInTypedTerm subst b)
  | .u8Or τ e a b => .u8Or (Typ.instantiate subst τ) e
      (substInTypedTerm subst a) (substInTypedTerm subst b)
  | .u8LessThan τ e a b => .u8LessThan (Typ.instantiate subst τ) e
      (substInTypedTerm subst a) (substInTypedTerm subst b)
  | .u32LessThan τ e a b => .u32LessThan (Typ.instantiate subst τ) e
      (substInTypedTerm subst a) (substInTypedTerm subst b)
  | .debug τ e l t r =>
    let t' := match t with
      | none => none
      | some sub => some (substInTypedTerm subst sub)
    .debug (Typ.instantiate subst τ) e l t' (substInTypedTerm subst r)
termination_by t => sizeOf t
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have : ∀ {α} [SizeOf α] (a : α), sizeOf a < sizeOf (some a) := by
         intros; show _ < 1 + _; omega
       grind)
    | (-- List branch bodies in `.match`: `(p, b) ∈ bs` ⇒ `sizeOf b < sizeOf bs`.
       have hmem : _ ∈ _ := ‹_ ∈ _›
       have := List.sizeOf_lt_of_mem hmem
       grind)
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

/-! ### Pure-fold decomposition of `Typed.Decls.concretize`.

Four pure functions:
  * `concretizeSeed` — Step 1, collect initial worklist from monomorphic decls.
  * `concretizeDrain` — Step 2, fuel-bounded worklist specialization.
  * `concretizeBuild` — Step 3, rewrite monomorphic decls using mono-map.
  * `step4Lower` — Step 4, lower to `Concrete.Decls` (defined in ConcretizeSound).

Composed without `let mut` / `while` / `for`. Each step exposes its equation
for downstream proofs. -/

/-- Step 2 state: pending worklist + seen set + accumulated mono map + arrays
of newly-specialized functions and datatypes. -/
structure DrainState where
  pending : Std.HashSet (Global × Array Typ)
  seen : Std.HashSet (Global × Array Typ)
  mono : Std.HashMap (Global × Array Typ) Global
  newFunctions : Array Typed.Function
  newDataTypes : Array DataType

/-- Step 1: seed the worklist from every monomorphic decl in `decls`. -/
def concretizeSeed (decls : Typed.Decls) : Std.HashSet (Global × Array Typ) :=
  decls.pairs.foldl
    (fun pending p =>
      match p.snd with
      | .function f =>
        if f.params.isEmpty then
          let p1 := collectInTyp pending f.output
          let p2 := f.inputs.foldl (fun s (_, t) => collectInTyp s t) p1
          let p3 := collectInTypedTerm p2 f.body
          collectCalls decls p3 f.body
        else pending
      | .dataType dt =>
        if dt.params.isEmpty then
          dt.constructors.foldl
            (fun s c => c.argTypes.foldl collectInTyp s) pending
        else pending
      | _ => pending)
    {}

/-- Process one `(name, args)` entry in the worklist: insert into `seen` + `mono`,
specialize its template, push new pending entries from substituted body. -/
def concretizeDrainEntry (decls : Typed.Decls) (state : DrainState)
    (entry : Global × Array Typ) : Except ConcretizeError DrainState := do
  let (name, args) := entry
  if state.seen.contains (name, args) then pure state
  else
    let concName := concretizeName name args
    let seen' := state.seen.insert (name, args)
    let mono' := state.mono.insert (name, args) concName
    match decls.getByKey name with
    | some (.function f) =>
      if f.params.length != args.size then
        throw (.wrongNumArgs name f.params.length args.size)
      let subst := mkParamSubst f.params args
      let newInputs := f.inputs.map fun (l, t) => (l, Typ.instantiate subst t)
      let newOutput := Typ.instantiate subst f.output
      let newBody := substInTypedTerm subst f.body
      let p1 := collectInTyp state.pending newOutput
      let p2 := newInputs.foldl (fun s (_, t) => collectInTyp s t) p1
      let p3 := collectInTypedTerm p2 newBody
      let pending' := collectCalls decls p3 newBody
      let newFn : Typed.Function :=
        { name := concName, params := [], inputs := newInputs,
          output := newOutput, body := newBody, entry := false }
      pure { pending := pending', seen := seen', mono := mono',
             newFunctions := state.newFunctions.push newFn,
             newDataTypes := state.newDataTypes }
    | some (.dataType dt) =>
      if dt.params.length != args.size then
        throw (.wrongNumArgs name dt.params.length args.size)
      let subst := mkParamSubst dt.params args
      let newCtors := dt.constructors.map fun c =>
        { c with argTypes := c.argTypes.map (Typ.instantiate subst) }
      let pending' := newCtors.foldl
        (fun s c => c.argTypes.foldl collectInTyp s) state.pending
      let newDt : DataType :=
        { name := concName, params := [], constructors := newCtors }
      pure { pending := pending', seen := seen', mono := mono',
             newFunctions := state.newFunctions,
             newDataTypes := state.newDataTypes.push newDt }
    | _ => throw (.templateNotFound name)

/-- One worklist iteration: drain all current `pending` into `seen` + mono.
New entries discovered during draining are added to the next-iteration
`pending`. Starts each iteration with `pending = {}`. -/
def concretizeDrainIter (decls : Typed.Decls) (state : DrainState) :
    Except ConcretizeError DrainState :=
  let batch := state.pending
  let state0 : DrainState := { state with pending := {} }
  batch.toArray.foldlM (concretizeDrainEntry decls) state0

/-- Step 2: fuel-bounded worklist drain. Fuel bounds total iterations; each
iteration fully drains current `pending` and may add new entries for the next.
`fuelExhausted` thrown if fuel hits 0 with non-empty pending.

For fully-monomorphic programs, 1 iteration suffices — `pending` empties
after the first drain since no polymorphic templates exist. -/
def concretizeDrain (decls : Typed.Decls) :
    Nat → DrainState → Except ConcretizeError DrainState
  | 0, state =>
    if state.pending.isEmpty then pure state
    else throw .fuelExhausted
  | fuel+1, state =>
    if state.pending.isEmpty then pure state
    else do
      let state' ← concretizeDrainIter decls state
      concretizeDrain decls fuel state'

/-- Step 3: build the rewritten monomorphic `Typed.Decls`. All `.app` types
with a mono-map entry are rewritten to `.ref`. -/
def concretizeBuild (decls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType) :
    Typed.Decls :=
  let emptySubst : Global → Option Typ := fun _ => none
  let fromSource : Typed.Decls := decls.pairs.foldl
    (fun acc p =>
      let (key, d) := p
      match d with
      | .function f =>
        if f.params.isEmpty then
          let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
          let newOutput := rewriteTyp emptySubst mono f.output
          let newBody := rewriteTypedTerm decls emptySubst mono f.body
          acc.insert key (.function
            { f with inputs := newInputs, output := newOutput, body := newBody })
        else acc
      | .dataType dt =>
        if dt.params.isEmpty then
          let newCtors := dt.constructors.map fun c =>
            { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
          acc.insert key (.dataType { dt with constructors := newCtors })
        else acc
      | .constructor dt c =>
        if dt.params.isEmpty then
          let newArgTypes := c.argTypes.map (rewriteTyp emptySubst mono)
          let newCtor : Constructor := { c with argTypes := newArgTypes }
          let rewrittenCtors := dt.constructors.map fun c' =>
            { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }
          let newDt : DataType := { dt with constructors := rewrittenCtors }
          acc.insert key (.constructor newDt newCtor)
        else acc)
    default
  let withNewDts : Typed.Decls := newDataTypes.foldl
    (fun acc dt =>
      let rewrittenCtors := dt.constructors.map fun c =>
        { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
      let newDt : DataType := { dt with constructors := rewrittenCtors }
      let acc' := acc.insert dt.name (.dataType newDt)
      rewrittenCtors.foldl
        (fun acc'' c =>
          let cName := dt.name.pushNamespace c.nameHead
          acc''.insert cName (.constructor newDt c))
        acc')
    fromSource
  newFunctions.foldl
    (fun acc f =>
      let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
      let newOutput := rewriteTyp emptySubst mono f.output
      let newBody := rewriteTypedTerm decls emptySubst mono f.body
      let newF : Typed.Function :=
        { f with inputs := newInputs, output := newOutput, body := newBody }
      acc.insert f.name (.function newF))
    withNewDts

/-- Fuel bound for Step 2: worst-case iterations of the worklist loop. Each
iteration adds at least one new `seen` entry (else `pending = ∅` exits). Total
entries ≤ number of distinct `(name, args)` pairs reachable from `decls` —
bounded by `decls.size * (upper-bound on nesting depth of type-argument
substitution)`. For fully-monomorphic programs, 1 suffices. Pick a generous
bound: `decls.size + 1`. Caller can raise if polymorphism hits the ceiling. -/
def concretizeDrainFuel (decls : Typed.Decls) : Nat := decls.size + 1

/-- The Step-4 lowering step: lowers one `(name, Typed.Declaration)` entry to
`Concrete.Decls` with an empty mono-map (all template instantiation is baked
into the keys by `concretizeBuild`). Named so downstream proofs can manipulate
the final `foldlM` equationally instead of through an anonymous lambda. -/
def step4Lower :
    Concrete.Decls → Global × Typed.Declaration →
      Except ConcretizeError Concrete.Decls :=
  fun acc (name, d) => do
    let emptyMono : Std.HashMap (Global × Array Typ) Global := {}
    match d with
    | .function f =>
      let inputs ← f.inputs.mapM fun (l, t) => do
        let t' ← typToConcrete emptyMono t
        pure (l, t')
      let output ← typToConcrete emptyMono f.output
      let body ← termToConcrete emptyMono f.body
      let concF : Concrete.Function :=
        { name := f.name, inputs, output, body, entry := f.entry }
      pure (acc.insert name (.function concF))
    | .dataType dt =>
      let ctors ← dt.constructors.mapM fun c => do
        let argTypes ← c.argTypes.mapM (typToConcrete emptyMono)
        pure ({ nameHead := c.nameHead, argTypes } : Concrete.Constructor)
      let concDt : Concrete.DataType := { name := dt.name, constructors := ctors }
      pure (acc.insert name (.dataType concDt))
    | .constructor dt c =>
      let ctors ← dt.constructors.mapM fun c' => do
        let argTypes ← c'.argTypes.mapM (typToConcrete emptyMono)
        pure ({ nameHead := c'.nameHead, argTypes } : Concrete.Constructor)
      let concDt : Concrete.DataType := { name := dt.name, constructors := ctors }
      let argTypes ← c.argTypes.mapM (typToConcrete emptyMono)
      let concC : Concrete.Constructor := { nameHead := c.nameHead, argTypes }
      pure (acc.insert name (.constructor concDt concC))

/-- Specialise every polymorphic template reachable from concrete decls into a
concrete monomorphic copy, then lower the whole table to `Concrete.Decls`. -/
def Typed.Decls.concretize (decls : Typed.Decls) :
    Except ConcretizeError Concrete.Decls := do
  let pending := concretizeSeed decls
  let initState : DrainState :=
    { pending, seen := {}, mono := {}, newFunctions := #[], newDataTypes := #[] }
  let drained ← concretizeDrain decls (concretizeDrainFuel decls) initState
  let monoDecls := concretizeBuild decls drained.mono
    drained.newFunctions drained.newDataTypes
  monoDecls.foldlM (init := default) step4Lower

end Aiur

end -- @[expose] section
end
