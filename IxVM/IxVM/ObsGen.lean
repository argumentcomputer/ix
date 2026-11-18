import IxVM.ProofGen
import IxVM.ExprPath

/-! # Generated path lemmas for observed derivations

For every IxVM function (monomorphic, without control syntax), this generator
renders an inductive `«f».Path` with one constructor per evaluation path of
the body (one per combination of selected arms), and a theorem `«f».obs` that
every observed derivation of `f` (`ObsFn`) takes one of the paths. A path's
fields are what the derivation established along it, with every variable
replaced by the value it was bound to:

* `loadValue heap p = .ok v` for each load;
* `ObsFn W "g" args heap result heap' cs` for each call (the callee's own
  derivation, with its call list `cs`);
* `v = template` when an arm's pattern matched a parameter, and `v ≠ u` (or
  `∀ vs, vs.length = n → v ≠ .construct E c vs`) when an earlier arm's literal
  or flat pattern did not match;
* `evalBinOp`, projection, member, slice, negation, update and hint facts as
  the semantics states them, and `x = y` for each `assert_eq!`;
* `r = …`, `h' = …` for the result and final heap when the path does not end
  in a call, and `calls = …`, the call list in normal form.

The proof inverts the derivation node by node with the generic lemmas of
`IxVMRefinement.Core.Obs` and closes each path with its constructor.

The generator reads only the program (`IxVM.program`) and the table of names
(`IxVM/IxVM/ObsNames.txt`): its output follows the source. It is untrusted; Lean
checks every generated proof.

**Names.** A generated name is a base (`ev`, `hv`, `m`, …) and a suffix. It is asked
for at a *position* in the function: the arms selected so far in matches of several
arms, the place in the body (the chain of enclosing statements and operands, a
statement being named by what it binds, not by its index), the
base, and how many names of that base the place has been given. A position does not
move when a statement is added or removed before it ("Places in the body" says what
the format is, and what does move a name).

* A name that appears in a constructor (a binder that is kept, a fact) is *shown*:
  proofs refer to it. Its suffix is the table's entry for the position if there is
  one, and `_` with eight letters derived from the position otherwise.
* Every other name is local to the generated proof and keeps the suffix of a
  counter that runs through the function.

The table holds, for each position that was shown when it was written, the suffix
the counter gave it then (`--emit-names`): at that source, the output is the
counter's, byte for byte. The table is never extended; its header carries a hash of
its lines, which the generator checks.

Two shown names of one inductive that read the same, two fields of one name in a
constructor, or a second pass that asks for other names than the first, stop the
generation: no function is dropped for its names. -/

namespace IxVM.ObsGen

open Aiur.Generic
open Aiur.Generic.SourceSemantics (instanceName constructorName)
open Aiur (BinOp)
open IxVM.ProofGen (q list field ty fieldRef updateStep functionName)

abbrev F := IxVM.F

/-! ## Terms -/

/-- A Lean term over the path's variables, kept structured so that a pattern
match can replace a variable by its template. -/
inductive T where
  | v (name : String)
  | field (c : String)
  | tuple (items : List T)
  /-- `.construct e c items`, `e` a rendered string literal. -/
  | ctor (e c : String) (items : List T)
  /-- `.ptr (type of stored) heap.length`. -/
  | ptr (stored heap : T)
  /-- `heap ++ [x]`. -/
  | snoc (heap x : T)
  /-- `(head a₁ … aₙ)`. -/
  | app (head : String) (args : List T)
  /-- `.tuple (List.replicate n x)`. -/
  | rep (n : Nat) (x : T)
  deriving Inhabited, BEq

partial def T.resolveN (s : List (String × T)) : Nat → T → T
  | 0, t => t
  | fuel + 1, .v n => match s.lookup n with
    | some t => T.resolveN s fuel t
    | none => .v n
  | _, .field c => .field c
  | fuel, .tuple xs => .tuple (xs.map (T.resolveN s fuel))
  | fuel, .ctor e c xs => .ctor e c (xs.map (T.resolveN s fuel))
  | fuel, .ptr x h => .ptr (T.resolveN s fuel x) (T.resolveN s fuel h)
  | fuel, .snoc h x => .snoc (T.resolveN s fuel h) (T.resolveN s fuel x)
  | fuel, .app f xs => .app f (xs.map (T.resolveN s fuel))
  | fuel, .rep n x => .rep n (T.resolveN s fuel x)

/-- Apply a path's substitution (a variable is replaced at most 10000 times deep). -/
def T.resolve (s : List (String × T)) (t : T) : T := T.resolveN s 10000 t

partial def T.mentions (n : String) : T → Bool
  | .v m => m == n
  | .field _ => false
  | .tuple xs | .ctor _ _ xs | .app _ xs => xs.any (T.mentions n)
  | .ptr x h | .snoc h x => T.mentions n x || T.mentions n h
  | .rep _ x => T.mentions n x

mutual
  partial def T.render : T → String
    | .v n => n
    | .field c => s!"(.field {c})"
    | .tuple xs => s!"(.tuple {list (xs.map T.render)})"
    | .ctor e c xs => s!"(.construct {e} {q c} {list (xs.map T.render)})"
    | .ptr x h => s!"(.ptr {T.tyOf x} ({T.render h}).length)"
    | .snoc h x => s!"({T.render h} ++ [{T.render x}])"
    | .app f xs => "(" ++ " ".intercalate (f :: xs.map T.render) ++ ")"
    | .rep n x => s!"(.tuple (List.replicate {n} {T.render x}))"

  /-- The `Value.type` of a term, in `simp only [Value.type]` normal form. -/
  partial def T.tyOf : T → String
    | .field _ => ".field"
    | .tuple xs => s!"(.tuple {list (xs.map T.tyOf)})"
    | .ctor e _ _ => s!"(.enum {e})"
    | .ptr x _ => s!"(.ptr {T.tyOf x})"
    | .rep n x => s!"(.tuple (List.map Value.type (List.replicate {n} ({T.render x} : SourceValue F))))"
    | t => s!"(Value.type ({T.render t} : SourceValue F))"
end

/-- A fact template: text and terms. -/
inductive Piece where
  | s (text : String)
  | t (term : T)
  deriving Inhabited

def renderPieces (sub : List (String × T)) (ps : List Piece) : String :=
  String.join (ps.map fun
    | .s x => x
    | .t x => (x.resolve sub).render)

/-- One entry of a call list: a recorded call, or a callee's own list. -/
inductive Seg where
  | call (name : String) (args : List T) (heap : T)
  | sub (name : String)

def renderSegs (sub : List (String × T)) : List Seg → String
  | [] => "[]"
  | [.call n args h] =>
    s!"[(⟨{n}, {list (args.map fun a => (a.resolve sub).render)}, {(h.resolve sub).render}⟩ : Call F)]"
  | [.sub c] => c
  | .call n args h :: rest =>
    s!"((⟨{n}, {list (args.map fun a => (a.resolve sub).render)}, {(h.resolve sub).render}⟩ : Call F) :: {renderSegs sub rest})"
  | .sub c :: rest => s!"({c} ++ {renderSegs sub rest})"

/-! ## Positions of names -/

/-- A 64-bit mixing step (the finalizer of MurmurHash3). -/
def mix64 (h : UInt64) : UInt64 :=
  let h := (h ^^^ (h >>> 33)) * 0xff51afd7ed558ccd
  let h := (h ^^^ (h >>> 33)) * 0xc4ceb9fe1a85ec53
  h ^^^ (h >>> 33)

/-- A string's hash: FNV-1a over its UTF-8 bytes, mixed. Written out here, so that the
names derived from it do not depend on the toolchain's `hash`. -/
def strHash (s : String) : UInt64 :=
  mix64 (s.toUTF8.data.foldl (fun h b => (h ^^^ b.toUInt64) * 1099511628211) 14695981039346656037)

def combine (a b : UInt64) : UInt64 :=
  mix64 (a * 0x9e3779b97f4a7c15 + b + 1)

/-- A position's key as the table writes it: sixteen hexadecimal digits. -/
def hex (h : UInt64) : String :=
  let ds := Nat.toDigits 16 h.toNat
  String.ofList (List.replicate (16 - ds.length) '0' ++ ds)

/-- Eight letters derived from a position: the suffix of a shown name the table does not have. -/
def letters (h : UInt64) : String :=
  String.ofList ((List.range 8).map fun i => Char.ofNat (97 + (h.toNat / 26 ^ i) % 26))

/-- One request for a name: the position's key, the base, the counter's suffix, the kind
(0: the function's counter; 1: the counter of the facts kept after the call equation; 2: a
segment's name, always shown), the inductive it belongs to (0: the function's paths; `i`: its
`i`-th segment), and the position in words (for `--explain` and for the messages). -/
structure Req where
  key : UInt64
  base : String
  sfx : String
  kind : Nat
  unit : Nat
  desc : String
  deriving Inhabited

/-! ## State -/

/-- What one path has established so far. -/
structure Path where
  /-- The arms selected so far in matches of several arms: a hash of their patterns' shapes
  in order (part of a name's position), and the same in words. -/
  ctx : UInt64 := 0
  ctxs : String := ""
  binders : Array (String × String) := #[]
  subst : List (String × T) := []
  /-- Field name, fact template, proof term, and a subject: the fact is dropped when
  its subject turns out to be a constructed value (it then says nothing). -/
  facts : Array (String × List Piece × String × Option T) := #[]
  /-- Hypotheses to normalize at the leaf. -/
  hyps : Array String := #[]
  tokens : Array String := #[]
  stored : Bool := false
  lemmas : Array String := #[]
  used : Array String := #[]
  /-- The path is impossible (a literal met a different literal); its goal is closed. -/
  dead : Bool := false
  /-- Facts kept after the call equation, so that the fields before it keep their positions:
  field name, fact template, proof term. -/
  late : Array (String × List Piece × String) := #[]
  deriving Inhabited

/-- A rendered constructor. -/
structure Ctor where
  name : String
  text : String

structure St where
  counter : Nat := 0
  path : Path := {}
  ctors : Array Ctor := #[]
  /-- Name lemmas: short name, statement. -/
  names : Array (String × String × String) := #[]
  /-- Name abbreviations: identifier, literal, and the instance it names. -/
  abbrevs : Array (String × String × String) := #[]
  /-- The variables a path never replaces: the parameters, `h`, `r`, `h'`, `calls`. -/
  params : List String := []
  src : Option (Aiur.Generic.Source F) := none
  maxPaths : Nat := 256
  /-- The type parameter of a generic function: its instance is `t_<name>`. -/
  typeParam : Option String := none
  /-- Inversion steps taken, against a budget. -/
  work : Nat := 0
  /-- Variable lookups weighted by the environment's length (each costs a `simp` over it). -/
  lookups : Nat := 0
  maxLookups : Nat := 3000
  /-- The function: its name, its Lean constant, its body (for positions). -/
  fname : String := ""
  leanName : String := ""
  body : Option (Expr F) := none
  /-- Whether `let`-bound matches are inverted as segments (`unsegmented`). -/
  segment : Bool := false
  /-- Segments generated so far: position, name, and rendered declarations. -/
  segs : Array (List Nat × String × String) := #[]
  /-- Inside a segment: no nested segments. -/
  inSeg : Bool := false
  /-- The names of the facts kept after the call equation (`Path.late`), numbered on their own so
  that the other names do not move. -/
  lateCounter : Nat := 0
  /-- The extended pass (`«f».PathX`, `«f».obsx`): the facts kept after the call equation are
  generated. Off, the paths are the unchanged `«f».Path`. -/
  late : Bool := false
  /-- A fact was kept after the call equation. -/
  lateUsed : Bool := false
  /-- The suffix of the extended pass's names (`X`). -/
  suffix : String := ""
  /-- Every request for a name in this pass, in order. -/
  trace : Array Req := #[]
  /-- How many names each place has been given under each base. -/
  ords : Std.HashMap UInt64 Nat := {}
  /-- The names that appear in a constructor, as `unit/kind/name`. -/
  shown : Std.HashSet String := {}
  /-- The names of the requests by index, when the pass is run again to rename. -/
  assigned : Option (Array String) := none
  /-- The inductive being generated: 0 the function's paths, `i` its `i`-th segment. -/
  unit : Nat := 0
  /-- A constructor that would have two fields of one name: the generation stops. -/
  fatal : Option String := none

abbrev M := StateT St (Except String)

/-- A name for the position `(arms selected, sc, base, how many before)`: the counter's
(`base ++ sfx`), or the one assigned to this request when the pass is run again. A segment's
name (kind 2) has the position of its `let` alone, and the same position in the extended pass,
where the name reads `SegX…`: the table's entry serves both. -/
def request (sc base sfx : String) (kind : Nat) : M String :=
  modifyGet fun s =>
    let ctx : UInt64 := if kind == 2 then 0 else s.path.ctx
    let h := combine (combine ctx (strHash sc)) (strHash base)
    let base := if kind == 2 then base ++ s.suffix else base
    -- the two collections are taken out of the state, so that they are updated in place
    let ords := s.ords
    let trace := s.trace
    let s := { s with ords := ∅, trace := #[] }
    let n := ords.getD h 0
    let name := match s.assigned with
      | some names => names.getD trace.size (base ++ sfx)
      | none => base ++ sfx
    let desc := s!"{s.path.ctxs} @ {sc} : {base} #{n}"
    (name, { s with
      ords := ords.insert h (n + 1),
      trace := trace.push { key := combine h n.toUInt64, base, sfx, kind, unit := s.unit, desc } })

def fresh (sc base : String) : M String := do
  let s ← get
  set { s with counter := s.counter + 1 }
  request sc base (toString s.counter) 0

def freshLate (sc base : String) : M String := do
  let s ← get
  set { s with lateCounter := s.lateCounter + 1 }
  request sc base (toString s.lateCounter) 1

def modifyPath (f : Path → Path) : M Unit :=
  modify fun s => { s with path := f s.path }

/-- A new path variable of a type. -/
def binder (sc base type : String) : M String := do
  let n ← fresh sc base
  modifyPath fun p => { p with binders := p.binders.push (n, type), used := p.used.push n }
  return n

/-- A binder named after a source variable, unique on the path. -/
def namedBinder (sc src type : String) : M String := do
  let base := "x_" ++ src
  let p := (← get).path
  let taken := (← get).params.contains base || p.used.contains base
  let n ← if taken then fresh sc (base ++ "_") else pure base
  modifyPath fun p => { p with binders := p.binders.push (n, type), used := p.used.push n }
  return n

def isParam (n : String) : M Bool := return (← get).params.contains n

def resolveT (t : T) : M T := return t.resolve (← get).path.subst

def addFact (name : String) (fact : List Piece) (proof : String) (hyp : Bool := true)
    (subject : Option T := none) : M Unit :=
  modifyPath fun p =>
    let hyps := if hyp then p.hyps.push name else p.hyps
    { p with facts := p.facts.push (name, fact, proof, subject), hyps := hyps }

def isDead : M Bool := return (← get).path.dead

def useLemma (l : String) : M Unit :=
  modifyPath fun p => if p.lemmas.contains l then p else { p with lemmas := p.lemmas.push l }

/-- Bind a destination: a path variable takes the term, a parameter gets an
equation proved by `rfl` (Lean has substituted it). -/
def assign (sc : String) (dest t : T) : M Unit := do
  match ← resolveT dest with
  | .v n =>
    if ← isParam n then
      let f ← fresh sc "he"
      addFact f [.s s!"{n} = ", .t t] "rfl" false
    else
      if (← resolveT t).mentions n then throw "cyclic assignment"
      modifyPath fun p => { p with subst := (n, t) :: p.subst }
  | _ => throw "destination is not a variable"

/-- A pattern's template for a scrutinee: a path variable is replaced (Lean:
`subst`), a parameter keeps its equation as a fact. -/
def unifyPat (V tmpl : T) (hv : String) : M (List String) := do
  match ← resolveT V with
  | .v n =>
    if ← isParam n then
      addFact hv [.s s!"{n} = ", .t tmpl] hv
      return []
    else
      if (← resolveT tmpl).mentions n then throw "cyclic template"
      modifyPath fun p => { p with subst := (n, tmpl) :: p.subst }
      return [s!"subst {hv}"]
  | Vc =>
    match Vc, ← resolveT tmpl with
    | .field a, .field b =>
      if a == b then return [s!"clear {hv}"]
      modifyPath fun p => { p with dead := true }
      return [s!"exact absurd (Value.field.inj {hv}) (by decide)"]
    | _, _ => throw "concrete scrutinee"

/-! ## Names -/

/-- How a name appears in statements: short ones as literals, long ones (the
JSON symbols of generic instances) by an abbreviation named after the instance. -/
def nameTerm (lit pretty inst : String) : M String := do
  if lit.length ≤ 48 && !lit.startsWith "$" then return q lit
  let s ← get
  unless s.abbrevs.any (·.1 == pretty) do
    set { s with abbrevs := s.abbrevs.push (pretty, lit, inst) }
  return s!"Names.«{pretty}»"

/-- A name lemma `lhs = name`, proved by the kernel; returns the name's term and
the lemma's name. -/
def nameLemma (lhs lit pretty inst : String) : M (String × String) := do
  let term ← nameTerm lit pretty inst
  let n := s!"n{(hash lhs).toNat}"
  let s ← get
  unless s.names.any (·.1 == n) do
    set { s with names := s.names.push (n, s!"{lhs} = {term}", "by decide +kernel") }
  return (term, s!"Names.{n}")

/-- A type in the source's notation. -/
partial def tyStr : Ty → String
  | .param p => p
  | .field => "Field"
  | .tuple ts => "(" ++ ", ".intercalate (ts.map tyStr) ++ ")"
  | .array t n => s!"[{tyStr t}; {n}]"
  | .ptr t => "&" ++ tyStr t
  | .named n [] => n
  | .named n args => n ++ "<" ++ ", ".intercalate (args.map tyStr) ++ ">"

partial def closed : Ty → Bool
  | .param _ => false
  | .field => true
  | .tuple ts => ts.all closed
  | .array t _ => closed t
  | .ptr t => closed t
  | .named _ args => args.all closed

/-- An instance name (call, constructor expression): the string and the lemma
that normalizes `instanceName [] name args` to it. -/
def instName (name : String) (args : Option (List Ty)) : M (String × String) := do
  match args, (← get).typeParam with
  | none, _ => return (q name, "instanceName_plain_none")
  | some [], _ => return (q name, "instanceName_plain_some")
  | some [.param p], some tp =>
    unless p == tp do throw s!"generic instance {name}"
    return (s!"(Instance.mk {q name} [t_{tp}]).symbol", "instanceName_some_one, subst_param_singleton")
  | some _, some _ => throw s!"generic instance {name}"
  | some ts, none =>
    unless ts.all closed do throw s!"generic instance {name}"
    let lit := instanceName [] name (some ts)
    nameLemma s!"instanceName [] {q name} (some {list (ts.map ty)})" lit
      (name ++ "<" ++ ", ".intercalate (ts.map tyStr) ++ ">") s!"Instance.mk {q name} {list (ts.map ty)}"

/-- A pattern's constructor name, and the lemma normalizing `constructorName [] t`. -/
def ctorName (t : Ty) : M (String × String) := do
  if let some tp := (← get).typeParam then
    match t with
    | .named n [.param p] =>
      unless p == tp do throw "generic constructor pattern"
      return (s!"(Instance.mk {q n} [t_{tp}]).symbol",
        "constructorName_named, instanceName_some_one, subst_param_singleton")
    | _ => throw "generic constructor pattern"
  unless closed t do throw "generic constructor pattern"
  let lit := constructorName [] t
  let inst := match t with
    | .named n args => s!"Instance.mk {q n} {list (args.map ty)}"
    | _ => ""
  nameLemma s!"constructorName [] {ty t}" lit (tyStr t) inst

/-- A literal constant: its value, and the name of its lookup fact (proved once, by
the kernel, in the names module). -/
def constField (n : String) (t : Ty) : M (String × String) := do
  let some src := (← get).src | throw "no source"
  unless (← get).typeParam.isNone do throw "constant in a generic function"
  match src.world.constant n (t.subst []) with
  | .ok (.literal c) =>
    let stmt := s!"W.constant {q n} (Generic.Ty.subst [] {ty t}) = .ok (.literal ({field c} : F))"
    let l := s!"c{(hash stmt).toNat}"
    let s ← get
    unless s.names.any (·.1 == l) do
      set { s with names := s.names.push (l, stmt, "eq_of_isLiteral (by decide +kernel)") }
    return (field c, s!"Names.{l}")
  | _ => throw s!"const {n} is not a literal"

/-- A constant pattern: its value and a `MatchesConst` proof. -/
partial def constPat? : Pattern F → M (Option (T × String))
  | .literal c => return some (.field (field c), s!"MatchesConst.literal {field c}")
  | .global n (some t) => do
    let (c, l) ← constField n t
    return some (.field c, s!"MatchesConst.global {l}")
  | .tuple ps => do
    let mut items := #[]
    for p in ps do
      match ← constPat? p with
      | some x => items := items.push x
      | none => return none
    let prf := items.toList.foldr (fun (_, hp) acc => s!".cons ({hp}) ({acc})") ".nil"
    return some (.tuple (items.toList.map (·.1)), s!"MatchesConst.tuple ({prf})")
  | .array ps => do
    let mut items := #[]
    for p in ps do
      match ← constPat? p with
      | some x => items := items.push x
      | none => return none
    let prf := items.toList.foldr (fun (_, hp) acc => s!".cons ({hp}) ({acc})") ".nil"
    return some (.tuple (items.toList.map (·.1)), s!"MatchesConst.array ({prf})")
  | _ => return none

def patKind : Pattern F → String
  | .literal _ => "literal" | .wildcard => "wildcard" | .bind _ => "bind"
  | .global _ _ => "global" | .load _ => "load" | .orElse _ _ _ => "or"
  | .tuple _ => "tuple" | .array _ => "array" | .repeat _ _ => "repeat"
  | .record _ _ => "record" | .construct _ _ _ => "construct" | .constructAs _ _ _ _ => "constructAs"

def isFlat : Pattern F → Bool
  | .bind _ | .wildcard => true
  | _ => false

partial def armToken : Pattern F → String
  | .construct _ c _ => c
  | .literal c => s!"n{c.val}"
  | .wildcard => "other"
  | .bind _ => "bind"
  | .tuple ps => "_".intercalate (ps.map armToken)
  | .global n _ => (n.splitOn "::").getLast!
  | .load p => armToken p
  | _ => "arm"

def sanitize (s : String) : String :=
  let cs := s.toList.map fun c => if c.isAlphanum || c == '_' then c else '_'
  let s := String.ofList cs
  if s.isEmpty then "run" else if s.front.isDigit then "c" ++ s else s

def bullet : List String → List String
  | [] => []
  | l :: ls => ("· " ++ l) :: ls.map ("  " ++ ·)

def uniqueName (taken : Array String) (base : String) : String := Id.run do
  if !taken.contains base then return base
  for i in [1:100000] do
    if !taken.contains s!"{base}_{i}" then return s!"{base}_{i}"
  return base

/-! ## Places in the body

A place is a string: the chain of enclosing nodes, each by its tag. The statements of a block
(`let`s and matches of one arm, whose bodies are the rest of the block) are siblings: each is
tagged by what it binds (`stmtTag`), so that a statement keeps its place when another is added
or removed before it.

**The format.** The table of names is keyed by positions, and a position is a hash of
strings built here. Each of the following is part of the format: changing it moves positions,
the table then has no entry for them, and their names are derived anew (the generation reports
the function as renamed, `--check` reports its files stale). The table cannot be written again
once derived names are in use, so all of this is fixed:

* `strHash`, `mix64`, `combine`, and how `request` combines the arms selected, the place, the
  base and the ordinal; `hex` (the table's keys) and `letters` (the derived suffixes);
* the tags: `placeTag`, `stmtTag`, `patShape`, `patText`, `patBinds`, `nodeTag`, `anchor`,
  `deep`, `blockTags`, `blockDups`, with what they print through `ProofGen.field` (a field
  element), `tyStr` (a type) and `patKind`, and with the order of `Expr.children`;
* the place strings built in `inv`, `invIn`, `invArgs`, `invArms`, `negArm`, `mixedNeg`,
  `patInv`, `subBinders`, `listInv`, `listInvConcrete`, `letSegment`, `genSegment` and `leaf`
  (`/`, `/l`, `/r`, `/on`, `/pat`, `/*`, `/seg`, `/leaf`, `/end`, `/call`, `/arm …`, the
  indices of operands and of a pattern's components);
* every base string (`ev`, `hv`, `m`, `x_<variable>_`, `Seg`, …), and the number and the order
  of the requests of one base at one place (the two `he` of a tail, one `v` for each argument
  of a call);
* a segment's name has one position for the plain and the extended pass: the place of its
  `let`, without the arms selected, under the base `Seg` (`request`, kind 2). The extended
  pass reads the same entry of the table and writes the name with `X` (`Seg1`, `SegX1`);
* an extended pass that keeps no fact after a call equation is not used (`function`), and its
  names are not assigned (`functionPass`): the table has entries of an extended pass only
  where the extended lemma is generated (its `hnt` facts);
* which matches select an arm (those of several arms) and which `let`s are segments
  (`segmentable`);
* the source language's lowering, as far as it decides the tree the tags are read from (a
  statement `e;` is a `let` whose pattern binds nothing; a destructuring `match` has one arm).

**What moves a name, by design.**

* A statement gains or loses a sibling with its tag: the hash of its content joins or leaves
  the tag. That renames the statement's own names, those of its bound expression and, for a
  `let` bound to a match of several arms, the segment and its names.
* A statement that contains a match of several arms which is not a segment (in a generic
  function, inside a segment, in an operand) is added or removed: the arm selected is part of
  every later position on the path.
* A pattern binds a variable name that a later pattern of the path also binds: the later
  binder is `x_<name>_<suffix>` instead of `x_<name>`, or the reverse.
* Statements of a block that are equal in pattern and content are told apart by order.
* A match of one arm becomes a match of several: its own names, the rest of the block and
  what follows it move.
* A `let`-bound variable is renamed: the statement is another statement (its own names, its
  bound expression's, its segment). So is a pattern of several components when one of its
  variables is renamed, or one of its `_` is bound.
* A statement that binds nothing is tagged by what it evaluates (`anchor`): another callee,
  or another variable or literal on a side of an assertion, makes it another statement.
* A call's callee is replaced: the call's own names (`ev`, `cs`, `m`, the values of its
  arguments) are another call's. Its operands keep their places.
* A match reaches `tableArms` arms: on a scrutinee that is a parameter, a matched arm no
  longer keeps the facts `hne` of the arms before it.
* Constructor names are not requests: paths with the same arm tokens are told apart by `_1`,
  `_2`, … in the order of the walk (`uniqueName`). -/

/-- A pattern without its variables' names: an arm keeps its place when a variable is renamed. -/
partial def patShape : Pattern F → String
  | .literal c => field c
  | .wildcard | .bind _ => "_"
  | .global n _ => n
  | .load p => "*" ++ patShape p
  | .tuple ps => "(" ++ ", ".intercalate (ps.map patShape) ++ ")"
  | .array ps => "[" ++ ", ".intercalate (ps.map patShape) ++ "]"
  | .construct t c ps | .constructAs _ t c ps =>
    tyStr t ++ "." ++ c ++ "(" ++ ", ".intercalate (ps.map patShape) ++ ")"
  | p => patKind p

/-- A pattern with its variables' names. -/
partial def patText : Pattern F → String
  | .bind n => n
  | .load p => "*" ++ patText p
  | .tuple ps => "(" ++ ", ".intercalate (ps.map patText) ++ ")"
  | .array ps => "[" ++ ", ".intercalate (ps.map patText) ++ "]"
  | .construct t c ps | .constructAs _ t c ps =>
    tyStr t ++ "." ++ c ++ "(" ++ ", ".intercalate (ps.map patText) ++ ")"
  | p => patShape p

/-- Whether a pattern binds a variable. -/
partial def patBinds : Pattern F → Bool
  | .bind _ => true
  | .load p => patBinds p
  | .tuple ps | .array ps => ps.any patBinds
  | .construct _ _ ps | .constructAs _ _ _ ps => ps.any patBinds
  | .orElse l r _ => patBinds l || patBinds r
  | .repeat p _ => patBinds p
  | .record _ ps => ps.any patBinds
  | _ => false

/-- A node's own tag, without its operands. -/
def nodeTag : Expr F → String
  | .literal c => s!"lit {field c}"
  | .var n => s!"var {n}"
  | .global n _ => s!"global {n}"
  | .tuple _ => "tuple"
  | .array _ => "array"
  | .repeat _ n => s!"repeat {n}"
  | .index _ i => s!"index {i}"
  | .slice _ a _ => s!"slice {a}"
  | .construct n _ c _ => s!"new {n}.{c}"
  | .constructAs _ t c _ => s!"new {tyStr t}.{c}"
  | .record _ _ => "record"
  | .member _ f => s!"member {f.name}"
  | .update _ _ => "update"
  | .builtin (.assertEq _) _ => "assert"
  | .builtin (.ascribe _) _ => "ascribe"
  | .builtin (.debug _) _ => "debug"
  | .project _ i => s!"project {i}"
  | .letValue _ _ _ => "let"
  | .store _ => "store"
  | .load _ => "load"
  | .hint _ _ _ => "hint"
  | .neg _ => "neg"
  | .binary .add _ _ => "add"
  | .binary .sub _ _ => "sub"
  | .binary .mul _ _ => "mul"
  | .binary .div _ _ => "div"
  | .call n _ _ => s!"call {n}"
  | .matchValue _ _ => "match"
  | .control _ _ => "control"

/-- What a statement that binds nothing evaluates, as far as it tells the statement from its
neighbours: a call's callee, an assertion's two sides by their tags. -/
def anchor : Expr F → String
  | .builtin (.assertEq _) es => "assert(" ++ ", ".intercalate (es.map nodeTag) ++ ")"
  | .matchValue x _ => "match " ++ nodeTag x
  | e => nodeTag e

/-- A statement's tag: what it binds. A variable by its name; a pattern of several components
by the pattern with its variables' names; a pattern that binds nothing by its shape and by
what it is bound to (`anchor`). Binding a variable or a pattern's variables to another
expression leaves the tag. -/
def stmtTag (kind : String) (p : Pattern F) (x : Expr F) : String :=
  match p with
  | .bind n => s!"{kind} {n}"
  | _ => if patBinds p then s!"{kind} {patText p}" else s!"{kind} {patShape p} = {anchor x}"

/-- A statement of a block: its tag, its pattern, what the pattern is bound to, and the rest of
the block. -/
def stmt? : Expr F → Option (String × Pattern F × Expr F × Expr F)
  | .letValue p x b => some (stmtTag "let" p x, p, x, b)
  | .matchValue x [(p, b)] => some (stmtTag "match" p x, p, x, b)
  | _ => none

/-- The tags of the statements of the block that `e` heads, in order. -/
partial def blockTags (e : Expr F) : List String :=
  match stmt? e with
  | some (t, _, _, b) => t :: blockTags b
  | none => []

/-- The tags that several statements of the block share. -/
def blockDups (e : Expr F) : List String :=
  let ts := blockTags e
  (ts.filter fun t => ts.count t > 1).eraseDups

/-- An expression in full: statements by what they bind, matches by their arms' shapes. -/
partial def deep (e : Expr F) : String :=
  let own := match e with
    | .letValue p _ _ => "let " ++ patShape p
    | .matchValue _ arms => "match [" ++ " | ".intercalate (arms.map fun (p, _) => patShape p) ++ "]"
    | e => nodeTag e
  own ++ "(" ++ ", ".intercalate (e.children.map deep) ++ ")"

/-- A node's tag in its place. A statement has its statement tag; where several statements of
the block share that tag (`dups`), each also a hash of its pattern with the variables' names
and of what the pattern is bound to, in full: they are told apart by content, not by order,
unless they are equal. A variable, a literal or a constant is tagged by its kind alone: the
names at a block's tail stand when the tail is another variable or value. -/
def placeTag (dups : List String) (e : Expr F) : String :=
  match stmt? e with
  | some (t, p, x, _) =>
    if dups.contains t then s!"{t} [{hex (strHash (patText p ++ " = " ++ deep x))}]" else t
  | none =>
    match e with
    | .var _ => "var"
    | .literal _ => "lit"
    | .global _ _ => "global"
    | e => nodeTag e

/-- The leaf: the call list's equation, then the path's constructor (of the inductive `ind`). -/
def leaf (sc ind : String) (segs : List Seg) : M (List String) := do
  let hcName ← fresh (sc ++ "/leaf") "hc"
  let s ← get
  if s.ctors.size ≥ s.maxPaths then throw "too many paths"
  if s.path.facts.size > 150 then throw "too many facts on a path"
  let p := s.path
  let lemmas := ["List.append_assoc", "List.cons_append", "List.nil_append", "List.append_nil",
    "instanceName_plain_none", "instanceName_plain_some"] ++ p.lemmas.toList
  let callsT := renderSegs p.subst segs
  let kept := p.facts.filter fun (_, _, _, subj) => match subj with
    | some v => match v.resolve p.subst with | .v _ => true | _ => false
    | none => true
  -- an equation whose two sides are one term under the path's substitution (an assertion
  -- on a value that a later arm fixed): the normalization below rewrites its hypothesis to
  -- `True`, so the field is proved by `rfl`
  let kept := kept.map fun (n, f, pr, subj) => match f with
    | [.s "(", .t a, .s " : SourceValue F) = ", .t b] =>
      if p.stored && a.resolve p.subst == b.resolve p.subst then (n, f, "rfl", subj)
      else (n, f, pr, subj)
    | _ => (n, f, pr, subj)
  let p := { p with facts := kept.push (hcName, [.s s!"calls = {callsT}"],
    s!"(by first | rfl | simp only [{", ".intercalate lemmas.eraseDups}])", none) }
  let binders := p.binders.toList.filter fun (n, _) => (p.subst.lookup n).isNone
  -- the constructor's name: the arm tokens, made unique
  let base := sanitize ("_".intercalate p.tokens.toList)
  let name := uniqueName (s.ctors.map (·.name)) base
  let fields := (p.facts.toList.map fun (n, f, _, _) => s!"({n} : {renderPieces p.subst f})")
    ++ (p.late.toList.map fun (n, f, _) => s!"({n} : {renderPieces p.subst f})")
  let bs := binders.map fun (n, t) => s!"({n} : {t})"
  let text := s!"  | {name}" ++
    (if bs.isEmpty then "" else "\n      " ++ " ".intercalate bs) ++
    String.join (fields.map ("\n      " ++ ·))
  -- what the constructor shows: its binders, its facts
  let unit := s.unit
  let shown := binders.foldl (fun acc (n, _) => acc.insert s!"{unit}/0/{n}") s.shown
  let shown := p.facts.foldl (fun acc (n, _, _, _) => acc.insert s!"{unit}/0/{n}") shown
  let shown := p.late.foldl (fun acc (n, _, _) => acc.insert s!"{unit}/1/{n}") shown
  -- a constructor never has two fields of one name
  let dup := ((binders.map (·.1) ++ p.facts.toList.map (·.1) ++ p.late.toList.map (·.1)).foldl
    (fun (acc : Std.HashSet String × Option String) n =>
      if acc.1.contains n then (acc.1, if acc.2.isSome then acc.2 else some n)
      else (acc.1.insert n, acc.2))
    (∅, none)).2
  let fatal := match s.fatal, dup with
    | some m, _ => some m
    | none, some n => some s!"constructor `{name}` of `{ind}` would have two fields named `{n}`"
    | none, none => none
  modify fun s => { s with ctors := s.ctors.push { name, text }, shown := shown, fatal := fatal }
  let norm := if p.stored then
      let hs := p.hyps.toList
      [s!"try simp only [Value.type, List.map_cons, List.map_nil] at {" ".intercalate hs} ⊢"]
    else []
  let holes := String.join (binders.map fun _ => " _")
  let proofs := String.join (p.facts.toList.map fun (_, _, pr, _) => " " ++ pr) ++
    String.join (p.late.toList.map fun (_, _, pr) => " " ++ pr)
  return norm ++ [s!"exact {ind}.{name}{holes}{proofs}"]

/-! ## Inversion -/

abbrev Env := List (String × T)

abbrev K := List Seg → M (List String)

/-- A match of at least this many arms is a table (`invArms`). -/
def tableArms : Nat := 16

/-- **Segments.** In a monomorphic function, a `let` bound to a match of several arms is
inverted by a theorem of its own: the match's paths become an inductive (`«f».Seg<i>`,
with its theorem `«f».seg<i>`), and the function's paths continue once after it, with
the fact `«f».Seg<i> env h v m cs`, instead of once per arm. The functions listed here
are inverted without segments. -/
def unsegmented : List String := []

/-- A `let`-bound match of several arms, outside any segment, in a monomorphic function
whose `let`-bound matches are segmented. -/
def segmentable (x : Expr F) : M Bool := do
  let s ← get
  unless s.segment && !s.inSeg && s.typeParam.isNone && s.body.isSome do return false
  match x with
  | .matchValue _ arms => return arms.length ≥ 2
  | _ => return false

mutual
  /-- Invert derivation `d` of `e` (input heap `hin`; destinations `dv`, `dh`),
  then continue with the call segments. -/
  partial def inv (sc0 : String) (e : Expr F) (d : String) (env : Env) (hin dv dh : T) (k : K) :
      M (List String) :=
    invIn (blockDups e) sc0 e d env hin dv dh k

  /-- `inv` inside a block: `dups` are the tags that several of the block's statements share,
  `sc0` is the block's place. -/
  partial def invIn (dups : List String) (sc0 : String) (e : Expr F) (d : String) (env : Env)
      (hin dv dh : T) (k : K) : M (List String) := do
    let s ← get
    if s.work ≥ 20000 then throw "too large"
    set { s with work := s.work + 1 }
    -- the node's place; a statement's body continues in the block's place `sc0`
    let sc := sc0 ++ "/" ++ placeTag dups e
    let fresh := fresh sc
    let binder := binder sc
    let assign := assign sc
    match e with
    | .var n =>
      let some t := env.lookup n | throw s!"unbound variable {n}"
      let s ← get
      if s.lookups + env.length > s.maxLookups then throw "too costly (variable lookups)"
      set { s with lookups := s.lookups + env.length }
      let l ← fresh "l"
      assign dv t
      assign dh hin
      return [s!"obtain ⟨{l}, rfl, rfl⟩ := {d}.var_inv", s!"simp at {l}", s!"subst {l}"] ++ (← k [])
    | .literal c =>
      assign dv (.field (field c))
      assign dh hin
      return [s!"obtain ⟨rfl, rfl, rfl⟩ := {d}.literal_inv"] ++ (← k [])
    | .global n (some t) =>
      let (c, l) ← constField n t
      assign dv (.field c)
      assign dh hin
      return [s!"obtain ⟨rfl, rfl, rfl⟩ := {d}.global_literal_inv {l}"] ++ (← k [])
    | .tuple es | .array es =>
      let vs ← fresh "vs"; let a ← fresh "a"
      let items ← es.mapM fun _ => binder "v" "SourceValue F"
      assign dv (.tuple (items.map .v))
      let lem := match e with | .tuple _ => "tuple_inv" | _ => "array_inv"
      return [s!"obtain ⟨{vs}, {a}, rfl⟩ := {d}.{lem}"] ++ (← invArgs sc 0 es a env hin items dh k)
    | .construct name targs ctor es =>
      let (lit, lem) ← instName name targs
      let vs ← fresh "vs"; let a ← fresh "a"; let hr ← fresh "hres"
      let items ← es.mapM fun _ => binder "v" "SourceValue F"
      assign dv (.ctor lit ctor (items.map .v))
      return [s!"obtain ⟨{vs}, {a}, {hr}⟩ := {d}.construct_inv", s!"rw [{lem}] at {hr}",
        s!"subst {hr}"] ++ (← invArgs sc 0 es a env hin items dh k)
    | .constructAs _ t ctor es =>
      let (lit, lem) ← ctorName t
      let vs ← fresh "vs"; let a ← fresh "a"; let hr ← fresh "hres"
      let items ← es.mapM fun _ => binder "v" "SourceValue F"
      assign dv (.ctor lit ctor (items.map .v))
      return [s!"obtain ⟨{vs}, {a}, {hr}⟩ := {d}.constructAs_inv", s!"rw [{lem}] at {hr}",
        s!"subst {hr}"] ++ (← invArgs sc 0 es a env hin items dh k)
    | .store x =>
      let v ← binder "v" "SourceValue F"; let m ← binder "m" "Heap F"; let d' ← fresh "d"
      let hm ← fresh "hm"
      assign dv (.ptr (.v v) (.v m))
      -- the grown heap stays a variable, with its equation (rendering it would nest heaps)
      match ← resolveT dh with
      | .v n => addFact hm [.s s!"{n} = ", .t (.snoc (.v m) (.v v))] hm
      | _ => throw "store destination is not a variable"
      modifyPath fun p => { p with stored := true }
      return [s!"obtain ⟨{v}, {m}, {d'}, rfl, {hm}⟩ := {d}.store_inv"] ++
        (← inv sc x d' env hin (.v v) (.v m) k)
    | .load x =>
      let p ← binder "p" "SourceValue F"; let d' ← fresh "d"; let ld ← fresh "ld"
      let rest ← inv sc x d' env hin (.v p) dh fun segs => do
        addFact ld [.s "loadValue ", .t dh, .s " ", .t (.v p), .s " = .ok ", .t dv] ld
        k segs
      return [s!"obtain ⟨{p}, {d'}, {ld}⟩ := {d}.load_inv"] ++ rest
    | .call name targs es =>
      let (lit, lem) ← instName name targs
      useLemma lem
      let vs ← fresh "vs"; let m ← binder "m" "Heap F"; let c1 ← fresh "c"
      let c2 ← binder "cs" "List (Call F)"; let a ← fresh "a"; let ev ← fresh "ev"
      let items ← es.mapM fun _ => binder "v" "SourceValue F"
      -- the operands' places do not name the callee: they stand when it is replaced
      let rest ← invArgs (sc0 ++ "/call") 0 es a env hin items (.v m) fun s1 => do
        let argPieces : List Piece :=
          ((items.map fun i => [Piece.t (.v i)]).intersperse [Piece.s ", "]).flatten
        addFact ev ([.s s!"ObsFn W {lit} ["] ++ argPieces ++
          [.s "] ", .t (.v m), .s " ", .t dv, .s " ", .t dh, .s s!" {c2}"]) ev
        k (s1 ++ [.call lit (items.map .v) (.v m), .sub c2])
      return [s!"obtain ⟨{vs}, {m}, {c1}, {c2}, {a}, {ev}, rfl⟩ := {d}.call_inv",
        s!"rw [{lem}] at {ev}"] ++ rest
    | .binary op l r =>
      let x ← binder "x" "SourceValue F"; let y ← binder "y" "SourceValue F"
      let m ← binder "m" "Heap F"
      let c1 ← fresh "c"; let c2 ← fresh "c"; let dl ← fresh "d"; let dr ← fresh "d"
      let o ← fresh "op"
      let opName := match op with
        | .add => ".add" | .sub => ".sub" | .mul => ".mul" | .div => ".div"
      let rest ← inv (sc ++ "/l") l dl env hin (.v x) (.v m) fun s1 =>
        inv (sc ++ "/r") r dr env (.v m) (.v y) dh fun s2 => do
          addFact o [.s s!"evalBinOp {opName} (", .t (.v x), .s " : SourceValue F) (", .t (.v y),
            .s " : SourceValue F) = .ok ", .t dv] o
          k (s1 ++ s2)
      return [s!"obtain ⟨{x}, {y}, {m}, {c1}, {c2}, {dl}, {dr}, {o}, rfl⟩ := {d}.binary_inv"] ++ rest
    | .builtin op es =>
      let vs ← fresh "vs"; let a ← fresh "a"; let ap ← fresh "ap"
      let items ← es.mapM fun _ => binder "v" "SourceValue F"
      let rest ← invArgs sc 0 es a env hin items dh fun segs => do
        match op, items with
        | .ascribe _, [x] =>
          let eq ← fresh "eq"
          assign dv (.v x)
          return [s!"have {eq} := Builtin.ascribe_inv {ap}", s!"subst {eq}"] ++ (← k segs)
        | .debug _, _ =>
          let eq ← fresh "eq"
          assign dv (.tuple [])
          return [s!"have {eq} := Builtin.debug_inv {ap}", s!"subst {eq}"] ++ (← k segs)
        | .assertEq _, [x, y] =>
          let eq ← fresh "heq"
          addFact eq [.s "(", .t (.v x), .s " : SourceValue F) = ", .t (.v y)] eq
          assign dv (.tuple [])
          return [s!"obtain ⟨{eq}, rfl⟩ := Builtin.assertEq_inv {ap}"] ++ (← k segs)
        | _, _ => throw "builtin arity"
      return [s!"obtain ⟨{vs}, {a}, {ap}⟩ := {d}.builtin_inv"] ++ rest
    | .index x i | .project x i =>
      let p ← binder "p" "SourceValue F"; let d' ← fresh "d"; let pr ← fresh "pr"
      let lem := match e with | .index _ _ => "index_inv" | _ => "project_inv"
      let rest ← inv sc x d' env hin (.v p) dh fun segs => do
        addFact pr [.s "projectValue (", .t (.v p), .s s!" : SourceValue F) {i} = .ok ", .t dv] pr
        k segs
      return [s!"obtain ⟨{p}, {d'}, {pr}⟩ := {d}.{lem}"] ++ rest
    | .slice x a b =>
      let p ← binder "p" "SourceValue F"; let d' ← fresh "d"; let pr ← fresh "sl"
      let bs := match b with | some n => s!"(some {n})" | none => "none"
      let rest ← inv sc x d' env hin (.v p) dh fun segs => do
        addFact pr [.s "sliceValue (", .t (.v p), .s s!" : SourceValue F) {a} {bs} = .ok ", .t dv] pr
        k segs
      return [s!"obtain ⟨{p}, {d'}, {pr}⟩ := {d}.slice_inv"] ++ rest
    | .member x f =>
      let p ← binder "p" "SourceValue F"; let d' ← fresh "d"; let pr ← fresh "mb"
      let rest ← inv sc x d' env hin (.v p) dh fun segs => do
        addFact pr [.s s!"memberValue [] {fieldRef f} (", .t (.v p), .s " : SourceValue F) = .ok ", .t dv] pr
        k segs
      return [s!"obtain ⟨{p}, {d'}, {pr}⟩ := {d}.member_inv"] ++ rest
    | .neg x =>
      let p ← binder "p" "SourceValue F"; let d' ← fresh "d"; let pr ← fresh "ng"
      let rest ← inv sc x d' env hin (.v p) dh fun segs => do
        addFact pr [.s "evalNeg (", .t (.v p), .s " : SourceValue F) = .ok ", .t dv] pr
        k segs
      return [s!"obtain ⟨{p}, {d'}, {pr}⟩ := {d}.neg_inv"] ++ rest
    | .repeat x n =>
      let p ← binder "v" "SourceValue F"; let d' ← fresh "d"
      assign dv (.rep n (.v p))
      return [s!"obtain ⟨{p}, {d'}, rfl⟩ := {d}.repeat_inv"] ++ (← inv sc x d' env hin (.v p) dh k)
    | .update paths es =>
      let vs ← fresh "vs"; let a ← fresh "a"; let up ← fresh "up"
      let items ← es.mapM fun _ => binder "v" "SourceValue F"
      let ps := list (paths.map fun p => list (p.map updateStep))
      let rest ← invArgs sc 0 es a env hin items dh fun segs => do
        addFact up ([.s s!"Update.value [] {ps} ["] ++
          ((items.map (fun i => [Piece.t (.v i)])).intersperse [.s ", "]).flatten ++
          [.s "] = .ok ", .t dv]) up
        k segs
      return [s!"obtain ⟨{vs}, {a}, {up}⟩ := {d}.update_inv"] ++ rest
    | .hint t key _ =>
      unless closed t do throw "generic hint"
      let x ← binder "x" "SourceValue F"; let c ← binder "k" "Constant F"
      let d' ← fresh "d"; let tp ← fresh "ty"
      assign dv (.app "Constant.toValue" [.v c])
      let rest ← inv sc key d' env hin (.v x) dh fun segs => do
        addFact tp [.s s!"W.typed (Generic.Ty.toCore (Generic.Ty.subst [] {ty t})) ", .t (.v c),
          .s " = true"] tp
        k segs
      return [s!"obtain ⟨{x}, {c}, {d'}, {tp}, rfl⟩ := {d}.hint_inv"] ++ rest
    | .letValue pat x b =>
      if ← segmentable x then return ← letSegment dups sc0 sc e pat x b d env hin dv dh k
      let v ← binder "v" "SourceValue F"; let m ← binder "m" "Heap F"
      let bs ← fresh "bs"; let c1 ← fresh "c"; let c2 ← fresh "c"
      let dx ← fresh "d"; let mt ← fresh "mt"; let db ← fresh "d"
      let rest ← inv sc x dx env hin (.v v) (.v m) fun s1 => do
        let (pl, binds) ← patInv (sc ++ "/pat") (.v v) pat mt (.v m)
        if ← isDead then return pl
        return pl ++ (← invIn dups sc0 b db (binds ++ env) (.v m) dv dh fun s2 => k (s1 ++ s2))
      return [s!"obtain ⟨{v}, {m}, {bs}, {c1}, {c2}, {dx}, {mt}, {db}, rfl⟩ := {d}.letValue_inv"] ++ rest
    | .matchValue x arms =>
      let v ← binder "v" "SourceValue F"; let m ← binder "m" "Heap F"
      let bs ← fresh "bs"; let body ← fresh "body"; let c1 ← fresh "c"; let c2 ← fresh "c"
      let dx ← fresh "d"; let sel ← fresh "sel"; let db ← fresh "d"
      let rest ← inv (sc ++ "/on") x dx env hin (.v v) (.v m) fun s1 =>
        invArms dups sc0 sc arms (arms.length > 1) (arms.length ≥ tableArms) sel db env (.v v) (.v m) dv dh
          fun s2 => k (s1 ++ s2)
      return [s!"obtain ⟨{v}, {m}, {bs}, {body}, {c1}, {c2}, {dx}, {sel}, {db}, rfl⟩ := {d}.matchValue_inv"] ++
        rest
    | .global _ none => throw "unannotated global"
    | .record _ _ => throw "record expression"
    | .control _ _ => throw "control"

  /-- `let pat = x; b` with `x` a match: the derivation of `x` is inverted by the
  segment's theorem (generated once per position), and `b` once, after it. The
  segment is stated over the whole local environment, entry by entry, in the
  evaluation's order (`bindings ++ locals`, as the generator's `binds ++ env`), so
  that the derivation of `x` instantiates it by unification alone. -/
  partial def letSegment (dups : List String) (sc0 sc : String) (e : Expr F) (pat : Pattern F) (x b : Expr F) (d : String)
      (env : Env) (hin dv dh : T) (k : K) : M (List String) := do
    let fresh := fresh sc
    let binder := binder sc
    let s ← get
    let some body := s.body | throw "segment without a body"
    let some pos := body.find? e | throw "segment position"
    let pos := pos ++ [0]
    let names := env.map (·.1)
    let segName ← match s.segs.find? (·.1 == pos) with
      | some (_, n, _) => pure n
      | none => genSegment sc pos names x
    let v ← binder "v" "SourceValue F"; let m ← binder "m" "Heap F"
    let bs ← fresh "bs"; let c1 ← binder "cs" "List (Call F)"; let c2 ← fresh "c"
    let dx ← fresh "d"; let mt ← fresh "mt"; let db ← fresh "d"; let sg ← fresh "sg"
    addFact sg ([.s s!"«{s.fname}».{segName}"] ++ (env.map fun (_, t) => [Piece.s " ", .t t]).flatten ++
      [.s " ", .t hin, .s " ", .t (.v v), .s " ", .t (.v m), .s s!" {c1}"]) sg
    let (pl, binds) ← patInv (sc ++ "/pat") (.v v) pat mt (.v m)
    let rest ← if ← isDead then pure pl else
      pure (pl ++ (← invIn dups sc0 b db (binds ++ env) (.v m) dv dh fun s2 => k ([Seg.sub c1] ++ s2)))
    return [s!"obtain ⟨{v}, {m}, {bs}, {c1}, {c2}, {dx}, {mt}, {db}, rfl⟩ := {d}.letValue_inv",
      s!"have {sg} := «{s.fname}».{segName.decapitalize} {dx}", s!"clear {dx}"] ++ rest

  /-- The segment at `pos`: its inductive and theorem, over the local environment `names`. -/
  partial def genSegment (sc : String) (pos : List Nat) (names : List String) (x : Expr F) :
      M String := do
    let s0 ← get
    let segName ← request sc "Seg" (toString (s0.segs.size + 1)) 2
    let saved ← get
    let es := names.zipIdx.map fun (n, i) => s!"e{i}_{sanitize n}"
    set { saved with path := {}, ctors := #[], params := es ++ ["h", "r", "h'", "calls"], inSeg := true, unit := saved.segs.size + 1 }
    let script ← inv (sc ++ "/seg") x "d0" (names.zip (es.map T.v)) (.v "h") (.v "r") (.v "h'")
      (leaf (sc ++ "/seg") s!"«{saved.fname}».{segName}")
    let st ← get
    let lean := saved.leanName
    let ebind := if es.isEmpty then "" else s!"({" ".intercalate es} : SourceValue F) "
    let eimpl := if es.isEmpty then "" else s!"\{{" ".intercalate es} : SourceValue F} "
    let eargs := String.join (es.map (" " ++ ·))
    let locals := list ((names.zip es).map fun (n, e) => s!"({q n}, {e})")
    let ind := s!"/-- The `let`-bound match of `{saved.fname}` at `{pos}`: one constructor per combination of selected arms. -/\n" ++
      s!"inductive «{saved.fname}».{segName} {ebind}(h : Heap F) (r : SourceValue F) (h' : Heap F)\n" ++
      "    (calls : List (Call F)) : Prop where\n" ++
      "\n".intercalate (st.ctors.toList.map (·.text)) ++ "\n"
    let thm := s!"/-- **Every observed derivation of the `let`-bound match of `{saved.fname}` at `{pos}` takes one of its paths.** -/\n" ++
      s!"theorem «{saved.fname}».{segName.decapitalize} {eimpl}\{h h' : Heap F} \{r : SourceValue F}\n" ++
      s!"    \{calls : List (Call F)}\n" ++
      s!"    (d0 : ObsExpr W [] {locals} (Expr.sub {lean}.body {list (pos.map toString)}) h r h' calls) :\n" ++
      s!"    «{saved.fname}».{segName}{eargs} h r h' calls := by\n" ++
      s!"  simp only [Expr.sub, Expr.childAt, Expr.children, {lean}, List.map_cons, List.map_nil] at d0\n" ++
      "\n".intercalate (script.map ("  " ++ ·)) ++ "\n"
    let segs := saved.segs.push (pos, segName, ind ++ "\n" ++ thm)
    set { saved with counter := st.counter, names := st.names, abbrevs := st.abbrevs, work := st.work, lookups := st.lookups, segs := segs, lateUsed := st.lateUsed, trace := st.trace, ords := st.ords, shown := st.shown, fatal := st.fatal }
    return segName

  partial def invArgs (sc : String) (i : Nat) (es : List (Expr F)) (a : String) (env : Env) (hin : T)
      (items : List String) (dh : T) (k : K) : M (List String) := do
    match es, items with
    | [], [] =>
      assign (sc ++ "/end") dh hin
      return [s!"obtain ⟨rfl, rfl, rfl⟩ := {a}.nil_inv"] ++ (← k [])
    | e :: es, it :: its =>
      -- the `i`-th operand's place
      let me := s!"{sc}/{i}"
      let fresh := fresh me
      let binder := binder me
      let vs ← fresh "vs"; let m ← binder "m" "Heap F"; let c1 ← fresh "c"; let c2 ← fresh "c"
      let dh' ← fresh "d"; let a' ← fresh "a"
      return [s!"obtain ⟨{it}, {vs}, {m}, {c1}, {c2}, rfl, {dh'}, {a'}, rfl⟩ := {a}.cons_inv"] ++
        (← inv me e dh' env hin (.v it) (.v m) fun s1 =>
          invArgs sc (i + 1) es a' env (.v m) its dh fun s2 => k (s1 ++ s2))
    | _, _ => throw "argument arity"

  /-- Arms in order: the first matched (positive branch) or did not (negative). In a
  table (`table`: a dispatch of at least `tableArms` arms) whose scrutinee is a
  parameter, a matched arm drops the negations of the earlier arms: its own equation
  `x = template` implies them, and keeping them makes the paths quadratic. -/
  partial def invArms (dups : List String) (sc0 sc : String) (arms : List (Pattern F × Expr F)) (multi table : Bool)
      (sel db : String) (env : Env) (V heap dv dh : T) (k : K) : M (List String) := do
    match arms with
    | [] => return [s!"exact (selectArm_nil_inv {sel}).elim"]
    | (p, b) :: rest =>
      -- the arm's place, by its pattern's shape; the body of a match's only arm is the rest
      -- of the enclosing block (`sc0`), and selecting it is no choice
      let arm := sc ++ "/arm " ++ patShape p
      let fresh := fresh arm
      let mt ← fresh "mt"; let nm ← fresh "nm"; let sel' ← fresh "sel"
      let saved := (← get).path
      if multi then modifyPath fun q => { q with
        tokens := q.tokens.push (armToken p),
        ctx := combine q.ctx (strHash (patShape p)),
        ctxs := q.ctxs ++ "/" ++ armToken p }
      let (pl, binds) ← patInv (arm ++ "/pat") V p mt heap
      if table && !(← isDead) then
        let s ← get
        let Vr := V.resolve s.path.subst
        if (match Vr with | .v n => s.params.contains n | _ => false) then
          modifyPath fun q => { q with facts := q.facts.filter fun (_, _, _, subj) =>
            match subj with | some u => u.resolve q.subst != Vr | none => true }
      let pos ← if ← isDead then pure [] else
        if multi then inv arm b db (binds ++ env) heap dv dh k
        else invIn dups sc0 b db (binds ++ env) heap dv dh k
      modify fun s => { s with path := saved }
      let (nl, dead) ← negArm arm V p nm
      let negRest ← if dead then pure [] else
        invArms dups sc0 sc rest multi table sel' db env V heap dv dh k
      modify fun s => { s with path := saved }
      return [s!"rcases selectArm_cons_inv {sel} with ⟨{mt}, rfl⟩ | ⟨{nm}, {sel'}⟩"] ++
        bullet (pl ++ pos) ++ bullet (nl ++ negRest)

  /-- What an unmatched arm tells about the scrutinee; `true` if impossible. -/
  partial def negArm (sc : String) (V : T) (p : Pattern F) (nm : String) : M (List String × Bool) := do
    let fresh := fresh sc
    match p with
    | .wildcard => return ([s!"exact (matchPattern_wildcard_none {nm}).elim"], true)
    | .bind _ => return ([s!"exact (matchPattern_bind_none {nm}).elim"], true)
    | _ =>
      if let some (u, prf) ← constPat? p then
        let hne ← fresh "hne"
        addFact hne [.s "(", .t V, .s " : SourceValue F) ≠ ", .t u] hne (subject := some V)
        return ([s!"have {hne} := MatchesConst.none_inv ({prf}) {nm}"], false)
      match p with
      | .construct t c ps =>
        if ps.all isFlat then
          let (lit, lem) ← ctorName t
          let hne ← fresh "hne"
          addFact hne [.s s!"∀ vs : List (SourceValue F), vs.length = {ps.length} → (", .t V,
            .s s!" : SourceValue F) ≠ .construct {lit} {q c} vs"] hne (subject := some V)
          return ([s!"have {hne} := matchPattern_construct_none (by trivial) {nm}",
            s!"simp only [{lem}] at {hne}"], false)
        else return ([s!"clear {nm}"], false)
      | .tuple ps | .array ps =>
        if ps.all isFlat then
          let hne ← fresh "hne"
          addFact hne [.s s!"∀ vs : List (SourceValue F), vs.length = {ps.length} → (", .t V,
            .s " : SourceValue F) ≠ .tuple vs"] hne (subject := some V)
          let lem := match p with | .tuple _ => "matchPattern_tuple_none" | _ => "matchPattern_array_none"
          return ([s!"have {hne} := {lem} (by trivial) {nm}"], false)
        else
          let kind := match p with | .tuple _ => "tuple" | _ => "array"
          match ← (if (← get).late then mixedNeg sc V kind ps nm else pure none) with
          | some ls => return (ls, false)
          | none => return ([s!"clear {nm}"], false)
      | _ => return ([s!"clear {nm}"], false)

  /-- **An unmatched tuple pattern of flat and constant components** (`(1, x)`, `(_, 1)`): its
  constant components' equations do not all hold. At a tuple of terms the fact is
  `¬ (u₁ = c₁ ∧ …)` (`u ≠ c` for one constant); at a variable `v`,
  `∀ a⃗, v ≠ .tuple [c₁, a₁, …]`. The fact is kept after the call equation (`Path.late`),
  so the fields before it keep their positions. `none` for any other pattern. -/
  partial def mixedNeg (sc : String) (V : T) (kind : String) (ps : List (Pattern F)) (nm : String) :
      M (Option (List String)) := do
    let freshLate := freshLate sc
    let mut comps : Array (Option (T × String)) := #[]
    for q in ps do
      if isFlat q then comps := comps.push none
      else match ← constPat? q with
        | some c => comps := comps.push (some c)
        | none => return none
    unless comps.any (·.isSome) do return none
    let lem := s!"matchPattern_{kind}_mixed_none"
    let name ← freshLate "hnt"
    match ← resolveT V with
    | .tuple us =>
      unless us.length == ps.length do return none
      let pairs := (us.zip comps.toList).zipIdx
      let consts := pairs.filterMap fun ((u, c), i) => c.map fun (t, _) => (u, t, i)
      let stmt : List Piece := match consts with
        | [(u, t, _)] => [.s "(", .t u, .s " : SourceValue F) ≠ ", .t t]
        | _ =>
          let eqs := consts.map fun (u, t, _) => [.s "(", .t u, .s " : SourceValue F) = ", .t t]
          [.s "¬ ("] ++ (eqs.intersperse [.s " ∧ "]).flatten ++ [.s ")"]
      let hs := consts.map fun (_, _, i) => s!"h{i}"
      let pat := match hs with | [h] => h | _ => "⟨" ++ ", ".intercalate hs ++ "⟩"
      let mml := pairs.foldr (fun ((_, c), i) acc => match c with
        | none => s!"(.cons (Or.inl trivial) {acc})"
        | some (_, prf) => s!"(.cons (Or.inr ⟨_, ({prf}), h{i}⟩) {acc})") ".nil"
      let s ← get
      modifyPath fun q => { q with late := q.late.push (name, stmt, name) }
      modify fun s => { s with lateUsed := true }
      return some [s!"have {name} : {renderPieces s.path.subst stmt} := fun {pat} => {lem} {nm} {mml}"]
    | .v n =>
      let mut binds : Array String := #[]
      let mut items : Array String := #[]
      for c in comps do
        match c with
        | none =>
          let a ← freshLate "a"
          binds := binds.push a
          items := items.push a
        | some (t, _) => items := items.push t.render
      let mml := comps.toList.foldr (fun c acc => match c with
        | none => s!"(.cons (Or.inl trivial) {acc})"
        | some (_, prf) => s!"(.cons (Or.inr ⟨_, ({prf}), rfl⟩) {acc})") ".nil"
      let stmt : List Piece := [.s s!"∀ {" ".intercalate binds.toList} : SourceValue F, (", .t (.v n),
        .s s!" : SourceValue F) ≠ .tuple [{", ".intercalate items.toList}]"]
      let hv ← freshLate "hv"
      let s ← get
      modifyPath fun q => { q with late := q.late.push (name, stmt, name) }
      modify fun s => { s with lateUsed := true }
      return some [s!"have {name} : {renderPieces s.path.subst stmt} := " ++
        s!"fun {" ".intercalate binds.toList} {hv} => by rw [{hv}] at {nm}; exact {lem} {nm} {mml}"]
    | _ => return none

  /-- Invert a successful match of `p` against `V`; returns the bindings. -/
  partial def patInv (sc : String) (V : T) (p : Pattern F) (mt : String) (heap : T) :
      M (List String × Env) := do
    let fresh := fresh sc
    let binder := binder sc
    match p with
    | .bind n => return ([s!"obtain rfl := matchPattern_bind_inv {mt}"], [(n, V)])
    | .wildcard => return ([s!"obtain rfl := matchPattern_wildcard_inv {mt}"], [])
    | .load p' =>
      let u ← binder "y" "SourceValue F"; let ld ← fresh "ld"; let mt' ← fresh "mt"
      addFact ld [.s "loadValue ", .t heap, .s " ", .t V, .s " = .ok ", .t (.v u)] ld
      let (ls, bs) ← patInv (sc ++ "/*") (.v u) p' mt' heap
      return ([s!"obtain ⟨{u}, {ld}, {mt'}⟩ := matchPattern_load_inv {mt}"] ++ ls, bs)
    | _ =>
      if let some (u, prf) ← constPat? p then
        let hv ← fresh "hv"
        let ls ← unifyPat V u hv
        return ([s!"obtain ⟨{hv}, rfl⟩ := MatchesConst.some_inv ({prf}) {mt}"] ++ ls, [])
      match p with
      | .construct t c ps =>
        let (lit, lem) ← ctorName t
        let vs ← fresh "vs"; let hv ← fresh "hv"; let ml ← fresh "ml"
        match ← resolveT V with
        | .ctor knownType knownCtor us =>
          unless knownType == lit && knownCtor == c do
            throw "concrete constructor pattern mismatch"
          unless us.length == ps.length do throw "constructor pattern length"
          let fields ← fresh "hfields"
          let (mls, bs) ← listInvConcrete sc 0 ps us ml heap
          return ([s!"obtain ⟨{vs}, {hv}, -, {ml}⟩ := matchPattern_construct_inv {mt}",
            s!"rw [{lem}] at {hv}",
            s!"have {fields} := (Value.construct.inj {hv}).2.2",
            s!"subst {vs}"] ++ mls, bs)
        | _ =>
          let subs ← subBinders sc ps
          let ls ← unifyPat V (.ctor lit c (subs.map .v)) hv
          let (mls, bs) ← listInv sc 0 ps subs ml heap
          return ([s!"obtain ⟨{vs}, {hv}, -, {ml}⟩ := matchPattern_construct_inv {mt}",
            s!"rw [{lem}] at {hv}"] ++ ls ++ mls, bs)
      | .tuple ps | .array ps =>
        let kind := match p with | .tuple _ => "tuple" | _ => "array"
        match ← resolveT V with
        | .tuple us =>
          unless us.length == ps.length do throw "tuple pattern length"
          let ml ← fresh "ml"
          let (mls, bs) ← listInvConcrete sc 0 ps us ml heap
          return ([s!"have {ml} := matchPattern_{kind}_tuple_inv {mt}"] ++ mls, bs)
        | .v _ =>
          let vs ← fresh "vs"; let hv ← fresh "hv"; let ml ← fresh "ml"
          let subs ← subBinders sc ps
          let ls ← unifyPat V (.tuple (subs.map .v)) hv
          if ← isDead then return ([s!"obtain ⟨{vs}, {hv}, -, {ml}⟩ := matchPattern_{kind}_inv {mt}"] ++ ls, [])
          let (mls, bs) ← listInv sc 0 ps subs ml heap
          return ([s!"obtain ⟨{vs}, {hv}, -, {ml}⟩ := matchPattern_{kind}_inv {mt}"] ++ ls ++ mls, bs)
        | _ => throw "tuple pattern on a non-tuple"
      | .orElse _ _ _ => throw "or-pattern"
      | p => throw s!"pattern form ({patKind p})"

  partial def subBinders (sc : String) (ps : List (Pattern F)) : M (List String) :=
    ps.zipIdx.mapM fun
      | (.bind n, i) => namedBinder s!"{sc}/{i}" n "SourceValue F"
      | (_, i) => binder s!"{sc}/{i}" "w" "SourceValue F"

  partial def listInv (sc : String) (i : Nat) (ps : List (Pattern F)) (subs : List String) (ml : String)
      (heap : T) : M (List String × Env) := do
    match ps, subs with
    | [], [] => return ([s!"obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv {ml}"], [])
    | p :: ps, w :: ws =>
      let me := s!"{sc}/{i}"
      let fresh := fresh me
      let vs ← fresh "vs"; let b1 ← fresh "b"; let b2 ← fresh "b"
      let mt ← fresh "mt"; let ml' ← fresh "ml"
      let hd := s!"obtain ⟨{w}, {vs}, {b1}, {b2}, rfl, {mt}, {ml'}, rfl⟩ := matchListWith_cons_inv {ml}"
      let (l1, bs1) ← patInv me (.v w) p mt heap
      if ← isDead then return (hd :: l1, bs1)
      let (l2, bs2) ← listInv sc (i + 1) ps ws ml' heap
      return (hd :: l1 ++ l2, bs1 ++ bs2)
    | _, _ => throw "pattern arity"

  partial def listInvConcrete (sc : String) (i : Nat) (ps : List (Pattern F)) (us : List T) (ml : String)
      (heap : T) : M (List String × Env) := do
    match ps, us with
    | [], [] => return ([s!"obtain ⟨-, rfl⟩ := matchListWith_nil_inv {ml}"], [])
    | p :: ps, u :: us =>
      let me := s!"{sc}/{i}"
      let fresh := fresh me
      let b1 ← fresh "b"; let b2 ← fresh "b"; let mt ← fresh "mt"; let ml' ← fresh "ml"
      let hd := s!"obtain ⟨{b1}, {b2}, {mt}, {ml'}, rfl⟩ := matchListWith_cons_cons_inv {ml}"
      let (l1, bs1) ← patInv me u p mt heap
      if ← isDead then return (hd :: l1, bs1)
      let (l2, bs2) ← listInvConcrete sc (i + 1) ps us ml' heap
      return (hd :: l1 ++ l2, bs1 ++ bs2)
    | _, _ => throw "pattern arity"
end

/-! ## One function -/


/-- Functions the refinement proofs need whose paths multiply: generated under
larger caps, at a larger module cost. -/
def generous : List String :=
  ["KernelWhnf::whnf_nd_const_head", "KernelRoles::basis_pin"]

/-! ## Renaming -/

/-- How names are chosen: with the table (`some`: function, then position key, to suffix), or
by the counter alone (`none`: the output before names had positions, and the entries the
table is written from). -/
structure NameCfg where
  table : Option (Std.HashMap String (Std.HashMap String String)) := none
  explain : Bool := false

/-- Why a function has no result. `skip`: it is not generated, as before names had positions
(control syntax, too many paths, …). `names`: its names cannot be assigned; the generation
stops and nothing is written. -/
inductive Failure where
  | skip (reason : String)
  | names (message : String)

def skipIf {α : Type} : Except String α → Except Failure α
  | .ok a => .ok a
  | .error e => .error (.skip e)

/-- What naming a function produced besides its text. -/
structure Naming where
  /-- The position key and the counter's suffix of each shown name: the function's entries of
  the table, when the names are the counter's. -/
  entries : Array (String × String) := #[]
  /-- The shown names with their positions in words (`NameCfg.explain`). -/
  lines : Array String := #[]
  /-- The function was run again, to rename. -/
  renamed : Bool := false
  /-- Shown names that are the table's, and shown names derived from their positions. -/
  fromTable : Nat := 0
  derived : Nat := 0

/-- Whether a request's name (as `name`) appears in a constructor. -/
def isShown (shown : Std.HashSet String) (r : Req) (name : String) : Bool :=
  r.kind == 2 || shown.contains s!"{r.unit}/{r.kind}/{name}"

/-- A shown name: the table's suffix for its position, or letters derived from the position. -/
def shownName (tbl : Std.HashMap String String) (r : Req) : String :=
  match tbl.get? (hex r.key) with
  | some sfx => r.base ++ sfx
  | none => r.base ++ "_" ++ letters r.key

/-- Two shown names of one inductive that read the same under `final`: the message, with the
two positions. -/
def shownClash (st : St) (final : Req → String) : Option String := Id.run do
  let mut seen : Std.HashMap String Req := ∅
  for r in st.trace do
    if isShown st.shown r (r.base ++ r.sfx) then
      let n := final r
      match seen.get? s!"{r.unit}/{n}" with
      | some r0 =>
        return some (s!"two shown names `{n}` in one inductive, at {r0.desc} [{hex r0.key}] " ++
          s!"and at {r.desc} [{hex r.key}]")
      | none => seen := seen.insert s!"{r.unit}/{n}" r
  return none

/-- The names of a pass's requests under the table, after the pass was run with the counter's
names (`st`). `none`: every shown name already is the table's, and the pass's output stands.
A name that is not shown keeps the counter's suffix, set apart (`_`) if a shown name of its
inductive reads the same. Two shown names of one inductive that read the same are an error
(`shownClash`), whether or not the pass is run again. -/
def rename (tbl : Std.HashMap String String) (st : St) : Except String (Option (Array String)) := do
  let shown (r : Req) : Bool := isShown st.shown r (r.base ++ r.sfx)
  if let some m := shownClash st (shownName tbl) then throw m
  if st.trace.all (fun r => !shown r || tbl.get? (hex r.key) == some r.sfx) then return none
  let used : Std.HashSet String := st.trace.foldl
    (fun acc r => if shown r then acc.insert s!"{r.unit}/{shownName tbl r}" else acc) ∅
  return some (st.trace.map fun r =>
    if shown r then shownName tbl r
    else if used.contains s!"{r.unit}/{r.base}{r.sfx}" then
      r.base ++ (if r.kind == 1 then "_l" else "_") ++ r.sfx
    else r.base ++ r.sfx)

/-- How the pass run again under `names` (`st2`) differs from the first (`st`) in what it asked
for: another number of requests, a request at another position, or a request shown in one and
not in the other. `none`: the same requests at the same positions, the same ones shown. -/
def requestMismatch (st : St) (names : Array String) (st2 : St) : Option String :=
  if st.trace.size != st2.trace.size || names.size != st.trace.size then
    some s!"the second pass made {st2.trace.size} requests for names, the first {st.trace.size}"
  else (List.range st.trace.size).findSome? fun i =>
    let r := st.trace[i]!
    let r2 := st2.trace[i]!
    if r.key != r2.key then
      some (s!"request {i} of the second pass is at another position: {r.desc} [{hex r.key}] " ++
        s!"in the first, {r2.desc} [{hex r2.key}] in the second")
    else if isShown st.shown r (r.base ++ r.sfx) != isShown st2.shown r2 (names.getD i "") then
      some s!"request {i}, at {r.desc} [{hex r.key}], is shown in one pass and not in the other"
    else none

/-- The table's entries of a pass run with the counter's names. -/
def tableEntries (st : St) : Array (String × String) :=
  st.trace.filterMap fun r =>
    if isShown st.shown r (r.base ++ r.sfx) then some (hex r.key, r.sfx) else none

/-- The shown names of a pass (as `names`, or the counter's) with their positions in words. -/
def explainLines (on : Bool) (fname : String) (st : St) (names : Option (Array String)) :
    Array String :=
  if !on then #[] else
    ((List.range st.trace.size).filterMap fun i =>
      let r := st.trace[i]!
      let name := (names.map fun ns => ns.getD i "").getD (r.base ++ r.sfx)
      if isShown st.shown r name then
        some s!"{fname}\t{r.unit}\t{name}\t{hex r.key}\t{r.desc}"
      else none).toArray

/-- The path inductive and the inversion theorem of one function, in one pass: the unchanged
`«f».Path` and `«f».obs`, or (`x`) the extended `«f».PathX` and `«f».obsx`, whose constructors
also carry the facts kept after the call equation. The last component of the first result says
whether any was.

The pass runs with the counter's names. Under a table, it runs once more with the names
`rename` gives, unless every shown name already is the table's: at the source the table was
written from, the output is the first run's.

A failure of the names (`Failure.names`: two shown names that read the same, two fields of
one name, a second run that asks for other names or fails) is not a reason to leave the
function out: it stops the generation. -/
def functionPass (cfg : NameCfg) (src : Aiur.Generic.Source F) (f : Function F) (index : Nat) (x : Bool)
    (maxChars : Nat := if generous.contains f.name then 2000000 else 200000) :
    Except Failure ((String × Array (String × String × String) × Array (String × String × String) × Nat × Bool) × Naming) := do
  if f.typeParams.length > 1 then throw (.skip "several type parameters")
  if f.name.startsWith "$" then throw (.skip "internal function")
  if ControlLower.hasControl f.body then throw (.skip "control")
  let sfx := if x then "X" else ""
  let tp := f.typeParams.head?
  let ps := f.params.map fun (n, _) => "x_" ++ n
  let params := ps ++ ["h", "r", "h'", "calls"]
  let env : Env := (f.params.map (·.1)).zip (ps.map .v)
  let leanName := s!"IxVM.{functionName f.name}"
  let body : M (List String) :=
    inv "" f.body "d0" env (.v "h") (.v "r") (.v "h'") (leaf "" s!"«{f.name}».Path{sfx}")
  let maxLookups := if generous.contains f.name then 40000 else 3000
  let init : St := { counter := 1, params, src := some src, typeParam := tp, maxLookups, fname := f.name, leanName, body := some f.body, segment := !unsegmented.contains f.name, late := x, suffix := sfx }
  -- a generic function is stated at its instance `t_<param>`
  let (tbind, targ, tibind, symbol, lookupThm, lookupDecl) := match tp with
    | none => ("", "", "", q f.name, s!"{leanName}.lookup", "")
    | some tp =>
      (s!"(t_{tp} : Generic.Ty) ", s!" t_{tp}", s!"\{t_{tp} : Generic.Ty} ",
       s!"(Instance.mk {q f.name} [t_{tp}]).symbol", s!"(«{f.name}».lookup t_{tp})",
       if x then "" else
       s!"/-- The program resolves `{f.name}` at each instance to its closure. -/\n" ++
       s!"theorem «{f.name}».lookup (t_{tp} : Generic.Ty) :\n" ++
       s!"    IxVM.source.program.sourceFunction? (Instance.mk {q f.name} [t_{tp}]).symbol =\n" ++
       s!"      some \{ types := [({q tp}, t_{tp})],\n" ++
       s!"             params := {leanName}.params.map fun (p, pt) => (p, (pt.subst [({q tp}, t_{tp})]).toCore),\n" ++
       s!"             body := {leanName}.body } :=\n" ++
       s!"  Program.sourceFunction?_of_mem_one (f := {leanName}) IxVM.functionNames_nodup\n" ++
       s!"    (List.getElem_mem (l := IxVM.functions) (n := {index}) (by decide +kernel)) rfl t_{tp}\n\n")
  let pbind := if ps.isEmpty then "" else s!"({" ".intercalate ps} : SourceValue F) "
  let pargs := if ps.isEmpty then "" else " " ++ " ".intercalate ps
  let ibind := if ps.isEmpty then "" else s!"\{{" ".intercalate ps} : SourceValue F} "
  let render (script : List String) (st : St) : String :=
    let ind := s!"/-- The evaluation paths of `{f.name}`: one constructor per combination of selected arms" ++
      (if x then ", with the facts of the arms not taken." else ".") ++ " -/\n" ++
      s!"inductive «{f.name}».Path{sfx} {tbind}{pbind}(h : Heap F) (r : SourceValue F) (h' : Heap F)\n" ++
      "    (calls : List (Call F)) : Prop where\n" ++
      "\n".intercalate (st.ctors.toList.map (·.text)) ++ "\n"
    let thm := s!"/-- **Every observed derivation of `{f.name}` takes one of its paths.** -/\n" ++
      s!"theorem «{f.name}».obs{sfx.toLower} {tibind}{ibind}\{h h' : Heap F} \{r : SourceValue F}\n" ++
      s!"    \{calls : List (Call F)} (ev : ObsFn W {symbol} {list ps} h r h' calls) :\n" ++
      s!"    «{f.name}».Path{sfx}{targ}{pargs} h r h' calls := by\n" ++
      s!"  have d0 := ObsFn.function_inv (s := IxVM.source) {lookupThm}\n" ++
      s!"    (by simp [{leanName}, ControlLower.hasControl]) ev\n" ++
      s!"  simp only [{leanName}] at d0\n" ++
      "\n".intercalate (script.map ("  " ++ ·)) ++ "\n"
    let segTexts := String.join (st.segs.toList.map fun (_, _, t) => t ++ "\n")
    lookupDecl ++ segTexts ++ ind ++ "\n" ++ thm
  -- a failure of the names, with the function and the pass
  let stop (m : String) : Failure :=
    .names s!"{f.name}{if x then " (extended lemma)" else ""}: {m}"
  -- the counter's names; the size limit is on this text, so that renaming never drops a function
  let (script, st) ← skipIf (body.run init)
  if let some m := st.fatal then throw (stop m)
  let text := render script st
  if text.length > maxChars then throw (.skip s!"too large: {text.length / 1000} KB")
  let out := (text, st.names, st.abbrevs, st.ctors.size, st.lateUsed)
  -- an extended pass that kept no fact is not used (`function`): its names are not assigned
  if x && !st.lateUsed then return (out, {})
  match cfg.table with
  | none =>
    if let some m := shownClash st (fun r => r.base ++ r.sfx) then throw (stop m)
    return (out, { entries := tableEntries st, lines := explainLines cfg.explain f.name st none })
  | some table =>
    let tbl : Std.HashMap String String := table.getD f.name ∅
    let shown := st.trace.filter fun r => isShown st.shown r (r.base ++ r.sfx)
    let fromTable := (shown.filter fun r => (tbl.get? (hex r.key)).isSome).size
    match rename tbl st with
    | .error m => throw (stop m)
    | .ok none => return (out, { lines := explainLines cfg.explain f.name st none, fromTable })
    | .ok (some names) =>
      let (script2, st2) ← match body.run { init with assigned := some names } with
        | .ok r => pure r
        | .error e => throw (stop s!"the second pass failed: {e}")
      if let some m := st2.fatal then throw (stop m)
      if let some m := requestMismatch st names st2 then throw (stop m)
      return ((render script2 st2, st2.names, st2.abbrevs, st2.ctors.size, st2.lateUsed),
        { lines := explainLines cfg.explain f.name st2 (some names), renamed := true, fromTable,
          derived := shown.size - fromTable })

/-- The path inductive and the inversion theorem of one function (`functionPass`), followed by
the extended ones when the function keeps a fact after a call equation. The extended pass is
left out when it is not generated, never for its names. -/
def function (cfg : NameCfg) (src : Aiur.Generic.Source F) (f : Function F) (index : Nat) :
    Except Failure ((String × Array (String × String × String) × Array (String × String × String) × Nat) × Naming) := do
  let ((text, names, abbrevs, n, _), nm) ← functionPass cfg src f index false
  match functionPass cfg src f index true with
  | .ok ((textX, namesX, abbrevsX, _, true), nmX) =>
    return ((text ++ "\n" ++ textX, names ++ namesX, abbrevs ++ abbrevsX, n),
      { entries := nm.entries ++ nmX.entries.filter fun e => !nm.entries.any (·.1 == e.1),
        lines := nm.lines ++ nmX.lines, renamed := nm.renamed || nmX.renamed,
        fromTable := nm.fromTable, derived := nm.derived })
  | .error (.names m) => throw (.names m)
  | _ => return ((text, names, abbrevs, n), nm)

/-! ## Files -/

def fileHeader (imports : List String) (doc : String) : String :=
  "\n".intercalate (imports.map ("import " ++ ·)) ++ "\n\n" ++
    s!"/-! {doc}\n\nGenerated by `lake exe ixvm/ixvm-proof-gen` from `IxVM.program`; do not\n" ++
    "edit. `--check` checks that the files are current. -/\n\n" ++
    "set_option maxRecDepth 100000\n" ++
    "set_option maxHeartbeats 40000000\n" ++
    "set_option linter.unusedVariables false\n" ++
    "set_option linter.unusedSimpArgs false\n" ++
    "set_option linter.unusedTactic false\n" ++
    "set_option linter.unreachableTactic false\n\n" ++
    "namespace IxVM.Refinement.Obs\n\n" ++
    "open Aiur Aiur.Generic Aiur.Generic.SourceSemantics\nopen IxVM (F)\n\n"

def fileFooter : String := "end IxVM.Refinement.Obs\n"

/-- The module group of a function: its name's first component. -/
def group (name : String) : String :=
  sanitize ((name.splitOn "::").head!)

abbrev Result :=
  Except String (String × Array (String × String × String) × Array (String × String × String) × Nat)

/-- **The generated files** from each function's result: the names module, one
module per chunk of a group, and the index module with the generator's report. -/
def assemble (results : List (String × Result)) (maxLines : Nat := 3000) :
    List (System.FilePath × String) := Id.run do
  let dir : System.FilePath := "IxVMRefinement/Obs"
  let mut names : Array (String × String × String) := #[]
  let mut abbrevs : Array (String × String × String) := #[]
  let mut report : Array String := #[]
  -- group → chunks (each: function texts, lines)
  let mut chunks : Array (String × Array String) := #[]
  let mut cur : Option (String × Array String × Nat) := none
  let mut proved := 0
  let mut paths := 0
  for (name, result) in results do
    match result with
    | .error e => report := report.push s!"{name}: skipped ({e})"
    | .ok (text, ns, abs, n) =>
      proved := proved + 1
      paths := paths + n
      report := report.push s!"{name}: {n} paths"
      for x in ns do
        unless names.any (·.1 == x.1) do names := names.push x
      -- an identifier names one literal (a second literal would redeclare it)
      for x in abs do
        unless abbrevs.any (· == x) do abbrevs := abbrevs.push x
      let g := group name
      let lines := (text.splitOn "\n").length
      match cur with
      | some (g', texts, l) =>
        if g' == g && l + lines ≤ maxLines then
          cur := some (g, texts.push text, l + lines)
        else
          chunks := chunks.push (g', texts)
          cur := some (g, #[text], lines)
      | none => cur := some (g, #[text], lines)
  if let some (g, texts, _) := cur then chunks := chunks.push (g, texts)
  -- number the chunks of each group
  let mut files : List (System.FilePath × String) := []
  let mut modules : Array String := #[]
  let mut owners : Array (String × String) := #[]
  let mut counts : List (String × Nat) := []
  for (g, texts) in chunks do
    let i := (counts.lookup g).getD 0
    counts := (g, i + 1) :: counts.filter (·.1 != g)
    let modName := s!"{g}{i}"
    modules := modules.push modName
    owners := owners.push (g, modName)
    let body := fileHeader ["IxVMRefinement.Obs.Names"]
      s!"Generated path lemmas: `{g}` functions, part {i}." ++
      "\n".intercalate texts.toList ++ "\n" ++ fileFooter
    files := files ++ [(dir / s!"{modName}.lean", body)]
  let namesText := fileHeader ["IxVMRefinement.Core.Obs", "IxVM.Lookup", "IxVM.ExprPath"]
      "Generated path lemmas: the world and the instance names they normalize." ++
    "/-- The prepared source's world. -/\nabbrev W : World F := IxVM.source.world\n\n" ++
    "namespace Names\n\n" ++
    String.join (abbrevs.toList.map fun (n, lit, inst) =>
      s!"/-- The instance `{n}`. -/\nabbrev «{n}» : String := {q lit}\n\n" ++
      (if inst.isEmpty then "" else
        s!"theorem «{n}».symbol : ({inst}).symbol = «{n}» := by decide +kernel\n\n")) ++
    String.join (names.toList.map fun (n, st, prf) =>
      s!"theorem {n} : {st} := {prf}\n\n") ++
    "end Names\n\n" ++ fileFooter
  -- one index module per group, so that importers do not depend on the chunking
  let mut groups : List String := []
  for (g, _) in chunks do
    unless groups.contains g do groups := groups ++ [g]
  for g in groups do
    let parts := (owners.toList.filter (·.1 == g)).map (·.2)
    let text := "\n".intercalate (parts.map (s!"import IxVMRefinement.Obs." ++ ·)) ++
      s!"\n\n/-! Generated path lemmas: the `{g}` functions (index of the parts). -/\n"
    files := files ++ [(dir / s!"{g}.lean", text)]
  let index := "\n".intercalate (modules.toList.map (s!"import IxVMRefinement.Obs." ++ ·)) ++
    "\n\n/-! # Generated path lemmas\n\n" ++
    "`«f».Path` and `«f».obs` for every monomorphic IxVM function without control\n" ++
    "syntax (`IxVM.ObsGen`). Generated by `lake exe ixvm/ixvm-proof-gen`; do not edit.\n\n" ++
    s!"{proved} functions, {paths} paths. Generator report:\n\n" ++
    String.join (report.toList.map (s!"* " ++ · ++ "\n")) ++ "-/\n"
  return [(dir / "Names.lean", namesText)] ++ files ++
    [(System.FilePath.mk "IxVMRefinement/Obs.lean", index)]


/-! ## The table of names

A text file. A line `@<tab>function` starts a function's entries, each a line
`key<tab>suffix`. A line that starts with `#` is a comment, except the line `#hash<tab>…`,
which declares the hash of all the other lines (`tableHash`). A function is renamed by
renaming its `@` line: positions do not name the function, and neither does the hash. -/

/-- The table of names as read: each function's entries, the functions in the file's order,
the hash its header declares and the hash of its lines. -/
structure Table where
  sections : Std.HashMap String (Std.HashMap String String) := ∅
  order : Array String := #[]
  declared : Option String := none
  computed : String := ""

/-- The hash of a table's lines: every line that is not empty, but the one that declares the
hash; a function's line counts as `@`, whatever function it names. -/
def tableHash (lines : List String) : String :=
  hex (strHash ("\n".intercalate (lines.filterMap fun line =>
    match line.splitOn "\t" with
    | ["#hash", _] => none
    | ["@", _] => some "@"
    | _ => if line.isEmpty then none else some line)))

/-- Read the table of names. Anything that is not a comment, a function's line or an entry
under a function, a second section for a function and a second entry for a key are errors. -/
def readTable (text : String) : Except String Table := do
  let lines := text.splitOn "\n"
  let mut sections : Std.HashMap String (Std.HashMap String String) := ∅
  let mut order : Array String := #[]
  let mut declared : Option String := none
  let mut cur : Option String := none
  let mut entries : Std.HashMap String String := ∅
  let mut n := 0
  for line in lines do
    n := n + 1
    match line.splitOn "\t" with
    | ["#hash", h] =>
      if declared.isSome then throw s!"line {n}: a second hash"
      declared := some h
    | ["@", name] =>
      if let some c := cur then sections := sections.insert c entries
      if sections.contains name then throw s!"line {n}: a second section for {name}"
      cur := some name
      order := order.push name
      entries := ∅
    | [key, sfx] =>
      if line.startsWith "#" then continue
      unless key.length == 16 && key.toList.all (fun c => "0123456789abcdef".toList.contains c) do
        throw s!"line {n}: not a position key"
      if cur.isNone then throw s!"line {n}: an entry before any function"
      if entries.contains key then throw s!"line {n}: a second entry for the position {key}"
      entries := entries.insert key sfx
    | _ =>
      unless line.isEmpty || line.startsWith "#" do
        throw s!"line {n}: neither a comment, a function nor an entry"
  if let some c := cur then sections := sections.insert c entries
  return { sections, order, declared, computed := tableHash lines }

/-- The table's text from each function's entries: the header, the hash of the lines, the
lines. -/
def tableText (sections : Array (String × Array (String × String))) : String :=
  let head := [
    "# Path-lemma names (IxVM.ObsGen): for each function, the positions that showed a name when",
    "# this table was written, with the suffix the name had. Written once, by",
    "# `lake exe ixvm/ixvm-proof-gen --emit-names`, and then neither extended nor edited, except",
    "# that a function is renamed by renaming its `@` line. The generator checks the hash below."]
  let body := (sections.toList.map fun (name, entries) =>
    s!"@\t{name}" :: entries.toList.map fun (key, sfx) => s!"{key}\t{sfx}").flatten
  "\n".intercalate (head ++ [s!"#hash\t{tableHash (head ++ body)}"] ++ body) ++ "\n"

/-- What a generation produced. -/
structure Rendered where
  files : List (System.FilePath × String) := []
  /-- The table of the counter's names (its entries are the counter's suffixes: meaningful
  when the names were chosen without a table). -/
  table : String := ""
  /-- The shown names with their positions in words (`NameCfg.explain`). -/
  explain : String := ""
  /-- The functions whose names could not be assigned. If there is one, nothing is to be
  written. -/
  failures : Array String := #[]

/-- Each function's result, in program order, printing each function's outcome and time. -/
def renderIO (cfg : NameCfg) : IO Rendered := do
  let mut rs : Array (String × Result) := #[]
  let mut sections : Array (String × Array (String × String)) := #[]
  let mut lines : Array String := #[]
  let mut failures : Array String := #[]
  for (name, i) in (IxVM.functions.map (·.name)).zipIdx do
    let some f := IxVM.program.functions.find? (·.name == name) | continue
    let t0 ← IO.monoMsNow
    let r := function cfg IxVM.source f i
    let tag := match r with
      | .ok ((_, _, _, n), nm) => s!"{n} paths" ++
        (if nm.renamed then s!", renamed: {nm.fromTable} names of the table, {nm.derived} derived" else "")
      | .error (.skip e) => s!"skipped ({e})"
      | .error (.names _) => "names could not be assigned"
    IO.eprintln s!"[obs-gen] {name}: {tag} {(← IO.monoMsNow) - t0}ms"
    match r with
    | .ok (out, nm) =>
      sections := sections.push (name, nm.entries)
      lines := lines ++ nm.lines
      rs := rs.push (name, .ok out)
    | .error (.skip e) => rs := rs.push (name, .error e)
    | .error (.names m) => failures := failures.push m
  return { files := assemble rs.toList, table := tableText sections,
           explain := "\n".intercalate lines.toList ++ "\n", failures }

end IxVM.ObsGen
