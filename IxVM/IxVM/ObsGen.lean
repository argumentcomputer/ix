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

The generator reads only the program (`IxVM.program`): its output follows the
source. It is untrusted; Lean checks every generated proof. -/

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

/-! ## State -/

/-- What one path has established so far. -/
structure Path where
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
  /-- Whether `let`-bound matches are inverted as segments (`segmented`). -/
  segment : Bool := false
  /-- Segments generated so far: position, name, and rendered declarations. -/
  segs : Array (List Nat × String × String) := #[]
  /-- Inside a segment: no nested segments. -/
  inSeg : Bool := false

abbrev M := StateT St (Except String)

def fresh (base : String) : M String := do
  let s ← get
  set { s with counter := s.counter + 1 }
  return s!"{base}{s.counter}"

def modifyPath (f : Path → Path) : M Unit :=
  modify fun s => { s with path := f s.path }

/-- A new path variable of a type. -/
def binder (base type : String) : M String := do
  let n ← fresh base
  modifyPath fun p => { p with binders := p.binders.push (n, type), used := p.used.push n }
  return n

/-- A binder named after a source variable, unique on the path. -/
def namedBinder (src type : String) : M String := do
  let base := "x_" ++ src
  let p := (← get).path
  let taken := (← get).params.contains base || p.used.contains base
  let n ← if taken then fresh (base ++ "_") else pure base
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
def assign (dest t : T) : M Unit := do
  match ← resolveT dest with
  | .v n =>
    if ← isParam n then
      let f ← fresh "he"
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

/-- The leaf: the call list's equation, then the path's constructor (of the inductive `ind`). -/
def leaf (ind : String) (segs : List Seg) : M (List String) := do
  let hcName ← fresh "hc"
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
  let p := { p with facts := kept.push (hcName, [.s s!"calls = {callsT}"],
    s!"(by first | rfl | simp only [{", ".intercalate lemmas.eraseDups}])", none) }
  let binders := p.binders.toList.filter fun (n, _) => (p.subst.lookup n).isNone
  -- the constructor's name: the arm tokens, made unique
  let base := sanitize ("_".intercalate p.tokens.toList)
  let name := uniqueName (s.ctors.map (·.name)) base
  let fields := p.facts.toList.map fun (n, f, _, _) => s!"({n} : {renderPieces p.subst f})"
  let bs := binders.map fun (n, t) => s!"({n} : {t})"
  let text := s!"  | {name}" ++
    (if bs.isEmpty then "" else "\n      " ++ " ".intercalate bs) ++
    String.join (fields.map ("\n      " ++ ·))
  modify fun s => { s with ctors := s.ctors.push { name, text } }
  let norm := if p.stored then
      let hs := p.hyps.toList
      [s!"try simp only [Value.type, List.map_cons, List.map_nil] at {" ".intercalate hs} ⊢"]
    else []
  let holes := String.join (binders.map fun _ => " _")
  let proofs := String.join (p.facts.toList.map fun (_, _, pr, _) => " " ++ pr)
  return norm ++ [s!"exact {ind}.{name}{holes}{proofs}"]

/-! ## Inversion -/

abbrev Env := List (String × T)

abbrev K := List Seg → M (List String)

/-- A match of at least this many arms is a table (`invArms`). -/
def tableArms : Nat := 16

/-- Functions whose `let`-bound matches are inverted as segments: the match's paths
become their own inductive (`«f».Seg<i>`, with its theorem `«f».seg<i>`), and the
function's paths continue once after it, instead of once per arm. -/
def segmented : List String :=
  ["KernelWhnf::red_rec", "KernelWhnf::whnf_nd_const_head", "KernelCheck::check_recursor_canonical_full"]

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
  partial def inv (e : Expr F) (d : String) (env : Env) (hin dv dh : T) (k : K) :
      M (List String) := do
    let s ← get
    if s.work ≥ 20000 then throw "too large"
    set { s with work := s.work + 1 }
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
      return [s!"obtain ⟨{vs}, {a}, rfl⟩ := {d}.{lem}"] ++ (← invArgs es a env hin items dh k)
    | .construct name targs ctor es =>
      let (lit, lem) ← instName name targs
      let vs ← fresh "vs"; let a ← fresh "a"; let hr ← fresh "hres"
      let items ← es.mapM fun _ => binder "v" "SourceValue F"
      assign dv (.ctor lit ctor (items.map .v))
      return [s!"obtain ⟨{vs}, {a}, {hr}⟩ := {d}.construct_inv", s!"rw [{lem}] at {hr}",
        s!"subst {hr}"] ++ (← invArgs es a env hin items dh k)
    | .constructAs _ t ctor es =>
      let (lit, lem) ← ctorName t
      let vs ← fresh "vs"; let a ← fresh "a"; let hr ← fresh "hres"
      let items ← es.mapM fun _ => binder "v" "SourceValue F"
      assign dv (.ctor lit ctor (items.map .v))
      return [s!"obtain ⟨{vs}, {a}, {hr}⟩ := {d}.constructAs_inv", s!"rw [{lem}] at {hr}",
        s!"subst {hr}"] ++ (← invArgs es a env hin items dh k)
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
        (← inv x d' env hin (.v v) (.v m) k)
    | .load x =>
      let p ← binder "p" "SourceValue F"; let d' ← fresh "d"; let ld ← fresh "ld"
      let rest ← inv x d' env hin (.v p) dh fun segs => do
        addFact ld [.s "loadValue ", .t dh, .s " ", .t (.v p), .s " = .ok ", .t dv] ld
        k segs
      return [s!"obtain ⟨{p}, {d'}, {ld}⟩ := {d}.load_inv"] ++ rest
    | .call name targs es =>
      let (lit, lem) ← instName name targs
      useLemma lem
      let vs ← fresh "vs"; let m ← binder "m" "Heap F"; let c1 ← fresh "c"
      let c2 ← binder "cs" "List (Call F)"; let a ← fresh "a"; let ev ← fresh "ev"
      let items ← es.mapM fun _ => binder "v" "SourceValue F"
      let rest ← invArgs es a env hin items (.v m) fun s1 => do
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
      let rest ← inv l dl env hin (.v x) (.v m) fun s1 =>
        inv r dr env (.v m) (.v y) dh fun s2 => do
          addFact o [.s s!"evalBinOp {opName} (", .t (.v x), .s " : SourceValue F) (", .t (.v y),
            .s " : SourceValue F) = .ok ", .t dv] o
          k (s1 ++ s2)
      return [s!"obtain ⟨{x}, {y}, {m}, {c1}, {c2}, {dl}, {dr}, {o}, rfl⟩ := {d}.binary_inv"] ++ rest
    | .builtin op es =>
      let vs ← fresh "vs"; let a ← fresh "a"; let ap ← fresh "ap"
      let items ← es.mapM fun _ => binder "v" "SourceValue F"
      let rest ← invArgs es a env hin items dh fun segs => do
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
      let rest ← inv x d' env hin (.v p) dh fun segs => do
        addFact pr [.s "projectValue (", .t (.v p), .s s!" : SourceValue F) {i} = .ok ", .t dv] pr
        k segs
      return [s!"obtain ⟨{p}, {d'}, {pr}⟩ := {d}.{lem}"] ++ rest
    | .slice x a b =>
      let p ← binder "p" "SourceValue F"; let d' ← fresh "d"; let pr ← fresh "sl"
      let bs := match b with | some n => s!"(some {n})" | none => "none"
      let rest ← inv x d' env hin (.v p) dh fun segs => do
        addFact pr [.s "sliceValue (", .t (.v p), .s s!" : SourceValue F) {a} {bs} = .ok ", .t dv] pr
        k segs
      return [s!"obtain ⟨{p}, {d'}, {pr}⟩ := {d}.slice_inv"] ++ rest
    | .member x f =>
      let p ← binder "p" "SourceValue F"; let d' ← fresh "d"; let pr ← fresh "mb"
      let rest ← inv x d' env hin (.v p) dh fun segs => do
        addFact pr [.s s!"memberValue [] {fieldRef f} (", .t (.v p), .s " : SourceValue F) = .ok ", .t dv] pr
        k segs
      return [s!"obtain ⟨{p}, {d'}, {pr}⟩ := {d}.member_inv"] ++ rest
    | .neg x =>
      let p ← binder "p" "SourceValue F"; let d' ← fresh "d"; let pr ← fresh "ng"
      let rest ← inv x d' env hin (.v p) dh fun segs => do
        addFact pr [.s "evalNeg (", .t (.v p), .s " : SourceValue F) = .ok ", .t dv] pr
        k segs
      return [s!"obtain ⟨{p}, {d'}, {pr}⟩ := {d}.neg_inv"] ++ rest
    | .repeat x n =>
      let p ← binder "v" "SourceValue F"; let d' ← fresh "d"
      assign dv (.rep n (.v p))
      return [s!"obtain ⟨{p}, {d'}, rfl⟩ := {d}.repeat_inv"] ++ (← inv x d' env hin (.v p) dh k)
    | .update paths es =>
      let vs ← fresh "vs"; let a ← fresh "a"; let up ← fresh "up"
      let items ← es.mapM fun _ => binder "v" "SourceValue F"
      let ps := list (paths.map fun p => list (p.map updateStep))
      let rest ← invArgs es a env hin items dh fun segs => do
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
      let rest ← inv key d' env hin (.v x) dh fun segs => do
        addFact tp [.s s!"W.typed (Generic.Ty.toCore (Generic.Ty.subst [] {ty t})) ", .t (.v c),
          .s " = true"] tp
        k segs
      return [s!"obtain ⟨{x}, {c}, {d'}, {tp}, rfl⟩ := {d}.hint_inv"] ++ rest
    | .letValue pat x b =>
      if ← segmentable x then return ← letSegment e pat x b d env hin dv dh k
      let v ← binder "v" "SourceValue F"; let m ← binder "m" "Heap F"
      let bs ← fresh "bs"; let c1 ← fresh "c"; let c2 ← fresh "c"
      let dx ← fresh "d"; let mt ← fresh "mt"; let db ← fresh "d"
      let rest ← inv x dx env hin (.v v) (.v m) fun s1 => do
        let (pl, binds) ← patInv (.v v) pat mt (.v m)
        if ← isDead then return pl
        return pl ++ (← inv b db (binds ++ env) (.v m) dv dh fun s2 => k (s1 ++ s2))
      return [s!"obtain ⟨{v}, {m}, {bs}, {c1}, {c2}, {dx}, {mt}, {db}, rfl⟩ := {d}.letValue_inv"] ++ rest
    | .matchValue x arms =>
      let v ← binder "v" "SourceValue F"; let m ← binder "m" "Heap F"
      let bs ← fresh "bs"; let body ← fresh "body"; let c1 ← fresh "c"; let c2 ← fresh "c"
      let dx ← fresh "d"; let sel ← fresh "sel"; let db ← fresh "d"
      let rest ← inv x dx env hin (.v v) (.v m) fun s1 =>
        invArms arms (arms.length > 1) (arms.length ≥ tableArms) sel db env (.v v) (.v m) dv dh
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
  partial def letSegment (e : Expr F) (pat : Pattern F) (x b : Expr F) (d : String) (env : Env)
      (hin dv dh : T) (k : K) : M (List String) := do
    let s ← get
    let some body := s.body | throw "segment without a body"
    let some pos := body.find? e | throw "segment position"
    let pos := pos ++ [0]
    let names := env.map (·.1)
    let segName ← match s.segs.find? (·.1 == pos) with
      | some (_, n, _) => pure n
      | none => genSegment pos names x
    let v ← binder "v" "SourceValue F"; let m ← binder "m" "Heap F"
    let bs ← fresh "bs"; let c1 ← binder "cs" "List (Call F)"; let c2 ← fresh "c"
    let dx ← fresh "d"; let mt ← fresh "mt"; let db ← fresh "d"; let sg ← fresh "sg"
    addFact sg ([.s s!"«{s.fname}».{segName}"] ++ (env.map fun (_, t) => [Piece.s " ", .t t]).flatten ++
      [.s " ", .t hin, .s " ", .t (.v v), .s " ", .t (.v m), .s s!" {c1}"]) sg
    let (pl, binds) ← patInv (.v v) pat mt (.v m)
    let rest ← if ← isDead then pure pl else
      pure (pl ++ (← inv b db (binds ++ env) (.v m) dv dh fun s2 => k ([.sub c1] ++ s2)))
    return [s!"obtain ⟨{v}, {m}, {bs}, {c1}, {c2}, {dx}, {mt}, {db}, rfl⟩ := {d}.letValue_inv",
      s!"have {sg} := «{s.fname}».{segName.decapitalize} {dx}", s!"clear {dx}"] ++ rest

  /-- The segment at `pos`: its inductive and theorem, over the local environment `names`. -/
  partial def genSegment (pos : List Nat) (names : List String) (x : Expr F) : M String := do
    let saved ← get
    let segName := s!"Seg{saved.segs.size + 1}"
    let es := names.zipIdx.map fun (n, i) => s!"e{i}_{sanitize n}"
    set { saved with path := {}, ctors := #[], params := es ++ ["h", "r", "h'", "calls"], inSeg := true }
    let script ← inv x "d0" (names.zip (es.map T.v)) (.v "h") (.v "r") (.v "h'")
      (leaf s!"«{saved.fname}».{segName}")
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
    set { saved with counter := st.counter, names := st.names, abbrevs := st.abbrevs,
      work := st.work, lookups := st.lookups,
      segs := saved.segs.push (pos, segName, ind ++ "\n" ++ thm) }
    return segName

  partial def invArgs (es : List (Expr F)) (a : String) (env : Env) (hin : T)
      (items : List String) (dh : T) (k : K) : M (List String) := do
    match es, items with
    | [], [] =>
      assign dh hin
      return [s!"obtain ⟨rfl, rfl, rfl⟩ := {a}.nil_inv"] ++ (← k [])
    | e :: es, it :: its =>
      let vs ← fresh "vs"; let m ← binder "m" "Heap F"; let c1 ← fresh "c"; let c2 ← fresh "c"
      let dh' ← fresh "d"; let a' ← fresh "a"
      return [s!"obtain ⟨{it}, {vs}, {m}, {c1}, {c2}, rfl, {dh'}, {a'}, rfl⟩ := {a}.cons_inv"] ++
        (← inv e dh' env hin (.v it) (.v m) fun s1 =>
          invArgs es a' env (.v m) its dh fun s2 => k (s1 ++ s2))
    | _, _ => throw "argument arity"

  /-- Arms in order: the first matched (positive branch) or did not (negative). In a
  table (`table`: a dispatch of at least `tableArms` arms) whose scrutinee is a
  parameter, a matched arm drops the negations of the earlier arms: its own equation
  `x = template` implies them, and keeping them makes the paths quadratic. -/
  partial def invArms (arms : List (Pattern F × Expr F)) (multi table : Bool) (sel db : String)
      (env : Env) (V heap dv dh : T) (k : K) : M (List String) := do
    match arms with
    | [] => return [s!"exact (selectArm_nil_inv {sel}).elim"]
    | (p, b) :: rest =>
      let mt ← fresh "mt"; let nm ← fresh "nm"; let sel' ← fresh "sel"
      let saved := (← get).path
      if multi then modifyPath fun q => { q with tokens := q.tokens.push (armToken p) }
      let (pl, binds) ← patInv V p mt heap
      if table && !(← isDead) then
        let s ← get
        let Vr := V.resolve s.path.subst
        if (match Vr with | .v n => s.params.contains n | _ => false) then
          modifyPath fun q => { q with facts := q.facts.filter fun (_, _, _, subj) =>
            match subj with | some u => u.resolve q.subst != Vr | none => true }
      let pos ← if ← isDead then pure [] else inv b db (binds ++ env) heap dv dh k
      modify fun s => { s with path := saved }
      let (nl, dead) ← negArm V p nm
      let negRest ← if dead then pure [] else invArms rest multi table sel' db env V heap dv dh k
      modify fun s => { s with path := saved }
      return [s!"rcases selectArm_cons_inv {sel} with ⟨{mt}, rfl⟩ | ⟨{nm}, {sel'}⟩"] ++
        bullet (pl ++ pos) ++ bullet (nl ++ negRest)

  /-- What an unmatched arm tells about the scrutinee; `true` if impossible. -/
  partial def negArm (V : T) (p : Pattern F) (nm : String) : M (List String × Bool) := do
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
        else return ([s!"clear {nm}"], false)
      | _ => return ([s!"clear {nm}"], false)

  /-- Invert a successful match of `p` against `V`; returns the bindings. -/
  partial def patInv (V : T) (p : Pattern F) (mt : String) (heap : T) :
      M (List String × Env) := do
    match p with
    | .bind n => return ([s!"obtain rfl := matchPattern_bind_inv {mt}"], [(n, V)])
    | .wildcard => return ([s!"obtain rfl := matchPattern_wildcard_inv {mt}"], [])
    | .load p' =>
      let u ← binder "y" "SourceValue F"; let ld ← fresh "ld"; let mt' ← fresh "mt"
      addFact ld [.s "loadValue ", .t heap, .s " ", .t V, .s " = .ok ", .t (.v u)] ld
      let (ls, bs) ← patInv (.v u) p' mt' heap
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
        let subs ← subBinders ps
        let ls ← unifyPat V (.ctor lit c (subs.map .v)) hv
        let (mls, bs) ← listInv ps subs ml heap
        return ([s!"obtain ⟨{vs}, {hv}, -, {ml}⟩ := matchPattern_construct_inv {mt}",
          s!"rw [{lem}] at {hv}"] ++ ls ++ mls, bs)
      | .tuple ps | .array ps =>
        let kind := match p with | .tuple _ => "tuple" | _ => "array"
        match ← resolveT V with
        | .tuple us =>
          unless us.length == ps.length do throw "tuple pattern length"
          let ml ← fresh "ml"
          let (mls, bs) ← listInvConcrete ps us ml heap
          return ([s!"have {ml} := matchPattern_{kind}_tuple_inv {mt}"] ++ mls, bs)
        | .v _ =>
          let vs ← fresh "vs"; let hv ← fresh "hv"; let ml ← fresh "ml"
          let subs ← subBinders ps
          let ls ← unifyPat V (.tuple (subs.map .v)) hv
          if ← isDead then return ([s!"obtain ⟨{vs}, {hv}, -, {ml}⟩ := matchPattern_{kind}_inv {mt}"] ++ ls, [])
          let (mls, bs) ← listInv ps subs ml heap
          return ([s!"obtain ⟨{vs}, {hv}, -, {ml}⟩ := matchPattern_{kind}_inv {mt}"] ++ ls ++ mls, bs)
        | _ => throw "tuple pattern on a non-tuple"
      | .orElse _ _ _ => throw "or-pattern"
      | p => throw s!"pattern form ({patKind p})"

  partial def subBinders (ps : List (Pattern F)) : M (List String) :=
    ps.mapM fun
      | .bind n => namedBinder n "SourceValue F"
      | _ => binder "w" "SourceValue F"

  partial def listInv (ps : List (Pattern F)) (subs : List String) (ml : String) (heap : T) :
      M (List String × Env) := do
    match ps, subs with
    | [], [] => return ([s!"obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv {ml}"], [])
    | p :: ps, w :: ws =>
      let vs ← fresh "vs"; let b1 ← fresh "b"; let b2 ← fresh "b"
      let mt ← fresh "mt"; let ml' ← fresh "ml"
      let hd := s!"obtain ⟨{w}, {vs}, {b1}, {b2}, rfl, {mt}, {ml'}, rfl⟩ := matchListWith_cons_inv {ml}"
      let (l1, bs1) ← patInv (.v w) p mt heap
      if ← isDead then return (hd :: l1, bs1)
      let (l2, bs2) ← listInv ps ws ml' heap
      return (hd :: l1 ++ l2, bs1 ++ bs2)
    | _, _ => throw "pattern arity"

  partial def listInvConcrete (ps : List (Pattern F)) (us : List T) (ml : String) (heap : T) :
      M (List String × Env) := do
    match ps, us with
    | [], [] => return ([s!"obtain ⟨-, rfl⟩ := matchListWith_nil_inv {ml}"], [])
    | p :: ps, u :: us =>
      let b1 ← fresh "b"; let b2 ← fresh "b"; let mt ← fresh "mt"; let ml' ← fresh "ml"
      let hd := s!"obtain ⟨{b1}, {b2}, {mt}, {ml'}, rfl⟩ := matchListWith_cons_cons_inv {ml}"
      let (l1, bs1) ← patInv u p mt heap
      if ← isDead then return (hd :: l1, bs1)
      let (l2, bs2) ← listInvConcrete ps us ml' heap
      return (hd :: l1 ++ l2, bs1 ++ bs2)
    | _, _ => throw "pattern arity"
end

/-! ## One function -/


/-- Functions L4 needs whose paths multiply (a `let` bound to a match): generated under
larger caps, at a larger module cost. -/
def generous : List String := ["KernelWhnf::whnf_nd_const_head"]

/-- The path inductive and the inversion theorem of one function. -/
def function (src : Aiur.Generic.Source F) (f : Function F) (index : Nat)
    (maxChars : Nat := if generous.contains f.name then 2000000 else 200000) :
    Except String (String × Array (String × String × String) × Array (String × String × String) × Nat) := do
  if f.typeParams.length > 1 then throw "several type parameters"
  if f.name.startsWith "$" then throw "internal function"
  if ControlLower.hasControl f.body then throw "control"
  let tp := f.typeParams.head?
  let ps := f.params.map fun (n, _) => "x_" ++ n
  let params := ps ++ ["h", "r", "h'", "calls"]
  let env : Env := (f.params.map (·.1)).zip (ps.map .v)
  let leanName := s!"IxVM.{functionName f.name}"
  let body : M (List String) :=
    inv f.body "d0" env (.v "h") (.v "r") (.v "h'") (leaf s!"«{f.name}».Path")
  let maxLookups := if generous.contains f.name then 40000 else 3000
  let (script, st) ← body.run { counter := 1, params, src := some src, typeParam := tp, maxLookups,
    fname := f.name, leanName, body := some f.body, segment := segmented.contains f.name }
  -- a generic function is stated at its instance `t_<param>`
  let (tbind, targ, tibind, symbol, lookupThm, lookupDecl) := match tp with
    | none => ("", "", "", q f.name, s!"{leanName}.lookup", "")
    | some tp =>
      (s!"(t_{tp} : Generic.Ty) ", s!" t_{tp}", s!"\{t_{tp} : Generic.Ty} ",
       s!"(Instance.mk {q f.name} [t_{tp}]).symbol", s!"(«{f.name}».lookup t_{tp})",
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
  let ind := s!"/-- The evaluation paths of `{f.name}`: one constructor per combination of selected arms. -/\n" ++
    s!"inductive «{f.name}».Path {tbind}{pbind}(h : Heap F) (r : SourceValue F) (h' : Heap F)\n" ++
    "    (calls : List (Call F)) : Prop where\n" ++
    "\n".intercalate (st.ctors.toList.map (·.text)) ++ "\n"
  let thm := s!"/-- **Every observed derivation of `{f.name}` takes one of its paths.** -/\n" ++
    s!"theorem «{f.name}».obs {tibind}{ibind}\{h h' : Heap F} \{r : SourceValue F}\n" ++
    s!"    \{calls : List (Call F)} (ev : ObsFn W {symbol} {list ps} h r h' calls) :\n" ++
    s!"    «{f.name}».Path{targ}{pargs} h r h' calls := by\n" ++
    s!"  have d0 := ObsFn.function_inv (s := IxVM.source) {lookupThm}\n" ++
    s!"    (by simp [{leanName}, ControlLower.hasControl]) ev\n" ++
    s!"  simp only [{leanName}] at d0\n" ++
    "\n".intercalate (script.map ("  " ++ ·)) ++ "\n"
  let segTexts := String.join (st.segs.toList.map fun (_, _, t) => t ++ "\n")
  let text := lookupDecl ++ segTexts ++ ind ++ "\n" ++ thm
  if text.length > maxChars then throw s!"too large: {text.length / 1000} KB"
  return (text, st.names, st.abbrevs, st.ctors.size)

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


/-- Each function's result, in program order. -/
def results : List (String × Result) :=
  ((IxVM.functions.map (·.name)).zipIdx).filterMap fun (name, i) =>
    (IxVM.program.functions.find? (·.name == name)).map fun f => (name, function IxVM.source f i)

def render : List (System.FilePath × String) := assemble results

/-- `render`, printing each function's outcome and time. -/
def renderIO : IO (List (System.FilePath × String)) := do
  let mut rs : Array (String × Result) := #[]
  for (name, i) in (IxVM.functions.map (·.name)).zipIdx do
    let some f := IxVM.program.functions.find? (·.name == name) | continue
    let t0 ← IO.monoMsNow
    let r := function IxVM.source f i
    let tag := match r with
      | .ok (_, _, _, n) => s!"{n} paths"
      | .error e => s!"skipped ({e})"
    IO.eprintln s!"[obs-gen] {name}: {tag} {(← IO.monoMsNow) - t0}ms"
    rs := rs.push (name, r)
  return assemble rs.toList

end IxVM.ObsGen
