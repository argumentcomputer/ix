/-
  Canonical pretty-printer for the Ixon text format.

  Behavioral mirror of `crates/ixon/src/syntax/print.rs`: same doc
  engine (Wadler-style, group-local fitting on cached flat widths),
  same WIDTH/INDENT, same precedence and escaping rules — byte-for-byte
  identical output for equal ASTs, which is what makes the printed
  corpus a cross-language parity surface.
-/
module

public import Ix.IxonSyntax.AST
public import Ix.IxonSyntax.Parser

public section

namespace Ixon.Syntax
namespace Print

/-- Canonical layout width, in columns (chars). Part of the canonical
    form; must equal Rust `syntax::print::WIDTH`. -/
def WIDTH : Nat := 100

/-- Canonical indent step. -/
def INDENT : Nat := 2

/-! ## Doc engine -/

mutual

/-- Layout document; `width` caches the flattened width (`none` when a
    hard newline is inside), so grouping decisions are O(1). -/
inductive Doc where
  | mk (width : Option Nat) (kind : DocKind)

inductive DocKind where
  | text (s : String)
  | cat (ds : Array Doc)
  /-- Space when flat, newline when broken. -/
  | line
  /-- Always a newline. -/
  | hard
  | group (d : Doc)
  | nest (d : Doc)

end

instance : Inhabited Doc := ⟨.mk (some 0) (.text "")⟩

def Doc.width : Doc → Option Nat
  | .mk w _ => w

def Doc.kind : Doc → DocKind
  | .mk _ k => k

def text (s : String) : Doc := .mk (some s.length) (.text s)

def cat (ds : Array Doc) : Doc :=
  let width := ds.foldl (init := some 0) fun acc d =>
    match acc, d.width with
    | some a, some w => some (a + w)
    | _, _ => none
  .mk width (.cat ds)

def line : Doc := .mk (some 1) .line

def hard : Doc := .mk none .hard

def group (d : Doc) : Doc := .mk d.width (.group d)

def nest (d : Doc) : Doc := .mk d.width (.nest d)

/-- Render with group-local fitting; iterative, mirrors the Rust
    renderer exactly (including traversal order). Mode: `true` =
    flat. -/
partial def render (doc : Doc) (width : Nat) : String := Id.run do
  let mut out := ""
  let mut col := 0
  let mut stack : Array (Nat × Bool × Doc) := #[(0, false, doc)]
  while stack.size > 0 do
    let (ind, flat, d) := stack.back!
    stack := stack.pop
    match d.kind with
    | .text s =>
      out := out ++ s
      col := col + s.length
    | .cat ds =>
      for c in ds.reverse do
        stack := stack.push (ind, flat, c)
    | .line =>
      if flat then
        out := out.push ' '
        col := col + 1
      else
        out := out.push '\n' |>.pushn ' ' ind
        col := ind
    | .hard =>
      out := out.push '\n' |>.pushn ' ' ind
      col := ind
    | .nest c => stack := stack.push (ind + INDENT, flat, c)
    | .group c =>
      let f := match c.width with
        | some w => col + w ≤ width
        | none => false
      stack := stack.push (ind, f, c)
  return out

/-! ## Lexical spelling -/

open Parser (isIdFirst isIdRest isReserved)

/-- Can `s` print as a bare identifier component? -/
def isBareComponent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c0 :: rest =>
    isIdFirst c0 && rest.all isIdRest && !isReserved s

/-- Bare when possible, `«…»` otherwise; `num` components print as
    bare digits. -/
def componentStr : NameComponent → String
  | .str s => if isBareComponent s then s else s!"«{s}»"
  | .num n => toString n

def snameStr (n : SName) : String :=
  ".".intercalate (n.parts.toList.map componentStr)

def hashStr (h : HashRef) : String := s!"#{h.hex}"

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + n - 10)

/-- Lean-style string escaping (matches Rust `escape_string`). -/
def escapeString (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    if c == '"' then out := out ++ "\\\""
    else if c == '\\' then out := out ++ "\\\\"
    else if c == '\n' then out := out ++ "\\n"
    else if c == '\t' then out := out ++ "\\t"
    else if c == '\r' then out := out ++ "\\r"
    else if c.toNat < 0x20 || c.toNat == 0x7f then
      out := out ++ "\\x" |>.push (hexDigit (c.toNat / 16))
        |>.push (hexDigit (c.toNat % 16))
    else out := out.push c
  return out.push '"'

/-! ## Universes -/

/-- `max`/`imax` are operators in universe positions; parameters
    spelled that way must escape. -/
def uvarStr : NameComponent → String
  | .str s => if s == "max" || s == "imax" then s!"«{s}»" else componentStr (.str s)
  | c => componentStr c

/-- Fold nested `add`s (the grammar admits a single `+ n`). -/
def foldAdd : UnivExpr → Nat → UnivExpr × Nat
  | .add inner n _, acc => foldAdd inner (acc + n)
  | u, acc => (u, acc)

/-- `atomCtx`: position admits only a universe atom — compounds
    parenthesize. -/
partial def univStr (u : UnivExpr) (atomCtx : Bool) : String :=
  match u with
  | .nat n _ => toString n
  | .var c _ => uvarStr c
  | .add a n _ =>
    let (base, total) := foldAdd a n
    let s := s!"{univStr base false} + {total}"
    if atomCtx then s!"({s})" else s
  | .max a b _ =>
    let s := s!"max {univStr a true} {univStr b true}"
    if atomCtx then s!"({s})" else s
  | .imax a b _ =>
    let s := s!"imax {univStr a true} {univStr b true}"
    if atomCtx then s!"({s})" else s

def crefStr (c : ConstRef) : String := Id.run do
  let mut s := ""
  if let some n := c.name then
    s := s ++ snameStr n
  if let some h := c.hash then
    s := s ++ hashStr h
  if let some ls := c.levels then
    s := s ++ ".{" ++ ", ".intercalate (ls.toList.map (univStr · false)) ++ "}"
  return s

/-! ## Terms -/

/-- Precedence: 0 = fun/let, 1 = arrows, 2 = loose atoms (spines,
    `Type u`/`Sort u`, `proj`), 3 = closed atoms. `Type`/`Sort` sit at
    2 even argument-less so a spine argument can never be captured as
    their universe argument. -/
def termPrec : Term → Nat
  | .lam .. | .letE .. => 0
  | .pi .. | .arrow .. => 1
  | .sort .prop _ | .ref _ | .natLit .. | .strLit .. => 3
  | .app .. | .proj .. | .sort .. => 2

def binderNameStr : BinderName → String
  | .ident c _ => componentStr c
  | .anon _ => "_"

mutual

partial def termDoc (t : Term) (minPrec : Nat) : Doc :=
  let d := termDocBare t
  if termPrec t < minPrec then cat #[text "(", d, text ")"]
  else d

partial def termDocBare : Term → Doc
  | .ref c => text (crefStr c)
  | .sort k _ =>
    match k with
    | .prop => text "Prop"
    | .type none => text "Type"
    | .type (some u) => text s!"Type {univStr u true}"
    | .sort u => text s!"Sort {univStr u true}"
  | .natLit n _ => text (toString n)
  | .strLit s _ => text (escapeString s)
  | .app head args _ => Id.run do
    -- Flatten nested spines: `(f a) b` prints `f a b`.
    let mut h := head
    let mut all := args
    let mut go := true
    while go do
      match h with
      | .app h2 a2 _ =>
        all := a2 ++ all
        h := h2
      | _ => go := false
    let mut ds := #[termDoc h 3]
    for a in all do
      ds := ds.push line
      ds := ds.push (termDoc a 3)
    return group (nest (cat ds))
  | .lam binders body _ => Id.run do
    let mut ds := #[text "fun"]
    for b in binders do
      ds := ds.push (text " ")
      ds := ds.push (binderDoc b)
    ds := ds.push (text " =>")
    ds := ds.push (group (nest (cat #[line, termDoc body 0])))
    return cat ds
  | .pi binders body _ => Id.run do
    let mut ds := #[]
    for b in binders do
      ds := ds.push (binderDoc b)
      ds := ds.push (text " ")
    ds := ds.push (text "→")
    ds := ds.push (group (nest (cat #[line, termDoc body 1])))
    return cat ds
  | .arrow dom cod _ =>
    cat #[termDoc dom 2, text " →",
      group (nest (cat #[line, termDoc cod 1]))]
  | .letE nonDep name ty val body _ =>
    let kwS := if nonDep then "have" else "let"
    cat #[text s!"{kwS} {binderNameStr name} : ", termDoc ty 0,
      text " :=", group (nest (cat #[line, termDoc val 0])), text ";",
      hard, termDoc body 0]
  | .proj typeRef idx val _ =>
    cat #[text s!"proj {crefStr typeRef} {idx} ", termDoc val 3]

partial def binderDoc (b : BinderGroup) : Doc :=
  let (openS, closeS) := match b.info with
    | .default => ("(", ")")
    | .implicit => ("{", "}")
    | .strictImplicit => ("⦃", "⦄")
    | .instImplicit => ("[", "]")
  let inner :=
    if b.names.isEmpty then #[termDoc b.ty 0]
    else
      #[text (" ".intercalate (b.names.toList.map binderNameStr) ++ " : "),
        termDoc b.ty 0]
  group (cat (#[text openS] ++ inner ++ #[text closeS]))

end

/-! ## Declarations -/

def uparamsStr (ups : Array UParam) : String :=
  if ups.isEmpty then ""
  else ".{" ++ ", ".intercalate (ups.toList.map (uvarStr ·.name)) ++ "}"

/-- Header prefix: keyword, optional name, uparams. -/
def headStr (kwS : String) (name : Option SName) (ups : Array UParam)
    : String :=
  match name with
  | some n => s!"{kwS} {snameStr n}{uparamsStr ups}"
  | none =>
    if ups.isEmpty then kwS else s!"{kwS} {uparamsStr ups}"

def sigDoc (head : String) (ty : Term) : Doc :=
  cat #[text head, text " :", group (nest (cat #[line, termDoc ty 0]))]

partial def declDoc : Decl → Doc
  | .defn x =>
    let kwS := (if x.mods.isUnsafe then "unsafe " else "")
      ++ (if x.mods.isPartial then "partial " else "")
      ++ (match x.kw with
          | .defn => "def"
          | .thm => "theorem"
          | .opaq => "opaque")
    cat #[sigDoc (headStr kwS x.name x.uparams) x.ty, text " :=",
      group (nest (cat #[line, termDoc x.value 0]))]
  | .axio x =>
    let kwS := if x.isUnsafe then "unsafe axiom" else "axiom"
    sigDoc (headStr kwS x.name x.uparams) x.ty
  | .quot x =>
    let kind := match x.kind with
      | .type => "type"
      | .ctor => "ctor"
      | .lift => "lift"
      | .ind => "ind"
    sigDoc (headStr s!"quot {kind}" x.name x.uparams) x.ty
  | .indc x => Id.run do
    let kwS := if x.isUnsafe then "unsafe inductive" else "inductive"
    let head := headStr kwS x.name x.uparams
      ++ s!" (params := {x.params}) (indices := {x.indices})"
    let mut ds := #[sigDoc head x.ty]
    if !x.ctors.isEmpty then
      ds := ds.push (text " where")
      let mut items := #[]
      for c in x.ctors do
        items := items.push hard
        let chead := headStr "|" c.name #[]
          ++ s!" (params := {c.params}) (fields := {c.fields})"
        items := items.push (sigDoc chead c.ty)
      ds := ds.push (nest (cat items))
    return cat ds
  | .recr x => Id.run do
    let kwS := if x.isUnsafe then "unsafe recursor" else "recursor"
    let mut head := headStr kwS x.name x.uparams
      ++ s!" (params := {x.params}) (indices := {x.indices})"
      ++ s!" (motives := {x.motives}) (minors := {x.minors})"
    if x.k then head := head ++ " (k := true)"
    let mut ds := #[sigDoc head x.ty]
    if !x.rules.isEmpty then
      ds := ds.push (text " where")
      let mut items := #[]
      for r in x.rules do
        items := items.push hard
        items := items.push (cat #[
          text s!"| rule (fields := {r.fields}) :=",
          group (nest (cat #[line, termDoc r.rhs 0]))])
      ds := ds.push (nest (cat items))
    return cat ds
  | .muts members _ => Id.run do
    let mut items := #[]
    for m in members do
      items := items.push hard
      items := items.push (declDoc m)
    return cat #[text "mutual", nest (cat items), hard, text "end"]
  | .prj x =>
    let kwS := match x.kind with
      | .dprj => "dprj"
      | .iprj => "iprj"
      | .cprj => "cprj"
      | .rprj => "rprj"
    let base := s!"{headStr kwS x.name #[]} := {hashStr x.block} {x.idx}"
    text (match x.cidx with
      | some c => s!"{base} {c}"
      | none => base)

def importStr (i : ImportDecl) : String :=
  match i.prefixName with
  | some p => s!"import {snameStr p}{hashStr i.hash}"
  | none => s!"import {hashStr i.hash}"

end Print

/-! ## Public API -/

/-- Print a term (canonical form, no trailing newline). -/
def printTerm (t : Term) : String :=
  Print.render (Print.group (Print.termDoc t 0)) Print.WIDTH

/-- Print one declaration (canonical form, no trailing newline). -/
def printDecl (d : Decl) : String :=
  Print.render (Print.declDoc d) Print.WIDTH

/-- Print a whole file in canonical form: sections (imports block,
    declarations, optional trailing main expression) separated by
    blank lines, trailing newline. The version header is emitted only
    for versions ≥ 2 — absent means version 1, forever. The main
    expression's value prints at precedence 2 — `fun`/`let`/arrows
    parenthesize, so `⊢ (fun (x : A) => x) : A → A` rather than the
    visually ambiguous bare form (both reparse identically). -/
def printFile (f : File) : String := Id.run do
  let mut sections : Array String := #[]
  if f.version != 1 then
    sections := sections.push s!"ixon {f.version}"
  if !f.imports.isEmpty then
    sections := sections.push
      ("\n".intercalate (f.imports.toList.map Print.importStr))
  for d in f.decls do
    sections := sections.push (printDecl d)
  if let some m := f.main then
    let doc := Print.cat #[Print.text "⊢ ", Print.termDoc m.value 2,
      Print.text " :",
      Print.group (Print.nest (Print.cat #[Print.line, Print.termDoc m.ty 0]))]
    sections := sections.push (Print.render doc Print.WIDTH)
  return "\n\n".intercalate sections.toList ++ "\n"

end Ixon.Syntax
