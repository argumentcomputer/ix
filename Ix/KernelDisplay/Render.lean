import IxC.Kernel.Core
import IxC.Kernel.ExprOps
import Lean.Data.Name

/-! # Printing terms with Lean's names (IxC step 6b, display only)

`.meta` and `.source` terms carry each binder's Lean name and binder info, and
a failure the terms it is about and the binders it was thrown under
(`Ix.Kernel.BinderMeta.display`, `Ix.Kernel.FailureDisplay`). This module
prints them in the style of Lean's delaborator (`ppExpr`), under Lean's
default options except three that need Lean's elaborator: no notation, no
coercions, full names (IxC has no open namespaces); proofs are printed.

* **Binders.** A binder's name is Lean's with its macro scopes erased; an
  anonymous one suggests `a`. A name already in scope is kept when the body
  does not mention the outer variable (`pp.safeShadowing`), and otherwise
  freshened with `_1`, `_2`, … (`LocalContext.getUnusedName`).
  `fun x y => b` (`pp.funBinderTypes false`), `{x}`, `⦃x⦄`, `[C]`.
* **Π.** A non-dependent explicit binder prints as `α → β`, except a
  proposition over a domain that is not one (Lean's RFC #1834): then, as a
  dependent binder, `∀ (x : α), β` for a proposition and `(x : α) → β` for a
  type, grouped as Lean groups (same binder info, same domain). Whether a Π
  is a proposition is read from its validated datum `pw` when written, and
  otherwise from a light inference over the constants' types (`isProp?`).
* **Free variables** print as the name of the binder the failure was thrown
  under at their depth (`Cx.fvarName`), else `x✝`, Lean's inaccessible style.
* **Applications** hide the implicit arguments of a constant's (or a free
  variable's) type (`pp.explicit false`); **universe** arguments of
  constants are hidden (`pp.universes false`); `Sort 0` is `Prop`, `Sort 1`
  is `Type`, `Sort (u+1)` is `Type u`.
* **Projections** are `e.1` (one-based, Lean's raw `Expr.proj`), literals
  Lean's, and a print stops at `maxSteps` nodes with `⋯`.

Everything here is safe code and reads nothing by itself: the display reads
are a parameter (`Peek`), which `Ix.KernelDisplay.Peek` supplies with the one
display-only `unsafe` read. Without it (`Peek.none`) every name is anonymous. -/

namespace Ix.KernelDisplay

open Ix.Kernel (Expr Key Mode Level BinderInfo BinderDisplay CheckError FailureDisplay MsgPart Msg)

/-- How a renderer reads display annotations (a `Squash` hides its value from
safe code: `Ix.KernelDisplay.Peek.peekAll` is the read). -/
structure Peek where
  binder : Squash BinderDisplay → BinderDisplay
  letName : Squash Ix.Kernel.Name → Ix.Kernel.Name
  failure : {md : Mode} → Squash (FailureDisplay md) → FailureDisplay md

/-- No read: every binder anonymous, every failure without terms. -/
def Peek.none : Peek := ⟨fun _ => {}, fun _ => .anonymous, fun _ => {}⟩

instance : Inhabited Peek := ⟨Peek.none⟩

/-- What a print reads besides the term. -/
structure Cx (md : Mode) where
  peek : Peek := Peek.none
  /-- a constant's name -/
  spell : Key md → String := fun k => toString k
  /-- level parameter `i`'s name -/
  levelName : Nat → String := fun i => s!"u_{i + 1}"
  /-- a constant's type (binder infos and proposition tests) -/
  constType : Key md → Option (Expr md) := fun _ => none
  /-- the name of the free variable at a depth -/
  fvarName : Nat → Option Ix.Kernel.Name := fun _ => none
  /-- a constant's name in a failure's message, if not `spell` (`.meta`'s
  messages spell `name@hex8`, its terms the name alone) -/
  msgSpell : Option (Key md → String) := none
  maxSteps : Nat := 5000

/-! ## Names -/

/-- The checker's name as Lean's. -/
def leanName : Ix.Kernel.Name → Lean.Name
  | .anonymous => .anonymous
  | .str p s => .str (leanName p) s
  | .num p n => .num (leanName p) n

/-- A name as Lean prints it. -/
def nameStr (n : Lean.Name) : String := n.toString

/-- A free variable's name as Lean prints a local: a hygienic one (macro
scopes) erased and marked inaccessible, `x✝`; none is `x✝`. -/
def fvarStr (n : Lean.Name) : String :=
  if n.isAnonymous then "x✝"
  else if n.hasMacroScopes then nameStr n.eraseMacroScopes ++ "✝"
  else nameStr n

/-- A binder's display name: Lean's with macro scopes erased, `a` for none. -/
def binderName (n : Ix.Kernel.Name) : Lean.Name :=
  let n := leanName n
  if n.isAnonymous then `a else n.eraseMacroScopes

/-! ## Levels -/

/-- Lean's level printing (`Level.PP`): numerals, `u + n`, `max u v`,
`imax u v`; `paren` parenthesizes a compound level (an argument), `k` the
successors above. -/
def levelAux (cx : Cx md) (paren : Bool) (k : Nat) : Level → String
  | .zero => toString k
  | .succ u => levelAux cx paren (k + 1) u
  | .param i => offset (cx.levelName i) k
  | .max u v => wrapOffset s!"max {levelAux cx true 0 u} {levelAux cx true 0 v}" k
  | .imax u v => wrapOffset s!"imax {levelAux cx true 0 u} {levelAux cx true 0 v}" k
where
  offset (s : String) (k : Nat) : String :=
    if k == 0 then s else if paren then s!"({s} + {k})" else s!"{s} + {k}"
  wrapOffset (s : String) (k : Nat) : String :=
    let s := if k == 0 then s else s!"{s} + {k}"
    if paren then s!"({s})" else s

/-- A level, printed. -/
def levelStr (cx : Cx md) (paren : Bool) (u : Level) : String := levelAux cx paren 0 u

/-- `Sort u` as Lean prints it: `Prop`, `Type`, `Type u`, `Sort u`. -/
def sortStr (cx : Cx md) (u : Level) : String × Bool :=
  match u with
  | .zero => ("Prop", true)
  | .succ .zero => ("Type", true)
  | .succ v => (s!"Type {levelStr cx true v}", false)
  | v => (s!"Sort {levelStr cx true v}", false)

/-! ## Scopes and light inference -/

/-- A bound variable in scope: its printed name and its type (relative to the
scope outside it). -/
structure Var (md : Mode) where
  name : Lean.Name
  type : Expr md

/-- The bound variables, innermost first, and the free variables' names. -/
structure Scope (md : Mode) where
  vars : List (Var md) := []
  fvars : Nat → Option Lean.Name := fun _ => none

/-- A `bvar`'s type in scope, lifted to the current position. -/
def Scope.bvarType? (sc : Scope md) (i : Nat) : Option (Expr md) :=
  (sc.vars[i]?).map fun v => v.type.liftLooseBVars (i + 1) 0

/-- Is a name in use by a bound variable or a free variable? -/
def Scope.uses (sc : Scope md) (n : Lean.Name) (maxDepth : Nat) : Bool :=
  sc.vars.any (·.name == n) || (List.range maxDepth).any (sc.fvars · == some n)

/-- Does `e` mention, at binder depth `k` inside it, a variable named `n`: a
loose `bvar (k + i)` naming the scope's `i`-th variable, or a free variable of
that name? Pruned by the cached ranges. -/
def mentionsName (sc : Scope md) (n : Lean.Name) : Nat → Expr md → Bool
  | k, e =>
    if e.bvarBRaw ≤ k && e.fvarBRaw == 0 then false else
    match e with
    | .bvar i => i ≥ k && (sc.vars[i - k]?).any (·.name == n)
    | .fvar d _ => sc.fvars d == some n
    | .app f a => mentionsName sc n k f || mentionsName sc n k a
    | .lam t b _ | .forallE t b _ => mentionsName sc n k t || mentionsName sc n (k + 1) b
    | .letE t v b _ =>
      mentionsName sc n k t || mentionsName sc n k v || mentionsName sc n (k + 1) b
    | .proj _ _ e => mentionsName sc n k e
    | _ => false

/-- **A fresh name for a binder over `body`** (`Delaborator.getUnusedName`):
the suggestion when no variable in scope has it, or when the body does not
mention the one that has it (safe shadowing), else the first unused
`suggestion_i`. `avoid`: names of the same `fun` group. -/
def unusedName (sc : Scope md) (suggestion : Lean.Name) (body : Expr md) (depth : Nat)
    (avoid : List Lean.Name := []) : Lean.Name :=
  if !sc.uses suggestion depth && !avoid.contains suggestion then suggestion
  else if !avoid.contains suggestion && !mentionsName sc suggestion 1 body then suggestion
  else Id.run do
    let mut i := 1
    for _ in [0:sc.vars.length + depth + avoid.length + 2] do
      let c := suggestion.appendIndexAfter i
      if !sc.uses c depth && !avoid.contains c then return c
      i := i + 1
    return suggestion.appendIndexAfter i

/-- The binder telescope's final codomain after `n` arguments, if it is
reached syntactically. -/
def codomainAfter : Nat → Expr md → Option (Expr md)
  | 0, e => some e
  | n + 1, .forallE _ b _ => codomainAfter n b
  | _, _ => none

/-- The binder infos of a type's ∀-telescope. -/
def telescopeInfos (peek : Peek) : Expr md → List BinderInfo
  | .forallE _ b m => (peek.binder m.display).info :: telescopeInfos peek b
  | _ => []

/-- The type of a spine's head, if the light inference knows it. -/
def headType? (cx : Cx md) (sc : Scope md) : Expr md → Option (Expr md)
  | .const k _ => cx.constType k
  | .fvar _ ty => some ty
  | .bvar i => sc.bvarType? i
  | _ => none

/-- **Is the type `e` a proposition?** `some true`/`some false` when the
light inference decides: a Π by its validated datum `pw`, else by its body; a
sort is not; an application by its head's type's codomain, when that is a
literal sort. `none` otherwise. -/
def isProp? (cx : Cx md) (sc : Scope md) : Expr md → Option Bool
  | .sort _ => some false
  | .forallE t b m =>
    match m.pw.toList? with
    | some [] => some true
    | some _ => isProp? cx { sc with vars := ⟨`x, t⟩ :: sc.vars } b
    | none => isProp? cx { sc with vars := ⟨`x, t⟩ :: sc.vars } b
  | .lit _ => some false
  | e =>
    let h := e.getAppFn
    let n := e.getAppArgs.length
    match (headType? cx sc h).bind (codomainAfter n) with
    | some (.sort .zero) => some true
    | some (.sort _) => some false
    | _ => none

/-! ## Terms -/

/-- Precedences: a binder form or `let` (0), an arrow (25), an application
(1023), an atom (1024). -/
abbrev Prec := Nat

/-- Parenthesize `s` (of precedence `p`) where `q` is required. -/
def paren (s : String) (p q : Prec) : String := if p < q then s!"({s})" else s

/-- The printer's monad: the nodes printed so far. -/
abbrev PM := StateM Nat

/-- One more node; `false` once the budget is spent. -/
def tick (cx : Cx md) : PM Bool := do
  let n ← get
  set (n + 1)
  return n < cx.maxSteps

/-- A string literal, as Lean writes it. -/
def strLit (s : String) : String := s.quote

/-- Does `e` mention its loose `bvar k`? Pruned by the cached bound. -/
def mentionsBVar (k : Nat) (e : Expr md) : Bool :=
  if e.bvarBRaw ≤ k then false else
  match e with
  | .bvar i => i == k
  | .fvar _ t => mentionsBVar k t
  | .app f a => mentionsBVar k f || mentionsBVar k a
  | .lam t b _ | .forallE t b _ => mentionsBVar k t || mentionsBVar (k + 1) b
  | .letE t v b _ => mentionsBVar k t || mentionsBVar k v || mentionsBVar (k + 1) b
  | .proj _ _ e => mentionsBVar k e
  | _ => false

/-- One binder of a Π chain: an arrow (its domain printed), or a binder (a
proposition's or a type's, its info, name, printed domain, and whether the
body mentions it). -/
inductive PiItem where
  | arrow (dom : String) (prec : Prec)
  | binder (prop : Bool) (info : BinderInfo) (name : String) (dom : String) (mentions : Bool)

/-- A Π chain's groups: an arrow, or binders with one info and domain. -/
inductive PiGroup where
  | arrow (dom : String) (prec : Prec)
  | binder (prop : Bool) (info : BinderInfo) (names : List String) (dom : String) (mentions : Bool)

/-- Lean's grouping (`shouldGroupWithNext`): consecutive binders with the
same kind, info and domain, not instance-implicit. -/
def groupItems (items : List PiItem) : List PiGroup :=
  items.foldr (init := []) fun item acc =>
    match item, acc with
    | .binder p i n d m, .binder p' i' ns d' m' :: rest =>
      if p == p' && i == i' && d == d' && i != .instImplicit then
        .binder p i (n :: ns) d (m || m') :: rest
      else .binder p i [n] d m :: acc
    | .binder p i n d m, _ => .binder p i [n] d m :: acc
    | .arrow d q, _ => .arrow d q :: acc

/-- A group's bracket: `(x y : α)`, `{x : α}`, `⦃x : α⦄`, `[inst : C]` or
`[C]` (an instance binder the body does not mention). -/
def bracket : BinderInfo → List String → String → Bool → String
  | .default, ns, d, _ => s!"({" ".intercalate ns} : {d})"
  | .implicit, ns, d, _ => s!"\{{" ".intercalate ns} : {d}}"
  | .strictImplicit, ns, d, _ => s!"⦃{" ".intercalate ns} : {d}⦄"
  | .instImplicit, ns, d, m => if m then s!"[{" ".intercalate ns} : {d}]" else s!"[{d}]"

/-- A Π chain, printed over its printed body (`delabForall`): `α → β`;
`∀ g₁ g₂, β` for propositions, the groups of one `∀`; `(x : α) → β` for
types. -/
def renderGroups : List PiGroup → String × Prec → String × Prec
  | [], body => body
  | .arrow d q :: rest, body => (s!"{paren d q 26} → {(renderGroups rest body).1}", 25)
  | .binder prop i ns d m :: rest, body =>
    let g := bracket i ns d m
    let (s, p) := renderGroups rest body
    if prop then
      if p == 0 && s.startsWith "∀ " then (s!"∀ {g} {s.drop 2}", 0)
      else (s!"∀ {g}, {s}", 0)
    else (s!"{g} → {s}", 25)

/-- A `fun` binder: its printed name, info and domain. -/
structure FunBinder (md : Mode) where
  name : Lean.Name
  info : BinderInfo
  dom : Expr md

/-- `fun` binders as Lean groups them (`delabBinders`): explicit ones bare,
consecutive implicit (strict implicit) ones with one domain in one bracket,
`{α β γ}`; an instance binder alone, `[inst]`. -/
def funGroups : List (FunBinder md) → List String
  | [] => []
  | b :: rest =>
    match b.info with
    | .default => nameStr b.name :: funGroups rest
    | .instImplicit => s!"[{nameStr b.name}]" :: funGroups rest
    | info =>
      let same := rest.takeWhile fun c => c.info == info && c.dom == b.dom
      let names := " ".intercalate ((b :: same).map (nameStr ·.name))
      let shown := if info == .implicit then s!"\{{names}}" else s!"⦃{names}⦄"
      shown :: funGroups (rest.drop same.length)
termination_by bs => bs.length
decreasing_by all_goals simp_wf <;> omega

mutual
/-- **A term, printed** under the scope `sc` (module docstring), with its
precedence; `fuel` bounds the nesting, `cx.maxSteps` the nodes. -/
def term (cx : Cx md) (sc : Scope md) (depth : Nat) : Nat → Expr md → PM (String × Prec)
  | 0, _ => pure ("⋯", 1024)
  | fuel + 1, e => do
    unless ← tick cx do return ("⋯", 1024)
    match e with
    | .bvar i =>
      match sc.vars[i]? with
      | some v => return (nameStr v.name, 1024)
      | none => return (s!"#{i}", 1024)
    | .fvar d _ =>
      match sc.fvars d with
      | some n => return (fvarStr n, 1024)
      | none => return ("x✝", 1024)
    | .sort u => let (s, atom) := sortStr cx u; return (s, if atom then 1024 else 1023)
    | .const k _ => return (cx.spell k, 1024)
    | .lit (.natVal n) => return (toString n, 1024)
    | .lit (.strVal s) => return (strLit s, 1024)
    | .proj _ i b => do
      let (s, p) ← term cx sc depth fuel b
      return (s!"{paren s p 1024}.{i + 1}", 1024)
    | .app f a => app cx sc depth fuel f [a]
    | .lam t b m => lam cx sc depth fuel [] (.lam t b m)
    | .forallE t b m => pi cx sc depth fuel [] (.forallE t b m)
    | .letE t v b l => do
      let n := unusedName sc (binderName (cx.peek.letName l.display)) b depth
      let (sv, _) ← term cx sc depth fuel v
      let (sb, _) ← term cx { sc with vars := ⟨n, t⟩ :: sc.vars } depth fuel b
      -- a non-dependent let is Lean's `have`
      let kw := if l.contract.nonDep then "have" else "let"
      return (s!"{kw} {nameStr n} := {sv}; {sb}", 0)

/-- An application spine `f a₁ … aₙ` (`args` the arguments seen so far, the
innermost first): the implicit arguments of a known head type hidden. -/
def app (cx : Cx md) (sc : Scope md) (depth : Nat) :
    Nat → Expr md → List (Expr md) → PM (String × Prec)
  | 0, _, _ => pure ("⋯", 1024)
  | fuel + 1, .app g a, args => app cx sc depth fuel g (a :: args)
  | fuel + 1, head, args => do
    let infos := match headType? cx sc head with
      | some ty => telescopeInfos cx.peek ty
      | none => []
    let (sh, ph) ← term cx sc depth fuel head
    let mut out := paren sh ph 1023
    let mut shown := 0
    for (a, i) in args.zipIdx do
      if (infos[i]?).getD .default == .default then
        let (sa, pa) ← term cx sc depth fuel a
        -- a `fun` last argument needs no parentheses (`Exists fun j => P j`)
        let last := i + 1 == args.length && a matches .lam ..
        out := out ++ " " ++ (if last then sa else paren sa pa 1024)
        shown := shown + 1
    return (out, if shown == 0 then ph else 1023)

/-- `fun` binders, grouped (`delabLam`, `pp.funBinderTypes false`): `names`
the printed binders so far. -/
def lam (cx : Cx md) (sc : Scope md) (depth : Nat) :
    Nat → List (FunBinder md) → Expr md → PM (String × Prec)
  | 0, _, _ => pure ("⋯", 1024)
  | fuel + 1, names, .lam t b m => do
    let d := cx.peek.binder m.display
    let n := unusedName sc (binderName d.name) b depth (names.map (·.name))
    lam cx { sc with vars := ⟨n, t⟩ :: sc.vars } depth fuel (names ++ [⟨n, d.info, t⟩]) b
  | fuel + 1, names, body => do
    let (sb, _) ← term cx sc depth fuel body
    return (s!"fun {" ".intercalate (funGroups names)} => {sb}", 0)

/-- A Π chain (`delabForall`): `items` the binders printed so far. -/
def pi (cx : Cx md) (sc : Scope md) (depth : Nat) :
    Nat → List PiItem → Expr md → PM (String × Prec)
  | 0, _, _ => pure ("⋯", 1024)
  | fuel + 1, items, .forallE t b m => do
    let d := cx.peek.binder m.display
    let prop := (isProp? cx sc (.forallE t b m)).getD false
    let mentions := mentionsBVar 0 b
    let explicit := d.info == .default
    -- RFC #1834: a proposition over a domain that is not one prints with `∀`
    let dep := mentions || (prop && explicit && !(isProp? cx sc t).getD false)
    let (st, pt) ← term cx sc depth fuel t
    if !dep && explicit then
      pi cx { sc with vars := ⟨.anonymous, t⟩ :: sc.vars } depth fuel
        (items ++ [.arrow st pt]) b
    else
      let n := unusedName sc (binderName d.name) b depth
      pi cx { sc with vars := ⟨n, t⟩ :: sc.vars } depth fuel
        (items ++ [.binder prop d.info (nameStr n) st mentions]) b
  | fuel + 1, items, body => do
    let r ← term cx sc depth fuel body
    return renderGroups (groupItems items) r
end

/-- The nesting a print descends at most. -/
def printFuel : Nat := 100000

/-- **A term, printed with names** (module docstring), its free variables
named by `cx.fvarName`. -/
def renderTerm (cx : Cx md) (e : Expr md) : String :=
  let sc : Scope md := { fvars := fun d => (cx.fvarName d).map leanName }
  ((term cx sc e.fvarBRaw printFuel e).run' 0).1

/-- A failure's display (the first prose part's), read with `cx.peek`. -/
def failureDisplay (cx : Cx md) (e : CheckError md) : FailureDisplay md :=
  match e.msg.find? (· matches .text ..) with
  | some (.text _ d) => cx.peek.failure d
  | _ => {}

/-- **A failure, printed with names**: the verdict and the message as the
mode's renderer spells them, then the terms it is about, each after its role
and indented, as Lean's kernel messages lay them out; free variables named
after the binders the failure was thrown under (the innermost binder recorded
at a depth names that depth's variable). -/
def renderFailure (cx : Cx md) (e : CheckError md) : String :=
  let disp := failureDisplay cx e
  let names : Nat → Option Ix.Kernel.Name := fun d =>
    (disp.binders.reverse.find? (·.1 == d)).map fun (_, m) => (cx.peek.binder m.display).name
  let cx := { cx with fvarName := fun d => names d <|> cx.fvarName d }
  let head := e.render (cx.msgSpell.getD cx.spell)
  disp.terms.foldl (fun acc (role, t) => acc ++ s!"\n{role}\n  {renderTerm cx t}") head

end Ix.KernelDisplay
