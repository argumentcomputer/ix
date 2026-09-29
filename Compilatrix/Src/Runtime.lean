import Compilatrix.Src.Syntax

/-! # The runtime view

The terms SrcEval can evaluate, and the relevant positions inside them
(design note 01 §5, 02 §3.3). A constant's runtime terms are its resolved
body: the `eqn` body, the `csimp` target, the declaration value of a safe
definition (or an allowlisted opaque), and the rules of a recursor; a `case`
key reaches its recursor. Relevant positions follow the installed tags:
`irr` arguments, λ domains, let types, irrelevant let values, sorts and Π
types are never evaluated, so they are skipped.

`Src.Relevance.check` (02) and `Src.Admit` (01) both walk this view. -/

namespace Compilatrix.Src

/-- A runtime term of a program. -/
inductive TermKey where
  /-- The value of a definition. -/
  | value (c : CId)
  /-- The body of `c`'s `eqn` entry. -/
  | eqn (c : CId)
  /-- Rule `j` of recursor `r`. -/
  | rule (r : CId) (j : Nat)
  deriving BEq, Hashable, Repr, Inhabited

namespace Program

def termOf (p : Program) : TermKey → Option Term
  | .value c =>
    match p.decl? c with
    | some (.defn _ _ _ _ v) => some v
    | _ => none
  | .eqn c =>
    match p.table.resolveOf c with
    | some (.eqn _ body) => some body
    | _ => none
  | .rule r j =>
    match p.decl? r with
    | some (.recr _ _ _ _ _ _ _ _ rules _) => rules[j]?.map (·.rhs)
    | _ => none

/-- Replace one runtime term (used by relevance installation and Lazify). -/
def setTerm (p : Program) (key : TermKey) (t : Term) : Program :=
  match key with
  | .value c =>
    match p.consts[c]? with
    | some e =>
      match e.decl with
      | .defn kind safety lvls type _ =>
        { p with consts := p.consts.set! c { e with decl := .defn kind safety lvls type t } }
      | _ => p
    | none => p
  | .eqn c =>
    match p.table.resolveOf c with
    | some (.eqn thm _) =>
      { p with table := { p.table with resolve := p.table.resolve.set! c (some (.eqn thm t)) } }
    | _ => p
  | .rule r j =>
    match p.consts[r]? with
    | some e =>
      match e.decl with
      | .recr safe k lvls np nmot nmin ni ind rules type =>
        match rules[j]? with
        | some rule =>
          let rules := rules.set! j { rule with rhs := t }
          let e' : ConstEntry := { e with decl := .recr safe k lvls np nmot nmin ni ind rules type }
          { p with consts := p.consts.set! r e' }
        | none => p
      | _ => p
    | none => p

/-- Whether a reference to `c` evaluates a runtime term of `c` (δ). -/
def isEvaluatedBody (p : Program) (c : CId) : Bool :=
  match p.decl? c with
  | some (.defn .defn .safe ..) => true
  | some (.defn .opaq .safe ..) => p.table.isOpaqueByValue c
  | _ => false

/-- The runtime terms reached by a relevant reference to `c`. -/
def runtimeKeys (p : Program) (c : CId) : Array TermKey :=
  match p.table.resolveOf c with
  | some (.prim _) => #[]
  | some (.csimp ..) => #[]
  | some (.eqn ..) => #[.eqn c]
  | some (.case _) => #[]
  | none =>
    match p.decl? c with
    | some (.recr _ _ _ _ _ _ _ _ rules _) => (Array.range rules.size).map (.rule c)
    | some (.defn ..) => if p.isEvaluatedBody c then #[.value c] else #[]
    | _ => #[]

/-- Constants reached through the table rather than a term: a `csimp`
target and the recursor under a `case` key. -/
def runtimeRefs (p : Program) (c : CId) : Array CId :=
  match p.table.resolveOf c with
  | some (.csimp g _ _) => #[g]
  | some (.case r) => #[r]
  | _ => #[]

end Program

namespace Term

/-- Constants in relevant positions, left to right (with repetitions). -/
def relevantConsts : Term → Array CId → Array CId
  | .const c _, acc => acc.push c
  | .app f a m, acc =>
    let acc := relevantConsts f acc
    if m == .irr then acc else relevantConsts a acc
  | .lam _ _ t, acc => relevantConsts t acc
  | .letE _ r _ v b, acc =>
    let acc := if r == .rel then relevantConsts v acc else acc
    relevantConsts b acc
  | .proj _ _ e, acc => relevantConsts e acc
  | _, acc => acc

end Term

end Compilatrix.Src
