import IxCC.Src.Syntax

/-! # The runtime view

The terms SrcEval can evaluate, and the relevant positions inside them
(design note 01 §5, 02 §3.3). A constant's runtime terms are its resolved
body: the `eqn` body, the `csimp` target, the declaration value of a safe
definition (or an allowlisted opaque), and the rules of a recursor; a `case`
key reaches its recursor. Relevant positions follow the installed tags at a
universe profile (D18): arguments and lets irrelevant at the profile, λ
domains, let types, sorts and Π types are never evaluated, so they are
skipped. The relevant closure is a set of instances `(constant, profile)`:
roots at the empty profile (every parameter zero, as `run` instantiates
them), and each reference at the profile its universe arguments give.

`Src.Relevance.check` (02) and `Src.Admit` (01) both walk this view. -/

namespace IxCC.Src

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
    match p.entry? c with
    | some e =>
      match e.decl with
      | .defn kind safety lvls type _ =>
        { p with consts := p.consts.insert c { e with decl := .defn kind safety lvls type t } }
      | _ => p
    | none => p
  | .eqn c =>
    match p.table.resolveOf c with
    | some (.eqn thm _) =>
      { p with table := { p.table with resolve := p.table.resolve.insert c (.eqn thm t) } }
    | _ => p
  | .rule r j =>
    match p.entry? r with
    | some e =>
      match e.decl with
      | .recr safe k lvls np nmot nmin ni ind rules type =>
        match rules[j]? with
        | some rule =>
          let rules := rules.set j { rule with rhs := t }
          let e' : ConstEntry := { e with decl := .recr safe k lvls np nmot nmin ni ind rules type }
          { p with consts := p.consts.insert r e' }
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
def runtimeKeys (p : Program) (c : CId) : List TermKey :=
  match p.table.resolveOf c with
  | some (.prim _) => []
  | some (.csimp ..) => []
  | some (.eqn ..) => [.eqn c]
  | some (.case _) => []
  | none =>
    match p.decl? c with
    | some (.recr _ _ _ _ _ _ _ _ rules _) => (List.range rules.length).map (.rule c)
    | some (.defn ..) => if p.isEvaluatedBody c then [.value c] else []
    | _ => []

/-- Constants reached through the table rather than a term, with their
universe arguments over `c`'s parameters: a `csimp` target and the recursor
under a `case` key (whose levels are the key's, `Table.checkCase`). -/
def runtimeRefs (p : Program) (c : CId) : List (CId × List Ixon.Univ) :=
  match p.table.resolveOf c with
  | some (.csimp g us _) => [(g, us)]
  | some (.case r) =>
    let lvls := ((p.decl? c).map Decl.lvls).getD 0
    [(r, (List.range lvls).map fun i => Ixon.Univ.var i.toUInt64)]
  | _ => []

end Program

/-- A constant at a universe profile: a node of the relevant closure (D18).
Relevance, `RecKind` and field classes are decided per instance. -/
abbrev Inst := CId × Profile

namespace Term

/-- Constants in relevant positions at profile `prof`, each at its
instantiated profile, prepended to `acc` (so the result lists them right to
left). A position is skipped where its class is irrelevant at `prof`, and a
λ's body where the λ is a proof at `prof` (the A1 guard never lets SrcEval
into it). -/
def relevantRefs (prof : Profile) : Term → List Inst → List Inst
  | .const c us, acc => (c, prof.inst us) :: acc
  | .app f a _ r, acc =>
    let acc := relevantRefs prof f acc
    if r.irrP prof then acc else relevantRefs prof a acc
  | .lam b _ t, acc => if b.propWhen.holdsP prof then acc else relevantRefs prof t acc
  | .letE _ r _ v b, acc =>
    let acc := if r.irrP prof then acc else relevantRefs prof v acc
    relevantRefs prof b acc
  | .proj _ _ e, acc => relevantRefs prof e acc
  | _, acc => acc

/-- Constants in positions relevant at *some* profile (every class but the
always-irrelevant ones), left to right: what the annotator must annotate. -/
def anyRelevantConsts : Term → Array CId → Array CId
  | .const c _, acc => acc.push c
  | .app f a _ r, acc =>
    let acc := anyRelevantConsts f acc
    if r.alwaysIrr then acc else anyRelevantConsts a acc
  | .lam _ _ t, acc => anyRelevantConsts t acc
  | .letE _ r _ v b, acc =>
    let acc := if r.alwaysIrr then acc else anyRelevantConsts v acc
    anyRelevantConsts b acc
  | .proj _ _ e, acc => anyRelevantConsts e acc
  | _, acc => acc

end Term

namespace Program

/-- The instances one visit of `(c, prof)` reaches, left to right: the
relevant references of each runtime term, then the table references. -/
def instRefs (p : Program) (c : CId) (prof : Profile) : List Inst :=
  let terms := (p.runtimeKeys c).filterMap p.termOf
  let fromTerms := terms.foldl (fun acc t => t.relevantRefs prof acc) []
  fromTerms.reverse ++ (p.runtimeRefs c).map fun (d, us) => (d, prof.inst us)

/-- A profile at a constant's level count (missing entries read as zero), so
that one instance has one spelling. -/
def instOf (p : Program) (c : CId) (prof : Profile) : Inst :=
  (c, prof.normalize (((p.decl? c).map Decl.lvls).getD 0))

end Program

end IxCC.Src
