import Compilatrix.Src.Runtime

/-! # The relevance annotation

Its format and installation (design note 02 §3.1). The annotation is
carried beside the Ixon bytes (D3): per-constant `ConstRel`, per-constructor
`CtorRel`, and node tags for every runtime term. `install` writes the node
tags into the Src terms: `Binder.rel` and `Binder.propWhen` on λs, the `Rel`
of arguments and the `Rel` of lets.

Relevance is level-exact (D18): a `proof` class carries the zero condition
over its constant's universe parameters under which the position is a proof,
and a `FieldClass` the condition over its constructor's parameters. A
position is decided at an instance's levels (SrcEval) or profile (the
checker, `Admit`, erasure).

Node tags cover the positions of a term that are relevant at *some*
instance, in the order `Term.tagOrder` gives: a λ's tag precedes its body;
an application's function comes first, then its argument's tag, then (unless
the argument is irrelevant at every instance) the argument; a let's tag
precedes its value (on the same condition) and its body. Always-irrelevant
subterms (λ domains, let types, types and always-proofs as arguments or let
values, sorts and Π types) carry no tags: SrcEval never evaluates them, and
erasure maps them to □ without looking inside. -/

namespace Compilatrix.Src.Relevance

/-- Class of a constructor field, over the constructor's universe
parameters: kept, a proof where `when` holds (kept elsewhere), or a type. -/
inductive FieldClass where
  | keep
  | proof (when : PropWhen)
  | type
  deriving BEq, DecidableEq, Repr, Inhabited

namespace FieldClass

/-- Dropped exactly where this holds. -/
def dropWhen : FieldClass → PropWhen
  | .keep => .never
  | .proof w => w
  | .type => .always

/-- Dropped at a profile. -/
def dropP (prof : Profile) (c : FieldClass) : Bool := c.dropWhen.holdsP prof

/-- A field class from a position class. -/
def ofRel : Rel → FieldClass
  | .rel => .keep
  | .proof w => .proof w
  | .type => .type

/-- Dropped at every instance. -/
def alwaysDropped (c : FieldClass) : Bool := c.dropWhen == .always

/-- A proof field at every instance. -/
def prf : FieldClass := .proof .always

end FieldClass

structure CtorRel where
  fields : Array FieldClass
  deriving BEq, Repr, Inhabited

/-- A constant's own class and its leading Π telescope's binder classes,
over the constant's universe parameters. -/
structure ConstRel where
  result : Rel
  params : Array Rel
  deriving BEq, Repr, Inhabited

inductive Tag where
  | lam (r : Rel) (pw : PropWhen)
  | arg (r : Rel)
  | letE (r : Rel)
  deriving BEq, Repr, Inhabited

structure Ann where
  consts : Array (Option ConstRel) := #[]
  ctors : Array (Option CtorRel) := #[]
  nodes : Array (TermKey × Array Tag) := #[]
  deriving Inhabited

namespace Ann

def constRel? (a : Ann) (c : CId) : Option ConstRel := (a.consts[c]?).join
def ctorRel? (a : Ann) (c : CId) : Option CtorRel := (a.ctors[c]?).join

end Ann

/-- Install tags into one term, consuming them in `tagOrder`. -/
def installTerm (tags : Array Tag) : Term → StateT Nat (Except String) Term
  | .lam b d t => do
    let i ← get
    match tags[i]? with
    | some (.lam r pw) =>
      set (i + 1)
      return .lam { b with rel := r, propWhen := pw } d (← installTerm tags t)
    | _ => throw s!"relevance: expected a λ tag at {i}"
  | .app f a m _ => do
    let f ← installTerm tags f
    let i ← get
    match tags[i]? with
    | some (.arg r) =>
      set (i + 1)
      if r.alwaysIrr then return .app f a m r
      else return .app f (← installTerm tags a) m r
    | _ => throw s!"relevance: expected an argument tag at {i}"
  | .letE c _ ty v body => do
    let i ← get
    match tags[i]? with
    | some (.letE r) =>
      set (i + 1)
      let v ← if r.alwaysIrr then pure v else installTerm tags v
      return .letE c r ty v (← installTerm tags body)
    | _ => throw s!"relevance: expected a let tag at {i}"
  | .proj s i e => return .proj s i (← installTerm tags e)
  | t => return t

/-- Tags of an installed term, in `tagOrder` (the inverse of `installTerm`). -/
def _root_.Compilatrix.Src.Term.tagOrder : Term → Array Tag → Array Tag
  | .lam b _ t, acc => Term.tagOrder t (acc.push (.lam b.rel b.propWhen))
  | .app f a _ r, acc =>
    let acc := Term.tagOrder f acc
    if r.alwaysIrr then acc.push (.arg r)
    else Term.tagOrder a (acc.push (.arg r))
  | .letE _ r _ v b, acc =>
    let acc := acc.push (.letE r)
    let acc := if r.alwaysIrr then acc else Term.tagOrder v acc
    Term.tagOrder b acc
  | .proj _ _ e, acc => Term.tagOrder e acc
  | _, acc => acc

/-- Write every node tag into its term. A tag list that does not cover its
term exactly is rejected (tier S1). -/
def install (p : Program) (a : Ann) : Except String Program := do
  let mut p := p
  for (key, tags) in a.nodes do
    let some t := p.termOf key | throw s!"relevance: no runtime term for {repr key}"
    let (t', used) ← (installTerm tags t).run 0
    unless used == tags.size do
      throw s!"relevance: {tags.size - used} extra tags for {repr key}"
    p := p.setTerm key t'
  return p

end Compilatrix.Src.Relevance
