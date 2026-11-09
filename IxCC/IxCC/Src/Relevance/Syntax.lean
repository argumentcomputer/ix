import IxCC.Src.Runtime

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

namespace IxCC.Src.Relevance

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
  fields : List FieldClass
  deriving BEq, DecidableEq, Repr, Inhabited

/-- A constant's own class and its leading Π telescope's binder classes,
over the constant's universe parameters. -/
structure ConstRel where
  result : Rel
  params : List Rel
  deriving BEq, DecidableEq, Repr, Inhabited

inductive Tag where
  | lam (r : Rel) (pw : PropWhen)
  | arg (r : Rel)
  | letE (r : Rel)
  deriving BEq, DecidableEq, Repr, Inhabited

/-- The annotation, kernel-evaluable (D17): records keyed by `CId`, and each
runtime term's tags as a list in `tagOrder`. -/
structure Ann where
  consts : NatMap ConstRel := .leaf
  ctors : NatMap CtorRel := .leaf
  nodes : List (TermKey × List Tag) := []
  deriving BEq, DecidableEq, Repr, Inhabited

namespace Ann

def constRel? (a : Ann) (c : CId) : Option ConstRel := a.consts.get? c
def ctorRel? (a : Ann) (c : CId) : Option CtorRel := a.ctors.get? c

end Ann

/-- Install tags into one term, consuming them in `tagOrder` from the front
of `tags`; `i` counts the tags consumed before (for diagnostics). Returns the
term, the tags left and the new count (structural on the term). -/
def installTerm : Term → List Tag → Nat → Except String (Term × List Tag × Nat)
  | .lam b d t, tags, i =>
    match tags with
    | .lam r pw :: tags => do
      let (t, tags, i) ← installTerm t tags (i + 1)
      return (.lam { b with rel := r, propWhen := pw } d t, tags, i)
    | _ => throw s!"relevance: expected a λ tag at {i}"
  | .app f a m _, tags, i => do
    let (f, tags, i) ← installTerm f tags i
    match tags with
    | .arg r :: tags =>
      if r.alwaysIrr then return (.app f a m r, tags, i + 1)
      else
        let (a, tags, i) ← installTerm a tags (i + 1)
        return (.app f a m r, tags, i)
    | _ => throw s!"relevance: expected an argument tag at {i}"
  | .letE c _ ty v body, tags, i =>
    match tags with
    | .letE r :: tags => do
      let (v, tags, i) ← if r.alwaysIrr then pure (v, tags, i + 1) else installTerm v tags (i + 1)
      let (body, tags, i) ← installTerm body tags i
      return (.letE c r ty v body, tags, i)
    | _ => throw s!"relevance: expected a let tag at {i}"
  | .proj s k e, tags, i => do
    let (e, tags, i) ← installTerm e tags i
    return (.proj s k e, tags, i)
  | t, tags, i => return (t, tags, i)

/-- Tags of an installed term in `tagOrder`, prepended in reverse to `acc`. -/
def _root_.IxCC.Src.Term.tagOrderRev : Term → List Tag → List Tag
  | .lam b _ t, acc => Term.tagOrderRev t (.lam b.rel b.propWhen :: acc)
  | .app f a _ r, acc =>
    let acc := Term.tagOrderRev f acc
    if r.alwaysIrr then .arg r :: acc
    else Term.tagOrderRev a (.arg r :: acc)
  | .letE _ r _ v b, acc =>
    let acc := .letE r :: acc
    let acc := if r.alwaysIrr then acc else Term.tagOrderRev v acc
    Term.tagOrderRev b acc
  | .proj _ _ e, acc => Term.tagOrderRev e acc
  | _, acc => acc

/-- `acc` followed by the tags of an installed term, in `tagOrder` (the
inverse of `installTerm`). -/
def _root_.IxCC.Src.Term.tagOrder (t : Term) (acc : List Tag := []) : List Tag :=
  acc ++ (t.tagOrderRev []).reverse

/-- Install the tags of each listed runtime term, in order (structural on
the list). -/
def installNodes (p : Program) : List (TermKey × List Tag) → Except String Program
  | [] => pure p
  | (key, tags) :: nodes => do
    let some t := p.termOf key | throw s!"relevance: no runtime term for {repr key}"
    let (t', rest, _) ← installTerm t tags 0
    unless rest.isEmpty do
      throw s!"relevance: {rest.length} extra tags for {repr key}"
    installNodes (p.setTerm key t') nodes

/-- Write every node tag into its term. A tag list that does not cover its
term exactly is rejected (tier S1). -/
def install (p : Program) (a : Ann) : Except String Program := installNodes p a.nodes

end IxCC.Src.Relevance
