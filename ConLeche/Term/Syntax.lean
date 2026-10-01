module

@[expose] public section

/-!
# Syntax of the erased term language (task #74; relocated at #209)

`Term` is the semantics tier's *own* term datatype — deliberately not
`ConLeche.Expr`.  It is what the denotation function from a real
`Env`+`Expr` targets (`ConLeche/Verify/Denote.lean`), and it is chosen for
proof convenience, not for fidelity to the checker's representation.

The declarative typing judgment this datatype was cut for is **gone**
(`HasType`, deleted at task #209 — see DESIGN.md's task #209 section);
the sentences below that motivate a design choice by a typing rule are
kept as the *reason the datatype has the shape it has*, not as a
claim that such a rule still exists anywhere in the tree.

Differences from `ConLeche.Expr`, each deliberate:

* **de Bruijn indices only.**  No `fvar`: the local context is an
  explicit `List Term`, so open terms need no type annotation at the
  leaf.
* **Universe levels are concrete `Nat`s.**  There is no `Level`
  inductive, no level substitution and no level-equality judgment.
  The denotation from a real `Env`+`Expr` unfolds everything, so every
  constant is instantiated at its use site and every level expression
  in the unfolded term evaluates to a ground natural.  `imax` is a
  *computed function* on `Nat` (`ConLeche.Term.imax`), so impredicativity
  of `Prop` is just its `v = 0` branch.  Universe polymorphism lives
  entirely in the bridge: a polymorphic declaration is denoted once per
  ground assignment, and "accepted" means the resulting statement holds
  at every assignment.  The layer therefore cannot state a polymorphic
  fact internally — and does not need to, because it has no definable
  constants at all.
* **There is no `letE`.**  No stored expression carries a `let`: the
  annotation pass runs the official `infer_let` triple and returns the
  ζ *reduct* (task #217), and every kernel arm that used to accept a
  `letE` node downstream of it is a positive error (task #241).  So the
  denotation's `letE` clause is `none`, the former is gone, and the
  substitution metatheory stays as small as it was — see
  `ConLeche/Verify/Denote.lean`'s "There is no `let` in the term
  language".
* **`fst`/`snd` are formers, and their type arguments live in the
  premise.**  A projection on a *modeled* structure never reaches this
  layer: the checker accepts no `.proj` node without a native table
  entry (task #175 wiring W5 — the annotation-time rewrites into
  eliminations are gone).  A projection on the **pinned pair** or on a
  direct structure's tower entry does: `ProjEntry.native` nodes are
  first-class by design and survive into stored terms — carrying the
  structure's name and the field index, and *not* the pair's type
  arguments, which the checker recovers at use time from the subject's
  inferred type.

  So the layer has **two unary formers**, `fst e` and `snd e`, taking
  only the subject (task #225; they were one `proj i e` node with a
  side condition `i < 2` until then).  The checker's node index is
  decoded once, at the denotation (`Term.projPair?`, below), and every
  reader downstream matches on a constructor instead of carrying the
  bound.  The typing rules read `A` and `B` off the premise
  `Γ ⊢ p : PSigma' A B` instead of off the term.  This is the same move
  the `app` rule makes, and it pays the same way: the premise hands
  soundness the `⟦p⟧ ∈ˢ sigmaSet …` package that the set model's
  `WellDenoted` clause has to carry by hand.  Interpretation is then
  literally `interpExpr`'s clause, `sfst`/`ssnd`.

  (An earlier design had projections denote to applications of basis
  constants `psigmaFst`/`psigmaSnd`.  That is *unimplementable* for the
  pinned pair — a denotation that is a function of the expression alone
  cannot invent `A` and `B` — and the constants are now derivable from
  this former anyway, so they are gone.)
* **No `lit`.**  Literal computation is *derived*, not built in: any
  term satisfying an operation's certified recurrences computes it on
  numerals (the pinned `Nat` operations, `ConLeche/Kernel/NatOpPins.lean`).
* **No global environment / no named constants.**  There is no `Env`
  and no delta rule: every constant the checker accepts either has a
  value (definitions, theorems, `opaque`s, the trust family), or has a
  checked model artifact that plays the role of a value (modeled
  inductives, direct structures), or is one of finitely many pinned
  standard axioms.  The first two unfold; the last are the built-in
  constants `propext` / `choice` below.  Consequently the constant
  alphabet `BConst` is *closed and finite*.
* **`eqE`, a primitive equality former.**  All conversion is expressed
  with the object-level equality, so `Eq`
  must be syntax rather than a constant: the conversion rule mentions
  it.  Making it a former (rather than a constant applied to three
  arguments) is what keeps every equational rule *premise-free in the
  type* — the interpretation of `eqE a b` reads only `a` and `b`, and
  since **nothing** reads the type, the former does not carry it
  (task #237; it did until then).
* **`prf`, the canonical proof.**  Equality proofs are irrelevant
  (`eqE _ _ _` is always a `Prop`), so the layer needs no proof terms
  with structure: every rule that concludes an equation concludes it
  for the single constant `prf`.

## The basis

The basis type formers are the ones the checker pins by hand
(`ConLeche/Kernel/Basis/*.lean`): `Nat`, `PUnit`, `PSigma'`, `Empty`,
`Quot`.  `Eq` is absent from the list only because it has been promoted
to a syntactic former.  Everything else the checker stores — every
modeled inductive, every direct structure — unfolds into this alphabet,
which is why the alphabet can be closed.

Four constants of the checker's basis are *derivable* here and
therefore absent: `Eq.rec` (transport is the identity once equality is
reflected, so `fun A a M m b h => m` types by conversion), `PSigma'.rec`
(`fun A B M f p => f p.1 p.2`, typed by conversion along structure
eta), and `PSigma'.fst`/`PSigma'.snd` themselves
(`fun A B p => p.fst`/`p.snd`, once those are formers).  Dropping them
removes the most index-heavy dependent types from `BConst.type`, and
in the projections' case it is evidence that the former is the right
primitive rather than an addition on top of one.
-/

namespace ConLeche.Term

/-- Lean's `imax`, as a function on concrete levels: `Prop` is
impredicative, every other codomain takes the `max`. -/
def imax (u v : Nat) : Nat := if v = 0 then 0 else Nat.max u v

/-- The closed, finite alphabet of built-in constants: the pinned basis
type formers with their constructors, recursors and projections, plus
the two pinned standard axioms that are not equations. -/
inductive BConst where
  /-- `Nat : Type` -/
  | nat
  /-- `Nat.zero : Nat` -/
  | natZero
  /-- `Nat.succ : Nat → Nat` -/
  | natSucc
  /-- `Nat.rec.{u}` -/
  | natRec
  /-- `PUnit.{u} : Sort u` -/
  | punit
  /-- `PUnit.unit.{u} : PUnit.{u}` -/
  | punitUnit
  /-- `PUnit.rec.{u,v}` -/
  | punitRec
  /-- `PSigma'.{u,v} : (A : Sort u) → (A → Sort v) → Sort (max u v)` -/
  | psigma
  /-- `PSigma'.mk.{u,v}` -/
  | psigmaMk
  /-- `Empty.{u} : Sort u` (level-polymorphic, so it covers `False` too) -/
  | empty
  /-- `Empty.rec.{u,v}` -/
  | emptyRec
  /-- `Quot.{u}` -/
  | quot
  /-- `Quot.mk.{u}` -/
  | quotMk
  /-- `Quot.lift.{u,v}` -/
  | quotLift
  /-- `Quot.ind.{u}` -/
  | quotInd
  /-- `Quot.sound.{u}` -/
  | quotSound
  /-- `propext`, in primitive form: two implications give equality of
  propositions (no `Iff`, which is a modeled inductive and unfolds). -/
  | propext
  /-- `Classical.choice.{u}`, in primitive form: double-negation
  elimination into `Sort u` (no `Nonempty`, which is a modeled
  inductive and unfolds). -/
  | choice
  /-- `lfpFam.{u,w} : Π (I : Sort u), ((I → Sort w) → (I → Sort w)) → I → Sort w`
  — the least pre-fixed point of a functor on FAMILIES over `I` (task
  #188: the carrier of a directly installed recursive inductive type,
  indexed from the start — `lfpFamSet`, `ConLeche/SetTheory/Derive/LfpFam.lean`).
  A model-side constant with no kernel counterpart: no stream declares
  it, only the direct route's leaves spell it.  Its value is total (the
  empty family when no closed family exists), so it inhabits this type
  with no certificate; the fixed-point laws hold under the semantic
  hypothesis that a closed family exists.  (The non-indexed `lfp` of
  the route's checkpoint was removed once the indexed leaf landed.) -/
  | lfpFam
  deriving Repr, DecidableEq, Inhabited

/-- Terms.  See the module docstring for what is *not* here. -/
inductive Term where
  /-- de Bruijn index -/
  | bvar (i : Nat)
  /-- `Sort u` at a concrete level -/
  | sort (u : Nat)
  /-- a built-in constant at a concrete level instantiation -/
  | const (c : BConst) (us : List Nat)
  /-- application -/
  | app (f a : Term)
  /-- `fun (_ : ty) => body` -/
  | lam (ty body : Term)
  /-- `(_ : ty) → body` -/
  | pi (ty body : Term)
  /-- `@Eq _ lhs rhs`, **without the type**: the interpretation is
  `⟦eqE a b⟧ = eqv ⟦a⟧ ⟦b⟧`, so soundness never constrains the type,
  and a census (task #237) found no definition and no theorem in any
  tier reading the slot the former used to carry.  It is gone; a
  producer that knows the type simply drops it. -/
  | eqE (lhs rhs : Term)
  /-- First field of a pair.  Carries **only** the subject: the pair's
  type arguments come from the typing premise `Γ ⊢ p : PSigma' A B`,
  not from the term — see the module docstring.  Interpreted by
  `sfst`, i.e. literally `interpExpr`'s clause. -/
  | fst (e : Term)
  /-- Second field of a pair; the `fst` twin, interpreted by `ssnd`. -/
  | snd (e : Term)
  /-- the canonical (irrelevant) proof of a derivable equation -/
  | prf
  deriving Repr, Inhabited

namespace Term

/-- Iterated application. -/
def mkAppN (f : Term) : List Term → Term
  | [] => f
  | a :: as => mkAppN (.app f a) as

@[simp] theorem mkAppN_nil (f : Term) : mkAppN f [] = f := rfl
@[simp] theorem mkAppN_cons (f a : Term) (as : List Term) :
    mkAppN f (a :: as) = mkAppN (.app f a) as := rfl

/-- Decode the checker's projection index for the **pinned pair**: the
two fields are the two formers `fst`/`snd`, and no other index denotes.
This is where the side condition `i < 2` of the old single `proj i e`
former lives now (task #225).  The denotation stays total, and a
`.proj T i` node with `2 ≤ i` and no projection-table entry still has
no image, exactly as when the bound was a conjunct of `WellDenoted`. -/
def projPair? : Nat → Term → Option Term
  | 0, e => some (.fst e)
  | 1, e => some (.snd e)
  | _ + 2, _ => none

end Term

/-- How many universe parameters each constant takes.  Level lists that
are too short are read with `0` defaults (`ConLeche/Term/Const.lean`), so
this is documentation and a bridge convention, never a side condition
of a rule. -/
def BConst.numLevels : BConst → Nat
  | .nat | .natZero | .natSucc | .propext => 0
  | .natRec | .punit | .punitUnit | .empty
  | .quot | .quotMk | .quotInd | .quotSound | .choice => 1
  | .lfpFam => 2
  | .punitRec | .psigma | .psigmaMk
  | .emptyRec | .quotLift => 2

end ConLeche.Term
