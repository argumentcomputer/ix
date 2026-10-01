module

public import ConLeche.Semantics.Syntax
public import ConLeche.Term.Const

@[expose] public section

/-!
# `BConst.typeAV` — the annotated basis-constant types (#151, step 2)

*(Re-based to `ConLeche/SetBase/*` at THE SEPARATION's S2, task #161: the
module already imported nothing but `SetBase/Syntax` and `TT/Const` —
it is the basis constants' *annotated types*, pure syntax — and the
graded lane's `Interp/BasisTypeOk` was reaching it through the 2U
`Interp/BasisOk`.  Path and module name changed; namespaces,
statements and proofs verbatim.)*


The first of the two suppliers the skeleton's `const` row waits on
(`Interp/Skeleton.lean`): the annotated mirror of
`ConLeche/Term/Const.lean`'s `BConst.type`, so that a built-in constant's
type can be *written* as an `AnnotTerm` at all.  `denoteAnnot` cannot produce
it — `BConst.type` yields a `Term` and `denoteAnnot` maps `Expr → AnnotTerm`
— which is why the former has to exist on its own.

## The annotation convention, inherited not invented

`Interp/Value.lean` fixed it for the value side, and this file mirrors
it exactly, because the two must agree for the capstone
(`bval_mem_type`) to typecheck at all:

* **every binder's codomain slot carries the tower's result sort `r`**,
  not the exact `imax` fold.  Sound because `piR`/`lamR` read the
  numeral only through `v = 0`, and `imax x y = 0 ↔ y = 0`
  (`imax_eq_zero_iff`);
* **every binder's domain slot carries the domain's exact sort**,
  because those are what the consumers' membership hypotheses are
  stated with — `WellDenoted`'s binder clauses and `Skeleton.sound_pi`
  both read the domain numeral.

So `.pi u' r A B` throughout, with `u'` exact.  The `v'`-for-a-`Sort`
trap is worth naming once: a codomain slot holds the sort of `B` **as
a type**, so a codomain `.sort k` gets `k + 1`, never `k`.  That is why
`A → Prop` annotates as `.pi u 1 A (.sort 0)` and is a *type*
(`Sort (max u 1)`), not a proposition.

## The result sorts, read off the towers

| constant | `r` | tower |
|---|---|---|
| the five atomic types | — | no binder |
| `natSucc` | `1` | `lamR 1 omega natsucc` |
| `natRec` | `u` | `natRecV` |
| `punitRec` | `v` | `punitRecV` |
| `psigma` | `max u v + 1` | `psigmaV` (a type former) |
| `psigmaMk` | `max u v` | `psigmaMkV` |
| `emptyRec` | `v` | `emptyRecV` |
| `quot` | `u + 1` | `quotV` (a type former) |
| `quotMk` | `u` | `quotMkV` |
| `quotLift` | `v` | `quotLiftV` |
| `quotInd`/`quotSound`/`propext` | `0` | `pt`: the types are `Prop` |
| `choice` | `u` | `choiceV` |
| `lfpFam` | `max (u + 1) (w + 1)` | `lfpFamV` (a type former) |

The faithfulness check is `typeAV_erase` below: erasure returns
`BConst.type` on the nose, so the former adds annotations and nothing
else.  It is the analogue of `denoteAnnot_erase`, and it is what makes a
numeral error the *only* thing that can go wrong here — a structural
error cannot survive it.
-/

namespace ConLeche.Semantics

open ConLeche.Semantics (AnnotTerm)
open ConLeche.Term (BConst lv)

/-! ## Annotated smart constructors

Mirrors of `ConLeche/Term/Const.lean`'s, one per former the basis types
mention.  Each carries the numerals its own shape fixes. -/

/-- `Nat` -/
def natTyAV : AnnotTerm := .const .nat []
/-- `Nat.zero` -/
def natZeroAV : AnnotTerm := .const .natZero []
/-- `Nat.succ e` -/
def natSuccAV (e : AnnotTerm) : AnnotTerm := .app (.const .natSucc []) e
/-- `PUnit.{u}` -/
def punitAV (u : Nat) : AnnotTerm := .const .punit [u]
/-- `PUnit.unit.{u}` -/
def punitUnitAV (u : Nat) : AnnotTerm := .const .punitUnit [u]
/-- `Empty.{u}` -/
def emptyAV (u : Nat) : AnnotTerm := .const .empty [u]
/-- `@PSigma'.{u,v} A B` -/
def psigmaAV (u v : Nat) (A B : AnnotTerm) : AnnotTerm :=
  AnnotTerm.mkAppN (.const .psigma [u, v]) [A, B]
/-- `@Quot.{u} A r` -/
def quotAV (u : Nat) (A r : AnnotTerm) : AnnotTerm :=
  AnnotTerm.mkAppN (.const .quot [u]) [A, r]
/-- `@Quot.mk.{u} A r a` -/
def quotMkAV (u : Nat) (A r a : AnnotTerm) : AnnotTerm :=
  AnnotTerm.mkAppN (.const .quotMk [u]) [A, r, a]

/-- `A → B`, at the domain's sort `u` and the codomain's sort `v`. -/
def arrowA (u v : Nat) (A B : AnnotTerm) : AnnotTerm := .pi u v A B.lift

/-- `A → A → Prop`, the relation type at `A : Sort u`.  Its own sort is
`max u 1` — a *type*, because `Prop` lives in `Sort 1`.  Matches
`relSpace`. -/
def relAV (u : Nat) (A : AnnotTerm) : AnnotTerm :=
  .pi u (Nat.max u 1) A (.pi u 1 A.lift (.sort 0))

/-- `¬ A`, i.e. `A → False`: a proposition, so the codomain slot is
`0`. -/
def negTyAV (u : Nat) (A : AnnotTerm) : AnnotTerm := arrowA u 0 A (emptyAV 0)

/-! ## The annotated type assignment -/

/-- The annotated type of each built-in constant — `BConst.type` with
every binder's two numerals supplied (see the module docstring). -/
def BConst.typeAV : BConst → List Nat → AnnotTerm
  | .nat, _ => .sort 1
  | .natZero, _ => natTyAV
  | .natSucc, _ => arrowA 1 1 natTyAV natTyAV
  | .natRec, us =>
    let u := lv us 0
    -- `∀ (M : Nat → Sort u), M 0 → (∀ n, M n → M (n+1)) → ∀ t, M t`
    .pi (u + 1) u (arrowA 1 (u + 1) natTyAV (.sort u)) <|
    .pi u u (.app (.bvar 0) natZeroAV) <|
    .pi u u (.pi 1 u natTyAV (.pi u u (.app (.bvar 2) (.bvar 0))
          (.app (.bvar 3) (natSuccAV (.bvar 1))))) <|
    .pi 1 u natTyAV <|
    .app (.bvar 3) (.bvar 0)
  | .punit, us => .sort (lv us 0)
  | .punitUnit, us => punitAV (lv us 0)
  | .punitRec, us =>
    let u := lv us 0; let v := lv us 1
    -- `∀ (M : PUnit.{u} → Sort v), M unit → ∀ t, M t`
    .pi (Nat.max u (v + 1)) v
      (arrowA u (v + 1) (punitAV u) (.sort v)) <|
    .pi v v (.app (.bvar 0) (punitUnitAV u)) <|
    .pi u v (punitAV u) <|
    .app (.bvar 2) (.bvar 0)
  | .psigma, us =>
    let u := lv us 0; let v := lv us 1
    let r := Nat.max u v + 1
    .pi (u + 1) r (.sort u) <|
    .pi (Nat.max u (v + 1)) r
      (arrowA u (v + 1) (.bvar 0) (.sort v)) <|
    .sort (Nat.max u v)
  | .psigmaMk, us =>
    let u := lv us 0; let v := lv us 1
    let r := Nat.max u v
    .pi (u + 1) r (.sort u) <|
    .pi (Nat.max u (v + 1)) r
      (arrowA u (v + 1) (.bvar 0) (.sort v)) <|
    .pi u r (.bvar 1) <|
    .pi v r (.app (.bvar 1) (.bvar 0)) <|
    psigmaAV u v (.bvar 3) (.bvar 2)
  | .empty, us => .sort (lv us 0)
  | .emptyRec, us =>
    let u := lv us 0; let v := lv us 1
    .pi (Nat.max u (v + 1)) v
      (arrowA u (v + 1) (emptyAV u) (.sort v)) <|
    .pi u v (emptyAV u) <|
    .app (.bvar 1) (.bvar 0)
  | .quot, us =>
    let u := lv us 0
    .pi (u + 1) (u + 1) (.sort u) <|
    .pi (Nat.max u 1) (u + 1) (relAV u (.bvar 0)) <|
    .sort u
  | .quotMk, us =>
    let u := lv us 0
    .pi (u + 1) u (.sort u) <|
    .pi (Nat.max u 1) u (relAV u (.bvar 0)) <|
    .pi u u (.bvar 1) <|
    quotAV u (.bvar 2) (.bvar 1)
  | .quotLift, us =>
    let u := lv us 0; let v := lv us 1
    -- `∀ A r B (f : A → B), (∀ a b, r a b → f a = f b) → Quot A r → B`
    .pi (u + 1) v (.sort u) <|
    .pi (Nat.max u 1) v (relAV u (.bvar 0)) <|
    .pi (v + 1) v (.sort v) <|
    .pi (ConLeche.Term.imax u v) v (.pi u v (.bvar 2) (.bvar 1)) <|
    .pi 0 v (.pi u 0 (.bvar 3) (.pi u 0 (.bvar 4)
          (.pi 0 0 (AnnotTerm.mkAppN (.bvar 4) [.bvar 1, .bvar 0])
            (.eqE (.app (.bvar 3) (.bvar 2))
              (.app (.bvar 3) (.bvar 1)))))) <|
    .pi u v (quotAV u (.bvar 4) (.bvar 3)) <|
    .bvar 3
  | .quotInd, us =>
    let u := lv us 0
    .pi (u + 1) 0 (.sort u) <|
    .pi (Nat.max u 1) 0 (relAV u (.bvar 0)) <|
    .pi (Nat.max u 1) 0
      (.pi u 1 (quotAV u (.bvar 1) (.bvar 0)) (.sort 0)) <|
    .pi 0 0 (.pi u 0 (.bvar 2)
      (.app (.bvar 1) (quotMkAV u (.bvar 3) (.bvar 2) (.bvar 0)))) <|
    .pi u 0 (quotAV u (.bvar 3) (.bvar 2)) <|
    .app (.bvar 2) (.bvar 0)
  | .quotSound, us =>
    let u := lv us 0
    .pi (u + 1) 0 (.sort u) <|
    .pi (Nat.max u 1) 0 (relAV u (.bvar 0)) <|
    .pi u 0 (.bvar 1) <|
    .pi u 0 (.bvar 2) <|
    .pi 0 0 (AnnotTerm.mkAppN (.bvar 2) [.bvar 1, .bvar 0]) <|
    .eqE (quotMkAV u (.bvar 4) (.bvar 3) (.bvar 2))
      (quotMkAV u (.bvar 4) (.bvar 3) (.bvar 1))
  | .propext, _ =>
    -- `∀ (A B : Prop), (A → B) → (B → A) → A = B`
    .pi 1 0 (.sort 0) <| .pi 1 0 (.sort 0) <|
    .pi 0 0 (.pi 0 0 (.bvar 1) (.bvar 1)) <|
    .pi 0 0 (.pi 0 0 (.bvar 1) (.bvar 3)) <|
    .eqE (.bvar 3) (.bvar 2)
  | .choice, us =>
    let u := lv us 0
    -- `∀ (A : Sort u), ¬¬A → A`
    .pi (u + 1) u (.sort u) <|
    .pi 0 u (negTyAV 0 (negTyAV u (.bvar 0))) <|
    .bvar 1
  | .lfpFam, us =>
    let u := lv us 0; let w := lv us 1
    let m := Nat.max u (w + 1)
    -- `Π (I : Sort u), ((I → Sort w) → (I → Sort w)) → I → Sort w` (task
    -- #188, indexed): `I → Sort w` has sort `max u (w + 1)`, and so do the
    -- functor space and the tail
    .pi (u + 1) m (.sort u) <|
    .pi m m (arrowA m m (arrowA u (w + 1) (.bvar 0) (.sort w)) (arrowA u (w + 1) (.bvar 0) (.sort w))) <|
    .pi u (w + 1) (.bvar 1) (.sort w)

/-! ## Faithfulness

The former adds annotations and nothing else — so a *numeral* error is
the only thing this file can get wrong, and the capstone
(`bval_mem_type`) is what tests those. -/

/-- **The erasure law**: `typeAV` erases to `BConst.type` on the nose. -/
theorem typeAV_erase (c : BConst) (us : List Nat) :
    (BConst.typeAV c us).erase = BConst.type c us := by
  cases c <;>
    simp [BConst.typeAV, ConLeche.Term.BConst.type, natTyAV, natZeroAV,
      natSuccAV, punitAV, punitUnitAV, emptyAV, psigmaAV, quotAV,
      quotMkAV, arrowA, relAV, negTyAV, ConLeche.Term.natT,
      ConLeche.Term.natZeroT,
      ConLeche.Term.natSuccT, ConLeche.Term.punitT, ConLeche.Term.punitUnitT,
      ConLeche.Term.emptyT, ConLeche.Term.psigmaT, ConLeche.Term.quotT,
      ConLeche.Term.quotMkT, ConLeche.Term.arrow, ConLeche.Term.relT,
      ConLeche.Term.negT, AnnotTerm.mkAppN, ConLeche.Term.Term.mkAppN]

end ConLeche.Semantics
