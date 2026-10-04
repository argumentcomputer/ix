/- # O11b: `noConfusion` of a split-off member in enumeration form

## Contract
Input: Lean's `T.noConfusionType` and `T.noConfusion` (definitions Lean
generates per inductive, `src/lean/Lean/Meta/Constructions/NoConfusion*`),
where `T` is a member of a changed Lean block (`all.size ≥ 2`, so Lean chose
the general form) whose Ix component is **one class**, and `T` is an
*enumeration* in Lean's sense (`isEnumType`): not a proposition, no
parameters, no indices, at least one constructor, every constructor without
fields, not unsafe. Declared alone, as in the canonical twin (one
declaration per component, the block's universes and parameters kept),
Lean gives such a `T` the enumeration form (§4.7 (c)); inside the mutual
block it gives it the general form
`λ P t t'. T.casesOn t (T.casesOn t' (P → P) P …) …`.

Output: the two constants keep their Lean names and Lean's types; their
values become the enumeration form, which is the twin's (measured on Lean
4.34.1 with `pp.all`; `v` the motive universe, `l` the universe of `T`'s
sort):
* one constructor: `T.noConfusionType := λ (P : Sort v) (x y : T). P → P`,
  `T.noConfusion := λ {P} {x y} (h : @Eq.{l} T x y) (p : P). p`;
* two or more constructors (`noConfusionTypeEnum T.ctorIdx`): **declined**
  at this head (below).
Each value's root carries the decompile record `_ix.inline` with Lean's
value as its source (placeholder indices from `o11bRecordBase`).

## Faithfulness (proof-justified; the statement Phase B formalises)
Write `G` and `E` for Lean's (general) and the enumeration
`noConfusionType`, `g` and `ε` for the two `noConfusion`s.
**Lemma O11b.1.** `∀ (P : Sort v) (x y : T), G P x y = E P x y`, hence `G =
E` by function extensionality (three times). *Proof*: case analysis on `x`,
then on `y` (`T.casesOn` at Prop motives). With one constructor `c`: `G P c
c` →δβι `P → P` and `E P c c` →δβ `P → P`, so `Eq.refl`. ∎
**Lemma O11b.2.** For all `P x y (h : x = y)`, `g h = cast (congrFun₃ G=E P
x y)⁻¹ (ε h)`, i.e. the two are equal as elements of the type `T.noConfusionType
P x y` whichever value `T.noConfusionType` has. *Proof*: `subst h`; case
analysis on `x`; `g (Eq.refl c)` →δβι `λ k. k` (Lean's `Eq.ndrec` over
`T.casesOn` at `c`) and `ε (Eq.refl c)` →δβ `λ p. p`; both at type `P → P`,
`Eq.refl`. ∎
So the environment with `(E, ε)` and the one with `(G, g)` agree on every
closed instance (Lemma O11b.1 at constructors is `rfl`), and every term
typed against `T.noConfusionType` is transported along `G = E`.

**Typing of the output.** `ε` has Lean's type `x = y → T.noConfusionType P
x y` only when `T.noConfusionType` unfolds to `E` at variables: `ε` is
rewritten only together with `E` (both decisions are the same function of
the input, `rewriteMembers`). Lean's own `g` checks against either value
(it instantiates `T.noConfusionType` generically in its motives and at
constructors in its minors), so a demoted `T.noConfusion` next to a
rewritten `T.noConfusionType` is well typed.

**Dependents.** The dependents rule (`Opt.Packed`): a constant outside the
pair that references `T.noConfusionType` (or `T.noConfusion`) and an
image-kind auxiliary of `T`'s block demotes it (`T.noConfusion` is not
counted for `T.noConfusionType`, `isCarriedDependent`). Users of
`T.noConfusion` apply it at constructors (`nomatch`, injectivity), where
both forms reduce alike.

## Canonicity
The output depends on `T` (canonical: the Ix inductive of the class), the
universe of its sort and the motive universe: it is the twin's value byte
for byte. Lean's general form is presentation-dependent only through
`numTypeFormers` (the mutual block), which the output no longer depends on.

## Side condition and fallback
Decidable: the names are `T.noConfusionType`/`T.noConfusion` of a member
`T` of a changed block (`T.casesOn` is an image-kind head); `T`'s Ix
component is one class; `T` is an enumeration as above, with exactly one
constructor; Lean's constants have the standard shape (a definition whose
type has three, resp. four, binders, the first a sort); not demoted.
Otherwise Lean's value, the baseline, faithful (§0.1).
**Two or more constructors** need `T.ctorIdx`, `noConfusionTypeEnum`,
`noConfusionEnum` and `instDecidableEqNat` compiled before `T`'s
`noConfusionType`, which the input's reference graph does not order (Lean's
general form references none of them): adding them without a scheduling
edge would make the output depend on the schedule. Declined (cause
`PENDING-NOCONFUSION`) until the edge exists (the O11a edge mechanism of A6f
is the vehicle).

## Non-canonical set and evidence
Several constructors: `PENDING-NOCONFUSION` (above). Evidence:
`Tests/Ix/Compile/Pass/O11bNoConfusion.lean` (a split-off one-constructor
enumeration: twin pairs byte-equal with the switch on; a two-constructor one
declines; value pins by `rfl` and a `noConfusion` user, checked by the three
kernels). Library load 0 (no split block with an enumeration member).
-/
module
public import Ix.Compile.Pass.Opt.Core
public import Ix.Compile.Pass.Names
public import Ix.Compile.Image.Expr
public section

namespace Ix.Compile.Pass.Opt

open Ix (Name Level Expr ConstantInfo DefinitionVal InductiveVal)

/-- Placeholder indices of O11b's decompile records (disjoint from the
call-site rewrite's, which start at 0, and the clique hook's, `2^40`). -/
def o11bRecordBase : Nat := 1 <<< 41

/-- The sort level of an inductive's type (`Sort l` after its binders). -/
def sortOfType : Expr → Option Level
  | .forallE _ _ b _ _ => sortOfType b
  | .mdata _ b _ => sortOfType b
  | .sort l _ => some l
  | _ => none

/-- `T.noConfusionType` or `T.noConfusion`: `(T, isType)`. -/
def noConfusionOf : Name → Option (Name × Bool)
  | .str t "noConfusionType" _ => some (t, true)
  | .str t "noConfusion" _ => some (t, false)
  | _ => none

/-- `T` is an enumeration in Lean's sense, with its constructor count. -/
def enumCtors (const? : Name → Option ConstantInfo) (t : Name) : Option (InductiveVal × Nat) := do
  let some (.inductInfo iv) := const? t | none
  if iv.numParams != 0 || iv.numIndices != 0 || iv.ctors.isEmpty || iv.isUnsafe then none
  let l ← sortOfType iv.cnst.type
  if l == Level.mkZero then none
  for c in iv.ctors do
    let some (.ctorInfo cv) := const? c | none
    if cv.numFields != 0 then none
  return (iv, iv.ctors.size)

/-- The enumeration form of `T`'s two constants (one constructor), at the
motive universe `v` and `T`'s universe arguments `us` (Lean's universe
parameters of the constant: the motive's first, then `T`'s). -/
def enumForm (iv : InductiveVal) (v : Level) (us : Array Level) (isType : Bool) : Option Expr := do
  let l ← sortOfType iv.cnst.type
  let l := Ix.Compile.Canon.substLevel iv.cnst.levelParams us l
  let tC := Expr.mkConst iv.cnst.name us
  let nm := fun (s : String) => Name.mkStr Name.mkAnon s
  let sortV := Expr.mkSort v
  if isType then
    -- λ (P : Sort v) (x y : T). P → P
    some (Expr.mkLam (nm "P") sortV (Expr.mkLam (nm "x") tC (Expr.mkLam (nm "y") tC
      (Expr.mkForallE (nm "a") (Expr.mkBVar 2) (Expr.mkBVar 3) .default) .default) .default) .default)
  else
    -- λ {P : Sort v} {x y : T} (h : @Eq.{l} T x y) (p : P). p
    let eqTy := Ix.Compile.Canon.mkAppN (Expr.mkConst Ix.Compile.Image.nEq #[l])
      #[tC, Expr.mkBVar 1, Expr.mkBVar 0]
    some (Expr.mkLam (nm "P") sortV (Expr.mkLam (nm "x") tC (Expr.mkLam (nm "y") tC
      (Expr.mkLam (nm "h") eqTy (Expr.mkLam (nm "p") (Expr.mkBVar 3) (Expr.mkBVar 0) .default)
        .default) .implicit) .implicit) .implicit)

/-- Whether O11b rewrites the pair of `T` (the same decision at both
constants): the side condition, and no demotion of `T.noConfusionType`. -/
def O11b.pairApplies (const? : Name → Option ConstantInfo)
    (classesOf : Name → Option (Array (Array Name))) (demoted : Name → Bool) (t : Name) : Bool :=
  Option.isSome do
    let iv0 ← (match const? t with | some (.inductInfo iv) => some iv | _ => none)
    if iv0.all.size < 2 then none
    let classes ← classesOf t
    if classes.size != 1 then none
    let (_, n) ← enumCtors const? t
    if n != 1 then none
    if demoted (Name.mkStr t "noConfusionType") then none
    pure ()

/-- The rewritten value of one of the pair, when O11b applies to it. -/
def O11b.rewrite (const? : Name → Option ConstantInfo)
    (classesOf : Name → Option (Array (Array Name))) (demoted : Name → Bool)
    (n : Name) (ci : ConstantInfo) : Option DefinitionVal := do
  let (t, isType) ← noConfusionOf n
  let .defnInfo dv := ci | none
  if !O11b.pairApplies const? classesOf demoted t then none
  if !isType && demoted n then none
  let v ← dv.cnst.levelParams[0]?
  if forallArity dv.cnst.type != (if isType then 3 else 4) then none
  let (iv, _) ← enumCtors const? t
  if dv.cnst.levelParams.size != iv.cnst.levelParams.size + 1 then none
  let us := (dv.cnst.levelParams.extract 1 dv.cnst.levelParams.size).map Level.mkParam
  let value ← enumForm iv (Level.mkParam v) us isType
  return { dv with value }

end Ix.Compile.Pass.Opt

end
