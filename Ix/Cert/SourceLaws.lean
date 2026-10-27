import Ix.Cert.Statement
import IxC.Kernel.Rules.Rel

/-! # Source laws: recursor rules and capability laws, at the level of values

A value model (`ValueModel`) fixes types and the values of definitions. It leaves
the values of inductive families, constructors and recursors free beyond their
types. The final statement asks more of the Source model it produces
(`LawModel`): the semantic content of Lean's computation rules, stated over values.

## What is covered
* **Recursor rules** (`RecRuleLaws`, `RecRuleLaw`). Take every stored recursor and
  every rule of it that fires, at every level instantiation. Let the arguments be
  values that fit the recursor's telescope (`Fits`), with the major premise the
  rule's constructor applied to values that fit the constructor's telescope.
  Require Lean's agreements:
  * a canonical rule's constructor parameters are the recursor's parameters;
  * a nested-auxiliary rule's constructor parameters are its stored instantiations
    (`RecRuleFire.nested`), read at the recursor's leading arguments;
  * the constructor's result indices are the recursor's index arguments.

  Then the recursor's value applied to them equals the rule's right-hand side
  applied to the leading arguments and the constructor's fields.
* **Structure η** (`EtaLaw`). A member of an η-capable stored family, at
  parameter values that fit its telescope, is the η constructor applied to the
  parameters and the member's fields. The fields are read through the family's
  projection table when every slot has an entry, else through its stored
  projection functions (`etaFieldVals`), as the checker's η certificate does.
* **Unit-like families** (`UnitLaw`): at fitting parameters, a unit-like stored
  family has at most one member.
* **Projections** (`ProjLaw`): at a stored projection table, the field of a
  constructor value at fitting arguments is the corresponding argument, wherever
  the checker's projection rule fires (`ProjEntry.fireOk`).

These are the public counterparts of the laws a strong model of an accepted
environment keeps internally: `Ix.Kernel.Model.RecRuleLaw` (read through
`Ix.Kernel.Cached.StrongModel.rec_rule`), `EtaLaw`, `UnitLaw` and `TowerEntryLaw`.
They are stated over public denotations only, and quantify over all values that
fit, not only over values of terms.

## What is not covered
* **Theorem and opaque values.** The checker never unfolds them, and a value
  model records none.
* **The quotient's computation rule**, and the rules the set semantics gives
  directly (β, function η, proof irrelevance).
* **The reserved basis families** (`reservedBasisNames`: `Eq`, `Nat`, `PUnit`,
  `Empty`, `False`, the quotient). Their η and unit-like laws are not stated
  here; their values are pinned by the kernel.
* **The checker's step forms.** These are the major's preparation (literals,
  unfolding, the K, η and `And` rescues) and steps between terms rather than
  values. They are stated as step laws in `Ix.Cert.StepLaws` and proved for
  unchanged closures there.

What a `Model` already carries of the roles: `False` denotes the empty set and
`Eq` denotes equality (`Model.false_empty`, `Model.eq_equality`). A `Nat` literal
denotes what its constructor form denotes by the definition of `Denotes`. -/

namespace Ix.Cert

open Ix.Kernel Ix.Kernel.SetTheory

universe w

variable {md : Mode} {V : Type w} [SetTheory V]

/-- **A value applied to argument values**, left to right. -/
noncomputable def spineV (f : V) (xs : List V) : V :=
  xs.foldl SetTheory.app f

/-- **Values fitting a telescope**: `Fits cval env φ ρ T xs ρ' R` peels one binder
of `T` per value. Each value lies in the denotation of its binder's domain, read
under `ρ` extended by the values before it. `ρ'` and `R` are the valuation and the
body left after the peel. -/
inductive Fits (cval : Key md → (LevelParam → Nat) → V) (env : Env md) (φ : LevelParam → Nat) :
    (BVarIdx → V) → Ix.Kernel.Expr md → List V → (BVarIdx → V) → Ix.Kernel.Expr md → Prop
  | nil {ρ : BVarIdx → V} {T : Ix.Kernel.Expr md} : Fits cval env φ ρ T [] ρ T
  | cons {ρ ρ' : BVarIdx → V} {A B R : Ix.Kernel.Expr md} {m : Ix.Kernel.BinderMeta} {Av x : V}
      {xs : List V} :
      Denotes cval env φ ρ A Av → x ∈ˢ Av → Fits cval env φ (push x ρ) B xs ρ' R →
      Fits cval env φ ρ (.forallE A B m) (x :: xs) ρ' R

/-- **The leading values as bound variables**: variable `i` is value `n - 1 - i`;
the innermost binder is variable `0`. -/
noncomputable def leadVal (xs : List V) (n : Nat) (i : BVarIdx) : V :=
  xs.getD (n - 1 - i) SetTheory.empty

/-- **One fired rule's law, at the level of values**, at the stored recursor `c`
(stored as `.recInfo cv mI rP rules`) and its rule `rl` (see the module docstring).

The recursor's arguments `xs` are its `mI` leading arguments (parameters,
motives, minor premises, indices). The major premise is the constructor's value
applied to `ys` (its parameters and fields). Both fit their telescopes. The
agreements are:
* the constructor's parameters are the recursor's (a canonical rule that
  compares them);
* they are the stored instantiations read at the leading arguments (a
  nested-auxiliary rule);
* the indices of the constructor's result (`Ry`'s arguments after its
  parameters) are the recursor's index arguments.

The conclusion is the rule's equation. -/
def RecRuleLaw (cval : Key md → (LevelParam → Nat) → V) (env : Env md) (c : Key md)
    (cv : Ix.Kernel.ConstantVal md) (mI rP : Nat) (rl : Ix.Kernel.RecRule md) : Prop :=
  ∀ (φ : LevelParam → Nat) (us : List Ix.Kernel.Level), us.length = cv.levelParams.length →
  ∀ (cvj : Ix.Kernel.ConstantVal md) (cnP cnF : Nat), env.find? rl.ctor = some (.ctorInfo cvj cnP cnF) →
  ∀ (usj : List Ix.Kernel.Level), usj.length = cvj.levelParams.length →
  Ix.Kernel.Level.substFn φ cvj.levelParams usj =
    Ix.Kernel.Level.substFn φ cvj.levelParams (recFireComparands rl cv.levelParams us cvj.levelParams [] rP).1 →
  ∀ (ρ ρx ρy : BVarIdx → V) (Rx Ry : Ix.Kernel.Expr md) (xs ys : List V),
    xs.length = mI → ys.length = rl.ctorParams + rl.nfields →
    Fits cval env φ ρ (cvj.type.instantiateLevelParams cvj.levelParams usj) ys ρy Ry →
    Fits cval env φ ρ (cv.type.instantiateLevelParams cv.levelParams us)
      (xs ++ [spineV (cval rl.ctor (Ix.Kernel.Level.substFn φ cvj.levelParams usj)) ys]) ρx Rx →
    (rl.paramsBlind = false → rl.fire = .plain →
      ∀ i, i < rl.ctorParams → i < mI →
        ys.getD i SetTheory.empty = xs.getD i SetTheory.empty) →
    (∀ lvls pins, rl.fire = .nested lvls pins → ∀ i, i < rl.ctorParams →
      Denotes cval env φ (leadVal xs rP)
        ((pins.getD i default).instantiateLevelParams cv.levelParams us)
        (ys.getD i SetTheory.empty)) →
    (mI = rP ∨ Ry.getAppArgs.length = rl.ctorParams + (mI - rP)) →
    (∀ i, i < mI - rP →
      Denotes cval env φ ρy (Ry.getAppArgs.getD (rl.ctorParams + i) (.bvar 0))
        (xs.getD (rP + i) SetTheory.empty)) →
    ∀ R, Denotes cval env φ ρ (rl.rhs.instantiateLevelParams cv.levelParams us) R →
      spineV (cval c (Ix.Kernel.Level.substFn φ cv.levelParams us))
          (xs ++ [spineV (cval rl.ctor (Ix.Kernel.Level.substFn φ cvj.levelParams usj)) ys]) =
        spineV R (xs.take rP ++ ys.drop rl.ctorParams)

/-- **The recursor rules hold at the level of values**: every fired rule of every
stored recursor (`RecRuleLaw`). -/
def RecRuleLaws (cval : Key md → (LevelParam → Nat) → V) (env : Env md) : Prop :=
  ∀ (c : Key md) (cv : Ix.Kernel.ConstantVal md) (mI rP : Nat) (rules : List (Ix.Kernel.RecRule md)),
    env.find? c = some (.recInfo cv mI rP rules) → ∀ rl ∈ rules, rl.fire ≠ .inert →
      RecRuleLaw cval env c cv mI rP rl

/-- **The field values of an η-expansion**: for a member `x` of the family `T` at
the parameter values `ts`, its `nF` fields are:
* read through `T`'s projection table when every slot has an entry;
* else the stored projection functions applied to `ts` and `x`.

This is the checker's own choice of spelling (`etaProjs`). -/
noncomputable def etaFieldVals (cval : Key md → (LevelParam → Nat) → V) (env : Env md) (T : Key md)
    (ψ : LevelParam → Nat) (ts : List V) (x : V) (nF : Nat) : List V :=
  if towerSlotsAll env T nF then
    (List.range nF).map fun j => field (j + (((env.findProj? T 0).map (·.off)).getD 0)) x
  else
    (List.range nF).map fun j => spineV (cval (projFnName T j) ψ) (ts ++ [x])

/-- **Structure η at the level of values** for the η-capable stored family `T`
(stored as `.indInfo cvT caps`) with a stored, non-reserved η constructor `C`.
At parameter values `ts` that fit `T`'s telescope, every member of `T` at `ts` is
`C` applied to `ts` and the member's fields (`etaFieldVals`). -/
def EtaLaw (cval : Key md → (LevelParam → Nat) → V) (env : Env md) (T : Key md)
    (cvT : Ix.Kernel.ConstantVal md) (caps : Ix.Kernel.IndCaps md) : Prop :=
  ∀ (C : Key md), caps.etaCtor = some C → reservedBasisNames.contains C = false →
  (∃ (cvC : Ix.Kernel.ConstantVal md) (nP nF : Nat), env.find? C = some (.ctorInfo cvC nP nF)) →
  ∀ (φ : LevelParam → Nat) (us : List Ix.Kernel.Level), us.length = cvT.levelParams.length →
  ∀ (ρ ρ' : BVarIdx → V) (R : Ix.Kernel.Expr md) (ts : List V) (x : V),
    ts.length = caps.etaParams →
    Fits cval env φ ρ (cvT.type.instantiateLevelParams cvT.levelParams us) ts ρ' R →
    x ∈ˢ spineV (cval T (Ix.Kernel.Level.substFn φ cvT.levelParams us)) ts →
    x = spineV (cval C (Ix.Kernel.Level.substFn φ cvT.levelParams us))
      (ts ++ etaFieldVals cval env T (Ix.Kernel.Level.substFn φ cvT.levelParams us) ts x caps.etaFields)

/-- **Unit-like families at the level of values**: at parameter values that fit
the telescope of the unit-like stored family `T`, `T` has at most one member. -/
def UnitLaw (cval : Key md → (LevelParam → Nat) → V) (env : Env md) (T : Key md)
    (cvT : Ix.Kernel.ConstantVal md) (caps : Ix.Kernel.IndCaps md) : Prop :=
  ∀ (φ : LevelParam → Nat) (us : List Ix.Kernel.Level), us.length = cvT.levelParams.length →
  ∀ (ρ ρ' : BVarIdx → V) (R : Ix.Kernel.Expr md) (ts : List V) (x y : V),
    ts.length = caps.unitParams →
    Fits cval env φ ρ (cvT.type.instantiateLevelParams cvT.levelParams us) ts ρ' R →
    x ∈ˢ spineV (cval T (Ix.Kernel.Level.substFn φ cvT.levelParams us)) ts →
    y ∈ˢ spineV (cval T (Ix.Kernel.Level.substFn φ cvT.levelParams us)) ts →
    x = y

/-- **Projections at the level of values**: at the stored projection-table entry
`entry` for field `i`, wherever the checker's projection rule fires, the field
of the constructor applied to fitting arguments `ys` is the corresponding
argument. -/
def ProjLaw (cval : Key md → (LevelParam → Nat) → V) (env : Env md) (entry : Ix.Kernel.ProjEntry md)
    (i : Nat) : Prop :=
  ∀ (φ : LevelParam → Nat) (us : List Ix.Kernel.Level), us.length = entry.levelParams.length →
  entry.fireOk us = true →
  ∀ (cvC : Ix.Kernel.ConstantVal md) (nP nF : Nat), env.find? entry.ctor = some (.ctorInfo cvC nP nF) →
  ∀ (ρ ρ' : BVarIdx → V) (R : Ix.Kernel.Expr md) (ys : List V),
    ys.length = entry.numParams + entry.numFields →
    Fits cval env φ ρ (cvC.type.instantiateLevelParams cvC.levelParams us) ys ρ' R →
    field (i + entry.off) (spineV (cval entry.ctor (Ix.Kernel.Level.substFn φ entry.levelParams us)) ys) =
      ys.getD (entry.numParams + i) SetTheory.empty

/-- **The capability laws hold at the level of values**:
* structure η for every η-capable, non-reserved stored family whose projection
  slots are all of one kind (as the checker's η certificate requires);
* unit-likeness for every unit-like, non-reserved stored family;
* the projection law at every stored projection-table entry. -/
def CapabilityLaws (cval : Key md → (LevelParam → Nat) → V) (env : Env md) : Prop :=
  (∀ (T : Key md) (cvT : Ix.Kernel.ConstantVal md) (caps : Ix.Kernel.IndCaps md),
    env.find? T = some (.indInfo cvT caps) → caps.eta = true →
    reservedBasisNames.contains T = false →
    (towerSlotsAll env T caps.etaFields || recSlotsAll env T caps.etaFields) = true →
    EtaLaw cval env T cvT caps) ∧
  (∀ (T : Key md) (cvT : Ix.Kernel.ConstantVal md) (caps : Ix.Kernel.IndCaps md),
    env.find? T = some (.indInfo cvT caps) → caps.unitlike = true →
    reservedBasisNames.contains T = false →
    UnitLaw cval env T cvT caps) ∧
  (∀ (sn : Key md) (i : Nat) (entry : Ix.Kernel.ProjEntry md), env.findProj? sn i = some entry →
    ProjLaw cval env entry i)

/-- **A value model with the Source laws**: every stored definition denotes its
value (`ValueModel`), and the recursor rules (`RecRuleLaws`) and the capability
laws (`CapabilityLaws`) hold at the level of values. -/
structure LawModel (V : Type w) [SetTheory V] (env : Env md) extends ValueModel V env where
  rec_rule : RecRuleLaws cval env
  caps : CapabilityLaws cval env

end Ix.Cert
