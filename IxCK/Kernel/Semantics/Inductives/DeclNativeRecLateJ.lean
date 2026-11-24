module

public import IxCK.Kernel.Semantics.Inductives.DeclNativeJ

@[expose] public section

/-!
# A recursor for a stored native family

`NativeFam` names what a native install leaves of an inductive family: the completed record,
the stored former, the telescope constant the stages read, and the stored constructors with
their field counts. The model lane keeps the family's data at a model under this summary
(`NativeFamOk`, `Model/Inductives/NativeFam.lean`), so that the recursor's stage applies to the
family at a later environment.

`DeclNativeRecLateRunJ` is that later step over a package: a recursor installed for a family
that is already stored (the first recursor of a family installed without one, or a further
one). It is stated at one environment, with no block position:

* the record is the family's with its recursor fields replaced (`NativeFam.recParts`), and the
  declared record's pins (major index, rule prefix, one rule per stored constructor, each at
  that constructor with its field count);
* the family as stored (`NativeFamStored`): the former at the family's own capability record,
  the constructors, and the family's counts;
* the elimination restriction, and at a large eliminator of a syntactically propositional
  family each constructor's field sorts (`FieldSortsJ`) at this environment;
* the recursor's stage and the recursor stored (`NativeRecJ`), as the native route has them,
  and the recursor consed with its generated rules.
-/

namespace Ix.Kernel.Semantics

open Ix.Kernel (Env Expr Level ConstantVal NativeParts RecRule)

/-- **A native family's summary**: the completed record (its recursor fields are not
read), the stored former, the telescope constant, and the stored constructors in order,
each with its field count. -/
structure NativeFam (md : Ix.Kernel.Mode) where
  /-- the completed record; `cvR`, `elim`, `large`, `rhss` and `recPinned` are not read -/
  p : NativeParts md
  /-- the stored former -/
  cvS : ConstantVal md
  /-- the telescope constant -/
  cvTa : ConstantVal md
  /-- the stored constructors, in order -/
  ctorsA : List (ConstantVal md × Nat)

/-- The record of a recursor over a stored family: the family's record with its recursor fields
replaced and the structural pin granted. Every family projection reduces to the family's. -/
def NativeFam.recParts (fam : NativeFam md) (cvR : ConstantVal md) (elim : LevelParam)
    (large : Bool) (rhs₀ : List (Expr md)) : NativeParts md :=
  { fam.p with cvR := cvR, elim := elim, large := large, rhss := rhs₀, recPinned := true }

/-- What the store holds of the family, and the family's counts: `NativeFront`
(`Model/StoreFold.lean`) without its `store` field, the former at the family's own capability
record. Only lookups and facts about the summary, so it is kept along `EnvExt.find`. -/
structure NativeFamStored (env : Env md) (fam : NativeFam md) : Prop where
  former : env.find? fam.p.cvT.name = some (.indInfo fam.cvS (Ix.Kernel.nativeCaps fam.p))
  ctor : ∀ (j : Nat) (cA : ConstantVal md × Nat), fam.ctorsA[j]? = some cA →
    env.find? cA.1.name = some (.ctorInfo cA.1 fam.p.nP cA.2) ∧
    cA.1.levelParams = fam.p.cvT.levelParams ∧
    ∃ cbs es, cA.1.type.stripPis (fam.p.nP + cA.2) = some (cbs,
      Expr.mkAppN (.const fam.p.cvT.name (fam.p.cvT.levelParams.map .param))
        (Ix.Kernel.structPsAt cA.2 fam.p.nP ++ es)) ∧
      es.length = fam.p.nIdx
  lenA : fam.ctorsA.length = fam.p.ctors.length
  lenK : fam.ctorsA.length = fam.p.kinds.length

/-- **A recursor for a stored native family, over a package.** `cvR`, `mI`, `rP`, `rules` are
the record as declared; `env` is the current environment (no block position, no staged
environment). -/
def DeclNativeRecLateRunJ (J : Judgements md) (env : Env md) (fam : NativeFam md)
    (cvR : ConstantVal md) (mI rP : Nat) (rules : List (RecRule md)) (env₂ : Env md) : Prop :=
  ∃ (elim : LevelParam) (large : Bool) (pR : NativeParts md) (cvRa : ConstantVal md)
    (rhss : List (Expr md)),
    pR = fam.recParts cvR elim large (rules.map (·.rhs)) ∧
    -- the record's pins (what `nativeRecPinOk` decides)
    mI = pR.majorIdx ∧ rP = pR.rulePrefix ∧ rules.length = fam.ctorsA.length ∧
    (∀ (j : Nat) (r : RecRule md) (cA : ConstantVal md × Nat), rules[j]? = some r →
      fam.ctorsA[j]? = some cA → r.ctor = cA.1.name ∧ r.nfields = cA.2) ∧
    -- the family, as stored
    NativeFamStored env fam ∧
    -- the elimination restriction
    (large = true →
      (∀ φ : LevelParam → Nat, Level.eval φ fam.p.resSort ≠ 0) ∨ fam.ctorsA.length < 2) ∧
    -- a large eliminator at a syntactically propositional family: every field of every
    -- constructor is a proposition or one of the result's index arguments, at this environment
    (large = true → fam.p.isProp = true →
      ∀ (j : Nat) (cA : ConstantVal md × Nat), fam.ctorsA[j]? = some cA →
        ∃ (fvsP : List (Expr md)) (crest : Expr md) (xFvs : List (Expr md)) (xrest : Expr md)
          (sorts : List Level),
          Ix.Kernel.openPisAtFvars fam.p.nP cA.1.type 0 = some (fvsP, crest) ∧
          Ix.Kernel.openPisAtFvars cA.2 crest fam.p.nP = some (xFvs, xrest) ∧
          FieldSortsJ J env true true fam.p.resSort fam.p.nP xFvs
            (xrest.getAppArgs.drop fam.p.nP) cA.2 sorts) ∧
    -- the recursor's stage and the recursor stored, as `DeclNativeRunJ` has them
    NativeRecJ J env pR fam.cvTa fam.ctorsA cvRa rhss ∧
    env₂ = ⟨.recInfo cvRa pR.majorIdx pR.rulePrefix
      (Ix.Kernel.sumRules env.find? cvRa.name pR.nP pR.majorIdx pR.rulePrefix cvRa.type
        fam.ctorsA rhss) :: env.consts⟩

end Ix.Kernel.Semantics
