module

public import IxC.Kernel.Semantics.Inductives.DeclNative
public import IxC.Kernel.Semantics.DeclIndJ
public import IxC.Kernel.Verify.Inductives.SumInv
public import IxC.Kernel.Verify.Inductives.FixInv
public import IxC.Kernel.Verify.Inductives.SumRec
import IxC.Kernel.Verify.Extend.Inversions
import IxC.Kernel.Verify.Level
import IxC.Kernel.Verify.Inductives.SumWF
import IxC.Kernel.Verify.Inductives.FixWF
import IxC.Kernel.Verify.Inductives.StructWF
public import IxC.Kernel.Verify.EnvWF
public import IxC.Kernel.Semantics.Inductives.WrapRelFacts

@[expose] public section

/-!
# The native inductive route over a judgement package

`DeclNativeRun` (`Semantics/Inductives/DeclNative.lean`) records what the kernel's
fold checked for a block its recogniser reads as one inductive type with its
constructors and its recursor (`nativeParts?`): the former's stage
(`checkSumInd`), the constructors' stage (`checkSumCtors`), the fields' kinds
(`classifyFixKinds`), the elimination restriction, the index binders' sorts and
the fields' universes (`checkStructFieldSortsI`), the recursor's stage
(`checkNativeRec`) and the projection table (`checkNativeTable`).

This module states that record over a judgement package (`Judgements`,
`Semantics/DeclJ.lean`), as `DeclJ` does for the value kinds and `DeclIndJ` for
the modeled route:

* every run of a checker function becomes the package's relation: the constant
  checks (`ConstantValCheckJ`, the package form of `checkConstantVal`), the
  parameter-domain pins (`StructDomsJ`), the fields' sorts (`FieldSortsJ`), and
  the recursor type's typing and its conversion with the declared one;
* the level comparisons the stages make are stated by their meaning at every
  assignment (`Level.eval`): a field's universe below the family's, a field that
  is a proposition, a sort that is never zero;
* the guards on stored data and the kernel's pure constructions (the recogniser,
  the kinds' classification, the generated recursor type and rules, the rules'
  comparison, the table) are unchanged.

`DeclNativeRunJ J env p₀ env₂` is the native route at a package; the kernel's
record gives it at its runs (`declNativeRun_runJ`). `DeclNativeNoRecRunJ` is the
same route for a one-type block without its recursor record (`nativePartsNoRec?`):
the former's and the constructors' stages and the table, with no recursor stage.
`IndRoutesJ` is the inductive kind's routes: native at the recognised parts,
modeled (`DeclIndRunJ`), or native without a recursor.
-/

namespace Ix.Kernel.Semantics

open Ix.Kernel (Env Expr Key Level CheckMode ConstantVal ConstantInfo IndCaps
  InductiveShape NativeParts RecRule fueledOps checkSumInd checkSumCtors checkSumCtor
  checkNativeRec checkNativeTable consSumCtors sumRules nativeFieldsOk nativeCaps
  nativeCapsAt)

/-! ## The stage records -/

/-- **`checkConstantVal` over a package**: the front door's guards, the type's
annotation, its scoping, and its typing at a sort; the checked constant carries
the annotated type. -/
def ConstantValCheckJ (J : Judgements md) (env : Env md) (cv cv' : ConstantVal md) : Prop :=
  ∃ type', ConstantValRunJ J env cv type' ∧ cv' = { cv with type := type' }

/-- **The former the block stores**, against the checked declared former `cvTa₀`
and the telescope constant `cvTa` the later stages read: the telescope constant
itself, as the kernel stores it, or the declared former, definitionally equal to
the telescope, at a family with indices (so with no η, unit-like or projection
capability, which read arities off the stored type). One definition, so that which
constant is stored is decided in one place. -/
def FormerStoredJ (J : Judgements md) (env : Env md) (nIdx : Nat)
    (cvTa₀ cvTa cvS : ConstantVal md) : Prop :=
  cvS = cvTa ∨ (cvS = cvTa₀ ∧ J.defeq env 0 cvTa₀.type cvTa.type ∧ nIdx ≠ 0)

/-- **The former's stage** (`checkSumInd`) over a package. The declared type is
checked (`cvTa₀`); the telescope constant `cvTa` the later stages read is that
constant, or (where the declared type is not a syntactic telescope ending in a
sort) a constant of the same name and level parameters checked from scratch at
another type. Either way its type is a syntactic telescope of the parameters and
indices ending in the sort `s` the completed record carries. The stored former is
`FormerStoredJ`'s. -/
def SumIndRunJ (J : Judgements md) (env : Env md) (p : InductiveShape md)
    (capsOf : InductiveShape md → IndCaps md) (envI : Env md) (cvTa : ConstantVal md)
    (p' : InductiveShape md) : Prop :=
  ∃ (cvTa₀ : ConstantVal md) (s : Level) (bs : List (Expr md × Ix.Kernel.BinderMeta))
    (cvS : ConstantVal md),
    ConstantValCheckJ J env p.cvT cvTa₀ ∧
    (cvTa = cvTa₀ ∨ ∃ ty, ConstantValCheckJ J env { p.cvT with type := ty } cvTa) ∧
    cvTa.type.stripPis (p.nP + p.nIdx) = some (bs, .sort s) ∧
    FormerStoredJ J env p.nIdx cvTa₀ cvTa cvS ∧
    p' = p.withSort s ∧
    envI = ⟨.indInfo cvS (capsOf p') :: env.consts⟩

/-- **The fields' sorts** (`checkStructFieldSortsI`) over a package, positionally:
one sort per field, the sort of the field's type at the field's own depth; at a
family that may be data each field's universe lies below the family's at every
assignment; at a propositional family with a large eliminator each field is a
proposition at every assignment or one of the residual's index expressions. -/
def FieldSortsJ (J : Judgements md) (env : Env md) (isProp large : Bool) (s : Level)
    (nP : Nat) (fvs idxArgs : List (Expr md)) (n : Nat) (sorts : List Level) : Prop :=
  sorts.length = n ∧
  ∀ i, i < n → ∃ (fv ty : Expr md) (u : Level), fvs[i]? = some fv ∧ sorts[i]? = some u ∧
    J.infer env (nP + i) (Expr.fvarTypeD fv) ty ∧ J.sort env (nP + i) ty u ∧
    (isProp = false → ∀ φ : LevelParam → Nat, Level.eval φ u ≤ Level.eval φ s) ∧
    (isProp = true → large = true →
      (∀ φ : LevelParam → Nat, Level.eval φ u = 0) ∨ idxArgs.contains fv = true)

/-- **The parameter domains' pins** (`checkStructDomsAt`) over a package: each
opened binder's domain is convertible with the matching domain at its own depth. -/
def StructDomsJ (J : Judgements md) (env : Env md) (off : Nat) (fvs doms : List (Expr md))
    (n : Nat) : Prop :=
  ∀ i, i < n → ∃ a b, fvs[i]? = some a ∧ doms[i]? = some b ∧
    J.defeq env (off + i) (Expr.fvarTypeD a) b

/-- **One constructor's stage** (`checkSumCtor`) over a package. The declared
constructor is checked; the stored one is that constant, or (where the positivity
normalisation rewrote a field's domain) a constant of the same name and level
parameters checked from scratch at the rewritten type. Then: the stored type's
residual is the family at its parameters and `nIdx` index expressions; its
parameter domains are pinned against the former's; its field domains and index
expressions resolve before the block (`env₀`); and its fields' sorts. -/
def SumCtorRunJ (J : Judgements md) (env₀ env : Env md) (T : Key md)
    (lps : List LevelParam) (nP nIdx : Nat) (resSort : Level) (isProp large : Bool)
    (cvC : ConstantVal md) (nF : Nat) (cvTa cvCa : ConstantVal md) (sorts : List Level) :
    Prop :=
  (∃ cvCa₀, ConstantValCheckJ J env cvC cvCa₀ ∧
    (cvCa = cvCa₀ ∨ ∃ ty', ConstantValCheckJ J env { cvC with type := ty' } cvCa)) ∧
  (∃ (cbs : List (Expr md × Ix.Kernel.BinderMeta)) (es : List (Expr md)),
    cvCa.type.stripPis (nP + nF)
      = some (cbs, Expr.mkAppN (.const T (lps.map .param)) (Ix.Kernel.structPsAt nF nP ++ es)) ∧
    es.length = nIdx) ∧
  ∃ (fvsP : List (Expr md)) (crest : Expr md) (tfvs : List (Expr md)) (trest : Expr md)
    (xFvs : List (Expr md)) (idxArgs : List (Expr md)),
    openPisAtFvars nP cvCa.type 0 = some (fvsP, crest) ∧
    openPisAtFvars nP cvTa.type 0 = some (tfvs, trest) ∧
    StructDomsJ J env 0 fvsP (tfvs.map Expr.fvarTypeD) nP ∧
    openPisAtFvars nF crest nP
      = some (xFvs, Expr.mkAppN (.const T (lps.map .param)) (fvsP ++ idxArgs)) ∧
    idxArgs.length = nIdx ∧
    (∀ x ∈ xFvs, x.fvarTypeD.constsResolve env₀ = true) ∧
    (∀ e ∈ idxArgs, e.constsResolve env₀ = true) ∧
    FieldSortsJ J env isProp large resSort nP xFvs idxArgs nF sorts

/-- **All constructors' stages** (`checkSumCtors`) over a package, positionally:
one stored constructor and one sort list per declared constructor, with the
declared field count. -/
def SumCtorsRunJ (J : Judgements md) (env₀ env : Env md) (T : Key md)
    (lps : List LevelParam) (nP nIdx : Nat) (resSort : Level) (isProp large : Bool)
    (cvTa : ConstantVal md) (cs ctorsA : List (ConstantVal md × Nat))
    (sortss : List (List Level)) : Prop :=
  ctorsA.length = cs.length ∧ sortss.length = cs.length ∧
  ∀ (j : Nat) (c cA : ConstantVal md × Nat), cs[j]? = some c → ctorsA[j]? = some cA →
    cA.2 = c.2 ∧ ∃ sorts, sortss[j]? = some sorts ∧
      SumCtorRunJ J env₀ env T lps nP nIdx resSort isProp large c.1 c.2 cvTa cA.1 sorts

/-! ## The zero-ness the constructors carry -/

/-- Every `∀` binder along the spine carries the zero-ness datum `z`. -/
def pwsAll (z : Ix.Kernel.PropWhen) : Expr md → Bool
  | .forallE _ b m => m.pw == z && pwsAll z b
  | _ => true

/-- The telescope of `e` ends in the family `T` applied (its spine's head, past the binders). -/
def famHead (T : Key md) : Expr md → Bool
  | .forallE _ b _ => famHead T b
  | .app f _ => famHead T f
  | .const c _ => c == T
  | _ => false

/-- A domain whose telescope ends in the family `T` carries `z` at every binder. -/
def famDomOk (T : Key md) (z : Ix.Kernel.PropWhen) (dom : Expr md) : Bool :=
  !famHead T dom || pwsAll z dom

/-- **A constructor type's binders carry `z`**: every binder of its telescope, and every
binder of each of its domains that ends in the family `T`. -/
def ctorZeroOk (T : Key md) (z : Ix.Kernel.PropWhen) : Expr md → Bool
  | .forallE dom b m => m.pw == z && famDomOk T z dom && ctorZeroOk T z b
  | _ => true

/-- **What the later stages read of the former**: the stored former is the telescope
constant, or every stored constructor's binders carry the zero-ness of the family's result
sort (`ctorZeroOk`). At the telescope the zero-ness follows from the constructors' typing,
which reads the former's type; at a declared former that is not a syntactic telescope it is
checked, since a derivation reaches the family's sort through the declared type's
reductions. -/
def FormerReadJ (env₁ : Env md) (p : NativeParts md) (cvTa : ConstantVal md)
    (ctorsA : List (ConstantVal md × Nat)) : Prop :=
  (∃ caps, env₁.find? p.cvT.name = some (.indInfo cvTa caps)) ∨
  ctorsA.all (fun cA => ctorZeroOk p.cvT.name (Level.zeronessOf p.resSort) cA.1.type) = true

/-- **The recursor's stage** (`checkNativeRec`) over a package: the record's pins
(its level parameters are the generated ones; its rule count, rules' constructors
and field counts and argument sums are the generated ones), the declared recursor
checked, the generated type scoped, typed at a sort and convertible with the
declared one, the generated rules scoped at the environment holding the
recursor; the recursor `cvRa` carries the generated type and `rhss` are the
generated rules. -/
def NativeRecRunJ (J : Judgements md) (env : Env md) (p : NativeParts md)
    (cvTa : ConstantVal md) (ctorsA : List (ConstantVal md × Nat)) (cvRa : ConstantVal md)
    (rhss : List (Expr md)) : Prop :=
  Ix.Kernel.nativeRecLpsOk p.toInductiveShape = true ∧ p.recPinned = true ∧
  ∃ (cvRi : ConstantVal md) (recTy sty : Expr md) (u : Level),
    ConstantValCheckJ J env p.cvR cvRi ∧
    Ix.Kernel.structRecTyR p.cvT.name p.cvT.levelParams p.elim p.large p.nP p.nIdx cvTa.type
      (Ix.Kernel.nativeCtors4 ctorsA p.kinds) = some recTy ∧
    recTy.allLevelParamsDefined p.cvR.levelParams = true ∧
    recTy.constsResolve env = true ∧
    recTy.looseBVarsBounded 0 = true ∧ recTy.hasFvar = false ∧
    J.infer env 0 recTy sty ∧ J.sort env 0 sty u ∧
    J.defeq env 0 cvRi.type recTy ∧
    Ix.Kernel.checkNativeRules (m := Ix.Kernel.CheckM md)
      ⟨.recInfo ⟨p.cvR.name, p.cvR.levelParams, recTy⟩ p.majorIdx p.rulePrefix []
        :: env.consts⟩
      p.cvR.levelParams p.cvT.name p.cvT.levelParams p.elim p.large p.nP p.nIdx cvTa.type
      (Ix.Kernel.nativeCtors4 ctorsA p.kinds) p.cvR.name (p.cvR.levelParams.map .param)
      (Ix.Kernel.nativeCtors4 ctorsA p.kinds).length 0 = .ok rhss ∧
    cvRa = ⟨p.cvR.name, p.cvR.levelParams, recTy⟩

/-- **The recursor the block stores**, against the generated recursor `cvRg` and its
rules `rhsG`: the generated one, as the kernel stores it, or the declared one. The
declared recursor is checked (`cvRi`); its type and each of its rules are the
generated ones with type-annotation wrappers consumed at binder domains (`WrapRel`,
at the lookup of the environment the recursor is checked at), the type and the rules
carry no `let`, and the rules annotate the declared rules at the environment holding
the recursor. One definition, so that which recursor is stored is decided in one
place. The generated type fires every rule (`recRulePlain_structRecTyR`), and so does
the declared one, whose major premise is the generated one's
(`WrapRel.major_structFamI`). -/
def RecStoredJ (J : Judgements md) (env : Env md) (p : NativeParts md)
    (cvRg : ConstantVal md) (rhsG : List (Expr md))
    (cvRa : ConstantVal md) (rhss : List (Expr md)) : Prop :=
  (cvRa = cvRg ∧ rhss = rhsG) ∨
  ∃ cvRi : ConstantVal md,
    ConstantValCheckJ J env p.cvR cvRi ∧
    cvRa = ⟨p.cvR.name, p.cvR.levelParams, cvRi.type⟩ ∧
    WrapRel env.find? cvRg.type cvRi.type ∧
    Forall₂ (WrapRel env.find?) rhsG rhss ∧
    (∀ r ∈ rhss, letFree r = true) ∧
    Forall₂ (J.annot ⟨.recInfo cvRa p.majorIdx p.rulePrefix [] :: env.consts⟩ 0) p.rhss
      rhss ∧
    letFree cvRi.type = true

/-- **The recursor's stage and the recursor stored**: the stage's generated recursor and
rules, and the recursor and rules the block stores. -/
def NativeRecJ (J : Judgements md) (env : Env md) (p : NativeParts md)
    (cvTa : ConstantVal md) (ctorsA : List (ConstantVal md × Nat)) (cvRa : ConstantVal md)
    (rhss : List (Expr md)) : Prop :=
  ∃ (cvRg : ConstantVal md) (rhsG : List (Expr md)),
    NativeRecRunJ J env p cvTa ctorsA cvRg rhsG ∧ RecStoredJ J env p cvRg rhsG cvRa rhss

/-! ## The block -/

/-- **The native route over a package**: the stages of `DeclNativeRun` with every
checker run read as the package's relation. `env` is the pre-block environment;
the former is stored at the capability record of an `is_rec` verdict, the
constructors are checked at its environment, the kinds classified on them, and
the classified record equals the one the former carries. -/
def DeclNativeRunJ (J : Judgements md) (env : Env md) (p₀ : NativeParts md)
    (env₂ : Env md) : Prop :=
  (p₀.ctors.map (·.1.name)).Nodup ∧
  ∃ (isRec : Bool) (env₁ : Env md) (cvTa : ConstantVal md) (p₁ : InductiveShape md)
    (p : NativeParts md) (ctorsA : List (ConstantVal md × Nat))
    (sortss : List (List Level)) (kinds : List (List RecFieldKind))
    (cvRa : ConstantVal md) (rhss : List (Expr md)) (tfvs : List (Expr md)) (trest : Expr md)
    (isorts : List Level),
    -- the former's stage completes the record with the sort it read
    SumIndRunJ J env p₀.toInductiveShape (fun p₁ => nativeCapsAt p₁ isRec) env₁ cvTa p₁ ∧
    p = (p₀.complete p₁).withKinds kinds ∧
    SumCtorsRunJ J env₁ env₁ p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp
      p.large cvTa p.ctors ctorsA sortss ∧
    Ix.Kernel.classifyFixKinds (m := Ix.Kernel.CheckM md) p.cvT.name p.cvT.levelParams p.nP
      p.nIdx ctorsA = .ok kinds ∧
    -- the record the block owes is the one the former carries
    nativeCaps p = nativeCapsAt p₁ isRec ∧
    -- the elimination restriction: a large eliminator needs a sort that is never
    -- zero unless the block has at most one constructor
    (p.large = true →
      (∀ φ : LevelParam → Nat, Level.eval φ p.resSort ≠ 0) ∨ p.ctors.length < 2) ∧
    -- the index binders' sorts, read
    openPisAtFvars (p.nP + p.nIdx) cvTa.type 0 = some (tfvs, trest) ∧
    FieldSortsJ J env₁ true false p.resSort p.nP (tfvs.drop p.nP) [] p.nIdx isorts ∧
    -- the kinds re-checked on the stored constructors
    nativeFieldsOk env p.cvT.name p.cvT.levelParams p.nP p.nIdx ctorsA p.kinds = true ∧
    -- the declared rules are the generated ones
    nativeRulesOk p.cvR.name (p.cvR.levelParams.map .param) .never p.nP p.ctors.length
      ctorsA p.kinds p.rhss p.cvR.type = true ∧
    -- the recursor; every stored rule fires (`NativeRecJ.plain`: the kernel's test of the
    -- stored type's major premise holds of every recursor this relation stores)
    NativeRecJ J (consSumCtors p.nP ctorsA env₁) p cvTa ctorsA cvRa rhss ∧
    -- the projection table at a structure-like block
    checkNativeTable (m := Ix.Kernel.CheckM md) p ctorsA sortss
      ⟨.recInfo cvRa p.majorIdx p.rulePrefix
        (sumRules (consSumCtors p.nP ctorsA env₁).find? cvRa.name p.nP p.majorIdx p.rulePrefix
          cvRa.type ctorsA rhss)
        :: (consSumCtors p.nP ctorsA env₁).consts⟩ = .ok env₂ ∧
    -- what the stages read of the former
    FormerReadJ env₁ p cvTa ctorsA

/-! ## The native route without a recursor record -/

/-- **The recursor slot of a block read without its recursor record**: the small
eliminator's level shape (the block's own level parameters) under a derived key
(`Key.aux`, which no input names), with no rule and argument sums `0`. It only fills
the recogniser's recursor fields: the route without a recursor reads none of them
and installs nothing for them. -/
def nativeRecStub (cvT : ConstantVal md) : ConstantInfo md :=
  .recInfo ⟨Ix.Kernel.auxKey cvT.name .recursor, cvT.levelParams, .sort .zero⟩ 0 0 []

/-- **A one-type block without its recursor record**: the type former followed by
constructors only. It is recognised as `nativeParts?` recognises the block with the
recursor slot `nativeRecStub` appended, so every condition on the former and the
constructors is the same. The slot is the small eliminator (`large = false`), so
no elimination restriction applies. A former declared at a definition is not
recognised here: its index count is read off the recursor record, and the slot has
none. -/
def nativePartsNoRec? (nPd : Nat) (block : List (ConstantInfo md)) :
    Option (NativeParts md) :=
  match block with
  | .indInfo cvT caps :: rest =>
    if rest.all (fun | .ctorInfo .. => true | _ => false) then
      Ix.Kernel.nativeParts? nPd (.indInfo cvT caps :: (rest ++ [nativeRecStub cvT]))
    else none
  | _ => none

/-- **The native route without a recursor record, over a package**: the stages of
`DeclNativeRunJ` for the former and the constructors (the former's stage, the
constructors' stage, the kinds' classification, the capability record, the index
binders' sorts, the kinds re-checked on the stored constructors), then, at a
structure-like block, the projection table over the constructors' environment. No
recursor is generated, compared or installed, so the block has no ι rule. -/
def DeclNativeNoRecRunJ (J : Judgements md) (env : Env md) (p₀ : NativeParts md)
    (env₂ : Env md) : Prop :=
  (p₀.ctors.map (·.1.name)).Nodup ∧
  ∃ (isRec : Bool) (env₁ : Env md) (cvTa : ConstantVal md) (p₁ : InductiveShape md)
    (p : NativeParts md) (ctorsA : List (ConstantVal md × Nat))
    (sortss : List (List Level)) (kinds : List (List RecFieldKind))
    (tfvs : List (Expr md)) (trest : Expr md) (isorts : List Level),
    SumIndRunJ J env p₀.toInductiveShape (fun p₁ => nativeCapsAt p₁ isRec) env₁ cvTa p₁ ∧
    p = (p₀.complete p₁).withKinds kinds ∧
    SumCtorsRunJ J env₁ env₁ p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp
      p.large cvTa p.ctors ctorsA sortss ∧
    Ix.Kernel.classifyFixKinds (m := Ix.Kernel.CheckM md) p.cvT.name p.cvT.levelParams p.nP
      p.nIdx ctorsA = .ok kinds ∧
    nativeCaps p = nativeCapsAt p₁ isRec ∧
    openPisAtFvars (p.nP + p.nIdx) cvTa.type 0 = some (tfvs, trest) ∧
    FieldSortsJ J env₁ true false p.resSort p.nP (tfvs.drop p.nP) [] p.nIdx isorts ∧
    nativeFieldsOk env p.cvT.name p.cvT.levelParams p.nP p.nIdx ctorsA p.kinds = true ∧
    -- the projection table at a structure-like block, over the constructors
    checkNativeTable (m := Ix.Kernel.CheckM md) p ctorsA sortss (consSumCtors p.nP ctorsA env₁)
      = .ok env₂ ∧
    -- what the stages read of the former
    FormerReadJ env₁ p cvTa ctorsA

/-- **An inductive block's routes over a package**: the native route at the parts
the recogniser reads off the block, the modeled route (`DeclIndRunJ`, stated for
every block), or the native route without a recursor record at the parts read off
a one-type block that has none (`nativePartsNoRec?`). -/
def IndRoutesJ (J : Judgements md) (env : Env md) (block : List (ConstantInfo md))
    (nP : Nat) (env₂ : Env md) : Prop :=
  (∃ p₀, Ix.Kernel.nativeParts? nP block = some p₀ ∧ DeclNativeRunJ J env p₀ env₂) ∨
  DeclIndRunJ J env block env₂ ∨
  (∃ p₀, nativePartsNoRec? nP block = some p₀ ∧ DeclNativeNoRecRunJ J env p₀ env₂)

/-! ## Facts the records carry -/

theorem ConstantValCheckJ.fresh {J : Judgements md} {env : Env md} {cv cv' : ConstantVal md}
    (h : ConstantValCheckJ J env cv cv') : env.find? cv.name = none := by
  obtain ⟨_, hrun, -⟩ := h
  exact Option.isNone_iff_eq_none.mp hrun.1

theorem ConstantValCheckJ.shape {J : Judgements md} {env : Env md} {cv cv' : ConstantVal md}
    (h : ConstantValCheckJ J env cv cv') : cv.name.isProjFnShape = false := by
  obtain ⟨_, hrun, -⟩ := h
  exact hrun.2.2.1

theorem ConstantValCheckJ.name_eq {J : Judgements md} {env : Env md} {cv cv' : ConstantVal md}
    (h : ConstantValCheckJ J env cv cv') : cv'.name = cv.name := by
  obtain ⟨_, -, rfl⟩ := h
  rfl

theorem ConstantValCheckJ.levelParams_eq {J : Judgements md} {env : Env md}
    {cv cv' : ConstantVal md} (h : ConstantValCheckJ J env cv cv') :
    cv'.levelParams = cv.levelParams := by
  obtain ⟨_, -, rfl⟩ := h
  rfl

/-- **A constant check's facts** (`checkConstantVal_inv` over a package), in the
kernel inversion's order. -/
theorem ConstantValCheckJ.inv {J : Judgements md} {env : Env md} {cv cv' : ConstantVal md}
    (h : ConstantValCheckJ J env cv cv') :
    env.find? cv.name = none ∧
    reservedBasisNames.contains cv.name = false ∧
    cv.name.isProjFnShape = false ∧
    LevelParam.nodup cv.levelParams = true ∧
    cv.type.looseBVarsBounded 0 = true ∧
    cv.type.hasFvar = false ∧
    ∃ type stype u,
      J.annot env 0 cv.type type ∧
      type.allLevelParamsDefined cv.levelParams = true ∧
      type.constsResolve env = true ∧
      J.infer env 0 type stype ∧
      J.sort env 0 stype u ∧
      cv' = { cv with type := type } := by
  obtain ⟨type, ⟨hf, hres, hpsh, hnd, hlbt, hitf, hann, htp, htr, stype, u, hst, hsort⟩, rfl⟩ := h
  exact ⟨Option.isNone_iff_eq_none.mp hf, hres, hpsh, hnd, hlbt, hitf, type, stype, u, hann,
    htp, htr, hst, hsort, rfl⟩

/-- A stored constructor keeps the declared name and level parameters; its name is
fresh where it is checked and passes the front door's shape test. -/
theorem SumCtorRunJ.names {J : Judgements md} {env₀ env : Env md} {T : Key md}
    {lps : List LevelParam} {nP nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {cvC : ConstantVal md} {nF : Nat} {cvTa cvCa : ConstantVal md} {sorts : List Level}
    (h : SumCtorRunJ J env₀ env T lps nP nIdx resSort isProp large cvC nF cvTa cvCa sorts) :
    cvCa.name = cvC.name ∧ cvCa.levelParams = cvC.levelParams ∧
      env.find? cvC.name = none ∧ cvC.name.isProjFnShape = false := by
  obtain ⟨⟨cvCa₀, h₀, hbr⟩, -⟩ := h
  refine ⟨?_, ?_, h₀.fresh, h₀.shape⟩
  · rcases hbr with rfl | ⟨ty', h₁⟩
    · exact h₀.name_eq
    · exact h₁.name_eq
  · rcases hbr with rfl | ⟨ty', h₁⟩
    · exact h₀.levelParams_eq
    · exact h₁.levelParams_eq

/-- A stored constructor is a constant check of the declared one at some type. -/
theorem SumCtorRunJ.check {J : Judgements md} {env₀ env : Env md} {T : Key md}
    {lps : List LevelParam} {nP nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {cvC : ConstantVal md} {nF : Nat} {cvTa cvCa : ConstantVal md} {sorts : List Level}
    (h : SumCtorRunJ J env₀ env T lps nP nIdx resSort isProp large cvC nF cvTa cvCa sorts) :
    ∃ ty', ConstantValCheckJ J env { cvC with type := ty' } cvCa := by
  obtain ⟨⟨cvCa₀, h₀, hbr⟩, -⟩ := h
  rcases hbr with rfl | hty
  · exact ⟨cvC.type, h₀⟩
  · exact hty

/-- The stored former keeps the declared name and level parameters; the name is
fresh before the block and passes the front door's shape test. -/
theorem SumIndRunJ.former {J : Judgements md} {env envI : Env md} {p p' : InductiveShape md}
    {capsOf : InductiveShape md → IndCaps md} {cvTa : ConstantVal md}
    (h : SumIndRunJ J env p capsOf envI cvTa p') :
    cvTa.name = p.cvT.name ∧ cvTa.levelParams = p.cvT.levelParams ∧
      env.find? p.cvT.name = none ∧ p.cvT.name.isProjFnShape = false := by
  obtain ⟨cvTa₀, s, bs, -, h₀, hbr, -⟩ := h
  refine ⟨?_, ?_, h₀.fresh, h₀.shape⟩
  · rcases hbr with rfl | ⟨ty, h₁⟩
    · exact h₀.name_eq
    · exact h₁.name_eq
  · rcases hbr with rfl | ⟨ty, h₁⟩
    · exact h₀.levelParams_eq
    · exact h₁.levelParams_eq

/-- **The former the stage stores**: the telescope constant, or a checked constant of the
declared former's name and level parameters, definitionally equal to it, at a family with
indices. -/
def StoredFormer (J : Judgements md) (env : Env md) (p : InductiveShape md)
    (cvTa cvS : ConstantVal md) : Prop :=
  cvS = cvTa ∨
    (ConstantValCheckJ J env p.cvT cvS ∧ J.defeq env 0 cvS.type cvTa.type ∧ p.nIdx ≠ 0)

/-- **The former's stage's shape** (`checkSumInd_shape` over a package): a constant
check of the declared former at some type, the completed record, the stored
former (`StoredFormer`), and the telescope ending in the record's sort. -/
theorem SumIndRunJ.shape {J : Judgements md} {env envI : Env md} {p p' : InductiveShape md}
    {capsOf : InductiveShape md → IndCaps md} {cvTa : ConstantVal md}
    (h : SumIndRunJ J env p capsOf envI cvTa p') :
    ∃ (cvT : ConstantVal md) (s : Level),
      cvT.name = p.cvT.name ∧ cvT.levelParams = p.cvT.levelParams ∧
      ConstantValCheckJ J env cvT cvTa ∧
      p' = p.withSort s ∧
      (∃ cvS, envI = ⟨.indInfo cvS (capsOf p') :: env.consts⟩ ∧ StoredFormer J env p cvTa cvS) ∧
      ∃ bs, cvTa.type.stripPis (p.nP + p.nIdx) = some (bs, .sort s) := by
  obtain ⟨cvTa₀, s, bs, cvS, h₀, hbr, hstrip, hSt, hp', henv⟩ := h
  have hS : StoredFormer J env p cvTa cvS := by
    rcases hSt with rfl | ⟨rfl, hdq, hn⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨h₀, hdq, hn⟩
  rcases hbr with rfl | ⟨ty, h₁⟩
  · exact ⟨p.cvT, s, rfl, rfl, h₀, hp', ⟨cvS, henv, hS⟩, bs, hstrip⟩
  · exact ⟨{ p.cvT with type := ty }, s, rfl, rfl, h₁, hp', ⟨cvS, henv, hS⟩, bs, hstrip⟩

/-- The stored former keeps the telescope constant's name and level parameters. -/
theorem StoredFormer.name_lps {J : Judgements md} {env : Env md} {p : InductiveShape md}
    {cvTa cvS : ConstantVal md} (hT : cvTa.name = p.cvT.name ∧ cvTa.levelParams = p.cvT.levelParams)
    (h : StoredFormer J env p cvTa cvS) :
    cvS.name = cvTa.name ∧ cvS.levelParams = cvTa.levelParams := by
  rcases h with rfl | ⟨hc, -, -⟩
  · exact ⟨rfl, rfl⟩
  · rw [hc.name_eq, hc.levelParams_eq, hT.1, hT.2]
    exact ⟨rfl, rfl⟩

/-- **The recursor record's pins** (`checkNativeRec_pins` over a package): at a
large eliminator the elimination parameter is the recursor's, and the family's
level parameters are the recursor's. -/
theorem NativeRecRunJ.pins {J : Judgements md} {env : Env md} {p : NativeParts md}
    {cvTa cvRa : ConstantVal md} {ctorsA : List (ConstantVal md × Nat)}
    {rhss : List (Expr md)} (h : NativeRecRunJ J env p cvTa ctorsA cvRa rhss) :
    (p.large = true → p.elim ∈ p.cvR.levelParams) ∧
    (∀ q ∈ p.cvT.levelParams, q ∈ p.cvR.levelParams) := by
  obtain ⟨hlp, -⟩ := h
  unfold Ix.Kernel.nativeRecLpsOk at hlp
  refine ⟨?_, ?_⟩
  · intro hL
    rw [if_pos hL] at hlp
    simp only [beq_iff_eq] at hlp
    rw [hlp]
    exact List.mem_cons_self
  · intro q hq
    by_cases hL : p.large = true
    · rw [if_pos hL] at hlp
      simp only [beq_iff_eq] at hlp
      rw [hlp]
      exact List.mem_cons_of_mem _ hq
    · rw [if_neg hL] at hlp
      simp only [beq_iff_eq] at hlp
      rw [hlp]
      exact hq

/-- The stored recursor keeps the declared name and level parameters; the name is
fresh where it is checked and passes the front door's shape test. -/
theorem NativeRecRunJ.recursor {J : Judgements md} {env : Env md} {p : NativeParts md}
    {cvTa cvRa : ConstantVal md} {ctorsA : List (ConstantVal md × Nat)}
    {rhss : List (Expr md)} (h : NativeRecRunJ J env p cvTa ctorsA cvRa rhss) :
    cvRa.name = p.cvR.name ∧ cvRa.levelParams = p.cvR.levelParams ∧
      env.find? p.cvR.name = none ∧ p.cvR.name.isProjFnShape = false := by
  obtain ⟨-, -, cvRi, recTy, sty, u, hcv, -, -, -, -, -, -, -, -, -, hstR⟩ := h
  obtain rfl : cvRa = ⟨p.cvR.name, p.cvR.levelParams, recTy⟩ := hstR
  exact ⟨rfl, rfl, hcv.fresh, hcv.shape⟩

/-- **The recursor stage's facts** (`checkNativeRec_facts` over a package): the
stored recursor's name and level parameters, its type's scoping, and the rules'
count and scoping at the environment holding the recursor. -/
theorem NativeRecRunJ.facts {J : Judgements md} {env : Env md} {p : NativeParts md}
    {cvTa cvRa : ConstantVal md} {ctorsA : List (ConstantVal md × Nat)} {rhss : List (Expr md)}
    (h : NativeRecRunJ J env p cvTa ctorsA cvRa rhss) :
    cvRa.name = p.cvR.name ∧ cvRa.levelParams = p.cvR.levelParams ∧
    (cvRa.type.hasFvar = false ∧
      cvRa.type.allLevelParamsDefined cvRa.levelParams = true ∧
      cvRa.type.constsResolve env = true ∧
      cvRa.type.looseBVarsBounded 0 = true) ∧
    rhss.length = (Ix.Kernel.nativeCtors4 ctorsA p.kinds).length ∧
    ∀ rhs ∈ rhss, rhs.hasFvar = false ∧
      rhs.allLevelParamsDefined cvRa.levelParams = true ∧
      rhs.constsResolve ⟨.recInfo cvRa p.majorIdx p.rulePrefix [] :: env.consts⟩ = true ∧
      rhs.looseBVarsBounded 0 = true := by
  obtain ⟨-, -, cvRi, recTy, sty, u, -, -, hlp, hres, hbv, hfv, -, -, -, hrules, hstR⟩ := h
  obtain rfl : cvRa = ⟨p.cvR.name, p.cvR.levelParams, recTy⟩ := hstR
  obtain ⟨hlen, hall⟩ := Ix.Kernel.checkNativeRules_inv hrules
  refine ⟨rfl, rfl, ⟨hfv, hlp, hres, hbv⟩, hlen, ?_⟩
  intro rhs hrhs
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hrhs
  have hi' : i < (Ix.Kernel.nativeCtors4 ctorsA p.kinds).length := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    omega
  obtain ⟨rhs', hget, -, hlp', hres', hbv', hfv'⟩ := hall i hi'
  obtain rfl := Option.some.inj (hi.symm.trans hget)
  exact ⟨hfv', hlp', hres', hbv'⟩

/-- **The recursor's cons keeps the environment well-formed** (`direct_fix_rec_wf`
over a package). -/
theorem NativeRecRunJ.recWF {J : Judgements md} {env : Env md} (henv : Ix.Kernel.EnvWF env)
    {p : NativeParts md} {cvTa cvRa : ConstantVal md} {ctorsA : List (ConstantVal md × Nat)}
    {rhss : List (Expr md)} (h : NativeRecRunJ J env p cvTa ctorsA cvRa rhss) :
    Ix.Kernel.EnvWF ⟨.recInfo cvRa p.majorIdx p.rulePrefix
      (sumRules env.find? cvRa.name p.nP p.majorIdx p.rulePrefix cvRa.type ctorsA rhss)
        :: env.consts⟩ := by
  obtain ⟨-, -, ⟨htf, htp, htr, htb⟩, -, hall⟩ := h.facts
  refine Ix.Kernel.EnvWF.cons henv (Ix.Kernel.structConstWF htf htp
    (Ix.Kernel.Expr.constsResolve_mono htr) htb
    (fun _ _ _ heq => nomatch heq) ?_)
  intro cvR' mI' rP' rules' heq r hr
  injection heq with e1 e2 e3 e4
  subst e1
  subst e4
  obtain ⟨hmem, hfire⟩ := Ix.Kernel.sumRules_mem hr
  obtain ⟨hrfv, hrlp, hrres, hrbv⟩ := hall r.rhs hmem
  refine ⟨hrfv, hrlp, Ix.Kernel.Expr.constsResolve_of_find
    (Ix.Kernel.find?_isSome_cons_same (c := .recInfo cvRa p.majorIdx p.rulePrefix [])
      (c' := .recInfo cvRa p.majorIdx p.rulePrefix
        (sumRules env.find? cvRa.name p.nP p.majorIdx p.rulePrefix cvRa.type ctorsA rhss)) rfl)
      hrres, hrbv, ?_⟩
  intro lvls pins hf
  exact absurd hf (hfire lvls pins)


theorem forall₂_length {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : Forall₂ R l₁ l₂) : l₁.length = l₂.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : Forall₂ R l₁ l₂) : ∀ b ∈ l₂, ∃ a ∈ l₁, R a b := by
  induction h with
  | nil => intro b hb; exact nomatch hb
  | @cons a b' _ _ hab _ ih =>
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, List.mem_cons_self, hab⟩
    · obtain ⟨a', ha', h'⟩ := ih b hb
      exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩

/-- The block's recursor record's pins (`NativeRecRunJ.pins`, at the stage it holds). -/
theorem NativeRecJ.pins {J : Judgements md} {env : Env md} {p : NativeParts md}
    {cvTa cvRa : ConstantVal md} {ctorsA : List (ConstantVal md × Nat)}
    {rhss : List (Expr md)} (h : NativeRecJ J env p cvTa ctorsA cvRa rhss) :
    (p.large = true → p.elim ∈ p.cvR.levelParams) ∧
    (∀ q ∈ p.cvT.levelParams, q ∈ p.cvR.levelParams) :=
  let ⟨_, _, hR, _⟩ := h; hR.pins

/-- The stored recursor keeps the declared name and level parameters; the name is fresh where
it is checked and passes the front door's shape test (`NativeRecRunJ.recursor`). -/
theorem NativeRecJ.recursor {J : Judgements md} {env : Env md} {p : NativeParts md}
    {cvTa cvRa : ConstantVal md} {ctorsA : List (ConstantVal md × Nat)}
    {rhss : List (Expr md)} (h : NativeRecJ J env p cvTa ctorsA cvRa rhss) :
    cvRa.name = p.cvR.name ∧ cvRa.levelParams = p.cvR.levelParams ∧
      env.find? p.cvR.name = none ∧ p.cvR.name.isProjFnShape = false := by
  obtain ⟨cvRg, rhsG, hR, hst⟩ := h
  obtain ⟨hn, hl, hf, hs⟩ := hR.recursor
  rcases hst with ⟨rfl, -⟩ | ⟨cvRi, -, rfl, -⟩
  · exact ⟨hn, hl, hf, hs⟩
  · exact ⟨rfl, rfl, hf, hs⟩

/-- **The stored recursor's facts** (`NativeRecRunJ.facts`): at the declared recursor, its
type's scoping is the declared one's (through the package's annotation frames, `hsyn`), and each
stored rule's scoping is its generated rule's, which `WrapRel` keeps at a rule without `let`. -/
theorem NativeRecJ.facts {J : Judgements md} {env : Env md} {p : NativeParts md}
    {cvTa cvRa : ConstantVal md} {ctorsA : List (ConstantVal md × Nat)} {rhss : List (Expr md)}
    (hsyn : ∀ {e e' : Expr md}, J.annot env 0 e e' → e.hasFvar = false →
      e.looseBVarsBounded 0 = true → e'.hasFvar = false ∧ e'.looseBVarsBounded 0 = true)
    (h : NativeRecJ J env p cvTa ctorsA cvRa rhss) :
    cvRa.name = p.cvR.name ∧ cvRa.levelParams = p.cvR.levelParams ∧
    (cvRa.type.hasFvar = false ∧
      cvRa.type.allLevelParamsDefined cvRa.levelParams = true ∧
      cvRa.type.constsResolve env = true ∧
      cvRa.type.looseBVarsBounded 0 = true) ∧
    rhss.length = (Ix.Kernel.nativeCtors4 ctorsA p.kinds).length ∧
    ∀ rhs ∈ rhss, rhs.hasFvar = false ∧
      rhs.allLevelParamsDefined cvRa.levelParams = true ∧
      rhs.constsResolve ⟨.recInfo cvRa p.majorIdx p.rulePrefix [] :: env.consts⟩ = true ∧
      rhs.looseBVarsBounded 0 = true := by
  obtain ⟨cvRg, rhsG, hR, hst⟩ := h
  have hF := hR.facts
  rcases hst with ⟨rfl, rfl⟩ | ⟨cvRi, hccv, rfl, -, hWr, hlf, -, -⟩
  · exact hF
  · obtain ⟨hnR, hlR, -, hlen, hall⟩ := hF
    obtain ⟨type', ⟨-, -, -, -, hlbt, hitf, hann, htp, htr, -⟩, rfl⟩ := hccv
    obtain ⟨htf, hbt⟩ := hsyn hann hitf hlbt
    refine ⟨rfl, rfl, ⟨htf, htp, htr, hbt⟩, by rw [← forall₂_length hWr]; exact hlen,
      fun rhs hrhs => ?_⟩
    obtain ⟨g, hg, hW⟩ := forall₂_mem_right hWr rhs hrhs
    obtain ⟨hgf, hglp, hgres, hgbv⟩ := hall g hg
    have hT := hW.toWrapT (hlf rhs hrhs)
    refine ⟨hT.hasFvar hgf, ?_, ?_, hT.looseBVarsBounded 0 hgbv⟩
    · have h1 := hT.allLevelParamsDefined _ hgf hglp
      rw [hlR] at h1
      exact h1
    · exact Ix.Kernel.Expr.constsResolve_of_find
        (Ix.Kernel.find?_isSome_cons_same (c := .recInfo cvRg p.majorIdx p.rulePrefix [])
          (c' := .recInfo ⟨p.cvR.name, p.cvR.levelParams, type'⟩ p.majorIdx p.rulePrefix [])
          hnR)
        (hT.constsResolve _ hgf hgres)

/-- **The stored recursor's cons keeps the environment well-formed** (`NativeRecRunJ.recWF`). -/
theorem NativeRecJ.recWF {J : Judgements md} {env : Env md} (henv : Ix.Kernel.EnvWF env)
    (hsyn : ∀ {e e' : Expr md}, J.annot env 0 e e' → e.hasFvar = false →
      e.looseBVarsBounded 0 = true → e'.hasFvar = false ∧ e'.looseBVarsBounded 0 = true)
    {p : NativeParts md} {cvTa cvRa : ConstantVal md} {ctorsA : List (ConstantVal md × Nat)}
    {rhss : List (Expr md)} (h : NativeRecJ J env p cvTa ctorsA cvRa rhss) :
    Ix.Kernel.EnvWF ⟨.recInfo cvRa p.majorIdx p.rulePrefix
      (sumRules env.find? cvRa.name p.nP p.majorIdx p.rulePrefix cvRa.type ctorsA rhss)
        :: env.consts⟩ := by
  obtain ⟨-, -, ⟨htf, htp, htr, htb⟩, -, hall⟩ := NativeRecJ.facts hsyn h
  refine Ix.Kernel.EnvWF.cons henv (Ix.Kernel.structConstWF htf htp
    (Ix.Kernel.Expr.constsResolve_mono htr) htb
    (fun _ _ _ heq => nomatch heq) ?_)
  intro cvR' mI' rP' rules' heq r hr
  injection heq with e1 e2 e3 e4
  subst e1
  subst e4
  obtain ⟨hmem, hfire⟩ := Ix.Kernel.sumRules_mem hr
  obtain ⟨hrfv, hrlp, hrres, hrbv⟩ := hall r.rhs hmem
  refine ⟨hrfv, hrlp, Ix.Kernel.Expr.constsResolve_of_find
    (Ix.Kernel.find?_isSome_cons_same (c := .recInfo cvRa p.majorIdx p.rulePrefix [])
      (c' := .recInfo cvRa p.majorIdx p.rulePrefix
        (sumRules env.find? cvRa.name p.nP p.majorIdx p.rulePrefix cvRa.type ctorsA rhss)) rfl)
      hrres, hrbv, ?_⟩
  intro lvls pins hf
  exact absurd hf (hfire lvls pins)

/-- **The stored recursor's major premise**: past the parameters, the motive, the minor
premises and the indices, the domain is the family at its level parameters applied to the
parameter and index variables, at the generated type (`structRecTyR_major`) and at a declared
one, which carries the generated domain verbatim (`WrapRel.major_structFamI`: the declared type
has no `let`, and the family is stored as an inductive type where the recursor is checked). -/
theorem NativeRecJ.major {J : Judgements md} {env : Env md} {p : NativeParts md}
    {cvTa cvRa : ConstantVal md} {ctorsA : List (ConstantVal md × Nat)} {rhss : List (Expr md)}
    (h : NativeRecJ J env p cvTa ctorsA cvRa rhss)
    (hT : ∃ cv caps, env.find? p.cvT.name = some (.indInfo cv caps))
    (hlen : (Ix.Kernel.nativeCtors4 ctorsA p.kinds).length = p.ctors.length) :
    ∃ bs B m, cvRa.type.stripPis p.majorIdx = some (bs,
      .forallE (Ix.Kernel.structFamI p.cvT.name p.cvT.levelParams p.nP p.nIdx
        (p.ctors.length + 1) 0) B m) := by
  obtain ⟨cvRg, rhsG, hR, hst⟩ := h
  obtain ⟨-, -, cvRi, recTy, sty, u, -, hty, -, -, -, -, -, -, -, -, rfl⟩ := hR
  obtain ⟨bs, B, m, hg⟩ := structRecTyR_major hty
  rw [hlen] at hg
  rcases hst with ⟨rfl, -⟩ | ⟨cvRi', -, rfl, hW, -, -, -, hlf⟩
  · exact ⟨bs, B, m, hg⟩
  · exact WrapRel.major_structFamI hW hlf hT hg

/-- The kinds the block re-checks are one list per constructor. -/
theorem nativeFieldsOk_length {env₀ : Env md} {T : Key md} {lps : List LevelParam}
    {nP nIdx : Nat} {ctorsA : List (ConstantVal md × Nat)} {kinds : List (List RecFieldKind)}
    (h : Ix.Kernel.nativeFieldsOk env₀ T lps nP nIdx ctorsA kinds = true) :
    ctorsA.length = kinds.length := by
  simp only [Ix.Kernel.nativeFieldsOk, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

/-- `NativeRecJ.major` at the block's counts: one kind list and one declared constructor per
stored constructor. -/
theorem NativeRecJ.majorOf {J : Judgements md} {env : Env md} {p : NativeParts md}
    {cvTa cvRa : ConstantVal md} {ctorsA : List (ConstantVal md × Nat)} {rhss : List (Expr md)}
    (h : NativeRecJ J env p cvTa ctorsA cvRa rhss)
    (hT : ∃ cv caps, env.find? p.cvT.name = some (.indInfo cv caps))
    (hk : ctorsA.length = p.kinds.length) (hlenA : ctorsA.length = p.ctors.length) :
    ∃ bs B m, cvRa.type.stripPis p.majorIdx = some (bs,
      .forallE (Ix.Kernel.structFamI p.cvT.name p.cvT.levelParams p.nP p.nIdx
        (p.ctors.length + 1) 0) B m) :=
  h.major hT (by rw [Ix.Kernel.nativeCtors4_length hk, hlenA])

/-- **Every stored rule fires**: the stored type's major premise is the family at the
constructors' level parameters, applied first to the parameters (`Expr.recRulePlain`, the
kernel's test after the recursor's stage). -/
theorem NativeRecJ.plain {J : Judgements md} {env : Env md} {p : NativeParts md}
    {cvTa cvRa : ConstantVal md} {ctorsA : List (ConstantVal md × Nat)} {rhss : List (Expr md)}
    (h : NativeRecJ J env p cvTa ctorsA cvRa rhss)
    (hT : ∃ cv caps, env.find? p.cvT.name = some (.indInfo cv caps))
    (hk : ctorsA.length = p.kinds.length) (hlenA : ctorsA.length = p.ctors.length)
    (hlps : ∀ c ∈ ctorsA, c.1.levelParams = p.cvT.levelParams) :
    ctorsA.all (fun c => Expr.recRulePlain cvRa.type p.majorIdx p.rulePrefix p.nP
      c.1.levelParams) = true := by
  obtain ⟨bs, B, m, hs⟩ := h.majorOf hT hk hlenA
  refine List.all_eq_true.mpr fun c hc => ?_
  rw [hlps c hc]
  exact recRulePlain_of_major (nP := p.nP) (n := p.ctors.length) (nIdx := p.nIdx) hs

/-! ## The kernel's records are the run instance -/

section RunInstance

variable {μ : CheckMode} {F : Nat}

private theorem throw_ne_ok {α : Type} {e : Ix.Kernel.CheckError md} {a : α}
    (h : (throw e : Ix.Kernel.CheckM md α) = .ok a) : False := by
  simp [throw, throwThe, MonadExceptOf.throw] at h

local syntax "close_throw" : tactic
local macro_rules
  | `(tactic| close_throw) =>
    `(tactic| first
        | (exfalso; exact throw_ne_ok (by assumption))
        | (exfalso; exact throw_ne_ok
            (by simpa [bind, Except.bind] using ‹_›)))

theorem constantValCheckJ_of_run {env : Env md} {cv cv' : ConstantVal md}
    (h : Ix.Kernel.checkConstantVal (fueledOps μ F) env cv = .ok cv') :
    ConstantValCheckJ (runJ μ F) env cv cv' := by
  obtain ⟨hfind, hres, hpsh, hnd, hlbt, hitf, type, stype, u, hann, htp,
    htr, hst, hsort, rfl⟩ := Ix.Kernel.checkConstantVal_inv h
  exact ⟨type, ⟨Option.isNone_iff_eq_none.mpr hfind, hres, hpsh, hnd, hlbt, hitf,
    hann, htp, htr, ⟨stype, u, hst, hsort⟩⟩, rfl⟩

theorem sumIndRunJ_of_run {env envI : Env md} {p p' : InductiveShape md}
    {cvTa : ConstantVal md} {capsOf : InductiveShape md → IndCaps md}
    (h : checkSumInd (fueledOps μ F) env p capsOf = .ok (envI, cvTa, p')) :
    SumIndRunJ (runJ μ F) env p capsOf envI cvTa p' := by
  unfold Ix.Kernel.checkSumInd at h
  obtain ⟨cvTa₀, hccv₀, h⟩ := Ix.Kernel.exceptBind_ok h
  obtain ⟨q, htele, h⟩ := Ix.Kernel.exceptBind_ok h
  obtain ⟨cvTa', s⟩ := q
  try simp only at h
  obtain ⟨q, hq, h⟩ := Ix.Kernel.exceptBind_ok h
  obtain ⟨bs, tbody⟩ := q
  have hq' := Ix.Kernel.unwrapOr_ok hq
  try simp only at h
  by_cases hc : (tbody == Expr.sort s) = true
  · rw [if_pos hc] at h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hstrip : cvTa'.type.stripPis (p.nP + p.nIdx) = some (bs, .sort s) := by
      rw [hq', beq_iff_eq.mp hc]
    refine ⟨cvTa₀, s, bs, cvTa', constantValCheckJ_of_run hccv₀, ?_, hstrip, Or.inl rfl, rfl, rfl⟩
    rcases Ix.Kernel.checkSumTele_shape htele with ⟨rfl, -⟩ | ⟨ty, hccv⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨ty, constantValCheckJ_of_run hccv⟩
  · rw [if_neg hc] at h
    close_throw

theorem fieldSortsJ_of_run {env : Env md} {isProp large : Bool} {s : Level} {nP : Nat}
    {fvs idxArgs : List (Expr md)} {n : Nat} {sorts : List Level}
    (h : Ix.Kernel.checkStructFieldSortsI (fueledOps μ F) env isProp large s nP fvs idxArgs n
      = .ok sorts) :
    FieldSortsJ (runJ μ F) env isProp large s nP fvs idxArgs n sorts := by
  obtain ⟨hlen, hall⟩ := Ix.Kernel.checkStructFieldSortsI_inv h
  refine ⟨hlen, fun i hi => ?_⟩
  obtain ⟨fv, ty, u, hfv, hu, hty, hen, hleq, hz⟩ := hall i hi
  refine ⟨fv, ty, u, hfv, hu, hty, hen, fun hp => Level.leq_sound (hleq hp),
    fun hp hl => ?_⟩
  rcases hz hp hl with h0 | hc
  · refine Or.inl fun φ => ?_
    have := Level.isEquiv_sound (beq_iff_eq.mp h0) φ
    simpa [Level.eval] using this
  · exact Or.inr hc

theorem structDomsJ_of_run {env : Env md} {off : Nat} {fvs doms : List (Expr md)} {n : Nat}
    (h : Ix.Kernel.checkStructDomsAt (fueledOps μ F) env off fvs doms n = .ok ()) :
    StructDomsJ (runJ μ F) env off fvs doms n :=
  Ix.Kernel.checkStructDomsAt_inv h

theorem sumCtorRunJ_of_run {env₀ env : Env md} {T : Key md} {lps : List LevelParam}
    {nP nIdx : Nat} {resSort : Level} {isProp large : Bool} {cvC cvTa cvCa : ConstantVal md}
    {nF : Nat} {sorts : List Level}
    (h : checkSumCtor (fueledOps μ F) env₀ env T lps nP nIdx resSort isProp large
      cvC nF cvTa = .ok (cvCa, sorts)) :
    SumCtorRunJ (runJ μ F) env₀ env T lps nP nIdx resSort isProp large cvC nF cvTa cvCa
      sorts := by
  obtain ⟨-, hres, fvsP, crest, tfvs, trest, xFvs, idxArgs, h1, h2, hdoms, h3, h4, h5, h6,
    hsorts⟩ := Ix.Kernel.checkSumCtor_shape h
  refine ⟨?_, hres, fvsP, crest, tfvs, trest, xFvs, idxArgs, h1, h2,
    structDomsJ_of_run hdoms, h3, h4, h5, h6, fieldSortsJ_of_run hsorts⟩
  -- the stage stores the normalised constant: the declared one checked, or the
  -- rebuilt one checked from scratch
  unfold Ix.Kernel.checkSumCtor at h
  obtain ⟨cvCa₀, hccv₀, h⟩ := Ix.Kernel.exceptBind_ok h
  obtain ⟨cvCa', hnorm, h⟩ := Ix.Kernel.exceptBind_ok h
  suffices hout : cvCa' = cvCa by
    subst hout
    refine ⟨cvCa₀, constantValCheckJ_of_run hccv₀, ?_⟩
    unfold Ix.Kernel.normCtorVal at hnorm
    obtain ⟨q, -, hnorm⟩ := Ix.Kernel.exceptBind_ok hnorm
    obtain ⟨cbs, _⟩ := q
    try simp only at hnorm
    obtain ⟨r, -, hnorm⟩ := Ix.Kernel.exceptBind_ok hnorm
    obtain ⟨fvsP', crest'⟩ := r
    try simp only at hnorm
    obtain ⟨u, -, hnorm⟩ := Ix.Kernel.exceptBind_ok hnorm
    obtain ⟨fbs, resid⟩ := u
    try simp only at hnorm
    split at hnorm
    · simp only [pure, Except.pure, Except.ok.injEq] at hnorm
      exact Or.inl hnorm.symm
    · exact Or.inr ⟨_, constantValCheckJ_of_run hnorm⟩
  -- the rest of the stage returns the normalised constant unchanged
  obtain ⟨q, -, h⟩ := Ix.Kernel.exceptBind_ok h
  obtain ⟨cbs, cbody⟩ := q
  try simp only at h
  by_cases hc : Ix.Kernel.structCtorResidOk T lps nP nF nIdx cbody = true
  case neg => rw [if_neg hc] at h; close_throw
  rw [if_pos hc] at h
  obtain ⟨cq, -, h⟩ := Ix.Kernel.exceptBind_ok h
  obtain ⟨fvsP', crest'⟩ := cq
  obtain ⟨tq, -, h⟩ := Ix.Kernel.exceptBind_ok h
  obtain ⟨tfvs', trest'⟩ := tq
  try simp only at h
  obtain ⟨u, -, h⟩ := Ix.Kernel.exceptBind_ok h
  obtain ⟨xq, -, h⟩ := Ix.Kernel.exceptBind_ok h
  obtain ⟨xFvs', xrest⟩ := xq
  try simp only at h
  by_cases g2 : (xrest.getAppFn == Expr.const T (lps.map .param) &&
      xrest.getAppArgs.take nP == fvsP' && xrest.getAppArgs.length == nP + nIdx) = true
  case neg => rw [if_neg g2] at h; close_throw
  rw [if_pos g2] at h
  by_cases g3 : (xFvs'.all fun x => Expr.constsResolve env₀ x.fvarTypeD) = true
  case neg => rw [if_neg g3] at h; close_throw
  rw [if_pos g3] at h
  by_cases g4 : ((xrest.getAppArgs.drop nP).all fun e => Expr.constsResolve env₀ e) = true
  case neg => rw [if_neg g4] at h; close_throw
  rw [if_pos g4] at h
  obtain ⟨sorts', -, h⟩ := Ix.Kernel.exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  exact h.1

theorem sumCtorsRunJ_of_run {env₀ env : Env md} {T : Key md} {lps : List LevelParam}
    {nP nIdx : Nat} {resSort : Level} {isProp large : Bool} {cvTa : ConstantVal md}
    {cs ctorsA : List (ConstantVal md × Nat)} {sortss : List (List Level)}
    (h : checkSumCtors (fueledOps μ F) env₀ env T lps nP nIdx resSort isProp large
      cvTa cs = .ok (ctorsA, sortss)) :
    SumCtorsRunJ (runJ μ F) env₀ env T lps nP nIdx resSort isProp large cvTa cs ctorsA
      sortss := by
  obtain ⟨hlen, hlenS, hall⟩ := Ix.Kernel.checkSumCtors_inv h
  refine ⟨hlen, hlenS, fun j c cA hc hcA => ?_⟩
  obtain ⟨hnF, sorts, hs, hrun⟩ := hall j c cA hc hcA
  exact ⟨hnF, sorts, hs, sumCtorRunJ_of_run hrun⟩

theorem nativeRecRunJ_of_run {env : Env md} {p : NativeParts md} {cvTa cvRa : ConstantVal md}
    {ctorsA : List (ConstantVal md × Nat)} {rhss : List (Expr md)}
    (h : checkNativeRec (fueledOps μ F) env p cvTa ctorsA = .ok (cvRa, rhss)) :
    NativeRecRunJ (runJ μ F) env p cvTa ctorsA cvRa rhss := by
  obtain ⟨cvRi, recTy, sty, u, hcv, hrt, h1, h2, h3, h4, hsty, hu, hb, hrules, hR⟩ :=
    Ix.Kernel.checkNativeRec_shape h
  refine ⟨?_, ?_, cvRi, recTy, sty, u, constantValCheckJ_of_run hcv, hrt, h1, h2, h3, h4,
    hsty, hu, hb, hrules, hR⟩
  · unfold Ix.Kernel.checkNativeRec at h
    by_cases hlp : Ix.Kernel.nativeRecLpsOk p.toInductiveShape = true
    · exact hlp
    · rw [if_neg hlp] at h
      close_throw
  · unfold Ix.Kernel.checkNativeRec at h
    by_cases hlp : Ix.Kernel.nativeRecLpsOk p.toInductiveShape = true
    · rw [if_pos hlp] at h
      try simp only [bind, Except.bind] at h
      by_cases hpin : p.recPinned = true
      · exact hpin
      · rw [if_neg hpin] at h
        close_throw
    · rw [if_neg hlp] at h
      close_throw

/-- **The kernel's native record is the restated one at its runs.** -/
theorem declNativeRun_runJ {env env₂ : Env md} {p₀ : NativeParts md}
    (h : DeclNativeRun μ F env p₀ env₂) : DeclNativeRunJ (runJ μ F) env p₀ env₂ := by
  obtain ⟨hnd, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, cvRa, rhss, tfvs, trest,
    isorts, hInd, hp, hCtors, hK, hcaps, hwl, hopT, hsorts, hFOk, hROk, hRec, -, hTbl⟩ := h
  -- the kernel stores the telescope constant
  have hFR : FormerReadJ env₁ p cvTa ctorsA := by
    obtain ⟨cvT, s, -, -, -, hp₁, henv₁, -⟩ := Ix.Kernel.checkSumInd_shape hInd
    have hcvTn : cvTa.name = p.cvT.name := by
      subst hp hp₁
      exact (sumIndRunJ_of_run hInd).former.1
    refine Or.inl ?_
    rw [henv₁, ← hcvTn]
    exact ⟨_, Ix.Kernel.Env.find?_cons_self _ _⟩
  exact ⟨hnd, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, cvRa, rhss, tfvs, trest, isorts,
    sumIndRunJ_of_run hInd, hp, sumCtorsRunJ_of_run hCtors, hK, hcaps,
    fun hl => (hwl hl).imp_left fun hnz φ => Ix.Kernel.Level.isNeverZero_sound φ _ hnz,
    hopT, fieldSortsJ_of_run hsorts, hFOk, hROk,
    ⟨cvRa, rhss, nativeRecRunJ_of_run hRec, Or.inl ⟨rfl, rfl⟩⟩, hTbl, hFR⟩

end RunInstance

end Ix.Kernel.Semantics
