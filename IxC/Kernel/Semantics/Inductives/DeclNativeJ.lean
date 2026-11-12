module

public import IxC.Kernel.Semantics.Inductives.DeclNative
public import IxC.Kernel.Semantics.DeclIndJ
public import IxC.Kernel.Verify.Inductives.SumInv
public import IxC.Kernel.Verify.Inductives.FixInv
public import IxC.Kernel.Verify.Inductives.SumRec
import IxC.Kernel.Verify.Extend.Inversions
import IxC.Kernel.Verify.Level

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
record gives it at its runs (`declNativeRun_runJ`). `IndRoutesJ` is the inductive
kind's two routes, native at the recognised parts or modeled (`DeclIndRunJ`).
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
itself, as the kernel stores it. One definition, so that which constant is stored
is decided in one place. -/
def FormerStoredJ (_J : Judgements md) (_env : Env md) (_cvTa₀ cvTa cvS : ConstantVal md) :
    Prop :=
  cvS = cvTa

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
    FormerStoredJ J env cvTa₀ cvTa cvS ∧
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

/-- **The recursor the block stores**, against the checked declared recursor `cvRi`
and the generated type `recTy`: the recursor at the generated type, as the kernel
stores it. One definition, so that which type is stored is decided in one place. -/
def RecStoredJ (_J : Judgements md) (_env : Env md) (p : NativeParts md) (_cvRi : ConstantVal md)
    (recTy : Expr md) (cvRa : ConstantVal md) : Prop :=
  cvRa = ⟨p.cvR.name, p.cvR.levelParams, recTy⟩

/-- **The recursor's stage** (`checkNativeRec`) over a package: the record's pins
(its level parameters are the generated ones; its rule count, rules' constructors
and field counts and argument sums are the generated ones), the declared recursor
checked, the generated type scoped, typed at a sort and convertible with the
declared one, the generated rules scoped at the environment holding the
recursor; the stored recursor carries the generated type. -/
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
    RecStoredJ J env p cvRi recTy cvRa

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
    NativeRecRunJ J (consSumCtors p.nP ctorsA env₁) p cvTa ctorsA cvRa rhss ∧
    ctorsA.all (fun c => Expr.recRulePlain cvRa.type p.majorIdx p.rulePrefix p.nP
      c.1.levelParams) = true ∧
    -- the projection table at a structure-like block
    checkNativeTable (m := Ix.Kernel.CheckM md) p ctorsA sortss
      ⟨.recInfo cvRa p.majorIdx p.rulePrefix
        (sumRules (consSumCtors p.nP ctorsA env₁).find? cvRa.name p.nP p.majorIdx p.rulePrefix
          cvRa.type ctorsA rhss)
        :: (consSumCtors p.nP ctorsA env₁).consts⟩ = .ok env₂

/-- **An inductive block's two routes over a package**: the native route at the
parts the recogniser reads off the block, or the modeled route (`DeclIndRunJ`,
stated for every block). -/
def IndRoutesJ (J : Judgements md) (env : Env md) (block : List (ConstantInfo md))
    (nP : Nat) (env₂ : Env md) : Prop :=
  (∃ p₀, Ix.Kernel.nativeParts? nP block = some p₀ ∧ DeclNativeRunJ J env p₀ env₂) ∨
  DeclIndRunJ J env block env₂

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

/-- The stored recursor keeps the declared name and level parameters; the name is
fresh where it is checked and passes the front door's shape test. -/
theorem NativeRecRunJ.recursor {J : Judgements md} {env : Env md} {p : NativeParts md}
    {cvTa cvRa : ConstantVal md} {ctorsA : List (ConstantVal md × Nat)}
    {rhss : List (Expr md)} (h : NativeRecRunJ J env p cvTa ctorsA cvRa rhss) :
    cvRa.name = p.cvR.name ∧ cvRa.levelParams = p.cvR.levelParams ∧
      env.find? p.cvR.name = none ∧ p.cvR.name.isProjFnShape = false := by
  obtain ⟨-, -, cvRi, recTy, sty, u, hcv, -, -, -, -, -, -, -, -, -, rfl⟩ := h
  exact ⟨rfl, rfl, hcv.fresh, hcv.shape⟩

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
    refine ⟨cvTa₀, s, bs, cvTa', constantValCheckJ_of_run hccv₀, ?_, hstrip, rfl, rfl, rfl⟩
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
    isorts, hInd, hp, hCtors, hK, hcaps, hwl, hopT, hsorts, hFOk, hROk, hRec, hpl, hTbl⟩ := h
  exact ⟨hnd, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, cvRa, rhss, tfvs, trest, isorts,
    sumIndRunJ_of_run hInd, hp, sumCtorsRunJ_of_run hCtors, hK, hcaps,
    fun hl => (hwl hl).imp_left fun hnz φ => Ix.Kernel.Level.isNeverZero_sound φ _ hnz,
    hopT, fieldSortsJ_of_run hsorts, hFOk, hROk, nativeRecRunJ_of_run hRec, hpl, hTbl⟩

end RunInstance

end Ix.Kernel.Semantics
