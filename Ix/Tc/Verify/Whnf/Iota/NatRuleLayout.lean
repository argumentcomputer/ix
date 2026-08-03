import Ix.Tc.Verify.Whnf.Iota.NatPatternMatching

/-!
# Trusted Nat-rule layout and through-major spine splitting

The linear descriptor checks that the recursor reports at least two minors,
but it never indexes the rule array.  Moreover, constructor indices are local
to an inductive family: an arbitrary constructor at index zero is not thereby
`Nat.zero`.  This slice records the missing Nat-specific catalog fact as an
explicit certificate rather than deriving it from either count alone.

The second half splits a translated production spine at an observed array
hit.  It retains the application through the major and a typed trailing
suffix separately, so later RHS reasoning cannot accidentally discard an
over-application.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

/-! ## Trusted Nat recursor layout -/

/-- Exact trusted catalog data needed to interpret the first two rules of a
`Nat.rec` declaration.  This is the Nat-specific consequence that a complete
inductive-admission proof must construct.  Neither `minors ≥ 2` nor a bare
constructor index can inhabit these fields. -/
structure TrustedNatRecursorLayout (trProj : RawProjRel) (world : VerifyWorld)
    (id : KId .anon) (recursor : KConst .anon) : Prop where
  primitive : PrimitiveIdAgrees world id ``Nat.rec
  catalog : world.catalog id = some recursor
  zero : ∃ rule pattern,
    recursor.RecursorRuleAt 0 rule ∧
      RawRecursorRulePatternRel world.venv world.catalog world.nameOf
        id recursor rule pattern ∧
      pattern.ruleIndex = 0 ∧
      pattern.constructorName = ``Nat.zero ∧
      pattern.constructorParams = 0 ∧
      pattern.constructorFields = 0
  succ : ∃ rule pattern,
    recursor.RecursorRuleAt 1 rule ∧
      RawRecursorRulePatternRel world.venv world.catalog world.nameOf
        id recursor rule pattern ∧
      pattern.ruleIndex = 1 ∧
      pattern.constructorName = ``Nat.succ ∧
      pattern.constructorParams = 0 ∧
      pattern.constructorFields = 1

/-- World-level provider for whichever concrete declaration is bound to the
trusted `Nat.rec` primitive.  Keeping the primitive and catalog equations as
arguments prevents a certificate for an unrelated recursor from being used. -/
def TrustedNatRecursorLayouts (trProj : RawProjRel)
    (world : VerifyWorld) : Prop :=
  ∀ {id recursor},
    PrimitiveIdAgrees world id ``Nat.rec →
    world.catalog id = some recursor →
    TrustedNatRecursorLayout trProj world id recursor

namespace TrustedNatRecursorLayout

/-- Select the exact trusted zero or successor rule for a canonical Nat
literal and recover both its registered equation and NatPatternMatching case shape. -/
theorem caseForMajor
    {trProj : RawProjRel} {world : VerifyWorld}
    {id : KId .anon} {recursor : KConst .anon}
    (layout : TrustedNatRecursorLayout trProj world id recursor)
    (hcatalogRel : TrustedCatalogRel trProj world)
    (major : Nat) :
    ∃ rule pattern,
      recursor.RecursorRuleAt pattern.ruleIndex rule ∧
      RawRecursorRuleRel world.venv world.nameOf trProj
        id recursor rule ∧
      RawRecursorRulePatternRel world.venv world.catalog world.nameOf
        id recursor rule pattern ∧
      NatRecIotaCase pattern major := by
  cases major with
  | zero =>
      obtain ⟨rule, pattern, hrule, hpattern, hindex, hname, hparams,
        hfields⟩ := layout.zero
      refine ⟨rule, pattern, ?_,
        hcatalogRel.recursorRule layout.primitive.1 layout.catalog
          hrule.hasRecursorRule,
        hpattern, ?_⟩
      · simpa only [hindex] using hrule
      · exact Or.inl ⟨rfl, hindex, hname, hparams, hfields⟩
  | succ predecessor =>
      obtain ⟨rule, pattern, hrule, hpattern, hindex, hname, hparams,
        hfields⟩ := layout.succ
      refine ⟨rule, pattern, ?_,
        hcatalogRel.recursorRule layout.primitive.1 layout.catalog
          hrule.hasRecursorRule,
        hpattern, ?_⟩
      · simpa only [hindex] using hrule
      · exact Or.inr
          ⟨predecessor, rfl, hindex, hname, hparams, hfields⟩

end TrustedNatRecursorLayout

/-! ## Typed application suffixes and positional splitting -/

namespace RecM

/-- Typed translation of a left-associated application suffix starting from
an already translated prefix.  The suffix is stored in production order. -/
inductive TrAppSuffix (env : Lean4Lean.VEnv) (uvars : Nat)
    (nameOf : Address → Option Lean.Name) (trProj : RawProjRel)
    (Delta : KVLCtx) (start : VExpr) :
    List (KExpr .anon) → VExpr → Prop
  | nil : TrAppSuffix env uvars nameOf trProj Delta start [] start
  | app {args current arg argV A B} :
      TrAppSuffix env uvars nameOf trProj Delta start args current →
      env.HasType uvars Delta.toCtx current (.forallE A B) →
      env.HasType uvars Delta.toCtx argV A →
      TrKExprS env uvars nameOf trProj Delta arg argV →
      TrAppSuffix env uvars nameOf trProj Delta start (args ++ [arg])
        (.app current argV)

namespace TrAppSuffix

/-- Reattach a certified suffix to a translated concrete prefix. -/
theorem tr
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {Delta : KVLCtx} {start : VExpr}
    {args : List (KExpr .anon)} {resultV : VExpr}
    (h : TrAppSuffix env uvars nameOf trProj Delta start args resultV)
    {startExpr : KExpr .anon}
    (hstart : TrKExprS env uvars nameOf trProj Delta startExpr start) :
    TrKExprS env uvars nameOf trProj Delta
      (args.foldl KExpr.mkApp startExpr) resultV := by
  induction h with
  | nil => exact hstart
  | app hsuffix hfun harg hargTr ih =>
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [KExpr.mkApp_shape]
      exact .app hfun harg ih hargTr

end TrAppSuffix

namespace TrAppSpine

/-- Complete typed decomposition of a translated spine at one observed raw
argument.  `throughTr` ends exactly after applying the major; `suffixTr`
accounts for every later argument. -/
def SplitAt
    (env : Lean4Lean.VEnv) (uvars : Nat)
    (nameOf : Address → Option Lean.Name) (trProj : RawProjRel)
    (Delta : KVLCtx) (head : KExpr .anon)
    (args : List (KExpr .anon)) (majorIdx : Nat)
    (major : KExpr .anon) (resultV : VExpr) : Prop :=
  ∃ (priorArgs laterArgs : List (KExpr .anon)) (priorV majorV : VExpr),
    args = priorArgs ++ major :: laterArgs ∧
    majorIdx = priorArgs.length ∧
    TrAppSpine env uvars nameOf trProj Delta head priorArgs priorV ∧
    TrKExprS env uvars nameOf trProj Delta major majorV ∧
    TrKExprS env uvars nameOf trProj Delta
      (KExpr.mkApp (priorArgs.foldl KExpr.mkApp head) major)
      (.app priorV majorV) ∧
    TrAppSuffix env uvars nameOf trProj Delta
      (.app priorV majorV) laterArgs resultV

/-- Split a typed production-order spine at any successful `getElem?` hit.
The proof follows the snoc structure of `TrAppSpine`, distinguishing a hit in
the prior prefix from the newly appended final argument. -/
theorem splitAt
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {Delta : KVLCtx} {head major : KExpr .anon}
    {args : List (KExpr .anon)} {majorIdx : Nat} {resultV : VExpr}
    (h : TrAppSpine env uvars nameOf trProj Delta head args resultV)
    (hmajor : args[majorIdx]? = some major) :
    SplitAt env uvars nameOf trProj Delta head args majorIdx major
      resultV := by
  induction h generalizing majorIdx major with
  | head hhead =>
      simp at hmajor
  | @app args fV arg argV A B hprefix hfun harg hargTr ih =>
      by_cases hbefore : majorIdx < args.length
      · have hprefixMajor := hmajor
        rw [List.getElem?_append_left hbefore] at hprefixMajor
        obtain ⟨priorArgs, laterArgs, priorV, majorV, hargs, hindex,
          hpriorTr, hmajorTr, hthroughTr, hlaterTr⟩ := ih hprefixMajor
        refine ⟨priorArgs, laterArgs ++ [arg], priorV, majorV, ?_, hindex,
          hpriorTr, hmajorTr, hthroughTr,
          TrAppSuffix.app hlaterTr hfun harg hargTr⟩
        calc
          args ++ [arg] =
              (priorArgs ++ major :: laterArgs) ++ [arg] :=
            congrArg (· ++ [arg]) hargs
          _ = priorArgs ++ major :: (laterArgs ++ [arg]) := by
            simp only [List.append_assoc, List.cons_append]
      · have hbound : majorIdx < (args ++ [arg]).length :=
          (List.getElem?_eq_some_iff.mp hmajor).choose
        have hindex : majorIdx = args.length := by
          simp only [List.length_append, List.length_singleton] at hbound
          omega
        subst majorIdx
        rw [List.getElem?_concat_length] at hmajor
        have hargMajor : arg = major := Option.some.inj hmajor
        subst major
        refine ⟨args, [], fV, argV, by simp, rfl, hprefix, hargTr, ?_, .nil⟩
        rw [KExpr.mkApp_shape]
        exact .app hfun harg hprefix.tr hargTr

end TrAppSpine

/-! ## Descriptor-indexed translated Nat splits -/

/-- Exact translated decomposition induced by the literal position recorded
in a successful Nat-recognizer descriptor. -/
def NatRecLiteralTranslationSplit
    (env : Lean4Lean.VEnv) (uvars : Nat)
    (nameOf : Address → Option Lean.Name) (trProj : RawProjRel)
    (Delta : KVLCtx) (id : KId .anon)
    (source : KExpr .anon) (parts : NatRecLiteralParts .anon)
    (majorIdx : Nat) (sourceV : VExpr)
    (priorArgs laterArgs : List (KExpr .anon)) (priorV : VExpr) : Prop :=
  ∃ (us : Array (KUniv .anon)) (headInfo : ExprInfo .anon)
      (blob : Address) (majorInfo : ExprInfo .anon),
    source.collectSpine = (.const id us headInfo, parts.spine) ∧
    parts.spine.toList =
      priorArgs ++ (.nat parts.major blob majorInfo) :: laterArgs ∧
    majorIdx = priorArgs.length ∧
    TrAppSpine env uvars nameOf trProj Delta
      (.const id us headInfo) priorArgs priorV ∧
    TrKExprS env uvars nameOf trProj Delta
      (KExpr.mkApp (priorArgs.foldl KExpr.mkApp (.const id us headInfo))
        (.nat parts.major blob majorInfo))
      (.app priorV (.natLit parts.major)) ∧
    TrAppSuffix env uvars nameOf trProj Delta
      (.app priorV (.natLit parts.major)) laterArgs sourceV

namespace NatRecLiteralPartsDescriptor

/-- Any trusted rule pattern for this descriptor uses the same major position
as the literal array hit.  This is NatRecognizer's arithmetic-coherence argument,
stated for an already selected pattern so no second oracle choice is made. -/
theorem patternMajor
    {world : VerifyWorld}
    {id : KId .anon} {recursor : KConst .anon}
    {source : KExpr .anon} {parts : NatRecLiteralParts .anon}
    (hdescriptor : NatRecLiteralPartsDescriptor id recursor source parts)
    {rule : RecRule .anon} {pattern : RecursorRulePattern}
    (hpattern : RawRecursorRulePatternRel world.venv world.catalog
      world.nameOf id recursor rule pattern) :
    ∃ blob majorInfo,
      source.collectSpine.2[pattern.majorIdx]? =
        some (.nat parts.major blob majorInfo) := by
  rcases hdescriptor with
    ⟨us, headInfo, spine, name, levelParams, k, isUnsafe, lvls, params,
      indices, motives, minors, block, memberIdx, ty, rules, leanAll, major,
      blob, majorInfo, hcollect, hrecursor, hminors, hmajor, hparts⟩
  have hpatternMajor := hpattern.2.1
  have hcoherent := hpattern.2.2.1
  rw [hrecursor] at hpatternMajor hcoherent
  simp only [KConst.RecursorMajorIdx, KConst.RecursorMajorIdxCoherent,
    Option.some.injEq] at hpatternMajor hcoherent
  have hmajorIdx : pattern.majorIdx =
      params.toNat + motives.toNat + minors.toNat + indices.toNat :=
    hpatternMajor.symm.trans hcoherent
  have hsourceSpine := congrArg Prod.snd hcollect
  subst parts
  refine ⟨blob, majorInfo, ?_⟩
  rw [hsourceSpine, hmajorIdx]
  exact hmajor

/-- Split the actual translated source at a descriptor-aligned literal hit.
The major translation becomes the canonical Theory numeral by inversion of
the owned literal translation rule. -/
theorem translatedSplit
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {Delta : KVLCtx} {id : KId .anon} {recursor : KConst .anon}
    {source : KExpr .anon} {parts : NatRecLiteralParts .anon}
    (hdescriptor : NatRecLiteralPartsDescriptor id recursor source parts)
    {majorIdx : Nat} {blob : Address} {majorInfo : ExprInfo .anon}
    {sourceV : VExpr}
    (hsource : TrKExprS env uvars nameOf trProj Delta source sourceV)
    (hmajor : source.collectSpine.2[majorIdx]? =
      some (.nat parts.major blob majorInfo)) :
    ∃ priorArgs laterArgs priorV,
      NatRecLiteralTranslationSplit env uvars nameOf trProj Delta id
        source parts majorIdx sourceV priorArgs laterArgs priorV := by
  rcases hdescriptor with
    ⟨us, headInfo, spine, name, levelParams, k, isUnsafe, lvls, params,
      indices, motives, minors, block, memberIdx, ty, rules, leanAll, major,
      descriptorBlob, descriptorInfo, hcollect, hrecursor, hminors,
      hdescriptorMajor, hparts⟩
  subst parts
  have hmajorSpine : spine[majorIdx]? =
      some (.nat major blob majorInfo) := by
    rw [hcollect] at hmajor
    exact hmajor
  have hmajorList : spine.toList[majorIdx]? =
      some (.nat major blob majorInfo) := by
    rw [Array.getElem?_toList]
    exact hmajorSpine
  have hspine := trAppSpine_of_collectSpine hsource hcollect
  obtain
    ⟨priorArgs, laterArgs, priorV, majorV, hargs, hindex, hpriorTr,
      hmajorTr, hthroughTr, hsuffixTr⟩ := hspine.splitAt hmajorList
  cases hmajorTr with
  | nat hlit =>
      exact ⟨priorArgs, laterArgs, priorV, us, headInfo, blob, majorInfo,
        hcollect, hargs, hindex, hpriorTr, hthroughTr, hsuffixTr⟩

end NatRecLiteralPartsDescriptor

namespace TrustedNatRecLiteralParts

/-- Assemble NatRecognizer's trusted descriptor, NatRuleLayout's exact Nat layout and source
split, and NatPatternMatching's constructive pattern match.  Pattern checks and RHS
identification deliberately remain outside this theorem. -/
theorem translatedCase
    {trProj : RawProjRel} {world : VerifyWorld}
    (hcatalogRel : TrustedCatalogRel trProj world)
    (layouts : TrustedNatRecursorLayouts trProj world)
    {source : KExpr .anon} {parts : NatRecLiteralParts .anon}
    (htrusted : TrustedNatRecLiteralParts world source parts)
    {uvars : Nat} {Delta : KVLCtx} {sourceV : VExpr}
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      source sourceV) :
    ∃ (id : KId .anon) (recursor : KConst .anon) (rule : RecRule .anon)
        (pattern : RecursorRulePattern)
        (priorArgs laterArgs : List (KExpr .anon)) (priorV : VExpr)
        (levels : List Lean4Lean.VLevel)
        (captures : (RecursorIotaPattern pattern.recursorName
          pattern.majorIdx pattern.constructorName
          (pattern.constructorParams.toNat +
            pattern.constructorFields.toNat)).Path → VExpr),
      NatRecLiteralTranslationSplit world.venv uvars world.nameOf trProj
        Delta id source parts pattern.majorIdx sourceV
        priorArgs laterArgs priorV ∧
      recursor.RecursorRuleAt pattern.ruleIndex rule ∧
      RawRecursorRuleRel world.venv world.nameOf trProj
        id recursor rule ∧
      RawRecursorRulePatternRel world.venv world.catalog world.nameOf
        id recursor rule pattern ∧
      NatRecIotaCase pattern parts.major ∧
      Lean4Lean.Pattern.Matches
        (RecursorIotaPattern pattern.recursorName pattern.majorIdx
          pattern.constructorName
          (pattern.constructorParams.toNat +
            pattern.constructorFields.toNat))
        (.app priorV (.natLit parts.major)) levels captures := by
  obtain ⟨id, recursor, hprimitive, hcatalog, hdescriptor⟩ := htrusted
  let layout := layouts hprimitive hcatalog
  obtain ⟨rule, pattern, hrule, hruleRel, hpattern, hcase⟩ :=
    layout.caseForMajor hcatalogRel parts.major
  obtain ⟨blob, majorInfo, hmajor⟩ := hdescriptor.patternMajor hpattern
  obtain ⟨priorArgs, laterArgs, priorV, us, headInfo, splitBlob,
    splitMajorInfo, hcollect, hargs, hindex, hpriorTr, hthroughTr,
    hlaterTr⟩ := hdescriptor.translatedSplit hsource hmajor
  obtain ⟨levels, captures, hmatch⟩ :=
    hpattern.matches_natLiteralPrefix hpriorTr hindex.symm hcase
  refine ⟨id, recursor, rule, pattern, priorArgs, laterArgs, priorV,
    levels, captures, ?_, hrule, hruleRel, hpattern, hcase, hmatch⟩
  exact ⟨us, headInfo, splitBlob, splitMajorInfo, hcollect, hargs, hindex,
    hpriorTr, hthroughTr, hlaterTr⟩

end TrustedNatRecLiteralParts

end RecM

end Ix.Tc
