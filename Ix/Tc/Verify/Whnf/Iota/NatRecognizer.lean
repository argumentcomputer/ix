import Ix.Tc.Verify.Whnf.RuntimeContracts

/-!
# Linear Nat-recognizer success provenance

The linear `Nat.rec` optimization used to expose only a whole-computation
semantic oracle.  This module first records what a successful production run
actually established: the exact constant-headed spine, primitive-address
test, recursor lookup, count test, and literal-major position.  Keeping this
trace separate from its semantic interpretation prevents trusted iota facts
from being applied to a recursor rule or major index that execution never
selected.
-/

namespace Ix.Tc

namespace KId

/-- In anonymous mode an identifier is completely determined by its content
address; the metadata component is `Unit`. -/
theorem anon_eq_of_addr_eq {left right : KId .anon}
    (h : left.addr = right.addr) : left = right := by
  rcases left with ⟨leftAddr, ⟨⟩⟩
  rcases right with ⟨rightAddr, ⟨⟩⟩
  cases h
  rfl

end KId

namespace TcM

/-- Any successful `tryGetConst` hit is present in the returned state's
concrete environment.  This covers both the initial fast hit and a hit after
the driver-owned lazy-ingress hook. -/
theorem tryGetConst_success_loaded
    {id : KId .anon} {c : KConst .anon} {s after : TcState .anon}
    (hrun : TcM.tryGetConst id s = .ok (some c) after) :
    after.env.get? id = some c := by
  unfold TcM.tryGetConst at hrun
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s = _ at hrun
  unfold EStateM.bind at hrun
  rw [show (get : TcM .anon (TcState .anon)) s = .ok s s from rfl] at hrun
  simp only at hrun
  match hget : s.env.get? id with
  | some found =>
      rw [hget] at hrun
      simp only at hrun
      rcases hrun with ⟨rfl, rfl⟩
      exact hget
  | none =>
      rw [hget] at hrun
      simp only [pure_bind] at hrun
      change EStateM.bind (get : TcM .anon (TcState .anon)) _ s = _ at hrun
      unfold EStateM.bind at hrun
      rw [show (get : TcM .anon (TcState .anon)) s = .ok s s from rfl]
        at hrun
      simp only at hrun
      change EStateM.bind (TcM.lazyIngressAddr id.addr) _ s = _ at hrun
      unfold EStateM.bind at hrun
      match hfault : TcM.lazyIngressAddr id.addr s with
      | .error err faultState =>
          rw [hfault] at hrun
          contradiction
      | .ok _ faultState =>
          rw [hfault] at hrun
          simp only at hrun
          change EStateM.bind (get : TcM .anon (TcState .anon)) _
            faultState = _ at hrun
          unfold EStateM.bind at hrun
          rw [show (get : TcM .anon (TcState .anon)) faultState =
            .ok faultState faultState from rfl] at hrun
          simp only at hrun
          match hretry : faultState.env.get? id with
          | some found =>
              rw [hretry] at hrun
              simp only at hrun
              rcases hrun with ⟨rfl, rfl⟩
              exact hretry
          | none =>
              rw [hretry] at hrun
              cases hlazy : s.lazyFault.isSome with
              | false => simp [hlazy] at hrun
              | true =>
                  simp only [hlazy, ↓reduceIte] at hrun
                  change EStateM.Result.error
                    (TcError.unknownConst id.addr) faultState = _ at hrun
                  cases hrun

end TcM

namespace RecM

/-- Pure structural meaning of a successful descriptor.  This relation
retains the recursor fields needed to compare the fast path's mathematical
major index with ordinary iota's wrapping index. -/
def NatRecLiteralPartsDescriptor (id : KId .anon) (c : KConst .anon)
    (source : KExpr .anon) (parts : NatRecLiteralParts .anon) : Prop :=
  ∃ (us : Array (KUniv .anon)) (headInfo : ExprInfo .anon)
      (spine : Array (KExpr .anon))
      (name levelParams : Unit) (k isUnsafe : Bool)
      (lvls params indices motives minors : UInt64)
      (block : KId .anon) (memberIdx : UInt64) (ty : KExpr .anon)
      (rules : Array (RecRule .anon)) (leanAll : Unit)
      (major : Nat) (blob : Address) (majorInfo : ExprInfo .anon),
    source.collectSpine = (.const id us headInfo, spine) ∧
    c = .recr name levelParams k isUnsafe lvls params indices motives
      minors block memberIdx ty rules leanAll ∧
    2 ≤ minors.toNat ∧
    spine[params.toNat + motives.toNat + minors.toNat + indices.toNat]? =
      some (.nat major blob majorInfo) ∧
    parts =
      { spine, major,
        baseIdx := params.toNat + motives.toNat,
        stepIdx := params.toNat + motives.toNat + 1,
        majorIdx := params.toNat + motives.toNat + minors.toNat +
          indices.toNat }

/-- Trusted-world certificate extracted from a successful descriptor run.
It identifies the exact catalog recursor selected by execution without yet
claiming that a zero or successor rule exists.  The witnesses remain under
the existential because this certificate is proof-irrelevant. -/
def TrustedNatRecLiteralParts (world : VerifyWorld)
    (source : KExpr .anon) (parts : NatRecLiteralParts .anon) : Prop :=
  ∃ id recursor,
    PrimitiveIdAgrees world id ``Nat.rec ∧
      world.catalog id = some recursor ∧
      NatRecLiteralPartsDescriptor id recursor source parts

/-- Exhaustive operational evidence returned by a successful
`natRecLiteralParts` execution.  The indices are definitionally the ones
computed by production, including its per-field `UInt64.toNat` conversion. -/
inductive NatRecLiteralPartsSuccessTrace
    (methods : Methods .anon) (source : KExpr .anon)
    (s : TcState .anon) :
    NatRecLiteralParts .anon → TcState .anon → Prop
  | intro
      {id : KId .anon} {us : Array (KUniv .anon)}
      {headInfo : ExprInfo .anon} {spine : Array (KExpr .anon)}
      {name : Unit} {levelParams : Unit} {k isUnsafe : Bool}
      {lvls params indices motives minors : UInt64}
      {block : KId .anon} {memberIdx : UInt64} {ty : KExpr .anon}
      {rules : Array (RecRule .anon)} {leanAll : Unit}
      {major : Nat} {blob : Address} {majorInfo : ExprInfo .anon}
      {after : TcState .anon}
      (hcollect : source.collectSpine = (.const id us headInfo, spine))
      (haddr : id.addr = s.prims.natRec.addr)
      (hlookup : TcM.tryGetConst id s =
        .ok (some (.recr name levelParams k isUnsafe lvls params indices
          motives minors block memberIdx ty rules leanAll)) after)
      (hminors : 2 ≤ minors.toNat)
      (hmajor : spine[params.toNat + motives.toNat + minors.toNat +
          indices.toNat]? = some (.nat major blob majorInfo)) :
      NatRecLiteralPartsSuccessTrace methods source s
        { spine, major,
          baseIdx := params.toNat + motives.toNat,
          stepIdx := params.toNat + motives.toNat + 1,
          majorIdx := params.toNat + motives.toNat + minors.toNat +
            indices.toNat }
        after

namespace NatRecLiteralPartsSuccessTrace

/-- Erase the success trace back to the exact production descriptor run. -/
theorem eval
    {methods : Methods .anon} {source : KExpr .anon}
    {s after : TcState .anon} {parts : NatRecLiteralParts .anon}
    (trace : NatRecLiteralPartsSuccessTrace methods source s parts after) :
    (natRecLiteralParts source).run methods s = .ok (some parts) after := by
  cases trace with
  | intro hcollect haddr hlookup hminors hmajor =>
      unfold natRecLiteralParts
      rw [hcollect, ReaderT.run_bind]
      change EStateM.bind (RecM.prims.run methods) _ s = _
      unfold EStateM.bind
      rw [prims_run]
      simp only
      simp [haddr]
      change EStateM.bind (TcM.tryGetConst _) _ s = _
      unfold EStateM.bind
      rw [hlookup]
      simp only
      rw [if_neg (by omega)]
      simp only [hmajor]
      rfl

/-- Every successful production descriptor run has the trace above; misses
and lazy-ingress errors cannot inhabit this result. -/
theorem complete
    {methods : Methods .anon} {source : KExpr .anon}
    {s after : TcState .anon} {parts : NatRecLiteralParts .anon}
    (hrun : (natRecLiteralParts source).run methods s =
      .ok (some parts) after) :
    NatRecLiteralPartsSuccessTrace methods source s parts after := by
  unfold natRecLiteralParts at hrun
  rcases hcollect : source.collectSpine with ⟨head, spine⟩
  rw [hcollect] at hrun
  cases head <;> simp only at hrun
  all_goals try { simp at hrun }
  case const id us headInfo =>
    rw [ReaderT.run_bind] at hrun
    change EStateM.bind (RecM.prims.run methods) _ s = _ at hrun
    unfold EStateM.bind at hrun
    rw [prims_run] at hrun
    simp only at hrun
    by_cases haddr : id.addr = s.prims.natRec.addr
    · simp [haddr] at hrun
      change EStateM.bind (TcM.tryGetConst id) _ s = _ at hrun
      unfold EStateM.bind at hrun
      match hlookup : TcM.tryGetConst id s with
      | .error err lookupState =>
          rw [hlookup] at hrun
          contradiction
      | .ok found lookupState =>
          rw [hlookup] at hrun
          cases found with
          | none =>
              simp only at hrun
              cases hrun
          | some c =>
              cases c <;> simp only at hrun
              all_goals try cases hrun
              case recr name levelParams k isUnsafe lvls params indices
                  motives minors block memberIdx ty rules leanAll =>
                by_cases hminors : 2 ≤ minors.toNat
                · rw [if_neg (by omega : ¬ minors.toNat < 2)] at hrun
                  match hmajor : spine[params.toNat + motives.toNat +
                      minors.toNat + indices.toNat]? with
                  | none =>
                      rw [hmajor] at hrun
                      cases hrun
                  | some majorExpr =>
                      rw [hmajor] at hrun
                      cases majorExpr
                      case nat major blob majorInfo =>
                        rcases hrun with ⟨rfl, rfl⟩
                        exact .intro hcollect haddr hlookup hminors hmajor
                      all_goals simp at hrun
                · have hlt : minors.toNat < 2 := by omega
                  rw [if_pos hlt] at hrun
                  cases hrun
    · simp [haddr] at hrun

end NatRecLiteralPartsSuccessTrace

/-- Interpret only the trusted-lookup portion of an operational success
trace.  The initial invariant binds the primitive address to `Nat.rec`; the
post-lookup invariant turns the concrete loaded hit into the immutable
catalog equation. -/
theorem NatRecLiteralPartsSuccessTrace.trusted
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode}
    (context : NoDeltaPrimitiveContext world support flags natSuccMode)
    {uvars : Nat} {Delta : KVLCtx}
    {methods : Methods .anon} {source : KExpr .anon}
    {s after : TcState .anon} {parts : NatRecLiteralParts .anon}
    (trace : NatRecLiteralPartsSuccessTrace methods source s parts after)
    (hI : WhnfStateInv .noAccel semantics trProj world support uvars Delta s)
    (hAfter : WhnfStateInv .noAccel semantics trProj world support
      uvars Delta after) :
    TrustedNatRecLiteralParts world source parts := by
  cases trace with
  | @intro id us headInfo spine name levelParams k isUnsafe lvls params
      indices motives minors block memberIdx ty rules leanAll major blob
      majorInfo after hcollect haddr hlookup hminors hmajor =>
      let recursor : KConst .anon :=
        .recr name levelParams k isUnsafe lvls params indices motives minors
          block memberIdx ty rules leanAll
      have hloaded : after.env.get? id = some recursor :=
        TcM.tryGetConst_success_loaded hlookup
      have hcatalog : world.catalog id = some recursor :=
        hAfter.1.core.loaded hloaded
      have hid : id = s.prims.natRec := KId.anon_eq_of_addr_eq haddr
      refine ⟨id, recursor, ?_, hcatalog, ?_⟩
      · simpa only [hid] using (context.stateTable hI).natRec
      · exact ⟨us, headInfo, spine, name, levelParams, k, isUnsafe, lvls,
          params, indices, motives, minors, block, memberIdx, ty, rules,
          leanAll, major, blob, majorInfo, hcollect, rfl, hminors, hmajor,
          rfl⟩

namespace TrustedNatRecLiteralParts

/-- Resolve an actually selected rule slot to the exact registered-rule
pattern and prove that the pattern's wrapping iota index is the literal
position inspected by the fast descriptor.  Rule existence remains an
explicit premise because `natRecLiteralParts` itself never indexes the rule
array. -/
theorem patternAt
    {trProj : RawProjRel} {world : VerifyWorld}
    (hcatalogRel : TrustedCatalogRel trProj world)
    {id : KId .anon} {recursor : KConst .anon}
    (hprimitive : PrimitiveIdAgrees world id ``Nat.rec)
    (hcatalog : world.catalog id = some recursor)
    {source : KExpr .anon} {parts : NatRecLiteralParts .anon}
    (hdescriptor : NatRecLiteralPartsDescriptor id recursor source parts)
    {ruleIndex : Nat} {rule : RecRule .anon}
    (hrule : recursor.RecursorRuleAt ruleIndex rule) :
    ∃ (pattern : RecursorRulePattern) (majorIdx : Nat)
        (blob : Address) (majorInfo : ExprInfo .anon),
      RawRecursorRuleRel world.venv world.nameOf trProj
          id recursor rule ∧
        RawRecursorRulePatternRel world.venv world.catalog world.nameOf
          id recursor rule pattern ∧
        pattern.ruleIndex = ruleIndex ∧
        source.collectSpine.2[majorIdx]? =
          some (.nat parts.major blob majorInfo) ∧
        pattern.majorIdx = majorIdx := by
  obtain ⟨pattern, hpattern, hindex⟩ :=
    hcatalogRel.recursorPattern hprimitive.1 hcatalog hrule
  have hruleSemantics := hcatalogRel.recursorRule hprimitive.1 hcatalog
    hrule.hasRecursorRule
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
  refine ⟨pattern,
    params.toNat + motives.toNat + minors.toNat + indices.toNat,
    blob, majorInfo, hruleSemantics, hpattern, hindex, ?_, hmajorIdx⟩
  rw [hsourceSpine]
  exact hmajor

end TrustedNatRecLiteralParts

end RecM
end Ix.Tc
