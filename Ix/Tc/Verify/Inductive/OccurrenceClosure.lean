import Ix.Tc.Verify.Inductive.OccurrenceValidation
import Ix.Tc.Verify.RecursiveMethods.ScopedCallDomains

/-!
# Run-scoped recursive-occurrence closure

The first E2c occurrence slice exposes the exact `isDefEq` calls made while
checking uniform recursive parameters, but deliberately leaves their semantic
meaning behind `PositiveParameterDefEqContract`.  This module closes that
boundary against K2S's actual finite successor-layer method contract.

The call evidence is positional.  We require only the parameter pairs that
the successful production loop executed, rather than admitting every pair of
expressions in `RunSupport`.  This keeps the construction compatible with a
finite `Methods.ScopedCallScheduleAt` and preserves the scoped suffix-state
witness on every intermediate checker state.
-/

namespace Ix.Tc

/-- Exact finite method-call footprint of one parameter-comparison slice. -/
def PositiveParameterCallPlan (calls : Methods.CallDomain)
    (args params : Array (KExpr .anon)) : Nat → Nat → Prop
  | _, 0 => True
  | index, remaining + 1 =>
      calls.isDefEq args[index]! params[index]! ∧
        PositiveParameterCallPlan calls args params (index + 1) remaining

namespace RecM.PositiveParameterComparisonTrace

/-- Interpret every successful parameter comparison through the real
successor method-table layer selected by K2S.

`Methods.next methods` is definitionally the six production algorithms run
with `methods` as their recursive callback table.  Its `isDefEq` field is
therefore exactly the action retained by
`PositiveParameterComparisonTrace`. -/
theorem theoryDefEqScoped
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport} {calls : Methods.CallDomain}
    {Delta : KVLCtx} {methods : Methods .anon}
    (successor : Methods.ScopedWFAtOn model layer semantics support calls
      (Methods.next methods))
    {args params : Array (KExpr .anon)}
    {index remaining : Nat} {initial final : TcState .anon}
    (trace : PositiveParameterComparisonTrace args params methods index
      remaining initial final)
    (hinitial : ScopedWhnfStateInv model layer semantics support Delta initial)
    (translations : PositiveParameterTranslationPlan trProj world support
      model.keys.uvars Delta args params index remaining)
    (callPlan : PositiveParameterCallPlan calls args params index remaining) :
    PositiveParameterPairs
        (TranslatedParameterDefEq trProj world support model.keys.uvars Delta)
        args params index remaining ∧
      ScopedWhnfStateInv model layer semantics support Delta final := by
  induction trace with
  | nil => exact ⟨trivial, hinitial⟩
  | @cons index remaining before afterComparison final hcomparison _ ih =>
      rcases translations with
        ⟨hargumentSupport, hparameterSupport, argumentV, parameterV,
          hargument, hparameter, htailTranslations⟩
      rcases callPlan with ⟨hcall, htailCalls⟩
      have hverified := successor.isDefEq (s := before) hcall hargument
        hparameter
      have hpost := hverified hinitial
      simp only [Methods.next] at hpost
      rw [hcomparison] at hpost
      have htail := ih hpost.1 htailTranslations htailCalls
      exact ⟨
        ⟨⟨hargumentSupport, hparameterSupport, argumentV, parameterV,
          hargument, hparameter, hpost.2 rfl⟩, htail.1⟩,
        htail.2⟩

end RecM.PositiveParameterComparisonTrace

namespace RecM.ValidPositiveRecursiveApplicationHeader

/-- Discharge the parameter component of one valid resolved recursive-family
header with an exact finite successor-layer call plan. -/
theorem theoryParametersScoped
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport} {calls : Methods.CallDomain}
    {Delta : KVLCtx} {methods : Methods .anon}
    (successor : Methods.ScopedWFAtOn model layer semantics support calls
      (Methods.next methods))
    {id : KId .anon} {us : Array (KUniv .anon)}
    {args : Array (KExpr .anon)} {group : PositivityGroup .anon}
    {rootAddrs : Array Address} {nParams nIndices levels : Nat}
    {initial final : TcState .anon}
    (valid : ValidPositiveRecursiveApplicationHeader id us args group
      rootAddrs nParams nIndices levels methods initial final)
    (hinitial : ScopedWhnfStateInv model layer semantics support Delta initial)
    (translations : PositiveParameterTranslationPlan trProj world support
      model.keys.uvars Delta args group.params 0 nParams)
    (callPlan : PositiveParameterCallPlan calls args group.params 0 nParams) :
    ∃ afterParameters,
      PositiveParameterPairs
          (TranslatedParameterDefEq trProj world support model.keys.uvars
            Delta)
          args group.params 0 nParams ∧
        ScopedWhnfStateInv model layer semantics support Delta afterParameters ∧
        final = afterParameters := by
  rcases valid with
    ⟨_, _, _, _, afterParameters, _, trace, _, hfinal⟩
  have hsemantic :=
    RecM.PositiveParameterComparisonTrace.theoryDefEqScoped successor trace
      hinitial translations callPlan
  exact ⟨afterParameters, hsemantic.1, hsemantic.2, hfinal⟩

end RecM.ValidPositiveRecursiveApplicationHeader

end Ix.Tc
