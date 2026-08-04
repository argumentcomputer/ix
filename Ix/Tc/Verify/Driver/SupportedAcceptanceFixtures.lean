import Ix.Tc.Verify.Driver.Fixtures
import Ix.Tc.Verify.Driver.SupportedAcceptance
import Ix.Tc.Verify.Inductive.EnumerationAcceptance

/-!
# Supported-acceptance adversarial and inductive fixtures

These fixtures guard the two representation-sensitive edges of the E3-S
adapter.  The first pair proves that a Muts work item cannot be discharged by
an unrouted call or a call routed to a different envelope.  The second joins
E2b's concrete Boolean family execution to the adapter's oracle-backed body
constructor; the only remaining inputs are the explicitly advertised scoped
recursive context and active cache invariant.
-/

namespace Ix.Tc

namespace SupportedAcceptanceFixture

def blockItem : AnonWorkItem :=
  .block E1Fixture.first E1Fixture.second #[E1Fixture.second]

/-- A Muts item can never be interpreted as an observed standalone route. -/
theorem block_rejects_standalone_route :
    ¬blockItem.SelectedBlockMatches none := by
  simp [blockItem, AnonWorkItem.SelectedBlockMatches]

/-- A successful route to a distinct block cannot certify this work item. -/
theorem block_rejects_wrong_route :
    ¬blockItem.SelectedBlockMatches
      (some (⟨E1Fixture.external, ()⟩ : KId .anon)) := by
  simp [blockItem, AnonWorkItem.SelectedBlockMatches]

/-- Standalone source entries deliberately admit either operational branch:
axioms use K3 directly, while singleton definitions and recursors are
committed through E0. -/
theorem standalone_allows_coordinated_route (selected : Option (KId .anon)) :
    (AnonWorkItem.standalone E1Fixture.first).SelectedBlockMatches selected :=
  trivial

/-! ## Concrete E2b body bridge -/

/-- E2b's actual Boolean family/constructor block inhabits the exact
oracle-backed constructor consumed by E3-S.  This theorem is indexed by the
real production body states and exact physical member array from
`BooleanEnumerationFixture`; it does not replace them with an abstract
inductive environment. -/
def booleanFamilyBodyResources
    {requests : List WalkerRequest} {support : RunSupport}
    (context : ScopedRecursiveMethodRunContext
      BooleanEnumerationFixture.checkerInitial
      (TcM.checkConst BooleanEnumerationFixture.familyId)
      requests RawProjRel.none BooleanEnumerationFixture.world support)
    (activePost : ActiveBlockStateWF
      (kernelCacheSemantics context.model.keys RawProjRel.none)
      RawProjRel.none BooleanEnumerationFixture.world support
      BooleanEnumerationFixture.familyMembers
      BooleanEnumerationFixture.familyBodyAfter) :
    SupportedBlockBodyResources context
      BooleanEnumerationFixture.familyBlockId
      BooleanEnumerationFixture.familyId
      BooleanEnumerationFixture.familyMembers .inductive'
      BooleanEnumerationFixture.checkerInitial
      BooleanEnumerationFixture.familyBodyAfter :=
  .oracleBacked
    (BooleanEnumerationFixture.familyLink.blockResources activePost)

/-- The adapter turns that E2b resource and the actual successful production
trace into E0's exact atomic-body certificate. -/
theorem booleanFamilyBody_certified
    {requests : List WalkerRequest} {support : RunSupport}
    (context : ScopedRecursiveMethodRunContext
      BooleanEnumerationFixture.checkerInitial
      (TcM.checkConst BooleanEnumerationFixture.familyId)
      requests RawProjRel.none BooleanEnumerationFixture.world support)
    (activePost : ActiveBlockStateWF
      (kernelCacheSemantics context.model.keys RawProjRel.none)
      RawProjRel.none BooleanEnumerationFixture.world support
      BooleanEnumerationFixture.familyMembers
      BooleanEnumerationFixture.familyBodyAfter) :
    CertifiedBlockBodySuccess
      (kernelCacheSemantics context.model.keys RawProjRel.none)
      RawProjRel.none BooleanEnumerationFixture.world support
      (Ix.Tc.methodsN (m := .anon)
        BooleanEnumerationFixture.checkerInitial.recFuel.toNat)
      BooleanEnumerationFixture.familyBlockId
      BooleanEnumerationFixture.familyId
      BooleanEnumerationFixture.familyMembers .inductive'
      BooleanEnumerationFixture.checkerInitial
      BooleanEnumerationFixture.familyBodyAfter := by
  apply (booleanFamilyBodyResources context activePost).certify
    BooleanEnumerationFixture.exactFamilyBlock
  simpa [BooleanEnumerationFixture.checkerInitial,
    BooleanEnumerationFixture.checkerMethods] using
      BooleanEnumerationFixture.familyBodyTrace

end SupportedAcceptanceFixture

end Ix.Tc
