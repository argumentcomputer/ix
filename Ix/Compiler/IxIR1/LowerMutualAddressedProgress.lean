import Ix.Compiler.EraseAddressedSim
import Ix.Compiler.IxIR1.LowerAddressedSim
import Ix.Compiler.IxIR1.LowerMutualAddressedSim
import Ix.Compiler.IxIR1.LowerProgress

/-!
# Certified progress through both production address passes

The executable erasure validator certifies the literal legacy IxIR₀
environment.  Production first replaces mutual-member keys in that environment
and then replaces generated IxIR₁ keys after lowering.  The trace transport
in `IxIR0.ReaddressProjectionSafe` lets the validator's exact call-aware trace
feed the sealed lowering-progress theorem at the first addressed image; the
existing IxIR₁ evaluator transport then carries the successful target run
through the second image.
-/

namespace Ix.Compiler.IxIR1.LowerSim

open Ix.Compiler.Ixon (Address Constant Owned)
open Ix.Compiler.IxIR1.Lower

/-- Preserve the source-value relation carried by a raw erasure certificate
while exposing the structurally renamed IxIR₀ value used by production. -/
def MutualAddressedInlinedValRel (ectx : Ixon.Eval.EvalCtx)
    (rawCtx : IxIR0.Ctx) (rename : Address → Address)
    (sourceValue : Ixon.Eval.Value) (addressedValue : IxIR0.Value)
    [scope : Ix.Compiler.Sim.MemberScope] : Prop :=
  ∃ rawValue,
    Ix.Compiler.Sim.InlinedValRel ectx rawCtx sourceValue rawValue ∧
      addressedValue = IxIR0.Readdress.Value.mapAddresses rename rawValue

namespace CallAwareProjectionSafe

/-- A validator certificate over the exact legacy environment yields the
exact call-aware trace of the addressed IxIR₀ main.  The accompanying value
relation retains the raw witness instead of pretending that `ValRel` itself is
address-invariant. -/
theorem of_certifiedSharedClosed_addressed
    {ectx : Ixon.Eval.EvalCtx} {frame : Ixon.Eval.Frame}
    {source : Ixon.Expr} {sourceFuel certFuel : Nat}
    {sourceValue : Ixon.Eval.Value} {eraseCtx : Erase.EraseCtx}
    {constants : List (Address × Constant)} {programEraseFuel : Nat}
    {erased : EraseAddressed.Result}
    (beforeOracle afterOracle : IxIR0.Oracle)
    (cert : Ix.Compiler.EraseValidator.CertifiedSharedExpr ectx
      (erased.rawCtx beforeOracle) none
      (Ix.Compiler.EraseValidator.tablesOfFrame frame)
      frame.selfAddr [] certFuel source)
    (hstrict : ectx.Strict)
    (herase : EraseAddressed.run eraseCtx constants cert.target
      programEraseFuel = .ok erased)
    (hrenameOracle : ∀ address arguments,
      afterOracle
          (IxIR0.MutualBlock.Renaming.apply erased.addressMap address)
          (IxIR0.Readdress.ValueList.mapAddresses
            (IxIR0.MutualBlock.Renaming.apply erased.addressMap) arguments) =
        (beforeOracle address arguments).map
          (IxIR0.Readdress.Value.mapAddresses
            (IxIR0.MutualBlock.Renaming.apply erased.addressMap)))
    (horacles : Ix.Compiler.Sim.OracleRel ectx.inlineSharing
      (erased.rawCtx beforeOracle))
    (hctx : ectx.SharingWF) (hframe : frame.SharingWF)
    (hbelow : Ixon.Sharing.sharesBelow frame.sharing.size source = true)
    (hsource : Ixon.Eval.eval ectx sourceFuel frame [] source =
      .ok sourceValue) :
    ∃ targetFuel targetValue,
      IxIR0.ProjectionSafe.Eval
          (erased.addressed.addressedCtx afterOracle) targetFuel []
          erased.main targetValue ∧
        MutualAddressedInlinedValRel ectx
          (erased.rawCtx beforeOracle)
          (IxIR0.MutualBlock.Renaming.apply erased.addressMap)
          sourceValue targetValue := by
  obtain ⟨targetFuel, rawValue, htrace, hrel⟩ :=
    CallAwareProjectionSafe.of_certifiedSharedClosed cert hstrict horacles hctx
      hframe hbelow hsource
  let rename := IxIR0.MutualBlock.Renaming.apply erased.addressMap
  refine ⟨targetFuel, IxIR0.Readdress.Value.mapAddresses rename rawValue,
    ?_, rawValue, hrel, rfl⟩
  exact EraseAddressed.run_projectionSafeMain_of_run_eq_ok herase
    beforeOracle afterOracle hrenameOracle htrace

/-- Member-scoped certificate transport through production IxIR₀
readdressing.  This is the cyclic/indexed counterpart of the empty-scope
compatibility theorem above. -/
theorem of_certifiedSharedClosed_addressed_with_members
    [scope : Ix.Compiler.Sim.MemberScope]
    {ectx : Ixon.Eval.EvalCtx} {frame : Ixon.Eval.Frame}
    {source : Ixon.Expr} {sourceFuel certFuel : Nat}
    {sourceValue : Ixon.Eval.Value} {eraseCtx : Erase.EraseCtx}
    {constants : List (Address × Constant)} {programEraseFuel : Nat}
    {erased : EraseAddressed.Result}
    (beforeOracle afterOracle : IxIR0.Oracle)
    (hmembers : Ix.Compiler.Sim.MemberCoverage ectx.inlineSharing
      (erased.rawCtx beforeOracle) scope.plan)
    (cert : Ix.Compiler.EraseValidator.CertifiedSharedExpr ectx
      (erased.rawCtx beforeOracle) none
      (Ix.Compiler.EraseValidator.tablesOfFrame frame)
      frame.selfAddr [] certFuel source)
    (herase : EraseAddressed.run eraseCtx constants cert.target
      programEraseFuel = .ok erased)
    (hrenameOracle : ∀ address arguments,
      afterOracle
          (IxIR0.MutualBlock.Renaming.apply erased.addressMap address)
          (IxIR0.Readdress.ValueList.mapAddresses
            (IxIR0.MutualBlock.Renaming.apply erased.addressMap) arguments) =
        (beforeOracle address arguments).map
          (IxIR0.Readdress.Value.mapAddresses
            (IxIR0.MutualBlock.Renaming.apply erased.addressMap)))
    (horacles : Ix.Compiler.Sim.OracleRel ectx.inlineSharing
      (erased.rawCtx beforeOracle))
    (hctx : ectx.SharingWF) (hframe : frame.SharingWF)
    (hbelow : Ixon.Sharing.sharesBelow frame.sharing.size source = true)
    (hsource : Ixon.Eval.eval ectx sourceFuel frame [] source =
      .ok sourceValue) :
    ∃ targetFuel targetValue,
      IxIR0.ProjectionSafe.Eval
          (erased.addressed.addressedCtx afterOracle) targetFuel []
          erased.main targetValue ∧
        MutualAddressedInlinedValRel ectx
          (erased.rawCtx beforeOracle)
          (IxIR0.MutualBlock.Renaming.apply erased.addressMap)
          sourceValue targetValue := by
  obtain ⟨targetFuel, rawValue, htrace, hrel⟩ :=
    CallAwareProjectionSafe.of_certifiedSharedClosed_with_members hmembers cert
      horacles hctx hframe hbelow hsource
  let rename := IxIR0.MutualBlock.Renaming.apply erased.addressMap
  refine ⟨targetFuel, IxIR0.Readdress.Value.mapAddresses rename rawValue,
    ?_, rawValue, hrel, rfl⟩
  exact EraseAddressed.run_projectionSafeMain_of_run_eq_ok herase
    beforeOracle afterOracle hrenameOracle htrace

end CallAwareProjectionSafe

/-- The raw IxIR₁ target produced from a certified addressed IxIR₀ main
has a successful run.  All callable value and trace contracts are rebuilt
from the actual compiler output; only the two explicit extern contracts
remain premises. -/
theorem lowerAllIndexedAction_main_progress_of_addressed_certificate_sealed
    {ectx : Ixon.Eval.EvalCtx} {frame : Ixon.Eval.Frame}
    {source : Ixon.Expr} {sourceFuel certFuel : Nat}
    {sourceValue : Ixon.Eval.Value} {eraseCtx : Erase.EraseCtx}
    {constants : List (Address × Constant)} {programEraseFuel : Nat}
    {erased : EraseAddressed.Result}
    (beforeOracle afterOracle : IxIR0.Oracle)
    (cert : Ix.Compiler.EraseValidator.CertifiedSharedExpr ectx
      (erased.rawCtx beforeOracle) none
      (Ix.Compiler.EraseValidator.tablesOfFrame frame)
      frame.selfAddr [] certFuel source)
    (hstrict : ectx.Strict)
    (herase : EraseAddressed.run eraseCtx constants cert.target
      programEraseFuel = .ok erased)
    (hrenameOracle : ∀ address arguments,
      afterOracle
          (IxIR0.MutualBlock.Renaming.apply erased.addressMap address)
          (IxIR0.Readdress.ValueList.mapAddresses
            (IxIR0.MutualBlock.Renaming.apply erased.addressMap) arguments) =
        (beforeOracle address arguments).map
          (IxIR0.Readdress.Value.mapAddresses
            (IxIR0.MutualBlock.Renaming.apply erased.addressMap)))
    (horacles : Ix.Compiler.Sim.OracleRel ectx.inlineSharing
      (erased.rawCtx beforeOracle))
    (hctx : ectx.SharingWF) (hframe : frame.SharingWF)
    (hbelow : Ixon.Sharing.sharesBelow frame.sharing.size source = true)
    (hsource : Ixon.Eval.eval ectx sourceFuel frame [] source =
      .ok sourceValue)
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {targetCtx : Ctx}
    (hlower :
      (lowerAllIndexedAction erased.declarations erased.main mainWorld
        compilerFuel).run {} = .ok (raw, mainCode) finalState)
    (htarget : ∀ {targetAddress targetDecl},
      (targetAddress, targetDecl) ∈ raw →
      targetCtx.decls targetAddress = some targetDecl)
    (hrepresented : ExtraRepresented targetCtx finalState)
    (hcontracts : CompilerContracts (IxIR0.Env.ofList erased.declarations)
      targetCtx)
    (hexternValue : ExternValueContract
      (CompilerFunctionRel
        (erased.addressed.addressedCtx afterOracle)
        (IxIR0.Env.ofList erased.declarations) finalState)
      (erased.addressed.addressedCtx afterOracle)
      targetCtx)
    (hexternProgress : ExternTraceProgressContract
      (CompilerFunctionRel
        (erased.addressed.addressedCtx afterOracle)
        (IxIR0.Env.ofList erased.declarations) finalState)
      (erased.addressed.addressedCtx afterOracle)
      targetCtx) :
    ∃ targetFuel store value,
      runMain targetCtx mainCode targetFuel = .ok (store, value) := by
  obtain ⟨traceFuel, _, htrace, _⟩ :=
    CallAwareProjectionSafe.of_certifiedSharedClosed_addressed
      beforeOracle afterOracle cert hstrict herase hrenameOracle horacles hctx
      hframe hbelow hsource
  have hlower' :
      (lowerAllAction erased.declarations erased.main mainWorld
        compilerFuel).run {} = .ok (raw, mainCode) finalState := by
    simpa only [lowerAllIndexedAction_eq_lowerAllAction] using hlower
  have henv : (erased.addressed.addressedCtx afterOracle).env =
      IxIR0.Env.ofList erased.declarations := rfl
  exact lowerAllAction_main_progress_of_trace_sealed henv hlower' htarget
    hrepresented hcontracts hexternValue hexternProgress htrace

/-- Member-scoped form of raw addressed target progress.  Simultaneous member
coverage replaces the empty-scope strictness route while all lowering and
extern contracts remain identical. -/
theorem
    lowerAllIndexedAction_main_progress_of_addressed_certificate_with_members_sealed
    [scope : Ix.Compiler.Sim.MemberScope]
    {ectx : Ixon.Eval.EvalCtx} {frame : Ixon.Eval.Frame}
    {source : Ixon.Expr} {sourceFuel certFuel : Nat}
    {sourceValue : Ixon.Eval.Value} {eraseCtx : Erase.EraseCtx}
    {constants : List (Address × Constant)} {programEraseFuel : Nat}
    {erased : EraseAddressed.Result}
    (beforeOracle afterOracle : IxIR0.Oracle)
    (hmembers : Ix.Compiler.Sim.MemberCoverage ectx.inlineSharing
      (erased.rawCtx beforeOracle) scope.plan)
    (cert : Ix.Compiler.EraseValidator.CertifiedSharedExpr ectx
      (erased.rawCtx beforeOracle) none
      (Ix.Compiler.EraseValidator.tablesOfFrame frame)
      frame.selfAddr [] certFuel source)
    (herase : EraseAddressed.run eraseCtx constants cert.target
      programEraseFuel = .ok erased)
    (hrenameOracle : ∀ address arguments,
      afterOracle
          (IxIR0.MutualBlock.Renaming.apply erased.addressMap address)
          (IxIR0.Readdress.ValueList.mapAddresses
            (IxIR0.MutualBlock.Renaming.apply erased.addressMap) arguments) =
        (beforeOracle address arguments).map
          (IxIR0.Readdress.Value.mapAddresses
            (IxIR0.MutualBlock.Renaming.apply erased.addressMap)))
    (horacles : Ix.Compiler.Sim.OracleRel ectx.inlineSharing
      (erased.rawCtx beforeOracle))
    (hctx : ectx.SharingWF) (hframe : frame.SharingWF)
    (hbelow : Ixon.Sharing.sharesBelow frame.sharing.size source = true)
    (hsource : Ixon.Eval.eval ectx sourceFuel frame [] source =
      .ok sourceValue)
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {targetCtx : Ctx}
    (hlower :
      (lowerAllIndexedAction erased.declarations erased.main mainWorld
        compilerFuel).run {} = .ok (raw, mainCode) finalState)
    (htarget : ∀ {targetAddress targetDecl},
      (targetAddress, targetDecl) ∈ raw →
      targetCtx.decls targetAddress = some targetDecl)
    (hrepresented : ExtraRepresented targetCtx finalState)
    (hcontracts : CompilerContracts (IxIR0.Env.ofList erased.declarations)
      targetCtx)
    (hexternValue : ExternValueContract
      (CompilerFunctionRel
        (erased.addressed.addressedCtx afterOracle)
        (IxIR0.Env.ofList erased.declarations) finalState)
      (erased.addressed.addressedCtx afterOracle)
      targetCtx)
    (hexternProgress : ExternTraceProgressContract
      (CompilerFunctionRel
        (erased.addressed.addressedCtx afterOracle)
        (IxIR0.Env.ofList erased.declarations) finalState)
      (erased.addressed.addressedCtx afterOracle)
      targetCtx) :
    ∃ targetFuel store value,
      runMain targetCtx mainCode targetFuel = .ok (store, value) := by
  obtain ⟨traceFuel, _, htrace, _⟩ :=
    CallAwareProjectionSafe.of_certifiedSharedClosed_addressed_with_members
      beforeOracle afterOracle hmembers cert herase hrenameOracle horacles hctx
      hframe hbelow hsource
  have hlower' :
      (lowerAllAction erased.declarations erased.main mainWorld
        compilerFuel).run {} = .ok (raw, mainCode) finalState := by
    simpa only [lowerAllIndexedAction_eq_lowerAllAction] using hlower
  have henv : (erased.addressed.addressedCtx afterOracle).env =
      IxIR0.Env.ofList erased.declarations := rfl
  exact lowerAllAction_main_progress_of_trace_sealed henv hlower' htarget
    hrepresented hcontracts hexternValue hexternProgress htrace

/-- The successful raw target run survives the generated-code address pass,
so the exact production artifact has a successful execution. -/
theorem lowerAllIndexedAddressed_main_progress_of_certificate_sealed
    {ectx : Ixon.Eval.EvalCtx} {frame : Ixon.Eval.Frame}
    {source : Ixon.Expr} {sourceFuel certFuel : Nat}
    {sourceValue : Ixon.Eval.Value} {eraseCtx : Erase.EraseCtx}
    {constants : List (Address × Constant)} {programEraseFuel : Nat}
    {erased : EraseAddressed.Result}
    (beforeOracle : IxIR0.Oracle)
    (cert : Ix.Compiler.EraseValidator.CertifiedSharedExpr ectx
      (erased.rawCtx beforeOracle) none
      (Ix.Compiler.EraseValidator.tablesOfFrame frame)
      frame.selfAddr [] certFuel source)
    (hstrict : ectx.Strict)
    (herase : EraseAddressed.run eraseCtx constants cert.target
      programEraseFuel = .ok erased)
    (hreaddressable : IxIR0.Readdress.Oracle.Readdressable
      erased.addressMap beforeOracle)
    (horacles : Ix.Compiler.Sim.OracleRel ectx.inlineSharing
      (erased.rawCtx beforeOracle))
    (hctx : ectx.SharingWF) (hframe : frame.SharingWF)
    (hbelow : Ixon.Sharing.sharesBelow frame.sharing.size source = true)
    (hsource : Ixon.Eval.eval ectx sourceFuel frame [] source =
      .ok sourceValue)
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {lowered : IxIR1.Readdress.Result}
    (hlower :
      (lowerAllIndexedAction erased.declarations erased.main mainWorld
        compilerFuel).run {} = .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllIndexedAddressed erased.declarations erased.main mainWorld
        compilerFuel = .ok lowered)
    (targetOracle : Address → List RVal → Option RVal)
    (htarget : ∀ {targetAddress targetDecl},
      (targetAddress, targetDecl) ∈ raw →
      (lowered.preAddressCtx raw targetOracle).decls targetAddress =
        some targetDecl)
    (hrepresented : ExtraRepresented
      (lowered.preAddressCtx raw targetOracle) finalState)
    (hcontracts : CompilerContracts (IxIR0.Env.ofList erased.declarations)
      (lowered.preAddressCtx raw targetOracle))
    (hexternValue : ExternValueContract
      (CompilerFunctionRel
        (erased.addressed.addressedCtx
          (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
        (IxIR0.Env.ofList erased.declarations) finalState)
      (erased.addressed.addressedCtx
        (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
      (lowered.preAddressCtx raw targetOracle))
    (hexternProgress : ExternTraceProgressContract
      (CompilerFunctionRel
        (erased.addressed.addressedCtx
          (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
        (IxIR0.Env.ofList erased.declarations) finalState)
      (erased.addressed.addressedCtx
        (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
      (lowered.preAddressCtx raw targetOracle)) :
    ∃ targetFuel store value,
      runMain (lowered.addressedCtx targetOracle) lowered.main targetFuel =
        .ok (store, value) := by
  obtain ⟨targetFuel, rawStore, targetValue, hraw⟩ :=
    lowerAllIndexedAction_main_progress_of_addressed_certificate_sealed
      (targetCtx := lowered.preAddressCtx raw targetOracle)
      beforeOracle
      (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle)
      cert hstrict herase
      (IxIR0.Readdress.Oracle.readdress_compatible hreaddressable)
      horacles hctx hframe
      hbelow hsource hlower htarget hrepresented hcontracts hexternValue
      hexternProgress
  refine ⟨targetFuel,
    IxIR1.Readdress.Store.mapAddresses
      (IxIR1.Readdress.Renaming.apply lowered.addressMap) rawStore,
    targetValue, ?_⟩
  exact lowerAllIndexedAddressed_runMain_success hlower haddressed
    targetOracle hraw

/-- Full certificate-sealed production simulation.  The validator's raw
call-aware trace establishes target progress after IxIR₀ readdressing;
whole-pass value contracts establish raw lowering agreement; and both address
maps are then composed by their evaluator transports. -/
theorem
    lowerAllIndexedAddressed_semanticForwardSimulation_of_certificate_sealed
    {ectx : Ixon.Eval.EvalCtx} {frame : Ixon.Eval.Frame}
    {source : Ixon.Expr} {sourceFuel certFuel : Nat}
    {sourceValue : Ixon.Eval.Value} {eraseCtx : Erase.EraseCtx}
    {constants : List (Address × Constant)} {programEraseFuel : Nat}
    {erased : EraseAddressed.Result}
    (beforeOracle : IxIR0.Oracle)
    (cert : Ix.Compiler.EraseValidator.CertifiedSharedExpr ectx
      (erased.rawCtx beforeOracle) none
      (Ix.Compiler.EraseValidator.tablesOfFrame frame)
      frame.selfAddr [] certFuel source)
    (hstrict : ectx.Strict)
    (herase : EraseAddressed.run eraseCtx constants cert.target
      programEraseFuel = .ok erased)
    (hreaddressable : IxIR0.Readdress.Oracle.Readdressable
      erased.addressMap beforeOracle)
    (horacles : Ix.Compiler.Sim.OracleRel ectx.inlineSharing
      (erased.rawCtx beforeOracle))
    (hctx : ectx.SharingWF) (hframe : frame.SharingWF)
    (hbelow : Ixon.Sharing.sharesBelow frame.sharing.size source = true)
    (hsource : Ixon.Eval.eval ectx sourceFuel frame [] source =
      .ok sourceValue)
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {lowered : IxIR1.Readdress.Result}
    (hlower :
      (lowerAllIndexedAction erased.declarations erased.main mainWorld
        compilerFuel).run {} = .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllIndexedAddressed erased.declarations erased.main mainWorld
        compilerFuel = .ok lowered)
    (targetOracle : Address → List RVal → Option RVal)
    (htarget : ∀ {targetAddress targetDecl},
      (targetAddress, targetDecl) ∈ raw →
      (lowered.preAddressCtx raw targetOracle).decls targetAddress =
        some targetDecl)
    (hrepresented : ExtraRepresented
      (lowered.preAddressCtx raw targetOracle) finalState)
    (hcontracts : CompilerContracts (IxIR0.Env.ofList erased.declarations)
      (lowered.preAddressCtx raw targetOracle))
    (hexternValue : ExternValueContract
      (CompilerFunctionRel
        (erased.addressed.addressedCtx
          (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
        (IxIR0.Env.ofList erased.declarations) finalState)
      (erased.addressed.addressedCtx
        (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
      (lowered.preAddressCtx raw targetOracle))
    (hexternProgress : ExternTraceProgressContract
      (CompilerFunctionRel
        (erased.addressed.addressedCtx
          (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
        (IxIR0.Env.ofList erased.declarations) finalState)
      (erased.addressed.addressedCtx
        (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
      (lowered.preAddressCtx raw targetOracle)) :
    MutualAddressedSemanticForwardSimulation
      (erased.addressed.preAddressCtx erased.groups beforeOracle)
      (lowered.addressedCtx targetOracle) cert.target lowered.main
      (IxIR0.MutualBlock.Renaming.apply erased.addressMap)
      (IxIR1.Readdress.Renaming.apply lowered.addressMap)
      (CompilerFunctionRel
        (erased.addressed.addressedCtx
          (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
        (IxIR0.Env.ofList erased.declarations) finalState) := by
  have hlower' :
      (lowerAllAction erased.declarations erased.main mainWorld
        compilerFuel).run {} = .ok (raw, mainCode) finalState := by
    simpa only [lowerAllIndexedAction_eq_lowerAllAction] using hlower
  have henv : (erased.addressed.addressedCtx
      (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle)).env =
      IxIR0.Env.ofList erased.declarations := rfl
  have hfixedProgress :=
    lowerAllIndexedAction_main_progress_of_addressed_certificate_sealed
      (targetCtx := lowered.preAddressCtx raw targetOracle)
      beforeOracle
      (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle)
      cert hstrict herase
      (IxIR0.Readdress.Oracle.readdress_compatible hreaddressable)
      horacles hctx hframe
      hbelow hsource hlower htarget hrepresented hcontracts hexternValue
      hexternProgress
  have hrawSimulation : SemanticForwardSimulation
      (erased.addressed.addressedCtx
        (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
      (lowered.preAddressCtx raw targetOracle) erased.main mainCode
      (CompilerFunctionRel
        (erased.addressed.addressedCtx
          (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
        (IxIR0.Env.ofList erased.declarations) finalState) := by
    apply lowerAllAction_semanticForwardSimulation_of_targetProgress_sealed
      henv hlower' htarget hrepresented hcontracts hexternValue
    intro _ _ _
    exact hfixedProgress
  intro legacyFuel legacyValue hlegacy
  exact lowerAllIndexedAddressed_after_addressedErasure herase
    beforeOracle
    (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle)
    (IxIR0.Readdress.Oracle.readdress_compatible hreaddressable)
    hlower haddressed targetOracle
    hrawSimulation hlegacy

/-! ## SCC-aware production endpoint -/

/-- The certificate-sealed raw target run survives complete source/generated
SCC readdressing, yielding progress for the exact pipeline artifact. -/
theorem lowerAllIndexedFullyAddressed_main_progress_of_certificate_sealed
    {ectx : Ixon.Eval.EvalCtx} {frame : Ixon.Eval.Frame}
    {source : Ixon.Expr} {sourceFuel certFuel : Nat}
    {sourceValue : Ixon.Eval.Value} {eraseCtx : Erase.EraseCtx}
    {constants : List (Address × Constant)} {programEraseFuel : Nat}
    {erased : EraseAddressed.Result}
    (beforeOracle : IxIR0.Oracle)
    (cert : Ix.Compiler.EraseValidator.CertifiedSharedExpr ectx
      (erased.rawCtx beforeOracle) none
      (Ix.Compiler.EraseValidator.tablesOfFrame frame)
      frame.selfAddr [] certFuel source)
    (hstrict : ectx.Strict)
    (herase : EraseAddressed.run eraseCtx constants cert.target
      programEraseFuel = .ok erased)
    (hreaddressable : IxIR0.Readdress.Oracle.Readdressable
      erased.addressMap beforeOracle)
    (horacles : Ix.Compiler.Sim.OracleRel ectx.inlineSharing
      (erased.rawCtx beforeOracle))
    (hctx : ectx.SharingWF) (hframe : frame.SharingWF)
    (hbelow : Ixon.Sharing.sharesBelow frame.sharing.size source = true)
    (hsource : Ixon.Eval.eval ectx sourceFuel frame [] source =
      .ok sourceValue)
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {lowered : IxIR1.ReaddressAll.Result}
    (hlower :
      (lowerAllIndexedAction erased.declarations erased.main mainWorld
        compilerFuel).run {} = .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllIndexedFullyAddressed erased.declarations erased.main mainWorld
        compilerFuel = .ok lowered)
    (targetOracle : Address → List RVal → Option RVal)
    (htarget : ∀ {targetAddress targetDecl},
      (targetAddress, targetDecl) ∈ raw →
      (lowered.preAddressCtx raw targetOracle).decls targetAddress =
        some targetDecl)
    (hrepresented : ExtraRepresented
      (lowered.preAddressCtx raw targetOracle) finalState)
    (hcontracts : CompilerContracts (IxIR0.Env.ofList erased.declarations)
      (lowered.preAddressCtx raw targetOracle))
    (hexternValue : ExternValueContract
      (CompilerFunctionRel
        (erased.addressed.addressedCtx
          (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
        (IxIR0.Env.ofList erased.declarations) finalState)
      (erased.addressed.addressedCtx
        (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
      (lowered.preAddressCtx raw targetOracle))
    (hexternProgress : ExternTraceProgressContract
      (CompilerFunctionRel
        (erased.addressed.addressedCtx
          (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
        (IxIR0.Env.ofList erased.declarations) finalState)
      (erased.addressed.addressedCtx
        (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
      (lowered.preAddressCtx raw targetOracle)) :
    ∃ targetFuel store value,
      runMain (lowered.addressedCtx targetOracle) lowered.main targetFuel =
        .ok (store, value) := by
  obtain ⟨targetFuel, rawStore, targetValue, hraw⟩ :=
    lowerAllIndexedAction_main_progress_of_addressed_certificate_sealed
      (targetCtx := lowered.preAddressCtx raw targetOracle)
      beforeOracle
      (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle)
      cert hstrict herase
      (IxIR0.Readdress.Oracle.readdress_compatible hreaddressable)
      horacles hctx hframe hbelow hsource hlower htarget hrepresented
      hcontracts hexternValue hexternProgress
  refine ⟨targetFuel,
    IxIR1.Readdress.Store.mapAddresses
      (IxIR1.Readdress.Renaming.apply lowered.addressMap) rawStore,
    targetValue, ?_⟩
  exact lowerAllIndexedFullyAddressed_runMain_success hlower haddressed
    targetOracle hraw

/-- Final certificate-sealed production simulation through cycle-safe IxIR₀
member addressing and complete cycle-safe IxIR₁ content addressing. -/
theorem
    lowerAllIndexedFullyAddressed_semanticForwardSimulation_of_certificate_sealed
    {ectx : Ixon.Eval.EvalCtx} {frame : Ixon.Eval.Frame}
    {source : Ixon.Expr} {sourceFuel certFuel : Nat}
    {sourceValue : Ixon.Eval.Value} {eraseCtx : Erase.EraseCtx}
    {constants : List (Address × Constant)} {programEraseFuel : Nat}
    {erased : EraseAddressed.Result}
    (beforeOracle : IxIR0.Oracle)
    (cert : Ix.Compiler.EraseValidator.CertifiedSharedExpr ectx
      (erased.rawCtx beforeOracle) none
      (Ix.Compiler.EraseValidator.tablesOfFrame frame)
      frame.selfAddr [] certFuel source)
    (hstrict : ectx.Strict)
    (herase : EraseAddressed.run eraseCtx constants cert.target
      programEraseFuel = .ok erased)
    (hreaddressable : IxIR0.Readdress.Oracle.Readdressable
      erased.addressMap beforeOracle)
    (horacles : Ix.Compiler.Sim.OracleRel ectx.inlineSharing
      (erased.rawCtx beforeOracle))
    (hctx : ectx.SharingWF) (hframe : frame.SharingWF)
    (hbelow : Ixon.Sharing.sharesBelow frame.sharing.size source = true)
    (hsource : Ixon.Eval.eval ectx sourceFuel frame [] source =
      .ok sourceValue)
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {lowered : IxIR1.ReaddressAll.Result}
    (hlower :
      (lowerAllIndexedAction erased.declarations erased.main mainWorld
        compilerFuel).run {} = .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllIndexedFullyAddressed erased.declarations erased.main mainWorld
        compilerFuel = .ok lowered)
    (targetOracle : Address → List RVal → Option RVal)
    (htarget : ∀ {targetAddress targetDecl},
      (targetAddress, targetDecl) ∈ raw →
      (lowered.preAddressCtx raw targetOracle).decls targetAddress =
        some targetDecl)
    (hrepresented : ExtraRepresented
      (lowered.preAddressCtx raw targetOracle) finalState)
    (hcontracts : CompilerContracts (IxIR0.Env.ofList erased.declarations)
      (lowered.preAddressCtx raw targetOracle))
    (hexternValue : ExternValueContract
      (CompilerFunctionRel
        (erased.addressed.addressedCtx
          (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
        (IxIR0.Env.ofList erased.declarations) finalState)
      (erased.addressed.addressedCtx
        (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
      (lowered.preAddressCtx raw targetOracle))
    (hexternProgress : ExternTraceProgressContract
      (CompilerFunctionRel
        (erased.addressed.addressedCtx
          (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
        (IxIR0.Env.ofList erased.declarations) finalState)
      (erased.addressed.addressedCtx
        (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
      (lowered.preAddressCtx raw targetOracle)) :
    MutualAddressedSemanticForwardSimulation
      (erased.addressed.preAddressCtx erased.groups beforeOracle)
      (lowered.addressedCtx targetOracle) cert.target lowered.main
      (IxIR0.MutualBlock.Renaming.apply erased.addressMap)
      (IxIR1.Readdress.Renaming.apply lowered.addressMap)
      (CompilerFunctionRel
        (erased.addressed.addressedCtx
          (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
        (IxIR0.Env.ofList erased.declarations) finalState) := by
  have hlower' :
      (lowerAllAction erased.declarations erased.main mainWorld
        compilerFuel).run {} = .ok (raw, mainCode) finalState := by
    simpa only [lowerAllIndexedAction_eq_lowerAllAction] using hlower
  have henv : (erased.addressed.addressedCtx
      (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle)).env =
      IxIR0.Env.ofList erased.declarations := rfl
  have hfixedProgress :=
    lowerAllIndexedAction_main_progress_of_addressed_certificate_sealed
      (targetCtx := lowered.preAddressCtx raw targetOracle)
      beforeOracle
      (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle)
      cert hstrict herase
      (IxIR0.Readdress.Oracle.readdress_compatible hreaddressable)
      horacles hctx hframe hbelow hsource hlower htarget hrepresented
      hcontracts hexternValue hexternProgress
  have hrawSimulation : SemanticForwardSimulation
      (erased.addressed.addressedCtx
        (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
      (lowered.preAddressCtx raw targetOracle) erased.main mainCode
      (CompilerFunctionRel
        (erased.addressed.addressedCtx
          (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
        (IxIR0.Env.ofList erased.declarations) finalState) := by
    apply lowerAllAction_semanticForwardSimulation_of_targetProgress_sealed
      henv hlower' htarget hrepresented hcontracts hexternValue
    intro _ _ _
    exact hfixedProgress
  intro legacyFuel legacyValue hlegacy
  exact lowerAllIndexedFullyAddressed_after_addressedErasure herase
    beforeOracle
    (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle)
    (IxIR0.Readdress.Oracle.readdress_compatible hreaddressable)
    hlower haddressed targetOracle hrawSimulation hlegacy

/-- Member-scoped production simulation used by validator-gated compilation.
The executable erasure certificate, simultaneous member coverage, and both
address-pass traces are exact; the ordinary compiler/extern contracts remain
the explicit semantic boundary. -/
theorem
    lowerAllIndexedFullyAddressed_semanticForwardSimulation_of_certificate_with_members_sealed
    [scope : Ix.Compiler.Sim.MemberScope]
    {ectx : Ixon.Eval.EvalCtx} {frame : Ixon.Eval.Frame}
    {source : Ixon.Expr} {sourceFuel certFuel : Nat}
    {sourceValue : Ixon.Eval.Value} {eraseCtx : Erase.EraseCtx}
    {constants : List (Address × Constant)} {programEraseFuel : Nat}
    {erased : EraseAddressed.Result}
    (beforeOracle : IxIR0.Oracle)
    (hmembers : Ix.Compiler.Sim.MemberCoverage ectx.inlineSharing
      (erased.rawCtx beforeOracle) scope.plan)
    (cert : Ix.Compiler.EraseValidator.CertifiedSharedExpr ectx
      (erased.rawCtx beforeOracle) none
      (Ix.Compiler.EraseValidator.tablesOfFrame frame)
      frame.selfAddr [] certFuel source)
    (herase : EraseAddressed.run eraseCtx constants cert.target
      programEraseFuel = .ok erased)
    (hreaddressable : IxIR0.Readdress.Oracle.Readdressable
      erased.addressMap beforeOracle)
    (horacles : Ix.Compiler.Sim.OracleRel ectx.inlineSharing
      (erased.rawCtx beforeOracle))
    (hctx : ectx.SharingWF) (hframe : frame.SharingWF)
    (hbelow : Ixon.Sharing.sharesBelow frame.sharing.size source = true)
    (hsource : Ixon.Eval.eval ectx sourceFuel frame [] source =
      .ok sourceValue)
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {lowered : IxIR1.ReaddressAll.Result}
    (hlower :
      (lowerAllIndexedAction erased.declarations erased.main mainWorld
        compilerFuel).run {} = .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllIndexedFullyAddressed erased.declarations erased.main mainWorld
        compilerFuel = .ok lowered)
    (targetOracle : Address → List RVal → Option RVal)
    (htarget : ∀ {targetAddress targetDecl},
      (targetAddress, targetDecl) ∈ raw →
      (lowered.preAddressCtx raw targetOracle).decls targetAddress =
        some targetDecl)
    (hrepresented : ExtraRepresented
      (lowered.preAddressCtx raw targetOracle) finalState)
    (hcontracts : CompilerContracts (IxIR0.Env.ofList erased.declarations)
      (lowered.preAddressCtx raw targetOracle))
    (hexternValue : ExternValueContract
      (CompilerFunctionRel
        (erased.addressed.addressedCtx
          (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
        (IxIR0.Env.ofList erased.declarations) finalState)
      (erased.addressed.addressedCtx
        (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
      (lowered.preAddressCtx raw targetOracle))
    (hexternProgress : ExternTraceProgressContract
      (CompilerFunctionRel
        (erased.addressed.addressedCtx
          (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
        (IxIR0.Env.ofList erased.declarations) finalState)
      (erased.addressed.addressedCtx
        (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
      (lowered.preAddressCtx raw targetOracle)) :
    MutualAddressedSemanticForwardSimulation
      (erased.addressed.preAddressCtx erased.groups beforeOracle)
      (lowered.addressedCtx targetOracle) cert.target lowered.main
      (IxIR0.MutualBlock.Renaming.apply erased.addressMap)
      (IxIR1.Readdress.Renaming.apply lowered.addressMap)
      (CompilerFunctionRel
        (erased.addressed.addressedCtx
          (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
        (IxIR0.Env.ofList erased.declarations) finalState) := by
  have hlower' :
      (lowerAllAction erased.declarations erased.main mainWorld
        compilerFuel).run {} = .ok (raw, mainCode) finalState := by
    simpa only [lowerAllIndexedAction_eq_lowerAllAction] using hlower
  have henv : (erased.addressed.addressedCtx
      (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle)).env =
      IxIR0.Env.ofList erased.declarations := rfl
  have hfixedProgress :=
    lowerAllIndexedAction_main_progress_of_addressed_certificate_with_members_sealed
      (targetCtx := lowered.preAddressCtx raw targetOracle)
      beforeOracle
      (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle)
      hmembers cert herase
      (IxIR0.Readdress.Oracle.readdress_compatible hreaddressable)
      horacles hctx hframe hbelow hsource hlower htarget hrepresented
      hcontracts hexternValue hexternProgress
  have hrawSimulation : SemanticForwardSimulation
      (erased.addressed.addressedCtx
        (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
      (lowered.preAddressCtx raw targetOracle) erased.main mainCode
      (CompilerFunctionRel
        (erased.addressed.addressedCtx
          (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
        (IxIR0.Env.ofList erased.declarations) finalState) := by
    apply lowerAllAction_semanticForwardSimulation_of_targetProgress_sealed
      henv hlower' htarget hrepresented hcontracts hexternValue
    intro _ _ _
    exact hfixedProgress
  intro legacyFuel legacyValue hlegacy
  exact lowerAllIndexedFullyAddressed_after_addressedErasure herase
    beforeOracle
    (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle)
    (IxIR0.Readdress.Oracle.readdress_compatible hreaddressable)
    hlower haddressed targetOracle hrawSimulation hlegacy

/-- Alias-free member-scoped progress for the exact production artifact.
The validator supplies progress in the literal raw declaration context, and
the certified rebuild map transports that successful run through complete
source/generated content addressing. -/
theorem
    lowerAllIndexedFullyAddressed_main_progress_of_addressed_certificate_with_members_exact_sealed
    [scope : Ix.Compiler.Sim.MemberScope]
    {ectx : Ixon.Eval.EvalCtx} {frame : Ixon.Eval.Frame}
    {source : Ixon.Expr} {sourceFuel certFuel : Nat}
    {sourceValue : Ixon.Eval.Value} {eraseCtx : Erase.EraseCtx}
    {constants : List (Address × Constant)} {programEraseFuel : Nat}
    {erased : EraseAddressed.Result}
    (beforeOracle : IxIR0.Oracle)
    (hmembers : Ix.Compiler.Sim.MemberCoverage ectx.inlineSharing
      (erased.rawCtx beforeOracle) scope.plan)
    (cert : Ix.Compiler.EraseValidator.CertifiedSharedExpr ectx
      (erased.rawCtx beforeOracle) none
      (Ix.Compiler.EraseValidator.tablesOfFrame frame)
      frame.selfAddr [] certFuel source)
    (herase : EraseAddressed.run eraseCtx constants cert.target
      programEraseFuel = .ok erased)
    (hreaddressable : IxIR0.Readdress.Oracle.Readdressable
      erased.addressMap beforeOracle)
    (horacles : Ix.Compiler.Sim.OracleRel ectx.inlineSharing
      (erased.rawCtx beforeOracle))
    (hctx : ectx.SharingWF) (hframe : frame.SharingWF)
    (hbelow : Ixon.Sharing.sharesBelow frame.sharing.size source = true)
    (hsource : Ixon.Eval.eval ectx sourceFuel frame [] source =
      .ok sourceValue)
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {lowered : IxIR1.ReaddressAll.Result}
    (hlower :
      (lowerAllIndexedAction erased.declarations erased.main mainWorld
        compilerFuel).run {} = .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllIndexedFullyAddressed erased.declarations erased.main mainWorld
        compilerFuel = .ok lowered)
    (targetOracle : Address → List RVal → Option RVal)
    (htarget : ∀ {targetAddress targetDecl},
      (targetAddress, targetDecl) ∈ raw →
      (lowered.rebuildSourceCtx raw targetOracle).decls targetAddress =
        some targetDecl)
    (hrepresented : ExtraRepresented
      (lowered.rebuildSourceCtx raw targetOracle) finalState)
    (hcontracts : CompilerContracts (IxIR0.Env.ofList erased.declarations)
      (lowered.rebuildSourceCtx raw targetOracle))
    (hexternValue : ExternValueContract
      (CompilerFunctionRel
        (erased.addressed.addressedCtx
          (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
        (IxIR0.Env.ofList erased.declarations) finalState)
      (erased.addressed.addressedCtx
        (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
      (lowered.rebuildSourceCtx raw targetOracle))
    (hexternProgress : ExternTraceProgressContract
      (CompilerFunctionRel
        (erased.addressed.addressedCtx
          (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
        (IxIR0.Env.ofList erased.declarations) finalState)
      (erased.addressed.addressedCtx
        (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
      (lowered.rebuildSourceCtx raw targetOracle)) :
    ∃ targetFuel store value,
      runMain (lowered.addressedCtx targetOracle) lowered.main targetFuel =
        .ok (store, value) := by
  obtain ⟨targetFuel, rawStore, targetValue, hraw⟩ :=
    lowerAllIndexedAction_main_progress_of_addressed_certificate_with_members_sealed
      (targetCtx := lowered.rebuildSourceCtx raw targetOracle)
      beforeOracle
      (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle)
      hmembers cert herase
      (IxIR0.Readdress.Oracle.readdress_compatible hreaddressable)
      horacles hctx hframe hbelow hsource hlower htarget hrepresented
      hcontracts hexternValue hexternProgress
  refine ⟨targetFuel,
    IxIR1.Readdress.Store.mapAddresses (lowered.rebuildRename raw) rawStore,
    targetValue, ?_⟩
  exact lowerAllIndexedFullyAddressed_runMain_exact_success
    hlower haddressed targetOracle hraw

/-- Alias-free member-scoped production simulation. All raw lowering
obligations are stated against the literal declaration environment, while the
certified rebuild map transports the successful evaluator run to the emitted
content-addressed graph. -/
theorem
    lowerAllIndexedFullyAddressed_semanticForwardSimulation_of_certificate_with_members_exact_sealed
    [scope : Ix.Compiler.Sim.MemberScope]
    {ectx : Ixon.Eval.EvalCtx} {frame : Ixon.Eval.Frame}
    {source : Ixon.Expr} {sourceFuel certFuel : Nat}
    {sourceValue : Ixon.Eval.Value} {eraseCtx : Erase.EraseCtx}
    {constants : List (Address × Constant)} {programEraseFuel : Nat}
    {erased : EraseAddressed.Result}
    (beforeOracle : IxIR0.Oracle)
    (hmembers : Ix.Compiler.Sim.MemberCoverage ectx.inlineSharing
      (erased.rawCtx beforeOracle) scope.plan)
    (cert : Ix.Compiler.EraseValidator.CertifiedSharedExpr ectx
      (erased.rawCtx beforeOracle) none
      (Ix.Compiler.EraseValidator.tablesOfFrame frame)
      frame.selfAddr [] certFuel source)
    (herase : EraseAddressed.run eraseCtx constants cert.target
      programEraseFuel = .ok erased)
    (hreaddressable : IxIR0.Readdress.Oracle.Readdressable
      erased.addressMap beforeOracle)
    (horacles : Ix.Compiler.Sim.OracleRel ectx.inlineSharing
      (erased.rawCtx beforeOracle))
    (hctx : ectx.SharingWF) (hframe : frame.SharingWF)
    (hbelow : Ixon.Sharing.sharesBelow frame.sharing.size source = true)
    (hsource : Ixon.Eval.eval ectx sourceFuel frame [] source =
      .ok sourceValue)
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {lowered : IxIR1.ReaddressAll.Result}
    (hlower :
      (lowerAllIndexedAction erased.declarations erased.main mainWorld
        compilerFuel).run {} = .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllIndexedFullyAddressed erased.declarations erased.main mainWorld
        compilerFuel = .ok lowered)
    (targetOracle : Address → List RVal → Option RVal)
    (htarget : ∀ {targetAddress targetDecl},
      (targetAddress, targetDecl) ∈ raw →
      (lowered.rebuildSourceCtx raw targetOracle).decls targetAddress =
        some targetDecl)
    (hrepresented : ExtraRepresented
      (lowered.rebuildSourceCtx raw targetOracle) finalState)
    (hcontracts : CompilerContracts (IxIR0.Env.ofList erased.declarations)
      (lowered.rebuildSourceCtx raw targetOracle))
    (hexternValue : ExternValueContract
      (CompilerFunctionRel
        (erased.addressed.addressedCtx
          (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
        (IxIR0.Env.ofList erased.declarations) finalState)
      (erased.addressed.addressedCtx
        (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
      (lowered.rebuildSourceCtx raw targetOracle))
    (hexternProgress : ExternTraceProgressContract
      (CompilerFunctionRel
        (erased.addressed.addressedCtx
          (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
        (IxIR0.Env.ofList erased.declarations) finalState)
      (erased.addressed.addressedCtx
        (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
      (lowered.rebuildSourceCtx raw targetOracle)) :
    MutualAddressedSemanticForwardSimulation
      (erased.addressed.preAddressCtx erased.groups beforeOracle)
      (lowered.addressedCtx targetOracle) cert.target lowered.main
      (IxIR0.MutualBlock.Renaming.apply erased.addressMap)
      (lowered.rebuildRename raw)
      (CompilerFunctionRel
        (erased.addressed.addressedCtx
          (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
        (IxIR0.Env.ofList erased.declarations) finalState) := by
  have hlower' :
      (lowerAllAction erased.declarations erased.main mainWorld
        compilerFuel).run {} = .ok (raw, mainCode) finalState := by
    simpa only [lowerAllIndexedAction_eq_lowerAllAction] using hlower
  have henv : (erased.addressed.addressedCtx
      (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle)).env =
      IxIR0.Env.ofList erased.declarations := rfl
  have hfixedProgress :=
    lowerAllIndexedAction_main_progress_of_addressed_certificate_with_members_sealed
      (targetCtx := lowered.rebuildSourceCtx raw targetOracle)
      beforeOracle
      (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle)
      hmembers cert herase
      (IxIR0.Readdress.Oracle.readdress_compatible hreaddressable)
      horacles hctx hframe hbelow hsource hlower htarget hrepresented
      hcontracts hexternValue hexternProgress
  have hrawSimulation : SemanticForwardSimulation
      (erased.addressed.addressedCtx
        (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
      (lowered.rebuildSourceCtx raw targetOracle) erased.main mainCode
      (CompilerFunctionRel
        (erased.addressed.addressedCtx
          (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle))
        (IxIR0.Env.ofList erased.declarations) finalState) := by
    apply lowerAllAction_semanticForwardSimulation_of_targetProgress_sealed
      henv hlower' htarget hrepresented hcontracts hexternValue
    intro _ _ _
    exact hfixedProgress
  intro legacyFuel legacyValue hlegacy
  exact lowerAllIndexedFullyAddressed_exact_after_addressedErasure herase
    beforeOracle
    (IxIR0.Readdress.Oracle.readdress erased.addressMap beforeOracle)
    (IxIR0.Readdress.Oracle.readdress_compatible hreaddressable)
    hlower haddressed targetOracle hrawSimulation hlegacy

end Ix.Compiler.IxIR1.LowerSim
