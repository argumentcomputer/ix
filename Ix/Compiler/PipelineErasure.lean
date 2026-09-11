import Ix.Compiler.Pipeline
import Ix.Compiler.Ixon.RecursorUsage

/-!
# Certified erasure of an explicit closed entry

The original compiler keeps its reference-entry and v0 usage interfaces.
This separate entry accepts a closed expression and retains its reconstructed
ownership result before selecting an ownership lowering policy. The strict
eraser, sharing-aware validator, member coverage, and extern boundary are the
same ones used by the ordinary validated compiler.
-/

namespace Ix.Compiler.Pipeline

open Ix.Compiler.Ixon (Address Constant Owned)

structure ClosedEntry where
  refs : Array Address
  univs : Array Ixon.Univ := #[]
  source : Ixon.Expr

def ClosedEntry.frame (entry : ClosedEntry) : Ixon.Eval.Frame :=
  { refs := entry.refs, univs := entry.univs }

theorem ClosedEntry.frameSharingWF (entry : ClosedEntry) : entry.frame.SharingWF := by
  constructor
  · rfl
  · intro index member hget
    simp [ClosedEntry.frame] at hget

inductive UsagePolicy where
  | v0
  | saturatedRecursorV1
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

def UsagePolicy.tag : UsagePolicy → String
  | .v0 => "usage/0"
  | .saturatedRecursorV1 => Ixon.RecursorUsage.policyTag

def UsagePolicy.checkConstant (policy : UsagePolicy)
    (resolve : Address → Option Constant) (constant : Constant) (fuel : Nat) :=
  match policy with
  | .v0 => Ixon.UsageCheck.checkConstant resolve constant fuel
  | .saturatedRecursorV1 => Ixon.RecursorUsage.checkConstant resolve constant fuel

private def checkConstants (policy : UsagePolicy)
    (resolve : Address → Option Constant) (fuel : Nat) :
    (constants : List (Address × Constant)) → Except Error (PLift
      (∀ pair ∈ constants, policy.checkConstant resolve pair.2 fuel = .ok ()))
  | [] => .ok ⟨by simp⟩
  | pair :: rest => do
      match hc : policy.checkConstant resolve pair.2 fuel with
      | .error error => throw (.usage pair.1 error)
      | .ok _ =>
          let checked ← checkConstants policy resolve fuel rest
          return ⟨by
            intro item hitem
            rcases List.mem_cons.mp hitem with heq | hrest
            · subst item; exact hc
            · exact checked.down item hrest⟩

def ClosedEntry.usageContext (constants : List (Address × Constant))
    (entry : ClosedEntry) : Ixon.UsageCheck.CheckCtx :=
  { resolve := (ResolverIndex.ofList constants).resolve, refs := entry.refs }

structure CertifiedErasure (constants : List (Address × Constant))
    (entry : ClosedEntry) (config : Config) (policy : UsagePolicy)
    (world : Owned) (checkFuel eraseFuel : Nat) where
  usage : ∀ pair ∈ constants, policy.checkConstant
    (ResolverIndex.ofList constants).resolve pair.2 checkFuel = .ok ()
  entryUsage : Ixon.UsageCheck.check (entry.usageContext constants) checkFuel
    false [] entry.source = .ok ([], world)
  entrySharesBelow : Ixon.Sharing.sharesBelow 0 entry.source = true
  memberScope : Sim.MemberScope
  rawMain : IxIR0.Expr
  erasure : EraseAddressed.RunTrace
    (EraseValidator.eraseCtxOf (validatedEvalCtx constants config))
    constants rawMain eraseFuel
  certificate : @EraseValidator.CertifiedSharedExpr
    (validatedEvalCtx constants config)
    { env := IxIR0.Env.ofList erasure.result.raw }
    none (EraseValidator.tablesOfFrame entry.frame) entry.frame.selfAddr []
    eraseFuel entry.source memberScope
  entryTarget : certificate.target = rawMain
  members : Sim.MemberCoverage (validatedEvalCtx constants config).inlineSharing
    { env := IxIR0.Env.ofList erasure.result.raw } memberScope.plan
  strict : (validatedEvalCtx constants config).Strict
  externsRejected : ValidatedExternsRejected erasure.result.declarations

private def certifyErasureCore [Sim.MemberScope]
    (constants : List (Address × Constant)) (entry : ClosedEntry)
    (config : Config) (policy : UsagePolicy) (world : Owned)
    (checkFuel eraseFuel validateFuel : Nat) :
    Except Error (CertifiedErasure constants entry config policy world checkFuel eraseFuel) := do
  let stats ← preflightValidated config.limits constants checkFuel eraseFuel validateFuel 0
  let entryUnits := Ixon.Work.exprUnits entry.source + entry.refs.size + entry.univs.size
  let enforce := fun metric actual limit => (Ixon.Work.ensure metric actual limit).mapError Error.resource
  enforce .programExpressionUnits (stats.expressionUnits + entryUnits) config.limits.maxExpressionUnits
  enforce .programExpandedExpressionUnits (stats.expandedExpressionUnits + entryUnits)
    config.limits.maxExpandedExpressionUnits
  enforce .layer1NodeVisits (stats.layer1NodeVisits + entryUnits) config.limits.maxLayer1NodeVisits
  enforce .certificateCandidates (stats.certificateCandidates + 1) config.limits.maxCertificateCandidates
  enforce .certificateValidationAttempts (stats.certificateValidationAttempts + 1)
    config.limits.maxCertificateValidationAttempts
  enforce .certificateSourceNodeWork
    (stats.certificateSourceNodeWork + stats.expandedExpressionUnits + entryUnits)
    config.limits.maxCertificateSourceNodeWork
  let diagnostic := entry.refs[0]?.getD (Address.replicate 0)
  let usage ← checkConstants policy (ResolverIndex.ofList constants).resolve checkFuel constants
  let entryUsage : PLift (Ixon.UsageCheck.check (entry.usageContext constants)
      checkFuel false [] entry.source = .ok ([], world)) ←
    match hu : Ixon.UsageCheck.check (entry.usageContext constants) checkFuel false [] entry.source with
    | .error error => throw (.usage diagnostic error)
    | .ok ([], actual) =>
        if hw : actual = world then pure ⟨by simpa [hw] using hu⟩
        else throw (.validate diagnostic "closed entry has a different ownership result")
    | .ok (_ :: _, _) => throw (.validate diagnostic "closed entry has free runtime variables")
  let below : PLift (Ixon.Sharing.sharesBelow 0 entry.source = true) ←
    if hb : Ixon.Sharing.sharesBelow 0 entry.source then pure ⟨hb⟩
    else throw (.validate diagnostic "closed entry contains an unresolved share")
  let ectx := validatedEvalCtx constants config
  let eraseCtx := EraseValidator.eraseCtxOf ectx
  let rawMain ← (Erase.eraseExpr eraseCtx eraseFuel (EraseValidator.tablesOfFrame entry.frame)
    [] entry.source).mapError Error.erase
  let erasure ← match EraseAddressed.runWithTrace eraseCtx constants rawMain eraseFuel with
    | .ok trace => pure trace
    | .error (.erase error) => throw (.erase error)
    | .error (.readdress message) => throw (.readdress message)
  let boundary : PLift (ValidatedExternsRejected erasure.result.declarations) ←
    match hb : firstValidatedExtern? erasure.result.declarations with
    | none => pure ⟨hb⟩
    | some address => throw (.validate address "validated extern ownership ABI rejects this declaration")
  let ictx : IxIR0.Ctx := { env := IxIR0.Env.ofList erasure.result.raw }
  let candidates := constants.filterMap fun pair => match pair.2.info with
    | .muts _ => none
    | _ => some pair.1
  let order ← (coveragePlan ectx.inlineSharing ictx validateFuel (candidates.length + 1)
    [] [] candidates).mapError fun (address, message) => Error.validate address message
  let program ← match EraseValidator.certifySharedProgram ectx constants order eraseFuel validateFuel with
    | .ok cert => pure cert
    | .error (.erase error) => throw (.erase error)
    | .error (.relation message) => throw (.validate diagnostic message)
  if ht : program.target == erasure.result.raw then
    have htEq : program.target = erasure.result.raw := beq_iff_eq.mp ht
    let coverage : EraseValidator.CoverageDB ectx.inlineSharing ictx := by
      simpa [ictx] using htEq ▸ program.coverage
    let certificate ← match EraseValidator.certifySharedClosedExpr ectx ictx coverage.oracle
        entry.frame entry.source eraseFuel validateFuel with
      | .ok cert => pure cert
      | .error (.erase error) => throw (.erase error)
      | .error (.relation message) => throw (.validate diagnostic message)
    if he : certificate.target == rawMain then
      have hstrict := program.members.strict
      let members : Sim.MemberCoverage ectx.inlineSharing ictx
          (inferInstance : Sim.MemberScope).plan := by
        have hm := program.members
        rw [htEq] at hm
        exact hm
      pure
        { usage := usage.down, entryUsage := entryUsage.down
          entrySharesBelow := below.down, memberScope := inferInstance
          rawMain, erasure, certificate, entryTarget := beq_iff_eq.mp he, members
          strict :=
            { neutralElims := by simpa using hstrict.neutralElims
              stringLiterals := by simpa using hstrict.stringLiterals }
          externsRejected := boundary.down }
    else throw (.validate diagnostic "certified closed entry differs from the compiled expression")
  else throw (.validate diagnostic "certified erasure differs from the compiled erasure")

/-- Independently usable source/erasure stage. A later compiler must consume
this exact certificate and source-derived result world. -/
def certifyErasure (constants : List (Address × Constant)) (entry : ClosedEntry)
    (config : Config := {}) (policy : UsagePolicy := .v0) (world : Owned := .shared)
    (checkFuel : Nat := 1000) (eraseFuel : Nat := 1000) (validateFuel : Nat := 1000) :
    Except Error (CertifiedErasure constants entry config policy world checkFuel eraseFuel) :=
  letI : Sim.MemberScope := { plan := programMemberPlan constants }
  certifyErasureCore constants entry config policy world checkFuel eraseFuel validateFuel

theorem CertifiedErasure.sourceRefines
    {constants : List (Address × Constant)} {entry : ClosedEntry} {config : Config}
    {policy : UsagePolicy} {world : Owned} {checkFuel eraseFuel : Nat}
    (compilation : CertifiedErasure constants entry config policy world checkFuel eraseFuel)
    {sourceFuel : Nat} {sourceValue : Ixon.Eval.Value}
    (horacles : @Sim.OracleRel compilation.memberScope
      (validatedEvalCtx constants config).inlineSharing
      { env := IxIR0.Env.ofList compilation.erasure.result.raw })
    (hctx : (validatedEvalCtx constants config).SharingWF)
    (hsource : Ixon.Eval.eval (validatedEvalCtx constants config) sourceFuel entry.frame []
      entry.source = .ok sourceValue) :
    ∃ targetFuel targetValue,
      IxIR0.eval { env := IxIR0.Env.ofList compilation.erasure.result.raw }
        targetFuel [] compilation.rawMain = .ok targetValue ∧
      @Sim.InlinedValRel (validatedEvalCtx constants config)
        { env := IxIR0.Env.ofList compilation.erasure.result.raw }
        sourceValue targetValue compilation.memberScope := by
  letI : Sim.MemberScope := compilation.memberScope
  have hinlined := Ixon.Eval.eval_inlineSharing hctx entry.frameSharingWF .nil
    compilation.entrySharesBelow hsource
  have hentry := compilation.certificate.related
  rw [EraseValidator.inlineTables_tablesOfFrame] at hentry
  obtain ⟨fuel, value, heval, hrelated⟩ := Sim.erasure_sim_with_members
    compilation.members horacles hinlined.1 hentry (by
      simpa [Ixon.Eval.valuesInlineSharing] using
        (Sim.EnvRel.nil (ectx := (validatedEvalCtx constants config).inlineSharing)
          (ictx := { env := IxIR0.Env.ofList compilation.erasure.result.raw })
          (refs := entry.frame.inlineSharing.refs) (muts := entry.frame.inlineSharing.selfMuts)
          (sa := entry.frame.inlineSharing.selfAddr)))
  rw [compilation.entryTarget] at heval
  exact ⟨fuel, value, heval, hrelated⟩

end Ix.Compiler.Pipeline
