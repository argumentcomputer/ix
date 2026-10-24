import Tests.Ix.AuxGen.GenerationOnlySpike
import Tests.Ix.AuxGen.NestedTailReference

namespace Tests.Ix.AuxGen.GenerationOnlySpike

open _root_.Ix _root_.Ix.AuxGen
open Tests.Ix.AuxGen.BelowIxc (tailArgs runIn stateKey planted)

private def need (condition : Bool) (why : String) : IO Unit :=
  unless condition do throw (IO.userError why)

private def isError (r : Except ε α) : Bool := match r with | .error _ => true | _ => false

def runTail (cenv : CompileM.CompileEnv) (lo : Name) (members : Array Name) (o : AuxOracle)
    (retry : Bool := false) : Except String (((Option Ixon.AuxLayout × AuxTailRecs) × AuxKernelCtx) × CompileM.BlockState) :=
  runIn cenv lo do
    let some (cs, sorted, addr, maps) ← tailArgs lo members
      | throw (.unsupportedExpr "spike: tail unavailable")
    if retry then CompileM.runAuxTail lo cs sorted addr maps (.ixc maps o)
    else (compileMutualAuxTail cs sorted addr maps (.ixc maps o)).run AuxKernelCtx.new

def sameTail (a b : ((Option Ixon.AuxLayout × AuxTailRecs) × AuxKernelCtx) × CompileM.BlockState) : Bool :=
  a.1.1.1 == b.1.1.1 && a.1.1.2.recs == b.1.1.2.recs && a.1.1.2.belowRecs == b.1.1.2.belowRecs &&
    a.2.auxConsts.map (fun (_, c) => Ixon.serConstant c) == b.2.auxConsts.map (fun (_, c) => Ixon.serConstant c) &&
    a.2.auxNamed == b.2.auxNamed && stateKey a.2 == stateKey b.2

def evaluate : IO Unit := do
  let leanEnv ← getCompileEnv #[`Tests.Ix.Compile.AuxCert.NestedSortUK]
  let env ← Tests.Ix.Kernel.SourceIngress.envOf leanEnv #[`NestedSortUK.T, `NestedSortUK.t_rec]
  let owner := Name.fromLeanName `NestedSortUK.T
  let dependent := Name.fromLeanName `NestedSortUK.t_rec
  let blockedAlias := owner.mkStr "_blocked_generation_control"
  let some (.thmInfo theoremVal) := env.get? dependent | throw (IO.userError "fixture theorem missing")
  let plantedDef : DefinitionVal := {
    cnst := { theoremVal.cnst with name := blockedAlias }
    value := Expr.mkConst dependent (theoremVal.cnst.levelParams.map Level.mkParam)
    hints := .abbrev, safety := .safe, all := #[blockedAlias] }
  let env := { env with consts := env.consts.insert blockedAlias (.defnInfo plantedDef) }
  let blocks := Tests.Ix.Kernel.SourceIngressStep.condense env
  let pre ← IO.ofExcept (Ix.Kernel.Reader.builtinPrelude.mapError IO.userError)
  let svc := (Source.Service.create pre env blocks (evidence := some (Ix.RoleEvidence.bundleEvidence ()))).ensureNames #[owner, dependent, blockedAlias]
  let some why := Ixc.blockStatus? svc #[owner] | throw (IO.userError "T unexpectedly Source-accepted")
  need ((why.splitOn "small eliminator on a non-Prop block").length == 2) s!"wrong Source reason: {why}"
  need ((svc.statusOf? dependent).any (fun | .blocked _ => true | _ => false)) "fixture dependent is not fenced"
  need ((svc.statusOf? blockedAlias).any (fun | .blocked _ => true | _ => false)) "planted safe alias is not fenced"
  let gen ← IO.ofExcept (start svc owner)
  need (gen.reason == why && Ixc.blockStatus? gen.baseline #[owner] == some why) "Source refusal changed"
  need ((gen.env.fold.fe.find? (Ix.LeanIngress.ingressKey owner)).isNone) "generation leaked T into logical fold"
  need ((gen.env.answers.find? (gen.env.key owner)).isSome) "generation answer view lacks T"
  need (gen.env.fold.pos == svc.env.fold.pos && gen.baseline.entries.map (·.status) == svc.entries.map (·.status)) "logical state advanced"
  let some (.inductive types ctors recs) := svc.input.blockGroupOf? owner | throw (IO.userError "original group missing")
  need (recs.size == 2) "expected provided rec and rec_1"
  let some record := recs[0]? | throw (IO.userError "provided recursor missing")
  let some firstType := types[0]? | throw (IO.userError "provided former missing")
  let params := record.cnst.levelParams
  let levels := params.map Level.mkParam
  let value := Expr.mkConst record.cnst.name levels
  let aliasName := owner.mkStr "_generation_alias"
  let uninstalled : Generation := ⟨svc, svc.env.tier, svc.env.sigma, why⟩
  match uninstalled.definition aliasName params record.cnst.type value false with
  | .error e => need (e.startsWith "generation: unaccepted dependency NestedSortUK.T") s!"wrong dependency refusal: {e}"
  | .ok _ => throw (IO.userError "unaccepted dependency was allowed before its checked install")
  match start svc (Name.fromLeanName `NestedSortUK.Box) with
  | .error e => need (e == "generation: Source-accepted block is ineligible") s!"wrong accepted-block refusal: {e}"
  | .ok _ => throw (IO.userError "Source-accepted block entered generation retry")
  let broken := recs.modify 0 fun r => { r with rules := r.rules.modify 0 fun rule => { rule with rhs := Expr.mkLit (.natVal 7) } }
  let malformed := do
    let b ← (Ix.LeanIngress.convertTierInductive types ctors broken).mapError Source.renderRead
    svc.env.installTierInd b
  match malformed with
  | .error e => need (e == "invalid: function expected") s!"wrong invalid-record refusal: {e}"; IO.println s!"invalid-record control: {e}"
  | .ok _ => throw (IO.userError "a mistyped supplied recursor rule passed")
  let baseOracle := oracle .failClosed gen 8
  let (afterBelow, ok, bad) ← IO.ofExcept (baseOracle.admitBelow #[⟨aliasName, params, record.cnst.type, value, false⟩])
  need (ok == 1 && bad == 0 && afterBelow.blockStatus () == some why) "below install lost generation-only policy"
  let (reduced, _) ← IO.ofExcept (do let s ← afterBelow.newScope params #[]; s.whnf (Expr.mkConst aliasName levels))
  need (Ix.Compile.ExactKey.exprEq reduced value) "typed generated alias did not unfold"
  let (_, rows) ← IO.ofExcept (afterBelow.admit #[.defn (owner.mkStr "_generation_alias2") params record.cnst.type (Expr.mkConst aliasName levels) false])
  need (rows.size == 1 && rows.all (·.2.isSome)) "generation admit reported logical acceptance"
  let (_, familyRows) ← IO.ofExcept (baseOracle.admit #[.family (types.zip ctors) (recs.map fun r => (r.cnst.name, r))])
  need (familyRows.size == types.size && familyRows.all (·.2.isSome)) "family install reported logical acceptance"
  let familyName := owner.mkStr "_generation_prop"
  let ctorName := familyName.mkStr "mk"
  let p : InductiveVal := { cnst := ⟨familyName, params, Expr.mkSort Level.mkZero⟩, numParams := 0, numIndices := 0, all := #[familyName], ctors := #[ctorName], numNested := 0, isRec := false, isUnsafe := false, isReflexive := false }
  let ct : ConstructorVal := { cnst := ⟨ctorName, params, Expr.mkConst familyName levels⟩, induct := familyName, cidx := 0, numParams := 0, numFields := 0, isUnsafe := false }
  let bare ← IO.ofExcept (baseOracle.withFamily #[(p, #[ct])])
  let _ ← IO.ofExcept (do let s ← bare.newScope params #[]; s.infer (Expr.mkConst ctorName levels))
  need (bare.blockStatus () == some why) "bare family lost original refusal"
  let flat ← IO.ofExcept (baseOracle.withFlat (types.map fun v => #[v.cnst.name]) firstType.all (recs.map fun r => (r.cnst.name, r)))
  need flat.isNone "unchanged Lean layout unexpectedly installed a flat block"
  let alternate := (owner.mkStr "_generationNested").mkStr "rec"
  let renamed := recs.mapIdx fun i r =>
    let n := if i == 1 then alternate else r.cnst.name
    (n, { r with cnst := { r.cnst with name := n } })
  let changed ← IO.ofExcept (baseOracle.withFlat (types.map fun v => #[v.cnst.name]) firstType.all renamed)
  let some next := changed | throw (IO.userError "renamed auxiliary did not exercise flat installation")
  need (next.blockStatus () == some why) "flat install lost original refusal"
  let _ ← IO.ofExcept (do let s ← next.newScope params #[]; s.infer (Expr.mkConst alternate levels))
  IO.println "callback controls: checked below/definition/family/bare and actual renamed-aux flat install; logical fold and statuses retained"
  let (_, _, cenv) ← IO.ofExcept (← IO.lazyPure fun _ => CompileM.compileEnvFold env blocks (width := 4))
  need cenv.ungrounded.isEmpty "baseline fixture compile failed"
  let some (lo, members) := (Tests.Ix.AuxGen.FlatBlockSource.inductiveBlocks env blocks).find?
    (fun (_, ms) => ms.any (Ix.Compile.ExactKey.nameEq · owner)) | throw (IO.userError "T block missing")
  let original (mode : IxcMode) := Ixc.oracleOf mode false { members, recursors := true, lookup := env.get? } none 8 (fun _ => .ok svc)
  -- The captured original shadow had three refusals; the complete old
  -- output remains the reference. Live checked queries must all succeed.
  let retryOracle := original .failClosed
  let cenv := { cenv with auxGenerationRetry := some (fun _ => .ok baseOracle) }
  let fresh ← IO.ofExcept (← IO.lazyPure fun _ => runTail cenv lo members retryOracle true)
  let st := fresh.1.2.ixcStats
  need (st.recWhnf == 8 && st.recRefused == 0 && [st.refused, st.scopesRefused, st.flatRefused,
    st.leanRecDiffer, st.belowRefused, st.elimRefused, st.familyRefused].all (· == 0)) "checked generation coverage/refusal changed"
  need (fresh.2.auxReport.retried == some why) "generation retry lost rollback reason"
  need (fresh.1.2.generated.size == 2 && fresh.1.2.admitted.size == fresh.1.2.generated.size) "exemption coverage differs/incomplete"
  need (fresh.1.2.admitted.all fun (_, v) => v == .exempt s!"{AuxTable.notAcceptedPrefix}{why}") "a generation-only row was accepted"
  let direct ← IO.ofExcept (← IO.lazyPure fun _ => runTail cenv lo members baseOracle)
  need (sameTail fresh direct) "checked direct/retry output differs"
  IO.ofExcept (NestedTailReference.check 0 #[`Tests.Ix.Compile.AuxCert.NestedSortUK] #[`NestedSortUK.T, `NestedSortUK.t_rec]
    (some blockedAlias) env blocks lo members why fresh direct)
  IO.println "nested tail reference: controls-planted-alias binding, full output and rollback passed"
  let stopped := runTail cenv lo members (planted retryOracle none) true
  need (isError stopped) "accepted-block refusal used the generation retry"
  match stopped with
  | .error e => need ((e.splitOn "accepted by Source mode").length == 2) "accepted failure lost named cause"
  | _ => pure ()
  IO.println s!"historical capture recRefused=3; checked generation {Tests.Ix.AuxGen.BelowIxc.checkedStatsLine st}"
  IO.println s!"retry: {fresh.1.2.generated.size} generated/exempt rows, exact bytes/metadata/recursors"
  IO.println s!"Source retained: {why}; actual and planted dependents remain blocked"

end Tests.Ix.AuxGen.GenerationOnlySpike
