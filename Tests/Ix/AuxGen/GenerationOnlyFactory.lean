import Ix.AuxGen.GenerationOnly
import Tests.Ix.AuxGen.GenerationOnlyControls

#check_failure Ix.AuxGen.GenerationOnly.Context
#check_failure Ix.AuxGen.GenerationOnly.start
#check_failure Ix.AuxGen.GenerationOnly.oracle

namespace Tests.Ix.AuxGen.GenerationOnlyFactory

open _root_.Ix _root_.Ix.AuxGen
open Tests.Ix.AuxGen.GenerationOnlySpike (runTail sameTail)

private def need (condition : Bool) (why : String) : IO Unit :=
  unless condition do throw (IO.userError why)

private def policy (o : AuxOracle) (why : String) : Bool :=
  o.mode == .failClosed && o.recursors && o.retry.isNone && o.blockStatus () == some why

def evaluate : IO Unit := do
  let leanEnv ← getCompileEnv #[`Tests.Ix.Compile.AuxCert.NestedSortUK]
  let env ← Tests.Ix.Kernel.SourceIngress.envOf leanEnv #[`NestedSortUK.T, `NestedSortUK.t_rec]
  let owner := Name.fromLeanName `NestedSortUK.T
  let dependent := Name.fromLeanName `NestedSortUK.t_rec
  let blocks := Tests.Ix.Kernel.SourceIngressStep.condense env
  let pre ← IO.ofExcept (Ix.Kernel.Reader.builtinPrelude.mapError IO.userError)
  let svc := (Source.Service.create pre env blocks (evidence := some (Ix.RoleEvidence.bundleEvidence ()))).ensureNames #[owner, dependent]
  let some why := Ixc.blockStatus? svc #[owner] | throw (IO.userError "missing Source refusal")
  let actual ← IO.ofExcept (GenerationOnly.ofService svc owner)
  need (policy actual why && !actual.trace) "factory did not fix failClosed/exempt policy"
  let some (.inductive types ctors recs) := svc.input.blockGroupOf? owner | throw (IO.userError "original group missing")
  let some record := recs[0]? | throw (IO.userError "original recursor missing")
  let some firstType := types[0]? | throw (IO.userError "original former missing")
  let lps := record.cnst.levelParams
  let levels := lps.map Level.mkParam
  let value := Expr.mkConst record.cnst.name levels
  let aliasName := owner.mkStr "_factory_alias"
  let (afterBelow, ok, bad) ← IO.ofExcept (actual.admitBelow #[⟨aliasName, lps, record.cnst.type, value, false⟩])
  need (ok == 1 && bad == 0 && policy afterBelow why) "below successor changed policy"
  let (result, _) ← IO.ofExcept ((afterBelow.newLazyScope (fun _ => none) lps #[]).whnf (Expr.mkConst aliasName levels))
  need (Ix.Compile.ExactKey.exprEq result value) "lazy successor cannot unfold checked alias"
  let (afterDef, rows) ← IO.ofExcept (afterBelow.admit #[.defn (owner.mkStr "_factory_alias2") lps record.cnst.type (Expr.mkConst aliasName levels) false])
  need (policy afterDef why && rows == #[(owner.mkStr "_factory_alias2", some why)]) "definition successor accepted a row"
  let (afterFamily, familyRows) ← IO.ofExcept (actual.admit #[.family (types.zip ctors) (recs.map fun r => (r.cnst.name, r))])
  need (policy afterFamily why && familyRows.all (·.2 == some why)) "family successor changed policy"
  let alternate := (owner.mkStr "_factoryNested").mkStr "rec"
  let renamed := recs.mapIdx fun i r =>
    let n := if i == 1 then alternate else r.cnst.name
    (n, { r with cnst := { r.cnst with name := n } })
  let some afterFlat ← IO.ofExcept (actual.withFlat (types.map fun v => #[v.cnst.name]) firstType.all renamed)
    | throw (IO.userError "positive flat callback was not exercised")
  need (policy afterFlat why) "flat successor changed policy"
  let _ ← IO.ofExcept (do let s ← afterFlat.newScope lps #[]; s.infer (Expr.mkConst alternate levels))
  let familyName := owner.mkStr "_factory_prop"
  let ctorName := familyName.mkStr "mk"
  let p : InductiveVal := { cnst := ⟨familyName, lps, Expr.mkSort Level.mkZero⟩, numParams := 0, numIndices := 0, all := #[familyName], ctors := #[ctorName], numNested := 0, isRec := false, isUnsafe := false, isReflexive := false }
  let ct : ConstructorVal := { cnst := ⟨ctorName, lps, Expr.mkConst familyName levels⟩, induct := familyName, cidx := 0, numParams := 0, numFields := 0, isUnsafe := false }
  let afterBare ← IO.ofExcept (actual.withFamily #[(p, #[ct])])
  need (policy afterBare why) "bare successor changed policy"
  let _ ← IO.ofExcept (do let s ← afterBare.newScope lps #[]; s.infer (Expr.mkConst ctorName levels))
  match GenerationOnly.ofService svc (Name.fromLeanName `NestedSortUK.Box) with
  | .error e => need (e == "generation: Source-accepted block is ineligible") s!"wrong accepted-block error: {e}"
  | .ok _ => throw (IO.userError "accepted block entered generation")
  let badRecord := { record with rules := record.rules.modify 0 fun rule => { rule with rhs := Expr.mkLit (.natVal 7) } }
  let badLookup (n : Name) : Option ConstantInfo :=
    if Ix.Compile.ExactKey.nameEq n record.cnst.name then some (.recInfo badRecord) else svc.input.get? n
  let malformed : Source.Service := { svc with input := { svc.input with get? := badLookup } }
  match GenerationOnly.ofService malformed owner with
  | .error e => need (e == "invalid: function expected") s!"wrong malformed-record error: {e}"
  | .ok _ => throw (IO.userError "malformed record entered generation")
  let some (.thmInfo theoremVal) := env.get? dependent | throw (IO.userError "dependent theorem missing")
  match actual.admit #[.defn (owner.mkStr "_blocked_factory") theoremVal.cnst.levelParams theoremVal.cnst.type
      (Expr.mkConst dependent (theoremVal.cnst.levelParams.map Level.mkParam)) false] with
  | .error e => need (e == "generation: unaccepted dependency NestedSortUK.t_rec") s!"wrong dependency error: {e}"
  | .ok _ => throw (IO.userError "blocked dependency entered generation")
  let exhausted ← IO.ofExcept (GenerationOnly.ofService svc owner 0 true)
  need (policy exhausted why && exhausted.trace) "exhausted oracle lost original reason"
  match exhausted.newScope #[] #[] with
  | .error e => need (e == "generation oracle fuel exhausted") "wrong fuel error"
  | .ok _ => throw (IO.userError "zero fuel opened a scope")
  let (_, _, cenv) ← IO.ofExcept (← IO.lazyPure fun _ => CompileM.compileEnvFold env blocks (width := 4))
  need cenv.ungrounded.isEmpty "baseline compile failed"
  let some (lo, members) := (Tests.Ix.AuxGen.FlatBlockSource.inductiveBlocks env blocks).find?
    (fun (_, ms) => ms.any (Ix.Compile.ExactKey.nameEq · owner)) | throw (IO.userError "T block missing")
  let original := Ixc.oracleOf .failClosed false { members, recursors := true, lookup := env.get? } none 8 (fun _ => .ok svc)
  let frozen ← IO.ofExcept (Tests.Ix.AuxGen.GenerationOnlySpike.start svc owner)
  let expected ← IO.ofExcept (← IO.lazyPure fun _ => runTail
    { cenv with auxGenerationRetry := some (fun _ => .ok (Tests.Ix.AuxGen.GenerationOnlySpike.oracle .failClosed frozen 8)) }
    lo members original true)
  let observed ← IO.ofExcept (← IO.lazyPure fun _ => runTail
    { cenv with auxGenerationRetry := some (fun _ => .ok actual) } lo members original true)
  need (sameTail expected observed && observed.1.2.admitted == expected.1.2.admitted &&
    observed.2.auxReport.retried == some why && observed.1.2.generated.size == 2) "factory changed actual retry output/verdicts"
  need (observed.1.2.scopeEpoch == 0 && observed.1.2.ingressCache.isEmpty && observed.1.2.tcState.env.consts.isEmpty) "factory retry used legacy scope"
  need ((svc.statusOf? dependent).any (fun | .blocked _ => true | _ => false)) "dependent fence changed"
  IO.println "factory: fixed failClosed/private capability; all callback successors retain refusal; exact negative errors; actual retry equals frozen spike (2 exempt rows)"

end Tests.Ix.AuxGen.GenerationOnlyFactory
