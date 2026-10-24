import LSpec
import Ix.Meta
import Ix.PrimAddrs
import Ix.CompileDriver
import Tests.Ix.Kernel.SourceIngress

namespace Tests.Ix.Compile.BridgePortable
open LSpec
open _root_.Ix _root_.Ix.AuxGen

private def fixture (s : String) := Name.fromLeanName (`Tests.Ix.Compile.BridgePortableFixtures ++ s.toName)
private def nm (s : String) := Name.mkStr .mkAnon s
private def cn (s : String) := Expr.mkConst (fixture s) #[]
private def type0 := Expr.mkSort (.mkSucc .mkZero)
private def polyLeft := Expr.mkApp (Expr.mkConst (fixture "Poly") #[.mkSucc .mkZero]) (cn "Left")
private def localDecl (s : String) (t : Expr) : LocalDecl := ⟨nm s, nm s, t, .default⟩
private def need (ok : Bool) (why : String) : IO Unit := unless ok do throw (IO.userError why)
private def require (ok : Bool) (why : String) : KBridgeM Unit :=
  unless ok do throw (.unsupportedExpr s!"portable bridge: {why}")
private def same (a b : Expr) := Compile.ExactKey.exprEq a b
private def capture (action : KBridgeM α) : KBridgeM String := do
  let result ← try do discard action; pure none catch e => pure (some (toString e))
  let some e := result | throw (.unsupportedExpr "portable bridge: expected refusal succeeded")
  return e
private def refused (r : Except String α) : Except String String := do
  match r with | .error e => return e | .ok _ => throw "portable bridge: expected egress refusal succeeded"
private def run (env : Environment) (action : KBridgeM α) : Except String (α × AuxKernelCtx) :=
  ((CompileM.CompileM.run (CompileM.CompileEnv.new env)
    { all := {}, current := fixture "NatAlias", mutCtx := default, univCtx := [] } {}
    (action.run AuxKernelCtx.new)).map (·.1)).mapError toString
private def scope (k : AuxKernel) (locals : Array LocalDecl := #[]) (levels : Array Name := #[])
    (route : AuxRoute := .below) (overlay : Name → Option ConstantInfo := fun _ => none) : KBridgeM AuxScope := do
  let s ← AuxScope.new k locals levels (route := route) (overlay := overlay)
  require (s.backend matches .ixc _) "scope selected a legacy backend"
  return s

private def prepare : IO (Environment × Source.Service × AuxKernel) := do
  let moduleName := `Tests.Ix.Compile.BridgePortableFixtures
  let leanEnv ← getCompileEnv #[moduleName]
  let some moduleIndex := leanEnv.getModuleIdx? moduleName | throw (IO.userError "runtime fixture absent")
  let labels := #["NatAlias", "Left", "Right", "Ambient", "Poly"]
  let roots := labels.map fixture
  let env ← Tests.Ix.Kernel.SourceIngress.envOf leanEnv (labels.map (moduleName ++ ·.toName))
  let pre ← IO.ofExcept (Kernel.Reader.builtinPrelude.mapError IO.userError)
  let svc := (Source.Service.create pre env (Tests.Ix.Kernel.SourceIngressStep.condense env)
    (evidence := some (Ix.RoleEvidence.bundleEvidence ()))).ensureNames roots
  let mut count := 0
  for root in roots do
    let some ci := env.get? root | throw (IO.userError s!"missing positive fixture {root.pretty}")
    let owned := match ci with | .inductInfo v => v.all ++ v.ctors ++ #[root.mkStr "rec"] | _ => #[root]
    for n in owned do
      need (leanEnv.getModuleIdxFor? (SemanticContract.toLeanName n) == some moduleIndex && (env.get? n).isSome &&
        (svc.statusOf? n).any (·.isAccepted)) s!"positive fixture not owned/Source-accepted: {n.pretty}: {Ixc.blockStatus? svc #[n]}"
      count := count + 1
  need (roots.size == 5 && count == 8) "positive fixture coverage differs"
  let some (.opaqueInfo left) := env.get? (fixture "Left") | throw (IO.userError "opaque fixture absent")
  for label in #["Left", "Right", "Ambient"] do
    let some (.opaqueInfo v) := env.get? (fixture label) | throw (IO.userError "opaque fixture kind differs")
    need (!v.isUnsafe && same v.cnst.type left.cnst.type && same v.value left.value)
      "shared-address fixtures must have identical safe opaque types/bodies"
  let pin := _root_.Ix.Tc.PrimAddrs.canonical.nat
  -- Query-map collisions do not modify or authenticate any Source record.
  let maps : AddrMaps := {
    nameToAddr := fun n =>
      if roots.contains n || n == fixture "Missing" || n == (Name.fromLeanName `Nat) then some pin else none }
  need (roots.all (fun n => maps.resolve n == pin) && maps.resolve (fixture "Missing") == pin)
    "address collision control was not exercised"
  let oracle := Ixc.oracleOf .failClosed false { members := roots, recursors := true, lookup := env.get? }
    none Ixc.oracleFuel (fun _ => .ok svc)
  need (oracle.blockStatus () == none && oracle.retry.isNone) "positive capability policy differs"
  IO.println s!"portable bridge fixtures: {roots.size} roots / {count} owned Source-accepted records"
  return (env, svc, .ixc maps oracle)

private def queryCases (env : Environment) (svc : Source.Service) (kernel : AuxKernel) :
    IO (Array (String × String) × AuxKernelCtx) := do
  let some (.opaqueInfo left) := env.get? (fixture "Left") | throw (IO.userError "opaque fixture kind differs")
  let falseBody := ConstantInfo.defnInfo {
    cnst := left.cnst, value := Expr.mkConst (Name.fromLeanName `Nat) #[]
    hints := .abbrev, safety := .safe, all := #[left.cnst.name] }
  let overlay n := if Name.beqRaw n left.cnst.name then some falseBody else none
  -- Overlay-first is intentional. Only checked agreement permits replay.
  need ((Ixc.overlaid overlay env.get? left.cnst.name).any (fun c => c matches .defnInfo _)) "overlay was not exercised"
  let direct ← IO.ofExcept (Ixc.Scope.new svc.env #[])
  let (checked, _) ← IO.ofExcept (direct.whnfExpr (cn "Left"))
  let some replay := Ixc.replay (Ixc.overlaid overlay env.get?) Ixc.replayFuel (cn "Left")
    | throw (IO.userError "replay missing")
  need (same checked (cn "Left") && same replay (Expr.mkConst (Name.fromLeanName `Nat) #[]) && !same checked replay)
    "conflicting overlay did not separate replay from the checked result"
  IO.ofExcept (run env do
    for route in #[AuxRoute.below, .recursor] do
      for order in #[#["Left", "Right"], #["Right", "Left"]] do
        let s ← scope kernel (route := route)
        for label in order do require (same (← s.whnfOrInput (cn label)) (cn label)) "shared address changed a requested Source name"
        let identity := Expr.mkLam (nm "A") type0 (Expr.mkBVar 0) .default
        require (same (← s.whnfOrInput (Expr.mkApp identity (cn "NatAlias"))) (cn "NatAlias")) "primitive-pin reduction renamed its Source inductive"
    let s ← scope kernel (route := .recursor)
    require (same (← s.whnfOrInput polyLeft) (cn "Left")) "checked polymorphic-identity replay changed its Source name"
    require (same (← s.whnfOrInput (cn "Ambient")) (cn "Ambient")) "ambient identity changed"
    let domainScope ← scope kernel #[localDecl "x" (cn "Left")]
    require ((← domainScope.inferType? (Expr.mkFVar (nm "x"))).any (same · (cn "Left"))) "local domain was replaced by an ambient alias"
    let missing ← capture (s.inferType? (cn "Missing"))
    let conflict ← scope kernel (route := .recursor) (overlay := overlay)
    let overlayError ← capture (conflict.whnfOrInput (cn "Left"))
    let alpha := localDecl "alpha" type0
    let x := localDecl "x" (Expr.mkFVar alpha.fvarName)
    let y := localDecl "y" x.domain
    let base ← scope kernel #[alpha, x]
    let batchError ← capture (base.push #[y, y])
    require ((← base.inferType? (Expr.mkFVar alpha.fvarName)).any (same · type0) && base.depth == 2 &&
      (← base.inferType? (Expr.mkFVar x.fvarName)).any (same · x.domain)) "caught batch failure damaged its original dependent scope"
    let leakError ← capture (base.inferType? (Expr.mkFVar y.fvarName))
    let pushed ← base.push #[y]
    require ((← pushed.inferType? (Expr.mkFVar y.fvarName)).any (same · y.domain)) "valid dependent push failed"
    let popped ← pushed.pop #[y]
    require (popped.depth == 2 && (← popped.inferType? (Expr.mkFVar x.fvarName)).any (same · x.domain)) "valid pop lost the dependent outer scope"
    let mut universeErrors := #[]
    for levels in #[#[], #[nm "ambient"], #[nm "other", nm "extra"]] do
      let ambient ← scope kernel #[] levels
      universeErrors := universeErrors.push (s!"constant universe arity/{levels.size}", ← capture (ambient.inferType? (cn "Poly")))
      for level in #[Level.mkZero, .mkSucc .mkZero] do
        let some explicit ← ambient.inferType? (Expr.mkConst (fixture "Poly") #[level])
          | throw (.unsupportedExpr "portable bridge: explicit constant universe refused")
        let .forallE _ domain body _ _ := explicit
          | throw (.unsupportedExpr "portable bridge: explicit constant type is not a forall")
        require (same domain (Expr.mkSort level) && same body (Expr.mkSort level))
          "explicit constant universe borrowed an ambient level"
    return #[("missing", missing), ("overlay", overlayError), ("duplicate batch", batchError),
      ("failed batch leaked no local", leakError)] ++ universeErrors)

private def egressAndNaturals (env : Environment) (svc : Source.Service) : IO (Array (String × String)) := do
  let s ← IO.ofExcept (Ixc.Scope.new svc.env #[nm "u"])
  let sx ← IO.ofExcept (s.push #[(nm "x", cn "Left")])
  let x := Expr.mkFVar (nm "x")
  need (same (← IO.ofExcept (sx.egress (← IO.ofExcept (sx.term x)))) x) "valid local did not roundtrip"
  let badVar ← IO.ofExcept (refused (sx.egress (.fvar 1 (.sort .zero))))
  let badLevel ← IO.ofExcept (refused ((Egress.egressLevel #[nm "u"] (.param 1)).mapError toString))
  need ((← IO.ofExcept ((Egress.egressLevel #[nm "u"] (.param 0)).mapError toString)) == Level.mkParam (nm "u")) "valid positional level changed"
  let big := 2 ^ 64
  let cases : Array (Nat × ByteArray) := #[(1, ⟨#[1]⟩), (big - 1, ⟨Array.replicate 8 255⟩),
    (big, ⟨(Array.replicate 8 0).push 1⟩), (big + 7, ⟨((#[7] : Array UInt8) ++ Array.replicate 7 0).push 1⟩)]
  for (n, want) in cases do
    let e := Expr.mkLit (.natVal n)
    need (same (← IO.ofExcept (s.egress (← IO.ofExcept (s.term e)))) e) "Source literal truncated"
    let (w, _) ← IO.ofExcept (s.whnfExpr e)
    let (ty, _) ← IO.ofExcept (s.inferExpr e)
    need (same w e && same ty (Expr.mkConst (Name.fromLeanName `Nat) #[])) "checked literal changed value/type"
    let (result, state) ← IO.ofExcept ((CompileM.CompileM.run (CompileM.CompileEnv.new env)
      { all := {}, current := fixture "Poly", mutCtx := default, univCtx := [] } {}
      (CompileM.compileExprNoSurgery e)).mapError toString)
    let (.nat i, _) := result | throw (IO.userError "literal compiler shape differs")
    let some address := state.refs[i.toNat]? | throw (IO.userError "literal reference missing")
    need (want == ByteArray.mk (Nat.toBytesLE n) && state.refs == #[address] &&
      (state.blockBlobs.get? address) == some want && address == Address.admissionHash want)
      "canonical Nat bytes/address differ"
    if n ≥ big then need (want != ByteArray.mk (Nat.toBytesLE (n % big))) "large literal stored its truncated residue"
  return #[("egress fvar", badVar), ("egress universe", badLevel)]

private def addressCases (env : Environment) (kernel : AuxKernel) : IO Unit := do
  let n := fixture "Left"
  let addr (s : String) := Address.blake3 s.toUTF8
  let primary := addr "primary"; let compiled := addr "compiled"; let auxiliary := addr "auxiliary"
  let cenv := { CompileM.CompileEnv.new env with nameToAddr := ({} : Std.HashMap Compile.ExactKey.ExactName Address).insert n compiled }
  let aux := ({} : Std.HashMap Compile.ExactKey.ExactName Address).insert n auxiliary
  let own := ({} : Std.HashMap Compile.ExactKey.ExactName Address).insert n primary
  need ((AddrMaps.ofCompileEnv cenv aux own).resolve n == primary && (AddrMaps.ofCompileEnv cenv aux).resolve n == compiled &&
    (AddrMaps.ofCompileEnv (CompileM.CompileEnv.new env) aux).resolve n == auxiliary &&
    (AddrMaps.ofCompileEnv (CompileM.CompileEnv.new env)).resolve n == n.getHash) "address precedence differs"
  let (result, _) ← IO.ofExcept (run env do
    let s ← scope kernel (route := .recursor)
    s.whnfOrInput polyLeft)
  need (same result (cn "Left")) "named result changed before compilation"
  let compile c := CompileM.CompileM.run c { all := {}, current := fixture "Poly", mutCtx := default, univCtx := [] } {}
    (CompileM.compileExprNoSurgery result)
  let ((compiledExpr, _), st) ← IO.ofExcept ((compile cenv).mapError toString)
  let .ref index levels := compiledExpr | throw (IO.userError "named result did not compile to a reference")
  need (index == 0 && levels.isEmpty && st.refs == #[compiled] && compiled != n.getHash) "compiler emitted a provisional identity"
  match compile (CompileM.CompileEnv.new env) with
  | .error (.missingConstant missing) => need (missing == toString n) "wrong unresolved Source identity"
  | _ => throw (IO.userError "unresolved query result was emitted")

def evaluate : IO Unit := do
  let (env, svc, kernel) ← prepare
  let (queries, ctx) ← queryCases env svc kernel
  let errors := queries ++ (← egressAndNaturals env svc)
  for (label, cause) in errors do IO.println s!"portable bridge refusal {label}: {cause}"
  let atSite (question site cause : String) := s!"unsupportedExpr: aux kernel (IxC Source mode): {question} in {site}: {cause}"
  let inferHead label := s!"inferType of a term headed by {(fixture label).pretty}"
  let recursor := "the recursor generator's scope at depth 0"
  let arity := atSite (inferHead "Poly") ".below's scope at depth 0"
    s!"invalid: incorrect number of universe levels for {(fixture "Poly").pretty}"
  let expected : Array (String × String) := #[
    ("missing", atSite (inferHead "Missing") recursor s!"invalid: unknown constant {(fixture "Missing").pretty}"),
    ("overlay", atSite s!"whnf of a term headed by {(fixture "Left").pretty}" recursor
      s!"replay: the replayed term is not IxC's whnf (input head {(fixture "Left").pretty}, replay head Nat, IxC head {(fixture "Left").pretty}, equal after egress false)"),
    ("duplicate batch", atSite "the push of 2 locals (y, y)" ".below's scope at depth 2" "duplicate free variable y"),
    ("failed batch leaked no local", atSite "inferType of a term headed by local y" ".below's scope at depth 2" "ingress: free variable y"),
    ("constant universe arity/0", arity), ("constant universe arity/1", arity), ("constant universe arity/2", arity),
    ("egress fvar", "egress: free variable 1 beyond the context's 1"),
    ("egress universe", "aux kernel bridge: kunivToLevel: universe parameter index 1 out of range")]
  need (errors == expected) "exact portable bridge refusal table differs"
  addressCases env kernel
  IO.println s!"portable bridge state: epoch={ctx.scopeEpoch}, constants={ctx.tcState.env.consts.size}, ingress={ctx.ingressCache.size}, auxiliary={ctx.auxIngressSeen.size}, names={ctx.sourceNames.size}, recForced={ctx.ixcStats.recForced}, recReplayed={ctx.ixcStats.recReplayed}"
  need (ctx.scopeEpoch == 0 && ctx.tcState.env.consts.isEmpty && ctx.ingressCache.isEmpty &&
    ctx.auxIngressSeen.isEmpty && ctx.sourceNames.isEmpty && ctx.ixcStats.recForced > 0 && ctx.ixcStats.recReplayed > 0)
    "portable bridge touched legacy state or never forced the checked named service"
  IO.println "portable bridge: checked names/overlays, batch isolation, universe arity, full naturals and source address resolution"

def suite : List TestSeq := [
  .individualIO "checked portable bridge names, scopes and boundary contracts" none
    (do evaluate; return (true, 1, 0, none)) .done]

end Tests.Ix.Compile.BridgePortable
