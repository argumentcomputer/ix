import LSpec
import Ix.Meta
import Ix.CompileDriver
import Tests.Ix.Kernel.SourceIngress

/-! Checked-source counterparts of AuxKernelTests and all eleven ElimRule
cases. Complete checked answers replace the retired backend comparisons. Expanded or
malformed query views are never installed as Source declarations. -/

namespace Tests.AuxGen.PortableKernel
open LSpec
open _root_.Ix _root_.Ix.AuxGen

private def nm (s : String) : Name := Name.mkStr .mkAnon s
private def fixtureName (s : String) : Name := Name.fromLeanName (`Tests.AuxGen.PortableFixtures ++ s.toName)
private def prop : Expr := Expr.mkSort .mkZero
private def type0 : Expr := Expr.mkSort (.mkSucc .mkZero)
private def cn (s : String) : Expr := Expr.mkConst (fixtureName s) #[]
private def localDecl (s : String) (type : Expr) : LocalDecl := ⟨nm s, nm s, type, .default⟩
private def alpha : LocalDecl := localDecl "alpha" type0

private def need (ok : Bool) (why : String) : IO Unit := unless ok do throw (IO.userError why)
private def require (ok : Bool) (why : String) : KBridgeM Unit :=
  unless ok do throw (.unsupportedExpr s!"portable kernel: {why}")

private def run (env : Environment) (action : KBridgeM α) : Except String (α × AuxKernelCtx) :=
  ((CompileM.CompileM.run (CompileM.CompileEnv.new env)
    { all := {}, current := nm "portable", mutCtx := default, univCtx := [] } {}
    (action.run AuxKernelCtx.new)).map (·.1)).mapError toString

private def scope (k : AuxKernel) (locals : Array LocalDecl := #[])
    (levels : Array Name := #[]) (route : AuxRoute := .below) : KBridgeM AuxScope := do
  let s ← AuxScope.new k locals levels (route := route)
  return s

private def refuses (action : KBridgeM α) (expected : String) : KBridgeM Unit := do
  let outcome ← try do discard action; pure none catch e => pure (some (toString e))
  require (outcome == some expected) s!"expected {expected}, got {repr outcome}"

private def question (what : String) (depth : Nat) (cause : String) : String :=
  s!"unsupportedExpr: aux kernel (IxC Source mode): {what} in .below's scope at depth {depth}: {cause}"

private def prepare : IO (Environment × AuxKernel) := do
  let moduleName := `Tests.Ix.AuxGen.PortableFixtures
  let leanEnv ← getCompileEnv #[moduleName]
  let some moduleIndex := leanEnv.getModuleIdx? moduleName | throw (IO.userError "fixture module absent")
  let labels := #["Pred", "Two", "One", "T", "Loop", "S", "NestedProp", "NestedType", "PolyTwo", "PolyOne", "PolyAux"]
  let roots := labels.map fixtureName |>.push (Name.fromLeanName `False)
  let seeds := (labels.map (`Tests.AuxGen.PortableFixtures ++ ·.toName)).push `False
  need ((seeds.pop).all (fun n => leanEnv.getModuleIdxFor? n == some moduleIndex)) "fixture ownership incomplete"
  let env ← Tests.Ix.Kernel.SourceIngress.envOf leanEnv seeds
  let pre ← IO.ofExcept (Kernel.Reader.builtinPrelude.mapError IO.userError)
  let svc := (Source.Service.create pre env (Tests.Ix.Kernel.SourceIngressStep.condense env)
    (evidence := some (Ix.RoleEvidence.bundleEvidence ()))).ensureNames roots
  let mut records := 0
  for root in roots do
    let some ci := env.get? root | throw (IO.userError s!"fixture absent: {root.pretty}")
    let owned := match ci with
      | .inductInfo v => v.all ++ v.ctors ++ #[root.mkStr "rec"] ++
        (Array.range v.numNested).map (fun i => root.mkStr s!"rec_{i + 1}")
      | _ => #[root]
    for n in owned do
      need ((env.get? n).isSome && (svc.statusOf? n).any (·.isAccepted))
        s!"positive fixture is not Source-accepted: {n.pretty}: {Ixc.blockStatus? svc #[n]}"
      records := records + 1
  need (records > roots.size) "owned constructor/recursor coverage was empty"
  let oracle := Ixc.oracleOf .failClosed false { members := roots, recursors := true, lookup := env.get? }
    none Ixc.oracleFuel (fun _ => .ok svc)
  need (oracle.blockStatus () == none && oracle.retry.isNone) "fixture capability is not accepted/failClosed"
  IO.println s!"portable fixtures: {roots.size} roots, {records} supplied Source-accepted records"
  return (env, .ixc (AddrMaps.ofCompileEnv (CompileM.CompileEnv.new env)) oracle)

private def answers (k : AuxKernel) : KBridgeM (Level × Level × Expr × Bool × Option Expr) := do
  let s ← AuxScope.new k #[alpha] #[nm "u"] (route := .recursor)
  let a := Expr.mkFVar alpha.fvarName
  let pred := Expr.mkApp (cn "Pred") a
  let pi := Expr.mkForallE (nm "x") a prop .default
  let l1 ← s.getLevel (Expr.mkSort (.mkParam (nm "u")))
  let l2 ← s.getLevel (Expr.mkForallE (nm "y") (Expr.mkSort (.mkParam (nm "u"))) type0 .default)
  return (l1, l2, ← s.whnfOrInput pred, ← s.isDefEqOrFalse pred pi, ← s.inferType? a)

private def scopeCases (k : AuxKernel) : KBridgeM Unit := do
  let s ← scope k #[alpha]
  let missing := Expr.mkFVar (nm "missing")
  let ingress := "ingress: free variable missing"
  refuses (s.getLevel missing) (question "getLevel of a type headed by local missing" 1 ingress)
  refuses (s.whnf? missing) (question "whnf of a term headed by local missing" 1 ingress)
  refuses (s.isDefEq? missing missing) (question "isDefEq of terms headed by local missing and local missing" 1 ingress)
  refuses (s.inferType? missing) (question "inferType of a term headed by local missing" 1 ingress)
  refuses (s.whnfOrInput missing) (question "whnf of a term headed by local missing" 1 ingress)
  refuses (s.isDefEqOrFalse missing missing) (question "isDefEq of terms headed by local missing and local missing" 1 ingress)
  refuses (s.getLevel (Expr.mkSort (.mkParam (nm "unknown"))))
    (question "getLevel of a type headed by a sort" 1 "aux kernel bridge: kunivToLevel: universe parameter index 0 out of range")
  refuses (s.getLevel (Expr.mkSort (.mkMvar (nm "m"))))
    (question "getLevel of a type headed by a sort" 1 "ingress: level metavariable m")
  refuses (s.inferType? (Expr.mkMVar (nm "m")))
    (question "inferType of a term headed by a term" 1 "ingress: metavariable m")
  refuses (s.getLevel (Expr.mkApp prop prop))
    (question "getLevel of a type headed by a sort" 1 "invalid: function expected")
  let x := localDecl "x" (Expr.mkFVar alpha.fvarName)
  let y := localDecl "y" prop
  refuses (scope k #[] #[nm "u", nm "u"])
    "unsupportedExpr: aux kernel bridge: duplicate universe parameter 'u'"
  refuses (scope k #[y, y]) "unsupportedExpr: aux kernel bridge: duplicate outer free variable 'y'"
  let sy ← scope k #[y]
  refuses (sy.push #[y]) "unsupportedExpr: aux kernel bridge: duplicate pushed free variable 'y'"
  refuses (sy.pop #[y]) "unsupportedExpr: aux kernel bridge: popLocals exceeds pushed local count"
  let empty ← scope k
  let xy ← empty.push #[localDecl "x" prop, y]
  refuses (xy.pop #[localDecl "x" prop]) "unsupportedExpr: aux kernel bridge: popLocals is not LIFO at 'x'"
  let sx ← s.push #[x]
  let popped ← sx.pop #[x]
  let other ← popped.push #[y]
  require ((← sx.inferType? (Expr.mkFVar x.fvarName)) == some (Expr.mkFVar alpha.fvarName) &&
    (← other.inferType? (Expr.mkFVar y.fvarName)) == some prop &&
    (← s.inferType? (Expr.mkFVar alpha.fvarName)) == some type0 &&
    (← popped.inferType? (Expr.mkFVar alpha.fvarName)) == some type0 &&
    sx.depth == 2 && popped.depth == 1 && sx.nOuter == 1) "immutable push/pop values or matching-depth isolation changed"
  try
    discard <| scope k
    throwBridge (.internal "caught portable control")
  catch _ => pure ()
  require ((← s.inferType? (Expr.mkFVar alpha.fvarName)) == some type0) "caught error/new scope invalidated retained scope"
  for (a, b) in #[(prop, prop), (type0, prop)] do
    require ((← s.whnfOrInput a) == (← s.whnf? a).getD a &&
      (← s.isDefEqOrFalse a b) == (← s.isDefEq? a b).getD false) "valid Option wrappers changed"
  require (!(← s.isDefEqOrFalse type0 prop)) "different sorts compare equal"

private def original (env : Environment) (n : Name) : Except String FlatInfo := do
  let some (.inductInfo v) := env.get? n | throw s!"missing former {n.pretty}"
  let ctors ← v.ctors.mapM fun n => do
    let some (.ctorInfo c) := env.get? n | throw s!"missing constructor {n.pretty}"
    return c
  return {
    name := n, ind := v, ctors, allNames := #[n], isAux := false
    specParams := #[], occurrenceLevelArgs := #[], ownParams := v.numParams, nIndices := v.numIndices }

private def expanded (env : Environment) (n : Name) : Except String (Array FlatInfo) := do
  let ((block, _), _) ← (CompileM.CompileM.run (CompileM.CompileEnv.new env)
    { all := {}, current := n, mutCtx := default, univCtx := [] } {}
    ((show KBridgeM ExpandedBlock from liftM (expandNestedBlock #[n] {})).run AuxKernelCtx.new)).mapError toString
  unless block.nOriginals == 1 && block.types.size == 2 && block.blockParamFvars.isEmpty do
    throw "expected one original and one real unparameterized nested auxiliary"
  let base ← original env n
  return block.types.mapIdx fun i member =>
    let ctors := member.ctors.mapIdx fun j c =>
      { cnst := ⟨c.name, block.levelParams, c.typ⟩, induct := member.name
        cidx := j, numParams := member.nParams, numFields := c.nFields, isUnsafe := false : ConstructorVal }
    { base with
      name := member.name, allNames := #[member.name], isAux := i > 0, ctors
      ind := { base.ind with
        cnst := ⟨member.name, block.levelParams, member.typ⟩
        ctors := ctors.map (·.cnst.name), numParams := member.nParams, numIndices := member.nIndices, numNested := 0 }
      ownParams := member.nParams, nIndices := member.nIndices }

private def eliminationCases (env : Environment) (k : AuxKernel) : IO Unit := do
  let nested ← IO.ofExcept (expanded env (fixtureName "NestedProp"))
  let nestedType ← IO.ofExcept (expanded env (fixtureName "NestedType"))
  let p := nested[0]!
  let auxiliary := nested[1]!.name
  need ((env.get? auxiliary).isNone &&
    p.ctors.any (fun c => (collectLeanConstRefs c.cnst.type {}).contains auxiliary)) "missing-aux control did not exercise an actual generated field"
  let empty ← IO.ofExcept (original env (Name.fromLeanName `False))
  let one ← IO.ofExcept (original env (fixtureName "One"))
  let loop ← IO.ofExcept (original env (fixtureName "Loop"))
  let polyTwo ← IO.ofExcept (original env (fixtureName "PolyTwo"))
  let polyOne ← IO.ofExcept (original env (fixtureName "PolyOne"))
  let polyAux ← IO.ofExcept (original env (fixtureName "PolyAux"))
  let u := nm "u"
  let zero := Level.mkIMax (.mkParam u) .mkZero
  let semantic := { p with ind := { p.ind with cnst := { p.ind.cnst with
    levelParams := #[u], type := Expr.mkSort zero } } }
  let (zeroEqual, _) ← IO.ofExcept (run env do
    let s ← scope k #[] #[u]; s.isDefEqOrFalse (Expr.mkSort zero) prop)
  need (zeroEqual) "semantic-zero header equivalence or checked scope changed"
  let badResult := { p with ind := { p.ind with cnst := { p.ind.cnst with type := Expr.mkConst (nm "MissingResult") #[] } } }
  let flags xs := computeIsLargeAndK xs 1 0 k
  let cases : Array (String × KBridgeM (Bool × Bool × Bool) × Except String (Bool × Bool × Bool)) := #[
    ("1 nested Prop before missing field", flags nested, .ok (false, false, true)),
    ("2 missing field without auxiliary", flags #[p], .error s!"unsupportedExpr: aux kernel (IxC Source mode): the elimination decision of {p.name.pretty} in the block's elimination decision: invalid: unknown constant {auxiliary.pretty}"),
    ("3 semantic-zero spelling", flags #[semantic, nested[1]!], .ok (false, false, true)),
    ("4 bad result still refuses", flags #[badResult, nested[1]!], .error s!"unsupportedExpr: aux kernel (IxC Source mode): the elimination decision of {p.name.pretty} in the block's elimination decision: get_result_sort_level: not a sort"),
    ("5 empty Prop", flags #[empty], .ok (true, false, true)),
    ("6 fieldless Prop singleton", flags #[one], .ok (true, true, true)),
    ("7 proof-only singleton", flags #[loop], .ok (true, false, true)),
    ("8 nested Type", flags nestedType, .ok (true, false, false)),
    ("9 Sort-u two constructors", flags #[polyTwo], .ok (false, false, false)),
    ("10 Sort-u singleton with auxiliary slot", flags #[polyOne, { polyAux with isAux := true }], .ok (false, false, false)),
    ("11 retained kernel sequence", (do require ((← flags nested) == (false, false, true)) "first decision changed"; flags #[loop]), .ok (true, false, true))]
  need (cases.size == 11) "elimination coverage incomplete"
  for (label, action, expected) in cases do
    let result := run env action
    match result, expected with
    | .ok (actual, _), .ok want => need (actual == want) s!"{label}: wrong flags"
    | .error actual, .error want => need (actual == want) s!"{label}: expected {want}, got {actual}"
    | _, _ => throw (IO.userError s!"{label}: success/refusal changed")
    IO.println s!"portable elimination {label}: passed"
  let (neighbor, _) ← IO.ofExcept (run env (flags #[polyOne]))
  need (neighbor.1) "Sort-u singleton neighbor was not large"

def evaluateScopes : IO Unit := do
  let (env, kernel) ← prepare
  discard <| IO.ofExcept (run env (scopeCases kernel))

def evaluate : IO Unit := do
  let (env, kernel) ← prepare
  let actual ← IO.ofExcept (run env (answers kernel))
  let pi := Expr.mkForallE (nm "x") (Expr.mkFVar alpha.fvarName) prop .default
  need (actual.1.1 == Level.mkSucc (.mkParam (nm "u")) &&
    actual.1.2.1 == Level.mkMax (Level.mkSucc (Level.mkSucc Level.mkZero)) (Level.mkSucc (.mkParam (nm "u"))) &&
    actual.1.2.2.1 == pi && actual.1.2.2.2.1 && actual.1.2.2.2.2 == some type0)
    s!"checked named queries/levels/local inference differ: {repr actual.1}"
  let s ← IO.ofExcept (original env (fixtureName "S"))
  let alternate := Expr.mkApp (cn "Pred") (cn "T")
  let (_, ctx) ← IO.ofExcept (run env do
    let sc ← scope kernel
    require (← sc.isDefEqOrFalse s.ind.cnst.type alternate) "alternate S header is not checked delta-equivalent"
    let s := { s with ind := { s.ind with cnst := { s.ind.cnst with type := alternate } } }
    for (row, flat, large, isProp) in #[(s, 1, true, true), (s, 2, false, true)] do
      let d ← kernel.elimDecision #[(row.ind, row.ctors)] row.ind.numParams flat
      require (d.isLarge == large && d.isProp == isProp) "alias result-sort decision changed"
    for (label, flat, large, isProp) in #[("Two", 1, false, true), ("T", 1, true, false),
        ("One", 1, true, true), ("One", 2, false, true), ("T", 2, true, false)] do
      let row ← match original env (fixtureName label) with
        | .ok v => pure v | .error e => throw (.unsupportedExpr e)
      let d ← kernel.elimDecision #[(row.ind, row.ctors)] row.ind.numParams flat
      require (d.isLarge == large && d.isProp == isProp) s!"ordinary elimination decision changed: {label}/{flat}"
    let retained ← scope kernel #[alpha]
    let one ← match original env (fixtureName "One") with
      | .ok v => pure v | .error e => throw (.unsupportedExpr e)
    discard <| kernel.elimDecision #[(one.ind, one.ctors)] 0 1
    require ((← retained.inferType? (Expr.mkFVar alpha.fvarName)) == some type0) "elimination invalidated an immutable scope")
  need (ctx.ixcStats.recForced > 0) "alias decision did not force its checked service"
  eliminationCases env kernel
  IO.println "portable kernel: checked names/queries/refusals and immutable scopes; eleven elimination cases"

def suite : List TestSeq := [
  .individualIO "checked-source portable AuxKernel and eleven elimination contracts" none
    (do evaluate; return (true, 1, 0, none)) .done]

end Tests.AuxGen.PortableKernel
