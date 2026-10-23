import Tests.Ix.AuxGen.GenerationOnlyAliases
import Lean.Elab.Command

namespace Tests.Ix.AuxGen.GenerationOnlyOpaques
open _root_.Ix _root_.Ix.AuxGen

run_cmd do
  let env ← Lean.getEnv
  for (suffix, aliasName) in #[("checkedOpaqueHeader", `checkedHeader),
      ("installPreparedOpaque", `installOpaque), ("actualGroup", `groupOf), ("refsOf", `refsOf)] do
    let names := env.constants.fold (init := (#[] : Array Lean.Name)) fun acc n _ =>
      if n.toString.startsWith "_private.Ix.AuxGen.GenerationOnly." &&
          n.toString.endsWith (".Ix.AuxGen.GenerationOnly." ++ suffix) then acc.push n else acc
    unless names.size == 1 do throwError "private alias {suffix}: {names}"
    Lean.Elab.Command.elabCommand (← `(abbrev $(Lean.mkIdent aliasName) := @$(Lean.mkIdent names[0]!)))

private def need (ok : Bool) (why : String) : IO Unit := unless ok do throw (IO.userError why)
private def refused (label : String) (r : Except String α) (want : String) : IO Unit := do
  match r with
  | .error e => need (e == want) s!"{label}: expected {want}, got {e}"
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly accepted")
private def name (s : String) : Name := Name.fromLeanName (`M7Opaque ++ s.toName)
private def key (s : String) : Kernel.Key .source := LeanIngress.ingressKey (name s)
private abbrev E := Kernel.Expr .source
private def prop : E := .sort .zero
private def type0 : E := .sort (.succ .zero)

private def rawControls : IO Unit := do
  let env : Source.SourceEnv := {}
  let raw label header body := (checkedHeader env ⟨key label, [], header⟩ body).mapError Source.renderCheck
  let mk label : OpaqueVal := ⟨⟨name label, #[], Expr.mkSort (.mkSucc .mkZero)⟩,
    Expr.mkSort .mkZero, false, #[name label]⟩
  let base := mk "good"
  let checked ← IO.ofExcept (installOpaque env base)
  let some entry := checked.tier.back? | throw (IO.userError "opaque entry absent")
  let .infos answers := entry.answer | throw (IO.userError "opaque answer kind changed")
  need (entry.stage == 2 && entry.check.length == 1 && answers.length == 1 &&
    (entry.check ++ answers).all (fun | .axiomInfo cv => cv.name == key "good" | _ => false))
    "opaque body escaped into a check/answer record"
  need (checked.fold.pos == env.fold.pos && decide (checked.fold.fe.env.consts = env.fold.fe.env.consts) &&
    checked.sigma.entries == env.sigma.entries && (checked.fold.fe.find? (key "good")).isNone)
    "opaque install changed the logical frame or sigma"
  refused "wrong body type" (raw "wrong" prop prop)
    s!"invalid: type mismatch in generation opaque {key "wrong"}"
  refused "bad application" (raw "badApp" type0 (.app prop prop)) "invalid: function expected"
  refused "self body" (raw "self" type0 (.const (key "self") []))
    s!"invalid: unknown constant in value of {key "self"}"
  refused "self header" (raw "selfHeader" (.const (key "selfHeader") []) prop)
    s!"invalid: unknown constant in type of {key "selfHeader"}"
  refused "loose body" (raw "loose" type0 (.bvar 0))
    s!"invalid: loose bound variable in value of {key "loose"}"
  refused "free body" (raw "free" type0 (.fvar 0 type0))
    s!"invalid: unexpected free variable in value of {key "free"}"
  refused "free header" (raw "freeType" (.fvar 0 type0) prop)
    s!"invalid: unexpected free variable in type of {key "freeType"}"
  refused "loose header" (raw "looseType" (.bvar 0) prop)
    s!"invalid: loose bound variable in type of {key "looseType"}"
  refused "header universe" (raw "typeUniverse" (.sort (.param 0)) prop)
    s!"invalid: undeclared universe parameter in type of {key "typeUniverse"}"
  refused "non-sort header" (raw "nonSort" (.lam prop (.bvar 0) default) prop) "invalid: expected a sort"
  refused "body universe" (raw "universe" type0 (.sort (.param 0)))
    s!"invalid: undeclared universe parameter in value of {key "universe"}"
  refused "unresolved body" (raw "missing" type0 (.const (key "absent") []))
    s!"invalid: unknown constant in value of {key "missing"}"
  refused "duplicate universes" ((checkedHeader env ⟨key "levels", [0, 0], type0⟩ prop).mapError Source.renderCheck)
    s!"invalid: duplicate universe parameters in {key "levels"}"
  refused "freshness" (installOpaque checked base) s!"tier: {key "good"} is already declared"
  refused "unsafe opaque" (installOpaque env { base with isUnsafe := true })
    s!"generation: unsafe supplied opaque {base.cnst.name.pretty}"
  let nat := Name.fromLeanName `Nat
  refused "role key" (installOpaque env { base with cnst := { base.cnst with name := nat } })
    "generation: opaque must have an input key"
  let failed := mk "rollback"
  refused "atomic invalid body" (installOpaque checked { failed with value := Expr.mkSort (.mkSucc .mkZero) })
    s!"invalid: type mismatch in generation opaque {key "rollback"}"
  need (checked.tier.size == 1 && ((checked.checkView 2).find? (key "rollback")).isNone &&
    ((checked.answers 2).find? (key "rollback")).isNone) "failed opaque published a header"

private def replace (svc : Source.Service) (n : Name) (ci : ConstantInfo) : Source.Service :=
  { svc with input := { svc.input with get? := fun k => if Name.beqRaw k n then some ci else svc.input.get? k } }

def evaluate : IO Unit := do
  rawControls
  let moduleName := `Tests.Ix.AuxGen.GenerationOnlyOpaqueFixtures
  let ln (s : String) := moduleName ++ s.toName
  let ixn (s : String) := Name.fromLeanName (ln s)
  let owner := ixn "Owner"
  let hidden := ixn "hidden"
  let companion := ixn "hidden._unsafe_rec"
  let bodyOnly := ixn "bodyOnly"
  let usesBody := ixn "usesBody"
  let leanEnv ← getCompileEnv #[moduleName]
  let some moduleIndex := leanEnv.getModuleIdx? moduleName | throw (IO.userError "runtime fixture module absent")
  need ((#["Owner", "hidden", "bodyOnly", "usesBody"].map ln).all
    (fun n => leanEnv.getModuleIdxFor? n == some moduleIndex)) "runtime fixture ownership/coverage is incomplete"
  let env ← Tests.Ix.Kernel.SourceIngress.envOf leanEnv #[ln "Owner", ln "hidden._unsafe_rec"]
  let blocks := Tests.Ix.Kernel.SourceIngressStep.condense env
  let pre ← IO.ofExcept (Kernel.Reader.builtinPrelude.mapError IO.userError)
  let svc := (Source.Service.create pre env blocks
    (evidence := some (Ix.RoleEvidence.bundleEvidence ()))).ensureNames #[owner]
  let some why := Ixc.blockStatus? svc #[owner] | throw (IO.userError "fixture owner accepted")
  let some (.opaqueInfo supplied) := env.get? hidden | throw (IO.userError "logical opaque wrapper absent")
  let some (.defnInfo implementation) := env.get? companion | throw (IO.userError "supplied companion absent")
  need (!supplied.isUnsafe && implementation.safety == .partial &&
    (collectLeanConstRefs supplied.value {}).contains (Name.fromLeanName `Inhabited.default))
    "fixture is not an actual supplied default-body opaque/partial pair"
  need (!(svc.statusOf? companion).any (fun s => s.isAccepted || s.isTier)) "companion already ready"
  let group ← IO.ofExcept (groupOf svc.input usesBody)
  need ((refsOf group).contains bodyOnly) "opaque body-only dependency was dropped"
  let oracle ← IO.ofExcept (GenerationOnly.ofService svc owner)
  need (oracle.mode == .failClosed && oracle.recursors && oracle.retry.isNone && oracle.blockStatus () == some why)
    "opaque preparation changed capability policy/reason"
  let localName := name "x"
  let localType := Expr.mkConst (Name.fromLeanName `Ix.AuxGen.OracleScope) #[]
  let scope ← IO.ofExcept (oracle.newScope #[] #[(localName, localType)])
  let app n := Expr.mkApp (Expr.mkConst n #[]) (Expr.mkFVar localName)
  for n in #[hidden, usesBody] do
    let value := app n
    let (whnf, _) ← IO.ofExcept (scope.whnf value)
    need (Ix.Compile.ExactKey.exprEq whnf value) s!"public oracle unfolded opaque {n.pretty}"
    for literal in #[0, 37, 41] do
      let (equal, _) ← IO.ofExcept (scope.isDefEq value (Expr.mkLit (.natVal literal)))
      need (!equal) "public oracle exposed an opaque logical/operational body"
  let (reduced, _) ← IO.ofExcept (scope.whnf (app bodyOnly))
  need (Ix.Compile.ExactKey.exprEq reduced (Expr.mkLit (.natVal 41))) "body-only checked dependency missing"
  refused "companion remains unavailable" (scope.infer (Expr.mkConst companion #[]))
    s!"invalid: unknown constant {companion.pretty}"
  let publicCase ci := GenerationOnly.ofService (replace svc hidden ci) owner
  refused "actual supplied body is checked" (publicCase (.opaqueInfo { supplied with value := Expr.mkSort .mkZero }))
    s!"invalid: type mismatch in generation opaque {LeanIngress.ingressKey hidden}"
  refused "unsafe public opaque" (publicCase (.opaqueInfo { supplied with isUnsafe := true }))
    s!"generation: unsafe supplied opaque {hidden.pretty}"
  refused "unready partial stays refused" (publicCase (.opaqueInfo { supplied with value := Expr.mkConst companion #[] }))
    s!"generation: non-safe definition unit member {companion.pretty}"
  for ci in #[ConstantInfo.axiomInfo ⟨supplied.cnst, false⟩, .thmInfo ⟨supplied.cnst, supplied.value, supplied.all⟩] do
    refused "unsupported no-body/theorem kind" (publicCase ci) s!"generation: unsupported supplied dependency {hidden.pretty}"
  let some rep := blocks.lowLinks.get? hidden | throw (IO.userError "opaque placement absent")
  refused "unplaced opaque" (groupOf { svc.input with blocks := { blocks with lowLinks := blocks.lowLinks.erase hidden } } hidden)
    s!"generation: opaque is unplaced {hidden.pretty}"
  refused "absent opaque unit" (groupOf { svc.input with blocks := { blocks with blocks := blocks.blocks.erase rep } } hidden)
    s!"generation: opaque unit is absent {hidden.pretty}"
  let malformed members := { svc.input with blocks := { blocks with blocks := blocks.blocks.insert rep members } }
  refused "non-singleton" (groupOf (malformed (({} : Set Name).insert hidden |>.insert bodyOnly)) hidden)
    s!"generation: opaque unit is not singleton {hidden.pretty}"
  let forged := match hidden with
    | .str parent s hash => Name.str parent (s ++ "forged") hash
    | _ => hidden
  need (forged == hidden && !Name.beqRaw forged hidden) "hash-collision control was vacuous"
  refused "structural singleton name" (groupOf (malformed (({} : Set Name).insert forged)) hidden)
    s!"generation: opaque unit member differs at {hidden.pretty}"
  refused "record name" (groupOf (replace svc hidden (.opaqueInfo { supplied with cnst := { supplied.cnst with name := forged } })).input hidden)
    s!"generation: input name differs at {hidden.pretty}"
  need (Ixc.blockStatus? svc #[owner] == some why && (svc.env.fold.fe.find? (LeanIngress.ingressKey hidden)).isNone)
    "opaque checking changed the original logical refusal/frame"
  IO.println "checked opaque: actual default body and body-only refs; public opacity; no companion grant; full guard/frame/rollback/name controls"

end Tests.Ix.AuxGen.GenerationOnlyOpaques
