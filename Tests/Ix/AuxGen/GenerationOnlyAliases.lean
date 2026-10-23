import Ix.AuxGen.GenerationOnly
import Tests.Ix.Kernel.SourceIngress
import Lean.Elab.Command

namespace Tests.Ix.AuxGen.GenerationOnlyAliases

open _root_.Ix.AuxGen
open _root_.Ix.Kernel (Expr ConstantVal ConstantInfo Key Level)

-- Test-only access to the bounded private retry, without a production hook.
run_cmd do
  let env ← Lean.getEnv
  for (suffix, aliasName) in #[("checkedDefinitionAnswers", `checkedAnswers),
      ("installPreparedDefinitions", `installDefs), ("Context", `Ctx),
      ("Context.mk", `context), ("Context.env", `genEnv),
      ("Context.update", `updated), ("Context.baseline", `baseline),
      ("Context.reason", `reason)] do
    let names := env.constants.fold (init := (#[] : Array Lean.Name)) fun acc n _ =>
      if n.toString.startsWith "_private.Ix.AuxGen.GenerationOnly." &&
          n.toString.endsWith (".Ix.AuxGen.GenerationOnly." ++ suffix) then acc.push n else acc
    unless names.size == 1 do throwError "private alias {suffix}: {names}"
    Lean.Elab.Command.elabCommand (← `(abbrev $(Lean.mkIdent aliasName) := @$(Lean.mkIdent names[0]!)))

-- Exact frames, including the complete baseline with its original statuses.
example (g : Ctx) (out : Source.SourceEnv) : baseline (updated g out) = baseline g := rfl
example (g : Ctx) (out : Source.SourceEnv) : reason (updated g out) = reason g := rfl
example (g : Ctx) (out : Source.SourceEnv) : (genEnv (updated g out)).fold = (genEnv g).fold := rfl
example (g : Ctx) (out : Source.SourceEnv) : (genEnv (updated g out)).ev = (genEnv g).ev := rfl

private abbrev E := Expr .source
private abbrev CV := ConstantVal .source
private abbrev Member := CV × E

private def k (label : String) : Key .source :=
  _root_.Ix.LeanIngress.ingressKey (_root_.Ix.Name.fromLeanName (`M7Alias ++ label.toName))
private def cv (label : String) (type : E) : CV := ⟨k label, [], type⟩
private def u1 : Level := .succ .zero
private def u2 : Level := .succ u1
private def prop : E := .sort .zero
private def type0 : E := .sort u1
private def aliasType : E := .const (k "Alias") []
private def functionMember : Member :=
  (cv "fn" (.forallE aliasType type0 default), .lam aliasType (.bvar 0) default)
private def value : E :=
  .letE type0 (.app (.const (k "fn") []) prop) (.bvar 0) default
private def member (label : String) : Member := (cv label type0, value)

private def need (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def refused (label : String) (result : Except String α) (expected : String) : IO Unit := do
  match result with
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly accepted")
  | .error actual => need (actual == expected) s!"{label}: expected {expected}, got {actual}"

private def errorOf (result : Except String α) : Option String :=
  match result with | .error error => some error | .ok _ => none

def evaluate : IO Unit := do
  -- A real checked prior alias, opaque for checks and transparent for answers.
  -- Sort 0 has type Sort 1, definitionally the prior Alias's value.
  let initial : Source.SourceEnv := {}
  let prior ← IO.ofExcept (initial.installTierDecl
    (.defs .unsaf [(cv "Alias" (.sort u2), type0)]) [.abbrev])
  -- The let's annotation infers its RHS before zeta reduction; a bare app
  -- is only traversed structurally. The current fn's body remains opaque.
  let positive := [functionMember, member "positive"]
  let original := prior.installTierDecl (.defs .unsaf positive) [.abbrev, .abbrev]
  refused "opaque annotation actually refuses" original "invalid: application type mismatch"
  let after ← IO.ofExcept (installDefs prior positive [.abbrev, .abbrev])
  need (after.tier.size == prior.tier.size + 1 && after.fold.pos == prior.fold.pos &&
    decide (after.fold.fe.env.consts = prior.fold.fe.env.consts) &&
    after.sigma.entries == prior.sigma.entries) "private install changed the logical frame or sigma"
  need ((after.fold.fe.find? (k "positive")).isNone) "generation dependency entered the logical fold"
  let some entry := after.tier.back? | throw (IO.userError "new tier entry absent")
  let names := [k "fn", k "positive"]
  need (entry.stage == 2 && entry.check.map (·.name) == names && entry.check.all
    (fun | .axiomInfo _ => true | _ => false)) "check entry gained a body or capability"
  let .infos infos := entry.answer | throw (IO.userError "wrong answer entry kind")
  let answersMatch := infos.all fun
    | .defnInfo _ _ hint => hint == .abbrev
    | _ => false
  need (infos.map (·.name) == names && answersMatch) "answer record order/name/hint changed"
  let reduced ← IO.ofExcept ((_root_.Ix.Kernel.Tier.runC
    ((after.answers 2).knot.whnf 0 (.const (k "positive") []))).mapError Source.renderCheck)
  need (decide (reduced = prop)) "checked prior-alias body does not unfold to the expected value"
  -- The prior ordinary path remains available, without invoking the repair.
  let simple := [(cv "ordinary" type0, prop)]
  let ordinary ← IO.ofExcept (prior.installTierDecl (.defs .unsaf simple) [.abbrev])
  let preserved ← IO.ofExcept (installDefs prior simple [.abbrev])
  need (preserved.tier.size == ordinary.tier.size &&
    decide ((preserved.checkView 2).env.consts = (ordinary.checkView 2).env.consts)) "ordinary install changed"

  let check members := (checkedAnswers prior members [.abbrev]).mapError Source.renderCheck
  refused "wrong result type" (check [functionMember, (cv "wrongType" prop, value)])
    s!"invalid: type mismatch in generation dependency {k "wrongType"}"
  refused "bad application body" (check [(cv "badBody" type0, .app prop prop)])
    "invalid: function expected"
  refused "loose body variable" (check [(cv "loose" type0, .bvar 0)])
    s!"invalid: loose bound variable in value of {k "loose"}"
  refused "free body variable" (check [(cv "free" type0, .fvar 0 type0)])
    s!"invalid: unexpected free variable in value of {k "free"}"
  refused "undeclared body universe" (check [(cv "universe" type0, .sort (.param 0))])
    s!"invalid: undeclared universe parameter in value of {k "universe"}"
  refused "unknown body constant" (check [(cv "unknown" type0, .const (k "absent") [])])
    s!"invalid: unknown constant in value of {k "unknown"}"
  refused "free header variable" (check [(cv "freeHeader" (.fvar 0 type0), prop)])
    s!"invalid: unexpected free variable in type of {k "freeHeader"}"
  refused "header must be a type" (check [(cv "nonSort" (.lam prop (.bvar 0) default), prop)])
    "invalid: expected a sort"
  refused "empty block" (check []) "not implemented yet: tier: an empty definition block"
  refused "duplicate current key" (check [member "duplicate", member "duplicate"])
    s!"not implemented yet: tier: a definition block declares a key twice ({k "duplicate"})"
  let second := { (cv "second" type0) with levelParams := [0] }
  refused "different member universes" (check [member "first", (second, prop)])
    s!"not implemented yet: tier: the members of a definition block disagree on their universe parameters ({k "second"})"
  for key in [Key.role .nat, Key.aux (k "base") .model] do
    refused "non-input key" (check [(⟨key, [], type0⟩, prop)])
      s!"not implemented yet: tier: a role key or a generated key ({key})"
  let collision := [(cv "Alias" (.sort u2), type0)]
  refused "existing key" (installDefs prior collision [.abbrev])
    s!"tier: {k "Alias"} is already declared"

  -- The current block remains opaque: a wrong-typed recursive argument
  -- fails at its application, and headers cannot refer to a later member.
  let selfType : E := .forallE type0 type0 default
  let selfBody : E := .lam type0 (.app (.const (k "self") []) type0) default
  refused "wrong-typed self call" (check [(cv "self" selfType, selfBody)])
    "invalid: application type mismatch"
  refused "header sees no current member" (check
    [(cv "forward" (.const (k "later") []), prop), (cv "later" (.sort u2), type0)])
    s!"invalid: unknown constant in type of {k "forward"}"
  let lateFailure := [functionMember, member "firstChecked", (cv "lateWrongType" prop, value)]
  let oldFailure := prior.installTierDecl (.defs .unsaf lateFailure) [.abbrev, .abbrev]
  let newFailure := installDefs prior lateFailure [.abbrev, .abbrev]
  need ((errorOf newFailure).isSome && errorOf newFailure == errorOf oldFailure)
    "late failure lost the original refusal"
  need (((prior.checkView 2).find? (k "firstChecked")).isNone &&
    ((prior.checkView 2).find? (k "fn")).isNone)
    "a failed block published its earlier checked member"
  need (prior.tier.size == 1 && prior.fold.fe.env.consts.isEmpty && prior.sigma.entries.isEmpty)
    "a failure changed the prior environment"

  -- Actual Source acceptance still excludes the owner from this factory.
  let leanEnv ← getCompileEnv #[`Init]
  let env ← Tests.Ix.Kernel.SourceIngress.envOf leanEnv #[`Nat]
  let blocks := Tests.Ix.Kernel.SourceIngressStep.condense env
  let pre ← IO.ofExcept (_root_.Ix.Kernel.Reader.builtinPrelude.mapError IO.userError)
  let owner := _root_.Ix.Name.fromLeanName `Nat
  let svc := (Source.Service.create pre env blocks
    (evidence := some (_root_.Ix.RoleEvidence.bundleEvidence ()))).ensureNames #[owner]
  need ((svc.statusOf? owner).any (·.isAccepted)) "accepted-owner control did not accept its actual Nat input"
  refused "accepted owner" (GenerationOnly.ofService svc owner)
    "generation: Source-accepted block is ineligible"
  IO.println "checked prior aliases: annotation retry; exact frames and opaque current headers; body/type/name/universe/shape/self-call negatives; atomic late failure; accepted-owner refusal"

end Tests.Ix.AuxGen.GenerationOnlyAliases
