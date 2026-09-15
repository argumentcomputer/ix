/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BinderInference
import Ix.Theory.Model.BetaSpine

/-!
Type formation comes from actual inference of a type, including the type
check performed while admitting a declaration. These results preserve that
information when the dependency interface grows, a local binder is opened,
or a closed declaration is instantiated at new universe levels.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v
variable {β : Type u}

/-- Every earlier declaration, with all its fields, remains in the later
interface. This is a syntactic map relation, not a realization assumption. -/
def InterfaceExtends (earlier later : Model.Environment β) : Prop :=
  ∀ ref entry, earlier ref = some entry → later ref = some entry

theorem InterfaceExtends.refl (entries : Model.Environment β) : InterfaceExtends entries entries :=
  fun _ _ found => found

theorem InterfaceExtends.trans {first second third : Model.Environment β}
    (left : InterfaceExtends first second) (right : InterfaceExtends second third) :
    InterfaceExtends first third := fun ref entry found => right ref entry (left ref entry found)

theorem InterfaceExtends.realizes {earlier later : Model.Environment β}
    (extension : InterfaceExtends earlier later) {V : Type v} [SetTheory V]
    {constants : Assignment β V} (realizes : Realizes constants later) : Realizes constants earlier := by
  constructor
  · intro ref entry found
    exact realizes.typeValid ref entry (extension ref entry found)
  · intro ref entry found
    exact realizes.member ref entry (extension ref entry found)
  · intro ref entry found
    exact realizes.bodyValid ref entry (extension ref entry found)
  · intro ref entry found
    exact realizes.bodyValue ref entry (extension ref entry found)
  · intro ref entry found
    exact realizes.equationValue ref entry (extension ref entry found)
  · intro ref entry found
    exact realizes.factMeaning ref entry (extension ref entry found)

theorem InterfaceExtends.typing {earlier later : Model.Environment β}
    (extension : InterfaceExtends earlier later) {context : Model.Context β} {term type : AExpr β}
    (typed : TypingClaim.{u,v} earlier context term type) :
    TypingClaim.{u,v} later context term type := by
  intro V _ constants realizes levels env valid
  exact typed V constants (extension.realizes realizes) levels env valid

theorem context_valid_tail {V : Type v} [SetTheory V]
    {constants : Assignment β V} {levels : List Nat} {context : Model.Context β}
    {domain : AExpr β} {env : Nat → V} (valid : (context.push domain).Valid constants levels env) :
    context.Valid constants levels (Valuation.skip 1 0 env) := valid.tail

theorem typing_weaken {entries : Model.Environment β} {context : Model.Context β}
    {term type domain : AExpr β} (typed : TypingClaim.{u,v} entries context term type) :
    TypingClaim.{u,v} entries (context.push domain) (term.liftN 1) (type.liftN 1) := by
  intro V _ constants realizes levels env valid
  have result := typed V constants realizes levels _ (context_valid_tail valid)
  simpa only [wellDenoted_liftN, interp_liftN] using result

/-- Closed type checks remain valid in any local context and at every
universe instance. The original assignment already realizes all instances
of every declaration in the dependency interface. -/
theorem typing_instL_closed {entries : Model.Environment β} {context : Model.Context β}
    {term type : AExpr β} (typed : TypingClaim.{u,v} entries [] term type) (arguments : List VLevel) :
    TypingClaim.{u,v} entries context (term.instL arguments) (type.instL arguments) := by
  intro V _ constants realizes levels env _
  have result := typed V constants realizes (arguments.map (VLevel.eval levels)) env
    (Context.valid_nil constants _ env)
  simpa only [wellDenoted_instL, interp_instL] using result

theorem context_valid_instL {V : Type v} [SetTheory V]
    {constants : Assignment β V} {levels : List Nat} {context : Model.Context β}
    {arguments : List VLevel} {env : Nat → V}
    (valid : Context.Valid constants levels (context.map (AExpr.instL arguments)) env) :
    context.Valid constants (arguments.map (VLevel.eval levels)) env := by
  intro index type found
  have atIndex := valid index (type.instL arguments) (by
    simp only [List.getElem?_map, found, Option.map_some])
  simpa only [wellDenoted_instL, interp_instL] using atIndex

theorem typing_instL_context {entries : Model.Environment β} {context : Model.Context β}
    {term type : AExpr β} (typed : TypingClaim.{u,v} entries context term type)
    (arguments : List VLevel) :
    TypingClaim.{u,v} entries (context.map (AExpr.instL arguments))
      (term.instL arguments) (type.instL arguments) := by
  intro V _ constants realizes levels env valid
  simpa only [wellDenoted_instL, interp_instL] using
    typed V constants realizes (arguments.map (VLevel.eval levels)) env (context_valid_instL valid)

theorem context_valid_prefix {V : Type v} [SetTheory V]
    {constants : Assignment β V} {levels : List Nat} {context outer : Model.Context β}
    {env : Nat → V} (valid : (context ++ outer).Valid constants levels env) :
    context.Valid constants levels env := by
  intro index type found
  exact valid index type (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]; exact found)

theorem typing_append_context {entries : Model.Environment β} {context : Model.Context β}
    {term type : AExpr β} (typed : TypingClaim.{u,v} entries context term type)
    (outer : Model.Context β) : TypingClaim.{u,v} entries (context ++ outer) term type := by
  intro V _ constants realizes levels env valid
  exact typed V constants realizes levels env (context_valid_prefix valid)

theorem context_push_instL (context : Model.Context β) (domain : AExpr β) (arguments : List VLevel) :
    (context.push domain).map (AExpr.instL arguments) =
      Context.push (domain.instL arguments) (context.map (AExpr.instL arguments)) := by
  simp only [Context.push, List.map_cons, AExpr.instL_liftN, List.map_map, Function.comp_def]

/-- Retain the syntax of both a checked type and its reduction while moving
that original check to its use site. Every step is an explicit interface or
syntax operation; no semantic equality is stored in this transport. -/
inductive TypeReductionTransport :
    Model.Environment β → Model.Context β → AExpr β → AExpr β → VLevel →
      Model.Environment β → Model.Context β → AExpr β → AExpr β → VLevel → Type u where
  | refl {entries context source reduced level} :
      TypeReductionTransport entries context source reduced level entries context source reduced level
  | extend {origin originContext source reduced level earlier later context current result bound}
      (prior : TypeReductionTransport origin originContext source reduced level
        earlier context current result bound)
      (extension : InterfaceExtends earlier later) :
      TypeReductionTransport origin originContext source reduced level later context current result bound
  | weaken {origin originContext source reduced level entries context current result bound}
      (prior : TypeReductionTransport origin originContext source reduced level
        entries context current result bound) (domain : AExpr β) :
      TypeReductionTransport origin originContext source reduced level entries (context.push domain)
        (current.liftN 1) (result.liftN 1) bound
  | instantiate {origin originContext source reduced level entries context current result bound}
      (prior : TypeReductionTransport origin originContext source reduced level
        entries [] current result bound) (arguments : List VLevel) :
      TypeReductionTransport origin originContext source reduced level entries context
        (current.instL arguments) (result.instL arguments) (bound.inst arguments)
  | instantiateContext {origin originContext source reduced level entries context current result bound}
      (prior : TypeReductionTransport origin originContext source reduced level
        entries context current result bound) (arguments : List VLevel) :
      TypeReductionTransport origin originContext source reduced level
        entries (context.map (AExpr.instL arguments))
        (current.instL arguments) (result.instL arguments) (bound.inst arguments)
  | appendContext {origin originContext source reduced level entries context current result bound}
      (prior : TypeReductionTransport origin originContext source reduced level
        entries context current result bound) (outer : Model.Context β) :
      TypeReductionTransport origin originContext source reduced level entries (context ++ outer)
        current result bound
  | equivalent {origin originContext source reduced level entries context current result bound current' result'}
      (prior : TypeReductionTransport origin originContext source reduced level
        entries context current result bound)
      (sameSource : AExpr.LevelEquivalent current current')
      (sameResult : AExpr.LevelEquivalent result result') :
      TypeReductionTransport origin originContext source reduced level entries context current' result' bound

/-- An origin and its beta result cross a local binder together; the result
is derived by substitution algebra rather than supplied independently. -/
def TypeReductionTransport.weakenPrefix
    {origin entries : Model.Environment β} {originContext context : Model.Context β}
    {source reduced head : AExpr β} {arguments : List (AExpr β)} {level bound : VLevel} {count : Nat}
    (prior : TypeReductionTransport origin originContext source reduced level
      entries context (head.appN arguments) (AExpr.betaPrefix count head arguments) bound)
    (domain : AExpr β) :
    TypeReductionTransport origin originContext source reduced level entries (context.push domain)
      ((head.liftN 1).appN (arguments.map (AExpr.liftN 1 ·)))
      (AExpr.betaPrefix count (head.liftN 1) (arguments.map (AExpr.liftN 1 ·))) bound := by
  simpa only [AExpr.liftN_appN, AExpr.liftN_betaPrefix] using prior.weaken domain

/-- Universe instantiation preserves the complete selected beta prefix,
including all annotations, dependent substitutions, and trailing arguments. -/
def TypeReductionTransport.instantiatePrefix
    {origin entries : Model.Environment β} {originContext context : Model.Context β}
    {source reduced head : AExpr β} {arguments : List (AExpr β)} {level bound : VLevel} {count : Nat}
    (prior : TypeReductionTransport origin originContext source reduced level
      entries [] (head.appN arguments) (AExpr.betaPrefix count head arguments) bound)
    (levels : List VLevel) :
    TypeReductionTransport origin originContext source reduced level entries context
      ((head.instL levels).appN (arguments.map (AExpr.instL levels)))
      (AExpr.betaPrefix count (head.instL levels) (arguments.map (AExpr.instL levels)))
      (bound.inst levels) := by
  simpa only [AExpr.instL_appN, AExpr.instL_betaPrefix] using prior.instantiate levels

theorem TypeReductionTransport.sound
    {origin entries : Model.Environment β} {originContext context : Model.Context β}
    {source reduced current result : AExpr β} {level bound : VLevel}
    (transport : TypeReductionTransport origin originContext source reduced level
      entries context current result bound)
    (converted : ConversionClaim.{u,v} origin originContext source reduced)
    (typed : TypingClaim.{u,v} origin originContext reduced (.sort level)) :
    ConversionClaim.{u,v} entries context current result ∧
      TypingClaim.{u,v} entries context result (.sort bound) := by
  induction transport with
  | refl => exact ⟨converted, typed⟩
  | extend prior extension ih =>
      refine ⟨?_, extension.typing ih.2⟩
      intro V _ constants realizes levels env valid
      exact ih.1 V constants (extension.realizes realizes) levels env valid
  | weaken prior domain ih =>
      refine ⟨?_, typing_weaken ih.2⟩
      intro V _ constants realizes levels env valid
      simpa only [interp_liftN] using
        ih.1 V constants realizes levels _ (context_valid_tail valid)
  | instantiate prior arguments ih =>
      refine ⟨?_, typing_instL_closed ih.2 arguments⟩
      intro V _ constants realizes levels env valid
      simpa only [interp_instL] using
        ih.1 V constants realizes (arguments.map (VLevel.eval levels)) env
          (Context.valid_nil constants _ env)
  | instantiateContext prior arguments ih =>
      refine ⟨?_, typing_instL_context ih.2 arguments⟩
      intro V _ constants realizes levels env valid
      simpa only [interp_instL] using
        ih.1 V constants realizes (arguments.map (VLevel.eval levels)) env (context_valid_instL valid)
  | appendContext prior outer ih =>
      refine ⟨?_, typing_append_context ih.2 outer⟩
      intro V _ constants realizes levels env valid
      exact ih.1 V constants realizes levels env (context_valid_prefix valid)
  | equivalent prior sameSource sameResult ih =>
      refine ⟨?_, sameResult.termTyping ih.2⟩
      intro V _ constants realizes levels env valid
      exact (sameSource.interp constants levels env).symm.trans
        ((ih.1 V constants realizes levels env valid).trans (sameResult.interp constants levels env))

/-- Evidence of an executed type-inference call. The witness stores raw
syntax, states, and a finite inference tree; it contains no semantic typing
field. Its conclusion is derived below from production soundness. -/
structure CheckedType (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) (context : Model.Context β) (type : AExpr β) (level : VLevel) where
  locals : List FVarId
  fuel : Nat
  before : TcState .anon
  after : TcState .anon
  source : KExpr .anon
  result : KExpr .anon
  inference : BinderInference resolve entries locals context fuel before source type (.sort level)
  agreement : LocalContextReading resolve locals before.lctx context
  reading : readScopedExpr? resolve locals source = some type.erase
  run : RecM.infer source (methodsN fuel) before = .ok result after

theorem CheckedType.sound {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {context : Model.Context β} {type : AExpr β} {level : VLevel}
    (checked : CheckedType resolve entries context type level) :
    TypingClaim.{u,v} entries context type (.sort level) :=
  (checked.inference.sound checked.agreement checked.reading checked.run).2.typingSort

/-- Formation facts retain their executed origin while being transported
through the operations needed by later inference. -/
inductive TypeFormation (resolve : Address → Option (ConstRef β)) :
    Model.Environment β → Model.Context β → AExpr β → VLevel → Type u where
  | checked {entries context type level}
      (origin : CheckedType resolve entries context type level) :
      TypeFormation resolve entries context type level
  | sort {entries context} (level : VLevel) :
      TypeFormation resolve entries context (.sort level) (.succ level)
  | extend {earlier later context type level}
      (extension : InterfaceExtends earlier later)
      (prior : TypeFormation resolve earlier context type level) :
      TypeFormation resolve later context type level
  | weaken {entries context type level} (domain : AExpr β)
      (prior : TypeFormation resolve entries context type level) :
      TypeFormation resolve entries (context.push domain) (type.liftN 1) level
  | instantiate {entries context type level} (arguments : List VLevel)
      (prior : TypeFormation resolve entries [] type level) :
      TypeFormation resolve entries context (type.instL arguments) (level.inst arguments)
  | equivalent {entries context type type' level}
      (same : AExpr.LevelEquivalent type type')
      (prior : TypeFormation resolve entries context type level) :
      TypeFormation resolve entries context type' level
  | forallE {entries context domain body domainLevel bodyLevel}
      (domainFormation : TypeFormation resolve entries context domain domainLevel)
      (bodyFormation : TypeFormation resolve entries (context.push domain) body bodyLevel) :
      TypeFormation resolve entries context
        (.forallE (Certified.zeroCondition bodyLevel) domain body) (.imax domainLevel bodyLevel)

theorem TypeFormation.sound {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {context : Model.Context β} {type : AExpr β} {level : VLevel}
    (formation : TypeFormation resolve entries context type level) :
    TypingClaim.{u,v} entries context type (.sort level) := by
  induction formation with
  | checked origin => exact origin.sound
  | sort level => exact TypingClaim.sort level
  | extend extension prior ih => exact extension.typing ih
  | weaken domain prior ih => exact typing_weaken ih
  | instantiate arguments prior ih => exact typing_instL_closed ih arguments
  | equivalent same prior ih => exact same.termTyping ih
  | forallE domain body ihDomain ihBody => exact TypingClaim.forallE ihDomain ihBody rfl

/-- The levels carried for local declarations refer to their types, all
expressed in the current context. Binder inference derives each new entry
from the executed domain check. -/
def ContextFormation (entries : Model.Environment β) (context : Model.Context β)
    (bounds : List VLevel) : Prop :=
  ∀ (index : Nat) type level, context[index]? = some type → bounds[index]? = some level →
    TypingClaim.{u,v} entries context type (.sort level)

theorem ContextFormation.empty (entries : Model.Environment β) :
    ContextFormation.{u,v} entries [] [] := by
  intro index type level found
  simp at found

theorem ContextFormation.push {entries : Model.Environment β} {context : Model.Context β}
    {bounds : List VLevel} {domain : AExpr β} {level : VLevel}
    (formed : ContextFormation.{u,v} entries context bounds)
    (domainFormed : TypingClaim.{u,v} entries context domain (.sort level)) :
    ContextFormation.{u,v} entries (context.push domain) (level :: bounds) := by
  intro index type bound found indexed
  cases index with
  | zero =>
      simp only [Context.push, List.getElem?_cons_zero, Option.some.injEq] at found indexed
      subst type bound
      exact typing_weaken domainFormed
  | succ index =>
      simp only [Context.push, List.getElem?_cons_succ, List.getElem?_map] at found
      obtain ⟨prior, priorFound, rfl⟩ := Option.map_eq_some_iff.mp found
      exact typing_weaken (formed index prior bound priorFound indexed)

end Ix.Kernel.Consistency
