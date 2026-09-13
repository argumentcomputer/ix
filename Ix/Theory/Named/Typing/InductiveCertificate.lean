/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Std.AxiomAudit
import Ix.Theory.Named.Typing.EnvLemmas
import Ix.Theory.Named.Typing.InductivePattern
import Ix.Theory.Named.Typing.NestedInductiveLemmas

/-!
# Consumer certificates for completed inductive blocks

`BlockGenerationCertificate` is the semantic input to the block transaction.
This module packages that input with one successful transaction and a
well-formed dependency environment, then exports the stable consequences a
consumer needs.  The package contains only Theory values and proofs: no
implementation metadata, checker state, or normalization execution crosses
this boundary.

In particular, `BlockCertificate.ruleClosure` derives the closed payload
required by the generated-pattern API from the registered, well-formed iota
rules in the completed environment.  A consumer therefore does not need a
second closedness assumption in order to use `IotaPat`.
-/

namespace Ix.Theory.Named

namespace VInductDecl

/-- One successful proof-carrying block transaction over an explicit
dependency environment. -/
structure BlockCertificate (source : VInductDecl) (before after : VEnv) where
  semantic : source.BlockGenerationCertificate before
  success : before.addInductBlockCertified semantic = some after
  beforeWF : before.WF

namespace BlockCertificate

variable {source : VInductDecl} {before after : VEnv}

/-- Package the ordinary raw `addInduct` entry point once its accepted block
descriptor and semantic proof are known.  This is the compatibility bridge
for consumers that still execute `addInduct`; no second transaction is run. -/
def ofAddInduct
    (generation : source.BlockGenerationChecked) (blockEnv : VEnv)
    (hidentity : source.identityBlockGeneration? = some generation)
    (hwf : generation.WF before blockEnv) (hbefore : before.WF)
    (hadd : before.addInduct source = some after) :
    BlockCertificate source before after where
  semantic := ⟨generation, blockEnv, hwf⟩
  success := by
    unfold VEnv.addInduct at hadd
    rw [hidentity] at hadd
    exact hadd
  beforeWF := hbefore

/-- The exact generation descriptor retained by a completed block. -/
abbrev generation (certificate : BlockCertificate source before after) :
    source.BlockGenerationChecked :=
  certificate.semantic.generation

/-- Recover the four exact insertion phases of the completed block. -/
theorem trace (certificate : BlockCertificate source before after) :
    Nonempty (VEnv.AddInductBlockGenerationTrace before after
      certificate.generation) :=
  VEnv.addInductBlockCertified_trace certificate.success

/-- The completed transaction is a genuine block declaration step. -/
theorem declWF (certificate : BlockCertificate source before after) :
    VDecl.WF before (.induct source) after := by
  apply VDecl.WF.inductBlock certificate.semantic.wf
  simpa only [VEnv.addInductBlockCertified_eq_addInductBlockGeneration] using
    certificate.success

/-- Extend the dependency-environment history with the certified block. -/
theorem afterWF (certificate : BlockCertificate source before after) :
    after.WF := by
  rcases certificate.beforeWF with ⟨decls, hdecls⟩
  exact ⟨.induct source :: decls, hdecls.decl certificate.declWF⟩

/-- A completed block only grows its dependency environment. -/
theorem envLE (certificate : BlockCertificate source before after) :
    before ≤ after := by
  rcases certificate.trace with ⟨trace⟩
  exact trace.le

/-- Compatibility spelling for consumers of the historical
`addInduct_le` growth theorem. -/
theorem addInduct_le (certificate : BlockCertificate source before after) :
    before ≤ after :=
  certificate.envLE

/-- Compatibility spelling for the preservation result traditionally
exported as `addInduct_WF`. -/
theorem addInduct_WF (certificate : BlockCertificate source before after) :
    after.WF :=
  certificate.afterWF

/-- Recover success through the ordinary raw API when this certificate's
descriptor is the declaration's identity descriptor. -/
theorem addInduct
    (certificate : BlockCertificate source before after)
    (hidentity : source.identityBlockGeneration? =
      some certificate.generation) :
    before.addInduct source = some after := by
  unfold VEnv.addInduct
  rw [hidentity]
  simpa [VEnv.addInductBlockCertified] using certificate.success

/-- Every source family has its exact stored Theory value in the completed
environment. -/
theorem familyLookup (certificate : BlockCertificate source before after)
    {family : VInductiveType} (hfamily : family ∈ source.types) :
    after.constants family.name = some family.toVConstant := by
  rcases certificate.trace with ⟨trace⟩
  exact trace.family_lookup hfamily

/-- Every flattened source constructor has its exact stored Theory value in
the completed environment. -/
theorem constructorLookup
    (certificate : BlockCertificate source before after)
    {constructor : VConstVal}
    (hconstructor : constructor ∈ source.blockConstructorConstants) :
    after.constants constructor.name = some constructor.toVConstant := by
  rcases certificate.trace with ⟨trace⟩
  exact trace.ctor_lookup hconstructor

/-- Every generated family recursor has its exact Theory value in the
completed environment. -/
theorem recursorLookup
    (certificate : BlockCertificate source before after)
    {recursor : VConstVal}
    (hrecursor : recursor ∈ certificate.generation.recursors) :
    after.constants recursor.name = some recursor.toVConstant := by
  rcases certificate.trace with ⟨trace⟩
  exact trace.rec_lookup hrecursor

/-- A source family name was fresh at the dependency boundary. -/
theorem familyFresh (certificate : BlockCertificate source before after)
    {family : VInductiveType} (hfamily : family ∈ source.types) :
    before.constants family.name = none := by
  rcases certificate.trace with ⟨trace⟩
  exact trace.family_fresh hfamily

/-- A flattened source constructor name was fresh at the dependency
boundary. -/
theorem constructorFresh
    (certificate : BlockCertificate source before after)
    {constructor : VConstVal}
    (hconstructor : constructor ∈ source.blockConstructorConstants) :
    before.constants constructor.name = none := by
  rcases certificate.trace with ⟨trace⟩
  exact trace.ctor_fresh hconstructor

/-- A generated recursor name was fresh at the dependency boundary. -/
theorem recursorFresh
    (certificate : BlockCertificate source before after)
    {recursor : VConstVal}
    (hrecursor : recursor ∈ certificate.generation.recursors) :
    before.constants recursor.name = none := by
  rcases certificate.trace with ⟨trace⟩
  exact trace.rec_fresh hrecursor

/-- Every generated rule is registered by the completed transaction. -/
theorem ruleRegistered
    (certificate : BlockCertificate source before after)
    {rule : VDefEq}
    (hrule : rule ∈ certificate.generation.generatedRules) :
    after.defeqs rule := by
  rcases certificate.trace with ⟨trace⟩
  exact trace.rule_mem hrule

/-- Every generated rule is well formed in the completed environment. -/
theorem ruleWF
    (certificate : BlockCertificate source before after)
    {rule : VDefEq}
    (hrule : rule ∈ certificate.generation.generatedRules) :
    rule.WF after :=
  certificate.afterWF.ordered.defEqWF (certificate.ruleRegistered hrule)

/-- An exact family lookup is unique.  This small eliminator is convenient
for consumers that translate their own family representation to a Theory
constant and then compare it with the certificate inventory. -/
theorem familyLookup_unique
    (certificate : BlockCertificate source before after)
    {family : VInductiveType} (hfamily : family ∈ source.types)
    {constant : VConstant}
    (hlookup : after.constants family.name = some constant) :
    constant = family.toVConstant := by
  exact Option.some.inj (hlookup.symm.trans (certificate.familyLookup hfamily))

/-- An exact constructor lookup is unique. -/
theorem constructorLookup_unique
    (certificate : BlockCertificate source before after)
    {constructor : VConstVal}
    (hconstructor : constructor ∈ source.blockConstructorConstants)
    {constant : VConstant}
    (hlookup : after.constants constructor.name = some constant) :
    constant = constructor.toVConstant := by
  exact Option.some.inj
    (hlookup.symm.trans (certificate.constructorLookup hconstructor))

/-- An exact generated-recursor lookup is unique. -/
theorem recursorLookup_unique
    (certificate : BlockCertificate source before after)
    {recursor : VConstVal}
    (hrecursor : recursor ∈ certificate.generation.recursors)
    {constant : VConstant}
    (hlookup : after.constants recursor.name = some constant) :
    constant = recursor.toVConstant := by
  exact Option.some.inj
    (hlookup.symm.trans (certificate.recursorLookup hrecursor))

private theorem rule_mem_generatedRules
    (generation : source.BlockGenerationChecked)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (hentry : generation.flatCtors[i]? = some constructor) :
    generation.rule i constructor ∈ generation.generatedRules := by
  apply List.mem_map.2
  refine ⟨(constructor, i), ?_, rfl⟩
  apply List.mem_of_getElem? (i := i)
  rw [List.getElem?_zipIdx, hentry, Option.map_some, Nat.zero_add]

private theorem closedN_lamN_body :
    ∀ {binders : List VExpr} {body : VExpr} {k : Nat},
      (VExpr.lamN binders body).ClosedN k →
        body.ClosedN (k + binders.length)
  | [], _, _, h => by
      simpa only [VExpr.lamN, List.length_nil, Nat.add_zero] using h
  | _ :: binders, body, k, h => by
      have hbody := closedN_lamN_body (binders := binders)
        (body := body) (k := k + 1) h.2
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbody

private theorem closedN_lamN_replace :
    ∀ {binders : List VExpr} {body body' : VExpr} {k : Nat},
      (VExpr.lamN binders body).ClosedN k →
      body'.ClosedN (k + binders.length) →
        (VExpr.lamN binders body').ClosedN k
  | [], _, _, _, _, hbody' => by
      simpa only [VExpr.lamN, List.length_nil, Nat.add_zero] using hbody'
  | _ :: binders, body, body', k, h, hbody' => by
      refine ⟨h.1, closedN_lamN_replace (binders := binders)
        (body := body) (body' := body') (k := k + 1) h.2 ?_⟩
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbody'

private theorem closedN_appN_function :
    ∀ {function : VExpr} {arguments : List VExpr} {k : Nat},
      (VExpr.appN function arguments).ClosedN k → function.ClosedN k
  | _, [], _, h => by simpa only [VExpr.appN] using h
  | function, argument :: arguments, k, h =>
      (closedN_appN_function (function := function.app argument)
        (arguments := arguments) (k := k) h).1

private theorem closedN_appN_argument
    {function : VExpr} {arguments : List VExpr} {k : Nat}
    (hclosed : (VExpr.appN function arguments).ClosedN k)
    {argument : VExpr} (hargument : argument ∈ arguments) :
    argument.ClosedN k := by
  induction arguments generalizing function with
  | nil => simp at hargument
  | cons head tail ih =>
    rcases List.mem_cons.1 hargument with heq | htail
    · rw [heq]
      exact (closedN_appN_function
        (function := function.app head) (arguments := tail)
        (k := k) hclosed).2
    · exact ih (function := function.app head) hclosed htail

/-- The successful block transaction supplies the closedness bundle required
by `IotaPat`.  Closedness is derived from the registered rules and the
completed environment's ordinary WF history; it is not an additional
consumer assumption. -/
theorem ruleClosure
    (certificate : BlockCertificate source before after) :
    certificate.generation.RuleClosure := by
  constructor
  · intro i constructor hentry
    have hmem := rule_mem_generatedRules certificate.generation hentry
    exact (certificate.ruleWF hmem).2.closedN
      certificate.afterWF.ordered trivial
  · intro constructor hconstructor expression hexpression
    obtain ⟨i, hentry⟩ := List.mem_iff_getElem?.1 hconstructor
    have hmem := rule_mem_generatedRules certificate.generation hentry
    have hlhs := (certificate.ruleWF hmem).1.closedN
      certificate.afterWF.ordered trivial
    rw [certificate.generation.rule_lhs i constructor] at hlhs
    have hbody := closedN_lamN_body hlhs
    have hexpression' : expression ∈
        certificate.generation.ruleIdx constructor ++
          [certificate.generation.ruleCtorApp constructor] :=
      List.mem_append.2 (.inl hexpression)
    have hclosed : expression.ClosedN
        (certificate.generation.ruleBinders constructor).length := by
      apply closedN_appN_argument
        (function := certificate.generation.recBase
          (certificate.generation.ruleFieldCount constructor)
          constructor.owner)
        (arguments := certificate.generation.ruleIdx constructor ++
          [certificate.generation.ruleCtorApp constructor])
      · simpa only [BlockGenerationChecked.ruleLhsBody, List.length_nil,
          Nat.zero_add] using hbody
      · exact hexpression'
    apply closedN_lamN_replace hlhs
    simpa using hclosed

/-- The exact generated pattern and payload associated with one flattened
rule entry. -/
theorem recursorPattern
    (certificate : BlockCertificate source before after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (hentry : certificate.generation.ruleEntry i constructor) :
    certificate.generation.IotaPat certificate.ruleClosure
      ((certificate.generation.rulePattern constructor).toPattern)
      (certificate.generation.ruleRHS certificate.ruleClosure hentry,
        certificate.generation.ruleCheck certificate.ruleClosure
          (List.mem_of_getElem? hentry)) :=
  .mk hentry

/-- Rule-level consumer bundle: exact global position, generated-list
membership, registration, well-formedness, and the corresponding iota-pattern
pattern all come from the same completed block. -/
structure RecursorRuleFacts
    (certificate : BlockCertificate source before after)
    (i : Nat) (constructor : NormalizedBlockCtor) : Prop where
  entry : certificate.generation.ruleEntry i constructor
  member : certificate.generation.rule i constructor ∈
    certificate.generation.generatedRules
  registered : after.defeqs (certificate.generation.rule i constructor)
  wf : (certificate.generation.rule i constructor).WF after
  pattern : certificate.generation.IotaPat certificate.ruleClosure
    ((certificate.generation.rulePattern constructor).toPattern)
    (certificate.generation.ruleRHS certificate.ruleClosure entry,
      certificate.generation.ruleCheck certificate.ruleClosure
        (List.mem_of_getElem? entry))

/-- Assemble all rule facts without a consumer-supplied semantic premise. -/
theorem recursorRuleFacts
    (certificate : BlockCertificate source before after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (hentry : certificate.generation.ruleEntry i constructor) :
    certificate.RecursorRuleFacts i constructor := by
  have hmember := rule_mem_generatedRules certificate.generation hentry
  exact {
    entry := hentry
    member := hmember
    registered := certificate.ruleRegistered hmember
    wf := certificate.ruleWF hmember
    pattern := certificate.recursorPattern hentry }

end BlockCertificate

/-! ## Completed nested transactions -/

/-- One successful proof-carrying nested transaction over an explicit
dependency environment.  As with `BlockCertificate`, this package contains
only Theory artifacts. -/
structure NestedBlockCertificate
    (source : VInductDecl) (before after : VEnv) where
  nested : source.NestedBlockChecked
  semantic : nested.WF before
  success : before.addInductNested nested = some after
  beforeWF : before.WF

namespace NestedBlockCertificate

variable {source : VInductDecl} {before after : VEnv}

/-- Recover the exact four-phase nested transaction trace. -/
theorem trace (certificate : NestedBlockCertificate source before after) :
    Nonempty (VEnv.AddInductNestedTrace before after certificate.nested) :=
  VEnv.addInductNested_trace certificate.success

/-- The nested completion is a genuine inductive declaration step. -/
theorem declWF (certificate : NestedBlockCertificate source before after) :
    VDecl.WF before (.induct source) after :=
  .inductNested certificate.semantic certificate.success

/-- Extend the dependency-environment history with the nested block. -/
theorem afterWF (certificate : NestedBlockCertificate source before after) :
    after.WF := by
  rcases certificate.beforeWF with ⟨decls, hdecls⟩
  exact ⟨.induct source :: decls, hdecls.decl certificate.declWF⟩

/-- A completed nested transaction only grows its dependency environment. -/
theorem envLE (certificate : NestedBlockCertificate source before after) :
    before ≤ after :=
  VEnv.addInductNested_le certificate.success

/-- Nested analogue of the public block growth result. -/
theorem addInduct_le
    (certificate : NestedBlockCertificate source before after) :
    before ≤ after :=
  certificate.envLE

/-- Nested analogue of the public block preservation result. -/
theorem addInduct_WF
    (certificate : NestedBlockCertificate source before after) :
    after.WF :=
  certificate.afterWF

/-- Every stored source family has its exact final value. -/
theorem familyLookup (certificate : NestedBlockCertificate source before after)
    {family : VInductiveType} (hfamily : family ∈ source.types) :
    after.constants family.name = some family.toVConstant := by
  rcases certificate.trace with ⟨trace⟩
  exact trace.family_lookup hfamily

/-- Every stored source constructor has its exact final value. -/
theorem constructorLookup
    (certificate : NestedBlockCertificate source before after)
    {family : VInductiveType} (hfamily : family ∈ source.types)
    {constructor : VConstVal} (hconstructor : constructor ∈ family.ctors) :
    after.constants constructor.name = some constructor.toVConstant := by
  rcases certificate.trace with ⟨trace⟩
  exact trace.ctor_lookup hfamily hconstructor

/-- Every restored recursor has its exact final value. -/
theorem recursorLookup
    (certificate : NestedBlockCertificate source before after)
    {recursor : VConstVal} (hrecursor : recursor ∈ certificate.nested.recursors) :
    after.constants recursor.name = some recursor.toVConstant := by
  rcases certificate.trace with ⟨trace⟩
  exact trace.rec_lookup hrecursor

/-- Every source family name was fresh at the dependency boundary. -/
theorem familyFresh (certificate : NestedBlockCertificate source before after)
    {family : VInductiveType} (hfamily : family ∈ source.types) :
    before.constants family.name = none := by
  rcases certificate.trace with ⟨trace⟩
  exact trace.family_fresh hfamily

/-- Every flattened source constructor name was fresh at the dependency
boundary. -/
theorem constructorFresh
    (certificate : NestedBlockCertificate source before after)
    {constructor : VConstVal}
    (hconstructor : constructor ∈ source.blockConstructorConstants) :
    before.constants constructor.name = none := by
  rcases certificate.trace with ⟨trace⟩
  exact trace.ctor_fresh hconstructor

/-- Every restored recursor name was fresh at the dependency boundary. -/
theorem recursorFresh
    (certificate : NestedBlockCertificate source before after)
    {recursor : VConstVal} (hrecursor : recursor ∈ certificate.nested.recursors) :
    before.constants recursor.name = none := by
  rcases certificate.trace with ⟨trace⟩
  exact trace.rec_fresh hrecursor

/-- Every restored rule is registered in the completed environment. -/
theorem ruleRegistered
    (certificate : NestedBlockCertificate source before after)
    {rule : VDefEq} (hrule : rule ∈ certificate.nested.generatedRules) :
    after.defeqs rule := by
  rcases certificate.trace with ⟨trace⟩
  exact trace.rule_mem hrule

/-- Every registered restored rule is well formed. -/
theorem ruleWF
    (certificate : NestedBlockCertificate source before after)
    {rule : VDefEq} (hrule : rule ∈ certificate.nested.generatedRules) :
    rule.WF after :=
  certificate.afterWF.ordered.defEqWF (certificate.ruleRegistered hrule)

/-- Exact family lookups are unique. -/
theorem familyLookup_unique
    (certificate : NestedBlockCertificate source before after)
    {family : VInductiveType} (hfamily : family ∈ source.types)
    {constant : VConstant}
    (hlookup : after.constants family.name = some constant) :
    constant = family.toVConstant :=
  Option.some.inj (hlookup.symm.trans (certificate.familyLookup hfamily))

/-- Exact constructor lookups are unique. -/
theorem constructorLookup_unique
    (certificate : NestedBlockCertificate source before after)
    {family : VInductiveType} (hfamily : family ∈ source.types)
    {constructor : VConstVal} (hconstructor : constructor ∈ family.ctors)
    {constant : VConstant}
    (hlookup : after.constants constructor.name = some constant) :
    constant = constructor.toVConstant :=
  Option.some.inj
    (hlookup.symm.trans (certificate.constructorLookup hfamily hconstructor))

/-- Exact restored-recursor lookups are unique. -/
theorem recursorLookup_unique
    (certificate : NestedBlockCertificate source before after)
    {recursor : VConstVal} (hrecursor : recursor ∈ certificate.nested.recursors)
    {constant : VConstant}
    (hlookup : after.constants recursor.name = some constant) :
    constant = recursor.toVConstant :=
  Option.some.inj
    (hlookup.symm.trans (certificate.recursorLookup hrecursor))

end NestedBlockCertificate

end VInductDecl

end Ix.Theory.Named

/-! ## Exact Theory trust guards -/

#guard_named_axioms Ix.Theory.Named.VInductDecl.BlockCertificate.afterWF [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.BlockCertificate.ruleClosure [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.BlockCertificate.recursorRuleFacts [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.NestedBlockCertificate.afterWF [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.NestedBlockCertificate.ruleWF [propext, Classical.choice, Quot.sound]
