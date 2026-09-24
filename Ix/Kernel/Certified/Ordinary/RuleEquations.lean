/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Certified/Ordinary/RuleEquations.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added;
K2: the input store and its exact-source facts are removed (comparing the
stored block with the generated one is the caller's check) and the recursor is
member 1 of the family's block.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.Ordinary.RuleReading

namespace Ix.Kernel.Certified.Ordinary.Shape

open Model Model.SetTheory Model.SetTheory.Tower Model.SetModel Inductive

universe u v
variable {β : Type u} {V : Type v} [SetTheory V]
  {entries : Environment β} {shape : Shape β} {source : β}
  {constants reading : Assignment β V} {levels : List Nat} {mode : ElimMode}

theorem ruleFields_curry (h : CheckedShape.{u,v} entries source shape)
    (hr : FamilyReading entries shape source constants reading) (hM : Realizes constants entries)
    (hn : levels.length = mode.recUvars shape.universes) {ctor : Constructor β} (hc : ctor ∈ shape.constructors)
    {ps minors : List V}
    (hps : FitsS (Telescope.interpret constants (mode.sourceArgs levels) (fun _ => empty) shape.parameters) ps)
    (hmlen : minors.length = shape.constructors.length) (m : V) (w : Nat) (f : List V → V) :
    Telescope.curry w (Telescope.interpret reading levels
      (Telescope.extend (Valuation.cons m (Telescope.extend (fun _ => empty) ps)) minors)
      (Telescope.lift (1 + shape.constructors.length) ((ctor.fields ++ ctor.recursiveTypes shape source).map
        (AExpr.instL (mode.sourceLevels shape.universes))))) f =
      Telescope.curry w
        (Telescope.interpret constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps) ctor.fields)
        (fun xs => Telescope.curry w
          (Telescope.simple (ctor.recursive.map
            (shape.recursiveSet constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps) xs)))
          (fun fs => f (xs ++ fs))) := by
  have hskip : Valuation.skip (1 + shape.constructors.length) 0
      (Telescope.extend (Valuation.cons m (Telescope.extend (fun _ => empty) ps)) minors) =
      Telescope.extend (fun _ => empty) ps := by
    have ht := Telescope.skip_extend (Telescope.extend (fun _ => empty) ps) (m :: minors)
    simpa only [List.length_cons, hmlen, Telescope.extend, Nat.add_comm] using ht
  rw [Telescope.curry_lift, hskip, Telescope.curry_instL, mode.sourceLevels_eval hn,
    Telescope.curry_append,
    hr.agrees.telescope (fun A ha => (h.constructors ctor hc).1 A (List.mem_append_left _ ha))]
  apply Telescope.curry_congr
  intro xs hxs
  have ht := curry_recursiveTypes h hr hM (mode.sourceArgs_length hn) hc (fun _ h => h) hps hxs [] w
    (fun fs => f (xs ++ fs))
  simpa only [Constructor.recursiveTypes, List.length_nil, Telescope.extend] using ht

/-- Equality of the complete lambda-abstracted rule, including parameters,
the motive, every minor premise, and all constructor fields. -/
theorem large_rule_eq (h : CheckedShape.{u,v} entries source shape)
    (hr : RecursorReading entries shape source .large constants reading)
    (hmode : ModeEvidence.{u,v} entries shape .large) (hM : Realizes constants entries)
    (hn : levels.length = ElimMode.large.recUvars shape.universes) {i : Nat} {ctor : Constructor β}
    (hc : shape.constructors[i]? = some ctor) :
    interp reading levels (fun _ => empty) (shape.ruleLhs source .large i ctor) =
      interp reading levels (fun _ => empty) (shape.ruleRhs source .large i ctor) := by
  simp only [ruleLhs, ruleRhs, ruleBinders, AExpr.lamN_append, AExpr.interp_lamN,
    Telescope.curry_instL, ElimMode.sourceLevels_eval _ hn,
    hr.agrees.telescope (fun A ha => h.references A (List.mem_append_left _ ha))]
  apply Telescope.curry_congr
  intro ps hps
  change lamR _ (interp reading levels _ (shape.motiveType source .large)) _ = lamR _ _ _
  rw [motiveType_interp hr.toFamilyReading hn hps (fun A ha => h.references A (List.mem_append_right _ ha))]
  apply lamR_congr
  intro m hm
  change Telescope.curry _ (Telescope.interpret reading levels
    (Valuation.cons m (Telescope.extend (fun _ => empty) ps)) (shape.minorTypesSyntax source .large)) _ =
    Telescope.curry _ (Telescope.interpret reading levels
      (Valuation.cons m (Telescope.extend (fun _ => empty) ps)) (shape.minorTypesSyntax source .large)) _
  simp only [Telescope.extend]
  simp only [minorTypes_curry h hr.toConstructorReading hM hn hps m]
  apply Telescope.curry_congr
  intro minors hminors
  have hmlen : minors.length = shape.constructors.length := by
    simpa only [minorTypes, List.length_map, List.length_zipIdx] using FitsS.length_eq hminors
  simp only [ruleFields_curry h hr.toFamilyReading hM hn (List.mem_of_getElem? hc) hps hmlen m]
  apply Telescope.curry_congr
  intro xs hxs
  apply Telescope.curry_congr
  intro fs hfs
  simp only [Telescope.extend_append]
  exact large_ruleBody_eq h hr hmode hM hn hc hps hxs hfs hm hminors

theorem large_rule_eq_closed (h : CheckedShape.{u,v} entries source shape)
    (hr : RecursorReading entries shape source .large constants reading)
    (hmode : ModeEvidence.{u,v} entries shape .large) (hM : Realizes constants entries)
    (hn : levels.length = ElimMode.large.recUvars shape.universes) {i : Nat} {ctor : Constructor β}
    (hc : shape.constructors[i]? = some ctor)
    (hscope : (shape.ruleLhs source .large i ctor).Scope (ElimMode.large.recUvars shape.universes) 0 ∧
      (shape.ruleRhs source .large i ctor).Scope (ElimMode.large.recUvars shape.universes) 0)
    (env : Nat → V) :
    interp reading levels env (shape.ruleLhs source .large i ctor) =
      interp reading levels env (shape.ruleRhs source .large i ctor) := by
  rw [← interp_closed _ _ _ hscope.1 (fun _ => empty) env,
    ← interp_closed _ _ _ hscope.2 (fun _ => empty) env]
  exact large_rule_eq h hr hmode hM hn hc

variable [DecidableEq β]

theorem produced_rule_eq (h : CheckedShape.{u,v} entries source shape)
    (hE : entries.WF) (hC : ConstructorFormation.{u,v} entries shape source)
    (hR : RecursorFormation.{u,v} entries shape source mode)
    (hmode : ModeEvidence.{u,v} entries shape mode) (hM : Realizes constants entries)
    (hn : levels.length = mode.recUvars shape.universes) {i : Nat} {ctor : Constructor β}
    (hc : shape.constructors[i]? = some ctor)
    (hRule : RuleFormation.{u,v} (shape.recursorEnvironment entries source mode)
      shape source mode i ctor) (env : Nat → V) :
    interp (shape.recursorAssignment constants source mode) levels env (shape.ruleLhs source mode i ctor) =
      interp (shape.recursorAssignment constants source mode) levels env (shape.ruleRhs source mode i ctor) := by
  cases mode with
  | small =>
    exact small_rule_eq hRule _ (recursorAssignment_realizes h hE hC hR hmode constants hM) levels env
  | large =>
    exact large_rule_eq_closed h (recursorAssignment_reading h hR constants) hmode hM hn hc hRule.scope env

end Ix.Kernel.Certified.Ordinary.Shape
