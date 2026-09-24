/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Certified/Structure/Computation.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added;
K2: the input store and its exact-source facts are removed and the recursor is
member 1 of the family's block.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.Structure.Reading

namespace Ix.Kernel.Certified.Structure.Description

open Model Model.SetTheory Model.SetTheory.Tower Model.SetModel Ordinary

universe u v
variable {β : Type u} {V : Type v} [SetTheory V]
  {d : Description β} {entries : Environment β} {source : β}
  {constants reading : Assignment β V} {levels : List Nat}

theorem constructorApp_interp (h : CheckedShape.{u,v} entries source d.ordinary)
    (hr : ConstructorReading entries d.ordinary source constants reading) (hM : Realizes constants entries)
    (hn : levels.length = d.universes) {ps xs : List V}
    (hps : FitsS (Telescope.interpret constants levels (fun _ => empty) d.parameters) ps)
    (hxs : FitsS (Telescope.interpret constants levels (Telescope.extend (fun _ => empty) ps) d.constructor.fields) xs)
    (env : Nat → V) (args : List (AExpr β)) (hargs : args.map (interp reading levels env) = ps ++ xs) :
    interp reading levels env (.appN (.const (.ctor source 0 0) (VLevel.params d.universes)) args) =
      d.ordinary.constructorValue constants levels (Telescope.extend (fun _ => empty) ps) d.constructor 0 xs [] := by
  rw [AExpr.interp_appN, interp, eval_params hn, hr.constructor levels hn 0 d.constructor rfl, hargs]
  simpa only [List.append_nil] using Shape.constructorClosedValue_apply h hM
    (show d.ordinary.constructors[0]? = some d.constructor from rfl) hps hxs
    (show d.ordinary.RecursiveValuesFit constants levels (Telescope.extend (fun _ => empty) ps) d.constructor xs [] from trivial)

theorem eta_eq (h : CheckedShape.{u,v} entries source d.ordinary)
    (hF : FieldsFormed.{u,v} entries d.level d.ordinary.parameterContext d.fields)
    (hr : ConstructorReading entries d.ordinary source constants reading) (hM : Realizes constants entries)
    (hn : levels.length = d.universes) :
    interp reading levels (fun _ => empty) (d.etaLhs source) =
      interp reading levels (fun _ => empty) (d.etaRhs source) := by
  simp only [etaLhs, etaRhs, projectionDomains, AExpr.lamN_append, AExpr.interp_lamN,
    hr.agrees.telescope (fun A hA => h.references A (by simpa [ordinary] using hA))]
  apply Telescope.curry_congr
  intro ps hps
  change lamR _ (interp reading levels _ (d.ordinary.familyApp source 0 [])) _ = lamR _ _ _
  apply lamR_congr
  intro x hx
  have he := Shape.familyApp_interp hr.toFamilyReading hn (extra := []) (indices := []) hps (by trivial)
  have hx' : x ∈ˢ app (d.ordinary.carrier constants levels (Telescope.extend (fun _ => empty) ps)) pt := by
    simpa only [List.length_nil, List.map_nil, mkTower, Telescope.extend] using he ▸ hx
  have hΓ := h.parameters.valid constants hM levels (Context.valid_nil constants levels (fun _ => empty)) hps
  have hxs := d.projections_fit h hF hM hΓ hx'
  change interp reading levels (Valuation.cons x _) (.appN _ _) = x
  rw [d.constructorApp_interp h hr hM hn hps hxs _ _ (by
    rw [List.map_append, projections_interp, interp_parameterVars_skip,
      Valuation.skip_succ_cons, Valuation.skip_zero, ← FitsS.length_eq hps, interp_parameterVars_extend]
    rfl)]
  exact d.constructor_eta h hM hΓ hx'

theorem iota_eq (h : CheckedShape.{u,v} entries source d.ordinary)
    (hF : FieldsFormed.{u,v} entries d.level d.ordinary.parameterContext d.fields)
    (hr : ConstructorReading entries d.ordinary source constants reading) (hM : Realizes constants entries)
    (hn : levels.length = d.universes) {i : Nat} {field : Field β} (hi : d.fields[i]? = some field) :
    interp reading levels (fun _ => empty) (d.iotaLhs source i field) =
      interp reading levels (fun _ => empty) (d.iotaRhs i field) := by
  simp only [iotaLhs, iotaRhs, AExpr.lamN_append, AExpr.interp_lamN,
    hr.agrees.telescope (fun A hA => h.references A (by simpa [ordinary] using hA))]
  apply Telescope.curry_congr
  intro ps hps
  rw [hr.agrees.telescope (fun A hA => (h.constructors d.constructor (by simp [ordinary])).1 A
    (List.mem_append_left _ hA))]
  apply Telescope.curry_congr
  intro xs hxs
  have hΓ := h.parameters.valid constants hM levels (Context.valid_nil constants levels (fun _ => empty)) hps
  have hlen : xs.length = d.fields.length := by simpa [constructor] using FitsS.length_eq hxs
  have hib := (List.getElem?_eq_some_iff.mp hi).1
  change projectValue i (interp reading levels _ (.appN _ _)) = _
  rw [d.constructorApp_interp h hr hM hn hps hxs _ _ (by
    rw [← Telescope.extend_append]
    have hlength : (ps ++ xs).length = d.parameters.length + d.fields.length := by
      rw [List.length_append, FitsS.length_eq hps, hlen]
    rw [← hlength, interp_parameterVars_extend])]
  have he := congrArg (fun zs : List V => zs.getD i empty) (d.constructor_iota hF hM hΓ hxs)
  rw [projectValues_getD _ _ _ hib] at he
  rw [he]
  symm
  simpa only [interp, hlen] using Telescope.extend_getD (Telescope.extend (fun _ => empty) ps) xs i (by omega)

end Ix.Kernel.Certified.Structure.Description
