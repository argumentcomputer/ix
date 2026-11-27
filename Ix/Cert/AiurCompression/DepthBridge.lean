import Aiur.Tiling.Claims
import Aiur.Tiling.Grouped
import Aiur.Plonk.SharedSound
import Aiur.Library.Field.BN254
import Aiur.Library.Field.BLS12381.Prime

/-! # Exempt-SCC Depth-Certificate Bridge (`Physical.Prepared.DepthCertified`)

The deployed Aiur compiler and exporter emit depth configurations certified by
`Aiur.Optimized.Physical.Prepared.DepthCertified` (`Depth.Structural.certify` +
`Depth.Structural.check`), which allows structurally-recursive exempt SCCs to run plain
calls at equal rank without carrying depth words.

`Aiur.Tiling.{WideStage, Grouped, PeriodicCompact, Compiled, Claims}` and `Aiur.Plonk.SharedSound`
state their composed theorems for the stricter no-exempt-SCC predicate `Depth.Certified`, even
though every underlying trace-to-`checkMemo` proof (`Wide.checkMemo`, `WideT.checkMemo`,
`Periodic.Sharded.sound`, `Plonk.stage_balanced`) is independent of exempt SCCs and
`Aiur.Optimized.Physical.Prepared.depth_grouped_activated_heap_sound` already discharges the
final step directly from `Physical.Prepared.DepthCertified`!

This module bridges that gap cleanly inside `Ix/Cert/AiurCompression/` (without modifying `Aiur`):
1. Lifts `Compiled.{fresh_of, system_wellFormed, depth_calls, depth_maps, shaped_of_compiled_on,
   context_of_compiled, claimsIn_of_maps}` and `Claims.ExportedIds.ids` from `Depth.Certified` to
   `Depth.Structural.certify` / `Physical.Prepared.DepthCertified`.
2. Proves the exempt-SCC-capable stage soundness theorems for all four L3 BN254 stages
   (plus generic prime-field and BLS12-381 shared-map PLONK specializations):
   - Stage 1 (`wide_heap_sound_goldilocks_structural`),
   - Stage 2 (`grouped_heap_sound_bn254_structural`, `grouped_heap_sound_shared_structural`),
   - Stage 3 (`narrow_heap_sound_compact_structural`),
   - Stage 4 (`plonk_shared_heap_sound_certified_prime`, `plonk_shared_heap_sound_structural_prime`,
     `plonk_shared_heap_sound_certified`, `plonk_shared_heap_sound_structural`,
     `plonk_shared_heap_sound_certified_bls12381`, `plonk_shared_heap_sound_structural_bls12381`).
3. Proves `represents_field_tuple`, recovering exact flat `[Field; n]` source outputs from
   `Aiur.Represents`.

Zero `sorry`, zero custom `axiom`, zero `native_decide`, zero `bv_decide`.
-/

namespace Ix.Cert.AiurCompression.DepthBridge

open Aiur Aiur.Circuit Aiur.Optimized Aiur.Optimized.Depth
open Aiur.Tiling Aiur.Tiling.Bridge Aiur.Tiling.Compiled Aiur.Tiling.Grouped
open Aiur.Tiling.WideStage Aiur.Tiling.Periodic
open Aiur.Plonk

/-! ## 1. Flat Field-Tuple Representation Recovery -/

private theorem represents_field_list {F : Type} {rom : Aiur.ROM F} {heap : Aiur.Heap F} :
    ∀ {ws : List F} {ss : List (Aiur.SourceValue F)},
      List.Forall₂ (Aiur.Represents rom heap) ss (ws.map Aiur.Value.field) →
      ss = ws.map Aiur.Value.field
  | [], [], _ => rfl
  | _ :: _, [], h => by cases h
  | [], _ :: _, h => by cases h
  | _ :: _, _ :: _, .cons h1 h2 => by
      cases h1
      exact congrArg (Aiur.Value.field _ :: ·) (represents_field_list h2)

/-- A flat tuple of field values (`[Field; n]`, such as the 4-word packed accumulator output of
`CompressNarrowFixed::step_v1` or the 18-word affine output of
`CompressFinalNarrow::verify_accumulator_v1`) represented in any ROM and heap equals that exact
tuple of `Value.field` words. -/
theorem represents_field_tuple {F : Type} {rom : Aiur.ROM F} {heap : Aiur.Heap F}
    {value : Aiur.SourceValue F} {ws : List F}
    (h : Aiur.Represents rom heap value (.tuple (ws.map Aiur.Value.field))) :
    value = .tuple (ws.map Aiur.Value.field) := by
  cases h with
  | tuple items => exact congrArg Aiur.Value.tuple (represents_field_list items)

/-! ## 2. Lifting `Aiur.Tiling.Compiled` Static Lemmas to `Depth.Structural.certify` -/

section StructuralStatic

variable {F : Type} [Field F] [DecidableEq F]

omit [Field F] [DecidableEq F] in
theorem structural_fresh_of {cfg : Depth.Config} {source : Circuit.System F}
    (certified : Depth.Structural.certify cfg source = true) :
    Fresh cfg source := by
  simp only [Depth.Structural.certify, Depth.fresh, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at certified
  obtain ⟨⟨⟨⟨⟨nodup, chips⟩, maps⟩, tables⟩, _⟩, _⟩ := certified
  exact ⟨nodup, fun c hc => (chips c hc).1, fun c hc => (chips c hc).2,
    fun m hm => ⟨(maps m hm).1.1.1, (maps m hm).1.1.2, (maps m hm).1.2⟩, tables⟩

theorem structural_compileChip_wellFormed (cfg : Depth.Config) (source : Circuit.System F)
    (chip : Chip F) (ok : Depth.Structural.chipOK cfg source chip = true) :
    (compileChip cfg.limbs (cfg.plan chip.name) chip).wellFormed = true := by
  simp only [Depth.Structural.chipOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ok
  obtain ⟨⟨formed, slots⟩, slotsOk⟩ := ok
  set plan := cfg.plan chip.name
  set pairs := chip.sends.zip plan.slots
  set bound := nextColumn cfg.limbs (plan.base chip) pairs
  have base : plan.base chip ≤ bound := nextColumn_ge _ _ _
  have grow : chip.numVars ≤ bound := le_trans (by unfold ChipPlan.base; split <;> omega) base
  simp only [Chip.wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at formed
  obtain ⟨⟨⟨⟨inputs, output⟩, constraints⟩, sends⟩, memory⟩ := formed
  have depthIn : ∀ p ∈ pairs, p.2 = .exact ∨ p.2 = .gap → chip.numVars < bound := by
    rintro ⟨send, kind⟩ hp kindIs
    have ok' := slotsOk (send, kind) hp
    have hSlot : Depth.slotOK cfg source chip.name send kind = true := by
      unfold Depth.Structural.slotOK at ok'
      simp only [Bool.or_eq_true, Bool.and_eq_true] at ok'
      rcases ok' with h | h
      · exact h
      · rcases kindIs with e | e <;> simp only at e <;> rw [e] at h <;>
          exact absurd h.1.1.1.1.1 (by decide)
    have recursive : plan.recursive = true := by
      unfold Depth.slotOK at hSlot
      rcases kindIs with e | e <;> simp only at e <;> subst e <;> split at hSlot <;>
        first | exact (of_decide_eq_true hSlot).1 | simp at hSlot
    have : plan.base chip = chip.numVars + 1 := by simp [ChipPlan.base, recursive]
    omega
  have sendsIn := sends_inBounds cfg.limbs chip.numVars bound (plan.base chip) pairs le_rfl
    (fun p hp => send_inBounds_mono grow (sends p.1 (List.of_mem_zip hp).1)) depthIn
  simp only [compileChip, Chip.wellFormed, Bool.and_eq_true, List.all_eq_true,
    List.mem_append]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro x hx
    refine decide_eq_true ?_
    simp only [List.mem_flatMap] at hx
    obtain ⟨a, ha, hxa⟩ := hx
    split at ha
    · rcases List.mem_append.mp ha with ha | ha
      · exact lt_of_lt_of_le (inputs x (List.mem_flatMap.mpr ⟨a, ha, hxa⟩)) grow
      · have : plan.base chip = chip.numVars + 1 := by simp [ChipPlan.base, *]
        simp only [List.mem_singleton] at ha
        subst ha
        simp only [List.mem_singleton] at hxa
        subst hxa
        exact lt_of_lt_of_le (by omega : chip.numVars < plan.base chip) base
    · exact lt_of_lt_of_le (inputs x (List.mem_flatMap.mpr ⟨a, ha, hxa⟩)) grow
  · exact fun x hx => Scalar.Circuit.ArithExpr.inBounds_mono grow (output x hx)
  · exact fun x hx => Scalar.Circuit.ArithExpr.inBounds_mono grow (constraints x hx)
  · rintro s (hs | hs)
    · exact sendsIn.1 s hs
    · exact sendsIn.2 s hs
  · intro m hm
    have := memory m hm
    simp only [MemoryLookup.inBounds, Bool.and_eq_true, List.all_eq_true] at this ⊢
    exact ⟨⟨Scalar.Circuit.ArithExpr.inBounds_mono grow this.1.1,
      Scalar.Circuit.ArithExpr.inBounds_mono grow this.1.2⟩,
      fun x hx => Scalar.Circuit.ArithExpr.inBounds_mono grow (this.2 x hx)⟩

theorem structural_system_wellFormed {cfg : Depth.Config} {source : Circuit.System F}
    (certified : Depth.Structural.certify cfg source = true)
    (names : (source.chips.map Chip.name).Nodup) : (Depth.system cfg source).WellFormed := by
  simp only [Depth.Structural.certify, Bool.and_eq_true, List.all_eq_true] at certified
  refine ⟨?_, ?_⟩
  · simpa [Depth.system, List.map_map, Function.comp_def, compileChip] using names
  · intro c hc
    simp only [Depth.system, List.mem_map] at hc
    obtain ⟨chip, member, rfl⟩ := hc
    exact structural_compileChip_wellFormed cfg source chip (certified.1.2 chip member)

theorem structural_slot_of_send {artifact : Artifact F} (prepared : Physical.Prepared artifact)
    {cfg : Depth.Config} (certified : Depth.Structural.certify cfg prepared.system = true)
    {c : Chip F} (hc : c ∈ prepared.system.chips) {p : Send F × SlotKind}
    (hp : p ∈ c.sends.zip (cfg.plan c.name).slots) :
    Depth.Structural.slotOK cfg prepared.system c.name p.1 p.2 = true := by
  simp only [Depth.Structural.certify, Bool.and_eq_true, List.all_eq_true] at certified
  have := certified.1.2 c hc
  simp only [Depth.Structural.chipOK, Bool.and_eq_true, List.all_eq_true] at this
  exact this.2 p hp

theorem structural_depth_calls {artifact : Artifact F} (prepared : Physical.Prepared artifact)
    {cfg : Depth.Config} (certified : Depth.Structural.certify cfg prepared.system = true) :
    ∀ D ∈ (Depth.system cfg prepared.system).chips, ∀ s ∈ D.sends,
      ∀ D' ∈ (Depth.system cfg prepared.system).chips, D'.name = s.channel →
        (s.args.map Erasure.shape, Erasure.shape s.result) = Erasure.signature D' := by
  have fr := structural_fresh_of certified
  intro D hD s hs D' hD' name
  obtain ⟨c, hc, rfl⟩ := depth_chip hD
  obtain ⟨c', hc', rfl⟩ := depth_chip hD'
  simp only [compileChip] at name
  simp only [compileChip, List.mem_append] at hs
  rcases hs with hs | hs
  · obtain ⟨p, hp, col, rfl⟩ := mem_mainSends hs
    obtain ⟨args, result, channel⟩ := extend_args p.1 (extra cfg.limbs (.var c.numVars) p.2 col)
    rw [channel] at name
    have sendIn := (List.of_mem_zip hp).1
    have base := prepared_call prepared hc sendIn hc' name
    have found : prepared.system.findChip? p.1.channel = some c' := by
      rw [← name]; exact findChip_of_mem (prepared_nodup prepared) hc'
    have slot := structural_slot_of_send prepared certified hc hp
    have same : (extra cfg.limbs (.var c.numVars : ArithExpr F) p.2 col).isSome =
        (cfg.plan c'.name).recursive := by
      rw [extra_isSome]
      unfold Depth.Structural.slotOK at slot
      simp only [Bool.or_eq_true, Bool.and_eq_true] at slot
      rcases slot with slot | hExempt
      · unfold Depth.slotOK at slot
        rw [found] at slot
        simp only [Config.recursive, name] at slot ⊢
        obtain ⟨sp, k⟩ := p
        cases k <;> simp only at slot ⊢ <;>
          first
          | exact ((of_decide_eq_true slot).1).symm
          | exact ((of_decide_eq_true slot).2.1).symm
      · have hk : p.2 = .plain := by
          have hb := hExempt.1.1.1.1.1
          cases hp2 : p.2 <;> rw [hp2] at hb <;> first | rfl | exact absurd hb (by decide)
        have hnr : cfg.recursive p.1.channel = false := by
          simpa using hExempt.1.1.1.2
        rw [hk]
        simp only [ne_eq, not_true_eq_false, decide_false]
        rw [← name] at hnr
        simpa [Config.recursive] using hnr.symm
    rw [compileChip_signature, args, result, ← same]
    simp only [Erasure.signature, Prod.mk.injEq] at base
    rw [base.1, base.2]
  · obtain ⟨w, hw, _, _, rfl⟩ := mem_rangeSends hs
    exact absurd (name ▸ rangeName_mem hw) (fr.chips c' hc')

theorem structural_depth_maps {artifact : Artifact F} (prepared : Physical.Prepared artifact)
    {cfg : Depth.Config} (certified : Depth.Structural.certify cfg prepared.system = true) :
    ∀ D ∈ (Depth.system cfg prepared.system).chips, ∀ s ∈ D.sends,
      ∀ mc ∈ (Depth.system cfg prepared.system).mapClaims, mc.channel = s.channel →
        Erasure.messageShape mc = (s.args.map Erasure.shape, Erasure.shape s.result) := by
  have fr := structural_fresh_of certified
  intro D hD s hs mc hmc channel
  obtain ⟨c, hc, rfl⟩ := depth_chip hD
  simp only [compileChip, List.mem_append] at hs
  rcases depth_claim fr hmc with ⟨outside, member⟩ | ⟨inside, shape⟩
  · rcases hs with hs | hs
    · obtain ⟨p, hp, col, rfl⟩ := mem_mainSends hs
      obtain ⟨args, result, sendChannel⟩ := extend_args p.1 (extra cfg.limbs (.var c.numVars) p.2 col)
      rw [sendChannel] at channel
      rw [prepared_mapClaims] at member
      have absent := prepared_claim_channel prepared member
      rw [channel] at absent
      have notChip : prepared.system.findChip? p.1.channel = none := by
        cases found : prepared.system.findChip? p.1.channel with
        | none => rfl
        | some c' =>
            have := prepared_name prepared (List.mem_of_find?_eq_some found)
            rw [System.findChip_name found, absent] at this
            simp at this
      have slot := structural_slot_of_send prepared certified hc hp
      have plain : p.2 = .plain := by
        unfold Depth.Structural.slotOK at slot
        rw [notChip] at slot
        simp only [Option.isSome_none, Bool.and_false, Bool.false_and, Bool.or_false] at slot
        unfold Depth.slotOK at slot
        rw [notChip] at slot
        simp only [decide_eq_true_eq] at slot
        exact slot.1
      have hNone : (extra cfg.limbs (.var c.numVars : ArithExpr F) p.2 col).isSome = false := by
        rw [extra_isSome, plain]; rfl
      rw [args, result, hNone]
      simp only [Bool.false_eq_true, ite_false, List.append_nil]
      obtain ⟨a, ha, hsa⟩ := prepared_static_call prepared hc (List.of_mem_zip hp).1 absent
      obtain ⟨map, hmap, mapName, mapShape⟩ := prepared.mapShaped.1 mc member
      rw [mapShape]
      exact (prepared.mapShaped.2 a ha p.1 hsa map hmap (mapName.trans channel)).symm
    · obtain ⟨w, hw, _, _, rfl⟩ := mem_rangeSends hs
      exact absurd (channel ▸ rangeName_mem hw) outside
  · rcases hs with hs | hs
    · obtain ⟨p, hp, col, rfl⟩ := mem_mainSends hs
      obtain ⟨_, _, sendChannel⟩ := extend_args p.1 (extra cfg.limbs (.var c.numVars) p.2 col)
      rw [sendChannel] at channel
      exact absurd (channel ▸ inside) (fr.sends c hc p.1 (List.of_mem_zip hp).1)
    · obtain ⟨w, hw, _, _, rfl⟩ := mem_rangeSends hs
      rw [shape]
      simp [rangeSend, unitWire, Erasure.shape]

theorem structural_shaped_of_compiled_on {artifact : Artifact F}
    (prepared : Physical.Prepared artifact) {cfg : Depth.Config}
    (certified : Depth.Structural.certify cfg prepared.system = true)
    {chips : List (Chip F)} (sub : ∀ c ∈ chips, c ∈ (Depth.system cfg prepared.system).chips)
    {name : String} (entry : name ∈ artifact.entries)
    {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed artifact.system ⟨name, wires, output⟩) {root : Circuit.Message F}
    (rooted : Depth.erase cfg root = Erasure.message artifact.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (entryChip : (artifact.system.findChip? name).isSome = true)
    (idOf : String → Nat) (bound : Nat)
    (ids : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) chips root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) chips root, idOf x = idOf y → x = y)
    (idBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) chips root, idOf x < bound) :
    Bridge.Shaped (Depth.system cfg prepared.system) chips idOf root bound := by
  have single := sub
  have rootIs := root_eq rooted entryPlain entryChip
  obtain ⟨t, found⟩ := Option.isSome_iff_exists.mp entryChip
  refine ⟨fun c hc s hs c' hc' e =>
      structural_depth_calls prepared certified c (single c hc) s hs c' (single c' hc') e,
    fun c hc s hs mc hmc e =>
      structural_depth_maps prepared certified c (single c hc) s hs mc hmc e,
    ?_, ?_, fun c hc m hm => depth_memory prepared c (single c hc) m hm, ids, idBound⟩
  · intro D hD e
    obtain ⟨c, hc, rfl⟩ := depth_chip (single D hD)
    simp only [compileChip] at e
    rw [rootIs] at e
    simp only at e
    have fixed : Dedup.rename prepared.merged.representatives name = name :=
      prepared.merged.certificate.2.2.2.2.2.2.2.2 name entry
    have callee := prepared_callee prepared found
    rw [fixed, ← e, findChip_of_mem (prepared_nodup prepared) hc, Option.some.injEq] at callee
    subst callee
    have plain : (cfg.plan ((Erasure.chip artifact.system t).rename
        (Dedup.rename prepared.merged.representatives)).name).recursive = false := by
      rw [e]; exact entryPlain
    rw [compileChip_signature, plain, rootIs]
    have sig := signed t found
    simp only [Erasure.messageShape, Erasure.signature, Prod.mk.injEq] at sig
    have args := congrArg (fun l => (l.map Prod.snd).sum) sig.1
    simp only [length_flatMap_words] at args
    have result := congrArg Prod.snd sig.2
    simp only [Erasure.shape] at result
    simp [Erasure.messageShape, Chip.rename, Erasure.chip, shape_pack, args, result]
  · intro mc hmc e
    rcases depth_claim (structural_fresh_of certified) hmc with ⟨_, member⟩ | ⟨inside, _⟩
    · rw [prepared_mapClaims] at member
      have absent := prepared_claim_channel prepared member
      rw [e, rootIs] at absent
      simp [found] at absent
    · exact absurd (e ▸ inside) outside

theorem structural_context_of_compiled {artifact : Artifact F}
    (prepared : Physical.Prepared artifact) {cfg : Depth.Config}
    (certified : Depth.Structural.certify cfg prepared.system = true)
    {name : String} {wires : List (WireValue F)} {output : WireValue F}
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root = Erasure.message artifact.system ⟨name, wires, output⟩)
    (entryPlain : cfg.recursive name = false)
    (entryChip : (artifact.system.findChip? name).isSome = true) :
    (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok () := by
  rw [root_eq rooted entryPlain entryChip]
  refine System.checkContext_iff.mpr ⟨?_, ?_, ?_,
      structural_system_wellFormed certified (prepared_nodup prepared)⟩
  · refine ⟨?_, ⟨_, pack_decode _ _⟩⟩
    intro a ha
    simp only [List.mem_singleton] at ha
    subst ha
    exact ⟨_, pack_decode _ _⟩
  · intro a ha
    simp only [List.mem_singleton] at ha
    subst ha
    exact pack_pointerFree _ _
  · exact Erasure.rawROM_valid (by intro a ha; simp at ha)

theorem structural_static_of_compiled {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Structural.certify cfg prepared.system = true)
    {chips : List (Chip F)} (sub : ∀ c ∈ chips, c ∈ (Depth.system cfg prepared.system).chips)
    {name : String} (entry : name ∈ entries)
    {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (idOf : String → Nat) {bound : Nat}
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) chips root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) chips root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) chips root, idOf x < bound) :
    Bridge.Shaped.check (Depth.system cfg prepared.system) chips idOf root bound = true ∧
      (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok () := by
  have entry' : name ∈ compiled.artifact.entries := by
    rw [(compile_stages compiled.compiled).2.2.1]; exact entry
  have entryChip := compile_entry_chip compiled.compiled entry
  exact ⟨Shaped.check_of (structural_shaped_of_compiled_on prepared certified sub entry' signed
      rooted outside entryPlain entryChip idOf bound chanIds chanBound),
    structural_context_of_compiled prepared certified rooted entryPlain entryChip⟩

/-- Exported package channel-ID injectivity and bound from `Claims.ExportedIds`, supporting
exempt SCCs (`Depth.Structural.certify` / `Physical.Prepared.DepthCertified`). -/
theorem structural_exportedIds_ids {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} {compiled : GenericArtifact specialized}
    {prepared : Physical.Prepared compiled.artifact} {cfg : Depth.Config}
    {callables : List String} {bound : Nat} {root : Circuit.Message F}
    (h : Claims.ExportedIds compiled prepared cfg callables bound root)
    (certified : Physical.Prepared.DepthCertified compiled prepared cfg)
    {chips : List (Chip F)} (sub : ∀ c ∈ chips, c ∈ (Depth.system cfg prepared.system).chips) :
    (∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) chips root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) chips root,
        callables.idxOf x = callables.idxOf y → x = y) ∧
      ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) chips root, callables.idxOf x < bound := by
  obtain ⟨_, _, _, _, exported, _, _, _, _, _, pkg, hcast, hlt, hcfg, exportedOk, written, decoded, rfl, checked⟩ := h
  have hClaims : ∀ mc ∈ (Depth.system cfg prepared.system).mapClaims, mc.channel ∈ pkg.mapNames := by
    obtain ⟨cfg', measures', hcfg', bc, maps⟩ := Claims.exportPrepared_spec exportedOk
    rw [hcfg] at hcfg'
    cases hcfg'
    have program := Ixa.program_of_decode hcast hlt written (Claims.decodePackage_of_checked decoded)
    have names : pkg.mapNames = (Trace.depthBytecode cfg exported.bytecode).maps.map (·.name) := by
      rw [Ixa.Package.mapNames, program, bc]
    obtain ⟨kept, ranges⟩ := Claims.depthBytecode_maps cfg exported.bytecode
    intro mc hmc
    have fr := structural_fresh_of certified.1
    rcases depth_claim fr hmc with ⟨_, member⟩ | ⟨inside, _⟩
    · have unmerged : compiled.artifact.system.mapClaims = compiled.artifact.unmerged.mapClaims :=
        compiled.artifact.deduplication.2.2.2.1
      rw [prepared_mapClaims, unmerged] at member
      have hmem := claim_channel member
      rw [(compile_stages compiled.compiled).2.2.2.2.2] at hmem
      obtain ⟨m, hm, e⟩ := List.mem_map.mp hmem
      obtain ⟨x, hx, ex⟩ := List.mem_map.mp (maps m hm)
      rw [← e, names, ← ex]
      exact kept x hx
    · have channel := claim_channel hmc
      simp only [Depth.system, List.map_append, List.mem_append, List.map_map, List.mem_map,
        Function.comp_def] at channel
      rcases channel with ⟨map, hmap, e⟩ | ⟨w, hw, e⟩
      · exact absurd (e ▸ inside) (fr.maps map hmap).1
      · rw [← e, names]
        exact ranges w (List.mem_dedup.mp hw)
  exact Ixa.ids_ofChip sub hClaims
    (Claims.checkIds_of_package hcast hlt hcfg exportedOk written decoded checked)

end StructuralStatic

/-! ## 3. Exempt-SCC Stage Soundness Theorems (BN254 L3 Stages & BLS12-381 Specializations) -/

/-- BN254 scalar field (`ZMod Aiur.Library.Field.BN254.modulus`, definitionally equal to `BN254Fr`). -/
abbrev Bn254F : Type := ZMod Aiur.Library.Field.BN254.modulus

/-- `BN254` scalar field characteristic satisfies `n ≤ 2^39 * 2^24 → (n : Bn254F) ≠ 0`. -/
theorem bn254_characteristic_24 :
    ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ 24 → (n : Bn254F) ≠ 0 := by
  intro n hpos hle
  have hlt : n < Aiur.Library.Field.BN254.modulus := Nat.lt_of_le_of_lt hle (by decide)
  intro h0
  have hv := congrArg ZMod.val h0
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, ZMod.val_zero] at hv
  omega

/-- `BLS12-381` scalar field characteristic satisfies `n ≤ 2^39 * 2^24 → (n : Aiur.Library.Field.BLS12381.F) ≠ 0`. -/
theorem bls12381_characteristic_24 :
    ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ 24 → (n : Aiur.Library.Field.BLS12381.F) ≠ 0 := by
  intro n hpos hle
  have hlt : n < Aiur.Library.Field.BLS12381.modulus := Nat.lt_of_le_of_lt hle (by decide)
  intro h0
  have hv := congrArg ZMod.val h0
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, ZMod.val_zero] at hv
  omega

/-- `Goldilocks` characteristic satisfies `n ≤ 2^39 * 2^24 → (n : Aiur.Library.U32.Goldilocks.F) ≠ 0`. -/
theorem goldilocks_characteristic_24 :
    ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ 24 → (n : Aiur.Library.U32.Goldilocks.F) ≠ 0 :=
  Depth.goldilocks_characteristic

/-- **Stage 1 (`CompressWrap`) Goldilocks Wide Soundness with Exempt SCCs (`Physical.Prepared.DepthCertified`):**
Matches `Aiur.Tiling.WideStage.wide_heap_sound` while accepting `Physical.Prepared.DepthCertified`. -/
theorem wide_heap_sound_goldilocks_structural
    {source : Generic.Source Aiur.Library.U32.Goldilocks.F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Physical.Prepared.DepthCertified compiled prepared cfg)
    {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id)
    (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue Aiur.Library.U32.Goldilocks.F)} {result : Value Aiur.Library.U32.Goldilocks.F}
    {wires : List (WireValue Aiur.Library.U32.Goldilocks.F)} {output : WireValue Aiur.Library.U32.Goldilocks.F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message Aiur.Library.U32.Goldilocks.F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat)
    {units : List ((Chip Aiur.Library.U32.Goldilocks.F × Option (Unroll Aiur.Library.U32.Goldilocks.F)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, Bridge.unitOk idOf u.1 = true)
    (capacity : WideStage.unitCapRows units ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound)
    (hbound : bound ≤ 2 ^ 63) (tags : 2 < bound)
    (lookups : WideStage.unitCapLookups units < bound)
    (hbits : cfg.bits ≤ 24)
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x < bound)
    (enablesOk : ∀ c ∈ plan.singles, Bridge.checkEnables bound c = true)
    {mainU mainM mainR : Nat → Nat → Scalar.Circuit.Var → Aiur.Library.U32.Goldilocks.F}
    (holds : WideStage.StageHolds (WideStage.unitAirs idOf units) mainU)
    (balanced : WideStage.stageLedger (WideStage.unitAirs idOf units) mainU +
      WideStage.stageLedger (WideStage.mapAirs
        ((Depth.system cfg prepared.system).mapClaims.map (Bridge.encode idOf)) mapCap) mainM +
      WideStage.stageLedger (WideStage.romAirs roms) mainR +
      Finsupp.single (Bridge.encode idOf root) 1 = 0) :
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result := by
  have small : SmallCast Aiur.Library.U32.Goldilocks.F bound := Aiur.Tiling.Goldilocks.smallCast hbound
  obtain ⟨shaped, context⟩ := structural_static_of_compiled compiled prepared certified.1
    (Claims.singles_sub plan) entry signed rooted outside entryPlain idOf chanIds chanBound
  rw [WideStage.unitAirs_ledger unrolled] at balanced
  set insts := WideStage.unitInsts idOf units mainU
  set rom := WideStage.wideRom roms mainR
  have valid : rom.Valid := WideStage.wideRom_valid widths (fun r hr i hi i' hi' e =>
    small.inj (by have := romCaps r hr; omega) (by have := romCaps r hr; omega) e) mainR
  have context' : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM rom) root = .ok () := by
    obtain ⟨formed, pub, _, wf⟩ := System.checkContext_iff.mp context
    exact System.checkContext_iff.mpr ⟨formed, pub, Erasure.rawROM_valid valid, wf⟩
  set claims := (Depth.system cfg prepared.system).mapClaims.map (Bridge.encode idOf)
  set tables := WideStage.stageLedger (WideStage.mapAirs claims mapCap) mainM +
    WideStage.stageLedger (WideStage.romAirs roms) mainR
  have W : Wide plan idOf bound (Erasure.rawROM rom) root insts tables := {
    chips := fun p hp => by obtain ⟨u, hu, e⟩ := WideStage.unitInsts_chip hp; rw [e]; exact chipsIn u hu
    holds := fun p hp => WideStage.unitInsts_holds holds hp
    small := small
    enablesOk := enablesOk
    tags := tags
    count := by rw [WideStage.lookupCount_unitInsts]; exact lookups
    shaped := Shaped.of_check shaped
    romPacked := WideStage.rawROM_packed rom
    tableSupport := fun t ht => by
      simp only [tables, Finsupp.add_apply] at ht
      by_cases hm : WideStage.stageLedger (WideStage.mapAirs claims mapCap) mainM t = 0
      · rw [hm, zero_add] at ht
        exact Or.inr (WideStage.romAirs_support roms mainR t ht)
      · obtain ⟨mc, hmc, e⟩ := List.mem_map.mp (WideStage.mapAirs_support claims mapCap mainM t hm)
        exact Or.inl ⟨mc, hmc, e.symm⟩
    balanced := by
      rw [← balanced]
      simp only [tables, insts]
      abel }
  obtain ⟨weighted, length, checked⟩ := W.checkMemo activated context'
  have hlen : weighted.length ≤ 2 ^ 39 :=
    (length.trans (WideStage.length_unitInsts idOf units mainU).le).trans capacity
  exact ⟨valid, prepared.depth_grouped_activated_heap_sound compiled certified hbits plan activated
    entry valid signed rooted outside hlen goldilocks_characteristic_24 checked arguments decoded⟩

/-- Internal shared core for grouped / shared-map stages with exempt SCCs
(`Physical.Prepared.DepthCertified`). Covers both Stage 2 (`CompressGL`) and Stage 4
(`CompressFinalNarrow` via `Plonk.stage_balanced`). -/
theorem grouped_heap_sound_core_structural {F : Type} [Field F] [DecidableEq F]
    {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Physical.Prepared.DepthCertified compiled prepared cfg)
    (hbits : cfg.bits ≤ 24)
    {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id)
    (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue F)} {result : Value F}
    {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) (idOk : ∀ x n, id x = .ok n → n = idOf x)
    (names : (circuitNames plan).Nodup)
    {units : List ((Chip F × Option (Unroll F)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, Bridge.unitOk idOf u.1 = true)
    {groups : List (Grouping.Packed F id × Nat)}
    (groupsIn : ∀ x ∈ groups, x.1 ∈ plan.groups)
    (capacity : WideStage.unitCapRows units + (groups.map (·.2)).sum ≤ 2 ^ 39)
    {mapLedger : Tiling.Ledger F}
    (mapSupport : ∀ t, mapLedger t ≠ 0 →
      t ∈ (Depth.system cfg prepared.system).mapClaims.map (Bridge.encode idOf))
    {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound) (romWidths : ∀ r ∈ roms, r.1 < bound)
    (small : SmallCast F bound) (tags : 2 < bound)
    (lookups : WideStage.unitCapLookups units + (groups.map fun x => x.2 * groupCost x.1).sum < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ 24 → (n : F) ≠ 0)
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x < bound)
    (enablesOk : ∀ c ∈ allChips plan, Bridge.checkEnables bound c = true)
    (memWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < bound)
    {mainU mainG mainR : Nat → Nat → Scalar.Circuit.Var → F}
    (holds : WideStage.StageHolds (WideStage.unitAirs idOf units) mainU)
    (holdsG : WideStage.StageHolds (groupAirs groups) mainG)
    (balanced : Finsupp.mapDomain trimZeros
      (WideStage.stageLedger (WideStage.unitAirs idOf units) mainU +
        WideStage.stageLedger (groupAirs groups) mainG +
        mapLedger + WideStage.stageLedger (WideStage.romAirs roms) mainR +
        Finsupp.single (Bridge.encode idOf root) 1) = 0) :
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result := by
  obtain ⟨shaped, context⟩ := structural_static_of_compiled compiled prepared certified.1
    (Claims.allChips_sub plan) entry signed rooted outside entryPlain idOf chanIds chanBound
  rw [WideStage.unitAirs_ledger unrolled, groupAirs_ledger] at balanced
  set sInsts := WideStage.unitInsts idOf units mainU
  set gInsts := groupRows groups mainG
  have sChips : ∀ p ∈ sInsts, p.1 ∈ plan.singles := fun p hp => by
    obtain ⟨u, hu, e⟩ := WideStage.unitInsts_chip hp; rw [e]; exact chipsIn u hu
  have sHold : ∀ p ∈ sInsts, (Bridge.lower idOf p.1).Holds p.2 := fun p hp =>
    WideStage.unitInsts_holds holds hp
  have gIn : ∀ x ∈ gInsts, x.1 ∈ plan.groups := fun x hx => by
    obtain ⟨y, hy, e⟩ := groupRows_in hx; rw [e]; exact groupsIn y hy
  have gHold : ∀ x ∈ gInsts, (lowerGroup x.1.checked.layout).Holds x.2 := groupRows_holds holdsG
  have cap' : sInsts.length + gInsts.length ≤ 2 ^ 39 := by
    rw [WideStage.length_unitInsts, length_groupRows]; exact capacity
  have look' : Bridge.lookupCount sInsts + (gInsts.map fun x => groupCost x.1).sum < bound := by
    rw [WideStage.lookupCount_unitInsts, cost_groupRows]; exact lookups
  set rom := WideStage.wideRom roms mainR
  have valid : rom.Valid := WideStage.wideRom_valid widths (fun r hr i hi i' hi' e =>
    small.inj (by have := romCaps r hr; omega) (by have := romCaps r hr; omega) e) mainR
  have context' : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM rom) root = .ok () := by
    obtain ⟨formed, pub, _, wf⟩ := System.checkContext_iff.mp context
    exact System.checkContext_iff.mpr ⟨formed, pub, Erasure.rawROM_valid valid, wf⟩
  set tables := mapLedger + WideStage.stageLedger (WideStage.romAirs roms) mainR
  obtain ⟨V, lenV, costV, fromV, ledgerV⟩ := group_virtual idOf idOk gHold
  let S : List (Inst F) := sInsts.map fun p => (p.1, p.2, p.2 (p.1.numVars + 1))
  have sLedger : S.map (instLedger idOf) = sInsts.map fun p => (Bridge.lower idOf p.1).rowLedger p.2 := by
    simp only [S, List.map_map]
    apply List.map_congr_left
    intro p _
    exact (lower_instLedger idOf p.1 p.2).symm
  have singleAll : ∀ c ∈ plan.singles, c ∈ allChips plan := fun c hc => List.mem_append_left _ hc
  have W : WideT (Depth.system cfg prepared.system) (allChips plan) idOf bound (Erasure.rawROM rom) root
      (S ++ V) tables := {
    chipsIn := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact singleAll _ (sChips q hq)
      · obtain ⟨x, hx, m, hm, -, -, -, rfl⟩ := fromV p hp
        exact origin_allChips plan (gIn x hx) hm
    sat := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact fun c hc => sHold q hq c (List.mem_append_left _ hc)
      · obtain ⟨x, hx, m, hm, sat, -, active, rfl⟩ := fromV p hp
        exact member_sat x.1.checked hm sat active
    mult := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        have := sHold q hq _ (List.mem_append_right _ (List.mem_singleton_self _))
        simpa [Scalar.Circuit.ArithExpr.denote] using this
      · obtain ⟨x, hx, m, hm, -, -, active, rfl⟩ := fromV p hp
        simp [memberInst, project_selector x.1.checked hm, active]
    small := small
    enablesOk := enablesOk
    tags := tags
    count := by
      have e : ((S ++ V).map fun p => p.1.sends.length + p.1.memory.length).sum =
          (sInsts.map fun p => p.1.sends.length + p.1.memory.length).sum +
            (V.map fun p => p.1.sends.length + p.1.memory.length).sum := by
        simp only [S, List.map_append, List.sum_append, List.map_map, Function.comp_def]
      have h1 : (sInsts.map fun p => p.1.sends.length + p.1.memory.length).sum +
          (V.map fun p => p.1.sends.length + p.1.memory.length).sum + 1 ≤
          Bridge.lookupCount sInsts + (gInsts.map fun x => groupCost x.1).sum := by
        unfold Bridge.lookupCount
        have hle := Nat.add_le_add_left costV
          (sInsts.map fun p => p.1.sends.length + p.1.memory.length).sum
        calc
          (sInsts.map fun p => p.1.sends.length + p.1.memory.length).sum +
              (V.map fun p => p.1.sends.length + p.1.memory.length).sum + 1
            ≤ (sInsts.map fun p => p.1.sends.length + p.1.memory.length).sum +
              (gInsts.map fun x => groupCost x.1).sum + 1 := Nat.add_le_add_right hle 1
          _ = (sInsts.map fun p => p.1.sends.length + p.1.memory.length).sum + 1 +
              (gInsts.map fun x => groupCost x.1).sum := by rw [Nat.add_right_comm]
      exact Nat.lt_of_le_of_lt (e ▸ h1) look'
    shaped := Shaped.of_check shaped
    romPacked := WideStage.rawROM_packed rom
    romWidth := by
      intro e he
      simp only [Erasure.rawROM, List.mem_map] at he
      obtain ⟨⟨addr, ws⟩, hw, rfl⟩ := he
      simp only [rom, WideStage.wideRom, List.mem_flatMap, List.mem_map, List.mem_range] at hw
      obtain ⟨x, hx, i, _, eq⟩ := hw
      simp only [Prod.mk.injEq] at eq
      obtain ⟨-, rfl⟩ := eq
      simp only [Erasure.pack_words, WideStage.romWords_length]
      exact romWidths x.1 (List.fst_mem_of_mem_zipIdx hx)
    memWidth := memWidth
    tableSupport := fun t ht => by
      simp only [tables, Finsupp.add_apply] at ht
      by_cases hm : mapLedger t = 0
      · rw [hm, zero_add] at ht
        exact Or.inr (WideStage.romAirs_support roms mainR t ht)
      · obtain ⟨mc, hmc, e⟩ := List.mem_map.mp (mapSupport t hm)
        exact Or.inl ⟨mc, hmc, e.symm⟩
    balanced := by
      have e : ((S ++ V).map (instLedger idOf)).sum + Finsupp.single (Bridge.encode idOf root) 1 + tables =
          ((S.map (instLedger idOf)).sum + tables + Finsupp.single (Bridge.encode idOf root) 1) +
            (V.map (instLedger idOf)).sum := by
        simp only [List.map_append, List.sum_append]; abel
      rw [e, Finsupp.mapDomain_add, ← ledgerV, ← Finsupp.mapDomain_add, sLedger, ← balanced]
      congr 1
      simp only [tables]
      abel }
  obtain ⟨rows, length, checked⟩ := W.checkMemo plan context' (fun p hp act mem => by
    rcases List.mem_append.mp hp with hp' | hp'
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp'
      have hc := sChips q hq
      obtain ⟨_, formedA⟩ := activated q.1 hc
      have finite := Chip.finiteAssignment formedA q.2 (Erasure.rawROM rom)
      have validA : (Activation.compile q.1).ValidAssignment (Erasure.rawROM rom) q.2 := ⟨W.sat _ hp, mem⟩
      refine ⟨Row.ofAssignment q.1.name (q.1.numVars + 1) q.2, ?_⟩
      have check : (Activation.compile q.1).checkRow (Erasure.rawROM rom)
          (Row.ofAssignment q.1.name (q.1.numVars + 1) q.2) =
            .ok ((Activation.compile q.1).conclusion q.2, (Activation.compile q.1).requirements q.2) := by
        apply Chip.checkRow_iff.mpr
        refine ⟨⟨formedA, Row.ofAssignment_length _ _ _, finite.1.mp validA⟩, ?_⟩
        exact Prod.ext finite.2.1 finite.2.2
      have sel : (Row.ofAssignment q.1.name (q.1.numVars + 1) q.2).assignment q.1.numVars = 1 := by
        rw [Row.ofAssignment_agree _ _ _ _ (Nat.lt_succ_self _)]; exact act
      have named : (Row.ofAssignment q.1.name (q.1.numVars + 1) q.2).chip = q.1.name := rfl
      simp only [Grouping.Plan.inspectRow, named, find_single plan hc, check, sel, ite_true]
    · obtain ⟨x, hx, m, hm, sat, actG, active, rfl⟩ := fromV p hp'
      exact ⟨_, group_inspect plan names (gIn x hx) hm sat actG active mem⟩)
  have total : rows.length ≤ 2 ^ 39 := by
    have : (S ++ V).length ≤ sInsts.length + gInsts.length := by
      simp only [S, List.length_append, List.length_map]; omega
    omega
  exact ⟨valid, prepared.depth_grouped_activated_heap_sound compiled certified hbits plan activated
    entry valid signed rooted outside total characteristic checked arguments decoded⟩

/-- **Stage 2 (`CompressGL`, BN254) Grouped Wide Soundness with Exempt SCCs:** -/
theorem grouped_heap_sound_bn254_structural
    {source : Generic.Source Bn254F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Physical.Prepared.DepthCertified compiled prepared cfg)
    {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id)
    (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue Bn254F)} {result : Value Bn254F}
    {wires : List (WireValue Bn254F)} {output : WireValue Bn254F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message Bn254F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) (idOk : ∀ x n, id x = .ok n → n = idOf x)
    (names : (circuitNames plan).Nodup)
    {units : List ((Chip Bn254F × Option (Unroll Bn254F)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, Bridge.unitOk idOf u.1 = true)
    {groups : List (Grouping.Packed Bn254F id × Nat)}
    (groupsIn : ∀ x ∈ groups, x.1 ∈ plan.groups)
    (capacity : WideStage.unitCapRows units + (groups.map (·.2)).sum ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound) (romWidths : ∀ r ∈ roms, r.1 < bound)
    (hbound : bound ≤ 2 ^ 63) (tags : 2 < bound)
    (lookups : WideStage.unitCapLookups units + (groups.map fun x => x.2 * groupCost x.1).sum < bound)
    (hbits : cfg.bits ≤ 24)
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x < bound)
    (enablesOk : ∀ c ∈ allChips plan, Bridge.checkEnables bound c = true)
    (memWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < bound)
    {mainU mainG mainM mainR : Nat → Nat → Scalar.Circuit.Var → Bn254F}
    (holds : WideStage.StageHolds (WideStage.unitAirs idOf units) mainU)
    (holdsG : WideStage.StageHolds (groupAirs groups) mainG)
    (balanced : Finsupp.mapDomain trimZeros
      (WideStage.stageLedger (WideStage.unitAirs idOf units) mainU +
        WideStage.stageLedger (groupAirs groups) mainG +
        WideStage.stageLedger (WideStage.mapAirs
          ((Depth.system cfg prepared.system).mapClaims.map (Bridge.encode idOf)) mapCap) mainM +
        WideStage.stageLedger (WideStage.romAirs roms) mainR +
        Finsupp.single (Bridge.encode idOf root) 1) = 0) :
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result :=
  grouped_heap_sound_core_structural compiled prepared certified hbits plan activated entry signed
    rooted outside entryPlain arguments decoded idOf idOk names chipsIn unrolled groupsIn capacity
    (WideStage.mapAirs_support _ mapCap mainM) widths romCaps romWidths
    (Grouped.bn254_smallCast hbound) tags lookups bn254_characteristic_24 chanIds chanBound
    enablesOk memWidth holds holdsG balanced

/-- **Stage 3 (`CompressNarrowFixed`, BN254) Tiled Narrow Compact Soundness with Exempt SCCs:** -/
theorem narrow_heap_sound_compact_structural {F : Type} [Field F] [DecidableEq F]
    {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Physical.Prepared.DepthCertified compiled prepared cfg)
    (hbits : cfg.bits ≤ 24)
    {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id)
    (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue F)} {result : Value F}
    {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {S : Periodic.Sharded F} (ok : S.check = true)
    {units : List (Chip F × Option (Unroll F))} (chipsIn : ∀ u ∈ units, u.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, Bridge.unitOk idOf u = true)
    {wide : List (Tiling.Circuit F)} {groups : List (List (List Nat))}
    (circuits : S.system.circuits = List.zipWith Tiling.Circuit.mergeBy wide groups)
    (wideEq : wide = units.map (Bridge.unitCircuit idOf))
    (lenG : groups.length = wide.length)
    (merged : ∀ j (hw : j < wide.length) (hg : j < groups.length), wide[j].checkMerge groups[j] = true)
    {ν : F → Nat} {tables : List (Periodic.Compact F)}
    (tablesOk : Periodic.checkTables S ν tables = true)
    (mapsIn : ∀ T ∈ tables, T.checkMap S = true → ∀ q ∈ T.parts,
      q.tag :: q.sub :: q.payload ∈ (Depth.system cfg prepared.system).mapClaims.map (Bridge.encode idOf))
    (capacity : Bridge.capacityRowsU units S.system ≤ 2 ^ 39)
    {bound : Nat} (small : SmallCast F bound) (tags : 3 < bound)
    (codesBound : ∀ e ∈ S.buses, e.2.1 < bound) (labels : Periodic.copyKey S.labelTotal < bound)
    (shadowBound : ∀ k < S.shards.length, ((S.layout k).shadow S.width).bound ≤ bound)
    (lookups : Bridge.capacityLookupsU units S.system < bound) (idsBound : S.system.instances ≤ bound)
    (parts : (S.system.enumerate S.system.lookupCount).length + 1 +
      (tables.map (·.parts.length)).sum < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ 24 → (n : F) ≠ 0)
    (req : (Part.request S.width (Bridge.encode idOf root)).checkRequest S.system
      (Bridge.encode idOf root) = true)
    (req2 : S.checkRequest2 (Part.request S.width (Bridge.encode idOf root)) = true)
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x < bound)
    (enablesOk : ∀ c ∈ plan.singles, Bridge.checkEnables bound c = true)
    {H : Nat → Nat} {main : Nat → Nat → Nat → F} {HT : Nat → Nat} {mainT : Nat → Nat → Nat → F}
    (tall : ∀ k < S.shards.length, ((S.layout k).shadow S.width).places.length ≤ H k)
    (tallT : ∀ t T, tables[t]? = some T → T.rows ≤ HT t)
    (rows : ∀ k < S.shards.length, ∀ p < H k,
      Scalar.Circuit.Satisfies (S.circuit k).constraints (S.assign k (main k) p))
    (balanced : Finsupp.mapDomain trimZeros (S.ledger H main + Periodic.compactLedger S tables HT mainT +
      S.padded2 (Part.request S.width (Bridge.encode idOf root))) = 0) :
    (Periodic.compactRom S tables mainT).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (Periodic.compactRom S tables mainT)).decode
          specialized.program.enums) heap value result := by
  obtain ⟨shaped, context⟩ := structural_static_of_compiled compiled prepared certified.1
    (Claims.singles_sub plan) entry signed rooted outside entryPlain idOf chanIds chanBound
  set rom : WidthROM F := Periodic.compactRom S tables mainT
  obtain ⟨each, keysNd, _⟩ := Periodic.checkTables_parts tablesOk
  obtain ⟨_, _, _, nodup, mods⟩ := Periodic.Sharded.check_parts ok
  have keyed := (Periodic.Sharded.check_parts ok).1
  have valid' := S.system.valid_of_checkKeyed keyed
  have sep : S.Separated bound :=
    ⟨small, by simpa [Periodic.Sharded.system] using valid'.width.1,
      fun e he => ⟨codesBound e he, mods e he⟩, nodup, labels⟩
  have W4 : 4 ≤ S.width := sep.width
  have valid : rom.Valid := Periodic.compactRom_valid tablesOk W4 mainT
  have context' : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM rom) root = .ok () := by
    obtain ⟨formed, pub, _, wf⟩ := System.checkContext_iff.mp context
    exact System.checkContext_iff.mpr ⟨formed, pub, Erasure.rawROM_valid valid, wf⟩
  have romPacked : ∀ e ∈ (Erasure.rawROM rom).entries,
      e.2.type = .tuple (List.replicate e.2.words.length .field) := by
    intro e he
    simp only [Erasure.rawROM, List.mem_map] at he
    obtain ⟨_, _, rfl⟩ := he
    simp [Erasure.pack]
  set request := Part.request S.width (Bridge.encode idOf root)
  have reqFacts : request.Request S.system (Bridge.encode idOf root) := Part.Request.of_check req
  set XT := Periodic.compactParts S tables mainT
  have facts : ∀ x ∈ XT, x.recv = true ∧ S.checkRequest2 x = true ∧ x.Formed S.system.width ∧
      x.RowsIn S.system.roleOf S.system.arityAt ∧
      (x.chunks = [] → S.system.arityAt (x.tag, x.sub) = some x.payload.length) ∧
      (x.chunks ≠ [] → (x.tag, x.sub) ∉ S.system.receivers) := by
    intro x hx
    obtain ⟨T, t, i, hi, hT, rfl⟩ := Periodic.mem_compactParts hx
    rw [Periodic.Compact.traceParts_getElem (S := S) (mainT t) hi]
    exact Periodic.CPart.trace_facts ((Periodic.Compact.check_parts (each T (List.mem_of_getElem? hT)).1).2.2 _
      (List.getElem_mem hi)) W4
  have tablesCheck : ∀ T ∈ tables, T.check S = true := fun T hT => (each T hT).1
  set ext := S.padded2 request + Periodic.compactLedger S tables HT mainT
  have balanced' : Finsupp.mapDomain trimZeros (S.ledger H main + ext) = 0 := by
    rw [← balanced, add_assoc]
    congr 2
    exact add_comm _ _
  have extShape : ∀ t, ext t ≠ 0 → S.MsgShape t := by
    intro t h
    simp only [ext, Finsupp.add_apply] at h
    by_cases h0 : S.padded2 request t = 0
    · rw [h0, zero_add] at h
      exact Periodic.compactLedger_shape tablesCheck mainT t h
    · exact Periodic.Sharded.padded2_shape req2 t h0
  have extParts : Finsupp.mapDomain S.proj2 ext = ((request :: XT).map Part.narrow).sum := by
    simp only [ext, Finsupp.mapDomain_add, List.map_cons, List.sum_cons]
    rw [Periodic.Sharded.padded2_proj sep reqFacts.arity reqFacts.rowsIn req2,
      Periodic.compactLedger_proj sep tablesCheck tallT]
  have pw : (request :: XT).Pairwise Clash := by
    refine List.pairwise_cons.mpr ⟨fun y _ r _ => ?_, Periodic.pairwise_compactParts keysNd⟩
    rw [reqFacts.send] at r
    cases r
  obtain ⟨holds, wideBalanced⟩ := S.sound ok small codesBound labels shadowBound idsBound (request :: XT)
    (by simp only [List.length_cons, XT, Periodic.length_compactParts]; omega) tall rows extShape extParts
    (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨reqFacts.formed, reqFacts.rowsIn⟩
      · exact ⟨(facts x hx).2.2.1, (facts x hx).2.2.2.1⟩)
    (by
      intro x hx hr hc
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [reqFacts.send] at hr; cases hr
      · exact (facts x hx).2.2.2.2.2 hc)
    (unique_of_pairwise pw) balanced'
  let sys' : Tiling.System F := { S.system with circuits := wide }
  have lenC : S.system.circuits.length = wide.length := by
    rw [circuits, List.length_zipWith, lenG, Nat.min_self]
  have circuitAt : ∀ f (hw : f < wide.length), S.system.circuits[f]? =
      some (wide[f].mergeBy (groups[f]'(by omega))) := by
    intro f hw
    rw [circuits, List.getElem?_zipWith, List.getElem?_eq_getElem hw,
      List.getElem?_eq_getElem (show f < groups.length by omega)]
  have ledgerEq : S.system.wideLedger (S.system.wideRow (S.mainV main)) =
      sys'.wideLedger (sys'.wideRow (S.mainV main)) := by
    simp only [Tiling.System.wideLedger, sys', lenC]
    congr 1
    apply List.map_congr_left
    intro f hf
    have hw : f < wide.length := List.mem_range.mp hf
    congr 1
    apply List.map_congr_left
    intro i _
    rw [circuitAt f hw, List.getElem?_eq_getElem hw]
    simp only [Option.map_some, Option.getD_some]
    exact Tiling.rowLedger_mergeBy (merged f hw (by omega)) _
  rw [ledgerEq] at wideBalanced
  have wideEq' : wide = units.map (Bridge.unitCircuit idOf) ++ ([] : List (List F)).map tableCircuit := by
    simp [wideEq]
  obtain ⟨tables0, support, split⟩ := Tiling.System.wideLedger_units sys' wideEq' unrolled (S.mainV main)
  have zero0 : tables0 = 0 := by
    ext t
    by_contra h
    simpa using support t h
  rw [split, zero0, add_zero] at wideBalanced
  have requestWide : request.wide = Finsupp.single (Bridge.encode idOf root) 1 := by
    simp [Part.wide, reqFacts.tuple, reqFacts.weight]
  simp only [List.map_cons, List.sum_cons, requestWide] at wideBalanced
  rw [← add_assoc] at wideBalanced
  have W : Wide plan idOf bound (Erasure.rawROM rom) root
      (instancesU idOf units S.system (S.mainV main)) (XT.map Part.wide).sum := {
    chips := fun p hp => by
      obtain ⟨f, hf, i, _, e, _⟩ := mem_instancesU hp
      rw [e]
      exact chipsIn _ (List.getElem_mem hf)
    holds := fun p hp => by
      obtain ⟨f, hf, i, hi, e, hr⟩ := mem_instancesU hp
      have hw : f < wide.length := by rw [wideEq]; simp; omega
      have lt : f < S.system.circuits.length := by rw [lenC]; exact hw
      have hw' : wide[f]? = some (Bridge.unitCircuit idOf units[f]) := by
        rw [wideEq]
        simp [hf]
      have ec : (S.system.circuits[f]'lt).constraints = (Bridge.unitCircuit idOf units[f]).constraints := by
        rw [Option.some.inj ((List.getElem?_eq_getElem lt).symm.trans (circuitAt f hw)),
          Tiling.mergeBy_constraints, Option.some.inj ((List.getElem?_eq_getElem hw).symm.trans hw')]
      have := holds f lt i hi
      have h' : (Bridge.unitCircuit idOf units[f]).Holds (S.system.wideRow (S.mainV main) f i) := by
        unfold Tiling.Circuit.Holds at this ⊢
        rw [ec] at this
        exact this
      rw [e]
      exact unit_holds h' _ hr
    small := small
    enablesOk := enablesOk
    tags := by omega
    count := by rw [lookupCount_instancesU]; exact lookups
    shaped := Shaped.of_check shaped
    romPacked := romPacked
    tableSupport := fun t ht => by
      obtain ⟨x, hx, hne⟩ := Periodic.exists_of_sum_ne ht
      have tx : t = x.tuple := by
        by_contra h
        simp [Part.wide, Ne.symm h] at hne
      obtain ⟨T, t', i, hi, hT, rfl⟩ := Periodic.mem_compactParts hx
      have mT := List.mem_of_getElem? hT
      rcases (each T mT).2 with km | kr
      · left
        rw [tx, Periodic.Compact.map_part (each T mT).1 km W4 _ hi]
        obtain ⟨mc, hmc, e⟩ := List.mem_map.mp (mapsIn T mT km _ (List.getElem_mem hi))
        exact ⟨mc, hmc, e.symm⟩
      · right
        have rp := Periodic.Compact.rom_part (each T mT).1 kr W4 (mainT t') hi
        refine ⟨_, ?_, by rw [tx]; exact rp.1⟩
        apply (Erasure.mem_rawROM).mpr
        simp only [rom, Periodic.compactRom, List.mem_map]
        refine ⟨_, ?_, rfl⟩
        simp only [Periodic.romParts, List.mem_flatMap]
        refine ⟨(T, t'), List.mk_mem_zipIdx_iff_getElem?.mpr hT, ?_⟩
        simp only [kr, ite_true]
        exact List.getElem_mem _
    balanced := wideBalanced }
  obtain ⟨weighted, length, checked⟩ := W.checkMemo activated context'
  exact ⟨valid, prepared.depth_grouped_activated_heap_sound compiled certified hbits plan activated
    entry valid signed rooted outside
    ((length.trans (length_instancesU _ _ _ _).le).trans capacity)
    characteristic checked arguments decoded⟩

/-! ## 4. Lowering-Independent PLONK Stage Certificate & Soundness

`Aiur.Plonk.stageOk` calls `Aiur.Plonk.Lower.lowerRow` (an untrusted lowerer containing
`partial def` helpers) to reconstruct each row's gate array before passing it to the total
checkers (`Template.check`, `coversVars`, `realisedB`, `colsB`, `AirIn.chainOk`).
`PlonkStageCert` and `PlonkStageWiring` factor out the untrusted lowering output `(rowGates,
rowFin)` as explicit parameters:
- Any `Aiur.Plonk.stageOk` + `Aiur.Plonk.Wiring` + `Aiur.Plonk.emitScs` instance immediately
  produces a `PlonkStageCert` / `PlonkStageWiring` whose `emitCertifiedScs` is definitionally
  equal (`rfl`) to `Aiur.Plonk.emitScs`.
- Explicit certificates avoid every `partial def` / `while` loop, so they reduce completely
  inside the Lean kernel with zero `native_decide`. -/

/-- Explicit, lowering-independent PLONK stage certificate for AIR tables `airs` and global pool `P`. -/
structure PlonkStageCert {F : Type} [Field F] [DecidableEq F]
    (airs : List (WideStage.Air F)) (P : Lower.Pool F) where
  rowGates : Nat × Nat → Array (Lower.LGate F)
  rowFin : Nat × Nat → Lower.Ref
  poolClosedOk : poolClosed P = true
  constraintCerts : ∀ i ∈ Plonk.instances airs,
    ∀ j < (airAt airs i.1).circuit.constraints.length,
      ∃ (T : Template F) (sr : Nat → Lower.Ref),
        T.check (AirIn.rowConstraint (airAt airs i.1) i.2 j) = true ∧
        coversVars T (airAt airs i.1).circuit.width (AirIn.rowConstraint (airAt airs i.1) i.2 j) = true ∧
        realisedB T sr ((rowGates i).filter (·.tag == .constraint)).toList = true ∧
        colsB T sr = true
  msgCerts : Nat × Nat → Nat → Except String (Option (AirIn.MsgCert F))
  chainOk : ∀ i ∈ Plonk.instances airs,
    AirIn.chainOk (airAt airs i.1) i.2 (AirIn.rowPool (rowGates i) P.gates) (msgCerts i)
      (List.range (airAt airs i.1).circuit.lookups.length) Lower.sumIn (rowFin i) = true

/-- Wire layout connecting row-local gates, cell wires, pool wires, and the running-sum chain
for an explicit `rowFin` map. -/
structure PlonkStageWiring {F : Type} (airs : List (WideStage.Air F)) (P : Lower.Pool F)
    (rowFin : Nat × Nat → Lower.Ref) where
  wireOf : Nat × Nat → Lower.Ref → Nat
  cellWire : Nat × Nat → Nat → Nat
  poolWire : Lower.Ref → Nat
  init : Nat
  last : Nat
  cell_eq : ∀ i x, x % 4 = 0 → wireOf i x = cellWire i (x / 8)
  pool_eq : ∀ i x, x % 4 = 2 → wireOf i x = poolWire x
  linked : Linked (fun i => wireOf i Lower.sumIn) (fun i => wireOf i (rowFin i)) init
    (Plonk.instances airs) last

def PlonkStageWiring.main {F : Type} {airs : List (WideStage.Air F)} {P : Lower.Pool F}
    {rowFin : Nat × Nat → Lower.Ref} (W : PlonkStageWiring airs P rowFin) (w : Nat → F)
    (t r c : Nat) : F :=
  w (W.cellWire (t, r) c)

/-- Emitted PLONK gates for an explicit `rowGates` / `PlonkStageWiring` pair. Definitionally
equal to `Aiur.Plonk.emitGates` when `rowGates i = (rowState airs P i).gates`. -/
def emitCertifiedGates {F : Type} [Field F] (airs : List (WideStage.Air F)) (P : Lower.Pool F)
    (rowGates : Nat × Nat → Array (Lower.LGate F)) (rowFin : Nat × Nat → Lower.Ref)
    (W : PlonkStageWiring airs P rowFin) : List (Gate F) :=
  [⟨W.last, W.last, W.last, 1, 0, 0, 0, 0⟩, ⟨W.init, W.init, W.init, 1, 0, 0, 0, 0⟩] ++
    P.gates.toList.map (·.inst W.poolWire) ++
    (Plonk.instances airs).flatMap fun i => (rowGates i).toList.map (·.inst (W.wireOf i))

/-- Emitted `Aiur.Plonk.Scs` for an explicit `rowGates` / `PlonkStageWiring` pair.
Definitionally equal to `Aiur.Plonk.emitScs` when `rowGates i = (rowState airs P i).gates`. -/
def emitCertifiedScs {F : Type} [Field F] (airs : List (WideStage.Air F)) (P : Lower.Pool F)
    (rowGates : Nat × Nat → Array (Lower.LGate F)) (rowFin : Nat × Nat → Lower.Ref)
    (W : PlonkStageWiring airs P rowFin) (wires publics : Nat) (committed : List Nat) :
    Scs F :=
  { wires, publics, committed, gamma := W.poolWire Lower.gammaRef,
    gates := emitCertifiedGates airs P rowGates rowFin W }

/-- Any `Aiur.Plonk.stageOk` certificate immediately yields a `PlonkStageCert`. -/
def PlonkStageCert.ofStageOk {p : Nat} [Fact (Nat.Prime p)]
    {airs : List (WideStage.Air (ZMod p))} {P : Lower.Pool (ZMod p)}
    {poolIdx : Lower.Ref → Option Nat} (ok : stageOk airs P poolIdx = true) :
    PlonkStageCert airs P where
  rowGates := fun i => (rowState airs P i).gates
  rowFin := fun i => (rowState airs P i).sum
  poolClosedOk := (Bool.and_eq_true _ _ |>.mp ok).1
  constraintCerts := by
    intro i hi j hj
    obtain ⟨x, hx, hix, hr, hat⟩ := mem_instances hi
    have hmem : x.1 ∈ airs := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hx)
    have hrc := rowCheck_of_stageOk ok hmem hr
    simp only [AirIn.rowCheck, Bool.and_eq_true] at hrc
    have hi1 : i.1 = x.2 := congrArg Prod.fst hix
    have hat' : airAt airs i.1 = x.1 := by rw [hi1, hat]
    have hcone := List.all_eq_true.mp hrc.1 j (List.mem_range.mpr (by rwa [hat'] at hj))
    obtain ⟨T, sr, hcheck, hcover, hreal, hcols⟩ := AirIn.coneOkR_spec hcone
    refine ⟨T, sr, ?_, ?_, ?_, hcols⟩
    · rwa [hat']
    · rwa [hat']
    · simpa [rowState, hat'] using hreal
  msgCerts := fun i k =>
    let gs := (rowState airs P i).gates
    let (localDef, byMsg) := AirIn.msgIndex gs
    let n := gs.size
    let defOf (x : Lower.Ref) : Option Nat :=
      if x % 4 == 2 then (poolIdx x).map (· + n) else localDef[x]?
    AirIn.msgCert (airAt airs i.1) (AirIn.rowPool gs P.gates) defOf (byMsg.getD k #[])
  chainOk := by
    intro i hi
    obtain ⟨x, hx, hix, hr, hat⟩ := mem_instances hi
    have hmem : x.1 ∈ airs := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hx)
    have hrc := rowCheck_of_stageOk ok hmem hr
    simp only [AirIn.rowCheck, Bool.and_eq_true] at hrc
    have hi1 : i.1 = x.2 := congrArg Prod.fst hix
    have hat' : airAt airs i.1 = x.1 := by rw [hi1, hat]
    simpa [AirIn.msgChainOk, rowState, hat'] using hrc.2

/-- Any `Aiur.Plonk.Wiring` immediately yields a `PlonkStageWiring`. -/
def PlonkStageWiring.ofWiring {p : Nat} [Fact (Nat.Prime p)]
    {airs : List (WideStage.Air (ZMod p))} {P : Lower.Pool (ZMod p)}
    (W : Wiring airs P) : PlonkStageWiring airs P (fun i => (rowState airs P i).sum) where
  wireOf := W.wireOf
  cellWire := W.cellWire
  poolWire := W.poolWire
  init := W.init
  last := W.last
  cell_eq := W.cell_eq
  pool_eq := W.pool_eq
  linked := W.linked

theorem certified_stage_sound {F : Type} [Field F] [DecidableEq F]
    {airs : List (WideStage.Air F)} {P : Lower.Pool F}
    (cert : PlonkStageCert airs P) (W : PlonkStageWiring airs P cert.rowFin) (w : Nat → F)
    (sat : ∀ g ∈ emitCertifiedGates airs P cert.rowGates cert.rowFin W, g.Holds w) :
    WideStage.StageHolds airs (W.main w) ∧
      ((∀ u, MsgTuple airs (W.main w) u →
          fp (w (W.poolWire Lower.gammaRef)) (w (W.poolWire Lower.betaRef)) u ≠ 0) →
        logupEval (w (W.poolWire Lower.gammaRef)) (w (W.poolWire Lower.betaRef))
          (WideStage.stageLedger airs (W.main w)) = - w W.init) := by
  have hlast : w W.last = 0 := by
    have := sat _ (List.mem_append.mpr (.inl (List.mem_append.mpr (.inl List.mem_cons_self))))
    simpa [Gate.Holds] using this
  have hpoolW : ∀ g ∈ P.gates, (g.inst W.poolWire).Holds w := fun g hg =>
    sat _ (List.mem_append.mpr (.inl (List.mem_append.mpr (.inr
      (List.mem_map.mpr ⟨g, Array.mem_toList_iff.mpr hg, rfl⟩)))))
  have row : ∀ x ∈ airs.zipIdx, ∀ r < x.1.rows,
      x.1.circuit.Holds (x.1.assign (W.main w x.2) r) ∧
        ((∀ l ∈ x.1.circuit.lookups,
            fp (w (W.poolWire Lower.gammaRef)) (w (W.poolWire Lower.betaRef))
              (l.tuple (x.1.assign (W.main w x.2) r)) ≠ 0) →
          w (W.wireOf (x.2, r) (cert.rowFin (x.2, r))) - w (W.wireOf (x.2, r) Lower.sumIn) =
            logupEval (w (W.poolWire Lower.gammaRef)) (w (W.poolWire Lower.betaRef))
              (x.1.circuit.rowLedger (x.1.assign (W.main w x.2) r))) := by
    intro x hx r hr
    have hat : airAt airs x.2 = x.1 := by
      have := List.mem_zipIdx_iff_getElem?.mp hx
      simp [airAt, List.getD_eq_getElem?_getD, this]
    have hin : (x.2, r) ∈ Plonk.instances airs := by
      unfold Plonk.instances
      simp only [List.mem_flatMap, List.mem_map, List.mem_range]
      exact ⟨x, hx, r, hr, rfl⟩
    have hrow : ∀ g ∈ cert.rowGates (x.2, r), (g.inst (W.wireOf (x.2, r))).Holds w := fun g hg =>
      sat _ (List.mem_append.mpr (.inr (List.mem_flatMap.mpr ⟨(x.2, r), hin,
        List.mem_map.mpr ⟨g, Array.mem_toList_iff.mpr hg, rfl⟩⟩)))
    have hpool : ∀ g ∈ P.gates, (g.inst (W.wireOf (x.2, r))).Holds w := fun g hg => by
      rw [gate_inst_pool cert.poolClosedOk (W.pool_eq (x.2, r)) hg]
      exact hpoolW g hg
    refine ⟨?_, ?_⟩
    · intro c hc
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
      obtain ⟨T, sr, hcheck, hcover, hreal, hcols⟩ :=
        cert.constraintCerts (x.2, r) hin j (by simpa [hat] using hj)
      rw [hat] at hcheck hcover
      have hold' : ∀ g ∈ ((cert.rowGates (x.2, r)).filter (·.tag == .constraint)).toList.map
          (Lower.LGate.inst (W.wireOf (x.2, r))), g.Holds w := by
        intro g hg
        obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
        exact hrow g' (Array.mem_of_mem_filter (Array.mem_toList_iff.mp hg'))
      have holds := relationsHold_of_realised (realised_of_realisedB hreal (W.wireOf (x.2, r))) hold'
      refine AirIn.constraint_of_cone hcheck hcover holds ?_ hj
      intro v _ s hs
      have hslot := AirIn.colSlot_column hs
      have hc' := List.all_eq_true.mp hcols (SlotDef.column v, s)
        (List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using hslot))
      simp only [Bool.and_eq_true, beq_iff_eq] at hc'
      simp [Function.comp, W.cell_eq (x.2, r) _ hc'.1, hc'.2, PlonkStageWiring.main]
    · intro hfp
      have hγ := W.pool_eq (x.2, r) Lower.gammaRef (by decide)
      have hβ := W.pool_eq (x.2, r) Lower.betaRef (by decide)
      have hch := cert.chainOk (x.2, r) hin
      rw [hat] at hch
      have hsum := AirIn.chain_sound (W.wireOf (x.2, r)) (W.cellWire (x.2, r))
        (W.cell_eq (x.2, r)) w
        (fun i g hg => by
          rcases AirIn.rowPool_mem hg with h | h
          · exact hrow g h
          · exact hpool g h)
        (W.main w x.2) (fun _ => rfl) _ _ _ hch
        (fun k hk => by
          have hk' := List.mem_range.mp hk
          rw [hγ, hβ]
          exact hfp _ (by
            simp [AirIn.lookupAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk',
              List.getElem_mem]))
      rw [AirIn.logupEval_rowLedger]
      simpa [hγ, hβ] using hsum
  refine ⟨fun x hx r hr => (row x hx r hr).1, fun hfp => ?_⟩
  have tele := (W.linked.map w).telescope
  rw [hlast, zero_sub] at tele
  rw [tele, sum_instances airs _ (fun a t r =>
    logupEval (w (W.poolWire Lower.gammaRef)) (w (W.poolWire Lower.betaRef))
      (a.circuit.rowLedger (a.assign (W.main w t) r)))]
  · rw [WideStage.stageLedger, map_list_sum, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro x _
    simp [WideStage.Air.ledger, map_list_sum, List.map_map, Function.comp_def]
  · intro x hx r hr
    exact (row x hx r hr).2 fun l hl => hfp _ ⟨x, hx, r, hr, l, hl, rfl⟩

theorem certified_stage_balanced {F : Type} [Field F] [DecidableEq F]
    {airs : List (WideStage.Air F)} {k : F} {n : Nat}
    {P : Lower.Pool F} (cert : PlonkStageCert (airs ++ [rootAir k n]) P)
    (W : PlonkStageWiring (airs ++ [rootAir k n]) P cert.rowFin) (w : Nat → F)
    (sat : ∀ g ∈ emitCertifiedGates (airs ++ [rootAir k n]) P cert.rowGates cert.rowFin W, g.Holds w)
    (good : ChallengeGood (w (W.poolWire Lower.gammaRef)) (w (W.poolWire Lower.betaRef))
      (MsgTuple (airs ++ [rootAir k n]) (W.main w))
      (WideStage.stageLedger (airs ++ [rootAir k n]) (W.main w))) :
    WideStage.StageHolds airs (W.main w) ∧
      WideStage.stageLedger airs (W.main w) +
        Finsupp.single ((CALL : F) :: k :: (List.range n).map (W.main w airs.length 0)) 1 = 0 := by
  obtain ⟨holds, eval⟩ := certified_stage_sound cert W w sat
  have hinit : w W.init = 0 := by
    have := sat ⟨W.init, W.init, W.init, 1, 0, 0, 0, 0⟩
      (List.mem_append.mpr (.inl (List.mem_append.mpr (.inl (List.mem_cons_of_mem _ List.mem_cons_self)))))
    simpa [Gate.Holds] using this
  refine ⟨stageHolds_append_left holds, ?_⟩
  have h := good.2 (by rw [eval good.1, hinit, neg_zero])
  rw [stageLedger_append, stageLedger_root] at h
  simpa using h

/-- Shared-table grouped wide soundness with exempt SCCs (exact structural analogue of
`Aiur.Tiling.Grouped.grouped_heap_sound_shared_compiled`). -/
theorem grouped_heap_sound_shared_structural {F : Type} [Field F] [DecidableEq F]
    {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Physical.Prepared.DepthCertified compiled prepared cfg)
    (hbits : cfg.bits ≤ 24)
    {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id)
    (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue F)} {result : Value F}
    {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) (idOk : ∀ x n, id x = .ok n → n = idOf x)
    (names : (circuitNames plan).Nodup)
    {units : List ((Chip F × Option (Unroll F)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, Bridge.unitOk idOf u.1 = true)
    {groups : List (Grouping.Packed F id × Nat)}
    (groupsIn : ∀ x ∈ groups, x.1 ∈ plan.groups)
    (capacity : WideStage.unitCapRows units + (groups.map (·.2)).sum ≤ 2 ^ 39)
    {shared : List (SharedTable F)}
    (sharedOk : ∀ T ∈ shared,
      T.check ((Depth.system cfg prepared.system).mapClaims.map (Bridge.encode idOf)) = true)
    {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound) (romWidths : ∀ r ∈ roms, r.1 < bound)
    (small : SmallCast F bound) (tags : 2 < bound)
    (lookups : WideStage.unitCapLookups units + (groups.map fun x => x.2 * groupCost x.1).sum < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ 24 → (n : F) ≠ 0)
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x < bound)
    (enablesOk : ∀ c ∈ allChips plan, Bridge.checkEnables bound c = true)
    (memWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < bound)
    {mainU mainG mainM mainR : Nat → Nat → Scalar.Circuit.Var → F}
    (holds : WideStage.StageHolds (WideStage.unitAirs idOf units) mainU)
    (holdsG : WideStage.StageHolds (groupAirs groups) mainG)
    (balanced : Finsupp.mapDomain trimZeros
      (WideStage.stageLedger (WideStage.unitAirs idOf units) mainU +
        WideStage.stageLedger (groupAirs groups) mainG +
        WideStage.stageLedger (shared.map SharedTable.air) mainM +
        WideStage.stageLedger (WideStage.romAirs roms) mainR +
        Finsupp.single (Bridge.encode idOf root) 1) = 0) :
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result :=
  grouped_heap_sound_core_structural compiled prepared certified hbits plan activated entry signed
    rooted outside entryPlain arguments decoded idOf idOk names chipsIn unrolled groupsIn capacity
    (shared_support sharedOk mainM) widths romCaps romWidths small tags lookups characteristic
    chanIds chanBound enablesOk memWidth holds holdsG balanced

/-- **Generic-Field Certified Shared-Map PLONK SCS Soundness with Exempt SCCs:**
Lowering-independent shared-map PLONK soundness over any field `F` with characteristic above
`2^39 * 2^24` (instantiated below at both BN254 and BLS12-381). -/
theorem plonk_shared_heap_sound_certified_field {F : Type} [Field F] [DecidableEq F]
    {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Physical.Prepared.DepthCertified compiled prepared cfg)
    (hbits : cfg.bits ≤ 24)
    {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id)
    (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue F)} {result : Value F}
    {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) (idOk : ∀ x n, id x = .ok n → n = idOf x)
    (names : (circuitNames plan).Nodup)
    {units : List ((Chip F × Option (Unroll F)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, Bridge.unitOk idOf u.1 = true)
    (capacity : WideStage.unitCapRows units ≤ 2 ^ 39)
    {shared : List (SharedTable F)}
    (sharedOk : ∀ T ∈ shared,
      T.check ((Depth.system cfg prepared.system).mapClaims.map (Bridge.encode idOf)) = true)
    {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound) (romWidths : ∀ r ∈ roms, r.1 < bound)
    (small : SmallCast F bound) (tags : 2 < bound)
    (lookups : WideStage.unitCapLookups units < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ 24 → (n : F) ≠ 0)
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x < bound)
    (enablesOk : ∀ c ∈ allChips plan, Bridge.checkEnables bound c = true)
    (memWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < bound)
    {airs : List (WideStage.Air F)}
    (hairs : airs = WideStage.unitAirs idOf units ++ shared.map SharedTable.air ++ WideStage.romAirs roms)
    {k : F} {n : Nat} {P : Lower.Pool F}
    (cert : PlonkStageCert (airs ++ [rootAir k n]) P)
    (W : PlonkStageWiring (airs ++ [rootAir k n]) P cert.rowFin)
    {nWires publics : Nat} {committed : List Nat} {w : Nat → F} {pub : List F}
    {H : List F → F}
    (sat : (emitCertifiedScs (airs ++ [rootAir k n]) P cert.rowGates cert.rowFin W nWires publics committed).Satisfied w pub H)
    (entryId : (idOf root.channel : F) = k)
    (statement : (List.range n).map (W.main w airs.length 0) = (Bridge.encode idOf root).drop 2)
    (good : ChallengeGood (w (W.poolWire Lower.gammaRef)) (w (W.poolWire Lower.betaRef))
      (MsgTuple (airs ++ [rootAir k n]) (W.main w))
      (WideStage.stageLedger (airs ++ [rootAir k n]) (W.main w))) :
    let mainR := fun t => W.main w ((WideStage.unitAirs idOf units).length + shared.length + t)
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result := by
  intro mainR
  obtain ⟨holds, balanced⟩ := certified_stage_balanced cert W w sat.2.2 good
  have hroot : (CALL : F) :: k :: (Bridge.encode idOf root).drop 2 = Bridge.encode idOf root := by
    rw [← entryId]; rfl
  rw [statement, hroot] at balanced
  subst hairs
  rw [stageLedger_append, stageLedger_append] at balanced
  refine grouped_heap_sound_shared_structural compiled prepared certified hbits plan activated entry signed
    rooted outside entryPlain arguments decoded idOf idOk names chipsIn unrolled (groups := [])
    (fun _ h => absurd h List.not_mem_nil) (by simpa using capacity) sharedOk
    widths romCaps romWidths small tags (by simpa using lookups) characteristic
    chanIds chanBound enablesOk memWidth
    (mainU := W.main w) (mainG := W.main w)
    (mainM := fun t => W.main w ((WideStage.unitAirs idOf units).length + t)) (mainR := mainR)
    (stageHolds_append_left (stageHolds_append_left holds)) (fun _ h => absurd h List.not_mem_nil) ?_
  have hG : WideStage.stageLedger (groupAirs ([] : List (Grouping.Packed F id × Nat))) (W.main w) = 0 := rfl
  rw [hG, add_zero, ← Finsupp.mapDomain_zero (f := trimZeros)]
  congr 1
  rw [← balanced]
  simp only [List.length_append, List.length_map, mainR, add_assoc]

/-- **Stage 4 (`CompressFinalNarrow`, BN254) Certified Shared-Map PLONK SCS Soundness with Exempt SCCs:**
Lowering-independent generalization of `plonk_shared_heap_sound_structural` accepting an explicit
`PlonkStageCert` and `PlonkStageWiring`. -/
theorem plonk_shared_heap_sound_certified
    {source : Generic.Source Bn254F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Physical.Prepared.DepthCertified compiled prepared cfg)
    (hbits : cfg.bits ≤ 24)
    {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id)
    (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue Bn254F)} {result : Value Bn254F}
    {wires : List (WireValue Bn254F)} {output : WireValue Bn254F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message Bn254F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) (idOk : ∀ x n, id x = .ok n → n = idOf x)
    (names : (circuitNames plan).Nodup)
    {units : List ((Chip Bn254F × Option (Unroll Bn254F)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, Bridge.unitOk idOf u.1 = true)
    (capacity : WideStage.unitCapRows units ≤ 2 ^ 39)
    {shared : List (SharedTable Bn254F)}
    (sharedOk : ∀ T ∈ shared,
      T.check ((Depth.system cfg prepared.system).mapClaims.map (Bridge.encode idOf)) = true)
    {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound) (romWidths : ∀ r ∈ roms, r.1 < bound)
    (small : SmallCast Bn254F bound) (tags : 2 < bound)
    (lookups : WideStage.unitCapLookups units < bound)
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x < bound)
    (enablesOk : ∀ c ∈ allChips plan, Bridge.checkEnables bound c = true)
    (memWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < bound)
    {airs : List (WideStage.Air Bn254F)}
    (hairs : airs = WideStage.unitAirs idOf units ++ shared.map SharedTable.air ++ WideStage.romAirs roms)
    {k : Bn254F} {n : Nat} {P : Lower.Pool Bn254F}
    (cert : PlonkStageCert (airs ++ [rootAir k n]) P)
    (W : PlonkStageWiring (airs ++ [rootAir k n]) P cert.rowFin)
    {nWires publics : Nat} {committed : List Nat} {w : Nat → Bn254F}
    {pub : List Bn254F} {H : List Bn254F → Bn254F}
    (sat : (emitCertifiedScs (airs ++ [rootAir k n]) P cert.rowGates cert.rowFin W nWires publics committed).Satisfied w pub H)
    (entryId : (idOf root.channel : Bn254F) = k)
    (statement : (List.range n).map (W.main w airs.length 0) = (Bridge.encode idOf root).drop 2)
    (good : ChallengeGood (w (W.poolWire Lower.gammaRef)) (w (W.poolWire Lower.betaRef))
      (MsgTuple (airs ++ [rootAir k n]) (W.main w))
      (WideStage.stageLedger (airs ++ [rootAir k n]) (W.main w))) :
    let mainR := fun t => W.main w ((WideStage.unitAirs idOf units).length + shared.length + t)
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result :=
  plonk_shared_heap_sound_certified_field compiled prepared certified hbits plan activated entry signed
    rooted outside entryPlain arguments decoded idOf idOk names chipsIn unrolled capacity
    sharedOk widths romCaps romWidths small tags lookups bn254_characteristic_24
    chanIds chanBound enablesOk memWidth hairs cert W sat entryId statement good

/-- **Stage 4 (`CompressFinalNarrow`, BN254) Shared-Map PLONK SCS Soundness with Exempt SCCs:**
Matches `Aiur.Plonk.plonk_shared_heap_sound` while accepting `Physical.Prepared.DepthCertified`. -/
theorem plonk_shared_heap_sound_structural
    {source : Generic.Source Bn254F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Physical.Prepared.DepthCertified compiled prepared cfg)
    (hbits : cfg.bits ≤ 24)
    {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id)
    (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue Bn254F)} {result : Value Bn254F}
    {wires : List (WireValue Bn254F)} {output : WireValue Bn254F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message Bn254F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) (idOk : ∀ x n, id x = .ok n → n = idOf x)
    (names : (circuitNames plan).Nodup)
    {units : List ((Chip Bn254F × Option (Unroll Bn254F)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, Bridge.unitOk idOf u.1 = true)
    (capacity : WideStage.unitCapRows units ≤ 2 ^ 39)
    {shared : List (SharedTable Bn254F)}
    (sharedOk : ∀ T ∈ shared,
      T.check ((Depth.system cfg prepared.system).mapClaims.map (Bridge.encode idOf)) = true)
    {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound) (romWidths : ∀ r ∈ roms, r.1 < bound)
    (small : SmallCast Bn254F bound) (tags : 2 < bound)
    (lookups : WideStage.unitCapLookups units < bound)
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x < bound)
    (enablesOk : ∀ c ∈ allChips plan, Bridge.checkEnables bound c = true)
    (memWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < bound)
    {airs : List (WideStage.Air Bn254F)}
    (hairs : airs = WideStage.unitAirs idOf units ++ shared.map SharedTable.air ++ WideStage.romAirs roms)
    {k : Bn254F} {n : Nat} {P : Lower.Pool Bn254F}
    {poolIdx : Lower.Ref → Option Nat}
    (ok : stageOk (airs ++ [rootAir k n]) P poolIdx = true)
    (W : Wiring (airs ++ [rootAir k n]) P)
    {nWires publics : Nat} {committed : List Nat} {w : Nat → Bn254F}
    {pub : List Bn254F} {H : List Bn254F → Bn254F}
    (sat : (emitScs (airs ++ [rootAir k n]) P W nWires publics committed).Satisfied w pub H)
    (entryId : (idOf root.channel : Bn254F) = k)
    (statement : (List.range n).map (W.main w airs.length 0) = (Bridge.encode idOf root).drop 2)
    (good : ChallengeGood (w (W.poolWire Lower.gammaRef)) (w (W.poolWire Lower.betaRef))
      (MsgTuple (airs ++ [rootAir k n]) (W.main w))
      (WideStage.stageLedger (airs ++ [rootAir k n]) (W.main w))) :
    let mainR := fun t => W.main w ((WideStage.unitAirs idOf units).length + shared.length + t)
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result :=
  plonk_shared_heap_sound_certified compiled prepared certified hbits plan activated entry signed
    rooted outside entryPlain arguments decoded idOf idOk names chipsIn unrolled capacity
    sharedOk widths romCaps romWidths small tags lookups chanIds chanBound enablesOk memWidth
    hairs (PlonkStageCert.ofStageOk ok) (PlonkStageWiring.ofWiring W) sat entryId statement good

/-- **BLS12-381 Certified Shared-Map PLONK SCS Soundness with Exempt SCCs:**
Instantiates `plonk_shared_heap_sound_certified_field` at `Aiur.Library.Field.BLS12381.F`
using `bls12381_characteristic_24`. -/
theorem plonk_shared_heap_sound_certified_bls12381
    {source : Generic.Source Aiur.Library.Field.BLS12381.F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Physical.Prepared.DepthCertified compiled prepared cfg)
    (hbits : cfg.bits ≤ 24)
    {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id)
    (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue Aiur.Library.Field.BLS12381.F)} {result : Value Aiur.Library.Field.BLS12381.F}
    {wires : List (WireValue Aiur.Library.Field.BLS12381.F)} {output : WireValue Aiur.Library.Field.BLS12381.F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message Aiur.Library.Field.BLS12381.F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) (idOk : ∀ x n, id x = .ok n → n = idOf x)
    (names : (circuitNames plan).Nodup)
    {units : List ((Chip Aiur.Library.Field.BLS12381.F × Option (Unroll Aiur.Library.Field.BLS12381.F)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, Bridge.unitOk idOf u.1 = true)
    (capacity : WideStage.unitCapRows units ≤ 2 ^ 39)
    {shared : List (SharedTable Aiur.Library.Field.BLS12381.F)}
    (sharedOk : ∀ T ∈ shared,
      T.check ((Depth.system cfg prepared.system).mapClaims.map (Bridge.encode idOf)) = true)
    {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound) (romWidths : ∀ r ∈ roms, r.1 < bound)
    (small : SmallCast Aiur.Library.Field.BLS12381.F bound) (tags : 2 < bound)
    (lookups : WideStage.unitCapLookups units < bound)
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x < bound)
    (enablesOk : ∀ c ∈ allChips plan, Bridge.checkEnables bound c = true)
    (memWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < bound)
    {airs : List (WideStage.Air Aiur.Library.Field.BLS12381.F)}
    (hairs : airs = WideStage.unitAirs idOf units ++ shared.map SharedTable.air ++ WideStage.romAirs roms)
    {k : Aiur.Library.Field.BLS12381.F} {n : Nat} {P : Lower.Pool Aiur.Library.Field.BLS12381.F}
    (cert : PlonkStageCert (airs ++ [rootAir k n]) P)
    (W : PlonkStageWiring (airs ++ [rootAir k n]) P cert.rowFin)
    {nWires publics : Nat} {committed : List Nat} {w : Nat → Aiur.Library.Field.BLS12381.F}
    {pub : List Aiur.Library.Field.BLS12381.F}
    {H : List Aiur.Library.Field.BLS12381.F → Aiur.Library.Field.BLS12381.F}
    (sat : (emitCertifiedScs (airs ++ [rootAir k n]) P cert.rowGates cert.rowFin W nWires publics committed).Satisfied w pub H)
    (entryId : (idOf root.channel : Aiur.Library.Field.BLS12381.F) = k)
    (statement : (List.range n).map (W.main w airs.length 0) = (Bridge.encode idOf root).drop 2)
    (good : ChallengeGood (w (W.poolWire Lower.gammaRef)) (w (W.poolWire Lower.betaRef))
      (MsgTuple (airs ++ [rootAir k n]) (W.main w))
      (WideStage.stageLedger (airs ++ [rootAir k n]) (W.main w))) :
    let mainR := fun t => W.main w ((WideStage.unitAirs idOf units).length + shared.length + t)
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result :=
  plonk_shared_heap_sound_certified_field compiled prepared certified hbits plan activated entry signed
    rooted outside entryPlain arguments decoded idOf idOk names chipsIn unrolled capacity
    sharedOk widths romCaps romWidths small tags lookups bls12381_characteristic_24
    chanIds chanBound enablesOk memWidth hairs cert W sat entryId statement good

/-- **BLS12-381 Shared-Map PLONK SCS Soundness with Exempt SCCs:**
Instantiates `Aiur.Plonk.plonk_shared_heap_sound` over `Aiur.Library.Field.BLS12381.F`
while accepting `Physical.Prepared.DepthCertified`. -/
theorem plonk_shared_heap_sound_structural_bls12381
    {source : Generic.Source Aiur.Library.Field.BLS12381.F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Physical.Prepared.DepthCertified compiled prepared cfg)
    (hbits : cfg.bits ≤ 24)
    {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id)
    (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue Aiur.Library.Field.BLS12381.F)} {result : Value Aiur.Library.Field.BLS12381.F}
    {wires : List (WireValue Aiur.Library.Field.BLS12381.F)} {output : WireValue Aiur.Library.Field.BLS12381.F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message Aiur.Library.Field.BLS12381.F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) (idOk : ∀ x n, id x = .ok n → n = idOf x)
    (names : (circuitNames plan).Nodup)
    {units : List ((Chip Aiur.Library.Field.BLS12381.F × Option (Unroll Aiur.Library.Field.BLS12381.F)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, Bridge.unitOk idOf u.1 = true)
    (capacity : WideStage.unitCapRows units ≤ 2 ^ 39)
    {shared : List (SharedTable Aiur.Library.Field.BLS12381.F)}
    (sharedOk : ∀ T ∈ shared,
      T.check ((Depth.system cfg prepared.system).mapClaims.map (Bridge.encode idOf)) = true)
    {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound) (romWidths : ∀ r ∈ roms, r.1 < bound)
    (small : SmallCast Aiur.Library.Field.BLS12381.F bound) (tags : 2 < bound)
    (lookups : WideStage.unitCapLookups units < bound)
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x < bound)
    (enablesOk : ∀ c ∈ allChips plan, Bridge.checkEnables bound c = true)
    (memWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < bound)
    {airs : List (WideStage.Air Aiur.Library.Field.BLS12381.F)}
    (hairs : airs = WideStage.unitAirs idOf units ++ shared.map SharedTable.air ++ WideStage.romAirs roms)
    {k : Aiur.Library.Field.BLS12381.F} {n : Nat} {P : Lower.Pool Aiur.Library.Field.BLS12381.F}
    {poolIdx : Lower.Ref → Option Nat}
    (ok : stageOk (airs ++ [rootAir k n]) P poolIdx = true)
    (W : Wiring (airs ++ [rootAir k n]) P)
    {nWires publics : Nat} {committed : List Nat} {w : Nat → Aiur.Library.Field.BLS12381.F}
    {pub : List Aiur.Library.Field.BLS12381.F}
    {H : List Aiur.Library.Field.BLS12381.F → Aiur.Library.Field.BLS12381.F}
    (sat : (emitScs (airs ++ [rootAir k n]) P W nWires publics committed).Satisfied w pub H)
    (entryId : (idOf root.channel : Aiur.Library.Field.BLS12381.F) = k)
    (statement : (List.range n).map (W.main w airs.length 0) = (Bridge.encode idOf root).drop 2)
    (good : ChallengeGood (w (W.poolWire Lower.gammaRef)) (w (W.poolWire Lower.betaRef))
      (MsgTuple (airs ++ [rootAir k n]) (W.main w))
      (WideStage.stageLedger (airs ++ [rootAir k n]) (W.main w))) :
    let mainR := fun t => W.main w ((WideStage.unitAirs idOf units).length + shared.length + t)
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result :=
  plonk_shared_heap_sound_certified_bls12381 compiled prepared certified hbits plan activated entry signed
    rooted outside entryPlain arguments decoded idOf idOk names chipsIn unrolled capacity
    sharedOk widths romCaps romWidths small tags lookups chanIds chanBound enablesOk memWidth
    hairs (PlonkStageCert.ofStageOk ok) (PlonkStageWiring.ofWiring W) sat entryId statement good

end Ix.Cert.AiurCompression.DepthBridge
