import Aiur.Tiling.Grouped
import Aiur.Tiling.IxaProgram
import Aiur.Tiling.IxaTraceCodec

/-!
# Map claim channels from a compiled package

`Ixa.ids_ofChip` turns the exporters' `Package.checkIds` into the channel
hypotheses `chanIds` and `chanBound` of the composed theorems, given
`claimsIn`: every map claim of the depth system is on a channel among the
package's map names. That is a theorem here (`claimsIn_of_export`):

* the compiler's `exportBytecode` refuses a program map that is not an exported
  map, and appends the range map of every depth limb (`exportBytecode_maps`);
* the package's program section decodes to the exported bytecode
  (`program_of_decode`), so its map names are the exported maps' names;
* `Compiled.claimsIn_of_maps` covers the depth system's claims by those names.

`ids_of_export` combines it with `ids_ofChip`. The package's chips are the
written depth chips (`chips_of_export`: the trace section reads back), so the
exporters' `Package.checkIds` over the decoded chips is `checkIds` over the
written depth chips (`checkIds_of_package`). The `_exported` theorems are the
`_compiled` ones with `chanIds` and `chanBound` replaced by the export, the
decoded package and its `Package.checkIds`.
-/

namespace Aiur.Tiling.Claims

open Aiur.Circuit Aiur.Optimized Aiur.Ixon Aiur.Tiling.Ixa

variable {F : Type} [Field F] [DecidableEq F]

section Export

theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {r : β}
    (h : (x >>= f) = .ok r) : ∃ a, x = .ok a ∧ f a = .ok r := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- What a successful `exportBytecode` returns: the depth configuration, the
exported bytecode with the range maps, after checking every program map is
an exported map. -/
theorem exportBytecode_spec {modulus : Nat} {program : Program F} {artifact : Artifact F}
    {physical : Physical.Prepared artifact} {exported : Execution.Export F}
    {replays : Option (List (Except String (Trace.Replay F)))} {cfg : Depth.Config}
    {measures : Depth.Structural.Plan} {bytecode : Execution.Bytecode F}
    (h : Trace.exportBytecode modulus program artifact physical exported replays =
      .ok (cfg, measures, bytecode)) :
    Trace.depthConfig modulus program physical = .ok (cfg, measures) ∧
      bytecode = Trace.depthBytecode cfg exported.bytecode ∧
      ∀ m ∈ program.maps, m.name ∈ exported.bytecode.maps.map (·.name) := by
  unfold Trace.exportBytecode at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' (split at h <;> try (cases h; done))
  all_goals
    rename_i hcfg hmaps
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨hcfg, rfl, fun m hm => ?_⟩
    simp only [List.all_eq_true, List.any_eq_true, beq_iff_eq] at hmaps
    obtain ⟨x, hx, e⟩ := hmaps m hm
    exact List.mem_map.mpr ⟨x, hx, e⟩

theorem exportPrepared_spec {encoding : FieldEncoding} {modulus : Nat} {encode : F → Nat}
    {program : Program F} {artifact : Artifact F} {physical : Physical.Prepared artifact}
    {exported exported' : Execution.Export F} {groups : List (String × List String)}
    {replays : Option (List (Except String (Trace.Replay F)))} {trace : ByteArray}
    (h : Trace.exportPreparedPlanWithEncoding encoding modulus encode program artifact physical exported
      groups replays = .ok (exported', trace)) :
    ∃ cfg measures, Trace.depthConfig modulus program physical = .ok (cfg, measures) ∧
      exported'.bytecode = Trace.depthBytecode cfg exported.bytecode ∧
      ∀ m ∈ program.maps, m.name ∈ exported.bytecode.maps.map (·.name) := by
  unfold Trace.exportPreparedPlanWithEncoding at h
  obtain ⟨⟨cfg, measures, bytecode⟩, hb, h⟩ := except_bind_ok h
  obtain ⟨_, _, h⟩ := except_bind_ok h
  cases h
  obtain ⟨hcfg, rfl, maps⟩ := exportBytecode_spec hb
  exact ⟨cfg, measures, hcfg, rfl, maps⟩

omit [Field F] [DecidableEq F] in
/-- `depthBytecode` keeps the original maps and adds the range map of every
depth limb. -/
theorem depthBytecode_maps [NatCast F] (cfg : Depth.Config) (bytecode : Execution.Bytecode F) :
    (∀ m ∈ bytecode.maps, m.name ∈ (Trace.depthBytecode cfg bytecode).maps.map (·.name)) ∧
      ∀ w ∈ cfg.limbs, Depth.rangeName w ∈ (Trace.depthBytecode cfg bytecode).maps.map (·.name) := by
  refine ⟨fun m hm => ?_, fun w hw => ?_⟩
  · simp only [Trace.depthBytecode, List.map_append, List.mem_append]
    exact Or.inl (List.mem_map.mpr ⟨m, hm, rfl⟩)
  · simp only [Trace.depthBytecode, List.map_append, List.mem_append, List.map_map]
    refine Or.inr ?_
    have e : ∀ (l : List Nat), l.zipIdx.map (fun x => Depth.rangeName x.1) =
        (l.zipIdx.map Prod.fst).map Depth.rangeName := fun l => by rw [List.map_map]; rfl
    simp only [Function.comp_def]
    rw [e, List.zipIdx_map_fst]
    exact List.mem_map.mpr ⟨w, List.mem_dedup.mpr hw, rfl⟩

end Export

section Decode

omit [Field F] [DecidableEq F] in
theorem decodePackage_of_checked [NatCast F] {modulus : Nat} {encode : F → Nat} {bytes : ByteArray}
    {pkg : Package F} (h : decodeChecked modulus encode bytes = .ok pkg) :
    decodePackage modulus bytes = .ok pkg := by
  unfold decodeChecked at h
  obtain ⟨p, hp, h⟩ := except_bind_ok h
  obtain ⟨_, _, h⟩ := except_bind_ok h
  obtain ⟨_, _, h⟩ := except_bind_ok h
  simp only at h
  split at h
  · cases h
    exact hp
  · cases h

end Decode

section Claims

/-- The exporters' scalar encoding `ZMod.val` meets the hypotheses on `encode`. -/
theorem zmod_val_encodes (p : Nat) [NeZero p] :
    (∀ x : ZMod p, ((x.val : Nat) : ZMod p) = x) ∧ ∀ x : ZMod p, x.val < p :=
  ⟨ZMod.natCast_zmod_val, ZMod.val_lt⟩

/-- `claimsIn` of `Ixa.ids_ofChip` for the depth system, with the package's map
names as the claim channels: the package is the compiler's export of
`compiled` with depth configuration `cfg`, and `decodeChecked` accepted it. -/
theorem claimsIn_of_export {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    {measures : Depth.Structural.Plan}
    (certified : Depth.Certified cfg prepared.system) {encoding : FieldEncoding} {modulus : Nat}
    {encode : F → Nat} (hcast : ∀ x, ((encode x : Nat) : F) = x) (hlt : ∀ x, encode x < modulus)
    (hcfg : Trace.depthConfig modulus compiled.inlined.program prepared = .ok (cfg, measures))
    {exported exported' : Execution.Export F} {groups : List (String × List String)}
    {replays : Option (List (Except String (Trace.Replay F)))} {trace bytes : ByteArray}
    {pkg : Package F}
    (exportedOk : Trace.exportPreparedPlanWithEncoding encoding modulus encode compiled.inlined.program
      compiled.artifact prepared exported groups replays = .ok (exported', trace))
    (written : Ixon.run (Artifact.putPackageWithEncoding encoding exported' modulus encode (some trace)) =
      .ok bytes)
    (decoded : decodeChecked modulus encode bytes = .ok pkg) :
    ∀ mc ∈ (Depth.system cfg prepared.system).mapClaims, mc.channel ∈ pkg.mapNames := by
  obtain ⟨cfg', measures', hcfg', bc, maps⟩ := exportPrepared_spec exportedOk
  rw [hcfg] at hcfg'
  cases hcfg'
  have program := program_of_decode hcast hlt written (decodePackage_of_checked decoded)
  have names : pkg.mapNames = (Trace.depthBytecode cfg exported.bytecode).maps.map (·.name) := by
    rw [Package.mapNames, program, bc]
  obtain ⟨kept, ranges⟩ := depthBytecode_maps cfg exported.bytecode
  refine Compiled.claimsIn_of_maps compiled prepared certified (fun m hm => ?_) (fun w hw => ?_)
  · obtain ⟨x, hx, e⟩ := List.mem_map.mp (maps m hm)
    rw [names, ← e]
    exact kept x hx
  · rw [names]
    exact ranges w hw

/-- `chanIds` and `chanBound` for the package's numbering (`callables.idxOf`)
on any chips of the depth system, from `checkIds` over its written chips with
the package's map names. -/
theorem ids_of_export {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    {measures : Depth.Structural.Plan}
    (certified : Depth.Certified cfg prepared.system) {encoding : FieldEncoding} {modulus : Nat}
    {encode : F → Nat} (hcast : ∀ x, ((encode x : Nat) : F) = x) (hlt : ∀ x, encode x < modulus)
    (hcfg : Trace.depthConfig modulus compiled.inlined.program prepared = .ok (cfg, measures))
    {exported exported' : Execution.Export F} {groups : List (String × List String)}
    {replays : Option (List (Except String (Trace.Replay F)))} {trace bytes : ByteArray}
    {pkg : Package F}
    (exportedOk : Trace.exportPreparedPlanWithEncoding encoding modulus encode compiled.inlined.program
      compiled.artifact prepared exported groups replays = .ok (exported', trace))
    (written : Ixon.run (Artifact.putPackageWithEncoding encoding exported' modulus encode (some trace)) =
      .ok bytes)
    (decoded : decodeChecked modulus encode bytes = .ok pkg)
    {chips : List (Chip F)} (sub : ∀ c ∈ chips, c ∈ (Depth.system cfg prepared.system).chips)
    {root : Message F} {callables : List String} {bound : Nat}
    (checked : checkIds callables bound
      (IChip.channels ((Depth.system cfg prepared.system).chips.map IChip.ofChip) pkg.mapNames
        root.channel) = true) :
    (∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) chips root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) chips root,
        callables.idxOf x = callables.idxOf y → x = y) ∧
      ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) chips root, callables.idxOf x < bound :=
  ids_ofChip sub
    (claimsIn_of_export compiled prepared certified hcast hlt hcfg exportedOk written decoded) checked

/-- The chips of a package that the compiler exported with depth configuration
`cfg` and `decodeChecked` accepted are the written form of the depth system's
chips: the trace section reads back (`section_reads`) and the package decoder
returns its chips (`chips_of_decode`). -/
theorem chips_of_export {encoding : FieldEncoding} {modulus : Nat} {encode : F → Nat}
    (hcast : ∀ x, ((encode x : Nat) : F) = x) (hlt : ∀ x, encode x < modulus)
    {program : Program F} {artifact : Artifact F} {prepared : Physical.Prepared artifact}
    {cfg : Depth.Config} {measures : Depth.Structural.Plan}
    (hcfg : Trace.depthConfig modulus program prepared = .ok (cfg, measures))
    {exported exported' : Execution.Export F} {groups : List (String × List String)}
    {replays : Option (List (Except String (Trace.Replay F)))} {trace bytes : ByteArray}
    {pkg : Package F}
    (exportedOk : Trace.exportPreparedPlanWithEncoding encoding modulus encode program artifact prepared
      exported groups replays = .ok (exported', trace))
    (written : Ixon.run (Artifact.putPackageWithEncoding encoding exported' modulus encode (some trace)) =
      .ok bytes)
    (decoded : decodeChecked modulus encode bytes = .ok pkg) :
    pkg.chips.toList = (Depth.system cfg prepared.system).chips.map IChip.ofChip := by
  unfold Trace.exportPreparedPlanWithEncoding at exportedOk
  obtain ⟨⟨cfg', measures', bytecode⟩, hb, h⟩ := except_bind_ok exportedOk
  obtain ⟨trace', ht, h⟩ := except_bind_ok h
  cases h
  obtain ⟨hcfg', -, -⟩ := exportBytecode_spec hb
  rw [hcfg] at hcfg'
  cases hcfg'
  obtain ⟨t, rt, hchips, -⟩ := section_reads hcast hlt ht
  rw [(chips_of_decode hcast hlt written (decodePackage_of_checked decoded) rt).1, List.toList_toArray, hchips,
    List.map_map]
  have len : (Depth.system cfg prepared.system).chips.length = prepared.system.chips.length := by
    simp [Depth.system]
  have e : ∀ (xs : List (Chip F)) (ys : List (Chip F)), xs.length = ys.length →
      (xs.zip ys).map (fun p => IChip.ofChip p.1) = xs.map IChip.ofChip := by
    intro xs ys h
    induction xs generalizing ys with
    | nil => rfl
    | cons x xs ih =>
        cases ys with
        | nil => cases h
        | cons y ys => simp [ih ys (by simpa using h)]
  exact e _ _ len

/-- The depth limbs of a package that the compiler exported with depth
configuration `cfg` and `decodeChecked` accepted are `cfg.limbs`. -/
theorem limbs_of_export {encoding : FieldEncoding} {modulus : Nat} {encode : F → Nat}
    (hcast : ∀ x, ((encode x : Nat) : F) = x) (hlt : ∀ x, encode x < modulus)
    {program : Program F} {artifact : Artifact F} {prepared : Physical.Prepared artifact}
    {cfg : Depth.Config} {measures : Depth.Structural.Plan}
    (hcfg : Trace.depthConfig modulus program prepared = .ok (cfg, measures))
    {exported exported' : Execution.Export F} {groups : List (String × List String)}
    {replays : Option (List (Except String (Trace.Replay F)))} {trace bytes : ByteArray}
    {pkg : Package F}
    (exportedOk : Trace.exportPreparedPlanWithEncoding encoding modulus encode program artifact prepared
      exported groups replays = .ok (exported', trace))
    (written : Ixon.run (Artifact.putPackageWithEncoding encoding exported' modulus encode (some trace)) =
      .ok bytes)
    (decoded : decodeChecked modulus encode bytes = .ok pkg) :
    pkg.limbs = cfg.limbs := by
  unfold Trace.exportPreparedPlanWithEncoding at exportedOk
  obtain ⟨⟨cfg', measures', bytecode⟩, hb, h⟩ := except_bind_ok exportedOk
  obtain ⟨trace', ht, h⟩ := except_bind_ok h
  cases h
  obtain ⟨hcfg', -, -⟩ := exportBytecode_spec hb
  rw [hcfg] at hcfg'
  cases hcfg'
  obtain ⟨t, rt, -, hlimbs⟩ := section_reads hcast hlt ht
  rw [(chips_of_decode hcast hlt written (decodePackage_of_checked decoded) rt).2, hlimbs]

/-- The written chip channels of the exporters' `Package.checkIds`, for a
package that the compiler exported with depth configuration `cfg` and
`decodeChecked` accepted (`chips_of_export`). -/
theorem checkIds_of_package {encoding : FieldEncoding} {modulus : Nat} {encode : F → Nat}
    (hcast : ∀ x, ((encode x : Nat) : F) = x) (hlt : ∀ x, encode x < modulus)
    {program : Program F} {artifact : Artifact F} {prepared : Physical.Prepared artifact}
    {cfg : Depth.Config} {measures : Depth.Structural.Plan}
    (hcfg : Trace.depthConfig modulus program prepared = .ok (cfg, measures))
    {exported exported' : Execution.Export F} {groups : List (String × List String)}
    {replays : Option (List (Except String (Trace.Replay F)))} {trace bytes : ByteArray}
    {pkg : Package F}
    (exportedOk : Trace.exportPreparedPlanWithEncoding encoding modulus encode program artifact prepared
      exported groups replays = .ok (exported', trace))
    (written : Ixon.run (Artifact.putPackageWithEncoding encoding exported' modulus encode (some trace)) =
      .ok bytes)
    (decoded : decodeChecked modulus encode bytes = .ok pkg) {bound : Nat} {root : String}
    (h : pkg.checkIds bound root = true) :
    checkIds pkg.callables.toList bound
      (IChip.channels ((Depth.system cfg prepared.system).chips.map IChip.ofChip) pkg.mapNames root) =
      true := by
  rw [← chips_of_export hcast hlt hcfg exportedOk written decoded]
  exact h

end Claims

/-! ## The composed theorems over an exported package -/

section Exported

/-- What the exporters establish about the channel numbering `callables`: the
package is the compiler's export of `compiled` with depth configuration `cfg`
in a field whose integers `encode` represents, `decodeChecked` accepted it,
`callables` is its callable numbering, and the exporters' `Package.checkIds`
accepts it with the entry `root`. -/
def ExportedIds {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) (cfg : Depth.Config) (callables : List String)
    (bound : Nat) (root : Message F) : Prop :=
  ∃ (encoding : FieldEncoding) (modulus : Nat) (encode : F → Nat)
    (measures : Depth.Structural.Plan)
    (exported exported' : Execution.Export F) (groups : List (String × List String))
    (replays : Option (List (Except String (Trace.Replay F)))) (trace bytes : ByteArray)
    (pkg : Package F),
    (∀ x, ((encode x : Nat) : F) = x) ∧ (∀ x, encode x < modulus) ∧
    Trace.depthConfig modulus compiled.inlined.program prepared = .ok (cfg, measures) ∧
    Trace.exportPreparedPlanWithEncoding encoding modulus encode compiled.inlined.program
      compiled.artifact prepared exported groups replays = .ok (exported', trace) ∧
    Ixon.run (Artifact.putPackageWithEncoding encoding exported' modulus encode (some trace)) =
      .ok bytes ∧
    decodeChecked modulus encode bytes = .ok pkg ∧
    callables = pkg.callables.toList ∧ pkg.checkIds bound root.channel = true

theorem ExportedIds.ids {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} {compiled : GenericArtifact specialized}
    {prepared : Physical.Prepared compiled.artifact} {cfg : Depth.Config} {callables : List String}
    {bound : Nat} {root : Message F} (h : ExportedIds compiled prepared cfg callables bound root)
    (certified : Depth.Certified cfg prepared.system) {chips : List (Chip F)}
    (sub : ∀ c ∈ chips, c ∈ (Depth.system cfg prepared.system).chips) :
    (∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) chips root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) chips root,
        callables.idxOf x = callables.idxOf y → x = y) ∧
      ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) chips root, callables.idxOf x < bound := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hcast, hlt, hcfg, exportedOk, written, decoded, rfl, checked⟩ := h
  exact ids_of_export compiled prepared certified hcast hlt hcfg exportedOk written decoded sub
    (checkIds_of_package hcast hlt hcfg exportedOk written decoded checked)

theorem singles_sub {source : Circuit.System F} {id : String → Except String Nat}
    (plan : Grouping.Plan source id) : ∀ c ∈ plan.singles, c ∈ source.chips :=
  fun c hc => List.mem_of_find?_eq_some (plan.certificate.1 c hc)

theorem allChips_sub {source : Circuit.System F} {id : String → Except String Nat}
    (plan : Grouping.Plan source id) : ∀ c ∈ Grouped.allChips plan, c ∈ source.chips := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact List.mem_of_find?_eq_some (plan.certificate.1 c hc)
  · obtain ⟨p, hp, hc⟩ := List.mem_flatMap.mp hc
    exact List.mem_of_find?_eq_some (plan.certificate.2.1 p hp c hc)

open Bridge Grouped

/-- `Compiled.narrow_heap_sound_compact_compiled` with `chanIds` and `chanBound` from the export (`ExportedIds`):
`idOf` numbers the channels by `callables`. -/
theorem narrow_heap_sound_compact_exported {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)}
    {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {S : Periodic.Sharded F} (ok : S.check = true)
    {units : List (Chip F × Option (Unroll F))} (chipsIn : ∀ u ∈ units, u.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, unitOk idOf u = true)
    {wide : List (Circuit F)} {groups : List (List (List Nat))}
    (circuits : S.system.circuits = List.zipWith Circuit.mergeBy wide groups)
    (wideEq : wide = units.map (unitCircuit idOf))
    (lenG : groups.length = wide.length)
    (merged : ∀ j (hw : j < wide.length) (hg : j < groups.length), wide[j].checkMerge groups[j] = true)
    {ν : F → Nat} {tables : List (Periodic.Compact F)}
    (tablesOk : Periodic.checkTables S ν tables = true)
    (mapsIn : ∀ T ∈ tables, T.checkMap S = true → ∀ q ∈ T.parts,
      q.tag :: q.sub :: q.payload ∈ (Depth.system cfg prepared.system).mapClaims.map (encode idOf))
    (capacity : Bridge.capacityRowsU units S.system ≤ 2 ^ 39)
    {bound : Nat} (small : SmallCast F bound) (tags : 3 < bound)
    (codesBound : ∀ e ∈ S.buses, e.2.1 < bound) (labels : Periodic.copyKey S.labelTotal < bound)
    (shadowBound : ∀ k < S.shards.length, ((S.layout k).shadow S.width).bound ≤ bound)
    (lookups : Bridge.capacityLookupsU units S.system < bound) (ids : S.system.instances ≤ bound)
    (parts : (S.system.enumerate S.system.lookupCount).length + 1 +
      (tables.map (·.parts.length)).sum < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0)
    (req : (Part.request S.width (encode idOf root)).checkRequest S.system
      (encode idOf root) = true)
    (req2 : S.checkRequest2 (Part.request S.width (encode idOf root)) = true)
    (callables : List String) (hid : idOf = callables.idxOf)
    (ids : ExportedIds compiled prepared cfg callables bound root)
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {H : Nat → Nat} {main : Nat → Nat → Nat → F} {HT : Nat → Nat} {mainT : Nat → Nat → Nat → F}
    (tall : ∀ k < S.shards.length, ((S.layout k).shadow S.width).places.length ≤ H k)
    (tallT : ∀ t T, tables[t]? = some T → T.rows ≤ HT t)
    (rows : ∀ k < S.shards.length, ∀ p < H k,
      Scalar.Circuit.Satisfies (S.circuit k).constraints (S.assign k (main k) p))
    (balanced : Finsupp.mapDomain trimZeros (S.ledger H main + Periodic.compactLedger S tables HT mainT +
      S.padded2 (Part.request S.width (encode idOf root))) = 0) :
    (Periodic.compactRom S tables mainT).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (Periodic.compactRom S tables mainT)).decode
          specialized.program.enums) heap value result := by
  subst hid
  obtain ⟨chanIds, chanBound⟩ := ids.ids certified (singles_sub plan)
  apply Compiled.narrow_heap_sound_compact_compiled (chanIds := chanIds) (chanBound := chanBound) <;> assumption

/-- `Compiled.mixed_heap_sound_compiled` with `chanIds` and `chanBound` from the export (`ExportedIds`):
`idOf` numbers the channels by `callables`. -/
theorem mixed_heap_sound_exported {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)}
    {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {S : Periodic.Sharded F} (ok : S.check = true)
    {units : List (Chip F × Option (Unroll F))} (chipsIn : ∀ u ∈ units, u.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, unitOk idOf u = true)
    {wide : List (Circuit F)} {groups : List (List (List Nat))}
    (circuits : S.system.circuits = List.zipWith Circuit.mergeBy wide groups)
    (wideEq : wide = units.map (unitCircuit idOf))
    (lenG : groups.length = wide.length)
    (merged : ∀ j (hw : j < wide.length) (hg : j < groups.length), wide[j].checkMerge groups[j] = true)
    {ν : F → Nat} {tables : List (Periodic.Compact F)}
    (tablesOk : Periodic.checkTables S ν tables = true)
    (mapsIn : ∀ T ∈ tables, T.checkMap S = true → ∀ q ∈ T.parts,
      q.tag :: q.sub :: q.payload ∈ (Depth.system cfg prepared.system).mapClaims.map (encode idOf))
    {wideUnits : List (Periodic.WideUnit F)} (wideIn : ∀ u ∈ wideUnits, u.chip ∈ plan.singles)
    (wideOk : Periodic.checkMixed S idOf ν tables wideUnits = true)
    (capacity : Bridge.capacityRowsU units S.system + Periodic.mixedRows wideUnits ≤ 2 ^ 39)
    {bound : Nat} (small : SmallCast F bound) (tags : 3 < bound)
    (codesBound : ∀ e ∈ S.buses, e.2.1 < bound) (labels : Periodic.copyKey S.labelTotal < bound)
    (shadowBound : ∀ k < S.shards.length, ((S.layout k).shadow S.width).bound ≤ bound)
    (lookups : Bridge.capacityLookupsU units S.system + Periodic.mixedLookups wideUnits < bound)
    (ids : S.system.instances ≤ bound)
    (parts : (S.system.enumerate S.system.lookupCount).length + 1 +
      (tables.map (·.parts.length)).sum + Periodic.mixedPartCount wideUnits < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0)
    (req : (Part.request S.width (encode idOf root)).checkRequest S.system
      (encode idOf root) = true)
    (req2 : S.checkRequest2 (Part.request S.width (encode idOf root)) = true)
    (callables : List String) (hid : idOf = callables.idxOf)
    (ids : ExportedIds compiled prepared cfg callables bound root)
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {H : Nat → Nat} {main : Nat → Nat → Nat → F} {HT : Nat → Nat} {mainT : Nat → Nat → Nat → F}
    {mainW : Nat → Nat → Nat → F}
    (tall : ∀ k < S.shards.length, ((S.layout k).shadow S.width).places.length ≤ H k)
    (tallT : ∀ t T, tables[t]? = some T → T.rows ≤ HT t)
    (rows : ∀ k < S.shards.length, ∀ p < H k,
      Scalar.Circuit.Satisfies (S.circuit k).constraints (S.assign k (main k) p))
    (rowsW : ∀ (t : Nat) (u : Periodic.WideUnit F), wideUnits[t]? = some u → ∀ r < u.rows,
      Scalar.Circuit.Satisfies (u.circuit idOf S.buses S.width).constraints (u.assign (mainW t) r))
    (balanced : Finsupp.mapDomain trimZeros (S.ledger H main + Periodic.compactLedger S tables HT mainT +
      Periodic.mixedLedger S idOf wideUnits mainW + S.padded2 (Part.request S.width (encode idOf root))) = 0) :
    (Periodic.compactRom S tables mainT).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (Periodic.compactRom S tables mainT)).decode
          specialized.program.enums) heap value result := by
  subst hid
  obtain ⟨chanIds, chanBound⟩ := ids.ids certified (singles_sub plan)
  apply Compiled.mixed_heap_sound_compiled (chanIds := chanIds) (chanBound := chanBound) <;> assumption

/-- `Compiled.wide_heap_sound_insts_compiled` with `chanIds` and `chanBound` from the export (`ExportedIds`):
`idOf` numbers the channels by `callables`. -/
theorem wide_heap_sound_insts_exported {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)}
    {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {insts : List (Chip F × (Scalar.Circuit.Var → F))}
    (chipsIn : ∀ p ∈ insts, p.1 ∈ plan.singles)
    (instsHold : ∀ p ∈ insts, (Bridge.lower idOf p.1).Holds p.2)
    (capacity : insts.length ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound)
    (small : SmallCast F bound) (tags : 2 < bound) (lookups : Bridge.lookupCount insts < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0)
    (callables : List String) (hid : idOf = callables.idxOf)
    (ids : ExportedIds compiled prepared cfg callables bound root)
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {mainM mainR : Nat → Nat → Scalar.Circuit.Var → F}
    (balanced : (insts.map fun p => (Bridge.lower idOf p.1).rowLedger p.2).sum +
      WideStage.stageLedger (WideStage.mapAirs
        ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap) mainM +
      WideStage.stageLedger (WideStage.romAirs roms) mainR + Finsupp.single (encode idOf root) 1 = 0) :
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result := by
  subst hid
  obtain ⟨chanIds, chanBound⟩ := ids.ids certified (singles_sub plan)
  apply Compiled.wide_heap_sound_insts_compiled (chanIds := chanIds) (chanBound := chanBound) <;> assumption

/-- `Compiled.wide_heap_sound_compiled` with `chanIds` and `chanBound` from the export (`ExportedIds`):
`idOf` numbers the channels by `callables`. -/
theorem wide_heap_sound_exported {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)}
    {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {units : List ((Chip F × Option (Unroll F)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, unitOk idOf u.1 = true)
    (capacity : WideStage.unitCapRows units ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound)
    (small : SmallCast F bound) (tags : 2 < bound) (lookups : WideStage.unitCapLookups units < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0)
    (callables : List String) (hid : idOf = callables.idxOf)
    (ids : ExportedIds compiled prepared cfg callables bound root)
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {mainU mainM mainR : Nat → Nat → Scalar.Circuit.Var → F}
    (holds : WideStage.StageHolds (WideStage.unitAirs idOf units) mainU)
    (balanced : WideStage.stageLedger (WideStage.unitAirs idOf units) mainU +
      WideStage.stageLedger (WideStage.mapAirs
        ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap) mainM +
      WideStage.stageLedger (WideStage.romAirs roms) mainR + Finsupp.single (encode idOf root) 1 = 0) :
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result := by
  subst hid
  obtain ⟨chanIds, chanBound⟩ := ids.ids certified (singles_sub plan)
  apply Compiled.wide_heap_sound_compiled (chanIds := chanIds) (chanBound := chanBound) <;> assumption

/-- `Grouped.grouped_heap_sound_compiled` with `chanIds` and `chanBound` from the export (`ExportedIds`):
`idOf` numbers the channels by `callables`. -/
theorem grouped_heap_sound_exported {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) (idOk : ∀ x n, id x = .ok n → n = idOf x) (names : (circuitNames plan).Nodup)
    {units : List ((Chip F × Option (Unroll F)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles) (unrolled : ∀ u ∈ units, unitOk idOf u.1 = true)
    {groups : List (Grouping.Packed F id × Nat)} (groupsIn : ∀ x ∈ groups, x.1 ∈ plan.groups)
    (capacity : WideStage.unitCapRows units + (groups.map (·.2)).sum ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound) (romWidths : ∀ r ∈ roms, r.1 < bound)
    (small : SmallCast F bound) (tags : 2 < bound)
    (lookups : WideStage.unitCapLookups units + (groups.map fun x => x.2 * groupCost x.1).sum < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0)
    (callables : List String) (hid : idOf = callables.idxOf)
    (ids : ExportedIds compiled prepared cfg callables bound root)
    (enablesOk : ∀ c ∈ allChips plan, checkEnables bound c = true)
    (memWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < bound)
    {mainU mainG mainM mainR : Nat → Nat → Scalar.Circuit.Var → F}
    (holds : WideStage.StageHolds (WideStage.unitAirs idOf units) mainU)
    (holdsG : WideStage.StageHolds (groupAirs groups) mainG)
    (balanced : Finsupp.mapDomain trimZeros
      (WideStage.stageLedger (WideStage.unitAirs idOf units) mainU +
        WideStage.stageLedger (groupAirs groups) mainG +
        WideStage.stageLedger (WideStage.mapAirs
          ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap) mainM +
        WideStage.stageLedger (WideStage.romAirs roms) mainR + Finsupp.single (encode idOf root) 1) = 0) :
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result := by
  subst hid
  obtain ⟨chanIds, chanBound⟩ := ids.ids certified (allChips_sub plan)
  apply Grouped.grouped_heap_sound_compiled (chanIds := chanIds) (chanBound := chanBound) <;> assumption

/-- `Grouped.grouped_heap_sound_shared_compiled` with `chanIds` and `chanBound` from the export (`ExportedIds`):
`idOf` numbers the channels by `callables`. -/
theorem grouped_heap_sound_shared_exported {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) (idOk : ∀ x n, id x = .ok n → n = idOf x) (names : (circuitNames plan).Nodup)
    {units : List ((Chip F × Option (Unroll F)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles) (unrolled : ∀ u ∈ units, unitOk idOf u.1 = true)
    {groups : List (Grouping.Packed F id × Nat)} (groupsIn : ∀ x ∈ groups, x.1 ∈ plan.groups)
    (capacity : WideStage.unitCapRows units + (groups.map (·.2)).sum ≤ 2 ^ 39)
    {shared : List (SharedTable F)}
    (sharedOk : ∀ T ∈ shared, T.check ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) = true)
    {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound) (romWidths : ∀ r ∈ roms, r.1 < bound)
    (small : SmallCast F bound) (tags : 2 < bound)
    (lookups : WideStage.unitCapLookups units + (groups.map fun x => x.2 * groupCost x.1).sum < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0)
    (callables : List String) (hid : idOf = callables.idxOf)
    (ids : ExportedIds compiled prepared cfg callables bound root)
    (enablesOk : ∀ c ∈ allChips plan, checkEnables bound c = true)
    (memWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < bound)
    {mainU mainG mainM mainR : Nat → Nat → Scalar.Circuit.Var → F}
    (holds : WideStage.StageHolds (WideStage.unitAirs idOf units) mainU)
    (holdsG : WideStage.StageHolds (groupAirs groups) mainG)
    (balanced : Finsupp.mapDomain trimZeros
      (WideStage.stageLedger (WideStage.unitAirs idOf units) mainU +
        WideStage.stageLedger (groupAirs groups) mainG +
        WideStage.stageLedger (shared.map SharedTable.air) mainM +
        WideStage.stageLedger (WideStage.romAirs roms) mainR + Finsupp.single (encode idOf root) 1) = 0) :
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result := by
  subst hid
  obtain ⟨chanIds, chanBound⟩ := ids.ids certified (allChips_sub plan)
  apply Grouped.grouped_heap_sound_shared_compiled (chanIds := chanIds) (chanBound := chanBound) <;> assumption

end Exported

section GoldilocksExported

open Aiur.Library.U32.Goldilocks (modulus)
open Bridge Grouped

local notation "GF" => ZMod modulus

/-- `Compiled.narrow_heap_sound_compact_goldilocks_compiled` with `chanIds` and `chanBound` from the export (`ExportedIds`). -/
theorem narrow_heap_sound_compact_goldilocks_exported {source : Generic.Source GF} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue GF)} {result : Value GF} {wires : List (WireValue GF)}
    {output : WireValue GF}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message GF}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {S : Periodic.Sharded GF} (ok : S.check = true)
    {units : List (Chip GF × Option (Unroll GF))} (chipsIn : ∀ u ∈ units, u.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, unitOk idOf u = true)
    {wide : List (Circuit GF)} {groups : List (List (List Nat))}
    (circuits : S.system.circuits = List.zipWith Circuit.mergeBy wide groups)
    (wideEq : wide = units.map (unitCircuit idOf))
    (lenG : groups.length = wide.length)
    (merged : ∀ j (hw : j < wide.length) (hg : j < groups.length), wide[j].checkMerge groups[j] = true)
    {ν : GF → Nat} {tables : List (Periodic.Compact GF)}
    (tablesOk : Periodic.checkTables S ν tables = true)
    (mapsIn : ∀ T ∈ tables, T.checkMap S = true → ∀ q ∈ T.parts,
      q.tag :: q.sub :: q.payload ∈ (Depth.system cfg prepared.system).mapClaims.map (encode idOf))
    (capacity : Bridge.capacityRowsU units S.system ≤ 2 ^ 39)
    {bound : Nat} (hbound : bound ≤ 2 ^ 63) (tags : 3 < bound)
    (codesBound : ∀ e ∈ S.buses, e.2.1 < bound) (labels : Periodic.copyKey S.labelTotal < bound)
    (shadowBound : ∀ k < S.shards.length, ((S.layout k).shadow S.width).bound ≤ bound)
    (lookups : Bridge.capacityLookupsU units S.system < bound) (ids : S.system.instances ≤ bound)
    (parts : (S.system.enumerate S.system.lookupCount).length + 1 +
      (tables.map (·.parts.length)).sum < bound)
    (hbits : cfg.bits ≤ 24)
    (req : (Part.request S.width (encode idOf root)).checkRequest S.system
      (encode idOf root) = true)
    (req2 : S.checkRequest2 (Part.request S.width (encode idOf root)) = true)
    (callables : List String) (hid : idOf = callables.idxOf)
    (ids : ExportedIds compiled prepared cfg callables bound root)
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {H : Nat → Nat} {main : Nat → Nat → Nat → GF} {HT : Nat → Nat} {mainT : Nat → Nat → Nat → GF}
    (tall : ∀ k < S.shards.length, ((S.layout k).shadow S.width).places.length ≤ H k)
    (tallT : ∀ t T, tables[t]? = some T → T.rows ≤ HT t)
    (rows : ∀ k < S.shards.length, ∀ p < H k,
      Scalar.Circuit.Satisfies (S.circuit k).constraints (S.assign k (main k) p))
    (balanced : Finsupp.mapDomain trimZeros (S.ledger H main + Periodic.compactLedger S tables HT mainT +
      S.padded2 (Part.request S.width (encode idOf root))) = 0) :
    (Periodic.compactRom S tables mainT).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (Periodic.compactRom S tables mainT)).decode
          specialized.program.enums) heap value result := by
  subst hid
  obtain ⟨chanIds, chanBound⟩ := ids.ids certified (singles_sub plan)
  apply Compiled.narrow_heap_sound_compact_goldilocks_compiled (chanIds := chanIds) (chanBound := chanBound) <;> assumption

/-- `Compiled.mixed_heap_sound_goldilocks_compiled` with `chanIds` and `chanBound` from the export (`ExportedIds`). -/
theorem mixed_heap_sound_goldilocks_exported {source : Generic.Source GF} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue GF)} {result : Value GF} {wires : List (WireValue GF)}
    {output : WireValue GF}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message GF}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {S : Periodic.Sharded GF} (ok : S.check = true)
    {units : List (Chip GF × Option (Unroll GF))} (chipsIn : ∀ u ∈ units, u.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, unitOk idOf u = true)
    {wide : List (Circuit GF)} {groups : List (List (List Nat))}
    (circuits : S.system.circuits = List.zipWith Circuit.mergeBy wide groups)
    (wideEq : wide = units.map (unitCircuit idOf))
    (lenG : groups.length = wide.length)
    (merged : ∀ j (hw : j < wide.length) (hg : j < groups.length), wide[j].checkMerge groups[j] = true)
    {ν : GF → Nat} {tables : List (Periodic.Compact GF)}
    (tablesOk : Periodic.checkTables S ν tables = true)
    (mapsIn : ∀ T ∈ tables, T.checkMap S = true → ∀ q ∈ T.parts,
      q.tag :: q.sub :: q.payload ∈ (Depth.system cfg prepared.system).mapClaims.map (encode idOf))
    {wideUnits : List (Periodic.WideUnit GF)} (wideIn : ∀ u ∈ wideUnits, u.chip ∈ plan.singles)
    (wideOk : Periodic.checkMixed S idOf ν tables wideUnits = true)
    (capacity : Bridge.capacityRowsU units S.system + Periodic.mixedRows wideUnits ≤ 2 ^ 39)
    {bound : Nat} (hbound : bound ≤ 2 ^ 63) (tags : 3 < bound)
    (codesBound : ∀ e ∈ S.buses, e.2.1 < bound) (labels : Periodic.copyKey S.labelTotal < bound)
    (shadowBound : ∀ k < S.shards.length, ((S.layout k).shadow S.width).bound ≤ bound)
    (lookups : Bridge.capacityLookupsU units S.system + Periodic.mixedLookups wideUnits < bound)
    (ids : S.system.instances ≤ bound)
    (parts : (S.system.enumerate S.system.lookupCount).length + 1 +
      (tables.map (·.parts.length)).sum + Periodic.mixedPartCount wideUnits < bound)
    (hbits : cfg.bits ≤ 24)
    (req : (Part.request S.width (encode idOf root)).checkRequest S.system
      (encode idOf root) = true)
    (req2 : S.checkRequest2 (Part.request S.width (encode idOf root)) = true)
    (callables : List String) (hid : idOf = callables.idxOf)
    (ids : ExportedIds compiled prepared cfg callables bound root)
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {H : Nat → Nat} {main : Nat → Nat → Nat → GF} {HT : Nat → Nat} {mainT : Nat → Nat → Nat → GF}
    {mainW : Nat → Nat → Nat → GF}
    (tall : ∀ k < S.shards.length, ((S.layout k).shadow S.width).places.length ≤ H k)
    (tallT : ∀ t T, tables[t]? = some T → T.rows ≤ HT t)
    (rows : ∀ k < S.shards.length, ∀ p < H k,
      Scalar.Circuit.Satisfies (S.circuit k).constraints (S.assign k (main k) p))
    (rowsW : ∀ (t : Nat) (u : Periodic.WideUnit GF), wideUnits[t]? = some u → ∀ r < u.rows,
      Scalar.Circuit.Satisfies (u.circuit idOf S.buses S.width).constraints (u.assign (mainW t) r))
    (balanced : Finsupp.mapDomain trimZeros (S.ledger H main + Periodic.compactLedger S tables HT mainT +
      Periodic.mixedLedger S idOf wideUnits mainW + S.padded2 (Part.request S.width (encode idOf root))) = 0) :
    (Periodic.compactRom S tables mainT).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (Periodic.compactRom S tables mainT)).decode
          specialized.program.enums) heap value result := by
  subst hid
  obtain ⟨chanIds, chanBound⟩ := ids.ids certified (singles_sub plan)
  apply Compiled.mixed_heap_sound_goldilocks_compiled (chanIds := chanIds) (chanBound := chanBound) <;> assumption

/-- `Compiled.wide_heap_sound_insts_goldilocks_compiled` with `chanIds` and `chanBound` from the export (`ExportedIds`). -/
theorem wide_heap_sound_insts_goldilocks_exported {source : Generic.Source GF} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue GF)} {result : Value GF} {wires : List (WireValue GF)}
    {output : WireValue GF}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message GF}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {insts : List (Chip GF × (Scalar.Circuit.Var → GF))}
    (chipsIn : ∀ p ∈ insts, p.1 ∈ plan.singles)
    (instsHold : ∀ p ∈ insts, (Bridge.lower idOf p.1).Holds p.2)
    (capacity : insts.length ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound)
    (hbound : bound ≤ 2 ^ 63) (tags : 2 < bound) (lookups : Bridge.lookupCount insts < bound)
    (hbits : cfg.bits ≤ 24)
    (callables : List String) (hid : idOf = callables.idxOf)
    (ids : ExportedIds compiled prepared cfg callables bound root)
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {mainM mainR : Nat → Nat → Scalar.Circuit.Var → GF}
    (balanced : (insts.map fun p => (Bridge.lower idOf p.1).rowLedger p.2).sum +
      WideStage.stageLedger (WideStage.mapAirs
        ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap) mainM +
      WideStage.stageLedger (WideStage.romAirs roms) mainR + Finsupp.single (encode idOf root) 1 = 0) :
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result := by
  subst hid
  obtain ⟨chanIds, chanBound⟩ := ids.ids certified (singles_sub plan)
  apply Compiled.wide_heap_sound_insts_goldilocks_compiled (chanIds := chanIds) (chanBound := chanBound) <;> assumption

/-- `Compiled.wide_heap_sound_goldilocks_compiled` with `chanIds` and `chanBound` from the export (`ExportedIds`). -/
theorem wide_heap_sound_goldilocks_exported {source : Generic.Source GF} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue GF)} {result : Value GF} {wires : List (WireValue GF)}
    {output : WireValue GF}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message GF}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {units : List ((Chip GF × Option (Unroll GF)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, unitOk idOf u.1 = true)
    (capacity : WideStage.unitCapRows units ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound)
    (hbound : bound ≤ 2 ^ 63) (tags : 2 < bound) (lookups : WideStage.unitCapLookups units < bound)
    (hbits : cfg.bits ≤ 24)
    (callables : List String) (hid : idOf = callables.idxOf)
    (ids : ExportedIds compiled prepared cfg callables bound root)
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {mainU mainM mainR : Nat → Nat → Scalar.Circuit.Var → GF}
    (holds : WideStage.StageHolds (WideStage.unitAirs idOf units) mainU)
    (balanced : WideStage.stageLedger (WideStage.unitAirs idOf units) mainU +
      WideStage.stageLedger (WideStage.mapAirs
        ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap) mainM +
      WideStage.stageLedger (WideStage.romAirs roms) mainR + Finsupp.single (encode idOf root) 1 = 0) :
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result := by
  subst hid
  obtain ⟨chanIds, chanBound⟩ := ids.ids certified (singles_sub plan)
  apply Compiled.wide_heap_sound_goldilocks_compiled (chanIds := chanIds) (chanBound := chanBound) <;> assumption

/-- `Grouped.grouped_heap_sound_goldilocks_compiled` with `chanIds` and `chanBound` from the export (`ExportedIds`). -/
theorem grouped_heap_sound_goldilocks_exported {source : Generic.Source GF} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue GF)} {result : Value GF} {wires : List (WireValue GF)} {output : WireValue GF}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message GF}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) (idOk : ∀ x n, id x = .ok n → n = idOf x) (names : (circuitNames plan).Nodup)
    {units : List ((Chip GF × Option (Unroll GF)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles) (unrolled : ∀ u ∈ units, unitOk idOf u.1 = true)
    {groups : List (Grouping.Packed GF id × Nat)} (groupsIn : ∀ x ∈ groups, x.1 ∈ plan.groups)
    (capacity : WideStage.unitCapRows units + (groups.map (·.2)).sum ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound) (romWidths : ∀ r ∈ roms, r.1 < bound)
    (hbound : bound ≤ 2 ^ 63) (tags : 2 < bound)
    (lookups : WideStage.unitCapLookups units + (groups.map fun x => x.2 * groupCost x.1).sum < bound)
    (hbits : cfg.bits ≤ 24)
    (callables : List String) (hid : idOf = callables.idxOf)
    (ids : ExportedIds compiled prepared cfg callables bound root)
    (enablesOk : ∀ c ∈ allChips plan, checkEnables bound c = true)
    (memWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < bound)
    {mainU mainG mainM mainR : Nat → Nat → Scalar.Circuit.Var → GF}
    (holds : WideStage.StageHolds (WideStage.unitAirs idOf units) mainU)
    (holdsG : WideStage.StageHolds (groupAirs groups) mainG)
    (balanced : Finsupp.mapDomain trimZeros
      (WideStage.stageLedger (WideStage.unitAirs idOf units) mainU +
        WideStage.stageLedger (groupAirs groups) mainG +
        WideStage.stageLedger (WideStage.mapAirs
          ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap) mainM +
        WideStage.stageLedger (WideStage.romAirs roms) mainR + Finsupp.single (encode idOf root) 1) = 0) :
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result := by
  subst hid
  obtain ⟨chanIds, chanBound⟩ := ids.ids certified (allChips_sub plan)
  apply Grouped.grouped_heap_sound_goldilocks_compiled (chanIds := chanIds) (chanBound := chanBound) <;> assumption

end GoldilocksExported

section BN254Exported

open Bridge Grouped

local notation "BF" => ZMod Aiur.Library.Field.BN254.modulus

local instance : Fact (Nat.Prime Aiur.Library.Field.BN254.modulus) := ⟨Aiur.Library.Field.BN254.modulus_prime⟩

/-- `Grouped.grouped_heap_sound_bn254_compiled` with `chanIds` and `chanBound` from the export (`ExportedIds`). -/
theorem grouped_heap_sound_bn254_exported {source : Generic.Source BF} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue BF)} {result : Value BF} {wires : List (WireValue BF)} {output : WireValue BF}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message BF}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) (idOk : ∀ x n, id x = .ok n → n = idOf x) (names : (circuitNames plan).Nodup)
    {units : List ((Chip BF × Option (Unroll BF)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles) (unrolled : ∀ u ∈ units, unitOk idOf u.1 = true)
    {groups : List (Grouping.Packed BF id × Nat)} (groupsIn : ∀ x ∈ groups, x.1 ∈ plan.groups)
    (capacity : WideStage.unitCapRows units + (groups.map (·.2)).sum ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound) (romWidths : ∀ r ∈ roms, r.1 < bound)
    (hbound : bound ≤ 2 ^ 63) (tags : 2 < bound)
    (lookups : WideStage.unitCapLookups units + (groups.map fun x => x.2 * groupCost x.1).sum < bound)
    (hbits : cfg.bits ≤ 24)
    (callables : List String) (hid : idOf = callables.idxOf)
    (ids : ExportedIds compiled prepared cfg callables bound root)
    (enablesOk : ∀ c ∈ allChips plan, checkEnables bound c = true)
    (memWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < bound)
    {mainU mainG mainM mainR : Nat → Nat → Scalar.Circuit.Var → BF}
    (holds : WideStage.StageHolds (WideStage.unitAirs idOf units) mainU)
    (holdsG : WideStage.StageHolds (groupAirs groups) mainG)
    (balanced : Finsupp.mapDomain trimZeros
      (WideStage.stageLedger (WideStage.unitAirs idOf units) mainU +
        WideStage.stageLedger (groupAirs groups) mainG +
        WideStage.stageLedger (WideStage.mapAirs
          ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap) mainM +
        WideStage.stageLedger (WideStage.romAirs roms) mainR + Finsupp.single (encode idOf root) 1) = 0) :
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result := by
  subst hid
  obtain ⟨chanIds, chanBound⟩ := ids.ids certified (allChips_sub plan)
  apply Grouped.grouped_heap_sound_bn254_compiled (chanIds := chanIds) (chanBound := chanBound) <;> assumption

end BN254Exported

end Aiur.Tiling.Claims
