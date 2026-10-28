import Ix.Cert.BlockLayout
import Ix.Cert.BlockStart
import Ix.CompileCert.EmissionDispatch

/-! # Every block the compiler returns is on the wire

`BlockLayout.BlocksWire`: every block `runBlock` returns is wire-valid. A block compiles as
a lone constant's `compileConstantInfo` or a mutual block's `compileMutualBlock`, from the
empty block state (`BlockRecords.runBlock_records`), whose tables are on the wire
(`BlockStart.wire_empty`). Both compiles return a block that decodes exactly
(`EmissionDispatch.constant_codec`, `EmissionDispatch.mutualBlock_codec`):

* the preseed puts the reference and universe tables on the wire
  (`EmissionWire.seeded_valid`), and every payload emitter keeps them there
  (`EmissionWire.Safe`);
* the builder makes a wire-valid constant from wire tables and a payload whose header
  fields fit the wire (`buildConstantWithSharing_wireWF_headers`): the canonical sharing's
  table and roots are in the wire domain (`Tiered.canonicalSharingTiered_format`), and the
  emitters check the headers' counts (`checkedTableCount`). -/

namespace Ix.Cert.BlockWire

open Ix.CompileM

/-- **Every block `runBlock` returns is wire-valid.** -/
theorem blocksWire : BlockLayout.BlocksWire := by
  intro cenv all lo r c h
  obtain ⟨const, -, rest⟩ := BlockRecords.runBlock_records h
  rcases rest with ⟨r', s₂, run, same⟩ | ⟨cs, out, s₄, run, same⟩
  · simp only [BlockRecords.recordsOf, Prod.mk.injEq] at same
    rw [same.1]
    exact (Ix.CompileCert.EmissionDispatch.constant_codec _ rfl const BlockStart.wire_empty run).1
  · simp only [BlockRecords.recordsOf, Prod.mk.injEq] at same
    rw [same.1]
    exact (Ix.CompileCert.EmissionDispatch.mutualBlock_codec _ rfl _ BlockStart.wire_empty run).1

/-- info: 'Ix.Cert.BlockWire.blocksWire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms blocksWire

end Ix.Cert.BlockWire
