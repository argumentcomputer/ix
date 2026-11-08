import Aiur.Optimized.Depth.Soundness
import Aiur.Optimized.Physical

/-!
# Memo-checker soundness over the depth pass of the physical circuits

`Physical.Prepared.native_heap_sound` starts from a finite derivation. Over the
certified depth pass of the same physical (ungrouped) circuits, the memo
checker's acceptance and a row bound supply it: no acyclicity hypothesis is
left. `Depth/Grouped.lean` does the same over the grouped, activated plan.
-/

namespace Aiur.Optimized.Physical

open Circuit

variable {F : Type} [Field F] [DecidableEq F]

/-- Source evaluation from weighted rows accepted over `Depth.system cfg prepared.system`.
`rooted` relates the public claim to the depth system's root: for a non-recursive
entry they are equal. Over Goldilocks, `Depth.goldilocks_characteristic` discharges
`characteristic` for `N = 2^39` and `cfg.bits = 24`. -/
theorem Prepared.depth_native_heap_sound {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system)
    {name : String} (entry : name ∈ entries) {rom : WidthROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Message F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    {rows : List (WeightedRow F)} {N : Nat} (bound : rows.length ≤ N)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ N * 2 ^ cfg.bits → (n : F) ≠ 0)
    (checked : (Depth.system cfg prepared.system).checkMemo (Erasure.rawROM rom) root rows = .ok ())
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result) :
    ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
      Represents ((Erasure.typedROM compiled.system rom).decode specialized.program.enums)
        heap value result :=
  prepared.native_heap_sound compiled entry valid signed
    (rooted ▸ Depth.checkMemo_sound certified bound characteristic checked outside) arguments decoded

end Aiur.Optimized.Physical
