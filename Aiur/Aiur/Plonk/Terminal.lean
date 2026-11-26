import Aiur.Plonk.SharedSound
import Aiur.Plonk.Commit
import Aiur.Plonk.Beta
import Aiur.Plonk.ScsLemmas

/-!
# The exported terminal system and its soundness

`emitScsFull` is the constraint system the exporter writes: the stage gates
(`emitGates`), the `β` gadget (`Beta.gadgetGates`), the commitment to the
message cells (`commitList`) and `γ` at the pool wire `gammaRef`.

`challenge_premise`: in a satisfying assignment, with `c` the committed
values,

* `γ = H c` (BSB22: the challenge is the hash of the commitment),
* `β = B γ` for the fixed function `B = Beta.betaFn steps …` (the gadget is
  checked by `betaOk`; `beta_functional`),
* the ledger and the message tuples are `ledgerOf W c` and `tuplesOf W c`
  (`committed_binds`).

So the challenge event of `plonk_wide_heap_sound` / `plonk_shared_heap_sound`
becomes `ChallengeGood (H c) (B (H c)) (tuplesOf W c) (ledgerOf W c)`: a
property of `γ = H c` alone, for values `c` fixed by the commitment before `H`
is evaluated. `plonk_terminal_sound` and `plonk_shared_terminal_sound` take
exactly that as their challenge hypothesis.

`exportGate` is the per-gate form the file carries (`GGate.ofCoeffs`, then
`GGate.nz` sets unselected operand coefficients to `1`, since gnark's
`Mul(x, 0)` is a constant and would change the constraint);
`exportGate_holds`: the exported gate holds iff the emitted gate does.
-/

namespace Aiur.Plonk

open Aiur.Circuit
open Aiur.Optimized
open Aiur.Tiling
open Aiur.Tiling.Bridge
open Aiur.Tiling.WideStage (Air stageLedger)
open Aiur.Tiling.Grouped (SharedTable allChips circuitNames)
open Lower (Ref)

section Generic

variable {F : Type} [Field F] [DecidableEq F]

omit [DecidableEq F] in
def GGate.nz (g : GGate F) : GGate F :=
  { g with
    α := if g.sL || g.sM then g.α else 1
    β := if g.sR || g.sM then g.β else 1
    ω := if g.sO then g.ω else 1 }

omit [DecidableEq F] in
theorem GGate.nz_toGate (g : GGate F) : g.nz.toGate = g.toGate := by
  cases g with
  | mk a b c α β ω sL sR sO sM qC =>
      cases sL <;> cases sR <;> cases sO <;> cases sM <;> simp [GGate.nz, GGate.toGate, sel]

def exportGate (g : Gate F) : Option (GGate F) :=
  (GGate.ofCoeffs g.a g.b g.c g.qL g.qR g.qO g.qM g.qC).map GGate.nz

theorem exportGate_holds {g : Gate F} {gg : GGate F} (h : exportGate g = some gg) (w : Nat → F) :
    gg.toGate.Holds w ↔ g.Holds w := by
  unfold exportGate at h
  obtain ⟨g0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [GGate.nz_toGate, GGate.ofCoeffs_holds h0]
  rfl

end Generic

section Prime

variable {p : Nat} [Fact (Nat.Prime p)]

def emitScsFull (airs : List (Air (ZMod p))) (P : Lower.Pool (ZMod p)) (W : Wiring airs P)
    (steps : List (Beta.Step (ZMod p))) (wires publics : Nat) : Scs (ZMod p) :=
  { wires, publics, committed := commitList airs W.cellWire, gamma := W.poolWire Lower.gammaRef,
    gates := emitGates airs P W ++ Beta.gadgetGates steps }

/-- The function the checked gadget computes from `γ`. -/
def Wiring.betaB {airs : List (Air (ZMod p))} {P : Lower.Pool (ZMod p)} (W : Wiring airs P)
    (steps : List (Beta.Step (ZMod p))) : ZMod p → ZMod p :=
  Beta.betaFn steps (W.poolWire Lower.gammaRef) (W.poolWire Lower.betaRef)

theorem challenge_premise {airs : List (Air (ZMod p))} {P : Lower.Pool (ZMod p)} (W : Wiring airs P)
    {steps : List (Beta.Step (ZMod p))}
    (bok : Beta.betaOk steps (W.poolWire Lower.gammaRef) (W.poolWire Lower.betaRef) = true)
    {wires publics : Nat} {w : Nat → ZMod p} {pub : List (ZMod p)} {H : List (ZMod p) → ZMod p}
    (sat : (emitScsFull airs P W steps wires publics).Satisfied w pub H) :
    w (W.poolWire Lower.gammaRef) = H ((commitList airs W.cellWire).map w) ∧
      w (W.poolWire Lower.betaRef) = W.betaB steps (H ((commitList airs W.cellWire).map w)) ∧
      stageLedger airs (W.main w) = ledgerOf W ((commitList airs W.cellWire).map w) ∧
      MsgTuple airs (W.main w) = tuplesOf W ((commitList airs W.cellWire).map w) := by
  have hγ : w (W.poolWire Lower.gammaRef) = H ((commitList airs W.cellWire).map w) := sat.2.1
  have hβ := Beta.beta_functional w bok fun g hg => sat.2.2 g (List.mem_append_right _ hg)
  obtain ⟨hl, ht⟩ := ledgerOf_spec W w
  exact ⟨hγ, by rw [hβ, hγ]; rfl, hl.symm, ht.symm⟩

theorem plonk_terminal_sound {source : Generic.Source (ZMod p)} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue (ZMod p))} {result : Value (ZMod p)} {wires : List (WireValue (ZMod p))}
    {output : WireValue (ZMod p)}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message (ZMod p)}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {units : List ((Chip (ZMod p) × Option (Unroll (ZMod p))) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, Bridge.unitOk idOf u.1 = true)
    (capacity : WideStage.unitCapRows units ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound)
    (small : SmallCast (ZMod p) bound) (tags : 2 < bound) (lookups : WideStage.unitCapLookups units < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : ZMod p) ≠ 0)
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x < bound)
    (enablesOk : ∀ c ∈ plan.singles, Bridge.checkEnables bound c = true)
    {airs : List (Air (ZMod p))}
    (hairs : airs = WideStage.unitAirs idOf units ++
      WideStage.mapAirs ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap ++
      WideStage.romAirs roms)
    {k : ZMod p} {n : Nat} {P : Lower.Pool (ZMod p)} {poolIdx : Ref → Option Nat}
    (ok : stageOk (airs ++ [rootAir k n]) P poolIdx = true)
    (W : Wiring (airs ++ [rootAir k n]) P) {steps : List (Beta.Step (ZMod p))}
    (bok : Beta.betaOk steps (W.poolWire Lower.gammaRef) (W.poolWire Lower.betaRef) = true)
    {nWires publics : Nat} {w : Nat → ZMod p} {pub : List (ZMod p)} {H : List (ZMod p) → ZMod p}
    (sat : (emitScsFull (airs ++ [rootAir k n]) P W steps nWires publics).Satisfied w pub H)
    (entryId : (idOf root.channel : ZMod p) = k)
    (statement : (List.range n).map (W.main w airs.length 0) = (encode idOf root).drop 2)
    (good : let c := (commitList (airs ++ [rootAir k n]) W.cellWire).map w
      ChallengeGood (H c) (W.betaB steps (H c)) (tuplesOf W c) (ledgerOf W c)) :
    let mainR := fun t => W.main w ((WideStage.unitAirs idOf units).length +
      (WideStage.mapAirs ((Depth.system cfg prepared.system).mapClaims.map (Bridge.encode idOf)) mapCap).length + t)
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result := by
  obtain ⟨hγ, hβ, hl, ht⟩ := challenge_premise W bok sat
  have sat' : (emitScs (airs ++ [rootAir k n]) P W nWires publics (commitList (airs ++ [rootAir k n]) W.cellWire)).Satisfied
      w pub H :=
    ⟨sat.1, sat.2.1, fun g hg => sat.2.2 g (List.mem_append_left _ hg)⟩
  simp only at good
  have hβ' : W.betaB steps (w (W.poolWire Lower.gammaRef)) = w (W.poolWire Lower.betaRef) := by
    rw [hγ]; exact hβ.symm
  rw [← hγ, ← hl, ← ht, hβ'] at good
  exact plonk_wide_heap_sound compiled prepared certified plan activated entry signed rooted outside entryPlain
    arguments decoded idOf chipsIn unrolled capacity widths romCaps small tags lookups characteristic chanIds
    chanBound enablesOk hairs ok W sat' entryId statement good

/-- `plonk_shared_heap_sound` composed with `challenge_premise` over the full
exported constraint system `emitScsFull` (including the in-circuit `β` gadget). -/
theorem plonk_shared_terminal_sound {source : Generic.Source (ZMod p)} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue (ZMod p))} {result : Value (ZMod p)} {wires : List (WireValue (ZMod p))}
    {output : WireValue (ZMod p)}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message (ZMod p)}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) (idOk : ∀ x n, id x = .ok n → n = idOf x) (names : (circuitNames plan).Nodup)
    {units : List ((Chip (ZMod p) × Option (Unroll (ZMod p))) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, Bridge.unitOk idOf u.1 = true)
    (capacity : WideStage.unitCapRows units ≤ 2 ^ 39)
    {shared : List (SharedTable (ZMod p))}
    (sharedOk : ∀ T ∈ shared,
      T.check ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) = true)
    {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound) (romWidths : ∀ r ∈ roms, r.1 < bound)
    (small : SmallCast (ZMod p) bound) (tags : 2 < bound) (lookups : WideStage.unitCapLookups units < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : ZMod p) ≠ 0)
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x < bound)
    (enablesOk : ∀ c ∈ allChips plan, Bridge.checkEnables bound c = true)
    (memWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < bound)
    {airs : List (Air (ZMod p))}
    (hairs : airs = WideStage.unitAirs idOf units ++ shared.map SharedTable.air ++ WideStage.romAirs roms)
    {k : ZMod p} {n : Nat} {P : Lower.Pool (ZMod p)} {poolIdx : Ref → Option Nat}
    (ok : stageOk (airs ++ [rootAir k n]) P poolIdx = true)
    (W : Wiring (airs ++ [rootAir k n]) P) {steps : List (Beta.Step (ZMod p))}
    (bok : Beta.betaOk steps (W.poolWire Lower.gammaRef) (W.poolWire Lower.betaRef) = true)
    {nWires publics : Nat} {w : Nat → ZMod p} {pub : List (ZMod p)} {H : List (ZMod p) → ZMod p}
    (sat : (emitScsFull (airs ++ [rootAir k n]) P W steps nWires publics).Satisfied w pub H)
    (entryId : (idOf root.channel : ZMod p) = k)
    (statement : (List.range n).map (W.main w airs.length 0) = (encode idOf root).drop 2)
    (good : let c := (commitList (airs ++ [rootAir k n]) W.cellWire).map w
      ChallengeGood (H c) (W.betaB steps (H c)) (tuplesOf W c) (ledgerOf W c)) :
    let mainR := fun t => W.main w ((WideStage.unitAirs idOf units).length + shared.length + t)
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result := by
  obtain ⟨hγ, hβ, hl, ht⟩ := challenge_premise W bok sat
  have sat' : (emitScs (airs ++ [rootAir k n]) P W nWires publics (commitList (airs ++ [rootAir k n]) W.cellWire)).Satisfied
      w pub H :=
    ⟨sat.1, sat.2.1, fun g hg => sat.2.2 g (List.mem_append_left _ hg)⟩
  simp only at good
  have hβ' : W.betaB steps (w (W.poolWire Lower.gammaRef)) = w (W.poolWire Lower.betaRef) := by
    rw [hγ]; exact hβ.symm
  rw [← hγ, ← hl, ← ht, hβ'] at good
  exact plonk_shared_heap_sound compiled prepared certified plan activated entry signed rooted outside entryPlain
    arguments decoded idOf idOk names chipsIn unrolled capacity sharedOk widths romCaps romWidths small tags lookups
    characteristic chanIds chanBound enablesOk memWidth hairs ok W sat' entryId statement good

end Prime

end Aiur.Plonk
