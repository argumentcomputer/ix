import Aiur.Plonk.StageSound
import Aiur.Tiling.Compiled

/-!
# A satisfying PLONK assignment gives the wide stage's semantics

`plonk_wide_heap_sound` composes `stage_balanced` with
`Compiled.wide_heap_sound_compiled`. The PLONK tables are the stage's
`unitAirs idOf units ++ mapAirs claims mapCap ++ romAirs roms` followed by
the root table (`rootAir`, `stageLedger_root`), table `t`'s
trace is `W.main w t`, and the three traces of the wide theorem are its
slices (`stageLedger_append`, `stageHolds_append_left`).

The hypotheses beyond those of `wide_heap_sound_compiled` (minus its
`holds` and `balanced`) are

* `ok : stageOk airs P poolIdx = true`, decided by the compiled checker;
* `sat`: `w` satisfies the emitted constraint system `emitScs` (with any
  public values and commitment hash: only its gates are used);
* the root table `rootAir k n` is appended to the tables. Its message is
  `[CALL, k, cells…]`: `CALL` and the entry id `k` are circuit constants
  (folded into the root fingerprint's coefficients), and the `n` cells are
  the rest of the root message. `entryId : idOf root.channel = k` and
  `statement`: the cells are `(encode idOf root).drop 2`. The first cells are
  the public wires and the rest the pairing outputs, so `Satisfied` with `pub`
  = the statement limbs gives the public part;
* `good : ChallengeGood γ β …`: the crypto-layer event for the challenge
  `γ = w gamma`, `β = w (poolWire betaRef)`. It is the only probabilistic
  step: it holds except with probability bounded by Fiat–Shamir over a
  binding commitment to the message cells and the Schwartz–Zippel count of
  `Logup.lean`.
-/

namespace Aiur.Plonk

open Aiur.Circuit
open Aiur.Optimized
open Aiur.Tiling
open Aiur.Tiling.Bridge
open Aiur.Tiling.WideStage (Air StageHolds stageLedger)
open Lower (Fr LGate Ref)

theorem stageLedger_append (A B : List (Air Fr)) (main : Nat → Nat → Nat → Fr) :
    stageLedger (A ++ B) main = stageLedger A main + stageLedger B (fun t => main (A.length + t)) := by
  simp only [stageLedger, List.zipIdx_append, List.map_append, List.sum_append, Nat.zero_add]
  congr 1
  rw [List.zipIdx_eq_map_add, List.map_map]
  rfl

theorem stageHolds_append_left {A B : List (Air Fr)} {main : Nat → Nat → Nat → Fr}
    (h : StageHolds (A ++ B) main) : StageHolds A main := by
  intro x hx
  exact h x (by rw [List.zipIdx_append]; exact List.mem_append_left _ hx)

/-- The root table: one row, `n` main cells and the lookup
`push(1, [CALL, k, cells…])`. `CALL` and the entry id `k` are constants of
the circuit, not cells; the cells are the rest of the statement. -/
def rootAir (k : Fr) (n : Nat) : Air Fr :=
  ⟨⟨n, 0, [], [⟨.const 1, .const (CALL : Fr) :: .const k :: (List.range n).map .var⟩]⟩, 1, fun _ _ => 0⟩

theorem stageLedger_root (k : Fr) (n : Nat) (main : Nat → Nat → Nat → Fr) :
    stageLedger [rootAir k n] main =
      Finsupp.single ((CALL : Fr) :: k :: (List.range n).map (main 0 0)) 1 := by
  simp only [stageLedger, List.zipIdx_singleton, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, Air.ledger, rootAir, List.range_one, Tiling.Circuit.rowLedger, Tiling.Lookup.entry,
    Tiling.Lookup.tuple, List.map_map]
  congr 1
  refine congrArg₂ List.cons (by simp [Scalar.Circuit.ArithExpr.denote])
    (congrArg₂ List.cons (by simp [Scalar.Circuit.ArithExpr.denote]) ?_)
  apply List.map_congr_left
  intro v hv
  simp [Function.comp, Scalar.Circuit.ArithExpr.denote, Air.assign, List.mem_range.mp hv]

/-- With the root table last and a good challenge, every table holds and the
ledger of `airs` plus the root message (row 0 of the root table) is zero. -/
theorem stage_balanced {airs : List (Air Fr)} {k : Fr} {n : Nat} {P : Lower.Pool} {poolIdx : Ref → Option Nat}
    (ok : stageOk (airs ++ [rootAir k n]) P poolIdx = true) (W : Wiring (airs ++ [rootAir k n]) P) (w : Nat → Fr)
    (sat : ∀ g ∈ emitGates (airs ++ [rootAir k n]) P W, g.Holds w)
    (good : ChallengeGood (w (W.poolWire Lower.gammaRef)) (w (W.poolWire Lower.betaRef))
      (MsgTuple (airs ++ [rootAir k n]) (W.main w)) (stageLedger (airs ++ [rootAir k n]) (W.main w))) :
    StageHolds airs (W.main w) ∧
      stageLedger airs (W.main w) +
        Finsupp.single ((CALL : Fr) :: k :: (List.range n).map (W.main w airs.length 0)) 1 = 0 := by
  obtain ⟨holds, eval⟩ := stage_sound ok W w sat
  refine ⟨stageHolds_append_left holds, ?_⟩
  have h := good.2 (by rw [eval good.1, init_zero W sat, neg_zero])
  rw [stageLedger_append, stageLedger_root] at h
  simpa using h

/-- The emitted constraint system. -/
def emitScs (airs : List (Air Fr)) (P : Lower.Pool) (W : Wiring airs P) (wires publics : Nat)
    (committed : List Nat) : Scs Fr :=
  { wires, publics, committed, gamma := W.poolWire Lower.gammaRef, gates := emitGates airs P W }

theorem plonk_wide_heap_sound {source : Generic.Source Fr} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue Fr)} {result : Value Fr} {wires : List (WireValue Fr)}
    {output : WireValue Fr}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message Fr}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {units : List ((Chip Fr × Option (Unroll Fr)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, Bridge.unitOk idOf u.1 = true)
    (capacity : WideStage.unitCapRows units ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound)
    (small : SmallCast Fr bound) (tags : 2 < bound) (lookups : WideStage.unitCapLookups units < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : Fr) ≠ 0)
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x < bound)
    (enablesOk : ∀ c ∈ plan.singles, Bridge.checkEnables bound c = true)
    {airs : List (Air Fr)}
    (hairs : airs = WideStage.unitAirs idOf units ++
      WideStage.mapAirs ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap ++
      WideStage.romAirs roms)
    {k : Fr} {n : Nat} {P : Lower.Pool} {poolIdx : Ref → Option Nat}
    (ok : stageOk (airs ++ [rootAir k n]) P poolIdx = true)
    (W : Wiring (airs ++ [rootAir k n]) P)
    {nWires publics : Nat} {committed : List Nat} {w : Nat → Fr} {pub : List Fr} {H : List Fr → Fr}
    (sat : (emitScs (airs ++ [rootAir k n]) P W nWires publics committed).Satisfied w pub H)
    (entryId : (idOf root.channel : Fr) = k)
    (statement : (List.range n).map (W.main w airs.length 0) = (encode idOf root).drop 2)
    (good : ChallengeGood (w (W.poolWire Lower.gammaRef)) (w (W.poolWire Lower.betaRef))
      (MsgTuple (airs ++ [rootAir k n]) (W.main w)) (stageLedger (airs ++ [rootAir k n]) (W.main w))) :
    let mainR := fun t => W.main w ((WideStage.unitAirs idOf units).length +
      (WideStage.mapAirs ((Depth.system cfg prepared.system).mapClaims.map (Bridge.encode idOf)) mapCap).length + t)
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result := by
  intro mainR
  obtain ⟨holds, balanced⟩ := stage_balanced ok W w sat.2.2 good
  have hroot : (CALL : Fr) :: k :: (encode idOf root).drop 2 = encode idOf root := by
    rw [← entryId]; rfl
  rw [statement, hroot] at balanced
  subst hairs
  rw [stageLedger_append, stageLedger_append] at balanced
  refine Compiled.wide_heap_sound_compiled compiled prepared certified plan activated entry signed rooted outside
    entryPlain arguments decoded idOf chipsIn unrolled capacity widths romCaps small tags lookups characteristic
    chanIds chanBound enablesOk (mapCap := mapCap) (mainU := W.main w)
    (mainM := fun t => W.main w ((WideStage.unitAirs idOf units).length + t))
    (stageHolds_append_left (stageHolds_append_left holds)) ?_
  rw [← balanced]
  simp only [List.length_append, mainR, Nat.add_assoc]

end Aiur.Plonk
