import Aiur.Tiling.PeriodicMixed
import Aiur.Tiling.Ixa

/-!
# Wide units from a compiled artifact

`Periodic.WideUnit` is stated over source chips (`Circuit.Chip`). An exporter
reads the written form `Ixa.IChip` instead. `IWideUnit` is the same unit over
the written form: `looks`, `circuit`, `check`, `sigs` and `checkMixedI` read
only `IChip` fields, and for `IChip.ofChip c` they are the source unit's
(`looks_ofUnit`, `circuit_ofUnit`, `checkMixedI_ofUnit`), so the circuits an
exporter writes and the check it runs are those of `mixed_heap_sound`.
-/

namespace Aiur.Tiling.Periodic

open Aiur.Scalar.Circuit (ArithExpr Var)
open Aiur.Tiling.Ixa

variable {F : Type} [Field F] [DecidableEq F]

/-- A wide unit over the written form of its chip. -/
structure IWideUnit (F : Type) where
  chip : IChip F
  keyBase : Nat
  rows : Nat

namespace IWideUnit

variable (idOf : String → Nat) (u : IWideUnit F)

def mainWidth : Nat := u.chip.activation + 2 + u.chip.sends.length

def idCol : Var := u.mainWidth

def keyCol (j : Nat) : Var := u.chip.activation + 2 + j

def receive : WLook F :=
  ⟨(Bridge.CALL : F), (idOf u.chip.name : F), u.chip.inputs.map .var ++ u.chip.output,
    .sub (.const 0) (.var (u.chip.activation + 1)), true, .var u.idCol⟩

def looks : List (WLook F) :=
  u.receive idOf ::
    ((u.chip.sends.zipIdx.map fun a =>
        (⟨(Bridge.CALL : F), (idOf a.1.channel : F), a.1.args ++ a.1.result.map .var, a.1.enable, false,
          .var (u.keyCol a.2)⟩ : WLook F)) ++
      u.chip.memory.map fun m =>
        ⟨(Bridge.ROM : F), (m.values.length : F), m.address :: m.values, m.enable, false, m.address⟩)

def circuit (buses : Buses F) (W : Nat) : Tiling.Circuit F where
  width := u.mainWidth
  fixedWidth := 1
  constraints := (u.chip.lower idOf).constraints
  lookups := (u.looks idOf).flatMap (·.narrowLookups W buses)

def check (S : Sharded F) : Bool := (u.looks idOf).all (·.check S)

def ofUnit (u : WideUnit F) : IWideUnit F := ⟨IChip.ofChip u.chip, u.keyBase, u.rows⟩

variable {idOf}

theorem receive_ofUnit (u : WideUnit F) :
    (ofUnit u).receive idOf = WLook.ofReceive idOf u.chip u.idCol := by
  simp [receive, ofUnit, IChip.ofChip, WLook.ofReceive, WideUnit.idCol, idCol, mainWidth,
    WideUnit.mainWidth, WideUnit.sends]

theorem looks_ofUnit (u : WideUnit F) : (ofUnit u).looks idOf = u.looks idOf := by
  simp only [looks, WideUnit.looks, receive_ofUnit]
  congr 1
  simp only [ofUnit, IChip.ofChip, WideUnit.sends, WLook.ofSend, WLook.ofMemory, keyCol, WideUnit.keyCol,
    List.map_map]
  congr 1
  rw [← List.zipIdx_map_fst 0 (Optimized.Activation.compile u.chip).sends]
  simp [List.zipIdx_map, Function.comp_def]

theorem circuit_ofUnit (u : WideUnit F) (buses : Buses F) (W : Nat) :
    (ofUnit u).circuit idOf buses W = u.circuit idOf buses W := by
  have lower : (ofUnit u).chip.lower idOf = Bridge.lower idOf u.chip := IChip.lower_ofChip idOf u.chip
  simp only [circuit, WideUnit.circuit, looks_ofUnit, lower]
  simp [ofUnit, mainWidth, WideUnit.mainWidth, IChip.ofChip, WideUnit.sends]

theorem check_ofUnit (u : WideUnit F) (S : Sharded F) : (ofUnit u).check idOf S = u.check idOf S := by
  simp only [check, WideUnit.check, looks_ofUnit]

end IWideUnit

/-- `mixedSigs` over written chips. -/
def mixedSigsI (idOf : String → Nat) (W : Nat) (units : List (IWideUnit F)) : List (F × F × F) :=
  units.flatMap fun u =>
    if ((u.receive idOf).chunkExprs W).isEmpty then []
    else (List.range u.rows).map fun r => ((Bridge.CALL : F), (idOf u.chip.name : F), ((u.keyBase + r : Nat) : F))

/-- `checkMixed` over written chips. -/
def checkMixedI (S : Sharded F) (idOf : String → Nat) (ν : F → Nat) (tables : List (Compact F))
    (units : List (IWideUnit F)) : Bool :=
  units.all (·.check idOf S) &&
    fastNodup ((((tables.flatMap (·.parts)).filterMap chunkSig) ++ mixedSigsI idOf S.width units).map
      fun x => (ν x.1, ν x.2.1, ν x.2.2))

theorem checkMixedI_ofUnit (S : Sharded F) (idOf : String → Nat) (ν : F → Nat) (tables : List (Compact F))
    (units : List (WideUnit F)) :
    checkMixedI S idOf ν tables (units.map IWideUnit.ofUnit) = checkMixed S idOf ν tables units := by
  have sigs : mixedSigsI idOf S.width (units.map IWideUnit.ofUnit) = mixedSigs idOf S.width units := by
    simp only [mixedSigsI, mixedSigs, List.flatMap_map, IWideUnit.receive_ofUnit]
    rfl
  simp [checkMixedI, checkMixed, sigs, IWideUnit.check_ofUnit, Function.comp_def]

end Aiur.Tiling.Periodic
