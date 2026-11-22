import Aiur.Tiling.PeriodicUnits

/-!
# Wide (non-tiled) proving stages

A wide stage proves the lowered chips directly, one STARK table per unit
(`Bridge.unitCircuit`: `Bridge.lower` of a chip, possibly unrolled), beside
two kinds of fixed tables:

* map tables (`mapCircuit L`), one per encoded claim length `L`: fixed
  column `sel` (1 on a claim row, 0 on padding) and the `L` cells of the
  encoded claim `encode idOf mc`; main column `mult`; one lookup
  `push(-(sel·mult), cells)`.
* ROM tables (`romCircuit w`), one per word count `w` with capacity `cap`:
  main columns `mult` and the `w` words, fixed column `addr` (the row index);
  one lookup `push(-mult, [ROM, w, addr, words…])`.

An `Air` is a circuit with a row count and its fixed matrix; row `i` of a
trace `main` is assigned `main i v` on main columns and the fixed value on
fixed columns (`Air.assign`). The ROM is the one the ROM traces hold
(`wideRom`); it is valid when the word counts are distinct and every row
index is a distinct field element.

`wide_heap_sound_insts` takes any list of lowered single-chip rows;
`wide_heap_sound` instantiates it with the rows of the unit tables. Both go
through `Bridge.Wide.checkMemo`, which only handles `plan.singles`: grouped
chips are out of scope, so a wide stage uses a plan whose proved chips are
all singles.
-/

namespace Aiur.Tiling.WideStage

open Aiur.Circuit
open Aiur.Optimized
open Bridge
open Scalar.Circuit (ArithExpr)

variable {F : Type} [Field F]

/-! ## Tables with fixed columns -/

/-- A circuit with its row count and fixed matrix (`fixed row column`). -/
structure Air (F : Type) where
  circuit : Tiling.Circuit F
  rows : Nat
  fixed : Nat → Nat → F

/-- Row `i` of trace `main`: main columns from the trace, fixed columns
`width + k` from the fixed matrix. -/
def Air.assign (a : Air F) (main : Nat → Scalar.Circuit.Var → F) (i : Nat) : Scalar.Circuit.Var → F :=
  fun v => if v < a.circuit.width then main i v else a.fixed i (v - a.circuit.width)

omit [Field F] in
theorem Air.assign_apply (a : Air F) (main : Nat → Scalar.Circuit.Var → F) (i v : Nat) :
    a.assign main i v = if v < a.circuit.width then main i v else a.fixed i (v - a.circuit.width) := rfl

def Air.Holds (a : Air F) (main : Nat → Scalar.Circuit.Var → F) : Prop :=
  ∀ i < a.rows, a.circuit.Holds (a.assign main i)

noncomputable def Air.ledger (a : Air F) (main : Nat → Scalar.Circuit.Var → F) : Ledger F :=
  ((List.range a.rows).map fun i => a.circuit.rowLedger (a.assign main i)).sum

/-- Table `f` of the list gets trace `main f`. -/
def StageHolds (airs : List (Air F)) (main : Nat → Nat → Scalar.Circuit.Var → F) : Prop :=
  ∀ x ∈ airs.zipIdx, x.1.Holds (main x.2)

noncomputable def stageLedger (airs : List (Air F)) (main : Nat → Nat → Scalar.Circuit.Var → F) : Ledger F :=
  (airs.zipIdx.map fun x => x.1.ledger (main x.2)).sum

/-! ## Map tables -/

/-- The map table circuit for claims of length `L`: main `mult` (var 0),
fixed `sel` (var 1) and cells (vars `2 … L + 1`). -/
def mapCircuit (L : Nat) : Tiling.Circuit F where
  width := 1
  fixedWidth := L + 1
  constraints := []
  lookups := [⟨.sub (.const 0) (.mul (.var 1) (.var 0)), (List.range L).map fun k => .var (k + 2)⟩]

/-- Fixed matrix of a map table over `claims`: column 0 is `sel`, column
`k + 1` is cell `k`; rows past the claims are padding with `sel = 0`. -/
def mapFixed (claims : List (List F)) (i : Nat) : Nat → F
  | 0 => if i < claims.length then 1 else 0
  | k + 1 => (claims.getD i []).getD k 0

def mapAir (L : Nat) (claims : List (List F)) (rows : Nat) : Air F :=
  ⟨mapCircuit L, rows, mapFixed claims⟩

/-- The claims of length `L`. -/
def claimsOf (claims : List (List F)) (L : Nat) : List (List F) := claims.filter (·.length == L)

/-- The claim lengths, without repeats. -/
def mapLengths (claims : List (List F)) : List Nat := (claims.map List.length).dedup

/-- One map table per claim length; `cap L` is the row count (at least the
number of claims of length `L` for all of them to be provable). -/
def mapAirs (claims : List (List F)) (cap : Nat → Nat) : List (Air F) :=
  (mapLengths claims).map fun L => mapAir L (claimsOf claims L) (cap L)

theorem map_getD_range (t : List F) : (List.range t.length).map (fun k => t.getD k 0) = t := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp [List.getElem?_eq_getElem h2]

theorem mapAir_rowLedger (L : Nat) (claims : List (List F)) (rows : Nat)
    (main : Nat → Scalar.Circuit.Var → F) (i : Nat) :
    (mapAir L claims rows).circuit.rowLedger ((mapAir L claims rows).assign main i) =
      Finsupp.single ((List.range L).map fun k => (claims.getD i []).getD k 0)
        (-(mapFixed claims i 0 * main i 0)) := by
  simp only [Circuit.rowLedger, Lookup.entry, Lookup.tuple, mapAir, mapCircuit]
  simp [Air.assign_apply, Scalar.Circuit.ArithExpr.denote, List.map_map, Function.comp_def, mapFixed]

/-- A nonzero entry of a map table row is one of its claims of length `L`. -/
theorem mapAir_support [DecidableEq F] {L : Nat} {claims : List (List F)} (len : ∀ t ∈ claims, t.length = L)
    {rows : Nat} (main : Nat → Scalar.Circuit.Var → F) (i : Nat) (t : List F)
    (h : (mapAir L claims rows).circuit.rowLedger ((mapAir L claims rows).assign main i) t ≠ 0) :
    t ∈ claims := by
  rw [mapAir_rowLedger, Finsupp.single_apply] at h
  split at h
  · rename_i e
    by_cases hi : i < claims.length
    · have mem := List.getElem_mem hi
      rw [← e, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, ← len _ mem,
        map_getD_range]
      exact mem
    · simp [mapFixed, hi] at h
  · exact absurd rfl h

omit [Field F] in
theorem claimsOf_length (claims : List (List F)) (L : Nat) : ∀ t ∈ claimsOf claims L, t.length = L := by
  intro t ht
  simpa [claimsOf] using (List.mem_filter.mp ht).2

omit [Field F] in
theorem claimsOf_sub (claims : List (List F)) (L : Nat) : ∀ t ∈ claimsOf claims L, t ∈ claims :=
  fun _ ht => (List.mem_filter.mp ht).1

/-! ## ROM tables -/

/-- The ROM table circuit for `w` words: main `mult` (var 0) and words
(vars `1 … w`), fixed `addr` (var `w + 1`). -/
def romCircuit (w : Nat) : Tiling.Circuit F where
  width := w + 1
  fixedWidth := 1
  constraints := []
  lookups := [⟨.sub (.const 0) (.var 0), .const (Bridge.ROM : F) :: .const (w : F) :: .var (w + 1) ::
    (List.range w).map fun k => .var (k + 1)⟩]

def romAir (w cap : Nat) : Air F := ⟨romCircuit w, cap, fun i _ => (i : F)⟩

/-- One ROM table per `(words, capacity)`. -/
def romAirs (roms : List (Nat × Nat)) : List (Air F) := roms.map fun r => romAir r.1 r.2

/-- The words of row `i` of a ROM trace with `w` words. -/
def romWords (w : Nat) (main : Nat → Scalar.Circuit.Var → F) (i : Nat) : List F :=
  (List.range w).map fun k => main i (k + 1)

/-- The ROM the ROM traces hold: for table `j` with `(w, cap)`, every
address `i < cap` with the words of row `i`. -/
def wideRom (roms : List (Nat × Nat)) (main : Nat → Nat → Scalar.Circuit.Var → F) : WidthROM F :=
  ⟨roms.zipIdx.flatMap fun x => (List.range x.1.2).map fun (i : Nat) => ((i : F), romWords x.1.1 (main x.2) i)⟩

theorem romAir_rowLedger (w cap : Nat) (main : Nat → Scalar.Circuit.Var → F) (i : Nat) :
    (romAir (F := F) w cap).circuit.rowLedger ((romAir w cap).assign main i) =
      Finsupp.single (encodeRom ((i : F), Erasure.pack (romWords w main i))) (-(main i 0)) := by
  simp only [Circuit.rowLedger, Lookup.entry, Lookup.tuple, romAir, romCircuit]
  have words : ((List.range w).map fun x => if x < w then main i (x + 1) else (i : F)) =
      (List.range w).map fun k => main i (k + 1) :=
    List.map_congr_left fun k hk => by simp [List.mem_range.mp hk]
  simp [Air.assign_apply, Scalar.Circuit.ArithExpr.denote, List.map_map, Function.comp_def, encodeRom,
    romWords, words]


/-! ## Ledger support -/

section Support

variable [DecidableEq F]

theorem exists_of_sum_ne {α : Type} {l : List α} {g : α → Ledger F} {u : List F}
    (h : (l.map g).sum u ≠ 0) : ∃ x ∈ l, g x u ≠ 0 := by
  by_contra none
  push Not at none
  apply h
  rw [Tiling.System.ledger_list_sum, List.map_map]
  exact List.sum_eq_zero fun y hy => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact none x hx

theorem stage_support {airs : List (Air F)} {main : Nat → Nat → Scalar.Circuit.Var → F} {P : List F → Prop}
    (h : ∀ x ∈ airs.zipIdx, ∀ i < x.1.rows, ∀ t,
      x.1.circuit.rowLedger (x.1.assign (main x.2) i) t ≠ 0 → P t)
    (t : List F) (ht : stageLedger airs main t ≠ 0) : P t := by
  obtain ⟨x, hx, hne⟩ := exists_of_sum_ne ht
  obtain ⟨i, hi, hne⟩ := exists_of_sum_ne hne
  exact h x hx i (List.mem_range.mp hi) t hne

/-- A nonzero entry of the map tables is a claim. -/
theorem mapAirs_support (claims : List (List F)) (cap : Nat → Nat)
    (main : Nat → Nat → Scalar.Circuit.Var → F) (t : List F)
    (ht : stageLedger (mapAirs claims cap) main t ≠ 0) : t ∈ claims := by
  refine stage_support (P := (· ∈ claims)) ?_ t ht
  intro x hx i _ u hu
  have mem := List.fst_mem_of_mem_zipIdx hx
  simp only [mapAirs, List.mem_map] at mem
  obtain ⟨L, _, e⟩ := mem
  rw [← e] at hu
  exact claimsOf_sub claims L _ (mapAir_support (claimsOf_length claims L) _ i u hu)

omit [Field F] [DecidableEq F] in
theorem romWords_length (w : Nat) (main : Nat → Scalar.Circuit.Var → F) (i : Nat) :
    (romWords w main i).length = w := by
  simp [romWords]

/-- A nonzero entry of the ROM tables is the encoding of an entry of the
ROM they hold. -/
theorem romAirs_support (roms : List (Nat × Nat)) (main : Nat → Nat → Scalar.Circuit.Var → F)
    (t : List F) (ht : stageLedger (romAirs roms) main t ≠ 0) :
    ∃ e ∈ (Erasure.rawROM (wideRom roms main)).entries, t = encodeRom e := by
  refine stage_support (P := fun t => ∃ e ∈ (Erasure.rawROM (wideRom roms main)).entries, t = encodeRom e)
    ?_ t ht
  intro x hx i hi u hu
  rw [romAirs, ← List.map_zipIdx] at hx
  obtain ⟨⟨r, j⟩, hr, rfl⟩ := List.mem_map.mp hx
  change (romAir r.1 r.2).circuit.rowLedger ((romAir r.1 r.2).assign (main j) i) u ≠ 0 at hu
  simp only [romAir_rowLedger, Finsupp.single_apply] at hu
  split at hu
  · rename_i eq
    refine ⟨((i : F), Erasure.pack (romWords r.1 (main j) i)), ?_, eq.symm⟩
    apply Erasure.mem_rawROM.mpr
    simp only [wideRom, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨(r, j), hr, i, hi, rfl⟩
  · exact absurd rfl hu

omit [Field F] [DecidableEq F] in
theorem rawROM_packed (rom : WidthROM F) :
    ∀ e ∈ (Erasure.rawROM rom).entries, e.2.type = .tuple (List.replicate e.2.words.length .field) := by
  intro e he
  simp only [Erasure.rawROM, List.mem_map] at he
  obtain ⟨_, _, rfl⟩ := he
  simp [Erasure.pack]

end Support

/-- The ROM is valid when the word counts are distinct and the addresses of
each table are distinct field elements. -/
theorem wideRom_valid {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    (addrs : ∀ r ∈ roms, ∀ i < r.2, ∀ i' < r.2, (i : F) = i' → i = i')
    (main : Nat → Nat → Scalar.Circuit.Var → F) : (wideRom roms main).Valid := by
  rintro a ha b hb addr len
  simp only [wideRom, List.mem_flatMap, List.mem_map, List.mem_range] at ha hb
  obtain ⟨⟨r, j⟩, hr, i, hi, rfl⟩ := ha
  obtain ⟨⟨r', j'⟩, hr', i', hi', rfl⟩ := hb
  simp only at len addr
  rw [romWords_length, romWords_length] at len
  simp only [List.mk_mem_zipIdx_iff_getElem?] at hr hr'
  have hj : j < roms.length := (List.getElem?_eq_some_iff.mp hr).1
  have hj' : j' < roms.length := (List.getElem?_eq_some_iff.mp hr').1
  have er : roms[j] = r := (List.getElem?_eq_some_iff.mp hr).2
  have er' : roms[j'] = r' := (List.getElem?_eq_some_iff.mp hr').2
  have same : j = j' := by
    have e : (roms.map Prod.fst)[j]'(by simpa using hj) = (roms.map Prod.fst)[j']'(by simpa using hj') := by
      simp [er, er', len]
    exact (List.Nodup.getElem_inj_iff widths).mp e
  subst same
  have rr : r = r' := er.symm.trans er'
  subst rr
  have := addrs r (List.mem_of_getElem? hr) i hi i' hi' addr
  subst this
  rfl


/-! ## Unit tables -/

section Units

variable [DecidableEq F]

/-- The table of a unit with its row count; it has no fixed columns. -/
def unitAir (idOf : String → Nat) (u : (Chip F × Option (Unroll F)) × Nat) : Air F :=
  ⟨unitCircuit idOf u.1, u.2, fun _ _ => 0⟩

def unitAirs (idOf : String → Nat) (units : List ((Chip F × Option (Unroll F)) × Nat)) : List (Air F) :=
  units.map (unitAir idOf)

/-- The chip rows of all rows of the unit tables. -/
def unitInsts (idOf : String → Nat) (units : List ((Chip F × Option (Unroll F)) × Nat))
    (main : Nat → Nat → Scalar.Circuit.Var → F) : List (Chip F × (Scalar.Circuit.Var → F)) :=
  units.zipIdx.flatMap fun x => (List.range x.1.2).flatMap fun i =>
    (unitRows idOf x.1.1 ((unitAir idOf x.1).assign (main x.2) i)).map fun r => (x.1.1.1, r)

def unitCapRows (units : List ((Chip F × Option (Unroll F)) × Nat)) : Nat :=
  (units.map fun u => u.2 * unitBodies u.1).sum

def unitCapLookups (units : List ((Chip F × Option (Unroll F)) × Nat)) : Nat :=
  (units.map fun u => u.2 * unitBodies u.1 * (u.1.1.sends.length + u.1.1.memory.length)).sum + 1

theorem unitAirs_ledger {idOf : String → Nat} {units : List ((Chip F × Option (Unroll F)) × Nat)}
    (ok : ∀ u ∈ units, unitOk idOf u.1 = true) (main : Nat → Nat → Scalar.Circuit.Var → F) :
    stageLedger (unitAirs idOf units) main =
      ((unitInsts idOf units main).map fun p => (Bridge.lower idOf p.1).rowLedger p.2).sum := by
  simp only [stageLedger, unitAirs, ← List.map_zipIdx, List.map_map, unitInsts, System.sum_map_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro x hx
  simp only [Function.comp_def, Prod.map, id, Air.ledger]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  exact unit_ledger (ok _ (List.fst_mem_of_mem_zipIdx hx)) _

theorem mem_unitInsts {idOf : String → Nat} {units : List ((Chip F × Option (Unroll F)) × Nat)}
    {main : Nat → Nat → Scalar.Circuit.Var → F} {p : Chip F × (Scalar.Circuit.Var → F)}
    (hp : p ∈ unitInsts idOf units main) :
    ∃ x ∈ units.zipIdx, ∃ i < x.1.2, p.1 = x.1.1.1 ∧
      p.2 ∈ unitRows idOf x.1.1 ((unitAir idOf x.1).assign (main x.2) i) := by
  simp only [unitInsts, List.mem_flatMap, List.mem_range, List.mem_map] at hp
  obtain ⟨x, hx, i, hi, r, hr, rfl⟩ := hp
  exact ⟨x, hx, i, hi, rfl, hr⟩

theorem unitInsts_holds {idOf : String → Nat} {units : List ((Chip F × Option (Unroll F)) × Nat)}
    {main : Nat → Nat → Scalar.Circuit.Var → F} (holds : StageHolds (unitAirs idOf units) main)
    {p : Chip F × (Scalar.Circuit.Var → F)} (hp : p ∈ unitInsts idOf units main) :
    (Bridge.lower idOf p.1).Holds p.2 := by
  obtain ⟨x, hx, i, hi, e, hr⟩ := mem_unitInsts hp
  have hx' : Prod.map (unitAir idOf) id x ∈ (unitAirs idOf units).zipIdx := by
    rw [unitAirs, ← List.map_zipIdx]
    exact List.mem_map_of_mem hx
  rw [e]
  exact unit_holds (holds _ hx' i hi) _ hr

theorem unitInsts_chip {idOf : String → Nat} {units : List ((Chip F × Option (Unroll F)) × Nat)}
    {main : Nat → Nat → Scalar.Circuit.Var → F} {p : Chip F × (Scalar.Circuit.Var → F)}
    (hp : p ∈ unitInsts idOf units main) : ∃ u ∈ units, p.1 = u.1.1 := by
  obtain ⟨x, hx, _, _, e, _⟩ := mem_unitInsts hp
  exact ⟨x.1, List.fst_mem_of_mem_zipIdx hx, e⟩

theorem sum_zipIdx {α : Type} (l : List α) (g : α → Nat) :
    (l.zipIdx.map fun x => g x.1).sum = (l.map g).sum := by
  rw [show (fun x : α × Nat => g x.1) = g ∘ Prod.fst from rfl, ← List.map_map, List.zipIdx_map_fst]

theorem length_unitInsts (idOf : String → Nat) (units : List ((Chip F × Option (Unroll F)) × Nat))
    (main : Nat → Nat → Scalar.Circuit.Var → F) :
    (unitInsts idOf units main).length = unitCapRows units := by
  simp only [unitInsts, unitCapRows, List.length_flatMap, List.length_map, length_unitRows,
    List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  exact sum_zipIdx units fun u => u.2 * unitBodies u.1

theorem lookupCount_unitInsts (idOf : String → Nat) (units : List ((Chip F × Option (Unroll F)) × Nat))
    (main : Nat → Nat → Scalar.Circuit.Var → F) :
    lookupCount (unitInsts idOf units main) = unitCapLookups units := by
  simp only [lookupCount, unitCapLookups, unitInsts, System.sum_map_flatMap, List.map_map,
    Function.comp_def, sum_const_length, length_unitRows, List.length_range, smul_eq_mul]
  congr 1
  rw [← sum_zipIdx units fun u => u.2 * unitBodies u.1 * (u.1.1.sends.length + u.1.1.memory.length)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro x _
  ring

end Units


/-! ## End to end -/

section Sound

variable [DecidableEq F]

/-- **End to end, wide stage, any chip rows.** Rows `insts` of lowered single
chips, the map tables over the encoded map claims and the ROM tables, whose
lookups balance against the entry request, prove the entry call; the ROM is
the one the ROM traces hold (`wideRom`). -/
theorem wide_heap_sound_insts {source : Generic.Source F} {entries : List String}
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
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {insts : List (Chip F × (Scalar.Circuit.Var → F))}
    (chipsIn : ∀ p ∈ insts, p.1 ∈ plan.singles)
    (instsHold : ∀ p ∈ insts, (Bridge.lower idOf p.1).Holds p.2)
    (capacity : insts.length ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound)
    (small : SmallCast F bound) (tags : 2 < bound) (lookups : lookupCount insts < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0)
    (shaped : Shaped.check (Depth.system cfg prepared.system) plan.singles idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ())
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {mainM mainR : Nat → Nat → Scalar.Circuit.Var → F}
    (balanced : (insts.map fun p => (Bridge.lower idOf p.1).rowLedger p.2).sum +
      stageLedger (mapAirs ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap) mainM +
      stageLedger (romAirs roms) mainR + Finsupp.single (encode idOf root) 1 = 0) :
    (wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (wideRom roms mainR)).decode
          specialized.program.enums) heap value result := by
  set rom := wideRom roms mainR
  have valid : rom.Valid := wideRom_valid widths (fun r hr i hi i' hi' e =>
    small.inj (by have := romCaps r hr; omega) (by have := romCaps r hr; omega) e) mainR
  have context' : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM rom) root = .ok () := by
    obtain ⟨formed, pub, _, wf⟩ := System.checkContext_iff.mp context
    exact System.checkContext_iff.mpr ⟨formed, pub, Erasure.rawROM_valid valid, wf⟩
  set claims := (Depth.system cfg prepared.system).mapClaims.map (encode idOf)
  set tables := stageLedger (mapAirs claims mapCap) mainM + stageLedger (romAirs roms) mainR
  have W : Wide plan idOf bound (Erasure.rawROM rom) root insts tables := {
    chips := chipsIn
    holds := instsHold
    small := small
    enablesOk := enablesOk
    tags := tags
    count := lookups
    shaped := Shaped.of_check shaped
    romPacked := rawROM_packed rom
    tableSupport := fun t ht => by
      simp only [tables, Finsupp.add_apply] at ht
      by_cases hm : stageLedger (mapAirs claims mapCap) mainM t = 0
      · rw [hm, zero_add] at ht
        exact Or.inr (romAirs_support roms mainR t ht)
      · obtain ⟨mc, hmc, e⟩ := List.mem_map.mp (mapAirs_support claims mapCap mainM t hm)
        exact Or.inl ⟨mc, hmc, e.symm⟩
    balanced := by
      rw [← balanced]
      simp only [tables]
      abel }
  obtain ⟨weighted, length, checked⟩ := W.checkMemo activated context'
  exact ⟨valid, prepared.depth_grouped_activated_heap_sound compiled certified plan activated entry valid
    signed rooted outside (length.trans capacity) characteristic checked arguments decoded⟩

/-- **End to end, wide stage.** One table per unit (`unitAir`: the lowered,
possibly unrolled chip, with its row count), the map tables and the ROM
tables; every unit row satisfies its circuit and all lookups balance against
the entry request. The map and ROM circuits have no constraints. -/
theorem wide_heap_sound {source : Generic.Source F} {entries : List String}
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
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {units : List ((Chip F × Option (Unroll F)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, unitOk idOf u.1 = true)
    (capacity : unitCapRows units ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound)
    (small : SmallCast F bound) (tags : 2 < bound) (lookups : unitCapLookups units < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0)
    (shaped : Shaped.check (Depth.system cfg prepared.system) plan.singles idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ())
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {mainU mainM mainR : Nat → Nat → Scalar.Circuit.Var → F}
    (holds : StageHolds (unitAirs idOf units) mainU)
    (balanced : stageLedger (unitAirs idOf units) mainU +
      stageLedger (mapAirs ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap) mainM +
      stageLedger (romAirs roms) mainR + Finsupp.single (encode idOf root) 1 = 0) :
    (wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (wideRom roms mainR)).decode
          specialized.program.enums) heap value result := by
  rw [unitAirs_ledger unrolled] at balanced
  exact wide_heap_sound_insts compiled prepared certified plan activated entry signed rooted outside
    arguments decoded idOf
    (fun p hp => by obtain ⟨u, hu, e⟩ := unitInsts_chip hp; rw [e]; exact chipsIn u hu)
    (fun p hp => unitInsts_holds holds hp)
    (by rw [length_unitInsts]; exact capacity) widths romCaps small tags
    (by rw [lookupCount_unitInsts]; exact lookups) characteristic shaped context enablesOk balanced

end Sound

end Aiur.Tiling.WideStage
