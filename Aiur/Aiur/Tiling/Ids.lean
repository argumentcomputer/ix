import Aiur.Tiling.IxaTrace

/-!
# Channel ids from a compiled artifact

`Bridge.Shaped`'s `ids` and `idBound` ask that `idOf` be injective and below
`bound` on `Bridge.channels source chips root`: the chip names, their send
channels, the map claim channels and the root's channel. An exporter numbers
the channels by their index among the package's callables
(`Package.idOf = callables.idxOf`), so both facts follow when every channel is
a callable and there are at most `bound` callables (`checkIds_sound`): the
index of a member determines it, and is below the length.

`IChip.channels` reads the same names off the written chips, and
`channels_ofChip` proves they cover `Bridge.channels` for `IChip.ofChip` of the
source chips, given claim channels covering the system's map claims. So
`checkIds` on the written chips (`ids_ofChip`) discharges `ids` and `idBound`.
The exporters run it as `Package.checkIds` on every chip of the package, with
the package's map names as the claim channels. That these cover the channels
of the depth system's map claims (`claimsIn`) is `Claims.claimsIn_of_export`:
the decoded program section is the exported one (`program_of_decode`), whose
maps the compiler checks.
-/

namespace Aiur.Tiling.Ixa

open Aiur.Circuit

variable {F : Type}

/-- The channel names of the written chips, as `Bridge.channels` lists them
for the source chips, with the map claim channels given as `claims`. -/
def IChip.channels (chips : List (IChip F)) (claims : List String) (root : String) : List String :=
  chips.map IChip.name ++ chips.flatMap (fun c => c.sends.map ISend.channel) ++ claims ++ [root]

/-- Every name is a callable, and there are at most `bound` callables. -/
def checkIds (callables : List String) (bound : Nat) (names : List String) : Bool :=
  decide (callables.length ≤ bound) && names.all (callables.contains ·)

theorem checkIds_sound {callables : List String} {bound : Nat} {names : List String}
    (h : checkIds callables bound names = true) :
    (∀ x ∈ names, ∀ y ∈ names, callables.idxOf x = callables.idxOf y → x = y) ∧
      ∀ x ∈ names, callables.idxOf x < bound := by
  simp only [checkIds, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.contains_iff_mem] at h
  obtain ⟨length, member⟩ := h
  refine ⟨fun x hx y hy e => ?_, fun x hx => (List.idxOf_lt_length_of_mem (member x hx)).trans_le length⟩
  have gx := List.getElem_idxOf (List.idxOf_lt_length_of_mem (member x hx))
  have gy := List.getElem_idxOf (List.idxOf_lt_length_of_mem (member y hy))
  rw [← gx, ← gy]
  simp only [e]

variable [Field F] [DecidableEq F]

theorem channels_ofChip {source : Circuit.System F} {chips all : List (Chip F)} {root : Message F}
    {claims : List String} (sub : ∀ c ∈ chips, c ∈ all)
    (claimsIn : ∀ mc ∈ source.mapClaims, mc.channel ∈ claims) :
    ∀ x ∈ Bridge.channels source chips root, x ∈ IChip.channels (all.map IChip.ofChip) claims root.channel := by
  intro x hx
  simp only [Bridge.channels, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_singleton] at hx
  simp only [IChip.channels, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_singleton]
  rcases hx with ((⟨c, hc, rfl⟩ | ⟨c, hc, s, hs, rfl⟩) | ⟨mc, hmc, rfl⟩) | rfl
  · exact Or.inl (Or.inl (Or.inl ⟨_, ⟨c, sub c hc, rfl⟩, rfl⟩))
  · refine Or.inl (Or.inl (Or.inr ⟨_, ⟨c, sub c hc, rfl⟩, ?_⟩))
    simp only [IChip.ofChip, Optimized.Activation.compile, List.map_map, List.mem_map, Function.comp_def,
      Optimized.Activation.send]
    exact ⟨_, ⟨s, hs, rfl⟩, rfl⟩
  · exact Or.inl (Or.inr (claimsIn mc hmc))
  · exact Or.inr rfl

/-- `ids` and `idBound` of `Bridge.Shaped` for `idOf = callables.idxOf`, from
`checkIds` on the written form of any chip list containing `chips`. -/
theorem ids_ofChip {source : Circuit.System F} {chips all : List (Chip F)} {root : Message F}
    {claims callables : List String} {bound : Nat} (sub : ∀ c ∈ chips, c ∈ all)
    (claimsIn : ∀ mc ∈ source.mapClaims, mc.channel ∈ claims)
    (checked : checkIds callables bound (IChip.channels (all.map IChip.ofChip) claims root.channel) = true) :
    (∀ x ∈ Bridge.channels source chips root, ∀ y ∈ Bridge.channels source chips root,
      callables.idxOf x = callables.idxOf y → x = y) ∧
      ∀ x ∈ Bridge.channels source chips root, callables.idxOf x < bound := by
  have sound := checkIds_sound checked
  have cover := channels_ofChip (root := root) sub claimsIn
  exact ⟨fun x hx y hy => sound.1 x (cover x hx) y (cover y hy), fun x hx => sound.2 x (cover x hx)⟩

/-- The names of the package's maps, in program order: the maps of its decoded
program section, which are also the callables after the functions. -/
def Package.mapNames {F : Type} (p : Package F) : List String :=
  p.program.bytecode.maps.map (·.name)

/-- `checkIds` for the package's numbering (`Package.idOf`) on every written
chip, the package's maps and the entry `root`. -/
def Package.checkIds {F : Type} (p : Package F) (bound : Nat) (root : String) : Bool :=
  Ixa.checkIds p.callables.toList bound (IChip.channels p.chips.toList p.mapNames root)

/-- Every range map of the trace's depth limbs is among the package's maps. -/
def Package.checkRanges {F : Type} (p : Package F) : Bool :=
  p.limbs.all fun w => p.mapNames.contains (Optimized.Depth.rangeName w)

/-- The entry chip's depth record has no depth column: it is not recursive. -/
def Package.checkEntryPlain {F : Type} (p : Package F) (entry : String) : Bool :=
  match p.trace.chips.find? (·.1.name == entry) with
  | some (_, depth) => depth.column.isNone
  | none => false

omit [Field F] [DecidableEq F] in
/-- A depth record without a depth column is that of a non-recursive chip
(`entryPlain` of the composed theorems, for `IDepth.of`, which `putDepth_eq`
proves is what the compiler writes). -/
theorem recursive_of_column {cfg : Optimized.Depth.Config} {c : Chip F}
    (h : (IDepth.of cfg c).column = none) : cfg.recursive c.name = false := by
  simp only [IDepth.of] at h
  unfold Optimized.Depth.Config.recursive
  split at h
  · cases h
  · simpa using ‹¬(cfg.plan c.name).recursive = true›

theorem checkRanges_spec {F : Type} {p : Package F} (h : p.checkRanges = true) :
    ∀ w ∈ p.limbs, Optimized.Depth.rangeName w ∈ p.mapNames := by
  simpa [Package.checkRanges] using h

end Aiur.Tiling.Ixa
