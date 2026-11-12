import IxCC.X86.Exe.Machine.Proof.Start

/-!
# The loader hypothesis can hold (non-vacuity of `Process.Loaded`)

`loaded_exists`: for a machine executable and any argument list of at most
2^24 arguments of at most 2^24 bytes each, there is a state that
`Process.Loaded` accepts: the file's bytes at `fileBase`, `rip` the entry, and
the argument block at `rsp = 2^47`, above the zero-filled segments (the
words from `2^47`, each argument's bytes in a slot of its own after them).
-/

set_option autoImplicit false

namespace IxCC.X86.Exe.Process

/-- Where the witness puts the argument block. -/
def bootBase : Nat := 2 ^ 47

section
variable (args : List (List Nat))

/-- Each argument's slot: the longest argument and its NUL. -/
def bootSlot : Nat := (args.map List.length).foldr max 0 + 1

/-- Where the arguments' bytes start: after `argc`, `argv[0 .. argc]` and the null. -/
def bootStrings : Nat := bootBase + 8 * (args.length + 3)

/-- The block's words: `argc`, `argv[0]` (unused), the arguments' addresses, the null. -/
def bootWord (k : Nat) : Word :=
  if k = 0 then UInt64.ofNat (args.length + 1)
  else if k = 1 then UInt64.ofNat (bootStrings args)
  else if k ≤ args.length + 1 then UInt64.ofNat (bootStrings args + (k - 2) * bootSlot args)
  else 0

/-- The witness's bytes: the file, the block's words, the arguments' bytes, zero elsewhere. -/
def bootBytes (file : ByteArray) (x : Word) : UInt8 :=
  if fileBase ≤ x.toNat ∧ x.toNat < fileBase + file.size then file[x.toNat - fileBase]!
  else if bootBase ≤ x.toNat ∧ x.toNat < bootStrings args then
    (bootWord args ((x.toNat - bootBase) / 8) >>> UInt64.ofNat (8 * ((x.toNat - bootBase) % 8))).toUInt8
  else if bootStrings args ≤ x.toNat then
    UInt8.ofNat ((((args[(x.toNat - bootStrings args) / bootSlot args]?).getD [])[(x.toNat - bootStrings args) %
      bootSlot args]?).getD 0)
  else 0

end

theorem le_bootSlot {args : List (List Nat)} {a : List Nat} (ha : a ∈ args) : a.length + 1 ≤ bootSlot args := by
  unfold bootSlot
  have : a.length ≤ (args.map List.length).foldr max 0 := by
    induction args with
    | nil => cases ha
    | cons b bs ih =>
      simp only [List.map_cons, List.foldr_cons]
      rcases List.mem_cons.mp ha with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)
  omega

theorem bootSlot_le {args : List (List Nat)} (h : ∀ a ∈ args, a.length < 2 ^ 24) : bootSlot args ≤ 2 ^ 24 := by
  unfold bootSlot
  have : (args.map List.length).foldr max 0 ≤ 2 ^ 24 - 1 := by
    induction args with
    | nil => simp
    | cons b bs ih =>
      simp only [List.map_cons, List.foldr_cons]
      have hb := h b List.mem_cons_self
      have := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
      omega
  omega

/-- A word read from bytes laid out little-endian. -/
theorem read64_of_bytes {m : Memory} {a v : Word}
    (h : ∀ j < 8, m.bytes (a + UInt64.ofNat j) = (v >>> UInt64.ofNat (8 * j)).toUInt8) : m.read64 a = v := by
  rw [← Memory.read64_write64 m a v]
  exact Memory.readLittle_congr _ _ _ _ (fun j hj => by
    rw [h j hj]
    exact (Memory.writeLittle_bytes m a v (by decide) hj).symm)

section
variable {L : Machine.Layout} {step : String} {object : ByteArray} (ce : Machine.Certified L step object)
include ce

theorem outside_high {a : Word} (h : 2 ^ 47 ≤ a.toNat) : OutsideSegments L.segments a := by
  obtain ⟨h1, -, -, h4, h5, h6, -, -, -, hd⟩ := numbers ce
  intro seg hseg
  simp only [Machine.Layout.segments, List.mem_cons, List.mem_nil_iff, or_false] at hseg
  rcases hseg with rfl | rfl
  · right; show dataBase + L.stackArea ≤ a.toNat; omega
  · right; show L.regionStart + alignUp L.region 0x1000 ≤ a.toNat; omega

/-- **The loader hypothesis can hold**: for any argument list of at most 2^24
arguments of at most 2^24 bytes each, there is a state `Process.Loaded`
accepts for the executable. -/
theorem loaded_exists {args : List (List Nat)} (hsize : args.length < 2 ^ 24 ∧ ∀ a ∈ args, a.length < 2 ^ 24) :
    ∃ s₀, Loaded ce.checked args s₀ := by
  obtain ⟨hlen, hlens⟩ := hsize
  have hM := bootSlot_le hlens
  have hfit := file_fit ce
  have ff := Machine.fileFacts ce.checked
  have hbl := ff.below
  have hsz := ff.size
  have hd : dataBase = 268435456 := rfl
  have hB : bootBase = 2 ^ 47 := rfl
  have hS : bootStrings args = bootBase + 8 * (args.length + 3) := rfl
  have hM1 : 1 ≤ bootSlot args := by unfold bootSlot; omega
  have htop : bootStrings args + args.length * bootSlot args < 2 ^ 63 := by
    have : args.length * bootSlot args ≤ 2 ^ 24 * 2 ^ 24 := Nat.mul_le_mul (Nat.le_of_lt hlen) hM
    omega
  let m : Memory := ⟨bootBytes args ce.checked.bytes, fun _ => true, fun _ => true⟩
  let sp : Word := UInt64.ofNat bootBase
  refine ⟨⟨⟨fun r => if r = .rsp then sp else 0, m⟩, UInt64.ofNat (fileBase + ce.checked.plan.placement.shellOffset), {}⟩,
    rfl, ?_, ?_⟩
  · intro i hi
    show bootBytes args ce.checked.bytes _ = _
    unfold bootBytes
    rw [toNat_small (by omega), ite_eq_left ⟨Nat.le_add_right _ _, by omega⟩, Nat.add_sub_cancel_left]
  · -- the argument block
    have hrsp : (fun r : GPR => if r = .rsp then sp else 0) .rsp = sp := by simp
    show ArgBlock m ((fun r : GPR => if r = .rsp then sp else 0) .rsp) args (OutsideSegments L.segments)
    rw [hrsp]
    have hsp : ∀ k, k < args.length + 3 → (sp + UInt64.ofNat (8 * k)).toNat = bootBase + 8 * k := fun k hk => by
      rw [toNat_add_small _ _ (by rw [toNat_small (by omega)]; omega), toNat_small (by omega)]
    have hword : ∀ k, k < args.length + 3 → m.read64 (sp + UInt64.ofNat (8 * k)) = bootWord args k := by
      intro k hk
      apply read64_of_bytes
      intro j hj
      show bootBytes args ce.checked.bytes _ = _
      unfold bootBytes
      have hx : (sp + UInt64.ofNat (8 * k) + UInt64.ofNat j).toNat = bootBase + (8 * k + j) := by
        rw [toNat_add_small _ _ (by rw [hsp k hk]; omega), hsp k hk]; omega
      rw [hx, ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩]
      rw [show bootBase + (8 * k + j) - bootBase = 8 * k + j by omega, show (8 * k + j) / 8 = k by omega,
        show (8 * k + j) % 8 = j by omega]
    have hstr : ∀ i, i < args.length → bootWord args (i + 2) = UInt64.ofNat (bootStrings args + i * bootSlot args) := by
      intro i hi
      unfold bootWord
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
      rfl
    have hbyte : ∀ i a, args[i]? = some a → ∀ j, j ≤ a.length →
        (UInt64.ofNat (bootStrings args + i * bootSlot args) + UInt64.ofNat j).toNat =
          bootStrings args + i * bootSlot args + j := by
      intro i a ha j hj
      have hi : i < args.length := (List.getElem?_eq_some_iff.mp ha).1
      have hl := le_bootSlot (List.mem_of_getElem? ha)
      have : (i + 1) * bootSlot args ≤ args.length * bootSlot args := Nat.mul_le_mul_right _ (by omega)
      rw [toNat_add_small _ _ (by rw [toNat_small (by rw [Nat.add_mul] at this; omega)]; rw [Nat.add_mul] at this; omega),
        toNat_small (by rw [Nat.add_mul] at this; omega)]
    have hstrbyte : ∀ i a, args[i]? = some a → ∀ j, j ≤ a.length →
        m.bytes (UInt64.ofNat (bootStrings args + i * bootSlot args) + UInt64.ofNat j) = UInt8.ofNat (a[j]?.getD 0) := by
      intro i a ha j hj
      show bootBytes args ce.checked.bytes _ = _
      unfold bootBytes
      have hl := le_bootSlot (List.mem_of_getElem? ha)
      have hq : (j + bootSlot args * i) / bootSlot args = i := by
        rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), Nat.zero_add]
      have hr : (j + bootSlot args * i) % bootSlot args = j := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      rw [hbyte i a ha j hj, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
        show bootStrings args + i * bootSlot args + j - bootStrings args = j + bootSlot args * i by
          rw [Nat.mul_comm]; omega, hq, hr, ha]
      rfl
    refine ⟨args.length + 1, by omega, ?_, .inr rfl, ?_, ?_, ?_, ?_⟩
    · rw [show sp = sp + UInt64.ofNat (8 * 0) from (UInt64.add_zero sp).symm, hword 0 (by omega)]
      rfl
    · rw [hword (args.length + 1 + 1) (by omega)]
      unfold bootWord
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    · intro i a ha
      have hi : i < args.length := (List.getElem?_eq_some_iff.mp ha).1
      have hiM : i * bootSlot args ≤ args.length * bootSlot args := Nat.mul_le_mul_right _ (by omega)
      rw [hword (i + 2) (by omega), hstr i hi]
      refine ⟨?_, fun j hj => ?_, ?_⟩
      · intro h0
        have := congrArg UInt64.toNat h0
        rw [toNat_small (by omega), show (0 : Word).toNat = 0 from rfl] at this
        omega
      · rw [hstrbyte i a ha j (Nat.le_of_lt hj), List.getElem?_eq_getElem hj, Option.getD_some, getElem!_pos a j hj]
      · rw [hstrbyte i a ha a.length (Nat.le_refl _), List.getElem?_eq_none (Nat.le_refl _)]
        rfl
    · intro i hi b hb
      apply outside_high ce
      rw [toNat_add_small _ _ (by rw [toNat_small (by omega)]; omega), toNat_small (by omega)]
      omega
    · intro i a ha j hj
      have hi : i < args.length := (List.getElem?_eq_some_iff.mp ha).1
      rw [hword (i + 2) (by omega), hstr i hi]
      apply outside_high ce
      rw [hbyte i a ha j hj]
      omega

end

end IxCC.X86.Exe.Process
