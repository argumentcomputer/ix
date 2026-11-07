import IxCC.Xv.Stacking.Proof.Trunc
import IxCC.Xv.Validate.Proof.Exec
import IxCC.X86.Memory

/-!
# A row in Xl and in the stacked code

Xl runs a row on a core whose registers lend each stack cell a scratch
register (`Xl.rowRegisters`) and whose memory is Xl's; the stacked code
runs the same row with the cell as an `rsp`-relative memory operand, on the
machine's registers and memory. `run_rel` relates the two runs:

* Xl's memory sits `Inside` the machine's: what Xl may read, the machine
  may read with the same bytes; what Xl may write, the machine may write.
* Arguments correspond slot by slot (`ArgRel`): the same register holding
  the same value (a write-only 32- or 64-bit register may start with
  anything), a scratch register against its cell (eight bytes the machine
  may read and write and Xl may not touch, holding the register's word
  unless the slot only writes it), the same address, or the same immediate.
* With at most one memory operand in the stacked row, the machine run
  succeeds with the same flags and outcome, keeps Xl's memory inside its
  own, writes each register Xl writes with Xl's value, leaves the cell it
  writes holding Xl's word, and changes no other byte Xl cannot write.

A cell may be read at any width (the row needs only its low bits, `sem_rel`)
and written only at width 64.
-/

namespace IxCC.Xv.Stacking.Proof

open IxCC.X86
open IxCC.Xv.Validate (Wide mergeWrite readReg_writeReg rowWrites implicitWrites)

/-! ## Bytes and words -/

theorem rangeAllowed_iff (permission : Word → Bool) (address : Word) (count : Nat) :
    Memory.rangeAllowed permission address count = true ↔
      ∀ i < count, permission (address + UInt64.ofNat i) = true := by
  induction count with
  | zero => simp [Memory.rangeAllowed]
  | succ count ih =>
      simp only [Memory.rangeAllowed, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨h, h'⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact h i hi
        · exact h'
      · intro h
        exact ⟨fun i hi => h i (by omega), h count (by omega)⟩

theorem width_bits (w : Width) : w.bits = 8 * w.bytes := by cases w <;> rfl

theorem width_bytes_le (w : Width) : w.bytes ≤ 8 := by cases w <;> decide

theorem width_bytes_pos (w : Width) : 0 < w.bytes := by cases w <;> decide

theorem readLittle_succ_toNat (m : Memory) (a : Word) {n : Nat} (hn : n < 8)
    (hlt : (m.readLittle a n).toNat < 2 ^ (8 * n)) :
    (m.readLittle a (n + 1)).toNat =
      (m.readLittle a n).toNat + (m.bytes (a + UInt64.ofNat n)).toNat * 2 ^ (8 * n) := by
  have hb := (m.bytes (a + UInt64.ofNat n)).toNat_lt
  have hs : (UInt64.ofNat (8 * n)).toNat = 8 * n := UInt64.toNat_ofNat_of_lt' (by
    simp only [UInt64.size]; omega)
  have hpow : 2 ^ (8 * n) * 2 ^ 8 ≤ 2 ^ 64 := by
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have hbig : (m.bytes (a + UInt64.ofNat n)).toNat * 2 ^ (8 * n) < 2 ^ 64 := by
    calc (m.bytes (a + UInt64.ofNat n)).toNat * 2 ^ (8 * n) < 2 ^ 8 * 2 ^ (8 * n) :=
          Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos _)
      _ ≤ 2 ^ 64 := by rw [Nat.mul_comm]; exact hpow
  simp only [Memory.readLittle, UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64, hs]
  rw [Nat.mod_eq_of_lt (by omega : 8 * n < 64), Nat.shiftLeft_eq, Nat.mod_eq_of_lt hbig, Nat.or_comm,
    Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt hlt, Nat.add_comm]

theorem readLittle_lt (m : Memory) (a : Word) : ∀ n, n ≤ 8 → (m.readLittle a n).toNat < 2 ^ (8 * n)
  | 0, _ => by simp [Memory.readLittle]
  | n + 1, hn => by
      have ih := readLittle_lt m a n (by omega)
      rw [readLittle_succ_toNat m a (by omega) ih]
      have hb := (m.bytes (a + UInt64.ofNat n)).toNat_lt
      have : (m.bytes (a + UInt64.ofNat n)).toNat * 2 ^ (8 * n) ≤ (2 ^ 8 - 1) * 2 ^ (8 * n) :=
        Nat.mul_le_mul_right _ (by omega)
      have e : 2 ^ (8 * (n + 1)) = 2 ^ 8 * 2 ^ (8 * n) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_comm]
      rw [e, Nat.sub_mul, Nat.one_mul] at *
      omega

theorem readLittle_mod (m : Memory) (a : Word) (k : Nat) :
    ∀ j, k + j ≤ 8 → (m.readLittle a (k + j)).toNat % 2 ^ (8 * k) = (m.readLittle a k).toNat
  | 0, h => Nat.mod_eq_of_lt (readLittle_lt m a k (by omega))
  | j + 1, h => by
      rw [← Nat.add_assoc, readLittle_succ_toNat m a (by omega) (readLittle_lt m a _ (by omega))]
      have e : 2 ^ (8 * (k + j)) = 2 ^ (8 * j) * 2 ^ (8 * k) := by
        rw [Nat.mul_add, Nat.pow_add, Nat.mul_comm]
      rw [e, ← Nat.mul_assoc, Nat.add_mul_mod_self_right]
      exact readLittle_mod m a k j (by omega)

/-- A narrow read is the low bits of the 64-bit read. -/
theorem read_eq_truncate (m : Memory) (w : Width) (a : Word) : m.read w a = w.truncate (m.read64 a) := by
  apply UInt64.toNat_inj.1
  rw [Encode.truncate_nat, width_bits]
  simp only [Memory.read64, Memory.read]
  have := readLittle_mod m a w.bytes (8 - w.bytes) (by have := width_bytes_le w; omega)
  rw [Nat.add_sub_cancel' (width_bytes_le w)] at this
  rw [show Width.bytes .w64 = 8 from rfl, this]

theorem truncate_truncate (w : Width) (v : Word) : w.truncate (w.truncate v) = w.truncate v := by
  apply UInt64.toNat_inj.1
  rw [Encode.truncate_nat, Encode.truncate_nat, Nat.mod_mod]

theorem truncate_w64 (v : Word) : Width.truncate .w64 v = v := by
  apply UInt64.toNat_inj.1
  rw [Encode.truncate_nat]
  exact Nat.mod_eq_of_lt v.toNat_lt

/-- The bytes a narrow write stores depend only on the low bits. -/
theorem byte_congr {w : Width} {v₁ v₂ : Word} (h : w.truncate v₁ = w.truncate v₂) {i : Nat}
    (hi : i < w.bytes) :
    (v₁ >>> UInt64.ofNat (8 * i)).toUInt8 = (v₂ >>> UInt64.ofNat (8 * i)).toUInt8 := by
  have h' := congrArg UInt64.toNat h
  rw [Encode.truncate_nat, Encode.truncate_nat, width_bits] at h'
  have hb := width_bytes_le w
  have hs : (UInt64.ofNat (8 * i)).toNat = 8 * i := UInt64.toNat_ofNat_of_lt' (by
    simp only [UInt64.size]; omega)
  apply UInt8.toNat_inj.1
  simp only [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, hs]
  rw [Nat.mod_eq_of_lt (by omega : 8 * i < 64), Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have key : ∀ x : Nat, x / 2 ^ (8 * i) % 2 ^ 8 = x % 2 ^ (8 * w.bytes) % (2 ^ (8 * i) * 2 ^ 8) / 2 ^ (8 * i) := by
    intro x
    rw [Nat.mod_mod_of_dvd, Nat.mod_mul_right_div_self]
    rw [← Nat.pow_add]
    exact Nat.pow_dvd_pow 2 (by omega)
  rw [key, key, h']

theorem writeLittle_congr (m : Memory) (a : Word) {w : Width} {v₁ v₂ : Word} (h : w.truncate v₁ = w.truncate v₂) :
    ∀ n, n ≤ w.bytes → m.writeLittle a v₁ n = m.writeLittle a v₂ n
  | 0, _ => rfl
  | n + 1, hn => by
      simp only [Memory.writeLittle]
      rw [writeLittle_congr m a h n (by omega), byte_congr h (by omega)]

theorem write_congr (m : Memory) (w : Width) (a : Word) {v₁ v₂ : Word} (h : w.truncate v₁ = w.truncate v₂) :
    m.write w a v₁ = m.write w a v₂ :=
  writeLittle_congr m a h w.bytes (Nat.le_refl _)

theorem writeReg_congr (c : Core) (w : Width) (r : GPR) {v₁ v₂ : Word} (h : w.truncate v₁ = w.truncate v₂) :
    c.writeReg w r v₁ = c.writeReg w r v₂ := by
  cases w with
  | w64 => simp only [truncate_w64] at h; rw [h]
  | _ => simp only [Core.writeReg, h]

theorem mergeWrite_congr (w : Width) (old : Word) {v₁ v₂ : Word} (h : w.truncate v₁ = w.truncate v₂) :
    mergeWrite w old v₁ = mergeWrite w old v₂ := by
  cases w with
  | w64 => simp only [truncate_w64] at h; rw [h]
  | _ => simp only [mergeWrite, h]

@[simp] theorem writeLittle_readable (m : Memory) (a v : Word) (n : Nat) :
    (m.writeLittle a v n).readable = m.readable := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

@[simp] theorem writeLittle_writable (m : Memory) (a v : Word) (n : Nat) :
    (m.writeLittle a v n).writable = m.writable := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

@[simp] theorem write_readable (m : Memory) (w : Width) (a v : Word) : (m.write w a v).readable = m.readable :=
  writeLittle_readable _ _ _ _

@[simp] theorem write_writable (m : Memory) (w : Width) (a v : Word) : (m.write w a v).writable = m.writable :=
  writeLittle_writable _ _ _ _

theorem w64_bytes : Width.bytes .w64 = 8 := rfl

/-! ## Xl memory inside the machine's -/

/-- What Xl may read, the machine may read with the same bytes; what Xl may
write, the machine may write. -/
structure Inside (xm mm : Memory) : Prop where
  readable : ∀ a, xm.readable a = true → mm.readable a = true
  writable : ∀ a, xm.writable a = true → mm.writable a = true
  bytes : ∀ a, (xm.readable a = true ∨ xm.writable a = true) → mm.bytes a = xm.bytes a

/-- Eight bytes the machine may read and write and Xl may not touch: a
stack cell. -/
structure Cell (xm mm : Memory) (a : Word) : Prop where
  readable : ∀ i < 8, mm.readable (a + UInt64.ofNat i) = true
  writable : ∀ i < 8, mm.writable (a + UInt64.ofNat i) = true
  noRead : ∀ i < 8, xm.readable (a + UInt64.ofNat i) = false
  noWrite : ∀ i < 8, xm.writable (a + UInt64.ofNat i) = false

theorem Inside.read? {xm mm : Memory} (h : Inside xm mm) {w : Width} {a v : Word}
    (hr : xm.read? w a = .ok v) : mm.read? w a = .ok v := by
  simp only [Memory.read?] at hr ⊢
  split at hr
  · rename_i hall
    have hall' := (rangeAllowed_iff _ _ _).1 hall
    have hm : Memory.rangeAllowed mm.readable a w.bytes = true :=
      (rangeAllowed_iff _ _ _).2 fun i hi => h.readable _ (hall' i hi)
    rw [if_pos hm, ← hr]
    simp only [Memory.read]
    congr 1
    exact Memory.readLittle_congr _ _ _ _ fun i hi => h.bytes _ (.inl (hall' i hi))
  · simp at hr

theorem write_bytes_inside {m : Memory} {w : Width} {a v b : Word} :
    (m.write w a v).bytes b = (if ∃ i < w.bytes, b = a + UInt64.ofNat i then
      (m.write w a v).bytes b else m.bytes b) := by
  split
  · rfl
  · rename_i hn
    exact Memory.writeLittle_bytes_outside _ _ _ _ _ fun i hi e => hn ⟨i, hi, e⟩

/-- A write Xl makes, made by the machine too, keeps Xl inside. -/
theorem Inside.write? {xm mm : Memory} (h : Inside xm mm) {w : Width} {a v : Word} {xm' : Memory}
    (hw : xm.write? w a v = .ok xm') :
    ∃ mm', mm.write? w a v = .ok mm' ∧ Inside xm' mm' ∧ xm'.readable = xm.readable ∧
      xm'.writable = xm.writable ∧ mm'.readable = mm.readable ∧ mm'.writable = mm.writable ∧
      (∀ b, xm.writable b = false → mm'.bytes b = mm.bytes b) := by
  simp only [Memory.write?] at hw ⊢
  split at hw
  · rename_i hall
    have hall' := (rangeAllowed_iff _ _ _).1 hall
    have hm : Memory.rangeAllowed mm.writable a w.bytes = true :=
      (rangeAllowed_iff _ _ _).2 fun i hi => h.writable _ (hall' i hi)
    rw [if_pos hm]
    simp only [Except.ok.injEq] at hw
    subst hw
    have hperm₁ : (xm.write w a v).readable = xm.readable := write_readable _ _ _ _
    have hperm₂ : (xm.write w a v).writable = xm.writable := write_writable _ _ _ _
    have hperm₃ : (mm.write w a v).readable = mm.readable := write_readable _ _ _ _
    have hperm₄ : (mm.write w a v).writable = mm.writable := write_writable _ _ _ _
    refine ⟨_, rfl, ⟨?_, ?_, ?_⟩, hperm₁, hperm₂, hperm₃, hperm₄, ?_⟩
    · intro b hb; rw [hperm₁] at hb; rw [hperm₃]; exact h.readable b hb
    · intro b hb; rw [hperm₂] at hb; rw [hperm₄]; exact h.writable b hb
    · intro b hb
      rw [hperm₁, hperm₂] at hb
      by_cases hin : ∃ i < w.bytes, b = a + UInt64.ofNat i
      · obtain ⟨i, hi, rfl⟩ := hin
        simp only [Memory.write]
        rw [Memory.writeLittle_bytes _ _ _ (width_bytes_le w) hi,
          Memory.writeLittle_bytes _ _ _ (width_bytes_le w) hi]
      · have out : ∀ i < w.bytes, b ≠ a + UInt64.ofNat i := fun i hi e => hin ⟨i, hi, e⟩
        simp only [Memory.write]
        rw [Memory.writeLittle_bytes_outside _ _ _ _ _ out, Memory.writeLittle_bytes_outside _ _ _ _ _ out]
        exact h.bytes b hb
    · intro b hb
      have out : ∀ i < w.bytes, b ≠ a + UInt64.ofNat i := fun i hi e => by
        have := hall' i hi
        rw [← e, hb] at this
        cases this
      simp only [Memory.write]
      exact Memory.writeLittle_bytes_outside _ _ _ _ _ out
  · simp at hw

/-- A write the machine makes to a cell keeps Xl inside. -/
theorem Inside.write_cell {xm mm : Memory} (h : Inside xm mm) {a : Word} (hc : Cell xm mm a) (v : Word) :
    Inside xm (mm.write .w64 a v) := by
  refine ⟨fun b hb => ?_, fun b hb => ?_, fun b hb => ?_⟩
  · simp only [write_readable]; exact h.readable b hb
  · simp only [write_writable]; exact h.writable b hb
  · have out : ∀ i < 8, b ≠ a + UInt64.ofNat i := fun i hi e => by
      subst e
      rcases hb with hb | hb
      · rw [hc.noRead i hi] at hb; cases hb
      · rw [hc.noWrite i hi] at hb; cases hb
    simp only [Memory.write, w64_bytes]
    rw [Memory.writeLittle_bytes_outside _ _ _ _ _ out]
    exact h.bytes b hb

theorem Cell.read? {xm mm : Memory} {a : Word} (hc : Cell xm mm a) (w : Width) :
    mm.read? w a = .ok (w.truncate (mm.read64 a)) := by
  simp only [Memory.read?]
  rw [if_pos ((rangeAllowed_iff _ _ _).2 fun i hi => hc.readable i (by have := width_bytes_le w; omega)),
    read_eq_truncate]

theorem Cell.write? {xm mm : Memory} {a : Word} (hc : Cell xm mm a) (v : Word) :
    mm.write? .w64 a v = .ok (mm.write .w64 a v) := by
  have h := (rangeAllowed_iff mm.writable a 8).2 fun i hi => hc.writable i hi
  simp [Memory.write?, w64_bytes, h]


theorem Cell.perm {xm mm xm' mm' : Memory} {a : Word} (hc : Cell xm mm a) (h₁ : xm'.readable = xm.readable)
    (h₂ : xm'.writable = xm.writable) (h₃ : mm'.readable = mm.readable) (h₄ : mm'.writable = mm.writable) :
    Cell xm' mm' a :=
  ⟨fun i hi => h₃ ▸ hc.readable i hi, fun i hi => h₄ ▸ hc.writable i hi, fun i hi => h₁ ▸ hc.noRead i hi,
    fun i hi => h₂ ▸ hc.noWrite i hi⟩

theorem write?_congr (m : Memory) (w : Width) (a : Word) {v₁ v₂ : Word} (h : w.truncate v₁ = w.truncate v₂) :
    m.write? w a v₁ = m.write? w a v₂ := by
  simp only [Memory.write?, write_congr m w a h]

/-! ## Corresponding arguments -/

/-- A row argument in Xl (`a₁`, on core `c₁`) and in the stacked code (`a₂`,
on `c₂`): the same register with the same value (a write-only 32- or 64-bit
register may start with anything), a scratch register and its cell (which
holds the register's word unless the slot only writes it; written only at
width 64), the same address, or the same immediate. -/
def ArgRel (c₁ c₂ : Core) (s : Slot) : Arg → Arg → Prop
  | .reg r₁, .reg r₂ => r₁ = r₂ ∧ (c₁.readReg r₁ = c₂.readReg r₂ ∨ (s.role = .write ∧ Wide s.width))
  | .reg r, .mem m => s.role ≠ .address ∧ (s.role = .read ∨ s.width = .w64) ∧
      Cell c₁.memory c₂.memory (m.eval c₂) ∧ (s.role = .write ∨ c₂.memory.read64 (m.eval c₂) = c₁.readReg r)
  | .mem m₁, .mem m₂ => m₁.eval c₁ = m₂.eval c₂
  | .imm v₁, .imm v₂ => v₁ = v₂
  | _, _ => False

/-- Corresponding arguments, one per slot. -/
def ArgsRel (c₁ c₂ : Core) : List Slot → List Arg → List Arg → Prop
  | [], [], [] => True
  | s :: ss, a₁ :: as₁, a₂ :: as₂ => ArgRel c₁ c₂ s a₁ a₂ ∧ ArgsRel c₁ c₂ ss as₁ as₂
  | _, _, _ => False

/-- The memory operands of a row. -/
def memCount : List Arg → Nat
  | [] => 0
  | .mem _ :: as => memCount as + 1
  | _ :: as => memCount as

/-- Slot `s` writes the cell at `a` from Xl's scratch register `r`. -/
def CellWrite (c₂ : Core) (a : Word) (r : GPR) : List Slot → List Arg → List Arg → Prop
  | s :: ss, a₁ :: as₁, a₂ :: as₂ =>
      (s.role.writes = true ∧ a₁ = .reg r ∧ ∃ m, a₂ = .mem m ∧ m.eval c₂ = a) ∨ CellWrite c₂ a r ss as₁ as₂
  | _, _, _ => False

/-- Some slot reads the cell at `a`, lent Xl's scratch register `r`. -/
def CellArg (c₂ : Core) (a : Word) (r : GPR) : List Slot → List Arg → List Arg → Prop
  | s :: ss, a₁ :: as₁, a₂ :: as₂ =>
      (s.role ≠ .write ∧ a₁ = .reg r ∧ ∃ m, a₂ = .mem m ∧ m.eval c₂ = a) ∨ CellArg c₂ a r ss as₁ as₂
  | _, _, _ => False

theorem CellWrite.memCount {c₂ : Core} {a : Word} {r : GPR} :
    ∀ {ss : List Slot} {as₁ as₂ : List Arg}, CellWrite c₂ a r ss as₁ as₂ → 0 < memCount as₂
  | _ :: _, _ :: _, a₂ :: as₂, h => by
      rcases h with ⟨_, _, m, rfl, _⟩ | h
      · simp [Proof.memCount]
      · have := CellWrite.memCount h
        cases a₂ <;> simp [Proof.memCount] <;> omega

theorem memCount_cons_le (a : Arg) (as : List Arg) : memCount as ≤ memCount (a :: as) := by
  cases a <;> simp [memCount]

/-- A register written by the stacked row is written by Xl's. -/
theorem ArgsRel.slotWrites_sublist {c₁ c₂ : Core} :
    ∀ {ss : List Slot} {as₁ as₂ : List Arg}, ArgsRel c₁ c₂ ss as₁ as₂ →
      (Validate.slotWrites ss as₂).Sublist (Validate.slotWrites ss as₁)
  | [], [], [], _ => by simp [Validate.slotWrites]
  | s :: ss, a₁ :: as₁, a₂ :: as₂, ⟨ha, hs⟩ => by
      have ih := ArgsRel.slotWrites_sublist hs
      cases a₁ <;> cases a₂ <;> simp only [ArgRel] at ha
      · obtain ⟨rfl, -⟩ := ha
        simp only [Validate.slotWrites]
        exact ih.append_left _
      · simp only [Validate.slotWrites]
        exact ih.trans (List.sublist_append_right _ _)
      · simp only [Validate.slotWrites]; exact ih
      · simp only [Validate.slotWrites]; exact ih

/-! ## Reading -/

theorem ArgRel.load_read {c₁ c₂ : Core} {s : Slot} {a₁ a₂ : Arg} (hin : Inside c₁.memory c₂.memory)
    (h : ArgRel c₁ c₂ s a₁ a₂) (hr : s.role = .read) {v₁ : Word} (hl : a₁.load c₁ s.width = .ok v₁) :
    ∃ v₂, a₂.load c₂ s.width = .ok v₂ ∧ s.width.truncate v₁ = s.width.truncate v₂ := by
  cases a₁ <;> cases a₂ <;> simp only [ArgRel] at h
  · obtain ⟨rfl, h | ⟨hw, _⟩⟩ := h
    · simp only [Arg.load, Except.ok.injEq] at hl ⊢
      subst hl
      exact ⟨_, rfl, by rw [h]⟩
    · rw [hr] at hw; cases hw
  · obtain ⟨-, -, hc, hv⟩ := h
    simp only [Arg.load, Except.ok.injEq] at hl
    subst hl
    refine ⟨_, hc.read? _, ?_⟩
    rcases hv with hw | hv
    · rw [hr] at hw; cases hw
    · rw [hv, truncate_truncate]
  · simp only [Arg.load] at hl ⊢
    rw [← h]
    exact ⟨v₁, hin.read? hl, rfl⟩
  · simp only [Arg.load, Except.ok.injEq] at hl ⊢
    subst hl h
    exact ⟨_, rfl, rfl⟩

theorem ArgRel.load_rw {c₁ c₂ : Core} {s : Slot} {a₁ a₂ : Arg} (hin : Inside c₁.memory c₂.memory)
    (h : ArgRel c₁ c₂ s a₁ a₂) (hr : s.role = .readWrite) {v₁ : Word} (hl : a₁.load c₁ s.width = .ok v₁) :
    a₂.load c₂ s.width = .ok v₁ := by
  cases a₁ <;> cases a₂ <;> simp only [ArgRel] at h
  · obtain ⟨rfl, h | ⟨hw, _⟩⟩ := h
    · simp only [Arg.load, Except.ok.injEq] at hl ⊢
      rw [← h, hl]
    · rw [hr] at hw; cases hw
  · obtain ⟨-, hw, hc, hv⟩ := h
    simp only [Arg.load, Except.ok.injEq] at hl
    subst hl
    rw [hr] at hw hv
    simp only [reduceCtorEq, false_or] at hw hv
    rw [hw]
    simp only [Arg.load]
    rw [hc.read? .w64, hv, truncate_w64]
  · simp only [Arg.load] at hl ⊢
    rw [← h]
    exact hin.read? hl
  · simp only [Arg.load, Except.ok.injEq] at hl ⊢
    rw [← h, hl]

theorem ArgRel.address {c₁ c₂ : Core} {s : Slot} {a₁ a₂ : Arg} (h : ArgRel c₁ c₂ s a₁ a₂)
    (hr : s.role = .address) : a₁.address c₁ = a₂.address c₂ := by
  cases a₁ <;> cases a₂ <;> simp only [ArgRel] at h
  · obtain ⟨rfl, h | ⟨hw, _⟩⟩ := h
    · exact h
    · rw [hr] at hw; cases hw
  · exact absurd hr h.1
  · exact h
  · exact h

theorem readSlots_rel {c₁ c₂ : Core} (hin : Inside c₁.memory c₂.memory) :
    ∀ {slots : List Slot} {as₁ as₂ : List Arg} {vs₁ : List Word}, ArgsRel c₁ c₂ slots as₁ as₂ →
      readSlots c₁ slots as₁ = .ok vs₁ →
      ∃ vs₂, readSlots c₂ slots as₂ = .ok vs₂ ∧ RelW (inWidths slots) vs₁ vs₂
  | [], [], [], vs₁, _, h => by
      simp only [readSlots, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨[], rfl, by simp [inWidths, RelW]⟩
  | ⟨kinds, width, role⟩ :: ss, a₁ :: as₁, a₂ :: as₂, vs₁, ⟨ha, hs⟩, h => by
      cases role with
      | write =>
        simp only [readSlots] at h ⊢
        obtain ⟨vs₂, h₂, hr⟩ := readSlots_rel hin hs h
        exact ⟨vs₂, h₂, by simpa [inWidths] using hr⟩
      | read =>
        simp only [readSlots, bind, Except.bind] at h ⊢
        cases hl : a₁.load c₁ width with
        | error e => simp [hl] at h
        | ok v₁ =>
          rw [hl] at h
          cases hr : readSlots c₁ ss as₁ with
          | error e => simp [hr] at h
          | ok rest₁ =>
            rw [hr] at h
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            obtain ⟨v₂, hl₂, hv⟩ := ArgRel.load_read (s := ⟨kinds, width, .read⟩) hin ha rfl hl
            obtain ⟨vs₂, hr₂, hrel⟩ := readSlots_rel hin hs hr
            refine ⟨v₂ :: vs₂, by simp only at hl₂; rw [hl₂, hr₂]; rfl, ?_⟩
            simp only [inWidths, List.filterMap_cons]
            exact ⟨hv, hrel⟩
      | readWrite =>
        simp only [readSlots, bind, Except.bind] at h ⊢
        cases hl : a₁.load c₁ width with
        | error e => simp [hl] at h
        | ok v₁ =>
          rw [hl] at h
          cases hr : readSlots c₁ ss as₁ with
          | error e => simp [hr] at h
          | ok rest₁ =>
            rw [hr] at h
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            have hl₂ := ArgRel.load_rw (s := ⟨kinds, width, .readWrite⟩) hin ha rfl hl
            obtain ⟨vs₂, hr₂, hrel⟩ := readSlots_rel hin hs hr
            refine ⟨v₁ :: vs₂, by simp only at hl₂; rw [hl₂, hr₂]; rfl, ?_⟩
            simp only [inWidths, List.filterMap_cons]
            exact ⟨rfl, hrel⟩
      | address =>
        simp only [readSlots, bind, Except.bind] at h ⊢
        cases hr : readSlots c₁ ss as₁ with
        | error e => simp [hr] at h
        | ok rest₁ =>
          rw [hr] at h
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          obtain ⟨vs₂, hr₂, hrel⟩ := readSlots_rel hin hs hr
          refine ⟨a₂.address c₂ :: vs₂, by rw [hr₂]; rfl, ?_⟩
          simp only [inWidths, List.filterMap_cons]
          exact ⟨ArgRel.address (s := ⟨kinds, width, .address⟩) ha rfl, hrel⟩

theorem RelW.append {ws₁ ws₂ : List (Option Width)} :
    ∀ {as₁ bs₁ as₂ bs₂ : List Word}, RelW ws₁ as₁ bs₁ → RelW ws₂ as₂ bs₂ →
      RelW (ws₁ ++ ws₂) (as₁ ++ as₂) (bs₁ ++ bs₂) := by
  induction ws₁ with
  | nil =>
    intro as₁ bs₁ as₂ bs₂ h₁ h₂
    obtain ⟨rfl, rfl⟩ := RelW.nil' h₁
    exact h₂
  | cons w ws ih =>
    intro as₁ bs₁ as₂ bs₂ h₁ h₂
    cases as₁ <;> cases bs₁ <;> simp only [RelW] at h₁
    exact ⟨h₁.1, ih h₁.2 h₂⟩

theorem RelW.implicits (c : Core) :
    ∀ is : List Implicit, RelW ((is.filter (·.role.reads)).map fun _ => none) (readImplicits c is)
      (readImplicits c is)
  | [] => by simp [readImplicits, RelW]
  | i :: is => by
      have ih := RelW.implicits c is
      unfold readImplicits at ih ⊢
      by_cases hr : i.role.reads = true
      · simp only [List.filter_cons, hr, ↓reduceIte, List.map_cons, List.filterMap_cons]
        exact ⟨rfl, ih⟩
      · simp only [List.filter_cons, hr, Bool.false_eq_true, ↓reduceIte, List.filterMap_cons]
        exact ih

/-! ## Writing -/

theorem ResW.head {w : Width} {ws : List Width} {rs₁ rs₂ : List Word} (h : ResW (w :: ws) rs₁ rs₂) :
    w.truncate (rs₁.headD 0) = w.truncate (rs₂.headD 0) := by
  have := h 0 w rfl
  cases rs₁ <;> cases rs₂ <;> simpa using this

theorem ResW.tail {w : Width} {ws : List Width} {rs₁ rs₂ : List Word} (h : ResW (w :: ws) rs₁ rs₂) :
    ResW ws rs₁.tail rs₂.tail := by
  intro i v hv
  have := h (i + 1) v (by simpa using hv)
  cases rs₁ <;> cases rs₂ <;> simpa using this

theorem readReg_writeReg_other (c : Core) (w : Width) {r r' : GPR} (v : Word) (h : r' ≠ r) :
    (c.writeReg w r v).readReg r' = c.readReg r' := by
  rw [readReg_writeReg, if_neg h]

theorem slotWrites_skip {s : Slot} (hs : s.role.writes = false) (a : Arg) (ss : List Slot) (as : List Arg) :
    Validate.slotWrites (s :: ss) (a :: as) = Validate.slotWrites ss as := by
  cases a <;> simp [Validate.slotWrites, hs]

/-- What a slot write leaves, related: Xl's memory inside the machine's,
permissions kept, every register the stacked row writes equal, each written
cell holding Xl's word, and no other machine byte Xl cannot write changed. -/
structure WriteOut (b₁ b₂ cur₁ cur₂ fin₁ fin₂ : Core) (slots : List Slot) (as₁ as₂ : List Arg) : Prop where
  inside : Inside fin₁.memory fin₂.memory
  readable₁ : fin₁.memory.readable = cur₁.memory.readable
  writable₁ : fin₁.memory.writable = cur₁.memory.writable
  readable₂ : fin₂.memory.readable = cur₂.memory.readable
  writable₂ : fin₂.memory.writable = cur₂.memory.writable
  written : ∀ r ∈ Validate.slotWrites slots as₂, fin₂.readReg r = fin₁.readReg r
  cell : ∀ a r, CellWrite b₂ a r slots as₁ as₂ → fin₂.memory.read64 a = fin₁.readReg r
  bytes : ∀ x, b₁.memory.writable x = false →
    (∀ a r, CellWrite b₂ a r slots as₁ as₂ → ∀ i < 8, x ≠ a + UInt64.ofNat i) →
    fin₂.memory.bytes x = cur₂.memory.bytes x
  noMem : memCount as₂ = 0 → fin₂.memory = cur₂.memory

theorem writeSlots_rel {b₁ b₂ : Core} {slots : List Slot} :
    ∀ {as₁ as₂ : List Arg} {rs₁ rs₂ : List Word} {cur₁ cur₂ fin₁ : Core},
      ArgsRel b₁ b₂ slots as₁ as₂ → ResW (outWidths slots) rs₁ rs₂ →
      Inside cur₁.memory cur₂.memory →
      cur₁.memory.readable = b₁.memory.readable → cur₁.memory.writable = b₁.memory.writable →
      cur₂.memory.readable = b₂.memory.readable → cur₂.memory.writable = b₂.memory.writable →
      (∀ r ∈ Validate.slotWrites slots as₁, cur₁.readReg r = b₁.readReg r) →
      (∀ r ∈ Validate.slotWrites slots as₂, cur₂.readReg r = b₂.readReg r) →
      (Validate.slotWrites slots as₁).Nodup → memCount as₂ ≤ 1 →
      writeSlots b₁ cur₁ slots as₁ rs₁ = .ok fin₁ →
      ∃ fin₂, writeSlots b₂ cur₂ slots as₂ rs₂ = .ok fin₂ ∧ WriteOut b₁ b₂ cur₁ cur₂ fin₁ fin₂ slots as₁ as₂ := by
  induction slots with
  | nil =>
    intro as₁ as₂ rs₁ rs₂ cur₁ cur₂ fin₁ hargs _ hin _ _ _ _ _ _ _ _ h
    cases as₁ <;> cases as₂ <;> simp only [ArgsRel] at hargs
    simp only [writeSlots, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨cur₂, rfl, hin, rfl, rfl, rfl, rfl, by simp [Validate.slotWrites], fun _ _ h => h.elim,
      fun _ _ _ => rfl, fun _ => rfl⟩
  | cons s ss ih =>
    intro as₁ as₂ rs₁ rs₂ cur₁ cur₂ fin₁ hargs hres hin hp₁ hp₂ hp₃ hp₄ hreg₁ hreg₂ hnd hone h
    cases as₁ with
    | nil => simp [ArgsRel] at hargs
    | cons a₁ as₁ =>
    cases as₂ with
    | nil => simp [ArgsRel] at hargs
    | cons a₂ as₂ =>
    obtain ⟨ha, hs⟩ := hargs
    have hone' : memCount as₂ ≤ 1 := Nat.le_trans (memCount_cons_le a₂ as₂) hone
    have hsub := ArgsRel.slotWrites_sublist hs
    obtain ⟨kinds, width, role⟩ := s
    by_cases hW : role.writes = true
    case neg =>
      have hW' : role.writes = false := by simpa using hW
      have hskip : ∀ (b cur : Core) (a : Arg) (as : List Arg) (rs : List Word),
          writeSlots b cur (⟨kinds, width, role⟩ :: ss) (a :: as) rs = writeSlots b cur ss as rs := by
        intro b cur a as rs
        cases role <;> simp [Role.writes] at hW' <;> rfl
      rw [hskip] at h
      rw [hskip]
      have hres' : ResW (outWidths ss) rs₁ rs₂ := by simpa [outWidths, hW'] using hres
      rw [slotWrites_skip hW'] at hreg₁ hnd hreg₂
      obtain ⟨fin₂, h₂, out⟩ := ih hs hres' hin hp₁ hp₂ hp₃ hp₄ hreg₁ hreg₂ hnd hone' h
      refine ⟨fin₂, h₂, out.inside, out.readable₁, out.writable₁, out.readable₂, out.writable₂,
        fun r hr => out.written r (by rwa [slotWrites_skip hW'] at hr), fun a r hc => ?_,
        fun x hx hout => ?_, fun hz => ?_⟩
      · rcases hc with ⟨hwr, _⟩ | hc
        · simp only at hwr; rw [hW'] at hwr; cases hwr
        · exact out.cell a r hc
      · exact out.bytes x hx fun a r hc => hout a r (.inr hc)
      · exact out.noMem (Nat.le_zero.1 (hz ▸ memCount_cons_le a₂ as₂))
    cases role with
    | read | address => simp [Role.writes] at hW
    | write | readWrite =>
      simp only [writeSlots, bind, Except.bind] at h ⊢
      have hres₀ := ResW.head (w := width) (by simpa [outWidths, Role.writes] using hres)
      have hres' : ResW (outWidths ss) rs₁.tail rs₂.tail :=
        ResW.tail (w := width) (by simpa [outWidths, Role.writes] using hres)
      cases a₁ <;> cases a₂ <;> simp only [ArgRel] at ha
      · -- a register in both
        rename_i r₁ r₂
        obtain ⟨rfl, hv⟩ := ha
        simp only [Arg.store] at h ⊢
        have hnd' : r₁ ∉ Validate.slotWrites ss as₁ ∧ (Validate.slotWrites ss as₁).Nodup := by
          simpa [Validate.slotWrites, Role.writes] using hnd
        have hnd₂ : r₁ ∉ Validate.slotWrites ss as₂ := fun hm => hnd'.1 (hsub.subset hm)
        have hreg₁' : ∀ r ∈ Validate.slotWrites ss as₁,
            (cur₁.writeReg width r₁ (rs₁.headD 0)).readReg r = b₁.readReg r := fun r hr => by
          rw [readReg_writeReg_other _ _ _ (fun e => hnd'.1 (by subst e; exact hr))]
          exact hreg₁ r (by simp [Validate.slotWrites, Role.writes, hr])
        have hreg₂' : ∀ r ∈ Validate.slotWrites ss as₂,
            (cur₂.writeReg width r₁ (rs₂.headD 0)).readReg r = b₂.readReg r := fun r hr => by
          rw [readReg_writeReg_other _ _ _ (fun e => hnd₂ (by subst e; exact hr))]
          exact hreg₂ r (by simp [Validate.slotWrites, Role.writes, hr])
        obtain ⟨fin₂, h₂, out⟩ := ih hs hres' (by simpa using hin) (by simpa using hp₁) (by simpa using hp₂)
          (by simpa using hp₃) (by simpa using hp₄) hreg₁' hreg₂' hnd'.2 hone' h
        refine ⟨fin₂, h₂, out.inside, by simpa using out.readable₁, by simpa using out.writable₁,
          by simpa using out.readable₂, by simpa using out.writable₂, fun r hr => ?_, fun a r hc => ?_,
          fun x hx hout => ?_, fun hz => ?_⟩
        · simp only [Validate.slotWrites, Role.writes, ↓reduceIte, List.singleton_append,
            List.mem_cons] at hr
          rcases hr with rfl | hr
          · rw [(Validate.writeSlots_frame h₂).2 _ hnd₂, (Validate.writeSlots_frame h).2 _ hnd'.1,
              readReg_writeReg, readReg_writeReg]
            simp only [↓reduceIte]
            rw [hreg₁ r (by simp [Validate.slotWrites, Role.writes]),
              hreg₂ r (by simp [Validate.slotWrites, Role.writes])]
            rcases hv with hv | ⟨_, hwide⟩
            · rw [hv, mergeWrite_congr _ _ hres₀]
            · rw [mergeWrite_congr _ _ hres₀]
              exact Validate.mergeWrite_wide hwide _ _ _
          · exact out.written r hr
        · rcases hc with ⟨_, _, m, hm, _⟩ | hc
          · cases hm
          · exact out.cell a r hc
        · rw [out.bytes x hx fun a r hc => hout a r (.inr hc)]
          simp
        · rw [out.noMem (by simpa [memCount] using hz)]
          simp
      · -- a scratch register and its cell
        rename_i r m
        obtain ⟨-, hw64, hc, -⟩ := ha
        have hw : width = .w64 := by
          rcases hw64 with h' | h'
          · cases h'
          · exact h'
        subst hw
        have hc₁ : Cell cur₁.memory cur₂.memory (m.eval b₂) := hc.perm hp₁ hp₂ hp₃ hp₄
        simp only [Arg.store] at h ⊢
        rw [hc₁.write? (rs₂.headD 0)]
        simp only [bind, Except.bind, pure, Except.pure]
        have hz : memCount as₂ = 0 := by simp [memCount] at hone; omega
        have hnd' : r ∉ Validate.slotWrites ss as₁ ∧ (Validate.slotWrites ss as₁).Nodup := by
          simpa [Validate.slotWrites, Role.writes] using hnd
        have hreg₁' : ∀ r' ∈ Validate.slotWrites ss as₁,
            (cur₁.writeReg .w64 r (rs₁.headD 0)).readReg r' = b₁.readReg r' := fun r' hr => by
          rw [readReg_writeReg_other _ _ _ (fun e => hnd'.1 (by subst e; exact hr))]
          exact hreg₁ r' (by simp [Validate.slotWrites, Role.writes, hr])
        obtain ⟨fin₂, h₂, out⟩ := ih (cur₂ := ⟨cur₂.registers, cur₂.memory.write .w64 (m.eval b₂) (rs₂.headD 0)⟩)
          hs hres' (by simpa using hin.write_cell hc₁ (rs₂.headD 0))
          (by simpa using hp₁) (by simpa using hp₂) (by simpa using hp₃) (by simpa using hp₄) hreg₁'
          (fun r' hr => hreg₂ r' (by simpa [Validate.slotWrites] using hr)) hnd'.2 hone' h
        have hfin : fin₂.memory = cur₂.memory.write .w64 (m.eval b₂) (rs₂.headD 0) := out.noMem hz
        refine ⟨fin₂, h₂, out.inside, by simpa using out.readable₁, by simpa using out.writable₁,
          by simpa using out.readable₂, by simpa using out.writable₂,
          fun r' hr => out.written r' (by simpa [Validate.slotWrites] using hr), fun a r' hcw => ?_,
          fun x hx hout => ?_, fun hz' => by simp [memCount] at hz'⟩
        · rcases hcw with ⟨_, hr, m', hm, ha⟩ | hcw
          · cases hr
            cases hm
            subst ha
            rw [hfin]
            change (cur₂.memory.write64 _ _).read64 _ = _
            rw [Memory.read64_write64, (Validate.writeSlots_frame h).2 _ hnd'.1, readReg_writeReg]
            simp only [↓reduceIte, mergeWrite]
            simpa only [truncate_w64] using hres₀.symm
          · exact absurd (CellWrite.memCount hcw) (by omega)
        · rw [hfin]
          refine Memory.writeLittle_bytes_outside _ _ _ _ _ fun i hi => ?_
          exact hout _ r (.inl ⟨rfl, rfl, m, rfl, rfl⟩) i hi
      · -- the same address
        rename_i m₁ m₂
        cases hw₁ : cur₁.memory.write? width (m₁.eval b₁) (rs₁.headD 0) with
        | error e =>
          simp only [Arg.store, hw₁, bind, Except.bind] at h
          cases h
        | ok xm' =>
        simp only [Arg.store, hw₁, bind, Except.bind, pure, Except.pure] at h
        obtain ⟨mm', hw₂, hin', q₁, q₂, q₃, q₄, hframe⟩ := hin.write? hw₁
        rw [ha] at hw₂
        simp only [Arg.store]
        rw [write?_congr _ _ _ hres₀.symm, hw₂]
        simp only [bind, Except.bind, pure, Except.pure]
        have hz : memCount as₂ = 0 := by simp [memCount] at hone; omega
        obtain ⟨fin₂, h₂, out⟩ := ih (cur₁ := ⟨cur₁.registers, xm'⟩) (cur₂ := ⟨cur₂.registers, mm'⟩) hs hres' hin' (by simpa [q₁] using hp₁) (by simpa [q₂] using hp₂)
          (by simpa [q₃] using hp₃) (by simpa [q₄] using hp₄)
          (fun r hr => hreg₁ r (by simpa [Validate.slotWrites] using hr))
          (fun r hr => hreg₂ r (by simpa [Validate.slotWrites] using hr))
          (by simpa [Validate.slotWrites] using hnd) hone' h
        refine ⟨fin₂, h₂, out.inside, by simpa [q₁] using out.readable₁, by simpa [q₂] using out.writable₁,
          by simpa [q₃] using out.readable₂, by simpa [q₄] using out.writable₂,
          fun r hr => out.written r (by simpa [Validate.slotWrites] using hr), fun a r hcw => ?_,
          fun x hx hout => ?_, fun hz' => by simp [memCount] at hz'⟩
        · rcases hcw with ⟨_, hr, _⟩ | hcw
          · cases hr
          · exact absurd (CellWrite.memCount hcw) (by omega)
        · rw [out.noMem hz]
          exact hframe x (by rw [hp₂]; exact hx)
      · -- an immediate
        simp only [Arg.store] at h ⊢
        obtain ⟨fin₂, h₂, out⟩ := ih hs hres' hin hp₁ hp₂ hp₃ hp₄
          (fun r hr => hreg₁ r (by simpa [Validate.slotWrites] using hr))
          (fun r hr => hreg₂ r (by simpa [Validate.slotWrites] using hr))
          (by simpa [Validate.slotWrites] using hnd) hone' h
        refine ⟨fin₂, h₂, out.inside, out.readable₁, out.writable₁, out.readable₂, out.writable₂,
          fun r hr => out.written r (by simpa [Validate.slotWrites] using hr), fun a r hcw => ?_,
          fun x hx hout => out.bytes x hx fun a r hc => hout a r (.inr hc),
          fun hz => out.noMem (by simpa [memCount] using hz)⟩
        rcases hcw with ⟨_, hr, _⟩ | hcw
        · cases hr
        · exact out.cell a r hcw

/-! ## Implicit registers -/

theorem writeImplicits_rel :
    ∀ {is : List Implicit} {res₁ res₂ : List Word} {cur₁ cur₂ : Core}, (implicitWrites is).Nodup →
      ResW (implicitOutWidths is) res₁ res₂ →
      (∀ i ∈ is, i.role.writes = true → Wide i.width ∨ cur₁.readReg i.reg = cur₂.readReg i.reg) →
      ∀ i ∈ is, i.role.writes = true →
        (writeImplicits cur₂ is res₂).readReg i.reg = (writeImplicits cur₁ is res₁).readReg i.reg
  | [], _, _, _, _, _, _, _, i, hi, _ => by simp at hi
  | j :: is, res₁, res₂, cur₁, cur₂, hn, hres, h, i, hi, hw => by
      simp only [writeImplicits]
      by_cases hj : j.role.writes = true
      · simp only [hj, ↓reduceIte]
        have hres' : ResW (j.width :: implicitOutWidths is) res₁ res₂ := by
          simpa [implicitOutWidths, List.filter_cons, hj] using hres
        have hn' : j.reg ∉ implicitWrites is ∧ (implicitWrites is).Nodup := by
          simpa [implicitWrites, List.filter_cons, hj] using hn
        have h' : ∀ i ∈ is, i.role.writes = true →
            Wide i.width ∨ (cur₁.writeReg j.width j.reg (res₁.headD 0)).readReg i.reg =
              (cur₂.writeReg j.width j.reg (res₂.headD 0)).readReg i.reg := by
          intro i' hi' hw'
          rcases h i' (List.mem_cons_of_mem _ hi') hw' with hw'' | he
          · exact .inl hw''
          · refine .inr ?_
            have : i'.reg ≠ j.reg := fun e => hn'.1 (by
              simp only [implicitWrites, List.mem_map, List.mem_filter]
              exact ⟨i', ⟨hi', hw'⟩, e⟩)
            rw [readReg_writeReg_other _ _ _ this, readReg_writeReg_other _ _ _ this, he]
        rcases List.mem_cons.1 hi with rfl | hi
        · rw [Validate.writeImplicits_frame hn'.1, Validate.writeImplicits_frame hn'.1, readReg_writeReg,
            readReg_writeReg]
          simp only [↓reduceIte]
          rw [mergeWrite_congr _ _ hres'.head]
          rcases h i (List.mem_cons_self) hw with hw' | he
          · exact Validate.mergeWrite_wide hw' _ _ _
          · rw [he]
        · exact writeImplicits_rel hn'.2 hres'.tail h' i hi hw
      · simp only [hj, Bool.false_eq_true, ↓reduceIte]
        have hres' : ResW (implicitOutWidths is) res₁ res₂ := by
          simpa [implicitOutWidths, List.filter_cons, hj] using hres
        have hn' : (implicitWrites is).Nodup := by
          simpa [implicitWrites, List.filter_cons, hj] using hn
        rcases List.mem_cons.1 hi with rfl | hi
        · exact absurd hw hj
        · exact writeImplicits_rel hn' hres' (fun i' hi' => h i' (List.mem_cons_of_mem _ hi')) i hi hw

/-! ## Footprints -/

theorem CellWrite.mem_slotWrites {c₂ : Core} {a : Word} {r : GPR} :
    ∀ {ss : List Slot} {as₁ as₂ : List Arg}, CellWrite c₂ a r ss as₁ as₂ → r ∈ Validate.slotWrites ss as₁
  | s :: ss, a₁ :: as₁, _ :: as₂, h => by
      rcases h with ⟨hw, rfl, _⟩ | h
      · simp [Validate.slotWrites, hw]
      · have := CellWrite.mem_slotWrites h
        cases a₁ <;> simp [Validate.slotWrites, this]

/-- Memory the stacked row reads: what Xl read, or a cell. -/
theorem reads_rel {c₁ c₂ : Core} :
    ∀ {slots : List Slot} {as₁ as₂ : List Arg} {vs₁ : List Word}, ArgsRel c₁ c₂ slots as₁ as₂ →
      readSlots c₁ slots as₁ = .ok vs₁ →
      ∀ acc ∈ slotReads c₂ slots as₂,
        (∀ i < acc.bytes, c₁.memory.readable (acc.address + UInt64.ofNat i) = true) ∨
          (acc.bytes ≤ 8 ∧ ∃ r, CellArg c₂ acc.address r slots as₁ as₂)
  | [], [], [], _, _, _, acc, hacc => by simp [slotReads] at hacc
  | ⟨kinds, width, role⟩ :: ss, a₁ :: as₁, a₂ :: as₂, vs₁, ⟨ha, hs⟩, h, acc, hacc => by
      have tail : ∀ vs, readSlots c₁ ss as₁ = .ok vs → acc ∈ slotReads c₂ ss as₂ →
          (∀ i < acc.bytes, c₁.memory.readable (acc.address + UInt64.ofNat i) = true) ∨
            (acc.bytes ≤ 8 ∧ ∃ r, CellArg c₂ acc.address r (⟨kinds, width, role⟩ :: ss) (a₁ :: as₁) (a₂ :: as₂)) :=
        fun vs hr hm => (reads_rel hs hr acc hm).imp_right fun ⟨hb, r, hc⟩ => ⟨hb, r, .inr hc⟩
      cases role with
      | write =>
        simp only [slotReads, List.nil_append] at hacc
        simp only [readSlots] at h
        exact tail _ h hacc
      | address =>
        simp only [slotReads, List.nil_append] at hacc
        simp only [readSlots, bind, Except.bind] at h
        split at h
        · simp at h
        · rename_i vs hr
          exact tail vs hr hacc
      | read | readWrite =>
        simp only [readSlots, bind, Except.bind] at h
        split at h
        · simp at h
        rename_i v hl
        split at h
        · simp at h
        rename_i vs hr
        simp only [slotReads, List.mem_append] at hacc
        rcases hacc with hacc | hacc
        · cases a₁ <;> cases a₂ <;> simp only [ArgRel] at ha <;> simp [Arg.access] at hacc
          · subst hacc
            exact .inr ⟨width_bytes_le _, _, .inl ⟨by simp, rfl, _, rfl, rfl⟩⟩
          · subst hacc
            rename_i m₁ m₂
            refine .inl fun i hi => ?_
            simp only [Arg.load, Memory.read?] at hl
            split at hl
            · rename_i hall
              rw [← ha]
              exact (rangeAllowed_iff _ _ _).1 hall i hi
            · simp at hl
        · exact tail vs hr hacc

/-- Memory the stacked row writes: what Xl wrote, or a cell (8 bytes). -/
theorem writes_rel {b₁ b₂ : Core} :
    ∀ {slots : List Slot} {as₁ as₂ : List Arg} {rs : List Word} {cur fin : Core}, ArgsRel b₁ b₂ slots as₁ as₂ →
      cur.memory.writable = b₁.memory.writable →
      writeSlots b₁ cur slots as₁ rs = .ok fin →
      ∀ acc ∈ slotWrites b₂ slots as₂,
        (∀ i < acc.bytes, b₁.memory.writable (acc.address + UInt64.ofNat i) = true) ∨
          (acc.bytes = 8 ∧ ∃ r, CellWrite b₂ acc.address r slots as₁ as₂)
  | [], [], [], _, _, _, _, _, _, acc, hacc => by simp [slotWrites] at hacc
  | ⟨kinds, width, role⟩ :: ss, a₁ :: as₁, a₂ :: as₂, rs, cur, fin, ⟨ha, hs⟩, hp, h, acc, hacc => by
      cases role with
      | read | address =>
        simp only [slotWrites, List.nil_append] at hacc
        simp only [writeSlots] at h
        exact (writes_rel hs hp h acc hacc).imp_right fun ⟨hb, r, hc⟩ => ⟨hb, r, .inr hc⟩
      | write | readWrite =>
        simp only [writeSlots, bind, Except.bind] at h
        split at h
        · simp at h
        rename_i cur' hst
        have hp' : cur'.memory.writable = b₁.memory.writable := by
          cases a₁ with
          | reg r => simp only [Arg.store, Except.ok.injEq] at hst; subst hst; simpa using hp
          | imm v => simp only [Arg.store, Except.ok.injEq] at hst; subst hst; exact hp
          | mem m =>
            simp only [Arg.store, bind, Except.bind] at hst
            split at hst
            · simp at hst
            · rename_i mem' hw
              simp only [pure, Except.pure, Except.ok.injEq] at hst
              subst hst
              simp only [Memory.write?] at hw
              split at hw
              · simp only [Except.ok.injEq] at hw; subst hw; simpa using hp
              · simp at hw
        simp only [slotWrites, List.mem_append] at hacc
        rcases hacc with hacc | hacc
        · cases a₁ <;> cases a₂ <;> simp only [ArgRel] at ha <;> simp [Arg.access] at hacc
          · subst hacc
            rename_i r m
            obtain ⟨-, hw64, -, -⟩ := ha
            have : width = .w64 := by rcases hw64 with h' | h' <;> first | exact h' | cases h'
            subst this
            exact .inr ⟨rfl, r, .inl ⟨rfl, rfl, m, rfl, rfl⟩⟩
          · subst hacc
            rename_i m₁ m₂
            refine .inl fun i hi => ?_
            simp only [Arg.store, bind, Except.bind] at hst
            split at hst
            · simp at hst
            · rename_i mem' hw
              simp only [Memory.write?] at hw
              split at hw
              · rename_i hall
                rw [← hp, ← ha]
                exact (rangeAllowed_iff _ _ _).1 hall i hi
              · simp at hw
        · exact (writes_rel hs hp' h acc hacc).imp_right fun ⟨hb, r, hc⟩ => ⟨hb, r, .inr hc⟩

/-! ## A row -/

/-- What a row leaves, related (`run_rel`). -/
structure RowOut (o : Op) (c₁ c₂ f₁ f₂ : Core) (as₁ as₂ : List Arg) : Prop where
  inside : Inside f₁.memory f₂.memory
  readable₁ : f₁.memory.readable = c₁.memory.readable
  writable₁ : f₁.memory.writable = c₁.memory.writable
  readable₂ : f₂.memory.readable = c₂.memory.readable
  writable₂ : f₂.memory.writable = c₂.memory.writable
  written : ∀ r ∈ rowWrites o as₂, f₂.readReg r = f₁.readReg r
  frame₁ : ∀ r, r ∉ rowWrites o as₁ → f₁.readReg r = c₁.readReg r
  frame₂ : ∀ r, r ∉ rowWrites o as₂ → f₂.readReg r = c₂.readReg r
  cell : ∀ a r, CellWrite c₂ a r (desc o).slots as₁ as₂ → f₂.memory.read64 a = f₁.readReg r
  bytes : ∀ x, c₁.memory.writable x = false →
    (∀ a r, CellWrite c₂ a r (desc o).slots as₁ as₂ → ∀ i < 8, x ≠ a + UInt64.ofNat i) →
    f₂.memory.bytes x = c₂.memory.bytes x
  reads : ∀ acc ∈ Op.reads o as₂ c₂,
    (∀ i < acc.bytes, c₁.memory.readable (acc.address + UInt64.ofNat i) = true) ∨
      (acc.bytes ≤ 8 ∧ ∃ r, CellArg c₂ acc.address r (desc o).slots as₁ as₂)
  writes : ∀ acc ∈ Op.writes o as₂ c₂,
    (∀ i < acc.bytes, c₁.memory.writable (acc.address + UInt64.ofNat i) = true) ∨
      (acc.bytes = 8 ∧ ∃ r, CellWrite c₂ acc.address r (desc o).slots as₁ as₂)

/-- A row without stack traffic, run by Xl (`as₁` on `c₁`) and by the
stacked code (`as₂` on `c₂`): the stacked run succeeds with the same flags
and outcome, and leaves related cores. -/
theorem run_rel {o : Op} (hstack : (desc o).stack = .none) {as₁ as₂ : List Arg} {c₁ c₂ f₁ : Core}
    {obs : ByteEval.Flags} {out₁ : SemOut}
    (hin : Inside c₁.memory c₂.memory) (hargs : ArgsRel c₁ c₂ (desc o).slots as₁ as₂)
    (himp : ∀ i ∈ (desc o).implicit, (i.role.reads = true ∨ (i.role.writes = true ∧ ¬ Wide i.width)) →
      c₁.readReg i.reg = c₂.readReg i.reg)
    (hw : (rowWrites o as₁).Nodup) (hone : memCount as₂ ≤ 1)
    (h : o.run as₁ c₁ obs = .ok (f₁, out₁)) :
    ∃ f₂ out₂, o.run as₂ c₂ obs = .ok (f₂, out₂) ∧ out₂.flags = out₁.flags ∧ out₂.taken = out₁.taken ∧
      RowOut o c₁ c₂ f₁ f₂ as₁ as₂ := by
  have hn₁ := List.nodup_append.1 hw
  have hsub := ArgsRel.slotWrites_sublist hargs
  have himpR : readImplicits c₁ (desc o).implicit = readImplicits c₂ (desc o).implicit :=
    Validate.readImplicits_corr fun i hi hr => himp i hi (.inl hr)
  rw [Validate.run_eq hstack] at h ⊢
  cases hr : readSlots c₁ (desc o).slots as₁ with
  | error e => simp [hr] at h
  | ok vs₁ =>
  obtain ⟨vs₂, hr₂, hrel⟩ := readSlots_rel hin hargs hr
  rw [hr₂, ← himpR]
  simp only
  simp only [hr] at h
  have hsem := sem_rel o hstack (vs₁ := vs₁ ++ readImplicits c₁ (desc o).implicit)
    (vs₂ := vs₂ ++ readImplicits c₁ (desc o).implicit) (RelW.append hrel (RelW.implicits c₁ _)) obs
  cases hs : (desc o).sem ⟨vs₁ ++ readImplicits c₁ (desc o).implicit, obs⟩ with
  | error e => simp [hs] at h
  | ok out₁' =>
  rw [hs] at hsem h
  cases hs₂ : (desc o).sem ⟨vs₂ ++ readImplicits c₁ (desc o).implicit, obs⟩ with
  | error e => rw [hs₂] at hsem; exact hsem.elim
  | ok out₂ =>
  rw [hs₂] at hsem
  obtain ⟨hfl, htk, hres, himpres⟩ := hsem
  simp only
  cases hw₁ : writeSlots c₁ c₁ (desc o).slots as₁ out₁'.results with
  | error e => simp [hw₁] at h
  | ok fin₁ =>
  simp only [hw₁, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨fin₂, h₂, wout⟩ := writeSlots_rel (cur₁ := c₁) (cur₂ := c₂) hargs hres hin rfl rfl rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl) hn₁.1 hone hw₁
  rw [h₂]
  have hfr₁ := (Validate.writeSlots_frame hw₁).2
  have hfr₂ := (Validate.writeSlots_frame h₂).2
  have hsi₁ : ∀ r ∈ Validate.slotWrites (desc o).slots as₁, r ∉ implicitWrites (desc o).implicit :=
    fun r hr hi => hn₁.2.2 r hr r hi rfl
  have hsi₂ : ∀ r ∈ Validate.slotWrites (desc o).slots as₂, r ∉ implicitWrites (desc o).implicit :=
    fun r hr => hsi₁ r (hsub.subset hr)
  have himpw : ∀ i ∈ (desc o).implicit, i.role.writes = true →
      i.reg ∈ implicitWrites (desc o).implicit := fun i hi hw => by
    simp only [implicitWrites, List.mem_map, List.mem_filter]
    exact ⟨i, ⟨hi, hw⟩, rfl⟩
  refine ⟨_, out₂, rfl, hfl.symm, htk.symm, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [Validate.writeImplicits_memory, Validate.writeImplicits_memory]; exact wout.inside
  · rw [Validate.writeImplicits_memory]; exact wout.readable₁
  · rw [Validate.writeImplicits_memory]; exact wout.writable₁
  · rw [Validate.writeImplicits_memory]; exact wout.readable₂
  · rw [Validate.writeImplicits_memory]; exact wout.writable₂
  · intro r hr
    simp only [rowWrites, List.mem_append] at hr
    rcases hr with hr | hr
    · rw [Validate.writeImplicits_frame (hsi₂ r hr), Validate.writeImplicits_frame (hsi₁ r (hsub.subset hr))]
      exact wout.written r hr
    · simp only [implicitWrites, List.mem_map, List.mem_filter] at hr
      obtain ⟨i, ⟨hi, hwi⟩, rfl⟩ := hr
      refine writeImplicits_rel hn₁.2.1 himpres (fun i hi hwi => ?_) i hi hwi
      by_cases hwide : Wide i.width
      · exact .inl hwide
      · refine .inr ?_
        have hni₁ : i.reg ∉ Validate.slotWrites (desc o).slots as₁ := fun hm => hsi₁ _ hm (himpw i hi hwi)
        have hni₂ : i.reg ∉ Validate.slotWrites (desc o).slots as₂ := fun hm => hsi₂ _ hm (himpw i hi hwi)
        rw [hfr₁ _ hni₁, hfr₂ _ hni₂]
        exact himp i hi (.inr ⟨hwi, hwide⟩)
  · intro r hr
    simp only [rowWrites, List.mem_append, not_or] at hr
    rw [Validate.writeImplicits_frame hr.2, hfr₁ r hr.1]
  · intro r hr
    simp only [rowWrites, List.mem_append, not_or] at hr
    rw [Validate.writeImplicits_frame hr.2, hfr₂ r hr.1]
  · intro a r hc
    rw [Validate.writeImplicits_memory, Validate.writeImplicits_frame (hsi₁ r (hc.mem_slotWrites))]
    exact wout.cell a r hc
  · intro x hx hout
    rw [Validate.writeImplicits_memory]
    exact wout.bytes x hx hout
  · intro acc hacc
    simp only [Op.reads, Op.pops, hstack, List.append_nil] at hacc
    exact reads_rel hargs hr acc hacc
  · intro acc hacc
    simp only [Op.writes, Op.pushes, hstack, List.nil_append] at hacc
    exact writes_rel hargs rfl hw₁ acc hacc

/-- `run_rel` for `Op.exec`: the flags agree too. -/
theorem exec_rel {o : Op} (hstack : (desc o).stack = .none) {as₁ as₂ : List Arg} {c₁ c₂ f₁ : Core}
    {flags flags' : ByteEval.Flags}
    (hin : Inside c₁.memory c₂.memory) (hargs : ArgsRel c₁ c₂ (desc o).slots as₁ as₂)
    (himp : ∀ i ∈ (desc o).implicit, (i.role.reads = true ∨ (i.role.writes = true ∧ ¬ Wide i.width)) →
      c₁.readReg i.reg = c₂.readReg i.reg)
    (hw : (rowWrites o as₁).Nodup) (hone : memCount as₂ ≤ 1)
    (h : o.exec as₁ c₁ flags = .ok (f₁, flags')) :
    ∃ f₂, o.exec as₂ c₂ flags = .ok (f₂, flags') ∧ RowOut o c₁ c₂ f₁ f₂ as₁ as₂ := by
  simp only [Op.exec, bind, Except.bind] at h ⊢
  cases hr : o.run as₁ c₁ (flags.restrict (desc o).flagsIn) with
  | error e => simp [hr] at h
  | ok res =>
    obtain ⟨fin, out⟩ := res
    simp only [hr, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨f₂, out₂, h₂, hfl, -, rest⟩ := run_rel hstack hin hargs himp hw hone hr
    rw [h₂]
    refine ⟨f₂, ?_, rest⟩
    simp only [pure, Except.pure, hfl]

end IxCC.Xv.Stacking.Proof
