import IxCC.X86.Exe.Machine.Proof.Report

/-!
# The shell's paths between its calls and system calls (X0-P, third part)

`from_loop` (`X86/Exe/Machine/Proof/Loop.lean`) follows one iteration of the
machine shell from `loop` to `loop` again, or to the end of the process. This
module proves the pieces it assembles, each a run of the byte machine from a
block's start to the next point of interest, or a memory fault on the way:

- `head`: the `loop` block up to `cx_init`'s call (`AtCall` for its driver);
- `back_nonzero`, `back_zero`: from a call's return through the `rsp` check
  and `initBack`/`stepBack` to `fail1` or onward;
- `fail_dispatch`: `fail1`–`fail4` to a resource failure's or a trap's message;
- `decode_even`, `decode_odd`, `split_run`: the result word's test and its
  split into the next state, the request's kind and its payload;
- `kinds`: the kind and payload to their block;
- `write_path`, `arg_path` pieces: the requests;
- the memory facts the iterations carry: the bytes outside the zero-filled
  segments and the argument cursor's 16 bytes are kept (`Kept`); a call's
  mapping and every store of the shell lie inside the segments.
-/

set_option autoImplicit false

namespace IxCC.X86.Exe.Process

open IxCC.X86.Encode (instructionOperation execute_linear)
open IxCC.X86.Exe.Shell (blockOffset instrOffset)
open SB

/-! ## Words -/

theorem toNat_add_small (x : Word) (k : Nat) (h : x.toNat + k < 2 ^ 64) : (x + UInt64.ofNat k).toNat = x.toNat + k := by
  rw [UInt64.toNat_add, toNat_small (by omega)]
  exact Nat.mod_eq_of_lt h

theorem ne_of_toNat {x y : Word} (h : x.toNat ≠ y.toNat) : x ≠ y := fun e => h (by rw [e])

theorem eval_at (core : Core) (r : GPR) {d : Nat} (h : signExtend32 (UInt32.ofNat d) = UInt64.ofNat d) :
    (SB.at_ r d).eval core = core.readReg r + UInt64.ofNat d := by
  show core.readReg r + 0 + signExtend32 (UInt32.ofNat d) = _
  rw [h, UInt64.add_zero]

/-- `shr r, imm8` (64 bits). -/
theorem exec_shr (s : ByteEval.State) (r : GPR) (v len : Nat) :
    ByteEval.execute ⟨instructionOperation (.op { mn := .shr, w := .w64, form := .MI } [.reg r, .imm (UInt64.ofNat v)]),
      len⟩ s =
      .ok ⟨s.core.setReg r ⟨(ShiftOp.shr.apply .w64 (s.core.readReg r) (shiftCount .w64 (UInt64.ofNat v))).setWidth 64⟩,
        s.rip + UInt64.ofNat len,
        ByteEval.Flags.merge Table.allSet s.flags (ByteEval.shiftFlags .shr .w64 (s.core.readReg r)
          (shiftCount .w64 (UInt64.ofNat v)))⟩ := by
  rw [instructionOperation, execute_linear rfl]
  simp [Op.exec, Op.run, Op.inputs, Op.stage, desc, Table.shiftDesc, Table.rmSlot, Table.immSlot, Table.shiftSem,
    readSlots, writeSlots, Arg.load, Arg.store, Except.mapError, Core.writeReg, bind, Except.bind, pure, Except.pure]

theorem shr_toNat (x : Word) (v : Nat) (hv : v < 64) :
    (⟨(ShiftOp.shr.apply .w64 x (shiftCount .w64 (UInt64.ofNat v))).setWidth 64⟩ : Word).toNat = x.toNat / 2 ^ v := by
  simp [ShiftOp.apply, shiftCount, Width.bits]
  rw [show (v % 18446744073709551616 &&& 63) = v by
    rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega]
  have h := BitVec.toNat_ushiftRight x.toBitVec v
  rw [Nat.shiftRight_eq_div_pow] at h
  exact h

theorem and_toNat (x : Word) (k : Nat) (hk : k < 64) : (x &&& UInt64.ofNat (2 ^ k - 1)).toNat = x.toNat % 2 ^ k := by
  rw [UInt64.toNat_and, toNat_small (by have : 2 ^ k ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega); omega),
    Nat.and_two_pow_sub_one_eq_mod]

theorem odd_test (w : Word) : (Width.w32.truncate (w &&& signExtend32 (UInt32.ofNat 1))).toNat = w.toNat % 2 := by
  show ((w &&& signExtend32 (UInt32.ofNat 1)) &&& 0xffffffff).toNat = _
  rw [show signExtend32 (UInt32.ofNat 1) = UInt64.ofNat (2 ^ 1 - 1) by decide, UInt64.toNat_and, and_toNat w 1 (by decide),
    show (0xffffffff : Word).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem load8_toNat (m : Memory) (a : Word) : (Width.w8.truncate (m.read .w8 a)).toNat = (m.bytes a).toNat := by
  show ((0 ||| (m.bytes (a + UInt64.ofNat 0)).toUInt64 <<< UInt64.ofNat 0) &&& 0xff).toNat = _
  rw [show a + UInt64.ofNat 0 = a from UInt64.add_zero a, show (0xff : Word) = UInt64.ofNat (2 ^ 8 - 1) from rfl,
    and_toNat _ 8 (by decide)]
  simp

/-! ## Memory -/

theorem read64_congr {m m' : Memory} {apart : Word → Prop} (hm : ∀ a, apart a → m'.bytes a = m.bytes a) {slot : Word}
    (hs : ∀ b < 8, apart (slot + UInt64.ofNat b)) : m'.read64 slot = m.read64 slot :=
  Memory.readLittle_congr _ _ _ _ (fun i hi => hm _ (hs i hi))

/-- A store's bytes, away from it. -/
theorem write_bytes_apart {m : Memory} {w : Width} {A v a : Word} (h : ∀ j < w.bytes, a ≠ A + UInt64.ofNat j) :
    (m.write w A v).bytes a = m.bytes a :=
  Memory.writeLittle_bytes_outside _ _ _ _ _ h

theorem write_read64_apart {m : Memory} {w : Width} {A v b : Word}
    (h : ∀ i < 8, ∀ j < w.bytes, b + UInt64.ofNat i ≠ A + UInt64.ofNat j) : (m.write w A v).read64 b = m.read64 b :=
  Memory.readLittle_congr _ _ _ _ (fun i hi => write_bytes_apart (h i hi))

theorem write_read64_same (m : Memory) (A v : Word) : (m.write .w64 A v).read64 A = v :=
  Memory.read64_write64 m A v

theorem write?_ok {m m' : Memory} {w : Width} {A v : Word} (h : m.write? w A v = .ok m') : m' = m.write w A v := by
  unfold Memory.write? at h
  split at h
  · cases h; rfl
  · cases h

/-- Writing a word twice is writing it once (the bytes). -/
theorem write_twice_bytes (m : Memory) (p q : Word → Bool) (A v : Word) :
    ((⟨(m.write .w64 A v).bytes, p, q⟩ : Memory).write .w64 A v).bytes = (m.write .w64 A v).bytes := by
  funext a
  by_cases h : ∃ j < 8, a = A + UInt64.ofNat j
  · obtain ⟨j, hj, rfl⟩ := h
    show ((⟨_, p, q⟩ : Memory).writeLittle A v 8).bytes _ = (m.writeLittle A v 8).bytes _
    rw [Memory.writeLittle_bytes _ _ _ (by decide) hj, Memory.writeLittle_bytes _ _ _ (by decide) hj]
  · rw [write_bytes_apart (w := .w64) (fun j hj e => h ⟨j, hj, e⟩),
      write_bytes_apart (w := .w64) (fun j hj e => h ⟨j, hj, e⟩)]

/-- Some state (the layout lemmas below use a driver of it, whose numbers do not depend on it). -/
def anyState : ByteEval.State := ⟨⟨fun _ => 0, Memory.flat⟩, 0, {}⟩

/-- The call top `C`, where the shell keeps its own bytes. -/
abbrev cTop (L : Machine.Layout) : Word := UInt64.ofNat L.callTop

/-- The addresses an iteration keeps: outside the zero-filled segments, and the
argument cursor's 16 bytes at `C + 16`. -/
def KeptAddr (L : Machine.Layout) (a : Word) : Prop :=
  OutsideSegments L.segments a ∨ (L.callTop + 16 ≤ a.toNat ∧ a.toNat < L.callTop + 32)

/-- What an iteration keeps of the memory of `s`. -/
def Kept (L : Machine.Layout) (s : ByteEval.State) (m : Memory) : Prop :=
  ∀ a, KeptAddr L a → m.bytes a = s.core.memory.bytes a

section
variable {L : Machine.Layout}

/-- An address of the stack segment is not outside the segments. -/
theorem inside_stack {a : Word} (h1 : dataBase ≤ a.toNat) (h2 : a.toNat < dataBase + L.stackArea) :
    ¬ OutsideSegments L.segments a := fun h => by
  have := h (dataBase, L.stackArea) List.mem_cons_self
  omega

theorem inside_region {a : Word} (h1 : L.regionStart ≤ a.toNat) (h2 : a.toNat < L.regionStart + alignUp L.region 0x1000) :
    ¬ OutsideSegments L.segments a := fun h => by
  have := h (L.regionStart, alignUp L.region 0x1000) (List.mem_cons_of_mem _ List.mem_cons_self)
  omega

theorem Kept.refl (s : ByteEval.State) : Kept L s s.core.memory := fun _ _ => rfl

theorem Kept.write {s : ByteEval.State} {m : Memory} (h : Kept L s m) {w : Width} {A v : Word}
    (hA : ∀ j < w.bytes, ¬ KeptAddr L (A + UInt64.ofNat j)) : Kept L s (m.write w A v) := fun a ha => by
  rw [write_bytes_apart (fun j hj e => hA j hj (e ▸ ha))]
  exact h a ha

end

section
variable {L : Machine.Layout} {step : String} {object : ByteArray} (ce : Machine.Certified L step object)
include ce

/-- The address of instruction `j` of block `b`. -/
abbrev addr (b j : Nat) : Word := UInt64.ofNat (shellAddr L step ce.checked b j)

/-- The layout's numbers, as the arithmetic below uses them. -/
theorem numbers :
    256 ≤ L.stackArea ∧ L.callTop = dataBase + L.stackArea - 256 ∧ L.shellTop = dataBase + L.stackArea ∧
      L.regionStart = dataBase + L.stackArea + 0x1000 ∧ L.region ≤ alignUp L.region 0x1000 ∧
      L.regionStart + alignUp L.region 0x1000 ≤ 2 ^ 47 ∧ L.stack + 256 ≤ L.stackArea ∧ 64 ≤ L.budget ∧
      L.budget = L.stack - 4096 ∧ dataBase = 268435456 := by
  obtain ⟨h1, -, h3, h4, h5⟩ := layout_numbers ce
  have ff := Machine.fileFacts ce.checked
  have hk := (initDriver_ok ce anyState).budgetMin
  have hb : ((initDriverOf L ce anyState).budget).toNat = L.budget := toNat_small (by
    have := ff.regionEnd; have : L.budget ≤ L.stack := Nat.sub_le _ _
    have := le_alignUp (L.stack + Machine.scratch) 0x1000 (by decide)
    have e1 : L.stackArea = alignUp (L.stack + Machine.scratch) 0x1000 := rfl
    have hd : dataBase = 268435456 := rfl
    omega)
  rw [hb] at hk
  exact ⟨h1, h3, h4, h5, le_alignUp _ _ (by decide), ff.regionEnd,
    le_alignUp (L.stack + Machine.scratch) 0x1000 (by decide), hk, rfl, rfl⟩

theorem cTop_add (k : Nat) (hk : k ≤ 256) : (cTop L + UInt64.ofNat k).toNat = L.callTop + k := by
  obtain ⟨h1, h2, -, -, -, h6, -, -, -, hd⟩ := numbers ce
  have : L.regionStart = dataBase + L.stackArea + 0x1000 := (numbers ce).2.2.2.1
  rw [toNat_add_small _ _ (by rw [toNat_small (by omega)]; omega), toNat_small (by omega)]

theorem cTop_toNat : (cTop L).toNat = L.callTop := by
  obtain ⟨h1, h2, -, -, -, h6, -, -, -, hd⟩ := numbers ce
  have : L.regionStart = dataBase + L.stackArea + 0x1000 := (numbers ce).2.2.2.1
  exact toNat_small (by omega)

theorem region_add (k : Nat) (hk : k ≤ 4096) :
    (UInt64.ofNat L.regionStart + UInt64.ofNat k).toNat = L.regionStart + k := by
  obtain ⟨-, -, -, -, h5, h6, -, -, -, hd⟩ := numbers ce
  rw [toNat_add_small _ _ (by rw [toNat_small (by omega)]; omega), toNat_small (by omega)]

/-- The shell's own words at `C + k` (below the cursor's) are not kept. -/
theorem notKept_low {a : Word} (h1 : L.callTop ≤ a.toNat) (h2 : a.toNat < L.callTop + 16) : ¬ KeptAddr L a := by
  obtain ⟨h1', h2', -, -, -, -, -, -, -, hd⟩ := numbers ce
  rintro (h | h)
  · exact inside_stack (L := L) (by omega) (by omega) h
  · omega

theorem notKept_high {a : Word} (h1 : L.callTop + 32 ≤ a.toNat) (h2 : a.toNat < L.callTop + 256) : ¬ KeptAddr L a := by
  obtain ⟨h1', h2', -, -, -, -, -, -, -, hd⟩ := numbers ce
  rintro (h | h)
  · exact inside_stack (L := L) (by omega) (by omega) h
  · omega

theorem notKept_region {a : Word} (h1 : L.regionStart ≤ a.toNat) (h2 : a.toNat < L.regionStart + 4096) :
    ¬ KeptAddr L a := by
  obtain ⟨h1', h2', -, h4, -, -, -, -, -, hd⟩ := numbers ce
  have hr := (initDriver_ok ce anyState).minSize
  have hs : ((initDriverOf L ce anyState).size).toNat = L.region := toNat_small (by
    have := (numbers ce).2.2.2.2.1; have := (numbers ce).2.2.2.2.2.1; omega)
  rw [hs] at hr
  have := (numbers ce).2.2.2.2.1
  rintro (h | h)
  · exact inside_region (L := L) (by omega) (by omega) h
  · omega

/-- **Outside the segments is outside every call's mapping.** -/
theorem kept_unmapped (s₀ : ByteEval.State) {a : Word} (h : KeptAddr L a) : (initDriverOf L ce s₀).mapped a = false := by
  rcases h with h | h
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hd⟩ := numbers ce
    have hseg1 := h (dataBase, L.stackArea) List.mem_cons_self
    have hseg2 := h (L.regionStart, alignUp L.region 0x1000) (List.mem_cons_of_mem _ List.mem_cons_self)
    show (L.driverWith ce.checked.plan.placement.textOffset (shellAddr L step ce.checked Machine.B.loop 12)
      s₀.core.memory.bytes).mapped a = false
    have e1 : (UInt64.ofNat L.regionStart).toNat = L.regionStart := toNat_small (by omega)
    have e2 : (UInt64.ofNat L.region).toNat = L.region := toNat_small (by omega)
    have e3 : (UInt64.ofNat (L.callTop - 8)).toNat = L.callTop - 8 := toNat_small (by omega)
    have e4 : (UInt64.ofNat L.budget).toNat = L.budget := toNat_small (by omega)
    simp only [Driver.mapped, Driver.inRegion, Driver.inStack, Machine.Layout.driverWith, e1, e2, e3, e4,
      Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    omega
  · have hk : a = cTop L + UInt64.ofNat (a.toNat - L.callTop) := by
      apply UInt64.toNat_inj.mp
      rw [cTop_add ce _ (by omega)]
      omega
    rw [hk]
    exact scratch_unmapped ce (shellAddr L step ce.checked Machine.B.loop 12) s₀.core.memory.bytes (by omega)

/-- The cursor's two words, kept. -/
theorem Kept.read64 {s : ByteEval.State} {m : Memory} (h : Kept L s m) {k : Nat} (hk1 : 16 ≤ k) (hk2 : k ≤ 24) :
    m.read64 (cTop L + UInt64.ofNat k) = s.core.memory.read64 (cTop L + UInt64.ofNat k) :=
  Memory.readLittle_congr _ _ _ _ (fun i hi => h _ (.inr (by
    have hi' : i < 8 := hi
    rw [UInt64.add_assoc, ← UInt64.ofNat_add, cTop_add ce _ (by omega)]; omega)))

/-- The store at `C + k` (`k ≤ 8`, a word) misses what an iteration keeps. -/
theorem store_low (k : Nat) (hk : k ≤ 8) :
    ∀ j < Width.w64.bytes, ¬ KeptAddr L (cTop L + UInt64.ofNat k + UInt64.ofNat j) := fun j hj => by
  have hj' : j < 8 := hj
  have e : (cTop L + UInt64.ofNat k + UInt64.ofNat j).toNat = L.callTop + k + j := by
    rw [UInt64.add_assoc, ← UInt64.ofNat_add, cTop_add ce _ (by omega)]; omega
  exact notKept_low ce (by omega) (by omega)

/-- The byte store at `C + 32` misses what an iteration keeps. -/
theorem store_out : ∀ j < Width.w8.bytes, ¬ KeptAddr L (cTop L + UInt64.ofNat 32 + UInt64.ofNat j) := fun j hj => by
  have hj' : j < 1 := hj
  have e : (cTop L + UInt64.ofNat 32 + UInt64.ofNat j).toNat = L.callTop + 32 + j := by
    rw [UInt64.add_assoc, ← UInt64.ofNat_add, cTop_add ce _ (by omega)]; omega
  exact notKept_high ce (by omega) (by omega)

/-- The budget's store at `region + 16` misses what an iteration keeps. -/
theorem store_region : ∀ j < Width.w64.bytes,
    ¬ KeptAddr L (UInt64.ofNat L.regionStart + UInt64.ofNat 16 + UInt64.ofNat j) :=
  fun j hj => by
    have hj' : j < 8 := by simpa [Width.bytes] using hj
    exact notKept_region ce (by rw [UInt64.add_assoc, ← UInt64.ofNat_add, region_add ce _ (by omega)]; omega)
      (by rw [UInt64.add_assoc, ← UInt64.ofNat_add, region_add ce _ (by omega)]; omega)

/-- The shell's word at `C + k` after a store at `C + k'`, `k ≠ k'` (both words of the shell's 256 bytes). -/
theorem cword_apart {m : Memory} {w : Width} {k k' : Nat} (hk : k + 8 ≤ 256) (hk' : k' + w.bytes ≤ 256)
    (hne : k + 8 ≤ k' ∨ k' + w.bytes ≤ k) (v : Word) :
    (m.write w (cTop L + UInt64.ofNat k') v).read64 (cTop L + UInt64.ofNat k) = m.read64 (cTop L + UInt64.ofNat k) :=
  write_read64_apart (fun i hi j hj e => by
    have := congrArg UInt64.toNat e
    rw [UInt64.add_assoc, ← UInt64.ofNat_add, cTop_add ce _ (by omega), UInt64.add_assoc, ← UInt64.ofNat_add,
      cTop_add ce _ (by omega)] at this
    omega)

theorem regionStart_toNat : (UInt64.ofNat L.regionStart).toNat = L.regionStart := by
  obtain ⟨-, -, -, -, h5, h6, -, -, -, -⟩ := numbers ce
  exact toNat_small (by omega)

/-- `cx_init`'s context pointer, less 48, is `region + 16`. -/
theorem ctx_sub (s₀ : ByteEval.State) :
    (initDriverOf L ce s₀).ctx - 48 = UInt64.ofNat L.regionStart + UInt64.ofNat 16 := by
  have hR := regionStart_toNat ce
  obtain ⟨-, -, -, -, h5, h6, -, -, -, -⟩ := numbers ce
  show UInt64.ofNat L.regionStart + UInt64.ofNat 64 - UInt64.ofNat 48 = _
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le, toNat_add_small _ 64 (by omega), toNat_small (by decide)]; omega),
    toNat_add_small _ 64 (by omega), toNat_add_small _ 16 (by omega), toNat_small (show 48 < 2 ^ 64 by decide)]
  omega

set_option maxRecDepth 20000 in
/-- **The loop head**: from `loop`, the block's first eleven instructions (the budget stored at
`region + 16`, `cx_init`'s arguments) reach its call of `cx_init` in the state its driver gives
it, or fault on the store. -/
theorem head {s : ByteEval.State} (hrip : s.rip = addr ce 6 0) :
    FaultsWithin ce.checked.bytes s 11 ∨ ∃ s₀, ByteEval.run ce.checked.bytes fetchBase 11 s = .ok s₀ ∧
      s₀.core.memory = s.core.memory.write .w64 (UInt64.ofNat L.regionStart + UInt64.ofNat 16) (UInt64.ofNat L.budget) ∧
      AtCall ce.checked.bytes object Rt.Procs.initSymbol (initDriverOf L ce s₀)
        [(initDriverOf L ce s₀).size, (initDriverOf L ce s₀).budget] (initDriverOf L ce s₀).initBytes s₀ := by
  let img := ce.checked.bytes
  let R : Word := UInt64.ofNat L.regionStart
  let B : Word := UInt64.ofNat L.budget
  let k1 := s.core.setReg .r14 R
  have e1 : ByteEval.step img fetchBase s = .ok ⟨k1, addr ce 6 1, s.flags⟩ :=
    mstep_ok ce (b := 6) (j := 0) (by decide) (s := s) (i := Instr.mov .w64 .r14 (.imm R)) (by rw [block_loop]; rfl)
      (ne_call_of_op ⟨_, _, rfl⟩) hrip (exec_mov _ _ _ _)
  let k2 := k1.setReg .rax B
  have e2 : ByteEval.step img fetchBase ⟨k1, addr ce 6 1, s.flags⟩ = .ok ⟨k2, addr ce 6 2, s.flags⟩ :=
    mstep_ok ce (b := 6) (j := 1) (by decide) (s := ⟨k1, addr ce 6 1, s.flags⟩) (i := Instr.mov .w64 .rax (.imm B))
      (by rw [block_loop]; rfl) (ne_call_of_op ⟨_, _, rfl⟩) rfl (exec_mov _ _ _ _)
  have hA : (SB.at_ .r14 16).eval k2 = R + UInt64.ofNat 16 := eval_at k2 .r14 (by decide)
  have hrax : k2.readReg .rax = B := rfl
  cases hw : k2.memory.write64? (R + UInt64.ofNat 16) B with
  | error f =>
    left
    refine ⟨2, by decide, ⟨k2, addr ce 6 2, s.flags⟩, f, run_comp (run_one e1) (run_one e2), ?_⟩
    refine mstep_fault ce (b := 6) (j := 2) (by decide) (s := ⟨k2, addr ce 6 2, s.flags⟩)
      (i := Instr.store .w64 (SB.at_ .r14 16) .rax) (by rw [block_loop]; rfl) (ne_call_of_op ⟨_, _, rfl⟩) rfl ?_
    rw [exec_store64]
    simp only [hA, hrax, hw]
  | ok m =>
    right
    have hm : m = s.core.memory.write .w64 (R + UInt64.ofNat 16) B := write?_ok (w := .w64) hw
    let k3 : Core := { k2 with memory := m }
    have e3 : ByteEval.step img fetchBase ⟨k2, addr ce 6 2, s.flags⟩ = .ok ⟨k3, addr ce 6 3, s.flags⟩ :=
      mstep_ok ce (b := 6) (j := 2) (by decide) (s := ⟨k2, addr ce 6 2, s.flags⟩)
        (i := Instr.store .w64 (SB.at_ .r14 16) .rax) (by rw [block_loop]; rfl) (ne_call_of_op ⟨_, _, rfl⟩) rfl
        (by rw [exec_store64]; simp only [hA, hrax, hw]; try rfl)
    let k4 := k3.setReg .rdi (k3.readReg .r14)
    have e4 : ByteEval.step img fetchBase ⟨k3, addr ce 6 3, s.flags⟩ = .ok ⟨k4, addr ce 6 4, s.flags⟩ :=
      mstep_ok ce (b := 6) (j := 3) (by decide) (s := ⟨k3, addr ce 6 3, s.flags⟩) (i := Instr.mov .w64 .rdi (.reg .r14))
        (by rw [block_loop]; rfl) (ne_call_of_op ⟨_, _, rfl⟩) rfl (exec_mov _ _ _ _)
    let k5 := k4.setReg .rsi (UInt64.ofNat L.region)
    have e5 : ByteEval.step img fetchBase ⟨k4, addr ce 6 4, s.flags⟩ = .ok ⟨k5, addr ce 6 5, s.flags⟩ :=
      mstep_ok ce (b := 6) (j := 4) (by decide) (s := ⟨k4, addr ce 6 4, s.flags⟩)
        (i := Instr.mov .w64 .rsi (.imm (UInt64.ofNat L.region)))
        (by rw [block_loop]; rfl) (ne_call_of_op ⟨_, _, rfl⟩) rfl (exec_mov _ _ _ _)
    let k6 := k5.setReg .rdx B
    have e6 : ByteEval.step img fetchBase ⟨k5, addr ce 6 5, s.flags⟩ = .ok ⟨k6, addr ce 6 6, s.flags⟩ :=
      mstep_ok ce (b := 6) (j := 5) (by decide) (s := ⟨k5, addr ce 6 5, s.flags⟩) (i := Instr.mov .w64 .rdx (.imm B))
        (by rw [block_loop]; rfl) (ne_call_of_op ⟨_, _, rfl⟩) rfl (exec_mov _ _ _ _)
    let k7 := k6.setReg .rcx (UInt64.ofNat 0)
    have e7 : ByteEval.step img fetchBase ⟨k6, addr ce 6 6, s.flags⟩ = .ok ⟨k7, addr ce 6 7, s.flags⟩ :=
      mstep_ok ce (b := 6) (j := 6) (by decide) (s := ⟨k6, addr ce 6 6, s.flags⟩)
        (i := Instr.mov .w64 .rcx (.imm (UInt64.ofNat 0)))
        (by rw [block_loop]; rfl) (ne_call_of_op ⟨_, _, rfl⟩) rfl (exec_mov _ _ _ _)
    let k8 := k7.setReg .r8 (UInt64.ofNat 0)
    have e8 : ByteEval.step img fetchBase ⟨k7, addr ce 6 7, s.flags⟩ = .ok ⟨k8, addr ce 6 8, s.flags⟩ :=
      mstep_ok ce (b := 6) (j := 7) (by decide) (s := ⟨k7, addr ce 6 7, s.flags⟩)
        (i := Instr.mov .w64 .r8 (.imm (UInt64.ofNat 0)))
        (by rw [block_loop]; rfl) (ne_call_of_op ⟨_, _, rfl⟩) rfl (exec_mov _ _ _ _)
    let k9 := k8.setReg .r9 (UInt64.ofNat 0)
    have e9 : ByteEval.step img fetchBase ⟨k8, addr ce 6 8, s.flags⟩ = .ok ⟨k9, addr ce 6 9, s.flags⟩ :=
      mstep_ok ce (b := 6) (j := 8) (by decide) (s := ⟨k8, addr ce 6 8, s.flags⟩)
        (i := Instr.mov .w64 .r9 (.imm (UInt64.ofNat 0)))
        (by rw [block_loop]; rfl) (ne_call_of_op ⟨_, _, rfl⟩) rfl (exec_mov _ _ _ _)
    let k10 := k9.setReg .r11 (cTop L)
    have e10 : ByteEval.step img fetchBase ⟨k9, addr ce 6 9, s.flags⟩ = .ok ⟨k10, addr ce 6 10, s.flags⟩ :=
      mstep_ok ce (b := 6) (j := 9) (by decide) (s := ⟨k9, addr ce 6 9, s.flags⟩)
        (i := Instr.mov .w64 .r11 (.imm (cTop L)))
        (by rw [block_loop]; rfl) (ne_call_of_op ⟨_, _, rfl⟩) rfl (exec_mov _ _ _ _)
    let k11 := k10.setReg .rsp (k10.readReg .r11)
    have e11 : ByteEval.step img fetchBase ⟨k10, addr ce 6 10, s.flags⟩ = .ok ⟨k11, addr ce 6 11, s.flags⟩ :=
      mstep_ok ce (b := 6) (j := 10) (by decide) (s := ⟨k10, addr ce 6 10, s.flags⟩) (i := Instr.mov .w64 .rsp (.reg .r11))
        (by rw [block_loop]; rfl) (ne_call_of_op ⟨_, _, rfl⟩) rfl (exec_mov _ _ _ _)
    let s₀ : ByteEval.State := ⟨k11, addr ce 6 11, s.flags⟩
    have hrun : ByteEval.run img fetchBase 11 s = .ok s₀ :=
      run_comp (run_one e1) (run_comp (run_one e2) (run_comp (run_one e3) (run_comp (run_one e4)
        (run_comp (run_one e5) (run_comp (run_one e6) (run_comp (run_one e7) (run_comp (run_one e8)
          (run_comp (run_one e9) (run_comp (run_one e10) (run_one e11))))))))))
    have hmem : s₀.core.memory = s.core.memory.write .w64 (R + UInt64.ofNat 16) B := hm
    refine ⟨s₀, hrun, hmem, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · obtain ⟨offset, hsym, hc⟩ := mcallsTo ce (b := 6) (j := 11) (by decide) (name := initSymbol)
        (by rw [block_loop]; rfl) (s := s₀) rfl
      exact ⟨offset, hsym, hc⟩
    · exact (next_addr (p := shellOf ce.checked) (origin := ce.checked.plan.placement.shellOffset) (b := 6)
        (j := 11) (i := .callExport initSymbol)
        (by show (blockAt (shellOf ce.checked) 6).instructions[11]? = _; rw [block_loop]; rfl)).symm
    · intro r hr
      cases r <;> simp [s₀, k11, k10, k9, k8, k7, k6, k5, k4, k3, k2, k1, Core.readReg, Core.setReg, Registers.set,
        Driver.core, Driver.regs, initDriverOf, Machine.Layout.driverWith, R, B] at hr ⊢
    · exact (sp_add8 ce (shellAddr L step ce.checked Machine.B.loop 12) s₀.core.memory.bytes).symm
    · show s₀.core.memory.bytes = ((⟨s₀.core.memory.bytes, fun _ => true, fun _ => true⟩ : Memory).write .w64
        ((initDriverOf L ce s₀).ctx - 48) (initDriverOf L ce s₀).budget).bytes
      rw [ctx_sub ce s₀, hmem]
      exact (write_twice_bytes s.core.memory _ _ _ _).symm

/-- The rest of a call's block after its return, and the `initBack`/`stepBack` block's two moves:
from the return address with `rsp` the call top, six instructions to the status test. -/
theorem back {b j b' : Nat} (hb : b < 46) (hb' : b' < 46)
    (hi : (blockAt (shellOf ce.checked) b).instructions[j]? = some (mI .r11 L.callTop))
    (hsz : (blockAt (shellOf ce.checked) b).instructions.size = j + 1)
    (ht : (blockAt (shellOf ce.checked) b).terminator = cmpR .rsp .r11 .ne 42 b')
    (hblk : blockAt (shellOf ce.checked) b' = ⟨#[mI .r11 L.shellTop, mR .rsp .r11], ifNz .rax 28 (b' + 1)⟩)
    {s : ByteEval.State} (hrip : s.rip = addr ce b j) (hrsp : s.core.readReg .rsp = cTop L) :
    ∃ fl, ByteEval.run ce.checked.bytes fetchBase 6 s = .ok ⟨((s.core.setReg .r11 (cTop L)).setReg .r11
      (UInt64.ofNat L.shellTop)).setReg .rsp (UInt64.ofNat L.shellTop), addr ce b' 2, fl⟩ := by
  let img := ce.checked.bytes
  let C := cTop L
  let T : Word := UInt64.ofNat L.shellTop
  let cmp : Compare := { width := .w64, left := .rsp, right := .reg .r11 }
  let k1 := s.core.setReg .r11 C
  have e1 : ByteEval.step img fetchBase s = .ok ⟨k1, addr ce b (j + 1), s.flags⟩ :=
    mstep_ok ce hb (s := s) (i := Instr.mov .w64 .r11 (.imm C)) hi (ne_call_of_op ⟨_, _, rfl⟩) hrip (exec_mov _ _ _ _)
  have e2 : ByteEval.run img fetchBase 3 ⟨k1, addr ce b (j + 1), s.flags⟩ =
      .ok ⟨k1, UInt64.ofNat (shellAddr L step ce.checked (UInt32.ofNat b').toNat 0), cmp.flags k1⟩ :=
    mrun_branch ce hb (o := cmp.row.1) (args := cmp.row.2) (cond := .ne) (yes := 42) (no := UInt32.ofNat b')
      ht (s := ⟨k1, addr ce b (j + 1), s.flags⟩) (core := k1) (fl := cmp.flags k1) (by rw [hsz]) (exec_compare _ _ _)
      (taken := false) (by
        rw [compare_test]
        show some (Condition.holds .ne .w64 (k1.readReg .rsp) (k1.readReg .r11)) = some false
        have h1 : k1.readReg .rsp = C := hrsp
        have h2 : k1.readReg .r11 = C := rfl
        rw [h1, h2]
        simp [Condition.holds])
  have hb'' : (UInt32.ofNat b').toNat = b' := UInt32.toNat_ofNat_of_lt' (by show b' < 4294967296; omega)
  rw [hb''] at e2
  let k3 := k1.setReg .r11 T
  have e3 : ByteEval.step img fetchBase ⟨k1, addr ce b' 0, cmp.flags k1⟩ = .ok ⟨k3, addr ce b' 1, cmp.flags k1⟩ :=
    mstep_ok ce hb' (j := 0) (s := ⟨k1, addr ce b' 0, cmp.flags k1⟩) (i := Instr.mov .w64 .r11 (.imm T))
      (by rw [hblk]; rfl) (ne_call_of_op ⟨_, _, rfl⟩) rfl (exec_mov _ _ _ _)
  let k4 := k3.setReg .rsp (k3.readReg .r11)
  have e4 : ByteEval.step img fetchBase ⟨k3, addr ce b' 1, cmp.flags k1⟩ = .ok ⟨k4, addr ce b' 2, cmp.flags k1⟩ :=
    mstep_ok ce hb' (j := 1) (s := ⟨k3, addr ce b' 1, cmp.flags k1⟩) (i := Instr.mov .w64 .rsp (.reg .r11))
      (by rw [hblk]; rfl) (ne_call_of_op ⟨_, _, rfl⟩) rfl (exec_mov _ _ _ _)
  exact ⟨cmp.flags k1, run_comp (run_one e1) (run_comp e2 (run_comp (run_one e3) (run_one e4)))⟩

/-- The status test after a return: nonzero to `fail1`. -/
theorem back_nonzero {b' : Nat} (hb' : b' < 46)
    (hblk : blockAt (shellOf ce.checked) b' = ⟨#[mI .r11 L.shellTop, mR .rsp .r11], ifNz .rax 28 (b' + 1)⟩)
    {core : Core} {fl : ByteEval.Flags} (hax : core.readReg .rax ≠ 0) :
    ∃ fl', ByteEval.run ce.checked.bytes fetchBase 2 ⟨core, addr ce b' 2, fl⟩ = .ok ⟨core, addr ce 28 0, fl'⟩ :=
  ⟨_, mrun_branch ce hb' (o := { mn := .test, w := .w64, form := .MR }) (args := [.reg .rax, .reg .rax]) (cond := .ne)
    (yes := 28) (no := UInt32.ofNat (b' + 1)) (by rw [hblk]; rfl) (s := ⟨core, addr ce b' 2, fl⟩) (core := core)
    (fl := ByteEval.aluFlags .and .w64 (core.readReg .rax) (core.readReg .rax)) (by rw [hblk]; rfl) (exec_test _ _ _ _)
    (taken := true) (by rw [test_ne_self]; simp [hax])⟩

/-- The status test after a return: zero to the next block. -/
theorem back_zero {b' : Nat} (hb' : b' < 46) (hb1 : b' + 1 < 46)
    (hblk : blockAt (shellOf ce.checked) b' = ⟨#[mI .r11 L.shellTop, mR .rsp .r11], ifNz .rax 28 (b' + 1)⟩)
    {core : Core} {fl : ByteEval.Flags} (hax : core.readReg .rax = 0) :
    ∃ fl', ByteEval.run ce.checked.bytes fetchBase 3 ⟨core, addr ce b' 2, fl⟩ = .ok ⟨core, addr ce (b' + 1) 0, fl'⟩ := by
  have h : ByteEval.run ce.checked.bytes fetchBase 3 ⟨core, addr ce b' 2, fl⟩ =
      .ok ⟨core, UInt64.ofNat (shellAddr L step ce.checked (UInt32.ofNat (b' + 1)).toNat 0),
        ByteEval.aluFlags .and .w64 (core.readReg .rax) (core.readReg .rax)⟩ :=
    mrun_branch ce hb' (o := { mn := .test, w := .w64, form := .MR }) (args := [.reg .rax, .reg .rax]) (cond := .ne)
      (yes := 28) (no := UInt32.ofNat (b' + 1)) (by rw [hblk]; rfl) (s := ⟨core, addr ce b' 2, fl⟩) (core := core)
      (fl := ByteEval.aluFlags .and .w64 (core.readReg .rax) (core.readReg .rax)) (by rw [hblk]; rfl) (exec_test _ _ _ _)
      (taken := false) (by rw [test_ne_self, hax]; rfl)
  rw [UInt32.toNat_ofNat_of_lt' (by show b' + 1 < 4294967296; omega)] at h
  exact ⟨_, h⟩

/-- One of the failure dispatch's comparisons (`fail1`–`fail4`). -/
theorem fail_step {b c t f : Nat} (hb : b < 46) (ht : t < 46) (hf : f < 46)
    (hblk : blockAt (shellOf ce.checked) b = ⟨#[], cmpI .rax c .eq t f⟩) {core : Core} (fl : ByteEval.Flags)
    {taken : Bool} (htk : Condition.holds .eq .w64 (core.readReg .rax) (signExtend32 (UInt32.ofNat c)) = taken) :
    ∃ fl', ByteEval.run ce.checked.bytes fetchBase (if taken then 2 else 3) ⟨core, addr ce b 0, fl⟩ =
      .ok ⟨core, addr ce (if taken then t else f) 0, fl'⟩ := by
  have h : ByteEval.run ce.checked.bytes fetchBase (if taken then 2 else 3) ⟨core, addr ce b 0, fl⟩ =
      .ok ⟨core, UInt64.ofNat (shellAddr L step ce.checked (if taken then (UInt32.ofNat t : BlockId) else UInt32.ofNat f).toNat 0),
        ({ width := .w64, left := .rax, right := .imm (UInt32.ofNat c) } : Compare).flags core⟩ :=
    mrun_branch ce hb (o := ({ width := .w64, left := .rax, right := .imm (UInt32.ofNat c) } : Compare).row.1)
      (args := ({ width := .w64, left := .rax, right := .imm (UInt32.ofNat c) } : Compare).row.2) (cond := .eq)
      (yes := UInt32.ofNat t) (no := UInt32.ofNat f) (by rw [hblk]; rfl) (s := ⟨core, addr ce b 0, fl⟩)
      (core := core) (by rw [hblk]; rfl) (exec_compare _ _ _) (taken := taken) (by rw [compare_test, ← htk]; rfl)
  cases taken with
  | true =>
    have h' : ByteEval.run ce.checked.bytes fetchBase 2 ⟨core, addr ce b 0, fl⟩ =
        .ok ⟨core, UInt64.ofNat (shellAddr L step ce.checked (UInt32.ofNat t).toNat 0), _⟩ := h
    rw [UInt32.toNat_ofNat_of_lt' (by show t < 4294967296; omega)] at h'
    exact ⟨_, h'⟩
  | false =>
    have h' : ByteEval.run ce.checked.bytes fetchBase 3 ⟨core, addr ce b 0, fl⟩ =
        .ok ⟨core, UInt64.ofNat (shellAddr L step ce.checked (UInt32.ofNat f).toNat 0), _⟩ := h
    rw [UInt32.toNat_ofNat_of_lt' (by show f < 4294967296; omega)] at h'
    exact ⟨_, h'⟩

/-- **The failure dispatch** (`fail1`–`fail4`): status `k + 1` (`k < 4`) to its message block. -/
theorem fail_dispatch {core : Core} {fl : ByteEval.Flags} (k : Nat) (hk : k < 4)
    (hax : core.readReg .rax = UInt64.ofNat (k + 1)) :
    ∃ m fl', ByteEval.run ce.checked.bytes fetchBase m ⟨core, addr ce 28 0, fl⟩ = .ok ⟨core, addr ce (38 + k) 0, fl'⟩ := by
  obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  · obtain ⟨f1, h1⟩ := fail_step ce (b := 28) (by decide) (by decide) (by decide) (block_fail1 L step _) fl (taken := true)
      (by rw [hax]; decide)
    exact ⟨_, _, h1⟩
  · obtain ⟨f1, h1⟩ := fail_step ce (b := 28) (by decide) (by decide) (by decide) (block_fail1 L step _) fl (taken := false)
      (by rw [hax]; decide)
    obtain ⟨f2, h2⟩ := fail_step ce (b := 29) (by decide) (by decide) (by decide) (block_fail2 L step _) f1 (taken := true)
      (by rw [hax]; decide)
    exact ⟨_, _, run_comp h1 h2⟩
  · obtain ⟨f1, h1⟩ := fail_step ce (b := 28) (by decide) (by decide) (by decide) (block_fail1 L step _) fl (taken := false)
      (by rw [hax]; decide)
    obtain ⟨f2, h2⟩ := fail_step ce (b := 29) (by decide) (by decide) (by decide) (block_fail2 L step _) f1 (taken := false)
      (by rw [hax]; decide)
    obtain ⟨f3, h3⟩ := fail_step ce (b := 30) (by decide) (by decide) (by decide) (block_fail3 L step _) f2 (taken := true)
      (by rw [hax]; decide)
    exact ⟨_, _, run_comp h1 (run_comp h2 h3)⟩
  · obtain ⟨f1, h1⟩ := fail_step ce (b := 28) (by decide) (by decide) (by decide) (block_fail1 L step _) fl (taken := false)
      (by rw [hax]; decide)
    obtain ⟨f2, h2⟩ := fail_step ce (b := 29) (by decide) (by decide) (by decide) (block_fail2 L step _) f1 (taken := false)
      (by rw [hax]; decide)
    obtain ⟨f3, h3⟩ := fail_step ce (b := 30) (by decide) (by decide) (by decide) (block_fail3 L step _) f2 (taken := false)
      (by rw [hax]; decide)
    obtain ⟨f4, h4⟩ := fail_step ce (b := 31) (by decide) (by decide) (by decide) (block_fail4 L step _) f3 (taken := true)
      (by rw [hax]; decide)
    exact ⟨_, _, run_comp h1 (run_comp h2 (run_comp h3 h4))⟩

/-! ## Steps, compactly -/

theorem mstep_movI {b j : Nat} (hb : b < 46) {r : GPR} {v : Nat}
    (hi : (blockAt (shellOf ce.checked) b).instructions[j]? = some (mI r v)) (core : Core) (fl : ByteEval.Flags) :
    ByteEval.step ce.checked.bytes fetchBase ⟨core, addr ce b j, fl⟩ =
      .ok ⟨core.setReg r (UInt64.ofNat v), addr ce b (j + 1), fl⟩ :=
  mstep_ok ce hb (s := ⟨core, addr ce b j, fl⟩) (i := Instr.mov .w64 r (.imm (UInt64.ofNat v))) hi
    (ne_call_of_op ⟨_, _, rfl⟩) rfl (exec_mov _ _ _ _)

theorem mstep_movR {b j : Nat} (hb : b < 46) {d r : GPR}
    (hi : (blockAt (shellOf ce.checked) b).instructions[j]? = some (mR d r)) (core : Core) (fl : ByteEval.Flags) :
    ByteEval.step ce.checked.bytes fetchBase ⟨core, addr ce b j, fl⟩ =
      .ok ⟨core.setReg d (core.readReg r), addr ce b (j + 1), fl⟩ :=
  mstep_ok ce hb (s := ⟨core, addr ce b j, fl⟩) (i := Instr.mov .w64 d (.reg r)) hi
    (ne_call_of_op ⟨_, _, rfl⟩) rfl (exec_mov _ _ _ _)

theorem mstep_alu {b j : Nat} (hb : b < 46) {op : AluOp} {w : Width} {r : GPR} {src : AluSource}
    (hi : (blockAt (shellOf ce.checked) b).instructions[j]? = some (.instr (Instr.alu op w r src)))
    (hnc : ∀ t, Instr.alu op w r src ≠ .call t) (core : Core)
    (fl : ByteEval.Flags) :
    ∃ fl', ByteEval.step ce.checked.bytes fetchBase ⟨core, addr ce b j, fl⟩ =
      .ok ⟨core.writeReg w r (op.eval (core.readReg r) (src.eval core)), addr ce b (j + 1), fl'⟩ := by
  obtain ⟨fl', h⟩ := exec_alu ⟨core, addr ce b j, fl⟩ op w r src (Shell.Instr.size (.instr (Instr.alu op w r src)))
  exact ⟨fl', mstep_ok ce hb (s := ⟨core, addr ce b j, fl⟩) (i := Instr.alu op w r src) hi
    hnc rfl h⟩

theorem mstep_shr {b j : Nat} (hb : b < 46) {r : GPR} {v : Nat}
    (hi : (blockAt (shellOf ce.checked) b).instructions[j]? = some (shrI r v)) (core : Core) (fl : ByteEval.Flags) :
    ∃ fl', ByteEval.step ce.checked.bytes fetchBase ⟨core, addr ce b j, fl⟩ =
      .ok ⟨core.setReg r ⟨(ShiftOp.shr.apply .w64 (core.readReg r) (shiftCount .w64 (UInt64.ofNat v))).setWidth 64⟩,
        addr ce b (j + 1), fl'⟩ :=
  ⟨_, mstep_ok ce hb (s := ⟨core, addr ce b j, fl⟩)
    (i := .op { mn := .shr, w := .w64, form := .MI } [.reg r, .imm (UInt64.ofNat v)]) hi
    (ne_call_of_op ⟨_, _, rfl⟩) rfl (exec_shr _ _ _ _)⟩

/-- A 64-bit load: a step, or a fault. -/
theorem mstep_load {b j : Nat} (hb : b < 46) {r : GPR} {A : MemAddr}
    (hi : (blockAt (shellOf ce.checked) b).instructions[j]? = some (ld r A)) (core : Core) (fl : ByteEval.Flags)
    {a : Word} (ha : A.eval core = a) :
    (∃ f, ByteEval.step ce.checked.bytes fetchBase ⟨core, addr ce b j, fl⟩ = .error (.memory f)) ∨
    ByteEval.step ce.checked.bytes fetchBase ⟨core, addr ce b j, fl⟩ =
      .ok ⟨core.setReg r (core.memory.read64 a), addr ce b (j + 1), fl⟩ := by
  cases hr : core.memory.read64? a with
  | error f =>
    exact .inl ⟨f, mstep_fault ce hb (s := ⟨core, addr ce b j, fl⟩) (i := Instr.load .w64 r A) hi
      (ne_call_of_op ⟨_, _, rfl⟩) rfl (by rw [exec_load64]; simp only [ha, hr])⟩
  | ok v =>
    have hv := read64?_value hr
    subst hv
    exact .inr (mstep_ok ce hb (s := ⟨core, addr ce b j, fl⟩) (i := Instr.load .w64 r A) hi
      (ne_call_of_op ⟨_, _, rfl⟩) rfl (by rw [exec_load64]; simp only [ha, hr]; try rfl))

/-- A byte load (`movzx`): a step, or a fault. -/
theorem mstep_load8 {b j : Nat} (hb : b < 46) {r : GPR} {A : MemAddr}
    (hi : (blockAt (shellOf ce.checked) b).instructions[j]? = some (ld8 r A)) (core : Core) (fl : ByteEval.Flags)
    {a : Word} (ha : A.eval core = a) :
    (∃ f, ByteEval.step ce.checked.bytes fetchBase ⟨core, addr ce b j, fl⟩ = .error (.memory f)) ∨
    ByteEval.step ce.checked.bytes fetchBase ⟨core, addr ce b j, fl⟩ =
      .ok ⟨core.setReg r (Width.w8.truncate (core.memory.read .w8 a)), addr ce b (j + 1), fl⟩ := by
  cases hr : core.memory.read? .w8 a with
  | error f =>
    exact .inl ⟨f, mstep_fault ce hb (s := ⟨core, addr ce b j, fl⟩) (i := Instr.load .w8 r A) hi
      (ne_call_of_op ⟨_, _, rfl⟩) rfl (by rw [exec_load8]; simp only [ha, hr])⟩
  | ok v =>
    have hv : v = core.memory.read .w8 a := by
      unfold Memory.read? at hr
      split at hr
      · cases hr; rfl
      · cases hr
    subst hv
    exact .inr (mstep_ok ce hb (s := ⟨core, addr ce b j, fl⟩) (i := Instr.load .w8 r A) hi
      (ne_call_of_op ⟨_, _, rfl⟩) rfl (by rw [exec_load8]; simp only [ha, hr]; try rfl))

/-- A store (64 bits or a byte): a step, or a fault. -/
theorem mstep_store {b j : Nat} (hb : b < 46) {w : Width} {A : MemAddr} {r : GPR}
    (hi : (blockAt (shellOf ce.checked) b).instructions[j]? = some (.instr (Instr.store w A r))) (hw : w = .w64 ∨ w = .w8)
    (core : Core) (fl : ByteEval.Flags) {a : Word} (ha : A.eval core = a) :
    (∃ f, ByteEval.step ce.checked.bytes fetchBase ⟨core, addr ce b j, fl⟩ = .error (.memory f)) ∨
    ByteEval.step ce.checked.bytes fetchBase ⟨core, addr ce b j, fl⟩ =
      .ok ⟨{ core with memory := core.memory.write w a (core.readReg r) }, addr ce b (j + 1), fl⟩ := by
  rcases hw with rfl | rfl
  · cases hwr : core.memory.write64? a (core.readReg r) with
    | error f =>
      exact .inl ⟨f, mstep_fault ce hb (s := ⟨core, addr ce b j, fl⟩) (i := Instr.store .w64 A r) hi
        (ne_call_of_op ⟨_, _, rfl⟩) rfl (by rw [exec_store64]; simp only [ha, hwr])⟩
    | ok m =>
      have hm : m = core.memory.write .w64 a (core.readReg r) := write?_ok (w := .w64) hwr
      subst hm
      exact .inr (mstep_ok ce hb (s := ⟨core, addr ce b j, fl⟩) (i := Instr.store .w64 A r) hi
        (ne_call_of_op ⟨_, _, rfl⟩) rfl (by rw [exec_store64]; simp only [ha, hwr]; try rfl))
  · cases hwr : core.memory.write? .w8 a (core.readReg r) with
    | error f =>
      exact .inl ⟨f, mstep_fault ce hb (s := ⟨core, addr ce b j, fl⟩) (i := Instr.store .w8 A r) hi
        (ne_call_of_op ⟨_, _, rfl⟩) rfl (by rw [exec_store8]; simp only [ha, hwr])⟩
    | ok m =>
      have hm : m = core.memory.write .w8 a (core.readReg r) := write?_ok hwr
      subst hm
      exact .inr (mstep_ok ce hb (s := ⟨core, addr ce b j, fl⟩) (i := Instr.store .w8 A r) hi
        (ne_call_of_op ⟨_, _, rfl⟩) rfl (by rw [exec_store8]; simp only [ha, hwr]; try rfl))

/-- A jump. -/
theorem mstep_jmp {b j t : Nat} (hb : b < 46) (hsz : (blockAt (shellOf ce.checked) b).instructions.size = j)
    (hterm : (blockAt (shellOf ce.checked) b).terminator = jmp t) (ht : t < 46) (core : Core) (fl : ByteEval.Flags) :
    ByteEval.step ce.checked.bytes fetchBase ⟨core, addr ce b j, fl⟩ = .ok ⟨core, addr ce t 0, fl⟩ := by
  have h := mstep_jump ce hb (t := UInt32.ofNat t) hterm (s := ⟨core, addr ce b j, fl⟩) (by rw [hsz])
  rw [UInt32.toNat_ofNat_of_lt' (by show t < 4294967296; omega)] at h
  exact h

/-- A compare-and-branch terminator `cmp r, c` on its condition. -/
theorem mrun_cmp {b j : Nat} (hb : b < 46) (hsz : (blockAt (shellOf ce.checked) b).instructions.size = j)
    {r : GPR} {c t f : Nat} {cond : Condition} (ht : t < 46) (hf : f < 46)
    (hterm : (blockAt (shellOf ce.checked) b).terminator = cmpI r c cond t f) {core : Core} (fl : ByteEval.Flags)
    {taken : Bool} (htk : Condition.holds cond .w64 (core.readReg r) (signExtend32 (UInt32.ofNat c)) = taken) :
    ∃ fl', ByteEval.run ce.checked.bytes fetchBase (if taken then 2 else 3) ⟨core, addr ce b j, fl⟩ =
      .ok ⟨core, addr ce (if taken then t else f) 0, fl'⟩ := by
  have h : ByteEval.run ce.checked.bytes fetchBase (if taken then 2 else 3) ⟨core, addr ce b j, fl⟩ =
      .ok ⟨core, UInt64.ofNat (shellAddr L step ce.checked (if taken then (UInt32.ofNat t : BlockId) else UInt32.ofNat f).toNat 0),
        ({ width := .w64, left := r, right := .imm (UInt32.ofNat c) } : Compare).flags core⟩ :=
    mrun_branch ce hb (o := ({ width := .w64, left := r, right := .imm (UInt32.ofNat c) } : Compare).row.1)
      (args := ({ width := .w64, left := r, right := .imm (UInt32.ofNat c) } : Compare).row.2) (cond := cond)
      (yes := UInt32.ofNat t) (no := UInt32.ofNat f) hterm (s := ⟨core, addr ce b j, fl⟩)
      (core := core) (by rw [hsz]) (exec_compare _ _ _) (taken := taken) (by rw [compare_test, ← htk]; rfl)
  cases taken with
  | true =>
    have h' : ByteEval.run ce.checked.bytes fetchBase 2 ⟨core, addr ce b j, fl⟩ =
        .ok ⟨core, UInt64.ofNat (shellAddr L step ce.checked (UInt32.ofNat t).toNat 0), _⟩ := h
    rw [UInt32.toNat_ofNat_of_lt' (by show t < 4294967296; omega)] at h'
    exact ⟨_, h'⟩
  | false =>
    have h' : ByteEval.run ce.checked.bytes fetchBase 3 ⟨core, addr ce b j, fl⟩ =
        .ok ⟨core, UInt64.ofNat (shellAddr L step ce.checked (UInt32.ofNat f).toNat 0), _⟩ := h
    rw [UInt32.toNat_ofNat_of_lt' (by show f < 4294967296; omega)] at h'
    exact ⟨_, h'⟩

end

/-- `cmp r, c` with `je`, on a small constant. -/
theorem holds_eq (v : Word) {c : Nat} (hc : c < 2 ^ 31) :
    Condition.holds .eq .w64 v (signExtend32 (UInt32.ofNat c)) = decide (v.toNat = c) := by
  have hs : signExtend32 (UInt32.ofNat c) = UInt64.ofNat c := by
    have h1 : (UInt32.ofNat c).toNat = c := UInt32.toNat_ofNat_of_lt' (by show c < 4294967296; omega)
    unfold signExtend32
    rw [ite_eq_left (by rw [UInt32.lt_iff_toNat_lt, h1]; show c < 2147483648; omega)]
    apply UInt64.toNat_inj.mp
    rw [UInt32.toNat_toUInt64, h1, toNat_small (by omega)]
  rw [hs]
  show (Width.w64.truncate v == Width.w64.truncate (UInt64.ofNat c)) = _
  rw [truncate64, truncate64]
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, decide_eq_true_iff]
  constructor
  · rintro rfl; exact toNat_small (by omega)
  · intro h; exact UInt64.toNat_inj.mp (by rw [h, toNat_small (by omega)])

/-- `cmp r, c` with `jne`, on a small constant. -/
theorem holds_ne (v : Word) {c : Nat} (hc : c < 2 ^ 31) :
    Condition.holds .ne .w64 v (signExtend32 (UInt32.ofNat c)) = decide (v.toNat ≠ c) := by
  have h := holds_eq v hc
  show (Width.w64.truncate v != Width.w64.truncate (signExtend32 (UInt32.ofNat c))) = _
  change (Width.w64.truncate v == Width.w64.truncate (signExtend32 (UInt32.ofNat c))) = _ at h
  rw [bne, h]
  by_cases hv : v.toNat = c <;> simp [hv]

theorem byte_of (v : Word) : (v >>> UInt64.ofNat (8 * 0)).toUInt8 = UInt8.ofNat v.toNat := by
  apply UInt8.toNat_inj.mp
  rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight]
  show _ = v.toNat % 2 ^ 8
  simp
theorem add_zero' (x : Word) : x + UInt64.ofNat 0 = x := UInt64.add_zero x

section
variable {L : Machine.Layout} {step : String} {object : ByteArray} (ce : Machine.Certified L step object)
include ce

/-- `decode`: an odd result word to `split`, an even one to the `notValue` message. -/
theorem decode_run (core : Core) (fl : ByteEval.Flags) :
    ∃ m core' fl', ByteEval.run ce.checked.bytes fetchBase m ⟨core, addr ce 10 0, fl⟩ =
      .ok ⟨core', addr ce (if (core.readReg .rdx).toNat % 2 = 1 then 11 else 43) 0, fl'⟩ ∧
      core'.memory = core.memory ∧ core'.readReg .rdx = core.readReg .rdx := by
  have e1 := mstep_movR ce (b := 10) (j := 0) (by decide) (d := .rcx) (r := .rdx) (by rw [block_decode] <;> rfl) core fl
  let k1 := core.setReg .rcx (core.readReg .rdx)
  obtain ⟨fl2, e2⟩ := mstep_alu ce (b := 10) (j := 1) (by decide) (op := .and) (w := .w32) (r := .rcx) (src := .imm 1)
    (by rw [block_decode] <;> rfl) (ne_call_of_op ⟨_, _, rfl⟩) k1 fl
  let k2 := k1.writeReg .w32 .rcx (AluOp.and.eval (k1.readReg .rcx) ((AluSource.imm 1).eval k1))
  have hrcx : (k2.readReg .rcx).toNat = (core.readReg .rdx).toNat % 2 := odd_test (core.readReg .rdx)
  by_cases hp : (core.readReg .rdx).toNat % 2 = 1
  · obtain ⟨fl3, e3⟩ := mrun_cmp ce (b := 10) (j := 2) (by decide) (by rw [block_decode] <;> rfl) (r := .rcx) (c := 0)
      (t := 43) (f := 11) (cond := .eq) (by decide) (by decide) (by rw [block_decode] <;> rfl) (core := k2) fl2
      (taken := false) (by rw [holds_eq _ (by decide), hrcx]; simp only [decide_eq_false_iff_not]; omega)
    refine ⟨5, k2, fl3, ?_, rfl, rfl⟩
    rw [ite_eq_left hp]
    exact run_comp (run_one e1) (run_comp (run_one e2) e3)
  · obtain ⟨fl3, e3⟩ := mrun_cmp ce (b := 10) (j := 2) (by decide) (by rw [block_decode] <;> rfl) (r := .rcx) (c := 0)
      (t := 43) (f := 11) (cond := .eq) (by decide) (by decide) (by rw [block_decode] <;> rfl) (core := k2) fl2
      (taken := true) (by rw [holds_eq _ (by decide), hrcx]; simp only [decide_eq_true_eq]; omega)
    refine ⟨4, k2, fl3, ?_, rfl, rfl⟩
    rw [ite_eq_right hp]
    exact run_comp (run_one e1) (run_comp (run_one e2) e3)

set_option maxRecDepth 20000 in
/-- `split`: from an odd word `w` in `rdx` (`x = w >>> 1`), the next state `x >>> 11` stored at
`C`, the kind `(x &&& 2047) &&& 7` in `rcx` and the payload `(x &&& 2047) >>> 3` in `rax`. -/
theorem split_run (core : Core) (fl : ByteEval.Flags) :
    FaultsWithin ce.checked.bytes ⟨core, addr ce 11 0, fl⟩ 9 ∨
    ∃ core' fl' z, ByteEval.run ce.checked.bytes fetchBase 9 ⟨core, addr ce 11 0, fl⟩ = .ok ⟨core', addr ce 11 9, fl'⟩ ∧
      core'.memory = core.memory.write .w64 (cTop L + UInt64.ofNat 0) z ∧
      z.toNat = (core.readReg .rdx).toNat / 2 / 2048 ∧
      (core'.readReg .rcx).toNat = (core.readReg .rdx).toNat / 2 % 2048 % 8 ∧
      (core'.readReg .rax).toNat = (core.readReg .rdx).toNat / 2 % 2048 / 8 := by
  obtain ⟨f1, e1⟩ := mstep_shr ce (b := 11) (j := 0) (by decide) (r := .rdx) (v := 1) (by rw [block_split] <;> rfl) core fl
  let x : Word := ⟨(ShiftOp.shr.apply .w64 (core.readReg .rdx) (shiftCount .w64 (UInt64.ofNat 1))).setWidth 64⟩
  have hx : x.toNat = (core.readReg .rdx).toNat / 2 := shr_toNat _ 1 (by decide)
  let k1 := core.setReg .rdx x
  have e2 := mstep_movR ce (b := 11) (j := 1) (by decide) (d := .rax) (r := .rdx) (by rw [block_split] <;> rfl) k1 f1
  let k2 := k1.setReg .rax (k1.readReg .rdx)
  obtain ⟨f3, e3⟩ := mstep_alu ce (b := 11) (j := 2) (by decide) (op := .and) (w := .w64) (r := .rax)
    (src := .imm (UInt32.ofNat 2047)) (by rw [block_split] <;> rfl) (ne_call_of_op ⟨_, _, rfl⟩) k2 f1
  let k3 := k2.writeReg .w64 .rax (AluOp.and.eval (k2.readReg .rax) ((AluSource.imm (UInt32.ofNat 2047)).eval k2))
  have hy : (k3.readReg .rax).toNat = x.toNat % 2048 := by
    show (x &&& signExtend32 (UInt32.ofNat 2047)).toNat = _
    rw [show signExtend32 (UInt32.ofNat 2047) = UInt64.ofNat (2 ^ 11 - 1) by decide, and_toNat x 11 (by decide)]
  obtain ⟨f4, e4⟩ := mstep_shr ce (b := 11) (j := 3) (by decide) (r := .rdx) (v := 11) (by rw [block_split] <;> rfl) k3 f3
  let z : Word := ⟨(ShiftOp.shr.apply .w64 (k3.readReg .rdx) (shiftCount .w64 (UInt64.ofNat 11))).setWidth 64⟩
  let k4 := k3.setReg .rdx z
  have e5 := mstep_movI ce (b := 11) (j := 4) (by decide) (r := .r10) (v := L.callTop) (by rw [block_split] <;> rfl) k4 f4
  let k5 := k4.setReg .r10 (UInt64.ofNat L.callTop)
  have hA : (SB.at_ .r10).eval k5 = cTop L + UInt64.ofNat 0 := eval_at k5 .r10 (by decide)
  have hpre : ByteEval.run ce.checked.bytes fetchBase 5 ⟨core, addr ce 11 0, fl⟩ = .ok ⟨k5, addr ce 11 5, f4⟩ :=
    run_comp (run_one e1) (run_comp (run_one e2) (run_comp (run_one e3) (run_comp (run_one e4) (run_one e5))))
  rcases mstep_store ce (b := 11) (j := 5) (by decide) (w := .w64) (A := SB.at_ .r10) (r := .rdx)
    (by rw [block_split] <;> rfl) (.inl rfl) k5 f4 hA with ⟨f, hf⟩ | e6
  · exact .inl ⟨5, by decide, ⟨k5, addr ce 11 5, f4⟩, f, hpre, hf⟩
  · right
    let k6 : Core := { k5 with memory := k5.memory.write .w64 (cTop L + UInt64.ofNat 0) (k5.readReg .rdx) }
    have e7 := mstep_movR ce (b := 11) (j := 6) (by decide) (d := .rcx) (r := .rax) (by rw [block_split] <;> rfl) k6 f4
    let k7 := k6.setReg .rcx (k6.readReg .rax)
    obtain ⟨f8, e8⟩ := mstep_alu ce (b := 11) (j := 7) (by decide) (op := .and) (w := .w64) (r := .rcx)
      (src := .imm (UInt32.ofNat 7)) (by rw [block_split] <;> rfl) (ne_call_of_op ⟨_, _, rfl⟩) k7 f4
    let k8 := k7.writeReg .w64 .rcx (AluOp.and.eval (k7.readReg .rcx) ((AluSource.imm (UInt32.ofNat 7)).eval k7))
    obtain ⟨f9, e9⟩ := mstep_shr ce (b := 11) (j := 8) (by decide) (r := .rax) (v := 3) (by rw [block_split] <;> rfl) k8 f8
    refine ⟨_, f9, z, run_comp hpre (run_comp (run_one e6) (run_comp (run_one e7) (run_comp (run_one e8)
      (run_one e9)))), rfl, ?_, ?_, ?_⟩
    · show (⟨(ShiftOp.shr.apply .w64 (k3.readReg .rdx) (shiftCount .w64 (UInt64.ofNat 11))).setWidth 64⟩ : Word).toNat = _
      rw [shr_toNat _ 11 (by decide)]
      show x.toNat / 2 ^ 11 = _
      rw [hx]
    · show ((k3.readReg .rax) &&& signExtend32 (UInt32.ofNat 7)).toNat = _
      rw [show signExtend32 (UInt32.ofNat 7) = UInt64.ofNat (2 ^ 3 - 1) by decide, and_toNat _ 3 (by decide), hy, hx]
    · show (⟨(ShiftOp.shr.apply .w64 (k3.readReg .rax) (shiftCount .w64 (UInt64.ofNat 3))).setWidth 64⟩ : Word).toNat = _
      rw [shr_toNat _ 3 (by decide), hy, hx]

/-- Where a request's kind and payload send the shell. -/
def kindTarget (kind payload : Nat) : Nat :=
  if kind = 0 then (if payload = 0 then 16 else 44) else if kind = 1 then 21 else if kind = 2 then 22
  else if kind = 3 then 26 else 44

/-- **The request's kind** (`split`'s terminator, `kindArg`, `kind1`–`kind3`). -/
theorem kinds (core : Core) (fl : ByteEval.Flags) :
    ∃ m fl', ByteEval.run ce.checked.bytes fetchBase m ⟨core, addr ce 11 9, fl⟩ =
      .ok ⟨core, addr ce (kindTarget (core.readReg .rcx).toNat (core.readReg .rax).toNat) 0, fl'⟩ := by
  by_cases h0 : (core.readReg .rcx).toNat = 0
  · obtain ⟨f1, e1⟩ := mrun_cmp ce (b := 11) (j := 9) (by decide) (by rw [block_split] <;> rfl) (r := .rcx) (c := 0)
      (t := 12) (f := 13) (cond := .eq) (by decide) (by decide) (by rw [block_split] <;> rfl) (core := core) fl
      (taken := true) (by rw [holds_eq _ (by decide)]; simp only [decide_eq_true_eq]; omega)
    by_cases hp : (core.readReg .rax).toNat = 0
    · obtain ⟨f2, e2⟩ := mrun_cmp ce (b := 12) (j := 0) (by decide) (by rw [block_kindArg] <;> rfl) (r := .rax) (c := 0)
        (t := 44) (f := 16) (cond := .ne) (by decide) (by decide) (by rw [block_kindArg] <;> rfl) (core := core) f1
        (taken := false) (by rw [holds_ne _ (by decide)]; simp only [decide_eq_false_iff_not]; omega)
      have ht : kindTarget (core.readReg .rcx).toNat (core.readReg .rax).toNat = 16 := by simp [kindTarget, h0, hp]
      rw [ht]
      exact ⟨_, _, run_comp e1 e2⟩
    · obtain ⟨f2, e2⟩ := mrun_cmp ce (b := 12) (j := 0) (by decide) (by rw [block_kindArg] <;> rfl) (r := .rax) (c := 0)
        (t := 44) (f := 16) (cond := .ne) (by decide) (by decide) (by rw [block_kindArg] <;> rfl) (core := core) f1
        (taken := true) (by rw [holds_ne _ (by decide)]; simp only [decide_eq_true_eq]; omega)
      have ht : kindTarget (core.readReg .rcx).toNat (core.readReg .rax).toNat = 44 := by simp [kindTarget, h0, hp]
      rw [ht]
      exact ⟨_, _, run_comp e1 e2⟩
  · obtain ⟨f1, e1⟩ := mrun_cmp ce (b := 11) (j := 9) (by decide) (by rw [block_split] <;> rfl) (r := .rcx) (c := 0)
      (t := 12) (f := 13) (cond := .eq) (by decide) (by decide) (by rw [block_split] <;> rfl) (core := core) fl
      (taken := false) (by rw [holds_eq _ (by decide)]; simp only [decide_eq_false_iff_not]; omega)
    by_cases h1 : (core.readReg .rcx).toNat = 1
    · obtain ⟨f2, e2⟩ := mrun_cmp ce (b := 13) (j := 0) (by decide) (by rw [block_kind1] <;> rfl) (r := .rcx) (c := 1)
        (t := 21) (f := 14) (cond := .eq) (by decide) (by decide) (by rw [block_kind1] <;> rfl) (core := core) f1
        (taken := true) (by rw [holds_eq _ (by decide)]; simp only [decide_eq_true_eq]; omega)
      have ht : kindTarget (core.readReg .rcx).toNat (core.readReg .rax).toNat = 21 := by simp [kindTarget, h1]
      rw [ht]
      exact ⟨_, _, run_comp e1 e2⟩
    obtain ⟨f2, e2⟩ := mrun_cmp ce (b := 13) (j := 0) (by decide) (by rw [block_kind1] <;> rfl) (r := .rcx) (c := 1)
      (t := 21) (f := 14) (cond := .eq) (by decide) (by decide) (by rw [block_kind1] <;> rfl) (core := core) f1
      (taken := false) (by rw [holds_eq _ (by decide)]; simp only [decide_eq_false_iff_not]; omega)
    by_cases h2 : (core.readReg .rcx).toNat = 2
    · obtain ⟨f3, e3⟩ := mrun_cmp ce (b := 14) (j := 0) (by decide) (by rw [block_kind2] <;> rfl) (r := .rcx) (c := 2)
        (t := 22) (f := 15) (cond := .eq) (by decide) (by decide) (by rw [block_kind2] <;> rfl) (core := core) f2
        (taken := true) (by rw [holds_eq _ (by decide)]; simp only [decide_eq_true_eq]; omega)
      have ht : kindTarget (core.readReg .rcx).toNat (core.readReg .rax).toNat = 22 := by simp [kindTarget, h2]
      rw [ht]
      exact ⟨_, _, run_comp e1 (run_comp e2 e3)⟩
    obtain ⟨f3, e3⟩ := mrun_cmp ce (b := 14) (j := 0) (by decide) (by rw [block_kind2] <;> rfl) (r := .rcx) (c := 2)
      (t := 22) (f := 15) (cond := .eq) (by decide) (by decide) (by rw [block_kind2] <;> rfl) (core := core) f2
      (taken := false) (by rw [holds_eq _ (by decide)]; simp only [decide_eq_false_iff_not]; omega)
    by_cases h3 : (core.readReg .rcx).toNat = 3
    · obtain ⟨f4, e4⟩ := mrun_cmp ce (b := 15) (j := 0) (by decide) (by rw [block_kind3] <;> rfl) (r := .rcx) (c := 3)
        (t := 26) (f := 44) (cond := .eq) (by decide) (by decide) (by rw [block_kind3] <;> rfl) (core := core) f3
        (taken := true) (by rw [holds_eq _ (by decide)]; simp only [decide_eq_true_eq]; omega)
      have ht : kindTarget (core.readReg .rcx).toNat (core.readReg .rax).toNat = 26 := by simp [kindTarget, h3]
      rw [ht]
      exact ⟨_, _, run_comp e1 (run_comp e2 (run_comp e3 e4))⟩
    · obtain ⟨f4, e4⟩ := mrun_cmp ce (b := 15) (j := 0) (by decide) (by rw [block_kind3] <;> rfl) (r := .rcx) (c := 3)
        (t := 26) (f := 44) (cond := .eq) (by decide) (by decide) (by rw [block_kind3] <;> rfl) (core := core) f3
        (taken := false) (by rw [holds_eq _ (by decide)]; simp only [decide_eq_false_iff_not]; omega)
      have ht : kindTarget (core.readReg .rcx).toNat (core.readReg .rax).toNat = 44 := by
        simp [kindTarget, h0, h1, h2, h3]
      rw [ht]
      exact ⟨_, _, run_comp e1 (run_comp e2 (run_comp e3 e4))⟩

/-- `exitCode` and `exit`: a trace is a prefix of the program's exit with the payload. -/
theorem exitCode_path (core : Core) (fl : ByteEval.Flags) {n : Nat} {σ : List Sys}
    (ht : TraceN ce.checked.bytes n ⟨core, addr ce 26 0, fl⟩ σ) : σ <+: [.exit (core.readReg .rax)] := by
  have e1 := mstep_movR ce (b := 26) (j := 0) (by decide) (d := .rdi) (r := .rax) (by rw [block_exitCode] <;> rfl) core fl
  have e2 := mstep_jmp ce (b := 26) (j := 1) (t := 27) (by decide) (by rw [block_exitCode] <;> rfl)
    (by rw [block_exitCode] <;> rfl) (by decide) (core.setReg .rdi (core.readReg .rax)) fl
  rcases TraceN.through (run_comp (run_one e1) (run_one e2)) ht with rfl | ⟨-, ht'⟩
  · exact List.nil_prefix
  · exact exit_path ce (s := ⟨core.setReg .rdi (core.readReg .rax), addr ce 27 0, fl⟩) rfl ht'

/-- `written`/`notWritten`: the answer stored at `C + 8`, back to `loop`. -/
theorem answer_run {b v : Nat} (hb : b < 46)
    (hblk : blockAt (shellOf ce.checked) b = ⟨#[mI .r10 L.callTop, mI .rax v, st (at_ .r10 8) .rax], jmp 6⟩)
    (core : Core) (fl : ByteEval.Flags) :
    FaultsWithin ce.checked.bytes ⟨core, addr ce b 0, fl⟩ 3 ∨
    ∃ core', ByteEval.run ce.checked.bytes fetchBase 4 ⟨core, addr ce b 0, fl⟩ = .ok ⟨core', addr ce 6 0, fl⟩ ∧
      core'.memory = core.memory.write .w64 (cTop L + UInt64.ofNat 8) (UInt64.ofNat v) := by
  have e1 := mstep_movI ce (b := b) (j := 0) hb (r := .r10) (v := L.callTop) (by rw [hblk] <;> rfl) core fl
  let k1 := core.setReg .r10 (UInt64.ofNat L.callTop)
  have e2 := mstep_movI ce (b := b) (j := 1) hb (r := .rax) (v := v) (by rw [hblk] <;> rfl) k1 fl
  let k2 := k1.setReg .rax (UInt64.ofNat v)
  have hA : (SB.at_ .r10 8).eval k2 = cTop L + UInt64.ofNat 8 := eval_at k2 .r10 (by decide)
  rcases mstep_store ce (b := b) (j := 2) hb (w := .w64) (A := SB.at_ .r10 8) (r := .rax) (by rw [hblk] <;> rfl) (.inl rfl)
    k2 fl hA with ⟨f, hf⟩ | e3
  · exact .inl ⟨2, by decide, ⟨k2, addr ce b 2, fl⟩, f, run_comp (run_one e1) (run_one e2), hf⟩
  · right
    have e4 := mstep_jmp ce (b := b) (j := 3) (t := 6) hb (by rw [hblk] <;> rfl) (by rw [hblk] <;> rfl) (by decide)
      { k2 with memory := k2.memory.write .w64 (cTop L + UInt64.ofNat 8) (k2.readReg .rax) } fl
    exact ⟨_, run_comp (run_one e1) (run_comp (run_one e2) (run_comp (run_one e3) (run_one e4))), rfl⟩

set_option maxRecDepth 20000 in
/-- **A one-byte write** (`out`/`err`, `write1`, then `written` or `notWritten`): a trace is
empty, or the write of the payload's byte to `fd`, then empty or a trace from `loop` with the answer
stored. -/
theorem write_path (fd : Nat) (hfd : fd = 1 ∨ fd = 2) (core : Core) (fl : ByteEval.Flags) {n : Nat} {σ : List Sys}
    (ht : TraceN ce.checked.bytes n ⟨core, addr ce (20 + fd) 0, fl⟩ σ) :
    σ = [] ∨ ∃ r σ', σ = .write (UInt64.ofNat fd) [UInt8.ofNat (core.readReg .rax).toNat] r :: σ' ∧
      (σ' = [] ∨ ∃ s' n', n' < n ∧ TraceN ce.checked.bytes n' s' σ' ∧ s'.rip = addr ce 6 0 ∧
        s'.core.memory = (core.memory.write .w8 (cTop L + UInt64.ofNat 32) (core.readReg .rax)).write .w64
          (cTop L + UInt64.ofNat 8) (UInt64.ofNat (if r.toNat = 1 then 0 else 1))) := by
  have hb : 20 + fd < 46 := by omega
  have hblk : blockAt (shellOf ce.checked) (20 + fd) = ⟨#[mI .rdi fd], jmp 23⟩ := by
    rcases hfd with rfl | rfl
    · exact block_out L step _
    · exact block_err L step _
  have e1 := mstep_movI ce (b := 20 + fd) (j := 0) hb (r := .rdi) (v := fd) (by rw [hblk] <;> rfl) core fl
  let k1 := core.setReg .rdi (UInt64.ofNat fd)
  have e2 := mstep_jmp ce (b := 20 + fd) (j := 1) (t := 23) hb (by rw [hblk] <;> rfl) (by rw [hblk] <;> rfl) (by decide) k1 fl
  have e3 := mstep_movI ce (b := 23) (j := 0) (by decide) (r := .r10) (v := L.callTop) (by rw [block_write1] <;> rfl) k1 fl
  let k2 := k1.setReg .r10 (UInt64.ofNat L.callTop)
  have hA : (SB.at_ .r10 32).eval k2 = cTop L + UInt64.ofNat 32 := eval_at k2 .r10 (by decide)
  have hpre : ByteEval.run ce.checked.bytes fetchBase 3 ⟨core, addr ce (20 + fd) 0, fl⟩ = .ok ⟨k2, addr ce 23 1, fl⟩ :=
    run_comp (run_one e1) (run_comp (run_one e2) (run_one e3))
  rcases mstep_store ce (b := 23) (j := 1) (by decide) (w := .w8) (A := SB.at_ .r10 32) (r := .rax)
    (by rw [block_write1] <;> rfl) (.inr rfl) k2 fl hA with ⟨f, hf⟩ | e4
  · exact .inl (TraceN.nil_of_faults (n' := 4) ⟨3, by decide, ⟨k2, addr ce 23 1, fl⟩, f, hpre, hf⟩ ht)
  let k3 : Core := { k2 with memory := k2.memory.write .w8 (cTop L + UInt64.ofNat 32) (k2.readReg .rax) }
  have e5 : ByteEval.step ce.checked.bytes fetchBase ⟨k3, addr ce 23 2, fl⟩ =
      .ok ⟨k3.setReg .rsi ((SB.at_ .r10 32).eval k3), addr ce 23 3, fl⟩ :=
    mstep_ok ce (b := 23) (j := 2) (by decide) (s := ⟨k3, addr ce 23 2, fl⟩) (i := Instr.lea .rsi (SB.at_ .r10 32))
      (by rw [block_write1] <;> rfl) (ne_call_of_op ⟨_, _, rfl⟩) rfl (exec_lea _ _ _ _)
  let k4 := k3.setReg .rsi ((SB.at_ .r10 32).eval k3)
  have e6 := mstep_movI ce (b := 23) (j := 3) (by decide) (r := .rdx) (v := 1) (by rw [block_write1] <;> rfl) k4 fl
  let k5 := k4.setReg .rdx (UInt64.ofNat 1)
  have e7 := mstep_movI ce (b := 23) (j := 4) (by decide) (r := .rax) (v := 1) (by rw [block_write1] <;> rfl) k5 fl
  let k6 := k5.setReg .rax (UInt64.ofNat 1)
  have hrun : ByteEval.run ce.checked.bytes fetchBase 7 ⟨core, addr ce (20 + fd) 0, fl⟩ = .ok ⟨k6, addr ce 23 5, fl⟩ :=
    run_comp hpre (run_comp (run_one e4) (run_comp (run_one e5) (run_comp (run_one e6) (run_one e7))))
  obtain ⟨hd, hb, hnext⟩ := msyscall_at ce (b := 23) (j := 5) (by decide) (by rw [block_write1] <;> rfl)
    (s := ⟨k6, addr ce 23 5, fl⟩) rfl
  rcases TraceN.through hrun ht with rfl | ⟨hn7, ht'⟩
  · exact .inl rfl
  rcases TraceN.write (s := ⟨k6, addr ce 23 5, fl⟩) hd hb rfl ht' with rfl | ⟨r, rcx, r11, fl', σ', rfl, -, hn1, ht''⟩
  · exact .inl rfl
  right
  have hk4 : k4.readReg .rsi = cTop L + UInt64.ofNat 32 := eval_at k3 .r10 (by decide)
  have hev : Sys.write (k6.readReg .rdi) (slice k6.memory (k6.readReg .rsi) (k6.readReg .rdx).toNat) r =
      .write (UInt64.ofNat fd) [UInt8.ofNat (core.readReg .rax).toNat] r := by
    show Sys.write (UInt64.ofNat fd) (slice k3.memory (k4.readReg .rsi) (UInt64.ofNat 1).toNat) r = _
    rw [hk4, show (UInt64.ofNat 1).toNat = 1 from rfl]
    show Sys.write _ [(core.memory.writeLittle (cTop L + UInt64.ofNat 32) (core.readReg .rax) 1).bytes
      (cTop L + UInt64.ofNat 32 + UInt64.ofNat 0)] r = _
    rw [Memory.writeLittle_bytes _ _ _ (by decide) (by decide), byte_of]
  refine ⟨r, σ', congrArg (· :: σ') hev, ?_⟩
  let s7 := returned ⟨k6, addr ce 23 5, fl⟩ r rcx r11 fl'
  have h7rip : s7.rip = addr ce 23 6 := hnext
  have h7 : ∃ m b fl₇, ByteEval.run ce.checked.bytes fetchBase m s7 = .ok ⟨s7.core, addr ce b 0, fl₇⟩ ∧
      blockAt (shellOf ce.checked) b = ⟨#[mI .r10 L.callTop, mI .rax (if r.toNat = 1 then 0 else 1),
        st (at_ .r10 8) .rax], jmp 6⟩ ∧ b < 46 := by
    by_cases h1 : r.toNat = 1
    · obtain ⟨f8, e8⟩ := mrun_cmp ce (b := 23) (j := 6) (by decide) (by rw [block_write1] <;> rfl) (r := .rax) (c := 1)
        (t := 24) (f := 25) (cond := .eq) (by decide) (by decide) (by rw [block_write1] <;> rfl) (core := s7.core) s7.flags
        (taken := true) (by rw [holds_eq _ (by decide)]; simp only [decide_eq_true_eq]; exact h1)
      refine ⟨_, 24, f8, by rw [← h7rip] at e8; exact e8, ?_, by decide⟩
      rw [ite_eq_left h1]
      exact block_written L step _
    · obtain ⟨f8, e8⟩ := mrun_cmp ce (b := 23) (j := 6) (by decide) (by rw [block_write1] <;> rfl) (r := .rax) (c := 1)
        (t := 24) (f := 25) (cond := .eq) (by decide) (by decide) (by rw [block_write1] <;> rfl) (core := s7.core) s7.flags
        (taken := false) (by rw [holds_eq _ (by decide)]; simp only [decide_eq_false_iff_not]; exact h1)
      refine ⟨_, 25, f8, by rw [← h7rip] at e8; exact e8, ?_, by decide⟩
      rw [ite_eq_right h1]
      exact block_notWritten L step _
  obtain ⟨m8, b8, f8, e8, hblk8, hb8⟩ := h7
  rcases TraceN.through e8 ht'' with rfl | ⟨hm8, ht3⟩
  · exact .inl rfl
  rcases answer_run ce hb8 hblk8 s7.core f8 with hf | ⟨core', e9, hmem⟩
  · exact .inl (TraceN.nil_of_faults hf ht3)
  rcases TraceN.through e9 ht3 with rfl | ⟨hm9, ht4⟩
  · exact .inl rfl
  refine .inr ⟨_, _, by omega, ht4, rfl, ?_⟩
  rw [hmem]
  rfl

/-- The `arg` block up to its test: the argument slot `[C + 16]` in `r11`, the word it points at in `rsi`. -/
theorem arg_head (core : Core) (fl : ByteEval.Flags) :
    FaultsWithin ce.checked.bytes ⟨core, addr ce 16 0, fl⟩ 3 ∨
    ∃ core', ByteEval.run ce.checked.bytes fetchBase 3 ⟨core, addr ce 16 0, fl⟩ = .ok ⟨core', addr ce 16 3, fl⟩ ∧
      core'.memory = core.memory ∧ core'.readReg .r10 = cTop L ∧
      core'.readReg .r11 = core.memory.read64 (cTop L + UInt64.ofNat 16) ∧
      core'.readReg .rsi = core.memory.read64 (core.memory.read64 (cTop L + UInt64.ofNat 16)) := by
  have e1 := mstep_movI ce (b := 16) (j := 0) (by decide) (r := .r10) (v := L.callTop) (by rw [block_arg] <;> rfl) core fl
  let k1 := core.setReg .r10 (UInt64.ofNat L.callTop)
  rcases mstep_load ce (b := 16) (j := 1) (by decide) (r := .r11) (A := SB.at_ .r10 16) (by rw [block_arg] <;> rfl) k1 fl
    (eval_at k1 .r10 (by decide)) with ⟨f, hf⟩ | e2
  · exact .inl ⟨1, by decide, _, f, run_one e1, hf⟩
  let k2 := k1.setReg .r11 (k1.memory.read64 (cTop L + UInt64.ofNat 16))
  rcases mstep_load ce (b := 16) (j := 2) (by decide) (r := .rsi) (A := SB.at_ .r11) (by rw [block_arg] <;> rfl) k2 fl
    (a := k2.readReg .r11) (by rw [eval_at k2 .r11 (by decide), add_zero']) with ⟨f, hf⟩ | e3
  · exact .inl ⟨2, by decide, _, f, run_comp (run_one e1) (run_one e2), hf⟩
  exact .inr ⟨_, run_comp (run_one e1) (run_comp (run_one e2) (run_one e3)), rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 20000 in
/-- `noMore`: the answer 257 stored at `C + 8`, back to `loop`. -/
theorem noMore_run (core : Core) (fl : ByteEval.Flags) (h10 : core.readReg .r10 = cTop L) :
    FaultsWithin ce.checked.bytes ⟨core, addr ce 17 0, fl⟩ 2 ∨
    ∃ core', ByteEval.run ce.checked.bytes fetchBase 3 ⟨core, addr ce 17 0, fl⟩ = .ok ⟨core', addr ce 6 0, fl⟩ ∧
      core'.memory = core.memory.write .w64 (cTop L + UInt64.ofNat 8) (UInt64.ofNat 257) := by
  have e1 := mstep_movI ce (b := 17) (j := 0) (by decide) (r := .rax) (v := 257) (by rw [block_noMore] <;> rfl) core fl
  let k1 := core.setReg .rax (UInt64.ofNat 257)
  rcases mstep_store ce (b := 17) (j := 1) (by decide) (w := .w64) (A := SB.at_ .r10 8) (r := .rax)
    (by rw [block_noMore] <;> rfl) (.inl rfl) k1 fl (by rw [eval_at k1 .r10 (by decide), show k1.readReg .r10 = cTop L from h10])
    with ⟨f, hf⟩ | e2
  · exact .inl ⟨1, by decide, _, f, run_one e1, hf⟩
  · have e3 := mstep_jmp ce (b := 17) (j := 2) (t := 6) (by decide) (by rw [block_noMore] <;> rfl) (by rw [block_noMore] <;> rfl)
      (by decide) { k1 with memory := k1.memory.write .w64 (cTop L + UInt64.ofNat 8) (k1.readReg .rax) } fl
    exact .inr ⟨_, run_comp (run_one e1) (run_comp (run_one e2) (run_one e3)), rfl⟩

/-- `argByte` up to its test: the byte pointer `[C + 24]` in `rsi`, the byte it points at in `rax`. -/
theorem argByte_run (core : Core) (fl : ByteEval.Flags) (h10 : core.readReg .r10 = cTop L) :
    FaultsWithin ce.checked.bytes ⟨core, addr ce 18 0, fl⟩ 2 ∨
    ∃ core', ByteEval.run ce.checked.bytes fetchBase 2 ⟨core, addr ce 18 0, fl⟩ = .ok ⟨core', addr ce 18 2, fl⟩ ∧
      core'.memory = core.memory ∧ core'.readReg .r10 = cTop L ∧ core'.readReg .r11 = core.readReg .r11 ∧
      core'.readReg .rsi = core.memory.read64 (cTop L + UInt64.ofNat 24) ∧
      (core'.readReg .rax).toNat = (core.memory.bytes (core.memory.read64 (cTop L + UInt64.ofNat 24))).toNat := by
  rcases mstep_load ce (b := 18) (j := 0) (by decide) (r := .rsi) (A := SB.at_ .r10 24) (by rw [block_argByte] <;> rfl) core fl
    (by rw [eval_at core .r10 (by decide), h10]) with ⟨f, hf⟩ | e1
  · exact .inl ⟨0, by decide, _, f, rfl, hf⟩
  let k1 := core.setReg .rsi (core.memory.read64 (cTop L + UInt64.ofNat 24))
  rcases mstep_load8 ce (b := 18) (j := 1) (by decide) (r := .rax) (A := SB.at_ .rsi) (by rw [block_argByte] <;> rfl) k1 fl
    (a := k1.readReg .rsi) (by rw [eval_at k1 .rsi (by decide), add_zero']) with ⟨f, hf⟩ | e2
  · exact .inl ⟨1, by decide, _, f, run_one e1, hf⟩
  exact .inr ⟨_, run_comp (run_one e1) (run_one e2), rfl, h10, rfl, rfl, load8_toNat _ _⟩

set_option maxRecDepth 20000 in
/-- `argNext`: the byte pointer moved on by one at `C + 24`, the byte stored at `C + 8`, back to `loop`. -/
theorem argNext_run (core : Core) (fl : ByteEval.Flags) (h10 : core.readReg .r10 = cTop L) :
    FaultsWithin ce.checked.bytes ⟨core, addr ce 19 0, fl⟩ 3 ∨
    ∃ core' fl', ByteEval.run ce.checked.bytes fetchBase 4 ⟨core, addr ce 19 0, fl⟩ = .ok ⟨core', addr ce 6 0, fl'⟩ ∧
      core'.memory = (core.memory.write .w64 (cTop L + UInt64.ofNat 24) (core.readReg .rsi + UInt64.ofNat 1)).write .w64
        (cTop L + UInt64.ofNat 8) (core.readReg .rax) := by
  obtain ⟨f1, e1⟩ := mstep_alu ce (b := 19) (j := 0) (by decide) (op := .add) (w := .w64) (r := .rsi)
    (src := .imm (UInt32.ofNat 1)) (by rw [block_argNext] <;> rfl) (ne_call_of_op ⟨_, _, rfl⟩) core fl
  let k1 := core.writeReg .w64 .rsi (AluOp.add.eval (core.readReg .rsi) ((AluSource.imm (UInt32.ofNat 1)).eval core))
  have hk1 : k1.readReg .rsi = core.readReg .rsi + UInt64.ofNat 1 := by
    show core.readReg .rsi + signExtend32 (UInt32.ofNat 1) = _
    rw [show signExtend32 (UInt32.ofNat 1) = UInt64.ofNat 1 by decide]
  rcases mstep_store ce (b := 19) (j := 1) (by decide) (w := .w64) (A := SB.at_ .r10 24) (r := .rsi)
    (by rw [block_argNext] <;> rfl) (.inl rfl) k1 f1 (by rw [eval_at k1 .r10 (by decide), show k1.readReg .r10 = cTop L from h10])
    with ⟨f, hf⟩ | e2
  · exact .inl ⟨1, by decide, _, f, run_one e1, hf⟩
  let k2 : Core := { k1 with memory := k1.memory.write .w64 (cTop L + UInt64.ofNat 24) (k1.readReg .rsi) }
  rcases mstep_store ce (b := 19) (j := 2) (by decide) (w := .w64) (A := SB.at_ .r10 8) (r := .rax)
    (by rw [block_argNext] <;> rfl) (.inl rfl) k2 f1 (by rw [eval_at k2 .r10 (by decide), show k2.readReg .r10 = cTop L from h10])
    with ⟨f, hf⟩ | e3
  · exact .inl ⟨2, by decide, _, f, run_comp (run_one e1) (run_one e2), hf⟩
  have e4 := mstep_jmp ce (b := 19) (j := 3) (t := 6) (by decide) (by rw [block_argNext] <;> rfl) (by rw [block_argNext] <;> rfl)
    (by decide) { k2 with memory := k2.memory.write .w64 (cTop L + UInt64.ofNat 8) (k2.readReg .rax) } f1
  refine .inr ⟨_, _, run_comp (run_one e1) (run_comp (run_one e2) (run_comp (run_one e3) (run_one e4))), ?_⟩
  show (core.memory.write .w64 (cTop L + UInt64.ofNat 24) (k1.readReg .rsi)).write .w64 _ _ = _
  rw [hk1]
  rfl

set_option maxRecDepth 20000 in
/-- `argEnd`: the answer 256 at `C + 8`, the next slot at `C + 16` and its word at `C + 24`, back to `loop`. -/
theorem argEnd_run (core : Core) (fl : ByteEval.Flags) (h10 : core.readReg .r10 = cTop L) :
    FaultsWithin ce.checked.bytes ⟨core, addr ce 20 0, fl⟩ 6 ∨
    ∃ core' fl', ByteEval.run ce.checked.bytes fetchBase 7 ⟨core, addr ce 20 0, fl⟩ = .ok ⟨core', addr ce 6 0, fl'⟩ ∧
      core'.memory = ((core.memory.write .w64 (cTop L + UInt64.ofNat 8) (UInt64.ofNat 256)).write .w64
        (cTop L + UInt64.ofNat 16) (core.readReg .r11 + UInt64.ofNat 8)).write .w64 (cTop L + UInt64.ofNat 24)
        (((core.memory.write .w64 (cTop L + UInt64.ofNat 8) (UInt64.ofNat 256)).write .w64
          (cTop L + UInt64.ofNat 16) (core.readReg .r11 + UInt64.ofNat 8)).read64 (core.readReg .r11 + UInt64.ofNat 8)) := by
  have e1 := mstep_movI ce (b := 20) (j := 0) (by decide) (r := .rax) (v := 256) (by rw [block_argEnd] <;> rfl) core fl
  let k1 := core.setReg .rax (UInt64.ofNat 256)
  rcases mstep_store ce (b := 20) (j := 1) (by decide) (w := .w64) (A := SB.at_ .r10 8) (r := .rax)
    (by rw [block_argEnd] <;> rfl) (.inl rfl) k1 fl (by rw [eval_at k1 .r10 (by decide), show k1.readReg .r10 = cTop L from h10])
    with ⟨f, hf⟩ | e2
  · exact .inl ⟨1, by decide, _, f, run_one e1, hf⟩
  let k2 : Core := { k1 with memory := k1.memory.write .w64 (cTop L + UInt64.ofNat 8) (k1.readReg .rax) }
  obtain ⟨f3, e3⟩ := mstep_alu ce (b := 20) (j := 2) (by decide) (op := .add) (w := .w64) (r := .r11)
    (src := .imm (UInt32.ofNat 8)) (by rw [block_argEnd] <;> rfl) (ne_call_of_op ⟨_, _, rfl⟩) k2 fl
  let k3 := k2.writeReg .w64 .r11 (AluOp.add.eval (k2.readReg .r11) ((AluSource.imm (UInt32.ofNat 8)).eval k2))
  have hk3 : k3.readReg .r11 = core.readReg .r11 + UInt64.ofNat 8 := by
    show core.readReg .r11 + signExtend32 (UInt32.ofNat 8) = _
    rw [show signExtend32 (UInt32.ofNat 8) = UInt64.ofNat 8 by decide]
  rcases mstep_store ce (b := 20) (j := 3) (by decide) (w := .w64) (A := SB.at_ .r10 16) (r := .r11)
    (by rw [block_argEnd] <;> rfl) (.inl rfl) k3 f3 (by rw [eval_at k3 .r10 (by decide), show k3.readReg .r10 = cTop L from h10])
    with ⟨f, hf⟩ | e4
  · exact .inl ⟨3, by decide, _, f, run_comp (run_one e1) (run_comp (run_one e2) (run_one e3)), hf⟩
  let k4 : Core := { k3 with memory := k3.memory.write .w64 (cTop L + UInt64.ofNat 16) (k3.readReg .r11) }
  rcases mstep_load ce (b := 20) (j := 4) (by decide) (r := .rcx) (A := SB.at_ .r11) (by rw [block_argEnd] <;> rfl) k4 f3
    (a := k4.readReg .r11) (by rw [eval_at k4 .r11 (by decide), add_zero']) with ⟨f, hf⟩ | e5
  · exact .inl ⟨4, by decide, _, f, run_comp (run_one e1) (run_comp (run_one e2) (run_comp (run_one e3) (run_one e4))), hf⟩
  let k5 := k4.setReg .rcx (k4.memory.read64 (k4.readReg .r11))
  rcases mstep_store ce (b := 20) (j := 5) (by decide) (w := .w64) (A := SB.at_ .r10 24) (r := .rcx)
    (by rw [block_argEnd] <;> rfl) (.inl rfl) k5 f3 (by rw [eval_at k5 .r10 (by decide), show k5.readReg .r10 = cTop L from h10])
    with ⟨f, hf⟩ | e6
  · exact .inl ⟨5, by decide, _, f, run_comp (run_one e1) (run_comp (run_one e2) (run_comp (run_one e3)
      (run_comp (run_one e4) (run_one e5)))), hf⟩
  have e7 := mstep_jmp ce (b := 20) (j := 6) (t := 6) (by decide) (by rw [block_argEnd] <;> rfl) (by rw [block_argEnd] <;> rfl)
    (by decide) { k5 with memory := k5.memory.write .w64 (cTop L + UInt64.ofNat 24) (k5.readReg .rcx) } f3
  refine .inr ⟨_, _, run_comp (run_one e1) (run_comp (run_one e2) (run_comp (run_one e3) (run_comp (run_one e4)
    (run_comp (run_one e5) (run_comp (run_one e6) (run_one e7)))))), ?_⟩
  show (k4.memory).write .w64 (cTop L + UInt64.ofNat 24) (k4.memory.read64 (k4.readReg .r11)) = _
  show ((core.memory.write .w64 (cTop L + UInt64.ofNat 8) (UInt64.ofNat 256)).write .w64 (cTop L + UInt64.ofNat 16)
    (k3.readReg .r11)).write .w64 _ (((core.memory.write .w64 (cTop L + UInt64.ofNat 8) (UInt64.ofNat 256)).write .w64
      (cTop L + UInt64.ofNat 16) (k3.readReg .r11)).read64 (k3.readReg .r11)) = _
  rw [hk3]

end

end IxCC.X86.Exe.Process
