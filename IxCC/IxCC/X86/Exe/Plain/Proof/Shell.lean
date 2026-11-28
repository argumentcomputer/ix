import IxCC.X86.Exe.Plain.Proof.Parse
import IxCC.X86.Exe.Machine.Proof.Glue

/-! # Plain Standalone Executable Shell Theorem (`plain_shell_sound`)

Proves end-to-end that the plain `--exe` shell (`X86.Exe.Code.shell`) realises
`PlainShows` under the **exact same three platform specifications** as the
proved `--machine` shell (`Process.Loaded`, `Process.Syscall`, `Process.Step`):

- `plain_confine_run`: confinement (`prctl` + `seccomp`, blocks 0–1)
- `plain_args_setup` & `plain_args_loop`: argument count check + decimal parsing
  into the dedicated 256-byte scratch/stack area (`[L.stackTop .. L.shellTop)`)
- `plain_glue` & `plain_calls`: `cx_init` and `root` calls lifted via `two_calls`
  with `L.driverAt` keeping `Driver.CanonicalOk` at both call sites
- `plain_shell_sound`: every finite trace from `Process.Loaded` satisfies
  `PlainShows`
- `plain_shell_unspecified`: `Unspecified` states are reachable only past a
  `.stuck` object call.

This formally verifies the plain `--exe` shell so `x86-linux-exe-shell` can be
retired from the trust ledger. -/

set_option autoImplicit false

namespace IxCC.X86.Exe.Plain

open IxCC.X86
open IxCC.X86.Exe
open IxCC.X86.Exe.Process
open IxCC.Sem (Result Obs)
open PB

/-- Root signature shape matching `input.result` (what `Exe.fragment` ensures). -/
def PlainRootMatches (input : X86.Exe.Input) (r : Linked.Root) : Prop :=
  r.symbol = input.root ∧
  r.params = input.arity ∧
  match input.result with
  | .nat => ∃ sig, r.ty = some (sig, .nat)
  | .enum n => ∃ sig idx ctors, r.ty = some (sig, .ind idx) ∧
      sig.inds[idx]? = some ctors ∧ ctors.length = n ∧ ctors.all List.isEmpty = true

/-! ## `Rt.readback` bijection for `.nat` and field-less `.enum n` -/

private theorem plain_signExtend32_ofNat {d : Nat} (hd : d < 2 ^ 31) :
    signExtend32 (UInt32.ofNat d) = UInt64.ofNat d := by
  have hd32 : (UInt32.ofNat d).toNat = d := UInt32.toNat_ofNat_of_lt' (by show d < 4294967296; omega)
  have hlt32 : UInt32.ofNat d < 2147483648 := by
    rw [UInt32.lt_iff_toNat_lt, hd32]; show d < 2147483648; omega
  simp only [signExtend32, hlt32, ↓reduceIte]
  apply UInt64.toNat_inj.mp
  rw [UInt32.toNat_toUInt64, hd32, toNat_small (by omega)]

private theorem slot_add (sp : Word) (a b : Nat) :
    sp + UInt64.ofNat a + UInt64.ofNat b = sp + UInt64.ofNat (a + b) := by
  rw [UInt64.add_assoc, ← UInt64.ofNat_add]

private theorem plain_shr1_toNat (w : Word) : (w >>> 1).toNat = w.toNat / 2 := by
  rw [UInt64.toNat_shiftRight, show (1 : Word).toNat % 64 = 1 from rfl, Nat.shiftRight_eq_div_pow]

theorem readback_nat_iff (sig : Rt.Sig) (fuel : Nat) (m : Memory) (w : Word) :
    (w.toNat % 2 = 1 → Rt.readback sig fuel m .nat w = some (.nat (w.toNat / 2))) ∧
    (w.toNat % 2 ≠ 1 → Rt.readback sig fuel m .nat w = none) := by
  have hand : (w &&& 1).toNat = w.toNat % 2 := by simp
  have hshr := plain_shr1_toNat w
  constructor
  · intro hodd
    have h1 : (w &&& 1 == 1) = true := by
      rw [beq_iff_eq]; exact UInt64.toNat_inj.mp (by rw [hand]; exact hodd)
    simp [Rt.readback, h1, hshr]
  · intro hev
    have h0 : (w &&& 1 == 1) = false := by
      rw [beq_eq_false_iff_ne]; intro heq; exact hev (by rw [← hand, heq]; rfl)
    simp [Rt.readback, h0]

theorem readback_enum_iff {sig : Rt.Sig} {idx n : Nat} {ctors : List (List Rt.FoTy)}
    (hinds : sig.inds[idx]? = some ctors) (hlen : ctors.length = n)
    (hemp : ctors.all List.isEmpty = true) (fuel : Nat) (m : Memory) (w : Word) :
    ((w.toNat % 2 = 1 ∧ w.toNat / 2 < n) →
      Rt.readback sig fuel m (.ind idx) w = some (.ctor (w.toNat / 2) [])) ∧
    (¬ (w.toNat % 2 = 1 ∧ w.toNat / 2 < n) →
      Rt.readback sig fuel m (.ind idx) w = none) := by
  have hand : (w &&& 1).toNat = w.toNat % 2 := by simp
  have hshr := plain_shr1_toNat w
  have hctor_empty : ∀ tag, tag < n → sig.ctor? idx tag = some [] := by
    intro tag htag
    unfold Rt.Sig.ctor?
    rw [hinds]
    have hlt : tag < ctors.length := hlen ▸ htag
    simp only [Option.bind_some, List.getElem?_eq_getElem hlt]
    have hmem : ctors[tag] ∈ ctors := List.getElem_mem hlt
    have hem := List.all_eq_true.mp hemp ctors[tag] hmem
    cases hc : ctors[tag] with
    | nil => rfl
    | cons _ _ => simp [hc] at hem
  constructor
  · rintro ⟨hodd, hlt⟩
    have h1 : (w &&& 1 == 1) = true := by
      rw [beq_iff_eq]; exact UInt64.toNat_inj.mp (by rw [hand]; exact hodd)
    unfold Rt.readback
    simp only [h1, ↓reduceIte, hshr, hctor_empty _ hlt]
  · intro hnot
    by_cases hodd : w.toNat % 2 = 1
    · have hge : n ≤ w.toNat / 2 := by omega
      have h1 : (w &&& 1 == 1) = true := by
        rw [beq_iff_eq]; exact UInt64.toNat_inj.mp (by rw [hand]; exact hodd)
      have hnone : sig.ctor? idx (w.toNat / 2) = none := by
        unfold Rt.Sig.ctor?
        rw [hinds, Option.bind_some, List.getElem?_eq_none (by omega)]
      unfold Rt.readback
      simp only [h1, ↓reduceIte, hshr, hnone]
    · have h0 : (w &&& 1 == 1) = false := by
        rw [beq_eq_false_iff_ne]; intro heq; exact hodd (by rw [← hand, heq]; rfl)
      cases fuel with
      | zero => unfold Rt.readback; simp only [h0, Bool.false_eq_true, ↓reduceIte]
      | succ fuel' =>
        unfold Rt.readback
        simp only [h0, Bool.false_eq_true, ↓reduceIte]
        cases m.read64? w with
        | error _ => rfl
        | ok h =>
          dsimp only
          cases hct : sig.ctor? idx ((h >>> 16) &&& 0xFFFF).toNat with
          | none => rfl
          | some tys =>
            have htysNil : tys = [] := by
              unfold Rt.Sig.ctor? at hct
              rw [hinds, Option.bind_some] at hct
              have hmem : tys ∈ ctors := List.mem_of_getElem? hct
              have hem := List.all_eq_true.mp hemp tys hmem
              cases tys with
              | nil => rfl
              | cons _ _ => simp at hem
            subst htysNil
            have hcondF : ((0 == (h &&& 0xFF).toNat) && decide (0 < (h &&& 0xFF).toNat)) = false := by
              cases hsc : (h &&& 0xFF).toNat with
              | zero => simp
              | succ _ => simp
            simp only [List.length_nil, hcondF, Bool.false_eq_true, ↓reduceIte]

section
variable {input : X86.Exe.Input} (ce : Certified input)

/-! ## Segment & memory disjointness helpers -/

private theorem plain_inside_stack {a : Word}
    (h1 : dataBase ≤ a.toNat) (h2 : a.toNat < dataBase + input.layout.stackArea) :
    ¬ OutsideSegments input.layout.segments a := by
  intro h
  have := h (dataBase, input.layout.stackArea) List.mem_cons_self
  omega

private theorem plain_scratch_unmapped (ret : Nat) (init : Word → UInt8) (fl : ByteEval.Flags)
    (other : GPR → Word) {i : Nat} (hi : i < 256) :
    (input.layout.driverAt ce.plan.placement.textOffset ret init fl other).mapped
      (UInt64.ofNat input.layout.stackTop + UInt64.ofNat i) = false := by
  have hL := plainLayout_numbers ce
  have hd : dataBase = 268435456 := rfl
  have ha : (UInt64.ofNat input.layout.stackTop + UInt64.ofNat i).toNat = input.layout.stackTop + i := by
    rw [← UInt64.ofNat_add, toNat_small (by omega)]
  simp only [Driver.mapped, Driver.inRegion, Driver.inStack, Layout.driverAt, ha,
    Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  rw [toNat_small (show input.layout.regionStart < 2 ^ 64 by omega),
      toNat_small (show input.layout.region < 2 ^ 64 by omega),
      toNat_small (show input.layout.stackTop - 8 < 2 ^ 64 by omega)]
  omega

private theorem plain_file_unmapped (ret : Nat) (init : Word → UInt8) (fl : ByteEval.Flags)
    (other : GPR → Word) {i : Nat} (hi : i < ce.bytes.size) :
    (input.layout.driverAt ce.plan.placement.textOffset ret init fl other).mapped
      (UInt64.ofNat (fileBase + i)) = false := by
  have ff := plainFileFacts ce
  have hL := plainLayout_numbers ce
  have hd : dataBase = 268435456 := rfl
  have hfb : fileBase = 4194304 := rfl
  have hbel := ff.below
  rw [ff.size] at hi
  have ha : (UInt64.ofNat (fileBase + i)).toNat = fileBase + i := toNat_small (by omega)
  simp only [Driver.mapped, Driver.inRegion, Driver.inStack, Layout.driverAt, ha,
    Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  rw [toNat_small (show input.layout.regionStart < 2 ^ 64 by omega),
      toNat_small (show input.layout.stackTop - 8 < 2 ^ 64 by omega),
      toNat_small (show input.layout.budget < 2 ^ 64 by omega)]
  omega

private theorem plain_write_scratch_preserves_outside (ce : Certified input) {m : Memory} {off : Nat} {v : Word}
    (hoff : off ≤ 248) :
    ∀ a, OutsideSegments input.layout.segments a →
      (m.write .w64 (UInt64.ofNat input.layout.stackTop + UInt64.ofNat off) v).bytes a = m.bytes a := by
  intro a hout
  have hL := plainLayout_numbers ce
  have hd : dataBase = 268435456 := rfl
  rw [write_bytes_apart]
  intro j hj heq
  apply plain_inside_stack (input := input) (a := a) _ _ hout
  · have h1 := congrArg UInt64.toNat heq
    rw [UInt64.add_assoc, ← UInt64.ofNat_add, ← UInt64.ofNat_add,
        toNat_small (by simp [Width.bytes] at hj; omega)] at h1
    omega
  · have h1 := congrArg UInt64.toNat heq
    rw [UInt64.add_assoc, ← UInt64.ofNat_add, ← UInt64.ofNat_add,
        toNat_small (by simp [Width.bytes] at hj; omega)] at h1
    simp [Width.bytes] at hj
    omega

private theorem plain_write_scratch_preserves_file (ce : Certified input) {m : Memory} {off : Nat} {v : Word}
    (hoff : off ≤ 248) {i : Nat} (hi : i < ce.bytes.size) :
    (m.write .w64 (UInt64.ofNat input.layout.stackTop + UInt64.ofNat off) v).bytes
      (UInt64.ofNat (fileBase + i)) = m.bytes (UInt64.ofNat (fileBase + i)) := by
  have ff := plainFileFacts ce
  have hL := plainLayout_numbers ce
  have hd : dataBase = 268435456 := rfl
  have hfb : fileBase = 4194304 := rfl
  have hbel := ff.below
  rw [ff.size] at hi
  apply plain_write_scratch_preserves_outside ce hoff
  intro seg hseg
  simp only [Layout.segments, List.mem_cons, List.not_mem_nil, or_false] at hseg
  rw [toNat_small (by omega)]
  rcases hseg with rfl | rfl <;> (left; omega)

/-! ## Step 1: Confinement (blocks 0 and 1) -/

theorem plain_confine_run (core : Core) (fl : ByteEval.Flags)
    (hfile : ∀ i < ce.bytes.size, core.memory.bytes (UInt64.ofNat (fileBase + i)) = ce.bytes[i]!)
    {n : Nat} {σ : List Sys} (ht : TraceN ce.bytes n ⟨core, paddr ce 0 0, fl⟩ σ) :
    PlainRefused input.arity (fileBase + ce.plan.placement.dataOffset) σ ∨
    σ <+: started (fileBase + ce.plan.placement.dataOffset) ∨
    ∃ core' fl' n' σ', σ = started (fileBase + ce.plan.placement.dataOffset) ++ σ' ∧
      TraceN ce.bytes n' ⟨core', paddr ce 2 0, fl'⟩ σ' ∧
      core'.memory = core.memory ∧ core'.readReg .rsp = core.readReg .rsp := by
  let D := fileBase + ce.plan.placement.dataOffset
  -- block 0: prctl(38, 1, 0, 0, 0)
  have e1 := pstep_movI ce (b := 0) (j := 0) (by decide) (r := .rax) (v := 157) (by rw [PB.block_start]; rfl) core fl
  let k1 := core.setReg .rax 157
  have e2 := pstep_movI ce (b := 0) (j := 1) (by decide) (r := .rdi) (v := 38) (by rw [PB.block_start]; rfl) k1 fl
  let k2 := k1.setReg .rdi 38
  have e3 := pstep_movI ce (b := 0) (j := 2) (by decide) (r := .rsi) (v := 1) (by rw [PB.block_start]; rfl) k2 fl
  let k3 := k2.setReg .rsi 1
  have e4 := pstep_movI ce (b := 0) (j := 3) (by decide) (r := .rdx) (v := 0) (by rw [PB.block_start]; rfl) k3 fl
  let k4 := k3.setReg .rdx 0
  have e5 := pstep_movI ce (b := 0) (j := 4) (by decide) (r := .r10) (v := 0) (by rw [PB.block_start]; rfl) k4 fl
  let k5 := k4.setReg .r10 0
  have e6 := pstep_movI ce (b := 0) (j := 5) (by decide) (r := .r8) (v := 0) (by rw [PB.block_start]; rfl) k5 fl
  let k6 := k5.setReg .r8 0
  have hrun0 := run_comp (run_one e1) (run_comp (run_one e2) (run_comp (run_one e3)
    (run_comp (run_one e4) (run_comp (run_one e5) (run_one e6)))))
  obtain ⟨hd0, hb0, hnext0⟩ := psyscall_at ce (b := 0) (j := 6) (by decide)
    (by rw [PB.block_start]; rfl) (s := ⟨k6, paddr ce 0 6, fl⟩) rfl
  rcases TraceN.through hrun0 ht with rfl | ⟨-, ht1⟩
  · exact .inr (.inl List.nil_prefix)
  rcases TraceN.prctl (s := ⟨k6, paddr ce 0 6, fl⟩) hd0 hb0 rfl rfl ht1 with
    rfl | ⟨r, rcx, r11, fl1, σ1, rfl, -, ht2⟩
  · exact .inr (.inl List.nil_prefix)
  let s2 := returned ⟨k6, paddr ce 0 6, fl⟩ r rcx r11 fl1
  by_cases hr : r = 0
  · subst hr
    obtain ⟨f3, e7⟩ := prun_ifNz ce (b := 0) (j := 7) (by decide) (by rw [PB.block_start]; rfl)
      (by rw [PB.block_start]) s2.core s2.flags (taken := false) rfl
    have e7' : ByteEval.run ce.bytes fetchBase 3 s2 = .ok ⟨s2.core, paddr ce 1 0, f3⟩ := by
      have hs2 : s2 = ⟨s2.core, paddr ce 0 7, s2.flags⟩ := by unfold s2 returned; dsimp only; rw [hnext0]
      rw [hs2]; exact e7
    rcases TraceN.through e7' ht2 with rfl | ⟨-, ht3⟩
    · exact .inr (.inl ⟨[_], rfl⟩)
    -- block 1: seccomp(1, 0, fprogAddr D)
    have g1 := pstep_movI ce (b := 1) (j := 0) (by decide) (r := .rax) (v := 317) (by rw [PB.block_seccomp]; rfl) s2.core f3
    let m1 := s2.core.setReg .rax 317
    have g2 := pstep_movI ce (b := 1) (j := 1) (by decide) (r := .rdi) (v := 1) (by rw [PB.block_seccomp]; rfl) m1 f3
    let m2 := m1.setReg .rdi 1
    have g3 := pstep_movI ce (b := 1) (j := 2) (by decide) (r := .rsi) (v := 0) (by rw [PB.block_seccomp]; rfl) m2 f3
    let m3 := m2.setReg .rsi 0
    have g4 := pstep_movI ce (b := 1) (j := 3) (by decide) (r := .rdx) (v := fprogAddr D) (by rw [PB.block_seccomp]; rfl) m3 f3
    let m4 := m3.setReg .rdx (UInt64.ofNat (fprogAddr D))
    have hrun1 := run_comp (run_one g1) (run_comp (run_one g2) (run_comp (run_one g3) (run_one g4)))
    obtain ⟨hd1, hb1, hnext1⟩ := psyscall_at ce (b := 1) (j := 4) (by decide)
      (by rw [PB.block_seccomp]; rfl) (s := ⟨m4, paddr ce 1 4, f3⟩) rfl
    rcases TraceN.through hrun1 ht3 with rfl | ⟨-, ht4⟩
    · exact .inr (.inl ⟨[_], rfl⟩)
    rcases TraceN.seccomp (s := ⟨m4, paddr ce 1 4, f3⟩) hd1 hb1 rfl rfl rfl ht4 with
      rfl | ⟨r2, rcx2, r112, fl2, σ2, rfl, -, ht5⟩
    · exact .inr (.inl ⟨[_], rfl⟩)
    let s3 := returned ⟨m4, paddr ce 1 4, f3⟩ r2 rcx2 r112 fl2
    by_cases hr2 : r2 = 0
    · subst hr2
      obtain ⟨f4, e8⟩ := prun_ifNz ce (b := 1) (j := 5) (by decide) (by rw [PB.block_seccomp]; rfl)
        (by rw [PB.block_seccomp]) s3.core s3.flags (taken := false) rfl
      have e8' : ByteEval.run ce.bytes fetchBase 3 s3 = .ok ⟨s3.core, paddr ce 2 0, f4⟩ := by
        have hs3 : s3 = ⟨s3.core, paddr ce 1 5, s3.flags⟩ := by unfold s3 returned; dsimp only; rw [hnext1]
        rw [hs3]; exact e8
      rcases TraceN.through e8' ht5 with rfl | ⟨-, ht6⟩
      · exact .inr (.inl (List.prefix_refl _))
      exact .inr (.inr ⟨s3.core, f4, _, σ2, rfl, ht6, rfl, rfl⟩)
    · have hne2 : (s3.core.readReg .rax != 0) = true := by
        change (r2 != 0) = true; simpa using hr2
      obtain ⟨f4, e8⟩ := prun_ifNz ce (b := 1) (j := 5) (by decide) (by rw [PB.block_seccomp]; rfl)
        (by rw [PB.block_seccomp]) s3.core s3.flags hne2
      have e8' : ByteEval.run ce.bytes fetchBase 2 s3 = .ok ⟨s3.core, paddr ce 46 0, f4⟩ := by
        have hs3 : s3 = ⟨s3.core, paddr ce 1 5, s3.flags⟩ := by unfold s3 returned; dsimp only; rw [hnext1]
        rw [hs3]; exact e8
      rcases TraceN.through e8' ht5 with rfl | ⟨-, ht6⟩
      · exact .inl (.inr ⟨r2, [], hr2, writeSeq_nil 2 _ _, List.prefix_refl _⟩)
      have hrep := plain_report_path ce .confine (core := s3.core) (fl := f4) hfile ht6
      exact .inl (.inr ⟨r2, σ2, hr2, hrep, List.prefix_refl _⟩)
  · have hne1 : (s2.core.readReg .rax != 0) = true := by
      change (r != 0) = true; simpa using hr
    obtain ⟨f3, e7⟩ := prun_ifNz ce (b := 0) (j := 7) (by decide) (by rw [PB.block_start]; rfl)
      (by rw [PB.block_start]) s2.core s2.flags hne1
    have e7' : ByteEval.run ce.bytes fetchBase 2 s2 = .ok ⟨s2.core, paddr ce 46 0, f3⟩ := by
      have hs2 : s2 = ⟨s2.core, paddr ce 0 7, s2.flags⟩ := by unfold s2 returned; dsimp only; rw [hnext0]
      rw [hs2]; exact e7
    rcases TraceN.through e7' ht2 with rfl | ⟨-, ht3⟩
    · exact .inl (.inl ⟨r, [], hr, writeSeq_nil 2 _ _, List.prefix_refl _⟩)
    have hrep := plain_report_path ce .confine (core := s2.core) (fl := f3) hfile ht3
    exact .inl (.inl ⟨r, σ1, hr, hrep, List.prefix_refl _⟩)

/-! ## Step 2: Argument loop (blocks 4–7) -/

/-- Execute blocks 4–7 (`loopHead` → `parseArg` → `storeArg` / `parseErr`) over
remaining arguments `args.drop i`, either reporting `.natOverflow`/`.numeral`
or reaching `B.callInit` (block 8) with all parsed arguments stored at
`[L.stackTop .. L.stackTop + 40)`. -/
private theorem plain_args_loop {args : List (List Nat)} (hargs : ArgsOk args)
    (hlen : args.length = input.arity) {sp0 : Word} :
    ∀ (rem i : Nat) (acc : List Nat) {core : Core} {fl : ByteEval.Flags} {n : Nat} {σ : List Sys},
      i + rem = input.arity →
      acc.length = i →
      (∀ x ∈ acc, x < 2 ^ 64) →
      ArgBlock core.memory sp0 args (fun a => OutsideSegments input.layout.segments a ∧ CanonicalUser a) →
      core.readReg .r12 = sp0 + 8 →
      core.readReg .rbp = UInt64.ofNat input.layout.stackTop →
      core.readReg .r13 = UInt64.ofNat input.layout.stackTop →
      core.readReg .r14 = UInt64.ofNat input.layout.regionStart →
      core.readReg .rsp = UInt64.ofNat input.layout.shellTop →
      core.readReg .r15 = UInt64.ofNat i →
      (∀ k < 5, core.memory.read64 (UInt64.ofNat input.layout.stackTop + UInt64.ofNat (8 * k)) =
        UInt64.ofNat (acc[k]?.getD 0)) →
      (∀ k < ce.bytes.size, core.memory.bytes (UInt64.ofNat (fileBase + k)) = ce.bytes[k]!) →
      TraceN ce.bytes n ⟨core, paddr ce 4 0, fl⟩ σ →
      match parseArgsList (args.drop i) with
      | .overflow => ReportsMsg input.arity .natOverflow σ
      | .bad => ReportsMsg input.arity .numeral σ
      | .ok rest =>
        σ = [] ∨
        ∃ core' fl' n', TraceN ce.bytes n' ⟨core', paddr ce 8 0, fl'⟩ σ ∧
          core'.readReg .rbp = UInt64.ofNat input.layout.stackTop ∧
          core'.readReg .r13 = UInt64.ofNat input.layout.stackTop ∧
          core'.readReg .r14 = UInt64.ofNat input.layout.regionStart ∧
          core'.readReg .rsp = UInt64.ofNat input.layout.shellTop ∧
          (∀ k < 5, core'.memory.read64 (UInt64.ofNat input.layout.stackTop + UInt64.ofNat (8 * k)) =
            UInt64.ofNat ((acc ++ rest)[k]?.getD 0)) ∧
          (∀ k < ce.bytes.size, core'.memory.bytes (UInt64.ofNat (fileBase + k)) = ce.bytes[k]!) := by
  intro rem
  induction rem with
  | zero =>
    intro i acc core fl n σ hi haccLen _ _ _ hrbp hr13 hr14 hrsp hr15 hslots hfile ht
    have hieq : i = input.arity := by omega
    subst hieq
    have hdrop : args.drop input.arity = [] := List.drop_eq_nil_of_le (by omega)
    rw [hdrop]
    simp only [parseArgsList, List.append_nil]
    have hff := plainFileFacts ce
    have har : input.arity ≤ 5 := hff.arity
    have hseA : signExtend32 (UInt32.ofNat input.arity) = UInt64.ofNat input.arity :=
      plain_signExtend32_ofNat (by omega)
    have hge : Condition.holds .unsignedGe .w64 (core.readReg .r15) (signExtend32 (UInt32.ofNat input.arity)) = true := by
      rw [hr15, hseA, pholds_unsignedGe]; exact decide_eq_true (Nat.le_refl _)
    obtain ⟨f1, e1⟩ := prun_cmpI ce (b := 4) (j := 0) (by decide) (by rw [PB.block_loopHead]; rfl)
      (by rw [PB.block_loopHead]) core fl hge
    rcases TraceN.through e1 ht with rfl | ⟨-, ht1⟩
    · exact .inl rfl
    exact .inr ⟨core, f1, _, ht1, hrbp, hr13, hr14, hrsp, hslots, hfile⟩
  | succ rem ih =>
    intro i acc core fl n σ hi haccLen haccLt hab hr12 hrbp hr13 hr14 hrsp hr15 hslots hfile ht
    have hff := plainFileFacts ce
    have har : input.arity ≤ 5 := hff.arity
    have hL := plainLayout_numbers ce
    have hd : dataBase = 268435456 := rfl
    have hilt : i < args.length := by omega
    have hdrop : args.drop i = args[i] :: args.drop (i + 1) := List.drop_eq_getElem_cons hilt
    have hseA : signExtend32 (UInt32.ofNat input.arity) = UInt64.ofNat input.arity :=
      plain_signExtend32_ofNat (by omega)
    have hgeF : Condition.holds .unsignedGe .w64 (core.readReg .r15) (signExtend32 (UInt32.ofNat input.arity)) = false := by
      rw [hr15, hseA, pholds_unsignedGe, toNat_small (by omega), toNat_small (by omega)]
      exact decide_eq_false (by omega)
    obtain ⟨f1, e1⟩ := prun_cmpI ce (b := 4) (j := 0) (by decide) (by rw [PB.block_loopHead]; rfl)
      (by rw [PB.block_loopHead]) core fl hgeF
    have hnil_goal : match parseArgsList (args.drop i) with
        | .overflow => ReportsMsg input.arity .natOverflow []
        | .bad => ReportsMsg input.arity .numeral []
        | .ok rest => ([] : List Sys) = [] ∨
            ∃ core' fl' n', TraceN ce.bytes n' ⟨core', paddr ce 8 0, fl'⟩ [] ∧
              core'.readReg .rbp = UInt64.ofNat input.layout.stackTop ∧
              core'.readReg .r13 = UInt64.ofNat input.layout.stackTop ∧
              core'.readReg .r14 = UInt64.ofNat input.layout.regionStart ∧
              core'.readReg .rsp = UInt64.ofNat input.layout.shellTop ∧
              (∀ k < 5, core'.memory.read64 (UInt64.ofNat input.layout.stackTop + UInt64.ofNat (8 * k)) =
                UInt64.ofNat ((acc ++ rest)[k]?.getD 0)) ∧
              ∀ k < ce.bytes.size, core'.memory.bytes (UInt64.ofNat (fileBase + k)) = ce.bytes[k]! := by
      cases parseArgsList (args.drop i)
      · exact .inl rfl
      · exact writeSeq_nil 2 _ _
      · exact writeSeq_nil 2 _ _
    rcases TraceN.through e1 ht with rfl | ⟨-, ht1⟩
    · exact hnil_goal
    -- block 5: ld rsi, [r12 + 8 + 8*r15]; call 23
    rcases pstep_load64 ce (b := 5) (j := 0) (by decide) (by rw [PB.block_parseArg]; rfl) core f1 with
      ⟨ptr, hptr, e2⟩ | ⟨_, efault⟩
    · let c1 := core.setReg .rsi ptr
      rcases TraceN.through (run_one e2) ht1 with rfl | ⟨-, ht2⟩
      · exact hnil_goal
      have ecall := pstep_call ce (b := 5) (j := 1) (by decide) (t := UInt32.ofNat 23)
        (by rw [PB.block_parseArg]; rfl) (s := ⟨c1, paddr ce 5 1, f1⟩) rfl
      cases hw : c1.memory.write64? (c1.readReg .rsp - 8) (paddr ce 5 2) with
      | error _ =>
        rw [hw] at ecall
        have := TraceN.nil_of_step_fault ecall ht2; subst this; exact hnil_goal
      | ok mem1 =>
        rw [hw] at ecall
        rcases TraceN.through (run_one ecall) ht2 with rfl | ⟨-, ht3⟩
        · exact hnil_goal
        have hmem1Eq : mem1 = core.memory.write .w64 (UInt64.ofNat input.layout.stackTop + UInt64.ofNat 248) (paddr ce 5 2) := by
          have hc1sp : c1.readReg .rsp = UInt64.ofNat input.layout.shellTop := hrsp
          have heq248 : UInt64.ofNat input.layout.shellTop - 8 = UInt64.ofNat input.layout.stackTop + UInt64.ofNat 248 := by
            apply UInt64.toNat_inj.mp
            rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, toNat_small (by omega), show (8 : Word).toNat = 8 from rfl]; omega),
              toNat_small (by omega), show (8 : Word).toNat = 8 from rfl,
              ← UInt64.ofNat_add, toNat_small (by omega)]
            omega
          rw [hc1sp, heq248] at hw; exact write?_ok hw
        have hfile1 : ∀ k < ce.bytes.size, mem1.bytes (UInt64.ofNat (fileBase + k)) = ce.bytes[k]! := by
          intro k hk; rw [hmem1Eq, plain_write_scratch_preserves_file ce (by decide) hk]; exact hfile k hk
        have hab1 : ArgBlock mem1 sp0 args (fun a => OutsideSegments input.layout.segments a ∧ CanonicalUser a) := by
          obtain ⟨argc, h1, h2, h3, h4, h5, h6, h7⟩ := hab
          have hout_eq : ∀ a, OutsideSegments input.layout.segments a → mem1.bytes a = core.memory.bytes a := by
            intro a ho; rw [hmem1Eq]; exact plain_write_scratch_preserves_outside ce (by decide) a ho
          have hr_eq : ∀ s, (∀ b < 8, OutsideSegments input.layout.segments (s + UInt64.ofNat b)) →
              mem1.read64 s = core.memory.read64 s := fun s hs => read64_congr hout_eq hs
          refine ⟨argc, h1, ?_, h3, ?_, ?_, h6, ?_⟩
          · rw [hr_eq _ (fun b hb => by simpa using (h6 0 (by omega) b hb).1)]; exact h2
          · rw [hr_eq _ (fun b hb => by rw [slot_add]; exact (h6 (argc + 1) (Nat.le_refl _) b hb).1)]; exact h4
          · intro idx a ha
            have hslot : mem1.read64 (sp0 + UInt64.ofNat (8 * (idx + 2))) =
                core.memory.read64 (sp0 + UInt64.ofNat (8 * (idx + 2))) := by
              apply hr_eq
              intro b hb
              rw [slot_add]
              have hidxLe : idx + 2 ≤ argc + 1 := by
                have hlt' : idx < args.length := by
                  cases hget : args[idx]? with
                  | none => rw [hget] at ha; cases ha
                  | some _ => exact (List.getElem?_eq_some_iff.mp ha).1
                rcases h3 with ⟨rfl, rfl⟩ | rfl
                · simp at hlt'
                · omega
              exact (h6 (idx + 2) hidxLe b hb).1
            obtain ⟨hp, hbs, hnl⟩ := h5 idx a ha
            refine ⟨by rw [hslot]; exact hp, fun j hj => ?_, ?_⟩
            · rw [hslot, hout_eq _ (h7 idx a ha j (by omega)).1]; exact hbs j hj
            · rw [hslot, hout_eq _ (h7 idx a ha a.length (Nat.le_refl _)).1]; exact hnl
          · intro idx a ha j hj
            have hslot : mem1.read64 (sp0 + UInt64.ofNat (8 * (idx + 2))) =
                core.memory.read64 (sp0 + UInt64.ofNat (8 * (idx + 2))) := by
              apply hr_eq
              intro b hb; rw [slot_add]
              have hlt' : idx < args.length := (List.getElem?_eq_some_iff.mp ha).1
              rcases h3 with ⟨rfl, rfl⟩ | rfl
              · simp at hlt'
              · exact (h6 (idx + 2) (by omega) b hb).1
            rw [hslot]; exact h7 idx a ha j hj
        have hptrEq : ptr = core.memory.read64 (sp0 + UInt64.ofNat (8 * (i + 2))) := by
          have heval : (atIdx .r12 8 .r15 .eight).eval core = sp0 + UInt64.ofNat (8 * (i + 2)) := by
            simp only [MemAddr.eval, hr12, IndexReg.gpr, Scale.word, hr15]
            rw [show signExtend32 (UInt32.ofNat 8) = UInt64.ofNat 8 by decide,
              show (8 : Word) = UInt64.ofNat 8 from rfl,
              ← UInt64.ofNat_mul, UInt64.add_assoc, UInt64.add_assoc,
              ← UInt64.ofNat_add, ← UInt64.ofNat_add]
            congr 1; congr 1; omega
          rw [read64?_value hptr, heval]
        have ⟨_, _, _, _, _, hstr1, _, _⟩ := hab1
        obtain ⟨_, hbytes1, hnul1⟩ := hstr1 i args[i] (List.getElem?_eq_getElem hilt)
        have hptrEq1 : ptr = mem1.read64 (sp0 + UInt64.ofNat (8 * (i + 2))) := by
          obtain ⟨argc, _, _, h3, _, _, h6, _⟩ := hab
          have hout_eq : ∀ a, OutsideSegments input.layout.segments a → mem1.bytes a = core.memory.bytes a := by
            intro a ho; rw [hmem1Eq]; exact plain_write_scratch_preserves_outside ce (by decide) a ho
          rw [hptrEq]
          symm
          apply read64_congr hout_eq
          intro b hb; rw [slot_add]
          rcases h3 with ⟨rfl, rfl⟩ | rfl
          · simp at hilt
          · exact (h6 (i + 2) (by omega) b hb).1
        rw [← hptrEq1] at hbytes1 hnul1
        have hretW : mem1.read64 (UInt64.ofNat input.layout.shellTop - 8) = paddr ce 5 2 := by
          have hc1sp : c1.readReg .rsp = UInt64.ofNat input.layout.shellTop := hrsp
          rw [hc1sp] at hw; rw [write?_ok hw]; exact write_read64_same _ _ _
        let c2 : Core := { c1.setReg .rsp (UInt64.ofNat input.layout.shellTop - 8) with memory := mem1 }
        change TraceN ce.bytes _ ⟨{ c1.setReg .rsp (c1.readReg .rsp - 8) with memory := mem1 }, paddr ce 23 0, f1⟩ σ at ht3
        rw [show c1.readReg .rsp = UInt64.ofNat input.layout.shellTop from hrsp] at ht3
        change TraceN ce.bytes _ ⟨c2, paddr ce 23 0, f1⟩ σ at ht3
        have haOk : ∀ b ∈ args[i], 0 < b ∧ b < 256 := hargs args[i] (List.getElem_mem hilt)
        rcases plain_parse_run ce haOk (ptr := ptr) (retAddr := paddr ce 5 2)
            (core := c2) (fl := f1) hbytes1 hnul1 rfl rfl hretW with
          ⟨mp, c3, f3, hrunP, hmemP, hspP, hsavedP, hresP⟩ | ⟨mp, hfaultP⟩
        · rcases TraceN.through hrunP ht3 with rfl | ⟨-, ht4⟩
          · exact hnil_goal
          have hfile3 : ∀ k < ce.bytes.size, c3.memory.bytes (UInt64.ofNat (fileBase + k)) = ce.bytes[k]! := by
            rw [hmemP]; exact hfile1
          have hrbp3 : c3.readReg .rbp = UInt64.ofNat input.layout.stackTop := by
            rw [hsavedP .rbp (by simp)]; exact hrbp
          have hr12_3 : c3.readReg .r12 = sp0 + 8 := by
            rw [hsavedP .r12 (by simp)]; exact hr12
          have hr13_3 : c3.readReg .r13 = UInt64.ofNat input.layout.stackTop := by
            rw [hsavedP .r13 (by simp)]; exact hr13
          have hr14_3 : c3.readReg .r14 = UInt64.ofNat input.layout.regionStart := by
            rw [hsavedP .r14 (by simp)]; exact hr14
          have hr15_3 : c3.readReg .r15 = UInt64.ofNat i := by
            rw [hsavedP .r15 (by simp)]; exact hr15
          rw [hdrop]
          simp only [parseArgsList]
          cases hpa : parseArgBytes args[i] with
          | overflow =>
            rw [hpa] at hresP
            have hc5 : Condition.holds .ne .w64 (c3.readReg .rdx) (signExtend32 (UInt32.ofNat 0)) = true := by
              rw [hresP]; decide
            obtain ⟨f4, e4⟩ := prun_cmpI ce (b := 5) (j := 2) (by decide) (by rw [PB.block_parseArg]; rfl)
              (by rw [PB.block_parseArg]) c3 f3 hc5
            have hc6 : Condition.holds .eq .w64 (c3.readReg .rdx) (signExtend32 (UInt32.ofNat 1)) = true := by
              rw [hresP]; decide
            obtain ⟨f5, e5⟩ := prun_cmpI ce (b := 6) (j := 0) (by decide) (by rw [PB.block_parseErr]; rfl)
              (by rw [PB.block_parseErr]) c3 f4 hc6
            rcases TraceN.through (run_comp e4 e5) ht4 with rfl | ⟨-, ht5⟩
            · exact writeSeq_nil 2 _ _
            exact plain_report_path ce .natOverflow hfile3 ht5
          | bad =>
            rw [hpa] at hresP
            have hc5 : Condition.holds .ne .w64 (c3.readReg .rdx) (signExtend32 (UInt32.ofNat 0)) = true := by
              rw [hresP]; decide
            obtain ⟨f4, e4⟩ := prun_cmpI ce (b := 5) (j := 2) (by decide) (by rw [PB.block_parseArg]; rfl)
              (by rw [PB.block_parseArg]) c3 f3 hc5
            have hc6 : Condition.holds .eq .w64 (c3.readReg .rdx) (signExtend32 (UInt32.ofNat 1)) = false := by
              rw [hresP]; decide
            obtain ⟨f5, e5⟩ := prun_cmpI ce (b := 6) (j := 0) (by decide) (by rw [PB.block_parseErr]; rfl)
              (by rw [PB.block_parseErr]) c3 f4 hc6
            rcases TraceN.through (run_comp e4 e5) ht4 with rfl | ⟨-, ht5⟩
            · exact writeSeq_nil 2 _ _
            exact plain_report_path ce .numeral hfile3 ht5
          | ok v =>
            rw [hpa] at hresP
            obtain ⟨hdx0, haxV⟩ := hresP
            have hvLt : v < 2 ^ 64 := by
              cases ha_eq : args[i] with
              | nil => rw [ha_eq] at hpa; simp [parseArgBytes] at hpa
              | cons b bs =>
                rw [ha_eq] at hpa; simp only [parseArgBytes] at hpa
                cases hd' : parseDigitsAux 0 (b :: bs) with
                | none => simp [hd'] at hpa
                | some m => simp only [hd'] at hpa; split at hpa <;> cases hpa; assumption
            have hc5 : Condition.holds .ne .w64 (c3.readReg .rdx) (signExtend32 (UInt32.ofNat 0)) = false := by
              rw [hdx0]; decide
            obtain ⟨f4, e4⟩ := prun_cmpI ce (b := 5) (j := 2) (by decide) (by rw [PB.block_parseArg]; rfl)
              (by rw [PB.block_parseArg]) c3 f3 hc5
            rcases TraceN.through e4 ht4 with rfl | ⟨-, ht5⟩
            · cases parseArgsList (args.drop (i + 1)) <;> first | exact .inl rfl | exact writeSeq_nil 2 _ _
            -- block 7: st [rbp + 8*r15], rax; add r15, 1; jmp 4
            rcases pstep_store64 ce (b := 7) (j := 0) (by decide) (by rw [PB.block_storeArg]; rfl) c3 f4 with
              ⟨mem4, hw4, e5⟩ | ⟨_, efault⟩
            · let c4 : Core := { c3 with memory := mem4 }
              obtain ⟨f6, e6⟩ := pstep_alu ce (b := 7) (j := 1) (by decide) (by rw [PB.block_storeArg]; rfl) c4 f4
              let c5 := c4.writeReg .w64 .r15 (AluOp.add.eval (c4.readReg .r15) (signExtend32 (UInt32.ofNat 1)))
              have e7 := pstep_jump ce (b := 7) (by decide) (t := UInt32.ofNat 4)
                (by rw [PB.block_storeArg]) (s := ⟨c5, paddr ce 7 2, f6⟩) (by rw [PB.block_storeArg]; rfl)
              rcases TraceN.through (run_comp (run_one e5) (run_comp (run_one e6) (run_one e7))) ht5 with
                rfl | ⟨-, ht6⟩
              · cases parseArgsList (args.drop (i + 1)) <;> first | exact .inl rfl | exact writeSeq_nil 2 _ _
              have hmem4Eq : mem4 = mem1.write .w64 (UInt64.ofNat input.layout.stackTop + UInt64.ofNat (8 * i)) (UInt64.ofNat v) := by
                have heval : (atIdx .rbp 0 .r15 .eight).eval c3 =
                    UInt64.ofNat input.layout.stackTop + UInt64.ofNat (8 * i) := by
                  simp only [MemAddr.eval, hrbp3, IndexReg.gpr, Scale.word, hr15_3]
                  rw [show signExtend32 (UInt32.ofNat 0) = 0 by decide, UInt64.add_zero,
                    show (8 : Word) = UInt64.ofNat 8 from rfl, ← UInt64.ofNat_mul, Nat.mul_comm i 8]
                rw [heval, haxV, hmemP] at hw4; exact write?_ok hw4
              have hfile4 : ∀ k < ce.bytes.size, c5.memory.bytes (UInt64.ofNat (fileBase + k)) = ce.bytes[k]! := by
                intro k hk; change mem4.bytes _ = _; rw [hmem4Eq, plain_write_scratch_preserves_file ce (by omega) hk]
                exact hfile1 k hk
              have hab4 : ArgBlock c5.memory sp0 args (fun a => OutsideSegments input.layout.segments a ∧ CanonicalUser a) := by
                change ArgBlock mem4 _ _ _
                obtain ⟨argc, h1, h2, h3, h4, h5, h6, h7⟩ := hab1
                have hout_eq : ∀ a, OutsideSegments input.layout.segments a → mem4.bytes a = mem1.bytes a := by
                  intro a ho; rw [hmem4Eq]; exact plain_write_scratch_preserves_outside ce (by omega) a ho
                have hr_eq : ∀ s, (∀ b < 8, OutsideSegments input.layout.segments (s + UInt64.ofNat b)) →
                    mem4.read64 s = mem1.read64 s := fun s hs => read64_congr hout_eq hs
                refine ⟨argc, h1, ?_, h3, ?_, ?_, h6, ?_⟩
                · rw [hr_eq _ (fun b hb => by simpa using (h6 0 (by omega) b hb).1)]; exact h2
                · rw [hr_eq _ (fun b hb => by rw [slot_add]; exact (h6 (argc + 1) (Nat.le_refl _) b hb).1)]; exact h4
                · intro idx a ha
                  have hslot : mem4.read64 (sp0 + UInt64.ofNat (8 * (idx + 2))) =
                      mem1.read64 (sp0 + UInt64.ofNat (8 * (idx + 2))) := by
                    apply hr_eq; intro b hb; rw [slot_add]
                    have hlt' : idx < args.length := (List.getElem?_eq_some_iff.mp ha).1
                    rcases h3 with ⟨rfl, rfl⟩ | rfl
                    · simp at hlt'
                    · exact (h6 (idx + 2) (by omega) b hb).1
                  obtain ⟨hp, hbs, hnl⟩ := h5 idx a ha
                  refine ⟨by rw [hslot]; exact hp, fun j hj => ?_, ?_⟩
                  · rw [hslot, hout_eq _ (h7 idx a ha j (by omega)).1]; exact hbs j hj
                  · rw [hslot, hout_eq _ (h7 idx a ha a.length (Nat.le_refl _)).1]; exact hnl
                · intro idx a ha j hj
                  have hslot : mem4.read64 (sp0 + UInt64.ofNat (8 * (idx + 2))) =
                      mem1.read64 (sp0 + UInt64.ofNat (8 * (idx + 2))) := by
                    apply hr_eq; intro b hb; rw [slot_add]
                    have hlt' : idx < args.length := (List.getElem?_eq_some_iff.mp ha).1
                    rcases h3 with ⟨rfl, rfl⟩ | rfl
                    · simp at hlt'
                    · exact (h6 (idx + 2) (by omega) b hb).1
                  rw [hslot]; exact h7 idx a ha j hj
              have hslots4 : ∀ k < 5, c5.memory.read64 (UInt64.ofNat input.layout.stackTop + UInt64.ofNat (8 * k)) =
                  UInt64.ofNat ((acc ++ [v])[k]?.getD 0) := by
                intro k hk
                change mem4.read64 _ = _
                rw [hmem4Eq]
                by_cases hki : k = i
                · subst hki
                  rw [write_read64_same, List.getElem?_append_right (by omega)]
                  simp [haccLen]
                · rw [write_read64_apart]
                  · rw [hmem1Eq, write_read64_apart]
                    · rw [hslots k hk]
                      by_cases hlt' : k < i
                      · rw [List.getElem?_append_left (by omega)]
                      · have hgt' : i < k := by omega
                        rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp [haccLen]; omega)]
                    · intro b1 hb1 b2 hb2 heq
                      have h1 := congrArg UInt64.toNat heq
                      rw [UInt64.add_assoc, UInt64.add_assoc, ← UInt64.ofNat_add, ← UInt64.ofNat_add,
                        ← UInt64.ofNat_add, ← UInt64.ofNat_add,
                        toNat_small (by omega), toNat_small (by simp [Width.bytes] at hb2; omega)] at h1
                      simp [Width.bytes] at hb2; omega
                  · intro b1 hb1 b2 hb2 heq
                    have h1 := congrArg UInt64.toNat heq
                    rw [UInt64.add_assoc, UInt64.add_assoc, ← UInt64.ofNat_add, ← UInt64.ofNat_add,
                      ← UInt64.ofNat_add, ← UInt64.ofNat_add,
                      toNat_small (by omega), toNat_small (by simp [Width.bytes] at hb2; omega)] at h1
                    simp [Width.bytes] at hb2; omega
              have hr15_5 : c5.readReg .r15 = UInt64.ofNat (i + 1) := by
                simp only [c5, c4, Core.writeReg, Core.readReg, Core.setReg, Registers.set,
                  AluOp.eval, BEq.rfl, ↓reduceIte]
                rw [show c3.registers .r15 = UInt64.ofNat i from hr15_3,
                  show signExtend32 (UInt32.ofNat 1) = UInt64.ofNat 1 by decide, ← UInt64.ofNat_add]
              have hrec := ih (i + 1) (acc ++ [v]) (by omega) (by simp [haccLen])
                (fun x hx => by
                  rcases List.mem_append.mp hx with h1 | h2
                  · exact haccLt x h1
                  · simp at h2; subst h2; exact hvLt)
                hab4 hr12_3 hrbp3 hr13_3 hr14_3 hspP hr15_5 hslots4 hfile4 ht6
              cases hrest : parseArgsList (args.drop (i + 1)) with
              | overflow => rw [hrest] at hrec; exact hrec
              | bad => rw [hrest] at hrec; exact hrec
              | ok rest =>
                rw [hrest] at hrec
                rcases hrec with rfl | ⟨core', fl', n', ht', h1, h2, h3, h4, h5, h6⟩
                · exact .inl rfl
                · exact .inr ⟨core', fl', n', ht', h1, h2, h3, h4,
                    by simpa [List.append_assoc] using h5, h6⟩
            · have := TraceN.nil_of_step_fault efault ht5; subst this
              cases parseArgsList (args.drop (i + 1)) <;> first | exact .inl rfl | exact writeSeq_nil 2 _ _
        · have := TraceN.nil_of_faults hfaultP ht3; subst this; exact hnil_goal
    · have := TraceN.nil_of_step_fault efault ht1; subst this; exact hnil_goal

/-! ## Step 3: `cx_init` + `root` glue and `two_calls` lift -/

/-- Exact instruction count from `cx_init`'s return (`paddr ce 8 10`) to
`root`'s call (`paddr ce 10 9`): `cmp rsp, r13` (3) + `mov rsp, shellTop` (1)
+ `ifNz rax` (3) + 9 instructions of `callRoot` = 16. -/
def plainGlueSteps : Nat := 16

/-- Driver for `cx_init` at `paddr ce 8 9` (return address `paddr ce 8 10`). -/
def plainInitDriver (s₀ : ByteEval.State) : Driver :=
  input.layout.driverAt ce.plan.placement.textOffset (plainAddr ce 8 10)
    s₀.core.memory.bytes s₀.flags s₀.core.registers

/-- Site for `root` at `paddr ce 10 9` (return address `paddr ce 10 10`). -/
def plainRootSite (s₀ : ByteEval.State) : Driver.Site :=
  ⟨paddr ce 10 10, ByteEval.aluFlags .and .w64 0 0,
    ((s₀.core.registers.set .rax 0).set .r10 0).set .r11 0⟩

private theorem plainInitDriver_ok (s₀ : ByteEval.State) :
    (plainInitDriver ce s₀).Ok ce.plan.placement.textSize := by
  have ff := plainFileFacts ce
  have hlo : fileBase + ce.plan.placement.textOffset + ce.plan.placement.textSize ≤ plainAddr ce 8 10 := by
    unfold plainAddr; have := ff.textEnd; have := ff.dataEnd; omega
  have hhi : plainAddr ce 8 10 < dataBase :=
    plainAddr_below ce (plainAddr_term_in ce (b := 8) (by decide))
  exact (input.layout.driverAt_canonicalOk ff.layoutCheck hlo hhi _ _ _).toOk

private theorem plainRootDriver_ok (s₀ : ByteEval.State) :
    ((plainInitDriver ce s₀).withSite (plainRootSite ce s₀)).Ok ce.plan.placement.textSize := by
  have ff := plainFileFacts ce
  have hlo : fileBase + ce.plan.placement.textOffset + ce.plan.placement.textSize ≤ plainAddr ce 10 10 := by
    unfold plainAddr; have := ff.textEnd; have := ff.dataEnd; omega
  have hhi : plainAddr ce 10 10 < dataBase :=
    plainAddr_below ce (plainAddr_term_in ce (b := 10) (by decide))
  have h := (input.layout.driverAt_canonicalOk ff.layoutCheck hlo hhi s₀.core.memory.bytes
    (plainRootSite ce s₀).flags (plainRootSite ce s₀).other).toOk
  exact ⟨h.aligned, h.minSize, h.below, h.spAlign, h.spTop, h.budgetMin, h.spLow, h.apart, h.retOut⟩

private theorem plain_file_text :
    ∃ text, ELFRead.text? input.object = some text ∧
      (∀ i < text.size, ce.bytes[ce.plan.placement.textOffset + i]? = text[i]?) ∧
      ce.plan.placement.textOffset + text.size ≤ 2 ^ 64 := by
  have ff := plainFileFacts ce
  obtain ⟨parsed, hp, hsize, htext⟩ := ff.text
  have hd : dataBase = 268435456 := rfl
  have hfs : ce.plan.placement.fileSize = ce.plan.placement.shellOffset + ce.plan.placement.shellSize := rfl
  have := ff.below; have := ff.textEnd; have := ff.dataEnd
  refine ⟨parsed.text, by simp [ELFRead.text?, hp], fun i hi => htext i (hsize ▸ hi), by omega⟩

private theorem plain_sp_add8 (s₀ : ByteEval.State) :
    (plainInitDriver ce s₀).sp + 8 = UInt64.ofNat input.layout.stackTop := by
  have hL := plainLayout_numbers ce
  have hd : dataBase = 268435456 := rfl
  show UInt64.ofNat (input.layout.stackTop - 8) + UInt64.ofNat 8 = UInt64.ofNat input.layout.stackTop
  rw [← UInt64.ofNat_add, Nat.sub_add_cancel (by omega)]

private theorem plainInitDriver_ctx_sub48 (s₀ : ByteEval.State) :
    (plainInitDriver ce s₀).ctx - 48 = UInt64.ofNat input.layout.regionStart + 16 := by
  have hL := plainLayout_numbers ce
  have hd : dataBase = 268435456 := rfl
  apply UInt64.toNat_inj.mp
  show ((UInt64.ofNat input.layout.regionStart + 64) - 48).toNat = (UInt64.ofNat input.layout.regionStart + 16).toNat
  have h64 : (UInt64.ofNat input.layout.regionStart + 64).toNat = input.layout.regionStart + 64 := by
    rw [show (64 : Word) = UInt64.ofNat 64 from rfl, ← UInt64.ofNat_add, toNat_small (by omega)]
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, h64, show (48 : Word).toNat = 48 from rfl]; omega),
    h64, show (48 : Word).toNat = 48 from rfl,
    show (16 : Word) = UInt64.ofNat 16 from rfl, ← UInt64.ofNat_add, toNat_small (by omega)]
  omega

/-- Second half of `plain_glue`: block 10 instructions `1..8` from an opaque `k3`
(after `mov rdi, r14`), avoiding `Core.setReg` term-size blowup. -/
private theorem plain_glue_callRoot {ns : List Nat} {s₀ s₁ : ByteEval.State}
    {k3 : Core} {f2 : ByteEval.Flags}
    (hf2 : f2 = ByteEval.aluFlags .and .w64 0 0)
    (hk3mem : k3.memory = s₁.core.memory)
    (hk3rbp : k3.readReg .rbp = UInt64.ofNat input.layout.stackTop)
    (hk3r13 : k3.readReg .r13 = UInt64.ofNat input.layout.stackTop)
    (hk3regs : ∀ r, r ≠ .rsp → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
      k3.readReg r = ((plainInitDriver ce s₀).withSite (plainRootSite ce s₀)).regs (ns.map UInt64.ofNat) r)
    (hslot1 : ∀ k < 5, s₁.core.memory.read64
      (UInt64.ofNat input.layout.stackTop + UInt64.ofNat (8 * k)) = UInt64.ofNat (ns[k]?.getD 0)) :
    (∃ s₂, ByteEval.run ce.bytes fetchBase 8 ⟨k3, paddr ce 10 1, f2⟩ = .ok s₂ ∧
      AtCall ce.bytes input.object input.root
        ((plainInitDriver ce s₀).withSite (plainRootSite ce s₀))
        (ns.map UInt64.ofNat) s₁.core.memory.bytes s₂) ∨
    FaultsWithin ce.bytes ⟨k3, paddr ce 10 1, f2⟩ 8 := by
  have hevalSlot : ∀ (c : Core) (d : Nat), c.readReg .rbp = UInt64.ofNat input.layout.stackTop →
      d < 2 ^ 31 → (SB.at_ .rbp d).eval c = UInt64.ofNat input.layout.stackTop + UInt64.ofNat d := by
    intro c d hrb hd'
    rw [eval_at c .rbp (plain_signExtend32_ofNat hd'), hrb]
  rcases pstep_load64 ce (b := 10) (j := 1) (by decide) (by rw [PB.block_callRoot]; rfl) k3 f2 with
    ⟨v0, hv0, e5⟩ | ⟨f, ef⟩
  · let k4 := k3.setReg .rsi v0
    rcases pstep_load64 ce (b := 10) (j := 2) (by decide) (by rw [PB.block_callRoot]; rfl) k4 f2 with
      ⟨v1, hv1, e6⟩ | ⟨f, ef⟩
    · let k5 := k4.setReg .rdx v1
      rcases pstep_load64 ce (b := 10) (j := 3) (by decide) (by rw [PB.block_callRoot]; rfl) k5 f2 with
        ⟨v2, hv2, e7⟩ | ⟨f, ef⟩
      · let k6 := k5.setReg .rcx v2
        rcases pstep_load64 ce (b := 10) (j := 4) (by decide) (by rw [PB.block_callRoot]; rfl) k6 f2 with
          ⟨v3, hv3, e8⟩ | ⟨f, ef⟩
        · let k7 := k6.setReg .r8 v3
          rcases pstep_load64 ce (b := 10) (j := 5) (by decide) (by rw [PB.block_callRoot]; rfl) k7 f2 with
            ⟨v4, hv4, e9⟩ | ⟨f, ef⟩
          · let k8 := k7.setReg .r9 v4
            have e10 := pstep_movI ce (b := 10) (j := 6) (by decide) (r := .r10) (v := 0)
              (by rw [PB.block_callRoot]; rfl) k8 f2
            let k9 := k8.setReg .r10 0
            have e11 := pstep_movI ce (b := 10) (j := 7) (by decide) (r := .r11) (v := 0)
              (by rw [PB.block_callRoot]; rfl) k9 f2
            let k10 := k9.setReg .r11 0
            have e12 := pstep_movR ce (b := 10) (j := 8) (by decide) (d := .rsp) (s := .r13)
              (by rw [PB.block_callRoot]; rfl) k10 f2
            rw [show k10.readReg .r13 = UInt64.ofNat input.layout.stackTop from hk3r13] at e12
            let k11 := k10.setReg .rsp (UInt64.ofNat input.layout.stackTop)
            have hrun8 : ByteEval.run ce.bytes fetchBase 8 ⟨k3, paddr ce 10 1, f2⟩ = .ok ⟨k11, paddr ce 10 9, f2⟩ :=
              run_comp (run_one e5) (run_comp (run_one e6) (run_comp (run_one e7)
                (run_comp (run_one e8) (run_comp (run_one e9) (run_comp (run_one e10)
                  (run_comp (run_one e11) (run_one e12)))))))
            have hv0Eq : v0 = (ns.map UInt64.ofNat).getD 0 0 := by
              rw [read64?_value hv0, hevalSlot k3 0 hk3rbp (by decide), hk3mem]
              change s₁.core.memory.read64 (UInt64.ofNat input.layout.stackTop + UInt64.ofNat (8 * 0)) = _
              rw [hslot1 0 (by decide)]
              cases ns with | nil => rfl | cons _ _ => rfl
            have hv1Eq : v1 = (ns.map UInt64.ofNat).getD 1 0 := by
              rw [read64?_value hv1, hevalSlot k4 8 hk3rbp (by decide), show k4.memory = s₁.core.memory from hk3mem]
              change s₁.core.memory.read64 (UInt64.ofNat input.layout.stackTop + UInt64.ofNat (8 * 1)) = _
              rw [hslot1 1 (by decide)]
              cases ns with | nil => rfl | cons _ t => cases t with | nil => rfl | cons _ _ => rfl
            have hv2Eq : v2 = (ns.map UInt64.ofNat).getD 2 0 := by
              rw [read64?_value hv2, hevalSlot k5 16 hk3rbp (by decide), show k5.memory = s₁.core.memory from hk3mem]
              change s₁.core.memory.read64 (UInt64.ofNat input.layout.stackTop + UInt64.ofNat (8 * 2)) = _
              rw [hslot1 2 (by decide)]
              cases ns with | nil => rfl | cons _ t => cases t with | nil => rfl | cons _ t => cases t with | nil => rfl | cons _ _ => rfl
            have hv3Eq : v3 = (ns.map UInt64.ofNat).getD 3 0 := by
              rw [read64?_value hv3, hevalSlot k6 24 hk3rbp (by decide), show k6.memory = s₁.core.memory from hk3mem]
              change s₁.core.memory.read64 (UInt64.ofNat input.layout.stackTop + UInt64.ofNat (8 * 3)) = _
              rw [hslot1 3 (by decide)]
              cases ns with | nil => rfl | cons _ t => cases t with | nil => rfl | cons _ t => cases t with | nil => rfl | cons _ t => cases t with | nil => rfl | cons _ _ => rfl
            have hv4Eq : v4 = (ns.map UInt64.ofNat).getD 4 0 := by
              rw [read64?_value hv4, hevalSlot k7 32 hk3rbp (by decide), show k7.memory = s₁.core.memory from hk3mem]
              change s₁.core.memory.read64 (UInt64.ofNat input.layout.stackTop + UInt64.ofNat (8 * 4)) = _
              rw [hslot1 4 (by decide)]
              cases ns with | nil => rfl | cons _ t => cases t with | nil => rfl | cons _ t => cases t with | nil => rfl | cons _ t => cases t with | nil => rfl | cons _ t => cases t with | nil => rfl | cons _ _ => rfl
            obtain ⟨off, hoff, hcalls⟩ := pcallsTo ce (b := 10) (j := 9) (by decide)
              (by rw [PB.block_callRoot]; rfl) (s := ⟨k11, paddr ce 10 9, f2⟩) rfl
            refine .inl ⟨⟨k11, paddr ce 10 9, f2⟩, hrun8, ?_⟩
            refine ⟨⟨off, hoff, hcalls⟩, ?_, ?_, ?_, congrArg Memory.bytes hk3mem, hf2⟩
            · show UInt64.ofNat (plainAddr ce 10 10) = paddr ce 10 9 + 5
              exact (next_addr (p := plainShellOf ce) (origin := ce.plan.placement.shellOffset) (b := 10)
                (j := 9) (i := .callExport input.root) (by rw [PB.block_callRoot]; rfl)).symm
            · intro r hr'
              cases r with
              | rsp => exact absurd rfl hr'
              | rsi => simp [k11, k10, k9, k8, k7, k6, k5, k4, Core.readReg, Core.setReg, Registers.set, Driver.withSite, Driver.core, Driver.regs, hv0Eq]
              | rdx => simp [k11, k10, k9, k8, k7, k6, k5, Core.readReg, Core.setReg, Registers.set, Driver.withSite, Driver.core, Driver.regs, hv1Eq]
              | rcx => simp [k11, k10, k9, k8, k7, k6, Core.readReg, Core.setReg, Registers.set, Driver.withSite, Driver.core, Driver.regs, hv2Eq]
              | r8 => simp [k11, k10, k9, k8, k7, Core.readReg, Core.setReg, Registers.set, Driver.withSite, Driver.core, Driver.regs, hv3Eq]
              | r9 => simp [k11, k10, k9, k8, Core.readReg, Core.setReg, Registers.set, Driver.withSite, Driver.core, Driver.regs, hv4Eq]
              | r10 => simp [k11, k10, k9, Core.readReg, Core.setReg, Registers.set, Driver.withSite, Driver.core, Driver.regs, plainRootSite]
              | r11 => simp [k11, k10, Core.readReg, Core.setReg, Registers.set, Driver.withSite, Driver.core, Driver.regs, plainRootSite]
              | rax => exact (show k11.readReg .rax = k3.readReg .rax from rfl).trans (hk3regs .rax (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
              | rbx => exact (show k11.readReg .rbx = k3.readReg .rbx from rfl).trans (hk3regs .rbx (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
              | rbp => exact (show k11.readReg .rbp = k3.readReg .rbp from rfl).trans (hk3regs .rbp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
              | rdi => exact (show k11.readReg .rdi = k3.readReg .rdi from rfl).trans (hk3regs .rdi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
              | r12 => exact (show k11.readReg .r12 = k3.readReg .r12 from rfl).trans (hk3regs .r12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
              | r13 => exact (show k11.readReg .r13 = k3.readReg .r13 from rfl).trans (hk3regs .r13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
              | r14 => exact (show k11.readReg .r14 = k3.readReg .r14 from rfl).trans (hk3regs .r14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
              | r15 => exact (show k11.readReg .r15 = k3.readReg .r15 from rfl).trans (hk3regs .r15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
            · show k11.readReg .rsp = ((plainInitDriver ce s₀).withSite (plainRootSite ce s₀)).sp + 8
              simp [k11, Core.readReg, Core.setReg, Registers.set, Driver.withSite]
              exact (plain_sp_add8 ce s₀).symm
          · exact .inr ⟨4, by decide, _, f, run_comp (run_one e5) (run_comp (run_one e6) (run_comp (run_one e7) (run_one e8))), ef⟩
        · exact .inr ⟨3, by decide, _, f, run_comp (run_one e5) (run_comp (run_one e6) (run_one e7)), ef⟩
      · exact .inr ⟨2, by decide, _, f, run_comp (run_one e5) (run_one e6), ef⟩
    · exact .inr ⟨1, by decide, _, f, run_one e5, ef⟩
  · exact .inr ⟨0, by decide, _, f, rfl, ef⟩

/-- **Glue between `cx_init` and `root`**: from any status-0 return of `cx_init`,
the next 16 instructions reach `root`'s call site in `AtCall` for `plainRootSite`
with `ns` loaded from `[L.stackTop .. L.stackTop + 40)`, or fault on memory. -/
private theorem plain_glue {ns : List Nat} (_hnsLen : ns.length ≤ 5) {s₀ : ByteEval.State}
    (hrbp : s₀.core.readReg .rbp = UInt64.ofNat input.layout.stackTop)
    (hr13 : s₀.core.readReg .r13 = UInt64.ofNat input.layout.stackTop)
    (hr14 : s₀.core.readReg .r14 = UInt64.ofNat input.layout.regionStart)
    (hslots : ∀ k < 5, wordOf (plainInitDriver ce s₀).initBytes
      (UInt64.ofNat input.layout.stackTop + UInt64.ofNat (8 * k)) = UInt64.ofNat (ns[k]?.getD 0)) :
    ∀ s₁, Returned (plainInitDriver ce s₀) (plainInitDriver ce s₀).initBytes 0 s₁ →
      (∃ s₂, ByteEval.run ce.bytes fetchBase plainGlueSteps s₁ = .ok s₂ ∧
        AtCall ce.bytes input.object input.root
          ((plainInitDriver ce s₀).withSite (plainRootSite ce s₀))
          (ns.map UInt64.ofNat) s₁.core.memory.bytes s₂) ∨
      FaultsWithin ce.bytes s₁ plainGlueSteps := by
  intro s₁ hr
  have hL := plainLayout_numbers ce
  have hd : dataBase = 268435456 := rfl
  have hrsp : s₁.core.readReg .rsp = UInt64.ofNat input.layout.stackTop := hr.rsp.trans (plain_sp_add8 ce s₀)
  have hrax : s₁.core.readReg .rax = 0 := hr.rax
  have hsaved : ∀ r ∈ SysV.calleeSaved, s₁.core.readReg r = s₀.core.registers r := hr.saved
  have hrbp1 : s₁.core.readReg .rbp = UInt64.ofNat input.layout.stackTop :=
    (hsaved .rbp (by simp [SysV.calleeSaved])).trans hrbp
  have hr13_1 : s₁.core.readReg .r13 = UInt64.ofNat input.layout.stackTop :=
    (hsaved .r13 (by simp [SysV.calleeSaved])).trans hr13
  have hr14_1 : s₁.core.readReg .r14 = UInt64.ofNat input.layout.regionStart :=
    (hsaved .r14 (by simp [SysV.calleeSaved])).trans hr14
  have hslot1 : ∀ k < 5, s₁.core.memory.read64
      (UInt64.ofNat input.layout.stackTop + UInt64.ofNat (8 * k)) = UInt64.ofNat (ns[k]?.getD 0) := by
    intro k hk
    rw [← hslots k hk]
    apply Memory.readLittle_congr
    intro j hj
    rw [UInt64.add_assoc, ← UInt64.ofNat_add]
    exact hr.frame _ (plain_scratch_unmapped ce (plainAddr ce 8 10) s₀.core.memory.bytes s₀.flags
      s₀.core.registers (i := 8 * k + j) (by simp [Width.bytes] at hj; omega))
  -- block 8 terminator: cmp rsp, r13 (equal), jne not taken -> block 9 (3 steps)
  have hc8 : Condition.holds .ne .w64 (s₁.core.readReg .rsp) (s₁.core.readReg .r13) = false := by
    rw [hrsp, hr13_1]; simp [Condition.holds]
  obtain ⟨f1, e1⟩ := prun_cmpR ce (b := 8) (j := 10) (by decide) (by rw [PB.block_callInit]; rfl)
    (by rw [PB.block_callInit]) s₁.core s₁.flags hc8
  have e1' : ByteEval.run ce.bytes fetchBase 3 s₁ = .ok ⟨s₁.core, paddr ce 9 0, f1⟩ := by
    have hrip1 : s₁.rip = paddr ce 8 10 := hr.rip
    rw [show s₁ = ⟨s₁.core, paddr ce 8 10, s₁.flags⟩ from by rw [← hrip1]]; exact e1
  -- block 9: mov rsp, shellTop (1) + ifNz rax 33 10 (3) -> block 10
  have e2 := pstep_movI ce (b := 9) (j := 0) (by decide) (r := .rsp) (v := input.layout.shellTop)
    (by rw [PB.block_initBack]; rfl) s₁.core f1
  let k2 := s₁.core.setReg .rsp (UInt64.ofNat input.layout.shellTop)
  have hk2ax : k2.readReg .rax = 0 := hrax
  have e3 : ByteEval.run ce.bytes fetchBase 3 ⟨k2, paddr ce 9 1, f1⟩ =
      .ok ⟨k2, paddr ce 10 0, ByteEval.aluFlags .and .w64 0 0⟩ := by
    have h := prun_branch ce (b := 9) (by decide) (o := { mn := .test, w := .w64, form := .MR })
      (args := [.reg .rax, .reg .rax]) (cond := .ne) (yes := 33) (no := 10)
      (by rw [PB.block_initBack]; rfl) (s := ⟨k2, paddr ce 9 1, f1⟩) (by rw [PB.block_initBack]; rfl)
      (exec_test _ _ _ _) (taken := false) (by rw [test_ne_self, hk2ax]; rfl)
    rw [hk2ax] at h; exact h
  let f2 := ByteEval.aluFlags .and .w64 0 0
  -- block 10 instr 0: mov rdi, r14
  have e4 := pstep_movR ce (b := 10) (j := 0) (by decide) (d := .rdi) (s := .r14)
    (by rw [PB.block_callRoot]; rfl) k2 f2
  rw [show k2.readReg .r14 = UInt64.ofNat input.layout.regionStart from hr14_1] at e4
  let k3 := k2.setReg .rdi (UInt64.ofNat input.layout.regionStart)
  have hpre8 : ByteEval.run ce.bytes fetchBase 8 s₁ = .ok ⟨k3, paddr ce 10 1, f2⟩ :=
    run_comp e1' (run_comp (run_one e2) (run_comp e3 (run_one e4)))
  have hk3regs : ∀ r, r ≠ .rsp → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
      k3.readReg r = ((plainInitDriver ce s₀).withSite (plainRootSite ce s₀)).regs (ns.map UInt64.ofNat) r := by
    intro r hsp hsi hdx hcx hr8 hr9 hr10 hr11
    have h0 : s₁.core.registers .rax = 0 := hrax
    have h1 : s₁.core.registers .rbx = s₀.core.registers .rbx := hsaved .rbx (by simp [SysV.calleeSaved])
    have h2 : s₁.core.registers .rbp = s₀.core.registers .rbp := hsaved .rbp (by simp [SysV.calleeSaved])
    have h3 : s₁.core.registers .r12 = s₀.core.registers .r12 := hsaved .r12 (by simp [SysV.calleeSaved])
    have h4 : s₁.core.registers .r13 = s₀.core.registers .r13 := hsaved .r13 (by simp [SysV.calleeSaved])
    have h5 : s₁.core.registers .r14 = s₀.core.registers .r14 := hsaved .r14 (by simp [SysV.calleeSaved])
    have h6 : s₁.core.registers .r15 = s₀.core.registers .r15 := hsaved .r15 (by simp [SysV.calleeSaved])
    cases r with
    | rsp => exact absurd rfl hsp
    | rsi => exact absurd rfl hsi
    | rdx => exact absurd rfl hdx
    | rcx => exact absurd rfl hcx
    | r8 => exact absurd rfl hr8
    | r9 => exact absurd rfl hr9
    | r10 => exact absurd rfl hr10
    | r11 => exact absurd rfl hr11
    | rax => simp [k3, k2, Core.readReg, Core.setReg, Registers.set, Driver.withSite, Driver.regs, plainRootSite, h0]
    | rbx => simp [k3, k2, Core.readReg, Core.setReg, Registers.set, Driver.withSite, Driver.regs, plainRootSite, h1]
    | rbp => simp [k3, k2, Core.readReg, Core.setReg, Registers.set, Driver.withSite, Driver.regs, plainRootSite, h2]
    | rdi => simp [k3, Core.readReg, Core.setReg, Registers.set, Driver.withSite, Driver.regs, plainInitDriver, Layout.driverAt]
    | r12 => simp [k3, k2, Core.readReg, Core.setReg, Registers.set, Driver.withSite, Driver.regs, plainRootSite, h3]
    | r13 => simp [k3, k2, Core.readReg, Core.setReg, Registers.set, Driver.withSite, Driver.regs, plainRootSite, h4]
    | r14 => simp [k3, k2, Core.readReg, Core.setReg, Registers.set, Driver.withSite, Driver.regs, plainRootSite, h5]
    | r15 => simp [k3, k2, Core.readReg, Core.setReg, Registers.set, Driver.withSite, Driver.regs, plainRootSite, h6]
  rcases plain_glue_callRoot ce (ns := ns) (s₀ := s₀) (s₁ := s₁) (k3 := k3) (f2 := f2)
      rfl rfl hrbp1 hr13_1 hk3regs hslot1 with ⟨s₂, hrun8, hAt⟩ | ⟨m, hm, sm, f, hr', hf⟩
  · exact .inl ⟨s₂, run_comp hpre8 hrun8, hAt⟩
  · exact .inr ⟨8 + m, by unfold plainGlueSteps; omega, sm, f, run_comp hpre8 hr', hf⟩

/-- Handle a nonzero-status return from either `cx_init` (at `paddr ce 8 10`) or
`root` (at `paddr ce 10 10`): `cmp rsp, r13` (equal) → `initBack`/`rootBack` → `fail`. -/
private theorem plain_returned_fail {s₀ s' : ByteEval.State} {status : Nat}
    (hst : status ≠ 0) (hstLt : status < 2 ^ 64)
    (hr13 : s₀.core.readReg .r13 = UInt64.ofNat input.layout.stackTop)
    (hfile : ∀ i < ce.bytes.size, s₀.core.memory.bytes (UInt64.ofNat (fileBase + i)) = ce.bytes[i]!)
    (hret : Returned (plainInitDriver ce s₀) (plainInitDriver ce s₀).initBytes (UInt64.ofNat status) s' ∨
            Returned ((plainInitDriver ce s₀).withSite (plainRootSite ce s₀)) (plainInitDriver ce s₀).initBytes (UInt64.ofNat status) s')
    {n : Nat} {σ : List Sys} (ht : TraceN ce.bytes n s' σ) :
    ReportsMsg input.arity (failMessage (UInt64.ofNat status)) σ := by
  have hL := plainLayout_numbers ce
  have hsp : s'.core.readReg .rsp = UInt64.ofNat input.layout.stackTop := by
    rcases hret with hr | hr <;> exact hr.rsp.trans (plain_sp_add8 ce s₀)
  have hax : s'.core.readReg .rax = UInt64.ofNat status := by
    rcases hret with hr | hr <;> exact hr.rax
  have hr13' : s'.core.readReg .r13 = UInt64.ofNat input.layout.stackTop := by
    rcases hret with hr | hr
    · exact (hr.saved .r13 (by simp [SysV.calleeSaved])).trans hr13
    · have := hr.saved .r13 (by simp [SysV.calleeSaved])
      simpa [plainRootSite, Driver.withSite, Registers.set] using this.trans hr13
  have hfile' : ∀ i < ce.bytes.size, s'.core.memory.bytes (UInt64.ofNat (fileBase + i)) = ce.bytes[i]! := by
    intro i hi
    have hfr : s'.core.memory.bytes (UInt64.ofNat (fileBase + i)) =
        (plainInitDriver ce s₀).initBytes (UInt64.ofNat (fileBase + i)) := by
      rcases hret with hr | hr
      · exact hr.frame _ (plain_file_unmapped ce _ _ _ _ hi)
      · exact hr.frame _ (plain_file_unmapped ce _ _ _ _ hi)
    rw [hfr]
    have hinit : (plainInitDriver ce s₀).initBytes (UInt64.ofNat (fileBase + i)) =
        s₀.core.memory.bytes (UInt64.ofNat (fileBase + i)) := by
      unfold Driver.initBytes
      rw [plainInitDriver_ctx_sub48 ce s₀, write_bytes_apart]
      · rfl
      · intro j hj heq
        have hff := plainFileFacts ce
        have hd : dataBase = 268435456 := rfl
        have hfb : fileBase = 4194304 := rfl
        have h1 := congrArg UInt64.toNat heq
        have hbel := hff.below; rw [hff.size] at hi
        rw [show (16 : Word) = UInt64.ofNat 16 from rfl, UInt64.add_assoc, ← UInt64.ofNat_add,
          ← UInt64.ofNat_add, toNat_small (by omega), toNat_small (by simp [Width.bytes] at hj; omega)] at h1
        simp [Width.bytes] at hj; omega
    rw [hinit]
    exact hfile i hi
  have hcEq : Condition.holds .ne .w64 (s'.core.readReg .rsp) (s'.core.readReg .r13) = false := by
    rw [hsp, hr13']; simp [Condition.holds]
  have haxNe : (s'.core.readReg .rax != 0) = true := by
    rw [hax]
    have : UInt64.ofNat status ≠ 0 := ne_of_toNat (by rw [toNat_small hstLt]; exact hst)
    simpa using this
  rcases hret with hr | hr
  · -- returned from cx_init at paddr ce 8 10
    obtain ⟨f1, e1⟩ := prun_cmpR ce (b := 8) (j := 10) (by decide) (by rw [PB.block_callInit]; rfl)
      (by rw [PB.block_callInit]) s'.core s'.flags hcEq
    have e1' : ByteEval.run ce.bytes fetchBase 3 s' = .ok ⟨s'.core, paddr ce 9 0, f1⟩ := by
      have hrip : s'.rip = paddr ce 8 10 := hr.rip
      rw [show s' = ⟨s'.core, paddr ce 8 10, s'.flags⟩ from by rw [← hrip]]; exact e1
    have e2 := pstep_movI ce (b := 9) (j := 0) (by decide) (r := .rsp) (v := input.layout.shellTop)
      (by rw [PB.block_initBack]; rfl) s'.core f1
    let c2 := s'.core.setReg .rsp (UInt64.ofNat input.layout.shellTop)
    obtain ⟨f3, e3⟩ := prun_ifNz ce (b := 9) (j := 1) (by decide) (by rw [PB.block_initBack]; rfl)
      (by rw [PB.block_initBack]) c2 f1 (by change (s'.core.readReg .rax != 0) = true; exact haxNe)
    rcases TraceN.through (run_comp e1' (run_comp (run_one e2) e3)) ht with rfl | ⟨-, ht1⟩
    · exact writeSeq_nil 2 _ _
    have hp := plain_fail_path ce (core := c2) hfile' ht1
    rw [show c2.readReg .rax = UInt64.ofNat status from hax] at hp
    exact hp
  · -- returned from root at paddr ce 10 10
    obtain ⟨f1, e1⟩ := prun_cmpR ce (b := 10) (j := 10) (by decide) (by rw [PB.block_callRoot]; rfl)
      (by rw [PB.block_callRoot]) s'.core s'.flags hcEq
    have e1' : ByteEval.run ce.bytes fetchBase 3 s' = .ok ⟨s'.core, paddr ce 11 0, f1⟩ := by
      have hrip : s'.rip = paddr ce 10 10 := hr.rip
      rw [show s' = ⟨s'.core, paddr ce 10 10, s'.flags⟩ from by rw [← hrip]]; exact e1
    have e2 := pstep_movI ce (b := 11) (j := 0) (by decide) (r := .rsp) (v := input.layout.shellTop)
      (by rw [PB.block_rootBack]; rfl) s'.core f1
    let c2 := s'.core.setReg .rsp (UInt64.ofNat input.layout.shellTop)
    obtain ⟨f3, e3⟩ := prun_ifNz ce (b := 11) (j := 1) (by decide) (by rw [PB.block_rootBack]; rfl)
      (by rw [PB.block_rootBack]) c2 f1 (by change (s'.core.readReg .rax != 0) = true; exact haxNe)
    rcases TraceN.through (run_comp e1' (run_comp (run_one e2) e3)) ht with rfl | ⟨-, ht1⟩
    · exact writeSeq_nil 2 _ _
    have hp := plain_fail_path ce (core := c2) hfile' ht1
    rw [show c2.readReg .rax = UInt64.ofNat status from hax] at hp
    exact hp

/-- Helper for early-stop (`σ = []`) cases inside `plain_from_callInit`: any valid
`(D, site)` witnesses one of the 5 `objPlainCall` outcomes with empty trace `[]`. -/
private theorem plain_callInit_nil {roots : List Linked.Root} {r : Linked.Root}
    (hroot0 : roots[0]? = some r) (hrm : PlainRootMatches input r) {ns : List Nat}
    (D : Driver) (site : Driver.Site)
    (hD1 : D.Ok ce.plan.placement.textSize) (hD2 : (D.withSite site).Ok ce.plan.placement.textSize) :
    (∃ v, objPlainCall (linkedOf input.object roots) ce.plan.placement.textSize input.result ns (.value v) ∧
      PrintsResult input.result v []) ∨
    (objPlainCall (linkedOf input.object roots) ce.plan.placement.textSize input.result ns .notValue ∧
      ReportsMsg input.arity .notValue []) ∨
    (∃ m, objPlainCall (linkedOf input.object roots) ce.plan.placement.textSize input.result ns (.fail m) ∧
      ReportsMsg input.arity m []) ∨
    (objPlainCall (linkedOf input.object roots) ce.plan.placement.textSize input.result ns .timeout ∧ ([] : List Sys) = []) ∨
    objPlainCall (linkedOf input.object roots) ce.plan.placement.textSize input.result ns .stuck := by
  let L := linkedOf input.object roots D site
  have hmk : ∀ out, PlainCallMatches input.result (L.call r ns 0) out →
      objPlainCall (linkedOf input.object roots) ce.plan.placement.textSize input.result ns out :=
    fun out hm => ⟨D, site, r, 0, hroot0, hD1, hD2, hm⟩
  cases hres : L.call r ns 0 with
  | timeout => exact .inr (.inr (.inr (.inl ⟨hmk .timeout hres, rfl⟩)))
  | stuck => exact .inr (.inr (.inr (.inr (hmk .stuck hres))))
  | trap => exact .inr (.inr (.inl ⟨.trap, hmk (.fail .trap) hres, writeSeq_nil 2 _ _⟩))
  | resource f =>
    cases f with
    | heap => exact .inr (.inr (.inl ⟨.heap, hmk (.fail .heap) hres, writeSeq_nil 2 _ _⟩))
    | stack => exact .inr (.inr (.inl ⟨.stack, hmk (.fail .stack) hres, writeSeq_nil 2 _ _⟩))
    | natOverflow => exact .inr (.inr (.inl ⟨.natOverflow, hmk (.fail .natOverflow) hres, writeSeq_nil 2 _ _⟩))
  | ok o =>
    cases o with
    | none =>
      refine .inr (.inl ⟨hmk .notValue ?_, writeSeq_nil 2 _ _⟩)
      cases input.result <;> exact .inl hres
    | some obs =>
      cases hkind : input.result with
      | nat =>
        rw [hkind] at hmk
        cases obs with
        | nat v =>
          by_cases hv : v < 2 ^ 63
          · exact .inl ⟨v, hmk (.value v) ⟨hres, hv⟩, writeSeq_nil 1 0 _⟩
          · exfalso
            unfold LinkedAt.call at hres
            split at hres
            · cases h1 : L.linked.initCall 0 <;> simp [h1, Sem.Result.bind] at hres
              rename_i p1
              cases h2 : L.rootCall r ns p1.2.bytes 0 <;> simp [h2, Sem.Result.bind, Sem.Result.map] at hres
              rename_i p2
              obtain ⟨_, _, htyM⟩ := hrm
              rw [hkind] at htyM
              obtain ⟨sig, hty⟩ := htyM
              simp only [Linked.observe, hty, Rt.readback] at hres
              split at hres
              · cases hres
                have := plain_shr1_toNat p2.1
                have : p2.1.toNat < 2 ^ 64 := p2.1.toBitVec.isLt
                omega
              · cases hres
            · cases hres
        | ctor c fs =>
          exact .inr (.inl ⟨hmk .notValue (.inr ⟨.ctor c fs, hres, fun _ h => by cases h⟩),
            writeSeq_nil 2 _ _⟩)
        | word w =>
          exact .inr (.inl ⟨hmk .notValue (.inr ⟨.word w, hres, fun _ h => by cases h⟩),
            writeSeq_nil 2 _ _⟩)
        | bytes bs =>
          exact .inr (.inl ⟨hmk .notValue (.inr ⟨.bytes bs, hres, fun _ h => by cases h⟩),
            writeSeq_nil 2 _ _⟩)
      | enum k =>
        rw [hkind] at hmk
        cases obs with
        | ctor c fs =>
          by_cases hck : fs = [] ∧ c < k
          · rcases hck with ⟨rfl, hclt⟩
            exact .inl ⟨c, hmk (.value c) ⟨hres, hclt⟩, writeSeq_nil 1 0 _⟩
          · exact .inr (.inl ⟨hmk .notValue (.inr ⟨.ctor c fs, hres, fun c' hc' heq => by cases heq; exact hck ⟨rfl, hc'⟩⟩),
              writeSeq_nil 2 _ _⟩)
        | nat v =>
          exact .inr (.inl ⟨hmk .notValue (.inr ⟨.nat v, hres, fun _ _ h => by cases h⟩),
            writeSeq_nil 2 _ _⟩)
        | word w =>
          exact .inr (.inl ⟨hmk .notValue (.inr ⟨.word w, hres, fun _ _ h => by cases h⟩),
            writeSeq_nil 2 _ _⟩)
        | bytes bs =>
          exact .inr (.inl ⟨hmk .notValue (.inr ⟨.bytes bs, hres, fun _ _ h => by cases h⟩),
            writeSeq_nil 2 _ _⟩)

/-- Second half of `plain_from_callInit`, taking `s₀` (at `paddr ce 8 9`, ready to
call `cx_init`) as an opaque parameter so `two_calls` never expands the block-8
register setup chain. -/
private theorem plain_from_initCall_at {roots : List Linked.Root} {r : Linked.Root}
    (hroot0 : roots[0]? = some r) (hrm : PlainRootMatches input r)
    {ns : List Nat} (hnsLen : ns.length = input.arity) (hnsLt : ∀ x ∈ ns, x < 2 ^ 64)
    {s₀ : ByteEval.State}
    (hrbp : s₀.core.readReg .rbp = UInt64.ofNat input.layout.stackTop)
    (hr13 : s₀.core.readReg .r13 = UInt64.ofNat input.layout.stackTop)
    (hr14 : s₀.core.readReg .r14 = UInt64.ofNat input.layout.regionStart)
    (hinitBytesEq : (plainInitDriver ce s₀).initBytes = s₀.core.memory.bytes)
    (hslots0 : ∀ k < 5, wordOf (plainInitDriver ce s₀).initBytes
      (UInt64.ofNat input.layout.stackTop + UInt64.ofNat (8 * k)) = UInt64.ofNat (ns[k]?.getD 0))
    (hfile0 : ∀ i < ce.bytes.size, s₀.core.memory.bytes (UInt64.ofNat (fileBase + i)) = ce.bytes[i]!)
    (hAtInit : AtCall ce.bytes input.object
      (linkedOf input.object roots (plainInitDriver ce s₀) (plainRootSite ce s₀)).linked.init
      (plainInitDriver ce s₀)
      [(plainInitDriver ce s₀).size, (plainInitDriver ce s₀).budget]
      (plainInitDriver ce s₀).initBytes s₀)
    {k : Nat} {σ : List Sys} (ht1 : TraceN ce.bytes k s₀ σ) :
    (∃ v, objPlainCall (linkedOf input.object roots) ce.plan.placement.textSize input.result ns (.value v) ∧
      PrintsResult input.result v σ) ∨
    (objPlainCall (linkedOf input.object roots) ce.plan.placement.textSize input.result ns .notValue ∧
      ReportsMsg input.arity .notValue σ) ∨
    (∃ m, objPlainCall (linkedOf input.object roots) ce.plan.placement.textSize input.result ns (.fail m) ∧
      ReportsMsg input.arity m σ) ∨
    (objPlainCall (linkedOf input.object roots) ce.plan.placement.textSize input.result ns .timeout ∧ σ = []) ∨
    objPlainCall (linkedOf input.object roots) ce.plan.placement.textSize input.result ns .stuck := by
  have hff := plainFileFacts ce
  let D0 := plainInitDriver ce s₀
  let L : LinkedAt := linkedOf input.object roots D0 (plainRootSite ce s₀)
  have hD1 : D0.Ok ce.plan.placement.textSize := plainInitDriver_ok ce s₀
  have hD2 : L.rootDriver.Ok ce.plan.placement.textSize := plainRootDriver_ok ce s₀
  obtain ⟨text, htext, htw, hfit⟩ := plain_file_text ce
  have hnsAll : ns.all (· < 2 ^ 64) = true := List.all_eq_true.mpr fun x hx => decide_eq_true (hnsLt x hx)
  have hglue := plain_glue ce (ns := ns) (by have := hff.arity; omega) (s₀ := s₀) hrbp hr13 hr14 hslots0
  rw [← hrm.1] at hglue
  have hlift := two_calls (image := ce.bytes) (text := text) (textOffset := ce.plan.placement.textOffset)
    (L := L) htext htw hfit hD1 hD2 rfl (r := r) (ns := ns) hnsAll hAtInit hglue k
  have hmk : ∀ out, PlainCallMatches input.result (L.call r ns k) out →
      objPlainCall (linkedOf input.object roots) ce.plan.placement.textSize input.result ns out :=
    fun out hm => ⟨D0, plainRootSite ce s₀, r, k, hroot0, hD1, hD2, hm⟩
  cases hcall : L.call r ns k with
  | timeout =>
    rw [hcall] at hlift
    rcases hlift with ⟨s', hr'⟩ | hf
    · rcases TraceN.through hr' ht1 with rfl | ⟨hle, -⟩
      · exact .inr (.inr (.inr (.inl ⟨hmk .timeout hcall, rfl⟩)))
      · omega
    · have hnil' := TraceN.nil_of_faults hf ht1
      exact .inr (.inr (.inr (.inl ⟨hmk .timeout hcall, hnil'⟩)))
  | stuck =>
    exact .inr (.inr (.inr (.inr (hmk .stuck hcall))))
  | trap =>
    rw [hcall] at hlift
    rcases hlift with ⟨m', s', _, hr', hret⟩ | hf
    · rcases TraceN.through hr' ht1 with rfl | ⟨-, ht2⟩
      · exact .inr (.inr (.inl ⟨.trap, hmk (.fail .trap) hcall, writeSeq_nil 2 _ _⟩))
      have hrep := plain_returned_fail ce (status := 4) (by decide) (by decide) hr13 hfile0 hret ht2
      exact .inr (.inr (.inl ⟨.trap, hmk (.fail .trap) hcall, hrep⟩))
    · have hnil' := TraceN.nil_of_faults hf ht1
      subst hnil'
      exact .inr (.inr (.inl ⟨.trap, hmk (.fail .trap) hcall, writeSeq_nil 2 _ _⟩))
  | resource f =>
    rw [hcall] at hlift
    rcases hlift with ⟨m', s', _, hr', hret⟩ | hf
    · rcases TraceN.through hr' ht1 with rfl | ⟨-, ht2⟩
      · cases f with
        | heap => exact .inr (.inr (.inl ⟨.heap, hmk (.fail .heap) hcall, writeSeq_nil 2 _ _⟩))
        | stack => exact .inr (.inr (.inl ⟨.stack, hmk (.fail .stack) hcall, writeSeq_nil 2 _ _⟩))
        | natOverflow => exact .inr (.inr (.inl ⟨.natOverflow, hmk (.fail .natOverflow) hcall, writeSeq_nil 2 _ _⟩))
      cases f with
      | heap =>
        have hrep := plain_returned_fail ce (status := 1) (by decide) (by decide) hr13 hfile0 hret ht2
        exact .inr (.inr (.inl ⟨.heap, hmk (.fail .heap) hcall, hrep⟩))
      | stack =>
        have hrep := plain_returned_fail ce (status := 2) (by decide) (by decide) hr13 hfile0 hret ht2
        exact .inr (.inr (.inl ⟨.stack, hmk (.fail .stack) hcall, hrep⟩))
      | natOverflow =>
        have hrep := plain_returned_fail ce (status := 3) (by decide) (by decide) hr13 hfile0 hret ht2
        exact .inr (.inr (.inl ⟨.natOverflow, hmk (.fail .natOverflow) hcall, hrep⟩))
    · have hnil' := TraceN.nil_of_faults hf ht1
      subst hnil'
      cases f with
      | heap => exact .inr (.inr (.inl ⟨.heap, hmk (.fail .heap) hcall, writeSeq_nil 2 _ _⟩))
      | stack => exact .inr (.inr (.inl ⟨.stack, hmk (.fail .stack) hcall, writeSeq_nil 2 _ _⟩))
      | natOverflow => exact .inr (.inr (.inl ⟨.natOverflow, hmk (.fail .natOverflow) hcall, writeSeq_nil 2 _ _⟩))
  | ok obsOpt =>
    rw [hcall] at hlift
    rcases hlift with ⟨m', s', w, memRes, _, hr', hret, hrdx, hbytesRes, hobsEq⟩ | hf
    · have hfile' : ∀ i < ce.bytes.size, s'.core.memory.bytes (UInt64.ofNat (fileBase + i)) = ce.bytes[i]! := by
        intro i hi
        rw [hret.frame _ (plain_file_unmapped ce _ _ _ _ hi)]
        change D0.initBytes _ = _
        rw [hinitBytesEq]
        exact hfile0 i hi
      have hrbp' : s'.core.readReg .rbp = UInt64.ofNat input.layout.stackTop := by
        have := hret.saved .rbp (by simp [SysV.calleeSaved])
        simpa [plainRootSite, Driver.withSite, Registers.set] using this.trans hrbp
      have hr13' : s'.core.readReg .r13 = UInt64.ofNat input.layout.stackTop := by
        have := hret.saved .r13 (by simp [SysV.calleeSaved])
        simpa [plainRootSite, Driver.withSite, Registers.set] using this.trans hr13
      have hsp' : s'.core.readReg .rsp = UInt64.ofNat input.layout.stackTop :=
        hret.rsp.trans (plain_sp_add8 ce s₀)
      have hc10 : Condition.holds .ne .w64 (s'.core.readReg .rsp) (s'.core.readReg .r13) = false := by
        rw [hsp', hr13']; simp [Condition.holds]
      obtain ⟨f10, e10⟩ := prun_cmpR ce (b := 10) (j := 10) (by decide) (by rw [PB.block_callRoot]; rfl)
        (by rw [PB.block_callRoot]) s'.core s'.flags hc10
      have e10' : ByteEval.run ce.bytes fetchBase 3 s' = .ok ⟨s'.core, paddr ce 11 0, f10⟩ := by
        have hrip : s'.rip = paddr ce 10 10 := hret.rip
        rw [show s' = ⟨s'.core, paddr ce 10 10, s'.flags⟩ from by rw [← hrip]]; exact e10
      have e11 := pstep_movI ce (b := 11) (j := 0) (by decide) (r := .rsp) (v := input.layout.shellTop)
        (by rw [PB.block_rootBack]; rfl) s'.core f10
      let c11 := s'.core.setReg .rsp (UInt64.ofNat input.layout.shellTop)
      have hax0 : (c11.readReg .rax != 0) = false := by
        change (s'.core.readReg .rax != 0) = false; rw [hret.rax]; rfl
      obtain ⟨f12, e12⟩ := prun_ifNz ce (b := 11) (j := 1) (by decide) (by rw [PB.block_rootBack]; rfl)
        (by rw [PB.block_rootBack]) c11 f10 hax0
      have hto12 := run_comp hr' (run_comp e10' (run_comp (run_one e11) e12))
      have hvalidObs : (w.toNat % 2 = 1 ∧ (match input.result with | .nat => True | .enum k => w.toNat / 2 < k)) →
          PlainCallMatches input.result (.ok obsOpt) (.value (w.toNat / 2)) := by
        intro hv
        have hwlt : w.toNat < 2 ^ 64 := w.toBitVec.isLt
        obtain ⟨_, _, htyM⟩ := hrm
        cases hkind : input.result with
        | nat =>
          rw [hkind] at htyM
          obtain ⟨sig, hty⟩ := htyM
          have hobs : obsOpt = some (.nat (w.toNat / 2)) := by
            rw [← hobsEq]; unfold Linked.observe; rw [hty]
            exact (readback_nat_iff sig _ _ w).1 hv.1
          exact ⟨by rw [hobs], by omega⟩
        | enum cnt =>
          rw [hkind] at htyM hv
          obtain ⟨sig, idx, ctors, hty, hinds, hlen, hemp⟩ := htyM
          have hobs : obsOpt = some (.ctor (w.toNat / 2) []) := by
            rw [← hobsEq]; unfold Linked.observe; rw [hty]
            exact (readback_enum_iff hinds hlen hemp _ _ w).1 hv
          exact ⟨by rw [hobs], hv.2⟩
      have hbadObs : ¬ (w.toNat % 2 = 1 ∧ (match input.result with | .nat => True | .enum k => w.toNat / 2 < k)) →
          PlainCallMatches input.result (.ok obsOpt) .notValue := by
        intro hnot
        obtain ⟨_, _, htyM⟩ := hrm
        cases hkind : input.result with
        | nat =>
          rw [hkind] at htyM hnot
          obtain ⟨sig, hty⟩ := htyM
          have hobs : obsOpt = none := by
            rw [← hobsEq]; unfold Linked.observe; rw [hty]
            exact (readback_nat_iff sig _ _ w).2 (fun h => hnot ⟨h, trivial⟩)
          exact .inl (by rw [hobs])
        | enum cnt =>
          rw [hkind] at htyM hnot
          obtain ⟨sig, idx, ctors, hty, hinds, hlen, hemp⟩ := htyM
          have hobs : obsOpt = none := by
            rw [← hobsEq]; unfold Linked.observe; rw [hty]
            exact (readback_enum_iff hinds hlen hemp _ _ w).2 hnot
          exact .inl (by rw [hobs])
      by_cases hv : w.toNat % 2 = 1 ∧ (match input.result with | .nat => True | .enum k => w.toNat / 2 < k)
      · have hvB : plainResultOk input.result w = true := by
          unfold plainResultOk
          cases hrk : input.result with
          | nat => simp [hrk] at hv; simp [hv]
          | enum k => simp [hrk] at hv; simp [hv.1, hv.2]
        rcases TraceN.through hto12 ht1 with rfl | ⟨-, ht12⟩
        · exact .inl ⟨w.toNat / 2, hmk (.value (w.toNat / 2)) (by rw [hcall]; exact hvalidObs hv),
            writeSeq_nil 1 0 _⟩
        have hres := plain_result_path ce (core := c11) (fl := f12) hrbp' rfl hfile' ht12
        have hdxW : c11.readReg .rdx = w := hrdx
        simp only [hdxW, hvB, ↓reduceIte] at hres
        exact .inl ⟨w.toNat / 2, hmk (.value (w.toNat / 2)) (by rw [hcall]; exact hvalidObs hv), hres⟩
      · have hvB : plainResultOk input.result w = false := by
          unfold plainResultOk
          cases hrk : input.result with
          | nat => simp [hrk] at hv; simp [hv]
          | enum k =>
            simp only [hrk] at hv
            by_cases h1 : w.toNat % 2 = 1
            · have h2 : ¬ (w.toNat / 2 < k) := fun hlt => hv ⟨h1, hlt⟩
              simp [h1, h2]
            · simp [h1]
        rcases TraceN.through hto12 ht1 with rfl | ⟨-, ht12⟩
        · exact .inr (.inl ⟨hmk .notValue (by rw [hcall]; exact hbadObs hv), writeSeq_nil 2 _ _⟩)
        have hres := plain_result_path ce (core := c11) (fl := f12) hrbp' rfl hfile' ht12
        have hdxW : c11.readReg .rdx = w := hrdx
        simp only [hdxW, hvB, Bool.false_eq_true, ↓reduceIte] at hres
        exact .inr (.inl ⟨hmk .notValue (by rw [hcall]; exact hbadObs hv), hres⟩)
    · have hnil' := TraceN.nil_of_faults hf ht1
      subst hnil'
      exact plain_callInit_nil ce hroot0 hrm D0 (plainRootSite ce s₀) hD1 hD2

/-- From `B.callInit` (block 8) with parsed `ns`, execute `cx_init` and `root`
via `two_calls` and handle every outcome. -/
private theorem plain_from_callInit {roots : List Linked.Root} {r : Linked.Root}
    (hroot0 : roots[0]? = some r) (hrm : PlainRootMatches input r)
    {ns : List Nat} (hnsLen : ns.length = input.arity) (hnsLt : ∀ x ∈ ns, x < 2 ^ 64)
    {core : Core} {fl : ByteEval.Flags}
    (hrbp : core.readReg .rbp = UInt64.ofNat input.layout.stackTop)
    (hr13 : core.readReg .r13 = UInt64.ofNat input.layout.stackTop)
    (hr14 : core.readReg .r14 = UInt64.ofNat input.layout.regionStart)
    (hslots : ∀ k < 5, core.memory.read64 (UInt64.ofNat input.layout.stackTop + UInt64.ofNat (8 * k)) =
      UInt64.ofNat (ns[k]?.getD 0))
    (hfile : ∀ i < ce.bytes.size, core.memory.bytes (UInt64.ofNat (fileBase + i)) = ce.bytes[i]!)
    {n : Nat} {σ : List Sys} (ht : TraceN ce.bytes n ⟨core, paddr ce 8 0, fl⟩ σ) :
    (∃ v, objPlainCall (linkedOf input.object roots) ce.plan.placement.textSize input.result ns (.value v) ∧
      PrintsResult input.result v σ) ∨
    (objPlainCall (linkedOf input.object roots) ce.plan.placement.textSize input.result ns .notValue ∧
      ReportsMsg input.arity .notValue σ) ∨
    (∃ m, objPlainCall (linkedOf input.object roots) ce.plan.placement.textSize input.result ns (.fail m) ∧
      ReportsMsg input.arity m σ) ∨
    (objPlainCall (linkedOf input.object roots) ce.plan.placement.textSize input.result ns .timeout ∧ σ = []) ∨
    objPlainCall (linkedOf input.object roots) ce.plan.placement.textSize input.result ns .stuck := by
  have hff := plainFileFacts ce
  have hL := plainLayout_numbers ce
  have hd : dataBase = 268435456 := rfl
  -- block 8 instrs 0..8: budget store + regs for cx_init
  have e0 := pstep_movI ce (b := 8) (j := 0) (by decide) (r := .rax) (v := input.layout.budget)
    (by rw [PB.block_callInit]; rfl) core fl
  let c0 := core.setReg .rax (UInt64.ofNat input.layout.budget)
  let sDummy : ByteEval.State := ⟨core, paddr ce 8 9, fl⟩
  have hnil := plain_callInit_nil ce hroot0 hrm (ns := ns) (plainInitDriver ce sDummy) (plainRootSite ce sDummy)
    (plainInitDriver_ok ce sDummy) (plainRootDriver_ok ce sDummy)
  rcases TraceN.through (run_one e0) ht with rfl | ⟨-, ht0⟩
  · exact hnil
  rcases pstep_store64 ce (b := 8) (j := 1) (by decide) (by rw [PB.block_callInit]; rfl) c0 fl with
    ⟨mem1, hw1, e1⟩ | ⟨_, efault⟩
  · let c1 : Core := { c0 with memory := mem1 }
    have e2 := pstep_movR ce (b := 8) (j := 2) (by decide) (d := .rdi) (s := .r14) (by rw [PB.block_callInit]; rfl) c1 fl
    rw [show c1.readReg .r14 = UInt64.ofNat input.layout.regionStart from hr14] at e2
    let c2 := c1.setReg .rdi (UInt64.ofNat input.layout.regionStart)
    have e3 := pstep_movI ce (b := 8) (j := 3) (by decide) (r := .rsi) (v := input.layout.region) (by rw [PB.block_callInit]; rfl) c2 fl
    let c3 := c2.setReg .rsi (UInt64.ofNat input.layout.region)
    have e4 := pstep_movI ce (b := 8) (j := 4) (by decide) (r := .rdx) (v := input.layout.budget) (by rw [PB.block_callInit]; rfl) c3 fl
    let c4 := c3.setReg .rdx (UInt64.ofNat input.layout.budget)
    have e5 := pstep_movI ce (b := 8) (j := 5) (by decide) (r := .rcx) (v := 0) (by rw [PB.block_callInit]; rfl) c4 fl
    let c5 := c4.setReg .rcx 0
    have e6 := pstep_movI ce (b := 8) (j := 6) (by decide) (r := .r8) (v := 0) (by rw [PB.block_callInit]; rfl) c5 fl
    let c6 := c5.setReg .r8 0
    have e7 := pstep_movI ce (b := 8) (j := 7) (by decide) (r := .r9) (v := 0) (by rw [PB.block_callInit]; rfl) c6 fl
    let c7 := c6.setReg .r9 0
    have e8 := pstep_movR ce (b := 8) (j := 8) (by decide) (d := .rsp) (s := .r13) (by rw [PB.block_callInit]; rfl) c7 fl
    rw [show c7.readReg .r13 = UInt64.ofNat input.layout.stackTop from hr13] at e8
    let c8 := c7.setReg .rsp (UInt64.ofNat input.layout.stackTop)
    have hrun8 := run_comp (run_one e1) (run_comp (run_one e2) (run_comp (run_one e3)
      (run_comp (run_one e4) (run_comp (run_one e5) (run_comp (run_one e6) (run_comp (run_one e7) (run_one e8)))))))
    rcases TraceN.through hrun8 ht0 with rfl | ⟨-, ht1⟩
    · exact hnil
    let s₀ : ByteEval.State := ⟨c8, paddr ce 8 9, fl⟩
    let D0 := plainInitDriver ce s₀
    have hmem1Eq : mem1 = core.memory.write .w64 (UInt64.ofNat input.layout.regionStart + 16)
        (UInt64.ofNat input.layout.budget) := by
      have heval : (SB.at_ .r14 16).eval c0 = UInt64.ofNat input.layout.regionStart + 16 := by
        rw [eval_at c0 .r14 (by decide)]; exact congrArg (· + 16) hr14
      rw [heval] at hw1; exact write?_ok hw1
    have hinitBytesEq : D0.initBytes = s₀.core.memory.bytes := by
      unfold Driver.initBytes
      rw [plainInitDriver_ctx_sub48 ce s₀]
      funext a
      have hbud : D0.budget = UInt64.ofNat input.layout.budget := rfl
      have hinit : D0.init = mem1.bytes := rfl
      change _ = mem1.bytes a
      rw [hbud, hinit, hmem1Eq]
      exact congrFun (write_twice_bytes core.memory (fun _ => true) (fun _ => true)
        (UInt64.ofNat input.layout.regionStart + 16) (UInt64.ofNat input.layout.budget)) a
    have hslots0 : ∀ k < 5, wordOf D0.initBytes (UInt64.ofNat input.layout.stackTop + UInt64.ofNat (8 * k)) =
        UInt64.ofNat (ns[k]?.getD 0) := by
      intro k hk
      rw [hinitBytesEq]
      show mem1.read64 _ = _
      rw [hmem1Eq, write_read64_apart]
      · exact hslots k hk
      · intro b1 hb1 b2 hb2 heq
        have h1 := congrArg UInt64.toNat heq
        rw [show (16 : Word) = UInt64.ofNat 16 from rfl,
          UInt64.add_assoc, UInt64.add_assoc, ← UInt64.ofNat_add, ← UInt64.ofNat_add,
          ← UInt64.ofNat_add, ← UInt64.ofNat_add,
          toNat_small (by omega), toNat_small (by simp [Width.bytes] at hb2; omega)] at h1
        simp [Width.bytes] at hb2; omega
    have hfile0 : ∀ i < ce.bytes.size, s₀.core.memory.bytes (UInt64.ofNat (fileBase + i)) = ce.bytes[i]! := by
      intro i hi
      change mem1.bytes _ = _
      rw [hmem1Eq, write_bytes_apart]
      · exact hfile i hi
      · intro j hj heq
        have hbel := hff.below; rw [hff.size] at hi
        have hfb : fileBase = 4194304 := rfl
        have h1 := congrArg UInt64.toNat heq
        rw [show (16 : Word) = UInt64.ofNat 16 from rfl,
          UInt64.add_assoc, ← UInt64.ofNat_add, ← UInt64.ofNat_add,
          toNat_small (by omega), toNat_small (by simp [Width.bytes] at hj; omega)] at h1
        simp [Width.bytes] at hj; omega
    obtain ⟨offInit, hoffInit, hcallsInit⟩ := pcallsTo ce (b := 8) (j := 9) (by decide)
      (by rw [PB.block_callInit]; rfl) (s := s₀) rfl
    have hAtInit : AtCall ce.bytes input.object
        (linkedOf input.object roots D0 (plainRootSite ce s₀)).linked.init
        D0 [D0.size, D0.budget] D0.initBytes s₀ := by
      refine ⟨⟨offInit, hoffInit, hcallsInit⟩, ?_, ?_, ?_, hinitBytesEq.symm, rfl⟩
      · show UInt64.ofNat (plainAddr ce 8 10) = paddr ce 8 9 + 5
        exact (next_addr (p := plainShellOf ce) (origin := ce.plan.placement.shellOffset) (b := 8)
          (j := 9) (i := .callExport initSymbol) (by rw [PB.block_callInit]; rfl)).symm
      · intro reg hreg
        cases reg <;> simp [Driver.core, Driver.regs, D0, plainInitDriver, Layout.driverAt, s₀,
          c8, c7, c6, c5, c4, c3, c2, c1, c0, Core.readReg, Core.setReg, Registers.set] at hreg ⊢
      · show c8.readReg .rsp = D0.sp + 8
        rw [show c8.readReg .rsp = UInt64.ofNat input.layout.stackTop from rfl]
        exact (plain_sp_add8 ce s₀).symm
    exact plain_from_initCall_at ce hroot0 hrm hnsLen hnsLt hrbp hr13 hr14 hinitBytesEq hslots0 hfile0 hAtInit ht1
  · have := TraceN.nil_of_step_fault efault ht0
    subst this
    exact hnil

/-! ## Step 4: Top-level `plain_shell_sound` and `plain_shell_unspecified` -/

/-- **The plain `--exe` shell theorem**: for every executable `X86.Exe.writeChecked`
made, run from `Process.Loaded` with `ArgsOk args` under `Process.Syscall` and
`Process.Step`, every finite trace of the process satisfies `PlainShows`. -/
theorem plain_shell_sound {roots : List Linked.Root} {r : Linked.Root}
    (hroot0 : roots[0]? = some r) (hrm : PlainRootMatches input r)
    {args : List (List Nat)} (hargs : ArgsOk args)
    {s₀ : ByteEval.State} (hload : Loaded (Certified.checked ce) args s₀)
    {σ : List Sys} (hσ : Trace ce.bytes s₀ σ) :
    PlainShows (linkedOf input.object roots) ce.plan.placement.textSize input.arity input.result
      (fileBase + ce.plan.placement.dataOffset) args σ := by
  obtain ⟨n, ht0⟩ := Trace.toN hσ
  obtain ⟨hrip0, hfile0, hab0⟩ := hload
  have hrip0' : s₀.rip = paddr ce 0 0 := hrip0.trans (plain_entry_addr ce)
  have ht0' : TraceN ce.bytes n ⟨s₀.core, paddr ce 0 0, s₀.flags⟩ σ := by
    have : s₀ = ⟨s₀.core, paddr ce 0 0, s₀.flags⟩ := by cases s₀; cases hrip0'; rfl
    rwa [← this]
  rcases plain_confine_run ce s₀.core s₀.flags hfile0 ht0' with
    href | hpre | ⟨core2, fl2, n2, σ2, rfl, ht2, hmem2, hrsp2⟩
  · exact .inl href
  · exact .inr (.inl hpre)
  -- Now at `B.args` (block 2) with `core2.memory = s₀.core.memory` and `core2.readReg .rsp = s₀.core.readReg .rsp`
  let sp0 := s₀.core.readReg .rsp
  have hfile2 : ∀ i < ce.bytes.size, core2.memory.bytes (UInt64.ofNat (fileBase + i)) = ce.bytes[i]! := by
    rw [hmem2]; exact hfile0
  have hab2 : ArgBlock core2.memory sp0 args (fun a => OutsideSegments input.layout.segments a ∧ CanonicalUser a) := by
    rw [hmem2]; exact hab0
  have hff := plainFileFacts ce
  have hL := plainLayout_numbers ce
  have hd : dataBase = 268435456 := rfl
  -- Execute block 2 (`args`): ld rbx, [rsp]; lea r12, [rsp+8]; mov rsp, shellTop; mov rbp, stackTop;
  -- mov rax, 0; st [rbp+0..32], rax; mov r14, regionStart; mov r13, stackTop; cmp rbx, arity+1
  have hnil_start : PlainShows (linkedOf input.object roots) ce.plan.placement.textSize input.arity
      input.result (fileBase + ce.plan.placement.dataOffset) args
      (started (fileBase + ce.plan.placement.dataOffset) ++ []) := by
    rw [List.append_nil]; exact .inr (.inl (List.prefix_refl _))
  rcases pstep_load64 ce (b := 2) (j := 0) (by decide) (by rw [PB.block_args]; rfl) core2 fl2 with
    ⟨argcW, hargcW, e0⟩ | ⟨_, efault⟩
  · let a1 := core2.setReg .rbx argcW
    have e1 := pstep_lea ce (b := 2) (j := 1) (by decide) (by rw [PB.block_args]; rfl) a1 fl2
    let a2 := a1.setReg .r12 ((SB.at_ .rsp 8).eval a1)
    have e2 := pstep_movI ce (b := 2) (j := 2) (by decide) (r := .rsp) (v := input.layout.shellTop) (by rw [PB.block_args]; rfl) a2 fl2
    let a3 := a2.setReg .rsp (UInt64.ofNat input.layout.shellTop)
    have e3 := pstep_movI ce (b := 2) (j := 3) (by decide) (r := .rbp) (v := input.layout.stackTop) (by rw [PB.block_args]; rfl) a3 fl2
    let a4 := a3.setReg .rbp (UInt64.ofNat input.layout.stackTop)
    have e4 := pstep_movI ce (b := 2) (j := 4) (by decide) (r := .rax) (v := 0) (by rw [PB.block_args]; rfl) a4 fl2
    let a5 := a4.setReg .rax 0
    rcases TraceN.through (run_comp (run_one e0) (run_comp (run_one e1) (run_comp (run_one e2)
        (run_comp (run_one e3) (run_one e4))))) ht2 with rfl | ⟨-, ht3⟩
    · exact hnil_start
    -- 5 zero stores at [rbp+0..32]
    rcases pstep_store64 ce (b := 2) (j := 5) (by decide) (by rw [PB.block_args]; rfl) a5 fl2 with
      ⟨m0, hm0, s0⟩ | ⟨_, ef⟩
    · let b0 : Core := { a5 with memory := m0 }
      rcases pstep_store64 ce (b := 2) (j := 6) (by decide) (by rw [PB.block_args]; rfl) b0 fl2 with
        ⟨m1, hm1, s1⟩ | ⟨_, ef⟩
      · let b1 : Core := { b0 with memory := m1 }
        rcases pstep_store64 ce (b := 2) (j := 7) (by decide) (by rw [PB.block_args]; rfl) b1 fl2 with
          ⟨m2, hm2, s2⟩ | ⟨_, ef⟩
        · let b2 : Core := { b1 with memory := m2 }
          rcases pstep_store64 ce (b := 2) (j := 8) (by decide) (by rw [PB.block_args]; rfl) b2 fl2 with
            ⟨m3, hm3, s3⟩ | ⟨_, ef⟩
          · let b3 : Core := { b2 with memory := m3 }
            rcases pstep_store64 ce (b := 2) (j := 9) (by decide) (by rw [PB.block_args]; rfl) b3 fl2 with
              ⟨m4, hm4, s4⟩ | ⟨_, ef⟩
            · let b4 : Core := { b3 with memory := m4 }
              have e10 := pstep_movI ce (b := 2) (j := 10) (by decide) (r := .r14) (v := input.layout.regionStart)
                (by rw [PB.block_args]; rfl) b4 fl2
              let b5 := b4.setReg .r14 (UInt64.ofNat input.layout.regionStart)
              have e11 := pstep_movI ce (b := 2) (j := 11) (by decide) (r := .r13) (v := input.layout.stackTop)
                (by rw [PB.block_args]; rfl) b5 fl2
              let b6 := b5.setReg .r13 (UInt64.ofNat input.layout.stackTop)
              rcases TraceN.through (run_comp (run_one s0) (run_comp (run_one s1) (run_comp (run_one s2)
                  (run_comp (run_one s3) (run_comp (run_one s4) (run_comp (run_one e10) (run_one e11))))))) ht3 with
                rfl | ⟨-, ht4⟩
              · exact hnil_start
              have hevalRbp : ∀ (c : Core) (d : Nat), c.readReg .rbp = UInt64.ofNat input.layout.stackTop →
                  d < 2 ^ 31 → (SB.at_ .rbp d).eval c = UInt64.ofNat input.layout.stackTop + UInt64.ofNat d := by
                intro c d hrb hd'; rw [eval_at c .rbp (plain_signExtend32_ofNat hd'), hrb]
              have heqM0 : m0 = core2.memory.write .w64 (UInt64.ofNat input.layout.stackTop + UInt64.ofNat 0) 0 := by
                rw [hevalRbp a5 0 rfl (by decide)] at hm0; exact write?_ok hm0
              have heqM1 : m1 = m0.write .w64 (UInt64.ofNat input.layout.stackTop + UInt64.ofNat 8) 0 := by
                rw [hevalRbp b0 8 rfl (by decide)] at hm1; exact write?_ok hm1
              have heqM2 : m2 = m1.write .w64 (UInt64.ofNat input.layout.stackTop + UInt64.ofNat 16) 0 := by
                rw [hevalRbp b1 16 rfl (by decide)] at hm2; exact write?_ok hm2
              have heqM3 : m3 = m2.write .w64 (UInt64.ofNat input.layout.stackTop + UInt64.ofNat 24) 0 := by
                rw [hevalRbp b2 24 rfl (by decide)] at hm3; exact write?_ok hm3
              have heqM4 : m4 = m3.write .w64 (UInt64.ofNat input.layout.stackTop + UInt64.ofNat 32) 0 := by
                rw [hevalRbp b3 32 rfl (by decide)] at hm4; exact write?_ok hm4
              have houtM4 : ∀ a, OutsideSegments input.layout.segments a → m4.bytes a = core2.memory.bytes a := by
                intro a ho
                rw [heqM4, plain_write_scratch_preserves_outside ce (by decide) a ho,
                    heqM3, plain_write_scratch_preserves_outside ce (by decide) a ho,
                    heqM2, plain_write_scratch_preserves_outside ce (by decide) a ho,
                    heqM1, plain_write_scratch_preserves_outside ce (by decide) a ho,
                    heqM0, plain_write_scratch_preserves_outside ce (by decide) a ho]
              have hfileM4 : ∀ k < ce.bytes.size, m4.bytes (UInt64.ofNat (fileBase + k)) = ce.bytes[k]! := by
                intro k hk
                rw [heqM4, plain_write_scratch_preserves_file ce (by decide) hk,
                    heqM3, plain_write_scratch_preserves_file ce (by decide) hk,
                    heqM2, plain_write_scratch_preserves_file ce (by decide) hk,
                    heqM1, plain_write_scratch_preserves_file ce (by decide) hk,
                    heqM0, plain_write_scratch_preserves_file ce (by decide) hk]
                exact hfile2 k hk
              obtain ⟨argc, hargcLt, hargcRead, hargcCase, hnull, hstr, hwords, hbytesA⟩ := hab2
              have hargcWEq : argcW = UInt64.ofNat argc := by
                rw [read64?_value hargcW, eval_at core2 .rsp (by decide), show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero, hrsp2, hargcRead]
              have hseAp1 : signExtend32 (UInt32.ofNat (input.arity + 1)) = UInt64.ofNat (input.arity + 1) :=
                plain_signExtend32_ofNat (by have := hff.arity; omega)
              by_cases hcnt : argc = input.arity + 1
              · -- Correct argc: `args.length = input.arity`
                have hargsLen : args.length = input.arity := by
                  rcases hargcCase with ⟨h0, _⟩ | h1 <;> omega
                have hcNeF : Condition.holds .ne .w64 (b6.readReg .rbx) (signExtend32 (UInt32.ofNat (input.arity + 1))) = false := by
                  have hbx : b6.readReg .rbx = UInt64.ofNat (input.arity + 1) := by
                    change argcW = _; rw [hargcWEq, hcnt]
                  rw [hbx, hseAp1]; simp [Condition.holds]
                obtain ⟨f5, e12⟩ := prun_cmpI ce (b := 2) (j := 12) (by decide) (by rw [PB.block_args]; rfl)
                  (by rw [PB.block_args]) b6 fl2 hcNeF
                -- block 3: mov r15, 0; jmp 4
                have e13 := pstep_movI ce (b := 3) (j := 0) (by decide) (r := .r15) (v := 0)
                  (by rw [PB.block_loopInit]; rfl) b6 f5
                let b7 := b6.setReg .r15 0
                have e14 := pstep_jump ce (b := 3) (by decide) (t := UInt32.ofNat 4)
                  (by rw [PB.block_loopInit]) (s := ⟨b7, paddr ce 3 1, f5⟩) (by rw [PB.block_loopInit]; rfl)
                rcases TraceN.through (run_comp e12 (run_comp (run_one e13) (run_one e14))) ht4 with
                  rfl | ⟨-, ht5⟩
                · exact hnil_start
                have habM4 : ArgBlock b7.memory sp0 args (fun a => OutsideSegments input.layout.segments a ∧ CanonicalUser a) := by
                  change ArgBlock m4 _ _ _
                  have hr_eq : ∀ s, (∀ b < 8, OutsideSegments input.layout.segments (s + UInt64.ofNat b)) →
                      m4.read64 s = core2.memory.read64 s := fun s hs => read64_congr houtM4 hs
                  refine ⟨argc, hargcLt, ?_, hargcCase, ?_, ?_, hwords, ?_⟩
                  · rw [hr_eq _ (fun b hb => by simpa using (hwords 0 (by omega) b hb).1)]; exact hargcRead
                  · rw [hr_eq _ (fun b hb => by rw [UInt64.add_assoc, ← UInt64.ofNat_add]; exact (hwords (argc + 1) (Nat.le_refl _) b hb).1)]; exact hnull
                  · intro idx a ha
                    have hlt' : idx < args.length := (List.getElem?_eq_some_iff.mp ha).1
                    have hslot : m4.read64 (sp0 + UInt64.ofNat (8 * (idx + 2))) =
                        core2.memory.read64 (sp0 + UInt64.ofNat (8 * (idx + 2))) := by
                      apply hr_eq; intro b hb; rw [UInt64.add_assoc, ← UInt64.ofNat_add]; exact (hwords (idx + 2) (by omega) b hb).1
                    obtain ⟨hp, hbs, hnl⟩ := hstr idx a ha
                    refine ⟨by rw [hslot]; exact hp, fun j hj => ?_, ?_⟩
                    · rw [hslot, houtM4 _ (hbytesA idx a ha j (by omega)).1]; exact hbs j hj
                    · rw [hslot, houtM4 _ (hbytesA idx a ha a.length (Nat.le_refl _)).1]; exact hnl
                  · intro idx a ha j hj
                    have hlt' : idx < args.length := (List.getElem?_eq_some_iff.mp ha).1
                    have hslot : m4.read64 (sp0 + UInt64.ofNat (8 * (idx + 2))) =
                        core2.memory.read64 (sp0 + UInt64.ofNat (8 * (idx + 2))) := by
                      apply hr_eq; intro b hb; rw [UInt64.add_assoc, ← UInt64.ofNat_add]; exact (hwords (idx + 2) (by omega) b hb).1
                    rw [hslot]; exact hbytesA idx a ha j hj
                have hslots0 : ∀ k < 5, b7.memory.read64 (UInt64.ofNat input.layout.stackTop + UInt64.ofNat (8 * k)) =
                    UInt64.ofNat (([ ] : List Nat)[k]?.getD 0) := by
                  intro k hk
                  change m4.read64 _ = 0
                  have hsep : ∀ (a b : Nat), a ≠ b → a < 5 → b < 5 →
                      ∀ i < 8, ∀ j < Width.w64.bytes,
                        UInt64.ofNat input.layout.stackTop + UInt64.ofNat (8 * a) + UInt64.ofNat i ≠
                        UInt64.ofNat input.layout.stackTop + UInt64.ofNat (8 * b) + UInt64.ofNat j := by
                    intro a b hab' ha' hb' i hi j hj heq
                    have h1 := congrArg UInt64.toNat heq
                    rw [UInt64.add_assoc, UInt64.add_assoc, ← UInt64.ofNat_add, ← UInt64.ofNat_add,
                      ← UInt64.ofNat_add, ← UInt64.ofNat_add,
                      toNat_small (by omega), toNat_small (by simp [Width.bytes] at hj; omega)] at h1
                    simp [Width.bytes] at hj; omega
                  match k with
                  | 0 =>
                    rw [heqM4, write_read64_apart (hsep 0 4 (by decide) (by decide) (by decide)),
                        heqM3, write_read64_apart (hsep 0 3 (by decide) (by decide) (by decide)),
                        heqM2, write_read64_apart (hsep 0 2 (by decide) (by decide) (by decide)),
                        heqM1, write_read64_apart (hsep 0 1 (by decide) (by decide) (by decide)),
                        heqM0, write_read64_same]
                  | 1 =>
                    rw [heqM4, write_read64_apart (hsep 1 4 (by decide) (by decide) (by decide)),
                        heqM3, write_read64_apart (hsep 1 3 (by decide) (by decide) (by decide)),
                        heqM2, write_read64_apart (hsep 1 2 (by decide) (by decide) (by decide)),
                        heqM1, write_read64_same]
                  | 2 =>
                    rw [heqM4, write_read64_apart (hsep 2 4 (by decide) (by decide) (by decide)),
                        heqM3, write_read64_apart (hsep 2 3 (by decide) (by decide) (by decide)),
                        heqM2, write_read64_same]
                  | 3 =>
                    rw [heqM4, write_read64_apart (hsep 3 4 (by decide) (by decide) (by decide)),
                        heqM3, write_read64_same]
                  | 4 => rw [heqM4, write_read64_same]
                  | k' + 5 => omega
                have hr12_7 : b7.readReg .r12 = sp0 + 8 := by
                  show (SB.at_ .rsp 8).eval a1 = sp0 + 8
                  rw [eval_at a1 .rsp (by decide)]; exact congrArg (· + 8) hrsp2
                have hloop := plain_args_loop ce hargs hargsLen (sp0 := sp0) input.arity 0 []
                  (Nat.zero_add _) rfl (fun _ hm => by cases hm) habM4 hr12_7 rfl rfl rfl rfl rfl
                  hslots0 hfileM4 ht5
                rw [List.drop_zero] at hloop
                cases hpa : parseArgsList args with
                | overflow =>
                  rw [hpa] at hloop
                  exact .inr (.inr ⟨σ2, rfl, .inr ⟨hargsLen, by rw [hpa]; exact hloop⟩⟩)
                | bad =>
                  rw [hpa] at hloop
                  exact .inr (.inr ⟨σ2, rfl, .inr ⟨hargsLen, by rw [hpa]; exact hloop⟩⟩)
                | ok ns =>
                  rw [hpa] at hloop
                  rcases hloop with rfl | ⟨core8, fl8, n8, ht8, hrbp8, hr13_8, hr14_8, _, hslots8, hfile8⟩
                  · exact hnil_start
                  have hnsLen : ns.length = input.arity := (parseArgsList_ok_length hpa).trans hargsLen
                  have hnsLt : ∀ x ∈ ns, x < 2 ^ 64 := parseArgsList_ok_lt hpa
                  have hres := plain_from_callInit ce hroot0 hrm hnsLen hnsLt hrbp8 hr13_8 hr14_8
                    (by simpa using hslots8) hfile8 ht8
                  exact .inr (.inr ⟨σ2, rfl, .inr ⟨hargsLen, by rw [hpa]; exact hres⟩⟩)
              · -- Wrong argc: `args.length ≠ input.arity` OR `(argc = 0 ∧ args = [])`
                have hwrong : args.length ≠ input.arity ∨ args = [] := by
                  rcases hargcCase with ⟨_, hemp⟩ | h1
                  · exact .inr hemp
                  · exact .inl (by omega)
                have hbxNe : b6.readReg .rbx ≠ UInt64.ofNat (input.arity + 1) := by
                  change argcW ≠ _; rw [hargcWEq]
                  apply ne_of_toNat
                  rw [toNat_small (by omega), toNat_small (by have := hff.arity; omega)]
                  exact hcnt
                have hcNeT : Condition.holds .ne .w64 (b6.readReg .rbx) (signExtend32 (UInt32.ofNat (input.arity + 1))) = true := by
                  rw [hseAp1, pholds_ne]
                  simpa using hbxNe
                obtain ⟨f5, e12⟩ := prun_cmpI ce (b := 2) (j := 12) (by decide) (by rw [PB.block_args]; rfl)
                  (by rw [PB.block_args]) b6 fl2 hcNeT
                rcases TraceN.through e12 ht4 with rfl | ⟨-, ht5⟩
                · exact hnil_start
                have hrep := plain_report_path ce .count hfileM4 ht5
                exact .inr (.inr ⟨σ2, rfl, .inl ⟨hwrong, hrep⟩⟩)
            · rcases TraceN.through (run_comp (run_one s0) (run_comp (run_one s1) (run_comp (run_one s2) (run_one s3)))) ht3 with rfl | ⟨-, ht'⟩
              · exact hnil_start
              · have := TraceN.nil_of_step_fault ef ht'; subst this; exact hnil_start
          · rcases TraceN.through (run_comp (run_one s0) (run_comp (run_one s1) (run_one s2))) ht3 with rfl | ⟨-, ht'⟩
            · exact hnil_start
            · have := TraceN.nil_of_step_fault ef ht'; subst this; exact hnil_start
        · rcases TraceN.through (run_comp (run_one s0) (run_one s1)) ht3 with rfl | ⟨-, ht'⟩
          · exact hnil_start
          · have := TraceN.nil_of_step_fault ef ht'; subst this; exact hnil_start
      · rcases TraceN.through (run_one s0) ht3 with rfl | ⟨-, ht'⟩
        · exact hnil_start
        · have := TraceN.nil_of_step_fault ef ht'; subst this; exact hnil_start
    · have := TraceN.nil_of_step_fault ef ht3; subst this; exact hnil_start
  · have := TraceN.nil_of_step_fault efault ht2; subst this; exact hnil_start

/-- **Corollary (`plain_shell_unspecified`)**: the plain `--exe` process reaches
an `Unspecified` state ONLY past valid argument parsing and a `.stuck` object call! -/
theorem plain_shell_unspecified {roots : List Linked.Root} {r : Linked.Root}
    (hroot0 : roots[0]? = some r) (hrm : PlainRootMatches input r)
    {args : List (List Nat)} (hargs : ArgsOk args)
    {s₀ : ByteEval.State} (hload : Loaded (Certified.checked ce) args s₀)
    {σ : List Sys} {s : ByteEval.State}
    (hr : Run ce.bytes s₀ σ s) (hu : Unspecified ce.bytes s) :
    args.length = input.arity ∧
    ∃ ns, parseArgsList args = .ok ns ∧
      objPlainCall (linkedOf input.object roots) ce.plan.placement.textSize input.result ns .stuck ∧
      started (fileBase + ce.plan.placement.dataOffset) <+: σ :=
  PlainShows.stuck_of_other (plain_shell_sound ce hroot0 hrm hargs hload (Run.other_of_unspecified hr hu 0))

end

end IxCC.X86.Exe.Plain
