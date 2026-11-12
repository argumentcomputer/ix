import IxCC.X86.Exe.Machine.Proof.Loop

/-!
# The shell's start-up (X0-P, third part)

`start`: from the loader's post-state (`Process.Loaded`), every trace of the
process is the confinement's refusal (`Refused`), or a prefix of the
confinement made (`started`), or `started` followed by a trace from a state at
`loop` standing for the session's first configuration (`Config.initial args`).

- `start` (block 0): `prctl(PR_SET_NO_NEW_PRIVS, 1)`; nonzero to the `confine`
  report; `seccomp` (block 1) likewise (`confine_run`);
- `args`, `argsNone`, `argsSome`, `setup` (blocks 2 to 5): `argc`, the event
  (the number of arguments), the cursor at `argv[1]` (or the null `argv[0]`
  when `argc = 0`), the state 0, the shell's own stack (`args_run`);
- `cursor_of_block`: the loader's argument block (`ArgBlock`) is a `Cursor`
  over the arguments, by induction over them.

The shell's stores at start-up are its own words at `C … C + 32`, inside the
zero-filled segments, so the argument block and the file are untouched.
-/

set_option autoImplicit false

namespace IxCC.X86.Exe.Process

open IxCC.Exe.Machine (Config)
open IxCC.X86.Exe.Shell (blockOffset instrOffset)
open SB

theorem slot_add (sp : Word) (a b : Nat) : sp + UInt64.ofNat a + UInt64.ofNat b = sp + UInt64.ofNat (a + b) := by
  rw [UInt64.add_assoc, ← UInt64.ofNat_add]

/-- **The loader's argument block is a cursor** over the arguments from `argv[i + 1]` on. -/
theorem cursor_of_block {m : Memory} {sp : Word} {args : List (List Nat)} {apart : Word → Prop}
    (hnull : m.read64 (sp + UInt64.ofNat (8 * (args.length + 2))) = 0)
    (hstr : ∀ i a, args[i]? = some a →
      m.read64 (sp + UInt64.ofNat (8 * (i + 2))) ≠ 0 ∧
      (∀ j < a.length, m.bytes (m.read64 (sp + UInt64.ofNat (8 * (i + 2))) + UInt64.ofNat j) = UInt8.ofNat a[j]!) ∧
      m.bytes (m.read64 (sp + UInt64.ofNat (8 * (i + 2))) + UInt64.ofNat a.length) = 0)
    (hwords : ∀ i ≤ args.length + 2, ∀ b < 8, apart (sp + UInt64.ofNat (8 * i + b)))
    (hbytes : ∀ i a, args[i]? = some a → ∀ j ≤ a.length,
      apart (m.read64 (sp + UInt64.ofNat (8 * (i + 2))) + UInt64.ofNat j)) :
    ∀ k i, i + k = args.length →
      Cursor m apart (sp + UInt64.ofNat (8 * (i + 2))) (m.read64 (sp + UInt64.ofNat (8 * (i + 2)))) (args.drop i) := by
  intro k
  induction k with
  | zero =>
    intro i hi
    rw [Nat.add_zero] at hi
    subst hi
    rw [List.drop_length]
    exact .done hnull (fun b hb => by rw [slot_add]; exact hwords _ (Nat.le_refl _) b hb)
  | succ k ih =>
    intro i hi
    have hlt : i < args.length := by omega
    obtain ⟨hp, hbs, hnul⟩ := hstr i args[i] (List.getElem?_eq_getElem hlt)
    have hnext := ih (i + 1) (by omega)
    rw [show 8 * (i + 1 + 2) = 8 * (i + 2) + 8 by omega, ← slot_add] at hnext
    have h := Cursor.arg (m := m) (apart := apart) (slot := sp + UInt64.ofNat (8 * (i + 2))) (a := args[i]) (j := 0)
      (more := args.drop (i + 1)) hp (fun b hb => by rw [slot_add]; exact hwords _ (by omega) b hb) (Nat.zero_le _)
      hbs hnul (hbytes i args[i] (List.getElem?_eq_getElem hlt)) hnext
    rw [List.drop_zero, add_zero'] at h
    rw [List.drop_eq_getElem_cons hlt]
    exact h

section
variable {L : Machine.Layout} {step : String} {object : ByteArray} (ce : Machine.Certified L step object)
include ce

/-- The loader's entry is the shell's first instruction. -/
theorem entry_addr : UInt64.ofNat (fileBase + ce.checked.plan.placement.shellOffset) = addr ce 0 0 := by
  show _ = UInt64.ofNat (fileBase + (ce.checked.plan.placement.shellOffset + blockOffset (shellOf ce.checked) 0 +
    instrOffset (blockAt (shellOf ce.checked) 0) 0))
  simp [blockOffset, instrOffset]

/-- A `test r, r` and `jne` terminator. -/
theorem mrun_ifNz {b j : Nat} (hb : b < 46) (hsz : (blockAt (shellOf ce.checked) b).instructions.size = j)
    {r : GPR} {t f : Nat} (ht : t < 46) (hf : f < 46)
    (hterm : (blockAt (shellOf ce.checked) b).terminator = ifNz r t f) (core : Core) (fl : ByteEval.Flags)
    {taken : Bool} (htk : (core.readReg r != 0) = taken) :
    ∃ fl', ByteEval.run ce.checked.bytes fetchBase (if taken then 2 else 3) ⟨core, addr ce b j, fl⟩ =
      .ok ⟨core, addr ce (if taken then t else f) 0, fl'⟩ := by
  have h : ByteEval.run ce.checked.bytes fetchBase (if taken then 2 else 3) ⟨core, addr ce b j, fl⟩ =
      .ok ⟨core, UInt64.ofNat (shellAddr L step ce.checked (if taken then (UInt32.ofNat t : BlockId) else UInt32.ofNat f).toNat 0),
        ByteEval.aluFlags .and .w64 (core.readReg r) (core.readReg r)⟩ :=
    mrun_branch ce hb (o := { mn := .test, w := .w64, form := .MR }) (args := [.reg r, .reg r]) (cond := .ne)
      (yes := UInt32.ofNat t) (no := UInt32.ofNat f) hterm (s := ⟨core, addr ce b j, fl⟩) (core := core)
      (fl := ByteEval.aluFlags .and .w64 (core.readReg r) (core.readReg r)) (by rw [hsz]) (exec_test _ _ _ _)
      (taken := taken) (by rw [test_ne_self, htk])
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

/-- **The confinement** (blocks `start` and `seccomp`): from the shell's entry, a trace is the
refusal, a prefix of `started`, or `started` followed by a trace from `args` with the memory and
the stack pointer of the entry. -/
theorem confine_run (core : Core) (fl : ByteEval.Flags)
    (hfile : ∀ i < ce.checked.bytes.size, core.memory.bytes (UInt64.ofNat (fileBase + i)) = ce.checked.bytes[i]!)
    {n : Nat} {σ : List Sys} (ht : TraceN ce.checked.bytes n ⟨core, addr ce 0 0, fl⟩ σ) :
    Refused (fileBase + ce.checked.plan.placement.dataOffset) σ ∨
    σ <+: started (fileBase + ce.checked.plan.placement.dataOffset) ∨
    ∃ core' fl' n' σ', σ = started (fileBase + ce.checked.plan.placement.dataOffset) ++ σ' ∧
      TraceN ce.checked.bytes n' ⟨core', addr ce 2 0, fl'⟩ σ' ∧ core'.memory = core.memory ∧
      core'.readReg .rsp = core.readReg .rsp := by
  let D := fileBase + ce.checked.plan.placement.dataOffset
  -- block 0: prctl
  have e1 := mstep_movI ce (b := 0) (j := 0) (by decide) (r := .rax) (v := 157) (by rw [block_start] <;> rfl) core fl
  let k1 := core.setReg .rax (UInt64.ofNat 157)
  have e2 := mstep_movI ce (b := 0) (j := 1) (by decide) (r := .rdi) (v := 38) (by rw [block_start] <;> rfl) k1 fl
  let k2 := k1.setReg .rdi (UInt64.ofNat 38)
  have e3 := mstep_movI ce (b := 0) (j := 2) (by decide) (r := .rsi) (v := 1) (by rw [block_start] <;> rfl) k2 fl
  let k3 := k2.setReg .rsi (UInt64.ofNat 1)
  have e4 := mstep_movI ce (b := 0) (j := 3) (by decide) (r := .rdx) (v := 0) (by rw [block_start] <;> rfl) k3 fl
  let k4 := k3.setReg .rdx (UInt64.ofNat 0)
  have e5 := mstep_movI ce (b := 0) (j := 4) (by decide) (r := .r10) (v := 0) (by rw [block_start] <;> rfl) k4 fl
  let k5 := k4.setReg .r10 (UInt64.ofNat 0)
  have e6 := mstep_movI ce (b := 0) (j := 5) (by decide) (r := .r8) (v := 0) (by rw [block_start] <;> rfl) k5 fl
  let k6 := k5.setReg .r8 (UInt64.ofNat 0)
  have hrun : ByteEval.run ce.checked.bytes fetchBase 6 ⟨core, addr ce 0 0, fl⟩ = .ok ⟨k6, addr ce 0 6, fl⟩ :=
    run_comp (run_one e1) (run_comp (run_one e2) (run_comp (run_one e3) (run_comp (run_one e4) (run_comp (run_one e5)
      (run_one e6)))))
  obtain ⟨hd, hb, hnext⟩ := msyscall_at ce (b := 0) (j := 6) (by decide) (by rw [block_start] <;> rfl)
    (s := ⟨k6, addr ce 0 6, fl⟩) rfl
  rcases TraceN.through hrun ht with rfl | ⟨-, ht1⟩
  · exact .inr (.inl List.nil_prefix)
  rcases TraceN.prctl (s := ⟨k6, addr ce 0 6, fl⟩) hd hb rfl rfl ht1 with rfl | ⟨r, rcx, r11, fl1, σ1, rfl, -, ht2⟩
  · exact .inr (.inl List.nil_prefix)
  let s2 := returned ⟨k6, addr ce 0 6, fl⟩ r rcx r11 fl1
  have h2rip : s2.rip = addr ce 0 7 := hnext
  have hfile2 : ∀ i < ce.checked.bytes.size, s2.core.memory.bytes (UInt64.ofNat (fileBase + i)) = ce.checked.bytes[i]! :=
    hfile
  by_cases hr : r = 0
  · subst hr
    obtain ⟨f3, e7⟩ := mrun_ifNz ce (b := 0) (j := 7) (by decide) (by rw [block_start] <;> rfl) (r := .rax) (t := 45)
      (f := 1) (by decide) (by decide) (by rw [block_start] <;> rfl) s2.core s2.flags (taken := false) rfl
    have e7 : ByteEval.run ce.checked.bytes fetchBase 3 s2 = .ok ⟨s2.core, addr ce 1 0, f3⟩ := by
      rw [show s2 = ⟨s2.core, addr ce 0 7, s2.flags⟩ from by rw [← h2rip]]
      exact e7
    rcases TraceN.through e7 ht2 with rfl | ⟨-, ht3⟩
    · exact .inr (.inl ⟨[_], rfl⟩)
    -- block 1: seccomp
    let c0 := s2.core
    have g1 := mstep_movI ce (b := 1) (j := 0) (by decide) (r := .rax) (v := 317) (by rw [block_seccomp] <;> rfl) c0 f3
    let c1 := c0.setReg .rax (UInt64.ofNat 317)
    have g2 := mstep_movI ce (b := 1) (j := 1) (by decide) (r := .rdi) (v := 1) (by rw [block_seccomp] <;> rfl) c1 f3
    let c2 := c1.setReg .rdi (UInt64.ofNat 1)
    have g3 := mstep_movI ce (b := 1) (j := 2) (by decide) (r := .rsi) (v := 0) (by rw [block_seccomp] <;> rfl) c2 f3
    let c3 := c2.setReg .rsi (UInt64.ofNat 0)
    have g4 := mstep_movI ce (b := 1) (j := 3) (by decide) (r := .rdx) (v := fprogAddr D) (by rw [block_seccomp] <;> rfl)
      c3 f3
    let c4 := c3.setReg .rdx (UInt64.ofNat (fprogAddr D))
    have hrun2 : ByteEval.run ce.checked.bytes fetchBase 4 ⟨c0, addr ce 1 0, f3⟩ = .ok ⟨c4, addr ce 1 4, f3⟩ :=
      run_comp (run_one g1) (run_comp (run_one g2) (run_comp (run_one g3) (run_one g4)))
    obtain ⟨hd2, hb2, hnext2⟩ := msyscall_at ce (b := 1) (j := 4) (by decide) (by rw [block_seccomp] <;> rfl)
      (s := ⟨c4, addr ce 1 4, f3⟩) rfl
    rcases TraceN.through hrun2 ht3 with rfl | ⟨-, ht4⟩
    · exact .inr (.inl ⟨[_], rfl⟩)
    rcases TraceN.seccomp (s := ⟨c4, addr ce 1 4, f3⟩) hd2 hb2 rfl rfl rfl ht4 with rfl | ⟨r2, rcx2, r112, fl2, σ2, rfl, -, ht5⟩
    · exact .inr (.inl ⟨[_], rfl⟩)
    let s5 := returned ⟨c4, addr ce 1 4, f3⟩ r2 rcx2 r112 fl2
    have h5rip : s5.rip = addr ce 1 5 := hnext2
    by_cases hr2 : r2 = 0
    · subst hr2
      obtain ⟨f6, e8⟩ := mrun_ifNz ce (b := 1) (j := 5) (by decide) (by rw [block_seccomp] <;> rfl) (r := .rax) (t := 45)
        (f := 2) (by decide) (by decide) (by rw [block_seccomp] <;> rfl) s5.core s5.flags (taken := false) rfl
      have e8 : ByteEval.run ce.checked.bytes fetchBase 3 s5 = .ok ⟨s5.core, addr ce 2 0, f6⟩ := by
        rw [show s5 = ⟨s5.core, addr ce 1 5, s5.flags⟩ from by rw [← h5rip]]
        exact e8
      rcases TraceN.through e8 ht5 with rfl | ⟨-, ht6⟩
      · exact .inr (.inl (List.prefix_refl _))
      exact .inr (.inr ⟨s5.core, f6, _, σ2, rfl, ht6, rfl, rfl⟩)
    · obtain ⟨f6, e8⟩ := mrun_ifNz ce (b := 1) (j := 5) (by decide) (by rw [block_seccomp] <;> rfl) (r := .rax) (t := 45)
        (f := 2) (by decide) (by decide) (by rw [block_seccomp] <;> rfl) s5.core s5.flags (taken := true)
        (by show (r2 != 0) = true; simp [hr2])
      have e8 : ByteEval.run ce.checked.bytes fetchBase 2 s5 = .ok ⟨s5.core, addr ce 45 0, f6⟩ := by
        rw [show s5 = ⟨s5.core, addr ce 1 5, s5.flags⟩ from by rw [← h5rip]]
        exact e8
      left
      rcases TraceN.through e8 ht5 with rfl | ⟨-, ht6⟩
      · obtain ⟨b, ρ, hρ, -⟩ := report_nil IxCC.Exe.Machine.statusConfine (messageOf IxCC.Exe.Machine.statusConfine)
        exact ⟨ρ, b, hρ, .inr ⟨r2, hr2, ⟨_, rfl⟩⟩⟩
      · obtain ⟨b, ρ, hρ, hp⟩ := report ce .confine (s := ⟨s5.core, addr ce 45 0, f6⟩) rfl hfile ht6
        exact ⟨ρ, b, hρ, .inr ⟨r2, hr2, (List.prefix_cons_inj _).mpr ((List.prefix_cons_inj _).mpr hp)⟩⟩
  · obtain ⟨f3, e7⟩ := mrun_ifNz ce (b := 0) (j := 7) (by decide) (by rw [block_start] <;> rfl) (r := .rax) (t := 45)
      (f := 1) (by decide) (by decide) (by rw [block_start] <;> rfl) s2.core s2.flags (taken := true)
      (by show (r != 0) = true; simp [hr])
    have e7 : ByteEval.run ce.checked.bytes fetchBase 2 s2 = .ok ⟨s2.core, addr ce 45 0, f3⟩ := by
      rw [show s2 = ⟨s2.core, addr ce 0 7, s2.flags⟩ from by rw [← h2rip]]
      exact e7
    left
    rcases TraceN.through e7 ht2 with rfl | ⟨-, ht3⟩
    · obtain ⟨b, ρ, hρ, -⟩ := report_nil IxCC.Exe.Machine.statusConfine (messageOf IxCC.Exe.Machine.statusConfine)
      exact ⟨ρ, b, hρ, .inl ⟨r, hr, ⟨_, rfl⟩⟩⟩
    · obtain ⟨b, ρ, hρ, hp⟩ := report ce .confine (s := ⟨s2.core, addr ce 45 0, f3⟩) rfl hfile2 ht3
      exact ⟨ρ, b, hρ, .inl ⟨r, hr, (List.prefix_cons_inj _).mpr hp⟩⟩

theorem out_low (k : Nat) (hk : k ≤ 8) {m : Memory} (v : Word) {x : Word} (hx : OutsideSegments L.segments x) :
    (m.write .w64 (cTop L + UInt64.ofNat k) v).bytes x = m.bytes x :=
  write_bytes_apart (fun j hj e => store_low ce k hk j hj (e ▸ .inl hx))

/-- `setup`: the state 0 stored at `C`, the shell's own stack, then `loop`. -/
theorem setup_run (core : Core) (fl : ByteEval.Flags) (h10 : core.readReg .r10 = cTop L) :
    FaultsWithin ce.checked.bytes ⟨core, addr ce 5 0, fl⟩ 2 ∨
    ∃ core', ByteEval.run ce.checked.bytes fetchBase 5 ⟨core, addr ce 5 0, fl⟩ = .ok ⟨core', addr ce 6 0, fl⟩ ∧
      core'.memory = core.memory.write .w64 (cTop L + UInt64.ofNat 0) (UInt64.ofNat 0) := by
  have e1 := mstep_movI ce (b := 5) (j := 0) (by decide) (r := .rax) (v := 0) (by rw [block_setup] <;> rfl) core fl
  let k1 := core.setReg .rax (UInt64.ofNat 0)
  rcases mstep_store ce (b := 5) (j := 1) (by decide) (w := .w64) (A := SB.at_ .r10) (r := .rax)
    (by rw [block_setup] <;> rfl) (.inl rfl) k1 fl (a := cTop L + UInt64.ofNat 0)
    (by rw [eval_at k1 .r10 (by decide), show k1.readReg .r10 = cTop L from h10]) with ⟨f, hf⟩ | e2
  · exact .inl ⟨1, by decide, _, f, run_one e1, hf⟩
  let k2 : Core := { k1 with memory := k1.memory.write .w64 (cTop L + UInt64.ofNat 0) (k1.readReg .rax) }
  have e3 := mstep_movI ce (b := 5) (j := 2) (by decide) (r := .r11) (v := L.shellTop) (by rw [block_setup] <;> rfl) k2 fl
  let k3 := k2.setReg .r11 (UInt64.ofNat L.shellTop)
  have e4 := mstep_movR ce (b := 5) (j := 3) (by decide) (d := .rsp) (r := .r11) (by rw [block_setup] <;> rfl) k3 fl
  let k4 := k3.setReg .rsp (k3.readReg .r11)
  have e5 := mstep_jmp ce (b := 5) (j := 4) (t := 6) (by decide) (by rw [block_setup] <;> rfl) (by rw [block_setup] <;> rfl)
    (by decide) k4 fl
  exact .inr ⟨k4, run_comp (run_one e1) (run_comp (run_one e2) (run_comp (run_one e3) (run_comp (run_one e4)
    (run_one e5)))), rfl⟩

set_option maxRecDepth 20000 in
/-- **The arguments** (`args`, `argsNone` or `argsSome`, `setup`): from `args` with the loader's
argument block at `rsp`, to `loop` standing for `Config.initial args`, or a fault. -/
theorem args_run {args : List (List Nat)} (hargs : ArgsOk args) (core : Core) (fl : ByteEval.Flags)
    (hab : ArgBlock core.memory (core.readReg .rsp) args (OutsideSegments L.segments))
    (hfile : ∀ i < ce.checked.bytes.size, core.memory.bytes (UInt64.ofNat (fileBase + i)) = ce.checked.bytes[i]!) :
    FaultsWithin ce.checked.bytes ⟨core, addr ce 2 0, fl⟩ 20 ∨
    ∃ m e, ByteEval.run ce.checked.bytes fetchBase m ⟨core, addr ce 2 0, fl⟩ = .ok e ∧
      AtLoop L ce.checked (loopAddr L step ce.checked) (Config.initial args) e := by
  obtain ⟨argc, hargc, hrd, hcase, hnull, hstr, hwords, hbytes⟩ := hab
  rcases mstep_load ce (b := 2) (j := 0) (by decide) (r := .rbx) (A := SB.at_ .rsp) (by rw [block_args] <;> rfl) core fl
    (a := core.readReg .rsp) (by rw [eval_at core .rsp (by decide), add_zero']) with ⟨f, hf⟩ | e1
  · exact .inl ⟨0, by decide, _, f, rfl, hf⟩
  let k1 := core.setReg .rbx (core.memory.read64 (core.readReg .rsp))
  have e2 : ByteEval.step ce.checked.bytes fetchBase ⟨k1, addr ce 2 1, fl⟩ =
      .ok ⟨k1.setReg .r12 ((SB.at_ .rsp 8).eval k1), addr ce 2 2, fl⟩ :=
    mstep_ok ce (b := 2) (j := 1) (by decide) (s := ⟨k1, addr ce 2 1, fl⟩) (i := Instr.lea .r12 (SB.at_ .rsp 8))
      (by rw [block_args] <;> rfl) (ne_call_of_op ⟨_, _, rfl⟩) rfl (exec_lea _ _ _ _)
  let k2 := k1.setReg .r12 ((SB.at_ .rsp 8).eval k1)
  have hr12 : k2.readReg .r12 = core.readReg .rsp + UInt64.ofNat 8 := eval_at k1 .rsp (by decide)
  have e3 := mstep_movI ce (b := 2) (j := 2) (by decide) (r := .r10) (v := L.callTop) (by rw [block_args] <;> rfl) k2 fl
  let k3 := k2.setReg .r10 (UInt64.ofNat L.callTop)
  have hpre : ByteEval.run ce.checked.bytes fetchBase 3 ⟨core, addr ce 2 0, fl⟩ = .ok ⟨k3, addr ce 2 3, fl⟩ :=
    run_comp (run_one e1) (run_comp (run_one e2) (run_one e3))
  have hrbx : k3.readReg .rbx = UInt64.ofNat argc := hrd
  have hout : ∀ {m : Memory}, (∀ x, OutsideSegments L.segments x → m.bytes x = core.memory.bytes x) →
      (∀ i < ce.checked.bytes.size, m.bytes (UInt64.ofNat (fileBase + i)) = ce.checked.bytes[i]!) :=
    fun hm i hi => (hm _ (file_outside ce hi)).trans (hfile i hi)
  by_cases h0 : argc = 0
  · -- no argument block (argc = 0): the slot is the null argv[0]
    have hnil : args = [] := by rcases hcase with h | h; exact h.2; omega
    subst hnil
    obtain ⟨f4, e4⟩ := mrun_cmp ce (b := 2) (j := 3) (by decide) (by rw [block_args] <;> rfl) (r := .rbx) (c := 0)
      (t := 3) (f := 4) (cond := .eq) (by decide) (by decide) (by rw [block_args] <;> rfl) (core := k3) fl
      (taken := true) (by rw [holds_eq _ (by decide), hrbx, toNat_small (by omega), h0]; rfl)
    have e4 : ByteEval.run ce.checked.bytes fetchBase 2 ⟨k3, addr ce 2 3, fl⟩ = .ok ⟨k3, addr ce 3 0, f4⟩ := e4
    rcases mstep_store ce (b := 3) (j := 0) (by decide) (w := .w64) (A := SB.at_ .r10 16) (r := .r12)
      (by rw [block_argsNone] <;> rfl) (.inl rfl) k3 f4 (a := cTop L + UInt64.ofNat 16) (eval_at k3 .r10 (by decide))
      with ⟨f, hf⟩ | e5
    · exact .inl ⟨5, by decide, _, f, run_comp hpre e4, hf⟩
    let k5 : Core := { k3 with memory := k3.memory.write .w64 (cTop L + UInt64.ofNat 16) (k3.readReg .r12) }
    have e6 := mstep_movI ce (b := 3) (j := 1) (by decide) (r := .rax) (v := 0) (by rw [block_argsNone] <;> rfl) k5 f4
    let k6 := k5.setReg .rax (UInt64.ofNat 0)
    rcases mstep_store ce (b := 3) (j := 2) (by decide) (w := .w64) (A := SB.at_ .r10 8) (r := .rax)
      (by rw [block_argsNone] <;> rfl) (.inl rfl) k6 f4 (a := cTop L + UInt64.ofNat 8) (eval_at k6 .r10 (by decide))
      with ⟨f, hf⟩ | e7
    · exact .inl ⟨7, by decide, _, f, run_comp hpre (run_comp e4 (run_comp (run_one e5) (run_one e6))), hf⟩
    let k7 : Core := { k6 with memory := k6.memory.write .w64 (cTop L + UInt64.ofNat 8) (k6.readReg .rax) }
    have e8 := mstep_jmp ce (b := 3) (j := 3) (t := 5) (by decide) (by rw [block_argsNone] <;> rfl)
      (by rw [block_argsNone] <;> rfl) (by decide) k7 f4
    have hpre2 : ByteEval.run ce.checked.bytes fetchBase 9 ⟨core, addr ce 2 0, fl⟩ = .ok ⟨k7, addr ce 5 0, f4⟩ :=
      run_comp hpre (run_comp e4 (run_comp (run_one e5) (run_comp (run_one e6) (run_comp (run_one e7) (run_one e8)))))
    rcases setup_run ce k7 f4 rfl with ⟨j, hj, s', f, hr, hf⟩ | ⟨k8, e9, hm8⟩
    · exact .inl ⟨9 + j, by omega, s', f, run_comp hpre2 hr, hf⟩
    right
    refine ⟨_, ⟨k8, addr ce 6 0, f4⟩, run_comp hpre2 e9, ?_⟩
    have hM : ∀ x, OutsideSegments L.segments x → k8.memory.bytes x = core.memory.bytes x := fun x hx => by
      rw [hm8]
      show (((core.memory.write .w64 (cTop L + UInt64.ofNat 16) _).write .w64 (cTop L + UInt64.ofNat 8) _).write .w64
        (cTop L + UInt64.ofNat 0) _).bytes x = _
      rw [out_low ce 0 (by decide) _ hx, out_low ce 8 (by decide) _ hx, cursor_store_out ce (by decide) (by decide) _ hx]
    have hs1 : ∀ b < 8, OutsideSegments L.segments (core.readReg .rsp + UInt64.ofNat 8 + UInt64.ofNat b) :=
      fun b hb => by rw [slot_add]; exact hwords 1 (by omega) b hb
    have hk7 : k7.memory = (core.memory.write .w64 (cTop L + UInt64.ofNat 16) (core.readReg .rsp + UInt64.ofNat 8)).write
        .w64 (cTop L + UInt64.ofNat 8) (UInt64.ofNat 0) := by
      show (k3.memory.write .w64 _ (k3.readReg .r12)).write .w64 _ (k6.readReg .rax) = _
      rw [show k3.readReg .r12 = core.readReg .rsp + UInt64.ofNat 8 from hr12]
      rfl
    refine ⟨rfl, by decide, ?_, by decide, ?_, fun a ha => by simp [Config.initial] at ha, ?_, hout hM⟩
    · show k8.memory.read64 (cTop L) = UInt64.ofNat 0
      rw [hm8, add_zero', write_read64_same]
    · show k8.memory.read64 (cTop L + UInt64.ofNat 8) = UInt64.ofNat 0
      rw [hm8, hk7, cword_apart ce (k := 8) (k' := 0) (by decide) (by decide) (.inr (by decide)), write_read64_same]
    · show Cursor _ _ (k8.memory.read64 (cTop L + UInt64.ofNat 16)) _ []
      have h16 : k8.memory.read64 (cTop L + UInt64.ofNat 16) = core.readReg .rsp + UInt64.ofNat 8 := by
        rw [hm8, hk7, cword_apart ce (k := 16) (k' := 0) (by decide) (by decide) (.inr (by decide)),
          cword_apart ce (k := 16) (k' := 8) (by decide) (by decide) (.inr (by decide)), write_read64_same]
      rw [h16]
      rw [h0] at hnull
      exact .done (by rw [read64_congr hM hs1]; exact hnull) hs1
  · -- arguments (argc = args.length + 1): the slot is argv[1]
    have hlen : argc = args.length + 1 := by rcases hcase with h | h; exact absurd h.1 h0; exact h
    obtain ⟨f4, e4⟩ := mrun_cmp ce (b := 2) (j := 3) (by decide) (by rw [block_args] <;> rfl) (r := .rbx) (c := 0)
      (t := 3) (f := 4) (cond := .eq) (by decide) (by decide) (by rw [block_args] <;> rfl) (core := k3) fl
      (taken := false) (by rw [holds_eq _ (by decide), hrbx, toNat_small (by omega)]; simp only [decide_eq_false_iff_not]; exact h0)
    have e4 : ByteEval.run ce.checked.bytes fetchBase 3 ⟨k3, addr ce 2 3, fl⟩ = .ok ⟨k3, addr ce 4 0, f4⟩ := e4
    have e5 := mstep_movR ce (b := 4) (j := 0) (by decide) (d := .rax) (r := .rbx) (by rw [block_argsSome] <;> rfl) k3 f4
    let k5 := k3.setReg .rax (k3.readReg .rbx)
    obtain ⟨f6, e6⟩ := mstep_alu ce (b := 4) (j := 1) (by decide) (op := .sub) (w := .w64) (r := .rax)
      (src := .imm (UInt32.ofNat 1)) (by rw [block_argsSome] <;> rfl) (ne_call_of_op ⟨_, _, rfl⟩) k5 f4
    let k6 := k5.writeReg .w64 .rax (AluOp.sub.eval (k5.readReg .rax) ((AluSource.imm (UInt32.ofNat 1)).eval k5))
    have hrax6 : k6.readReg .rax = UInt64.ofNat args.length := by
      show k3.readReg .rbx - signExtend32 (UInt32.ofNat 1) = _
      rw [hrbx, show signExtend32 (UInt32.ofNat 1) = UInt64.ofNat 1 by decide, hlen]
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, toNat_small (by omega), toNat_small (by omega)]; omega),
        toNat_small (by omega), toNat_small (by omega), toNat_small (by omega)]
      omega
    have hpre2 : ByteEval.run ce.checked.bytes fetchBase 8 ⟨core, addr ce 2 0, fl⟩ = .ok ⟨k6, addr ce 4 2, f6⟩ :=
      run_comp hpre (run_comp e4 (run_comp (run_one e5) (run_one e6)))
    rcases mstep_store ce (b := 4) (j := 2) (by decide) (w := .w64) (A := SB.at_ .r10 8) (r := .rax)
      (by rw [block_argsSome] <;> rfl) (.inl rfl) k6 f6 (a := cTop L + UInt64.ofNat 8) (eval_at k6 .r10 (by decide))
      with ⟨f, hf⟩ | e7
    · exact .inl ⟨8, by decide, _, f, hpre2, hf⟩
    let k7 : Core := { k6 with memory := k6.memory.write .w64 (cTop L + UInt64.ofNat 8) (k6.readReg .rax) }
    obtain ⟨f8, e8⟩ := mstep_alu ce (b := 4) (j := 3) (by decide) (op := .add) (w := .w64) (r := .r12)
      (src := .imm (UInt32.ofNat 8)) (by rw [block_argsSome] <;> rfl) (ne_call_of_op ⟨_, _, rfl⟩) k7 f6
    let k8 := k7.writeReg .w64 .r12 (AluOp.add.eval (k7.readReg .r12) ((AluSource.imm (UInt32.ofNat 8)).eval k7))
    have hr8 : k8.readReg .r12 = core.readReg .rsp + UInt64.ofNat (8 * (0 + 2)) := by
      show k2.readReg .r12 + signExtend32 (UInt32.ofNat 8) = _
      rw [hr12, show signExtend32 (UInt32.ofNat 8) = UInt64.ofNat 8 by decide, slot_add]
    rcases mstep_store ce (b := 4) (j := 4) (by decide) (w := .w64) (A := SB.at_ .r10 16) (r := .r12)
      (by rw [block_argsSome] <;> rfl) (.inl rfl) k8 f8 (a := cTop L + UInt64.ofNat 16) (eval_at k8 .r10 (by decide))
      with ⟨f, hf⟩ | e9
    · exact .inl ⟨10, by decide, _, f, run_comp hpre2 (run_comp (run_one e7) (run_one e8)), hf⟩
    let k9 : Core := { k8 with memory := k8.memory.write .w64 (cTop L + UInt64.ofNat 16) (k8.readReg .r12) }
    rcases mstep_load ce (b := 4) (j := 5) (by decide) (r := .rcx) (A := SB.at_ .r12) (by rw [block_argsSome] <;> rfl) k9 f8
      (a := k9.readReg .r12) (by rw [eval_at k9 .r12 (by decide), add_zero']) with ⟨f, hf⟩ | e10
    · exact .inl ⟨11, by decide, _, f, run_comp hpre2 (run_comp (run_one e7) (run_comp (run_one e8) (run_one e9))), hf⟩
    let k10 := k9.setReg .rcx (k9.memory.read64 (k9.readReg .r12))
    rcases mstep_store ce (b := 4) (j := 6) (by decide) (w := .w64) (A := SB.at_ .r10 24) (r := .rcx)
      (by rw [block_argsSome] <;> rfl) (.inl rfl) k10 f8 (a := cTop L + UInt64.ofNat 24) (eval_at k10 .r10 (by decide))
      with ⟨f, hf⟩ | e11
    · exact .inl ⟨12, by decide, _, f, run_comp hpre2 (run_comp (run_one e7) (run_comp (run_one e8) (run_comp (run_one e9)
        (run_one e10)))), hf⟩
    let k11 : Core := { k10 with memory := k10.memory.write .w64 (cTop L + UInt64.ofNat 24) (k10.readReg .rcx) }
    have e12 := mstep_jmp ce (b := 4) (j := 7) (t := 5) (by decide) (by rw [block_argsSome] <;> rfl)
      (by rw [block_argsSome] <;> rfl) (by decide) k11 f8
    have hpre3 : ByteEval.run ce.checked.bytes fetchBase 14 ⟨core, addr ce 2 0, fl⟩ = .ok ⟨k11, addr ce 5 0, f8⟩ :=
      run_comp hpre2 (run_comp (run_one e7) (run_comp (run_one e8) (run_comp (run_one e9) (run_comp (run_one e10)
        (run_comp (run_one e11) (run_one e12))))))
    rcases setup_run ce k11 f8 rfl with ⟨j, hj, s', f, hr, hf⟩ | ⟨k12, e13, hm12⟩
    · exact .inl ⟨14 + j, by omega, s', f, run_comp hpre3 hr, hf⟩
    right
    refine ⟨_, ⟨k12, addr ce 6 0, f8⟩, run_comp hpre3 e13, ?_⟩
    let m2 := (core.memory.write .w64 (cTop L + UInt64.ofNat 8) (UInt64.ofNat args.length)).write .w64
      (cTop L + UInt64.ofNat 16) (core.readReg .rsp + UInt64.ofNat (8 * (0 + 2)))
    have hm2 : ∀ x, OutsideSegments L.segments x → m2.bytes x = core.memory.bytes x := fun x hx => by
      show ((core.memory.write .w64 (cTop L + UInt64.ofNat 8) _).write .w64 (cTop L + UInt64.ofNat 16) _).bytes x = _
      rw [cursor_store_out ce (by decide) (by decide) _ hx, out_low ce 8 (by decide) _ hx]
    have hk9 : k9.memory = m2 := by
      show (core.memory.write .w64 (cTop L + UInt64.ofNat 8) (k6.readReg .rax)).write .w64 _ (k8.readReg .r12) = _
      rw [hrax6, hr8]
    have hs2 : ∀ b < 8, OutsideSegments L.segments (core.readReg .rsp + UInt64.ofNat (8 * (0 + 2)) + UInt64.ofNat b) :=
      fun b hb => by rw [slot_add]; exact hwords 2 (by omega) b hb
    have hmem12 : k12.memory = ((m2.write .w64 (cTop L + UInt64.ofNat 24)
        (core.memory.read64 (core.readReg .rsp + UInt64.ofNat (8 * (0 + 2))))).write .w64 (cTop L + UInt64.ofNat 0)
        (UInt64.ofNat 0)) := by
      rw [hm12]
      show ((k9.memory.write .w64 _ (k9.memory.read64 (k9.readReg .r12))).write .w64 _ _) = _
      rw [hk9, show k9.readReg .r12 = core.readReg .rsp + UInt64.ofNat (8 * (0 + 2)) from hr8, read64_congr hm2 hs2]
    have hM : ∀ x, OutsideSegments L.segments x → k12.memory.bytes x = core.memory.bytes x := fun x hx => by
      rw [hmem12, out_low ce 0 (by decide) _ hx, cursor_store_out ce (by decide) (by decide) _ hx]
      exact hm2 x hx
    have hcur := cursor_of_block (m := core.memory) (sp := core.readReg .rsp) (args := args)
      (apart := OutsideSegments L.segments) (by rw [show 8 * (args.length + 2) = 8 * (argc + 1) by omega]; exact hnull)
      hstr (fun i hi b hb => hwords i (by omega) b hb) hbytes args.length 0 (by omega)
    rw [List.drop_zero] at hcur
    refine ⟨rfl, by show (0 : Nat) < 2 ^ 64; decide, ?_, by show args.length < 2 ^ 64; omega, ?_, hargs, ?_, hout hM⟩
    · show k12.memory.read64 (cTop L) = UInt64.ofNat 0
      rw [hmem12, add_zero', write_read64_same]
    · show k12.memory.read64 (cTop L + UInt64.ofNat 8) = UInt64.ofNat args.length
      rw [hmem12, cword_apart ce (k := 8) (k' := 0) (by decide) (by decide) (.inr (by decide)),
        cword_apart ce (k := 8) (k' := 24) (by decide) (by decide) (.inl (by decide)),
        cword_apart ce (k := 8) (k' := 16) (by decide) (by decide) (.inl (by decide)), write_read64_same]
    · show Cursor _ _ (k12.memory.read64 (cTop L + UInt64.ofNat 16)) (k12.memory.read64 (cTop L + UInt64.ofNat 24)) args
      rw [hmem12, cword_apart ce (k := 16) (k' := 0) (by decide) (by decide) (.inr (by decide)),
        cword_apart ce (k := 16) (k' := 24) (by decide) (by decide) (.inl (by decide)), write_read64_same,
        cword_apart ce (k := 24) (k' := 0) (by decide) (by decide) (.inr (by decide)), write_read64_same]
      have hc := Cursor.congr hM hcur
      rw [hmem12] at hc
      exact hc

/-- **Start-up**: from the loader's post-state, a trace is a refusal, or a prefix of `started`,
or `started` followed by a trace from a state at `loop` standing for `Config.initial args`. -/
theorem start {args : List (List Nat)} (hargs : ArgsOk args) {s₀ : ByteEval.State} (hload : Loaded ce.checked args s₀)
    {σ : List Sys} (hσ : Trace ce.checked.bytes s₀ σ) :
    let data := fileBase + ce.checked.plan.placement.dataOffset
    Refused data σ ∨ σ <+: started data ∨
    ∃ s σ', AtLoop L ce.checked (loopAddr L step ce.checked) (Config.initial args) s ∧
      Trace ce.checked.bytes s σ' ∧ σ = started data ++ σ' := by
  obtain ⟨n, ht⟩ := Trace.toN hσ
  obtain ⟨core, rip, fl⟩ := s₀
  obtain ⟨hrip, hfile, hab⟩ := hload
  change rip = _ at hrip
  subst hrip
  rw [entry_addr ce] at ht
  rcases confine_run ce core fl hfile ht with h | h | ⟨core', fl', n', σ', rfl, ht', hmem, hrsp⟩
  · exact .inl h
  · exact .inr (.inl h)
  have hab' : ArgBlock core'.memory (core'.readReg .rsp) args (OutsideSegments L.segments) := by
    rw [hmem, hrsp]; exact hab
  have hfile' : ∀ i < ce.checked.bytes.size, core'.memory.bytes (UInt64.ofNat (fileBase + i)) = ce.checked.bytes[i]! := by
    rw [hmem]; exact hfile
  rcases args_run ce hargs core' fl' hab' hfile' with hf | ⟨m, e, hrun, hat⟩
  · rw [TraceN.nil_of_faults hf ht', List.append_nil]
    exact .inr (.inl (List.prefix_refl _))
  rcases TraceN.through hrun ht' with rfl | ⟨-, ht''⟩
  · rw [List.append_nil]
    exact .inr (.inl (List.prefix_refl _))
  · exact .inr (.inr ⟨e, σ', hat, ht''.toTrace, rfl⟩)

end

end IxCC.X86.Exe.Process
