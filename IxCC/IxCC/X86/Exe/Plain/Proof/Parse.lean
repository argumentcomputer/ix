import IxCC.X86.Exe.Plain.Proof.Report

/-! # Plain Shell: Decimal Argument Parser & Argument Loop

Proves:
- `plain_parse_run` (blocks 23–32): for any NUL-terminated C string `a` (`∀ b ∈ a, 0 < b < 256`),
  calling `B.parse` either faults on memory or returns cleanly with `rsp` restored, memory and
  callee-saved registers untouched, and `(rdx, rax)` matching `parseArgBytes a` exactly.
- `plain_args_loop` (blocks 4–7): parsing `args[0..arity)` into `[L.stackTop .. L.stackTop + 40)`
  either reports `.natOverflow` / `.numeral` on the first invalid argument or reaches `B.callInit`
  with all parsed words stored and `0` in any remaining slots `arity..4`. -/

set_option autoImplicit false

namespace IxCC.X86.Exe.Plain

open IxCC.X86
open IxCC.X86.Exe
open IxCC.X86.Exe.Process
open PB

section
variable {input : X86.Exe.Input} (ce : Certified input)

/-- The 128-bit overflow check of `parseMul` + `parseAdd` matches `2^64 ≤ acc * 10 + d` exactly. -/
private theorem parse_ovf_iff (acc d : Nat) :
    (2 ^ 64 ≤ acc ∨ 2 ^ 64 ≤ 10 * (acc % 2 ^ 64) ∨ 2 ^ 64 ≤ 10 * (acc % 2 ^ 64) % 2 ^ 64 + d) ↔
      2 ^ 64 ≤ acc * 10 + d := by
  by_cases h1 : 2 ^ 64 ≤ acc
  · constructor <;> intro _ <;> omega
  · have hmod : acc % 2 ^ 64 = acc := Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    by_cases h2 : 2 ^ 64 ≤ 10 * acc
    · constructor <;> intro _ <;> omega
    · have hmod2 : (10 * acc) % 2 ^ 64 = 10 * acc := Nat.mod_eq_of_lt (by omega)
      rw [hmod2]
      omega

private theorem parse_mod_step (acc d : Nat) :
    ((10 * (acc % 2 ^ 64)) % 2 ^ 64 + d) % 2 ^ 64 = (acc * 10 + d) % 2 ^ 64 := by
  rw [Nat.add_mod, Nat.mod_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_comm 10 acc, ← Nat.add_mod]

private theorem saved_read_setReg {c : Core} {r' : GPR} {v : Word}
    (h : r' = .rax ∨ r' = .rcx ∨ r' = .rdx ∨ r' = .rsi ∨ r' = .rdi ∨ r' = .r8 ∨ r' = .r9 ∨ r' = .rsp) :
    ∀ r ∈ ([.rbx, .rbp, .r12, .r13, .r14, .r15] : List GPR), (c.setReg r' v).readReg r = c.readReg r := by
  intro r hr
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [List.mem_cons, List.not_mem_nil, or_false] at hr;
     rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)

/-- Pure `ByteEval.run` lemma for `B.parseBad` (block 32): returns `rdx = 2` to `retAddr`. -/
private theorem parseBad_run {core : Core} {fl : ByteEval.Flags} {retAddr : Word}
    (hrsp : core.readReg .rsp = UInt64.ofNat input.layout.shellTop - 8)
    (hret : core.memory.read64 (UInt64.ofNat input.layout.shellTop - 8) = retAddr) :
    (∃ m core' fl', ByteEval.run ce.bytes fetchBase m ⟨core, paddr ce 32 0, fl⟩ = .ok ⟨core', retAddr, fl'⟩ ∧
      core'.memory = core.memory ∧
      core'.readReg .rsp = UInt64.ofNat input.layout.shellTop ∧
      core'.readReg .rdx = 2 ∧
      (∀ r ∈ ([.rbx, .rbp, .r12, .r13, .r14, .r15] : List GPR), core'.readReg r = core.readReg r)) ∨
    (∃ m, FaultsWithin ce.bytes ⟨core, paddr ce 32 0, fl⟩ m) := by
  have hL := plainLayout_numbers ce
  have hd : dataBase = 268435456 := rfl
  have htop8 : (UInt64.ofNat input.layout.shellTop - 8) + 8 = UInt64.ofNat input.layout.shellTop := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, toNat_small (by omega), show (8 : Word).toNat = 8 from rfl]; omega),
      toNat_small (by omega), show (8 : Word).toNat = 8 from rfl,
      Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt (by omega)]
  have e0 := pstep_movI ce (b := 32) (j := 0) (by decide) (r := .rdx) (v := 2)
    (by rw [PB.block_parseBad]; rfl) core fl
  let c0 := core.setReg .rdx 2
  have eret := pstep_ret ce (b := 32) (by decide) (by rw [PB.block_parseBad])
    (s := ⟨c0, paddr ce 32 1, fl⟩) (by rw [PB.block_parseBad]; rfl)
  cases hr : c0.memory.read64? (c0.readReg .rsp) with
  | error f =>
    rw [hr] at eret
    exact .inr ⟨2, 1, by decide, ⟨c0, paddr ce 32 1, fl⟩, f, run_one e0, eret⟩
  | ok tgt =>
    rw [hr] at eret
    have htgt : tgt = retAddr := by
      rw [read64?_value hr]; change core.memory.read64 (core.readReg .rsp) = _; rw [hrsp, hret]
    subst htgt
    refine .inl ⟨2, c0.setReg .rsp (c0.readReg .rsp + 8), fl, run_comp (run_one e0) (run_one eret),
      rfl, by show core.readReg .rsp + 8 = _; rw [hrsp, htop8],
      rfl, fun r hr' => (saved_read_setReg (.inr (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))) r hr').trans
        (saved_read_setReg (.inr (.inr (.inl rfl))) r hr')⟩

/-- Pure `ByteEval.run` lemma for `B.parseDone` (block 31): returns `rdx = r9` to `retAddr`. -/
private theorem parseDone_run {core : Core} {fl : ByteEval.Flags} {retAddr : Word}
    (hrsp : core.readReg .rsp = UInt64.ofNat input.layout.shellTop - 8)
    (hret : core.memory.read64 (UInt64.ofNat input.layout.shellTop - 8) = retAddr) :
    (∃ m core' fl', ByteEval.run ce.bytes fetchBase m ⟨core, paddr ce 31 0, fl⟩ = .ok ⟨core', retAddr, fl'⟩ ∧
      core'.memory = core.memory ∧
      core'.readReg .rsp = UInt64.ofNat input.layout.shellTop ∧
      core'.readReg .rax = core.readReg .rax ∧
      core'.readReg .rdx = core.readReg .r9 ∧
      (∀ r ∈ ([.rbx, .rbp, .r12, .r13, .r14, .r15] : List GPR), core'.readReg r = core.readReg r)) ∨
    (∃ m, FaultsWithin ce.bytes ⟨core, paddr ce 31 0, fl⟩ m) := by
  have hL := plainLayout_numbers ce
  have hd : dataBase = 268435456 := rfl
  have htop8 : (UInt64.ofNat input.layout.shellTop - 8) + 8 = UInt64.ofNat input.layout.shellTop := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, toNat_small (by omega), show (8 : Word).toNat = 8 from rfl]; omega),
      toNat_small (by omega), show (8 : Word).toNat = 8 from rfl,
      Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt (by omega)]
  have e0 := pstep_movR ce (b := 31) (j := 0) (by decide) (d := .rdx) (s := .r9)
    (by rw [PB.block_parseDone]; rfl) core fl
  let c0 := core.setReg .rdx (core.readReg .r9)
  have eret := pstep_ret ce (b := 31) (by decide) (by rw [PB.block_parseDone])
    (s := ⟨c0, paddr ce 31 1, fl⟩) (by rw [PB.block_parseDone]; rfl)
  cases hr : c0.memory.read64? (c0.readReg .rsp) with
  | error f =>
    rw [hr] at eret
    exact .inr ⟨2, 1, by decide, ⟨c0, paddr ce 31 1, fl⟩, f, run_one e0, eret⟩
  | ok tgt =>
    rw [hr] at eret
    have htgt : tgt = retAddr := by
      rw [read64?_value hr]; change core.memory.read64 (core.readReg .rsp) = _; rw [hrsp, hret]
    subst htgt
    refine .inl ⟨2, c0.setReg .rsp (c0.readReg .rsp + 8), fl, run_comp (run_one e0) (run_one eret),
      rfl, by show core.readReg .rsp + 8 = _; rw [hrsp, htop8],
      rfl, rfl, fun r hr' => (saved_read_setReg (.inr (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))) r hr').trans
        (saved_read_setReg (.inr (.inr (.inl rfl))) r hr')⟩

/-- Inductive loop invariant for `B.parseLoop` (blocks 24–30): runs over `a.drop j`
accumulating into `acc` until NUL or a non-digit byte. -/
private theorem parseLoop_run {a : List Nat} (ha : ∀ b ∈ a, 0 < b ∧ b < 256)
    {ptr retAddr : Word} :
    ∀ (k j acc : Nat) {core : Core} {fl : ByteEval.Flags},
      j + k = a.length →
      (∀ i < a.length, core.memory.bytes (ptr + UInt64.ofNat i) = UInt8.ofNat a[i]!) →
      core.memory.bytes (ptr + UInt64.ofNat a.length) = 0 →
      core.readReg .rsi = ptr + UInt64.ofNat j →
      core.readReg .rax = UInt64.ofNat (acc % 2 ^ 64) →
      core.readReg .r9 = (if 2 ^ 64 ≤ acc then 1 else 0) →
      core.readReg .rsp = UInt64.ofNat input.layout.shellTop - 8 →
      core.memory.read64 (UInt64.ofNat input.layout.shellTop - 8) = retAddr →
      (∃ m core' fl', ByteEval.run ce.bytes fetchBase m ⟨core, paddr ce 24 0, fl⟩ = .ok ⟨core', retAddr, fl'⟩ ∧
        core'.memory = core.memory ∧
        core'.readReg .rsp = UInt64.ofNat input.layout.shellTop ∧
        (∀ r ∈ ([.rbx, .rbp, .r12, .r13, .r14, .r15] : List GPR), core'.readReg r = core.readReg r) ∧
        match parseDigitsAux acc (a.drop j) with
        | none => core'.readReg .rdx = 2
        | some total =>
          if total < 2 ^ 64 then core'.readReg .rdx = 0 ∧ core'.readReg .rax = UInt64.ofNat total
          else core'.readReg .rdx = 1) ∨
      (∃ m, FaultsWithin ce.bytes ⟨core, paddr ce 24 0, fl⟩ m) := by
  intro k
  induction k with
  | zero =>
    intro j acc core fl hj hbytes hnul hsi hax hr9 hrsp hret
    have hjeq : j = a.length := by omega
    subst hjeq
    rw [List.drop_length]
    rcases pstep_load8 ce (b := 24) (j := 0) (by decide) (by rw [PB.block_parseLoop]; rfl) core fl with
      ⟨v, hrv, e0⟩ | ⟨f, efault⟩
    · let c0 := core.setReg .rcx (Width.w8.truncate v)
      have hcx0 : c0.readReg .rcx = 0 := by
        have hv : v = core.memory.read .w8 ((SB.at_ .rsi).eval core) := by
          unfold Memory.read? at hrv; split at hrv <;> cases hrv; rfl
        apply UInt64.toNat_inj.mp
        show (Width.w8.truncate v).toNat = 0
        rw [hv, load8_toNat, eval_at core .rsi (by decide), show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero, hsi, hnul]; rfl
      have hcond : Condition.holds .eq .w64 (c0.readReg .rcx) (signExtend32 (UInt32.ofNat 0)) = true := by
        rw [hcx0]; decide
      obtain ⟨f1, e1⟩ := prun_cmpI ce (b := 24) (j := 1) (by decide) (by rw [PB.block_parseLoop]; rfl)
        (by rw [PB.block_parseLoop]) c0 fl hcond
      have hto31 := run_comp (run_one e0) e1
      rcases parseDone_run ce (core := c0) (fl := f1) (retAddr := retAddr) hrsp hret with
        ⟨m', core', fl', hrun', hmem', hsp', hax', hdx', hsaved'⟩ | ⟨m', hf'⟩
      · refine .inl ⟨1 + 2 + m', core', fl', run_comp hto31 hrun', hmem', hsp',
          fun r hr' => (hsaved' r hr').trans (saved_read_setReg (.inr (.inl rfl)) r hr'), ?_⟩
        simp only [parseDigitsAux]
        by_cases hlt : acc < 2 ^ 64
        · simp only [hlt, ↓reduceIte]
          have hgeF : ¬ 2 ^ 64 ≤ acc := by omega
          refine ⟨by rw [hdx']; change c0.readReg .r9 = 0; rw [show c0.readReg .r9 = core.readReg .r9 from rfl, hr9, ite_eq_right hgeF],
                  by rw [hax']; change c0.readReg .rax = UInt64.ofNat acc; rw [show c0.readReg .rax = core.readReg .rax from rfl, hax, Nat.mod_eq_of_lt hlt]⟩
        · simp only [hlt, ↓reduceIte]
          have hgeT : 2 ^ 64 ≤ acc := by omega
          rw [hdx']; change c0.readReg .r9 = 1; rw [show c0.readReg .r9 = core.readReg .r9 from rfl, hr9, ite_eq_left hgeT]
      · exact .inr ⟨1 + 2 + m', hf'.shift hto31⟩
    · exact .inr ⟨1, 0, by decide, _, f, rfl, efault⟩
  | succ k ih =>
    intro j acc core fl hj hbytes hnul hsi hax hr9 hrsp hret
    have hjlt : j < a.length := by omega
    have hdrop : a.drop j = a[j] :: a.drop (j + 1) := List.drop_eq_getElem_cons hjlt
    have hb_bounds := ha a[j] (List.getElem_mem hjlt)
    rcases pstep_load8 ce (b := 24) (j := 0) (by decide) (by rw [PB.block_parseLoop]; rfl) core fl with
      ⟨v, hrv, e0⟩ | ⟨f, efault⟩
    · let c0 := core.setReg .rcx (Width.w8.truncate v)
      have hcxVal : (c0.readReg .rcx).toNat = a[j] := by
        have hv : v = core.memory.read .w8 ((SB.at_ .rsi).eval core) := by
          unfold Memory.read? at hrv; split at hrv <;> cases hrv; rfl
        show (Width.w8.truncate v).toNat = a[j]
        rw [hv, load8_toNat, eval_at core .rsi (by decide), show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero, hsi, hbytes j hjlt]
        simp [getElem!_pos a j hjlt]
        exact hb_bounds.2
      have hcxNe : c0.readReg .rcx ≠ 0 := ne_of_toNat (by rw [hcxVal]; change a[j] ≠ 0; omega)
      have hcond0 : Condition.holds .eq .w64 (c0.readReg .rcx) (signExtend32 (UInt32.ofNat 0)) = false := by
        rw [show signExtend32 (UInt32.ofNat 0) = 0 by decide, pholds_eq]
        simpa using hcxNe
      obtain ⟨f1, e1⟩ := prun_cmpI ce (b := 24) (j := 1) (by decide) (by rw [PB.block_parseLoop]; rfl)
        (by rw [PB.block_parseLoop]) c0 fl hcond0
      -- block 25: sub rcx, 48; cmp rcx, 9; ja 32 else 26
      obtain ⟨f2, e2⟩ := pstep_alu ce (b := 25) (j := 0) (by decide) (by rw [PB.block_parseDigit]; rfl) c0 f1
      let c1 := c0.writeReg .w64 .rcx (AluOp.sub.eval (c0.readReg .rcx) (signExtend32 (UInt32.ofNat 48)))
      have hcx1 : c1.readReg .rcx = c0.readReg .rcx - 48 := by
        change c0.readReg .rcx - signExtend32 (UInt32.ofNat 48) = _
        rw [show signExtend32 (UInt32.ofNat 48) = 48 by decide]
      have hto25_1 := run_comp (run_one e0) (run_comp e1 (run_one e2))
      by_cases hdig : 48 ≤ a[j] ∧ a[j] ≤ 57
      · have hcx1Nat : (c1.readReg .rcx).toNat = a[j] - 48 := by
          rw [hcx1, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hcxVal]; exact hdig.1), hcxVal]; rfl
        have hgtF : Condition.holds .unsignedGt .w64 (c1.readReg .rcx) (signExtend32 (UInt32.ofNat 9)) = false := by
          rw [show signExtend32 (UInt32.ofNat 9) = 9 by decide, pholds_unsignedGt, hcx1Nat]
          exact decide_eq_false (by show ¬ (9 : Word).toNat < a[j] - 48; rw [show (9 : Word).toNat = 9 from rfl]; omega)
        obtain ⟨f3, e3⟩ := prun_cmpI ce (b := 25) (j := 1) (by decide) (by rw [PB.block_parseDigit]; rfl)
          (by rw [PB.block_parseDigit]) c1 f2 hgtF
        -- block 26: mov r8, 10; mul r8; cmp rdx, 0; jne 27 else 28
        have e4 := pstep_movI ce (b := 26) (j := 0) (by decide) (r := .r8) (v := 10)
          (by rw [PB.block_parseMul]; rfl) c1 f3
        let c2 := c1.setReg .r8 10
        obtain ⟨f5, e5⟩ := pstep_umul64 ce (b := 26) (j := 1) (by decide) (by rw [PB.block_parseMul]; rfl) c2 f3
        let prod := 10 * (acc % 2 ^ 64)
        have hprodEq : (c2.readReg .r8).toNat * (c2.readReg .rax).toNat = prod := by
          have : c2.readReg .rax = UInt64.ofNat (acc % 2 ^ 64) := hax
          rw [this, show (c2.readReg .r8).toNat = 10 from rfl, toNat_small (Nat.mod_lt _ (by decide))]
        let c3 := (c2.setReg .rax (UInt64.ofNat (prod % 2 ^ 64))).setReg .rdx (UInt64.ofNat (prod / 2 ^ 64))
        have e5' : ByteEval.step ce.bytes fetchBase ⟨c2, paddr ce 26 1, f3⟩ = .ok ⟨c3, paddr ce 26 2, f5⟩ := by
          simpa [c3, hprodEq] using e5
        have hto26_2 := run_comp hto25_1 (run_comp e3 (run_comp (run_one e4) (run_one e5')))
        -- Reach block 28 (`parseAdd`) with `c4`, setting `r9 := 1` if `prod / 2^64 ≠ 0`
        have hto28 : ∃ m4 c4 f4, ByteEval.run ce.bytes fetchBase m4 ⟨core, paddr ce 24 0, fl⟩ =
            .ok ⟨c4, paddr ce 28 0, f4⟩ ∧
            c4.memory = core.memory ∧
            c4.readReg .rsp = UInt64.ofNat input.layout.shellTop - 8 ∧
            c4.readReg .rsi = ptr + UInt64.ofNat j ∧
            c4.readReg .rax = UInt64.ofNat (prod % 2 ^ 64) ∧
            c4.readReg .rcx = UInt64.ofNat (a[j] - 48) ∧
            c4.readReg .r9 = (if 2 ^ 64 ≤ acc ∨ 2 ^ 64 ≤ prod then 1 else 0) ∧
            (∀ r ∈ ([.rbx, .rbp, .r12, .r13, .r14, .r15] : List GPR), c4.readReg r = core.readReg r) := by
          have hcx3 : c3.readReg .rcx = UInt64.ofNat (a[j] - 48) :=
            UInt64.toNat_inj.mp (by rw [show c3.readReg .rcx = c1.readReg .rcx from rfl, hcx1Nat, toNat_small (by omega)])
          have hdxLt : prod / 2 ^ 64 < 2 ^ 64 := by
            have : acc % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide); omega
          by_cases hov1 : 2 ^ 64 ≤ prod
          · have hdxNe : c3.readReg .rdx ≠ 0 := ne_of_toNat (by
              show (UInt64.ofNat (prod / 2 ^ 64)).toNat ≠ 0; rw [toNat_small hdxLt]; omega)
            have hc6 : Condition.holds .ne .w64 (c3.readReg .rdx) (signExtend32 (UInt32.ofNat 0)) = true := by
              rw [show signExtend32 (UInt32.ofNat 0) = 0 by decide, pholds_ne]
              simpa using hdxNe
            obtain ⟨f6, e6⟩ := prun_cmpI ce (b := 26) (j := 2) (by decide) (by rw [PB.block_parseMul]; rfl)
              (by rw [PB.block_parseMul]) c3 f5 hc6
            have e7 := pstep_movI ce (b := 27) (j := 0) (by decide) (r := .r9) (v := 1)
              (by rw [PB.block_parseOvf1]; rfl) c3 f6
            let c4 := c3.setReg .r9 1
            have e8 := pstep_jump ce (b := 27) (by decide) (t := UInt32.ofNat 28)
              (by rw [PB.block_parseOvf1]) (s := ⟨c4, paddr ce 27 1, f6⟩) (by rw [PB.block_parseOvf1]; rfl)
            refine ⟨_, c4, f6, run_comp hto26_2 (run_comp e6 (run_comp (run_one e7) (run_one e8))),
              rfl, hrsp, hsi, rfl, hcx3, by simp only [hov1, or_true, ↓reduceIte]; rfl,
              fun r hr' => by rcases List.mem_cons.mp hr' with rfl | hr' <;> first | rfl |
                (rcases List.mem_cons.mp hr' with rfl | hr' <;> first | rfl |
                (rcases List.mem_cons.mp hr' with rfl | hr' <;> first | rfl |
                (rcases List.mem_cons.mp hr' with rfl | hr' <;> first | rfl |
                (rcases List.mem_cons.mp hr' with rfl | hr' <;> first | rfl |
                (rcases List.mem_cons.mp hr' with rfl | hr' <;> first | rfl | cases hr')))))⟩
          · have hdx0 : c3.readReg .rdx = 0 := UInt64.toNat_inj.mp (by
              show (UInt64.ofNat (prod / 2 ^ 64)).toNat = 0; rw [toNat_small hdxLt]; omega)
            have hc6 : Condition.holds .ne .w64 (c3.readReg .rdx) (signExtend32 (UInt32.ofNat 0)) = false := by
              rw [hdx0]; decide
            obtain ⟨f6, e6⟩ := prun_cmpI ce (b := 26) (j := 2) (by decide) (by rw [PB.block_parseMul]; rfl)
              (by rw [PB.block_parseMul]) c3 f5 hc6
            refine ⟨_, c3, f6, run_comp hto26_2 e6, rfl, hrsp, hsi, rfl, hcx3,
              by change core.readReg .r9 = _; simp only [hr9, hov1, or_false],
              fun r hr' => by rcases List.mem_cons.mp hr' with rfl | hr' <;> first | rfl |
                (rcases List.mem_cons.mp hr' with rfl | hr' <;> first | rfl |
                (rcases List.mem_cons.mp hr' with rfl | hr' <;> first | rfl |
                (rcases List.mem_cons.mp hr' with rfl | hr' <;> first | rfl |
                (rcases List.mem_cons.mp hr' with rfl | hr' <;> first | rfl |
                (rcases List.mem_cons.mp hr' with rfl | hr' <;> first | rfl | cases hr')))))⟩
        obtain ⟨m4, c4, f4, hrun4, hmem4, hrsp4, hsi4, hax4, hcx4, hr9_4, hsaved4⟩ := hto28
        -- block 28 (`parseAdd`): add rax, rcx; jb 29 else 30
        let d := a[j] - 48
        let nextAcc := acc * 10 + d
        have haddSum : c4.readReg .rax + c4.readReg .rcx = UInt64.ofNat (nextAcc % 2 ^ 64) := by
          rw [hax4, hcx4, ← UInt64.ofNat_add]
          apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat']
          show (prod % 2 ^ 64 + d) % 2 ^ 64 = (acc * 10 + d) % 2 ^ 64 % 2 ^ 64
          rw [Nat.mod_mod, parse_mod_step]
        have hcarry : (ByteEval.aluFlags .add .w64 (c4.readReg .rax) (c4.readReg .rcx)).test .unsignedLt =
            some (decide (2 ^ 64 ≤ prod % 2 ^ 64 + d)) := by
          rw [add64_carry_test, hax4, hcx4, toNat_small (Nat.mod_lt _ (by decide)), toNat_small (by omega)]
        -- Reach block 30 (`parseNext`) then block 24 (`parseLoop`)
        have hto24 : ∃ m5 c5 f5, ByteEval.run ce.bytes fetchBase m5 ⟨core, paddr ce 24 0, fl⟩ =
            .ok ⟨c5, paddr ce 24 0, f5⟩ ∧
            c5.memory = core.memory ∧
            c5.readReg .rsp = UInt64.ofNat input.layout.shellTop - 8 ∧
            c5.readReg .rsi = ptr + UInt64.ofNat (j + 1) ∧
            c5.readReg .rax = UInt64.ofNat (nextAcc % 2 ^ 64) ∧
            c5.readReg .r9 = (if 2 ^ 64 ≤ nextAcc then 1 else 0) ∧
            (∀ r ∈ ([.rbx, .rbp, .r12, .r13, .r14, .r15] : List GPR), c5.readReg r = core.readReg r) := by
          let f9 := ByteEval.aluFlags .add .w64 (c4.readReg .rax) (c4.readReg .rcx)
          by_cases hov2 : 2 ^ 64 ≤ prod % 2 ^ 64 + d
          · have hcf : f9.test .unsignedLt = some true := by
              rw [show f9 = _ from rfl, hcarry, decide_eq_true hov2]
            have e9 := prun_branch ce (b := 28) (by decide) (by rw [PB.block_parseAdd])
              (s := ⟨c4, paddr ce 28 0, f4⟩) (by rw [PB.block_parseAdd]; rfl)
              (exec_add64_mr _ _ _ _) hcf
            let c4' := c4.setReg .rax (c4.readReg .rax + c4.readReg .rcx)
            have e10 := pstep_movI ce (b := 29) (j := 0) (by decide) (r := .r9) (v := 1)
              (by rw [PB.block_parseOvf2]; rfl) c4' f9
            let c4'' := c4'.setReg .r9 1
            have e11 := pstep_jump ce (b := 29) (by decide) (t := UInt32.ofNat 30)
              (by rw [PB.block_parseOvf2]) (s := ⟨c4'', paddr ce 29 1, f9⟩) (by rw [PB.block_parseOvf2]; rfl)
            obtain ⟨f12, e12⟩ := pstep_alu ce (b := 30) (j := 0) (by decide) (by rw [PB.block_parseNext]; rfl) c4'' f9
            let c5 := c4''.writeReg .w64 .rsi (AluOp.add.eval (c4''.readReg .rsi) (signExtend32 (UInt32.ofNat 1)))
            have e13 := pstep_jump ce (b := 30) (by decide) (t := UInt32.ofNat 24)
              (by rw [PB.block_parseNext]) (s := ⟨c5, paddr ce 30 1, f12⟩) (by rw [PB.block_parseNext]; rfl)
            have hgeNext : 2 ^ 64 ≤ nextAcc := (parse_ovf_iff acc d).mp (.inr (.inr hov2))
            refine ⟨_, c5, f12, run_comp hrun4 (run_comp e9 (run_comp (run_one e10)
              (run_comp (run_one e11) (run_comp (run_one e12) (run_one e13))))),
              hmem4, hrsp4, ?_, ?_, by simp only [hgeNext, ↓reduceIte]; rfl, fun r hr' => by
                have h5 : c5.readReg r = c4.readReg r := by
                  rcases List.mem_cons.mp hr' with rfl | hr' <;> first | rfl |
                    (rcases List.mem_cons.mp hr' with rfl | hr' <;> first | rfl |
                    (rcases List.mem_cons.mp hr' with rfl | hr' <;> first | rfl |
                    (rcases List.mem_cons.mp hr' with rfl | hr' <;> first | rfl |
                    (rcases List.mem_cons.mp hr' with rfl | hr' <;> first | rfl |
                    (rcases List.mem_cons.mp hr' with rfl | hr' <;> first | rfl | cases hr')))))
                rw [h5]; exact hsaved4 r hr'⟩
            · change c4.readReg .rsi + signExtend32 (UInt32.ofNat 1) = _
              rw [hsi4, show signExtend32 (UInt32.ofNat 1) = UInt64.ofNat 1 by decide,
                UInt64.add_assoc, ← UInt64.ofNat_add]
            · change c4.readReg .rax + c4.readReg .rcx = _
              exact haddSum
          · have hcf : f9.test .unsignedLt = some false := by
              rw [show f9 = _ from rfl, hcarry, decide_eq_false hov2]
            have e9 := prun_branch ce (b := 28) (by decide) (by rw [PB.block_parseAdd])
              (s := ⟨c4, paddr ce 28 0, f4⟩) (by rw [PB.block_parseAdd]; rfl)
              (exec_add64_mr _ _ _ _) hcf
            let c4' := c4.setReg .rax (c4.readReg .rax + c4.readReg .rcx)
            obtain ⟨f12, e12⟩ := pstep_alu ce (b := 30) (j := 0) (by decide) (by rw [PB.block_parseNext]; rfl) c4' f9
            let c5 := c4'.writeReg .w64 .rsi (AluOp.add.eval (c4'.readReg .rsi) (signExtend32 (UInt32.ofNat 1)))
            have e13 := pstep_jump ce (b := 30) (by decide) (t := UInt32.ofNat 24)
              (by rw [PB.block_parseNext]) (s := ⟨c5, paddr ce 30 1, f12⟩) (by rw [PB.block_parseNext]; rfl)
            have hr9Next : c5.readReg .r9 = (if 2 ^ 64 ≤ nextAcc then 1 else 0) := by
              have h1 : c5.readReg .r9 = c4.readReg .r9 := rfl
              rw [h1, hr9_4]
              have hiff : (2 ^ 64 ≤ acc ∨ 2 ^ 64 ≤ prod) ↔ 2 ^ 64 ≤ nextAcc := by
                constructor
                · intro h; exact (parse_ovf_iff acc d).mp (h.elim .inl (fun h' => .inr (.inl h')))
                · intro h; rcases (parse_ovf_iff acc d).mpr h with h' | h' | h'
                  · exact .inl h'
                  · exact .inr h'
                  · exact absurd h' hov2
              by_cases hp : 2 ^ 64 ≤ acc ∨ 2 ^ 64 ≤ prod
              · rw [ite_eq_left hp, ite_eq_left (hiff.mp hp)]
              · rw [ite_eq_right hp, ite_eq_right (fun h => hp (hiff.mpr h))]
            refine ⟨_, c5, f12, run_comp hrun4 (run_comp e9 (run_comp (run_one e12) (run_one e13))),
              hmem4, hrsp4, ?_, ?_, hr9Next, fun r hr' => by
                have h5 : c5.readReg r = c4.readReg r := by
                  rcases List.mem_cons.mp hr' with rfl | hr' <;> first | rfl |
                    (rcases List.mem_cons.mp hr' with rfl | hr' <;> first | rfl |
                    (rcases List.mem_cons.mp hr' with rfl | hr' <;> first | rfl |
                    (rcases List.mem_cons.mp hr' with rfl | hr' <;> first | rfl |
                    (rcases List.mem_cons.mp hr' with rfl | hr' <;> first | rfl |
                    (rcases List.mem_cons.mp hr' with rfl | hr' <;> first | rfl | cases hr')))))
                rw [h5]; exact hsaved4 r hr'⟩
            · change c4.readReg .rsi + signExtend32 (UInt32.ofNat 1) = _
              rw [hsi4, show signExtend32 (UInt32.ofNat 1) = UInt64.ofNat 1 by decide,
                UInt64.add_assoc, ← UInt64.ofNat_add]
            · change c4.readReg .rax + c4.readReg .rcx = _
              exact haddSum
        obtain ⟨m5, c5, f5, hrun5, hmem5, hrsp5, hsi5, hax5, hr9_5, hsaved5⟩ := hto24
        rcases ih (j + 1) nextAcc (by omega) (by rw [hmem5]; exact hbytes) (by rw [hmem5]; exact hnul)
            hsi5 hax5 hr9_5 hrsp5 (by rw [hmem5]; exact hret) with
          ⟨m6, core', fl', hrun6, hmem6, hsp6, hsaved6, hres6⟩ | ⟨m6, hf6⟩
        · refine .inl ⟨m5 + m6, core', fl', run_comp hrun5 hrun6, by rw [hmem6, hmem5], hsp6,
            fun r hr' => by rw [hsaved6 r hr', hsaved5 r hr'], ?_⟩
          rw [hdrop]
          simp only [parseDigitsAux, hdig, and_self, ↓reduceIte]
          exact hres6
        · exact .inr ⟨m5 + m6, hf6.shift hrun5⟩
      · -- Not a digit: `c1.readReg .rcx > 9` (unsigned), jump to `parseBad` (block 32)
        have hcx1Gt : 9 < (c1.readReg .rcx).toNat := by
          rw [hcx1]
          have hsub : (c0.readReg .rcx - 48).toNat = (2 ^ 64 - 48 + a[j]) % 2 ^ 64 := by
            rw [UInt64.toNat_sub, hcxVal]; rfl
          rw [hsub]
          have hlt256 : a[j] < 256 := hb_bounds.2
          by_cases hlt48 : a[j] < 48
          · rw [Nat.mod_eq_of_lt (by omega)]; omega
          · rw [show 2 ^ 64 - 48 + a[j] = 2 ^ 64 + (a[j] - 48) by omega,
              Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
            omega
        have hgtT : Condition.holds .unsignedGt .w64 (c1.readReg .rcx) (signExtend32 (UInt32.ofNat 9)) = true := by
          rw [show signExtend32 (UInt32.ofNat 9) = 9 by decide, pholds_unsignedGt]
          exact decide_eq_true hcx1Gt
        obtain ⟨f3, e3⟩ := prun_cmpI ce (b := 25) (j := 1) (by decide) (by rw [PB.block_parseDigit]; rfl)
          (by rw [PB.block_parseDigit]) c1 f2 hgtT
        have hto32 := run_comp hto25_1 e3
        rcases parseBad_run ce (core := c1) (fl := f3) (retAddr := retAddr) hrsp hret with
          ⟨m', core', fl', hrun', hmem', hsp', hdx', hsaved'⟩ | ⟨m', hf'⟩
        · refine .inl ⟨_, core', fl', run_comp hto32 hrun', hmem', hsp',
            fun r hr' => (hsaved' r hr').trans ((saved_read_setReg (.inr (.inl rfl)) r hr').trans
              (saved_read_setReg (.inr (.inl rfl)) r hr')), ?_⟩
          rw [hdrop]
          simp only [parseDigitsAux, hdig, ↓reduceIte]
          exact hdx'
        · exact .inr ⟨_, hf'.shift hto32⟩
    · exact .inr ⟨1, 0, by decide, _, f, rfl, efault⟩

/-- **Top-level `B.parse` (block 23) theorem**: calling `B.parse` on NUL-terminated
C string `a` at `ptr` returns cleanly with `(rdx, rax)` matching `parseArgBytes a`
(or faults on memory). -/
theorem plain_parse_run {a : List Nat} (ha : ∀ b ∈ a, 0 < b ∧ b < 256)
    {ptr retAddr : Word} {core : Core} {fl : ByteEval.Flags}
    (hbytes : ∀ i < a.length, core.memory.bytes (ptr + UInt64.ofNat i) = UInt8.ofNat a[i]!)
    (hnul : core.memory.bytes (ptr + UInt64.ofNat a.length) = 0)
    (hsi : core.readReg .rsi = ptr)
    (hrsp : core.readReg .rsp = UInt64.ofNat input.layout.shellTop - 8)
    (hret : core.memory.read64 (UInt64.ofNat input.layout.shellTop - 8) = retAddr) :
    (∃ m core' fl', ByteEval.run ce.bytes fetchBase m ⟨core, paddr ce 23 0, fl⟩ = .ok ⟨core', retAddr, fl'⟩ ∧
      core'.memory = core.memory ∧
      core'.readReg .rsp = UInt64.ofNat input.layout.shellTop ∧
      (∀ r ∈ ([.rbx, .rbp, .r12, .r13, .r14, .r15] : List GPR), core'.readReg r = core.readReg r) ∧
      match parseArgBytes a with
      | .ok v => core'.readReg .rdx = 0 ∧ core'.readReg .rax = UInt64.ofNat v
      | .overflow => core'.readReg .rdx = 1
      | .bad => core'.readReg .rdx = 2) ∨
    (∃ m, FaultsWithin ce.bytes ⟨core, paddr ce 23 0, fl⟩ m) := by
  have e0 := pstep_movI ce (b := 23) (j := 0) (by decide) (r := .rax) (v := 0)
    (by rw [PB.block_parse]; rfl) core fl
  let c0 := core.setReg .rax 0
  have e1 := pstep_movI ce (b := 23) (j := 1) (by decide) (r := .r9) (v := 0)
    (by rw [PB.block_parse]; rfl) c0 fl
  let c1 := c0.setReg .r9 0
  have hpre := run_comp (run_one e0) (run_one e1)
  rcases pstep_load8 ce (b := 23) (j := 2) (by decide) (by rw [PB.block_parse]; rfl) c1 fl with
    ⟨v, hrv, e2⟩ | ⟨f, efault⟩
  · let c2 := c1.setReg .rcx (Width.w8.truncate v)
    cases a with
    | nil =>
      have hcx0 : c2.readReg .rcx = 0 := by
        have hv : v = core.memory.read .w8 ((SB.at_ .rsi).eval c1) := by
          unfold Memory.read? at hrv; split at hrv <;> cases hrv; rfl
        apply UInt64.toNat_inj.mp
        show (Width.w8.truncate v).toNat = 0
        rw [hv, load8_toNat, eval_at c1 .rsi (by decide), show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero]
        change (core.memory.bytes (core.readReg .rsi)).toNat = 0
        rw [hsi]; simpa using congrArg UInt8.toNat hnul
      have hcond : Condition.holds .eq .w64 (c2.readReg .rcx) (signExtend32 (UInt32.ofNat 0)) = true := by
        rw [hcx0]; decide
      obtain ⟨f3, e3⟩ := prun_cmpI ce (b := 23) (j := 3) (by decide) (by rw [PB.block_parse]; rfl)
        (by rw [PB.block_parse]) c2 fl hcond
      have hto32 := run_comp hpre (run_comp (run_one e2) e3)
      rcases parseBad_run ce (core := c2) (fl := f3) (retAddr := retAddr) hrsp hret with
        ⟨m', core', fl', hrun', hmem', hsp', hdx', hsaved'⟩ | ⟨m', hf'⟩
      · exact .inl ⟨_, core', fl', run_comp hto32 hrun', hmem', hsp',
          fun r hr' => (hsaved' r hr').trans ((saved_read_setReg (.inr (.inl rfl)) r hr').trans
            ((saved_read_setReg (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))) r hr').trans
              (saved_read_setReg (.inl rfl) r hr'))), hdx'⟩
      · exact .inr ⟨_, hf'.shift hto32⟩
    | cons b bs =>
      have hb0 := ha b List.mem_cons_self
      have hcxVal : (c2.readReg .rcx).toNat = b := by
        have hv : v = core.memory.read .w8 ((SB.at_ .rsi).eval c1) := by
          unfold Memory.read? at hrv; split at hrv <;> cases hrv; rfl
        show (Width.w8.truncate v).toNat = b
        rw [hv, load8_toNat, eval_at c1 .rsi (by decide), show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero]
        change (core.memory.bytes (core.readReg .rsi)).toNat = b
        rw [hsi]
        have h0 := hbytes 0 (Nat.zero_lt_succ _)
        rw [show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero] at h0
        simp only [List.getElem!_cons_zero] at h0
        rw [h0]; exact Nat.mod_eq_of_lt hb0.2
      have hcxNe : c2.readReg .rcx ≠ 0 := ne_of_toNat (by rw [hcxVal]; change b ≠ 0; omega)
      have hcond : Condition.holds .eq .w64 (c2.readReg .rcx) (signExtend32 (UInt32.ofNat 0)) = false := by
        rw [show signExtend32 (UInt32.ofNat 0) = 0 by decide, pholds_eq]
        simpa using hcxNe
      obtain ⟨f3, e3⟩ := prun_cmpI ce (b := 23) (j := 3) (by decide) (by rw [PB.block_parse]; rfl)
        (by rw [PB.block_parse]) c2 fl hcond
      have hto24 := run_comp hpre (run_comp (run_one e2) e3)
      rcases parseLoop_run ce ha (ptr := ptr) (retAddr := retAddr) (b :: bs).length 0 0
          (core := c2) (fl := f3) (Nat.zero_add _) hbytes hnul
          (by show core.readReg .rsi = ptr + 0; rw [hsi, UInt64.add_zero])
          rfl (by change (0 : Word) = if 2 ^ 64 ≤ 0 then 1 else 0; decide) hrsp hret with
        ⟨m', core', fl', hrun', hmem', hsp', hsaved', hres'⟩ | ⟨m', hf'⟩
      · refine .inl ⟨_, core', fl', run_comp hto24 hrun', hmem', hsp',
          fun r hr' => (hsaved' r hr').trans ((saved_read_setReg (.inr (.inl rfl)) r hr').trans
            ((saved_read_setReg (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))) r hr').trans
              (saved_read_setReg (.inl rfl) r hr'))), ?_⟩
        rw [List.drop_zero] at hres'
        simp only [parseArgBytes]
        cases hpd : parseDigitsAux 0 (b :: bs) with
        | none => rw [hpd] at hres'; exact hres'
        | some total =>
          rw [hpd] at hres'
          by_cases hlt : total < 2 ^ 64
          · simp only [hlt, ↓reduceIte] at hres' ⊢; exact hres'
          · simp only [hlt, ↓reduceIte] at hres' ⊢; exact hres'
      · exact .inr ⟨_, hf'.shift hto24⟩
  · exact .inr ⟨3, 2, by decide, _, f, hpre, efault⟩

end

end IxCC.X86.Exe.Plain
