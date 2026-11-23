import IxCC.Rt.Rc.Array.Proof.BasicOps

/-! # Operational Correctness of In-Place Array and ByteArray Mutations

Proves exact Lir operational correctness for unique O(1) in-place mutations and
boundary fast paths across all three native contiguous array kinds:
* `arrSetLimbs_unique_eval` & `arrSetLimbs_oob_eval`,
* `arrPushBoxed_unique_room_eval` & `arrPushLimbs_unique_room_eval`,
* `byteArrSet_unique_eval` & `byteArrPush_unique_room_eval`,
* `arrCopySliceLimbs_zero_len_eval` & `byteArrCopySlice_zero_len_eval`. -/

set_option autoImplicit false

namespace IxCC.Rt.Rc.Array

open Lir
open IxCC.Rt.Proof (WordAt addr_toNat write?_ok)
open IxCC.Rt.Rc.Procs (v i to cellAddr)
open IxCC.X86 (Memory)

/-! ## `arrSetLimbs` (O(1) unique in-place + OOB no-op) -/

/-- Unique (`refs = 1`) in-bounds `arrSetLimbs` writes directly in place with
zero allocation, returns the same `addr`, and establishes `LiveArrayCell` on
`elems.set idx val`. -/
theorem arrSetLimbs_unique_eval {mem addr cls cap elems}
    (h : LiveArrayCell mem addr 1 cls cap (.limbs elems))
    {idx : Nat} (hidx : idx < elems.length) (val context : Word) (clock : Nat) :
    ∃ mem',
      eval (arrayProgram fnSetLimbs) clock [addr, UInt64.ofNat idx, val] mem context =
        .ok ([addr], mem') ∧
      LiveArrayCell mem' addr 1 cls cap (.limbs (elems.set idx val)) := by
  have hf := arrayProgram_func_setLimbs fnSetLimbs
  have hbytes := (arrayBytes_eq_classBytes h.cls_lo h.cls_hi).1
  have hfit := h.fit; have hcap : cap ≤ wordCapOfClass cls := h.cap_fit; have hsz := h.size_le
  have hlen_lt : elems.length < 2 ^ 63 := by unfold arrayPayloadOffset at hbytes; simp [ArrayVal.size] at hsz; omega
  have hsz_w : WordAt mem (addr + 8) (UInt64.ofNat elems.length) := h.size_word
  have hcnt : loadWord mem .w32 .zero (addr + 4) = some (UInt64.ofNat 0) := h.count_load
  let slotAddr := addr + UInt64.ofNat (arrayPayloadOffset + 8 * idx)
  let mem' := mem.write .w64 slotAddr val
  have hwr : mem.write? .w64 slotAddr val = .ok mem' :=
    live_write64_ok h (by simp [ArrayVal.size] at hsz; omega) val
  refine ⟨mem', ?_, h.setWord_limbs hidx val⟩
  let e0 : Env := ((({} : Env).insert 0 addr).insert 1 (UInt64.ofNat idx)).insert 2 val
  let e1 := e0.insert 3 (UInt64.ofNat elems.length)
  let e2 := e1.insert 4 (UInt64.ofNat 0)
  have hinit := state_initial_of (p := arrayProgram fnSetLimbs) (args := [addr, UInt64.ofNat idx, val])
    (mem := mem) (context := context) hf rfl
  have hbr : Cond.holds .ult .w64 (UInt64.ofNat idx) (UInt64.ofNat elems.length) = true := by
    rw [cond_ult_w64, u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by omega)]
    exact decide_eq_true hidx
  have s00 := step_assign (p := arrayProgram fnSetLimbs) (fn := fnSetLimbs) (lbl := 0) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_8 (by simp only [e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]))
      (wordAt_load64 hsz_w))
  have s02 := step_br_true (p := arrayProgram fnSetLimbs) (fn := fnSetLimbs) (lbl := 0) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl rfl
    (by simp only [v, Arg.eval, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
    (by simp only [v, Arg.eval, e1, env_get_insert_self]) hbr rfl rfl rfl
  have s20 := step_assign (p := arrayProgram fnSetLimbs) (fn := fnSetLimbs) (lbl := 2) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_4 (by simp only [e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])) hcnt)
  have s23 := step_br_true (p := arrayProgram fnSetLimbs) (fn := fnSetLimbs) (lbl := 2) (rest := [])
    (mem := mem) (context := context) (env := e2) hf rfl rfl
    (by simp only [v, Arg.eval, e2, env_get_insert_self]; rfl) rfl (by decide) rfl rfl rfl
  have s30 := step_store (p := arrayProgram fnSetLimbs) (fn := fnSetLimbs) (lbl := 3) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e2) hf rfl (by decide) rfl
    (wordElemAddr_eval (by simp only [e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
      (by simp only [e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
      (by simp only [ArrayVal.size] at hsz; omega))
    (by simp only [v, Arg.eval, e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) hwr
  have sfin := final_ret_one (p := arrayProgram fnSetLimbs) (fn := fnSetLimbs) (lbl := 3)
    (mem := mem') (context := context) (env := e2) (res := addr) hf rfl rfl
    (by simp only [v, Arg.eval, e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
  apply (runs_eval hinit).eq
  exact .free s00 (.free s02 (.free s20 (.free s23 (.free s30 (.final sfin)))))

/-- Out-of-bounds `arrSetLimbs` is a pure no-op returning `addr` and untouched memory. -/
theorem arrSetLimbs_oob_eval {mem addr refs cls cap elems}
    (h : LiveArrayCell mem addr refs cls cap (.limbs elems))
    {idx : Word} (hoob : elems.length ≤ idx.toNat) (val context : Word) (clock : Nat) :
    eval (arrayProgram fnSetLimbs) clock [addr, idx, val] mem context = .ok ([addr], mem) := by
  have hf := arrayProgram_func_setLimbs fnSetLimbs
  have hbytes := (arrayBytes_eq_classBytes h.cls_lo h.cls_hi).1
  have hfit := h.fit; have hcap : cap ≤ wordCapOfClass cls := h.cap_fit; have hsz := h.size_le
  have hlen_lt : elems.length < 2 ^ 63 := by unfold arrayPayloadOffset at hbytes; simp [ArrayVal.size] at hsz; omega
  have hsz_w : WordAt mem (addr + 8) (UInt64.ofNat elems.length) := h.size_word
  let e0 : Env := ((({} : Env).insert 0 addr).insert 1 idx).insert 2 val
  let e1 := e0.insert 3 (UInt64.ofNat elems.length)
  have hinit := state_initial_of (p := arrayProgram fnSetLimbs) (args := [addr, idx, val])
    (mem := mem) (context := context) hf rfl
  have hbr : Cond.holds .ult .w64 idx (UInt64.ofNat elems.length) = false := by
    rw [cond_ult_w64, u64_toNat_ofNat_lt (by omega)]
    exact decide_eq_false (by omega)
  have s00 := step_assign (p := arrayProgram fnSetLimbs) (fn := fnSetLimbs) (lbl := 0) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_8 (by simp only [e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]))
      (wordAt_load64 hsz_w))
  have s01 := step_br_false (p := arrayProgram fnSetLimbs) (fn := fnSetLimbs) (lbl := 0) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl rfl
    (by simp only [v, Arg.eval, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
    (by simp only [v, Arg.eval, e1, env_get_insert_self]) hbr rfl rfl rfl
  have sfin := final_ret_one (p := arrayProgram fnSetLimbs) (fn := fnSetLimbs) (lbl := 1)
    (mem := mem) (context := context) (env := e1) (res := addr) hf rfl rfl
    (by simp only [v, Arg.eval, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
  apply (runs_eval hinit).eq
  exact .free s00 (.free s01 (.final sfin))

/-! ## `arrPushBoxed` & `arrPushLimbs` (O(1) unique in-place with room) -/

/-- Unique (`refs = 1`) boxed `Array` push with slack capacity (`elems.length < cap`)
writes directly in place with zero allocation and preserves `LiveArrayCell` on `elems ++ [val]`. -/
theorem arrPushBoxed_unique_room_eval {mem addr cls cap elems}
    (h : LiveArrayCell mem addr 1 cls cap (.boxed elems))
    (hroom : elems.length < cap) (val context : Word) (clock : Nat) :
    ∃ mem',
      eval (arrayProgram fnPushBoxed) clock [addr, val] mem context = .ok ([addr], mem') ∧
      LiveArrayCell mem' addr 1 cls cap (.boxed (elems ++ [val])) := by
  have hf := arrayProgram_func_pushBoxed fnPushBoxed
  have h24 := h.classBytes_ge_24
  have hbytes := (arrayBytes_eq_classBytes h.cls_lo h.cls_hi).1
  have hfit := h.fit; have hcap : cap ≤ wordCapOfClass cls := h.cap_fit
  have hcap_lt : cap < 2 ^ 63 := by unfold arrayPayloadOffset at hbytes; omega
  have hsz_w : WordAt mem (addr + 8) (UInt64.ofNat elems.length) := h.size_word
  have hcnt : loadWord mem .w32 .zero (addr + 4) = some (UInt64.ofNat 0) := h.count_load
  let slotAddr := addr + UInt64.ofNat (arrayPayloadOffset + 8 * elems.length)
  let m1 := mem.write .w64 slotAddr val
  let m2 := m1.write .w64 (addr + 8) (UInt64.ofNat (elems.length + 1))
  have hwr1 : mem.write? .w64 slotAddr val = .ok m1 :=
    live_write64_ok h (by omega) val
  have hwr2 : m1.write? .w64 (addr + 8) (UInt64.ofNat (elems.length + 1)) = .ok m2 := by
    apply write?_ok
    intro k hk
    have hk8 : k < 8 := by simpa [X86.Width.bytes] using hk
    have h8 : (addr + 8).toNat = addr.toNat + 8 := addr_toNat_8 (by omega)
    have hka : (addr + 8) + UInt64.ofNat k = addr + UInt64.ofNat (8 + k) := by
      apply UInt64.toNat_inj.mp
      rw [addr_toNat (by rw [h8]; omega), h8, addr_toNat (by omega)]; omega
    rw [hka]
    simpa [m1, Memory.write] using (h.access (8 + k) (by omega)).2
  refine ⟨m2, ?_, h.pushWord_boxed hroom val⟩
  let e0 : Env := (({} : Env).insert 0 addr).insert 1 val
  let e1 := e0.insert 2 (UInt64.ofNat elems.length)
  let e2 := e1.insert 3 (UInt64.ofNat cap)
  let e3 := e2.insert 4 (UInt64.ofNat 0)
  let e4 := e3.insert 5 (UInt64.ofNat (elems.length + 1))
  have hinit := state_initial_of (p := arrayProgram fnPushBoxed) (args := [addr, val])
    (mem := mem) (context := context) hf rfl
  have hltb : Cond.holds .ult .w64 (UInt64.ofNat elems.length) (UInt64.ofNat cap) = true := by
    rw [cond_ult_w64, u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by omega)]
    exact decide_eq_true hroom
  have s00 := step_assign (p := arrayProgram fnPushBoxed) (fn := fnPushBoxed) (lbl := 0) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_8 (by simp only [e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]))
      (wordAt_load64 hsz_w))
  have s01 := step_assign (p := arrayProgram fnPushBoxed) (fn := fnPushBoxed) (lbl := 0) (pos := 1) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_16 (by simp only [e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]))
      (wordAt_load64 h.cap_word))
  have s02 := step_assign (p := arrayProgram fnPushBoxed) (fn := fnPushBoxed) (lbl := 0) (pos := 2) (rest := [])
    (mem := mem) (context := context) (env := e2) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_4 (by simp only [e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])) hcnt)
  have s0_1 := step_br_true (p := arrayProgram fnPushBoxed) (fn := fnPushBoxed) (lbl := 0) (rest := [])
    (mem := mem) (context := context) (env := e3) hf rfl rfl
    (by simp only [v, Arg.eval, e3, env_get_insert_self]; rfl) rfl (by decide) rfl rfl rfl
  have s1_2 := step_br_true (p := arrayProgram fnPushBoxed) (fn := fnPushBoxed) (lbl := 1) (rest := [])
    (mem := mem) (context := context) (env := e3) hf rfl rfl
    (by simp only [v, Arg.eval, e3, e2, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
    (by simp only [v, Arg.eval, e3, e2, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) hltb rfl rfl rfl
  have s20 := step_store (p := arrayProgram fnPushBoxed) (fn := fnPushBoxed) (lbl := 2) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e3) hf rfl (by decide) rfl
    (wordElemAddr_eval (by simp only [e3, e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
      (by simp only [e3, e2, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) (by omega))
    (by simp only [v, Arg.eval, e3, e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) hwr1
  have s21 := step_assign (p := arrayProgram fnPushBoxed) (fn := fnPushBoxed) (lbl := 2) (pos := 1) (rest := [])
    (mem := m1) (context := context) (env := e3) hf rfl (by decide) rfl
    (rhs_bin_eval (by simp only [v, Arg.eval, e3, e2, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) rfl
      (binOp_add64 elems.length 1 (by omega)))
  have s22 := step_store (p := arrayProgram fnPushBoxed) (fn := fnPushBoxed) (lbl := 2) (pos := 2) (rest := [])
    (mem := m1) (context := context) (env := e4) hf rfl (by decide) rfl
    (cellAddr_eval_8 (by simp only [e4, e3, e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]))
    (by simp only [v, Arg.eval, e4, env_get_insert_self]) hwr2
  have sfin := final_ret_one (p := arrayProgram fnPushBoxed) (fn := fnPushBoxed) (lbl := 2)
    (mem := m2) (context := context) (env := e4) (res := addr) hf rfl rfl
    (by simp only [v, Arg.eval, e4, e3, e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
  apply (runs_eval hinit).eq
  exact .free s00 (.free s01 (.free s02 (.free s0_1 (.free s1_2 (.free s20 (.free s21 (.free s22 (.final sfin))))))))

/-- Unique (`refs = 1`) `LimbArray` (`Array UInt64`) push with slack capacity
writes directly in place with zero allocation and preserves `LiveArrayCell` on `elems ++ [val]`. -/
theorem arrPushLimbs_unique_room_eval {mem addr cls cap elems}
    (h : LiveArrayCell mem addr 1 cls cap (.limbs elems))
    (hroom : elems.length < cap) (val context : Word) (clock : Nat) :
    ∃ mem',
      eval (arrayProgram fnPushLimbs) clock [addr, val] mem context = .ok ([addr], mem') ∧
      LiveArrayCell mem' addr 1 cls cap (.limbs (elems ++ [val])) := by
  have hf := arrayProgram_func_pushLimbs fnPushLimbs
  have h24 := h.classBytes_ge_24
  have hbytes := (arrayBytes_eq_classBytes h.cls_lo h.cls_hi).1
  have hfit := h.fit; have hcap : cap ≤ wordCapOfClass cls := h.cap_fit
  have hcap_lt : cap < 2 ^ 63 := by unfold arrayPayloadOffset at hbytes; omega
  have hsz_w : WordAt mem (addr + 8) (UInt64.ofNat elems.length) := h.size_word
  have hcnt : loadWord mem .w32 .zero (addr + 4) = some (UInt64.ofNat 0) := h.count_load
  let slotAddr := addr + UInt64.ofNat (arrayPayloadOffset + 8 * elems.length)
  let m1 := mem.write .w64 slotAddr val
  let m2 := m1.write .w64 (addr + 8) (UInt64.ofNat (elems.length + 1))
  have hwr1 : mem.write? .w64 slotAddr val = .ok m1 :=
    live_write64_ok h (by omega) val
  have hwr2 : m1.write? .w64 (addr + 8) (UInt64.ofNat (elems.length + 1)) = .ok m2 := by
    apply write?_ok
    intro k hk
    have hk8 : k < 8 := by simpa [X86.Width.bytes] using hk
    have h8 : (addr + 8).toNat = addr.toNat + 8 := addr_toNat_8 (by omega)
    have hka : (addr + 8) + UInt64.ofNat k = addr + UInt64.ofNat (8 + k) := by
      apply UInt64.toNat_inj.mp
      rw [addr_toNat (by rw [h8]; omega), h8, addr_toNat (by omega)]; omega
    rw [hka]
    simpa [m1, Memory.write] using (h.access (8 + k) (by omega)).2
  refine ⟨m2, ?_, h.pushWord_limbs hroom val⟩
  let e0 : Env := (({} : Env).insert 0 addr).insert 1 val
  let e1 := e0.insert 2 (UInt64.ofNat elems.length)
  let e2 := e1.insert 3 (UInt64.ofNat cap)
  let e3 := e2.insert 4 (UInt64.ofNat 0)
  let e4 := e3.insert 5 (UInt64.ofNat (elems.length + 1))
  have hinit := state_initial_of (p := arrayProgram fnPushLimbs) (args := [addr, val])
    (mem := mem) (context := context) hf rfl
  have hltb : Cond.holds .ult .w64 (UInt64.ofNat elems.length) (UInt64.ofNat cap) = true := by
    rw [cond_ult_w64, u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by omega)]
    exact decide_eq_true hroom
  have s00 := step_assign (p := arrayProgram fnPushLimbs) (fn := fnPushLimbs) (lbl := 0) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_8 (by simp only [e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]))
      (wordAt_load64 hsz_w))
  have s01 := step_assign (p := arrayProgram fnPushLimbs) (fn := fnPushLimbs) (lbl := 0) (pos := 1) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_16 (by simp only [e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]))
      (wordAt_load64 h.cap_word))
  have s02 := step_assign (p := arrayProgram fnPushLimbs) (fn := fnPushLimbs) (lbl := 0) (pos := 2) (rest := [])
    (mem := mem) (context := context) (env := e2) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_4 (by simp only [e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])) hcnt)
  have s0_1 := step_br_true (p := arrayProgram fnPushLimbs) (fn := fnPushLimbs) (lbl := 0) (rest := [])
    (mem := mem) (context := context) (env := e3) hf rfl rfl
    (by simp only [v, Arg.eval, e3, env_get_insert_self]; rfl) rfl (by decide) rfl rfl rfl
  have s1_2 := step_br_true (p := arrayProgram fnPushLimbs) (fn := fnPushLimbs) (lbl := 1) (rest := [])
    (mem := mem) (context := context) (env := e3) hf rfl rfl
    (by simp only [v, Arg.eval, e3, e2, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
    (by simp only [v, Arg.eval, e3, e2, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) hltb rfl rfl rfl
  have s20 := step_store (p := arrayProgram fnPushLimbs) (fn := fnPushLimbs) (lbl := 2) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e3) hf rfl (by decide) rfl
    (wordElemAddr_eval (by simp only [e3, e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
      (by simp only [e3, e2, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) (by omega))
    (by simp only [v, Arg.eval, e3, e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) hwr1
  have s21 := step_assign (p := arrayProgram fnPushLimbs) (fn := fnPushLimbs) (lbl := 2) (pos := 1) (rest := [])
    (mem := m1) (context := context) (env := e3) hf rfl (by decide) rfl
    (rhs_bin_eval (by simp only [v, Arg.eval, e3, e2, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) rfl
      (binOp_add64 elems.length 1 (by omega)))
  have s22 := step_store (p := arrayProgram fnPushLimbs) (fn := fnPushLimbs) (lbl := 2) (pos := 2) (rest := [])
    (mem := m1) (context := context) (env := e4) hf rfl (by decide) rfl
    (cellAddr_eval_8 (by simp only [e4, e3, e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]))
    (by simp only [v, Arg.eval, e4, env_get_insert_self]) hwr2
  have sfin := final_ret_one (p := arrayProgram fnPushLimbs) (fn := fnPushLimbs) (lbl := 2)
    (mem := m2) (context := context) (env := e4) (res := addr) hf rfl rfl
    (by simp only [v, Arg.eval, e4, e3, e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
  apply (runs_eval hinit).eq
  exact .free s00 (.free s01 (.free s02 (.free s0_1 (.free s1_2 (.free s20 (.free s21 (.free s22 (.final sfin))))))))

/-! ## `byteArrSet` & `byteArrPush` (O(1) unique in-place packed `.w8` mutations) -/

/-- Unique (`refs = 1`) in-bounds `byteArrSet` executes an O(1) in-place `.w8`
store and preserves `LiveArrayCell` on `data.set idx val.toUInt8`. -/
theorem byteArrSet_unique_eval {mem addr cls cap data}
    (h : LiveArrayCell mem addr 1 cls cap (.bytes data))
    {idx : Nat} (hidx : idx < data.length) (val context : Word) (clock : Nat) :
    ∃ mem',
      eval (arrayProgram fnByteSet) clock [addr, UInt64.ofNat idx, val] mem context =
        .ok ([addr], mem') ∧
      LiveArrayCell mem' addr 1 cls cap (.bytes (data.set idx val.toUInt8)) := by
  have hf := arrayProgram_func_byteSet fnByteSet
  have hbytes := (arrayBytes_eq_classBytes h.cls_lo h.cls_hi).2
  have hfit := h.fit; have hcap : cap ≤ byteCapOfClass cls := h.cap_fit; have hsz := h.size_le
  have hlen_lt : data.length < 2 ^ 63 := by unfold arrayPayloadOffset at hbytes; simp [ArrayVal.size] at hsz; omega
  have hsz_w : WordAt mem (addr + 8) (UInt64.ofNat data.length) := h.size_word
  have hcnt : loadWord mem .w32 .zero (addr + 4) = some (UInt64.ofNat 0) := h.count_load
  let slotAddr := addr + UInt64.ofNat (arrayPayloadOffset + idx)
  let mem' := mem.write .w8 slotAddr val
  have hwr : mem.write? .w8 slotAddr val = .ok mem' :=
    live_write8_ok h (by simp [ArrayVal.size] at hsz; omega) val
  refine ⟨mem', ?_, h.setByte_inPlace hidx val⟩
  let e0 : Env := ((({} : Env).insert 0 addr).insert 1 (UInt64.ofNat idx)).insert 2 val
  let e1 := e0.insert 3 (UInt64.ofNat data.length)
  let e2 := e1.insert 4 (UInt64.ofNat 0)
  have hinit := state_initial_of (p := arrayProgram fnByteSet) (args := [addr, UInt64.ofNat idx, val])
    (mem := mem) (context := context) hf rfl
  have hbr : Cond.holds .ult .w64 (UInt64.ofNat idx) (UInt64.ofNat data.length) = true := by
    rw [cond_ult_w64, u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by omega)]
    exact decide_eq_true hidx
  have s00 := step_assign (p := arrayProgram fnByteSet) (fn := fnByteSet) (lbl := 0) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_8 (by simp only [e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]))
      (wordAt_load64 hsz_w))
  have s02 := step_br_true (p := arrayProgram fnByteSet) (fn := fnByteSet) (lbl := 0) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl rfl
    (by simp only [v, Arg.eval, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
    (by simp only [v, Arg.eval, e1, env_get_insert_self]) hbr rfl rfl rfl
  have s20 := step_assign (p := arrayProgram fnByteSet) (fn := fnByteSet) (lbl := 2) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_4 (by simp only [e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])) hcnt)
  have s23 := step_br_true (p := arrayProgram fnByteSet) (fn := fnByteSet) (lbl := 2) (rest := [])
    (mem := mem) (context := context) (env := e2) hf rfl rfl
    (by simp only [v, Arg.eval, e2, env_get_insert_self]; rfl) rfl (by decide) rfl rfl rfl
  have s30 := step_store (p := arrayProgram fnByteSet) (fn := fnByteSet) (lbl := 3) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e2) hf rfl (by decide) rfl
    (byteElemAddr_eval (by simp only [e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
      (by simp only [e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) (by omega))
    (by simp only [v, Arg.eval, e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) hwr
  have sfin := final_ret_one (p := arrayProgram fnByteSet) (fn := fnByteSet) (lbl := 3)
    (mem := mem') (context := context) (env := e2) (res := addr) hf rfl rfl
    (by simp only [v, Arg.eval, e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
  apply (runs_eval hinit).eq
  exact .free s00 (.free s02 (.free s20 (.free s23 (.free s30 (.final sfin)))))

/-- Unique (`refs = 1`) `ByteArray` push with slack capacity (`data.length < cap`)
writes directly in place with zero allocation and preserves `LiveArrayCell` on `data ++ [val.toUInt8]`. -/
theorem byteArrPush_unique_room_eval {mem addr cls cap data}
    (h : LiveArrayCell mem addr 1 cls cap (.bytes data))
    (hroom : data.length < cap) (val context : Word) (clock : Nat) :
    ∃ mem',
      eval (arrayProgram fnBytePush) clock [addr, val] mem context = .ok ([addr], mem') ∧
      LiveArrayCell mem' addr 1 cls cap (.bytes (data ++ [val.toUInt8])) := by
  have hf := arrayProgram_func_bytePush fnBytePush
  have h24 := h.classBytes_ge_24
  have hbytes := (arrayBytes_eq_classBytes h.cls_lo h.cls_hi).2
  have hfit := h.fit; have hcap : cap ≤ byteCapOfClass cls := h.cap_fit
  have hcap_lt : cap < 2 ^ 63 := by unfold arrayPayloadOffset at hbytes; omega
  have hsz_w : WordAt mem (addr + 8) (UInt64.ofNat data.length) := h.size_word
  have hcnt : loadWord mem .w32 .zero (addr + 4) = some (UInt64.ofNat 0) := h.count_load
  let slotAddr := addr + UInt64.ofNat (arrayPayloadOffset + data.length)
  let m1 := mem.write .w8 slotAddr val
  let m2 := m1.write .w64 (addr + 8) (UInt64.ofNat (data.length + 1))
  have hwr1 : mem.write? .w8 slotAddr val = .ok m1 :=
    live_write8_ok h (by omega) val
  have hwr2 : m1.write? .w64 (addr + 8) (UInt64.ofNat (data.length + 1)) = .ok m2 := by
    apply write?_ok
    intro k hk
    have hk8 : k < 8 := by simpa [X86.Width.bytes] using hk
    have h8 : (addr + 8).toNat = addr.toNat + 8 := addr_toNat_8 (by omega)
    have hka : (addr + 8) + UInt64.ofNat k = addr + UInt64.ofNat (8 + k) := by
      apply UInt64.toNat_inj.mp
      rw [addr_toNat (by rw [h8]; omega), h8, addr_toNat (by omega)]; omega
    rw [hka]
    simpa [m1, Memory.write] using (h.access (8 + k) (by omega)).2
  refine ⟨m2, ?_, h.pushByte_inPlace hroom val⟩
  let e0 : Env := (({} : Env).insert 0 addr).insert 1 val
  let e1 := e0.insert 2 (UInt64.ofNat data.length)
  let e2 := e1.insert 3 (UInt64.ofNat cap)
  let e3 := e2.insert 4 (UInt64.ofNat 0)
  let e4 := e3.insert 5 (UInt64.ofNat (data.length + 1))
  have hinit := state_initial_of (p := arrayProgram fnBytePush) (args := [addr, val])
    (mem := mem) (context := context) hf rfl
  have hltb : Cond.holds .ult .w64 (UInt64.ofNat data.length) (UInt64.ofNat cap) = true := by
    rw [cond_ult_w64, u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by omega)]
    exact decide_eq_true hroom
  have s00 := step_assign (p := arrayProgram fnBytePush) (fn := fnBytePush) (lbl := 0) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_8 (by simp only [e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]))
      (wordAt_load64 hsz_w))
  have s01 := step_assign (p := arrayProgram fnBytePush) (fn := fnBytePush) (lbl := 0) (pos := 1) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_16 (by simp only [e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]))
      (wordAt_load64 h.cap_word))
  have s02 := step_assign (p := arrayProgram fnBytePush) (fn := fnBytePush) (lbl := 0) (pos := 2) (rest := [])
    (mem := mem) (context := context) (env := e2) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_4 (by simp only [e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])) hcnt)
  have s0_1 := step_br_true (p := arrayProgram fnBytePush) (fn := fnBytePush) (lbl := 0) (rest := [])
    (mem := mem) (context := context) (env := e3) hf rfl rfl
    (by simp only [v, Arg.eval, e3, env_get_insert_self]; rfl) rfl (by decide) rfl rfl rfl
  have s1_2 := step_br_true (p := arrayProgram fnBytePush) (fn := fnBytePush) (lbl := 1) (rest := [])
    (mem := mem) (context := context) (env := e3) hf rfl rfl
    (by simp only [v, Arg.eval, e3, e2, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
    (by simp only [v, Arg.eval, e3, e2, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) hltb rfl rfl rfl
  have s20 := step_store (p := arrayProgram fnBytePush) (fn := fnBytePush) (lbl := 2) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e3) hf rfl (by decide) rfl
    (byteElemAddr_eval (by simp only [e3, e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
      (by simp only [e3, e2, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) (by omega))
    (by simp only [v, Arg.eval, e3, e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) hwr1
  have s21 := step_assign (p := arrayProgram fnBytePush) (fn := fnBytePush) (lbl := 2) (pos := 1) (rest := [])
    (mem := m1) (context := context) (env := e3) hf rfl (by decide) rfl
    (rhs_bin_eval (by simp only [v, Arg.eval, e3, e2, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) rfl
      (binOp_add64 data.length 1 (by omega)))
  have s22 := step_store (p := arrayProgram fnBytePush) (fn := fnBytePush) (lbl := 2) (pos := 2) (rest := [])
    (mem := m1) (context := context) (env := e4) hf rfl (by decide) rfl
    (cellAddr_eval_8 (by simp only [e4, e3, e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]))
    (by simp only [v, Arg.eval, e4, env_get_insert_self]) hwr2
  have sfin := final_ret_one (p := arrayProgram fnBytePush) (fn := fnBytePush) (lbl := 2)
    (mem := m2) (context := context) (env := e4) (res := addr) hf rfl rfl
    (by simp only [v, Arg.eval, e4, e3, e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
  apply (runs_eval hinit).eq
  exact .free s00 (.free s01 (.free s02 (.free s0_1 (.free s1_2 (.free s20 (.free s21 (.free s22 (.final sfin))))))))

/-! ## `arrCopySliceLimbs` & `byteArrCopySlice` zero-length fast paths -/

theorem arrCopySliceLimbs_zero_len_eval {mem src dest r1 c1 cap1 r2 c2 cap2 xs ys}
    (hs : LiveArrayCell mem src r1 c1 cap1 (.limbs xs))
    (hd : LiveArrayCell mem dest r2 c2 cap2 (.limbs ys))
    (srcOff destOff context : Word) (clock : Nat) :
    eval (arrayProgram fnCopySliceLimbs) clock [src, srcOff, dest, destOff, 0] mem context =
      .ok ([dest], mem) := by
  have hf := arrayProgram_func_copySliceLimbs fnCopySliceLimbs
  have hxs_w : WordAt mem (src + 8) (UInt64.ofNat xs.length) := hs.size_word
  have hys_w : WordAt mem (dest + 8) (UInt64.ofNat ys.length) := hd.size_word
  let e0 : Env := ((((({} : Env).insert 0 src).insert 1 srcOff).insert 2 dest).insert 3 destOff).insert 4 0
  let e1 := e0.insert 5 (UInt64.ofNat xs.length)
  let e2 := e1.insert 6 (UInt64.ofNat ys.length)
  have hinit := state_initial_of (p := arrayProgram fnCopySliceLimbs) (args := [src, srcOff, dest, destOff, 0])
    (mem := mem) (context := context) hf rfl
  have s00 := step_assign (p := arrayProgram fnCopySliceLimbs) (fn := fnCopySliceLimbs) (lbl := 0) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_8 (by simp only [e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]))
      (wordAt_load64 hxs_w))
  have s01 := step_assign (p := arrayProgram fnCopySliceLimbs) (fn := fnCopySliceLimbs) (lbl := 0) (pos := 1) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_8 (by simp only [e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]))
      (wordAt_load64 hys_w))
  have s0_1 := step_br_true (p := arrayProgram fnCopySliceLimbs) (fn := fnCopySliceLimbs) (lbl := 0) (rest := [])
    (mem := mem) (context := context) (env := e2) hf rfl rfl
    (by simp only [v, Arg.eval, e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]; rfl) rfl (by decide) rfl rfl rfl
  have sfin := final_ret_one (p := arrayProgram fnCopySliceLimbs) (fn := fnCopySliceLimbs) (lbl := 1)
    (mem := mem) (context := context) (env := e2) (res := dest) hf rfl rfl
    (by simp only [v, Arg.eval, e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
  apply (runs_eval hinit).eq
  exact .free s00 (.free s01 (.free s0_1 (.final sfin)))

theorem byteArrCopySlice_zero_len_eval {mem src dest r1 c1 cap1 r2 c2 cap2 xs ys}
    (hs : LiveArrayCell mem src r1 c1 cap1 (.bytes xs))
    (hd : LiveArrayCell mem dest r2 c2 cap2 (.bytes ys))
    (srcOff destOff context : Word) (clock : Nat) :
    eval (arrayProgram fnByteCopySlice) clock [src, srcOff, dest, destOff, 0] mem context =
      .ok ([dest], mem) := by
  have hf := arrayProgram_func_byteCopySlice fnByteCopySlice
  have hxs_w : WordAt mem (src + 8) (UInt64.ofNat xs.length) := hs.size_word
  have hys_w : WordAt mem (dest + 8) (UInt64.ofNat ys.length) := hd.size_word
  let e0 : Env := ((((({} : Env).insert 0 src).insert 1 srcOff).insert 2 dest).insert 3 destOff).insert 4 0
  let e1 := e0.insert 5 (UInt64.ofNat xs.length)
  let e2 := e1.insert 6 (UInt64.ofNat ys.length)
  have hinit := state_initial_of (p := arrayProgram fnByteCopySlice) (args := [src, srcOff, dest, destOff, 0])
    (mem := mem) (context := context) hf rfl
  have s00 := step_assign (p := arrayProgram fnByteCopySlice) (fn := fnByteCopySlice) (lbl := 0) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_8 (by simp only [e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]))
      (wordAt_load64 hxs_w))
  have s01 := step_assign (p := arrayProgram fnByteCopySlice) (fn := fnByteCopySlice) (lbl := 0) (pos := 1) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_8 (by simp only [e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]))
      (wordAt_load64 hys_w))
  have s0_1 := step_br_true (p := arrayProgram fnByteCopySlice) (fn := fnByteCopySlice) (lbl := 0) (rest := [])
    (mem := mem) (context := context) (env := e2) hf rfl rfl
    (by simp only [v, Arg.eval, e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]; rfl) rfl (by decide) rfl rfl rfl
  have sfin := final_ret_one (p := arrayProgram fnByteCopySlice) (fn := fnByteCopySlice) (lbl := 1)
    (mem := mem) (context := context) (env := e2) (res := dest) hf rfl rfl
    (by simp only [v, Arg.eval, e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
  apply (runs_eval hinit).eq
  exact .free s00 (.free s01 (.free s0_1 (.final sfin)))

end IxCC.Rt.Rc.Array
