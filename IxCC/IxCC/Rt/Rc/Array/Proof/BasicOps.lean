import IxCC.Rt.Rc.Array.Proof.StepLemmas

/-! # Operational Correctness of Array Queries and In-Place Pop

Proves exact Lir operational correctness of:
* `arrSize` and `arrCap` on BOTH `LiveArrayCell` (all 3 kinds) and
  `StaticArrayCell` (immortal `.rodata`, all 3 kinds),
* `arrGet` on boxed & limb arrays (live + static `.rodata`) and OOB trap,
* `byteArrGet` on `ByteArray` (live + static `.rodata`) and OOB trap,
* `arrPopLimbs` and `byteArrPop` (empty no-op + O(1) unique in-place pop
  preserving `LiveArrayCell` with `dropLast`). -/

set_option autoImplicit false

namespace IxCC.Rt.Rc.Array

open Lir
open IxCC.Rt.Proof (WordAt addr_toNat write?_ok)
open IxCC.Rt.Rc.Procs (v i to cellAddr)
open IxCC.X86 (Memory)

theorem live_write64_ok {mem addr refs cls cap val}
    (h : LiveArrayCell mem addr refs cls cap val) {off : Nat} (hoff : off + 8 ≤ classBytes cls)
    (w : Word) :
    mem.write? .w64 (addr + UInt64.ofNat off) w = .ok (mem.write .w64 (addr + UInt64.ofNat off) w) := by
  have hfit := h.fit
  apply write?_ok
  intro k hk
  have hk8 : k < 8 := by simpa [X86.Width.bytes] using hk
  have ho : (addr + UInt64.ofNat off).toNat = addr.toNat + off := addr_toNat (by omega)
  have hka : (addr + UInt64.ofNat off) + UInt64.ofNat k = addr + UInt64.ofNat (off + k) := by
    apply UInt64.toNat_inj.mp
    rw [addr_toNat (by rw [ho]; omega), ho, addr_toNat (by omega)]
    omega
  rw [hka]
  exact (h.access (off + k) (by omega)).2

theorem live_write8_ok {mem addr refs cls cap val}
    (h : LiveArrayCell mem addr refs cls cap val) {off : Nat} (hoff : off < classBytes cls)
    (w : Word) :
    mem.write? .w8 (addr + UInt64.ofNat off) w = .ok (mem.write .w8 (addr + UInt64.ofNat off) w) := by
  apply write?_ok
  intro k hk
  have hk0 : k = 0 := by simp [X86.Width.bytes] at hk; omega
  subst hk0
  rw [show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero]
  exact (h.access off hoff).2

/-! ## `arrSize` and `arrCap` -/

theorem arrSize_live_eval {mem addr refs cls cap val}
    (h : LiveArrayCell mem addr refs cls cap val) (context : Word) (clock : Nat) :
    eval (arrayProgram fnSize) clock [addr] mem context =
      .ok ([UInt64.ofNat val.size], mem) := by
  have hf := arrayProgram_func_size fnSize
  let e0 : Env := ({} : Env).insert 0 addr
  let e1 := e0.insert 1 (UInt64.ofNat val.size)
  have hinit := state_initial_of (p := arrayProgram fnSize) (args := [addr]) (mem := mem) (context := context) hf rfl
  have s0 := step_assign (p := arrayProgram fnSize) (fn := fnSize) (lbl := 0) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_8 (by simp only [e0, env_get_insert_self]))
      (wordAt_load64 h.size_word))
  have sfin := final_ret_one (p := arrayProgram fnSize) (fn := fnSize) (lbl := 0)
    (mem := mem) (context := context) (env := e1) (res := UInt64.ofNat val.size) hf rfl rfl
    (by simp only [v, Arg.eval, e1, env_get_insert_self])
  apply (runs_eval hinit).eq
  exact .free s0 (.final sfin)

theorem arrSize_static_eval {mem addr cap val}
    (h : StaticArrayCell mem addr cap val) (context : Word) (clock : Nat) :
    eval (arrayProgram fnSize) clock [addr] mem context =
      .ok ([UInt64.ofNat val.size], mem) := by
  have hf := arrayProgram_func_size fnSize
  let e0 : Env := ({} : Env).insert 0 addr
  let e1 := e0.insert 1 (UInt64.ofNat val.size)
  have hinit := state_initial_of (p := arrayProgram fnSize) (args := [addr]) (mem := mem) (context := context) hf rfl
  have s0 := step_assign (p := arrayProgram fnSize) (fn := fnSize) (lbl := 0) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_8 (by simp only [e0, env_get_insert_self]))
      (wordAt_load64 h.size_word))
  have sfin := final_ret_one (p := arrayProgram fnSize) (fn := fnSize) (lbl := 0)
    (mem := mem) (context := context) (env := e1) (res := UInt64.ofNat val.size) hf rfl rfl
    (by simp only [v, Arg.eval, e1, env_get_insert_self])
  apply (runs_eval hinit).eq
  exact .free s0 (.final sfin)

theorem arrCap_live_eval {mem addr refs cls cap val}
    (h : LiveArrayCell mem addr refs cls cap val) (context : Word) (clock : Nat) :
    eval (arrayProgram fnCap) clock [addr] mem context =
      .ok ([UInt64.ofNat cap], mem) := by
  have hf := arrayProgram_func_cap fnCap
  let e0 : Env := ({} : Env).insert 0 addr
  let e1 := e0.insert 1 (UInt64.ofNat cap)
  have hinit := state_initial_of (p := arrayProgram fnCap) (args := [addr]) (mem := mem) (context := context) hf rfl
  have s0 := step_assign (p := arrayProgram fnCap) (fn := fnCap) (lbl := 0) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_16 (by simp only [e0, env_get_insert_self]))
      (wordAt_load64 h.cap_word))
  have sfin := final_ret_one (p := arrayProgram fnCap) (fn := fnCap) (lbl := 0)
    (mem := mem) (context := context) (env := e1) (res := UInt64.ofNat cap) hf rfl rfl
    (by simp only [v, Arg.eval, e1, env_get_insert_self])
  apply (runs_eval hinit).eq
  exact .free s0 (.final sfin)

theorem arrCap_static_eval {mem addr cap val}
    (h : StaticArrayCell mem addr cap val) (context : Word) (clock : Nat) :
    eval (arrayProgram fnCap) clock [addr] mem context =
      .ok ([UInt64.ofNat cap], mem) := by
  have hf := arrayProgram_func_cap fnCap
  let e0 : Env := ({} : Env).insert 0 addr
  let e1 := e0.insert 1 (UInt64.ofNat cap)
  have hinit := state_initial_of (p := arrayProgram fnCap) (args := [addr]) (mem := mem) (context := context) hf rfl
  have s0 := step_assign (p := arrayProgram fnCap) (fn := fnCap) (lbl := 0) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_16 (by simp only [e0, env_get_insert_self]))
      (wordAt_load64 h.cap_word))
  have sfin := final_ret_one (p := arrayProgram fnCap) (fn := fnCap) (lbl := 0)
    (mem := mem) (context := context) (env := e1) (res := UInt64.ofNat cap) hf rfl rfl
    (by simp only [v, Arg.eval, e1, env_get_insert_self])
  apply (runs_eval hinit).eq
  exact .free s0 (.final sfin)

/-! ## `arrGet` and `byteArrGet` -/

private theorem arrGet_word_core {mem : Memory} {addr elem : Word} {len idx : Nat}
    (hsz : WordAt mem (addr + 8) (UInt64.ofNat len))
    (helem : WordAt mem (addr + UInt64.ofNat (arrayPayloadOffset + 8 * idx)) elem)
    (hidx : idx < len) (hlen : 24 + 8 * len < 2 ^ 64) (context : Word) (clock : Nat) :
    eval (arrayProgram fnGetWord) clock [addr, UInt64.ofNat idx] mem context =
      .ok ([elem], mem) := by
  have hf := arrayProgram_func_getWord fnGetWord
  let e0 : Env := (({} : Env).insert 0 addr).insert 1 (UInt64.ofNat idx)
  let e1 := e0.insert 2 (UInt64.ofNat len)
  let e2 := e1.insert 3 elem
  have hinit := state_initial_of (p := arrayProgram fnGetWord) (args := [addr, UInt64.ofNat idx])
    (mem := mem) (context := context) hf rfl
  have hbr : Cond.holds .ult .w64 (UInt64.ofNat idx) (UInt64.ofNat len) = true := by
    rw [cond_ult_w64, u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by omega)]
    exact decide_eq_true hidx
  have s00 := step_assign (p := arrayProgram fnGetWord) (fn := fnGetWord) (lbl := 0) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_8 (by simp only [e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]))
      (wordAt_load64 hsz))
  have s01 := step_br_true (p := arrayProgram fnGetWord) (fn := fnGetWord) (lbl := 0) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl rfl
    (by simp only [v, Arg.eval, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
    (by simp only [v, Arg.eval, e1, env_get_insert_self]) hbr rfl rfl rfl
  have s10 := step_assign (p := arrayProgram fnGetWord) (fn := fnGetWord) (lbl := 1) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl (by decide) rfl
    (rhs_load_eval
      (wordElemAddr_eval (by simp only [e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
        (by simp only [e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) (by omega))
      (wordAt_load64 helem))
  have sfin := final_ret_one (p := arrayProgram fnGetWord) (fn := fnGetWord) (lbl := 1)
    (mem := mem) (context := context) (env := e2) (res := elem) hf rfl rfl
    (by simp only [v, Arg.eval, e2, env_get_insert_self])
  apply (runs_eval hinit).eq
  exact .free s00 (.free s01 (.free s10 (.final sfin)))

theorem arrGet_limbs_live_eval {mem addr refs cls cap elems}
    (h : LiveArrayCell mem addr refs cls cap (.limbs elems))
    {idx : Nat} (hidx : idx < elems.length) (context : Word) (clock : Nat) :
    eval (arrayProgram fnGetWord) clock [addr, UInt64.ofNat idx] mem context =
      .ok ([elems[idx]], mem) := by
  have hbytes := (arrayBytes_eq_classBytes h.cls_lo h.cls_hi).1
  have hfit := h.fit; have hcap : cap ≤ wordCapOfClass cls := h.cap_fit; have hsz := h.size_le
  exact arrGet_word_core (len := elems.length) h.size_word (h.payload idx hidx) hidx
    (by unfold arrayPayloadOffset at hbytes; simp [ArrayVal.size] at hsz; omega) context clock

theorem arrGet_boxed_live_eval {mem addr refs cls cap elems}
    (h : LiveArrayCell mem addr refs cls cap (.boxed elems))
    {idx : Nat} (hidx : idx < elems.length) (context : Word) (clock : Nat) :
    eval (arrayProgram fnGetWord) clock [addr, UInt64.ofNat idx] mem context =
      .ok ([elems[idx]], mem) := by
  have hbytes := (arrayBytes_eq_classBytes h.cls_lo h.cls_hi).1
  have hfit := h.fit; have hcap : cap ≤ wordCapOfClass cls := h.cap_fit; have hsz := h.size_le
  exact arrGet_word_core (len := elems.length) h.size_word (h.payload idx hidx) hidx
    (by unfold arrayPayloadOffset at hbytes; simp [ArrayVal.size] at hsz; omega) context clock

theorem arrGet_limbs_static_eval {mem addr cap elems}
    (h : StaticArrayCell mem addr cap (.limbs elems))
    {idx : Nat} (hidx : idx < elems.length) (context : Word) (clock : Nat) :
    eval (arrayProgram fnGetWord) clock [addr, UInt64.ofNat idx] mem context =
      .ok ([elems[idx]], mem) := by
  have hfit := h.fit; have hsz := h.size_le
  simp only [arrayPayloadOffset, ArrayVal.size] at hfit hsz
  exact arrGet_word_core (len := elems.length) h.size_word (h.payload idx hidx) hidx (by omega) context clock

theorem arrGet_oob_trap {mem addr refs cls cap val}
    (h : LiveArrayCell mem addr refs cls cap val)
    {idx : Word} (hoob : val.size ≤ idx.toNat) (context : Word) (clock : Nat) :
    eval (arrayProgram fnGetWord) clock [addr, idx] mem context = .trap := by
  have hf := arrayProgram_func_getWord fnGetWord
  have hbytes := arrayBytes_eq_classBytes h.cls_lo h.cls_hi
  have hsz_lt : val.size < 2 ^ 63 := by
    have hfit := h.fit; have hcap := h.cap_fit; have hle := h.size_le
    cases val <;> simp only [arrayPayloadOffset] at hbytes <;> omega
  let e0 : Env := (({} : Env).insert 0 addr).insert 1 idx
  let e1 := e0.insert 2 (UInt64.ofNat val.size)
  have hinit := state_initial_of (p := arrayProgram fnGetWord) (args := [addr, idx])
    (mem := mem) (context := context) hf rfl
  have hbr : Cond.holds .ult .w64 idx (UInt64.ofNat val.size) = false := by
    rw [cond_ult_w64, u64_toNat_ofNat_lt (by omega)]
    exact decide_eq_false (by omega)
  have s00 := step_assign (p := arrayProgram fnGetWord) (fn := fnGetWord) (lbl := 0) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_8 (by simp only [e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]))
      (wordAt_load64 h.size_word))
  have s02 := step_br_false (p := arrayProgram fnGetWord) (fn := fnGetWord) (lbl := 0) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl rfl
    (by simp only [v, Arg.eval, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
    (by simp only [v, Arg.eval, e1, env_get_insert_self]) hbr rfl rfl rfl
  have sfin := final_trap (p := arrayProgram fnGetWord) (fn := fnGetWord)
    (lbl := 2) (rest := []) (mem := mem) (context := context) (env := e1) hf rfl rfl
  apply (runs_eval hinit).eq
  exact .free s00 (.free s02 (.final sfin))

private theorem byteArrGet_core {mem : Memory} {addr : Word} {b : UInt8} {len idx : Nat}
    (hsz : WordAt mem (addr + 8) (UInt64.ofNat len))
    (hbyte : ByteAt mem (addr + UInt64.ofNat (arrayPayloadOffset + idx)) b)
    (hidx : idx < len) (hlen : 24 + len < 2 ^ 64) (context : Word) (clock : Nat) :
    eval (arrayProgram fnByteGet) clock [addr, UInt64.ofNat idx] mem context =
      .ok ([b.toUInt64], mem) := by
  have hf := arrayProgram_func_byteGet fnByteGet
  let e0 : Env := (({} : Env).insert 0 addr).insert 1 (UInt64.ofNat idx)
  let e1 := e0.insert 2 (UInt64.ofNat len)
  let e2 := e1.insert 3 b.toUInt64
  have hinit := state_initial_of (p := arrayProgram fnByteGet) (args := [addr, UInt64.ofNat idx])
    (mem := mem) (context := context) hf rfl
  have hbr : Cond.holds .ult .w64 (UInt64.ofNat idx) (UInt64.ofNat len) = true := by
    rw [cond_ult_w64, u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by omega)]
    exact decide_eq_true hidx
  have s00 := step_assign (p := arrayProgram fnByteGet) (fn := fnByteGet) (lbl := 0) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_8 (by simp only [e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]))
      (wordAt_load64 hsz))
  have s01 := step_br_true (p := arrayProgram fnByteGet) (fn := fnByteGet) (lbl := 0) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl rfl
    (by simp only [v, Arg.eval, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
    (by simp only [v, Arg.eval, e1, env_get_insert_self]) hbr rfl rfl rfl
  have s10 := step_assign (p := arrayProgram fnByteGet) (fn := fnByteGet) (lbl := 1) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl (by decide) rfl
    (rhs_load_eval
      (byteElemAddr_eval (by simp only [e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
        (by simp only [e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) (by omega))
      hbyte.load8)
  have sfin := final_ret_one (p := arrayProgram fnByteGet) (fn := fnByteGet) (lbl := 1)
    (mem := mem) (context := context) (env := e2) (res := b.toUInt64) hf rfl rfl
    (by simp only [v, Arg.eval, e2, env_get_insert_self])
  apply (runs_eval hinit).eq
  exact .free s00 (.free s01 (.free s10 (.final sfin)))

theorem byteArrGet_live_eval {mem addr refs cls cap data}
    (h : LiveArrayCell mem addr refs cls cap (.bytes data))
    {idx : Nat} (hidx : idx < data.length) (context : Word) (clock : Nat) :
    eval (arrayProgram fnByteGet) clock [addr, UInt64.ofNat idx] mem context =
      .ok ([data[idx].toUInt64], mem) := by
  have hbytes := (arrayBytes_eq_classBytes h.cls_lo h.cls_hi).2
  have hfit := h.fit; have hcap : cap ≤ byteCapOfClass cls := h.cap_fit; have hsz := h.size_le
  exact byteArrGet_core (len := data.length) h.size_word (h.payload idx hidx) hidx
    (by unfold arrayPayloadOffset at hbytes; simp [ArrayVal.size] at hsz; omega) context clock

theorem byteArrGet_static_eval {mem addr cap data}
    (h : StaticArrayCell mem addr cap (.bytes data))
    {idx : Nat} (hidx : idx < data.length) (context : Word) (clock : Nat) :
    eval (arrayProgram fnByteGet) clock [addr, UInt64.ofNat idx] mem context =
      .ok ([data[idx].toUInt64], mem) := by
  have hfit := h.fit; have hsz := h.size_le
  simp only [arrayPayloadOffset, ArrayVal.size] at hfit hsz
  exact byteArrGet_core (len := data.length) h.size_word (h.payload idx hidx) hidx (by omega) context clock

/-! ## `arrPopLimbs` & `byteArrPop` (empty no-op + O(1) unique in-place) -/

theorem arrPopLimbs_empty_eval {mem addr refs cls cap}
    (h : LiveArrayCell mem addr refs cls cap (.limbs [])) (context : Word) (clock : Nat) :
    eval (arrayProgram fnPopLimbs) clock [addr] mem context = .ok ([addr], mem) := by
  have hf := arrayProgram_func_popLimbs fnPopLimbs
  have hsz_w : WordAt mem (addr + 8) (UInt64.ofNat 0) := h.size_word
  let e0 : Env := ({} : Env).insert 0 addr
  let e1 := e0.insert 1 (UInt64.ofNat 0)
  have hinit := state_initial_of (p := arrayProgram fnPopLimbs) (args := [addr])
    (mem := mem) (context := context) hf rfl
  have s00 := step_assign (p := arrayProgram fnPopLimbs) (fn := fnPopLimbs) (lbl := 0) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_8 (by simp only [e0, env_get_insert_self])) (wordAt_load64 hsz_w))
  have s01 := step_br_true (p := arrayProgram fnPopLimbs) (fn := fnPopLimbs) (lbl := 0) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl rfl
    (by simp only [v, Arg.eval, e1, env_get_insert_self]; rfl) rfl (by decide) rfl rfl rfl
  have sfin := final_ret_one (p := arrayProgram fnPopLimbs) (fn := fnPopLimbs) (lbl := 1)
    (mem := mem) (context := context) (env := e1) (res := addr) hf rfl rfl
    (by simp only [v, Arg.eval, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
  apply (runs_eval hinit).eq
  exact .free s00 (.free s01 (.final sfin))

/-- Unique (`refs = 1`) non-empty `LimbArray` pop executes O(1) in place with
zero allocation and preserves `LiveArrayCell` on `elems.dropLast`. -/
theorem arrPopLimbs_unique_eval {mem addr cls cap elems}
    (h : LiveArrayCell mem addr 1 cls cap (.limbs elems))
    (hne : 0 < elems.length) (context : Word) (clock : Nat) :
    ∃ mem',
      eval (arrayProgram fnPopLimbs) clock [addr] mem context = .ok ([addr], mem') ∧
      LiveArrayCell mem' addr 1 cls cap (.limbs elems.dropLast) := by
  have hf := arrayProgram_func_popLimbs fnPopLimbs
  have h24 := h.classBytes_ge_24
  have hbytes := (arrayBytes_eq_classBytes h.cls_lo h.cls_hi).1
  have hfit := h.fit; have hcap : cap ≤ wordCapOfClass cls := h.cap_fit; have hsz := h.size_le
  have hlen_lt : elems.length < 2 ^ 63 := by unfold arrayPayloadOffset at hbytes; simp [ArrayVal.size] at hsz; omega
  have hsz_w : WordAt mem (addr + 8) (UInt64.ofNat elems.length) := h.size_word
  have hcnt : loadWord mem .w32 .zero (addr + 4) = some (UInt64.ofNat 0) := h.count_load
  let mem' := mem.write .w64 (addr + 8) (UInt64.ofNat (elems.length - 1))
  have hwr : mem.write? .w64 (addr + 8) (UInt64.ofNat (elems.length - 1)) = .ok mem' :=
    live_write64_ok h (off := 8) (by omega) _
  refine ⟨mem', ?_, h.pop_inPlace hne⟩
  let e0 : Env := ({} : Env).insert 0 addr
  let e1 := e0.insert 1 (UInt64.ofNat elems.length)
  let e2 := e1.insert 2 (UInt64.ofNat (elems.length - 1))
  let e3 := e2.insert 3 (UInt64.ofNat 0)
  have hinit := state_initial_of (p := arrayProgram fnPopLimbs) (args := [addr])
    (mem := mem) (context := context) hf rfl
  have hne0 : Cond.holds .eq .w64 (UInt64.ofNat elems.length) (UInt64.ofNat 0) = false := by
    rw [cond_eq_w64]
    exact beq_false_of_ne (fun heq => by
      have := congrArg UInt64.toNat heq
      rw [u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by decide)] at this; omega)
  have s00 := step_assign (p := arrayProgram fnPopLimbs) (fn := fnPopLimbs) (lbl := 0) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_8 (by simp only [e0, env_get_insert_self])) (wordAt_load64 hsz_w))
  have s02 := step_br_false (p := arrayProgram fnPopLimbs) (fn := fnPopLimbs) (lbl := 0) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl rfl
    (by simp only [v, Arg.eval, e1, env_get_insert_self]) rfl hne0 rfl rfl rfl
  have s20 := step_assign (p := arrayProgram fnPopLimbs) (fn := fnPopLimbs) (lbl := 2) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl (by decide) rfl
    (rhs_bin_eval (by simp only [v, Arg.eval, e1, env_get_insert_self]) rfl
      (binOp_sub64 elems.length 1 hne (by omega)))
  have s21 := step_assign (p := arrayProgram fnPopLimbs) (fn := fnPopLimbs) (lbl := 2) (pos := 1) (rest := [])
    (mem := mem) (context := context) (env := e2) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_4 (by simp only [e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])) hcnt)
  have s23 := step_br_true (p := arrayProgram fnPopLimbs) (fn := fnPopLimbs) (lbl := 2) (rest := [])
    (mem := mem) (context := context) (env := e3) hf rfl rfl
    (by simp only [v, Arg.eval, e3, env_get_insert_self]; rfl) rfl (by decide) rfl rfl rfl
  have s30 := step_store (p := arrayProgram fnPopLimbs) (fn := fnPopLimbs) (lbl := 3) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e3) hf rfl (by decide) rfl
    (cellAddr_eval_8 (by simp only [e3, e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]))
    (by simp only [v, Arg.eval, e3, e2, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) hwr
  have sfin := final_ret_one (p := arrayProgram fnPopLimbs) (fn := fnPopLimbs) (lbl := 3)
    (mem := mem') (context := context) (env := e3) (res := addr) hf rfl rfl
    (by simp only [v, Arg.eval, e3, e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
  apply (runs_eval hinit).eq
  exact .free s00 (.free s02 (.free s20 (.free s21 (.free s23 (.free s30 (.final sfin))))))

/-- Unique (`refs = 1`) non-empty `ByteArray` pop executes O(1) in place and
preserves `LiveArrayCell` on `data.dropLast`. -/
theorem byteArrPop_unique_eval {mem addr cls cap data}
    (h : LiveArrayCell mem addr 1 cls cap (.bytes data))
    (hne : 0 < data.length) (context : Word) (clock : Nat) :
    ∃ mem',
      eval (arrayProgram fnBytePop) clock [addr] mem context = .ok ([addr], mem') ∧
      LiveArrayCell mem' addr 1 cls cap (.bytes data.dropLast) := by
  have hf := arrayProgram_func_bytePop fnBytePop
  have h24 := h.classBytes_ge_24
  have hbytes := (arrayBytes_eq_classBytes h.cls_lo h.cls_hi).2
  have hfit := h.fit; have hcap : cap ≤ byteCapOfClass cls := h.cap_fit; have hsz := h.size_le
  have hlen_lt : data.length < 2 ^ 63 := by unfold arrayPayloadOffset at hbytes; simp [ArrayVal.size] at hsz; omega
  have hsz_w : WordAt mem (addr + 8) (UInt64.ofNat data.length) := h.size_word
  have hcnt : loadWord mem .w32 .zero (addr + 4) = some (UInt64.ofNat 0) := h.count_load
  let mem' := mem.write .w64 (addr + 8) (UInt64.ofNat (data.length - 1))
  have hwr : mem.write? .w64 (addr + 8) (UInt64.ofNat (data.length - 1)) = .ok mem' :=
    live_write64_ok h (off := 8) (by omega) _
  refine ⟨mem', ?_, h.pop_inPlace hne⟩
  let e0 : Env := ({} : Env).insert 0 addr
  let e1 := e0.insert 1 (UInt64.ofNat data.length)
  let e2 := e1.insert 2 (UInt64.ofNat (data.length - 1))
  let e3 := e2.insert 3 (UInt64.ofNat 0)
  have hinit := state_initial_of (p := arrayProgram fnBytePop) (args := [addr])
    (mem := mem) (context := context) hf rfl
  have hne0 : Cond.holds .eq .w64 (UInt64.ofNat data.length) (UInt64.ofNat 0) = false := by
    rw [cond_eq_w64]
    exact beq_false_of_ne (fun heq => by
      have := congrArg UInt64.toNat heq
      rw [u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by decide)] at this; omega)
  have s00 := step_assign (p := arrayProgram fnBytePop) (fn := fnBytePop) (lbl := 0) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_8 (by simp only [e0, env_get_insert_self])) (wordAt_load64 hsz_w))
  have s02 := step_br_false (p := arrayProgram fnBytePop) (fn := fnBytePop) (lbl := 0) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl rfl
    (by simp only [v, Arg.eval, e1, env_get_insert_self]) rfl hne0 rfl rfl rfl
  have s20 := step_assign (p := arrayProgram fnBytePop) (fn := fnBytePop) (lbl := 2) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl (by decide) rfl
    (rhs_bin_eval (by simp only [v, Arg.eval, e1, env_get_insert_self]) rfl
      (binOp_sub64 data.length 1 hne (by omega)))
  have s21 := step_assign (p := arrayProgram fnBytePop) (fn := fnBytePop) (lbl := 2) (pos := 1) (rest := [])
    (mem := mem) (context := context) (env := e2) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_4 (by simp only [e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])) hcnt)
  have s23 := step_br_true (p := arrayProgram fnBytePop) (fn := fnBytePop) (lbl := 2) (rest := [])
    (mem := mem) (context := context) (env := e3) hf rfl rfl
    (by simp only [v, Arg.eval, e3, env_get_insert_self]; rfl) rfl (by decide) rfl rfl rfl
  have s30 := step_store (p := arrayProgram fnBytePop) (fn := fnBytePop) (lbl := 3) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e3) hf rfl (by decide) rfl
    (cellAddr_eval_8 (by simp only [e3, e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]))
    (by simp only [v, Arg.eval, e3, e2, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) hwr
  have sfin := final_ret_one (p := arrayProgram fnBytePop) (fn := fnBytePop) (lbl := 3)
    (mem := mem') (context := context) (env := e3) (res := addr) hf rfl rfl
    (by simp only [v, Arg.eval, e3, e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
  apply (runs_eval hinit).eq
  exact .free s00 (.free s02 (.free s20 (.free s21 (.free s23 (.free s30 (.final sfin))))))

end IxCC.Rt.Rc.Array
