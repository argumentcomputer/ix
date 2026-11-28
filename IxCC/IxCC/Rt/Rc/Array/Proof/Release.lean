import IxCC.Rt.Rc.Array.Proof.BasicOps
import IxCC.Rt.Rc.Proof.FreeList

/-! # Operational Correctness of Unified Iterative `arrDec`

Proves exact Lir operational correctness of `arrDec` across all paths:
* `arrDec_immediate_eval`: odd immediate word (`w &&& 1 = 1`) — zero memory accesses,
  returns `.ok ([], mem)`.
* `arrDec_static_eval`: any immortal `.rodata` `StaticArrayCell` (boxed, bytes,
  or limbs) — reads only the negative `rc = INT32_MIN` halfword, performs ZERO
  writes to read-only memory, returns `.ok ([], mem)`.
* `arrDec_shared_eval`: any shared `LiveArrayCell` (`1 < refs`) — decrements `rc`
  in place via `storeCount`, preserving `LiveArrayCell` at `refs - 1`.
* `arrDec_unboxed_free_eval`: any unique (`refs = 1`) `ByteArray` or `LimbArray`
  (`scan = 0`) — O(1) recycles onto `[ctx + cls*8]` and extends `FreeChain`.
* `arrDec_boxed_empty_free_eval`: any unique empty boxed `Array` — O(1) recycles
  onto `[ctx + cls*8]` and extends `FreeChain`.
* `arrDec_boxed_immediates_free_eval`: any unique non-empty boxed `Array` of
  immediates — proves the iterative O(1)-stack right-to-left pointer-reversal
  loop (`blocks 1, 2, 3, 5, 12, 13, 15, 6, 7, 16, 19, 18, 10`) terminates and
  recycles the shell onto `[ctx + cls*8]`. -/

set_option autoImplicit false

namespace IxCC.Rt.Rc.Array

open Lir
open IxCC.Rt.Proof (WordAt addr_toNat write?_ok wordAt_write64)
open IxCC.Rt.Rc (maxClass classBytes)
open IxCC.Rt.Rc.Procs (v i to cellAddr FreeChain freeHeadAddress storeCount countAddress
  recycleParent recycled_head)
open IxCC.X86 (Memory)

private theorem recycle_writes_ok {mem : Memory} {context addr oldHead : Word} {cls : Nat}
    (hhead_wr : ∀ j < 8, mem.writable (freeHeadAddress context (UInt64.ofNat cls) + UInt64.ofNat j) = true)
    (haddr_wr : ∀ j < 8, mem.writable (addr + UInt64.ofNat j) = true) :
    mem.write? .w64 addr oldHead = .ok (mem.write .w64 addr oldHead) ∧
    (mem.write .w64 addr oldHead).write? .w64 (freeHeadAddress context (UInt64.ofNat cls)) addr =
      .ok (recycleParent mem context (UInt64.ofNat cls) addr oldHead) := by
  refine ⟨write?_ok (fun j hj => haddr_wr j (by simpa [X86.Width.bytes] using hj)), ?_⟩
  have hwr2 := write?_ok (m := mem.write .w64 addr oldHead) (w := .w64)
    (a := freeHeadAddress context (UInt64.ofNat cls)) (v := addr)
    (fun j hj => by simpa [Memory.write] using hhead_wr j (by simpa [X86.Width.bytes] using hj))
  simpa [recycleParent] using hwr2

private theorem freeChain_write64_disjoint {mem : Memory} {wa val : Word} {chain : List Word}
    (hchain : FreeChain mem chain) (hwa : wa.toNat + 8 ≤ 2 ^ 64)
    (hfit : ∀ a ∈ chain, a.toNat + 8 ≤ 2 ^ 64)
    (hsep : ∀ a ∈ chain, a.toNat + 8 ≤ wa.toNat ∨ wa.toNat + 8 ≤ a.toNat) :
    FreeChain (mem.write .w64 wa val) chain := by
  induction chain with
  | nil => trivial
  | cons a tail ih =>
    obtain ⟨hw, ht⟩ := hchain
    exact ⟨wordAt_write64_disjoint hw hwa (hfit a (by simp)) (hsep a (by simp)),
      ih ht (fun b hb => hfit b (by simp [hb])) (fun b hb => hsep b (by simp [hb]))⟩

private theorem loadWord8_write64_disjoint {mem : Memory} {wa ra val res : Word}
    (hload : loadWord mem .w8 .zero ra = some res)
    (hwa : wa.toNat + 8 ≤ 2 ^ 64)
    (hsep : ra.toNat + 1 ≤ wa.toNat ∨ wa.toNat + 8 ≤ ra.toNat) :
    loadWord (mem.write .w64 wa val) .w8 .zero ra = some res := by
  have hne : ∀ k < 8, ra ≠ wa + UInt64.ofNat k := by
    intro k hk heq
    have hto := congrArg UInt64.toNat heq
    rw [addr_toNat (by omega)] at hto
    omega
  have hbyte : (mem.write .w64 wa val).bytes ra = mem.bytes ra :=
    Memory.writeLittle_bytes_outside mem wa val ra 8 hne
  have hmem : (mem.write .w64 wa val).read? .w8 ra = mem.read? .w8 ra := by
    have hread : (mem.write .w64 wa val).read .w8 ra = mem.read .w8 ra := by
      simp only [Memory.read, X86.Width.bytes, Memory.readLittle,
        show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero]
      rw [hbyte]
    have hrd : (mem.write .w64 wa val).readable = mem.readable := rfl
    simp only [Memory.read?, hrd, hread]
  simpa [loadWord, hmem] using hload

/-! ## 1. Immediate word (`w &&& 1 = 1`) -/

/-- Releasing an immediate word performs zero memory accesses and leaves memory untouched. -/
theorem arrDec_immediate_eval (mem : Memory) (context word : Word) (clock : Nat)
    (htag : word &&& 1 = 1) :
    eval (arrayProgram fnDec) clock [word] mem context = .ok ([], mem) := by
  have hf := arrayProgram_func_dec fnDec
  let e0 : Env := ({} : Env).insert 0 word
  let e1 := (e0.insert 1 word).insert 2 0
  let e6 := e1.insert 8 0
  have hinit := state_initial_of (p := arrayProgram fnDec) (args := [word])
    (mem := mem) (context := context) hf rfl
  have htnz : Cond.holds .tnz .w64 word (UInt64.ofNat 1) = true := by
    simp [Cond.holds, htag]
  have s01 := step_jump (p := arrayProgram fnDec) (fn := fnDec) (lbl := 0) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl rfl
    (evalArgs_pair (by simp only [v, Arg.eval, e0, env_get_insert_self]; rfl) rfl)
    rfl rfl
  have s16 := step_br_true (p := arrayProgram fnDec) (fn := fnDec) (lbl := 1) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl rfl
    (by simp only [v, Arg.eval, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) rfl htnz
    (evalArgs_singleton (by simp only [v, Arg.eval, e1, env_get_insert_self]; rfl))
    rfl rfl
  have s610 := step_br_true (p := arrayProgram fnDec) (fn := fnDec) (lbl := 6) (rest := [])
    (mem := mem) (context := context) (env := e6) hf rfl rfl
    (by simp only [v, Arg.eval, e6, env_get_insert_self]; rfl) rfl (by decide) rfl rfl rfl
  have sfin := final_ret_zero (p := arrayProgram fnDec) (fn := fnDec) (lbl := 10)
    (mem := mem) (context := context) (env := e6) hf rfl rfl
  apply (runs_eval hinit).eq
  exact .free s01 (.free s16 (.free s610 (.final sfin)))

/-! ## 2. Immortal static `.rodata` array cell -/

/-- Releasing ANY immortal `.rodata` `StaticArrayCell` (boxed, `ByteArray`, or
`LimbArray`) performs ZERO writes to read-only memory and returns `.ok ([], mem)`. -/
theorem arrDec_static_eval {mem addr cap val}
    (h : StaticArrayCell mem addr cap val) (context : Word) (clock : Nat) :
    eval (arrayProgram fnDec) clock [addr] mem context = .ok ([], mem) := by
  have hf := arrayProgram_func_dec fnDec
  let e0 : Env := ({} : Env).insert 0 addr
  let e1 := (e0.insert 1 addr).insert 2 0
  let e2 := e1.insert 3 (UInt64.ofNat Rt.immortalRc)
  let e6 := e2.insert 8 0
  have hinit := state_initial_of (p := arrayProgram fnDec) (args := [addr])
    (mem := mem) (context := context) hf rfl
  have s01 := step_jump (p := arrayProgram fnDec) (fn := fnDec) (lbl := 0) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl rfl
    (evalArgs_pair (by simp only [v, Arg.eval, e0, env_get_insert_self]; rfl) rfl)
    rfl rfl
  have s12 := step_br_false (p := arrayProgram fnDec) (fn := fnDec) (lbl := 1) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl rfl
    (by simp only [v, Arg.eval, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) rfl h.pointer_branch rfl rfl rfl
  have s20 := step_assign (p := arrayProgram fnDec) (fn := fnDec) (lbl := 2) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_4 (by simp only [e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])) h.count_load)
  have s26 := step_br_true (p := arrayProgram fnDec) (fn := fnDec) (lbl := 2) (rest := [])
    (mem := mem) (context := context) (env := e2) hf rfl rfl
    (by simp only [v, Arg.eval, e2, env_get_insert_self]) rfl StaticArrayCell.rc_slt_zero
    (evalArgs_singleton (by simp only [v, Arg.eval, e2, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]; rfl))
    rfl rfl
  have s610 := step_br_true (p := arrayProgram fnDec) (fn := fnDec) (lbl := 6) (rest := [])
    (mem := mem) (context := context) (env := e6) hf rfl rfl
    (by simp only [v, Arg.eval, e6, env_get_insert_self]; rfl) rfl (by decide) rfl rfl rfl
  have sfin := final_ret_zero (p := arrayProgram fnDec) (fn := fnDec) (lbl := 10)
    (mem := mem) (context := context) (env := e6) hf rfl rfl
  apply (runs_eval hinit).eq
  exact .free s01 (.free s12 (.free s20 (.free s26 (.free s610 (.final sfin)))))

/-! ## 3. Shared dynamic array cell (`1 < refs`) -/

/-- Releasing a shared (`1 < refs`) live array cell decrements its RC count word
in place via `storeCount` and preserves `LiveArrayCell` at `refs - 1`. -/
theorem arrDec_shared_eval {mem addr refs cls cap val}
    (h : LiveArrayCell mem addr refs cls cap val) (hshared : 1 < refs)
    (context : Word) (clock : Nat) :
    let mem' := storeCount mem addr (UInt64.ofNat (refs - 2))
    eval (arrayProgram fnDec) clock [addr] mem context = .ok ([], mem') ∧
      LiveArrayCell mem' addr (refs - 1) cls cap val := by
  intro mem'
  have hf := arrayProgram_func_dec fnDec
  have h24 := h.classBytes_ge_24
  have hfit := h.fit
  have hmax := h.refs_le
  unfold IxCC.Rt.Rc.maxCount at hmax
  refine ⟨?_, h.dec_shared hshared⟩
  have hwr : mem.write? .w32 (addr + 4) (UInt64.ofNat (refs - 2)) = .ok mem' := by
    apply write?_ok
    intro k hk
    have hk4 : k < 4 := by simpa [X86.Width.bytes] using hk
    have h4 : (addr + 4).toNat = addr.toNat + 4 := countAddress (by omega)
    have hka : (addr + 4) + UInt64.ofNat k = addr + UInt64.ofNat (4 + k) := by
      apply UInt64.toNat_inj.mp
      rw [addr_toNat (by rw [h4]; omega), h4, addr_toNat (by omega)]
      omega
    rw [hka]
    exact (h.access (4 + k) (by omega)).2
  have hrc_ne0 : Cond.holds .eq .w32 (UInt64.ofNat (refs - 1)) (UInt64.ofNat 0) = false := by
    have htr : X86.Width.truncate .w32 (UInt64.ofNat (refs - 1)) = UInt64.ofNat (refs - 1) := by
      apply UInt64.toNat_inj.mp
      rw [X86.Width.truncate, X86.Width.mask, UInt64.toNat_and, u64_toNat_ofNat_lt (by omega),
        show (UInt64.toNat 0xffffffff) = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_eq_of_lt (by omega)
    have htr0 : X86.Width.truncate .w32 (UInt64.ofNat 0) = 0 := by decide
    simp only [Cond.holds, htr, htr0]
    exact beq_false_of_ne (fun heq => by
      have := congrArg UInt64.toNat heq
      rw [u64_toNat_ofNat_lt (by omega)] at this; simp at this; omega)
  have hsub32 : BinOp.eval .sub .w32 (UInt64.ofNat (refs - 1)) (UInt64.ofNat 1) =
      some (UInt64.ofNat (refs - 2)) := by
    simp only [BinOp.eval]
    congr 1
    rw [u64_sub_ofNat (by omega) (by omega)]
    have hsub : refs - 1 - 1 = refs - 2 := by omega
    rw [hsub]
    apply UInt64.toNat_inj.mp
    rw [X86.Width.truncate, X86.Width.mask, UInt64.toNat_and, u64_toNat_ofNat_lt (by omega),
      show (UInt64.toNat 0xffffffff) = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_of_lt (by omega)
  let e0 : Env := ({} : Env).insert 0 addr
  let e1 := (e0.insert 1 addr).insert 2 0
  let e2 := e1.insert 3 (UInt64.ofNat (refs - 1))
  let e4 := e2.insert 4 (UInt64.ofNat (refs - 2))
  let e6 := e4.insert 8 0
  have hinit := state_initial_of (p := arrayProgram fnDec) (args := [addr])
    (mem := mem) (context := context) hf rfl
  have s01 := step_jump (p := arrayProgram fnDec) (fn := fnDec) (lbl := 0) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl rfl
    (evalArgs_pair (by simp only [v, Arg.eval, e0, env_get_insert_self]; rfl) rfl)
    rfl rfl
  have s12 := step_br_false (p := arrayProgram fnDec) (fn := fnDec) (lbl := 1) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl rfl
    (by simp only [v, Arg.eval, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) rfl h.pointer_branch rfl rfl rfl
  have s20 := step_assign (p := arrayProgram fnDec) (fn := fnDec) (lbl := 2) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_4 (by simp only [e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])) h.count_load)
  have s23 := step_br_false (p := arrayProgram fnDec) (fn := fnDec) (lbl := 2) (rest := [])
    (mem := mem) (context := context) (env := e2) hf rfl rfl
    (by simp only [v, Arg.eval, e2, env_get_insert_self]) rfl h.rc_not_slt_zero rfl rfl rfl
  have s34 := step_br_false (p := arrayProgram fnDec) (fn := fnDec) (lbl := 3) (rest := [])
    (mem := mem) (context := context) (env := e2) hf rfl rfl
    (by simp only [v, Arg.eval, e2, env_get_insert_self]) rfl hrc_ne0 rfl rfl rfl
  have s40 := step_assign (p := arrayProgram fnDec) (fn := fnDec) (lbl := 4) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e2) hf rfl (by decide) rfl
    (rhs_bin_eval (by simp only [v, Arg.eval, e2, env_get_insert_self]) rfl hsub32)
  have s41 := step_store (p := arrayProgram fnDec) (fn := fnDec) (lbl := 4) (pos := 1) (rest := [])
    (mem := mem) (context := context) (env := e4) hf rfl (by decide) rfl
    (cellAddr_eval_4 (by simp only [e4, e2, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]))
    (by simp only [v, Arg.eval, e4, env_get_insert_self]) hwr
  have s46 := step_jump (p := arrayProgram fnDec) (fn := fnDec) (lbl := 4) (rest := [])
    (mem := mem') (context := context) (env := e4) hf rfl rfl
    (evalArgs_singleton (by simp only [v, Arg.eval, e4, e2, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]; rfl))
    rfl rfl
  have s610 := step_br_true (p := arrayProgram fnDec) (fn := fnDec) (lbl := 6) (rest := [])
    (mem := mem') (context := context) (env := e6) hf rfl rfl
    (by simp only [v, Arg.eval, e6, env_get_insert_self]; rfl) rfl (by decide) rfl rfl rfl
  have sfin := final_ret_zero (p := arrayProgram fnDec) (fn := fnDec)
    (lbl := 10) (mem := mem') (context := context) (env := e6) hf rfl rfl
  apply (runs_eval hinit).eq
  exact .free s01 (.free s12 (.free s20 (.free s23 (.free s34 (.free s40 (.free s41
    (.free s46 (.free s610 (.final sfin)))))))))

/-! ## 4. O(1) recycling of unique `ByteArray`, `LimbArray`, and empty boxed `Array` -/

private theorem arrDec_block11_free {mem : Memory} {context addr : Word} {cls : Nat} {chain : List Word}
    {e : Env} (he1 : e[1]? = some addr) (he2 : e[2]? = some 0)
    (hcls_load : loadWord mem .w8 .zero (addr + 1) = some (UInt64.ofNat cls))
    (hhead : WordAt mem (freeHeadAddress context (UInt64.ofNat cls)) (chain.headD 0))
    (hchain : FreeChain mem chain)
    (haddr_rd : ∀ j < 8, mem.readable (addr + UInt64.ofNat j) = true)
    (haddr_wr : ∀ j < 8, mem.writable (addr + UInt64.ofNat j) = true)
    (hhead_wr : ∀ j < 8, mem.writable (freeHeadAddress context (UInt64.ofNat cls) + UInt64.ofNat j) = true)
    (ha_fit : addr.toNat + 8 ≤ 2 ^ 64)
    (hh_fit : (freeHeadAddress context (UInt64.ofNat cls)).toNat + 8 ≤ 2 ^ 64)
    (hac : addr.toNat + 8 ≤ (freeHeadAddress context (UInt64.ofNat cls)).toNat ∨
      (freeHeadAddress context (UInt64.ofNat cls)).toNat + 8 ≤ addr.toNat)
    (hfit_chain : ∀ a ∈ chain, a.toNat + 8 ≤ 2 ^ 64)
    (hsep_chain : ∀ a ∈ chain,
      (a.toNat + 8 ≤ addr.toNat ∨ addr.toNat + 8 ≤ a.toNat) ∧
      (a.toNat + 8 ≤ (freeHeadAddress context (UInt64.ofNat cls)).toNat ∨
        (freeHeadAddress context (UInt64.ofNat cls)).toNat + 8 ≤ a.toNat))
    (clock : Nat) :
    let mem' := recycleParent mem context (UInt64.ofNat cls) addr (chain.headD 0)
    Sem.Reaches (semStep (arrayProgram fnDec))
      (State.mk mem context [{ fn := fnDec, label := 11, pos := 0, env := e }])
      (clock + 1) (.ok ([], mem')) ∧
    WordAt mem' (freeHeadAddress context (UInt64.ofNat cls)) addr ∧
    FreeChain mem' (addr :: chain) := by
  intro mem'
  have hf := arrayProgram_func_dec fnDec
  obtain ⟨hwr1, hwr2⟩ := recycle_writes_ok (oldHead := chain.headD 0) hhead_wr haddr_wr
  let m1 := mem.write .w64 addr (chain.headD 0)
  let e17 := e.insert 17 (UInt64.ofNat cls)
  let e18 := e17.insert 18 (chain.headD 0)
  let e6 := e18.insert 8 0
  refine ⟨?_, recycled_head hhead.readable,
    hchain.recycle_push haddr_rd ha_fit hh_fit hac hfit_chain hsep_chain⟩
  have s110 := step_assign (p := arrayProgram fnDec) (fn := fnDec) (lbl := 11) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_1 he1) hcls_load)
  have s111 := step_assign (p := arrayProgram fnDec) (fn := fnDec) (lbl := 11) (pos := 1) (rest := [])
    (mem := mem) (context := context) (env := e17) hf rfl (by decide) rfl
    (rhs_load_eval (ctxHeadAddr_eval (by simp only [e17, env_get_insert_self])) (wordAt_load64 hhead))
  have s112 := step_store (p := arrayProgram fnDec) (fn := fnDec) (lbl := 11) (pos := 2) (rest := [])
    (mem := mem) (context := context) (env := e18) hf rfl (by decide) rfl
    (cellAddr0_eval (by simp only [e18, e17, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, he1]))
    (by simp only [v, Arg.eval, e18, env_get_insert_self]) hwr1
  have s113 := step_store (p := arrayProgram fnDec) (fn := fnDec) (lbl := 11) (pos := 3) (rest := [])
    (mem := m1) (context := context) (env := e18) hf rfl (by decide) rfl
    (ctxHeadAddr_eval (by simp only [e18, e17, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]))
    (by simp only [v, Arg.eval, e18, e17, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, he1]) hwr2
  have s116 := step_jump (p := arrayProgram fnDec) (fn := fnDec) (lbl := 11) (rest := [])
    (mem := mem') (context := context) (env := e18) hf rfl rfl
    (evalArgs_singleton (by simp only [v, Arg.eval, e18, e17, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, he2]; rfl))
    rfl rfl
  have s610 := step_br_true (p := arrayProgram fnDec) (fn := fnDec) (lbl := 6) (rest := [])
    (mem := mem') (context := context) (env := e6) hf rfl rfl
    (by simp only [v, Arg.eval, e6, env_get_insert_self]; rfl) rfl (by decide) rfl rfl rfl
  have sfin := final_ret_zero (p := arrayProgram fnDec) (fn := fnDec)
    (lbl := 10) (mem := mem') (context := context) (env := e6) hf rfl rfl
  exact .free s110 (.free s111 (.free s112 (.free s113
    (.charge s116 (.free s610 (.final sfin))))))

/-- Unique (`refs = 1`) unboxed `ByteArray` or `LimbArray` (`val.kind.scan = 0`)
is recycled in O(1) onto `[ctx + cls*8]` with zero child scanning, extending
`FreeChain` to `addr :: chain`. -/
theorem arrDec_unboxed_free_eval {mem : Memory} {context addr : Word} {cls cap : Nat} {val : ArrayVal}
    {chain : List Word}
    (h : LiveArrayCell mem addr 1 cls cap val)
    (hunboxed : val.kind.scan = 0)
    (hhead : WordAt mem (freeHeadAddress context (UInt64.ofNat cls)) (chain.headD 0))
    (hchain : FreeChain mem chain)
    (hhead_wr : ∀ j < 8, mem.writable (freeHeadAddress context (UInt64.ofNat cls) + UInt64.ofNat j) = true)
    (hh_fit : (freeHeadAddress context (UInt64.ofNat cls)).toNat + 8 ≤ 2 ^ 64)
    (hac : addr.toNat + 8 ≤ (freeHeadAddress context (UInt64.ofNat cls)).toNat ∨
      (freeHeadAddress context (UInt64.ofNat cls)).toNat + 8 ≤ addr.toNat)
    (hfit_chain : ∀ a ∈ chain, a.toNat + 8 ≤ 2 ^ 64)
    (hsep_chain : ∀ a ∈ chain,
      (a.toNat + 8 ≤ addr.toNat ∨ addr.toNat + 8 ≤ a.toNat) ∧
      (a.toNat + 8 ≤ (freeHeadAddress context (UInt64.ofNat cls)).toNat ∨
        (freeHeadAddress context (UInt64.ofNat cls)).toNat + 8 ≤ a.toNat))
    (clock : Nat) :
    let mem' := recycleParent mem context (UInt64.ofNat cls) addr (chain.headD 0)
    eval (arrayProgram fnDec) (clock + 1) [addr] mem context = .ok ([], mem') ∧
      WordAt mem' (freeHeadAddress context (UInt64.ofNat cls)) addr ∧
      FreeChain mem' (addr :: chain) := by
  intro mem'
  have hf := arrayProgram_func_dec fnDec
  have h24 := h.classBytes_ge_24
  have hfit := h.fit
  have hcnt : loadWord mem .w32 .zero (addr + 4) = some (UInt64.ofNat 0) := h.count_load
  have hsc : loadWord mem .w8 .zero addr = some (UInt64.ofNat 0) := by
    have := h.scan_load; rwa [hunboxed] at this
  let e0 : Env := ({} : Env).insert 0 addr
  let e1 := (e0.insert 1 addr).insert 2 0
  let e2 := e1.insert 3 (UInt64.ofNat 0)
  let e5 := e2.insert 5 (UInt64.ofNat 0)
  have hinit := state_initial_of (p := arrayProgram fnDec) (args := [addr])
    (mem := mem) (context := context) hf rfl
  obtain ⟨hreach11, hhead', hchain'⟩ :=
    arrDec_block11_free (e := e5)
      (by simp only [e5, e2, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
      (by simp only [e5, e2, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
      h.class_load hhead hchain
      (fun j hj => (h.access j (by omega)).1) (fun j hj => (h.access j (by omega)).2)
      hhead_wr (by omega) hh_fit hac hfit_chain hsep_chain clock
  refine ⟨?_, hhead', hchain'⟩
  have s01 := step_jump (p := arrayProgram fnDec) (fn := fnDec) (lbl := 0) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl rfl
    (evalArgs_pair (by simp only [v, Arg.eval, e0, env_get_insert_self]; rfl) rfl)
    rfl rfl
  have s12 := step_br_false (p := arrayProgram fnDec) (fn := fnDec) (lbl := 1) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl rfl
    (by simp only [v, Arg.eval, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) rfl h.pointer_branch rfl rfl rfl
  have s20 := step_assign (p := arrayProgram fnDec) (fn := fnDec) (lbl := 2) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_4 (by simp only [e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])) hcnt)
  have s23 := step_br_false (p := arrayProgram fnDec) (fn := fnDec) (lbl := 2) (rest := [])
    (mem := mem) (context := context) (env := e2) hf rfl rfl
    (by simp only [v, Arg.eval, e2, env_get_insert_self]; rfl) rfl (by decide) rfl rfl rfl
  have s35 := step_br_true (p := arrayProgram fnDec) (fn := fnDec) (lbl := 3) (rest := [])
    (mem := mem) (context := context) (env := e2) hf rfl rfl
    (by simp only [v, Arg.eval, e2, env_get_insert_self]; rfl) rfl (by decide) rfl rfl rfl
  have s50 := step_assign (p := arrayProgram fnDec) (fn := fnDec) (lbl := 5) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e2) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr0_eval (by simp only [e2, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])) hsc)
  have s511 := step_br_true (p := arrayProgram fnDec) (fn := fnDec) (lbl := 5) (rest := [])
    (mem := mem) (context := context) (env := e5) hf rfl rfl
    (by simp only [v, Arg.eval, e5, env_get_insert_self]; rfl) rfl (by decide) rfl rfl rfl
  apply (runs_eval hinit).eq
  exact .free s01 (.free s12 (.free s20 (.free s23 (.free s35 (.free s50 (.free s511 hreach11))))))

/-- Unique (`refs = 1`) empty boxed `Array` (`size = 0`) is recycled in O(1) onto
`[ctx + cls*8]` and extends `FreeChain` to `addr :: chain`. -/
theorem arrDec_boxed_empty_free_eval {mem : Memory} {context addr : Word} {cls cap : Nat}
    {chain : List Word}
    (h : LiveArrayCell mem addr 1 cls cap (.boxed []))
    (hhead : WordAt mem (freeHeadAddress context (UInt64.ofNat cls)) (chain.headD 0))
    (hchain : FreeChain mem chain)
    (hhead_wr : ∀ j < 8, mem.writable (freeHeadAddress context (UInt64.ofNat cls) + UInt64.ofNat j) = true)
    (hh_fit : (freeHeadAddress context (UInt64.ofNat cls)).toNat + 8 ≤ 2 ^ 64)
    (hac : addr.toNat + 8 ≤ (freeHeadAddress context (UInt64.ofNat cls)).toNat ∨
      (freeHeadAddress context (UInt64.ofNat cls)).toNat + 8 ≤ addr.toNat)
    (hfit_chain : ∀ a ∈ chain, a.toNat + 8 ≤ 2 ^ 64)
    (hsep_chain : ∀ a ∈ chain,
      (a.toNat + 8 ≤ addr.toNat ∨ addr.toNat + 8 ≤ a.toNat) ∧
      (a.toNat + 8 ≤ (freeHeadAddress context (UInt64.ofNat cls)).toNat ∨
        (freeHeadAddress context (UInt64.ofNat cls)).toNat + 8 ≤ a.toNat))
    (clock : Nat) :
    let mem' := recycleParent mem context (UInt64.ofNat cls) addr (chain.headD 0)
    eval (arrayProgram fnDec) (clock + 2) [addr] mem context = .ok ([], mem') ∧
      WordAt mem' (freeHeadAddress context (UInt64.ofNat cls)) addr ∧
      FreeChain mem' (addr :: chain) := by
  intro mem'
  have hf := arrayProgram_func_dec fnDec
  have h24 := h.classBytes_ge_24
  have hfit := h.fit
  have hcnt : loadWord mem .w32 .zero (addr + 4) = some (UInt64.ofNat 0) := h.count_load
  have hsc : loadWord mem .w8 .zero addr = some (UInt64.ofNat 0xFF) := h.scan_load
  have hsz_w : WordAt mem (addr + 8) (UInt64.ofNat 0) := h.size_word
  let e0 : Env := ({} : Env).insert 0 addr
  let e1 := (e0.insert 1 addr).insert 2 0
  let e2 := e1.insert 3 (UInt64.ofNat 0)
  let e5 := e2.insert 5 (UInt64.ofNat 0xFF)
  let e13 := e5.insert 19 (UInt64.ofNat 0)
  have hinit := state_initial_of (p := arrayProgram fnDec) (args := [addr])
    (mem := mem) (context := context) hf rfl
  obtain ⟨hreach11, hhead', hchain'⟩ :=
    arrDec_block11_free (e := e13)
      (by simp only [e13, e5, e2, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
      (by simp only [e13, e5, e2, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
      h.class_load hhead hchain
      (fun j hj => (h.access j (by omega)).1) (fun j hj => (h.access j (by omega)).2)
      hhead_wr (by omega) hh_fit hac hfit_chain hsep_chain clock
  refine ⟨?_, hhead', hchain'⟩
  have s01 := step_jump (p := arrayProgram fnDec) (fn := fnDec) (lbl := 0) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl rfl
    (evalArgs_pair (by simp only [v, Arg.eval, e0, env_get_insert_self]; rfl) rfl)
    rfl rfl
  have s12 := step_br_false (p := arrayProgram fnDec) (fn := fnDec) (lbl := 1) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl rfl
    (by simp only [v, Arg.eval, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) rfl h.pointer_branch rfl rfl rfl
  have s20 := step_assign (p := arrayProgram fnDec) (fn := fnDec) (lbl := 2) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_4 (by simp only [e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])) hcnt)
  have s23 := step_br_false (p := arrayProgram fnDec) (fn := fnDec) (lbl := 2) (rest := [])
    (mem := mem) (context := context) (env := e2) hf rfl rfl
    (by simp only [v, Arg.eval, e2, env_get_insert_self]; rfl) rfl (by decide) rfl rfl rfl
  have s35 := step_br_true (p := arrayProgram fnDec) (fn := fnDec) (lbl := 3) (rest := [])
    (mem := mem) (context := context) (env := e2) hf rfl rfl
    (by simp only [v, Arg.eval, e2, env_get_insert_self]; rfl) rfl (by decide) rfl rfl rfl
  have s50 := step_assign (p := arrayProgram fnDec) (fn := fnDec) (lbl := 5) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e2) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr0_eval (by simp only [e2, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])) hsc)
  have s512 := step_br_false (p := arrayProgram fnDec) (fn := fnDec) (lbl := 5) (rest := [])
    (mem := mem) (context := context) (env := e5) hf rfl rfl
    (by simp only [v, Arg.eval, e5, env_get_insert_self]; rfl) rfl (by decide) rfl rfl rfl
  have s1213 := step_br_true (p := arrayProgram fnDec) (fn := fnDec) (lbl := 12) (rest := [])
    (mem := mem) (context := context) (env := e5) hf rfl rfl
    (by simp only [v, Arg.eval, e5, env_get_insert_self]; rfl) rfl (by decide) rfl rfl rfl
  have s130 := step_assign (p := arrayProgram fnDec) (fn := fnDec) (lbl := 13) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e5) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_8 (by simp only [e5, e2, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]))
      (wordAt_load64 hsz_w))
  have s1311 := step_br_true (p := arrayProgram fnDec) (fn := fnDec) (lbl := 13) (rest := [])
    (mem := mem) (context := context) (env := e13) hf rfl rfl
    (by simp only [v, Arg.eval, e13, env_get_insert_self]; rfl) rfl (by decide) rfl rfl rfl
  apply (runs_eval hinit).eq
  exact .free s01 (.free s12 (.free s20 (.free s23 (.free s35 (.free s50
    (.free s512 (.free s1213 (.free s130 (.charge s1311 hreach11)))))))))

/-! ## 5. Iterative pointer-reversal loop for non-empty boxed `Array` -/

/-- Inductive invariant for the iterative right-to-left release loop of a unique
boxed `Array` holding immediate elements (`rem` elements still to visit, parent
link `0` stored at `addr + 16`). -/
private theorem arrDec_boxed_immediates_loop (rem : Nat) :
    ∀ {mem : Memory} {context addr : Word} {cls : Nat} {elems : List Word} {chain : List Word} {e : Env},
    (hrem : rem ≤ elems.length) →
    addr ≠ 0 →
    e[8]? = some addr →
    minArrayClass ≤ cls →
    cls ≤ maxClass →
    addr.toNat + classBytes cls < 2 ^ 63 →
    arrayPayloadOffset + 8 * elems.length ≤ classBytes cls →
    (∀ j < classBytes cls, mem.readable (addr + UInt64.ofNat j) = true ∧
      mem.writable (addr + UInt64.ofNat j) = true) →
    loadWord mem .w8 .zero addr = some (UInt64.ofNat 0xFF) →
    loadWord mem .w8 .zero (addr + 1) = some (UInt64.ofNat cls) →
    WordAt mem (addr + 8) (UInt64.ofNat rem) →
    WordAt mem (addr + 16) 0 →
    (∀ (j : Nat) (hj : j < rem),
      WordAt mem (addr + UInt64.ofNat (arrayPayloadOffset + 8 * j)) (elems[j]'(by omega))) →
    (∀ (j : Nat) (hj : j < elems.length), elems[j] &&& 1 = 1) →
    WordAt mem (freeHeadAddress context (UInt64.ofNat cls)) (chain.headD 0) →
    FreeChain mem chain →
    (∀ j < 8, mem.writable (freeHeadAddress context (UInt64.ofNat cls) + UInt64.ofNat j) = true) →
    (freeHeadAddress context (UInt64.ofNat cls)).toNat + 8 ≤ 2 ^ 64 →
    (addr.toNat + classBytes cls ≤ (freeHeadAddress context (UInt64.ofNat cls)).toNat ∨
      (freeHeadAddress context (UInt64.ofNat cls)).toNat + 8 ≤ addr.toNat) →
    (∀ a ∈ chain, a.toNat + 8 ≤ 2 ^ 64) →
    (∀ a ∈ chain,
      (a.toNat + 8 ≤ addr.toNat ∨ addr.toNat + classBytes cls ≤ a.toNat) ∧
      (a.toNat + 8 ≤ (freeHeadAddress context (UInt64.ofNat cls)).toNat ∨
        (freeHeadAddress context (UInt64.ofNat cls)).toNat + 8 ≤ a.toNat)) →
    ∀ clock,
      ∃ mem',
        Sem.Reaches (semStep (arrayProgram fnDec))
          (State.mk mem context [{ fn := fnDec, label := 6, pos := 0, env := e }])
          (clock + rem + 1) (.ok ([], mem')) ∧
        WordAt mem' (freeHeadAddress context (UInt64.ofNat cls)) addr ∧
        FreeChain mem' (addr :: chain) := by
  have hf := arrayProgram_func_dec fnDec
  induction rem with
  | zero =>
    intro mem context addr cls elems chain e _ hnz he8 hcls_lo hcls_hi hfit hlen_fit hacc
      hscan hcls_load hrem_w hpred_w _ _ hhead hchain hhead_wr hh_fit hac hfit_ch hsep_ch clock
    have h24 : 24 ≤ classBytes cls := by
      have := classWords_ge_three hcls_lo hcls_hi; unfold classBytes; omega
    have hne0 : Cond.holds .eq .w64 addr (UInt64.ofNat 0) = false := by
      rw [cond_eq_w64]; exact beq_false_of_ne hnz
    obtain ⟨hwr1, hwr2⟩ := recycle_writes_ok (oldHead := chain.headD 0) hhead_wr (fun j hj => (hacc j (by omega)).2)
    let m1 := mem.write .w64 addr (chain.headD 0)
    let mem' := recycleParent mem context (UInt64.ofNat cls) addr (chain.headD 0)
    let e10 := e.insert 10 (UInt64.ofNat 0xFF)
    let e22 := e10.insert 22 (UInt64.ofNat 0)
    let e23 := e22.insert 23 (UInt64.ofNat cls)
    let e24 := e23.insert 24 0
    let e25 := e24.insert 25 (chain.headD 0)
    let e6' := e25.insert 8 0
    have s67 := step_br_false (p := arrayProgram fnDec) (fn := fnDec) (lbl := 6) (rest := [])
      (mem := mem) (context := context) (env := e) hf rfl rfl (by simp only [v, Arg.eval, he8]) rfl hne0 rfl rfl rfl
    have s70 := step_assign (p := arrayProgram fnDec) (fn := fnDec) (lbl := 7) (pos := 0) (rest := [])
      (mem := mem) (context := context) (env := e) hf rfl (by decide) rfl
      (rhs_load_eval (cellAddr0_eval he8) hscan)
    have s716 := step_br_true (p := arrayProgram fnDec) (fn := fnDec) (lbl := 7) (rest := [])
      (mem := mem) (context := context) (env := e10) hf rfl rfl
      (by simp only [v, Arg.eval, e10, env_get_insert_self]; rfl) rfl (by decide) rfl rfl rfl
    have s160 := step_assign (p := arrayProgram fnDec) (fn := fnDec) (lbl := 16) (pos := 0) (rest := [])
      (mem := mem) (context := context) (env := e10) hf rfl (by decide) rfl
      (rhs_load_eval (cellAddr_eval_8 (by simp only [e10, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, he8]))
        (wordAt_load64 hrem_w))
    have s1618 := step_br_true (p := arrayProgram fnDec) (fn := fnDec) (lbl := 16) (rest := [])
      (mem := mem) (context := context) (env := e22) hf rfl rfl
      (by simp only [v, Arg.eval, e22, env_get_insert_self]; rfl) rfl (by decide) rfl rfl rfl
    have s180 := step_assign (p := arrayProgram fnDec) (fn := fnDec) (lbl := 18) (pos := 0) (rest := [])
      (mem := mem) (context := context) (env := e22) hf rfl (by decide) rfl
      (rhs_load_eval (cellAddr_eval_1 (by simp only [e22, e10, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, he8])) hcls_load)
    have s181 := step_assign (p := arrayProgram fnDec) (fn := fnDec) (lbl := 18) (pos := 1) (rest := [])
      (mem := mem) (context := context) (env := e23) hf rfl (by decide) rfl
      (rhs_load_eval (cellAddr_eval_16 (by simp only [e23, e22, e10, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, he8]))
        (wordAt_load64 hpred_w))
    have s182 := step_assign (p := arrayProgram fnDec) (fn := fnDec) (lbl := 18) (pos := 2) (rest := [])
      (mem := mem) (context := context) (env := e24) hf rfl (by decide) rfl
      (rhs_load_eval (ctxHeadAddr_eval (by simp only [e24, e23, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]))
        (wordAt_load64 hhead))
    have s183 := step_store (p := arrayProgram fnDec) (fn := fnDec) (lbl := 18) (pos := 3) (rest := [])
      (mem := mem) (context := context) (env := e25) hf rfl (by decide) rfl
      (cellAddr0_eval (by simp only [e25, e24, e23, e22, e10, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, he8]))
      (by simp only [v, Arg.eval, e25, env_get_insert_self]) hwr1
    have s184 := step_store (p := arrayProgram fnDec) (fn := fnDec) (lbl := 18) (pos := 4) (rest := [])
      (mem := m1) (context := context) (env := e25) hf rfl (by decide) rfl
      (ctxHeadAddr_eval (by simp only [e25, e24, e23, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]))
      (by simp only [v, Arg.eval, e25, e24, e23, e22, e10, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, he8]) hwr2
    have s186 := step_jump (p := arrayProgram fnDec) (fn := fnDec) (lbl := 18) (rest := [])
      (mem := mem') (context := context) (env := e25) hf rfl rfl
      (evalArgs_singleton (by simp only [v, Arg.eval, e25, e24, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]; rfl))
      rfl rfl
    have s610 := step_br_true (p := arrayProgram fnDec) (fn := fnDec) (lbl := 6) (rest := [])
      (mem := mem') (context := context) (env := e6') hf rfl rfl
      (by simp only [v, Arg.eval, e6', env_get_insert_self]; rfl) rfl (by decide) rfl rfl rfl
    have sfin := final_ret_zero (p := arrayProgram fnDec) (fn := fnDec)
      (lbl := 10) (mem := mem') (context := context) (env := e6') hf rfl rfl
    refine ⟨mem', ?_, recycled_head hhead.readable,
      hchain.recycle_push (fun j hj => (hacc j (by omega)).1) (by omega) hh_fit
        (by rcases hac with h1 | h2; exact Or.inl (by omega); exact Or.inr h2) hfit_ch
        (fun a ha => ⟨by rcases (hsep_ch a ha).1 with h1 | h2; exact Or.inl h1; exact Or.inr (by omega),
          (hsep_ch a ha).2⟩)⟩
    exact .free s67 (.free s70 (.free s716 (.free s160 (.free s1618
      (.free s180 (.free s181 (.free s182 (.free s183 (.free s184
        (.charge s186 (.free s610 (.final sfin))))))))))))
  | succ k ih =>
    intro mem context addr cls elems chain e hk_le hnz he8 hcls_lo hcls_hi hfit hlen_fit hacc
      hscan hcls_load hrem_w hpred_w helems himm hhead hchain hhead_wr hh_fit hac hfit_ch hsep_ch clock
    have h24 : 24 ≤ classBytes cls := by
      have := classWords_ge_three hcls_lo hcls_hi; unfold classBytes; omega
    have hk_lt_len : k < elems.length := by omega
    have hlen_lt : elems.length < 2 ^ 60 := by unfold arrayPayloadOffset at hlen_fit; omega
    have hne0 : Cond.holds .eq .w64 addr (UInt64.ofNat 0) = false := by
      rw [cond_eq_w64]; exact beq_false_of_ne hnz
    have hrem_ne0 : Cond.holds .eq .w64 (UInt64.ofNat (k + 1)) (UInt64.ofNat 0) = false := by
      rw [cond_eq_w64]
      exact beq_false_of_ne (fun h => by
        have := congrArg UInt64.toNat h
        rw [u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by decide)] at this; omega)
    let elem := elems[k]'hk_lt_len
    let m1 := mem.write .w64 (addr + 8) (UInt64.ofNat k)
    have h8_toNat : (addr + 8).toNat = addr.toNat + 8 := addr_toNat_8 (by omega)
    have hwr : mem.write? .w64 (addr + 8) (UInt64.ofNat k) = .ok m1 := by
      apply write?_ok
      intro j hj
      have hj8 : j < 8 := by simpa [X86.Width.bytes] using hj
      have hka : (addr + 8) + UInt64.ofNat j = addr + UInt64.ofNat (8 + j) := by
        apply UInt64.toNat_inj.mp
        rw [addr_toNat (by rw [h8_toNat]; omega), h8_toNat, addr_toNat (by omega)]; omega
      rw [hka]
      exact (hacc (8 + j) (by omega)).2
    let e10 := e.insert 10 (UInt64.ofNat 0xFF)
    let e22 := e10.insert 22 (UInt64.ofNat (k + 1))
    let e26 := e22.insert 26 (UInt64.ofNat k)
    let e27 := e26.insert 27 elem
    let e1' := (e27.insert 1 elem).insert 2 addr
    let e6' := e1'.insert 8 addr
    have s67 := step_br_false (p := arrayProgram fnDec) (fn := fnDec) (lbl := 6) (rest := [])
      (mem := mem) (context := context) (env := e) hf rfl rfl (by simp only [v, Arg.eval, he8]) rfl hne0 rfl rfl rfl
    have s70 := step_assign (p := arrayProgram fnDec) (fn := fnDec) (lbl := 7) (pos := 0) (rest := [])
      (mem := mem) (context := context) (env := e) hf rfl (by decide) rfl
      (rhs_load_eval (cellAddr0_eval he8) hscan)
    have s716 := step_br_true (p := arrayProgram fnDec) (fn := fnDec) (lbl := 7) (rest := [])
      (mem := mem) (context := context) (env := e10) hf rfl rfl
      (by simp only [v, Arg.eval, e10, env_get_insert_self]; rfl) rfl (by decide) rfl rfl rfl
    have s160 := step_assign (p := arrayProgram fnDec) (fn := fnDec) (lbl := 16) (pos := 0) (rest := [])
      (mem := mem) (context := context) (env := e10) hf rfl (by decide) rfl
      (rhs_load_eval (cellAddr_eval_8 (by simp only [e10, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, he8]))
        (wordAt_load64 hrem_w))
    have s1619 := step_br_false (p := arrayProgram fnDec) (fn := fnDec) (lbl := 16) (rest := [])
      (mem := mem) (context := context) (env := e22) hf rfl rfl
      (by simp only [v, Arg.eval, e22, env_get_insert_self]) rfl hrem_ne0 rfl rfl rfl
    have hsub_k : BinOp.eval .sub .w64 (UInt64.ofNat (k + 1)) (UInt64.ofNat 1) = some (UInt64.ofNat k) := by
      simpa using binOp_sub64 (k + 1) 1 (by omega) (by omega)
    have s190 := step_assign (p := arrayProgram fnDec) (fn := fnDec) (lbl := 19) (pos := 0) (rest := [])
      (mem := mem) (context := context) (env := e22) hf rfl (by decide) rfl
      (rhs_bin_eval (by simp only [v, Arg.eval, e22, env_get_insert_self]) rfl hsub_k)
    have s191 := step_assign (p := arrayProgram fnDec) (fn := fnDec) (lbl := 19) (pos := 1) (rest := [])
      (mem := mem) (context := context) (env := e26) hf rfl (by decide) rfl
      (rhs_load_eval
        (wordElemAddr_eval (by simp only [e26, e22, e10, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, he8])
          (by simp only [e26, env_get_insert_self]) (by omega))
        (wordAt_load64 (helems k (by omega))))
    have s192 := step_store (p := arrayProgram fnDec) (fn := fnDec) (lbl := 19) (pos := 2) (rest := [])
      (mem := mem) (context := context) (env := e27) hf rfl (by decide) rfl
      (cellAddr_eval_8 (by simp only [e27, e26, e22, e10, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, he8]))
      (by simp only [v, Arg.eval, e27, e26, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) hwr
    have s191' := step_jump (p := arrayProgram fnDec) (fn := fnDec) (lbl := 19) (rest := [])
      (mem := m1) (context := context) (env := e27) hf rfl rfl
      (evalArgs_pair (by simp only [v, Arg.eval, e27, env_get_insert_self]; rfl)
        (by simp only [v, Arg.eval, e27, e26, e22, e10, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, he8]; rfl))
      rfl rfl
    have htnz : Cond.holds .tnz .w64 elem (UInt64.ofNat 1) = true := by
      simp [Cond.holds, elem, himm k hk_lt_len]
    have s16' := step_br_true (p := arrayProgram fnDec) (fn := fnDec) (lbl := 1) (rest := [])
      (mem := m1) (context := context) (env := e1') hf rfl rfl
      (by simp only [v, Arg.eval, e1', env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) rfl htnz
      (evalArgs_singleton (by simp only [v, Arg.eval, e1', env_get_insert_self]; rfl))
      rfl rfl
    -- Frame all loop invariants across writing `[addr + 8] := k`
    have hscan1 : loadWord m1 .w8 .zero addr = some (UInt64.ofNat 0xFF) :=
      loadWord8_write64_disjoint hscan (by rw [h8_toNat]; omega) (Or.inl (by rw [h8_toNat]; omega))
    have hcls1 : loadWord m1 .w8 .zero (addr + 1) = some (UInt64.ofNat cls) := by
      have h1_toNat : (addr + 1).toNat = addr.toNat + 1 := addr_toNat_1 (by omega)
      exact loadWord8_write64_disjoint hcls_load (by rw [h8_toNat]; omega) (Or.inl (by rw [h1_toNat, h8_toNat]; omega))
    have hrem1 : WordAt m1 (addr + 8) (UInt64.ofNat k) := wordAt_write64 hrem_w.readable
    have hpred1 : WordAt m1 (addr + 16) 0 := by
      have h16_toNat : (addr + 16).toNat = addr.toNat + 16 := addr_toNat_16 (by omega)
      exact wordAt_write64_disjoint hpred_w (by rw [h8_toNat]; omega) (by rw [h16_toNat]; omega)
        (Or.inr (by rw [h8_toNat, h16_toNat]; omega))
    have helems1 : ∀ (j : Nat) (hj : j < k),
        WordAt m1 (addr + UInt64.ofNat (arrayPayloadOffset + 8 * j)) (elems[j]'(by omega)) := by
      intro j hj
      have hj_toNat : (addr + UInt64.ofNat (arrayPayloadOffset + 8 * j)).toNat =
          addr.toNat + (arrayPayloadOffset + 8 * j) := addr_toNat (by unfold arrayPayloadOffset at hlen_fit ⊢; omega)
      exact wordAt_write64_disjoint (helems j (by omega)) (by rw [h8_toNat]; omega)
        (by rw [hj_toNat]; unfold arrayPayloadOffset at hlen_fit ⊢; omega)
        (Or.inr (by rw [h8_toNat, hj_toNat]; unfold arrayPayloadOffset; omega))
    have hhead1 : WordAt m1 (freeHeadAddress context (UInt64.ofNat cls)) (chain.headD 0) :=
      wordAt_write64_disjoint hhead (by rw [h8_toNat]; omega) hh_fit
        (by rcases hac with h1 | h2; exact Or.inr (by rw [h8_toNat]; omega); exact Or.inl (by rw [h8_toNat]; omega))
    have hchain1 : FreeChain m1 chain :=
      freeChain_write64_disjoint hchain (by rw [h8_toNat]; omega) hfit_ch (fun a ha => by
        rcases (hsep_ch a ha).1 with h1 | h2
        · exact Or.inl (by rw [h8_toNat]; omega)
        · exact Or.inr (by rw [h8_toNat]; omega))
    obtain ⟨mem', hreach', hhead', hchain'⟩ := ih (mem := m1) (e := e6') (by omega) hnz
      (by simp only [e6', env_get_insert_self])
      hcls_lo hcls_hi hfit hlen_fit
      (fun j hj => by simpa [m1, Memory.write] using hacc j hj)
      hscan1 hcls1 hrem1 hpred1 helems1 himm hhead1 hchain1
      (fun j hj => by simpa [m1, Memory.write] using hhead_wr j hj)
      hh_fit hac hfit_ch hsep_ch clock
    refine ⟨mem', ?_, hhead', hchain'⟩
    have hclk : clock + (k + 1) + 1 = (clock + k + 1) + 1 := by omega
    rw [hclk]
    exact .free s67 (.free s70 (.free s716 (.free s160 (.free s1619
      (.free s190 (.free s191 (.free s192 (.charge s191' (.free s16' hreach')))))))))

/-- Unique (`refs = 1`) non-empty boxed `Array` holding immediate elements:
`arrDec` runs its O(1)-stack iterative pointer-reversal loop over all `elems.length`
slots right-to-left and recycles the shell onto `[ctx + cls*8]`, extending
`FreeChain` to `addr :: chain`. -/
theorem arrDec_boxed_immediates_free_eval {mem : Memory} {context addr : Word} {cls cap : Nat}
    {elems : List Word} {chain : List Word}
    (h : LiveArrayCell mem addr 1 cls cap (.boxed elems))
    (hne : 0 < elems.length)
    (himm : ∀ (j : Nat) (hj : j < elems.length), elems[j] &&& 1 = 1)
    (hhead : WordAt mem (freeHeadAddress context (UInt64.ofNat cls)) (chain.headD 0))
    (hchain : FreeChain mem chain)
    (hhead_wr : ∀ j < 8, mem.writable (freeHeadAddress context (UInt64.ofNat cls) + UInt64.ofNat j) = true)
    (hh_fit : (freeHeadAddress context (UInt64.ofNat cls)).toNat + 8 ≤ 2 ^ 64)
    (hac : addr.toNat + classBytes cls ≤ (freeHeadAddress context (UInt64.ofNat cls)).toNat ∨
      (freeHeadAddress context (UInt64.ofNat cls)).toNat + 8 ≤ addr.toNat)
    (hfit_chain : ∀ a ∈ chain, a.toNat + 8 ≤ 2 ^ 64)
    (hsep_chain : ∀ a ∈ chain,
      (a.toNat + 8 ≤ addr.toNat ∨ addr.toNat + classBytes cls ≤ a.toNat) ∧
      (a.toNat + 8 ≤ (freeHeadAddress context (UInt64.ofNat cls)).toNat ∨
        (freeHeadAddress context (UInt64.ofNat cls)).toNat + 8 ≤ a.toNat))
    (clock : Nat) :
    ∃ mem',
      eval (arrayProgram fnDec) (clock + elems.length + 1) [addr] mem context = .ok ([], mem') ∧
      WordAt mem' (freeHeadAddress context (UInt64.ofNat cls)) addr ∧
      FreeChain mem' (addr :: chain) := by
  have hf := arrayProgram_func_dec fnDec
  have h24 := h.classBytes_ge_24
  have hfit := h.fit
  have hbytes := (arrayBytes_eq_classBytes h.cls_lo h.cls_hi).1
  have hcap : cap ≤ wordCapOfClass cls := h.cap_fit
  have hsz_le := h.size_le
  simp only [ArrayVal.size] at hsz_le
  have hlen_fit : arrayPayloadOffset + 8 * elems.length ≤ classBytes cls := by omega
  have hlen_lt : elems.length < 2 ^ 60 := by unfold arrayPayloadOffset at hlen_fit; omega
  have hcnt : loadWord mem .w32 .zero (addr + 4) = some (UInt64.ofNat 0) := h.count_load
  have hsc : loadWord mem .w8 .zero addr = some (UInt64.ofNat 0xFF) := h.scan_load
  have hsz_w : WordAt mem (addr + 8) (UInt64.ofNat elems.length) := h.size_word
  let k := elems.length - 1
  have hk_lt : k < elems.length := by omega
  let lastElem := elems[k]'hk_lt
  let m1 := mem.write .w64 (addr + 8) (UInt64.ofNat k)
  let m2 := m1.write .w64 (addr + 16) 0
  have h8_toNat : (addr + 8).toNat = addr.toNat + 8 := addr_toNat_8 (by omega)
  have h16_toNat : (addr + 16).toNat = addr.toNat + 16 := addr_toNat_16 (by omega)
  have hwr1 : mem.write? .w64 (addr + 8) (UInt64.ofNat k) = .ok m1 :=
    live_write64_ok h (off := 8) (by omega) _
  have hwr2 : m1.write? .w64 (addr + 16) 0 = .ok m2 := by
    apply write?_ok
    intro j hj
    have hj8 : j < 8 := by simpa [X86.Width.bytes] using hj
    have hka : (addr + 16) + UInt64.ofNat j = addr + UInt64.ofNat (16 + j) := by
      apply UInt64.toNat_inj.mp
      rw [addr_toNat (by rw [h16_toNat]; omega), h16_toNat, addr_toNat (by omega)]; omega
    rw [hka]
    simpa [m1, Memory.write] using (h.access (16 + j) (by omega)).2
  let e0 : Env := ({} : Env).insert 0 addr
  let e1 := (e0.insert 1 addr).insert 2 0
  let e2 := e1.insert 3 (UInt64.ofNat 0)
  let e5 := e2.insert 5 (UInt64.ofNat 0xFF)
  let e13 := e5.insert 19 (UInt64.ofNat elems.length)
  let e20 := e13.insert 20 (UInt64.ofNat k)
  let e21 := e20.insert 21 lastElem
  let e1' := (e21.insert 1 lastElem).insert 2 addr
  let e6' := e1'.insert 8 addr
  have hinit := state_initial_of (p := arrayProgram fnDec) (args := [addr])
    (mem := mem) (context := context) hf rfl
  have hsz_ne0 : Cond.holds .eq .w64 (UInt64.ofNat elems.length) (UInt64.ofNat 0) = false := by
    rw [cond_eq_w64]
    exact beq_false_of_ne (fun heq => by
      have := congrArg UInt64.toNat heq
      rw [u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by decide)] at this; omega)
  have s01 := step_jump (p := arrayProgram fnDec) (fn := fnDec) (lbl := 0) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl rfl
    (evalArgs_pair (by simp only [v, Arg.eval, e0, env_get_insert_self]; rfl) rfl)
    rfl rfl
  have s12 := step_br_false (p := arrayProgram fnDec) (fn := fnDec) (lbl := 1) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl rfl
    (by simp only [v, Arg.eval, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) rfl h.pointer_branch rfl rfl rfl
  have s20 := step_assign (p := arrayProgram fnDec) (fn := fnDec) (lbl := 2) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_4 (by simp only [e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])) hcnt)
  have s23 := step_br_false (p := arrayProgram fnDec) (fn := fnDec) (lbl := 2) (rest := [])
    (mem := mem) (context := context) (env := e2) hf rfl rfl
    (by simp only [v, Arg.eval, e2, env_get_insert_self]; rfl) rfl (by decide) rfl rfl rfl
  have s35 := step_br_true (p := arrayProgram fnDec) (fn := fnDec) (lbl := 3) (rest := [])
    (mem := mem) (context := context) (env := e2) hf rfl rfl
    (by simp only [v, Arg.eval, e2, env_get_insert_self]; rfl) rfl (by decide) rfl rfl rfl
  have s50 := step_assign (p := arrayProgram fnDec) (fn := fnDec) (lbl := 5) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e2) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr0_eval (by simp only [e2, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])) hsc)
  have s512 := step_br_false (p := arrayProgram fnDec) (fn := fnDec) (lbl := 5) (rest := [])
    (mem := mem) (context := context) (env := e5) hf rfl rfl
    (by simp only [v, Arg.eval, e5, env_get_insert_self]; rfl) rfl (by decide) rfl rfl rfl
  have s1213 := step_br_true (p := arrayProgram fnDec) (fn := fnDec) (lbl := 12) (rest := [])
    (mem := mem) (context := context) (env := e5) hf rfl rfl
    (by simp only [v, Arg.eval, e5, env_get_insert_self]; rfl) rfl (by decide) rfl rfl rfl
  have s130 := step_assign (p := arrayProgram fnDec) (fn := fnDec) (lbl := 13) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e5) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_8 (by simp only [e5, e2, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]))
      (wordAt_load64 hsz_w))
  have s1315 := step_br_false (p := arrayProgram fnDec) (fn := fnDec) (lbl := 13) (rest := [])
    (mem := mem) (context := context) (env := e13) hf rfl rfl
    (by simp only [v, Arg.eval, e13, env_get_insert_self]) rfl hsz_ne0 rfl rfl rfl
  have s150 := step_assign (p := arrayProgram fnDec) (fn := fnDec) (lbl := 15) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e13) hf rfl (by decide) rfl
    (rhs_bin_eval (by simp only [v, Arg.eval, e13, env_get_insert_self]) rfl
      (binOp_sub64 elems.length 1 hne (by omega)))
  have s151 := step_assign (p := arrayProgram fnDec) (fn := fnDec) (lbl := 15) (pos := 1) (rest := [])
    (mem := mem) (context := context) (env := e20) hf rfl (by decide) rfl
    (rhs_load_eval
      (wordElemAddr_eval (by simp only [e20, e13, e5, e2, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
        (by simp only [e20, env_get_insert_self]) (by omega))
      (wordAt_load64 (h.payload k hk_lt)))
  have s152 := step_store (p := arrayProgram fnDec) (fn := fnDec) (lbl := 15) (pos := 2) (rest := [])
    (mem := mem) (context := context) (env := e21) hf rfl (by decide) rfl
    (cellAddr_eval_8 (by simp only [e21, e20, e13, e5, e2, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]))
    (by simp only [v, Arg.eval, e21, e20, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) hwr1
  have s153 := step_store (p := arrayProgram fnDec) (fn := fnDec) (lbl := 15) (pos := 3) (rest := [])
    (mem := m1) (context := context) (env := e21) hf rfl (by decide) rfl
    (cellAddr_eval_16 (by simp only [e21, e20, e13, e5, e2, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]))
    (by simp only [v, Arg.eval, e21, e20, e13, e5, e2, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) hwr2
  have s151' := step_jump (p := arrayProgram fnDec) (fn := fnDec) (lbl := 15) (rest := [])
    (mem := m2) (context := context) (env := e21) hf rfl rfl
    (evalArgs_pair (by simp only [v, Arg.eval, e21, env_get_insert_self]; rfl)
      (by simp only [v, Arg.eval, e21, e20, e13, e5, e2, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]; rfl))
    rfl rfl
  have htnz : Cond.holds .tnz .w64 lastElem (UInt64.ofNat 1) = true := by
    simp [Cond.holds, lastElem, himm k hk_lt]
  have s16' := step_br_true (p := arrayProgram fnDec) (fn := fnDec) (lbl := 1) (rest := [])
    (mem := m2) (context := context) (env := e1') hf rfl rfl
    (by simp only [v, Arg.eval, e1', env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) rfl htnz
    (evalArgs_singleton (by simp only [v, Arg.eval, e1', env_get_insert_self]; rfl))
    rfl rfl
  -- Establish loop invariants on `m2`
  have hscan2 : loadWord m2 .w8 .zero addr = some (UInt64.ofNat 0xFF) :=
    loadWord8_write64_disjoint
      (loadWord8_write64_disjoint hsc (by rw [h8_toNat]; omega) (Or.inl (by rw [h8_toNat]; omega)))
      (by rw [h16_toNat]; omega) (Or.inl (by rw [h16_toNat]; omega))
  have hcls2 : loadWord m2 .w8 .zero (addr + 1) = some (UInt64.ofNat cls) := by
    have h1_toNat : (addr + 1).toNat = addr.toNat + 1 := addr_toNat_1 (by omega)
    exact loadWord8_write64_disjoint
      (loadWord8_write64_disjoint h.class_load (by rw [h8_toNat]; omega) (Or.inl (by rw [h1_toNat, h8_toNat]; omega)))
      (by rw [h16_toNat]; omega) (Or.inl (by rw [h1_toNat, h16_toNat]; omega))
  have hrem2 : WordAt m2 (addr + 8) (UInt64.ofNat k) :=
    wordAt_write64_disjoint (wordAt_write64 h.size_word.readable) (by rw [h16_toNat]; omega) (by rw [h8_toNat]; omega)
      (Or.inl (by rw [h8_toNat, h16_toNat]; omega))
  have hpred2 : WordAt m2 (addr + 16) 0 :=
    wordAt_write64 (fun j hj => by simpa [m1, Memory.write] using h.cap_word.readable j hj)
  have helems2 : ∀ (j : Nat) (hj : j < k),
      WordAt m2 (addr + UInt64.ofNat (arrayPayloadOffset + 8 * j)) (elems[j]'(by omega)) := by
    intro j hj
    have hj_toNat : (addr + UInt64.ofNat (arrayPayloadOffset + 8 * j)).toNat =
        addr.toNat + (arrayPayloadOffset + 8 * j) := addr_toNat (by unfold arrayPayloadOffset at hlen_fit ⊢; omega)
    exact wordAt_write64_disjoint
      (wordAt_write64_disjoint (h.payload j (by omega)) (by rw [h8_toNat]; omega)
        (by rw [hj_toNat]; unfold arrayPayloadOffset at hlen_fit ⊢; omega)
        (Or.inr (by rw [h8_toNat, hj_toNat]; unfold arrayPayloadOffset; omega)))
      (by rw [h16_toNat]; omega)
      (by rw [hj_toNat]; unfold arrayPayloadOffset at hlen_fit ⊢; omega)
      (Or.inr (by rw [h16_toNat, hj_toNat]; unfold arrayPayloadOffset; omega))
  have hhead2 : WordAt m2 (freeHeadAddress context (UInt64.ofNat cls)) (chain.headD 0) :=
    wordAt_write64_disjoint
      (wordAt_write64_disjoint hhead (by rw [h8_toNat]; omega) hh_fit
        (by rcases hac with h1 | h2; exact Or.inr (by rw [h8_toNat]; omega); exact Or.inl (by rw [h8_toNat]; omega)))
      (by rw [h16_toNat]; omega) hh_fit
      (by rcases hac with h1 | h2; exact Or.inr (by rw [h16_toNat]; omega); exact Or.inl (by rw [h16_toNat]; omega))
  have hchain2 : FreeChain m2 chain :=
    freeChain_write64_disjoint
      (freeChain_write64_disjoint hchain (by rw [h8_toNat]; omega) hfit_chain (fun a ha => by
        rcases (hsep_chain a ha).1 with h1 | h2; exact Or.inl (by rw [h8_toNat]; omega); exact Or.inr (by rw [h8_toNat]; omega)))
      (by rw [h16_toNat]; omega) hfit_chain (fun a ha => by
        rcases (hsep_chain a ha).1 with h1 | h2; exact Or.inl (by rw [h16_toNat]; omega); exact Or.inr (by rw [h16_toNat]; omega))
  obtain ⟨mem', hreach', hhead', hchain'⟩ :=
    arrDec_boxed_immediates_loop k (mem := m2) (e := e6') (by omega) h.nonzero
      (by simp only [e6', env_get_insert_self])
      h.cls_lo h.cls_hi hfit hlen_fit
      (fun j hj => by simpa [m2, m1, Memory.write] using h.access j hj)
      hscan2 hcls2 hrem2 hpred2 helems2 himm hhead2 hchain2
      (fun j hj => by simpa [m2, m1, Memory.write] using hhead_wr j hj)
      hh_fit hac hfit_chain hsep_chain clock
  refine ⟨mem', ?_, hhead', hchain'⟩
  apply (runs_eval hinit).eq
  have hclk : clock + elems.length + 1 = (clock + k + 1) + 1 := by omega
  rw [hclk]
  exact .free s01 (.free s12 (.free s20 (.free s23 (.free s35 (.free s50
    (.free s512 (.free s1213 (.free s130 (.free s1315
      (.free s150 (.free s151 (.free s152 (.free s153 (.charge s151' (.free s16' hreach')))))))))))))))

end IxCC.Rt.Rc.Array
