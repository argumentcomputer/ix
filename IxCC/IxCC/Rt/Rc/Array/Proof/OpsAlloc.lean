import IxCC.Rt.Rc.Array.Ops
import IxCC.Rt.Rc.Array.Proof.DecArrCell

/-! # Allocation of an array cell (`Ops.alloc`), specified

`alloc_returns`: in any program holding `Ops.alloc t k` at `fn` and the two size-class
procedures at `t.classFor` and `t.classWords`, a request for capacity `n ≤ k.maxCap` whose class
has a free cell or room below the limit returns, after 2 charges (the two class calls), a fresh
empty cell of class `allocClass k n` with one reference and the class's capacity (`AllocDone`):

* the allocator kept, with the cell popped from its free list or the bump pointer advanced;
* the cell allocated, apart from every free cell;
* every cell allocated before still allocated, and apart from the new one;
* memory changed only in the allocator's bytes and the new cell's.

Here also the address lemmas the other procedures' proofs share (`elemAt_eval`, `headAt_eval`). -/

set_option autoImplicit false

namespace IxCC.Rt.Rc.Array

open Lir
open IxCC.Rt.Proof (WordAt addr_toNat write?_ok wordAt_write64)
open IxCC.Rt.Rc (maxClass classWords classFor classBytes maxCellWords maxCount)
open IxCC.Rt.Rc.Procs (v i to cellAddr FreeChain freeHeadAddress bumpAddress limitAddress)
open IxCC.X86 (Memory)
open Ops

/-! ## Addresses -/

theorem elemAt_eval {ρ : Env} {ctx addr : Word} {k : ElemKind} {b r : VReg} {j : Nat}
    (hb : ρ[b]? = some addr) (hr : ρ[r]? = some (UInt64.ofNat j))
    (hj : arrayPayloadOffset + k.bytes * j < 2 ^ 64) :
    (elemAt k b r).eval ρ ctx = some (elemAddr addr k j) := by
  simp only [elemAt, Addr.eval, hb, hr, bind, Option.bind, Functor.map, Option.map,
    k.scale_word]
  congr 1
  have h24 : dispWord 24 = UInt64.ofNat 24 := dispWord_ofNat 24
  have hbj : k.bytes * j < 2 ^ 64 := by unfold arrayPayloadOffset at hj; omega
  have hb8 := k.bytes_le
  have hm : UInt64.ofNat j * UInt64.ofNat k.bytes = UInt64.ofNat (k.bytes * j) := by
    apply UInt64.toNat_inj.mp
    have hjj : j < 2 ^ 64 := by
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · omega
      · have := Nat.le_mul_of_pos_left j k.bytes_pos; omega
    rw [UInt64.toNat_mul, u64_toNat_ofNat_lt hjj, u64_toNat_ofNat_lt (by omega),
      u64_toNat_ofNat_lt hbj, Nat.mul_comm, Nat.mod_eq_of_lt hbj]
  rw [h24, hm, UInt64.add_assoc, u64_add_ofNat (by unfold arrayPayloadOffset at hj; omega)]
  unfold elemAddr arrayPayloadOffset
  rw [Nat.add_comm (k.bytes * j) 24]

theorem headAt_eval {ρ : Env} {ctx c : Word} {r : VReg} (hr : ρ[r]? = some c) :
    (headAt r).eval ρ ctx = some (freeHeadAddress ctx c) := ctxHead_eval hr

theorem ovf_addC_ok {a b : Word} (h : a.toNat + b.toNat < 2 ^ 64) :
    Ovf.eval .addC a b = (a + b, false) := by
  have hsum : (a + b).toNat = a.toNat + b.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt h]
  have hlt : ¬ (a + b < a) := by
    rw [UInt64.lt_iff_toNat_lt, hsum]; omega
  simp [Ovf.eval, hlt]

/-! ## The class of a request -/

/-- The class `alloc k` allocates for capacity `n`. -/
def allocClass (k : ElemKind) (n : Nat) : Nat := classForFast (k.cellWords n)

theorem allocClass_spec (k : ElemKind) {n : Nat} (hn : n ≤ k.maxCap) :
    minArrayClass ≤ allocClass k n ∧ allocClass k n ≤ maxClass ∧ n ≤ k.capOfClass (allocClass k n) :=
  k.capOfClass_spec (classForFast_eq (by have := k.cellWords_ge_three n; omega) (k.cellWords_le_max hn))

/-- What an allocation leaves: the allocator after it, the fresh cell, and everything else kept. -/
structure AllocDone (mem mem' : Memory) (ctx base bump limit : Word) (lists : Nat → List Word)
    (k : ElemKind) (cls : Nat) (addr bump' : Word) (lists' : Nat → List Word) : Prop where
  alloc : ArrayAllocator mem' ctx base bump' limit lists'
  cell : ArrCell mem' addr 1 cls (k.capOfClass cls) k []
  allocated : Allocated base bump' lists' addr (classBytes cls)
  keeps : ∀ a n, Allocated base bump lists a n →
    Allocated base bump' lists' a n ∧ (a.toNat + n ≤ addr.toNat ∨ addr.toNat + classBytes cls ≤ a.toNat)
  frame : MemFrame mem mem' (fun x => AllocBytes ctx lists x ∨
    (addr.toNat ≤ x ∧ x < addr.toNat + classBytes cls))

private theorem classBytes_ge_8 {c : Nat} (h : 1 ≤ c) : 8 ≤ classBytes c := by
  have := IxCC.Rt.Rc.classWords_pos h; unfold classBytes; omega

/-- Block 6: the header, size and capacity words of the fresh cell. -/
private theorem init_cell {mem : Memory} {ctx base bump limit : Word} {lists : Nat → List Word}
    (halloc : ArrayAllocator mem ctx base bump limit lists) {k : ElemKind} {cls : Nat}
    (hlo : minArrayClass ≤ cls) (hhi : cls ≤ maxClass) {a : Word}
    (ha : Allocated base bump lists a (classBytes cls)) (hal : a.toNat % 8 = 0) (hnz : a ≠ 0) :
    let m1 := mem.write .w64 a (k.header cls 1)
    let m2 := m1.write .w64 (a + 8) (UInt64.ofNat 0)
    let m3 := m2.write .w64 (a + 16) (UInt64.ofNat (k.capOfClass cls))
    mem.write? .w64 a (k.header cls 1) = .ok m1 ∧
    m1.write? .w64 (a + 8) (UInt64.ofNat 0) = .ok m2 ∧
    m2.write? .w64 (a + 16) (UInt64.ofNat (k.capOfClass cls)) = .ok m3 ∧
    ArrayAllocator m3 ctx base bump limit lists ∧ ArrCell m3 a 1 cls (k.capOfClass cls) k [] ∧
    MemFrame mem m3 (fun x => a.toNat ≤ x ∧ x < a.toNat + 24) := by
  intro m1 m2 m3
  have h3 := classWords_ge_three hlo hhi
  have hcb : classBytes cls = 8 * classWords cls := rfl
  have hlf := halloc.limit_fit
  have hbl := halloc.bump_le_limit
  have hfit : a.toNat + classBytes cls < 2 ^ 63 := by have := ha.2.1; omega
  have hacc : ∀ j < classBytes cls, mem.readable (a + UInt64.ofNat j) = true ∧
      mem.writable (a + UInt64.ofNat j) = true := by
    intro j hj
    have hja : (a + UInt64.ofNat j).toNat = a.toNat + j := addr_toNat (by omega)
    exact halloc.arena_access _ (by have := ha.1; omega) (by have := ha.2.1; omega)
  have h8 : (a + 8).toNat = a.toNat + 8 := addr_toNat (i := 8) (by omega)
  have h16 : (a + 16).toNat = a.toNat + 16 := addr_toNat (i := 16) (by omega)
  have hw1 : mem.write? .w64 a (k.header cls 1) = .ok m1 :=
    write?_ok (fun j hj => (hacc j (by simp [X86.Width.bytes] at hj; omega)).2)
  have hw2 : m1.write? .w64 (a + 8) (UInt64.ofNat 0) = .ok m2 :=
    write?_ok_of_access (off := 8) (n := classBytes cls) (base := a) _
      (fun j hj => by simpa [m1, Memory.write] using (hacc j hj).2) (by omega)
      (by simp [X86.Width.bytes]; omega)
  have hw3 : m2.write? .w64 (a + 16) (UInt64.ofNat (k.capOfClass cls)) = .ok m3 :=
    write?_ok_of_access (off := 16) (n := classBytes cls) (base := a) _
      (fun j hj => by simpa [m2, m1, Memory.write] using (hacc j hj).2) (by omega)
      (by simp [X86.Width.bytes]; omega)
  have f1 := MemFrame.write mem .w64 a (k.header cls 1) (by simp [X86.Width.bytes]; omega)
  have f2 := MemFrame.write m1 .w64 (a + 8) (UInt64.ofNat 0) (by rw [h8]; simp [X86.Width.bytes]; omega)
  have f3 := MemFrame.write m2 .w64 (a + 16) (UInt64.ofNat (k.capOfClass cls))
    (by rw [h16]; simp [X86.Width.bytes]; omega)
  have hfr : MemFrame mem m3 (fun x => a.toNat ≤ x ∧ x < a.toNat + 24) :=
    ((f1.mono (fun x hx => by unfold Span at hx; simp [X86.Width.bytes] at hx; omega)).trans
      (f2.mono (fun x hx => by unfold Span at hx; rw [h8] at hx; simp [X86.Width.bytes] at hx; omega))).trans
      (f3.mono (fun x hx => by unfold Span at hx; rw [h16] at hx; simp [X86.Width.bytes] at hx; omega))
  have hcap := k.capOfClass_le_maxCap hhi
  refine ⟨hw1, hw2, hw3, halloc.frame hfr (fun x hx => ha.not_allocBytes halloc x hx.1 (by omega)),
    ⟨⟨hal, hnz, hlo, hhi, by decide, by unfold maxCount; omega, hfit, by simp, Nat.le_refl _,
      fun j hj => by simpa [m3, m2, m1, Memory.write] using hacc j hj, ?_, ?_, ?_⟩,
      fun j hj => by simp at hj, fun x hx => by simp at hx⟩, hfr⟩
  · have hw : WordAt m1 a (k.header cls 1) := wordAt_write64 (fun j hj => (hacc j (by omega)).1)
    exact (hw.write_disjoint (by rw [h8]; simp [X86.Width.bytes]; omega) (by omega)
      (by rw [h8]; simp [X86.Width.bytes])).write_disjoint
      (by rw [h16]; simp [X86.Width.bytes]; omega) (by omega) (by rw [h16]; simp [X86.Width.bytes])
  · have hw : WordAt m2 (a + 8) (UInt64.ofNat 0) := wordAt_write64 (fun j hj => by
      have := hacc (8 + j) (by omega)
      have hja : a + 8 + UInt64.ofNat j = a + UInt64.ofNat (8 + j) := by
        apply UInt64.toNat_inj.mp
        rw [addr_toNat (by rw [h8]; omega), h8, addr_toNat (by omega)]; omega
      rw [hja]; simpa [m1, Memory.write] using this.1)
    simpa using hw.write_disjoint (by rw [h16]; simp [X86.Width.bytes]; omega) (by rw [h8]; omega)
      (by rw [h8, h16]; simp [X86.Width.bytes])
  · exact wordAt_write64 (fun j hj => by
      have := hacc (16 + j) (by omega)
      have hja : a + 16 + UInt64.ofNat j = a + UInt64.ofNat (16 + j) := by
        apply UInt64.toNat_inj.mp
        rw [addr_toNat (by rw [h16]; omega), h16, addr_toNat (by omega)]; omega
      rw [hja]; simpa [m2, m1, Memory.write] using this.1)

/-- Blocks 0 and 1: the class of the request and the head of its free list, after the two class
calls. -/
theorem alloc_prefix {P : Program} {fn : FunId} {t : Fns} {k : ElemKind}
    (hfn : P.funcs[fn]? = some (alloc t k)) (hcf : P.funcs[t.classFor]? = some arrClassFor)
    (hcw : P.funcs[t.classWords]? = some arrClassWords) {mem : Memory} {ctx : Word}
    {n : Nat} (hn : n ≤ k.maxCap) {head : Word}
    (hhead : loadWord mem .w64 .zero (freeHeadAddress ctx (UInt64.ofNat (allocClass k n))) = some head) :
    ∃ e, e[5]? = some (UInt64.ofNat (allocClass k n)) ∧
      e[6]? = some (UInt64.ofNat (classWords (allocClass k n))) ∧ e[7]? = some head ∧
      ∀ rest : List Frame, Sem.Star (semStep P)
        (State.mk mem ctx ({ fn, label := 0, pos := 0, env := ({} : Env).insert 0 (UInt64.ofNat n) } :: rest)) 2
        (State.mk mem ctx ({ fn, label := 1, pos := 7, env := e } :: rest)) := by
  obtain ⟨hlo, hhi, _⟩ := allocClass_spec k hn
  have hmc : k.maxCap ≤ 8 * maxWordCap := by
    unfold ElemKind.maxCap; exact Nat.mul_le_mul_right _ k.perWord_le
  have hmw : maxWordCap = 2 ^ 26 - 3 := by
    unfold maxWordCap arrayHeaderWords; rw [IxCC.Rt.Rc.maxCellWords_eq]
  have hsh := k.shift_le
  have hbs := k.bytes_eq_shift
  have hnb : n <<< k.shift = k.bytes * n := by rw [Nat.shiftLeft_eq, hbs, Nat.mul_comm]
  have hb8 := k.bytes_le
  have hbn : k.bytes * n ≤ 8 * n := Nat.mul_le_mul_right n hb8
  have hugt : Cond.holds .ugt .w64 (UInt64.ofNat n) (UInt64.ofNat k.maxCap) = false := by
    rw [cond_ugt_w64, u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by omega)]
    exact decide_eq_false (by omega)
  have hshl : BinOp.eval .shl .w64 (UInt64.ofNat n) (UInt64.ofNat k.shift) =
      some (UInt64.ofNat (k.bytes * n)) := by
    rw [binOp_shl64 n k.shift (by omega) (by omega) (by rw [hnb]; omega), hnb]
  have hadd7 := binOp_add64 (k.bytes * n) 7 (by omega)
  have hshr := binOp_shr64 (k.bytes * n + 7) 3 (by decide) (by omega)
  have hwords : BinOp.eval .add .w64 (UInt64.ofNat ((k.bytes * n + 7) >>> 3)) (UInt64.ofNat 3) =
      some (UInt64.ofNat (k.cellWords n)) := by
    rw [binOp_add64 _ _ (by rw [Nat.shiftRight_eq_div_pow]; omega)]
    unfold ElemKind.cellWords arrayHeaderWords
    rw [Nat.shiftRight_eq_div_pow]; congr 2; omega
  have hw1 : 1 ≤ k.cellWords n := by have := k.cellWords_ge_three n; omega
  have hw2 := k.cellWords_le_max hn
  have hc1 : 1 ≤ allocClass k n := by unfold minArrayClass at hlo; omega
  have hcfr : Returns1 P t.classFor (({} : Env).insert 0 (UInt64.ofNat (k.cellWords n))) mem ctx 0
      (UInt64.ofNat (allocClass k n)) mem := classFor_returns hcf mem ctx hw1 hw2
  refine ⟨?e, ?h5, ?h6, ?h7, fun rest => ?hs⟩
  case hs =>
    refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hugt
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hfn rfl (by body_pos) rfl (rhs_bin_eval (by arg_eval) (by arg_eval) hshl) ?_
    refine star_assign hfn rfl (by body_pos) rfl (rhs_bin_eval (by arg_eval) (by arg_eval) hadd7) ?_
    refine star_assign hfn rfl (by body_pos) rfl (rhs_bin_eval (by arg_eval) (by arg_eval) hshr) ?_
    refine star_assign hfn rfl (by body_pos) rfl (rhs_bin_eval (by arg_eval) (by arg_eval) hwords) ?_
    refine star_call1_eq (c' := 1) hfn rfl (by body_pos) rfl (evalArgs1 (by arg_eval)) hcf rfl
      hcfr ?_ rfl
    refine star_call1_eq (c' := 0) hfn rfl (by body_pos) rfl (evalArgs1 (by arg_eval)) hcw rfl
      (classWords_returns hcw mem ctx (c := allocClass k n) hc1 hhi) ?_ rfl
    refine star_assign hfn rfl (by body_pos) rfl
      (rhs_load_eval (headAt_eval (by env_lookup)) hhead) ?_
    exact .refl _
  case h5 => env_lookup
  case h6 => env_lookup
  case h7 => env_lookup

/-- Block 6 to the return, from a cell address in register 13. -/
private theorem alloc_tail {P : Program} {fn : FunId} {t : Fns} {k : ElemKind}
    (hfn : P.funcs[fn]? = some (alloc t k)) {mem m1 m2 m3 : Memory} {ctx a : Word}
    {cls : Nat} (hlo : minArrayClass ≤ cls) (hhi : cls ≤ maxClass)
    (hw1 : mem.write? .w64 a (k.header cls 1) = .ok m1)
    (hw2 : m1.write? .w64 (a + 8) (UInt64.ofNat 0) = .ok m2)
    (hw3 : m2.write? .w64 (a + 16) (UInt64.ofNat (k.capOfClass cls)) = .ok m3)
    {e : Env} (h5 : e[5]? = some (UInt64.ofNat cls))
    (h6 : e[6]? = some (UInt64.ofNat (classWords cls))) (h13 : e[13]? = some a) :
    ∃ e', e'[13]? = some a ∧
      ∀ rest : List Frame, Sem.Star (semStep P) (State.mk mem ctx ({ fn, label := 6, pos := 0, env := e } :: rest)) 0
        (State.mk m3 ctx ({ fn, label := 6, pos := 7, env := e' } :: rest)) := by
  have h3 := classWords_ge_three hlo hhi
  have hcwm := IxCC.Rt.Rc.classWords_le_max hhi
  have hmax : maxCellWords = 2 ^ 26 := IxCC.Rt.Rc.maxCellWords_eq
  have hsh := k.shift_le
  have hcls8 : cls <<< 8 < 2 ^ 64 := by rw [Nat.shiftLeft_eq]; unfold maxClass at hhi; omega
  have hhdr : BinOp.eval .or .w64 k.template (UInt64.ofNat (cls <<< 8)) = some (k.header cls 1) := by
    rw [binOp_or64, ← u64_shl_ofNat (by decide) (by unfold maxClass at hhi; omega) hcls8]
    exact congrArg some (k.template_or_cls hhi)
  have hcap : (classWords cls - 3) <<< (3 - k.shift) = k.capOfClass cls := by
    unfold ElemKind.capOfClass ElemKind.perWord arrayHeaderWords
    rw [Nat.shiftLeft_eq, Nat.mul_comm]
  have hp8 := k.perWord_le
  have hcapb : (classWords cls - 3) <<< (3 - k.shift) < 2 ^ 64 := by
    rw [hcap]; unfold ElemKind.capOfClass arrayHeaderWords
    have := Nat.mul_le_mul_right (classWords cls - 3) hp8; omega
  have hshl2 := binOp_shl64 (classWords cls - 3) (3 - k.shift) (by omega) (by omega) hcapb
  rw [hcap] at hshl2
  refine ⟨?e, ?h13, fun rest => ?hs⟩
  case hs =>
    refine star_assign hfn rfl (by body_pos) rfl (rhs_bin_eval (by arg_eval) (by arg_eval)
      (binOp_shl64 cls 8 (by decide) (by unfold maxClass at hhi; omega) hcls8)) ?_
    refine star_assign hfn rfl (by body_pos) rfl (rhs_bin_eval (by arg_eval) (by arg_eval) hhdr) ?_
    refine star_assign hfn rfl (by body_pos) rfl (rhs_bin_eval (by arg_eval) (by arg_eval)
      (binOp_sub64 (classWords cls) 3 (by omega) (by omega))) ?_
    refine star_assign hfn rfl (by body_pos) rfl (rhs_bin_eval (by arg_eval) (by arg_eval) hshl2) ?_
    refine star_store hfn rfl (by body_pos) rfl (cellAddr0_eval (by env_lookup)) (by arg_eval) hw1 ?_
    refine star_store hfn rfl (by body_pos) rfl (cellAddr_eval_8 (by env_lookup)) (by arg_eval) hw2 ?_
    refine star_store hfn rfl (by body_pos) rfl (cellAddr_eval_16 (by env_lookup)) (by arg_eval) hw3 ?_
    exact .refl _
  case h13 => env_lookup

/-- **Allocation.** A request for capacity `n ≤ k.maxCap` whose class has a free cell, or room
below the limit, returns a fresh empty cell of the class, in two charges. -/
theorem alloc_returns {P : Program} {fn : FunId} {t : Fns} {k : ElemKind}
    (hfn : P.funcs[fn]? = some (alloc t k)) (hcf : P.funcs[t.classFor]? = some arrClassFor)
    (hcw : P.funcs[t.classWords]? = some arrClassWords)
    {mem : Memory} {ctx base bump limit : Word} {lists : Nat → List Word}
    (halloc : ArrayAllocator mem ctx base bump limit lists) {n : Nat} (hn : n ≤ k.maxCap)
    (hroom : lists (allocClass k n) ≠ [] ∨
      bump.toNat + classBytes (allocClass k n) ≤ limit.toNat) :
    ∃ addr mem' bump' lists',
      Returns1 P fn (({} : Env).insert 0 (UInt64.ofNat n)) mem ctx 2 addr mem' ∧
      AllocDone mem mem' ctx base bump limit lists k (allocClass k n) addr bump' lists' := by
  obtain ⟨hlo, hhi, _⟩ := allocClass_spec k hn
  have hc1 : 1 ≤ allocClass k n := by unfold minArrayClass at hlo; omega
  have hcb := halloc.context_before
  have hcf' := halloc.context_fit
  have hcl := halloc.context_lower
  have hlf := halloc.limit_fit
  have hbl := halloc.bump_le_limit
  have hbb := halloc.base_le_bump
  have hcwm := IxCC.Rt.Rc.classWords_le_max hhi
  have hmax : maxCellWords = 2 ^ 26 := IxCC.Rt.Rc.maxCellWords_eq
  have hcbytes : classBytes (allocClass k n) = 8 * classWords (allocClass k n) := rfl
  have h3 := classWords_ge_three hlo hhi
  have hhn := halloc.freeHead_toNat hhi
  have hhead := wordAt_load64 (halloc.free_heads _ hc1 hhi)
  have hmc : maxClass = 71 := rfl
  cases hlist : lists (allocClass k n) with
  | cons a tail =>
    rw [hlist, List.headD_cons] at hhead
    have hin := halloc.free_in_arena _ a (by rw [hlist]; exact List.mem_cons_self)
    obtain ⟨hwh, halloc1, hdisj⟩ := halloc.pop_free_head hlo hhi hlist
    have hchain := halloc.free_chains (allocClass k n)
    rw [hlist] at hchain
    have hmem_old : ∀ c b, b ∈ (fun c => if c = allocClass k n then tail else lists c) c →
        b ∈ lists c := by
      intro c b hb
      by_cases hce : c = allocClass k n
      · subst hce; rw [hlist]; exact List.mem_cons_of_mem _ (by simpa using hb)
      · simpa [hce] using hb
    have hA : Allocated base bump (fun c => if c = allocClass k n then tail else lists c) a
        (classBytes (allocClass k n)) := ⟨hin.1, hin.2.1, fun c b hb => hdisj c b hb⟩
    have hfr1 : MemFrame mem (mem.write .w64 (freeHeadAddress ctx (UInt64.ofNat (allocClass k n)))
        (tail.headD 0)) (fun x => AllocBytes ctx lists x) :=
      (MemFrame.write mem .w64 _ _ (by simp [X86.Width.bytes]; omega)).mono
        (fun x hx => by
          unfold Span at hx; simp [X86.Width.bytes] at hx
          exact Or.inl ⟨by omega, by omega⟩)
    obtain ⟨hw1, hw2, hw3, hal3, hcell, hfr2⟩ := init_cell (k := k) halloc1 hlo hhi hA hin.2.2.1 hin.2.2.2
    refine ⟨a, _, bump, _, ?_, ⟨hal3, hcell, hA, ?_, ?_⟩⟩
    · obtain ⟨e, h5, h6, h7, hpre⟩ := alloc_prefix hfn hcf hcw hn hhead
      obtain ⟨e', h13', htail⟩ := alloc_tail (t := t) hfn hlo hhi hw1 hw2 hw3
        (e := ((e.insert 8 (tail.headD 0)).insert 13 a)) (by env_lookup) (by env_lookup)
        (by env_lookup)
      refine returns1_of_star (lbl := 6) (env' := e') hfn rfl rfl (by arg_eval) (fun rest => ?_)
      refine star_cast ((hpre rest).trans ?_) (show 2 + 0 = 2 from rfl)
      have hne0 : Cond.holds .eq .w64 a (UInt64.ofNat 0) = false := by
        rw [cond_eq_w64]; exact beq_false_of_ne hin.2.2.2
      refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hne0
        (evalArgs_nil _) rfl rfl ?_
      refine star_assign hfn rfl (by body_pos) rfl
        (rhs_load_eval (cellAddr0_eval (by env_lookup)) (wordAt_load64 hchain.1)) ?_
      refine star_store hfn rfl (by body_pos) rfl (headAt_eval (by env_lookup)) (by arg_eval) hwh ?_
      refine star_jump_fwd hfn rfl rfl rfl rfl (evalArgs1 (by arg_eval)) rfl rfl ?_
      exact htail rest
    · intro b m hb
      refine ⟨⟨hb.1, hb.2.1, fun c d hd => hb.2.2 c d (hmem_old c d hd)⟩, ?_⟩
      rcases hb.2.2 (allocClass k n) a (by rw [hlist]; exact List.mem_cons_self) with h | h
      · exact Or.inr h
      · exact Or.inl h
    · exact (hfr1.mono (fun x hx => Or.inl hx)).trans
        (hfr2.mono (fun x hx => Or.inr ⟨hx.1, by omega⟩))
  | nil =>
    rw [hlist, List.headD_nil] at hhead
    have hroom' : bump.toNat + classBytes (allocClass k n) ≤ limit.toNat := by
      rcases hroom with h | h
      · exact absurd hlist h
      · exact h
    obtain ⟨hwb, halloc1, hdisj⟩ := halloc.advance_bump (cls := allocClass k n) hroom'
    have hbn' : (bump + UInt64.ofNat (classBytes (allocClass k n))).toNat =
        bump.toNat + classBytes (allocClass k n) := addr_toNat (by omega)
    have hA : Allocated base (bump + UInt64.ofNat (classBytes (allocClass k n))) lists bump
        (classBytes (allocClass k n)) :=
      ⟨hbb, by rw [hbn']; exact Nat.le_refl _, fun c b hb => by
        have := halloc.free_in_arena c b hb; exact Or.inl (by omega)⟩
    have hnz : bump ≠ 0 := fun h => by rw [h] at hbb; simp at hbb; omega
    have hbn := halloc.bump_toNat
    have hfr1 : MemFrame mem (mem.write .w64 (bumpAddress ctx)
        (bump + UInt64.ofNat (classBytes (allocClass k n)))) (fun x => AllocBytes ctx lists x) :=
      (MemFrame.write mem .w64 _ _ (by simp [X86.Width.bytes]; omega)).mono
        (fun x hx => by
          unfold Span at hx; simp [X86.Width.bytes] at hx
          exact Or.inl ⟨by omega, by omega⟩)
    obtain ⟨hw1, hw2, hw3, hal3, hcell, hfr2⟩ :=
      init_cell (k := k) halloc1 hlo hhi hA halloc.bump_aligned hnz
    refine ⟨bump, _, _, lists, ?_, ⟨hal3, hcell, hA, ?_, ?_⟩⟩
    · obtain ⟨e, h5, h6, h7, hpre⟩ := alloc_prefix hfn hcf hcw hn hhead
      obtain ⟨e', h13', htail⟩ := alloc_tail (t := t) hfn hlo hhi hw1 hw2 hw3
        (e := (((((e.insert 9 bump).insert 10 limit).insert 11
          (UInt64.ofNat (classBytes (allocClass k n)))).insert 12
          (bump + UInt64.ofNat (classBytes (allocClass k n)))).insert 13 bump))
        (by env_lookup) (by env_lookup) (by env_lookup)
      refine returns1_of_star (lbl := 6) (env' := e') hfn rfl rfl (by arg_eval) (fun rest => ?_)
      refine star_cast ((hpre rest).trans ?_) (show 2 + 0 = 2 from rfl)
      have hshl3 : BinOp.eval .shl .w64 (UInt64.ofNat (classWords (allocClass k n))) (UInt64.ofNat 3) =
          some (UInt64.ofNat (classBytes (allocClass k n))) := by
        rw [binOp_shl64 _ 3 (by decide) (by omega) (by rw [Nat.shiftLeft_eq]; omega), Nat.shiftLeft_eq,
          hcbytes, Nat.mul_comm]
      have hcbw : (UInt64.ofNat (classBytes (allocClass k n))).toNat = classBytes (allocClass k n) :=
        u64_toNat_ofNat_lt (by omega)
      refine star_br_true_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) (by decide)
        (evalArgs_nil _) rfl rfl ?_
      refine star_assign hfn rfl (by body_pos) rfl
        (rhs_load_eval (ctxAddr_eval_bump _ _) (wordAt_load64 halloc.bump_word)) ?_
      refine star_assign hfn rfl (by body_pos) rfl
        (rhs_load_eval (ctxAddr_eval_limit _ _) (wordAt_load64 halloc.limit_word)) ?_
      refine star_assign hfn rfl (by body_pos) rfl (rhs_bin_eval (by arg_eval) (by arg_eval) hshl3) ?_
      refine star_brOvf_ok_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval)
        (ovf_addC_ok (by rw [hcbw]; omega)) (evalArgs_nil _) rfl rfl ?_
      have hule : Cond.holds .ule .w64 (bump + UInt64.ofNat (classBytes (allocClass k n))) limit = true := by
        rw [cond_ule_w64, hbn']; exact decide_eq_true hroom'
      refine star_br_true_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hule
        (evalArgs_nil _) rfl rfl ?_
      refine star_store hfn rfl (by body_pos) rfl (ctxAddr_eval_bump _ _) (by arg_eval) hwb ?_
      refine star_jump_fwd hfn rfl rfl rfl rfl (evalArgs1 (by arg_eval)) rfl rfl ?_
      exact htail rest
    · intro b m hb
      have hb21 := hb.2.1
      exact ⟨⟨hb.1, by rw [hbn']; omega, hb.2.2⟩, Or.inl hb21⟩
    · exact (hfr1.mono (fun x hx => Or.inl hx)).trans
        (hfr2.mono (fun x hx => Or.inr ⟨hx.1, by omega⟩))

end IxCC.Rt.Rc.Array
