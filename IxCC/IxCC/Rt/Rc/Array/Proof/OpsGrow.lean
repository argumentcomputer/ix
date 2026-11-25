import IxCC.Rt.Rc.Array.Proof.OpsShared

/-! # Growth and the copying paths of `push` and `pop`, specified

| procedure | path | theorem | charges |
| --- | --- | --- | --- |
| `push k` | unique and full: grown, old cell recycled | `push_grow` | `n + 4` |
| `push (.packed w)` | shared | `push_shared_packed` | `n + 5` |
| `pop (.packed w)` | shared, non-empty | `pop_shared_packed` | `n + 4` |

Growth moves the elements (no increment, no release: the references move with them) into a cell
of `growCap k n` elements (twice the size, at least one more, at most `k.maxCap`), appends, and
recycles the old cell onto its free list. -/

set_option autoImplicit false

namespace IxCC.Rt.Rc.Array

open Lir
open IxCC.Rt.Proof (WordAt addr_toNat write?_ok wordAt_write64)
open IxCC.Rt.Rc (maxClass classBytes classWords maxCount)
open IxCC.Rt.Rc.Procs (v i to cellAddr storeCount freeHeadAddress recycleParent)
open IxCC.X86 (Memory)
open Ops

/-- The two stores of an append in place succeed. -/
theorem ArrCell.push_writes {mem : Memory} {a : Word} {refs cls cap : Nat} {k : ElemKind}
    {xs : List Word} (h : ArrCell mem a refs cls cap k xs) (hroom : xs.length < cap) (x : Word) :
    mem.write? k.width (elemAddr a k xs.length) x =
      .ok (mem.write k.width (elemAddr a k xs.length) x) ∧
    (mem.write k.width (elemAddr a k xs.length) x).write? .w64 (a + 8)
      (UInt64.ofNat (xs.length + 1)) = .ok ((mem.write k.width (elemAddr a k xs.length) x).write .w64
        (a + 8) (UInt64.ofNat (xs.length + 1))) ∧
    arrayPayloadOffset + k.bytes * xs.length < 2 ^ 64 := by
  have hs := h.shell
  have hfit := hs.fit
  have h24 := hs.classBytes_ge_24
  have hbw : k.width.bytes = k.bytes := rfl
  obtain ⟨hja, hjb⟩ := hs.elem_toNat hroom
  refine ⟨write?_ok (fun b hb => ?_), ?_, by omega⟩
  · have := hs.access (arrayPayloadOffset + k.bytes * xs.length + b) (by omega)
    have hadd : elemAddr a k xs.length + UInt64.ofNat b =
        a + UInt64.ofNat (arrayPayloadOffset + k.bytes * xs.length + b) := by
      apply UInt64.toNat_inj.mp
      rw [addr_toNat (by rw [hja]; omega), hja, addr_toNat (by omega)]; omega
    rw [hadd]; exact this.2
  · exact (MemFrame.write mem k.width (elemAddr a k xs.length) x (by rw [hja]; omega)).write?_ok
      (hs.write_ok (off := 8) (w := .w64) (by simp [X86.Width.bytes]; omega) (UInt64.ofNat 0))

theorem growCap_spec (k : ElemKind) {n : Nat} (hn : n < k.maxCap) :
    n + 1 ≤ growCap k n ∧ growCap k n ≤ k.maxCap := by
  unfold growCap; split <;> omega

/-- The capacity `push`'s growth computes. -/
private theorem growCap_eval {k : ElemKind} {n : Nat} (hn : n < k.maxCap) (hmc : k.maxCap < 2 ^ 62) :
    (if Cond.holds .ult .w64 (UInt64.ofNat k.maxCap) (UInt64.ofNat (n <<< 1)) then
      UInt64.ofNat (n + 1) else
      (if Cond.holds .ugt .w64 (UInt64.ofNat (n <<< 1)) (UInt64.ofNat (n + 1)) then
        UInt64.ofNat (n <<< 1) else UInt64.ofNat (n + 1))) = UInt64.ofNat (growCap k n) := by
  have h2 : n <<< 1 = 2 * n := by rw [Nat.shiftLeft_eq]; omega
  rw [cond_ult_w64, cond_ugt_w64, u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by omega),
    u64_toNat_ofNat_lt (by omega), h2]
  unfold growCap
  simp only [decide_eq_true_eq, Nat.max_def]
  by_cases h1 : k.maxCap < 2 * n
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h3 : n + 1 < 2 * n
    · rw [if_pos h3, if_neg (by omega)]
    · rw [if_neg h3, if_pos (by omega)]

theorem ElemKind.maxCap_lt (k : ElemKind) : k.maxCap < 2 ^ 62 := by
  have := k.perWord_le
  unfold ElemKind.maxCap maxWordCap arrayHeaderWords
  rw [IxCC.Rt.Rc.maxCellWords_eq]
  have := Nat.mul_le_mul_right (2 ^ 26 - 3) this
  omega

/-- **`push`, growing**: a unique full array (size = capacity below `k.maxCap`) moves to a cell of
`growCap k n` elements with `x` appended; the old cell is recycled. -/
theorem push_grow {P : Program} {fn : FunId} {t : Fns} {k : ElemKind}
    (hfn : P.funcs[fn]? = some (push t k)) (hf : FnsOk P t k)
    {mem : Memory} {ctx base bump limit : Word} {lists : Nat → List Word}
    (halloc : ArrayAllocator mem ctx base bump limit lists) {a x : Word} {cls : Nat}
    {xs : List Word} (h : ArrCell mem a 1 cls xs.length k xs)
    (ha : Allocated base bump lists a (classBytes cls)) (hlt : xs.length < k.maxCap)
    (hx : k.Fits x) (hroom : AllocRoom bump limit lists k (growCap k xs.length)) :
    ∃ b mem' bump' lists',
      Returns1 P fn (pushEnv a x) mem ctx (xs.length + 4) b mem' ∧
      ArrCell mem' b 1 (allocClass k (growCap k xs.length))
        (k.capOfClass (allocClass k (growCap k xs.length))) k (xs ++ [x]) ∧
      ArrayAllocator mem' ctx base bump' limit (pushFree lists' cls a) ∧
      Allocated base bump' (pushFree lists' cls a) b (classBytes (allocClass k (growCap k xs.length))) ∧
      (∀ c m, Allocated base bump lists c m →
        (c.toNat + m ≤ a.toNat ∨ a.toNat + classBytes cls ≤ c.toNat) →
        Allocated base bump' (pushFree lists' cls a) c m) ∧
      MemFrame mem mem' (fun y => AllocBytes ctx lists y ∨
        CellBytes b (allocClass k (growCap k xs.length)) y ∨ CellBytes a cls y ∨
        AllocBytes ctx lists' y) := by
  obtain ⟨hg1, hg2⟩ := growCap_spec k hlt
  obtain ⟨hlo, hhi, hcap⟩ := allocClass_spec k hg2
  obtain ⟨b, m1, bump', lists', hret, hd⟩ := alloc_returns hf.alloc hf.classFor hf.classWords
    halloc hg2 hroom
  obtain ⟨hdrop, hsb, hdb, hsrc, hfit, hacc, hapart, hafter⟩ :=
    fresh_copy hd halloc hlo hhi h ha (off := 0) (n := xs.length) (by omega) (by omega)
  obtain ⟨m2, hcopy, hel2, hfr2⟩ := copy_returns hf.copy hfit hdrop hsb hdb hsrc hacc hapart
  obtain ⟨hw3, hb3, ha3, hal3, hA3, hsep, hfr3⟩ := hafter m2 hel2 hfr2
  simp only [List.drop_zero, List.take_length] at hb3
  let m3 := m2.write .w64 (b + 8) (UInt64.ofNat xs.length)
  have hroom' : xs.length < k.capOfClass (allocClass k (growCap k xs.length)) := by omega
  obtain ⟨hw4, hw5, hbnd⟩ := hb3.push_writes hroom' x
  have hb5 := hb3.pushElem hroom' hx
  let m5 := (m3.write k.width (elemAddr b k xs.length) x).write .w64 (b + 8)
    (UInt64.ofNat (xs.length + 1))
  -- the two stores are inside the fresh cell
  have hbs := hb3.shell
  have hbfit := hbs.fit
  have hb24 := hbs.classBytes_ge_24
  have hbw : k.width.bytes = k.bytes := rfl
  obtain ⟨hja, hjb⟩ := hbs.elem_toNat hroom'
  have h8 := hbs.off8
  have hfr5a : MemFrame m3 (m3.write k.width (elemAddr b k xs.length) x)
      (CellBytes b (allocClass k (growCap k xs.length))) := by
    refine (MemFrame.write m3 k.width (elemAddr b k xs.length) x (by rw [hja]; omega)).mono ?_
    intro y hy
    unfold Span at hy; rw [hja] at hy
    exact ⟨by omega, by omega⟩
  have hfr5b : MemFrame (m3.write k.width (elemAddr b k xs.length) x) m5
      (CellBytes b (allocClass k (growCap k xs.length))) := by
    refine (MemFrame.write _ .w64 (b + 8) (UInt64.ofNat (xs.length + 1))
      (by rw [h8]; simp [X86.Width.bytes]; omega)).mono ?_
    intro y hy
    unfold Span at hy; rw [h8] at hy; simp [X86.Width.bytes] at hy
    exact ⟨by omega, by omega⟩
  have hfr5 : MemFrame m3 m5 (CellBytes b (allocClass k (growCap k xs.length))) := hfr5a.trans hfr5b
  have ha5 : ArrCell m5 a 1 cls xs.length k xs := hfr5.arrCell ha3 (fun y y1 y2 hy => by
    unfold CellBytes at hy; rcases hsep with hs | hs <;> omega)
  have hal5 : ArrayAllocator m5 ctx base bump' limit lists' :=
    hal3.frame hfr5 (fun y hy => hd.allocated.not_allocBytes hal3 y hy.1 hy.2)
  -- recycle the old cell
  have has := ha5.shell
  have hc1 : 1 ≤ cls := by have := has.cls_lo; unfold minArrayClass at this; omega
  obtain ⟨hr1, hr2, hal6⟩ := hal5.push_free hc1 has.cls_hi hA3 has.aligned has.nonzero
  let m6 := recycleParent m5 ctx (UInt64.ofNat cls) a ((lists' cls).headD 0)
  have hhn := hal5.freeHead_toNat has.cls_hi
  have hcb := hal5.context_before
  have hcf := hal5.context_fit
  have hcl := hal5.context_lower
  have hch := has.cls_hi
  have hmc71 : maxClass = 71 := rfl
  have h24a := has.classBytes_ge_24
  have hafit := has.fit
  have hfr6 : MemFrame m5 m6 (fun y => CellBytes a cls y ∨ AllocBytes ctx lists' y) := by
    have f1 := MemFrame.write m5 .w64 a ((lists' cls).headD 0) (by simp [X86.Width.bytes]; omega)
    have f2 := MemFrame.write (m5.write .w64 a ((lists' cls).headD 0)) .w64
      (freeHeadAddress ctx (UInt64.ofNat cls)) a (by simp [X86.Width.bytes]; omega)
    have g1 : MemFrame m5 (m5.write .w64 a ((lists' cls).headD 0))
        (fun y => CellBytes a cls y ∨ AllocBytes ctx lists' y) := by
      refine f1.mono ?_
      intro y hy
      unfold Span at hy; simp [X86.Width.bytes] at hy
      exact Or.inl ⟨by omega, by omega⟩
    have g2 : MemFrame (m5.write .w64 a ((lists' cls).headD 0)) m6
        (fun y => CellBytes a cls y ∨ AllocBytes ctx lists' y) := by
      refine f2.mono ?_
      intro y hy
      unfold Span at hy; simp [X86.Width.bytes] at hy
      refine Or.inr (Or.inl ⟨by omega, ?_⟩)
      omega
    exact g1.trans g2
  have hb6 : ArrCell m6 b 1 _ _ k (xs ++ [x]) := hfr6.arrCell hb5 (fun y y1 y2 hy => by
    rcases hy with hy | hy
    · unfold CellBytes at hy; rcases hsep with hs | hs <;> omega
    · exact hd.allocated.not_allocBytes hal5 y y1 y2 hy)
  have hA6 : Allocated base bump' (pushFree lists' cls a) b (classBytes (allocClass k (growCap k xs.length))) := by
    refine ⟨hd.allocated.1, hd.allocated.2.1, fun c d hdm => ?_⟩
    by_cases hce : c = cls
    · subst hce
      simp only [pushFree, ite_true, List.mem_cons] at hdm
      rcases hdm with rfl | hdm
      · rcases hsep with hs | hs
        · exact Or.inl hs
        · exact Or.inr hs
      · exact hd.allocated.2.2 c d hdm
    · simp only [pushFree, hce, ite_false] at hdm; exact hd.allocated.2.2 c d hdm
  refine ⟨b, m6, bump', lists', ?_, hb6, hal6, hA6, ?_, ?_⟩
  · have hlen := h.arrRead.len_lt
    have hmc := k.maxCap_lt
    have hnlt : Cond.holds .ult .w64 (UInt64.ofNat xs.length) (UInt64.ofNat xs.length) = false := by
      rw [cond_ult_w64]; simp
    have hshl : BinOp.eval .shl .w64 (UInt64.ofNat xs.length) (UInt64.ofNat 1) =
        some (UInt64.ofNat (xs.length <<< 1)) :=
      binOp_shl64 _ 1 (by decide) (by omega) (by rw [Nat.shiftLeft_eq]; omega)
    have hgc := growCap_eval (k := k) hlt hmc
    have hcl1 : loadWord m5 .w8 .zero (a + 1) = some (UInt64.ofNat cls) := has.class_load
    have hhead : loadWord m5 .w64 .zero (freeHeadAddress ctx (UInt64.ofNat cls)) =
        some ((lists' cls).headD 0) := wordAt_load64 (hal5.free_heads cls hc1 has.cls_hi)
    refine returns1_of_star (lbl := 3) (env' := ?env) hfn rfl rfl ?ha (fun rest => ?run)
    case run =>
      unfold pushEnv
      refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (cellAddr_eval_8 (by env_lookup))
        h.shell.size_load) ?_
      refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (cellAddr_eval_16 (by env_lookup))
        h.shell.cap_load) ?_
      refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (cellAddr_eval_4 (by env_lookup))
        h.shell.count_load) ?_
      refine star_br_true_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) (by decide)
        (evalArgs_nil _) rfl rfl ?_
      refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hnlt
        (evalArgs_nil _) rfl rfl ?_
      refine star_assign hfn rfl (by body_pos) rfl (rhs_bin_eval (by arg_eval) (by arg_eval)
        (binOp_add64 xs.length 1 (by omega))) ?_
      refine star_assign hfn rfl (by body_pos) rfl (rhs_bin_eval (by arg_eval) (by arg_eval) hshl) ?_
      refine star_assign hfn rfl (by body_pos) rfl (rhs_select_eval (by arg_eval) (by arg_eval)
        (by arg_eval) (by arg_eval)) ?_
      refine star_assign hfn rfl (by body_pos) rfl (rhs_select_eval (by arg_eval) (by arg_eval)
        (by arg_eval) (by arg_eval)) ?_
      refine star_call1_eq (c' := xs.length + 1) hfn rfl (by body_pos) rfl
        (evalArgs1 (by rw [← hgc]; arg_eval)) hf.alloc rfl hret ?_ (by omega)
      refine star_call0_eq (c' := 0) hfn rfl (by body_pos) rfl
        (evalArgs5 (by arg_eval) (by arg_eval) (by arg_eval) (by arg_eval) (by arg_eval)) hf.copy rfl
        hcopy ?_ (by omega)
      refine star_store hfn rfl (by body_pos) rfl (cellAddr_eval_8 (by env_lookup)) (by arg_eval)
        hw3 ?_
      refine star_store hfn rfl (by body_pos) rfl (elemAt_eval (by env_lookup) (by env_lookup) hbnd)
        (by arg_eval) hw4 ?_
      refine star_store hfn rfl (by body_pos) rfl (cellAddr_eval_8 (by env_lookup)) (by arg_eval)
        hw5 ?_
      refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (cellAddr_eval_1 (by env_lookup))
        hcl1) ?_
      refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (headAt_eval (by env_lookup))
        hhead) ?_
      refine star_store hfn rfl (by body_pos) rfl (cellAddr0_eval (by env_lookup)) (by arg_eval)
        hr1 ?_
      refine star_store hfn rfl (by body_pos) rfl (headAt_eval (by env_lookup)) (by arg_eval) hr2 ?_
      exact .refl _
    case ha => arg_eval
  · intro c m hc hca
    obtain ⟨hc', _⟩ := hd.keeps c m hc
    refine ⟨hc'.1, hc'.2.1, fun e d hdm => ?_⟩
    by_cases hce : e = cls
    · subst hce
      simp only [pushFree, ite_true, List.mem_cons] at hdm
      rcases hdm with rfl | hdm
      · rcases hca with hs | hs
        · exact Or.inr hs
        · exact Or.inl hs
      · exact hc'.2.2 e d hdm
    · simp only [pushFree, hce, ite_false] at hdm; exact hc'.2.2 e d hdm
  · exact ((hfr3.mono (fun y hy => by
        rcases hy with hy | hy; exact Or.inl hy; exact Or.inr (Or.inl hy))).trans
      (hfr5.mono (fun y hy => Or.inr (Or.inl hy)))).trans
      (hfr6.mono (fun y hy => by
        rcases hy with hy | hy; exact Or.inr (Or.inr (Or.inl hy)); exact Or.inr (Or.inr (Or.inr hy))))

end IxCC.Rt.Rc.Array
