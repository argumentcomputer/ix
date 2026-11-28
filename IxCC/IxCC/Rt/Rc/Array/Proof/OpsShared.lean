import IxCC.Rt.Rc.Array.Proof.OpsFresh

/-! # The copying paths, specified

A packed array that is shared (more than one reference) is never written: `set`, `push` and
`pop` copy it into a fresh cell, update the copy, and release the old array by the one release,
which only lowers its count (`ArrShell.decArr_returns_shared`). `extract` copies a run of any
live array and leaves the source alone. In any program that holds the procedure at `fn` and its
callees where `t` says (`FnsOk`), and whose allocation request is met (`AllocRoom`):

| procedure | path | theorem | charges |
| --- | --- | --- | --- |
| `set (.packed w)` | shared | `set_shared_packed` | `n + 5` |

Each concludes: the fresh cell with its elements, the old array with one reference fewer and its
elements, the allocator kept, both cells allocated, every other allocated cell still allocated,
and memory changed only in the allocator's bytes, the fresh cell and the old array's count word. -/

set_option autoImplicit false

namespace IxCC.Rt.Rc.Array

open Lir
open IxCC.Rt.Proof (WordAt addr_toNat write?_ok wordAt_write64)
open IxCC.Rt.Rc (maxClass classBytes classWords maxCount)
open IxCC.Rt.Rc.Procs (v i to cellAddr storeCount storeCount_frame)
open IxCC.X86 (Memory)
open Ops

/-- The count word of the cell at `a`. -/
def CountWord (a : Word) : Nat → Prop := fun x => a.toNat + 4 ≤ x ∧ x < a.toNat + 8

theorem ArrCell.len_le_maxCap {mem : Memory} {a : Word} {refs cls cap : Nat} {k : ElemKind}
    {xs : List Word} (h : ArrCell mem a refs cls cap k xs) : xs.length ≤ k.maxCap :=
  Nat.le_trans h.shell.size_le (Nat.le_trans h.shell.cap_fit (k.capOfClass_le_maxCap h.shell.cls_hi))

/-- The count store of a release keeps a cell elsewhere, and the allocator. -/
private theorem storeCount_frame' {mem : Memory} {a : Word} (hfit : a.toNat + 8 ≤ 2 ^ 64) (c : Word) :
    MemFrame mem (storeCount mem a c) (CountWord a) := by
  have hf := storeCount_frame mem a c hfit
  exact ⟨hf.readable, hf.writable, fun x hx => hf.outside x (by unfold CountWord at hx; omega)⟩

/-- **`set`, copying**: a shared packed array, in range. -/
theorem set_shared_packed {P : Program} {fn : FunId} {t : Fns} {w : X86.Width}
    (hfn : P.funcs[fn]? = some (set t (.packed w))) (hf : FnsOk P t (.packed w))
    {mem : Memory} {ctx base bump limit : Word} {lists : Nat → List Word}
    (halloc : ArrayAllocator mem ctx base bump limit lists) {a x : Word} {refs cls cap : Nat}
    {xs : List Word} (h : ArrCell mem a refs cls cap (.packed w) xs) (hsh : 1 < refs)
    (ha : Allocated base bump lists a (classBytes cls)) {j : Nat} (hj : j < xs.length)
    (hx : (ElemKind.packed w).Fits x) (hroom : AllocRoom bump limit lists (.packed w) xs.length) :
    ∃ b mem' bump' lists',
      Returns1 P fn (setEnv a j x) mem ctx (xs.length + 5) b mem' ∧
      ArrCell mem' b 1 (allocClass (.packed w) xs.length)
        ((ElemKind.packed w).capOfClass (allocClass (.packed w) xs.length)) (.packed w) (xs.set j x) ∧
      ArrCell mem' a (refs - 1) cls cap (.packed w) xs ∧
      ArrayAllocator mem' ctx base bump' limit lists' ∧
      Allocated base bump' lists' b (classBytes (allocClass (.packed w) xs.length)) ∧
      Allocated base bump' lists' a (classBytes cls) ∧
      (∀ c m, Allocated base bump lists c m → Allocated base bump' lists' c m) ∧
      MemFrame mem mem' (fun y => AllocBytes ctx lists y ∨
        CellBytes b (allocClass (.packed w) xs.length) y ∨ CountWord a y) := by
  have hn := h.len_le_maxCap
  obtain ⟨hlo, hhi, hcap⟩ := allocClass_spec (.packed w) hn
  obtain ⟨b, m1, bump', lists', hret, hd⟩ := alloc_returns hf.alloc hf.classFor hf.classWords
    halloc hn hroom
  obtain ⟨hdrop, hsb, hdb, hsrc, hfit, hacc, hapart, hafter⟩ :=
    fresh_copy hd halloc hlo hhi h ha (off := 0) (n := xs.length) (by omega) hcap
  obtain ⟨m2, hcopy, hel2, hfr2⟩ := copy_returns hf.copy hfit hdrop hsb hdb hsrc hacc hapart
  obtain ⟨hw3, hb3, ha3, hal3, hA3, hsep, hfr3⟩ := hafter m2 hel2 hfr2
  simp only [List.drop_zero, List.take_length] at hb3
  let m3 := m2.write .w64 (b + 8) (UInt64.ofNat xs.length)
  -- the store into the copy
  have hbs := hb3.shell
  have hbfit := hbs.fit
  obtain ⟨hja, hjb⟩ := hbs.elem_toNat (j := j) (by have := hbs.size_le; omega)
  have hbw : (ElemKind.packed w).width.bytes = (ElemKind.packed w).bytes := rfl
  have hbw2 : w.bytes = (ElemKind.packed w).bytes := rfl
  have hpl := hbs.payload_le
  have hcp := Nat.mul_le_mul_left (ElemKind.packed w).bytes hbs.size_le
  have hwj : m3.write? w (elemAddr b (.packed w) j) x = .ok (m3.write w (elemAddr b (.packed w) j) x) :=
    write?_ok (fun c hc => by
      have := hbs.access (arrayPayloadOffset + (ElemKind.packed w).bytes * j + c) (by
        omega)
      have hadd : elemAddr b (.packed w) j + UInt64.ofNat c =
          b + UInt64.ofNat (arrayPayloadOffset + (ElemKind.packed w).bytes * j + c) := by
        apply UInt64.toNat_inj.mp
        rw [addr_toNat (by rw [hja]; omega), hja, addr_toNat (by omega)]; omega
      rw [hadd]; exact this.2)
  let m4 := m3.write w (elemAddr b (.packed w) j) x
  have hfw4 := MemFrame.write m3 w (elemAddr b (.packed w) j) x (by rw [hja]; omega)
  have hb4 : ArrCell m4 b 1 _ _ (.packed w) (xs.set j x) := hb3.setElem hj hx
  have ha4 : ArrCell m4 a refs cls cap (.packed w) xs := hfw4.arrCell ha3 (fun y y1 y2 hy => by
    unfold Span at hy; rw [hja] at hy; rcases hsep with hs | hs <;> omega)
  -- the release of the old array
  have ha24 := ha4.shell.classBytes_ge_24
  have hafit := ha4.shell.fit
  obtain ⟨hdec, hsh5⟩ := ha4.shell.decArr_returns_shared hf.dec hsh ctx
  let m5 := storeCount m4 a (UInt64.ofNat (refs - 2))
  have hfr5 : MemFrame m4 m5 (CountWord a) := storeCount_frame' (by omega) _
  have ha5 : ArrCell m5 a (refs - 1) cls cap (.packed w) xs := by
    have := ha4.withCount (refs' := refs - 1) (by omega) (by have := ha4.shell.refs_le; omega)
    rwa [show refs - 1 - 1 = refs - 2 by omega] at this
  have hb5 : ArrCell m5 b 1 _ _ (.packed w) (xs.set j x) := hfr5.arrCell hb4 (fun y y1 y2 hy => by
    unfold CountWord at hy; rcases hsep with hs | hs <;> omega)
  have hal5 : ArrayAllocator m5 ctx base bump' limit lists' :=
    (hal3.frame hfw4 (fun y hy => by
        unfold Span at hy; rw [hja] at hy
        exact hd.allocated.not_allocBytes hal3 y (by omega) (by omega))).frame hfr5
      (fun y hy => by unfold CountWord at hy; exact hA3.not_allocBytes hal3 y (by omega) (by omega))
  refine ⟨b, m5, bump', lists', ?_, hb5, ha5, hal5, hd.allocated, hA3,
    fun c m hc => (hd.keeps c m hc).1, ?_⟩
  · have hlen := h.arrRead.len_lt
    have hlt : Cond.holds .ult .w64 (UInt64.ofNat j) (UInt64.ofNat xs.length) = true := by
      rw [cond_ult_w64, u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by omega)]
      exact decide_eq_true hj
    have hmax := h.shell.refs_le
    unfold maxCount at hmax
    have hne : Cond.holds .eq .w32 (UInt64.ofNat (refs - 1)) (UInt64.ofNat 0) = false := by
      rw [cond_eq_ofNat .w32 (by show refs - 1 < 2 ^ 32; omega) (by decide)]; simp; omega
    have hbj := hb3.arrRead.elem_bound hj
    refine returns1_of_star (lbl := 4) (env' := ?env) hfn rfl rfl ?ha (fun rest => ?run)
    case run =>
      unfold setEnv
      refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (cellAddr_eval_8 (by env_lookup))
        h.shell.size_load) ?_
      refine star_br_true_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hlt
        (evalArgs_nil _) rfl rfl ?_
      refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (cellAddr_eval_4 (by env_lookup))
        h.shell.count_load) ?_
      refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hne
        (evalArgs_nil _) rfl rfl ?_
      refine star_jump_fwd hfn rfl rfl rfl rfl (evalArgs_nil _) rfl rfl ?_
      refine star_call1_eq (c' := xs.length + 2) hfn rfl (by body_pos) rfl
        (evalArgs1 (by arg_eval)) hf.alloc rfl hret ?_ (by omega)
      refine star_call0_eq (c' := 1) hfn rfl (by body_pos) rfl
        (evalArgs5 (by arg_eval) (by arg_eval) (by arg_eval) (by arg_eval) (by arg_eval)) hf.copy rfl
        hcopy ?_ (by omega)
      refine star_store hfn rfl (by body_pos) rfl (cellAddr_eval_8 (by env_lookup)) (by arg_eval)
        hw3 ?_
      refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (elemAt_eval (by env_lookup)
        (by env_lookup) hbj) (hb3.elem_load hj)) ?_
      refine star_store hfn rfl (by body_pos) rfl (elemAt_eval (by env_lookup) (by env_lookup) hbj)
        (by arg_eval) hwj ?_
      refine star_call0_eq (c' := 0) hfn rfl (by body_pos) rfl (evalArgs1 (by arg_eval)) hf.dec rfl
        hdec ?_ rfl
      exact .refl _
    case ha => arg_eval
  · refine (hfr3.mono (fun y hy => by rcases hy with hy | hy; exact Or.inl hy; exact Or.inr (Or.inl hy))).trans
      ((hfw4.mono (fun y hy => Or.inr (Or.inl ?_))).trans (hfr5.mono (fun y hy => Or.inr (Or.inr hy))))
    unfold Span at hy; rw [hja] at hy
    exact ⟨by omega, by omega⟩

end IxCC.Rt.Rc.Array
