import IxCC.Rt.Rc.Array.Proof.OpsGrow

/-! # The copying paths of `push` and `pop` on a shared packed array, specified

| procedure | path | theorem | charges |
| --- | --- | --- | --- |
| `push (.packed w)` | shared | `push_shared_packed` | `n + 5` |
| `pop (.packed w)` | shared, non-empty | `pop_shared_packed` | `n + 4` |

As `set_shared_packed`: the fresh cell, the old array with one reference fewer, the allocator
kept, the cells allocated, and the frame. -/

set_option autoImplicit false

namespace IxCC.Rt.Rc.Array

open Lir
open IxCC.Rt.Proof (WordAt addr_toNat write?_ok wordAt_write64)
open IxCC.Rt.Rc (maxClass classBytes classWords maxCount)
open IxCC.Rt.Rc.Procs (v i to cellAddr storeCount storeCount_frame)
open IxCC.X86 (Memory)
open Ops

private theorem countFrame {mem : Memory} {a : Word} (hfit : a.toNat + 8 ≤ 2 ^ 64) (c : Word) :
    MemFrame mem (storeCount mem a c) (CountWord a) := by
  have hf := storeCount_frame mem a c hfit
  exact ⟨hf.readable, hf.writable, fun x hx => hf.outside x (by unfold CountWord at hx; omega)⟩

/-- **`push`, copying**: a shared packed array below the largest capacity. -/
theorem push_shared_packed {P : Program} {fn : FunId} {t : Fns} {w : X86.Width}
    (hfn : P.funcs[fn]? = some (push t (.packed w))) (hf : FnsOk P t (.packed w))
    {mem : Memory} {ctx base bump limit : Word} {lists : Nat → List Word}
    (halloc : ArrayAllocator mem ctx base bump limit lists) {a x : Word} {refs cls cap : Nat}
    {xs : List Word} (h : ArrCell mem a refs cls cap (.packed w) xs) (hsh : 1 < refs)
    (ha : Allocated base bump lists a (classBytes cls)) (hlt : xs.length < (ElemKind.packed w).maxCap)
    (hx : (ElemKind.packed w).Fits x)
    (hroom : AllocRoom bump limit lists (.packed w) (xs.length + 1)) :
    ∃ b mem' bump' lists',
      Returns1 P fn (pushEnv a x) mem ctx (xs.length + 5) b mem' ∧
      ArrCell mem' b 1 (allocClass (.packed w) (xs.length + 1))
        ((ElemKind.packed w).capOfClass (allocClass (.packed w) (xs.length + 1))) (.packed w)
        (xs ++ [x]) ∧
      ArrCell mem' a (refs - 1) cls cap (.packed w) xs ∧
      ArrayAllocator mem' ctx base bump' limit lists' ∧
      Allocated base bump' lists' b (classBytes (allocClass (.packed w) (xs.length + 1))) ∧
      Allocated base bump' lists' a (classBytes cls) ∧
      (∀ c m, Allocated base bump lists c m → Allocated base bump' lists' c m) ∧
      MemFrame mem mem' (fun y => AllocBytes ctx lists y ∨
        CellBytes b (allocClass (.packed w) (xs.length + 1)) y ∨ CountWord a y) := by
  have hn : xs.length + 1 ≤ (ElemKind.packed w).maxCap := by omega
  obtain ⟨hlo, hhi, hcap⟩ := allocClass_spec (.packed w) hn
  obtain ⟨b, m1, bump', lists', hret, hd⟩ := alloc_returns hf.alloc hf.classFor hf.classWords
    halloc hn hroom
  obtain ⟨hdrop, hsb, hdb, hsrc, hfit, hacc, hapart, hafter⟩ :=
    fresh_copy hd halloc hlo hhi h ha (off := 0) (n := xs.length) (by omega) (by omega)
  obtain ⟨m2, hcopy, hel2, hfr2⟩ := copy_returns hf.copy hfit hdrop hsb hdb hsrc hacc hapart
  obtain ⟨hw3, hb3, ha3, hal3, hA3, hsep, hfr3⟩ := hafter m2 hel2 hfr2
  simp only [List.drop_zero, List.take_length] at hb3
  let m3 := m2.write .w64 (b + 8) (UInt64.ofNat xs.length)
  have hroom' : xs.length < (ElemKind.packed w).capOfClass (allocClass (.packed w) (xs.length + 1)) := by
    omega
  obtain ⟨hw4, hw5, hbnd⟩ := hb3.push_writes hroom' x
  have hb5 := hb3.pushElem hroom' hx
  let m5 := (m3.write w (elemAddr b (.packed w) xs.length) x).write .w64 (b + 8)
    (UInt64.ofNat (xs.length + 1))
  have hbs := hb3.shell
  have hbfit := hbs.fit
  have hb24 := hbs.classBytes_ge_24
  have hbw2 : w.bytes = (ElemKind.packed w).bytes := rfl
  obtain ⟨hja, hjb⟩ := hbs.elem_toNat hroom'
  have h8 := hbs.off8
  have hfr5a : MemFrame m3 (m3.write w (elemAddr b (.packed w) xs.length) x)
      (CellBytes b (allocClass (.packed w) (xs.length + 1))) := by
    refine (MemFrame.write m3 w (elemAddr b (.packed w) xs.length) x (by rw [hja]; omega)).mono ?_
    intro y hy
    unfold Span at hy; rw [hja] at hy
    exact ⟨by omega, by omega⟩
  have hfr5b : MemFrame (m3.write w (elemAddr b (.packed w) xs.length) x) m5
      (CellBytes b (allocClass (.packed w) (xs.length + 1))) := by
    refine (MemFrame.write _ .w64 (b + 8) (UInt64.ofNat (xs.length + 1))
      (by rw [h8]; simp [X86.Width.bytes]; omega)).mono ?_
    intro y hy
    unfold Span at hy; rw [h8] at hy; simp [X86.Width.bytes] at hy
    exact ⟨by omega, by omega⟩
  have hfr5 := hfr5a.trans hfr5b
  have ha5 : ArrCell m5 a refs cls cap (.packed w) xs := hfr5.arrCell ha3 (fun y y1 y2 hy => by
    unfold CellBytes at hy; rcases hsep with hs | hs <;> omega)
  have hal5 : ArrayAllocator m5 ctx base bump' limit lists' :=
    hal3.frame hfr5 (fun y hy => hd.allocated.not_allocBytes hal3 y hy.1 hy.2)
  have ha24 := ha5.shell.classBytes_ge_24
  have hafit := ha5.shell.fit
  obtain ⟨hdec, _⟩ := ha5.shell.decArr_returns_shared hf.dec hsh ctx
  let m6 := storeCount m5 a (UInt64.ofNat (refs - 2))
  have hfr6 : MemFrame m5 m6 (CountWord a) := countFrame (by omega) _
  have ha6 : ArrCell m6 a (refs - 1) cls cap (.packed w) xs := by
    have := ha5.withCount (refs' := refs - 1) (by omega) (by have := ha5.shell.refs_le; omega)
    rwa [show refs - 1 - 1 = refs - 2 by omega] at this
  have hb6 : ArrCell m6 b 1 _ _ (.packed w) (xs ++ [x]) := hfr6.arrCell hb5 (fun y y1 y2 hy => by
    unfold CountWord at hy; rcases hsep with hs | hs <;> omega)
  have hal6 : ArrayAllocator m6 ctx base bump' limit lists' :=
    hal5.frame hfr6 (fun y hy => by unfold CountWord at hy; exact hA3.not_allocBytes hal5 y (by omega) (by omega))
  refine ⟨b, m6, bump', lists', ?_, hb6, ha6, hal6, hd.allocated, hA3,
    fun c m hc => (hd.keeps c m hc).1, ?_⟩
  · have hmax := h.shell.refs_le
    unfold maxCount at hmax
    have hne : Cond.holds .eq .w32 (UInt64.ofNat (refs - 1)) (UInt64.ofNat 0) = false := by
      rw [cond_eq_ofNat .w32 (by show refs - 1 < 2 ^ 32; omega) (by decide)]; simp; omega
    have hlen := h.arrRead.len_lt
    refine returns1_of_star (lbl := 5) (env' := ?env) hfn rfl rfl ?ha (fun rest => ?run)
    case run =>
      unfold pushEnv
      refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (cellAddr_eval_8 (by env_lookup))
        h.shell.size_load) ?_
      refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (cellAddr_eval_16 (by env_lookup))
        h.shell.cap_load) ?_
      refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (cellAddr_eval_4 (by env_lookup))
        h.shell.count_load) ?_
      refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hne
        (evalArgs_nil _) rfl rfl ?_
      refine star_jump_fwd hfn rfl rfl rfl rfl (evalArgs_nil _) rfl rfl ?_
      refine star_assign hfn rfl (by body_pos) rfl (rhs_bin_eval (by arg_eval) (by arg_eval)
        (binOp_add64 xs.length 1 (by omega))) ?_
      refine star_call1_eq (c' := xs.length + 2) hfn rfl (by body_pos) rfl
        (evalArgs1 (by arg_eval)) hf.alloc rfl hret ?_ (by omega)
      refine star_call0_eq (c' := 1) hfn rfl (by body_pos) rfl
        (evalArgs5 (by arg_eval) (by arg_eval) (by arg_eval) (by arg_eval) (by arg_eval)) hf.copy rfl
        hcopy ?_ (by omega)
      refine star_store hfn rfl (by body_pos) rfl (cellAddr_eval_8 (by env_lookup)) (by arg_eval)
        hw3 ?_
      refine star_store hfn rfl (by body_pos) rfl (elemAt_eval (by env_lookup) (by env_lookup) hbnd)
        (by arg_eval) hw4 ?_
      refine star_store hfn rfl (by body_pos) rfl (cellAddr_eval_8 (by env_lookup)) (by arg_eval)
        hw5 ?_
      refine star_call0_eq (c' := 0) hfn rfl (by body_pos) rfl (evalArgs1 (by arg_eval)) hf.dec rfl
        hdec ?_ rfl
      exact .refl _
    case ha => arg_eval
  · exact ((hfr3.mono (fun y hy => by
        rcases hy with hy | hy; exact Or.inl hy; exact Or.inr (Or.inl hy))).trans
      (hfr5.mono (fun y hy => Or.inr (Or.inl hy)))).trans (hfr6.mono (fun y hy => Or.inr (Or.inr hy)))

/-- **`pop`, copying**: a shared non-empty packed array; the copy keeps all but the last. -/
theorem pop_shared_packed {P : Program} {fn : FunId} {t : Fns} {w : X86.Width}
    (hfn : P.funcs[fn]? = some (pop t (.packed w))) (hf : FnsOk P t (.packed w))
    {mem : Memory} {ctx base bump limit : Word} {lists : Nat → List Word}
    (halloc : ArrayAllocator mem ctx base bump limit lists) {a : Word} {refs cls cap : Nat}
    {xs : List Word} (h : ArrCell mem a refs cls cap (.packed w) xs) (hsh : 1 < refs)
    (ha : Allocated base bump lists a (classBytes cls)) (hne : xs ≠ [])
    (hroom : AllocRoom bump limit lists (.packed w) (xs.length - 1)) :
    ∃ b mem' bump' lists',
      Returns1 P fn (({} : Env).insert 0 a) mem ctx (xs.length + 4) b mem' ∧
      ArrCell mem' b 1 (allocClass (.packed w) (xs.length - 1))
        ((ElemKind.packed w).capOfClass (allocClass (.packed w) (xs.length - 1))) (.packed w)
        xs.dropLast ∧
      ArrCell mem' a (refs - 1) cls cap (.packed w) xs ∧
      ArrayAllocator mem' ctx base bump' limit lists' ∧
      Allocated base bump' lists' b (classBytes (allocClass (.packed w) (xs.length - 1))) ∧
      Allocated base bump' lists' a (classBytes cls) ∧
      (∀ c m, Allocated base bump lists c m → Allocated base bump' lists' c m) ∧
      MemFrame mem mem' (fun y => AllocBytes ctx lists y ∨
        CellBytes b (allocClass (.packed w) (xs.length - 1)) y ∨ CountWord a y) := by
  have hpos : 0 < xs.length := List.length_pos_iff.mpr hne
  have hn : xs.length - 1 ≤ (ElemKind.packed w).maxCap := by have := h.len_le_maxCap; omega
  obtain ⟨hlo, hhi, hcap⟩ := allocClass_spec (.packed w) hn
  obtain ⟨b, m1, bump', lists', hret, hd⟩ := alloc_returns hf.alloc hf.classFor hf.classWords
    halloc hn hroom
  obtain ⟨hdrop, hsb, hdb, hsrc, hfit, hacc, hapart, hafter⟩ :=
    fresh_copy hd halloc hlo hhi h ha (off := 0) (n := xs.length - 1) (by omega) hcap
  obtain ⟨m2, hcopy, hel2, hfr2⟩ := copy_returns hf.copy hfit hdrop hsb hdb hsrc hacc hapart
  obtain ⟨hw3, hb3, ha3, hal3, hA3, hsep, hfr3⟩ := hafter m2 hel2 hfr2
  simp only [List.drop_zero, ← List.dropLast_eq_take] at hb3
  let m3 := m2.write .w64 (b + 8) (UInt64.ofNat (xs.length - 1))
  have ha24 := ha3.shell.classBytes_ge_24
  have hafit := ha3.shell.fit
  obtain ⟨hdec, _⟩ := ha3.shell.decArr_returns_shared hf.dec hsh ctx
  let m4 := storeCount m3 a (UInt64.ofNat (refs - 2))
  have hfr4 : MemFrame m3 m4 (CountWord a) := countFrame (by omega) _
  have ha4 : ArrCell m4 a (refs - 1) cls cap (.packed w) xs := by
    have := ha3.withCount (refs' := refs - 1) (by omega) (by have := ha3.shell.refs_le; omega)
    rwa [show refs - 1 - 1 = refs - 2 by omega] at this
  have hb4 := hfr4.arrCell hb3 (fun y y1 y2 hy => by
    unfold CountWord at hy; rcases hsep with hs | hs <;> omega)
  have hal4 : ArrayAllocator m4 ctx base bump' limit lists' :=
    hal3.frame hfr4 (fun y hy => by unfold CountWord at hy; exact hA3.not_allocBytes hal3 y (by omega) (by omega))
  refine ⟨b, m4, bump', lists', ?_, hb4, ha4, hal4, hd.allocated, hA3,
    fun c m hc => (hd.keeps c m hc).1, ?_⟩
  · have hmax := h.shell.refs_le
    unfold maxCount at hmax
    have hne' : Cond.holds .eq .w32 (UInt64.ofNat (refs - 1)) (UInt64.ofNat 0) = false := by
      rw [cond_eq_ofNat .w32 (by show refs - 1 < 2 ^ 32; omega) (by decide)]; simp; omega
    have hlen := h.arrRead.len_lt
    have hnz : Cond.holds .eq .w64 (UInt64.ofNat xs.length) (UInt64.ofNat 0) = false := by
      rw [cond_eq_w64]
      exact beq_false_of_ne (fun hq => by
        have := congrArg UInt64.toNat hq
        rw [u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by decide)] at this; omega)
    refine returns1_of_star (lbl := 5) (env' := ?env) hfn rfl rfl ?ha (fun rest => ?run)
    case run =>
      refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (cellAddr_eval_8 (by env_lookup))
        h.shell.size_load) ?_
      refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hnz
        (evalArgs_nil _) rfl rfl ?_
      refine star_assign hfn rfl (by body_pos) rfl (rhs_bin_eval (by arg_eval) (by arg_eval)
        (binOp_sub64 xs.length 1 (by omega) (by omega))) ?_
      refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (cellAddr_eval_4 (by env_lookup))
        h.shell.count_load) ?_
      refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hne'
        (evalArgs_nil _) rfl rfl ?_
      refine star_jump_fwd hfn rfl rfl rfl rfl (evalArgs_nil _) rfl rfl ?_
      refine star_call1_eq (c' := xs.length - 1 + 2) hfn rfl (by body_pos) rfl
        (evalArgs1 (by arg_eval)) hf.alloc rfl hret ?_ (by omega)
      refine star_call0_eq (c' := 1) hfn rfl (by body_pos) rfl
        (evalArgs5 (by arg_eval) (by arg_eval) (by arg_eval) (by arg_eval) (by arg_eval)) hf.copy rfl
        hcopy ?_ (by omega)
      refine star_store hfn rfl (by body_pos) rfl (cellAddr_eval_8 (by env_lookup)) (by arg_eval)
        hw3 ?_
      refine star_call0_eq (c' := 0) hfn rfl (by body_pos) rfl (evalArgs1 (by arg_eval)) hf.dec rfl
        hdec ?_ rfl
      exact .refl _
    case ha => arg_eval
  · exact (hfr3.mono (fun y hy => by
        rcases hy with hy | hy; exact Or.inl hy; exact Or.inr (Or.inl hy))).trans
      (hfr4.mono (fun y hy => Or.inr (Or.inr hy)))

end IxCC.Rt.Rc.Array
