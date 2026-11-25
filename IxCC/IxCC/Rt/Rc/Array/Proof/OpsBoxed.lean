import IxCC.Rt.Rc.Array.Proof.OpsIncs

/-! # The copying paths on a shared boxed array, specified

A shared boxed array is copied like a packed one, after the elements it keeps are incremented by
the one increment (`Ops.incs`, `incs_returns`). The increments are the memory `IncAll` makes; their
count words lie outside the allocator's bytes and the array's cell (`hcw`), which the heap
invariant above provides.

| procedure | path | theorem | charges |
| --- | --- | --- | --- |
| `set .boxed` | shared | `set_shared_boxed` | `3n + 6` |
| `push .boxed` | shared | `push_shared_boxed` | `3n + 6` |
| `pop .boxed` | shared, non-empty | `pop_shared_boxed` | `3n + 3` |
| `extract .boxed` | live source | `extract_boxed` | `3n + 5` |

`set` returns the element it replaced as its second result (the copy's increment paid for it), to
be released by the caller. -/

set_option autoImplicit false

namespace IxCC.Rt.Rc.Array

open Lir
open IxCC.Rt.Proof (WordAt addr_toNat write?_ok wordAt_write64)
open IxCC.Rt.Rc (maxClass classBytes classWords maxCount)
open IxCC.Rt.Rc.Procs (v i to cellAddr storeCount storeCount_frame)
open IxCC.X86 (Memory)
open Ops

private theorem countFrame' {mem : Memory} {a : Word} (hfit : a.toNat + 8 ≤ 2 ^ 64) (c : Word) :
    MemFrame mem (storeCount mem a c) (CountWord a) := by
  have hf := storeCount_frame mem a c hfit
  exact ⟨hf.readable, hf.writable, fun x hx => hf.outside x (by unfold CountWord at hx; omega)⟩

/-- The increments of the elements of `a`: the allocator and the cell kept, the call specified. -/
theorem incs_keep {P : Program} {t : Fns} (hf : FnsOk P t .boxed)
    {mem mem0 : Memory} {ctx base bump limit : Word} {lists : Nat → List Word}
    (halloc : ArrayAllocator mem ctx base bump limit lists) {a : Word} {refs cls cap : Nat}
    {xs : List Word} (h : ArrCell mem a refs cls cap .boxed xs) (hincs : IncAll mem xs mem0)
    (hptr : ∀ y ∈ xs, Cond.holds .tnz .w64 y 1 = false → y.toNat + 8 ≤ 2 ^ 64)
    (hcw : ∀ y, CountWords xs y → ¬ AllocBytes ctx lists y ∧ ¬ CellBytes a cls y) :
    MemFrame mem mem0 (CountWords xs) ∧ ArrCell mem0 a refs cls cap .boxed xs ∧
      ArrayAllocator mem0 ctx base bump limit lists ∧
      Returns0 P t.incs (incsEnv a 0 xs.length) mem ctx (2 * xs.length) mem0 := by
  have hs := h.shell
  have hfit := hs.fit
  have hp := hs.payload_le
  have hm := Nat.mul_le_mul_left ElemKind.boxed.bytes hs.size_le
  have hb8 : ElemKind.boxed.bytes = 8 := rfl
  have hfr0 : MemFrame mem mem0 (CountWords xs) := hincs.frame hptr
  refine ⟨hfr0, hfr0.arrCell h (fun y y1 y2 hy => (hcw y hy).2 ⟨y1, y2⟩),
    halloc.frame hfr0 (fun y hy => (hcw y hy).1), ?_⟩
  have := incs_returns (ctx := ctx) hf.incs hf.inc (lo := 0) (ys := xs)
    (by rw [Nat.zero_add]; rw [hb8] at hp hm; omega) h.elems.elemsAt hincs hptr
    (fun y hy hr => (hcw y hy).2 ⟨by
        obtain ⟨r1, _⟩ := hr; unfold arrayPayloadOffset at r1; omega, by
        obtain ⟨_, r2⟩ := hr; rw [Nat.zero_add] at r2; rw [hb8] at hp hm r2
        unfold arrayPayloadOffset at hp r2; omega⟩)
  simpa only [Nat.zero_add] using this

theorem set_shared_boxed {P : Program} {fn : FunId} {t : Fns}
    (hfn : P.funcs[fn]? = some (set t .boxed)) (hf : FnsOk P t .boxed)
    {mem : Memory} {ctx base bump limit : Word} {lists : Nat → List Word}
    (halloc : ArrayAllocator mem ctx base bump limit lists) {a x : Word} {refs cls cap : Nat}
    {xs : List Word} (h : ArrCell mem a refs cls cap .boxed xs) (hsh : 1 < refs)
    (ha : Allocated base bump lists a (classBytes cls)) {j : Nat} (hj : j < xs.length)
    (hroom : AllocRoom bump limit lists .boxed xs.length) {mem0 : Memory}
    (hincs : IncAll mem xs mem0)
    (hptr : ∀ y ∈ xs, Cond.holds .tnz .w64 y 1 = false → y.toNat + 8 ≤ 2 ^ 64)
    (hcw : ∀ y, CountWords xs y → ¬ AllocBytes ctx lists y ∧ ¬ CellBytes a cls y) :
    ∃ b mem' bump' lists',
      Returns2 P fn (setEnv a j x) mem ctx (3 * xs.length + 6) b xs[j] mem' ∧
      ArrCell mem' b 1 (allocClass .boxed xs.length)
        (ElemKind.boxed.capOfClass (allocClass .boxed xs.length)) .boxed (xs.set j x) ∧
      ArrCell mem' a (refs - 1) cls cap .boxed xs ∧
      ArrayAllocator mem' ctx base bump' limit lists' ∧
      Allocated base bump' lists' b (classBytes (allocClass .boxed xs.length)) ∧
      Allocated base bump' lists' a (classBytes cls) ∧
      (∀ c m, Allocated base bump lists c m → Allocated base bump' lists' c m) ∧
      MemFrame mem mem' (fun y => AllocBytes ctx lists y ∨
        CellBytes b (allocClass .boxed xs.length) y ∨ CountWord a y ∨ CountWords xs y) := by
  obtain ⟨hfr0, h0, halloc0, hincsR⟩ := incs_keep hf halloc h hincs hptr hcw
  have hn := h.len_le_maxCap
  obtain ⟨hlo, hhi, hcap⟩ := allocClass_spec .boxed hn
  obtain ⟨b, m1, bump', lists', hret, hd⟩ := alloc_returns hf.alloc hf.classFor hf.classWords
    halloc0 hn hroom
  obtain ⟨hdrop, hsb, hdb, hsrc, hfit, hacc, hapart, hafter⟩ :=
    fresh_copy hd halloc0 hlo hhi h0 ha (off := 0) (n := xs.length) (by omega) hcap
  obtain ⟨m2, hcopy, hel2, hfr2⟩ := copy_returns hf.copy hfit hdrop hsb hdb hsrc hacc hapart
  obtain ⟨hw3, hb3, ha3, hal3, hA3, hsep, hfr3⟩ := hafter m2 hel2 hfr2
  simp only [List.drop_zero, List.take_length] at hb3
  let m3 := m2.write .w64 (b + 8) (UInt64.ofNat xs.length)
  -- the store into the copy
  have hbs := hb3.shell
  have hbfit := hbs.fit
  obtain ⟨hja, hjb⟩ := hbs.elem_toNat (j := j) (by have := hbs.size_le; omega)
  have hbw : ElemKind.boxed.width.bytes = ElemKind.boxed.bytes := rfl
  have hbw2 : X86.Width.w64.bytes = ElemKind.boxed.bytes := rfl
  have hpl := hbs.payload_le
  have hcp := Nat.mul_le_mul_left ElemKind.boxed.bytes hbs.size_le
  have hwj : m3.write? .w64 (elemAddr b .boxed j) x = .ok (m3.write .w64 (elemAddr b .boxed j) x) :=
    write?_ok (fun c hc => by
      have := hbs.access (arrayPayloadOffset + ElemKind.boxed.bytes * j + c) (by
        omega)
      have hadd : elemAddr b .boxed j + UInt64.ofNat c =
          b + UInt64.ofNat (arrayPayloadOffset + ElemKind.boxed.bytes * j + c) := by
        apply UInt64.toNat_inj.mp
        rw [addr_toNat (by rw [hja]; omega), hja, addr_toNat (by omega)]; omega
      rw [hadd]; exact this.2)
  let m4 := m3.write .w64 (elemAddr b .boxed j) x
  have hfw4 := MemFrame.write m3 .w64 (elemAddr b .boxed j) x (by rw [hja]; omega)
  have hb4 : ArrCell m4 b 1 _ _ .boxed (xs.set j x) := hb3.setElem hj (ElemKind.boxed_fits x)
  have ha4 : ArrCell m4 a refs cls cap .boxed xs := hfw4.arrCell ha3 (fun y y1 y2 hy => by
    unfold Span at hy; rw [hja] at hy; rcases hsep with hs | hs <;> omega)
  -- the release of the old array
  have ha24 := ha4.shell.classBytes_ge_24
  have hafit := ha4.shell.fit
  obtain ⟨hdec, hsh5⟩ := ha4.shell.decArr_returns_shared hf.dec hsh ctx
  let m5 := storeCount m4 a (UInt64.ofNat (refs - 2))
  have hfr5 : MemFrame m4 m5 (CountWord a) := countFrame' (by omega) _
  have ha5 : ArrCell m5 a (refs - 1) cls cap .boxed xs := by
    have := ha4.withCount (refs' := refs - 1) (by omega) (by have := ha4.shell.refs_le; omega)
    rwa [show refs - 1 - 1 = refs - 2 by omega] at this
  have hb5 : ArrCell m5 b 1 _ _ .boxed (xs.set j x) := hfr5.arrCell hb4 (fun y y1 y2 hy => by
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
    refine returns2_of_star (lbl := 4) (env' := ?env) hfn rfl rfl ?ha ?hb (fun rest => ?run)
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
      refine star_call0_eq (c' := xs.length + 5) hfn rfl (by body_pos) rfl
        (evalArgs3 (by arg_eval) (by arg_eval) (by arg_eval)) hf.incs rfl hincsR ?_ (by omega)
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
    case hb => arg_eval
  · refine (hfr0.mono (fun y hy => Or.inr (Or.inr (Or.inr hy)))).trans ?_
    refine (hfr3.mono (fun y hy => by rcases hy with hy | hy; exact Or.inl hy; exact Or.inr (Or.inl hy))).trans
      ((hfw4.mono (fun y hy => Or.inr (Or.inl ?_))).trans (hfr5.mono (fun y hy => Or.inr (Or.inr (Or.inl hy)))))
    unfold Span at hy; rw [hja] at hy
    exact ⟨by omega, by omega⟩


/-- **`push`, copying**: a shared boxed array below the largest capacity; the elements kept are
incremented first. -/
theorem push_shared_boxed {P : Program} {fn : FunId} {t : Fns}
    (hfn : P.funcs[fn]? = some (push t .boxed)) (hf : FnsOk P t .boxed)
    {mem : Memory} {ctx base bump limit : Word} {lists : Nat → List Word}
    (halloc : ArrayAllocator mem ctx base bump limit lists) {a x : Word} {refs cls cap : Nat}
    {xs : List Word} (h : ArrCell mem a refs cls cap .boxed xs) (hsh : 1 < refs)
    (ha : Allocated base bump lists a (classBytes cls)) (hlt : xs.length < ElemKind.boxed.maxCap)
    (hroom : AllocRoom bump limit lists .boxed (xs.length + 1)) {mem0 : Memory}
    (hincs : IncAll mem xs mem0)
    (hptr : ∀ y ∈ xs, Cond.holds .tnz .w64 y 1 = false → y.toNat + 8 ≤ 2 ^ 64)
    (hcw : ∀ y, CountWords xs y → ¬ AllocBytes ctx lists y ∧ ¬ CellBytes a cls y) :
    ∃ b mem' bump' lists',
      Returns1 P fn (pushEnv a x) mem ctx (3 * xs.length + 6) b mem' ∧
      ArrCell mem' b 1 (allocClass .boxed (xs.length + 1))
        (ElemKind.boxed.capOfClass (allocClass .boxed (xs.length + 1))) .boxed
        (xs ++ [x]) ∧
      ArrCell mem' a (refs - 1) cls cap .boxed xs ∧
      ArrayAllocator mem' ctx base bump' limit lists' ∧
      Allocated base bump' lists' b (classBytes (allocClass .boxed (xs.length + 1))) ∧
      Allocated base bump' lists' a (classBytes cls) ∧
      (∀ c m, Allocated base bump lists c m → Allocated base bump' lists' c m) ∧
      MemFrame mem mem' (fun y => AllocBytes ctx lists y ∨
        CellBytes b (allocClass .boxed (xs.length + 1)) y ∨ CountWord a y ∨ CountWords xs y) := by
  obtain ⟨hfr0, h0, halloc0, hincsR⟩ := incs_keep hf halloc h hincs hptr hcw
  have hn : xs.length + 1 ≤ ElemKind.boxed.maxCap := by omega
  obtain ⟨hlo, hhi, hcap⟩ := allocClass_spec .boxed hn
  obtain ⟨b, m1, bump', lists', hret, hd⟩ := alloc_returns hf.alloc hf.classFor hf.classWords
    halloc0 hn hroom
  obtain ⟨hdrop, hsb, hdb, hsrc, hfit, hacc, hapart, hafter⟩ :=
    fresh_copy hd halloc0 hlo hhi h0 ha (off := 0) (n := xs.length) (by omega) (by omega)
  obtain ⟨m2, hcopy, hel2, hfr2⟩ := copy_returns hf.copy hfit hdrop hsb hdb hsrc hacc hapart
  obtain ⟨hw3, hb3, ha3, hal3, hA3, hsep, hfr3⟩ := hafter m2 hel2 hfr2
  simp only [List.drop_zero, List.take_length] at hb3
  let m3 := m2.write .w64 (b + 8) (UInt64.ofNat xs.length)
  have hroom' : xs.length < ElemKind.boxed.capOfClass (allocClass .boxed (xs.length + 1)) := by
    omega
  obtain ⟨hw4, hw5, hbnd⟩ := hb3.push_writes hroom' x
  have hb5 := hb3.pushElem hroom' (ElemKind.boxed_fits x)
  let m5 := (m3.write .w64 (elemAddr b .boxed xs.length) x).write .w64 (b + 8)
    (UInt64.ofNat (xs.length + 1))
  have hbs := hb3.shell
  have hbfit := hbs.fit
  have hb24 := hbs.classBytes_ge_24
  have hbw2 : X86.Width.w64.bytes = ElemKind.boxed.bytes := rfl
  obtain ⟨hja, hjb⟩ := hbs.elem_toNat hroom'
  have h8 := hbs.off8
  have hfr5a : MemFrame m3 (m3.write .w64 (elemAddr b .boxed xs.length) x)
      (CellBytes b (allocClass .boxed (xs.length + 1))) := by
    refine (MemFrame.write m3 .w64 (elemAddr b .boxed xs.length) x (by rw [hja]; omega)).mono ?_
    intro y hy
    unfold Span at hy; rw [hja] at hy
    exact ⟨by omega, by omega⟩
  have hfr5b : MemFrame (m3.write .w64 (elemAddr b .boxed xs.length) x) m5
      (CellBytes b (allocClass .boxed (xs.length + 1))) := by
    refine (MemFrame.write _ .w64 (b + 8) (UInt64.ofNat (xs.length + 1))
      (by rw [h8]; simp [X86.Width.bytes]; omega)).mono ?_
    intro y hy
    unfold Span at hy; rw [h8] at hy; simp [X86.Width.bytes] at hy
    exact ⟨by omega, by omega⟩
  have hfr5 := hfr5a.trans hfr5b
  have ha5 : ArrCell m5 a refs cls cap .boxed xs := hfr5.arrCell ha3 (fun y y1 y2 hy => by
    unfold CellBytes at hy; rcases hsep with hs | hs <;> omega)
  have hal5 : ArrayAllocator m5 ctx base bump' limit lists' :=
    hal3.frame hfr5 (fun y hy => hd.allocated.not_allocBytes hal3 y hy.1 hy.2)
  have ha24 := ha5.shell.classBytes_ge_24
  have hafit := ha5.shell.fit
  obtain ⟨hdec, _⟩ := ha5.shell.decArr_returns_shared hf.dec hsh ctx
  let m6 := storeCount m5 a (UInt64.ofNat (refs - 2))
  have hfr6 : MemFrame m5 m6 (CountWord a) := countFrame' (by omega) _
  have ha6 : ArrCell m6 a (refs - 1) cls cap .boxed xs := by
    have := ha5.withCount (refs' := refs - 1) (by omega) (by have := ha5.shell.refs_le; omega)
    rwa [show refs - 1 - 1 = refs - 2 by omega] at this
  have hb6 : ArrCell m6 b 1 _ _ .boxed (xs ++ [x]) := hfr6.arrCell hb5 (fun y y1 y2 hy => by
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
      refine star_call0_eq (c' := xs.length + 5) hfn rfl (by body_pos) rfl
        (evalArgs3 (by arg_eval) (by arg_eval) (by arg_eval)) hf.incs rfl hincsR ?_ (by omega)
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
  · refine (hfr0.mono (fun y hy => Or.inr (Or.inr (Or.inr hy)))).trans ?_
    exact ((hfr3.mono (fun y hy => by
        rcases hy with hy | hy; exact Or.inl hy; exact Or.inr (Or.inl hy))).trans
      (hfr5.mono (fun y hy => Or.inr (Or.inl hy)))).trans (hfr6.mono (fun y hy => Or.inr (Or.inr (Or.inl hy))))


/-- The increments of the first `n` elements of `a`. -/
theorem incs_keep_take {P : Program} {t : Fns} (hf : FnsOk P t .boxed)
    {mem mem0 : Memory} {ctx base bump limit : Word} {lists : Nat → List Word}
    (halloc : ArrayAllocator mem ctx base bump limit lists) {a : Word} {refs cls cap : Nat}
    {xs : List Word} (h : ArrCell mem a refs cls cap .boxed xs) {n : Nat} (hn : n ≤ xs.length)
    (hincs : IncAll mem (xs.take n) mem0)
    (hptr : ∀ y ∈ xs.take n, Cond.holds .tnz .w64 y 1 = false → y.toNat + 8 ≤ 2 ^ 64)
    (hcw : ∀ y, CountWords (xs.take n) y → ¬ AllocBytes ctx lists y ∧ ¬ CellBytes a cls y) :
    MemFrame mem mem0 (CountWords (xs.take n)) ∧ ArrCell mem0 a refs cls cap .boxed xs ∧
      ArrayAllocator mem0 ctx base bump limit lists ∧
      Returns0 P t.incs (incsEnv a 0 n) mem ctx (2 * n) mem0 := by
  have hs := h.shell
  have hfit := hs.fit
  have hp := hs.payload_le
  have hm := Nat.mul_le_mul_left ElemKind.boxed.bytes (show n ≤ cap by have := hs.size_le; omega)
  have hb8 : ElemKind.boxed.bytes = 8 := rfl
  have hlen : (xs.take n).length = n := by simp; omega
  have hfr0 : MemFrame mem mem0 (CountWords (xs.take n)) := hincs.frame hptr
  refine ⟨hfr0, hfr0.arrCell h (fun y y1 y2 hy => (hcw y hy).2 ⟨y1, y2⟩),
    halloc.frame hfr0 (fun y hy => (hcw y hy).1), ?_⟩
  have hel : ElemsAt mem a .boxed 0 (xs.take n) := by
    intro j hj
    rw [List.getElem_take, Nat.zero_add]
    exact h.elems j (by simp at hj; omega)
  have := incs_returns (ctx := ctx) hf.incs hf.inc (lo := 0) (ys := xs.take n)
    (by rw [hlen, Nat.zero_add]; rw [hb8] at hp hm; omega) hel hincs hptr
    (fun y hy hr => (hcw y hy).2 ⟨by
        obtain ⟨r1, _⟩ := hr; unfold arrayPayloadOffset at r1; omega, by
        obtain ⟨_, r2⟩ := hr; rw [hlen, Nat.zero_add] at r2; rw [hb8] at hp hm r2
        unfold arrayPayloadOffset at hp r2; omega⟩)
  simpa only [Nat.zero_add, hlen] using this

/-- **`pop`, copying**: a shared non-empty boxed array; the elements kept are incremented first,
and there is nothing to drop (the second result is an immediate). -/
theorem pop_shared_boxed {P : Program} {fn : FunId} {t : Fns}
    (hfn : P.funcs[fn]? = some (pop t .boxed)) (hf : FnsOk P t .boxed)
    {mem : Memory} {ctx base bump limit : Word} {lists : Nat → List Word}
    (halloc : ArrayAllocator mem ctx base bump limit lists) {a : Word} {refs cls cap : Nat}
    {xs : List Word} (h : ArrCell mem a refs cls cap .boxed xs) (hsh : 1 < refs)
    (ha : Allocated base bump lists a (classBytes cls)) (hne : xs ≠ [])
    (hroom : AllocRoom bump limit lists .boxed (xs.length - 1)) {mem0 : Memory}
    (hincs : IncAll mem (xs.take (xs.length - 1)) mem0)
    (hptr : ∀ y ∈ xs.take (xs.length - 1), Cond.holds .tnz .w64 y 1 = false → y.toNat + 8 ≤ 2 ^ 64)
    (hcw : ∀ y, CountWords (xs.take (xs.length - 1)) y → ¬ AllocBytes ctx lists y ∧
      ¬ CellBytes a cls y) :
    ∃ b mem' bump' lists',
      Returns2 P fn (({} : Env).insert 0 a) mem ctx (3 * xs.length + 3) b 1 mem' ∧
      ArrCell mem' b 1 (allocClass .boxed (xs.length - 1))
        (ElemKind.boxed.capOfClass (allocClass .boxed (xs.length - 1))) .boxed
        xs.dropLast ∧
      ArrCell mem' a (refs - 1) cls cap .boxed xs ∧
      ArrayAllocator mem' ctx base bump' limit lists' ∧
      Allocated base bump' lists' b (classBytes (allocClass .boxed (xs.length - 1))) ∧
      Allocated base bump' lists' a (classBytes cls) ∧
      (∀ c m, Allocated base bump lists c m → Allocated base bump' lists' c m) ∧
      MemFrame mem mem' (fun y => AllocBytes ctx lists y ∨
        CellBytes b (allocClass .boxed (xs.length - 1)) y ∨ CountWord a y ∨
        CountWords (xs.take (xs.length - 1)) y) := by
  obtain ⟨hfr0, h0, halloc0, hincsR⟩ := incs_keep_take hf halloc h (Nat.sub_le _ _) hincs hptr hcw
  have hpos : 0 < xs.length := List.length_pos_iff.mpr hne
  have hn : xs.length - 1 ≤ ElemKind.boxed.maxCap := by have := h.len_le_maxCap; omega
  obtain ⟨hlo, hhi, hcap⟩ := allocClass_spec .boxed hn
  obtain ⟨b, m1, bump', lists', hret, hd⟩ := alloc_returns hf.alloc hf.classFor hf.classWords
    halloc0 hn hroom
  obtain ⟨hdrop, hsb, hdb, hsrc, hfit, hacc, hapart, hafter⟩ :=
    fresh_copy hd halloc0 hlo hhi h0 ha (off := 0) (n := xs.length - 1) (by omega) hcap
  obtain ⟨m2, hcopy, hel2, hfr2⟩ := copy_returns hf.copy hfit hdrop hsb hdb hsrc hacc hapart
  obtain ⟨hw3, hb3, ha3, hal3, hA3, hsep, hfr3⟩ := hafter m2 hel2 hfr2
  simp only [List.drop_zero, ← List.dropLast_eq_take] at hb3
  let m3 := m2.write .w64 (b + 8) (UInt64.ofNat (xs.length - 1))
  have ha24 := ha3.shell.classBytes_ge_24
  have hafit := ha3.shell.fit
  obtain ⟨hdec, _⟩ := ha3.shell.decArr_returns_shared hf.dec hsh ctx
  let m4 := storeCount m3 a (UInt64.ofNat (refs - 2))
  have hfr4 : MemFrame m3 m4 (CountWord a) := countFrame' (by omega) _
  have ha4 : ArrCell m4 a (refs - 1) cls cap .boxed xs := by
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
    refine returns2_of_star (lbl := 5) (env' := ?env) hfn rfl rfl ?ha ?hb (fun rest => ?run)
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
      refine star_call0_eq (c' := xs.length + 4) hfn rfl (by body_pos) rfl
        (evalArgs3 (by arg_eval) (by arg_eval) (by arg_eval)) hf.incs rfl hincsR ?_ (by omega)
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
    case hb => arg_eval
  · refine (hfr0.mono (fun y hy => Or.inr (Or.inr (Or.inr hy)))).trans ?_
    exact (hfr3.mono (fun y hy => by
        rcases hy with hy | hy; exact Or.inl hy; exact Or.inr (Or.inl hy))).trans
      (hfr4.mono (fun y hy => Or.inr (Or.inr (Or.inl hy))))


/-- The increments of the elements `s ..< s + n` of `a`. -/
theorem incs_keep_range {P : Program} {t : Fns} (hf : FnsOk P t .boxed)
    {mem mem0 : Memory} {ctx base bump limit : Word} {lists : Nat → List Word}
    (halloc : ArrayAllocator mem ctx base bump limit lists) {a : Word} {refs cls cap : Nat}
    {xs : List Word} (h : ArrCell mem a refs cls cap .boxed xs) {s n : Nat} (hn : s + n ≤ xs.length)
    (hincs : IncAll mem ((xs.drop s).take n) mem0)
    (hptr : ∀ y ∈ (xs.drop s).take n, Cond.holds .tnz .w64 y 1 = false → y.toNat + 8 ≤ 2 ^ 64)
    (hcw : ∀ y, CountWords ((xs.drop s).take n) y → ¬ AllocBytes ctx lists y ∧ ¬ CellBytes a cls y) :
    MemFrame mem mem0 (CountWords ((xs.drop s).take n)) ∧ ArrCell mem0 a refs cls cap .boxed xs ∧
      ArrayAllocator mem0 ctx base bump limit lists ∧
      Returns0 P t.incs (incsEnv a s (s + n)) mem ctx (2 * n) mem0 := by
  have hs := h.shell
  have hfit := hs.fit
  have hp := hs.payload_le
  have hm := Nat.mul_le_mul_left ElemKind.boxed.bytes (show s + n ≤ cap by have := hs.size_le; omega)
  have hb8 : ElemKind.boxed.bytes = 8 := rfl
  have hlen : ((xs.drop s).take n).length = n := by simp; omega
  have hfr0 : MemFrame mem mem0 (CountWords ((xs.drop s).take n)) := hincs.frame hptr
  refine ⟨hfr0, hfr0.arrCell h (fun y y1 y2 hy => (hcw y hy).2 ⟨y1, y2⟩),
    halloc.frame hfr0 (fun y hy => (hcw y hy).1), ?_⟩
  have hel : ElemsAt mem a .boxed s ((xs.drop s).take n) := by
    intro j hj
    rw [List.getElem_take, List.getElem_drop]
    exact h.elems (s + j) (by simp at hj; omega)
  have := incs_returns (ctx := ctx) hf.incs hf.inc (lo := s) (ys := (xs.drop s).take n)
    (by rw [hlen]; rw [hb8] at hp hm; omega) hel hincs hptr
    (fun y hy hr => (hcw y hy).2 ⟨by
        obtain ⟨r1, _⟩ := hr; unfold arrayPayloadOffset at r1; omega, by
        obtain ⟨_, r2⟩ := hr; rw [hlen] at r2; rw [hb8] at hp hm r2
        unfold arrayPayloadOffset at hp r2; omega⟩)
  simpa only [hlen] using this

/-- **`extract`** of a live boxed array: a fresh array of the run, whose elements are incremented
first; the source is read, not released. -/
theorem extract_boxed {P : Program} {fn : FunId} {t : Fns}
    (hfn : P.funcs[fn]? = some (extract t .boxed)) (hf : FnsOk P t .boxed)
    {mem : Memory} {ctx base bump limit : Word} {lists : Nat → List Word}
    (halloc : ArrayAllocator mem ctx base bump limit lists) {a : Word} {refs cls cap : Nat}
    {xs : List Word} (h : ArrCell mem a refs cls cap .boxed xs)
    (ha : Allocated base bump lists a (classBytes cls)) {start stop : Nat}
    (hs64 : start < 2 ^ 64) (ht64 : stop < 2 ^ 64)
    (hroom : AllocRoom bump limit lists .boxed (extractLen xs.length start stop)) {mem0 : Memory}
    (hincs : IncAll mem (IxCC.Src.ArraySpec.extractList xs start stop) mem0)
    (hptr : ∀ y ∈ IxCC.Src.ArraySpec.extractList xs start stop, Cond.holds .tnz .w64 y 1 = false →
      y.toNat + 8 ≤ 2 ^ 64)
    (hcw : ∀ y, CountWords (IxCC.Src.ArraySpec.extractList xs start stop) y →
      ¬ AllocBytes ctx lists y ∧ ¬ CellBytes a cls y) :
    ∃ b mem' bump' lists',
      Returns1 P fn (extractEnv a start stop) mem ctx (3 * extractLen xs.length start stop + 5) b
        mem' ∧
      ArrCell mem' b 1 (allocClass .boxed (extractLen xs.length start stop))
        (ElemKind.boxed.capOfClass (allocClass .boxed (extractLen xs.length start stop)))
        .boxed (IxCC.Src.ArraySpec.extractList xs start stop) ∧
      ArrCell mem' a refs cls cap .boxed xs ∧
      ArrayAllocator mem' ctx base bump' limit lists' ∧
      Allocated base bump' lists' b (classBytes (allocClass .boxed (extractLen xs.length start stop))) ∧
      Allocated base bump' lists' a (classBytes cls) ∧
      (∀ c m, Allocated base bump lists c m → Allocated base bump' lists' c m) ∧
      MemFrame mem mem' (fun y => AllocBytes ctx lists y ∨
        CellBytes b (allocClass .boxed (extractLen xs.length start stop)) y ∨
        CountWords (IxCC.Src.ArraySpec.extractList xs start stop) y) := by
  have hlen := h.arrRead.len_lt
  have hmaxc := h.len_le_maxCap
  have hle : extractStart xs.length start stop + extractLen xs.length start stop ≤ xs.length := by
    unfold extractStart extractLen; split <;> omega
  have hn : extractLen xs.length start stop ≤ ElemKind.boxed.maxCap := by omega
  rw [extractList_eq] at hincs hptr hcw ⊢
  obtain ⟨hfr0, h0, halloc0, hincsR⟩ := incs_keep_range hf halloc h hle hincs hptr hcw
  obtain ⟨hlo, hhi, hcap⟩ := allocClass_spec .boxed hn
  obtain ⟨b, m1, bump', lists', hret, hd⟩ := alloc_returns hf.alloc hf.classFor hf.classWords
    halloc0 hn hroom
  obtain ⟨hdrop, hsb, hdb, hsrc, hfit, hacc, hapart, hafter⟩ :=
    fresh_copy hd halloc0 hlo hhi h0 ha (off := extractStart xs.length start stop)
      (n := extractLen xs.length start stop) hle hcap
  obtain ⟨m2, hcopy, hel2, hfr2⟩ := copy_returns hf.copy hfit hdrop hsb hdb hsrc hacc hapart
  obtain ⟨hw3, hb3, ha3, hal3, hA3, hsep, hfr3⟩ := hafter m2 hel2 hfr2
  have hb3e := hb3
  refine ⟨b, _, bump', lists', ?_, hb3, ha3, hal3, hd.allocated, hA3,
    fun c m hc => (hd.keeps c m hc).1,
    (hfr0.mono (fun y hy => Or.inr (Or.inr hy))).trans (hfr3.mono (fun y hy => by
      rcases hy with hy | hy; exact Or.inl hy; exact Or.inr (Or.inl hy)))⟩
  -- the arithmetic of block 0
  have hm : (if Cond.holds .ult .w64 (UInt64.ofNat stop) (UInt64.ofNat xs.length) then
      UInt64.ofNat stop else UInt64.ofNat xs.length) = UInt64.ofNat (min stop xs.length) := by
    rw [cond_ult_w64, u64_toNat_ofNat_lt ht64, u64_toNat_ofNat_lt (by omega)]
    by_cases hc : stop < xs.length
    · simp only [decide_eq_true_eq, hc, ↓reduceIte, Nat.min_eq_left (Nat.le_of_lt hc)]
    · simp only [decide_eq_true_eq, hc, ↓reduceIte, Nat.min_eq_right (Nat.le_of_not_lt hc)]
  have hmlt : min stop xs.length < 2 ^ 64 := by omega
  have hsub : BinOp.eval .sub .w64 (UInt64.ofNat (min stop xs.length)) (UInt64.ofNat start) =
      some (UInt64.ofNat (min stop xs.length) - UInt64.ofNat start) := by
    simp only [BinOp.eval, w64_trunc]
  have hl : (if Cond.holds .ult .w64 (UInt64.ofNat start) (UInt64.ofNat (min stop xs.length)) then
      UInt64.ofNat (min stop xs.length) - UInt64.ofNat start else UInt64.ofNat 0) =
      UInt64.ofNat (extractLen xs.length start stop) := by
    rw [cond_ult_w64, u64_toNat_ofNat_lt hs64, u64_toNat_ofNat_lt hmlt]
    unfold extractLen
    by_cases hc : start < min stop xs.length
    · simp only [decide_eq_true_eq, hc, ↓reduceIte, u64_sub_ofNat (Nat.le_of_lt hc) hmlt]
    · simp only [decide_eq_true_eq, hc, ↓reduceIte]
  have hst : (if Cond.holds .ult .w64 (UInt64.ofNat start) (UInt64.ofNat (min stop xs.length)) then
      UInt64.ofNat start else UInt64.ofNat 0) = UInt64.ofNat (extractStart xs.length start stop) := by
    rw [cond_ult_w64, u64_toNat_ofNat_lt hs64, u64_toNat_ofNat_lt hmlt]
    unfold extractStart
    by_cases hc : start < min stop xs.length
    · simp only [decide_eq_true_eq, hc, ↓reduceIte]
    · simp only [decide_eq_true_eq, hc, ↓reduceIte]
  refine returns1_of_star (lbl := 2) (env' := ?env) hfn rfl rfl ?ha (fun rest => ?run)
  case run =>
    unfold extractEnv
    refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (cellAddr_eval_8 (by env_lookup))
      h.shell.size_load) ?_
    refine star_assign (val := UInt64.ofNat (min stop xs.length)) hfn rfl (by body_pos) rfl (by
      rw [rhs_select_eval (by arg_eval) (by arg_eval) (by arg_eval) (by arg_eval)]
      exact congrArg some hm) ?_
    refine star_assign hfn rfl (by body_pos) rfl (rhs_bin_eval (by arg_eval) (by arg_eval) hsub) ?_
    refine star_assign (val := UInt64.ofNat (extractLen xs.length start stop)) hfn rfl (by body_pos)
      rfl (by
      rw [rhs_select_eval (by arg_eval) (by arg_eval) (by arg_eval) (by arg_eval)]
      exact congrArg some hl) ?_
    refine star_assign (val := UInt64.ofNat (extractStart xs.length start stop)) hfn rfl
      (by body_pos) rfl (by
      rw [rhs_select_eval (by arg_eval) (by arg_eval) (by arg_eval) (by arg_eval)]
      exact congrArg some hst) ?_
    refine star_assign hfn rfl (by body_pos) rfl (rhs_bin_eval (by arg_eval) (by arg_eval)
      (binOp_add64 (extractStart xs.length start stop) (extractLen xs.length start stop)
        (by omega))) ?_
    refine star_jump_fwd hfn rfl rfl rfl rfl (evalArgs_nil _) rfl rfl ?_
    refine star_call0_eq (c' := extractLen xs.length start stop + 4) hfn rfl (by body_pos) rfl
      (evalArgs3 (by arg_eval) (by arg_eval) (by arg_eval)) hf.incs rfl hincsR ?_ (by omega)
    refine star_jump_fwd hfn rfl rfl rfl rfl (evalArgs_nil _) rfl rfl ?_
    refine star_call1_eq (c' := extractLen xs.length start stop + 1) hfn rfl (by body_pos) rfl
      (evalArgs1 (by arg_eval)) hf.alloc rfl hret ?_ (by omega)
    refine star_call0_eq (c' := 0) hfn rfl (by body_pos) rfl
      (evalArgs5 (by arg_eval) (by arg_eval) (by arg_eval) (by arg_eval) (by arg_eval)) hf.copy rfl
      hcopy ?_ (by omega)
    refine star_store hfn rfl (by body_pos) rfl (cellAddr_eval_8 (by env_lookup)) (by arg_eval)
      hw3 ?_
    exact .refl _
  case ha => arg_eval

end IxCC.Rt.Rc.Array
