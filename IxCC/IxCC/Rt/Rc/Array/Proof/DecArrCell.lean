import IxCC.Rt.Rc.Array.Proof.DecArr
import IxCC.Rt.Rc.Array.Proof.Allocator

/-! # The one release on array cells, as returns

`Gen.decArr`'s paths that close over the array invariant alone, each a `Returns0` in any program
that holds `decArr` at `fn`, from the step theorems of `DecArr`:

| value | theorem | charges | memory after |
| --- | --- | --- | --- |
| an immediate | `decArr_returns_immediate` | 0 | unchanged |
| a static cell (negative count) | `decArr_returns_static`, `StaticArrCell.decArr_returns` | 0 | unchanged |
| a shared array cell | `ArrShell.decArr_returns_shared` | 0 | count word lowered |
| the last reference of a packed array | `ArrShell.decArr_returns_packed` | 1 | recycled |
| the last reference of an empty boxed array | `ArrShell.decArr_returns_boxed_empty` | 2 | recycled |
| the last reference of a boxed array of immediates | `ArrCell.decArr_returns_immediates` | `n + 1` | recycled |

A recycled cell is pushed on its class's free list and the allocator is kept
(`ArrayAllocator.push_free`). The release of a boxed array whose elements are cells is the
release of those cells in turn; its theorem needs the heap invariant that says what the elements
are, which is the bridge to the abstract heap, not here (the step theorems of `DecArr` cover
every edge it takes). -/

set_option autoImplicit false

namespace IxCC.Rt.Rc.Array

open Lir
open IxCC.Rt.Proof (WordAt addr_toNat write?_ok wordAt_write64)
open IxCC.Rt.Rc (maxClass classBytes maxCount)
open IxCC.Rt.Rc.Gen (decArr arrayScan)
open IxCC.Rt.Rc.Procs (v i to cellAddr FreeChain freeHeadAddress storeCount countAddress
  recycleParent recycled_head storeCount_frame)
open IxCC.X86 (Memory)

/-! ## Word arithmetic at a width -/

theorem cond_eq_ofNat (w : X86.Width) {a b : Nat} (ha : a < 2 ^ w.bits) (hb : b < 2 ^ w.bits) :
    Cond.holds .eq w (UInt64.ofNat a) (UInt64.ofNat b) = decide (a = b) := by
  have hw : w.bits ≤ 64 := by cases w <;> decide
  have h64 : 2 ^ w.bits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw
  simp only [Cond.holds, truncate_of_lt (show (UInt64.ofNat a).toNat < 2 ^ w.bits by
      rw [u64_toNat_ofNat_lt (by omega)]; exact ha),
    truncate_of_lt (show (UInt64.ofNat b).toNat < 2 ^ w.bits by
      rw [u64_toNat_ofNat_lt (by omega)]; exact hb)]
  by_cases hab : a = b
  · subst hab; simp
  · have : UInt64.ofNat a ≠ UInt64.ofNat b := fun h => by
      have := congrArg UInt64.toNat h
      rw [u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by omega)] at this
      exact hab this
    simp [hab, this]

theorem binOp_sub_ofNat (w : X86.Width) {a b : Nat} (hba : b ≤ a) (ha : a < 2 ^ w.bits) :
    BinOp.eval .sub w (UInt64.ofNat a) (UInt64.ofNat b) = some (UInt64.ofNat (a - b)) := by
  have hw : w.bits ≤ 64 := by cases w <;> decide
  have h64 : 2 ^ w.bits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw
  simp only [BinOp.eval, u64_sub_ofNat hba (by omega)]
  rw [truncate_of_lt (by rw [u64_toNat_ofNat_lt (by omega)]; omega)]

theorem binOp_add_ofNat (w : X86.Width) {a b : Nat} (hab : a + b < 2 ^ w.bits) :
    BinOp.eval .add w (UInt64.ofNat a) (UInt64.ofNat b) = some (UInt64.ofNat (a + b)) := by
  have hw : w.bits ≤ 64 := by cases w <;> decide
  have h64 : 2 ^ w.bits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw
  simp only [BinOp.eval, u64_add_ofNat (a := a) (b := b) (by omega)]
  rw [truncate_of_lt (by rw [u64_toNat_ofNat_lt (by omega)]; omega)]

/-! ## Values that need no write -/

/-- An immediate: nothing is read or written. -/
theorem decArr_returns_immediate {P : Program} {fn : FunId} (hfn : P.funcs[fn]? = some decArr)
    (mem : Memory) (ctx : Word) {x : Word} (hx : x &&& 1 = 1) :
    Returns0 P fn (decArrEnv x) mem ctx 0 mem := by
  intro caller callers hd
  obtain ⟨e, he1, he2, h0⟩ := decArr_entry hfn mem ctx x (caller :: callers)
  obtain ⟨e', he8, h1⟩ := decArr_step_immediate hfn he1 he2 hx (caller :: callers)
  have h2 := decArr_step_finish hfn (mem := mem) (context := ctx) he8 (caller :: callers)
  exact (h0.trans (h1.trans (h2.trans (decArr_ret hfn mem ctx e' callers hd))))

/-- A cell whose count word is negative (static, immortal): one read, no write. -/
theorem decArr_returns_static {P : Program} {fn : FunId} (hfn : P.funcs[fn]? = some decArr)
    (mem : Memory) (ctx : Word) {x cnt : Word} (hptr : Cond.holds .tnz .w64 x 1 = false)
    (hcnt : loadWord mem .w32 .zero (x + 4) = some cnt) (hneg : Cond.holds .slt .w32 cnt 0 = true) :
    Returns0 P fn (decArrEnv x) mem ctx 0 mem := by
  intro caller callers hd
  obtain ⟨e, he1, he2, h0⟩ := decArr_entry hfn mem ctx x (caller :: callers)
  obtain ⟨e', he8, h1⟩ := decArr_step_static hfn he1 he2 hptr hcnt hneg (caller :: callers)
  have h2 := decArr_step_finish hfn (mem := mem) (context := ctx) he8 (caller :: callers)
  exact (h0.trans (h1.trans (h2.trans (decArr_ret hfn mem ctx e' callers hd))))

/-- A static array cell is left alone. -/
theorem StaticArrCell.decArr_returns {P : Program} {fn : FunId} (hfn : P.funcs[fn]? = some decArr)
    {mem : Memory} {x : Word} {cap : Nat} {k : ElemKind} {xs : List Word}
    (h : StaticArrCell mem x cap k xs) (ctx : Word) :
    Returns0 P fn (decArrEnv x) mem ctx 0 mem :=
  decArr_returns_static hfn mem ctx h.pointer_branch h.count_load immortal_slt_zero

/-- A shared array cell: its count word is lowered; the cell keeps everything else. -/
theorem ArrShell.decArr_returns_shared {P : Program} {fn : FunId}
    (hfn : P.funcs[fn]? = some decArr) {mem : Memory} {x : Word} {refs cls cap : Nat}
    {k : ElemKind} {size : Nat} (h : ArrShell mem x refs cls cap k size) (hsh : 1 < refs)
    (ctx : Word) :
    Returns0 P fn (decArrEnv x) mem ctx 0 (storeCount mem x (UInt64.ofNat (refs - 2))) ∧
      ArrShell (storeCount mem x (UInt64.ofNat (refs - 2))) x (refs - 1) cls cap k size := by
  have hmax := h.refs_le
  unfold maxCount at hmax
  have hb32 : (2 : Nat) ^ X86.Width.w32.bits = 2 ^ 32 := rfl
  have hne : Cond.holds .eq .w32 (UInt64.ofNat (refs - 1)) (UInt64.ofNat 0) = false := by
    rw [cond_eq_ofNat .w32 (by rw [hb32]; omega) (by rw [hb32]; omega)]; simp; omega
  have hsub : BinOp.eval .sub .w32 (UInt64.ofNat (refs - 1)) (UInt64.ofNat 1) =
      some (UInt64.ofNat (refs - 2)) := by
    rw [binOp_sub_ofNat .w32 (by omega) (by rw [hb32]; omega)]; congr 2
  have h24 := h.classBytes_ge_24
  have hwr : mem.write? .w32 (x + 4) (UInt64.ofNat (refs - 2)) =
      .ok (storeCount mem x (UInt64.ofNat (refs - 2))) := h.write_ok (by simp [X86.Width.bytes]; omega) _
  refine ⟨fun caller callers hd => ?_, ?_⟩
  · obtain ⟨e, he1, he2, h0⟩ := decArr_entry hfn mem ctx x (caller :: callers)
    obtain ⟨e', he8, h1⟩ := decArr_step_shared hfn he1 he2 h.pointer_branch h.count_load
      h.rc_not_slt_zero hne hsub hwr (caller :: callers)
    have h2 := decArr_step_finish hfn (mem := storeCount mem x (UInt64.ofNat (refs - 2)))
      (context := ctx) he8 (caller :: callers)
    exact (h0.trans (h1.trans (h2.trans (decArr_ret hfn _ ctx e' callers hd))))
  · have := h.withCount (refs' := refs - 1) (by omega) (by unfold maxCount; omega)
    rwa [show refs - 1 - 1 = refs - 2 by omega] at this

/-! ## The last reference: recycling -/

/-- The loads and stores of recycling `x`, from the allocator and the cell. -/
private theorem recycle_facts {mem : Memory} {ctx base bump limit : Word}
    {lists : Nat → List Word} (halloc : ArrayAllocator mem ctx base bump limit lists)
    {x : Word} {cls cap : Nat} {k : ElemKind} {size : Nat} (h : ArrShell mem x 1 cls cap k size)
    (ha : Allocated base bump lists x (classBytes cls)) :
    loadWord mem .w64 .zero (freeHeadAddress ctx (UInt64.ofNat cls)) = some ((lists cls).headD 0) ∧
    mem.write? .w64 x ((lists cls).headD 0) = .ok (mem.write .w64 x ((lists cls).headD 0)) ∧
    (mem.write .w64 x ((lists cls).headD 0)).write? .w64 (freeHeadAddress ctx (UInt64.ofNat cls)) x =
      .ok (recycleParent mem ctx (UInt64.ofNat cls) x ((lists cls).headD 0)) ∧
    ArrayAllocator (recycleParent mem ctx (UInt64.ofNat cls) x ((lists cls).headD 0)) ctx base bump
      limit (pushFree lists cls x) := by
  have hc1 : 1 ≤ cls := by have := h.cls_lo; unfold minArrayClass at this; omega
  obtain ⟨hw1, hw2, hal⟩ := halloc.push_free hc1 h.cls_hi ha h.aligned h.nonzero
  exact ⟨wordAt_load64 (halloc.free_heads cls hc1 h.cls_hi), hw1, hw2, hal⟩

/-- The last reference of a packed array: recycled at once. -/
theorem ArrShell.decArr_returns_packed {P : Program} {fn : FunId}
    (hfn : P.funcs[fn]? = some decArr) {mem : Memory} {ctx base bump limit : Word}
    {lists : Nat → List Word} {x : Word} {cls cap : Nat} {w : X86.Width} {size : Nat}
    (h : ArrShell mem x 1 cls cap (.packed w) size)
    (halloc : ArrayAllocator mem ctx base bump limit lists)
    (ha : Allocated base bump lists x (classBytes cls)) :
    Returns0 P fn (decArrEnv x) mem ctx 1
        (recycleParent mem ctx (UInt64.ofNat cls) x ((lists cls).headD 0)) ∧
      ArrayAllocator (recycleParent mem ctx (UInt64.ofNat cls) x ((lists cls).headD 0)) ctx base
        bump limit (pushFree lists cls x) := by
  obtain ⟨hhead, hw1, hw2, hal⟩ := recycle_facts halloc h ha
  refine ⟨fun caller callers hd => ?_, hal⟩
  obtain ⟨e, he1, he2, h0⟩ := decArr_entry hfn mem ctx x (caller :: callers)
  have hscan := h.scan_load
  simp only [ElemKind.packed_scan] at hscan
  obtain ⟨e', he8, h1⟩ := decArr_step_leaf hfn he1 he2 h.pointer_branch h.count_load
    h.rc_not_slt_zero (by decide) hscan (by decide) h.class_load hhead hw1 hw2 (caller :: callers)
  have h2 := decArr_step_finish hfn (mem := recycleParent mem ctx (UInt64.ofNat cls) x
    ((lists cls).headD 0)) (context := ctx) he8 (caller :: callers)
  exact (h0.trans (h1.trans (h2.trans (decArr_ret hfn _ ctx e' callers hd))))

/-- The last reference of an empty boxed array: recycled at once. -/
theorem ArrShell.decArr_returns_boxed_empty {P : Program} {fn : FunId}
    (hfn : P.funcs[fn]? = some decArr) {mem : Memory} {ctx base bump limit : Word}
    {lists : Nat → List Word} {x : Word} {cls cap : Nat}
    (h : ArrShell mem x 1 cls cap .boxed 0)
    (halloc : ArrayAllocator mem ctx base bump limit lists)
    (ha : Allocated base bump lists x (classBytes cls)) :
    Returns0 P fn (decArrEnv x) mem ctx 2
        (recycleParent mem ctx (UInt64.ofNat cls) x ((lists cls).headD 0)) ∧
      ArrayAllocator (recycleParent mem ctx (UInt64.ofNat cls) x ((lists cls).headD 0)) ctx base
        bump limit (pushFree lists cls x) := by
  obtain ⟨hhead, hw1, hw2, hal⟩ := recycle_facts halloc h ha
  refine ⟨fun caller callers hd => ?_, hal⟩
  obtain ⟨e, he1, he2, h0⟩ := decArr_entry hfn mem ctx x (caller :: callers)
  obtain ⟨e', he8, h1⟩ := decArr_step_array_empty hfn he1 he2 h.pointer_branch h.count_load
    h.rc_not_slt_zero (by decide) h.scan_load (by decide) (by decide) h.size_load (by decide)
    h.class_load hhead hw1 hw2 (caller :: callers)
  have h2 := decArr_step_finish hfn (mem := recycleParent mem ctx (UInt64.ofNat cls) x
    ((lists cls).headD 0)) (context := ctx) he8 (caller :: callers)
  exact (h0.trans (h1.trans (h2.trans (decArr_ret hfn _ ctx e' callers hd))))

/-! ## The last reference of a boxed array of immediates: the scan -/

/-- The scan from the continuation with `r` immediates left, over any memories `M r` that hold
what the loop reads: `r` elements visited, then the cell recycled; `r + 1` charges. -/
private theorem scan_loop {P : Program} {fn : FunId} (hfn : P.funcs[fn]? = some decArr)
    {M : Nat → Memory} {ctx x : Word} {cls n : Nat} {xs : List Word} {head : Word}
    (hlen : xs.length = n) (hx : x ≠ 0) (hn : n < 2 ^ 32)
    (hcnt : ∀ r ≤ n, loadWord (M r) .w32 .zero (x + 4) = some (UInt64.ofNat r))
    (hscan : ∀ r ≤ n, loadWord (M r) .w8 .zero x = some (UInt64.ofNat arrayScan))
    (helem : ∀ (j : Nat) (hj : j < xs.length),
      loadWord (M (j + 1)) .w64 .zero (x + UInt64.ofNat (arrayPayloadOffset + 8 * j)) = some xs[j])
    (hw : ∀ r < n, (M (r + 1)).write? .w32 (x + 4) (UInt64.ofNat r) = .ok (M r))
    (himm : ∀ y ∈ xs, y &&& 1 = 1)
    (hcls : loadWord (M 0) .w8 .zero (x + 1) = some (UInt64.ofNat cls))
    (hpred : loadWord (M 0) .w64 .zero (x + 8) = some 0)
    (hhead : loadWord (M 0) .w64 .zero (freeHeadAddress ctx (UInt64.ofNat cls)) = some head)
    (hrec1 : (M 0).write? .w64 x head = .ok ((M 0).write .w64 x head))
    (hrec2 : ((M 0).write .w64 x head).write? .w64 (freeHeadAddress ctx (UInt64.ofNat cls)) x =
      .ok (recycleParent (M 0) ctx (UInt64.ofNat cls) x head))
    (rest : List Frame) :
    ∀ r, r ≤ n → ∀ e : Env, e[8]? = some x →
      ∃ e', e'[8]? = some 0 ∧
        Sem.Star (semStep P) (State.mk (M r) ctx ({ fn, label := 6, pos := 0, env := e } :: rest))
          (r + 1)
          (State.mk (recycleParent (M 0) ctx (UInt64.ofNat cls) x head) ctx
            ({ fn, label := 6, pos := 0, env := e' } :: rest)) := by
  intro r
  induction r with
  | zero =>
    intro _ e he8
    have h := decArr_step_recycle hfn (mem := M 0) (context := ctx) he8 hx (hcnt 0 (by omega))
      (hscan 0 (by omega)) hcls hpred hhead hrec1 hrec2 rest
    simpa using h
  | succ r ih =>
    intro hr e he8
    have hj : r < xs.length := by omega
    obtain ⟨e1, he1, he2, h1⟩ := decArr_step_array_next hfn (mem := M (r + 1)) (context := ctx)
      (r := r) he8 hx (hcnt (r + 1) hr) (by omega) (hscan (r + 1) hr) (helem r hj)
      (hw r (by omega)) rest
    obtain ⟨e2, he8', h2⟩ := decArr_step_immediate hfn (mem := M r) (context := ctx) he1 he2
      (himm _ (List.getElem_mem hj)) rest
    obtain ⟨e3, he3, h3⟩ := ih (by omega) e2 he8'
    refine ⟨e3, he3, ?_⟩
    have := h1.trans (h2.trans h3)
    rwa [show 1 + (0 + (r + 1)) = r + 1 + 1 by omega] at this


/-- The last reference of a non-empty boxed array of immediates: the scan visits every element
from the last to the first, then the cell is recycled; `n + 1` charges for `n` elements. -/
theorem ArrCell.decArr_returns_immediates {P : Program} {fn : FunId}
    (hfn : P.funcs[fn]? = some decArr) {mem : Memory} {ctx base bump limit : Word}
    {lists : Nat → List Word} {x : Word} {cls cap : Nat} {xs : List Word}
    (h : ArrCell mem x 1 cls cap .boxed xs) (hne : xs ≠ []) (himm : ∀ y ∈ xs, y &&& 1 = 1)
    (halloc : ArrayAllocator mem ctx base bump limit lists)
    (ha : Allocated base bump lists x (classBytes cls)) :
    ∃ mem', Returns0 P fn (decArrEnv x) mem ctx (xs.length + 1) mem' ∧
      ArrayAllocator mem' ctx base bump limit (pushFree lists cls x) := by
  have hs := h.shell
  have h24 := hs.classBytes_ge_24
  have hfit := hs.fit
  have hsz := hs.size_le
  have hp := hs.payload_le
  have hm8 : 8 * xs.length ≤ 8 * cap := Nat.mul_le_mul_left 8 hsz
  have hbx : ElemKind.boxed.bytes = 8 := rfl
  rw [hbx] at hp
  unfold arrayPayloadOffset at hp
  have hcw := IxCC.Rt.Rc.classWords_le_max hs.cls_hi
  have hmax : IxCC.Rt.Rc.maxCellWords = 2 ^ 26 := IxCC.Rt.Rc.maxCellWords_eq
  have hcb8 : classBytes cls = 8 * IxCC.Rt.Rc.classWords cls := rfl
  have hlen32 : xs.length < 2 ^ 32 := by omega
  obtain ⟨n, hn⟩ : ∃ n, xs.length = n + 1 := by
    cases xs with
    | nil => exact absurd rfl hne
    | cons y ys => exact ⟨ys.length, by simp⟩
  have h4 : (x + 4).toNat = x.toNat + 4 := addr_toNat (i := 4) (by omega)
  have h8 := hs.off8
  let B := mem.write .w64 (x + 8) 0
  let M : Nat → Memory := fun r => B.write .w32 (x + 4) (UInt64.ofNat r)
  have hfrB : MemFrame mem B (Span (x.toNat + 8) 8) := by
    have := MemFrame.write mem .w64 (x + 8) 0 (by rw [h8]; simp [X86.Width.bytes]; omega)
    rw [h8] at this; simpa [X86.Width.bytes] using this
  have hfrM : ∀ r, MemFrame mem (M r) (fun k => x.toNat + 4 ≤ k ∧ k < x.toNat + 16) := by
    intro r
    have f2 := MemFrame.write B .w32 (x + 4) (UInt64.ofNat r) (by rw [h4]; simp [X86.Width.bytes]; omega)
    exact (hfrB.mono (fun k hk => by unfold Span at hk; omega)).trans
      (f2.mono (fun k hk => by unfold Span at hk; rw [h4] at hk; simp [X86.Width.bytes] at hk; omega))
  have hr4 : ∀ j < 4, B.readable (x + 4 + UInt64.ofNat j) = true := by
    intro j hj
    have := hs.readable_at (off := 4) (n := 4) (by omega) j hj
    rw [show (x + 4 : Word) = x + UInt64.ofNat 4 from rfl]
    simpa [B, Memory.write] using this
  have hcnt : ∀ r ≤ n + 1, loadWord (M r) .w32 .zero (x + 4) = some (UInt64.ofNat r) := by
    intro r hr
    exact load32_write32 hr4 (by rw [u64_toNat_ofNat_lt (by omega)]; omega)
  have hscan : ∀ r ≤ n + 1, loadWord (M r) .w8 .zero x = some (UInt64.ofNat arrayScan) := by
    intro r _
    exact (hfrM r).load hs.scan_load (by simp [X86.Width.bytes]; omega)
      (fun k _ k2 hk => by simp [X86.Width.bytes] at k2; omega)
  have h1 : (x + 1).toNat = x.toNat + 1 := addr_toNat (i := 1) (by omega)
  have hcls : loadWord (M 0) .w8 .zero (x + 1) = some (UInt64.ofNat cls) :=
    (hfrM 0).load hs.class_load (by rw [h1]; simp [X86.Width.bytes]; omega)
      (fun k k1 k2 hk => by rw [h1] at k1 k2; simp [X86.Width.bytes] at k2; omega)
  have hpred : loadWord (M 0) .w64 .zero (x + 8) = some 0 := by
    have hw : WordAt B (x + 8) 0 := wordAt_write64 (fun i hi => by
      simpa [B, Memory.write] using hs.size_word.readable i hi)
    exact wordAt_load64 (hw.write_disjoint (by rw [h4]; simp [X86.Width.bytes]; omega)
      (by rw [h8]; omega) (by rw [h8, h4]; simp [X86.Width.bytes]))
  have hc1 : 1 ≤ cls := by have := hs.cls_lo; unfold minArrayClass at this; omega
  have hhn := halloc.freeHead_toNat hs.cls_hi
  have hcb := halloc.context_before
  have hcf := halloc.context_fit
  have hcls_hi := hs.cls_hi
  unfold maxClass at hcb hcf hcls_hi
  have hhead : loadWord (M 0) .w64 .zero (freeHeadAddress ctx (UInt64.ofNat cls)) =
      some ((lists cls).headD 0) :=
    (hfrM 0).load (wordAt_load64 (halloc.free_heads cls hc1 hs.cls_hi))
      (by simp [X86.Width.bytes]; omega)
      (fun k k1 k2 hk => by have := ha.1; simp [X86.Width.bytes] at k2; omega)
  have helem : ∀ (j : Nat) (hj : j < xs.length),
      loadWord (M (j + 1)) .w64 .zero (x + UInt64.ofNat (arrayPayloadOffset + 8 * j)) = some xs[j] := by
    intro j hj
    obtain ⟨hja, hjb⟩ := hs.elem_toNat (j := j) (by omega)
    rw [hbx] at hja hjb
    exact (hfrM (j + 1)).load (h.elem_load hj)
      (by show (elemAddr x .boxed j).toNat + 8 ≤ 2 ^ 64; rw [hja]; omega)
      (fun k k1 _ hk => by
        change (elemAddr x .boxed j).toNat ≤ k at k1
        rw [hja] at k1; unfold arrayPayloadOffset at k1; omega)
  have hw4 : mem.write? .w32 (x + 4) (UInt64.ofNat 0) = .ok (mem.write .w32 (x + 4) (UInt64.ofNat 0)) :=
    hs.write_ok (off := 4) (w := .w32) (by simp [X86.Width.bytes]; omega) _
  have hw : ∀ r < n + 1, (M (r + 1)).write? .w32 (x + 4) (UInt64.ofNat r) = .ok (M r) := by
    intro r _
    rw [(hfrM (r + 1)).write?_ok hw4]
    exact congrArg Except.ok (Lir.Opt.write_write_overwrite B .w32 (x + 4) _ _)
  obtain ⟨hw1, -, -⟩ := halloc.push_free hc1 hs.cls_hi ha hs.aligned hs.nonzero
  have hrec1 : (M 0).write? .w64 x ((lists cls).headD 0) =
      .ok ((M 0).write .w64 x ((lists cls).headD 0)) := (hfrM 0).write?_ok hw1
  have hrec2 : ((M 0).write .w64 x ((lists cls).headD 0)).write? .w64
      (freeHeadAddress ctx (UInt64.ofNat cls)) x =
      .ok (recycleParent (M 0) ctx (UInt64.ofNat cls) x ((lists cls).headD 0)) := by
    have := write?_ok (m := (M 0).write .w64 x ((lists cls).headD 0)) (w := .w64)
      (a := freeHeadAddress ctx (UInt64.ofNat cls)) (v := x) (fun j hj => by
        have hj8 : j < 8 := by simpa [X86.Width.bytes] using hj
        have hwm := halloc.head_writable cls hc1 hs.cls_hi j hj8
        rw [← (hfrM 0).writable] at hwm
        simpa [Memory.write] using hwm)
    simpa [recycleParent] using this
  have halloc0 : ArrayAllocator (M 0) ctx base bump limit lists :=
    halloc.frame (hfrM 0) (fun k hk => ha.not_allocBytes halloc k (by omega) (by omega))
  obtain ⟨-, -, hal0⟩ := halloc0.push_free hc1 hs.cls_hi ha hs.aligned hs.nonzero
  refine ⟨recycleParent (M 0) ctx (UInt64.ofNat cls) x ((lists cls).headD 0), ?_, hal0⟩
  intro caller callers hd
  obtain ⟨e, he1, he2, h0⟩ := decArr_entry hfn mem ctx x (caller :: callers)
  have hsize : loadWord mem .w64 .zero (x + 8) = some (UInt64.ofNat (n + 1)) := by
    rw [← hn]; exact hs.size_load
  have hwB : mem.write? .w64 (x + 8) 0 = .ok B :=
    hs.write_ok (off := 8) (w := .w64) (by simp [X86.Width.bytes]; omega) _
  have hwMn : B.write? .w32 (x + 4) (UInt64.ofNat n) = .ok (M n) := hfrB.write?_ok hw4
  have hjn : n < xs.length := by omega
  obtain ⟨e1, he1', he2', h1⟩ := decArr_step_array_detach hfn (mem := mem) (context := ctx)
    (n := n) he1 he2 hs.pointer_branch hs.count_load hs.rc_not_slt_zero (by decide)
    hs.scan_load (by decide) (by decide) hsize (by omega) (h.elem_load hjn) hwB hwMn
    (caller :: callers)
  obtain ⟨e2, he8, h2⟩ := decArr_step_immediate hfn (mem := M n) (context := ctx) he1' he2'
    (himm _ (List.getElem_mem hjn)) (caller :: callers)
  obtain ⟨e3, he3, h3⟩ := scan_loop hfn (M := M) (ctx := ctx) (x := x) (cls := cls) (n := n + 1)
    (xs := xs) (head := (lists cls).headD 0) hn hs.nonzero (by omega) hcnt hscan helem hw himm
    hcls hpred hhead hrec1 hrec2 (caller :: callers) n (by omega) e2 he8
  have h4' := decArr_step_finish hfn (mem := recycleParent (M 0) ctx (UInt64.ofNat cls) x
    ((lists cls).headD 0)) (context := ctx) he3 (caller :: callers)
  have hall := h0.trans (h1.trans (h2.trans (h3.trans (h4'.trans
    (decArr_ret hfn _ ctx e3 callers hd)))))
  rw [hn]
  exact star_cast hall (by omega)

end IxCC.Rt.Rc.Array
