import Compilatrix.Rt.Procs.Entry
import Compilatrix.Rt.Proof.OpsAlloc
import Compilatrix.Lir.Proof.Run

/-!
# `cx_init`

`cx_init` (`Rt.Procs.cxInit`) runs on a region of `size` bytes from
`ctx − 64` that is readable and writable (`Region`). It fails with `heap`
exactly when the region is misaligned, below `minRegion` bytes, or reaches
`2^63` (`RegionOk`, `cxInit_fail`); otherwise it returns, without charging
the clock, with memory satisfying the immortal heap invariant for the empty
heap and no cells, the stack budget at `ctx − 48`, and the permissions it
was given (`cxInit_ok`). The heap invariant is `Rt.lower_correct`'s
precondition for a run from an empty heap.
-/

set_option autoImplicit false

namespace Compilatrix.Rt.Proof

open Compilatrix.Lir
open Compilatrix.Rt.Procs
open Compilatrix.X86 (Memory)

/-! ## Aligning down -/

theorem and_alignDown {n : Nat} (hn : n < 2 ^ 64) : n &&& (2 ^ 64 - 64) = n / 64 * 64 := by
  have h1 : (2 ^ 64 - 64 : Nat) = (2 ^ 58 - 1) <<< 6 := by decide
  have h2 : n / 64 * 64 = (n >>> 6) <<< 6 := by
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [h1, h2]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one,
    Nat.testBit_shiftRight]
  by_cases h6 : 6 ≤ i
  · have h' : 6 + (i - 6) = i := by omega
    by_cases h64 : i < 64
    · simp [h6, h', show i - 6 < 58 by omega]
    · have : n.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [h6, h', this, show ¬ (i - 6 < 58) by omega]
  · simp [h6]

theorem word_alignDown (x : Word) : (x &&& (0 - UInt64.ofNat 64)).toNat = x.toNat / 64 * 64 := by
  rw [UInt64.toNat_and, show (0 - UInt64.ofNat 64 : Word).toNat = 2 ^ 64 - 64 from rfl]
  exact and_alignDown (by have := x.toNat_lt_size; simp only [UInt64.size] at this; omega)

/-! ## Zeroing words of the context block -/

/-- A 64-bit store of `0` at `ctx + d`. -/
def zeroAt (d : Int) : Stmt := .store .w64 { base := some .ctx, disp := d } (.imm 0)

/-- The memory after zeroing the words at `ctx + d`, `d ∈ ds`, in order. -/
def zeros (m : Memory) (ctx : Word) : List Int → Memory
  | [] => m
  | d :: ds => zeros (m.write .w64 (ctx + 0 + dispWord d) 0) ctx ds

@[simp] theorem zeros_readable {ctx : Word} : ∀ (m : Memory) (ds : List Int), (zeros m ctx ds).readable = m.readable
  | _, [] => rfl
  | m, _ :: ds => by rw [zeros, zeros_readable _ ds]; simp [Memory.write]

@[simp] theorem zeros_writable {ctx : Word} : ∀ (m : Memory) (ds : List Int), (zeros m ctx ds).writable = m.writable
  | _, [] => rfl
  | m, _ :: ds => by rw [zeros, zeros_writable _ ds]; simp [Memory.write]

theorem execList_zeros {ρ : Env} {ctx : Word} : ∀ (m : Memory) (ds : List Int),
    (∀ d ∈ ds, ∀ i < 8, m.writable (ctx + 0 + dispWord d + UInt64.ofNat i) = true) →
    execList ρ m ctx (ds.map zeroAt) = some (ρ, zeros m ctx ds)
  | _, [], _ => rfl
  | m, d :: ds, h => by
    simp only [List.map_cons, execList, zeroAt, Stmt.exec, Addr.eval, Arg.eval_imm, Option.bind_eq_bind,
      Option.bind_some]
    rw [write?_ok (w := .w64) (fun i hi => h d (by simp) i (by simpa [X86.Width.bytes] using hi))]
    simp only
    exact execList_zeros _ ds fun d' hd' i hi => by
      simpa [Memory.write] using h d' (List.mem_cons_of_mem _ hd') i hi

/-- A word clear of every zeroed word keeps its value. -/
theorem zeros_keep {ctx b v : Word} (hb : b.toNat + 8 ≤ 2 ^ 64) : ∀ (m : Memory) (ds : List Int), WordAt m b v →
    (∀ d ∈ ds, (ctx + 0 + dispWord d).toNat + 8 ≤ 2 ^ 64 ∧
      (b.toNat + 8 ≤ (ctx + 0 + dispWord d).toNat ∨ (ctx + 0 + dispWord d).toNat + 8 ≤ b.toNat)) →
    WordAt (zeros m ctx ds) b v
  | _, [], hw, _ => hw
  | m, d :: ds, hw, h => by
    obtain ⟨ha, hd⟩ := h d (by simp)
    exact zeros_keep hb _ ds (hw.write_disjoint ha hb hd) fun d' hd' => h d' (List.mem_cons_of_mem _ hd')

/-! ## The blocks -/

/-- Block 8's body, with its zeroing stores as one list. -/
def body8 : List Stmt :=
  [.assign 5 (.addr { base := some (.v 2), disp := ((ctxBlockBytes + objectAlign - 1 : Nat) : Int) }),
    .assign 6 (.bin .and .w64 (.v 5) (.imm (0 - UInt64.ofNat objectAlign))),
    .store .w64 { base := some .ctx, disp := stackBudgetOff } (.v 1),
    .store .w64 { base := some .ctx, disp := bumpOff } (.v 6),
    .store .w64 { base := some .ctx, disp := limitOff } (.v 4),
    .store .w64 { base := some .ctx, disp := regionBaseOff } (.v 2)] ++
  (reservedOffs ++ headClasses.map headOffset).map zeroAt ++
  [.assign 7 (.bin .sub .w64 (.v 4) (.v 6))]

theorem cxInit_b0 : cxInit.blocks[0]? = some {
    body := #[.assign 2 (.addr { base := some .ctx, disp := -(ctxOffset : Int) }),
      .assign 3 (.bin .and .w64 (.v 2) (.imm (UInt64.ofNat 7)))]
    term := .br .ne .w64 (.v 3) (.imm (UInt64.ofNat 0)) ⟨1, []⟩ ⟨2, []⟩ } := rfl
theorem cxInit_b1 : cxInit.blocks[1]? = some { term := .fail .heap, cold := true } := rfl
theorem cxInit_b2 : cxInit.blocks[2]? =
    some { term := .br .ult .w64 (.v 0) (.imm (UInt64.ofNat minRegion)) ⟨3, []⟩ ⟨4, []⟩ } := rfl
theorem cxInit_b3 : cxInit.blocks[3]? = some { term := .fail .heap, cold := true } := rfl
theorem cxInit_b4 : cxInit.blocks[4]? = some { term := .brOvf .addC 4 (.v 2) (.v 0) ⟨5, []⟩ ⟨6, []⟩ } := rfl
theorem cxInit_b5 : cxInit.blocks[5]? =
    some { term := .br .slt .w64 (.v 4) (.imm (UInt64.ofNat 0)) ⟨7, []⟩ ⟨8, []⟩ } := rfl
theorem cxInit_b6 : cxInit.blocks[6]? = some { term := .fail .heap, cold := true } := rfl
theorem cxInit_b7 : cxInit.blocks[7]? = some { term := .fail .heap, cold := true } := rfl
set_option maxRecDepth 8000 in
theorem cxInit_b8 : cxInit.blocks[8]? = some { body := body8.toArray, term := .ret [.v 7] } := rfl

theorem cxInit_params : cxInit.params = [0, 1] := rfl

theorem body8_noCall : ∀ s ∈ body8, s.isCall = false := by
  intro s hs
  rcases List.mem_append.1 hs with hs | hs
  · rcases List.mem_append.1 hs with hs | hs
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · obtain ⟨d, -, rfl⟩ := List.mem_map.1 hs
      rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    subst hs
    rfl

/-! ## Statements and outcomes -/

theorem execList_cons_of {ρ ρ' : Env} {m m' : Memory} {ctx : Word} {s : Stmt} {ss : List Stmt}
    (h : s.exec ρ m ctx = some (ρ', m')) : execList ρ m ctx (s :: ss) = execList ρ' m' ctx ss := by
  simp only [execList, h]

theorem exec_assign {ρ : Env} {m : Memory} {ctx : Word} {x : VReg} {r : Rhs} {v : Word}
    (h : r.eval ρ m ctx = some v) : (Stmt.assign x r).exec ρ m ctx = some (ρ.insert x v, m) := by
  simp [Stmt.exec, h]

theorem exec_store {ρ : Env} {m : Memory} {ctx a v : Word} {d : Int} {x : Arg}
    (hd : ctx + 0 + dispWord d = a) (hx : x.eval ρ = some v)
    (hw : ∀ i < 8, m.writable (a + UInt64.ofNat i) = true) :
    (Stmt.store .w64 { base := some .ctx, disp := d } x).exec ρ m ctx = some (ρ, m.write .w64 a v) := by
  simp only [Stmt.exec, Addr.eval, Option.bind_eq_bind, Option.bind_some, hd, hx]
  rw [write?_ok (w := .w64) (fun i hi => hw i (by simpa [X86.Width.bytes] using hi))]

theorem eval_fail_of {q : Program} {args : List Word} {mem : Memory} {ctx : Word} {s₀ s : State} {c : Nat}
    {r : Sem.Resource} (hinit : State.initial q args mem ctx = some s₀) (hst : Sem.Star (semStep q) s₀ c s)
    (hc : c = 0) (hf : step q s = .fail r) (k : Nat) : eval q k args mem ctx = .resource r := by
  subst hc
  exact (runs_eval hinit).eq ((Sem.Reaches.final (k := k) (by rw [semStep_fail.2 hf]; exact .fail)).star hst)

theorem eval_done_of {q : Program} {args : List Word} {mem mem' : Memory} {ctx : Word} {s₀ s : State} {c : Nat}
    {vals : List Word} (hinit : State.initial q args mem ctx = some s₀) (hst : Sem.Star (semStep q) s₀ c s)
    (hc : c = 0) (hf : step q s = .done vals mem') (k : Nat) : eval q k args mem ctx = .ok (vals, mem') := by
  subst hc
  exact (runs_eval hinit).eq ((Sem.Reaches.final (k := k) (by rw [semStep_done.2 hf]; exact .done)).star hst)

/-! ## Words and addresses -/

theorem and7_toNat (x : Word) : (x &&& UInt64.ofNat 7).toNat = x.toNat % 8 := by
  rw [UInt64.toNat_and, show (UInt64.ofNat 7 : Word).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem base_toNat (ctx : Word) : (ctx - 64).toNat = (2 ^ 64 - 64 + ctx.toNat) % 2 ^ 64 := by
  rw [UInt64.toNat_sub]
  rfl

theorem add_word_toNat (a b : Word) : (a + b).toNat = (a.toNat + b.toNat) % 2 ^ 64 := UInt64.toNat_add a b

theorem zeroOff_mem {d : Int} (h : d ∈ reservedOffs ++ headClasses.map headOffset) :
    d = -((16 : Nat) : Int) ∨ d = -((8 : Nat) : Int) ∨ ∃ n : Nat, 8 ≤ n ∧ n ≤ 568 ∧ d = (n : Int) := by
  simp only [reservedOffs, headClasses, headOffset, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at h
  rcases h with (rfl | rfl) | ⟨c, ⟨j, hj, rfl⟩, rfl⟩
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr ⟨8 * (j + 1), by omega, by omega, by push_cast; rfl⟩)

/-- The zeroed words lie in `[ctx − 16, ctx + 576)`. -/
theorem zeroAddr {ctx : Word} {d : Int} (hc : 64 ≤ ctx.toNat) (hfit : ctx.toNat + 576 < 2 ^ 64)
    (h : d ∈ reservedOffs ++ headClasses.map headOffset) :
    ctx.toNat - 16 ≤ (ctx + 0 + dispWord d).toNat ∧ (ctx + 0 + dispWord d).toNat + 8 ≤ ctx.toNat + 576 := by
  rcases zeroOff_mem h with rfl | rfl | ⟨n, h8, h568, rfl⟩
  · rw [ctx_disp_neg ctx (by omega), ctx_sub_toNat hc (by omega)]; omega
  · rw [ctx_disp_neg ctx (by omega), ctx_sub_toNat hc (by omega)]; omega
  · rw [dispWord_ofNat, UInt64.add_zero, addr_toNat (by omega)]; omega

/-! ## The run -/

/-- The region `cx_init` is given: `size` bytes from `ctx − 64`, readable
and writable. -/
def Region (mem : Memory) (ctx size : Word) : Prop :=
  ∀ k : Nat, (ctx - 64).toNat ≤ k → k < (ctx - 64).toNat + size.toNat →
    mem.readable (UInt64.ofNat k) = true ∧ mem.writable (UInt64.ofNat k) = true

/-- `cx_init`'s checks: the region from `ctx − 64` is 8-aligned, at least
`minRegion` bytes, and below `2^63`. -/
def RegionOk (ctx size : Word) : Prop :=
  (ctx - 64).toNat % 8 = 0 ∧ minRegion ≤ size.toNat ∧ (ctx - 64).toNat + size.toNat < 2 ^ 63

/-- What `cx_init` leaves: the heap invariant for the empty heap (under any
constructor table), the stack budget at `ctx − 48`, and the permissions it
was given. -/
structure InitPost (ctx budget : Word) (mem mem' : Memory) : Prop where
  heap : ∀ T : Lower.Tables, HeapInv T [] { cells := #[] } ctx mem'
  budget : WordAt mem' (ctx - 48) budget
  readable : mem'.readable = mem.readable
  writable : mem'.writable = mem.writable

theorem region_at {mem : Memory} {ctx size : Word} (hreg : Region mem ctx size) {a : Word} {i : Nat}
    (hlo : (ctx - 64).toNat ≤ a.toNat + i) (hhi : a.toNat + i < (ctx - 64).toNat + size.toNat)
    (hfit : a.toNat + i < 2 ^ 64) :
    mem.readable (a + UInt64.ofNat i) = true ∧ mem.writable (a + UInt64.ofNat i) = true := by
  have : a + UInt64.ofNat i = UInt64.ofNat (a.toNat + i) :=
    UInt64.toNat_inj.mp (by rw [addr_toNat hfit, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hfit])
  rw [this]
  exact hreg _ hlo hhi

/-- The part of the region Lir uses: from `ctx − 48` (the context words
`cx_init` and the allocator use, then the objects) to its end. The first 16
bytes (`entrySp`, `stackLimit`, 04 §6) are the export wrapper's: the
machine writes them and Lir never does, so the backend's entry invariant
keeps them out of Lir's memory (`Stacking.Proof.EntryBase.ctxCells`). -/
def LirRegion (mem : Memory) (ctx size : Word) : Prop :=
  ∀ k : Nat, (ctx - 64).toNat + 16 ≤ k → k < (ctx - 64).toNat + size.toNat →
    mem.readable (UInt64.ofNat k) = true ∧ mem.writable (UInt64.ofNat k) = true

/-- The whole region includes the part Lir uses. -/
theorem Region.lir {mem : Memory} {ctx size : Word} (h : Region mem ctx size) : LirRegion mem ctx size :=
  fun k h1 h2 => h k (by omega) h2

theorem lirRegion_at {mem : Memory} {ctx size : Word} (hreg : LirRegion mem ctx size) {a : Word} {i : Nat}
    (hlo : (ctx - 64).toNat + 16 ≤ a.toNat + i) (hhi : a.toNat + i < (ctx - 64).toNat + size.toNat)
    (hfit : a.toNat + i < 2 ^ 64) :
    mem.readable (a + UInt64.ofNat i) = true ∧ mem.writable (a + UInt64.ofNat i) = true := by
  have : a + UInt64.ofNat i = UInt64.ofNat (a.toNat + i) :=
    UInt64.toNat_inj.mp (by rw [addr_toNat hfit, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hfit])
  rw [this]
  exact hreg _ hlo hhi

/-- The last byte of the context block, from the region base (`v5`). -/
def blockEnd (base : Word) : Word := base + 0 + dispWord ((ctxBlockBytes + objectAlign - 1 : Nat) : Int)

/-- The first object: the context block's end aligned down to `objectAlign`. -/
def bumpOf (base : Word) : Word := blockEnd base &&& (0 - UInt64.ofNat objectAlign)

theorem bumpOf_toNat {base : Word} (h : base.toNat + 703 < 2 ^ 64) :
    (bumpOf base).toNat = (base.toNat + 703) / 64 * 64 := by
  have h703 : (ctxBlockBytes + objectAlign - 1 : Nat) = 703 := rfl
  simp only [bumpOf, blockEnd, h703, dispWord_ofNat, UInt64.add_zero]
  rw [show objectAlign = 64 from rfl, word_alignDown, addr_toNat h]

/-- **`cx_init` from its entry.** Where its checks reject the region
(`¬ RegionOk`), it fails with `heap`; otherwise, when the part of the region
Lir uses is readable and writable (`LirRegion`), it returns the bytes left
for objects with `InitPost`. The outcome does not depend on the clock: no
step charges it. -/
theorem cxInit_cases_lir {q : Program} {g : FunId} (hq : q.funcs[g]? = some cxInit) (hmain : q.main = g)
    (size budget ctx : Word) (mem : Memory) :
    ((∀ k, eval q k [size, budget] mem ctx = .resource .heap) ∧ ¬ RegionOk ctx size) ∨
      (RegionOk ctx size ∧ (LirRegion mem ctx size → ∃ left mem',
        (∀ k, eval q k [size, budget] mem ctx = .ok ([left], mem')) ∧ InitPost ctx budget mem mem')) := by
  let ρ₀ : Env := (({} : Env).insert 0 size).insert 1 budget
  have hinit : State.initial q [size, budget] mem ctx = some (atState mem ctx g 0 0 ρ₀ []) := by
    simp [State.initial, enter, hmain, hq, cxInit_params, bindParams, ρ₀]
  have hB := base_toNat ctx
  have hctx := word_lt ctx
  have hS := word_lt size
  -- block 0: the base and its misalignment
  let ρ₁ : Env := (ρ₀.insert 2 (ctx - 64)).insert 3 ((ctx - 64) &&& UInt64.ofNat 7)
  have hbase : ctx + 0 + dispWord (-(ctxOffset : Int)) = ctx - 64 := ctx_disp_neg ctx (k := ctxOffset) (by decide)
  have hx0 : execList ρ₀ mem ctx [.assign 2 (.addr { base := some .ctx, disp := -(ctxOffset : Int) }),
      .assign 3 (.bin .and .w64 (.v 2) (.imm (UInt64.ofNat 7)))] = some (ρ₁, mem) := by
    rw [execList_cons_of (exec_assign (v := ctx - 64) (by simp only [lir_eval]; rw [hbase])),
      execList_cons_of (exec_assign (v := (ctx - 64) &&& UInt64.ofNat 7) (by simp only [lir_eval, env_insert_self]))]
    rfl
  have hstar0 := stmts_at (p := q) (rest := []) (pre := []) (post := []) hq cxInit_b0 (by rfl)
    (by simp [Stmt.isCall]) hx0
  by_cases h7n : (ctx - 64) &&& UInt64.ofNat 7 ≠ 0
  · -- misaligned
    left
    have hs := br_at (p := q) (mem := mem) (ctx := ctx) (rest := []) (pos := 2) (ρ := ρ₁)
      (e := ⟨1, []⟩) (va := (ctx - 64) &&& UInt64.ofNat 7) (vb := 0) (vals := []) (ρ' := ρ₁)
      hq cxInit_b0 rfl rfl (by simp [ρ₁]) rfl (by rw [holds_ne, decide_eq_true h7n]; rfl) rfl cxInit_b1 rfl
    refine ⟨eval_fail_of hinit (hstar0.trans (star_of_step hs)) rfl (fail_at hq cxInit_b1 rfl rfl), ?_⟩
    rintro ⟨h8, -, -⟩
    apply h7n
    apply UInt64.toNat_inj.mp
    rw [and7_toNat, h8]
    rfl
  have h7 : (ctx - 64) &&& UInt64.ofNat 7 = 0 := Decidable.of_not_not h7n
  have hs0 := br_at (p := q) (mem := mem) (ctx := ctx) (rest := []) (pos := 2) (ρ := ρ₁)
    (e := ⟨2, []⟩) (va := (ctx - 64) &&& UInt64.ofNat 7) (vb := 0) (vals := []) (ρ' := ρ₁)
    hq cxInit_b0 rfl rfl (by simp [ρ₁]) rfl (by rw [holds_ne, h7]; rfl) rfl cxInit_b2 rfl
  have hstar1 := hstar0.trans (star_of_step hs0)
  -- block 2: at least `minRegion` bytes
  have hv0 : (Arg.v 0).eval ρ₁ = some size := by
    simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁, ρ₀]
  have hmin' : (UInt64.ofNat minRegion : Word).toNat = 4096 := rfl
  by_cases hmin : size < UInt64.ofNat minRegion
  · left
    have hs := br_at (p := q) (mem := mem) (ctx := ctx) (rest := []) (pos := 0) (ρ := ρ₁)
      (e := ⟨3, []⟩) (va := size) (vb := UInt64.ofNat minRegion) (vals := []) (ρ' := ρ₁)
      hq cxInit_b2 rfl rfl hv0 rfl (by rw [holds_ult, decide_eq_true hmin]; rfl) rfl cxInit_b3 rfl
    refine ⟨eval_fail_of hinit (hstar1.trans (star_of_step hs)) rfl (fail_at hq cxInit_b3 rfl rfl), ?_⟩
    rintro ⟨-, hm, -⟩
    rw [UInt64.lt_iff_toNat_lt, hmin'] at hmin
    exact absurd hm (Nat.not_le.2 hmin)
  have hs2 := br_at (p := q) (mem := mem) (ctx := ctx) (rest := []) (pos := 0) (ρ := ρ₁)
    (e := ⟨4, []⟩) (va := size) (vb := UInt64.ofNat minRegion) (vals := []) (ρ' := ρ₁)
    hq cxInit_b2 rfl rfl hv0 rfl (by rw [holds_ult, decide_eq_false hmin]; rfl) rfl cxInit_b4 rfl
  have hstar2 := hstar1.trans (star_of_step hs2)
  -- block 4: the limit, without a carry
  have hv2 : (Arg.v 2).eval ρ₁ = some (ctx - 64) := by
    simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁, ρ₀]
  let ρ₄ : Env := ρ₁.insert 4 (ctx - 64 + size)
  by_cases hcar : ctx - 64 + size < ctx - 64
  · left
    have hs := brOvf_at (p := q) (mem := mem) (ctx := ctx) (rest := []) (pos := 0) (ρ := ρ₁) (o := .addC)
      (x := 4) (e := ⟨6, []⟩) (va := ctx - 64) (vb := size) (vals := []) (ρ' := ρ₄)
      hq cxInit_b4 rfl rfl hv2 hv0 (by simp [Ovf.eval, hcar]) rfl cxInit_b6 rfl
    refine ⟨eval_fail_of hinit (hstar2.trans (star_of_step hs)) rfl (fail_at hq cxInit_b6 rfl rfl), ?_⟩
    rintro ⟨-, -, hlt⟩
    rw [UInt64.lt_iff_toNat_lt, add_word_toNat] at hcar
    omega
  have hs4 := brOvf_at (p := q) (mem := mem) (ctx := ctx) (rest := []) (pos := 0) (ρ := ρ₁) (o := .addC)
    (x := 4) (e := ⟨5, []⟩) (va := ctx - 64) (vb := size) (vals := []) (ρ' := ρ₄)
    hq cxInit_b4 rfl rfl hv2 hv0 (by simp [Ovf.eval, hcar]) rfl cxInit_b5 rfl
  have hstar4 := hstar2.trans (star_of_step hs4)
  -- block 5: below `2^63`
  have hv4 : (Arg.v 4).eval ρ₄ = some (ctx - 64 + size) := by
    simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₄]
  by_cases hneg : 2 ^ 63 ≤ (ctx - 64 + size).toNat
  · left
    have hs := br_at (p := q) (mem := mem) (ctx := ctx) (rest := []) (pos := 0) (ρ := ρ₄)
      (e := ⟨7, []⟩) (va := ctx - 64 + size) (vb := 0) (vals := []) (ρ' := ρ₄)
      hq cxInit_b5 rfl rfl hv4 rfl (by rw [holds_slt_zero, decide_eq_true hneg]; rfl) rfl cxInit_b7 rfl
    refine ⟨eval_fail_of hinit (hstar4.trans (star_of_step hs)) rfl (fail_at hq cxInit_b7 rfl rfl), ?_⟩
    rintro ⟨-, -, hlt⟩
    rw [add_word_toNat] at hneg
    omega
  have hs5 := br_at (p := q) (mem := mem) (ctx := ctx) (rest := []) (pos := 0) (ρ := ρ₄)
    (e := ⟨8, []⟩) (va := ctx - 64 + size) (vb := 0) (vals := []) (ρ' := ρ₄)
    hq cxInit_b5 rfl rfl hv4 rfl (by rw [holds_slt_zero, decide_eq_false hneg]; rfl) rfl cxInit_b8 rfl
  have hstar5 := hstar4.trans (star_of_step hs5)
  -- the region passes the checks
  rw [UInt64.lt_iff_toNat_lt, add_word_toNat] at hcar
  rw [UInt64.lt_iff_toNat_lt, hmin'] at hmin
  rw [add_word_toNat] at hneg
  have h7' : (ctx - 64).toNat % 8 = 0 := by rw [← and7_toNat, h7]; rfl
  have hc64 : 64 ≤ ctx.toNat := by omega
  have hBc : (ctx - 64).toNat = ctx.toNat - 64 := by omega
  have hlim : (ctx - 64 + size).toNat = (ctx - 64).toNat + size.toNat := by rw [add_word_toNat]; omega
  right
  refine ⟨⟨h7', by rw [show minRegion = 4096 from rfl]; omega, by omega⟩, fun hreg => ?_⟩
  -- block 8
  have hW : ∀ (a : Word) (i : Nat), ctx.toNat - 48 ≤ a.toNat + i → a.toNat + i < ctx.toNat - 64 + size.toNat →
      mem.readable (a + UInt64.ofNat i) = true ∧ mem.writable (a + UInt64.ofNat i) = true :=
    fun a i h1 h2 => lirRegion_at hreg (by omega) (by omega) (by omega)
  have h48 : (ctx - 48).toNat = ctx.toNat - 48 := ctx_sub_toNat (k := 48) hc64 (by omega)
  have h40 : (ctx - 40).toNat = ctx.toNat - 40 := ctx40_toNat hc64
  have h32 : (ctx - 32).toNat = ctx.toNat - 32 := ctx32_toNat hc64
  have h24 : (ctx - 24).toNat = ctx.toNat - 24 := ctx_sub_toNat (k := 24) hc64 (by omega)
  have hbump := bumpOf_toNat (base := ctx - 64) (by omega)
  let bump := bumpOf (ctx - 64)
  let limit := ctx - 64 + size
  let ρ₅ : Env := (ρ₄.insert 5 (blockEnd (ctx - 64))).insert 6 bump
  let ρ₈ : Env := ρ₅.insert 7 (limit - bump)
  let m₁ := mem.write .w64 (ctx - 48) budget
  let m₂ := m₁.write .w64 (ctx - 40) bump
  let m₃ := m₂.write .w64 (ctx - 32) limit
  let m₄ := m₃.write .w64 (ctx - 24) (ctx - 64)
  let ds := reservedOffs ++ headClasses.map headOffset
  have hp₄ : m₄.readable = mem.readable ∧ m₄.writable = mem.writable := by
    simp [m₄, m₃, m₂, m₁, Memory.write]
  have e5 : (Stmt.assign 5
      (.addr { base := some (.v 2), disp := ((ctxBlockBytes + objectAlign - 1 : Nat) : Int) })).exec
        ρ₄ mem ctx = some (ρ₄.insert 5 (blockEnd (ctx - 64)), mem) :=
    exec_assign (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₄, ρ₁, ρ₀]; rfl)
  have e6 : (Stmt.assign 6 (.bin .and .w64 (.v 5) (.imm (0 - UInt64.ofNat objectAlign)))).exec
      (ρ₄.insert 5 (blockEnd (ctx - 64))) mem ctx = some (ρ₅, mem) :=
    exec_assign (by simp only [lir_eval, env_insert_self]; rfl)
  have eB : (Stmt.store .w64 { base := some .ctx, disp := stackBudgetOff } (.v 1)).exec ρ₅ mem ctx =
      some (ρ₅, m₁) :=
    exec_store (ctx_disp_neg ctx (k := 48) (by omega))
      (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₅, ρ₄, ρ₁, ρ₀])
      (fun i hi => (hW _ i (by omega) (by omega)).2)
  have eP : (Stmt.store .w64 { base := some .ctx, disp := bumpOff } (.v 6)).exec ρ₅ m₁ ctx =
      some (ρ₅, m₂) :=
    exec_store (ctx_disp_neg ctx (k := 40) (by omega))
      (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₅])
      (fun i hi => by simpa [m₁, Memory.write] using (hW (ctx - 40) i (by omega) (by omega)).2)
  have eL : (Stmt.store .w64 { base := some .ctx, disp := limitOff } (.v 4)).exec ρ₅ m₂ ctx =
      some (ρ₅, m₃) :=
    exec_store (ctx_disp_neg ctx (k := 32) (by omega))
      (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₅, ρ₄]; rfl)
      (fun i hi => by simpa [m₂, m₁, Memory.write] using (hW (ctx - 32) i (by omega) (by omega)).2)
  have eR : (Stmt.store .w64 { base := some .ctx, disp := regionBaseOff } (.v 2)).exec ρ₅ m₃ ctx =
      some (ρ₅, m₄) :=
    exec_store (ctx_disp_neg ctx (k := 24) (by omega))
      (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₅, ρ₄, ρ₁, ρ₀])
      (fun i hi => by simpa [m₃, m₂, m₁, Memory.write] using (hW (ctx - 24) i (by omega) (by omega)).2)
  have hfit : ctx.toNat + 576 < 2 ^ 64 := by omega
  have hwz : ∀ d ∈ ds, ∀ i < 8, m₄.writable (ctx + 0 + dispWord d + UInt64.ofNat i) = true := by
    intro d hd i hi
    obtain ⟨h1, h2⟩ := zeroAddr hc64 hfit hd
    rw [hp₄.2]
    exact (hW _ i (by omega) (by omega)).2
  have e7 : (Stmt.assign 7 (.bin .sub .w64 (.v 4) (.v 6))).exec ρ₅ (zeros m₄ ctx ds) ctx =
      some (ρ₈, zeros m₄ ctx ds) :=
    exec_assign (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₅, ρ₄]; rfl)
  have hx8 : execList ρ₄ mem ctx body8 = some (ρ₈, zeros m₄ ctx ds) := by
    simp only [body8, List.cons_append, List.nil_append]
    rw [execList_cons_of e5, execList_cons_of e6, execList_cons_of eB, execList_cons_of eP, execList_cons_of eL,
      execList_cons_of eR, execList_append, execList_zeros _ _ hwz, Option.bind_some, execList_cons_of e7]
    rfl
  have hstar8 := stmts_at (p := q) (rest := []) (pre := []) (post := []) hq cxInit_b8 (by simp)
    body8_noCall hx8
  have hdone : step q (atState (zeros m₄ ctx ds) ctx g 8 (([] : List Stmt).length + body8.length) ρ₈ []) =
      .done [limit - bump] (zeros m₄ ctx ds) :=
    step_ret_done (fr := { fn := g, label := 8, pos := ([] : List Stmt).length + body8.length, env := ρ₈ }) hq cxInit_b8
      (by simp) rfl (by simp [ρ₈])
  refine ⟨limit - bump, zeros m₄ ctx ds, eval_done_of hinit (hstar5.trans hstar8) rfl hdone, ?_⟩
  -- the words the context block holds
  have hR : ∀ (a : Word) (i : Nat), ctx.toNat - 48 ≤ a.toNat + i → a.toNat + i < ctx.toNat - 64 + size.toNat →
      mem.readable (a + UInt64.ofNat i) = true := fun a i h1 h2 => (hW a i h1 h2).1
  have w8 : 8 = X86.Width.bytes .w64 := rfl
  have wB₁ : WordAt m₁ (ctx - 48) budget := wordAt_write64 fun i hi => hR _ i (by omega) (by omega)
  have wB₂ : WordAt m₂ (ctx - 48) budget := wB₁.write_disjoint (by rw [← w8]; omega) (by omega) (.inl (by omega))
  have wP₂ : WordAt m₂ (ctx - 40) bump :=
    wordAt_write64 fun i hi => by simpa [m₁, Memory.write] using hR (ctx - 40) i (by omega) (by omega)
  have wB₃ : WordAt m₃ (ctx - 48) budget := wB₂.write_disjoint (by rw [← w8]; omega) (by omega) (.inl (by omega))
  have wP₃ : WordAt m₃ (ctx - 40) bump := wP₂.write_disjoint (by rw [← w8]; omega) (by omega) (.inl (by omega))
  have wL₃ : WordAt m₃ (ctx - 32) limit :=
    wordAt_write64 fun i hi => by simpa [m₂, m₁, Memory.write] using hR (ctx - 32) i (by omega) (by omega)
  have wB₄ : WordAt m₄ (ctx - 48) budget := wB₃.write_disjoint (by rw [← w8]; omega) (by omega) (.inl (by omega))
  have wP₄ : WordAt m₄ (ctx - 40) bump := wP₃.write_disjoint (by rw [← w8]; omega) (by omega) (.inl (by omega))
  have wL₄ : WordAt m₄ (ctx - 32) limit := wL₃.write_disjoint (by rw [← w8]; omega) (by omega) (.inl (by omega))
  have hkeep : ∀ (b v : Word), b.toNat + 8 ≤ ctx.toNat - 16 → WordAt m₄ b v → WordAt (zeros m₄ ctx ds) b v :=
    fun b v hb hw => zeros_keep (by omega) _ ds hw fun d hd => by
      obtain ⟨h1, h2⟩ := zeroAddr hc64 hfit hd
      exact ⟨by omega, .inl (by omega)⟩
  have hp' : (zeros m₄ ctx ds).readable = mem.readable ∧ (zeros m₄ ctx ds).writable = mem.writable := by
    rw [zeros_readable, zeros_writable]; exact hp₄
  refine ⟨fun T => ⟨bump, limit, ?_⟩, hkeep _ _ (by omega) wB₄, hp'.1, hp'.2⟩
  exact {
    len := rfl
    ctxLo := hc64
    bumpWord := hkeep _ _ (by omega) wP₄
    bumpWritable := fun i hi => by rw [hp'.2]; exact (hW (ctx - 40) i (by omega) (by omega)).2
    limitWord := hkeep _ _ (by omega) wL₄
    start := by show ctx.toNat + 576 ≤ (bumpOf (ctx - 64)).toNat; omega
    bumpLe := by show (bumpOf (ctx - 64)).toNat ≤ (ctx - 64 + size).toNat; omega
    limitLt := by show (ctx - 64 + size).toNat < 2 ^ 63; omega
    bumpAligned := by show (bumpOf (ctx - 64)).toNat % 8 = 0; omega
    free := fun k hk hk' => by
      rw [hp'.1, hp'.2]
      exact hreg k (by show (ctx - 64).toNat + 16 ≤ k; change (bumpOf (ctx - 64)).toNat ≤ k at hk; omega)
        (by change k < (ctx - 64 + size).toNat at hk'; omega)
    cells := fun ℓ h => absurd h (Nat.not_lt_zero ℓ)
    ordered := fun ℓ ℓ' a a' rc b _ hP => by simp at hP }

/-- **`cx_init` from its entry**, on a region given whole (`Region`). -/
theorem cxInit_cases {q : Program} {g : FunId} (hq : q.funcs[g]? = some cxInit) (hmain : q.main = g)
    (size budget ctx : Word) (mem : Memory) :
    ((∀ k, eval q k [size, budget] mem ctx = .resource .heap) ∧ ¬ RegionOk ctx size) ∨
      (RegionOk ctx size ∧ (Region mem ctx size → ∃ left mem',
        (∀ k, eval q k [size, budget] mem ctx = .ok ([left], mem')) ∧ InitPost ctx budget mem mem')) := by
  rcases cxInit_cases_lir hq hmain size budget ctx mem with h | ⟨hok, hs⟩
  · exact .inl h
  · exact .inr ⟨hok, fun hreg => hs hreg.lir⟩

/-- `cx_init` fails with `heap` on a region its checks reject. -/
theorem cxInit_fail {p : Program} {g : FunId} (hg : p.funcs[g]? = some cxInit) {size budget ctx : Word}
    {mem : Memory} (h : ¬ RegionOk ctx size) (k : Nat) :
    eval { p with main := g } k [size, budget] mem ctx = .resource .heap := by
  rcases cxInit_cases (q := { p with main := g }) hg rfl size budget ctx mem with ⟨he, -⟩ | ⟨hok, -⟩
  · exact he k
  · exact absurd hok h

/-- **`cx_init` establishes the heap invariant** on a readable and writable
region its checks accept, at every clock. -/
theorem cxInit_ok {p : Program} {g : FunId} (hg : p.funcs[g]? = some cxInit) {size budget ctx : Word}
    {mem : Memory} (hok : RegionOk ctx size) (hreg : Region mem ctx size) :
    ∃ left mem', (∀ k, eval { p with main := g } k [size, budget] mem ctx = .ok ([left], mem')) ∧
      InitPost ctx budget mem mem' := by
  rcases cxInit_cases (q := { p with main := g }) hg rfl size budget ctx mem with ⟨-, hn⟩ | ⟨-, hs⟩
  · exact absurd hok hn
  · exact hs hreg

/-- **`cx_init` establishes the heap invariant** when the part of the region
Lir uses is readable and writable and its checks accept the region, at
every clock. -/
theorem cxInit_ok_lir {p : Program} {g : FunId} (hg : p.funcs[g]? = some cxInit) {size budget ctx : Word}
    {mem : Memory} (hok : RegionOk ctx size) (hreg : LirRegion mem ctx size) :
    ∃ left mem', (∀ k, eval { p with main := g } k [size, budget] mem ctx = .ok ([left], mem')) ∧
      InitPost ctx budget mem mem' := by
  rcases cxInit_cases_lir (q := { p with main := g }) hg rfl size budget ctx mem with ⟨-, hn⟩ | ⟨-, hs⟩
  · exact absurd hok hn
  · exact hs hreg

end Compilatrix.Rt.Proof
