import IxCC.Rt.Proof.Heap

/-!
# The immortal bump allocation keeps the heap invariant

`Rt.lower`'s allocation stores the new bump pointer, the header as two
32-bit halves, and the fields, into a cell that fits below the limit. This
module proves the memory those stores leave satisfies `HeapAt` for the heap
with the new cell appended, placed at the old bump pointer
(`alloc_mem`), and that each store is allowed (`alloc_writable`). -/

set_option autoImplicit false

namespace IxCC.Rt.Proof

open IxCC.X86 (Memory)
open IxCC.Lir (Word)
open IxCC.Rt.Lower (Tables)

/-- The field stores of a cell at `a`, from field `i`. -/
def storeFields (m : Memory) (a : Word) : Nat → List Word → Memory
  | _, [] => m
  | i, w :: ws => storeFields (m.write .w64 (a + UInt64.ofNat (8 + 8 * i)) w) a (i + 1) ws

@[simp] theorem storeFields_readable (m : Memory) (a : Word) :
    ∀ (i : Nat) (ws : List Word), (storeFields m a i ws).readable = m.readable
  | _, [] => rfl
  | i, w :: ws => by simp [storeFields, storeFields_readable _ a (i + 1) ws, Memory.write]

@[simp] theorem storeFields_writable (m : Memory) (a : Word) :
    ∀ (i : Nat) (ws : List Word), (storeFields m a i ws).writable = m.writable
  | _, [] => rfl
  | i, w :: ws => by simp [storeFields, storeFields_writable _ a (i + 1) ws, Memory.write]

/-- A word outside the fields' range survives the field stores. -/
theorem storeFields_keeps {m : Memory} {a b v : Word} (hb : b.toNat + 8 ≤ 2 ^ 64) :
    ∀ (i : Nat) (ws : List Word), a.toNat + 8 + 8 * (i + ws.length) ≤ 2 ^ 64 →
      (b.toNat + 8 ≤ a.toNat + 8 + 8 * i ∨ a.toNat + 8 + 8 * (i + ws.length) ≤ b.toNat) →
      WordAt m b v → WordAt (storeFields m a i ws) b v
  | _, [], _, _, h => h
  | i, w :: ws, hfit, hd, h => by
    simp only [storeFields]
    apply storeFields_keeps hb (i + 1) ws (by simp at hfit ⊢; omega) (by simp at hd ⊢; omega)
    apply h.write_disjoint
    · rw [addr_toNat (by simp at hfit; omega)]; simp [X86.Width.bytes] at hfit ⊢; omega
    · exact hb
    · rw [addr_toNat (by simp at hfit; omega)]; simp [X86.Width.bytes] at hd ⊢; omega

/-- Field `i + j` holds the `j`-th stored word. -/
theorem storeFields_word {m : Memory} {a : Word} :
    ∀ (i : Nat) (ws : List Word), a.toNat + 8 + 8 * (i + ws.length) ≤ 2 ^ 64 →
      (∀ k : Nat, a.toNat + 8 + 8 * i ≤ k → k < a.toNat + 8 + 8 * (i + ws.length) →
        m.readable (UInt64.ofNat k) = true) →
      ∀ (j : Nat) (w : Word), ws[j]? = some w → WordAt (storeFields m a i ws) (a + UInt64.ofNat (8 + 8 * (i + j))) w
  | _, [], _, _, j, w, hj => by simp at hj
  | i, w' :: ws, hfit, hr, j, w, hj => by
    simp only [storeFields]
    have hfit' : a.toNat + 8 + 8 * i + 8 ≤ 2 ^ 64 := by simp at hfit; omega
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      apply storeFields_keeps (by rw [addr_toNat (by omega)]; omega) (i + 1) ws (by simp at hfit ⊢; omega)
        (by rw [addr_toNat (by omega)]; omega)
      simp only [Nat.add_zero]
      apply wordAt_write64
      intro k hk
      rw [show a + UInt64.ofNat (8 + 8 * i) + UInt64.ofNat k = UInt64.ofNat (a.toNat + 8 + 8 * i + k) by
        apply UInt64.toNat_inj.mp
        rw [addr_toNat (by rw [addr_toNat (by omega)]; omega), addr_toNat (by omega), UInt64.toNat_ofNat',
          Nat.mod_eq_of_lt (by omega)]
        omega]
      exact hr _ (by omega) (by simp at hfit ⊢; omega)
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      have := storeFields_word (m := m.write .w64 (a + UInt64.ofNat (8 + 8 * i)) w') (a := a) (i + 1) ws
        (by simp at hfit ⊢; omega)
        (fun k hk hk' => by simpa [Memory.write] using hr k (by omega) (by simp at hk' ⊢; omega)) j w hj
      rwa [show i + 1 + j = i + (j + 1) by omega] at this

theorem ctx_sub_toNat {ctx : Word} {k : Nat} (h : 64 ≤ ctx.toNat) (hk : k ≤ 64) :
    (ctx - UInt64.ofNat k).toNat = ctx.toNat - k := by
  rw [sub_toNat_of_le (by rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega),
    UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

theorem ctx40_toNat {ctx : Word} (h : 64 ≤ ctx.toNat) : (ctx - 40).toNat = ctx.toNat - 40 :=
  ctx_sub_toNat (k := 40) h (by omega)

theorem ctx32_toNat {ctx : Word} (h : 64 ≤ ctx.toNat) : (ctx - 32).toNat = ctx.toNat - 32 :=
  ctx_sub_toNat (k := 32) h (by omega)

/-- The immortal header is the word of its two 32-bit halves. -/
theorem immortalHeader_halves {n tag : Nat} (hn : n ≤ maxFields) (ht : tag ≤ maxTag) :
    UInt64.ofNat ((UInt64.ofNat (headerLow n 0 tag)).toNat + 2 ^ 32 * (UInt64.ofNat immortalRc).toNat) =
      immortalHeader n tag := by
  unfold immortalHeader header
  congr 1
  unfold headerLow maxFields maxTag immortalRc at *
  rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The memory after the allocation's stores: the bump pointer `e` at
`ctx − 40`, the header halves `lo`, `hi` at `a`, the fields `ws` after
them. -/
def allocStores (m : Memory) (ctx a e lo hi : Word) (ws : List Word) : Memory :=
  storeFields (((m.write .w64 (ctx - 40) e).write .w32 a lo).write .w32 (a + 4) hi) a 0 ws

@[simp] theorem allocStores_readable (m : Memory) (ctx a e lo hi : Word) (ws : List Word) :
    (allocStores m ctx a e lo hi ws).readable = m.readable := by
  simp [allocStores, Memory.write]

@[simp] theorem allocStores_writable (m : Memory) (ctx a e lo hi : Word) (ws : List Word) :
    (allocStores m ctx a e lo hi ws).writable = m.writable := by
  simp [allocStores, Memory.write]

theorem add4_toNat {a : Word} (h : a.toNat + 8 ≤ 2 ^ 64) : (a + 4).toNat = a.toNat + 4 := by
  rw [UInt64.toNat_add]
  simp
  omega

/-- A word away from the bump pointer's word and below the new cell
survives the allocation's stores. -/
theorem allocStores_keep {m : Memory} {ctx a e lo hi b v : Word} {ws : List Word} (hw : WordAt m b v)
    (hctx : 64 ≤ ctx.toNat) (ha : a.toNat + 8 + 8 * ws.length < 2 ^ 63) (hb : b.toNat + 8 ≤ a.toNat)
    (hd : ctx.toNat - 32 ≤ b.toNat ∨ b.toNat + 8 ≤ ctx.toNat - 40) :
    WordAt (allocStores m ctx a e lo hi ws) b v := by
  have h40 := ctx40_toNat hctx
  have h4 := add4_toNat (a := a) (by omega)
  have hb64 := word_lt b
  have hc64 := word_lt ctx
  unfold allocStores
  apply storeFields_keeps (by omega) 0 ws (by omega) (by omega)
  apply WordAt.write_disjoint _ (by rw [h4]; simp only [X86.Width.bytes]; omega) (by omega)
    (by rw [h4]; simp only [X86.Width.bytes]; omega)
  apply WordAt.write_disjoint _ (by simp only [X86.Width.bytes]; omega) (by omega)
    (by simp only [X86.Width.bytes]; omega)
  exact hw.write_disjoint (by rw [h40]; simp only [X86.Width.bytes]; omega) (by omega)
    (by rw [h40]; simp only [X86.Width.bytes]; omega)

/-- The bump pointer's word holds the new bump pointer. -/
theorem allocStores_bump {m : Memory} {ctx a e lo hi : Word} {ws : List Word}
    (hr : ∀ i < 8, m.readable (ctx - 40 + UInt64.ofNat i) = true)
    (hctx : 64 ≤ ctx.toNat) (ha : a.toNat + 8 + 8 * ws.length < 2 ^ 63) (hlo : ctx.toNat + 576 ≤ a.toNat) :
    WordAt (allocStores m ctx a e lo hi ws) (ctx - 40) e := by
  have h40 := ctx40_toNat hctx
  have h4 := add4_toNat (a := a) (by omega)
  unfold allocStores
  apply storeFields_keeps (by omega) 0 ws (by omega) (by omega)
  apply WordAt.write_disjoint _ (by rw [h4]; simp only [X86.Width.bytes]; omega) (by omega)
    (by rw [h4]; simp only [X86.Width.bytes]; omega)
  apply WordAt.write_disjoint _ (by simp only [X86.Width.bytes]; omega) (by omega)
    (by simp only [X86.Width.bytes]; omega)
  exact wordAt_write64 hr

/-- The new cell's header. -/
theorem allocStores_header {m : Memory} {ctx a e : Word} {ws : List Word} {n tag : Nat}
    (hr : ∀ k : Nat, a.toNat ≤ k → k < a.toNat + 8 → m.readable (UInt64.ofNat k) = true)
    (hctx : 64 ≤ ctx.toNat) (ha : a.toNat + 8 + 8 * ws.length < 2 ^ 63) (hlo : ctx.toNat + 576 ≤ a.toNat)
    (hn : n ≤ maxFields) (ht : tag ≤ maxTag) :
    WordAt (allocStores m ctx a e (UInt64.ofNat (headerLow n 0 tag)) (UInt64.ofNat immortalRc) ws) a
      (immortalHeader n tag) := by
  have h40 := ctx40_toNat hctx
  unfold allocStores
  apply storeFields_keeps (by omega) 0 ws (by omega) (by omega)
  rw [← immortalHeader_halves hn ht]
  apply wordAt_write32_pair
    (by rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by unfold headerLow maxFields maxTag at *; omega)]
        unfold headerLow maxFields maxTag at *; omega)
    (by rw [UInt64.toNat_ofNat']; decide) (by omega)
  intro i hi
  simp only [Memory.write, writeLittle_readable]
  rw [show a + UInt64.ofNat i = UInt64.ofNat (a.toNat + i) by
    apply UInt64.toNat_inj.mp
    rw [addr_toNat (by omega), UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]]
  exact hr _ (by omega) (by omega)

/-- The new cell's fields. -/
theorem allocStores_field {m : Memory} {ctx a e lo hi : Word} {ws : List Word}
    (hr : ∀ k : Nat, a.toNat + 8 ≤ k → k < a.toNat + 8 + 8 * ws.length → m.readable (UInt64.ofNat k) = true)
    (ha : a.toNat + 8 + 8 * ws.length < 2 ^ 63) {i : Nat} {w : Word} (hw : ws[i]? = some w) :
    WordAt (allocStores m ctx a e lo hi ws) (a + UInt64.ofNat (8 + 8 * i)) w := by
  unfold allocStores
  have := storeFields_word (m := ((m.write .w64 (ctx - 40) e).write .w32 a lo).write .w32 (a + 4) hi) (a := a)
    0 ws (by omega) (fun k hk hk' => by simpa [Memory.write] using hr k (by omega) (by omega)) i w hw
  rwa [Nat.zero_add] at this

/-- **The immortal bump allocation keeps the heap invariant**: after the
bump pointer is advanced and the header and fields stored, the heap with
the new cell, placed at the old bump pointer, satisfies `HeapAt` with the
new bump pointer. -/
theorem alloc_mem {T : Tables} {P : List Word} {H : Own.Heap} {ctx : Word} {m : Memory} {bump limit : Word}
    (h : HeapAt T P H ctx m bump limit) {c : Fir.CtorInfo} {vs : List Own.RVal} {ws : List Word}
    (hc : CtorOk T c) (hfl : c.fieldless = false) (hn : vs.length = c.arity) (hsmall : vs.length ≤ maxFields)
    (hvw : ListRel (ValRel T P) vs ws) (hfit : bump.toNat + cellSize vs.length ≤ limit.toNat) :
    HeapAt T (P ++ [bump]) { cells := H.cells.push (.live 1 .static { ctor := c, fields := vs }) } ctx
      (allocStores m ctx bump (bump + UInt64.ofNat (cellSize vs.length)) (UInt64.ofNat (headerLow vs.length 0 c.tag))
        (UInt64.ofNat immortalRc) ws)
      (bump + UInt64.ofNat (cellSize vs.length)) limit := by
  have hlen := hvw.length_eq
  have hctx := h.ctxLo
  have h40 := ctx40_toNat hctx
  have h32 := ctx32_toNat hctx
  have hstart := h.start
  have hlim := h.limitLt
  have hfit' : bump.toNat + 8 + 8 * ws.length ≤ limit.toNat := by
    rw [← hlen]; simp only [cellSize] at hfit; omega
  have he : (bump + UInt64.ofNat (cellSize vs.length)).toNat = bump.toNat + 8 + 8 * ws.length := by
    rw [addr_toNat (by simp only [cellSize]; omega)]; rw [← hlen]; simp only [cellSize]; omega
  refine {
    len := by simp [h.len]
    ctxLo := hctx
    bumpWord := allocStores_bump h.bumpWord.readable hctx (by omega) hstart
    bumpWritable := fun i hi => by rw [allocStores_writable]; exact h.bumpWritable i hi
    limitWord := allocStores_keep h.limitWord hctx (by omega) (by rw [h32]; omega) (.inl (by rw [h32]; exact Nat.le_refl _))
    start := by rw [he]; omega
    bumpLe := by rw [he]; omega
    limitLt := hlim
    bumpAligned := by rw [he]; have := h.bumpAligned; omega
    free := fun k hk hk' => by
      rw [allocStores_readable, allocStores_writable]
      exact h.free k (by rw [he] at hk; omega) hk'
    cells := ?_
    ordered := ?_ }
  · intro ℓ hℓ
    simp only [Array.size_push] at hℓ
    by_cases hold : ℓ < H.cells.size
    · obtain ⟨a, rc, b, hP, hH, hcell, hlo, hhi⟩ := h.cells ℓ hold
      simp only [cellSize] at hhi
      refine ⟨a, rc, b, ?_, ?_, ?_, hlo, by simp only [cellSize]; rw [he]; omega⟩
      · rw [List.getElem?_append_left (by rw [h.len]; exact hold)]; exact hP
      · rw [Array.getElem?_push_lt hold]; rw [Array.getElem?_eq_getElem hold] at hH; exact hH
      · refine { ctor := hcell.ctor, fieldless := hcell.fieldless, arity := hcell.arity, small := hcell.small,
                 aligned := hcell.aligned, header := ?_, fields := ?_ }
        · exact allocStores_keep hcell.header hctx (by omega) (by omega) (.inl (by omega))
        · intro i v hv
          obtain ⟨w, hw, hvw'⟩ := hcell.fields i v hv
          have hi : i < b.fields.length := (List.getElem?_eq_some_iff.1 hv).1
          refine ⟨w, allocStores_keep hw hctx (by omega) ?_ (.inl ?_), ValRel.mono ⟨[bump], rfl⟩ hvw'⟩
          · rw [addr_toNat (by omega)]; omega
          · rw [addr_toNat (by omega)]; omega
    · have hℓ' : ℓ = H.cells.size := by omega
      subst hℓ'
      refine ⟨bump, 1, { ctor := c, fields := vs }, ?_, ?_, ?_, hstart, by simp only [cellSize]; rw [he, hlen]; omega⟩
      · rw [List.getElem?_append_right (by simp [h.len]), h.len]; simp
      · rw [Array.getElem?_push_size]
      · refine { ctor := hc, fieldless := hfl, arity := hn, small := hsmall, aligned := h.bumpAligned,
                 header := ?_, fields := ?_ }
        · exact allocStores_header (fun k hk hk' => (h.free k hk (by omega)).1) hctx (by omega) hstart hsmall hc.tag
        · intro i v hv
          obtain ⟨w, hw, hvw'⟩ := hvw.get hv
          exact ⟨w, allocStores_field (fun k hk hk' => (h.free k (by omega) (by omega)).1) (by omega) hw,
            ValRel.mono ⟨[bump], rfl⟩ hvw'⟩
  · intro ℓ ℓ' a a' rc b hlt hP hP' hH
    have hlen' := (List.getElem?_eq_some_iff.1 hP').1
    simp only [List.length_append, List.length_cons, List.length_nil, h.len] at hlen'
    have hℓ : ℓ < H.cells.size := by omega
    rw [Array.getElem?_push_lt hℓ] at hH
    rw [List.getElem?_append_left (by rw [h.len]; exact hℓ)] at hP
    have hH' : H.cells[ℓ]? = some (.live rc .static b) := by
      rw [Array.getElem?_eq_getElem hℓ]; exact hH
    by_cases hℓ' : ℓ' < H.cells.size
    · rw [List.getElem?_append_left (by rw [h.len]; exact hℓ')] at hP'
      exact h.ordered ℓ ℓ' a a' rc b hlt hP hP' hH'
    · have hl' : ℓ' = H.cells.size := by omega
      subst hl'
      rw [List.getElem?_append_right (by simp [h.len]), h.len] at hP'
      simp at hP'
      subst hP'
      obtain ⟨a₀, rc₀, b₀, hP₀, hH₀, _, _, hhi⟩ := h.cells ℓ hℓ
      rw [hP] at hP₀
      cases hP₀
      rw [hH'] at hH₀
      simp only [Option.some.injEq, Own.Cell.live.injEq] at hH₀
      obtain ⟨rfl, -, rfl⟩ := hH₀
      exact hhi

end IxCC.Rt.Proof
