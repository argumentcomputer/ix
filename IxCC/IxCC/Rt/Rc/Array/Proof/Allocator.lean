import IxCC.Rt.Rc.Array.Proof.Alloc
import IxCC.Rt.Rc.Array.Proof.Call
import IxCC.Rt.Rc.Proof.FreeList

/-! # The allocator across a procedure: frames, allocated cells, and recycling

`ArrayAllocator` reads few bytes: the bump and limit words and the 71 free-list heads in the
context block, and the link word of every free cell (`AllocBytes`). A store anywhere else keeps it
(`ArrayAllocator.frame`). A cell is `Allocated` when its bytes lie in the arena below the bump
pointer and apart from every free cell; such a cell's bytes are never the allocator's
(`Allocated.not_allocBytes`), so a procedure that writes only into allocated cells keeps the
allocator.

Recycling a cell pushes it on its class's free list (`ArrayAllocator.push_free`): the inverse of
the allocator's pop, with the two stores the release makes (`Procs.recycleParent`). -/

set_option autoImplicit false

namespace IxCC.Rt.Rc.Array

open Lir
open IxCC.Rt.Proof (WordAt addr_toNat write?_ok wordAt_write64)
open IxCC.Rt.Rc (maxClass classWords classBytes classWords_pos)
open IxCC.Rt.Rc.Procs (FreeChain freeHeadAddress bumpAddress limitAddress recycleParent
  recycled_head)
open IxCC.X86 (Memory)

/-- The bytes `ArrayAllocator` reads: the context block from the bump word to the last free-list
head, and the link word of each free cell. -/
def AllocBytes (context : Word) (lists : Nat → List Word) : Nat → Prop :=
  fun k => (context.toNat - 40 ≤ k ∧ k < context.toNat + 8 * (maxClass + 1)) ∨
    ∃ c a, a ∈ lists c ∧ a.toNat ≤ k ∧ k < a.toNat + 8

/-- `n` bytes at `addr` are allocated: in the arena below the bump pointer, apart from every free
cell. -/
def Allocated (base bump : Word) (lists : Nat → List Word) (addr : Word) (n : Nat) : Prop :=
  base.toNat ≤ addr.toNat ∧ addr.toNat + n ≤ bump.toNat ∧
    ∀ c a, a ∈ lists c → a.toNat + classBytes c ≤ addr.toNat ∨ addr.toNat + n ≤ a.toNat

private theorem classBytes_ge_8 {c : Nat} (h : 1 ≤ c) : 8 ≤ classBytes c := by
  have := classWords_pos h; unfold classBytes; omega

theorem Allocated.not_allocBytes {mem : Memory} {context base bump limit : Word}
    {lists : Nat → List Word} (h : ArrayAllocator mem context base bump limit lists) {addr : Word}
    {n : Nat} (ha : Allocated base bump lists addr n) :
    ∀ k, addr.toNat ≤ k → k < addr.toNat + n → ¬ AllocBytes context lists k := by
  intro k h1 h2 hk
  have hcb := h.context_before
  rcases hk with ⟨_, hk⟩ | ⟨c, a, hmem, hk1, hk2⟩
  · have := ha.1; omega
  · have hpos := (h.free_cls_pos c a hmem).1
    have h8 := classBytes_ge_8 hpos
    rcases ha.2.2 c a hmem with hs | hs <;> omega

/-- A store outside the allocator's bytes keeps it. -/
theorem ArrayAllocator.frame {m m' : Memory} {context base bump limit : Word}
    {lists : Nat → List Word} (h : ArrayAllocator m context base bump limit lists)
    {t : Nat → Prop} (hf : MemFrame m m' t) (hout : ∀ k, t k → ¬ AllocBytes context lists k) :
    ArrayAllocator m' context base bump limit lists := by
  have hcl := h.context_lower
  have hcf := h.context_fit
  have hbn := h.bump_toNat
  have hln := h.limit_toNat
  refine ⟨h.context_lower, h.context_fit, h.context_before, h.base_le_bump, h.bump_le_limit,
    h.limit_fit, h.bump_aligned, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.free_distinct, h.free_cls_pos,
    h.free_in_arena, h.free_disjoint⟩
  · exact hf.wordAt h.bump_word (by omega)
      (fun k h1 h2 ht => hout k ht (Or.inl ⟨by omega, by unfold maxClass; omega⟩))
  · exact hf.wordAt h.limit_word (by omega)
      (fun k h1 h2 ht => hout k ht (Or.inl ⟨by omega, by unfold maxClass; omega⟩))
  · intro j hj; rw [hf.writable]; exact h.bump_writable j hj
  · intro a ha1 ha2; rw [hf.readable, hf.writable]; exact h.arena_access a ha1 ha2
  · intro c hc1 hc2
    have hhn := h.freeHead_toNat hc2
    exact hf.wordAt (h.free_heads c hc1 hc2) (by omega)
      (fun k h1 h2 ht => hout k ht (Or.inl ⟨by omega, by unfold maxClass at hc2 ⊢; omega⟩))
  · intro c hc1 hc2 j hj; rw [hf.writable]; exact h.head_writable c hc1 hc2 j hj
  · intro c
    exact hf.freeChain (lists c) (h.free_chains c) (fun a ha => by
      have hin := h.free_in_arena c a ha
      have hbl := h.bump_le_limit
      have hlf := h.limit_fit
      have h8 := classBytes_ge_8 (h.free_cls_pos c a ha).1
      exact ⟨by omega, fun k h1 h2 ht => hout k ht (Or.inr ⟨c, a, ha, h1, h2⟩)⟩)

/-- The free lists with `addr` pushed on class `cls`. -/
def pushFree (lists : Nat → List Word) (cls : Nat) (addr : Word) : Nat → List Word :=
  fun c => if c = cls then addr :: lists cls else lists c

/-- Recycling an allocated cell of class `cls` onto its free list keeps the allocator, with the
cell pushed. The two stores are the release's: the old head into the cell's first word, the cell
into the head. -/
theorem ArrayAllocator.push_free {mem : Memory} {context base bump limit : Word}
    {lists : Nat → List Word} (h : ArrayAllocator mem context base bump limit lists)
    {cls : Nat} {addr : Word} (hc1 : 1 ≤ cls) (hc2 : cls ≤ maxClass)
    (ha : Allocated base bump lists addr (classBytes cls)) (haligned : addr.toNat % 8 = 0)
    (hnz : addr ≠ 0) :
    mem.write? .w64 addr ((lists cls).headD 0) = .ok (mem.write .w64 addr ((lists cls).headD 0)) ∧
    (mem.write .w64 addr ((lists cls).headD 0)).write? .w64 (freeHeadAddress context (UInt64.ofNat cls))
        addr = .ok (recycleParent mem context (UInt64.ofNat cls) addr ((lists cls).headD 0)) ∧
    ArrayAllocator (recycleParent mem context (UInt64.ofNat cls) addr ((lists cls).headD 0))
      context base bump limit (pushFree lists cls addr) := by
  have hcl := h.context_lower
  have hcf := h.context_fit
  have hcb := h.context_before
  have hbl := h.bump_le_limit
  have hlf := h.limit_fit
  have hbn := h.bump_toNat
  have hln := h.limit_toNat
  have h8 := classBytes_ge_8 hc1
  have hhn := h.freeHead_toNat hc2
  obtain ⟨hlo, hhi, hsep⟩ := ha
  have hacc : ∀ j < 8, mem.readable (addr + UInt64.ofNat j) = true ∧
      mem.writable (addr + UInt64.ofNat j) = true := by
    intro j hj
    have hja : (addr + UInt64.ofNat j).toNat = addr.toNat + j := addr_toNat (by omega)
    exact h.arena_access _ (by omega) (by omega)
  have hw1 : mem.write? .w64 addr ((lists cls).headD 0) = .ok (mem.write .w64 addr ((lists cls).headD 0)) :=
    write?_ok (fun j hj => by
      have hj8 : j < 8 := by simpa [X86.Width.bytes] using hj
      exact (hacc j hj8).2)
  have hw2 : (mem.write .w64 addr ((lists cls).headD 0)).write? .w64 (freeHeadAddress context (UInt64.ofNat cls)) addr =
      .ok (recycleParent mem context (UInt64.ofNat cls) addr ((lists cls).headD 0)) := by
    have := write?_ok (m := mem.write .w64 addr ((lists cls).headD 0)) (w := .w64) (a := freeHeadAddress context (UInt64.ofNat cls)) (v := addr)
      (fun j hj => by
        have hj8 : j < 8 := by simpa [X86.Width.bytes] using hj
        simpa [Memory.write] using h.head_writable cls hc1 hc2 j hj8)
    simpa [recycleParent] using this
  refine ⟨hw1, hw2, ?_⟩
  let mem' := recycleParent mem context (UInt64.ofNat cls) addr ((lists cls).headD 0)
  have hperm_r : mem'.readable = mem.readable := by simp [mem', recycleParent, Memory.write]
  have hperm_w : mem'.writable = mem.writable := by simp [mem', recycleParent, Memory.write]
  -- the two stores, as a frame
  have hfr : MemFrame mem mem' (fun k => (addr.toNat ≤ k ∧ k < addr.toNat + 8) ∨
      ((freeHeadAddress context (UInt64.ofNat cls)).toNat ≤ k ∧ k < (freeHeadAddress context (UInt64.ofNat cls)).toNat + 8)) := by
    have f1 := MemFrame.write mem .w64 addr ((lists cls).headD 0) (by simp [X86.Width.bytes]; omega)
    have f2 := MemFrame.write (mem.write .w64 addr ((lists cls).headD 0)) .w64 (freeHeadAddress context (UInt64.ofNat cls)) addr
      (by simp [X86.Width.bytes]; omega)
    exact (f1.mono (fun k hk => Or.inl (by unfold Span at hk; simpa [X86.Width.bytes] using hk))).trans
      (f2.mono (fun k hk => Or.inr (by unfold Span at hk; simpa [X86.Width.bytes] using hk)))
  have hmem_new : ∀ c a, a ∈ pushFree lists cls addr c → (c = cls ∧ a = addr) ∨ a ∈ lists c := by
    intro c a hm
    by_cases hce : c = cls
    · subst hce
      simp only [pushFree, ite_true, List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr hm
    · simp only [pushFree, hce, ite_false] at hm; exact Or.inr hm
  have hnot_old : addr ∉ lists cls := by
    intro hm
    rcases hsep cls addr hm with hs | hs <;> omega
  refine ⟨h.context_lower, h.context_fit, h.context_before, h.base_le_bump, h.bump_le_limit,
    h.limit_fit, h.bump_aligned, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hfr.wordAt h.bump_word (by omega) (fun k h1 h2 hk => by
      rcases hk with hk | hk <;> omega)
  · exact hfr.wordAt h.limit_word (by omega) (fun k h1 h2 hk => by
      rcases hk with hk | hk <;> omega)
  · intro j hj; rw [hperm_w]; exact h.bump_writable j hj
  · intro a ha1 ha2; rw [hperm_r, hperm_w]; exact h.arena_access a ha1 ha2
  · intro c hcc1 hcc2
    by_cases hce : c = cls
    · subst hce
      simp only [pushFree, ite_true, List.headD_cons]
      exact recycled_head (fun j hj => by
        simpa [Memory.write] using (h.free_heads c hcc1 hcc2).readable j hj)
    · simp only [pushFree, hce, ite_false]
      have hhc := h.freeHead_toNat hcc2
      exact hfr.wordAt (h.free_heads c hcc1 hcc2) (by omega) (fun k h1 h2 hk => by
        rcases hk with hk | hk <;> omega)
  · intro c hcc1 hcc2 j hj; rw [hperm_w]; exact h.head_writable c hcc1 hcc2 j hj
  · intro c
    have hfit_chain : ∀ a ∈ lists c, a.toNat + 8 ≤ 2 ^ 64 := by
      intro a ha'
      have := h.free_in_arena c a ha'
      have := classBytes_ge_8 (h.free_cls_pos c a ha').1
      omega
    have hsep_chain : ∀ a ∈ lists c,
        (a.toNat + 8 ≤ addr.toNat ∨ addr.toNat + 8 ≤ a.toNat) ∧
        (a.toNat + 8 ≤ (freeHeadAddress context (UInt64.ofNat cls)).toNat ∨ (freeHeadAddress context (UInt64.ofNat cls)).toNat + 8 ≤ a.toNat) := by
      intro a ha'
      have hin := h.free_in_arena c a ha'
      have h8c := classBytes_ge_8 (h.free_cls_pos c a ha').1
      refine ⟨by rcases hsep c a ha' with hs | hs <;> omega, Or.inr (by omega)⟩
    by_cases hce : c = cls
    · subst hce
      simp only [pushFree, ite_true]
      exact (h.free_chains c).recycle_push (fun j hj => (hacc j hj).1) (by omega)
        (by omega) (Or.inr (by omega)) hfit_chain hsep_chain
    · simp only [pushFree, hce, ite_false]
      exact (h.free_chains c).recycle_frame (by omega) (by omega)
        hfit_chain hsep_chain
  · intro c
    by_cases hce : c = cls
    · subst hce
      simp only [pushFree, ite_true]
      exact List.nodup_cons.mpr ⟨hnot_old, h.free_distinct c⟩
    · simp only [pushFree, hce, ite_false]; exact h.free_distinct c
  · intro c a hm
    rcases hmem_new c a hm with ⟨rfl, rfl⟩ | hm
    · exact ⟨hc1, hc2⟩
    · exact h.free_cls_pos c a hm
  · intro c a hm
    rcases hmem_new c a hm with ⟨rfl, rfl⟩ | hm
    · exact ⟨hlo, hhi, haligned, hnz⟩
    · exact h.free_in_arena c a hm
  · intro c₁ c₂ a₁ a₂ hm₁ hm₂
    rcases hmem_new c₁ a₁ hm₁ with ⟨rfl, rfl⟩ | ho₁ <;>
      rcases hmem_new c₂ a₂ hm₂ with ⟨rfl, rfl⟩ | ho₂
    · exact Or.inl ⟨rfl, rfl⟩
    · rcases hsep c₂ a₂ ho₂ with hs | hs
      · exact Or.inr (Or.inr hs)
      · exact Or.inr (Or.inl hs)
    · rcases hsep c₁ a₁ ho₁ with hs | hs
      · exact Or.inr (Or.inl hs)
      · exact Or.inr (Or.inr hs)
    · exact h.free_disjoint c₁ c₂ a₁ a₂ ho₁ ho₂

end IxCC.Rt.Rc.Array
