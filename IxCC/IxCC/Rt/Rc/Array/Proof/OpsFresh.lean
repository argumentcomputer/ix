import IxCC.Rt.Rc.Array.Proof.OpsInPlace

/-! # A fresh copy of a run of elements

The copying paths of `set`, `push`, `pop` and `extract`, and the growth of `push`, all allocate a
cell of the source's kind, copy a run of the source's elements into it, and store its size.
`fresh_copy` is that, at the level of memory: from the allocation's result (`AllocDone`) and a
live source cell, the copy's preconditions hold, and after the copy and the size store the fresh
cell holds the run, the source is untouched, and the allocator is kept.

`FnsOk P t k`: the program holds every procedure an array operation of kind `k` calls, at the
indices the table `t` names. -/

set_option autoImplicit false

namespace IxCC.Rt.Rc.Array

open Lir
open IxCC.Rt.Proof (WordAt addr_toNat write?_ok wordAt_write64)
open IxCC.Rt.Rc (maxClass classBytes classWords maxCount)
open IxCC.Rt.Rc.Procs (v i to cellAddr storeCount)
open IxCC.X86 (Memory)
open Ops

/-- The program holds the procedures an operation of kind `k` calls, where `t` says. -/
structure FnsOk (P : Program) (t : Fns) (k : ElemKind) : Prop where
  inc : P.funcs[t.inc]? = some IxCC.Rt.Rc.Procs.inc
  dec : P.funcs[t.dec]? = some IxCC.Rt.Rc.Gen.decArr
  classFor : P.funcs[t.classFor]? = some arrClassFor
  classWords : P.funcs[t.classWords]? = some arrClassWords
  alloc : P.funcs[t.alloc]? = some (alloc t k)
  copy : P.funcs[t.copy]? = some (copy k)
  incs : P.funcs[t.incs]? = some (incs t)

/-- An allocation's request is met: its class has a free cell, or room below the limit. -/
def AllocRoom (bump limit : Word) (lists : Nat → List Word) (k : ElemKind) (n : Nat) : Prop :=
  lists (allocClass k n) ≠ [] ∨ bump.toNat + classBytes (allocClass k n) ≤ limit.toNat

/-- The bytes of the cell at `addr` of class `cls`. -/
def CellBytes (addr : Word) (cls : Nat) : Nat → Prop :=
  fun x => addr.toNat ≤ x ∧ x < addr.toNat + classBytes cls

/-- The source survives the allocation. -/
theorem AllocDone.arrCell {mem m1 : Memory} {ctx base bump limit : Word}
    {lists lists' : Nat → List Word} {k : ElemKind} {cls' : Nat} {b bump' : Word}
    (hd : AllocDone mem m1 ctx base bump limit lists k cls' b bump' lists')
    (halloc : ArrayAllocator mem ctx base bump limit lists) {a : Word} {refs cls cap : Nat}
    {k' : ElemKind} {xs : List Word} (h : ArrCell mem a refs cls cap k' xs)
    (ha : Allocated base bump lists a (classBytes cls)) :
    ArrCell m1 a refs cls cap k' xs ∧ Allocated base bump' lists' a (classBytes cls) ∧
      (a.toNat + classBytes cls ≤ b.toNat ∨ b.toNat + classBytes cls' ≤ a.toNat) := by
  obtain ⟨ha', hsep⟩ := hd.keeps a _ ha
  refine ⟨hd.frame.arrCell h (fun x h1 h2 hx => ?_), ha', hsep⟩
  rcases hx with hx | hx
  · exact ha.not_allocBytes halloc x h1 h2 hx
  · rcases hsep with hs | hs <;> omega

/-- **A fresh copy.** The copy's preconditions after the allocation, and the cells after the copy
and the size store. -/
theorem fresh_copy {mem m1 : Memory} {ctx base bump limit : Word}
    {lists lists' : Nat → List Word} {k : ElemKind} {cls' : Nat} {b bump' : Word}
    (hd : AllocDone mem m1 ctx base bump limit lists k cls' b bump' lists')
    (halloc : ArrayAllocator mem ctx base bump limit lists)
    (hlo : minArrayClass ≤ cls') (hhi : cls' ≤ maxClass)
    {a : Word} {refs cls cap : Nat} {xs : List Word} (h : ArrCell mem a refs cls cap k xs)
    (ha : Allocated base bump lists a (classBytes cls)) {off n : Nat} (hn : off + n ≤ xs.length)
    (hcap : n ≤ k.capOfClass cls') :
    (n ≤ (xs.drop off).length) ∧
    (a.toNat + (arrayPayloadOffset + k.bytes * (off + n)) < 2 ^ 63) ∧
    (b.toNat + (arrayPayloadOffset + k.bytes * (0 + n)) < 2 ^ 63) ∧
    ElemsAt m1 a k off (xs.drop off) ∧ ElemsFit k (xs.drop off) ∧
    (∀ j < n, ∀ c < k.bytes,
      m1.readable (elemAddr b k (0 + j) + UInt64.ofNat c) = true ∧
        m1.writable (elemAddr b k (0 + j) + UInt64.ofNat c) = true) ∧
    (∀ x, ElemRange b k 0 (0 + n) x → ¬ ElemRange a k off (off + n) x) ∧
    ∀ m2, ElemsAt m2 b k 0 ((xs.drop off).take n) → MemFrame m1 m2 (ElemRange b k 0 (0 + n)) →
      m2.write? .w64 (b + 8) (UInt64.ofNat n) = .ok (m2.write .w64 (b + 8) (UInt64.ofNat n)) ∧
      ArrCell (m2.write .w64 (b + 8) (UInt64.ofNat n)) b 1 cls' (k.capOfClass cls') k
        ((xs.drop off).take n) ∧
      ArrCell (m2.write .w64 (b + 8) (UInt64.ofNat n)) a refs cls cap k xs ∧
      ArrayAllocator (m2.write .w64 (b + 8) (UInt64.ofNat n)) ctx base bump' limit lists' ∧
      Allocated base bump' lists' a (classBytes cls) ∧
      (a.toNat + classBytes cls ≤ b.toNat ∨ b.toNat + classBytes cls' ≤ a.toNat) ∧
      MemFrame mem (m2.write .w64 (b + 8) (UInt64.ofNat n))
        (fun x => AllocBytes ctx lists x ∨ CellBytes b cls' x) := by
  obtain ⟨h1, ha1, hsep⟩ := hd.arrCell halloc h ha
  have hb := hd.cell.shell
  have hs := h1.shell
  have hbp := hb.payload_le
  have hsp := hs.payload_le
  have hbfit := hb.fit
  have hsfit := hs.fit
  have hb24 := hb.classBytes_ge_24
  have hbw : k.width.bytes = k.bytes := rfl
  have hmn : k.bytes * n ≤ k.bytes * k.capOfClass cls' := Nat.mul_le_mul_left _ hcap
  have hmon : k.bytes * (off + n) ≤ k.bytes * cap :=
    Nat.mul_le_mul_left _ (by have := hs.size_le; omega)
  have hlo' : k.bytes * off ≤ k.bytes * (off + n) := Nat.mul_le_mul_left _ (by omega)
  unfold arrayPayloadOffset at hbp hsp
  have hdrop : n ≤ (xs.drop off).length := by simp; omega
  refine ⟨hdrop, by unfold arrayPayloadOffset; omega, by rw [Nat.zero_add]; unfold arrayPayloadOffset; omega,
    h1.elems.drop off, ?_, ?_, ?_, ?_⟩
  · intro y hy; exact h1.fits y (List.mem_of_mem_drop hy)
  · intro j hj c hc
    rw [Nat.zero_add]
    obtain ⟨hja, hjb⟩ := hb.elem_toNat (j := j) (by omega)
    have := hb.access (arrayPayloadOffset + k.bytes * j + c) (by unfold arrayPayloadOffset at hjb ⊢; omega)
    have hadd : elemAddr b k j + UInt64.ofNat c = b + UInt64.ofNat (arrayPayloadOffset + k.bytes * j + c) := by
      apply UInt64.toNat_inj.mp
      rw [addr_toNat (by rw [hja]; unfold arrayPayloadOffset at hjb ⊢; omega), hja,
        addr_toNat (by unfold arrayPayloadOffset at hjb ⊢; omega)]; omega
    rw [hadd]; exact this
  · intro x hx hx'
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hx'
    unfold arrayPayloadOffset at hx1 hx2 hy1 hy2
    rw [Nat.zero_add] at hx2
    rcases hsep with hs' | hs' <;> omega
  · intro m2 hel2 hfr2
    have hfr2' : MemFrame m1 m2 (fun x => b.toNat + 24 ≤ x ∧ x < b.toNat + classBytes cls') :=
      hfr2.mono (fun x hx => by
        obtain ⟨hx1, hx2⟩ := hx; unfold arrayPayloadOffset at hx1 hx2; rw [Nat.zero_add] at hx2
        exact ⟨by omega, by omega⟩)
    have hb2 : ArrShell m2 b 1 cls' (k.capOfClass cls') k 0 := by
      have := hfr2'.arrShell hb (fun x h1 h2 hx => by omega)
      simpa using this
    have h2 : ArrCell m2 a refs cls cap k xs :=
      hfr2'.arrCell h1 (fun x h1 h2 hx => by rcases hsep with hs' | hs' <;> omega)
    have h8 := hb2.off8
    have hw := hb2.write_ok (off := 8) (w := .w64) (by simp [X86.Width.bytes]; omega) (UInt64.ofNat n)
    have hfw := MemFrame.write m2 .w64 (b + 8) (UInt64.ofNat n) (by rw [h8]; simp [X86.Width.bytes]; omega)
    have hlen : ((xs.drop off).take n).length = n := by simp; omega
    refine ⟨hw, ⟨⟨hb2.aligned, hb2.nonzero, hb2.cls_lo, hb2.cls_hi, hb2.refs_pos, hb2.refs_le,
      hb2.fit, by rw [hlen]; exact hcap, hb2.cap_fit, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ha1, hsep, ?_⟩
    · intro j hj; simpa [Memory.write] using hb2.access j hj
    · exact hfw.wordAt hb2.header_word (by omega) (fun x x1 x2 hx => by
        unfold Span at hx; rw [h8] at hx; simp [X86.Width.bytes] at hx; omega)
    · rw [hlen]; exact wordAt_write64 (fun c hc => hb2.size_word.readable c hc)
    · exact hfw.wordAt hb2.cap_word (by rw [hb2.off16]; omega) (fun x x1 x2 hx => by
        unfold Span at hx; rw [h8] at hx; rw [hb2.off16] at x1 x2; simp [X86.Width.bytes] at hx; omega)
    · have := hel2.elems
      exact hfw.elems hb2 this (by rw [hlen]; exact hcap) (fun x x1 x2 hx => by
        unfold Span at hx; rw [h8] at hx; simp [X86.Width.bytes] at hx; unfold arrayPayloadOffset at x1
        omega)
    · intro y hy; exact h1.fits y (List.mem_of_mem_drop (List.mem_of_mem_take hy))
    · exact hfw.arrCell h2 (fun x x1 x2 hx => by
        unfold Span at hx; rw [h8] at hx; simp [X86.Width.bytes] at hx
        rcases hsep with hs' | hs' <;> omega)
    · have halloc1 := hd.alloc
      exact (halloc1.frame hfr2' (fun x hx => hd.allocated.not_allocBytes halloc1 x
        (by omega) hx.2)).frame hfw (fun x hx => by
          unfold Span at hx; rw [h8] at hx; simp [X86.Width.bytes] at hx
          exact hd.allocated.not_allocBytes halloc1 x (by omega) (by omega))
    · refine (hd.frame.trans (hfr2'.mono (fun x hx => Or.inr ⟨by omega, hx.2⟩))).trans
        (hfw.mono (fun x hx => Or.inr ?_))
      unfold Span at hx; rw [h8] at hx; simp [X86.Width.bytes] at hx
      exact ⟨by omega, by omega⟩

end IxCC.Rt.Rc.Array
