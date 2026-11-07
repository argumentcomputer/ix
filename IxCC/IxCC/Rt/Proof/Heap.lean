import IxCC.Rt.Lower
import IxCC.Cfg.Semantics
import IxCC.Rt.Proof.Mem
import IxCC.Rt.Proof.Words

/-!
# The data refinement: values and the immortal heap (04 §8, §8.1)

`ValRel T P v w` relates a Cfg value to its Lir word under a placement
`P` (the address of each cell, by location: cells are appended, so `P` is a
list as long as the heap):

* a `Nat` literal is its tagged word (`natWord`, so below `2^63`);
* a field-less constructor is `2·tag + 1`, for a constructor as the table
  has it, outside `Nat`'s keys and within the tag limit (`CtorOk`);
* □ is `1`; a location is its cell's address.

`HeapAt T P H ctx m bump limit` is 04 §8.1's `HeapInv` for the Phase 1
fragment, with the bump pointer and limit the context block holds:

* the context block: `ctx ≥ 64`, the bump pointer and the limit as words at
  `ctx − 40` and `ctx − 32` (the bump pointer's bytes writable), objects
  start at `ctx + 576` or later, `bump ≤ limit < 2^63`, and `[bump, limit)`
  is readable and writable;
* every cell is live and static, placed (`P`), and `ImmortalAt` (`CellAt`):
  8-aligned, a constructor as the table has it with fields, the immortal
  header (`immortalHeader`), and fields whose words relate by `ValRel`;
* cells are ordered by location and lie in `[ctx + 576, bump)`, so they are
  pairwise disjoint and disjoint from the context block and the free area.

`HeapInv` hides the two words. `alloc_mem` proves the immortal bump
allocation keeps it; `proj_mem` and `tag_mem` read a cell's fields and
tag.
-/

set_option autoImplicit false

namespace IxCC.Rt.Proof

open IxCC.X86 (Memory)
open IxCC.Lir (Word)
open IxCC.Rt.Lower (Tables isNatKey)

/-- A constructor as the table has it, outside `Nat`'s keys, within the
tag limit. -/
structure CtorOk (T : Tables) (c : Fir.CtorInfo) : Prop where
  table : Fir.CtorInfo.ofKey T.ctors c.key = some c
  notNat : isNatKey T c.key = false
  tag : c.tag ≤ maxTag

/-- The value relation (04 §8 `ValRel`, Phase 1). -/
def ValRel (T : Tables) (P : List Word) : Own.RVal → Word → Prop
  | .lit (.nat n), w => natWord n = some w
  | .lit (.str _), _ => False
  | .ctor0 c, w => w = ctor0Word c.tag ∧ CtorOk T c ∧ c.fieldless = true
  | .erased, w => w = erasedWord
  | .loc ℓ, w => P[ℓ]? = some w

theorem ValRel.mono {T : Tables} {P P' : List Word} (hP : P <+: P') :
    ∀ {v : Own.RVal} {w : Word}, ValRel T P v w → ValRel T P' v w
  | .lit (.nat _), _, h => h
  | .lit (.str _), _, h => h
  | .ctor0 _, _, h => h
  | .erased, _, h => h
  | .loc ℓ, w, h => by
    simp only [ValRel] at h ⊢
    obtain ⟨t, rfl⟩ := hP
    rw [List.getElem?_append_left (List.lt_length_of_getElem? h)]
    exact h
where
  List.lt_length_of_getElem? {α : Type} {l : List α} {i : Nat} {x : α} (h : l[i]? = some x) : i < l.length :=
    (List.getElem?_eq_some_iff.1 h).1

/-- Two lists related elementwise. -/
inductive ListRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : ListRel R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} : R a b → ListRel R as bs → ListRel R (a :: as) (b :: bs)

namespace ListRel

variable {α β : Type} {R : α → β → Prop}

theorem length_eq {as : List α} {bs : List β} (h : ListRel R as bs) : as.length = bs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem get {as : List α} {bs : List β} (h : ListRel R as bs) :
    ∀ {i : Nat} {a : α}, as[i]? = some a → ∃ b, bs[i]? = some b ∧ R a b := by
  induction h with
  | nil => intro i a h; simp at h
  | cons hab _ ih =>
    intro i a h
    cases i with
    | zero => simp at h; subst h; exact ⟨_, rfl, hab⟩
    | succ i => simpa using ih (by simpa using h)

theorem mono {R' : α → β → Prop} (hR : ∀ a b, R a b → R' a b) {as : List α} {bs : List β}
    (h : ListRel R as bs) : ListRel R' as bs := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (hR _ _ hab) ih

end ListRel

/-- The bytes a cell with `n` fields occupies. -/
abbrev cellSize (n : Nat) : Nat := 8 * (1 + n)

/-- A cell at address `a` holding `b` (04 §8.1 `ImmortalAt`). -/
structure CellAt (T : Tables) (P : List Word) (m : Memory) (a : Word) (b : Own.Body) : Prop where
  ctor : CtorOk T b.ctor
  fieldless : b.ctor.fieldless = false
  arity : b.fields.length = b.ctor.arity
  small : b.fields.length ≤ maxFields
  aligned : a.toNat % 8 = 0
  header : WordAt m a (immortalHeader b.fields.length b.ctor.tag)
  fields : ∀ (i : Nat) (v : Own.RVal), b.fields[i]? = some v →
    ∃ w, WordAt m (a + UInt64.ofNat (8 + 8 * i)) w ∧ ValRel T P v w

/-- The heap invariant with the bump pointer and the limit the context
block holds. -/
structure HeapAt (T : Tables) (P : List Word) (H : Own.Heap) (ctx : Word) (m : Memory) (bump limit : Word) :
    Prop where
  len : P.length = H.cells.size
  ctxLo : 64 ≤ ctx.toNat
  bumpWord : WordAt m (ctx - 40) bump
  bumpWritable : ∀ i < 8, m.writable (ctx - 40 + UInt64.ofNat i) = true
  limitWord : WordAt m (ctx - 32) limit
  start : ctx.toNat + 576 ≤ bump.toNat
  bumpLe : bump.toNat ≤ limit.toNat
  limitLt : limit.toNat < 2 ^ 63
  bumpAligned : bump.toNat % 8 = 0
  free : ∀ k : Nat, bump.toNat ≤ k → k < limit.toNat →
    m.readable (UInt64.ofNat k) = true ∧ m.writable (UInt64.ofNat k) = true
  cells : ∀ ℓ, ℓ < H.cells.size → ∃ (a : Word) (rc : Nat) (b : Own.Body), P[ℓ]? = some a ∧ H.cells[ℓ]? = some (.live rc .static b) ∧
    CellAt T P m a b ∧ ctx.toNat + 576 ≤ a.toNat ∧ a.toNat + cellSize b.fields.length ≤ bump.toNat
  ordered : ∀ (ℓ ℓ' : Nat) (a a' : Word) (rc : Nat) (b : Own.Body), ℓ < ℓ' → P[ℓ]? = some a → P[ℓ']? = some a' →
    H.cells[ℓ]? = some (.live rc .static b) → a.toNat + cellSize b.fields.length ≤ a'.toNat

/-- 04 §8.1's `HeapInv`: the heap invariant for some bump pointer and
limit. -/
def HeapInv (T : Tables) (P : List Word) (H : Own.Heap) (ctx : Word) (m : Memory) : Prop :=
  ∃ bump limit, HeapAt T P H ctx m bump limit

/-! ## Reading cells -/

theorem HeapAt.cell {T : Tables} {P : List Word} {H : Own.Heap} {ctx : Word} {m : Memory} {bump limit : Word}
    (h : HeapAt T P H ctx m bump limit) {ℓ : Nat} {a : Word} {rc : Nat} {mode : Own.OMode} {b : Own.Body}
    (hP : P[ℓ]? = some a) (hH : H.cells[ℓ]? = some (.live rc mode b)) :
    mode = .static ∧ CellAt T P m a b ∧ ctx.toNat + 576 ≤ a.toNat ∧ a.toNat + cellSize b.fields.length ≤ bump.toNat := by
  have hℓ : ℓ < H.cells.size := (Array.getElem?_eq_some_iff.1 hH).1
  obtain ⟨a', rc', b', hP', hH', hcell, hlo, hhi⟩ := h.cells ℓ hℓ
  rw [hP] at hP'
  rw [hH] at hH'
  cases hP'
  simp only [Option.some.injEq, Own.Cell.live.injEq] at hH'
  obtain ⟨rfl, rfl, rfl⟩ := hH'
  exact ⟨rfl, hcell, hlo, hhi⟩

/-- A cell's address reads as an even word (it is 8-aligned). -/
theorem cell_even {a : Word} (h : a.toNat % 8 = 0) : a &&& 1 ≠ 1 := by
  intro e
  have := congrArg UInt64.toNat e
  rw [UInt64.toNat_and, show (UInt64.toNat 1) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod] at this
  simp at this
  omega

/-- A field of a cell reads as a related word. -/
theorem proj_mem {T : Tables} {P : List Word} {m : Memory} {a : Word} {b : Own.Body} (hc : CellAt T P m a b)
    {i : Nat} {v : Own.RVal} (hi : b.fields[i]? = some v) :
    ∃ w, m.read? .w64 (a + UInt64.ofNat (8 + 8 * i)) = .ok w ∧ ValRel T P v w := by
  obtain ⟨w, hw, hv⟩ := hc.fields i v hi
  exact ⟨w, hw.read64, hv⟩

theorem immortalHeader_tag_half {n tag : Nat} (hn : n ≤ maxFields) (ht : tag ≤ maxTag) :
    (immortalHeader n tag).toNat / 2 ^ 16 % 2 ^ 16 = tag := by
  rw [immortalHeader_toNat hn ht]
  unfold maxFields maxTag immortalRc at *
  omega

/-- A cell's tag half-word reads as its constructor's tag. -/
theorem tag_mem {T : Tables} {P : List Word} {m : Memory} {a : Word} {b : Own.Body} (hc : CellAt T P m a b)
    (ha : a.toNat + 8 ≤ 2 ^ 64) : m.read? .w16 (a + 2) = .ok (UInt64.ofNat b.ctor.tag) := by
  rw [hc.header.read16_tag ha, immortalHeader_tag_half hc.small hc.ctor.tag]

end IxCC.Rt.Proof
