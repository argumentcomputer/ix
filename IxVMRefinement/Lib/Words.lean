import IxVMRefinement.Lib.Lists
import IxVMRefinement.Obs.WordLists
import Ix.IxVM.Refinement.Deserialize
import Ix.IxVM.Refinement.KernelLevels

/-! # Word and field library functions, over observed derivations

The library functions the core calls on fields, bytes and 64-bit words, as specs over
observed derivations (`ObsFn`): `UInt32::less_than_fields`, `Fields::is_zero`, the
`UInt8` conversions and comparison, the `UInt64` tests, conversions and steps, and
`WordLists::lookup_u64`.

Each spec erases the observed derivation to the source semantics (`ObsFn.erase`) and
reads it through the function's mirror (`IxVM.Refinement.Mirrors`, `«f».of_eval`: every
derivation is a run of the mirror) and the mirror's computation on represented inputs
(`IxVM.Refinement.TagN`, `Deserialize`, `KernelLevels`). A byte is a field below `256`
(`RepU8`); a word is its eight little-endian bytes (`RepU64`, equivalently
`TagN.u64Value w.toNat`, `repU64_eq`). Results that are words are stated as
`TagN.u64Value m` for the natural `m` they hold (`repU64_ofNatLT` turns one back into a
`RepU64`). -/

namespace IxVM.Refinement.Lib

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library Aiur.Library.List
open IxVM.Refinement.Obs (W)
open IxVM (F)

set_option linter.unusedVariables false

/-! ## Words as values -/

/-- **A represented word is its byte tuple** (`RepU64`'s definition, as `u64Value`). -/
theorem repU64_eq {h : Heap F} {w : UInt64} {v : SourceValue F} (hv : RepU64 h w v) :
    v = TagN.u64Value w.toNat := by
  have e := Deserialize.repU64_u64Value h w
  unfold RepU64 at hv e
  exact hv.trans e.symm

/-- The byte tuple of a natural below `2^64` represents that word. -/
theorem repU64_ofNatLT (h : Heap F) {m : Nat} (hm : m < 18446744073709551616) :
    RepU64 h (UInt64.ofNatLT m hm) (TagN.u64Value m) := by
  have e := Deserialize.repU64_u64Value h (UInt64.ofNatLT m hm)
  rwa [UInt64.toNat_ofNatLT] at e

theorem u64_toNat_lt (w : UInt64) : w.toNat < 18446744073709551616 := w.toNat_lt

/-! ## `UInt32::less_than_fields` -/

/-- **`UInt32::less_than_fields(x, y)`**: both arguments are field elements below `2^32`
(the circuit range-checks their byte decompositions; there is no derivation otherwise), the
answer is `1` exactly when the first is smaller, and nothing is allocated. -/
theorem less_than_fields_spec {x y r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt32::less_than_fields" [x, y] h r h' cs) :
    ∃ a b : F, x = .field a ∧ y = .field b ∧ a.val < 4294967296 ∧ b.val < 4294967296 ∧
      r = .field (if a.val < b.val then 1 else 0) ∧ h' = h := by
  obtain ⟨k0, hk0⟩ := KernelLevels.u32LessThanFields_complete ev.erase
  have run := hk0 (k0 + 1) (by omega)
  cases x with
  | field a =>
    cases y with
    | field b =>
      simp only [Mirrors.«UInt32::less_than_fields»] at run
      by_cases hlt : a.val < 4294967296 ∧ b.val < 4294967296
      · simp only [hlt.1, hlt.2, and_self, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at run
        exact ⟨a, b, rfl, rfl, hlt.1, hlt.2, run.1.symm, run.2.symm⟩
      · simp [hlt] at run
    | tuple _ => simp [Mirrors.«UInt32::less_than_fields»] at run
    | ptr _ _ => simp [Mirrors.«UInt32::less_than_fields»] at run
    | construct _ _ _ => simp [Mirrors.«UInt32::less_than_fields»] at run
  | tuple _ => simp [Mirrors.«UInt32::less_than_fields»] at run
  | ptr _ _ => simp [Mirrors.«UInt32::less_than_fields»] at run
  | construct _ _ _ => simp [Mirrors.«UInt32::less_than_fields»] at run

/-- **`UInt32::less_than_fields` on two field elements**: both below `2^32`, the answer `0`
or `1`, `1` exactly when `a.val < b.val`; no allocation. -/
theorem less_than_fields_field {a b : F} {r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "UInt32::less_than_fields" [.field a, .field b] h r h' cs) :
    a.val < 4294967296 ∧ b.val < 4294967296 ∧ (r = .field 1 ↔ a.val < b.val) ∧
      (r = .field 0 ∨ r = .field 1) ∧ h' = h := by
  obtain ⟨a', b', ha, hb, hla, hlb, hr, hh⟩ := less_than_fields_spec ev
  injection ha with ha
  injection hb with hb
  subst ha hb
  refine ⟨hla, hlb, ?_, ?_, hh⟩
  · by_cases hab : a.val < b.val
    · rw [ite_eq_left hab] at hr
      exact ⟨fun _ => hab, fun _ => hr⟩
    · rw [ite_eq_right hab] at hr
      subst hr
      exact ⟨fun e => absurd (Value.field.inj e) zero_ne_one, fun e => absurd e hab⟩
  · by_cases hab : a.val < b.val
    · rw [ite_eq_left hab] at hr
      exact .inr hr
    · rw [ite_eq_right hab] at hr
      exact .inl hr

/-! ## `Fields::is_zero` -/

/-- **`Fields::is_zero(x)`**: `1` exactly when `x` is the field element `0`, else `0`; no
allocation. -/
theorem is_zero_spec {x r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "Fields::is_zero" [x] h r h' cs) :
    r = .field (if x = .field 0 then 1 else 0) ∧ h' = h := by
  obtain ⟨k0, hk0⟩ := Mirrors.«Fields::is_zero».of_eval ev.erase
  have run := hk0 (k0 + 1) (by omega)
  simp only [Mirrors.«Fields::is_zero»] at run
  by_cases hx : x = .field 0
  · rw [ite_eq_left hx] at run
    simp only [Option.some.injEq, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    rw [ite_eq_left hx]
    exact ⟨rfl, rfl⟩
  · rw [ite_eq_right hx] at run
    simp only [Option.some.injEq, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    rw [ite_eq_right hx]
    exact ⟨rfl, rfl⟩

/-- **`Fields::is_zero` on a field element `a`**: `1` exactly when `a = 0`. -/
theorem is_zero_field {a : F} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "Fields::is_zero" [.field a] h r h' cs) :
    r = .field (if a = 0 then 1 else 0) ∧ h' = h := by
  obtain ⟨hr, hh⟩ := is_zero_spec ev
  refine ⟨hr.trans ?_, hh⟩
  by_cases ha : a = 0
  · subst ha
    simp
  · have hne : (Value.field a : SourceValue F) ≠ .field 0 := fun e => ha (Value.field.inj e)
    rw [ite_eq_right hne, ite_eq_right ha]

/-! ## `UInt8` -/

/-- **`UInt8::to_field(x)`** returns its argument; no allocation. -/
theorem u8_to_field_spec {x r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt8::to_field" [x] h r h' cs) : r = x ∧ h' = h :=
  Deserialize.u8ToField_refines ev.erase

/-- **`UInt8::from_field(x)`**: a derivation exists only on a byte (a field element below
`256`), and returns it; no allocation. -/
theorem u8_from_field_spec {x r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt8::from_field" [x] h r h' cs) :
    r = x ∧ h' = h ∧ ∃ b : UInt8, RepU8 h b x := by
  obtain ⟨hr, hh, n, hn, hx⟩ :=
    Deserialize.fromField_mapCall_inv (ev.erase.map_row Mirrors.«UInt8::from_field».none)
  refine ⟨hr, hh, UInt8.ofNatLT n hn, ?_⟩
  show x = .field ((UInt8.ofNatLT n hn).toNat : F)
  rw [UInt8.toNat_ofNatLT]
  exact hx

/-- **`UInt8::less_than(x, y)`** on two bytes: `1` exactly when the first is smaller, else
`0`; no allocation. -/
theorem u8_less_than_spec {x y r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {a b : UInt8} (hx : RepU8 h a x) (hy : RepU8 h b y)
    (ev : ObsFn W "UInt8::less_than" [x, y] h r h' cs) :
    r = .field (if a.toNat < b.toNat then 1 else 0) ∧ h' = h := by
  unfold RepU8 at hx hy
  subst hx hy
  obtain ⟨hr, hh⟩ := Deserialize.u8LessThan_refines (show a.toNat < 256 from a.toNat_lt)
    (show b.toNat < 256 from b.toNat_lt) ev.erase
  refine ⟨hr.trans ?_, hh⟩
  by_cases hab : a.toNat < b.toNat
  · rw [ite_eq_left hab, ite_eq_left hab, Nat.cast_one]
  · rw [ite_eq_right hab, ite_eq_right hab, Nat.cast_zero]

/-- **`UInt8::bit_decomposition(x)`** on a byte: its eight bits, least significant first; no
allocation. -/
theorem u8_bit_decomposition_spec {x r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {b : UInt8} (hx : RepU8 h b x)
    (ev : ObsFn W "UInt8::bit_decomposition" [x] h r h' cs) :
    r = .tuple [.field ((b.toNat % 2 : Nat) : F), .field ((b.toNat / 2 % 2 : Nat) : F),
      .field ((b.toNat / 4 % 2 : Nat) : F), .field ((b.toNat / 8 % 2 : Nat) : F),
      .field ((b.toNat / 16 % 2 : Nat) : F), .field ((b.toNat / 32 % 2 : Nat) : F),
      .field ((b.toNat / 64 % 2 : Nat) : F), .field ((b.toNat / 128 % 2 : Nat) : F)] ∧
      h' = h := by
  unfold RepU8 at hx
  subst hx
  exact Deserialize.u8BitDecomposition_refines (show b.toNat < 256 from b.toNat_lt) ev.erase

/-- **`UInt8::raw_bit_decomposition(x)`** (the table map) on a byte: its eight bits, least
significant first; no allocation. -/
theorem u8_raw_bit_decomposition_spec {x r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} {b : UInt8} (hx : RepU8 h b x)
    (ev : ObsFn W "UInt8::raw_bit_decomposition" [x] h r h' cs) :
    r = .tuple [.field ((b.toNat % 2 : Nat) : F), .field ((b.toNat / 2 % 2 : Nat) : F),
      .field ((b.toNat / 4 % 2 : Nat) : F), .field ((b.toNat / 8 % 2 : Nat) : F),
      .field ((b.toNat / 16 % 2 : Nat) : F), .field ((b.toNat / 32 % 2 : Nat) : F),
      .field ((b.toNat / 64 % 2 : Nat) : F), .field ((b.toNat / 128 % 2 : Nat) : F)] ∧
      h' = h := by
  unfold RepU8 at hx
  subst hx
  have hm := ev.erase.map_row Mirrors.«UInt8::raw_bit_decomposition».none
  have run := TagN.bitDecomp_run (show b.toNat < 256 from b.toNat_lt) 0 h
  simp only [Mirrors.«UInt8::bit_decomposition»] at run
  rw [run, Option.some.injEq, Prod.mk.injEq] at hm
  exact ⟨hm.1.symm, hm.2.symm⟩

/-! ## `UInt64` -/

/-- **`UInt64::is_zero(x)`** on a word: `1` exactly when it is `0`; no allocation. -/
theorem u64_is_zero_spec {x r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {w : UInt64} (hx : RepU64 h w x)
    (ev : ObsFn W "UInt64::is_zero" [x] h r h' cs) :
    r = .field (if w.toNat = 0 then 1 else 0) ∧ h' = h := by
  obtain rfl := repU64_eq hx
  exact Deserialize.u64IsZero_refines (u64_toNat_lt w) ev.erase

/-- **`UInt64::eq(x, y)`** on two words: `1` exactly when they are equal; no allocation. -/
theorem u64_eq_spec {x y r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {v w : UInt64} (hx : RepU64 h v x) (hy : RepU64 h w y)
    (ev : ObsFn W "UInt64::eq" [x, y] h r h' cs) :
    r = .field (if v.toNat = w.toNat then 1 else 0) ∧ h' = h := by
  obtain rfl := repU64_eq hx
  obtain rfl := repU64_eq hy
  obtain ⟨k0, hk0⟩ := Mirrors.«UInt64::eq».of_eval ev.erase
  have run := hk0 (k0 + 2) (by omega)
  rw [Deserialize.u64Eq_run (u64_toNat_lt v) (u64_toNat_lt w) k0 h, Option.some.injEq,
    Prod.mk.injEq] at run
  exact ⟨run.1.symm, run.2.symm⟩

/-- **`UInt64::to_field(x)`** on a word: a derivation exists only below `2^56` (the top byte
must be zero), and returns the word's value as a field element; no allocation. -/
theorem u64_to_field_spec {x r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {w : UInt64} (hx : RepU64 h w x)
    (ev : ObsFn W "UInt64::to_field" [x] h r h' cs) :
    w.toNat < 72057594037927936 ∧ r = .field (w.toNat : F) ∧ h' = h := by
  obtain rfl := repU64_eq hx
  obtain ⟨k0, hk0⟩ := Mirrors.«UInt64::to_field».of_eval ev.erase
  by_cases hlt : w.toNat < 72057594037927936
  · have run := hk0 (k0 + 2) (by omega)
    rw [Deserialize.u64ToField_run hlt k0 h, Option.some.injEq, Prod.mk.injEq] at run
    exact ⟨hlt, run.1.symm, run.2.symm⟩
  · have run := hk0 k0 (Nat.le_refl _)
    rw [Deserialize.u64ToField_none (by omega) (u64_toNat_lt w) k0 h] at run
    cases run

/-- **`UInt64::saturating_pred(x)`** on a word `w`: the word `w - 1`, or `0` at `0` (natural
subtraction); no allocation. -/
theorem u64_saturating_pred_spec {x r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {w : UInt64} (hx : RepU64 h w x)
    (ev : ObsFn W "UInt64::saturating_pred" [x] h r h' cs) :
    r = TagN.u64Value (w.toNat - 1) ∧ h' = h := by
  obtain rfl := repU64_eq hx
  exact Deserialize.u64SaturatingPred_refines (u64_toNat_lt w) ev.erase

/-- **`UInt64::wrapping_succ(x)`** on a word `w`: `w + 1` modulo `2^64`; no allocation. -/
theorem u64_wrapping_succ_spec {x r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {w : UInt64} (hx : RepU64 h w x)
    (ev : ObsFn W "UInt64::wrapping_succ" [x] h r h' cs) :
    r = TagN.u64Value ((w.toNat + 1) % 18446744073709551616) ∧ h' = h := by
  obtain rfl := repU64_eq hx
  obtain ⟨k0, hk0⟩ := Mirrors.«UInt64::wrapping_succ».of_eval ev.erase
  have run := hk0 (k0 + 2) (by omega)
  rw [Deserialize.u64WrappingSucc_run (u64_toNat_lt w) k0 h, Option.some.injEq,
    Prod.mk.injEq] at run
  exact ⟨run.1.symm, run.2.symm⟩

/-- **`UInt64::add(x, y)`** on two words: the sum modulo `2^64` and the carry out (a field
element, `0` or `1`); no allocation. -/
theorem u64_add_spec {x y r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {v w : UInt64} (hx : RepU64 h v x) (hy : RepU64 h w y)
    (ev : ObsFn W "UInt64::add" [x, y] h r h' cs) :
    r = .tuple [TagN.u64Value ((v.toNat + w.toNat) % 18446744073709551616),
      .field (((v.toNat + w.toNat) / 18446744073709551616 : Nat) : F)] ∧ h' = h := by
  obtain rfl := repU64_eq hx
  obtain rfl := repU64_eq hy
  obtain ⟨k0, hk0⟩ := Mirrors.«UInt64::add».of_eval ev.erase
  have run := hk0 (k0 + 2) (by omega)
  rw [TagN.u64Add_value (u64_toNat_lt v) (u64_toNat_lt w) k0 h, Option.some.injEq,
    Prod.mk.injEq] at run
  exact ⟨run.1.symm, run.2.symm⟩

/-! ## `WordLists::lookup_u64` -/

section
variable {α : Type} {t : Generic.Ty} {R : Heap F → α → SourceValue F → Prop}

/-- **`WordLists::lookup_u64(list, idx)`** at the word index `n`: the element at `n` (which
exists); no allocation. -/
theorem lookup_u64_spec {xs : List α} :
    ∀ {n : Nat} {l x r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
    n < 18446744073709551616 → x = TagN.u64Value n →
    ObsFn W (Instance.mk "WordLists::lookup_u64" [t]).symbol [l, x] h r h' cs →
    RepList (Instance.mk "Lists::Node" [t]).symbol R h xs l →
    (∃ v, xs[n]? = some v ∧ R h v r) ∧ h' = h := by
  induction xs with
  | nil =>
    intro n l x r h h' cs hn hx ev hl
    rcases Obs.«WordLists::lookup_u64».obs ev with
      ⟨xv, xrest, m, cs1, ld, -, -, -, -⟩ |
      ⟨xv, xrest, m, cs1, cs2, v, m2, cs3, ld, -, -, -, -⟩
    · obtain ⟨z, zs, he, -, -⟩ := rep_cons_of_load hl ld
      cases he
    · obtain ⟨z, zs, he, -, -⟩ := rep_cons_of_load hl ld
      cases he
  | cons z zs ih =>
    intro n l x r h h' cs hn hx ev hl
    subst hx
    rcases Obs.«WordLists::lookup_u64».obs ev with
      ⟨xv, xrest, m, cs1, ld, ev1, rfl, rfl, -⟩ |
      ⟨xv, xrest, m, cs1, cs2, v, m2, cs3, ld, ev1, ev2, ev3, -⟩
    · -- `is_zero(idx) = 1`: the head
      obtain ⟨hz, rfl⟩ := Deserialize.u64IsZero_refines hn ev1.erase
      have hn0 : n = 0 := by
        by_contra hne
        rw [ite_eq_right hne] at hz
        exact one_ne_zero (Value.field.inj hz)
      subst hn0
      obtain ⟨z', zs', he, hz', -⟩ := rep_cons_of_load hl ld
      injection he with h1 h2
      subst h1 h2
      exact ⟨⟨z, rfl, hz'⟩, rfl⟩
    · -- `is_zero(idx) = 0`: the tail at `idx - 1`
      obtain ⟨hz, rfl⟩ := Deserialize.u64IsZero_refines hn ev1.erase
      have hn0 : n ≠ 0 := by
        intro he
        rw [ite_eq_left he] at hz
        exact zero_ne_one (Value.field.inj hz)
      obtain ⟨hv, rfl⟩ := Deserialize.u64SaturatingPred_refines hn ev2.erase
      obtain ⟨z', zs', he, -, hzs⟩ := rep_cons_of_load hl ld
      injection he with h1 h2
      subst h1 h2
      obtain ⟨⟨v', hv', hR⟩, hh⟩ := ih (n := n - 1) (by omega) hv ev3 hzs
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      refine ⟨⟨v', ?_, hR⟩, hh⟩
      simpa using hv'

/-- **`WordLists::lookup_u64`** at a represented word index `w`: the element at `w.toNat`. -/
theorem lookup_u64_rep {xs : List α} {l x r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} {w : UInt64} (hx : RepU64 h w x)
    (ev : ObsFn W (Instance.mk "WordLists::lookup_u64" [t]).symbol [l, x] h r h' cs)
    (hl : RepList (Instance.mk "Lists::Node" [t]).symbol R h xs l) :
    (∃ v, xs[w.toNat]? = some v ∧ R h v r) ∧ h' = h :=
  lookup_u64_spec (u64_toNat_lt w) (repU64_eq hx) ev hl

end

end IxVM.Refinement.Lib
