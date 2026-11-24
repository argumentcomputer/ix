import IxCC.Rt.Layout
import IxCC.Rt.Rc.Array.Invariant
import IxCC.Rt.Readback.Array
import IxCC.X86.ELFRodata
import IxCC.BigNat.Proof.Entry
import IxCC.Rt.Proof.Words

/-! # Phase 4 Arbitrary-Precision `Nat` Runtime Representation (`IxCC.Rt.BigNat.Cell`)

Unifies the two runtime encodings of `Nat` (`IxCC/docs/bignum-design.md`, §Representation):

* **Small immediate (`n < 2^63`):** odd tagged word `2n + 1` (`Rt.natWord n = some w`,
  `w &&& 1 = 1`), zero heap allocation.
* **Big limb cell (`n ≥ 2^63`):** even 8-byte-aligned pointer `addr` (`addr &&& 1 = 0`,
  `addr ≠ 0`) to a canonical `LimbArray` cell (`header(scan = 0, tag = 0x7F03, rc) |
  size | cap | limbs[cap]`), living either in the dynamic counted heap (`LiveArrayCell`)
  or in read-only ELF `.rodata` (`StaticArrayCell`, for `≥ 2^63` literals via
  `X86.ELFRodata`).

Proves the key properties consumed by `IxCC.Rt.BigNat.Dispatch` and `IxCC.Rt.BigNat.Proof`:
* Exact 1-instruction low-bit tag test (`test (a & b), 1`) iff both operands are small;
* Exact `Rt.Readback.readbackBigNat` agreement and value injectivity (`NatVal.unique_val`);
* Exact zero test `w = 1 ↔ n = 0` across ALL arbitrary-precision `Nat` values;
* Immortal static `.rodata` literal encoding and representation proof (`NatVal.ofRodataLiteral`).

Strictly standard axioms `[propext, Classical.choice, Quot.sound]`; zero `sorry`. -/

set_option autoImplicit false

namespace IxCC.Rt.BigNat

open IxCC.Lir (Word)
open IxCC.Rt
open IxCC.Rt.Proof
open IxCC.Rt.Rc.Array
open IxCC.Rt.Readback
open IxCC.X86 (Memory)
open IxCC.X86.ELFRodata

/-! ## Layout Constants -/

/-- Object-kind tag for `BigNat` limb cells (`0x7F03`, strictly above `Rt.maxTag = 0x7EFF`). -/
def bigNatTag : Nat := X86.ELFRodata.tagLimbArray

/-- Header `scan` byte for `BigNat` limb cells (`0`: unboxed raw limbs, O(1) RC release). -/
def bigNatScan : Nat := ArrayKind.limbs.scan

theorem bigNatTag_gt_maxTag : Rt.maxTag < bigNatTag := ArrayKind.tag_gt_maxTag .limbs

theorem bigNatScan_eq_zero : bigNatScan = 0 := rfl

theorem bigNatTag_eq_limbs : bigNatTag = ArrayKind.limbs.tag := rfl

/-! ## Canonical `BigNat` Cell and Unified `NatVal` Relation -/

/-- Physical storage of a `BigNat` limb array cell: either a live dynamic heap cell
or an immortal read-only ELF `.rodata` cell. -/
inductive BigNatStorage (mem : Memory) (addr : Word) (limbs : List Word) : Prop where
  | live (refs cls cap : Nat) (h : LiveArrayCell mem addr refs cls cap (.limbs limbs))
  | static (cap : Nat) (h : StaticArrayCell mem addr cap (.limbs limbs))

/-- A canonical `BigNat` cell at `addr` in memory `mem`: backed by a valid dynamic or
static `LimbArray` cell with canonical normal form (`WF` and `toNat ≥ 2^63`). -/
structure BigNatCell (mem : Memory) (addr : Word) (limbs : List Word) : Prop where
  storage : BigNatStorage mem addr limbs
  wf : IxCC.BigNat.WF limbs.toArray
  ge_limit : Rt.natLimit ≤ IxCC.BigNat.toNat limbs.toArray

/-- **Unified Phase 4 `Nat` value relation (`NatVal mem n w`)**:
* `.small`: `n < 2^63` and `w = 2n + 1` (odd tagged immediate);
* `.big`: `n ≥ 2^63` and `w` points to a canonical `BigNatCell` (even 8-aligned pointer). -/
inductive NatVal (mem : Memory) : Nat → Word → Prop where
  | small {n : Nat} {w : Word} (h : Rt.natWord n = some w) : NatVal mem n w
  | big {addr : Word} {limbs : List Word} (h : BigNatCell mem addr limbs) :
      NatVal mem (IxCC.BigNat.toNat limbs.toArray) addr

/-- Boolean result word relation (`BoolVal tWord fWord b w`), matching `Rt.Lower.Tables.bools`. -/
def BoolVal (tWord fWord : Word) (b : Bool) (w : Word) : Prop :=
  w = if b then tWord else fWord

/-! ## Alignment and Tag-Bit Lemmas -/

theorem BigNatStorage.aligned {mem : Memory} {addr : Word} {limbs : List Word}
    (h : BigNatStorage mem addr limbs) : addr.toNat % 8 = 0 := by
  cases h with
  | live _ _ _ hl => exact hl.aligned
  | static _ hs => exact hs.aligned

theorem BigNatStorage.nonzero {mem : Memory} {addr : Word} {limbs : List Word}
    (h : BigNatStorage mem addr limbs) : addr ≠ 0 := by
  cases h with
  | live _ _ _ hl => exact hl.nonzero
  | static _ hs => exact hs.nonzero

theorem BigNatStorage.even_word {mem : Memory} {addr : Word} {limbs : List Word}
    (h : BigNatStorage mem addr limbs) : addr &&& 1 = 0 := by
  have hal := h.aligned
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, show (UInt64.toNat 1) = 2 ^ 1 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, show (0 : Word).toNat = 0 from rfl]
  omega

theorem BigNatCell.even_word {mem : Memory} {addr : Word} {limbs : List Word}
    (h : BigNatCell mem addr limbs) : addr &&& 1 = 0 :=
  h.storage.even_word

theorem BigNatCell.aligned {mem : Memory} {addr : Word} {limbs : List Word}
    (h : BigNatCell mem addr limbs) : addr.toNat % 8 = 0 :=
  h.storage.aligned

theorem BigNatCell.nonzero {mem : Memory} {addr : Word} {limbs : List Word}
    (h : BigNatCell mem addr limbs) : addr ≠ 0 :=
  h.storage.nonzero

theorem BigNatCell.readbackLimbs {mem : Memory} {addr : Word} {limbs : List Word}
    (h : BigNatCell mem addr limbs) : readbackLimbArray mem addr = some limbs.toArray := by
  cases h.storage with
  | live _ _ _ hl => exact readbackLimbArray_live hl
  | static _ hs => exact readbackLimbArray_static hs

theorem BigNatCell.readback {mem : Memory} {addr : Word} {limbs : List Word}
    (h : BigNatCell mem addr limbs) :
    readbackBigNat mem addr = some (IxCC.BigNat.toNat limbs.toArray) := by
  cases h.storage with
  | live _ _ _ hl => exact readbackBigNat_big_live hl h.wf h.ge_limit
  | static _ hs => exact readbackBigNat_big_static hs h.wf h.ge_limit

theorem natWord_low_bit {n : Nat} {w : Word} (h : Rt.natWord n = some w) : w &&& 1 = 1 :=
  (Rt.odd_word (Rt.natWord_toNat h)).1

theorem NatVal.ofNat_lt {mem : Memory} {n : Nat} (hn : n < Rt.natLimit) :
    NatVal mem n (UInt64.ofNat (2 * n + 1)) :=
  .small (natWord_of_lt hn)

theorem NatVal.small_mono {mem₁ mem₂ : Memory} {n : Nat} {w : Word}
    (h : NatVal mem₁ n w) (hlt : n < Rt.natLimit) : NatVal mem₂ n w := by
  cases h with
  | small hw => exact .small hw
  | big hc =>
    have hge := hc.ge_limit
    omega

theorem NatVal.low_bit_cases {mem : Memory} {n : Nat} {w : Word} (h : NatVal mem n w) :
    (w &&& 1 = 1 ∧ Rt.natWord n = some w ∧ n < Rt.natLimit) ∨
    (w &&& 1 = 0 ∧ Rt.natLimit ≤ n ∧ ∃ limbs, BigNatCell mem w limbs ∧ IxCC.BigNat.toNat limbs.toArray = n) := by
  cases h with
  | small hw =>
    exact Or.inl ⟨natWord_low_bit hw, hw, natWord_lt hw⟩
  | big hc =>
    exact Or.inr ⟨hc.even_word, hc.ge_limit, _, hc, rfl⟩

theorem NatVal.low_bit_small {mem : Memory} {n : Nat} {w : Word}
    (h : NatVal mem n w) (hodd : w &&& 1 = 1) : Rt.natWord n = some w := by
  rcases h.low_bit_cases with ⟨_, hw, _⟩ | ⟨hev, _, _⟩
  · exact hw
  · rw [hev] at hodd; cases hodd

theorem NatVal.low_bit_big {mem : Memory} {n : Nat} {w : Word}
    (h : NatVal mem n w) (hev : w &&& 1 = 0) :
    Rt.natLimit ≤ n ∧ ∃ limbs, BigNatCell mem w limbs ∧ IxCC.BigNat.toNat limbs.toArray = n := by
  rcases h.low_bit_cases with ⟨hodd, _, _⟩ | ⟨_, hge, limbs, hc, hto⟩
  · rw [hodd] at hev; cases hev
  · exact ⟨hge, limbs, hc, hto⟩

theorem NatVal.small_iff_odd {mem : Memory} {n : Nat} {w : Word} (h : NatVal mem n w) :
    w &&& 1 = 1 ↔ n < Rt.natLimit := by
  rcases h.low_bit_cases with ⟨hodd, _, hlt⟩ | ⟨hev, hge, _⟩
  · exact ⟨fun _ => hlt, fun _ => hodd⟩
  · constructor
    · intro h1; rw [hev] at h1; cases h1
    · intro hlt; omega

theorem NatVal.tz_one_false_iff {mem : Memory} {n : Nat} {w : Word} (h : NatVal mem n w) :
    Lir.Cond.holds .tz .w64 w 1 = false ↔ Rt.natWord n = some w := by
  simp only [Lir.Cond.holds, truncate_w64]
  rcases h.low_bit_cases with ⟨hodd, hw, _⟩ | ⟨hev, hge, _⟩
  · simp [hodd, hw]
  · simp only [hev, beq_self_eq_true, Bool.true_eq_false, false_iff]
    intro hw
    have := natWord_lt hw
    unfold Rt.natLimit at hge
    omega

/-- **1-instruction binary tag test (`(wa &&& wb) &&& 1 = 1`)**: holds iff BOTH operands
are small tagged immediates (`< 2^63`). -/
theorem NatVal.both_small_iff_and_odd {mem : Memory} {p q : Nat} {wa wb : Word}
    (ha : NatVal mem p wa) (hb : NatVal mem q wb) :
    (wa &&& wb) &&& 1 = 1 ↔ Rt.natWord p = some wa ∧ Rt.natWord q = some wb := by
  have hassoc : (wa &&& wb) &&& (1 : Word) = (wa &&& 1) &&& (wb &&& 1) := by
    apply UInt64.toNat_inj.mp
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [UInt64.toNat_and, Nat.testBit_and]
    cases (wa.toNat.testBit i) <;> cases (wb.toNat.testBit i) <;> cases ((1 : Word).toNat.testBit i) <;> rfl
  rw [hassoc]
  rcases ha.low_bit_cases with ⟨ha1, hwa, _⟩ | ⟨ha0, hap, _⟩
  · rcases hb.low_bit_cases with ⟨hb1, hwb, _⟩ | ⟨hb0, hbq, _⟩
    · simp [ha1, hb1, hwa, hwb]
    · simp only [ha1, hb0, show (1 : Word) &&& 0 = 0 from rfl,
        show (0 : Word) = 1 ↔ False from by decide, false_iff]
      rintro ⟨_, hwb⟩
      have := natWord_lt hwb
      unfold Rt.natLimit at hbq
      omega
  · rw [ha0, UInt64.zero_and]
    constructor
    · intro h01; cases h01
    · rintro ⟨hwa, _⟩
      have := natWord_lt hwa
      unfold Rt.natLimit at hap
      omega

/-- Fast-path condition for `br .tz .w64 (wa &&& wb) 1 slow fast`:
the branch falls through to `fast` (`holds .tz = false`) iff BOTH operands are tagged immediates. -/
theorem NatVal.and_tz_one_false_iff {mem : Memory} {p q : Nat} {wa wb : Word}
    (ha : NatVal mem p wa) (hb : NatVal mem q wb) :
    Lir.Cond.holds .tz .w64 (wa &&& wb) 1 = false ↔
      Rt.natWord p = some wa ∧ Rt.natWord q = some wb := by
  have hbit : (wa &&& wb) &&& (1 : Word) = 0 ∨ (wa &&& wb) &&& (1 : Word) = 1 := by
    have hlt : ((wa &&& wb) &&& (1 : Word)).toNat < 2 := by
      rw [UInt64.toNat_and, show (UInt64.toNat 1) = 2 ^ 1 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod]
      omega
    rcases (show ((wa &&& wb) &&& (1 : Word)).toNat = 0 ∨ ((wa &&& wb) &&& (1 : Word)).toNat = 1 by omega) with h0 | h1
    · exact Or.inl (UInt64.toNat_inj.mp h0)
    · exact Or.inr (UInt64.toNat_inj.mp h1)
  rw [← NatVal.both_small_iff_and_odd ha hb]
  simp only [Lir.Cond.holds, truncate_w64]
  rcases hbit with h0 | h1
  · simp [h0]
  · simp [h1]

/-- Slow-path condition for `br .tz .w64 (wa &&& wb) 1 slow fast`:
the branch jumps to `slow` (`holds .tz = true`) iff at least one operand is `≥ 2^63`. -/
theorem NatVal.and_tz_one_true_iff {mem : Memory} {p q : Nat} {wa wb : Word}
    (ha : NatVal mem p wa) (hb : NatVal mem q wb) :
    Lir.Cond.holds .tz .w64 (wa &&& wb) 1 = true ↔
      Rt.natLimit ≤ p ∨ Rt.natLimit ≤ q := by
  have hfalse := NatVal.and_tz_one_false_iff ha hb
  cases h : Lir.Cond.holds .tz .w64 (wa &&& wb) 1
  · simp only [Bool.false_eq_true, false_iff]
    obtain ⟨hwa, hwb⟩ := hfalse.mp h
    have hp := natWord_lt hwa
    have hq := natWord_lt hwb
    unfold Rt.natLimit
    omega
  · simp only [true_iff]
    rcases ha.low_bit_cases with ⟨_, hwa, _⟩ | ⟨_, hgep, _⟩
    · rcases hb.low_bit_cases with ⟨_, hwb, _⟩ | ⟨_, hgeq, _⟩
      · have hf := hfalse.mpr ⟨hwa, hwb⟩
        rw [h] at hf
        cases hf
      · exact Or.inr hgeq
    · exact Or.inl hgep

/-! ## Readback Agreement, Uniqueness, and Exact Zero Test -/

/-- Any `NatVal mem n w` reads back via `Rt.Readback.readbackBigNat` to `some n`. -/
theorem NatVal.readback {mem : Memory} {n : Nat} {w : Word} (h : NatVal mem n w) :
    readbackBigNat mem w = some n := by
  cases h with
  | small hw => exact readbackBigNat_small hw
  | big hc => exact hc.readback

/-- A runtime word denotes at most one mathematical `Nat` in memory `mem`. -/
theorem NatVal.unique_val {mem : Memory} {n₁ n₂ : Nat} {w : Word}
    (h₁ : NatVal mem n₁ w) (h₂ : NatVal mem n₂ w) : n₁ = n₂ := by
  have r1 := h₁.readback
  have r2 := h₂.readback
  rw [r1] at r2
  exact Option.some.inj r2

/-- Exact zero test across ALL arbitrary-precision `Nat` values (`< 2^63` and `≥ 2^63`):
a `NatVal` word equals `1` iff it denotes `0`. (Every big pointer is even so never `1`.) -/
theorem NatVal.eq_one_iff_zero {mem : Memory} {n : Nat} {w : Word} (h : NatVal mem n w) :
    w = 1 ↔ n = 0 := by
  cases h with
  | small hw => exact natWord_eq_one hw
  | big hc =>
    have hge := hc.ge_limit
    have hev := hc.even_word
    constructor
    · intro h1; subst h1; cases hev
    · intro h0; unfold Rt.natLimit at hge; omega

/-! ## Immortal Static `.rodata` `≥ 2^63` Literal Cells (`X86.ELFRodata`) -/

/-- Encode a `Nat` literal `n ≥ 2^63` as an immortal static `.rodata` `LimbArray` cell
(`header(scan = 0, cls = 0, tag = 0x7F03, rc = INT32_MIN) | size | cap | limbs`). -/
def encodeBigNatLiteral (n : Nat) : ByteArray :=
  encodeStaticLimbArray (IxCC.BigNat.ofNat n).toList

/-- Append a `≥ 2^63` `Nat` literal as an 8-byte-aligned static cell in a `.rodata` table. -/
def addBigNatLiteral (t : RodataTable) (name : String) (n : Nat) : RodataTable × Nat :=
  t.addLimbArray name (IxCC.BigNat.ofNat n).toList

theorem encodeBigNatLiteral_size (n : Nat) :
    (encodeBigNatLiteral n).size = 24 + 8 * (IxCC.BigNat.ofNat n).size := by
  unfold encodeBigNatLiteral
  rw [encodeStaticLimbArray_size, Array.length_toList]

/-- Any `Nat` literal `n ≥ 2^63` encoded via `encodeBigNatLiteral` inside a `RodataMapped`
ELF `.rodata` section satisfies `BigNatCell` and `NatVal`, and reads back to `some n`. -/
theorem NatVal.ofRodataLiteral {mem : Memory} {base : Word} {rodata : ByteArray}
    {off n : Nat} (hge : Rt.natLimit ≤ n)
    (hm : RodataMapped base rodata mem)
    (hoff_align : off % 8 = 0)
    (hnonzero : base + UInt64.ofNat off ≠ 0)
    (hbound : off + (encodeBigNatLiteral n).size ≤ rodata.size)
    (hslice : ∀ j (hj : j < (encodeBigNatLiteral n).size),
      rodata[off + j]'(by omega) = (encodeBigNatLiteral n)[j]'hj) :
    NatVal mem n (base + UInt64.ofNat off) ∧
      readbackBigNat mem (base + UInt64.ofNat off) = some n := by
  have hst := StaticArrayCell.ofRodataLimbArray hm hoff_align hnonzero hbound hslice
  have hwf : IxCC.BigNat.WF (IxCC.BigNat.ofNat n).toList.toArray := by
    simpa [Array.toArray_toList] using IxCC.BigNat.wf_ofNat n
  have hto : IxCC.BigNat.toNat (IxCC.BigNat.ofNat n).toList.toArray = n := by
    simpa [Array.toArray_toList] using IxCC.BigNat.toNat_ofNat n
  have hcell : BigNatCell mem (base + UInt64.ofNat off) (IxCC.BigNat.ofNat n).toList :=
    { storage := .static _ hst, wf := hwf, ge_limit := by rw [hto]; exact hge }
  have hnv : NatVal mem n (base + UInt64.ofNat off) := by
    rw [← hto]
    exact .big hcell
  exact ⟨hnv, hnv.readback⟩

/-! ## Bridge to `IxCC.BigNat.Entry.SlowNat` -/

/-- A `NatVal mem a.val w` agrees with a canonical `SlowNat`:
small iff `.small`, big iff `.big` with identical canonical limbs. -/
theorem NatVal.matches_slowNat {mem : Memory} {a : IxCC.BigNat.Entry.SlowNat} {w : Word}
    (hcan : a.Canonical) (hnv : NatVal mem a.val w) :
    match a with
    | .small v => w = UInt64.ofNat (2 * v.toNat + 1)
    | .big ls => readbackLimbArray mem w = some ls ∧ w &&& 1 = 0 := by
  cases a with
  | small v =>
    have hv : v.toNat < Rt.natLimit := hcan
    rcases hnv.low_bit_cases with ⟨_, hw, _⟩ | ⟨_, hge, _⟩
    · simp only [IxCC.BigNat.Entry.val_small] at hw
      have h1 := natWord_of_lt hv
      rw [h1] at hw
      exact (Option.some.inj hw).symm
    · simp only [IxCC.BigNat.Entry.val_small] at hge
      unfold Rt.natLimit at hv hge
      omega
  | big ls =>
    rcases hcan with ⟨hwf_ls, hge_ls⟩
    rcases hnv.low_bit_cases with ⟨_, _, hlt⟩ | ⟨hev, _, limbs, hc, hval⟩
    · simp only [IxCC.BigNat.Entry.val_big] at hlt
      unfold Rt.natLimit at hlt
      omega
    · simp only [IxCC.BigNat.Entry.val_big] at hval
      have heq : limbs.toArray = ls := IxCC.BigNat.toNat_inj hc.wf hwf_ls hval
      exact ⟨by rw [hc.readbackLimbs, heq], hev⟩

/-! ## Kernel-Evaluable `.rodata` BigNat Encoders (`*K`) -/

/-- Kernel-evaluable static `LimbArray` / `BigNat` cell encoder (zero `ByteArray` copies). -/
def encodeStaticLimbArrayK (limbs : List Word) : List UInt8 :=
  encodeWordsK (staticHeader 0 tagLimbArray :: UInt64.ofNat limbs.length :: UInt64.ofNat limbs.length :: limbs)

/-- Kernel-evaluable static `BigNat` literal encoder (`n ≥ 2^63`). -/
def encodeBigNatLiteralK (n : Nat) : List UInt8 :=
  encodeStaticLimbArrayK (IxCC.BigNat.ofNat n).toList

/-- Kernel-evaluable `.rodata` table append for a `≥ 2^63` `Nat` literal. -/
def addBigNatLiteralK (t : RodataTableK) (name : String) (n : Nat) : RodataTableK × Nat :=
  t.addCell name (encodeBigNatLiteralK n)

theorem encodeStaticLimbArrayK_eq (limbs : List Word) :
    (⟨⟨encodeStaticLimbArrayK limbs⟩⟩ : ByteArray) = encodeStaticLimbArray limbs :=
  encodeWordsK_eq _

theorem encodeBigNatLiteralK_eq (n : Nat) :
    (⟨⟨encodeBigNatLiteralK n⟩⟩ : ByteArray) = encodeBigNatLiteral n :=
  encodeStaticLimbArrayK_eq _

theorem addBigNatLiteralK_toRodataTable (t : RodataTableK) (name : String) (n : Nat) :
    let (t', off) := addBigNatLiteralK t name n
    (t'.toRodataTable, off) = addBigNatLiteral t.toRodataTable name n := by
  simp only [addBigNatLiteralK, addBigNatLiteral, RodataTable.addLimbArray]
  rw [← encodeStaticLimbArrayK_eq]
  exact RodataTableK.addCell_toRodataTable t name (encodeBigNatLiteralK n)

/-! ## Exact Equivalence Between `Rt.readbackBig` and `Rt.Readback.readbackBigNat` -/

private theorem readWordsList_eq_mapM (m : Memory) (addr : Word) :
    ∀ (n off : Nat),
      Rt.readWordsList m addr off n =
        (List.range n).mapM fun j =>
          match m.read64? (addr + UInt64.ofNat (24 + 8 * (off + j))) with
          | .ok w => some w
          | .error _ => none
  | 0, _ => rfl
  | n + 1, off => by
    rw [List.range_succ_eq_map, List.mapM_cons]
    unfold Rt.readWordsList
    simp only [Nat.add_zero]
    cases m.read64? (addr + UInt64.ofNat (24 + 8 * off)) with
    | error _ => rfl
    | ok w =>
      simp only [List.mapM_map]
      have ih := readWordsList_eq_mapM m addr n (off + 1)
      rw [ih]
      have hfn :
          (fun x => match m.read64? (addr + UInt64.ofNat (24 + 8 * (off + 1 + x))) with
            | .ok w => some w | .error _ => none) =
          ((fun j => match m.read64? (addr + UInt64.ofNat (24 + 8 * (off + j))) with
            | .ok w => some w | .error _ => none) ∘ Nat.succ) := by
        funext x
        simp only [Function.comp, show off + 1 + x = off + x.succ by omega]
      rw [hfn]
      cases ((List.range n).mapM ((fun j =>
        match m.read64? (addr + UInt64.ofNat (24 + 8 * (off + j))) with
        | .ok w => some w | .error _ => none) ∘ Nat.succ)) <;> rfl

theorem readWordsList_eq_readWordsRange (m : Memory) (addr : Word) (n : Nat) :
    Rt.readWordsList m addr 0 n = readWordsRange m addr n := by
  rw [readWordsList_eq_mapM]
  unfold readWordsRange arrayPayloadOffset
  simp only [Nat.zero_add]
  rfl

theorem limbsToNatList_eq_toNat (limbs : List Word) :
    Rt.limbsToNatList limbs = IxCC.BigNat.toNat limbs.toArray := by
  have aux : ∀ (ls : List Word), Rt.limbsToNatList ls = IxCC.BigNat.toNatPrefix ls.toArray ls.length := by
    intro ls
    induction ls with
    | nil => rfl
    | cons w ws ih =>
      have hshift : ∀ (k : Nat), k ≤ ws.length →
          IxCC.BigNat.toNatPrefix (w :: ws).toArray (k + 1) =
            w.toNat + 2 ^ 64 * IxCC.BigNat.toNatPrefix ws.toArray k := by
        intro k hk
        induction k with
        | zero =>
          simp only [IxCC.BigNat.toNatPrefix, Nat.zero_add, Nat.pow_zero, Nat.mul_one, Nat.mul_zero, Nat.add_zero]
          have h0 : IxCC.BigNat.getLimb (w :: ws).toArray 0 = w := by
            rw [IxCC.BigNat.getLimb_lt (by simp)]; rfl
          rw [h0]
        | succ k ihk =>
          rw [IxCC.BigNat.toNatPrefix, ihk (by omega)]
          conv => rhs; rw [IxCC.BigNat.toNatPrefix]
          have hg1 : IxCC.BigNat.getLimb (w :: ws).toArray (k + 1) = ws[k]'(by omega) := by
            rw [IxCC.BigNat.getLimb_lt (by simp; omega)]; rfl
          have hg2 : IxCC.BigNat.getLimb ws.toArray k = ws[k]'(by omega) := by
            rw [IxCC.BigNat.getLimb_lt (by simp; omega)]; rfl
          rw [hg1, hg2, Nat.mul_add, Nat.pow_succ (2 ^ 64) k]
          have hcomm : (ws[k]'(by omega)).toNat * ((2 ^ 64) ^ k * 2 ^ 64) =
              2 ^ 64 * ((ws[k]'(by omega)).toNat * (2 ^ 64) ^ k) := by
            rw [Nat.mul_comm ((2 ^ 64) ^ k) (2 ^ 64), ← Nat.mul_assoc,
              Nat.mul_comm ((ws[k]'(by omega)).toNat) (2 ^ 64), Nat.mul_assoc]
          rw [hcomm, Nat.add_assoc]
      simp only [Rt.limbsToNatList, List.length_cons, ih]
      exact (hshift ws.length (Nat.le_refl _)).symm
  simpa [IxCC.BigNat.toNat] using aux limbs

theorem isCanonicalLimbsList_iff (limbs : List Word) :
    Rt.isCanonicalLimbsList limbs = true ↔
      IxCC.BigNat.WF limbs.toArray ∧ Rt.natLimit ≤ IxCC.BigNat.toNat limbs.toArray := by
  cases limbs with
  | nil =>
    simp [Rt.isCanonicalLimbsList, IxCC.BigNat.toNat, Rt.natLimit]
  | cons w rest =>
    cases rest with
    | nil =>
      simp only [Rt.isCanonicalLimbsList, decide_eq_true_eq]
      have hto : IxCC.BigNat.toNat [w].toArray = w.toNat := by
        rw [← limbsToNatList_eq_toNat]; simp [Rt.limbsToNatList]
      rw [hto]
      constructor
      · intro hge
        refine ⟨Or.inr ?_, hge⟩
        have hg : IxCC.BigNat.getLimb [w].toArray 0 = w := by
          rw [IxCC.BigNat.getLimb_lt (by simp)]; rfl
        simp only [List.size_toArray, List.length_singleton, Nat.sub_self, hg]
        intro hz
        rw [hz] at hge
        simp [Rt.natLimit] at hge
      · exact (·.2)
    | cons w1 rest' =>
      simp only [Rt.isCanonicalLimbsList]
      have hlast : (w1 :: rest').getLast? = some ((w1 :: rest').getLast (List.cons_ne_nil _ _)) :=
        List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)
      rw [hlast]
      simp only [bne_iff_ne, ne_eq]
      let top := (w1 :: rest').getLast (List.cons_ne_nil _ _)
      have hlen : (w :: w1 :: rest').toArray.size = rest'.length + 2 := by simp
      have htop_eq : IxCC.BigNat.getLimb (w :: w1 :: rest').toArray ((w :: w1 :: rest').toArray.size - 1) = top := by
        rw [IxCC.BigNat.getLimb_lt (by omega)]
        simp only [List.getElem_toArray]
        have hidx : (w :: w1 :: rest').toArray.size - 1 = (rest'.length + 1) := by omega
        simp only [hidx, List.getElem_cons_succ]
        exact (List.getLast_eq_getElem (List.cons_ne_nil w1 rest')).symm
      constructor
      · intro hne
        have hwf : IxCC.BigNat.WF (w :: w1 :: rest').toArray := Or.inr (by rw [htop_eq]; exact hne)
        have htop_pos : 1 ≤ top.toNat := by
          have : top.toNat ≠ 0 := fun h0 => hne (UInt64.toNat_inj.mp (by simpa using h0))
          omega
        have hge : 2 ^ 64 ≤ IxCC.BigNat.toNat (w :: w1 :: rest').toArray := by
          unfold IxCC.BigNat.toNat
          rw [hlen]
          change 2 ^ 64 ≤ IxCC.BigNat.toNatPrefix (w :: w1 :: rest').toArray ((rest'.length + 1) + 1)
          rw [IxCC.BigNat.toNatPrefix]
          have hsub : (w :: w1 :: rest').toArray.size - 1 = rest'.length + 1 := by omega
          have htop_eq' : IxCC.BigNat.getLimb (w :: w1 :: rest').toArray (rest'.length + 1) = top := by
            rwa [← hsub]
          rw [htop_eq']
          have hpow : 2 ^ 64 ≤ (2 ^ 64) ^ (rest'.length + 1) := by
            have : (2 ^ 64) ^ 1 ≤ (2 ^ 64) ^ (rest'.length + 1) :=
              Nat.pow_le_pow_right (by decide) (by omega)
            simpa using this
          have hmul : 1 * 2 ^ 64 ≤ top.toNat * (2 ^ 64) ^ (rest'.length + 1) :=
            Nat.mul_le_mul htop_pos hpow
          omega
        exact ⟨hwf, by unfold Rt.natLimit; omega⟩
      · rintro ⟨hwf, _⟩
        rcases hwf with h0 | htop
        · omega
        · rwa [htop_eq] at htop

theorem isCanonicalLimbsList_eq_isCanonicalBigNat (limbs : List Word) :
    Rt.isCanonicalLimbsList limbs = isCanonicalBigNat limbs.toArray := by
  apply Bool.eq_iff_iff.mpr
  rw [isCanonicalLimbsList_iff, isCanonicalBigNat_iff]
  rfl

/-- **`Rt.readbackNatWord` agrees identically with `Rt.Readback.readbackBigNat` on all words.** -/
theorem readbackNatWord_eq_readbackBigNat (m : Memory) (w : Word) :
    Rt.readbackNatWord m w = readbackBigNat m w := by
  unfold Rt.readbackNatWord readbackBigNat readbackLimbArray
  split
  · rfl
  · simp only [Rt.bigNatTag, ArrayKind.scan, ArrayKind.tag, tagLimbArray]
    cases m.read64? w with
    | error _ => rfl
    | ok hdr =>
      cases m.read64? (w + 8) with
      | error _ => rfl
      | ok sz =>
        cases m.read64? (w + 16) with
        | error _ => rfl
        | ok cap =>
          dsimp only
          by_cases hcond : ((hdr &&& 0xFF).toNat == 0 &&
              ((hdr >>> 16) &&& 0xFFFF).toNat == 0x7F03 &&
              decide (sz.toNat ≤ cap.toNat)) = true
          · simp only [hcond, ↓reduceIte]
            rw [readWordsList_eq_readWordsRange]
            cases readWordsRange m w sz.toNat with
            | none => rfl
            | some limbs =>
              simp only [Option.map_some, isCanonicalLimbsList_eq_isCanonicalBigNat, limbsToNatList_eq_toNat]
          · simp only [hcond, Bool.false_eq_true, ↓reduceIte]

/-- Any `NatVal mem n w` reads back via `Rt.readbackBig` to `some (.nat n)`. -/
theorem NatVal.readbackBig {sig : Sig} {fuel : Nat} {mem : Memory} {n : Nat} {w : Word}
    (h : NatVal mem n w) :
    Rt.readbackBig sig fuel mem .nat w = some (.nat n) := by
  unfold Rt.readbackBig
  rw [readbackNatWord_eq_readbackBigNat, h.readback]
  rfl

end IxCC.Rt.BigNat
