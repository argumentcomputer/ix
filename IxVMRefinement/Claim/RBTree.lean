import IxVMRefinement.Obs.RBTreeMap
import IxVMRefinement.Lib.Bytes
import IxVMRefinement.Lib.Words
import IxVMRefinement.Core.Ctx

/-! # Red-black address maps (`RBTreeMap`), over observed derivations

`RBTreeMap::RBTreeMap<V>` is a search tree keyed by 32-byte `Bytes::AddressRef` pointers and
ordered lexicographically across all eight big-endian 32-bit chunks (`canon_addr_cmp`).

We map each 32-byte `Bytes.Address` injectively to its 256-bit big-endian natural rank
`addrRank : Bytes.Address → Nat`, so strict key comparison reduces to `Nat` `<`. Separating the
structural in-order entry list (`RBTreeEntries`) from pairwise key sorting (`RBTreeBST`) makes
all four rotation arms of `rbtree_map_balance_fix` preserve the entry list up to `List.append_assoc`
with zero ordering casework. -/

namespace IxVM.Refinement.Claim

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library
open IxVM.Refinement.Core (addrTy addrMapEnum AddrMapAll ixAddr)
open IxVM.Refinement.Obs (W)
open IxVM (F)

set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## Address injectivity and field-cast helpers -/

theorem ixAddr_injective : Function.Injective ixAddr := by
  intro a b h
  cases a with | mk arrA szA =>
  cases b with | mk arrB szB =>
  unfold ixAddr at h
  injection h with h1
  injection h1 with h2
  subst h2
  rfl

theorem val_of_lt_u32 {n : Nat} (hn : n < 4294967296) : ZMod.val (n : F) = n :=
  ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)

theorem natCast_inj_of_lt_u32 {m n : Nat} (hm : m < 4294967296) (hn : n < 4294967296)
    (h : (m : F) = (n : F)) : m = n := by
  have hv := congrArg ZMod.val h
  rwa [val_of_lt_u32 hm, val_of_lt_u32 hn] at hv

theorem loadValue_snoc_self (h : Heap F) (v : SourceValue F) :
    loadValue (h ++ [v]) (.ptr v.type h.length) = .ok v := by
  have cell : (h ++ [v])[h.length]? = some v := by simp
  simp [loadValue, cell, bind, Except.bind, pure, Except.pure]

theorem loadValue_eq_inj {h : Heap F} {p v₁ v₂ : SourceValue F}
    (h1 : loadValue h p = .ok v₁) (h2 : loadValue h p = .ok v₂) : v₁ = v₂ :=
  Except.ok.inj (h1.symm.trans h2)

/-! ## Three-way natural comparison and 256-bit address rank -/

/-- Three-way comparison code matching `canon_ord_cmp_g`: `0` (`<`), `1` (`=`), `2` (`>`). -/
def cmpNat (x y : Nat) : Nat :=
  if x < y then 0 else if x = y then 1 else 2

/-- Lexicographic combination matching `canon_ord_then`. -/
def thenCmp (c1 c2 : Nat) : Nat :=
  if c1 = 1 then c2 else c1

theorem cmpNat_values (x y : Nat) : cmpNat x y = 0 ∨ cmpNat x y = 1 ∨ cmpNat x y = 2 := by
  unfold cmpNat
  by_cases h1 : x < y
  · rw [ite_eq_left h1]; exact .inl rfl
  · rw [ite_eq_right h1]
    by_cases h2 : x = y
    · rw [ite_eq_left h2]; exact .inr (.inl rfl)
    · rw [ite_eq_right h2]; exact .inr (.inr rfl)

theorem cmpNat_lt_u32 (x y : Nat) : cmpNat x y < 4294967296 := by
  rcases cmpNat_values x y with h | h | h <;> omega

@[simp] theorem cmpNat_eq_zero_iff {x y : Nat} : cmpNat x y = 0 ↔ x < y := by
  unfold cmpNat
  by_cases h1 : x < y
  · rw [ite_eq_left h1]; omega
  · rw [ite_eq_right h1]
    by_cases h2 : x = y
    · rw [ite_eq_left h2]; omega
    · rw [ite_eq_right h2]; omega

@[simp] theorem cmpNat_eq_one_iff {x y : Nat} : cmpNat x y = 1 ↔ x = y := by
  unfold cmpNat
  by_cases h1 : x < y
  · rw [ite_eq_left h1]; omega
  · rw [ite_eq_right h1]
    by_cases h2 : x = y
    · rw [ite_eq_left h2]; omega
    · rw [ite_eq_right h2]; omega

@[simp] theorem cmpNat_eq_two_iff {x y : Nat} : cmpNat x y = 2 ↔ y < x := by
  unfold cmpNat
  by_cases h1 : x < y
  · rw [ite_eq_left h1]; omega
  · rw [ite_eq_right h1]
    by_cases h2 : x = y
    · rw [ite_eq_left h2]; omega
    · rw [ite_eq_right h2]; omega

theorem thenCmp_cmpNat {x y rx ry B : Nat} (hrx : rx < B) (hry : ry < B) :
    thenCmp (cmpNat x y) (cmpNat rx ry) = cmpNat (x * B + rx) (y * B + ry) := by
  unfold thenCmp cmpNat
  by_cases hxy : x < y
  · have hlt : x * B + rx < y * B + ry := by
      have hle : (x + 1) * B ≤ y * B := Nat.mul_le_mul_right B hxy
      have hexp : (x + 1) * B = x * B + B := (Nat.add_mul x 1 B).trans (by simp)
      omega
    rw [ite_eq_left hxy, ite_eq_left hlt]
    simp
  · rw [ite_eq_right hxy]
    by_cases heq : x = y
    · subst heq
      have hlt_iff : (x * B + rx < x * B + ry) ↔ (rx < ry) := by omega
      have heq_iff : (x * B + rx = x * B + ry) ↔ (rx = ry) := by omega
      simp [hlt_iff, heq_iff]
    · have hyx : y < x := by omega
      have hgt : y * B + ry < x * B + rx := by
        have hle : (y + 1) * B ≤ x * B := Nat.mul_le_mul_right B hyx
        have hexp : (y + 1) * B = y * B + B := (Nat.add_mul y 1 B).trans (by simp)
        omega
      have nlt : ¬ (x * B + rx < y * B + ry) := by omega
      have neq : ¬ (x * B + rx = y * B + ry) := by omega
      rw [ite_eq_right heq, ite_eq_right nlt, ite_eq_right neq]
      simp

/-- Big-endian 32-bit word from four bytes (`canon_addr_chunk`). -/
def packChunk (b0 b1 b2 b3 : UInt8) : Nat :=
  b0.toNat * 16777216 + b1.toNat * 65536 + b2.toNat * 256 + b3.toNat

theorem packChunk_lt (b0 b1 b2 b3 : UInt8) : packChunk b0 b1 b2 b3 < 4294967296 := by
  have h0 := b0.toNat_lt
  have h1 := b1.toNat_lt
  have h2 := b2.toNat_lt
  have h3 := b3.toNat_lt
  unfold packChunk
  omega

theorem packChunk_inj {a0 a1 a2 a3 b0 b1 b2 b3 : UInt8}
    (h : packChunk a0 a1 a2 a3 = packChunk b0 b1 b2 b3) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 := by
  have ha0 := a0.toNat_lt; have ha1 := a1.toNat_lt
  have ha2 := a2.toNat_lt; have ha3 := a3.toNat_lt
  have hb0 := b0.toNat_lt; have hb1 := b1.toNat_lt
  have hb2 := b2.toNat_lt; have hb3 := b3.toNat_lt
  unfold packChunk at h
  have e0 : a0.toNat = b0.toNat := by omega
  have e1 : a1.toNat = b1.toNat := by omega
  have e2 : a2.toNat = b2.toNat := by omega
  have e3 : a3.toNat = b3.toNat := by omega
  exact ⟨UInt8.toNat_inj.mp e0, UInt8.toNat_inj.mp e1,
    UInt8.toNat_inj.mp e2, UInt8.toNat_inj.mp e3⟩

/-- Big-endian value of a non-empty list of 32-bit chunks. -/
def packChunks : List Nat → Nat
  | [] => 0
  | [c] => c
  | c :: cs => c * (4294967296 ^ cs.length) + packChunks cs

theorem packChunks_lt : ∀ {cs : List Nat}, cs ≠ [] → (∀ c ∈ cs, c < 4294967296) →
    packChunks cs < 4294967296 ^ cs.length
  | [], hne, _ => absurd rfl hne
  | [c], _, hbd => by
    simp only [packChunks, List.length_singleton, Nat.pow_one]
    exact hbd c (by simp)
  | c :: d :: cs, _, hbd => by
    simp only [packChunks, List.length_cons]
    have hc : c < 4294967296 := hbd c (by simp)
    have hrest : packChunks (d :: cs) < 4294967296 ^ (d :: cs).length :=
      packChunks_lt (by simp) (fun x hx => hbd x (by simp [hx]))
    set B := 4294967296 ^ (d :: cs).length
    have hle : (c + 1) * B ≤ 4294967296 * B := Nat.mul_le_mul_right B hc
    have hexp : (c + 1) * B = c * B + B := (Nat.add_mul c 1 B).trans (by simp)
    have hpow : 4294967296 ^ (cs.length + 1 + 1) = 4294967296 * B := by
      simp [B, Nat.pow_succ, Nat.mul_comm]
    omega

theorem mul_add_inj {x y rx ry B : Nat} (hrx : rx < B) (hry : ry < B)
    (heq : x * B + rx = y * B + ry) : x = y ∧ rx = ry := by
  by_cases hlt : x < y
  · have hle : (x + 1) * B ≤ y * B := Nat.mul_le_mul_right B hlt
    have hexp : (x + 1) * B = x * B + B := (Nat.add_mul x 1 B).trans (by simp)
    omega
  · by_cases hgt : y < x
    · have hle : (y + 1) * B ≤ x * B := Nat.mul_le_mul_right B hgt
      have hexp : (y + 1) * B = y * B + B := (Nat.add_mul y 1 B).trans (by simp)
      omega
    · have hxy : x = y := by omega
      subst hxy
      exact ⟨rfl, by omega⟩

theorem packChunks_inj : ∀ {xs ys : List Nat},
    xs.length = ys.length →
    (∀ x ∈ xs, x < 4294967296) → (∀ y ∈ ys, y < 4294967296) →
    packChunks xs = packChunks ys → xs = ys
  | [], [], _, _, _, _ => rfl
  | [x], [y], _, _, _, heq => by
    simp only [packChunks] at heq
    exact congrArg (· :: []) heq
  | x :: x2 :: xs, y :: y2 :: ys, hlen, hx, hy, heq => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    have hlen' : (x2 :: xs).length = (y2 :: ys).length := by simp [hlen]
    simp only [packChunks] at heq
    rw [hlen'] at heq
    have hrx : packChunks (x2 :: xs) < 4294967296 ^ (y2 :: ys).length := by
      rw [← hlen']
      exact packChunks_lt (by simp) (fun z hz => hx z (by simp [hz]))
    have hry : packChunks (y2 :: ys) < 4294967296 ^ (y2 :: ys).length :=
      packChunks_lt (by simp) (fun z hz => hy z (by simp [hz]))
    obtain ⟨hxy, hrest⟩ := mul_add_inj hrx hry heq
    subst hxy
    rw [packChunks_inj hlen' (fun z hz => hx z (by simp [hz]))
      (fun z hz => hy z (by simp [hz])) hrest]

theorem thenCmp_packChunks {x y : Nat} {xs ys : List Nat}
    (hne : xs ≠ []) (hlen : xs.length = ys.length)
    (hx : ∀ z ∈ xs, z < 4294967296) (hy : ∀ z ∈ ys, z < 4294967296) :
    thenCmp (cmpNat x y) (cmpNat (packChunks xs) (packChunks ys)) =
      cmpNat (packChunks (x :: xs)) (packChunks (y :: ys)) := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons x2 xs' =>
    cases ys with
    | nil => simp at hlen
    | cons y2 ys' =>
      have hrx : packChunks (x2 :: xs') < 4294967296 ^ (x2 :: xs').length :=
        packChunks_lt (by simp) hx
      have hry : packChunks (y2 :: ys') < 4294967296 ^ (x2 :: xs').length := by
        rw [hlen]
        exact packChunks_lt (by simp) hy
      have key := thenCmp_cmpNat hrx hry
      simpa [packChunks, hlen] using key

/-- The eight 32-bit chunks of a 32-byte address. -/
def addrChunks (a : Bytes.Address) : List Nat :=
  [packChunk a[0] a[1] a[2] a[3],
   packChunk a[4] a[5] a[6] a[7],
   packChunk a[8] a[9] a[10] a[11],
   packChunk a[12] a[13] a[14] a[15],
   packChunk a[16] a[17] a[18] a[19],
   packChunk a[20] a[21] a[22] a[23],
   packChunk a[24] a[25] a[26] a[27],
   packChunk a[28] a[29] a[30] a[31]]

/-- The 256-bit big-endian rank of an address. -/
def addrRank (a : Bytes.Address) : Nat :=
  packChunks (addrChunks a)

theorem addrRank_injective : Function.Injective addrRank := by
  intro a b h
  unfold addrRank at h
  have ha : ∀ c ∈ addrChunks a, c < 4294967296 := by
    intro c hc
    simp only [addrChunks, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact packChunk_lt _ _ _ _
  have hb : ∀ c ∈ addrChunks b, c < 4294967296 := by
    intro c hc
    simp only [addrChunks, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact packChunk_lt _ _ _ _
  have hcs := packChunks_inj (by simp [addrChunks]) ha hb h
  simp only [addrChunks, List.cons.injEq, and_true] at hcs
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := hcs
  obtain ⟨e0, e1, e2, e3⟩ := packChunk_inj c0
  obtain ⟨e4, e5, e6, e7⟩ := packChunk_inj c1
  obtain ⟨e8, e9, e10, e11⟩ := packChunk_inj c2
  obtain ⟨e12, e13, e14, e15⟩ := packChunk_inj c3
  obtain ⟨e16, e17, e18, e19⟩ := packChunk_inj c4
  obtain ⟨e20, e21, e22, e23⟩ := packChunk_inj c5
  obtain ⟨e24, e25, e26, e27⟩ := packChunk_inj c6
  obtain ⟨e28, e29, e30, e31⟩ := packChunk_inj c7
  have hlist : a.toList = b.toList := by
    rw [Lib.vec32_toList a, Lib.vec32_toList b]
    simp [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15,
      e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31]
  exact Vector.toList_inj.mp hlist

/-! ## Specifications of `canon_ord_cmp_g`, `canon_ord_then`, `canon_addr_chunk`, `canon_addr_cmp` -/

theorem canon_ord_cmp_g_spec {m n : Nat} (hm : m < 4294967296) (hn : n < 4294967296)
    {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "RBTreeMap::canon_ord_cmp_g" [.field (m : F), .field (n : F)] h r h' cs) :
    r = .field (cmpNat m n : F) ∧ h' = h := by
  rcases Obs.«RBTreeMap::canon_ord_cmp_g».obs ev with
    ⟨op17, rfl, rfl, -⟩ |
    ⟨v1, m32, cs43, op17, hne27, ev45, rfl, rfl, -⟩ |
    ⟨v1, m32, cs43, op17, hne27, ev45, rfl, rfl, -⟩
  · simp only [evalBinOp, Except.ok.injEq, Value.field.injEq] at op17
    have hmn : m = n := natCast_inj_of_lt_u32 hm hn (sub_eq_zero.mp op17)
    subst hmn
    have hc : cmpNat m m = 1 := cmpNat_eq_one_iff.mpr rfl
    exact ⟨by simp [hc], rfl⟩
  · obtain ⟨_, _, hlt, _, hh⟩ := Lib.less_than_fields_field ev45
    have hmn : m < n := by
      have hv := hlt.mp rfl
      rwa [val_of_lt_u32 hm, val_of_lt_u32 hn] at hv
    have hc : cmpNat m n = 0 := cmpNat_eq_zero_iff.mpr hmn
    exact ⟨by simp [hc], hh⟩
  · obtain ⟨_, _, hlt, _, hh⟩ := Lib.less_than_fields_field ev45
    have nlt : ¬ m < n := by
      intro hmn
      have hv : ZMod.val (m : F) < ZMod.val (n : F) := by
        rwa [val_of_lt_u32 hm, val_of_lt_u32 hn]
      have e := hlt.mpr hv
      exact zero_ne_one (Value.field.inj e)
    have hne : m ≠ n := by
      intro e
      subst e
      simp only [evalBinOp, sub_self, Except.ok.injEq] at op17
      exact hne27 op17.symm
    have hnm : n < m := by omega
    have hc : cmpNat m n = 2 := cmpNat_eq_two_iff.mpr hnm
    exact ⟨by simp [hc], hh⟩

theorem canon_ord_then_spec {c1 c2 : Nat} (hc1 : c1 = 0 ∨ c1 = 1 ∨ c1 = 2)
    {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "RBTreeMap::canon_ord_then" [.field (c1 : F), .field (c2 : F)] h r h' cs) :
    r = .field (thenCmp c1 c2 : F) ∧ h' = h := by
  rcases Obs.«RBTreeMap::canon_ord_then».obs ev with
    ⟨hv, rfl, rfl, -⟩ | ⟨hne, rfl, rfl, -⟩
  · have hc1_lt : c1 < 4294967296 := by omega
    have he1 : c1 = 1 := natCast_inj_of_lt_u32 hc1_lt (by decide) (Value.field.inj hv)
    subst he1
    exact ⟨by simp [thenCmp], rfl⟩
  · have ne1 : c1 ≠ 1 := by
      intro e
      subst e
      exact hne rfl
    exact ⟨by simp [thenCmp, ne1], rfl⟩

theorem canon_addr_chunk_spec {a0 a1 a2 a3 b0 b1 b2 b3 : UInt8}
    {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "RBTreeMap::canon_addr_chunk"
      [.field (a0.toNat : F), .field (a1.toNat : F), .field (a2.toNat : F), .field (a3.toNat : F),
       .field (b0.toNat : F), .field (b1.toNat : F), .field (b2.toNat : F), .field (b3.toNat : F)]
      h r h' cs) :
    r = .field (cmpNat (packChunk a0 a1 a2 a3) (packChunk b0 b1 b2 b3) : F) ∧ h' = h := by
  obtain ⟨v1, x9, x17, y18, x25, y26, v61, x69, x77, y78, x85, y86, cs124,
    op40, op49, op32, op58, op24, op16, op100, op109, op92, op118, op84, op76, ev126, -⟩ :=
    Obs.«RBTreeMap::canon_addr_chunk».obs ev
  simp only [evalBinOp, Except.ok.injEq] at
    op40 op49 op32 op58 op24 op16 op100 op109 op92 op118 op84 op76
  subst op40 op49 op32 op58 op24 op16 op100 op109 op92 op118 op84 op76
  have hx : ((a0.toNat : F) * 16777216 + (a1.toNat : F) * 65536 +
      (a2.toNat : F) * 256 + (a3.toNat : F)) = (packChunk a0 a1 a2 a3 : F) := by
    unfold packChunk; push_cast; ring
  have hy : ((b0.toNat : F) * 16777216 + (b1.toNat : F) * 65536 +
      (b2.toNat : F) * 256 + (b3.toNat : F)) = (packChunk b0 b1 b2 b3 : F) := by
    unfold packChunk; push_cast; ring
  rw [hx, hy] at ev126
  exact canon_ord_cmp_g_spec (packChunk_lt _ _ _ _) (packChunk_lt _ _ _ _) ev126

section CanonAddrCmp

private theorem computes_let_load {h : Heap F} {locals : List (String × SourceValue F)}
    {p bname : String} {ptr val : SourceValue F} {rest : Generic.Expr F} {w : F}
    (hp : locals.find? (·.1 == p) = some (p, ptr))
    (hl : ∀ v, loadValue h ptr = .ok v → v = val)
    (hrest : Lib.ComputesAt h ((bname, val) :: locals) rest w) :
    Lib.ComputesAt h locals (.letValue (.bind bname) (.load (.var p)) rest) w := by
  intro r h' cs d
  obtain ⟨input, m, bs, c1, c2, dv, mt, db, -⟩ := d.letValue_inv
  obtain ⟨q, dq, ld⟩ := dv.load_inv
  obtain ⟨lq, hm, -⟩ := dq.var_inv
  subst hm
  have hq : q = ptr := (Prod.mk.inj (Option.some.inj (lq.symm.trans hp))).2
  subst hq
  have hin := hl _ ld
  subst hin
  have hbs := matchPattern_bind_inv mt
  subst hbs
  simpa only [List.cons_append, List.nil_append] using hrest _ _ _ db

private theorem projectValue_getElem {vs : List (SourceValue F)} {i : Nat} {r : SourceValue F}
    (hi : i < vs.length) (hp : projectValue (.tuple vs) i = .ok r) : r = vs[i] := by
  have e : projectValue (Value.tuple vs : SourceValue F) i = .ok vs[i] := by
    simp [projectValue, List.getElem?_eq_getElem hi, bind, Except.bind, pure, Except.pure]
  rw [e] at hp
  exact (Except.ok.inj hp).symm

private theorem addrCell_getElem (a : Bytes.Address) (i : Nat) (hi : i < 32) :
    (Lib.addrCell F a)[i]'(by simp [Lib.addrCell]; exact hi) = .field (a[i].toNat : F) := by
  have hlist : Lib.addrCell F a = a.toList.map (fun c => Value.field (c.toNat : F)) := by
    rw [Lib.vec32_toList a]; rfl
  simp [hlist]

private theorem computes_idx_byte {h : Heap F} {locals : List (String × SourceValue F)}
    {n : String} {a : Bytes.Address} {i : Nat} (hi : i < 32)
    (hn : locals.find? (·.1 == n) = some (n, .tuple (Lib.addrCell F a))) :
    Lib.ComputesAt h locals
      (.call "UInt8::to_field" (some []) [.index (.var n) i]) (a[i].toNat : F) := by
  intro r h' cs d
  obtain ⟨vs, m, c1, c2, args, ev, -⟩ := d.call_inv
  rw [instanceName_plain_some] at ev
  obtain ⟨v, vs2, m2, c3, c4, rfl, dv, args2, -⟩ := args.cons_inv
  obtain ⟨rfl, rfl, -⟩ := args2.nil_inv
  obtain ⟨tup, dtup, pr⟩ := dv.index_inv
  obtain ⟨ltup, rfl, -⟩ := dtup.var_inv
  have htup : tup = .tuple (Lib.addrCell F a) :=
    (Prod.mk.inj (Option.some.inj (ltup.symm.trans hn))).2
  subst htup
  have hlen : i < (Lib.addrCell F a).length := by simp [Lib.addrCell]; exact hi
  have hv : v = .field (a[i].toNat : F) :=
    (projectValue_getElem hlen pr).trans (addrCell_getElem a i hi)
  subst hv
  exact Lib.u8_to_field_spec ev

private theorem computes_chunk {h : Heap F} {locals : List (String × SourceValue F)}
    {e0 e1 e2 e3 f0 f1 f2 f3 : Generic.Expr F}
    {a0 a1 a2 a3 b0 b1 b2 b3 : UInt8}
    (ha0 : Lib.ComputesAt h locals e0 (a0.toNat : F))
    (ha1 : Lib.ComputesAt h locals e1 (a1.toNat : F))
    (ha2 : Lib.ComputesAt h locals e2 (a2.toNat : F))
    (ha3 : Lib.ComputesAt h locals e3 (a3.toNat : F))
    (hb0 : Lib.ComputesAt h locals f0 (b0.toNat : F))
    (hb1 : Lib.ComputesAt h locals f1 (b1.toNat : F))
    (hb2 : Lib.ComputesAt h locals f2 (b2.toNat : F))
    (hb3 : Lib.ComputesAt h locals f3 (b3.toNat : F)) :
    Lib.ComputesAt h locals
      (.call "RBTreeMap::canon_addr_chunk" (some []) [e0, e1, e2, e3, f0, f1, f2, f3])
      (cmpNat (packChunk a0 a1 a2 a3) (packChunk b0 b1 b2 b3) : F) := by
  intro r h' cs d
  obtain ⟨vs, m, c1, c2, args, ev, -⟩ := d.call_inv
  rw [instanceName_plain_some] at ev
  obtain ⟨v0, _, m0, _, _, rfl, d0, args, -⟩ := args.cons_inv
  obtain ⟨rfl, rfl⟩ := ha0 _ _ _ d0
  obtain ⟨v1, _, m1, _, _, rfl, d1, args, -⟩ := args.cons_inv
  obtain ⟨rfl, rfl⟩ := ha1 _ _ _ d1
  obtain ⟨v2, _, m2, _, _, rfl, d2, args, -⟩ := args.cons_inv
  obtain ⟨rfl, rfl⟩ := ha2 _ _ _ d2
  obtain ⟨v3, _, m3, _, _, rfl, d3, args, -⟩ := args.cons_inv
  obtain ⟨rfl, rfl⟩ := ha3 _ _ _ d3
  obtain ⟨w0, _, n0, _, _, rfl, g0, args, -⟩ := args.cons_inv
  obtain ⟨rfl, rfl⟩ := hb0 _ _ _ g0
  obtain ⟨w1, _, n1, _, _, rfl, g1, args, -⟩ := args.cons_inv
  obtain ⟨rfl, rfl⟩ := hb1 _ _ _ g1
  obtain ⟨w2, _, n2, _, _, rfl, g2, args, -⟩ := args.cons_inv
  obtain ⟨rfl, rfl⟩ := hb2 _ _ _ g2
  obtain ⟨w3, _, n3, _, _, rfl, g3, args, -⟩ := args.cons_inv
  obtain ⟨rfl, rfl⟩ := hb3 _ _ _ g3
  obtain ⟨rfl, rfl, -⟩ := args.nil_inv
  exact canon_addr_chunk_spec ev

private theorem computes_then {h : Heap F} {locals : List (String × SourceValue F)}
    {e1 e2 : Generic.Expr F} {c1 c2 : Nat}
    (hc1 : c1 = 0 ∨ c1 = 1 ∨ c1 = 2)
    (h1 : Lib.ComputesAt h locals e1 (c1 : F))
    (h2 : Lib.ComputesAt h locals e2 (c2 : F)) :
    Lib.ComputesAt h locals
      (.call "RBTreeMap::canon_ord_then" (some []) [e1, e2])
      (thenCmp c1 c2 : F) := by
  intro r h' cs d
  obtain ⟨vs, m, ca, cb, args, ev, -⟩ := d.call_inv
  rw [instanceName_plain_some] at ev
  obtain ⟨v1, _, m1, _, _, rfl, d1, args, -⟩ := args.cons_inv
  obtain ⟨rfl, rfl⟩ := h1 _ _ _ d1
  obtain ⟨v2, _, m2, _, _, rfl, d2, args, -⟩ := args.cons_inv
  obtain ⟨rfl, rfl⟩ := h2 _ _ _ d2
  obtain ⟨rfl, rfl, -⟩ := args.nil_inv
  exact canon_ord_then_spec hc1 ev

local macro "rbtree_lookup" : tactic =>
  `(tactic| repeat (first | exact Lib.find_here | refine Lib.find_skip (by decide) ?_))

local macro "rbtree_chunk" : tactic =>
  `(tactic| refine computes_chunk
      (computes_idx_byte (by decide) (by rbtree_lookup))
      (computes_idx_byte (by decide) (by rbtree_lookup))
      (computes_idx_byte (by decide) (by rbtree_lookup))
      (computes_idx_byte (by decide) (by rbtree_lookup))
      (computes_idx_byte (by decide) (by rbtree_lookup))
      (computes_idx_byte (by decide) (by rbtree_lookup))
      (computes_idx_byte (by decide) (by rbtree_lookup))
      (computes_idx_byte (by decide) (by rbtree_lookup)))

set_option maxHeartbeats 2000000 in
/-- **`RBTreeMap::canon_addr_cmp`**: compares all 32 bytes of two represented addresses as
`cmpNat (addrRank a) (addrRank b)` (`0` if `<`, `1` if `=`, `2` if `>`), without allocating. -/
theorem canon_addr_cmp_spec {x y r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {a b : Bytes.Address}
    (hx : Bytes.RepAddressRef addrTy h a x) (hy : Bytes.RepAddressRef addrTy h b y)
    (ev : ObsFn W "RBTreeMap::canon_addr_cmp" [x, y] h r h' cs) :
    r = .field (cmpNat (addrRank a) (addrRank b) : F) ∧ h' = h := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.RBTreeMap.canon_addr_cmp.lookup
    (by simp [IxVM.RBTreeMap.canon_addr_cmp, ControlLower.hasControl]) ev
  simp only [IxVM.RBTreeMap.canon_addr_cmp, List.map, List.zip, List.zipWith] at d0
  have comp : Lib.ComputesAt h [("x", x), ("y", y)] IxVM.RBTreeMap.canon_addr_cmp.body
      (thenCmp (cmpNat (packChunk a[0] a[1] a[2] a[3]) (packChunk b[0] b[1] b[2] b[3]))
        (thenCmp (cmpNat (packChunk a[4] a[5] a[6] a[7]) (packChunk b[4] b[5] b[6] b[7]))
          (thenCmp (cmpNat (packChunk a[8] a[9] a[10] a[11]) (packChunk b[8] b[9] b[10] b[11]))
            (thenCmp (cmpNat (packChunk a[12] a[13] a[14] a[15]) (packChunk b[12] b[13] b[14] b[15]))
              (thenCmp (cmpNat (packChunk a[16] a[17] a[18] a[19]) (packChunk b[16] b[17] b[18] b[19]))
                (thenCmp (cmpNat (packChunk a[20] a[21] a[22] a[23]) (packChunk b[20] b[21] b[22] b[23]))
                  (thenCmp (cmpNat (packChunk a[24] a[25] a[26] a[27]) (packChunk b[24] b[25] b[26] b[27]))
                    (cmpNat (packChunk a[28] a[29] a[30] a[31]) (packChunk b[28] b[29] b[30] b[31]))))))))) := by
    simp only [IxVM.RBTreeMap.canon_addr_cmp]
    refine computes_let_load (by rbtree_lookup) (Lib.load_addr hx) ?_
    refine computes_let_load (by rbtree_lookup) (Lib.load_addr hy) ?_
    refine computes_then (cmpNat_values _ _) (by rbtree_chunk) ?_
    refine computes_then (cmpNat_values _ _) (by rbtree_chunk) ?_
    refine computes_then (cmpNat_values _ _) (by rbtree_chunk) ?_
    refine computes_then (cmpNat_values _ _) (by rbtree_chunk) ?_
    refine computes_then (cmpNat_values _ _) (by rbtree_chunk) ?_
    refine computes_then (cmpNat_values _ _) (by rbtree_chunk) ?_
    refine computes_then (cmpNat_values _ _) (by rbtree_chunk) ?_
    rbtree_chunk
  obtain ⟨hr, hh⟩ := comp r h' cs d0
  have hfold :
      thenCmp (cmpNat (packChunk a[0] a[1] a[2] a[3]) (packChunk b[0] b[1] b[2] b[3]))
        (thenCmp (cmpNat (packChunk a[4] a[5] a[6] a[7]) (packChunk b[4] b[5] b[6] b[7]))
          (thenCmp (cmpNat (packChunk a[8] a[9] a[10] a[11]) (packChunk b[8] b[9] b[10] b[11]))
            (thenCmp (cmpNat (packChunk a[12] a[13] a[14] a[15]) (packChunk b[12] b[13] b[14] b[15]))
              (thenCmp (cmpNat (packChunk a[16] a[17] a[18] a[19]) (packChunk b[16] b[17] b[18] b[19]))
                (thenCmp (cmpNat (packChunk a[20] a[21] a[22] a[23]) (packChunk b[20] b[21] b[22] b[23]))
                  (thenCmp (cmpNat (packChunk a[24] a[25] a[26] a[27]) (packChunk b[24] b[25] b[26] b[27]))
                    (cmpNat (packChunk a[28] a[29] a[30] a[31]) (packChunk b[28] b[29] b[30] b[31])))))))) =
        cmpNat (addrRank a) (addrRank b) := by
    have bnd : ∀ (u0 u1 u2 u3 : UInt8), packChunk u0 u1 u2 u3 < 4294967296 := packChunk_lt
    unfold addrRank addrChunks
    change thenCmp _ (thenCmp _ (thenCmp _ (thenCmp _ (thenCmp _ (thenCmp _
      (thenCmp (cmpNat _ _) (cmpNat (packChunks [_]) (packChunks [_])))))))) = _
    rw [thenCmp_packChunks (by simp) (by simp) (by simp [bnd]) (by simp [bnd])]
    rw [thenCmp_packChunks (by simp) (by simp) (by simp [bnd]) (by simp [bnd])]
    rw [thenCmp_packChunks (by simp) (by simp) (by simp [bnd]) (by simp [bnd])]
    rw [thenCmp_packChunks (by simp) (by simp) (by simp [bnd]) (by simp [bnd])]
    rw [thenCmp_packChunks (by simp) (by simp) (by simp [bnd]) (by simp [bnd])]
    rw [thenCmp_packChunks (by simp) (by simp) (by simp [bnd]) (by simp [bnd])]
    rw [thenCmp_packChunks (by simp) (by simp) (by simp [bnd]) (by simp [bnd])]
  exact ⟨hr.trans (congrArg Value.field (congrArg Nat.cast hfold)), hh⟩

end CanonAddrCmp

/-! ## Structural in-order entries and BST invariant for `RBTreeMap` -/

/-- Enum name for `RBTreeMap::RBTreeMap<t_V>`. -/
abbrev rbtreeEnum (t_V : Generic.Ty) : String :=
  (Instance.mk "RBTreeMap::RBTreeMap" [t_V]).symbol

@[simp] theorem rbtreeEnum_field : rbtreeEnum .field = addrMapEnum := by decide +kernel

/-- Structural relation pairing an `RBTreeMap<t_V>` value with its in-order list of
`(address, value)` entries. -/
inductive RBTreeEntries (t_V : Generic.Ty) (h : Heap F) :
    List (Bytes.Address × SourceValue F) → SourceValue F → Prop where
  | nil : RBTreeEntries t_V h [] (.construct (rbtreeEnum t_V) "Nil" [])
  | node {c : F} {kp v lp rp lv rv : SourceValue F} {a : Bytes.Address}
      {ls rs : List (Bytes.Address × SourceValue F)}
      (hk : Bytes.RepAddressRef addrTy h a kp)
      (hl : loadValue h lp = .ok lv) (hr : loadValue h rp = .ok rv)
      (rl : RBTreeEntries t_V h ls lv) (rr : RBTreeEntries t_V h rs rv) :
      RBTreeEntries t_V h (ls ++ [(a, v)] ++ rs)
        (.construct (rbtreeEnum t_V) "Node" [.field c, kp, v, lp, rp])

theorem RBTreeEntries.mono {t_V : Generic.Ty} {h₁ h₂ : Heap F}
    {es : List (Bytes.Address × SourceValue F)} {tree : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (ht : RBTreeEntries t_V h₁ es tree) :
    RBTreeEntries t_V h₂ es tree := by
  induction ht with
  | nil => exact .nil
  | node hk hl hr _ _ ihl ihr =>
    exact .node (Bytes.repAddressRef_heapMono₂ addrTy ext hk)
      (ext.loadValue_eq hl) (ext.loadValue_eq hr) ihl ihr

theorem RBTreeEntries.nil_inv {t_V : Generic.Ty} {h : Heap F}
    {es : List (Bytes.Address × SourceValue F)}
    (ht : RBTreeEntries t_V h es (.construct (rbtreeEnum t_V) "Nil" [])) : es = [] := by
  generalize hv : (Value.construct (rbtreeEnum t_V) "Nil" [] : SourceValue F) = tree at ht
  cases ht with
  | nil => rfl
  | node _ _ _ _ _ => injection hv with _ hc _; cases hc

theorem RBTreeEntries.node_inv {t_V : Generic.Ty} {h : Heap F}
    {es : List (Bytes.Address × SourceValue F)}
    {cv kp v lp rp : SourceValue F}
    (ht : RBTreeEntries t_V h es (.construct (rbtreeEnum t_V) "Node" [cv, kp, v, lp, rp])) :
    ∃ (c : F) (a : Bytes.Address) (lv rv : SourceValue F)
      (ls rs : List (Bytes.Address × SourceValue F)),
      cv = .field c ∧ es = ls ++ [(a, v)] ++ rs ∧
      Bytes.RepAddressRef addrTy h a kp ∧
      loadValue h lp = .ok lv ∧ loadValue h rp = .ok rv ∧
      RBTreeEntries t_V h ls lv ∧ RBTreeEntries t_V h rs rv := by
  generalize hv :
    (Value.construct (rbtreeEnum t_V) "Node" [cv, kp, v, lp, rp] : SourceValue F) = tree at ht
  cases ht with
  | nil => injection hv with _ hc _; cases hc
  | node hk hl hr rl rr =>
    injection hv with _ _ hargs
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
    exact ⟨_, _, _, _, _, _, rfl, rfl, hk, hl, hr, rl, rr⟩

/-- Every `RBTreeEntries .field` whose entries satisfy `P` yields `Core.AddrMapAll`. -/
theorem RBTreeEntries.toAddrMapAll {h : Heap F} {es : List (Bytes.Address × SourceValue F)}
    {tree : SourceValue F} {P : Heap F → Bytes.Address → SourceValue F → Prop}
    (ht : RBTreeEntries .field h es tree) (hP : ∀ p ∈ es, P h p.1 p.2) :
    AddrMapAll addrMapEnum P h tree := by
  induction ht with
  | nil =>
    rw [rbtreeEnum_field]
    exact .nil
  | node hk hl hr _ _ ihl ihr =>
    rw [rbtreeEnum_field]
    exact .node hk (hP _ (by simp)) hl hr
      (ihl (fun p hp => hP p (by simp [hp])))
      (ihr (fun p hp => hP p (by simp [hp])))

/-- BST-ordered `RBTreeMap<t_V>`: structural `RBTreeEntries` with strictly increasing `addrRank`. -/
def RBTreeBST (t_V : Generic.Ty) (h : Heap F)
    (es : List (Bytes.Address × SourceValue F)) (tree : SourceValue F) : Prop :=
  RBTreeEntries t_V h es tree ∧ es.Pairwise (fun p q => addrRank p.1 < addrRank q.1)

theorem RBTreeBST.mono {t_V : Generic.Ty} {h₁ h₂ : Heap F}
    {es : List (Bytes.Address × SourceValue F)} {tree : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (hb : RBTreeBST t_V h₁ es tree) :
    RBTreeBST t_V h₂ es tree :=
  ⟨hb.1.mono ext, hb.2⟩

theorem RBTreeBST.nil (t_V : Generic.Ty) (h : Heap F) :
    RBTreeBST t_V h [] (.construct (rbtreeEnum t_V) "Nil" []) :=
  ⟨.nil, List.Pairwise.nil⟩

/-! ## Pure model operations on sorted entry lists (`lookupEntries` and `insSorted`) -/

/-- Pure lookup in a sorted `(address, value)` association list. -/
def lookupEntries (a : Bytes.Address)
    (es : List (Bytes.Address × SourceValue F)) (dflt : SourceValue F) : SourceValue F :=
  match es.find? (fun p => decide (p.1 = a)) with
  | some (_, v) => v
  | none => dflt

/-- Pure insertion/overwrite into a sorted `(address, value)` association list. -/
def insSorted (a : Bytes.Address) (v : SourceValue F) :
    List (Bytes.Address × SourceValue F) → List (Bytes.Address × SourceValue F)
  | [] => [(a, v)]
  | (k, w) :: es =>
    if addrRank a < addrRank k then (a, v) :: (k, w) :: es
    else if a = k then (a, v) :: es
    else (k, w) :: insSorted a v es

theorem mem_insSorted {a : Bytes.Address} {v : SourceValue F}
    {es : List (Bytes.Address × SourceValue F)} {p : Bytes.Address × SourceValue F} :
    p ∈ insSorted a v es → p = (a, v) ∨ p ∈ es := by
  induction es with
  | nil =>
    intro hp
    simp [insSorted] at hp
    exact .inl hp
  | cons kw rest ih =>
    intro hp
    rcases kw with ⟨k, w⟩
    unfold insSorted at hp
    by_cases hlt : addrRank a < addrRank k
    · rw [ite_eq_left hlt] at hp
      simp at hp
      rcases hp with rfl | rfl | hmem
      · exact .inl rfl
      · exact .inr (by simp)
      · exact .inr (by simp [hmem])
    · rw [ite_eq_right hlt] at hp
      by_cases heq : a = k
      · rw [ite_eq_left heq] at hp
        simp at hp
        rcases hp with rfl | hmem
        · exact .inl rfl
        · exact .inr (by simp [hmem])
      · rw [ite_eq_right heq] at hp
        simp at hp
        rcases hp with rfl | hmem
        · exact .inr (by simp)
        · rcases ih hmem with rfl | hmem'
          · exact .inl rfl
          · exact .inr (by simp [hmem'])

theorem mem_insSorted_self (a : Bytes.Address) (v : SourceValue F)
    (es : List (Bytes.Address × SourceValue F)) : (a, v) ∈ insSorted a v es := by
  induction es with
  | nil => simp [insSorted]
  | cons kw rest ih =>
    rcases kw with ⟨k, w⟩
    unfold insSorted
    by_cases hlt : addrRank a < addrRank k
    · rw [ite_eq_left hlt]; simp
    · rw [ite_eq_right hlt]
      by_cases heq : a = k
      · rw [ite_eq_left heq]; simp
      · rw [ite_eq_right heq]; simp [ih]

theorem mem_fst_insSorted_iff {a k : Bytes.Address} {v : SourceValue F}
    {es : List (Bytes.Address × SourceValue F)} :
    (∃ w, (k, w) ∈ insSorted a v es) ↔ (k = a ∨ ∃ w, (k, w) ∈ es) := by
  constructor
  · rintro ⟨w, hw⟩
    rcases mem_insSorted hw with heq | hmem
    · injection heq with hka _; exact .inl hka
    · exact .inr ⟨w, hmem⟩
  · rintro (rfl | ⟨w, hw⟩)
    · exact ⟨v, mem_insSorted_self k v es⟩
    · induction es with
      | nil => cases hw
      | cons kw rest ih =>
        rcases kw with ⟨k0, w0⟩
        unfold insSorted
        simp at hw
        by_cases hlt : addrRank a < addrRank k0
        · rw [ite_eq_left hlt]
          rcases hw with ⟨rfl, rfl⟩ | hrest
          · exact ⟨w0, by simp⟩
          · exact ⟨w, by simp [hrest]⟩
        · rw [ite_eq_right hlt]
          by_cases heq : a = k0
          · rw [ite_eq_left heq]
            subst heq
            rcases hw with ⟨rfl, _⟩ | hrest
            · exact ⟨v, by simp⟩
            · exact ⟨w, by simp [hrest]⟩
          · rw [ite_eq_right heq]
            rcases hw with ⟨rfl, rfl⟩ | hrest
            · exact ⟨w0, by simp⟩
            · obtain ⟨w', hw'⟩ := ih hrest
              exact ⟨w', by simp [hw']⟩

theorem insSorted_pairwise {a : Bytes.Address} {v : SourceValue F}
    {es : List (Bytes.Address × SourceValue F)}
    (hpw : es.Pairwise (fun p q => addrRank p.1 < addrRank q.1)) :
    (insSorted a v es).Pairwise (fun p q => addrRank p.1 < addrRank q.1) := by
  induction es with
  | nil => simp [insSorted]
  | cons kw rest ih =>
    rcases kw with ⟨k, w⟩
    obtain ⟨hhead, hrest⟩ := List.pairwise_cons.mp hpw
    unfold insSorted
    by_cases hlt : addrRank a < addrRank k
    · rw [ite_eq_left hlt]
      refine List.pairwise_cons.mpr ⟨?_, hpw⟩
      intro q hq
      simp at hq
      rcases hq with rfl | hq
      · exact hlt
      · exact Nat.lt_trans hlt (hhead q hq)
    · rw [ite_eq_right hlt]
      by_cases heq : a = k
      · rw [ite_eq_left heq]
        subst heq
        exact List.pairwise_cons.mpr ⟨hhead, hrest⟩
      · rw [ite_eq_right heq]
        have hklt : addrRank k < addrRank a := by
          have hne : addrRank a ≠ addrRank k := fun e => heq (addrRank_injective e)
          omega
        refine List.pairwise_cons.mpr ⟨?_, ih hrest⟩
        intro q hq
        rcases mem_insSorted hq with rfl | hq'
        · exact hklt
        · exact hhead q hq'

theorem pairwise_split {ls rs : List (Bytes.Address × SourceValue F)}
    {ak : Bytes.Address} {vk : SourceValue F}
    (hpw : (ls ++ [(ak, vk)] ++ rs).Pairwise (fun p q => addrRank p.1 < addrRank q.1)) :
    ls.Pairwise (fun p q => addrRank p.1 < addrRank q.1) ∧
    rs.Pairwise (fun p q => addrRank p.1 < addrRank q.1) ∧
    (∀ p ∈ ls, addrRank p.1 < addrRank ak) ∧
    (∀ q ∈ rs, addrRank ak < addrRank q.1) := by
  rw [List.append_assoc, List.pairwise_append] at hpw
  obtain ⟨hpwL, hpwKR, hcross1⟩ := hpw
  simp only [List.singleton_append, List.pairwise_cons] at hpwKR
  obtain ⟨hkr, hpwR⟩ := hpwKR
  refine ⟨hpwL, hpwR, ?_, hkr⟩
  intro p hp
  exact hcross1 p hp (ak, vk) (by simp)

theorem find_append_left_of_not {α : Type} {p : α → Bool} {xs ys : List α}
    (hno : ∀ x ∈ xs, p x = false) : (xs ++ ys).find? p = ys.find? p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.find?, hno x (by simp), ih (fun z hz => hno z (by simp [hz]))]

theorem find_append_right_of_not {α : Type} {p : α → Bool} {xs ys : List α}
    (hno : ∀ y ∈ ys, p y = false) : (xs ++ ys).find? p = xs.find? p := by
  induction xs with
  | nil =>
    induction ys with
    | nil => rfl
    | cons y ys ihy =>
      simp [List.find?, hno y (by simp), ihy (fun z hz => hno z (by simp [hz]))]
  | cons x xs ih =>
    simp only [List.cons_append, List.find?]
    cases p x
    · exact ih
    · rfl

theorem lookupEntries_split_lt {a ak : Bytes.Address} {vk dflt : SourceValue F}
    {ls rs : List (Bytes.Address × SourceValue F)}
    (hpw : (ls ++ [(ak, vk)] ++ rs).Pairwise (fun p q => addrRank p.1 < addrRank q.1))
    (hlt : addrRank a < addrRank ak) :
    lookupEntries a (ls ++ [(ak, vk)] ++ rs) dflt = lookupEntries a ls dflt := by
  obtain ⟨_, _, _, hR⟩ := pairwise_split hpw
  unfold lookupEntries
  rw [List.append_assoc, find_append_right_of_not]
  intro q hq
  simp only [decide_eq_false_iff_not]
  intro heq
  subst heq
  simp at hq
  rcases hq with ⟨rfl, _⟩ | hq
  · omega
  · have := hR q hq; omega

theorem lookupEntries_split_eq {ak : Bytes.Address} {vk dflt : SourceValue F}
    {ls rs : List (Bytes.Address × SourceValue F)}
    (hpw : (ls ++ [(ak, vk)] ++ rs).Pairwise (fun p q => addrRank p.1 < addrRank q.1)) :
    lookupEntries ak (ls ++ [(ak, vk)] ++ rs) dflt = vk := by
  obtain ⟨_, _, hL, _⟩ := pairwise_split hpw
  unfold lookupEntries
  rw [List.append_assoc, find_append_left_of_not]
  · simp [List.find?]
  · intro p hp
    simp only [decide_eq_false_iff_not]
    intro heq
    have := hL p hp
    rw [heq] at this
    omega

theorem lookupEntries_split_gt {a ak : Bytes.Address} {vk dflt : SourceValue F}
    {ls rs : List (Bytes.Address × SourceValue F)}
    (hpw : (ls ++ [(ak, vk)] ++ rs).Pairwise (fun p q => addrRank p.1 < addrRank q.1))
    (hgt : addrRank ak < addrRank a) :
    lookupEntries a (ls ++ [(ak, vk)] ++ rs) dflt = lookupEntries a rs dflt := by
  obtain ⟨_, _, hL, _⟩ := pairwise_split hpw
  unfold lookupEntries
  rw [find_append_left_of_not]
  intro p hp
  simp only [decide_eq_false_iff_not]
  intro heq
  subst heq
  simp at hp
  rcases hp with hp | ⟨rfl, _⟩
  · have := hL p hp; omega
  · omega

theorem lookupEntries_eq_of_mem {a : Bytes.Address} {v dflt : SourceValue F}
    {es : List (Bytes.Address × SourceValue F)}
    (hpw : es.Pairwise (fun p q => addrRank p.1 < addrRank q.1))
    (hmem : (a, v) ∈ es) : lookupEntries a es dflt = v := by
  obtain ⟨ls, rs, rfl⟩ := List.append_of_mem hmem
  have hpw' : (ls ++ [(a, v)] ++ rs).Pairwise (fun p q => addrRank p.1 < addrRank q.1) := by
    simpa [List.append_assoc] using hpw
  simpa [List.append_assoc] using lookupEntries_split_eq (dflt := dflt) hpw'

theorem lookupEntries_eq_dflt_of_not_mem {a : Bytes.Address} {dflt : SourceValue F}
    {es : List (Bytes.Address × SourceValue F)}
    (hno : ∀ v, (a, v) ∉ es) : lookupEntries a es dflt = dflt := by
  unfold lookupEntries
  have hf : es.find? (fun p => decide (p.1 = a)) = none := by
    rw [← List.nil_append es, find_append_right_of_not]
    · rfl
    · intro p hp
      simp only [decide_eq_false_iff_not]
      intro heq
      subst heq
      exact hno p.2 hp
  rw [hf]

theorem insSorted_split_lt_aux {a ak : Bytes.Address} {v vk : SourceValue F}
    {ls rs : List (Bytes.Address × SourceValue F)}
    (hlt : addrRank a < addrRank ak) :
    insSorted a v (ls ++ [(ak, vk)] ++ rs) = insSorted a v ls ++ [(ak, vk)] ++ rs := by
  induction ls with
  | nil =>
    simp only [List.nil_append, List.singleton_append, insSorted, ite_eq_left hlt]
  | cons kw ls ih =>
    rcases kw with ⟨k, w⟩
    simp only [List.cons_append, insSorted]
    by_cases h1 : addrRank a < addrRank k
    · simp [h1]
    · rw [ite_eq_right h1, ite_eq_right h1]
      by_cases h2 : a = k
      · simp [h2]
      · simp [h2, ih]

theorem insSorted_split_eq_aux {ak : Bytes.Address} {v vk : SourceValue F}
    {ls rs : List (Bytes.Address × SourceValue F)}
    (hL : ∀ p ∈ ls, addrRank p.1 < addrRank ak) :
    insSorted ak v (ls ++ [(ak, vk)] ++ rs) = ls ++ [(ak, v)] ++ rs := by
  induction ls with
  | nil =>
    simp [insSorted]
  | cons kw ls ih =>
    rcases kw with ⟨k, w⟩
    have hklt : addrRank k < addrRank ak := hL (k, w) (by simp)
    have nlt : ¬ addrRank ak < addrRank k := by omega
    have neq : ak ≠ k := by intro e; subst e; omega
    simp only [List.cons_append, insSorted, ite_eq_right nlt, ite_eq_right neq]
    rw [ih (fun p hp => hL p (by simp [hp]))]

theorem insSorted_append_prefix {a : Bytes.Address} {v : SourceValue F}
    {xs ys : List (Bytes.Address × SourceValue F)}
    (hxs : ∀ p ∈ xs, addrRank p.1 < addrRank a) :
    insSorted a v (xs ++ ys) = xs ++ insSorted a v ys := by
  induction xs with
  | nil => rfl
  | cons kw xs ih =>
    rcases kw with ⟨k, w⟩
    have hklt : addrRank k < addrRank a := hxs (k, w) (by simp)
    have nlt : ¬ addrRank a < addrRank k := by omega
    have neq : a ≠ k := by intro e; subst e; omega
    simp only [List.cons_append, insSorted, ite_eq_right nlt, ite_eq_right neq]
    rw [ih (fun p hp => hxs p (by simp [hp]))]

theorem insSorted_split_gt_aux {a ak : Bytes.Address} {v vk : SourceValue F}
    {ls rs : List (Bytes.Address × SourceValue F)}
    (hL : ∀ p ∈ ls, addrRank p.1 < addrRank ak)
    (hgt : addrRank ak < addrRank a) :
    insSorted a v (ls ++ [(ak, vk)] ++ rs) = ls ++ [(ak, vk)] ++ insSorted a v rs := by
  refine insSorted_append_prefix ?_
  intro p hp
  simp at hp
  rcases hp with hp | ⟨rfl, _⟩
  · exact Nat.lt_trans (hL p hp) hgt
  · exact hgt

/-! ## Branch-decoding helpers for `canon_addr_cmp` in `lookup_or_default` and `ins` -/

private theorem cmp_branch_lt {x_key x_k v_cmp : SourceValue F} {h m1 m2 : Heap F}
    {cs1 cs2 : List (Call F)} {a ak : Bytes.Address}
    (hk : Bytes.RepAddressRef addrTy h a x_key)
    (hk_node : Bytes.RepAddressRef addrTy h ak x_k)
    (ev_cmp : ObsFn W "RBTreeMap::canon_addr_cmp" [x_key, x_k] h v_cmp m1 cs1)
    (ev_z : ObsFn W "Fields::is_zero" [v_cmp] m1 (.field 1) m2 cs2) :
    m2 = h ∧ addrRank a < addrRank ak := by
  obtain ⟨rfl, rfl⟩ := canon_addr_cmp_spec hk hk_node ev_cmp
  obtain ⟨hz, rfl⟩ := Lib.is_zero_field ev_z
  have hc0 : (cmpNat (addrRank a) (addrRank ak) : F) = 0 := by
    by_cases he : (cmpNat (addrRank a) (addrRank ak) : F) = 0
    · exact he
    · rw [ite_eq_right he] at hz
      exact absurd (Value.field.inj hz) one_ne_zero
  have hc_eq : cmpNat (addrRank a) (addrRank ak) = 0 :=
    natCast_inj_of_lt_u32 (cmpNat_lt_u32 _ _) (by decide) hc0
  exact ⟨rfl, cmpNat_eq_zero_iff.mp hc_eq⟩

private theorem cmp_branch_eq {x_key x_k v_cmp v_lt x_cmp2 : SourceValue F}
    {h m1 m2 m3 : Heap F} {cs1 cs2 cs3 : List (Call F)} {a ak : Bytes.Address}
    (hk : Bytes.RepAddressRef addrTy h a x_key)
    (hk_node : Bytes.RepAddressRef addrTy h ak x_k)
    (ev_cmp1 : ObsFn W "RBTreeMap::canon_addr_cmp" [x_key, x_k] h v_cmp m1 cs1)
    (ev_z : ObsFn W "Fields::is_zero" [v_cmp] m1 v_lt m2 cs2)
    (ev_cmp2 : ObsFn W "RBTreeMap::canon_addr_cmp" [x_key, x_k] m2 x_cmp2 m3 cs3)
    (op_sub : evalBinOp .sub x_cmp2 (.field 1) = .ok (.field 0)) :
    m3 = h ∧ a = ak := by
  obtain ⟨rfl, rfl⟩ := canon_addr_cmp_spec hk hk_node ev_cmp1
  obtain ⟨_, rfl⟩ := Lib.is_zero_field ev_z
  obtain ⟨rfl, rfl⟩ := canon_addr_cmp_spec hk hk_node ev_cmp2
  simp only [evalBinOp, Except.ok.injEq, Value.field.injEq] at op_sub
  have hc1 : (cmpNat (addrRank a) (addrRank ak) : F) = (1 : F) := by
    simpa using sub_eq_zero.mp op_sub
  have hc_eq : cmpNat (addrRank a) (addrRank ak) = 1 :=
    natCast_inj_of_lt_u32 (cmpNat_lt_u32 _ _) (by decide) hc1
  exact ⟨rfl, addrRank_injective (cmpNat_eq_one_iff.mp hc_eq)⟩

private theorem cmp_branch_gt {x_key x_k v_cmp v_lt x_cmp2 v_sub : SourceValue F}
    {h m1 m2 m3 : Heap F} {cs1 cs2 cs3 : List (Call F)} {a ak : Bytes.Address}
    (hk : Bytes.RepAddressRef addrTy h a x_key)
    (hk_node : Bytes.RepAddressRef addrTy h ak x_k)
    (ev_cmp1 : ObsFn W "RBTreeMap::canon_addr_cmp" [x_key, x_k] h v_cmp m1 cs1)
    (ev_z : ObsFn W "Fields::is_zero" [v_cmp] m1 v_lt m2 cs2)
    (hne_lt : v_lt ≠ .field 1)
    (ev_cmp2 : ObsFn W "RBTreeMap::canon_addr_cmp" [x_key, x_k] m2 x_cmp2 m3 cs3)
    (op_sub : evalBinOp .sub x_cmp2 (.field 1) = .ok v_sub)
    (hne_eq : v_sub ≠ .field 0) :
    m3 = h ∧ addrRank ak < addrRank a := by
  obtain ⟨rfl, rfl⟩ := canon_addr_cmp_spec hk hk_node ev_cmp1
  obtain ⟨hz, rfl⟩ := Lib.is_zero_field ev_z
  obtain ⟨rfl, rfl⟩ := canon_addr_cmp_spec hk hk_node ev_cmp2
  have nc0 : cmpNat (addrRank a) (addrRank ak) ≠ 0 := by
    intro e
    rw [e] at hz
    simp at hz
    exact hne_lt hz
  have nc1 : cmpNat (addrRank a) (addrRank ak) ≠ 1 := by
    intro e
    rw [e] at op_sub
    simp [evalBinOp] at op_sub
    exact hne_eq op_sub.symm
  rcases cmpNat_values (addrRank a) (addrRank ak) with h0 | h1 | h2
  · exact absurd h0 nc0
  · exact absurd h1 nc1
  · exact ⟨rfl, cmpNat_eq_two_iff.mp h2⟩

/-! ## Specifications of `rbtree_map_balance_fix`, `rbtree_map_balance`, `rbtree_map_ins`,
`rbtree_map_insert`, and `rbtree_map_lookup_or_default` -/

theorem rbtree_map_balance_fix_entries {t_V : Generic.Ty}
    {x_key x_value x_left x_right r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    {a : Bytes.Address} {ls rs : List (Bytes.Address × SourceValue F)}
    (hk : Bytes.RepAddressRef addrTy h a x_key)
    (hl : RBTreeEntries t_V h ls x_left)
    (hr : RBTreeEntries t_V h rs x_right)
    (ev : ObsFn W (Instance.mk "RBTreeMap::rbtree_map_balance_fix" [t_V]).symbol
      [x_key, x_value, x_left, x_right] h r h' calls) :
    Heap.Extends h h' ∧ RBTreeEntries t_V h' (ls ++ [(a, x_value)] ++ rs) r := by
  have ext : Heap.Extends h h' := ObsFn.heap_extends ev
  rcases Obs.«RBTreeMap::rbtree_map_balance_fix».obs ev with
    ⟨x_yk, x_yv, w40, x_c, x_xk, x_xv, x_a, x_b, m134, m186, m231,
      hv37, ld63, rfl, hm142, hm194, hm239, rfl, -⟩ |
    ⟨x_xk, x_xv, x_a, w255, x_yk, x_yv, x_b, x_c, m349, m401, m446,
      hv252, ld283, rfl, hm357, hm409, hm454, rfl, -⟩ |
    ⟨x_zk, x_zv, w474, x_d, x_yk, x_yv, x_b, x_c, m564, m602, m620,
      hv471, ld497, rfl, hm572, hm610, hm628, rfl, -⟩ |
    ⟨x_yk, x_yv, x_b, w689, x_zk, x_zv, x_c, x_d, m779, m817, m835,
      hv686, ld717, rfl, hm787, hm825, hm843, rfl, -⟩ |
    ⟨m921, m932, rfl, hm929, hm940, rfl, -⟩
  · -- Arm 1: `(Node(0, yk, yv, &Node(0, xk, xv, a, b), c), d)`
    subst hv37 hm142 hm239 hm194
    obtain ⟨_, ay, lv_w, rv_c, l_w, lc, _, rfl, hyk, hl_w, hl_c, rl_w, rl_c⟩ := hl.node_inv
    obtain rfl := loadValue_eq_inj ld63 hl_w
    obtain ⟨_, ax, lv_a, rv_b, la, lb, _, rfl, hxk, hl_a, hl_b, rl_a, rl_b⟩ := rl_w.node_inv
    set nL := Value.construct (rbtreeEnum t_V) "Node" [.field 1, x_xk, x_xv, x_a, x_b]
    set m1 := h ++ [nL]
    set m2 := m1 ++ [x_right]
    set nR := Value.construct (rbtreeEnum t_V) "Node"
      [.field 1, x_key, x_value, x_c, .ptr x_right.type m1.length]
    set m3 := m2 ++ [nR]
    have e12 : Heap.Extends m1 m2 := Heap.Extends.snoc _ _
    have e23 : Heap.Extends m2 m3 := Heap.Extends.snoc _ _
    have e13 : Heap.Extends m1 m3 := e12.trans e23
    have ldL : loadValue m3 (.ptr (.enum (rbtreeEnum t_V)) h.length) = .ok nL :=
      e13.loadValue_eq (loadValue_snoc_self h nL)
    have ld_d : loadValue m3 (.ptr x_right.type m1.length) = .ok x_right :=
      e23.loadValue_eq (loadValue_snoc_self m1 x_right)
    have ldR : loadValue m3 (.ptr (.enum (rbtreeEnum t_V)) m2.length) = .ok nR :=
      loadValue_snoc_self m2 nR
    have tL : RBTreeEntries t_V m3 (la ++ [(ax, x_xv)] ++ lb) nL :=
      .node (Bytes.repAddressRef_heapMono₂ addrTy ext hxk)
        (ext.loadValue_eq hl_a) (ext.loadValue_eq hl_b) (rl_a.mono ext) (rl_b.mono ext)
    have tR : RBTreeEntries t_V m3 (lc ++ [(a, x_value)] ++ rs) nR :=
      .node (Bytes.repAddressRef_heapMono₂ addrTy ext hk)
        (ext.loadValue_eq hl_c) ld_d (rl_c.mono ext) (hr.mono ext)
    have tRoot := RBTreeEntries.node (Bytes.repAddressRef_heapMono₂ addrTy ext hyk) ldL ldR tL tR
    exact ⟨ext, by simpa only [List.append_assoc] using tRoot⟩
  · -- Arm 2: `(Node(0, xk, xv, a, &Node(0, yk, yv, b, c)), d)`
    subst hv252 hm357 hm454 hm409
    obtain ⟨_, ax, lv_a, rv_w, la, l_w, _, rfl, hxk, hl_a, hl_w, rl_a, rl_w⟩ := hl.node_inv
    obtain rfl := loadValue_eq_inj ld283 hl_w
    obtain ⟨_, ay, lv_b, rv_c, lb, lc, _, rfl, hyk, hl_b, hl_c, rl_b, rl_c⟩ := rl_w.node_inv
    set nL := Value.construct (rbtreeEnum t_V) "Node" [.field 1, x_xk, x_xv, x_a, x_b]
    set m1 := h ++ [nL]
    set m2 := m1 ++ [x_right]
    set nR := Value.construct (rbtreeEnum t_V) "Node"
      [.field 1, x_key, x_value, x_c, .ptr x_right.type m1.length]
    set m3 := m2 ++ [nR]
    have e12 : Heap.Extends m1 m2 := Heap.Extends.snoc _ _
    have e23 : Heap.Extends m2 m3 := Heap.Extends.snoc _ _
    have e13 : Heap.Extends m1 m3 := e12.trans e23
    have ldL : loadValue m3 (.ptr (.enum (rbtreeEnum t_V)) h.length) = .ok nL :=
      e13.loadValue_eq (loadValue_snoc_self h nL)
    have ld_d : loadValue m3 (.ptr x_right.type m1.length) = .ok x_right :=
      e23.loadValue_eq (loadValue_snoc_self m1 x_right)
    have ldR : loadValue m3 (.ptr (.enum (rbtreeEnum t_V)) m2.length) = .ok nR :=
      loadValue_snoc_self m2 nR
    have tL : RBTreeEntries t_V m3 (la ++ [(ax, x_xv)] ++ lb) nL :=
      .node (Bytes.repAddressRef_heapMono₂ addrTy ext hxk)
        (ext.loadValue_eq hl_a) (ext.loadValue_eq hl_b) (rl_a.mono ext) (rl_b.mono ext)
    have tR : RBTreeEntries t_V m3 (lc ++ [(a, x_value)] ++ rs) nR :=
      .node (Bytes.repAddressRef_heapMono₂ addrTy ext hk)
        (ext.loadValue_eq hl_c) ld_d (rl_c.mono ext) (hr.mono ext)
    have tRoot := RBTreeEntries.node (Bytes.repAddressRef_heapMono₂ addrTy ext hyk) ldL ldR tL tR
    exact ⟨ext, by simpa only [List.append_assoc] using tRoot⟩
  · -- Arm 3: `(a, Node(0, zk, zv, &Node(0, yk, yv, b, c), d))`
    subst hv471 hm610 hm572 hm628
    obtain ⟨_, az, lv_w, rv_d, l_w, ld, _, rfl, hzk, hl_w, hl_d, rl_w, rl_d⟩ := hr.node_inv
    obtain rfl := loadValue_eq_inj ld497 hl_w
    obtain ⟨_, ay, lv_b, rv_c, lb, lc, _, rfl, hyk, hl_b, hl_c, rl_b, rl_c⟩ := rl_w.node_inv
    set m1 := h ++ [x_left]
    set nL := Value.construct (rbtreeEnum t_V) "Node"
      [.field 1, x_key, x_value, .ptr x_left.type h.length, x_b]
    set m2 := m1 ++ [nL]
    set nR := Value.construct (rbtreeEnum t_V) "Node" [.field 1, x_zk, x_zv, x_c, x_d]
    set m3 := m2 ++ [nR]
    have e12 : Heap.Extends m1 m2 := Heap.Extends.snoc _ _
    have e23 : Heap.Extends m2 m3 := Heap.Extends.snoc _ _
    have e13 : Heap.Extends m1 m3 := e12.trans e23
    have ld_a : loadValue m3 (.ptr x_left.type h.length) = .ok x_left :=
      e13.loadValue_eq (loadValue_snoc_self h x_left)
    have ldL : loadValue m3 (.ptr (.enum (rbtreeEnum t_V)) m1.length) = .ok nL :=
      e23.loadValue_eq (loadValue_snoc_self m1 nL)
    have ldR : loadValue m3 (.ptr (.enum (rbtreeEnum t_V)) m2.length) = .ok nR :=
      loadValue_snoc_self m2 nR
    have tL : RBTreeEntries t_V m3 (ls ++ [(a, x_value)] ++ lb) nL :=
      .node (Bytes.repAddressRef_heapMono₂ addrTy ext hk)
        ld_a (ext.loadValue_eq hl_b) (hl.mono ext) (rl_b.mono ext)
    have tR : RBTreeEntries t_V m3 (lc ++ [(az, x_zv)] ++ ld) nR :=
      .node (Bytes.repAddressRef_heapMono₂ addrTy ext hzk)
        (ext.loadValue_eq hl_c) (ext.loadValue_eq hl_d) (rl_c.mono ext) (rl_d.mono ext)
    have tRoot := RBTreeEntries.node (Bytes.repAddressRef_heapMono₂ addrTy ext hyk) ldL ldR tL tR
    exact ⟨ext, by simpa only [List.append_assoc] using tRoot⟩
  · -- Arm 4: `(a, Node(0, yk, yv, b, &Node(0, zk, zv, c, d)))`
    subst hv686 hm825 hm787 hm843
    obtain ⟨_, ay, lv_b, rv_w, lb, l_w, _, rfl, hyk, hl_b, hl_w, rl_b, rl_w⟩ := hr.node_inv
    obtain rfl := loadValue_eq_inj ld717 hl_w
    obtain ⟨_, az, lv_c, rv_d, lc, ld, _, rfl, hzk, hl_c, hl_d, rl_c, rl_d⟩ := rl_w.node_inv
    set m1 := h ++ [x_left]
    set nL := Value.construct (rbtreeEnum t_V) "Node"
      [.field 1, x_key, x_value, .ptr x_left.type h.length, x_b]
    set m2 := m1 ++ [nL]
    set nR := Value.construct (rbtreeEnum t_V) "Node" [.field 1, x_zk, x_zv, x_c, x_d]
    set m3 := m2 ++ [nR]
    have e12 : Heap.Extends m1 m2 := Heap.Extends.snoc _ _
    have e23 : Heap.Extends m2 m3 := Heap.Extends.snoc _ _
    have e13 : Heap.Extends m1 m3 := e12.trans e23
    have ld_a : loadValue m3 (.ptr x_left.type h.length) = .ok x_left :=
      e13.loadValue_eq (loadValue_snoc_self h x_left)
    have ldL : loadValue m3 (.ptr (.enum (rbtreeEnum t_V)) m1.length) = .ok nL :=
      e23.loadValue_eq (loadValue_snoc_self m1 nL)
    have ldR : loadValue m3 (.ptr (.enum (rbtreeEnum t_V)) m2.length) = .ok nR :=
      loadValue_snoc_self m2 nR
    have tL : RBTreeEntries t_V m3 (ls ++ [(a, x_value)] ++ lb) nL :=
      .node (Bytes.repAddressRef_heapMono₂ addrTy ext hk)
        ld_a (ext.loadValue_eq hl_b) (hl.mono ext) (rl_b.mono ext)
    have tR : RBTreeEntries t_V m3 (lc ++ [(az, x_zv)] ++ ld) nR :=
      .node (Bytes.repAddressRef_heapMono₂ addrTy ext hzk)
        (ext.loadValue_eq hl_c) (ext.loadValue_eq hl_d) (rl_c.mono ext) (rl_d.mono ext)
    have tRoot := RBTreeEntries.node (Bytes.repAddressRef_heapMono₂ addrTy ext hyk) ldL ldR tL tR
    exact ⟨ext, by simpa only [List.append_assoc] using tRoot⟩
  · -- Arm 5 (`other`): `Node(1, key, value, &left, &right)`
    subst hm929 hm940
    set m1 := h ++ [x_left]
    set m2 := m1 ++ [x_right]
    have e12 : Heap.Extends m1 m2 := Heap.Extends.snoc _ _
    have ldL : loadValue m2 (.ptr x_left.type h.length) = .ok x_left :=
      e12.loadValue_eq (loadValue_snoc_self h x_left)
    have ldR : loadValue m2 (.ptr x_right.type m1.length) = .ok x_right :=
      loadValue_snoc_self m1 x_right
    exact ⟨ext, .node (Bytes.repAddressRef_heapMono₂ addrTy ext hk)
      ldL ldR (hl.mono ext) (hr.mono ext)⟩

theorem rbtree_map_balance_entries {t_V : Generic.Ty} {c : F}
    {x_key x_value x_left x_right r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    {a : Bytes.Address} {ls rs : List (Bytes.Address × SourceValue F)}
    (hk : Bytes.RepAddressRef addrTy h a x_key)
    (hl : RBTreeEntries t_V h ls x_left)
    (hr : RBTreeEntries t_V h rs x_right)
    (ev : ObsFn W (Instance.mk "RBTreeMap::rbtree_map_balance" [t_V]).symbol
      [.field c, x_key, x_value, x_left, x_right] h r h' calls) :
    Heap.Extends h h' ∧ RBTreeEntries t_V h' (ls ++ [(a, x_value)] ++ rs) r := by
  rcases Obs.«RBTreeMap::rbtree_map_balance».obs ev with
    ⟨cs18, _, ev20, -⟩ | ⟨m89, m100, _, rfl, hm97, hm108, rfl, -⟩
  · exact rbtree_map_balance_fix_entries hk hl hr ev20
  · subst hm97 hm108
    have ext : Heap.Extends h ((h ++ [x_left]) ++ [x_right]) :=
      (Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _)
    have e12 : Heap.Extends (h ++ [x_left]) ((h ++ [x_left]) ++ [x_right]) :=
      Heap.Extends.snoc _ _
    have ldL : loadValue ((h ++ [x_left]) ++ [x_right]) (.ptr x_left.type h.length) = .ok x_left :=
      e12.loadValue_eq (loadValue_snoc_self h x_left)
    have ldR : loadValue ((h ++ [x_left]) ++ [x_right])
        (.ptr x_right.type (h ++ [x_left]).length) = .ok x_right :=
      loadValue_snoc_self (h ++ [x_left]) x_right
    exact ⟨ext, .node (Bytes.repAddressRef_heapMono₂ addrTy ext hk)
      ldL ldR (hl.mono ext) (hr.mono ext)⟩

/-- **`RBTreeMap::rbtree_map_lookup_or_default`**: returns `lookupEntries a es x_default`
without allocating. -/
theorem rbtree_map_lookup_or_default_spec {t_V : Generic.Ty}
    {es : List (Bytes.Address × SourceValue F)} :
    ∀ {x_key x_tree x_default r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
      {a : Bytes.Address},
      Bytes.RepAddressRef addrTy h a x_key →
      RBTreeBST t_V h es x_tree →
      ObsFn W (Instance.mk "RBTreeMap::rbtree_map_lookup_or_default" [t_V]).symbol
        [x_key, x_tree, x_default] h r h' calls →
      r = lookupEntries a es x_default ∧ h' = h := by
  intro x_key x_tree x_default r h h' calls a hk ⟨htree, hpw⟩ ev
  induction htree generalizing r h' calls with
  | nil =>
    rcases Obs.«RBTreeMap::rbtree_map_lookup_or_default».obs ev with
      ⟨_, rfl, rfl, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hv26, _, _, _, _, _, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv26, _, _, _, _, _, _, _, _, _, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv26, _, _, _, _, _, _, _, _, _, -⟩
    · exact ⟨rfl, rfl⟩
    · injection hv26 with _ hc _; cases hc
    · injection hv26 with _ hc _; cases hc
    · injection hv26 with _ hc _; cases hc
  | node hk_node hl hr rl rr ihl ihr =>
    obtain ⟨hpwL, hpwR, _, _⟩ := pairwise_split hpw
    rcases Obs.«RBTreeMap::rbtree_map_lookup_or_default».obs ev with
      ⟨hv15, _, _, -⟩ |
      ⟨w28, x_k, x_v, w29, w30, y51, y59, m63, cs73, v76, m78, cs86, cs122,
        _, hv26, ld52, ld60, ev88, ev75, ev124, -⟩ |
      ⟨w28, x_k, x_v, w29, w30, y51, y59, v62, m63, cs73, v76, m78, cs86, x162, m164, cs173,
        _, hv26, ld52, ld60, ev88, ev75, hne150, ev175, op169, rfl, rfl, -⟩ |
      ⟨w28, x_k, x_v, w29, w30, y51, y59, v62, m63, cs73, v76, m78, cs86, v154, x162, m164,
        cs173, cs217, _, hv26, ld52, ld60, ev88, ev75, hne150, ev175, op169, hne210, ev219, -⟩
    · injection hv15 with _ hc _; cases hc
    · injection hv26 with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
      obtain rfl := loadValue_eq_inj ld52 hl
      obtain ⟨rfl, hlt⟩ := cmp_branch_lt hk hk_node ev88 ev75
      rw [lookupEntries_split_lt hpw hlt]
      exact ihl hk hpwL ev124
    · injection hv26 with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
      obtain ⟨rfl, rfl⟩ := cmp_branch_eq hk hk_node ev88 ev75 ev175 op169
      exact ⟨(lookupEntries_split_eq hpw).symm, rfl⟩
    · injection hv26 with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
      obtain rfl := loadValue_eq_inj ld60 hr
      obtain ⟨rfl, hgt⟩ := cmp_branch_gt hk hk_node ev88 ev75 hne150 ev175 op169 hne210
      rw [lookupEntries_split_gt hpw hgt]
      exact ihr hk hpwR ev219

/-- **`RBTreeMap::rbtree_map_ins`**: inserts/overwrites `(a, x_value)` in `es` while preserving
the structural entries invariant. -/
theorem rbtree_map_ins_entries {t_V : Generic.Ty}
    {es : List (Bytes.Address × SourceValue F)} :
    ∀ {x_key x_value x_tree r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
      {a : Bytes.Address},
      Bytes.RepAddressRef addrTy h a x_key →
      RBTreeBST t_V h es x_tree →
      ObsFn W (Instance.mk "RBTreeMap::rbtree_map_ins" [t_V]).symbol
        [x_key, x_value, x_tree] h r h' calls →
      Heap.Extends h h' ∧ RBTreeEntries t_V h' (insSorted a x_value es) r := by
  intro x_key x_value x_tree r h h' calls a hk ⟨htree, hpw⟩ ev
  induction htree generalizing r h' calls with
  | nil =>
    rcases Obs.«RBTreeMap::rbtree_map_ins».obs ev with
      ⟨m47, m60, _, rfl, hm55, hm68, rfl, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv79, _, _, _, _, _, _, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv79, _, _, _, _, _, _, _, _, _, _, _, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv79, _, _, _, _, _, _, _, _, _, _, -⟩
    · subst hm55 hm68
      set nilVal := Value.construct (rbtreeEnum t_V) "Nil" []
      set m1 := h ++ [nilVal]
      set m2 := m1 ++ [nilVal]
      have e12 : Heap.Extends m1 m2 := Heap.Extends.snoc _ _
      have ext : Heap.Extends h m2 := (Heap.Extends.snoc _ _).trans e12
      have ldL : loadValue m2 (.ptr (.enum (rbtreeEnum t_V)) h.length) = .ok nilVal :=
        e12.loadValue_eq (loadValue_snoc_self h nilVal)
      have ldR : loadValue m2 (.ptr (.enum (rbtreeEnum t_V)) m1.length) = .ok nilVal :=
        loadValue_snoc_self m1 nilVal
      have tRoot := RBTreeEntries.node (Bytes.repAddressRef_heapMono₂ addrTy ext hk)
        ldL ldR .nil .nil
      exact ⟨ext, tRoot⟩
    · injection hv79 with _ hc _; cases hc
    · injection hv79 with _ hc _; cases hc
    · injection hv79 with _ hc _; cases hc
  | node hk_node hl hr rl rr ihl ihr =>
    obtain ⟨hpwL, hpwR, hL, _⟩ := pairwise_split hpw
    rcases Obs.«RBTreeMap::rbtree_map_ins».obs ev with
      ⟨_, _, hv15, _, _, _, _, -⟩ |
      ⟨x_color, x_k, x_v, w81, w82, y103, y111, m115, cs125, v128, m130, cs138, cs174,
        v180, m204, cs212, _, hv79, ld104, ld112, ev140, ev127, ev214, ev176, -⟩ |
      ⟨x_color, x_k, x_v, w81, w82, y103, y111, v114, m115, cs125, v128, m130, cs138,
        x259, m261, cs270, m334, m345,
        _, hv79, ld104, ld112, ev140, ev127, hne247, ev272, op266, rfl, hm342, hm353, rfl, -⟩ |
      ⟨x_color, x_k, x_v, w81, w82, y103, y111, v114, m115, cs125, v128, m130, cs138,
        v251, x259, m261, cs270, cs364, v371, m401, cs409,
        _, hv79, ld104, ld112, ev140, ev127, hne247, ev272, op266, hne357, ev411, ev366, -⟩
    · injection hv15 with _ hc _; cases hc
    · -- `<`: insert left, then balance
      injection hv79 with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
      obtain rfl := loadValue_eq_inj ld104 hl
      obtain rfl := loadValue_eq_inj ld112 hr
      obtain ⟨rfl, hlt⟩ := cmp_branch_lt hk hk_node ev140 ev127
      obtain ⟨ext1, rl'⟩ := ihl hk hpwL ev214
      obtain ⟨ext2, rbal⟩ := rbtree_map_balance_entries
        (Bytes.repAddressRef_heapMono₂ addrTy ext1 hk_node) rl' (rr.mono ext1) ev176
      rw [insSorted_split_lt_aux hlt]
      exact ⟨ext1.trans ext2, rbal⟩
    · -- `=`: overwrite root
      injection hv79 with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
      obtain rfl := loadValue_eq_inj ld104 hl
      obtain rfl := loadValue_eq_inj ld112 hr
      obtain ⟨rfl, rfl⟩ := cmp_branch_eq hk hk_node ev140 ev127 ev272 op266
      subst hm342 hm353
      set m1 := h ++ [y103]
      set m2 := m1 ++ [y111]
      have e12 : Heap.Extends m1 m2 := Heap.Extends.snoc _ _
      have ext : Heap.Extends h m2 := (Heap.Extends.snoc _ _).trans e12
      have ldL : loadValue m2 (.ptr y103.type h.length) = .ok y103 :=
        e12.loadValue_eq (loadValue_snoc_self h y103)
      have ldR : loadValue m2 (.ptr y111.type m1.length) = .ok y111 :=
        loadValue_snoc_self m1 y111
      rw [insSorted_split_eq_aux hL]
      exact ⟨ext, .node (Bytes.repAddressRef_heapMono₂ addrTy ext hk)
        ldL ldR (rl.mono ext) (rr.mono ext)⟩
    · -- `>`: insert right, then balance
      injection hv79 with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
      obtain rfl := loadValue_eq_inj ld104 hl
      obtain rfl := loadValue_eq_inj ld112 hr
      obtain ⟨rfl, hgt⟩ := cmp_branch_gt hk hk_node ev140 ev127 hne247 ev272 op266 hne357
      obtain ⟨ext1, rr'⟩ := ihr hk hpwR ev411
      obtain ⟨ext2, rbal⟩ := rbtree_map_balance_entries
        (Bytes.repAddressRef_heapMono₂ addrTy ext1 hk_node) (rl.mono ext1) rr' ev366
      rw [insSorted_split_gt_aux hL hgt]
      exact ⟨ext1.trans ext2, rbal⟩

/-- **`RBTreeMap::rbtree_map_insert`**: inserts/overwrites `(a, x_value)` in a `RBTreeBST`,
preserving the `RBTreeBST` invariant. -/
theorem rbtree_map_insert_spec {t_V : Generic.Ty}
    {es : List (Bytes.Address × SourceValue F)}
    {x_key x_value x_tree r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    {a : Bytes.Address}
    (hk : Bytes.RepAddressRef addrTy h a x_key)
    (hbst : RBTreeBST t_V h es x_tree)
    (ev : ObsFn W (Instance.mk "RBTreeMap::rbtree_map_insert" [t_V]).symbol
      [x_key, x_value, x_tree] h r h' calls) :
    Heap.Extends h h' ∧ RBTreeBST t_V h' (insSorted a x_value es) r := by
  obtain ⟨m2, cs12, w55, x_k, x_v, x_left, x_right, ev14, rfl, rfl, -⟩ :=
    Obs.«RBTreeMap::rbtree_map_insert».obs ev
  obtain ⟨ext, hent⟩ := rbtree_map_ins_entries hk hbst ev14
  obtain ⟨_, ak, lv, rv, ls, rs, _, heq, hk_root, hl, hr, rl, rr⟩ := hent.node_inv
  refine ⟨ext, ⟨?_, insSorted_pairwise hbst.2⟩⟩
  rw [heq]
  exact .node hk_root hl hr rl rr

/-! ## High-level address-set interface (`RBTreeMap<Field>` with `1` / `0`) -/

/-- `tree` (`RBTreeMap<Field>`) represents the finite set of addresses in `S`: every present
key maps to `.field 1`, and a key is present iff its `ixAddr` lies in `S`. -/
def RepAddrSet (h : Heap F) (S : List _root_.Address) (tree : SourceValue F) : Prop :=
  ∃ es, RBTreeBST .field h es tree ∧
    (∀ p ∈ es, p.2 = .field 1) ∧
    (∀ b : Bytes.Address, (∃ v, (b, v) ∈ es) ↔ ixAddr b ∈ S)

theorem RepAddrSet.nil (h : Heap F) :
    RepAddrSet h [] (.construct addrMapEnum "Nil" []) := by
  refine ⟨[], ?_, by simp, by simp⟩
  rw [← rbtreeEnum_field]
  exact RBTreeBST.nil .field h

theorem RepAddrSet.mono {h₁ h₂ : Heap F} {S : List _root_.Address} {tree : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (hs : RepAddrSet h₁ S tree) : RepAddrSet h₂ S tree := by
  obtain ⟨es, hbst, hval, hmem⟩ := hs
  exact ⟨es, hbst.mono ext, hval, hmem⟩

theorem rbtree_set_insert_spec {S : List _root_.Address}
    {x_key x_tree r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    {a : Bytes.Address}
    (hk : Bytes.RepAddressRef addrTy h a x_key)
    (hs : RepAddrSet h S x_tree)
    (ev : ObsFn W (Instance.mk "RBTreeMap::rbtree_map_insert" [.field]).symbol
      [x_key, .field 1, x_tree] h r h' calls) :
    Heap.Extends h h' ∧ RepAddrSet h' (ixAddr a :: S) r := by
  obtain ⟨es, hbst, hval, hmem⟩ := hs
  obtain ⟨ext, hbst'⟩ := rbtree_map_insert_spec hk hbst ev
  refine ⟨ext, ⟨insSorted a (.field 1) es, hbst', ?_, ?_⟩⟩
  · intro p hp
    rcases mem_insSorted hp with rfl | hp'
    · rfl
    · exact hval p hp'
  · intro b
    rw [mem_fst_insSorted_iff, hmem b, List.mem_cons]
    constructor
    · rintro (rfl | hb)
      · exact .inl rfl
      · exact .inr hb
    · rintro (heq | hb)
      · exact .inl (ixAddr_injective heq)
      · exact .inr hb

theorem rbtree_set_lookup_spec {S : List _root_.Address}
    {x_key x_tree r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    {a : Bytes.Address}
    (hk : Bytes.RepAddressRef addrTy h a x_key)
    (hs : RepAddrSet h S x_tree)
    (ev : ObsFn W (Instance.mk "RBTreeMap::rbtree_map_lookup_or_default" [.field]).symbol
      [x_key, x_tree, .field 0] h r h' calls) :
    r = .field (if ixAddr a ∈ S then 1 else 0) ∧ h' = h := by
  obtain ⟨es, hbst, hval, hmem⟩ := hs
  obtain ⟨rfl, rfl⟩ := rbtree_map_lookup_or_default_spec hk hbst ev
  by_cases hin : ixAddr a ∈ S
  · rw [ite_eq_left hin]
    obtain ⟨v, hv⟩ := (hmem a).mpr hin
    have hv1 : v = .field 1 := hval (a, v) hv
    subst hv1
    exact ⟨lookupEntries_eq_of_mem hbst.2 hv, rfl⟩
  · rw [ite_eq_right hin]
    have hno : ∀ v, (a, v) ∉ es := fun v hv => hin ((hmem a).mp ⟨v, hv⟩)
    exact ⟨lookupEntries_eq_dflt_of_not_mem hno, rfl⟩

end IxVM.Refinement.Claim
