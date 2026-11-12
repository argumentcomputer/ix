import IxVMRefinement.Core.Registry
import IxVMRefinement.Core.Roles
import IxVMRefinement.Lib.Words
import IxVMRefinement.Lib.WordSub
import IxVMRefinement.Lib.WordOps
import IxVMRefinement.Lib.Lists
import IxVMRefinement.Obs.KernelKlimbs
import IxVMRefinement.Obs.IxVMCompat
import IxVMRefinement.Obs.KernelLevels

/-! # Limbs, words and fields: the toolkit of the `Nat` natives

A `Nat` literal is a little-endian list of 64-bit limbs (`KernelTypes::KLimbs`), each limb a
word of eight bytes (`RepU64`), read as its value (`limbsVal`). This file gathers what the step
lemmas of the limb functions share:

* **Fields.** IxVM's carries, borrows and counters are field elements; the values read here are
  far below the field's size, so the field arithmetic is the natural one (`val_natCast`,
  `natCast_inj`, `natCast_eq_zero_iff`).
* **Words.** A word holding the natural `m` (below `2^64`) is `TagN.u64Value m`
  (`repU64_of`); the constant words the circuit writes (`[1, 0, …]`, `[2, 0, …]`, …) are
  `u64Value` of small naturals (`u64Value_lt256`).
* **Limb lists.** The value of a cons, canonical lists (no trailing zero limb: `Canon`), and the
  uniqueness of a canonical list of a given value (`canon_inj`), so a canonical list is empty
  exactly at `0` (`eq_nil_of_canon`).
* **Heaps.** Limb lists stay represented in later heaps (`lrep_mono`), and a stored `Cons` cell
  of a represented limb and list represents the longer list (`lrep_store_cons`). -/

namespace IxVM.Refinement.Core.NatAux

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List

set_option linter.unusedVariables false

/-- The field's size, as a literal (`omega` reads literals, not definitions). -/
scoped notation "PF" => (18446744069414584321 : Nat)

/-- `2^64`, the base of the limbs, as a literal. -/
scoped notation "B64" => (18446744073709551616 : Nat)

/-- A callee's derivation has fewer calls than its caller's. -/
macro "nat_lt_calls" : tactic =>
  `(tactic| (simp only [List.length_cons, List.length_append]; omega))

/-- Arithmetic on limb values, with the value of the empty list known. -/
macro "lv_omega" : tactic => `(tactic| (have := IxVM.Refinement.Core.NatAux.limbsVal_nil; omega))

/-! ## Fields -/

theorem val_natCast {n : Nat} (hn : n < PF) : ZMod.val (n : F) = n := ZMod.val_natCast_of_lt hn

theorem natCast_val (x : F) : ((ZMod.val x : Nat) : F) = x := ZMod.natCast_zmod_val x

theorem natCast_inj {a b : Nat} (ha : a < PF) (hb : b < PF) : (a : F) = (b : F) ↔ a = b := by
  constructor
  · intro h
    have := congrArg ZMod.val h
    rwa [val_natCast ha, val_natCast hb] at this
  · intro h; rw [h]

theorem natCast_eq_zero_iff {n : Nat} (hn : n < PF) : (n : F) = 0 ↔ n = 0 := by
  have := natCast_inj (a := n) (b := 0) hn (by decide)
  simpa using this

theorem field_inj {a b : F} (h : (Value.field a : SourceValue F) = .field b) : a = b :=
  Value.field.inj h

theorem field_one_ne_zero : (Value.field (1 : F) : SourceValue F) ≠ .field 0 := by
  intro h
  have := field_inj h
  exact one_ne_zero this

theorem val_one : ZMod.val (1 : F) = 1 := by
  have := val_natCast (n := 1) (by decide)
  simpa using this

theorem val_zero : ZMod.val (0 : F) = 0 := ZMod.val_zero

/-- `x + 1` read as a natural, below the field's size. -/
theorem val_add_one {x : F} (h : ZMod.val x + 1 < PF) : ZMod.val (x + 1) = ZMod.val x + 1 := by
  rw [ZMod.val_add_of_lt (by rw [val_one]; exact h), val_one]

theorem val_sub_one {x : F} (h : x ≠ 0) : ZMod.val (x - 1) = ZMod.val x - 1 := by
  have := Lib.val_sub_one h
  omega

theorem val_sub {x y : F} (h : ZMod.val y ≤ ZMod.val x) : ZMod.val (x - y) = ZMod.val x - ZMod.val y :=
  ZMod.val_sub h

/-- A bit field element given as a value. -/
theorem bit_cases {k : F} (hk : ZMod.val k ≤ 1) : (k = 0 ∧ ZMod.val k = 0) ∨ (k = 1 ∧ ZMod.val k = 1) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with h0 | h1
  · exact .inl ⟨(ZMod.val_eq_zero k).mp h0, h0⟩
  · refine .inr ⟨?_, h1⟩
    rw [← natCast_val k, h1, Nat.cast_one]

theorem field_eq_zero_val {k : F} (hv : (Value.field k : SourceValue F) = .field 0) :
    ZMod.val k = 0 := by
  rw [field_inj hv]; exact val_zero

theorem field_ne_zero_val {k : F} (hv : (Value.field k : SourceValue F) ≠ .field 0) :
    ZMod.val k ≠ 0 := by
  intro h0
  exact hv (by rw [(ZMod.val_eq_zero k).mp h0])

/-- **An `if` on a bit, as a natural**: `1` exactly when the condition holds. -/
theorem ite_bit (p : Prop) [Decidable p] :
    ∃ b : Nat, (if p then (1 : F) else 0) = (b : F) ∧ ((p ∧ b = 1) ∨ (¬ p ∧ b = 0)) := by
  by_cases hp : p
  · exact ⟨1, by simp [hp], .inl ⟨hp, rfl⟩⟩
  · exact ⟨0, by simp [hp], .inr ⟨hp, rfl⟩⟩

/-- A field element read back from its natural. -/
theorem field_val (x : F) : (Value.field x : SourceValue F) = .field ((ZMod.val x : Nat) : F) := by
  rw [natCast_val]

theorem binop_fields {op : BinOp} {a b r : SourceValue F} (hop : evalBinOp op a b = .ok r) :
    ∃ x y : F, a = .field x ∧ b = .field y := by
  cases a <;> cases b <;> first | exact ⟨_, _, rfl, rfl⟩ | cases hop

theorem add_ok {a b : F} {r : SourceValue F}
    (hop : evalBinOp .add (.field a : SourceValue F) (.field b) = .ok r) : r = .field (a + b) :=
  (Except.ok.inj hop).symm

theorem sub_ok {a b : F} {r : SourceValue F}
    (hop : evalBinOp .sub (.field a : SourceValue F) (.field b) = .ok r) : r = .field (a - b) :=
  (Except.ok.inj hop).symm

theorem mul_ok {a b : F} {r : SourceValue F}
    (hop : evalBinOp .mul (.field a : SourceValue F) (.field b) = .ok r) : r = .field (a * b) :=
  (Except.ok.inj hop).symm

/-! ## Words -/

theorem toNat_lt (w : UInt64) : w.toNat < B64 := w.toNat_lt

/-- **The word holding `m`** (`m` below `2^64`): a word of value `m` represented by
`u64Value m`. -/
theorem word_of (h : Heap F) {m : Nat} (hm : m < B64) :
    ∃ w : UInt64, w.toNat = m ∧ RepU64 h w (TagN.u64Value m) :=
  ⟨UInt64.ofNatLT m hm, by rw [UInt64.toNat_ofNatLT], Lib.repU64_ofNatLT h hm⟩

/-- A word is the byte tuple of its value. -/
theorem repU64_eq {h : Heap F} {w : UInt64} {v : SourceValue F} (hv : RepU64 h w v) :
    v = TagN.u64Value w.toNat :=
  Lib.repU64_eq hv

/-- A small word: its low byte, then seven zero bytes. -/
theorem u64Value_lt256 {n : Nat} (hn : n < 256) :
    TagN.u64Value n = .tuple [.field (n : F), .field 0, .field 0, .field 0, .field 0, .field 0,
      .field 0, .field 0] := by
  have e0 : n % 256 = n := Nat.mod_eq_of_lt hn
  have e1 : n / 256 = 0 := by omega
  have e2 : n / 65536 = 0 := by omega
  have e3 : n / 16777216 = 0 := by omega
  have e4 : n / 4294967296 = 0 := by omega
  have e5 : n / 1099511627776 = 0 := by omega
  have e6 : n / 281474976710656 = 0 := by omega
  have e7 : n / 72057594037927936 = 0 := by omega
  simp only [TagN.u64Value, e0, e1, e2, e3, e4, e5, e6, e7, Nat.zero_mod, Nat.cast_zero]

/-- **A word whose low byte is the field element `k` (of value below `256`) and whose other
bytes are zero holds `k`'s value.** -/
theorem word_lowByte (h : Heap F) {k : F} (hk : ZMod.val k < 256) :
    ∃ w : UInt64, w.toNat = ZMod.val k ∧ RepU64 h w (.tuple [.field k, .field 0, .field 0,
      .field 0, .field 0, .field 0, .field 0, .field 0]) := by
  obtain ⟨w, hw, hr⟩ := word_of h (m := ZMod.val k) (by omega)
  refine ⟨w, hw, ?_⟩
  have e := u64Value_lt256 hk
  rw [natCast_val] at e
  rwa [e] at hr

/-- The word `[0, 0, …]` holds `0`. -/
theorem word_zero (h : Heap F) :
    ∃ w : UInt64, w.toNat = 0 ∧ RepU64 h w (.tuple [.field 0, .field 0, .field 0, .field 0,
      .field 0, .field 0, .field 0, .field 0]) := by
  have := word_lowByte h (k := 0) (by rw [val_zero]; decide)
  rwa [val_zero] at this

/-- The word `[1, 0, …]` holds `1`. -/
theorem word_one (h : Heap F) :
    ∃ w : UInt64, w.toNat = 1 ∧ RepU64 h w (.tuple [.field 1, .field 0, .field 0, .field 0,
      .field 0, .field 0, .field 0, .field 0]) := by
  have := word_lowByte h (k := 1) (by rw [val_one]; decide)
  rwa [val_one] at this

/-- The word `[2, 0, …]` holds `2`. -/
theorem word_two (h : Heap F) :
    ∃ w : UInt64, w.toNat = 2 ∧ RepU64 h w (.tuple [.field 2, .field 0, .field 0, .field 0,
      .field 0, .field 0, .field 0, .field 0]) := by
  have hv : ZMod.val (2 : F) = 2 := by
    have := val_natCast (n := 2) (by decide)
    simpa using this
  have := word_lowByte h (k := 2) (by rw [hv]; decide)
  rwa [hv] at this

/-- **`UInt64::add` on two words**: the sum's low word and the carry, nothing allocated. -/
theorem add_words {x y s cy : SourceValue F} {h h₀ h₁ m : Heap F} {cs : List (Call F)}
    {v w : UInt64} (hx : RepU64 h₀ v x) (hy : RepU64 h₁ w y)
    (ev : ObsFn W "UInt64::add" [x, y] h (.tuple [s, cy]) m cs) :
    s = TagN.u64Value ((v.toNat + w.toNat) % B64) ∧
      cy = .field (((v.toNat + w.toNat) / B64 : Nat) : F) ∧ h = m := by
  obtain ⟨hr, hm⟩ := Lib.u64_add_spec (h := h) hx hy ev
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hr
  exact ⟨hr.1, hr.2, hm.symm⟩

/-- **`UInt64::sub_with_borrow` on two words**: the difference modulo `2^64` and the borrow. -/
theorem sub_words {x y s br : SourceValue F} {h h₀ h₁ m : Heap F} {cs : List (Call F)}
    {v w : UInt64} (hx : RepU64 h₀ v x) (hy : RepU64 h₁ w y)
    (ev : ObsFn W "UInt64::sub_with_borrow" [x, y] h (.tuple [s, br]) m cs) :
    s = TagN.u64Value ((v.toNat + B64 - w.toNat) % B64) ∧
      br = .field (if v.toNat < w.toNat then 1 else 0) ∧ h = m := by
  obtain ⟨hr, hm⟩ := Lib.u64_sub_with_borrow_spec (h := h) hx hy ev
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hr
  exact ⟨hr.1, hr.2, hm.symm⟩

/-- **`UInt64::is_zero`** on a word: `1` exactly at `0`, nothing allocated. -/
theorem is_zero_word {x r : SourceValue F} {h h₀ h' : Heap F} {cs : List (Call F)} {w : UInt64}
    (hx : RepU64 h₀ w x) (ev : ObsFn W "UInt64::is_zero" [x] h r h' cs) :
    r = .field (if w.toNat = 0 then 1 else 0) ∧ h = h' := by
  obtain ⟨h1, h2⟩ := Lib.u64_is_zero_spec (h := h) hx ev
  exact ⟨h1, h2.symm⟩

/-- **`UInt64::and`** on two words. -/
theorem and_words {x y r : SourceValue F} {h h₀ h₁ h' : Heap F} {cs : List (Call F)} {v w : UInt64}
    (hx : RepU64 h₀ v x) (hy : RepU64 h₁ w y) (ev : ObsFn W "UInt64::and" [x, y] h r h' cs) :
    RepU64 h (v &&& w) r ∧ h = h' := by
  obtain ⟨h1, h2⟩ := Lib.u64_and_spec (h := h) hx hy ev
  exact ⟨h1, h2.symm⟩

/-- **`UInt64::or`** on two words. -/
theorem or_words {x y r : SourceValue F} {h h₀ h₁ h' : Heap F} {cs : List (Call F)} {v w : UInt64}
    (hx : RepU64 h₀ v x) (hy : RepU64 h₁ w y) (ev : ObsFn W "UInt64::or" [x, y] h r h' cs) :
    RepU64 h (v ||| w) r ∧ h = h' := by
  obtain ⟨h1, h2⟩ := Lib.u64_or_spec (h := h) hx hy ev
  exact ⟨h1, h2.symm⟩

/-- **`UInt64::xor`** on two words. -/
theorem xor_words {x y r : SourceValue F} {h h₀ h₁ h' : Heap F} {cs : List (Call F)} {v w : UInt64}
    (hx : RepU64 h₀ v x) (hy : RepU64 h₁ w y) (ev : ObsFn W "UInt64::xor" [x, y] h r h' cs) :
    RepU64 h (v ^^^ w) r ∧ h = h' := by
  obtain ⟨h1, h2⟩ := Lib.u64_xor_spec (h := h) hx hy ev
  exact ⟨h1, h2.symm⟩

/-- **`UInt8::to_field`** returns its argument, allocating nothing. -/
theorem to_field {x r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt8::to_field" [x] h r h' cs) : x = r ∧ h = h' := by
  obtain ⟨h1, h2⟩ := Lib.u8_to_field_spec ev
  exact ⟨h1.symm, h2.symm⟩

/-- **`UInt8::from_field`** returns its argument, a byte, allocating nothing. -/
theorem from_field {x r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt8::from_field" [x] h r h' cs) : x = r ∧ h = h' ∧ ∃ b : UInt8, RepU8 h b x := by
  obtain ⟨h1, h2, h3⟩ := Lib.u8_from_field_spec ev
  exact ⟨h1.symm, h2.symm, h3⟩

/-- A carry out of a sum of two words and a bit is `0` or `1`, and `0` exactly when the sum
stays below `2^64`. -/
theorem carry_zero_iff {s : Nat} (hs : s < 2 * B64) : (((s / B64 : Nat) : F) = 0 ↔ s < B64) := by
  rw [natCast_eq_zero_iff (by omega)]
  omega

theorem carry_val {s : Nat} (hs : s < 2 * B64) : ZMod.val ((s / B64 : Nat) : F) = s / B64 :=
  val_natCast (by omega)

/-! ## Limb lists -/

/-- A limb list (`KernelTypes::KLimbs`). -/
abbrev LRep (h : Heap F) (ls : List UInt64) (p : SourceValue F) : Prop :=
  RepList limbListEnum RepU64 h ls p

/-- **A canonical limb list**: no trailing zero limb. -/
def Canon (ls : List UInt64) : Prop := ls.getLast? ≠ some 0

theorem limbsVal_nil : limbsVal [] = 0 := rfl

theorem limbsVal_cons (l : UInt64) (ls : List UInt64) :
    limbsVal (l :: ls) = l.toNat + B64 * limbsVal ls := rfl

theorem canon_nil : Canon [] := by simp [Canon]

theorem canon_cons {l : UInt64} {ls : List UInt64} :
    Canon (l :: ls) ↔ (ls = [] → l ≠ 0) ∧ Canon ls := by
  cases ls with
  | nil => simp [Canon]
  | cons m ms => simp [Canon, List.getLast?_cons_cons]

theorem canon_tail {l : UInt64} {ls : List UInt64} (h : Canon (l :: ls)) : Canon ls :=
  (canon_cons.mp h).2

theorem uint64_eq_zero_iff {l : UInt64} : l = 0 ↔ l.toNat = 0 := by
  rw [← UInt64.toNat_inj]; simp

theorem eq_nil_of_canon {ls : List UInt64} (hc : Canon ls) (h0 : limbsVal ls = 0) : ls = [] := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    exfalso
    rw [limbsVal_cons] at h0
    have hl : l.toNat = 0 := by omega
    have hls : limbsVal ls = 0 := by omega
    have hnil := ih (canon_tail hc) hls
    exact (canon_cons.mp hc).1 hnil (uint64_eq_zero_iff.mpr hl)

/-- **A canonical list is determined by its value.** -/
theorem canon_inj : ∀ {a b : List UInt64}, Canon a → Canon b → limbsVal a = limbsVal b → a = b
  | [], b, _, hb, h => (eq_nil_of_canon hb h.symm).symm
  | x :: xs, [], ha, _, h => eq_nil_of_canon ha h
  | x :: xs, y :: ys, ha, hb, h => by
    rw [limbsVal_cons, limbsVal_cons] at h
    have hx := toNat_lt x
    have hy := toNat_lt y
    have h1 : x.toNat = y.toNat := by omega
    have h2 : limbsVal xs = limbsVal ys := by omega
    rw [UInt64.toNat_inj.mp h1, canon_inj (canon_tail ha) (canon_tail hb) h2]

/-- A cons onto a canonical list is canonical when its value is not `0`. -/
theorem canon_cons_of_pos {l : UInt64} {ls : List UInt64} (hc : Canon ls)
    (hpos : 0 < limbsVal (l :: ls)) : Canon (l :: ls) := by
  refine canon_cons.mpr ⟨fun hnil => ?_, hc⟩
  subst hnil
  intro hl
  subst hl
  simp [limbsVal_cons, limbsVal_nil] at hpos

theorem limbsVal_pos_of_ne_nil {ls : List UInt64} (hc : Canon ls) (hne : ls ≠ []) :
    0 < limbsVal ls := by
  rcases Nat.eq_zero_or_pos (limbsVal ls) with h | h
  · exact absurd (eq_nil_of_canon hc h) hne
  · exact h

/-! ## Heaps -/

theorem lrep_mono {h₁ h₂ : Heap F} {ls : List UInt64} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (r : LRep h₁ ls p) : LRep h₂ ls p :=
  repList_heapMono₂ limbListEnum repU64_heapMono₂ ext r

theorem repLimbs_mono {h₁ h₂ : Heap F} {n : Nat} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (r : RepLimbs h₁ n p) : RepLimbs h₂ n p :=
  let ⟨ls, hl, hv⟩ := r; ⟨ls, lrep_mono ext hl, hv⟩

theorem repLimbsC_mono {h₁ h₂ : Heap F} {n : Nat} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (r : Specs.Nat.RepLimbsC h₁ n p) : Specs.Nat.RepLimbsC h₂ n p :=
  let ⟨ls, hl, hv, hc⟩ := r; ⟨ls, lrep_mono ext hl, hv, hc⟩

theorem RepLimbsC.toRepLimbs {h : Heap F} {n : Nat} {p : SourceValue F}
    (r : Specs.Nat.RepLimbsC h n p) : RepLimbs h n p :=
  let ⟨ls, hl, hv, _⟩ := r; ⟨ls, hl, hv⟩

/-- A stored `Cons` cell of a represented limb and list. -/
theorem lrep_store_cons {h h₀ : Heap F} {l : UInt64} {ls : List UInt64} {v p : SourceValue F}
    (hv : RepU64 h₀ l v) (hl : LRep h ls p) :
    LRep (h ++ [.construct limbListEnum "Cons" [v, p]]) (l :: ls) (.ptr (.enum limbListEnum) h.length) :=
  Lib.rep_store_cons (h := h) repU64_heapMono₂ hv hl

/-- A stored `Nil` cell. -/
theorem lrep_store_nil (h : Heap F) :
    LRep (h ++ [.construct limbListEnum "Nil" []]) [] (.ptr (.enum limbListEnum) h.length) :=
  Lib.rep_store_nil h

theorem lrep_nil_of_load {h : Heap F} {ls : List UInt64} {p : SourceValue F}
    (rep : LRep h ls p) (hl : loadValue h p = .ok (.construct limbListEnum "Nil" [])) : ls = [] :=
  Lib.rep_nil_of_load rep hl

theorem lrep_cons_of_load {h : Heap F} {ls : List UInt64} {p x y : SourceValue F}
    (rep : LRep h ls p) (hl : loadValue h p = .ok (.construct limbListEnum "Cons" [x, y])) :
    ∃ z zs, ls = z :: zs ∧ RepU64 h z x ∧ LRep h zs y :=
  Lib.rep_cons_of_load rep hl

/-- **A list whose cell is not `Nil`** (the `_` arm after a `Nil` arm) is a cons. -/
theorem rep_cons_of_not_nil {α : Type} {en : String} {R : Heap F → α → SourceValue F → Prop}
    {h : Heap F} {xs : List α} {p v : SourceValue F}
    (rep : RepList en R h xs p) (hl : loadValue h p = .ok v)
    (hne : ∀ vs : List (SourceValue F), vs.length = 0 → v ≠ .construct en "Nil" vs) :
    xs ≠ [] := by
  intro hnil
  subst hnil
  cases rep with
  | nil cell =>
    rw [Lib.load_enum_cell cell] at hl
    injection hl with hv
    exact hne [] rfl hv.symm

end IxVM.Refinement.Core.NatAux
