import Aiur.HeapMono
import Aiur.Library.List
import Aiur.Library.List.Word
import Aiur.Library.Option
import Aiur.Library.U32.Correctness
import Aiur.Library.U64.Correctness

/-!
# Canonical Source Representation Predicates and `Lists` / `WordLists` / `Options` Correctness

This module establishes:
1. Canonical `SourceValue F` representation predicates `RepU8`, `RepU32`, `RepU64`,
   `RepOption` (`Options::Option<T>`), and `RepList` (`Lists::List<T>`) along with
   their `HeapMono` / `HeapMono₂` proofs.
2. Heap-allocation constructors (`allocNil`, `allocCons`, `allocList`) and their
   heap-extension and representation soundness proofs.
3. Mathematical specifications for `Lists` (`is_empty`, `length`, `concat`,
   `drop`, `take`, `lookup`, `lookup_or_default`, `snoc`, `reverse_acc`, `reverse`)
   and `WordLists` (`checked_depth_succ`, `depth_checked`, `length_u64`,
   `lookup_u64`).
-/

namespace Aiur.Library

open Aiur

variable {F : Type}

/-! ### 1. Word Representation Predicates (`RepU8`, `RepU32`, `RepU64`) and `HeapMono` -/

/-- Canonical `SourceValue F` representation of a checked byte `UInt8::U8`. -/
def RepU8 [NatCast F] (_h : Heap F) (b : UInt8) (v : SourceValue F) : Prop :=
  v = .field (b.toNat : F)

theorem repU8_heapMono₂ [NatCast F] : HeapMono₂ (RepU8 (F := F)) :=
  fun _ _ _ _ _ h => h

theorem repU8_heapMono [NatCast F] (b : UInt8) :
    HeapMono (fun h v => RepU8 (F := F) h b v) :=
  HeapMono.of_heapMono₂ repU8_heapMono₂ b

theorem repU8_inj [Field F] (large : U32.Compatible F) {h : Heap F}
    {a b : UInt8} {v : SourceValue F}
    (ha : RepU8 h a v) (hb : RepU8 h b v) : a = b := by
  rw [RepU8] at ha hb
  have heq : (a.toNat : F) = (b.toNat : F) := Value.field.inj (ha.symm.trans hb)
  have ha_lt : a.toNat < 3 * U32.base := by
    have := a.toNat_lt; unfold U32.base; omega
  have hb_lt : b.toNat < 3 * U32.base := by
    have := b.toNat_lt; unfold U32.base; omega
  exact UInt8.ext (large ha_lt hb_lt heq)

/-- Canonical `SourceValue F` representation of a 4-byte little-endian `UInt32::U32`. -/
def RepU32 [NatCast F] (_h : Heap F) (w : UInt32) (v : SourceValue F) : Prop :=
  v = .tuple ((List.range 4).map fun i => .field (((w.toNat / 256 ^ i) % 256 : Nat) : F))

theorem repU32_heapMono₂ [NatCast F] : HeapMono₂ (RepU32 (F := F)) :=
  fun _ _ _ _ _ h => h

theorem repU32_heapMono [NatCast F] (w : UInt32) :
    HeapMono (fun h v => RepU32 (F := F) h w v) :=
  HeapMono.of_heapMono₂ repU32_heapMono₂ w

/-- Canonical `SourceValue F` representation of an 8-byte little-endian `UInt64::U64`. -/
def RepU64 [NatCast F] (_h : Heap F) (w : UInt64) (v : SourceValue F) : Prop :=
  v = .tuple ((List.range 8).map fun i => .field (((w.toNat / 256 ^ i) % 256 : Nat) : F))

theorem repU64_heapMono₂ [NatCast F] : HeapMono₂ (RepU64 (F := F)) :=
  fun _ _ _ _ _ h => h

theorem repU64_heapMono [NatCast F] (w : UInt64) :
    HeapMono (fun h v => RepU64 (F := F) h w v) :=
  HeapMono.of_heapMono₂ repU64_heapMono₂ w

/-! ### 2. `RepOption` (`Options::Option<T>`) and `HeapMono` -/

/-- Nominal enum symbol for `Options::Option<T>` instantiated at `elemTy`. -/
def optionEnumName (elemTy : Generic.Ty) : String :=
  (Generic.Instance.mk "Options::Option" [elemTy]).symbol

/-- Canonical `SourceValue F` representation of `Options::Option<T>` (`Some(x)` / `None`). -/
inductive RepOption {α : Type*} (enumName : String)
    (R : Heap F → α → SourceValue F → Prop) (h : Heap F) :
    Option α → SourceValue F → Prop where
  | none : RepOption enumName R h none (.construct enumName "None" [])
  | some {x : α} {v : SourceValue F} (hv : R h x v) :
      RepOption enumName R h (some x) (.construct enumName "Some" [v])

theorem RepOption.mono {α : Type*} {enumName : String}
    {R : Heap F → α → SourceValue F → Prop} (hR : HeapMono₂ R)
    {h₁ h₂ : Heap F} {opt : Option α} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepOption enumName R h₁ opt v) :
    RepOption enumName R h₂ opt v := by
  cases rep with
  | none => exact .none
  | some hv => exact .some (hR ext hv)

theorem repOption_heapMono₂ {α : Type*} (enumName : String)
    {R : Heap F → α → SourceValue F → Prop} (hR : HeapMono₂ R) :
    HeapMono₂ (RepOption enumName R) :=
  fun _ _ _ _ ext rep => rep.mono hR ext

theorem repOption_heapMono {α : Type*} (enumName : String)
    {R : Heap F → α → SourceValue F → Prop} (hR : HeapMono₂ R) (opt : Option α) :
    HeapMono (fun h v => RepOption enumName R h opt v) :=
  HeapMono.of_heapMono₂ (repOption_heapMono₂ enumName hR) opt

/-! ### 3. `RepList` (`Lists::List<T>`) and Heap Allocation -/

namespace List

/-- Nominal enum symbol for `Lists::Node<T>` instantiated at `elemTy`. -/
def nodeEnumName (elemTy : Generic.Ty) : String :=
  (Generic.Instance.mk "Lists::Node" [elemTy]).symbol

/-- Canonical `SourceValue F` representation of `Lists::List<T> = &Lists::Node<T>`
stored in `h : Heap F`. -/
abbrev RepList {α : Type*} (enumName : String)
    (R : Heap F → α → SourceValue F → Prop) (h : Heap F)
    (xs : _root_.List α) (ptr : SourceValue F) : Prop :=
  RepLinkedList enumName "Nil" "Cons" R h xs ptr

theorem repList_heapMono₂ {α : Type*} (enumName : String)
    {R : Heap F → α → SourceValue F → Prop} (hR : HeapMono₂ R) :
    HeapMono₂ (RepList enumName R) :=
  fun _ _ _ _ ext rep => rep.mono hR ext

theorem repList_heapMono {α : Type*} (enumName : String)
    {R : Heap F → α → SourceValue F → Prop} (hR : HeapMono₂ R) (xs : _root_.List α) :
    HeapMono (fun h ptr => RepList enumName R h xs ptr) :=
  HeapMono.repLinkedList enumName "Nil" "Cons" hR xs

theorem repList_inj {α : Type*} {enumName : String}
    {R : Heap F → α → SourceValue F → Prop} {h : Heap F}
    (hR : ∀ {x₁ x₂ v}, R h x₁ v → R h x₂ v → x₁ = x₂)
    {xs₁ xs₂ : _root_.List α} {ptr : SourceValue F}
    (h₁ : RepList enumName R h xs₁ ptr)
    (h₂ : RepList enumName R h xs₂ ptr) :
    xs₁ = xs₂ := by
  induction h₁ generalizing xs₂ with
  | nil cell₁ =>
      cases h₂ with
      | nil _ => rfl
      | cons cell₂ _ _ =>
          rw [cell₁] at cell₂
          injection cell₂ with hVal
          injection hVal with _ hCtor _
          exact absurd hCtor (by decide)
  | cons cell₁ headRep₁ _ ih =>
      cases h₂ with
      | nil cell₂ =>
          rw [cell₁] at cell₂
          injection cell₂ with hVal
          injection hVal with _ hCtor _
          exact absurd hCtor.symm (by decide)
      | cons cell₂ headRep₂ tailRep₂ =>
          rw [cell₁] at cell₂
          injection cell₂ with hVal
          injection hVal with _ _ hArgs
          injection hArgs with hHead hTail
          injection hTail with hTailPtr _
          subst hHead hTailPtr
          exact _root_.List.cons_eq_cons.mpr ⟨hR headRep₁ headRep₂, ih tailRep₂⟩

/-- Allocate `&Lists::Node::Nil` at the end of `h : Heap F`. -/
def allocNil (enumName : String) (h : Heap F) : SourceValue F × Heap F :=
  (.ptr (.enum enumName) h.length, h ++ [.construct enumName "Nil" []])

theorem allocNil_extends (enumName : String) (h : Heap F) :
    Heap.Extends h (allocNil enumName h).2 :=
  Heap.Extends.snoc h _

theorem allocNil_rep {α : Type*} (enumName : String)
    (R : Heap F → α → SourceValue F → Prop) (h : Heap F) :
    RepList enumName R (allocNil enumName h).2 [] (allocNil enumName h).1 := by
  exact .nil (by simp [allocNil])

/-- Allocate `&(Lists::Node::Cons(headVal, tailPtr))` at the end of `h : Heap F`. -/
def allocCons (enumName : String) (headVal tailPtr : SourceValue F) (h : Heap F) :
    SourceValue F × Heap F :=
  (.ptr (.enum enumName) h.length, h ++ [.construct enumName "Cons" [headVal, tailPtr]])

theorem allocCons_extends (enumName : String) (headVal tailPtr : SourceValue F) (h : Heap F) :
    Heap.Extends h (allocCons enumName headVal tailPtr h).2 :=
  Heap.Extends.snoc h _

theorem allocCons_rep {α : Type*} (enumName : String)
    {R : Heap F → α → SourceValue F → Prop} (hR : HeapMono₂ R)
    {h : Heap F} {x : α} {xs : _root_.List α} {headVal tailPtr : SourceValue F}
    (hx : R h x headVal) (hxs : RepList enumName R h xs tailPtr) :
    RepList enumName R (allocCons enumName headVal tailPtr h).2 (x :: xs)
      (allocCons enumName headVal tailPtr h).1 := by
  have ext := allocCons_extends enumName headVal tailPtr h
  exact .cons (by simp [allocCons]) (hR ext hx) (hxs.mono hR ext)

/-- Allocate a full linked list of pre-encoded `SourceValue F` elements in `h : Heap F`. -/
def allocValues (enumName : String) (h : Heap F) :
    _root_.List (SourceValue F) → SourceValue F × Heap F
  | [] => allocNil enumName h
  | v :: vs =>
      let (tailPtr, h₁) := allocValues enumName h vs
      allocCons enumName v tailPtr h₁

theorem allocValues_extends (enumName : String) (h : Heap F)
    (vs : _root_.List (SourceValue F)) :
    Heap.Extends h (allocValues enumName h vs).2 := by
  induction vs generalizing h with
  | nil => exact allocNil_extends enumName h
  | cons v vs ih =>
      dsimp only [allocValues]
      exact (ih h).trans (allocCons_extends enumName v (allocValues enumName h vs).1 _)

theorem allocValues_rep {α : Type*} (enumName : String)
    {R : Heap F → α → SourceValue F → Prop} (hR : HeapMono₂ R)
    (h : Heap F) {xs : _root_.List α} {vs : _root_.List (SourceValue F)}
    (hrel : _root_.List.Forall₂ (R h) xs vs) :
    RepList enumName R (allocValues enumName h vs).2 xs (allocValues enumName h vs).1 := by
  induction hrel with
  | nil =>
      exact allocNil_rep enumName R h
  | @cons x v xs vs hx _ ih =>
      dsimp only [allocValues]
      have ext₁ := allocValues_extends enumName h vs
      have hx₁ : R (allocValues enumName h vs).2 x v := hR ext₁ hx
      exact allocCons_rep enumName hR hx₁ ih

/-! ### 4. Specifications of `Lists` Operations -/

/-- `Lists::is_empty` returns `1` on `Nil` and `0` on `Cons`. -/
def isEmpty [Zero F] [One F] (xs : _root_.List α) : F :=
  match xs with
  | [] => 1
  | _ :: _ => 0

theorem is_empty_spec [Field F] (xs : _root_.List α) :
    (isEmpty xs : F) = if xs.isEmpty then 1 else 0 := by
  cases xs <;> rfl

theorem is_empty_one_iff [Field F] (xs : _root_.List α) :
    (isEmpty xs : F) = 1 ↔ xs = [] := by
  cases xs <;> simp [isEmpty]

theorem is_empty_zero_iff [Field F] (xs : _root_.List α) :
    (isEmpty xs : F) = 0 ↔ xs ≠ [] := by
  cases xs <;> simp [isEmpty]

/-- `Lists::reverse_acc(list, acc)` computes `list.reverseAux acc = list.reverse ++ acc`. -/
def reverseAcc (xs acc : _root_.List α) : _root_.List α :=
  match xs with
  | [] => acc
  | x :: rest => reverseAcc rest (x :: acc)

theorem reverse_acc_spec (xs acc : _root_.List α) :
    reverseAcc xs acc = xs.reverse ++ acc := by
  induction xs generalizing acc with
  | nil => simp [reverseAcc]
  | cons x rest ih =>
      simp [reverseAcc, ih, _root_.List.reverse_cons, _root_.List.append_assoc]

theorem reverse_spec (xs : _root_.List α) :
    reverseAcc xs [] = xs.reverse := by
  rw [reverse_acc_spec, _root_.List.append_nil]

theorem snoc_spec (xs : _root_.List α) (v : α) :
    xs ++ [v] = _root_.List.concat xs v := by
  simp

/-! ### 5. Specifications of `WordLists` (`depth_checked`, `length_u64`, `lookup_u64`) -/

namespace Word

/-- `WordLists::checked_depth_succ(depth)` checks `UInt32::less_than_fields(depth, 4294967295) == 1`
and returns `depth + 1`. -/
def checkedDepthSucc (depth : Nat) : Option Nat :=
  if depth < 4294967295 then some (depth + 1) else none

/-- `WordLists::depth_checked(list)` recursively computes the list length while asserting
at each step that the depth is `< 2^32 - 1`, so the resulting length fits in `UInt32`. -/
def depthChecked : _root_.List α → Option Nat
  | [] => some 0
  | _ :: rest => do
      let d ← depthChecked rest
      checkedDepthSucc d

theorem checked_depth_succ_sound [Field F] (large : U32.Compatible F)
    {depth difference : Nat} (hdepth : depth < U32.base) (hdiff : difference < U32.base)
    (hborrow : let borrow := ((difference : F) + (4294967295 : Nat) - (depth : F)) / (U32.base : F)
      borrow * (borrow - 1) = 0)
    (hlt : ((difference : F) + (4294967295 : Nat) - (depth : F)) / (U32.base : F) = 1) :
    depth < 4294967295 ∧ depth + 1 < U32.base ∧
      (depth : F) + 1 = ((depth + 1 : Nat) : F) := by
  have hcmp := U32.compare_fields_sound large (depth : F) ((4294967295 : Nat) : F)
    hdepth (by unfold U32.base; omega) hdiff rfl rfl hborrow
  rw [hlt] at hcmp
  by_cases h : depth < 4294967295
  · refine ⟨h, by unfold U32.base; omega, by push_cast; rfl⟩
  · simp [h] at hcmp

theorem depth_checked_iff (xs : _root_.List α) :
    depthChecked xs = if xs.length < U32.base then some xs.length else none := by
  induction xs with
  | nil =>
      simp [depthChecked, U32.base]
  | cons x rest ih =>
      simp only [depthChecked, ih, _root_.List.length_cons]
      by_cases hrest : rest.length < U32.base
      · simp only [hrest, ↓reduceIte, checkedDepthSucc]
        by_cases hlt : rest.length < 4294967295
        · have hsucc : rest.length + 1 < U32.base := by unfold U32.base; omega
          simp [hlt, hsucc]
        · have hnsucc : ¬(rest.length + 1 < U32.base) := by unfold U32.base at *; omega
          simp [hlt, hnsucc]
      · have hnsucc : ¬(rest.length + 1 < U32.base) := by unfold U32.base at *; omega
        simp [hrest, hnsucc]

theorem depth_checked_some_iff (xs : _root_.List α) (n : Nat) :
    depthChecked xs = some n ↔ n = xs.length ∧ xs.length < U32.base := by
  rw [depth_checked_iff]
  by_cases h : xs.length < U32.base
  · simp [h, eq_comm]
  · simp [h]

/-- `WordLists::length_u64(list)` computes the 64-bit length by starting at `0 : UInt64`
on `Nil` and applying `UInt64::wrapping_succ` on each `Cons`. -/
def lengthU64 : _root_.List α → UInt64
  | [] => 0
  | _ :: rest => lengthU64 rest + 1

theorem length_u64_spec (xs : _root_.List α) :
    lengthU64 xs = UInt64.ofNat xs.length := by
  induction xs with
  | nil => rfl
  | cons _ rest ih =>
      simp only [lengthU64, ih, _root_.List.length_cons, UInt64.ofNat_add]
      rfl

theorem length_u64_toNat_of_lt {xs : _root_.List α} (hlt : xs.length < U64.base) :
    (lengthU64 xs).toNat = xs.length := by
  rw [length_u64_spec, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt hlt

theorem length_u64_of_depth_checked {xs : _root_.List α} {n : Nat}
    (hchecked : depthChecked xs = some n) :
    (lengthU64 xs).toNat = xs.length ∧ n = xs.length := by
  obtain ⟨rfl, hlt32⟩ := (depth_checked_some_iff xs n).mp hchecked
  have hlt64 : xs.length < U64.base := by
    unfold U32.base U64.base at *; omega
  exact ⟨length_u64_toNat_of_lt hlt64, rfl⟩

/-- `WordLists::lookup_u64(list, idx)` dereferences `Cons(v, rest)` and returns `v`
when `UInt64::is_zero(idx) == 1`, or recurses with `UInt64::saturating_pred(idx)`
when `UInt64::is_zero(idx) == 0`. -/
def lookupU64 : _root_.List α → UInt64 → Option α
  | [], _ => none
  | v :: rest, idx =>
      if idx.toNat = 0 then
        some v
      else
        lookupU64 rest (UInt64.ofNat (idx.toNat - 1))

theorem lookup_u64_spec (xs : _root_.List α) (idx : UInt64) :
    lookupU64 xs idx = xs[idx.toNat]? := by
  induction xs generalizing idx with
  | nil =>
      simp [lookupU64]
  | cons v rest ih =>
      simp only [lookupU64]
      rcases eq_or_ne idx.toNat 0 with h0 | hne
      · simp [h0]
      · obtain ⟨k, hk⟩ : ∃ k, idx.toNat = k + 1 := ⟨idx.toNat - 1, by omega⟩
        have hlt := idx.toNat_lt
        have hmod : k % 18446744073709551616 = k := by omega
        simp [ih, hk, hmod]

theorem lookup_u64_rep {α : Type*} (enumName : String)
    (R : Heap F → α → SourceValue F → Prop)
    {h : Heap F} {xs : _root_.List α} {ptr : SourceValue F}
    (rep : RepList enumName R h xs ptr) (idx : UInt64) {x : α}
    (hlookup : lookupU64 xs idx = some x) :
    ∃ v : SourceValue F, R h x v := by
  rw [lookup_u64_spec] at hlookup
  revert idx
  induction rep with
  | nil =>
      intro idx hlookup
      simp at hlookup
  | @cons head tail addr headVal tailPtr _ headRep _ ih =>
      intro idx hlookup
      rcases eq_or_ne idx.toNat 0 with h0 | hne
      · rw [h0] at hlookup
        simp only [_root_.List.getElem?_cons_zero, Option.some.injEq] at hlookup
        subst hlookup
        exact ⟨headVal, headRep⟩
      · obtain ⟨k, hk⟩ : ∃ k, idx.toNat = k + 1 := ⟨idx.toNat - 1, by omega⟩
        rw [hk, _root_.List.getElem?_cons_succ] at hlookup
        have hlt := idx.toNat_lt
        have hk_eq : (UInt64.ofNat k).toNat = k := by
          rw [UInt64.toNat_ofNat']; omega
        exact ih (UInt64.ofNat k) (by simpa [hk_eq] using hlookup)

end Word
end List
end Aiur.Library
