import Ix.CompileCert.Canon.Basic
import Ix.Compile.ExactKey

/-! # Names and addresses: lawful orders

`Ix.Name`'s `==` compares the stored hashes and `compare` (`Ix.nameCompare`)
is the byte order of the hashes; both are lawful on the hashes
(`name_beq_iff`, `nameCompare_eq_iff`, `Std.TransCmp Ix.nameCompare`). The
class context `MutCtx` is a tree map under `nameCompareExact` (the hash order,
ties broken structurally by `Ix.Name.cmpRaw`), a lawful total order whose
`eq` is equality (`Std.TransCmp nameCompareExact`,
`Std.LawfulEqCmp nameCompareExact`), and `Ix.Compile.ExactKey.nameEq` is
equality (`nameEq_true`, `nameEq_false`). -/

namespace Ix.CompileCert.Canon

open Ix (Name)

/-! ## Addresses -/

theorem addr_beq_iff {a b : Address} : (a == b) = true ↔ a = b := by
  obtain ⟨⟨x⟩⟩ := a
  obtain ⟨⟨y⟩⟩ := b
  show (ByteArray.beq ⟨x⟩ ⟨y⟩) = true ↔ _
  simp [ByteArray.beq]

theorem addr_data_inj {a b : Address} (h : a.hash.data.toList = b.hash.data.toList) : a = b := by
  obtain ⟨⟨x⟩⟩ := a
  obtain ⟨⟨y⟩⟩ := b
  simp only at h
  have : x = y := Array.toList_inj.1 h
  subst this; rfl

/-- Comparison of two `Ord` keys read through a function. -/
theorem transCmp_comap {α : Type u} {β : Type v} (cmp : β → β → Ordering) [Std.TransCmp cmp]
    (f : α → β) : Std.TransCmp (fun a b => cmp (f a) (f b)) where
  eq_swap := Std.OrientedCmp.eq_swap (cmp := cmp)
  isLE_trans h1 h2 := Std.TransCmp.isLE_trans (cmp := cmp) h1 h2

instance transCmp_address : Std.TransCmp (compare : Address → Address → Ordering) :=
  transCmp_comap (cmp := @compare (List UInt8) (@List.instOrd UInt8 UInt8.instOrd))
    (fun a : Address => a.hash.data.toList)

theorem address_compare_eq_iff {a b : Address} : compare a b = .eq ↔ a = b := by
  constructor
  · intro h
    have : @compare (List UInt8) (@List.instOrd UInt8 UInt8.instOrd)
        a.hash.data.toList b.hash.data.toList = .eq := h
    exact addr_data_inj (Std.LawfulEqCmp.eq_of_compare this)
  · rintro rfl; exact Std.ReflCmp.compare_self (cmp := (compare : Address → Address → Ordering))

/-! ## Names under `==` and `nameCompare` (the stored hash) -/

theorem name_beq_iff {a b : Name} : (a == b) = true ↔ a.getHash = b.getHash :=
  addr_beq_iff

theorem name_beq_refl (a : Name) : (a == a) = true := name_beq_iff.2 rfl

theorem name_beq_symm {a b : Name} (h : (a == b) = true) : (b == a) = true :=
  name_beq_iff.2 (name_beq_iff.1 h).symm

theorem name_beq_trans {a b c : Name} (h1 : (a == b) = true) (h2 : (b == c) = true) :
    (a == c) = true :=
  name_beq_iff.2 ((name_beq_iff.1 h1).trans (name_beq_iff.1 h2))

theorem name_beq_comm (a b : Name) : (a == b) = (b == a) := by
  cases h : (a == b) <;> cases h' : (b == a) <;> first
    | rfl
    | (exfalso; simp_all [name_beq_symm h])
    | (have := name_beq_symm h'; simp_all)

theorem name_beq_of_eq {a b : Name} (h : a = b) : (a == b) = true := h ▸ name_beq_refl a

instance transCmp_nameCompare : Std.TransCmp Ix.nameCompare :=
  transCmp_comap (cmp := (compare : Address → Address → Ordering)) Name.getHash

theorem nameCompare_eq_iff {a b : Name} : Ix.nameCompare a b = .eq ↔ (a == b) = true := by
  rw [name_beq_iff]; exact address_compare_eq_iff

/-! ## `nameCompareExact`: a lawful total order whose `eq` is equality -/

def nameSize : Name → Nat
  | .anonymous _ => 1
  | .str p _ _ | .num p _ _ => nameSize p + 1

def nameTag : Name → Nat
  | .anonymous _ => 0
  | .str .. => 1
  | .num .. => 2

def nameParent : Name → Name
  | .str p _ _ | .num p _ _ => p
  | n => n

def nameStr : Name → String
  | .str _ s _ => s
  | _ => ""

def nameNum : Name → Nat
  | .num _ i _ => i
  | _ => 0

theorem cmpHash_eq (h h' : Address) : Name.cmpHash h h' = compare h h' := by
  unfold Name.cmpHash
  split
  · rename_i e; rw [addr_beq_iff.1 e]; exact (address_compare_eq_iff.2 rfl).symm
  · rfl

theorem cmpRaw_str (p p' : Name) (s s' : String) (h h' : Address) :
    Name.cmpRaw (.str p s h) (.str p' s' h') =
      (Name.cmpRaw p p').then ((compare s s').then (compare h h')) := by
  rw [Name.cmpRaw, cmpHash_eq]
  cases Name.cmpRaw p p' <;> simp only [Ordering.then]
  by_cases e : s = s'
  · subst e; simp
  · have ne : compare s s' ≠ .eq := fun c => e (Std.LawfulEqCmp.eq_of_compare c)
    simp only [beq_iff_eq, e, ↓reduceIte]

theorem cmpRaw_num (p p' : Name) (i i' : Nat) (h h' : Address) :
    Name.cmpRaw (.num p i h) (.num p' i' h') =
      (Name.cmpRaw p p').then ((compare i i').then (compare h h')) := by
  rw [Name.cmpRaw, cmpHash_eq]
  cases Name.cmpRaw p p' <;> simp only [Ordering.then]
  by_cases e : i = i'
  · subst e; simp
  · have ne : compare i i' ≠ .eq := fun c => e (Nat.compare_eq_eq.1 c)
    simp only [beq_iff_eq, e, ↓reduceIte]

/-- `Ix.Name.cmpRaw` as a strong comparison. -/
def rawC (a b : Name) : Except Unit SOrder := pure ⟨true, Name.cmpRaw a b⟩

theorem rawC_total : TotalPre rawC := by
  refine PreOn.ofSize nameSize fun n ih => ?_
  refine PreOn.ofTag nameTag ?_ ?_
  · intro a b _ _ h
    cases a <;> cases b <;> simp_all [rawC, nameTag, Name.cmpRaw, pure, Except.pure] <;> rfl
  intro T
  have hP : ∀ a, nameSize a < n + 1 ∧ nameTag a = T → T = 1 ∨ T = 2 →
      nameSize (nameParent a) < n := by
    intro a ⟨hs, ht⟩ hT
    cases a <;> simp_all [nameSize, nameTag, nameParent]
    omega
  match T with
  | 0 =>
    refine (PreOn.pureCmp (compare : Address → Address → Ordering) Name.getHash).congr ?_
    intro a b ⟨_, ha⟩ ⟨_, hb⟩
    cases a <;> cases b <;> simp_all [rawC, nameTag, Name.cmpRaw, Name.getHash, cmpHash_eq]
  | 1 =>
    refine ((ih.comap nameParent fun a h => hP a h (by omega)).cmpM
      ((PreOn.pureCmp (compare : String → String → Ordering) nameStr).cmpM
        (PreOn.pureCmp (compare : Address → Address → Ordering) Name.getHash))).congr ?_
    intro a b ⟨_, ha⟩ ⟨_, hb⟩
    cases a <;> cases b <;> simp only [nameTag] at ha hb <;> try omega
    simp only [rawC, nameParent, nameStr, Name.getHash, cmpM_pure, cmpRaw_str]
  | 2 =>
    refine ((ih.comap nameParent fun a h => hP a h (by omega)).cmpM
      ((PreOn.pureCmp (compare : Nat → Nat → Ordering) nameNum).cmpM
        (PreOn.pureCmp (compare : Address → Address → Ordering) Name.getHash))).congr ?_
    intro a b ⟨_, ha⟩ ⟨_, hb⟩
    cases a <;> cases b <;> simp only [nameTag] at ha hb <;> try omega
    simp only [rawC, nameParent, nameNum, Name.getHash, cmpM_pure, cmpRaw_num]
  | T + 3 =>
    refine PreOn.empty fun a ⟨_, ha⟩ => ?_
    cases a <;> simp [nameTag] at ha

instance transCmp_cmpRaw : Std.TransCmp Name.cmpRaw := transCmp_of_total _ rawC_total

theorem cmpRaw_eq_iff : ∀ {a b : Name}, Name.cmpRaw a b = .eq ↔ a = b
  | .anonymous h, .anonymous h' => by
    simp only [Name.cmpRaw, cmpHash_eq, address_compare_eq_iff, Name.anonymous.injEq]
  | .str p s h, .str p' s' h' => by
    rw [cmpRaw_str]
    simp only [Ordering.then_eq_eq, cmpRaw_eq_iff, address_compare_eq_iff, Name.str.injEq]
    constructor
    · rintro ⟨rfl, hs, rfl⟩; exact ⟨rfl, Std.LawfulEqCmp.eq_of_compare hs, rfl⟩
    · rintro ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, Std.ReflCmp.compare_self (cmp := (compare : String → String → Ordering)), rfl⟩
  | .num p i h, .num p' i' h' => by
    rw [cmpRaw_num]
    simp only [Ordering.then_eq_eq, cmpRaw_eq_iff, address_compare_eq_iff, Name.num.injEq,
      Nat.compare_eq_eq]
  | .anonymous _, .str .. | .anonymous _, .num .. | .str .., .anonymous _ | .str .., .num ..
  | .num .., .anonymous _ | .num .., .str .. => by simp [Name.cmpRaw]

theorem nameCompareExact_eq (a b : Name) :
    Ix.nameCompareExact a b = (Ix.nameCompare a b).then (Name.cmpRaw a b) := by
  unfold Ix.nameCompareExact
  cases Ix.nameCompare a b <;> rfl

instance transCmp_nameCompareExact : Std.TransCmp Ix.nameCompareExact :=
  transCmp_of_total _ <|
    ((PreOn.pureCmp (ε := Unit) Ix.nameCompare id).cmpM (rawC_total.comap id fun _ _ => trivial)).congr
      fun a b _ _ => by simp only [id, rawC, cmpM_pure, nameCompareExact_eq]

theorem nameCompareExact_eq_iff {a b : Name} : Ix.nameCompareExact a b = .eq ↔ a = b := by
  rw [nameCompareExact_eq, Ordering.then_eq_eq, cmpRaw_eq_iff]
  constructor
  · exact fun h => h.2
  · rintro rfl; exact ⟨nameCompare_eq_iff.2 (name_beq_refl a), rfl⟩

instance lawfulEqCmp_nameCompareExact : Std.LawfulEqCmp Ix.nameCompareExact where
  compare_self := nameCompareExact_eq_iff.2 rfl
  eq_of_compare := nameCompareExact_eq_iff.1

/-! ## Exact name equality -/

theorem nameEq_true {x y : Name} (h : x = y) : Ix.Compile.ExactKey.nameEq x y = true :=
  (Ix.Compile.ExactKey.nameEq_iff x y).2 h

theorem nameEq_false {x y : Name} (h : x ≠ y) : Ix.Compile.ExactKey.nameEq x y = false :=
  Bool.eq_false_iff.2 fun e => h ((Ix.Compile.ExactKey.nameEq_iff x y).1 e)

theorem nameEq_comm (x y : Name) : Ix.Compile.ExactKey.nameEq x y = Ix.Compile.ExactKey.nameEq y x := by
  by_cases h : x = y
  · subst h; rfl
  · rw [nameEq_false h, nameEq_false (Ne.symm h)]

end Ix.CompileCert.Canon
