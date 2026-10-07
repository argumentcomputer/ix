/-! # Fixture: changed constants (M5, W+)

Declarations whose compiled form under Pass 3 (the default) is *changed*: blocks
Pass 1 reorders, splits, collapses or whose nested auxiliary evaporates (their
recursors become images, their `casesOn`/`recOn`/`below`/`brecOn` image-kind
definitions, their users' values inline the images), and definition cliques
in a non-canonical order (transported). Shapes copied from the compiler's
image fixtures (`Tests/Ix/Compile/Image/C1Perm`, `C2Split`, `C4Evap`,
`C5Collapse`), the clique twins (`Tests/Ix/Compile/Twins/Cliques.lean`, `WD`,
`SA`) and M3's minimal reordered Prop block (`plans/review2/M3-certifier.md`
§4.2). Each clique is given in both member orders: one of them is the
canonical one, the other is transported. Every block has a theorem over it. -/

namespace Tests.Ix.CompileCert.ChangedDefs

/-! ## A reordered block (Type): Lean's order `Even`, `Odd`; Ix's canonical order `Odd`, `Even` -/
namespace Reord
mutual
inductive Even
  | zero : Even
  | s : Odd → Even
inductive Odd
  | s : Even → Odd
end

mutual
def Odd.toNat : Odd → Nat
  | .s e => e.toNat + 1
def Even.toNat : Even → Nat
  | .zero => 0
  | .s o => o.toNat + 1
end

theorem three : Odd.toNat (.s (.s (.s .zero))) = 3 := rfl

def Even.isZero : Even → Bool
  | .zero => true
  | .s _ => false

noncomputable def Even.viaRec : Even → Nat :=
  @Even.rec (fun _ => Nat) (fun _ => Nat) 0 (fun _ ih => ih + 1) (fun _ ih => ih + 1)

theorem viaRec_zero : Even.viaRec .zero = 0 := rfl
end Reord

/-! ## A reordered block (Prop, indexed) -/
namespace ReordProp
mutual
inductive Even : Nat → Prop
  | zero : Even 0
  | succ : Odd n → Even (n + 1)
inductive Odd : Nat → Prop
  | succ : Even n → Odd (n + 1)
end

theorem even_two : Even 2 := .succ (.succ .zero)

theorem even_true {n : Nat} (h : Even n) : True :=
  @Even.rec (fun _ _ => True) (fun _ _ => True) trivial (fun _ _ => trivial) (fun _ _ => trivial) n h
end ReordProp

/-! ## A split block: `B` does not mention `A` -/
namespace Split
mutual
inductive A
  | nil : A
  | a : B → A → A
inductive B
  | nil : B
end

def A.len : A → Nat
  | .nil => 0
  | .a _ x => x.len + 1

theorem len2 : A.len (.a .nil (.a .nil .nil)) = 2 := rfl

noncomputable def A.viaRec : A → Nat :=
  @A.rec (fun _ => Nat) (fun _ => Nat) 0 (fun _ _ ihb iha => ihb + iha + 1) 7

theorem viaRec_nil : A.viaRec .nil = 0 := rfl
end Split

/-! ## A collapsed block: `A ≅ B` -/
namespace Collapse
mutual
inductive A
  | nil : A
  | a : B → A
inductive B
  | nil : B
  | b : A → B
end

noncomputable def f : A → Nat :=
  @A.rec (fun _ => Nat) (fun _ => Nat) 0 (fun _ ih => ih + 1) 100 (fun _ ih => ih * 2)

theorem f_ab : f (.a .nil) = 101 := rfl

def A.isNil : A → Bool
  | .nil => true
  | .a _ => false
end Collapse

/-! ## A nested auxiliary that evaporates (`List B` once `B` is split off) -/
namespace Evap
mutual
inductive A
  | mk : List B → A
inductive B
  | leaf : B
end

noncomputable def useRec : A → Nat :=
  @A.rec (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ ih => ih + 1) 5 0 (fun _ _ ihb ihl => ihb + ihl)

theorem useRec_ex : useRec (.mk [.leaf, .leaf]) = 11 := rfl

def A.isMk : A → Bool
  | .mk _ => true
end Evap

/-! ## A well-founded clique, both member orders, with Lean's `eq_def`s -/
namespace WF0
mutual
def wa (n : Nat) : Nat := if h : n ≤ 1 then n else wb (n - 2) + 1
def wb (n : Nat) : Nat := if h : n = 0 then 0 else wa (n - 1) + 2
end
theorem wa_unfold (n : Nat) : wa n = if _h : n ≤ 1 then n else wb (n - 2) + 1 := wa.eq_def n
theorem wb_unfold (n : Nat) : wb n = if _h : n = 0 then 0 else wa (n - 1) + 2 := wb.eq_def n
theorem wa_zero : wa 0 = 0 := by rw [wa.eq_def]; simp
end WF0

namespace WF1
mutual
def wb (n : Nat) : Nat := if h : n = 0 then 0 else wa (n - 1) + 2
def wa (n : Nat) : Nat := if h : n ≤ 1 then n else wb (n - 2) + 1
end
theorem wa_unfold (n : Nat) : wa n = if _h : n ≤ 1 then n else wb (n - 2) + 1 := wa.eq_def n
theorem wb_unfold (n : Nat) : wb n = if _h : n = 0 then 0 else wa (n - 1) + 2 := wb.eq_def n
theorem wa_zero : wa 0 = 0 := by rw [wa.eq_def]; simp
end WF1

/-! ## A structural clique, both member orders. The canonical order (`SC0`)
uses Lean's `eq_def`s; the transported order (`SC1`) does not: compiled with
them, its `eq_def`s are rejected by the certified checker (compiler defect
D-M5-1, `plans/review2/M5-W-changed.md`), so without them its members are the
expected Unsupported class `changed definition: transported clique member
without eq_def` -/
namespace SC0
mutual
def ev : Nat → Bool
  | 0 => true
  | n + 1 => od n
def od : Nat → Bool
  | 0 => false
  | n + 1 => ev n
end
theorem ev4 : ev 4 = true := rfl
/-- Uses (hence realizes) Lean's unfolding lemmas. -/
theorem unfold_used (n : Nat) : ev n = ev n ∧ od n = od n :=
  ⟨(ev.eq_def n).trans (ev.eq_def n).symm, (od.eq_def n).trans (od.eq_def n).symm⟩
end SC0

namespace SC1
mutual
def od : Nat → Bool
  | 0 => false
  | n + 1 => ev n
def ev : Nat → Bool
  | 0 => true
  | n + 1 => od n
end
theorem ev4 : ev 4 = true := rfl
end SC1

end Tests.Ix.CompileCert.ChangedDefs
