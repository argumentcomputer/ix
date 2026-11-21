/-!
# Honest inductive declarations for the differential suite of inductive variations

One declaration per dimension of Lean 4's inductive kernel (`inductive.cpp`),
each elaborated and checked by Lean, with theorems that exercise its iota, eta,
projection and K rules. `Tests.Ix.IxVM.IndVariations` runs them, and must-reject
mutations of their records, through Lean's kernel, the certified kernel and
IxVM. Everything is in the namespace `IxIV`.
-/

namespace IxIV

universe u v

/-! ## Plain blocks -/

inductive Color
  | r
  | g
  | b

theorem Color.rec' : @Color.rec (fun _ => Nat) 1 2 3 Color.g = 2 := rfl

structure Pt where
  x : Nat
  y : Bool

theorem Pt.eta' (p : Pt) : p = ⟨p.x, p.y⟩ := rfl
theorem Pt.proj' : (Pt.mk 1 true).x = 1 := rfl

structure U0

theorem U0.uniq (a b : U0) : a = b := rfl

structure PA (a b : Prop) : Prop where
  l : a
  r : b

theorem PA.eta' (a b : Prop) (p : PA a b) : p = ⟨p.l, p.r⟩ := rfl

class Cls (α : Type) where
  op : α → α

theorem Cls.app' : (@Cls.op Nat ⟨Nat.succ⟩) 3 = 4 := rfl

structure Box (α : Type u) where
  val : α

theorem Box.eta' (b : Box Nat) : b = ⟨b.val⟩ := rfl

/-! ## Recursive, reflexive, indexed -/

inductive Tr
  | leaf
  | node (l r : Tr)

theorem Tr.rec' (m : Nat) (f : Tr → Tr → Nat → Nat → Nat) :
    @Tr.rec (fun _ => Nat) m f Tr.leaf = m := rfl

/-- A recursive structure-like inductive (one constructor, no index, recursive):
no structure eta in Lean. -/
inductive RS
  | mk (n : Nat) (s : RS)

inductive W
  | leaf
  | sup (f : Nat → W)

theorem W.rec' (a : Nat) (h : (Nat → W) → (Nat → Nat) → Nat) :
    @W.rec (fun _ => Nat) a h W.leaf = a := rfl

inductive Vec (α : Type) : Nat → Type
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)

/-- A one-constructor indexed family (Lean's `infer_proj` allows `.proj` on it). -/
inductive IV1 : Nat → Type
  | mk (n : Nat) (b : Bool) : IV1 n

/-! ## Propositions -/

inductive Eq' {α : Sort u} (a : α) : α → Prop
  | refl : Eq' a a

/-- K: `h` is a variable, and the recursor still reduces. -/
theorem Eq'.k (h : Eq' (3 : Nat) 3) : @Eq'.rec Nat 3 (fun _ _ => Nat) 5 3 h = 5 := rfl

inductive Acc' {α : Sort u} (r : α → α → Prop) : α → Prop
  | intro (x : α) (h : (y : α) → r y x → Acc' r y) : Acc' r x

inductive Or' (a b : Prop) : Prop
  | inl (h : a) : Or' a b
  | inr (h : b) : Or' a b

inductive Ex' {α : Sort u} (p : α → Prop) : Prop
  | intro (w : α) (h : p w) : Ex' p

inductive F0 : Prop

inductive E0 : Type

/-! ## Sort polymorphism -/

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PU : Sort u
  | unit : PU

inductive PS (α : Sort u) (β : Sort v) : Sort (max 1 u v)
  | inl (a : α) : PS α β
  | inr (b : β) : PS α β

/-! ## Mutual blocks -/

mutual
inductive Ev : Nat → Prop
  | zero : Ev 0
  | succ {n : Nat} (h : Od n) : Ev (n + 1)
inductive Od : Nat → Prop
  | succ {n : Nat} (h : Ev n) : Od (n + 1)
end

mutual
inductive TA
  | a
  | b (x : TB)
inductive TB
  | c (x : TA)
end

theorem TA.rec' :
    @TA.rec (fun _ => Nat) (fun _ => Nat) 7 (fun _ n => n) (fun _ n => n) TA.a = 7 := rfl

/- A non-recursive mutual block: structure eta, unit-like eta and projections
hold in Lean. -/
mutual
structure MA where
  n : Nat
  b : Bool
inductive MB
  | u
end

theorem MA.eta' (p : MA) : p = ⟨p.n, p.b⟩ := rfl
theorem MB.uniq (x y : MB) : x = y := rfl

mutual
/-- A constraint stores a reason that can refer back to another constraint,
as in Lean's cutsat data structures. -/
structure Constraint where
  value : Nat
  reason : Reason
inductive Reason where
  | given
  | derived (c : Constraint)
end

theorem Constraint.value_mk (n : Nat) (r : Reason) : (Constraint.mk n r).value = n := rfl

noncomputable def Constraint.valueRec (c : Constraint) : Nat :=
  Constraint.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => PUnit)
    (fun n _ _ => n) PUnit.unit (fun _ _ => PUnit.unit) c

theorem Constraint.valueRec_mk (n : Nat) (r : Reason) : (Constraint.mk n r).valueRec = n := rfl

example (c : Constraint) : c.valueRec = c.value := by cases c; rfl

/-! ## Nested blocks -/

inductive Rose
  | node (kids : List Rose)

theorem Rose.rec' :
    @Rose.rec (fun _ => Nat) (fun _ => Nat) (fun _ n => n) 0 (fun _ _ a b => a + b)
      (Rose.node []) = 0 := rfl

inductive J
  | mk (a : Array J) (o : Option J)

inductive NN
  | mk (x : List (Array NN))

mutual
inductive A1
  | mk (x : List B1)
inductive B1
  | mk (x : Option A1)
  | stop
end

structure NS where
  kids : List NS

theorem NS.kids' : (NS.mk []).kids = [] := rfl

/-- A nested occurrence under a binder. -/
inductive NB
  | mk (f : Nat → List NB)

/-- Three nested shapes: an index domain over a parameter, a reflexive field into a
member of a nested block, a container pinned at a function into the block. -/
inductive NB4 (α : Type) : List α → Type where
  | nil : NB4 α []
  | mk : List (NB4 α []) → NB4 α []

inductive RA1 where
  | leaf : RA1
  | mk : (Nat → RA1) → List RA1 → RA1

inductive RA3 where
  | leaf : RA3
  | mk : Option (Nat → RA3) → RA3

/-! ## Definitions the raw fixtures use -/

/-- An identity on types: a recursive occurrence behind it is direct after whnf. -/
def Id' (α : Type) : Type := α

/-- `List` behind a definition: a nested occurrence Lean's syntactic detection
does not see. -/
def LA (α : Type) : Type := List α

/-- A phantom: a definition that discards its argument. -/
def Tagged (_α : Type) : Type := Nat

/-- A container negative in its parameter, and a definition that hides it. -/
inductive NegC (α : Type)
  | mk (f : α → Nat)

def NA (α : Type) : Type := NegC α

/-- A former declared at a definition (Mathlib's `MorphismProperty.ofHoms` shape). -/
def RelP (α : Type) : Type := α → α → Prop

inductive RT : RelP Nat
  | refl (a : Nat) : RT a a

/-! ## Quotients -/

def QR (a b : Nat) : Prop := a % 2 = b % 2

def QT : Type := Quot QR

def QT.f : QT → Nat := Quot.lift (fun n => n % 2) (fun _ _ h => h)

theorem QT.f' : QT.f (Quot.mk QR 3) = 1 := rfl

/-! ## Unsafe -/

unsafe inductive UB
  | mk (f : UB → UB)

end IxIV
