/-! # Lean sources of the tier's inductive fixtures (M7 Q1)

Ordinary Lean declarations, checked by Lean's kernel, that
`Tests.Ix.Kernel.TierInd` installs typing only (`Ix.Kernel.Tier.indC`) and
asks about in the check view and the answer view: unsafe inductives (a
reflexive one, a nested one, a negative occurrence, a structure, a mutual
pair), a propositional family installed without its recursor, a universe
fixture, an unsafe definition, and the queries (unsafe definitions whose
values are the terms asked about). The module imports only `Init`. -/

namespace Tests.Ix.Kernel.TierIndDefs

unsafe inductive U
  | leaf
  | mk : (U → U) → U

unsafe inductive UN
  | mk : List UN → UN

/-- MLList's polymorphic shape, including its nested Thunk recursor. -/
unsafe inductive Poly (m : Type u → Type u) (α : Type u) : Type u
  | nil : Poly m α
  | cons : α → Poly m α → Poly m α
  | thunk : Thunk (Poly m α) → Poly m α
  | squash : (Unit → m (Poly m α)) → Poly m α

unsafe inductive UNeg
  | mk : (UNeg → Bool) → UNeg

unsafe structure S where
  b : Bool

mutual
unsafe inductive A
  | a : B → A
  | z : A
unsafe inductive B
  | b : A → B
end

/-- A family installed without its recursor (as a Prop-level `.below`
family is, before its recursors exist). -/
inductive PF : Bool → Prop
  | t : PF true

unsafe inductive Big : Type 1
  | mk : Type → Big

unsafe def kdef : Bool := true

/-- A partial definition (its `_unsafe_rec` companion is the tier's stage 0). -/
partial def spin (n : Nat) : Nat := if n == 0 then 0 else spin (n - 1)

/-! The queries: each value is a term asked about. -/

noncomputable unsafe def qIota : Bool := U.rec (motive := fun _ => Bool) true (fun _ _ => false) U.leaf
noncomputable unsafe def qNested : Bool :=
  UN.rec (motive_1 := fun _ => Bool) (motive_2 := fun _ => Bool) (fun _ ih => ih) true
    (fun _ _ _ _ => false) (UN.mk [])
noncomputable unsafe def qPoly : Bool :=
  Poly.rec (motive_1 := fun _ => Bool) (motive_2 := fun _ => Bool)
    true (fun _ _ ih => ih) (fun _ ih => ih) (fun _ => false) (fun _ ih => ih ())
    (Poly.thunk ⟨fun _ => Poly.nil (m := Id) (α := Bool)⟩)
unsafe def qEtaL : S → S := fun s => s
unsafe def qEtaR : S → S := fun s => S.mk s.b
unsafe def qDelta : Bool := kdef
unsafe def qTrue : Bool := true
theorem qPfL : PF true → PF true := fun h => h
theorem qPfR : PF true → PF true := fun _ => PF.t
noncomputable def qPfRec := @PF.rec

end Tests.Ix.Kernel.TierIndDefs
