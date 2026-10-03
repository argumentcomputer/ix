/-! A0: passing neighbours of the audit reproducers (`auxgen-audit/blackbox/
repro/*` headers and `audit-whitebox-5.md`), with value pins. Each namespace
must compile in both compilers (`ALIGNED`) and be accepted by both kernels and
the certified checker; a neighbour that starts failing is a regression. -/

/-! BB-F1 neighbours: the alpha pair alone, the 3-ring, the alpha triple. -/
namespace F1Pair
mutual
inductive A where
  | z
  | s : B → A
inductive B where
  | z
  | s : A → B
end
mutual
def A.depth : A → Nat
  | .z => 0
  | .s b => b.depth + 1
def B.depth : B → Nat
  | .z => 0
  | .s a => a.depth + 1
end
theorem depth_pin : A.depth (.s (.s .z)) = 2 := rfl
end F1Pair

namespace F1Ring
mutual
inductive A where
  | z
  | s : B → A
inductive B where
  | z
  | s : C → B
inductive C where
  | z
  | s : A → C
end
theorem ring_inh : Nonempty A := ⟨.s (.s (.s .z))⟩
end F1Ring

-- The ring again, with mutual structural recursion over all three members.
namespace F1Triple
mutual
inductive A where
  | z
  | s : B → A
inductive B where
  | z
  | s : C → B
inductive C where
  | z
  | s : A → C
end
mutual
def A.n : A → Nat
  | .z => 0
  | .s b => b.n + 1
def B.n : B → Nat
  | .z => 0
  | .s c => c.n + 1
def C.n : C → Nat
  | .z => 0
  | .s a => a.n + 1
end
theorem n_pin : A.n (.s (.s (.s (.s .z)))) = 4 := rfl
end F1Triple

/-! BB-F4 neighbours: fully applied users of a non-nested alpha pair. -/
namespace F4Flat
mutual
inductive A : Type where
  | z
  | s : B → A
inductive B : Type where
  | z
  | s : A → B
end
theorem t (a : A) : True :=
  A.rec (motive_1 := fun _ => True) (motive_2 := fun _ => True)
    trivial (fun _ _ => trivial) trivial (fun _ _ => trivial) a
mutual
def A.size : A → Nat
  | .z => 1
  | .s b => b.size + 1
def B.size : B → Nat
  | .z => 1
  | .s a => a.size + 1
end
theorem size_pin : A.size (.s (.s .z)) = 3 := rfl
end F4Flat

/-! BB-F5 neighbours: nested through a non-dependent pair and a PSigma. -/
namespace F5Prod
inductive T : Type where
  | leaf : T
  | node : Nat × List T → T
theorem inh : Nonempty T := ⟨.node (1, [.leaf])⟩
end F5Prod

namespace F5PSigma
inductive T : Type where
  | leaf : T
  | node : PSigma (fun (_ : Nat) => T) → T
theorem inh : Nonempty T := ⟨.node ⟨0, .leaf⟩⟩
end F5PSigma

/-! BB-F6 neighbour: the indexed member declared second. -/
namespace F6AFirst
mutual
inductive A : Type where
  | nil
  | mk : {n : Nat} → B n → A
inductive B : Nat → Type where
  | z : B 0
  | s : {n : Nat} → A → B n → B (n + 1)
end
mutual
def A.w : A → Nat
  | .nil => 0
  | .mk b => b.w + 1
  termination_by structural x => x
def B.w : {n : Nat} → B n → Nat
  | _, .z => 0
  | _, .s a b => a.w + b.w
  termination_by structural _ x => x
end
theorem w_pin : A.w (.mk (.s .nil .z)) = 1 := rfl
end F6AFirst

/-! BB-F8 neighbour: `B` also references `A`, so the block does not split. -/
namespace F8NoSplit
inductive PBox (p : Prop) : Prop
  | mk : p → PBox p
mutual
inductive A : Prop
  | mk : PBox B → A
inductive B : Prop
  | leaf
  | s : A → B
end
theorem b_inh : B := .leaf
end F8NoSplit

/-! BB-L2 neighbours: Prop members with two constructors, or a data field. -/
namespace L2TwoCtors
mutual
inductive A : Prop
  | mk : True → A
  | mk2 : A
inductive B : Prop
  | mk : True → True → B
  | mk2 : B
end
theorem ua (h : A) : True := by
  cases h <;> trivial
end L2TwoCtors

namespace L2Data
mutual
inductive A : Type
  | mk : Nat → A
inductive B : Type
  | mk : Nat → Nat → B
end
def A.val : A → Nat
  | .mk n => n
theorem val_pin : A.val (.mk 5) = 5 := rfl
end L2Data

/-! WB-B1 neighbours: `.below`/`.brecOn` of a recursive inductive, used by
    structural recursion (the auxiliary family exists by Lean's rule). -/
namespace RecBelow
inductive T where
  | leaf
  | node : T → T → T
def T.size : T → Nat
  | .leaf => 1
  | .node l r => l.size + r.size
theorem size_pin : T.size (.node .leaf (.node .leaf .leaf)) = 3 := rfl
end RecBelow
