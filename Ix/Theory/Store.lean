/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Const

namespace Ix.Theory

/-- A finite view of a content-addressed constant store. -/
structure Store (β : Type u) where
  dom : List β
  nodup : dom.Nodup
  blocks : β → Option (Block β)
  mem_dom : ∀ b, (blocks b).isSome ↔ b ∈ dom

namespace Store

/-- Look up an ordinary block member. Constructor references use `lookupCtor`. -/
def lookup (store : Store β) : ConstRef β → Option (Const β)
  | .member block index => do
      let contents ← store.blocks block
      contents.members[index]?
  | .ctor .. => none

/-- Look up a constructor nested under an inductive block member. -/
def lookupCtor (store : Store β) : ConstRef β → Option (Ctor β)
  | .member .. => none
  | .ctor block member ctor => do
      let contents ← store.blocks block
      let constant ← contents.members[member]?
      match constant with
      | .induct _ _ _ _ ctors _ => ctors[ctor]?
      | _ => none

/-- Flattened constructor-rule position of a nested constructor reference. -/
def ctorRuleIndex? (store : Store β) : ConstRef β → Option Nat
  | .member .. => none
  | .ctor block member ctor => do
      let some contents := store.blocks block | none
      let some constant := contents.members[member]? | none
      match constant with
      | .induct _ _ _ _ ctors _ =>
          if ctor < ctors.length then
            some ((contents.members.take member).foldl
              (fun offset entry => offset + entry.ctorCount) 0 + ctor)
          else
            none
      | _ => none

/-- Classify either an ordinary member or a nested constructor reference. -/
def kind (store : Store β) (ref : ConstRef β) : Option ConstKind :=
  match store.lookup ref with
  | some constant => some constant.kind
  | none => (store.lookupCtor ref).map fun _ => .ctor

/-- Universe arity of an ordinary member or nested constructor. -/
def uvars (store : Store β) (ref : ConstRef β) : Option Nat :=
  match store.lookup ref with
  | some constant => some constant.uvars
  | none => (store.lookupCtor ref).map Ctor.uvars

/-- Type of an ordinary member or nested constructor. -/
def type (store : Store β) (ref : ConstRef β) : Option (VExpr β) :=
  match store.lookup ref with
  | some constant => some constant.type
  | none => (store.lookupCtor ref).map Ctor.type

/-- Distinct dependencies of a block, excluding self references. -/
def deps [DecidableEq β] (store : Store β) (block : β) : List β :=
  (((store.blocks block).map Block.refs).getD []).map ConstRef.block
    |>.filter (· != block)
    |>.eraseDups

/-- `block` directly refers to `dependency`, and the dependency is present. -/
def DependsOn [DecidableEq β] (store : Store β) (block dependency : β) : Prop :=
  dependency ∈ store.deps block ∧ dependency ∈ store.dom

/-- Reflexive transitive dependency closure of one block. -/
inductive Closure [DecidableEq β] (store : Store β) (root : β) : β → Prop where
  | refl : store.Closure root root
  | step : store.Closure root block → store.DependsOn block dependency →
      store.Closure root dependency

/-- Dependencies point strictly backward in some well-founded order. -/
def Acyclic [DecidableEq β] (store : Store β) : Prop :=
  WellFounded (flip store.DependsOn)

/-- Keep exactly the blocks satisfying `keep`. This is a proof-facing view;
executable consumers may supply their own finite closure computation. -/
noncomputable def restrict (store : Store β) (keep : β → Prop) : Store β := by
  classical
  exact {
    dom := store.dom.filter keep
    nodup := store.nodup.filter _
    blocks := fun block => if keep block then store.blocks block else none
    mem_dom := by
      intro block
      by_cases h : keep block <;> simp [h, store.mem_dom]
  }

/-- Pointwise inclusion of partial block maps. -/
protected def Subset (left right : Store β) : Prop :=
  ∀ block contents, left.blocks block = some contents →
    right.blocks block = some contents

instance : HasSubset (Store β) := ⟨Store.Subset⟩

/-- Return a block identifier only when the requested content occurs exactly once. -/
def designated [DecidableEq β] (store : Store β) (canon : Block β) : Option β :=
  match store.dom.filter fun block => store.blocks block == some canon with
  | [block] => some block
  | _ => none

end Store
end Ix.Theory
