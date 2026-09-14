/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Std.AxiomAudit
import Ix.Theory.Named.Inductive
import Ix.Theory.Named.Meta

/-!
# Mutual public-generation fixtures

These real kernel declarations pin shared parameters, per-family
indices/results, constructor order, and cross-family recursive target
ordinals at the `VInductDecl.CheckedBlock` boundary, then exercise the
block-wide public generation transaction. The Verify mutual
fixture supplies semantic preservation, complete kernel metadata comparison,
and environment replay.
-/

namespace Ix.Theory.Named.MutualInductiveFixtures

open VInductDecl

universe u

/-! ## Unindexed Tree/TreeList -/

mutual

inductive Tree (α : Type u) : Type u where
  | leaf : α → Tree α
  | node : TreeList α → Tree α
  | branch : (α → TreeList α) → Tree α

inductive TreeList (α : Type u) : Type u where
  | nil : TreeList α
  | cons : Tree α → TreeList α → TreeList α

end

def treeType : VInductiveType where
  name := ``Tree
  uvars := 1
  type := vconst(type_of% @Tree).type
  ctors := [⟨vconst(type_of% @Tree.leaf), ``Tree.leaf⟩,
    ⟨vconst(type_of% @Tree.node), ``Tree.node⟩,
    ⟨vconst(type_of% @Tree.branch), ``Tree.branch⟩]

def treeListType : VInductiveType where
  name := ``TreeList
  uvars := 1
  type := vconst(type_of% @TreeList).type
  ctors := [⟨vconst(type_of% @TreeList.nil), ``TreeList.nil⟩,
    ⟨vconst(type_of% @TreeList.cons), ``TreeList.cons⟩]

def treeDecl : VInductDecl :=
  ⟨1, 1, [treeType, treeListType]⟩

def treeChecked : treeDecl.CheckedBlock :=
  treeDecl.checkedBlock?.get (by decide)

/-- Block-wide generation data for the real unindexed mutual declaration. -/
def treeGeneration : BlockGenerationChecked treeDecl :=
  treeDecl.identityBlockGeneration?.get (by decide)

example : treeChecked.params = [.sort (.succ (.param 0))] := rfl
example : treeChecked.families.values = [treeType, treeListType] := rfl
example : treeChecked.families.ordinals = [0, 1] := rfl
example : treeChecked.families.names = [``Tree, ``TreeList] := rfl
example : treeChecked.families.indices = [[], []] := rfl
example : treeChecked.families.resultLevels =
    [.succ (.param 0), .succ (.param 0)] := rfl
example : treeChecked.families.constructorNames =
    [[``Tree.leaf, ``Tree.node, ``Tree.branch],
      [``TreeList.nil, ``TreeList.cons]] := rfl
example : treeChecked.families.recursiveTargets =
    [[[], [1], [1]], [[], [0, 1]]] := rfl
example : treeChecked.names =
    [``Tree, ``TreeList, ``Tree.leaf, ``Tree.node, ``Tree.branch,
      ``TreeList.nil, ``TreeList.cons, ``Tree.rec, ``TreeList.rec] := rfl

example : treeGeneration.families.map (·.raw.name) =
    [``Tree, ``TreeList] := rfl
example : treeGeneration.motiveTypes.length = 2 := rfl
example : treeGeneration.minorTypes.length = 5 := rfl
example : treeGeneration.recursors.map (·.name) =
    [``Tree.rec, ``TreeList.rec] := rfl
example : treeGeneration.generatedRules.length = 5 := rfl

example : treeChecked.families.constructors[0][1].recursive[0].fieldIndex = 0 := rfl
example : treeChecked.families.constructors[0][1].recursive[0].targetType = 1 := rfl
example : treeChecked.families.constructors[0][2].recursive[0].fieldIndex = 0 := rfl
example : treeChecked.families.constructors[0][2].recursive[0].binders.length = 1 := rfl
example : treeChecked.families.constructors[0][2].recursive[0].targetType = 1 := rfl
example : treeChecked.families.constructors[1][1].recursive[0].targetType = 0 := rfl
example : treeChecked.families.constructors[1][1].recursive[1].targetType = 1 := rfl

/-! ## Indexed mutual block -/

mutual

inductive IndexedTree (α : Type u) : Nat → Type u where
  | leaf : α → IndexedTree α .zero
  | node {n : Nat} : IndexedTreeList α n → IndexedTree α (.succ n)

inductive IndexedTreeList (α : Type u) : Nat → Type u where
  | nil : IndexedTreeList α .zero
  | cons {n : Nat} :
      IndexedTree α n → IndexedTreeList α n → IndexedTreeList α (.succ n)

end

def indexedTreeType : VInductiveType where
  name := ``IndexedTree
  uvars := 1
  type := vconst(type_of% @IndexedTree).type
  ctors := [⟨vconst(type_of% @IndexedTree.leaf), ``IndexedTree.leaf⟩,
    ⟨vconst(type_of% @IndexedTree.node), ``IndexedTree.node⟩]

def indexedTreeListType : VInductiveType where
  name := ``IndexedTreeList
  uvars := 1
  type := vconst(type_of% @IndexedTreeList).type
  ctors := [⟨vconst(type_of% @IndexedTreeList.nil), ``IndexedTreeList.nil⟩,
    ⟨vconst(type_of% @IndexedTreeList.cons), ``IndexedTreeList.cons⟩]

def indexedTreeDecl : VInductDecl :=
  ⟨1, 1, [indexedTreeType, indexedTreeListType]⟩

def indexedTreeChecked : indexedTreeDecl.CheckedBlock :=
  indexedTreeDecl.checkedBlock?.get (by decide)

/-- Block-wide generation data for the real indexed mutual declaration. -/
def indexedTreeGeneration : BlockGenerationChecked indexedTreeDecl :=
  indexedTreeDecl.identityBlockGeneration?.get (by decide)

example : indexedTreeChecked.params = [.sort (.succ (.param 0))] := rfl
example : indexedTreeChecked.families.values =
    [indexedTreeType, indexedTreeListType] := rfl
example : indexedTreeChecked.families.ordinals = [0, 1] := rfl
example : indexedTreeChecked.families.names =
    [``IndexedTree, ``IndexedTreeList] := rfl
example : indexedTreeChecked.families.indices =
    [[.const ``Nat []], [.const ``Nat []]] := rfl
example : indexedTreeChecked.families.resultLevels =
    [.succ (.param 0), .succ (.param 0)] := rfl
example : indexedTreeChecked.families.constructorNames =
    [[``IndexedTree.leaf, ``IndexedTree.node],
      [``IndexedTreeList.nil, ``IndexedTreeList.cons]] := rfl
example : indexedTreeChecked.families.recursiveTargets =
    [[[], [1]], [[], [0, 1]]] := rfl

example : indexedTreeGeneration.families.map (·.raw.name) =
    [``IndexedTree, ``IndexedTreeList] := rfl
example : indexedTreeGeneration.motiveTypes.length = 2 := rfl
example : indexedTreeGeneration.minorTypes.length = 4 := rfl
example : indexedTreeGeneration.recursors.map (·.name) =
    [``IndexedTree.rec, ``IndexedTreeList.rec] := rfl
example : indexedTreeGeneration.generatedRules.length = 4 := rfl

example : indexedTreeChecked.families.constructors[0][0].resultIndices =
    [.const ``Nat.zero []] := rfl
example : indexedTreeChecked.families.constructors[0][1].resultIndices =
    [.app (.const ``Nat.succ []) (.bvar 1)] := rfl
example : indexedTreeChecked.families.constructors[1][0].resultIndices =
    [.const ``Nat.zero []] := rfl
example : indexedTreeChecked.families.constructors[1][1].resultIndices =
    [.app (.const ``Nat.succ []) (.bvar 2)] := rfl
example : indexedTreeChecked.families.constructors[0][1].recursive[0].fieldIndex = 1 := rfl
example : indexedTreeChecked.families.constructors[0][1].recursive[0].targetType = 1 := rfl
example : indexedTreeChecked.families.constructors[0][1].recursive[0].indices =
    [.bvar 0] := rfl
example : indexedTreeChecked.families.constructors[1][1].recursive[0].fieldIndex = 1 := rfl
example : indexedTreeChecked.families.constructors[1][1].recursive[0].targetType = 0 := rfl
example : indexedTreeChecked.families.constructors[1][1].recursive[1].fieldIndex = 2 := rfl
example : indexedTreeChecked.families.constructors[1][1].recursive[1].targetType = 1 := rfl

/-! ## Public block-wide boundary -/

example : treeDecl.stage3 = true := rfl
example : indexedTreeDecl.stage3 = true := rfl
example : VEnv.empty.addInduct treeDecl =
    VEnv.empty.addInductBlockGeneration treeGeneration := rfl
example : VEnv.empty.addInduct indexedTreeDecl =
    VEnv.empty.addInductBlockGeneration indexedTreeGeneration := rfl
example : (VEnv.empty.addInduct treeDecl).isSome = true := rfl
example : (VEnv.empty.addInduct indexedTreeDecl).isSome = true := rfl

#guard_named_axioms Ix.Theory.Named.VInductDecl.checkedBlock? [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.MutualInductiveFixtures.treeChecked [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.MutualInductiveFixtures.indexedTreeChecked [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.CheckedFamilies.values_eq [propext, Quot.sound]

end Ix.Theory.Named.MutualInductiveFixtures
