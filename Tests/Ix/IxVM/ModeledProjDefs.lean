/-! # Fixtures for modeled structure projections

Ordinary, kernel-checked Lean declarations for `Tests.Ix.IxVM.ModeledProj`:

* **Nested-recursive structures**: `NestedDoc` (0-param, mirroring `Lean.Doc.Part` /
  `SnapshotTree`), `MyTree` (`Bool`-parameterized, two same-typed `Nat` fields for the
  parameter-dependent projection-swap attack), `DepNested` (type + `Bool` parameters,
  `Prop` field, dependent `Fin (idx + 1)` field), `SortPolyField` (universe-polymorphic
  `Sort u` field + dependent element field).
* **Mutual-recursive structures**: `GuardedExp` / `GuardedExprs` (mirroring
  `HaskellSpec.Source.{GuardedExp,GuardedExprs}`), plus direct projection functions and
  definitional ι-reduction theorems (`rfl`).
* **Negative-control base families**: a 2-constructor mutual family (`TwoCtorMutA`/`TwoCtorMutB`),
  a 0-constructor mutual member (`ZeroCtorMutA`/`ZeroCtorMutB`), an indexed nested 1-constructor
  inductive (`IndexedNested`), and a `Prop` 1-constructor mutual pair (`PropMutA`/`PropMutB`),
  whose forged `.proj` expressions IxVM must refuse. -/

namespace Tests.Ix.IxVM.ModeledProjDefs

/-! ## Nested-recursive 1-constructor structures -/

/-- Nested-recursive structure (0 parameters), mirroring `Lean.Doc.Part`. -/
structure NestedDoc where
  title : String
  rank : Nat
  subParts : Array NestedDoc

theorem nestedDocTitleIota : (NestedDoc.mk "doc" 7 #[]).title = "doc" := rfl
theorem nestedDocRankIota : (NestedDoc.mk "doc" 7 #[]).rank = 7 := rfl
theorem nestedDocSubPartsIota : (NestedDoc.mk "doc" 7 #[]).subParts = #[] := rfl

/-- `Bool`-parameterized nested-recursive structure with two `Nat` fields. -/
structure MyTree (b : Bool) where
  left : Nat
  right : Nat
  kids : List (MyTree b)

theorem myTreeLeftIota (b : Bool) : (MyTree.mk (b := b) 1 2 []).left = 1 := rfl
theorem myTreeRightIota (b : Bool) : (MyTree.mk (b := b) 1 2 []).right = 2 := rfl

/-- `Nat`-parameterized nested-recursive structure for parameter-dependent `swap01` attack. -/
structure NatTree (n : Nat) where
  left : Nat
  right : Nat
  kids : List (NatTree n)

theorem natTreeLeftIota (n : Nat) : (NatTree.mk (n := n) 1 2 []).left = 1 := rfl

/-- Parameterized nested-recursive structure with a `Prop` field and a dependent field. -/
structure DepNested (α : Type u) (flag : Bool) where
  idx : Nat
  fin : Fin (idx + 1)
  proof : idx = idx
  val : α
  kids : List (DepNested α flag)

theorem depNestedFinIota :
    (DepNested.mk (α := Nat) (flag := true) 3 ⟨2, by decide⟩ rfl 9 []).fin = ⟨2, by decide⟩ := rfl
theorem depNestedProofIota :
    (DepNested.mk (α := Nat) (flag := true) 3 ⟨2, by decide⟩ rfl 9 []).proof = rfl := rfl
theorem depNestedValIota :
    (DepNested.mk (α := Nat) (flag := true) 3 ⟨2, by decide⟩ rfl 9 []).val = 9 := rfl

/-- Nested-recursive structure with a sort-polymorphic `Sort u` field over a parameter. -/
structure SortPolyParam.{u} (α : Sort u) : Type u where
  elem : α
  kids : List (SortPolyParam α)

theorem sortPolyParamTypeIota :
    (@SortPolyParam.mk.{1} Nat 5 []).elem = 5 := rfl
theorem sortPolyParamPropIota :
    (@SortPolyParam.mk.{0} True trivial []).elem = trivial := rfl

/-- Nested-recursive structure whose `Sort u` field depends on an earlier field (control). -/
structure SortPolyField.{u} where
  carrier : Sort u
  elem : carrier
  kids : List SortPolyField

/-! ## Mutual-recursive 1-constructor structures -/

mutual
  structure GuardedExp where
    guard : Nat
    body : GuardedExprs

  structure GuardedExprs where
    binds : List GuardedExp
    gdes : List GuardedExp
end

theorem guardedExpGuardIota :
    (GuardedExp.mk 11 (GuardedExprs.mk [] [])).guard = 11 := rfl
theorem guardedExprsBindsIota :
    (GuardedExprs.mk [GuardedExp.mk 5 (GuardedExprs.mk [] [])] []).binds.length = 1 := rfl
theorem guardedExpNestedProjIota :
    ((GuardedExp.mk 3 (GuardedExprs.mk [GuardedExp.mk 9 (GuardedExprs.mk [] [])] [])).body).binds.length = 1 := rfl

/-! ## Negative-control base families (legal Lean types; projections on them are illegal) -/

mutual
  inductive TwoCtorMutA where
    | a1 (n : Nat) : TwoCtorMutA
    | a2 (b : TwoCtorMutB) : TwoCtorMutA
  inductive TwoCtorMutB where
    | b1 (a : TwoCtorMutA) : TwoCtorMutB
end

mutual
  inductive ZeroCtorMutA where
  inductive ZeroCtorMutB where
    | b1 (a : ZeroCtorMutA) : ZeroCtorMutB
end

inductive IndexedNested : Nat → Type where
  | mk (n : Nat) (xs : List (IndexedNested 0)) : IndexedNested 1

mutual
  inductive PropMutA : Prop where
    | mk (n : Nat) (b : PropMutB) : PropMutA
  inductive PropMutB : Prop where
    | mk (a : PropMutA) : PropMutB
end

end Tests.Ix.IxVM.ModeledProjDefs
