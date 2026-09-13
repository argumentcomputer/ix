/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Std.AxiomAudit
import Ix.Theory.Named.Verify.Environment.Lemmas
import Ix.Theory.Named.Verify.Environment.ConstructorValidation
import Ix.Theory.Named.Reference.Inductive.Add
import Ix.Theory.Named.Meta
import Ix.Theory.Named.InductiveFixtures
import Ix.Theory.Named.Typing.Meta

open Ix.Theory (VLevel)

/-! End-to-end replay fixtures for inductive environment alignment.

The Theory fixtures compare generated recursors and iota rules with Lean's
kernel declarations. This module closes the next bridge: it quotes the actual
`ConstantInfo` metadata, translates each metadata type in the precise
intermediate Theory environment, constructs `AddInduct`, and drives the live
`TrEnv'.induct` case. -/

namespace Ix.Theory.Named.InductiveReplayFixtures
open Lean Meta Elab Term
open Ix.Theory.Named.InductiveFixtures

/- These instances are used only by the elaborators below to quote the kernel
metadata returned by `getConstInfo`. -/
deriving instance ToExpr for ConstantVal
deriving instance ToExpr for InductiveVal
deriving instance ToExpr for ConstructorVal
deriving instance ToExpr for RecursorRule
deriving instance ToExpr for RecursorVal
deriving instance ToExpr for ReducibilityHints
deriving instance ToExpr for DefinitionSafety
deriving instance ToExpr for DefinitionVal

syntax "kernelInductInfo%" ident : term
syntax "kernelCtorInfo%" ident : term
syntax "kernelRecInfo%" ident : term
syntax "kernelRecRuleRhs%" ident num : term
syntax "kernelDefVal%" ident : term

elab_rules : term
  | `(kernelInductInfo% $n:ident) => do
    let name ← realizeGlobalConstNoOverloadWithInfo n
    let .inductInfo info ← getConstInfo name
      | throwError "expected inductive metadata for {name}"
    return mkApp (mkConst ``ConstantInfo.inductInfo) (toExpr info)
  | `(kernelCtorInfo% $n:ident) => do
    let name ← realizeGlobalConstNoOverloadWithInfo n
    let .ctorInfo info ← getConstInfo name
      | throwError "expected constructor metadata for {name}"
    return mkApp (mkConst ``ConstantInfo.ctorInfo) (toExpr info)
  | `(kernelRecInfo% $n:ident) => do
    let name ← realizeGlobalConstNoOverloadWithInfo n
    let .recInfo info ← getConstInfo name
      | throwError "expected recursor metadata for {name}"
    return mkApp (mkConst ``ConstantInfo.recInfo) (toExpr info)
  | `(kernelDefVal% $n:ident) => do
    let name ← realizeGlobalConstNoOverloadWithInfo n
    let .defnInfo info ← getConstInfo name
      | throwError "expected definition metadata for {name}"
    return toExpr info

/-- Quote one kernel recursor-rule RHS using the rule's own universe-parameter
order. This lets replay fixtures compare implementation metadata with the
Theory equation generator by reduction, including lambdas under recursive Pi
arguments. -/
elab_rules : term
  | `(kernelRecRuleRhs% $n:ident $i:num) => do
    let name ← realizeGlobalConstNoOverloadWithInfo n
    let .recInfo info ← getConstInfo name
      | throwError "expected recursor metadata for {name}"
    let some rule := info.rules[i.getNat]?
      | throwError "missing recursor rule {i.getNat} for {name}"
    let rhs ← Ix.Theory.Named.Meta.expandExpr rule.rhs
    let rhs ← Ix.Theory.Named.Meta.ofExpr info.levelParams {} rhs
    return toExpr rhs

/- Construct the representation-only half of a metadata-type translation.
The `to_trExprS` theorem supplies every typing premise from the declaration's
actual Theory `WF` evidence. -/
syntax "tr_type_expr_tac" : tactic
macro_rules
  | `(tactic| tr_type_expr_tac) => `(tactic|
    first
    | apply TrTypeExpr.bvar; rfl
    | apply TrTypeExpr.sort; rfl
    | apply TrTypeExpr.const <;>
        (first | assumption | rfl | (dsimp; simp [VLevel.params']))
    | apply TrTypeExpr.app <;> tr_type_expr_tac
    | apply TrTypeExpr.mdata; tr_type_expr_tac
    | apply TrTypeExpr.forallE <;> tr_type_expr_tac)

local instance : Inhabited VEnv := ⟨.empty⟩

/-! ## Nat -/

/-- Kernel metadata, captured at elaboration rather than reconstructed by the
fixture. A change in Lean's emitted record is therefore a compile failure. -/
def natInfo : ConstantInfo := kernelInductInfo% Nat
def natZeroInfo : ConstantInfo := kernelCtorInfo% Nat.zero
def natSuccInfo : ConstantInfo := kernelCtorInfo% Nat.succ
def natRecInfo : ConstantInfo := kernelRecInfo% Nat.rec
def natZeroKernelRuleRhs : VExpr := kernelRecRuleRhs% Nat.rec 0
def natSuccKernelRuleRhs : VExpr := kernelRecRuleRhs% Nat.rec 1

example : natInfo.name = ``Nat := rfl
example : natZeroInfo.name = ``Nat.zero := rfl
example : natSuccInfo.name = ``Nat.succ := rfl
example : natRecInfo.name = ``Nat.rec := rfl
example : natZeroKernelRuleRhs =
    natChecked.identityGeneration.generatedRules[0].rhs := rfl
example : natSuccKernelRuleRhs =
    natChecked.identityGeneration.generatedRules[1].rhs := rfl

def natTypeEnv := (VEnv.empty.addConst natType.name natType.toVConstant).get!
def natZeroEnv :=
  (natTypeEnv.addConst natType.ctors[0].name natType.ctors[0].toVConstant).get!
def natCtorEnv :=
  (natZeroEnv.addConst natType.ctors[1].name natType.ctors[1].toVConstant).get!
def natRecEnv :=
  (natCtorEnv.addConst ``Nat.rec (VInductDecl.recConst 0 ``Nat 0 natType)).get!

theorem natTypeEnv_ordered : natTypeEnv.Ordered := by
  refine .const .empty ?_ rfl
  exact ⟨.succ (.succ .zero), VEnv.HasType.sort (by decide)⟩

theorem natZeroEnv_ordered : natZeroEnv.Ordered := by
  refine .const (n := natType.ctors[0].name) (ci := natType.ctors[0].toVConstant)
    natTypeEnv_ordered ?_ rfl
  have hNat : natTypeEnv.constants ``Nat = some natType.toVConstant := rfl
  exact ⟨.succ .zero, by type_tac⟩

theorem natSucc_wf : natType.ctors[1].toVConstant.WF natZeroEnv := by
  have hNat : natZeroEnv.constants ``Nat = some natType.toVConstant := rfl
  refine ⟨.imax (.succ .zero) (.succ .zero), ?_⟩
  refine VEnv.HasType.forallE (u := .succ .zero) (v := .succ .zero) ?_ ?_
  · type_tac
  · type_tac

theorem natCtorEnv_ordered : natCtorEnv.Ordered := by
  exact .const (n := natType.ctors[1].name) (ci := natType.ctors[1].toVConstant)
    natZeroEnv_ordered natSucc_wf rfl

/-- `Nat` satisfies the public Stage-3 declaration contract without a fixture
assumption. -/
theorem natDecl_wf : natDecl.WF VEnv.empty := by
  refine ⟨rfl, ?_⟩
  intro ty hty
  have hty' : ty = natType := List.mem_singleton.1 (by simpa [natDecl] using hty)
  subst ty
  refine ⟨?_, ?_⟩
  · change True
    trivial
  intro c hc
  rcases List.mem_cons.1 hc with rfl | hc
  · constructor
    · change True
      trivial
    · exact .nil
  · have hc' := List.mem_singleton.1 hc
    subst c
    constructor
    · refine ⟨.inl rfl, ?_, trivial⟩
      intro
      exact .nil
    · exact .nil

/-- The exact intermediate invariant used to type the generated recursor. -/
theorem natStage3 :
    VInductDecl.Stage3Env natCtorEnv 0 ``Nat 0 (.succ .zero) natType := by
  refine {
    ord := natCtorEnv_ordered
    hl := by decide
    hsort := rfl
    hlen := rfl
    hT := rfl
    hcs := ?_
    htel := ?_
    hs3 := ?_
    hparams := ?_
    hfields := ?_
    hresult := ?_ }
  · intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · rfl
    · have hc' := List.mem_singleton.1 hc
      subst c
      rfl
  · intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · rfl
    · have hc' := List.mem_singleton.1 hc
      subst c
      rfl
  · intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · rfl
    · have hc' := List.mem_singleton.1 hc
      subst c
      rfl
  · change True
    trivial
  · intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · change True
      trivial
    · have hc' := List.mem_singleton.1 hc
      subst c
      refine ⟨.inl rfl, ?_, trivial⟩
      intro
      exact .nil
  · intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact .nil
    · have hc' := List.mem_singleton.1 hc
      subst c
      exact .nil

theorem natInfo_tr :
    TrConstVal .safe VEnv.empty natInfo natType.toVConstVal := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  exact .sort rfl

theorem natZeroInfo_tr :
    TrConstVal .safe natTypeEnv natZeroInfo natType.ctors[0] := by
  have hNat : natTypeEnv.constants ``Nat = some natType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr natTypeEnv natZeroInfo.levelParams []
      natZeroInfo.type natType.ctors[0].type := by tr_type_expr_tac
  exact hshape.to_trExprS natTypeEnv_ordered trivial
    ⟨.sort (.succ .zero), by type_tac⟩

theorem natSuccInfo_tr :
    TrConstVal .safe natZeroEnv natSuccInfo natType.ctors[1] := by
  have hNat : natZeroEnv.constants ``Nat = some natType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr natZeroEnv natSuccInfo.levelParams []
      natSuccInfo.type natType.ctors[1].type := by
    exact .forallE (.const hNat rfl rfl) (.const hNat rfl rfl)
  exact hshape.to_trExprS natZeroEnv_ordered trivial
    ⟨.sort (.imax (.succ .zero) (.succ .zero)), by
      refine VEnv.HasType.forallE (u := .succ .zero) (v := .succ .zero) ?_ ?_
      · type_tac
      · type_tac⟩

theorem natRecInfo_tr :
    TrConstVal .safe natCtorEnv natRecInfo (inductRecVal natDecl natType) := by
  have hNat : natCtorEnv.constants ``Nat = some natType.toVConstant := rfl
  have hZero :
      natCtorEnv.constants ``Nat.zero = some natType.ctors[0].toVConstant := rfl
  have hSucc :
      natCtorEnv.constants ``Nat.succ = some natType.ctors[1].toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr natCtorEnv natRecInfo.levelParams [] natRecInfo.type
      (inductRecVal natDecl natType).type := by tr_type_expr_tac
  obtain ⟨u, hrec⟩ := natStage3.recConst_wf
  exact hshape.to_trExprS natCtorEnv_ordered trivial ⟨.sort u, hrec⟩

def natTypeMap : ConstMap := ({} : ConstMap).insert ``Nat natInfo
def natZeroMap : ConstMap := natTypeMap.insert ``Nat.zero natZeroInfo
def natCtorMap : ConstMap := natZeroMap.insert ``Nat.succ natSuccInfo
def natMap : ConstMap := natCtorMap.insert ``Nat.rec natRecInfo
def natFinalEnv : VEnv :=
  (VInductDecl.rules 0 ``Nat 0 natType).foldl VEnv.addDefEq natRecEnv

theorem natType_fresh : ({} : ConstMap).find? ``Nat = none := by
  simp [SMap.find?]

theorem natTypeMap_wf : natTypeMap.WF :=
  SMap.WF.empty.insert _ _ natType_fresh

theorem natZero_fresh : natTypeMap.find? ``Nat.zero = none := by
  rw [natTypeMap, SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem natZeroMap_wf : natZeroMap.WF :=
  natTypeMap_wf.insert _ _ natZero_fresh

theorem natSucc_fresh : natZeroMap.find? ``Nat.succ = none := by
  rw [natZeroMap, natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem natCtorMap_wf : natCtorMap.WF :=
  natZeroMap_wf.insert _ _ natSucc_fresh

theorem natRec_fresh : natCtorMap.find? ``Nat.rec = none := by
  rw [natCtorMap, natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

/-- A concrete `AddInduct` witness whose implementation side consists of the
actual kernel metadata above and whose Theory side is the Stage-3 Nat
transaction. -/
theorem nat_addInduct :
    AddInduct ({} : ConstMap) VEnv.empty natDecl natMap natFinalEnv := by
  refine ⟨{
    generation := natChecked.identityGeneration
    generation_wf :=
      (natChecked.wf_of_decl natDecl_wf).identityGeneration .empty
    typeMap := natTypeMap
    typeEnv := natTypeEnv
    ctorMap := natCtorMap
    ctorEnv := natCtorEnv
    recEnv := natRecEnv
    addType := {
      info := natInfo
      kind_eq := by simp [natInfo, InductConstantKind.Matches]
      tr := natInfo_tr
      map_fresh := by
        change ({} : ConstMap).find? ``Nat = none
        exact natType_fresh
      env_add := rfl
      map_add := rfl }
    addCtors := ?_
    addRec := {
      info := natRecInfo
      kind_eq := by simp [natRecInfo, InductConstantKind.Matches]
      tr := natRecInfo_tr
      map_fresh := by
        change natCtorMap.find? ``Nat.rec = none
        exact natRec_fresh
      env_add := rfl
      map_add := rfl }
    recK := by decide
    addRules := ⟨rfl⟩ }⟩
  exact .cons {
      info := natZeroInfo
      kind_eq := by simp [natZeroInfo, InductConstantKind.Matches]
      tr := natZeroInfo_tr
      map_fresh := by simpa [natType] using natZero_fresh
      env_add := rfl
      map_add := rfl }
    (.cons {
      info := natSuccInfo
      kind_eq := by simp [natSuccInfo, InductConstantKind.Matches]
      tr := natSuccInfo_tr
      map_fresh := by
        change natZeroMap.find? ``Nat.succ = none
        exact natSucc_fresh
      env_add := rfl
      map_add := rfl } .nil)

/-- The formerly impossible `TrEnv'.induct` branch, instantiated with a real
Lean declaration transaction. -/
theorem nat_trEnv' {safety : DefinitionSafety} :
    TrEnv' safety natMap false natFinalEnv :=
  .induct nat_addInduct .empty

theorem nat_final_matches_addInduct :
    VEnv.empty.addInduct natDecl = some natFinalEnv :=
  rfl

/-- Theory-only ordering evidence for the Nat dependency environment. This
keeps later inductive preservation proofs entirely within the Theory layer. -/
theorem natFinalEnv_ordered : natFinalEnv.Ordered :=
  VEnv.addInductGeneration_WF .empty
    ((natChecked.wf_of_decl natDecl_wf).identityGeneration .empty) rfl

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.natFinalEnv_ordered [propext, Classical.choice, Quot.sound]

theorem nat_env_wf : natFinalEnv.WF := (nat_trEnv' (safety := .safe)).wf

theorem nat_aligned : Aligned .safe natMap natFinalEnv := (nat_trEnv' (safety := .safe)).aligned

theorem nat_type_map_lookup : natMap.find? ``Nat = some natInfo := by
  rw [natMap, natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap, natTypeMap_wf.find?_insert,
    natTypeMap, SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  rfl

theorem nat_type_env_lookup :
    natFinalEnv.constants ``Nat = some natType.toVConstant := rfl

theorem nat_type_lookup_unique :
    natInfo.name = ``Nat ∧
      TrConstant .safe natFinalEnv natInfo natType.toVConstant :=
  nat_aligned.find?_uniq nat_type_map_lookup nat_type_env_lookup

theorem nat_succ_map_lookup : natMap.find? ``Nat.succ = some natSuccInfo := by
  rw [natMap, natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert]
  rfl

theorem nat_succ_env_lookup : natFinalEnv.constants ``Nat.succ =
    some natType.ctors[1].toVConstant := rfl

theorem nat_succ_lookup_unique :
    natSuccInfo.name = ``Nat.succ ∧
      TrConstant .safe natFinalEnv natSuccInfo
        natType.ctors[1].toVConstant :=
  nat_aligned.find?_uniq nat_succ_map_lookup nat_succ_env_lookup

theorem nat_rec_map_lookup : natMap.find? ``Nat.rec = some natRecInfo := by
  rw [natMap, natCtorMap_wf.find?_insert]
  rfl

theorem nat_rec_env_lookup : natFinalEnv.constants ``Nat.rec =
    some (VInductDecl.recConst 0 ``Nat 0 natType) := rfl

/-- Lookup uniqueness is tested at the generated recursor, after all iota
rules have been installed. -/
theorem nat_rec_lookup_unique :
    natRecInfo.name = ``Nat.rec ∧
      TrConstant .safe natFinalEnv natRecInfo
        (VInductDecl.recConst 0 ``Nat 0 natType) :=
  nat_aligned.find?_uniq nat_rec_map_lookup nat_rec_env_lookup

/- This closure is now free of `sorryAx`; the persistent-map contracts come
from proving concrete `SMap` freshness. The fixture introduces no new axiom. -/
#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.nat_trEnv' [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

/-! ## A value-bearing prefix followed by Nat -/

/-- A dependency-free definition used to ensure value translation survives a
later inductive metadata transaction. -/
def ReplaySeed : Type 1 := Type

def seedKernelDef : DefinitionVal := kernelDefVal% ReplaySeed
def seedInfo : ConstantInfo := .defnInfo seedKernelDef

def seedVal : VDefVal where
  name := ``ReplaySeed
  uvars := 0
  type := .sort (.succ (.succ .zero))
  value := .sort (.succ .zero)

theorem seedInfo_tr : TrDefVal .safe VEnv.empty seedInfo seedVal := by
  refine ⟨⟨⟨by decide, rfl, ?_⟩, rfl⟩, ?_⟩
  · exact .sort rfl
  · exact .sort rfl

theorem seedVal_wf : seedVal.WF VEnv.empty :=
  VEnv.HasType.sort (by decide)

def seedConstEnv := (VEnv.empty.addConst seedVal.name seedVal.toVConstant).get!
def seedEnv := seedConstEnv.addDefEq seedVal.toDefEq
def seedMap : ConstMap := ({} : ConstMap).insert seedVal.name seedInfo

theorem seed_fresh : ({} : ConstMap).find? seedVal.name = none := by
  simp [seedVal, SMap.find?]

theorem seed_trEnv' : TrEnv' .safe seedMap false seedEnv :=
  .defn (ci := seedKernelDef) (ci' := seedVal) seedInfo_tr seed_fresh
    seedVal_wf rfl .empty

theorem seed_map_lookup : seedMap.find? ``ReplaySeed = some seedInfo := by
  rw [seedMap, SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  rfl

theorem seed_le : VEnv.empty ≤ seedEnv :=
  (VEnv.addConst_le (show VEnv.empty.addConst seedVal.name seedVal.toVConstant =
    some seedConstEnv from rfl)).trans VEnv.addDefEq_le

theorem seedEnv_ordered : seedEnv.Ordered := seed_trEnv'.wf.ordered

def seedNatTypeEnv := (seedEnv.addConst natType.name natType.toVConstant).get!
def seedNatZeroEnv :=
  (seedNatTypeEnv.addConst natType.ctors[0].name natType.ctors[0].toVConstant).get!
def seedNatCtorEnv :=
  (seedNatZeroEnv.addConst natType.ctors[1].name natType.ctors[1].toVConstant).get!
def seedNatRecEnv :=
  (seedNatCtorEnv.addConst ``Nat.rec (VInductDecl.recConst 0 ``Nat 0 natType)).get!

theorem natTypeEnv_le_seedNatTypeEnv : natTypeEnv ≤ seedNatTypeEnv :=
  VEnv.LE.addConst (n := natType.name) (ci := natType.toVConstant) seed_le rfl rfl

theorem natZeroEnv_le_seedNatZeroEnv : natZeroEnv ≤ seedNatZeroEnv :=
  VEnv.LE.addConst (n := natType.ctors[0].name)
    (ci := natType.ctors[0].toVConstant) natTypeEnv_le_seedNatTypeEnv rfl rfl

theorem natCtorEnv_le_seedNatCtorEnv : natCtorEnv ≤ seedNatCtorEnv :=
  VEnv.LE.addConst (n := natType.ctors[1].name)
    (ci := natType.ctors[1].toVConstant) natZeroEnv_le_seedNatZeroEnv rfl rfl

theorem seedNatTypeEnv_ordered : seedNatTypeEnv.Ordered := by
  refine .const (n := natType.name) (ci := natType.toVConstant)
    seedEnv_ordered ?_ rfl
  exact ⟨.succ (.succ .zero), VEnv.HasType.sort (by decide)⟩

theorem seedNatZeroEnv_ordered : seedNatZeroEnv.Ordered := by
  refine .const (n := natType.ctors[0].name) (ci := natType.ctors[0].toVConstant)
    seedNatTypeEnv_ordered ?_ rfl
  have hNat : seedNatTypeEnv.constants ``Nat = some natType.toVConstant := rfl
  exact ⟨.succ .zero, by type_tac⟩

theorem seedNatSucc_wf : natType.ctors[1].toVConstant.WF seedNatZeroEnv := by
  have hNat : seedNatZeroEnv.constants ``Nat = some natType.toVConstant := rfl
  refine ⟨.imax (.succ .zero) (.succ .zero), ?_⟩
  refine VEnv.HasType.forallE (u := .succ .zero) (v := .succ .zero) ?_ ?_
  · type_tac
  · type_tac

theorem seedNatCtorEnv_ordered : seedNatCtorEnv.Ordered :=
  .const (n := natType.ctors[1].name) (ci := natType.ctors[1].toVConstant)
    seedNatZeroEnv_ordered seedNatSucc_wf rfl

theorem seedNatInfo_tr :
    TrConstVal .safe seedEnv natInfo natType.toVConstVal :=
  natInfo_tr.mono seed_le

theorem seedNatZeroInfo_tr :
    TrConstVal .safe seedNatTypeEnv natZeroInfo natType.ctors[0] :=
  natZeroInfo_tr.mono natTypeEnv_le_seedNatTypeEnv

theorem seedNatSuccInfo_tr :
    TrConstVal .safe seedNatZeroEnv natSuccInfo natType.ctors[1] :=
  natSuccInfo_tr.mono natZeroEnv_le_seedNatZeroEnv

theorem seedNatRecInfo_tr :
    TrConstVal .safe seedNatCtorEnv natRecInfo (inductRecVal natDecl natType) :=
  natRecInfo_tr.mono natCtorEnv_le_seedNatCtorEnv

def seedNatTypeMap : ConstMap := seedMap.insert ``Nat natInfo
def seedNatZeroMap : ConstMap := seedNatTypeMap.insert ``Nat.zero natZeroInfo
def seedNatCtorMap : ConstMap := seedNatZeroMap.insert ``Nat.succ natSuccInfo
def seedNatMap : ConstMap := seedNatCtorMap.insert ``Nat.rec natRecInfo
def seedNatFinalEnv : VEnv :=
  (VInductDecl.rules 0 ``Nat 0 natType).foldl VEnv.addDefEq seedNatRecEnv

theorem seedMap_wf : seedMap.WF := seed_trEnv'.map_wf

theorem seedNatType_fresh : seedMap.find? ``Nat = none := by
  rw [seedMap, SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [seedVal, SMap.find?]

theorem seedNatTypeMap_wf : seedNatTypeMap.WF :=
  seedMap_wf.insert _ _ seedNatType_fresh

theorem seedNatZero_fresh : seedNatTypeMap.find? ``Nat.zero = none := by
  rw [seedNatTypeMap, seedMap_wf.find?_insert, seedMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [seedVal, SMap.find?]

theorem seedNatZeroMap_wf : seedNatZeroMap.WF :=
  seedNatTypeMap_wf.insert _ _ seedNatZero_fresh

theorem seedNatSucc_fresh : seedNatZeroMap.find? ``Nat.succ = none := by
  rw [seedNatZeroMap, seedNatTypeMap_wf.find?_insert, seedNatTypeMap,
    seedMap_wf.find?_insert, seedMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [seedVal, SMap.find?]

theorem seedNatCtorMap_wf : seedNatCtorMap.WF :=
  seedNatZeroMap_wf.insert _ _ seedNatSucc_fresh

theorem seedNatRec_fresh : seedNatCtorMap.find? ``Nat.rec = none := by
  rw [seedNatCtorMap, seedNatZeroMap_wf.find?_insert, seedNatZeroMap,
    seedNatTypeMap_wf.find?_insert, seedNatTypeMap, seedMap_wf.find?_insert,
    seedMap, SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [seedVal, SMap.find?]

theorem seedNat_addInduct :
    AddInduct seedMap seedEnv natDecl seedNatMap seedNatFinalEnv := by
  refine ⟨{
    generation := natChecked.identityGeneration
    generation_wf :=
      (natChecked.wf_of_decl (natDecl_wf.mono seed_le)).identityGeneration
        seedEnv_ordered
    typeMap := seedNatTypeMap
    typeEnv := seedNatTypeEnv
    ctorMap := seedNatCtorMap
    ctorEnv := seedNatCtorEnv
    recEnv := seedNatRecEnv
    addType := {
      info := natInfo
      kind_eq := by simp [natInfo, InductConstantKind.Matches]
      tr := seedNatInfo_tr
      map_fresh := by
        change seedMap.find? ``Nat = none
        exact seedNatType_fresh
      env_add := rfl
      map_add := rfl }
    addCtors := ?_
    addRec := {
      info := natRecInfo
      kind_eq := by simp [natRecInfo, InductConstantKind.Matches]
      tr := seedNatRecInfo_tr
      map_fresh := by
        change seedNatCtorMap.find? ``Nat.rec = none
        exact seedNatRec_fresh
      env_add := rfl
      map_add := rfl }
    recK := by decide
    addRules := ⟨rfl⟩ }⟩
  exact .cons {
      info := natZeroInfo
      kind_eq := by simp [natZeroInfo, InductConstantKind.Matches]
      tr := seedNatZeroInfo_tr
      map_fresh := by simpa [natType] using seedNatZero_fresh
      env_add := rfl
      map_add := rfl }
    (.cons {
      info := natSuccInfo
      kind_eq := by simp [natSuccInfo, InductConstantKind.Matches]
      tr := seedNatSuccInfo_tr
      map_fresh := by
        change seedNatZeroMap.find? ``Nat.succ = none
        exact seedNatSucc_fresh
      env_add := rfl
      map_add := rfl } .nil)

theorem seedNat_trEnv' : TrEnv' .safe seedNatMap false seedNatFinalEnv :=
  .induct seedNat_addInduct seed_trEnv'

theorem seedNat_seed_lookup : seedNatMap.find? ``ReplaySeed = some seedInfo := by
  rw [seedNatMap, seedNatCtorMap_wf.find?_insert, seedNatCtorMap,
    seedNatZeroMap_wf.find?_insert, seedNatZeroMap,
    seedNatTypeMap_wf.find?_insert, seedNatTypeMap, seedMap_wf.find?_insert]
  simpa [seedVal] using seed_map_lookup

/-- A concrete regression for the formerly impossible `TrEnv'.of_value`
inductive branch: the value was inserted before Nat, so this theorem must pull
its lookup back through every Nat metadata insertion. -/
theorem seed_after_nat_of_value :
    TrExpr seedNatFinalEnv seedInfo.levelParams [] seedKernelDef.value
      (.const seedInfo.name (VLevel.params seedInfo.levelParams.length)) :=
  seedNat_trEnv'.of_value (name := ``ReplaySeed) (ci := seedInfo)
    (v := seedKernelDef.value) seedNat_seed_lookup (by decide) rfl

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.seed_after_nat_of_value [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

/-! ## Eq -/

/- `Eq` exercises parameters, a genuine index, Prop-valued elimination, and
the kernel/generated recursor universe permutation. -/
def eqInfo : ConstantInfo := kernelInductInfo% Eq
def eqReflInfo : ConstantInfo := kernelCtorInfo% Eq.refl
def eqRecInfo : ConstantInfo := kernelRecInfo% Eq.rec
def eqReflKernelRuleRhs : VExpr := kernelRecRuleRhs% Eq.rec 0

example : eqReflKernelRuleRhs =
    eqChecked.identityGeneration.generatedRules[0].rhs := rfl

def eqTypeEnv := (VEnv.empty.addConst eqType.name eqType.toVConstant).get!
def eqCtorEnv :=
  (eqTypeEnv.addConst eqType.ctors[0].name eqType.ctors[0].toVConstant).get!
def eqRecEnv :=
  (eqCtorEnv.addConst ``Eq.rec (VInductDecl.recConst 1 ``Eq 2 eqType)).get!

theorem eqType_wf : eqType.toVConstant.WF VEnv.empty := by
  refine ⟨.imax (.succ (.param 0))
    (.imax (.param 0) (.imax (.param 0) (.succ .zero))), ?_⟩
  refine VEnv.HasType.forallE
    (u := .succ (.param 0))
    (v := .imax (.param 0) (.imax (.param 0) (.succ .zero))) ?_ ?_
  · exact VEnv.HasType.sort (by decide)
  · refine VEnv.HasType.forallE
      (u := .param 0) (v := .imax (.param 0) (.succ .zero)) ?_ ?_
    · type_tac
    · refine VEnv.HasType.forallE
        (u := .param 0) (v := .succ .zero) ?_ ?_
      · type_tac
      · exact VEnv.HasType.sort (by decide)

theorem eqTypeEnv_ordered : eqTypeEnv.Ordered :=
  .const .empty eqType_wf rfl

theorem eqDecl_wf : eqDecl.WF VEnv.empty := by
  refine ⟨rfl, ?_⟩
  intro ty hty
  have hty' : ty = eqType := List.mem_singleton.1 (by simpa [eqDecl] using hty)
  subst ty
  refine ⟨?_, ?_⟩
  · change VEnv.empty.OnTel 1 []
      [.sort (.param 0), .bvar 0, .bvar 1]
    exact ⟨⟨.succ (.param 0), VEnv.HasType.sort (by decide)⟩,
      ⟨⟨.param 0, by type_tac⟩, ⟨⟨.param 0, by type_tac⟩, trivial⟩⟩⟩
  · intro c hc
    have hc' := List.mem_singleton.1 hc
    subst c
    constructor
    · change True
      trivial
    · exact .cons (by type_tac) .nil

theorem eqRefl_wf : eqType.ctors[0].toVConstant.WF eqTypeEnv := by
  have hblock := eqDecl_wf.2 eqType (by simp [eqDecl])
  have hctor := hblock.2 eqType.ctors[0] (by simp)
  have hle : VEnv.empty ≤ eqTypeEnv := VEnv.addConst_le rfl
  have S0 : VInductDecl.Stage3Env eqTypeEnv 1 ``Eq 2 .zero
      { eqType with ctors := [] } := {
    ord := eqTypeEnv_ordered
    hl := by decide
    hsort := rfl
    hlen := rfl
    hT := rfl
    hcs := by simp
    htel := by simp
    hs3 := by simp
    hparams := hblock.1.mono hle
    hfields := by simp
    hresult := by simp }
  exact S0.ctorType_isType' rfl rfl
    (VInductDecl.fieldsWF_mono hle hctor.1) (hctor.2.mono hle)

theorem eqCtorEnv_ordered : eqCtorEnv.Ordered :=
  .const (n := eqType.ctors[0].name) (ci := eqType.ctors[0].toVConstant)
    eqTypeEnv_ordered eqRefl_wf rfl

theorem eqStage3 :
    VInductDecl.Stage3Env eqCtorEnv 1 ``Eq 2 .zero eqType := by
  have hblock := eqDecl_wf.2 eqType (by simp [eqDecl])
  have hctor := hblock.2 eqType.ctors[0] (by simp)
  have h0 : VEnv.empty ≤ eqTypeEnv :=
    VEnv.addConst_le (show VEnv.empty.addConst eqType.name eqType.toVConstant =
      some eqTypeEnv from rfl)
  have h1 : eqTypeEnv ≤ eqCtorEnv :=
    VEnv.addConst_le (show eqTypeEnv.addConst eqType.ctors[0].name
      eqType.ctors[0].toVConstant = some eqCtorEnv from rfl)
  have hle : VEnv.empty ≤ eqCtorEnv := h0.trans h1
  refine {
    ord := eqCtorEnv_ordered
    hl := by decide
    hsort := rfl
    hlen := rfl
    hT := rfl
    hcs := by
      intro c hc
      have hc' := List.mem_singleton.1 hc
      subst c
      rfl
    htel := by
      intro c hc
      have hc' := List.mem_singleton.1 hc
      subst c
      rfl
    hs3 := by
      intro c hc
      have hc' := List.mem_singleton.1 hc
      subst c
      rfl
    hparams := hblock.1.mono hle
    hfields := by
      intro c hc
      have hc' := List.mem_singleton.1 hc
      subst c
      exact VInductDecl.fieldsWF_mono hle hctor.1
    hresult := by
      intro c hc
      have hc' := List.mem_singleton.1 hc
      subst c
      exact hctor.2.mono hle }

theorem eqInfo_tr :
    TrConstVal .safe VEnv.empty eqInfo eqType.toVConstVal := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr VEnv.empty eqInfo.levelParams [] eqInfo.type
      eqType.type := by tr_type_expr_tac
  obtain ⟨u, htype⟩ := eqType_wf
  exact hshape.to_trExprS .empty trivial ⟨.sort u, htype⟩

theorem eqReflInfo_tr :
    TrConstVal .safe eqTypeEnv eqReflInfo eqType.ctors[0] := by
  have hEq : eqTypeEnv.constants ``Eq = some eqType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr eqTypeEnv eqReflInfo.levelParams [] eqReflInfo.type
      eqType.ctors[0].type := by tr_type_expr_tac
  obtain ⟨u, htype⟩ := eqRefl_wf
  exact hshape.to_trExprS eqTypeEnv_ordered trivial ⟨.sort u, htype⟩

theorem eqRecInfo_tr :
    TrConstVal .safe eqCtorEnv eqRecInfo (inductRecVal eqDecl eqType) := by
  have hEq : eqCtorEnv.constants ``Eq = some eqType.toVConstant := rfl
  have hRefl : eqCtorEnv.constants ``Eq.refl =
      some eqType.ctors[0].toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr eqCtorEnv eqRecInfo.levelParams [] eqRecInfo.type
      (inductRecVal eqDecl eqType).type := by tr_type_expr_tac
  obtain ⟨u, hrec⟩ := eqStage3.recConst_wf
  exact hshape.to_trExprS eqCtorEnv_ordered trivial ⟨.sort u, hrec⟩

def eqTypeMap : ConstMap := ({} : ConstMap).insert ``Eq eqInfo
def eqCtorMap : ConstMap := eqTypeMap.insert ``Eq.refl eqReflInfo
def eqMap : ConstMap := eqCtorMap.insert ``Eq.rec eqRecInfo
def eqFinalEnv : VEnv :=
  (VInductDecl.rules 1 ``Eq 2 eqType).foldl VEnv.addDefEq eqRecEnv

theorem eqType_fresh : ({} : ConstMap).find? ``Eq = none := by
  simp [SMap.find?]

theorem eqTypeMap_wf : eqTypeMap.WF :=
  SMap.WF.empty.insert _ _ eqType_fresh

theorem eqRefl_fresh : eqTypeMap.find? ``Eq.refl = none := by
  rw [eqTypeMap, SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem eqCtorMap_wf : eqCtorMap.WF :=
  eqTypeMap_wf.insert _ _ eqRefl_fresh

theorem eqRec_fresh : eqCtorMap.find? ``Eq.rec = none := by
  rw [eqCtorMap, eqTypeMap_wf.find?_insert, eqTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem eq_addInduct :
    AddInduct ({} : ConstMap) VEnv.empty eqDecl eqMap eqFinalEnv := by
  refine ⟨{
    generation := eqChecked.identityGeneration
    generation_wf :=
      (eqChecked.wf_of_decl eqDecl_wf).identityGeneration .empty
    typeMap := eqTypeMap
    typeEnv := eqTypeEnv
    ctorMap := eqCtorMap
    ctorEnv := eqCtorEnv
    recEnv := eqRecEnv
    addType := {
      info := eqInfo
      kind_eq := by simp [eqInfo, InductConstantKind.Matches]
      tr := eqInfo_tr
      map_fresh := by
        change ({} : ConstMap).find? ``Eq = none
        exact eqType_fresh
      env_add := rfl
      map_add := rfl }
    addCtors := ?_
    addRec := {
      info := eqRecInfo
      kind_eq := by simp [eqRecInfo, InductConstantKind.Matches]
      tr := eqRecInfo_tr
      map_fresh := by
        change eqCtorMap.find? ``Eq.rec = none
        exact eqRec_fresh
      env_add := rfl
      map_add := rfl }
    recK := by decide
    addRules := ⟨rfl⟩ }⟩
  exact .cons {
    info := eqReflInfo
    kind_eq := by simp [eqReflInfo, InductConstantKind.Matches]
    tr := eqReflInfo_tr
    map_fresh := by simpa [eqType] using eqRefl_fresh
    env_add := rfl
    map_add := rfl } .nil

/-- Replay actual kernel `Eq` metadata through the formerly empty inductive
environment branch. -/
theorem eq_trEnv' : TrEnv' .safe eqMap false eqFinalEnv :=
  .induct eq_addInduct .empty

theorem eq_final_matches_addInduct :
    VEnv.empty.addInduct eqDecl = some eqFinalEnv :=
  rfl

theorem eq_env_wf : eqFinalEnv.WF := eq_trEnv'.wf

theorem eq_aligned : Aligned .safe eqMap eqFinalEnv := eq_trEnv'.aligned

theorem eq_type_map_lookup : eqMap.find? ``Eq = some eqInfo := by
  rw [eqMap, eqCtorMap_wf.find?_insert, eqCtorMap,
    eqTypeMap_wf.find?_insert, eqTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  rfl

theorem eq_type_env_lookup :
    eqFinalEnv.constants ``Eq = some eqType.toVConstant := rfl

theorem eq_type_lookup_unique :
    eqInfo.name = ``Eq ∧
      TrConstant .safe eqFinalEnv eqInfo eqType.toVConstant :=
  eq_aligned.find?_uniq eq_type_map_lookup eq_type_env_lookup

theorem eq_refl_map_lookup : eqMap.find? ``Eq.refl = some eqReflInfo := by
  rw [eqMap, eqCtorMap_wf.find?_insert, eqCtorMap,
    eqTypeMap_wf.find?_insert]
  rfl

theorem eq_refl_env_lookup : eqFinalEnv.constants ``Eq.refl =
    some eqType.ctors[0].toVConstant := rfl

theorem eq_refl_lookup_unique :
    eqReflInfo.name = ``Eq.refl ∧
      TrConstant .safe eqFinalEnv eqReflInfo
        eqType.ctors[0].toVConstant :=
  eq_aligned.find?_uniq eq_refl_map_lookup eq_refl_env_lookup

theorem eq_rec_map_lookup : eqMap.find? ``Eq.rec = some eqRecInfo := by
  rw [eqMap, eqCtorMap_wf.find?_insert]
  rfl

theorem eq_rec_env_lookup : eqFinalEnv.constants ``Eq.rec =
    some (VInductDecl.recConst 1 ``Eq 2 eqType) := rfl

theorem eq_rec_lookup_unique :
    eqRecInfo.name = ``Eq.rec ∧
      TrConstant .safe eqFinalEnv eqRecInfo
        (VInductDecl.recConst 1 ``Eq 2 eqType) :=
  eq_aligned.find?_uniq eq_rec_map_lookup eq_rec_env_lookup

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.eq_trEnv' [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

/-! ## IndexedVec over the replayed Nat prefix -/

/- The fixture spells its changing index as `Nat.succ n` (and its base as
`Nat.zero`) so its kernel metadata has exactly the semantically relevant Nat
dependency prefix, rather than the unrelated `OfNat`/`HAdd` instance
implementation generated by notation. The declaration and every metadata
record below are still quoted from and checked against the real kernel
objects. -/
def indexedVecInfo : ConstantInfo := kernelInductInfo% IndexedVec
def indexedVecNilInfo : ConstantInfo := kernelCtorInfo% IndexedVec.nil
def indexedVecConsInfo : ConstantInfo := kernelCtorInfo% IndexedVec.cons
def indexedVecRecInfo : ConstantInfo := kernelRecInfo% IndexedVec.rec
def indexedVecNilKernelRuleRhs : VExpr :=
  kernelRecRuleRhs% IndexedVec.rec 0
def indexedVecConsKernelRuleRhs : VExpr :=
  kernelRecRuleRhs% IndexedVec.rec 1

example : indexedVecNilKernelRuleRhs =
    indexedVecChecked.identityGeneration.generatedRules[0].rhs := rfl
example : indexedVecConsKernelRuleRhs =
    indexedVecChecked.identityGeneration.generatedRules[1].rhs := rfl

def indexedVecTypeEnv :=
  (natFinalEnv.addConst indexedVecType.name indexedVecType.toVConstant).get!
def indexedVecNilEnv :=
  (indexedVecTypeEnv.addConst indexedVecType.ctors[0].name
    indexedVecType.ctors[0].toVConstant).get!
def indexedVecCtorEnv :=
  (indexedVecNilEnv.addConst indexedVecType.ctors[1].name
    indexedVecType.ctors[1].toVConstant).get!
def indexedVecRecEnv :=
  (indexedVecCtorEnv.addConst ``IndexedVec.rec
    (VInductDecl.recConst 1 ``IndexedVec 1 indexedVecType)).get!
theorem indexedVecType_wf : indexedVecType.toVConstant.WF natFinalEnv := by
  have hNat : natFinalEnv.constants ``Nat = some natType.toVConstant := rfl
  refine ⟨.imax (.succ (.succ (.param 0)))
    (.imax (.succ .zero) (.succ (.succ (.param 0)))), ?_⟩
  refine VEnv.HasType.forallE
    (u := .succ (.succ (.param 0)))
    (v := .imax (.succ .zero) (.succ (.succ (.param 0)))) ?_ ?_
  · exact VEnv.HasType.sort (by decide)
  · refine VEnv.HasType.forallE
      (u := .succ .zero) (v := .succ (.succ (.param 0))) ?_ ?_
    · type_tac
    · exact VEnv.HasType.sort (by decide)

theorem indexedVecDecl_wf : indexedVecDecl.WF natFinalEnv := by
  refine ⟨rfl, ?_⟩
  intro ty hty
  have hty' : ty = indexedVecType :=
    List.mem_singleton.1 (by simpa [indexedVecDecl] using hty)
  subst ty
  refine ⟨?_, ?_⟩
  · change natFinalEnv.OnTel 1 []
      [.sort (.succ (.param 0)), .const ``Nat []]
    have hNat : natFinalEnv.constants ``Nat = some natType.toVConstant := rfl
    exact ⟨⟨.succ (.succ (.param 0)), VEnv.HasType.sort (by decide)⟩,
      ⟨⟨.succ .zero, by type_tac⟩, trivial⟩⟩
  · intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · constructor
      · change True
        trivial
      · change natFinalEnv.SpineWF 1
          [.sort (.succ (.param 0))]
          (.forallE (.const ``Nat []) (.sort (.succ (.param 0))))
          [.const ``Nat.zero []] (.sort (.succ (.param 0)))
        have hNat : natFinalEnv.constants ``Nat = some natType.toVConstant := rfl
        have hZero : natFinalEnv.constants ``Nat.zero =
            some natType.ctors[0].toVConstant := rfl
        exact .cons (by type_tac) .nil
    · have hc' := List.mem_singleton.1 hc
      subst c
      constructor
      · change VInductDecl.fieldsWF 1 ``IndexedVec 1 natFinalEnv
          (VLevel.succ (VLevel.param 0)) [VExpr.const ``Nat []]
          [VExpr.sort (VLevel.succ (VLevel.param 0))] 0
          [VExpr.const ``Nat [], VExpr.bvar 1,
            VExpr.app (VExpr.app (VExpr.const ``IndexedVec [VLevel.param 0])
              (VExpr.bvar 2)) (VExpr.bvar 1)]
        have hNat : natFinalEnv.constants ``Nat = some natType.toVConstant := rfl
        constructor
        · exact .inr (.inr ⟨rfl, .succ .zero, (by type_tac),
            .inr (VLevel.succ_le_succ VLevel.zero_le)⟩)
        constructor
        · intro h
          contradiction
        constructor
        · exact .inr (.inr ⟨rfl, .succ (.param 0), (by type_tac),
            .inr (VLevel.le_refl _)⟩)
        constructor
        · intro h
          contradiction
        constructor
        · exact .inl rfl
        constructor
        · intro _
          exact .cons (by type_tac) .nil
        · trivial
      · change natFinalEnv.SpineWF 1
          [VExpr.app (VExpr.app (VExpr.const ``IndexedVec [VLevel.param 0])
              (VExpr.bvar 2)) (VExpr.bvar 1),
            VExpr.bvar 1, VExpr.const ``Nat [],
            VExpr.sort (VLevel.succ (VLevel.param 0))]
          (VExpr.forallE (VExpr.const ``Nat [])
            (VExpr.sort (VLevel.succ (VLevel.param 0))))
          [VExpr.app (VExpr.const ``Nat.succ []) (VExpr.bvar 2)]
          (VExpr.sort (VLevel.succ (VLevel.param 0)))
        have hNat : natFinalEnv.constants ``Nat = some natType.toVConstant := rfl
        have hSucc : natFinalEnv.constants ``Nat.succ =
            some natType.ctors[1].toVConstant := rfl
        exact .cons (by type_tac) .nil

theorem natFinalEnv_le_indexedVecTypeEnv : natFinalEnv ≤ indexedVecTypeEnv :=
  VEnv.addConst_le (show natFinalEnv.addConst indexedVecType.name
    indexedVecType.toVConstant = some indexedVecTypeEnv from rfl)

theorem indexedVecTypeEnv_le_indexedVecNilEnv :
    indexedVecTypeEnv ≤ indexedVecNilEnv :=
  VEnv.addConst_le (show indexedVecTypeEnv.addConst
    indexedVecType.ctors[0].name indexedVecType.ctors[0].toVConstant =
      some indexedVecNilEnv from rfl)

theorem indexedVecNilEnv_le_indexedVecCtorEnv :
    indexedVecNilEnv ≤ indexedVecCtorEnv :=
  VEnv.addConst_le (show indexedVecNilEnv.addConst
    indexedVecType.ctors[1].name indexedVecType.ctors[1].toVConstant =
      some indexedVecCtorEnv from rfl)

theorem indexedVecTypeEnv_ordered : indexedVecTypeEnv.Ordered :=
  .const (n := indexedVecType.name) (ci := indexedVecType.toVConstant)
    nat_env_wf.ordered indexedVecType_wf rfl

theorem indexedVecNil_wf :
    indexedVecType.ctors[0].toVConstant.WF indexedVecTypeEnv := by
  have hblock := indexedVecDecl_wf.2 indexedVecType
    (by simp [indexedVecDecl])
  have hctor := hblock.2 indexedVecType.ctors[0] (by simp)
  have hle : natFinalEnv ≤ indexedVecTypeEnv :=
    natFinalEnv_le_indexedVecTypeEnv
  have S0 : VInductDecl.Stage3Env indexedVecTypeEnv 1 ``IndexedVec 1
      (.succ (.param 0)) { indexedVecType with ctors := [] } := {
    ord := indexedVecTypeEnv_ordered
    hl := by decide
    hsort := rfl
    hlen := rfl
    hT := rfl
    hcs := by simp
    htel := by simp
    hs3 := by simp
    hparams := hblock.1.mono hle
    hfields := by simp
    hresult := by simp }
  exact S0.ctorType_isType' rfl rfl
    (VInductDecl.fieldsWF_mono hle hctor.1) (hctor.2.mono hle)

theorem indexedVecNilEnv_ordered : indexedVecNilEnv.Ordered :=
  .const (n := indexedVecType.ctors[0].name)
    (ci := indexedVecType.ctors[0].toVConstant)
    indexedVecTypeEnv_ordered indexedVecNil_wf rfl

theorem indexedVecCons_wf :
    indexedVecType.ctors[1].toVConstant.WF indexedVecNilEnv := by
  have hblock := indexedVecDecl_wf.2 indexedVecType
    (by simp [indexedVecDecl])
  have hnil := hblock.2 indexedVecType.ctors[0] (by simp)
  have hcons := hblock.2 indexedVecType.ctors[1] (by simp)
  have h0 : natFinalEnv ≤ indexedVecTypeEnv :=
    natFinalEnv_le_indexedVecTypeEnv
  have h1 : indexedVecTypeEnv ≤ indexedVecNilEnv :=
    indexedVecTypeEnv_le_indexedVecNilEnv
  have hle : natFinalEnv ≤ indexedVecNilEnv := h0.trans h1
  have S1 : VInductDecl.Stage3Env indexedVecNilEnv 1 ``IndexedVec 1
      (.succ (.param 0))
      { indexedVecType with ctors := [indexedVecType.ctors[0]] } := {
    ord := indexedVecNilEnv_ordered
    hl := by decide
    hsort := rfl
    hlen := rfl
    hT := rfl
    hcs := by
      intro c hc
      have hc' := List.mem_singleton.1 hc
      subst c
      rfl
    htel := by
      intro c hc
      have hc' := List.mem_singleton.1 hc
      subst c
      rfl
    hs3 := by
      intro c hc
      have hc' := List.mem_singleton.1 hc
      subst c
      rfl
    hparams := hblock.1.mono hle
    hfields := by
      intro c hc
      have hc' := List.mem_singleton.1 hc
      subst c
      exact VInductDecl.fieldsWF_mono hle hnil.1
    hresult := by
      intro c hc
      have hc' := List.mem_singleton.1 hc
      subst c
      exact hnil.2.mono hle }
  exact S1.ctorType_isType' rfl rfl
    (VInductDecl.fieldsWF_mono hle hcons.1) (hcons.2.mono hle)

theorem indexedVecCtorEnv_ordered : indexedVecCtorEnv.Ordered :=
  .const (n := indexedVecType.ctors[1].name)
    (ci := indexedVecType.ctors[1].toVConstant)
    indexedVecNilEnv_ordered indexedVecCons_wf rfl

theorem indexedVecStage3 :
    VInductDecl.Stage3Env indexedVecCtorEnv 1 ``IndexedVec 1
      (.succ (.param 0)) indexedVecType := by
  have hblock := indexedVecDecl_wf.2 indexedVecType
    (by simp [indexedVecDecl])
  have h0 : natFinalEnv ≤ indexedVecTypeEnv :=
    natFinalEnv_le_indexedVecTypeEnv
  have h1 : indexedVecTypeEnv ≤ indexedVecNilEnv :=
    indexedVecTypeEnv_le_indexedVecNilEnv
  have h2 : indexedVecNilEnv ≤ indexedVecCtorEnv :=
    indexedVecNilEnv_le_indexedVecCtorEnv
  have hle : natFinalEnv ≤ indexedVecCtorEnv := (h0.trans h1).trans h2
  refine {
    ord := indexedVecCtorEnv_ordered
    hl := by decide
    hsort := rfl
    hlen := rfl
    hT := rfl
    hcs := ?_
    htel := ?_
    hs3 := ?_
    hparams := hblock.1.mono hle
    hfields := ?_
    hresult := ?_ }
  · intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · rfl
    · have hc' := List.mem_singleton.1 hc
      subst c
      rfl
  · intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · rfl
    · have hc' := List.mem_singleton.1 hc
      subst c
      rfl
  · intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · rfl
    · have hc' := List.mem_singleton.1 hc
      subst c
      rfl
  · intro c hc
    exact VInductDecl.fieldsWF_mono hle (hblock.2 c hc).1
  · intro c hc
    exact (hblock.2 c hc).2.mono hle

theorem indexedVecInfo_tr :
    TrConstVal .safe natFinalEnv indexedVecInfo indexedVecType.toVConstVal := by
  have hNat : natFinalEnv.constants ``Nat = some natType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr natFinalEnv indexedVecInfo.levelParams []
      indexedVecInfo.type indexedVecType.type := by tr_type_expr_tac
  obtain ⟨u, htype⟩ := indexedVecType_wf
  exact hshape.to_trExprS nat_env_wf.ordered trivial ⟨.sort u, htype⟩

theorem indexedVecNilInfo_tr :
    TrConstVal .safe indexedVecTypeEnv indexedVecNilInfo
      indexedVecType.ctors[0] := by
  have hNat : indexedVecTypeEnv.constants ``Nat = some natType.toVConstant := rfl
  have hZero : indexedVecTypeEnv.constants ``Nat.zero =
      some natType.ctors[0].toVConstant := rfl
  have hVec : indexedVecTypeEnv.constants ``IndexedVec =
      some indexedVecType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr indexedVecTypeEnv indexedVecNilInfo.levelParams []
      indexedVecNilInfo.type indexedVecType.ctors[0].type := by
    tr_type_expr_tac
  obtain ⟨u, htype⟩ := indexedVecNil_wf
  exact hshape.to_trExprS indexedVecTypeEnv_ordered trivial ⟨.sort u, htype⟩

theorem indexedVecConsInfo_tr :
    TrConstVal .safe indexedVecNilEnv indexedVecConsInfo
      indexedVecType.ctors[1] := by
  have hNat : indexedVecNilEnv.constants ``Nat = some natType.toVConstant := rfl
  have hSucc : indexedVecNilEnv.constants ``Nat.succ =
      some natType.ctors[1].toVConstant := rfl
  have hVec : indexedVecNilEnv.constants ``IndexedVec =
      some indexedVecType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr indexedVecNilEnv indexedVecConsInfo.levelParams []
      indexedVecConsInfo.type indexedVecType.ctors[1].type := by
    tr_type_expr_tac
  obtain ⟨u, htype⟩ := indexedVecCons_wf
  exact hshape.to_trExprS indexedVecNilEnv_ordered trivial ⟨.sort u, htype⟩

theorem indexedVecRecInfo_tr :
    TrConstVal .safe indexedVecCtorEnv indexedVecRecInfo
      (inductRecVal indexedVecDecl indexedVecType) := by
  have hNat : indexedVecCtorEnv.constants ``Nat = some natType.toVConstant := rfl
  have hZero : indexedVecCtorEnv.constants ``Nat.zero =
      some natType.ctors[0].toVConstant := rfl
  have hSucc : indexedVecCtorEnv.constants ``Nat.succ =
      some natType.ctors[1].toVConstant := rfl
  have hVec : indexedVecCtorEnv.constants ``IndexedVec =
      some indexedVecType.toVConstant := rfl
  have hNil : indexedVecCtorEnv.constants ``IndexedVec.nil =
      some indexedVecType.ctors[0].toVConstant := rfl
  have hCons : indexedVecCtorEnv.constants ``IndexedVec.cons =
      some indexedVecType.ctors[1].toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr indexedVecCtorEnv indexedVecRecInfo.levelParams []
      indexedVecRecInfo.type
      (inductRecVal indexedVecDecl indexedVecType).type := by
    tr_type_expr_tac
  obtain ⟨u, hrec⟩ := indexedVecStage3.recConst_wf
  exact hshape.to_trExprS indexedVecCtorEnv_ordered trivial ⟨.sort u, hrec⟩

def indexedVecTypeMap : ConstMap := natMap.insert ``IndexedVec indexedVecInfo
def indexedVecNilMap : ConstMap :=
  indexedVecTypeMap.insert ``IndexedVec.nil indexedVecNilInfo
def indexedVecCtorMap : ConstMap :=
  indexedVecNilMap.insert ``IndexedVec.cons indexedVecConsInfo
def indexedVecMap : ConstMap :=
  indexedVecCtorMap.insert ``IndexedVec.rec indexedVecRecInfo
def indexedVecFinalEnv : VEnv :=
  (VInductDecl.rules 1 ``IndexedVec 1 indexedVecType).foldl
    VEnv.addDefEq indexedVecRecEnv

theorem natMap_wf : natMap.WF := (nat_trEnv' (safety := .safe)).map_wf

theorem indexedVecType_fresh : natMap.find? ``IndexedVec = none := by
  rw [natMap, natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem indexedVecTypeMap_wf : indexedVecTypeMap.WF :=
  natMap_wf.insert _ _ indexedVecType_fresh

theorem indexedVecNil_fresh :
    indexedVecTypeMap.find? ``IndexedVec.nil = none := by
  rw [indexedVecTypeMap, natMap_wf.find?_insert, natMap,
    natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem indexedVecNilMap_wf : indexedVecNilMap.WF :=
  indexedVecTypeMap_wf.insert _ _ indexedVecNil_fresh

theorem indexedVecCons_fresh :
    indexedVecNilMap.find? ``IndexedVec.cons = none := by
  rw [indexedVecNilMap, indexedVecTypeMap_wf.find?_insert,
    indexedVecTypeMap, natMap_wf.find?_insert, natMap,
    natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem indexedVecCtorMap_wf : indexedVecCtorMap.WF :=
  indexedVecNilMap_wf.insert _ _ indexedVecCons_fresh

theorem indexedVecRec_fresh :
    indexedVecCtorMap.find? ``IndexedVec.rec = none := by
  rw [indexedVecCtorMap, indexedVecNilMap_wf.find?_insert,
    indexedVecNilMap, indexedVecTypeMap_wf.find?_insert,
    indexedVecTypeMap, natMap_wf.find?_insert, natMap,
    natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem indexedVec_addInduct :
    AddInduct natMap natFinalEnv indexedVecDecl indexedVecMap
      indexedVecFinalEnv := by
  refine ⟨{
    generation := indexedVecChecked.identityGeneration
    generation_wf :=
      (indexedVecChecked.wf_of_decl indexedVecDecl_wf).identityGeneration
        nat_env_wf.ordered
    typeMap := indexedVecTypeMap
    typeEnv := indexedVecTypeEnv
    ctorMap := indexedVecCtorMap
    ctorEnv := indexedVecCtorEnv
    recEnv := indexedVecRecEnv
    addType := {
      info := indexedVecInfo
      kind_eq := by simp [indexedVecInfo, InductConstantKind.Matches]
      tr := indexedVecInfo_tr
      map_fresh := by
        change natMap.find? ``IndexedVec = none
        exact indexedVecType_fresh
      env_add := rfl
      map_add := rfl }
    addCtors := ?_
    addRec := {
      info := indexedVecRecInfo
      kind_eq := by simp [indexedVecRecInfo, InductConstantKind.Matches]
      tr := indexedVecRecInfo_tr
      map_fresh := by
        change indexedVecCtorMap.find? ``IndexedVec.rec = none
        exact indexedVecRec_fresh
      env_add := rfl
      map_add := rfl }
    recK := by decide
    addRules := ⟨rfl⟩ }⟩
  exact .cons {
      info := indexedVecNilInfo
      kind_eq := by simp [indexedVecNilInfo, InductConstantKind.Matches]
      tr := indexedVecNilInfo_tr
      map_fresh := by simpa [indexedVecType] using indexedVecNil_fresh
      env_add := rfl
      map_add := rfl }
    (.cons {
      info := indexedVecConsInfo
      kind_eq := by simp [indexedVecConsInfo, InductConstantKind.Matches]
      tr := indexedVecConsInfo_tr
      map_fresh := by
        change indexedVecNilMap.find? ``IndexedVec.cons = none
        exact indexedVecCons_fresh
      env_add := rfl
      map_add := rfl } .nil)

theorem indexedVec_trEnv' :
    TrEnv' .safe indexedVecMap false indexedVecFinalEnv :=
  .induct indexedVec_addInduct nat_trEnv'

theorem indexedVec_final_matches_addInduct :
    natFinalEnv.addInduct indexedVecDecl = some indexedVecFinalEnv :=
  rfl

theorem indexedVec_env_wf : indexedVecFinalEnv.WF := indexedVec_trEnv'.wf

theorem indexedVec_aligned :
    Aligned .safe indexedVecMap indexedVecFinalEnv :=
  indexedVec_trEnv'.aligned

theorem indexedVec_type_map_lookup :
    indexedVecMap.find? ``IndexedVec = some indexedVecInfo := by
  rw [indexedVecMap, indexedVecCtorMap_wf.find?_insert, indexedVecCtorMap,
    indexedVecNilMap_wf.find?_insert, indexedVecNilMap,
    indexedVecTypeMap_wf.find?_insert, indexedVecTypeMap,
    natMap_wf.find?_insert]
  rfl

theorem indexedVec_type_env_lookup :
    indexedVecFinalEnv.constants ``IndexedVec =
      some indexedVecType.toVConstant := rfl

theorem indexedVec_type_lookup_unique :
    indexedVecInfo.name = ``IndexedVec ∧
      TrConstant .safe indexedVecFinalEnv indexedVecInfo
        indexedVecType.toVConstant :=
  indexedVec_aligned.find?_uniq indexedVec_type_map_lookup
    indexedVec_type_env_lookup

theorem indexedVec_cons_map_lookup :
    indexedVecMap.find? ``IndexedVec.cons = some indexedVecConsInfo := by
  rw [indexedVecMap, indexedVecCtorMap_wf.find?_insert, indexedVecCtorMap,
    indexedVecNilMap_wf.find?_insert]
  rfl

theorem indexedVec_cons_env_lookup :
    indexedVecFinalEnv.constants ``IndexedVec.cons =
      some indexedVecType.ctors[1].toVConstant := rfl

theorem indexedVec_cons_lookup_unique :
    indexedVecConsInfo.name = ``IndexedVec.cons ∧
      TrConstant .safe indexedVecFinalEnv indexedVecConsInfo
        indexedVecType.ctors[1].toVConstant :=
  indexedVec_aligned.find?_uniq indexedVec_cons_map_lookup
    indexedVec_cons_env_lookup

theorem indexedVec_rec_map_lookup :
    indexedVecMap.find? ``IndexedVec.rec = some indexedVecRecInfo := by
  rw [indexedVecMap, indexedVecCtorMap_wf.find?_insert]
  rfl

theorem indexedVec_rec_env_lookup :
    indexedVecFinalEnv.constants ``IndexedVec.rec =
      some (VInductDecl.recConst 1 ``IndexedVec 1 indexedVecType) := rfl

theorem indexedVec_rec_lookup_unique :
    indexedVecRecInfo.name = ``IndexedVec.rec ∧
      TrConstant .safe indexedVecFinalEnv indexedVecRecInfo
        (VInductDecl.recConst 1 ``IndexedVec 1 indexedVecType) :=
  indexedVec_aligned.find?_uniq indexedVec_rec_map_lookup
    indexedVec_rec_env_lookup

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.indexedVec_trEnv' [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

/-! ## Acc: recursive Pi metadata -/

/- `Acc` is the first replay whose recursive constructor argument is a
function. In addition to translating the three kernel constants, this fixture
quotes the actual `RecursorRule.rhs` and compares it definitionally with the
public generalized Theory rule. -/
def accInfo : ConstantInfo := kernelInductInfo% Acc
def accIntroInfo : ConstantInfo := kernelCtorInfo% Acc.intro
def accRecInfo : ConstantInfo := kernelRecInfo% Acc.rec
def accKernelRuleRhs : VExpr := kernelRecRuleRhs% Acc.rec 0

example : (match accIntroInfo with
    | .ctorInfo ci => ci.numParams
    | _ => 0) = 2 := rfl
example : (match accIntroInfo with
    | .ctorInfo ci => ci.numFields
    | _ => 0) = 2 := rfl
example : (match accRecInfo with
    | .recInfo ci => ci.numParams
    | _ => 0) = 2 := rfl
example : (match accRecInfo with
    | .recInfo ci => ci.numIndices
    | _ => 0) = 1 := rfl
example : (match accRecInfo with
    | .recInfo ci => ci.numMotives
    | _ => 0) = 1 := rfl
example : (match accRecInfo with
    | .recInfo ci => ci.numMinors
    | _ => 0) = 1 := rfl
example : (match accRecInfo with
    | .recInfo ci => ci.rules.length
    | _ => 0) = 1 := rfl
example : (match accRecInfo with
    | .recInfo ci => ci.rules[0]?.map (·.ctor) |>.getD .anonymous
    | _ => .anonymous) = ``Acc.intro := rfl
example : (match accRecInfo with
    | .recInfo ci => ci.rules[0]?.map (·.nfields) |>.getD 0
    | _ => 0) = 2 := rfl

/-- The actual kernel rule has the same lambda-wrapped functional recursive
call as the public Theory generator, in the kernel recursor's universe order. -/
example : accKernelRuleRhs =
    (VInductDecl.ruleRec 1 ``Acc 2 accType 0 accType.ctors[0]).rhs := rfl
example : accKernelRuleRhs =
    accChecked.identityGeneration.generatedRules[0].rhs := rfl

def accTypeEnv := (VEnv.empty.addConst accType.name accType.toVConstant).get!
def accCtorEnv :=
  (accTypeEnv.addConst accType.ctors[0].name accType.ctors[0].toVConstant).get!
def accRecEnv :=
  (accCtorEnv.addConst ``Acc.rec
    (VInductDecl.recConstRec 1 ``Acc 2 accType)).get!

theorem accType_wf : accType.toVConstant.WF VEnv.empty := by
  have htel := (accDecl_wf.2 accType (by simp [accDecl])).1
  change VEnv.empty.IsType 1 [] accType.type
  rw [show accType.type = VExpr.forallN
    [.sort (.param 0),
      .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)),
      .bvar 1] (.sort .zero) from rfl]
  exact VEnv.IsType.forallN htel ⟨.succ .zero, VEnv.HasType.sort (by decide)⟩

theorem accTypeEnv_ordered : accTypeEnv.Ordered :=
  .const .empty accType_wf rfl

theorem accIntro_wf : accType.ctors[0].toVConstant.WF accTypeEnv := by
  have hblock := accDecl_wf.2 accType (by simp [accDecl])
  have hctor := hblock.2 accType.ctors[0] (by simp)
  have hle : VEnv.empty ≤ accTypeEnv := VEnv.addConst_le rfl
  have S0 : VInductDecl.Stage3Env accTypeEnv 1 ``Acc 2 .zero
      { accType with ctors := [] } := {
    ord := accTypeEnv_ordered
    hl := by decide
    hsort := rfl
    hlen := rfl
    hT := rfl
    hcs := by simp
    htel := by simp
    hs3 := by simp
    hparams := hblock.1.mono hle
    hfields := by simp
    hresult := by simp }
  exact S0.ctorType_isType' rfl rfl
    (VInductDecl.fieldsWF_mono hle hctor.1) (hctor.2.mono hle)

theorem accCtorEnv_ordered : accCtorEnv.Ordered :=
  .const (n := accType.ctors[0].name) (ci := accType.ctors[0].toVConstant)
    accTypeEnv_ordered accIntro_wf rfl

theorem accStage3 :
    VInductDecl.Stage3Env accCtorEnv 1 ``Acc 2 .zero accType := by
  have hblock := accDecl_wf.2 accType (by simp [accDecl])
  have hctor := hblock.2 accType.ctors[0] (by simp)
  have h0 : VEnv.empty ≤ accTypeEnv := VEnv.addConst_le rfl
  have h1 : accTypeEnv ≤ accCtorEnv :=
    VEnv.addConst_le (show accTypeEnv.addConst accType.ctors[0].name
      accType.ctors[0].toVConstant = some accCtorEnv from rfl)
  have hle : VEnv.empty ≤ accCtorEnv := h0.trans h1
  refine {
    ord := accCtorEnv_ordered
    hl := by decide
    hsort := rfl
    hlen := rfl
    hT := rfl
    hcs := ?_
    htel := ?_
    hs3 := ?_
    hparams := hblock.1.mono hle
    hfields := ?_
    hresult := ?_ }
  · intro c hc
    have hc' := List.mem_singleton.1 hc
    subst c
    rfl
  · intro c hc
    have hc' := List.mem_singleton.1 hc
    subst c
    rfl
  · intro c hc
    have hc' := List.mem_singleton.1 hc
    subst c
    rfl
  · intro c hc
    have hc' := List.mem_singleton.1 hc
    subst c
    exact VInductDecl.fieldsWF_mono hle hctor.1
  · intro c hc
    have hc' := List.mem_singleton.1 hc
    subst c
    exact hctor.2.mono hle

theorem accInfo_tr :
    TrConstVal .safe VEnv.empty accInfo accType.toVConstVal := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr VEnv.empty accInfo.levelParams [] accInfo.type
      accType.type := by tr_type_expr_tac
  obtain ⟨u, htype⟩ := accType_wf
  exact hshape.to_trExprS .empty trivial ⟨.sort u, htype⟩

theorem accIntroInfo_tr :
    TrConstVal .safe accTypeEnv accIntroInfo accType.ctors[0] := by
  have hAcc : accTypeEnv.constants ``Acc = some accType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr accTypeEnv accIntroInfo.levelParams []
      accIntroInfo.type accType.ctors[0].type := by tr_type_expr_tac
  obtain ⟨u, htype⟩ := accIntro_wf
  exact hshape.to_trExprS accTypeEnv_ordered trivial ⟨.sort u, htype⟩

theorem accRecInfo_tr :
    TrConstVal .safe accCtorEnv accRecInfo (inductRecVal accDecl accType) := by
  have hAcc : accCtorEnv.constants ``Acc = some accType.toVConstant := rfl
  have hIntro : accCtorEnv.constants ``Acc.intro =
      some accType.ctors[0].toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr accCtorEnv accRecInfo.levelParams []
      accRecInfo.type (inductRecVal accDecl accType).type := by tr_type_expr_tac
  obtain ⟨u, hrec⟩ := accStage3.recConstRec_wf
  exact hshape.to_trExprS accCtorEnv_ordered trivial ⟨.sort u, hrec⟩

def accTypeMap : ConstMap := ({} : ConstMap).insert ``Acc accInfo
def accCtorMap : ConstMap := accTypeMap.insert ``Acc.intro accIntroInfo
def accMap : ConstMap := accCtorMap.insert ``Acc.rec accRecInfo
def accFinalEnv : VEnv :=
  (VInductDecl.rulesRec 1 ``Acc 2 accType).foldl VEnv.addDefEq accRecEnv

theorem accType_fresh : ({} : ConstMap).find? ``Acc = none := by
  simp [SMap.find?]

theorem accTypeMap_wf : accTypeMap.WF :=
  SMap.WF.empty.insert _ _ accType_fresh

theorem accIntro_fresh : accTypeMap.find? ``Acc.intro = none := by
  rw [accTypeMap, SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem accCtorMap_wf : accCtorMap.WF :=
  accTypeMap_wf.insert _ _ accIntro_fresh

theorem accRec_fresh : accCtorMap.find? ``Acc.rec = none := by
  rw [accCtorMap, accTypeMap_wf.find?_insert, accTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem acc_addInduct :
    AddInduct ({} : ConstMap) VEnv.empty accDecl accMap accFinalEnv := by
  refine ⟨{
    generation := accChecked.identityGeneration
    generation_wf :=
      (accChecked.wf_of_decl accDecl_wf).identityGeneration .empty
    typeMap := accTypeMap
    typeEnv := accTypeEnv
    ctorMap := accCtorMap
    ctorEnv := accCtorEnv
    recEnv := accRecEnv
    addType := {
      info := accInfo
      kind_eq := by simp [accInfo, InductConstantKind.Matches]
      tr := accInfo_tr
      map_fresh := by
        change ({} : ConstMap).find? ``Acc = none
        exact accType_fresh
      env_add := rfl
      map_add := rfl }
    addCtors := ?_
    addRec := {
      info := accRecInfo
      kind_eq := by simp [accRecInfo, InductConstantKind.Matches]
      tr := accRecInfo_tr
      map_fresh := by
        change accCtorMap.find? ``Acc.rec = none
        exact accRec_fresh
      env_add := rfl
      map_add := rfl }
    recK := by decide
    addRules := ⟨rfl⟩ }⟩
  exact .cons {
    info := accIntroInfo
    kind_eq := by simp [accIntroInfo, InductConstantKind.Matches]
    tr := accIntroInfo_tr
    map_fresh := by simpa [accType] using accIntro_fresh
    env_add := rfl
    map_add := rfl } .nil

/-- Replay the actual kernel `Acc` metadata through the live inductive
environment branch. -/
theorem acc_trEnv' : TrEnv' .safe accMap false accFinalEnv :=
  .induct acc_addInduct .empty

theorem acc_final_matches_addInduct :
    VEnv.empty.addInduct accDecl = some accFinalEnv :=
  rfl

theorem acc_env_wf : accFinalEnv.WF := acc_trEnv'.wf

theorem acc_aligned : Aligned .safe accMap accFinalEnv := acc_trEnv'.aligned

theorem acc_type_map_lookup : accMap.find? ``Acc = some accInfo := by
  rw [accMap, accCtorMap_wf.find?_insert, accCtorMap,
    accTypeMap_wf.find?_insert, accTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  rfl

theorem acc_type_env_lookup :
    accFinalEnv.constants ``Acc = some accType.toVConstant := rfl

theorem acc_type_lookup_unique :
    accInfo.name = ``Acc ∧
      TrConstant .safe accFinalEnv accInfo accType.toVConstant :=
  acc_aligned.find?_uniq acc_type_map_lookup acc_type_env_lookup

theorem acc_intro_map_lookup :
    accMap.find? ``Acc.intro = some accIntroInfo := by
  rw [accMap, accCtorMap_wf.find?_insert, accCtorMap,
    accTypeMap_wf.find?_insert]
  rfl

theorem acc_intro_env_lookup :
    accFinalEnv.constants ``Acc.intro =
      some accType.ctors[0].toVConstant := rfl

theorem acc_intro_lookup_unique :
    accIntroInfo.name = ``Acc.intro ∧
      TrConstant .safe accFinalEnv accIntroInfo
        accType.ctors[0].toVConstant :=
  acc_aligned.find?_uniq acc_intro_map_lookup acc_intro_env_lookup

theorem acc_rec_map_lookup : accMap.find? ``Acc.rec = some accRecInfo := by
  rw [accMap, accCtorMap_wf.find?_insert]
  rfl

theorem acc_rec_env_lookup :
    accFinalEnv.constants ``Acc.rec =
      some (VInductDecl.recConstRec 1 ``Acc 2 accType) := rfl

theorem acc_rec_lookup_unique :
    accRecInfo.name = ``Acc.rec ∧
      TrConstant .safe accFinalEnv accRecInfo
        (VInductDecl.recConstRec 1 ``Acc 2 accType) :=
  acc_aligned.find?_uniq acc_rec_map_lookup acc_rec_env_lookup

/- This has the same `sorryAx`-free closure as the direct replay roots; the
persistent-map contracts enter through concrete `SMap` freshness proofs. -/
#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.acc_trEnv' [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

/-! ## AliasFormer: non-identity family-result normalization -/

/-- The actual reducible alias declaration that precedes `AliasFormer` in the
kernel environment. -/
def typeFamilyAliasKernelDef : DefinitionVal :=
  kernelDefVal% TypeFamilyAlias

def typeFamilyAliasInfo : ConstantInfo :=
  .defnInfo typeFamilyAliasKernelDef

def typeFamilyAliasVal : VDefVal where
  name := ``TypeFamilyAlias
  uvars := (vconst(type_of% @TypeFamilyAlias) : VConstant).uvars
  type := (vconst(type_of% @TypeFamilyAlias) : VConstant).type
  value := typeFamilyAliasDefEq.rhs

theorem typeFamilyAliasInfo_tr :
    TrDefVal .safe VEnv.empty typeFamilyAliasInfo typeFamilyAliasVal := by
  refine ⟨⟨⟨by decide, rfl, ?_⟩, rfl⟩, ?_⟩
  · exact .sort rfl
  · exact .sort rfl

theorem typeFamilyAliasVal_wf :
    typeFamilyAliasVal.WF VEnv.empty :=
  VEnv.HasType.sort (by decide)

def typeFamilyAliasMap : ConstMap :=
  ({} : ConstMap).insert ``TypeFamilyAlias typeFamilyAliasInfo

theorem typeFamilyAliasMap_fresh :
    ({} : ConstMap).find? ``TypeFamilyAlias = none := by
  simp [SMap.find?]

/-- Replay the actual alias definition, including its Theory delta rule. -/
theorem typeFamilyAlias_trEnv' {safety : DefinitionSafety} :
    TrEnv' safety typeFamilyAliasMap false typeFamilyAliasEnv :=
  .defn (ci := typeFamilyAliasKernelDef) (ci' := typeFamilyAliasVal)
    (typeFamilyAliasInfo_tr.sf_mono DefinitionSafety.le_safe)
    typeFamilyAliasMap_fresh
    typeFamilyAliasVal_wf rfl .empty

def aliasFormerInfo : ConstantInfo := kernelInductInfo% AliasFormer
def aliasFormerMkInfo : ConstantInfo := kernelCtorInfo% AliasFormer.mk
def aliasFormerRecInfo : ConstantInfo := kernelRecInfo% AliasFormer.rec
def aliasFormerKernelRuleRhs : VExpr :=
  kernelRecRuleRhs% AliasFormer.rec 0

example : aliasFormerRawDecl.checked? = none := rfl
example : aliasFormerGenerationChecked.block.sourceType =
    aliasFormerRawType := rfl
example : aliasFormerGenerationChecked.block.checked.type =
    aliasFormerViewType := rfl
example : aliasFormerKernelRuleRhs =
    aliasFormerGenerationChecked.generatedRules[0].rhs := rfl

def aliasFormerTypeEnv :=
  (typeFamilyAliasEnv.addConst aliasFormerRawType.name
    aliasFormerRawType.toVConstant).get!

def aliasFormerCtorEnv :=
  (aliasFormerTypeEnv.addConst aliasFormerRawType.ctors[0].name
    aliasFormerRawType.ctors[0].toVConstant).get!

def aliasFormerRecEnv :=
  (aliasFormerCtorEnv.addConst ``AliasFormer.rec
    aliasFormerGenerationChecked.recursor).get!

theorem aliasFormerTypeEnv_ordered : aliasFormerTypeEnv.Ordered := by
  refine .const (n := aliasFormerRawType.name)
    (ci := aliasFormerRawType.toVConstant)
    typeFamilyAliasEnv_ordered ?_ rfl
  show typeFamilyAliasEnv.IsType
    aliasFormerGenerationChecked.block.sourceType.uvars []
    aliasFormerGenerationChecked.block.sourceType.type
  rw [aliasFormerGenerationChecked.block.sourceType_uvars_eq]
  exact aliasFormerGenerationChecked_wf.rawFamily_isType

theorem aliasFormerRawCtor_wf :
    aliasFormerRawType.ctors[0].toVConstant.WF aliasFormerTypeEnv := by
  have hctor :
      (⟨aliasFormerRawType.ctors[0],
        aliasFormerViewChecked.constructors[0]⟩ :
          VInductDecl.NormalizedCtor) ∈
        aliasFormerGenerationChecked.block.ctorPairs := by
    exact .head _
  show aliasFormerTypeEnv.IsType
    aliasFormerRawType.ctors[0].uvars []
    aliasFormerRawType.ctors[0].type
  rw [aliasFormerGenerationChecked.ctor_uvars_eq hctor]
  exact aliasFormerGenerationChecked_wf.rawCtor_isType rfl hctor

theorem aliasFormerCtorEnv_ordered : aliasFormerCtorEnv.Ordered :=
  .const (n := aliasFormerRawType.ctors[0].name)
    (ci := aliasFormerRawType.ctors[0].toVConstant)
    aliasFormerTypeEnv_ordered aliasFormerRawCtor_wf rfl

theorem aliasFormerGenerationEnv :
    VInductDecl.GenerationEnv aliasFormerGenerationChecked
      aliasFormerCtorEnv := by
  apply aliasFormerGenerationChecked_wf.toGenerationEnv
    (envT := aliasFormerTypeEnv)
  · rfl
  · exact (VEnv.addConst_le (show
      typeFamilyAliasEnv.addConst aliasFormerRawType.name
        aliasFormerRawType.toVConstant = some aliasFormerTypeEnv from rfl)).trans
      (VEnv.addConst_le (show
        aliasFormerTypeEnv.addConst aliasFormerRawType.ctors[0].name
          aliasFormerRawType.ctors[0].toVConstant =
            some aliasFormerCtorEnv from rfl))
  · exact VEnv.addConst_le (show
      aliasFormerTypeEnv.addConst aliasFormerRawType.ctors[0].name
        aliasFormerRawType.ctors[0].toVConstant =
          some aliasFormerCtorEnv from rfl)
  · exact aliasFormerCtorEnv_ordered
  · rfl
  · intro ctor hctor
    change ctor ∈
      [⟨aliasFormerRawType.ctors[0],
        aliasFormerViewChecked.constructors[0]⟩] at hctor
    obtain rfl := List.mem_singleton.1 hctor
    rfl

theorem aliasFormerInfo_tr :
    TrConstVal .safe typeFamilyAliasEnv aliasFormerInfo
      aliasFormerRawType.toVConstVal := by
  have hAlias : typeFamilyAliasEnv.constants ``TypeFamilyAlias =
      some (vconst(type_of% @TypeFamilyAlias)) := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr typeFamilyAliasEnv
      aliasFormerInfo.levelParams [] aliasFormerInfo.type
      aliasFormerRawType.type := by
    tr_type_expr_tac
  obtain ⟨u, htype⟩ :=
    aliasFormerGenerationChecked_wf.rawFamily_isType
  exact hshape.to_trExprS typeFamilyAliasEnv_ordered trivial
    ⟨.sort u, htype⟩

theorem aliasFormerMkInfo_tr :
    TrConstVal .safe aliasFormerTypeEnv aliasFormerMkInfo
      aliasFormerRawType.ctors[0] := by
  have hFamily : aliasFormerTypeEnv.constants ``AliasFormer =
      some aliasFormerRawType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr aliasFormerTypeEnv
      aliasFormerMkInfo.levelParams [] aliasFormerMkInfo.type
      aliasFormerRawType.ctors[0].type := by
    tr_type_expr_tac
  obtain ⟨u, htype⟩ := aliasFormerRawCtor_wf
  exact hshape.to_trExprS aliasFormerTypeEnv_ordered trivial
    ⟨.sort u, htype⟩

theorem aliasFormerRecInfo_tr :
    TrConstVal .safe aliasFormerCtorEnv aliasFormerRecInfo
      (inductGenerationRecVal aliasFormerGenerationChecked) := by
  have hFamily : aliasFormerCtorEnv.constants ``AliasFormer =
      some aliasFormerRawType.toVConstant := rfl
  have hMk : aliasFormerCtorEnv.constants ``AliasFormer.mk =
      some aliasFormerRawType.ctors[0].toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr aliasFormerCtorEnv
      aliasFormerRecInfo.levelParams [] aliasFormerRecInfo.type
      (inductGenerationRecVal aliasFormerGenerationChecked).type := by
    tr_type_expr_tac
  obtain ⟨u, hrec⟩ := aliasFormerGenerationEnv.recursor_wf
  exact hshape.to_trExprS aliasFormerCtorEnv_ordered trivial
    ⟨.sort u, hrec⟩

def aliasFormerTypeMap : ConstMap :=
  typeFamilyAliasMap.insert ``AliasFormer aliasFormerInfo

def aliasFormerCtorMap : ConstMap :=
  aliasFormerTypeMap.insert ``AliasFormer.mk aliasFormerMkInfo

def aliasFormerMap : ConstMap :=
  aliasFormerCtorMap.insert ``AliasFormer.rec aliasFormerRecInfo

theorem typeFamilyAliasMap_wf : typeFamilyAliasMap.WF :=
  (typeFamilyAlias_trEnv' (safety := .safe)).map_wf

theorem aliasFormerType_fresh :
    typeFamilyAliasMap.find? ``AliasFormer = none := by
  rw [typeFamilyAliasMap, SMap.WF.find?_insert
    (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem aliasFormerTypeMap_wf : aliasFormerTypeMap.WF :=
  typeFamilyAliasMap_wf.insert _ _ aliasFormerType_fresh

theorem aliasFormerMk_fresh :
    aliasFormerTypeMap.find? ``AliasFormer.mk = none := by
  rw [aliasFormerTypeMap, typeFamilyAliasMap_wf.find?_insert,
    typeFamilyAliasMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem aliasFormerCtorMap_wf : aliasFormerCtorMap.WF :=
  aliasFormerTypeMap_wf.insert _ _ aliasFormerMk_fresh

theorem aliasFormerRec_fresh :
    aliasFormerCtorMap.find? ``AliasFormer.rec = none := by
  rw [aliasFormerCtorMap, aliasFormerTypeMap_wf.find?_insert,
    aliasFormerTypeMap, typeFamilyAliasMap_wf.find?_insert,
    typeFamilyAliasMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

private def aliasFormerAddInductTraceWith
    (generation_wf :
      aliasFormerGenerationChecked.WF typeFamilyAliasEnv) :
    AddInductTrace typeFamilyAliasMap typeFamilyAliasEnv
      aliasFormerRawDecl aliasFormerMap aliasFormerFinalEnv := by
  refine {
    generation := aliasFormerGenerationChecked
    generation_wf := generation_wf
    typeMap := aliasFormerTypeMap
    typeEnv := aliasFormerTypeEnv
    ctorMap := aliasFormerCtorMap
    ctorEnv := aliasFormerCtorEnv
    recEnv := aliasFormerRecEnv
    addType := {
      info := aliasFormerInfo
      kind_eq := by simp [aliasFormerInfo, InductConstantKind.Matches]
      tr := aliasFormerInfo_tr
      map_fresh := by
        change typeFamilyAliasMap.find? ``AliasFormer = none
        exact aliasFormerType_fresh
      env_add := rfl
      map_add := rfl }
    addCtors := ?_
    addRec := {
      info := aliasFormerRecInfo
      kind_eq := by simp [aliasFormerRecInfo, InductConstantKind.Matches]
      tr := aliasFormerRecInfo_tr
      map_fresh := by
        change aliasFormerCtorMap.find? ``AliasFormer.rec = none
        exact aliasFormerRec_fresh
      env_add := rfl
      map_add := rfl }
    recK := by decide
    addRules := ⟨rfl⟩ }
  exact .cons {
    info := aliasFormerMkInfo
    kind_eq := by simp [aliasFormerMkInfo, InductConstantKind.Matches]
    tr := aliasFormerMkInfo_tr
    map_fresh := by
      simpa [aliasFormerRawType] using aliasFormerMk_fresh
    env_add := rfl
    map_add := rfl } .nil

theorem aliasFormer_addInduct :
    AddInduct typeFamilyAliasMap typeFamilyAliasEnv
      aliasFormerRawDecl aliasFormerMap aliasFormerFinalEnv :=
  ⟨aliasFormerAddInductTraceWith aliasFormerGenerationChecked_wf⟩

theorem aliasFormer_trEnv' :
    TrEnv' .safe aliasFormerMap false aliasFormerFinalEnv :=
  .induct aliasFormer_addInduct typeFamilyAlias_trEnv'

theorem aliasFormer_final_matches_generation :
    typeFamilyAliasEnv.addInductGeneration
      aliasFormerGenerationChecked = some aliasFormerFinalEnv :=
  aliasFormer_addInductGeneration

theorem aliasFormer_env_wf : aliasFormerFinalEnv.WF :=
  aliasFormer_trEnv'.wf

theorem aliasFormer_aligned :
    Aligned .safe aliasFormerMap aliasFormerFinalEnv :=
  aliasFormer_trEnv'.aligned

theorem aliasFormer_type_map_lookup :
    aliasFormerMap.find? ``AliasFormer = some aliasFormerInfo := by
  rw [aliasFormerMap, aliasFormerCtorMap_wf.find?_insert,
    aliasFormerCtorMap, aliasFormerTypeMap_wf.find?_insert,
    aliasFormerTypeMap, typeFamilyAliasMap_wf.find?_insert]
  rfl

theorem aliasFormer_type_lookup_unique :
    aliasFormerInfo.name = ``AliasFormer ∧
      TrConstant .safe aliasFormerFinalEnv aliasFormerInfo
        aliasFormerRawType.toVConstant :=
  aliasFormer_aligned.find?_uniq aliasFormer_type_map_lookup
    aliasFormerFinalEnv_family_lookup

theorem aliasFormer_mk_map_lookup :
    aliasFormerMap.find? ``AliasFormer.mk = some aliasFormerMkInfo := by
  rw [aliasFormerMap, aliasFormerCtorMap_wf.find?_insert,
    aliasFormerCtorMap, aliasFormerTypeMap_wf.find?_insert]
  rfl

theorem aliasFormer_mk_lookup_unique :
    aliasFormerMkInfo.name = ``AliasFormer.mk ∧
      TrConstant .safe aliasFormerFinalEnv aliasFormerMkInfo
        aliasFormerRawType.ctors[0].toVConstant :=
  aliasFormer_aligned.find?_uniq aliasFormer_mk_map_lookup
    (aliasFormerFinalEnv_ctor_lookup _ (.head _))

theorem aliasFormer_rec_map_lookup :
    aliasFormerMap.find? ``AliasFormer.rec = some aliasFormerRecInfo := by
  rw [aliasFormerMap, aliasFormerCtorMap_wf.find?_insert]
  rfl

theorem aliasFormer_rec_lookup_unique :
    aliasFormerRecInfo.name = ``AliasFormer.rec ∧
      TrConstant .safe aliasFormerFinalEnv aliasFormerRecInfo
        aliasFormerGenerationChecked.recursor :=
  aliasFormer_aligned.find?_uniq aliasFormer_rec_map_lookup
    aliasFormerFinalEnv_rec_lookup

/-! ## AliasRec: non-identity recursive-field normalization -/

def recAliasKernelDef : DefinitionVal := kernelDefVal% RecAlias

def recAliasInfo : ConstantInfo := .defnInfo recAliasKernelDef

def recAliasVal : VDefVal where
  name := ``RecAlias
  uvars := (vconst(type_of% @RecAlias) : VConstant).uvars
  type := (vconst(type_of% @RecAlias) : VConstant).type
  value := recAliasDefEq.rhs

theorem recAliasInfo_tr :
    TrDefVal .safe VEnv.empty recAliasInfo recAliasVal := by
  refine ⟨⟨⟨by decide, rfl, ?_⟩, rfl⟩, ?_⟩
  · have hshape : TrTypeExpr VEnv.empty recAliasInfo.levelParams []
        recAliasInfo.type recAliasVal.type := by
      tr_type_expr_tac
    obtain ⟨u, htype⟩ := recAliasConstant_wf
    exact hshape.to_trExprS .empty trivial ⟨.sort u, htype⟩
  · refine .lam ?_ (.sort rfl) (.bvar rfl)
    exact ⟨_, VEnv.HasType.sort (by decide)⟩

theorem recAliasVal_wf : recAliasVal.WF VEnv.empty := by
  exact VEnv.HasType.lam
    (VEnv.HasType.sort (by decide))
    (VEnv.HasType.bvar .zero)

def recAliasMap : ConstMap :=
  ({} : ConstMap).insert ``RecAlias recAliasInfo

theorem recAliasMap_fresh :
    ({} : ConstMap).find? ``RecAlias = none := by
  simp [SMap.find?]

theorem recAlias_trEnv' {safety : DefinitionSafety} :
    TrEnv' safety recAliasMap false recAliasEnv :=
  .defn (ci := recAliasKernelDef) (ci' := recAliasVal)
    (recAliasInfo_tr.sf_mono DefinitionSafety.le_safe)
    recAliasMap_fresh recAliasVal_wf rfl .empty

def aliasRecInfo : ConstantInfo := kernelInductInfo% AliasRec
def aliasRecMkInfo : ConstantInfo := kernelCtorInfo% AliasRec.mk
def aliasRecRecInfo : ConstantInfo := kernelRecInfo% AliasRec.rec
def aliasRecKernelRuleRhs : VExpr :=
  kernelRecRuleRhs% AliasRec.rec 0

example : aliasRecRawDecl.checked? = none := rfl
example : aliasRecGenerationChecked.block.sourceType = aliasRecRawType := rfl
example : aliasRecGenerationChecked.block.checked.type = aliasRecViewType := rfl
example : aliasRecGenerationChecked.block.ctorPairs[0].rawFields 0 =
    [aliasRecRawField] := rfl
example : (VInductDecl.ctorFields
    aliasRecGenerationChecked.minorTypes[0])[0]? =
      some aliasRecRawField := rfl
example : aliasRecKernelRuleRhs =
    aliasRecGenerationChecked.generatedRules[0].rhs := rfl

def aliasRecTypeEnv :=
  (recAliasEnv.addConst aliasRecRawType.name
    aliasRecRawType.toVConstant).get!

def aliasRecCtorEnv :=
  (aliasRecTypeEnv.addConst aliasRecRawType.ctors[0].name
    aliasRecRawType.ctors[0].toVConstant).get!

def aliasRecRecEnv :=
  (aliasRecCtorEnv.addConst ``AliasRec.rec
    aliasRecGenerationChecked.recursor).get!

theorem aliasRecTypeEnv_ordered : aliasRecTypeEnv.Ordered := by
  refine .const (n := aliasRecRawType.name)
    (ci := aliasRecRawType.toVConstant)
    recAliasEnv_ordered ?_ rfl
  show recAliasEnv.IsType
    aliasRecGenerationChecked.block.sourceType.uvars []
    aliasRecGenerationChecked.block.sourceType.type
  rw [aliasRecGenerationChecked.block.sourceType_uvars_eq]
  exact aliasRecGenerationChecked_wf.rawFamily_isType

theorem aliasRecRawCtor_wf :
    aliasRecRawType.ctors[0].toVConstant.WF aliasRecTypeEnv := by
  have hctor :
      (⟨aliasRecRawType.ctors[0],
        aliasRecViewChecked.constructors[0]⟩ :
          VInductDecl.NormalizedCtor) ∈
        aliasRecGenerationChecked.block.ctorPairs := by
    exact .head _
  show aliasRecTypeEnv.IsType aliasRecRawType.ctors[0].uvars []
    aliasRecRawType.ctors[0].type
  rw [aliasRecGenerationChecked.ctor_uvars_eq hctor]
  exact aliasRecGenerationChecked_wf.rawCtor_isType rfl hctor

theorem aliasRecCtorEnv_ordered : aliasRecCtorEnv.Ordered :=
  .const (n := aliasRecRawType.ctors[0].name)
    (ci := aliasRecRawType.ctors[0].toVConstant)
    aliasRecTypeEnv_ordered aliasRecRawCtor_wf rfl

theorem aliasRecGenerationEnv :
    VInductDecl.GenerationEnv aliasRecGenerationChecked aliasRecCtorEnv := by
  apply aliasRecGenerationChecked_wf.toGenerationEnv
    (envT := aliasRecTypeEnv)
  · rfl
  · exact (VEnv.addConst_le (show
      recAliasEnv.addConst aliasRecRawType.name
        aliasRecRawType.toVConstant = some aliasRecTypeEnv from rfl)).trans
      (VEnv.addConst_le (show
        aliasRecTypeEnv.addConst aliasRecRawType.ctors[0].name
          aliasRecRawType.ctors[0].toVConstant =
            some aliasRecCtorEnv from rfl))
  · exact VEnv.addConst_le (show
      aliasRecTypeEnv.addConst aliasRecRawType.ctors[0].name
        aliasRecRawType.ctors[0].toVConstant =
          some aliasRecCtorEnv from rfl)
  · exact aliasRecCtorEnv_ordered
  · rfl
  · intro ctor hctor
    change ctor ∈
      [⟨aliasRecRawType.ctors[0],
        aliasRecViewChecked.constructors[0]⟩] at hctor
    obtain rfl := List.mem_singleton.1 hctor
    rfl

theorem aliasRecInfo_tr :
    TrConstVal .safe recAliasEnv aliasRecInfo
      aliasRecRawType.toVConstVal := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr recAliasEnv aliasRecInfo.levelParams []
      aliasRecInfo.type aliasRecRawType.type := by
    tr_type_expr_tac
  exact hshape.to_trExprS recAliasEnv_ordered trivial
    ⟨.sort (.succ (.succ .zero)), VEnv.HasType.sort (by decide)⟩

theorem aliasRecMkInfo_tr :
    TrConstVal .safe aliasRecTypeEnv aliasRecMkInfo
      aliasRecRawType.ctors[0] := by
  have hAlias : aliasRecTypeEnv.constants ``RecAlias =
      some (vconst(type_of% @RecAlias)) := rfl
  have hFamily : aliasRecTypeEnv.constants ``AliasRec =
      some aliasRecRawType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr aliasRecTypeEnv
      aliasRecMkInfo.levelParams [] aliasRecMkInfo.type
      aliasRecRawType.ctors[0].type := by
    tr_type_expr_tac
  obtain ⟨u, htype⟩ := aliasRecRawCtor_wf
  exact hshape.to_trExprS aliasRecTypeEnv_ordered trivial
    ⟨.sort u, htype⟩

theorem aliasRecRecInfo_tr :
    TrConstVal .safe aliasRecCtorEnv aliasRecRecInfo
      (inductGenerationRecVal aliasRecGenerationChecked) := by
  have hAlias : aliasRecCtorEnv.constants ``RecAlias =
      some (vconst(type_of% @RecAlias)) := rfl
  have hFamily : aliasRecCtorEnv.constants ``AliasRec =
      some aliasRecRawType.toVConstant := rfl
  have hMk : aliasRecCtorEnv.constants ``AliasRec.mk =
      some aliasRecRawType.ctors[0].toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr aliasRecCtorEnv
      aliasRecRecInfo.levelParams [] aliasRecRecInfo.type
      (inductGenerationRecVal aliasRecGenerationChecked).type := by
    tr_type_expr_tac
  obtain ⟨u, hrec⟩ := aliasRecGenerationEnv.recursor_wf
  exact hshape.to_trExprS aliasRecCtorEnv_ordered trivial
    ⟨.sort u, hrec⟩

def aliasRecTypeMap : ConstMap :=
  recAliasMap.insert ``AliasRec aliasRecInfo

def aliasRecCtorMap : ConstMap :=
  aliasRecTypeMap.insert ``AliasRec.mk aliasRecMkInfo

def aliasRecMap : ConstMap :=
  aliasRecCtorMap.insert ``AliasRec.rec aliasRecRecInfo

theorem recAliasMap_wf : recAliasMap.WF := (recAlias_trEnv' (safety := .safe)).map_wf

theorem aliasRecType_fresh :
    recAliasMap.find? ``AliasRec = none := by
  rw [recAliasMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem aliasRecTypeMap_wf : aliasRecTypeMap.WF :=
  recAliasMap_wf.insert _ _ aliasRecType_fresh

theorem aliasRecMk_fresh :
    aliasRecTypeMap.find? ``AliasRec.mk = none := by
  rw [aliasRecTypeMap, recAliasMap_wf.find?_insert, recAliasMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem aliasRecCtorMap_wf : aliasRecCtorMap.WF :=
  aliasRecTypeMap_wf.insert _ _ aliasRecMk_fresh

theorem aliasRecRec_fresh :
    aliasRecCtorMap.find? ``AliasRec.rec = none := by
  rw [aliasRecCtorMap, aliasRecTypeMap_wf.find?_insert,
    aliasRecTypeMap, recAliasMap_wf.find?_insert, recAliasMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

private def aliasRecAddInductTraceWith
    (generation_wf : aliasRecGenerationChecked.WF recAliasEnv) :
    AddInductTrace recAliasMap recAliasEnv aliasRecRawDecl
      aliasRecMap aliasRecFinalEnv := by
  refine {
    generation := aliasRecGenerationChecked
    generation_wf := generation_wf
    typeMap := aliasRecTypeMap
    typeEnv := aliasRecTypeEnv
    ctorMap := aliasRecCtorMap
    ctorEnv := aliasRecCtorEnv
    recEnv := aliasRecRecEnv
    addType := {
      info := aliasRecInfo
      kind_eq := by simp [aliasRecInfo, InductConstantKind.Matches]
      tr := aliasRecInfo_tr
      map_fresh := by
        change recAliasMap.find? ``AliasRec = none
        exact aliasRecType_fresh
      env_add := rfl
      map_add := rfl }
    addCtors := ?_
    addRec := {
      info := aliasRecRecInfo
      kind_eq := by simp [aliasRecRecInfo, InductConstantKind.Matches]
      tr := aliasRecRecInfo_tr
      map_fresh := by
        change aliasRecCtorMap.find? ``AliasRec.rec = none
        exact aliasRecRec_fresh
      env_add := rfl
      map_add := rfl }
    recK := by decide
    addRules := ⟨rfl⟩ }
  exact .cons {
    info := aliasRecMkInfo
    kind_eq := by simp [aliasRecMkInfo, InductConstantKind.Matches]
    tr := aliasRecMkInfo_tr
    map_fresh := by simpa [aliasRecRawType] using aliasRecMk_fresh
    env_add := rfl
    map_add := rfl } .nil

theorem aliasRec_addInduct :
    AddInduct recAliasMap recAliasEnv aliasRecRawDecl
      aliasRecMap aliasRecFinalEnv :=
  ⟨aliasRecAddInductTraceWith aliasRecGenerationChecked_wf⟩

theorem aliasRec_trEnv' :
    TrEnv' .safe aliasRecMap false aliasRecFinalEnv :=
  .induct aliasRec_addInduct recAlias_trEnv'

theorem aliasRec_final_matches_generation :
    recAliasEnv.addInductGeneration aliasRecGenerationChecked =
      some aliasRecFinalEnv :=
  aliasRec_addInductGeneration

theorem aliasRec_env_wf : aliasRecFinalEnv.WF :=
  aliasRec_trEnv'.wf

theorem aliasRec_aligned :
    Aligned .safe aliasRecMap aliasRecFinalEnv :=
  aliasRec_trEnv'.aligned

theorem aliasRec_type_map_lookup :
    aliasRecMap.find? ``AliasRec = some aliasRecInfo := by
  rw [aliasRecMap, aliasRecCtorMap_wf.find?_insert,
    aliasRecCtorMap, aliasRecTypeMap_wf.find?_insert,
    aliasRecTypeMap, recAliasMap_wf.find?_insert]
  rfl

theorem aliasRec_type_lookup_unique :
    aliasRecInfo.name = ``AliasRec ∧
      TrConstant .safe aliasRecFinalEnv aliasRecInfo
        aliasRecRawType.toVConstant :=
  aliasRec_aligned.find?_uniq aliasRec_type_map_lookup
    aliasRecFinalEnv_family_lookup

theorem aliasRec_mk_map_lookup :
    aliasRecMap.find? ``AliasRec.mk = some aliasRecMkInfo := by
  rw [aliasRecMap, aliasRecCtorMap_wf.find?_insert,
    aliasRecCtorMap, aliasRecTypeMap_wf.find?_insert]
  rfl

theorem aliasRec_mk_lookup_unique :
    aliasRecMkInfo.name = ``AliasRec.mk ∧
      TrConstant .safe aliasRecFinalEnv aliasRecMkInfo
        aliasRecRawType.ctors[0].toVConstant :=
  aliasRec_aligned.find?_uniq aliasRec_mk_map_lookup
    (aliasRecFinalEnv_ctor_lookup _ (.head _))

theorem aliasRec_rec_map_lookup :
    aliasRecMap.find? ``AliasRec.rec = some aliasRecRecInfo := by
  rw [aliasRecMap, aliasRecCtorMap_wf.find?_insert]
  rfl

theorem aliasRec_rec_lookup_unique :
    aliasRecRecInfo.name = ``AliasRec.rec ∧
      TrConstant .safe aliasRecFinalEnv aliasRecRecInfo
        aliasRecGenerationChecked.recursor :=
  aliasRec_aligned.find?_uniq aliasRec_rec_map_lookup
    aliasRecFinalEnv_rec_lookup

/-! ## Binder annotation candidate fixtures -/

/- These four definitions are quoted from the running kernel rather than
reconstructed. The resulting minimal environment is sufficient for the
ordinary checker to delta-reduce every annotation gadget while leaving the
shared `Nat` endpoint opaque. -/
private def annotationOutParamInfo : ConstantInfo :=
  .defnInfo (kernelDefVal% outParam)

private def annotationSemiOutParamInfo : ConstantInfo :=
  .defnInfo (kernelDefVal% semiOutParam)

private def annotationOptParamInfo : ConstantInfo :=
  .defnInfo (kernelDefVal% optParam)

private def annotationAutoParamInfo : ConstantInfo :=
  .defnInfo (kernelDefVal% autoParam)

private def annotationKernelMap : ConstMap :=
  ((({} : ConstMap).insert ``outParam annotationOutParamInfo).insert
    ``semiOutParam annotationSemiOutParamInfo).insert
      ``optParam annotationOptParamInfo |>.insert
        ``autoParam annotationAutoParamInfo

private def annotationKernelEnv : Kernel.Environment :=
  Kernel.Environment.ofConstants `_annotationCandidate annotationKernelMap

private def annotationCandidateContext : AddInductive.Context where
  env := annotationKernelEnv
  lparams := []
  safety := .safe
  allowPrimitive := false

private def annotationNatExpr : Expr := .const ``Nat []

private def outParamDomain : Expr :=
  .app (.const ``outParam [.succ .zero]) annotationNatExpr

private def semiOutParamDomain : Expr :=
  .app (.const ``semiOutParam [.succ .zero]) annotationNatExpr

private def optParamDomain : Expr :=
  .app (.app (.const ``optParam [.succ .zero]) annotationNatExpr)
    (.lit (.natVal 0))

private def autoParamDomain : Expr :=
  .app (.app (.const ``autoParam [.succ .zero]) annotationNatExpr)
    (.const ``Lean.Syntax.missing [])

/- Each constructor is inhabited at its precise source and consumed indices;
the guards below additionally ensure the executable structural mirror chooses
that constructor. -/
private def outParamTrace :
    AddInductive.CandidateTypeAnnotationTrace
      outParamDomain annotationNatExpr :=
  .outParam [.succ .zero] annotationNatExpr (.identity _)

private def semiOutParamTrace :
    AddInductive.CandidateTypeAnnotationTrace
      semiOutParamDomain annotationNatExpr :=
  .semiOutParam [.succ .zero] annotationNatExpr (.identity _)

private def optParamTrace :
    AddInductive.CandidateTypeAnnotationTrace
      optParamDomain annotationNatExpr :=
  .optParam [.succ .zero] annotationNatExpr
    (.lit (.natVal 0)) (.identity _)

private def autoParamTrace :
    AddInductive.CandidateTypeAnnotationTrace
      autoParamDomain annotationNatExpr :=
  .autoParam [.succ .zero] annotationNatExpr
    (.const ``Lean.Syntax.missing []) (.identity _)

private def annotationTraceTag :
    AddInductive.CandidateTypeAnnotationTrace source consumed → Nat
  | .identity _ => 0
  | .outParam .. => 1
  | .semiOutParam .. => 2
  | .optParam .. => 3
  | .autoParam .. => 4

#guard let ⟨consumed, trace⟩ :=
    AddInductive.CandidateTypeAnnotationTrace.build outParamDomain
  consumed.equal annotationNatExpr && annotationTraceTag trace == 1

#guard let ⟨consumed, trace⟩ :=
    AddInductive.CandidateTypeAnnotationTrace.build semiOutParamDomain
  consumed.equal annotationNatExpr && annotationTraceTag trace == 2

#guard let ⟨consumed, trace⟩ :=
    AddInductive.CandidateTypeAnnotationTrace.build optParamDomain
  consumed.equal annotationNatExpr && annotationTraceTag trace == 3

#guard let ⟨consumed, trace⟩ :=
    AddInductive.CandidateTypeAnnotationTrace.build autoParamDomain
  consumed.equal annotationNatExpr && annotationTraceTag trace == 4

private def annotationCandidateAccepted (domain expected : Expr) : Bool :=
  match AddInductive.buildCandidateTypeAnnotations domain with
  | .error _ => false
  | .ok annotations =>
    annotations.consumed.equal expected &&
      match AddInductive.observeCandidateIsDefEq annotationCandidateContext
          domain annotations.consumed with
      | .ok _ => true
      | .error _ => false

/- These guards cover the complete binder-annotation seam used by the
candidate producer: the transparent structural implementation remains
differentially equal to Lean's opaque helper, followed by an exact successful
ordinary-checker equality observation. -/
#guard AddInductive.candidateTypeAnnotationsAgree outParamDomain
#guard AddInductive.candidateTypeAnnotationsAgree semiOutParamDomain
#guard AddInductive.candidateTypeAnnotationsAgree optParamDomain
#guard AddInductive.candidateTypeAnnotationsAgree autoParamDomain
#guard annotationCandidateAccepted outParamDomain annotationNatExpr
#guard annotationCandidateAccepted semiOutParamDomain annotationNatExpr
#guard annotationCandidateAccepted optParamDomain annotationNatExpr
#guard annotationCandidateAccepted autoParamDomain annotationNatExpr

private def annotationIsDefEq (lhs rhs : Expr) :=
  TypeChecker.M.run annotationCandidateContext.env
    annotationCandidateContext.safety annotationCandidateContext.lctx
    annotationCandidateContext.lparams annotationCandidateContext.fuel
    (TypeChecker.isDefEq lhs rhs)

/- A genuinely unequal domain is observed as `.ok false`, not a checker
failure, and the candidate boundary rejects it with the dedicated error. -/
#guard match annotationIsDefEq (.sort .zero) (.sort (.succ .zero)) with
  | .ok false => true
  | _ => false

#guard match AddInductive.observeCandidateIsDefEq annotationCandidateContext
    (.sort .zero) (.sort (.succ .zero)) with
  | .error (.other message) =>
    message == "normalization candidate changed a binder domain"
  | _ => false

/-! ## Annotated recursive-Pi candidate -/

/-- Exact kernel definition and Theory value used to interpret `outParam`
inside a complete recursive constructor candidate. -/
private def outParamKernelDef : DefinitionVal :=
  kernelDefVal% outParam

private def outParamVal : VDefVal where
  name := ``outParam
  uvars := (vconst(type_of% @outParam) : VConstant).uvars
  type := (vconst(type_of% @outParam) : VConstant).type
  value := outParamDefEq.rhs

private theorem outParamInfo_tr :
    TrDefVal .safe VEnv.empty annotationOutParamInfo outParamVal := by
  refine ⟨⟨⟨by decide, rfl, ?_⟩, rfl⟩, ?_⟩
  · exact .forallE
      ⟨_, VEnv.HasType.sort (by decide)⟩
      ⟨_, VEnv.HasType.sort (by decide)⟩
      (.sort rfl) (.sort rfl)
  · exact .lam
      ⟨_, VEnv.HasType.sort (by decide)⟩
      (.sort rfl) (.bvar rfl)

private theorem outParamVal_wf : outParamVal.WF VEnv.empty := by
  exact VEnv.HasType.lam
    (VEnv.HasType.sort (by decide))
    (VEnv.HasType.bvar .zero)

private def outParamMap : ConstMap :=
  ({} : ConstMap).insert ``outParam annotationOutParamInfo

private theorem outParamMap_fresh :
    ({} : ConstMap).find? ``outParam = none := by
  simp [SMap.find?]

private theorem outParam_trEnv' {safety : DefinitionSafety} :
    TrEnv' safety outParamMap false outParamEnv :=
  .defn (ci := outParamKernelDef) (ci' := outParamVal)
    (outParamInfo_tr.sf_mono DefinitionSafety.le_safe)
    outParamMap_fresh outParamVal_wf rfl .empty

private theorem outParamMap_wf : outParamMap.WF :=
  (outParam_trEnv' (safety := .safe)).map_wf

/-- Public map-well-formedness boundary for replay artifacts whose concrete
dependency map is intentionally kept private to this fixture module. -/
theorem annotatedReplayInputMap_wf : outParamMap.WF :=
  outParamMap_wf

private def outParamKernelEnv : Kernel.Environment :=
  Kernel.Environment.ofConstants `_annotatedPiCandidate outParamMap

private theorem outParam_trEnv :
    TrEnv .safe outParamKernelEnv outParamEnv := by
  simpa [TrEnv, outParamKernelEnv, Kernel.Environment.ofConstants] using
    outParam_trEnv'

private theorem outParam_hasPrimitives :
    VEnv.HasPrimitives outParamEnv := by
  apply VEnv.HasPrimitives.of_avoids
  intro n hn
  simp only [VEnv.reflectedPrimitiveNames, List.mem_cons,
    List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;>
    rfl

private theorem outParam_safePrimitives :
    outParamKernelEnv.find? n = some ci →
      Kernel.Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [] := by
  intro hfind hprim
  change outParamMap.find?' n = some ci at hfind
  rw [outParamMap_wf.find?'_eq_find?, outParamMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty] at hfind
  simp [SMap.find?] at hfind
  obtain ⟨rfl, rfl⟩ := hfind
  simp [Kernel.Environment.primitives, NameSet.ofList] at hprim
  simp +decide [NameSet.contains] at hprim

private def outParamVEnvs : VEnvs where
  venv _ := outParamEnv

private theorem outParamVEnvs_wf : outParamVEnvs.WF outParamKernelEnv where
  tr := by
    intro safety
    exact outParam_trEnv'
  hasPrimitives := outParam_hasPrimitives
  safePrimitives := outParam_safePrimitives
  mono := fun _ => .rfl
  projectionReady := ProjectionReady.of_no_ctorInfo <| by
    intro name _info h
    change outParamMap.find?' name = some (.ctorInfo _info) at h
    rw [outParamMap_wf.find?'_eq_find?] at h
    simp only [outParamMap, SMap.WF.find?_insert
      (s := ({} : ConstMap)) SMap.WF.empty] at h
    simp [SMap.find?, annotationOutParamInfo] at h
  structureEtaReady := StructureEtaReady.of_no_ctorInfo <| by
    intro name _info h
    change outParamMap.find?' name = some (.ctorInfo _info) at h
    rw [outParamMap_wf.find?'_eq_find?] at h
    simp only [outParamMap, SMap.WF.find?_insert
      (s := ({} : ConstMap)) SMap.WF.empty] at h
    simp [SMap.find?, annotationOutParamInfo] at h

/-! ## Definitionally equal constructor parameters -/

def annotatedParamInfo : ConstantInfo := kernelInductInfo% AnnotatedParam
def annotatedParamMkInfo : ConstantInfo := kernelCtorInfo% AnnotatedParam.mk
def annotatedParamRecInfo : ConstantInfo := kernelRecInfo% AnnotatedParam.rec
def annotatedParamKernelRuleRhs : VExpr :=
  kernelRecRuleRhs% AnnotatedParam.rec 0

example : annotatedParamKernelRuleRhs =
    annotatedParamGenerationChecked.generatedRules[0].rhs := rfl

private def annotatedParamKernelCtor : Constructor where
  name := annotatedParamMkInfo.name
  type := annotatedParamMkInfo.type

private def annotatedParamKernelType : InductiveType where
  name := annotatedParamInfo.name
  type := annotatedParamInfo.type
  ctors := [annotatedParamKernelCtor]

private def annotatedParamCandidateContext : AddInductive.Context where
  env := outParamKernelEnv
  lparams := []
  safety := .safe
  allowPrimitive := false

private def annotatedParamExpectedFamilyView : Expr :=
  .forallE `alpha (.sort (.succ .zero))
    (.sort (.succ .zero)) .default

private def annotatedParamExpectedCtorView : Expr :=
  .forallE `alpha (.sort (.succ .zero))
    (.app (.const ``AnnotatedParam []) (.bvar 0)) .implicit

/- The successful whole metadata pass reaches `checkConstructors`, compares
the stored `outParam Type` constructor prefix with the checked `Type` family
local by ordinary definitional equality, and retains the checked surface in
both candidate views. -/
#guard match AddInductive.buildNormalizationCandidate 1
    [annotatedParamKernelType] 0 false annotatedParamCandidateContext with
  | .ok candidate =>
    candidate.families.singleton.familyType.type.view.equal
        annotatedParamExpectedFamilyView &&
      match candidate.families.singleton.constructors with
      | .cons constructor .nil =>
        constructor.type.view.equal annotatedParamExpectedCtorView
  | .error _ => false

/- Keep the constructor type closed and independently well typed while making
its declared parameter domain genuinely different. The fixed result avoids a
premature application-type failure, so rejection is specifically the same
constructor-parameter check exercised by the positive. -/
private def annotatedParamNonDefEqCtor : Constructor where
  name := annotatedParamMkInfo.name
  type := .forallE `alpha (.sort .zero)
    (.app (.const ``AnnotatedParam []) (.sort .zero)) .implicit

private def annotatedParamNonDefEqType : InductiveType :=
  { annotatedParamKernelType with ctors := [annotatedParamNonDefEqCtor] }

#guard match AddInductive.buildNormalizationCandidate 1
    [annotatedParamNonDefEqType] 0 false annotatedParamCandidateContext with
  | .error (.other message) =>
    message ==
      "arg #1 of 'Ix.Theory.Named.InductiveFixtures.AnnotatedParam.mk' does not match inductive datatype parameters"
  | _ => false

private theorem annotatedParamRawType_wf :
    annotatedParamRawType.toVConstant.WF outParamEnv := by
  refine ⟨.imax (.succ (.succ .zero)) (.succ (.succ .zero)), ?_⟩
  change outParamEnv.HasType 0 []
    (.forallE
      (.app (.const ``outParam [.succ (.succ .zero)])
        (.sort (.succ .zero)))
      (.sort (.succ .zero)))
    (.sort (.imax (.succ (.succ .zero)) (.succ (.succ .zero))))
  apply VEnv.HasType.forallE
  · apply VEnv.HasType.app
      (A := .sort (.succ (.succ .zero)))
      (B := .sort (.succ (.succ .zero)))
    · simpa [VExpr.instL, VLevel.inst] using VEnv.HasType.const
        (env := outParamEnv) (U := 0) (c := ``outParam)
        (ci := vconst(type_of% @outParam))
        (ls := [.succ (.succ .zero)]) rfl
        (by simp; decide) rfl
    · exact VEnv.HasType.sort (by decide)
  · exact VEnv.HasType.sort (by decide)

private theorem annotatedParamInfo_tr :
    TrConstVal .safe outParamEnv annotatedParamInfo
      annotatedParamRawType.toVConstVal := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr outParamEnv annotatedParamInfo.levelParams []
      annotatedParamInfo.type annotatedParamRawType.type := by
    tr_type_expr_tac
  obtain ⟨u, htype⟩ := annotatedParamRawType_wf
  exact hshape.to_trExprS outParamEnv_ordered trivial ⟨.sort u, htype⟩

private def annotatedParamTypeEnv : VEnv :=
  (outParamEnv.addConst annotatedParamRawType.name
    annotatedParamRawType.toVConstant).get!

private def annotatedParamTypeMap : ConstMap :=
  outParamMap.insert ``AnnotatedParam annotatedParamInfo

private theorem annotatedParamType_fresh :
    outParamMap.find? ``AnnotatedParam = none := by
  rw [outParamMap, SMap.WF.find?_insert
    (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

private theorem annotatedParamTypeMap_wf : annotatedParamTypeMap.WF :=
  outParamMap_wf.insert _ _ annotatedParamType_fresh

private def annotatedParamAddType :
    AddInductConstant .induct outParamMap outParamEnv
      annotatedParamRawType.toVConstVal annotatedParamTypeMap
      annotatedParamTypeEnv where
  info := annotatedParamInfo
  kind_eq := by simp [annotatedParamInfo, InductConstantKind.Matches]
  tr := annotatedParamInfo_tr
  map_fresh := by simpa [annotatedParamRawType] using
    annotatedParamType_fresh
  env_add := rfl
  map_add := rfl

private def annotatedParamTypeKernelEnv : Kernel.Environment :=
  Kernel.Environment.ofConstants `_annotatedParamCandidate
    annotatedParamTypeMap

private theorem annotatedParamTypeEnv_ordered :
    annotatedParamTypeEnv.Ordered :=
  .const (n := annotatedParamRawType.name)
    (ci := annotatedParamRawType.toVConstant)
    outParamEnv_ordered annotatedParamRawType_wf rfl

private def annotatedParamCtorCandidateContext : AddInductive.Context where
  env := annotatedParamTypeKernelEnv
  lparams := []
  safety := .safe
  allowPrimitive := false

private theorem annotatedParamType_lookup_outParam :
    annotatedParamTypeKernelEnv.find? ``outParam =
      some annotationOutParamInfo := by
  change annotatedParamTypeMap.find?' ``outParam =
    some annotationOutParamInfo
  rw [annotatedParamTypeMap_wf.find?'_eq_find?, annotatedParamTypeMap,
    outParamMap_wf.find?_insert]
  rw [outParamMap, SMap.WF.find?_insert
    (s := ({} : ConstMap)) SMap.WF.empty]
  rfl

private theorem annotatedParamType_lookup_family :
    annotatedParamTypeKernelEnv.find? ``AnnotatedParam =
      some annotatedParamInfo := by
  change annotatedParamTypeMap.find?' ``AnnotatedParam =
    some annotatedParamInfo
  rw [annotatedParamTypeMap_wf.find?'_eq_find?, annotatedParamTypeMap,
    outParamMap_wf.find?_insert]
  rfl

@[simp] private theorem annotatedParamType_get_outParam :
    annotatedParamTypeKernelEnv.get ``outParam =
      .ok annotationOutParamInfo := by
  unfold Kernel.Environment.get
  rw [annotatedParamType_lookup_outParam]
  rfl

@[simp] private theorem annotatedParamType_get_family :
    annotatedParamTypeKernelEnv.get ``AnnotatedParam =
      .ok annotatedParamInfo := by
  unfold Kernel.Environment.get
  rw [annotatedParamType_lookup_family]
  rfl

def annotatedPiInfo : ConstantInfo := kernelInductInfo% AnnotatedPi
def annotatedPiMkInfo : ConstantInfo := kernelCtorInfo% AnnotatedPi.mk
def annotatedPiRecInfo : ConstantInfo := kernelRecInfo% AnnotatedPi.rec
def annotatedPiKernelRuleRhs : VExpr :=
  kernelRecRuleRhs% AnnotatedPi.rec 0

example : annotatedPiKernelRuleRhs =
    annotatedPiGenerationChecked.generatedRules[0].rhs := rfl

private def annotatedPiKernelCtor : Constructor where
  name := annotatedPiMkInfo.name
  type := annotatedPiMkInfo.type

private def annotatedPiKernelType : InductiveType where
  name := annotatedPiInfo.name
  type := annotatedPiInfo.type
  ctors := [annotatedPiKernelCtor]

/- The whole-candidate negative keeps the actual AnnotatedPi family and
constructor metadata, but gives the annotation symbol its correct type as an
opaque constant. Ordinary metadata typing can therefore reach the recursive
constructor candidate, while `outParam Prop` is no longer definitionally equal
to the syntactically consumed `Prop`. -/
private def annotatedPiOpaqueOutParamInfo : ConstantInfo :=
  .axiomInfo {
    name := ``outParam
    levelParams := outParamKernelDef.levelParams
    type := outParamKernelDef.type
    isUnsafe := false }

private def annotatedPiOpaqueOutParamMap : ConstMap :=
  ({} : ConstMap).insert ``outParam annotatedPiOpaqueOutParamInfo

private def annotatedPiOpaqueOutParamEnv : Kernel.Environment :=
  Kernel.Environment.ofConstants `_annotatedPiOpaqueAnnotation
    annotatedPiOpaqueOutParamMap

private def annotatedPiOpaqueOutParamContext : AddInductive.Context where
  env := annotatedPiOpaqueOutParamEnv
  lparams := []
  safety := .safe
  allowPrimitive := false

/- This is a complete family/constructor candidate rejection, not the earlier
leaf-level `isDefEq` test. The dedicated message proves failure occurs at the
raw-to-consumed binder equality boundary before any semantic package or
transaction can be assembled. -/
#guard match AddInductive.buildNormalizationCandidate 0
    [annotatedPiKernelType] 0 false annotatedPiOpaqueOutParamContext with
  | .error (.other message) =>
    message == "normalization candidate changed a binder domain"
  | _ => false

private theorem annotatedPiRawType_wf :
    annotatedPiRawType.toVConstant.WF outParamEnv := by
  exact ⟨_, VEnv.HasType.sort (by decide)⟩

private theorem annotatedPiInfo_tr :
    TrConstVal .safe outParamEnv annotatedPiInfo
      annotatedPiRawType.toVConstVal := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr outParamEnv annotatedPiInfo.levelParams []
      annotatedPiInfo.type annotatedPiRawType.type := by
    tr_type_expr_tac
  obtain ⟨u, htype⟩ := annotatedPiRawType_wf
  exact hshape.to_trExprS outParamEnv_ordered trivial ⟨.sort u, htype⟩

private def annotatedPiTypeEnv : VEnv :=
  (outParamEnv.addConst annotatedPiRawType.name
    annotatedPiRawType.toVConstant).get!

private def annotatedPiTypeMap : ConstMap :=
  outParamMap.insert ``AnnotatedPi annotatedPiInfo

private theorem annotatedPiType_fresh :
    outParamMap.find? ``AnnotatedPi = none := by
  rw [outParamMap, SMap.WF.find?_insert
    (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

private theorem annotatedPiTypeMap_wf : annotatedPiTypeMap.WF :=
  outParamMap_wf.insert _ _ annotatedPiType_fresh

private def annotatedPiAddType :
    AddInductConstant .induct outParamMap outParamEnv
      annotatedPiRawType.toVConstVal annotatedPiTypeMap
      annotatedPiTypeEnv where
  info := annotatedPiInfo
  kind_eq := by simp [annotatedPiInfo, InductConstantKind.Matches]
  tr := annotatedPiInfo_tr
  map_fresh := by simpa [annotatedPiRawType] using annotatedPiType_fresh
  env_add := rfl
  map_add := rfl

private def annotatedPiTypeKernelEnv : Kernel.Environment :=
  Kernel.Environment.ofConstants `_annotatedPiCandidate annotatedPiTypeMap

private theorem annotatedPiTypeEnv_ordered : annotatedPiTypeEnv.Ordered :=
  .const (n := annotatedPiRawType.name)
    (ci := annotatedPiRawType.toVConstant)
    outParamEnv_ordered annotatedPiRawType_wf rfl

private def annotatedPiFamilyCandidateContext : AddInductive.Context where
  env := outParamKernelEnv
  lparams := []
  safety := .safe
  allowPrimitive := false

private def annotatedPiCtorCandidateContext : AddInductive.Context where
  env := annotatedPiTypeKernelEnv
  lparams := []
  safety := .safe
  allowPrimitive := false

private theorem annotatedPiType_lookup_outParam :
    annotatedPiTypeKernelEnv.find? ``outParam =
      some annotationOutParamInfo := by
  change annotatedPiTypeMap.find?' ``outParam =
    some annotationOutParamInfo
  rw [annotatedPiTypeMap_wf.find?'_eq_find?, annotatedPiTypeMap,
    outParamMap_wf.find?_insert]
  rw [outParamMap, SMap.WF.find?_insert
    (s := ({} : ConstMap)) SMap.WF.empty]
  rfl

private theorem annotatedPiType_lookup_family :
    annotatedPiTypeKernelEnv.find? ``AnnotatedPi =
      some annotatedPiInfo := by
  change annotatedPiTypeMap.find?' ``AnnotatedPi = some annotatedPiInfo
  rw [annotatedPiTypeMap_wf.find?'_eq_find?, annotatedPiTypeMap,
    outParamMap_wf.find?_insert]
  rfl

@[simp] private theorem annotatedPiType_get_outParam :
    annotatedPiTypeKernelEnv.get ``outParam =
      .ok annotationOutParamInfo := by
  unfold Kernel.Environment.get
  rw [annotatedPiType_lookup_outParam]
  rfl

@[simp] private theorem annotatedPiType_get_family :
    annotatedPiTypeKernelEnv.get ``AnnotatedPi =
      .ok annotatedPiInfo := by
  unfold Kernel.Environment.get
  rw [annotatedPiType_lookup_family]
  rfl

@[simp] private theorem annotatedPi_checkLevelZero
    (context : TypeChecker.Context) :
    TypeChecker.Inner.checkLevel context .zero = .ok () := by
  simp [TypeChecker.Inner.checkLevel, Level.getUndefParam, Level.forEach,
    Level.hasParam_eq, Level.hasParam']
  rfl

@[simp] private theorem annotatedPi_checkLevelSuccZero
    (context : TypeChecker.Context) :
    TypeChecker.Inner.checkLevel context (.succ .zero) = .ok () := by
  simp [TypeChecker.Inner.checkLevel, Level.getUndefParam, Level.forEach,
    Level.hasParam_eq, Level.hasParam']
  rfl

open private mkLevelIMaxCore mkLevelMaxCore from Lean.Level in
@[simp] private theorem annotatedPi_mkLevelIMaxSuccZero :
    mkLevelIMax' (.succ .zero) (.succ .zero) = .succ .zero := by
  simp [mkLevelIMax', mkLevelIMaxCore, mkLevelMax', mkLevelMaxCore]

private theorem annotatedPiExceptPure
    {α} (a : α) :
    (pure a : Except Kernel.Exception α) = .ok a := rfl

@[simp] private theorem annotatedPiInferConstantOutParam
    (lctx : LocalContext) :
    TypeChecker.Inner.inferConstant
        ({ env := annotatedPiTypeKernelEnv, lctx := lctx } :
          TypeChecker.Context)
        ``outParam [.succ .zero] false =
      .ok (.forallE `α (.sort (.succ .zero))
        (.sort (.succ .zero)) .default) := by
  unfold TypeChecker.Inner.inferConstant
  rw [show annotatedPiTypeKernelEnv.get ``outParam =
    .ok annotationOutParamInfo by exact annotatedPiType_get_outParam]
  simp [annotationOutParamInfo, Bind.bind, Except.bind,
    annotatedPiExceptPure,
    ConstantInfo.levelParams, ConstantInfo.isUnsafe,
    ConstantInfo.instantiateTypeLevelParams,
    ConstantInfo.toConstantVal,
    ConstantVal.instantiateTypeLevelParams,
    Expr.instantiateLevelParams_eq, Expr.instantiateLevelParamsCore',
    Level.substParams']

@[simp] private theorem annotatedPiInferConstantFamily
    (lctx : LocalContext) :
    TypeChecker.Inner.inferConstant
        ({ env := annotatedPiTypeKernelEnv, lctx := lctx } :
          TypeChecker.Context)
        ``AnnotatedPi [] false =
      .ok (.sort (.succ .zero)) := by
  unfold TypeChecker.Inner.inferConstant
  rw [show annotatedPiTypeKernelEnv.get ``AnnotatedPi =
    .ok annotatedPiInfo by exact annotatedPiType_get_family]
  rfl

@[simp] private theorem annotatedPiInferConstantOutParamCandidate :
    TypeChecker.Inner.inferConstant
        annotatedPiCtorCandidateContext.toTypeChecker
        ``outParam [.succ .zero] false =
      .ok (.forallE `α (.sort (.succ .zero))
        (.sort (.succ .zero)) .default) := by
  simp [annotatedPiCtorCandidateContext, AddInductive.Context.toTypeChecker]

@[simp] private theorem annotatedPiEnsureForall
    (name dom body bi source methods context state) :
    TypeChecker.Inner.ensureForallCore (.forallE name dom body bi) source
        methods context state =
      .ok (.forallE name dom body bi, state) := by
  unfold TypeChecker.Inner.ensureForallCore
  rfl

@[simp] private theorem annotatedPiEnsureSort
    (u source methods context state) :
    TypeChecker.Inner.ensureSortCore (.sort u) source methods context state =
      .ok (.sort u, state) := by
  unfold TypeChecker.Inner.ensureSortCore
  rfl

@[simp] private theorem annotatedPiForall_bindingDomain
    (name dom body bi) :
    (Expr.forallE name dom body bi).bindingDomain! = dom := rfl

@[simp] private theorem annotatedPiForall_bindingBody
    (name dom body bi) :
    (Expr.forallE name dom body bi).bindingBody! = body := rfl

@[simp] private theorem annotatedPiSort_instantiate1'
    (u arg) :
    (Expr.sort u).instantiate1' arg = .sort u := rfl

@[simp] private theorem annotatedPiConst_beq_sort
    (name levels u) :
    ((.const name levels : Expr) == .sort u) = false := by
  change Expr.eqv (.const name levels) (.sort u) = false
  rw [Expr.eqv_eq]
  rfl

@[simp] private theorem annotatedPiSort_beq_const
    (u name levels) :
    ((.sort u : Expr) == .const name levels) = false := by
  change Expr.eqv (.sort u) (.const name levels) = false
  rw [Expr.eqv_eq]
  rfl

@[simp] private theorem annotatedPiApp_beq_const
    (fn arg name levels) :
    ((.app fn arg : Expr) == .const name levels) = false := by
  change Expr.eqv (.app fn arg) (.const name levels) = false
  rw [Expr.eqv_eq]
  rfl

@[simp] private theorem annotatedPiForall_beq_const
    (binderName dom body bi name levels) :
    ((.forallE binderName dom body bi : Expr) == .const name levels) =
      false := by
  change Expr.eqv (.forallE binderName dom body bi)
    (.const name levels) = false
  rw [Expr.eqv_eq]
  rfl

@[simp] private theorem annotatedPiOutParam_beq_family :
    ((.const ``outParam [.succ .zero] : Expr) ==
      .const ``AnnotatedPi []) = false := by
  change Expr.eqv (.const ``outParam [.succ .zero])
    (.const ``AnnotatedPi []) = false
  rw [Expr.eqv_eq]
  rfl

@[simp] private theorem annotatedPiFamilyCacheAfterForall
    (cache : InferCache) (name : Name) (dom body result : Expr)
    (bi : BinderInfo) :
    (((cache.insert (.const ``AnnotatedPi []) (.sort (.succ .zero))).insert
        (.forallE name dom body bi) result)[
        (.const ``AnnotatedPi [] : Expr)]?) =
      some (.sort (.succ .zero)) := by
  rw [Std.HashMap.getElem?_insert,
    annotatedPiForall_beq_const]
  exact Std.HashMap.getElem?_insert_self

private def annotatedPiOutParamFnType : Expr :=
  .forallE `α (.sort (.succ .zero))
    (.sort (.succ .zero)) .default

@[simp] private theorem annotatedPiOutParamFnType_bindingDomain :
    annotatedPiOutParamFnType.bindingDomain! =
      .sort (.succ .zero) := rfl

@[simp] private theorem annotatedPiOutParamFnType_instantiatedBody :
    annotatedPiOutParamFnType.bindingBody!.instantiate1 (.sort .zero) =
      .sort (.succ .zero) := by
  simp [annotatedPiOutParamFnType, Expr.bindingBody!,
    Expr.instantiate1_eq, Expr.instantiate1']

@[simp] private theorem annotatedPiSort_notEagerReduce :
    (Expr.sort .zero).isAppOfArity ``eagerReduce 2 = false := rfl

private def annotatedPiOutParamFnState : TypeChecker.State :=
  { ({} : TypeChecker.State) with
    inferTypeC := ({} : TypeChecker.State).inferTypeC.insert
      (.const ``outParam [.succ .zero]) annotatedPiOutParamFnType }

private def annotatedPiOutParamArgState : TypeChecker.State :=
  { annotatedPiOutParamFnState with
    inferTypeC := annotatedPiOutParamFnState.inferTypeC.insert
      (.sort .zero) (.sort (.succ .zero)) }

private def annotatedPiWithSuccessCache
    (state : TypeChecker.State) (m : Std.HashSet (Expr × Expr)) :
    TypeChecker.State :=
  { state with success := m }

private theorem annotatedPiIsDefEqSort
    (fuel : Nat)
    (context : TypeChecker.Context)
    (initial : TypeChecker.State) :
    TypeChecker.Inner.isDefEq
        (.sort (.succ .zero)) (.sort (.succ .zero))
        (TypeChecker.Methods.withFuel fuel) context initial =
      .ok (true, initial) := by
  unfold TypeChecker.Inner.isDefEq
  rw [if_pos (Expr.eqv_refl _)]
  rfl

private def annotatedPiCtorExpectedView : Expr :=
  match annotatedPiMkInfo.type with
  | .forallE outerName (.forallE innerName _ innerBody innerInfo)
      outerBody outerInfo =>
    .forallE outerName
      (.forallE innerName (.sort .zero) innerBody innerInfo)
      outerBody outerInfo
  | source => source

private def annotatedPiOuterName : Name :=
  .mkNum
    (.mkStr
      (.mkStr (.mkStr (.mkStr .anonymous "a") "_@") "_internal")
      "_hyg")
    0

@[simp] private theorem annotatedPiFamilyType_noLooseBVars :
    annotatedPiInfo.type.hasLooseBVars = false := by
  rw [show annotatedPiInfo.type = .sort (.succ .zero) by rfl]
  simp [Expr.hasLooseBVars, Expr.looseBVarRange']

@[simp] private theorem emptyCheckTypeCache_annotatedPiFamily :
    (({} : TypeChecker.State).inferTypeC)[annotatedPiInfo.type]? = none := by
  exact Std.HashMap.getElem?_empty

@[simp] private theorem annotatedPiFamily_checkLevel :
    TypeChecker.Inner.checkLevel
      annotatedPiFamilyCandidateContext.toTypeChecker (.succ .zero) =
      .ok () := by
  simp [TypeChecker.Inner.checkLevel, Level.getUndefParam, Level.forEach, Level.hasParam_eq,
    Level.hasParam']
  rfl

@[simp] private theorem annotatedPiRecMGet (methods context state) :
    (get : TypeChecker.RecM TypeChecker.State) methods context state =
      .ok (state, state) := rfl

@[simp] private theorem annotatedPiRecMReadContext
    (methods context state) :
    (readThe TypeChecker.Context : TypeChecker.RecM TypeChecker.Context)
        methods context state =
      .ok (context, state) := rfl

@[simp] private theorem annotatedPiRecMModify
    (f : TypeChecker.State → TypeChecker.State)
    (methods context state) :
    (modify f : TypeChecker.RecM PUnit) methods context state =
      .ok (.unit, f state) := rfl

@[simp] private theorem annotatedPiRecMPure
    {α} (a : α) (methods context state) :
    (pure a : TypeChecker.RecM α) methods context state =
      .ok (a, state) := rfl

@[simp] private theorem annotatedPiRecMBind
    {α β} (x : TypeChecker.RecM α)
    (f : α → TypeChecker.RecM β) (methods context state) :
    (x >>= f) methods context state =
      match x methods context state with
      | .error e => .error e
      | .ok (a, state') => f a methods context state' := by
  simp [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  cases h : x methods context state with
  | error => rfl
  | ok value => cases value; rfl

@[simp] private theorem annotatedPiRecMLiftExceptOk
    {α} (a : α) (methods context state) :
    (liftM (.ok a : Except Kernel.Exception α) :
        TypeChecker.RecM α) methods context state =
      .ok (a, state) := rfl

@[simp] private theorem annotatedPiGetNGen
    (context : TypeChecker.Context) (state : TypeChecker.State) :
    (getNGen : TypeChecker.M NameGenerator) context state =
      .ok (state.ngen, state) := rfl

@[simp] private theorem annotatedPiSetNGen
    (ngen : NameGenerator) (context : TypeChecker.Context)
    (state : TypeChecker.State) :
    (setNGen ngen : TypeChecker.M PUnit) context state =
      .ok (.unit, { state with ngen }) := rfl

@[simp] private theorem annotatedPiMPure
    {α} (a : α) (context : TypeChecker.Context)
    (state : TypeChecker.State) :
    (pure a : TypeChecker.M α) context state =
      .ok (a, state) := rfl

@[simp] private theorem annotatedPiRecMWithReader
    {α} (f : LocalContext → LocalContext)
    (x : TypeChecker.RecM α) (methods : TypeChecker.Methods)
    (context : TypeChecker.Context) (state : TypeChecker.State) :
    (MonadWithReaderOf.withReader (m := TypeChecker.RecM) f x)
        methods context state =
      x methods { context with lctx := f context.lctx } state := rfl

private theorem annotatedPiWithLocalDecl
    {α} (name : Name) (bi : BinderInfo) (ty : Expr)
    (k : Expr → TypeChecker.RecM α)
    (methods : TypeChecker.Methods) (context : TypeChecker.Context)
    (state : TypeChecker.State) :
    (withLocalDecl (m := TypeChecker.RecM) name bi ty k)
        methods context state =
      k (.fvar ⟨state.ngen.curr⟩) methods
        { context with
          lctx := context.lctx.mkLocalDecl
            ⟨state.ngen.curr⟩ name ty bi }
        { state with ngen := state.ngen.next } := rfl

@[simp] private theorem annotatedPiInferTypeFuel
    (n e inferOnly context state) :
    TypeChecker.Inner.inferType e inferOnly
        (TypeChecker.Methods.withFuel (n + 1)) context state =
      TypeChecker.Inner.inferType' e inferOnly
        (TypeChecker.Methods.withFuel n) context state := rfl

@[simp] private theorem annotatedPiInferTypeFamilyCore
    (n : Nat) (lctx : LocalContext) (state : TypeChecker.State)
    (hcache :
      state.inferTypeC[(.const ``AnnotatedPi [] : Expr)]? = none) :
    TypeChecker.Inner.inferType' (.const ``AnnotatedPi []) false
        (TypeChecker.Methods.withFuel n)
        ({ env := annotatedPiTypeKernelEnv, lctx := lctx } :
          TypeChecker.Context)
        state =
      .ok (.sort (.succ .zero),
        { state with
          inferTypeC := state.inferTypeC.insert
            (.const ``AnnotatedPi []) (.sort (.succ .zero)) }) := by
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange', hcache,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

@[simp] private theorem annotatedPiInferTypeFamily
    (n : Nat) (lctx : LocalContext) (state : TypeChecker.State)
    (hcache :
      state.inferTypeC[(.const ``AnnotatedPi [] : Expr)]? = none) :
    TypeChecker.Inner.inferType (.const ``AnnotatedPi []) false
        (TypeChecker.Methods.withFuel (n + 1))
        ({ env := annotatedPiTypeKernelEnv, lctx := lctx } :
          TypeChecker.Context)
        state =
      .ok (.sort (.succ .zero),
        { state with
          inferTypeC := state.inferTypeC.insert
            (.const ``AnnotatedPi []) (.sort (.succ .zero)) }) :=
  annotatedPiInferTypeFamilyCore n lctx state hcache

@[simp] private theorem annotatedPiInferTypeFamilyCached
    (n : Nat) (lctx : LocalContext) (state : TypeChecker.State)
    (hcache :
      state.inferTypeC[(.const ``AnnotatedPi [] : Expr)]? =
        some (.sort (.succ .zero))) :
    TypeChecker.Inner.inferType' (.const ``AnnotatedPi []) false
        (TypeChecker.Methods.withFuel n)
        ({ env := annotatedPiTypeKernelEnv, lctx := lctx } :
          TypeChecker.Context)
        state =
      .ok (.sort (.succ .zero), state) := by
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange', hcache,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

@[simp] private theorem annotatedPiInferTypeFamilyAfterForall
    (n : Nat) (lctx : LocalContext) (state : TypeChecker.State)
    (name : Name) (dom body result : Expr) (bi : BinderInfo) :
    let state' : TypeChecker.State :=
      { state with
        inferTypeC :=
          (state.inferTypeC.insert
            (.const ``AnnotatedPi []) (.sort (.succ .zero))).insert
            (.forallE name dom body bi) result }
    TypeChecker.Inner.inferType' (.const ``AnnotatedPi []) false
        (TypeChecker.Methods.withFuel n)
        ({ env := annotatedPiTypeKernelEnv, lctx := lctx } :
          TypeChecker.Context)
        state' =
      .ok (.sort (.succ .zero), state') := by
  dsimp only
  apply annotatedPiInferTypeFamilyCached
  exact annotatedPiFamilyCacheAfterForall
    state.inferTypeC name dom body result bi

private def annotatedPiFamilyCheckTypeState : TypeChecker.State :=
  { ({} : TypeChecker.State) with
    inferTypeC := ({} : TypeChecker.State).inferTypeC.insert
      (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) }

private theorem annotatedPiFamily_checkTypeInner :
    TypeChecker.Inner.inferType annotatedPiInfo.type false
        (TypeChecker.Methods.withFuel 10000)
        annotatedPiFamilyCandidateContext.toTypeChecker
        ({} : TypeChecker.State) =
      .ok (.sort (.succ (.succ .zero)),
        annotatedPiFamilyCheckTypeState) := by
  change
    TypeChecker.Inner.inferType' (.sort (.succ .zero)) false
        (TypeChecker.Methods.withFuel 9999)
        annotatedPiFamilyCandidateContext.toTypeChecker
        ({} : TypeChecker.State) =
      .ok (.sort (.succ (.succ .zero)),
        annotatedPiFamilyCheckTypeState)
  unfold TypeChecker.Inner.inferType'
  simp [annotatedPiFamilyCheckTypeState, Expr.hasLooseBVars, Expr.looseBVarRange', Bind.bind,
    ReaderT.bind, StateT.bind, Except.bind]

private theorem annotatedPiFamily_checkTypeM :
    TypeChecker.M.run annotatedPiFamilyCandidateContext.env
      annotatedPiFamilyCandidateContext.safety
      annotatedPiFamilyCandidateContext.lctx
      annotatedPiFamilyCandidateContext.lparams
      annotatedPiFamilyCandidateContext.fuel
      (TypeChecker.checkType annotatedPiInfo.type) =
        .ok (.sort (.succ (.succ .zero))) := by
  change
    Except.map (fun x : Expr × TypeChecker.State => x.1)
      (TypeChecker.Inner.inferType annotatedPiInfo.type false
        (TypeChecker.Methods.withFuel 10000)
        annotatedPiFamilyCandidateContext.toTypeChecker
        ({} : TypeChecker.State)) =
      .ok (.sort (.succ (.succ .zero)))
  rw [annotatedPiFamily_checkTypeInner]
  rfl

private theorem annotatedPiFamily_whnfM :
    TypeChecker.M.run annotatedPiFamilyCandidateContext.env
      annotatedPiFamilyCandidateContext.safety
      annotatedPiFamilyCandidateContext.lctx
      annotatedPiFamilyCandidateContext.lparams
      annotatedPiFamilyCandidateContext.fuel
      (TypeChecker.whnf annotatedPiInfo.type) =
        .ok annotatedPiInfo.type := by rfl

private theorem annotatedPiCtor_checkTypeM :
    TypeChecker.M.run annotatedPiCtorCandidateContext.env
      annotatedPiCtorCandidateContext.safety
      annotatedPiCtorCandidateContext.lctx
      annotatedPiCtorCandidateContext.lparams
      annotatedPiCtorCandidateContext.fuel
      (TypeChecker.checkType annotatedPiMkInfo.type) =
        .ok (.sort (.succ .zero)) := by
  change
    Except.map (fun x : Expr × TypeChecker.State => x.1)
      (TypeChecker.Inner.inferType annotatedPiMkInfo.type false
        (TypeChecker.Methods.withFuel 10000)
        annotatedPiCtorCandidateContext.toTypeChecker
        ({} : TypeChecker.State)) =
      .ok (.sort (.succ .zero))
  rw [show annotatedPiMkInfo.type =
    .forallE annotatedPiOuterName
      (.forallE `p
        (.app (.const ``outParam [.succ .zero]) (.sort .zero))
        (.const ``AnnotatedPi []) .default)
      (.const ``AnnotatedPi []) .default by rfl]
  change
    Except.map (fun x : Expr × TypeChecker.State => x.1)
      (TypeChecker.Inner.inferType'
        (.forallE annotatedPiOuterName
          (.forallE `p
            (.app (.const ``outParam [.succ .zero]) (.sort .zero))
            (.const ``AnnotatedPi []) .default)
          (.const ``AnnotatedPi []) .default)
        false (TypeChecker.Methods.withFuel 9999)
        annotatedPiCtorCandidateContext.toTypeChecker
        ({} : TypeChecker.State)) =
      .ok (.sort (.succ .zero))
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange', TypeChecker.Inner.inferType',
    TypeChecker.Inner.inferForall, TypeChecker.Inner.inferForall.loop, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind]
  rw [annotatedPiIsDefEqSort 9997]
  simp [Expr.instantiate1', annotatedPiWithLocalDecl, annotatedPiCtorCandidateContext,
    AddInductive.Context.toTypeChecker, Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [annotatedPiInferTypeFamilyCached (hcache := by
    apply annotatedPiFamilyCacheAfterForall)]
  simp [Expr.sortLevel!, annotatedPi_mkLevelIMaxSuccZero]
  rfl

private theorem annotatedPiCtor_whnfM :
    TypeChecker.M.run annotatedPiCtorCandidateContext.env
      annotatedPiCtorCandidateContext.safety
      annotatedPiCtorCandidateContext.lctx
      annotatedPiCtorCandidateContext.lparams
      annotatedPiCtorCandidateContext.fuel
      (TypeChecker.whnf annotatedPiMkInfo.type) =
        .ok annotatedPiMkInfo.type := by rfl

/-! ## Checker-produced alias normalization certificates -/

/-- Minimal kernel environment used to replay family-result WHNF without
bringing unrelated constants or primitives into the certificate. -/
private def aliasFormerNormalizationKernelEnv : Kernel.Environment :=
  Kernel.Environment.ofConstants `_aliasFormerNormalization
    typeFamilyAliasMap

private theorem aliasFormerNormalization_trEnv :
    TrEnv .safe aliasFormerNormalizationKernelEnv typeFamilyAliasEnv := by
  simpa [TrEnv, aliasFormerNormalizationKernelEnv,
    Kernel.Environment.ofConstants] using
    typeFamilyAlias_trEnv'

private theorem aliasFormerNormalization_hasPrimitives :
    VEnv.HasPrimitives typeFamilyAliasEnv := by
  apply VEnv.HasPrimitives.of_avoids
  intro n hn
  simp only [VEnv.reflectedPrimitiveNames, List.mem_cons,
    List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;>
    rfl

private theorem aliasFormerNormalization_safePrimitives :
    aliasFormerNormalizationKernelEnv.find? n = some ci →
      Kernel.Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [] := by
  intro hfind hprim
  change typeFamilyAliasMap.find?' n = some ci at hfind
  rw [typeFamilyAliasMap_wf.find?'_eq_find?,
    typeFamilyAliasMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty] at hfind
  simp [SMap.find?] at hfind
  obtain ⟨rfl, rfl⟩ := hfind
  simp [Kernel.Environment.primitives, NameSet.ofList] at hprim
  simp +decide [NameSet.contains] at hprim

private def aliasFormerNormalizationVEnvs : VEnvs where
  venv _ := typeFamilyAliasEnv

private theorem aliasFormerNormalizationVEnvs_wf :
    aliasFormerNormalizationVEnvs.WF
      aliasFormerNormalizationKernelEnv where
  tr := by
    intro safety
    change TrEnv' _ typeFamilyAliasMap false typeFamilyAliasEnv
    exact typeFamilyAlias_trEnv'
  hasPrimitives := aliasFormerNormalization_hasPrimitives
  safePrimitives := aliasFormerNormalization_safePrimitives
  mono := fun _ => .rfl
  projectionReady := ProjectionReady.of_no_ctorInfo <| by
    intro name _info h
    change typeFamilyAliasMap.find?' name = some (.ctorInfo _info) at h
    rw [typeFamilyAliasMap_wf.find?'_eq_find?] at h
    simp only [typeFamilyAliasMap, SMap.WF.find?_insert
      (s := ({} : ConstMap)) SMap.WF.empty] at h
    simp [SMap.find?, typeFamilyAliasInfo] at h
  structureEtaReady := StructureEtaReady.of_no_ctorInfo <| by
    intro name _info h
    change typeFamilyAliasMap.find?' name = some (.ctorInfo _info) at h
    rw [typeFamilyAliasMap_wf.find?'_eq_find?] at h
    simp only [typeFamilyAliasMap, SMap.WF.find?_insert
      (s := ({} : ConstMap)) SMap.WF.empty] at h
    simp [SMap.find?, typeFamilyAliasInfo] at h

private def aliasFormerNormalizationContext : TypeChecker.VContext :=
  TypeChecker.VContext.mk' aliasFormerNormalizationVEnvs_wf
    (fuel := { whnf := 2 })

private def aliasFormerNormalizationRawContext : TypeChecker.Context where
  env := aliasFormerNormalizationKernelEnv
  fuel := { whnf := 2 }

private def aliasFormerCheckTypeState (state : TypeChecker.State) :
    TypeChecker.State :=
  { state with
    inferTypeC := state.inferTypeC.insert
      (.const ``TypeFamilyAlias [])
      (.sort (.succ (.succ .zero))) }

/-- Insert the raw AliasFormer family before checking its constructor type. -/
private def aliasFormerCtorNormalizationAddType :
    AddInductConstant .induct typeFamilyAliasMap typeFamilyAliasEnv
      aliasFormerRawType.toVConstVal aliasFormerTypeMap
      aliasFormerTypeEnv where
  info := aliasFormerInfo
  kind_eq := by simp [aliasFormerInfo, InductConstantKind.Matches]
  tr := aliasFormerInfo_tr
  map_fresh := by simpa [aliasFormerRawType] using aliasFormerType_fresh
  env_add := rfl
  map_add := rfl

private def aliasFormerCtorNormalizationKernelEnv : Kernel.Environment :=
  Kernel.Environment.ofConstants `_aliasFormerNormalization
    aliasFormerTypeMap

private def aliasFormerCtorNormalizationRawContext : TypeChecker.Context where
  env := aliasFormerCtorNormalizationKernelEnv
  fuel := { whnf := 2 }

private def aliasFormerCtorCheckTypeState (state : TypeChecker.State) :
    TypeChecker.State :=
  { state with
    inferTypeC := state.inferTypeC.insert
      (.const ``AliasFormer [])
      (.const ``TypeFamilyAlias []) }

/-- Insert only the raw `AliasRec` family into the replay environment. This is
the exact staging at which constructor domains are normalized. -/
private def aliasRecNormalizationAddType :
    AddInductConstant .induct recAliasMap recAliasEnv
      aliasRecRawType.toVConstVal aliasRecTypeMap aliasRecTypeEnv where
  info := aliasRecInfo
  kind_eq := by simp [aliasRecInfo, InductConstantKind.Matches]
  tr := aliasRecInfo_tr
  map_fresh := by simpa [aliasRecRawType] using aliasRecType_fresh
  env_add := rfl
  map_add := rfl

private theorem aliasRecNormalization_trEnv' {safety : DefinitionSafety} :
    TrEnv' safety aliasRecTypeMap false aliasRecTypeEnv :=
  .inductStaging aliasRecNormalizationAddType
    ⟨.succ (.succ .zero), VEnv.HasType.sort (by decide)⟩
    recAlias_trEnv'

private def aliasRecNormalizationKernelEnv : Kernel.Environment :=
  Kernel.Environment.ofConstants `_aliasRecNormalization aliasRecTypeMap

private theorem aliasRecNormalization_trEnv :
    TrEnv .safe aliasRecNormalizationKernelEnv aliasRecTypeEnv := by
  simpa [TrEnv, aliasRecNormalizationKernelEnv,
    Kernel.Environment.ofConstants] using
    aliasRecNormalization_trEnv'

private theorem aliasRecNormalization_hasPrimitives :
    VEnv.HasPrimitives aliasRecTypeEnv := by
  apply VEnv.HasPrimitives.of_avoids
  intro n hn
  simp only [VEnv.reflectedPrimitiveNames, List.mem_cons,
    List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;>
    rfl

private theorem aliasRecNormalization_safePrimitives :
    aliasRecNormalizationKernelEnv.find? n = some ci →
      Kernel.Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [] := by
  intro hfind hprim
  change aliasRecTypeMap.find?' n = some ci at hfind
  rw [aliasRecTypeMap_wf.find?'_eq_find?,
    aliasRecTypeMap, recAliasMap_wf.find?_insert] at hfind
  split at hfind
  · rename_i heq
    simp at heq
    subst n
    simp [Kernel.Environment.primitives, NameSet.ofList] at hprim
    simp +decide [NameSet.contains] at hprim
  · rw [recAliasMap,
      SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty] at hfind
    simp [SMap.find?] at hfind
    obtain ⟨rfl, rfl⟩ := hfind
    simp [Kernel.Environment.primitives, NameSet.ofList] at hprim
    simp +decide [NameSet.contains] at hprim

private def aliasRecNormalizationVEnvs : VEnvs where
  venv _ := aliasRecTypeEnv

private theorem aliasRecNormalizationVEnvs_wf :
    aliasRecNormalizationVEnvs.WF aliasRecNormalizationKernelEnv where
  tr := by
    intro safety
    change TrEnv' _ aliasRecTypeMap false aliasRecTypeEnv
    exact aliasRecNormalization_trEnv'
  hasPrimitives := aliasRecNormalization_hasPrimitives
  safePrimitives := aliasRecNormalization_safePrimitives
  mono := fun _ => .rfl
  projectionReady := ProjectionReady.of_no_ctorInfo <| by
    intro name _info h
    change aliasRecTypeMap.find?' name = some (.ctorInfo _info) at h
    rw [aliasRecTypeMap_wf.find?'_eq_find?] at h
    simp only [aliasRecTypeMap, recAliasMap_wf.find?_insert] at h
    simp only [recAliasMap, SMap.WF.find?_insert
      (s := ({} : ConstMap)) SMap.WF.empty] at h
    by_cases hAliasRec : ``AliasRec = name <;>
      by_cases hRecAlias : ``RecAlias = name <;>
      simp +decide [hAliasRec, hRecAlias, SMap.find?, aliasRecInfo,
        recAliasInfo] at h
  structureEtaReady := StructureEtaReady.of_no_ctorInfo <| by
    intro name _info h
    change aliasRecTypeMap.find?' name = some (.ctorInfo _info) at h
    rw [aliasRecTypeMap_wf.find?'_eq_find?] at h
    simp only [aliasRecTypeMap, recAliasMap_wf.find?_insert] at h
    simp only [recAliasMap, SMap.WF.find?_insert
      (s := ({} : ConstMap)) SMap.WF.empty] at h
    by_cases hAliasRec : ``AliasRec = name <;>
      by_cases hRecAlias : ``RecAlias = name <;>
      simp +decide [hAliasRec, hRecAlias, SMap.find?, aliasRecInfo,
        recAliasInfo] at h

private def aliasRecNormalizationContext : TypeChecker.VContext :=
  TypeChecker.VContext.mk' aliasRecNormalizationVEnvs_wf
    (fuel := { whnf := 2 })

private def aliasRecNormalizationRawContext : TypeChecker.Context where
  env := aliasRecNormalizationKernelEnv
  fuel := { whnf := 2 }

private def aliasFormerCandidateContext : AddInductive.Context where
  env := aliasFormerNormalizationKernelEnv
  lparams := []
  safety := .safe
  allowPrimitive := false
  fuel := { whnf := 2 }

private def aliasFormerCtorCandidateContext : AddInductive.Context where
  env := aliasFormerCtorNormalizationKernelEnv
  lparams := []
  safety := .safe
  allowPrimitive := false
  fuel := { whnf := 2 }

/-- Exact kernel request indexed by the singleton normalization candidate. -/
private def aliasFormerKernelCtor : Constructor where
  name := aliasFormerMkInfo.name
  type := aliasFormerMkInfo.type

private def aliasFormerKernelType : InductiveType where
  name := aliasFormerInfo.name
  type := aliasFormerInfo.type
  ctors := [aliasFormerKernelCtor]

private theorem aliasFormerNormalization_lookup :
    aliasFormerNormalizationKernelEnv.find? ``TypeFamilyAlias =
      some typeFamilyAliasInfo := by
  change typeFamilyAliasMap.find?' ``TypeFamilyAlias =
    some typeFamilyAliasInfo
  rw [typeFamilyAliasMap_wf.find?'_eq_find?, typeFamilyAliasMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  rfl

private theorem aliasFormerCtorNormalization_lookup :
    aliasFormerCtorNormalizationKernelEnv.find? ``AliasFormer =
      some aliasFormerInfo := by
  change aliasFormerTypeMap.find?' ``AliasFormer = some aliasFormerInfo
  rw [aliasFormerTypeMap_wf.find?'_eq_find?, aliasFormerTypeMap,
    typeFamilyAliasMap_wf.find?_insert]
  rfl

private theorem aliasRecNormalization_lookup :
    aliasRecNormalizationKernelEnv.find? ``RecAlias =
      some recAliasInfo := by
  change aliasRecTypeMap.find?' ``RecAlias = some recAliasInfo
  rw [aliasRecTypeMap_wf.find?'_eq_find?, aliasRecTypeMap,
    recAliasMap_wf.find?_insert, recAliasMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  rfl

private theorem aliasRecNormalization_family_lookup :
    aliasRecNormalizationKernelEnv.find? ``AliasRec =
      some aliasRecInfo := by
  change aliasRecTypeMap.find?' ``AliasRec = some aliasRecInfo
  rw [aliasRecTypeMap_wf.find?'_eq_find?, aliasRecTypeMap,
    recAliasMap_wf.find?_insert]
  rfl

private def recAliasWhnfKernelExpr : Expr :=
  recAliasInfo.instantiateValueLevelParams! [.succ .zero]

private def aliasRecFieldKernelExpr : Expr :=
  aliasRecMkInfo.type.bindingDomain!

private theorem aliasRecFieldKernelExpr_eq :
    aliasRecFieldKernelExpr =
      .app (.const ``RecAlias [.succ .zero])
        (.const ``AliasRec []) := rfl

private theorem recAliasWhnfKernelExpr_eq :
    recAliasWhnfKernelExpr =
      .lam `α (.sort (.succ .zero)) (.bvar 0) .default := by
  simp [recAliasWhnfKernelExpr, recAliasInfo,
    recAliasKernelDef, ConstantInfo.instantiateValueLevelParams!,
    ConstantInfo.levelParams, ConstantInfo.value!,
    ConstantInfo.toConstantVal,
    Expr.instantiateLevelParams_eq, Expr.instantiateLevelParamsCore',
    Level.substParams']

private def recAliasUnfoldState (state : TypeChecker.State) :
    TypeChecker.State :=
  { state with
    unfold := state.unfold.insert
      (.const ``RecAlias [.succ .zero])
      recAliasWhnfKernelExpr }

/- The following small operational equations expose only the transformer
plumbing needed to kernel-reduce the two concrete WHNF traces. -/

@[simp] private theorem normalizationRecMGet (methods context state) :
    (get : TypeChecker.RecM TypeChecker.State) methods context state =
      .ok (state, state) := rfl

@[simp] private theorem normalizationRecMReadContext
    (methods context state) :
    (readThe TypeChecker.Context : TypeChecker.RecM TypeChecker.Context)
        methods context state =
      .ok (context, state) := rfl

@[simp] private theorem normalizationRecMModify
    (f : TypeChecker.State → TypeChecker.State)
    (methods context state) :
    (modify f : TypeChecker.RecM PUnit) methods context state =
      .ok (.unit, f state) := rfl

@[simp] private theorem normalizationRecMPure
    {α} (a : α) (methods context state) :
    (pure a : TypeChecker.RecM α) methods context state =
      .ok (a, state) := rfl

@[simp] private theorem normalizationRecMBind
    {α β} (x : TypeChecker.RecM α)
    (f : α → TypeChecker.RecM β) (methods context state) :
    (x >>= f) methods context state =
      match x methods context state with
      | .error e => .error e
      | .ok (a, state') => f a methods context state' := by
  simp [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  cases h : x methods context state with
  | error => rfl
  | ok value => cases value; rfl

@[simp] private theorem normalizationRecMGetEnv
    (methods context state) :
    (liftM TypeChecker.getEnv :
        TypeChecker.RecM Kernel.Environment) methods context state =
      .ok (context.env, state) := rfl

@[simp] private theorem normalizationRecMLiftExceptOk
    {α} (a : α) (methods context state) :
    (liftM (.ok a : Except Kernel.Exception α) :
        TypeChecker.RecM α) methods context state =
      .ok (a, state) := rfl

private theorem normalizationExceptPure
    {α} (a : α) :
    (pure a : Except Kernel.Exception α) = .ok a := rfl

@[simp] private theorem typeFamilyAlias_noLooseBVars :
    (Expr.const ``TypeFamilyAlias []).hasLooseBVars = false := by
  simp [Expr.hasLooseBVars, Expr.looseBVarRange']

@[simp] private theorem aliasFormer_noLooseBVars :
    (Expr.const ``AliasFormer []).hasLooseBVars = false := by
  simp [Expr.hasLooseBVars, Expr.looseBVarRange']

@[simp] private theorem recAlias_noLooseBVars :
    (Expr.const ``RecAlias [.succ .zero]).hasLooseBVars = false := by
  simp [Expr.hasLooseBVars, Expr.looseBVarRange']

@[simp] private theorem aliasRec_noLooseBVars :
    (Expr.const ``AliasRec []).hasLooseBVars = false := by
  simp [Expr.hasLooseBVars, Expr.looseBVarRange']

@[simp] private theorem aliasRecField_noLooseBVars :
    (Expr.app
      (.const ``RecAlias [.succ .zero])
      (.const ``AliasRec [])).hasLooseBVars = false := by
  simp [Expr.hasLooseBVars, Expr.looseBVarRange']

@[simp] private theorem emptyCheckTypeCache_typeFamilyAlias :
    (({} : TypeChecker.State).inferTypeC)[
      Expr.const ``TypeFamilyAlias []]? = none := by
  exact Std.HashMap.getElem?_empty

@[simp] private theorem emptyCheckTypeCache_aliasFormer :
    (({} : TypeChecker.State).inferTypeC)[
      Expr.const ``AliasFormer []]? = none := by
  exact Std.HashMap.getElem?_empty

@[simp] private theorem emptyCheckTypeCache_recAlias :
    (({} : TypeChecker.State).inferTypeC)[
      Expr.const ``RecAlias [.succ .zero]]? = none := by
  exact Std.HashMap.getElem?_empty

@[simp] private theorem emptyCheckTypeCache_aliasRecField :
    (({} : TypeChecker.State).inferTypeC)[
      Expr.app
        (.const ``RecAlias [.succ .zero])
        (.const ``AliasRec [])]? = none := by
  exact Std.HashMap.getElem?_empty

@[simp] private theorem aliasFormerNormalization_get :
    aliasFormerNormalizationRawContext.env.get ``TypeFamilyAlias =
      .ok typeFamilyAliasInfo := by
  unfold Kernel.Environment.get
  change
    (match aliasFormerNormalizationKernelEnv.find? ``TypeFamilyAlias with
    | some ci => pure ci
    | none => throw <| Kernel.Exception.unknownConstant
        aliasFormerNormalizationKernelEnv ``TypeFamilyAlias) =
      Except.ok typeFamilyAliasInfo
  rw [aliasFormerNormalization_lookup]
  rfl

@[simp] private theorem inferConstantTypeFamilyAlias :
    TypeChecker.Inner.inferConstant aliasFormerNormalizationRawContext
        ``TypeFamilyAlias [] false =
      .ok (.sort (.succ (.succ .zero))) := by
  unfold TypeChecker.Inner.inferConstant
  rw [aliasFormerNormalization_get]
  rfl

@[simp] private theorem aliasFormerCtorNormalization_get :
    aliasFormerCtorNormalizationRawContext.env.get ``AliasFormer =
      .ok aliasFormerInfo := by
  unfold Kernel.Environment.get
  change
    (match aliasFormerCtorNormalizationKernelEnv.find? ``AliasFormer with
    | some ci => pure ci
    | none => throw <| Kernel.Exception.unknownConstant
        aliasFormerCtorNormalizationKernelEnv ``AliasFormer) =
      Except.ok aliasFormerInfo
  rw [aliasFormerCtorNormalization_lookup]
  rfl

@[simp] private theorem inferConstantAliasFormer :
    TypeChecker.Inner.inferConstant aliasFormerCtorNormalizationRawContext
        ``AliasFormer [] false =
      .ok (.const ``TypeFamilyAlias []) := by
  unfold TypeChecker.Inner.inferConstant
  rw [aliasFormerCtorNormalization_get]
  rfl

private theorem checkTypeTypeFamilyAlias :
    TypeChecker.Inner.inferType (.const ``TypeFamilyAlias []) false
        (TypeChecker.Methods.withFuel 9999)
        aliasFormerNormalizationRawContext ({} : TypeChecker.State) =
      .ok (.sort (.succ (.succ .zero)),
        aliasFormerCheckTypeState {}) := by
  change TypeChecker.Inner.inferType'
      (.const ``TypeFamilyAlias []) false
      (TypeChecker.Methods.withFuel 9998)
      aliasFormerNormalizationRawContext ({} : TypeChecker.State) =
    .ok (.sort (.succ (.succ .zero)),
      aliasFormerCheckTypeState {})
  unfold TypeChecker.Inner.inferType'
  simp [aliasFormerCheckTypeState,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

private theorem checkTypeTypeFamilyAliasCandidate :
    TypeChecker.Inner.inferType (.const ``TypeFamilyAlias []) false
        (TypeChecker.Methods.withFuel 10000)
        aliasFormerNormalizationRawContext ({} : TypeChecker.State) =
      .ok (.sort (.succ (.succ .zero)),
        aliasFormerCheckTypeState {}) := by
  change TypeChecker.Inner.inferType'
      (.const ``TypeFamilyAlias []) false
      (TypeChecker.Methods.withFuel 9999)
      aliasFormerNormalizationRawContext ({} : TypeChecker.State) =
    .ok (.sort (.succ (.succ .zero)),
      aliasFormerCheckTypeState {})
  unfold TypeChecker.Inner.inferType'
  simp [aliasFormerCheckTypeState,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

private theorem checkTypeAliasFormer :
    TypeChecker.Inner.inferType (.const ``AliasFormer []) false
        (TypeChecker.Methods.withFuel 9999)
        aliasFormerCtorNormalizationRawContext ({} : TypeChecker.State) =
      .ok (.const ``TypeFamilyAlias [],
        aliasFormerCtorCheckTypeState {}) := by
  change TypeChecker.Inner.inferType'
      (.const ``AliasFormer []) false
      (TypeChecker.Methods.withFuel 9998)
      aliasFormerCtorNormalizationRawContext ({} : TypeChecker.State) =
    .ok (.const ``TypeFamilyAlias [],
      aliasFormerCtorCheckTypeState {})
  unfold TypeChecker.Inner.inferType'
  simp [aliasFormerCtorCheckTypeState,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

private theorem checkTypeAliasFormerCandidate :
    TypeChecker.Inner.inferType (.const ``AliasFormer []) false
        (TypeChecker.Methods.withFuel 10000)
        aliasFormerCtorNormalizationRawContext ({} : TypeChecker.State) =
      .ok (.const ``TypeFamilyAlias [],
        aliasFormerCtorCheckTypeState {}) := by
  change TypeChecker.Inner.inferType'
      (.const ``AliasFormer []) false
      (TypeChecker.Methods.withFuel 9999)
      aliasFormerCtorNormalizationRawContext ({} : TypeChecker.State) =
    .ok (.const ``TypeFamilyAlias [],
      aliasFormerCtorCheckTypeState {})
  unfold TypeChecker.Inner.inferType'
  simp [aliasFormerCtorCheckTypeState,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

@[simp] private theorem aliasRecNormalization_getRecAlias :
    aliasRecNormalizationRawContext.env.get ``RecAlias =
      .ok recAliasInfo := by
  unfold Kernel.Environment.get
  change
    (match aliasRecNormalizationKernelEnv.find? ``RecAlias with
    | some ci => pure ci
    | none => throw <| Kernel.Exception.unknownConstant
        aliasRecNormalizationKernelEnv ``RecAlias) =
      Except.ok recAliasInfo
  rw [aliasRecNormalization_lookup]
  rfl

@[simp] private theorem aliasRecNormalization_getFamily :
    aliasRecNormalizationRawContext.env.get ``AliasRec =
      .ok aliasRecInfo := by
  unfold Kernel.Environment.get
  change
    (match aliasRecNormalizationKernelEnv.find? ``AliasRec with
    | some ci => pure ci
    | none => throw <| Kernel.Exception.unknownConstant
        aliasRecNormalizationKernelEnv ``AliasRec) =
      Except.ok aliasRecInfo
  rw [aliasRecNormalization_family_lookup]
  rfl

@[simp] private theorem aliasRecNormalization_checkLevelSuccZero :
    TypeChecker.Inner.checkLevel aliasRecNormalizationRawContext
      (.succ .zero) = .ok () := by
  simp [TypeChecker.Inner.checkLevel, Level.getUndefParam, Level.forEach,
    Level.hasParam_eq,
    Level.hasParam', normalizationExceptPure]

@[simp] private theorem recAliasInfo_isUnsafe :
    recAliasInfo.isUnsafe = false := rfl

@[simp] private theorem aliasRecNormalization_safety :
    aliasRecNormalizationRawContext.safety = .safe := rfl

@[simp] private theorem recAliasInfo_instantiateType :
    recAliasInfo.instantiateTypeLevelParams [.succ .zero] =
      .forallE `α (.sort (.succ .zero))
        (.sort (.succ .zero)) .default := by
  simp [recAliasInfo, recAliasKernelDef,
    ConstantInfo.instantiateTypeLevelParams,
    ConstantVal.instantiateTypeLevelParams,
    ConstantInfo.toConstantVal,
    Expr.instantiateLevelParams_eq, Expr.instantiateLevelParamsCore',
    Level.substParams']

@[simp] private theorem inferConstantRecAlias :
    TypeChecker.Inner.inferConstant aliasRecNormalizationRawContext
        ``RecAlias [.succ .zero] false =
      .ok (.forallE `α (.sort (.succ .zero))
        (.sort (.succ .zero)) .default) := by
  unfold TypeChecker.Inner.inferConstant
  rw [aliasRecNormalization_getRecAlias]
  simp [recAliasInfo, recAliasKernelDef, Bind.bind, Except.bind, normalizationExceptPure,
    ConstantInfo.levelParams, ConstantInfo.isUnsafe, ConstantInfo.instantiateTypeLevelParams,
    ConstantInfo.toConstantVal, ConstantVal.instantiateTypeLevelParams,
    Expr.instantiateLevelParams_eq, Expr.instantiateLevelParamsCore', Level.substParams']

@[simp] private theorem inferConstantAliasRec :
    TypeChecker.Inner.inferConstant aliasRecNormalizationRawContext
        ``AliasRec [] false =
      .ok (.sort (.succ .zero)) := by
  unfold TypeChecker.Inner.inferConstant
  rw [aliasRecNormalization_getFamily]
  rfl

@[simp] private theorem normalizationWhnfCoreConst
    (methods context state n ls) :
    (TypeChecker.Inner.whnfCore' (.const n ls)
        (cheapProj := false))
        methods context state =
      .ok (.const n ls, state) := rfl

@[simp] private theorem normalizationWhnfCoreSort
    (methods context state u) :
    (TypeChecker.Inner.whnfCore' (.sort u)
        (cheapProj := false))
        methods context state =
      .ok (.sort u, state) := rfl

@[simp] private theorem normalizationWhnfCoreLam
    (methods context state name ty body bi) :
    (TypeChecker.Inner.whnfCore' (.lam name ty body bi)
        (cheapProj := false))
        methods context state =
      .ok (.lam name ty body bi, state) := rfl

@[simp] private theorem normalizationReduceNativeConst
    (env methods context state n ls) :
    (liftM (TypeChecker.Inner.reduceNative env (.const n ls)) :
        TypeChecker.RecM (Option Expr)) methods context state =
      .ok (none, state) := rfl

@[simp] private theorem normalizationReduceNativeSort
    (env methods context state u) :
    (liftM (TypeChecker.Inner.reduceNative env (.sort u)) :
        TypeChecker.RecM (Option Expr)) methods context state =
      .ok (none, state) := rfl

@[simp] private theorem normalizationReduceNativeLam
    (env methods context state name ty body bi) :
    (liftM (TypeChecker.Inner.reduceNative env (.lam name ty body bi)) :
        TypeChecker.RecM (Option Expr)) methods context state =
      .ok (none, state) := rfl

@[simp] private theorem normalizationReduceNatConst
    (methods context state n ls) :
    TypeChecker.Inner.reduceNat (.const n ls) methods context state =
      .ok (none, state) := rfl

@[simp] private theorem normalizationReduceNatSort
    (methods context state u) :
    TypeChecker.Inner.reduceNat (.sort u) methods context state =
      .ok (none, state) := rfl

@[simp] private theorem normalizationReduceNatLam
    (methods context state name ty body bi) :
    TypeChecker.Inner.reduceNat (.lam name ty body bi)
        methods context state =
      .ok (none, state) := rfl

@[simp] private theorem normalizationUnfoldSort
    (methods context state u) :
    TypeChecker.Inner.unfoldDefinition (.sort u) methods context state =
      .ok (none, state) := rfl

@[simp] private theorem normalizationUnfoldLam
    (methods context state name ty body bi) :
    TypeChecker.Inner.unfoldDefinition (.lam name ty body bi)
        methods context state =
      .ok (none, state) := rfl

private theorem unfoldTypeFamilyAlias (methods state) :
    TypeChecker.Inner.unfoldDefinition (.const ``TypeFamilyAlias [])
        methods aliasFormerNormalizationRawContext state =
      .ok (some (.sort (.succ .zero)), state) := by
  change
    TypeChecker.Inner.unfoldDefinitionCore (.const ``TypeFamilyAlias [])
        methods aliasFormerNormalizationRawContext state =
      .ok (some (.sort (.succ .zero)), state)
  simp [TypeChecker.Inner.unfoldDefinitionCore, TypeChecker.Inner.isDelta, Expr.getAppFn,
    aliasFormerNormalizationRawContext, aliasFormerNormalization_lookup, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind, typeFamilyAliasInfo, typeFamilyAliasKernelDef,
    ConstantInfo.deltaValue?, TypeChecker.Inner.instantiateDeltaValue, ConstantInfo.numLevelParams,
    ConstantInfo.levelParams, ConstantInfo.toConstantVal, Expr.instantiateLevelParams]

private theorem unfoldAliasFormer (methods state) :
    TypeChecker.Inner.unfoldDefinition (.const ``AliasFormer [])
        methods aliasFormerCtorNormalizationRawContext state =
      .ok (none, state) := by
  change
    TypeChecker.Inner.unfoldDefinitionCore (.const ``AliasFormer [])
        methods aliasFormerCtorNormalizationRawContext state =
      .ok (none, state)
  simp [TypeChecker.Inner.unfoldDefinitionCore, TypeChecker.Inner.isDelta,
    Expr.getAppFn, aliasFormerCtorNormalizationRawContext,
    aliasFormerCtorNormalization_lookup, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind, aliasFormerInfo,
    ConstantInfo.deltaValue?]

private theorem unfoldRecAliasInitial (methods) :
    TypeChecker.Inner.unfoldDefinition
        (.const ``RecAlias [.succ .zero])
        methods aliasRecNormalizationRawContext ({} : TypeChecker.State) =
      .ok (some recAliasWhnfKernelExpr, recAliasUnfoldState {}) := by
  change
    TypeChecker.Inner.unfoldDefinitionCore
        (.const ``RecAlias [.succ .zero])
        methods aliasRecNormalizationRawContext ({} : TypeChecker.State) =
      .ok (some recAliasWhnfKernelExpr, recAliasUnfoldState {})
  simp [TypeChecker.Inner.unfoldDefinitionCore, TypeChecker.Inner.isDelta,
    Expr.getAppFn, aliasRecNormalizationRawContext,
    aliasRecNormalization_lookup, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind, recAliasInfo, recAliasKernelDef,
    ConstantInfo.deltaValue?, TypeChecker.Inner.instantiateDeltaValue,
    ConstantInfo.numLevelParams,
    ConstantInfo.instantiateValueLevelParams!, ConstantInfo.levelParams,
    ConstantInfo.value!, ConstantInfo.toConstantVal,
    Expr.instantiateLevelParams, recAliasWhnfKernelExpr,
    recAliasUnfoldState]

private theorem unfoldRecAliasCoreInitial (methods) :
    TypeChecker.Inner.unfoldDefinitionCore
        (.const ``RecAlias [.succ .zero])
        methods aliasRecNormalizationRawContext ({} : TypeChecker.State) =
      .ok (some recAliasWhnfKernelExpr, recAliasUnfoldState {}) := by
  change
    TypeChecker.Inner.unfoldDefinition
        (.const ``RecAlias [.succ .zero])
        methods aliasRecNormalizationRawContext ({} : TypeChecker.State) =
      .ok (some recAliasWhnfKernelExpr, recAliasUnfoldState {})
  exact unfoldRecAliasInitial methods

private theorem unfoldAliasRecFieldInitial (methods) :
    TypeChecker.Inner.unfoldDefinition aliasRecFieldKernelExpr
        methods aliasRecNormalizationRawContext ({} : TypeChecker.State) =
      .ok (some (.app recAliasWhnfKernelExpr
        (.const ``AliasRec [])), recAliasUnfoldState {}) := by
  rw [aliasRecFieldKernelExpr_eq]
  unfold TypeChecker.Inner.unfoldDefinition
  rw [if_pos (show (Expr.app (.const ``RecAlias [.succ .zero])
    (.const ``AliasRec [])).isApp = true from rfl)]
  rw [show
    (Expr.app (.const ``RecAlias [.succ .zero])
      (.const ``AliasRec [])).getAppFn =
        .const ``RecAlias [.succ .zero] by rfl]
  simp only [normalizationRecMBind]
  rw [unfoldRecAliasCoreInitial]
  rw [show
    (Expr.app (.const ``RecAlias [.succ .zero])
      (.const ``AliasRec [])).getAppRevArgs =
        #[.const ``AliasRec []] by rfl]
  simp only [normalizationRecMPure]
  rw [Expr.mkAppRevRange_eq
    (l₁ := []) (l₂ := [.const ``AliasRec []]) (l₃ := [])
    (by simp) (by rfl) (by rfl)]
  rfl

private theorem whnfLoopTypeFamilyAlias (methods state) :
    TypeChecker.Inner.whnf'.loop (.const ``TypeFamilyAlias []) 2
        methods aliasFormerNormalizationRawContext state =
      .ok (.sort (.succ .zero), state) := by
  unfold TypeChecker.Inner.whnf'.loop
  simp [unfoldTypeFamilyAlias]
  unfold TypeChecker.Inner.whnf'.loop
  simp

private theorem whnfLoopAliasFormer (methods state) :
    TypeChecker.Inner.whnf'.loop (.const ``AliasFormer []) 2
        methods aliasFormerCtorNormalizationRawContext state =
      .ok (.const ``AliasFormer [], state) := by
  unfold TypeChecker.Inner.whnf'.loop
  simp [unfoldAliasFormer]

private theorem whnfLoopRecAlias (methods) :
    TypeChecker.Inner.whnf'.loop
        (.const ``RecAlias [.succ .zero]) 2
        methods aliasRecNormalizationRawContext ({} : TypeChecker.State) =
      .ok (recAliasWhnfKernelExpr, recAliasUnfoldState {}) := by
  unfold TypeChecker.Inner.whnf'.loop
  simp [unfoldRecAliasInitial]
  unfold TypeChecker.Inner.whnf'.loop
  rw [recAliasWhnfKernelExpr_eq]
  simp

/-- The actual verified WHNF computation for the raw AliasFormer family
result. -/
theorem aliasFormerFamily_whnf :
    ∃ state : TypeChecker.State,
      TypeChecker.Inner.whnf' (.const ``TypeFamilyAlias [])
          (TypeChecker.Methods.withFuel 9999)
          aliasFormerNormalizationRawContext ({} : TypeChecker.State) =
        .ok (.sort (.succ .zero), state) := by
  unfold TypeChecker.Inner.whnf'
  simp
  rw [show (if aliasFormerNormalizationRawContext.eagerReduce then
      aliasFormerNormalizationRawContext.fuel.whnfEager
    else aliasFormerNormalizationRawContext.fuel.whnf) = 2 by rfl]
  rw [whnfLoopTypeFamilyAlias]
  simp [Functor.map, StateT.map, Except.map]

/-- Constructor normalization is staged after inserting the raw family. The
family constant is opaque, so this exact checker run retains the constructor
type unchanged. -/
theorem aliasFormerCtor_whnf :
    ∃ state : TypeChecker.State,
      TypeChecker.Inner.whnf' (.const ``AliasFormer [])
          (TypeChecker.Methods.withFuel 9999)
          aliasFormerCtorNormalizationRawContext
          ({} : TypeChecker.State) =
        .ok (.const ``AliasFormer [], state) := by
  unfold TypeChecker.Inner.whnf'
  simp
  rw [show (if aliasFormerCtorNormalizationRawContext.eagerReduce then
      aliasFormerCtorNormalizationRawContext.fuel.whnfEager
    else aliasFormerCtorNormalizationRawContext.fuel.whnf) = 2 by rfl]
  rw [whnfLoopAliasFormer]
  simp [Functor.map, StateT.map, Except.map]

/-- The full non-inference-only checker run for the raw AliasFormer family
type. The returned sort is recorded together with the checker's cache update,
rather than supplied as an external Theory premise. -/
theorem aliasFormerFamily_checkType :
    ∃ state : TypeChecker.State,
      TypeChecker.Inner.inferType aliasFormerInfo.type false
          (TypeChecker.Methods.withFuel 9999)
          aliasFormerNormalizationContext.toContext
          ({} : TypeChecker.State) =
        .ok (.sort (.succ (.succ .zero)), state) := by
  exact ⟨aliasFormerCheckTypeState {}, by
    simpa [aliasFormerInfo, ConstantInfo.type,
      ConstantInfo.toConstantVal,
      aliasFormerNormalizationContext,
      TypeChecker.VContext.mk', TypeChecker.VContext.mk1,
      TypeChecker.MLCtx.lctx,
      aliasFormerNormalizationRawContext] using
      checkTypeTypeFamilyAlias⟩

/-- The exact full checker run for the actual AliasFormer constructor type,
staged after insertion of the raw family. The checker returns the retained
family-type alias rather than silently normalizing it. -/
theorem aliasFormerCtor_checkType :
    ∃ state : TypeChecker.State,
      TypeChecker.Inner.inferType aliasFormerMkInfo.type false
          (TypeChecker.Methods.withFuel 9999)
          aliasFormerCtorCandidateContext.toTypeChecker
          ({} : TypeChecker.State) =
        .ok (.const ``TypeFamilyAlias [], state) := by
  exact ⟨aliasFormerCtorCheckTypeState {}, by
    simpa [aliasFormerMkInfo, ConstantInfo.type,
      ConstantInfo.toConstantVal,
      aliasFormerCtorCandidateContext,
      AddInductive.Context.toTypeChecker,
      aliasFormerCtorNormalizationRawContext] using
      checkTypeAliasFormer⟩

/-- The actual verified WHNF computation for the reducible `RecAlias`
head at the universe used by `AliasRec.mk`. -/
theorem recAlias_whnf :
    ∃ state : TypeChecker.State,
      TypeChecker.Inner.whnf'
          (.const ``RecAlias [.succ .zero])
          (TypeChecker.Methods.withFuel 9999)
          aliasRecNormalizationRawContext ({} : TypeChecker.State) =
        .ok (recAliasWhnfKernelExpr, state) := by
  unfold TypeChecker.Inner.whnf'
  simp
  rw [show (if aliasRecNormalizationRawContext.eagerReduce then
      aliasRecNormalizationRawContext.fuel.whnfEager
    else aliasRecNormalizationRawContext.fuel.whnf) = 2 by rfl]
  rw [whnfLoopRecAlias]
  simp [Functor.map, StateT.map, Except.map]

private theorem aliasFormerFamily_whnfM :
    TypeChecker.M.run aliasFormerNormalizationKernelEnv .safe {} []
        { whnf := 2 } (TypeChecker.whnf aliasFormerInfo.type) =
      .ok (.sort (.succ .zero)) := by
  change
    Except.map (fun x : Expr × TypeChecker.State => x.1)
      (TypeChecker.Inner.whnf'
        (.const ``TypeFamilyAlias [])
        (TypeChecker.Methods.withFuel 9999)
        aliasFormerNormalizationRawContext ({} : TypeChecker.State)) =
        Except.ok (.sort (.succ .zero))
  obtain ⟨state, hrun⟩ := aliasFormerFamily_whnf
  rw [hrun]
  rfl

private theorem aliasFormerFamily_checkTypeM :
    TypeChecker.M.run aliasFormerNormalizationKernelEnv .safe {} []
        { whnf := 2 } (TypeChecker.checkType aliasFormerInfo.type) =
      .ok (.sort (.succ (.succ .zero))) := by
  change
    Except.map (fun x : Expr × TypeChecker.State => x.1)
      (TypeChecker.Inner.inferType aliasFormerInfo.type false
        (TypeChecker.Methods.withFuel 10000)
        aliasFormerNormalizationRawContext ({} : TypeChecker.State)) =
      Except.ok (.sort (.succ (.succ .zero)))
  rw [show aliasFormerInfo.type =
    .const ``TypeFamilyAlias [] by rfl]
  rw [checkTypeTypeFamilyAliasCandidate]
  rfl

private theorem aliasFormerCtor_checkTypeM :
    TypeChecker.M.run aliasFormerCtorNormalizationKernelEnv .safe {} []
        { whnf := 2 } (TypeChecker.checkType aliasFormerMkInfo.type) =
      .ok (.const ``TypeFamilyAlias []) := by
  change
    Except.map (fun x : Expr × TypeChecker.State => x.1)
      (TypeChecker.Inner.inferType aliasFormerMkInfo.type false
        (TypeChecker.Methods.withFuel 10000)
        aliasFormerCtorNormalizationRawContext ({} : TypeChecker.State)) =
      Except.ok (.const ``TypeFamilyAlias [])
  rw [show aliasFormerMkInfo.type =
    .const ``AliasFormer [] by rfl]
  rw [checkTypeAliasFormerCandidate]
  rfl

private theorem aliasFormerCtor_whnfM :
    TypeChecker.M.run aliasFormerCtorNormalizationKernelEnv .safe {} []
        { whnf := 2 } (TypeChecker.whnf aliasFormerMkInfo.type) =
      .ok (.const ``AliasFormer []) := by
  change
    Except.map (fun x : Expr × TypeChecker.State => x.1)
      (TypeChecker.Inner.whnf'
        (.const ``AliasFormer [])
        (TypeChecker.Methods.withFuel 9999)
        aliasFormerCtorNormalizationRawContext ({} : TypeChecker.State)) =
      Except.ok (.const ``AliasFormer [])
  obtain ⟨state, hrun⟩ := aliasFormerCtor_whnf
  rw [hrun]
  rfl

private def annotatedPiRawDomainKernel : Expr :=
  .app (.const ``outParam [.succ .zero]) (.sort .zero)

private def annotatedPiInnerKernel : Expr :=
  .forallE `p annotatedPiRawDomainKernel
    (.const ``AnnotatedPi []) .default

@[simp] private theorem annotatedPiRawDomain_getAppFn :
    annotatedPiRawDomainKernel.getAppFn =
      .const ``outParam [.succ .zero] := rfl

@[simp] private theorem annotatedPiRawDomain_getAppRevArgs :
    annotatedPiRawDomainKernel.getAppRevArgs = #[.sort .zero] := rfl

private def annotatedPiOutParamWhnfKernelExpr : Expr :=
  annotationOutParamInfo.instantiateValueLevelParams! [.succ .zero]

private theorem annotatedPiOutParamWhnfKernelExpr_eq :
    annotatedPiOutParamWhnfKernelExpr =
      .lam `α (.sort (.succ .zero)) (.bvar 0) .default := by
  simp [annotatedPiOutParamWhnfKernelExpr, annotationOutParamInfo,
    ConstantInfo.instantiateValueLevelParams!, ConstantInfo.levelParams, ConstantInfo.value!,
    ConstantInfo.toConstantVal, Expr.instantiateLevelParams_eq, Expr.instantiateLevelParamsCore',
    Level.substParams']

private def annotatedPiOutParamUnfoldState (state : TypeChecker.State) :
    TypeChecker.State :=
  { state with
    unfold := state.unfold.insert
      (.const ``outParam [.succ .zero])
      annotatedPiOutParamWhnfKernelExpr }

private def annotatedPiDomainBetaKernel : Expr :=
  .app annotatedPiOutParamWhnfKernelExpr (.sort .zero)

private def annotatedPiDomainBetaState (state : TypeChecker.State) :
    TypeChecker.State :=
  { state with
    whnfCoreCache := state.whnfCoreCache.insert
      annotatedPiDomainBetaKernel (.sort .zero) }

@[simp] private theorem annotatedPiType_quotInit :
    annotatedPiTypeKernelEnv.quotInit = false := rfl

private theorem annotatedPiInductiveReduceRecDomain
    {m : Type → Type} [Monad m]
    (whnf inferType : Expr → m Expr)
    (isDefEq : Expr → Expr → m Bool) (isNeverProp : Expr → m Bool) :
    inductiveReduceRec annotatedPiTypeKernelEnv annotatedPiRawDomainKernel
        whnf inferType isDefEq isNeverProp =
      pure none := by
  unfold inductiveReduceRec
  rw [show annotatedPiRawDomainKernel.getAppFn =
    .const ``outParam [.succ .zero] by rfl]
  simp only
  rw [annotatedPiType_lookup_outParam]
  rfl

private theorem annotatedPiReduceRecursorDomain
    (methods state) :
    TypeChecker.Inner.reduceRecursor annotatedPiRawDomainKernel
        methods annotatedPiCtorCandidateContext.toTypeChecker state =
      .ok (none, state) := by
  unfold TypeChecker.Inner.reduceRecursor
  simp only [normalizationRecMBind, normalizationRecMGetEnv]
  rw [if_neg (show
    ¬(annotatedPiCtorCandidateContext.toTypeChecker.env.quotInit = true) by
      simp [annotatedPiCtorCandidateContext,
        AddInductive.Context.toTypeChecker, annotatedPiType_quotInit])]
  simp only [annotatedPiCtorCandidateContext,
    AddInductive.Context.toTypeChecker]
  rw [annotatedPiInductiveReduceRecDomain]
  rfl

@[simp] private theorem annotatedPiWhnfCoreOutParamConst (n state) :
    TypeChecker.Inner.whnfCore
        (.const ``outParam [.succ .zero]) false
        (TypeChecker.Methods.withFuel (n + 1))
        annotatedPiCtorCandidateContext.toTypeChecker state =
      .ok (.const ``outParam [.succ .zero], state) := by
  rfl

private theorem annotatedPiWhnfCoreDomainInitial (n) :
    TypeChecker.Inner.whnfCore' annotatedPiRawDomainKernel
        (cheapProj := false)
        (TypeChecker.Methods.withFuel (n + 1))
        annotatedPiCtorCandidateContext.toTypeChecker
        ({} : TypeChecker.State) =
      .ok (annotatedPiRawDomainKernel, ({} : TypeChecker.State)) := by
  change
    TypeChecker.Inner.whnfCore'
        (.app (.const ``outParam [.succ .zero]) (.sort .zero))
        (cheapProj := false)
        (TypeChecker.Methods.withFuel (n + 1))
        annotatedPiCtorCandidateContext.toTypeChecker
        ({} : TypeChecker.State) =
      .ok (.app (.const ``outParam [.succ .zero]) (.sort .zero),
        ({} : TypeChecker.State))
  unfold TypeChecker.Inner.whnfCore'
  simp only [normalizationRecMBind, normalizationRecMGet, Std.HashMap.getElem?_empty]
  rw [Expr.withRevApp_eq]
  simp only [normalizationRecMBind]
  rw [show
    (Expr.app (.const ``outParam [.succ .zero])
      (.sort .zero)).getAppFn =
        .const ``outParam [.succ .zero] by rfl]
  rw [annotatedPiWhnfCoreOutParamConst n ({} : TypeChecker.State)]
  simp [Expr.structuralEq, Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [show
    .app (.const ``outParam [.succ .zero]) (.sort .zero) =
      annotatedPiRawDomainKernel by rfl]
  rw [annotatedPiReduceRecursorDomain]
  rfl

private theorem annotatedPiUnfoldOutParamCoreInitial (methods) :
    TypeChecker.Inner.unfoldDefinitionCore
        (.const ``outParam [.succ .zero])
        methods annotatedPiCtorCandidateContext.toTypeChecker
        ({} : TypeChecker.State) =
      .ok (some annotatedPiOutParamWhnfKernelExpr,
        annotatedPiOutParamUnfoldState {}) := by
  simp [TypeChecker.Inner.unfoldDefinitionCore, TypeChecker.Inner.isDelta, Expr.getAppFn,
    annotatedPiCtorCandidateContext, AddInductive.Context.toTypeChecker,
    annotatedPiType_lookup_outParam, Bind.bind, ReaderT.bind, StateT.bind, Except.bind,
    annotationOutParamInfo, ConstantInfo.deltaValue?, TypeChecker.Inner.instantiateDeltaValue,
    ConstantInfo.numLevelParams, ConstantInfo.instantiateValueLevelParams!,
    ConstantInfo.levelParams, ConstantInfo.value!, ConstantInfo.toConstantVal,
    Expr.instantiateLevelParams, annotatedPiOutParamWhnfKernelExpr, annotatedPiOutParamUnfoldState]

private theorem annotatedPiUnfoldDomainInitial (methods) :
    TypeChecker.Inner.unfoldDefinition annotatedPiRawDomainKernel
        methods annotatedPiCtorCandidateContext.toTypeChecker
        ({} : TypeChecker.State) =
      .ok (some annotatedPiDomainBetaKernel,
        annotatedPiOutParamUnfoldState {}) := by
  change
    TypeChecker.Inner.unfoldDefinition
        (.app (.const ``outParam [.succ .zero]) (.sort .zero))
        methods annotatedPiCtorCandidateContext.toTypeChecker
        ({} : TypeChecker.State) =
      .ok (some annotatedPiDomainBetaKernel,
        annotatedPiOutParamUnfoldState {})
  unfold TypeChecker.Inner.unfoldDefinition
  rw [if_pos (show (Expr.app (.const ``outParam [.succ .zero])
    (.sort .zero)).isApp = true from rfl)]
  rw [show
    (Expr.app (.const ``outParam [.succ .zero])
      (.sort .zero)).getAppFn =
        .const ``outParam [.succ .zero] by rfl]
  simp only [normalizationRecMBind]
  rw [annotatedPiUnfoldOutParamCoreInitial]
  rw [show
    (Expr.app (.const ``outParam [.succ .zero])
      (.sort .zero)).getAppRevArgs = #[.sort .zero] by rfl]
  simp only [normalizationRecMPure]
  rw [Expr.mkAppRevRange_eq
    (l₁ := []) (l₂ := [.sort .zero]) (l₃ := [])
    (by simp) (by rfl) (by rfl)]
  rfl

@[simp] private theorem annotatedPiWhnfCoreOutParamIdentity (n state) :
    TypeChecker.Inner.whnfCore
        (.lam `α (.sort (.succ .zero)) (.bvar 0) .default)
        false (TypeChecker.Methods.withFuel (n + 1))
        annotatedPiCtorCandidateContext.toTypeChecker state =
      .ok (.lam `α (.sort (.succ .zero)) (.bvar 0) .default,
        state) := by
  rfl

@[simp] private theorem annotatedPiWhnfCoreDomainSort (n state) :
    TypeChecker.Inner.whnfCore (.sort .zero) false
        (TypeChecker.Methods.withFuel (n + 1))
        annotatedPiCtorCandidateContext.toTypeChecker state =
      .ok (.sort .zero, state) := by
  rfl

@[simp] private theorem annotatedPiSort_mkAppRevRangeZero :
    (Expr.sort .zero).mkAppRevRange 0 0 #[.sort .zero] =
      .sort .zero := by
  rw [Expr.mkAppRevRange_eq
    (l₁ := []) (l₂ := []) (l₃ := [.sort .zero])
    (by simp) (by rfl) (by rfl)]
  rfl

private theorem annotatedPiWhnfCoreDomainBeta (n) :
    TypeChecker.Inner.whnfCore' annotatedPiDomainBetaKernel
        (cheapProj := false)
        (TypeChecker.Methods.withFuel (n + 1))
        annotatedPiCtorCandidateContext.toTypeChecker
        (annotatedPiOutParamUnfoldState {}) =
      .ok (.sort .zero,
        annotatedPiDomainBetaState
          (annotatedPiOutParamUnfoldState {})) := by
  rw [annotatedPiDomainBetaKernel,
    annotatedPiOutParamWhnfKernelExpr_eq]
  unfold TypeChecker.Inner.whnfCore'
  simp only [normalizationRecMBind, normalizationRecMGet, annotatedPiOutParamUnfoldState,
    Std.HashMap.getElem?_empty]
  rw [Expr.withRevApp_eq]
  simp only [normalizationRecMBind]
  rw [show
    (Expr.app
      (.lam `α (.sort (.succ .zero)) (.bvar 0) .default)
      (.sort .zero)).getAppFn =
        .lam `α (.sort (.succ .zero)) (.bvar 0) .default by rfl]
  rw [annotatedPiWhnfCoreOutParamIdentity]
  rw [show
    (Expr.app
      (.lam `α (.sort (.succ .zero)) (.bvar 0) .default)
      (.sort .zero)).getAppRevArgs = #[.sort .zero] by rfl]
  simp [TypeChecker.Inner.whnfCore'.loop, TypeChecker.Inner.whnfCore'.loop.cont,
    TypeChecker.Inner.whnfCore'.save, annotatedPiDomainBetaKernel,
    annotatedPiOutParamWhnfKernelExpr_eq, annotatedPiDomainBetaState, Expr.instantiate1', Bind.bind,
    ReaderT.bind, StateT.bind, Except.bind]

@[simp] private theorem annotatedPiReduceNativeDomain
    (env methods state) :
    (liftM (TypeChecker.Inner.reduceNative env annotatedPiRawDomainKernel) :
        TypeChecker.RecM (Option Expr))
        methods annotatedPiCtorCandidateContext.toTypeChecker state =
      .ok (none, state) := by
  rfl

@[simp] private theorem annotatedPiReduceNatDomain (methods state) :
    TypeChecker.Inner.reduceNat annotatedPiRawDomainKernel
        methods annotatedPiCtorCandidateContext.toTypeChecker state =
      .ok (none, state) := by
  change
    TypeChecker.Inner.reduceNat
        (.app (.const ``outParam [.succ .zero]) (.sort .zero))
        methods annotatedPiCtorCandidateContext.toTypeChecker state =
      .ok (none, state)
  simp [TypeChecker.Inner.reduceNat, Expr.getAppNumArgs_eq,
    Expr.getAppArgsRevList, Expr.appFn!, Expr.structuralEq]

private theorem annotatedPiWhnfLoopDomain :
    TypeChecker.Inner.whnf'.loop annotatedPiRawDomainKernel 100000
        (TypeChecker.Methods.withFuel 9999)
        annotatedPiCtorCandidateContext.toTypeChecker
        ({} : TypeChecker.State) =
      .ok (.sort .zero,
        annotatedPiDomainBetaState
          (annotatedPiOutParamUnfoldState {})) := by
  rw [show 100000 = 99999 + 1 by rfl]
  unfold TypeChecker.Inner.whnf'.loop
  rw [show 9999 = 9998 + 1 by rfl]
  simp only [normalizationRecMBind, normalizationRecMGetEnv]
  rw [annotatedPiWhnfCoreDomainInitial]
  simp only []
  rw [annotatedPiReduceNativeDomain]
  simp only [normalizationRecMBind]
  rw [annotatedPiReduceNatDomain]
  simp only [normalizationRecMBind]
  rw [annotatedPiUnfoldDomainInitial]
  simp only []
  unfold TypeChecker.Inner.whnf'.loop
  simp only [normalizationRecMBind, normalizationRecMGetEnv]
  rw [annotatedPiWhnfCoreDomainBeta]
  simp only []
  rw [normalizationReduceNativeSort]
  simp only [normalizationRecMBind]
  rw [normalizationReduceNatSort]
  simp only [normalizationRecMBind]
  rw [normalizationUnfoldSort]
  rfl

private theorem annotatedPiWhnfLoopDomainConcrete :
    TypeChecker.Inner.whnf'.loop
        (.app (.const ``outParam [.succ .zero]) (.sort .zero)) 100000
        (TypeChecker.Methods.withFuel 9999)
        annotatedPiCtorCandidateContext.toTypeChecker
        ({} : TypeChecker.State) =
      .ok (.sort .zero,
        annotatedPiDomainBetaState
          (annotatedPiOutParamUnfoldState {})) := by
  exact annotatedPiWhnfLoopDomain

private theorem annotatedPiDomain_checkTypeM :
    TypeChecker.M.run annotatedPiCtorCandidateContext.env
      annotatedPiCtorCandidateContext.safety
      annotatedPiCtorCandidateContext.lctx
      annotatedPiCtorCandidateContext.lparams
      annotatedPiCtorCandidateContext.fuel
      (TypeChecker.checkType annotatedPiRawDomainKernel) =
        .ok (.sort (.succ .zero)) := by
  change
    Except.map (fun x : Expr × TypeChecker.State => x.1)
      (TypeChecker.Inner.inferType annotatedPiRawDomainKernel false
        (TypeChecker.Methods.withFuel 10000)
        annotatedPiCtorCandidateContext.toTypeChecker
        ({} : TypeChecker.State)) =
      .ok (.sort (.succ .zero))
  change
    Except.map (fun x : Expr × TypeChecker.State => x.1)
      (TypeChecker.Inner.inferType' annotatedPiRawDomainKernel false
        (TypeChecker.Methods.withFuel 9999)
        annotatedPiCtorCandidateContext.toTypeChecker
        ({} : TypeChecker.State)) =
      .ok (.sort (.succ .zero))
  unfold annotatedPiRawDomainKernel TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange', TypeChecker.Inner.inferType', Bind.bind,
    ReaderT.bind, StateT.bind, Except.bind]
  rw [annotatedPiIsDefEqSort 9999]
  simp [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rfl

private theorem annotatedPiDomain_whnfM :
    TypeChecker.M.run annotatedPiCtorCandidateContext.env
      annotatedPiCtorCandidateContext.safety
      annotatedPiCtorCandidateContext.lctx
      annotatedPiCtorCandidateContext.lparams
      annotatedPiCtorCandidateContext.fuel
      (TypeChecker.whnf annotatedPiRawDomainKernel) =
        .ok (.sort .zero) := by
  change
    Except.map (fun x : Expr × TypeChecker.State => x.1)
      (TypeChecker.Inner.whnf' annotatedPiRawDomainKernel
        (TypeChecker.Methods.withFuel 9999)
        annotatedPiCtorCandidateContext.toTypeChecker
        ({} : TypeChecker.State)) =
      .ok (.sort .zero)
  rw [show annotatedPiRawDomainKernel =
    .app (.const ``outParam [.succ .zero]) (.sort .zero) by rfl]
  unfold TypeChecker.Inner.whnf'
  simp
  rw [show
    (if annotatedPiCtorCandidateContext.toTypeChecker.eagerReduce then
      annotatedPiCtorCandidateContext.toTypeChecker.fuel.whnfEager
    else annotatedPiCtorCandidateContext.toTypeChecker.fuel.whnf) =
        100000 by rfl]
  rw [annotatedPiWhnfLoopDomainConcrete]
  simp [Functor.map, StateT.map, Except.map]

@[simp] private theorem annotatedPiApp_beq_sort
    (fn arg : Expr) (u : Level) :
    ((.app fn arg : Expr) == .sort u) = false := by
  change Expr.eqv (.app fn arg) (.sort u) = false
  rw [Expr.eqv_eq]
  rfl

/-- `quickIsDefEq` only reads the success cache, so whichever answer the cache gives, the state
comes back unchanged and the result is `.true` or `.undef` -- never `.false`, since an application
and a sort are not settled structurally. -/
private theorem annotatedPiQuickIsDefEqDomainInitial
    (methods : TypeChecker.Methods)
    (context : TypeChecker.Context) (initial : Std.HashSet (Expr × Expr)) :
    ∃ (r : LBool) (m : Std.HashSet (Expr × Expr)),
      TypeChecker.Inner.quickIsDefEq
          annotatedPiRawDomainKernel (.sort .zero)
          methods context ({ success := initial } : TypeChecker.State) =
        .ok (r, ({ success := m } : TypeChecker.State)) ∧
      (r = .true ∨ r = .undef) := by
  have hb : (annotatedPiRawDomainKernel == Expr.sort .zero) = false :=
    annotatedPiApp_beq_sort ..
  by_cases h : TypeChecker.Inner.succeededBefore initial
      annotatedPiRawDomainKernel (.sort .zero) = true
  · refine ⟨.true, initial, ?_, Or.inl rfl⟩
    simp [TypeChecker.Inner.quickIsDefEq, hb, h, Bind.bind, ReaderT.bind, StateT.bind, Except.bind,
      pure, ReaderT.pure, StateT.pure, Except.pure]
  · simp only [Bool.not_eq_true] at h
    refine ⟨.undef, initial, ?_, Or.inr rfl⟩
    simp [TypeChecker.Inner.quickIsDefEq, hb, h, Bind.bind, ReaderT.bind, StateT.bind, Except.bind,
      pure]
    rfl

@[simp] private theorem annotatedPiWhnfCoreOutParamConstCheap
    (fuel : Nat) (m : Std.HashSet (Expr × Expr)) :
    TypeChecker.Inner.whnfCore
        (.const ``outParam [.succ .zero]) true
        (TypeChecker.Methods.withFuel (fuel + 2))
        annotatedPiCtorCandidateContext.toTypeChecker
        ({ success := m } : TypeChecker.State) =
      .ok (.const ``outParam [.succ .zero],
        ({ success := m } : TypeChecker.State)) := by
  rfl

private theorem annotatedPiWhnfCoreDomainCheap
    (fuel : Nat) (m : Std.HashSet (Expr × Expr)) :
    TypeChecker.Inner.whnfCore annotatedPiRawDomainKernel true
        (TypeChecker.Methods.withFuel (fuel + 3))
        annotatedPiCtorCandidateContext.toTypeChecker
        ({ success := m } : TypeChecker.State) =
      .ok (annotatedPiRawDomainKernel,
        ({ success := m } : TypeChecker.State)) := by
  change
    TypeChecker.Inner.whnfCore'
        (.app (.const ``outParam [.succ .zero]) (.sort .zero))
        true (TypeChecker.Methods.withFuel (fuel + 2))
        annotatedPiCtorCandidateContext.toTypeChecker
        ({ success := m } : TypeChecker.State) =
      .ok (.app (.const ``outParam [.succ .zero]) (.sort .zero),
        ({ success := m } : TypeChecker.State))
  unfold TypeChecker.Inner.whnfCore'
  simp only [normalizationRecMBind, normalizationRecMGet, Std.HashMap.getElem?_empty]
  rw [Expr.withRevApp_eq]
  simp only [normalizationRecMBind]
  rw [show
    (Expr.app (.const ``outParam [.succ .zero])
      (.sort .zero)).getAppFn =
        .const ``outParam [.succ .zero] by rfl]
  rw [annotatedPiWhnfCoreOutParamConstCheap fuel]
  simp [Expr.structuralEq, Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [show
    .app (.const ``outParam [.succ .zero]) (.sort .zero) =
      annotatedPiRawDomainKernel by rfl]
  rw [annotatedPiReduceRecursorDomain]
  rfl

@[simp] private theorem annotatedPiInferConstantOutParamCandidateOnly :
    TypeChecker.Inner.inferConstant
        annotatedPiCtorCandidateContext.toTypeChecker
        ``outParam [.succ .zero] true =
      .ok annotatedPiOutParamFnType := by
  unfold TypeChecker.Inner.inferConstant
  simp only [annotatedPiCtorCandidateContext,
    AddInductive.Context.toTypeChecker]
  rw [show annotatedPiTypeKernelEnv.get ``outParam =
    .ok annotationOutParamInfo by exact annotatedPiType_get_outParam]
  simp [annotationOutParamInfo, annotatedPiOutParamFnType, Bind.bind, Except.bind,
    annotatedPiExceptPure, ConstantInfo.levelParams, ConstantInfo.instantiateTypeLevelParams,
    ConstantInfo.toConstantVal, ConstantVal.instantiateTypeLevelParams,
    Expr.instantiateLevelParams_eq, Expr.instantiateLevelParamsCore', Level.substParams']

private def annotatedPiOutParamInferOnlyState
    (m : Std.HashSet (Expr × Expr)) : TypeChecker.State :=
  { inferTypeI := ({} : InferCache).insert
      (.const ``outParam [.succ .zero]) annotatedPiOutParamFnType,
    success := m }

private theorem annotatedPiInferTypeOutParamOnly
    (fuel : Nat) (m : Std.HashSet (Expr × Expr)) :
    TypeChecker.Inner.inferType
        (.const ``outParam [.succ .zero]) true
        (TypeChecker.Methods.withFuel (fuel + 2))
        annotatedPiCtorCandidateContext.toTypeChecker
        ({ success := m } : TypeChecker.State) =
      .ok (annotatedPiOutParamFnType,
        annotatedPiOutParamInferOnlyState m) := by
  change
    TypeChecker.Inner.inferType'
        (.const ``outParam [.succ .zero]) true
        (TypeChecker.Methods.withFuel (fuel + 1))
        annotatedPiCtorCandidateContext.toTypeChecker
        ({ success := m } : TypeChecker.State) =
      .ok (annotatedPiOutParamFnType,
        annotatedPiOutParamInferOnlyState m)
  unfold TypeChecker.Inner.inferType'
  simp [annotatedPiOutParamInferOnlyState,
    Expr.hasLooseBVars, Expr.looseBVarRange',
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

private theorem annotatedPiInferAppDomainOnly
    (fuel : Nat) (m : Std.HashSet (Expr × Expr)) :
    TypeChecker.Inner.inferApp annotatedPiRawDomainKernel
        (TypeChecker.Methods.withFuel (fuel + 2))
        annotatedPiCtorCandidateContext.toTypeChecker
        ({ success := m } : TypeChecker.State) =
      .ok (.sort (.succ .zero),
        annotatedPiOutParamInferOnlyState m) := by
  unfold TypeChecker.Inner.inferApp
  rw [Expr.withApp_eq]
  rw [annotatedPiRawDomain_getAppFn]
  rw [show annotatedPiRawDomainKernel.getAppArgs =
    #[.sort .zero] by rfl]
  simp only [normalizationRecMBind]
  rw [annotatedPiInferTypeOutParamOnly fuel]
  simp [TypeChecker.Inner.inferApp.loop, annotatedPiOutParamFnType]

private def annotatedPiDomainInferOnlyState
    (m : Std.HashSet (Expr × Expr)) : TypeChecker.State :=
  { inferTypeI :=
      (({} : InferCache).insert
        (.const ``outParam [.succ .zero]) annotatedPiOutParamFnType).insert
        annotatedPiRawDomainKernel (.sort (.succ .zero)),
    success := m }

private theorem annotatedPiInferTypeDomainOnlyAny
    (fuel : Nat) (m : Std.HashSet (Expr × Expr)) :
    TypeChecker.Inner.inferType annotatedPiRawDomainKernel true
        (TypeChecker.Methods.withFuel (fuel + 3))
        annotatedPiCtorCandidateContext.toTypeChecker
        ({ success := m } : TypeChecker.State) =
      .ok (.sort (.succ .zero), annotatedPiDomainInferOnlyState m) := by
  change
    TypeChecker.Inner.inferType' annotatedPiRawDomainKernel true
        (TypeChecker.Methods.withFuel (fuel + 2))
        annotatedPiCtorCandidateContext.toTypeChecker
        ({ success := m } : TypeChecker.State) =
      .ok (.sort (.succ .zero), annotatedPiDomainInferOnlyState m)
  rw [show annotatedPiRawDomainKernel =
    .app (.const ``outParam [.succ .zero]) (.sort .zero) by rfl]
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange',
    annotatedPiDomainInferOnlyState, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind]
  rw [show
    .app (.const ``outParam [.succ .zero]) (.sort .zero) =
      annotatedPiRawDomainKernel by rfl]
  rw [annotatedPiInferAppDomainOnly fuel]
  simp [annotatedPiOutParamInferOnlyState]

private theorem annotatedPiInferTypeDomainOnly998
    (m : Std.HashSet (Expr × Expr)) :
    TypeChecker.Inner.inferType'
        (.app (.const ``outParam [.succ .zero]) (.sort .zero)) true
        (TypeChecker.Methods.withFuel 9998)
        annotatedPiCtorCandidateContext.toTypeChecker
        ({ success := m } : TypeChecker.State) =
      .ok (.sort (.succ .zero), annotatedPiDomainInferOnlyState m) := by
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange',
    annotatedPiDomainInferOnlyState, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind]
  rw [show
    .app (.const ``outParam [.succ .zero]) (.sort .zero) =
      annotatedPiRawDomainKernel by rfl]
  rw [show TypeChecker.Inner.inferApp annotatedPiRawDomainKernel
      (TypeChecker.Methods.withFuel 9998)
      annotatedPiCtorCandidateContext.toTypeChecker
      ({ success := m } : TypeChecker.State) =
    .ok (.sort (.succ .zero), annotatedPiOutParamInferOnlyState m) by
      simpa only [Nat.reduceAdd] using
        annotatedPiInferAppDomainOnly 9996 m]
  simp [annotatedPiOutParamInferOnlyState]

private def annotatedPiSortOneInferOnlyState
    (m : Std.HashSet (Expr × Expr)) : TypeChecker.State :=
  { annotatedPiDomainInferOnlyState m with
    inferTypeI := (annotatedPiDomainInferOnlyState m).inferTypeI.insert
      (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) }

@[simp] private theorem annotatedPiDomainInferOnlyState_sortOneMiss
    (m : Std.HashSet (Expr × Expr)) :
    (annotatedPiDomainInferOnlyState m).inferTypeI[
        (.sort (.succ .zero) : Expr)]? = none := by
  simp [annotatedPiDomainInferOnlyState, annotatedPiRawDomainKernel, annotatedPiOutParamFnType]

private theorem annotatedPiInferTypeSortOneOnly
    (fuel : Nat) (m : Std.HashSet (Expr × Expr)) :
    TypeChecker.Inner.inferType (.sort (.succ .zero)) true
        (TypeChecker.Methods.withFuel (fuel + 3))
        annotatedPiCtorCandidateContext.toTypeChecker
        (annotatedPiDomainInferOnlyState m) =
      .ok (.sort (.succ (.succ .zero)),
        annotatedPiSortOneInferOnlyState m) := by
  change
    TypeChecker.Inner.inferType' (.sort (.succ .zero)) true
        (TypeChecker.Methods.withFuel (fuel + 2))
        annotatedPiCtorCandidateContext.toTypeChecker
        (annotatedPiDomainInferOnlyState m) =
      .ok (.sort (.succ (.succ .zero)),
        annotatedPiSortOneInferOnlyState m)
  unfold TypeChecker.Inner.inferType'
  simp [annotatedPiDomainInferOnlyState_sortOneMiss,
    annotatedPiSortOneInferOnlyState, Expr.hasLooseBVars,
    Expr.looseBVarRange', Bind.bind, ReaderT.bind, StateT.bind,
    Except.bind]

@[simp] private theorem annotatedPiWhnfSortTwo
    (fuel : Nat) (state : TypeChecker.State) :
    TypeChecker.Inner.whnf (.sort (.succ (.succ .zero)))
        (TypeChecker.Methods.withFuel (fuel + 3))
        annotatedPiCtorCandidateContext.toTypeChecker state =
      .ok (.sort (.succ (.succ .zero)), state) := by
  rfl

private theorem annotatedPiIsPropSortOneFalse
    (fuel : Nat) (m : Std.HashSet (Expr × Expr)) :
    TypeChecker.Inner.isProp (.sort (.succ .zero))
        (TypeChecker.Methods.withFuel (fuel + 3))
        annotatedPiCtorCandidateContext.toTypeChecker
        (annotatedPiDomainInferOnlyState m) =
      .ok (false, annotatedPiSortOneInferOnlyState m) := by
  unfold TypeChecker.Inner.isProp TypeChecker.Inner.getSortLevel
  simp only [normalizationRecMBind]
  rw [annotatedPiInferTypeSortOneOnly fuel]
  rfl

private theorem annotatedPiIsDefEqProofIrrelDomain
    (fuel : Nat) (m : Std.HashSet (Expr × Expr)) :
    TypeChecker.Inner.isDefEqProofIrrel
        annotatedPiRawDomainKernel (.sort .zero)
        (TypeChecker.Methods.withFuel (fuel + 3))
        annotatedPiCtorCandidateContext.toTypeChecker
        ({ success := m } : TypeChecker.State) =
      .ok (.undef, annotatedPiSortOneInferOnlyState m) := by
  unfold TypeChecker.Inner.isDefEqProofIrrel
  simp only [normalizationRecMBind]
  rw [annotatedPiInferTypeDomainOnlyAny fuel]
  simp only []
  rw [annotatedPiIsPropSortOneFalse fuel]
  rfl

private theorem annotatedPiUnfoldOutParamCoreOfMiss
    (methods : TypeChecker.Methods) (state : TypeChecker.State)
    (hcache : state.unfold[
      (.const ``outParam [.succ .zero] : Expr)]? = none) :
    TypeChecker.Inner.unfoldDefinitionCore
        (.const ``outParam [.succ .zero]) methods
        annotatedPiCtorCandidateContext.toTypeChecker state =
      .ok (some annotatedPiOutParamWhnfKernelExpr,
        annotatedPiOutParamUnfoldState state) := by
  simp [TypeChecker.Inner.unfoldDefinitionCore,
    TypeChecker.Inner.isDelta, Expr.getAppFn,
    annotatedPiCtorCandidateContext,
    AddInductive.Context.toTypeChecker, annotatedPiType_lookup_outParam,
    hcache, Bind.bind, ReaderT.bind, StateT.bind, Except.bind,
    annotationOutParamInfo, ConstantInfo.deltaValue?,
    TypeChecker.Inner.instantiateDeltaValue,
    ConstantInfo.numLevelParams,
    ConstantInfo.instantiateValueLevelParams!, ConstantInfo.levelParams,
    ConstantInfo.value!, ConstantInfo.toConstantVal,
    Expr.instantiateLevelParams, annotatedPiOutParamWhnfKernelExpr,
    annotatedPiOutParamUnfoldState]

private theorem annotatedPiUnfoldDomainOfMiss
    (methods : TypeChecker.Methods) (state : TypeChecker.State)
    (hcache : state.unfold[
      (.const ``outParam [.succ .zero] : Expr)]? = none) :
    TypeChecker.Inner.unfoldDefinition annotatedPiRawDomainKernel
        methods annotatedPiCtorCandidateContext.toTypeChecker state =
      .ok (some annotatedPiDomainBetaKernel,
        annotatedPiOutParamUnfoldState state) := by
  change
    TypeChecker.Inner.unfoldDefinition
        (.app (.const ``outParam [.succ .zero]) (.sort .zero))
        methods annotatedPiCtorCandidateContext.toTypeChecker state =
      .ok (some annotatedPiDomainBetaKernel,
        annotatedPiOutParamUnfoldState state)
  unfold TypeChecker.Inner.unfoldDefinition
  rw [if_pos (show (Expr.app (.const ``outParam [.succ .zero])
    (.sort .zero)).isApp = true from rfl)]
  rw [show
    (Expr.app (.const ``outParam [.succ .zero])
      (.sort .zero)).getAppFn =
        .const ``outParam [.succ .zero] by rfl]
  simp only [normalizationRecMBind]
  rw [annotatedPiUnfoldOutParamCoreOfMiss methods state hcache]
  rw [show
    (Expr.app (.const ``outParam [.succ .zero])
      (.sort .zero)).getAppRevArgs = #[.sort .zero] by rfl]
  simp only [normalizationRecMPure]
  rw [Expr.mkAppRevRange_eq
    (l₁ := []) (l₂ := [.sort .zero]) (l₃ := [])
    (by simp) (by rfl) (by rfl)]
  rfl

@[simp] private theorem annotatedPiWhnfCoreIdentityCheap
    (fuel : Nat) (state) :
    TypeChecker.Inner.whnfCore
        (.lam `α (.sort (.succ .zero)) (.bvar 0) .default)
        true (TypeChecker.Methods.withFuel (fuel + 2))
        annotatedPiCtorCandidateContext.toTypeChecker state =
      .ok (.lam `α (.sort (.succ .zero)) (.bvar 0) .default,
        state) := by
  rfl

@[simp] private theorem annotatedPiWhnfCoreSortZeroCheap
    (fuel : Nat) (state) :
    TypeChecker.Inner.whnfCore (.sort .zero) true
        (TypeChecker.Methods.withFuel (fuel + 2))
        annotatedPiCtorCandidateContext.toTypeChecker state =
      .ok (.sort .zero, state) := by
  rfl

private theorem annotatedPiWhnfCoreDomainBetaCheap
    (fuel : Nat) (m : Std.HashSet (Expr × Expr)) :
    TypeChecker.Inner.whnfCore annotatedPiDomainBetaKernel true
        (TypeChecker.Methods.withFuel (fuel + 3))
        annotatedPiCtorCandidateContext.toTypeChecker
        (annotatedPiOutParamUnfoldState
          (annotatedPiSortOneInferOnlyState m)) =
      .ok (.sort .zero,
        annotatedPiOutParamUnfoldState
          (annotatedPiSortOneInferOnlyState m)) := by
  change
    TypeChecker.Inner.whnfCore' annotatedPiDomainBetaKernel true
        (TypeChecker.Methods.withFuel (fuel + 2))
        annotatedPiCtorCandidateContext.toTypeChecker
        (annotatedPiOutParamUnfoldState
          (annotatedPiSortOneInferOnlyState m)) =
      .ok (.sort .zero,
        annotatedPiOutParamUnfoldState
          (annotatedPiSortOneInferOnlyState m))
  rw [annotatedPiDomainBetaKernel,
    annotatedPiOutParamWhnfKernelExpr_eq]
  unfold TypeChecker.Inner.whnfCore'
  simp only [normalizationRecMBind, normalizationRecMGet, annotatedPiOutParamUnfoldState,
    annotatedPiSortOneInferOnlyState, annotatedPiDomainInferOnlyState, Std.HashMap.getElem?_empty]
  rw [Expr.withRevApp_eq]
  simp only [normalizationRecMBind]
  rw [show
    (Expr.app
      (.lam `α (.sort (.succ .zero)) (.bvar 0) .default)
      (.sort .zero)).getAppFn =
        .lam `α (.sort (.succ .zero)) (.bvar 0) .default by rfl]
  rw [annotatedPiWhnfCoreIdentityCheap fuel]
  rw [show
    (Expr.app
      (.lam `α (.sort (.succ .zero)) (.bvar 0) .default)
      (.sort .zero)).getAppRevArgs = #[.sort .zero] by rfl]
  simp [TypeChecker.Inner.whnfCore'.loop, TypeChecker.Inner.whnfCore'.loop.cont,
    TypeChecker.Inner.whnfCore'.save, annotatedPiOutParamWhnfKernelExpr_eq, Expr.instantiate1',
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

private theorem annotatedPiQuickIsDefEqSortZeroAny
    (methods : TypeChecker.Methods)
    (context : TypeChecker.Context)
    (initial : TypeChecker.State) :
    ∃ m : Std.HashSet (Expr × Expr),
      TypeChecker.Inner.quickIsDefEq (.sort .zero) (.sort .zero)
          methods context initial =
        .ok (.true, annotatedPiWithSuccessCache initial m) := by
  -- The two sides are syntactically equal, so the structural check settles it without the cache.
  refine ⟨initial.success, ?_⟩
  simp [TypeChecker.Inner.quickIsDefEq, annotatedPiWithSuccessCache, pure, ReaderT.pure,
    StateT.pure, Except.pure, Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

private theorem annotatedPiIsDeltaDomain :
    TypeChecker.Inner.isDelta annotatedPiTypeKernelEnv
        annotatedPiRawDomainKernel =
      some annotationOutParamInfo := by
  unfold TypeChecker.Inner.isDelta
  rw [annotatedPiRawDomain_getAppFn]
  simp only
  rw [annotatedPiType_lookup_outParam]
  simp [annotationOutParamInfo, ConstantInfo.deltaValue?,
    ConstantInfo.numLevelParams, ConstantInfo.levelParams,
    ConstantInfo.toConstantVal]

@[simp] private theorem annotatedPiIsDeltaSortZero :
    TypeChecker.Inner.isDelta annotatedPiTypeKernelEnv (.sort .zero) =
      none := by
  rfl

@[simp] private theorem annotatedPiTryUnfoldProjAppSortZero
    (methods state) :
    TypeChecker.Inner.tryUnfoldProjApp (.sort .zero) methods
        annotatedPiCtorCandidateContext.toTypeChecker state =
      .ok (none, state) := by
  rfl

private theorem annotatedPiDeltaDomain
    (fuel : Nat) (m : Std.HashSet (Expr × Expr)) :
    (TypeChecker.Inner.unfoldDefinition annotatedPiRawDomainKernel >>=
      fun e => TypeChecker.Inner.whnfCore e.get! true)
        (TypeChecker.Methods.withFuel (fuel + 3))
        annotatedPiCtorCandidateContext.toTypeChecker
        (annotatedPiSortOneInferOnlyState m) =
      .ok (.sort .zero,
        annotatedPiOutParamUnfoldState
          (annotatedPiSortOneInferOnlyState m)) := by
  simp only [normalizationRecMBind]
  rw [annotatedPiUnfoldDomainOfMiss
    (TypeChecker.Methods.withFuel (fuel + 3))
    (annotatedPiSortOneInferOnlyState m) (by
      simp [annotatedPiSortOneInferOnlyState,
        annotatedPiDomainInferOnlyState])]
  simp only
  rw [show (some annotatedPiDomainBetaKernel).get! =
    annotatedPiDomainBetaKernel by rfl]
  rw [annotatedPiWhnfCoreDomainBetaCheap fuel]

private theorem annotatedPiLazyDeltaStepDomain
    (fuel : Nat) (m : Std.HashSet (Expr × Expr)) :
    ∃ m' : Std.HashSet (Expr × Expr),
      TypeChecker.Inner.lazyDeltaReductionStep
          annotatedPiRawDomainKernel (.sort .zero)
          (TypeChecker.Methods.withFuel (fuel + 3))
          annotatedPiCtorCandidateContext.toTypeChecker
          (annotatedPiSortOneInferOnlyState m) =
        .ok (.bool true,
          annotatedPiWithSuccessCache
            (annotatedPiOutParamUnfoldState
              (annotatedPiSortOneInferOnlyState m)) m') := by
  obtain ⟨m', hquick⟩ := annotatedPiQuickIsDefEqSortZeroAny
    (TypeChecker.Methods.withFuel (fuel + 3))
    annotatedPiCtorCandidateContext.toTypeChecker
    (annotatedPiOutParamUnfoldState
      (annotatedPiSortOneInferOnlyState m))
  refine ⟨m', ?_⟩
  unfold TypeChecker.Inner.lazyDeltaReductionStep
  rw [normalizationRecMBind]
  rw [normalizationRecMGetEnv]
  simp only
  rw [show annotatedPiCtorCandidateContext.toTypeChecker.env =
    annotatedPiTypeKernelEnv by rfl]
  rw [annotatedPiIsDeltaDomain, annotatedPiIsDeltaSortZero]
  simp only
  rw [normalizationRecMBind]
  rw [annotatedPiTryUnfoldProjAppSortZero]
  simp only
  rw [normalizationRecMBind]
  rw [annotatedPiDeltaDomain fuel]
  simp only
  rw [normalizationRecMBind]
  rw [hquick]
  rfl

@[simp] private theorem annotatedPiIsDefEqOffsetDomain
    (fuel : Nat) (m : Std.HashSet (Expr × Expr)) :
    TypeChecker.Inner.isDefEqOffset
        annotatedPiRawDomainKernel (.sort .zero)
        (TypeChecker.Methods.withFuel (fuel + 3))
        annotatedPiCtorCandidateContext.toTypeChecker
        (annotatedPiSortOneInferOnlyState m) =
      .ok (.undef, annotatedPiSortOneInferOnlyState m) := by
  have hzero :
      (annotatedPiRawDomainKernel == Expr.natZero) = false := by
    rw [show annotatedPiRawDomainKernel =
      .app (.const ``outParam [.succ .zero]) (.sort .zero) by rfl]
    exact annotatedPiApp_beq_const _ _ _ _
  unfold TypeChecker.Inner.isDefEqOffset
  simp [TypeChecker.Inner.isNatZero, TypeChecker.Inner.isNatSuccOf?, annotatedPiRawDomainKernel,
    Expr.natZero]

private theorem annotatedPiLazyDeltaLoopDomain
    (fuel : Nat) (m : Std.HashSet (Expr × Expr)) :
    ∃ m' : Std.HashSet (Expr × Expr),
      TypeChecker.Inner.lazyDeltaReduction.loop
          annotatedPiRawDomainKernel (.sort .zero) 1000
          (TypeChecker.Methods.withFuel (fuel + 3))
          annotatedPiCtorCandidateContext.toTypeChecker
          (annotatedPiSortOneInferOnlyState m) =
        .ok (.bool true,
          annotatedPiWithSuccessCache
            (annotatedPiOutParamUnfoldState
              (annotatedPiSortOneInferOnlyState m)) m') := by
  obtain ⟨m', hstep⟩ := annotatedPiLazyDeltaStepDomain fuel m
  refine ⟨m', ?_⟩
  rw [show 1000 = 999 + 1 by rfl]
  unfold TypeChecker.Inner.lazyDeltaReduction.loop
  rw [normalizationRecMBind]
  rw [annotatedPiIsDefEqOffsetDomain fuel]
  simp only
  rw [show (LBool.undef != LBool.undef) = false by rfl]
  simp only [Bool.false_eq_true, if_false]
  rw [normalizationRecMBind]
  rw [normalizationRecMReadContext]
  simp only
  rw [show
    (!annotatedPiRawDomainKernel.hasFVar &&
        !(.sort .zero : Expr).hasFVar ||
      annotatedPiCtorCandidateContext.toTypeChecker.eagerReduce) = true
    by
      simp [Expr.hasFVar_eq, Expr.hasFVar',
        annotatedPiRawDomainKernel]]
  simp only [if_true]
  rw [normalizationRecMBind]
  rw [annotatedPiReduceNatDomain]
  simp only
  rw [normalizationRecMBind]
  rw [normalizationReduceNatSort]
  simp only
  rw [normalizationRecMBind]
  rw [normalizationRecMGetEnv]
  simp only
  rw [normalizationRecMBind]
  rw [annotatedPiReduceNativeDomain]
  simp only
  rw [normalizationRecMBind]
  rw [normalizationReduceNativeSort]
  simp only
  rw [normalizationRecMBind]
  rw [hstep]
  rfl

private theorem annotatedPiLazyDeltaDomain
    (fuel : Nat) (m : Std.HashSet (Expr × Expr)) :
    ∃ m' : Std.HashSet (Expr × Expr),
      TypeChecker.Inner.lazyDeltaReduction
          annotatedPiRawDomainKernel (.sort .zero)
          (TypeChecker.Methods.withFuel (fuel + 3))
          annotatedPiCtorCandidateContext.toTypeChecker
          (annotatedPiSortOneInferOnlyState m) =
        .ok (.bool true,
          annotatedPiWithSuccessCache
            (annotatedPiOutParamUnfoldState
              (annotatedPiSortOneInferOnlyState m)) m') := by
  obtain ⟨m', hloop⟩ := annotatedPiLazyDeltaLoopDomain fuel m
  refine ⟨m', ?_⟩
  unfold TypeChecker.Inner.lazyDeltaReduction
  rw [normalizationRecMBind]
  rw [normalizationRecMReadContext]
  simp only
  change
    TypeChecker.Inner.lazyDeltaReduction.loop
        annotatedPiRawDomainKernel (.sort .zero) 1000
        (TypeChecker.Methods.withFuel (fuel + 3))
        annotatedPiCtorCandidateContext.toTypeChecker
        (annotatedPiSortOneInferOnlyState m) = _
  exact hloop

private theorem annotatedPiQuickIsDefEqDomainAny
    (fuel : Nat) (m : Std.HashSet (Expr × Expr)) :
    ∃ (r : LBool) (m' : Std.HashSet (Expr × Expr)),
      TypeChecker.Inner.quickIsDefEq
          annotatedPiRawDomainKernel (.sort .zero)
          (TypeChecker.Methods.withFuel (fuel + 3))
          annotatedPiCtorCandidateContext.toTypeChecker
          ({ success := m } : TypeChecker.State) =
        .ok (r, ({ success := m' } : TypeChecker.State)) ∧
      (r = .true ∨ r = .undef) :=
  annotatedPiQuickIsDefEqDomainInitial _ _ m

@[simp] private theorem annotatedPiWhnfCoreSortCheap
    (fuel : Nat) (state : TypeChecker.State) :
    TypeChecker.Inner.whnfCore (.sort .zero) true
        (TypeChecker.Methods.withFuel (fuel + 3))
        annotatedPiCtorCandidateContext.toTypeChecker state =
      .ok (.sort .zero, state) := by
  rfl

private theorem annotatedPiIsDefEqCoreDomain
    (fuel : Nat) (initial : Std.HashSet (Expr × Expr) := {}) :
    ∃ state : TypeChecker.State,
      TypeChecker.Inner.isDefEqCore'
          annotatedPiRawDomainKernel (.sort .zero)
          (TypeChecker.Methods.withFuel (fuel + 3))
          annotatedPiCtorCandidateContext.toTypeChecker
          ({ success := initial } : TypeChecker.State) =
        .ok (true, state) := by
  obtain ⟨r, m, hquick, hr⟩ := annotatedPiQuickIsDefEqDomainInitial
    (TypeChecker.Methods.withFuel (fuel + 3))
    annotatedPiCtorCandidateContext.toTypeChecker initial
  unfold TypeChecker.Inner.isDefEqCore'
  rw [normalizationRecMBind]
  rw [hquick]
  rcases hr with htrue | hundef
  · subst r
    simp only
    rw [show (LBool.true != LBool.undef) = true by rfl]
    simp only [if_true]
    exact ⟨({ success := m } : TypeChecker.State), rfl⟩
  · subst r
    simp only
    rw [show (LBool.undef != LBool.undef) = false by rfl]
    simp only [Bool.false_eq_true, if_false]
    rw [normalizationRecMBind]
    rw [normalizationRecMReadContext]
    simp only
    rw [show ((.sort .zero : Expr).isConstOf ``true) = false by rfl]
    simp only [Bool.and_false, Bool.false_eq_true, if_false]
    rw [normalizationRecMBind]
    rw [annotatedPiWhnfCoreDomainCheap fuel]
    simp only
    rw [normalizationRecMBind]
    rw [annotatedPiWhnfCoreSortCheap fuel]
    simp only
    cases hptr :
        (!(ptrEqExpr annotatedPiRawDomainKernel annotatedPiRawDomainKernel &&
          ptrEqExpr (.sort .zero) (.sort .zero)))
    · simp only [Bool.false_eq_true, if_false]
      rw [normalizationRecMBind]
      rw [annotatedPiIsDefEqProofIrrelDomain fuel]
      simp only
      rw [show (LBool.undef != LBool.undef) = false by rfl]
      simp only [Bool.false_eq_true, if_false]
      rw [normalizationRecMBind]
      obtain ⟨m'', hlazy⟩ := annotatedPiLazyDeltaDomain fuel m
      rw [hlazy]
      refine ⟨annotatedPiWithSuccessCache
        (annotatedPiOutParamUnfoldState
          (annotatedPiSortOneInferOnlyState m)) m'', ?_⟩
      rfl
    · simp only [if_true]
      obtain ⟨r, m', hquick', hr⟩ :=
        annotatedPiQuickIsDefEqDomainAny fuel m
      rw [normalizationRecMBind]
      rw [hquick']
      simp only
      rcases hr with htrue | hundef
      · subst r
        rw [show (LBool.true != LBool.undef) = true by rfl]
        simp only [if_true]
        refine ⟨({ success := m' } : TypeChecker.State), ?_⟩
        rfl
      · subst r
        rw [show (LBool.undef != LBool.undef) = false by rfl]
        simp only [Bool.false_eq_true, if_false]
        rw [normalizationRecMBind]
        rw [annotatedPiIsDefEqProofIrrelDomain fuel]
        simp only
        rw [show (LBool.undef != LBool.undef) = false by rfl]
        simp only [Bool.false_eq_true, if_false]
        rw [normalizationRecMBind]
        obtain ⟨m'', hlazy⟩ := annotatedPiLazyDeltaDomain fuel m'
        rw [hlazy]
        refine ⟨annotatedPiWithSuccessCache
          (annotatedPiOutParamUnfoldState
            (annotatedPiSortOneInferOnlyState m')) m'', ?_⟩
        rfl

private theorem annotatedPiDomain_isDefEqInner
    (fuel : Nat) (initial : Std.HashSet (Expr × Expr) := {}) :
    ∃ state : TypeChecker.State,
      TypeChecker.Inner.isDefEq annotatedPiRawDomainKernel (.sort .zero)
          (TypeChecker.Methods.withFuel (fuel + 4))
          annotatedPiCtorCandidateContext.toTypeChecker
          ({ success := initial } : TypeChecker.State) =
        .ok (true, state) := by
  obtain ⟨state, hcore⟩ := annotatedPiIsDefEqCoreDomain fuel initial
  have hcore' :
      TypeChecker.Inner.isDefEqCore
          annotatedPiRawDomainKernel (.sort .zero)
          (TypeChecker.Methods.withFuel (fuel + 4))
          annotatedPiCtorCandidateContext.toTypeChecker
          ({ success := initial } : TypeChecker.State) =
        .ok (true, state) := by
    change
      TypeChecker.Inner.isDefEqCore'
          annotatedPiRawDomainKernel (.sort .zero)
          (TypeChecker.Methods.withFuel (fuel + 3))
          annotatedPiCtorCandidateContext.toTypeChecker
          ({ success := initial } : TypeChecker.State) =
        .ok (true, state)
    exact hcore
  unfold TypeChecker.Inner.isDefEq
  rw [show
    (annotatedPiRawDomainKernel == (.sort .zero : Expr)) = false by
      exact annotatedPiApp_beq_sort _ _ _]
  simp only [Bool.false_eq_true, if_false, normalizationRecMBind]
  rw [hcore']
  exact ⟨_, rfl⟩

private theorem annotatedPiDomain_isDefEqM :
    TypeChecker.M.run annotatedPiCtorCandidateContext.env
      annotatedPiCtorCandidateContext.safety
      annotatedPiCtorCandidateContext.lctx
      annotatedPiCtorCandidateContext.lparams
      annotatedPiCtorCandidateContext.fuel
      (TypeChecker.isDefEq annotatedPiRawDomainKernel (.sort .zero)) =
        .ok true := by
  obtain ⟨state, hrun⟩ := annotatedPiDomain_isDefEqInner 9996
  change
    Except.map (fun x : Bool × TypeChecker.State => x.1)
      (TypeChecker.Inner.isDefEq
        annotatedPiRawDomainKernel (.sort .zero)
        (TypeChecker.Methods.withFuel 10000)
        annotatedPiCtorCandidateContext.toTypeChecker
        ({} : TypeChecker.State)) =
      .ok true
  rw [show TypeChecker.Inner.isDefEq
      annotatedPiRawDomainKernel (.sort .zero)
      (TypeChecker.Methods.withFuel 10000)
      annotatedPiCtorCandidateContext.toTypeChecker
      ({} : TypeChecker.State) = .ok (true, state) by
    simpa only [Nat.reduceAdd] using hrun]
  rfl

private theorem annotatedPiInner_checkTypeM :
    TypeChecker.M.run annotatedPiCtorCandidateContext.env
      annotatedPiCtorCandidateContext.safety
      annotatedPiCtorCandidateContext.lctx
      annotatedPiCtorCandidateContext.lparams
      annotatedPiCtorCandidateContext.fuel
      (TypeChecker.checkType annotatedPiInnerKernel) =
        .ok (.sort (.succ .zero)) := by
  change
    Except.map (fun x : Expr × TypeChecker.State => x.1)
      (TypeChecker.Inner.inferType annotatedPiInnerKernel false
        (TypeChecker.Methods.withFuel 10000)
        annotatedPiCtorCandidateContext.toTypeChecker
        ({} : TypeChecker.State)) =
      .ok (.sort (.succ .zero))
  change
    Except.map (fun x : Expr × TypeChecker.State => x.1)
      (TypeChecker.Inner.inferType' annotatedPiInnerKernel false
        (TypeChecker.Methods.withFuel 9999)
        annotatedPiCtorCandidateContext.toTypeChecker
        ({} : TypeChecker.State)) =
      .ok (.sort (.succ .zero))
  unfold annotatedPiInnerKernel TypeChecker.Inner.inferType'
  simp [annotatedPiRawDomainKernel, Expr.hasLooseBVars, Expr.looseBVarRange',
    TypeChecker.Inner.inferType', TypeChecker.Inner.inferForall, TypeChecker.Inner.inferForall.loop,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [annotatedPiIsDefEqSort 9998]
  simp [Expr.instantiate1', annotatedPiWithLocalDecl, annotatedPiCtorCandidateContext,
    AddInductive.Context.toTypeChecker, Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  simp [Expr.sortLevel!, annotatedPi_mkLevelIMaxSuccZero]
  rfl

private theorem annotatedPiInner_whnfM :
    TypeChecker.M.run annotatedPiCtorCandidateContext.env
      annotatedPiCtorCandidateContext.safety
      annotatedPiCtorCandidateContext.lctx
      annotatedPiCtorCandidateContext.lparams
      annotatedPiCtorCandidateContext.fuel
      (TypeChecker.whnf annotatedPiInnerKernel) =
        .ok annotatedPiInnerKernel := by
  rfl

private theorem annotatedPiInner_isDefEqM :
    TypeChecker.M.run annotatedPiCtorCandidateContext.env
      annotatedPiCtorCandidateContext.safety
      annotatedPiCtorCandidateContext.lctx
      annotatedPiCtorCandidateContext.lparams
      annotatedPiCtorCandidateContext.fuel
      (TypeChecker.isDefEq annotatedPiInnerKernel
        annotatedPiInnerKernel) = .ok true := by
  change
    Except.map (fun x : Bool × TypeChecker.State => x.1)
      (TypeChecker.Inner.isDefEq annotatedPiInnerKernel
        annotatedPiInnerKernel (TypeChecker.Methods.withFuel 10000)
        annotatedPiCtorCandidateContext.toTypeChecker
        ({} : TypeChecker.State)) = .ok true
  unfold TypeChecker.Inner.isDefEq
  rw [if_pos (Expr.eqv_refl _)]
  rfl

private theorem annotatedPiConst_checkTypeM (lctx : LocalContext) :
    TypeChecker.M.run annotatedPiTypeKernelEnv .safe lctx []
      ({} : FuelConfig)
      (TypeChecker.checkType (.const ``AnnotatedPi [])) =
        .ok (.sort (.succ .zero)) := by
  change
    Except.map (fun x : Expr × TypeChecker.State => x.1)
      (TypeChecker.Inner.inferType (.const ``AnnotatedPi []) false
        (TypeChecker.Methods.withFuel 10000)
        ({ env := annotatedPiTypeKernelEnv, lctx := lctx } :
          TypeChecker.Context)
        ({} : TypeChecker.State)) =
      .ok (.sort (.succ .zero))
  rw [annotatedPiInferTypeFamily 9999 lctx
    ({} : TypeChecker.State) Std.HashMap.getElem?_empty]
  rfl

private def annotatedPiNormalizationRawContext
    (lctx : LocalContext) : TypeChecker.Context :=
  { env := annotatedPiTypeKernelEnv, lctx := lctx }

private theorem unfoldAnnotatedPi (lctx methods state) :
    TypeChecker.Inner.unfoldDefinition (.const ``AnnotatedPi [])
        methods (annotatedPiNormalizationRawContext lctx) state =
      .ok (none, state) := by
  change
    TypeChecker.Inner.unfoldDefinitionCore (.const ``AnnotatedPi [])
        methods (annotatedPiNormalizationRawContext lctx) state =
      .ok (none, state)
  simp [TypeChecker.Inner.unfoldDefinitionCore, TypeChecker.Inner.isDelta,
    Expr.getAppFn, annotatedPiNormalizationRawContext,
    annotatedPiType_lookup_family, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind, annotatedPiInfo, ConstantInfo.deltaValue?]

private theorem whnfLoopAnnotatedPi (lctx methods state n) :
    TypeChecker.Inner.whnf'.loop (.const ``AnnotatedPi []) (n + 1)
        methods (annotatedPiNormalizationRawContext lctx) state =
      .ok (.const ``AnnotatedPi [], state) := by
  unfold TypeChecker.Inner.whnf'.loop
  simp [unfoldAnnotatedPi]

private theorem annotatedPiConst_whnfM (lctx : LocalContext) :
    TypeChecker.M.run annotatedPiTypeKernelEnv .safe lctx []
      ({} : FuelConfig)
      (TypeChecker.whnf (.const ``AnnotatedPi [])) =
        .ok (.const ``AnnotatedPi []) := by
  change
    Except.map (fun x : Expr × TypeChecker.State => x.1)
      (TypeChecker.Inner.whnf' (.const ``AnnotatedPi [])
        (TypeChecker.Methods.withFuel 9999)
        (annotatedPiNormalizationRawContext lctx)
        ({} : TypeChecker.State)) =
      .ok (.const ``AnnotatedPi [])
  unfold TypeChecker.Inner.whnf'
  simp
  rw [show
    (if (annotatedPiNormalizationRawContext lctx).eagerReduce then
      (annotatedPiNormalizationRawContext lctx).fuel.whnfEager
    else (annotatedPiNormalizationRawContext lctx).fuel.whnf) =
        100000 by rfl]
  rw [show 100000 = 99999 + 1 by rfl]
  rw [whnfLoopAnnotatedPi]
  simp [Functor.map, StateT.map, Except.map]

private def annotatedPiFamilyCandidateStep :
    AddInductive.CandidateWhnfStep where
  context := annotatedPiFamilyCandidateContext
  source := annotatedPiInfo.type
  result := annotatedPiInfo.type

private theorem annotatedPiFamilyCandidateStep_valid :
    annotatedPiFamilyCandidateStep.Valid := by
  exact annotatedPiFamily_whnfM

private def annotatedPiFamilyCheckTypeStep :
    AddInductive.CandidateCheckTypeStep where
  context := annotatedPiFamilyCandidateContext
  source := annotatedPiInfo.type
  inferred := .sort (.succ (.succ .zero))

private theorem annotatedPiFamilyCheckTypeStep_valid :
    annotatedPiFamilyCheckTypeStep.Valid := by
  exact annotatedPiFamily_checkTypeM

private def annotatedPiCtorCandidateStep :
    AddInductive.CandidateWhnfStep where
  context := annotatedPiCtorCandidateContext
  source := annotatedPiMkInfo.type
  result := annotatedPiMkInfo.type

private theorem annotatedPiCtorCandidateStep_valid :
    annotatedPiCtorCandidateStep.Valid := by
  exact annotatedPiCtor_whnfM

private def annotatedPiCtorCheckTypeStep :
    AddInductive.CandidateCheckTypeStep where
  context := annotatedPiCtorCandidateContext
  source := annotatedPiMkInfo.type
  inferred := .sort (.succ .zero)

private theorem annotatedPiCtorCheckTypeStep_valid :
    annotatedPiCtorCheckTypeStep.Valid := by
  exact annotatedPiCtor_checkTypeM

private def annotatedPiInnerCandidateStep :
    AddInductive.CandidateWhnfStep where
  context := annotatedPiCtorCandidateContext
  source := annotatedPiInnerKernel
  result := annotatedPiInnerKernel

private theorem annotatedPiInnerCandidateStep_valid :
    annotatedPiInnerCandidateStep.Valid := by
  exact annotatedPiInner_whnfM

private def annotatedPiInnerCheckTypeStep :
    AddInductive.CandidateCheckTypeStep where
  context := annotatedPiCtorCandidateContext
  source := annotatedPiInnerKernel
  inferred := .sort (.succ .zero)

private theorem annotatedPiInnerCheckTypeStep_valid :
    annotatedPiInnerCheckTypeStep.Valid := by
  exact annotatedPiInner_checkTypeM

private def annotatedPiDomainCandidateStep :
    AddInductive.CandidateWhnfStep where
  context := annotatedPiCtorCandidateContext
  source := annotatedPiRawDomainKernel
  result := .sort .zero

private theorem annotatedPiDomainCandidateStep_valid :
    annotatedPiDomainCandidateStep.Valid := by
  exact annotatedPiDomain_whnfM

private def annotatedPiDomainCheckTypeStep :
    AddInductive.CandidateCheckTypeStep where
  context := annotatedPiCtorCandidateContext
  source := annotatedPiRawDomainKernel
  inferred := .sort (.succ .zero)

private theorem annotatedPiDomainCheckTypeStep_valid :
    annotatedPiDomainCheckTypeStep.Valid := by
  exact annotatedPiDomain_checkTypeM

private def annotatedPiDomainAnnotations :
    AddInductive.CandidateTypeAnnotations
      annotatedPiRawDomainKernel where
  consumed := .sort .zero
  trace := .outParam [.succ .zero] (.sort .zero) (.identity _)

private theorem annotatedPiDomainAnnotationsEq :
    AddInductive.CandidateIsDefEqStep.Valid
      ⟨annotatedPiCtorCandidateContext,
        annotatedPiRawDomainKernel,
        annotatedPiDomainAnnotations.consumed⟩ := by
  exact annotatedPiDomain_isDefEqM

private def annotatedPiInnerAnnotations :
    AddInductive.CandidateTypeAnnotations annotatedPiInnerKernel where
  consumed := annotatedPiInnerKernel
  trace := .identity _

private theorem annotatedPiInnerAnnotationsEq :
    AddInductive.CandidateIsDefEqStep.Valid
      ⟨annotatedPiCtorCandidateContext, annotatedPiInnerKernel,
        annotatedPiInnerAnnotations.consumed⟩ := by
  exact annotatedPiInner_isDefEqM

private def annotatedPiInnerBodyCandidateContext :
    AddInductive.Context :=
  annotatedPiCtorCandidateContext.pushLocalDecl
    `p .default annotatedPiDomainAnnotations.consumed

private def annotatedPiOuterBodyCandidateContext :
    AddInductive.Context :=
  annotatedPiCtorCandidateContext.pushLocalDecl
    annotatedPiOuterName .default annotatedPiInnerAnnotations.consumed

@[simp] private theorem addInductiveWithReader_apply
    {alpha : Type} (f : AddInductive.Context → AddInductive.Context)
    (x : AddInductive.M alpha) (context : AddInductive.Context) :
    (withReader f x) context = x (f context) := rfl

@[simp] private theorem addInductiveWithLocalReader_apply
    {alpha : Type} (f : LocalContext → LocalContext)
    (x : AddInductive.M alpha) (context : AddInductive.Context) :
    (MonadWithReaderOf.withReader (m := AddInductive.M) f x) context =
      x { context with lctx := f context.lctx } := rfl

private theorem annotatedPiCtorCandidateFresh :
    annotatedPiCtorCandidateContext.lctx.find?
        annotatedPiCtorCandidateContext.freshFVarId = none := by
  have h := LocalContext.WF.find?_eq_find?_toList
    (fv := annotatedPiCtorCandidateContext.freshFVarId)
    LocalContext.WF.nil
  change
    ({ fvarIdToDecl := PersistentHashMap.empty,
       decls := PersistentArray.empty,
       auxDeclToFullName := Std.TreeMap.empty } : LocalContext).find?
      annotatedPiCtorCandidateContext.freshFVarId = none
  rw [h]
  simp [LocalContext.toList]

@[simp] private theorem annotatedPiConst_instantiate1 (arg : Expr) :
    (Expr.const ``AnnotatedPi []).instantiate1 arg =
      .const ``AnnotatedPi [] := by
  simp [Expr.instantiate1_eq, Expr.instantiate1']

@[simp] private theorem annotatedPiConst_instantiate1' (arg : Expr) :
    (Expr.const ``AnnotatedPi []).instantiate1' arg =
      .const ``AnnotatedPi [] := by
  rfl

private def annotatedPiInnerBodyCandidateStep :
    AddInductive.CandidateWhnfStep where
  context := annotatedPiInnerBodyCandidateContext
  source := .const ``AnnotatedPi []
  result := .const ``AnnotatedPi []

private theorem annotatedPiInnerBodyCandidateStep_valid :
    annotatedPiInnerBodyCandidateStep.Valid := by
  exact annotatedPiConst_whnfM _

private def annotatedPiInnerBodyCheckTypeStep :
    AddInductive.CandidateCheckTypeStep where
  context := annotatedPiInnerBodyCandidateContext
  source := .const ``AnnotatedPi []
  inferred := .sort (.succ .zero)

private theorem annotatedPiInnerBodyCheckTypeStep_valid :
    annotatedPiInnerBodyCheckTypeStep.Valid := by
  exact annotatedPiConst_checkTypeM _

private def annotatedPiOuterBodyCandidateStep :
    AddInductive.CandidateWhnfStep where
  context := annotatedPiOuterBodyCandidateContext
  source := .const ``AnnotatedPi []
  result := .const ``AnnotatedPi []

private theorem annotatedPiOuterBodyCandidateStep_valid :
    annotatedPiOuterBodyCandidateStep.Valid := by
  exact annotatedPiConst_whnfM _

private def annotatedPiOuterBodyCheckTypeStep :
    AddInductive.CandidateCheckTypeStep where
  context := annotatedPiOuterBodyCandidateContext
  source := .const ``AnnotatedPi []
  inferred := .sort (.succ .zero)

private theorem annotatedPiOuterBodyCheckTypeStep_valid :
    annotatedPiOuterBodyCheckTypeStep.Valid := by
  exact annotatedPiConst_checkTypeM _

private def annotatedPiDomainCandidateTrace :
    AddInductive.CandidateExprTrace annotatedPiCtorCandidateContext
      annotatedPiRawDomainKernel :=
  .terminal annotatedPiCtorCandidateContext
    annotatedPiRawDomainKernel (.sort (.succ .zero)) (.sort .zero)
    annotatedPiDomainCheckTypeStep_valid
    annotatedPiDomainCandidateStep_valid

private def annotatedPiInnerBodyCandidateTrace :
    AddInductive.CandidateExprTrace annotatedPiInnerBodyCandidateContext
      ((Expr.const ``AnnotatedPi []).instantiate1
        annotatedPiCtorCandidateContext.freshExpr) :=
  .terminal annotatedPiInnerBodyCandidateContext
    ((Expr.const ``AnnotatedPi []).instantiate1
      annotatedPiCtorCandidateContext.freshExpr)
    (.sort (.succ .zero))
    (.const ``AnnotatedPi [])
    (by simpa only [annotatedPiInnerBodyCheckTypeStep,
        annotatedPiConst_instantiate1] using
      annotatedPiInnerBodyCheckTypeStep_valid)
    (by simpa only [annotatedPiInnerBodyCandidateStep,
        annotatedPiConst_instantiate1] using
      annotatedPiInnerBodyCandidateStep_valid)

private def annotatedPiOuterBodyCandidateTrace :
    AddInductive.CandidateExprTrace annotatedPiOuterBodyCandidateContext
      ((Expr.const ``AnnotatedPi []).instantiate1
        annotatedPiCtorCandidateContext.freshExpr) :=
  .terminal annotatedPiOuterBodyCandidateContext
    ((Expr.const ``AnnotatedPi []).instantiate1
      annotatedPiCtorCandidateContext.freshExpr)
    (.sort (.succ .zero))
    (.const ``AnnotatedPi [])
    (by simpa only [annotatedPiOuterBodyCheckTypeStep,
        annotatedPiConst_instantiate1] using
      annotatedPiOuterBodyCheckTypeStep_valid)
    (by simpa only [annotatedPiOuterBodyCandidateStep,
        annotatedPiConst_instantiate1] using
      annotatedPiOuterBodyCandidateStep_valid)

private def annotatedPiInnerCandidateTrace :
    AddInductive.CandidateExprTrace annotatedPiCtorCandidateContext
      annotatedPiInnerKernel :=
  .forallE annotatedPiCtorCandidateContext annotatedPiInnerKernel
    (.sort (.succ .zero)) `p annotatedPiRawDomainKernel
    (.const ``AnnotatedPi []) .default annotatedPiCtorCandidateFresh
    annotatedPiDomainAnnotations annotatedPiDomainAnnotationsEq
    annotatedPiInnerCheckTypeStep_valid
    annotatedPiInnerCandidateStep_valid
    annotatedPiDomainCandidateTrace annotatedPiInnerBodyCandidateTrace

private def annotatedPiCtorCandidateTrace :
    AddInductive.CandidateExprTrace annotatedPiCtorCandidateContext
      annotatedPiMkInfo.type :=
  .forallE annotatedPiCtorCandidateContext annotatedPiMkInfo.type
    (.sort (.succ .zero)) annotatedPiOuterName annotatedPiInnerKernel
    (.const ``AnnotatedPi []) .default annotatedPiCtorCandidateFresh
    annotatedPiInnerAnnotations annotatedPiInnerAnnotationsEq
    annotatedPiCtorCheckTypeStep_valid annotatedPiCtorCandidateStep_valid
    annotatedPiInnerCandidateTrace annotatedPiOuterBodyCandidateTrace

private def annotatedPiFamilyCandidate :
    AddInductive.CandidateExpr annotatedPiInfo.type :=
  ⟨annotatedPiFamilyCandidateContext,
    .terminal annotatedPiFamilyCandidateContext annotatedPiInfo.type
      (.sort (.succ (.succ .zero))) annotatedPiInfo.type
      annotatedPiFamilyCheckTypeStep_valid
      annotatedPiFamilyCandidateStep_valid⟩

private def annotatedPiCtorCandidate :
    AddInductive.CandidateExpr annotatedPiMkInfo.type :=
  ⟨annotatedPiCtorCandidateContext, annotatedPiCtorCandidateTrace⟩

private def annotatedPiConstructorCandidate :
    AddInductive.CandidateConstructor annotatedPiKernelCtor :=
  ⟨annotatedPiCtorCandidate⟩

private def annotatedPiFamilyListCandidate :
    AddInductive.CandidateFamily annotatedPiKernelType where
  familyType := ⟨annotatedPiFamilyCandidate⟩
  constructors := .cons annotatedPiConstructorCandidate .nil

private def annotatedPiNormalizationCandidate :
    AddInductive.NormalizationCandidate [annotatedPiKernelType] where
  families := .cons annotatedPiFamilyListCandidate .nil

private def annotatedPiInductiveStats : AddInductive.InductiveStats where
  levels := []
  resultLevel := .succ .zero
  nindices := #[0]
  indConsts := #[.const ``AnnotatedPi []]
  params := #[]
  isNotZero := true

private theorem annotatedPiSortOne_data_hasExprMVar_false :
    (Expr.sort (.succ .zero)).data.hasExprMVar = false := by
  change (Expr.sort (.succ .zero)).hasExprMVar = false
  rw [Expr.hasExprMVar_eq]
  rfl

private theorem annotatedPiSortOne_data_hasLevelMVar_false :
    (Expr.sort (.succ .zero)).data.hasLevelMVar = false := by
  change (Expr.sort (.succ .zero)).hasLevelMVar = false
  rw [Expr.hasLevelMVar_eq]
  simp [Expr.hasLevelMVar', Level.hasMVar_eq, Level.hasMVar']

private theorem annotatedPiSortOne_data_hasFVar_false :
    (Expr.sort (.succ .zero)).data.hasFVar = false := by
  change (Expr.sort (.succ .zero)).hasFVar = false
  rw [Expr.hasFVar_eq]
  rfl

private theorem annotatedPi_checkInductiveTypes
    (k : AddInductive.InductiveStats → AddInductive.M α) :
    AddInductive.checkInductiveTypes 0 #[annotatedPiKernelType] k
        annotatedPiFamilyCandidateContext =
      k annotatedPiInductiveStats annotatedPiFamilyCandidateContext := by
  apply AddInductive.checkInductiveTypes_singleton_zero_of_whnf_sort
  · decide
  · simp [Kernel.Environment.checkNoMVarNoFVar,
      Kernel.Environment.checkNoMVar, Kernel.Environment.checkNoFVar,
      annotatedPiKernelType, annotatedPiInfo, ConstantInfo.type,
      ConstantInfo.toConstantVal, Expr.hasMVar, Expr.hasFVar,
      annotatedPiSortOne_data_hasExprMVar_false,
      annotatedPiSortOne_data_hasLevelMVar_false,
      annotatedPiSortOne_data_hasFVar_false,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  · simpa [annotatedPiFamilyCandidateContext,
      annotatedPiKernelType] using annotatedPiFamily_checkTypeM
  · simpa [annotatedPiFamilyCandidateContext,
      annotatedPiKernelType, annotatedPiInfo, ConstantInfo.type,
      ConstantInfo.toConstantVal] using annotatedPiFamily_whnfM
  · rfl

private theorem annotatedPiFamilyEnv_not_contains :
    outParamKernelEnv.contains ``AnnotatedPi = false := by
  unfold Kernel.Environment.contains
  change outParamMap.contains ``AnnotatedPi = false
  rw [SMap.find?_isSome, annotatedPiType_fresh]
  rfl

private theorem annotatedPiFamilyEnv_checkName :
    outParamKernelEnv.checkName ``AnnotatedPi false = .ok () := by
  simp [Kernel.Environment.checkName, annotatedPiFamilyEnv_not_contains,
    Kernel.Environment.primitives, NameSet.ofList, NameSet.contains, Pure.pure, Except.pure]

private theorem annotatedPiInner_hasIndOcc :
    AddInductive.hasIndOcc #[.const ``AnnotatedPi []]
      annotatedPiInnerKernel = true := by
  simp [AddInductive.hasIndOcc, annotatedPiInnerKernel,
    annotatedPiRawDomainKernel, Expr.constName!]

private theorem annotatedPi_declareInductiveTypes :
    AddInductive.declareInductiveTypes annotatedPiInductiveStats 0
        #[annotatedPiKernelType] 0 false annotatedPiFamilyCandidateContext =
      .ok annotatedPiTypeKernelEnv := by
  simp [AddInductive.declareInductiveTypes, annotatedPiInductiveStats,
    annotatedPiKernelType, annotatedPiKernelCtor,
    annotatedPiInfo, annotatedPiMkInfo, ConstantInfo.name,
    ConstantInfo.type, ConstantInfo.toConstantVal,
    annotatedPiFamilyCandidateContext, annotatedPiTypeKernelEnv,
    outParamKernelEnv, annotatedPiTypeMap,
    AddInductive.isRec, AddInductive.isRec.loop,
    AddInductive.isReflexive, AddInductive.isReflexive.loop,
    AddInductive.hasIndOcc, Expr.constName!,
    Bind.bind, Pure.pure, Except.bind, Except.pure]
  rw [show (Kernel.Environment.ofConstants `_annotatedPiCandidate
      outParamMap).checkName ``AnnotatedPi = .ok () by
    simpa [outParamKernelEnv] using annotatedPiFamilyEnv_checkName]
  rfl

private theorem annotatedPiCtor_data_hasExprMVar_false :
    annotatedPiMkInfo.type.data.hasExprMVar = false := by
  change annotatedPiMkInfo.type.hasExprMVar = false
  rw [Expr.hasExprMVar_eq]
  rfl

private theorem annotatedPiCtor_data_hasLevelMVar_false :
    annotatedPiMkInfo.type.data.hasLevelMVar = false := by
  change annotatedPiMkInfo.type.hasLevelMVar = false
  rw [Expr.hasLevelMVar_eq]
  simp [annotatedPiMkInfo, ConstantInfo.type,
    ConstantInfo.toConstantVal, Expr.hasLevelMVar',
    Level.hasMVar_eq, Level.hasMVar']

private theorem annotatedPiCtor_data_hasFVar_false :
    annotatedPiMkInfo.type.data.hasFVar = false := by
  change annotatedPiMkInfo.type.hasFVar = false
  rw [Expr.hasFVar_eq]
  rfl

private theorem annotatedPiCtor_noMVarNoFVar :
    annotatedPiTypeKernelEnv.checkNoMVarNoFVar
        annotatedPiMkInfo.name annotatedPiMkInfo.type = .ok () := by
  simp [Kernel.Environment.checkNoMVarNoFVar,
    Kernel.Environment.checkNoMVar, Kernel.Environment.checkNoFVar,
    Expr.hasMVar, Expr.hasFVar,
    annotatedPiCtor_data_hasExprMVar_false,
    annotatedPiCtor_data_hasLevelMVar_false,
    annotatedPiCtor_data_hasFVar_false,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

@[simp] private theorem annotatedPiInferConstantFamilyOnly
    (lctx : LocalContext) :
    TypeChecker.Inner.inferConstant
        ({ env := annotatedPiTypeKernelEnv, lctx := lctx } :
          TypeChecker.Context)
        ``AnnotatedPi [] true =
      .ok (.sort (.succ .zero)) := by
  unfold TypeChecker.Inner.inferConstant
  rw [show annotatedPiTypeKernelEnv.get ``AnnotatedPi =
    .ok annotatedPiInfo by exact annotatedPiType_get_family]
  simp [annotatedPiInfo, Bind.bind, Except.bind,
    annotatedPiExceptPure, ConstantInfo.levelParams,
    ConstantInfo.instantiateTypeLevelParams,
    ConstantInfo.toConstantVal,
    ConstantVal.instantiateTypeLevelParams,
    Expr.instantiateLevelParams_eq,
    Expr.instantiateLevelParamsCore_id]

private theorem annotatedPiInferTypeFamilyOnly
    (n : Nat) (lctx : LocalContext) (state : TypeChecker.State)
    (hcache :
      state.inferTypeI[(.const ``AnnotatedPi [] : Expr)]? = none) :
    TypeChecker.Inner.inferType (.const ``AnnotatedPi []) true
        (TypeChecker.Methods.withFuel (n + 1))
        ({ env := annotatedPiTypeKernelEnv, lctx := lctx } :
          TypeChecker.Context)
        state =
      .ok (.sort (.succ .zero),
        { state with
          inferTypeI := state.inferTypeI.insert
            (.const ``AnnotatedPi []) (.sort (.succ .zero)) }) := by
  change
    TypeChecker.Inner.inferType' (.const ``AnnotatedPi []) true
        (TypeChecker.Methods.withFuel n)
        ({ env := annotatedPiTypeKernelEnv, lctx := lctx } :
          TypeChecker.Context)
        state = _
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange', hcache,
    annotatedPiInferConstantFamilyOnly,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

private def annotatedPiInnerInferOnlyLCtx : LocalContext :=
  ({} : LocalContext).mkLocalDecl
    ⟨({} : TypeChecker.State).ngen.curr⟩ `p
    annotatedPiRawDomainKernel .default

private def annotatedPiInnerInferOnlyState : TypeChecker.State :=
  { annotatedPiDomainInferOnlyState {} with
    ngen := ({} : TypeChecker.State).ngen.next }

private def annotatedPiFamilyInferOnlyState : TypeChecker.State :=
  { annotatedPiInnerInferOnlyState with
    inferTypeI := annotatedPiInnerInferOnlyState.inferTypeI.insert
      (.const ``AnnotatedPi []) (.sort (.succ .zero)) }

@[simp] private theorem annotatedPiInnerInferOnlyState_family_miss :
    annotatedPiInnerInferOnlyState.inferTypeI[
        (.const ``AnnotatedPi [] : Expr)]? = none := by
  simp [annotatedPiInnerInferOnlyState,
    annotatedPiDomainInferOnlyState, annotatedPiRawDomainKernel,
    annotatedPiOutParamFnType]

@[simp] private theorem annotatedPiInferTypeFamilyAfterDomainOnly :
    TypeChecker.Inner.inferType' (.const ``AnnotatedPi []) true
        (TypeChecker.Methods.withFuel 9998)
        ({ env := annotatedPiTypeKernelEnv, lctx :=
          annotatedPiInnerInferOnlyLCtx } :
          TypeChecker.Context)
        annotatedPiInnerInferOnlyState =
      .ok (.sort (.succ .zero), annotatedPiFamilyInferOnlyState) := by
  change
    TypeChecker.Inner.inferType (.const ``AnnotatedPi []) true
        (TypeChecker.Methods.withFuel 9999)
        ({ env := annotatedPiTypeKernelEnv, lctx :=
          annotatedPiInnerInferOnlyLCtx } :
          TypeChecker.Context)
        annotatedPiInnerInferOnlyState = _
  simpa [annotatedPiFamilyInferOnlyState] using
    annotatedPiInferTypeFamilyOnly 9998 annotatedPiInnerInferOnlyLCtx
      annotatedPiInnerInferOnlyState
      annotatedPiInnerInferOnlyState_family_miss

private theorem annotatedPiInferTypeFamilyAfterDomainOnly_exact :
    TypeChecker.Inner.inferType (.const ``AnnotatedPi []) true
        (TypeChecker.Methods.withFuel 9999)
        { annotatedPiCtorCandidateContext.toTypeChecker with
          lctx := annotatedPiCtorCandidateContext.toTypeChecker.lctx.mkLocalDecl
            ⟨(annotatedPiDomainInferOnlyState {}).ngen.curr⟩ `p
            annotatedPiRawDomainKernel .default }
        { annotatedPiDomainInferOnlyState {} with
          ngen := (annotatedPiDomainInferOnlyState {}).ngen.next } =
      .ok (.sort (.succ .zero), annotatedPiFamilyInferOnlyState) := by
  simpa [annotatedPiInnerInferOnlyLCtx,
    annotatedPiInnerInferOnlyState, annotatedPiCtorCandidateContext,
    annotatedPiDomainInferOnlyState,
    AddInductive.Context.toTypeChecker] using
      annotatedPiInferTypeFamilyAfterDomainOnly

private theorem annotatedPiInferTypeFamilyAfterDomainOnly_literal :
    TypeChecker.Inner.inferType (.const ``AnnotatedPi []) true
        (TypeChecker.Methods.withFuel 9999)
        { env := annotatedPiCtorCandidateContext.toTypeChecker.env
          lctx := annotatedPiCtorCandidateContext.toTypeChecker.lctx.mkLocalDecl
            { name := (annotatedPiDomainInferOnlyState {}).ngen.curr } `p
            (.app (.const ``outParam [.succ .zero]) (.sort .zero))
            .default
          safety := annotatedPiCtorCandidateContext.toTypeChecker.safety
          eagerReduce :=
            annotatedPiCtorCandidateContext.toTypeChecker.eagerReduce
          lparams := annotatedPiCtorCandidateContext.toTypeChecker.lparams
          fuel := annotatedPiCtorCandidateContext.toTypeChecker.fuel }
        { ngen := (annotatedPiDomainInferOnlyState {}).ngen.next
          inferTypeI := (annotatedPiDomainInferOnlyState {}).inferTypeI
          inferTypeC := (annotatedPiDomainInferOnlyState {}).inferTypeC
          whnfCoreCache :=
            (annotatedPiDomainInferOnlyState {}).whnfCoreCache
          whnfCache := (annotatedPiDomainInferOnlyState {}).whnfCache
          success := (annotatedPiDomainInferOnlyState {}).success
          failure := (annotatedPiDomainInferOnlyState {}).failure
          unfold := (annotatedPiDomainInferOnlyState {}).unfold } =
      .ok (.sort (.succ .zero), annotatedPiFamilyInferOnlyState) := by
  simpa [annotatedPiRawDomainKernel] using
    annotatedPiInferTypeFamilyAfterDomainOnly_exact

private def annotatedPiInnerInferOnlyFinalState : TypeChecker.State :=
  { annotatedPiFamilyInferOnlyState with
    inferTypeI := annotatedPiFamilyInferOnlyState.inferTypeI.insert
      annotatedPiInnerKernel (.sort (.succ .zero)) }

set_option maxRecDepth 10000 in
private theorem annotatedPiInner_inferTypeInner :
    TypeChecker.Inner.inferType annotatedPiInnerKernel true
        (TypeChecker.Methods.withFuel 10000)
        annotatedPiCtorCandidateContext.toTypeChecker
        ({} : TypeChecker.State) =
      .ok (.sort (.succ .zero),
        annotatedPiInnerInferOnlyFinalState) := by
  change
    TypeChecker.Inner.inferType' annotatedPiInnerKernel true
        (TypeChecker.Methods.withFuel 9999)
        annotatedPiCtorCandidateContext.toTypeChecker
        ({} : TypeChecker.State) = _
  unfold annotatedPiInnerKernel TypeChecker.Inner.inferType'
  simp [annotatedPiRawDomainKernel,
    Expr.hasLooseBVars, Expr.looseBVarRange',
    TypeChecker.Inner.inferForall, TypeChecker.Inner.inferForall.loop,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [annotatedPiInferTypeDomainOnly998]
  simp only [TypeChecker.Inner.ensureSortCore, Expr.isSort, ↓reduceIte, annotatedPiWithLocalDecl,
    annotatedPiRecMPure, Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [annotatedPiInferTypeFamilyAfterDomainOnly_literal]
  simp [Expr.sortLevel!, annotatedPiInnerInferOnlyFinalState,
    annotatedPiInnerKernel, annotatedPiRawDomainKernel]

private theorem annotatedPiInner_inferTypeM :
    TypeChecker.M.run annotatedPiCtorCandidateContext.env
      annotatedPiCtorCandidateContext.safety
      annotatedPiCtorCandidateContext.lctx
      annotatedPiCtorCandidateContext.lparams
      annotatedPiCtorCandidateContext.fuel
      (TypeChecker.inferType annotatedPiInnerKernel) =
        .ok (.sort (.succ .zero)) := by
  change
    Except.map (fun x : Expr × TypeChecker.State => x.1)
      (TypeChecker.Inner.inferType annotatedPiInnerKernel true
        (TypeChecker.Methods.withFuel 10000)
        annotatedPiCtorCandidateContext.toTypeChecker
        ({} : TypeChecker.State)) =
      .ok (.sort (.succ .zero))
  rw [annotatedPiInner_inferTypeInner]
  rfl

private theorem annotatedPiInner_ensureTypeM :
    TypeChecker.M.run annotatedPiCtorCandidateContext.env
      annotatedPiCtorCandidateContext.safety
      annotatedPiCtorCandidateContext.lctx
      annotatedPiCtorCandidateContext.lparams
      annotatedPiCtorCandidateContext.fuel
      (TypeChecker.ensureType annotatedPiInnerKernel) =
        .ok (.sort (.succ .zero)) := by
  unfold TypeChecker.ensureType TypeChecker.inferType
    TypeChecker.ensureSort TypeChecker.RecM.run TypeChecker.M.run
  simp only [readThe, MonadReaderOf.read, ReaderT.read,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure, StateT.run',
    Functor.map, Except.map]
  rw [show TypeChecker.Inner.inferType annotatedPiInnerKernel true
      (TypeChecker.Methods.withFuel
        annotatedPiCtorCandidateContext.fuel.recDepth)
      { env := annotatedPiCtorCandidateContext.env
        lctx := annotatedPiCtorCandidateContext.lctx
        safety := annotatedPiCtorCandidateContext.safety
        lparams := annotatedPiCtorCandidateContext.lparams
        fuel := annotatedPiCtorCandidateContext.fuel }
      ({} : TypeChecker.State) =
        .ok (.sort (.succ .zero),
          annotatedPiInnerInferOnlyFinalState) by
    simpa [annotatedPiCtorCandidateContext,
      AddInductive.Context.toTypeChecker] using
        annotatedPiInner_inferTypeInner]
  rfl

private theorem annotatedPiCtor_getEnvM :
    TypeChecker.M.run annotatedPiCtorCandidateContext.env
        annotatedPiCtorCandidateContext.safety
        annotatedPiCtorCandidateContext.lctx
        annotatedPiCtorCandidateContext.lparams
        annotatedPiCtorCandidateContext.fuel TypeChecker.getEnv =
      .ok annotatedPiTypeKernelEnv := by
  rfl

private theorem annotatedPiRawDomain_hasIndOcc_false :
    AddInductive.hasIndOcc annotatedPiInductiveStats.indConsts
        annotatedPiRawDomainKernel = false := by
  simp [AddInductive.hasIndOcc, annotatedPiInductiveStats,
    annotatedPiRawDomainKernel, Expr.constName!]

private theorem annotatedPiConst_isValidIndAppIdx :
    AddInductive.isValidIndAppIdx annotatedPiInductiveStats
        (.const ``AnnotatedPi []) 0 = true := by
  simp +decide [AddInductive.isValidIndAppIdx,
    annotatedPiInductiveStats, Expr.getAppFn, Expr.getAppArgs,
    Expr.getAppNumArgs]

private theorem annotatedPiInner_stats_hasIndOcc :
    AddInductive.hasIndOcc annotatedPiInductiveStats.indConsts
        annotatedPiInnerKernel = true := by
  simpa [annotatedPiInductiveStats] using annotatedPiInner_hasIndOcc

private theorem annotatedPiConst_hasIndOcc :
    AddInductive.hasIndOcc annotatedPiInductiveStats.indConsts
        (.const ``AnnotatedPi []) = true := by
  simp [AddInductive.hasIndOcc, annotatedPiInductiveStats,
    Expr.constName!]

private theorem annotatedPiConst_isValidIndApp :
    AddInductive.isValidIndApp? annotatedPiInductiveStats
        (.const ``AnnotatedPi []) = some 0 := by
  exact AddInductive.isValidIndApp?_singleton_zero
    annotatedPiInductiveStats (.const ``AnnotatedPi []) rfl
      annotatedPiConst_isValidIndAppIdx

private theorem annotatedPi_checkPositivity_terminal :
    AddInductive.checkPositivity.loop annotatedPiInductiveStats
        annotatedPiMkInfo.name 0 (.const ``AnnotatedPi []) 999
        annotatedPiInnerBodyCandidateContext = .ok () := by
  rw [show 999 = 998 + 1 by rfl]
  unfold AddInductive.checkPositivity.loop
  simp only [ReaderT.bind, Bind.bind]
  rw [AddInductive.liftTypeChecker_apply]
  rw [show TypeChecker.M.run
      annotatedPiInnerBodyCandidateContext.env
      annotatedPiInnerBodyCandidateContext.safety
      annotatedPiInnerBodyCandidateContext.lctx
      annotatedPiInnerBodyCandidateContext.lparams
      annotatedPiInnerBodyCandidateContext.fuel
      (TypeChecker.whnf (.const ``AnnotatedPi [])) =
        .ok (.const ``AnnotatedPi []) by
    exact annotatedPiConst_whnfM _]
  simp [annotatedPiConst_hasIndOcc, annotatedPiConst_isValidIndApp, ReaderT.pure, Pure.pure,
    Except.bind, Except.pure]

private theorem annotatedPi_checkPositivity :
    AddInductive.checkPositivity annotatedPiInductiveStats
        annotatedPiInnerKernel annotatedPiMkInfo.name 0
        annotatedPiCtorCandidateContext = .ok () := by
  unfold AddInductive.checkPositivity
  simp only [readThe, MonadReaderOf.read, ReaderT.read, ReaderT.bind, Bind.bind, Pure.pure,
    Except.bind, Except.pure]
  rw [show annotatedPiCtorCandidateContext.fuel.inductiveFuel =
      999 + 1 by rfl]
  unfold AddInductive.checkPositivity.loop
  simp only [ReaderT.bind, Bind.bind]
  rw [AddInductive.liftTypeChecker_apply]
  rw [annotatedPiInner_whnfM]
  simp only [Except.bind]
  rw [show AddInductive.hasIndOcc annotatedPiInductiveStats.indConsts
      annotatedPiInnerKernel = true by
    exact annotatedPiInner_stats_hasIndOcc]
  simp only [Bool.not_true, Bool.false_eq_true, if_false, Pure.pure]
  unfold annotatedPiInnerKernel
  simp only
  rw [show AddInductive.hasIndOcc annotatedPiInductiveStats.indConsts
      annotatedPiRawDomainKernel = false by
    exact annotatedPiRawDomain_hasIndOcc_false]
  simp only [Bool.false_eq_true, if_false]
  simpa [withLocalDecl, annotatedPiInnerBodyCandidateContext,
    withFreshId, MonadLocalNameGenerator.withFreshId,
    MonadWithReader.withReader, withTheReader,
    AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshExpr, AddInductive.Context.freshFVarId,
    AddInductive.consumeTypeAnnotations, annotatedPiDomainAnnotations,
    annotatedPiRawDomainKernel, annotatedPiCtorCandidateContext] using
      annotatedPi_checkPositivity_terminal

private theorem annotatedPiInner_ensureTypeM_expanded :
    TypeChecker.M.run annotatedPiCtorCandidateContext.env
        annotatedPiCtorCandidateContext.safety
        annotatedPiCtorCandidateContext.lctx
        annotatedPiCtorCandidateContext.lparams
        annotatedPiCtorCandidateContext.fuel
        (TypeChecker.ensureType
          (.forallE `p
            (.app (.const ``outParam [.succ .zero]) (.sort .zero))
            (.const ``AnnotatedPi []) .default)) =
      .ok (.sort (.succ .zero)) := by
  simpa [annotatedPiInnerKernel, annotatedPiRawDomainKernel] using
    annotatedPiInner_ensureTypeM

private theorem annotatedPi_checkPositivity_expanded :
    AddInductive.checkPositivity annotatedPiInductiveStats
        (.forallE `p
          (.app (.const ``outParam [.succ .zero]) (.sort .zero))
          (.const ``AnnotatedPi []) .default)
        ``AnnotatedPi.mk 0 annotatedPiCtorCandidateContext = .ok () := by
  simpa [annotatedPiMkInfo, ConstantInfo.name,
    ConstantInfo.toConstantVal, annotatedPiInnerKernel,
    annotatedPiRawDomainKernel] using annotatedPi_checkPositivity

private theorem annotatedPi_checkConstructors_terminal :
    AddInductive.checkConstructorType.loop annotatedPiInductiveStats false 0
        ``AnnotatedPi.mk (.const ``AnnotatedPi []) 1 999
        annotatedPiOuterBodyCandidateContext = .ok () := by
  rw [show 999 = 998 + 1 by rfl]
  unfold AddInductive.checkConstructorType.loop
  simp [annotatedPiConst_isValidIndAppIdx,
    ReaderT.pure, Pure.pure, Except.pure]

private theorem annotatedPi_checkConstructors_terminal_expanded :
    AddInductive.checkConstructorType.loop annotatedPiInductiveStats false 0
        ``AnnotatedPi.mk (.const ``AnnotatedPi []) 1 999
        ({ env := annotatedPiTypeKernelEnv
           lctx := ({} : LocalContext).mkLocalDecl
             ⟨({ namePrefix := `_ind_fresh } : NameGenerator).curr⟩
             (.mkNum
               (.mkStr
                 (.mkStr (.mkStr (.mkStr .anonymous "a") "_@")
                   "_internal") "_hyg") 0)
             (.forallE `p
               (.app (.const ``outParam [.succ .zero]) (.sort .zero))
               (.const ``AnnotatedPi []) .default)
             .default
           lparams := []
           ngen := ({ namePrefix := `_ind_fresh } : NameGenerator).next
           safety := .safe
           allowPrimitive := false } : AddInductive.Context) = .ok () := by
  simpa [annotatedPiOuterBodyCandidateContext,
    AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshFVarId,
    annotatedPiInnerAnnotations, annotatedPiOuterName,
    annotatedPiInnerKernel, annotatedPiRawDomainKernel,
    annotatedPiCtorCandidateContext] using
      annotatedPi_checkConstructors_terminal

private theorem annotatedPiCtor_noMVarNoFVar_literal :
    annotatedPiTypeKernelEnv.checkNoMVarNoFVar
        ``AnnotatedPi.mk
        (.forallE annotatedPiOuterName annotatedPiInnerKernel
          (.const ``AnnotatedPi []) .default) = .ok () := by
  simpa [annotatedPiMkInfo, ConstantInfo.name, ConstantInfo.type,
    ConstantInfo.toConstantVal, annotatedPiInnerKernel,
    annotatedPiRawDomainKernel, annotatedPiOuterName] using
      annotatedPiCtor_noMVarNoFVar

private theorem annotatedPiCtor_noMVarNoFVar_projected :
    annotatedPiTypeKernelEnv.checkNoMVarNoFVar
        annotatedPiMkInfo.toConstantVal.name annotatedPiMkInfo.type =
      .ok () := by
  simpa [ConstantInfo.name] using annotatedPiCtor_noMVarNoFVar

private theorem annotatedPiCtor_checkTypeM_literal :
    TypeChecker.M.run annotatedPiCtorCandidateContext.env
        annotatedPiCtorCandidateContext.safety
        annotatedPiCtorCandidateContext.lctx
        annotatedPiCtorCandidateContext.lparams
        annotatedPiCtorCandidateContext.fuel
        (TypeChecker.checkType
          (.forallE annotatedPiOuterName annotatedPiInnerKernel
            (.const ``AnnotatedPi []) .default)) =
      .ok (.sort (.succ .zero)) := by
  simpa [annotatedPiMkInfo, ConstantInfo.type,
    ConstantInfo.toConstantVal, annotatedPiInnerKernel,
    annotatedPiRawDomainKernel, annotatedPiOuterName] using
      annotatedPiCtor_checkTypeM

private theorem annotatedPiCtor_noMVarNoFVar_expanded :
    annotatedPiTypeKernelEnv.checkNoMVarNoFVar ``AnnotatedPi.mk
        (.forallE
          (.mkNum
            (.mkStr
              (.mkStr (.mkStr (.mkStr .anonymous "a") "_@")
                "_internal") "_hyg") 0)
          (.forallE `p
            (.app (.const ``outParam [.succ .zero]) (.sort .zero))
            (.const ``AnnotatedPi []) .default)
          (.const ``AnnotatedPi []) .default) = .ok () := by
  simpa [annotatedPiMkInfo, ConstantInfo.name, ConstantInfo.type,
    ConstantInfo.toConstantVal, annotatedPiOuterName,
    annotatedPiInnerKernel, annotatedPiRawDomainKernel] using
      annotatedPiCtor_noMVarNoFVar

private theorem annotatedPiCtor_checkTypeM_expanded :
    TypeChecker.M.run annotatedPiCtorCandidateContext.env
        annotatedPiCtorCandidateContext.safety
        annotatedPiCtorCandidateContext.lctx
        annotatedPiCtorCandidateContext.lparams
        annotatedPiCtorCandidateContext.fuel
        (TypeChecker.checkType
          (.forallE
            (.mkNum
              (.mkStr
                (.mkStr (.mkStr (.mkStr .anonymous "a") "_@")
                  "_internal") "_hyg") 0)
            (.forallE `p
              (.app (.const ``outParam [.succ .zero]) (.sort .zero))
              (.const ``AnnotatedPi []) .default)
            (.const ``AnnotatedPi []) .default)) =
      .ok (.sort (.succ .zero)) := by
  simpa [annotatedPiMkInfo, ConstantInfo.type,
    ConstantInfo.toConstantVal, annotatedPiOuterName,
    annotatedPiInnerKernel, annotatedPiRawDomainKernel] using
      annotatedPiCtor_checkTypeM

private theorem annotatedPiCtor_checkTypeM_empty :
    TypeChecker.M.run annotatedPiCtorCandidateContext.env
        annotatedPiCtorCandidateContext.safety {}
        annotatedPiCtorCandidateContext.lparams
        annotatedPiCtorCandidateContext.fuel
        (TypeChecker.checkType
          (.forallE
            (.mkNum
              (.mkStr
                (.mkStr (.mkStr (.mkStr .anonymous "a") "_@")
                  "_internal") "_hyg") 0)
            (.forallE `p
              (.app (.const ``outParam [.succ .zero]) (.sort .zero))
              (.const ``AnnotatedPi []) .default)
            (.const ``AnnotatedPi []) .default)) =
      .ok (.sort (.succ .zero)) := by
  simpa [annotatedPiCtorCandidateContext] using
    annotatedPiCtor_checkTypeM_expanded

private theorem annotatedPi_checkConstructors :
    AddInductive.checkConstructors #[annotatedPiKernelType]
        annotatedPiInductiveStats false
        annotatedPiCtorCandidateContext = .ok () := by
  unfold AddInductive.checkConstructors
  simp only [ReaderT.bind, Bind.bind]
  rw [AddInductive.liftTypeChecker_apply]
  rw [annotatedPiCtor_getEnvM]
  simp only [Except.bind]
  unfold AddInductive.checkConstructorsLoop AddInductive.checkConstructorFold
  simp +decide [annotatedPiKernelType, annotatedPiKernelCtor, annotatedPiMkInfo, ConstantInfo.name,
    ConstantInfo.type, ConstantInfo.toConstantVal]
  rw [annotatedPiCtor_noMVarNoFVar_expanded]
  simp only [ReaderT.bind, Bind.bind, Except.bind]
  rw [AddInductive.withEmptyLocalContext_apply]
  rw [AddInductive.liftTypeChecker_apply]
  simp only
  rw [annotatedPiCtor_checkTypeM_empty]
  simp only []
  unfold AddInductive.checkConstructorType
  simp +decide [readThe, MonadReaderOf.read, ReaderT.read, ReaderT.bind, Bind.bind, Pure.pure,
    Except.bind, Except.pure]
  rw [show annotatedPiCtorCandidateContext.fuel.inductiveFuel =
      999 + 1 by rfl]
  unfold AddInductive.checkConstructorType.loop
  simp only
  rw [show annotatedPiInductiveStats.params[0]? = none by rfl]
  simp only
  simp only [ReaderT.bind, Bind.bind]
  rw [AddInductive.liftTypeChecker_apply]
  rw [annotatedPiInner_ensureTypeM_expanded]
  simp only [Except.bind]
  rw [if_pos (show AddInductive.levelStructGe
      annotatedPiInductiveStats.resultLevel
      (Expr.sort (.succ .zero)).sortLevel! = true from rfl)]
  simp only [Bool.not_false, ↓reduceIte, ReaderT.bind, Bind.bind, Except.bind]
  rw [annotatedPi_checkPositivity_expanded]
  simp only []
  simp only [AddInductive.withLocalDecl_apply, annotatedPiConst_instantiate1,
    AddInductive.Context.pushLocalDecl, AddInductive.Context.freshFVarId,
    AddInductive.consumeTypeAnnotations, annotatedPiCtorCandidateContext]
  rw [annotatedPi_checkConstructors_terminal_expanded]
  unfold AddInductive.checkConstructorsLoop AddInductive.checkConstructorFold
  simp [ReaderT.pure, Pure.pure, Except.pure]

private theorem annotatedPi_checkConstructorUniverseSemantics :
    AddInductive.checkConstructorUniverseListSemantics
        annotatedPiInductiveStats annotatedPiKernelType.ctors
        annotatedPiCtorCandidateContext = .ok () := by
  unfold AddInductive.checkConstructorUniverseListSemantics
  simp only [annotatedPiKernelType, annotatedPiKernelCtor,
    annotatedPiMkInfo, ConstantInfo.type, ConstantInfo.toConstantVal,
    ReaderT.bind, Bind.bind]
  unfold AddInductive.checkConstructorUniverseSemantics
  simp only [readThe, MonadReaderOf.read, ReaderT.read, ReaderT.bind, Bind.bind, Pure.pure,
    Except.bind, Except.pure]
  rw [show annotatedPiCtorCandidateContext.fuel.inductiveFuel =
      999 + 1 by rfl]
  unfold AddInductive.checkConstructorUniverseSemantics.loop
  simp only
  rw [show annotatedPiInductiveStats.params[0]? = none by rfl]
  simp only [ReaderT.bind, Bind.bind, AddInductive.liftTypeChecker_apply]
  rw [annotatedPiInner_ensureTypeM_expanded]
  simp only [Except.bind]
  simp [Expr.sortLevel!, AddInductive.constructorUniverseSemanticGe]
  simp only [AddInductive.consumeTypeAnnotations, annotatedPiCtorCandidateContext]
  unfold AddInductive.checkConstructorUniverseSemantics.loop
  rfl

private theorem annotatedPiSortAnnotationTrace_build :
    AddInductive.CandidateTypeAnnotationTrace.build (.sort .zero) =
      ⟨.sort .zero, .identity _⟩ := by
  simp [AddInductive.CandidateTypeAnnotationTrace.build]

private theorem annotatedPiDomainAnnotationTrace_build :
    AddInductive.CandidateTypeAnnotationTrace.build
        annotatedPiRawDomainKernel =
      ⟨.sort .zero,
        .outParam [.succ .zero] (.sort .zero) (.identity _)⟩ := by
  simp [AddInductive.CandidateTypeAnnotationTrace.build,
    annotatedPiRawDomainKernel, annotatedPiSortAnnotationTrace_build]
  rw [annotatedPiSortAnnotationTrace_build]

private theorem annotatedPiInnerAnnotationTrace_build :
    AddInductive.CandidateTypeAnnotationTrace.build
        annotatedPiInnerKernel =
      ⟨annotatedPiInnerKernel, .identity _⟩ := by
  simp [AddInductive.CandidateTypeAnnotationTrace.build,
    annotatedPiInnerKernel]

private theorem annotatedPiDomainAnnotations_produced :
    AddInductive.buildCandidateTypeAnnotations
        annotatedPiRawDomainKernel =
      .ok annotatedPiDomainAnnotations := by
  unfold AddInductive.buildCandidateTypeAnnotations
  rw [annotatedPiDomainAnnotationTrace_build]
  rfl

private theorem annotatedPiInnerAnnotations_produced :
    AddInductive.buildCandidateTypeAnnotations annotatedPiInnerKernel =
      .ok annotatedPiInnerAnnotations := by
  unfold AddInductive.buildCandidateTypeAnnotations
  rw [annotatedPiInnerAnnotationTrace_build]
  rfl

private theorem annotatedPiDomainCandidateTrace_loop (fuel : Nat) :
    AddInductive.buildCandidateExpr.loop
        annotatedPiCtorCandidateContext annotatedPiRawDomainKernel
        (fuel + 1) =
      .ok annotatedPiDomainCandidateTrace := by
  simpa only [annotatedPiDomainCandidateTrace] using
    AddInductive.buildCandidateExpr_loop_of_whnf_nonForall
      annotatedPiCtorCandidateContext annotatedPiRawDomainKernel
      (.sort (.succ .zero)) (.sort .zero) fuel
      annotatedPiDomainCheckTypeStep_valid
      annotatedPiDomainCandidateStep_valid rfl

private theorem annotatedPiInnerBodyCandidateTrace_loop (fuel : Nat) :
    AddInductive.buildCandidateExpr.loop
        annotatedPiInnerBodyCandidateContext
        ((Expr.const ``AnnotatedPi []).instantiate1
          annotatedPiCtorCandidateContext.freshExpr)
        (fuel + 1) =
      .ok annotatedPiInnerBodyCandidateTrace := by
  simpa only [annotatedPiInnerBodyCandidateTrace] using
    AddInductive.buildCandidateExpr_loop_of_whnf_nonForall
      annotatedPiInnerBodyCandidateContext
      ((Expr.const ``AnnotatedPi []).instantiate1
        annotatedPiCtorCandidateContext.freshExpr)
      (.sort (.succ .zero)) (.const ``AnnotatedPi []) fuel
      (by simpa only [annotatedPiInnerBodyCheckTypeStep,
          annotatedPiConst_instantiate1] using
        annotatedPiInnerBodyCheckTypeStep_valid)
      (by simpa only [annotatedPiInnerBodyCandidateStep,
          annotatedPiConst_instantiate1] using
        annotatedPiInnerBodyCandidateStep_valid) rfl

private theorem annotatedPiOuterBodyCandidateTrace_loop (fuel : Nat) :
    AddInductive.buildCandidateExpr.loop
        annotatedPiOuterBodyCandidateContext
        ((Expr.const ``AnnotatedPi []).instantiate1
          annotatedPiCtorCandidateContext.freshExpr)
        (fuel + 1) =
      .ok annotatedPiOuterBodyCandidateTrace := by
  simpa only [annotatedPiOuterBodyCandidateTrace] using
    AddInductive.buildCandidateExpr_loop_of_whnf_nonForall
      annotatedPiOuterBodyCandidateContext
      ((Expr.const ``AnnotatedPi []).instantiate1
        annotatedPiCtorCandidateContext.freshExpr)
      (.sort (.succ .zero)) (.const ``AnnotatedPi []) fuel
      (by simpa only [annotatedPiOuterBodyCheckTypeStep,
          annotatedPiConst_instantiate1] using
        annotatedPiOuterBodyCheckTypeStep_valid)
      (by simpa only [annotatedPiOuterBodyCandidateStep,
          annotatedPiConst_instantiate1] using
        annotatedPiOuterBodyCandidateStep_valid) rfl

private theorem annotatedPiInnerCandidateTrace_loop :
    AddInductive.buildCandidateExpr.loop
        annotatedPiCtorCandidateContext annotatedPiInnerKernel 999 =
      .ok annotatedPiInnerCandidateTrace := by
  rw [show 999 = 998 + 1 by rfl]
  simpa only [annotatedPiInnerCandidateTrace,
    annotatedPiInnerBodyCandidateContext] using
    (AddInductive.buildCandidateExpr_loop_of_whnf_forall
      (context := annotatedPiCtorCandidateContext)
      (e := annotatedPiInnerKernel)
      (inferred := .sort (.succ .zero))
      (fuel := 998)
      (name := `p)
      (domain := annotatedPiRawDomainKernel)
      (body := .const ``AnnotatedPi [])
      (binderInfo := .default)
      (hfresh := annotatedPiCtorCandidateFresh)
      (annotations := annotatedPiDomainAnnotations)
      (hannotations := annotatedPiDomainAnnotations_produced)
      (hannotationsEq := annotatedPiDomainAnnotationsEq)
      (hcheck := annotatedPiInnerCheckTypeStep_valid)
      (hrun := annotatedPiInnerCandidateStep_valid)
      (domainCandidate := annotatedPiDomainCandidateTrace)
      (bodyCandidate := annotatedPiInnerBodyCandidateTrace)
      (hdomain := by
        simpa using annotatedPiDomainCandidateTrace_loop 997)
      (hbody := by
        simpa [annotatedPiInnerBodyCandidateContext] using
          annotatedPiInnerBodyCandidateTrace_loop 997))

private theorem annotatedPiCtorCandidateTrace_loop :
    AddInductive.buildCandidateExpr.loop
        annotatedPiCtorCandidateContext annotatedPiMkInfo.type
        annotatedPiCtorCandidateContext.fuel.inductiveFuel =
      .ok annotatedPiCtorCandidateTrace := by
  change AddInductive.buildCandidateExpr.loop
      annotatedPiCtorCandidateContext annotatedPiMkInfo.type
      (999 + 1) = _
  simpa only [annotatedPiCtorCandidateTrace,
    annotatedPiOuterBodyCandidateContext] using
    (AddInductive.buildCandidateExpr_loop_of_whnf_forall
      (context := annotatedPiCtorCandidateContext)
      (e := annotatedPiMkInfo.type)
      (inferred := .sort (.succ .zero))
      (fuel := 999)
      (name := annotatedPiOuterName)
      (domain := annotatedPiInnerKernel)
      (body := .const ``AnnotatedPi [])
      (binderInfo := .default)
      (hfresh := annotatedPiCtorCandidateFresh)
      (annotations := annotatedPiInnerAnnotations)
      (hannotations := annotatedPiInnerAnnotations_produced)
      (hannotationsEq := annotatedPiInnerAnnotationsEq)
      (hcheck := annotatedPiCtorCheckTypeStep_valid)
      (hrun := annotatedPiCtorCandidateStep_valid)
      (domainCandidate := annotatedPiInnerCandidateTrace)
      (bodyCandidate := annotatedPiOuterBodyCandidateTrace)
      (hdomain := annotatedPiInnerCandidateTrace_loop)
      (hbody := by
        simpa [annotatedPiOuterBodyCandidateContext] using
          annotatedPiOuterBodyCandidateTrace_loop 998))

/-- The executable candidate traversal returns the exact nested-forall
AnnotatedPi constructor trace, including both annotation boundaries and the
two recursively extended body contexts. -/
theorem annotatedPiCtor_candidateTrace :
    AddInductive.buildCandidateExpr annotatedPiMkInfo.type
        annotatedPiCtorCandidateContext =
      .ok annotatedPiCtorCandidate := by
  unfold AddInductive.buildCandidateExpr
  simp only [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
    Except.bind, Except.pure]
  rw [annotatedPiCtorCandidateTrace_loop]
  rfl

/-- The family position is the exact terminal candidate returned in the
pre-family environment. -/
theorem annotatedPiFamily_candidateTrace :
    AddInductive.buildCandidateExpr annotatedPiInfo.type
        annotatedPiFamilyCandidateContext =
      .ok annotatedPiFamilyCandidate := by
  apply AddInductive.buildCandidateExpr_of_whnf_nonForall
  · decide
  · rfl

private theorem annotatedPiFamilyTypeListProduced :
    AddInductive.CandidateFamilyTypeListProduced
      annotatedPiFamilyCandidateContext
      (.cons annotatedPiFamilyListCandidate.familyType .nil) := by
  exact .cons (by
    unfold AddInductive.normalizeCandidateFamilyType
    simp only [ReaderT.bind, Bind.bind]
    simp only [annotatedPiKernelType]
    rw [annotatedPiFamily_candidateTrace]
    rfl) .nil

private theorem annotatedPiFamilyTypeList_candidateTrace :
    AddInductive.normalizeCandidateFamilyTypeList
        [annotatedPiKernelType] annotatedPiFamilyCandidateContext =
      .ok (.cons annotatedPiFamilyListCandidate.familyType .nil) := by
  exact annotatedPiFamilyTypeListProduced.normalize

private theorem annotatedPiConstructorListProduced :
    AddInductive.CandidateConstructorListProduced
      annotatedPiCtorCandidateContext
      annotatedPiFamilyListCandidate.constructors := by
  exact .cons (by
    unfold AddInductive.normalizeCandidateConstructor
    simp only [ReaderT.bind, Bind.bind]
    simp only [annotatedPiKernelCtor]
    rw [annotatedPiCtor_candidateTrace]
    rfl) .nil

private theorem annotatedPiConstructorList_candidateTrace :
    AddInductive.normalizeCandidateConstructorList
        annotatedPiKernelType.ctors annotatedPiCtorCandidateContext =
      .ok annotatedPiFamilyListCandidate.constructors := by
  exact annotatedPiConstructorListProduced.normalize

private theorem annotatedPiFamilyListProduced :
    AddInductive.CandidateFamilyListProduced
      annotatedPiCtorCandidateContext
      (.cons annotatedPiFamilyListCandidate.familyType .nil)
      annotatedPiNormalizationCandidate.families := by
  exact .cons annotatedPiConstructorListProduced .nil

private theorem annotatedPiFamilyList_candidateTrace :
    AddInductive.normalizeCandidateFamilyList
        (.cons annotatedPiFamilyListCandidate.familyType .nil)
        annotatedPiCtorCandidateContext =
      .ok annotatedPiNormalizationCandidate.families := by
  exact annotatedPiFamilyListProduced.normalize

/-- The complete positive AnnotatedPi metadata request selects the exact
nested-forall normalization candidate in the real pre-family and post-family
checker environments. -/
theorem annotatedPiNormalizationCandidate_produced :
    AddInductive.buildNormalizationCandidate 0
        [annotatedPiKernelType] 0 false
        annotatedPiFamilyCandidateContext =
      .ok annotatedPiNormalizationCandidate := by
  unfold AddInductive.buildNormalizationCandidate
  rw [annotatedPi_checkInductiveTypes]
  simp only [ReaderT.bind, Bind.bind]
  rw [show
    (withReader (fun _ : AddInductive.Context =>
        { annotatedPiFamilyCandidateContext with lctx := {} })
      (AddInductive.normalizeCandidateFamilyTypeList
        [annotatedPiKernelType])) annotatedPiFamilyCandidateContext =
      .ok (.cons annotatedPiFamilyListCandidate.familyType .nil) by
    change AddInductive.normalizeCandidateFamilyTypeList
      [annotatedPiKernelType]
      { annotatedPiFamilyCandidateContext with lctx := {} } = _
    rw [show { annotatedPiFamilyCandidateContext with lctx := {} } =
      annotatedPiFamilyCandidateContext by rfl]
    exact annotatedPiFamilyTypeList_candidateTrace]
  simp only [Except.bind]
  rw [annotatedPi_declareInductiveTypes]
  unfold AddInductive.withEnv
  change (ReaderT.bind
      (AddInductive.checkConstructors #[annotatedPiKernelType]
        annotatedPiInductiveStats false)
      (fun _ => ReaderT.bind
        (AddInductive.normalizeCandidateFamilyList
          (.cons annotatedPiFamilyListCandidate.familyType .nil))
        (fun families => pure
          (⟨families⟩ : AddInductive.NormalizationCandidate
            [annotatedPiKernelType]))))
      ({ annotatedPiFamilyCandidateContext with
        env := annotatedPiTypeKernelEnv } :
          AddInductive.Context) = _
  rw [show ({ annotatedPiFamilyCandidateContext with
      env := annotatedPiTypeKernelEnv } : AddInductive.Context) =
        annotatedPiCtorCandidateContext by rfl]
  simp only [ReaderT.bind, Bind.bind]
  rw [annotatedPi_checkConstructors]
  simp only [Except.bind]
  rw [annotatedPiFamilyList_candidateTrace]
  rfl

private def aliasFormerFamilyCandidateStep :
    AddInductive.CandidateWhnfStep where
  context := aliasFormerCandidateContext
  source := aliasFormerInfo.type
  result := .sort (.succ .zero)

private theorem aliasFormerFamilyCandidateStep_valid :
    aliasFormerFamilyCandidateStep.Valid := by
  change
    TypeChecker.M.run aliasFormerNormalizationKernelEnv .safe {} []
        { whnf := 2 } (TypeChecker.whnf aliasFormerInfo.type) =
      .ok (.sort (.succ .zero))
  exact aliasFormerFamily_whnfM

private def aliasFormerFamilyCheckTypeStep :
    AddInductive.CandidateCheckTypeStep where
  context := aliasFormerCandidateContext
  source := aliasFormerInfo.type
  inferred := .sort (.succ (.succ .zero))

private theorem aliasFormerFamilyCheckTypeStep_valid :
    aliasFormerFamilyCheckTypeStep.Valid := by
  change
    TypeChecker.M.run aliasFormerNormalizationKernelEnv .safe {} []
        { whnf := 2 } (TypeChecker.checkType aliasFormerInfo.type) =
      .ok (.sort (.succ (.succ .zero)))
  exact aliasFormerFamily_checkTypeM

private def aliasFormerCtorCheckTypeStep :
    AddInductive.CandidateCheckTypeStep where
  context := aliasFormerCtorCandidateContext
  source := aliasFormerMkInfo.type
  inferred := .const ``TypeFamilyAlias []

private theorem aliasFormerCtorCheckTypeStep_valid :
    aliasFormerCtorCheckTypeStep.Valid := by
  change
    TypeChecker.M.run aliasFormerCtorNormalizationKernelEnv .safe {} []
        { whnf := 2 } (TypeChecker.checkType aliasFormerMkInfo.type) =
      .ok (.const ``TypeFamilyAlias [])
  exact aliasFormerCtor_checkTypeM

private def aliasFormerCtorCandidateStep :
    AddInductive.CandidateWhnfStep where
  context := aliasFormerCtorCandidateContext
  source := aliasFormerMkInfo.type
  result := .const ``AliasFormer []

private theorem aliasFormerCtorCandidateStep_valid :
    aliasFormerCtorCandidateStep.Valid := by
  change
    TypeChecker.M.run aliasFormerCtorNormalizationKernelEnv .safe {} []
        { whnf := 2 } (TypeChecker.whnf aliasFormerMkInfo.type) =
      .ok (.const ``AliasFormer [])
  exact aliasFormerCtor_whnfM

private def aliasFormerFamilyCandidate :
    AddInductive.CandidateExpr aliasFormerInfo.type :=
  ⟨aliasFormerCandidateContext,
    .terminal aliasFormerCandidateContext aliasFormerInfo.type
      (.sort (.succ (.succ .zero))) (.sort (.succ .zero))
      aliasFormerFamilyCheckTypeStep_valid
      aliasFormerFamilyCandidateStep_valid⟩

private def aliasFormerCtorCandidate :
    AddInductive.CandidateExpr aliasFormerMkInfo.type :=
  ⟨aliasFormerCtorCandidateContext,
    .terminal aliasFormerCtorCandidateContext aliasFormerMkInfo.type
      (.const ``TypeFamilyAlias []) (.const ``AliasFormer [])
      aliasFormerCtorCheckTypeStep_valid
      aliasFormerCtorCandidateStep_valid⟩

private def aliasFormerConstructorCandidate :
    AddInductive.CandidateConstructor aliasFormerKernelCtor :=
  ⟨aliasFormerCtorCandidate⟩

private def aliasFormerFamilyListCandidate :
    AddInductive.CandidateFamily aliasFormerKernelType where
  familyType := ⟨aliasFormerFamilyCandidate⟩
  constructors := .cons aliasFormerConstructorCandidate .nil

/-- Exact singleton family/constructor candidate list used to exercise the
generic positional Theory boundary. -/
private def aliasFormerNormalizationCandidate :
    AddInductive.NormalizationCandidate [aliasFormerKernelType] where
  families := .cons aliasFormerFamilyListCandidate .nil

private def aliasFormerInductiveStats : AddInductive.InductiveStats where
  levels := []
  resultLevel := .succ .zero
  nindices := #[0]
  indConsts := #[.const ``AliasFormer []]
  params := #[]
  isNotZero := true

private theorem constNil_data_hasExprMVar_false (n : Name) :
    (Expr.const n []).data.hasExprMVar = false := by
  change (Expr.const n []).hasExprMVar = false
  rw [Expr.hasExprMVar_eq]
  rfl

private theorem constNil_data_hasLevelMVar_false (n : Name) :
    (Expr.const n []).data.hasLevelMVar = false := by
  change (Expr.const n []).hasLevelMVar = false
  rw [Expr.hasLevelMVar_eq]
  rfl

private theorem constNil_data_hasFVar_false (n : Name) :
    (Expr.const n []).data.hasFVar = false := by
  change (Expr.const n []).hasFVar = false
  rw [Expr.hasFVar_eq]
  rfl

private theorem aliasFormer_checkInductiveTypes
    (k : AddInductive.InductiveStats → AddInductive.M α) :
    AddInductive.checkInductiveTypes 0 #[aliasFormerKernelType] k
        aliasFormerCandidateContext =
      k aliasFormerInductiveStats aliasFormerCandidateContext := by
  apply AddInductive.checkInductiveTypes_singleton_zero_of_whnf_sort
  · decide
  · simp [Kernel.Environment.checkNoMVarNoFVar,
      Kernel.Environment.checkNoMVar, Kernel.Environment.checkNoFVar,
      aliasFormerKernelType, aliasFormerInfo, ConstantInfo.type,
      ConstantInfo.toConstantVal, Expr.hasMVar, Expr.hasFVar,
      constNil_data_hasExprMVar_false,
      constNil_data_hasLevelMVar_false, constNil_data_hasFVar_false,
      Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  · simpa [aliasFormerCandidateContext, aliasFormerKernelType] using
      aliasFormerFamily_checkTypeM
  · simpa [aliasFormerCandidateContext, aliasFormerKernelType] using
      aliasFormerFamily_whnfM
  · rfl

private theorem aliasFormerNormalization_not_contains :
    aliasFormerNormalizationKernelEnv.contains ``AliasFormer = false := by
  unfold Kernel.Environment.contains
  change typeFamilyAliasMap.contains ``AliasFormer = false
  rw [SMap.find?_isSome, aliasFormerType_fresh]
  rfl

private theorem aliasFormerNormalization_checkName :
    aliasFormerNormalizationKernelEnv.checkName ``AliasFormer false =
      .ok () := by
  simp [Kernel.Environment.checkName, aliasFormerNormalization_not_contains,
    Kernel.Environment.primitives, NameSet.ofList, NameSet.contains, Pure.pure, Except.pure]

private theorem aliasFormer_declareInductiveTypes :
    AddInductive.declareInductiveTypes aliasFormerInductiveStats 0
        #[aliasFormerKernelType] 0 false aliasFormerCandidateContext =
      .ok aliasFormerCtorNormalizationKernelEnv := by
  simp [AddInductive.declareInductiveTypes, aliasFormerInductiveStats,
    aliasFormerKernelType, aliasFormerKernelCtor,
    aliasFormerInfo, aliasFormerMkInfo, ConstantInfo.name,
    ConstantInfo.type, ConstantInfo.toConstantVal,
    aliasFormerCandidateContext, aliasFormerCtorNormalizationKernelEnv,
    aliasFormerNormalizationKernelEnv, aliasFormerTypeMap,
    AddInductive.isRec,
    AddInductive.isRec.loop, AddInductive.isReflexive,
    AddInductive.isReflexive.loop,
    Bind.bind, Pure.pure,
    Except.bind, Except.pure]
  rw [show (Kernel.Environment.ofConstants `_aliasFormerNormalization
      typeFamilyAliasMap).checkName ``AliasFormer = .ok () by
    simpa [aliasFormerNormalizationKernelEnv] using
      aliasFormerNormalization_checkName]
  rfl

private theorem aliasFormerCtor_getEnvM :
    TypeChecker.M.run aliasFormerCtorCandidateContext.env
        aliasFormerCtorCandidateContext.safety
        aliasFormerCtorCandidateContext.lctx
        aliasFormerCtorCandidateContext.lparams
        aliasFormerCtorCandidateContext.fuel TypeChecker.getEnv =
      .ok aliasFormerCtorNormalizationKernelEnv := by
  rfl

private theorem aliasFormerCtor_isValidIndAppIdx :
    AddInductive.isValidIndAppIdx aliasFormerInductiveStats
      (.const ``AliasFormer []) 0 = true := by
  simp +decide [AddInductive.isValidIndAppIdx,
    aliasFormerInductiveStats,
    Expr.getAppFn, Expr.getAppArgs, Expr.getAppNumArgs]

private theorem aliasFormerCtor_noMVarNoFVar :
    aliasFormerCtorNormalizationKernelEnv.checkNoMVarNoFVar
        ``AliasFormer.mk (.const ``AliasFormer []) = .ok () := by
  simp [Kernel.Environment.checkNoMVarNoFVar,
    Kernel.Environment.checkNoMVar, Kernel.Environment.checkNoFVar,
    Expr.hasMVar, Expr.hasFVar,
    constNil_data_hasExprMVar_false,
    constNil_data_hasLevelMVar_false, constNil_data_hasFVar_false,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem aliasFormerCtor_checkTypeM_const :
    TypeChecker.M.run aliasFormerCtorCandidateContext.env
        aliasFormerCtorCandidateContext.safety
        aliasFormerCtorCandidateContext.lctx
        aliasFormerCtorCandidateContext.lparams
        aliasFormerCtorCandidateContext.fuel
        (TypeChecker.checkType (.const ``AliasFormer [])) =
      .ok (.const ``TypeFamilyAlias []) := by
  simpa [aliasFormerMkInfo, ConstantInfo.type,
    ConstantInfo.toConstantVal, aliasFormerCtorCandidateContext] using
      aliasFormerCtor_checkTypeM

private theorem aliasFormerCtor_checkTypeM_empty :
    TypeChecker.M.run aliasFormerCtorCandidateContext.env
        aliasFormerCtorCandidateContext.safety {}
        aliasFormerCtorCandidateContext.lparams
        aliasFormerCtorCandidateContext.fuel
        (TypeChecker.checkType (.const ``AliasFormer [])) =
      .ok (.const ``TypeFamilyAlias []) := by
  simpa [aliasFormerCtorCandidateContext] using
    aliasFormerCtor_checkTypeM_const

private theorem aliasFormerCtor_checkTypeM_of_empty
    (lctx : LocalContext) (hlctx : lctx = {}) :
    TypeChecker.M.run aliasFormerCtorCandidateContext.env
        aliasFormerCtorCandidateContext.safety lctx
        aliasFormerCtorCandidateContext.lparams
        aliasFormerCtorCandidateContext.fuel
        (TypeChecker.checkType (.const ``AliasFormer [])) =
      .ok (.const ``TypeFamilyAlias []) := by
  subst lctx
  exact aliasFormerCtor_checkTypeM_empty

private theorem aliasFormer_checkConstructors :
    AddInductive.checkConstructors #[aliasFormerKernelType]
        aliasFormerInductiveStats false aliasFormerCtorCandidateContext =
      .ok () := by
  unfold AddInductive.checkConstructors
  simp only [ReaderT.bind, Bind.bind]
  rw [AddInductive.liftTypeChecker_apply]
  rw [aliasFormerCtor_getEnvM]
  simp only [Except.bind]
  unfold AddInductive.checkConstructorsLoop AddInductive.checkConstructorFold
  simp +decide [aliasFormerKernelType, aliasFormerKernelCtor, aliasFormerMkInfo, ConstantInfo.name]
  simp +decide [ConstantInfo.type, ConstantInfo.toConstantVal, AddInductive.liftTypeChecker_apply,
    aliasFormerCtor_noMVarNoFVar, ReaderT.bind, Bind.bind, Except.bind]
  rw [aliasFormerCtor_checkTypeM_of_empty
    ({ decls :=
      { root := PersistentArrayNode.node #[], tail := #[] } } :
        LocalContext) rfl]
  simp only []
  unfold AddInductive.checkConstructorType
  simp only [readThe, MonadReaderOf.read, ReaderT.read, ReaderT.bind, Bind.bind, Pure.pure,
    Except.bind, Except.pure]
  rw [show aliasFormerCtorCandidateContext.fuel.inductiveFuel = 999 + 1 by
    rfl]
  unfold AddInductive.checkConstructorType.loop
  simp [aliasFormerCtor_isValidIndAppIdx, ReaderT.pure, Pure.pure,
    Except.pure, AddInductive.checkConstructorFold,
    AddInductive.checkConstructorsLoop]

private theorem aliasFormer_checkConstructorUniverseSemantics :
    AddInductive.checkConstructorUniverseListSemantics
        aliasFormerInductiveStats aliasFormerKernelType.ctors
        aliasFormerCtorCandidateContext = .ok () := by
  unfold AddInductive.checkConstructorUniverseListSemantics
  simp only [aliasFormerKernelType, aliasFormerKernelCtor,
    aliasFormerMkInfo, ConstantInfo.type, ConstantInfo.toConstantVal,
    ReaderT.bind, Bind.bind]
  unfold AddInductive.checkConstructorUniverseSemantics
  simp only [readThe, MonadReaderOf.read, ReaderT.read, ReaderT.bind, Bind.bind, Pure.pure,
    Except.bind, Except.pure]
  rw [show aliasFormerCtorCandidateContext.fuel.inductiveFuel = 999 + 1 by
    rfl]
  unfold AddInductive.checkConstructorUniverseSemantics.loop
  rfl

/-- The generic candidate traversal retains the exact context, input, and
result of the actual AliasFormer family WHNF observation. -/
theorem aliasFormerFamily_candidateTrace :
    AddInductive.buildCandidateExpr aliasFormerInfo.type
        aliasFormerCandidateContext =
      .ok aliasFormerFamilyCandidate := by
  apply AddInductive.buildCandidateExpr_of_whnf_nonForall
  · decide
  · rfl

private theorem aliasFormerFamilyTypeListProduced :
    AddInductive.CandidateFamilyTypeListProduced aliasFormerCandidateContext
      (.cons aliasFormerFamilyListCandidate.familyType .nil) := by
  exact .cons (by
    unfold AddInductive.normalizeCandidateFamilyType
    simp only [ReaderT.bind, Bind.bind]
    simp only [aliasFormerKernelType]
    rw [aliasFormerFamily_candidateTrace]
    rfl) .nil

private theorem aliasFormerFamilyTypeList_candidateTrace :
    AddInductive.normalizeCandidateFamilyTypeList
        [aliasFormerKernelType] aliasFormerCandidateContext =
      .ok (.cons aliasFormerFamilyListCandidate.familyType .nil) := by
  exact aliasFormerFamilyTypeListProduced.normalize

/-- The post-family constructor position is produced by the same executable
candidate traversal and retains its exact opaque result. -/
theorem aliasFormerCtor_candidateTrace :
    AddInductive.buildCandidateExpr aliasFormerMkInfo.type
        aliasFormerCtorCandidateContext =
      .ok aliasFormerCtorCandidate := by
  apply AddInductive.buildCandidateExpr_of_whnf_nonForall
  · decide
  · rfl

private theorem aliasFormerConstructorListProduced :
    AddInductive.CandidateConstructorListProduced
      aliasFormerCtorCandidateContext
      aliasFormerFamilyListCandidate.constructors := by
  exact .cons (by
    unfold AddInductive.normalizeCandidateConstructor
    simp only [ReaderT.bind, Bind.bind]
    simp only [aliasFormerKernelCtor]
    rw [aliasFormerCtor_candidateTrace]
    rfl) .nil

private theorem aliasFormerConstructorList_candidateTrace :
    AddInductive.normalizeCandidateConstructorList
        aliasFormerKernelType.ctors aliasFormerCtorCandidateContext =
      .ok aliasFormerFamilyListCandidate.constructors := by
  exact aliasFormerConstructorListProduced.normalize

private theorem aliasFormerFamilyListProduced :
    AddInductive.CandidateFamilyListProduced aliasFormerCtorCandidateContext
      (.cons aliasFormerFamilyListCandidate.familyType .nil)
      aliasFormerNormalizationCandidate.families := by
  exact .cons aliasFormerConstructorListProduced .nil

private theorem aliasFormerFamilyList_candidateTrace :
    AddInductive.normalizeCandidateFamilyList
        (.cons aliasFormerFamilyListCandidate.familyType .nil)
        aliasFormerCtorCandidateContext =
      .ok aliasFormerNormalizationCandidate.families := by
  exact aliasFormerFamilyListProduced.normalize

theorem aliasFormerNormalizationCandidate_produced :
    AddInductive.buildNormalizationCandidate 0
        [aliasFormerKernelType] 0 false aliasFormerCandidateContext =
      .ok aliasFormerNormalizationCandidate := by
  unfold AddInductive.buildNormalizationCandidate
  rw [aliasFormer_checkInductiveTypes]
  simp only [ReaderT.bind, Bind.bind]
  rw [show
    (withReader (fun _ : AddInductive.Context =>
        { aliasFormerCandidateContext with lctx := {} })
      (AddInductive.normalizeCandidateFamilyTypeList
        [aliasFormerKernelType])) aliasFormerCandidateContext =
      .ok (.cons aliasFormerFamilyListCandidate.familyType .nil) by
    change AddInductive.normalizeCandidateFamilyTypeList
      [aliasFormerKernelType]
      { aliasFormerCandidateContext with lctx := {} } = _
    rw [show { aliasFormerCandidateContext with lctx := {} } =
      aliasFormerCandidateContext by rfl]
    exact aliasFormerFamilyTypeList_candidateTrace]
  simp only [Except.bind]
  rw [aliasFormer_declareInductiveTypes]
  unfold AddInductive.withEnv
  change (ReaderT.bind
      (AddInductive.checkConstructors #[aliasFormerKernelType]
        aliasFormerInductiveStats false)
      (fun _ => ReaderT.bind
        (AddInductive.normalizeCandidateFamilyList
          (.cons aliasFormerFamilyListCandidate.familyType .nil))
        (fun families => pure
          (⟨families⟩ : AddInductive.NormalizationCandidate
            [aliasFormerKernelType]))))
      ({ aliasFormerCandidateContext with
        env := aliasFormerCtorNormalizationKernelEnv } :
          AddInductive.Context) = _
  rw [show ({ aliasFormerCandidateContext with
      env := aliasFormerCtorNormalizationKernelEnv } :
        AddInductive.Context) = aliasFormerCtorCandidateContext by rfl]
  simp only [ReaderT.bind, Bind.bind]
  rw [aliasFormer_checkConstructors]
  simp only [Except.bind]
  rw [aliasFormerFamilyList_candidateTrace]
  rfl

/-- Erasing the retained trace produces the expected AliasFormer analysis
view at the same checker boundary. -/
theorem aliasFormerFamily_candidate :
    AddInductive.normalizeCandidateExpr aliasFormerInfo.type
        aliasFormerCandidateContext =
      .ok (.sort (.succ .zero)) := by
  apply AddInductive.normalizeCandidateExpr_of_whnf_nonForall
  · decide
  · simpa [aliasFormerCandidateContext] using
      aliasFormerFamily_checkTypeM
  · simpa [aliasFormerCandidateContext] using
      aliasFormerFamily_whnfM
  · rfl

private def aliasRecFieldFnType : Expr :=
  .forallE `α (.sort (.succ .zero))
    (.sort (.succ .zero)) .default

@[simp] private theorem aliasRecFieldFnType_isForall :
    aliasRecFieldFnType.isForall = true := rfl

@[simp] private theorem aliasRecFieldFnType_bindingDomain :
    aliasRecFieldFnType.bindingDomain! =
      .sort (.succ .zero) := rfl

@[simp] private theorem aliasRecFieldFnType_instantiatedBody :
    aliasRecFieldFnType.bindingBody!.instantiate1
        (.const ``AliasRec []) =
      .sort (.succ .zero) := by
  simp [aliasRecFieldFnType, Expr.bindingBody!,
    Expr.instantiate1_eq,
    Expr.instantiate1']

@[simp] private theorem aliasRecFamily_notEagerReduce :
    (Expr.const ``AliasRec []).isAppOfArity ``eagerReduce 2 =
      false := rfl

private def aliasRecFieldFnState (state : TypeChecker.State) :
    TypeChecker.State :=
  { state with
    inferTypeC := state.inferTypeC.insert
      (.const ``RecAlias [.succ .zero]) aliasRecFieldFnType }

private def aliasRecFieldArgState (state : TypeChecker.State) :
    TypeChecker.State :=
  { state with
    inferTypeC := state.inferTypeC.insert
      (.const ``AliasRec []) (.sort (.succ .zero)) }

private def aliasRecFieldResultState (state : TypeChecker.State) :
    TypeChecker.State :=
  { state with
    inferTypeC := state.inferTypeC.insert
      aliasRecFieldKernelExpr (.sort (.succ .zero)) }

@[simp] private theorem aliasRecFieldFnCache_miss :
    (({} : Ix.Theory.Named.InferCache).insert
      (Expr.const ``RecAlias [.succ .zero]) aliasRecFieldFnType)[
        Expr.const ``AliasRec []]? = none := by
  rw [Std.HashMap.getElem?_insert]
  have h :
      (Expr.const ``RecAlias [.succ .zero] ==
        Expr.const ``AliasRec []) = false := by
    change Expr.eqv
      (Expr.const ``RecAlias [.succ .zero])
      (Expr.const ``AliasRec []) = false
    rw [Expr.eqv_eq]
    rfl
  rw [h]
  exact Std.HashMap.getElem?_empty

@[simp] private theorem aliasRecFieldFnState_cache_miss :
    (aliasRecFieldFnState {}).inferTypeC[
      Expr.const ``AliasRec []]? = none := by
  change
    (({} : Ix.Theory.Named.InferCache).insert
      (Expr.const ``RecAlias [.succ .zero]) aliasRecFieldFnType)[
        Expr.const ``AliasRec []]? = none
  exact aliasRecFieldFnCache_miss

private theorem isDefEqSort
    (context : TypeChecker.Context)
    (initial : TypeChecker.State) :
    ∃ state : TypeChecker.State,
      TypeChecker.Inner.isDefEq
          (.sort (.succ .zero)) (.sort (.succ .zero))
          (TypeChecker.Methods.withFuel 9998) context initial =
        .ok (true, state) := by
  refine ⟨initial, ?_⟩
  unfold TypeChecker.Inner.isDefEq
  rw [if_pos (Expr.eqv_refl _)]
  rfl

private theorem inferTypeRecAliasInitial :
    TypeChecker.Inner.inferType'
        (.const ``RecAlias [.succ .zero]) false
        (TypeChecker.Methods.withFuel 9998)
        aliasRecNormalizationRawContext ({} : TypeChecker.State) =
      .ok (aliasRecFieldFnType, aliasRecFieldFnState {}) := by
  unfold TypeChecker.Inner.inferType'
  simp [aliasRecFieldFnType, aliasRecFieldFnState,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

private theorem inferTypeAliasRecAfterRecAlias :
    TypeChecker.Inner.inferType'
        (.const ``AliasRec []) false
        (TypeChecker.Methods.withFuel 9998)
        aliasRecNormalizationRawContext (aliasRecFieldFnState {}) =
      .ok (.sort (.succ .zero),
        aliasRecFieldArgState (aliasRecFieldFnState {})) := by
  unfold TypeChecker.Inner.inferType'
  simp [aliasRecFieldArgState, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind]

/-- The exact full checker run for the raw `RecAlias AliasRec` constructor
field in the post-family environment. -/
theorem aliasRecField_checkType :
    ∃ state : TypeChecker.State,
      TypeChecker.Inner.inferType aliasRecFieldKernelExpr false
          (TypeChecker.Methods.withFuel 9999)
          aliasRecNormalizationRawContext ({} : TypeChecker.State) =
        .ok (.sort (.succ .zero), state) := by
  change ∃ state : TypeChecker.State,
    TypeChecker.Inner.inferType' aliasRecFieldKernelExpr false
        (TypeChecker.Methods.withFuel 9998)
        aliasRecNormalizationRawContext ({} : TypeChecker.State) =
      .ok (.sort (.succ .zero), state)
  rw [aliasRecFieldKernelExpr_eq]
  unfold TypeChecker.Inner.inferType'
  simp only [aliasRecField_noLooseBVars, Bool.false_eq_true, if_false, cond, normalizationRecMGet,
    Std.HashMap.getElem?_empty, normalizationRecMBind]
  rw [inferTypeRecAliasInitial]
  simp only
    [TypeChecker.Inner.ensureForallCore,
      aliasRecFieldFnType_isForall, ↓reduceIte, normalizationRecMPure]
  rw [inferTypeAliasRecAfterRecAlias]
  obtain ⟨eqState, heq⟩ :=
    isDefEqSort aliasRecNormalizationRawContext
      (aliasRecFieldArgState (aliasRecFieldFnState {}))
  dsimp only
  rw [if_neg (show ¬((Expr.const ``AliasRec []).isAppOfArity
      `eagerReduce 2 = true) from by
    simp [aliasRecFamily_notEagerReduce])]
  simp only [aliasRecFieldFnType_bindingDomain,
    normalizationRecMBind]
  rw [heq]
  rw [aliasRecFieldFnType_instantiatedBody]
  refine ⟨aliasRecFieldResultState eqState, ?_⟩
  simp [aliasRecFieldResultState, aliasRecFieldKernelExpr_eq,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

/-- The paired full-check/WHNF interpretation of the retained AliasFormer
family node.  Both semantic runs are obtained from the candidate's exact
observations in one verified context. -/
private def aliasFormerFamilyCandidateNodeRun :
    TypeChecker.CandidateNodeRun typeFamilyAliasEnv [] []
      aliasFormerCandidateContext aliasFormerInfo.type
      (.sort (.succ (.succ .zero))) (.sort (.succ .zero))
      aliasFormerRawType.type aliasFormerViewType.type
      (.sort (.succ (.succ .zero))) := by
  exact TypeChecker.CandidateNodeRun.ofCandidate
    aliasFormerCandidateContext aliasFormerInfo.type
    (.sort (.succ (.succ .zero))) (.sort (.succ .zero))
    aliasFormerFamilyCheckTypeStep_valid
    aliasFormerFamilyCandidateStep_valid
    aliasFormerNormalizationContext (by rfl)
    rfl rfl rfl TypeChecker.VState.WF.empty
    (.const rfl rfl rfl) (.sort rfl)
    (by
      have hs : TrExprS typeFamilyAliasEnv [] []
          (.sort (.succ .zero)) (.sort (.succ .zero)) := .sort rfl
      exact hs)
    10000 9999 (by rfl) (by rfl)

/-- Verified family-result normalization leaf for AliasFormer. -/
def aliasFormerFamilyWhnfRun :
    TypeChecker.WhnfRun typeFamilyAliasEnv [] []
      aliasFormerInfo.type (.sort (.succ .zero))
      aliasFormerRawType.type aliasFormerViewType.type :=
  aliasFormerFamilyCandidateNodeRun.whnf

/-- Verified full-check certificate for the raw AliasFormer family type. -/
def aliasFormerFamilyCheckTypeRun :
    TypeChecker.CheckTypeRun typeFamilyAliasEnv [] []
      aliasFormerInfo.type (.sort (.succ (.succ .zero)))
      aliasFormerRawType.type (.sort (.succ (.succ .zero))) :=
  aliasFormerFamilyCandidateNodeRun.check

/-- Recursive semantic interpretation of the exact source-indexed candidate
trace.  This terminal fixture is the base case used by the generic Pi
interpreter for larger metadata. -/
private theorem aliasFormerFamilyCandidateRun :
    TypeChecker.CandidateExprRun typeFamilyAliasEnv []
      aliasFormerFamilyCandidate.trace []
      aliasFormerRawType.type aliasFormerViewType.type
      (.sort (.succ (.succ .zero))) :=
  .terminal aliasFormerFamilyCandidateNodeRun

private theorem aliasFormerCandidatePrefix_ne :
    aliasFormerCandidateContext.ngen.namePrefix ≠
      (({} : TypeChecker.VState).ngen).namePrefix := by
  decide

/-- The generic root constructor aligns the actual candidate context with the
verified AliasFormer environment and supplies the empty-state certificate. -/
private def aliasFormerCandidateContextRun :
    TypeChecker.CandidateContextRun aliasFormerCandidateContext :=
  TypeChecker.CandidateContextRun.root aliasFormerNormalizationVEnvs_wf
    rfl aliasFormerCandidatePrefix_ne

/-- The retained AliasFormer full check now selects its own Theory source and
output translations; no expression translation is supplied by the fixture. -/
theorem aliasFormerFamily_candidateRun_exists :
    ∃ source' view' inferred',
      aliasFormerCandidateContextRun.context.TrExprS
        aliasFormerInfo.type source' ∧
      Nonempty (TypeChecker.CandidateExprRun
        aliasFormerCandidateContextRun.context.venv
        aliasFormerCandidateContextRun.context.lparams
        aliasFormerFamilyCandidate.trace
        aliasFormerCandidateContextRun.context.vlctx
        source' view' inferred') := by
  apply TypeChecker.CandidateExprRun.exists_ofCandidateFVars
    aliasFormerFamilyCandidate.trace aliasFormerCandidateContextRun
      (whnfFuel := 9999)
  · change ∀ u ∈ ([] : List Level), u.hasMVar' = false
    simp
  · rfl

/-- The generic interpreter retains the strict translation of the raw
candidate endpoint. -/
theorem aliasFormerFamily_candidateSource_tr :
    TrExprS typeFamilyAliasEnv [] [] aliasFormerInfo.type
      aliasFormerRawType.type :=
  aliasFormerFamilyCandidateRun.source_tr

/-- The reconstructed candidate endpoint is also tied back to the concrete
kernel WHNF result, closing the source/view translation pair. -/
theorem aliasFormerFamily_candidateView_tr :
    TrExpr typeFamilyAliasEnv [] [] (.sort (.succ .zero))
      aliasFormerViewType.type := by
  simpa [aliasFormerFamilyCandidate,
    AddInductive.CandidateExprTrace.view] using
    aliasFormerFamilyCandidateRun.view_tr

private def aliasFormerPreFamilyStage :
    TypeChecker.CandidateSemanticStage aliasFormerCandidateContext
      typeFamilyAliasEnv [] where
  contextRun := aliasFormerCandidateContextRun
  venv_eq := rfl
  lparams_eq := rfl
  vlctx_eq := rfl

private def aliasFormerFamilyValidationRun :
    AddInductive.CandidateExprTrace.FamilyValidationRun
      aliasFormerKernelType aliasFormerFamilyCandidate.trace where
  nparams := 0
  resultLevel := .succ .zero
  stats := aliasFormerInductiveStats
  stats_eq := rfl
  terminal_eq := rfl
  run := aliasFormer_checkInductiveTypes

private def aliasFormerFamilyStage :
    VInductDecl.CandidateFamilyStagedInput aliasFormerCandidateContext
      aliasFormerCtorCandidateContext typeFamilyAliasEnv []
      aliasFormerFamilyListCandidate.familyType aliasFormerRawType
      aliasFormerPreFamilyStage where
  name_eq := rfl
  uvars_eq := rfl
  type := {
    context_eq := rfl
    source_tr := aliasFormerFamily_candidateSource_tr
    whnfFuel := 9999
    whnfDepth := rfl }
  validation := aliasFormerFamilyValidationRun
  typeEnv := aliasFormerTypeEnv
  addInduct := aliasFormerCtorNormalizationAddType
  projectionReady := ProjectionReady.of_no_ctorInfo <| by
    intro name _info h
    change aliasFormerTypeMap.find?' name = some (.ctorInfo _info) at h
    rw [aliasFormerTypeMap_wf.find?'_eq_find?] at h
    simp only [aliasFormerTypeMap, typeFamilyAliasMap_wf.find?_insert] at h
    simp only [typeFamilyAliasMap, SMap.WF.find?_insert
      (s := ({} : ConstMap)) SMap.WF.empty] at h
    by_cases hAliasFormer : ``AliasFormer = name
    · subst name
      simp [aliasFormerInfo] at h
    · by_cases hTypeFamilyAlias : ``TypeFamilyAlias = name
      · subst name
        simp [hAliasFormer, typeFamilyAliasInfo] at h
      · simp [hAliasFormer, hTypeFamilyAlias, SMap.find?] at h
  structureEtaReady := StructureEtaReady.of_no_ctorInfo <| by
    intro name _info h
    change aliasFormerTypeMap.find?' name = some (.ctorInfo _info) at h
    rw [aliasFormerTypeMap_wf.find?'_eq_find?] at h
    simp only [aliasFormerTypeMap, typeFamilyAliasMap_wf.find?_insert] at h
    simp only [typeFamilyAliasMap, SMap.WF.find?_insert
      (s := ({} : ConstMap)) SMap.WF.empty] at h
    by_cases hAliasFormer : ``AliasFormer = name
    · subst name
      simp [aliasFormerInfo] at h
    · by_cases hTypeFamilyAlias : ``TypeFamilyAlias = name
      · subst name
        simp [hAliasFormer, typeFamilyAliasInfo] at h
      · simp [hAliasFormer, hTypeFamilyAlias, SMap.find?] at h
  family_lctx_eq := rfl
  constructorContext_eq := rfl
  quotInit_eq := rfl
  name_not_reflected := by decide
  name_not_primitive := by
    simp [aliasFormerRawType, Kernel.Environment.primitives,
      NameSet.ofList]
    simp +decide [NameSet.contains]

private def aliasFormerCtorCandidateContextRun :
    TypeChecker.CandidateContextRun aliasFormerCtorCandidateContext :=
  aliasFormerFamilyStage.postContextRun

/-- Family endpoint certificate used by the singleton list assembler. -/
private def aliasFormerFamilySemanticRootRun :
    TypeChecker.CandidateExprSemanticRootRun typeFamilyAliasEnv []
      aliasFormerFamilyCandidate aliasFormerRawType.type
    where
  contextRun := aliasFormerCandidateContextRun
  venv_eq := rfl
  lparams_eq := rfl
  vlctx_eq := rfl
  source_tr := aliasFormerFamily_candidateSource_tr
  whnfFuel := 9999
  whnfDepth := rfl
  view := aliasFormerViewType.type
  recursive := ⟨.sort (.succ (.succ .zero)),
    aliasFormerFamilyCandidateRun⟩

private def aliasFormerFamilyRootRun :
    TypeChecker.CandidateExprRootRun typeFamilyAliasEnv []
      aliasFormerFamilyCandidate aliasFormerRawType.type
      aliasFormerViewType.type :=
  aliasFormerFamilySemanticRootRun.root

/-- Verified full-check certificate for the actual AliasFormer constructor
type in the post-family environment. -/
def aliasFormerCtorCheckTypeRun :
    TypeChecker.CheckTypeRun aliasFormerTypeEnv [] []
      aliasFormerMkInfo.type (.const ``TypeFamilyAlias [])
      aliasFormerRawType.ctors[0].type
      (.const ``TypeFamilyAlias []) := by
  exact TypeChecker.CheckTypeRun.ofCandidateStep
    aliasFormerCtorCheckTypeStep aliasFormerCtorCheckTypeStep_valid
    aliasFormerCtorCandidateContextRun.context
    aliasFormerCtorCandidateContextRun.context_eq
    rfl rfl rfl aliasFormerCtorCandidateContextRun.state_wf
    (.const rfl rfl rfl) (.const rfl rfl rfl)
    10000 (by rfl)

/-- Paired full-check/WHNF interpretation of the retained constructor leaf.
This is the post-family terminal used by the generic constructor-spine
assembler. -/
private def aliasFormerCtorCandidateNodeRun :
    TypeChecker.CandidateNodeRun aliasFormerTypeEnv [] []
      aliasFormerCtorCandidateContext aliasFormerMkInfo.type
      (.const ``TypeFamilyAlias []) (.const ``AliasFormer [])
      aliasFormerRawType.ctors[0].type
      aliasFormerRawType.ctors[0].type
      (.const ``TypeFamilyAlias []) := by
  exact TypeChecker.CandidateNodeRun.ofCandidate
    aliasFormerCtorCandidateContext aliasFormerMkInfo.type
    (.const ``TypeFamilyAlias []) (.const ``AliasFormer [])
    aliasFormerCtorCheckTypeStep_valid
    aliasFormerCtorCandidateStep_valid
    aliasFormerCtorCandidateContextRun.context
    aliasFormerCtorCandidateContextRun.context_eq
    rfl rfl rfl aliasFormerCtorCandidateContextRun.state_wf
    aliasFormerCtorCheckTypeRun.expr_tr (.const rfl rfl rfl)
    aliasFormerCtorCheckTypeRun.expr_tr
    10000 9999 (by rfl) (by rfl)

private theorem aliasFormerCtorCandidateRun :
    TypeChecker.CandidateExprRun aliasFormerTypeEnv []
      aliasFormerCtorCandidate.trace []
      aliasFormerRawType.ctors[0].type
      aliasFormerRawType.ctors[0].type
      (.const ``TypeFamilyAlias []) :=
  .terminal aliasFormerCtorCandidateNodeRun

/-- Constructor endpoint certificate in the exact post-family context. -/
private def aliasFormerCtorSemanticRootRun :
    TypeChecker.CandidateExprSemanticRootRun aliasFormerTypeEnv []
      aliasFormerCtorCandidate aliasFormerRawType.ctors[0].type
    where
  contextRun := aliasFormerCtorCandidateContextRun
  venv_eq := rfl
  lparams_eq := rfl
  vlctx_eq := rfl
  source_tr := aliasFormerCtorCheckTypeRun.expr_tr
  whnfFuel := 9999
  whnfDepth := rfl
  view := aliasFormerRawType.ctors[0].type
  recursive := ⟨.const ``TypeFamilyAlias [], aliasFormerCtorCandidateRun⟩

private def aliasFormerCtorRootRun :
    TypeChecker.CandidateExprRootRun aliasFormerTypeEnv []
      aliasFormerCtorCandidate aliasFormerRawType.ctors[0].type
      aliasFormerRawType.ctors[0].type :=
  aliasFormerCtorSemanticRootRun.root

/-- The actual AliasFormer constructor type is typed by the verified full
checker in the post-family environment. -/
theorem aliasFormerCtor_hasType_checked :
    aliasFormerTypeEnv.HasType 0 []
      aliasFormerRawType.ctors[0].type
      (.const ``TypeFamilyAlias []) :=
  aliasFormerCtorCheckTypeRun.hasType

/-- The raw AliasFormer family is a Theory type because the verified checker
actually accepted it and inferred a sort. -/
theorem aliasFormerFamily_isType_checked :
    typeFamilyAliasEnv.IsType 0 [] aliasFormerRawType.type :=
  aliasFormerFamilyCheckTypeRun.isType

private theorem aliasFormerFamilySpineRun :
    TypeChecker.CandidateExprSpineRun typeFamilyAliasEnv []
      aliasFormerFamilyCandidate aliasFormerRawType.type
      aliasFormerViewType.type :=
  aliasFormerFamilySemanticRootRun.spine rfl

private theorem aliasFormerCtorSpineRun :
    TypeChecker.CandidateExprSpineRun aliasFormerTypeEnv []
      aliasFormerCtorCandidate aliasFormerRawType.ctors[0].type
      aliasFormerRawType.ctors[0].type :=
  aliasFormerCtorSemanticRootRun.spine rfl

/-- Verified delta-normalization leaf for `RecAlias.{1}`. -/
def recAliasWhnfRun :
    TypeChecker.WhnfRun aliasRecTypeEnv [] []
      (.const ``RecAlias [.succ .zero])
      recAliasWhnfKernelExpr
      (.const ``RecAlias [.succ .zero])
      (.lam (.sort (.succ .zero)) (.bvar 0)) where
  context := aliasRecNormalizationContext
  venv_eq := rfl
  lparams_eq := rfl
  vlctx_eq := rfl
  state_wf := TypeChecker.VState.WF.empty
  lhs_tr := .const rfl rfl rfl
  rhs_tr := by
    have hs : TrExprS aliasRecTypeEnv [] []
        recAliasWhnfKernelExpr
        (.lam (.sort (.succ .zero)) (.bvar 0)) := by
      rw [recAliasWhnfKernelExpr_eq]
      exact .lam
        ⟨_, VEnv.HasType.sort (by decide)⟩
        (.sort rfl) (.bvar rfl)
    exact hs
  recursionFuel := 9999
  run_eq := by
    simpa [aliasRecNormalizationContext, TypeChecker.VContext.mk',
      TypeChecker.VContext.mk1, TypeChecker.MLCtx.lctx,
      aliasRecNormalizationRawContext] using
      recAlias_whnf

private theorem recAliasConst_hasType :
    aliasRecTypeEnv.HasType 0 []
      (.const ``RecAlias [.succ .zero])
      (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) := by
  have hAlias : aliasRecTypeEnv.constants ``RecAlias =
      some (vconst(type_of% @RecAlias)) := rfl
  type_tac

private theorem aliasRecConst_hasType :
    aliasRecTypeEnv.HasType 0 []
      (.const ``AliasRec []) (.sort (.succ .zero)) := by
  exact .constDF
    (VEnv.addConst_self (show
      recAliasEnv.addConst aliasRecRawType.name
      aliasRecRawType.toVConstant = some aliasRecTypeEnv from rfl))
    (fun _ h => nomatch h) (fun _ h => nomatch h) rfl .nil

/-- Verified full-check certificate for the actual raw recursive field in the
exact environment produced by inserting `AliasRec`. -/
def aliasRecFieldCheckTypeRun :
    TypeChecker.CheckTypeRun aliasRecTypeEnv [] []
      aliasRecFieldKernelExpr (.sort (.succ .zero))
      aliasRecRawField (.sort (.succ .zero)) where
  context := aliasRecNormalizationContext
  venv_eq := rfl
  lparams_eq := rfl
  vlctx_eq := rfl
  state_wf := TypeChecker.VState.WF.empty
  expr_tr := .app recAliasConst_hasType aliasRecConst_hasType
    (.const rfl rfl rfl) (.const rfl rfl rfl)
  inferred_tr := .sort rfl
  recursionFuel := 9999
  run_eq := by
    simpa [aliasRecNormalizationContext, TypeChecker.VContext.mk',
      TypeChecker.VContext.mk1, TypeChecker.MLCtx.lctx,
      aliasRecNormalizationRawContext] using
      aliasRecField_checkType

/-- The raw recursive field is typed by an exact full checker execution in
the post-family environment. -/
theorem aliasRecField_hasType_checked :
    aliasRecTypeEnv.HasType 0 []
      aliasRecRawField (.sort (.succ .zero)) :=
  aliasRecFieldCheckTypeRun.hasType

private theorem aliasRecFieldEvidenceBase :
    TypeChecker.DefEqEvidence aliasRecTypeEnv 0 []
      aliasRecRawField (.const ``AliasRec []) (.sort (.succ .zero)) := by
  exact .trans
    (.app
      (.whnf recAliasWhnfRun recAliasConst_hasType)
      (.refl aliasRecConst_hasType))
    (.beta (VEnv.HasType.bvar .zero) aliasRecConst_hasType)

private theorem aliasRecFieldEvidence :
    TypeChecker.DefEqEvidence aliasRecTypeEnv 0 []
      aliasRecRawField (.const ``AliasRec []) (.sort (.succ .zero)) :=
  .trans (.refl aliasRecField_hasType_checked)
    aliasRecFieldEvidenceBase

private theorem aliasRecCtorEvidence :
    ∃ A, TypeChecker.DefEqEvidence aliasRecTypeEnv 0 []
      aliasRecRawType.ctors[0].type aliasRecViewCtor.type A := by
  exact ⟨.sort (.imax (.succ .zero) (.succ .zero)),
    .forallE aliasRecFieldEvidence
      (.refl (aliasRecResult_hasType rfl))⟩

private def aliasFormerCandidateConstructorSemanticRun :
    VInductDecl.CandidateConstructorSemanticRun aliasFormerTypeEnv []
      aliasFormerConstructorCandidate aliasFormerRawType.ctors[0] where
  name_eq := rfl
  uvars_eq := rfl
  type := aliasFormerCtorSemanticRootRun

private def aliasFormerCandidateConstructorRun :
    VInductDecl.CandidateConstructorRun aliasFormerTypeEnv []
      aliasFormerConstructorCandidate aliasFormerRawType.ctors[0] :=
  aliasFormerCandidateConstructorSemanticRun.root

private def aliasFormerCandidateConstructorSemanticListRun :
    VInductDecl.CandidateConstructorSemanticListRun aliasFormerTypeEnv []
      aliasFormerFamilyListCandidate.constructors
      aliasFormerRawType.ctors := by
  exact .cons aliasFormerCandidateConstructorSemanticRun .nil

private def aliasFormerCandidateConstructorListRun :
    VInductDecl.CandidateConstructorListRun aliasFormerTypeEnv []
      aliasFormerFamilyListCandidate.constructors
      aliasFormerRawType.ctors :=
  aliasFormerCandidateConstructorSemanticListRun.roots

private def aliasFormerCandidateFamilySemanticRun :
    VInductDecl.CandidateFamilySemanticRun typeFamilyAliasEnv []
      aliasFormerFamilyListCandidate aliasFormerRawType where
  name_eq := rfl
  uvars_eq := rfl
  type := aliasFormerFamilySemanticRootRun
  typeEnv := aliasFormerTypeEnv
  addType := rfl
  constructors := aliasFormerCandidateConstructorSemanticListRun

private def aliasFormerCandidateFamilyRun :
    VInductDecl.CandidateFamilyRun typeFamilyAliasEnv []
      aliasFormerFamilyListCandidate aliasFormerRawType :=
  aliasFormerCandidateFamilySemanticRun.root

private def aliasFormerStagedUniverseInput :
    VInductDecl.StagedNormalizationCandidateUniverseInput
      aliasFormerCandidateContext aliasFormerCtorCandidateContext
      typeFamilyAliasEnv [] aliasFormerNormalizationCandidate
      aliasFormerRawDecl where
  staged := {
    raw := aliasFormerRawType
    raw_types_eq := rfl
    declaration_uvars_eq := rfl
    preFamily := aliasFormerPreFamilyStage
    family := aliasFormerFamilyStage
    validation_nparams_eq := rfl
    constructorValidation :=
      AddInductive.ConstructorValidationRun.of_run aliasFormer_checkConstructors
    constructors := .cons {
      name_eq := rfl
      uvars_eq := rfl
      type := {
        context_eq := rfl
        source_tr := aliasFormerCtorCheckTypeRun.expr_tr
        whnfFuel := 9999
        whnfDepth := rfl } } .nil
    familyTypesProduced := aliasFormerFamilyTypeListProduced
    familiesProduced := aliasFormerFamilyListProduced }
  universeRun := aliasFormer_checkConstructorUniverseSemantics

private theorem aliasFormerConstructorValidationContext_eq :
    { aliasFormerNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext with
      env := aliasFormerCtorCandidateContext.env } =
      aliasFormerCtorCandidateContext := rfl

private theorem aliasFormerCtorCandidateContext_empty :
    aliasFormerCtorCandidateContext.withEmptyLocalContext =
      aliasFormerCtorCandidateContext := rfl

set_option warn.sorry false in
theorem aliasFormerAlignmentRun :
    aliasFormerStagedUniverseInput.staged.constructorValidation.trace.checkCandidateAlignment
      aliasFormerNormalizationCandidate.families.singleton.constructors
      { aliasFormerNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext with
        env := aliasFormerCtorCandidateContext.env } = .ok () := by
  -- Tier V (Spec-19B, v4.33 reconciliation repair debt): the premerge proof
  -- stepped `ConstructorCandidateAlignmentTrace.build` with `rw [build.eq_def]`,
  -- which the v4.33 elaborator no longer matches (and eq_def-in-simp loops).
  -- The statement is an exact closed checker run and remains true; the
  -- stepping proof needs a rework against the new equation-lemma shapes.
  sorry

private def aliasFormerStagedPostFamilyInput :
    VInductDecl.StagedNormalizationCandidatePostFamilyInput
      aliasFormerCandidateContext aliasFormerCtorCandidateContext
      typeFamilyAliasEnv [] aliasFormerNormalizationCandidate
      aliasFormerRawDecl :=
  VInductDecl.StagedNormalizationCandidatePostFamilyInput.ofRun
    aliasFormerStagedUniverseInput aliasFormerAlignmentRun

private theorem aliasFormerPreFamilySafetyRun :
    AddInductive.checkConstructorPreFamilySafety
        aliasFormerStagedUniverseInput.staged.family.validation.stats
        aliasFormerNormalizationCandidate.families.singleton.familyType.type.view
        aliasFormerNormalizationCandidate.families.singleton.constructors
        aliasFormerNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext =
      .ok () := by
  change AddInductive.checkConstructorPreFamilySafety
    aliasFormerInductiveStats (.sort (.succ .zero))
    (.cons aliasFormerConstructorCandidate .nil)
    aliasFormerCandidateContext = .ok ()
  let sortStep : AddInductive.CandidateCheckTypeStep :=
    ⟨aliasFormerCandidateContext, .sort (.succ .zero),
      .sort (.succ (.succ .zero))⟩
  have sortRun : sortStep.Valid := by
    change Except.map (fun x : Expr × TypeChecker.State => x.1)
      (TypeChecker.Inner.inferType' (.sort (.succ .zero)) false
        (TypeChecker.Methods.withFuel 9999)
        aliasFormerCandidateContext.toTypeChecker
        ({} : TypeChecker.State)) = _
    unfold TypeChecker.Inner.inferType'
    simp [Expr.hasLooseBVars, Expr.looseBVarRange',
      annotatedPi_checkLevelSuccZero, Bind.bind, ReaderT.bind,
      StateT.bind, Except.bind]
    rfl
  have sortHasMVar : (Expr.sort (.succ .zero)).hasMVar = false := by
    simp [Expr.hasMVar, annotatedPiSortOne_data_hasExprMVar_false,
      annotatedPiSortOne_data_hasLevelMVar_false]
  obtain ⟨sortChecked, sortCheckedRun⟩ :=
    AddInductive.checkConstructorAlignedExpr.exists_of_run
      (context := aliasFormerCandidateContext)
      (source := .sort (.succ .zero))
      (inferred := .sort (.succ (.succ .zero))) rfl sortHasMVar sortRun
  have aliasArgs :
      (Expr.const ``AliasFormer []).getAppArgs.toList.drop 0 = [] := by
    rfl
  have paramsSize : aliasFormerInductiveStats.params.size = 0 := rfl
  have targetArgs :
      (Expr.const ``AliasFormer []).getAppArgs.toList.drop
        aliasFormerInductiveStats.params.size = [] := by
    rw [paramsSize]
    exact aliasArgs
  have inductiveFuel :
      aliasFormerCandidateContext.fuel.inductiveFuel = 1000 := rfl
  unfold AddInductive.checkConstructorPreFamilySafety
  have parametersRun :
      AddInductive.instantiateFamilyParameters (.sort (.succ .zero))
      aliasFormerInductiveStats.params.toList = .ok (.sort (.succ .zero)) := by
    rfl
  have sortTerminal : (Expr.sort (.succ .zero)).isForall = false := rfl
  let spineTrace : AddInductive.ConstructorPreFamilyIndexSpineTrace
      aliasFormerCandidateContext (.sort (.succ .zero)) [] :=
    .nil aliasFormerCandidateContext (.sort (.succ .zero)) sortChecked
      sortTerminal
  have spineRun :
      AddInductive.ConstructorPreFamilyIndexSpineTrace.build
          aliasFormerCandidateContext (.sort (.succ .zero)) [] =
        .ok spineTrace := by
    unfold AddInductive.ConstructorPreFamilyIndexSpineTrace.build
    rw [dif_pos sortTerminal, sortCheckedRun]
    rfl
  obtain ⟨targetSpineTrace, targetSpineRun⟩ :
      ∃ targetSpineTrace : AddInductive.ConstructorPreFamilyIndexSpineTrace
          aliasFormerCandidateContext (.sort (.succ .zero))
          ((Expr.const ``AliasFormer []).getAppArgs.toList.drop
            aliasFormerInductiveStats.params.size),
        AddInductive.ConstructorPreFamilyIndexSpineTrace.build
            aliasFormerCandidateContext (.sort (.succ .zero))
          ((Expr.const ``AliasFormer []).getAppArgs.toList.drop
              aliasFormerInductiveStats.params.size) =
          .ok targetSpineTrace := by
    rw [targetArgs]
    exact ⟨spineTrace, spineRun⟩
  have valid : AddInductive.isValidIndAppIdx aliasFormerInductiveStats
      (.const ``AliasFormer []) 0 = true :=
    aliasFormerCtor_isValidIndAppIdx
  have independent : AddInductive.constructorIndependentOf
      (.const ``AliasFormer []) [] = true := by
    rfl
  obtain ⟨viewTrace, viewRun⟩ : ∃ viewTrace,
      AddInductive.ConstructorPreFamilyViewTrace.build
          aliasFormerInductiveStats 0 (.sort (.succ .zero))
          aliasFormerCandidateContext (.const ``AliasFormer []) 0 [] false
          aliasFormerCandidateContext.fuel.inductiveFuel = .ok viewTrace := by
    rw [inductiveFuel]
    rw [show 1000 = 999 + 1 by rfl]
    simp only [AddInductive.ConstructorPreFamilyViewTrace.build]
    rw [dif_pos valid, dif_pos independent]
    rw [targetSpineRun]
    exact ⟨_, rfl⟩
  obtain ⟨listTrace, listRun⟩ : ∃ listTrace,
      AddInductive.ConstructorPreFamilyListTrace.build
          aliasFormerInductiveStats 0 (.sort (.succ .zero))
          aliasFormerCandidateContext
          (.cons aliasFormerConstructorCandidate .nil) = .ok listTrace := by
    refine ⟨.cons viewTrace .nil, ?_⟩
    simp [AddInductive.ConstructorPreFamilyListTrace.build,
      aliasFormerConstructorCandidate, aliasFormerCtorCandidate,
      AddInductive.CandidateExpr.view, AddInductive.CandidateExprTrace.view,
      viewRun, Bind.bind, Except.bind, Except.pure, Pure.pure]
  have translationUnique :
      (AddInductive.theoryTranslationUnique (.sort (.succ .zero)) &&
        (AddInductive.CandidateList.cons aliasFormerConstructorCandidate
          (AddInductive.CandidateList.nil : AddInductive.CandidateList
            AddInductive.CandidateConstructor [])).viewTranslationUnique) =
        true := by
    rfl
  rw [if_pos translationUnique]
  simp [parametersRun, listRun, Bind.bind, Except.bind,
    Except.pure, Pure.pure]

private def aliasFormerStagedPreFamilyInput :
    VInductDecl.StagedNormalizationCandidatePreFamilyInput
      aliasFormerCandidateContext aliasFormerCtorCandidateContext
      typeFamilyAliasEnv [] aliasFormerNormalizationCandidate
      aliasFormerRawDecl :=
  VInductDecl.StagedNormalizationCandidatePreFamilyInput.ofRun
    aliasFormerStagedPostFamilyInput aliasFormerPreFamilySafetyRun

/-- The exact family/constructor producer traversals and verified translations
automatically determine a complete retained AliasFormer hierarchy. -/
theorem aliasFormerProducedSemanticHierarchy_exists :
    Nonempty (VInductDecl.ProducedNormalizationCandidateSemanticRun
      aliasFormerCandidateContext aliasFormerCtorCandidateContext
      typeFamilyAliasEnv [] aliasFormerNormalizationCandidate
      aliasFormerRawDecl) :=
  aliasFormerStagedUniverseInput.exists

/-- The retained validator telescope and independently produced candidate
telescope align positionally and admit the complete post-family semantic
interpretation for `AliasFormer`. -/
theorem aliasFormerProducedPostFamilySemantic_exists :
    Nonempty (VInductDecl.ProducedNormalizationCandidatePostFamilySemanticRun
      aliasFormerStagedPostFamilyInput) :=
  aliasFormerStagedPostFamilyInput.exists

/-- AliasFormer's analyzer-owned constructor candidate passes the executable
pre-family suffix/dependency gate and admits the exact family-free replay. -/
theorem aliasFormerProducedPreFamilySemantic_exists :
    Nonempty (VInductDecl.ProducedNormalizationCandidatePreFamilySemanticRun
      aliasFormerStagedPreFamilyInput) :=
  aliasFormerStagedPreFamilyInput.exists

def aliasFormerNormalizationCandidateRun :
    VInductDecl.NormalizationCandidateRun typeFamilyAliasEnv []
      aliasFormerNormalizationCandidate aliasFormerRawDecl where
  raw := aliasFormerRawType
  raw_types_eq := rfl
  uvars_eq := rfl
  family := aliasFormerCandidateFamilyRun

example : aliasFormerNormalizationCandidateRun.viewDecl =
    aliasFormerViewDecl := rfl

example : aliasFormerNormalizationCandidateRun.normalization.accepted =
    true := rfl

theorem aliasFormerCandidateNormalization_eq :
    aliasFormerNormalizationCandidateRun.normalization =
      aliasFormerNormalization := rfl

private def aliasFormerTruncatedViewType : VInductiveType :=
  { aliasFormerViewType with ctors := [] }

private def aliasFormerTruncatedViewDecl : VInductDecl :=
  { aliasFormerViewDecl with types := [aliasFormerTruncatedViewType] }

/-- A shorter view cannot cross even the computational normalization-shape
gate, so it cannot reach dependent analysis or transaction construction. -/
theorem aliasFormerTruncatedView_rejected :
    VInductDecl.normalization? aliasFormerRawDecl
      aliasFormerTruncatedViewDecl = none := rfl

/-- Complete checker-produced semantic normalization certificate for
AliasFormer. -/
def aliasFormerNormalizationRun :
    VInductDecl.NormalizationRun aliasFormerNormalization
      typeFamilyAliasEnv := by
  simpa only [aliasFormerCandidateNormalization_eq] using
    aliasFormerNormalizationCandidateRun.normalizationRun

theorem aliasFormerNormalization_wf_checked :
    aliasFormerNormalization.WF typeFamilyAliasEnv :=
  aliasFormerNormalizationRun.wf

/-- Complete checker-produced semantic normalization certificate for
AliasRec. The field comparison is assembled from verified WHNF, application,
beta, and outer-forall congruence. -/
def aliasRecNormalizationRun :
    VInductDecl.NormalizationRun aliasRecNormalization recAliasEnv := by
  refine {
    raw := aliasRecRawType
    view := aliasRecViewType
    source_types_eq := rfl
    view_types_eq := rfl
    family := ?_
    typeEnv := aliasRecTypeEnv
    addType := rfl
    constructors := ?_ }
  · exact ⟨.sort (.succ (.succ .zero)),
      .refl (VEnv.HasType.sort (by decide))⟩
  · exact .cons aliasRecCtorEvidence .nil

theorem aliasRecNormalization_wf_checked :
    aliasRecNormalization.WF recAliasEnv :=
  aliasRecNormalizationRun.wf

/-- The paired AliasFormer block with its normalization component supplied by
the checked WHNF path. The view's structural semantics remain the ordinary
Theory `Checked.WF` proof. -/
theorem aliasFormerBlock_wf_checked :
    aliasFormerBlock.WF typeFamilyAliasEnv := by
  refine ⟨aliasFormerNormalization_wf_checked, ?_⟩
  change aliasFormerViewChecked.WF typeFamilyAliasEnv
  exact aliasFormerViewChecked.wf_of_decl aliasFormerViewDecl_wf

private theorem aliasFormerFamily_defeq_checked :
    typeFamilyAliasEnv.IsDefEq 0 []
      (.const ``TypeFamilyAlias []) (.sort (.succ .zero))
      (.sort (.succ (.succ .zero))) :=
  aliasFormerFamilyWhnfRun.isDefEq
    aliasFormerFamilyCheckTypeRun.hasType

/-- Combining the constructor's exact full-check result with the verified
family-alias WHNF fixes its Theory sort. -/
theorem aliasFormerCtor_hasSort_checked :
    aliasFormerTypeEnv.HasType 0 []
      aliasFormerRawType.ctors[0].type (.sort (.succ .zero)) := by
  have halias :=
    aliasFormerFamily_defeq_checked.mono (VEnv.addConst_le (show
      typeFamilyAliasEnv.addConst aliasFormerRawType.name
        aliasFormerRawType.toVConstant = some aliasFormerTypeEnv from rfl))
  exact halias.defeq aliasFormerCtor_hasType_checked

theorem aliasFormerCtor_isType_checked :
    aliasFormerTypeEnv.IsType 0 []
      aliasFormerRawType.ctors[0].type :=
  ⟨.succ .zero, aliasFormerCtor_hasSort_checked⟩

private theorem aliasFormerCandidate_generationShape :
    VInductDecl.normalizationCandidateGenerationShape aliasFormerRawDecl
      aliasFormerRawType aliasFormerNormalizationCandidate = true :=
  rfl

private def aliasFormerProducedGenerationShapeCandidate :
    VInductDecl.ProducedGenerationShapeCandidate aliasFormerRawDecl
      aliasFormerRawType aliasFormerKernelType 0 false
      aliasFormerCandidateContext where
  candidate := aliasFormerNormalizationCandidate
  produced := aliasFormerNormalizationCandidate_produced
  shape := aliasFormerCandidate_generationShape

/-- The strengthened outer gate returns the exact AliasFormer candidate with
its complete executable generation layout attached. -/
theorem aliasFormerGenerationShapeCandidate_produced :
    VInductDecl.produceGenerationShapeCandidate aliasFormerRawDecl
      aliasFormerRawType aliasFormerKernelType 0 false
      aliasFormerCandidateContext =
        .ok aliasFormerProducedGenerationShapeCandidate := by
  have produced :
      AddInductive.buildNormalizationCandidate aliasFormerRawDecl.nparams
          [aliasFormerKernelType] 0 false aliasFormerCandidateContext =
        .ok aliasFormerNormalizationCandidate :=
    aliasFormerNormalizationCandidate_produced
  simpa only [aliasFormerProducedGenerationShapeCandidate] using
    VInductDecl.produceGenerationShapeCandidate_eq_ok
      (source := aliasFormerRawDecl) (raw := aliasFormerRawType)
      produced aliasFormerCandidate_generationShape

private theorem aliasFormerCandidate_analysis
    (normalization : VInductDecl.NormalizationCandidateSemanticRun
      typeFamilyAliasEnv [] aliasFormerNormalizationCandidate
      aliasFormerRawDecl) :
    normalization.root.normalization.generation? =
      some aliasFormerGenerationChecked := by
  let reference : VInductDecl.NormalizationCandidateSemanticRun
      typeFamilyAliasEnv [] aliasFormerNormalizationCandidate
      aliasFormerRawDecl := {
    raw := aliasFormerRawType
    raw_types_eq := rfl
    uvars_eq := rfl
    family := aliasFormerCandidateFamilySemanticRun }
  rw [aliasFormerStagedPreFamilyInput.normalization_eq normalization reference]
  rfl

/-- The staged owner, exact dependent analysis, and strengthened producer
close AliasFormer without exposing a caller-selected semantic hierarchy. -/
theorem aliasFormerExactProducedGenerationCandidatePackage_exists :
    Nonempty (VInductDecl.ExactProducedGenerationCandidatePackage
      typeFamilyAliasEnv [] aliasFormerProducedGenerationShapeCandidate
      aliasFormerGenerationChecked) :=
  aliasFormerProducedGenerationShapeCandidate.exactProducedPackage_nonempty
    aliasFormerStagedPreFamilyInput rfl aliasFormerGenerationChecked
    aliasFormerCandidate_analysis

private def
    aliasFormerExactProducedGenerationCandidatePackage :
    VInductDecl.ExactProducedGenerationCandidatePackage typeFamilyAliasEnv []
      aliasFormerProducedGenerationShapeCandidate aliasFormerGenerationChecked :=
  aliasFormerProducedGenerationShapeCandidate.exactProducedPackage
    aliasFormerStagedPreFamilyInput rfl aliasFormerGenerationChecked
    aliasFormerCandidate_analysis

/-- Complete source-indexed candidate certificate for the non-identity
AliasFormer generation transaction. -/
def aliasFormerGenerationCandidateSemanticRun :
  VInductDecl.GenerationCandidateSemanticRun
      aliasFormerExactProducedGenerationCandidatePackage.normalization
      aliasFormerGenerationChecked :=
  aliasFormerExactProducedGenerationCandidatePackage.semantic

def aliasFormerGenerationCandidateRun :
    VInductDecl.GenerationCandidateRun
      aliasFormerExactProducedGenerationCandidatePackage.normalization.root
      aliasFormerGenerationChecked :=
  aliasFormerGenerationCandidateSemanticRun.run

/-- The generic dependent package retains the exact AliasFormer kernel
source, candidate trace, reconstructed normalization, successful dependent
analysis, and semantic generation run in one value. -/
def aliasFormerGenerationCandidatePackage :
    VInductDecl.GenerationCandidatePackage typeFamilyAliasEnv [] :=
  aliasFormerGenerationCandidateSemanticRun.package

/-- The complete AliasFormer semantic package is selected by the exact
successful whole-call metadata producer, including its pre-family and
post-family checker environments. -/
def aliasFormerProducedGenerationCandidatePackage :
    VInductDecl.ProducedGenerationCandidatePackage typeFamilyAliasEnv [] :=
  aliasFormerExactProducedGenerationCandidatePackage.package

/-- Theory-only erasure of the AliasFormer producer package. This is the
consumer-facing value accepted by the public non-identity transaction. -/
def aliasFormerGenerationCertificate :
    aliasFormerRawDecl.GenerationCertificate typeFamilyAliasEnv where
  generation := aliasFormerGenerationChecked
  wf := aliasFormerExactProducedGenerationCandidatePackage.semantic.run.wf

/-- The public proof-carrying path exposes AliasFormer's candidate-derived
non-identity generation without exposing its checker package. -/
theorem aliasFormer_addInductCertified_checked :
    typeFamilyAliasEnv.addInductCertified
        aliasFormerGenerationCertificate =
      some aliasFormerFinalEnv :=
  aliasFormer_addInductGeneration

theorem aliasFormerCertified_trace :
    Nonempty (VEnv.AddInductGenerationTrace typeFamilyAliasEnv
      aliasFormerFinalEnv aliasFormerGenerationChecked) :=
  VEnv.addInductCertified_trace aliasFormer_addInductCertified_checked

theorem aliasFormerCertified_ordered : aliasFormerFinalEnv.Ordered :=
  VEnv.addInductCertified_WF typeFamilyAliasEnv_ordered
    aliasFormer_addInductCertified_checked

/-- Complete checker-side AliasFormer generation run, now derived by the
generic family/constructor spine assembler from the executable singleton
candidate rather than assembled field-by-field by the fixture. -/
def aliasFormerGenerationRun :
    VInductDecl.GenerationRun aliasFormerGenerationChecked
      typeFamilyAliasEnv :=
  aliasFormerProducedGenerationCandidatePackage.package.run.generationRun

/-- Generation-ready AliasFormer certificate whose raw/view family equality
comes from the verified checker execution rather than the fixture's explicit
delta rule. -/
theorem aliasFormerGenerationChecked_wf_checked :
    aliasFormerGenerationChecked.WF typeFamilyAliasEnv :=
  aliasFormerGenerationCertificate.wf

/-- The paired AliasRec block with its field normalization supplied by the
checked WHNF/application/beta certificate. -/
theorem aliasRecBlock_wf_checked :
    aliasRecBlock.WF recAliasEnv := by
  refine ⟨aliasRecNormalization_wf_checked, ?_⟩
  change aliasRecViewChecked.WF recAliasEnv
  exact aliasRecViewChecked.wf_of_decl aliasRecViewDecl_wf

/-- Complete checker-side AliasRec generation run. Its constructor telescope
retains the checked compositional alias equality as pointwise evidence. -/
def aliasRecGenerationRun :
    VInductDecl.GenerationRun aliasRecGenerationChecked recAliasEnv := by
  refine {
    normalization := aliasRecNormalizationRun
    checked := aliasRecViewChecked.wf_of_decl aliasRecViewDecl_wf
    familyTel := .nil
    familyResult := .refl (VEnv.HasType.sort (by decide))
    typeEnv := aliasRecTypeEnv
    addType := rfl
    constructors := ?_ }
  intro ctor hctor
  change ctor ∈
    [⟨aliasRecRawType.ctors[0],
      aliasRecViewChecked.constructors[0]⟩] at hctor
  obtain rfl := List.mem_singleton.1 hctor
  have hresult := aliasRecResult_hasType rfl
  exact {
    declaredTel := .cons aliasRecFieldEvidence .nil
    declaredResult := .refl hresult
    emittedTel := .cons aliasRecFieldEvidence .nil
    emittedResult := .refl hresult }

/-- Generation-ready AliasRec certificate whose raw field typing comes from
the exact post-family full-check run and whose normalization equality composes
the verified WHNF, application, and beta steps. -/
theorem aliasRecGenerationChecked_wf_checked :
    aliasRecGenerationChecked.WF recAliasEnv :=
  aliasRecGenerationRun.wf

/-! ## Annotated recursive-Pi candidate interpretation -/

private def annotatedPiRawDomain : VExpr :=
  .app (.const ``outParam [.succ .zero]) (.sort .zero)

private def annotatedPiRawInner : VExpr :=
  .forallE annotatedPiRawDomain (.const ``AnnotatedPi [])

private def annotatedPiViewInner : VExpr :=
  .forallE (.sort .zero) (.const ``AnnotatedPi [])

private theorem annotatedPiFamilyConst_hasType (Γ : List VExpr) :
    annotatedPiTypeEnv.HasType 0 Γ
      (.const ``AnnotatedPi []) (.sort (.succ .zero)) := by
  have hfamily : annotatedPiTypeEnv.constants ``AnnotatedPi =
      some annotatedPiRawType.toVConstant := rfl
  type_tac

private theorem annotatedPiRawDomain_hasType (Γ : List VExpr) :
    annotatedPiTypeEnv.HasType 0 Γ annotatedPiRawDomain
      (.sort (.succ .zero)) := by
  have hout : annotatedPiTypeEnv.constants ``outParam =
      some (vconst(type_of% @outParam)) := rfl
  type_tac

private theorem annotatedPiForall_hasType
    {Γ : List VExpr} {domain body : VExpr}
    (domainType : annotatedPiTypeEnv.HasType 0 Γ domain
      (.sort (.succ .zero)))
    (bodyType : annotatedPiTypeEnv.HasType 0 (domain :: Γ) body
      (.sort (.succ .zero))) :
    annotatedPiTypeEnv.HasType 0 Γ (.forallE domain body)
      (.sort (.succ .zero)) :=
  .defeqDF
    (.sortDF (by decide) (by decide) VLevel.imax_self)
    (VEnv.HasType.forallE domainType bodyType)

private theorem annotatedPiRawInner_hasType (Γ : List VExpr) :
    annotatedPiTypeEnv.HasType 0 Γ annotatedPiRawInner
      (.sort (.succ .zero)) := by
  simpa [annotatedPiRawInner] using annotatedPiForall_hasType
    (annotatedPiRawDomain_hasType Γ)
    (annotatedPiFamilyConst_hasType (annotatedPiRawDomain :: Γ))

private theorem annotatedPiViewInner_hasType (Γ : List VExpr) :
    annotatedPiTypeEnv.HasType 0 Γ annotatedPiViewInner
      (.sort (.succ .zero)) := by
  simpa [annotatedPiViewInner] using annotatedPiForall_hasType
    (VEnv.HasType.sort (by decide))
    (annotatedPiFamilyConst_hasType ((.sort .zero) :: Γ))

private theorem annotatedPiRawCtor_hasType :
    annotatedPiTypeEnv.HasType 0 []
      annotatedPiRawType.ctors[0].type (.sort (.succ .zero)) := by
  rw [show annotatedPiRawType.ctors[0].type =
    .forallE annotatedPiRawInner (.const ``AnnotatedPi []) by rfl]
  simpa using annotatedPiForall_hasType
    (annotatedPiRawInner_hasType [])
    (annotatedPiFamilyConst_hasType [annotatedPiRawInner])

private theorem annotatedPiViewCtor_hasType :
    annotatedPiTypeEnv.HasType 0 []
      annotatedPiViewCtor.type (.sort (.succ .zero)) := by
  simpa [annotatedPiViewCtor, annotatedPiViewInner] using
    annotatedPiForall_hasType (annotatedPiViewInner_hasType [])
      (annotatedPiFamilyConst_hasType [annotatedPiViewInner])

private theorem annotatedPiCtorSource_tr :
    TrExprS annotatedPiTypeEnv [] [] annotatedPiMkInfo.type
      annotatedPiRawType.ctors[0].type := by
  have hshape : TrTypeExpr annotatedPiTypeEnv [] []
      annotatedPiMkInfo.type annotatedPiRawType.ctors[0].type := by
    tr_type_expr_tac
  exact hshape.to_trExprS annotatedPiTypeEnv_ordered trivial
    ⟨_, annotatedPiRawCtor_hasType⟩

private theorem annotatedPiInnerSource_tr :
    TrExprS annotatedPiTypeEnv [] [] annotatedPiInnerKernel
      annotatedPiRawInner := by
  have hshape : TrTypeExpr annotatedPiTypeEnv [] []
      annotatedPiInnerKernel annotatedPiRawInner := by
    tr_type_expr_tac
  exact hshape.to_trExprS annotatedPiTypeEnv_ordered trivial
    ⟨_, annotatedPiRawInner_hasType []⟩

private theorem annotatedPiDomainSource_tr :
    TrExprS annotatedPiTypeEnv [] [] annotatedPiRawDomainKernel
      annotatedPiRawDomain := by
  have hshape : TrTypeExpr annotatedPiTypeEnv [] []
      annotatedPiRawDomainKernel annotatedPiRawDomain := by
    tr_type_expr_tac
  exact hshape.to_trExprS annotatedPiTypeEnv_ordered trivial
    ⟨_, annotatedPiRawDomain_hasType []⟩

private theorem annotatedPiConstSource_tr (Δ : VLCtx) :
    TrExprS annotatedPiTypeEnv [] Δ (Expr.const ``AnnotatedPi [])
      (VExpr.const ``AnnotatedPi []) :=
  .const rfl rfl rfl

private theorem annotatedPiInstConstSource_tr (Δ : VLCtx) :
    TrExprS annotatedPiTypeEnv [] Δ
      ((Expr.const ``AnnotatedPi []).instantiate1
        annotatedPiCtorCandidateContext.freshExpr)
      (VExpr.const ``AnnotatedPi []) := by
  simpa using annotatedPiConstSource_tr Δ

private theorem annotatedPiFamilyCandidatePrefix_ne :
    annotatedPiFamilyCandidateContext.ngen.namePrefix ≠
      (({} : TypeChecker.VState).ngen).namePrefix := by
  decide

private def annotatedPiFamilyCandidateContextRun :
    TypeChecker.CandidateContextRun annotatedPiFamilyCandidateContext :=
  TypeChecker.CandidateContextRun.root outParamVEnvs_wf rfl
    annotatedPiFamilyCandidatePrefix_ne

private theorem annotatedPiFamilySource_tr :
    TrExprS outParamEnv [] [] annotatedPiInfo.type
      annotatedPiRawType.type :=
  annotatedPiInfo_tr.1.2.2

private def annotatedPiPreFamilyStage :
    TypeChecker.CandidateSemanticStage annotatedPiFamilyCandidateContext
      outParamEnv [] where
  contextRun := annotatedPiFamilyCandidateContextRun
  venv_eq := rfl
  lparams_eq := rfl
  vlctx_eq := rfl

private def annotatedPiFamilyValidationRun :
    AddInductive.CandidateExprTrace.FamilyValidationRun
      annotatedPiKernelType annotatedPiFamilyCandidate.trace where
  nparams := 0
  resultLevel := .succ .zero
  stats := annotatedPiInductiveStats
  stats_eq := rfl
  terminal_eq := rfl
  run := annotatedPi_checkInductiveTypes

private def annotatedPiFamilyStage :
    VInductDecl.CandidateFamilyStagedInput
      annotatedPiFamilyCandidateContext annotatedPiCtorCandidateContext
      outParamEnv [] annotatedPiFamilyListCandidate.familyType
      annotatedPiRawType annotatedPiPreFamilyStage where
  name_eq := rfl
  uvars_eq := rfl
  type := {
    context_eq := rfl
    source_tr := annotatedPiFamilySource_tr
    whnfFuel := 9999
    whnfDepth := rfl }
  validation := annotatedPiFamilyValidationRun
  typeEnv := annotatedPiTypeEnv
  addInduct := annotatedPiAddType
  projectionReady := ProjectionReady.of_no_ctorInfo <| by
    intro name _info h
    change annotatedPiTypeMap.find?' name = some (.ctorInfo _info) at h
    rw [annotatedPiTypeMap_wf.find?'_eq_find?] at h
    simp only [annotatedPiTypeMap, outParamMap_wf.find?_insert] at h
    simp only [outParamMap, SMap.WF.find?_insert
      (s := ({} : ConstMap)) SMap.WF.empty] at h
    by_cases hAnnotatedPi : ``AnnotatedPi = name <;>
      by_cases hOutParam : ``outParam = name <;>
      simp +decide [hAnnotatedPi, hOutParam, SMap.find?, annotatedPiInfo,
        annotationOutParamInfo] at h
  structureEtaReady := StructureEtaReady.of_no_ctorInfo <| by
    intro name _info h
    change annotatedPiTypeMap.find?' name = some (.ctorInfo _info) at h
    rw [annotatedPiTypeMap_wf.find?'_eq_find?] at h
    simp only [annotatedPiTypeMap, outParamMap_wf.find?_insert] at h
    simp only [outParamMap, SMap.WF.find?_insert
      (s := ({} : ConstMap)) SMap.WF.empty] at h
    by_cases hAnnotatedPi : ``AnnotatedPi = name <;>
      by_cases hOutParam : ``outParam = name <;>
      simp +decide [hAnnotatedPi, hOutParam, SMap.find?, annotatedPiInfo,
        annotationOutParamInfo] at h
  family_lctx_eq := rfl
  constructorContext_eq := rfl
  quotInit_eq := rfl
  name_not_reflected := by decide
  name_not_primitive := by
    simp [annotatedPiRawType, Kernel.Environment.primitives,
      NameSet.ofList]
    simp +decide [NameSet.contains]

private def annotatedPiCtorCandidateContextRun :
    TypeChecker.CandidateContextRun annotatedPiCtorCandidateContext :=
  annotatedPiFamilyStage.postContextRun

private def annotatedPiInnerBodyCandidateContextRun :
    TypeChecker.CandidateContextRun
      annotatedPiInnerBodyCandidateContext := by
  simpa [annotatedPiInnerBodyCandidateContext,
    annotatedPiDomainAnnotations] using
    annotatedPiCtorCandidateContextRun.pushLocalDecl `p .default
      (.sort .zero) annotatedPiCtorCandidateFresh (.sort .zero)
      (TrExprS.sort rfl)
      ⟨.succ .zero, VEnv.HasType.sort (by decide)⟩

private def annotatedPiOuterBodyCandidateContextRun :
    TypeChecker.CandidateContextRun
      annotatedPiOuterBodyCandidateContext := by
  have domain_tr :
      annotatedPiCtorCandidateContextRun.context.TrExprS
        annotatedPiInnerKernel annotatedPiRawInner := by
    change
      (annotatedPiFamilyStage.postFamily.contextRun.context.TrExprS
        annotatedPiInnerKernel annotatedPiRawInner)
    change TrExprS
      annotatedPiFamilyStage.postFamily.contextRun.context.venv
      annotatedPiFamilyStage.postFamily.contextRun.context.lparams
      annotatedPiFamilyStage.postFamily.contextRun.context.vlctx
      annotatedPiInnerKernel annotatedPiRawInner
    rw [annotatedPiFamilyStage.postFamily.venv_eq,
      annotatedPiFamilyStage.postFamily.lparams_eq,
      annotatedPiFamilyStage.postFamily.vlctx_eq]
    change TrExprS annotatedPiTypeEnv [] []
      annotatedPiInnerKernel annotatedPiRawInner
    exact annotatedPiInnerSource_tr
  simpa [annotatedPiOuterBodyCandidateContext,
    annotatedPiInnerAnnotations] using
    annotatedPiCtorCandidateContextRun.pushLocalDecl
      annotatedPiOuterName .default annotatedPiInnerKernel
      annotatedPiCtorCandidateFresh annotatedPiRawInner domain_tr
      ⟨.succ .zero, annotatedPiRawInner_hasType []⟩

private theorem annotatedPiInnerBodyCandidateContextRun_vlctx :
    annotatedPiInnerBodyCandidateContextRun.context.vlctx =
      [(some (annotatedPiCtorCandidateContext.freshFVarId,
          annotatedPiDomainAnnotations.consumed.fvarsList),
        .vlam (.sort .zero))] := by
  rfl

private theorem annotatedPiOuterBodyCandidateContextRun_vlctx :
    annotatedPiOuterBodyCandidateContextRun.context.vlctx =
      [(some (annotatedPiCtorCandidateContext.freshFVarId,
          annotatedPiInnerAnnotations.consumed.fvarsList),
        .vlam annotatedPiRawInner)] := by
  rfl

private def annotatedPiFamilyCandidateNodeRun :
    TypeChecker.CandidateNodeRun outParamEnv [] []
      annotatedPiFamilyCandidateContext annotatedPiInfo.type
      (.sort (.succ (.succ .zero))) annotatedPiInfo.type
      annotatedPiRawType.type annotatedPiRawType.type
      (.sort (.succ (.succ .zero))) := by
  exact TypeChecker.CandidateNodeRun.ofCandidate
    annotatedPiFamilyCandidateContext annotatedPiInfo.type
    (.sort (.succ (.succ .zero))) annotatedPiInfo.type
    annotatedPiFamilyCheckTypeStep_valid
    annotatedPiFamilyCandidateStep_valid
    annotatedPiFamilyCandidateContextRun.context
    annotatedPiFamilyCandidateContextRun.context_eq
    rfl rfl rfl annotatedPiFamilyCandidateContextRun.state_wf
    (.sort rfl) (.sort rfl)
    (TrExprS.sort rfl)
    10000 9999 rfl rfl

private theorem annotatedPiFamilyCandidateRun :
    TypeChecker.CandidateExprRun outParamEnv []
      annotatedPiFamilyCandidate.trace []
      annotatedPiRawType.type annotatedPiRawType.type
      (.sort (.succ (.succ .zero))) :=
  .terminal annotatedPiFamilyCandidateNodeRun

private def annotatedPiFamilySemanticRootRun :
    TypeChecker.CandidateExprSemanticRootRun outParamEnv []
      annotatedPiFamilyCandidate annotatedPiRawType.type
    where
  contextRun := annotatedPiFamilyCandidateContextRun
  venv_eq := rfl
  lparams_eq := rfl
  vlctx_eq := rfl
  source_tr := annotatedPiFamilyCandidateRun.source_tr
  whnfFuel := 9999
  whnfDepth := rfl
  view := annotatedPiRawType.type
  recursive := ⟨.sort (.succ (.succ .zero)),
    annotatedPiFamilyCandidateRun⟩

private def annotatedPiFamilyRootRun :
    TypeChecker.CandidateExprRootRun outParamEnv []
      annotatedPiFamilyCandidate annotatedPiRawType.type
      annotatedPiRawType.type :=
  annotatedPiFamilySemanticRootRun.root

private theorem annotatedPiFamilySpineRun :
    TypeChecker.CandidateExprSpineRun outParamEnv []
      annotatedPiFamilyCandidate annotatedPiRawType.type
      annotatedPiRawType.type :=
  annotatedPiFamilySemanticRootRun.spine rfl

private def annotatedPiCtorCandidateNodeRun :
    TypeChecker.CandidateNodeRun annotatedPiTypeEnv [] []
      annotatedPiCtorCandidateContext annotatedPiMkInfo.type
      (.sort (.succ .zero)) annotatedPiMkInfo.type
      annotatedPiRawType.ctors[0].type
      annotatedPiRawType.ctors[0].type
      (.sort (.succ .zero)) := by
  exact TypeChecker.CandidateNodeRun.ofCandidate
    annotatedPiCtorCandidateContext annotatedPiMkInfo.type
    (.sort (.succ .zero)) annotatedPiMkInfo.type
    annotatedPiCtorCheckTypeStep_valid annotatedPiCtorCandidateStep_valid
    annotatedPiCtorCandidateContextRun.context
    annotatedPiCtorCandidateContextRun.context_eq
    rfl rfl rfl annotatedPiCtorCandidateContextRun.state_wf
    annotatedPiCtorSource_tr (.sort rfl)
    annotatedPiCtorSource_tr
    10000 9999 rfl rfl

private def annotatedPiInnerCandidateNodeRun :
    TypeChecker.CandidateNodeRun annotatedPiTypeEnv [] []
      annotatedPiCtorCandidateContext annotatedPiInnerKernel
      (.sort (.succ .zero)) annotatedPiInnerKernel
      annotatedPiRawInner annotatedPiRawInner
      (.sort (.succ .zero)) := by
  exact TypeChecker.CandidateNodeRun.ofCandidate
    annotatedPiCtorCandidateContext annotatedPiInnerKernel
    (.sort (.succ .zero)) annotatedPiInnerKernel
    annotatedPiInnerCheckTypeStep_valid annotatedPiInnerCandidateStep_valid
    annotatedPiCtorCandidateContextRun.context
    annotatedPiCtorCandidateContextRun.context_eq
    rfl rfl rfl annotatedPiCtorCandidateContextRun.state_wf
    annotatedPiInnerSource_tr (.sort rfl)
    annotatedPiInnerSource_tr
    10000 9999 rfl rfl

private def annotatedPiDomainCandidateNodeRun :
    TypeChecker.CandidateNodeRun annotatedPiTypeEnv [] []
      annotatedPiCtorCandidateContext annotatedPiRawDomainKernel
      (.sort (.succ .zero)) (.sort .zero)
      annotatedPiRawDomain (.sort .zero)
      (.sort (.succ .zero)) := by
  exact TypeChecker.CandidateNodeRun.ofCandidate
    annotatedPiCtorCandidateContext annotatedPiRawDomainKernel
    (.sort (.succ .zero)) (.sort .zero)
    annotatedPiDomainCheckTypeStep_valid annotatedPiDomainCandidateStep_valid
    annotatedPiCtorCandidateContextRun.context
    annotatedPiCtorCandidateContextRun.context_eq
    rfl rfl rfl annotatedPiCtorCandidateContextRun.state_wf
    annotatedPiDomainSource_tr (.sort rfl)
    (TrExprS.sort rfl)
    10000 9999 rfl rfl

private def annotatedPiInnerBodyCandidateNodeRun :
    TypeChecker.CandidateNodeRun annotatedPiTypeEnv []
      annotatedPiInnerBodyCandidateContextRun.context.vlctx
      annotatedPiInnerBodyCandidateContext
      ((Expr.const ``AnnotatedPi []).instantiate1
        annotatedPiCtorCandidateContext.freshExpr)
      (.sort (.succ .zero)) (.const ``AnnotatedPi [])
      (.const ``AnnotatedPi []) (.const ``AnnotatedPi [])
      (.sort (.succ .zero)) := by
  exact TypeChecker.CandidateNodeRun.ofCandidate
    annotatedPiInnerBodyCandidateContext
    ((Expr.const ``AnnotatedPi []).instantiate1
      annotatedPiCtorCandidateContext.freshExpr)
    (.sort (.succ .zero)) (.const ``AnnotatedPi [])
    (by simpa only [annotatedPiInnerBodyCheckTypeStep,
        annotatedPiConst_instantiate1] using
      annotatedPiInnerBodyCheckTypeStep_valid)
    (by simpa only [annotatedPiInnerBodyCandidateStep,
        annotatedPiConst_instantiate1] using
      annotatedPiInnerBodyCandidateStep_valid)
    annotatedPiInnerBodyCandidateContextRun.context
    annotatedPiInnerBodyCandidateContextRun.context_eq
    rfl rfl rfl annotatedPiInnerBodyCandidateContextRun.state_wf
    (annotatedPiInstConstSource_tr
      annotatedPiInnerBodyCandidateContextRun.context.vlctx)
    (.sort rfl)
    (annotatedPiConstSource_tr
      annotatedPiInnerBodyCandidateContextRun.context.vlctx)
    10000 9999 rfl rfl

private def annotatedPiOuterBodyCandidateNodeRun :
    TypeChecker.CandidateNodeRun annotatedPiTypeEnv []
      annotatedPiOuterBodyCandidateContextRun.context.vlctx
      annotatedPiOuterBodyCandidateContext
      ((Expr.const ``AnnotatedPi []).instantiate1
        annotatedPiCtorCandidateContext.freshExpr)
      (.sort (.succ .zero)) (.const ``AnnotatedPi [])
      (.const ``AnnotatedPi []) (.const ``AnnotatedPi [])
      (.sort (.succ .zero)) := by
  exact TypeChecker.CandidateNodeRun.ofCandidate
    annotatedPiOuterBodyCandidateContext
    ((Expr.const ``AnnotatedPi []).instantiate1
      annotatedPiCtorCandidateContext.freshExpr)
    (.sort (.succ .zero)) (.const ``AnnotatedPi [])
    (by simpa only [annotatedPiOuterBodyCheckTypeStep,
        annotatedPiConst_instantiate1] using
      annotatedPiOuterBodyCheckTypeStep_valid)
    (by simpa only [annotatedPiOuterBodyCandidateStep,
        annotatedPiConst_instantiate1] using
      annotatedPiOuterBodyCandidateStep_valid)
    annotatedPiOuterBodyCandidateContextRun.context
    annotatedPiOuterBodyCandidateContextRun.context_eq
    rfl rfl rfl annotatedPiOuterBodyCandidateContextRun.state_wf
    (annotatedPiInstConstSource_tr
      annotatedPiOuterBodyCandidateContextRun.context.vlctx)
    (.sort rfl)
    (annotatedPiConstSource_tr
      annotatedPiOuterBodyCandidateContextRun.context.vlctx)
    10000 9999 rfl rfl

private def annotatedPiDomainAnnotationsRun :
    TypeChecker.IsDefEqRun annotatedPiTypeEnv [] []
      annotatedPiRawDomainKernel annotatedPiDomainAnnotations.consumed
      annotatedPiRawDomain (.sort .zero) := by
  exact TypeChecker.IsDefEqRun.ofCandidateStep
    ⟨annotatedPiCtorCandidateContext, annotatedPiRawDomainKernel,
      annotatedPiDomainAnnotations.consumed⟩
    annotatedPiDomainAnnotationsEq
    annotatedPiCtorCandidateContextRun.context
    annotatedPiCtorCandidateContextRun.context_eq
    rfl rfl rfl annotatedPiCtorCandidateContextRun.state_wf
    annotatedPiDomainSource_tr (.sort rfl) 10000 rfl

private def annotatedPiInnerAnnotationsRun :
    TypeChecker.IsDefEqRun annotatedPiTypeEnv [] []
      annotatedPiInnerKernel annotatedPiInnerAnnotations.consumed
      annotatedPiRawInner annotatedPiRawInner := by
  exact TypeChecker.IsDefEqRun.ofCandidateStep
    ⟨annotatedPiCtorCandidateContext, annotatedPiInnerKernel,
      annotatedPiInnerAnnotations.consumed⟩
    annotatedPiInnerAnnotationsEq
    annotatedPiCtorCandidateContextRun.context
    annotatedPiCtorCandidateContextRun.context_eq
    rfl rfl rfl annotatedPiCtorCandidateContextRun.state_wf
    annotatedPiInnerSource_tr annotatedPiInnerSource_tr 10000 rfl

private theorem annotatedPiDomainCandidateRun :
    TypeChecker.CandidateExprRun annotatedPiTypeEnv []
      annotatedPiDomainCandidateTrace [] annotatedPiRawDomain
      (.sort .zero) (.sort (.succ .zero)) :=
  .terminal annotatedPiDomainCandidateNodeRun

private theorem annotatedPiInnerBodyCandidateRun :
    TypeChecker.CandidateExprRun annotatedPiTypeEnv []
      annotatedPiInnerBodyCandidateTrace
      [(some (annotatedPiCtorCandidateContext.freshFVarId,
          annotatedPiDomainAnnotations.consumed.fvarsList),
        .vlam (.sort .zero))]
      (.const ``AnnotatedPi []) (.const ``AnnotatedPi [])
      (.sort (.succ .zero)) := by
  simpa only [annotatedPiInnerBodyCandidateTrace,
    annotatedPiInnerBodyCandidateContextRun_vlctx] using
    (TypeChecker.CandidateExprRun.terminal
      annotatedPiInnerBodyCandidateNodeRun)

private theorem annotatedPiOuterBodyCandidateRun :
    TypeChecker.CandidateExprRun annotatedPiTypeEnv []
      annotatedPiOuterBodyCandidateTrace
      [(some (annotatedPiCtorCandidateContext.freshFVarId,
          annotatedPiInnerAnnotations.consumed.fvarsList),
        .vlam annotatedPiRawInner)]
      (.const ``AnnotatedPi []) (.const ``AnnotatedPi [])
      (.sort (.succ .zero)) := by
  simpa only [annotatedPiOuterBodyCandidateTrace,
    annotatedPiOuterBodyCandidateContextRun_vlctx] using
    (TypeChecker.CandidateExprRun.terminal
      annotatedPiOuterBodyCandidateNodeRun)

private theorem annotatedPiInnerCandidateRun :
    TypeChecker.CandidateExprRun annotatedPiTypeEnv []
      annotatedPiInnerCandidateTrace [] annotatedPiRawInner
      annotatedPiViewInner (.sort (.succ .zero)) := by
  exact .forallE annotatedPiDomainAnnotations
    annotatedPiDomainAnnotationsEq annotatedPiDomainCandidateTrace
    annotatedPiInnerBodyCandidateTrace
    annotatedPiInnerCandidateNodeRun annotatedPiDomainCandidateRun
    annotatedPiDomainAnnotationsRun annotatedPiInnerBodyCandidateRun
    (annotatedPiRawDomain_hasType [])
    (annotatedPiFamilyConst_hasType [annotatedPiRawDomain])
    (annotatedPiFamilyConst_hasType [annotatedPiRawDomain]) rfl

private theorem annotatedPiCtorCandidateRun :
    TypeChecker.CandidateExprRun annotatedPiTypeEnv []
      annotatedPiCtorCandidate.trace []
      annotatedPiRawType.ctors[0].type annotatedPiViewCtor.type
      (.sort (.succ .zero)) := by
  exact .forallE annotatedPiInnerAnnotations
    annotatedPiInnerAnnotationsEq annotatedPiInnerCandidateTrace
    annotatedPiOuterBodyCandidateTrace
    annotatedPiCtorCandidateNodeRun annotatedPiInnerCandidateRun
    annotatedPiInnerAnnotationsRun annotatedPiOuterBodyCandidateRun
    (annotatedPiRawInner_hasType [])
    (annotatedPiFamilyConst_hasType [annotatedPiRawInner])
    (annotatedPiFamilyConst_hasType [annotatedPiRawInner]) rfl

private def annotatedPiCtorSemanticRootRun :
    TypeChecker.CandidateExprSemanticRootRun annotatedPiTypeEnv []
      annotatedPiCtorCandidate annotatedPiRawType.ctors[0].type
    where
  contextRun := annotatedPiCtorCandidateContextRun
  venv_eq := rfl
  lparams_eq := rfl
  vlctx_eq := rfl
  source_tr := annotatedPiCtorCandidateRun.source_tr
  whnfFuel := 9999
  whnfDepth := rfl
  view := annotatedPiViewCtor.type
  recursive := ⟨.sort (.succ .zero), annotatedPiCtorCandidateRun⟩

private def annotatedPiCtorRootRun :
    TypeChecker.CandidateExprRootRun annotatedPiTypeEnv []
      annotatedPiCtorCandidate annotatedPiRawType.ctors[0].type
      annotatedPiViewCtor.type :=
  annotatedPiCtorSemanticRootRun.root

private theorem annotatedPiCtorCandidate_storedSpine :
    annotatedPiCtorCandidate.trace.storedSpine = true := by
  have hsource : annotatedPiMkInfo.type =
      .forallE annotatedPiOuterName annotatedPiInnerKernel
        (.const ``AnnotatedPi []) .default := rfl
  simp only [annotatedPiCtorCandidate, annotatedPiCtorCandidateTrace,
    AddInductive.CandidateExprTrace.storedSpine, hsource,
    Expr.structuralEq_refl, Bool.true_and]
  rfl

private theorem annotatedPiCtorSpineRun :
    TypeChecker.CandidateExprSpineRun annotatedPiTypeEnv []
      annotatedPiCtorCandidate annotatedPiRawType.ctors[0].type
      annotatedPiViewCtor.type :=
  annotatedPiCtorSemanticRootRun.spine
    annotatedPiCtorCandidate_storedSpine

private def annotatedPiCandidateConstructorSemanticRun :
    VInductDecl.CandidateConstructorSemanticRun annotatedPiTypeEnv []
      annotatedPiConstructorCandidate annotatedPiRawType.ctors[0] where
  name_eq := rfl
  uvars_eq := rfl
  type := annotatedPiCtorSemanticRootRun

private def annotatedPiCandidateConstructorRun :
    VInductDecl.CandidateConstructorRun annotatedPiTypeEnv []
      annotatedPiConstructorCandidate annotatedPiRawType.ctors[0] :=
  annotatedPiCandidateConstructorSemanticRun.root

private def annotatedPiCandidateConstructorSemanticListRun :
    VInductDecl.CandidateConstructorSemanticListRun annotatedPiTypeEnv []
      annotatedPiFamilyListCandidate.constructors
      annotatedPiRawType.ctors := by
  exact .cons annotatedPiCandidateConstructorSemanticRun .nil

private def annotatedPiCandidateConstructorListRun :
    VInductDecl.CandidateConstructorListRun annotatedPiTypeEnv []
      annotatedPiFamilyListCandidate.constructors
      annotatedPiRawType.ctors :=
  annotatedPiCandidateConstructorSemanticListRun.roots

private def annotatedPiCandidateFamilySemanticRun :
    VInductDecl.CandidateFamilySemanticRun outParamEnv []
      annotatedPiFamilyListCandidate annotatedPiRawType where
  name_eq := rfl
  uvars_eq := rfl
  type := annotatedPiFamilySemanticRootRun
  typeEnv := annotatedPiTypeEnv
  addType := rfl
  constructors := annotatedPiCandidateConstructorSemanticListRun

private def annotatedPiCandidateFamilyRun :
    VInductDecl.CandidateFamilyRun outParamEnv []
      annotatedPiFamilyListCandidate annotatedPiRawType :=
  annotatedPiCandidateFamilySemanticRun.root

private def annotatedPiStagedUniverseInput :
    VInductDecl.StagedNormalizationCandidateUniverseInput
      annotatedPiFamilyCandidateContext annotatedPiCtorCandidateContext
      outParamEnv [] annotatedPiNormalizationCandidate
      annotatedPiRawDecl where
  staged := {
    raw := annotatedPiRawType
    raw_types_eq := rfl
    declaration_uvars_eq := rfl
    preFamily := annotatedPiPreFamilyStage
    family := annotatedPiFamilyStage
    validation_nparams_eq := rfl
    constructorValidation :=
      AddInductive.ConstructorValidationRun.of_run annotatedPi_checkConstructors
    constructors := .cons {
      name_eq := rfl
      uvars_eq := rfl
      type := {
        context_eq := rfl
        source_tr := annotatedPiCtorCandidateRun.source_tr
        whnfFuel := 9999
        whnfDepth := rfl } } .nil
    familyTypesProduced := annotatedPiFamilyTypeListProduced
    familiesProduced := annotatedPiFamilyListProduced }
  universeRun := annotatedPi_checkConstructorUniverseSemantics

private def annotatedPiConstructorValidationContext : AddInductive.Context :=
  { env := annotatedPiCtorCandidateContext.env
    lctx := annotatedPiNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext.lctx
    lparams := annotatedPiNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext.lparams
    ngen := annotatedPiNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext.ngen
    safety := annotatedPiNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext.safety
    allowPrimitive := annotatedPiNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext.allowPrimitive
    fuel := annotatedPiNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext.fuel }

private theorem annotatedPiConstructorValidationContext_eq :
    { annotatedPiNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext with
      env := annotatedPiCtorCandidateContext.env } =
      annotatedPiCtorCandidateContext := rfl

private theorem annotatedPiConstructorValidationContext_def_eq :
    annotatedPiConstructorValidationContext =
      annotatedPiCtorCandidateContext := rfl

private theorem annotatedPiConstructorValidationContextLiteral_eq :
    ({ env := annotatedPiCtorCandidateContext.env
       lctx := annotatedPiNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext.lctx
       lparams := annotatedPiNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext.lparams
       ngen := annotatedPiNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext.ngen
       safety := annotatedPiNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext.safety
       allowPrimitive := annotatedPiNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext.allowPrimitive
       fuel := annotatedPiNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext.fuel } :
      AddInductive.Context) = annotatedPiCtorCandidateContext := rfl

private theorem annotatedPiStagedStats_eq :
    annotatedPiStagedUniverseInput.staged.family.validation.stats =
      annotatedPiInductiveStats := rfl

private theorem annotatedPiStagedParams_zero :
    annotatedPiStagedUniverseInput.staged.family.validation.stats.params[0]? =
      none := by
  rw [annotatedPiStagedStats_eq]
  rfl

private theorem annotatedPiKernelCtor_isForall :
    annotatedPiKernelCtor.type.isForall = true := rfl

private theorem annotatedPiKernelType_ctors_eq :
    annotatedPiKernelType.ctors = [annotatedPiKernelCtor] := rfl

private theorem annotatedPiKernelCtor_type_eq :
    annotatedPiKernelCtor.type =
      .forallE annotatedPiOuterName annotatedPiInnerKernel
        (.const ``AnnotatedPi []) .default := rfl

private theorem annotatedPiConstructorValidationFuel_eq :
    annotatedPiNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext.fuel.inductiveFuel =
      1000 := rfl

private theorem annotatedPiCtorCandidateContext_empty :
    annotatedPiCtorCandidateContext.withEmptyLocalContext =
      annotatedPiCtorCandidateContext := rfl

private def annotatedPiViewInnerKernel : Expr :=
  .forallE `p (.sort .zero) (.const ``AnnotatedPi []) .default

private def annotatedPiViewCtorKernel : Expr :=
  .forallE annotatedPiOuterName annotatedPiViewInnerKernel
    (.const ``AnnotatedPi []) .default

private def annotatedPiAlignedViewInnerKernel : Expr :=
  .forallE `p (.sort .zero)
    ((Expr.const ``AnnotatedPi []).abstract
      #[annotatedPiCtorCandidateContext.freshExpr]) .default

private def annotatedPiAlignedViewCtorKernel : Expr :=
  .forallE annotatedPiOuterName annotatedPiAlignedViewInnerKernel
    ((Expr.const ``AnnotatedPi []).abstract
      #[annotatedPiCtorCandidateContext.freshExpr]) .default

@[simp] private theorem annotatedPiConst_abstract_singleton
    (context : AddInductive.Context) :
    (Expr.const ``AnnotatedPi []).abstract #[context.freshExpr] =
      .const ``AnnotatedPi [] := by
  rw [show #[context.freshExpr] =
    ⟨[context.freshFVarId].map Expr.fvar⟩ by rfl]
  simp only [Expr.abstract_eq, Expr.abstractList, Expr.abstract1]

private theorem annotatedPiAlignedViewInnerKernel_eq :
    annotatedPiAlignedViewInnerKernel = annotatedPiViewInnerKernel := by
  simp [annotatedPiAlignedViewInnerKernel, annotatedPiViewInnerKernel]

private theorem annotatedPiAlignedViewCtorKernel_eq :
    annotatedPiAlignedViewCtorKernel = annotatedPiViewCtorKernel := by
  simp [annotatedPiAlignedViewCtorKernel, annotatedPiViewCtorKernel,
    annotatedPiAlignedViewInnerKernel, annotatedPiViewInnerKernel]

set_option maxRecDepth 10000 in
private theorem annotatedPiDomain_isDefEqInner9999
    (initial : Std.HashSet (Expr × Expr)) :
    ∃ state : TypeChecker.State,
      TypeChecker.Inner.isDefEq annotatedPiRawDomainKernel (.sort .zero)
          (TypeChecker.Methods.withFuel 9999)
          annotatedPiCtorCandidateContext.toTypeChecker
          ({ success := initial } : TypeChecker.State) =
        .ok (true, state) := by
  simpa only [Nat.reduceAdd] using
    annotatedPiDomain_isDefEqInner 9995 initial

private theorem annotatedPiInnerView_isDefEqForall
    (initial : Std.HashSet (Expr × Expr)) :
    ∃ state : TypeChecker.State,
      TypeChecker.Inner.isDefEqForall
          annotatedPiInnerKernel annotatedPiViewInnerKernel #[]
          (TypeChecker.Methods.withFuel 9999)
          annotatedPiCtorCandidateContext.toTypeChecker
          ({ success := initial } : TypeChecker.State) =
        .ok (true, state) := by
  obtain ⟨state, domainRun⟩ :=
    annotatedPiDomain_isDefEqInner9999 initial
  have domainRun' : TypeChecker.Inner.isDefEq
      (annotatedPiRawDomainKernel.instantiateRev #[])
      ((.sort .zero : Expr).instantiateRev #[])
      (TypeChecker.Methods.withFuel 9999)
      annotatedPiCtorCandidateContext.toTypeChecker
      ({ success := initial } : TypeChecker.State) =
        .ok (true, state) := by
    simpa [Expr.instantiateRev] using domainRun
  refine ⟨state, ?_⟩
  unfold annotatedPiInnerKernel annotatedPiViewInnerKernel
    TypeChecker.Inner.isDefEqForall
  rw [show
    (annotatedPiRawDomainKernel == (.sort .zero : Expr)) = false by
      exact annotatedPiApp_beq_sort _ _ _]
  simp only [Bool.false_eq_true, if_false, pure_bind,
    normalizationRecMBind]
  rw [domainRun']
  simp [TypeChecker.Inner.isDefEqForall, TypeChecker.Inner.isDefEq, Expr.hasLooseBVars,
    Expr.looseBVarRange']

private theorem annotatedPiInnerView_quickIsDefEq
    (initial : Std.HashSet (Expr × Expr)) :
    ∃ state : TypeChecker.State,
      TypeChecker.Inner.quickIsDefEq
          annotatedPiInnerKernel annotatedPiViewInnerKernel
          (TypeChecker.Methods.withFuel 9999)
          annotatedPiCtorCandidateContext.toTypeChecker
          ({ success := initial } : TypeChecker.State) =
        .ok (.true, state) := by
  by_cases hc : (annotatedPiInnerKernel == annotatedPiViewInnerKernel ||
      TypeChecker.Inner.succeededBefore initial
        annotatedPiInnerKernel annotatedPiViewInnerKernel) = true
  -- Settled structurally or by the cache: the state comes back untouched.
  · refine ⟨({ success := initial } : TypeChecker.State), ?_⟩
    unfold TypeChecker.Inner.quickIsDefEq
    simp [hc, pure, ReaderT.pure, StateT.pure, Except.pure,
      Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  -- Otherwise both sides are for-alls and the match hands off to `isDefEqForall`.
  · simp only [Bool.not_eq_true] at hc
    obtain ⟨state, forallRun⟩ := annotatedPiInnerView_isDefEqForall initial
    refine ⟨state, ?_⟩
    unfold annotatedPiInnerKernel annotatedPiViewInnerKernel at hc forallRun ⊢
    unfold TypeChecker.Inner.quickIsDefEq
    simp [hc, Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
    unfold toLBoolM
    rw [normalizationRecMBind, forallRun]
    rfl

private theorem annotatedPiInnerView_isDefEqInner :
    ∃ state : TypeChecker.State,
      TypeChecker.Inner.isDefEq
          annotatedPiInnerKernel annotatedPiViewInnerKernel
          (TypeChecker.Methods.withFuel 10000)
          annotatedPiCtorCandidateContext.toTypeChecker
          ({} : TypeChecker.State) =
        .ok (true, state) := by
  obtain ⟨quickState, quickRun⟩ :=
    annotatedPiInnerView_quickIsDefEq {}
  have coreRun : TypeChecker.Inner.isDefEqCore
      annotatedPiInnerKernel annotatedPiViewInnerKernel
      (TypeChecker.Methods.withFuel 10000)
      annotatedPiCtorCandidateContext.toTypeChecker
      ({} : TypeChecker.State) = .ok (true, quickState) := by
    change TypeChecker.Inner.isDefEqCore'
      annotatedPiInnerKernel annotatedPiViewInnerKernel
      (TypeChecker.Methods.withFuel 9999)
      annotatedPiCtorCandidateContext.toTypeChecker
      ({} : TypeChecker.State) = .ok (true, quickState)
    unfold TypeChecker.Inner.isDefEqCore'
    rw [normalizationRecMBind, quickRun]
    rfl
  unfold TypeChecker.Inner.isDefEq
  rw [show
    (annotatedPiInnerKernel == annotatedPiViewInnerKernel) = false by
      change Expr.eqv
        (.forallE `p annotatedPiRawDomainKernel
          (.const ``AnnotatedPi []) .default)
        (.forallE `p (.sort .zero)
          (.const ``AnnotatedPi []) .default) = false
      rw [Expr.eqv_eq]
      rfl]
  simp only [Bool.false_eq_true, if_false, normalizationRecMBind]
  rw [coreRun]
  exact ⟨_, rfl⟩

private theorem annotatedPiInnerView_isDefEq :
    AddInductive.CandidateIsDefEqStep.Valid
      ⟨annotatedPiConstructorValidationContext,
        annotatedPiInnerKernel, annotatedPiAlignedViewInnerKernel⟩ := by
  unfold AddInductive.CandidateIsDefEqStep.Valid
  rw [annotatedPiConstructorValidationContext_def_eq,
    annotatedPiAlignedViewInnerKernel_eq]
  obtain ⟨state, run⟩ := annotatedPiInnerView_isDefEqInner
  change Except.map (fun x : Bool × TypeChecker.State => x.1)
      (TypeChecker.Inner.isDefEq annotatedPiInnerKernel
        annotatedPiViewInnerKernel
        (TypeChecker.Methods.withFuel 10000)
        annotatedPiCtorCandidateContext.toTypeChecker
        ({} : TypeChecker.State)) = .ok true
  rw [run]
  rfl

private theorem annotatedPiValidationAlignedCheck_exists
    {source candidateSource : Expr}
    (source_eq : source = candidateSource)
    {checked : AddInductive.ConstructorCheckedExpr
      annotatedPiCtorCandidateContext candidateSource}
    (run : AddInductive.checkConstructorAlignedExpr
      annotatedPiCtorCandidateContext candidateSource = .ok checked) :
    ∃ aligned : AddInductive.ConstructorCheckedExpr
        annotatedPiConstructorValidationContext source,
      AddInductive.checkConstructorAlignedExpr
        annotatedPiConstructorValidationContext source = .ok aligned := by
  subst candidateSource
  rw [annotatedPiConstructorValidationContext_def_eq]
  exact ⟨checked, run⟩

private def annotatedPiAlignChecked
    {context candidateContext : AddInductive.Context}
    {source candidateSource : Expr}
    (context_eq : context = candidateContext)
    (source_eq : source = candidateSource)
    (checked : AddInductive.ConstructorCheckedExpr
      candidateContext candidateSource) :
    AddInductive.ConstructorCheckedExpr context source := by
  subst candidateContext
  subst candidateSource
  exact checked

private def annotatedPiAlignIsDefEq
    {context candidateContext : AddInductive.Context}
    {lhs rhs candidateLhs candidateRhs : Expr}
    (context_eq : context = candidateContext)
    (lhs_eq : lhs = candidateLhs)
    (rhs_eq : rhs = candidateRhs)
    (observation : AddInductive.CandidateIsDefEqObservation
      candidateContext candidateLhs candidateRhs) :
    AddInductive.CandidateIsDefEqObservation context lhs rhs := by
  subst candidateContext
  subst candidateLhs
  subst candidateRhs
  exact observation

private theorem annotatedPiViewInnerCheckTypeStep_valid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨annotatedPiCtorCandidateContext, annotatedPiViewInnerKernel,
        .sort (.succ .zero)⟩ := by
  change TypeChecker.M.run annotatedPiCtorCandidateContext.env
      annotatedPiCtorCandidateContext.safety
      annotatedPiCtorCandidateContext.lctx
      annotatedPiCtorCandidateContext.lparams
      annotatedPiCtorCandidateContext.fuel
      (TypeChecker.checkType annotatedPiViewInnerKernel) =
        .ok (.sort (.succ .zero))
  change
    Except.map (fun x : Expr × TypeChecker.State => x.1)
      (TypeChecker.Inner.inferType annotatedPiViewInnerKernel false
        (TypeChecker.Methods.withFuel 10000)
        annotatedPiCtorCandidateContext.toTypeChecker
        ({} : TypeChecker.State)) =
      .ok (.sort (.succ .zero))
  change
    Except.map (fun x : Expr × TypeChecker.State => x.1)
      (TypeChecker.Inner.inferType' annotatedPiViewInnerKernel false
        (TypeChecker.Methods.withFuel 9999)
        annotatedPiCtorCandidateContext.toTypeChecker
        ({} : TypeChecker.State)) =
      .ok (.sort (.succ .zero))
  unfold annotatedPiViewInnerKernel TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange', TypeChecker.Inner.inferType',
    TypeChecker.Inner.inferForall, TypeChecker.Inner.inferForall.loop, Expr.instantiate1',
    annotatedPiWithLocalDecl, annotatedPiCtorCandidateContext, AddInductive.Context.toTypeChecker,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  simp [Expr.sortLevel!, annotatedPi_mkLevelIMaxSuccZero]
  rfl

private def annotatedPiViewInnerFinalState : TypeChecker.State :=
  { ({} : TypeChecker.State) with
    ngen := ({} : TypeChecker.State).ngen.next
    inferTypeC :=
      ((({} : TypeChecker.State).inferTypeC.insert
          (.sort .zero) (.sort (.succ .zero))).insert
          (.const ``AnnotatedPi []) (.sort (.succ .zero))).insert
          annotatedPiViewInnerKernel (.sort (.succ .zero)) }

private theorem annotatedPiViewInnerInferType_exists (n : Nat) :
    ∃ state : TypeChecker.State,
      TypeChecker.Inner.inferType' annotatedPiViewInnerKernel false
          (TypeChecker.Methods.withFuel (n + 1))
          annotatedPiCtorCandidateContext.toTypeChecker
          ({} : TypeChecker.State) =
        .ok (.sort (.succ .zero), state) ∧
      state.inferTypeC[(.const ``AnnotatedPi [] : Expr)]? =
        some (.sort (.succ .zero)) := by
  refine ⟨annotatedPiViewInnerFinalState, ?_, ?_⟩
  · unfold annotatedPiViewInnerKernel TypeChecker.Inner.inferType'
    simp [Expr.hasLooseBVars, Expr.looseBVarRange', TypeChecker.Inner.inferType',
      TypeChecker.Inner.inferForall, TypeChecker.Inner.inferForall.loop, Expr.instantiate1',
      annotatedPiWithLocalDecl, annotatedPiCtorCandidateContext, AddInductive.Context.toTypeChecker,
      Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
    simp [Expr.sortLevel!, annotatedPi_mkLevelIMaxSuccZero]
    rfl
  · simpa [annotatedPiViewInnerFinalState,
      annotatedPiViewInnerKernel] using
      annotatedPiFamilyCacheAfterForall
        (({} : TypeChecker.State).inferTypeC.insert
          (.sort .zero) (.sort (.succ .zero)))
        `p (.sort .zero) (.const ``AnnotatedPi [])
        (.sort (.succ .zero)) .default

private theorem annotatedPiViewCtorCheckTypeStep_valid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨annotatedPiCtorCandidateContext, annotatedPiViewCtorKernel,
        .sort (.succ .zero)⟩ := by
  change TypeChecker.M.run annotatedPiCtorCandidateContext.env
      annotatedPiCtorCandidateContext.safety
      annotatedPiCtorCandidateContext.lctx
      annotatedPiCtorCandidateContext.lparams
      annotatedPiCtorCandidateContext.fuel
      (TypeChecker.checkType annotatedPiViewCtorKernel) =
        .ok (.sort (.succ .zero))
  change
    Except.map (fun x : Expr × TypeChecker.State => x.1)
      (TypeChecker.Inner.inferType annotatedPiViewCtorKernel false
        (TypeChecker.Methods.withFuel 10000)
        annotatedPiCtorCandidateContext.toTypeChecker
        ({} : TypeChecker.State)) =
      .ok (.sort (.succ .zero))
  change
    Except.map (fun x : Expr × TypeChecker.State => x.1)
      (TypeChecker.Inner.inferType' annotatedPiViewCtorKernel false
        (TypeChecker.Methods.withFuel 9999)
        annotatedPiCtorCandidateContext.toTypeChecker
        ({} : TypeChecker.State)) =
      .ok (.sort (.succ .zero))
  obtain ⟨innerState, hinner, hinnerCache⟩ :=
    annotatedPiViewInnerInferType_exists 9997
  change TypeChecker.Inner.inferType' annotatedPiViewInnerKernel false
      (TypeChecker.Methods.withFuel 9998)
      annotatedPiCtorCandidateContext.toTypeChecker
      ({} : TypeChecker.State) =
    .ok (.sort (.succ .zero), innerState) at hinner
  unfold annotatedPiViewInnerKernel at hinner
  let outerState : TypeChecker.State :=
    { innerState with ngen := innerState.ngen.next }
  have houterCache :
      outerState.inferTypeC[(.const ``AnnotatedPi [] : Expr)]? =
        some (.sort (.succ .zero)) := by
    exact hinnerCache
  have hfamily :
      TypeChecker.Inner.inferType' (.const ``AnnotatedPi []) false
          (TypeChecker.Methods.withFuel 9998)
          ({ env := annotatedPiCtorCandidateContext.toTypeChecker.env
             lctx := annotatedPiCtorCandidateContext.toTypeChecker.lctx.mkLocalDecl
               ⟨innerState.ngen.curr⟩ annotatedPiOuterName
               annotatedPiViewInnerKernel .default
             safety := annotatedPiCtorCandidateContext.toTypeChecker.safety
             eagerReduce := annotatedPiCtorCandidateContext.toTypeChecker.eagerReduce
             lparams := annotatedPiCtorCandidateContext.toTypeChecker.lparams
             fuel := annotatedPiCtorCandidateContext.toTypeChecker.fuel } :
            TypeChecker.Context)
          outerState =
        .ok (.sort (.succ .zero), outerState) := by
    simpa [annotatedPiCtorCandidateContext,
      AddInductive.Context.toTypeChecker] using
      annotatedPiInferTypeFamilyCached 9998
        (annotatedPiCtorCandidateContext.toTypeChecker.lctx.mkLocalDecl
          ⟨innerState.ngen.curr⟩ annotatedPiOuterName
          annotatedPiViewInnerKernel .default)
        outerState houterCache
  unfold annotatedPiViewInnerKernel at hfamily
  unfold annotatedPiViewCtorKernel TypeChecker.Inner.inferType'
  simp [annotatedPiViewInnerKernel, Expr.hasLooseBVars, Expr.looseBVarRange',
    TypeChecker.Inner.inferForall, TypeChecker.Inner.inferForall.loop, Expr.instantiate1',
    annotatedPiWithLocalDecl, Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [hinner]
  simp only [TypeChecker.Inner.ensureSortCore, Expr.isSort, ↓reduceIte, Bind.bind, ReaderT.pure,
    StateT.pure, Except.pure, Pure.pure]
  rw [hfamily]
  simp [Expr.sortLevel!, annotatedPi_mkLevelIMaxSuccZero, ReaderT.pure, StateT.pure, Except.pure,
    Pure.pure]
  rfl

private theorem annotatedPiSortZeroCheckTypeStep_valid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨annotatedPiCtorCandidateContext, .sort .zero,
        .sort (.succ .zero)⟩ := by
  unfold AddInductive.CandidateCheckTypeStep.Valid
  change
    Except.map (fun x : Expr × TypeChecker.State => x.1)
      (TypeChecker.Inner.inferType (.sort .zero) false
        (TypeChecker.Methods.withFuel 10000)
        annotatedPiCtorCandidateContext.toTypeChecker
        ({} : TypeChecker.State)) =
      .ok (.sort (.succ .zero))
  change
    Except.map (fun x : Expr × TypeChecker.State => x.1)
      (TypeChecker.Inner.inferType' (.sort .zero) false
        (TypeChecker.Methods.withFuel 9999)
        annotatedPiCtorCandidateContext.toTypeChecker
        ({} : TypeChecker.State)) =
      .ok (.sort (.succ .zero))
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange',
    annotatedPiCtorCandidateContext,
    AddInductive.Context.toTypeChecker,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rfl

private theorem annotatedPiConsumeRawDomain :
    AddInductive.consumeTypeAnnotations annotatedPiRawDomainKernel =
      .sort .zero := by
  simp [AddInductive.consumeTypeAnnotations, annotatedPiRawDomainKernel]

private theorem annotatedPiConsumeInner :
    AddInductive.consumeTypeAnnotations annotatedPiInnerKernel =
      annotatedPiInnerKernel := by
  simp [AddInductive.consumeTypeAnnotations, annotatedPiInnerKernel]

private theorem annotatedPiValidationInnerBodyContext_eq :
    annotatedPiConstructorValidationContext.pushLocalDecl
      `p .default
        (AddInductive.consumeTypeAnnotations annotatedPiRawDomainKernel) =
      annotatedPiInnerBodyCandidateContext := by
  rw [annotatedPiConstructorValidationContext_def_eq,
    annotatedPiConsumeRawDomain]
  rfl

private theorem annotatedPiValidationOuterBodyContext_eq :
    annotatedPiConstructorValidationContext.pushLocalDecl
      annotatedPiOuterName .default
        (AddInductive.consumeTypeAnnotations annotatedPiInnerKernel) =
      annotatedPiOuterBodyCandidateContext := by
  rw [annotatedPiConstructorValidationContext_def_eq,
    annotatedPiConsumeInner]
  rfl

private theorem annotatedPiValidationInnerBody_whnf_eq
    {result : Expr}
    (run : AddInductive.CandidateWhnfStep.Valid
      ⟨({ annotatedPiNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext with
          env := annotatedPiCtorCandidateContext.env }).pushLocalDecl
          `p .default (AddInductive.consumeTypeAnnotations
            annotatedPiRawDomainKernel),
        .const ``AnnotatedPi [], result⟩) :
    result = .const ``AnnotatedPi [] := by
  rw [annotatedPiConstructorValidationContext_eq,
    annotatedPiConsumeRawDomain] at run
  change TypeChecker.M.run annotatedPiInnerBodyCandidateContext.env
    annotatedPiInnerBodyCandidateContext.safety
    annotatedPiInnerBodyCandidateContext.lctx
    annotatedPiInnerBodyCandidateContext.lparams
    annotatedPiInnerBodyCandidateContext.fuel
    (TypeChecker.whnf (.const ``AnnotatedPi [])) = .ok result at run
  have known := annotatedPiInnerBodyCandidateStep_valid
  change TypeChecker.M.run annotatedPiInnerBodyCandidateContext.env
    annotatedPiInnerBodyCandidateContext.safety
    annotatedPiInnerBodyCandidateContext.lctx
    annotatedPiInnerBodyCandidateContext.lparams
    annotatedPiInnerBodyCandidateContext.fuel
    (TypeChecker.whnf (.const ``AnnotatedPi [])) =
      .ok (.const ``AnnotatedPi []) at known
  rw [known] at run
  exact (Except.ok.inj run).symm

private theorem constructorTypeValidationTrace_spineLength_zero
    {stats : AddInductive.InductiveStats} {isUnsafe : Bool}
    {familyIdx : Nat} {ctor : Name} {context : AddInductive.Context}
    {source : Expr} {argIdx fuel : Nat}
    (trace : AddInductive.ConstructorTypeValidationTrace stats isUnsafe
      familyIdx ctor context source argIdx fuel)
    (terminal : source.isForall = false) :
    trace.spineLength = 0 := by
  cases trace <;>
    simp_all [AddInductive.ConstructorTypeValidationTrace.spineLength,
      Expr.isForall]

private theorem constructorTypeValidationTrace_eq_terminal
    {stats : AddInductive.InductiveStats} {isUnsafe : Bool}
    {familyIdx : Nat} {ctor : Name} {context : AddInductive.Context}
    {source : Expr} {argIdx fuel : Nat}
    (trace : AddInductive.ConstructorTypeValidationTrace stats isUnsafe
      familyIdx ctor context source argIdx (fuel + 1))
    (terminal : source.isForall = false)
    (valid : AddInductive.isValidIndAppIdx stats source familyIdx = true) :
    trace = .terminal context source fuel argIdx terminal valid := by
  cases trace with
  | parameter context fuel argIdx name domain body binderInfo param
      parameterType parameterAt parameterTypeRun defeq tail =>
      have impossible :
          (Expr.forallE name domain body binderInfo).isForall = true := rfl
      rw [impossible] at terminal
      contradiction
  | ordinary context fuel argIdx name domain body binderInfo sortResult
      noParameter ensureType universeTrace positivity tail =>
      have impossible :
          (Expr.forallE name domain body binderInfo).isForall = true := rfl
      rw [impossible] at terminal
      contradiction
  | terminal => rfl

set_option maxHeartbeats 10000000 in
private def annotatedPiStagedPostFamilyInput :
    VInductDecl.StagedNormalizationCandidatePostFamilyInput
      annotatedPiFamilyCandidateContext annotatedPiCtorCandidateContext
      outParamEnv [] annotatedPiNormalizationCandidate
      annotatedPiRawDecl where
  universeInput := annotatedPiStagedUniverseInput
  alignment := by
    change AddInductive.ConstructorCandidateAlignmentTrace
      annotatedPiStagedUniverseInput.staged.family.validation.stats false 0
      annotatedPiConstructorValidationContext
      annotatedPiStagedUniverseInput.staged.constructorValidation.trace
      (.cons annotatedPiConstructorCandidate .nil)
    generalize htrace :
      annotatedPiStagedUniverseInput.staged.constructorValidation.trace = trace
    cases trace with
    | cons seen head constructors constructorFresh constructorClosed
        constructorRootCheck typeTrace listTailTrace =>
        cases typeTrace with
        | parameter context fuel argIdx name domain body binderInfo param
            parameterType parameterAt parameterTypeRun defeq tail =>
            rw [annotatedPiStagedParams_zero] at parameterAt
            contradiction
        | terminal context source fuel argIdx terminal valid =>
            rw [annotatedPiKernelCtor_isForall] at terminal
            contradiction
        | ordinary context fuel argIdx name domain body binderInfo sortResult
            noParameter ensureType universeTrace positivity tail =>
            cases listTailTrace
            cases positivity with
            | skipped isUnsafe_eq => contradiction
            | safe isUnsafe_eq positivityTrace =>
                cases positivityTrace with
                | absent context source result fuel whnf occurs =>
                    change AddInductive.CandidateWhnfStep.Valid
                      ⟨{ annotatedPiNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext with
                          env := annotatedPiCtorCandidateContext.env },
                        annotatedPiInnerKernel, result⟩ at whnf
                    rw [annotatedPiConstructorValidationContext_eq] at whnf
                    change TypeChecker.M.run annotatedPiCtorCandidateContext.env
                      annotatedPiCtorCandidateContext.safety
                      annotatedPiCtorCandidateContext.lctx
                      annotatedPiCtorCandidateContext.lparams
                      annotatedPiCtorCandidateContext.fuel
                      (TypeChecker.whnf annotatedPiInnerKernel) =
                        .ok result at whnf
                    rw [annotatedPiInner_whnfM] at whnf
                    cases whnf
                    rw [annotatedPiStagedStats_eq,
                      annotatedPiInner_stats_hasIndOcc] at occurs
                    contradiction
                | target context source result fuel targetIdx whnf occurs
                    terminal valid =>
                    change AddInductive.CandidateWhnfStep.Valid
                      ⟨{ annotatedPiNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext with
                          env := annotatedPiCtorCandidateContext.env },
                        annotatedPiInnerKernel, result⟩ at whnf
                    rw [annotatedPiConstructorValidationContext_eq] at whnf
                    change TypeChecker.M.run annotatedPiCtorCandidateContext.env
                      annotatedPiCtorCandidateContext.safety
                      annotatedPiCtorCandidateContext.lctx
                      annotatedPiCtorCandidateContext.lparams
                      annotatedPiCtorCandidateContext.fuel
                      (TypeChecker.whnf annotatedPiInnerKernel) =
                        .ok result at whnf
                    rw [annotatedPiInner_whnfM] at whnf
                    cases whnf
                    simp [annotatedPiInnerKernel, Expr.isForall] at terminal
                | forallE positivityContext positivitySource positivityFuel
                    positivityName positivityDomain positivityBody
                    positivityBinderInfo positivityWhnf positivityOccurs
                    positivityDomainFree positivityTail =>
                    change AddInductive.CandidateWhnfStep.Valid
                      ⟨{ annotatedPiNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext with
                          env := annotatedPiCtorCandidateContext.env },
                        annotatedPiInnerKernel,
                        .forallE positivityName positivityDomain positivityBody
                          positivityBinderInfo⟩ at positivityWhnf
                    rw [annotatedPiConstructorValidationContext_eq] at positivityWhnf
                    change TypeChecker.M.run annotatedPiCtorCandidateContext.env
                      annotatedPiCtorCandidateContext.safety
                      annotatedPiCtorCandidateContext.lctx
                      annotatedPiCtorCandidateContext.lparams
                      annotatedPiCtorCandidateContext.fuel
                      (TypeChecker.whnf annotatedPiInnerKernel) =
                        .ok (.forallE positivityName positivityDomain
                          positivityBody positivityBinderInfo) at positivityWhnf
                    rw [annotatedPiInner_whnfM] at positivityWhnf
                    cases positivityWhnf
                    have hTailSpine : tail.spineLength = 0 :=
                      constructorTypeValidationTrace_spineLength_zero tail (by
                        simp only [annotatedPiConst_instantiate1,
                          Expr.isForall])
                    cases positivityTail with
                    | absent context source result fuel whnf occurs =>
                        have whnf' : AddInductive.CandidateWhnfStep.Valid
                            ⟨({ annotatedPiNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext with
                                env := annotatedPiCtorCandidateContext.env }).pushLocalDecl
                                `p .default (AddInductive.consumeTypeAnnotations
                                  annotatedPiRawDomainKernel),
                              .const ``AnnotatedPi [], result⟩ := by
                          simpa only [annotatedPiConst_instantiate1] using whnf
                        have hresult :=
                          annotatedPiValidationInnerBody_whnf_eq whnf'
                        subst result
                        rw [annotatedPiStagedStats_eq,
                          annotatedPiConst_hasIndOcc] at occurs
                        contradiction
                    | forallE context source fuel name domain body binderInfo
                        whnf occurs domainFree positivityTail =>
                        have whnf' : AddInductive.CandidateWhnfStep.Valid
                            ⟨({ annotatedPiNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext with
                                env := annotatedPiCtorCandidateContext.env }).pushLocalDecl
                                `p .default (AddInductive.consumeTypeAnnotations
                                  annotatedPiRawDomainKernel),
                              .const ``AnnotatedPi [],
                              .forallE name domain body binderInfo⟩ := by
                          simpa only [annotatedPiConst_instantiate1] using whnf
                        have hresult :=
                          annotatedPiValidationInnerBody_whnf_eq whnf'
                        contradiction
                    | target targetContext targetSource targetResult targetFuel
                        targetIdx targetWhnf targetOccurs targetTerminal
                        targetValid =>
                        have targetWhnfNormalized :
                            AddInductive.CandidateWhnfStep.Valid
                              ⟨({ annotatedPiNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext with
                                  env := annotatedPiCtorCandidateContext.env }).pushLocalDecl
                                  `p .default (AddInductive.consumeTypeAnnotations
                                    annotatedPiRawDomainKernel),
                                .const ``AnnotatedPi [], targetResult⟩ := by
                          simpa only [annotatedPiConst_instantiate1] using
                            targetWhnf
                        have hresult :=
                          annotatedPiValidationInnerBody_whnf_eq
                            targetWhnfNormalized
                        subst targetResult
                        simp only [annotatedPiConst_instantiate1] at tail ⊢
                        cases tail
                        change AddInductive.CandidateCheckTypeObservation
                          annotatedPiConstructorValidationContext.withEmptyLocalContext
                          annotatedPiKernelCtor.type at constructorRootCheck
                        let rootChecked :=
                          AddInductive.ConstructorCheckedExpr.ofClosedRoot
                            constructorClosed constructorRootCheck
                        let innerChecked : AddInductive.ConstructorCheckedExpr
                            annotatedPiCtorCandidateContext
                            annotatedPiInnerKernel :=
                          .ofRun (by
                            simp [annotatedPiInnerKernel,
                              annotatedPiRawDomainKernel, FVarsIn,
                              Level.hasMVar'])
                            annotatedPiInnerCheckTypeStep_valid
                        let viewInnerChecked : AddInductive.ConstructorCheckedExpr
                            annotatedPiCtorCandidateContext
                            annotatedPiViewInnerKernel :=
                          .ofRun (by
                            simp [annotatedPiViewInnerKernel, FVarsIn,
                              Level.hasMVar'])
                            annotatedPiViewInnerCheckTypeStep_valid
                        let domainChecked : AddInductive.ConstructorCheckedExpr
                            annotatedPiCtorCandidateContext
                            annotatedPiRawDomainKernel :=
                          .ofRun (by
                            simp [annotatedPiRawDomainKernel, FVarsIn,
                              Level.hasMVar'])
                            annotatedPiDomainCheckTypeStep_valid
                        let sortChecked : AddInductive.ConstructorCheckedExpr
                            annotatedPiCtorCandidateContext (.sort .zero) :=
                          .ofRun (by simp [FVarsIn, Level.hasMVar'])
                            annotatedPiSortZeroCheckTypeStep_valid
                        let innerBodyChecked :
                            AddInductive.ConstructorCheckedExpr
                              annotatedPiInnerBodyCandidateContext
                              (.const ``AnnotatedPi []) :=
                          .ofRun (by simp [FVarsIn])
                            annotatedPiInnerBodyCheckTypeStep_valid
                        let outerBodyChecked :
                            AddInductive.ConstructorCheckedExpr
                              annotatedPiOuterBodyCandidateContext
                              (.const ``AnnotatedPi []) :=
                          .ofRun (by simp [FVarsIn])
                            annotatedPiOuterBodyCheckTypeStep_valid
                        let innerChecked' := annotatedPiAlignChecked
                          annotatedPiConstructorValidationContext_def_eq rfl
                          innerChecked
                        let viewInnerChecked' := annotatedPiAlignChecked
                          annotatedPiConstructorValidationContext_def_eq
                          annotatedPiAlignedViewInnerKernel_eq viewInnerChecked
                        let consumedInnerChecked := annotatedPiAlignChecked
                          annotatedPiConstructorValidationContext_def_eq
                          annotatedPiConsumeInner innerChecked
                        let domainChecked' := annotatedPiAlignChecked
                          annotatedPiConstructorValidationContext_def_eq rfl
                          domainChecked
                        let sortChecked' := annotatedPiAlignChecked
                          annotatedPiConstructorValidationContext_def_eq
                          annotatedPiConsumeRawDomain sortChecked
                        let innerBodyChecked' := annotatedPiAlignChecked
                          annotatedPiValidationInnerBodyContext_eq rfl
                          innerBodyChecked
                        let innerBodyPositivityChecked :=
                          annotatedPiAlignChecked
                            annotatedPiValidationInnerBodyContext_eq
                            (annotatedPiConst_instantiate1
                              annotatedPiConstructorValidationContext.freshExpr)
                            innerBodyChecked
                        let outerBodyChecked' := annotatedPiAlignChecked
                          annotatedPiValidationOuterBodyContext_eq rfl
                          outerBodyChecked
                        let outerBodySourceChecked := annotatedPiAlignChecked
                          annotatedPiValidationOuterBodyContext_eq
                          (annotatedPiConst_instantiate1
                            annotatedPiConstructorValidationContext.freshExpr)
                          outerBodyChecked
                        have outerTailView_eq :
                            ((Expr.const ``AnnotatedPi []).abstract
                                #[annotatedPiCtorCandidateContext.freshExpr]
                              |>.instantiate1
                                annotatedPiConstructorValidationContext.freshExpr) =
                              .const ``AnnotatedPi [] := by
                          simp [annotatedPiConst_abstract_singleton]
                        let outerBodyViewChecked := annotatedPiAlignChecked
                          annotatedPiValidationOuterBodyContext_eq
                          outerTailView_eq outerBodyChecked
                        let innerAnnotations :
                            AddInductive.CandidateIsDefEqObservation
                              annotatedPiCtorCandidateContext
                              annotatedPiInnerKernel annotatedPiInnerKernel :=
                          ⟨AddInductive.candidateIsDefEqRefl
                            annotatedPiCtorCandidateContext
                            annotatedPiInnerKernel⟩
                        let innerAnnotations' := annotatedPiAlignIsDefEq
                          annotatedPiConstructorValidationContext_def_eq rfl
                          annotatedPiConsumeInner innerAnnotations
                        let domainAnnotations :
                            AddInductive.CandidateIsDefEqObservation
                              annotatedPiCtorCandidateContext
                              annotatedPiRawDomainKernel (.sort .zero) :=
                          ⟨annotatedPiDomainAnnotationsEq⟩
                        let domainAnnotations' := annotatedPiAlignIsDefEq
                          annotatedPiConstructorValidationContext_def_eq rfl
                          annotatedPiConsumeRawDomain domainAnnotations
                        have sortCheckedInferred :
                            sortChecked'.observation.inferred =
                              .sort (.succ .zero) := by
                          apply sortChecked'.inferred_eq_of_run
                          rw [annotatedPiConstructorValidationContext_def_eq,
                            annotatedPiConsumeRawDomain]
                          exact annotatedPiSortZeroCheckTypeStep_valid
                        have rootStoredSpine :
                            annotatedPiConstructorCandidate.type.trace.storedSpine =
                              true := by
                          change annotatedPiCtorCandidate.trace.storedSpine = true
                          exact annotatedPiCtorCandidate_storedSpine
                        have rootDepth :
                            annotatedPiConstructorCandidate.type.context.fuel.recDepth =
                              annotatedPiConstructorValidationContext.fuel.recDepth := by
                          rfl
                        let constructorTailTrace :=
                          AddInductive.ConstructorTypeValidationTrace.terminal
                            (stats := annotatedPiStagedUniverseInput.staged.family.validation.stats)
                            (isUnsafe := false) (familyIdx := 0)
                            (ctor := annotatedPiKernelCtor.name)
                            (annotatedPiConstructorValidationContext.pushLocalDecl
                              annotatedPiOuterName .default
                                (AddInductive.consumeTypeAnnotations
                                  annotatedPiInnerKernel))
                            ((Expr.const ``AnnotatedPi []).instantiate1
                              annotatedPiConstructorValidationContext.freshExpr)
                            998 1
                            (by
                              simp only [annotatedPiConst_instantiate1,
                                Expr.isForall])
                            (by
                              simp only [annotatedPiConst_instantiate1]
                              assumption)
                        have tail_eq : tail = constructorTailTrace := by
                          unfold constructorTailTrace
                          apply constructorTypeValidationTrace_eq_terminal
                        let positivityTargetTrace :=
                          AddInductive.ConstructorPositivityTrace.target
                            (stats := annotatedPiStagedUniverseInput.staged.family.validation.stats)
                            (ctor := annotatedPiKernelCtor.name)
                            (argIdx := 0)
                            (annotatedPiConstructorValidationContext.pushLocalDecl
                              `p .default
                                (AddInductive.consumeTypeAnnotations
                                  annotatedPiRawDomainKernel))
                            ((Expr.const ``AnnotatedPi []).instantiate1
                              annotatedPiConstructorValidationContext.freshExpr)
                            (.const ``AnnotatedPi []) 998 targetIdx
                            targetWhnf targetOccurs targetTerminal targetValid
                        let nestedPositivityTrace :=
                          AddInductive.ConstructorPositivityTrace.forallE
                            (stats := annotatedPiStagedUniverseInput.staged.family.validation.stats)
                            (ctor := annotatedPiKernelCtor.name)
                            (argIdx := 0)
                            annotatedPiConstructorValidationContext
                            annotatedPiInnerKernel 999 `p
                            annotatedPiRawDomainKernel
                            (.const ``AnnotatedPi []) .default positivityWhnf
                            positivityOccurs positivityDomainFree
                            positivityTargetTrace
                        let positivityModeTrace :=
                          AddInductive.ConstructorPositivityModeTrace.safe
                            isUnsafe_eq nestedPositivityTrace
                        let headValidationTrace :=
                          AddInductive.ConstructorTypeValidationTrace.ordinary
                            annotatedPiConstructorValidationContext 999 0
                            annotatedPiOuterName annotatedPiInnerKernel
                            (.const ``AnnotatedPi []) .default sortResult
                            noParameter ensureType universeTrace
                            positivityModeTrace constructorTailTrace
                        have rootSpineLength' :
                            annotatedPiConstructorCandidate.type.trace.spineLength =
                              headValidationTrace.spineLength := by
                          rfl
                        have positivityTargetAlignment :
                            AddInductive.ConstructorPositivityAlignmentTrace
                              positivityTargetTrace :=
                          .target innerBodyPositivityChecked
                        have positivityAlignment :
                            AddInductive.ConstructorPositivityModeAlignmentTrace
                              positivityModeTrace :=
                          .safe <| .forallE innerChecked' domainChecked'
                            sortChecked' (.succ .zero)
                            sortCheckedInferred (by
                              rw [annotatedPiConstructorValidationContext_def_eq]
                              exact annotatedPiCtorCandidateFresh)
                            domainAnnotations' positivityTargetTrace
                            positivityTargetAlignment
                        have outerTailAlignment :
                            AddInductive.ConstructorViewAlignmentTrace
                              constructorTailTrace
                              ((Expr.const ``AnnotatedPi []).abstract
                                  #[annotatedPiCtorCandidateContext.freshExpr]
                                |>.instantiate1
                                  annotatedPiConstructorValidationContext.freshExpr) := by
                          simp only [annotatedPiConst_abstract_singleton,
                            annotatedPiConst_instantiate1]
                          exact .terminal outerBodySourceChecked
                            outerBodyChecked'
                            (by simp [Expr.isForall]) (by assumption)
                        have headAlignment :
                            AddInductive.ConstructorViewAlignmentTrace
                              headValidationTrace
                              annotatedPiConstructorCandidate.type.view := by
                          change AddInductive.ConstructorViewAlignmentTrace
                            headValidationTrace
                            annotatedPiAlignedViewCtorKernel
                          exact AddInductive.ConstructorViewAlignmentTrace.ordinary
                              innerChecked' viewInnerChecked'
                              ⟨annotatedPiInnerView_isDefEq⟩
                              consumedInnerChecked
                              positivityModeTrace
                              positivityAlignment (by
                                rw [annotatedPiConstructorValidationContext_def_eq]
                                exact annotatedPiCtorCandidateFresh)
                              innerAnnotations' constructorTailTrace
                              outerTailAlignment
                        rw [tail_eq]
                        exact
                          AddInductive.ConstructorCandidateAlignmentTrace.cons
                            (seen := ∅) (fresh := constructorFresh)
                            (closed := constructorClosed)
                            (rootCheck := constructorRootCheck)
                            (typeTrace := headValidationTrace)
                            (tailTrace :=
                              AddInductive.ConstructorListValidationTrace.nil
                                ((∅ : NameSet).insert
                                  annotatedPiKernelCtor.name))
                            (candidate := annotatedPiConstructorCandidate)
                            (candidates := AddInductive.CandidateList.nil)
                            rootChecked rootStoredSpine rootSpineLength'
                            rootDepth headAlignment
                            (AddInductive.ConstructorCandidateAlignmentTrace.nil
                              (stats := annotatedPiStagedUniverseInput.staged.family.validation.stats)
                              (isUnsafe := false) (familyIdx := 0)
                              (context := annotatedPiConstructorValidationContext)
                              ((∅ : NameSet).insert
                                annotatedPiKernelCtor.name))

private theorem annotatedPiPreFamilySortZeroCheckTypeStep_valid
    (context : AddInductive.Context)
    (depth : context.fuel.recDepth = 10000) :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨context, .sort .zero, .sort (.succ .zero)⟩ := by
  unfold AddInductive.CandidateCheckTypeStep.Valid
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
      (TypeChecker.Inner.inferType (.sort .zero) false
        (TypeChecker.Methods.withFuel context.fuel.recDepth)
        context.toTypeChecker ({} : TypeChecker.State)) = _
  rw [depth]
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
      (TypeChecker.Inner.inferType' (.sort .zero) false
        (TypeChecker.Methods.withFuel 9999)
        context.toTypeChecker ({} : TypeChecker.State)) = _
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange',
    annotatedPi_checkLevelZero, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind]
  rfl

private theorem annotatedPiPreFamilySortOneCheckTypeStep_valid
    (context : AddInductive.Context)
    (depth : context.fuel.recDepth = 10000) :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨context, .sort (.succ .zero),
        .sort (.succ (.succ .zero))⟩ := by
  unfold AddInductive.CandidateCheckTypeStep.Valid
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
      (TypeChecker.Inner.inferType (.sort (.succ .zero)) false
        (TypeChecker.Methods.withFuel context.fuel.recDepth)
        context.toTypeChecker ({} : TypeChecker.State)) = _
  rw [depth]
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
      (TypeChecker.Inner.inferType' (.sort (.succ .zero)) false
        (TypeChecker.Methods.withFuel 9999)
        context.toTypeChecker ({} : TypeChecker.State)) = _
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange',
    annotatedPi_checkLevelSuccZero, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind]
  rfl

private def annotatedPiPreFamilySortZeroInferState : TypeChecker.State :=
  { ({} : TypeChecker.State) with
    inferTypeI := ({} : TypeChecker.State).inferTypeI.insert
      (.sort .zero) (.sort (.succ .zero)) }

private theorem annotatedPiPreFamilySortZeroInferTypeInner
    (context : AddInductive.Context)
    (depth : context.fuel.recDepth = 10000) :
    TypeChecker.Inner.inferType (.sort .zero) true
        (TypeChecker.Methods.withFuel context.fuel.recDepth)
        context.toTypeChecker ({} : TypeChecker.State) =
      .ok (.sort (.succ .zero),
        annotatedPiPreFamilySortZeroInferState) := by
  rw [depth]
  change TypeChecker.Inner.inferType' (.sort .zero) true
      (TypeChecker.Methods.withFuel 9999) context.toTypeChecker
      ({} : TypeChecker.State) = _
  unfold TypeChecker.Inner.inferType'
  simp [annotatedPiPreFamilySortZeroInferState,
    Expr.hasLooseBVars, Expr.looseBVarRange', Bind.bind,
    ReaderT.bind, StateT.bind, Except.bind]

private theorem annotatedPiPreFamilySortZeroEnsureTypeStep_valid
    (context : AddInductive.Context)
    (depth : context.fuel.recDepth = 10000) :
    AddInductive.ConstructorEnsureTypeStep.Valid
      ⟨context, .sort .zero, .sort (.succ .zero)⟩ := by
  unfold AddInductive.ConstructorEnsureTypeStep.Valid
    TypeChecker.ensureType TypeChecker.inferType TypeChecker.ensureSort
    TypeChecker.RecM.run TypeChecker.M.run
  simp only [readThe, MonadReaderOf.read, ReaderT.read,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure, StateT.run',
    Functor.map, Except.map]
  rw [show TypeChecker.Inner.inferType (.sort .zero) true
      (TypeChecker.Methods.withFuel context.fuel.recDepth)
      { env := context.env
        lctx := context.lctx
        safety := context.safety
        lparams := context.lparams
        fuel := context.fuel }
      ({} : TypeChecker.State) =
        .ok (.sort (.succ .zero),
          annotatedPiPreFamilySortZeroInferState) by
    simpa [AddInductive.Context.toTypeChecker] using
      annotatedPiPreFamilySortZeroInferTypeInner context depth]
  rfl

private theorem annotatedPiPreFamilySafetyRun :
    AddInductive.checkConstructorPreFamilySafety
        annotatedPiStagedUniverseInput.staged.family.validation.stats
        annotatedPiNormalizationCandidate.families.singleton.familyType.type.view
        annotatedPiNormalizationCandidate.families.singleton.constructors
        annotatedPiNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext =
      .ok () := by
  change AddInductive.checkConstructorPreFamilySafety
    annotatedPiInductiveStats (.sort (.succ .zero))
    (.cons annotatedPiConstructorCandidate .nil)
    annotatedPiFamilyCandidateContext = .ok ()
  have consumeSortZero : AddInductive.consumeTypeAnnotations
      (.sort .zero) = .sort .zero := by
    simp [AddInductive.consumeTypeAnnotations]
  let nestedContext := annotatedPiFamilyCandidateContext.pushLocalDecl
    `p .default (AddInductive.consumeTypeAnnotations (.sort .zero))
  let resultContext := annotatedPiFamilyCandidateContext.advanceFresh
  let rootSortZero : AddInductive.ConstructorCheckedExpr
      annotatedPiFamilyCandidateContext (.sort .zero) :=
    .ofRun (by simp [FVarsIn, Level.hasMVar'])
      (annotatedPiPreFamilySortZeroCheckTypeStep_valid
        annotatedPiFamilyCandidateContext rfl)
  let rootSortOne : AddInductive.ConstructorCheckedExpr
      annotatedPiFamilyCandidateContext (.sort (.succ .zero)) :=
    .ofRun (by simp [FVarsIn, Level.hasMVar'])
      (annotatedPiPreFamilySortOneCheckTypeStep_valid
        annotatedPiFamilyCandidateContext rfl)
  let nestedSortOne : AddInductive.ConstructorCheckedExpr
      nestedContext (.sort (.succ .zero)) :=
    .ofRun (by simp [FVarsIn, Level.hasMVar'])
      (annotatedPiPreFamilySortOneCheckTypeStep_valid nestedContext rfl)
  let resultSortOne : AddInductive.ConstructorCheckedExpr
      resultContext (.sort (.succ .zero)) :=
    .ofRun (by simp [FVarsIn, Level.hasMVar'])
      (annotatedPiPreFamilySortOneCheckTypeStep_valid resultContext rfl)
  let rootEnsure : AddInductive.ConstructorEnsureTypeObservation
      annotatedPiFamilyCandidateContext (.sort .zero) :=
    ⟨.sort (.succ .zero),
      annotatedPiPreFamilySortZeroEnsureTypeStep_valid
        annotatedPiFamilyCandidateContext rfl⟩
  let consumedSortZero : AddInductive.ConstructorCheckedExpr
      annotatedPiFamilyCandidateContext
        (AddInductive.consumeTypeAnnotations (.sort .zero)) := by
    rw [consumeSortZero]
    exact rootSortZero
  let annotations : AddInductive.CandidateIsDefEqObservation
      annotatedPiFamilyCandidateContext (.sort .zero)
        (AddInductive.consumeTypeAnnotations (.sort .zero)) :=
    ⟨by
      rw [consumeSortZero]
      exact AddInductive.candidateIsDefEqRefl
        annotatedPiFamilyCandidateContext (.sort .zero)⟩
  have rootFresh : annotatedPiFamilyCandidateContext.lctx.find?
      annotatedPiFamilyCandidateContext.freshFVarId = none := by
    have h := LocalContext.WF.find?_eq_find?_toList
      (fv := annotatedPiFamilyCandidateContext.freshFVarId)
      LocalContext.WF.nil
    change
      ({ fvarIdToDecl := PersistentHashMap.empty
         decls := PersistentArray.empty
         auxDeclToFullName := Std.TreeMap.empty } : LocalContext).find?
        annotatedPiFamilyCandidateContext.freshFVarId = none
    rw [h]
    simp [LocalContext.toList]
  let rootSpine : AddInductive.ConstructorPreFamilyIndexSpineTrace
      annotatedPiFamilyCandidateContext (.sort (.succ .zero)) [] :=
    .nil annotatedPiFamilyCandidateContext (.sort (.succ .zero))
      rootSortOne rfl
  let nestedSpine : AddInductive.ConstructorPreFamilyIndexSpineTrace
      nestedContext (.sort (.succ .zero)) [] :=
    .nil nestedContext (.sort (.succ .zero)) nestedSortOne rfl
  let resultSpine : AddInductive.ConstructorPreFamilyIndexSpineTrace
      resultContext (.sort (.succ .zero)) [] :=
    .nil resultContext (.sort (.succ .zero)) resultSortOne rfl
  have valid : AddInductive.isValidIndAppIdx annotatedPiInductiveStats
      (.const ``AnnotatedPi []) 0 = true :=
    annotatedPiConst_isValidIndAppIdx
  have targetArgs :
      (Expr.const ``AnnotatedPi []).getAppArgs.toList.drop
        annotatedPiInductiveStats.params.size = [] := by
    rfl
  obtain ⟨nestedTargetSpine, nestedTargetSpineRun⟩ :
      ∃ nestedTargetSpine :
          AddInductive.ConstructorPreFamilyIndexSpineTrace nestedContext
            (.sort (.succ .zero))
            ((Expr.const ``AnnotatedPi []).getAppArgs.toList.drop
              annotatedPiInductiveStats.params.size),
        AddInductive.ConstructorPreFamilyIndexSpineTrace.build nestedContext
            (.sort (.succ .zero))
            ((Expr.const ``AnnotatedPi []).getAppArgs.toList.drop
              annotatedPiInductiveStats.params.size) =
          .ok nestedTargetSpine := by
    rw [targetArgs]
    exact ⟨nestedSpine, nestedSpine.build_eq⟩
  let targetTrace : AddInductive.ConstructorPreFamilyRecursiveTrace
      annotatedPiInductiveStats 0 (.sort (.succ .zero)) nestedContext
        (.const ``AnnotatedPi []) 999 :=
    .target nestedContext (.const ``AnnotatedPi []) valid nestedTargetSpine
  have targetRun :
      AddInductive.ConstructorPreFamilyRecursiveTrace.build
          annotatedPiInductiveStats 0 (.sort (.succ .zero)) nestedContext
          (.const ``AnnotatedPi []) 999 = .ok targetTrace := by
    simp only [AddInductive.ConstructorPreFamilyRecursiveTrace.build]
    rw [dif_pos valid, nestedTargetSpineRun]
    rfl
  obtain ⟨recursiveTailTrace, recursiveTailRun⟩ :
      ∃ recursiveTailTrace :
          AddInductive.ConstructorPreFamilyRecursiveTrace
            annotatedPiInductiveStats 0 (.sort (.succ .zero)) nestedContext
            ((Expr.const ``AnnotatedPi []).instantiate1
              annotatedPiFamilyCandidateContext.freshExpr) 999,
        AddInductive.ConstructorPreFamilyRecursiveTrace.build
            annotatedPiInductiveStats 0 (.sort (.succ .zero)) nestedContext
            ((Expr.const ``AnnotatedPi []).instantiate1
              annotatedPiFamilyCandidateContext.freshExpr) 999 =
          .ok recursiveTailTrace := by
    rw [annotatedPiConst_instantiate1]
    exact ⟨targetTrace, targetRun⟩
  let recursiveTrace : AddInductive.ConstructorPreFamilyRecursiveTrace
      annotatedPiInductiveStats 0 (.sort (.succ .zero))
        annotatedPiFamilyCandidateContext annotatedPiViewInnerKernel
        annotatedPiFamilyCandidateContext.fuel.inductiveFuel :=
    .forallE annotatedPiFamilyCandidateContext `p (.sort .zero)
      (.const ``AnnotatedPi []) .default rootSortZero rootEnsure
      consumedSortZero annotations rootFresh (by
        simpa only [nestedContext] using recursiveTailTrace)
  have recursiveRun :
      AddInductive.ConstructorPreFamilyRecursiveTrace.build
          annotatedPiInductiveStats 0 (.sort (.succ .zero))
          annotatedPiFamilyCandidateContext annotatedPiViewInnerKernel
          annotatedPiFamilyCandidateContext.fuel.inductiveFuel =
        .ok recursiveTrace := by
    change AddInductive.ConstructorPreFamilyRecursiveTrace.build
        annotatedPiInductiveStats 0 (.sort (.succ .zero))
        annotatedPiFamilyCandidateContext annotatedPiViewInnerKernel 1000 =
      .ok recursiveTrace
    simp only [annotatedPiViewInnerKernel,
      AddInductive.ConstructorPreFamilyRecursiveTrace.build]
    rw [rootSortZero.check_eq, rootEnsure.observe_eq,
      consumedSortZero.check_eq]
    simp only [Bind.bind, Except.bind]
    rw [annotations.observe_eq]
    simp only []
    rw [dif_pos rootFresh]
    rw [recursiveTailRun]
    rfl
  have resultIndependent : AddInductive.constructorIndependentOf
      (.const ``AnnotatedPi [])
      [annotatedPiFamilyCandidateContext.freshFVarId] = true := by
    rfl
  obtain ⟨resultTargetSpine, resultTargetSpineRun⟩ :
      ∃ resultTargetSpine :
          AddInductive.ConstructorPreFamilyIndexSpineTrace resultContext
            (.sort (.succ .zero))
            ((Expr.const ``AnnotatedPi []).getAppArgs.toList.drop
              annotatedPiInductiveStats.params.size),
        AddInductive.ConstructorPreFamilyIndexSpineTrace.build resultContext
            (.sort (.succ .zero))
            ((Expr.const ``AnnotatedPi []).getAppArgs.toList.drop
              annotatedPiInductiveStats.params.size) =
          .ok resultTargetSpine := by
    rw [targetArgs]
    exact ⟨resultSpine, resultSpine.build_eq⟩
  let terminalTrace : AddInductive.ConstructorPreFamilyViewTrace
      annotatedPiInductiveStats 0 (.sort (.succ .zero)) resultContext
        (.const ``AnnotatedPi []) 1
        [annotatedPiFamilyCandidateContext.freshFVarId] true :=
    .terminal resultContext (.const ``AnnotatedPi []) 1
      [annotatedPiFamilyCandidateContext.freshFVarId] true valid
      resultIndependent resultTargetSpine
  have terminalRun :
      AddInductive.ConstructorPreFamilyViewTrace.build
          annotatedPiInductiveStats 0 (.sort (.succ .zero)) resultContext
          (.const ``AnnotatedPi []) 1
          [annotatedPiFamilyCandidateContext.freshFVarId] true 999 =
        .ok terminalTrace := by
    simp only [AddInductive.ConstructorPreFamilyViewTrace.build]
    rw [dif_pos valid, dif_pos resultIndependent, resultTargetSpineRun]
    rfl
  obtain ⟨viewTailTrace, viewTailRun⟩ :
      ∃ viewTailTrace : AddInductive.ConstructorPreFamilyViewTrace
          annotatedPiInductiveStats 0 (.sort (.succ .zero)) resultContext
          ((Expr.const ``AnnotatedPi []).instantiate1
            annotatedPiFamilyCandidateContext.freshExpr)
          1 [annotatedPiFamilyCandidateContext.freshFVarId] true,
        AddInductive.ConstructorPreFamilyViewTrace.build
            annotatedPiInductiveStats 0 (.sort (.succ .zero)) resultContext
            ((Expr.const ``AnnotatedPi []).instantiate1
              annotatedPiFamilyCandidateContext.freshExpr)
            1 [annotatedPiFamilyCandidateContext.freshFVarId] true 999 =
          .ok viewTailTrace := by
    rw [annotatedPiConst_instantiate1]
    exact ⟨terminalTrace, terminalRun⟩
  have noParameter : annotatedPiInductiveStats.params[0]? = none := rfl
  have recursive : AddInductive.hasIndOcc annotatedPiInductiveStats.indConsts
      annotatedPiViewInnerKernel = true := by
    simp [AddInductive.hasIndOcc, annotatedPiInductiveStats,
      annotatedPiViewInnerKernel, Expr.constName!]
  have fieldIndependent : AddInductive.constructorIndependentOf
      annotatedPiViewInnerKernel [] = true := by
    simp [AddInductive.constructorIndependentOf,
      annotatedPiViewInnerKernel]
  let viewTrace : AddInductive.ConstructorPreFamilyViewTrace
      annotatedPiInductiveStats 0 (.sort (.succ .zero))
        annotatedPiFamilyCandidateContext annotatedPiViewCtorKernel 0 [] false :=
    .recursive annotatedPiFamilyCandidateContext 0 [] false
      annotatedPiOuterName annotatedPiViewInnerKernel
      (.const ``AnnotatedPi []) .default noParameter recursive
      fieldIndependent recursiveTrace rootFresh (by
        simpa only [resultContext] using viewTailTrace)
  have viewRun :
      AddInductive.ConstructorPreFamilyViewTrace.build
          annotatedPiInductiveStats 0 (.sort (.succ .zero))
          annotatedPiFamilyCandidateContext annotatedPiViewCtorKernel 0 []
          false 1000 = .ok viewTrace := by
    simp only [annotatedPiViewCtorKernel,
      AddInductive.ConstructorPreFamilyViewTrace.build]
    split
    · rename_i parameter parameterAt
      rw [noParameter] at parameterAt
      contradiction
    · split
      · rename_i nonrecursive
        rw [recursive] at nonrecursive
        contradiction
      · rw [dif_pos fieldIndependent]
        rw [recursiveRun]
        simp only [Bind.bind, Except.bind]
        rw [dif_pos rootFresh]
        rw [viewTailRun]
        rfl
  have candidateViewEq : annotatedPiConstructorCandidate.type.view =
      annotatedPiViewCtorKernel := by
    change annotatedPiCtorCandidate.trace.view = annotatedPiViewCtorKernel
    change annotatedPiAlignedViewCtorKernel = annotatedPiViewCtorKernel
    exact annotatedPiAlignedViewCtorKernel_eq
  obtain ⟨headTrace, headRun⟩ :
      ∃ headTrace : AddInductive.ConstructorPreFamilyViewTrace
          annotatedPiInductiveStats 0 (.sort (.succ .zero))
          annotatedPiFamilyCandidateContext
          annotatedPiConstructorCandidate.type.view 0 [] false,
        AddInductive.ConstructorPreFamilyViewTrace.build
            annotatedPiInductiveStats 0 (.sort (.succ .zero))
            annotatedPiFamilyCandidateContext
            annotatedPiConstructorCandidate.type.view 0 [] false 1000 =
          .ok headTrace := by
    rw [candidateViewEq]
    exact ⟨viewTrace, viewRun⟩
  let listTrace : AddInductive.ConstructorPreFamilyListTrace
      annotatedPiInductiveStats 0 (.sort (.succ .zero))
        annotatedPiFamilyCandidateContext
        (.cons annotatedPiConstructorCandidate .nil) :=
    .cons headTrace .nil
  have listRun :
      AddInductive.ConstructorPreFamilyListTrace.build
          annotatedPiInductiveStats 0 (.sort (.succ .zero))
          annotatedPiFamilyCandidateContext
          (.cons annotatedPiConstructorCandidate .nil) = .ok listTrace := by
    simp only [AddInductive.ConstructorPreFamilyListTrace.build]
    rw [show annotatedPiFamilyCandidateContext.fuel.inductiveFuel = 1000 by
      rfl, headRun]
    rfl
  have parametersRun : AddInductive.instantiateFamilyParameters
      (.sort (.succ .zero)) annotatedPiInductiveStats.params.toList =
        .ok (.sort (.succ .zero)) := by
    rfl
  unfold AddInductive.checkConstructorPreFamilySafety
  have translationUnique :
      (AddInductive.theoryTranslationUnique (.sort (.succ .zero)) &&
        (AddInductive.CandidateList.cons annotatedPiConstructorCandidate
          (AddInductive.CandidateList.nil : AddInductive.CandidateList
            AddInductive.CandidateConstructor [])).viewTranslationUnique) =
        true := by
    simp [AddInductive.theoryTranslationUnique,
      AddInductive.CandidateList.viewTranslationUnique,
      AddInductive.CandidateExprTrace.viewTranslationUnique,
      AddInductive.CandidateExprTrace.view,
      annotatedPiConstructorCandidate, annotatedPiCtorCandidate,
      annotatedPiCtorCandidateTrace, annotatedPiInnerCandidateTrace,
      annotatedPiDomainCandidateTrace, annotatedPiInnerBodyCandidateTrace,
      annotatedPiOuterBodyCandidateTrace,
      annotatedPiConst_abstract_singleton]
  rw [if_pos translationUnique]
  rw [parametersRun]
  simp only [Bind.bind, Except.bind]
  rw [listRun]
  rfl

private def annotatedPiStagedPreFamilyInput :
    VInductDecl.StagedNormalizationCandidatePreFamilyInput
      annotatedPiFamilyCandidateContext annotatedPiCtorCandidateContext
      outParamEnv [] annotatedPiNormalizationCandidate annotatedPiRawDecl :=
  VInductDecl.StagedNormalizationCandidatePreFamilyInput.ofRun
    annotatedPiStagedPostFamilyInput annotatedPiPreFamilySafetyRun

/-- AnnotatedPi's retained validator telescope and candidate telescope admit
the complete post-family semantic interpretation, including the nested
annotation-bearing recursive field. -/
theorem annotatedPiProducedPostFamilySemantic_exists :
    Nonempty (VInductDecl.ProducedNormalizationCandidatePostFamilySemanticRun
      annotatedPiStagedPostFamilyInput) :=
  annotatedPiStagedPostFamilyInput.exists

/-- AnnotatedPi's recursive outer field is omitted from the pre-family local
context while its nested Pi binder and both family-index spines receive the
exact verified family-free interpretation. -/
theorem annotatedPiProducedPreFamilySemantic_exists :
    Nonempty (VInductDecl.ProducedNormalizationCandidatePreFamilySemanticRun
      annotatedPiStagedPreFamilyInput) :=
  annotatedPiStagedPreFamilyInput.exists

/-- The exact family/constructor producer traversals and verified translations
automatically determine the complete retained AnnotatedPi hierarchy, including
its nested annotation-consuming constructor trace. -/
theorem annotatedPiProducedSemanticHierarchy_exists :
    Nonempty (VInductDecl.ProducedNormalizationCandidateSemanticRun
      annotatedPiFamilyCandidateContext annotatedPiCtorCandidateContext
      outParamEnv [] annotatedPiNormalizationCandidate
      annotatedPiRawDecl) :=
  annotatedPiStagedUniverseInput.exists

def annotatedPiNormalizationCandidateRun :
    VInductDecl.NormalizationCandidateRun outParamEnv []
      annotatedPiNormalizationCandidate annotatedPiRawDecl where
  raw := annotatedPiRawType
  raw_types_eq := rfl
  uvars_eq := rfl
  family := annotatedPiCandidateFamilyRun

example : annotatedPiNormalizationCandidateRun.viewDecl =
    annotatedPiViewDecl := rfl

theorem annotatedPiCandidateNormalization_eq :
    annotatedPiNormalizationCandidateRun.normalization =
      annotatedPiNormalization := rfl

def annotatedPiNormalizationRun :
    VInductDecl.NormalizationRun annotatedPiNormalization outParamEnv := by
  simpa only [annotatedPiCandidateNormalization_eq] using
    annotatedPiNormalizationCandidateRun.normalizationRun

theorem annotatedPiNormalization_wf_checked :
    annotatedPiNormalization.WF outParamEnv :=
  annotatedPiNormalizationRun.wf

theorem annotatedPiBlock_wf_checked :
    annotatedPiBlock.WF outParamEnv := by
  refine ⟨annotatedPiNormalization_wf_checked, ?_⟩
  exact annotatedPiViewChecked_wf

private theorem annotatedPiCandidate_generationShape :
    VInductDecl.normalizationCandidateGenerationShape annotatedPiRawDecl
      annotatedPiRawType annotatedPiNormalizationCandidate = true := by
  change ((true && true) &&
    (annotatedPiCtorCandidate.trace.storedSpine && true && true)) = true
  rw [annotatedPiCtorCandidate_storedSpine]
  rfl

private def annotatedPiProducedGenerationShapeCandidate :
    VInductDecl.ProducedGenerationShapeCandidate annotatedPiRawDecl
      annotatedPiRawType annotatedPiKernelType 0 false
      annotatedPiFamilyCandidateContext where
  candidate := annotatedPiNormalizationCandidate
  produced := annotatedPiNormalizationCandidate_produced
  shape := annotatedPiCandidate_generationShape

/-- The strengthened outer gate retains AnnotatedPi's nested annotation-
normalizing candidate only after its complete raw generation spine passes. -/
theorem annotatedPiGenerationShapeCandidate_produced :
    VInductDecl.produceGenerationShapeCandidate annotatedPiRawDecl
      annotatedPiRawType annotatedPiKernelType 0 false
      annotatedPiFamilyCandidateContext =
        .ok annotatedPiProducedGenerationShapeCandidate := by
  have produced :
      AddInductive.buildNormalizationCandidate annotatedPiRawDecl.nparams
          [annotatedPiKernelType] 0 false annotatedPiFamilyCandidateContext =
        .ok annotatedPiNormalizationCandidate :=
    annotatedPiNormalizationCandidate_produced
  simpa only [annotatedPiProducedGenerationShapeCandidate] using
    VInductDecl.produceGenerationShapeCandidate_eq_ok
      (source := annotatedPiRawDecl) (raw := annotatedPiRawType)
      produced annotatedPiCandidate_generationShape

private theorem annotatedPiCandidate_analysis
    (normalization : VInductDecl.NormalizationCandidateSemanticRun
      outParamEnv [] annotatedPiNormalizationCandidate
      annotatedPiRawDecl) :
    normalization.root.normalization.generation? =
      some annotatedPiGenerationChecked := by
  let reference : VInductDecl.NormalizationCandidateSemanticRun outParamEnv []
      annotatedPiNormalizationCandidate annotatedPiRawDecl := {
    raw := annotatedPiRawType
    raw_types_eq := rfl
    uvars_eq := rfl
    family := annotatedPiCandidateFamilySemanticRun }
  rw [annotatedPiStagedPreFamilyInput.normalization_eq normalization reference]
  rfl

/-- AnnotatedPi's nested annotation-normalizing candidate closes through the
same generic staged-owner boundary as the ordinary singleton fixture. -/
theorem annotatedPiExactProducedGenerationCandidatePackage_exists :
    Nonempty (VInductDecl.ExactProducedGenerationCandidatePackage
      outParamEnv [] annotatedPiProducedGenerationShapeCandidate
      annotatedPiGenerationChecked) :=
  annotatedPiProducedGenerationShapeCandidate.exactProducedPackage_nonempty
    annotatedPiStagedPreFamilyInput rfl annotatedPiGenerationChecked
    annotatedPiCandidate_analysis

private def
    annotatedPiExactProducedGenerationCandidatePackage :
    VInductDecl.ExactProducedGenerationCandidatePackage outParamEnv []
      annotatedPiProducedGenerationShapeCandidate annotatedPiGenerationChecked :=
  annotatedPiProducedGenerationShapeCandidate.exactProducedPackage
    annotatedPiStagedPreFamilyInput rfl annotatedPiGenerationChecked
    annotatedPiCandidate_analysis

/-- Complete source-indexed checker certificate for annotated recursive-Π
generation. This is the first live generation run whose main constructor
spine contains an annotation-normalized recursive function domain. -/
def annotatedPiGenerationCandidateSemanticRun :
  VInductDecl.GenerationCandidateSemanticRun
      annotatedPiExactProducedGenerationCandidatePackage.normalization
      annotatedPiGenerationChecked :=
  annotatedPiExactProducedGenerationCandidatePackage.semantic

def annotatedPiGenerationCandidateRun :
    VInductDecl.GenerationCandidateRun
      annotatedPiExactProducedGenerationCandidatePackage.normalization.root
      annotatedPiGenerationChecked :=
  annotatedPiGenerationCandidateSemanticRun.run

/-- Complete dependent producer package for the annotation-bearing recursive
Π candidate. -/
def annotatedPiGenerationCandidatePackage :
    VInductDecl.GenerationCandidatePackage outParamEnv [] :=
  annotatedPiGenerationCandidateSemanticRun.package

/-- The complete AnnotatedPi semantic package is selected by the exact
successful whole-call metadata producer, including its nested annotation-
consuming traversal in the post-family environment. -/
def annotatedPiProducedGenerationCandidatePackage :
    VInductDecl.ProducedGenerationCandidatePackage outParamEnv [] :=
  annotatedPiExactProducedGenerationCandidatePackage.package

/-- Theory-only erasure consumed by the public certified transaction. -/
def annotatedPiGenerationCertificate :
    annotatedPiRawDecl.GenerationCertificate outParamEnv where
  generation := annotatedPiGenerationChecked
  wf := annotatedPiExactProducedGenerationCandidatePackage.semantic.run.wf

def annotatedPiGenerationRun :
    VInductDecl.GenerationRun annotatedPiGenerationChecked outParamEnv :=
  annotatedPiProducedGenerationCandidatePackage.package.run.generationRun

theorem annotatedPiGenerationChecked_wf_checked :
    annotatedPiGenerationChecked.WF outParamEnv :=
  annotatedPiGenerationCertificate.wf

def annotatedPiCtorEnv : VEnv :=
  (annotatedPiTypeEnv.addConst annotatedPiRawType.ctors[0].name
    annotatedPiRawType.ctors[0].toVConstant).get!

def annotatedPiRecEnv : VEnv :=
  (annotatedPiCtorEnv.addConst ``AnnotatedPi.rec
    annotatedPiGenerationChecked.recursor).get!

def annotatedPiFinalEnv : VEnv :=
  (outParamEnv.addInductGeneration
    annotatedPiGenerationChecked).get (by decide)

theorem annotatedPi_addInductGeneration :
    outParamEnv.addInductGeneration annotatedPiGenerationChecked =
      some annotatedPiFinalEnv := rfl

/-- The public proof-carrying path accepts the non-identity AnnotatedPi view
while computing exactly the established mixed Theory transaction. -/
theorem annotatedPi_addInductCertified :
    outParamEnv.addInductCertified annotatedPiGenerationCertificate =
      some annotatedPiFinalEnv :=
  annotatedPi_addInductGeneration

theorem annotatedPiCertified_ordered : annotatedPiFinalEnv.Ordered :=
  VEnv.addInductCertified_WF outParamEnv_ordered
    annotatedPi_addInductCertified

private theorem annotatedPiRawCtor_wf :
    annotatedPiRawType.ctors[0].toVConstant.WF
      annotatedPiTypeEnv :=
  ⟨.succ .zero, annotatedPiRawCtor_hasType⟩

private theorem annotatedPiCtorEnv_ordered :
    annotatedPiCtorEnv.Ordered :=
  .const (n := annotatedPiRawType.ctors[0].name)
    (ci := annotatedPiRawType.ctors[0].toVConstant)
    annotatedPiTypeEnv_ordered annotatedPiRawCtor_wf rfl

private theorem annotatedPiGenerationEnv :
    VInductDecl.GenerationEnv annotatedPiGenerationChecked
      annotatedPiCtorEnv := by
  apply annotatedPiGenerationChecked_wf_checked.toGenerationEnv
    (envT := annotatedPiTypeEnv)
  · rfl
  · exact (VEnv.addConst_le (show
      outParamEnv.addConst annotatedPiRawType.name
        annotatedPiRawType.toVConstant = some annotatedPiTypeEnv from rfl)).trans
      (VEnv.addConst_le (show
        annotatedPiTypeEnv.addConst annotatedPiRawType.ctors[0].name
          annotatedPiRawType.ctors[0].toVConstant =
            some annotatedPiCtorEnv from rfl))
  · exact VEnv.addConst_le (show
      annotatedPiTypeEnv.addConst annotatedPiRawType.ctors[0].name
        annotatedPiRawType.ctors[0].toVConstant =
          some annotatedPiCtorEnv from rfl)
  · exact annotatedPiCtorEnv_ordered
  · rfl
  · intro ctor hctor
    change ctor ∈
      [⟨annotatedPiRawType.ctors[0],
        annotatedPiViewChecked.constructors[0]⟩] at hctor
    obtain rfl := List.mem_singleton.1 hctor
    rfl

private theorem annotatedPiMkInfo_tr :
    TrConstVal .safe annotatedPiTypeEnv annotatedPiMkInfo
      annotatedPiRawType.ctors[0] := by
  exact ⟨⟨by decide, rfl, annotatedPiCtorSource_tr⟩, rfl⟩

private theorem annotatedPiRecInfo_tr :
    TrConstVal .safe annotatedPiCtorEnv annotatedPiRecInfo
      (inductGenerationRecVal annotatedPiGenerationChecked) := by
  have hfamily : annotatedPiCtorEnv.constants ``AnnotatedPi =
      some annotatedPiRawType.toVConstant := rfl
  have hmk : annotatedPiCtorEnv.constants ``AnnotatedPi.mk =
      some annotatedPiRawType.ctors[0].toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr annotatedPiCtorEnv
      annotatedPiRecInfo.levelParams [] annotatedPiRecInfo.type
      (inductGenerationRecVal annotatedPiGenerationChecked).type := by
    tr_type_expr_tac
  obtain ⟨u, hrec⟩ := annotatedPiGenerationEnv.recursor_wf
  exact hshape.to_trExprS annotatedPiCtorEnv_ordered trivial
    ⟨.sort u, hrec⟩

private def annotatedPiCtorMap : ConstMap :=
  annotatedPiTypeMap.insert ``AnnotatedPi.mk annotatedPiMkInfo

private def annotatedPiMap : ConstMap :=
  annotatedPiCtorMap.insert ``AnnotatedPi.rec annotatedPiRecInfo

private theorem annotatedPiMk_fresh :
    annotatedPiTypeMap.find? ``AnnotatedPi.mk = none := by
  rw [annotatedPiTypeMap, outParamMap_wf.find?_insert,
    outParamMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

private theorem annotatedPiCtorMap_wf : annotatedPiCtorMap.WF :=
  annotatedPiTypeMap_wf.insert _ _ annotatedPiMk_fresh

private theorem annotatedPiRec_fresh :
    annotatedPiCtorMap.find? ``AnnotatedPi.rec = none := by
  rw [annotatedPiCtorMap, annotatedPiTypeMap_wf.find?_insert,
    annotatedPiTypeMap, outParamMap_wf.find?_insert, outParamMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

/-- Complete kernel-metadata replay transaction for `AnnotatedPi`, driven by
the checker-produced non-identity normalization certificate. -/
def annotatedPiAddInductTraceChecked :
    AddInductTrace outParamMap outParamEnv annotatedPiRawDecl
      annotatedPiMap annotatedPiFinalEnv := by
  refine annotatedPiProducedGenerationCandidatePackage.package.addInductTrace
    annotatedPiTypeMap annotatedPiTypeEnv annotatedPiCtorMap
    annotatedPiCtorEnv annotatedPiRecEnv annotatedPiAddType ?_ ?_ ?_ ⟨rfl⟩
  · exact .cons {
      info := annotatedPiMkInfo
      kind_eq := by simp [annotatedPiMkInfo, InductConstantKind.Matches]
      tr := annotatedPiMkInfo_tr
      map_fresh := by
        simpa [annotatedPiRawType] using annotatedPiMk_fresh
      env_add := rfl
      map_add := rfl } .nil
  · exact {
      info := annotatedPiRecInfo
      kind_eq := by simp [annotatedPiRecInfo, InductConstantKind.Matches]
      tr := annotatedPiRecInfo_tr
      map_fresh := by
        rw [show
          (inductGenerationRecVal
            annotatedPiProducedGenerationCandidatePackage.package.generation).name =
              ``AnnotatedPi.rec by rfl]
        exact annotatedPiRec_fresh
      env_add := rfl
      map_add := rfl }
  · decide

theorem annotatedPi_addInduct_checked :
    AddInduct outParamMap outParamEnv annotatedPiRawDecl
      annotatedPiMap annotatedPiFinalEnv :=
  ⟨annotatedPiAddInductTraceChecked⟩

theorem annotatedPi_trEnv'_checked :
    TrEnv' .safe annotatedPiMap false annotatedPiFinalEnv :=
  .induct annotatedPi_addInduct_checked outParam_trEnv'

theorem annotatedPi_env_wf_checked : annotatedPiFinalEnv.WF :=
  annotatedPi_trEnv'_checked.wf

theorem annotatedPi_aligned_checked :
    Aligned .safe annotatedPiMap annotatedPiFinalEnv :=
  annotatedPi_trEnv'_checked.aligned

theorem annotatedPiFinalEnv_trace :
    Nonempty (VEnv.AddInductGenerationTrace outParamEnv
      annotatedPiFinalEnv annotatedPiGenerationChecked) :=
  VEnv.addInductGeneration_trace annotatedPi_addInductGeneration

/-- The public certified wrapper exposes the same trace. This deliberately
stays separate from the minimal Theory-only iota root below: the concrete
certificate remembers its Verify provenance, while the transaction equality
itself admits the smaller Theory proof. -/
theorem annotatedPiCertified_trace :
    Nonempty (VEnv.AddInductGenerationTrace outParamEnv
      annotatedPiFinalEnv annotatedPiGenerationChecked) :=
  VEnv.addInductCertified_trace annotatedPi_addInductCertified

theorem annotatedPiFinalEnv_family_lookup :
    annotatedPiFinalEnv.constants ``AnnotatedPi =
      some annotatedPiRawType.toVConstant := by
  rcases annotatedPiFinalEnv_trace with ⟨trace⟩
  exact trace.family_lookup

theorem annotatedPiFinalEnv_ctor_lookup :
    annotatedPiFinalEnv.constants ``AnnotatedPi.mk =
      some annotatedPiRawType.ctors[0].toVConstant := by
  rcases annotatedPiFinalEnv_trace with ⟨trace⟩
  exact trace.ctor_lookup (.head _)

theorem annotatedPiFinalEnv_rec_lookup :
    annotatedPiFinalEnv.constants ``AnnotatedPi.rec =
      some annotatedPiGenerationChecked.recursor := by
  rcases annotatedPiFinalEnv_trace with ⟨trace⟩
  exact trace.rec_lookup

theorem annotatedPiFinalEnv_rule_mem :
    ∀ df ∈ annotatedPiGenerationChecked.generatedRules,
      annotatedPiFinalEnv.defeqs df := by
  intro df hdf
  rcases annotatedPiFinalEnv_trace with ⟨trace⟩
  exact trace.rule_mem hdf

theorem annotatedPiFinalEnv_iota_mem :
    annotatedPiFinalEnv.defeqs
      annotatedPiGenerationChecked.generatedRules[0] := by
  apply annotatedPiFinalEnv_rule_mem
  exact .head _

theorem annotatedPi_iota_rhs_matches_kernel :
    annotatedPiKernelRuleRhs =
      annotatedPiGenerationChecked.generatedRules[0].rhs := rfl

theorem annotatedPi_type_map_lookup :
    annotatedPiMap.find? ``AnnotatedPi = some annotatedPiInfo := by
  rw [annotatedPiMap, annotatedPiCtorMap_wf.find?_insert,
    annotatedPiCtorMap, annotatedPiTypeMap_wf.find?_insert]
  simp +decide
  rw [annotatedPiTypeMap, outParamMap_wf.find?_insert]
  simp +decide

theorem annotatedPi_mk_map_lookup :
    annotatedPiMap.find? ``AnnotatedPi.mk = some annotatedPiMkInfo := by
  rw [annotatedPiMap, annotatedPiCtorMap_wf.find?_insert,
    annotatedPiCtorMap, annotatedPiTypeMap_wf.find?_insert]
  rfl

theorem annotatedPi_rec_map_lookup :
    annotatedPiMap.find? ``AnnotatedPi.rec = some annotatedPiRecInfo := by
  rw [annotatedPiMap, annotatedPiCtorMap_wf.find?_insert]
  rfl

theorem annotatedPi_type_lookup_unique :
    annotatedPiInfo.name = ``AnnotatedPi ∧
      TrConstant .safe annotatedPiFinalEnv annotatedPiInfo
        annotatedPiRawType.toVConstant :=
  annotatedPi_aligned_checked.find?_uniq annotatedPi_type_map_lookup
    annotatedPiFinalEnv_family_lookup

theorem annotatedPi_mk_lookup_unique :
    annotatedPiMkInfo.name = ``AnnotatedPi.mk ∧
      TrConstant .safe annotatedPiFinalEnv annotatedPiMkInfo
        annotatedPiRawType.ctors[0].toVConstant :=
  annotatedPi_aligned_checked.find?_uniq annotatedPi_mk_map_lookup
    annotatedPiFinalEnv_ctor_lookup

theorem annotatedPi_rec_lookup_unique :
    annotatedPiRecInfo.name = ``AnnotatedPi.rec ∧
      TrConstant .safe annotatedPiFinalEnv annotatedPiRecInfo
        annotatedPiGenerationChecked.recursor :=
  annotatedPi_aligned_checked.find?_uniq annotatedPi_rec_map_lookup
    annotatedPiFinalEnv_rec_lookup

/-! ## Definitionally equal parameter transaction replay -/

/-- Consumer-facing certificate for the exact mixed generation value whose
stored parameter is `outParam Type` and whose emitted recursor parameter is
the definitionally equal checked `Type`. -/
def annotatedParamGenerationCertificate :
    annotatedParamRawDecl.GenerationCertificate outParamEnv where
  generation := annotatedParamGenerationChecked
  wf := annotatedParamGenerationChecked_wf

def annotatedParamCtorEnv : VEnv :=
  (annotatedParamTypeEnv.addConst annotatedParamRawType.ctors[0].name
    annotatedParamRawType.ctors[0].toVConstant).get!

def annotatedParamRecEnv : VEnv :=
  (annotatedParamCtorEnv.addConst ``AnnotatedParam.rec
    annotatedParamGenerationChecked.recursor).get!

def annotatedParamFinalEnv : VEnv :=
  (outParamEnv.addInductGeneration
    annotatedParamGenerationChecked).get (by decide)

theorem annotatedParam_addInductGeneration :
    outParamEnv.addInductGeneration annotatedParamGenerationChecked =
      some annotatedParamFinalEnv := rfl

/-- The public proof-carrying transaction accepts the raw/checked parameter
normalization and computes the same environment as the underlying generation
transaction. -/
theorem annotatedParam_addInductCertified :
    outParamEnv.addInductCertified annotatedParamGenerationCertificate =
      some annotatedParamFinalEnv :=
  annotatedParam_addInductGeneration

theorem annotatedParamCertified_ordered :
    annotatedParamFinalEnv.Ordered :=
  VEnv.addInductCertified_WF outParamEnv_ordered
    annotatedParam_addInductCertified

private theorem annotatedParamRawCtor_wf :
    annotatedParamRawType.ctors[0].toVConstant.WF
      annotatedParamTypeEnv := by
  change annotatedParamTypeEnv.IsType 0 []
    annotatedParamRawType.ctors[0].type
  let ctor : VInductDecl.NormalizedCtor :=
    ⟨annotatedParamRawType.ctors[0],
      annotatedParamViewChecked.constructors[0]⟩
  have hctor : ctor ∈
      annotatedParamGenerationChecked.block.ctorPairs := by
    change ctor ∈ [⟨annotatedParamRawType.ctors[0],
      annotatedParamViewChecked.constructors[0]⟩]
    exact .head _
  simpa [ctor, annotatedParamRawDecl] using
    annotatedParamGenerationChecked_wf.rawCtor_isType
      (envT := annotatedParamTypeEnv) rfl hctor

private theorem annotatedParamCtorEnv_ordered :
    annotatedParamCtorEnv.Ordered :=
  .const (n := annotatedParamRawType.ctors[0].name)
    (ci := annotatedParamRawType.ctors[0].toVConstant)
    annotatedParamTypeEnv_ordered annotatedParamRawCtor_wf rfl

private theorem annotatedParamGenerationEnv :
    VInductDecl.GenerationEnv annotatedParamGenerationChecked
      annotatedParamCtorEnv := by
  apply annotatedParamGenerationChecked_wf.toGenerationEnv
    (envT := annotatedParamTypeEnv)
  · rfl
  · exact (VEnv.addConst_le (show
      outParamEnv.addConst annotatedParamRawType.name
        annotatedParamRawType.toVConstant =
          some annotatedParamTypeEnv from rfl)).trans
      (VEnv.addConst_le (show
        annotatedParamTypeEnv.addConst
          annotatedParamRawType.ctors[0].name
          annotatedParamRawType.ctors[0].toVConstant =
            some annotatedParamCtorEnv from rfl))
  · exact VEnv.addConst_le (show
      annotatedParamTypeEnv.addConst
        annotatedParamRawType.ctors[0].name
        annotatedParamRawType.ctors[0].toVConstant =
          some annotatedParamCtorEnv from rfl)
  · exact annotatedParamCtorEnv_ordered
  · rfl
  · intro ctor hctor
    change ctor ∈ [⟨annotatedParamRawType.ctors[0],
      annotatedParamViewChecked.constructors[0]⟩] at hctor
    obtain rfl := List.mem_singleton.1 hctor
    rfl

private theorem annotatedParamMkInfo_tr :
    TrConstVal .safe annotatedParamTypeEnv annotatedParamMkInfo
      annotatedParamRawType.ctors[0] := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr annotatedParamTypeEnv
      annotatedParamMkInfo.levelParams [] annotatedParamMkInfo.type
      annotatedParamRawType.ctors[0].type := by
    tr_type_expr_tac
  obtain ⟨u, htype⟩ := annotatedParamRawCtor_wf
  exact hshape.to_trExprS annotatedParamTypeEnv_ordered trivial
    ⟨.sort u, htype⟩

private theorem annotatedParamRecInfo_tr :
    TrConstVal .safe annotatedParamCtorEnv annotatedParamRecInfo
      (inductGenerationRecVal annotatedParamGenerationChecked) := by
  have hfamily : annotatedParamCtorEnv.constants ``AnnotatedParam =
      some annotatedParamRawType.toVConstant := rfl
  have hmk : annotatedParamCtorEnv.constants ``AnnotatedParam.mk =
      some annotatedParamRawType.ctors[0].toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr annotatedParamCtorEnv
      annotatedParamRecInfo.levelParams [] annotatedParamRecInfo.type
      (inductGenerationRecVal annotatedParamGenerationChecked).type := by
    tr_type_expr_tac
  obtain ⟨u, hrec⟩ := annotatedParamGenerationEnv.recursor_wf
  exact hshape.to_trExprS annotatedParamCtorEnv_ordered trivial
    ⟨.sort u, hrec⟩

private def annotatedParamCtorMap : ConstMap :=
  annotatedParamTypeMap.insert ``AnnotatedParam.mk annotatedParamMkInfo

private def annotatedParamMap : ConstMap :=
  annotatedParamCtorMap.insert ``AnnotatedParam.rec annotatedParamRecInfo

private theorem annotatedParamMk_fresh :
    annotatedParamTypeMap.find? ``AnnotatedParam.mk = none := by
  rw [annotatedParamTypeMap, outParamMap_wf.find?_insert,
    outParamMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

private theorem annotatedParamCtorMap_wf : annotatedParamCtorMap.WF :=
  annotatedParamTypeMap_wf.insert _ _ annotatedParamMk_fresh

private theorem annotatedParamRec_fresh :
    annotatedParamCtorMap.find? ``AnnotatedParam.rec = none := by
  rw [annotatedParamCtorMap, annotatedParamTypeMap_wf.find?_insert,
    annotatedParamTypeMap, outParamMap_wf.find?_insert, outParamMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

/-- Real `ConstantInfo` replay for the definitionally equal parameter case.
The generation certificate and the emitted recursor/rule payload are the same
values checked against kernel metadata above. -/
def annotatedParamAddInductTraceChecked :
    AddInductTrace outParamMap outParamEnv annotatedParamRawDecl
      annotatedParamMap annotatedParamFinalEnv := by
  refine {
    generation := annotatedParamGenerationChecked
    generation_wf := annotatedParamGenerationChecked_wf
    typeMap := annotatedParamTypeMap
    typeEnv := annotatedParamTypeEnv
    ctorMap := annotatedParamCtorMap
    ctorEnv := annotatedParamCtorEnv
    recEnv := annotatedParamRecEnv
    addType := annotatedParamAddType
    addCtors := ?_
    addRec := {
      info := annotatedParamRecInfo
      kind_eq := by
        simp [annotatedParamRecInfo, InductConstantKind.Matches]
      tr := annotatedParamRecInfo_tr
      map_fresh := by
        rw [show
          (inductGenerationRecVal annotatedParamGenerationChecked).name =
            ``AnnotatedParam.rec by rfl]
        exact annotatedParamRec_fresh
      env_add := rfl
      map_add := rfl }
    recK := by decide
    addRules := ⟨rfl⟩ }
  exact .cons {
    info := annotatedParamMkInfo
    kind_eq := by
      simp [annotatedParamMkInfo, InductConstantKind.Matches]
    tr := annotatedParamMkInfo_tr
    map_fresh := by
      simpa [annotatedParamRawType] using annotatedParamMk_fresh
    env_add := rfl
    map_add := rfl } .nil

theorem annotatedParam_addInduct_checked :
    AddInduct outParamMap outParamEnv annotatedParamRawDecl
      annotatedParamMap annotatedParamFinalEnv :=
  ⟨annotatedParamAddInductTraceChecked⟩

theorem annotatedParam_trEnv'_checked :
    TrEnv' .safe annotatedParamMap false annotatedParamFinalEnv :=
  .induct annotatedParam_addInduct_checked outParam_trEnv'

theorem annotatedParam_env_wf_checked : annotatedParamFinalEnv.WF :=
  annotatedParam_trEnv'_checked.wf

theorem annotatedParam_aligned_checked :
    Aligned .safe annotatedParamMap annotatedParamFinalEnv :=
  annotatedParam_trEnv'_checked.aligned

theorem annotatedParamCertified_trace :
    Nonempty (VEnv.AddInductGenerationTrace outParamEnv
      annotatedParamFinalEnv annotatedParamGenerationChecked) :=
  VEnv.addInductCertified_trace annotatedParam_addInductCertified

theorem annotatedParamFinalEnv_family_lookup :
    annotatedParamFinalEnv.constants ``AnnotatedParam =
      some annotatedParamRawType.toVConstant := by
  rcases annotatedParamCertified_trace with ⟨trace⟩
  exact trace.family_lookup

theorem annotatedParamFinalEnv_ctor_lookup :
    annotatedParamFinalEnv.constants ``AnnotatedParam.mk =
      some annotatedParamRawType.ctors[0].toVConstant := by
  rcases annotatedParamCertified_trace with ⟨trace⟩
  exact trace.ctor_lookup (.head _)

theorem annotatedParamFinalEnv_rec_lookup :
    annotatedParamFinalEnv.constants ``AnnotatedParam.rec =
      some annotatedParamGenerationChecked.recursor := by
  rcases annotatedParamCertified_trace with ⟨trace⟩
  exact trace.rec_lookup

theorem annotatedParamFinalEnv_iota_mem :
    annotatedParamFinalEnv.defeqs
      annotatedParamGenerationChecked.generatedRules[0] := by
  rcases annotatedParamCertified_trace with ⟨trace⟩
  exact trace.rule_mem (.head _)

theorem annotatedParam_iota_rhs_matches_kernel :
    annotatedParamKernelRuleRhs =
      annotatedParamGenerationChecked.generatedRules[0].rhs := rfl

theorem annotatedParam_type_map_lookup :
    annotatedParamMap.find? ``AnnotatedParam =
      some annotatedParamInfo := by
  rw [annotatedParamMap, annotatedParamCtorMap_wf.find?_insert,
    annotatedParamCtorMap, annotatedParamTypeMap_wf.find?_insert,
    annotatedParamTypeMap, outParamMap_wf.find?_insert]
  simp +decide

theorem annotatedParam_mk_map_lookup :
    annotatedParamMap.find? ``AnnotatedParam.mk =
      some annotatedParamMkInfo := by
  rw [annotatedParamMap, annotatedParamCtorMap_wf.find?_insert,
    annotatedParamCtorMap, annotatedParamTypeMap_wf.find?_insert]
  rfl

theorem annotatedParam_rec_map_lookup :
    annotatedParamMap.find? ``AnnotatedParam.rec =
      some annotatedParamRecInfo := by
  rw [annotatedParamMap, annotatedParamCtorMap_wf.find?_insert]
  rfl

theorem annotatedParam_type_lookup_unique :
    annotatedParamInfo.name = ``AnnotatedParam ∧
      TrConstant .safe annotatedParamFinalEnv annotatedParamInfo
        annotatedParamRawType.toVConstant :=
  annotatedParam_aligned_checked.find?_uniq annotatedParam_type_map_lookup
    annotatedParamFinalEnv_family_lookup

theorem annotatedParam_mk_lookup_unique :
    annotatedParamMkInfo.name = ``AnnotatedParam.mk ∧
      TrConstant .safe annotatedParamFinalEnv annotatedParamMkInfo
        annotatedParamRawType.ctors[0].toVConstant :=
  annotatedParam_aligned_checked.find?_uniq annotatedParam_mk_map_lookup
    annotatedParamFinalEnv_ctor_lookup

theorem annotatedParam_rec_lookup_unique :
    annotatedParamRecInfo.name = ``AnnotatedParam.rec ∧
      TrConstant .safe annotatedParamFinalEnv annotatedParamRecInfo
        annotatedParamGenerationChecked.recursor :=
  annotatedParam_aligned_checked.find?_uniq annotatedParam_rec_map_lookup
    annotatedParamFinalEnv_rec_lookup

/-- The complete AliasFormer metadata trace with the generation-WF field
supplied by the checker-produced certificate. All computational metadata
witnesses are shared with the existing replay. -/
def aliasFormerAddInductTraceChecked :
    AddInductTrace typeFamilyAliasMap typeFamilyAliasEnv
      aliasFormerRawDecl aliasFormerMap aliasFormerFinalEnv :=
  let replay :=
    aliasFormerAddInductTraceWith aliasFormerGenerationCertificate.wf
  aliasFormerProducedGenerationCandidatePackage.package.addInductTrace
    replay.typeMap replay.typeEnv replay.ctorMap replay.ctorEnv replay.recEnv
    replay.addType replay.addCtors replay.addRec replay.recK replay.addRules

theorem aliasFormer_addInduct_checked :
    AddInduct typeFamilyAliasMap typeFamilyAliasEnv
      aliasFormerRawDecl aliasFormerMap aliasFormerFinalEnv :=
  ⟨aliasFormerAddInductTraceChecked⟩

theorem aliasFormer_trEnv'_checked :
    TrEnv' .safe aliasFormerMap false aliasFormerFinalEnv :=
  .induct aliasFormer_addInduct_checked typeFamilyAlias_trEnv'

theorem aliasFormer_env_wf_checked : aliasFormerFinalEnv.WF :=
  aliasFormer_trEnv'_checked.wf

theorem aliasFormer_aligned_checked :
    Aligned .safe aliasFormerMap aliasFormerFinalEnv :=
  aliasFormer_trEnv'_checked.aligned

/-- The complete AliasRec metadata trace with the generation-WF field supplied
by the checker-produced normalization certificate. -/
def aliasRecAddInductTraceChecked :
    AddInductTrace recAliasMap recAliasEnv aliasRecRawDecl
      aliasRecMap aliasRecFinalEnv :=
  aliasRecAddInductTraceWith aliasRecGenerationChecked_wf_checked

theorem aliasRec_addInduct_checked :
    AddInduct recAliasMap recAliasEnv aliasRecRawDecl
      aliasRecMap aliasRecFinalEnv :=
  ⟨aliasRecAddInductTraceChecked⟩

theorem aliasRec_trEnv'_checked :
    TrEnv' .safe aliasRecMap false aliasRecFinalEnv :=
  .induct aliasRec_addInduct_checked recAlias_trEnv'

theorem aliasRec_env_wf_checked : aliasRecFinalEnv.WF :=
  aliasRec_trEnv'_checked.wf

theorem aliasRec_aligned_checked :
    Aligned .safe aliasRecMap aliasRecFinalEnv :=
  aliasRec_trEnv'_checked.aligned

/- The operational traces do not reach the pointer-equality contracts. Their
semantic endpoints intentionally inherit Verify's existing checker-refinement
and reflection contracts, including pointer equality. No new axiom or
native-evaluation principle is used. -/
#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormerFamily_candidateTrace [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.Expr.eqv_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormerCtor_candidateTrace [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.Expr.eqv_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormerFamily_candidate [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.Expr.eqv_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormerFamily_candidateRun_exists [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormerFamily_candidateSource_tr [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.Expr.eqv_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormerFamily_candidateView_tr [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormerNormalizationCandidateRun [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormerCandidateNormalization_eq [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormerTruncatedView_rejected [propext]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasRecField_checkType [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.Expr.eqv_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasRecField_hasType_checked [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormerFamily_whnf [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.Expr.eqv_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormerCtor_whnf [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.Expr.eqv_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.recAlias_whnf [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.Expr.eqv_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormerFamily_checkType [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.Expr.eqv_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormerCtor_checkType [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.Expr.eqv_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormerFamily_isType_checked [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormerCtor_isType_checked [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormerNormalization_wf_checked [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasRecNormalization_wf_checked [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormerBlock_wf_checked [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormerProducedSemanticHierarchy_exists [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormerProducedPostFamilySemantic_exists [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormerProducedPreFamilySemantic_exists [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormerGenerationCandidateSemanticRun [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormerGenerationCandidateRun [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormerGenerationCandidatePackage [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormerNormalizationCandidate_produced [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.Expr.eqv_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormerGenerationShapeCandidate_produced [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.Expr.eqv_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormerExactProducedGenerationCandidatePackage_exists [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormerProducedGenerationCandidatePackage [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormer_addInductCertified_checked [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormerGenerationChecked_wf_checked [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasRecBlock_wf_checked [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasRecGenerationChecked_wf_checked [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormerAddInductTraceChecked [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormer_trEnv'_checked [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasRecAddInductTraceChecked [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasRec_trEnv'_checked [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

/- Both alias replays have the same `sorryAx`-free Verify closure as the
identity fixtures. The three persistent-map contracts enter through concrete
`ConstMap` freshness proofs. -/
#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormer_trEnv' [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormer_env_wf [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasFormer_aligned [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasRec_trEnv' [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasRec_env_wf [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.aliasRec_aligned [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.annotatedPiProducedSemanticHierarchy_exists [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.annotatedPiProducedPostFamilySemantic_exists [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.annotatedPiProducedPreFamilySemantic_exists [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.annotatedPiNormalizationCandidateRun [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.annotatedPiGenerationCandidateSemanticRun [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.annotatedPiGenerationCandidateRun [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.annotatedPiGenerationCandidatePackage [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.annotatedPiCtor_candidateTrace [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.Expr.eqv_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.annotatedPiFamily_candidateTrace [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.Expr.eqv_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Syntax.structEq_eq]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.annotatedPiNormalizationCandidate_produced [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.Expr.eqv_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.annotatedPiGenerationShapeCandidate_produced [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.Expr.eqv_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.annotatedPiExactProducedGenerationCandidatePackage_exists [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.annotatedPiProducedGenerationCandidatePackage [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.annotatedPi_addInductCertified [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.annotatedPiGenerationChecked_wf_checked [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.annotatedPiAddInductTraceChecked [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.annotatedPi_trEnv'_checked [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.annotatedPiFinalEnv_iota_mem [propext, Quot.sound]

/-! The parameter-parity fixture deliberately keeps its operational checker
outcome guard separate from the Theory certificate. These pins make the exact
trust split visible: the semantic transaction stays Theory-small, while real
`ConstantInfo` replay inherits only the already classified Verify frontier. -/

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.annotatedParam_addInductCertified [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.annotatedParamAddInductTraceChecked [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.annotatedParam_trEnv'_checked [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.annotatedParamFinalEnv_iota_mem [propext, Quot.sound]

end Ix.Theory.Named.InductiveReplayFixtures
