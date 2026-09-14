/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.NestedInductive
import Ix.Theory.Named.Typing.InductiveLemmas

/-!
# Nested transaction facts and preservation

The `addInductNested` analog of the block-wide transaction lemma suite:
exact phase recovery, atomicity, monotonicity, freshness, lookup and rule
membership through `ctorFold_spec`/`rulesFold_spec`, and `Ordered`
preservation from the `NestedBlockChecked.WF` package.
-/

namespace Ix.Theory.Named

open VInductDecl

namespace VEnv

/-- Recover every phase boundary from a successful nested transaction. -/
theorem addInductNested_trace {source : VInductDecl}
    {nested : source.NestedBlockChecked}
    (hadd : addInductNested env nested = some env') :
    Nonempty (AddInductNestedTrace env env' nested) := by
  unfold addInductNested at hadd
  obtain ⟨typeEnv, addTypes, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  obtain ⟨ctorEnv, addCtors, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  obtain ⟨recEnv, addRecs, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  cases hadd
  exact ⟨⟨typeEnv, ctorEnv, recEnv, addTypes, addCtors, addRecs, rfl⟩⟩

/-- The nested transaction is atomic at its public `Option` boundary. -/
theorem addInductNested_atomic {source : VInductDecl}
    (env : VEnv) (nested : source.NestedBlockChecked) :
    addInductNested env nested = none ∨
      ∃ env', addInductNested env nested = some env' ∧
        Nonempty (AddInductNestedTrace env env' nested) := by
  cases hadd : addInductNested env nested with
  | none => exact .inl rfl
  | some env' => exact .inr ⟨env', rfl, addInductNested_trace hadd⟩

namespace AddInductNestedTrace

variable {source : VInductDecl} {nested : source.NestedBlockChecked}

/-- Every phase of a successful nested transaction only grows the Theory
environment. -/
theorem le (H : AddInductNestedTrace env env' nested) : env ≤ env' := by
  have htypes := (ctorFold_spec source.blockTypeConstants H.addTypes).1
  have hctors := (ctorFold_spec source.blockConstructorConstants H.addCtors).1
  have hrecs := (ctorFold_spec nested.recursors H.addRecs).1
  have hrules : H.recEnv ≤ env' := by
    simpa only [H.addRules] using
      (rulesFold_spec nested.generatedRules H.recEnv).1
  exact htypes.trans (hctors.trans (hrecs.trans hrules))

/-- Every source family name was fresh before the transaction. -/
theorem family_fresh (H : AddInductNestedTrace env env' nested)
    {type : VInductiveType} (htype : type ∈ source.types) :
    env.constants type.name = none := by
  have hmem : type.toVConstVal ∈ source.blockTypeConstants :=
    List.mem_map.2 ⟨type, htype, rfl⟩
  simpa [VInductDecl.blockTypeConstants] using
    (ctorFold_spec source.blockTypeConstants H.addTypes).2.2
      type.toVConstVal hmem

/-- The final environment stores every exact source family constant. -/
theorem family_lookup (H : AddInductNestedTrace env env' nested)
    {type : VInductiveType} (htype : type ∈ source.types) :
    env'.constants type.name = some type.toVConstant := by
  have hmem : type.toVConstVal ∈ source.blockTypeConstants :=
    List.mem_map.2 ⟨type, htype, rfl⟩
  have hlookup :=
    (ctorFold_spec source.blockTypeConstants H.addTypes).2.1
      type.toVConstVal hmem
  have hctors := (ctorFold_spec source.blockConstructorConstants H.addCtors).1
  have hrecs := (ctorFold_spec nested.recursors H.addRecs).1
  have hrules : H.recEnv ≤ env' := by
    simpa only [H.addRules] using
      (rulesFold_spec nested.generatedRules H.recEnv).1
  exact (hctors.trans (hrecs.trans hrules)).constants hlookup

/-- Every flattened source constructor name was fresh before the nested
transaction. -/
theorem ctor_fresh (H : AddInductNestedTrace env env' nested)
    {c : VConstVal} (hc : c ∈ source.blockConstructorConstants) :
    env.constants c.name = none := by
  have htypes := (ctorFold_spec source.blockTypeConstants H.addTypes).1
  have hfresh :=
    (ctorFold_spec source.blockConstructorConstants H.addCtors).2.2 c hc
  exact htypes.constants_none hfresh

/-- The final environment stores every exact source constructor
constant. -/
theorem ctor_lookup (H : AddInductNestedTrace env env' nested)
    {type : VInductiveType} (htype : type ∈ source.types)
    {c : VConstVal} (hc : c ∈ type.ctors) :
    env'.constants c.name = some c.toVConstant := by
  have hmem : c ∈ source.blockConstructorConstants :=
    List.mem_flatMap.2 ⟨type, htype, hc⟩
  have hlookup :=
    (ctorFold_spec source.blockConstructorConstants H.addCtors).2.1 c hmem
  have hrecs := (ctorFold_spec nested.recursors H.addRecs).1
  have hrules : H.recEnv ≤ env' := by
    simpa only [H.addRules] using
      (rulesFold_spec nested.generatedRules H.recEnv).1
  exact (hrecs.trans hrules).constants hlookup

/-- The final environment stores every restored recursor constant. -/
theorem rec_lookup (H : AddInductNestedTrace env env' nested)
    {recursor : VConstVal} (hrec : recursor ∈ nested.recursors) :
    env'.constants recursor.name = some recursor.toVConstant := by
  have hlookup := (ctorFold_spec nested.recursors H.addRecs).2.1 recursor hrec
  have hrules : H.recEnv ≤ env' := by
    simpa only [H.addRules] using
      (rulesFold_spec nested.generatedRules H.recEnv).1
  exact hrules.constants hlookup

/-- Every restored recursor name was fresh before the nested transaction. -/
theorem rec_fresh (H : AddInductNestedTrace env env' nested)
    {recursor : VConstVal} (hrec : recursor ∈ nested.recursors) :
    env.constants recursor.name = none := by
  have htypes := (ctorFold_spec source.blockTypeConstants H.addTypes).1
  have hctors :=
    (ctorFold_spec source.blockConstructorConstants H.addCtors).1
  have hfresh := (ctorFold_spec nested.recursors H.addRecs).2.2 recursor hrec
  exact (htypes.trans hctors).constants_none hfresh

/-- The final environment registers every restored rule. -/
theorem rule_mem (H : AddInductNestedTrace env env' nested)
    {df : VDefEq} (hdf : df ∈ nested.generatedRules) :
    env'.defeqs df := by
  simpa only [H.addRules] using
    (rulesFold_spec nested.generatedRules H.recEnv).2 df hdf

end AddInductNestedTrace

nonrec theorem addInductNested_le {source : VInductDecl}
    {nested : source.NestedBlockChecked}
    (hadd : addInductNested env nested = some env') : env ≤ env' := by
  obtain ⟨H⟩ := addInductNested_trace hadd
  exact H.le

end VEnv

/-- A chained constant package folds into `Ordered` preservation. -/
theorem NestedConstsWF.fold_ordered :
    ∀ {cs : List VConstVal} {env env' : VEnv},
      VEnv.Ordered env → NestedConstsWF env cs →
      cs.foldlM (fun env c => env.addConst c.name c.toVConstant) env =
        some env' →
      VEnv.Ordered env'
  | [], _, _, h, _, hf => by cases hf; exact h
  | c :: cs, env, env', h, hwf, hf => by
    rw [List.foldlM_cons] at hf
    obtain ⟨env₁, hadd, htail⟩ := Option.bind_eq_some_iff.1 hf
    exact NestedConstsWF.fold_ordered (.const h hwf.1 hadd)
      (hwf.2 env₁ hadd) htail

/-- A chained rule package folds into `Ordered` preservation. -/
theorem NestedRulesWF.fold_ordered :
    ∀ {dfs : List VDefEq} {env : VEnv},
      VEnv.Ordered env → NestedRulesWF env dfs →
      VEnv.Ordered (dfs.foldl VEnv.addDefEq env)
  | [], _, h, _ => h
  | df :: dfs, env, h, hwf => by
    rw [List.foldl_cons]
    exact NestedRulesWF.fold_ordered (.defeq h hwf.1) hwf.2

/-- `Ordered` preservation for the nested transaction. -/
theorem VEnv.addInductNested_WF {source : VInductDecl}
    {nested : source.NestedBlockChecked}
    (ih : VEnv.Ordered env) (h1 : nested.WF env)
    (h2 : addInductNested env nested = some env') : VEnv.Ordered env' := by
  unfold addInductNested at h2
  obtain ⟨typeEnv, addTypes, h2⟩ := Option.bind_eq_some_iff.1 h2
  obtain ⟨ctorEnv, addCtors, h2⟩ := Option.bind_eq_some_iff.1 h2
  obtain ⟨recEnv, addRecs, h2⟩ := Option.bind_eq_some_iff.1 h2
  cases h2
  have hT := NestedConstsWF.fold_ordered ih h1.types addTypes
  have hC := NestedConstsWF.fold_ordered hT (h1.ctors addTypes) addCtors
  have hR := NestedConstsWF.fold_ordered hC (h1.recs addTypes addCtors) addRecs
  exact NestedRulesWF.fold_ordered hR (h1.rules addTypes addCtors addRecs)

end Ix.Theory.Named
