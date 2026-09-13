/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Compiler
import Ix.Aiur.Proofs.Metadata
import Ix.Aiur.Proofs.Relayout
import Ix.Aiur.Proofs.Dedup
import Std.Data.HashMap.Lemmas

/-! Artifact binding for the actual compilation pipeline. This strengthens
stage existence with equality to the returned artifact. Semantic success
reflection through these stages remains a separate obligation. -/

namespace Aiur

/-- Inlining changes function bodies and retains the selected rank policy. -/
theorem Source.Toplevel.inlineCalls_componentRanks {source inlined : Source.Toplevel}
    (accepted : source.inlineCalls = .ok inlined) :
    inlined.componentRanks = source.componentRanks := by
  unfold Source.Toplevel.inlineCalls at accepted
  simp only [bind, Except.bind, pure, Except.pure] at accepted
  repeat' first
    | split at accepted
    | (dsimp only at accepted; split at accepted)
  all_goals cases accepted
  all_goals rfl

theorem Source.Toplevel.compile_artifact_of_ok
    {source : Source.Toplevel} {compiled : CompiledToplevel}
    (h : source.compile = .ok compiled) :
    ∃ inlined typed concrete raw names,
      source.inlineCalls = .ok inlined ∧
      inlined.checkAndSimplify = .ok typed ∧
      typed.concretize = .ok concrete ∧
      concrete.toBytecode = .ok (raw, names) ∧
      compiled = finishCompilation inlined raw names := by
  obtain ⟨inlined, typed, concrete, raw, names, hi, ht, hc, hb⟩ :=
    source.compile_stages_of_ok h
  refine ⟨inlined, typed, concrete, raw, names, hi, ht, hc, hb, ?_⟩
  simpa only [Source.Toplevel.compile, hi, ht, hc, hb, Except.mapError,
    bind, Except.bind, pure, Except.pure, Except.ok.injEq] using h.symm

/-- Reachability, checked component layouts and partition construction retain
the executable behavior and input arity of the deduplicated program. -/
theorem finishCompilation_sameCode (source : Source.Toplevel) (raw : Bytecode.Toplevel)
    (names : Std.HashMap Global Bytecode.FunIdx) :
    Bytecode.Eval.SameCode (finishCompilation source raw names).bytecode raw.deduplicate.1 := by
  let dedup := raw.deduplicate.1
  let reachable : Bytecode.Toplevel := { dedup with
    functions := dedup.functions.mapIdx fun i f =>
      { f with constrained := dedup.needsCircuit[i]! } }
  let ranked := if source.componentRanks then reachable.withCallComponents else reachable
  have reach : Bytecode.Eval.SameCode reachable dedup := by
    constructor
    · simp only [reachable, Array.size_mapIdx]
    · intro i ha hb t fuel st
      simp only [reachable, Array.getElem_mapIdx]
    · intro i ha hb
      simp only [reachable, Array.getElem_mapIdx]
  have rank : Bytecode.Eval.SameCode ranked reachable := by
    dsimp only [ranked]
    split
    · exact reachable.withCallComponents_sameCode
    · exact Bytecode.Eval.SameCode.refl reachable
  have partition : Bytecode.Eval.SameCode
      (finishCompilation source raw names).bytecode ranked :=
    Bytecode.Eval.SameCode.ofFunctionsEq rfl
  exact partition.trans (rank.trans reach)

/-- Backward success reflection for the final reachability/partition passes.
The preceding deduplication and source-to-bytecode passes remain separate. -/
theorem finishCompilation_reflects {source : Source.Toplevel} {raw : Bytecode.Toplevel}
    {names : Std.HashMap Global Bytecode.FunIdx} {function : Bytecode.FunIdx}
    {args : Array G} {io : IOBuffer} {fuel : Nat} {result : Array G × IOBuffer}
    (h : Bytecode.Eval.runFunction (finishCompilation source raw names).bytecode
      function args io fuel = .ok result) :
    Bytecode.Eval.runFunction raw.deduplicate.1 function args io fuel = .ok result :=
  (Bytecode.Eval.runFunction_sameCode (finishCompilation_sameCode source raw names)
    function args io fuel).symm.trans h

/-- Checked deduplication, reachability metadata and circuit construction
preserve and reflect success at the actual remapping of each original index. -/
theorem finishCompilation_preserves_execution (source : Source.Toplevel) (raw : Bytecode.Toplevel)
    (names : Std.HashMap Global Bytecode.FunIdx) (function : Bytecode.FunIdx)
    (args : Array G) (io : IOBuffer) (fuel : Nat) (result : Array G × IOBuffer) :
    Bytecode.Eval.runFunction raw function args io fuel = .ok result ↔
      Bytecode.Eval.runFunction (finishCompilation source raw names).bytecode
        (raw.deduplicate.2 function) args io fuel = .ok result := by
  rw [Bytecode.Eval.runFunction_sameCode (finishCompilation_sameCode source raw names)]
  exact Bytecode.Eval.deduplicate_preserves_execution raw function args io fuel result

private theorem fold_renamed_name_image {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (items : List (α × Nat)) (initial : Std.HashMap α Nat) (rename : Nat → Nat)
    {name : α} {value : Nat}
    (present : (items.foldl (fun acc item => acc.insert item.1 (rename item.2)) initial)[name]? =
      some value) :
    initial[name]? = some value ∨ ∃ before, (name, before) ∈ items ∧ rename before = value := by
  induction items generalizing initial with
  | nil => exact Or.inl present
  | cons item items ih =>
    simp only [List.foldl_cons] at present
    rcases ih _ present with prior | ⟨before, member, eq⟩
    · rw [Std.HashMap.getElem?_insert] at prior
      split at prior
      next same =>
        have hname : item.1 = name := eq_of_beq same
        have hvalue : rename item.2 = value := Option.some.inj prior
        exact Or.inr ⟨item.2, List.mem_cons.mpr (Or.inl (Prod.ext hname.symm rfl)), hvalue⟩
      next different => exact Or.inl prior
    · exact Or.inr ⟨before, by simp [member], eq⟩

/-- A compiled entrypoint comes from the same name before deduplication,
with its index transformed by the actual selected renaming. -/
theorem finishCompilation_nameMap_image {source : Source.Toplevel} {raw : Bytecode.Toplevel}
    {names : Std.HashMap Global Bytecode.FunIdx} {name : Lean.Name} {function : Bytecode.FunIdx}
    (present : (finishCompilation source raw names).getFuncIdx name = some function) :
    ∃ original, names[Global.mk name]? = some original ∧ raw.deduplicate.2 original = function := by
  simp only [finishCompilation, CompiledToplevel.getFuncIdx, Id.run, pure] at present
  rw [Std.HashMap.fold_eq_foldl_toList] at present
  rcases fold_renamed_name_image names.toList ∅ raw.deduplicate.2 present with impossible | ⟨original, member, eq⟩
  · simp at impossible
  · exact ⟨original, by simpa using member, eq⟩

end Aiur
