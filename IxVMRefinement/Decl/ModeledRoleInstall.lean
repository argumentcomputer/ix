import IxVMRefinement.Decl.DeclsGlue
import IxVMRefinement.Decl.RoleAnnot
import IxVMRefinement.Decl.ModeledReferenceStep

/-! # Reader-shaped installations from the complete modeled check

Actual annotation runs establish the stored types and rule right-hand sides. The auxiliary
projection-function phase extends the installation without changing its declared members.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model
open IxVM.Consistency (StoredAs ValStored RuleStored InstallStep)

private theorem modeledMember_valStored {fuel : Nat} {env : Env .anon}
    {names : List (Key .anon)} {cv cvA : ConstantVal .anon}
    (run : MemberValRun .verified fuel env names cv cvA) : ValStored cvA cv := by
  obtain ⟨ty, hcv, rfl, _⟩ := run
  obtain ⟨_, _, _, _, hbound, hclosed, annotated, _⟩ := hcv
  exact ⟨rfl, rfl, annotateCore_to_annotates annotated hclosed hbound⟩

private theorem modeledMembers_stored {fuel : Nat} {names : List (Key .anon)}
    {caps : IndCaps .anon} {env out : Env .anon} {members : List (ConstantInfo .anon)}
    (run : IndMembersRun .verified fuel names caps env members out) :
    ∀ raw ∈ members, ∃ stored, out.find? raw.name = some stored ∧ StoredAs stored raw := by
  induction members generalizing env with
  | nil => intro _ h; cases h
  | cons ci rest ih =>
    obtain ⟨cvA, member, tail⟩ := run
    have hs := modeledMember_valStored member
    intro raw mem
    cases ci with
    | indInfo cv caps₀ =>
      rcases List.mem_cons.mp mem with rfl | mem
      · refine ⟨.indInfo cvA caps, ?_, hs, trivial⟩
        change out.find? cv.name = _
        rw [← hs.1]
        exact indMembersRun_mono rest (indMembersRun_runJ tail) _ _ (Env.find?_cons_self _ _)
      · exact ih tail raw mem
    | ctorInfo cv nP nF =>
      rcases List.mem_cons.mp mem with rfl | mem
      · refine ⟨.ctorInfo cvA nP nF, ?_, hs, rfl, rfl⟩
        change out.find? cv.name = _
        rw [← hs.1]
        exact indMembersRun_mono rest (indMembersRun_runJ tail) _ _ (Env.find?_cons_self _ _)
      · exact ih tail raw mem
    | _ => exact tail.elim

private def PreparedRec (entry : ConstantVal .anon × Nat × Nat × List (RecRule .anon))
    (raw : ConstantInfo .anon) : Prop :=
  raw = .recInfo raw.toConstantVal entry.2.1 entry.2.2.1 entry.2.2.2 ∧
    ValStored entry.1 raw.toConstantVal

private theorem modeledProvision_annotations {fuel : Nat} {names : List (Key .anon)}
    {env envSelf : Env .anon} {recs : List (ConstantInfo .anon)}
    {checked : List (ConstantVal .anon × Nat × Nat × List (RecRule .anon))}
    (run : ProvisionRecsRun .verified fuel names env recs envSelf checked) :
    List.Forall₂ PreparedRec checked recs := by
  induction recs generalizing env checked with
  | nil =>
    obtain ⟨_, rfl⟩ := run
    exact .nil
  | cons ci rest ih =>
    obtain ⟨cvA, mI, rP, rules, rest', hci, member, provision, rfl⟩ := run
    exact .cons ⟨hci, modeledMember_valStored member⟩ (ih provision)

private theorem modeledIotaRule_stored {fuel : Nat} {env envSelf : Env .anon}
    {f : Key .anon → Key .anon} {name : Key .anon} {lps : List LevelParam}
    {ty : Expr .anon} {mI rP j : Nat} {raw stored : RecRule .anon}
    (run : IotaRuleRun .verified fuel env envSelf f name lps ty mI rP j raw stored) :
    RuleStored stored raw := by
  obtain ⟨cvj, cnP, cnF, rhs, _, _, bounded, closed, annotated, _, _, _, _, fire, rfl, _⟩ := run
  exact ⟨rfl, rfl, annotateCore_to_annotates annotated closed bounded⟩

private theorem modeledIotaRules_stored {fuel : Nat} {env envSelf : Env .anon}
    {f : Key .anon → Key .anon} {name : Key .anon} {lps : List LevelParam}
    {ty : Expr .anon} {mI rP j : Nat} {raw stored : List (RecRule .anon)}
    (run : IotaRulesRun .verified fuel env envSelf f name lps ty mI rP j raw stored) :
    List.Forall₂ RuleStored stored raw := by
  induction raw generalizing j stored with
  | nil =>
    change stored = [] at run
    subst stored
    exact .nil
  | cons rule rest ih =>
    obtain ⟨rule', rest', hrule, hrest, rfl⟩ := run
    exact .cons (modeledIotaRule_stored hrule) (ih hrest)

private theorem modeledRecFold_stored {fuel : Nat} {names : List (Key .anon)}
    {envBase envSelf acc out : Env .anon}
    {checked : List (ConstantVal .anon × Nat × Nat × List (RecRule .anon))}
    (run : IndRecsRun.IndRecsFoldRun .verified fuel names envBase envSelf acc checked out)
    (nodup : (checked.map (·.1.name)).Nodup) :
    ∀ entry ∈ checked, ∃ rules,
      out.find? entry.1.name = some (.recInfo entry.1 entry.2.1 entry.2.2.1 rules) ∧
      List.Forall₂ RuleStored rules entry.2.2.2 := by
  induction checked generalizing acc with
  | nil => intro _ h; cases h
  | cons c rest ih =>
    obtain ⟨rules, hRules, hrest⟩ := run
    simp only [List.map_cons, List.nodup_cons] at nodup
    intro entry mem
    rcases List.mem_cons.mp mem with rfl | mem
    · refine ⟨rules, ?_, modeledIotaRules_stored hRules⟩
      rw [indRecsFoldRun_keep rest (indRecsFoldRun_runJ hrest) c.1.name ?_]
      · exact Env.find?_cons_self _ _
      · intro other hother heq
        exact nodup.1 (List.mem_map.mpr ⟨other, hother, heq⟩)
    · exact ih hrest nodup.2 entry mem

private theorem modeledRecs_stored {fuel : Nat} {names : List (Key .anon)}
    {env out : Env .anon} {recs : List (ConstantInfo .anon)}
    (run : IndRecsRun .verified fuel names env recs out) :
    ∀ raw ∈ recs, ∃ stored, out.find? raw.name = some stored ∧ StoredAs stored raw := by
  rcases run with ⟨rfl, _⟩ | ⟨_, _, envSelf, checked, provision, installed⟩
  · intro _ h; cases h
  · have prepared := modeledProvision_annotations provision
    obtain ⟨_, nodup, _⟩ := provisionRecsRunJ_fresh _ (provisionRecsRun_runJ provision)
    intro raw mem
    obtain ⟨entry, hentry, hshape, hcv⟩ := Ix.Kernel.Semantics.forall₂_mem_right prepared raw mem
    obtain ⟨rules, found, hRules⟩ := modeledRecFold_stored installed nodup entry hentry
    refine ⟨.recInfo entry.1 entry.2.1 entry.2.2.1 rules, ?_, ?_⟩
    · change out.find? raw.toConstantVal.name = _
      rw [← hcv.1]
      exact found
    · rw [hshape]
      exact ⟨hcv, rfl, rfl, hRules⟩

private theorem modeledPhases_stored {fuel : Nat} {env envM out : Env .anon}
    {block members recs : List (ConstantInfo .anon)} {caps : IndCaps .anon}
    (split : block = members ++ recs)
    (memberRun : IndMembersRun .verified fuel (block.map (·.name)) caps env members envM)
    (recRun : IndRecsRun .verified fuel (block.map (·.name)) envM recs out) :
    ∀ raw ∈ block, ∃ stored, out.find? raw.name = some stored ∧ StoredAs stored raw := by
  intro raw mem
  rw [split] at mem
  rcases List.mem_append.mp mem with mem | mem
  · obtain ⟨stored, found, annotated⟩ := modeledMembers_stored memberRun raw mem
    exact ⟨stored, indRecsRun_keep (indRecsRun_runJ recRun) _ _ found, annotated⟩
  · exact modeledRecs_stored recRun raw mem

private theorem installStep_cons_aux {env acc : Env .anon} {d : Declaration .anon}
    (installed : InstallStep env d acc) {ci : ConstantInfo .anon}
    (fresh : acc.find? ci.name = none) (aux : ∃ root tag, ci.name = .aux root tag) :
    InstallStep env d ⟨ci :: acc.consts⟩ := by
  obtain ⟨new, heq, hn, hf, stored, shape⟩ := installed
  have chain : FreshChain env new acc := ⟨heq, hn, hf⟩
  have next := freshChain_cons chain fresh
  refine ⟨ci :: new, next.eq, next.nodup, next.fresh, ?_, ?_⟩
  · intro raw mem
    obtain ⟨actual, ha, hs⟩ := stored raw mem
    exact ⟨actual, List.mem_cons_of_mem ci ha, hs⟩
  · intro actual mem
    rcases List.mem_cons.mp mem with rfl | mem
    · exact Or.inr aux
    · exact shape actual mem

/-- A modeled projection phase adds fresh auxiliary recursors to the same declaration's install. -/
theorem installStep_modeledProjections {fuel : Nat} {env acc out : Env .anon}
    {d : Declaration .anon} {T ctor : Key .anon} {lps : List LevelParam}
    {nP nF : Nat} {fields : List Nat}
    (installed : InstallStep env d acc)
    (run : ProjInstallRun .verified fuel T ctor lps nP nF acc fields out) :
    InstallStep env d out := by
  induction fields generalizing acc with
  | nil =>
    change out = acc at run
    subst out
    exact installed
  | cons i rest ih =>
    obtain ⟨next, step, tail⟩ := run
    rcases step with checked | ⟨_, rfl⟩
    · obtain ⟨cvj, mcv, mval, mhint, pty, rhs, _, _, _, fresh,
        _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := checked
      apply ih ?_ tail
      exact installStep_cons_aux installed (Option.isNone_iff_eq_none.mp fresh) ⟨T, .projFn i, rfl⟩
    · exact ih installed tail

/-- Every actual modeled run supplies its reader-shaped installation, including its projection tail. -/
theorem modeledRun_installStep {fuel : Nat} {env out : Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat}
    (notPinned : basisPinHit block = none)
    (run : DeclIndRun .verified fuel env block out) : InstallStep env (.indDecl block nP) out := by
  obtain ⟨split, branch⟩ := run
  rcases branch with ⟨cvT, capsT, cvC, cnP, cnF, _, _, envM, envR, members, recs,
    _, _, projections⟩ | ⟨_, envM, members, recs⟩
  · have prefix : InstallStep env (.indDecl block nP) envR :=
      installStep_glue_indPhases notPinned split (indMembersRun_runJ members) (indRecsRun_runJ recs)
        (modeledPhases_stored split members recs)
    exact installStep_modeledProjections prefix projections
  · exact installStep_glue_indPhases notPinned split (indMembersRun_runJ members) (indRecsRun_runJ recs)
      (modeledPhases_stored split members recs)

end IxVM.Refinement.Decl
