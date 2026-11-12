import IxVMRefinement.Levels.Rom

/-! # The smart constructors over observed, bounded derivations

`level_max`, `level_imax`, `level_reduce`, `level_inst_params` and `level_list_inst` with no
hypothesis on the heights of the levels: `level_max` hands both its arguments to memoized
callees (`level_explicit_val`, `level_max_go`), so in a bounded derivation they are lower than
the field size (`arg_levelDepth_lt`), which is what `levelMax_refines` needs; `level_imax`
calls `level_max` whenever its result depends on a comparison; `level_reduce`,
`level_inst_params` and `level_list_inst` are proved by induction on the derivation, through
the first two. -/

namespace IxVM.Refinement.Levels

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.KernelLevels
open IxVM.Consistency (memoCall Bounded)

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

theorem explicitVal_memoized :
    memoCall IxVM.source "KernelLevels::level_explicit_val" = true := by decide +kernel
theorem maxGo_memoized : memoCall IxVM.source "KernelLevels::level_max_go" = true := by
  decide +kernel
theorem max_memoized : memoCall IxVM.source "KernelLevels::level_max" = true := by
  decide +kernel
theorem isNotZero_memoized : memoCall IxVM.source "KernelLevels::level_is_not_zero" = true := by
  decide +kernel
theorem eq_memoized : memoCall IxVM.source "KernelLevels::level_eq" = true := by
  decide +kernel

theorem klevelList_names :
    klevelListEnum = Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» := by decide +kernel

/-- A sub-derivation of a bounded derivation is bounded. -/
theorem bounded_sub {calls₁ calls₂ : List (Call F)} (hb : Bounded calls₂)
    (hsub : ∀ x ∈ calls₁, x ∈ calls₂) : Bounded calls₁ := by
  obtain ⟨rom, valid, bound⟩ := hb
  exact ⟨rom, valid, fun name hm =>
    let ⟨keys, hk, cover⟩ := bound name hm
    ⟨keys, hk, fun c hc => cover c (hsub c hc)⟩⟩

theorem rep_param_of_load' {h : Heap F} {l : Ix.Kernel.Level} {p x : SourceValue F}
    (rep : RepKLevel h l p)
    (ld : loadValue h p = .ok (.construct "KernelTypes::KLevelNode" "Param" [x])) :
    ∃ n, l = .param n ∧ x = .field (n : F) ∧ n < 4294967296 := by
  cases rep with
  | param hn cell =>
    obtain ⟨-, hx⟩ := load_klevel cell ld
    injection hx with hx _
    exact ⟨_, rfl, hx.symm, hn⟩
  | zero cell | succ cell _ | max cell _ _ | imax cell _ _ =>
    exact absurd (load_klevel cell ld).1 (by decide)

/-! ## `level_max` and `level_imax` -/

/-- **`level_max` returns `levelMax`** on represented levels, in a bounded derivation. -/
theorem levelMax_obs {x_a x_b r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {la lb : Ix.Kernel.Level}
    (ev : ObsFn IxVM.source.world "KernelLevels::level_max" [x_a, x_b] h r h' cs)
    (hb : Bounded cs) (repA : RepKLevel h la x_a) (repB : RepKLevel h lb x_b) :
    RepKLevel h' (levelMax la lb) r ∧ Heap.Extends h h' := by
  have hla : levelDepth la < fieldSize := by
    have hmem : (⟨"KernelLevels::level_explicit_val", [x_a], h⟩ : Call F) ∈ cs := by
      cases Obs.«KernelLevels::level_max».obs ev <;>
        (rename_i hc; rw [hc]; simp)
    exact arg_levelDepth_lt hb hmem explicitVal_memoized (by simp) repA
  have hlb : levelDepth lb < fieldSize := by
    cases Obs.«KernelLevels::level_max».obs ev with
    | n1_bind_n1_bind_n1 m2 cs13 x_na m43 cs54 x_nb m84 cs95 ev15 ev56 ev97 he1 he2 hc =>
      exact arg_levelDepth_lt hb (c := ⟨"KernelLevels::level_explicit_val", [x_b], m2⟩)
        (by rw [hc]; simp) explicitVal_memoized (by simp) (repB.mono ev15.heap_extends)
    | n1_bind_n1_bind_n0 m2 cs13 x_na m43 cs54 x_nb m84 cs95 ev15 ev56 ev97 he1 he2 hc =>
      exact arg_levelDepth_lt hb (c := ⟨"KernelLevels::level_explicit_val", [x_b], m2⟩)
        (by rw [hc]; simp) explicitVal_memoized (by simp) (repB.mono ev15.heap_extends)
    | n1_bind_other m2 cs13 x_na v42 m43 cs54 cs138 ev15 ev56 ev140 hc =>
      exact arg_levelDepth_lt hb (c := ⟨"KernelLevels::level_explicit_val", [x_b], m2⟩)
        (by rw [hc]; simp) explicitVal_memoized (by simp) (repB.mono ev15.heap_extends)
    | other v1 m2 cs13 cs164 ev15 ev166 hc =>
      exact arg_levelDepth_lt hb (c := ⟨"KernelLevels::level_max_go", [x_a, x_b], m2⟩)
        (by rw [hc]; simp) maxGo_memoized (by simp) (repB.mono ev15.heap_extends)
  exact levelMax_refines repA repB hla hlb ev.erase

/-- **`level_imax` returns `levelIMax`** on represented levels, in a bounded derivation. -/
theorem levelIMax_obs {x_a x_b r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {la lb : Ix.Kernel.Level}
    (ev : ObsFn IxVM.source.world "KernelLevels::level_imax" [x_a, x_b] h r h' cs)
    (hb : Bounded cs) (repA : RepKLevel h la x_a) (repB : RepKLevel h lb x_b) :
    RepKLevel h' (levelIMax la lb) r ∧ Heap.Extends h h' := by
  cases Obs.«KernelLevels::level_imax».obs ev with
  | Zero ld he hm hc =>
    obtain rfl := rep_zero_of_load repB ld
    subst he hm
    exact RepKLevel.allocZero h
  | Succ w36 cs45 ld ev47 hc =>
    have hmem : (⟨"KernelLevels::level_max", [x_a, x_b], h⟩ : Call F) ∈ cs := by rw [hc]; simp
    exact levelIMax_refines repA repB
      (arg_levelDepth_lt hb hmem max_memoized (by simp) repA)
      (arg_levelDepth_lt hb hmem max_memoized (by simp) repB) ev.erase
  | other_n1 v1 m70 cs80 cs108 ld hne29 hne65 ev82 ev110 hc =>
    have ext := ev82.heap_extends
    have hmem : (⟨"KernelLevels::level_max", [x_a, x_b], m70⟩ : Call F) ∈ cs := by rw [hc]; simp
    exact levelIMax_refines repA repB
      (arg_levelDepth_lt hb hmem max_memoized (by simp) (repA.mono ext))
      (arg_levelDepth_lt hb hmem max_memoized (by simp) (repB.mono ext)) ev.erase
  | other_n0_Zero v1 m70 cs80 ld hne29 hne65 ev82 ld144 he he' hc =>
    have ext := ev82.heap_extends
    obtain rfl := rep_zero_of_load (repA.mono ext) ld144
    have hmem : (⟨"KernelLevels::level_is_not_zero", [x_b], h⟩ : Call F) ∈ cs := by
      rw [hc]; simp
    exact levelIMax_refines repA repB (by simp [levelDepth])
      (arg_levelDepth_lt hb hmem isNotZero_memoized (by simp) repB) ev.erase
  | other_n0_other_n1 v1 m70 cs80 v133 m161 cs171 ld hne29 hne65 ev82 ld144 hne156 ev173
      he he' hc =>
    have ext := ev82.heap_extends
    have hmem : (⟨"KernelLevels::level_eq", [x_a, x_b], m70⟩ : Call F) ∈ cs := by rw [hc]; simp
    exact levelIMax_refines repA repB
      (arg_levelDepth_lt hb hmem eq_memoized (by simp) (repA.mono ext))
      (arg_levelDepth_lt hb hmem eq_memoized (by simp) (repB.mono ext)) ev.erase
  | other_n0_other_n0 v1 m70 cs80 v133 m161 cs171 ld hne29 hne65 ev82 ld144 hne156 ev173
      he hm hc =>
    have ext := ev82.heap_extends
    have hmem : (⟨"KernelLevels::level_eq", [x_a, x_b], m70⟩ : Call F) ∈ cs := by rw [hc]; simp
    exact levelIMax_refines repA repB
      (arg_levelDepth_lt hb hmem eq_memoized (by simp) (repA.mono ext))
      (arg_levelDepth_lt hb hmem eq_memoized (by simp) (repB.mono ext)) ev.erase

/-! ## `level_reduce`, `level_inst_params`, `level_list_inst`: induction on the derivation -/

/-- **`level_reduce` returns `levelReduce`** on a represented level, in a bounded derivation. -/
theorem levelReduce_obs {x_l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {l : Ix.Kernel.Level}
    (ev : ObsFn IxVM.source.world "KernelLevels::level_reduce" [x_l] h r h' cs)
    (hb : Bounded cs) (rep : RepKLevel h l x_l) :
    RepKLevel h' (levelReduce l) r ∧ Heap.Extends h h' := by
  cases Obs.«KernelLevels::level_reduce».obs ev with
  | Zero ld he hm hc =>
    obtain rfl := rep_zero_of_load rep ld
    subst he hm
    exact RepKLevel.allocZero h
  | Param x_i ld he hm hc =>
    obtain ⟨n, rfl, rfl, hn⟩ := rep_param_of_load' rep ld
    subst he hm
    exact RepKLevel.allocParam h hn
  | Succ x_u v78 m80 cs88 ld he hm ev90 hc =>
    obtain ⟨u, rfl, hu⟩ := rep_succ_of_load rep ld
    obtain ⟨repU, ext1⟩ := levelReduce_obs ev90 (bounded_sub hb (by rw [hc]; chainsub)) hu
    subst he hm
    obtain ⟨repS, ext2⟩ := RepKLevel.allocSucc repU
    exact ⟨repS, ext1.trans ext2⟩
  | Max x_a x_b cs120 v123 v124 m126 cs134 m146 cs154 ld ev136 ev156 ev122 hc =>
    obtain ⟨a, b, rfl, ha, hb'⟩ := rep_max_of_load rep ld
    obtain ⟨repA, ext1⟩ := levelReduce_obs ev136 (bounded_sub hb (by rw [hc]; chainsub)) ha
    obtain ⟨repB, ext2⟩ := levelReduce_obs ev156 (bounded_sub hb (by rw [hc]; chainsub)) (hb'.mono ext1)
    obtain ⟨repM, ext3⟩ := levelMax_obs ev122 (bounded_sub hb (by rw [hc]; chainsub)) (repA.mono ext2) repB
    exact ⟨repM, (ext1.trans ext2).trans ext3⟩
  | IMax x_a x_b cs186 v189 v190 m192 cs200 m212 cs220 ld ev202 ev222 ev188 hc =>
    obtain ⟨a, b, rfl, ha, hb'⟩ := rep_imax_of_load rep ld
    obtain ⟨repA, ext1⟩ := levelReduce_obs ev202 (bounded_sub hb (by rw [hc]; chainsub)) ha
    obtain ⟨repB, ext2⟩ := levelReduce_obs ev222 (bounded_sub hb (by rw [hc]; chainsub)) (hb'.mono ext1)
    obtain ⟨repM, ext3⟩ :=
      levelIMax_obs ev188 (bounded_sub hb (by rw [hc]; chainsub)) (repA.mono ext2) repB
    exact ⟨repM, (ext1.trans ext2).trans ext3⟩
termination_by cs.length
decreasing_by all_goals (rw [hc]; simp only [List.length_append, List.length_cons]; omega)

/-- **`level_inst_params` returns `substLevel`** on a represented level and parameter list, in a
bounded derivation; every parameter the level names is in the list. -/
theorem levelInstParams_obs {x_l x_ps r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {l : Ix.Kernel.Level} {params : List Ix.Kernel.Level}
    (ev : ObsFn IxVM.source.world "KernelLevels::level_inst_params" [x_l, x_ps] h r h' cs)
    (hb : Bounded cs) (rep : RepKLevel h l x_l) (repPs : RepKLevelList h params x_ps) :
    ParamsLt params.length l ∧ RepKLevel h' (substLevel l params) r ∧ Heap.Extends h h' := by
  cases Obs.«KernelLevels::level_inst_params».obs ev with
  | Zero ld he hm hc =>
    obtain rfl := rep_zero_of_load rep ld
    subst he hm
    obtain ⟨repZ, ext⟩ := RepKLevel.allocZero h
    exact ⟨trivial, repZ, ext⟩
  | Succ x_u v49 m51 cs59 ld he hm ev61 hc =>
    obtain ⟨u, rfl, hu⟩ := rep_succ_of_load rep ld
    obtain ⟨hpu, repU, ext1⟩ := levelInstParams_obs ev61 (bounded_sub hb (by rw [hc]; chainsub)) hu repPs
    subst he hm
    obtain ⟨repS, ext2⟩ := RepKLevel.allocSucc repU
    exact ⟨hpu, repS, ext1.trans ext2⟩
  | Max x_a x_b cs99 v102 v103 m105 cs113 m133 cs141 ld ev115 ev143 ev101 hc =>
    obtain ⟨a, b, rfl, ha, hb'⟩ := rep_max_of_load rep ld
    obtain ⟨hpa, repA, ext1⟩ :=
      levelInstParams_obs ev115 (bounded_sub hb (by rw [hc]; chainsub)) ha repPs
    obtain ⟨hpb, repB, ext2⟩ :=
      levelInstParams_obs ev143 (bounded_sub hb (by rw [hc]; chainsub)) (hb'.mono ext1) (repPs.mono ext1)
    obtain ⟨repM, ext3⟩ := levelMax_obs ev101 (bounded_sub hb (by rw [hc]; chainsub)) (repA.mono ext2) repB
    exact ⟨⟨hpa, hpb⟩, repM, (ext1.trans ext2).trans ext3⟩
  | IMax x_a x_b cs181 v184 v185 m187 cs195 m215 cs223 ld ev197 ev225 ev183 hc =>
    obtain ⟨a, b, rfl, ha, hb'⟩ := rep_imax_of_load rep ld
    obtain ⟨hpa, repA, ext1⟩ :=
      levelInstParams_obs ev197 (bounded_sub hb (by rw [hc]; chainsub)) ha repPs
    obtain ⟨hpb, repB, ext2⟩ :=
      levelInstParams_obs ev225 (bounded_sub hb (by rw [hc]; chainsub)) (hb'.mono ext1) (repPs.mono ext1)
    obtain ⟨repM, ext3⟩ :=
      levelIMax_obs ev183 (bounded_sub hb (by rw [hc]; chainsub)) (repA.mono ext2) repB
    exact ⟨⟨hpa, hpb⟩, repM, (ext1.trans ext2).trans ext3⟩
  | Param x_i cs258 ld ev260 hc =>
    obtain ⟨n, rfl, rfl, hn⟩ := rep_param_of_load' rep ld
    rw [← Obs.Names.«Lists::lookup<&KernelTypes::KLevelNode>».symbol] at ev260
    obtain ⟨l', hl', repL', rfl⟩ := listsLookup_refines hn repPs ev260.erase
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hl'
    refine ⟨hlt, ?_, Heap.Extends.refl _⟩
    simp only [substLevel, hl', Option.getD_some]
    exact repL'
termination_by cs.length
decreasing_by all_goals (rw [hc]; simp only [List.length_append, List.length_cons]; omega)

/-- **`level_list_inst` returns `substLevelList`**, in a bounded derivation. -/
theorem levelListInst_obs {x_ls x_ps r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {lvls params : List Ix.Kernel.Level}
    (ev : ObsFn IxVM.source.world "KernelLevels::level_list_inst" [x_ls, x_ps] h r h' cs)
    (hb : Bounded cs) (repLs : RepKLevelList h lvls x_ls) (repPs : RepKLevelList h params x_ps) :
    (∀ l ∈ lvls, ParamsLt params.length l) ∧ RepKLevelList h' (substLevelList lvls params) r ∧
      Heap.Extends h h' := by
  cases Obs.«KernelLevels::level_list_inst».obs ev with
  | Nil ld he hm hc =>
    cases repLs with
    | nil cell =>
      subst he hm
      obtain ⟨repN, ext⟩ := RepKLevelList.allocNil h
      rw [klevelList_names] at repN ext
      exact ⟨by simp, repN, ext⟩
    | cons cell _ _ =>
      rw [loadValue_enum_cell cell, klevelList_names] at ld
      injection ld with hv
      injection hv with _ hc' _
      exact absurd hc' (by decide)
  | Cons x_l x_rest v54 v55 m57 cs65 m85 cs93 ld he hm ev67 ev95 hc =>
    cases repLs with
    | nil cell =>
      rw [loadValue_enum_cell cell, klevelList_names] at ld
      injection ld with hv
      injection hv with _ hc' _
      exact absurd hc' (by decide)
    | @cons l rest addr lPtr restPtr cell repL repRest =>
      rw [loadValue_enum_cell cell, klevelList_names] at ld
      injection ld with hv
      injection hv with _ _ hxs
      injection hxs with hx hxs
      injection hxs with hr _
      subst hx hr
      obtain ⟨hp1, repL', ext1⟩ :=
        levelInstParams_obs ev67 (bounded_sub hb (by rw [hc]; chainsub)) repL repPs
      obtain ⟨hp2, repRest', ext2⟩ :=
        levelListInst_obs ev95 (bounded_sub hb (by rw [hc]; chainsub)) (RepKLevelList.mono repRest ext1)
          (repPs.mono ext1)
      subst he hm
      obtain ⟨repC, ext3⟩ := RepKLevelList.allocCons (repL'.mono ext2) repRest'
      rw [klevelList_names] at repC ext3
      refine ⟨?_, repC, (ext1.trans ext2).trans ext3⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hp1
      · exact hp2 x hx
termination_by cs.length
decreasing_by all_goals (rw [hc]; simp only [List.length_append, List.length_cons]; omega)

end IxVM.Refinement.Levels
