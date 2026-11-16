import IxVMRefinement.Decl.ReferenceReplayScope
import IxC.Kernel.Verify.Rename.Installs
import IxC.Kernel.Verify.Rename.Pins

/-! # Metadata scope of actual reference installs

Inductive capabilities and projection tables carry constructor keys outside their expression
payloads. Actual block checking confines these keys to the block's declared names. Other
stored kinds have no such extra metadata keys.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model

/-- The non-expression keys needed by the kernel's environment-frame relation. -/
def MetadataGood (P : KeyScope .anon) : ConstantInfo .anon → Prop
  | .indInfo _ caps => caps.Good P
  | .projInfo table => table.structName.Good P ∧ table.ctor.Good P
  | _ => True

def MetadataIn (P : KeyScope .anon) (env : Env .anon) : Prop :=
  ∀ name ci, env.find? name = some ci → MetadataGood P ci

theorem MetadataGood.of_good {P : KeyScope .anon} {ci : ConstantInfo .anon}
    (good : ci.Good P) : MetadataGood P ci := by
  cases ci with
  | indInfo _ _ => exact good.2
  | projInfo _ => exact ⟨good.1, good.2.1⟩
  | _ => trivial

theorem MetadataGood.mono {P Q : KeyScope .anon} (includeScope : P.Le Q) :
    ∀ {ci : ConstantInfo .anon}, MetadataGood P ci → MetadataGood Q ci := by
  intro ci good
  cases ci with
  | indInfo _ _ => exact fun name member => Key.Good.mono includeScope.1 includeScope.2 (good name member)
  | projInfo _ => exact ⟨Key.Good.mono includeScope.1 includeScope.2 good.1,
      Key.Good.mono includeScope.1 includeScope.2 good.2⟩
  | _ => trivial

private theorem native_caps_metadata {P : KeyScope .anon} {p : InductiveShape .anon}
    (constructors : ∀ c ∈ p.ctors, c.1.name.Good P) (isRec : Bool) :
    (nativeCapsAt p isRec).Good P := by
  unfold nativeCapsAt
  rcases hctors : p.ctors with _ | ⟨c, _ | _⟩
  · intro name member; simp at member
  · intro name member
    simp only [Option.mem_def, Option.some.injEq] at member
    rw [← member]
    exact constructors c (by rw [hctors]; exact List.mem_cons_self)
  · intro name member; simp at member

private theorem native_table_metadata {P : KeyScope .anon} {p : NativeParts .anon}
    {ctors : List (ConstantVal .anon × Nat)} {sorts : List (List Level)}
    {before after : Env .anon}
    (former : p.cvT.name.Good P) (constructors : ∀ c ∈ ctors, c.1.name.Good P)
    (run : checkNativeTable (m := CheckM .anon) p ctors sorts before = .ok after) :
    NewSat before after (MetadataGood P) := by
  unfold checkNativeTable at run
  split at run
  · next c sorts =>
    split at run
    · obtain ⟨bodies, _, _, _, _, rfl⟩ := checkStructProjTable_inv run
      exact NewSat.cons ⟨former, constructors c (by simp_all)⟩
    · obtain rfl := Except.ok.inj run
      exact NewSat.refl _ _
  · obtain rfl := Except.ok.inj run
    exact NewSat.refl _ _

/-- The actual native run's capability and table constructor keys are its declared keys. -/
theorem nativeRun_metadata {P : KeyScope .anon} {fuel : Nat} {before after : Env .anon}
    {p₀ : NativeParts .anon}
    (formerKey : p₀.cvT.name.Good P)
    (constructorKeys : ∀ c ∈ p₀.ctors, c.1.name.Good P)
    (run : DeclNativeRun .verified fuel before p₀ after) :
    NewSat before after (MetadataGood P) := by
  obtain ⟨_, isRec, middle, cvTa, p₁, p, ctorsA, sortss, kinds, cvRa, rhss, _, _, _,
    former, completed, ctors, _, _, _, _, _, _, _, _, _, table⟩ := run
  have formerData := checkSumInd_post (ops := fueledOps .verified fuel) before
    p₀.toInductiveShape (fun shape => nativeCapsAt shape isRec) _ former
  dsimp only at formerData
  obtain ⟨formerEnv, _, sameFormer, sameCtors, _, _⟩ := formerData
  have finalFormer : p.cvT = p₀.cvT := by
    rw [completed]
    simpa only [NativeParts.withKinds, NativeParts.complete] using sameFormer
  have finalCtors : p.ctors = p₀.ctors := by
    rw [completed]
    simpa only [NativeParts.withKinds, NativeParts.complete] using sameCtors
  have checkedNames := (checkSumCtors_post (ops := fueledOps .verified fuel) middle middle
    p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large cvTa p.ctors _ ctors).1
  have checkedCtors : ∀ c ∈ ctorsA, c.1.name.Good P := by
    intro c member
    have named : c.1.name ∈ ctorsA.map (·.1.name) := List.mem_map_of_mem member
    rw [checkedNames, finalCtors] at named
    obtain ⟨original, old, same⟩ := List.mem_map.mp named
    rw [← same]
    exact constructorKeys original old
  have first : NewSat before middle (MetadataGood P) := by
    rw [formerEnv]
    apply NewSat.cons
    apply native_caps_metadata
    simpa only [sameCtors] using constructorKeys
  exact first.trans ((consSumCtors_newSat (Q := MetadataGood P) (fun _ _ _ => trivial)).trans
    ((NewSat.cons (Q := MetadataGood P) (by trivial)).trans
      (native_table_metadata (by rw [finalFormer]; exact formerKey) checkedCtors table)))

private theorem projection_metadata {P : KeyScope .anon} {fuel : Nat}
    {T ctor : Key .anon} {lps : List LevelParam} {nP nF : Nat} :
    ∀ {before after : Env .anon} {fields : List Nat},
      ProjInstallRun .verified fuel T ctor lps nP nF before fields after →
      NewSat before after (MetadataGood P) := by
  intro before after fields run
  induction fields generalizing before with
  | nil =>
    change after = before at run
    subst after
    exact NewSat.refl _ _
  | cons i fields ih =>
    obtain ⟨next, step, tail⟩ := run
    rcases step with checked | ⟨_, rfl⟩
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := checked
      exact (NewSat.cons (Q := MetadataGood P) (by trivial)).trans (ih tail)
    · exact ih tail

private theorem phases_metadata {P : KeyScope .anon} {J : Judgements .anon}
    {before middle after : Env .anon} {names : List (Key .anon)} {caps : IndCaps .anon}
    {members recs : List (ConstantInfo .anon)}
    (capKeys : caps.Good P)
    (memberRun : IndMembersRunJ J names caps before members middle)
    (recRun : IndRecsRunJ J names middle recs after) :
    NewSat before after (MetadataGood P) := by
  have first := indMembersRunJ_newSat (Q := MetadataGood P)
    (fun _ => capKeys) (fun _ _ _ => trivial) memberRun
  rcases recRun with ⟨_, rfl⟩ | ⟨_, _, _, _, _, folded⟩
  · exact first
  · exact first.trans (indRecsFoldRunJ_newSat (Q := MetadataGood P) (fun _ _ _ _ => trivial) folded)

/-- Both complete modeled branches keep metadata constructor keys inside the declared block. -/
theorem modeledRun_metadata {P : KeyScope .anon} {fuel : Nat} {before after : Env .anon}
    {block : List (ConstantInfo .anon)} (keys : ∀ ci ∈ block, ci.name.Good P)
    (run : DeclIndRun .verified fuel before block after) :
    NewSat before after (MetadataGood P) := by
  obtain ⟨_, branch⟩ := run
  rcases branch with ⟨cvT, capsT, cvC, nP, nF, _, ctors, middle, beforeProjections,
      members, recs, _, _, projections⟩ | ⟨_, middle, members, recs⟩
  · have ctorMember : ConstantInfo.ctorInfo cvC nP nF ∈ block := by
      have filtered : ConstantInfo.ctorInfo cvC nP nF ∈
          block.filter (fun ci => match ci with | .ctorInfo _ _ _ => true | _ => false) := by
        rw [ctors]
        exact List.mem_cons_self
      exact (List.mem_filter.mp filtered).1
    have capKeys : (indBlockCaps .verified before cvT cvC nP nF).Good P := by
      intro name member
      have same : cvC.name = name := Option.some.inj member
      rw [← same]
      exact keys _ ctorMember
    exact (phases_metadata capKeys (indMembersRun_runJ members) (indRecsRun_runJ recs)).trans
      (projection_metadata projections)
  · exact phases_metadata (by intro name member; cases member)
      (indMembersRun_runJ members) (indRecsRun_runJ recs)

/-- Pinned basis metadata refers only to prelude roles. -/
private theorem basis_metadata {P : KeyScope .anon} (prelude : P.Pre)
    {before after : Env .anon} {kind : BasisKind}
    (run : DeclBasisRun before kind after) : NewSat before after (MetadataGood P) :=
  basis_newSat (fun ci member => MetadataGood.of_good
    (ConstantInfo.good_of_pinIn prelude (List.all_eq_true.mp (declsA_pinIn kind) ci member))) run

/-- Every actual declaration installs only metadata supported by its own names and the prelude. -/
theorem checkedDecl_metadata {P : KeyScope .anon} (prelude : P.Pre)
    {fuel : Nat} {ev : Evidences .anon} {before after : Env .anon} {d : Declaration .anon}
    (keys : ∀ name ∈ d.names, name.Good P)
    (checked : checkDecl .verified (fueledOps .verified fuel) ev before d = .ok after) :
    NewSat before after (MetadataGood P) := by
  cases d with
  | defnDecl cv value hint =>
    obtain ⟨_, _, _, _, rfl, _, _⟩ := declDefnRun_of checked
    exact NewSat.cons trivial
  | thmDecl cv value =>
    obtain ⟨_, _, _, _, _, rfl⟩ := declThmRun_of checked
    exact NewSat.cons trivial
  | opaqueDecl cv value =>
    obtain ⟨_, _, _, _, rfl⟩ := declOpaqueRun_of checked
    exact NewSat.cons trivial
  | axiomDecl cv =>
    rcases declAxiomRun_of checked with ⟨_, rfl⟩ | ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩⟩
    · exact NewSat.refl _ _
    · exact NewSat.cons trivial
    · exact NewSat.refl _ _
  | basisDecl kind => exact basis_metadata prelude (declBasisRunOf checked)
  | quotDecl kind cv =>
    simp only [checkDecl] at checked
    split at checked
    · cases kind with
      | type => exact basis_metadata prelude (declBasisRunOf checked)
      | ctor | lift | ind | sound =>
        obtain rfl := Except.ok.inj checked
        exact NewSat.refl _ _
    · cases checked
  | indDecl block nP =>
    simp only [checkDecl] at checked
    have rest := (checkIndShape_bind_ok checked).2
    cases pinned : basisPinHit block with
    | some kind =>
      simp only [pinned] at rest
      exact basis_metadata prelude (declBasisRunOf rest)
    | none =>
      simp only [pinned] at rest
      split at rest
      · cases native : nativeParts? nP block with
        | some parts =>
          simp only [native] at rest
          have named := nativeParts?_names native
          exact nativeRun_metadata (keys _ named.1)
            (fun c member => keys _ (named.2.2 c member)) (declNativeRun_of rest)
        | none =>
          simp only [native] at rest
          exact modeledRun_metadata
            (fun ci member => keys _ (List.mem_map_of_mem member)) (declIndRun_of rest)
      · cases rest


theorem MetadataIn.mono {P Q : KeyScope .anon} (includeScope : P.Le Q)
    {env : Env .anon} (support : MetadataIn P env) : MetadataIn Q env :=
  fun name ci found => MetadataGood.mono includeScope (support name ci found)

/-- The actual pure fold bounds all extra metadata keys by its declaration names. -/
theorem checkedDecls_metadata (fuel : Nat) (ev : Evidences .anon) :
    ∀ (ds : List (Declaration .anon)) (known : List (Key .anon)) {before after : Env .anon},
      MetadataIn (nameScope known) before →
      ds.foldlM (checkDecl .verified (fueledOps .verified fuel) ev) before = .ok after →
      MetadataIn (nameScope (known ++ ds.flatMap Declaration.names)) after := by
  intro ds
  induction ds with
  | nil =>
    intro known before after supported checked
    obtain rfl := Except.ok.inj checked
    simpa only [List.flatMap_nil, List.append_nil] using supported
  | cons d ds ih =>
    intro known before after supported checked
    obtain ⟨middle, head, tail⟩ := foldlM_cons_ok checked
    have added := checkedDecl_metadata (nameScope_pre (known ++ d.names))
      (fun name member => Key.good_nameScope.mpr
        (Over.of_mem (List.mem_append_right known member))) head
    have old := supported.mono (nameScope_le (fun name member => List.mem_append_left d.names member))
    have next : MetadataIn (nameScope (known ++ d.names)) middle := by
      intro name ci found
      exact (added name ci found).elim (old name ci) id
    simpa only [List.flatMap_cons, List.append_assoc] using ih (known ++ d.names) next tail

private theorem metadata_entry_reverse {a b : Option (ConstantInfo .anon)}
    (entry : ThmBodyView.Entry a b) : ThmBodyView.Entry b a := by
  cases entry with
  | same => exact .same _
  | thm cv old new => exact .thm cv new old

/-- Opaque theorem-body replacement does not change metadata support. -/
theorem ThmBodyView.Agrees.metadata {P : KeyScope .anon} {source target : Env .anon}
    (agreement : ThmBodyView.Agrees source target) (supported : MetadataIn P source) :
    MetadataIn P target := by
  intro name ci found
  have reverse : ThmBodyView.Agrees target source := fun key => metadata_entry_reverse (agreement key)
  cases ci with
  | indInfo cv caps =>
    exact supported name _ (reverse.find_nonThm found (by intros; intro h; cases h))
  | projInfo table =>
    exact supported name _ (reverse.find_nonThm found (by intros; intro h; cases h))
  | _ => trivial

theorem ReferenceReplay.metadata {fuel : Nat} {ev : Evidences .anon}
    {target sourceOut targetOut : Env .anon} {ds : List (Declaration .anon)}
    (replay : ReferenceReplay fuel ev Env.empty target ds sourceOut targetOut) :
    MetadataIn (nameScope (ds.flatMap Declaration.names)) targetOut := by
  have empty : MetadataIn (nameScope []) (Env.empty : Env .anon) := by
    intro name ci found
    simp [Env.find?, Env.empty] at found
  apply replay.endAgreement.metadata
  simpa only [List.nil_append] using checkedDecls_metadata fuel ev ds [] empty replay.sourceRun

universe u

/-- The checked model supplies expression payload support; the actual install supplies metadata support. -/
theorem model_findGood {V : Type u} [SetTheory V] {env : Env .anon} {P : KeyScope .anon}
    (model : EnvModelM V .verified env) (theorems : ThmValOk model)
    (keys : ∀ name, (env.find? name).isSome = true → name.Good P)
    (metadata : MetadataIn P env) : FindGood P env := by
  intro name ci found
  have member := List.mem_of_find?_eq_some found
  have wf := model.base2.wf ci member
  have nameEq : ci.name = name := Ix.Kernel.Semantics.Env.find?_name found
  have cvGood : ci.toConstantVal.Good P := by
    refine ⟨?_, expression_good_of_resolves keys _ wf.2.2.1⟩
    change ci.name.Good P
    rw [nameEq]
    exact keys name (by rw [found]; rfl)
  cases ci with
  | axiomInfo cv | ctorInfo cv _ _ => exact cvGood
  | defnInfo cv value hint =>
    exact ⟨cvGood, expression_good_of_resolves keys _
      (wf.2.2.2.2.1 cv value hint rfl).2.2.1⟩
  | thmInfo cv value =>
    exact ⟨cvGood, expression_good_of_resolves keys _ (theorems.resolve cv value member)⟩
  | indInfo cv caps => exact ⟨cvGood, metadata name _ found⟩
  | recInfo cv mI rP rules =>
    refine ⟨cvGood, ?_⟩
    intro rule inRules
    obtain ⟨⟨ctorCV, ctorFound, _, _, _, _⟩, _, _⟩ :=
      model.base2.rec_ctors name cv mI rP rules found rule inRules
    have ruleWF := wf.2.2.2.2.2.1 cv mI rP rules rfl rule inRules
    refine ⟨keys rule.ctor (by rw [ctorFound]; rfl), ?_,
      expression_good_of_resolves keys _ ruleWF.2.2.1⟩
    cases fire : rule.fire with
    | inert | plain => trivial
    | nested levels pins =>
      intro pin inPins
      exact expression_good_of_resolves keys _
        ((ruleWF.2.2.2.2 levels pins fire).2.2.1 pin inPins).2.2.1
  | projInfo table =>
    have tableKeys := metadata name _ found
    refine ⟨tableKeys.1, tableKeys.2, ?_⟩
    intro body inBodies
    obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem inBodies
    exact expression_good_of_resolves keys _
      ((wf.2.2.2.2.2.2.1 table rfl).2 i _ (Array.getElem?_eq_getElem hi)).2.2.1

/-- Every actual annotated prefix is good at the scope of its preceding declaration names. -/
theorem ReferenceReplay.findGood {V : Type u} [SetTheory V] {fuel : Nat} {ev : Evidences .anon}
    {sourceOut targetOut : Env .anon} {ds : List (Declaration .anon)}
    (replay : ReferenceReplay fuel ev Env.empty Env.empty ds sourceOut targetOut) :
    FindGood (nameScope (ds.flatMap Declaration.names)) targetOut := by
  obtain ⟨⟨model, theorems⟩, _⟩ :=
    (show EnvModelT V .verified targetOut from replay.checked.envModelT EnvModelT.empty)
  apply model_findGood model theorems ?_ replay.metadata
  intro name present
  obtain ⟨ci, found⟩ := Option.isSome_iff_exists.mp present
  exact Key.good_nameScope.mpr (replay.declaredScope name ci found)

end IxVM.Refinement.Decl
