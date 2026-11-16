import IxVMRefinement.Decl.ReferenceReplay
import IxVMRefinement.Decl.ThmBodyRole

/-! # Definition typing retained by actual reference replay

The semantic model alone records membership, not the definition front's conversion check.
Actual replay supplies that additional fact for every stored definition, and it remains
available under the environment extensions used by constructor normalization.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model

/-- The actual value/type checking evidence of a stored definition, at a later environment. -/
def DefinitionTyping (env : Env .anon) (cv : ConstantVal .anon) (value : Expr .anon) : Prop :=
  value.hasFvar = false ∧ value.looseBVarsBounded 0 = true ∧
    ∃ valueType typeType universe,
      Ix.Kernel.Rules.Infer env .full 0 value valueType ∧
      Ix.Kernel.Rules.DefEq env 0 valueType cv.type ∧
      Ix.Kernel.Rules.Infer env .full 0 cv.type typeType ∧
      Ix.Kernel.Rules.Red env 0 typeType (.sort universe)

def DefinitionsTyped (env : Env .anon) : Prop :=
  ∀ name cv value hint, env.find? name = some (.defnInfo cv value hint) → DefinitionTyping env cv value

theorem DefinitionTyping.weaken {before after : Env .anon} (extension : EnvExt before after)
    {cv : ConstantVal .anon} {value : Expr .anon} (typed : DefinitionTyping before cv value) :
    DefinitionTyping after cv value := by
  obtain ⟨closed, bounded, vt, st, u, hv, hd, ht, hs⟩ := typed
  exact ⟨closed, bounded, vt, st, u, Ix.Kernel.Rules.Infer.weaken extension hv,
    Ix.Kernel.Rules.DefEq.weaken extension hd, Ix.Kernel.Rules.Infer.weaken extension ht,
    Ix.Kernel.Rules.Red.weaken extension hs⟩

theorem DefinitionTyping.of_runs {env : Env .anon} {fuel : Nat}
    {raw : ConstantVal .anon} {rawValue type value : Expr .anon}
    (header : ConstantValRun .verified fuel env raw type)
    (body : ValueFrontRun .verified fuel env raw rawValue type value) :
    DefinitionTyping env { raw with type } value := by
  have headerRules := constantValRun_rulesJ header
  have bodyRules := valueFrontRun_rulesJ body
  obtain ⟨_, _, _, _, _, _, _, _, _, st, u, ht, hs⟩ := headerRules
  obtain ⟨bounded, closed, annotated, _, _, vt, hv, hd⟩ := bodyRules
  obtain ⟨closedOut, boundedOut⟩ := (judgeFrames_rulesJ env).annot_syntax annotated closed bounded
  exact ⟨closedOut, boundedOut, vt, st, u, hv, hd, ht, hs⟩

private def NotDefinition : ConstantInfo .anon → Prop
  | .defnInfo _ _ _ => False
  | _ => True

private theorem basis_not_definition (kind : BasisKind) :
    (kind.declsA (md := .anon)).all (fun ci => match ci with | .defnInfo _ _ _ => false | _ => true) = true := by
  cases kind <;> decide +kernel

private theorem basis_no_definitions {before after : Env .anon} {kind : BasisKind}
    (run : DeclBasisRun before kind after) : NewSat before after NotDefinition := by
  apply basis_newSat _ run
  intro ci member
  have shape := List.all_eq_true.mp (basis_not_definition kind) ci member
  cases ci <;> first | trivial | cases shape

private theorem projections_no_definitions {fuel : Nat} {T ctor : Key .anon}
    {levels : List LevelParam} {nP nF : Nat} :
    ∀ {before after : Env .anon} {fields : List Nat},
      ProjInstallRun .verified fuel T ctor levels nP nF before fields after →
      NewSat before after NotDefinition := by
  intro before after fields run
  induction fields generalizing before with
  | nil =>
    change after = before at run
    subst after
    exact NewSat.refl _ _
  | cons i fields ih =>
    obtain ⟨next, step, rest⟩ := run
    rcases step with checked | ⟨_, rfl⟩
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := checked
      exact (NewSat.cons (Q := NotDefinition) (by trivial)).trans (ih rest)
    · exact ih rest

private theorem phases_no_definitions {J : Judgements .anon}
    {before middle after : Env .anon} {names : List (Key .anon)} {caps : IndCaps .anon}
    {members recs : List (ConstantInfo .anon)}
    (memberRun : IndMembersRunJ J names caps before members middle)
    (recRun : IndRecsRunJ J names middle recs after) : NewSat before after NotDefinition := by
  have first := indMembersRunJ_newSat (Q := NotDefinition) (fun _ => trivial) (fun _ _ _ => trivial) memberRun
  rcases recRun with ⟨_, rfl⟩ | ⟨_, _, _, _, _, rest⟩
  · exact first
  · exact first.trans (indRecsFoldRunJ_newSat (Q := NotDefinition) (fun _ _ _ _ => trivial) rest)

private theorem modeled_no_definitions {fuel : Nat} {before after : Env .anon}
    {block : List (ConstantInfo .anon)} (run : DeclIndRun .verified fuel before block after) :
    NewSat before after NotDefinition := by
  obtain ⟨_, branches⟩ := run
  rcases branches with ⟨_, _, _, _, _, _, _, _, _, members, recs, _, _, projections⟩ | ⟨_, _, members, recs⟩
  · exact (phases_no_definitions (indMembersRun_runJ members) (indRecsRun_runJ recs)).trans
      (projections_no_definitions projections)
  · exact phases_no_definitions (indMembersRun_runJ members) (indRecsRun_runJ recs)

private theorem checkDecl_definition_old {fuel : Nat} {ev : Evidences .anon}
    {before after : Env .anon} {d : Declaration .anon}
    (notDefn : ∀ cv value hint, d ≠ .defnDecl cv value hint)
    (checked : checkDecl .verified (fueledOps .verified fuel) ev before d = .ok after) :
    NewSat before after NotDefinition := by
  cases d with
  | defnDecl cv value hint => exact (notDefn cv value hint rfl).elim
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
  | basisDecl kind => exact basis_no_definitions (declBasisRunOf checked)
  | quotDecl kind cv =>
    simp only [checkDecl] at checked
    split at checked
    · cases kind with
      | type => exact basis_no_definitions (declBasisRunOf checked)
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
      exact basis_no_definitions (declBasisRunOf rest)
    | none =>
      simp only [pinned] at rest
      split at rest
      · cases native : nativeParts? nP block with
        | some parts =>
          simp only [native] at rest
          exact native_newSat (Q := NotDefinition) (fun _ _ => trivial) (fun _ _ _ => trivial)
            (fun _ _ _ _ => trivial) (fun _ => trivial) (declNativeRun_runJ (declNativeRun_of rest))
        | none =>
          simp only [native] at rest
          exact modeled_no_definitions (declIndRun_of rest)
      · cases rest

/-- Definition typing comes from each actual declaration check, and survives every replayed branch. -/
theorem ReferenceReplay.definitionsTyped {fuel : Nat} {ev : Evidences .anon}
    {source target sourceOut targetOut : Env .anon} {ds : List (Declaration .anon)}
    (replay : ReferenceReplay fuel ev source target ds sourceOut targetOut) :
    DefinitionsTyped target → DefinitionsTyped targetOut := by
  induction replay with
  | nil => exact id
  | @cons source target sourceNext targetNext sourceOut targetOut d ds agreement sourceCheck targetCheck tail ih =>
    intro typed
    apply ih
    intro name cv value hint found
    have sourceFound := (tail.startAgreement name).symm.find_nonThm found
      (by intro _ _ impossible; cases impossible)
    have oldRow (old : source.find? name = some (.defnInfo cv value hint)) :
        DefinitionTyping targetNext cv value := by
      have targetFound := (agreement name).find_nonThm old (by intro _ _ impossible; cases impossible)
      exact (typed name cv value hint targetFound).weaken targetCheck.envExt
    cases d with
    | defnDecl raw rawValue rawHint =>
      obtain ⟨type, checkedValue, header, body, output, _, _⟩ := declDefnRun_of sourceCheck
      rw [output, Env.find?_cons] at sourceFound
      split at sourceFound
      · obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.defnInfo.inj (Option.some.inj sourceFound)
        exact (DefinitionTyping.of_runs (agreement.constantValRun header)
          (agreement.valueFrontRun body)).weaken targetCheck.envExt
      · exact oldRow sourceFound
    | _ =>
      rcases checkDecl_definition_old (by intros; intro impossible; cases impossible) sourceCheck
        name (.defnInfo cv value hint) sourceFound with old | impossible
      · exact oldRow old
      · exact impossible.elim

/-- Every definition in the actual annotated reference prefix retains its checking evidence. -/
theorem ReferenceReplay.definitionsTyped_from_empty {fuel : Nat} {ev : Evidences .anon}
    {sourceOut targetOut : Env .anon} {ds : List (Declaration .anon)}
    (replay : ReferenceReplay fuel ev Env.empty Env.empty ds sourceOut targetOut) :
    DefinitionsTyped targetOut :=
  replay.definitionsTyped (by intro name cv value hint found; cases found)

end IxVM.Refinement.Decl
