import IxVMRefinement.Decl.NativeConstructorFieldChecks
import IxC.Kernel.Verify.Denote.IndFrame

/-! # The two actual free-variable frames of a constructor rebuild

Each frame retains canonical indices, local scope, leaf closure and the executable domain
checks. Pairing the frames does not assert that their type annotations are equal or convertible.
Application inversions expose the real argument comparisons, so subsequent dependent transport
can use those comparisons instead of conversion transitivity or semantic context equivalence.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model Ix.Kernel.Semantics

private theorem opened_domain_scope {md : Mode} :
    ∀ {count depth : Nat} {e residual : Expr md} {fvars : List (Expr md)},
      openPisAtFvars count e depth = some (fvars, residual) → Expr.WScoped depth e →
      e.looseBVarsBounded 0 = true → ∀ slot fv, fvars[slot]? = some fv →
        Expr.WScoped (depth + slot) fv.fvarTypeD ∧ fv.fvarTypeD.looseBVarsBounded 0 = true := by
  intro count
  induction count with
  | zero =>
    intro depth e residual fvars opened _ _ slot fv atSlot
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj opened)
    cases slot <;> cases atSlot
  | succ count ih =>
    intro depth e residual fvars opened scope bounded slot fv atSlot
    cases e with
    | forallE domain body metadata =>
      simp only [openPisAtFvars] at opened
      cases tail : openPisAtFvars count (body.instantiate1 (.fvar depth domain)) (depth + 1) with
      | none => rw [tail] at opened; cases opened
      | some pair =>
        obtain ⟨tailVars, tailResidual⟩ := pair
        rw [tail] at opened
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj opened)
        simp only [Expr.WScoped] at scope
        simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at bounded
        cases slot with
        | zero =>
          obtain rfl := Option.some.inj atSlot
          simpa only [Nat.add_zero, Expr.fvarTypeD] using And.intro scope.1 bounded.1
        | succ slot =>
          have rest := ih tail (scope.1.instantiate1 0 scope.2)
            (looseBVarsBounded_instantiate1 _ 0 bounded.2) slot fv atSlot
          simpa only [Nat.add_succ, Nat.succ_add] using rest
    | _ => cases opened

private theorem opened_leaf_lookup {count : Nat} {e residual fv : Expr .anon} {fvars : List (Expr .anon)}
    (opened : openPisAtFvars count e 0 = some (fvars, residual)) (closed : e.hasFvar = false)
    (member : fv ∈ fvars) {leaf : Nat × Expr .anon} (inLeaf : leaf ∈ fv.fvarLeaves) :
    fvars[leaf.1]? = some (.fvar leaf.1 leaf.2) := by
  have present := Ix.Kernel.Verify.openPisAtFvars_leaves count opened leaf (.inr ⟨fv, member, inLeaf⟩)
  rcases present with inInput | inFrame
  · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar closed] at inInput
    cases inInput
  · obtain ⟨slot, atSlot⟩ := List.mem_iff_getElem?.mp inFrame
    obtain ⟨type, same⟩ := openPisAtFvars_index count e 0 opened slot _ atSlot
    have indexEq := (Expr.fvar.inj same).1
    simp only [Nat.zero_add] at indexEq
    rwa [← indexEq] at atSlot

/-- Actual checked domains in one canonical opener frame. -/
structure CheckedFVarFrame (env : Env .anon) (fuel : Nat) (fvars : List (Expr .anon)) : Prop where
  indexed : ∀ (slot : Nat) (fv : Expr .anon), fvars[slot]? = some fv → fv = .fvar slot fv.fvarTypeD
  domainScope : ∀ (slot : Nat) (fv : Expr .anon), fvars[slot]? = some fv →
    Expr.WScoped slot fv.fvarTypeD ∧ fv.fvarTypeD.looseBVarsBounded 0 = true
  domainChecks : ∀ (slot : Nat) (fv : Expr .anon), fvars[slot]? = some fv → ∃ inferred level,
    inferTypeCore .verified env fuel slot fv.fvarTypeD = .ok inferred ∧
      ensureSortCore .verified env fuel slot inferred = .ok level
  leaves : ∀ (slot : Nat) (fv : Expr .anon), fvars[slot]? = some fv → ∀ (leaf : Nat × Expr .anon), leaf ∈ fv.fvarTypeD.fvarLeaves →
    fvars[leaf.1]? = some (.fvar leaf.1 leaf.2) ∧ leaf.1 < slot

/-- The old and new frames retain separate actual type annotations and checking derivations. -/
structure CheckedFramePair (env : Env .anon) (fuel count : Nat)
    (originalVars finalVars : List (Expr .anon)) : Prop where
  original : CheckedFVarFrame env fuel originalVars
  final : CheckedFVarFrame env fuel finalVars
  originalLength : originalVars.length = count
  finalLength : finalVars.length = count

/-- All frame facts are produced by the header check and its actual opening. -/
theorem checkedFVarFrame_of_check {env : Env .anon} {fuel count : Nat} {raw checked : ConstantVal .anon}
    {fvars : List (Expr .anon)} {residual : Expr .anon}
    (run : checkConstantVal (fueledOps .verified fuel) env raw = .ok checked)
    (opened : openPisAtFvars count checked.type 0 = some (fvars, residual)) : CheckedFVarFrame env fuel fvars := by
  obtain ⟨closed, _, _, bounded⟩ := checkConstantVal_typeWF run
  have domains := opened_domain_scope opened (Expr.WScoped.of_not_hasFvar closed) bounded
  refine ⟨?_, ?_, checked_type_domain_checks run opened, ?_⟩
  · intro slot fv atSlot
    obtain ⟨type, same⟩ := openPisAtFvars_index count checked.type 0 opened slot fv atSlot
    rw [same]
    simp only [Nat.zero_add, Expr.fvarTypeD]
  · intro slot fv atSlot
    simpa only [Nat.zero_add] using domains slot fv atSlot
  · intro slot fv atSlot leaf inType
    have scope := (domains slot fv atSlot).1
    have inVar : leaf ∈ fv.fvarLeaves := by
      obtain ⟨type, same⟩ := openPisAtFvars_index count checked.type 0 opened slot fv atSlot
      rw [same] at inType ⊢
      exact List.mem_cons_of_mem _ inType
    exact ⟨opened_leaf_lookup opened closed (List.mem_of_getElem? atSlot) inVar,
      by simpa only [Nat.zero_add] using Expr.fvarLeaves_lt_of_wscoped scope leaf inType⟩

/-- Variables in paired slots have their own genuine type at any later use depth. -/
theorem CheckedFramePair.variables_typed {env : Env .anon} {fuel count depth slot : Nat}
    {originalVars finalVars : List (Expr .anon)} (frames : CheckedFramePair env fuel count originalVars finalVars)
    {original final : Expr .anon} (originalAt : originalVars[slot]? = some original)
    (finalAt : finalVars[slot]? = some final) (earlier : slot < depth) :
    Rules.Infer env .full depth original original.fvarTypeD ∧
      Rules.Infer env .full depth final final.fvarTypeD := by
  constructor
  · have indexed := frames.original.indexed slot original originalAt
    have typed : Rules.Infer env .full depth (.fvar slot original.fvarTypeD) original.fvarTypeD := .fvar earlier
    rw [← indexed] at typed
    exact typed
  · have indexed := frames.final.indexed slot final finalAt
    have typed : Rules.Infer env .full depth (.fvar slot final.fvarTypeD) final.fvarTypeD := .fvar earlier
    rw [← indexed] at typed
    exact typed

/-- One pair of genuinely checked variable entries, retaining their distinct type annotations. -/
structure TypedFVarPair (env : Env .anon) (fuel index : Nat) (original final : Expr .anon) : Prop where
  originalIndex : original = .fvar index original.fvarTypeD
  finalIndex : final = .fvar index final.fvarTypeD
  originalScope : Expr.WScoped index original.fvarTypeD ∧ original.fvarTypeD.looseBVarsBounded 0 = true
  finalScope : Expr.WScoped index final.fvarTypeD ∧ final.fvarTypeD.looseBVarsBounded 0 = true
  originalChecked : ∃ inferred level, inferTypeCore .verified env fuel index original.fvarTypeD = .ok inferred ∧
    ensureSortCore .verified env fuel index inferred = .ok level
  finalChecked : ∃ inferred level, inferTypeCore .verified env fuel index final.fvarTypeD = .ok inferred ∧
    ensureSortCore .verified env fuel index inferred = .ok level

theorem CheckedFramePair.entry {env : Env .anon} {fuel count index : Nat}
    {originalVars finalVars : List (Expr .anon)} (frames : CheckedFramePair env fuel count originalVars finalVars)
    {original final : Expr .anon} (originalAt : originalVars[index]? = some original)
    (finalAt : finalVars[index]? = some final) : TypedFVarPair env fuel index original final :=
  ⟨frames.original.indexed index original originalAt, frames.final.indexed index final finalAt,
    frames.original.domainScope index original originalAt, frames.final.domainScope index final finalAt,
    frames.original.domainChecks index original originalAt, frames.final.domainChecks index final finalAt⟩

/-- An application inside an actual domain check exposes its real argument comparison. -/
theorem CheckedFVarFrame.application_check {env : Env .anon} {fuel slot : Nat} {fvars : List (Expr .anon)}
    (frame : CheckedFVarFrame env fuel fvars) {fv functionExpr argument : Expr .anon}
    (atSlot : fvars[slot]? = some fv) (shape : fv.fvarTypeD = .app functionExpr argument) :
    ∃ inferred level functionType expectedDomain resultBody metadata argumentType,
      inferTypeCore .verified env fuel slot fv.fvarTypeD = .ok inferred ∧
      ensureSortCore .verified env fuel slot inferred = .ok level ∧
      Rules.Infer env .full slot functionExpr functionType ∧
      Rules.Red env slot functionType (.forallE expectedDomain resultBody metadata) ∧
      Rules.Infer env .full slot argument argumentType ∧
      Rules.DefEq env slot argumentType expectedDomain ∧ inferred = resultBody.instantiate1 argument := by
  obtain ⟨inferred, level, typed, sorted⟩ := frame.domainChecks slot fv atSlot
  have application := Rules.inferTypeCore_bridge typed
  rw [shape] at application
  obtain ⟨functionType, expectedDomain, resultBody, metadata, argumentType,
    functionTyped, functionReduced, argumentTyped, compared, result⟩ := Rules.Infer.app_inv application
  exact ⟨inferred, level, functionType, expectedDomain, resultBody, metadata, argumentType,
    typed, sorted, functionTyped, functionReduced, argumentTyped, compared, result⟩

/-- The actual constructor run produces the paired typed frames with the same rebuilt witness. -/
theorem checkSumCtor_frame_trace {before env : Env .anon} (wellFormed : EnvWF env)
    {T : Key .anon} {levels : List LevelParam} {nP nI nF fuel : Nat}
    {sortLevel : Level} {isProp large : Bool} {raw former checked : ConstantVal .anon} {sorts : List Level}
    (run : checkSumCtor (fueledOps .verified fuel) before env T levels nP nI sortLevel isProp large
      raw nF former = .ok (checked, sorts)) :
    ∃ initial rebuilt originalVars originalResidual finalVars finalResidual,
      checkConstantVal (fueledOps .verified fuel) env raw = .ok initial ∧
      normCtorVal (fueledOps .verified fuel) env T nP nF raw initial = .ok checked ∧
      ConstructorRebuildRun env fuel T nP nF initial.type rebuilt ∧
      (checked = initial ∨ checkConstantVal (fueledOps .verified fuel) env { raw with type := rebuilt } = .ok checked) ∧
      openPisAtFvars (nP + nF) initial.type 0 = some (originalVars, originalResidual) ∧
      openPisAtFvars (nP + nF) checked.type 0 = some (finalVars, finalResidual) ∧
      CheckedFramePair env fuel (nP + nF) originalVars finalVars := by
  obtain ⟨initial, rebuilt, originalVars, originalResidual, finalVars, finalResidual,
    first, normalized, rebuild, lastBranch, originalOpen, finalOpen, originalLength, finalLength, _⟩ :=
    checkSumCtor_rebuild_domain_checks wellFormed run
  have finalFrame : CheckedFVarFrame env fuel finalVars := by
    rcases lastBranch with same | lastCheck
    · apply checkedFVarFrame_of_check first
      simpa only [same] using finalOpen
    · exact checkedFVarFrame_of_check lastCheck finalOpen
  exact ⟨initial, rebuilt, originalVars, originalResidual, finalVars, finalResidual,
    first, normalized, rebuild, lastBranch, originalOpen, finalOpen,
    checkedFVarFrame_of_check first originalOpen, finalFrame, originalLength, finalLength⟩

end IxVM.Refinement.Decl
