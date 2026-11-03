import Aiur.Optimized.ReferenceState
import Aiur.Optimized.BranchFacts
import Aiur.Circuit.EncodingWitness

namespace Aiur.Optimized.Compiler

variable {F : Type} [Field F] [DecidableEq F]

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

theorem equations_scopes {scope : ScopeId} {conditions : List (Polynomial F)} {before after : State F}
    (compiled : (do for condition in conditions do equation scope condition : Build F Unit)
      before = .ok ((), after)) : after.scopes = before.scopes := by
  induction conditions generalizing before with
  | nil =>
      have same : before = after := by
        simpa [List.forIn_nil, pure, StateT.pure, StateT.bind, bind, Except.bind, Except.pure] using compiled
      exact congrArg State.scopes same.symm
  | cons condition conditions ih =>
      simp [List.forIn_cons, equation, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
        StateT.bind, bind, Except.bind, StateT.pure, pure, Except.pure] at compiled
      exact ih (before := {before with equations := before.equations.push ⟨scope, condition⟩}) compiled

theorem equations_complete {scope : ScopeId} {conditions : List (Polynomial F)} {before after : State F}
    (compiled : (do for condition in conditions do equation scope condition : Build F Unit)
      before = .ok ((), after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {assignment : Witness → F}
    (layout : before.toReference.WellFormed) (valid : before.Valid rom calls assignment)
    (scopeBound : (before.activation scope).inBounds before.roles.size = true)
    (bounded : ∀ condition ∈ conditions, condition.inBounds before.roles.size = true)
    (zero : (before.activation scope).denote assignment = 0 ∨
      ∀ condition ∈ conditions, condition.denote assignment = 0) :
    Extension rom calls before after assignment assignment := by
  induction conditions generalizing before with
  | nil =>
      have same : before = after := by
        simpa [List.forIn_nil, pure, StateT.pure, StateT.bind, bind, Except.bind, Except.pure] using compiled
      subst after
      exact .refl layout ((before.valid_iff_reference rom calls assignment).mp valid)
  | cons condition conditions ih =>
      simp [List.forIn_cons, equation, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
        StateT.bind, bind, Except.bind, StateT.pure, pure, Except.pure] at compiled
      have step := equation_complete (scope := scope) (polynomial := condition) (before := before) rfl
        layout valid (by simp [Scalar.Circuit.ArithExpr.inBounds, scopeBound, bounded condition (by simp)]) (by
          rcases zero with inactive | zeros
          · simp [inactive]
          · simp [zeros condition (by simp)])
      exact step.trans (ih (before := {before with equations := before.equations.push ⟨scope, condition⟩})
        compiled step.layout step.validAssignment scopeBound
        (fun p member => bounded p (by simp [member]))
        (zero.imp_right (fun zeros p member => zeros p (by simp [member]))))

theorem equalValue_complete {scope : ScopeId} {left right : Symbolic F} {before after : State F}
    (compiled : equalValue scope left right before = .ok ((), after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {assignment : Witness → F}
    (layout : before.toReference.WellFormed) (valid : before.Valid rom calls assignment)
    (scopeBound : (before.activation scope).inBounds before.roles.size = true)
    (leftBound : Circuit.Compiler.Bounded before.roles.size left)
    (rightBound : Circuit.Compiler.Bounded before.roles.size right)
    (equal : (before.activation scope).denote assignment = 0 ∨
      left.map (Circuit.ArithExpr.denote assignment) = right.map (Circuit.ArithExpr.denote assignment)) :
    Extension rom calls before after assignment assignment := by
  simp only [equalValue] at compiled
  split at compiled
  · simp [StateT.bind, bind, Except.bind] at compiled
  · obtain ⟨⟨⟩, middle, unchanged, rest⟩ := bind_ok.mp compiled
    obtain ⟨_, rfl⟩ := pure_ok.mp unchanged
    have equations : (do
        for polynomial in (left.words.zip right.words).map (fun (a, b) => Polynomial.sub a b) do
          equation scope polynomial : Build F Unit) before = .ok ((), after) := by
      simpa only [List.forIn_map] using rest
    apply equations_complete equations layout valid scopeBound
    · intro polynomial member
      obtain ⟨⟨a, b⟩, pairMember, rfl⟩ := List.mem_map.mp member
      have members := List.of_mem_zip pairMember
      simp [Scalar.Circuit.ArithExpr.inBounds, leftBound _ members.1, rightBound _ members.2]
    · rcases equal with inactive | equal
      · exact Or.inl inactive
      · right
        intro polynomial member
        obtain ⟨⟨a, b⟩, pairMember, rfl⟩ := List.mem_map.mp member
        have wordsEq := congrArg WireValue.words equal
        have mapped : (a.denote assignment, b.denote assignment) ∈
            (left.words.map (Circuit.ArithExpr.denote assignment)).zip
              (right.words.map (Circuit.ArithExpr.denote assignment)) := by
          rw [List.zip_map]
          exact List.mem_map.mpr ⟨(a, b), pairMember, rfl⟩
        change left.words.map (Circuit.ArithExpr.denote assignment) =
          right.words.map (Circuit.ArithExpr.denote assignment) at wordsEq
        rw [wordsEq, List.zip_eq_zipWith, List.zipWith_self] at mapped
        obtain ⟨word, _, pairEq⟩ := List.mem_map.mp mapped
        have pair := Prod.mk.inj pairEq
        change a.denote assignment - b.denote assignment = 0
        exact sub_eq_zero.mpr (pair.1.symm.trans pair.2)

theorem freshValue_decoded_complete {decls : Declarations}
    (checked : checkDeclarations decls = .ok ()) (tags : decls.tagsValid F = true)
    {role : Role} {type : Ty} {vars : WireValue Witness} {before after : State F}
    (compiled : freshValue decls role type before = .ok (vars, after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {initial : Witness → F}
    (layout : before.toReference.WellFormed) (valid : before.Valid rom calls initial)
    (value : Value F) (shape : value.type = type) (formed : value.wellFormed decls = true) :
    ∃ assignment, Extension rom calls before after initial assignment ∧
      Circuit.Compiler.Bounded (F := F) after.roles.size (vars.map Polynomial.var) ∧
      (vars.map assignment).decode decls = some value :=
  Circuit.Compiler.freshValue_decoded_complete checked tags (freshValue_reference compiled) layout
    ((before.valid_iff_reference rom calls initial).mp valid) value shape formed

theorem freshValue_zero_complete {decls : Declarations} {role : Role} {type : Ty}
    {vars : WireValue Witness} {before after : State F}
    (compiled : freshValue decls role type before = .ok (vars, after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {initial : Witness → F}
    (layout : before.toReference.WellFormed) (valid : before.Valid rom calls initial) :
    ∃ assignment, Extension rom calls before after initial assignment ∧
      Circuit.Compiler.Bounded (F := F) after.roles.size (vars.map Polynomial.var) :=
  Circuit.Compiler.freshValue_zero_complete (freshValue_reference compiled) layout
    ((before.valid_iff_reference rom calls initial).mp valid)

theorem destination_complete {decls : Declarations} {scope : ScopeId} {type : Ty}
    {target : Option (WireValue Witness)} {vars : WireValue Witness} {before after : State F}
    (compiled : destination decls scope type target before = .ok (vars, after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {initial : Witness → F}
    (layout : before.toReference.WellFormed) (valid : before.Valid rom calls initial)
    (value : WireValue F) (shape : value.type = type) (sized : value.Sized decls)
    (targetBound : ∀ candidate, target = some candidate →
      Circuit.Compiler.Bounded (F := F) before.roles.size (candidate.map Polynomial.var))
    (targetValue : ∀ candidate, target = some candidate → candidate.map initial = value) :
    ∃ assignment, Extension rom calls before after initial assignment ∧
      Circuit.Compiler.Bounded (F := F) after.roles.size (vars.map Polynomial.var) ∧ vars.map assignment = value := by
  cases target with
  | none =>
      exact freshValue_complete (by simpa [destination] using compiled) layout valid value shape sized
  | some candidate =>
      simp only [destination] at compiled
      split at compiled
      · simp [StateT.bind, bind, Except.bind] at compiled
      · obtain ⟨⟨⟩, middle, unchanged, finished⟩ := bind_ok.mp compiled
        obtain ⟨_, rfl⟩ := pure_ok.mp unchanged
        obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
        exact ⟨initial, .refl layout ((before.valid_iff_reference rom calls initial).mp valid),
          targetBound _ rfl, targetValue _ rfl⟩

theorem destination_inactive {decls : Declarations} {scope : ScopeId} {type : Ty}
    {target : Option (WireValue Witness)} {vars : WireValue Witness} {before after : State F}
    (compiled : destination decls scope type target before = .ok (vars, after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {initial : Witness → F}
    (layout : before.toReference.WellFormed) (valid : before.Valid rom calls initial)
    (targetBound : ∀ candidate, target = some candidate →
      Circuit.Compiler.Bounded (F := F) before.roles.size (candidate.map Polynomial.var)) :
    ∃ assignment, Extension rom calls before after initial assignment ∧
      Circuit.Compiler.Bounded (F := F) after.roles.size (vars.map Polynomial.var) := by
  cases target with
  | none =>
      exact freshValue_zero_complete (by simpa [destination] using compiled) layout valid
  | some candidate =>
      simp only [destination] at compiled
      split at compiled
      · simp [StateT.bind, bind, Except.bind] at compiled
      · obtain ⟨⟨⟩, middle, unchanged, finished⟩ := bind_ok.mp compiled
        obtain ⟨_, rfl⟩ := pure_ok.mp unchanged
        obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
        exact ⟨initial, .refl layout ((before.valid_iff_reference rom calls initial).mp valid), targetBound _ rfl⟩

theorem destination_decoded_complete {decls : Declarations}
    (checked : checkDeclarations decls = .ok ()) (tags : decls.tagsValid F = true)
    {scope : ScopeId} {type : Ty} {target : Option (WireValue Witness)}
    {vars : WireValue Witness} {before after : State F}
    (compiled : destination decls scope type target before = .ok (vars, after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {initial : Witness → F}
    (layout : before.toReference.WellFormed) (valid : before.Valid rom calls initial)
    (value : Value F) (shape : value.type = type) (formed : value.wellFormed decls = true)
    (targetBound : ∀ candidate, target = some candidate →
      Circuit.Compiler.Bounded (F := F) before.roles.size (candidate.map Polynomial.var))
    (targetDecode : ∀ candidate, target = some candidate → (candidate.map initial).decode decls = some value) :
    ∃ assignment, Extension rom calls before after initial assignment ∧
      Circuit.Compiler.Bounded (F := F) after.roles.size (vars.map Polynomial.var) ∧
      (vars.map assignment).decode decls = some value := by
  cases target with
  | none =>
      exact freshValue_decoded_complete checked tags (by simpa [destination] using compiled)
        layout valid value shape formed
  | some candidate =>
      simp only [destination] at compiled
      split at compiled
      · simp [StateT.bind, bind, Except.bind] at compiled
      · obtain ⟨⟨⟩, middle, unchanged, finished⟩ := bind_ok.mp compiled
        obtain ⟨_, rfl⟩ := pure_ok.mp unchanged
        obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
        exact ⟨initial, .refl layout ((before.valid_iff_reference rom calls initial).mp valid),
          targetBound _ rfl, targetDecode _ rfl⟩

private theorem failure_terms_complete {scope : ScopeId} {conditions terms : List (Polynomial F)}
    {before after : State F}
    (compiled : (conditions.mapM fun difference => do
      return Polynomial.mul difference (.var (← fresh (.auxiliary scope))) : Build F (List (Polynomial F)))
        before = .ok (terms, after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {initial : Witness → F}
    (layout : before.toReference.WellFormed) (valid : before.Valid rom calls initial)
    (bounded : ∀ condition ∈ conditions, condition.inBounds before.roles.size = true)
    (coefficients : List F) (sized : coefficients.length = conditions.length) :
    ∃ assignment, Extension rom calls before after initial assignment ∧
      after.scopes = before.scopes ∧
      (∀ term ∈ terms, term.inBounds after.roles.size = true) ∧
      terms.map (Circuit.ArithExpr.denote assignment) =
        List.zipWith (· * ·) (conditions.map (Circuit.ArithExpr.denote initial)) coefficients := by
  induction conditions generalizing terms before initial coefficients with
  | nil =>
      cases coefficients with
      | cons => simp at sized
      | nil =>
          obtain ⟨rfl, rfl⟩ := pure_ok.mp (by simpa only [List.mapM_nil] using compiled)
          exact ⟨initial, .refl layout ((before.valid_iff_reference rom calls initial).mp valid),
            rfl, by simp, rfl⟩
  | cons difference conditions ih =>
      cases coefficients with
      | nil => simp at sized
      | cons coefficient coefficients =>
          simp only [List.mapM_cons] at compiled
          obtain ⟨term, middle, headRun, restBind⟩ := bind_ok.mp compiled
          obtain ⟨tail, last, tailRun, finished⟩ := bind_ok.mp restBind
          obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
          obtain ⟨id, afterFresh, freshRun, headFinished⟩ := bind_ok.mp headRun
          obtain ⟨rfl, rfl⟩ := pure_ok.mp headFinished
          obtain ⟨a, freshExt, idBound, assigned⟩ := fresh_complete freshRun layout valid coefficient
          have scopes : afterFresh.scopes = before.scopes := by
            simpa only using congrArg (fun state : State F => state.scopes) (fresh_eq freshRun).2
          obtain ⟨b, tailExt, tailScopes, tailBound, tailValues⟩ := ih tailRun freshExt.layout
            freshExt.validAssignment (fun p member => freshExt.bound (bounded p (by simp [member])))
              coefficients (by simpa using sized)
          have differenceBound := bounded difference (by simp)
          have varBound : (Polynomial.var id : Polynomial F).inBounds afterFresh.roles.size = true := by
            simpa [Scalar.Circuit.ArithExpr.inBounds] using idBound
          refine ⟨b, freshExt.trans tailExt, tailScopes.trans scopes, ?_, ?_⟩
          · intro p member
            rcases List.mem_cons.mp member with rfl | member
            · simpa [Scalar.Circuit.ArithExpr.inBounds, State.toReference] using
                And.intro ((freshExt.trans tailExt).bound differenceBound) (tailExt.bound varBound)
            · exact tailBound p member
          · have tailInputs : conditions.map (Circuit.ArithExpr.denote a) =
                conditions.map (Circuit.ArithExpr.denote initial) :=
              List.map_congr_left (fun p member => freshExt.polynomial (bounded p (by simp [member])))
            have varValue : b id = coefficient := (tailExt.agree id idBound).trans assigned
            simp only [List.map_cons, List.zipWith_cons_cons, Scalar.Circuit.ArithExpr.denote,
              (freshExt.trans tailExt).polynomial differenceBound, varValue, tailValues, tailInputs]

private theorem sum_zipWith_eq_combination (left right : List F) :
    (List.zipWith (· * ·) left right).sum = combination left right := by
  induction left generalizing right with
  | nil => simp [combination]
  | cons head tail ih =>
      cases right <;> simp [combination, ih]

/-- A failed earlier pattern has a finite list of inverse coefficients. The
construction allocates exactly the witnesses used by the executable compiler. -/
theorem failure_complete {scope : ScopeId} {conditions : List (Polynomial F)} {before after : State F}
    (compiled : failure scope conditions before = .ok ((), after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {initial : Witness → F}
    (layout : before.toReference.WellFormed) (valid : before.Valid rom calls initial)
    (scopeBound : (before.activation scope).inBounds before.roles.size = true)
    (bounded : ∀ condition ∈ conditions, condition.inBounds before.roles.size = true)
    (failed : (before.activation scope).denote initial = 0 ∨
      ¬ ∀ condition ∈ conditions, condition.denote initial = 0) :
    ∃ assignment, Extension rom calls before after initial assignment := by
  simp only [failure] at compiled
  obtain ⟨terms, middle, termsRun, equationRun⟩ := bind_ok.mp compiled
  have failure : (before.activation scope).denote initial = 0 ∨
      ¬ ∀ value ∈ conditions.map (Circuit.ArithExpr.denote initial), value = 0 := by
    simpa only [List.forall_mem_map] using failed
  obtain ⟨coefficients, sized, certificate⟩ :=
    (guarded_failure_iff ((before.activation scope).denote initial)
      (conditions.map (Circuit.ArithExpr.denote initial))).mpr failure
  obtain ⟨a, ext, scopes, termsBound, termsValue⟩ := failure_terms_complete termsRun layout valid
    bounded coefficients (by simpa using sized)
  have activation : middle.activation scope = before.activation scope := by simp [State.activation, scopes]
  have sumBound : (terms.foldl Polynomial.add (.const (0 : F))).inBounds middle.roles.size = true :=
    Scalar.Circuit.Compiler.foldl_add_inBounds rfl termsBound
  have finalExt := equation_complete equationRun ext.layout ext.validAssignment (by
    simp only [Scalar.Circuit.ArithExpr.inBounds, Bool.and_eq_true, and_true]
    exact ⟨activation ▸ ext.bound scopeBound, sumBound⟩) (by
      rw [activation, ext.polynomial scopeBound]
      change (before.activation scope).denote initial *
        ((terms.foldl Polynomial.add (.const (0 : F))).denote a - 1) = 0
      rw [Scalar.Circuit.ArithExpr.denote_foldl_add, termsValue]
      simpa only [Scalar.Circuit.ArithExpr.denote, zero_add, sum_zipWith_eq_combination] using certificate)
  exact ⟨a, ext.trans finalExt⟩

theorem cell_complete {cell : Cell F} {before after : State F}
    (compiled : (modify (fun state => {state with cells := state.cells.push cell}) : Build F Unit)
      before = .ok ((), after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {assignment : Witness → F}
    (layout : before.toReference.WellFormed) (valid : before.Valid rom calls assignment)
    (scopeBound : (before.activation cell.scope).inBounds before.roles.size = true)
    (addressBound : cell.address.inBounds before.roles.size = true)
    (valueBound : Circuit.Compiler.Bounded before.roles.size cell.value)
    (member : (before.activation cell.scope).denote assignment = 1 →
      (cell.address.denote assignment, cell.value.map (Circuit.ArithExpr.denote assignment)) ∈ rom.entries) :
    Extension rom calls before after assignment assignment := by
  change Except.ok ((), {before with cells := before.cells.push cell}) = Except.ok ((), after) at compiled
  have stateEq := congrArg Prod.snd (Except.ok.inj compiled)
  dsimp only at stateEq
  subst after
  apply Circuit.Compiler.requireCell_complete (enable := before.activation cell.scope)
    (address := cell.address) (value := cell.value) _ layout
    ((before.valid_iff_reference rom calls assignment).mp valid) scopeBound addressBound valueBound member
  simp [Circuit.Compiler.requireCell_apply, State.toReference, State.activation]

theorem call_complete {call : Call F} {before after : State F}
    (compiled : (modify (fun state => {state with calls := state.calls.push call}) : Build F Unit)
      before = .ok ((), after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {assignment : Witness → F}
    (layout : before.toReference.WellFormed) (valid : before.Valid rom calls assignment)
    (scopeBound : (before.activation call.scope).inBounds before.roles.size = true)
    (argsBound : ∀ arg ∈ call.args, Circuit.Compiler.Bounded before.roles.size arg)
    (resultBound : Circuit.Compiler.Bounded (F := F) before.roles.size (call.result.map Polynomial.var))
    (member : (before.activation call.scope).denote assignment = 1 →
      calls call.channel (call.message assignment).args (call.message assignment).result) :
    Extension rom calls before after assignment assignment := by
  change Except.ok ((), {before with calls := before.calls.push call}) = Except.ok ((), after) at compiled
  have stateEq := congrArg Prod.snd (Except.ok.inj compiled)
  dsimp only at stateEq
  subst after
  have reference := Circuit.Compiler.send_complete layout
    ((before.valid_iff_reference rom calls assignment).mp valid)
    ⟨call.channel, call.args, call.result, before.activation call.scope⟩
    (Circuit.Compiler.send_bounded argsBound resultBound scopeBound) member
  simpa only [Extension, State.toReference, State.activation, Array.map_push] using reference

end Aiur.Optimized.Compiler
