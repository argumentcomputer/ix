import Aiur.Circuit.Indicator

namespace Aiur.Circuit.Compiler

variable {F : Type} {rom : WireROM F}

/-- All leaves of a symbolic tuple refer only to allocated variables. -/
def Bounded (bound : Nat) (value : Symbolic F) : Prop :=
  ∀ polynomial ∈ value.words, polynomial.inBounds bound = true

@[simp] theorem bounded_field {bound : Nat} {polynomial : ArithExpr F} :
    Bounded bound (.field polynomial) ↔ polynomial.inBounds bound = true := by
  simp [Bounded, WireValue.field, WireValue.ptr]

@[simp] theorem bounded_ptr {bound : Nat} {target : Ty} {address : ArithExpr F} :
    Bounded bound (.ptr target address) ↔ address.inBounds bound = true := by
  simp [Bounded, WireValue.field, WireValue.ptr]

@[simp] theorem bounded_tuple {bound : Nat} {values : List (Symbolic F)} :
    Bounded bound (.tuple values) ↔ ∀ value ∈ values, Bounded bound value := by
  simp only [Bounded, WireValue.tuple, List.mem_flatMap, forall_exists_index, and_imp]
  constructor
  · intro h value member p leaf
    exact h p value member leaf
  · intro h p value member leaf
    exact h value member p leaf

theorem Bounded.mono {before after : Nat} (increase : before ≤ after)
    {value : Symbolic F} (bounded : Bounded before value) : Bounded after value :=
  fun p member => Scalar.Circuit.ArithExpr.inBounds_mono increase (bounded p member)

def LocalsBounded (bound : Nat) (locals : Locals F) : Prop :=
  ∀ binding ∈ locals, Bounded bound binding.2

theorem LocalsBounded.mono {before after : Nat} (increase : before ≤ after)
    {locals : Locals F} (bounded : LocalsBounded before locals) : LocalsBounded after locals :=
  fun binding member => (bounded binding member).mono increase

@[simp] theorem localsBounded_append {bound : Nat} {left right : Locals F} :
    LocalsBounded bound (left ++ right) ↔ LocalsBounded bound left ∧ LocalsBounded bound right := by
  simp [LocalsBounded, or_imp, forall_and]

structure BuildState.WellFormed (state : BuildState F) : Prop where
  constraints : ∀ polynomial ∈ state.constraints.toList, polynomial.inBounds state.nextVar = true
  sends : ∀ send ∈ state.sends.toList, send.inBounds state.nextVar = true
  memory : ∀ lookup ∈ state.memory.toList, lookup.inBounds state.nextVar = true

theorem Send_bounds_mono {send : Send F} {before after : Nat} (increase : before ≤ after)
    (bounded : send.inBounds before = true) : send.inBounds after = true := by
  simp only [Send.inBounds, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at bounded ⊢
  exact ⟨⟨fun id member => lt_of_lt_of_le (bounded.1.1 id member) increase,
    Scalar.Circuit.ArithExpr.inBounds_mono increase bounded.1.2⟩,
    fun polynomial member => Scalar.Circuit.ArithExpr.inBounds_mono increase (bounded.2 polynomial member)⟩

theorem MemoryLookup_bounds_mono {lookup : MemoryLookup F} {before after : Nat}
    (increase : before ≤ after) (bounded : lookup.inBounds before = true) :
    lookup.inBounds after = true := by
  simp only [MemoryLookup.inBounds, Bool.and_eq_true, List.all_eq_true] at bounded ⊢
  exact ⟨⟨Scalar.Circuit.ArithExpr.inBounds_mono increase bounded.1.1,
    Scalar.Circuit.ArithExpr.inBounds_mono increase bounded.1.2⟩,
    fun p member => Scalar.Circuit.ArithExpr.inBounds_mono increase (bounded.2 p member)⟩

theorem BuildState.WellFormed.grow {state : BuildState F} (layout : state.WellFormed)
    {bound : Nat} (increase : state.nextVar ≤ bound) :
    { state with nextVar := bound }.WellFormed :=
  ⟨fun p member => Scalar.Circuit.ArithExpr.inBounds_mono increase (layout.constraints p member),
    fun send member => Send_bounds_mono increase (layout.sends send member),
    fun lookup member => MemoryLookup_bounds_mono increase (layout.memory lookup member)⟩

theorem BuildState.WellFormed.constrain {state : BuildState F} (layout : state.WellFormed)
    {polynomial : ArithExpr F} (bounded : polynomial.inBounds state.nextVar = true) :
    { state with constraints := state.constraints.push polynomial }.WellFormed := by
  refine ⟨?_, layout.sends, layout.memory⟩
  intro p member
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact layout.constraints p member
  · exact bounded

theorem BuildState.Valid.constrain [Field F] {state : BuildState F} {calls : CallRelation F}
    {assignment : Var → F} (valid : state.Valid rom calls assignment) {polynomial : ArithExpr F}
    (zero : polynomial.denote assignment = 0) :
    { state with constraints := state.constraints.push polynomial }.Valid rom calls assignment := by
  refine ⟨?_, valid.calls, valid.memory⟩
  intro p member
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact valid.constraints p member
  · exact zero

theorem BuildState.Valid.of_agree [Field F] {state : BuildState F} {calls : CallRelation F}
    {before after : Var → F} (valid : state.Valid rom calls before) (layout : state.WellFormed)
    (agree : ∀ id < state.nextVar, after id = before id) : state.Valid rom calls after := by
  constructor
  · intro p member
    rw [Scalar.Circuit.ArithExpr.denote_eq_of_agree agree (layout.constraints p member)]
    exact valid.constraints p member
  · intro send member active
    have bounded := layout.sends send member
    simp only [Send.inBounds, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at bounded
    have enabled : send.enable.denote after = send.enable.denote before :=
      Scalar.Circuit.ArithExpr.denote_eq_of_agree agree bounded.1.2
    have result : send.result.map after = send.result.map before :=
      WireValue.map_congr _ (fun id inside => agree id (bounded.1.1 id inside))
    have args : send.args.map (WireValue.map (ArithExpr.denote after)) =
        send.args.map (WireValue.map (ArithExpr.denote before)) := by
      apply List.map_congr_left
      intro value inside
      apply WireValue.map_congr
      intro p leaf
      exact Scalar.Circuit.ArithExpr.denote_eq_of_agree agree
        (bounded.2 p (List.mem_flatMap.mpr ⟨value, inside, leaf⟩))
    rw [args, result]
    exact valid.calls send member (enabled.symm.trans active)

  · intro lookup member active
    have bounded := layout.memory lookup member
    simp only [MemoryLookup.inBounds, Bool.and_eq_true, List.all_eq_true] at bounded
    have enabled := Scalar.Circuit.ArithExpr.denote_eq_of_agree agree bounded.1.2
    have address := Scalar.Circuit.ArithExpr.denote_eq_of_agree agree bounded.1.1
    have value := WireValue.map_congr lookup.value
      (fun p leaf => Scalar.Circuit.ArithExpr.denote_eq_of_agree agree (bounded.2 p leaf))
    change (lookup.address.denote after, lookup.value.map (ArithExpr.denote after)) ∈ rom.entries
    change lookup.address.denote after = lookup.address.denote before at address
    rw [address, value]
    exact valid.memory lookup member (enabled.symm.trans active)

/-- A witness extends the allocation frontier and preserves every old variable. -/
structure Extension [Field F] (rom : WireROM F) (calls : CallRelation F) (before after : BuildState F)
    (initial assignment : Var → F) : Prop where
  increase : before.nextVar ≤ after.nextVar
  agree : ∀ id < before.nextVar, assignment id = initial id
  layout : after.WellFormed
  valid : after.Valid rom calls assignment

theorem Extension.refl [Field F] {calls : CallRelation F} {state : BuildState F}
    {assignment : Var → F} (layout : state.WellFormed) (valid : state.Valid rom calls assignment) :
    Extension rom calls state state assignment assignment := ⟨le_rfl, by intros; rfl, layout, valid⟩

theorem Extension.trans [Field F] {calls : CallRelation F} {s₁ s₂ s₃ : BuildState F}
    {a₁ a₂ a₃ : Var → F} (left : Extension rom calls s₁ s₂ a₁ a₂)
    (right : Extension rom calls s₂ s₃ a₂ a₃) : Extension rom calls s₁ s₃ a₁ a₃ :=
  ⟨left.increase.trans right.increase,
    fun id bound => (right.agree id (lt_of_lt_of_le bound left.increase)).trans (left.agree id bound),
    right.layout, right.valid⟩

theorem Extension.polynomial [Field F] {calls : CallRelation F} {before after : BuildState F}
    {a b : Var → F} (extension : Extension rom calls before after a b) {p : ArithExpr F}
    (bounded : p.inBounds before.nextVar = true) : p.denote b = p.denote a :=
  Scalar.Circuit.ArithExpr.denote_eq_of_agree extension.agree bounded

theorem Extension.value [Field F] {calls : CallRelation F} {before after : BuildState F}
    {a b : Var → F} (extension : Extension rom calls before after a b) {value : Symbolic F}
    (bounded : Bounded before.nextVar value) :
    value.map (ArithExpr.denote b) = value.map (ArithExpr.denote a) :=
  WireValue.map_congr _ (fun p member => extension.polynomial (bounded p member))

theorem Extension.locals [Field F] {calls : CallRelation F} {before after : BuildState F}
    {a b : Var → F} (extension : Extension rom calls before after a b) {locals : Locals F}
    (bounded : LocalsBounded before.nextVar locals) : localsEnvironment locals b = localsEnvironment locals a := by
  apply List.map_congr_left
  intro binding member
  simp only [extension.value (bounded binding member)]

theorem Extension.variables [Field F] {calls : CallRelation F} {before after : BuildState F}
    {a b : Var → F} (extension : Extension rom calls before after a b) {value : WireValue Var}
    (bounded : Bounded (F := F) before.nextVar (value.map ArithExpr.var)) : value.map b = value.map a := by
  simpa only [WireValue.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote] using extension.value bounded

theorem fresh_complete [Field F] {calls : CallRelation F} {before after : BuildState F} {id : Var}
    (compiled : fresh before = .ok (id, after)) {initial : Var → F}
    (layout : before.WellFormed) (valid : before.Valid rom calls initial) (value : F) :
    ∃ assignment, Extension rom calls before after initial assignment ∧
      id < after.nextVar ∧ assignment id = value := by
  simp only [fresh_apply, Except.ok.injEq, Prod.mk.injEq] at compiled
  obtain ⟨rfl, rfl⟩ := compiled
  let assignment := Function.update initial before.nextVar value
  have agree : ∀ id < before.nextVar, assignment id = initial id := by
    intro id bounded
    exact Function.update_of_ne (Nat.ne_of_lt bounded) _ _
  have oldValid := valid.of_agree layout agree
  exact ⟨assignment, ⟨Nat.le_succ _, agree, layout.grow (Nat.le_succ _),
    ⟨oldValid.constraints, oldValid.calls, oldValid.memory⟩⟩, Nat.lt_succ_self _, by simp [assignment]⟩

theorem constrain_complete [Field F] {calls : CallRelation F} {before after : BuildState F}
    {p : ArithExpr F} (compiled : constrain p before = .ok ((), after)) {assignment : Var → F}
    (layout : before.WellFormed) (valid : before.Valid rom calls assignment)
    (bounded : p.inBounds before.nextVar = true) (zero : p.denote assignment = 0) :
    Extension rom calls before after assignment assignment := by
  simp only [constrain_apply, Except.ok.injEq, Prod.mk.injEq, true_and] at compiled
  subst after
  exact ⟨le_rfl, by intros; rfl, layout.constrain bounded, valid.constrain zero⟩

theorem boolean_complete [Field F] {calls : CallRelation F} {before after : BuildState F}
    {p : ArithExpr F} (compiled : boolean p before = .ok ((), after)) {assignment : Var → F}
    (layout : before.WellFormed) (valid : before.Valid rom calls assignment)
    (bounded : p.inBounds before.nextVar = true) (value : p.denote assignment = 0 ∨ p.denote assignment = 1) :
    Extension rom calls before after assignment assignment := by
  apply constrain_complete compiled layout valid
  · simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using bounded
  · rcases value with zero | one <;>
      simp [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote, *]

theorem Extension.bound [Field F] {calls : CallRelation F} {before after : BuildState F}
    {a b : Var → F} (extension : Extension rom calls before after a b) {p : ArithExpr F}
    (bounded : p.inBounds before.nextVar = true) : p.inBounds after.nextVar = true :=
  Scalar.Circuit.ArithExpr.inBounds_mono extension.increase bounded

theorem Extension.values [Field F] {calls : CallRelation F} {before after : BuildState F}
    {a b : Var → F} (extension : Extension rom calls before after a b) {values : List (Symbolic F)}
    (bounded : ∀ value ∈ values, Bounded before.nextVar value) :
    values.map (WireValue.map (ArithExpr.denote b)) = values.map (WireValue.map (ArithExpr.denote a)) :=
  List.map_congr_left (fun value member => extension.value (bounded value member))

theorem send_complete [Field F] {calls : CallRelation F} {before : BuildState F}
    {assignment : Var → F} (layout : before.WellFormed) (valid : before.Valid rom calls assignment)
    (send : Send F) (bounded : send.inBounds before.nextVar = true)
    (called : send.enable.denote assignment = 1 →
      calls send.channel (send.args.map (WireValue.map (ArithExpr.denote assignment))) (send.result.map assignment)) :
    Extension rom calls before { before with sends := before.sends.push send } assignment assignment := by
  refine ⟨le_rfl, by intros; rfl, ⟨layout.constraints, ?_, layout.memory⟩, ⟨valid.constraints, ?_, valid.memory⟩⟩
  · intro next member
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact layout.sends next member
    · exact bounded
  · intro next member active
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact valid.calls next member active
    · exact called active

theorem send_bounded {name : String} {args : List (Symbolic F)} {result : WireValue Var}
    {enable : ArithExpr F} {bound : Nat}
    (argsBound : ∀ value ∈ args, Bounded bound value)
    (resultBound : Bounded (F := F) bound (result.map ArithExpr.var))
    (enableBound : enable.inBounds bound = true) :
    (⟨name, args, result, enable⟩ : Send F).inBounds bound = true := by
  simp only [Send.inBounds, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨⟨?_, enableBound⟩, ?_⟩
  · intro id member
    have := resultBound (.var id) (by simpa only [WireValue.words_map, List.mem_map] using
      (show ∃ x ∈ result.words, ArithExpr.var x = .var id from ⟨id, member, rfl⟩))
    simpa only [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds, decide_eq_true_eq] using this
  · intro p member
    obtain ⟨value, member, leaf⟩ := List.mem_flatMap.mp member
    exact argsBound value member p leaf

theorem guarded_complete [Field F] {calls : CallRelation F} {before after : BuildState F}
    {enable polynomial : ArithExpr F}
    (compiled : guarded enable polynomial before = .ok ((), after)) {assignment : Var → F}
    (layout : before.WellFormed) (valid : before.Valid rom calls assignment)
    (enableBound : enable.inBounds before.nextVar = true)
    (polyBound : polynomial.inBounds before.nextVar = true)
    (zero : enable.denote assignment = 0 ∨ polynomial.denote assignment = 0) :
    Extension rom calls before after assignment assignment := by
  apply constrain_complete compiled layout valid
  · simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using And.intro enableBound polyBound
  · change enable.denote assignment * polynomial.denote assignment = 0
    exact mul_eq_zero.mpr zero

theorem requireCell_complete [Field F] {calls : CallRelation F} {before after : BuildState F}
    {enable address : ArithExpr F} {value : Symbolic F}
    (compiled : requireCell enable address value before = .ok ((), after)) {assignment : Var → F}
    (layout : before.WellFormed) (valid : before.Valid rom calls assignment)
    (enableBound : enable.inBounds before.nextVar = true)
    (addressBound : address.inBounds before.nextVar = true)
    (valueBound : Bounded before.nextVar value)
    (cell : enable.denote assignment = 1 →
      (address.denote assignment, value.map (ArithExpr.denote assignment)) ∈ rom.entries) :
    Extension rom calls before after assignment assignment := by
  simp only [requireCell_apply, Except.ok.injEq, Prod.mk.injEq, true_and] at compiled
  subst after
  refine ⟨le_rfl, by intros; rfl, ⟨layout.constraints, layout.sends, ?_⟩,
    ⟨valid.constraints, valid.calls, ?_⟩⟩
  · intro lookup member
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact layout.memory lookup member
    · simpa [MemoryLookup.inBounds, List.all_eq_true] using ⟨⟨addressBound, enableBound⟩, valueBound⟩
  · intro lookup member
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact valid.memory lookup member
    · exact cell

end Aiur.Circuit.Compiler
