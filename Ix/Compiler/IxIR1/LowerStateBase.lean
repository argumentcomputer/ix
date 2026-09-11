import Ix.Compiler.IxIR1.Lower

/-!
# Structural compile-environment invariants

State-only facts needed by the semantic lowering proof, kept below
`LowerSim` in the import graph.  In particular, ordinary function bodies
start without the synthetic recursor-self entry and successful lowering
never invents one.
-/

namespace Ix.Compiler.IxIR1.Lower

open Ix.Compiler.Ixon (Owned Uses)

/-- No logical entry advertises the recursor-only `callSelf` capability. -/
def NoRecSelf (input : VEnv) : Prop :=
  ∀ (index arity : Nat),
    input.entries[index]? ≠ some (VEntry.recSelf arity)

theorem NoRecSelf.empty : NoRecSelf ⟨[], depth⟩ := by
  intro index arity
  simp

theorem NoRecSelf.bump {input : VEnv} (h : NoRecSelf input) :
    NoRecSelf input.bump := by
  simpa [NoRecSelf, VEnv.bump] using h

theorem NoRecSelf.setSlot {input : VEnv} (h : NoRecSelf input)
    (changed abs remaining : Nat) (uses : Uses) (held : Bool) :
    NoRecSelf
      (input.setEntry changed (.slot abs remaining uses held)) := by
  intro index arity hentry
  by_cases heq : changed = index
  · subst index
    rw [VEnv.setEntry, List.getElem?_set] at hentry
    simp at hentry
  · rw [VEnv.setEntry, List.getElem?_set] at hentry
    simp [heq] at hentry
    exact h index arity hentry

theorem NoRecSelf.consSlot {input : VEnv} (h : NoRecSelf input)
    (abs remaining : Nat) (uses : Uses) (held : Bool) :
    NoRecSelf
      { input with
        entries := .slot abs remaining uses held :: input.entries } := by
  intro index arity hentry
  cases index with
  | zero => simp at hentry
  | succ index =>
    exact h index arity (by simpa using hentry)

theorem NoRecSelf.pop {input : VEnv} (h : NoRecSelf input) :
    NoRecSelf input.pop := by
  intro index arity hentry
  exact h (index + 1) arity (by simpa [VEnv.pop] using hentry)

theorem NoRecSelf.of_entries_eq {input output : VEnv}
    (h : NoRecSelf input) (hentries : output.entries = input.entries) :
    NoRecSelf output := by
  simpa [NoRecSelf, hentries] using h

theorem NoRecSelf.of_mem_not_recSelf (input : VEnv)
    (hentries : ∀ entry ∈ input.entries, ∀ arity,
      entry ≠ VEntry.recSelf arity) :
    NoRecSelf input := by
  intro index arity hentry
  obtain ⟨hindex, heq⟩ := List.getElem?_eq_some_iff.mp hentry
  have hmember : VEntry.recSelf arity ∈ input.entries := by
    rw [← heq]
    exact List.getElem_mem hindex
  exact hentries (.recSelf arity) hmember arity rfl

private theorem parameterEntries_mem_not_recSelf (base : Nat) :
    ∀ (modes : List Uses) (remaining : Nat → Nat) entry,
      entry ∈ parameterEntries base modes remaining →
      ∀ arity, entry ≠ VEntry.recSelf arity := by
  intro modes remaining
  exact parameterEntries_traverse remaining
    (Result := fun _ _ entries =>
      ∀ entry ∈ entries, ∀ arity, entry ≠ VEntry.recSelf arity)
    (hnil := by
      intro current entry hmember
      simp at hmember)
    (hcons := by
      intro current mode rest tail htail entry hmember arity heq
      rw [List.mem_append] at hmember
      cases hmember with
      | inl hinner => exact htail entry hinner arity heq
      | inr hlast =>
        simp only [List.mem_singleton] at hlast
        subst entry
        contradiction)
    base modes

/-- Canonical ordinary-function parameter layouts contain only slots. -/
theorem parameterEntries_noRecSelf (base : Nat) (modes : List Uses)
    (remaining : Nat → Nat) (depth : Nat) :
    NoRecSelf ⟨parameterEntries base modes remaining, depth⟩ := by
  apply NoRecSelf.of_mem_not_recSelf
  intro entry hmember arity
  exact parameterEntries_mem_not_recSelf base modes remaining entry hmember
    arity

/-- Foundational dependent traversal for the pure `releaseAll` fold.  Empty,
constant, and slot normalization plus environment and emitter threading
recurse once; clients provide only their three result constructors. -/
theorem releaseAll_traverse_core
    {Result : VEnv → List AVal → VEnv → Emit → Prop}
    (hnil : ∀ input,
      Result input [] input (_root_.id : Emit))
    (hconst : ∀ {input : VEnv} {atom : Atom} {rest : List AVal}
        {output : VEnv} {emit : Emit},
      Result input rest output emit →
      Result input (.constA atom :: rest) output emit)
    (hslot : ∀ {input : VEnv} {abs : Nat} {rest : List AVal}
        {output : VEnv} {tailEmit : Emit},
      Result input.bump rest output tailEmit →
      Result input (.slotA abs :: rest) output
        (emitOp (.drop (.var (input.rel abs))) ∘ tailEmit))
    (input : VEnv) (values : List AVal) :
    Result input values (releaseAll input values).1
      (releaseAll input values).2 := by
  induction values generalizing input with
  | nil => exact hnil input
  | cons value rest ih =>
    cases value with
    | constA atom =>
      simpa [releaseAll] using hconst (ih input)
    | slotA abs =>
      simpa [releaseAll] using hslot (ih input.bump)

theorem NoRecSelf.releaseAll (input : VEnv) (values : List AVal)
    (h : NoRecSelf input) :
    NoRecSelf (releaseAll input values).1 := by
  exact releaseAll_traverse_core
    (Result := fun initial _ output _ =>
      NoRecSelf initial → NoRecSelf output)
    (hnil := fun _ hinitial => hinitial)
    (hconst := fun htail hinitial => htail hinitial)
    (hslot := fun htail hinitial => htail hinitial.bump)
    input values h

private theorem throw_run_not_ok {α : Type} {message : String}
    {initial final : LowSt} {result : α}
    (hrun : (throw message : LowerM α).run initial = .ok result final) :
    False := by
  change EStateM.Result.error message initial = .ok result final at hrun
  contradiction

private theorem bind_run_ok_inv {error state α β : Type}
    {action : EStateM error state α} {next : α → EStateM error state β}
    {initial final : state} {result : β}
    (hrun : (action >>= next).run initial = .ok result final) :
    ∃ value middle,
      action.run initial = .ok value middle ∧
      (next value).run middle = .ok result final := by
  change
    (match action.run initial with
      | .ok value nextState => (next value).run nextState
      | .error err nextState => .error err nextState) =
      .ok result final at hrun
  cases haction : action.run initial with
  | ok value middle =>
    rw [haction] at hrun
    exact ⟨value, middle, rfl, hrun⟩
  | error err middle =>
    rw [haction] at hrun
    contradiction

/-- Source-neutral operational traversal for a successful `lowerCaptures`
run.  Empty recovery, both bind inversions, compiler-state threading, and
final tuple reconstruction happen once; clients supply only their empty
judgment and one successful-capture composition step. -/
theorem lowerCaptures_run_core
    (e : IxIR0.Expr)
    {Result : VEnv → VEnv → List Nat → Emit → List AVal → Prop}
    (hnil : ∀ input,
      Result input input [] (_root_.id : Emit) [])
    (hcons : ∀ {index : Nat} {rest : List Nat}
        {input middle output : VEnv} {headEmit tailEmit : Emit}
        {headValue : AVal} {tailValues : List AVal}
        {state middleState : LowSt},
      (lowerCapture e input index).run state =
        .ok (middle, headEmit, headValue) middleState →
      Result middle output rest tailEmit tailValues →
      Result input output (index :: rest) (headEmit ∘ tailEmit)
        (headValue :: tailValues))
    {captures : List Nat} {input output : VEnv}
    {emit : Emit} {values : List AVal} {state finalState : LowSt}
    (hrun : (lowerCaptures e input captures).run state =
      .ok (output, emit, values) finalState) :
    Result input output captures emit values := by
  induction captures generalizing input output emit values state finalState with
  | nil =>
    have hpure :
        (input, (_root_.id : Emit), []) = (output, emit, values) ∧
          state = finalState := by
      simpa [lowerCaptures] using hrun
    obtain ⟨hresult, hstate⟩ := hpure
    cases hresult
    subst finalState
    exact hnil _
  | cons index rest ih =>
    simp only [lowerCaptures] at hrun
    obtain ⟨headResult, middleState, hheadRun, hafterHead⟩ :=
      bind_run_ok_inv hrun
    rcases headResult with ⟨middle, headEmit, headValue⟩
    obtain ⟨tailResult, tailState, htailRun, hafterTail⟩ :=
      bind_run_ok_inv hafterHead
    rcases tailResult with ⟨tailOutput, tailEmit, tailValues⟩
    have hpure :
        (tailOutput, headEmit ∘ tailEmit, headValue :: tailValues) =
            (output, emit, values) ∧ tailState = finalState := by
      simpa using hafterTail
    obtain ⟨hresult, hstate⟩ := hpure
    cases hresult
    subst finalState
    exact hcons hheadRun (ih htailRun)

/-- Property-polymorphic action traversal for `lowerCaptures`.  Its
left-to-right `lowerCapture` sequencing and final pure tuple construction
recurse once for every action invariant closed under `pure` and `bind`. -/
theorem lowerCaptures_action_core
    (e : IxIR0.Expr)
    {ActionProperty : {α : Type} → LowerM α → Prop}
    (hpure : ∀ {α : Type} (value : α),
      ActionProperty (pure value : LowerM α))
    (hbind : ∀ {α β : Type} {action : LowerM α}
        {next : α → LowerM β},
      ActionProperty action →
      (∀ value, ActionProperty (next value)) →
      ActionProperty (action >>= next))
    (hcapture : ∀ input index,
      ActionProperty (lowerCapture e input index)) :
    ∀ (input : VEnv) (captures : List Nat),
      ActionProperty (lowerCaptures e input captures) := by
  intro input captures
  induction captures generalizing input with
  | nil =>
    change ActionProperty
      (pure (input, (_root_.id : Emit), ([] : List AVal)) :
        LowerM (VEnv × Emit × List AVal))
    exact hpure _
  | cons index rest ih =>
    simp only [lowerCaptures]
    apply hbind (hcapture input index)
    intro headResult
    rcases headResult with ⟨middle, headEmit, headValue⟩
    apply hbind (ih middle)
    intro tailResult
    rcases tailResult with ⟨output, tailEmit, tailValues⟩
    exact hpure
      (output, headEmit ∘ tailEmit, headValue :: tailValues)

private theorem map_run_ok_inv {α β : Type} {action : LowerM α}
    {f : α → β} {initial final : LowSt} {result : β}
    (hrun : (f <$> action).run initial = .ok result final) :
    ∃ value,
      action.run initial = .ok value final ∧ f value = result := by
  have hbind : (action >>= fun value => pure (f value)).run initial =
      .ok result final := by
    simpa only [bind_pure_comp] using hrun
  obtain ⟨value, middle, haction, hpure⟩ := bind_run_ok_inv hbind
  have hresult : f value = result ∧ middle = final := by
    simpa using hpure
  cases hresult.2
  exact ⟨value, haction, hresult.1⟩

/-- Source-neutral operational traversal for a successful `releaseSlots`
run.  Mode rejection, environment rewriting, depth advancement, tail-run
recovery, and emitter composition recurse once; clients supply only their
empty, affine-drop, and shared-drop judgments. -/
theorem releaseSlots_run_core
    {Result : VEnv → VEnv → List SlotDrop → Emit → Prop}
    (hnil : ∀ input,
      Result input input [] (_root_.id : Emit))
    (haffine : ∀ {entry abs : Nat} {rest : List SlotDrop}
        {input output : VEnv} {tailEmit : Emit},
      Result
        (input.setEntry entry (.slot abs 0 .affine false)).bump
        output rest tailEmit →
      Result input output
        (⟨entry, abs, .affine⟩ :: rest)
        (emitOp (.dropU (.var (input.rel abs))) ∘ tailEmit))
    (hmany : ∀ {entry abs : Nat} {rest : List SlotDrop}
        {input output : VEnv} {tailEmit : Emit},
      Result
        (input.setEntry entry (.slot abs 0 .many false)).bump
        output rest tailEmit →
      Result input output
        (⟨entry, abs, .many⟩ :: rest)
        (emitOp (.drop (.var (input.rel abs))) ∘ tailEmit))
    {input output : VEnv} {drops : List SlotDrop} {emit : Emit}
    {state finalState : LowSt}
    (hrun : (releaseSlots input drops).run state =
      .ok (output, emit) finalState) :
    Result input output drops emit := by
  induction drops generalizing input output emit state finalState with
  | nil =>
    have hpure :
        (input, (_root_.id : Emit)) = (output, emit) ∧
          state = finalState := by
      simpa [releaseSlots] using hrun
    obtain ⟨hresult, _⟩ := hpure
    cases hresult
    exact hnil input
  | cons drop rest ih =>
    rcases drop with ⟨entry, abs, uses⟩
    cases uses with
    | erased =>
      obtain ⟨_, _, hthrow, _⟩ := bind_run_ok_inv (by
        simpa [releaseSlots] using hrun)
      exact (throw_run_not_ok hthrow).elim
    | linear =>
      obtain ⟨_, _, hthrow, _⟩ := bind_run_ok_inv (by
        simpa [releaseSlots] using hrun)
      exact (throw_run_not_ok hthrow).elim
    | affine =>
      have hmap :
          ((fun result : VEnv × Emit =>
              (result.1,
                emitOp (.dropU (.var (input.rel abs))) ∘ result.2)) <$>
            releaseSlots
              (input.setEntry entry
                (.slot abs 0 .affine false)).bump rest).run state =
            .ok (output, emit) finalState := by
        simpa [releaseSlots] using hrun
      obtain ⟨tailResult, htailRun, hvalue⟩ := map_run_ok_inv hmap
      rcases tailResult with ⟨actualOutput, tailEmit⟩
      have houtput : actualOutput = output := congrArg Prod.fst hvalue
      have hemit :
          emitOp (.dropU (.var (input.rel abs))) ∘ tailEmit = emit :=
        congrArg Prod.snd hvalue
      subst output
      subst emit
      exact haffine (ih htailRun)
    | many =>
      have hmap :
          ((fun result : VEnv × Emit =>
              (result.1,
                emitOp (.drop (.var (input.rel abs))) ∘ result.2)) <$>
            releaseSlots
              (input.setEntry entry
                (.slot abs 0 .many false)).bump rest).run state =
            .ok (output, emit) finalState := by
        simpa [releaseSlots] using hrun
      obtain ⟨tailResult, htailRun, hvalue⟩ := map_run_ok_inv hmap
      rcases tailResult with ⟨actualOutput, tailEmit⟩
      have houtput : actualOutput = output := congrArg Prod.fst hvalue
      have hemit :
          emitOp (.drop (.var (input.rel abs))) ∘ tailEmit = emit :=
        congrArg Prod.snd hvalue
      subst output
      subst emit
      exact hmany (ih htailRun)

/-- Property-polymorphic action traversal for `releaseSlots`.  Its mode
dispatch, state-free head action, environment threading, tail action, and
pure emitter assembly recurse once for every property closed under `pure`,
`bind`, and an immediately throwing bind. -/
theorem releaseSlots_action_core
    {ActionProperty : {α : Type} → LowerM α → Prop}
    (hpure : ∀ {α : Type} (value : α),
      ActionProperty (pure value : LowerM α))
    (hbind : ∀ {α β : Type} {action : LowerM α}
        {next : α → LowerM β},
      ActionProperty action →
      (∀ value, ActionProperty (next value)) →
      ActionProperty (action >>= next))
    (hthrowBind : ∀ {α β : Type} (message : String)
        (next : α → LowerM β),
      ActionProperty
        ((EStateM.throw message : LowerM α) >>= next)) :
    ∀ (input : VEnv) (drops : List SlotDrop),
      ActionProperty (releaseSlots input drops) := by
  intro input drops
  induction drops generalizing input with
  | nil =>
    change ActionProperty
      (pure (input, (_root_.id : Emit)) : LowerM (VEnv × Emit))
    exact hpure _
  | cons drop rest ih =>
    simp only [releaseSlots]
    cases drop.uses with
    | erased => exact hthrowBind _ _
    | linear => exact hthrowBind _ _
    | affine =>
      apply hbind (hpure _)
      intro headEmit
      apply hbind
        (ih (input.setEntry drop.entry
          (.slot drop.abs 0 .affine false)).bump)
      intro tailResult
      rcases tailResult with ⟨output, tailEmit⟩
      exact hpure (output, headEmit ∘ tailEmit)
    | many =>
      apply hbind (hpure _)
      intro headEmit
      apply hbind
        (ih (input.setEntry drop.entry
          (.slot drop.abs 0 .many false)).bump)
      intro tailResult
      rcases tailResult with ⟨output, tailEmit⟩
      exact hpure (output, headEmit ∘ tailEmit)

theorem releaseSlots_noRecSelf (input : VEnv) :
    ∀ {drops output emit state finalState},
      (releaseSlots input drops).run state =
        .ok (output, emit) finalState →
      NoRecSelf input → NoRecSelf output := by
  intro drops output emit state finalState hrun hno
  exact releaseSlots_run_core
    (Result := fun initial final _ _ =>
      NoRecSelf initial → NoRecSelf final)
    (hnil := fun _ h => h)
    (haffine := by
      intro entry abs rest initial final tailEmit htail hinitial
      exact htail
        (hinitial.setSlot entry abs 0 .affine false).bump)
    (hmany := by
      intro entry abs rest initial final tailEmit htail hinitial
      exact htail
        (hinitial.setSlot entry abs 0 .many false).bump)
    hrun hno

theorem lowerCapture_noRecSelf (expr : IxIR0.Expr) (input : VEnv)
    (index : Nat) {output : VEnv} {emit : Emit} {value : AVal}
    {state finalState : LowSt}
    (hrun : (lowerCapture expr input index).run state =
      .ok (output, emit, value) finalState)
    (hno : NoRecSelf input) : NoRecSelf output := by
  cases hentry : input.entries[index]? with
  | none => exact (throw_run_not_ok (by
      simpa [lowerCapture, hentry] using hrun)).elim
  | some entry =>
    cases entry with
    | recSelf arity => exact (hno index arity hentry).elim
    | slot abs remaining uses held =>
      cases held with
      | false => exact (throw_run_not_ok (by
          simpa [lowerCapture, hentry] using hrun)).elim
      | true =>
        by_cases hunique : worldOfUses uses = .unique
        · have huuEq : (Owned.unique == Owned.unique) = true := by decide
          exact (throw_run_not_ok (by
            simpa [lowerCapture, hentry, hunique, huuEq] using hrun)).elim
        · have huniqueEq :
              (worldOfUses uses == Owned.unique) = false := by
            cases uses <;> simp_all [worldOfUses] <;> decide
          by_cases hmore : remaining > countUses index expr
          · have houtput : output =
                (input.setEntry index
                  (.slot abs (remaining - countUses index expr) uses true)).bump := by
              have hvalue := congrArg
                (fun result : EStateM.Result String LowSt
                    (VEnv × Emit × AVal) =>
                  match result with
                  | .ok value _ => value.1
                  | .error _ _ => input) hrun
              simpa [lowerCapture, hentry, huniqueEq, hmore] using hvalue.symm
            subst output
            exact (hno.setSlot index abs
              (remaining - countUses index expr) uses true).bump
          · by_cases hequal : remaining = countUses index expr
            · have houtput : output =
                  input.setEntry index (.slot abs 0 uses false) := by
                have hvalue := congrArg
                  (fun result : EStateM.Result String LowSt
                      (VEnv × Emit × AVal) =>
                    match result with
                    | .ok value _ => value.1
                    | .error _ _ => input) hrun
                simpa [lowerCapture, hentry, huniqueEq, hmore, hequal]
                  using hvalue.symm
              subst output
              exact hno.setSlot index abs 0 uses false
            · exact (throw_run_not_ok (by
                simpa [lowerCapture, hentry, huniqueEq, hmore, hequal]
                  using hrun)).elim

theorem lowerCaptures_noRecSelf (expr : IxIR0.Expr) :
    ∀ {indices input output emit values state finalState},
      (lowerCaptures expr input indices).run state =
        .ok (output, emit, values) finalState →
      NoRecSelf input → NoRecSelf output := by
  intro indices input output emit values state finalState hrun
  apply lowerCaptures_run_core
    (Result := fun input output _ _ _ =>
      NoRecSelf input → NoRecSelf output)
    (e := expr) (hrun := hrun)
  · intro input hno
    exact hno
  · intro index rest input middle output headEmit tailEmit headValue
      tailValues state middleState hheadRun htail hno
    exact htail
      (lowerCapture_noRecSelf expr input index hheadRun hno)

def LowerEPreservesNoRecSelf (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {world : Owned} {expr : IxIR0.Expr}
      {state finalState : LowSt} {output : VEnv} {emit : Emit} {value : AVal},
    (lowerE src fuel input world expr).run state =
      .ok (output, emit, value) finalState →
    NoRecSelf input → NoRecSelf output

def LowerBorrowPreservesNoRecSelf (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {expr : IxIR0.Expr} {state finalState : LowSt}
      {output : VEnv} {emit : Emit} {value : AVal} {release : Bool},
    (lowerBorrow src fuel input expr).run state =
      .ok (output, emit, value, release) finalState →
    NoRecSelf input → NoRecSelf output

def LowerSpinePreservesNoRecSelf (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {world : Owned} {head : IxIR0.Expr}
      {args : List IxIR0.Expr} {state finalState : LowSt}
      {output : VEnv} {emit : Emit} {value : AVal},
    (lowerSpine src fuel input world head args).run state =
      .ok (output, emit, value) finalState →
    NoRecSelf input → NoRecSelf output

def KnownCallPreservesNoRecSelf (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {build : Array Atom → Op} {count : Nat}
      {argWorlds : List Owned} {resultWorld : Owned}
      {args : List IxIR0.Expr} {state finalState : LowSt}
      {output : VEnv} {emit : Emit} {value : AVal},
    (knownCall src fuel input build count argWorlds resultWorld args).run
      state = .ok (output, emit, value) finalState →
    NoRecSelf input → NoRecSelf output

def LowerArgsPreservesNoRecSelf (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {args : List (IxIR0.Expr × Owned)}
      {state finalState : LowSt} {output : VEnv}
      {emit : Emit} {values : List AVal},
    (lowerArgs src fuel input args).run state =
      .ok (output, emit, values) finalState →
    NoRecSelf input → NoRecSelf output

def ApplyRestPreservesNoRecSelf (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {resultWorld : Owned} {pre : Emit}
      {function : AVal} {args : List IxIR0.Expr}
      {state finalState : LowSt} {output : VEnv}
      {emit : Emit} {value : AVal},
    (applyRest src fuel input resultWorld pre function args).run state =
      .ok (output, emit, value) finalState →
    NoRecSelf input → NoRecSelf output

def LowerLamPreservesNoRecSelf (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {expr : IxIR0.Expr} {state finalState : LowSt}
      {output : VEnv} {emit : Emit} {value : AVal},
    (lowerLam src fuel input expr).run state =
      .ok (output, emit, value) finalState →
    NoRecSelf input → NoRecSelf output

structure LowerPreservesNoRecSelf (src : IxIR0.Env) (fuel : Nat) : Prop where
  expr : LowerEPreservesNoRecSelf src fuel
  borrow : LowerBorrowPreservesNoRecSelf src fuel
  spine : LowerSpinePreservesNoRecSelf src fuel
  knownCall : KnownCallPreservesNoRecSelf src fuel
  args : LowerArgsPreservesNoRecSelf src fuel
  applyRest : ApplyRestPreservesNoRecSelf src fuel
  lam : LowerLamPreservesNoRecSelf src fuel

theorem lowerPreservesNoRecSelf_zero (src : IxIR0.Env) :
    LowerPreservesNoRecSelf src 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro input world expr state finalState output emit value hrun _
    exact (throw_run_not_ok (by simpa [lowerE] using hrun)).elim
  · intro input expr state finalState output emit value release hrun _
    exact (throw_run_not_ok (by simpa [lowerBorrow] using hrun)).elim
  · intro input world head args state finalState output emit value hrun _
    exact (throw_run_not_ok (by simpa [lowerSpine] using hrun)).elim
  · intro input build count argWorlds resultWorld args state finalState
      output emit value hrun _
    exact (throw_run_not_ok (by simpa [knownCall] using hrun)).elim
  · intro input args state finalState output emit values hrun _
    exact (throw_run_not_ok (by simpa [lowerArgs] using hrun)).elim
  · intro input resultWorld pre function args state finalState output emit
      value hrun _
    exact (throw_run_not_ok (by simpa [applyRest] using hrun)).elim
  · intro input expr state finalState output emit value hrun _
    exact (throw_run_not_ok (by simpa [lowerLam] using hrun)).elim

theorem lowerArgsPreservesNoRecSelf_succ {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesNoRecSelf src fuel)
    (hargs : LowerArgsPreservesNoRecSelf src fuel) :
    LowerArgsPreservesNoRecSelf src (fuel + 1) := by
  intro input args state finalState output emit values hrun hno
  cases args with
  | nil =>
    have hpure :
        (input, (_root_.id : Emit), []) = (output, emit, values) ∧
          state = finalState := by
      simpa [lowerArgs] using hrun
    cases hpure.1
    exact hno
  | cons head rest =>
    rcases head with ⟨expr, world⟩
    simp only [lowerArgs] at hrun
    obtain ⟨headResult, middleState, hheadRun, hafterHead⟩ :=
      bind_run_ok_inv hrun
    rcases headResult with ⟨middle, headEmit, headValue⟩
    obtain ⟨tailResult, tailState, htailRun, hafterTail⟩ :=
      bind_run_ok_inv hafterHead
    rcases tailResult with ⟨actualOutput, tailEmit, tailValues⟩
    have hvalue : actualOutput = output := by
      have hpure :
          (actualOutput, headEmit ∘ tailEmit, headValue :: tailValues) =
              (output, emit, values) ∧ tailState = finalState := by
        simpa using hafterTail
      exact congrArg Prod.fst hpure.1
    subst output
    exact hargs htailRun (hexpr hheadRun hno)

theorem applyRestPreservesNoRecSelf_succ {src : IxIR0.Env} {fuel : Nat}
    (hargs : LowerArgsPreservesNoRecSelf src fuel) :
    ApplyRestPreservesNoRecSelf src (fuel + 1) := by
  intro input resultWorld pre function args state finalState output emit value
    hrun hno
  cases function with
  | constA atom =>
    cases atom with
    | erased =>
      simp only [applyRest] at hrun
      obtain ⟨argsResult, argsState, hargsRun, hpureRun⟩ :=
        bind_run_ok_inv hrun
      rcases argsResult with ⟨middle, argsEmit, values⟩
      have hpure : (releaseAll middle values).1 = output := by
        have hvalue :
            ((releaseAll middle values).1,
              pre ∘ argsEmit ∘ (releaseAll middle values).2,
              AVal.constA .erased) = (output, emit, value) ∧
              argsState = finalState := by
          simpa using hpureRun
        exact congrArg Prod.fst hvalue.1
      subst output
      exact (hargs hargsRun hno).releaseAll middle values
    | var relative =>
      simp only [applyRest] at hrun
      obtain ⟨_, checkedState, _, hafterCheck⟩ := bind_run_ok_inv hrun
      obtain ⟨argsResult, argsState, hargsRun, hpureRun⟩ :=
        bind_run_ok_inv hafterCheck
      rcases argsResult with ⟨middle, argsEmit, values⟩
      have houtput : middle.bump = output := by
        have hvalue := congrArg
          (fun result : EStateM.Result String LowSt (VEnv × Emit × AVal) =>
            match result with
            | .ok value _ => value.1
            | .error _ _ => input) hpureRun
        simpa using hvalue
      subst output
      exact (hargs hargsRun hno).bump
    | lit literal =>
      simp only [applyRest] at hrun
      obtain ⟨_, checkedState, _, hafterCheck⟩ := bind_run_ok_inv hrun
      obtain ⟨argsResult, argsState, hargsRun, hpureRun⟩ :=
        bind_run_ok_inv hafterCheck
      rcases argsResult with ⟨middle, argsEmit, values⟩
      have houtput : middle.bump = output := by
        have hvalue := congrArg
          (fun result : EStateM.Result String LowSt (VEnv × Emit × AVal) =>
            match result with
            | .ok value _ => value.1
            | .error _ _ => input) hpureRun
        simpa using hvalue
      subst output
      exact (hargs hargsRun hno).bump
  | slotA abs =>
    simp only [applyRest] at hrun
    obtain ⟨_, checkedState, _, hafterCheck⟩ := bind_run_ok_inv hrun
    obtain ⟨argsResult, argsState, hargsRun, hpureRun⟩ :=
      bind_run_ok_inv hafterCheck
    rcases argsResult with ⟨middle, argsEmit, values⟩
    have houtput : middle.bump = output := by
      have hvalue := congrArg
        (fun result : EStateM.Result String LowSt (VEnv × Emit × AVal) =>
          match result with
          | .ok value _ => value.1
          | .error _ _ => input) hpureRun
      simpa using hvalue
    subst output
    exact (hargs hargsRun hno).bump

theorem knownCallPreservesNoRecSelf_succ {src : IxIR0.Env} {fuel : Nat}
    (hargs : LowerArgsPreservesNoRecSelf src fuel)
    (hrest : ApplyRestPreservesNoRecSelf src fuel) :
    KnownCallPreservesNoRecSelf src (fuel + 1) := by
  intro input build count argWorlds resultWorld args state finalState output
    emit value hrun hno
  simp only [knownCall] at hrun
  obtain ⟨argsResult, argsState, hargsRun, hafterArgs⟩ :=
    bind_run_ok_inv hrun
  rcases argsResult with ⟨middle, argsEmit, values⟩
  have hmiddle := hargs hargsRun hno
  by_cases hterminal : args.length ≤ count
  · have houtput : middle.bump = output := by
      have hvalue := congrArg
        (fun result : EStateM.Result String LowSt (VEnv × Emit × AVal) =>
          match result with
          | .ok value _ => value.1
          | .error _ _ => input) hafterArgs
      simpa [hterminal] using hvalue
    subst output
    exact hmiddle.bump
  · have hrestRun :
        (applyRest src fuel middle.bump resultWorld
          (argsEmit ∘ emitOp
            (build (values.map (·.toAtom middle)).toArray))
          (.slotA middle.depth) (args.drop count)).run argsState =
            .ok (output, emit, value) finalState := by
      simpa [hterminal] using hafterArgs
    exact hrest hrestRun hmiddle.bump

private theorem lowerBorrow_dynamic_noRecSelf
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesNoRecSelf src fuel)
    {input output : VEnv} {expr : IxIR0.Expr}
    {state finalState : LowSt} {emit : Emit} {value : AVal}
    {releaseFlag : Bool}
    {finish : (VEnv × Emit × AVal) → (VEnv × Emit × AVal × Bool)}
    (hrun : (finish <$> lowerE src fuel input .shared expr).run state =
        .ok (output, emit, value, releaseFlag) finalState)
    (hfinish : ∀ result, (finish result).1 = result.1)
    (hno : NoRecSelf input) : NoRecSelf output := by
  obtain ⟨exprResult, hexprRun, hvalue⟩ := map_run_ok_inv hrun
  rcases exprResult with ⟨middle, middleEmit, middleValue⟩
  have houtput : middle = output := by
    have := congrArg Prod.fst hvalue
    simpa [hfinish] using this
  subst output
  exact hexpr hexprRun hno

theorem lowerBorrowPreservesNoRecSelf_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesNoRecSelf src fuel) :
    LowerBorrowPreservesNoRecSelf src (fuel + 1) := by
  intro input expr state finalState output emit value release hrun hno
  cases expr with
  | var index =>
    cases hentry : input.entries[index]? with
    | none => exact (throw_run_not_ok (by
        simpa [lowerBorrow, hentry] using hrun)).elim
    | some entry =>
      cases entry with
      | recSelf arity => exact (hno index arity hentry).elim
      | slot abs remaining uses held =>
        cases held with
        | false => exact (throw_run_not_ok (by
            simpa [lowerBorrow, hentry] using hrun)).elim
        | true =>
          by_cases hunique : worldOfUses uses = .unique
          · have huuEq : (Owned.unique == Owned.unique) = true := by decide
            exact (throw_run_not_ok (by
              simpa [lowerBorrow, hentry, hunique, huuEq] using hrun)).elim
          · have huniqueEq :
                (worldOfUses uses == Owned.unique) = false := by
              cases uses <;> simp_all [worldOfUses] <;> decide
            cases remaining with
            | zero => exact (throw_run_not_ok (by
                simpa [lowerBorrow, hentry, huniqueEq] using hrun)).elim
            | succ remaining =>
              cases remaining with
              | zero =>
                have hpure :
                    (input.setEntry index (.slot abs 0 uses false),
                      (_root_.id : Emit), AVal.slotA abs, true) =
                        (output, emit, value, release) ∧
                      state = finalState := by
                  simpa [lowerBorrow, hentry, huniqueEq] using hrun
                cases hpure.1
                exact hno.setSlot index abs 0 uses false
              | succ remaining =>
                have hpure :
                    (input.setEntry index
                        (.slot abs (remaining + 1) uses true),
                      (_root_.id : Emit), AVal.slotA abs, false) =
                        (output, emit, value, release) ∧
                      state = finalState := by
                  simpa [lowerBorrow, hentry, huniqueEq] using hrun
                cases hpure.1
                exact hno.setSlot index abs (remaining + 1) uses true
  | ref address =>
    apply lowerBorrow_dynamic_noRecSelf hexpr
      (by simpa [lowerBorrow] using hrun) (fun _ => rfl) hno
  | app function argument =>
    apply lowerBorrow_dynamic_noRecSelf hexpr
      (by simpa [lowerBorrow] using hrun) (fun _ => rfl) hno
  | lam uses body =>
    apply lowerBorrow_dynamic_noRecSelf hexpr
      (by simpa [lowerBorrow] using hrun) (fun _ => rfl) hno
  | letE uses value body =>
    apply lowerBorrow_dynamic_noRecSelf hexpr
      (by simpa [lowerBorrow] using hrun) (fun _ => rfl) hno
  | proj index source =>
    apply lowerBorrow_dynamic_noRecSelf hexpr
      (by simpa [lowerBorrow] using hrun) (fun _ => rfl) hno
  | lit literal =>
    apply lowerBorrow_dynamic_noRecSelf hexpr
      (by simpa [lowerBorrow] using hrun) (fun _ => rfl) hno
  | erased =>
    apply lowerBorrow_dynamic_noRecSelf hexpr
      (by simpa [lowerBorrow] using hrun) (fun _ => rfl) hno

private theorem lowerE_applyRest_noRecSelf
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesNoRecSelf src fuel)
    (hrest : ApplyRestPreservesNoRecSelf src fuel)
    {input output : VEnv} {world : Owned} {head : IxIR0.Expr}
    {args : List IxIR0.Expr} {state finalState : LowSt}
    {emit : Emit} {value : AVal}
    (hrun : (do
      let (middle, headEmit, function) ←
        lowerE src fuel input .shared head
      applyRest src fuel middle world headEmit function args).run state =
        .ok (output, emit, value) finalState)
    (hno : NoRecSelf input) : NoRecSelf output := by
  obtain ⟨headResult, middleState, hheadRun, hrestRun⟩ :=
    bind_run_ok_inv hrun
  rcases headResult with ⟨middle, headEmit, function⟩
  exact hrest hrestRun (hexpr hheadRun hno)

theorem lowerSpinePreservesNoRecSelf_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesNoRecSelf src fuel)
    (hspine : LowerSpinePreservesNoRecSelf src fuel)
    (hknown : KnownCallPreservesNoRecSelf src fuel)
    (hrest : ApplyRestPreservesNoRecSelf src fuel) :
    LowerSpinePreservesNoRecSelf src (fuel + 1) := by
  intro input world head args state finalState output emit value hrun hno
  have hsuEq : (Owned.shared == Owned.unique) = false := by decide
  cases head with
  | app function argument =>
    apply hspine
    · simpa [lowerSpine] using hrun
    · exact hno
  | erased =>
    apply hrest
    · simpa [lowerSpine] using hrun
    · exact hno
  | var index =>
    simp only [lowerSpine] at hrun
    cases hentry : input.entries[index]? with
    | none =>
      apply lowerE_applyRest_noRecSelf hexpr hrest
      · simpa [hentry] using hrun
      · exact hno
    | some entry =>
      cases entry with
      | recSelf arity => exact (hno index arity hentry).elim
      | slot abs remaining uses held =>
        apply lowerE_applyRest_noRecSelf hexpr hrest
        · simpa [hentry] using hrun
        · exact hno
  | ref address =>
    simp only [lowerSpine] at hrun
    cases hsource : src address with
    | none =>
      rw [hsource] at hrun
      exact (throw_run_not_ok hrun).elim
    | some decl =>
      rw [hsource] at hrun
      cases decl with
      | defn result body =>
        simp only at hrun
        by_cases hunder : args.length < lamArity body
        · rw [if_pos hunder] at hrun
          cases world with
          | unique => exact (throw_run_not_ok hrun).elim
          | shared =>
            cases result with
            | unique => exact (throw_run_not_ok hrun).elim
            | shared =>
              cases hp : papSafe body with
              | false => exact (throw_run_not_ok (by
                  simpa [hp, hsuEq] using hrun)).elim
              | true =>
                apply hknown
                · simpa [hp, hsuEq] using hrun
                · exact hno
        · rw [if_neg hunder] at hrun
          obtain ⟨_, checkedState, _, hknownRun⟩ := bind_run_ok_inv hrun
          exact hknown hknownRun hno
      | ctor tag arity =>
        simp only at hrun
        by_cases hunder : args.length < arity
        · rw [if_pos hunder] at hrun
          cases world with
          | unique => exact (throw_run_not_ok hrun).elim
          | shared =>
            obtain ⟨wrapper, wrapperState, _, hknownRun⟩ :=
              bind_run_ok_inv hrun
            exact hknown hknownRun hno
        · rw [if_neg hunder] at hrun
          exact hknown hrun hno
      | recursor numArgs natLit rules =>
        simp only at hrun
        by_cases hunder : args.length < numArgs + 1
        · rw [if_pos hunder] at hrun
          cases world with
          | unique => exact (throw_run_not_ok hrun).elim
          | shared => exact hknown hrun hno
        · rw [if_neg hunder] at hrun
          obtain ⟨_, checkedState, _, hknownRun⟩ := bind_run_ok_inv hrun
          exact hknown hknownRun hno
      | extern arity =>
        simp only at hrun
        by_cases hunder : args.length < arity
        · rw [if_pos hunder] at hrun
          cases world with
          | unique => exact (throw_run_not_ok hrun).elim
          | shared => exact hknown hrun hno
        · rw [if_neg hunder] at hrun
          exact hknown hrun hno
  | lam uses body =>
    apply lowerE_applyRest_noRecSelf hexpr hrest
    · simpa [lowerSpine] using hrun
    · exact hno
  | letE uses bound body =>
    apply lowerE_applyRest_noRecSelf hexpr hrest
    · simpa [lowerSpine] using hrun
    · exact hno
  | proj index source =>
    apply lowerE_applyRest_noRecSelf hexpr hrest
    · simpa [lowerSpine] using hrun
    · exact hno
  | lit literal =>
    apply lowerE_applyRest_noRecSelf hexpr hrest
    · simpa [lowerSpine] using hrun
    · exact hno

theorem lowerLamPreservesNoRecSelf_succ
    {src : IxIR0.Env} {fuel : Nat} :
    LowerLamPreservesNoRecSelf src (fuel + 1) := by
  intro input expr state finalState output emit value hrun hno
  cases hp : papSafe expr with
  | false => simp [lowerLam, hp] at hrun
  | true =>
    simp only [lowerLam] at hrun
    simp only [hp, ↓reduceIte, bind_pure_comp] at hrun
    let captures := (List.range input.entries.length).filter
      (fun index => countUses index expr > 0)
    have hcaptures : captures = (List.range input.entries.length).filter
        (fun index => countUses index expr > 0) := rfl
    rw [← hcaptures] at hrun
    obtain ⟨captureResult, captureState, hcaptureRun, hafterCapture⟩ :=
      bind_run_ok_inv hrun
    rcases captureResult with ⟨captureOutput, captureEmit, captureValues⟩
    obtain ⟨fnAddr, addressState, _, hafterFresh⟩ :=
      bind_run_ok_inv hafterCapture
    obtain ⟨code, bodyState, _, hafterBody⟩ :=
      bind_run_ok_inv hafterFresh
    obtain ⟨_, _, hvalue⟩ := map_run_ok_inv hafterBody
    have houtput : captureOutput.bump = output := by
      exact congrArg Prod.fst hvalue
    subst output
    exact (lowerCaptures_noRecSelf expr hcaptureRun hno).bump

private theorem lowerE_ref_entries_eq_noRecSelf
    {src : IxIR0.Env} {fuel : Nat} {input output : VEnv}
    {world : Owned} {address : Ixon.Address}
    {state finalState : LowSt} {emit : Emit} {value : AVal}
    (hrun : (lowerE src (fuel + 1) input world (.ref address)).run state =
      .ok (output, emit, value) finalState) :
    output.entries = input.entries := by
  have huuEq : (Owned.unique == Owned.unique) = true := by decide
  have hsuEq : (Owned.shared == Owned.unique) = false := by decide
  cases hsource : src address with
  | none => exact (throw_run_not_ok (by
      simpa [lowerE, hsource] using hrun)).elim
  | some decl =>
    cases decl with
    | defn result body =>
      cases harity : lamArity body with
      | zero =>
        have hrun' := hrun
        simp only [lowerE, hsource, harity] at hrun'
        obtain ⟨_, checkedState, _, hpureRun⟩ := bind_run_ok_inv hrun'
        have houtput := congrArg
          (fun result : EStateM.Result String LowSt (VEnv × Emit × AVal) =>
            match result with
            | .ok value _ => value.1.entries
            | .error _ _ => []) hpureRun
        simpa [VEnv.bump] using houtput.symm
      | succ arity =>
        cases world with
        | unique => exact (throw_run_not_ok (by
            simpa [lowerE, hsource, harity, huuEq] using hrun)).elim
        | shared =>
          cases result with
          | unique => exact (throw_run_not_ok (by
              simpa [lowerE, hsource, harity, hsuEq, huuEq]
                using hrun)).elim
          | shared =>
            cases hp : papSafe body with
            | false => exact (throw_run_not_ok (by
                simpa [lowerE, hsource, harity, hsuEq, hp]
                  using hrun)).elim
            | true =>
              have hpure := hrun
              simp [lowerE, hsource, harity, hsuEq, hp] at hpure
              rw [← hpure.1.1]
              rfl
    | ctor tag arity =>
      cases arity with
      | zero =>
        have hpure := hrun
        simp [lowerE, hsource] at hpure
        rw [← hpure.1.1]
        rfl
      | succ arity =>
        cases world with
        | unique => exact (throw_run_not_ok (by
            simpa [lowerE, hsource, huuEq] using hrun)).elim
        | shared =>
          have hrun' := hrun
          simp only [lowerE, hsource, hsuEq, Bool.false_eq_true,
            if_false] at hrun'
          obtain ⟨wrapper, wrapperState, _, hpureRun⟩ :=
            bind_run_ok_inv hrun'
          have houtput := congrArg
            (fun result : EStateM.Result String LowSt
                (VEnv × Emit × AVal) =>
              match result with
              | .ok value _ => value.1.entries
              | .error _ _ => []) hpureRun
          simpa [VEnv.bump] using houtput.symm
    | recursor numArgs natLit rules =>
      cases world with
      | unique => exact (throw_run_not_ok (by
          simpa [lowerE, hsource, huuEq] using hrun)).elim
      | shared =>
        have hpure := hrun
        simp [lowerE, hsource, hsuEq] at hpure
        rw [← hpure.1.1]
        rfl
    | extern arity =>
      cases arity with
      | zero =>
        have hpure := hrun
        simp [lowerE, hsource] at hpure
        rw [← hpure.1.1]
        rfl
      | succ arity =>
        cases world with
        | unique => exact (throw_run_not_ok (by
            simpa [lowerE, hsource, huuEq] using hrun)).elim
        | shared =>
          have hpure := hrun
          simp [lowerE, hsource, hsuEq] at hpure
          rw [← hpure.1.1]
          rfl

private theorem lowerE_proj_noRecSelf
    {src : IxIR0.Env} {fuel : Nat}
    (hborrow : LowerBorrowPreservesNoRecSelf src fuel)
    {input output : VEnv} {world : Owned} {fieldIndex : Nat}
    {source : IxIR0.Expr} {state finalState : LowSt}
    {emit : Emit} {value : AVal}
    (hrun : (lowerE src (fuel + 1) input world
      (.proj fieldIndex source)).run state =
        .ok (output, emit, value) finalState)
    (hno : NoRecSelf input) : NoRecSelf output := by
  cases world with
  | unique =>
    have huuEq : (Owned.unique == Owned.unique) = true := by decide
    simp [lowerE, huuEq] at hrun
  | shared =>
    have hsuEq : (Owned.shared == Owned.unique) = false := by decide
    simp only [lowerE, hsuEq, Bool.false_eq_true, if_false] at hrun
    obtain ⟨borrowResult, middleState, hborrowRun, hafterBorrow⟩ :=
      bind_run_ok_inv hrun
    rcases borrowResult with
      ⟨borrowOutput, borrowEmit, borrowed, release⟩
    have hborrowNo := hborrow hborrowRun hno
    cases borrowed with
    | constA atom =>
      cases atom with
      | var relative =>
        have hpure : borrowOutput.bump = output := by
          have hvalue := congrArg
            (fun result : EStateM.Result String LowSt
                (VEnv × Emit × AVal) =>
              match result with
              | .ok value _ => value.1
              | .error _ _ => input) hafterBorrow
          simpa using hvalue
        subst output
        exact hborrowNo.bump
      | lit literal =>
        have hpure : borrowOutput.bump = output := by
          have hvalue := congrArg
            (fun result : EStateM.Result String LowSt
                (VEnv × Emit × AVal) =>
              match result with
              | .ok value _ => value.1
              | .error _ _ => input) hafterBorrow
          simpa using hvalue
        subst output
        exact hborrowNo.bump
      | erased =>
        have hpure : borrowOutput = output := by
          have hvalue := congrArg
            (fun result : EStateM.Result String LowSt
                (VEnv × Emit × AVal) =>
              match result with
              | .ok value _ => value.1
              | .error _ _ => input) hafterBorrow
          simpa using hvalue
        subst output
        exact hborrowNo
    | slotA targetAbs =>
      cases release with
      | false =>
        have hpure : borrowOutput.bump.bump = output := by
          have hvalue := congrArg
            (fun result : EStateM.Result String LowSt
                (VEnv × Emit × AVal) =>
              match result with
              | .ok value _ => value.1
              | .error _ _ => input) hafterBorrow
          simpa using hvalue
        subst output
        exact hborrowNo.bump.bump
      | true =>
        have hpure : borrowOutput.bump.bump.bump = output := by
          have hvalue := congrArg
            (fun result : EStateM.Result String LowSt
                (VEnv × Emit × AVal) =>
              match result with
              | .ok value _ => value.1
              | .error _ _ => input) hafterBorrow
          simpa using hvalue
        subst output
        exact hborrowNo.bump.bump.bump

private theorem lowerE_mapped_body_pop_noRecSelf
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesNoRecSelf src fuel)
    {bodyInput output : VEnv} {world : Owned} {body : IxIR0.Expr}
    {state finalState : LowSt} {emit : Emit} {value : AVal}
    {finish : (VEnv × Emit × AVal) → (VEnv × Emit × AVal)}
    (hrun : (finish <$> lowerE src fuel bodyInput world body).run state =
      .ok (output, emit, value) finalState)
    (hfinish : ∀ result, (finish result).1 = result.1.pop)
    (hno : NoRecSelf bodyInput) : NoRecSelf output := by
  obtain ⟨bodyResult, hbodyRun, hvalue⟩ := map_run_ok_inv hrun
  rcases bodyResult with ⟨bodyOutput, bodyEmit, bodyValue⟩
  have houtput : bodyOutput.pop = output := by
    have := congrArg Prod.fst hvalue
    simpa [hfinish] using this
  subst output
  exact (hexpr hbodyRun hno).pop

private theorem lowerE_let_noRecSelf
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesNoRecSelf src fuel)
    {input output : VEnv} {world : Owned} {binderUses : Uses}
    {bound body : IxIR0.Expr} {state finalState : LowSt}
    {emit : Emit} {value : AVal}
    (hrun : (lowerE src (fuel + 1) input world
      (.letE binderUses bound body)).run state =
        .ok (output, emit, value) finalState)
    (hno : NoRecSelf input) : NoRecSelf output := by
  simp only [lowerE] at hrun
  obtain ⟨boundResult, boundState, hboundRun, hafterBound⟩ :=
    bind_run_ok_inv hrun
  rcases boundResult with ⟨middle, boundEmit, boundValue⟩
  have hmiddle := hexpr hboundRun hno
  cases boundValue with
  | slotA boundAbs =>
    by_cases hzero : countUses 0 body = 0
    · cases binderUses with
      | erased =>
        obtain ⟨_, _, hthrow, _⟩ := bind_run_ok_inv
          (by simpa [hzero] using hafterBound)
        exact (throw_run_not_ok hthrow).elim
      | linear =>
        obtain ⟨_, _, hthrow, _⟩ := bind_run_ok_inv
          (by simpa [hzero] using hafterBound)
        exact (throw_run_not_ok hthrow).elim
      | affine =>
        let bodyInput : VEnv :=
          { middle with
            entries := .slot boundAbs 0 .affine false :: middle.entries
            depth := middle.depth + 1 }
        have hbodyNo : NoRecSelf bodyInput := by
          exact hmiddle.consSlot boundAbs 0 .affine false
        apply lowerE_mapped_body_pop_noRecSelf hexpr
          (bodyInput := bodyInput)
          (by simpa [hzero, bodyInput] using hafterBound)
          (fun _ => rfl) hbodyNo
      | many =>
        let bodyInput : VEnv :=
          { middle with
            entries := .slot boundAbs 0 .many false :: middle.entries
            depth := middle.depth + 1 }
        have hbodyNo : NoRecSelf bodyInput := by
          exact hmiddle.consSlot boundAbs 0 .many false
        apply lowerE_mapped_body_pop_noRecSelf hexpr
          (bodyInput := bodyInput)
          (by simpa [hzero, bodyInput] using hafterBound)
          (fun _ => rfl) hbodyNo
    · let bodyInput : VEnv :=
        { middle with
          entries :=
            .slot boundAbs (countUses 0 body) binderUses true ::
              middle.entries }
      have hbodyNo : NoRecSelf bodyInput := by
        exact hmiddle.consSlot boundAbs (countUses 0 body) binderUses true
      apply lowerE_mapped_body_pop_noRecSelf hexpr
        (bodyInput := bodyInput)
        (by simpa [hzero, bodyInput] using hafterBound)
        (fun _ => rfl) hbodyNo

  | constA atom =>
    by_cases hzero : countUses 0 body = 0
    · let bodyInput : VEnv :=
        { middle with
          entries := .slot middle.depth 0 binderUses false :: middle.entries
          depth := middle.depth + 1 }
      have hbodyNo : NoRecSelf bodyInput := by
        exact hmiddle.consSlot middle.depth 0 binderUses false
      apply lowerE_mapped_body_pop_noRecSelf hexpr
        (bodyInput := bodyInput)
        (by simpa [hzero, bodyInput] using hafterBound)
        (fun _ => rfl) hbodyNo

    · let bodyInput : VEnv :=
        { middle with
          entries :=
            .slot middle.depth (countUses 0 body) binderUses true ::
              middle.entries
          depth := middle.depth + 1 }
      have hbodyNo : NoRecSelf bodyInput := by
        exact hmiddle.consSlot middle.depth (countUses 0 body) binderUses true
      apply lowerE_mapped_body_pop_noRecSelf hexpr
        (bodyInput := bodyInput)
        (by simpa [hzero, bodyInput] using hafterBound)
        (fun _ => rfl) hbodyNo

private theorem lowerE_var_noRecSelf
    {src : IxIR0.Env} {fuel : Nat} {input output : VEnv}
    {world : Owned} {index : Nat} {state finalState : LowSt}
    {emit : Emit} {value : AVal}
    (hrun : (lowerE src (fuel + 1) input world (.var index)).run state =
      .ok (output, emit, value) finalState)
    (hno : NoRecSelf input) : NoRecSelf output := by
  have hssNe : (Owned.shared != Owned.shared) = false := by decide
  have huuNe : (Owned.unique != Owned.unique) = false := by decide
  have hsuNe : (Owned.shared != Owned.unique) = true := by decide
  have husNe : (Owned.unique != Owned.shared) = true := by decide
  have hsuEq : (Owned.shared == Owned.unique) = false := by decide
  have huuEq : (Owned.unique == Owned.unique) = true := by decide
  cases hentry : input.entries[index]? with
  | none => exact (throw_run_not_ok (by
      simpa [lowerE, hentry] using hrun)).elim
  | some entry =>
    cases entry with
    | recSelf arity => exact (hno index arity hentry).elim
    | slot abs remaining uses held =>
      cases held with
      | false => exact (throw_run_not_ok (by
          simpa [lowerE, hentry] using hrun)).elim
      | true =>
        by_cases hworld : worldOfUses uses = world
        · subst world
          have hsame :
              (worldOfUses uses != worldOfUses uses) = false := by
            cases uses <;> decide
          cases remaining with
          | zero => exact (throw_run_not_ok (by
              simpa [lowerE, hentry, hsame] using hrun)).elim
          | succ remaining =>
            cases remaining with
            | zero =>
              have hpure :
                  (input.setEntry index (.slot abs 0 uses false),
                    (_root_.id : Emit), AVal.slotA abs) =
                      (output, emit, value) ∧ state = finalState := by
                simpa [lowerE, hentry, hsame] using hrun
              cases hpure.1
              exact hno.setSlot index abs 0 uses false
            | succ remaining =>
              by_cases hunique : worldOfUses uses = .unique
              · have huniqueEq :
                    (worldOfUses uses == Owned.unique) = true := by
                  rw [hunique]
                  exact huuEq
                exact (throw_run_not_ok (by
                  simpa [lowerE, hentry, hsame, huniqueEq, huuNe]
                    using hrun)).elim
              · have huniqueEq :
                    (worldOfUses uses == Owned.unique) = false := by
                  cases uses <;> simp_all [worldOfUses] <;> decide
                let changed := input.setEntry index
                  (.slot abs (remaining + 1) uses true)
                have hpure :
                    (changed.bump,
                      emitOp (.dup (.var (changed.rel abs))),
                      AVal.slotA changed.depth) =
                        (output, emit, value) ∧ state = finalState := by
                  simpa [lowerE, hentry, hsame, huniqueEq, hssNe, changed]
                    using hrun
                cases hpure.1
                exact (hno.setSlot index abs (remaining + 1) uses true).bump
        · cases uses <;> cases world
          all_goals
            try { exact (hworld (by rfl)).elim }
          all_goals
            exact (throw_run_not_ok (by
              simpa [lowerE, hentry, worldOfUses, hssNe, huuNe, hsuNe,
                husNe, hsuEq, huuEq] using hrun)).elim

theorem lowerEPreservesNoRecSelf_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesNoRecSelf src fuel)
    (hborrow : LowerBorrowPreservesNoRecSelf src fuel)
    (hspine : LowerSpinePreservesNoRecSelf src fuel)
    (hlam : LowerLamPreservesNoRecSelf src fuel) :
    LowerEPreservesNoRecSelf src (fuel + 1) := by
  intro input world expr state finalState output emit value hrun hno
  cases expr with
  | var index => exact lowerE_var_noRecSelf hrun hno
  | ref address =>
    exact hno.of_entries_eq (lowerE_ref_entries_eq_noRecSelf hrun)
  | app function argument =>
    apply hspine
    · simpa [lowerE] using hrun
    · exact hno
  | lam uses body =>
    cases world with
    | unique =>
      have huuEq : (Owned.unique == Owned.unique) = true := by decide
      exact (throw_run_not_ok (by
        simpa [lowerE, huuEq] using hrun)).elim
    | shared =>
      have hsuEq : (Owned.shared == Owned.unique) = false := by decide
      apply hlam
      · simpa [lowerE, hsuEq] using hrun
      · exact hno
  | letE uses bound body => exact lowerE_let_noRecSelf hexpr hrun hno
  | proj fieldIndex source => exact lowerE_proj_noRecSelf hborrow hrun hno
  | lit literal =>
    have hpure :
        (input, (_root_.id : Emit), AVal.constA (.lit literal)) =
            (output, emit, value) ∧ state = finalState := by
      simpa [lowerE] using hrun
    cases hpure.1
    exact hno
  | erased =>
    have hpure :
        (input, (_root_.id : Emit), AVal.constA .erased) =
            (output, emit, value) ∧ state = finalState := by
      simpa [lowerE] using hrun
    cases hpure.1
    exact hno

theorem lowerPreservesNoRecSelf_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hprev : LowerPreservesNoRecSelf src fuel) :
    LowerPreservesNoRecSelf src (fuel + 1) where
  expr := lowerEPreservesNoRecSelf_succ
    hprev.expr hprev.borrow hprev.spine hprev.lam
  borrow := lowerBorrowPreservesNoRecSelf_succ hprev.expr
  spine := lowerSpinePreservesNoRecSelf_succ
    hprev.expr hprev.spine hprev.knownCall hprev.applyRest
  knownCall := knownCallPreservesNoRecSelf_succ hprev.args hprev.applyRest
  args := lowerArgsPreservesNoRecSelf_succ hprev.expr hprev.args
  applyRest := applyRestPreservesNoRecSelf_succ hprev.args
  lam := lowerLamPreservesNoRecSelf_succ

/-- Successful lowering never synthesizes the recursor-only logical entry. -/
theorem lowerPreservesNoRecSelf (src : IxIR0.Env) :
    ∀ fuel, LowerPreservesNoRecSelf src fuel
  | 0 => lowerPreservesNoRecSelf_zero src
  | fuel + 1 =>
    lowerPreservesNoRecSelf_succ (lowerPreservesNoRecSelf src fuel)

theorem lowerE_noRecSelf
    {src : IxIR0.Env} {fuel : Nat} {input output : VEnv}
    {world : Owned} {expr : IxIR0.Expr}
    {state finalState : LowSt} {emit : Emit} {value : AVal}
    (hrun : (lowerE src fuel input world expr).run state =
      .ok (output, emit, value) finalState)
    (hno : NoRecSelf input) : NoRecSelf output :=
  (lowerPreservesNoRecSelf src fuel).expr hrun hno

/-! ## Logical-entry cardinality

The lowering environment may gain physical runtime slots (`depth`), but a
completed expression never gains or loses source-level logical entries.  Let
binders are installed only for the recursive body run and are popped again at
the boundary.  This structural invariant complements exact occurrence
consumption: together they rule out untracked output entries when closing a
generated function body. -/

/-- The output contains exactly as many source-level entries as the input. -/
def EntryCountPreserved (input output : VEnv) : Prop :=
  output.entries.length = input.entries.length

theorem EntryCountPreserved.refl (input : VEnv) :
    EntryCountPreserved input input := rfl

theorem EntryCountPreserved.trans {first middle final : VEnv}
    (hleft : EntryCountPreserved first middle)
    (hright : EntryCountPreserved middle final) :
    EntryCountPreserved first final :=
  Eq.trans hright hleft

theorem EntryCountPreserved.bump {input output : VEnv}
    (h : EntryCountPreserved input output) :
    EntryCountPreserved input output.bump := by
  simpa [EntryCountPreserved, VEnv.bump] using h

theorem releaseAll_preservesEntryCount (input : VEnv) (values : List AVal) :
    EntryCountPreserved input (releaseAll input values).1 := by
  exact releaseAll_traverse_core
    (Result := fun initial _ output _ =>
      EntryCountPreserved initial output)
    (hnil := EntryCountPreserved.refl)
    (hconst := fun htail => htail)
    (hslot := by
      intro initial abs rest output tailEmit htail
      simpa [EntryCountPreserved, VEnv.bump] using htail)
    input values

/-- Entry releases update slots in place and therefore preserve logical-entry
cardinality even though each emitted drop bumps the physical depth. -/
theorem releaseSlots_preservesEntryCount (input : VEnv) :
    ∀ {drops output emit state finalState},
      (releaseSlots input drops).run state =
        .ok (output, emit) finalState →
      EntryCountPreserved input output := by
  intro drops output emit state finalState hrun
  exact releaseSlots_run_core
    (Result := fun initial final _ _ =>
      EntryCountPreserved initial final)
    (hnil := EntryCountPreserved.refl)
    (haffine := by
      intro entry abs rest initial final tailEmit htail
      simpa [EntryCountPreserved, VEnv.bump, VEnv.setEntry] using htail)
    (hmany := by
      intro entry abs rest initial final tailEmit htail
      simpa [EntryCountPreserved, VEnv.bump, VEnv.setEntry] using htail)
    hrun

theorem lowerCapture_preservesEntryCount (expr : IxIR0.Expr) (input : VEnv)
    (index : Nat) {output : VEnv} {emit : Emit} {value : AVal}
    {state finalState : LowSt}
    (hrun : (lowerCapture expr input index).run state =
      .ok (output, emit, value) finalState) :
    EntryCountPreserved input output := by
  cases hentry : input.entries[index]? with
  | none => exact (throw_run_not_ok (by
      simpa [lowerCapture, hentry] using hrun)).elim
  | some entry =>
    cases entry with
    | recSelf arity => exact (throw_run_not_ok (by
        simpa [lowerCapture, hentry] using hrun)).elim
    | slot abs remaining uses held =>
      cases held with
      | false => exact (throw_run_not_ok (by
          simpa [lowerCapture, hentry] using hrun)).elim
      | true =>
        by_cases hunique : worldOfUses uses = .unique
        · have huuEq : (Owned.unique == Owned.unique) = true := by decide
          exact (throw_run_not_ok (by
            simpa [lowerCapture, hentry, hunique, huuEq] using hrun)).elim
        · have huniqueEq :
              (worldOfUses uses == Owned.unique) = false := by
            cases uses <;> simp_all [worldOfUses] <;> decide
          by_cases hmore : remaining > countUses index expr
          · have houtput : output =
                (input.setEntry index
                  (.slot abs (remaining - countUses index expr) uses true)).bump := by
              have hvalue := congrArg
                (fun result : EStateM.Result String LowSt
                    (VEnv × Emit × AVal) =>
                  match result with
                  | .ok value _ => value.1
                  | .error _ _ => input) hrun
              simpa [lowerCapture, hentry, huniqueEq, hmore] using hvalue.symm
            subst output
            simp [EntryCountPreserved, VEnv.setEntry, VEnv.bump]
          · by_cases hequal : remaining = countUses index expr
            · have houtput : output =
                  input.setEntry index (.slot abs 0 uses false) := by
                have hvalue := congrArg
                  (fun result : EStateM.Result String LowSt
                      (VEnv × Emit × AVal) =>
                    match result with
                    | .ok value _ => value.1
                    | .error _ _ => input) hrun
                simpa [lowerCapture, hentry, huniqueEq, hmore, hequal]
                  using hvalue.symm
              subst output
              simp [EntryCountPreserved, VEnv.setEntry]
            · exact (throw_run_not_ok (by
                simpa [lowerCapture, hentry, huniqueEq, hmore, hequal]
                  using hrun)).elim

theorem lowerCaptures_preservesEntryCount (expr : IxIR0.Expr) :
    ∀ {indices input output emit values state finalState},
      (lowerCaptures expr input indices).run state =
        .ok (output, emit, values) finalState →
      EntryCountPreserved input output := by
  intro indices input output emit values state finalState hrun
  apply lowerCaptures_run_core
    (Result := fun input output _ _ _ =>
      EntryCountPreserved input output)
    (e := expr) (hrun := hrun)
  · intro input
    exact .refl input
  · intro index rest input middle output headEmit tailEmit headValue
      tailValues state middleState hheadRun htail
    exact (lowerCapture_preservesEntryCount expr input index hheadRun).trans
      htail

def LowerEPreservesEntryCount (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {world : Owned} {expr : IxIR0.Expr}
      {state finalState : LowSt} {output : VEnv} {emit : Emit} {value : AVal},
    (lowerE src fuel input world expr).run state =
      .ok (output, emit, value) finalState →
    EntryCountPreserved input output

def LowerBorrowPreservesEntryCount (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {expr : IxIR0.Expr} {state finalState : LowSt}
      {output : VEnv} {emit : Emit} {value : AVal} {release : Bool},
    (lowerBorrow src fuel input expr).run state =
      .ok (output, emit, value, release) finalState →
    EntryCountPreserved input output

def LowerSpinePreservesEntryCount (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {world : Owned} {head : IxIR0.Expr}
      {args : List IxIR0.Expr} {state finalState : LowSt}
      {output : VEnv} {emit : Emit} {value : AVal},
    (lowerSpine src fuel input world head args).run state =
      .ok (output, emit, value) finalState →
    EntryCountPreserved input output

def KnownCallPreservesEntryCount (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {build : Array Atom → Op} {count : Nat}
      {argWorlds : List Owned} {resultWorld : Owned}
      {args : List IxIR0.Expr} {state finalState : LowSt}
      {output : VEnv} {emit : Emit} {value : AVal},
    (knownCall src fuel input build count argWorlds resultWorld args).run
      state = .ok (output, emit, value) finalState →
    EntryCountPreserved input output

def LowerArgsPreservesEntryCount (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {args : List (IxIR0.Expr × Owned)}
      {state finalState : LowSt} {output : VEnv}
      {emit : Emit} {values : List AVal},
    (lowerArgs src fuel input args).run state =
      .ok (output, emit, values) finalState →
    EntryCountPreserved input output

def ApplyRestPreservesEntryCount (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {resultWorld : Owned} {pre : Emit}
      {function : AVal} {args : List IxIR0.Expr}
      {state finalState : LowSt} {output : VEnv}
      {emit : Emit} {value : AVal},
    (applyRest src fuel input resultWorld pre function args).run state =
      .ok (output, emit, value) finalState →
    EntryCountPreserved input output

def LowerLamPreservesEntryCount (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {expr : IxIR0.Expr} {state finalState : LowSt}
      {output : VEnv} {emit : Emit} {value : AVal},
    (lowerLam src fuel input expr).run state =
      .ok (output, emit, value) finalState →
    EntryCountPreserved input output

structure LowerPreservesEntryCount (src : IxIR0.Env) (fuel : Nat) : Prop where
  expr : LowerEPreservesEntryCount src fuel
  borrow : LowerBorrowPreservesEntryCount src fuel
  spine : LowerSpinePreservesEntryCount src fuel
  knownCall : KnownCallPreservesEntryCount src fuel
  args : LowerArgsPreservesEntryCount src fuel
  applyRest : ApplyRestPreservesEntryCount src fuel
  lam : LowerLamPreservesEntryCount src fuel

theorem lowerPreservesEntryCount_zero (src : IxIR0.Env) :
    LowerPreservesEntryCount src 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro input world expr state finalState output emit value hrun
    exact (throw_run_not_ok (by simpa [lowerE] using hrun)).elim
  · intro input expr state finalState output emit value release hrun
    exact (throw_run_not_ok (by simpa [lowerBorrow] using hrun)).elim
  · intro input world head args state finalState output emit value hrun
    exact (throw_run_not_ok (by simpa [lowerSpine] using hrun)).elim
  · intro input build count argWorlds resultWorld args state finalState
      output emit value hrun
    exact (throw_run_not_ok (by simpa [knownCall] using hrun)).elim
  · intro input args state finalState output emit values hrun
    exact (throw_run_not_ok (by simpa [lowerArgs] using hrun)).elim
  · intro input resultWorld pre function args state finalState output emit
      value hrun
    exact (throw_run_not_ok (by simpa [applyRest] using hrun)).elim
  · intro input expr state finalState output emit value hrun
    exact (throw_run_not_ok (by simpa [lowerLam] using hrun)).elim

theorem lowerArgsPreservesEntryCount_succ {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesEntryCount src fuel)
    (hargs : LowerArgsPreservesEntryCount src fuel) :
    LowerArgsPreservesEntryCount src (fuel + 1) := by
  intro input args state finalState output emit values hrun
  cases args with
  | nil =>
    have hpure :
        (input, (_root_.id : Emit), []) = (output, emit, values) ∧
          state = finalState := by
      simpa [lowerArgs] using hrun
    cases hpure.1
    exact .refl input
  | cons head rest =>
    rcases head with ⟨expr, world⟩
    simp only [lowerArgs] at hrun
    obtain ⟨headResult, middleState, hheadRun, hafterHead⟩ :=
      bind_run_ok_inv hrun
    rcases headResult with ⟨middle, headEmit, headValue⟩
    obtain ⟨tailResult, tailState, htailRun, hafterTail⟩ :=
      bind_run_ok_inv hafterHead
    rcases tailResult with ⟨actualOutput, tailEmit, tailValues⟩
    have hvalue : actualOutput = output := by
      have hpure :
          (actualOutput, headEmit ∘ tailEmit, headValue :: tailValues) =
              (output, emit, values) ∧ tailState = finalState := by
        simpa using hafterTail
      exact congrArg Prod.fst hpure.1
    subst output
    exact (hexpr hheadRun).trans (hargs htailRun)

theorem applyRestPreservesEntryCount_succ {src : IxIR0.Env} {fuel : Nat}
    (hargs : LowerArgsPreservesEntryCount src fuel) :
    ApplyRestPreservesEntryCount src (fuel + 1) := by
  intro input resultWorld pre function args state finalState output emit value
    hrun
  cases function with
  | constA atom =>
    cases atom with
    | erased =>
      simp only [applyRest] at hrun
      obtain ⟨argsResult, argsState, hargsRun, hpureRun⟩ :=
        bind_run_ok_inv hrun
      rcases argsResult with ⟨middle, argsEmit, values⟩
      have hpure : (releaseAll middle values).1 = output := by
        have hvalue :
            ((releaseAll middle values).1,
              pre ∘ argsEmit ∘ (releaseAll middle values).2,
              AVal.constA .erased) = (output, emit, value) ∧
              argsState = finalState := by
          simpa using hpureRun
        exact congrArg Prod.fst hvalue.1
      subst output
      exact (hargs hargsRun).trans
        (releaseAll_preservesEntryCount middle values)
    | var relative =>
      simp only [applyRest] at hrun
      obtain ⟨_, checkedState, _, hafterCheck⟩ := bind_run_ok_inv hrun
      obtain ⟨argsResult, argsState, hargsRun, hpureRun⟩ :=
        bind_run_ok_inv hafterCheck
      rcases argsResult with ⟨middle, argsEmit, values⟩
      have houtput : middle.bump = output := by
        have hvalue := congrArg
          (fun result : EStateM.Result String LowSt (VEnv × Emit × AVal) =>
            match result with
            | .ok value _ => value.1
            | .error _ _ => input) hpureRun
        simpa using hvalue
      subst output
      exact (hargs hargsRun).bump
    | lit literal =>
      simp only [applyRest] at hrun
      obtain ⟨_, checkedState, _, hafterCheck⟩ := bind_run_ok_inv hrun
      obtain ⟨argsResult, argsState, hargsRun, hpureRun⟩ :=
        bind_run_ok_inv hafterCheck
      rcases argsResult with ⟨middle, argsEmit, values⟩
      have houtput : middle.bump = output := by
        have hvalue := congrArg
          (fun result : EStateM.Result String LowSt (VEnv × Emit × AVal) =>
            match result with
            | .ok value _ => value.1
            | .error _ _ => input) hpureRun
        simpa using hvalue
      subst output
      exact (hargs hargsRun).bump
  | slotA abs =>
    simp only [applyRest] at hrun
    obtain ⟨_, checkedState, _, hafterCheck⟩ := bind_run_ok_inv hrun
    obtain ⟨argsResult, argsState, hargsRun, hpureRun⟩ :=
      bind_run_ok_inv hafterCheck
    rcases argsResult with ⟨middle, argsEmit, values⟩
    have houtput : middle.bump = output := by
      have hvalue := congrArg
        (fun result : EStateM.Result String LowSt (VEnv × Emit × AVal) =>
          match result with
          | .ok value _ => value.1
          | .error _ _ => input) hpureRun
      simpa using hvalue
    subst output
    exact (hargs hargsRun).bump

theorem knownCallPreservesEntryCount_succ {src : IxIR0.Env} {fuel : Nat}
    (hargs : LowerArgsPreservesEntryCount src fuel)
    (hrest : ApplyRestPreservesEntryCount src fuel) :
    KnownCallPreservesEntryCount src (fuel + 1) := by
  intro input build count argWorlds resultWorld args state finalState output
    emit value hrun
  simp only [knownCall] at hrun
  obtain ⟨argsResult, argsState, hargsRun, hafterArgs⟩ :=
    bind_run_ok_inv hrun
  rcases argsResult with ⟨middle, argsEmit, values⟩
  have hmiddle := hargs hargsRun
  by_cases hterminal : args.length ≤ count
  · have houtput : middle.bump = output := by
      have hvalue := congrArg
        (fun result : EStateM.Result String LowSt (VEnv × Emit × AVal) =>
          match result with
          | .ok value _ => value.1
          | .error _ _ => input) hafterArgs
      simpa [hterminal] using hvalue
    subst output
    exact hmiddle.bump
  · have hrestRun :
        (applyRest src fuel middle.bump resultWorld
          (argsEmit ∘ emitOp
            (build (values.map (·.toAtom middle)).toArray))
          (.slotA middle.depth) (args.drop count)).run argsState =
            .ok (output, emit, value) finalState := by
      simpa [hterminal] using hafterArgs
    exact hmiddle.bump.trans (hrest hrestRun)

private theorem lowerBorrow_dynamic_preservesEntryCount
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesEntryCount src fuel)
    {input output : VEnv} {expr : IxIR0.Expr}
    {state finalState : LowSt} {emit : Emit} {value : AVal}
    {releaseFlag : Bool}
    {finish : (VEnv × Emit × AVal) → (VEnv × Emit × AVal × Bool)}
    (hrun : (finish <$> lowerE src fuel input .shared expr).run state =
        .ok (output, emit, value, releaseFlag) finalState)
    (hfinish : ∀ result, (finish result).1 = result.1) :
    EntryCountPreserved input output := by
  obtain ⟨exprResult, hexprRun, hvalue⟩ := map_run_ok_inv hrun
  rcases exprResult with ⟨middle, middleEmit, middleValue⟩
  have houtput : middle = output := by
    have := congrArg Prod.fst hvalue
    simpa [hfinish] using this
  subst output
  exact hexpr hexprRun

theorem lowerBorrowPreservesEntryCount_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesEntryCount src fuel) :
    LowerBorrowPreservesEntryCount src (fuel + 1) := by
  intro input expr state finalState output emit value release hrun
  cases expr with
  | var index =>
    cases hentry : input.entries[index]? with
    | none => exact (throw_run_not_ok (by
        simpa [lowerBorrow, hentry] using hrun)).elim
    | some entry =>
      cases entry with
      | recSelf arity => exact (throw_run_not_ok (by
          simpa [lowerBorrow, hentry] using hrun)).elim
      | slot abs remaining uses held =>
        cases held with
        | false => exact (throw_run_not_ok (by
            simpa [lowerBorrow, hentry] using hrun)).elim
        | true =>
          by_cases hunique : worldOfUses uses = .unique
          · have huuEq : (Owned.unique == Owned.unique) = true := by decide
            exact (throw_run_not_ok (by
              simpa [lowerBorrow, hentry, hunique, huuEq] using hrun)).elim
          · have huniqueEq :
                (worldOfUses uses == Owned.unique) = false := by
              cases uses <;> simp_all [worldOfUses] <;> decide
            cases remaining with
            | zero => exact (throw_run_not_ok (by
                simpa [lowerBorrow, hentry, huniqueEq] using hrun)).elim
            | succ remaining =>
              cases remaining with
              | zero =>
                have hpure :
                    (input.setEntry index (.slot abs 0 uses false),
                      (_root_.id : Emit), AVal.slotA abs, true) =
                        (output, emit, value, release) ∧
                      state = finalState := by
                  simpa [lowerBorrow, hentry, huniqueEq] using hrun
                cases hpure.1
                simp [EntryCountPreserved, VEnv.setEntry]
              | succ remaining =>
                have hpure :
                    (input.setEntry index
                        (.slot abs (remaining + 1) uses true),
                      (_root_.id : Emit), AVal.slotA abs, false) =
                        (output, emit, value, release) ∧
                      state = finalState := by
                  simpa [lowerBorrow, hentry, huniqueEq] using hrun
                cases hpure.1
                simp [EntryCountPreserved, VEnv.setEntry]
  | ref address =>
    apply lowerBorrow_dynamic_preservesEntryCount hexpr
      (by simpa [lowerBorrow] using hrun) (fun _ => rfl)
  | app function argument =>
    apply lowerBorrow_dynamic_preservesEntryCount hexpr
      (by simpa [lowerBorrow] using hrun) (fun _ => rfl)
  | lam uses body =>
    apply lowerBorrow_dynamic_preservesEntryCount hexpr
      (by simpa [lowerBorrow] using hrun) (fun _ => rfl)
  | letE uses value body =>
    apply lowerBorrow_dynamic_preservesEntryCount hexpr
      (by simpa [lowerBorrow] using hrun) (fun _ => rfl)
  | proj index source =>
    apply lowerBorrow_dynamic_preservesEntryCount hexpr
      (by simpa [lowerBorrow] using hrun) (fun _ => rfl)
  | lit literal =>
    apply lowerBorrow_dynamic_preservesEntryCount hexpr
      (by simpa [lowerBorrow] using hrun) (fun _ => rfl)
  | erased =>
    apply lowerBorrow_dynamic_preservesEntryCount hexpr
      (by simpa [lowerBorrow] using hrun) (fun _ => rfl)

private theorem lowerE_applyRest_preservesEntryCount
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesEntryCount src fuel)
    (hrest : ApplyRestPreservesEntryCount src fuel)
    {input output : VEnv} {world : Owned} {head : IxIR0.Expr}
    {args : List IxIR0.Expr} {state finalState : LowSt}
    {emit : Emit} {value : AVal}
    (hrun : (do
      let (middle, headEmit, function) ←
        lowerE src fuel input .shared head
      applyRest src fuel middle world headEmit function args).run state =
        .ok (output, emit, value) finalState) :
    EntryCountPreserved input output := by
  obtain ⟨headResult, middleState, hheadRun, hrestRun⟩ :=
    bind_run_ok_inv hrun
  rcases headResult with ⟨middle, headEmit, function⟩
  exact (hexpr hheadRun).trans (hrest hrestRun)

theorem lowerSpinePreservesEntryCount_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesEntryCount src fuel)
    (hspine : LowerSpinePreservesEntryCount src fuel)
    (hknown : KnownCallPreservesEntryCount src fuel)
    (hrest : ApplyRestPreservesEntryCount src fuel) :
    LowerSpinePreservesEntryCount src (fuel + 1) := by
  intro input world head args state finalState output emit value hrun
  have hsuEq : (Owned.shared == Owned.unique) = false := by decide
  cases head with
  | app function argument =>
    apply hspine
    simpa [lowerSpine] using hrun
  | erased =>
    apply hrest
    simpa [lowerSpine] using hrun
  | var index =>
    simp only [lowerSpine] at hrun
    cases hentry : input.entries[index]? with
    | none =>
      apply lowerE_applyRest_preservesEntryCount hexpr hrest
      simpa [hentry] using hrun
    | some entry =>
      cases entry with
      | recSelf arity =>
        rw [hentry] at hrun
        simp only at hrun
        by_cases hunder : args.length < arity
        · rw [if_pos hunder] at hrun
          exact (throw_run_not_ok hrun).elim
        · rw [if_neg hunder] at hrun
          obtain ⟨unitValue, checkedState, _, hknownRun⟩ :=
            bind_run_ok_inv hrun
          cases unitValue
          exact hknown hknownRun
      | slot abs remaining uses held =>
        apply lowerE_applyRest_preservesEntryCount hexpr hrest
        simpa [hentry] using hrun
  | ref address =>
    simp only [lowerSpine] at hrun
    cases hsource : src address with
    | none =>
      rw [hsource] at hrun
      exact (throw_run_not_ok hrun).elim
    | some decl =>
      rw [hsource] at hrun
      cases decl with
      | defn result body =>
        simp only at hrun
        by_cases hunder : args.length < lamArity body
        · rw [if_pos hunder] at hrun
          cases world with
          | unique => exact (throw_run_not_ok hrun).elim
          | shared =>
            cases result with
            | unique => exact (throw_run_not_ok hrun).elim
            | shared =>
              cases hp : papSafe body with
              | false => exact (throw_run_not_ok (by
                  simpa [hp, hsuEq] using hrun)).elim
              | true =>
                apply hknown
                simpa [hp, hsuEq] using hrun
        · rw [if_neg hunder] at hrun
          obtain ⟨_, checkedState, _, hknownRun⟩ := bind_run_ok_inv hrun
          exact hknown hknownRun
      | ctor tag arity =>
        simp only at hrun
        by_cases hunder : args.length < arity
        · rw [if_pos hunder] at hrun
          cases world with
          | unique => exact (throw_run_not_ok hrun).elim
          | shared =>
            obtain ⟨wrapper, wrapperState, _, hknownRun⟩ :=
              bind_run_ok_inv hrun
            exact hknown hknownRun
        · rw [if_neg hunder] at hrun
          exact hknown hrun
      | recursor numArgs natLit rules =>
        simp only at hrun
        by_cases hunder : args.length < numArgs + 1
        · rw [if_pos hunder] at hrun
          cases world with
          | unique => exact (throw_run_not_ok hrun).elim
          | shared => exact hknown hrun
        · rw [if_neg hunder] at hrun
          obtain ⟨_, checkedState, _, hknownRun⟩ := bind_run_ok_inv hrun
          exact hknown hknownRun
      | extern arity =>
        simp only at hrun
        by_cases hunder : args.length < arity
        · rw [if_pos hunder] at hrun
          cases world with
          | unique => exact (throw_run_not_ok hrun).elim
          | shared => exact hknown hrun
        · rw [if_neg hunder] at hrun
          exact hknown hrun
  | lam uses body =>
    apply lowerE_applyRest_preservesEntryCount hexpr hrest
    simpa [lowerSpine] using hrun
  | letE uses bound body =>
    apply lowerE_applyRest_preservesEntryCount hexpr hrest
    simpa [lowerSpine] using hrun
  | proj index source =>
    apply lowerE_applyRest_preservesEntryCount hexpr hrest
    simpa [lowerSpine] using hrun
  | lit literal =>
    apply lowerE_applyRest_preservesEntryCount hexpr hrest
    simpa [lowerSpine] using hrun

theorem lowerLamPreservesEntryCount_succ
    {src : IxIR0.Env} {fuel : Nat} :
    LowerLamPreservesEntryCount src (fuel + 1) := by
  intro input expr state finalState output emit value hrun
  cases hp : papSafe expr with
  | false => simp [lowerLam, hp] at hrun
  | true =>
    simp only [lowerLam] at hrun
    simp only [hp, ↓reduceIte, bind_pure_comp] at hrun
    let captures := (List.range input.entries.length).filter
      (fun index => countUses index expr > 0)
    have hcaptures : captures = (List.range input.entries.length).filter
        (fun index => countUses index expr > 0) := rfl
    rw [← hcaptures] at hrun
    obtain ⟨captureResult, captureState, hcaptureRun, hafterCapture⟩ :=
      bind_run_ok_inv hrun
    rcases captureResult with ⟨captureOutput, captureEmit, captureValues⟩
    obtain ⟨fnAddr, addressState, _, hafterFresh⟩ :=
      bind_run_ok_inv hafterCapture
    obtain ⟨code, bodyState, _, hafterBody⟩ :=
      bind_run_ok_inv hafterFresh
    obtain ⟨_, _, hvalue⟩ := map_run_ok_inv hafterBody
    have houtput : captureOutput.bump = output :=
      congrArg Prod.fst hvalue
    subst output
    exact (lowerCaptures_preservesEntryCount expr hcaptureRun).bump

private theorem lowerE_proj_preservesEntryCount
    {src : IxIR0.Env} {fuel : Nat}
    (hborrow : LowerBorrowPreservesEntryCount src fuel)
    {input output : VEnv} {world : Owned} {fieldIndex : Nat}
    {source : IxIR0.Expr} {state finalState : LowSt}
    {emit : Emit} {value : AVal}
    (hrun : (lowerE src (fuel + 1) input world
      (.proj fieldIndex source)).run state =
        .ok (output, emit, value) finalState) :
    EntryCountPreserved input output := by
  cases world with
  | unique =>
    have huuEq : (Owned.unique == Owned.unique) = true := by decide
    simp [lowerE, huuEq] at hrun
  | shared =>
    have hsuEq : (Owned.shared == Owned.unique) = false := by decide
    simp only [lowerE, hsuEq, Bool.false_eq_true, if_false] at hrun
    obtain ⟨borrowResult, middleState, hborrowRun, hafterBorrow⟩ :=
      bind_run_ok_inv hrun
    rcases borrowResult with
      ⟨borrowOutput, borrowEmit, borrowed, release⟩
    have hborrowCount := hborrow hborrowRun
    cases borrowed with
    | constA atom =>
      cases atom with
      | var relative =>
        have hpure : borrowOutput.bump = output := by
          have hvalue := congrArg
            (fun result : EStateM.Result String LowSt
                (VEnv × Emit × AVal) =>
              match result with
              | .ok value _ => value.1
              | .error _ _ => input) hafterBorrow
          simpa using hvalue
        subst output
        exact hborrowCount.bump
      | lit literal =>
        have hpure : borrowOutput.bump = output := by
          have hvalue := congrArg
            (fun result : EStateM.Result String LowSt
                (VEnv × Emit × AVal) =>
              match result with
              | .ok value _ => value.1
              | .error _ _ => input) hafterBorrow
          simpa using hvalue
        subst output
        exact hborrowCount.bump
      | erased =>
        have hpure : borrowOutput = output := by
          have hvalue := congrArg
            (fun result : EStateM.Result String LowSt
                (VEnv × Emit × AVal) =>
              match result with
              | .ok value _ => value.1
              | .error _ _ => input) hafterBorrow
          simpa using hvalue
        subst output
        exact hborrowCount
    | slotA targetAbs =>
      cases release with
      | false =>
        have hpure : borrowOutput.bump.bump = output := by
          have hvalue := congrArg
            (fun result : EStateM.Result String LowSt
                (VEnv × Emit × AVal) =>
              match result with
              | .ok value _ => value.1
              | .error _ _ => input) hafterBorrow
          simpa using hvalue
        subst output
        exact hborrowCount.bump.bump
      | true =>
        have hpure : borrowOutput.bump.bump.bump = output := by
          have hvalue := congrArg
            (fun result : EStateM.Result String LowSt
                (VEnv × Emit × AVal) =>
              match result with
              | .ok value _ => value.1
              | .error _ _ => input) hafterBorrow
          simpa using hvalue
        subst output
        exact hborrowCount.bump.bump.bump

private theorem lowerE_mapped_body_pop_preservesEntryCount
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesEntryCount src fuel)
    {middle bodyInput output : VEnv} {world : Owned} {body : IxIR0.Expr}
    {state finalState : LowSt} {emit : Emit} {value : AVal}
    {finish : (VEnv × Emit × AVal) → (VEnv × Emit × AVal)}
    {binder : VEntry}
    (hrun : (finish <$> lowerE src fuel bodyInput world body).run state =
      .ok (output, emit, value) finalState)
    (hfinish : ∀ result, (finish result).1 = result.1.pop)
    (hentries : bodyInput.entries = binder :: middle.entries) :
    EntryCountPreserved middle output := by
  obtain ⟨bodyResult, hbodyRun, hvalue⟩ := map_run_ok_inv hrun
  rcases bodyResult with ⟨bodyOutput, bodyEmit, bodyValue⟩
  have houtput : bodyOutput.pop = output := by
    have := congrArg Prod.fst hvalue
    simpa [hfinish] using this
  subst output
  have hbodyCount := hexpr hbodyRun
  rw [EntryCountPreserved] at hbodyCount ⊢
  simp only [VEnv.pop]
  rw [List.length_tail]
  rw [hbodyCount, hentries]
  simp

private theorem lowerE_let_preservesEntryCount
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesEntryCount src fuel)
    {input output : VEnv} {world : Owned} {binderUses : Uses}
    {bound body : IxIR0.Expr} {state finalState : LowSt}
    {emit : Emit} {value : AVal}
    (hrun : (lowerE src (fuel + 1) input world
      (.letE binderUses bound body)).run state =
        .ok (output, emit, value) finalState) :
    EntryCountPreserved input output := by
  simp only [lowerE] at hrun
  obtain ⟨boundResult, boundState, hboundRun, hafterBound⟩ :=
    bind_run_ok_inv hrun
  rcases boundResult with ⟨middle, boundEmit, boundValue⟩
  have hmiddle := hexpr hboundRun
  cases boundValue with
  | slotA boundAbs =>
    by_cases hzero : countUses 0 body = 0
    · cases binderUses with
      | erased =>
        obtain ⟨_, _, hthrow, _⟩ := bind_run_ok_inv
          (by simpa [hzero] using hafterBound)
        exact (throw_run_not_ok hthrow).elim
      | linear =>
        obtain ⟨_, _, hthrow, _⟩ := bind_run_ok_inv
          (by simpa [hzero] using hafterBound)
        exact (throw_run_not_ok hthrow).elim
      | affine =>
        let bodyInput : VEnv :=
          { middle with
            entries := .slot boundAbs 0 .affine false :: middle.entries
            depth := middle.depth + 1 }
        apply hmiddle.trans
        apply lowerE_mapped_body_pop_preservesEntryCount hexpr
          (middle := middle) (bodyInput := bodyInput)
          (by simpa [hzero, bodyInput] using hafterBound)
          (fun _ => rfl)
        rfl
      | many =>
        let bodyInput : VEnv :=
          { middle with
            entries := .slot boundAbs 0 .many false :: middle.entries
            depth := middle.depth + 1 }
        apply hmiddle.trans
        apply lowerE_mapped_body_pop_preservesEntryCount hexpr
          (middle := middle) (bodyInput := bodyInput)
          (by simpa [hzero, bodyInput] using hafterBound)
          (fun _ => rfl)
        rfl
    · let bodyInput : VEnv :=
        { middle with
          entries :=
            .slot boundAbs (countUses 0 body) binderUses true ::
              middle.entries }
      apply hmiddle.trans
      apply lowerE_mapped_body_pop_preservesEntryCount hexpr
        (middle := middle) (bodyInput := bodyInput)
        (by simpa [hzero, bodyInput] using hafterBound)
        (fun _ => rfl)
      rfl
  | constA atom =>
    by_cases hzero : countUses 0 body = 0
    · let bodyInput : VEnv :=
        { middle with
          entries := .slot middle.depth 0 binderUses false :: middle.entries
          depth := middle.depth + 1 }
      apply hmiddle.trans
      apply lowerE_mapped_body_pop_preservesEntryCount hexpr
        (middle := middle) (bodyInput := bodyInput)
        (by simpa [hzero, bodyInput] using hafterBound)
        (fun _ => rfl)
      rfl
    · let bodyInput : VEnv :=
        { middle with
          entries :=
            .slot middle.depth (countUses 0 body) binderUses true ::
              middle.entries
          depth := middle.depth + 1 }
      apply hmiddle.trans
      apply lowerE_mapped_body_pop_preservesEntryCount hexpr
        (middle := middle) (bodyInput := bodyInput)
        (by simpa [hzero, bodyInput] using hafterBound)
        (fun _ => rfl)
      rfl

private theorem lowerE_var_preservesEntryCount
    {src : IxIR0.Env} {fuel : Nat} {input output : VEnv}
    {world : Owned} {index : Nat} {state finalState : LowSt}
    {emit : Emit} {value : AVal}
    (hrun : (lowerE src (fuel + 1) input world (.var index)).run state =
      .ok (output, emit, value) finalState) :
    EntryCountPreserved input output := by
  have hssNe : (Owned.shared != Owned.shared) = false := by decide
  have huuNe : (Owned.unique != Owned.unique) = false := by decide
  have hsuNe : (Owned.shared != Owned.unique) = true := by decide
  have husNe : (Owned.unique != Owned.shared) = true := by decide
  have hsuEq : (Owned.shared == Owned.unique) = false := by decide
  have huuEq : (Owned.unique == Owned.unique) = true := by decide
  cases hentry : input.entries[index]? with
  | none => exact (throw_run_not_ok (by
      simpa [lowerE, hentry] using hrun)).elim
  | some entry =>
    cases entry with
    | recSelf arity => exact (throw_run_not_ok (by
        simpa [lowerE, hentry] using hrun)).elim
    | slot abs remaining uses held =>
      cases held with
      | false => exact (throw_run_not_ok (by
          simpa [lowerE, hentry] using hrun)).elim
      | true =>
        by_cases hworld : worldOfUses uses = world
        · subst world
          have hsame :
              (worldOfUses uses != worldOfUses uses) = false := by
            cases uses <;> decide
          cases remaining with
          | zero => exact (throw_run_not_ok (by
              simpa [lowerE, hentry, hsame] using hrun)).elim
          | succ remaining =>
            cases remaining with
            | zero =>
              have hpure :
                  (input.setEntry index (.slot abs 0 uses false),
                    (_root_.id : Emit), AVal.slotA abs) =
                      (output, emit, value) ∧ state = finalState := by
                simpa [lowerE, hentry, hsame] using hrun
              cases hpure.1
              simp [EntryCountPreserved, VEnv.setEntry]
            | succ remaining =>
              by_cases hunique : worldOfUses uses = .unique
              · have huniqueEq :
                    (worldOfUses uses == Owned.unique) = true := by
                  rw [hunique]
                  exact huuEq
                exact (throw_run_not_ok (by
                  simpa [lowerE, hentry, hsame, huniqueEq, huuNe]
                    using hrun)).elim
              · have huniqueEq :
                    (worldOfUses uses == Owned.unique) = false := by
                  cases uses <;> simp_all [worldOfUses] <;> decide
                let changed := input.setEntry index
                  (.slot abs (remaining + 1) uses true)
                have hpure :
                    (changed.bump,
                      emitOp (.dup (.var (changed.rel abs))),
                      AVal.slotA changed.depth) =
                        (output, emit, value) ∧ state = finalState := by
                  simpa [lowerE, hentry, hsame, huniqueEq, hssNe, changed]
                    using hrun
                cases hpure.1
                simp [EntryCountPreserved, changed, VEnv.setEntry, VEnv.bump]
        · cases uses <;> cases world
          all_goals
            try { exact (hworld (by rfl)).elim }
          all_goals
            exact (throw_run_not_ok (by
              simpa [lowerE, hentry, worldOfUses, hssNe, huuNe, hsuNe,
                husNe, hsuEq, huuEq] using hrun)).elim

theorem lowerEPreservesEntryCount_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesEntryCount src fuel)
    (hborrow : LowerBorrowPreservesEntryCount src fuel)
    (hspine : LowerSpinePreservesEntryCount src fuel)
    (hlam : LowerLamPreservesEntryCount src fuel) :
    LowerEPreservesEntryCount src (fuel + 1) := by
  intro input world expr state finalState output emit value hrun
  cases expr with
  | var index => exact lowerE_var_preservesEntryCount hrun
  | ref address =>
    exact congrArg List.length (lowerE_ref_entries_eq_noRecSelf hrun)
  | app function argument =>
    apply hspine
    simpa [lowerE] using hrun
  | lam uses body =>
    cases world with
    | unique =>
      have huuEq : (Owned.unique == Owned.unique) = true := by decide
      exact (throw_run_not_ok (by
        simpa [lowerE, huuEq] using hrun)).elim
    | shared =>
      have hsuEq : (Owned.shared == Owned.unique) = false := by decide
      apply hlam
      simpa [lowerE, hsuEq] using hrun
  | letE uses bound body => exact lowerE_let_preservesEntryCount hexpr hrun
  | proj fieldIndex source =>
    exact lowerE_proj_preservesEntryCount hborrow hrun
  | lit literal =>
    have hpure :
        (input, (_root_.id : Emit), AVal.constA (.lit literal)) =
            (output, emit, value) ∧ state = finalState := by
      simpa [lowerE] using hrun
    cases hpure.1
    exact .refl input
  | erased =>
    have hpure :
        (input, (_root_.id : Emit), AVal.constA .erased) =
            (output, emit, value) ∧ state = finalState := by
      simpa [lowerE] using hrun
    cases hpure.1
    exact .refl input

theorem lowerPreservesEntryCount_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hprev : LowerPreservesEntryCount src fuel) :
    LowerPreservesEntryCount src (fuel + 1) where
  expr := lowerEPreservesEntryCount_succ
    hprev.expr hprev.borrow hprev.spine hprev.lam
  borrow := lowerBorrowPreservesEntryCount_succ hprev.expr
  spine := lowerSpinePreservesEntryCount_succ
    hprev.expr hprev.spine hprev.knownCall hprev.applyRest
  knownCall := knownCallPreservesEntryCount_succ hprev.args hprev.applyRest
  args := lowerArgsPreservesEntryCount_succ hprev.expr hprev.args
  applyRest := applyRestPreservesEntryCount_succ hprev.args
  lam := lowerLamPreservesEntryCount_succ

/-- Successful expression lowering preserves the cardinality of its logical
source environment, even though emitted operations may increase runtime depth. -/
theorem lowerPreservesEntryCount (src : IxIR0.Env) :
    ∀ fuel, LowerPreservesEntryCount src fuel
  | 0 => lowerPreservesEntryCount_zero src
  | fuel + 1 =>
    lowerPreservesEntryCount_succ (lowerPreservesEntryCount src fuel)

theorem lowerE_preservesEntryCount
    {src : IxIR0.Env} {fuel : Nat} {input output : VEnv}
    {world : Owned} {expr : IxIR0.Expr}
    {state finalState : LowSt} {emit : Emit} {value : AVal}
    (hrun : (lowerE src fuel input world expr).run state =
      .ok (output, emit, value) finalState) :
    EntryCountPreserved input output :=
  (lowerPreservesEntryCount src fuel).expr hrun

/-! ## Recursive-self entry preservation

Unlike an ordinary slot, the synthetic recursor entry carries no ownership.
Successful lowering may inspect it only as the head of a saturated recursive
call; it never rewrites it.  The pointwise invariant below records that fact
without imposing any restriction on the ordinary entries around it. -/

def RecSelfAt (input : VEnv) (index arity : Nat) : Prop :=
  input.entries[index]? = some (.recSelf arity)

theorem RecSelfAt.bump {input : VEnv} {index arity : Nat}
    (hself : RecSelfAt input index arity) :
    RecSelfAt input.bump index arity := by
  simpa [RecSelfAt, VEnv.bump] using hself

theorem RecSelfAt.of_entries_eq {input output : VEnv}
    {index arity : Nat} (hentries : output.entries = input.entries)
    (hself : RecSelfAt input index arity) :
    RecSelfAt output index arity := by
  simpa [RecSelfAt, hentries] using hself

theorem RecSelfAt.setSlot {input : VEnv} {index arity changed : Nat}
    {oldAbs oldRemaining : Nat} {oldUses : Uses} {oldHeld : Bool}
    (hself : RecSelfAt input index arity)
    (hslot : input.entries[changed]? =
      some (.slot oldAbs oldRemaining oldUses oldHeld))
    (newAbs newRemaining : Nat) (newUses : Uses) (newHeld : Bool) :
    RecSelfAt
      (input.setEntry changed
        (.slot newAbs newRemaining newUses newHeld))
      index arity := by
  have hne : changed ≠ index := by
    intro heq
    subst changed
    rw [hself] at hslot
    cases hslot
  rw [RecSelfAt, VEnv.setEntry, List.getElem?_set]
  simp [hne]
  exact hself

theorem RecSelfAt.cons {input : VEnv} {index arity : Nat}
    {entry : VEntry} (hself : RecSelfAt input index arity) :
    RecSelfAt { input with entries := entry :: input.entries }
      (index + 1) arity := by
  simpa [RecSelfAt] using hself

theorem RecSelfAt.pop_succ {input : VEnv} {index arity : Nat}
    (hself : RecSelfAt input (index + 1) arity) :
    RecSelfAt input.pop index arity := by
  simpa [RecSelfAt, VEnv.pop] using hself

theorem releaseAll_recSelfAt (input : VEnv) (values : List AVal)
    {index arity : Nat} (hself : RecSelfAt input index arity) :
    RecSelfAt (releaseAll input values).1 index arity := by
  exact releaseAll_traverse_core
    (Result := fun initial _ output _ =>
      RecSelfAt initial index arity → RecSelfAt output index arity)
    (hnil := fun _ hinitial => hinitial)
    (hconst := fun htail hinitial => htail hinitial)
    (hslot := fun htail hinitial => htail hinitial.bump)
    input values hself

theorem lowerCapture_recSelfAt (expr : IxIR0.Expr) (input : VEnv)
    (captured : Nat) {output : VEnv} {emit : Emit} {value : AVal}
    {state finalState : LowSt} {index arity : Nat}
    (hrun : (lowerCapture expr input captured).run state =
      .ok (output, emit, value) finalState)
    (hself : RecSelfAt input index arity) :
    RecSelfAt output index arity := by
  cases hentry : input.entries[captured]? with
  | none => exact (throw_run_not_ok (by
      simpa [lowerCapture, hentry] using hrun)).elim
  | some entry =>
    cases entry with
    | recSelf foundArity => exact (throw_run_not_ok (by
        simpa [lowerCapture, hentry] using hrun)).elim
    | slot abs remaining uses held =>
      cases held with
      | false => exact (throw_run_not_ok (by
          simpa [lowerCapture, hentry] using hrun)).elim
      | true =>
        by_cases hunique : worldOfUses uses = .unique
        · have huuEq : (Owned.unique == Owned.unique) = true := by decide
          exact (throw_run_not_ok (by
            simpa [lowerCapture, hentry, hunique, huuEq] using hrun)).elim
        · have huniqueEq :
              (worldOfUses uses == Owned.unique) = false := by
            cases uses <;> simp_all [worldOfUses] <;> decide
          by_cases hmore : remaining > countUses captured expr
          · have houtput : output =
                (input.setEntry captured
                  (.slot abs (remaining - countUses captured expr)
                    uses true)).bump := by
              have hvalue := congrArg
                (fun result : EStateM.Result String LowSt
                    (VEnv × Emit × AVal) =>
                  match result with
                  | .ok value _ => value.1
                  | .error _ _ => input) hrun
              simpa [lowerCapture, hentry, huniqueEq, hmore]
                using hvalue.symm
            subst output
            exact (hself.setSlot hentry abs
              (remaining - countUses captured expr) uses true).bump
          · by_cases hequal : remaining = countUses captured expr
            · have houtput : output =
                  input.setEntry captured (.slot abs 0 uses false) := by
                have hvalue := congrArg
                  (fun result : EStateM.Result String LowSt
                      (VEnv × Emit × AVal) =>
                    match result with
                    | .ok value _ => value.1
                    | .error _ _ => input) hrun
                simpa [lowerCapture, hentry, huniqueEq, hmore, hequal]
                  using hvalue.symm
              subst output
              exact hself.setSlot hentry abs 0 uses false
            · exact (throw_run_not_ok (by
                simpa [lowerCapture, hentry, huniqueEq, hmore, hequal]
                  using hrun)).elim

theorem lowerCaptures_recSelfAt (expr : IxIR0.Expr) :
    ∀ {captures input output emit values state finalState index arity},
      (lowerCaptures expr input captures).run state =
        .ok (output, emit, values) finalState →
      RecSelfAt input index arity → RecSelfAt output index arity := by
  intro captures input output emit values state finalState index arity hrun
  apply lowerCaptures_run_core
    (Result := fun input output _ _ _ =>
      RecSelfAt input index arity → RecSelfAt output index arity)
    (e := expr) (hrun := hrun)
  · intro input hself
    exact hself
  · intro captured rest input middle output headEmit tailEmit headValue
      tailValues state middleState hheadRun htail hself
    exact htail
      (lowerCapture_recSelfAt expr input captured hheadRun hself)

def LowerEPreservesRecSelf (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {world : Owned} {expr : IxIR0.Expr}
      {state finalState : LowSt} {output : VEnv} {emit : Emit} {value : AVal}
      {index arity : Nat},
    (lowerE src fuel input world expr).run state =
      .ok (output, emit, value) finalState →
    RecSelfAt input index arity → RecSelfAt output index arity

def LowerBorrowPreservesRecSelf (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {expr : IxIR0.Expr} {state finalState : LowSt}
      {output : VEnv} {emit : Emit} {value : AVal} {release : Bool}
      {index arity : Nat},
    (lowerBorrow src fuel input expr).run state =
      .ok (output, emit, value, release) finalState →
    RecSelfAt input index arity → RecSelfAt output index arity

def LowerSpinePreservesRecSelf (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {world : Owned} {head : IxIR0.Expr}
      {args : List IxIR0.Expr} {state finalState : LowSt}
      {output : VEnv} {emit : Emit} {value : AVal} {index arity : Nat},
    (lowerSpine src fuel input world head args).run state =
      .ok (output, emit, value) finalState →
    RecSelfAt input index arity → RecSelfAt output index arity

def KnownCallPreservesRecSelf (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {build : Array Atom → Op} {count : Nat}
      {argWorlds : List Owned} {resultWorld : Owned}
      {args : List IxIR0.Expr} {state finalState : LowSt}
      {output : VEnv} {emit : Emit} {value : AVal} {index arity : Nat},
    (knownCall src fuel input build count argWorlds resultWorld args).run
      state = .ok (output, emit, value) finalState →
    RecSelfAt input index arity → RecSelfAt output index arity

def LowerArgsPreservesRecSelf (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {args : List (IxIR0.Expr × Owned)}
      {state finalState : LowSt} {output : VEnv}
      {emit : Emit} {values : List AVal} {index arity : Nat},
    (lowerArgs src fuel input args).run state =
      .ok (output, emit, values) finalState →
    RecSelfAt input index arity → RecSelfAt output index arity

def ApplyRestPreservesRecSelf (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {resultWorld : Owned} {pre : Emit}
      {function : AVal} {args : List IxIR0.Expr}
      {state finalState : LowSt} {output : VEnv}
      {emit : Emit} {value : AVal} {index arity : Nat},
    (applyRest src fuel input resultWorld pre function args).run state =
      .ok (output, emit, value) finalState →
    RecSelfAt input index arity → RecSelfAt output index arity

def LowerLamPreservesRecSelf (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {expr : IxIR0.Expr} {state finalState : LowSt}
      {output : VEnv} {emit : Emit} {value : AVal} {index arity : Nat},
    (lowerLam src fuel input expr).run state =
      .ok (output, emit, value) finalState →
    RecSelfAt input index arity → RecSelfAt output index arity

structure LowerPreservesRecSelf (src : IxIR0.Env) (fuel : Nat) : Prop where
  expr : LowerEPreservesRecSelf src fuel
  borrow : LowerBorrowPreservesRecSelf src fuel
  spine : LowerSpinePreservesRecSelf src fuel
  knownCall : KnownCallPreservesRecSelf src fuel
  args : LowerArgsPreservesRecSelf src fuel
  applyRest : ApplyRestPreservesRecSelf src fuel
  lam : LowerLamPreservesRecSelf src fuel

theorem lowerPreservesRecSelf_zero (src : IxIR0.Env) :
    LowerPreservesRecSelf src 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro input world expr state finalState output emit value index arity
      hrun _
    exact (throw_run_not_ok (by simpa [lowerE] using hrun)).elim
  · intro input expr state finalState output emit value release index arity
      hrun _
    exact (throw_run_not_ok (by simpa [lowerBorrow] using hrun)).elim
  · intro input world head args state finalState output emit value index
      arity hrun _
    exact (throw_run_not_ok (by simpa [lowerSpine] using hrun)).elim
  · intro input build count argWorlds resultWorld args state finalState
      output emit value index arity hrun _
    exact (throw_run_not_ok (by simpa [knownCall] using hrun)).elim
  · intro input args state finalState output emit values index arity hrun _
    exact (throw_run_not_ok (by simpa [lowerArgs] using hrun)).elim
  · intro input resultWorld pre function args state finalState output emit
      value index arity hrun _
    exact (throw_run_not_ok (by simpa [applyRest] using hrun)).elim
  · intro input expr state finalState output emit value index arity hrun _
    exact (throw_run_not_ok (by simpa [lowerLam] using hrun)).elim

theorem lowerArgsPreservesRecSelf_succ {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesRecSelf src fuel)
    (hargs : LowerArgsPreservesRecSelf src fuel) :
    LowerArgsPreservesRecSelf src (fuel + 1) := by
  intro input args state finalState output emit values index arity hrun hself
  cases args with
  | nil =>
    have hpure :
        (input, (_root_.id : Emit), []) = (output, emit, values) ∧
          state = finalState := by
      simpa [lowerArgs] using hrun
    cases hpure.1
    exact hself
  | cons head rest =>
    rcases head with ⟨expr, world⟩
    simp only [lowerArgs] at hrun
    obtain ⟨headResult, middleState, hheadRun, hafterHead⟩ :=
      bind_run_ok_inv hrun
    rcases headResult with ⟨middle, headEmit, headValue⟩
    obtain ⟨tailResult, tailState, htailRun, hafterTail⟩ :=
      bind_run_ok_inv hafterHead
    rcases tailResult with ⟨actualOutput, tailEmit, tailValues⟩
    have houtput : actualOutput = output := by
      have hpure :
          (actualOutput, headEmit ∘ tailEmit, headValue :: tailValues) =
              (output, emit, values) ∧ tailState = finalState := by
        simpa using hafterTail
      exact congrArg Prod.fst hpure.1
    subst output
    exact hargs htailRun (hexpr hheadRun hself)

theorem applyRestPreservesRecSelf_succ {src : IxIR0.Env} {fuel : Nat}
    (hargs : LowerArgsPreservesRecSelf src fuel) :
    ApplyRestPreservesRecSelf src (fuel + 1) := by
  intro input resultWorld pre function args state finalState output emit value
    index arity hrun hself
  cases function with
  | constA atom =>
    cases atom with
    | erased =>
      simp only [applyRest] at hrun
      obtain ⟨argsResult, argsState, hargsRun, hpureRun⟩ :=
        bind_run_ok_inv hrun
      rcases argsResult with ⟨middle, argsEmit, values⟩
      have hpure : (releaseAll middle values).1 = output := by
        have hvalue :
            ((releaseAll middle values).1,
              pre ∘ argsEmit ∘ (releaseAll middle values).2,
              AVal.constA .erased) = (output, emit, value) ∧
              argsState = finalState := by
          simpa using hpureRun
        exact congrArg Prod.fst hvalue.1
      subst output
      exact releaseAll_recSelfAt middle values (hargs hargsRun hself)
    | var relative =>
      simp only [applyRest] at hrun
      obtain ⟨_, checkedState, _, hafterCheck⟩ := bind_run_ok_inv hrun
      obtain ⟨argsResult, argsState, hargsRun, hpureRun⟩ :=
        bind_run_ok_inv hafterCheck
      rcases argsResult with ⟨middle, argsEmit, values⟩
      have houtput : middle.bump = output := by
        have hvalue := congrArg
          (fun result : EStateM.Result String LowSt (VEnv × Emit × AVal) =>
            match result with
            | .ok value _ => value.1
            | .error _ _ => input) hpureRun
        simpa using hvalue
      subst output
      exact (hargs hargsRun hself).bump
    | lit literal =>
      simp only [applyRest] at hrun
      obtain ⟨_, checkedState, _, hafterCheck⟩ := bind_run_ok_inv hrun
      obtain ⟨argsResult, argsState, hargsRun, hpureRun⟩ :=
        bind_run_ok_inv hafterCheck
      rcases argsResult with ⟨middle, argsEmit, values⟩
      have houtput : middle.bump = output := by
        have hvalue := congrArg
          (fun result : EStateM.Result String LowSt (VEnv × Emit × AVal) =>
            match result with
            | .ok value _ => value.1
            | .error _ _ => input) hpureRun
        simpa using hvalue
      subst output
      exact (hargs hargsRun hself).bump
  | slotA abs =>
    simp only [applyRest] at hrun
    obtain ⟨_, checkedState, _, hafterCheck⟩ := bind_run_ok_inv hrun
    obtain ⟨argsResult, argsState, hargsRun, hpureRun⟩ :=
      bind_run_ok_inv hafterCheck
    rcases argsResult with ⟨middle, argsEmit, values⟩
    have houtput : middle.bump = output := by
      have hvalue := congrArg
        (fun result : EStateM.Result String LowSt (VEnv × Emit × AVal) =>
          match result with
          | .ok value _ => value.1
          | .error _ _ => input) hpureRun
      simpa using hvalue
    subst output
    exact (hargs hargsRun hself).bump

theorem knownCallPreservesRecSelf_succ {src : IxIR0.Env} {fuel : Nat}
    (hargs : LowerArgsPreservesRecSelf src fuel)
    (hrest : ApplyRestPreservesRecSelf src fuel) :
    KnownCallPreservesRecSelf src (fuel + 1) := by
  intro input build count argWorlds resultWorld args state finalState output
    emit value index arity hrun hself
  simp only [knownCall] at hrun
  obtain ⟨argsResult, argsState, hargsRun, hafterArgs⟩ :=
    bind_run_ok_inv hrun
  rcases argsResult with ⟨middle, argsEmit, values⟩
  have hmiddle := hargs hargsRun hself
  by_cases hterminal : args.length ≤ count
  · have houtput : middle.bump = output := by
      have hvalue := congrArg
        (fun result : EStateM.Result String LowSt (VEnv × Emit × AVal) =>
          match result with
          | .ok value _ => value.1
          | .error _ _ => input) hafterArgs
      simpa [hterminal] using hvalue
    subst output
    exact hmiddle.bump
  · have hrestRun :
        (applyRest src fuel middle.bump resultWorld
          (argsEmit ∘ emitOp
            (build (values.map (·.toAtom middle)).toArray))
          (.slotA middle.depth) (args.drop count)).run argsState =
            .ok (output, emit, value) finalState := by
      simpa [hterminal] using hafterArgs
    exact hrest hrestRun hmiddle.bump

private theorem lowerBorrow_dynamic_recSelf
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesRecSelf src fuel)
    {input output : VEnv} {expr : IxIR0.Expr}
    {state finalState : LowSt} {emit : Emit} {value : AVal}
    {releaseFlag : Bool} {index arity : Nat}
    {finish : (VEnv × Emit × AVal) → (VEnv × Emit × AVal × Bool)}
    (hrun : (finish <$> lowerE src fuel input .shared expr).run state =
        .ok (output, emit, value, releaseFlag) finalState)
    (hfinish : ∀ result, (finish result).1 = result.1)
    (hself : RecSelfAt input index arity) :
    RecSelfAt output index arity := by
  obtain ⟨exprResult, hexprRun, hvalue⟩ := map_run_ok_inv hrun
  rcases exprResult with ⟨middle, middleEmit, middleValue⟩
  have houtput : middle = output := by
    have := congrArg Prod.fst hvalue
    simpa [hfinish] using this
  subst output
  exact hexpr hexprRun hself

theorem lowerBorrowPreservesRecSelf_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesRecSelf src fuel) :
    LowerBorrowPreservesRecSelf src (fuel + 1) := by
  intro input expr state finalState output emit value release selfIndex
    selfArity hrun hself
  cases expr with
  | var variableIndex =>
    cases hentry : input.entries[variableIndex]? with
    | none => exact (throw_run_not_ok (by
        simpa [lowerBorrow, hentry] using hrun)).elim
    | some entry =>
      cases entry with
      | recSelf arity => exact (throw_run_not_ok (by
          simpa [lowerBorrow, hentry] using hrun)).elim
      | slot abs remaining uses held =>
        cases held with
        | false => exact (throw_run_not_ok (by
            simpa [lowerBorrow, hentry] using hrun)).elim
        | true =>
          by_cases hunique : worldOfUses uses = .unique
          · have huuEq : (Owned.unique == Owned.unique) = true := by decide
            exact (throw_run_not_ok (by
              simpa [lowerBorrow, hentry, hunique, huuEq] using hrun)).elim
          · have huniqueEq :
                (worldOfUses uses == Owned.unique) = false := by
              cases uses <;> simp_all [worldOfUses] <;> decide
            cases remaining with
            | zero => exact (throw_run_not_ok (by
                simpa [lowerBorrow, hentry, huniqueEq] using hrun)).elim
            | succ remaining =>
              cases remaining with
              | zero =>
                have hpure :
                    (input.setEntry variableIndex
                        (.slot abs 0 uses false),
                      (_root_.id : Emit), AVal.slotA abs, true) =
                        (output, emit, value, release) ∧
                      state = finalState := by
                  simpa [lowerBorrow, hentry, huniqueEq] using hrun
                cases hpure.1
                exact hself.setSlot hentry abs 0 uses false
              | succ remaining =>
                have hpure :
                    (input.setEntry variableIndex
                        (.slot abs (remaining + 1) uses true),
                      (_root_.id : Emit), AVal.slotA abs, false) =
                        (output, emit, value, release) ∧
                      state = finalState := by
                  simpa [lowerBorrow, hentry, huniqueEq] using hrun
                cases hpure.1
                exact hself.setSlot hentry abs (remaining + 1) uses true
  | ref address =>
    apply lowerBorrow_dynamic_recSelf hexpr
      (by simpa [lowerBorrow] using hrun) (fun _ => rfl) hself
  | app function argument =>
    apply lowerBorrow_dynamic_recSelf hexpr
      (by simpa [lowerBorrow] using hrun) (fun _ => rfl) hself
  | lam uses body =>
    apply lowerBorrow_dynamic_recSelf hexpr
      (by simpa [lowerBorrow] using hrun) (fun _ => rfl) hself
  | letE uses value body =>
    apply lowerBorrow_dynamic_recSelf hexpr
      (by simpa [lowerBorrow] using hrun) (fun _ => rfl) hself
  | proj index source =>
    apply lowerBorrow_dynamic_recSelf hexpr
      (by simpa [lowerBorrow] using hrun) (fun _ => rfl) hself
  | lit literal =>
    apply lowerBorrow_dynamic_recSelf hexpr
      (by simpa [lowerBorrow] using hrun) (fun _ => rfl) hself
  | erased =>
    apply lowerBorrow_dynamic_recSelf hexpr
      (by simpa [lowerBorrow] using hrun) (fun _ => rfl) hself

private theorem lowerE_applyRest_recSelf
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesRecSelf src fuel)
    (hrest : ApplyRestPreservesRecSelf src fuel)
    {input output : VEnv} {world : Owned} {head : IxIR0.Expr}
    {args : List IxIR0.Expr} {state finalState : LowSt}
    {emit : Emit} {value : AVal} {index arity : Nat}
    (hrun : (do
      let (middle, headEmit, function) ←
        lowerE src fuel input .shared head
      applyRest src fuel middle world headEmit function args).run state =
        .ok (output, emit, value) finalState)
    (hself : RecSelfAt input index arity) :
    RecSelfAt output index arity := by
  obtain ⟨headResult, middleState, hheadRun, hrestRun⟩ :=
    bind_run_ok_inv hrun
  rcases headResult with ⟨middle, headEmit, function⟩
  exact hrest hrestRun (hexpr hheadRun hself)

theorem lowerSpinePreservesRecSelf_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesRecSelf src fuel)
    (hspine : LowerSpinePreservesRecSelf src fuel)
    (hknown : KnownCallPreservesRecSelf src fuel)
    (hrest : ApplyRestPreservesRecSelf src fuel) :
    LowerSpinePreservesRecSelf src (fuel + 1) := by
  intro input world head args state finalState output emit value selfIndex
    selfArity hrun hself
  have hsuEq : (Owned.shared == Owned.unique) = false := by decide
  cases head with
  | app function argument =>
    apply hspine
    · simpa [lowerSpine] using hrun
    · exact hself
  | erased =>
    apply hrest
    · simpa [lowerSpine] using hrun
    · exact hself
  | var variableIndex =>
    simp only [lowerSpine] at hrun
    cases hentry : input.entries[variableIndex]? with
    | none =>
      apply lowerE_applyRest_recSelf hexpr hrest
      · simpa [hentry] using hrun
      · exact hself
    | some entry =>
      cases entry with
      | recSelf arity =>
        rw [hentry] at hrun
        simp only at hrun
        by_cases hunder : args.length < arity
        · rw [if_pos hunder] at hrun
          exact (throw_run_not_ok hrun).elim
        · rw [if_neg hunder] at hrun
          obtain ⟨unitValue, checkedState, _, hknownRun⟩ :=
            bind_run_ok_inv hrun
          cases unitValue
          exact hknown hknownRun hself
      | slot abs remaining uses held =>
        apply lowerE_applyRest_recSelf hexpr hrest
        · simpa [hentry] using hrun
        · exact hself
  | ref address =>
    simp only [lowerSpine] at hrun
    cases hsource : src address with
    | none =>
      rw [hsource] at hrun
      exact (throw_run_not_ok hrun).elim
    | some decl =>
      rw [hsource] at hrun
      cases decl with
      | defn result body =>
        simp only at hrun
        by_cases hunder : args.length < lamArity body
        · rw [if_pos hunder] at hrun
          cases world with
          | unique => exact (throw_run_not_ok hrun).elim
          | shared =>
            cases result with
            | unique => exact (throw_run_not_ok hrun).elim
            | shared =>
              cases hp : papSafe body with
              | false => exact (throw_run_not_ok (by
                  simpa [hp, hsuEq] using hrun)).elim
              | true =>
                apply hknown
                · simpa [hp, hsuEq] using hrun
                · exact hself
        · rw [if_neg hunder] at hrun
          obtain ⟨_, checkedState, _, hknownRun⟩ := bind_run_ok_inv hrun
          exact hknown hknownRun hself
      | ctor tag arity =>
        simp only at hrun
        by_cases hunder : args.length < arity
        · rw [if_pos hunder] at hrun
          cases world with
          | unique => exact (throw_run_not_ok hrun).elim
          | shared =>
            obtain ⟨wrapper, wrapperState, _, hknownRun⟩ :=
              bind_run_ok_inv hrun
            exact hknown hknownRun hself
        · rw [if_neg hunder] at hrun
          exact hknown hrun hself
      | recursor numArgs natLit rules =>
        simp only at hrun
        by_cases hunder : args.length < numArgs + 1
        · rw [if_pos hunder] at hrun
          cases world with
          | unique => exact (throw_run_not_ok hrun).elim
          | shared => exact hknown hrun hself
        · rw [if_neg hunder] at hrun
          obtain ⟨_, checkedState, _, hknownRun⟩ := bind_run_ok_inv hrun
          exact hknown hknownRun hself
      | extern arity =>
        simp only at hrun
        by_cases hunder : args.length < arity
        · rw [if_pos hunder] at hrun
          cases world with
          | unique => exact (throw_run_not_ok hrun).elim
          | shared => exact hknown hrun hself
        · rw [if_neg hunder] at hrun
          exact hknown hrun hself
  | lam uses body =>
    apply lowerE_applyRest_recSelf hexpr hrest
    · simpa [lowerSpine] using hrun
    · exact hself
  | letE uses bound body =>
    apply lowerE_applyRest_recSelf hexpr hrest
    · simpa [lowerSpine] using hrun
    · exact hself
  | proj index source =>
    apply lowerE_applyRest_recSelf hexpr hrest
    · simpa [lowerSpine] using hrun
    · exact hself
  | lit literal =>
    apply lowerE_applyRest_recSelf hexpr hrest
    · simpa [lowerSpine] using hrun
    · exact hself

theorem lowerLamPreservesRecSelf_succ
    {src : IxIR0.Env} {fuel : Nat} :
    LowerLamPreservesRecSelf src (fuel + 1) := by
  intro input expr state finalState output emit value index arity hrun hself
  cases hp : papSafe expr with
  | false => simp [lowerLam, hp] at hrun
  | true =>
    simp only [lowerLam] at hrun
    simp only [hp, ↓reduceIte, bind_pure_comp] at hrun
    let captures := (List.range input.entries.length).filter
      (fun index => countUses index expr > 0)
    have hcaptures : captures = (List.range input.entries.length).filter
        (fun index => countUses index expr > 0) := rfl
    rw [← hcaptures] at hrun
    obtain ⟨captureResult, captureState, hcaptureRun, hafterCapture⟩ :=
      bind_run_ok_inv hrun
    rcases captureResult with ⟨captureOutput, captureEmit, captureValues⟩
    obtain ⟨fnAddr, addressState, _, hafterFresh⟩ :=
      bind_run_ok_inv hafterCapture
    obtain ⟨code, bodyState, _, hafterBody⟩ :=
      bind_run_ok_inv hafterFresh
    obtain ⟨_, _, hvalue⟩ := map_run_ok_inv hafterBody
    have houtput : captureOutput.bump = output :=
      congrArg Prod.fst hvalue
    subst output
    exact (lowerCaptures_recSelfAt expr hcaptureRun hself).bump

private theorem lowerE_proj_recSelf
    {src : IxIR0.Env} {fuel : Nat}
    (hborrow : LowerBorrowPreservesRecSelf src fuel)
    {input output : VEnv} {world : Owned} {fieldIndex : Nat}
    {source : IxIR0.Expr} {state finalState : LowSt}
    {emit : Emit} {value : AVal} {index arity : Nat}
    (hrun : (lowerE src (fuel + 1) input world
      (.proj fieldIndex source)).run state =
        .ok (output, emit, value) finalState)
    (hself : RecSelfAt input index arity) :
    RecSelfAt output index arity := by
  cases world with
  | unique =>
    have huuEq : (Owned.unique == Owned.unique) = true := by decide
    simp [lowerE, huuEq] at hrun
  | shared =>
    have hsuEq : (Owned.shared == Owned.unique) = false := by decide
    simp only [lowerE, hsuEq, Bool.false_eq_true, if_false] at hrun
    obtain ⟨borrowResult, middleState, hborrowRun, hafterBorrow⟩ :=
      bind_run_ok_inv hrun
    rcases borrowResult with
      ⟨borrowOutput, borrowEmit, borrowed, release⟩
    have hborrowSelf := hborrow hborrowRun hself
    cases borrowed with
    | constA atom =>
      cases atom with
      | var relative =>
        have hpure : borrowOutput.bump = output := by
          have hvalue := congrArg
            (fun result : EStateM.Result String LowSt
                (VEnv × Emit × AVal) =>
              match result with
              | .ok value _ => value.1
              | .error _ _ => input) hafterBorrow
          simpa using hvalue
        subst output
        exact hborrowSelf.bump
      | lit literal =>
        have hpure : borrowOutput.bump = output := by
          have hvalue := congrArg
            (fun result : EStateM.Result String LowSt
                (VEnv × Emit × AVal) =>
              match result with
              | .ok value _ => value.1
              | .error _ _ => input) hafterBorrow
          simpa using hvalue
        subst output
        exact hborrowSelf.bump
      | erased =>
        have hpure : borrowOutput = output := by
          have hvalue := congrArg
            (fun result : EStateM.Result String LowSt
                (VEnv × Emit × AVal) =>
              match result with
              | .ok value _ => value.1
              | .error _ _ => input) hafterBorrow
          simpa using hvalue
        subst output
        exact hborrowSelf
    | slotA targetAbs =>
      cases release with
      | false =>
        have hpure : borrowOutput.bump.bump = output := by
          have hvalue := congrArg
            (fun result : EStateM.Result String LowSt
                (VEnv × Emit × AVal) =>
              match result with
              | .ok value _ => value.1
              | .error _ _ => input) hafterBorrow
          simpa using hvalue
        subst output
        exact hborrowSelf.bump.bump
      | true =>
        have hpure : borrowOutput.bump.bump.bump = output := by
          have hvalue := congrArg
            (fun result : EStateM.Result String LowSt
                (VEnv × Emit × AVal) =>
              match result with
              | .ok value _ => value.1
              | .error _ _ => input) hafterBorrow
          simpa using hvalue
        subst output
        exact hborrowSelf.bump.bump.bump

private theorem lowerE_mapped_body_pop_recSelf
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesRecSelf src fuel)
    {middle bodyInput output : VEnv} {world : Owned} {body : IxIR0.Expr}
    {state finalState : LowSt} {emit : Emit} {value : AVal}
    {finish : (VEnv × Emit × AVal) → (VEnv × Emit × AVal)}
    {binder : VEntry} {index arity : Nat}
    (hrun : (finish <$> lowerE src fuel bodyInput world body).run state =
      .ok (output, emit, value) finalState)
    (hfinish : ∀ result, (finish result).1 = result.1.pop)
    (hentries : bodyInput.entries = binder :: middle.entries)
    (hself : RecSelfAt middle index arity) :
    RecSelfAt output index arity := by
  obtain ⟨bodyResult, hbodyRun, hvalue⟩ := map_run_ok_inv hrun
  rcases bodyResult with ⟨bodyOutput, bodyEmit, bodyValue⟩
  have houtput : bodyOutput.pop = output := by
    have := congrArg Prod.fst hvalue
    simpa [hfinish] using this
  subst output
  have hbodyInput : RecSelfAt bodyInput (index + 1) arity := by
    rw [RecSelfAt, hentries]
    simpa [RecSelfAt] using hself
  exact (hexpr hbodyRun hbodyInput).pop_succ

private theorem lowerE_let_recSelf
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesRecSelf src fuel)
    {input output : VEnv} {world : Owned} {binderUses : Uses}
    {bound body : IxIR0.Expr} {state finalState : LowSt}
    {emit : Emit} {value : AVal} {index arity : Nat}
    (hrun : (lowerE src (fuel + 1) input world
      (.letE binderUses bound body)).run state =
        .ok (output, emit, value) finalState)
    (hself : RecSelfAt input index arity) :
    RecSelfAt output index arity := by
  simp only [lowerE] at hrun
  obtain ⟨boundResult, boundState, hboundRun, hafterBound⟩ :=
    bind_run_ok_inv hrun
  rcases boundResult with ⟨middle, boundEmit, boundValue⟩
  have hmiddle := hexpr hboundRun hself
  cases boundValue with
  | slotA boundAbs =>
    by_cases hzero : countUses 0 body = 0
    · cases binderUses with
      | erased =>
        obtain ⟨_, _, hthrow, _⟩ := bind_run_ok_inv
          (by simpa [hzero] using hafterBound)
        exact (throw_run_not_ok hthrow).elim
      | linear =>
        obtain ⟨_, _, hthrow, _⟩ := bind_run_ok_inv
          (by simpa [hzero] using hafterBound)
        exact (throw_run_not_ok hthrow).elim
      | affine =>
        let bodyInput : VEnv :=
          { middle with
            entries := .slot boundAbs 0 .affine false :: middle.entries
            depth := middle.depth + 1 }
        apply lowerE_mapped_body_pop_recSelf hexpr
          (middle := middle) (bodyInput := bodyInput)
          (by simpa [hzero, bodyInput] using hafterBound)
          (fun _ => rfl) (by rfl) hmiddle
      | many =>
        let bodyInput : VEnv :=
          { middle with
            entries := .slot boundAbs 0 .many false :: middle.entries
            depth := middle.depth + 1 }
        apply lowerE_mapped_body_pop_recSelf hexpr
          (middle := middle) (bodyInput := bodyInput)
          (by simpa [hzero, bodyInput] using hafterBound)
          (fun _ => rfl) (by rfl) hmiddle
    · let bodyInput : VEnv :=
        { middle with
          entries :=
            .slot boundAbs (countUses 0 body) binderUses true ::
              middle.entries }
      apply lowerE_mapped_body_pop_recSelf hexpr
        (middle := middle) (bodyInput := bodyInput)
        (by simpa [hzero, bodyInput] using hafterBound)
        (fun _ => rfl) (by rfl) hmiddle
  | constA atom =>
    by_cases hzero : countUses 0 body = 0
    · let bodyInput : VEnv :=
        { middle with
          entries := .slot middle.depth 0 binderUses false ::
            middle.entries
          depth := middle.depth + 1 }
      apply lowerE_mapped_body_pop_recSelf hexpr
        (middle := middle) (bodyInput := bodyInput)
        (by simpa [hzero, bodyInput] using hafterBound)
        (fun _ => rfl) (by rfl) hmiddle
    · let bodyInput : VEnv :=
        { middle with
          entries :=
            .slot middle.depth (countUses 0 body) binderUses true ::
              middle.entries
          depth := middle.depth + 1 }
      apply lowerE_mapped_body_pop_recSelf hexpr
        (middle := middle) (bodyInput := bodyInput)
        (by simpa [hzero, bodyInput] using hafterBound)
        (fun _ => rfl) (by rfl) hmiddle

private theorem lowerE_var_recSelf
    {src : IxIR0.Env} {fuel : Nat} {input output : VEnv}
    {world : Owned} {variableIndex : Nat} {state finalState : LowSt}
    {emit : Emit} {value : AVal} {selfIndex selfArity : Nat}
    (hrun : (lowerE src (fuel + 1) input world
      (.var variableIndex)).run state =
        .ok (output, emit, value) finalState)
    (hself : RecSelfAt input selfIndex selfArity) :
    RecSelfAt output selfIndex selfArity := by
  have hssNe : (Owned.shared != Owned.shared) = false := by decide
  have huuNe : (Owned.unique != Owned.unique) = false := by decide
  have hsuNe : (Owned.shared != Owned.unique) = true := by decide
  have husNe : (Owned.unique != Owned.shared) = true := by decide
  have hsuEq : (Owned.shared == Owned.unique) = false := by decide
  have huuEq : (Owned.unique == Owned.unique) = true := by decide
  cases hentry : input.entries[variableIndex]? with
  | none => exact (throw_run_not_ok (by
      simpa [lowerE, hentry] using hrun)).elim
  | some entry =>
    cases entry with
    | recSelf arity => exact (throw_run_not_ok (by
        simpa [lowerE, hentry] using hrun)).elim
    | slot abs remaining uses held =>
      cases held with
      | false => exact (throw_run_not_ok (by
          simpa [lowerE, hentry] using hrun)).elim
      | true =>
        by_cases hworld : worldOfUses uses = world
        · subst world
          have hsame :
              (worldOfUses uses != worldOfUses uses) = false := by
            cases uses <;> decide
          cases remaining with
          | zero => exact (throw_run_not_ok (by
              simpa [lowerE, hentry, hsame] using hrun)).elim
          | succ remaining =>
            cases remaining with
            | zero =>
              have hpure :
                  (input.setEntry variableIndex (.slot abs 0 uses false),
                    (_root_.id : Emit), AVal.slotA abs) =
                      (output, emit, value) ∧ state = finalState := by
                simpa [lowerE, hentry, hsame] using hrun
              cases hpure.1
              exact hself.setSlot hentry abs 0 uses false
            | succ remaining =>
              by_cases hunique : worldOfUses uses = .unique
              · have huniqueEq :
                    (worldOfUses uses == Owned.unique) = true := by
                  rw [hunique]
                  exact huuEq
                exact (throw_run_not_ok (by
                  simpa [lowerE, hentry, hsame, huniqueEq, huuNe]
                    using hrun)).elim
              · have huniqueEq :
                    (worldOfUses uses == Owned.unique) = false := by
                  cases uses <;> simp_all [worldOfUses] <;> decide
                let changed := input.setEntry variableIndex
                  (.slot abs (remaining + 1) uses true)
                have hpure :
                    (changed.bump,
                      emitOp (.dup (.var (changed.rel abs))),
                      AVal.slotA changed.depth) =
                        (output, emit, value) ∧ state = finalState := by
                  simpa [lowerE, hentry, hsame, huniqueEq, hssNe, changed]
                    using hrun
                cases hpure.1
                exact (hself.setSlot hentry abs
                  (remaining + 1) uses true).bump
        · cases uses <;> cases world
          all_goals
            try { exact (hworld (by rfl)).elim }
          all_goals
            exact (throw_run_not_ok (by
              simpa [lowerE, hentry, worldOfUses, hssNe, huuNe, hsuNe,
                husNe, hsuEq, huuEq] using hrun)).elim

theorem lowerEPreservesRecSelf_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesRecSelf src fuel)
    (hborrow : LowerBorrowPreservesRecSelf src fuel)
    (hspine : LowerSpinePreservesRecSelf src fuel)
    (hlam : LowerLamPreservesRecSelf src fuel) :
    LowerEPreservesRecSelf src (fuel + 1) := by
  intro input world expr state finalState output emit value index arity hrun
    hself
  cases expr with
  | var variableIndex => exact lowerE_var_recSelf hrun hself
  | ref address =>
    exact hself.of_entries_eq (lowerE_ref_entries_eq_noRecSelf hrun)
  | app function argument =>
    apply hspine
    · simpa [lowerE] using hrun
    · exact hself
  | lam uses body =>
    cases world with
    | unique =>
      have huuEq : (Owned.unique == Owned.unique) = true := by decide
      exact (throw_run_not_ok (by
        simpa [lowerE, huuEq] using hrun)).elim
    | shared =>
      have hsuEq : (Owned.shared == Owned.unique) = false := by decide
      apply hlam
      · simpa [lowerE, hsuEq] using hrun
      · exact hself
  | letE uses bound body => exact lowerE_let_recSelf hexpr hrun hself
  | proj fieldIndex source => exact lowerE_proj_recSelf hborrow hrun hself
  | lit literal =>
    have hpure :
        (input, (_root_.id : Emit), AVal.constA (.lit literal)) =
            (output, emit, value) ∧ state = finalState := by
      simpa [lowerE] using hrun
    cases hpure.1
    exact hself
  | erased =>
    have hpure :
        (input, (_root_.id : Emit), AVal.constA .erased) =
            (output, emit, value) ∧ state = finalState := by
      simpa [lowerE] using hrun
    cases hpure.1
    exact hself

theorem lowerPreservesRecSelf_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hprev : LowerPreservesRecSelf src fuel) :
    LowerPreservesRecSelf src (fuel + 1) where
  expr := lowerEPreservesRecSelf_succ
    hprev.expr hprev.borrow hprev.spine hprev.lam
  borrow := lowerBorrowPreservesRecSelf_succ hprev.expr
  spine := lowerSpinePreservesRecSelf_succ
    hprev.expr hprev.spine hprev.knownCall hprev.applyRest
  knownCall := knownCallPreservesRecSelf_succ hprev.args hprev.applyRest
  args := lowerArgsPreservesRecSelf_succ hprev.expr hprev.args
  applyRest := applyRestPreservesRecSelf_succ hprev.args
  lam := lowerLamPreservesRecSelf_succ

/-- Successful expression lowering preserves every synthetic recursive-self
entry at its original logical index. -/
theorem lowerPreservesRecSelf (src : IxIR0.Env) :
    ∀ fuel, LowerPreservesRecSelf src fuel
  | 0 => lowerPreservesRecSelf_zero src
  | fuel + 1 =>
    lowerPreservesRecSelf_succ (lowerPreservesRecSelf src fuel)

theorem lowerE_recSelfAt
    {src : IxIR0.Env} {fuel : Nat} {input output : VEnv}
    {world : Owned} {expr : IxIR0.Expr}
    {state finalState : LowSt} {emit : Emit} {value : AVal}
    {index arity : Nat}
    (hrun : (lowerE src fuel input world expr).run state =
      .ok (output, emit, value) finalState)
    (hself : RecSelfAt input index arity) :
    RecSelfAt output index arity :=
  (lowerPreservesRecSelf src fuel).expr hrun hself

end Ix.Compiler.IxIR1.Lower
