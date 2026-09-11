import Compilatrix.IxIR2.SpaceLayout

/-!
# Execution with finite heap and explicit control storage

The checker validates the initial state and every successor before continuing.
Exhaustion reports the first disallowed state's demand and remaining control
fuel. The interpreter is pure: a rejected transition commits no external
memory writes. Profiling computes a certificate for one actual execution,
including its representation checks and both independent maximum demands.
-/

namespace Compilatrix.IxIR2.Eval.Space

inductive Fault where
  | evaluation (error : Error)
  | representation
  | capacity (needed available : Demand) (controlRemaining : Nat)
  deriving BEq, Repr

structure Profile where
  result : Result
  demand : Demand
  deriving Repr

def allowed (capacity : Option Capacity) (demand : Demand) : Bool :=
  capacity.all demand.within

def execute (layout : Layout) (capacity : Option Capacity) (policy : CreditPolicy)
    (context : Context) : Nat → Machine → Except Fault Profile
  | fuel, machine => do
      if !layout.machineFits machine then .error .representation
      let needed := layout.demand machine
      if let some available := capacity then
        if !needed.within available then .error (.capacity needed available fuel)
      match fuel, machine.control with
      | _, .halted value =>
          return ⟨⟨machine.store, value, fuel, machine.heapFuel⟩, needed⟩
      | 0, .running .. => .error (.evaluation .controlFuel)
      | fuel + 1, .running .. =>
          let next ← (Policy.step policy context .physical machine).mapError Fault.evaluation
          let tail ← execute layout capacity policy context fuel next
          return { tail with demand := needed.join tail.demand }

def profile (layout : Layout) (policy : CreditPolicy) (context : Context)
    (fuel : Nat) (machine : Machine) : Except Fault Profile :=
  execute layout none policy context fuel machine

def run (layout : Layout) (capacity : Capacity) (policy : CreditPolicy) (context : Context)
    (fuel : Nat) (machine : Machine) : Except Fault Profile :=
  execute layout (some capacity) policy context fuel machine

private theorem execute_unfold (layout : Layout) (capacity : Option Capacity)
    (policy : CreditPolicy) (context : Context) (fuel : Nat) (machine : Machine) :
    execute layout capacity policy context fuel machine =
      if layout.machineFits machine = false then .error .representation
      else if allowed capacity (layout.demand machine) = false then
        match capacity with
        | none => .error .representation
        | some available => .error (.capacity (layout.demand machine) available fuel)
      else match fuel, machine.control with
      | _, .halted value => .ok ⟨⟨machine.store, value, fuel, machine.heapFuel⟩, layout.demand machine⟩
      | 0, .running .. => .error (.evaluation .controlFuel)
      | fuel + 1, .running .. => do
          let next ← (Policy.step policy context .physical machine).mapError Fault.evaluation
          let tail ← execute layout capacity policy context fuel next
          return { tail with demand := (layout.demand machine).join tail.demand } := by
  rw [execute]
  cases fit : layout.machineFits machine <;> cases capacity with
  | none => simp [allowed, bind, Except.bind, pure, Except.pure]
  | some available =>
      cases enough : (layout.demand machine).within available <;>
        simp [enough, allowed, bind, Except.bind, pure, Except.pure]

theorem execute_erases {layout : Layout} {capacity : Option Capacity} {policy : CreditPolicy}
    {context : Context} {fuel : Nat} {machine : Machine} {observed : Profile}
    (ran : execute layout capacity policy context fuel machine = .ok observed) :
    Policy.runMachine policy context .physical fuel machine = .ok observed.result := by
  induction fuel generalizing machine observed with
  | zero =>
      rw [execute_unfold] at ran
      split at ran <;> try cases ran
      split at ran
      · cases capacity <;> cases ran
      · cases machine with
        | mk store heapFuel control =>
            cases control <;> simp only at ran
            · cases ran
            · cases ran; rfl
  | succ fuel ih =>
      rw [execute_unfold] at ran
      split at ran <;> try cases ran
      split at ran
      · cases capacity <;> cases ran
      · cases machine with
        | mk store heapFuel control =>
            cases control with
            | halted value => cases ran; rfl
            | running frame stack =>
                cases stepAt : Policy.step policy context .physical
                    ⟨store, heapFuel, .running frame stack⟩ with
                | error error => simp [stepAt, Except.mapError, bind, Except.bind] at ran
                | ok next =>
                    cases tailAt : execute layout capacity policy context fuel next with
                    | error error => simp [stepAt, tailAt, Except.mapError, bind, Except.bind] at ran
                    | ok tail =>
                        simp only [stepAt, tailAt, Except.mapError, bind, Except.bind,
                          pure, Except.pure, Except.ok.injEq] at ran
                        subst observed
                        simpa only [Policy.runMachine, stepAt, bind, Except.bind] using ih tailAt

theorem execute_within {layout : Layout} {capacity : Capacity} {policy : CreditPolicy}
    {context : Context} {fuel : Nat} {machine : Machine} {observed : Profile}
    (ran : execute layout (some capacity) policy context fuel machine = .ok observed) :
    observed.demand.within capacity = true := by
  induction fuel generalizing machine observed with
  | zero =>
      rw [execute_unfold] at ran
      split at ran <;> try cases ran
      simp only [allowed, Option.all_some] at ran
      cases enough : (layout.demand machine).within capacity <;> simp only [enough,
        Bool.true_eq_false, ↓reduceIte] at ran
      · cases ran
      · cases machine with
        | mk store heapFuel control =>
            cases control with
            | running frame stack => cases ran
            | halted value => cases ran; exact enough
  | succ fuel ih =>
      rw [execute_unfold] at ran
      split at ran <;> try cases ran
      simp only [allowed, Option.all_some] at ran
      cases enough : (layout.demand machine).within capacity <;> simp only [enough,
        Bool.true_eq_false, ↓reduceIte] at ran
      · cases ran
      · cases machine with
        | mk store heapFuel control =>
            cases control with
            | halted value => cases ran; exact enough
            | running frame stack =>
                cases stepAt : Policy.step policy context .physical
                    ⟨store, heapFuel, .running frame stack⟩ with
                | error error => simp [stepAt, Except.mapError, bind, Except.bind] at ran
                | ok next =>
                    cases tailAt : execute layout (some capacity) policy context fuel next with
                    | error error => simp [stepAt, tailAt, Except.mapError, bind, Except.bind] at ran
                    | ok tail =>
                        simp only [stepAt, tailAt, Except.mapError, bind, Except.bind,
                          pure, Except.pure, Except.ok.injEq] at ran
                        subst observed
                        exact Demand.join_within _ _ _ |>.mpr ⟨enough, ih tailAt⟩

theorem profile_sufficient {layout : Layout} {capacity : Capacity} {policy : CreditPolicy}
    {context : Context} {fuel : Nat} {machine : Machine} {observed : Profile}
    (profiled : profile layout policy context fuel machine = .ok observed)
    (sufficient : observed.demand.within capacity = true) :
    run layout capacity policy context fuel machine = .ok observed := by
  unfold profile at profiled
  unfold run
  induction fuel generalizing machine observed with
  | zero =>
      rw [execute_unfold] at profiled ⊢
      cases fit : layout.machineFits machine <;> simp only [fit,
        Bool.true_eq_false, ↓reduceIte, allowed, Option.all_none, Option.all_some] at profiled ⊢
      · cases profiled
      · cases machine with
        | mk store heapFuel control =>
            cases control with
            | running frame stack => cases profiled
            | halted value =>
                cases profiled
                simp [sufficient]
  | succ fuel ih =>
      rw [execute_unfold] at profiled ⊢
      cases fit : layout.machineFits machine <;> simp only [fit,
        Bool.true_eq_false, ↓reduceIte, allowed, Option.all_none, Option.all_some] at profiled ⊢
      · cases profiled
      · cases machine with
        | mk store heapFuel control =>
            cases control with
            | halted value =>
                cases profiled
                simp [sufficient]
            | running frame stack =>
                cases stepAt : Policy.step policy context .physical
                    ⟨store, heapFuel, .running frame stack⟩ with
                | error error => simp [stepAt, Except.mapError, bind, Except.bind] at profiled
                | ok next =>
                    cases tailAt : execute layout none policy context fuel next with
                    | error error => simp [stepAt, tailAt, Except.mapError, bind, Except.bind] at profiled
                    | ok tail =>
                        simp only [stepAt, tailAt, Except.mapError, bind, Except.bind,
                          pure, Except.pure, Except.ok.injEq] at profiled
                        subst observed
                        obtain ⟨headEnough, tailEnough⟩ := Demand.join_within _ _ _ |>.mp sufficient
                        simp [headEnough, Except.mapError, ih tailAt tailEnough,
                          bind, Except.bind, pure, Except.pure]

/-- A successful profile is sufficient and necessary for the same finite
execution. No caller-supplied bound over individual steps is required. -/
theorem capacity_iff {layout : Layout} {capacity : Capacity} {policy : CreditPolicy}
    {context : Context} {fuel : Nat} {machine : Machine} {observed : Profile}
    (profiled : profile layout policy context fuel machine = .ok observed) :
    run layout capacity policy context fuel machine = .ok observed ↔
      observed.demand.within capacity = true :=
  ⟨execute_within, profile_sufficient profiled⟩

/-- If the profiled computation is representable and terminates, a bounded
attempt either reproduces it or reports a capacity failure at the first
disallowed state. It cannot manufacture an evaluator or representation error. -/
theorem profile_capacity_cases {layout : Layout} {capacity : Capacity} {policy : CreditPolicy}
    {context : Context} {fuel : Nat} {machine : Machine} {observed : Profile}
    (profiled : profile layout policy context fuel machine = .ok observed) :
    run layout capacity policy context fuel machine = .ok observed ∨
      ∃ needed remaining, run layout capacity policy context fuel machine =
        .error (.capacity needed capacity remaining) ∧ needed.within capacity = false := by
  unfold profile at profiled
  unfold run
  induction fuel generalizing machine observed with
  | zero =>
      rw [execute_unfold] at profiled ⊢
      cases fit : layout.machineFits machine <;> simp only [fit,
        Bool.true_eq_false, ↓reduceIte, allowed, Option.all_none, Option.all_some] at profiled ⊢
      · cases profiled
      · by_cases short : (layout.demand machine).within capacity = false
        · exact Or.inr ⟨_, 0, by simp [short], short⟩
        · have enough : (layout.demand machine).within capacity = true := by simpa using short
          cases machine with
          | mk store heapFuel control =>
              cases control with
              | running frame stack => cases profiled
              | halted value => cases profiled; exact Or.inl (by simp [enough])
  | succ fuel ih =>
      rw [execute_unfold] at profiled ⊢
      cases fit : layout.machineFits machine <;> simp only [fit,
        Bool.true_eq_false, ↓reduceIte, allowed, Option.all_none, Option.all_some] at profiled ⊢
      · cases profiled
      · by_cases short : (layout.demand machine).within capacity = false
        · exact Or.inr ⟨_, fuel + 1, by simp [short], short⟩
        · have enough : (layout.demand machine).within capacity = true := by simpa using short
          cases machine with
          | mk store heapFuel control =>
              cases control with
              | halted value => cases profiled; exact Or.inl (by simp [enough])
              | running frame stack =>
                  cases stepAt : Policy.step policy context .physical
                      ⟨store, heapFuel, .running frame stack⟩ with
                  | error error => simp [stepAt, Except.mapError, bind, Except.bind] at profiled
                  | ok next =>
                      cases tailAt : execute layout none policy context fuel next with
                      | error error => simp [stepAt, tailAt, Except.mapError, bind, Except.bind] at profiled
                      | ok tail =>
                          simp only [stepAt, tailAt, Except.mapError, bind, Except.bind,
                            pure, Except.pure, Except.ok.injEq] at profiled
                          subst observed
                          rcases ih tailAt with success | ⟨needed, remaining, failed, short⟩
                          · exact Or.inl (by simp [enough, Except.mapError, success,
                              bind, Except.bind, pure, Except.pure])
                          · exact Or.inr ⟨needed, remaining, by simp [enough,
                              Except.mapError, failed, bind, Except.bind], short⟩

theorem capacity_exhausted {layout : Layout} {capacity : Capacity} {policy : CreditPolicy}
    {context : Context} {fuel : Nat} {machine : Machine} {observed : Profile}
    (profiled : profile layout policy context fuel machine = .ok observed)
    (insufficient : observed.demand.within capacity = false) :
    ∃ needed remaining, run layout capacity policy context fuel machine =
      .error (.capacity needed capacity remaining) ∧ needed.within capacity = false := by
  rcases profile_capacity_cases (capacity := capacity) profiled with success | exhausted
  · have := execute_within success
    rw [insufficient] at this
    contradiction
  · exact exhausted

private theorem execute_head {layout : Layout} {capacity : Option Capacity} {policy : CreditPolicy}
    {context : Context} {fuel : Nat} {machine : Machine} {observed : Profile}
    (ran : execute layout capacity policy context fuel machine = .ok observed) :
    layout.machineFits machine = true ∧ allowed capacity (layout.demand machine) = true := by
  rw [execute_unfold] at ran
  by_cases bad : layout.machineFits machine = false
  · simp [bad] at ran
  · refine ⟨by simpa using bad, ?_⟩
    simp only [bad] at ran
    by_cases short : allowed capacity (layout.demand machine) = false
    · rw [if_pos short] at ran
      cases capacity <;> cases ran
    · simpa using short

private theorem execute_next {layout : Layout} {capacity : Option Capacity} {policy : CreditPolicy}
    {context : Context} {fuel : Nat} {machine : Machine} {observed : Profile}
    {frame : Frame} {stack : List Continuation}
    (running : machine.control = .running frame stack)
    (ran : execute layout capacity policy context fuel machine = .ok observed) :
    ∃ remaining next tail, fuel = remaining + 1 ∧
      Policy.step policy context .physical machine = .ok next ∧
      execute layout capacity policy context remaining next = .ok tail := by
  obtain ⟨fit, enough⟩ := execute_head ran
  rw [execute_unfold] at ran
  simp only [fit, enough, Bool.true_eq_false, ↓reduceIte, running] at ran
  cases fuel with
  | zero => cases ran
  | succ fuel =>
      cases stepAt : Policy.step policy context .physical machine with
      | error error => simp [stepAt, Except.mapError, bind, Except.bind] at ran
      | ok next =>
          cases tailAt : execute layout capacity policy context fuel next with
          | error error => simp [stepAt, tailAt, Except.mapError, bind, Except.bind] at ran
          | ok tail => exact ⟨fuel, next, tail, rfl, rfl, tailAt⟩

/-- Every actual prefix of a successful finite run is representable and
fits both budgets, including all suspended callers. -/
theorem run_prefix_within {layout : Layout} {capacity : Capacity} {policy : CreditPolicy}
    {context : Context} {fuel count : Nat} {initial middle : Machine} {observed : Profile}
    (ran : run layout capacity policy context fuel initial = .ok observed)
    (steps : Policy.Steps policy context .physical count initial middle) :
    layout.machineFits middle = true ∧ (layout.demand middle).within capacity = true := by
  unfold run at ran
  induction steps generalizing fuel observed with
  | refl => exact execute_head ran
  | @cons count before next after frame stack running head tail ih =>
      obtain ⟨remaining, other, result, _, stepped, continued⟩ := execute_next running ran
      have same := head.deterministic stepped
      subst other
      exact ih continued

/-- The maximum heap requirement is the terminal backing arena size, even
when many cells were released during calls. Control storage has its own peak. -/
theorem execute_heap_exact {layout : Layout} {capacity : Option Capacity} {policy : CreditPolicy}
    {context : Context} {fuel : Nat} {machine : Machine} {observed : Profile}
    (ran : execute layout capacity policy context fuel machine = .ok observed) :
    observed.demand.heap = layout.committedBytes observed.result.store := by
  induction fuel generalizing machine observed with
  | zero =>
      obtain ⟨fit, enough⟩ := execute_head ran
      rw [execute_unfold] at ran
      simp only [fit, enough, Bool.true_eq_false, ↓reduceIte] at ran
      cases machine with
      | mk store heapFuel control =>
          cases control with
          | running frame stack => cases ran
          | halted value => cases ran; rfl
  | succ fuel ih =>
      have headBound := layout.prefix_capacity (execute_erases ran) (.refl machine)
      obtain ⟨fit, enough⟩ := execute_head ran
      rw [execute_unfold] at ran
      simp only [fit, enough, Bool.true_eq_false, ↓reduceIte] at ran
      cases machine with
      | mk store heapFuel control =>
          cases control with
          | halted value => cases ran; rfl
          | running frame stack =>
              cases stepAt : Policy.step policy context .physical
                  ⟨store, heapFuel, .running frame stack⟩ with
              | error error => simp [stepAt, Except.mapError, bind, Except.bind] at ran
              | ok next =>
                  cases tailAt : execute layout capacity policy context fuel next with
                  | error error => simp [stepAt, tailAt, Except.mapError, bind, Except.bind] at ran
                  | ok tail =>
                      simp only [stepAt, tailAt, Except.mapError, bind, Except.bind,
                        pure, Except.pure, Except.ok.injEq] at ran
                      subst observed
                      change max (layout.committedBytes store) tail.demand.heap = _
                      rw [ih tailAt]
                      exact Nat.max_eq_right headBound

end Compilatrix.IxIR2.Eval.Space
