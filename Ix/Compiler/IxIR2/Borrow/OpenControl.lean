import Ix.Compiler.IxIR2.Borrow.OpenHeap

namespace Ix.Compiler.IxIR2.Borrow.Open

open Eval

/-- A scalar-returning entry may halt or resume its immediate caller. The
caller's remaining continuation stack is arbitrary and is preserved. -/
inductive Exit where
  | halt
  | resume (caller : Frame) (rest : List Continuation)

def Exit.stack : Exit → List Continuation
  | .halt => []
  | .resume caller rest => .resume caller :: rest

def Exit.result (exit : Exit) (value : RVal) : Control :=
  match exit with
  | .halt => .halted value
  | .resume caller rest => .running { caller with values := caller.values.push value } rest

def start (definition : Function) (location : Nat) (store : Store) (fuel : Nat) (exit : Exit) : Machine :=
  { store, heapFuel := fuel, control := .running { definition, values := #[.loc location] } exit.stack }

def finish (store : Store) (fuel number : Nat) (exit : Exit) : Machine :=
  { store, heapFuel := fuel, control := exit.result (.lit (.nat number)) }

/-- Every intermediate state preserves the lender's complete heap, not just
the final state. This composes under arbitrary suspended callers. -/
inductive StableSteps (context : Context) (mode : Interpretation) : Nat → Machine → Machine → Prop where
  | refl (machine : Machine) : StableSteps context mode 0 machine machine
  | cons {count : Nat} {before middle after : Machine} {frame : Frame} {stack : List Continuation}
      (running : before.control = .running frame stack)
      (step : Step context mode before middle) (unchanged : middle.store = before.store)
      (tail : StableSteps context mode count middle after) :
      StableSteps context mode (count + 1) before after

theorem StableSteps.steps {context mode count before after}
    (trace : StableSteps context mode count before after) : Steps context mode count before after := by
  induction trace with
  | refl machine => exact .refl machine
  | cons running step _ _ ih => exact .cons running step ih

theorem StableSteps.one {context mode before after frame stack}
    (step : Step context mode before after) (running : before.control = .running frame stack)
    (unchanged : after.store = before.store) : StableSteps context mode 1 before after :=
  .cons running step unchanged (.refl after)

theorem StableSteps.trans {context mode firstCount secondCount before middle after}
    (first : StableSteps context mode firstCount before middle)
    (second : StableSteps context mode secondCount middle after) :
    StableSteps context mode (firstCount + secondCount) before after := by
  induction first with
  | refl => simpa using second
  | cons running step unchanged _ ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StableSteps.cons running step unchanged (ih second)

theorem StableSteps.prefix {context mode count before after}
    (trace : StableSteps context mode count before after) {prefixCount middle}
    (initial : Steps context mode prefixCount before middle) (bound : prefixCount ≤ count) :
    middle.store = before.store := by
  induction trace generalizing prefixCount middle with
  | refl =>
      have zero : prefixCount = 0 := by omega
      subst prefixCount
      cases initial
      rfl
  | @cons count before next after frame stack running step unchanged tail ih =>
      cases initial with
      | refl => rfl
      | cons _ head rest =>
          have eq := step.deterministic head
          subst_vars
          exact (ih rest (by omega)).trans unchanged

theorem returnScalar {context : Context} {mode : Interpretation} {frame : Frame} {current : Block}
    (store : Store) (fuel number : Nat) (exit : Exit) (atom : Atom)
    (blockAt : frame.definition.blocks[frame.block]? = some current)
    (pc : frame.pc = current.instructions.size)
    (term : current.terminator = .ret atom)
    (resolved : resolveAtom frame.values atom = .ok (.lit (.nat number)))
    (credits : frame.credits = #[]) :
    StableSteps context mode 1
      { store, heapFuel := fuel, control := .running frame exit.stack }
      (finish store fuel number exit) := by
  cases exit with
  | halt =>
      exact StableSteps.one
        (Step.retHalt rfl blockAt pc term resolved credits rfl) rfl rfl
  | resume caller rest =>
      exact StableSteps.one
        (Step.retResume rfl blockAt pc term resolved credits rfl) rfl rfl

def readerFrame (schema : Schema) (borrowed : Bool) (major : Major) (location : Nat) : Frame :=
  { definition := reader schema borrowed
    block := match major with | .zero => 1 | .succ _ => 2
    pc := major.fieldCost
    values := #[.loc location] ++ major.fields }

theorem readerPrefix (context : Context) (mode : Interpretation) (schema : Schema) (borrowed : Bool)
    (distinct : schema.zero ≠ schema.succ) (major : Major)
    {store : Store} {location rc : Nat} (view : major.At schema store location rc)
    (fuel : Nat) (exit : Exit) :
    StableSteps context mode (1 + major.fieldCost)
      (start (reader schema borrowed) location store fuel exit)
      { store, heapFuel := fuel, control := .running (readerFrame schema borrowed major location) exit.stack } := by
  cases major with
  | zero =>
      have step : Step context mode (start (reader schema borrowed) location store fuel exit)
          { store, heapFuel := fuel
            control := .running (readerFrame schema borrowed .zero location) exit.stack } :=
        Step.switchCtor (alternative := {
          cid := schema.zero
          edge := { target := 1, values := #[.reg 0], credits := #[] } })
          rfl rfl rfl rfl rfl view rfl (by simp [Major.cid]) (by
            exact EdgeTransfer.baseline (values := #[.loc location]) rfl rfl rfl rfl rfl rfl)
      exact StableSteps.one step rfl rfl
  | succ field =>
      let middle : Machine := {
        store, heapFuel := fuel
        control := .running { definition := reader schema borrowed, block := 2, values := #[.loc location] } exit.stack }
      have switch : Step context mode (start (reader schema borrowed) location store fuel exit) middle :=
        Step.switchCtor (alternative := {
          cid := schema.succ
          edge := { target := 2, values := #[.reg 0], credits := #[] } })
          rfl rfl rfl rfl rfl view rfl (by simp [Major.cid, distinct]) (by
            exact EdgeTransfer.baseline (values := #[.loc location]) rfl rfl rfl rfl rfl rfl)
      have fetch : Step context mode middle {
          store, heapFuel := fuel
          control := .running (readerFrame schema borrowed (.succ field) location) exit.stack } :=
        Step.fetch (machine := middle) (atom := .reg 0) (cid := schema.succ)
          (field := 0) (value := field) rfl rfl
          (by simp [reader, block, release]; omega) (by cases borrowed <;> rfl) rfl view rfl rfl
      exact (StableSteps.one switch rfl rfl).trans (StableSteps.one fetch rfl rfl)

theorem readerBorrowed (context : Context) (mode : Interpretation) (schema : Schema)
    (distinct : schema.zero ≠ schema.succ) (major : Major)
    {store : Store} {location rc : Nat} (view : major.At schema store location rc)
    (fuel : Nat) (exit : Exit) :
    StableSteps context mode (2 + major.fieldCost)
      (start (reader schema true) location store fuel exit)
      (finish store fuel (major.result schema) exit) := by
  have headPath := readerPrefix context mode schema true distinct major view fuel exit
  have ret : StableSteps context mode 1
      { store, heapFuel := fuel, control := .running (readerFrame schema true major location) exit.stack }
      (finish store fuel (major.result schema) exit) := by
    cases major with
    | zero => exact returnScalar store fuel schema.zeroResult exit _ rfl rfl rfl rfl rfl
    | succ field => exact returnScalar store fuel schema.succResult exit _ rfl rfl rfl rfl rfl
  have count : 1 + major.fieldCost + 1 = 2 + major.fieldCost := by omega
  simpa only [count] using headPath.trans ret

theorem readerOwned (context : Context) (mode : Interpretation) (schema : Schema)
    (distinct : schema.zero ≠ schema.succ) (major : Major)
    {store output : Store} {location rc fuel remaining : Nat}
    (view : major.At schema store location rc)
    (released : releaseShared fuel store (.loc location) = .ok (output, remaining)) (exit : Exit) :
    Steps context mode (3 + major.fieldCost)
      (start (reader schema false) location store fuel exit)
      (finish output remaining (major.result schema) exit) := by
  have headPath := readerPrefix context mode schema false distinct major view fuel exit
  let afterRelease : Frame := { readerFrame schema false major location with pc := major.fieldCost + 1 }
  have drop : Step context mode
      { store, heapFuel := fuel, control := .running (readerFrame schema false major location) exit.stack }
      { store := output, heapFuel := remaining, control := .running afterRelease exit.stack } := by
    cases major with
    | zero => exact Step.releaseShared rfl rfl (by simp [readerFrame, reader, block, release, Major.fieldCost]) rfl rfl released
    | succ field => exact Step.releaseShared rfl rfl (by simp [readerFrame, reader, block, release, Major.fieldCost]) rfl rfl released
  have ret : StableSteps context mode 1
      { store := output, heapFuel := remaining, control := .running afterRelease exit.stack }
      (finish output remaining (major.result schema) exit) := by
    cases major with
    | zero => exact returnScalar output remaining schema.zeroResult exit _ rfl rfl rfl rfl rfl
    | succ field => exact returnScalar output remaining schema.succResult exit _ rfl rfl rfl rfl rfl
  have count : 1 + major.fieldCost + 1 + 1 = 3 + major.fieldCost := by omega
  simpa only [count] using
    (headPath.steps.trans (drop.toSteps rfl)).trans ret.steps

end Ix.Compiler.IxIR2.Borrow.Open
