import Ix.Compiler.IxIR2.Borrow.OpenControl

namespace Ix.Compiler.IxIR2.Borrow.Open

open Eval
open Ix.Compiler.Ixon (Address)

theorem Chain.borrowedSteps {context : Context} {schema : Schema} {definition : Function}
    (chain : Chain context schema true definition) (mode : Interpretation)
    (distinct : schema.zero ≠ schema.succ) (major : Major)
    {store : Store} {location rc : Nat} (view : major.At schema store location rc)
    (fuel : Nat) (exit : Exit) :
    StableSteps context mode (chain.depth + 2 + major.fieldCost)
      (start definition location store fuel exit) (finish store fuel (major.result schema) exit) := by
  induction chain with
  | reader => exact readerBorrowed context mode schema distinct major view fuel exit
  | forward address callee found tail ih =>
      have step : Step context mode (start (Open.forward true address) location store fuel exit)
          (start callee location store fuel exit) :=
        Step.tailCallFn rfl rfl rfl rfl rfl rfl found
          (by rw [tail.signature]; rfl) tail.nonempty
      have count : 1 + (tail.depth + 2 + major.fieldCost) = tail.depth + 1 + 2 + major.fieldCost := by omega
      simpa only [Chain.depth, count] using (StableSteps.one step rfl rfl).trans ih

theorem Chain.ownedSteps {context : Context} {schema : Schema} {definition : Function}
    (chain : Chain context schema false definition) (mode : Interpretation)
    (distinct : schema.zero ≠ schema.succ) (major : Major)
    {store output : Store} {location rc fuel remaining : Nat}
    (view : major.At schema store location rc)
    (released : releaseShared fuel store (.loc location) = .ok (output, remaining)) (exit : Exit) :
    Steps context mode (chain.depth + 3 + major.fieldCost)
      (start definition location store fuel exit) (finish output remaining (major.result schema) exit) := by
  induction chain with
  | reader => exact readerOwned context mode schema distinct major view released exit
  | forward address callee found tail ih =>
      have step : Step context mode (start (Open.forward false address) location store fuel exit)
          (start callee location store fuel exit) :=
        Step.tailCallFn rfl rfl rfl rfl rfl rfl found
          (by rw [tail.signature]; rfl) tail.nonempty
      have count : 1 + (tail.depth + 3 + major.fieldCost) = tail.depth + 1 + 3 + major.fieldCost := by omega
      simpa only [Chain.depth, count] using (step.toSteps rfl).trans ih

def twiceSaved (borrowed : Bool) (address : Address) (location : Nat) : Frame :=
  { definition := twice borrowed address, pc := 2, values := #[.loc location, .loc location] }

def twiceResumed (borrowed : Bool) (address : Address) (location number : Nat) : Frame :=
  { twiceSaved borrowed address location with values := #[.loc location, .loc location, .lit (.nat number)] }

theorem twiceBorrowed {context : Context} {schema : Schema} {address : Address} {callee : Function}
    (found : context.declarations address = some (.fn callee))
    (chain : Chain context schema true callee) (mode : Interpretation)
    (distinct : schema.zero ≠ schema.succ) (major : Major)
    {store : Store} {location rc : Nat} (view : major.At schema store location rc)
    (fuel : Nat) (exit : Exit) :
    StableSteps context mode (2 * chain.depth + 8 + 2 * major.fieldCost)
      (start (twice true address) location store (fuel + 1) exit)
      (finish store fuel (major.result schema) exit) := by
  let moved : Machine := {
    store, heapFuel := fuel + 1
    control := .running { definition := twice true address, pc := 1, values := #[.loc location, .loc location] } exit.stack }
  let saved := twiceSaved true address location
  let resumed := twiceResumed true address location (major.result schema)
  let next : Machine := {
    store, heapFuel := fuel
    control := .running { resumed with pc := 3 } exit.stack }
  have move : Step context mode (start (twice true address) location store (fuel + 1) exit) moved :=
    Step.move (machine := start (twice true address) location store (fuel + 1) exit)
      (atom := .reg 0) (value := .loc location) rfl rfl (by change 0 < 3; omega) rfl rfl
  have call : Step context mode moved (start callee location store (fuel + 1) (.resume saved exit.stack)) :=
    Step.callFn (machine := moved) (arguments := #[.reg 1]) (values := #[.loc location])
      rfl rfl (by change 1 < 3; omega) rfl rfl rfl found
      (by rw [chain.signature]; rfl) chain.nonempty
  have first := chain.borrowedSteps mode distinct major view (fuel + 1) (.resume saved exit.stack)
  have discard : Step context mode (finish store (fuel + 1) (major.result schema) (.resume saved exit.stack)) next :=
    Step.releaseShared rfl rfl (by change 2 < 3; omega) rfl rfl
      (by simp [releaseShared, releaseSharedWork, finish, resumed, twiceResumed])
  have tailCall : Step context mode next (start callee location store fuel exit) :=
    Step.tailCallFn rfl rfl rfl rfl rfl rfl found
      (by rw [chain.signature]; rfl) chain.nonempty
  have second := chain.borrowedSteps mode distinct major view fuel exit
  have path := (((((StableSteps.one move rfl rfl).trans (StableSteps.one call rfl rfl)).trans first).trans
    (StableSteps.one discard rfl rfl)).trans (StableSteps.one tailCall rfl rfl)).trans second
  have count : 1 + 1 + (chain.depth + 2 + major.fieldCost) + 1 + 1 +
      (chain.depth + 2 + major.fieldCost) = 2 * chain.depth + 8 + 2 * major.fieldCost := by omega
  simpa only [count] using path

theorem twiceOwned {context : Context} {schema : Schema} {address : Address} {callee : Function}
    (found : context.declarations address = some (.fn callee))
    (chain : Chain context schema false callee) (mode : Interpretation)
    (distinct : schema.zero ≠ schema.succ) (major : Major)
    {store output : Store} {location rc fuel remaining : Nat}
    (view : major.At schema store location rc) (positive : 0 < rc)
    (released : releaseShared fuel store (.loc location) = .ok (output, remaining)) (exit : Exit) :
    Steps context mode (2 * chain.depth + 10 + 2 * major.fieldCost)
      (start (twice false address) location store (fuel + 2) exit)
      (finish (bump output 2) remaining (major.result schema) exit) := by
  let box : NodeBox := ⟨.shared, rc, .ctorN (major.cid schema) major.fields⟩
  let held := retained store location box
  let moved : Machine := {
    store := held, heapFuel := fuel + 2
    control := .running { definition := twice false address, pc := 1, values := #[.loc location, .loc location] } exit.stack }
  let saved := twiceSaved false address location
  let resumed := twiceResumed false address location (major.result schema)
  let next : Machine := {
    store := bump store 2, heapFuel := fuel
    control := .running { resumed with pc := 3 } exit.stack }
  have retain : Step context mode (start (twice false address) location store (fuel + 2) exit) moved :=
    Step.retainShared (machine := start (twice false address) location store (fuel + 2) exit)
      (atom := .reg 0) (value := .loc location) rfl rfl (by change 0 < 3; omega) rfl rfl (retain_eq view rfl)
  have call : Step context mode moved (start callee location held (fuel + 2) (.resume saved exit.stack)) :=
    Step.callFn (machine := moved) (arguments := #[.reg 1]) (values := #[.loc location])
      rfl rfl (by change 1 < 3; omega) rfl rfl rfl found
      (by rw [chain.signature]; rfl) chain.nonempty
  have first := chain.ownedSteps mode distinct major view.retained
    (retain_release_cancel view rfl positive (fuel + 1)) (.resume saved exit.stack)
  have discard : Step context mode (finish (bump store 2) (fuel + 1) (major.result schema) (.resume saved exit.stack)) next :=
    Step.releaseShared rfl rfl (by change 2 < 3; omega) rfl rfl
      (by simp [releaseShared, releaseSharedWork, finish, resumed, twiceResumed])
  have tailCall : Step context mode next (start callee location (bump store 2) fuel exit) :=
    Step.tailCallFn rfl rfl rfl rfl rfl rfl found
      (by rw [chain.signature]; rfl) chain.nonempty
  have second := chain.ownedSteps mode distinct major (view.bump 2) (release_bump released 2) exit
  have path := (((((retain.toSteps rfl).trans (call.toSteps rfl)).trans first).trans
    (discard.toSteps rfl)).trans (tailCall.toSteps rfl)).trans second
  have count : 1 + 1 + (chain.depth + 3 + major.fieldCost) + 1 + 1 +
      (chain.depth + 3 + major.fieldCost) = 2 * chain.depth + 10 + 2 * major.fieldCost := by omega
  simpa only [count] using path

/-- One exact owned wrapper brackets the borrowed execution with a live
lender, performs the ordinary final release, and resumes the caller. -/
theorem wrapper {context : Context} {schema : Schema} {borrowed : Address} {callee baseline : Function}
    (found : context.declarations borrowed = some (.fn callee))
    (arity : callee.signature.params.size = 1) (nonempty : callee.blocks.isEmpty = false)
    (mode : Interpretation) (major : Major) {store output : Store} {location fuel remaining work count : Nat}
    (released : releaseShared fuel store (.loc location) = .ok (output, remaining))
    (exit : Exit)
    (run : ∀ caller rest,
      StableSteps context mode count
        (start callee location store (fuel + work) (.resume caller rest))
        (finish store fuel (major.result schema) (.resume caller rest))) :
    Steps context mode (count + 3)
      (start (ownedWrapper borrowed baseline) location store (fuel + work) exit)
      (finish output remaining (major.result schema) exit) := by
  let saved : Frame := { definition := ownedWrapper borrowed baseline, pc := 1, values := #[.loc location] }
  let resumed : Frame := { saved with values := #[.loc location, .lit (.nat (major.result schema))] }
  let next : Machine := {
    store := output, heapFuel := remaining
    control := .running { resumed with pc := 2 } exit.stack }
  have call : Step context mode
      (start (ownedWrapper borrowed baseline) location store (fuel + work) exit)
      (start callee location store (fuel + work) (.resume saved exit.stack)) :=
    Step.callFn (machine := start (ownedWrapper borrowed baseline) location store (fuel + work) exit)
      (values := #[.loc location]) rfl rfl (by change 0 < 2; omega) rfl rfl rfl found
      (by simpa using arity.symm) nonempty
  have drop : Step context mode (finish store fuel (major.result schema) (.resume saved exit.stack)) next :=
    Step.releaseShared rfl rfl (by change 1 < 2; omega) rfl rfl released
  have ret : StableSteps context mode 1 next (finish output remaining (major.result schema) exit) :=
    returnScalar output remaining (major.result schema) exit _ rfl rfl rfl rfl rfl
  have path := (((call.toSteps rfl).trans (run saved exit.stack).steps).trans (drop.toSteps rfl)).trans ret.steps
  have counts : 1 + count + 1 + 1 = count + 3 := by omega
  simpa only [counts] using path

theorem Body.borrowedSteps {context : Context} {schema : Schema} {definition : Function}
    (body : Body context schema true definition) (mode : Interpretation)
    (distinct : schema.zero ≠ schema.succ) (major : Major)
    {store : Store} {location rc : Nat} (view : major.At schema store location rc)
    (fuel : Nat) (exit : Exit) :
    StableSteps context mode (body.readCost major.fieldCost)
      (start definition location store (fuel + body.readWork) exit)
      (finish store fuel (major.result schema) exit) := by
  cases body with
  | chain chain => exact chain.borrowedSteps mode distinct major view fuel exit
  | twice address callee found chain => exact twiceBorrowed found chain mode distinct major view fuel exit

theorem Body.ownedSteps {context : Context} {schema : Schema} {definition : Function}
    (body : Body context schema false definition) (mode : Interpretation)
    (distinct : schema.zero ≠ schema.succ) (major : Major)
    {store output : Store} {location rc fuel remaining : Nat}
    (view : major.At schema store location rc) (positive : 0 < rc)
    (released : releaseShared fuel store (.loc location) = .ok (output, remaining)) (exit : Exit) :
    Steps context mode (body.ownedCost major.fieldCost)
      (start definition location store (fuel + 2 * body.readWork) exit)
      (finish (bump output (2 * body.readWork)) remaining (major.result schema) exit) := by
  cases body with
  | chain chain => exact chain.ownedSteps mode distinct major view released exit
  | twice address callee found chain => exact twiceOwned found chain mode distinct major view positive released exit

end Ix.Compiler.IxIR2.Borrow.Open
