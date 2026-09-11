import Ix.Compiler.IxIR2.Borrow.OpenResources
import Ix.Compiler.IxIR2.Borrow.Examples

/-! Structural and lifetime neighbors for the open-input certificate. The
positive source/measurement boundary is supplied by Borrow.Runtime. -/

namespace Ix.Compiler.IxIR2.Borrow.Open.Examples

open Ix.Compiler.Ixon (Address)

def schema : Schema := { zero := Borrow.Examples.leaf, succ := Borrow.Examples.box, zeroResult := 11, succResult := 22 }
def readerAddress : Address := .replicate 1
def workerAddress : Address := .replicate 2
def factoryAddress : Address := .replicate 3
def cycleAddress : Address := .replicate 4
def callerAddress : Address := .replicate 5
def readerBorrowed : Address := .replicate 11
def workerBorrowed : Address := .replicate 12
def cycleBorrowed : Address := .replicate 14
def validation : Validate.Context := Borrow.Examples.context

def baseline : Program :=
  { declarations := [(readerAddress, .fn (reader schema false)),
      (workerAddress, .fn (twice false readerAddress)), (factoryAddress, .fn (factory workerAddress))]
    main := moduleMain factoryAddress }

def claims : List Summary :=
  [{ owner := readerAddress, borrowed := readerBorrowed }, { owner := workerAddress, borrowed := workerBorrowed }]

def accepted : Bool := (certify {} validation baseline claims).isOk

def cycle : Program :=
  { baseline with declarations := baseline.declarations ++ [(cycleAddress, .fn (forward false cycleAddress))] }

def cycleClaims : List Summary := claims ++ [{ owner := cycleAddress, borrowed := cycleBorrowed }]

def cycleRejected : Bool :=
  (Borrow.check {} validation cycle cycleClaims).isOk &&
    match certify {} validation cycle cycleClaims with
    | .error .body => true
    | _ => false

/-- Baseline release before allocation is safe. Borrowing delays that final
release across the allocation, so B2 must reject it without sampling a heap. -/
def allocatingReader : Function :=
  { reader schema false with
    blocks := (reader schema false).blocks.set! 1
      (block false #[.releaseShared (.reg 0), .alloc .shared schema.zero #[], .releaseShared (.reg 1)]
        (.ret (.lit (.nat 11)))) }

def allocation : Program :=
  { baseline with declarations := baseline.declarations.map fun (address, declaration) =>
      (address, if address == readerAddress then .fn allocatingReader else declaration) }

def allocationRejected : Bool :=
  (Borrow.check {} validation allocation claims).isOk &&
    match certify {} validation allocation claims with
    | .error .schema => true
    | _ => false

def callbackFreeFallback : Bool :=
  match certify {} validation baseline claims { maxDepth := 0 } with
  | .error .body => true
  | _ => false

def incompleteRejected : Bool := !(certify {} validation baseline
  [{ owner := workerAddress, borrowed := workerBorrowed }]).isOk

/-- A caller can borrow, regain its unchanged lender, then reset and discard
the slot. The caller itself is deliberately not rewritten to a borrowed ABI. -/
def resettingCaller : Function :=
  { signature := signature false
    blocks := #[block false #[.call workerBorrowed #[.reg 0], .resetShared (.reg 0) schema.zero, .discardCredit 0]
      (.ret (.reg 1))] }

def lenderThenReset : Bool :=
  match certify {} validation baseline claims with
  | .error _ => false
  | .ok result =>
      let program := { result.rewrite.program with
        declarations := result.rewrite.program.declarations ++ [(callerAddress, .fn resettingCaller)] }
      let allocated := ({} : Eval.Store).allocNode .shared (.ctorN schema.zero #[])
      (Validate.validate validation program).isOk &&
        match Eval.runFunction (context validation program) .physical resettingCaller #[.loc allocated.2] 100 100 allocated.1 with
        | .error _ => false
        | .ok output => output.value == .lit (.nat 11) && output.store.live == 0 &&
            output.store.heap.allocs == output.store.heap.frees && output.store.hotResets == 1

def localTailRejected : Bool := Borrow.Examples.accepted Borrow.Examples.localTailLender && Borrow.Examples.rejected Borrow.Examples.localTailLender
def laterResetRejected : Bool := Borrow.Examples.accepted Borrow.Examples.laterReset && Borrow.Examples.rejected Borrow.Examples.laterReset

def guards : Array (String × Bool) := #[
  ("structural-open-certificate", accepted),
  ("cyclic-summary-rejected", cycleRejected),
  ("allocation-peak-hazard-rejected", allocationRejected),
  ("structural-budget-fallback", callbackFreeFallback),
  ("incomplete-summary-rejected", incompleteRejected),
  ("borrow-then-reset", lenderThenReset),
  ("local-tail-lender-rejected", localTailRejected),
  ("later-reset-keeps-owned-parameter", laterResetRejected)]

#guard guards.all (·.2)

end Ix.Compiler.IxIR2.Borrow.Open.Examples
