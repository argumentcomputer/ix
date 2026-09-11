import Ix.Compiler.IxIR2.Borrow.Replay

/-! Negative ownership and peak-space neighbors for the borrowed ABI.
These hand-built programs test the optimizer boundary; the source gate
separately derives its positive witnesses through the Ixon compiler. -/

namespace Ix.Compiler.IxIR2.Borrow.Examples

open Ix.Compiler.Ixon (Address)

def readerAddress : Address := .replicate 1
def workerAddress : Address := .replicate 2
def captureAddress : Address := .replicate 3
def readerBorrowed : Address := .replicate 11
def workerBorrowed : Address := .replicate 12
def leaf : CtorId := { block := .replicate 20, indIdx := 0, cidx := 0 }
def box : CtorId := { block := .replicate 20, indIdx := 0, cidx := 1 }
def layout : Address := .replicate 21

def context : Validate.Context :=
  { schemas := fun world cid =>
      if world == .shared && (cid == leaf || cid == box) then
        some { layout, fields := if cid == leaf then #[] else #[.shared] }
      else none }

def unary : Signature :=
  { params := #[{ world := .shared, passing := .owned }], result := .shared, papSafe := true }

def fn (instructions : Array Instr) (terminator : Terminator) : Function :=
  { signature := unary
    blocks := #[{ valueParams := #[.owned .shared], creditParams := #[]
                  instructions, terminator }] }

def reader : Function := fn #[.releaseShared (.reg 0)] (.ret (.lit (.nat 0)))

def main (instructions : Array Instr := #[]) (terminator : Terminator := .ret (.lit (.nat 0))) :
    Function :=
  { signature := { params := #[], result := .shared, papSafe := false }
    blocks := #[{ valueParams := #[], creditParams := #[], instructions, terminator }] }

def program (worker : Function) : Program :=
  { declarations := [(readerAddress, .fn reader), (workerAddress, .fn worker)]
    main := main }

def claims : List Summary :=
  [{ owner := readerAddress, borrowed := readerBorrowed },
   { owner := workerAddress, borrowed := workerBorrowed }]

def accepted (program : Program) : Bool := (Validate.validate context program).isOk
def rejected (program : Program) : Bool := !(check {} context program claims).isOk

def returnEscape : Program := program (fn #[] (.ret (.reg 0)))
def storeEscape : Program := program (fn #[.alloc .shared box #[.reg 0]] (.ret (.reg 1)))

def capture : Function :=
  { signature := { unary with params := unary.params ++ unary.params }
    blocks := #[{
      valueParams := #[.owned .shared, .owned .shared], creditParams := #[]
      instructions := #[.releaseShared (.reg 0), .releaseShared (.reg 1)]
      terminator := .ret (.lit (.nat 0)) }] }

def captureEscape : Program :=
  { program (fn #[.papp captureAddress #[.reg 0]] (.ret (.reg 1))) with
    declarations := (program (fn #[.papp captureAddress #[.reg 0]] (.ret (.reg 1)))).declarations ++
      [(captureAddress, .fn capture)] }

def localTailLender : Program := program (fn
  #[.releaseShared (.reg 0), .alloc .shared leaf #[]]
  (.tailCall readerAddress #[.reg 1]))

def laterReset : Program := program (fn
  #[.retainShared (.reg 0), .call readerAddress #[.reg 1], .releaseShared (.reg 2),
    .resetShared (.reg 0) leaf, .discardCredit 0]
  (.ret (.lit (.nat 0))))

/-- Delaying an early release can increase peak space even if the ownership
validator accepts and two real RC operations disappear. Replay rejects it. -/
def peakRegression : Program :=
  { program (fn
      #[.retainShared (.reg 0), .call readerAddress #[.reg 1], .releaseShared (.reg 2),
        .releaseShared (.reg 0), .alloc .shared leaf #[], .releaseShared (.reg 3)]
      (.ret (.lit (.nat 0)))) with
    main := main #[.alloc .shared leaf #[]] (.tailCall workerAddress #[.reg 0]) }

def peakRejected : Bool :=
  match check {} context peakRegression claims with
  | .error _ => false
  | .ok rewritten =>
      match replay context {} rewritten with
      | .error .peakIncrease => true
      | _ => false

def noGainRejected : Bool :=
  match check {} context peakRegression [] with
  | .error _ => false
  | .ok rewritten =>
      match replay context {} rewritten with
      | .error .noImprovement => true
      | _ => false

def budgetRejected : Bool :=
  match check {} context peakRegression claims with
  | .error _ => false
  | .ok rewritten =>
      match replay context { control := 0 } rewritten with
      | .error (.execution .controlFuel) => true
      | _ => false

def collisionRejected : Bool :=
  match check {} context (program reader)
      [{ owner := readerAddress, borrowed := workerAddress }] with
  | .error (.validation (.duplicateDeclaration _)) => true
  | _ => false

/-- Retaining a projected field creates an independent owned result. That
retain must survive even when the containing parameter is borrowed. -/
def fieldRetainPreserved : Bool :=
  let source := program (fn
    #[.fetch (.reg 0) box 0, .retainShared (.reg 1), .releaseShared (.reg 0)]
    (.ret (.reg 2)))
  accepted source && match check {} context source claims with
  | .error _ => false
  | .ok result =>
      match result.program.declarations.find? (fun entry => entry.1 == workerBorrowed) with
      | some (_, .fn definition) =>
          definition.blocks[0]?.map (·.instructions) ==
            some #[.fetch (.reg 0) box 0, .retainShared (.reg 1)]
      | _ => false

#guard fieldRetainPreserved

def guards : List (String × Bool) :=
  [("return-escape", accepted returnEscape && rejected returnEscape),
   ("store-escape", accepted storeEscape && rejected storeEscape),
   ("capture-escape", accepted captureEscape && rejected captureEscape),
   ("local-tail-lender", accepted localTailLender && rejected localTailLender),
   ("later-reset", accepted laterReset && rejected laterReset),
   ("peak-regression", accepted peakRegression && peakRejected),
   ("no-rc-gain", noGainRejected),
   ("replay-budget", budgetRejected),
   ("internal-label-collision", collisionRejected),
   ("duplicate-summary", !(check {} context (program reader) (claims ++ claims)).isOk),
   ("missing-summary-owner", !(check {} context (program reader)
     [{ owner := .replicate 99, borrowed := readerBorrowed }]).isOk),
   ("candidate-limit", !(check { maxCandidates := 0 } context (program reader) claims).isOk)]

#guard guards.all (·.2)

end Ix.Compiler.IxIR2.Borrow.Examples
