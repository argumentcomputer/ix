import IxCC.Aiur.OracleEval.Op

/-! A bounded local machine with explicit shared-continuation frames.
Return exits the function; yield restores the closest continuation's saved
register namespace and appends only its declared outputs. -/

namespace IxCC.Aiur.OracleEval

open _root_.IxCC.Vendor.Aiur (G)
open _root_.IxCC.Vendor.Aiur.Bytecode (Op Ctrl Block Toplevel)

structure Continuation where
  savedValues : Array G
  outputSize : Nat
  block : Block

inductive Task where
  | ops (operations : List Op) (control : Ctrl)
  | control (control : Ctrl)

def start (block : Block) : Task := .ops block.ops.toList block.ctrl

/-- First matching case, including when labels are repeated. -/
def selectBranch (scrutinee : G) (cases : Array (G × Block)) (fallback : Option Block) :
    Except Error Block :=
  match cases.toList.find? (fun arm => arm.1 == scrutinee) with
  | some (_, block) => .ok block
  | none => match fallback with
      | some block => .ok block
      | none => .error .noMatch

def finish (outcome : Outcome) (state : State) : Except Error Result :=
  if state.replies.isEmpty then
    .ok ⟨outcome, state.demandsRev.reverse, state.adviceRev.reverse⟩
  else .error .unusedReplies

inductive Progress where
  | done (result : Result)
  | more (task : Task) (continuations : List Continuation) (state : State)

def step (toplevel : Toplevel) (maxValues : Nat) (task : Task)
    (continuations : List Continuation) (state : State) : Except Error Progress :=
  match task with
  | .ops [] control => .ok (.more (.control control) continuations state)
  | .ops (op :: rest) control => do
      let state ← evalOp toplevel maxValues op state
      pure (.more (.ops rest control) continuations state)
  | .control control =>
      match control with
      | .return selector indices => do
          let outputs ← readMany maxValues state indices
          pure (.done (← finish (.returned selector outputs) state))
      | .yield selector indices => do
          let outputs ← readMany maxValues state indices
          match continuations with
          | [] => pure (.done (← finish (.yielded selector outputs) state))
          | frame :: rest =>
              if outputs.length != frame.outputSize then
                .error (.yieldArity frame.outputSize outputs.length)
              else
                let state ← appendValues maxValues { state with values := frame.savedValues } outputs
                pure (.more (start frame.block) rest state)
      | .match index cases fallback => do
          let scrutinee ← read state index
          let block ← selectBranch scrutinee cases fallback
          pure (.more (start block) continuations state)
      | .matchContinue index cases fallback outputSize _sharedAux _sharedLookups continuation => do
          let scrutinee ← read state index
          let block ← selectBranch scrutinee cases fallback
          let frame := ⟨state.values, outputSize, continuation⟩
          pure (.more (start block) (frame :: continuations) state)

def run (toplevel : Toplevel) (maxValues : Nat) : Nat → Task → List Continuation → State →
    Except Error Result
  | 0, _, _, _ => .error .fuelExhausted
  | fuel + 1, task, continuations, state => do
      match ← step toplevel maxValues task continuations state with
      | .done result => .ok result
      | .more task continuations state => run toplevel maxValues fuel task continuations state

def prepare (toplevel : Toplevel) (maxValues maxReplies maxReplyFields maxObservationFields : Nat)
    (function : Nat) (inputs : Values) (replies : List Values) : Except Error (Task × State) := do
  if inputs.length > maxValues then .error .valueLimit
  else if replies.length > maxReplies ||
      replies.foldl (fun count reply => count + reply.length) 0 > maxReplyFields then
    .error .answerLimit
  else
    let callee ← match toplevel.functions[function]? with
      | some callee => .ok callee
      | none => .error (.invalidFunction function)
    if inputs.length != callee.layout.inputSize then
      .error (.inputArity function callee.layout.inputSize inputs.length)
    else
      .ok (start callee.body, { values := inputs.toArray, replies, remainingFields := maxObservationFields })

def runFunction (toplevel : Toplevel) (limits : Limits) (function : Nat) (inputs : Values)
    (replies : List Values) : Except Error Result := do
  let (task, state) ← prepare toplevel limits.maxValues limits.maxReplies limits.maxReplyFields limits.maxObservationFields
    function inputs replies
  run toplevel limits.maxValues limits.maxSteps task [] state

end IxCC.Aiur.OracleEval
