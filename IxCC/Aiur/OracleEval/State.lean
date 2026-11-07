import IxCC.Aiur.OracleEval.Gadgets

namespace IxCC.Aiur.OracleEval

open _root_.Aiur (G)

def read (state : State) (index : Nat) : Except Error G :=
  match state.values[index]? with
  | some value => .ok value
  | none => .error (.invalidIndex index)

def readMany (maxValues : Nat) (state : State) (indices : Array Nat) : Except Error Values :=
  if indices.size > maxValues then .error .valueLimit
  else indices.toList.mapM (read state)

def appendValues (maxValues : Nat) (state : State) (values : Values) : Except Error State :=
  if state.values.size + values.length > maxValues then .error .valueLimit
  else .ok { state with values := state.values ++ values.toArray }

/-- Check the supplied list's size; never allocate from an opcode's size. -/
def takeReply (state : State) (expected : Nat) : Except Error (Values × State) :=
  match state.replies with
  | [] => .error .missingReply
  | answer :: rest =>
      if answer.length = expected then .ok (answer, { state with replies := rest })
      else .error (.replyArity expected answer.length)

def demandFields : Message → Nat
  | .function _ inputs outputs => inputs.length + outputs.length + 2
  | .memory _ _ values => values.length + 3
  | .gadget _ payload => payload.length + 2

def chargeFields (state : State) (count : Nat) : Except Error State :=
  if count > state.remainingFields then .error .observationLimit
  else .ok { state with remainingFields := state.remainingFields - count }

def demand (state : State) (message : Message) : Except Error State := do
  let state ← chargeFields state (demandFields message)
  pure { state with demandsRev := message :: state.demandsRev }

def recordAdvice (state : State) (request : AdviceRequest) (answer : Values) : Except Error State := do
  let state ← chargeFields state (1 + request.inputFields + answer.length)
  pure { state with adviceRev := ⟨request, answer⟩ :: state.adviceRev }

def hint (maxValues : Nat) (state : State) (request : AdviceRequest) (size : Nat) :
    Except Error State := do
  let (answer, state) ← takeReply state size
  let state ← recordAdvice state request answer
  appendValues maxValues state answer

def fieldBinary (maxValues : Nat) (state : State) (left right : Nat)
    (operation : G → G → G) : Except Error State := do
  let a ← read state left
  let b ← read state right
  appendValues maxValues state [operation a b]

def gadgetStep (maxValues : Nat) (state : State) (gadget : Gadget) (inputs : Values) :
    Except Error State := do
  let (outputs, state) ← takeReply state gadget.outputSize
  let state ← demand state (gadget.message inputs outputs)
  appendValues maxValues state outputs

def unaryGadget (maxValues : Nat) (state : State) (gadget : Gadget) (index : Nat) :
    Except Error State := do
  let value ← read state index
  gadgetStep maxValues state gadget [value]

def binaryGadget (maxValues : Nat) (state : State) (gadget : Gadget) (left right : Nat) :
    Except Error State := do
  let a ← read state left
  let b ← read state right
  gadgetStep maxValues state gadget [a, b]

/-- Field packing. The opcode helpers separately require four operands. -/
def packBytes (bytes : Values) : G := bytes.foldr (fun byte rest => byte + 256 * rest) 0

def invTwo32 : G := G.ofNat 0xfffffffe00000002

theorem two32_mul_inv : (G.ofNat (2 ^ 32)) * invTwo32 = 1 := by decide

def readWord (maxValues : Nat) (state : State) (indices : Array Nat) : Except Error Values :=
  if indices.size = 4 then readMany maxValues state indices
  else .error (.operandArity 4 indices.size)

def u32Hint (maxValues : Nat) (state : State) (request : AdviceRequest) (sum : G) :
    Except Error State := do
  let (bytes, state) ← takeReply state 4
  let carry := (sum - packBytes bytes) * invTwo32
  let state ← recordAdvice state request bytes
  appendValues maxValues state (bytes ++ [carry])

end IxCC.Aiur.OracleEval
