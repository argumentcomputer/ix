import Compilatrix.X86.PhysicalHeapPrimitiveCode

namespace Compilatrix.X86.PhysicalHeap

/-- Argument selection consumes each owning source before selecting the
next one. The certificate records that order independently of runtime data. -/
inductive TakeValues : Scope → List IxIR2.Atom → List Kind → List Scalar.Atom → Scope → Prop where
  | nil (scope) : TakeValues scope [] [] [] scope
  | cons {scope middle next source sources kind kinds operand operands}
      (head : scope.take source = .ok (kind, operand, middle))
      (tail : TakeValues middle sources kinds operands next) :
      TakeValues scope (source :: sources) (kind :: kinds) (operand :: operands) next

inductive TakeCredits : Scope → List IxIR2.CreditId → List IxIR2.LayoutId → Scope → Prop where
  | nil (scope) : TakeCredits scope [] [] scope
  | cons {scope middle next source sources id ids}
      (head : scope.takeCredit source = .ok (id, middle))
      (tail : TakeCredits middle sources ids next) : TakeCredits scope (source :: sources) (id :: ids) next

structure ValueArguments (scope : Scope) (sources : List IxIR2.Atom) where
  kinds : List Kind
  operands : List Scalar.Atom
  next : Scope
  code : TakeValues scope sources kinds operands next

def selectValueList (scope : Scope) : (sources : List IxIR2.Atom) → Except String (ValueArguments scope sources)
  | [] => .ok ⟨[], [], scope, .nil scope⟩
  | source :: sources => do
      let head ← checkedExcept (scope.take source)
      let tail ← selectValueList head.val.2.2 sources
      return ⟨head.val.1 :: tail.kinds, head.val.2.1 :: tail.operands, tail.next, .cons head.property tail.code⟩

abbrev ArgumentsCode (scope : Scope) (arguments : Array IxIR2.Atom)
    (kinds : Array Kind) (operands : Array Scalar.Atom) (next : Scope) : Prop :=
  TakeValues scope arguments.toList kinds.toList operands.toList next

structure ArgumentRow (scope : Scope) (arguments : Array IxIR2.Atom) where
  kinds : Array Kind
  operands : Array Scalar.Atom
  next : Scope
  code : ArgumentsCode scope arguments kinds operands next

def selectArgumentsChecked (scope : Scope) (arguments : Array IxIR2.Atom) : Except String (ArgumentRow scope arguments) := do
  let row ← selectValueList scope arguments.toList
  return ⟨row.kinds.toArray, row.operands.toArray, row.next, by simpa only [ArgumentsCode, List.toList_toArray] using row.code⟩

structure CreditArguments (scope : Scope) (sources : List IxIR2.CreditId) where
  layouts : List IxIR2.LayoutId
  next : Scope
  code : TakeCredits scope sources layouts next

def selectCreditList (scope : Scope) : (sources : List IxIR2.CreditId) → Except String (CreditArguments scope sources)
  | [] => .ok ⟨[], scope, .nil scope⟩
  | source :: sources => do
      let head ← checkedExcept (scope.takeCredit source)
      let tail ← selectCreditList head.val.2 sources
      return ⟨head.val.1 :: tail.layouts, tail.next, .cons head.property tail.code⟩

def valueCopies : Nat → List Scalar.Atom → List Copy
  | _, [] => []
  | start, operand :: operands => ⟨.atom operand, start⟩ :: valueCopies (start + 1) operands

def creditCopies : Nat → List IxIR2.CreditId → List Copy
  | _, [] => []
  | start, source :: sources => ⟨.atom (.var (creditBase + source)), creditBase + start⟩ :: creditCopies (start + 1) sources

def implicitKinds : Option Scalar.Atom → List Kind
  | none => []
  | some _ => [.scalar]

def implicitCopies : Option Scalar.Atom → List Copy
  | none => []
  | some source => [⟨.predecessor source, 0⟩]

def edgeTransfer (implicitValue : Option Scalar.Atom) (kinds : List Kind) (operands : List Scalar.Atom)
    (credits : List IxIR2.CreditId) (layouts : List IxIR2.LayoutId) : Transfer :=
  ⟨(implicitCopies implicitValue ++ valueCopies (implicitKinds implicitValue).length operands ++ creditCopies 0 credits).toArray,
    ⟨((implicitKinds implicitValue ++ kinds).map some).toArray, (layouts.map some).toArray⟩⟩

inductive TransferCode (definition : IxIR2.Function) (scope : Scope) (edge : IxIR2.Edge)
    (implicitValue : Option Scalar.Atom) : Transfer → Prop where
  | mk {target kinds operands middle layouts next}
      (targetAt : definition.blocks[edge.target]? = some target)
      (values : TakeValues scope edge.values.toList kinds operands middle)
      (credits : TakeCredits middle edge.credits.toList layouts next)
      (finished : next.finished = true)
      (bounded : (edgeTransfer implicitValue kinds operands edge.credits.toList layouts).scope.bounded = true) :
      TransferCode definition scope edge implicitValue (edgeTransfer implicitValue kinds operands edge.credits.toList layouts)

structure TransferRow (definition : IxIR2.Function) (scope : Scope) (edge : IxIR2.Edge) (implicitValue : Option Scalar.Atom) where
  transfer : Transfer
  code : TransferCode definition scope edge implicitValue transfer

def selectTransferChecked (definition : IxIR2.Function) (scope : Scope) (edge : IxIR2.Edge)
    (implicitValue : Option Scalar.Atom := none) : Except String (TransferRow definition scope edge implicitValue) := do
  match targetAt : definition.blocks[edge.target]? with
  | none => throw "heap CFG edge target is missing"
  | some target =>
      let values ← selectValueList scope edge.values.toList
      let credits ← selectCreditList values.next edge.credits.toList
      if finished : credits.next.finished = true then
        let transfer := edgeTransfer implicitValue values.kinds values.operands edge.credits.toList credits.layouts
        if transfer.copies.size > maxEdge then throw "heap CFG simultaneous edge copies exceed twelve"
        if transfer.scope.values.size != target.valueParams.size || transfer.scope.credits.size != target.creditParams.size then
          throw "heap CFG edge arity mismatch"
        if !(transfer.scope.values.zip target.valueParams).all (fun (kind, cap) => kind.any (capAccepts cap)) then
          throw "heap CFG edge value capability mismatch"
        if !(transfer.scope.credits.zip target.creditParams).all (fun (id, cap) => id.any (creditAccepts cap)) then
          throw "heap CFG edge credit capability mismatch"
        if bounded : transfer.scope.bounded = true then
          return ⟨transfer, .mk targetAt values.code credits.code finished bounded⟩
        else throw "heap CFG edge parameters exceed the frame"
      else throw "heap CFG edge leaves an owning value or credit behind"

end Compilatrix.X86.PhysicalHeap
