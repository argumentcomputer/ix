import Ix.Compiler.IxIR2.Borrow.Rewrite
import Ix.Compiler.IxIR2.Eval

/-! Structural certificates for allocation-free borrowed readers. The
certificate contains syntax and declaration lookup facts, never an execution
of a runtime argument. The semantic proof is in `OpenSim`. -/

namespace Ix.Compiler.IxIR2.Borrow.Open

open Ix.Compiler.Ixon (Address)

structure Schema where
  zero : CtorId
  succ : CtorId
  zeroResult : Nat
  succResult : Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

def signature (borrowed : Bool) : Signature :=
  { params := #[{ world := .shared, passing := if borrowed then .borrowed else .owned }]
    result := .shared
    papSafe := !borrowed }

def capability (borrowed : Bool) : ValueCap :=
  if borrowed then .borrowed .shared .caller else .owned .shared

def block (borrowed : Bool) (instructions : Array Instr) (terminator : Terminator) : Block :=
  { valueParams := #[capability borrowed], creditParams := #[], instructions, terminator }

def release (borrowed : Bool) : Array Instr :=
  if borrowed then #[] else #[.releaseShared (.reg 0)]

def reader (schema : Schema) (borrowed : Bool) : Function :=
  { signature := signature borrowed
    blocks := #[
      block borrowed #[] (.switchValue (.reg 0) #[
        { cid := schema.zero, edge := { target := 1, values := #[.reg 0], credits := #[] } },
        { cid := schema.succ, edge := { target := 2, values := #[.reg 0], credits := #[] } }] none),
      block borrowed (release borrowed) (.ret (.lit (.nat schema.zeroResult))),
      block borrowed (#[.fetch (.reg 0) schema.succ 0] ++ release borrowed)
        (.ret (.lit (.nat schema.succResult))) ] }

def forward (borrowed : Bool) (address : Address) : Function :=
  { signature := signature borrowed
    blocks := #[block borrowed #[] (.tailCall address #[.reg 0])] }

def twice (borrowed : Bool) (address : Address) : Function :=
  { signature := signature borrowed
    blocks := #[block borrowed #[
      if borrowed then .move (.reg 0) else .retainShared (.reg 0),
      .call address #[.reg 1], .releaseShared (.reg 2)] (.tailCall address #[.reg 0])] }

def factory (address : Address) : Function :=
  { signature := { params := #[], result := .shared, papSafe := true }
    blocks := #[{ valueParams := #[], creditParams := #[], instructions := #[.papp address #[]]
                  terminator := .ret (.reg 0) }] }

/-- A finite declaration derivation rules out unresolved calls and recursive
cycles. Its depth is independent of every runtime value and heap. -/
inductive Chain (context : Eval.Context) (schema : Schema) (borrowed : Bool) : Function → Type where
  | reader : Chain context schema borrowed (reader schema borrowed)
  | forward (address : Address) (callee : Function)
      (found : context.declarations address = some (.fn callee))
      (tail : Chain context schema borrowed callee) :
      Chain context schema borrowed (forward borrowed address)

def Chain.depth {context schema borrowed definition} :
    Chain context schema borrowed definition → Nat
  | .reader => 0
  | .forward _ _ _ tail => tail.depth + 1

def recognizeChain (context : Eval.Context) (schema : Schema) (borrowed : Bool) :
    Nat → (definition : Function) → Option (Chain context schema borrowed definition)
  | 0, _ => none
  | fuel + 1, definition =>
      if exact : definition = reader schema borrowed then
        some (exact ▸ Chain.reader)
      else do
        let some entry := definition.blocks[0]? | none
        let .tailCall address _ := entry.terminator | none
        let some (.fn callee) := context.declarations address | none
        let tail ← recognizeChain context schema borrowed fuel callee
        if found : context.declarations address = some (.fn callee) then
          if exact : definition = forward borrowed address then
            some (exact ▸ Chain.forward address callee found tail)
          else none
        else none

inductive Body (context : Eval.Context) (schema : Schema) (borrowed : Bool) : Function → Type where
  | chain {definition : Function} (chain : Chain context schema borrowed definition) :
      Body context schema borrowed definition
  | twice (address : Address) (callee : Function)
      (found : context.declarations address = some (.fn callee))
      (chain : Chain context schema borrowed callee) :
      Body context schema borrowed (twice borrowed address)

def Body.isTwice {context schema borrowed definition} : Body context schema borrowed definition → Bool
  | .chain _ => false
  | .twice .. => true

def Body.depth {context schema borrowed definition} : Body context schema borrowed definition → Nat
  | .chain derivation => derivation.depth
  | .twice _ _ _ derivation => derivation.depth

def Body.readWork {context schema borrowed definition} (body : Body context schema borrowed definition) : Nat :=
  if body.isTwice then 1 else 0

def Body.readCost {context schema borrowed definition} (body : Body context schema borrowed definition)
    (fieldCost : Nat) : Nat :=
  if body.isTwice then 2 * body.depth + 8 + 2 * fieldCost else body.depth + 2 + fieldCost

def Body.ownedCost {context schema borrowed definition} (body : Body context schema borrowed definition)
    (fieldCost : Nat) : Nat :=
  if body.isTwice then 2 * body.depth + 10 + 2 * fieldCost else body.depth + 3 + fieldCost

def recognizeBody (context : Eval.Context) (schema : Schema) (borrowed : Bool)
    (fuel : Nat) (definition : Function) : Option (Body context schema borrowed definition) := do
  match recognizeChain context schema borrowed fuel definition with
  | some chain => some (.chain chain)
  | none =>
      let some entry := definition.blocks[0]? | none
      let .tailCall address _ := entry.terminator | none
      let some (.fn callee) := context.declarations address | none
      let chain ← recognizeChain context schema borrowed fuel callee
      if found : context.declarations address = some (.fn callee) then
        if exact : definition = twice borrowed address then
          some (exact ▸ Body.twice address callee found chain)
        else none
      else none

theorem Chain.signature {context schema borrowed definition}
    (chain : Chain context schema borrowed definition) : definition.signature = signature borrowed := by
  cases chain <;> rfl

theorem Chain.nonempty {context schema borrowed definition}
    (chain : Chain context schema borrowed definition) : definition.blocks.isEmpty = false := by
  cases chain <;> rfl

theorem Body.signature {context schema borrowed definition}
    (body : Body context schema borrowed definition) : definition.signature = signature borrowed := by
  cases body with
  | chain chain => exact chain.signature
  | twice => rfl

theorem Body.nonempty {context schema borrowed definition}
    (body : Body context schema borrowed definition) : definition.blocks.isEmpty = false := by
  cases body with
  | chain derivation => exact derivation.nonempty
  | twice => rfl

end Ix.Compiler.IxIR2.Borrow.Open
