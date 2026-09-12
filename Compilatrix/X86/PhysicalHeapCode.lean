import Compilatrix.X86.PhysicalHeapTransferCode

namespace Compilatrix.X86.PhysicalHeap
open Compilatrix.Ixon (Address)

inductive Tree where
  | ret (kind : Kind) (value : Scalar.Atom)
  | primitive (operation : Primitive) (next : Tree)
  | jump (transfer : Transfer) (next : Tree)
  | branch (value : Scalar.Atom) (zeroTransfer : Transfer) (zero : Tree)
      (succTransfer : Transfer) (successor : Tree)
  | call (function : Nat) (arguments : Array Scalar.Atom) (destination : Nat) (next : Tree)
  | tailCall (kind : Kind) (function : Nat) (arguments : Array Scalar.Atom)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def Tree.result : Tree → Kind
  | .ret kind _ | .tailCall kind _ _ => kind
  | .primitive _ next | .jump _ next | .call _ _ _ next => next.result
  | .branch _ _ zero _ _ => zero.result

def Tree.nodes : Tree → Nat
  | .ret .. | .tailCall .. => 1
  | .primitive _ next | .jump _ next | .call _ _ _ next => 1 + next.nodes
  | .branch _ _ zero _ successor => 1 + zero.nodes + successor.nodes

def Tree.allocations (callees : Array Nat) : Tree → Nat
  | .ret .. => 0
  | .primitive operation next => operation.allocations + next.allocations callees
  | .jump _ next => next.allocations callees
  | .branch _ _ zero _ successor => max (zero.allocations callees) (successor.allocations callees)
  | .call function _ _ next => callees[function]?.getD 0 + next.allocations callees
  | .tailCall _ function _ => callees[function]?.getD 0

def Tree.controls (callees : Array Nat) : Tree → Nat
  | .ret .. => 1
  | .primitive _ next | .jump _ next => 1 + next.controls callees
  | .branch _ _ zero _ successor => 1 + max (zero.controls callees) (successor.controls callees)
  | .call function _ _ next => 1 + callees[function]?.getD 0 + next.controls callees
  | .tailCall _ function _ => 1 + callees[function]?.getD 0

structure Interface where
  address : Address
  definition : IxIR2.Function
  parameters : Array Kind
  result : Kind
  allocations : Nat
  controls : Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

abbrev Interfaces := Array Interface

/-- Each constructor records actual source syntax and executable scope
selection. The certificate contains no input values, heap, or runtime trace. -/
inductive Code (schemas : Schemas) (constructors : Array IxIR2.CtorId)
    (entries : Interfaces) (current : Nat) (definition : IxIR2.Function) :
    Nat → Nat → Scope → Tree → Prop where
  | ret {block pc scope body source kind value next}
      (blockAt : definition.blocks[block]? = some body) (endAt : pc = body.instructions.size)
      (term : body.terminator = .ret source) (taken : scope.take source = .ok (kind, value, next))
      (finished : next.finished = true) : Code schemas constructors entries current definition block pc scope (.ret kind value)
  | primitive {block pc scope body instruction operation nextScope next}
      (blockAt : definition.blocks[block]? = some body) (instructionAt : body.instructions[pc]? = some instruction)
      (selected : PrimitiveCode schemas constructors scope instruction operation nextScope)
      (rest : Code schemas constructors entries current definition block (pc + 1) nextScope next) :
      Code schemas constructors entries current definition block pc scope (.primitive operation next)
  | jump {block pc scope body edge transfer next}
      (blockAt : definition.blocks[block]? = some body) (endAt : pc = body.instructions.size)
      (term : body.terminator = .jump edge) (selected : TransferCode definition scope edge none transfer)
      (rest : Code schemas constructors entries current definition edge.target 0 transfer.scope next) :
      Code schemas constructors entries current definition block pc scope (.jump transfer next)
  | branch {block pc scope body source constructorsAt peel value zeroTransfer zero succTransfer successor}
      (blockAt : definition.blocks[block]? = some body) (endAt : pc = body.instructions.size)
      (term : body.terminator = .switchValue source constructorsAt (some peel))
      (scalar : scope.scalar source = .ok value)
      (zeroSelected : TransferCode definition scope peel.zero none zeroTransfer)
      (succSelected : TransferCode definition scope peel.succ (some value) succTransfer)
      (sameResult : zero.result = successor.result)
      (zeroCode : Code schemas constructors entries current definition peel.zero.target 0 zeroTransfer.scope zero)
      (succCode : Code schemas constructors entries current definition peel.succ.target 0 succTransfer.scope successor) :
      Code schemas constructors entries current definition block pc scope
        (.branch value zeroTransfer zero succTransfer successor)
  | constructor {block pc scope body source alternative peel value transfer next}
      (blockAt : definition.blocks[block]? = some body) (endAt : pc = body.instructions.size)
      (term : body.terminator = .switchValue source #[alternative] peel)
      (node : scope.node source = .ok value)
      (selected : TransferCode definition scope alternative.edge none transfer)
      (rest : Code schemas constructors entries current definition alternative.edge.target 0 transfer.scope next) :
      Code schemas constructors entries current definition block pc scope (.jump transfer next)
  | present {block pc scope body credit yes no layout transfer next}
      (blockAt : definition.blocks[block]? = some body) (endAt : pc = body.instructions.size)
      (term : body.terminator = .branchCredit credit yes no)
      (active : scope.credits[credit]? = some (some layout))
      (selected : TransferCode definition scope yes none transfer)
      (rest : Code schemas constructors entries current definition yes.target 0 transfer.scope next) :
      Code schemas constructors entries current definition block pc scope (.jump transfer next)
  | call {block pc scope body address arguments kinds operands consumed index callee nextScope next}
      (blockAt : definition.blocks[block]? = some body)
      (instructionAt : body.instructions[pc]? = some (.call address arguments))
      (selected : ArgumentsCode scope arguments kinds operands consumed)
      (found : entries[index]? = some callee) (earlier : index < current)
      (addressed : callee.address = address) (parameters : callee.parameters = kinds)
      (pushed : consumed.pushValue callee.result = .ok nextScope)
      (rest : Code schemas constructors entries current definition block (pc + 1) nextScope next) :
      Code schemas constructors entries current definition block pc scope (.call index operands scope.values.size next)
  | tailCall {block pc scope body address arguments kinds operands consumed index callee}
      (blockAt : definition.blocks[block]? = some body) (endAt : pc = body.instructions.size)
      (term : body.terminator = .tailCall address arguments)
      (selected : ArgumentsCode scope arguments kinds operands consumed)
      (finished : consumed.finished = true)
      (found : entries[index]? = some callee) (earlier : index < current)
      (addressed : callee.address = address) (parameters : callee.parameters = kinds) :
      Code schemas constructors entries current definition block pc scope (.tailCall callee.result index operands)

/-- Appending later declarations does not change any earlier call target. -/
theorem Code.weaken {schemas constructors entries current definition block pc scope tree}
    (code : Code schemas constructors entries current definition block pc scope tree)
    {larger : Interfaces} {rank : Nat}
    (same : ∀ (index : Nat) (callee : Interface), entries[index]? = some callee → larger[index]? = some callee)
    (rankBound : current ≤ rank) : Code schemas constructors larger rank definition block pc scope tree := by
  induction code with
  | ret a b c d e => exact .ret a b c d e
  | primitive a b c _ ih => exact .primitive a b c ih
  | jump a b c d _ ih => exact .jump a b c d ih
  | branch a b c d e f g _ _ ihZero ihSucc => exact .branch a b c d e f g ihZero ihSucc
  | constructor a b c d e _ ih => exact .constructor a b c d e ih
  | present a b c d e _ ih => exact .present a b c d e ih
  | call a b c d e f g h _ ih => exact .call a b c (same _ _ d) (by omega) f g h ih
  | tailCall a b c d e f g h i => exact .tailCall a b c d e (same _ _ f) (by omega) h i

theorem Code.budgets {schemas constructors entries current definition block pc scope tree}
    (code : Code schemas constructors entries current definition block pc scope tree)
    {larger : Interfaces}
    (same : ∀ (index : Nat) (callee : Interface), entries[index]? = some callee → larger[index]? = some callee) :
    tree.allocations (larger.map (·.allocations)) = tree.allocations (entries.map (·.allocations)) ∧
      tree.controls (larger.map (·.controls)) = tree.controls (entries.map (·.controls)) := by
  induction code with
  | ret => exact ⟨rfl, rfl⟩
  | primitive _ _ _ _ ih => simp only [Tree.allocations, Tree.controls, ih.1, ih.2, and_self]
  | jump _ _ _ _ _ ih | constructor _ _ _ _ _ _ ih | present _ _ _ _ _ _ ih =>
      simp only [Tree.allocations, Tree.controls, ih.1, ih.2, and_self]
  | branch _ _ _ _ _ _ _ _ _ ihZero ihSucc =>
      simp only [Tree.allocations, Tree.controls, ihZero.1, ihSucc.1, ihZero.2, ihSucc.2, and_self]
  | call _ _ _ found _ _ _ _ _ ih =>
      simp only [Tree.allocations, Tree.controls, Array.getElem?_map, found, same _ _ found,
        Option.map_some, Option.getD_some, ih.1, ih.2, and_self]
  | tailCall _ _ _ _ _ found _ _ _ =>
      simp only [Tree.allocations, Tree.controls, Array.getElem?_map, found, same _ _ found,
        Option.map_some, Option.getD_some, and_self]

structure FunctionCode (schemas : Schemas) (constructors : Array IxIR2.CtorId)
    (entries : Interfaces) (current : Nat) (interface : Interface) where
  tree : Tree
  arity : interface.parameters.size = interface.definition.signature.params.size
  small : interface.parameters.size ≤ 2
  owned : interface.definition.signature.params.all (·.passing == .owned) = true
  nonempty : interface.definition.blocks.isEmpty = false
  result : tree.result = interface.result
  allocations : tree.allocations (entries.map (·.allocations)) = interface.allocations
  controls : tree.controls (entries.map (·.controls)) = interface.controls
  code : Code schemas constructors entries current interface.definition 0 0 (Scope.initial interface.parameters) tree

def FunctionCode.weaken {schemas constructors entries current interface}
    (source : FunctionCode schemas constructors entries current interface) {larger : Interfaces}
    (same : ∀ (index : Nat) (callee : Interface), entries[index]? = some callee → larger[index]? = some callee) :
    FunctionCode schemas constructors larger current interface :=
  { source with
    allocations := (source.code.budgets same).1.trans source.allocations
    controls := (source.code.budgets same).2.trans source.controls
    code := source.code.weaken same (Nat.le_refl _) }

end Compilatrix.X86.PhysicalHeap
