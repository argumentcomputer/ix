import Ix.Compiler.X86.Scalar
import Ix.Compiler.IxIR2.EvalFuel

/-! A proof-facing scalar fragment of the actual physical IxIR₂ CFG.
Registers contain exact literal Nats. Copying and scalar ownership operations
preserve that representation; Nat peeling exposes the exact predecessor.
Block edges substitute their arguments simultaneously. Direct calls target
earlier functions, and bounded CFG expansion excludes cycles. -/
namespace Ix.Compiler.X86.PhysicalScalar
open Ix.Compiler.Ixon (Address)
abbrev Entries := Array (Address × IxIR2.Function)

def lookup (program : IxIR2.Program) (address : Address) : Option IxIR2.Decl :=
  (program.declarations.find? (fun entry => entry.1 == address)).map (·.2)

def lowerAtom (bindings : Array Scalar.Atom) : IxIR2.Atom → Option Scalar.Atom
  | .reg index => bindings[index]?
  | .lit (.nat number) => (ExactNat.encode number).map Scalar.Atom.constant
  | _ => none

def lowerAtoms (bindings : Array Scalar.Atom) (atoms : Array IxIR2.Atom) : Option (Array Scalar.Atom) :=
  atoms.mapM (lowerAtom bindings)

def parameters (count : Nat) : Array Scalar.Atom := (List.range count).toArray.map Scalar.Atom.var

/-- These checks describe a complete credit-free edge, including the implicit
predecessor register on a successor edge. -/
inductive EdgeReady (definition : IxIR2.Function) (edge : IxIR2.Edge)
    (arguments : Array Scalar.Atom) (implicitCount : Nat) : Prop where
  | mk (target : IxIR2.Block)
      (found : definition.blocks[edge.target]? = some target)
      (arity : implicitCount + arguments.size = target.valueParams.size)
      (credits : edge.credits = #[])
      (targetCredits : target.creditParams = #[])

/-- Selection certificates compose at an arbitrary instruction position.
They record only syntax and checked indices, never runtime input values or
an evaluator result. Unused copies are represented by an extended map. -/
inductive Code (entries : Entries) (current : Nat) (definition : IxIR2.Function) :
    Nat → Nat → Array Scalar.Atom → Nat → Scalar.Expr → Prop where
  | ret {block pc bindings locals source target body}
      (blockAt : definition.blocks[block]? = some body) (endAt : pc = body.instructions.size)
      (term : body.terminator = .ret source) (atom : lowerAtom bindings source = some target) :
      Code entries current definition block pc bindings locals (.atom target)
  | move {block pc bindings locals source target body expression}
      (blockAt : definition.blocks[block]? = some body) (instruction : body.instructions[pc]? = some (.move source))
      (atom : lowerAtom bindings source = some target)
      (rest : Code entries current definition block (pc + 1) (bindings.push target) locals expression) :
      Code entries current definition block pc bindings locals expression
  | retain {block pc bindings locals source target body expression}
      (blockAt : definition.blocks[block]? = some body) (instruction : body.instructions[pc]? = some (.retainShared source))
      (atom : lowerAtom bindings source = some target)
      (rest : Code entries current definition block (pc + 1) (bindings.push target) locals expression) :
      Code entries current definition block pc bindings locals expression
  | release {block pc bindings locals source target body expression}
      (blockAt : definition.blocks[block]? = some body) (instruction : body.instructions[pc]? = some (.releaseShared source))
      (atom : lowerAtom bindings source = some target)
      (rest : Code entries current definition block (pc + 1) bindings locals expression) :
      Code entries current definition block pc bindings locals expression
  | drop {block pc bindings locals source target body expression}
      (blockAt : definition.blocks[block]? = some body) (instruction : body.instructions[pc]? = some (.dropUnique source))
      (atom : lowerAtom bindings source = some target)
      (rest : Code entries current definition block (pc + 1) bindings locals expression) :
      Code entries current definition block pc bindings locals expression
  | jump {block pc bindings locals edge arguments body expression}
      (blockAt : definition.blocks[block]? = some body) (endAt : pc = body.instructions.size)
      (term : body.terminator = .jump edge) (atoms : lowerAtoms bindings edge.values = some arguments)
      (ready : EdgeReady definition edge arguments 0)
      (rest : Code entries current definition edge.target 0 arguments locals expression) :
      Code entries current definition block pc bindings locals expression
  | branch {block pc bindings locals source target peel zeroArgs succArgs body zero successor}
      (blockAt : definition.blocks[block]? = some body) (endAt : pc = body.instructions.size)
      (term : body.terminator = .switchValue source #[] (some peel))
      (atom : lowerAtom bindings source = some target)
      (zeroAtoms : lowerAtoms bindings peel.zero.values = some zeroArgs)
      (succAtoms : lowerAtoms bindings peel.succ.values = some succArgs)
      (zeroReady : EdgeReady definition peel.zero zeroArgs 0)
      (succReady : EdgeReady definition peel.succ succArgs 1)
      (zeroCode : Code entries current definition peel.zero.target 0 zeroArgs locals zero)
      (succCode : Code entries current definition peel.succ.target 0 (#[.var locals] ++ succArgs) (locals + 1) successor) :
      Code entries current definition block pc bindings locals
        (.branch target zero (.letE (.sub target (.constant 1)) successor))
  | call {block pc bindings locals address source arguments index callee body expression}
      (blockAt : definition.blocks[block]? = some body) (instruction : body.instructions[pc]? = some (.call address source))
      (atoms : lowerAtoms bindings source = some arguments)
      (found : entries[index]? = some (address, callee)) (earlier : index < current)
      (arity : arguments.size = callee.signature.params.size)
      (rest : Code entries current definition block (pc + 1) (bindings.push (.var locals)) (locals + 1) expression) :
      Code entries current definition block pc bindings locals (.letE (.call index arguments) expression)
  | tailCall {block pc bindings locals address source arguments index callee body}
      (blockAt : definition.blocks[block]? = some body) (endAt : pc = body.instructions.size)
      (term : body.terminator = .tailCall address source) (atoms : lowerAtoms bindings source = some arguments)
      (found : entries[index]? = some (address, callee)) (earlier : index < current)
      (arity : arguments.size = callee.signature.params.size) :
      Code entries current definition block pc bindings locals (.call index arguments)

end Ix.Compiler.X86.PhysicalScalar
