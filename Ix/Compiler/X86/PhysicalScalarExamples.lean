import Ix.Compiler.X86.PhysicalScalarExport

namespace Ix.Compiler.X86.PhysicalScalar.Examples
open Ixon (Address)

def block (parameters : Nat) (instructions : Array IxIR2.Instr) (terminator : IxIR2.Terminator) : IxIR2.Block :=
  { valueParams := Array.replicate parameters .scalar, creditParams := #[], instructions, terminator }

def function (arity : Nat) (blocks : Array IxIR2.Block) : IxIR2.Function :=
  { signature := { params := Array.replicate arity ⟨.shared, .owned⟩, result := .shared, papSafe := true }, blocks }

def edge (target : Nat) (values : Array IxIR2.Atom) : IxIR2.Edge := { target, values, credits := #[] }

def root : Address := Address.replicate 0x40
def helper : Address := Address.replicate 0x41

def program (definition : IxIR2.Function) (helpers : List (Address × IxIR2.Decl) := []) : IxIR2.Program :=
  { declarations := helpers ++ [(root, .fn definition)]
    main := function 0 #[block 0 #[] (.ret (.lit (.nat 0)))] }

def diamond : IxIR2.Program := program (function 2 #[
  block 2 #[] (.switchValue (.reg 0) #[] (some ⟨edge 1 #[.reg 1, .reg 0], edge 2 #[.reg 1, .reg 0]⟩)),
  block 2 #[.move (.reg 0)] (.jump (edge 3 #[.reg 2, .reg 1])),
  block 3 #[.retainShared (.reg 0), .releaseShared (.reg 2)] (.jump (edge 3 #[.reg 3, .reg 1])),
  block 2 #[.dropUnique (.reg 1)] (.ret (.reg 0))])

def swap : IxIR2.Program := program (function 2 #[
  block 2 #[] (.jump (edge 1 #[.reg 1, .reg 0])),
  block 2 #[.move (.reg 0)] (.ret (.reg 1))])

def permuted : IxIR2.Program := program (function 2 #[
  block 2 #[] (.jump (edge 3 #[.reg 1, .reg 0])),
  block 2 #[] (.ret (.reg 0)),
  block 1 #[] (.ret (.reg 0)),
  block 2 #[] (.switchValue (.reg 1) #[] (some ⟨edge 1 #[.reg 0, .reg 1], edge 4 #[.reg 0, .reg 1]⟩)),
  block 3 #[] (.jump (edge 1 #[.reg 2, .reg 1]))])

def constant : IxIR2.Program := program (function 2 #[block 2 #[.call helper #[]] (.ret (.reg 2))])
  [(helper, .fn (function 0 #[block 0 #[] (.ret (.lit (.nat (UInt64.size - 1))))]))]

def cfgs : List (String × IxIR2.Program) := [("diamond", diamond), ("swap", swap), ("permuted", permuted), ("constant", constant)]

def expansion : IxIR2.Program := Id.run do
  let mut blocks := #[]
  for index in [:13] do
    let start := index * 3
    blocks := blocks ++ #[
      block (if index == 0 then 2 else 1) #[] (.switchValue (.reg 0) #[]
        (some ⟨edge (start + 1) #[.reg 0], edge (start + 2) #[.reg 0]⟩)),
      block 1 #[] (.jump (edge (start + 3) #[.reg 0])),
      block 2 #[] (.jump (edge (start + 3) #[.reg 1]))]
  return program (function 2 (blocks.push (block 1 #[] (.ret (.reg 0)))))

def rejections : List (String × IxIR2.Program) :=
  let one := fun instructions terminator => program (function 2 #[block 2 instructions terminator])
  let ret := IxIR2.Terminator.ret (.reg 0)
  let jump := fun e => program (function 2 #[block 2 #[] (.jump e), block 1 #[] (.ret (.reg 0))])
  let cid : IxIR2.CtorId := ⟨Address.replicate 0x20, 0, 0⟩
  let credit : IxIR2.CreditCap := .required (Address.replicate 0x22)
  let identity := function 1 #[block 1 #[] (.ret (.reg 0))]
  [
    ("unknown-register", one #[] (.ret (.reg 2))),
    ("erased-result", one #[] (.ret .erased)),
    ("literal-overflow", one #[] (.ret (.lit (.nat UInt64.size)))),
    ("unknown-block", jump (edge 99 #[.reg 0])),
    ("edge-arity", jump (edge 1 #[.reg 0, .reg 1])),
    ("edge-credit", jump { edge 1 #[.reg 0] with credits := #[0] }),
    ("target-credit", program (function 2 #[block 2 #[] (.jump (edge 1 #[.reg 0])),
      { block 1 #[] (.ret (.reg 0)) with creditParams := #[credit] }])),
    ("missing-peel", one #[] (.switchValue (.reg 0) #[] none)),
    ("constructor-switch", one #[] (.switchValue (.reg 0) #[⟨cid, edge 0 #[]⟩] (some ⟨edge 0 #[], edge 0 #[]⟩))),
    ("allocation", one #[.alloc .shared cid #[]] ret),
    ("fetch", one #[.fetch (.reg 0) cid 0] ret),
    ("extern", one #[.extern helper #[.reg 0]] ret),
    ("apply", one #[.apply (.reg 0) #[.reg 1]] ret),
    ("pap", one #[.papp helper #[]] ret),
    ("self-call", one #[.callSelf #[.reg 0, .reg 1]] ret),
    ("self-tail-call", one #[] (.tailCallSelf #[.reg 0, .reg 1])),
    ("recursive-call", one #[.call root #[.reg 0, .reg 1]] ret),
    ("missing-callee", one #[.call helper #[.reg 0]] ret),
    ("extern-callee", program (function 2 #[block 2 #[.call helper #[.reg 0]] ret]) [(helper, .extern 1)]),
    ("call-arity", program (function 2 #[block 2 #[.call helper #[]] ret]) [(helper, .fn identity)]),
    ("parameters", program (function 3 #[block 3 #[] ret])),
    ("no-blocks", program (function 2 #[])),
    ("cycle", one #[] (.jump (edge 0 #[.reg 0, .reg 1]))),
    ("local-capacity", program (function 2 #[block 2 (Array.replicate 31 (.call helper #[.reg 0])) (.ret (.reg 32))])
      [(helper, .fn identity)]),
    ("expansion-budget", expansion),
    ("instruction-budget", one (Array.replicate 129 (.move (.reg 0))) ret)]

end Ix.Compiler.X86.PhysicalScalar.Examples
