import Ix.Compiler.IxIR0.Serialize

/-! Explicit recursor instantiation metadata. Ordinary IxIR₀ declarations
retain their existing syntax and evaluator. The instantiation identity commits
to both that declaration and every argument, field, and result world. -/

namespace Ix.Compiler.IxIR0

open Ix.Compiler.Ixon (Address Owned)
open Ix.Compiler.IxIR

structure RecursorInstance where
  declaration : Decl
  arguments : List Owned
  fields : List (List Owned)
  result : Owned
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

def RecursorInstance.wellShaped (instantiation : RecursorInstance) : Bool :=
  match instantiation.declaration with
  | .recursor numArgs _ rules =>
      instantiation.arguments.length == numArgs + 1 &&
        instantiation.fields.length == rules.size &&
        (instantiation.fields.zip rules.toList).all fun (worlds, rule) => worlds.length == rule.fields
  | _ => false

def RecursorInstance.bytes (instantiation : RecursorInstance) : ByteArray :=
  Encoding.domain "compilatrix/ixir0/recursor-instance/1" ++ Encoding.tag 0 ++
    Encoding.blob instantiation.declaration.preimage ++
    Encoding.list (fun world => Encoding.tag world.toBits) instantiation.arguments ++
    Encoding.list (Encoding.list fun world => Encoding.tag world.toBits) instantiation.fields ++
    Encoding.tag instantiation.result.toBits

def RecursorInstance.address (instantiation : RecursorInstance) : Address :=
  Address.blake3 instantiation.bytes

theorem RecursorInstance.address_eq_iff_bytes_eq (left right : RecursorInstance)
    (hcollision : Address.Blake3NoCollision left.bytes right.bytes) :
    left.address = right.address ↔ left.bytes = right.bytes := by
  constructor
  · exact hcollision
  · intro h; simp only [address]; rw [h]

end Ix.Compiler.IxIR0
