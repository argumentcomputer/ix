import Compilatrix.Ixby.Runtime.ScalarLaws

namespace Compilatrix.Ixby.Runtime.Native

open Ix.Ixby

def natural (n : Nat) : Value := .scalar (.nat n)
def word (w : UInt32) : Value := .scalar (.word32 w)
def field (f : Goldilocks) : Value := .scalar (.field f)

def arrayId : CtorId := ⟨1, 0, 1⟩
def bytesId : CtorId := ⟨1, 0, 0⟩
def writerId : CtorId := ⟨1, 0, 2⟩

@[simp] theorem bytes_array_distinct : ((⟨1, 0, 0⟩ : CtorId) == ⟨1, 0, 1⟩) = false := rfl
@[simp] theorem bytes_writer_distinct : ((⟨1, 0, 0⟩ : CtorId) == ⟨1, 0, 2⟩) = false := rfl
@[simp] theorem array_writer_distinct : ((⟨1, 0, 1⟩ : CtorId) == ⟨1, 0, 2⟩) = false := rfl

def arrayValue (values : Array Value) : Value := .ctor arrayId #[.array values]
def packedValue (bytes : Array UInt8) : Value :=
  .ctor bytesId #[.scalar (.bytes bytes), natural bytes.size]
def writerValue (bytes : Array UInt8) : Value := .ctor writerId #[.byteBuilder bytes]

/-- An embedding can represent arbitrary source elements, including nested
arrays, constructors, and closures. Pointer identity plays no part. -/
def ArrayRep {α : Type} (encode : α → Value) (source : Array α) (value : Value) : Prop :=
  value = arrayValue (source.map encode)

def byteWord (byte : UInt8) : Value := word byte.toUInt32

inductive BytesRep (bytes : Array UInt8) : Value → Prop
  | packed : BytesRep bytes (packedValue bytes)
  | array : BytesRep bytes (arrayValue (bytes.map byteWord))

/-- This relation is internal to a writer; it is never an I/O representation. -/
def BuilderRep (bytes : Array UInt8) (value : Value) : Prop := value = .byteBuilder bytes

def NatValid (limits : Limits) (n : Nat) : Prop := (Scalar.nat n).validate limits = .ok ()

/-- The primitive evaluator checks each immediate operand before computation.
Whole input admission additionally checks every nested element. -/
def ArgumentValid (limits : Limits) : Value → Prop
  | .scalar scalar => scalar.validate limits = .ok ()
  | .array values => values.size < 2 ^ 32
  | .byteBuilder bytes => (Scalar.bytes bytes).validate limits = .ok ()
  | _ => True

def ResultValid (limits : Limits) : Value → Prop
  | .scalar scalar => scalar.validate limits = .ok ()
  | _ => True

theorem natural_injective : Function.Injective natural := by intro a b h; cases h; rfl
theorem natural_ne_word (n : Nat) (w : UInt32) : natural n ≠ word w := by simp [natural, word]
theorem natural_ne_field (n : Nat) (f : Goldilocks) : natural n ≠ field f := by simp [natural, field]

/-- Native proof admission is stricter than the Lean semantics. Capacity of
at least 128 bits does not license a value outside the Nat128 encoding. -/
def Nat128Admitted (n : Nat) : Prop := n < 2 ^ 128

theorem semantic_nat_outside_nat128 :
    NatValid { natBits := 129 } (2 ^ 128) ∧ ¬ Nat128Admitted (2 ^ 128) := by
  unfold NatValid Nat128Admitted
  constructor
  · rfl
  · omega

theorem arrayRep_length {α : Type} (encode : α → Value) (source : Array α) :
    (source.map encode).size = source.size := Array.size_map

theorem arrayRep_index {α : Type} (encode : α → Value) (source : Array α)
    (index : Nat) (bound : index < source.size) :
    (source.map encode)[index]'(by simpa using bound) = encode source[index] := by simp

theorem arrayRep_update {α : Type} (encode : α → Value) (source : Array α)
    (index : Nat) (value : α) :
    ArrayRep encode (source.set! index value)
      (arrayValue ((source.map encode).set! index (encode value))) := by
  simp [ArrayRep, Array.set!]

theorem arrayRep_push {α : Type} (encode : α → Value) (source : Array α) (value : α) :
    ArrayRep encode (source.push value) (arrayValue ((source.map encode).push (encode value))) := by
  simp [ArrayRep]

theorem arrayRep_append {α : Type} (encode : α → Value) (a b : Array α) :
    ArrayRep encode (a ++ b) (arrayValue (a.map encode ++ b.map encode)) := by simp [ArrayRep]

/-- Updating a derived version leaves the old represented sequence available. -/
theorem arrayRep_alias {α : Type} (encode : α → Value) (source : Array α)
    (index : Nat) (value : α) :
    ArrayRep encode source (arrayValue (source.map encode)) ∧
    ArrayRep encode (source.set! index value)
      (arrayValue ((source.map encode).set! index (encode value))) :=
  ⟨rfl, arrayRep_update encode source index value⟩

end Compilatrix.Ixby.Runtime.Native
