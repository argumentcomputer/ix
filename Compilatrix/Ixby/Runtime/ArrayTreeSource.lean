import Compilatrix.Ixby.Runtime.ArrayTreeLookup
import Compilatrix.Ixby.Runtime.ArrayTreeUpdate
import Compilatrix.Ixby.Runtime.ArrayTreePush
import Compilatrix.Ixby.Runtime.ArrayTreeLaws

/-! Source Array observations and updates for every tree-backed representation.
The element relation is arbitrary; these proofs do not assume numeric elements
or turn an erased source bound proof into a trusted machine precondition. -/

namespace Compilatrix.Ixby.Runtime.ArrayTrees.Certificate

open Ix.Ixby Execution Representation ScalarFunction Conversion
open Words (cachedValue)

variable {program : Program} {links : Links} (certificate : Certificate program links)
  (limits : Limits)

include certificate

theorem size_source (room : 5 ≤ limits.locals) (typeValue : Value)
    {element : α → Value → Prop} {source : Array α} {height : Nat} {tree : Tree height} {size : Value}
    (represented : Prefix links.arithmetic.conversions.layout element source height tree size)
    (continuation : Array Continuation) :
    Reaches limits program
      (frameState links.size 0 #[typeValue, arrayValue links.layout height tree size] continuation)
      (returned size continuation) ∧ Number links.arithmetic.conversions.layout source.size size :=
  ⟨certificate.size_returns limits room typeValue height tree size continuation, represented.sizeRep⟩

theorem usize_source (room : 11 ≤ limits.locals) (capacity : 65 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (platform : System.Platform.numBits = 64) (typeValue : Value)
    {element : α → Value → Prop} {source : Array α} {height : Nat} {tree : Tree height} {size : Value}
    (represented : Prefix links.arithmetic.conversions.layout element source height tree size)
    (valid : (Scalar.nat source.size).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program
      (frameState links.usize 0 #[typeValue, arrayValue links.layout height tree size] continuation)
      (returned (cachedValue links.arithmetic.conversions.layout source.usize.toNat) continuation) := by
  simpa only [Array.usize, Nat.toUSize] using certificate.usize_returns limits room capacity bytesCapacity platform
    typeValue height tree size source.size represented.sizeRep valid continuation stack

theorem empty_source {id : FunctionId} (checked : Checked program id (ArrayTrees.empty links))
    (room : 5 ≤ limits.locals) (typeValue capacityValue : Value) (requested : Nat)
    (element : α → Value → Prop) (continuation : Array Continuation) :
    ∃ value, Reaches limits program (frameState id 0 #[typeValue, capacityValue] continuation)
      (returned value continuation) ∧
      Represents links.arithmetic.conversions.layout links.layout element
        (Array.emptyWithCapacity requested) value := by
  refine ⟨_, certificate.empty_returns limits checked room typeValue capacityValue continuation,
    0, .empty 0, cachedValue links.arithmetic.conversions.layout 0, rfl, ?_⟩
  exact empty_prefix links.arithmetic.conversions.layout element

theorem get_source (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (typeValue proofValue : Value)
    {element : α → Value → Prop} {source : Array α} {height : Nat} {tree : Tree height} {size : Value}
    (represented : Prefix links.arithmetic.conversions.layout element source height tree size)
    (index : Nat) (indexValue : Value) (indexRep : Number links.arithmetic.conversions.layout index indexValue)
    (bounded : index < source.size) (valid : (Scalar.nat (2 ^ height)).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 4 ≤ limits.continuations) :
    ∃ value, Reaches limits program
      (frameState links.get 0 #[typeValue, arrayValue links.layout height tree size, indexValue, proofValue] continuation)
      (returned value continuation) ∧ element source[index] value := by
  obtain ⟨value, found, related⟩ := represented.elements index bounded
  exact ⟨value, certificate.get_returns limits room capacity bytesCapacity typeValue proofValue height tree source.size
    size index indexValue value represented.sizeRep indexRep represented.capacity bounded found valid continuation stack, related⟩

theorem getAlias_source {id : FunctionId} (checked : Checked program id (getAlias links))
    (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (typeValue proofValue : Value)
    {element : α → Value → Prop} {source : Array α} {height : Nat} {tree : Tree height} {size : Value}
    (represented : Prefix links.arithmetic.conversions.layout element source height tree size)
    (index : Nat) (indexValue : Value) (indexRep : Number links.arithmetic.conversions.layout index indexValue)
    (bounded : index < source.size) (valid : (Scalar.nat (2 ^ height)).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 4 ≤ limits.continuations) :
    ∃ value, Reaches limits program
      (frameState id 0 #[typeValue, arrayValue links.layout height tree size, indexValue, proofValue] continuation)
      (returned value continuation) ∧ element source[index] value := by
  obtain ⟨value, found, related⟩ := represented.elements index bounded
  exact ⟨value, certificate.getAlias_returns limits checked room capacity bytesCapacity typeValue proofValue height tree source.size
    size index indexValue value represented.sizeRep indexRep represented.capacity bounded found valid continuation stack, related⟩

theorem getBang_source {id : FunctionId} (checked : Checked program id (ArrayTrees.getBang links))
    (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (typeValue defaultValue : Value)
    {element : α → Value → Prop} {source : Array α} {height : Nat} {tree : Tree height} {size : Value}
    (represented : Prefix links.arithmetic.conversions.layout element source height tree size)
    (fallback : α) (fallbackRep : element fallback defaultValue)
    (index : Nat) (indexValue : Value) (indexRep : Number links.arithmetic.conversions.layout index indexValue)
    (valid : (Scalar.nat (2 ^ height)).validate limits = .ok ())
    (indexValid : (Scalar.nat index).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 4 ≤ limits.continuations) :
    ∃ value, Reaches limits program
      (frameState id 0 #[typeValue, defaultValue, arrayValue links.layout height tree size, indexValue] continuation)
      (returned value continuation) ∧ element (source.getD index fallback) value := by
  by_cases bounded : index < source.size
  · obtain ⟨value, found, related⟩ := represented.elements index bounded
    exact ⟨value, certificate.getBang_of_lt_returns limits checked room capacity bytesCapacity typeValue defaultValue
      height tree source.size size index indexValue value represented.sizeRep indexRep represented.capacity bounded found
      valid continuation stack, by simpa [Array.getD, bounded] using related⟩
  · exact ⟨defaultValue, certificate.getBang_of_ge_returns limits checked room capacity bytesCapacity typeValue defaultValue
      height tree source.size size index indexValue represented.sizeRep indexRep (by omega)
      (validate_nat_mono represented.capacity valid) indexValid continuation stack,
      by simpa [Array.getD, bounded] using fallbackRep⟩

theorem set_source (room : 12 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (typeValue : Value)
    {element : α → Value → Prop} {source : Array α} {height : Nat} {tree : Tree height} {size : Value}
    (represented : Prefix links.arithmetic.conversions.layout element source height tree size)
    (index : Nat) (indexValue : Value) (indexRep : Number links.arithmetic.conversions.layout index indexValue)
    (item : α) (value : Value) (itemRep : element item value)
    (valid : (Scalar.nat (2 ^ height)).validate limits = .ok ())
    (indexValid : (Scalar.nat index).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + max 4 (height + 1) ≤ limits.continuations) :
    ∃ result, Reaches limits program
      (frameState links.set 0 #[typeValue, arrayValue links.layout height tree size, indexValue, value] continuation)
      (returned result continuation) ∧
      Represents links.arithmetic.conversions.layout links.layout element (source.set! index item) result := by
  by_cases bounded : index < source.size
  · exact ⟨_, certificate.set_of_lt_returns limits room capacity bytesCapacity typeValue height tree source.size
      size index indexValue value represented.sizeRep indexRep represented.capacity bounded valid continuation stack,
      height, tree.set height index value, size, rfl, represented.set index bounded item value itemRep⟩
  · refine ⟨_, certificate.set_of_ge_returns limits (by omega) capacity bytesCapacity typeValue height tree source.size
      size index indexValue value represented.sizeRep indexRep (by omega) (validate_nat_mono represented.capacity valid)
      indexValid continuation (by omega), height, tree, size, rfl, ?_⟩
    simpa [Array.set!_eq_setIfInBounds, Array.setIfInBounds, bounded] using represented

theorem uset_source (room : 12 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (typeValue proofValue : Value)
    {element : α → Value → Prop} {source : Array α} {height : Nat} {tree : Tree height} {size : Value}
    (represented : Prefix links.arithmetic.conversions.layout element source height tree size)
    (index : USize) (indexValue : Value) (indexRep : Number links.arithmetic.conversions.layout index.toNat indexValue)
    (bounded : index.toNat < source.size) (item : α) (value : Value) (itemRep : element item value)
    (valid : (Scalar.nat (2 ^ height)).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + max 4 (height + 1) ≤ limits.continuations) :
    ∃ result, Reaches limits program
      (frameState links.uset 0 #[typeValue, arrayValue links.layout height tree size, indexValue, value, proofValue] continuation)
      (returned result continuation) ∧
      Represents links.arithmetic.conversions.layout links.layout element (source.uset index item bounded) result := by
  refine ⟨_, certificate.uset_returns limits room capacity bytesCapacity typeValue proofValue height tree source.size
    size index.toNat indexValue value represented.sizeRep indexRep represented.capacity bounded valid continuation stack,
    height, tree.set height index.toNat value, size, rfl, ?_⟩
  simpa [Array.uset, Array.set!_eq_setIfInBounds, Array.setIfInBounds, bounded] using
    represented.set index.toNat bounded item value itemRep

theorem push_source (room : 16 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (typeValue : Value)
    {element : α → Value → Prop} {source : Array α} {height : Nat} {tree : Tree height} {size : Value}
    (represented : Prefix links.arithmetic.conversions.layout element source height tree size)
    (item : α) (value : Value) (itemRep : element item value)
    (valid : (Scalar.nat (2 ^ (height + 1))).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + max 4 (height + 2) ≤ limits.continuations) :
    ∃ result, Reaches limits program
      (frameState links.push 0 #[typeValue, arrayValue links.layout height tree size, value] continuation)
      (returned result continuation) ∧
      Represents links.arithmetic.conversions.layout links.layout element (source.push item) result := by
  have positive := pow_positive height
  have doubled : 2 ^ (height + 1) = 2 ^ height + 2 ^ height := by rw [Nat.pow_succ]; omega
  by_cases space : source.size < 2 ^ height
  · obtain ⟨nextSize, path, nextRep⟩ := certificate.push_with_space_returns limits (by omega) capacity bytesCapacity
      typeValue height tree source.size size value represented.sizeRep space
      (validate_nat_mono (by omega : 2 ^ height ≤ 2 ^ (height + 1)) valid) continuation (by omega)
    exact ⟨_, path, height, tree.set height source.size value, nextSize, rfl,
      represented.push space item value nextSize itemRep nextRep⟩
  · have full : source.size = 2 ^ height := by have := represented.capacity; omega
    obtain ⟨nextSize, path, nextRep⟩ := certificate.push_full_returns limits room capacity bytesCapacity
      typeValue height tree size value (by simpa only [full] using represented.sizeRep) valid continuation stack
    refine ⟨_, path, height + 1, (Tree.node tree (.empty height)).set (height + 1) (2 ^ height) value,
      nextSize, rfl, ?_⟩
    simpa only [full] using represented.grow.push (by omega) item value nextSize itemRep
      (by simpa only [full] using nextRep)

end Compilatrix.Ixby.Runtime.ArrayTrees.Certificate
