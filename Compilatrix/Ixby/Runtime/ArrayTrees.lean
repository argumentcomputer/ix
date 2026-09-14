import Compilatrix.Ixby.Runtime.ArrayTreeSource

/-! Whole-program corollaries for all fifteen certified tree-slice helpers.
Each corollary requires ordinary admission and complete input validation.
Borrowed entry points share the corresponding safe source observation. -/

namespace Compilatrix.Ixby.Runtime.ArrayTrees.Certificate

open Ix.Ixby Execution Representation ScalarFunction Conversion
open Words (cachedValue)

variable {program : Program} {links : Links} (certificate : Certificate program links)
  (limits : Limits)

include certificate

theorem treeGet_evaluates (room : 8 ≤ limits.locals) (capacity : 2 ≤ limits.natBits)
    (height : Nat) (tree : Tree height) (index : Nat) (value : Value)
    (bounded : index < 2 ^ height) (found : tree.get index = some value)
    (valid : (Scalar.nat (2 ^ height)).validate limits = .ok ())
    (entry : program.entry = links.treeGet) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes #[tree.encode links.layout, .scalar (.nat (2 ^ height)), .scalar (.nat index)].toList = .ok ()) :
    Evaluates limits program #[tree.encode links.layout, .scalar (.nat (2 ^ height)), .scalar (.nat index)]
      value := by
  apply evaluates_of_returns certificate.treeGet rfl rfl _ rfl (by simp; omega) entry admitted inputs
  exact certificate.treeGet_returns limits room capacity height tree index value bounded found valid #[]

theorem treeSet_evaluates (room : 12 ≤ limits.locals) (capacity : 2 ≤ limits.natBits)
    (height : Nat) (tree : Tree height) (index : Nat) (value : Value)
    (bounded : index < 2 ^ height)
    (valid : (Scalar.nat (2 ^ height)).validate limits = .ok ())
    (stack : height ≤ limits.continuations)
    (entry : program.entry = links.treeSet) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes #[tree.encode links.layout, .scalar (.nat (2 ^ height)), .scalar (.nat index), value].toList = .ok ()) :
    Evaluates limits program #[tree.encode links.layout, .scalar (.nat (2 ^ height)), .scalar (.nat index), value]
      ((tree.set height index value).encode links.layout) := by
  apply evaluates_of_returns certificate.treeSet rfl rfl _ rfl (by simp; omega) entry admitted inputs
  exact certificate.treeSet_returns limits room capacity height tree index value bounded valid #[] (by simpa using stack)

theorem empty_evaluates (room : 5 ≤ limits.locals) (typeValue capacityValue : Value)
    (requested : Nat) (element : α → Value → Prop)
    (entry : program.entry = links.empty) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes #[typeValue, capacityValue].toList = .ok ()) :
    ∃ value, Evaluates limits program #[typeValue, capacityValue] value ∧
      Represents links.arithmetic.conversions.layout links.layout element (Array.emptyWithCapacity requested) value := by
  obtain ⟨value, path, related⟩ := certificate.empty_source limits certificate.empty room typeValue capacityValue
    requested element #[]
  exact ⟨value, evaluates_of_returns certificate.empty rfl rfl _ rfl (by simp; omega) entry admitted inputs path, related⟩

theorem mkEmpty_evaluates (room : 5 ≤ limits.locals) (typeValue capacityValue : Value)
    (requested : Nat) (element : α → Value → Prop)
    (entry : program.entry = links.mkEmpty) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes #[typeValue, capacityValue].toList = .ok ()) :
    ∃ value, Evaluates limits program #[typeValue, capacityValue] value ∧
      Represents links.arithmetic.conversions.layout links.layout element (Array.mkEmpty requested) value := by
  obtain ⟨value, path, related⟩ := certificate.empty_source limits certificate.mkEmpty room typeValue capacityValue
    requested element #[]
  exact ⟨value, evaluates_of_returns certificate.mkEmpty rfl rfl _ rfl (by simp; omega) entry admitted inputs path, related⟩

theorem size_evaluates (room : 5 ≤ limits.locals) (typeValue : Value)
    {element : α → Value → Prop} {source : Array α} {height : Nat} {tree : Tree height} {size : Value}
    (represented : Prefix links.arithmetic.conversions.layout element source height tree size)
    (entry : program.entry = links.size) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes #[typeValue, arrayValue links.layout height tree size].toList = .ok ()) :
    Evaluates limits program #[typeValue, arrayValue links.layout height tree size] size ∧
      Number links.arithmetic.conversions.layout source.size size := by
  have path := certificate.size_source limits room typeValue represented #[]
  exact ⟨evaluates_of_returns certificate.size rfl rfl _ rfl (by simp; omega) entry admitted inputs path.1, path.2⟩

theorem usize_evaluates (room : 11 ≤ limits.locals) (capacity : 65 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (platform : System.Platform.numBits = 64) (typeValue : Value)
    {element : α → Value → Prop} {source : Array α} {height : Nat} {tree : Tree height} {size : Value}
    (represented : Prefix links.arithmetic.conversions.layout element source height tree size)
    (valid : (Scalar.nat source.size).validate limits = .ok ()) (stack : 3 ≤ limits.continuations)
    (entry : program.entry = links.usize) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes #[typeValue, arrayValue links.layout height tree size].toList = .ok ()) :
    Evaluates limits program #[typeValue, arrayValue links.layout height tree size]
      (cachedValue links.arithmetic.conversions.layout source.usize.toNat) := by
  apply evaluates_of_returns certificate.usize rfl rfl _ rfl (by simp; omega) entry admitted inputs
  exact certificate.usize_source limits room capacity bytesCapacity platform typeValue represented valid #[] (by simpa using stack)

theorem get_evaluates (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (typeValue proofValue : Value)
    {element : α → Value → Prop} {source : Array α} {height : Nat} {tree : Tree height} {size : Value}
    (represented : Prefix links.arithmetic.conversions.layout element source height tree size)
    (index : Nat) (indexValue : Value)
    (indexRep : Number links.arithmetic.conversions.layout index indexValue)
    (bounded : index < source.size) (valid : (Scalar.nat (2 ^ height)).validate limits = .ok ())
    (stack : 4 ≤ limits.continuations)
    (entry : program.entry = links.get) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes #[typeValue, arrayValue links.layout height tree size, indexValue, proofValue].toList = .ok ()) :
    ∃ value, Evaluates limits program #[typeValue, arrayValue links.layout height tree size, indexValue, proofValue] value ∧ element source[index] value := by
  obtain ⟨value, path, related⟩ := certificate.get_source limits room capacity bytesCapacity
    typeValue proofValue represented index indexValue indexRep bounded valid #[] (by simpa using stack)
  exact ⟨value, evaluates_of_returns certificate.get rfl rfl _ rfl (by simp; omega) entry admitted inputs path, related⟩

theorem getBorrowed_evaluates (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (typeValue proofValue : Value)
    {element : α → Value → Prop} {source : Array α} {height : Nat} {tree : Tree height} {size : Value}
    (represented : Prefix links.arithmetic.conversions.layout element source height tree size)
    (index : Nat) (indexValue : Value)
    (indexRep : Number links.arithmetic.conversions.layout index indexValue)
    (bounded : index < source.size) (valid : (Scalar.nat (2 ^ height)).validate limits = .ok ())
    (stack : 4 ≤ limits.continuations)
    (entry : program.entry = links.getBorrowed) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes #[typeValue, arrayValue links.layout height tree size, indexValue, proofValue].toList = .ok ()) :
    ∃ value, Evaluates limits program #[typeValue, arrayValue links.layout height tree size, indexValue, proofValue] value ∧ element source[index] value := by
  obtain ⟨value, path, related⟩ := certificate.getAlias_source limits certificate.getBorrowed room capacity bytesCapacity
    typeValue proofValue represented index indexValue indexRep bounded valid #[] (by simpa using stack)
  exact ⟨value, evaluates_of_returns certificate.getBorrowed rfl rfl _ rfl (by simp; omega) entry admitted inputs path, related⟩

theorem uget_evaluates (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (typeValue proofValue : Value)
    {element : α → Value → Prop} {source : Array α} {height : Nat} {tree : Tree height} {size : Value}
    (represented : Prefix links.arithmetic.conversions.layout element source height tree size)
    (index : USize) (indexValue : Value)
    (indexRep : Number links.arithmetic.conversions.layout index.toNat indexValue)
    (bounded : index.toNat < source.size) (valid : (Scalar.nat (2 ^ height)).validate limits = .ok ())
    (stack : 4 ≤ limits.continuations)
    (entry : program.entry = links.uget) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes #[typeValue, arrayValue links.layout height tree size, indexValue, proofValue].toList = .ok ()) :
    ∃ value, Evaluates limits program #[typeValue, arrayValue links.layout height tree size, indexValue, proofValue] value ∧ element (source.uget index bounded) value := by
  obtain ⟨value, path, related⟩ := certificate.getAlias_source limits certificate.uget room capacity bytesCapacity
    typeValue proofValue represented index.toNat indexValue indexRep bounded valid #[] (by simpa using stack)
  exact ⟨value, evaluates_of_returns certificate.uget rfl rfl _ rfl (by simp; omega) entry admitted inputs path, related⟩

theorem ugetBorrowed_evaluates (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (typeValue proofValue : Value)
    {element : α → Value → Prop} {source : Array α} {height : Nat} {tree : Tree height} {size : Value}
    (represented : Prefix links.arithmetic.conversions.layout element source height tree size)
    (index : USize) (indexValue : Value)
    (indexRep : Number links.arithmetic.conversions.layout index.toNat indexValue)
    (bounded : index.toNat < source.size) (valid : (Scalar.nat (2 ^ height)).validate limits = .ok ())
    (stack : 4 ≤ limits.continuations)
    (entry : program.entry = links.ugetBorrowed) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes #[typeValue, arrayValue links.layout height tree size, indexValue, proofValue].toList = .ok ()) :
    ∃ value, Evaluates limits program #[typeValue, arrayValue links.layout height tree size, indexValue, proofValue] value ∧ element (source.uget index bounded) value := by
  obtain ⟨value, path, related⟩ := certificate.getAlias_source limits certificate.ugetBorrowed room capacity bytesCapacity
    typeValue proofValue represented index.toNat indexValue indexRep bounded valid #[] (by simpa using stack)
  exact ⟨value, evaluates_of_returns certificate.ugetBorrowed rfl rfl _ rfl (by simp; omega) entry admitted inputs path, related⟩

theorem getBang_evaluates [Inhabited α] (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (typeValue defaultValue : Value)
    {element : α → Value → Prop} {source : Array α} {height : Nat} {tree : Tree height} {size : Value}
    (represented : Prefix links.arithmetic.conversions.layout element source height tree size)
    (fallbackRep : element default defaultValue) (index : Nat) (indexValue : Value)
    (indexRep : Number links.arithmetic.conversions.layout index indexValue)
    (valid : (Scalar.nat (2 ^ height)).validate limits = .ok ())
    (indexValid : (Scalar.nat index).validate limits = .ok ()) (stack : 4 ≤ limits.continuations)
    (entry : program.entry = links.getBang) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes #[typeValue, defaultValue, arrayValue links.layout height tree size, indexValue].toList = .ok ()) :
    ∃ value, Evaluates limits program #[typeValue, defaultValue, arrayValue links.layout height tree size, indexValue] value ∧ element (Array.get!Internal source index) value := by
  obtain ⟨value, path, related⟩ := certificate.getBang_source limits certificate.getBang room capacity bytesCapacity
    typeValue defaultValue represented default fallbackRep index indexValue indexRep valid indexValid #[] (by simpa using stack)
  exact ⟨value, evaluates_of_returns certificate.getBang rfl rfl _ rfl (by simp; omega) entry admitted inputs path, related⟩

theorem getBangBorrowed_evaluates [Inhabited α] (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (typeValue defaultValue : Value)
    {element : α → Value → Prop} {source : Array α} {height : Nat} {tree : Tree height} {size : Value}
    (represented : Prefix links.arithmetic.conversions.layout element source height tree size)
    (fallbackRep : element default defaultValue) (index : Nat) (indexValue : Value)
    (indexRep : Number links.arithmetic.conversions.layout index indexValue)
    (valid : (Scalar.nat (2 ^ height)).validate limits = .ok ())
    (indexValid : (Scalar.nat index).validate limits = .ok ()) (stack : 4 ≤ limits.continuations)
    (entry : program.entry = links.getBangBorrowed) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes #[typeValue, defaultValue, arrayValue links.layout height tree size, indexValue].toList = .ok ()) :
    ∃ value, Evaluates limits program #[typeValue, defaultValue, arrayValue links.layout height tree size, indexValue] value ∧ element (Array.get!Internal source index) value := by
  obtain ⟨value, path, related⟩ := certificate.getBang_source limits certificate.getBangBorrowed room capacity bytesCapacity
    typeValue defaultValue represented default fallbackRep index indexValue indexRep valid indexValid #[] (by simpa using stack)
  exact ⟨value, evaluates_of_returns certificate.getBangBorrowed rfl rfl _ rfl (by simp; omega) entry admitted inputs path, related⟩

theorem set_evaluates (room : 12 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (typeValue : Value)
    {element : α → Value → Prop} {source : Array α} {height : Nat} {tree : Tree height} {size : Value}
    (represented : Prefix links.arithmetic.conversions.layout element source height tree size)
    (index : Nat) (indexValue : Value)
    (indexRep : Number links.arithmetic.conversions.layout index indexValue)
    (item : α) (value : Value) (itemRep : element item value)
    (valid : (Scalar.nat (2 ^ height)).validate limits = .ok ())
    (indexValid : (Scalar.nat index).validate limits = .ok ())
    (stack : max 4 (height + 1) ≤ limits.continuations)
    (entry : program.entry = links.set) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes #[typeValue, arrayValue links.layout height tree size, indexValue, value].toList = .ok ()) :
    ∃ result, Evaluates limits program #[typeValue, arrayValue links.layout height tree size, indexValue, value] result ∧
      Represents links.arithmetic.conversions.layout links.layout element (source.set! index item) result := by
  obtain ⟨result, path, related⟩ := certificate.set_source limits room capacity bytesCapacity
    typeValue represented index indexValue indexRep item value itemRep valid indexValid #[] (by simpa using stack)
  exact ⟨result, evaluates_of_returns certificate.set rfl rfl _ rfl (by simp; omega) entry admitted inputs path, related⟩

theorem uset_evaluates (room : 12 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (typeValue proofValue : Value)
    {element : α → Value → Prop} {source : Array α} {height : Nat} {tree : Tree height} {size : Value}
    (represented : Prefix links.arithmetic.conversions.layout element source height tree size)
    (index : USize) (indexValue : Value)
    (indexRep : Number links.arithmetic.conversions.layout index.toNat indexValue)
    (bounded : index.toNat < source.size)
    (item : α) (value : Value) (itemRep : element item value)
    (valid : (Scalar.nat (2 ^ height)).validate limits = .ok ())
    (stack : max 4 (height + 1) ≤ limits.continuations)
    (entry : program.entry = links.uset) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes #[typeValue, arrayValue links.layout height tree size, indexValue, value, proofValue].toList = .ok ()) :
    ∃ result, Evaluates limits program #[typeValue, arrayValue links.layout height tree size, indexValue, value, proofValue] result ∧
      Represents links.arithmetic.conversions.layout links.layout element (source.uset index item bounded) result := by
  obtain ⟨result, path, related⟩ := certificate.uset_source limits room capacity bytesCapacity
    typeValue proofValue represented index indexValue indexRep bounded item value itemRep valid #[] (by simpa using stack)
  exact ⟨result, evaluates_of_returns certificate.uset rfl rfl _ rfl (by simp; omega) entry admitted inputs path, related⟩

theorem push_evaluates (room : 16 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (typeValue : Value)
    {element : α → Value → Prop} {source : Array α} {height : Nat} {tree : Tree height} {size : Value}
    (represented : Prefix links.arithmetic.conversions.layout element source height tree size)
    (item : α) (value : Value) (itemRep : element item value)
    (valid : (Scalar.nat (2 ^ (height + 1))).validate limits = .ok ())
    (stack : max 4 (height + 2) ≤ limits.continuations)
    (entry : program.entry = links.push) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes #[typeValue, arrayValue links.layout height tree size, value].toList = .ok ()) :
    ∃ result, Evaluates limits program #[typeValue, arrayValue links.layout height tree size, value] result ∧
      Represents links.arithmetic.conversions.layout links.layout element (source.push item) result := by
  obtain ⟨result, path, related⟩ := certificate.push_source limits room capacity bytesCapacity
    typeValue represented item value itemRep valid #[] (by simpa using stack)
  exact ⟨result, evaluates_of_returns certificate.push rfl rfl _ rfl (by simp; omega) entry admitted inputs path, related⟩

end Compilatrix.Ixby.Runtime.ArrayTrees.Certificate
