import Compilatrix.Ixby.Runtime.ToWord
import Compilatrix.Ixby.Runtime.FromWord

namespace Compilatrix.Ixby.Runtime.Conversion

open Ix.Ixby Execution Representation ScalarFunction

structure Links where
  toWord : FunctionId
  fromWordLoop : FunctionId
  fromWord : FunctionId
  fromRaw : FunctionId
  lowWord : FunctionId
  natural : FunctionId
  fieldNatural : FunctionId
  asField : FunctionId
  fieldFromNatural : FunctionId
  nibbleWord : FunctionId
  nibbleNat : FunctionId
  cachedCtor : Constructor
  rawCtor : Constructor
  fieldCtor : Constructor
  layout : NumberLayout

/-- Exact function and constructor evidence for all eleven number conversion
helpers. Distinct tags are checked explicitly before constructor dispatch is
used in the local execution contracts. -/
structure Certificate (program : Program) (links : Links) : Type where
  toWord : Checked program links.toWord (Conversion.toWord links.toWord links.nibbleWord)
  fromWordLoop : Checked program links.fromWordLoop
    (Conversion.fromWordLoop links.fromWordLoop links.nibbleNat)
  fromWord : Checked program links.fromWord (Conversion.fromWord links.fromWordLoop links.cachedCtor)
  fromRaw : Checked program links.fromRaw (Conversion.fromRaw links.rawCtor)
  lowWord : Checked program links.lowWord
    (Conversion.lowWord links.toWord links.cachedCtor links.rawCtor links.fieldCtor)
  natural : Checked program links.natural
    (Conversion.natural links.fieldNatural links.cachedCtor links.rawCtor links.fieldCtor)
  fieldNatural : Checked program links.fieldNatural (Conversion.fieldNatural links.fromWordLoop)
  asField : Checked program links.asField
    (Conversion.asField links.fieldFromNatural links.cachedCtor links.rawCtor links.fieldCtor)
  fieldFromNatural : Checked program links.fieldFromNatural (Conversion.fieldFromNatural links.toWord)
  nibbleWord : Checked program links.nibbleWord (nibble true)
  nibbleNat : Checked program links.nibbleNat (nibble false)
  cached : program.getConstructor links.cachedCtor = .ok ⟨links.layout.cached, 2⟩
  raw : program.getConstructor links.rawCtor = .ok ⟨links.layout.raw, 1⟩
  field : program.getConstructor links.fieldCtor = .ok ⟨links.layout.field, 1⟩
  cachedRaw : (links.layout.cached == links.layout.raw) = false
  cachedField : (links.layout.cached == links.layout.field) = false
  rawField : (links.layout.raw == links.layout.field) = false

private structure ConstructorChecked (program : Program) (index : Constructor) (expected : CtorDecl) : Type where
  code : program.getConstructor index = .ok expected

private def checkConstructor (program : Program) (index : Constructor) (expected : CtorDecl) :
    Except String (ConstructorChecked program index expected) := do
  match found : program.getConstructor index with
  | .error _ => throw s!"missing conversion constructor {index}"
  | .ok actual =>
    if same : actual = expected then return ⟨same ▸ found⟩
    else throw s!"conversion constructor differs: {index}"

def certify (program : Program) (links : Links) : Except String (Certificate program links) := do
  let toWord ← check program links.toWord (Conversion.toWord links.toWord links.nibbleWord)
  let fromWordLoop ← check program links.fromWordLoop
    (Conversion.fromWordLoop links.fromWordLoop links.nibbleNat)
  let fromWord ← check program links.fromWord (Conversion.fromWord links.fromWordLoop links.cachedCtor)
  let fromRaw ← check program links.fromRaw (Conversion.fromRaw links.rawCtor)
  let lowWord ← check program links.lowWord
    (Conversion.lowWord links.toWord links.cachedCtor links.rawCtor links.fieldCtor)
  let natural ← check program links.natural
    (Conversion.natural links.fieldNatural links.cachedCtor links.rawCtor links.fieldCtor)
  let fieldNatural ← check program links.fieldNatural (Conversion.fieldNatural links.fromWordLoop)
  let asField ← check program links.asField
    (Conversion.asField links.fieldFromNatural links.cachedCtor links.rawCtor links.fieldCtor)
  let fieldFromNatural ← check program links.fieldFromNatural (Conversion.fieldFromNatural links.toWord)
  let nibbleWord ← check program links.nibbleWord (nibble true)
  let nibbleNat ← check program links.nibbleNat (nibble false)
  let cached ← checkConstructor program links.cachedCtor ⟨links.layout.cached, 2⟩
  let raw ← checkConstructor program links.rawCtor ⟨links.layout.raw, 1⟩
  let field ← checkConstructor program links.fieldCtor ⟨links.layout.field, 1⟩
  if cachedRaw : (links.layout.cached == links.layout.raw) = false then
    if cachedField : (links.layout.cached == links.layout.field) = false then
      if rawField : (links.layout.raw == links.layout.field) = false then
        return {
          toWord := toWord
          fromWordLoop := fromWordLoop
          fromWord := fromWord
          fromRaw := fromRaw
          lowWord := lowWord
          natural := natural
          fieldNatural := fieldNatural
          asField := asField
          fieldFromNatural := fieldFromNatural
          nibbleWord := nibbleWord
          nibbleNat := nibbleNat
          cached := cached.code
          raw := raw.code
          field := field.code
          cachedRaw := cachedRaw
          cachedField := cachedField
          rawField := rawField }
      else throw "conversion raw and field tags coincide"
    else throw "conversion cached and field tags coincide"
  else throw "conversion cached and raw tags coincide"

namespace Certificate

variable {program : Program} {links : Links} (certificate : Certificate program links)
  (limits : Limits)

include certificate

-- Keep the existing caller-facing sufficient bounds; the direct execution
-- theorem needs only six locals and validation of the source Nat.
theorem toWord_returns (room : 11 ≤ limits.locals) (_capacity : 5 ≤ limits.natBits)
    (n : Nat) (valid : (Scalar.nat n).validate limits = .ok ())
    (continuation : Array Continuation) (_stack : continuation.size < limits.continuations) :
    Reaches limits program
      (frameState links.toWord 0 #[.scalar (.nat n), .scalar (.word32 1), .scalar (.word32 0)]
        continuation)
      (returned (.scalar (.word32 n.toUInt32)) continuation) := by
  simpa using Conversion.toWord_returns certificate.toWord
    limits (by omega) n 1 0 valid continuation

theorem fromWordLoop_returns (room : 10 ≤ limits.locals) (capacity : 32 ≤ limits.natBits)
    (word : UInt32) (continuation : Array Continuation)
    (_stack : continuation.size < limits.continuations) :
    Reaches limits program
      (frameState links.fromWordLoop 0
        #[.scalar (.word32 word), .scalar (.nat 1), .scalar (.nat 0)] continuation)
      (returned (.scalar (.nat word.toNat)) continuation) := by
  have resultValid : (Scalar.nat (0 + word.toNat * 1)).validate limits = .ok () := by
    simpa using validate_nat_of_bits word.toNat_lt (show 32 ≤ limits.natBits by omega)
  have wordValid := validate_nat_of_bits word.toNat_lt capacity
  have weightValid := validate_nat_of_bits (by decide : 1 < 2 ^ 32) capacity
  simpa using Conversion.fromWordLoop_returns certificate.fromWordLoop
    limits (by omega) word 1 0 wordValid weightValid resultValid continuation

theorem fromRaw_returns (room : 2 ≤ limits.locals) (n : Nat)
    (continuation : Array Continuation) :
    Reaches limits program (frameState links.fromRaw 0 #[.scalar (.nat n)] continuation)
      (returned (.ctor links.layout.raw #[.scalar (.nat n)]) continuation) := by
  have localRoom : ∀ k, k ≤ 2 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 2) (count := 0)
  iterate 2
    rw [runChunk]
    simp [step, stepEval, Frame.check, certificate.fromRaw.code, Conversion.fromRaw,
      certificate.raw, frameState, returned, evalOp, Frame.readOperands, Frame.read,
      Frame.transfer, localRoom, bind, Except.bind, pure, Except.pure]
  rfl

theorem fromWord_returns (room : 10 ≤ limits.locals) (capacity : 32 ≤ limits.natBits)
    (word : UInt32) (continuation : Array Continuation)
    (stack : continuation.size + 2 ≤ limits.continuations) :
    Reaches limits program (frameState links.fromWord 0 #[.scalar (.word32 word)] continuation)
      (returned (.ctor links.layout.cached
        #[.scalar (.nat word.toNat), .scalar (.word32 word)]) continuation) := by
  have localRoom : ∀ k, k ≤ 10 → ¬limits.locals < k := by omega
  let saved : Frame := { function := links.fromWord, block := 1, locals := #[.scalar (.word32 word)] }
  have beforeCall : Reaches limits program
      (frameState links.fromWord 0 #[.scalar (.word32 word)] continuation)
      (frameState links.fromWordLoop 0
        #[.scalar (.word32 word), .scalar (.nat 1), .scalar (.nat 0)]
        (continuation.push (.resume saved))) := by
    apply reaches_of_chunk (fuel := 1) (count := 0)
    rw [runChunk]
    simp [step, stepEval, Frame.check, certificate.fromWord.code, certificate.fromWordLoop.code,
      Conversion.fromWord, Conversion.fromWordLoop, frameState, saved, evalOp,
      Frame.readOperands, Frame.read, State.push, enter, N,
      localRoom, show ¬continuation.size ≥ limits.continuations by omega,
      bind, Except.bind, pure, Except.pure]
    rfl
  have loopPath := certificate.fromWordLoop_returns limits room capacity word
    (continuation.push (.resume saved)) (by simp; omega)
  have resumed : Reaches limits program
      (returned (.scalar (.nat word.toNat)) (continuation.push (.resume saved)))
      (frameState links.fromWord 1 #[.scalar (.word32 word), .scalar (.nat word.toNat)]
        continuation) := by
    apply Execution.resume
    simp [Frame.transfer, Frame.check, certificate.fromWord.code, Conversion.fromWord,
      saved, localRoom, bind, Except.bind, pure, Except.pure]
  have suffix : Reaches limits program
      (frameState links.fromWord 1 #[.scalar (.word32 word), .scalar (.nat word.toNat)] continuation)
      (returned (.ctor links.layout.cached
        #[.scalar (.nat word.toNat), .scalar (.word32 word)]) continuation) := by
    apply reaches_of_chunk (fuel := 2) (count := 0)
    iterate 2
      rw [runChunk]
      simp [step, stepEval, Frame.check, certificate.fromWord.code, Conversion.fromWord,
        certificate.cached, frameState, returned, evalOp, Frame.readOperands, Frame.read,
        Frame.transfer, localRoom, bind, Except.bind, pure, Except.pure]
    rfl
  exact beforeCall.trans (loopPath.trans (resumed.trans suffix))

end Certificate

end Compilatrix.Ixby.Runtime.Conversion
