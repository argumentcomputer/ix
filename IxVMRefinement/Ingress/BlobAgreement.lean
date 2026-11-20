import IxVMRefinement.Ingress.ConvertExpr
import IxVMRefinement.Core.Good

/-! # Agreement at successful literal reads

The raw conversion trace identifies bytes it hashed. A successful reader lookup supplies the
bytes it used. Conditional equality is sufficient for conversion and does not require unrelated
hash inputs to be present in the reader blob store.
-/

namespace IxVM.Refinement.Ingress

open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

/-- Hashed bytes agree at every successful reader blob lookup of the same address. -/
def HashedBlobReadAgreement (blob : _root_.Address → Option ByteArray)
    (calls : List (Call F)) : Prop :=
  ∀ address observed, Hashed calls observed → Address.blake3Pure observed = address →
    ∀ declared, blob address = some declared → observed = declared

/-- A concrete raw blob list inherits agreement from the enclosing actual trace. -/
theorem HashedBlobReadAgreement.of_pairs {blob : _root_.Address → Option ByteArray}
    {calls : List (Call F)} {blobs : List (_root_.Address × ByteArray)}
    (agreement : HashedBlobReadAgreement blob calls) (hashed : HashedPairs calls blobs) :
    BlobReadAgreement blob blobs := by
  intro address observed member declared found
  exact agreement address observed (hashed (address, observed) member).1
    (hashed (address, observed) member).2 declared found

/-- Agreement passes to the actual child calls selected by a scoped proof. -/
theorem HashedBlobReadAgreement.sub {blob : _root_.Address → Option ByteArray}
    {calls childCalls : List (Call F)} (agreement : HashedBlobReadAgreement blob calls)
    (subset : ∀ call ∈ childCalls, call ∈ calls) : HashedBlobReadAgreement blob childCalls := by
  intro address observed hashed hashEq declared found
  exact agreement address observed (Core.hashed_mono subset hashed) hashEq declared found

/-- Compatibility with the stronger assumption that all hashed payloads are stored as blobs. -/
theorem HashedBlobReadAgreement.of_stored {blob : _root_.Address → Option ByteArray}
    {calls : List (Call F)}
    (stored : ∀ address bytes, Hashed calls bytes → Address.blake3Pure bytes = address →
      blob address = some bytes) : HashedBlobReadAgreement blob calls := by
  intro address observed hashed hashEq declared found
  exact Option.some.inj ((stored address observed hashed hashEq).symm.trans found)

end IxVM.Refinement.Ingress
