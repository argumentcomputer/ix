/-
  Regression pin for the const/blob classification of a ref that is NOT
  ingressed.

  `augment_with_blob_refs` (`Ix/IxVM/Ingress.lean`) classifies any ref
  absent from the const-position map as a BLOB via the sentinel;
  `build_ref_idxs_and_blobs` emits ref index 0 for it, and `convert_expr`
  turns `Expr.Ref` into `KExprNode.Const(0, levels)`. Absence is therefore
  read as "blob", never as "missing", and the reference rebinds to
  whatever constant occupies kernel position 0.

  `load_verified_blob` is no barrier: it applies the SAME check as
  `load_verified_constant` — blake3 of the served bytes against the
  address — so a constant's own bytes verify on the blob channel.

  These tests drive that path the way an adversarial prover would: flip
  the channel-4 discriminator for one constant to "blob" and serve its
  real serialized bytes on channel 5. Today every such reclassification
  is rejected downstream, because `Const(0)` is type-incompatible — an
  incidental defence, not an explicit check that a ref resolves to the
  constant it names. This suite pins that rejection so a change which
  starts ACCEPTING an erased constant fails loudly.

  It also pins the reason: the corrupted-bytes control must fail
  DIFFERENTLY from the real-bytes case. If both failed alike, the blob
  channel would be rejecting the bytes outright and these tests would no
  longer be exercising the rebinding they claim to cover.

  Run with: `lake test -- ixvm --ignored`
-/
import Ix.Meta
import Ix.Aiur.Protocol
import Ix.Aiur.Compiler
import Ix.IxVM
import Ix.IxVM.ClaimHarness
import Ix.Claim
import Ix.Ixon
import LSpec

open LSpec
open IxVM.ClaimHarness

namespace Tests.Ix.Kernel.BlobRefAudit

/-- Reclassify `victim` as a blob: flip its channel-4 discriminator to 0
    and serve `bytes` on the blob channel. Channels 2/4/5 share the
    address as key and `IOBuffer.extend` overwrites a key's slot, so this
    replaces the honest classification rather than adding to it. -/
private def reclassifyAsBlob (victim : Address) (bytes : Array Aiur.G)
    (io : Aiur.IOBuffer) : Aiur.IOBuffer :=
  let key : Array Aiur.G := victim.hash.data.map .ofUInt8
  (io.extend 4 key #[.ofNat 0]).extend 5 key bytes

/-- Run `verify_claim` and report the error message, if any. -/
private def runClaim (compiled : Aiur.CompiledToplevel)
    (funIdx : Aiur.Bytecode.FunIdx) (input : Array Aiur.G)
    (io : Aiur.IOBuffer) : Option String :=
  match compiled.bytecode.execute funIdx input io with
  | .error e => some e
  | .ok _ => none

def blobRefAuditTests (env : Lean.Environment)
    (compiled : Aiur.CompiledToplevel) : IO TestSeq := do
  let targetName := `Nat.add
  let ixonEnv ← loadIxonEnv targetName env
  let target ← lookupAddr ixonEnv targetName
  let witness ← IO.ofExcept <| buildClaimWitness ixonEnv (Ix.Claim.check target none)
  let funIdx ← match compiled.getFuncIdx witness.funcName with
    | some i => pure i
    | none => throw <| IO.userError "verify_claim entrypoint missing"
  let io := witness.inputIOBuffer

  let mut tests : TestSeq :=
    test "honest witness checks" (runClaim compiled funIdx witness.input io).isNone
  let mut reachedRebinding := 0

  -- Every closure member other than the target is referenced by something
  -- in the closure, so erasing it exercises a real `Expr.Ref` rebinding.
  for victim in (closureFrom ixonEnv target).toArray do
    if victim == target then continue
    match ixonEnv.consts[victim]? with
    | none => pure ()
    | some lc =>
      let real := lc.rawBytes.data.map fun b => Aiur.G.ofNat b.toNat
      let corrupted := lc.rawBytes.data.map fun b => Aiur.G.ofNat (b.toNat ^^^ 0xFF)
      let realErr := runClaim compiled funIdx witness.input
        (reclassifyAsBlob victim real io)
      let badErr := runClaim compiled funIdx witness.input
        (reclassifyAsBlob victim corrupted io)
      -- Distinct failures ⇒ the real bytes cleared `load_verified_blob`
      -- and reached the rebinding, while the corrupted ones died at the
      -- hash comparison. Not every constant gets that far: some fail
      -- earlier, before the blob channel is consulted at all.
      if realErr != badErr then reachedRebinding := reachedRebinding + 1
      tests := tests
        ++ test s!"erasing {victim} is rejected" realErr.isSome
        ++ test s!"erasing {victim} with non-matching bytes is rejected"
             badErr.isSome
  -- The suite is only meaningful while the rebinding path is reachable:
  -- if no victim clears blob verification, these tests have stopped
  -- covering what they document and the pin above proves nothing.
  pure (tests ++ test
    s!"blob verification accepts a constant's own bytes ({reachedRebinding} victims)"
    (reachedRebinding > 0))

end Tests.Ix.Kernel.BlobRefAudit
