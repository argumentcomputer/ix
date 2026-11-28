import IxCK.Kernel.Audit.ClosureManifest
import IxCK.Kernel.Admission.Theorems
import IxCK.Kernel.Admission.TierTheorems
import IxCK.Kernel.Admission.UserAxioms

/-! # The definitional closure of the certified Ixon entry, pinned

Pins the kernel-level definitional closure of the public certified admission statements:
* `Ix.Kernel.Admission.checkBytes_has_model`
* `Ix.Kernel.Admission.checkBytes_consts`
* `Ix.Kernel.Admission.checkBytesTiered_has_model`
* `Ix.Kernel.Admission.checkBytesUnder_strict_of_nil`

A change to any definition, inductive, constructor, recursor, or statement type reachable
from these theorems changes the SHA-256 digest and fails the build of this module.

Updating it (only with a reviewed change to the statements' meaning): build this module
with `IXC_CLOSURE_MANIFEST_WRITE=Tests/Fixtures/check-bytes-closure-manifest.txt`, then
update `pinnedDigest` below with the reported SHA-256 digest and commit both. -/

namespace Ix.Kernel.Admission.ClosureManifest

/-- The public admission theorem roots whose definitional closure is pinned. -/
def roots : Array Lean.Name := #[
  ``Ix.Kernel.Admission.checkBytes_has_model,
  ``Ix.Kernel.Admission.checkBytes_consts,
  ``Ix.Kernel.Admission.checkBytesTiered_has_model,
  ``Ix.Kernel.Admission.checkBytesUnder_strict_of_nil]

/-- The committed text of the manifest, relative to the repository root. -/
def manifestPath : System.FilePath := "Tests/Fixtures/check-bytes-closure-manifest.txt"

/-- The SHA-256 digest of the manifest's text (its lines, each followed by a newline).
Regenerate with `IXC_CLOSURE_MANIFEST_WRITE=Tests/Fixtures/check-bytes-closure-manifest.txt`. -/
def pinnedDigest : String := "2118cc66b1a33756f9f56074e9b15166980ee04221d35f934798a1138f0741bc"

open Lean Elab Command in
elab "#check_closure_manifest" : command =>
  Ix.Kernel.Audit.ClosureManifest.checkClosureManifest
    roots manifestPath pinnedDigest "IXC_CLOSURE_MANIFEST_WRITE"

#check_closure_manifest

end Ix.Kernel.Admission.ClosureManifest
