import IxCK.Kernel.Audit.ClosureManifest
import Ix.Cert.CompileCorrect

/-! # The definitional closure of `Ix.Cert.CompileCorrect`, pinned

Pins the kernel-level definitional closure of the compiler-correctness statement
`Ix.Cert.CompileCorrect`. Every definition, inductive, constructor, recursor, and
referenced statement type that `Ix.Cert.CompileCorrect` unfolds to is canonically
serialized and hashed with SHA-256; theorem proofs are not entered. Any change to the
meaning of `CompileCorrect` or any definition it reaches changes the digest and fails
the build of this module.

Updating it (only with a reviewed change to the statement's meaning): build this module
with `IX_CERT_CLOSURE_MANIFEST_WRITE=Tests/Fixtures/compile-correct-closure-manifest.txt`,
then update `pinnedDigest` below with the reported SHA-256 digest and commit both. -/

namespace Ix.Cert.ClosureManifest

/-- The public compiler-correctness statement root whose definitional closure is pinned. -/
def roots : Array Lean.Name := #[``Ix.Cert.CompileCorrect]

/-- The committed text of the manifest, relative to the repository root. -/
def manifestPath : System.FilePath := "Tests/Fixtures/compile-correct-closure-manifest.txt"

/-- The SHA-256 digest of the manifest's text (its lines, each followed by a newline).
Regenerate with `IX_CERT_CLOSURE_MANIFEST_WRITE=Tests/Fixtures/compile-correct-closure-manifest.txt`. -/
def pinnedDigest : String := "ee0ecc9df3a6345cf7b187687ea952175ec6b6bab62c3d9ae7c79e9d04c76cb6"

open Lean Elab Command in
elab "#check_closure_manifest" : command =>
  Ix.Kernel.Audit.ClosureManifest.checkClosureManifest
    roots manifestPath pinnedDigest "IX_CERT_CLOSURE_MANIFEST_WRITE"

#check_closure_manifest

end Ix.Cert.ClosureManifest
