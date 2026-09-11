/-! Reviewed native inputs for the compiler component. Changes to these values
require review of the corresponding implementation, symbols, and proof boundary.
See `docs/compiler/trusted-extern-ledger.md` for assumptions and scope. -/

namespace Ix.Compiler.Tools.TrustProfile

structure Profile where
  leanVersion : String
  blakeRevision : String
  blakeUpstreamRevision : String
  blakeVersion : String
  leanFfiRevision : String
  cargoSha256 : String
  durableSha256 : String
  lakeSectionSha256 : String
  deriving Repr

def reviewed : Profile := {
  leanVersion := "leanprover/lean4:v4.33.1"
  blakeRevision := "78f5bc4b22de1172af8a5d91e7039128084fad3a"
  blakeUpstreamRevision := "f3149ec5bb5449af877ba20377a11008ff499fa2"
  blakeVersion := "1.8.7"
  leanFfiRevision := "93c7e52952ae94546be08313f4ff3922984c84d5"
  cargoSha256 := "4ebb14071ab64d7913f299e243630b4b4f8aebd55db1a68d3b8a7ce1251778ea"
  durableSha256 := "f44c087cf80b2f5499ac1e25c0bb63be0f1e0687bc49a941c6b0ace8b03248f5"
  lakeSectionSha256 := "9a38d159118f4736947238d1fb0656f2af7c6e4a7bab28644ad73aec64a6c781"
}

def projectSymbols : List (String × String × String) := [
  ("Ix.Compiler.DurableSync", "Ix.Compiler.DurableSync.file", "compilatrix_durable_sync_file"),
  ("Ix.Compiler.DurableSync", "Ix.Compiler.DurableSync.directory", "compilatrix_durable_sync_directory")]

def dependencySymbols : List (String × String × String) :=
  [ ("Blake3.Rust", "rs_blake3"), ("Blake3.C", "c_blake3") ].flatMap fun (mod, symbolPrefix) =>
    [("internalVersion", "version"), ("hasherInit", "init"),
      ("hasherInitKeyed", "init_keyed"), ("hasherInitDeriveKey", "init_derive_key"),
      ("hasherUpdate", "hasher_update"), ("hasherFinalize", "hasher_finalize")].map
      fun (name, suffix) => (mod, mod ++ "." ++ name, symbolPrefix ++ "_" ++ suffix)

def entrypoints : List (String × List String) := [
  ("Blake3.Rust", ["Blake3.Rust.hash"]),
  ("Blake3.C", []),
  ("Ix.Compiler.DurableSync", ["Ix.Compiler.DurableSync.file", "Ix.Compiler.DurableSync.directory"])]

end Ix.Compiler.Tools.TrustProfile
