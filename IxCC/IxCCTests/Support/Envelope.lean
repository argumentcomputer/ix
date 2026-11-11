import IxCC.Ixon.V3.Env

/-! # Writing `.ixe` envelopes in tests

The two envelopes ix writes (`IxCC/docs/byte-contract.md`), from a decoded
environment, and the unbound twin of a committed role-bound closure: every
committed closure is role-bound, and the suites that exercise the unbound
envelope, or compare the two, write it from the same records. -/

namespace IxCCTests.Support.Envelope

open IxCC.Ixon IxCC.Ixon.V3

/-- `env` in the envelope ix writes: role-bound, with `binding`'s address,
length and bytes after the assumptions, when it is given; with the root
recomputed from the constants. -/
def envelope (env : Env) (binding : Option (IxCC.Ixon.Address × ByteArray)) : ByteArray :=
  _root_.Ixon.runPut do
    let constants := env.consts.toArray.qsort (fun a b => Merkle.addressLT a.1 b.1)
    let blobs := env.blobs.toArray.qsort (fun a b => Merkle.addressLT a.1 b.1)
    _root_.Ixon.putTagN 4 0xE (if binding.isSome then boundEnvVersion else envVersion)
    _root_.Ixon.putBytes (Merkle.rootCanonicalBy IxCC.Ixon.Address.blake3Pure (constants.map Prod.fst)).hash
    match env.main with
    | none => _root_.Ixon.putU8 0
    | some a => _root_.Ixon.putU8 1; _root_.Ixon.putBytes a.hash
    _root_.Ixon.putTagN 0 0 env.assumptions.size.toUInt64
    for a in env.assumptions do _root_.Ixon.putBytes a.hash
    if let some (address, bytes) := binding then
      _root_.Ixon.putBytes address.hash
      _root_.Ixon.putTagN 0 0 bytes.size.toUInt64
      _root_.Ixon.putBytes bytes
    for table in #[blobs, constants] do
      _root_.Ixon.putTagN 0 0 table.size.toUInt64
      for (address, raw) in table do
        _root_.Ixon.putBytes address.hash
        _root_.Ixon.putTagN 0 0 raw.size.toUInt64
        _root_.Ixon.putBytes raw
    let hints := env.hints.qsort (fun a b => Merkle.addressLT a.1 b.1)
    _root_.Ixon.putTagN 0 0 hints.size.toUInt64
    let mut cursor := 0
    for (address, hint) in hints do
      let index := (constants.findIdx? (·.1 == address)).getD 0
      _root_.Ixon.putTagN 0 0 (index + 1 - cursor).toUInt64
      _root_.Ixon.putTagN 0 0 hint
      cursor := index + 1
    _root_.Ixon.putBytes env.metadata

/-- The unbound envelope of a committed role-bound closure: the same records,
blobs, hints and metadata, without the binding (every committed closure is
role-bound; the unbound envelope is still read, with the fixed pins). -/
def unboundTwin (path : System.FilePath) : IO ByteArray := do
  let env ← IO.ofExcept (decodeAnonymousEnv (← IO.FS.readBinFile path))
  unless env.isBound do throw (IO.userError s!"role binding: {path} is not role-bound")
  return envelope env none

end IxCCTests.Support.Envelope
