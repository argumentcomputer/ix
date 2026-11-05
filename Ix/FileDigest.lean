module

public import Blake3.Rust

/-! # File digests for tests

The Blake3 digest of a file, for tests that pin or compare an artifact's
bytes: Ix addresses are Blake3, and so are the file digests the tests record.
The file is read in chunks through the streaming hasher (`Blake3.HasherOps`:
`init`, `update`, `finalize`), in process, so no `b3sum` or other external
tool is needed. -/

public section

namespace Ix.FileDigest

/-- Lowercase hexadecimal, two digits per byte. -/
def lowerHex (bytes : ByteArray) : String :=
  let digit (n : UInt8) : Char := "0123456789abcdef".toList[n.toNat]!
  bytes.foldl (fun s b => (s.push (digit (b >>> 4))).push (digit (b &&& 0xf))) ""

/-- The Blake3 digest of the file at `path`, as 64 lowercase hexadecimal
digits, read `chunk` bytes at a time (at least one: a read of zero bytes would
end the loop at once, with the empty input's digest). -/
def blake3File (path : System.FilePath) (chunk : USize := 1048576) : IO String := do
  let handle ← IO.FS.Handle.mk path .read
  let mut hasher := Blake3.HasherOps.init (H := Blake3.Rust.Hasher) ()
  repeat
    let bytes ← handle.read (max chunk 1)
    if bytes.isEmpty then break
    hasher := Blake3.HasherOps.update hasher bytes
  return lowerHex (Blake3.HasherOps.finalize hasher 32).val

#guard lowerHex ⟨#[0xaf, 0x13, 0x09, 0x00]⟩ == "af130900"

end Ix.FileDigest

end
