module

public import LSpec
public import Ix.Ixon
public import Ix.CompileM
public import Ix.Meta
public import Ix.Common

/-!
Real-corpus gate for the Lean↔Rust Ixon sync (`ixon-corpus`, ignored).

The generator-driven properties (`Tests.Ixon.suite`) cover the wire grammar
compositionally; this suite covers whatever hand-written generators miss,
because its input is the production Rust compiler's real output over the
ENTIRE current Lean environment — including call-site surgery, extension
tables, aux layouts, `original` metadata, and every §-section interaction.

Gate:
1. Rust-compile the whole `get_env!` to `.ixe` bytes.
2. The pure-Lean parser (`Ixon.deEnv`) must parse them — every metadata
   variant, no lossy skips.
3. The pure-Lean writer (`Ixon.serEnv`) must reproduce the input bytes
   EXACTLY (writers are canonical: section sort orders, name topological
   order, index assignment, and metadata encoding all agree).
4. The Rust FFI value path (`Ixon.rsDeEnv`) must agree with the pure parse
   (content comparison per section).
-/

namespace Tests.Ixon.Corpus

open LSpec

public section

/-- Content comparison between two parsed envs (no BEq instance on `Env` —
    HashMaps compare per-key). Returns the first difference found. -/
def envContentDiff (a b : Ixon.Env) : Option String := Id.run do
  if a.consts.size != b.consts.size then
    return some s!"consts size {a.consts.size} vs {b.consts.size}"
  for (addr, lc) in a.consts do
    match b.consts.get? addr with
    | none => return some s!"const {addr} missing"
    | some lc' =>
      if lc.rawBytes != lc'.rawBytes then
        return some s!"const {addr} bytes differ"
  if a.named.size != b.named.size then
    return some s!"named size {a.named.size} vs {b.named.size}"
  for (name, n) in a.named do
    match b.named.get? name with
    | none => return some s!"named {name} missing"
    | some n' =>
      if n != n' then
        let field :=
          if n.addr != n'.addr then s!"addr {n.addr} vs {n'.addr}"
          else if n.hints != n'.hints then
            s!"hints {reprStr n.hints} vs {reprStr n'.hints}"
          else if n.constMeta != n'.constMeta then
            let cm := n.constMeta
            let cm' := n'.constMeta
            if cm.info != cm'.info then
              s!"constMeta.info:\n  pure: {(reprStr cm.info).take 400}\n  ffi:  {(reprStr cm'.info).take 400}"
            else
              s!"constMeta ext tables: sharing {cm.metaSharing.size}/{cm'.metaSharing.size} refs {cm.metaRefs.size}/{cm'.metaRefs.size} univs {cm.metaUnivs.size}/{cm'.metaUnivs.size}"
          else
            s!"original:\n  pure: {(reprStr n.original).take 400}\n  ffi:  {(reprStr n'.original).take 400}"
        return some s!"named {name} differs — {field}"
  if a.blobs.size != b.blobs.size then
    return some s!"blobs size {a.blobs.size} vs {b.blobs.size}"
  for (addr, bytes) in a.blobs do
    if b.blobs.get? addr != some bytes then
      return some s!"blob {addr} differs"
  if a.names.size != b.names.size then
    return some s!"names size {a.names.size} vs {b.names.size}"
  for (addr, name) in a.names do
    if b.names.get? addr != some name then
      return some s!"name {addr} differs"
  if a.comms.size != b.comms.size then
    return some s!"comms size {a.comms.size} vs {b.comms.size}"
  if a.main != b.main then
    return some s!"main differs"
  if a.assumptions.size != b.assumptions.size then
    return some "assumptions differ"
  if a.anonHints.size != b.anonHints.size then
    return some s!"anonHints size {a.anonHints.size} vs {b.anonHints.size}"
  for (addr, h) in a.anonHints do
    if b.anonHints.get? addr != some h then
      return some s!"anonHints {addr} differs"
  return none

/-- Compile the whole current env through the Rust compiler and return the
    `.ixe` bytes. -/
def compileWholeEnvBytes (leanEnv : Lean.Environment) : IO ByteArray := do
  let dir ← IO.FS.createTempDir
  let path := dir / "ixon-corpus.ixe"
  let _ ← Ix.CompileM.rsCompileEnvBytesFFI leanEnv.constants.toList path.toString
  let bytes ← IO.FS.readBinFile path
  IO.FS.removeDirAll dir
  return bytes

def corpusSuite : TestSeq :=
  .individualIO "pure deEnv/serEnv roundtrip whole Rust-compiled env" none (do
    let leanEnv ← get_env!
    let bytes ← compileWholeEnvBytes leanEnv
    -- 2. Pure parse.
    match Ixon.deEnv bytes with
    | .error e => return (false, 0, 0, some s!"pure deEnv failed: {e}")
    | .ok env => do
      -- 3. Byte-exact pure re-serialization.
      match Ixon.serEnv env with
      | .error e => return (false, 0, 0, some s!"pure serEnv failed: {e}")
      | .ok bytes' =>
        if bytes' != bytes then
          return (false, env.consts.size, 0,
            some s!"serEnv bytes differ: {bytes'.size} vs {bytes.size}")
        -- 4. FFI value path agrees with the pure parse.
        match Ixon.rsDeEnv bytes with
        | .error e => return (false, 0, 0, some s!"rsDeEnv failed: {e}")
        | .ok rsEnv =>
          match envContentDiff env rsEnv with
          | some d => return (false, env.consts.size, 0,
              some s!"pure vs FFI parse disagree: {d}")
          | none => return (true, env.consts.size, 0, none)) .done

public def suite : List TestSeq := [corpusSuite]

end

end Tests.Ixon.Corpus
