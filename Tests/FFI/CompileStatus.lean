/-
  `rs_compile_env` structured-status tests: the fail-closed default
  writes nothing when a requested constant is ungrounded, while
  allow-partial serializes the grounded subset as a reloadable artifact
  and the status enumerates exactly the missing names.
-/
module

public import LSpec
public import Ix.CompileM
public import Ix.Ixon

public section

open LSpec

namespace Tests.FFI.CompileStatus

private def goodName : Lean.Name := `TestsCompileStatus.good
private def badName : Lean.Name := `TestsCompileStatus.bad

private def goodAx : Lean.ConstantInfo := .axiomInfo {
  name := goodName, levelParams := [], type := .sort .zero
  isUnsafe := false }

/-- References a constant absent from the env, so grounding rejects its
    block and it lands in `CompileState.ungrounded`. -/
private def badAx : Lean.ConstantInfo := .axiomInfo {
  name := badName, levelParams := []
  type := .const `TestsCompileStatus.doesNotExist []
  isUnsafe := false }

private def consts : List (Lean.Name × Lean.ConstantInfo) :=
  [(goodName, goodAx), (badName, badAx)]

def failClosedTest : TestSeq :=
  .individualIO "rs_compile_env fail-closed: ungrounded ⇒ no artifact" none (do
    let dir ← IO.FS.createTempDir
    let out := dir / "fail-closed.ixe"
    let status ← Ix.CompileM.rsCompileEnvBytesFFI consts out.toString false
    let outExists ← out.pathExists
    let tmpExists ← (dir / "fail-closed.ixe.tmp").pathExists
    IO.FS.removeDirAll dir
    let checks : List (String × Bool) :=
      [ ("no output file", !outExists)
      , ("no .tmp left behind", !tmpExists)
      , ("bytes == 0", status.bytes == 0)
      , ("one ungrounded entry", status.ungrounded.size == 1)
      , ("ungrounded names the bad axiom",
          status.ungrounded[0]?.map (·.1) == some badName.toString)
      , ("root is 64 hex chars", status.root.length == 64) ]
    match checks.find? (!·.2) with
    | some (what, _) => return (false, 0, 0, some s!"failed: {what}")
    | none => return (true, 0, 0, none)
  ) .done

def allowPartialTest : TestSeq :=
  .individualIO "rs_compile_env allow-partial: grounded subset reloads" none (do
    let dir ← IO.FS.createTempDir
    let out := dir / "partial.ixe"
    let status ← Ix.CompileM.rsCompileEnvBytesFFI consts out.toString true
    let bytes ← IO.FS.readBinFile out
    IO.FS.removeDirAll dir
    let env ← match Ixon.deEnv bytes with
      | .ok env => pure env
      | .error e => return (false, 0, 0, some s!"reload failed: {e}")
    let checks : List (String × Bool) :=
      [ ("bytes matches file size", status.bytes.toNat == bytes.size)
      , ("one ungrounded entry", status.ungrounded.size == 1)
      , ("grounded axiom is named in the reloaded env",
          env.named.size == status.named.toNat && status.named ≥ 1)
      , ("bad axiom is absent from the reloaded env",
          env.named.size < consts.length + 1) ]
    match checks.find? (!·.2) with
    | some (what, _) => return (false, 0, 0, some s!"failed: {what}")
    | none => return (true, 0, 0, none)
  ) .done

def suite : List TestSeq := [failClosedTest, allowPartialTest]

end Tests.FFI.CompileStatus
