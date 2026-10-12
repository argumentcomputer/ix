import LSpec
import Ix.CompileM

namespace Tests.Ix.Compile.UniverseCache

open LSpec
open _root_.Ix (Level Name)
open _root_.Ix.CompileM

private def digest : Address := ⟨⟨Array.replicate 32 7⟩⟩
private def u : Name := .str (.anonymous digest) "u" digest
private def v : Name := .str (.anonymous digest) "v" digest

private def run (level : Level) (params : List Name := []) (state : BlockState := {}) :
    Except CompileError Ixon.Univ × BlockState :=
  (compileUniv level (default,
    { all := {}, current := .anonymous digest, mutCtx := {}, univCtx := params })).run state

def controls : List (String × Bool) := Id.run do
  let zero : Level := .zero digest
  let succ : Level := .succ zero digest
  let mvar : Level := .mvar u digest
  let (first, state) := run zero
  let (cold, _) := run succ
  let (warm, after) := run succ [] state
  let (refused, failed) := run mvar [] state
  let (parameter, _) := run (.param v digest) [u, v]
  let (missing, _) := run (.param v digest) [u]
  let realU := Name.fromLeanName `u
  let realV := Name.fromLeanName `v
  let parameterLevel := Level.mkParam realU
  let scopedAction : CompileM (Ixon.Univ × Ixon.Univ) := withUnivCtx [realU, realV] do
    let inner ← withUnivCtx [realV, realU] (compileUniv parameterLevel)
    let outer ← compileUniv parameterLevel
    pure (inner, outer)
  let (scopedResult, _) := (scopedAction (default,
    { all := {}, current := .anonymous digest, mutCtx := {}, univCtx := [] })).run {}
  return [
    ("cold zero and successor retain their shapes",
      first.toOption == some .zero && cold.toOption == some (.succ .zero)),
    ("colliding stored hashes do not alias compiled levels",
      warm.toOption == some (.succ .zero) && after.univCache.size == 2),
    ("colliding metavariables retain the unsupported error",
      (match refused with | .error (.unsupportedExpr "level metavariable") => true | _ => false)
        && failed.univCache.size == 1),
    ("parameter positions use exact names", parameter.toOption == some (.var 1)),
    ("a hash-aliasing absent parameter remains unbound",
      match missing with | .error (.unknownUnivParam ..) => true | _ => false),
    ("leaving a nested parameter context restores the outer meaning",
      scopedResult.toOption == some (.var 1, .var 0))]

def suite : List TestSeq := controls.map fun (label, ok) => test s!"universe cache: {label}" ok

end Tests.Ix.Compile.UniverseCache
