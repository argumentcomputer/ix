import LSpec
import Ix.Compile.Pass.Driver

namespace Tests.Ix.Compile.HeadLookup

open LSpec
open _root_.Ix (Name Expr)
open _root_.Ix.Compile.Pass

/-- Synthetic cached-name controls; these do not claim a cryptographic
collision or a kernel-checked Lean environment with corrupt caches. -/
def controls : List (String × Bool) := Id.run do
  let owner := Name.fromLeanName `HeadLookupControl.Owner
  let original := owner.mkStr "below"
  let forgedOwner := Name.str Name.mkAnon "OtherOwner" owner.getHash
  let forged := Name.str forgedOwner "below" original.getHash
  let heads := ({} : Std.HashMap Name Name).insert original owner
  let type := Expr.mkForallE Name.mkAnon (Expr.mkSort .mkZero)
    (Expr.mkForallE Name.mkAnon (Expr.mkSort .mkZero) (Expr.mkSort .mkZero) .default) .default
  let declaration : _root_.Ix.ConstantInfo := .defnInfo {
    cnst := { name := original, levelParams := #[], type }
    value := Expr.mkSort .mkZero, safety := .safe, hints := .abbrev, all := #[original] }
  let env : _root_.Ix.Environment := { consts := ({} : Std.HashMap _ _).insert original declaration }
  let recName := owner.mkStr "rec"
  let ixRoot := owner.mkStr "_ix"
  let shape : Opt.RecShape := {
    leanRec := recName, levelParams := #[], np := 0, nm := 1, nmin := 0, ni := 0
    ixRec := ixRoot.mkStr "rec", ixLevels := #[], motiveSrc := #[0]
    minorSrc := #[], minorTerms := #[] }
  let block : Opt.OptBlock := {
    all := #[owner], change := default
    classOf := ({} : Std.HashMap _ _).insert owner #[owner]
    shapes := ({} : Std.HashMap _ _).insert recName shape }
  let blocks := ({} : Std.HashMap _ _).insert owner block
  let addresses := ({} : Std.HashMap Name Address).insert (ixRoot.mkStr "below") original.getHash
  let cenv : _root_.Ix.CompileM.CompileEnv := {
    (default : _root_.Ix.CompileM.CompileEnv) with
    env, nameToAddr := addresses, p3Heads := heads, pass3 := true }
  let oldEnv : Opt.OptEnv := {
    ienv := env, resolves := addresses.contains
    blockOf := fun n => (heads.get? n).bind blocks.get? }
  let args := #[Expr.mkBVar 0, Expr.mkBVar 1]
  let user := fun name => _root_.Ix.ConstantInfo.defnInfo {
    cnst := { name := Name.fromLeanName `User, levelParams := #[], type := Expr.mkSort .mkZero }
    value := Expr.mkConst name #[], safety := .safe, hints := .abbrev, all := #[] }
  let table : Std.HashMap Name (Thunk (Except String (Option Expansion))) :=
    ({} : Std.HashMap _ _).insert original (Thunk.pure (.error "original cache entry"))
  return [
    ("raw hash lookup aliases distinct names", heads.get? forged == some owner),
    ("original full-name lookup succeeds", headOwner? heads original == some owner),
    ("different full name cannot borrow entry", (headOwner? heads forged).isNone),
    ("old optimizer can use aliased bucket",
      (Opt.engineFull oldEnv { head := forged, us := #[], args }).isSome),
    ("production optimizer refuses aliased bucket", (optLookup cenv blocks none forged #[] args).isNone),
    ("original optimizer route remains available", (optLookup cenv blocks none original #[] args).isSome),
    ("head discovery rejects different name", (headsIn heads (user forged)).isEmpty),
    ("head discovery retains original", (headsIn heads (user original)).contains original),
    ("image block admission rejects different name", !isImageBlock cenv (({} : _root_.Ix.Set Name).insert forged)),
    ("image block admission retains original", isImageBlock cenv (({} : _root_.Ix.Set Name).insert original)),
    ("cached expansion cannot bypass head identity", match expansionLookupIn table cenv {} forged with
      | .ok none => true | _ => false),
    ("original cached expansion remains selected", match expansionLookupIn table cenv {} original with
      | .error "original cache entry" => true | _ => false)
  ]

def suite : List TestSeq := controls.map fun (label, ok) => test s!"image head lookup: {label}" ok

end Tests.Ix.Compile.HeadLookup
