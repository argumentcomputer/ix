/-
  image-head-lookup: Pass 3's head table confirms the full stored name.

  `CompileEnv.p3Heads` (and the image memo `p3ImageExps`) are keyed by
  `Ix.Compile.ExactKey.ExactName`, which compares names structurally, so a
  different name that carries a head's stored hash selects nothing. These
  controls build such a name (a synthetic cached hash: no cryptographic
  collision is claimed) and check every route of the hooks
  (`Ix.Compile.Pass`) that reads the head table: head discovery
  (`headsIn`), image-block admission (`isImageBlock`), expansion lookup
  (`expansionLookup`, the image memo included) and the second hook
  (`prepareBlock`, its reference prefilter and its walk). Each refusal of
  the different name has a neighbour in which the original name takes the
  route; the first control shows that an `Ix.Name`-keyed table does alias
  the two names, so the others are not vacuous.

  Ported from `5b57d0e0` (`Tests/Ix/Compile/HeadLookup.lean`), whose Lean
  driver confirmed the name by hand (`headOwner?`) over an `Ix.Name`-keyed
  table. Here the key type does it. The definitional passes' routes
  (`optLookup`, `Opt.engineFull`) come with batch 5; the proofs of
  `5b57d0e0` (`Ix/CompileCert/Head*.lean`) are the statements lane's.
-/
import LSpec
import Ix.Compile.Pass.Driver

namespace Tests.Ix.Compile.HeadLookup

open LSpec
open _root_.Ix (Name Expr)
open _root_.Ix.Compile.Pass
open _root_.Ix.Compile.ExactKey (ExactName)

/-- A definition `name : Sort 0 := value`. -/
def defn (name : Name) (value : Expr) : _root_.Ix.ConstantInfo :=
  .defnInfo {
    cnst := { name, levelParams := #[], type := Expr.mkSort .mkZero }
    value, safety := .safe, hints := .abbrev, all := #[name] }

def controls : List (String × Bool) := Id.run do
  let owner := Name.fromLeanName `HeadLookupControl.Owner
  let original := owner.mkStr "below"
  -- another name carrying `original`'s stored hash
  let forgedOwner := Name.str Name.mkAnon "OtherOwner" owner.getHash
  let forged := Name.str forgedOwner "below" original.getHash
  let raw := ({} : Std.HashMap Name Name).insert original owner
  let heads := ({} : Std.HashMap ExactName Name).insert original owner
  -- one caller of each name
  let userOriginal := (Name.fromLeanName `HeadLookupControl.User).mkStr "original"
  let userForged := (Name.fromLeanName `HeadLookupControl.User).mkStr "forged"
  let ciOriginal := defn userOriginal (Expr.mkConst original #[])
  let ciForged := defn userForged (Expr.mkConst forged #[])
  let consts : Std.HashMap Name _root_.Ix.ConstantInfo :=
    (({} : Std.HashMap _ _).insert original (defn original (Expr.mkSort .mkZero))
      |>.insert userOriginal ciOriginal) |>.insert userForged ciForged
  let expansion : Expansion :=
    { levelParams := #[], value := Expr.mkSort .mkZero, arity := 0, needsRewrite := false }
  let cenv : _root_.Ix.CompileM.CompileEnv := {
    (default : _root_.Ix.CompileM.CompileEnv) with
    env := { consts }, p3Heads := heads
    p3ImageExps := ({} : Std.HashMap ExactName (Expansion × Expr)).insert original
      (expansion, Expr.mkSort .mkZero) }
  let one := fun (n : Name) => ({} : _root_.Ix.Set Name).insert n
  -- the second hook, with the condensation's references of the block, or
  -- without them (then only the walk decides)
  let prepare := fun (user : Name) (refs : Option Name) =>
    let cenv := match refs with
      | some r => { cenv with p3BlockRefs := ({} : Std.HashMap Name (_root_.Ix.Set Name)).insert user (one r) }
      | none => cenv
    prepareBlock cenv (one user) user
  let identity := fun (r : Except _root_.Ix.CompileM.CompileError
      (_root_.Ix.CompileM.CompileEnv × Published)) => match r with
    | .ok (c, p) => c.p3Sources.isEmpty && p.views.isEmpty && p.imageExps.isEmpty
    | .error _ => false
  -- the original enters the rewrite: the head selects its block, `owner`'s,
  -- whose view is built first; that block is absent from this environment,
  -- so the hook reports its member as missing (`pass3Failure`)
  let entersRewrite := fun (r : Except _root_.Ix.CompileM.CompileError
      (_root_.Ix.CompileM.CompileEnv × Published)) => match r with
    | .error (.missingConstant m) => m == owner.pretty
    | _ => false
  return [
    ("an Ix.Name-keyed table aliases the two names", raw.get? forged == some owner),
    ("the head table finds the original name", heads.get? original == some owner),
    ("the head table refuses the different name", (heads.get? forged).isNone),
    ("head discovery rejects the different name", (headsIn heads ciForged).isEmpty),
    ("head discovery retains the original", (headsIn heads ciOriginal).contains original),
    ("image block admission rejects the different name", !isImageBlock cenv (one forged)),
    ("image block admission retains the original", isImageBlock cenv (one original)),
    ("expansion lookup gives the different name no expansion",
      match expansionLookup cenv {} forged with
      | .ok none => true
      | _ => false),
    ("expansion lookup selects the original's memoized expansion",
      match expansionLookup cenv {} original with
      | .ok (some x) => x == expansion
      | _ => false),
    ("the reference prefilter skips a block that names the different name",
      identity (prepare userForged (some forged))),
    ("the walk finds no head in a block that names the different name",
      identity (prepare userForged none)),
    ("a block that names the original enters the rewrite (prefilter)",
      entersRewrite (prepare userOriginal (some original))),
    ("a block that names the original enters the rewrite (walk)",
      entersRewrite (prepare userOriginal none))
  ]

def suite : List TestSeq := controls.map fun (label, ok) => test s!"image head lookup: {label}" ok

end Tests.Ix.Compile.HeadLookup
