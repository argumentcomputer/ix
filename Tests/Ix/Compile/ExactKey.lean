import LSpec
import Ix.Compile.ExactKey
import Ix.CompileM

namespace Tests.Ix.Compile.ExactKey

open LSpec
open _root_.Ix (Expr Level Name Syntax)

def controls : List (String × Bool) := Id.run do
  let digest : Address := ⟨⟨Array.replicate 32 7⟩⟩
  let otherDigest : Address := ⟨⟨Array.replicate 32 9⟩⟩
  let anon : Name := .anonymous digest
  let xName : Name := .str anon "x" digest
  let yName : Name := .str anon "y" digest
  let zero : Expr := .bvar 0 digest
  let one : Expr := .bvar 1 digest
  let equal := _root_.Ix.Compile.ExactKey.exprEq
  let mut left := zero
  let mut right := zero
  let mut different := one
  for _ in [:64] do
    left := .lam anon left left .default digest
    right := .lam anon right right .default digest
    different := .lam anon different different .default digest
  let mut levelLeft : Level := .zero digest
  let mut levelRight : Level := .zero digest
  for _ in [:64] do
    levelLeft := .max levelLeft levelLeft digest
    levelRight := .max levelRight levelRight digest
  let mut syntaxLeft : Syntax := .missing
  let mut syntaxRight : Syntax := .missing
  for _ in [:64] do
    syntaxLeft := .node .none anon #[syntaxLeft, syntaxLeft]
    syntaxRight := .node .none anon #[syntaxRight, syntaxRight]
  return [
    ("equal leaf", equal zero zero),
    ("equal-hash different indices", !equal zero one),
    ("same payload with different stored hashes", !equal zero (.bvar 0 otherDigest)),
    ("equal-hash different names", !equal (.fvar xName digest) (.fvar yName digest)),
    ("equal-hash different universe names", !equal
      (.sort (.param xName digest) digest) (.sort (.param yName digest) digest)),
    ("binder information", !equal
      (.lam anon zero zero .default digest) (.lam anon zero zero .implicit digest)),
    ("let dependency flag", !equal
      (.letE anon zero zero zero false digest) (.letE anon zero zero zero true digest)),
    ("semantic metadata payload", !equal
      (.mdata #[(xName, .ofNat 0)] zero digest) (.mdata #[(xName, .ofNat 1)] zero digest)),
    ("64-level distinct equal expression DAGs", equal left right),
    ("64-level unequal expression DAGs", !equal left different),
    ("64-level distinct equal universe DAGs", equal (.sort levelLeft digest) (.sort levelRight digest)),
    ("64-level distinct equal metadata DAGs", equal
      (.mdata #[(xName, .ofSyntax syntaxLeft)] zero digest)
      (.mdata #[(xName, .ofSyntax syntaxRight)] zero digest))]

/-- Two names with one stored hash, as only a digest collision makes them:
the compiler's name tables keep them apart, where a table keyed by
`Ix.Name`'s `==` (stored hashes only) makes them one entry. -/
def nameTableControls : List (String × Bool) := Id.run do
  let digest : Address := ⟨⟨Array.replicate 32 7⟩⟩
  let anon : Name := .anonymous digest
  let xName : Name := .str anon "x" digest
  let yName : Name := .str anon "y" digest
  let zName : Name := .str anon "z" digest
  let xAddr : Address := ⟨⟨Array.replicate 32 1⟩⟩
  let yAddr : Address := ⟨⟨Array.replicate 32 2⟩⟩
  let hashKeyed : Std.HashMap Name Address := ({} : Std.HashMap Name Address).insert xName xAddr |>.insert yName yAddr
  let table : Std.HashMap _root_.Ix.Compile.ExactKey.ExactName Address :=
    ({} : Std.HashMap _root_.Ix.Compile.ExactKey.ExactName Address).insert xName xAddr |>.insert yName yAddr
  let ctx : _root_.Ix.MutCtx := (Std.TreeMap.empty : _root_.Ix.MutCtx).insert xName 0 |>.insert yName 1
  let cenv : _root_.Ix.CompileM.CompileEnv := { (default : _root_.Ix.CompileM.CompileEnv) with nameToAddr := table }
  let block : _root_.Ix.CompileM.BlockEnv := { all := {}, current := anon, mutCtx := ctx, univCtx := [] }
  let lookup (n : Name) : Option Address :=
    match _root_.Ix.CompileM.CompileM.run cenv block {} (_root_.Ix.CompileM.lookupConstAddr n) with
    | .ok (address, _) => some address
    | .error _ => none
  return [
    ("control: a hash-keyed table holds the two names as one entry",
      hashKeyed.size == 1 && hashKeyed.get? xName == some yAddr),
    ("a name table holds both", table.size == 2
      && table.get? xName == some xAddr && table.get? yName == some yAddr),
    ("a name absent from a name table is absent, whatever its hash",
      table.get? zName == none && !table.contains zName),
    ("an equal name built separately is found", table.get? (Name.str anon "x" digest) == some xAddr),
    ("lookupConstAddr resolves each name to its own address",
      lookup xName == some xAddr && lookup yName == some yAddr && lookup zName == none),
    ("the mutual context holds both", ctx.size == 2
      && ctx.get? xName == some 0 && ctx.get? yName == some 1 && ctx.get? zName == none)]

def suite : List TestSeq :=
  controls.map (fun (label, passed) => test s!"exact expression key: {label}" passed)
  ++ nameTableControls.map (fun (label, passed) => test s!"exact name table: {label}" passed)

end Tests.Ix.Compile.ExactKey
