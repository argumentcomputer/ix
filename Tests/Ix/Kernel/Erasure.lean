import Benchmarks.Kernel.CheckIxeMeta
import Tests.Ix.Kernel.Reader

/-! # The erasure test on fixtures (IXC-PLAN §11, step 6)

`.meta` never decides: the reported verdict is the `.anon` run's, and the
`.meta` run explains a failure with names. The erasure property is that the
two runs agree on the erasure: the same declarations up to the keys' mode,
the same verdict, the same fold position and the same failure, its keys
mapped from `.anon` to `.meta` (`Key.map id`: the same addresses). The corpus
form is `kernel-check-ixe --meta` (`Benchmarks.Kernel.CheckIxeMeta`) on
Init+Std; here, at build time:

* the committed prelude read at both modes declares the same keys and is
  accepted by the fold at both;
* the prelude followed by an axiom whose type names an unknown constant fails
  at both modes at the same position with the same failure, keys mapped;
* the `.meta` renderer spells a key the display table knows by its names and
  address, a derived key by its base's spelling and its shape's suffix, and
  any other as `.anon` does. -/

open Ix.Kernel.Reader
open Benchmarks.Kernel.CheckIxeMeta
open Tests.Ix.Kernel.Reader (address builtinPre)

namespace Tests.Ix.Kernel.Erasure

/-- The committed prelude, read at `.meta`. -/
def builtinPreMeta : Prelude .meta := match builtinPrelude with | .ok p => p | .error _ => default

#guard builtinPre.ix.decls.size > 0

-- the same declared keys, up to the mode
#guard (builtinPre.ix.decls.toList.flatMap declaredKeys).map toMeta ==
  builtinPreMeta.ix.decls.toList.flatMap declaredKeys
-- the same terms (by their cached hashes)
#guard builtinPre.ix.decls.toList.map fingerprint == builtinPreMeta.ix.decls.toList.map fingerprint

/-- An axiom at `name` whose type is the constant `ref`. -/
def axiomOf (name ref : Ix.Kernel.Key md) : Ix.Kernel.Declaration md :=
  .axiomDecl { name, levelParams := [], type := .const ref [] }

/-- The two runs' results agree: both accept, or both fail at the same
position with the same failure, keys mapped. -/
def agree (a : Except (Ix.Kernel.CheckError .anon × Nat) (Ix.Kernel.Env .anon))
    (m : Except (Ix.Kernel.CheckError .meta × Nat) (Ix.Kernel.Env .meta)) : Bool :=
  match a, m with
  | .ok ea, .ok em => ea.consts.length == em.consts.length
  | .error (ea, ia), .error (em, im) => ia == im && sameError (ea.mapKeys toMeta) em
  | _, _ => false

def anonRun (extra : Array (Ix.Kernel.Declaration .anon)) :=
  Ix.Kernel.Cached.checkDecls .verified [] (builtinPre.ix.decls ++ extra)

def metaRun (extra : Array (Ix.Kernel.Declaration .meta)) :=
  Ix.Kernel.Cached.checkDecls .verified [] (builtinPreMeta.ix.decls ++ extra)

-- the prelude is accepted at both modes
#guard (anonRun #[]).isOk && (metaRun #[]).isOk
#guard agree (anonRun #[]) (metaRun #[])

-- a failure naming keys: the same at both modes, keys mapped
#guard (anonRun #[axiomOf (.id (address 201)) (.id (address 202))]).toOption.isNone
#guard agree (anonRun #[axiomOf (.id (address 201)) (.id (address 202))])
  (metaRun #[axiomOf (.id (address 201)) (.id (address 202))])

/-- A display table naming the two addresses. -/
def table : DisplayTable .meta :=
  ({} : DisplayTable .meta)
    |>.insert (.id (address 201)) ({ names := [.str (.str .anonymous "Foo") "bar"] }, address 201)
    |>.insert (.id (address 202)) ({ names := [.str .anonymous "b", .str .anonymous "a"] }, address 202)

/-- info: [("reject", "unknown constant in type of Foo.bar@c9c9c9c9")] -/
#guard_msgs in
#eval match metaRun #[axiomOf (.id (address 201)) (.id (address 202))] with
  | .error (e, _) => [Benchmarks.Kernel.CheckIxeStep.checkOutcome e (spellWith table)]
  | .ok _ => []

/-- info: [("reject", "unknown constant in type of #c9c9c9c9c9c9")] -/
#guard_msgs in
#eval match anonRun #[axiomOf (.id (address 201)) (.id (address 202))] with
  | .error (e, _) => [Benchmarks.Kernel.CheckIxeStep.checkOutcome e]
  | .ok _ => []

-- the renderer: names and address, an alias fiber's names as given, a
-- derived key's suffix, and the `.anon` spelling for a key the table lacks
#guard spellWith table (.id (address 201)) == "Foo.bar@c9c9c9c9"
#guard spellWith table (.id (address 202)) == "b | a@cacacaca"
#guard spellWith table (.aux (.id (address 201)) .model) == "Foo.bar@c9c9c9c9._model"
#guard spellWith table (.id (address 203)) == "#cbcbcbcbcbcb"
#guard spellWith table (.role .natAdd) == "Nat.add"

end Tests.Ix.Kernel.Erasure
