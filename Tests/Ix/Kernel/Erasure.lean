import Benchmarks.Kernel.CheckIxeMeta
import Ix.KernelDisplay.Peek
import Tests.Ix.Kernel.Reader

/-! # The erasure test on fixtures

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

/-! ## Named terms (step 6b)

`.meta` (and `.source`) binders carry Lean's names in a subsingleton
(`BinderMeta.display`): the named declarations below are *equal* to their
anonymous erasures, the fold decides them alike at both modes, and a failure
prints its terms with the names (read through `Ix.KernelDisplay.peekAll`, the
display-only read, at elaboration time). -/

/-- A binder named `n`, with info `bi`. -/
def named (n : String) (bi : Ix.Kernel.BinderInfo := .default) : Ix.Kernel.BinderMeta :=
  { pw := .never, display := Squash.mk ⟨.str .anonymous n, bi⟩ }

/-- `∀ (x : Prop), x → x`, its binders named `x` and `h` (anonymous with
`n := false`). -/
def idTy (n : Bool) : Ix.Kernel.Expr md :=
  .forallE (.sort .zero)
    (.forallE (.bvar 0) (.bvar 1) (if n then named "h" else { pw := .never }))
    (if n then named "x" else { pw := .never })

/-- `fun (y : Prop) (h : y) => y`: of type `(y : Prop) → y → Prop`, not
`idTy`'s. -/
def badVal (n : Bool) : Ix.Kernel.Expr md :=
  .lam (.sort .zero) (.lam (.bvar 0) (.bvar 1) (if n then named "h" else { pw := .never }))
    (if n then named "y" else { pw := .never })

/-- A theorem named at its key `k`. -/
def thmOf (k : Ix.Kernel.Key md) (ty v : Ix.Kernel.Expr md) : Ix.Kernel.Declaration md :=
  .thmDecl { name := k, levelParams := [], type := ty } v

-- the named term is its erasure
#guard (idTy true : Ix.Kernel.Expr .meta) == idTy false
#guard decide ((idTy true : Ix.Kernel.Expr .meta) = idTy false)
#guard hash (idTy true : Ix.Kernel.Expr .meta) == hash (idTy false : Ix.Kernel.Expr .meta)

-- a named axiom: accepted at both modes; a named ill-typed theorem: the same
-- failure at both modes
#guard agree (anonRun #[.axiomDecl { name := .id (address 204), levelParams := [], type := idTy false }])
  (metaRun #[.axiomDecl { name := .id (address 204), levelParams := [], type := idTy true }])
#guard (anonRun #[thmOf (.id (address 205)) (idTy false) (badVal false)]).toOption.isNone
#guard agree (anonRun #[thmOf (.id (address 205)) (idTy false) (badVal false)])
  (metaRun #[thmOf (.id (address 205)) (idTy true) (badVal true)])

/-- The named ill-typed theorem's failure. -/
def namedFailure : Option (Ix.Kernel.CheckError .meta) :=
  match metaRun #[thmOf (.id (address 205)) (idTy true) (badVal true)] with
  | .error (e, _) => some e
  | .ok _ => none

/-- The same failure at `.anon`. -/
def anonFailure : Option (Ix.Kernel.CheckError .anon) :=
  match anonRun #[thmOf (.id (address 205)) (idTy false) (badVal false)] with
  | .error (e, _) => some e
  | .ok _ => none

-- printed with names (the display-only read, evaluated at elaboration time)
/--
info: some "invalid: type mismatch in theorem #cdcdcdcdcdcd\nhas type\n  (y : Prop) → y → Prop\nbut is expected to have type\n  ∀ (x : Prop), x → x"
-/
#guard_msgs (whitespace := lax) in
#eval namedFailure.map
  (Ix.KernelDisplay.renderFailure { peek := Ix.KernelDisplay.peekAll, spell := spellWith table })

-- at `.anon` the failure carries no terms (`Msg.withTerms` writes none there)
/-- info: some "invalid: type mismatch in theorem #cdcdcdcdcdcd" -/
#guard_msgs (whitespace := lax) in
#eval anonFailure.map (Ix.KernelDisplay.renderFailure { peek := Ix.KernelDisplay.peekAll })

-- PERF P14 keeps a name: `withPw` at the shared datum copies a named binder
/-- info: "x" -/
#guard_msgs in
#eval toString (Ix.KernelDisplay.peekSquash ((named "x").withPw (.ifAllZero [])).display).name

end Tests.Ix.Kernel.Erasure
