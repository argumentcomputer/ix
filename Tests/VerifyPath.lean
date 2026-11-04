import Lean
import Blake3.Rust

/-! Fingerprint of the Lean code that decides whether a formal Aiur proof is
accepted.

The closure starts from the acceptance entry points (`ix verify`, formal,
aggregate and catalog, and the checks `ix prove` and `ix aggregate` apply to
the roots the aggregate controller returns) and from the code that compiles
the certified programs the verifying keys are taken from: the compiler
linked into `ix`, which the selection code reaches through
`FormalProver.compiler?`, and the standalone exporters. It follows every constant referenced by a
type, a value, a constructor or recursor, an `@[implemented_by]` target, and
the `_unsafe_rec` definition the compiler runs for recursive definitions.
Constants of the toolchain (`Init`, `Std`, `Lean`, `Lake`) end the walk:
they are fixed by `lean-toolchain`, whose version is part of the
fingerprint. Every other module, project or dependency, is followed.

Each constant is hashed from its kernel declaration (kind, universe
parameters, type, value or inductive data) and its `@[extern]` and
`@[implemented_by]` attributes. Expressions are hashed up to alpha
equivalence: binder names, binder annotations and metadata are ignored,
because none of them changes what a term means.

The Aiur sources of the certified programs and the pinned verifying keys
(`tools/formal-aiur.keys`) are files rather than constants, so their
contents are hashed too.

Output: `fingerprint <hex>`, the toolchain, the roots, the source files with
their hashes, then one `<hex> <group>:<name>` line per constant, sorted. -/

open Lean

namespace VerifyPath

abbrev Digest := ByteArray

def blake3 (bytes : ByteArray) : Digest := (Blake3.Rust.hash bytes).val

def hex (bytes : ByteArray) : String :=
  bytes.foldl (init := "") fun acc b =>
    let digit (n : UInt8) : Char := "0123456789abcdef".toList[n.toNat]!
    (acc.push (digit (b >>> 4))).push (digit (b &&& 15))

/-- A byte buffer with length-prefixed fields, so distinct field sequences
never encode to the same bytes. -/
structure Buf where
  bytes : ByteArray := .empty

namespace Buf

def u8 (b : Buf) (x : UInt8) : Buf := ⟨b.bytes.push x⟩

def nat (b : Buf) (n : Nat) : Buf := Id.run do
  -- LEB128
  let mut out := b.bytes
  let mut n := n
  repeat
    let low := (n % 128).toUInt8
    n := n / 128
    if n == 0 then
      out := out.push low
      break
    out := out.push (low ||| 128)
  return ⟨out⟩

def raw (b : Buf) (bytes : ByteArray) : Buf := ⟨b.bytes ++ bytes⟩

def str (b : Buf) (s : String) : Buf := (b.nat s.utf8ByteSize).raw s.toUTF8

def bool (b : Buf) (x : Bool) : Buf := b.u8 (if x then 1 else 0)

partial def name (b : Buf) : Name → Buf
  | .anonymous => b.u8 0
  | .str p s => ((b.u8 1).name p).str s
  | .num p n => ((b.u8 2).name p).nat n

def names (b : Buf) (ns : List Name) : Buf :=
  ns.foldl (init := b.nat ns.length) Buf.name

partial def level (b : Buf) : Level → Buf
  | .zero => b.u8 0
  | .succ l => (b.u8 1).level l
  | .max l r => ((b.u8 2).level l).level r
  | .imax l r => ((b.u8 3).level l).level r
  | .param n => (b.u8 4).name n
  | .mvar m => (b.u8 5).name m.name

def levels (b : Buf) (ls : List Level) : Buf :=
  ls.foldl (init := b.nat ls.length) Buf.level

end Buf

/-- Merkle hash of an expression up to alpha equivalence. `BEq Expr` is
alpha equivalence ignoring binder annotations, so the cache key and the hash
identify exactly the same terms. -/
partial def exprHash (e : Expr) : StateM (Std.HashMap Expr Digest) Digest := do
  if let some d := (← get)[e]? then return d
  let b : Buf := {}
  let b ← match e with
    | .bvar i => pure ((b.u8 0).nat i)
    | .fvar x => pure ((b.u8 1).name x.name)
    | .mvar m => pure ((b.u8 2).name m.name)
    | .sort l => pure ((b.u8 3).level l)
    | .const n ls => pure (((b.u8 4).name n).levels ls)
    | .app f a => return ← finish e (((b.u8 5).raw (← exprHash f)).raw (← exprHash a))
    | .lam _ t body _ =>
      return ← finish e (((b.u8 6).raw (← exprHash t)).raw (← exprHash body))
    | .forallE _ t body _ =>
      return ← finish e (((b.u8 7).raw (← exprHash t)).raw (← exprHash body))
    | .letE _ t v body nonDep =>
      return ← finish e (((((b.u8 8).raw (← exprHash t)).raw (← exprHash v)).raw
        (← exprHash body)).bool nonDep)
    | .lit (.natVal n) => pure ((b.u8 9).str (toString n))
    | .lit (.strVal s) => pure ((b.u8 10).str s)
    | .mdata _ inner => return ← exprHash inner
    | .proj s i inner => return ← finish e ((((b.u8 11).name s).nat i).raw (← exprHash inner))
  finish e b
where
  finish (e : Expr) (b : Buf) : StateM (Std.HashMap Expr Digest) Digest := do
    let d := blake3 b.bytes
    modify (·.insert e d)
    return d

def Buf.extern (b : Buf) : ExternEntry → Buf
  | .adhoc backend => (b.u8 0).name backend
  | .inline backend pattern => ((b.u8 1).name backend).str pattern
  | .standard backend fn => ((b.u8 2).name backend).str fn
  | .opaque => b.u8 3

def Buf.safety (b : Buf) : DefinitionSafety → Buf
  | .unsafe => b.u8 0
  | .safe => b.u8 1
  | .partial => b.u8 2

def constantHash (env : Environment) (c : ConstantInfo) :
    StateM (Std.HashMap Expr Digest) Digest := do
  let b : Buf := ((({} : Buf).name c.name).names c.levelParams).raw (← exprHash c.type)
  let b ← match c with
    | .defnInfo v => pure (((b.u8 0).raw (← exprHash v.value)).safety v.safety)
    | .thmInfo v => pure ((b.u8 1).raw (← exprHash v.value))
    | .opaqueInfo v => pure (((b.u8 2).raw (← exprHash v.value)).bool v.isUnsafe)
    | .axiomInfo v => pure ((b.u8 3).bool v.isUnsafe)
    | .quotInfo v =>
      let kind : UInt8 := match v.kind with
        | .type => 0
        | .ctor => 1
        | .lift => 2
        | .ind => 3
      pure ((b.u8 4).u8 kind)
    | .inductInfo v =>
      let b := ((b.u8 5).nat v.numParams).nat v.numIndices
      let b := (b.names v.all).names v.ctors
      pure ((((b.nat v.numNested).bool v.isRec).bool v.isUnsafe).bool v.isReflexive)
    | .ctorInfo v =>
      let b := (((b.u8 6).name v.induct).nat v.cidx).nat v.numParams
      pure ((b.nat v.numFields).bool v.isUnsafe)
    | .recInfo v => do
      let mut b := (((b.u8 7).names v.all).nat v.numParams).nat v.numIndices
      b := (((b.nat v.numMotives).nat v.numMinors).bool v.k).bool v.isUnsafe
      b := b.nat v.rules.length
      for rule in v.rules do
        b := ((b.name rule.ctor).nat rule.nfields).raw (← exprHash rule.rhs)
      pure b
  let b := match getExternAttrData? env c.name with
    | none => b.u8 0
    | some data => data.entries.foldl (init := (b.u8 1).nat data.entries.length) Buf.extern
  let b := match Compiler.getImplementedBy? env c.name with
    | none => b.u8 0
    | some target => (b.u8 1).name target
  return blake3 b.bytes

def toolchainRoots : List Name := [`Init, `Std, `Lean, `Lake]

def isToolchain (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => toolchainRoots.contains (env.header.moduleNames[idx.toNat]!).getRoot
  | none => false

/-- Names a constant depends on, including the code the compiler runs for it. -/
def edges (env : Environment) (c : ConstantInfo) : Array Name := Id.run do
  let mut out := c.type.getUsedConstants
  match c with
  | .defnInfo v => out := out ++ v.value.getUsedConstants
  | .thmInfo v => out := out ++ v.value.getUsedConstants
  | .opaqueInfo v => out := out ++ v.value.getUsedConstants
  | .inductInfo v => out := out ++ v.all.toArray ++ v.ctors.toArray
  | .ctorInfo v => out := out.push v.induct
  | .recInfo v =>
    out := out ++ v.all.toArray
    for rule in v.rules do out := out ++ rule.rhs.getUsedConstants
  | _ => pure ()
  if let some target := Compiler.getImplementedBy? env c.name then out := out.push target
  let unsafeRec := Name.str c.name "_unsafe_rec"
  if env.contains unsafeRec then out := out.push unsafeRec
  return out

def closure (env : Environment) (roots : Array Name) : IO (Array (Name × Digest)) := do
  let mut seen : NameSet := {}
  let mut stack := roots
  let mut found : Array ConstantInfo := #[]
  for root in roots do
    unless env.contains root do throw (IO.userError s!"root {root} is not defined")
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    if isToolchain env n then continue
    let some c := env.find? n | throw (IO.userError s!"{n} is referenced but not defined")
    found := found.push c
    stack := stack ++ edges env c
  let (hashes, _) := (found.mapM (constantHash env)).run {}
  return (found.map (·.name)).zip hashes

structure Group where
  label : String
  imports : Array Name
  roots : Array Name

def groups : Array Group := #[
  { label := "ix"
    imports := #[`Ix.Cli.CatalogAggregate, `Ix.Cli.FormalAggregate, `Ix.Cli.FormalAiur,
      `Ix.Cli.VerifyCmd]
    roots := #[
      `Ix.Cli.VerifyCmd.runVerifyCmd,
      `Ix.Cli.FormalAggregate.verify,
      `Ix.Cli.FormalAggregate.accept,
      `Ix.Cli.FormalAggregate.acceptSlot,
      `Ix.Cli.CatalogAggregate.verifyCatalog,
      `Ix.Cli.CatalogAggregate.acceptCatalog,
      `Ix.Cli.FormalAiur.verify,
      `Ix.Cli.FormalAggregate.context,
      `Ix.Cli.FormalAiur.compiledArtifact,
      `Ix.Cli.FormalAiur.artifact,
      `Ix.Cli.FormalAiur.aggregationArtifact,
      `Ix.Cli.FormalAiur.verifierArtifact,
      `Ix.Cli.FormalAiur.artifactPath,
      `Ix.Cli.FormalAiur.aggregationArtifactPath,
      `Ix.Cli.FormalAiur.verifierArtifactPath] },
  { label := "linked-compiler", imports := #[`Ix.FormalCompiler]
    roots := #[`Ix.FormalCompiler.compile, `Ix.FormalCompiler.digest,
      `Ix.FormalCompiler.identity] },
  { label := "ixvm-exporter", imports := #[`IxVM.Main], roots := #[`main] },
  { label := "stark-exporter", imports := #[`MultiStark.Main], roots := #[`main] }]

/-- The `.sources` bundles the certified artifacts are compiled from. -/
def bundles : Array System.FilePath := #[
  "IxVM/IxVM/Program.sources",
  "MultiStark/MultiStark/Aggregate.sources",
  "MultiStark/MultiStark/Program.sources"]

/-- The pinned identities and verifying keys acceptance compares with. -/
def pinFiles : Array System.FilePath := #["tools/formal-aiur.keys"]

/-- Each bundle manifest and every file it lists, and the pin files, with
the content hash. -/
def sourceFiles : IO (Array (String × Digest)) := do
  let mut out := #[]
  for path in pinFiles do
    out := out.push (path.toString, blake3 (← IO.FS.readBinFile path))
  for manifest in bundles do
    let text ← IO.FS.readFile manifest
    out := out.push (manifest.toString, blake3 text.toUTF8)
    let directory := manifest.parent.getD "."
    for raw in text.splitOn "\n" do
      let line := raw.trimAscii.toString
      if line.isEmpty || line.startsWith "#" then continue
      let path := directory / line
      out := out.push (path.toString, blake3 (← IO.FS.readBinFile path))
  return out

end VerifyPath

open VerifyPath in
unsafe def main (_ : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mut lines : Array (String × String) := #[]
  let mut header : Array String := #[s!"toolchain {Lean.versionString} {Lean.githash}"]
  for group in groups do
    let env ← importModules (group.imports.map ({ module := · })) {} (loadExts := false)
    let found ← closure env group.roots
    header := header.push s!"roots {group.label}: {" ".intercalate (group.roots.map toString).toList}"
    header := header.push s!"closure {group.label}: {found.size} constants"
    for (n, d) in found do
      let key := s!"{group.label}:{n}"
      lines := lines.push (key, s!"{hex d} {key}")
  for (path, d) in ← sourceFiles do header := header.push s!"source {hex d} {path}"
  let sorted := (lines.qsort (fun a b => a.1 < b.1)).map (·.2)
  let body := "\n".intercalate (header ++ sorted).toList ++ "\n"
  IO.println s!"fingerprint {hex (blake3 body.toUTF8)}"
  IO.print body
  return 0
