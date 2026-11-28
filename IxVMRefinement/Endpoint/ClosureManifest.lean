import Ix.IxVM.Consistency.TableValid
import Lean
import Std.Data.HashMap
import Std.Data.HashSet

/-! # The definitional closure of the public statement, pinned

`IxVM.Consistency.CircuitComposed` means what the definitions it unfolds to say. Those
definitions live in many files (the statement files, the reader, the codecs, the basis pins,
the circuit source `IxVM.source`, the Aiur semantics, the kernel's model interface, and the
Lean core library), and a change to any of them changes the meaning of the theorem
`IxVM.Refinement.Endpoint.circuitComposed` without changing its name. This module pins that
meaning at the level of the kernel's environment, independently of files and commits.

It walks every constant reachable from `CircuitComposed` through the kernel's view of
declarations: the type of every constant, the value of every definition and opaque
constant, the constructors and recursor rules of every inductive type. It does not enter
the value of a theorem: by proof irrelevance a proof never contributes to what a
proposition means, so proofs may change freely. For every reached constant it computes a
SHA-256 digest of a canonical serialization of the kernel content
`(kind, name, universe parameters, type, value / constructors / rules, flags)`:

* expressions are serialized as a DAG, each distinct subterm once, children before parents,
  in a fixed traversal order; distinctness is the kernel's alpha-equivalence (`Expr.eqv`),
  and binder names, binder annotations and metadata are not serialized, so the digest is a
  function of what the kernel reads, and of nothing else;
* names, levels, literals and every numeric field are serialized with explicit tags and
  lengths, so the serialization is injective on that content.

The manifest is the sorted list of lines `KIND DIGEST MODULE NAME` (`KIND`: `A` axiom,
`D` definition, `T` theorem (statement only), `O` opaque, `Q` quotient, `I` inductive,
`C` constructor, `R` recursor), headed by the Lean version. Its own SHA-256 digest is
pinned below (`pinnedDigest`), so the build of this module fails when any constant of the
closure changes, appears or disappears, or when the toolchain changes. The text of the
manifest is committed beside it (`manifestPath`), for review and to name the constants
that changed when the check fails.

Updating it (only with a reviewed change to the statement's meaning): build this module
with the environment variable `IXVM_CLOSURE_MANIFEST_WRITE` set to a path; the manifest is
written there and its digest printed; commit both, the digest in `pinnedDigest`. -/

namespace IxVM.Refinement.ClosureManifest

open Lean Elab Command

/-! ## SHA-256 (FIPS 180-4), in Lean -/

/-- The round constants. -/
def sha256K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The initial hash value. -/
def sha256H0 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

def rotr (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- One compression of the 64-byte block of `m` at `off`. -/
def sha256Block (h : Array UInt32) (m : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  let byte (i : Nat) : UInt32 := m[off + i]!.toUInt32
  let mut w : Array UInt32 := #[]
  for i in [0:16] do
    w := w.push ((byte (4*i) <<< 24) ||| (byte (4*i+1) <<< 16) ||| (byte (4*i+2) <<< 8) |||
      byte (4*i+3))
  for i in [16:64] do
    let x := w[i-15]!
    let y := w[i-2]!
    let s0 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
    let s1 := rotr y 17 ^^^ rotr y 19 ^^^ (y >>> 10)
    w := w.push (w[i-16]! + s0 + w[i-7]! + s1)
  let mut a := h[0]!
  let mut b := h[1]!
  let mut c := h[2]!
  let mut d := h[3]!
  let mut e := h[4]!
  let mut f := h[5]!
  let mut g := h[6]!
  let mut k := h[7]!
  for i in [0:64] do
    let s1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let t1 := k + s1 + ch + sha256K[i]! + w[i]!
    let s0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := s0 + maj
    k := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  return #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g,
    h[7]! + k]

/-- The SHA-256 digest of `msg`, as 64 lowercase hexadecimal digits. -/
def sha256Hex (msg : ByteArray) : String := Id.run do
  let len := msg.size
  let mut m := msg.push 0x80
  while m.size % 64 != 56 do
    m := m.push 0
  let bits := len * 8
  for i in [0:8] do
    m := m.push ((bits >>> (8 * (7 - i))) % 256).toUInt8
  let mut h := sha256H0
  let mut off := 0
  while off < m.size do
    h := sha256Block h m off
    off := off + 64
  let hex (x : UInt32) : String :=
    let s := String.ofList (Nat.toDigits 16 x.toNat)
    "".pushn '0' (8 - s.length) ++ s
  return h.foldl (fun acc x => acc ++ hex x) ""

-- FIPS 180-4 test vectors: the hash used below is SHA-256.
#guard sha256Hex "".toUTF8 =
  "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard sha256Hex "abc".toUTF8 =
  "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard sha256Hex "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8 =
  "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"

/-! ## Canonical serialization of kernel content -/

/-- Unsigned LEB128. -/
partial def putNat (b : ByteArray) (n : Nat) : ByteArray :=
  if n < 128 then b.push n.toUInt8 else putNat (b.push (n % 128 + 128).toUInt8) (n / 128)

def putStr (b : ByteArray) (s : String) : ByteArray :=
  let u := s.toUTF8
  putNat b u.size ++ u

def putBool (b : ByteArray) (x : Bool) : ByteArray := b.push (if x then 1 else 0)

def putName : ByteArray → Name → ByteArray
  | b, .anonymous => b.push 0
  | b, .str p s => putStr ((putName b p).push 1) s
  | b, .num p n => putNat ((putName b p).push 2) n

def putNames (b : ByteArray) (ns : List Name) : ByteArray :=
  ns.foldl putName (putNat b ns.length)

partial def putLevel : ByteArray → Level → Except String ByteArray
  | b, .zero => pure (b.push 0)
  | b, .succ l => putLevel (b.push 1) l
  | b, .max l r => do putLevel (← putLevel (b.push 2) l) r
  | b, .imax l r => do putLevel (← putLevel (b.push 3) l) r
  | b, .param n => pure (putName (b.push 4) n)
  | _, .mvar _ => throw "a universe metavariable in a declaration"

def putLevels (b : ByteArray) (ls : List Level) : Except String ByteArray :=
  ls.foldlM putLevel (putNat b ls.length)

/-- The serializer's state: the index of every subterm already written, and the stream. -/
structure SerState where
  ids : Std.HashMap Expr Nat := {}
  out : ByteArray := .empty

abbrev SerM := StateT SerState (Except String)

/-- Write `e` (each distinct subterm once, children first) and return its index. -/
partial def serExpr (e : Expr) : SerM Nat := do
  if let .mdata _ e' := e then return (← serExpr e')
  if let some i := (← get).ids[e]? then return i
  let node : ByteArray ← match e with
    | .bvar i => pure (putNat (ByteArray.empty.push 0) i)
    | .sort l => ofExcept (putLevel (ByteArray.empty.push 1) l)
    | .const n ls => ofExcept (putLevels (putName (ByteArray.empty.push 2) n) ls)
    | .app f a => do
      let i ← serExpr f
      let j ← serExpr a
      pure (putNat (putNat (ByteArray.empty.push 3) i) j)
    | .lam _ t b _ => do
      let i ← serExpr t
      let j ← serExpr b
      pure (putNat (putNat (ByteArray.empty.push 4) i) j)
    | .forallE _ t b _ => do
      let i ← serExpr t
      let j ← serExpr b
      pure (putNat (putNat (ByteArray.empty.push 5) i) j)
    | .letE _ t v b _ => do
      let i ← serExpr t
      let j ← serExpr v
      let k ← serExpr b
      pure (putNat (putNat (putNat (ByteArray.empty.push 6) i) j) k)
    | .lit (.natVal n) => pure (putNat (ByteArray.empty.push 7) n)
    | .lit (.strVal s) => pure (putStr (ByteArray.empty.push 8) s)
    | .proj s i x => do
      let j ← serExpr x
      pure (putNat (putNat (putName (ByteArray.empty.push 9) s) i) j)
    | .fvar _ => throw "a free variable in a declaration"
    | .mvar _ => throw "a metavariable in a declaration"
    | .mdata .. => throw "unreachable: metadata"
  let s ← get
  let i := s.ids.size
  set { ids := s.ids.insert e i, out := s.out ++ node : SerState }
  return i
where
  ofExcept {α} (x : Except String α) : SerM α := StateT.lift x

def kindChar : ConstantInfo → Char
  | .axiomInfo _ => 'A'
  | .defnInfo _ => 'D'
  | .thmInfo _ => 'T'
  | .opaqueInfo _ => 'O'
  | .quotInfo _ => 'Q'
  | .inductInfo _ => 'I'
  | .ctorInfo _ => 'C'
  | .recInfo _ => 'R'

/-- The canonical bytes of a constant's kernel content. A theorem contributes its statement
only. -/
def constBytes (ci : ConstantInfo) : Except String ByteArray := do
  let go : SerM ByteArray := do
    let ty ← serExpr ci.type
    let mut t := putNat ByteArray.empty ty
    match ci with
    | .axiomInfo v => t := putBool t v.isUnsafe
    | .defnInfo v =>
      t := putNat t (← serExpr v.value)
      t := t.push (match v.safety with | .unsafe => 0 | .safe => 1 | .partial => 2)
      t := match v.hints with
        | .opaque => t.push 0
        | .abbrev => t.push 1
        | .regular h => putNat (t.push 2) h.toNat
      t := putNames t v.all
    | .thmInfo v => t := putNames t v.all
    | .opaqueInfo v =>
      t := putNat t (← serExpr v.value)
      t := putBool t v.isUnsafe
      t := putNames t v.all
    | .quotInfo v =>
      t := t.push (match v.kind with | .type => 0 | .ctor => 1 | .lift => 2 | .ind => 3)
    | .inductInfo v =>
      t := putNat (putNat t v.numParams) v.numIndices
      t := putNames (putNames t v.all) v.ctors
      t := putNat t v.numNested
      t := putBool (putBool (putBool t v.isRec) v.isUnsafe) v.isReflexive
    | .ctorInfo v =>
      t := putName t v.induct
      t := putNat (putNat (putNat t v.cidx) v.numParams) v.numFields
      t := putBool t v.isUnsafe
    | .recInfo v =>
      t := putNames t v.all
      t := putNat (putNat (putNat (putNat t v.numParams) v.numIndices) v.numMotives) v.numMinors
      t := putNat t v.rules.length
      for r in v.rules do
        t := putName t r.ctor
        t := putNat t r.nfields
        t := putNat t (← serExpr r.rhs)
      t := putBool (putBool t v.k) v.isUnsafe
    return t
  let (trailer, s) ← go.run {}
  let head := putNames (putName (ByteArray.empty.push (kindChar ci).toNat.toUInt8) ci.name)
    ci.levelParams
  return putNat head s.ids.size ++ s.out ++ trailer

/-- The constants a constant's kernel content names. A theorem's proof is not entered. -/
def constDeps (ci : ConstantInfo) : Array Name :=
  let ofExprs (es : List Expr) : Array Name :=
    es.foldl (fun acc e => acc ++ e.getUsedConstants) #[]
  match ci with
  | .axiomInfo v => ofExprs [v.type]
  | .defnInfo v => ofExprs [v.type, v.value] ++ v.all.toArray
  | .thmInfo v => ofExprs [v.type]
  | .opaqueInfo v => ofExprs [v.type, v.value] ++ v.all.toArray
  | .quotInfo v => ofExprs [v.type]
  | .inductInfo v => ofExprs [v.type] ++ v.all.toArray ++ v.ctors.toArray
  | .ctorInfo v => ofExprs [v.type] ++ #[v.induct]
  | .recInfo v =>
    ofExprs (v.type :: v.rules.map (·.rhs)) ++ v.all.toArray ++ (v.rules.map (·.ctor)).toArray

/-- Every constant reachable from `root` through `constDeps`. -/
def closure (env : Environment) (root : Name) : Except String (Array ConstantInfo) := do
  let mut seen : Std.HashSet Name := {}
  let mut todo : Array Name := #[root]
  let mut out : Array ConstantInfo := #[]
  seen := seen.insert root
  while todo.size > 0 do
    let n := todo.back!
    todo := todo.pop
    let some ci := env.find? n | throw s!"unknown constant {n}"
    out := out.push ci
    for d in constDeps ci do
      unless seen.contains d do
        seen := seen.insert d
        todo := todo.push d
  return out

/-- The manifest of `root`'s closure: header lines, then one sorted line per constant. -/
def manifest (env : Environment) (root : Name) : Except String (Array String) := do
  let cis ← closure env root
  let mods := env.allImportedModuleNames
  let mut lines : Array String := #[]
  for ci in cis do
    let modName := match env.getModuleIdxFor? ci.name with
      | some i => (mods[i]?).map toString |>.getD "?"
      | none => "-"
    let digest := sha256Hex (← constBytes ci)
    lines := lines.push s!"{kindChar ci} {digest} {modName} {ci.name}"
  let sorted := lines.qsort (· < ·)
  let header := #[
    s!"# definitional closure of {root}",
    s!"# lean {Lean.versionString} {Lean.githash}",
    s!"# constants {sorted.size}"]
  return header ++ sorted

/-! ## The pin -/

/-- The root: the public statement. -/
def root : Name := ``IxVM.Consistency.CircuitComposed

/-- The committed text of the manifest, relative to the package root. -/
def manifestPath : System.FilePath := "Tests/Fixtures/circuit-composed-closure-manifest.txt"

/-- The SHA-256 digest of the manifest's text (its lines, each followed by a newline). -/
def pinnedDigest : String := "e31c0bcc0dc030642ca48461a988a60fff620e81f2d383c6b8617355a80b38fd"

/-- Lines of `a` not in `b`. -/
def missingFrom (a b : Array String) : Array String :=
  let sb : Std.HashSet String := b.foldl (·.insert ·) {}
  a.filter (!sb.contains ·)

/-- Check the closure of `root` against `pinnedDigest`, and the committed text against the
closure. With `IXVM_CLOSURE_MANIFEST_WRITE` set, write the manifest there first. -/
elab "#check_closure_manifest" : command => do
  let env ← getEnv
  let lines ← match manifest env root with
    | .ok ls => pure ls
    | .error e => throwError "closure manifest: {e}"
  let text := lines.foldl (fun acc l => acc ++ l ++ "\n") ""
  let digest := sha256Hex text.toUTF8
  let counts := "ADTOQICR".toList.map fun k =>
    s!"{k}={(lines.filter fun l => l.startsWith (toString k ++ " ")).size}"
  let summary := s!"{lines.size - 3} constants ({" ".intercalate counts})"
  if let some path ← IO.getEnv "IXVM_CLOSURE_MANIFEST_WRITE" then
    IO.FS.writeFile path text
    logInfo m!"closure manifest written to {path}: digest {digest}, {summary}"
  let mut committedText := ""
  try committedText ← IO.FS.readFile manifestPath
  catch e => throwError "closure manifest: cannot read {manifestPath}: {e.toMessageData}"
  if digest != pinnedDigest || committedText != text then
    let committed := (committedText.splitOn "\n").filter (· != "") |>.toArray
    let added := missingFrom lines committed
    let removed := missingFrom committed lines
    let render (xs : Array String) : String := "\n".intercalate (xs.toList.take 40)
    throwError (m!"the definitional closure of {root} differs from its pin: digest {digest}, " ++
      m!"pinned {pinnedDigest}; {summary}.\n" ++
      m!"Lines not in {manifestPath} ({added.size}):\n{render added}\n" ++
      m!"Lines of {manifestPath} not in the closure ({removed.size}):\n{render removed}")

#check_closure_manifest

end IxVM.Refinement.ClosureManifest
