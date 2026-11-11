import Ix.Ixon
import Tests.Ix.IxVM.Harness
import Tests.Ix.IxVM.Exploits
import LSpec

/-!
# TagN in the IxVM program

The program carries its own TagN readers (`get_tagn0/2/4`,
`IxonDeserialize`) and writers (`put_tagn0/2/4`, `IxonSerialize`). These cases
hold them to the host codec (`Ixon.putTagN` / `Ixon.getTagN`) on the vectors of
`Tests.Ixon.tagNUnits`, through the production claim entry point: every
TagN-coded field the program reads belongs to a constant it loads by address.

The cases rewrite one field of `unsafe axiom _ : Sort 0`, whose bytes are
`[0xD2][isUnsafe][lvls: N0][type: N4…][sharing][refs][univs: count, N2…]`:

- the level count `lvls` (`f = 0`, byte 2);
- the type's root expression (`f = 4`, byte 3), a sort, variable, string,
  numeral or share node carrying the value;
- the last universe (`f = 2`, the last byte), a variable or a successor count.

Each rewritten string is a differential case. If the host's reader accepts the
whole constant, a `Reveal` of its level count and of its type's address must be
accepted: the program decodes the level count to the host's value, and
re-encodes the type to the host's bytes. If the host rejects it, any `Reveal`
of it must be rejected. The vectors: every rung boundary for each flag width,
with the lowest and the highest flag; the expected encodings; the rejection
vectors; every invalid code followed by as many bytes as a valid rung reads;
the 2^64 limit; truncations and a trailing byte; and every one-byte string
with a sample of second bytes.

A universe variable is checked by value too: `Sort (var v)` is well-formed under
`v + 1` universe parameters and not under `v`. The program bounds the variable
with `UInt32::less_than_fields(v, lvls)`, whose operands must have a 4-byte
decomposition in the circuit, so a parameter count of `2^32` or more has no
trace: those claims are true but unprovable, and the circuit verdict (the
suite's) rejects them at the comparison's range check.

The legacy suite also proved one value per rung through a test-only codec
entry point. The production program has no such entry point, and
`tools/ixvm/check-formal.sh` proves a whole claim, so no proof runs here.
-/

namespace Tests.Ix.IxVM.TagN

open LSpec Tests.Ix.IxVM

/-- The constant the cases rewrite. -/
def base : Ixon.Constant := ⟨.axio ⟨true, 0, .sort 0⟩, #[], #[], #[.zero], #[]⟩

/-- Where a case rewrites `base`'s bytes. -/
inductive Field where
  /-- The level count, an `f = 0` value. -/
  | lvls
  /-- The type's root expression, an `f = 4` tag. -/
  | type
  /-- The last universe, an `f = 2` tag, at the end of the constant. -/
  | univ
  deriving BEq

def Field.width : Field → Nat
  | .lvls => 0 | .type => 4 | .univ => 2

def Field.name : Field → String
  | .lvls => "level count" | .type => "type root" | .univ => "last universe"

/-- `base`'s bytes with `field`'s one-byte encoding replaced by `encoding`. -/
def rewrite (field : Field) (encoding : ByteArray) : ByteArray :=
  let bytes := Ixon.ser base
  let off := match field with
    | .lvls => 2 | .type => 3 | .univ => bytes.size - 1
  bytes.extract 0 off ++ encoding ++ bytes.extract (off + 1) bytes.size

/-- `env` bound to the default role table without the table's support records.
These claims use no role, so their witnesses carry their own constant alone,
not the role closure `withDefaultRoleBinding` adds. -/
def bare (env : Ixon.Env) : Except String Ixon.Env := do
  let bytes ← Ix.Kernel.Reader.defaultTableBytes
  return { env with roleBinding := some { address := Address.blake3 bytes, bytes } }

/-- The content address of an expression's bytes, which a `Reveal` compares
with the program's re-encoding of the expression it read. -/
def exprAddr (e : Ixon.Expr) : Address := Address.blake3 (Ixon.runPut (Ixon.putExpr e))

/-- A `Reveal` of the fields the host read: the scalar fields by value and the
expressions by address, so that the program must decode each field to the
host's value and re-encode each expression to the host's bytes. A mutual
block is revealed by kind alone. -/
def revealAll : Ixon.ConstantInfo → Ix.RevealConstantInfo
  | .defn d => .defn (some d.kind) (some d.safety) (some d.lvls) (some (exprAddr d.typ))
      (some (exprAddr d.value))
  | .recr r => .recr (some r.k) (some r.isUnsafe) (some r.lvls) (some r.params)
      (some r.indices) (some r.motives) (some r.minors) (some (exprAddr r.typ)) none
  | .axio a => .axio (some a.isUnsafe) (some a.lvls) (some (exprAddr a.typ))
  | .quot q => .quot (some q.kind) (some q.lvls) (some (exprAddr q.typ))
  | .cPrj p => .cPrj (some p.idx) (some p.cidx) (some p.block)
  | .rPrj p => .rPrj (some p.idx) (some p.block)
  | .iPrj p => .iPrj (some p.idx) (some p.block)
  | .dPrj p => .dPrj (some p.idx) (some p.block)
  | .muts _ => .muts #[]

/-- The `Reveal` case for constant bytes: the host's reading of every field
when the host accepts them (`revealAll`), a rejection when it does not. -/
def differential (label : String) (bytes : ByteArray) : Builder := fun _ => do
  let (env, addr) := Exploits.storeRawAt {} bytes
  let env ← bare env
  match Ixon.runGetExact Ixon.getConstant bytes with
  | .ok c =>
    Case.ofClaim s!"{label} (the host reads it)" env (.reveal addr (revealAll c.info))
  | .error e =>
    Case.ofClaim s!"{label} (the host refuses it: {e})" env
      (.reveal addr (.axio none none none)) (accept := false)

def tagNBytes (f : Nat) (flag : UInt8) (v : Nat) : ByteArray :=
  Ixon.runPut (Ixon.putTagN f flag v.toUInt64)

/-- The flags a field's value is tested under: the lowest and the highest the
field gives a free value. A universe's successor count builds a chain of that
length, so it is tested only up to `4129`; a universe variable takes any
value. -/
def flags : Field → Nat → List UInt8
  | .lvls, _ => [0]
  -- sort, variable, string, numeral and share nodes carry a bare value
  | .type, _ => [0x0, 0x1, 0x5, 0x6, 0xB]
  | .univ, v => if v ≤ 4129 then [0, 3] else [3]

/-- The encoding of `v` under `flag`, as the field holds it: a successor count
`v > 0` is followed by its base universe (`zero`). -/
def encodingOf (field : Field) (flag : UInt8) (v : Nat) : ByteArray :=
  let bytes := tagNBytes field.width flag v
  if field == .univ && flag == 0 && v > 0 then bytes.push 0 else bytes

/-- Rung boundary values for an `f`-bit flag, plus the `UInt64` extremes. -/
def boundaries (f : Nat) : List Nat :=
  let ends := [Ixon.tagNEnd1 f, Ixon.tagNEnd2 f, Ixon.tagNEnd3 f, Ixon.tagNEnd4 f,
    Ixon.tagNEnd5 f]
  ([0, 1, 2 ^ 64 - 1] ++ ends.flatMap fun e => [e - 1, e, e + 1]).eraseDups

def fields : List Field := [.lvls, .type, .univ]

/-- Each boundary value's encoding, its proper prefixes, and the encoding with
a trailing byte, in each field. -/
def boundaryCases (_ : Unit) : Array Builder := Id.run do
  let mut out := #[]
  for field in fields do
    for v in boundaries field.width do
      for flag in flags field v do
        let bytes := encodingOf field flag v
        let tag := s!"TagN f={field.width} flag={flag} value={v} in the {field.name}"
        out := out.push (differential tag (rewrite field bytes))
        out := out.push (differential s!"{tag} with a trailing byte" (rewrite field (bytes.push 0)))
        for n in [1:bytes.size] do
          out := out.push (differential s!"{tag} cut to {n} bytes" (rewrite field (bytes.extract 0 n)))
  return out

/-- The expected encodings of `Tests.Ixon.tagNUnits`. -/
def expectedVectors : List (Nat × UInt8 × Nat × Array UInt8) := [
  (4, 0xA, 7, #[0xA7]),
  (4, 0xA, 8, #[0xA8, 0x00]),
  (4, 0x1, 1031, #[0x1B, 0xFF]),
  (4, 0, 1032, #[0x0C, 0x00, 0x00]),
  (4, 0, 66567, #[0x0C, 0xFF, 0xFF]),
  (4, 0, 66568, #[0x0D, 0, 0, 0]),
  (4, 0, 16843783, #[0x0D, 0xFF, 0xFF, 0xFF]),
  (4, 0, 16843784, #[0x0E, 0, 0, 0, 0]),
  (4, 0, 4311811079, #[0x0E, 0xFF, 0xFF, 0xFF, 0xFF]),
  (4, 0, 4311811080, #[0x0F, 0, 0, 0, 0, 0, 0, 0, 0]),
  (0, 0, 127, #[0x7F]),
  (0, 0, 128, #[0x80, 0x00]),
  (0, 0, 16512, #[0xC0, 0x00, 0x00]),
  (0, 0, 82047, #[0xC0, 0xFF, 0xFF]),
  (0, 0, 82048, #[0xC1, 0, 0, 0]),
  (0, 0, 16859263, #[0xC1, 0xFF, 0xFF, 0xFF]),
  (0, 0, 16859264, #[0xC2, 0, 0, 0, 0]),
  (0, 0, 4311826560, #[0xC3, 0, 0, 0, 0, 0, 0, 0, 0]),
  (0, 0, 2 ^ 64 - 1, #[0xC3, 0x7F, 0xBF, 0xFE, 0xFE, 0xFE, 0xFF, 0xFF, 0xFF]),
  (2, 3, 32, #[0xE0, 0x00]),
  (2, 3, 4128, #[0xF0, 0x00, 0x00]),
  (2, 3, 69663, #[0xF0, 0xFF, 0xFF]),
  (2, 3, 69664, #[0xF1, 0, 0, 0]),
  (2, 3, 16846879, #[0xF1, 0xFF, 0xFF, 0xFF]),
  (2, 3, 16846880, #[0xF2, 0, 0, 0, 0]),
  (2, 3, 4311814176, #[0xF3, 0, 0, 0, 0, 0, 0, 0, 0])
]

def fieldOfWidth (f : Nat) : Field := if f == 0 then .lvls else if f == 2 then .univ else .type

/-- The host writes the expected bytes. -/
def expectedHostTests : TestSeq :=
  expectedVectors.foldl (init := .done) fun acc (f, flag, v, bytes) =>
    acc ++ test s!"host TagN f={f} flag={flag} writes {v} as {bytes}"
      (tagNBytes f flag v == ⟨bytes⟩)

/-- The expected encodings in their field. A flag the field gives no free value
(an expression of another kind) is read under the field's own flag. -/
def expectedCases (_ : Unit) : Array Builder :=
  expectedVectors.toArray.map fun (f, flag, v, bytes) =>
    let field := fieldOfWidth f
    let flag := if field == .type && !(flags .type v).contains flag then 0x1 else flag
    let bytes : ByteArray := if field == .type then tagNBytes 4 flag v else ⟨bytes⟩
    differential s!"TagN f={f} expected bytes of {v} (flag {flag})" (rewrite field bytes)

/-- Little-endian bytes of `x`, `n` of them. -/
def le (n x : Nat) : Array UInt8 :=
  (Array.range n).map fun i => ((x >>> (8 * i)) % 256).toUInt8

/-- The rejection vectors of `Tests.Ixon.tagNUnits`, plus the exact 2^64 limit
of the 8-byte rung for every flag width. -/
def rejectedVectors : List (String × Nat × Array UInt8) := [
  ("f=2 code 4", 2, #[0x34]),
  ("f=2 code 15", 2, #[0x3F]),
  ("f=0 code 4", 0, #[0xC4]),
  ("f=0 code 63", 0, #[0xFF]),
  ("f=0 code 4 with eight payload bytes", 0, #[0xC4, 0, 0, 0, 0, 0, 0, 0, 0]),
  ("f=4 overflow", 4, #[0x0F, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]),
  ("f=2 overflow", 2, #[0xF3, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]),
  ("f=0 overflow", 0, #[0xC3, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]),
  ("truncated rung 2", 4, #[0x08]),
  ("truncated rung 4", 4, #[0x0D, 0x00, 0x00]),
  ("truncated rung 6", 4, #[0x0F, 0x00, 0x00, 0x00]),
  ("trailing byte", 4, #[0x07, 0x00])
] ++ [0, 2, 4].map fun f =>
  -- Code 3 sits at payload 3h + 3, h = 2^(6 - f).
  (s!"f={f} value 2^64", f,
    #[Ixon.tagNHeader f 0 (3 * 2 ^ (6 - f) + 3)] ++ le 8 (2 ^ 64 - Ixon.tagNEnd5 f))

/-- The rejection vectors in their field. Only the last universe ends the
constant, so a vector elsewhere is followed by the constant's remaining bytes,
and the host's verdict on the whole constant is the expected one. -/
def rejectedCases (_ : Unit) : Array Builder :=
  rejectedVectors.toArray.map fun (name, f, bytes) =>
    differential s!"TagN rejects {name}" (rewrite (fieldOfWidth f) ⟨bytes⟩)

/-- Every invalid code (4..63 for f = 0, 4..15 for f = 2; code `c` sits at
payload `3h + c`, `h = 2^(6 - f)`) followed by exactly as many zero bytes as a
valid rung reads (2, 3, 4 or 8). Length alone does not reject these: a reader
that kept only the code's low two bits would read each as a valid rung. -/
def invalidCodeCases (_ : Unit) : Array Builder := Id.run do
  let mut out := #[]
  for (f, lastCode, flag) in [(0, 63, (0 : UInt8)), (2, 15, 3)] do
    for width in [2, 3, 4, 8] do
      for c in [4:lastCode + 1] do
        let bytes : ByteArray :=
          ⟨#[Ixon.tagNHeader f flag (3 * 2 ^ (6 - f) + c)] ++ Array.replicate width 0⟩
        out := out.push (differential s!"TagN f={f} invalid code {c} with {width} following bytes"
          (rewrite (fieldOfWidth f) bytes))
  return out

/-- Every one-byte string, and every header followed by a sample of second
bytes, in each field. -/
def sweepCases (_ : Unit) : Array Builder := Id.run do
  let seconds : List UInt8 := [0x00, 0x7F, 0x80, 0xFF]
  let mut out := #[]
  for field in fields do
    for a in [0:256] do
      out := out.push (differential s!"TagN f={field.width} one byte {a} in the {field.name}"
        (rewrite field ⟨#[a.toUInt8]⟩))
      for b in seconds do
        out := out.push (differential
          s!"TagN f={field.width} bytes {a} {b} in the {field.name}"
          (rewrite field ⟨#[a.toUInt8, b]⟩))
  return out

/-- `axiom _ : Sort (var v)` with `lvls` universe parameters, a user axiom of
the claim (its axioms tree names it, so a typing claim checks it under the
axiom policy; an unsafe axiom is no claim's seed): well-formed exactly when
`v < lvls`, so the program must read `v` as the host wrote it. A well-formed
one with `lvls ≥ 2^32` is unprovable (the bound's range check has no trace), so
the circuit rejects it at `u32 comparison`. -/
def universeVariableCases (_ : Unit) : Array Builder :=
  let values := (boundaries 2).filter (· < 2 ^ 64 - 1)
  values.toArray.flatMap fun v =>
    #[(v + 1, true), (v, false)].map fun (lvls, wellFormed) _ => do
      let ctx ← Ix.ClaimContext.ofDefaultTable
      let c : Ixon.Constant :=
        ⟨.axio ⟨false, lvls.toUInt64, .sort 0⟩, #[], #[], #[.var v.toUInt64], #[]⟩
      let (env, addr) := Exploits.storeAt {} c
      let some axioms := Ix.AssumptionTree.canonical #[addr]
        | throw "the axiom has no tree"
      let trees := ({} : Std.HashMap Address Ix.AssumptionTree).insert axioms.root axioms
      let provable := lvls < 2 ^ 32
      Case.ofClaim s!"TagN f=2 universe variable {v} under {lvls} parameters" (← bare env)
        (.check { ctx with axioms := some axioms.root } addr none) trees
        (accept := wellFormed && provable)
        (rejectsWith := if wellFormed && !provable then some "u32 comparison" else none)

/-- The level count by value: a `Reveal` of another count is refused. -/
def levelCountCases (_ : Unit) : Array Builder :=
  (boundaries 0).toArray.map fun v _ => do
    let c : Ixon.Constant := ⟨.axio ⟨true, v.toUInt64, .sort 0⟩, #[], #[], #[.zero], #[]⟩
    let (env, addr) := Exploits.storeAt {} c
    let other := if v == 0 then 1 else v - 1
    Case.ofClaim s!"TagN f=0 level count {v} is not revealed as {other}" (← bare env)
      (.reveal addr (.axio none (some other.toUInt64) none)) (accept := false)

def run : IO UInt32 := do
  let host ← lspecIO (.ofList [("ixvm-tagn host", [expectedHostTests])]) []
  let cases := expectedCases () ++ rejectedCases () ++ boundaryCases () ++ invalidCodeCases ()
    ++ levelCountCases () ++ universeVariableCases () ++ sweepCases ()
  -- The universe-variable cases are decided by the circuit's range check, so
  -- this suite always takes the circuit verdict.
  let ixvm ← runCases "ixvm-tagn" cases (circuit := some true)
  return if host == 0 && ixvm == 0 then 0 else 1

end Tests.Ix.IxVM.TagN
