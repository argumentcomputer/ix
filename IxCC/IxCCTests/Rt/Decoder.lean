/-!
# An independent decoder of native results

The native suites decode every result a test executable returns twice: with
`Rt.readback` (the production readback, over the region the test executable
left) and with this decoder, and require the two texts to agree
(`IxCCTests.Rt.Native.runShell`). Until X1 the second decoder was the C runtime
driver's mirror of `Rt.readback`; this module is that C decoder transcribed to
Lean, statement for statement, so that the suites keep two decoders after the C
driver went.

**What kind of independence this is.** Separate code with a separate
derivation, in the same language: it imports nothing from IxCC (not
`Rt.readback`, not the word or header encodings, not `X86.Memory`); it reads the
result type and the signature from their text forms (`Rt.FoTy.encode`,
`Rt.Sig.encode`) with its own parser, as the C decoder read `--type` and
`--sig`; it reads little-endian words from the region's bytes itself, with the C
decoder's bounds (`[region + 16, region + size)`); and it renders the
observation text directly, as the C decoder printed it. It was derived from the
C decoder's logic, not from `Rt.readback`'s. It is still Lean, written knowing
the same object layout, so it guards against a mistake in either code, not
against a misunderstanding of the layout that both share; the expected values
the suites compare with (Lean's interpreter, Cfg, independent formulas) guard
against that.

The decoding, as the C decoder did it: a `Nat` result is an odd word `2n + 1`,
printed `n`. For an inductive, an odd word `2t + 1` is constructor `t` without
fields (`#t`); an even word is a pointer to a cell whose header holds the tag in
bits 16 to 31 and the field count in bits 0 to 7, which must be the
constructor's (nonzero), followed by one word per field, decoded at the field's
type with one less unit of fuel and printed `#t(f1,f2,…)`. Anything else, a
read outside the region, or fuel exhausted, fails (the C decoder printed `-`).
The C decoder's type parser read the digits of `iK` with `strtol`, which also
skips leading blanks and a sign; this one accepts digits only, which is all
`Rt.FoTy.encode` writes.
-/

namespace IxCCTests.Rt.Decoder

/-- A field or result type: `-1` for `Nat`, `k ≥ 0` for the `k`th inductive. -/
abbrev Ty := Int

/-- The inductives, each a list of constructors, each a list of field types. -/
abbrev Sig := Array (Array (Array Ty))

/-- `parse_ty`: one type at the start of `cs`, and the rest. -/
def parseTy : List Char → Option (Ty × List Char)
  | 'n' :: rest => some (-1, rest)
  | 'i' :: rest =>
    let digits := rest.takeWhile Char.isDigit
    if digits.isEmpty then none
    else some ((String.ofList digits).toNat!, rest.drop digits.length)
  | _ => none

/-- A whole type text (`--type`). -/
def parseType (s : String) : Option Ty :=
  match parseTy s.toList with
  | some (t, []) => some t
  | _ => none

/-- The fields of one constructor, up to and past its `)`. -/
def parseFields : Nat → List Char → Array Ty → Option (Array Ty × List Char)
  | 0, _, _ => none
  | _ + 1, ')' :: rest, acc => some (acc, rest)
  | fuel + 1, cs, acc => do
    let (t, rest) ← parseTy cs
    match rest with
    | ',' :: rest => parseFields fuel rest (acc.push t)
    | ')' :: rest => some (acc.push t, rest)
    | _ => none

/-- The constructors of one inductive: a run of `(…)`. -/
def parseCtors : Nat → List Char → Array (Array Ty) → Option (Array (Array Ty) × List Char)
  | 0, _, _ => none
  | fuel + 1, '(' :: rest, acc => do
    let (fs, rest) ← parseFields rest.length rest #[]
    parseCtors fuel rest (acc.push fs)
  | _ + 1, cs, acc => some (acc, cs)

/-- The inductives, separated by `/`. -/
def parseInds : Nat → List Char → Sig → Option Sig
  | 0, _, _ => none
  | fuel + 1, cs, acc => do
    let (ctors, rest) ← parseCtors (cs.length + 1) cs #[]
    match rest with
    | [] => some (acc.push ctors)
    | '/' :: rest => parseInds fuel rest (acc.push ctors)
    | _ => none

/-- `parse_sig`: the empty text is no inductive. -/
def parseSig (s : String) : Option Sig :=
  if s.isEmpty then some #[] else parseInds (s.length + 1) s.toList #[]

/-- The region as the decoder sees it: its base and size, and its bytes from
`base + 16` (bytes past the end of `live` read as zero). -/
structure View where
  base : UInt64
  size : UInt64
  live : ByteArray

/-- `readable(a, n)`: `[a, a + n)` lies in `[base + 16, base + size)`. -/
def View.readable (v : View) (a n : UInt64) : Bool :=
  if v.size < 16 then false
  else
    let lo := v.base + 16
    let room := v.size - 16
    a ≥ lo && a - lo ≤ room && n ≤ room - (a - lo)

/-- The little-endian word at `a` (which `readable` has admitted). -/
def View.load (v : View) (a : UInt64) : UInt64 :=
  let off := (a - (v.base + 16)).toNat
  (List.range 8).foldl (fun w k => w ||| (((v.live[off + k]?).getD 0).toUInt64 <<< (8 * k).toUInt64)) 0

/-- `decode(w, ty, fuel)`: the observation text, or `none` where the C decoder
returned `-1`. -/
def decode (sig : Sig) (v : View) : Nat → UInt64 → Ty → Option String
  | fuel, w, ty => do
    if ty == -1 then
      if w &&& 1 == 0 then none
      return toString (w >>> 1).toNat
    if ty < 0 then none
    let some ind := sig[ty.toNat]? | none
    if w &&& 1 == 1 then
      let tag := (w >>> 1).toNat
      let some c := ind[tag]? | none
      if c.size != 0 then none
      return s!"#{tag}"
    match fuel with
    | 0 => none
    | fuel + 1 =>
      if !v.readable w 8 then none
      let h := v.load w
      let tag := ((h >>> 16) &&& 0xFFFF).toNat
      let scan := (h &&& 0xFF).toNat
      let some c := ind[tag]? | none
      if c.size != scan || scan == 0 then none
      let fields ← (c.toList.zipIdx).mapM fun (t, j) => do
        let a := w + 8 + 8 * UInt64.ofNat j
        if !v.readable a 8 then none
        decode sig v fuel (v.load a) t
      return s!"#{tag}(" ++ ",".intercalate fields ++ ")"

/-- Decode `w` at the type and signature texts, with `fuel`; `none` if either
text does not parse or the word does not decode. -/
def decodeText (typeText sigText : String) (v : View) (fuel : Nat) (w : UInt64) : Option String := do
  let ty ← parseType typeText
  let sig ← parseSig sigText
  decode sig v fuel w ty

end IxCCTests.Rt.Decoder
