import Aiur.Plonk.Beta

/-!
# The `β` gadget: one BLAKE3 compression of `γ` (untrusted emitter)

The same function as `aiurLookupBeta` (`tools/gnark/aiur_plonk_blake3.go`):

* the block is `"ix/aiur-plonk/logup/v1\0"` (23 bytes) followed by the
  canonical 256-bit little-endian bits of `γ` (254 decomposed bits and two
  zero bits) and zero padding, as sixteen little-endian 32-bit words;
* the state is `IV`, `IV[0..4]`, counter `0`, block length `55`, flags
  `CHUNK_START | CHUNK_END | ROOT`;
* seven rounds of `G`, the message permuted between rounds;
* the 16 output words `s[i] ⊕ s[i+8]`, `s[i+8] ⊕ IV[i]`, read as one
  little-endian 512-bit integer, reduced in `Fr`.

Words are 32 bits, least significant first. A bit is a constant or a wire,
possibly negated (`1 − w`), so constants fold and negations are free. XOR of
two wires is the gate `a + b − 2ab − c = 0`; a sum of words is a linear
chain followed by a bit decomposition of `32 + ⌈log₂ k⌉` bits whose low 32
bits are the result; rotation is a renaming.

Nothing here is trusted: `Beta.betaOk` checks the emitted steps and
`Beta.beta_functional` gives the function they force; that this function is
the BLAKE3 expansion is tested against the Lean specification
(`Examples/PlonkBetaTest.lean`).
-/

namespace Aiur.Plonk.Beta

open Aiur.Library.Field.BN254 (modulus)

inductive Bit where
  | c (b : Bool)
  | w (wire : Nat) (neg : Bool)
  deriving Inhabited

structure GS where
  steps : Array Step := #[]
  next : Nat

abbrev GM := StateM GS

def fresh : GM Nat := modifyGet fun s => (s.next, { s with next := s.next + 1 })

def freshN (n : Nat) : GM (List Nat) := do
  let mut l : Array Nat := #[]
  for _ in [0:n] do l := l.push (← fresh)
  return l.toList

def emit (st : Step) : GM Unit := modify fun s => { s with steps := s.steps.push st }

def Bit.xor : Bit → Bit → GM Bit
  | .c a, .c b => pure (.c (a ^^ b))
  | .c a, .w x n => pure (.w x (n ^^ a))
  | .w x n, .c a => pure (.w x (n ^^ a))
  | .w x n, .w y m => do
      let z ← fresh
      emit (.lin ⟨x, y, z, 1, 1, -1, -2, 0⟩)
      pure (.w z (n ^^ m))

abbrev Word := Array Bit

def constWord (v : Nat) : Word := (Array.range 32).map fun i => .c (v / 2 ^ i % 2 == 1)

def xorW (a b : Word) : GM Word := do
  let mut r : Word := #[]
  for i in [0:32] do r := r.push (← a[i]!.xor b[i]!)
  return r

/-- Rotation right by `k`. -/
def rotW (a : Word) (k : Nat) : Word := (Array.range 32).map fun i => a[(i + k) % 32]!

/-- `Σ cᵢ·bᵢ + k0` as a wire (named `target` when given), or the constant
when no term is a wire. -/
def linComb (terms : Array (Bit × Fr)) (k0 : Fr) (target : Option Nat) : GM (Sum Fr Nat) := do
  let mut k := k0
  let mut vs : Array (Nat × Fr) := #[]
  for (b, c) in terms do
    match b with
    | .c true => k := k + c
    | .c false => pure ()
    | .w x false => vs := vs.push (x, c)
    | .w x true => vs := vs.push (x, -c); k := k + c
  if vs.isEmpty then return .inl k
  let out (last : Bool) : GM Nat := if last then (match target with | some t => pure t | none => fresh) else fresh
  if vs.size == 1 then
    let o ← out true
    emit (.lin ⟨vs[0]!.1, vs[0]!.1, o, vs[0]!.2, 0, -1, 0, k⟩)
    return .inr o
  let mut acc ← out (vs.size == 2)
  emit (.lin ⟨vs[0]!.1, vs[1]!.1, acc, vs[0]!.2, vs[1]!.2, -1, 0, k⟩)
  for i in [2:vs.size] do
    let o ← out (i + 1 == vs.size)
    emit (.lin ⟨acc, vs[i]!.1, o, 1, vs[i]!.2, -1, 0, 0⟩)
    acc := o
  return .inr acc

/-- The wires of the comparison chain against `r − 1` for `n` bits. -/
def canonCount (n : Nat) : Nat := ((natBits n (modulus - 1)).filter (· == 1)).length - 1

/-- The `n` bits of wire `x`, least significant first. -/
def decompose (x n : Nat) (canon : Bool) : GM (Array Nat) := do
  let bs ← freshN n
  let accs ← freshN (n - 2)
  let ps ← if canon then some <$> freshN (canonCount n) else pure none
  emit (.bits x bs accs ps)
  return bs.toArray.reverse

def addW (ws : List Word) : GM Word := do
  let width := 32 + (if ws.length ≤ 1 then 0 else Nat.log2 (ws.length - 1) + 1)
  let terms := ws.foldl (fun acc wd => acc ++ wd.mapIdx fun i b => (b, ((2 ^ i : Nat) : Fr))) #[]
  match ← linComb terms 0 none with
  | .inl k => return constWord (k.val % 2 ^ 32)
  | .inr s =>
      let bits ← decompose s width false
      return (bits.extract 0 32).map fun b => .w b false

def blakeIV : Array Nat :=
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

def blakePermutation : Array Nat := #[2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]

/-- `"ix/aiur-plonk/logup/v1\0"`. -/
def lookupDomain : List UInt8 := "ix/aiur-plonk/logup/v1".toUTF8.toList ++ [0]

def gMix (st : Array Word) (a b c d : Nat) (x y : Word) : GM (Array Word) := do
  let mut s := st
  s := s.set! a (← addW [s[a]!, s[b]!, x])
  s := s.set! d (rotW (← xorW s[d]! s[a]!) 16)
  s := s.set! c (← addW [s[c]!, s[d]!])
  s := s.set! b (rotW (← xorW s[b]! s[c]!) 12)
  s := s.set! a (← addW [s[a]!, s[b]!, y])
  s := s.set! d (rotW (← xorW s[d]! s[a]!) 8)
  s := s.set! c (← addW [s[c]!, s[d]!])
  s := s.set! b (rotW (← xorW s[b]! s[c]!) 7)
  return s

/-- The gadget's steps over `γ`, writing `β` to wire `βw`; fresh wires start
at `next`. -/
def betaM (γw βw : Nat) : GM Unit := do
  let gbits ← decompose γw 254 true
  let mut input : Array Bit := #[]
  for byte in lookupDomain do
    for j in [0:8] do input := input.push (.c (byte.toNat / 2 ^ j % 2 == 1))
  for b in gbits do input := input.push (.w b false)
  input := input ++ #[.c false, .c false]
  input := input ++ Array.replicate (512 - input.size) (.c false)
  let mut block : Array Word := (Array.range 16).map fun i => input.extract (32 * i) (32 * i + 32)
  let mut st : Array Word := (blakeIV.map constWord) ++ ((blakeIV.extract 0 4).map constWord) ++
    #[constWord 0, constWord 0, constWord (lookupDomain.length + 32), constWord (1 ||| 2 ||| 8)]
  for _ in [0:7] do
    st ← gMix st 0 4 8 12 block[0]! block[1]!
    st ← gMix st 1 5 9 13 block[2]! block[3]!
    st ← gMix st 2 6 10 14 block[4]! block[5]!
    st ← gMix st 3 7 11 15 block[6]! block[7]!
    st ← gMix st 0 5 10 15 block[8]! block[9]!
    st ← gMix st 1 6 11 12 block[10]! block[11]!
    st ← gMix st 2 7 8 13 block[12]! block[13]!
    st ← gMix st 3 4 9 14 block[14]! block[15]!
    let previous := block
    block := blakePermutation.map fun i => previous[i]!
  let mut out : Array Word := #[]
  for i in [0:8] do out := out.push (← xorW st[i]! st[i + 8]!)
  for i in [0:8] do out := out.push (← xorW st[i + 8]! (constWord blakeIV[i]!))
  let mut terms : Array (Bit × Fr) := #[]
  for i in [0:16] do
    for j in [0:32] do terms := terms.push ((out[i]!)[j]!, ((2 ^ (32 * i + j) : Nat) : Fr))
  let _ ← linComb terms 0 (some βw)

/-- The steps and the next unused wire. -/
def betaSteps (γw βw next : Nat) : List Step × Nat :=
  let ((), s) := (betaM γw βw).run { next }
  (s.steps.toList, s.next)

/-- The prover's assignment: `Step.eval`, plus the Horner and comparison
wires of each decomposition. -/
def Step.witness (env : Std.HashMap Nat Fr) (s : Step) : Std.HashMap Nat Fr := Id.run do
  let mut e := s.eval env
  if let .bits _ bs accs canon := s then
    let v (e : Std.HashMap Nat Fr) (x : Nat) : Fr := e.getD x 0
    let mut prev := bs.headD 0
    let mut as := accs
    for b in (bs.drop 1).dropLast do
      let a := as.headD 0
      e := e.insert a (2 * v e prev + v e b)
      prev := a
      as := as.tail
    if let some ps := canon then
      let mut p : Option Nat := none
      let mut ps := ps
      for (b, k) in bs.zip (natBits bs.length (modulus - 1)) do
        if k == 1 then
          match p with
          | none => p := some b
          | some pw =>
              let q := ps.headD 0
              e := e.insert q (v e pw * v e b)
              p := some q
              ps := ps.tail
  return e

def witnessAll (env : Std.HashMap Nat Fr) (ss : List Step) : Std.HashMap Nat Fr :=
  ss.foldl Step.witness env

end Aiur.Plonk.Beta
