import Aiur.Library.Field.BN254
import Aiur.Library.Field.BLS12381.Prime
import Aiur.Plonk.BetaGadget
import Aiur.Library.Blake3.Correctness

/-!
# The `β` gadget's function against the Lean BLAKE3 specification

`plonk_beta_test` emits the gadget (`Beta.betaSteps`), decides `Beta.betaOk`
and compares `Beta.betaFn` (the function `beta_functional` says the gates
force) with the specification of `Aiur.Library.Blake3` (`Correctness.lean`):
the compression of the block `domain ‖ le32(γ)` with counter 0, length 55
and flags `1 | 2 | 8`, its 16 output words read as a little-endian integer
and reduced mod `p`. It checks both BN254 and BLS12-381 scalar fields, also
verifying that the first 8 output words are `compress` and that their bytes
are `digest` of the same input (the standard 32-byte hash), and that the
prover's assignment (`witnessAll`) satisfies every gadget gate. The vectors
are those of `TestAiurLookupBlake3` (`tools/gnark/aiur_plonk_blake3_test.go`):
`0`, `1`, `2^200`, `p − 1` (and `2^254` for BLS12-381) and `BLAKE3([i, 0xa5])`
mod `p` for `i < 8` (big-endian, as Go's `SetBytes`).
-/

namespace Aiur.Plonk.BetaTest

open Aiur.Plonk.Beta
open Aiur.Library.Blake3 (iv schedules round initialWords blockWords compress digest cvBytes)

def le32 (n : Nat) : List UInt8 := (List.range 32).map fun i => (n / 256 ^ i % 256).toUInt8

def beNat (bytes : List UInt8) : Nat := bytes.foldl (fun a b => 256 * a + b.toNat) 0

/-- The specification's `β` modulo `p`. -/
def specBeta (p γ : Nat) : Nat × Bool :=
  let input := lookupDomain ++ le32 γ
  let block := blockWords input
  let st := schedules.foldl (fun s sch => round s block sch) (initialWords iv 0 55 (1 ||| 2 ||| 8))
  let out : List UInt32 := (List.range 8).map (fun i => st[i]! ^^^ st[i + 8]!) ++
    (List.range 8).map (fun i => st[i + 8]! ^^^ iv[i]!)
  let cv := compress iv block 0 55 (1 ||| 2 ||| 8)
  let firstOk := (List.range 8).all (fun i => cv[i]! == out[i]!) && cvBytes cv == digest input
  let v := (out.zipIdx.map fun (x, i) => x.toNat * 2 ^ (32 * i)).sum
  (v % p, firstOk)

def runFor (p : Nat) [Fact (Nat.Prime p)] (label : String) (extraCases : List Nat := []) : IO UInt32 := do
  let (steps, next) := betaSteps p 0 1 2
  let gates := gadgetGates steps
  IO.println s!"[{label}] gadget: {steps.length} steps, {gates.length} gates, {next - 2} internal wires"
  let ok := betaOk steps 0 1
  IO.println s!"[{label}] betaOk: {ok}"
  let mut bad := if ok then 0 else 1
  let mut cases : List Nat := [0, 1, 2 ^ 200, p - 1] ++ extraCases
  for i in [0:8] do
    cases := cases ++ [beNat (digest [i.toUInt8, 0xa5]).toList % p]
  for γ in cases do
    let env := witnessAll (({} : Std.HashMap Nat (ZMod p)).insert 0 (γ : ZMod p)) steps
    let b := (env.getD 1 0).val
    let (s, firstOk) := specBeta p γ
    let holds := gates.all fun g =>
      let v (x : Nat) := env.getD x 0
      g.qL * v g.a + g.qR * v g.b + g.qO * v g.c + g.qM * (v g.a * v g.b) + g.qC == 0
    let same := b == s && betaFn steps 0 1 (γ : ZMod p) == (s : ZMod p)
    IO.println s!"[{label}] γ = {γ}: β = {b}, spec {if same then "equal" else s!"DIFFERS ({s})"}, compress/digest {firstOk}, gates hold {holds}"
    unless same && firstOk && holds do bad := bad + 1
  IO.println s!"[{label}] {if bad == 0 then "all agree" else s!"{bad} failures"}"
  return if bad == 0 then 0 else 1

def run : IO UInt32 := do
  let r1 ← runFor Aiur.Library.Field.BN254.modulus "BN254"
  let r2 ← runFor Aiur.Library.Field.BLS12381.modulus "BLS12-381" [2 ^ 254]
  return if r1 == 0 && r2 == 0 then 0 else 1

end Aiur.Plonk.BetaTest

def main : IO UInt32 := Aiur.Plonk.BetaTest.run
