import Aiur.Plonk.BetaGadget
import Aiur.Library.Blake3.Correctness

/-!
# The `β` gadget's function against the Lean BLAKE3 specification

`plonk_beta_test` emits the gadget (`Beta.betaSteps`), decides `Beta.betaOk`
and compares `Beta.betaFn` (the function `beta_functional` says the gates
force) with the specification of `Aiur.Library.Blake3` (`Correctness.lean`):
the compression of the block `domain ‖ le32(γ)` with counter 0, length 55
and flags `1 | 2 | 8`, its 16 output words read as a little-endian integer
and reduced mod `r`. It also checks that the first 8 output words are
`compress` and that their bytes are `digest` of the same input (the
standard 32-byte hash), and that the prover's assignment (`witnessAll`) satisfies every gadget
gate. The vectors are those of `TestAiurLookupBlake3`
(`tools/gnark/aiur_plonk_blake3_test.go`): `0`, `1`, `2^200`, `r − 1` and
`BLAKE3([i, 0xa5])` mod `r` for `i < 8` (big-endian, as Go's `SetBytes`).
-/

namespace Aiur.Plonk.BetaTest

open Aiur.Plonk.Beta
open Aiur.Library.Field.BN254 (modulus)
open Aiur.Library.Blake3 (iv schedules round initialWords blockWords compress digest cvBytes)

def le32 (n : Nat) : List UInt8 := (List.range 32).map fun i => (n / 256 ^ i % 256).toUInt8

def beNat (bytes : List UInt8) : Nat := bytes.foldl (fun a b => 256 * a + b.toNat) 0

/-- The specification's `β`. -/
def specBeta (γ : Nat) : Nat × Bool :=
  let input := lookupDomain ++ le32 γ
  let block := blockWords input
  let st := schedules.foldl (fun s sch => round s block sch) (initialWords iv 0 55 (1 ||| 2 ||| 8))
  let out : List UInt32 := (List.range 8).map (fun i => st[i]! ^^^ st[i + 8]!) ++
    (List.range 8).map (fun i => st[i + 8]! ^^^ iv[i]!)
  let cv := compress iv block 0 55 (1 ||| 2 ||| 8)
  let firstOk := (List.range 8).all (fun i => cv[i]! == out[i]!) && cvBytes cv == digest input
  let v := (out.zipIdx.map fun (x, i) => x.toNat * 2 ^ (32 * i)).sum
  (v % modulus, firstOk)

def run : IO UInt32 := do
  let (steps, next) := betaSteps 0 1 2
  let gates := gadgetGates steps
  IO.println s!"gadget: {steps.length} steps, {gates.length} gates, {next - 2} internal wires"
  let ok := betaOk steps 0 1
  IO.println s!"betaOk: {ok}"
  let mut bad := if ok then 0 else 1
  let mut cases : List Nat := [0, 1, 2 ^ 200, modulus - 1]
  for i in [0:8] do
    cases := cases ++ [beNat (digest [i.toUInt8, 0xa5]).toList % modulus]
  for γ in cases do
    let env := witnessAll (({} : Std.HashMap Nat Fr).insert 0 (γ : Fr)) steps
    let b := (env.getD 1 0).val
    let (s, firstOk) := specBeta γ
    let holds := gates.all fun g =>
      let v (x : Nat) := env.getD x 0
      g.qL * v g.a + g.qR * v g.b + g.qO * v g.c + g.qM * (v g.a * v g.b) + g.qC == 0
    let same := b == s && betaFn steps 0 1 (γ : Fr) == (s : Fr)
    IO.println s!"γ = {γ}: β = {b}, spec {if same then "equal" else s!"DIFFERS ({s})"}, compress/digest {firstOk}, gates hold {holds}"
    unless same && firstOk && holds do bad := bad + 1
  IO.println s!"{if bad == 0 then "all agree" else s!"{bad} failures"}"
  return if bad == 0 then 0 else 1

end Aiur.Plonk.BetaTest

def main : IO UInt32 := Aiur.Plonk.BetaTest.run
