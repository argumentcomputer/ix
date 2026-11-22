/-! K5 `pi-digits`: unbounded Lambert/Gibbons spigot algorithm for the first `n`
decimal digits of pi, written in pure total `Nat` (sign-magnitude `acc`).
Returns `last9 * (10^9 + 7) + hash`, where `last9` is the last 9 emitted digits
and `hash` is the rolling polynomial hash over all `n` digits (or `0` if fuel
were exhausted). -/

namespace PiDigitsBench

/-- Total loop of the CLBG/Gibbons spigot using pure `Nat` arithmetic. -/
def spigotLoop (target : Nat) :
    Nat → Nat → Nat → Bool → Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _, _, _, emitted, last9, h =>
    if emitted == target then last9 * 1000000007 + h else 0
  | fuel + 1, num, den, accNeg, accMag, k, emitted, last9, h =>
    if emitted ≥ target then
      last9 * 1000000007 + h
    else
      -- next_term(k + 1)
      let k' := k + 1
      let k2 := 2 * k' + 1
      let add := 2 * num
      let (accNeg1, accMag1) :=
        if !accNeg then
          (false, (accMag + add) * k2)
        else if add ≥ accMag then
          (false, (add - accMag) * k2)
        else
          (true, (accMag - add) * k2)
      let den1 := den * k2
      let num1 := num * k'
      -- check ready: acc >= num (requires acc >= 0)
      if accNeg1 || num1 > accMag1 then
        spigotLoop target fuel num1 den1 accNeg1 accMag1 k' emitted last9 h
      else
        let d3 := (3 * num1 + accMag1) / den1
        let d4 := (4 * num1 + accMag1) / den1
        if d3 != d4 then
          spigotLoop target fuel num1 den1 accNeg1 accMag1 k' emitted last9 h
        else
          -- emit digit d3 and eliminate_digit(d3)
          let last9' := (last9 * 10 + d3) % 1000000000
          let h' := (h * 31 + d3) % 1000000007
          let sub := den1 * d3
          let (accNeg2, accMag2) :=
            if accMag1 ≥ sub then
              (false, (accMag1 - sub) * 10)
            else
              (true, (sub - accMag1) * 10)
          let num2 := num1 * 10
          spigotLoop target fuel num2 den1 accNeg2 accMag2 k' (emitted + 1) last9' h'

def piDigits (n : Nat) : Nat :=
  spigotLoop n (16 * n + 256) 1 1 false 0 0 0 0 0

end PiDigitsBench

/-- The pure benchmark entry: last 9 decimal digits and full polynomial hash of
the first `n` digits of pi. -/
def entry (n : Nat) : Nat := PiDigitsBench.piDigits n

def main : List String → IO UInt32
  | [n] => do IO.println (toString (entry n.toNat!)); pure 0
  | _ => do IO.eprintln "usage: pi-digits N"; pure 1
