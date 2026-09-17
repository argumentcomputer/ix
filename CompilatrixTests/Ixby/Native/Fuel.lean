import CompilatrixTests.Ixby.Native.Support

namespace CompilatrixTests.Ixby.Native

open Ix.Ixby Compilatrix.Tools.Check Compilatrix.Ixby.LeanFrontend

private def shiftCost : Nat → Nat → Nat
  | _, 0 => 3
  | 0, _ + 1 => 5
  | n + 1, k + 1 => 7 + shiftCost ((n + 1) / 2) k

private def powCost : Nat → Nat
  | 0 => 3
  | e + 1 => if e + 1 == 1 then 10 else
      (if (e + 1) % 2 == 0 then 10 else 11) + powCost ((e + 1) / 2)
termination_by e => e
decreasing_by omega

/-- Independent instruction accounting, including final halt. Each case also
checks exhaustion one transition before the expected result. -/
def fuelCases (image : Image) : IO Nat := do
  let count ← IO.mkRef 0
  let check (id : Nat) (args : Array Value) (expected : Value) (steps : Nat) : IO Unit := do
    let program := { image.program with entry := id }
    let frame ← checked ((enter image.state.limits program id args).mapError reprStr)
    let state : State := ⟨.eval frame, #[]⟩
    let initial := Compilatrix.Ixby.Runtime.Chunked.State.ofReference state
    let actual := Compilatrix.Ixby.Runtime.Chunked.runChunk image.state.limits program (steps + 1) initial 0
    let accepted := match actual with
      | .ok (.inl value, used) => value.toReference == expected && used == steps
      | _ => false
    need accepted s!"fuel formula {id}: expected {steps} transitions; {reprStr actual}"
    need (same (Ix.Ixby.run image.state.limits program steps state) (.ok expected))
      s!"reference fuel formula {id}"
    need (same (Ix.Ixby.run image.state.limits program (steps - 1) state) (.error .outOfFuel))
      s!"one-less-fuel formula {id}"
    count.modify (· + 1)
  let arrayId ← checked (image.ctorId `Ixby.Runtime.Array)
  let bytesId ← checked (image.ctorId `Ixby.Runtime.Bytes)
  let array (xs : Array Value) := Value.ctor arrayId #[.array xs]
  let packed (xs : Array UInt8) := Value.ctor bytesId #[.scalar (.bytes xs), natural xs.size]
  for n in #[0, 1, 2, 3, 7, 8, 15, 31, 32, 33, 65, 257] do
    let bytes := (List.range n).toArray.map Nat.toUInt8
    let xs := bytes.map (fun b => word b.toUInt32)
    check 58 #[.erased, array xs] (natural n) 4
    check 58 #[.erased, packed bytes] (natural n) 3
    check 51 #[array xs] (.scalar (.bytes bytes)) (8 * n + 9)
    check 51 #[packed bytes] (.scalar (.bytes bytes)) 3
    check 50 #[.array xs, natural 0, natural n, .byteBuilder #[42]]
      (.scalar (.bytes (#[42] ++ bytes))) (8 * n + 5)
    check 99 #[.scalar (.bytes bytes), word n.toUInt32, natural 0]
      (natural (bytes.toList.foldr (fun b a => b.toNat + 256 * a) 0)) (8 * n + 4)
    for start in #[0, n / 2, n, n + 1] do
      let slice := xs.extract start n
      check 72 #[array xs, natural start, natural n] (array slice)
        (if start < n then 22 * (n - start) + 20 else 13)
      check 72 #[packed bytes, natural start, natural n]
        (if start < n then packed (bytes.extract start n) else array #[])
        (if start < n then 16 else 12)
    if n > 0 then
      check 62 #[.erased, array xs, natural (n - 1), .erased] xs[n - 1]! 11
      check 62 #[.erased, packed bytes, natural (n - 1), .erased] xs[n - 1]! 11
      check 69 #[.erased, array xs, natural (n - 1), word 37] (array (xs.set! (n - 1) (word 37))) 12
    check 69 #[.erased, array xs, natural n, word 37] (array xs) 9
    check 68 #[.erased, array xs, word 37] (array (xs.push (word 37))) 5
    for m in #[0, 1, 7] do
      let tailBytes := (List.range m).toArray.map (fun i => (i + 100).toUInt8)
      let tailValues := tailBytes.map (fun b => word b.toUInt32)
      check 74 #[array xs, array tailValues] (array (xs ++ tailValues))
        (if n == 0 then 14 else if m == 0 then 16 else 22 * m + 24)
      check 74 #[packed bytes, packed tailBytes] (packed (bytes ++ tailBytes))
        (if n == 0 then 12 else if m == 0 then 14 else 25)
  for n in #[0, 1, 2, 3, 7, 256, 2 ^ 64, 2 ^ 256] do
    for k in #[0, 1, 2, 31, 32, 64, 128, 257] do
      check 21 #[natural n, natural k] (natural (n >>> k)) (shiftCost n k + 2)
    check 22 #[natural n] (natural n.log2) (5 * n.log2 + 5)
  for e in #[0, 1, 2, 3, 4, 7, 8, 31, 32, 65, 127] do
    check 20 #[natural 3, natural e] (natural (3 ^ e)) (powCost e + 2)
  for width in #[0, 1, 3, 4, 5, 7, 8, 9, 32, 33, 65] do
    check 98 #[natural width, natural 37, .byteBuilder #[42]]
      (.scalar (.bytes (#[42] ++ (List.range width).toArray.map (fun i => (37 / 256 ^ i).toUInt8))))
      (8 * ((width - 1) / 4) + 10)
  IO.println s!"native fuel: {← count.get} exact transition formulas and one-less-fuel rejections"
  return ← count.get

end CompilatrixTests.Ixby.Native
