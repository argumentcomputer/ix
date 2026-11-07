import Aiur.Modules.Frontend
import Aiur.Execution
import Aiur.Trace.Export
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.NormNum.Prime

/-! A persistent binary trie benchmark. All input construction, updates and
queries execute inside Aiur. Keys are explicit little-endian bit lists.
The same source algorithm is implemented in Ix's Benchmarks/Trie.lean. -/
namespace TrieBenchmark
open Aiur Lean

def source : Modules.Program Nat := aiur_modules% "
module Trie {
  enum Bits { End, Bit(Field, &Bits) }
  enum Node { Leaf(Field), Branch(&Node, &Node, Field) }

  fn total(tree: &Node) -> Field {
    match *tree { Node::Leaf(x) => x, Node::Branch(_, _, sum) => sum }
  }
  fn branch(left: &Node, right: &Node) -> &Node {
    &Node::Branch(left, right, total(left) + total(right))
  }
  fn build(depth: Field, base: Field, stride: Field, seed: Field) -> &Node {
    match depth {
      0 => &Node::Leaf(seed + base * base + 3 * base),
      _ => branch(build(depth - 1, base, stride * 2, seed),
                  build(depth - 1, base + stride, stride * 2, seed)),
    }
  }
  fn zero_key(depth: Field) -> &Bits {
    match depth { 0 => &Bits::End, _ => &Bits::Bit(0, zero_key(depth - 1)) }
  }
  fn increment(key: &Bits) -> &Bits {
    match *key {
      Bits::End => key,
      Bits::Bit(bit, tail) => match bit {
        0 => &Bits::Bit(1, tail),
        _ => &Bits::Bit(0, increment(tail)),
      },
    }
  }
  fn lookup(tree: &Node, key: &Bits) -> Field {
    match *tree {
      Node::Leaf(value) => value,
      Node::Branch(left, right, _) => {
        let Bits::Bit(bit, tail) = *key;
        match bit { 0 => lookup(left, tail), _ => lookup(right, tail) }
      },
    }
  }
  fn update(tree: &Node, key: &Bits, value: Field) -> &Node {
    match *tree {
      Node::Leaf(_) => &Node::Leaf(value),
      Node::Branch(left, right, _) => {
        let Bits::Bit(bit, tail) = *key;
        match bit {
          0 => branch(update(left, tail, value), right),
          _ => branch(left, update(right, tail, value)),
        }
      },
    }
  }
  fn steps(remaining: Field, tree: &Node, snapshot: &Node, key: &Bits,
           probe: &Bits, checkpoint: Field, value: Field, checksum: Field) -> (Field, Field) {
    match remaining {
      0 => (checksum, total(tree)),
      _ => {
        let next = update(tree, key, value);
        let next_key = increment(key);
        let current = lookup(next, next_key);
        let previous = lookup(snapshot, probe);
        let checksum = checksum * 17 + current + previous * 3;
        let value = value * 13 + 7;
        match checkpoint {
          0 => steps(remaining - 1, next, next, next_key, next_key, 63, value, checksum),
          _ => steps(remaining - 1, next, snapshot, next_key, probe, checkpoint - 1, value, checksum),
        }
      },
    }
  }
  fn run(depth: Field, updates: Field, seed: Field) -> (Field, Field) {
    let tree = build(depth, 0, 1, seed);
    let key = zero_key(depth);
    steps(updates, tree, tree, key, key, 63, seed + 100, 0)
  }
}
"

abbrev modulus := 18446744069414584321
abbrev F := ZMod modulus

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem modulus_prime : Nat.Prime modulus := by
  apply lucas_primality modulus (7 : F)
  · reduce_mod_char
  · intro q hq hd
    have factors : modulus - 1 = 2^32 * 3 * 5 * 17 * 257 * 65537 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd | hd | hd | hd
    all_goals
      try replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q
      reduce_mod_char
      decide

instance : Fact (Nat.Prime modulus) := ⟨modulus_prime⟩

def main (args : List String) : IO Unit := do
  let path := args.headD "/tmp/aiur-trie.json"
  let prepared ← IO.ofExcept (Modules.prepare (source.toField F) ["Trie::run"])
  let execution ← IO.ofExcept prepared.exportExecution
  let compiled ← IO.ofExcept (prepared.compileOptimized {})
  let program ← IO.ofExcept (execution.toJson modulus ZMod.val)
  let trace ← IO.ofExcept (Trace.exportJson modulus ZMod.val compiled.circuit.inlined.program
    compiled.circuit.artifact execution.bytecode)
  IO.FS.writeFile path (Json.mkObj [
    ("program", program), ("trace", trace),
    ("args", toJson ([14, 4096, 17] : List Nat))]).compress
  IO.println s!"Exported {execution.bytecode.functions.length} functions to {path}"

end TrieBenchmark

def main (args : List String) : IO Unit := TrieBenchmark.main args
