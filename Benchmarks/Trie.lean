import Ix.Aiur.Meta
import Ix.Aiur.Compiler
import Lean

/-! Hint-free persistent trie. The algorithm and function boundaries match
the new Aiur repository's Examples/Trie.lean. Only bytecode is exported. -/
namespace TrieBenchmark
open Aiur Lean

def source := ⟦
  enum Bits { End, Bit(G, &Bits) }
  enum Node { Leaf(G), Branch(&Node, &Node, G) }

  fn total(tree: &Node) -> G {
    match load(tree) { Node.Leaf(x) => x, Node.Branch(_, _, sum) => sum, }
  }
  fn branch(left: &Node, right: &Node) -> &Node {
    store(Node.Branch(left, right, total(left) + total(right)))
  }
  fn build(depth: G, base: G, stride: G, seed: G) -> &Node {
    match depth {
      0 => store(Node.Leaf(seed + base * base + 3 * base)),
      _ => branch(build(depth - 1, base, stride * 2, seed),
                  build(depth - 1, base + stride, stride * 2, seed)),
    }
  }
  fn zero_key(depth: G) -> &Bits {
    match depth { 0 => store(Bits.End), _ => store(Bits.Bit(0, zero_key(depth - 1))), }
  }
  fn increment(key: &Bits) -> &Bits {
    match load(key) {
      Bits.End => key,
      Bits.Bit(bit, tail) => match bit {
        0 => store(Bits.Bit(1, tail)),
        _ => store(Bits.Bit(0, increment(tail))),
      },
    }
  }
  fn lookup(tree: &Node, key: &Bits) -> G {
    match load(tree) {
      Node.Leaf(value) => value,
      Node.Branch(left, right, _) =>
        let Bits.Bit(bit, tail) = load(key);
        match bit { 0 => lookup(left, tail), _ => lookup(right, tail), },
    }
  }
  fn update(tree: &Node, key: &Bits, value: G) -> &Node {
    match load(tree) {
      Node.Leaf(_) => store(Node.Leaf(value)),
      Node.Branch(left, right, _) =>
        let Bits.Bit(bit, tail) = load(key);
        match bit {
          0 => branch(update(left, tail, value), right),
          _ => branch(left, update(right, tail, value)),
        },
    }
  }
  fn steps(remaining: G, tree: &Node, snapshot: &Node, key: &Bits,
           probe: &Bits, checkpoint: G, value: G, checksum: G) -> (G, G) {
    match remaining {
      0 => (checksum, total(tree)),
      _ =>
        let next = update(tree, key, value);
        let next_key = increment(key);
        let current = lookup(next, next_key);
        let previous = lookup(snapshot, probe);
        let checksum = checksum * 17 + current + previous * 3;
        let value = value * 13 + 7;
        match checkpoint {
          0 => steps(remaining - 1, next, next, next_key, next_key, 63, value, checksum),
          _ => steps(remaining - 1, next, snapshot, next_key, probe, checkpoint - 1, value, checksum),
        },
    }
  }
  pub fn run(depth: G, updates: G, seed: G) -> (G, G) {
    let tree = build(depth, 0, 1, seed);
    let key = zero_key(depth);
    steps(updates, tree, tree, key, key, 63, seed + 100, 0)
  }
⟧

instance : ToJson Aiur.G := ⟨fun x => toJson x.n⟩
deriving instance ToJson for Bytecode.Op
deriving instance ToJson for Bytecode.Ctrl, Bytecode.Block
deriving instance ToJson for Bytecode.FunctionLayout, Bytecode.Function, Bytecode.Circuit

def main (args : List String) : IO Unit := do
  let path := args.headD "/tmp/ix-trie.json"
  let compiled ← IO.ofExcept source.compile
  let some entry := compiled.getFuncIdx `run | throw (IO.userError "missing entry")
  let names := compiled.bytecode.functions.mapIdx fun i _ =>
    (compiled.nameMap.toArray.filterMap fun (name, j) =>
      if i == j then some (toString name) else none).qsort (· < ·)
  IO.FS.writeFile path (Json.mkObj [
    ("entry", toJson entry), ("names", toJson names),
    ("functions", toJson compiled.bytecode.functions),
    ("circuits", toJson compiled.bytecode.circuits),
    ("memory_sizes", toJson compiled.bytecode.memorySizes),
    ("args", toJson ([14, 4096, 17] : List Nat))]).compress
  IO.println s!"Exported {compiled.bytecode.functions.size} functions to {path}"

end TrieBenchmark

def main (args : List String) : IO Unit := TrieBenchmark.main args
