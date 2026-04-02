module
public import Ix.Aiur.Bytecode
public import Std.Data.HashMap

/-!
Bytecode function deduplication via partition refinement (bisimulation).

Functions with identical structure that differ only in call target indices are
merged. This handles mutual recursion and cycles: two mutual blocks
`{A calls B, B calls A}` and `{C calls D, D calls C}` are correctly identified
as equivalent when A~C and B~D structurally.

Algorithm: compute structural skeletons (erasing call indices), group by
skeleton+layout, then iteratively refine by the equivalence classes of callees
until stable. Same approach as DFA minimization / LLVM ICF.
-/

public section

namespace Aiur

namespace Bytecode

/-- Erase `FunIdx` in call ops, replacing with 0. -/
def skeletonOp : Op → Op
  | .call _ args size u => .call 0 args size u
  | op => op

mutual
  partial def skeletonCtrl : Ctrl → Ctrl
    | .match v branches def_ =>
      .match v (branches.map fun (g, b) => (g, skeletonBlock b))
        (def_.map skeletonBlock)
    | .return s vs => .return s vs

  partial def skeletonBlock (block : Block) : Block :=
    { block with
      ops := block.ops.map skeletonOp
      ctrl := skeletonCtrl block.ctrl }
end

/-- Collect all callee `FunIdx` values from a block, depth-first. -/
def collectCalleesOp : Op → Array FunIdx → Array FunIdx
  | .call idx _ _ _, acc => acc.push idx
  | _, acc => acc

mutual
  partial def collectCalleesCtrl : Ctrl → Array FunIdx → Array FunIdx
    | .match _ branches def_, acc =>
      let acc := branches.foldl (fun acc (_, b) => collectCalleesBlock b acc) acc
      match def_ with
      | none => acc
      | some b => collectCalleesBlock b acc
    | .return .., acc => acc

  partial def collectCalleesBlock (block : Block) (acc : Array FunIdx) : Array FunIdx :=
    let acc := block.ops.foldl (fun acc op => collectCalleesOp op acc) acc
    collectCalleesCtrl block.ctrl acc
end

/-- Rewrite all `FunIdx` values in a block using a mapping function. -/
def rewriteOp (f : FunIdx → FunIdx) : Op → Op
  | .call idx args size u => .call (f idx) args size u
  | op => op

mutual
  partial def rewriteCtrl (f : FunIdx → FunIdx) : Ctrl → Ctrl
    | .match v branches def_ =>
      .match v (branches.map fun (g, b) => (g, rewriteBlock f b))
        (def_.map (rewriteBlock f))
    | .return s vs => .return s vs

  partial def rewriteBlock (f : FunIdx → FunIdx) (block : Block) : Block :=
    { block with
      ops := block.ops.map (rewriteOp f)
      ctrl := rewriteCtrl f block.ctrl }
end

/-- Assign class ids by grouping equal values. Returns an array of class ids
    (same length as input) and the number of distinct classes. -/
def assignClasses [BEq α] [Hashable α] (values : Array α) : Array Nat × Nat :=
  let (classes, _, nextId) := values.foldl (init := (#[], (∅ : Std.HashMap α Nat), 0))
    fun (classes, map, nextId) v =>
      match map[v]? with
      | some id => (classes.push id, map, nextId)
      | none => (classes.push nextId, map.insert v nextId, nextId + 1)
  (classes, nextId)

/-- Run partition refinement to find the coarsest bisimulation.
    Returns final class assignments. -/
partial def partitionRefine (classes : Array Nat) (callees : Array (Array FunIdx)) : Array Nat :=
  let signatures := classes.mapIdx fun i cls =>
    (cls, callees[i]!.map (classes[·]!))
  let (newClasses, _) := assignClasses signatures
  if newClasses == classes then classes
  else partitionRefine newClasses callees

/-- Deduplicate bytecode functions via partition refinement.
    Returns the deduplicated toplevel and a mapping from old index to new index. -/
def Toplevel.deduplicate (t : Toplevel) : Toplevel × (FunIdx → FunIdx) := Id.run do
  let functions := t.functions
  let n := functions.size
  if n == 0 then return (t, id)

  -- Step 1: initial partition by (skeleton, inputSize)
  -- inputSize is needed because the Block alone doesn't capture input arity:
  -- e.g. `id(x) { x }` and `proj1(a, b) { a }` produce identical blocks
  -- (both `return 0 #[0]`) but have 1 vs 2 input columns.
  let skeletons := functions.map fun f => (skeletonBlock f.body, f.layout.inputSize)
  let (initClasses, _) := assignClasses skeletons

  -- Step 2: extract call sequences
  let callees := functions.map fun f => collectCalleesBlock f.body #[]

  -- Step 3: partition refinement
  let classes := partitionRefine initClasses callees

  -- Step 4: build output
  -- Annotate which functions are canonical; that is, which ones represent
  -- their equivalence group. We choose the first function we find
  let mut canonical : Array Bool := #[]
  let mut top_cls := 0
  for cls in classes do
    if cls == top_cls then
      canonical := canonical.push True
      top_cls := top_cls + 1
    else
      canonical := canonical.push False

  -- Since classes are assigned from 0, representing each new class by the successor of
  -- the last created classe in order, then it should represent the new index after
  -- deduplication
  let remapFn : FunIdx → FunIdx := (classes[·]!)

  -- Build new functions array
  let mut newFunctions : Array Function := #[]
  for i in [:n] do
    if canonical[i]! then
      let cls := classes[i]!
      let f := functions[i]!
      -- Merge entry flags from all class members
      let mut entry := f.entry
      for j in [:n] do
        if j != i && classes[j]! == cls then
          entry := entry || functions[j]!.entry
      let body := rewriteBlock remapFn f.body
      newFunctions := newFunctions.push { body, layout := f.layout, entry }

  let toplevel := { t with functions := newFunctions }
  return (toplevel, remapFn)

end Bytecode

end Aiur

end
