module
public import Ix.Aiur.Stages.Bytecode
public import Std.Data.HashMap

/-!
Bytecode function deduplication via partition refinement (bisimulation).

Functions with identical structure that differ only in call target indices are
merged — this handles mutual recursion and cycles.
-/

public section
@[expose] section

namespace Aiur

namespace Bytecode

def skeletonOp : Op → Op
  | .call _ args size u => .call 0 args size u
  | op => op

/-- Termination helpers for the Block/Ctrl mutual traversals below. -/
private theorem Block.sizeOf_ctrl_lt (b : Block) : sizeOf b.ctrl < sizeOf b := by
  rcases b with ⟨ops, ctrl⟩
  show sizeOf ctrl < 1 + sizeOf ops + sizeOf ctrl
  omega

mutual
  def skeletonCtrl : Ctrl → Ctrl
    | .match v branches def_ =>
      .match v (branches.attach.map fun ⟨(g, b), _⟩ => (g, skeletonBlock b))
        (match def_ with | none => none | some b => some (skeletonBlock b))
    | .return s vs => .return s vs
    | .yield s vs => .yield s vs
    | .matchContinue v branches def_ outputSize sharedAux sharedLookups cont =>
      .matchContinue v (branches.attach.map fun ⟨(g, b), _⟩ => (g, skeletonBlock b))
        (match def_ with | none => none | some b => some (skeletonBlock b))
        outputSize sharedAux sharedLookups (skeletonBlock cont)
  termination_by c => (sizeOf c, 0)
  decreasing_by
    all_goals first
      | decreasing_tactic
      | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

  def skeletonBlock (block : Block) : Block :=
    { block with
      ops := block.ops.map skeletonOp
      ctrl := skeletonCtrl block.ctrl }
  termination_by (sizeOf block, 1)
  decreasing_by
    all_goals first
      | decreasing_tactic
      | (apply Prod.Lex.left; exact Block.sizeOf_ctrl_lt _)
end

def collectCalleesOp : Op → Array FunIdx
  | .call idx _ _ _ => #[idx]
  | _ => #[]

private theorem Block.sizeOf_ctrl_lt' (b : Block) : sizeOf b.ctrl < sizeOf b := by
  rcases b with ⟨ops, ctrl⟩
  show sizeOf ctrl < 1 + sizeOf ops + sizeOf ctrl
  omega

mutual
  def collectCalleesCtrl (c : Ctrl) : Array FunIdx := match c with
    | .match _ branches def_ =>
      let branchCallees := branches.attach.foldl (init := #[]) fun acc ⟨(_, b), _⟩ =>
        acc ++ collectCalleesBlock b
      match def_ with
      | none => branchCallees
      | some b => branchCallees ++ collectCalleesBlock b
    | .return .. => #[]
    | .yield .. => #[]
    | .matchContinue _ branches def_ _ _ _ cont =>
      let branchCallees := branches.attach.foldl (init := #[]) fun acc ⟨(_, b), _⟩ =>
        acc ++ collectCalleesBlock b
      let withDefault := match def_ with
        | none => branchCallees
        | some b => branchCallees ++ collectCalleesBlock b
      withDefault ++ collectCalleesBlock cont
  termination_by (sizeOf c, 0)
  decreasing_by
    all_goals first
      | decreasing_tactic
      | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
      | grind

  def collectCalleesBlock (block : Block) : Array FunIdx :=
    let opCallees := block.ops.foldl (init := #[]) fun acc op =>
      acc ++ collectCalleesOp op
    opCallees ++ collectCalleesCtrl block.ctrl
  termination_by (sizeOf block, 1)
  decreasing_by
    all_goals first
      | decreasing_tactic
      | (apply Prod.Lex.left; exact Block.sizeOf_ctrl_lt' _)
end

def rewriteOp (f : FunIdx → FunIdx) : Op → Op
  | .call idx args size u => .call (f idx) args size u
  | op => op

mutual
  def rewriteCtrl (f : FunIdx → FunIdx) (c : Ctrl) : Ctrl := match c with
    | .match v branches def_ =>
      .match v (branches.attach.map fun ⟨(g, b), _⟩ => (g, rewriteBlock f b))
        (match def_ with | none => none | some b => some (rewriteBlock f b))
    | .return s vs => .return s vs
    | .yield s vs => .yield s vs
    | .matchContinue v branches def_ outputSize sharedAux sharedLookups cont =>
      .matchContinue v (branches.attach.map fun ⟨(g, b), _⟩ => (g, rewriteBlock f b))
        (match def_ with | none => none | some b => some (rewriteBlock f b))
        outputSize sharedAux sharedLookups (rewriteBlock f cont)
  termination_by (sizeOf c, 0)
  decreasing_by
    all_goals first
      | decreasing_tactic
      | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

  def rewriteBlock (f : FunIdx → FunIdx) (block : Block) : Block :=
    { block with
      ops := block.ops.map (rewriteOp f)
      ctrl := rewriteCtrl f block.ctrl }
  termination_by (sizeOf block, 1)
  decreasing_by
    all_goals first
      | decreasing_tactic
      | (apply Prod.Lex.left; exact Block.sizeOf_ctrl_lt _)
end

def assignClasses [BEq α] [Hashable α] (values : Array α) : Array Nat × Nat :=
  let (classes, _, nextId) := values.foldl (init := (#[], (∅ : Std.HashMap α Nat), 0))
    fun (classes, map, nextId) v =>
      match map[v]? with
      | some id => (classes.push id, map, nextId)
      | none => (classes.push nextId, map.insert v nextId, nextId + 1)
  (classes, nextId)

/-- Bounded refinement step. The bound caps optimization work. The public
pass validates the final candidate, so execution preservation does not
depend on proving that this iteration has reached a fixed point. -/
def partitionRefineBound : Nat → Array Nat → Array (Array FunIdx) → Array Nat
  | 0, classes, _ => classes
  | bound+1, classes, callees =>
    let signatures := classes.mapIdx fun i cls =>
      (cls, (callees[i]?.getD #[]).map fun callee => classes[callee]?.getD 0)
    let (newClasses, _) := assignClasses signatures
    if newClasses == classes then classes
    else partitionRefineBound bound newClasses callees
termination_by bound _ _ => bound

/-- Outer interface. Uses `classes.size + 1` as the bound. -/
def partitionRefine (classes : Array Nat) (callees : Array (Array FunIdx)) : Array Nat :=
  partitionRefineBound (classes.size + 1) classes callees

/-! ### Pure-fold decomposition of `Toplevel.deduplicate`.

Three pure step functions, composed without `Id.run do`. Each step exposes a
clean equation lemma for downstream proofs. -/

/-- Step 1: canonical-class flags from `classes`. Position `i` is canonical
iff `classes[i]` equals the number of canonical flags seen so far. -/
def deduplicate_canonical (classes : Array Nat) : Array Bool × Nat :=
  classes.foldl
    (fun (acc : Array Bool × Nat) cls =>
      let (flags, top_cls) := acc
      if cls == top_cls then (flags.push True, top_cls + 1)
      else (flags.push False, top_cls))
    (#[], 0)

/-- Step 2: `remap` function. In-domain: `classes[i]`. Out-of-domain: identity
(semantically irrelevant — evaluator guards `funIdx < functions.size` before
calling — but makes out-of-range agreement provable without a separate
domain invariant). -/
def deduplicate_remap (classes : Array Nat) : FunIdx → FunIdx :=
  fun i => if h : i < classes.size then classes[i] else i

/-- Per-class `entry` aggregation: OR all `.entry` fields across class members.
Total — uses `Array.zip` (truncates to `min classes.size functions.size`). -/
def deduplicate_class_entry (functions : Array Function) (classes : Array Nat)
    (cls : Nat) : Bool :=
  (classes.zip functions).foldl
    (fun acc p => if p.fst == cls then acc || p.snd.entry else acc)
    false

/-- Step 3: build `newFunctions` by filter-mapping canonical indices. Total —
uses `Array.zip` to pair `classes × canonical × functions` (truncates to min
size; all three have size `n` after refinement). -/
def deduplicate_newFunctions (functions : Array Function) (classes : Array Nat)
    (canonical : Array Bool) (remapFn : FunIdx → FunIdx) : Array Function :=
  ((classes.zip canonical).zip functions).foldl
    (fun acc p =>
      let ((cls, can), f) := p
      if can then
        let entry := deduplicate_class_entry functions classes cls
        let body := rewriteBlock remapFn f.body
        acc.push { body, layout := f.layout, entry, constrained := false }
      else acc)
    #[]

/-- Propose a deduplication by partition refinement. The public pass validates
this candidate before returning it. -/
def Toplevel.deduplicateCandidate (t : Toplevel) : Toplevel × (FunIdx → FunIdx) :=
  let functions := t.functions
  let n := functions.size
  if n == 0 then (t, id)
  else
    -- Skeleton key includes full `FunctionLayout`: same-class functions share
    -- every layout field, so dedup's per-class `layout := f.layout`
    -- (canonical rep's) matches every class member's layout.
    let skeletons := functions.map fun f => (skeletonBlock f.body, f.layout)
    let (initClasses, _) := assignClasses skeletons
    let callees := functions.map fun f => collectCalleesBlock f.body
    let classes := partitionRefine initClasses callees
    let (canonical, _top_cls) := deduplicate_canonical classes
    let remapFn := deduplicate_remap classes
    let newFunctions := deduplicate_newFunctions functions classes canonical remapFn
    ({ t with functions := newFunctions }, remapFn)

/-- Keep invalid source function indices outside the target's domain. -/
def boundedRenaming (source : Toplevel) (rename : FunIdx → FunIdx) (i : FunIdx) : FunIdx :=
  if i < source.functions.size then rename i else i

/-- Every old function must map to a valid target with the same layout and
the exact body obtained by rewriting calls. Target size and bounded renaming
also prevent invalid source calls from becoming valid target calls. -/
def validatesRenaming (source target : Toplevel) (rename : FunIdx → FunIdx) : Bool :=
  target.functions.size ≤ source.functions.size &&
    (Array.range source.functions.size).all fun i =>
      if hi : i < source.functions.size then
        if hj : rename i < target.functions.size then
          source.functions[i].layout == target.functions[rename i].layout &&
            rewriteBlock rename source.functions[i].body == target.functions[rename i].body
        else false
      else false

/-- Use a proposed function renaming only after checking its complete code
relation. An invalid candidate leaves the original program and indices intact. -/
def checkedRenaming (source candidate : Toplevel) (rename : FunIdx → FunIdx) :
    Toplevel × (FunIdx → FunIdx) :=
  let bounded := boundedRenaming source rename
  if validatesRenaming source candidate bounded then (candidate, bounded)
  else (source, id)

/-- Deduplicate bytecode functions via validated partition refinement.
Returns the selected program and a mapping from old index to new index. -/
def Toplevel.deduplicate (source : Toplevel) : Toplevel × (FunIdx → FunIdx) :=
  let candidate := source.deduplicateCandidate
  checkedRenaming source candidate.1 candidate.2

end Bytecode

end Aiur

end -- @[expose] section
end
