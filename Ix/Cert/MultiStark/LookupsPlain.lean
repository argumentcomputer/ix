import Ix.Cert.MultiStark.Types
import Ix.Cert.MultiStark.Air

/-! # Executable `LookupsPlain` & Compiler-Context Checks (`Ix.Cert.MultiStark.LookupsPlain`)

Mathlib-free executable validation and soundness proofs enforcing the same graph-context
invariants as `multi-stark`'s constraint compiler (`Context::Lookup`, base constraints) and
`crates/stark-key/src/lib.rs` (`check_compiler_contexts`):

1. **Lookup prefix isolation (`checkLookupsPlain`, `SysCircuit.LookupsPlain`):**
   Every lookup multiplicity and argument root lies strictly inside `lookupPrefixLen ≤ nodes.size`,
   and no node in `[0, lookupPrefixLen)` reads a public value, a row selector
   (`isFirstRow`, `isLastRow`, `isTransition`), or a stage-2 column.
2. **Base-constraint context (`checkZerosNoStage2`, `checkCompilerContexts`):**
   No node reachable from any user constraint root in `zeros` reads a stage-2 column.
3. **Topological order (`checkTopological`, `SysCircuit.Topological`):**
   Every arithmetic node (`add`, `sub`, `mul`, `neg`) refers strictly to earlier nodes.
4. **Semantic independence (`sweepGraph_prefix_congr_of_lookupsPlain`,
   `lookup_eval_congr_of_checkLookupsPlain`):**
   Whenever `checkTopological c.nodes = true` and `checkLookupsPlain c = true`, evaluating
   `sweepGraph?` on two contexts that agree on `(prepCur, prepNext, mainCur, mainNext)` produces
   identical values for every lookup multiplicity and argument, independent of stage-2 columns,
   public inputs, and row selectors.
-/

namespace Ix.Cert.MultiStark

open CertiFri.P3

/-- Maximum lookup group size supported by the direct LogUp evaluator
(`multi_stark::lookup::MAX_LOOKUP_GROUP`). -/
def MAX_LOOKUP_GROUP : Nat := 8

/-- Public-input width in base coordinates for cubic extension `Fp^3`
(`multi_stark::lookup::num_publics(3) = 4 * 3`). -/
def LOOKUP_NUM_PUBLICS : Nat := 12

/-- Check that every index `i` in `[start, stop)` satisfies `p i`. -/
def allRange (start stop : Nat) (p : Nat → Bool) : Bool :=
  if _ : start < stop then
    p start && allRange (start + 1) stop p
  else
    true
termination_by stop - start

theorem allRange_eq_true_iff (start stop : Nat) (p : Nat → Bool) :
    allRange start stop p = true ↔ ∀ i, start ≤ i → i < stop → p i = true := by
  unfold allRange
  split
  · next h =>
    have ih := allRange_eq_true_iff (start + 1) stop p
    constructor
    · intro hboth i hlo hhi
      simp only [Bool.and_eq_true] at hboth
      if heq : i = start then
        subst heq; exact hboth.1
      else
        exact ih.mp hboth.2 i (by omega) hhi
    · intro hall
      simp only [Bool.and_eq_true]
      exact ⟨hall start (Nat.le_refl _) h, ih.mpr fun i hlo hhi => hall i (by omega) hhi⟩
  · next h =>
    constructor
    · intro _ i hlo hhi; omega
    · intro _; rfl
termination_by stop - start

/-- Whether a `GraphNode` is legal in a lookup expression (`Context::Lookup`):
may read only constants, preprocessed columns, main columns, and arithmetic ops —
never public values, row selectors, or stage-2 columns. -/
def GraphNode.isLookupPlain : GraphNode → Bool
  | .const _ => true
  | .var .preprocessed _ _ => true
  | .var .main _ _ => true
  | .var .stage2 _ _ => false
  | .publicInput _ => false
  | .isFirstRow => false
  | .isLastRow => false
  | .isTransition => false
  | .add _ _ => true
  | .sub _ _ => true
  | .mul _ _ => true
  | .neg _ => true

/-- Proposition that a `GraphNode` is legal in a lookup expression (`Context::Lookup`). -/
def GraphNode.LookupPlain (n : GraphNode) : Prop :=
  n.isLookupPlain = true

/-- Whether all child node indices of `n` lie strictly before `idx`. -/
def GraphNode.childrenInRange (idx : Nat) : GraphNode → Bool
  | .add a b => decide (a < idx) && decide (b < idx)
  | .sub a b => decide (a < idx) && decide (b < idx)
  | .mul a b => decide (a < idx) && decide (b < idx)
  | .neg a => decide (a < idx)
  | _ => true

/-- Proposition that all child indices of `n` lie strictly before `idx`. -/
def GraphNode.ChildrenBefore (idx : Nat) (n : GraphNode) : Prop :=
  n.childrenInRange idx = true

/-- Executable check that every node in `nodes` refers strictly to earlier nodes. -/
def checkTopological (nodes : Array GraphNode) : Bool :=
  allRange 0 nodes.size fun i =>
    match nodes[i]? with
    | some n => n.childrenInRange i
    | none => false

/-- Proposition that every node of `c.nodes` refers strictly to earlier nodes. -/
def SysCircuit.Topological (c : SysCircuit) : Prop :=
  ∀ (i : Nat) (node : GraphNode), c.nodes[i]? = some node → node.ChildrenBefore i

theorem checkTopological_sound {c : SysCircuit} (h : checkTopological c.nodes = true) :
    c.Topological := by
  intro i node hnode
  have hi : i < c.nodes.size := by
    cases Nat.lt_or_ge i c.nodes.size with
    | inl hlt => exact hlt
    | inr hge =>
      rw [Array.getElem?_eq_none hge] at hnode
      cases hnode
  have hall := (allRange_eq_true_iff 0 c.nodes.size _).mp h i (Nat.zero_le _) hi
  rw [hnode] at hall
  exact hall

/-- Proposition that `c` has plain lookups: there is a prefix of `k ≤ c.nodes.size` nodes,
every node in the prefix is `LookupPlain` (reads only constants, preprocessed/main columns, and
arithmetic ops — no public inputs, row selectors, or stage-2 columns), and every lookup's
multiplicity and arguments lie inside the prefix. -/
def SysCircuit.LookupsPlain (c : SysCircuit) : Prop :=
  ∃ k, k ≤ c.nodes.size ∧
    (∀ i < k, ∀ node, c.nodes[i]? = some node → node.LookupPlain) ∧
    (∀ l ∈ c.lookups, l.multiplicity < k ∧ ∀ a ∈ l.args, a < k)

/-- Executable check for `SysCircuit.LookupsPlain` using `c.lookupPrefixLen` as the prefix bound. -/
def checkLookupsPlain (c : SysCircuit) : Bool :=
  decide (c.lookupPrefixLen ≤ c.nodes.size) &&
    allRange 0 c.lookupPrefixLen (fun i =>
      match c.nodes[i]? with
      | some n => n.isLookupPlain
      | none => false) &&
    c.lookups.all fun l =>
      decide (l.multiplicity < c.lookupPrefixLen) &&
        l.args.all fun a => decide (a < c.lookupPrefixLen)

/-- Soundness of the executable `checkLookupsPlain` validator: acceptance implies
`SysCircuit.LookupsPlain`. -/
theorem checkLookupsPlain_sound {c : SysCircuit} (h : checkLookupsPlain c = true) :
    c.LookupsPlain := by
  unfold checkLookupsPlain at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hlen, hnodes⟩, hlookups⟩ := h
  refine ⟨c.lookupPrefixLen, hlen, ?_, ?_⟩
  · intro i hi node hget
    have hp := (allRange_eq_true_iff 0 c.lookupPrefixLen _).mp hnodes i (Nat.zero_le _) hi
    rw [hget] at hp
    exact hp
  · intro l hl
    have hmem : ∀ x ∈ c.lookups,
        (decide (x.multiplicity < c.lookupPrefixLen) &&
          x.args.all fun a => decide (a < c.lookupPrefixLen)) = true :=
      Array.all_eq_true_iff_forall_mem.mp hlookups
    have hl' := hmem l hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hl'
    refine ⟨hl'.1, fun a ha => ?_⟩
    have ha' := Array.all_eq_true_iff_forall_mem.mp hl'.2 a ha
    exact of_decide_eq_true ha'

/-- Descriptive check that every node in `nodes[0..lookupPrefixLen)` is legal in `Context::Lookup`
and every lookup root lies strictly inside `lookupPrefixLen` (`crates/stark-key/src/lib.rs`). -/
def checkLookupPrefix (c : SysCircuit) : Except String Unit := do
  unless c.lookupPrefixLen ≤ c.nodes.size do
    throw s!"lookup_prefix_len {c.lookupPrefixLen} exceeds node_count {c.nodes.size}"
  for i in [0:c.lookupPrefixLen] do
    let some node := c.nodes[i]?
      | throw s!"lookup prefix node {i} out of bounds ({c.nodes.size})"
    match node with
    | .publicInput _ =>
      throw s!"lookup prefix node {i} reads a public value, which a lookup may not read"
    | .isFirstRow | .isLastRow | .isTransition =>
      throw s!"lookup prefix node {i} reads a row selector, which a lookup may not read"
    | .var .stage2 _ _ =>
      throw s!"lookup prefix node {i} reads a stage-2 column, which a lookup may not read"
    | _ => pure ()
  for l in c.lookups do
    unless l.multiplicity < c.lookupPrefixLen do
      throw s!"lookup multiplicity node {l.multiplicity} exceeds lookup_prefix_len {c.lookupPrefixLen}"
    for a in l.args do
      unless a < c.lookupPrefixLen do
        throw s!"lookup arg node {a} exceeds lookup_prefix_len {c.lookupPrefixLen}"

/-- Check that no node reachable from any root in `zeros` reads a stage-2 column
(`crates/stark-key/src/lib.rs`, `check_compiler_contexts`). Assumes `nodes` is topological
(children precede parents), so one descending sweep suffices. -/
def checkZerosNoStage2 (nodes : Array GraphNode) (zeros : Array Nat) : Except String Unit := do
  let mut reached := Array.replicate nodes.size false
  for z in zeros do
    unless z < nodes.size do
      throw s!"zero constraint node id {z} out of bounds ({nodes.size})"
    reached := reached.setIfInBounds z true
  for offset in [0:nodes.size] do
    let id := nodes.size - 1 - offset
    if reached.getD id false then
      match nodes[id]? with
      | some (.var .stage2 _ col) =>
        throw s!"constraint node {id} reads stage-2 column {col}, which a base constraint may not read"
      | some (.add a b) | some (.sub a b) | some (.mul a b) =>
        reached := reached.setIfInBounds a true |>.setIfInBounds b true
      | some (.neg a) =>
        reached := reached.setIfInBounds a true
      | _ => pure ()

/-- Full compiler-context check matching `crates/stark-key/src/lib.rs` (`check_compiler_contexts`):
1. `checkLookupsPlain c` (lookup prefix nodes and lookup roots), with detailed diagnostics;
2. `checkZerosNoStage2 c.nodes c.zeros` (no stage-2 column reachable from any zero root). -/
def checkCompilerContexts (c : SysCircuit) : Except String Unit := do
  checkLookupPrefix c
  unless checkLookupsPlain c do
    throw "circuit failed LookupsPlain check"
  checkZerosNoStage2 c.nodes c.zeros

/-- Boolean wrapper around `checkCompilerContexts`. -/
def compilerContextsOk (c : SysCircuit) : Bool :=
  (checkCompilerContexts c).isOk

theorem checkCompilerContexts_implies_checkLookupsPlain {c : SysCircuit}
    (h : checkCompilerContexts c = .ok ()) : checkLookupsPlain c = true := by
  unfold checkCompilerContexts at h
  cases hp : checkLookupPrefix c with
  | error e => simp [hp, bind, Except.bind] at h
  | ok u =>
    simp only [hp, bind, Except.bind] at h
    cases hlp : checkLookupsPlain c with
    | true => rfl
    | false => simp [hlp, throw, throwThe, MonadExceptOf.throw] at h

theorem checkCompilerContexts_implies_lookupsPlain {c : SysCircuit}
    (h : checkCompilerContexts c = .ok ()) : c.LookupsPlain :=
  checkLookupsPlain_sound (checkCompilerContexts_implies_checkLookupsPlain h)

theorem compilerContextsOk_implies_lookupsPlain {c : SysCircuit}
    (h : compilerContextsOk c = true) : c.LookupsPlain := by
  unfold compilerContextsOk at h
  cases hcc : checkCompilerContexts c with
  | error _ => simp [hcc, Except.isOk, Except.toBool] at h
  | ok u => exact checkCompilerContexts_implies_lookupsPlain hcc

/-! ## Semantic Independence of `sweepGraph?` on Plain Lookup Prefixes -/

/-- Single node evaluation step of `sweepGraph?`, factored out for induction. -/
private def evalStep? (prepCur prepNext mainCur mainNext s2Cur s2Next publics : Array EF)
    (isFirst isLast isTrans : EF) (vals : Array EF) (node : GraphNode) : Option EF :=
  match node with
  | .const c => some (GoldilocksExt3.embed c)
  | .var src off col =>
    let row := match src, off with
      | .preprocessed, .current => prepCur
      | .preprocessed, .next => prepNext
      | .main, .current => mainCur
      | .main, .next => mainNext
      | .stage2, .current => s2Cur
      | .stage2, .next => s2Next
    row[col]?
  | .publicInput idx => publics[idx]?
  | .isFirstRow => some isFirst
  | .isLastRow => some isLast
  | .isTransition => some isTrans
  | .add a b => do
    let va ← vals[a]?
    let vb ← vals[b]?
    pure (va.add vb)
  | .sub a b => do
    let va ← vals[a]?
    let vb ← vals[b]?
    pure (va.sub vb)
  | .mul a b => do
    let va ← vals[a]?
    let vb ← vals[b]?
    pure (va.mul vb)
  | .neg a => do
    let va ← vals[a]?
    pure va.neg

private theorem evalStep?_congr_of_plain
    {prepCur prepNext mainCur mainNext : Array EF}
    {s2Cur₁ s2Next₁ publics₁ s2Cur₂ s2Next₂ publics₂ : Array EF}
    {isFirst₁ isLast₁ isTrans₁ isFirst₂ isLast₂ isTrans₂ : EF}
    {vals₁ vals₂ : Array EF} {idx : Nat} {node : GraphNode}
    (hplain : node.LookupPlain)
    (htopo : node.ChildrenBefore idx)
    (hbuf : ∀ j < idx, vals₁[j]? = vals₂[j]?) :
    evalStep? prepCur prepNext mainCur mainNext s2Cur₁ s2Next₁ publics₁
      isFirst₁ isLast₁ isTrans₁ vals₁ node =
    evalStep? prepCur prepNext mainCur mainNext s2Cur₂ s2Next₂ publics₂
      isFirst₂ isLast₂ isTrans₂ vals₂ node := by
  cases node with
  | const c => rfl
  | var src off col =>
    cases src with
    | preprocessed => cases off <;> rfl
    | main => cases off <;> rfl
    | stage2 => simp [GraphNode.LookupPlain, GraphNode.isLookupPlain] at hplain
  | publicInput _ => simp [GraphNode.LookupPlain, GraphNode.isLookupPlain] at hplain
  | isFirstRow => simp [GraphNode.LookupPlain, GraphNode.isLookupPlain] at hplain
  | isLastRow => simp [GraphNode.LookupPlain, GraphNode.isLookupPlain] at hplain
  | isTransition => simp [GraphNode.LookupPlain, GraphNode.isLookupPlain] at hplain
  | add a b =>
    simp only [GraphNode.ChildrenBefore, GraphNode.childrenInRange, Bool.and_eq_true,
      decide_eq_true_eq] at htopo
    simp only [evalStep?, hbuf a htopo.1, hbuf b htopo.2]
  | sub a b =>
    simp only [GraphNode.ChildrenBefore, GraphNode.childrenInRange, Bool.and_eq_true,
      decide_eq_true_eq] at htopo
    simp only [evalStep?, hbuf a htopo.1, hbuf b htopo.2]
  | mul a b =>
    simp only [GraphNode.ChildrenBefore, GraphNode.childrenInRange, Bool.and_eq_true,
      decide_eq_true_eq] at htopo
    simp only [evalStep?, hbuf a htopo.1, hbuf b htopo.2]
  | neg a =>
    simp only [GraphNode.ChildrenBefore, GraphNode.childrenInRange,
      decide_eq_true_eq] at htopo
    simp only [evalStep?, hbuf a htopo]

private theorem sweepGraph?_eq_foldlM (nodes : Array GraphNode)
    (prepCur prepNext mainCur mainNext s2Cur s2Next publics : Array EF)
    (isFirst isLast isTrans : EF) :
    sweepGraph? nodes prepCur prepNext mainCur mainNext s2Cur s2Next publics
      isFirst isLast isTrans =
    nodes.toList.foldlM (init := Array.mkEmpty nodes.size) (fun vals node => do
      let v ← evalStep? prepCur prepNext mainCur mainNext s2Cur s2Next publics
        isFirst isLast isTrans vals node
      pure (vals.push v)) := by
  have hgen : ∀ (l : List GraphNode) (init : Array EF),
      forIn l init (fun node vals => do
        let v ← evalStep? prepCur prepNext mainCur mainNext s2Cur s2Next publics
          isFirst isLast isTrans vals node
        pure (ForInStep.yield (vals.push v))) =
      l.foldlM (init := init) (fun vals node => do
        let v ← evalStep? prepCur prepNext mainCur mainNext s2Cur s2Next publics
          isFirst isLast isTrans vals node
        pure (vals.push v)) := by
    intro l
    induction l with
    | nil => intro init; rfl
    | cons hd tl ih =>
      intro init
      simp only [List.forIn_cons, List.foldlM_cons, bind, Option.bind]
      cases evalStep? prepCur prepNext mainCur mainNext s2Cur s2Next publics
        isFirst isLast isTrans init hd with
      | none => rfl
      | some v => exact ih (init.push v)
  unfold sweepGraph?
  change (forIn nodes (Array.mkEmpty nodes.size) _ >>= pure) = _
  rw [bind_pure, ← Array.forIn_toList]
  refine Eq.trans ?_ (hgen nodes.toList (Array.mkEmpty nodes.size))
  congr 1
  funext node vals
  cases node with
  | const _ | var _ _ _ | publicInput _ | isFirstRow | isLastRow | isTransition => rfl
  | add a b =>
    simp only [evalStep?, bind, Option.bind, pure]
    cases vals[a]? <;> cases vals[b]? <;> rfl
  | sub a b =>
    simp only [evalStep?, bind, Option.bind, pure]
    cases vals[a]? <;> cases vals[b]? <;> rfl
  | mul a b =>
    simp only [evalStep?, bind, Option.bind, pure]
    cases vals[a]? <;> cases vals[b]? <;> rfl
  | neg a =>
    simp only [evalStep?, bind, Option.bind, pure]
    cases vals[a]? <;> rfl

private theorem foldlM_sweep_prefix_congr
    {prepCur prepNext mainCur mainNext : Array EF}
    {s2Cur₁ s2Next₁ publics₁ s2Cur₂ s2Next₂ publics₂ : Array EF}
    {isFirst₁ isLast₁ isTrans₁ isFirst₂ isLast₂ isTrans₂ : EF}
    (k : Nat) (l : List GraphNode) (vals₁ vals₂ out₁ out₂ : Array EF)
    (hsize : vals₁.size = vals₂.size)
    (hbuf : ∀ i < min vals₁.size k, vals₁[i]? = vals₂[i]?)
    (htopo : ∀ (j : Nat) (node : GraphNode), l[j]? = some node → node.ChildrenBefore (vals₁.size + j))
    (hplain : ∀ (j : Nat), vals₁.size + j < k → ∀ (node : GraphNode), l[j]? = some node → node.LookupPlain)
    (h1 : l.foldlM (init := vals₁) (fun vals node => do
      let v ← evalStep? prepCur prepNext mainCur mainNext s2Cur₁ s2Next₁ publics₁
        isFirst₁ isLast₁ isTrans₁ vals node
      pure (vals.push v)) = some out₁)
    (h2 : l.foldlM (init := vals₂) (fun vals node => do
      let v ← evalStep? prepCur prepNext mainCur mainNext s2Cur₂ s2Next₂ publics₂
        isFirst₂ isLast₂ isTrans₂ vals node
      pure (vals.push v)) = some out₂) :
    ∀ i < min (vals₁.size + l.length) k, out₁[i]? = out₂[i]? := by
  induction l generalizing vals₁ vals₂ with
  | nil =>
    simp only [List.foldlM_nil, pure, Option.some.injEq] at h1 h2
    subst h1; subst h2
    simpa using hbuf
  | cons hd tl ih =>
    simp only [List.foldlM_cons, bind, Option.bind] at h1 h2
    cases hs1 : evalStep? prepCur prepNext mainCur mainNext s2Cur₁ s2Next₁ publics₁
        isFirst₁ isLast₁ isTrans₁ vals₁ hd with
    | none => simp [hs1] at h1
    | some v1 =>
      cases hs2 : evalStep? prepCur prepNext mainCur mainNext s2Cur₂ s2Next₂ publics₂
          isFirst₂ isLast₂ isTrans₂ vals₂ hd with
      | none => simp [hs2] at h2
      | some v2 =>
        simp only [hs1, hs2, pure] at h1 h2
        have hstep := ih (vals₁.push v1) (vals₂.push v2)
          (by simp only [Array.size_push, hsize])
          (by
            intro i hi
            rw [Array.size_push] at hi
            by_cases hilt : i < vals₁.size
            · have hilt₂ : i < vals₂.size := by omega
              rw [Array.getElem?_push_lt hilt, Array.getElem?_push_lt hilt₂]
              have hb := hbuf i (by omega)
              rwa [Array.getElem?_eq_getElem hilt, Array.getElem?_eq_getElem hilt₂] at hb
            · have hieq : i = vals₁.size := by omega
              subst hieq
              rw [Array.getElem?_push_size, hsize, Array.getElem?_push_size]
              have hltK : vals₁.size < k := by omega
              have hpl : hd.LookupPlain := hplain 0 (by omega) hd rfl
              have htp : hd.ChildrenBefore vals₁.size := by
                simpa using htopo 0 hd rfl
              have heqStep := evalStep?_congr_of_plain
                (prepCur := prepCur) (prepNext := prepNext)
                (mainCur := mainCur) (mainNext := mainNext)
                (s2Cur₁ := s2Cur₁) (s2Next₁ := s2Next₁) (publics₁ := publics₁)
                (s2Cur₂ := s2Cur₂) (s2Next₂ := s2Next₂) (publics₂ := publics₂)
                (isFirst₁ := isFirst₁) (isLast₁ := isLast₁) (isTrans₁ := isTrans₁)
                (isFirst₂ := isFirst₂) (isLast₂ := isLast₂) (isTrans₂ := isTrans₂)
                hpl htp (fun j hj => hbuf j (by omega))
              rw [hs1, hs2] at heqStep
              exact heqStep)
          (by
            intro j node hnode
            rw [Array.size_push]
            have h := htopo (j + 1) node (by simpa using hnode)
            have heq : vals₁.size + (j + 1) = vals₁.size + 1 + j := by omega
            rwa [← heq])
          (by
            intro j hj node hnode
            rw [Array.size_push] at hj
            exact hplain (j + 1) (by omega) node (by simpa using hnode))
          h1 h2
        intro i hi
        refine hstep i ?_
        rw [Array.size_push]
        simp only [List.length_cons] at hi
        omega

/-- **Prefix Congruence of `sweepGraph?` under `Topological` and `LookupsPlain`:**
If `c` is topological and its first `k ≤ c.nodes.size` nodes are `LookupPlain`, then evaluating
`sweepGraph?` on two contexts that share `(prepCur, prepNext, mainCur, mainNext)` produces
identical values on every node `i < k`, independent of stage-2 columns, public inputs, and
row selectors. -/
theorem sweepGraph_prefix_congr_of_lookupsPlain {c : SysCircuit}
    (htopo : c.Topological)
    {k : Nat} (hk : k ≤ c.nodes.size)
    (hplain : ∀ i < k, ∀ node, c.nodes[i]? = some node → node.LookupPlain)
    {prepCur prepNext mainCur mainNext : Array EF}
    {s2Cur₁ s2Next₁ publics₁ s2Cur₂ s2Next₂ publics₂ : Array EF}
    {isFirst₁ isLast₁ isTrans₁ isFirst₂ isLast₂ isTrans₂ : EF}
    {vals₁ vals₂ : Array EF}
    (h1 : sweepGraph? c.nodes prepCur prepNext mainCur mainNext s2Cur₁ s2Next₁ publics₁
      isFirst₁ isLast₁ isTrans₁ = some vals₁)
    (h2 : sweepGraph? c.nodes prepCur prepNext mainCur mainNext s2Cur₂ s2Next₂ publics₂
      isFirst₂ isLast₂ isTrans₂ = some vals₂) :
    ∀ i < k, vals₁[i]? = vals₂[i]? := by
  rw [sweepGraph?_eq_foldlM] at h1 h2
  have hsz : (Array.mkEmpty (α := EF) c.nodes.size).size = 0 := rfl
  have hres := foldlM_sweep_prefix_congr k c.nodes.toList
    (Array.mkEmpty c.nodes.size) (Array.mkEmpty c.nodes.size) vals₁ vals₂
    rfl
    (fun i hi => by simp only [hsz, Nat.zero_min] at hi; exact absurd hi (Nat.not_lt_zero _))
    (fun j node hnode => by
      rw [hsz, Nat.zero_add]
      rw [Array.getElem?_toList] at hnode
      exact htopo j node hnode)
    (fun j hj node hnode => by
      rw [hsz, Nat.zero_add] at hj
      rw [Array.getElem?_toList] at hnode
      exact hplain j hj node hnode)
    h1 h2
  intro i hi
  refine hres i ?_
  rw [hsz, Nat.zero_add, Array.length_toList]
  omega

/-- **Lookup-Evaluation Independence from `checkTopological` + `checkLookupsPlain`:**
For any circuit passing the executable checks `checkTopological` and `checkLookupsPlain`,
every lookup's multiplicity and arguments evaluate identically under `sweepGraph?` for any
two contexts sharing `(prepCur, prepNext, mainCur, mainNext)` — completely independent of
stage-2 columns, public values (`β, γ, accPrev, accNext`), and row selectors. -/
theorem lookup_eval_congr_of_checkLookupsPlain {c : SysCircuit}
    (htopo : checkTopological c.nodes = true)
    (hlp : checkLookupsPlain c = true)
    {prepCur prepNext mainCur mainNext : Array EF}
    {s2Cur₁ s2Next₁ publics₁ s2Cur₂ s2Next₂ publics₂ : Array EF}
    {isFirst₁ isLast₁ isTrans₁ isFirst₂ isLast₂ isTrans₂ : EF}
    {vals₁ vals₂ : Array EF}
    (h1 : sweepGraph? c.nodes prepCur prepNext mainCur mainNext s2Cur₁ s2Next₁ publics₁
      isFirst₁ isLast₁ isTrans₁ = some vals₁)
    (h2 : sweepGraph? c.nodes prepCur prepNext mainCur mainNext s2Cur₂ s2Next₂ publics₂
      isFirst₂ isLast₂ isTrans₂ = some vals₂) :
    ∀ l ∈ c.lookups,
      vals₁[l.multiplicity]? = vals₂[l.multiplicity]? ∧
      ∀ a ∈ l.args, vals₁[a]? = vals₂[a]? := by
  obtain ⟨k, hk, hnodes, hlookups⟩ := checkLookupsPlain_sound hlp
  have hpre := sweepGraph_prefix_congr_of_lookupsPlain (checkTopological_sound htopo) hk hnodes h1 h2
  intro l hl
  obtain ⟨hm, hargs⟩ := hlookups l hl
  exact ⟨hpre l.multiplicity hm, fun a ha => hpre a (hargs a ha)⟩

end Ix.Cert.MultiStark
