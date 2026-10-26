import IxSharingVerify.CanonicalMeaning
import IxSharingVerify.UniformFinal
import IxSharingVerify.BudgetMono
import IxC.Kernel.Audit.Axioms

/-! Canonical renumbering never refuses its production input.

`canonicalize` places each height group in key order and refuses a group
whose keys do not strictly increase. On the interner's output (`Run`: children
first, roots in range, reachable nodes hash-consed) two distinct nodes of one
group always have distinct keys, since equal keys over the already-placed
children would denote the same term. So the check passes at every height and
canonicalization succeeds. -/

namespace Ix.Sharing.Verify.CanonicalMeaning

open Ix.Sharing.Exact Ix.Sharing.Verify.SharingExact Ix.Sharing.Verify.Ingestion

theorem keysIncreasing_of_pairwise : ∀ (ns : List Node),
    ns.Pairwise (fun a b => Node.compareKey a b = .lt) → ∀ (prev : Option Node),
      (∀ p, prev = some p → ∀ x ∈ ns, Node.compareKey p x = .lt) → keysIncreasing prev ns = true
  | [], _, _, _ => rfl
  | n :: ns, pw, prev, first => by
    simp only [keysIncreasing, Bool.and_eq_true]
    refine ⟨?_, keysIncreasing_of_pairwise ns (List.pairwise_cons.mp pw).2 (some n) ?_⟩
    · cases prev with
      | none => rfl
      | some p =>
        show (Node.compareKey p n == .lt) = true
        rw [first p rfl n List.mem_cons_self]
        rfl
    · intro p hp x hx
      cases hp
      exact (List.pairwise_cons.mp pw).1 x hx

/-- A height group whose items are ready to place has strictly increasing
keys: its nodes are distinct and sorted by the key order. -/
theorem sortedGroup_keysIncreasing (source : Array Node) (roots : Array Nat) (run : Run source roots)
    (state : State) (height : Nat) (bucket : Array Nat) (atHeight : BucketAt source roots height bucket)
    (ready : ∀ item ∈ sortedGroup source state.1 bucket, Ready source state item) :
    keysIncreasing none ((sortedGroup source state.1 bucket).map (·.2)) = true := by
  apply keysIncreasing_of_pairwise _ _ none (fun _ h => by cases h)
  rw [sortedGroup_nodes]
  have sorted := List.pairwise_mergeSort (le := keyLe)
    (fun a b c h₁ h₂ => keyLe_trans a b c h₁ h₂) (fun a b => keyLe_total a b)
    (bucket.toList.map (keyOf source state.1))
  have injective : ∀ x ∈ bucket.toList, ∀ y ∈ bucket.toList,
      keyOf source state.1 x = keyOf source state.1 y → x = y := by
    intro x hx y hy same
    have readyX := ready (x, keyOf source state.1 x)
      ((sortedGroup_perm source state.1 bucket).mem_iff.mpr (List.mem_map_of_mem hx))
    have readyY := ready (y, keyOf source state.1 y)
      ((sortedGroup_perm source state.1 bucket).mem_iff.mpr (List.mem_map_of_mem hy))
    have mx : (keyOf source state.1 x).toExpr (termOf state.2) = termOf source x := readyX.meaning
    have my : (keyOf source state.1 y).toExpr (termOf state.2) = termOf source y := readyY.meaning
    have meaning : termOf source x = termOf source y := by
      rw [← mx, ← my, same]
    exact run.hashConsed x y ((mem_bucket run atHeight x).mp hx).1
      ((mem_bucket run atHeight y).mp hy).1 meaning
  have distinct : ((bucket.toList.map (keyOf source state.1)).mergeSort keyLe).Nodup :=
    (List.mergeSort_perm _ _).nodup_iff.mpr (nodup_map_on injective (bucket_nodup atHeight))
  refine (sorted.and distinct).imp ?_
  intro a b ⟨le, ne⟩
  unfold keyLe at le
  cases h : Node.compareKey a b with
  | lt => rfl
  | eq => exact absurd ((compareKey_eq_iff a b).mp h) ne
  | gt => rw [h] at le; cases le

theorem exists_ok_of_bind {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {a : α}
    (hx : x = .ok a) (hf : ∃ b, f a = .ok b) : ∃ b, (x >>= f) = .ok b := by
  obtain ⟨b, hb⟩ := hf
  exact ⟨b, by rw [hx]; exact hb⟩

/-- Canonical renumbering succeeds on the interner's output. -/
theorem canonicalize_ok {source : Array Node} {roots : Array Nat} (run : Run source roots) :
    ∃ out, canonicalize source roots = .ok out := by
  let maximum := maxHeight (reachMarks source roots) (nodeHeights source) source.size
  let buckets := heightBuckets (reachMarks source roots) (nodeHeights source) maximum source.size
  have upper := (maxHeight_spec (reachMarks source roots) (nodeHeights source) source.size).1
  have fold : ∀ count start, start + count ≤ maximum + 1 → ∀ before,
      Invariant source roots start before →
      ∃ after, (List.range' start count).foldlM (fun st h => placeBucket source st buckets[h]!) before =
        .ok after := by
    intro count
    induction count with
    | zero => intro start _ before _; exact ⟨before, rfl⟩
    | succ count ih =>
      intro start bound before valid
      rw [List.range'_succ, List.foldlM_cons]
      have atHeight : BucketAt source roots start buckets[start]! :=
        (heightBuckets_spec _ _ maximum source.size upper).2 start (by omega)
      have ready : ∀ item ∈ sortedGroup source before.1 buckets[start]!, Ready source before item := by
        intro item member
        have fromBucket := (sortedGroup_perm source before.1 buckets[start]!).mem_iff.mp member
        obtain ⟨index, indexMember, same⟩ := List.mem_map.mp fromBucket
        subst item
        have properties := (mem_bucket run atHeight index).mp indexMember
        exact key_ready source roots run start before valid index properties.1 properties.2
      have increasing := sortedGroup_keysIncreasing source roots run before start _ atHeight ready
      have placed : placeBucket source before buckets[start]! =
          .ok (placeFold (sortedGroup source before.1 buckets[start]!) before) := by
        rw [placeBucket_eq, placeSorted_eq, ite_eq_left increasing]
      have middleValid :=
        placeBucket_correct source roots run start _ atHeight before _ valid placed
      obtain ⟨after, ran⟩ := ih (start + 1) (by omega) _ middleValid
      exact ⟨after, by rw [placed]; exact ran⟩
  obtain ⟨state, folded⟩ := fold (maximum + 1) 0 (by omega) _ (invariant_initial source roots)
  rw [canonicalize_eq run]
  have ran : (List.range (maximum + 1)).foldlM (fun st h => placeBucket source st buckets[h]!)
      (Array.replicate source.size 0, #[]) = .ok state := by
    rw [List.range_eq_range']
    exact folded
  exact exists_ok_of_bind ran ⟨_, rfl⟩


/-! ## Share-free ingestion within its budgets -/

/-- No `Share` leaf. -/
def ShareFree : Ixon.Expr → Prop
  | .prj _ _ value => ShareFree value
  | .app fn arg => ShareFree fn ∧ ShareFree arg
  | .lam _ type body => ShareFree type ∧ ShareFree body
  | .all _ _ type body => ShareFree type ∧ ShareFree body
  | .letE _ type value body => ShareFree type ∧ ShareFree value ∧ ShareFree body
  | .share _ => False
  | _ => True

/-- Nodes of the expression tree. -/
def nodeCount : Ixon.Expr → Nat
  | .prj _ _ value => nodeCount value + 1
  | .app fn arg => nodeCount fn + nodeCount arg + 1
  | .lam _ type body => nodeCount type + nodeCount body + 1
  | .all _ _ type body => nodeCount type + nodeCount body + 1
  | .letE _ type value body => nodeCount type + nodeCount value + nodeCount body + 1
  | _ => 1

/-- Edges on the longest root-to-leaf path. -/
def treeHeight : Ixon.Expr → Nat
  | .prj _ _ value => treeHeight value + 1
  | .app fn arg => max (treeHeight fn) (treeHeight arg) + 1
  | .lam _ type body => max (treeHeight type) (treeHeight body) + 1
  | .all _ _ type body => max (treeHeight type) (treeHeight body) + 1
  | .letE _ type value body => max (treeHeight type) (max (treeHeight value) (treeHeight body)) + 1
  | _ => 0

theorem intern_size (s : Interner) (node : Node) : (s.intern node).1.nodes.size ≤ s.nodes.size + 1 := by
  unfold Interner.intern
  split <;> simp

theorem run_bind_ok {α β : Type} {x : IngestM α} {f : α → IngestM β} {before middle : IngestState}
    {a : α} (h : x.run before = .ok (a, middle)) : (x >>= f).run before = (f a).run middle := by
  rw [StateT.run_bind, h]
  rfl

/-- One node fits when the node budget has room for it. -/
theorem internNode_ok (limits : Limits) (node : Node) (before : IngestState)
    (room : before.interner.nodes.size + 1 ≤ limits.maxNodes) :
    ∃ id after, (internNode limits node).run before = .ok (id, after) ∧ after.visits = before.visits ∧
      after.interner.nodes.size ≤ before.interner.nodes.size + 1 := by
  have size := intern_size before.interner node
  unfold internNode
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases step : before.interner.intern node with
  | mk interner actual =>
    rw [step] at size
    simp only at size
    simp only [show ¬ interner.nodes.size > limits.maxNodes by omega, ↓reduceIte]
    exact ⟨actual, { before with interner }, rfl, rfl, size⟩

theorem bump_ok' {count n limit : Nat} {r : Resource} (h : count + n ≤ limit) :
    bump count n limit r = .ok (count + n) := by
  unfold bump
  simp only [show ¬ count + n > limit by omega, ↓reduceIte]

/-- A cache hit returns at once; a miss within the depth and visit budgets
runs the body on the counted state and records the result. -/
theorem cached_ok (limits : Limits) (depth : Nat) (source : Ixon.Expr) (body : IngestM Nat)
    (before : IngestState) (k : Nat) (deep : depth ≤ limits.maxDepth)
    (visit : before.visits + 1 ≤ limits.maxExprVisits)
    (bodyOk : ∃ id after, body.run { before with visits := before.visits + 1 } = .ok (id, after) ∧
      after.visits ≤ before.visits + k ∧ after.interner.nodes.size ≤ before.interner.nodes.size + k) :
    ∃ id after, (cached limits depth source body).run before = .ok (id, after) ∧
      after.visits ≤ before.visits + k ∧ after.interner.nodes.size ≤ before.interner.nodes.size + k := by
  unfold cached
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases found : before.ptrCache.get? (exprKey source) with
  | some actual => exact ⟨actual, before, rfl, by omega, by omega⟩
  | none =>
    simp only [show ¬ depth > limits.maxDepth by omega, ↓reduceIte, StateT.run_bind,
      StateT.run_get, pure_bind]
    rw [bump_ok' visit]
    obtain ⟨id, after, ran, visits, nodes⟩ := bodyOk
    refine ⟨id, { after with ptrCache := after.ptrCache.insert (exprKey source) id }, ?_, visits, nodes⟩
    change ((body.run { before with visits := before.visits + 1 }) >>= fun (value, state) =>
      Except.ok (value, { state with ptrCache := state.ptrCache.insert (exprKey source) value })) = _
    rw [ran]
    rfl

theorem counted_visits (before : IngestState) :
    ({ before with visits := before.visits + 1 } : IngestState).visits = before.visits + 1 := rfl

theorem counted_nodes (before : IngestState) :
    ({ before with visits := before.visits + 1 } : IngestState).interner.nodes.size =
      before.interner.nodes.size := rfl

/-- A leaf interned on the counted state stays within one visit and one node. -/
theorem internNode_leaf (limits : Limits) (node : Node) (before : IngestState)
    (room : before.interner.nodes.size + 1 ≤ limits.maxNodes) :
    ∃ id after, (internNode limits node).run { before with visits := before.visits + 1 } =
        .ok (id, after) ∧
      after.visits ≤ before.visits + 1 ∧ after.interner.nodes.size ≤ before.interner.nodes.size + 1 := by
  have cv := counted_visits before
  have cn := counted_nodes before
  obtain ⟨id, after, ran, v, n⟩ :=
    internNode_ok limits node { before with visits := before.visits + 1 } (by omega)
  exact ⟨id, after, ran, by omega, by omega⟩

/-- Ingestion of an expression whose Shares resolve succeeds when the
depth, visit and node budgets cover its tree; it then uses at most one visit and one node per
tree node. -/
theorem ingestExpr_ok (limits : Limits) (context : ShareCtx) :
    ∀ (source : Ixon.Expr) (depth : Nat) (before : IngestState), SharesValid context source →
      depth + treeHeight source ≤ limits.maxDepth →
      before.visits + nodeCount source ≤ limits.maxExprVisits →
      before.interner.nodes.size + nodeCount source ≤ limits.maxNodes →
      ∃ id after, (ingestExpr limits context depth source).run before = .ok (id, after) ∧
        after.visits ≤ before.visits + nodeCount source ∧
        after.interner.nodes.size ≤ before.interner.nodes.size + nodeCount source := by
  intro source
  induction source with
  | prj index field value ih =>
    intro depth before free deep visits nodes
    simp only [SharesValid, nodeCount, treeHeight] at free deep visits nodes ⊢
    have cv := counted_visits before
    have cn := counted_nodes before
    rw [ingestExpr_eq]
    apply cached_ok limits depth _ _ before _ (by omega) (by omega)
    simp only [ingestBody]
    obtain ⟨i1, s1, r1, v1, n1⟩ := ih (depth + 1) { before with visits := before.visits + 1 } free
      (by omega) (by omega) (by omega)
    obtain ⟨i2, s2, r2, v2, n2⟩ := internNode_ok limits ⟨.prj index field, #[i1]⟩ s1 (by omega)
    exact ⟨i2, s2, by rw [run_bind_ok r1]; exact r2, by omega, by omega⟩
  | app fn arg fnIh argIh =>
    intro depth before free deep visits nodes
    simp only [SharesValid, nodeCount, treeHeight] at free deep visits nodes ⊢
    have cv := counted_visits before
    have cn := counted_nodes before
    rw [ingestExpr_eq]
    apply cached_ok limits depth _ _ before _ (by omega) (by omega)
    simp only [ingestBody]
    obtain ⟨i1, s1, r1, v1, n1⟩ := fnIh (depth + 1) { before with visits := before.visits + 1 } free.1
      (by omega) (by omega) (by omega)
    obtain ⟨i2, s2, r2, v2, n2⟩ := argIh (depth + 1) s1 free.2 (by omega) (by omega) (by omega)
    obtain ⟨i3, s3, r3, v3, n3⟩ := internNode_ok limits ⟨.app, #[i1, i2]⟩ s2 (by omega)
    exact ⟨i3, s3, by rw [run_bind_ok r1, run_bind_ok r2]; exact r3, by omega, by omega⟩
  | lam contract type body typeIh bodyIh =>
    intro depth before free deep visits nodes
    simp only [SharesValid, nodeCount, treeHeight] at free deep visits nodes ⊢
    have cv := counted_visits before
    have cn := counted_nodes before
    rw [ingestExpr_eq]
    apply cached_ok limits depth _ _ before _ (by omega) (by omega)
    simp only [ingestBody]
    obtain ⟨i1, s1, r1, v1, n1⟩ := typeIh (depth + 1) { before with visits := before.visits + 1 }
      free.1 (by omega) (by omega) (by omega)
    obtain ⟨i2, s2, r2, v2, n2⟩ := bodyIh (depth + 1) s1 free.2 (by omega) (by omega) (by omega)
    obtain ⟨i3, s3, r3, v3, n3⟩ := internNode_ok limits ⟨.lam contract, #[i1, i2]⟩ s2 (by omega)
    exact ⟨i3, s3, by rw [run_bind_ok r1, run_bind_ok r2]; exact r3, by omega, by omega⟩
  | all contract result type body typeIh bodyIh =>
    intro depth before free deep visits nodes
    simp only [SharesValid, nodeCount, treeHeight] at free deep visits nodes ⊢
    have cv := counted_visits before
    have cn := counted_nodes before
    rw [ingestExpr_eq]
    apply cached_ok limits depth _ _ before _ (by omega) (by omega)
    simp only [ingestBody]
    obtain ⟨i1, s1, r1, v1, n1⟩ := typeIh (depth + 1) { before with visits := before.visits + 1 }
      free.1 (by omega) (by omega) (by omega)
    obtain ⟨i2, s2, r2, v2, n2⟩ := bodyIh (depth + 1) s1 free.2 (by omega) (by omega) (by omega)
    obtain ⟨i3, s3, r3, v3, n3⟩ :=
      internNode_ok limits ⟨.all contract result, #[i1, i2]⟩ s2 (by omega)
    exact ⟨i3, s3, by rw [run_bind_ok r1, run_bind_ok r2]; exact r3, by omega, by omega⟩
  | letE contract type value body typeIh valueIh bodyIh =>
    intro depth before free deep visits nodes
    simp only [SharesValid, nodeCount, treeHeight] at free deep visits nodes ⊢
    have cv := counted_visits before
    have cn := counted_nodes before
    rw [ingestExpr_eq]
    apply cached_ok limits depth _ _ before _ (by omega) (by omega)
    simp only [ingestBody]
    obtain ⟨i1, s1, r1, v1, n1⟩ := typeIh (depth + 1) { before with visits := before.visits + 1 }
      free.1 (by omega) (by omega) (by omega)
    obtain ⟨i2, s2, r2, v2, n2⟩ := valueIh (depth + 1) s1 free.2.1 (by omega) (by omega) (by omega)
    obtain ⟨i3, s3, r3, v3, n3⟩ := bodyIh (depth + 1) s2 free.2.2 (by omega) (by omega) (by omega)
    obtain ⟨i4, s4, r4, v4, n4⟩ := internNode_ok limits ⟨.letE contract, #[i1, i2, i3]⟩ s3 (by omega)
    exact ⟨i4, s4, by rw [run_bind_ok r1, run_bind_ok r2, run_bind_ok r3]; exact r4, by omega,
      by omega⟩
  | share index =>
    intro depth before free deep visits nodes
    simp only [SharesValid, nodeCount, treeHeight] at free deep visits nodes ⊢
    obtain ⟨id, resolved⟩ := free
    rw [ingestExpr_eq]
    apply cached_ok limits depth _ _ before _ (by omega) (by omega)
    refine ⟨id, { before with visits := before.visits + 1 }, ?_, by simp, by simp⟩
    simp only [ingestBody, resolved]
    rfl
  | sort index =>
    intro depth before _ deep visits nodes
    simp only [nodeCount, treeHeight] at deep visits nodes ⊢
    rw [ingestExpr_eq]
    exact cached_ok limits depth _ _ before _ (by omega) (by omega)
      (internNode_leaf limits _ before (by omega))
  | var index =>
    intro depth before _ deep visits nodes
    simp only [nodeCount, treeHeight] at deep visits nodes ⊢
    rw [ingestExpr_eq]
    exact cached_ok limits depth _ _ before _ (by omega) (by omega)
      (internNode_leaf limits _ before (by omega))
  | ref index levels =>
    intro depth before _ deep visits nodes
    simp only [nodeCount, treeHeight] at deep visits nodes ⊢
    rw [ingestExpr_eq]
    exact cached_ok limits depth _ _ before _ (by omega) (by omega)
      (internNode_leaf limits _ before (by omega))
  | recur index levels =>
    intro depth before _ deep visits nodes
    simp only [nodeCount, treeHeight] at deep visits nodes ⊢
    rw [ingestExpr_eq]
    exact cached_ok limits depth _ _ before _ (by omega) (by omega)
      (internNode_leaf limits _ before (by omega))
  | str index =>
    intro depth before _ deep visits nodes
    simp only [nodeCount, treeHeight] at deep visits nodes ⊢
    rw [ingestExpr_eq]
    exact cached_ok limits depth _ _ before _ (by omega) (by omega)
      (internNode_leaf limits _ before (by omega))
  | nat index =>
    intro depth before _ deep visits nodes
    simp only [nodeCount, treeHeight] at deep visits nodes ⊢
    rw [ingestExpr_eq]
    exact cached_ok limits depth _ _ before _ (by omega) (by omega)
      (internNode_leaf limits _ before (by omega))

/-! ## The canonical DAG is reachable from its roots -/

open Ix.Sharing.Verify.UniformModel (desc_snoc dag_node_eq)

theorem append_getElem!_left {α : Type} [Inhabited α] (a b : Array α) {k : Nat} (hk : k < a.size) :
    (a ++ b)[k]! = a[k]! := by
  rw [getElem!_pos (a ++ b) k (by simp; omega), Array.getElem_append_left hk, getElem!_pos a k hk]

theorem append_getElem!_right {α : Type} [Inhabited α] (a b : Array α) {i : Nat} (hi : i < b.size) :
    (a ++ b)[a.size + i]! = b[i]! := by
  rw [getElem!_pos (a ++ b) (a.size + i) (by simp; omega), getElem!_pos b i hi,
    Array.getElem_append_right (by omega)]
  simp

/-- Placed output nodes and their source nodes, after the heights below `height`. -/
structure Shaped (source : Array Node) (roots : Array Nat) (height : Nat) (canon : Array Nat)
    (store : Array Node) : Prop where
  forward : ∀ t, Reach source roots t → (nodeHeights source)[t]! < height →
    canon[t]! < store.size ∧ store[canon[t]!]! = keyOf source canon t
  backward : ∀ k, k < store.size →
    ∃ t, Reach source roots t ∧ (nodeHeights source)[t]! < height ∧ canon[t]! = k

theorem keyOf_congr {source : Array Node} {a b : Array Nat} {t : Nat}
    (same : ∀ c ∈ (source[t]!).children, a[c]! = b[c]!) : keyOf source a t = keyOf source b t := by
  have children : (source[t]!).children.map (a[·]!) = (source[t]!).children.map (b[·]!) := by
    apply Array.ext (by simp)
    intro i hi _
    simp only [Array.getElem_map]
    exact same _ (Array.getElem_mem (by simpa using hi))
  unfold keyOf
  rw [children]

theorem shaped_initial (source : Array Node) (roots : Array Nat) :
    Shaped source roots 0 (Array.replicate source.size 0) #[] :=
  ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (by simp)⟩

theorem shaped_step (source : Array Node) (roots : Array Nat) (run : Run source roots)
    (height : Nat) (canon : Array Nat) (store : Array Node) (bucket : Array Nat)
    (atHeight : BucketAt source roots height bucket) (sizeEq : canon.size = source.size)
    (shaped : Shaped source roots height canon store) :
    Shaped source roots (height + 1) (placeFold (sortedGroup source canon bucket) (canon, store)).1
      (placeFold (sortedGroup source canon bucket) (canon, store)).2 := by
  have fstPerm := sortedGroup_fst_perm source canon bucket
  have nodup := fstPerm.nodup_iff.mpr (bucket_nodup atHeight)
  have bounded : ∀ x ∈ sortedGroup source canon bucket, x.1 < canon.size :=
    sortedGroup_fst_lt run atHeight canon sizeEq
  have itemKey : ∀ x ∈ sortedGroup source canon bucket, x.2 = keyOf source canon x.1 := by
    intro x member
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp ((sortedGroup_perm source canon bucket).subset member)
    rfl
  generalize sortedGroup source canon bucket = l at fstPerm nodup bounded itemKey ⊢
  obtain ⟨out, _, other, placed⟩ := placeFold_spec l canon store nodup bounded
  have inL : ∀ t, t ∈ bucket.toList → ∃ i, ∃ hi : i < l.length, l[i].1 = t := by
    intro t ht
    obtain ⟨x, xm, rfl⟩ := List.mem_map.mp (fstPerm.symm.subset ht)
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp xm
    exact ⟨i, hi, rfl⟩
  have notIn : ∀ t, (nodeHeights source)[t]! < height → t ∉ l.map (·.1) := by
    intro t below member
    have := ((mem_bucket run atHeight t).mp (fstPerm.subset member)).2
    omega
  have keyKeep : ∀ t, Reach source roots t → (nodeHeights source)[t]! ≤ height →
      keyOf source (placeFold l (canon, store)).1 t = keyOf source canon t := by
    intro t reach atMost
    apply keyOf_congr
    intro c member
    have bound := reach_lt run.cp run.inRange reach
    have lt := child_height_lt source (nodeHeights source) t c member
    rw [← nodeHeights_spec run.cp t bound] at lt
    exact other c (notIn c (by omega))
  rw [out]
  refine ⟨?_, ?_⟩
  · intro t reach below
    by_cases old : (nodeHeights source)[t]! < height
    · obtain ⟨slot, node⟩ := shaped.forward t reach old
      rw [other t (notIn t old)]
      refine ⟨by simp; omega, ?_⟩
      rw [append_getElem!_left _ _ slot, node, keyKeep t reach (by omega)]
    · have exact : (nodeHeights source)[t]! = height := by omega
      have member : t ∈ bucket.toList := (mem_bucket run atHeight t).mpr ⟨reach, exact⟩
      obtain ⟨i, hi, hit⟩ := inL t member
      have slotEq := placed i hi
      rw [hit] at slotEq
      rw [slotEq]
      refine ⟨by simp; omega, ?_⟩
      rw [append_getElem!_right _ _ (by simpa using hi), keyKeep t reach (by omega),
        getElem!_pos _ i (by simpa using hi)]
      simp only [List.getElem_toArray, List.getElem_map]
      rw [itemKey _ (List.getElem_mem hi), hit]
  · intro k hk
    simp only [Array.size_append, List.size_toArray, List.length_map] at hk
    by_cases old : k < store.size
    · obtain ⟨t, reach, below, slot⟩ := shaped.backward k old
      exact ⟨t, reach, by omega, by rw [other t (notIn t below)]; exact slot⟩
    · obtain ⟨i, rfl⟩ : ∃ i, k = store.size + i := ⟨k - store.size, by omega⟩
      have hi : i < l.length := by omega
      have lmem : l[i].1 ∈ bucket.toList :=
        fstPerm.subset (List.mem_map_of_mem (f := (·.1)) (List.getElem_mem hi))
      obtain ⟨reach, exact⟩ := (mem_bucket run atHeight _).mp lmem
      exact ⟨l[i].1, reach, by omega, placed i hi⟩

/-- The state after the last height of a successful `canonicalize`: every
reachable source node is placed with its term, every placed node comes from
a reachable source node, and the DAG and roots are read from it. -/
theorem canonicalize_final {source : Array Node} {roots : Array Nat} (run : Run source roots)
    {dag : Dag} {out : Array Nat} (ran : canonicalize source roots = .ok (dag, out)) :
    ∃ (height : Nat) (state : State), dag = ⟨state.2⟩ ∧ out = roots.map (state.1[·]!) ∧
      Invariant source roots height state ∧ Shaped source roots height state.1 state.2 ∧
      ∀ t, Reach source roots t → (nodeHeights source)[t]! < height := by
  let maximum := maxHeight (reachMarks source roots) (nodeHeights source) source.size
  let buckets := heightBuckets (reachMarks source roots) (nodeHeights source) maximum source.size
  have upper := (maxHeight_spec (reachMarks source roots) (nodeHeights source) source.size).1
  rw [canonicalize_eq run] at ran
  obtain ⟨state, folded, finished⟩ := bind_eq_ok ran
  change Except.ok ((⟨state.2⟩ : Dag), roots.map (state.1[·]!)) = .ok (dag, out) at finished
  obtain ⟨dagEq, outEq⟩ := Prod.mk.inj (Except.ok.inj finished)
  change (List.range (maximum + 1)).foldlM (fun st h => placeBucket source st buckets[h]!)
    (Array.replicate source.size 0, #[]) = .ok state at folded
  rw [List.range_eq_range'] at folded
  have step : ∀ height, height < maximum + 1 → ∀ before : State,
      (Invariant source roots height before ∧ Shaped source roots height before.1 before.2) →
      ∀ after, placeBucket source before buckets[height]! = .ok after →
        Invariant source roots (height + 1) after ∧ Shaped source roots (height + 1) after.1 after.2 := by
    intro height below before ⟨valid, shaped⟩ after stepRan
    have atHeight : BucketAt source roots height buckets[height]! :=
      (heightBuckets_spec _ _ maximum source.size upper).2 height (by omega)
    refine ⟨placeBucket_correct source roots run height _ atHeight before after valid stepRan, ?_⟩
    rw [placeBucket_eq, placeSorted_eq] at stepRan
    split at stepRan
    · cases Except.ok.inj stepRan
      exact shaped_step source roots run height before.1 before.2 _ atHeight valid.size shaped
    · cases stepRan
  have final := fold_heights _
    (fun h (st : State) => Invariant source roots h st ∧ Shaped source roots h st.1 st.2)
    (maximum + 1) step (maximum + 1) 0 (by omega) _
    ⟨invariant_initial source roots, shaped_initial source roots⟩ state folded
  simp only [Nat.zero_add] at final
  refine ⟨maximum + 1, state, dagEq.symm, outEq.symm, final.1, final.2, fun t reach => ?_⟩
  have bound := reach_lt run.cp run.inRange reach
  have marked := (reachMarks_spec run.cp run.inRange t bound).mpr reach
  exact Nat.lt_succ_of_le (upper t bound marked)

/-- Every node of the canonical DAG is reachable from its roots. -/
theorem canonicalize_reach {source : Array Node} {roots : Array Nat} (run : Run source roots)
    {dag : Dag} {out : Array Nat} (ran : canonicalize source roots = .ok (dag, out)) :
    ∀ k, k < dag.size → ∃ r ∈ out.toList, Desc dag r k := by
  obtain ⟨height, state, rfl, rfl, _, shaped, below⟩ := canonicalize_final run ran
  have descends : ∀ t, Reach source roots t →
      ∃ r ∈ (roots.map (state.1[·]!)).toList, Desc (⟨state.2⟩ : Dag) r state.1[t]! := by
    intro t reach
    induction reach with
    | @root t member =>
      refine ⟨state.1[t]!, ?_, .refl _⟩
      rw [Array.toList_map]
      exact List.mem_map.mpr ⟨t, Array.mem_toList_iff.mpr member, rfl⟩
    | @child t c reach member ih =>
      obtain ⟨r, rm, d⟩ := ih
      obtain ⟨slot, node⟩ := shaped.forward t reach (below t reach)
      have nodeEq : Dag.node (⟨state.2⟩ : Dag) state.1[t]! = keyOf source state.1 t := by
        rw [dag_node_eq (by simpa [Dag.size] using slot)]
        exact node
      obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp member
      have hj' : j < (Dag.node (⟨state.2⟩ : Dag) state.1[t]!).children.size := by
        rw [nodeEq]; simpa [keyOf] using hj
      have childEq : (Dag.node (⟨state.2⟩ : Dag) state.1[t]!).child j =
          state.1[(source[t]!).children[j]]! := by
        rw [child_eq_getElem _ j hj']
        simp [nodeEq, keyOf]
      exact ⟨r, rm, childEq ▸ desc_snoc d hj'⟩
  intro k hk
  obtain ⟨t, reach, _, slot⟩ := shaped.backward k hk
  obtain ⟨r, rm, d⟩ := descends t reach
  exact ⟨r, rm, slot ▸ d⟩

/-- **Hash-consing of the canonical DAG.** Distinct terms of a canonical DAG
denote distinct expressions: each is the image of a reachable source node,
with that node's term, and the source nodes are hash-consed. -/
theorem canonicalize_injective {source : Array Node} {roots : Array Nat} (run : Run source roots)
    {dag : Dag} {out : Array Nat} (ran : canonicalize source roots = .ok (dag, out)) :
    ∀ a, a < dag.size → ∀ b, b < dag.size → termOf dag.nodes a = termOf dag.nodes b → a = b := by
  obtain ⟨height, state, rfl, rfl, valid, shaped, below⟩ := canonicalize_final run ran
  intro a ha b hb same
  obtain ⟨s, sReach, _, rfl⟩ := shaped.backward a ha
  obtain ⟨s', sReach', _, rfl⟩ := shaped.backward b hb
  have first := (valid.mapped s sReach (below s sReach)).2.2
  have second := (valid.mapped s' sReach' (below s' sReach')).2.2
  change termOf state.2 state.1[s]! = termOf state.2 state.1[s']! at same
  rw [first, second] at same
  rw [run.hashConsed s s' sReach sReach' same]

/-! ## Whole tables within their budgets -/

theorem sharesValid_of_free (context : ShareCtx) (source : Ixon.Expr) (free : ShareFree source) :
    SharesValid context source := by
  induction source with
  | share _ => simp only [ShareFree] at free
  | prj _ _ _ ih => exact ih free
  | app _ _ ihf iha | lam _ _ _ ihf iha | all _ _ _ _ ihf iha => exact ⟨ihf free.1, iha free.2⟩
  | letE _ _ _ _ iht ihv ihb => exact ⟨iht free.1, ihv free.2.1, ihb free.2.2⟩
  | _ => trivial

/-- With Shares allowed, every Share below the resolved count resolves. -/
theorem sharesValid_of_below (context : ShareCtx) (allow : context.allowShare = true)
    (source : Ixon.Expr) (below : SharesIn (· < context.resolved.size) source) :
    SharesValid context source := by
  induction source with
  | share index =>
    simp only [SharesIn] at below
    refine ⟨context.resolved[index.toNat]'below, ?_⟩
    unfold resolveShare
    rw [allow, Array.getElem?_eq_getElem below]
    rfl
  | prj _ _ _ ih => exact ih below
  | app _ _ ihf iha | lam _ _ _ ihf iha | all _ _ _ _ ihf iha => exact ⟨ihf below.1, iha below.2⟩
  | letE _ _ _ _ iht ihv ihb => exact ⟨iht below.1, ihv below.2.1, ihb below.2.2⟩
  | _ => trivial

theorem treeHeight_lt (source : Ixon.Expr) : treeHeight source < nodeCount source := by
  induction source with
  | prj _ _ _ ih => simp only [treeHeight, nodeCount]; omega
  | app _ _ ihf iha | lam _ _ _ ihf iha | all _ _ _ _ ihf iha =>
    simp only [treeHeight, nodeCount]
    have := Nat.max_le.mpr (And.intro (Nat.le_of_lt_succ (Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le ihf
      (Nat.le_add_right _ _)))) (Nat.le_of_lt_succ (Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le iha
      (Nat.le_add_left _ _)))))
    omega
  | letE _ ty v b iht ihv ihb =>
    simp only [treeHeight, nodeCount]
    have inner : max (treeHeight v) (treeHeight b) ≤ nodeCount ty + nodeCount v + nodeCount b :=
      Nat.max_le.mpr ⟨by omega, by omega⟩
    have := Nat.max_le.mpr (And.intro (show treeHeight ty ≤ nodeCount ty + nodeCount v + nodeCount b by
      omega) inner)
    omega
  | _ => simp only [treeHeight, nodeCount]; omega

/-- Tree nodes of `sources[index], …, sources[index + count - 1]`. -/
def rangeNodes (sources : Array Ixon.Expr) (index count : Nat) : Nat :=
  ((List.range' index count).map fun i => nodeCount sources[i]!).sum

theorem rangeNodes_succ (sources : Array Ixon.Expr) (index count : Nat) :
    rangeNodes sources index (count + 1) = nodeCount sources[index]! + rangeNodes sources (index + 1) count := by
  simp [rangeNodes, List.range'_succ]

theorem rangeNodes_zero (sources : Array Ixon.Expr) (index : Nat) : rangeNodes sources index 0 = 0 := by
  simp [rangeNodes]

theorem le_rangeNodes (sources : Array Ixon.Expr) :
    ∀ count index i, index ≤ i → i < index + count → nodeCount sources[i]! ≤ rangeNodes sources index count := by
  intro count
  induction count with
  | zero => intro index i _ _; omega
  | succ count ih =>
    intro index i low high
    rw [rangeNodes_succ]
    by_cases first : i = index
    · subst first; omega
    · have := ih (index + 1) i (by omega) (by omega)
      omega

/-- Share-valid ingestion of `count` sources from `index` within the visit
and node budgets. -/
theorem walk_ok (limits : Limits) (sources : Array Ixon.Expr) (ctxOf : Nat → Array Nat → ShareCtx)
    (valid : ∀ index, index < sources.size → ∀ acc : Array Nat, acc.size = index →
      SharesValid (ctxOf index acc) sources[index]!)
    (deep : ∀ index, index < sources.size → treeHeight sources[index]! ≤ limits.maxDepth) :
    ∀ count index (acc : Array Nat) (before : IngestState), index + count ≤ sources.size →
      acc.size = index →
      before.visits + rangeNodes sources index count ≤ limits.maxExprVisits →
      before.interner.nodes.size + rangeNodes sources index count ≤ limits.maxNodes →
      ∃ out after, (walk limits sources ctxOf count index acc).run before = .ok (out, after) ∧
        out.size = index + count ∧
        after.visits ≤ before.visits + rangeNodes sources index count ∧
        after.interner.nodes.size ≤ before.interner.nodes.size + rangeNodes sources index count := by
  intro count
  induction count with
  | zero =>
    intro index acc before _ size _ _
    rw [rangeNodes_zero]
    exact ⟨acc, before, rfl, by omega, by omega, by omega⟩
  | succ count ih =>
    intro index acc before bound size visits nodes
    rw [rangeNodes_succ] at visits nodes ⊢
    obtain ⟨id, middle, ran, v1, n1⟩ := ingestExpr_ok limits (ctxOf index acc) sources[index]! 0 before
      (valid index (by omega) acc size) (by have := deep index (by omega); omega) (by omega) (by omega)
    obtain ⟨out, after, rest, outSize, v2, n2⟩ := ih (index + 1) (acc.push id) middle (by omega)
      (by simp [size]) (by omega) (by omega)
    refine ⟨out, after, ?_, by omega, by omega, by omega⟩
    rw [walk, run_bind_ok ran]
    exact rest

/-- Ingestion of a table and roots whose Shares resolve, within the budgets. -/
theorem ingestTable_ok (limits : Limits) (sharing roots : Array Ixon.Expr) (allowShare : Bool)
    (before : IngestState) (capacity : sharing.size < wordBound)
    (entries : ∀ index, index < sharing.size → ∀ acc : Array Nat, acc.size = index →
      SharesValid (tableContext sharing.size allowShare index acc) sharing[index]!)
    (rootsValid : ∀ index, index < roots.size → ∀ resolved : Array Nat, resolved.size = sharing.size →
      SharesValid (rootContext sharing.size allowShare index resolved) roots[index]!)
    (deepE : ∀ index, index < sharing.size → treeHeight sharing[index]! ≤ limits.maxDepth)
    (deepR : ∀ index, index < roots.size → treeHeight roots[index]! ≤ limits.maxDepth)
    (visits : before.visits + rangeNodes sharing 0 sharing.size + rangeNodes roots 0 roots.size ≤
      limits.maxExprVisits)
    (nodes : before.interner.nodes.size + rangeNodes sharing 0 sharing.size +
      rangeNodes roots 0 roots.size ≤ limits.maxNodes) :
    ∃ resolved out after, (ingestTable limits sharing roots allowShare).run before =
        .ok ((resolved, out), after) ∧ resolved.size = sharing.size ∧ out.size = roots.size ∧
      after.interner.nodes.size ≤ before.interner.nodes.size + rangeNodes sharing 0 sharing.size +
        rangeNodes roots 0 roots.size := by
  rw [ingestTable_eq, ite_eq_right (show ¬ sharing.size ≥ wordBound by omega)]
  unfold tableBody
  simp only [arrayLoop_eq_walk]
  obtain ⟨resolved, middle, r1, s1, v1, n1⟩ := walk_ok limits sharing
    (tableContext sharing.size allowShare) entries deepE sharing.size 0 #[] before (by omega) rfl
    (by omega) (by omega)
  obtain ⟨out, after, r2, s2, v2, n2⟩ := walk_ok limits roots
    (fun index _ => rootContext sharing.size allowShare index resolved)
    (fun index bound _ _ => rootsValid index bound resolved (by simpa using s1)) deepR roots.size 0 #[]
    middle (by omega) rfl (by omega) (by omega)
  refine ⟨resolved, out, after, ?_, by simpa using s1, by simpa using s2, by omega⟩
  rw [run_bind_ok r1, run_bind_ok r2]
  rfl

theorem le_foldl_max (l : List Nat) (acc : Nat) :
    acc ≤ l.foldl max acc ∧ ∀ x ∈ l, x ≤ l.foldl max acc := by
  induction l generalizing acc with
  | nil => simp
  | cons y ys ih =>
    obtain ⟨h1, h2⟩ := ih (max acc y)
    refine ⟨by simp only [List.foldl_cons]; omega, fun x hx => ?_⟩
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · exact h2 x hx

/-- A canonical DAG has at most as many terms as the interner's output. -/
theorem canonicalize_size {source : Array Node} {roots : Array Nat} (run : Run source roots)
    {dag : Dag} {out : Array Nat} (ran : canonicalize source roots = .ok (dag, out)) :
    dag.size ≤ source.size := by
  obtain ⟨height, state, rfl, rfl, _, shaped, _⟩ := canonicalize_final run ran
  have pick : ∀ k, k < state.2.size → ∃ t, t < source.size ∧ state.1[t]! = k := by
    intro k hk
    obtain ⟨t, reach, _, slot⟩ := shaped.backward k hk
    exact ⟨t, reach_lt run.cp run.inRange reach, slot⟩
  let g : Nat → Nat := fun k => if h : k < state.2.size then Classical.choose (pick k h) else 0
  have gSpec : ∀ k, k < state.2.size → g k < source.size ∧ state.1[g k]! = k := by
    intro k hk
    simp only [g, hk, dite_true]
    exact Classical.choose_spec (pick k hk)
  have nodup : ((List.range state.2.size).map g).Nodup := by
    apply nodup_map_on _ List.nodup_range
    intro a ha b hb same
    have ea := (gSpec a (List.mem_range.mp ha)).2
    have eb := (gSpec b (List.mem_range.mp hb)).2
    rw [same] at ea
    exact ea.symm.trans eb
  have sub : (List.range state.2.size).map g ⊆ List.range source.size := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    exact List.mem_range.mpr (gSpec k (List.mem_range.mp hk)).1
  have := List.Nodup.length_le_of_subset nodup sub
  simpa [Dag.size] using this

/-- **Expansion never refuses** a table and roots whose Shares resolve and
whose table fits the Share word: under some limits, which
`Budget.expand_mono` extends to every larger one, it succeeds, with at most
one term per input expression node. -/
theorem expand_ok_of (sharing roots : Array Ixon.Expr) (allowShare : Bool)
    (capacity : sharing.size < wordBound)
    (entries : ∀ index, index < sharing.size → ∀ acc : Array Nat, acc.size = index →
      SharesValid (tableContext sharing.size allowShare index acc) sharing[index]!)
    (rootsValid : ∀ index, index < roots.size → ∀ resolved : Array Nat, resolved.size = sharing.size →
      SharesValid (rootContext sharing.size allowShare index resolved) roots[index]!) :
    ∃ limits ex, expand limits sharing roots allowShare = .ok ex ∧
      ex.dag.size ≤ rangeNodes sharing 0 sharing.size + rangeNodes roots 0 roots.size := by
  let total := rangeNodes sharing 0 sharing.size + rangeNodes roots 0 roots.size
  let first : Limits := { maxExprVisits := total, maxDepth := total, maxNodes := total }
  have deepE : ∀ index, index < sharing.size → treeHeight sharing[index]! ≤ first.maxDepth := by
    intro index bound
    have := treeHeight_lt sharing[index]!
    have := le_rangeNodes sharing sharing.size 0 index (by omega) (by omega)
    change _ ≤ total
    omega
  have deepR : ∀ index, index < roots.size → treeHeight roots[index]! ≤ first.maxDepth := by
    intro index bound
    have := treeHeight_lt roots[index]!
    have := le_rangeNodes roots roots.size 0 index (by omega) (by omega)
    change _ ≤ total
    omega
  obtain ⟨resolved, out, state, ran, -, -, nodes⟩ := ingestTable_ok first sharing roots allowShare {}
    capacity entries rootsValid deepE deepR (by change 0 + _ + _ ≤ total; omega)
    (by change 0 + _ + _ ≤ total; omega)
  have run := ingestTable_run first sharing roots allowShare resolved out state ran
  obtain ⟨⟨dag, ids⟩, numbered⟩ := canonicalize_ok run
  have dagSize := canonicalize_size run numbered
  let tallest := (nodeHeights dag.nodes).toList.foldl max 0
  let second : Limits := { first with maxDepth := max total tallest }
  have le : Budget.LimitsLe first second :=
    ⟨Nat.le_refl _, Nat.le_max_left _ _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
      Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  have shallow : ¬ ((nodeHeights dag.nodes).any (· > second.maxDepth) = true) := by
    intro high
    obtain ⟨i, hi, gt⟩ := Array.any_eq_true.mp high
    have member : (nodeHeights dag.nodes)[i] ∈ (nodeHeights dag.nodes).toList :=
      Array.mem_toList_iff.mpr (Array.getElem_mem hi)
    have := (le_foldl_max _ 0).2 _ member
    have := Nat.le_max_right total tallest
    simp only [decide_eq_true_eq] at gt
    change (nodeHeights dag.nodes)[i] > max total tallest at gt
    omega
  refine ⟨second, ⟨dag, ids, state.visits, state.interner.nodes.size⟩, ?_, ?_⟩
  · unfold expand
    rw [Budget.bind_ok_eq (Budget.ingestTable_refines le sharing roots allowShare {} _ ran)]
    dsimp only
    rw [Budget.bind_ok_eq numbered]
    dsimp only
    rw [ite_eq_right shallow]
    rfl
  · change dag.size ≤ total
    change _ ≤ 0 + _ + _ at nodes
    omega

/-- **Expansion never refuses Share-free roots.** -/
theorem expand_ok (roots : Array Ixon.Expr) (free : ∀ index, index < roots.size → ShareFree roots[index]!) :
    ∃ limits ex, expand limits #[] roots false = .ok ex ∧ ex.dag.size ≤ rangeNodes roots 0 roots.size := by
  obtain ⟨limits, ex, ran, size⟩ := expand_ok_of #[] roots false (by simp [wordBound])
    (fun index bound => absurd bound (by simp))
    (fun index bound resolved _ => sharesValid_of_free _ _ (free index bound))
  refine ⟨limits, ex, ran, ?_⟩
  simpa [rangeNodes] using size

end Ix.Sharing.Verify.CanonicalMeaning

#guard_kernel_axioms Ix.Sharing.Verify.CanonicalMeaning.canonicalize_ok [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.CanonicalMeaning.ingestExpr_ok [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.CanonicalMeaning.canonicalize_reach [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.CanonicalMeaning.canonicalize_injective [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.CanonicalMeaning.ingestTable_ok [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.CanonicalMeaning.expand_ok [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.CanonicalMeaning.expand_ok_of [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.CanonicalMeaning.canonicalize_size [propext, Classical.choice, Quot.sound]
