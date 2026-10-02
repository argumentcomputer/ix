/-
  Exact minimum sharing: re-expansion against a fixed DAG without hashing
  whole nodes.

  `reexpand` checks an encoding by expanding it again against a canonical
  DAG: it runs the expansion of `expand` (`ingestTable`, in the
  `StateT`/`Except` monad) with the interner seeded with every node of the
  DAG (`Interner.ofNodes`, a hash map keyed by whole nodes, built per
  call). `reexpandFast` makes the same walk, with the same pointer cache,
  visit count, limits and errors in the same order, but finds the ID of a
  node without hashing it: among the parents of its child with the fewest
  parents, or in a map of the leaf heads (`ReIndex.lookup`), and it passes
  its state explicitly. A node that is not in the DAG, which the interner
  would add, makes `reexpandFast` run `reexpand` instead.

  `reexpand_eq_fast` proves the two equal for every input: `lookup_sound`
  (the lookup returns the ID the interner's map holds: the last position of
  the node in the DAG) and `reIngestExpr_sim` (each step agrees with
  `ingestExpr` until the fast walk stops).
-/
module

public import Ix.Sharing.Exact.Phase3
import all Ix.Sharing.Exact.Basic
import all Ix.Sharing.Exact.Dag
import all Ix.Sharing.Exact.Phase3

public section

namespace Ix.Sharing.Exact

/-! ## Structural equality of nodes -/

theorem isEqv_decide_iff {α : Type} [DecidableEq α] (a b : Array α) :
    (a.isEqv b fun x y => decide (x = y)) = true ↔ a = b := by
  rw [Array.isEqv_iff_rel, Array.ext_iff]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨h, h'⟩; exact ⟨h, fun i h1 _ => h' i h1⟩
  · rintro ⟨h, h'⟩; exact ⟨h, fun i h1 => h' i h1 (h ▸ h1)⟩

theorem binderContract_beq_iff (a b : Ixon.BinderContract) :
    Ixon.instBEqBinderContract.beq a b = true ↔ a = b :=
  (beq_iff_eq : (a == b) = true ↔ a = b)

theorem valueContract_beq_iff (a b : Ixon.ValueContract) :
    Ixon.instBEqValueContract.beq a b = true ↔ a = b :=
  (beq_iff_eq : (a == b) = true ↔ a = b)

theorem letContract_beq_iff (a b : Ixon.LetContract) :
    Ixon.instBEqLetContract.beq a b = true ↔ a = b := by
  cases a; cases b
  simp only [Ixon.instBEqLetContract.beq, Bool.and_eq_true, Ixon.LetContract.mk.injEq, beq_iff_eq]

theorem Head.beq_iff (a b : Head) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;>
    simp [BEq.beq, instBEqHead.beq, Head.ctorIdx, isEqv_decide_iff, binderContract_beq_iff,
      valueContract_beq_iff, letContract_beq_iff]

theorem Node.beq_iff (a b : Node) : (a == b) = true ↔ a = b := by
  cases a; cases b
  have hh : ∀ h h' : Head, instBEqHead.beq h h' = true ↔ h = h' := Head.beq_iff
  simp only [BEq.beq, instBEqNode.beq, Bool.and_eq_true, hh, isEqv_decide_iff, Node.mk.injEq]

instance : LawfulBEq Head where
  rfl := (Head.beq_iff _ _).mpr rfl
  eq_of_beq h := (Head.beq_iff _ _).mp h

instance : LawfulBEq Node where
  rfl := (Node.beq_iff _ _).mpr rfl
  eq_of_beq h := (Node.beq_iff _ _).mp h

/-! ## The interner's map: the last position of each node -/

theorem ofNodes_get? (nodes : Array Node) (k : Node) (u : Nat) :
    (Interner.ofNodes nodes).index.get? k = some u ↔
      (u < nodes.size ∧ nodes[u]! = k ∧ ∀ v, u < v → v < nodes.size → nodes[v]! ≠ k) := by
  unfold Interner.ofNodes
  simp only [Std.HashMap.get?_eq_getElem?]
  have := Array.foldl_induction (as := nodes.zipIdx)
    (motive := fun j (m : Std.HashMap Node Nat) => ∀ u, m[k]? = some u ↔
      (u < j ∧ nodes[u]! = k ∧ ∀ v, u < v → v < j → nodes[v]! ≠ k))
    (init := {}) (f := fun m (n, i) => m.insert n i)
    (by intro u; simp)
    (by
      intro i m ih u
      have hi' : i.1 < nodes.size := by simpa using i.2
      have hz : nodes.zipIdx[i] = (nodes[i.1], i.1) := by simp [Array.getElem_zipIdx]
      rw [hz]
      dsimp only
      rw [Std.HashMap.getElem?_insert]
      have hni : nodes[i.1]! = nodes[i.1] := getElem!_pos nodes i.1 hi'
      by_cases hk : nodes[i.1] = k
      · rw [if_pos ((Node.beq_iff _ _).mpr hk), Option.some.injEq]
        constructor
        · rintro rfl
          exact ⟨by omega, by rw [hni, hk], fun v h1 h2 => by omega⟩
        · rintro ⟨h1, h2, h3⟩
          by_cases hui : u = i.1
          · exact hui.symm
          · exact absurd (by rw [hni, hk]) (h3 i.1 (by omega) (by omega))
      · rw [if_neg (fun h => hk ((Node.beq_iff _ _).mp h)), ih u]
        constructor
        · rintro ⟨h1, h2, h3⟩
          refine ⟨by omega, h2, fun v h4 h5 => ?_⟩
          by_cases hvi : v = i.1
          · subst hvi; rw [hni]; exact hk
          · exact h3 v h4 (by omega)
        · rintro ⟨h1, h2, h3⟩
          have hui : u ≠ i.1 := fun h => hk (by subst h; rw [← hni]; exact h2)
          exact ⟨by omega, h2, fun v h4 h5 => h3 v h4 (by omega)⟩)
  simpa [Array.size_zipIdx] using this u

/-! ## Finding a node without hashing it -/

/-- Each leaf head of the DAG (the head of a node without children) to its
last position. -/
def leafIndex (dag : Dag) : Std.HashMap Head Nat :=
  dag.nodes.zipIdx.foldl (fun m (n, i) => if n.children.isEmpty then m.insert n.head i else m) {}

theorem leafIndex_get? (dag : Dag) (h : Head) (u : Nat) :
    (leafIndex dag)[h]? = some u ↔
      (u < dag.nodes.size ∧ dag.nodes[u]! = ⟨h, #[]⟩ ∧
        ∀ v, u < v → v < dag.nodes.size → dag.nodes[v]! ≠ ⟨h, #[]⟩) := by
  unfold leafIndex
  have := Array.foldl_induction (as := dag.nodes.zipIdx)
    (motive := fun j (m : Std.HashMap Head Nat) => ∀ u, m[h]? = some u ↔
      (u < j ∧ dag.nodes[u]! = ⟨h, #[]⟩ ∧ ∀ v, u < v → v < j → dag.nodes[v]! ≠ ⟨h, #[]⟩))
    (init := {}) (f := fun m (n, i) => if n.children.isEmpty then m.insert n.head i else m)
    (by intro u; simp)
    (by
      intro i m ih u
      have hi' : i.1 < dag.nodes.size := by simpa using i.2
      have hz : dag.nodes.zipIdx[i] = (dag.nodes[i.1], i.1) := by simp [Array.getElem_zipIdx]
      rw [hz]
      dsimp only
      have hni : dag.nodes[i.1]! = dag.nodes[i.1] := getElem!_pos dag.nodes i.1 hi'
      by_cases hk : dag.nodes[i.1] = ⟨h, #[]⟩
      · have he : dag.nodes[i.1].children.isEmpty = true := by rw [hk]; rfl
        have hh : (dag.nodes[i.1].head == h) = true := by rw [hk]; exact (Head.beq_iff _ _).mpr rfl
        rw [if_pos he, Std.HashMap.getElem?_insert, if_pos hh, Option.some.injEq]
        constructor
        · rintro rfl
          exact ⟨by omega, by rw [hni, hk], fun v h1 h2 => by omega⟩
        · rintro ⟨h1, h2, h3⟩
          by_cases hui : u = i.1
          · exact hui.symm
          · exact absurd (by rw [hni, hk]) (h3 i.1 (by omega) (by omega))
      · have hstep : (if dag.nodes[i.1].children.isEmpty = true then
            m.insert dag.nodes[i.1].head i.1 else m)[h]? = m[h]? := by
          split
          · rename_i he
            rw [Std.HashMap.getElem?_insert, if_neg]
            intro hh
            apply hk
            have h1 := (Head.beq_iff _ _).mp hh
            have h2 : dag.nodes[i.1].children = #[] := by
              simpa [Array.isEmpty_iff] using he
            cases hn : dag.nodes[i.1]
            rw [hn] at h1 h2
            simp only at h1 h2
            rw [h1, h2]
          · rfl
        rw [hstep, ih u]
        constructor
        · rintro ⟨h1, h2, h3⟩
          refine ⟨by omega, h2, fun v h4 h5 => ?_⟩
          by_cases hvi : v = i.1
          · subst hvi; rw [hni]; exact hk
          · exact h3 v h4 (by omega)
        · rintro ⟨h1, h2, h3⟩
          have hui : u ≠ i.1 := fun h' => hk (by subst h'; rw [← hni]; exact h2)
          exact ⟨by omega, h2, fun v h4 h5 => h3 v h4 (by omega)⟩)
  simpa [Array.size_zipIdx] using this u

/-- The largest `u` of `ps` below `dag.size` whose node is `n`. -/
def lastMatch (dag : Dag) (n : Node) (ps : Array Nat) : Option Nat :=
  ps.foldl (fun acc u =>
      if u < dag.size && dag.node u == n then
        some (match acc with
          | some v => max v u
          | none => u)
      else acc) none

theorem lastMatch_spec (dag : Dag) (n : Node) (ps : Array Nat) (u : Nat)
    (h : lastMatch dag n ps = some u) :
    u ∈ ps ∧ u < dag.size ∧ dag.node u = n ∧
      ∀ v ∈ ps, v < dag.size → dag.node v = n → v ≤ u := by
  unfold lastMatch at h
  rw [← Array.foldl_toList] at h
  suffices hs : ∀ (l : List Nat) (acc : Option Nat) (u : Nat),
      l.foldl (fun acc u =>
        if u < dag.size && dag.node u == n then
          some (match acc with
            | some v => max v u
            | none => u)
        else acc) acc = some u →
      ((acc = some u) ∨ (u ∈ l ∧ u < dag.size ∧ dag.node u = n)) ∧
        (∀ a, acc = some a → a ≤ u) ∧ (∀ v ∈ l, v < dag.size → dag.node v = n → v ≤ u) by
    obtain ⟨h1, _, h3⟩ := hs ps.toList none u h
    rcases h1 with h1 | ⟨h1, h2, h4⟩
    · cases h1
    · exact ⟨Array.mem_toList_iff.mp h1, h2, h4, fun v hv => h3 v (Array.mem_toList_iff.mpr hv)⟩
  intro l
  induction l with
  | nil =>
    intro acc u h
    simp only [List.foldl_nil] at h
    exact ⟨Or.inl h, fun a ha => by rw [h] at ha; cases ha; exact Nat.le_refl _, by simp⟩
  | cons w l ih =>
    intro acc u h
    simp only [List.foldl_cons] at h
    obtain ⟨h1, h2, h3⟩ := ih _ u h
    by_cases hw : (w < dag.size && dag.node w == n) = true
    · rw [if_pos hw] at h1 h2
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hw
      have hacc : ∀ a, acc = some a → a ≤ u := by
        intro a ha
        subst ha
        have := h2 _ rfl
        simp only at this
        omega
      have hwu : w ≤ u := by
        have := h2 _ rfl
        cases acc <;> simp only at this <;> omega
      refine ⟨?_, hacc, ?_⟩
      · rcases h1 with h1 | h1
        · cases acc with
          | none =>
            simp only [Option.some.injEq] at h1
            exact Or.inr ⟨by simp [h1], h1 ▸ hw.1, h1 ▸ hw.2⟩
          | some a =>
            simp only [Option.some.injEq] at h1
            by_cases hav : a ≤ w
            · rw [Nat.max_eq_right hav] at h1
              exact Or.inr ⟨by simp [h1], h1 ▸ hw.1, h1 ▸ hw.2⟩
            · rw [Nat.max_eq_left (by omega)] at h1
              exact Or.inl (by rw [h1])
        · exact Or.inr ⟨List.mem_cons_of_mem _ h1.1, h1.2⟩
      · intro v hv hv1 hv2
        simp only [List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact hwu
        · exact h3 v hv hv1 hv2
    · rw [if_neg hw] at h1 h2
      refine ⟨?_, h2, ?_⟩
      · rcases h1 with h1 | h1
        · exact Or.inl h1
        · exact Or.inr ⟨List.mem_cons_of_mem _ h1.1, h1.2⟩
      · intro v hv hv1 hv2
        simp only [List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact absurd (by simp [hv1, hv2]) hw
        · exact h3 v hv hv1 hv2

/-- The child in `cs` with the fewest parents (the first of `cs` on a tie). -/
def fewestParents (parents : Array (Array Nat)) (cs : Array Nat) : Nat :=
  cs.foldl (fun best c =>
    if (parents[c]?.getD #[]).size < (parents[best]?.getD #[]).size then c else best) cs[0]!

theorem fewestParents_mem (parents : Array (Array Nat)) (cs : Array Nat) (h : 0 < cs.size) :
    fewestParents parents cs ∈ cs := by
  unfold fewestParents
  rw [← Array.foldl_toList]
  have h0 : cs[0]! ∈ cs.toList := by
    rw [getElem!_pos cs 0 h]
    exact Array.mem_toList_iff.mpr (Array.getElem_mem h)
  suffices hs : ∀ (l : List Nat) (b : Nat), b ∈ cs.toList → (∀ c ∈ l, c ∈ cs.toList) →
      l.foldl (fun best c =>
        if (parents[c]?.getD #[]).size < (parents[best]?.getD #[]).size then c else best) b ∈
        cs.toList by
    exact Array.mem_toList_iff.mp (hs cs.toList _ h0 (fun c hc => hc))
  intro l
  induction l with
  | nil => intro b hb _; exact hb
  | cons c l ih =>
    intro b hb hl
    simp only [List.foldl_cons]
    apply ih _ _ (fun c' hc' => hl c' (List.mem_cons_of_mem _ hc'))
    split
    · exact hl c (List.mem_cons_self ..)
    · exact hb

/-- The tables `ReIndex.lookup` finds nodes with. -/
structure ReIndex where
  parents : Array (Array Nat)
  leaves : Std.HashMap Head Nat

/-- The parent lists and leaf heads of a DAG. -/
def ReIndex.ofDag (dag : Dag) : ReIndex :=
  { parents := parentEdgeLists dag, leaves := leafIndex dag }

/-- The ID of `n` in the DAG, if it occurs there (its last position): a leaf
by its head, any other node among the parents of its child with the fewest
parents. -/
def ReIndex.lookup (ix : ReIndex) (dag : Dag) (n : Node) : Option Nat :=
  if n.children.isEmpty then ix.leaves[n.head]?
  else
    let c := fewestParents ix.parents n.children
    if c < dag.size then lastMatch dag n (ix.parents[c]?.getD #[]) else none

theorem dag_node_eq_getElem! (dag : Dag) (u : Nat) (hu : u < dag.size) :
    dag.node u = dag.nodes[u]! := by
  unfold Dag.node
  rw [getElem!_pos dag.nodes u hu, Array.getElem?_eq_getElem hu]
  rfl

/-- **Lookup soundness.** A node `lookup` finds has the ID the interner's map
holds for it. -/
theorem lookup_sound (dag : Dag) (n : Node) (u : Nat)
    (h : (ReIndex.ofDag dag).lookup dag n = some u) :
    (Interner.ofNodes dag.nodes).index.get? n = some u := by
  rw [ofNodes_get?]
  unfold ReIndex.lookup ReIndex.ofDag at h
  split at h
  · rename_i he
    have hn : n = ⟨n.head, #[]⟩ := by
      cases n
      simp only at he ⊢
      rw [Node.mk.injEq]
      exact ⟨rfl, by simpa [Array.isEmpty_iff] using he⟩
    rw [hn]
    exact (leafIndex_get? dag n.head u).mp h
  · rename_i he
    simp only at h
    split at h
    · rename_i hc
      obtain ⟨hu, hus, hun, hmax⟩ := lastMatch_spec dag n _ u h
      have hcs : 0 < n.children.size := by
        cases hcs : n.children.size
        · exfalso; apply he; simpa [Array.isEmpty_iff, Array.size_eq_zero_iff] using hcs
        · omega
      have hcm := fewestParents_mem (parentEdgeLists dag) n.children hcs
      refine ⟨hus, by rw [← dag_node_eq_getElem! dag u hus, hun], fun v h1 h2 h3 => ?_⟩
      have hv : dag.node v = n := by rw [dag_node_eq_getElem! dag v h2, h3]
      have hok := parentEdgeLists_ok dag
      unfold ParentsOK at hok
      have hp := (hok _ hc v).mpr ⟨h2, by rw [hv]; exact hcm⟩
      have := hmax v hp h2 hv
      omega
    · cases h

/-! ## The re-expansion walk with explicit state -/

/-- A step of the fast re-expansion: a value with the pointer cache and the
visit count, an error, or `stop` (a node is not in the DAG). -/
inductive ReStep (α : Type) where
  | ok (a : α) (cache : Std.HashMap USize Nat) (visits : Nat)
  | error (e : SharingError)
  | stop

/-- `internNode` against the DAG's own interner. -/
@[inline] def reIntern (limits : Limits) (dag : Dag) (ix : ReIndex) (n : Node)
    (cache : Std.HashMap USize Nat) (visits : Nat) : ReStep Nat :=
  match ix.lookup dag n with
  | some id =>
    if dag.nodes.size > limits.maxNodes then .error (.resourceExhausted .nodes limits.maxNodes)
    else .ok id cache visits
  | none => .stop

/-- Continue an ok step with `k`. -/
@[inline] def ReStep.bind {α β : Type} (r : ReStep α)
    (k : α → Std.HashMap USize Nat → Nat → ReStep β) : ReStep β :=
  match r with
  | .ok a cache visits => k a cache visits
  | .error err => .error err
  | .stop => .stop

/-- Record the ID of the expression at `ptr` in the pointer cache. -/
@[inline] def reFinish (ptr : USize) (r : ReStep Nat) : ReStep Nat :=
  r.bind fun id cache visits => .ok id (cache.insert ptr id) visits

/-- `ingestExpr` against the DAG's own interner. -/
def reIngestExpr (limits : Limits) (dag : Dag) (ix : ReIndex) (ctx : ShareCtx) (depth : Nat)
    (e : Ixon.Expr) (cache : Std.HashMap USize Nat) (visits : Nat) : ReStep Nat :=
  match cache.get? (exprPtr e) with
  | some id => .ok id cache visits
  | none =>
    if depth > limits.maxDepth then .error (.resourceExhausted .depth limits.maxDepth) else
    match bump visits 1 limits.maxExprVisits .exprVisits with
    | .error err => .error err
    | .ok visits => reFinish (exprPtr e) <| match e with
      | .sort i => reIntern limits dag ix ⟨.sort i, #[]⟩ cache visits
      | .var i => reIntern limits dag ix ⟨.var i, #[]⟩ cache visits
      | .ref r us => reIntern limits dag ix ⟨.ref r us, #[]⟩ cache visits
      | .recur r us => reIntern limits dag ix ⟨.recur r us, #[]⟩ cache visits
      | .prj t f v =>
        (reIngestExpr limits dag ix ctx (depth + 1) v cache visits).bind fun vi cache visits =>
          reIntern limits dag ix ⟨.prj t f, #[vi]⟩ cache visits
      | .str i => reIntern limits dag ix ⟨.str i, #[]⟩ cache visits
      | .nat i => reIntern limits dag ix ⟨.nat i, #[]⟩ cache visits
      | .app f a =>
        (reIngestExpr limits dag ix ctx (depth + 1) f cache visits).bind fun fi cache visits =>
        (reIngestExpr limits dag ix ctx (depth + 1) a cache visits).bind fun ai cache visits =>
          reIntern limits dag ix ⟨.app, #[fi, ai]⟩ cache visits
      | .lam c ty body =>
        (reIngestExpr limits dag ix ctx (depth + 1) ty cache visits).bind fun ti cache visits =>
        (reIngestExpr limits dag ix ctx (depth + 1) body cache visits).bind fun bi cache visits =>
          reIntern limits dag ix ⟨.lam c, #[ti, bi]⟩ cache visits
      | .all c r ty body =>
        (reIngestExpr limits dag ix ctx (depth + 1) ty cache visits).bind fun ti cache visits =>
        (reIngestExpr limits dag ix ctx (depth + 1) body cache visits).bind fun bi cache visits =>
          reIntern limits dag ix ⟨.all c r, #[ti, bi]⟩ cache visits
      | .letE c ty v body =>
        (reIngestExpr limits dag ix ctx (depth + 1) ty cache visits).bind fun ti cache visits =>
        (reIngestExpr limits dag ix ctx (depth + 1) v cache visits).bind fun vi cache visits =>
        (reIngestExpr limits dag ix ctx (depth + 1) body cache visits).bind fun bi cache visits =>
          reIntern limits dag ix ⟨.letE c, #[ti, vi, bi]⟩ cache visits
      | .share j =>
        match resolveShare ctx j with
        | .ok id => .ok id cache visits
        | .error err => .error err

/-! ## Agreement with `ingestExpr` -/

/-- A fast step agrees with a run of the expansion monad from the DAG's
interner, unless it stopped. -/
def ReSim {α : Type} (I0 : Interner) : ReStep α → Except SharingError (α × IngestState) → Prop
  | .ok a cache visits, r => r = .ok (a, { interner := I0, ptrCache := cache, visits })
  | .error e, r => r = .error e
  | .stop, _ => True

theorem reIntern_sim (limits : Limits) (dag : Dag) (n : Node) (cache : Std.HashMap USize Nat)
    (visits : Nat) :
    ReSim (Interner.ofNodes dag.nodes) (reIntern limits dag (ReIndex.ofDag dag) n cache visits)
      ((internNode limits n).run
        { interner := Interner.ofNodes dag.nodes, ptrCache := cache, visits }) := by
  unfold reIntern
  split
  · rename_i id hl
    have hg := lookup_sound dag n id hl
    have hint : (Interner.ofNodes dag.nodes).intern n = (Interner.ofNodes dag.nodes, id) := by
      unfold Interner.intern
      rw [hg]
    unfold internNode
    have hn : (Interner.ofNodes dag.nodes).nodes = dag.nodes := rfl
    by_cases hm : limits.maxNodes < dag.nodes.size
    · simp [hint, hn, hm, ReSim]
      rfl
    · simp [hint, hn, hm, ReSim]
      rfl
  · trivial

theorem ReSim.bind {α β : Type} {I0 : Interner} {r : ReStep α}
    {m : Except SharingError (α × IngestState)}
    {k : α → Std.HashMap USize Nat → Nat → ReStep β}
    {m' : α → IngestState → Except SharingError (β × IngestState)}
    (h : ReSim I0 r m)
    (hk : ∀ a c v, ReSim I0 (k a c v) (m' a { interner := I0, ptrCache := c, visits := v })) :
    ReSim I0 (r.bind k) (m >>= fun p => m' p.1 p.2) := by
  cases r with
  | ok a c v =>
    simp only [ReSim] at h
    subst h
    exact hk a c v
  | error e =>
    simp only [ReSim] at h
    subst h
    simp only [ReStep.bind, ReSim]
    rfl
  | stop => trivial

theorem reFinish_sim {I0 : Interner} (ptr : USize) {r : ReStep Nat}
    {m : Except SharingError (Nat × IngestState)} (h : ReSim I0 r m) :
    ReSim I0 (reFinish ptr r)
      ((fun a => (a.1,
          { interner := a.2.interner, ptrCache := a.2.ptrCache.insert ptr a.1,
            visits := a.2.visits })) <$> m) := by
  cases r with
  | ok a c v =>
    simp only [ReSim] at h
    subst h
    simp only [reFinish, ReStep.bind, ReSim]
    rfl
  | error e =>
    simp only [ReSim] at h
    subst h
    simp only [reFinish, ReStep.bind, ReSim]
    rfl
  | stop => trivial

/-- The part of `ingestExpr` and `reIngestExpr` around the node itself: the
pointer cache, the depth limit, the visit count, and recording the ID. -/
theorem sim_prefix (limits : Limits) (dag : Dag) (depth : Nat) (e : Ixon.Expr)
    (cache : Std.HashMap USize Nat) (visits : Nat) (fb : Nat → ReStep Nat) (mb : IngestM Nat)
    (hb : ∀ v, ReSim (Interner.ofNodes dag.nodes) (fb v)
      (mb.run { interner := Interner.ofNodes dag.nodes, ptrCache := cache, visits := v })) :
    ReSim (Interner.ofNodes dag.nodes)
      (match cache.get? (exprPtr e) with
        | some id => .ok id cache visits
        | none =>
          if depth > limits.maxDepth then .error (.resourceExhausted .depth limits.maxDepth) else
          match bump visits 1 limits.maxExprVisits .exprVisits with
          | .error err => .error err
          | .ok visits => reFinish (exprPtr e) (fb visits))
      ((do
        let ptr := exprPtr e
        match (← get).ptrCache.get? ptr with
        | some id => return id
        | none =>
          if depth > limits.maxDepth then
            throw (.resourceExhausted .depth limits.maxDepth)
          let s ← get
          let visits ← liftExcept (bump s.visits 1 limits.maxExprVisits .exprVisits)
          set { s with visits }
          let id ← mb
          modify fun s => { s with ptrCache := s.ptrCache.insert ptr id }
          return id : IngestM Nat).run
        { interner := Interner.ofNodes dag.nodes, ptrCache := cache, visits }) := by
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases hc : cache.get? (exprPtr e) with
  | some id => simp only [ReSim]; rfl
  | none =>
    by_cases hd : depth > limits.maxDepth
    · simp only [hd, if_true, ReSim]; rfl
    · simp only [hd, if_false]
      cases hbv : bump visits 1 limits.maxExprVisits .exprVisits with
      | error err => simp [hbv, liftExcept, ReSim]; rfl
      | ok v =>
        simp [hbv, liftExcept]
        exact reFinish_sim _ (hb v)

theorem share_sim (I0 : Interner) (ctx : ShareCtx) (j : UInt64) (cache : Std.HashMap USize Nat)
    (visits : Nat) :
    ReSim I0 (match resolveShare ctx j with
        | .ok id => .ok id cache visits
        | .error err => .error err)
      ((liftExcept (resolveShare ctx j)).run { interner := I0, ptrCache := cache, visits }) := by
  cases resolveShare ctx j with
  | ok id => simp only [liftExcept, ReSim]; rfl
  | error err => simp only [liftExcept, ReSim]; rfl

theorem ReSim.bind' {α β : Type} {I0 : Interner} {r : ReStep α}
    {m : Except SharingError (α × IngestState)}
    {k : α → Std.HashMap USize Nat → Nat → ReStep β}
    {m' : α × IngestState → Except SharingError (β × IngestState)}
    (h : ReSim I0 r m)
    (hk : ∀ a c v, ReSim I0 (k a c v) (m' (a, { interner := I0, ptrCache := c, visits := v }))) :
    ReSim I0 (r.bind k) (m >>= m') := by
  cases r with
  | ok a c v =>
    simp only [ReSim] at h
    subst h
    exact hk a c v
  | error e =>
    simp only [ReSim] at h
    subst h
    simp only [ReStep.bind, ReSim]
    rfl
  | stop => trivial

theorem reFinish_bind {α : Type} {I0 : Interner} (ptr : USize) {r : ReStep α}
    {m : Except SharingError (α × IngestState)}
    {k : α → Std.HashMap USize Nat → Nat → ReStep Nat}
    {m' : α × IngestState → Except SharingError (Nat × IngestState)}
    (h : ReSim I0 r m)
    (hk : ∀ a c v, ReSim I0 (reFinish ptr (k a c v))
      (m' (a, { interner := I0, ptrCache := c, visits := v }))) :
    ReSim I0 (reFinish ptr (r.bind k)) (m >>= m') := by
  have : reFinish ptr (r.bind k) = r.bind (fun a c v => reFinish ptr (k a c v)) := by
    cases r <;> rfl
  rw [this]
  exact ReSim.bind' h hk

theorem reIngestExpr_sim (limits : Limits) (dag : Dag) (ctx : ShareCtx) :
    ∀ (e : Ixon.Expr) (depth : Nat) (cache : Std.HashMap USize Nat) (visits : Nat),
      ReSim (Interner.ofNodes dag.nodes)
        (reIngestExpr limits dag (ReIndex.ofDag dag) ctx depth e cache visits)
        ((ingestExpr limits ctx depth e).run
          { interner := Interner.ofNodes dag.nodes, ptrCache := cache, visits }) := by
  intro e
  induction e with
  | sort i | var i | ref i us | recur i us | str i | nat i =>
    intro depth cache visits
    unfold reIngestExpr ingestExpr
    refine sim_prefix limits dag depth _ cache visits _ _ ?_
    intro v
    exact reIntern_sim limits dag _ cache v
  | prj t f v ih =>
    intro depth cache visits
    rw [reIngestExpr, ingestExpr]
    dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hc : cache.get? (exprPtr (Ixon.Expr.prj t f v)) with
    | some id => simp only [ReSim]; rfl
    | none =>
      by_cases hd : depth > limits.maxDepth
      · simp only [hd, if_true, ReSim]; rfl
      · simp only [hd, if_false]
        cases hbv : bump visits 1 limits.maxExprVisits .exprVisits with
        | error err => simp [hbv, liftExcept, ReSim]; rfl
        | ok w =>
          simp [hbv, liftExcept]
          exact reFinish_bind _ (ih (depth + 1) cache w)
            (fun a c v' => reFinish_sim _ (reIntern_sim limits dag _ c v'))
  | app f a ihf iha =>
    intro depth cache visits
    rw [reIngestExpr, ingestExpr]
    dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hc : cache.get? (exprPtr (Ixon.Expr.app f a)) with
    | some id => simp only [ReSim]; rfl
    | none =>
      by_cases hd : depth > limits.maxDepth
      · simp only [hd, if_true, ReSim]; rfl
      · simp only [hd, if_false]
        cases hbv : bump visits 1 limits.maxExprVisits .exprVisits with
        | error err => simp [hbv, liftExcept, ReSim]; rfl
        | ok w =>
          simp [hbv, liftExcept]
          exact reFinish_bind _ (ihf (depth + 1) cache w) (fun fi c v' =>
            reFinish_bind _ (iha (depth + 1) c v')
              (fun ai c' v'' => reFinish_sim _ (reIntern_sim limits dag _ c' v'')))
  | lam bc ty body iht ihb =>
    intro depth cache visits
    rw [reIngestExpr, ingestExpr]
    dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hc : cache.get? (exprPtr (Ixon.Expr.lam bc ty body)) with
    | some id => simp only [ReSim]; rfl
    | none =>
      by_cases hd : depth > limits.maxDepth
      · simp only [hd, if_true, ReSim]; rfl
      · simp only [hd, if_false]
        cases hbv : bump visits 1 limits.maxExprVisits .exprVisits with
        | error err => simp [hbv, liftExcept, ReSim]; rfl
        | ok w =>
          simp [hbv, liftExcept]
          exact reFinish_bind _ (iht (depth + 1) cache w) (fun ti c v' =>
            reFinish_bind _ (ihb (depth + 1) c v')
              (fun bi c' v'' => reFinish_sim _ (reIntern_sim limits dag _ c' v'')))
  | all bc r ty body iht ihb =>
    intro depth cache visits
    rw [reIngestExpr, ingestExpr]
    dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hc : cache.get? (exprPtr (Ixon.Expr.all bc r ty body)) with
    | some id => simp only [ReSim]; rfl
    | none =>
      by_cases hd : depth > limits.maxDepth
      · simp only [hd, if_true, ReSim]; rfl
      · simp only [hd, if_false]
        cases hbv : bump visits 1 limits.maxExprVisits .exprVisits with
        | error err => simp [hbv, liftExcept, ReSim]; rfl
        | ok w =>
          simp [hbv, liftExcept]
          exact reFinish_bind _ (iht (depth + 1) cache w) (fun ti c v' =>
            reFinish_bind _ (ihb (depth + 1) c v')
              (fun bi c' v'' => reFinish_sim _ (reIntern_sim limits dag _ c' v'')))
  | letE lc ty v body iht ihv ihb =>
    intro depth cache visits
    rw [reIngestExpr, ingestExpr]
    dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hc : cache.get? (exprPtr (Ixon.Expr.letE lc ty v body)) with
    | some id => simp only [ReSim]; rfl
    | none =>
      by_cases hd : depth > limits.maxDepth
      · simp only [hd, if_true, ReSim]; rfl
      · simp only [hd, if_false]
        cases hbv : bump visits 1 limits.maxExprVisits .exprVisits with
        | error err => simp [hbv, liftExcept, ReSim]; rfl
        | ok w =>
          simp [hbv, liftExcept]
          exact reFinish_bind _ (iht (depth + 1) cache w) (fun ti c v' =>
            reFinish_bind _ (ihv (depth + 1) c v') (fun vi c' v'' =>
              reFinish_bind _ (ihb (depth + 1) c' v'')
                (fun bi c'' v''' => reFinish_sim _ (reIntern_sim limits dag _ c'' v'''))))
  | share j =>
    intro depth cache visits
    unfold reIngestExpr ingestExpr
    refine sim_prefix limits dag depth _ cache visits _ _ ?_
    intro v
    exact share_sim _ ctx j cache v

/-! ## The table and the roots -/

/-- The entries `i, …, i + k - 1` of `ingestTable` (`allowShare`). -/
def reIngestEntries (limits : Limits) (dag : Dag) (ix : ReIndex) (sharing : Array Ixon.Expr) :
    Nat → Nat → Array Nat → Std.HashMap USize Nat → Nat → ReStep (Array Nat)
  | 0, _, resolved, cache, visits => .ok resolved cache visits
  | k + 1, i, resolved, cache, visits =>
    let ctx : ShareCtx :=
      { resolved, tableSize := sharing.size, entry := some i, root := 0, allowShare := true }
    (reIngestExpr limits dag ix ctx 0 sharing[i]! cache visits).bind fun id cache visits =>
      reIngestEntries limits dag ix sharing k (i + 1) (resolved.push id) cache visits

/-- The roots `r, …, r + k - 1` of `ingestTable` (`allowShare`). -/
def reIngestRoots (limits : Limits) (dag : Dag) (ix : ReIndex) (tableSize : Nat)
    (resolved : Array Nat) (roots : Array Ixon.Expr) :
    Nat → Nat → Array Nat → Std.HashMap USize Nat → Nat → ReStep (Array Nat)
  | 0, _, out, cache, visits => .ok out cache visits
  | k + 1, r, out, cache, visits =>
    let ctx : ShareCtx := { resolved, tableSize, entry := none, root := r, allowShare := true }
    (reIngestExpr limits dag ix ctx 0 roots[r]! cache visits).bind fun id cache visits =>
      reIngestRoots limits dag ix tableSize resolved roots k (r + 1) (out.push id) cache visits

/-- A loop of `ingestTable` over the positions `i, …, i + k - 1` of `xs`,
each expanded in the context `ctxOf a acc` and pushed onto the accumulator. -/
theorem loop_sim (limits : Limits) (dag : Dag) (xs : Array Ixon.Expr)
    (ctxOf : Nat → Array Nat → ShareCtx)
    (fast : Nat → Nat → Array Nat → Std.HashMap USize Nat → Nat → ReStep (Array Nat))
    (hfast0 : ∀ i acc cache visits, fast 0 i acc cache visits = .ok acc cache visits)
    (hfast : ∀ k i acc cache visits, fast (k + 1) i acc cache visits =
      (reIngestExpr limits dag (ReIndex.ofDag dag) (ctxOf i acc) 0 xs[i]! cache visits).bind
        fun id cache visits => fast k (i + 1) (acc.push id) cache visits) :
    ∀ (k i : Nat) (acc : Array Nat) (cache : Std.HashMap USize Nat) (visits : Nat)
      (l : List Nat) (_ : l = List.range' i k)
      (f : (a : Nat) → a ∈ l → Array Nat → IngestM (ForInStep (Array Nat))),
      (∀ a h acc, f a h acc = (ingestExpr limits (ctxOf a acc) 0 xs[a]! >>= fun id =>
        pure (ForInStep.yield (acc.push id)))) →
      ReSim (Interner.ofNodes dag.nodes) (fast k i acc cache visits)
        ((forIn' l acc f).run
          { interner := Interner.ofNodes dag.nodes, ptrCache := cache, visits })
  | 0, i, acc, cache, visits, l, hl, f, _ => by
    rw [hfast0]
    simp only [List.range'_zero] at hl
    subst hl
    simp only [List.forIn'_nil, ReSim]
    rfl
  | k + 1, i, acc, cache, visits, l, hl, f, hf => by
    rw [List.range'_succ] at hl
    subst hl
    rw [hfast, List.forIn'_cons, hf, bind_assoc, StateT.run_bind]
    simp only [pure_bind]
    refine ReSim.bind' (reIngestExpr_sim limits dag (ctxOf i acc) xs[i]! 0 cache visits) ?_
    intro id c v
    exact loop_sim limits dag xs ctxOf fast hfast0 hfast k (i + 1) (acc.push id) c v _ rfl _
      (fun a h acc => hf a _ acc)

/-- `ingestTable` (`allowShare`) against the DAG's own interner. -/
def reIngestTable (limits : Limits) (dag : Dag) (ix : ReIndex) (sharing roots : Array Ixon.Expr) :
    ReStep (Array Nat × Array Nat) :=
  (reIngestEntries limits dag ix sharing sharing.size 0 #[] {} 0).bind fun resolved cache visits =>
    (reIngestRoots limits dag ix sharing.size resolved roots roots.size 0 #[] cache visits).bind
      fun out cache visits => .ok (resolved, out) cache visits

theorem ingestTable_sim (limits : Limits) (dag : Dag) (sharing roots : Array Ixon.Expr)
    (hw : ¬sharing.size ≥ wordBound) :
    ReSim (Interner.ofNodes dag.nodes) (reIngestTable limits dag (ReIndex.ofDag dag) sharing roots)
      ((ingestTable limits sharing roots true).run
        { interner := Interner.ofNodes dag.nodes, ptrCache := {}, visits := 0 }) := by
  unfold ingestTable reIngestTable
  simp only [hw, if_false, Std.Legacy.Range.forIn'_eq_forIn'_range', StateT.run_bind]
  refine ReSim.bind' (loop_sim limits dag sharing
    (fun i acc => { resolved := acc, tableSize := sharing.size, entry := some i, root := 0,
                    allowShare := true })
    (reIngestEntries limits dag (ReIndex.ofDag dag) sharing) (fun _ _ _ _ => rfl)
    (fun _ _ _ _ _ => rfl) sharing.size 0 #[] {} 0 _ ?_ _ ?_) ?_
  · simp [Std.Legacy.Range.size]
  · intro a h acc
    have ha : a < sharing.size := by
      have := List.mem_range'.mp h
      simp [Std.Legacy.Range.size] at this
      omega
    rw [getElem!_pos sharing a ha]
  · intro resolved c v
    refine ReSim.bind' (loop_sim limits dag roots
      (fun r acc => { resolved, tableSize := sharing.size, entry := none, root := r,
                      allowShare := true })
      (reIngestRoots limits dag (ReIndex.ofDag dag) sharing.size resolved roots)
      (fun _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) roots.size 0 #[] c v _ ?_ _ ?_) ?_
    · simp [Std.Legacy.Range.size]
    · intro a h acc
      have ha : a < roots.size := by
        have := List.mem_range'.mp h
        simp [Std.Legacy.Range.size] at this
        omega
      rw [getElem!_pos roots a ha]
    · intro out c' v'
      simp only [ReSim]
      rfl

/-! ## The fast re-expansion -/

/-- `reexpand` with the DAG's nodes found by `ReIndex.lookup` and the state
passed explicitly (`reexpand_eq_fast`); when a node is not in the DAG it
runs `reexpand`. The construction re-expands only its own output, whose
nodes are all in the DAG, so there that fallback is defensive; a direct
caller with an encoding of other terms takes it. -/
def reexpandFast (limits : Limits) (dag : Dag) (sharing roots : Array Ixon.Expr) :
    Except SharingError (Array Nat × Array Nat × Nat) :=
  if sharing.size ≥ wordBound then .error (.formatBound "sharing table size" sharing.size) else
  match reIngestTable limits dag (ReIndex.ofDag dag) sharing roots with
  | .ok (resolved, out) _ visits => .ok (resolved, out, visits)
  | .error e => .error e
  | .stop => reexpand limits dag sharing roots

@[csimp] theorem reexpand_eq_fast : @reexpand = @reexpandFast := by
  funext limits dag sharing roots
  unfold reexpandFast
  by_cases hw : sharing.size ≥ wordBound
  · simp only [hw, if_true]
    unfold reexpand ingestTable
    simp only [hw, if_true]
    rfl
  · simp only [hw, if_false]
    have hs := ingestTable_sim limits dag sharing roots hw
    cases hr : reIngestTable limits dag (ReIndex.ofDag dag) sharing roots with
    | ok p cache visits =>
      rw [hr] at hs
      simp only [ReSim] at hs
      obtain ⟨resolved, out⟩ := p
      unfold reexpand
      simp only [hs]
      rfl
    | error e =>
      rw [hr] at hs
      simp only [ReSim] at hs
      unfold reexpand
      simp only [hs]
      rfl
    | stop => rfl

end Ix.Sharing.Exact

end
