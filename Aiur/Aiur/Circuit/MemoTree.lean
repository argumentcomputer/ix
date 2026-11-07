import Aiur.Circuit.MemoAcyclic

namespace Aiur.Circuit

variable {F : Type} [Field F] [DecidableEq F]
variable {system : System F} {rom : WireROM F} {message : Message F}

/-- A finite natural rank decreasing along every reference rules out cycles. -/
theorem MemoDerivation.acyclic_of_rank (graph : MemoDerivation system rom message)
    (rank : Fin graph.size → Nat)
    (decreases : ∀ i j, rank (graph.target i j) < rank i) : graph.Acyclic := by
  have edge {child parent} (dependency : graph.Dependency child parent) : rank child < rank parent := by
    obtain ⟨j, rfl⟩ := dependency
    exact decreases parent j
  have path {child parent} (steps : Relation.TransGen graph.Dependency child parent) :
      rank child < rank parent := by
    induction steps with
    | single dependency => exact edge dependency
    | tail _ dependency ih => exact ih.trans (edge dependency)
  exact fun i cycle => (Nat.lt_irrefl (rank i)) (path cycle)

/-- Build an acyclic graph from a finite collection of ranked rules, choosing
only providers of strictly smaller rank. Repeated claims need not be merged. -/
theorem MemoDerivation.exists_acyclic_of_ranked
    (rules : List (RuleInstance system rom × Nat))
    (root : ∃ rule ∈ rules, rule.1.conclusion = message)
    (closed : ∀ rule ∈ rules, ∀ premise ∈ rule.1.premises,
      ∃ provider ∈ rules, provider.1.conclusion = premise ∧ provider.2 < rule.2) :
    ∃ graph : MemoDerivation system rom message, graph.Acyclic := by
  classical
  have locate {P : RuleInstance system rom × Nat → Prop}
      (present : ∃ rule ∈ rules, P rule) : ∃ i : Fin rules.length, P rules[i] := by
    obtain ⟨rule, member, property⟩ := present
    obtain ⟨i, bounded, same⟩ := List.mem_iff_getElem.mp member
    exact ⟨⟨i, bounded⟩, by simpa [same] using property⟩
  let rootIndex := Classical.choose (locate root)
  have targets (i : Fin rules.length) (j : Fin rules[i].1.premises.length) :
      ∃ target : Fin rules.length,
        rules[target].1.conclusion = rules[i].1.premises[j] ∧ rules[target].2 < rules[i].2 :=
    locate (closed rules[i] (List.getElem_mem _) _ (List.getElem_mem _))
  let graph : MemoDerivation system rom message := {
    size := rules.length
    node := fun i => rules[i].1
    root := rootIndex
    root_claim := Classical.choose_spec (locate root)
    target := fun i j => Classical.choose (targets i j)
    target_claim := fun i j => (Classical.choose_spec (targets i j)).1
  }
  refine ⟨graph, graph.acyclic_of_rank (fun i => rules[i].2) ?_⟩
  exact fun i j => (Classical.choose_spec (targets i j)).2

mutual
  /-- Height of a finite rule derivation. -/
  def Derivation.height {message : Message F} : Derivation system rom message → Nat
    | .node _ _ _ _ children => children.height + 1
    | .table _ => 0

  def Derivations.height {messages : List (Message F)} : Derivations system rom messages → Nat
    | .nil => 0
    | .cons head tail => max head.height tail.height
end

mutual
  /-- Every occurrence is accompanied by its subtree height. -/
  def Derivation.rankedInstances {message : Message F} :
      Derivation system rom message → List (RuleInstance system rom × Nat)
    | .node chip row lookup valid children =>
        (.node chip row lookup valid, children.height + 1) :: children.rankedInstances
    | .table member => [(.table _ member, 0)]

  def Derivations.rankedInstances {messages : List (Message F)} :
      Derivations system rom messages → List (RuleInstance system rom × Nat)
    | .nil => []
    | .cons head tail => head.rankedInstances ++ tail.rankedInstances
end

theorem Derivation.root_rankedInstance (tree : Derivation system rom message) :
    ∃ rule ∈ tree.rankedInstances, rule.1.conclusion = message ∧ rule.2 = tree.height := by
  cases tree with
  | node chip row lookup valid children =>
      exact ⟨(.node chip row lookup valid, children.height + 1), by simp [rankedInstances], rfl, rfl⟩
  | table member => exact ⟨(.table _ member, 0), by simp [rankedInstances], rfl, rfl⟩

theorem Derivations.root_rankedInstances {messages : List (Message F)}
    (trees : Derivations system rom messages) :
    ∀ message ∈ messages, ∃ rule ∈ trees.rankedInstances,
      rule.1.conclusion = message ∧ rule.2 ≤ trees.height := by
  cases trees with
  | nil => simp
  | cons head tail =>
      intro message member
      rcases List.mem_cons.mp member with rfl | member
      · obtain ⟨rule, present, conclusion, rank⟩ := head.root_rankedInstance
        exact ⟨rule, by simp [rankedInstances, present], conclusion,
          by simp [rank, height]⟩
      · obtain ⟨rule, present, conclusion, rank⟩ := tail.root_rankedInstances message member
        exact ⟨rule, by simp [rankedInstances, present], conclusion,
          rank.trans (Nat.le_max_right head.height tail.height)⟩
termination_by structural trees

theorem Derivation.rankedInstances_closed (tree : Derivation system rom message) :
    ∀ rule ∈ tree.rankedInstances, ∀ premise ∈ rule.1.premises,
      ∃ provider ∈ tree.rankedInstances,
        provider.1.conclusion = premise ∧ provider.2 < rule.2 := by
  induction tree using Derivation.rec
    (motive_2 := fun messages (trees : Derivations system rom messages) =>
      ∀ rule ∈ trees.rankedInstances, ∀ premise ∈ rule.1.premises,
      ∃ provider ∈ trees.rankedInstances,
        provider.1.conclusion = premise ∧ provider.2 < rule.2) with
  | node chip row lookup valid children ih =>
      intro rule member premise required
      simp only [rankedInstances, List.mem_cons] at member
      rcases member with rfl | member
      · obtain ⟨provider, present, conclusion, rank⟩ := children.root_rankedInstances premise required
        exact ⟨provider, by simp [rankedInstances, present], conclusion,
          Nat.lt_succ_of_le rank⟩
      · obtain ⟨provider, present, conclusion, rank⟩ := ih rule member premise required
        exact ⟨provider, by simp [rankedInstances, present], conclusion, rank⟩
  | table member =>
      intro rule present premise required
      simp only [rankedInstances, List.mem_singleton] at present
      subst rule
      simp [RuleInstance.premises] at required
  | nil => rename_i rule member premise required; simp [Derivations.rankedInstances] at member
  | cons head tail headIH tailIH =>
      rename_i rule member premise required
      simp only [Derivations.rankedInstances, List.mem_append] at member
      rcases member with member | member
      · obtain ⟨provider, present, conclusion, rank⟩ := headIH rule member premise required
        exact ⟨provider, by simp [Derivations.rankedInstances, present], conclusion, rank⟩
      · obtain ⟨provider, present, conclusion, rank⟩ := tailIH rule member premise required
        exact ⟨provider, by simp [Derivations.rankedInstances, present], conclusion, rank⟩

/-- A finite derivation always has an acyclic memoized representation, even
when the same claim occurs at different heights in the tree. -/
theorem Derives.acyclic (derives : Derives system rom message) :
    ∃ graph : MemoDerivation system rom message, graph.Acyclic := by
  obtain ⟨tree⟩ := derives
  obtain ⟨rule, present, conclusion, _⟩ := tree.root_rankedInstance
  exact MemoDerivation.exists_acyclic_of_ranked tree.rankedInstances
    ⟨rule, present, conclusion⟩ tree.rankedInstances_closed

theorem derives_iff_acyclic_memo :
    Derives system rom message ↔ ∃ graph : MemoDerivation system rom message, graph.Acyclic :=
  ⟨Derives.acyclic, fun ⟨graph, acyclic⟩ => graph.derives_of_acyclic acyclic⟩

end Aiur.Circuit
