import Aiur.Tuple.Circuit.Derivation

namespace Aiur.Tuple.Circuit

/-- One locally checked rule instance, without proofs of its call premises. -/
structure RuleInstance [Field F] (system : System F) where
  chip : Chip F
  row : Row F
  lookup : system.findChip? row.chip = some chip
  valid : chip.ValidRow row

def RuleInstance.conclusion [Field F] {system : System F}
    (rule : RuleInstance system) : Message F := rule.chip.receive rule.row

def RuleInstance.premises [Field F] [DecidableEq F] {system : System F}
    (rule : RuleInstance system) : List (Message F) := rule.chip.premises rule.row

/--
A finite graph of locally valid rules. Every enabled call has an explicit target
with the required conclusion. References may be shared or cyclic, including self-references.
There is no ordering, rank, multiplicity, or source-termination condition.
-/
structure MemoDerivation [Field F] [DecidableEq F] (system : System F)
    (message : Message F) where
  size : Nat
  node : Fin size → RuleInstance system
  root : Fin size
  root_claim : (node root).conclusion = message
  target : (i : Fin size) → Fin (node i).premises.length → Fin size
  target_claim : ∀ i j, (node (target i j)).conclusion = (node i).premises[j]

/-- Memoized acceptance asserts the existence of a finite, possibly cyclic graph. -/
def MemoDerives [Field F] [DecidableEq F] (system : System F) (message : Message F) : Prop :=
  Nonempty (MemoDerivation system message)

def MemoAccepts [Field F] [DecidableEq F] (system : System F)
    (function : String) (args : List (Value F)) (result : Value F) : Prop :=
  MemoDerives system ⟨function, args, result⟩

/-- The claims represented anywhere in a graph, including its root. -/
def MemoDerivation.Claims [Field F] [DecidableEq F] {system : System F} {message : Message F}
    (graph : MemoDerivation system message) (claim : Message F) : Prop :=
  ∃ i, (graph.node i).conclusion = claim

theorem MemoDerivation.root_mem [Field F] [DecidableEq F]
    {system : System F} {message : Message F} (graph : MemoDerivation system message) :
    graph.Claims message := ⟨graph.root, graph.root_claim⟩

theorem MemoDerivation.premise_mem [Field F] [DecidableEq F]
    {system : System F} {message : Message F} (graph : MemoDerivation system message)
    (i : Fin graph.size) {premise : Message F} (member : premise ∈ (graph.node i).premises) :
    graph.Claims premise := by
  obtain ⟨j, bounded, same⟩ := List.mem_iff_getElem.mp member
  exact ⟨graph.target i ⟨j, bounded⟩, (graph.target_claim i ⟨j, bounded⟩).trans same⟩

/-- Build explicit references from a finite table closed under call premises. -/
noncomputable def MemoDerivation.ofClosed [Field F] [DecidableEq F]
    {system : System F} {message : Message F} (rules : List (RuleInstance system))
    (root : ∃ rule ∈ rules, rule.conclusion = message)
    (closed : ∀ rule ∈ rules, ∀ premise ∈ rule.premises,
      ∃ provider ∈ rules, provider.conclusion = premise) : MemoDerivation system message := by
  have locate {claim : Message F} (present : ∃ rule ∈ rules, rule.conclusion = claim) :
      ∃ i : Fin rules.length, rules[i].conclusion = claim := by
    obtain ⟨rule, member, conclusion⟩ := present
    obtain ⟨i, bounded, same⟩ := List.mem_iff_getElem.mp member
    exact ⟨⟨i, bounded⟩, by simpa [same] using conclusion⟩
  let rootIndex := Classical.choose (locate root)
  have targets (i : Fin rules.length) (j : Fin rules[i].premises.length) :
      ∃ target : Fin rules.length, rules[target].conclusion = rules[i].premises[j] :=
    locate (closed rules[i] (List.getElem_mem _) _ (List.getElem_mem _))
  exact {
    size := rules.length
    node := fun i => rules[i]
    root := rootIndex
    root_claim := Classical.choose_spec (locate root)
    target := fun i j => Classical.choose (targets i j)
    target_claim := fun i j => Classical.choose_spec (targets i j)
  }

mutual
  /-- Keep each tree occurrence as a locally valid graph node. -/
  def Derivation.instances [Field F] [DecidableEq F] {system : System F} {message : Message F} :
      Derivation system message → List (RuleInstance system)
    | .node chip row lookup valid children => ⟨chip, row, lookup, valid⟩ :: children.instances

  def Derivations.instances [Field F] [DecidableEq F] {system : System F} {messages : List (Message F)} :
      Derivations system messages → List (RuleInstance system)
    | .nil => []
    | .cons head tail => head.instances ++ tail.instances
end

theorem Derivation.root_instance [Field F] [DecidableEq F]
    {system : System F} {message : Message F} (tree : Derivation system message) :
    ∃ rule ∈ tree.instances, rule.conclusion = message := by
  cases tree with
  | node chip row lookup valid children => exact ⟨⟨chip, row, lookup, valid⟩, by simp [instances], rfl⟩

theorem Derivations.root_instances [Field F] [DecidableEq F]
    {system : System F} {messages : List (Message F)} (trees : Derivations system messages) :
    ∀ message ∈ messages, ∃ rule ∈ trees.instances, rule.conclusion = message := by
  cases trees with
  | nil => simp
  | cons head tail =>
      intro message member
      rcases List.mem_cons.mp member with rfl | member
      · obtain ⟨rule, present, conclusion⟩ := head.root_instance
        exact ⟨rule, by simp [instances, present], conclusion⟩
      · obtain ⟨rule, present, conclusion⟩ := tail.root_instances message member
        exact ⟨rule, by simp [instances, present], conclusion⟩
termination_by structural trees

theorem Derivation.instances_closed [Field F] [DecidableEq F]
    {system : System F} {message : Message F} (tree : Derivation system message) :
    ∀ rule ∈ tree.instances, ∀ premise ∈ rule.premises,
      ∃ provider ∈ tree.instances, provider.conclusion = premise := by
  induction tree using Derivation.rec
    (motive_2 := fun messages (trees : Derivations system messages) =>
      ∀ (rule : RuleInstance system), rule ∈ trees.instances → ∀ premise ∈ rule.premises,
      ∃ provider ∈ trees.instances, provider.conclusion = premise) with
  | node chip row lookup valid children ih =>
      intro rule member premise required
      simp only [instances, List.mem_cons] at member
      rcases member with rfl | member
      · obtain ⟨provider, present, conclusion⟩ := children.root_instances premise required
        exact ⟨provider, by simp [instances, present], conclusion⟩
      · obtain ⟨provider, present, conclusion⟩ := ih rule member premise required
        exact ⟨provider, by simp [instances, present], conclusion⟩
  | nil => rename_i rule member premise required; simp [Derivations.instances] at member
  | cons head tail headIH tailIH =>
      rename_i rule member premise required
      simp only [Derivations.instances, List.mem_append] at member
      rcases member with member | member
      · obtain ⟨provider, present, conclusion⟩ := headIH rule member premise required
        exact ⟨provider, by simp [Derivations.instances, present], conclusion⟩
      · obtain ⟨provider, present, conclusion⟩ := tailIH rule member premise required
        exact ⟨provider, by simp [Derivations.instances, present], conclusion⟩

/-- Every ordinary derivation supplies a memoized graph; cycles are not required. -/
noncomputable def Derivation.toMemo [Field F] [DecidableEq F]
    {system : System F} {message : Message F} (tree : Derivation system message) :
    MemoDerivation system message :=
  .ofClosed tree.instances tree.root_instance tree.instances_closed

theorem Derives.memo [Field F] [DecidableEq F] {system : System F} {message : Message F}
    (derives : Derives system message) : MemoDerives system message := by
  obtain ⟨tree⟩ := derives
  exact ⟨tree.toMemo⟩

end Aiur.Tuple.Circuit
