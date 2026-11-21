import Aiur.Circuit.Derivation

namespace Aiur.Circuit

variable {F : Type} {rom : WireROM F}

/-- One locally checked rule instance, without proofs of its call premises. -/
inductive RuleInstance [Field F] (system : System F) (rom : WireROM F) where
  | node (chip : Chip F) (row : Row F)
      (lookup : system.findChip? row.chip = some chip) (valid : chip.ValidRow rom row)
  | table (message : Message F) (member : system.MapClaim message)

def RuleInstance.conclusion [Field F] {system : System F}
    : RuleInstance system rom → Message F
  | .node chip row _ _ => chip.receive row
  | .table message _ => message

def RuleInstance.premises [Field F] [DecidableEq F] {system : System F}
    : RuleInstance system rom → List (Message F)
  | .node chip row _ _ => chip.premises row
  | .table _ _ => []

/--
A finite graph of locally valid rules. Every enabled call has an explicit target
with the required conclusion. References may be shared or cyclic, including self-references.
There is no ordering, rank, multiplicity, or source-termination condition.
-/
structure MemoDerivation [Field F] [DecidableEq F] (system : System F) (rom : WireROM F)
    (message : Message F) where
  size : Nat
  node : Fin size → RuleInstance system rom
  root : Fin size
  root_claim : (node root).conclusion = message
  target : (i : Fin size) → Fin (node i).premises.length → Fin size
  target_claim : ∀ i j, (node (target i j)).conclusion = (node i).premises[j]

/-- Memoized acceptance asserts the existence of a finite, possibly cyclic graph. -/
def MemoDerives [Field F] [DecidableEq F] (system : System F) (rom : WireROM F) (message : Message F) : Prop :=
  Nonempty (MemoDerivation system rom message)

def MemoAccepts [Field F] [DecidableEq F] (system : System F) (rom : WireROM F)
    (function : String) (args : List (WireValue F)) (result : WireValue F) : Prop :=
  MemoDerives system rom ⟨function, args, result⟩

/-- The claims represented anywhere in a graph, including its root. -/
def MemoDerivation.Claims [Field F] [DecidableEq F] {system : System F} {message : Message F}
    (graph : MemoDerivation system rom message) (claim : Message F) : Prop :=
  ∃ i, (graph.node i).conclusion = claim

theorem MemoDerivation.root_mem [Field F] [DecidableEq F]
    {system : System F} {message : Message F} (graph : MemoDerivation system rom message) :
    graph.Claims message := ⟨graph.root, graph.root_claim⟩

theorem MemoDerivation.premise_mem [Field F] [DecidableEq F]
    {system : System F} {message : Message F} (graph : MemoDerivation system rom message)
    (i : Fin graph.size) {premise : Message F} (member : premise ∈ (graph.node i).premises) :
    graph.Claims premise := by
  obtain ⟨j, bounded, same⟩ := List.mem_iff_getElem.mp member
  exact ⟨graph.target i ⟨j, bounded⟩, (graph.target_claim i ⟨j, bounded⟩).trans same⟩

/-- Build explicit references from a finite table closed under call premises. -/
noncomputable def MemoDerivation.ofClosed [Field F] [DecidableEq F]
    {system : System F} {message : Message F} (rules : List (RuleInstance system rom))
    (root : ∃ rule ∈ rules, rule.conclusion = message)
    (closed : ∀ rule ∈ rules, ∀ premise ∈ rule.premises,
      ∃ provider ∈ rules, provider.conclusion = premise) : MemoDerivation system rom message := by
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
      Derivation system rom message → List (RuleInstance system rom)
    | .node chip row lookup valid children => .node chip row lookup valid :: children.instances
    | .table member => [.table _ member]

  def Derivations.instances [Field F] [DecidableEq F] {system : System F} {messages : List (Message F)} :
      Derivations system rom messages → List (RuleInstance system rom)
    | .nil => []
    | .cons head tail => head.instances ++ tail.instances
end

theorem Derivation.root_instance [Field F] [DecidableEq F]
    {system : System F} {message : Message F} (tree : Derivation system rom message) :
    ∃ rule ∈ tree.instances, rule.conclusion = message := by
  cases tree with
  | node chip row lookup valid children => exact ⟨.node chip row lookup valid, by simp [instances], rfl⟩
  | table member => exact ⟨.table _ member, by simp [instances], rfl⟩

theorem Derivations.root_instances [Field F] [DecidableEq F]
    {system : System F} {messages : List (Message F)} (trees : Derivations system rom messages) :
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
    {system : System F} {message : Message F} (tree : Derivation system rom message) :
    ∀ rule ∈ tree.instances, ∀ premise ∈ rule.premises,
      ∃ provider ∈ tree.instances, provider.conclusion = premise := by
  induction tree using Derivation.rec
    (motive_2 := fun messages (trees : Derivations system rom messages) =>
      ∀ (rule : RuleInstance system rom), rule ∈ trees.instances → ∀ premise ∈ rule.premises,
      ∃ provider ∈ trees.instances, provider.conclusion = premise) with
  | node chip row lookup valid children ih =>
      intro rule member premise required
      simp only [instances, List.mem_cons] at member
      rcases member with rfl | member
      · obtain ⟨provider, present, conclusion⟩ := children.root_instances premise required
        exact ⟨provider, by simp [instances, present], conclusion⟩
      · obtain ⟨provider, present, conclusion⟩ := ih rule member premise required
        exact ⟨provider, by simp [instances, present], conclusion⟩
  | table member =>
      intro rule present premise required
      simp only [instances, List.mem_singleton] at present
      subst rule
      simp [RuleInstance.premises] at required
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
    {system : System F} {message : Message F} (tree : Derivation system rom message) :
    MemoDerivation system rom message :=
  .ofClosed tree.instances tree.root_instance tree.instances_closed

theorem Derives.memo [Field F] [DecidableEq F] {system : System F} {message : Message F}
    (derives : Derives system rom message) : MemoDerives system rom message := by
  obtain ⟨tree⟩ := derives
  exact ⟨tree.toMemo⟩

end Aiur.Circuit
