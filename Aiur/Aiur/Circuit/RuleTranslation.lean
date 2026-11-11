import Aiur.Circuit.RuleEquivalence
import Mathlib.Data.Fintype.Sigma

namespace Aiur.Circuit

variable {F : Type} [Field F] [DecidableEq F]

def Message.rename (rename : String → String) (message : Message F) : Message F :=
  { message with channel := rename message.channel }

/-- Uniform lifting is required for each original channel, not merely for the
union of the rules in an equivalence class. -/
structure System.RuleTranslation (source target : System F) (rename : String → String) : Prop where
  forward : ∀ rom (rule : RuleInstance source rom), ∃ next : RuleInstance target rom,
    next.conclusion = rule.conclusion.rename rename ∧
    next.premises = rule.premises.map (Message.rename rename)
  backward : ∀ rom (rule : RuleInstance target rom) (claim : Message F),
    claim.rename rename = rule.conclusion → ∃ previous : RuleInstance source rom,
      previous.conclusion = claim ∧
      previous.premises.map (Message.rename rename) = rule.premises

theorem System.RuleTranslation.derives_forward {source target : System F} {rename : String → String}
    (same : source.RuleTranslation target rename) {rom : WireROM F} {claim : Message F}
    (derived : Derives source rom claim) : Derives target rom (claim.rename rename) := by
  obtain ⟨tree⟩ := derived
  induction tree using Derivation.rec
    (motive_2 := fun messages _ => ∀ message ∈ messages, Derives target rom (message.rename rename)) with
  | node chip row lookup valid children ih =>
      obtain ⟨rule, conclusion, premises⟩ := same.forward rom (.node chip row lookup valid)
      change rule.conclusion = (chip.receive row).rename rename at conclusion
      rw [← conclusion]
      apply rule.derives
      intro message member
      rw [premises] at member
      obtain ⟨old, oldMember, renamed⟩ := List.mem_map.mp member
      rw [← renamed]
      exact ih old oldMember
  | table member =>
      obtain ⟨rule, conclusion, premises⟩ := same.forward rom (.table _ member)
      dsimp only [RuleInstance.conclusion] at conclusion
      rw [← conclusion]
      have empty : rule.premises = [] := premises
      exact rule.derives (by rw [empty]; simp)
  | nil => simp_all
  | cons _ _ head tail =>
      rename_i message member
      rcases List.mem_cons.mp member with rfl | member
      · exact head
      · exact tail message member

theorem System.RuleTranslation.derives_backward {source target : System F} {rename : String → String}
    (same : source.RuleTranslation target rename) {rom : WireROM F} {claim : Message F}
    (derived : Derives target rom (claim.rename rename)) : Derives source rom claim := by
  obtain ⟨tree⟩ := derived
  have lift {message : Message F} (tree : Derivation target rom message) :
      ∀ claim, claim.rename rename = message → Derives source rom claim := by
    refine Derivation.rec
      (motive_1 := fun message _ => ∀ claim, claim.rename rename = message → Derives source rom claim)
      (motive_2 := fun messages _ => ∀ message ∈ messages, ∀ claim,
        claim.rename rename = message → Derives source rom claim) ?_ ?_ ?_ ?_ tree
    · intro chip row lookup valid children ih claim renamed
      obtain ⟨rule, conclusion, premises⟩ := same.backward rom (.node chip row lookup valid) claim renamed
      change rule.premises.map (Message.rename rename) = chip.premises row at premises
      rw [← conclusion]
      apply rule.derives
      intro premise member
      exact ih (premise.rename rename) (by rw [← premises]; exact List.mem_map.mpr ⟨premise, member, rfl⟩)
        premise rfl
    · intro message member claim renamed
      obtain ⟨rule, conclusion, premises⟩ := same.backward rom (.table _ member) claim renamed
      rw [← conclusion]
      have empty : rule.premises = [] := List.map_eq_nil_iff.mp premises
      exact rule.derives (by simp [empty])
    · simp
    · intro first rest headTree tailTrees head tail message member claim renamed
      rcases List.mem_cons.mp member with rfl | member
      · exact head claim renamed
      · exact tail message member claim renamed
  exact lift tree claim rfl

theorem System.RuleTranslation.derives_iff {source target : System F} {rename : String → String}
    (same : source.RuleTranslation target rename) {rom : WireROM F} {claim : Message F} :
    Derives source rom claim ↔ Derives target rom (claim.rename rename) :=
  ⟨same.derives_forward, same.derives_backward⟩

/-- A finite index type is equivalent to the concrete finite indices used by
the graph datatype. This is also useful when a translated node needs copies. -/
noncomputable def MemoDerivation.ofFinite {system : System F} {rom : WireROM F} {claim : Message F}
    {I : Type} [Fintype I] (node : I → RuleInstance system rom) (root : I)
    (root_claim : (node root).conclusion = claim)
    (target : (i : I) → Fin (node i).premises.length → I)
    (target_claim : ∀ i j, (node (target i j)).conclusion = (node i).premises[j]) :
    MemoDerivation system rom claim where
  size := Fintype.card I
  node i := node ((Fintype.equivFin I).symm i)
  root := Fintype.equivFin I root
  root_claim := by simpa using root_claim
  target i j := Fintype.equivFin I (target ((Fintype.equivFin I).symm i) j)
  target_claim i j := by simpa using target_claim ((Fintype.equivFin I).symm i) j

/-- Mapping graph nodes to another graph and preserving every edge preserves
acyclicity. The node map need not be injective. -/
theorem MemoDerivation.acyclic_of_projection {source target : System F} {rom : WireROM F}
    {a b : Message F} (original : MemoDerivation source rom a) (next : MemoDerivation target rom b)
    (project : Fin next.size → Fin original.size)
    (edges : ∀ {child parent}, next.Dependency child parent →
      original.Dependency (project child) (project parent))
    (acyclic : original.Acyclic) : next.Acyclic := by
  have paths {a b} (path : Relation.TransGen next.Dependency a b) :
      Relation.TransGen original.Dependency (project a) (project b) := by
    induction path with
    | single edge => exact .single (edges edge)
    | tail _ edge ih => exact .tail ih (edges edge)
  exact fun i path => acyclic (project i) (paths path)

noncomputable def System.RuleTranslation.forwardInstance {source target : System F}
    {rename : String → String} (same : source.RuleTranslation target rename)
    {rom : WireROM F} (rule : RuleInstance source rom) : RuleInstance target rom :=
  Classical.choose (same.forward rom rule)

theorem System.RuleTranslation.forwardInstance_spec {source target : System F}
    {rename : String → String} (same : source.RuleTranslation target rename)
    {rom : WireROM F} (rule : RuleInstance source rom) :
    (same.forwardInstance rule).conclusion = rule.conclusion.rename rename ∧
    (same.forwardInstance rule).premises = rule.premises.map (Message.rename rename) :=
  Classical.choose_spec (same.forward rom rule)

noncomputable def MemoDerivation.renameRules {source target : System F} {rename : String → String}
    {rom : WireROM F} {claim : Message F} (graph : MemoDerivation source rom claim)
    (same : source.RuleTranslation target rename) : MemoDerivation target rom (claim.rename rename) where
  size := graph.size
  node i := same.forwardInstance (graph.node i)
  root := graph.root
  root_claim := (same.forwardInstance_spec _).1.trans (congrArg (Message.rename rename) graph.root_claim)
  target i j := graph.target i ⟨j.val, by simpa [(same.forwardInstance_spec _).2] using j.isLt⟩
  target_claim i j := by
    rw [(same.forwardInstance_spec _).1, graph.target_claim]
    simp only [Fin.getElem_fin, (same.forwardInstance_spec _).2, List.getElem_map]

theorem MemoDerivation.renameRules_acyclic {source target : System F} {rename : String → String}
    {rom : WireROM F} {claim : Message F} (graph : MemoDerivation source rom claim)
    (same : source.RuleTranslation target rename) (acyclic : graph.Acyclic) :
    (graph.renameRules same).Acyclic := by
  apply graph.acyclic_of_projection (graph.renameRules same) id ?_ acyclic
  rintro child parent ⟨j, rfl⟩
  exact ⟨⟨j.val, by simpa only [renameRules, (same.forwardInstance_spec _).2,
    List.length_map, id] using j.isLt⟩, rfl⟩

noncomputable def System.RuleTranslation.backwardInstance {source target : System F}
    {rename : String → String} (same : source.RuleTranslation target rename)
    {rom : WireROM F} (rule : RuleInstance target rom) (claim : Message F)
    (renamed : claim.rename rename = rule.conclusion) : RuleInstance source rom :=
  Classical.choose (same.backward rom rule claim renamed)

theorem System.RuleTranslation.backwardInstance_spec {source target : System F}
    {rename : String → String} (same : source.RuleTranslation target rename)
    {rom : WireROM F} (rule : RuleInstance target rom) (claim : Message F)
    (renamed : claim.rename rename = rule.conclusion) :
    (same.backwardInstance rule claim renamed).conclusion = claim ∧
    (same.backwardInstance rule claim renamed).premises.map (Message.rename rename) = rule.premises :=
  Classical.choose_spec (same.backward rom rule claim renamed)

/-- Duplicate an optimized node when its incoming edges request different
original channels. Edges still project to edges of the optimized graph. -/
theorem MemoDerivation.liftRules {source target : System F} {rename : String → String}
    {rom : WireROM F} {claim : Message F}
    (graph : MemoDerivation target rom (claim.rename rename))
    (same : source.RuleTranslation target rename)
    (finite : ∀ message : Message F, Finite {c : Message F // c.rename rename = message}) :
    ∃ lifted : MemoDerivation source rom claim, graph.Acyclic → lifted.Acyclic := by
  classical
  let I := (i : Fin graph.size) × {c : Message F // c.rename rename = (graph.node i).conclusion}
  letI (i : Fin graph.size) : Fintype {c : Message F // c.rename rename = (graph.node i).conclusion} :=
    @Fintype.ofFinite _ (finite _)
  letI : Fintype I := inferInstanceAs (Fintype ((i : Fin graph.size) ×
    {c : Message F // c.rename rename = (graph.node i).conclusion}))
  let node : I → RuleInstance source rom := fun i => same.backwardInstance (graph.node i.1) i.2.val i.2.property
  have spec (i : I) : (node i).conclusion = i.2.val ∧
      (node i).premises.map (Message.rename rename) = (graph.node i.1).premises :=
    same.backwardInstance_spec _ _ _
  let position (i : I) (j : Fin (node i).premises.length) : Fin (graph.node i.1).premises.length :=
    ⟨j.val, by simpa only [← (spec i).2, List.length_map, id] using j.isLt⟩
  have premise (i : I) (j : Fin (node i).premises.length) :
      ((node i).premises[j]).rename rename = (graph.node i.1).premises[position i j] := by
    simp only [Fin.getElem_fin, ← (spec i).2, List.getElem_map, position]
  let target (i : I) (j : Fin (node i).premises.length) : I :=
    ⟨graph.target i.1 (position i j),
      ⟨(node i).premises[j], (premise i j).trans (graph.target_claim i.1 (position i j)).symm⟩⟩
  let root : I := ⟨graph.root, ⟨claim, graph.root_claim.symm⟩⟩
  let lifted := MemoDerivation.ofFinite node root (spec root).1 target (fun i j => (spec (target i j)).1)
  refine ⟨lifted, ?_⟩
  apply graph.acyclic_of_projection lifted (fun i => ((Fintype.equivFin I).symm i).1)
  rintro child parent ⟨j, rfl⟩
  refine ⟨position ((Fintype.equivFin I).symm parent) j, ?_⟩
  simp [lifted, MemoDerivation.ofFinite, target]

theorem System.RuleTranslation.memoDerives_iff {source target : System F} {rename : String → String}
    (same : source.RuleTranslation target rename)
    (finite : ∀ message : Message F, Finite {c : Message F // c.rename rename = message})
    {rom : WireROM F} {claim : Message F} :
    MemoDerives source rom claim ↔ MemoDerives target rom (claim.rename rename) := by
  constructor
  · rintro ⟨graph⟩
    exact ⟨graph.renameRules same⟩
  · rintro ⟨graph⟩
    obtain ⟨lifted, _⟩ := graph.liftRules same finite
    exact ⟨lifted⟩

theorem System.RuleTranslation.acyclic_iff {source target : System F} {rename : String → String}
    (same : source.RuleTranslation target rename)
    (finite : ∀ message : Message F, Finite {c : Message F // c.rename rename = message})
    {rom : WireROM F} {claim : Message F} :
    (∃ graph : MemoDerivation source rom claim, graph.Acyclic) ↔
      (∃ graph : MemoDerivation target rom (claim.rename rename), graph.Acyclic) := by
  constructor
  · rintro ⟨graph, acyclic⟩
    exact ⟨graph.renameRules same, graph.renameRules_acyclic same acyclic⟩
  · rintro ⟨graph, acyclic⟩
    obtain ⟨lifted, preserves⟩ := graph.liftRules same finite
    exact ⟨lifted, preserves acyclic⟩

theorem System.RuleTranslation.check_iff {source target : System F} {rename : String → String}
    (same : source.RuleTranslation target rename) {rom : WireROM F} {root : Message F}
    (sourceContext : source.checkContext rom root = .ok ())
    (targetContext : target.checkContext rom (root.rename rename) = .ok ()) :
    (∃ rows, source.check rom root rows = .ok ()) ↔
      (∃ rows, target.check rom (root.rename rename) rows = .ok ()) := by
  rw [source.check_derives_iff sourceContext, target.check_derives_iff targetContext]
  exact same.derives_iff

theorem System.RuleTranslation.checkMemo_iff {source target : System F} {rename : String → String}
    (same : source.RuleTranslation target rename)
    (finite : ∀ message : Message F, Finite {c : Message F // c.rename rename = message})
    {rom : WireROM F} {root : Message F}
    (sourceContext : source.checkContext rom root = .ok ())
    (targetContext : target.checkContext rom (root.rename rename) = .ok ()) :
    (∃ rows, source.checkMemo rom root rows = .ok ()) ↔
      (∃ rows, target.checkMemo rom (root.rename rename) rows = .ok ()) := by
  rw [source.checkMemo_derives_iff sourceContext, target.checkMemo_derives_iff targetContext]
  exact same.memoDerives_iff finite

end Aiur.Circuit
