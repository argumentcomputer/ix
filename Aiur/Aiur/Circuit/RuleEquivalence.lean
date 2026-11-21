import Aiur.Circuit.CheckerContext
import Aiur.Circuit.MemoAcyclic

namespace Aiur.Circuit

variable {F : Type} [Field F] [DecidableEq F]

/-- A local conclusion/premise relation. Auxiliary assignments are existential;
premises retain their multiplicities but may be reordered. Static maps are
zero-premise rules in this same interface. -/
def System.Rule (system : System F) (rom : WireROM F)
    (conclusion : Message F) (premises : List (Message F)) : Prop :=
  ∃ rule : RuleInstance system rom,
    rule.conclusion = conclusion ∧ rule.premises.Perm premises

def System.RuleRefines (source target : System F) : Prop :=
  ∀ rom conclusion premises, source.Rule rom conclusion premises → target.Rule rom conclusion premises

def System.RuleEquiv (source target : System F) : Prop :=
  ∀ rom conclusion premises, source.Rule rom conclusion premises ↔ target.Rule rom conclusion premises

theorem System.RuleEquiv.refl (system : System F) : system.RuleEquiv system := fun _ _ _ => Iff.rfl

theorem System.RuleEquiv.symm {source target : System F} (same : source.RuleEquiv target) :
    target.RuleEquiv source := fun rom conclusion premises => (same rom conclusion premises).symm

theorem System.RuleEquiv.trans {a b c : System F}
    (ab : a.RuleEquiv b) (bc : b.RuleEquiv c) : a.RuleEquiv c :=
  fun rom conclusion premises => (ab rom conclusion premises).trans (bc rom conclusion premises)

theorem System.RuleEquiv.forward {source target : System F} (same : source.RuleEquiv target) :
    source.RuleRefines target := fun rom conclusion premises => (same rom conclusion premises).mp

theorem System.RuleRefines.derives {source target : System F}
    (refines : source.RuleRefines target) {rom : WireROM F} {message : Message F}
    (derived : Derives source rom message) : Derives target rom message := by
  obtain ⟨tree⟩ := derived
  induction tree using Derivation.rec
    (motive_2 := fun messages _ => ∀ message ∈ messages, Derives target rom message) with
  | node chip row lookup valid children ih =>
      obtain ⟨rule, conclusion, premises⟩ := refines rom _ _
        ⟨.node chip row lookup valid, rfl, List.Perm.refl _⟩
      change rule.conclusion = chip.receive row at conclusion
      rw [← conclusion]
      exact rule.derives (fun message member => ih message (premises.mem_iff.mp member))
  | table member =>
      obtain ⟨rule, conclusion, premises⟩ := refines rom _ _
        ⟨.table _ member, rfl, List.Perm.refl []⟩
      change rule.conclusion = _ at conclusion
      dsimp only [RuleInstance.conclusion] at conclusion
      rw [← conclusion]
      exact rule.derives (fun message member => by simpa using premises.mem_iff.mp member)
  | nil => simp_all
  | cons _ _ head tail =>
      rename_i message member
      rcases List.mem_cons.mp member with rfl | member
      · exact head
      · exact tail message member

theorem System.RuleEquiv.derives_iff {source target : System F}
    (same : source.RuleEquiv target) {rom : WireROM F} {message : Message F} :
    Derives source rom message ↔ Derives target rom message :=
  ⟨same.forward.derives, same.symm.forward.derives⟩

/-- Pick a corresponding row separately for every proof node, without merging
nodes whose conclusions happen to agree. -/
noncomputable def System.RuleRefines.instance {source target : System F}
    (refines : source.RuleRefines target) {rom : WireROM F}
    (rule : RuleInstance source rom) : RuleInstance target rom :=
  Classical.choose (refines rom rule.conclusion rule.premises ⟨rule, rfl, List.Perm.refl _⟩)

theorem System.RuleRefines.instance_spec {source target : System F}
    (refines : source.RuleRefines target) {rom : WireROM F} (rule : RuleInstance source rom) :
    (refines.instance rule).conclusion = rule.conclusion ∧
      (refines.instance rule).premises.Perm rule.premises :=
  Classical.choose_spec (refines rom rule.conclusion rule.premises ⟨rule, rfl, List.Perm.refl _⟩)

private theorem premise_index {source target : System F}
    (refines : source.RuleRefines target) {rom : WireROM F} (rule : RuleInstance source rom)
    (j : Fin (refines.instance rule).premises.length) :
    ∃ k : Fin rule.premises.length, rule.premises[k] = (refines.instance rule).premises[j] := by
  have member := (refines.instance_spec rule).2.mem_iff.mp
    (List.getElem_mem (l := (refines.instance rule).premises) (n := j.val) j.isLt)
  obtain ⟨k, bounded, same⟩ := List.mem_iff_getElem.mp member
  exact ⟨⟨k, bounded⟩, same⟩

/-- Transport a graph with the same node indices. Each new premise occurrence
uses an edge of its corresponding old node; sharing and cycles are allowed. -/
noncomputable def MemoDerivation.mapRules {source target : System F} {rom : WireROM F}
    {message : Message F} (graph : MemoDerivation source rom message)
    (refines : source.RuleRefines target) : MemoDerivation target rom message where
  size := graph.size
  node i := refines.instance (graph.node i)
  root := graph.root
  root_claim := (refines.instance_spec (graph.node graph.root)).1.trans graph.root_claim
  target i j := graph.target i (Classical.choose (premise_index refines (graph.node i) j))
  target_claim i j := by
    exact ((refines.instance_spec _).1.trans (graph.target_claim i _)).trans
      (Classical.choose_spec (premise_index refines (graph.node i) j))

theorem MemoDerivation.mapRules_dependency {source target : System F} {rom : WireROM F}
    {message : Message F} (graph : MemoDerivation source rom message)
    (refines : source.RuleRefines target) {child parent : Fin graph.size}
    (edge : (graph.mapRules refines).Dependency child parent) : graph.Dependency child parent := by
  obtain ⟨j, same⟩ := edge
  exact ⟨Classical.choose (premise_index refines (graph.node parent) j), same⟩

theorem MemoDerivation.mapRules_acyclic {source target : System F} {rom : WireROM F}
    {message : Message F} (graph : MemoDerivation source rom message)
    (refines : source.RuleRefines target) (acyclic : graph.Acyclic) :
    (graph.mapRules refines).Acyclic := by
  intro i cycle
  exact acyclic i (Relation.TransGen.mono (fun _ _ edge => graph.mapRules_dependency refines edge) i i cycle)

theorem System.RuleRefines.memoDerives {source target : System F}
    (refines : source.RuleRefines target) {rom : WireROM F} {message : Message F}
    (derived : MemoDerives source rom message) : MemoDerives target rom message := by
  obtain ⟨graph⟩ := derived
  exact ⟨graph.mapRules refines⟩

theorem System.RuleEquiv.memoDerives_iff {source target : System F}
    (same : source.RuleEquiv target) {rom : WireROM F} {message : Message F} :
    MemoDerives source rom message ↔ MemoDerives target rom message :=
  ⟨same.forward.memoDerives, same.symm.forward.memoDerives⟩

theorem System.RuleEquiv.acyclic_iff {source target : System F}
    (same : source.RuleEquiv target) {rom : WireROM F} {message : Message F} :
    (∃ graph : MemoDerivation source rom message, graph.Acyclic) ↔
      (∃ graph : MemoDerivation target rom message, graph.Acyclic) := by
  constructor
  · rintro ⟨graph, acyclic⟩
    exact ⟨graph.mapRules same.forward, graph.mapRules_acyclic same.forward acyclic⟩
  · rintro ⟨graph, acyclic⟩
    exact ⟨graph.mapRules same.symm.forward, graph.mapRules_acyclic same.symm.forward acyclic⟩

/-- Equality of local rules is sufficient for existential trace equivalence;
the rows and their auxiliary widths need not be the same. -/
theorem System.RuleEquiv.check_iff {source target : System F}
    (same : source.RuleEquiv target) {rom : WireROM F} {root : Message F}
    (sourceContext : source.checkContext rom root = .ok ())
    (targetContext : target.checkContext rom root = .ok ()) :
    (∃ rows, source.check rom root rows = .ok ()) ↔
      (∃ rows, target.check rom root rows = .ok ()) := by
  rw [source.check_derives_iff sourceContext, target.check_derives_iff targetContext]
  exact same.derives_iff

theorem System.RuleEquiv.checkMemo_iff {source target : System F}
    (same : source.RuleEquiv target) {rom : WireROM F} {root : Message F}
    (sourceContext : source.checkContext rom root = .ok ())
    (targetContext : target.checkContext rom root = .ok ()) :
    (∃ rows, source.checkMemo rom root rows = .ok ()) ↔
      (∃ rows, target.checkMemo rom root rows = .ok ()) := by
  rw [source.checkMemo_derives_iff sourceContext, target.checkMemo_derives_iff targetContext]
  exact same.memoDerives_iff

end Aiur.Circuit
