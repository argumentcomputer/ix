import Aiur.Circuit.RuleEquivalence

namespace Aiur.Circuit

variable {F : Type} [Field F] [DecidableEq F]

/-- For closed proofs it suffices to reproduce a rule using its available
premises. Each premise has some locally valid provider; it need not already
have a finite derivation. This distinction retains cyclic memoized proofs. -/
def System.SupportRefines (source target : System F) : Prop :=
  ∀ rom (rule : RuleInstance source rom),
    (∀ premise ∈ rule.premises, ∃ provider : RuleInstance source rom, provider.conclusion = premise) →
    ∃ next : RuleInstance target rom,
      next.conclusion = rule.conclusion ∧ next.premises ⊆ rule.premises

def System.SupportEquiv (source target : System F) : Prop :=
  source.SupportRefines target ∧ target.SupportRefines source

theorem System.RuleRefines.supportRefines {source target : System F}
    (refines : source.RuleRefines target) : source.SupportRefines target := by
  intro rom rule _
  obtain ⟨next, conclusion, premises⟩ := refines rom rule.conclusion rule.premises
    ⟨rule, rfl, List.Perm.refl _⟩
  exact ⟨next, conclusion, fun _ member => premises.mem_iff.mp member⟩

theorem System.SupportRefines.derives {source target : System F}
    (refines : source.SupportRefines target) {rom : WireROM F} {message : Message F}
    (derived : Derives source rom message) : Derives target rom message := by
  obtain ⟨tree⟩ := derived
  induction tree using Derivation.rec
    (motive_2 := fun messages _ => ∀ message ∈ messages, Derives target rom message) with
  | node chip row lookup valid children ih =>
      obtain ⟨next, conclusion, premises⟩ := refines rom (.node chip row lookup valid) (by
        intro premise member
        obtain ⟨provider, _, same⟩ := children.root_instances premise member
        exact ⟨provider, same⟩)
      change next.conclusion = chip.receive row at conclusion
      rw [← conclusion]
      exact next.derives (fun premise member => ih premise (premises member))
  | table member =>
      obtain ⟨next, conclusion, premises⟩ := refines rom (.table _ member) (by simp [RuleInstance.premises])
      dsimp only [RuleInstance.conclusion] at conclusion
      rw [← conclusion]
      exact next.derives (fun premise member => by simpa [RuleInstance.premises] using premises member)
  | nil => simp_all
  | cons _ _ head tail =>
      rename_i message member
      rcases List.mem_cons.mp member with rfl | member
      · exact head
      · exact tail message member

private theorem MemoDerivation.supported {source : System F} {rom : WireROM F} {message : Message F}
    (graph : MemoDerivation source rom message) (i : Fin graph.size) :
    ∀ premise ∈ (graph.node i).premises,
      ∃ provider : RuleInstance source rom, provider.conclusion = premise := by
  intro premise member
  obtain ⟨index, same⟩ := graph.premise_mem i member
  exact ⟨graph.node index, same⟩

noncomputable def MemoDerivation.supportInstance {source target : System F}
    {rom : WireROM F} {message : Message F} (graph : MemoDerivation source rom message)
    (refines : source.SupportRefines target) (i : Fin graph.size) : RuleInstance target rom :=
  Classical.choose (refines rom (graph.node i) (graph.supported i))

theorem MemoDerivation.supportInstance_spec {source target : System F}
    {rom : WireROM F} {message : Message F} (graph : MemoDerivation source rom message)
    (refines : source.SupportRefines target) (i : Fin graph.size) :
    (graph.supportInstance refines i).conclusion = (graph.node i).conclusion ∧
      (graph.supportInstance refines i).premises ⊆ (graph.node i).premises :=
  Classical.choose_spec (refines rom (graph.node i) (graph.supported i))

private theorem MemoDerivation.supportIndex {source target : System F}
    {rom : WireROM F} {message : Message F} (graph : MemoDerivation source rom message)
    (refines : source.SupportRefines target) (i : Fin graph.size)
    (j : Fin (graph.supportInstance refines i).premises.length) :
    ∃ k : Fin (graph.node i).premises.length,
      (graph.node i).premises[k] = (graph.supportInstance refines i).premises[j] := by
  have member := (graph.supportInstance_spec refines i).2
    (List.getElem_mem (l := (graph.supportInstance refines i).premises) (n := j.val) j.isLt)
  obtain ⟨k, bounded, same⟩ := List.mem_iff_getElem.mp member
  exact ⟨⟨k, bounded⟩, same⟩

/-- Every new edge uses an old edge. This construction applies to shared and
cyclic graphs, and preserves acyclicity when the original graph is acyclic. -/
noncomputable def MemoDerivation.mapSupport {source target : System F}
    {rom : WireROM F} {message : Message F} (graph : MemoDerivation source rom message)
    (refines : source.SupportRefines target) : MemoDerivation target rom message where
  size := graph.size
  node := graph.supportInstance refines
  root := graph.root
  root_claim := (graph.supportInstance_spec refines graph.root).1.trans graph.root_claim
  target i j := graph.target i (Classical.choose (graph.supportIndex refines i j))
  target_claim i j :=
    ((graph.supportInstance_spec refines _).1.trans (graph.target_claim i _)).trans
      (Classical.choose_spec (graph.supportIndex refines i j))

theorem MemoDerivation.mapSupport_dependency {source target : System F}
    {rom : WireROM F} {message : Message F} (graph : MemoDerivation source rom message)
    (refines : source.SupportRefines target) {child parent : Fin graph.size}
    (edge : (graph.mapSupport refines).Dependency child parent) : graph.Dependency child parent := by
  obtain ⟨j, same⟩ := edge
  exact ⟨Classical.choose (graph.supportIndex refines parent j), same⟩

theorem MemoDerivation.mapSupport_acyclic {source target : System F}
    {rom : WireROM F} {message : Message F} (graph : MemoDerivation source rom message)
    (refines : source.SupportRefines target) (acyclic : graph.Acyclic) :
    (graph.mapSupport refines).Acyclic := by
  intro i cycle
  exact acyclic i (Relation.TransGen.mono (fun _ _ edge => graph.mapSupport_dependency refines edge) i i cycle)

theorem System.SupportRefines.memoDerives {source target : System F}
    (refines : source.SupportRefines target) {rom : WireROM F} {message : Message F}
    (derived : MemoDerives source rom message) : MemoDerives target rom message := by
  obtain ⟨graph⟩ := derived
  exact ⟨graph.mapSupport refines⟩

theorem System.SupportEquiv.derives_iff {source target : System F}
    (same : source.SupportEquiv target) {rom : WireROM F} {message : Message F} :
    Derives source rom message ↔ Derives target rom message :=
  ⟨same.1.derives, same.2.derives⟩

theorem System.SupportEquiv.memoDerives_iff {source target : System F}
    (same : source.SupportEquiv target) {rom : WireROM F} {message : Message F} :
    MemoDerives source rom message ↔ MemoDerives target rom message :=
  ⟨same.1.memoDerives, same.2.memoDerives⟩

theorem System.SupportEquiv.acyclic_iff {source target : System F}
    (same : source.SupportEquiv target) {rom : WireROM F} {message : Message F} :
    (∃ graph : MemoDerivation source rom message, graph.Acyclic) ↔
      (∃ graph : MemoDerivation target rom message, graph.Acyclic) := by
  constructor
  · rintro ⟨graph, acyclic⟩
    exact ⟨graph.mapSupport same.1, graph.mapSupport_acyclic same.1 acyclic⟩
  · rintro ⟨graph, acyclic⟩
    exact ⟨graph.mapSupport same.2, graph.mapSupport_acyclic same.2 acyclic⟩

theorem System.SupportEquiv.check_iff {source target : System F}
    (same : source.SupportEquiv target) {rom : WireROM F} {root : Message F}
    (sourceContext : source.checkContext rom root = .ok ())
    (targetContext : target.checkContext rom root = .ok ()) :
    (∃ rows, source.check rom root rows = .ok ()) ↔
      (∃ rows, target.check rom root rows = .ok ()) := by
  rw [source.check_derives_iff sourceContext, target.check_derives_iff targetContext]
  exact same.derives_iff

theorem System.SupportEquiv.checkMemo_iff {source target : System F}
    (same : source.SupportEquiv target) {rom : WireROM F} {root : Message F}
    (sourceContext : source.checkContext rom root = .ok ())
    (targetContext : target.checkContext rom root = .ok ()) :
    (∃ rows, source.checkMemo rom root rows = .ok ()) ↔
      (∃ rows, target.checkMemo rom root rows = .ok ()) := by
  rw [source.checkMemo_derives_iff sourceContext, target.checkMemo_derives_iff targetContext]
  exact same.memoDerives_iff

end Aiur.Circuit
