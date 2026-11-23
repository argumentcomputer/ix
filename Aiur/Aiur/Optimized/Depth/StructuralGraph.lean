import Aiur.Optimized.Depth.Soundness
import Aiur.Optimized.Depth.Structural

/-!
# Memo graphs over a depth system with exempt SCCs

Under `Structural.certify` an edge of a memo graph over the depth system lowers the SCC rank,
or keeps it between two circuits that both carry a depth word, lowering it by a small step, or
keeps it between two circuits of one exempt SCC (`graph_step`). The first two are
`Depth.local_step`; the third is new, and says nothing about the rows: that is left to the
source half of the certificate.

`erase_graph` drops the depth words of a whole memo graph, where `Depth.derives_erase` drops
those of a finite derivation. The erased graph is a memo graph over the source system. It may
be cyclic, so it is returned with the map `origin` back to the depth graph, along which its
edges are edges of the depth graph.
-/

namespace Aiur.Optimized.Depth.Structural

open Circuit

variable {F : Type} [Field F] [DecidableEq F] {cfg : Config} {source : System F} {rom : WireROM F}

/-! ## Certificate facts -/

/-- The source system without its chips. Fixed claims do not read the chips, so the lemmas of
`Depth.Soundness` about them apply to it under `Structural.certify`. -/
def chipless (source : System F) : System F := { source with chips := [] }

/-- Everything the graph lemmas read from `Structural.certify`. -/
structure Facts (cfg : Config) (source : System F) : Prop where
  tables : Depth.Facts cfg (chipless source)
  chipName : ∀ chip ∈ source.chips, chip.name ∉ cfg.names
  sendName : ∀ chip ∈ source.chips, ∀ send ∈ chip.sends, send.channel ∉ cfg.names
  formed : ∀ chip ∈ source.chips, chip.wellFormed = true
  length : ∀ chip ∈ source.chips, (cfg.plan chip.name).slots.length = chip.sends.length
  slot : ∀ chip ∈ source.chips, ∀ pair ∈ chip.sends.zip (cfg.plan chip.name).slots,
    slotOK cfg source chip.name pair.1 pair.2 = true
  exempt : ∀ name ∈ cfg.structural, cfg.recursive name = false

omit [Field F] [DecidableEq F] in
theorem certify_facts(certified : certify cfg source = true) : Facts cfg source := by
  simp only [certify, fresh, chipOK, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at certified
  obtain ⟨⟨⟨⟨⟨nodup, chips⟩, maps⟩, tables⟩, each⟩, exempt⟩ := certified
  exact {
    tables := {
      nodup
      chipName := fun chip member => by cases member
      sendName := fun chip member => by cases member
      mapName := fun map member => (maps map member).1.1.1
      mapInput := fun map member => (maps map member).1.1.2
      mapOutput := fun map member => (maps map member).1.2
      mapPlain := fun map member => (maps map member).2
      tableName := tables
      formed := fun chip member => by cases member
      length := fun chip member => by cases member
      slot := fun chip member => by cases member }
    chipName := fun chip member => (chips chip member).1
    sendName := fun chip member => (chips chip member).2
    formed := fun chip member => (each chip member).1.1
    length := fun chip member => (each chip member).1.2
    slot := fun chip member => (each chip member).2
    exempt := fun name member => by simpa using exempt name member }

/-- The kind of a certified slot matches its callee; equal rank needs a depth word on both
sides, or both circuits in an exempt SCC. -/
theorem slot_spec {caller : String} {send : Send F} {kind : SlotKind}
    (ok : slotOK cfg source caller send kind = true) :
    (kind = .plain ↔ cfg.recursive send.channel = false) ∧
    ∀ callee, source.findChip? send.channel = some callee →
      ((kind = .plain ∨ kind = .external) ∧ cfg.rank send.channel < cfg.rank caller) ∨
      ((kind = .exact ∨ kind = .gap) ∧ cfg.recursive caller = true ∧
        cfg.recursive send.channel = true ∧ cfg.rank send.channel = cfg.rank caller) ∨
      (kind = .plain ∧ cfg.rank send.channel = cfg.rank caller ∧
        cfg.structural.contains caller = true ∧ cfg.structural.contains send.channel = true) := by
  unfold slotOK at ok
  rcases Bool.or_eq_true_iff.mp ok with ok | ok
  · have spec := Depth.slot_spec ok
    refine ⟨spec.1, fun callee found => ?_⟩
    rcases spec.2 callee found with lower | ⟨intra, recursive, equal⟩
    · exact Or.inl lower
    · refine Or.inr (Or.inl ⟨intra, recursive, ?_, equal⟩)
      cases plain : cfg.recursive send.channel
      · rcases intra with rfl | rfl <;> exact absurd (spec.1.mpr plain) (by simp)
      · rfl
  · simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at ok
    obtain ⟨⟨⟨⟨⟨isPlain, _⟩, plain⟩, rank⟩, exemptCaller⟩, exemptCallee⟩ := ok
    have kindPlain : kind = .plain := by
      cases kind <;> first | rfl | exact absurd isPlain (by decide)
    subst kindPlain
    exact ⟨by simp [plain], fun _ _ => Or.inr (Or.inr ⟨rfl, rank, exemptCaller, exemptCallee⟩)⟩

omit [Field F] [DecidableEq F] in
theorem findChip_none(facts : Facts cfg source) {name : String} (named : name ∈ cfg.names) :
    source.findChip? name = none := by
  apply List.find?_eq_none.mpr
  intro chip member same
  exact facts.chipName chip member (by rw [beq_iff_eq.mp same]; exact named)

/-- Fixed claims outside the added names are the source's fixed claims. -/
theorem mapClaim_source (facts : Facts cfg source) {message : Message F}
    (claim : (system cfg source).MapClaim message) (outside : message.channel ∉ cfg.names) :
    source.MapClaim message :=
  Depth.mapClaim_source (source := chipless source) facts.tables claim outside

/-- The channel of a row's conclusion is the name of its source chip. -/
theorem receive_channel (limbs : List Nat) (plan : ChipPlan) (chip : Chip F) (row : Row F) :
    ((compileChip limbs plan chip).receive row).channel = chip.name := by
  rw [compileChip_receive]
  split <;> rfl

/-! ## Edges -/

/-- `Depth.local_step` under `Structural.certify`: a reference may also keep the rank between
two circuits of an exempt SCC. -/
theorem local_step (facts : Facts cfg source) (parent child : RuleInstance (system cfg source) rom)
    (premise : Message F) (member : premise ∈ parent.premises) (claim : child.conclusion = premise)
    (static : ∀ q ∈ parent.premises, source.findChip? q.channel = none →
      (system cfg source).MapClaim q) :
    nodeRank cfg child < nodeRank cfg parent ∨ nodeRank cfg child = nodeRank cfg parent ∧
      ((cfg.recursive parent.conclusion.channel = true ∧
          cfg.recursive child.conclusion.channel = true ∧
          ∃ s : Nat, 0 < s ∧ s ≤ 2 ^ cfg.bits ∧
            depthWord child.conclusion + (s : F) = depthWord parent.conclusion) ∨
        (cfg.structural.contains parent.conclusion.channel = true ∧
          cfg.structural.contains child.conclusion.channel = true)) := by
  cases parent with
  | table _ _ => simp [RuleInstance.premises] at member
  | node compiled row lookup valid =>
    obtain ⟨chip, found, rfl⟩ := found_compiled lookup
    have chipMember := List.mem_of_find?_eq_some found
    simp only [RuleInstance.premises] at member static
    have whole := member
    rw [compileChip_premises, List.mem_append] at member
    cases child with
    | table _ _ => left; simp [nodeRank]
    | node compiledCallee rowCallee lookupCallee _ =>
      obtain ⟨callee, foundCallee, rfl⟩ := found_compiled lookupCallee
      have calleeName := System.findChip_name foundCallee
      have channel : premise.channel = rowCallee.chip := by
        rw [← claim]
        exact calleeName
      rcases member with member | member
      · obtain ⟨send, kind, position, pair, on, same, checks⟩ :=
          mainSends_mem _ _ _ _ _ premise member
        have sendChannel : send.channel = rowCallee.chip := by
          rw [← channel, same, extend_channel]
        have spec := slot_spec (facts.slot chip chipMember (send, kind) pair)
        dsimp only at spec
        have equalRank : cfg.rank send.channel = cfg.rank chip.name →
            nodeRank cfg (.node (compileChip cfg.limbs (cfg.plan callee.name) callee) rowCallee
              lookupCallee ‹_› : RuleInstance (system cfg source) rom) =
            nodeRank cfg (.node (compileChip cfg.limbs (cfg.plan chip.name) chip) row
              lookup valid : RuleInstance (system cfg source) rom) := by
          intro equal
          simp only [nodeRank, compileChip]
          rw [calleeName, ← sendChannel, equal]
        rcases spec.2 callee (by rw [sendChannel]; exact foundCallee) with
          ⟨_, lower⟩ | ⟨intra, recursive, recursiveCallee, equal⟩ | ⟨_, equal, exempt, exemptCallee⟩
        · left
          simp only [nodeRank, compileChip]
          rw [calleeName, ← sendChannel]
          omega
        · right
          refine ⟨equalRank equal, Or.inl ⟨?_, ?_, ?_⟩⟩
          · simp only [RuleInstance.conclusion, receive_channel]
            exact recursive
          · simp only [RuleInstance.conclusion, receive_channel]
            rw [calleeName, ← sendChannel]
            exact recursiveCallee
          rw [claim, same]
          simp only [RuleInstance.conclusion]
          rw [compileChip_depthWord _ _ _ _ recursive]
          rcases intra with rfl | rfl
          · refine ⟨1, Nat.one_pos, Nat.one_le_two_pow, ?_⟩
            simp only [extra, depthWord_extend, Scalar.Circuit.ArithExpr.denote]
            push_cast
            ring
          · have ranged : ∀ check ∈ (limbChecks cfg.limbs position send.enable).filterMap
                (enabled row.assignment), (system cfg source).MapClaim check := by
              intro check present
              have inside := checks rfl check present
              obtain ⟨width, widthIn, named⟩ := rangeSends_channel _ _ _ _ check inside
              apply static check
                (by rw [compileChip_premises]; exact List.mem_append_right _ inside)
              rw [named]
              exact findChip_none facts (mem_names widthIn (by simp [rangeNames]))
            obtain ⟨gap, bound, value⟩ := gap_value row.assignment (system cfg source).MapClaim
              cfg.limbs (fun width inside x claim =>
                rangeClaim (source := chipless source) facts.tables inside claim)
              position send.enable on ranged
            refine ⟨1 + gap, by omega, ?_, ?_⟩
            · have : gap + 1 ≤ 2 ^ cfg.limbs.sum := bound
              simp only [Config.bits]
              omega
            · simp only [extra, depthWord_extend, Scalar.Circuit.ArithExpr.denote]
              change row.assignment chip.numVars - 1 - (gapExpr cfg.limbs position).denote row.assignment +
                ((1 + gap : Nat) : F) = row.assignment chip.numVars
              rw [value]
              push_cast
              ring
        · right
          refine ⟨equalRank equal, Or.inr ⟨?_, ?_⟩⟩
          · simp only [RuleInstance.conclusion, receive_channel]
            exact exempt
          · simp only [RuleInstance.conclusion, receive_channel]
            rw [calleeName, ← sendChannel]
            exact exemptCallee
      · exfalso
        obtain ⟨width, widthIn, named⟩ := rangeSends_channel _ _ _ _ premise member
        have calleeMember := List.mem_of_find?_eq_some foundCallee
        apply facts.chipName callee calleeMember
        rw [calleeName, ← channel, named]
        exact mem_names widthIn (by simp [rangeNames])

/-- How an edge of a memo graph over the depth system moves, under `Structural.certify`. -/
theorem graph_step (certified : certify cfg source = true) {root : Message F}
    (graph : MemoDerivation (system cfg source) rom root) (i : Fin graph.size)
    (k : Fin (graph.node i).premises.length) :
    nodeRank cfg (graph.node (graph.target i k)) < nodeRank cfg (graph.node i) ∨
      nodeRank cfg (graph.node (graph.target i k)) = nodeRank cfg (graph.node i) ∧
        ((cfg.recursive (graph.node i).conclusion.channel = true ∧
            cfg.recursive (graph.node (graph.target i k)).conclusion.channel = true ∧
            ∃ s : Nat, 0 < s ∧ s ≤ 2 ^ cfg.bits ∧
              depthWord (graph.node (graph.target i k)).conclusion + (s : F) =
                depthWord (graph.node i).conclusion) ∨
          (cfg.structural.contains (graph.node i).conclusion.channel = true ∧
            cfg.structural.contains (graph.node (graph.target i k)).conclusion.channel = true)) := by
  have facts := certify_facts certified
  apply local_step facts (graph.node i) (graph.node (graph.target i k)) _
    (List.getElem_mem k.isLt) (graph.target_claim i k)
  intro q present absent
  obtain ⟨t, claim⟩ := graph.premise_mem i present
  generalize graph.node t = node at claim
  cases node with
  | table _ member =>
      simp only [RuleInstance.conclusion] at claim
      subst claim
      exact member
  | node compiled rowT lookupT _ =>
      exfalso
      obtain ⟨chip, found, rfl⟩ := found_compiled lookupT
      have chipName := System.findChip_name found
      have named : q.channel = rowT.chip := by rw [← claim]; exact chipName
      rw [named, found] at absent
      cases absent

/-! ## Erasure -/

/-- Entries of a mapped prefix are the images of the entries of the whole list. -/
theorem getElem_prefix {α β : Type} {f : α → β} {good : α → Prop} {whole main rest : List α}
    {mapped : List β} (split : whole = main ++ rest) (same : mapped = main.map f)
    (all : ∀ entry ∈ main, good entry) (j : Nat) (bound : j < mapped.length) :
    ∃ inside : j < whole.length, mapped[j] = f whole[j] ∧ good whole[j] := by
  subst split same
  have short : j < main.length := by simpa using bound
  refine ⟨by rw [List.length_append]; omega, ?_, ?_⟩
  · rw [List.getElem_map, List.getElem_append_left short]
  · rw [List.getElem_append_left short]
    exact all _ (List.getElem_mem _)

/-- One rule of the depth system outside the added names erases to a rule of the source
system. Its premises are the erased main sends, a prefix of the depth rule's premises. -/
theorem erase_rule (facts : Facts cfg source) (rule : RuleInstance (system cfg source) rom)
    (outside : rule.conclusion.channel ∉ cfg.names) :
    ∃ erased : RuleInstance source rom, erased.isNode = rule.isNode ∧
      erased.conclusion = erase cfg rule.conclusion ∧
      ∀ (j : Nat) (bound : j < erased.premises.length), ∃ inside : j < rule.premises.length,
        erased.premises[j] = erase cfg rule.premises[j] ∧ rule.premises[j].channel ∉ cfg.names := by
  cases rule with
  | table message member =>
      have claim := mapClaim_source facts member outside
      obtain ⟨map, mapMember, _, _, encoded⟩ := (mapClaim_iff _ _).mp claim
      have channel := (encodeMapEntry_some encoded).1
      refine ⟨.table message claim, rfl, ?_, ?_⟩
      · change message = erase cfg message
        exact (erase_plain cfg _ (by rw [channel]; exact facts.tables.mapPlain map mapMember)).symm
      · intro j bound
        exact absurd bound (Nat.not_lt_zero _)
  | node compiled row lookup valid =>
      obtain ⟨chip, found, rfl⟩ := found_compiled lookup
      have member := List.mem_of_find?_eq_some found
      have formed := facts.formed chip member
      have name := System.findChip_name found
      have validAssignment : chip.ValidAssignment rom row.assignment := ⟨valid.2.2.1, valid.2.2.2⟩
      have finite := chip.finiteAssignment formed row.assignment rom
      have valid₀ : chip.ValidRow rom (Row.ofAssignment chip.name chip.numVars row.assignment) :=
        ⟨formed, Row.ofAssignment_length _ _ _, finite.1.mp validAssignment⟩
      have lookup₀ : source.findChip? (Row.ofAssignment chip.name chip.numVars row.assignment).chip =
          some chip := by
        simpa [Row.ofAssignment, name] using found
      have kinds : ∀ pair ∈ chip.sends.zip (cfg.plan chip.name).slots,
          (pair.2 = .plain ↔ cfg.recursive pair.1.channel = false) :=
        fun pair present => (slot_spec (facts.slot chip member pair present)).1
      have premises : chip.premises (Row.ofAssignment chip.name chip.numVars row.assignment) =
          ((mainSends cfg.limbs (.var chip.numVars) ((cfg.plan chip.name).base chip)
            (chip.sends.zip (cfg.plan chip.name).slots)).filterMap (enabled row.assignment)).map
            (erase cfg) := by
        rw [← finite.2.2, requirements_eq, mainSends_erase cfg _ row.assignment _ _ kinds,
          List.map_fst_zip (facts.length chip member).symm.le]
      refine ⟨.node chip _ lookup₀ valid₀, rfl, ?_, ?_⟩
      · change chip.receive (Row.ofAssignment chip.name chip.numVars row.assignment) =
          erase cfg ((compileChip cfg.limbs (cfg.plan chip.name) chip).receive row)
        rw [compileChip_erase]
        exact finite.2.1.symm
      · simp only [RuleInstance.premises]
        apply getElem_prefix (good := fun entry => entry.channel ∉ cfg.names)
          (compileChip_premises _ _ _ _) premises
        intro p pMember
        obtain ⟨send, kind, position, pair, _, rfl, _⟩ := mainSends_mem _ _ _ _ _ p pMember
        rw [extend_channel]
        exact facts.sendName chip member send (List.of_mem_zip pair).1

/-- The depth words of a memo graph erase: a memo graph over the source system for the erased
root, with no more rows, whose nodes and edges come from nodes and edges of the depth graph.
`origin` of a row is a row of the depth graph with the erased conclusion. -/
theorem erase_graph (certified : certify cfg source = true) {root : Message F}
    (graph : MemoDerivation (system cfg source) rom root) (outside : root.channel ∉ cfg.names) :
    ∃ (erased : MemoDerivation source rom (erase cfg root)) (origin : Fin erased.size → Fin graph.size),
      erased.rows.card ≤ graph.rows.card ∧
      (∀ i, (erased.node i).isNode = true → (graph.node (origin i)).isNode = true ∧
        (erased.node i).conclusion = erase cfg (graph.node (origin i)).conclusion ∧
        (graph.node (origin i)).conclusion.channel ∉ cfg.names) ∧
      (∀ i j, (erased.node (erased.target i j)).isNode = true →
        ∃ k, origin (erased.target i j) = graph.target (origin i) k) := by
  classical
  have facts := certify_facts certified
  let I := {i : Fin graph.size // (graph.node i).conclusion.channel ∉ cfg.names}
  have rule (i : I) := erase_rule facts (graph.node i.1) i.2
  let node (i : I) : RuleInstance source rom := Classical.choose (rule i)
  have spec (i : I) : (node i).isNode = (graph.node i.1).isNode ∧
      (node i).conclusion = erase cfg (graph.node i.1).conclusion ∧
      ∀ (j : Nat) (bound : j < (node i).premises.length),
        ∃ inside : j < (graph.node i.1).premises.length,
          (node i).premises[j] = erase cfg (graph.node i.1).premises[j] ∧
            (graph.node i.1).premises[j].channel ∉ cfg.names :=
    Classical.choose_spec (rule i)
  let position (i : I) (j : Fin (node i).premises.length) : Fin (graph.node i.1).premises.length :=
    ⟨j.val, ((spec i).2.2 j.val j.isLt).choose⟩
  have premise (i : I) (j : Fin (node i).premises.length) :
      (node i).premises[j] = erase cfg (graph.node i.1).premises[position i j] ∧
        (graph.node i.1).premises[position i j].channel ∉ cfg.names :=
    ((spec i).2.2 j.val j.isLt).choose_spec
  let target (i : I) (j : Fin (node i).premises.length) : I :=
    ⟨graph.target i.1 (position i j), by rw [graph.target_claim]; exact (premise i j).2⟩
  let root : I := ⟨graph.root, by rw [graph.root_claim]; exact outside⟩
  let erased := MemoDerivation.ofFinite node root
    ((spec root).2.1.trans (congrArg (erase cfg) graph.root_claim)) target
    (fun i j => ((spec (target i j)).2.1.trans
      (congrArg (erase cfg) (graph.target_claim i.1 (position i j)))).trans (premise i j).1.symm)
  let origin : Fin erased.size → Fin graph.size := fun i => ((Fintype.equivFin I).symm i).1
  refine ⟨erased, origin, ?_, ?_, ?_⟩
  · apply Finset.card_le_card_of_injOn origin
    · intro i member
      have isNode := (Finset.mem_filter.mp (Finset.mem_coe.mp member)).2
      apply Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
      rw [← (spec ((Fintype.equivFin I).symm i)).1]
      exact isNode
    · intro a _ b _ same
      exact (Fintype.equivFin I).symm.injective (Subtype.ext same)
  · intro i isNode
    refine ⟨?_, (spec ((Fintype.equivFin I).symm i)).2.1, ((Fintype.equivFin I).symm i).2⟩
    rw [← (spec ((Fintype.equivFin I).symm i)).1]
    exact isNode
  · intro i j _
    refine ⟨position ((Fintype.equivFin I).symm i) j, ?_⟩
    simp [erased, origin, MemoDerivation.ofFinite, target]

end Aiur.Optimized.Depth.Structural
