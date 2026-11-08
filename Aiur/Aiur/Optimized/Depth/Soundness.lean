import Aiur.Optimized.Depth.Rule
import Aiur.Circuit.MemoRows
import Aiur.Circuit.CheckerSoundness
import Aiur.Optimized.DedupCertificate
import Mathlib.Data.ZMod.Basic

/-!
# Soundness of the depth pass

* `Depth.acyclic`: every memo graph over a certified depth system with at most
  `N` row nodes is acyclic, when no positive integer up to `N · 2^k` vanishes in
  the field. No ordering or termination fact about the source is used.
* `Depth.derives_erase`: a finite derivation in the depth system erases to a
  finite derivation in the source system.
* `Depth.checkMemo_sound`: the Lean memo checker's acceptance over the depth
  system, plus the row bound, gives a finite derivation of the erased root in
  the source system. The acyclicity hypothesis of `checkerMemo_acyclic_heap_sound`
  is discharged.
-/

namespace Aiur.Optimized.Depth

open Circuit

variable {F : Type} [Field F] [DecidableEq F] {cfg : Config} {source : System F} {rom : WireROM F}

/-! ## Chips and names -/

theorem findChip_system (cfg : Config) (source : System F) (name : String) :
    (system cfg source).findChip? name =
      (source.findChip? name).map fun chip => compileChip cfg.limbs (cfg.plan chip.name) chip := by
  simp only [System.findChip?, system, List.find?_map]
  rfl

theorem found_compiled {name : String} {compiled : Chip F}
    (lookup : (system cfg source).findChip? name = some compiled) :
    ∃ chip, source.findChip? name = some chip ∧
      compiled = compileChip cfg.limbs (cfg.plan chip.name) chip := by
  rw [findChip_system] at lookup
  obtain ⟨chip, found, rfl⟩ := Option.map_eq_some_iff.mp lookup
  exact ⟨chip, found, rfl⟩

theorem mem_names {width : Nat} (inside : width ∈ cfg.limbs) {name : String}
    (named : name ∈ rangeNames width) : name ∈ cfg.names :=
  List.mem_flatMap.mpr ⟨width, List.mem_dedup.mpr inside, named⟩

/-- Distinct widths have disjoint names. -/
theorem names_inj (nodup : cfg.names.Nodup) {first second : Nat}
    (firstIn : first ∈ cfg.limbs.dedup) (secondIn : second ∈ cfg.limbs.dedup) {name : String}
    (firstNamed : name ∈ rangeNames first) (secondNamed : name ∈ rangeNames second) :
    first = second := by
  by_contra different
  have key : ∀ {widths : List Nat},
      widths.Pairwise (fun a b => List.Disjoint (rangeNames a) (rangeNames b)) →
      ∀ {x y : Nat}, x ∈ widths → y ∈ widths → x ≠ y → List.Disjoint (rangeNames x) (rangeNames y) := by
    intro widths pairwise
    induction pairwise with
    | nil => intro x y member; cases member
    | @cons head rest heads _ ih =>
        intro x y xIn yIn ne
        rcases List.mem_cons.mp xIn with rfl | xRest <;> rcases List.mem_cons.mp yIn with rfl | yRest
        · exact absurd rfl ne
        · exact heads y yRest
        · exact (heads x xRest).symm
        · exact ih xRest yRest ne
  exact key (List.nodup_flatMap.mp nodup).2 firstIn secondIn different firstNamed secondNamed

theorem names_own (nodup : cfg.names.Nodup) {width : Nat} (inside : width ∈ cfg.limbs.dedup) :
    (rangeNames width).Nodup :=
  (List.nodup_flatMap.mp nodup).1 width inside

theorem findChip_none (facts : Facts cfg source) {name : String} (named : name ∈ cfg.names) :
    source.findChip? name = none := by
  apply List.find?_eq_none.mpr
  intro chip member same
  exact facts.chipName chip member (by rw [beq_iff_eq.mp same]; exact named)

/-! ## Fixed maps -/

theorem mapClaim_iff (system : System F) (message : Message F) :
    system.MapClaim message ↔ ∃ map ∈ system.maps,
      ∃ entry ∈ ({ functions := [], enums := system.enums, tables := system.tables, maps := system.maps } :
        Program F).mapEntries map,
        encodeMapEntry system.enums map.name entry = some message := by
  simp only [System.MapClaim, System.mapClaims, List.mem_flatMap, List.mem_filterMap]

theorem encodeMapEntry_some {decls : Declarations} {name : String} {entry : MapEntry F}
    {message : Message F} (encoded : encodeMapEntry decls name entry = some message) :
    message.channel = name ∧
      entry.args.mapM (fun arg => arg.toValue.encode decls) = some message.args := by
  unfold encodeMapEntry at encoded
  obtain ⟨wires, arguments, rest⟩ := Option.bind_eq_some_iff.mp encoded
  obtain ⟨output, _, finished⟩ := Option.bind_eq_some_iff.mp rest
  cases finished
  exact ⟨rfl, arguments⟩

theorem encode_field (decls : Declarations) (n : F) :
    (Constant.toValue (.field n : Constant F)).encode decls = some ⟨.field, [n]⟩ := by
  simp [show (Constant.toValue : Constant F → Value F F) = Value.mapAddress Empty.elim from rfl,
    Value.mapAddress, Value.encode, Value.wellFormed, Value.type, Declarations.layout_field,
    Except.toOption, Layout.encode]

/-- Outside the added names, the depth system reads the source tables. -/
theorem findTable_system (facts : Facts cfg source) {name : String} (outside : name ∉ cfg.names)
    (enums : Declarations) (maps maps' : List MapDecl) :
    ({ functions := [], enums, tables := source.tables ++ cfg.limbs.dedup.flatMap rangeTables,
        maps } : Program F).findTable? name =
      ({ functions := [], enums, tables := source.tables, maps := maps' } : Program F).findTable? name := by
  simp only [Program.findTable?, List.find?_append]
  have absent : (cfg.limbs.dedup.flatMap rangeTables : List (Table F)).find? (·.name == name) = none := by
    apply List.find?_eq_none.mpr
    intro table member same
    obtain ⟨width, inside, member⟩ := List.mem_flatMap.mp member
    apply outside
    rw [← beq_iff_eq.mp same]
    apply List.mem_flatMap.mpr ⟨width, inside, ?_⟩
    simp only [rangeTables, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp [rangeInputTable, rangeUnitTable, rangeNames]
  rw [absent, Option.or_none]

theorem mapEntries_system (facts : Facts cfg source) {map : MapDecl} (member : map ∈ source.maps)
    (maps maps' : List MapDecl) :
    ({ functions := [], enums := source.enums,
        tables := source.tables ++ cfg.limbs.dedup.flatMap rangeTables, maps } : Program F).mapEntries map =
      ({ functions := [], enums := source.enums, tables := source.tables, maps := maps' } : Program F).mapEntries map := by
  simp only [Program.mapEntries, Program.mapRows,
    findTable_system facts (facts.mapInput map member) _ maps maps',
    findTable_system facts (facts.mapOutput map member) _ maps maps']

/-- Fixed claims outside the added names are the source's fixed claims. -/
theorem mapClaim_source (facts : Facts cfg source) {message : Message F}
    (claim : (system cfg source).MapClaim message) (outside : message.channel ∉ cfg.names) :
    source.MapClaim message := by
  rw [mapClaim_iff] at claim ⊢
  obtain ⟨map, member, entry, entryMember, encoded⟩ := claim
  have channel := (encodeMapEntry_some encoded).1
  simp only [system, List.mem_append] at member
  rcases member with member | member
  · refine ⟨map, member, entry, ?_, encoded⟩
    simpa only [system, mapEntries_system facts member _ source.maps] using entryMember
  · obtain ⟨width, inside, rfl⟩ := List.mem_map.mp member
    exact absurd (by rw [channel]; exact mem_names (List.mem_dedup.mp inside) (by simp [rangeDecl, rangeNames]))
      outside

theorem source_mapClaim (facts : Facts cfg source) {message : Message F}
    (claim : source.MapClaim message) : (system cfg source).MapClaim message := by
  rw [mapClaim_iff] at claim ⊢
  obtain ⟨map, member, entry, entryMember, encoded⟩ := claim
  refine ⟨map, List.mem_append_left _ member, entry, ?_, encoded⟩
  simpa only [system, mapEntries_system facts member _ source.maps] using entryMember

/-- A range claim bounds its argument. -/
theorem rangeClaim (facts : Facts cfg source) {width : Nat} {x : F} (inside : width ∈ cfg.limbs)
    (claim : (system cfg source).MapClaim (rangeMessage width x)) :
    ∃ n : Nat, n < 2 ^ width ∧ x = (n : F) := by
  have dedupIn := List.mem_dedup.mpr inside
  rw [mapClaim_iff] at claim
  obtain ⟨map, member, entry, entryMember, encoded⟩ := claim
  obtain ⟨channel, arguments⟩ := encodeMapEntry_some encoded
  simp only [system, List.mem_append] at member
  rcases member with member | member
  · exact absurd (by rw [← channel]; exact mem_names inside (by simp [rangeMessage, rangeNames]))
      (facts.mapName map member)
  obtain ⟨other, otherIn, rfl⟩ := List.mem_map.mp member
  have same : other = width := names_inj facts.nodup otherIn dedupIn
    (name := rangeName other) (by simp [rangeNames])
    (by rw [show rangeName other = rangeName width from channel.symm]; simp [rangeNames])
  subst same
  rw [mapEntry_mem_iff] at entryMember
  unfold Program.mapRows at entryMember
  split at entryMember
  · rename_i inputs outputs foundInputs _
    have row := (List.of_mem_zip entryMember).1
    have named := List.find?_some foundInputs
    have present := List.mem_of_find?_eq_some foundInputs
    simp only [rangeDecl, beq_iff_eq] at named
    rcases List.mem_append.mp present with present | present
    · exact absurd (by rw [named]; exact mem_names inside (by simp [rangeNames]))
        (facts.tableName inputs present)
    obtain ⟨owner, ownerIn, present⟩ := List.mem_flatMap.mp present
    simp only [rangeTables, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · simp only [rangeInputTable] at named row
      have : owner = other := names_inj facts.nodup ownerIn dedupIn (name := rangeInputs owner)
        (by simp [rangeNames]) (by rw [named]; simp [rangeNames])
      subst this
      obtain ⟨n, bound, shape⟩ : ∃ n : Nat, n ∈ List.range (2 ^ owner) ∧
          (Value.tuple [Value.field (n : F)] : Constant F) = Value.tuple entry.args :=
        List.mem_map.mp row
      simp only [Value.tuple.injEq] at shape
      rw [← shape] at arguments
      simp [encode_field, rangeMessage] at arguments
      exact ⟨n, List.mem_range.mp bound, by first | exact arguments.symm | exact arguments⟩
    · simp only [rangeUnitTable] at named
      have : owner = other := names_inj facts.nodup ownerIn dedupIn (name := rangeUnits owner)
        (by simp [rangeNames]) (by rw [named]; simp [rangeNames])
      subst this
      have own := names_own facts.nodup ownerIn
      simp [rangeNames, named] at own
  · simp at entryMember

/-! ## Erasure -/

/-- A finite derivation in the depth system erases to one in the source system. -/
theorem derives_erase (facts : Facts cfg source) {message : Message F}
    (derived : Derives (system cfg source) rom message) (outside : message.channel ∉ cfg.names) :
    Derives source rom (erase cfg message) := by
  obtain ⟨tree⟩ := derived
  revert outside
  induction tree using Derivation.rec
    (motive_2 := fun messages _ => ∀ m ∈ messages, m.channel ∉ cfg.names →
      Derives source rom (erase cfg m)) with
  | node compiled row lookup valid _ ih =>
      intro _
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
      have children : ∀ q ∈ chip.premises (Row.ofAssignment chip.name chip.numVars row.assignment),
          Derives source rom q := by
        rw [premises]
        intro q present
        obtain ⟨p, pMember, rfl⟩ := List.mem_map.mp present
        apply ih p (by rw [compileChip_premises]; exact List.mem_append_left _ pMember)
        obtain ⟨send, kind, position, pair, _, rfl, _⟩ := mainSends_mem _ _ _ _ _ p pMember
        rw [extend_channel]
        exact facts.sendName chip member send (List.of_mem_zip pair).1
      obtain ⟨forest⟩ := derivations_nonempty_iff.mpr children
      rw [compileChip_erase]
      have conclusion : chip.receive row =
          chip.receive (Row.ofAssignment chip.name chip.numVars row.assignment) := finite.2.1
      rw [conclusion]
      exact ⟨.node chip _ lookup₀ valid₀ forest⟩
  | table member =>
      intro outside
      have claim := mapClaim_source facts member outside
      obtain ⟨map, mapMember, _, _, encoded⟩ := (mapClaim_iff _ _).mp claim
      have channel := (encodeMapEntry_some encoded).1
      rw [erase_plain cfg _ (by rw [channel]; exact facts.mapPlain map mapMember)]
      exact ⟨.table claim⟩
  | nil =>
      rename_i m member _
      cases member
  | cons _ _ headIH tailIH =>
      rename_i m member outside
      rcases List.mem_cons.mp member with rfl | member
      · exact headIH outside
      · exact tailIH m member outside

/-! ## Acyclicity -/

/-- Rows rank one above their SCC rank; fixed claims rank zero. -/
def nodeRank (cfg : Config) {system : System F} : RuleInstance system rom → Nat
  | .node chip _ _ _ => cfg.rank chip.name + 1
  | .table _ _ => 0

/-- One reference of a memo graph over the depth system lowers the rank, or
keeps it and lowers the depth word by `1 + gap` with `gap < 2 ^ cfg.bits`. -/
theorem local_step (facts : Facts cfg source) (parent child : RuleInstance (system cfg source) rom)
    (premise : Message F) (member : premise ∈ parent.premises) (claim : child.conclusion = premise)
    (static : ∀ q ∈ parent.premises, source.findChip? q.channel = none →
      (system cfg source).MapClaim q) :
    nodeRank cfg child < nodeRank cfg parent ∨ nodeRank cfg child = nodeRank cfg parent ∧
      ∃ s : Nat, 0 < s ∧ s ≤ 2 ^ cfg.bits ∧
        depthWord child.conclusion + (s : F) = depthWord parent.conclusion := by
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
        rcases spec.2 callee (by rw [sendChannel]; exact foundCallee) with
          ⟨_, lower⟩ | ⟨intra, recursive, equal⟩
        · left
          simp only [nodeRank, compileChip]
          rw [calleeName, ← sendChannel]
          omega
        · right
          refine ⟨by simp only [nodeRank, compileChip]; rw [calleeName, ← sendChannel, equal], ?_⟩
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
              cfg.limbs (fun width inside x claim => rangeClaim facts inside claim)
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
      · exfalso
        obtain ⟨width, widthIn, named⟩ := rangeSends_channel _ _ _ _ premise member
        have calleeMember := List.mem_of_find?_eq_some foundCallee
        apply facts.chipName callee calleeMember
        rw [calleeName, ← channel, named]
        exact mem_names widthIn (by simp [rangeNames])

/-- The headline acyclicity theorem (strictness variant (ii)): a memo graph over a
certified depth system with at most `N` rows is acyclic when no positive integer
up to `N · 2 ^ cfg.bits` vanishes in the field. -/
theorem acyclic (facts : Facts cfg source) {root : Message F}
    (graph : MemoDerivation (system cfg source) rom root) {N : Nat} (card : graph.rows.card ≤ N)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ N * 2 ^ cfg.bits → (n : F) ≠ 0) : graph.Acyclic := by
  apply graph.acyclic_of_steps card (fun i => nodeRank cfg (graph.node i))
    (fun i => depthWord (graph.node i).conclusion) ?_ characteristic
  intro i j
  apply local_step facts (graph.node i) (graph.node (graph.target i j)) _
    (List.getElem_mem j.isLt) (graph.target_claim i j)
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

/-! ## The memo checker -/

theorem derives_of_checkMemo (facts : Facts cfg source) {root : Message F}
    {rows : List (WeightedRow F)} {N : Nat} (bound : rows.length ≤ N)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ N * 2 ^ cfg.bits → (n : F) ≠ 0)
    (checked : (system cfg source).checkMemo rom root rows = .ok ()) :
    Derives (system cfg source) rom root := by
  obtain ⟨graph, card⟩ := System.checkMemo_graph checked
  exact graph.derives_of_acyclic (acyclic facts graph (card.trans bound) characteristic)

/-- Memo-checker acceptance over the certified depth system and the row bound
give a finite derivation of the erased root in the source system. -/
theorem checkMemo_sound (certified : Certified cfg source) {root : Message F}
    {rows : List (WeightedRow F)} {N : Nat} (bound : rows.length ≤ N)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ N * 2 ^ cfg.bits → (n : F) ≠ 0)
    (checked : (system cfg source).checkMemo rom root rows = .ok ())
    (outside : root.channel ∉ cfg.names) : Derives source rom (erase cfg root) :=
  derives_erase certified.facts (derives_of_checkMemo certified.facts bound characteristic checked)
    outside

/-! ## Goldilocks -/

/-- The row bound `2 ^ 39` with gap width `24` fits below the Goldilocks characteristic. -/
theorem goldilocks_characteristic (n : Nat) (positive : 0 < n) (small : n ≤ 2 ^ 39 * 2 ^ 24) :
    ((n : ZMod 18446744069414584321)) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff (ZMod 18446744069414584321) 18446744069414584321]
  intro divides
  have := Nat.le_of_dvd positive divides
  norm_num at small
  omega

end Aiur.Optimized.Depth
