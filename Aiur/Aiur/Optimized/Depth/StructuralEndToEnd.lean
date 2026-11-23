import Aiur.Optimized.StructuralModel
import Aiur.Optimized.Depth.StructuralGraph
import Aiur.Optimized.Depth.StructuralMeasure
import Aiur.Circuit.CycleMixed
import Aiur.Optimized.Equivalence
import Aiur.Optimized.Physical
import Aiur.Optimized.Grouping.Memo

/-!
# A finite derivation from a memo graph with exempt SCCs

`Depth.acyclic` shows every memo graph over a certified depth system acyclic. With exempt SCCs
(`Depth.Structural`) that fails: rows of a structurally recursive circuit over a cyclic data
structure may support each other. Such rows are never called by a row whose arguments have
store provenance, and that is enough.

`Prepared.structural_memo_sound`: from a memo graph over the depth pass of the physical
circuits, with both halves of the structural certificate, the entry claim has a finite
derivation in the physical circuits. That is what `Depth.plan_checkMemo_sound` concludes from
the certificate with no exempt SCC.

`Prepared.DepthCertified` is the certificate of the physical circuits of a compiled program,
`Prepared.checkDepthPlan` its executable exporter check, and `Prepared.depth_checkMemo_sound`
the same conclusion from rows accepted by the grouped, activated memo checker; the headline
theorems (`Depth.Grouped`, `Observed`) go through it.

The argument reads each row of the graph at every source claim that translates to it
(`Prepared.rule_view`), and shows by induction that a view whose arguments have store
provenance evaluates, with a result that has store provenance:

* The induction is on the calls between such views that the static analysis allows
  (`Structural.Allowed`); `compile_structural_sound` asks for nothing else.
* Those calls have no cycle. A cycle keeps the SCC rank (`graph_step`). In an SCC with depth
  words the depth word falls by a small step along the underlying rows (`CycleLength.no_cycle`).
  In an exempt SCC the checked measures fall (`Structural.check`, `move_parts`, `move_down`,
  `move_up`): the height of a parameter with store provenance (`exists_height`), or a
  countdown, which a view takes at most once per function sharing its circuit
  (`CycleLength.no_cycle_mixed`).
* The entry's arguments are pointer-free, so they have store provenance; its evaluation gives
  a finite derivation back by completeness (`ProvenanceModel.complete_encoded`), which
  deduplication and type erasure carry to the physical circuits (`Prepared.derives_iff`).
-/

namespace Aiur.Circuit.CycleLength

variable {V : Type}

/-- A relation whose edges all leave a finite set, with no cycle inside that set, is
well-founded from targets to sources. -/
theorem wellFounded_of_no_cycle {edge : V → V → Prop} {rows : Finset V}
    (source : ∀ u v, edge u v → u ∈ rows)
    (acyclic : ∀ u, ¬ Relation.TransGen (fun u v => edge u v ∧ v ∈ rows) u u) :
    WellFounded fun v u => edge u v := by
  let inner : {u // u ∈ rows} → {u // u ∈ rows} → Prop := fun v u => edge u.1 v.1
  have irreflexive : ∀ u, ¬ Relation.TransGen inner u u := by
    intro u cycle
    have swapped : Relation.TransGen (Function.swap inner) u u := Relation.transGen_swap.mpr cycle
    exact acyclic u.1 (swapped.lift Subtype.val fun a b step => ⟨step, b.2⟩)
  have : Std.Irrefl (Relation.TransGen inner) := ⟨irreflexive⟩
  have founded : WellFounded inner :=
    (Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen inner)).mono
      (fun _ _ step => .single step)
  have accessible : ∀ u : {u // u ∈ rows}, Acc (fun v u => edge u v) u.1 := by
    intro u
    induction u using founded.induction with
    | h u ih =>
        refine ⟨_, fun v step => ?_⟩
        by_cases member : v ∈ rows
        · exact ih ⟨v, member⟩ step
        · exact ⟨_, fun w next => absurd (source v w next) member⟩
  refine ⟨fun u => ?_⟩
  by_cases member : u ∈ rows
  · exact accessible ⟨u, member⟩
  · exact ⟨_, fun w next => absurd (source u w next) member⟩

/-- No cycle when every edge lowers the rank, or keeps it between two nodes of one kind, where
the edges of neither kind have a cycle. -/
theorem no_cycle_kinds {edge first second : V → V → Prop} (rank : V → Nat) (kind : V → Prop)
    (step : ∀ u v, edge u v → rank v < rank u ∨ rank v = rank u ∧
      ((kind u ∧ kind v ∧ first u v) ∨ (¬ kind u ∧ ¬ kind v ∧ second u v)))
    (firstAcyclic : ∀ u, ¬ Relation.TransGen first u u)
    (secondAcyclic : ∀ u, ¬ Relation.TransGen (fun u v => edge u v ∧ second u v) u u) (u : V) :
    ¬ Relation.TransGen edge u u := by
  have flat : ∀ v, Relation.TransGen edge u v → rank v ≤ rank u ∧ (rank v = rank u →
      (kind u → kind v ∧ Relation.TransGen first u v) ∧
      (¬ kind u → ¬ kind v ∧ Relation.TransGen (fun u v => edge u v ∧ second u v) u v)) := by
    intro v path
    induction path with
    | single link =>
        rcases step _ _ link with lower | ⟨same, ⟨here, next, moved⟩ | ⟨here, next, moved⟩⟩
        · exact ⟨by omega, fun equal => by omega⟩
        · exact ⟨by omega, fun _ => ⟨fun _ => ⟨next, .single moved⟩, fun other => absurd here other⟩⟩
        · exact ⟨by omega, fun _ =>
            ⟨fun other => absurd other here, fun _ => ⟨next, .single ⟨link, moved⟩⟩⟩⟩
    | tail _ link ih =>
        obtain ⟨below, pure⟩ := ih
        rcases step _ _ link with lower | ⟨same, ⟨here, next, moved⟩ | ⟨here, next, moved⟩⟩
        · exact ⟨by omega, fun equal => by omega⟩
        · refine ⟨by omega, fun equal => ?_⟩
          obtain ⟨counted, plain⟩ := pure (by omega)
          exact ⟨fun start => ⟨next, (counted start).2.tail moved⟩,
            fun start => absurd here (plain start).1⟩
        · refine ⟨by omega, fun equal => ?_⟩
          obtain ⟨counted, plain⟩ := pure (by omega)
          exact ⟨fun start => absurd (counted start).1 here,
            fun start => ⟨next, (plain start).2.tail ⟨link, moved⟩⟩⟩
  intro cycle
  obtain ⟨counted, plain⟩ := (flat u cycle).2 rfl
  by_cases start : kind u
  · exact firstAcyclic u (counted start).2
  · exact secondAcyclic u (plain start).2

end Aiur.Circuit.CycleLength

namespace Aiur.Optimized.Depth.Structural

variable {F : Type} [Field F] [DecidableEq F] {rom : ROM F}

/-- Whether a measure is a data structure, as opposed to a countdown. -/
def Measure.isParts : Measure → Bool
  | .parts _ => true
  | _ => false

/-- The field value of an argument, if it is one. -/
def fieldValue : Option (Value F) → F
  | some (.field x) => x
  | _ => 0

/-- What a countdown measure reads of the arguments: the parameter, negated when it counts up,
so both kinds fall. -/
def Measure.depth (measure : Measure) (args : List (Value F)) : F :=
  match measure with
  | .parts _ => 0
  | .down i => fieldValue args[i]?
  | .up i => -fieldValue args[i]?

/-- What a `parts` measure reads of the arguments: the largest height of its parameters. -/
def Measure.size (height : Value F → Nat) (measure : Measure) (args : List (Value F)) : Nat :=
  match measure with
  | .parts params => params.toFinset.sup fun i => (args[i]?.map height).getD 0
  | _ => 0

/-- A call from `params` to `values` moves the measures of the two functions down: both count,
by a small step or to a lower order, or both are data structures, to a lower height or order. -/
def Moves (height : Value F → Nat) (own callee : FunctionPlan) (params values : List (Value F)) :
    Prop :=
  (own.measure.isParts = false ∧ callee.measure.isParts = false ∧
      ((∃ s : Nat, 0 < s ∧ s ≤ maxStep ∧
          callee.measure.depth values + (s : F) = own.measure.depth params) ∨
        (callee.measure.depth values = own.measure.depth params ∧ callee.order < own.order))) ∨
    (own.measure.isParts = true ∧ callee.measure.isParts = true ∧
      (callee.measure.size height values < own.measure.size height params ∨
        (callee.measure.size height values ≤ own.measure.size height params ∧
          callee.order < own.order)))

/-- A call that descends, with arguments satisfying its static relations to parameters with
store provenance, moves the measures down. -/
theorem descends_moves {height : Value F → Nat}
    (falls : ∀ {part whole : Value F}, rom.Provenance whole → Part rom part whole →
      height part < height whole)
    {plan : Plan} {own : FunctionPlan} {site : Call} {params values : List (Value F)}
    (good : ∀ value ∈ params, rom.Provenance value)
    (sound : List.Forall₂ (Sound rom params) site.args values)
    (descent : descends plan own site = true) :
    ∃ callee, plan.lookup site.callee = some callee ∧ Moves height own callee params values := by
  unfold descends at descent
  cases found : plan.lookup site.callee with
  | none => simp [found] at descent
  | some callee =>
      simp only [found] at descent
      refine ⟨callee, rfl, ?_⟩
      have known : Measure.move site.args own.measure callee.measure ≠ .unknown := by
        intro unknown
        simp [unknown] at descent
      have order : Measure.move site.args own.measure callee.measure = .keeps →
          callee.order < own.order := by
        intro keeps
        simpa [keeps] using descent
      unfold Moves
      rcases move_kind known with ⟨source, target, hs, ht⟩ | ⟨i, j, hs, ht⟩ | ⟨i, j, hs, ht⟩
      · rw [hs, ht] at known order ⊢
        refine .inr ⟨rfl, rfl, ?_⟩
        obtain ⟨lowers, keeps⟩ :=
          move_parts (rom := rom) (params := params) (source := source) (target := target) sound
        have top : ∀ i ∈ source, ∀ param, params[i]? = some param →
            height param ≤ Measure.size height (.parts source) params := by
          intro i inside param atParam
          have high := Finset.le_sup (f := fun i => (params[i]?.map height).getD 0)
            (List.mem_toFinset.mpr inside)
          simp only [atParam, Option.map_some, Option.getD_some] at high
          exact high
        cases moved : Measure.move site.args (.parts source) (.parts target) with
        | unknown => exact absurd moved known
        | lowers =>
            obtain ⟨nonempty, each⟩ := lowers moved
            have bound : ∀ j ∈ target, (values[j]?.map height).getD 0 <
                Measure.size height (.parts source) params := by
              intro j member
              obtain ⟨i, inside, value, param, atValue, atParam, part⟩ := each j member
              have lower := falls (good param (List.mem_of_getElem? atParam)) part
              have high := top i inside param atParam
              simp only [atValue, Option.map_some, Option.getD_some]
              omega
            obtain ⟨j, member⟩ := List.exists_mem_of_ne_nil _ nonempty
            exact .inl ((Finset.sup_lt_iff (lt_of_le_of_lt bot_le (bound j member))).mpr
              fun j member => bound j (List.mem_toFinset.mp member))
        | keeps =>
            obtain ⟨_, each⟩ := keeps moved
            refine .inr ⟨Finset.sup_le fun j member => ?_, order moved⟩
            obtain ⟨i, inside, value, param, atValue, atParam, part⟩ :=
              each j (List.mem_toFinset.mp member)
            have high := top i inside param atParam
            simp only [atValue, Option.map_some, Option.getD_some]
            rcases part with rfl | part
            · exact high
            · have lower := falls (good param (List.mem_of_getElem? atParam)) part
              omega
      · rw [hs, ht] at known order ⊢
        refine .inl ⟨rfl, rfl, ?_⟩
        obtain ⟨lowers, keeps⟩ := move_down (rom := rom) (params := params) (i := i) (j := j) sound
        cases moved : Measure.move site.args (.down i) (.down j) with
        | unknown => exact absurd moved known
        | lowers =>
            obtain ⟨x, n, positive, small, atValue, atParam⟩ := lowers moved
            exact .inl ⟨n, positive, small, by simp [Measure.depth, fieldValue, atValue, atParam]⟩
        | keeps =>
            obtain ⟨value, atValue, atParam⟩ := keeps moved
            exact .inr ⟨by simp [Measure.depth, atValue, atParam], order moved⟩
      · rw [hs, ht] at known order ⊢
        refine .inl ⟨rfl, rfl, ?_⟩
        obtain ⟨lowers, keeps⟩ := move_up (rom := rom) (params := params) (i := i) (j := j) sound
        cases moved : Measure.move site.args (.up i) (.up j) with
        | unknown => exact absurd moved known
        | lowers =>
            obtain ⟨x, n, positive, small, atValue, atParam⟩ := lowers moved
            exact .inl ⟨n, positive, small, by simp [Measure.depth, fieldValue, atValue, atParam]⟩
        | keeps =>
            obtain ⟨value, atValue, atParam⟩ := keeps moved
            exact .inr ⟨by simp [Measure.depth, atValue, atParam], order moved⟩

end Aiur.Optimized.Depth.Structural

namespace Aiur.Optimized.Physical

open Circuit

variable {F : Type} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- A rule with a premise is a row. -/
theorem isNode_of_premise [DecidableEq F] {system : System F} {rom : WireROM F}
    {rule : RuleInstance system rom} (j : Fin rule.premises.length) : rule.isNode = true := by
  cases rule with
  | node => rfl
  | table =>
      have bound := j.isLt
      simp [RuleInstance.premises] at bound

omit [DecidableEq F] in
/-- A row ranks one above the SCC rank of its channel. -/
theorem nodeRank_row (cfg : Depth.Config) {system : System F} {rom : WireROM F}
    {rule : RuleInstance system rom} (row : rule.isNode = true) :
    Depth.nodeRank cfg rule = cfg.rank rule.conclusion.channel + 1 := by
  cases rule with
  | node => rfl
  | table => cases row

/-- A rule of the compiled circuits on a channel that is no function is a fixed-table claim. -/
theorem premises_of_no_function {program : Program F} {entries : List String} {config : Config}
    {artifact : Artifact F} (compiled : compile program entries config = .ok artifact)
    {rom : WireROM F} (rule : RuleInstance artifact.unmerged rom)
    (absent : program.findFunction? rule.conclusion.channel = none) : rule.premises = [] := by
  cases rule with
  | node chip row lookup valid =>
      obtain ⟨function, found, _⟩ := compile_find_chip compiled lookup
      have names : chip.name = row.chip := by simpa using List.find?_some lookup
      simp [RuleInstance.conclusion, Chip.receive, names, found] at absent
  | table message member => rfl

variable {program : Program F} {artifact : Artifact F} {rom : WireROM F} {message : Message F}

/-- Node `view.1` of a memo graph over the physical circuits, read at the channel `view.2`, is
the source claim `claim`. One node has one view per function that shares its circuit. -/
def Prepared.Reads (prepared : Prepared artifact) (graph : MemoDerivation prepared.system rom message)
    (view : Fin graph.size × String) (claim : Message F) : Prop :=
  claim.channel = view.2 ∧ prepared.Signed claim ∧
    prepared.translate claim = (graph.node view.1).conclusion

/-- A view reads one claim. -/
theorem Prepared.Reads.unique {prepared : Prepared artifact}
    {graph : MemoDerivation prepared.system rom message} {view : Fin graph.size × String}
    {first second : Message F} (left : prepared.Reads graph view first)
    (right : prepared.Reads graph view second) : first = second :=
  prepared.translate_injective (left.1.trans right.1.symm) left.2.1 right.2.1
    (left.2.2.trans right.2.2.symm)

/-- `caller` calls `callee`: a premise of the caller's node, both read at claims whose decoded
arguments have store provenance, by a call the static analysis of the caller's function
allows. -/
def Prepared.Calls (program : Program F) (prepared : Prepared artifact) (store : ROM F)
    (graph : MemoDerivation prepared.system rom message) (caller callee : Fin graph.size × String) :
    Prop :=
  ∃ (claim next : Message F) (args values : List (Value F)) (function : Function F),
    prepared.Reads graph caller claim ∧ prepared.Reads graph callee next ∧
    (∃ j, callee.1 = graph.target caller.1 j) ∧
    DecodesValues program.enums claim.args args ∧ (∀ value ∈ args, store.Provenance value) ∧
    DecodesValues program.enums next.args values ∧ (∀ value ∈ values, store.Provenance value) ∧
    program.findFunction? caller.2 = some function ∧
    Depth.Structural.Allowed store args (Depth.Structural.calls function) callee.2 values

/-- The decoded arguments of the claim a view reads, if it reads one that decodes. -/
noncomputable def Prepared.arguments (program : Program F) (prepared : Prepared artifact)
    (graph : MemoDerivation prepared.system rom message) (view : Fin graph.size × String) :
    List (Value F) :=
  open Classical in
  if known : ∃ args claim, prepared.Reads graph view claim ∧
      DecodesValues program.enums claim.args args then known.choose else []

theorem Prepared.arguments_eq {prepared : Prepared artifact}
    {graph : MemoDerivation prepared.system rom message} {view : Fin graph.size × String}
    {claim : Message F} {args : List (Value F)} (reads : prepared.Reads graph view claim)
    (decoded : DecodesValues program.enums claim.args args) :
    prepared.arguments program graph view = args := by
  have known : ∃ args claim, prepared.Reads graph view claim ∧
      DecodesValues program.enums claim.args args := ⟨args, claim, reads, decoded⟩
  rw [Prepared.arguments, dite_eq_left_of_eq_true (eq_true known)]
  obtain ⟨other, otherReads, otherDecoded⟩ := known.choose_spec
  rw [otherReads.unique reads] at otherDecoded
  exact otherDecoded.unique decoded

/-- A view whose arguments have store provenance evaluates, with a result that has store
provenance, once the calls between such views are well-founded. -/
theorem Prepared.view_sound {entries : List String} {config : Config}
    (compiled : compile program entries config = .ok artifact) (prepared : Prepared artifact)
    {rom : WidthROM F} (valid : rom.Valid) {message : Message F}
    (graph : MemoDerivation prepared.system (Erasure.rawROM rom) message)
    (founded : WellFounded fun callee caller => prepared.Calls program
      ((Erasure.typedROM artifact.system rom).decode program.enums) graph caller callee)
    (view : Fin graph.size × String) (claim : Message F) (reads : prepared.Reads graph view claim)
    (args : List (Value F)) (arguments : DecodesValues program.enums claim.args args)
    (trusted : ∀ value ∈ args,
      ((Erasure.typedROM artifact.system rom).decode program.enums).Provenance value) :
    ∃ result, claim.result.decode program.enums = some result ∧
      ROMEvalCall ((Erasure.typedROM artifact.system rom).decode program.enums) program
        claim.channel args result ∧
      ((Erasure.typedROM artifact.system rom).decode program.enums).Provenance result := by
  have romValid : (Erasure.typedROM artifact.system rom).Valid := rom.toWireROM_valid valid _ _
  induction view using founded.induction generalizing claim args with
  | h view ih =>
      obtain ⟨rule, rfl, translated, signed⟩ :=
        prepared.rule_view (graph.node view.1) claim reads.2.1 reads.2.2
      obtain ⟨result, decoded, ⟨locals, body, called, evaluated⟩, resultTrusted⟩ :=
        compile_structural_sound compiled _ romValid rule
          (ROMEvalCall ((Erasure.typedROM artifact.system rom).decode program.enums) program) args
          arguments trusted (by
            intro premise member values premiseArguments premiseTrusted allowed
            obtain ⟨j, bounded, same⟩ := List.mem_iff_getElem.mp member
            have inside : j < (graph.node view.1).premises.length := by
              rw [← translated, List.length_map]
              exact bounded
            have next : prepared.Reads graph (graph.target view.1 ⟨j, inside⟩, premise.channel)
                premise := by
              refine ⟨rfl, signed premise member, ?_⟩
              rw [graph.target_claim view.1 ⟨j, inside⟩]
              have item := List.getElem_of_eq translated.symm inside
              rw [List.getElem_map, same] at item
              exact item.symm
            cases found : program.findFunction? rule.conclusion.channel with
            | none =>
                rw [premises_of_no_function compiled rule found] at member
                cases member
            | some function =>
                obtain ⟨value, decoded, evaluated, _⟩ := ih _
                  ⟨rule.conclusion, premise, args, values, function, reads, next, ⟨_, rfl⟩,
                    arguments, trusted, premiseArguments, premiseTrusted, reads.1 ▸ found,
                    allowed function found⟩
                  premise next values premiseArguments premiseTrusted
                exact ⟨value, decoded, evaluated⟩)
          (fun _ _ _ evaluated trusted =>
            evaluated.provenance (WireROM.decode_valid romValid) trusted)
      exact ⟨result, decoded, .intro called evaluated.toEvalExpr, resultTrusted⟩

/-- An edge of the depth graph that keeps the rank between two circuits with depth words,
lowering the word by a small step. -/
def DepthStep (cfg : Depth.Config) {system : System F} {root : Message F}
    (graph : MemoDerivation (Depth.system cfg system) rom root) (parent child : Fin graph.size) :
    Prop :=
  ∃ k, child = graph.target parent k ∧ ∃ s : Nat, 0 < s ∧ s ≤ 2 ^ cfg.bits ∧
    Depth.depthWord (graph.node child).conclusion + (s : F) =
      Depth.depthWord (graph.node parent).conclusion

/-- A function's plan, by name. -/
def planOf (measures : Depth.Structural.Plan) (name : String) : Depth.Structural.FunctionPlan :=
  (measures.lookup name).getD default

/-- A call between two views moves the measures of their functions down. -/
def Prepared.Falls (program : Program F) (prepared : Prepared artifact)
    (measures : Depth.Structural.Plan) (height : Value F → Nat)
    (graph : MemoDerivation prepared.system rom message) (caller callee : Fin graph.size × String) :
    Prop :=
  Depth.Structural.Moves height (planOf measures caller.2) (planOf measures callee.2)
    (prepared.arguments program graph caller) (prepared.arguments program graph callee)

omit [Field F] [DecidableEq F] in
/-- The channel of a row of the depth graph is the channel of the row it erases to. -/
theorem erase_channel {cfg : Depth.Config} {erased original : Message F}
    (same : erased = Depth.erase cfg original) : original.channel = erased.channel := by
  rw [same]
  unfold Depth.erase
  split <;> rfl

/-- How a call between two views moves, under both halves of the structural certificate: it
lowers the SCC rank, or it lies over a depth-word step of the depth graph, or it moves the
checked measures down. -/
theorem Prepared.calls_step (prepared : Prepared artifact) {cfg : Depth.Config}
    (certified : Depth.Structural.certify cfg prepared.system = true)
    {measures : Depth.Structural.Plan}
    (checked : Depth.Structural.check cfg program prepared.representative measures = true)
    {store : ROM F} {height : Value F → Nat}
    (falls : ∀ {part whole : Value F}, store.Provenance whole →
      Depth.Structural.Part store part whole → height part < height whole)
    {root : Message F} (graph : MemoDerivation (Depth.system cfg prepared.system) rom root)
    (erased : MemoDerivation prepared.system rom (Depth.erase cfg root))
    (origin : Fin erased.size → Fin graph.size)
    (rows : ∀ i, (erased.node i).isNode = true → (graph.node (origin i)).isNode = true ∧
      (erased.node i).conclusion = Depth.erase cfg (graph.node (origin i)).conclusion ∧
      (graph.node (origin i)).conclusion.channel ∉ cfg.names)
    (edges : ∀ i j, (erased.node (erased.target i j)).isNode = true →
      ∃ k, origin (erased.target i j) = graph.target (origin i) k)
    {caller callee : Fin erased.size × String}
    (call : prepared.Calls program store erased caller callee)
    (row : (erased.node callee.1).isNode = true) :
    Depth.nodeRank cfg (graph.node (origin callee.1)) <
        Depth.nodeRank cfg (graph.node (origin caller.1)) ∨
      Depth.nodeRank cfg (graph.node (origin callee.1)) =
          Depth.nodeRank cfg (graph.node (origin caller.1)) ∧
        ((cfg.recursive (graph.node (origin caller.1)).conclusion.channel = true ∧
            cfg.recursive (graph.node (origin callee.1)).conclusion.channel = true ∧
            DepthStep cfg graph (origin caller.1) (origin callee.1)) ∨
          (¬ cfg.recursive (graph.node (origin caller.1)).conclusion.channel = true ∧
            ¬ cfg.recursive (graph.node (origin callee.1)).conclusion.channel = true ∧
            prepared.Falls program measures height erased caller callee)) := by
  obtain ⟨claim, next, args, values, function, reads, nextReads, ⟨j, target⟩, decoded, good,
    nextDecoded, _, found, site, listed, named, sound⟩ := call
  have callerRow : (erased.node caller.1).isNode = true := isNode_of_premise j
  rw [target] at row
  obtain ⟨k, edge⟩ := edges caller.1 j row
  rw [← target] at edge row
  have step := Depth.Structural.graph_step certified graph (origin caller.1) k
  rw [← edge] at step
  rcases step with lower | ⟨same, ⟨first, second, depth⟩ | ⟨first, second⟩⟩
  · exact .inl lower
  · exact .inr ⟨same, .inl ⟨first, second, k, edge, depth⟩⟩
  · have plain : ∀ name, cfg.structural.contains name = true → ¬ cfg.recursive name = true := by
      intro name member
      have all := certified
      simp only [Depth.Structural.certify, Bool.and_eq_true, List.all_eq_true] at all
      simpa using all.2 name (List.contains_iff_mem.mp member)
    refine .inr ⟨same, .inr ⟨plain _ first, plain _ second, ?_⟩⟩
    have callerChannel : (graph.node (origin caller.1)).conclusion.channel =
        prepared.representative caller.2 := by
      rw [erase_channel (rows _ callerRow).2.1, ← reads.2.2, Prepared.translate_channel, reads.1]
    have calleeChannel : (graph.node (origin callee.1)).conclusion.channel =
        prepared.representative callee.2 := by
      rw [erase_channel (rows _ row).2.1, ← nextReads.2.2, Prepared.translate_channel,
        nextReads.1]
    rw [nodeRank_row cfg (rows _ callerRow).1, nodeRank_row cfg (rows _ row).1, callerChannel,
      calleeChannel] at same
    rw [callerChannel] at first
    rw [calleeChannel] at second
    have member := List.mem_of_find?_eq_some found
    have name : function.name = caller.2 := Circuit.findFunction_name found
    simp only [Depth.Structural.check, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true'] at checked
    have functionChecked :
        Depth.Structural.checkFunction cfg prepared.representative measures function = true := by
      rcases checked.1.2 function member with absent | present
      · rw [name, first] at absent
        cases absent
      · exact present
    unfold Depth.Structural.checkFunction at functionChecked
    cases planned : measures.lookup function.name with
    | none => simp [planned] at functionChecked
    | some own =>
        simp only [planned, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at functionChecked
        have descent : Depth.Structural.descends measures own site = true := by
          rcases functionChecked site listed with apart | present
          · have joined : Depth.Structural.together cfg prepared.representative function.name
                site.callee = true := by
              unfold Depth.Structural.together
              rw [name, named, first, second, Nat.succ_injective same]
              simp
            rw [joined] at apart
            cases apart
          · exact present
        obtain ⟨goal, goalPlanned, moves⟩ :=
          Depth.Structural.descends_moves falls good sound descent
        have ownPlan : planOf measures caller.2 = own := by simp [planOf, ← name, planned]
        have goalPlan : planOf measures callee.2 = goal := by simp [planOf, ← named, goalPlanned]
        unfold Prepared.Falls
        rw [ownPlan, goalPlan, prepared.arguments_eq reads decoded,
          prepared.arguments_eq nextReads nextDecoded]
        exact moves

/-- Under both halves of the structural certificate, the calls between views with store
provenance are well-founded. -/
theorem Prepared.calls_wellFounded (prepared : Prepared artifact) {cfg : Depth.Config}
    (certified : Depth.Structural.certify cfg prepared.system = true)
    {measures : Depth.Structural.Plan}
    (checked : Depth.Structural.check cfg program prepared.representative measures = true)
    (bits : cfg.bits ≤ 24) {store : ROM F} (valid : store.Valid)
    {root : Message F} (graph : MemoDerivation (Depth.system cfg prepared.system) rom root)
    (erased : MemoDerivation prepared.system rom (Depth.erase cfg root))
    (origin : Fin erased.size → Fin graph.size) (count : erased.rows.card ≤ graph.rows.card)
    (rows : ∀ i, (erased.node i).isNode = true → (graph.node (origin i)).isNode = true ∧
      (erased.node i).conclusion = Depth.erase cfg (graph.node (origin i)).conclusion ∧
      (graph.node (origin i)).conclusion.channel ∉ cfg.names)
    (edges : ∀ i j, (erased.node (erased.target i j)).isNode = true →
      ∃ k, origin (erased.target i j) = graph.target (origin i) k)
    {N : Nat} (card : graph.rows.card ≤ N)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ N * 2 ^ 24 → (n : F) ≠ 0) :
    WellFounded fun callee caller => prepared.Calls program store erased caller callee := by
  obtain ⟨height, falls⟩ := Depth.Structural.exists_height valid
  let live : Finset (Fin erased.size × String) :=
    erased.rows ×ˢ (program.functions.map (·.name)).toFinset
  have source : ∀ caller callee, prepared.Calls program store erased caller callee →
      caller ∈ live := by
    rintro caller callee ⟨_, _, _, _, function, _, _, ⟨j, _⟩, _, _, _, _, found, _⟩
    refine Finset.mem_product.mpr ⟨?_, List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨function, List.mem_of_find?_eq_some found, Circuit.findFunction_name found⟩)⟩
    simpa [MemoDerivation.rows] using isNode_of_premise j
  have functions : program.functions.length ≤ 2 ^ 16 := by
    simp only [Depth.Structural.check, Bool.and_eq_true, decide_eq_true_eq] at checked
    exact checked.1.1
  have liveCard : live.card ≤ N * 2 ^ 16 := by
    rw [Finset.card_product]
    refine Nat.mul_le_mul (count.trans card) ((List.toFinset_card_le _).trans ?_)
    simpa using functions
  refine CycleLength.wellFounded_of_no_cycle (rows := live) source fun view => ?_
  refine CycleLength.no_cycle_kinds
    (first := fun caller callee => DepthStep cfg graph (origin caller.1) (origin callee.1))
    (second := fun caller callee => prepared.Falls program measures height erased caller callee)
    (fun view => Depth.nodeRank cfg (graph.node (origin view.1)))
    (fun view => cfg.recursive (graph.node (origin view.1)).conclusion.channel = true)
    ?_ ?_ ?_ view
  · rintro caller callee ⟨call, member⟩
    refine prepared.calls_step certified checked falls graph erased origin rows edges call ?_
    simpa [MemoDerivation.rows] using (Finset.mem_product.mp member).1
  · intro view cycle
    refine CycleLength.no_cycle (edge := DepthStep cfg graph) (rows := graph.rows) (N := N)
      (B := 2 ^ cfg.bits) ?_ card (fun _ => 0)
      (fun node => Depth.depthWord (graph.node node).conclusion)
      (fun _ _ step => .inr ⟨rfl, step.choose_spec.2⟩) ?_ (origin view.1)
      (cycle.lift (fun view : Fin erased.size × String => origin view.1) fun _ _ step => step)
    · rintro parent child ⟨k, rfl, _⟩
      exact graph.source_row ⟨k, rfl⟩
    · intro n positive small
      exact characteristic n positive (small.trans
        (Nat.mul_le_mul_left N (Nat.pow_le_pow_right (by norm_num) bits)))
  · intro view cycle
    refine CycleLength.no_cycle_mixed (rows := live) (N := N * 2 ^ 16)
      (B := Depth.Structural.maxStep) (fun caller callee step => source caller callee step.1.1)
      liveCard (fun _ => 0)
      (fun view => (planOf measures view.2).measure.isParts = false)
      (fun view => (planOf measures view.2).measure.depth (prepared.arguments program erased view))
      (fun view => (planOf measures view.2).measure.size height
        (prepared.arguments program erased view))
      (fun view => (planOf measures view.2).order) ?_ ?_ view cycle
    · rintro caller callee ⟨_, moves | moves⟩
      · exact .inr ⟨rfl, .inl moves⟩
      · exact .inr ⟨rfl, .inr ⟨by simp [moves.1], by simp [moves.2.1], moves.2.2⟩⟩
    · intro n positive small
      refine characteristic n positive (small.trans (le_of_eq ?_))
      rw [Depth.Structural.maxStep, Nat.mul_assoc]
      norm_num

/-- The root of a memo graph for an entry claim, read at the entry's channel, is that claim. -/
theorem Prepared.reads_entry (prepared : Prepared artifact) {claim : Message F}
    (selected : claim.channel ∈ artifact.entries) (signed : Erasure.Signed artifact.system claim)
    (rooted : message = Erasure.message artifact.system claim)
    (graph : MemoDerivation prepared.system rom message) :
    prepared.Reads graph (graph.root, claim.channel) claim := by
  have fixed := artifact.deduplication.entry_fixed (root := claim) selected
  refine ⟨rfl, ?_, ?_⟩
  · unfold Prepared.Signed
    rw [fixed]
    exact signed
  · rw [graph.root_claim, rooted]
    unfold Prepared.translate
    rw [fixed]
    exact prepared.merged.certificate.entry_fixed
      (root := Erasure.message artifact.system claim) (by simpa using selected)

/-- The arguments of an entry claim at the root of a memo graph are pointer-free: the root row
has the argument types of the entry's signature, which `checkEntry` validated. -/
theorem Prepared.entry_publicArguments {entries : List String} {config : Config}
    (compiled : compile program entries config = .ok artifact) (prepared : Prepared artifact)
    {rom : WidthROM F} {claim : Message F} (entry : claim.channel ∈ entries)
    (interface : checkEntry program claim.channel = .ok ())
    (signed : Erasure.Signed artifact.system claim)
    (rooted : message = Erasure.message artifact.system claim)
    (graph : MemoDerivation prepared.system (Erasure.rawROM rom) message) :
    claim.PublicArguments program.enums := by
  have selected : claim.channel ∈ artifact.entries := by
    simpa only [(compile_stages compiled).2.2.1] using entry
  have reads := prepared.reads_entry selected signed rooted graph
  obtain ⟨rule, conclusion, _, _⟩ :=
    prepared.rule_view (graph.node graph.root) claim reads.2.1 reads.2.2
  obtain ⟨signature, found, free⟩ := (checkEntry_ok program claim.channel).mp interface
  have types := (compile_semanticModel compiled).argumentTypes _ rule signature
    (by simpa only [conclusion] using found)
  rw [conclusion] at types
  intro wire member
  apply free wire.type
  rw [← types]
  exact List.mem_map.mpr ⟨wire, member, rfl⟩

/-- A memo graph over the depth pass of the physical circuits, certified with exempt SCCs,
gives a finite derivation of the entry claim in the physical circuits. -/
theorem Prepared.structural_memo_sound {program : Program F} {entries : List String}
    {config : Config} {artifact : Artifact F}
    (compiled : compile program entries config = .ok artifact) (prepared : Prepared artifact)
    {cfg : Depth.Config} (certified : Depth.Structural.certify cfg prepared.system = true)
    {measures : Depth.Structural.Plan}
    (checked : Depth.Structural.check cfg program prepared.representative measures = true)
    (bits : cfg.bits ≤ 24)
    {rom : WidthROM F} (valid : rom.Valid) {claim : Message F} (entry : claim.channel ∈ entries)
    (signed : Erasure.Signed artifact.system claim) (free : claim.PublicArguments program.enums)
    {root : Message F} (rooted : Depth.erase cfg root = Erasure.message artifact.system claim)
    (outside : root.channel ∉ cfg.names)
    (graph : MemoDerivation (Depth.system cfg prepared.system) (Erasure.rawROM rom) root)
    {N : Nat} (card : graph.rows.card ≤ N)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ N * 2 ^ 24 → (n : F) ≠ 0) :
    Derives prepared.system (Erasure.rawROM rom) (Erasure.message artifact.system claim) := by
  have stages := compile_stages compiled
  have selected : claim.channel ∈ artifact.entries := by simpa only [stages.2.2.1] using entry
  have romValid : (Erasure.typedROM artifact.system rom).Valid := rom.toWireROM_valid valid _ _
  obtain ⟨erased, origin, count, rows, edges⟩ :=
    Depth.Structural.erase_graph certified graph outside
  have founded := prepared.calls_wellFounded (program := program) certified checked bits
    (WireROM.decode_valid (decls := program.enums) romValid) graph erased origin count rows edges
    card characteristic
  have reads := prepared.reads_entry selected signed rooted erased
  obtain ⟨rule, conclusion, _, _⟩ :=
    prepared.rule_view (erased.node erased.root) claim reads.2.1 reads.2.2
  obtain ⟨args, arguments⟩ :=
    compile_entry_arguments compiled rule (by rw [conclusion]; exact entry)
  rw [conclusion] at arguments
  have trusted : ∀ value ∈ args,
      ((Erasure.typedROM artifact.system rom).decode program.enums).Provenance value := by
    intro value member
    have typeMember : value.type ∈ claim.args.map WireValue.type := by
      rw [← arguments.types]
      exact List.mem_map.mpr ⟨value, member, rfl⟩
    obtain ⟨wire, wireMember, same⟩ := List.mem_map.mp typeMember
    exact .of_pointerFree value
      (Value.pointerFree_of_type (same ▸ free wire wireMember) (arguments.wellFormed value member))
  obtain ⟨result, decoded, evaluated, _⟩ :=
    prepared.view_sound compiled valid erased founded _ claim reads args arguments trusted
  have derived := (compile_semanticModel compiled).complete_encoded evaluated arguments decoded
  exact (prepared.derives_iff selected signed).mp ((artifact.dedup_derives_iff selected).mp derived)

/-! ## The certificate of compiled circuits -/

variable {source : Generic.Source F} {entries : List String}
  {specialized : Generic.Specialized source entries} {id : String → Except String Nat}

/-- The depth certificate of the physical circuits of a compiled program: the circuit half
(`Depth.Structural.certify`), and the source half (`Depth.Structural.check`) for some measures
of the functions compiled to circuits without a depth word. -/
def Prepared.DepthCertified (compiled : GenericArtifact specialized)
    (prepared : Prepared compiled.artifact) (cfg : Depth.Config) : Prop :=
  Depth.Structural.certify cfg prepared.system = true ∧
    ∃ measures, Depth.Structural.check cfg compiled.inlined.program prepared.representative
      measures = true

/-- Executable exporter certificate of a depth-grouped plan over the physical circuits compiled
from `program`: both halves of the depth certificate with the given measures, `cfg.bits ≤ 24`,
and `plan.WellFormedActivation`. -/
def Prepared.checkDepthPlan (program : Program F) {artifact : Artifact F}
    (prepared : Prepared artifact) (cfg : Depth.Config) (measures : Depth.Structural.Plan)
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) : Bool :=
  Depth.Structural.certify cfg prepared.system &&
    Depth.Structural.check cfg program prepared.representative measures &&
    decide (cfg.bits ≤ 24) && plan.checkWellFormedActivation

theorem Prepared.checkDepthPlan_iff (program : Program F) {artifact : Artifact F}
    (prepared : Prepared artifact) (cfg : Depth.Config) (measures : Depth.Structural.Plan)
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) :
    prepared.checkDepthPlan program cfg measures plan = true ↔
      (Depth.Structural.certify cfg prepared.system = true ∧
        Depth.Structural.check cfg program prepared.representative measures = true) ∧
      cfg.bits ≤ 24 ∧ plan.WellFormedActivation := by
  simp [Prepared.checkDepthPlan, Grouping.Plan.checkWellFormedActivation_iff, and_assoc]

/-- The exporter certificate over the program a `GenericArtifact` compiles gives its depth
certificate. -/
theorem Prepared.checkDepthPlan_sound {compiled : GenericArtifact specialized}
    {prepared : Prepared compiled.artifact} {cfg : Depth.Config}
    {measures : Depth.Structural.Plan}
    {plan : Grouping.Plan (Depth.system cfg prepared.system) id}
    (checked : prepared.checkDepthPlan compiled.inlined.program cfg measures plan = true) :
    Prepared.DepthCertified compiled prepared cfg ∧ cfg.bits ≤ 24 ∧ plan.WellFormedActivation := by
  obtain ⟨⟨certified, source⟩, bits, activated⟩ :=
    (prepared.checkDepthPlan_iff compiled.inlined.program cfg measures plan).mp checked
  exact ⟨⟨certified, measures, source⟩, bits, activated⟩

/-- Rows accepted by the grouped, activated memo checker over the certified depth pass of the
physical circuits, with a row bound, give a finite derivation of the entry claim in the
physical circuits. -/
theorem Prepared.depth_checkMemo_sound (compiled : GenericArtifact specialized)
    (prepared : Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Prepared.DepthCertified compiled prepared cfg) (bits : cfg.bits ≤ 24)
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id)
    (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries) {rom : WidthROM F} (valid : rom.Valid)
    {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Message F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    {rows : List (WeightedRow F)} {N : Nat} (bound : rows.length ≤ N)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ N * 2 ^ 24 → (n : F) ≠ 0)
    (checked : plan.checkMemo (Erasure.rawROM rom) root rows = .ok ()) :
    Derives prepared.system (Erasure.rawROM rom)
      (Erasure.message compiled.system ⟨name, wires, output⟩) := by
  obtain ⟨circuits, measures, functions⟩ := certified
  obtain ⟨graph, card⟩ := Grouping.Plan.checkMemo_graph activated checked
  obtain ⟨erased, _⟩ := Depth.Structural.erase_graph circuits graph outside
  have free := prepared.entry_publicArguments compiled.compiled (claim := ⟨name, wires, output⟩)
    entry (compiled.inlined.valid.2.2 name entry).2 signed rooted erased
  exact prepared.structural_memo_sound compiled.compiled circuits functions bits valid
    (claim := ⟨name, wires, output⟩) entry signed free rooted outside graph (card.trans bound)
    characteristic

end Aiur.Optimized.Physical
