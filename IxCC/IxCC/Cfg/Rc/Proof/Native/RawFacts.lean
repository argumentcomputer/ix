import IxCC.Cfg.Rc.Proof.Native.ConsumedCursor
import IxCC.Cfg.Rc.Proof.Native.Consume
import IxCC.Cfg.Rc.Proof.Physical.Bridge.RawSlots

/-! What the accepted native flow check (`Cfg.Rc.Raw.rawOk` over the consumed program) says at
a cursor: the current instruction's and terminator's flows, the raw flags of a block's
parameters, and that a function with a heap-cell instruction has no raw register. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Rt.Rc.Procs IxCC.Rt.Lower

theorem tablesOf_rawVar (P : Program) (pairs : List (Nat × Cfg.Fun)) :
    (tablesOf P pairs).rawVar = P.raw.isRaw := rfl

theorem tablesOf_rawRet (P : Program) (pairs : List (Nat × Cfg.Fun)) :
    (tablesOf P pairs).rawRet = P.raw.retRaw := rfl

theorem consumed_size (P : Program) (pairs : List (Nat × Cfg.Fun)) :
    (consumed P pairs).size = P.base.size := rfl

/-- A function of the consumed program is a function of the source program. -/
theorem consumed_lookup_lt {P : Program} {pairs : List (Nat × Cfg.Fun)}
    (consuming : consumeAll P = .ok pairs) {f : Nat} {fd : Cfg.Fun}
    (lookup : (consumed P pairs).fun? f = some fd) : f < P.base.size := by
  rcases Nat.lt_or_ge f P.base.size with inside | outside
  · exact inside
  · exfalso
    have keys := consumeAll_keys consuming
    have nodup : (pairs.map (·.1)).Nodup := by
      rw [show (pairs.map (·.1)) = pairs.map Prod.fst from rfl, keys]
      exact List.nodup_range
    have absent : f ∉ pairs.map (·.1) := by
      rw [show (pairs.map (·.1)) = pairs.map Prod.fst from rfl, keys, List.mem_range]
      omega
    have none := (Src.NatMap.get?_foldl_insert (fun _ _ => rfl) pairs .leaf nodup).1 f absent
    simp only [consumed, Cfg.Program.fun?, Src.NatMap.ofList] at lookup
    rw [none] at lookup
    cases lookup

/-- A runtime procedure (past the program's functions) has no raw parameter. -/
theorem rawParams_runtime {P : Program} {pairs : List (Nat × Cfg.Fun)}
    (consuming : consumeAll P = .ok pairs) {g : Nat} (outside : P.base.size ≤ g) (b : Nat) :
    (tablesOf P pairs).rawParams g b = [] := by
  cases h : (consumed P pairs).fun? g with
  | none => simp [tablesOf, Raw.rawTables, Raw.paramsOf, h]
  | some fd => exact absurd (consumed_lookup_lt consuming h) (Nat.not_lt.mpr outside)

/-- A call of a runtime procedure reads its operands tagged. -/
theorem operandsAt_runtime {P : Program} {pairs : List (Nat × Cfg.Fun)}
    (consuming : consumeAll P = .ok pairs) {g : Nat} (outside : P.base.size ≤ g)
    (f : Fir.FunId) (as : List Fir.Arg) :
    Rt.Lower.operandsAt f ((tablesOf P pairs).rawParams g 0) as = Rt.Lower.operands f as := by
  rw [rawParams_runtime consuming outside]
  exact Rt.Proof.operandsAt_tagged (by simp)

/-- A call of a runtime procedure is not one a function with a raw register may hold. -/
theorem rawFnInstr_runtime {P : Program} {pairs : List (Nat × Cfg.Fun)} {f x g : Nat}
    {as : List Fir.Arg} (outside : P.base.size ≤ g) :
    Raw.rawFnInstr P.raw (consumed P pairs) f (.bind x (.fir (.call g as))) = false := by
  simp only [Raw.rawFnInstr, consumed_size]
  exact decide_eq_false (Nat.not_lt.mpr outside)

/-- The raw flags of a block's parameters are its parameters' own. -/
theorem rawParams_consumed {P : Program} {pairs : List (Nat × Cfg.Fun)}
    (consuming : consumeAll P = .ok pairs) {f b : Nat} (range : f < P.base.size)
    {fd : Cfg.Fun} {block : Cfg.Block} (lookup : P.base.fun? f = some fd)
    (blockLookup : fd.blocks[b]? = some block) :
    (tablesOf P pairs).rawParams f b = (block.params.map Prod.fst).map (P.raw.isRaw f) := by
  obtain ⟨original, lowered, originalLookup, receipt, consumedLookup⟩ := consumed_entry consuming range
  rw [lookup] at originalLookup
  cases originalLookup
  obtain ⟨body, _, targetBlock⟩ := (consumeFunction_parts receipt).2.2.2.2.2 blockLookup
  simp only [tablesOf, Raw.rawTables, Raw.paramsOf, consumedLookup, targetBlock, List.map_map]
  rfl

/-! ## The check, function by function -/

variable {L : RawLayout} {C : Cfg.Program}

theorem rawOk_funOk (h : Raw.rawOk L C = true) {f : Nat} {fd : Cfg.Fun} (range : f < C.size)
    (lookup : C.fun? f = some fd) : Raw.funOk L C f fd = true := by
  simp only [Raw.rawOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have := h.1.1 f range
  rw [lookup] at this
  exact this

theorem rawOk_exportOk (h : Raw.rawOk L C = true) {f : Nat} (member : f ∈ C.exports) :
    Raw.exportOk L C f = true := by
  simp only [Raw.rawOk, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1.2 f member


/-- No function returns a raw word. -/
theorem rawOk_retRaw (h : Raw.rawOk L C = true) (f : Nat) : L.retRaw f = false := by
  simp only [Raw.rawOk, Bool.and_eq_true, List.isEmpty_iff] at h
  simp [RawLayout.retRaw, h.2]
theorem funOk_blockOk {f : Nat} {fd : Cfg.Fun} (h : Raw.funOk L C f fd = true) {i : Nat}
    {b : Cfg.Block} (lookup : fd.blocks[i]? = some b) : Raw.blockOk L C f b = true := by
  simp only [Raw.funOk, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1 b (List.mem_of_getElem? lookup)

theorem blockOk_instrOk {f : Nat} {b : Cfg.Block} (h : Raw.blockOk L C f b = true) {i : Cfg.Instr}
    (member : i ∈ b.body) : Raw.instrOk L C f i = true := by
  simp only [Raw.blockOk, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1 i member

theorem blockOk_termOk {f : Nat} {b : Cfg.Block} (h : Raw.blockOk L C f b = true) :
    Raw.termOk L C f b.term = true := by
  simp only [Raw.blockOk, Bool.and_eq_true] at h
  exact h.2

/-- A function with a heap-cell instruction has no raw register and no raw result. -/
theorem funOk_heap {f : Nat} {fd : Cfg.Fun} (h : Raw.funOk L C f fd = true) {j : Nat}
    {b : Cfg.Block} (lookup : fd.blocks[j]? = some b) {i : Cfg.Instr} (member : i ∈ b.body)
    (heap : Raw.heapInstr C i = true) : (∀ y, L.isRaw f y = false) ∧ L.retRaw f = false := by
  simp only [Raw.funOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h.2 with noRaw | free
  · simp only [Raw.hasRaw, Bool.or_eq_false_iff, Bool.not_eq_false', List.isEmpty_iff] at noRaw
    refine ⟨fun y => ?_, noRaw.2⟩
    simp [RawLayout.isRaw, noRaw.1]
  · simp only [Raw.rawFree, List.all_eq_true] at free
    have := free b (List.mem_of_getElem? lookup) i member
    rw [Raw.rawFnInstr_heap heap] at this
    cases this

/-- An instruction of a function: either the function has no raw register, or the instruction
is one a function with a raw register may hold. -/
theorem funOk_raw {f : Nat} {fd : Cfg.Fun} (h : Raw.funOk L C f fd = true) {j : Nat}
    {b : Cfg.Block} (lookup : fd.blocks[j]? = some b) {i : Cfg.Instr} (member : i ∈ b.body) :
    (∀ y, L.isRaw f y = false) ∨ Raw.rawFnInstr L C f i = true := by
  simp only [Raw.funOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h.2 with noRaw | free
  · simp only [Raw.hasRaw, Bool.or_eq_false_iff, Bool.not_eq_false', List.isEmpty_iff] at noRaw
    exact .inl fun y => by simp [RawLayout.isRaw, noRaw.1]
  · simp only [Raw.rawFree, List.all_eq_true] at free
    exact .inr (free b (List.mem_of_getElem? lookup) i member)

/-- A block whose last comparison is fused holds a `Nat` comparison, which a function with a raw
register may not hold: its function has no raw register. -/
theorem fusable_noRaw {T : Tables} {uses : Src.NatMap Nat} {f : Nat} {fd : Cfg.Fun}
    (h : Raw.funOk L C f fd = true) {j : Nat} {b : Cfg.Block} (lookup : fd.blocks[j]? = some b)
    (row : List Cfg.Instr × Lir.Cond × Fir.Arg × Fir.Arg) (fused : fusable T uses b = some row) :
    ∀ y, L.isRaw f y = false := by
  obtain ⟨init, c, a, a'⟩ := row
  obtain ⟨x, op, alts, d, body, comparison, _⟩ := Rt.Proof.fusable_some fused
  rcases funOk_raw h lookup (i := .bind x (.fir (.prim op [a, a']))) (by rw [body]; simp)
    with noRaw | raw
  · exact noRaw
  · exfalso
    cases op
    case word w o => simp [compareOf] at comparison
    all_goals simp [Raw.rawFnInstr] at raw

/-! ## At a cursor -/

/-- The current instruction: its function has no raw register, or it is one a function with a
raw register may hold. -/
theorem Cursor.rawCases {T : Tables} {lp : Lir.Program} {source : Cfg.Frame} {target : Lir.Frame}
    (cursor : Cursor T C lp source target) {i : Cfg.Instr} {tail : List Cfg.Instr}
    (head : source.rest = i :: tail) (h : Raw.rawOk L C = true) (range : source.fn < C.size) :
    (∀ y, L.isRaw source.fn y = false) ∨ Raw.rawFnInstr L C source.fn i = true := by
  obtain ⟨fd, block, _, _, _, _, _, _, lookup, blockLookup, _, _, _, _, _, _, _, _, _,
    ⟨pre, body⟩, _⟩ := cursor
  exact funOk_raw (rawOk_funOk h range lookup) blockLookup (by rw [← body, head]; simp)

/-- The current instruction's flows. -/
theorem Cursor.instrOk {T : Tables} {lp : Lir.Program} {source : Cfg.Frame} {target : Lir.Frame}
    (cursor : Cursor T C lp source target) {i : Cfg.Instr} {tail : List Cfg.Instr}
    (head : source.rest = i :: tail) (h : Raw.rawOk L C = true) (range : source.fn < C.size) :
    Raw.instrOk L C source.fn i = true := by
  obtain ⟨fd, block, _, _, _, _, _, _, lookup, blockLookup, _, _, _, _, _, _, _, _, _,
    ⟨pre, body⟩, _⟩ := cursor
  exact blockOk_instrOk (funOk_blockOk (rawOk_funOk h range lookup) blockLookup)
    (by rw [← body, head]; simp)

/-- The current block's terminator flows. -/
theorem Cursor.termOk {T : Tables} {lp : Lir.Program} {source : Cfg.Frame} {target : Lir.Frame}
    (_cursor : Cursor T C lp source target) (h : Raw.rawOk L C = true) (range : source.fn < C.size)
    {fd : Cfg.Fun} {block : Cfg.Block} (lookup : C.fun? source.fn = some fd)
    (blockLookup : fd.blocks[source.blk]? = some block) :
    Raw.termOk L C source.fn block.term = true :=
  blockOk_termOk (funOk_blockOk (rawOk_funOk h range lookup) blockLookup)

/-- A heap-cell instruction at the cursor: its function has no raw register or result. -/
theorem Cursor.noRaw {T : Tables} {lp : Lir.Program} {source : Cfg.Frame} {target : Lir.Frame}
    (cursor : Cursor T C lp source target) {i : Cfg.Instr} {tail : List Cfg.Instr}
    (head : source.rest = i :: tail) (h : Raw.rawOk L C = true) (range : source.fn < C.size)
    (heap : Raw.heapInstr C i = true) :
    (∀ y, L.isRaw source.fn y = false) ∧ L.retRaw source.fn = false := by
  obtain ⟨fd, block, _, _, _, _, _, _, lookup, blockLookup, _, _, _, _, _, _, _, _, _,
    ⟨pre, body⟩, _⟩ := cursor
  exact funOk_heap (rawOk_funOk h range lookup) blockLookup (by rw [← body, head]; simp) heap

/-- The consumed instruction at a consumed cursor has the flows the check states. -/
theorem ConsumedCursor.instrOk {P : Program} {pairs : List (Nat × Cfg.Fun)} {lp : Lir.Program}
    {source : Cfg.Frame} {target : Lir.Frame} (cursor : ConsumedCursor P pairs lp source target)
    {i : Cfg.Instr} {tail : List Cfg.Instr} (head : source.rest = i :: tail) {actual : Cfg.Instr}
    (consuming : consume P (layoutOf P) i = .ok actual)
    (h : Raw.rawOk P.raw (consumed P pairs) = true) (range : source.fn < P.base.size) :
    Raw.instrOk P.raw (consumed P pairs) source.fn actual = true := by
  obtain ⟨actual', rest, hc, _, position⟩ := cursor.next head
  rw [consuming] at hc
  cases hc
  exact position.instrOk (tail := rest) rfl h range

/-- The consumed instruction at a consumed cursor: its function has no raw register, or it is
one a function with a raw register may hold. -/
theorem ConsumedCursor.rawCases {P : Program} {pairs : List (Nat × Cfg.Fun)} {lp : Lir.Program}
    {source : Cfg.Frame} {target : Lir.Frame} (cursor : ConsumedCursor P pairs lp source target)
    {i : Cfg.Instr} {tail : List Cfg.Instr} (head : source.rest = i :: tail) {actual : Cfg.Instr}
    (consuming : consume P (layoutOf P) i = .ok actual)
    (h : Raw.rawOk P.raw (consumed P pairs) = true) (range : source.fn < P.base.size) :
    (∀ y, P.raw.isRaw source.fn y = false) ∨
      Raw.rawFnInstr P.raw (consumed P pairs) source.fn actual = true := by
  obtain ⟨actual', rest, hc, _, position⟩ := cursor.next head
  rw [consuming] at hc
  cases hc
  exact position.rawCases (tail := rest) rfl h range

/-- **A consumed instruction a function with a raw register may not hold**: its function has
no raw register. -/
theorem ConsumedCursor.noRaw {P : Program} {pairs : List (Nat × Cfg.Fun)} {lp : Lir.Program}
    {source : Cfg.Frame} {target : Lir.Frame} (cursor : ConsumedCursor P pairs lp source target)
    {i : Cfg.Instr} {tail : List Cfg.Instr} (head : source.rest = i :: tail) {actual : Cfg.Instr}
    (consuming : consume P (layoutOf P) i = .ok actual)
    (h : Raw.rawOk P.raw (consumed P pairs) = true) (range : source.fn < P.base.size)
    (excluded : Raw.rawFnInstr P.raw (consumed P pairs) source.fn actual = false) :
    ∀ y, (tablesOf P pairs).rawVar source.fn y = false :=
  (cursor.rawCases head consuming h range).resolve_right (by rw [excluded]; simp)

/-- The flows of a block's terminator, read off the consumed block (consumption keeps it). -/
theorem termOk_source {P : Program} {pairs : List (Nat × Cfg.Fun)}
    (consuming : consumeAll P = .ok pairs) (h : Raw.rawOk P.raw (consumed P pairs) = true)
    {f b : Nat} (range : f < P.base.size) {fd : Cfg.Fun} {block : Cfg.Block}
    (lookup : P.base.fun? f = some fd) (blockLookup : fd.blocks[b]? = some block) :
    Raw.termOk P.raw (consumed P pairs) f block.term = true := by
  obtain ⟨original, lowered, originalLookup, receipt, consumedLookup⟩ := consumed_entry consuming range
  rw [lookup] at originalLookup
  cases originalLookup
  obtain ⟨body, _, targetBlock⟩ := (consumeFunction_parts receipt).2.2.2.2.2 blockLookup
  have flows := blockOk_termOk (funOk_blockOk (rawOk_funOk h range consumedLookup) targetBlock)
  exact flows

/-- The arguments of an edge of a block fit its target's parameters. -/
theorem termOk_edge {f : Nat} {t : Cfg.Term} (h : Raw.termOk L C f t = true) {e : Cfg.Edge}
    (member : e ∈ t.edges) : Raw.edgeOk L C f e = true := by
  cases t with
  | jump e' =>
    simp only [Cfg.Term.edges, List.mem_singleton] at member
    subst member
    exact h
  | switch x alts d =>
    simp only [Raw.termOk, Bool.and_eq_true, List.all_eq_true] at h
    exact h.2 e (by simpa [Cfg.Term.edges] using member)
  | ret a => simp [Cfg.Term.edges] at member
  | tcall g as => simp [Cfg.Term.edges] at member
  | trap => simp [Cfg.Term.edges] at member

/-- An edge's arguments fit its target block's parameters, read as the lowering reads them. -/
theorem edgeOk_fits {P : Program} {pairs : List (Nat × Cfg.Fun)} {f : Nat} {e : Cfg.Edge}
    (h : Raw.edgeOk P.raw (consumed P pairs) f e = true) :
    Raw.argsFit ((tablesOf P pairs).rawVar f) ((tablesOf P pairs).rawParams f e.target) e.args = true :=
  h

/-- A call's arguments fit the callee's parameters, read as the lowering reads them. -/
theorem paramsOf_tables (P : Program) (pairs : List (Nat × Cfg.Fun)) (g b : Nat) :
    (tablesOf P pairs).rawParams g b = Raw.paramsOf P.raw (consumed P pairs) g b := rfl

/-- At tagged positions only, the parameters of an exported function. -/
theorem exportOk_params {f : Nat} (h : Raw.exportOk L C f = true) :
    ∀ r ∈ Raw.paramsOf L C f 0, r = false := by
  simp only [Raw.exportOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  exact h.1


/-- **An exported function is entered with tagged words**: its parameters are not raw. -/
theorem entry_of_export {P : Program} {pairs : List (Nat × Cfg.Fun)}
    (h : Raw.rawOk P.raw (consumed P pairs) = true) {f : Nat} (member : f ∈ P.base.exports) :
    ∀ r ∈ (tablesOf P pairs).rawParams f 0, r = false :=
  exportOk_params (rawOk_exportOk h member)

end IxCC.Cfg.Rc.Native.Spec
