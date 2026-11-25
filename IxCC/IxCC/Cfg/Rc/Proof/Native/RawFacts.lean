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
  · simp only [Raw.heapFree, List.all_eq_true] at free
    have := free b (List.mem_of_getElem? lookup) i member
    simp [heap] at this

/-! ## At a cursor -/

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

end IxCC.Cfg.Rc.Native.Spec
