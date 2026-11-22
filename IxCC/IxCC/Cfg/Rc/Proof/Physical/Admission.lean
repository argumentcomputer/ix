import IxCC.Cfg.Rc.Proof.Entry
import IxCC.Cfg.Rc.Proof.Bounds
import IxCC.Cfg.Rc.Proof.Native.Consume
import IxCC.Rt.Proof.LayoutFun

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec

theorem functionBounds_block {limit first : Nat} {fd : Cfg.Fun}
    (checked : functionBounds limit first fd = true) {index : Nat} {block : Cfg.Block}
    (lookup : fd.blocks[index]? = some block) :
    block.params.all (fun p => decide (p.1 < first)) = true ∧
      block.body.all (instrBound limit first) = true ∧
      termBound limit first fd.blocks.length block.term = true := by
  have each := List.all_eq_true.mp checked block (List.mem_of_getElem? lookup)
  simpa only [Bool.and_eq_true, and_assoc] using each

theorem functionBounds_params {limit first : Nat} {fd : Cfg.Fun}
    (checked : functionBounds limit first fd = true) {index : Nat} {block : Cfg.Block}
    (lookup : fd.blocks[index]? = some block) :
    ∀ x ∈ block.params.map Prod.fst, x < first := by
  intro x member
  obtain ⟨param, present, rfl⟩ := List.mem_map.mp member
  exact of_decide_eq_true (List.all_eq_true.mp (functionBounds_block checked lookup).1 param present)

theorem functionBounds_marker {limit first : Nat} {fd : Cfg.Fun}
    (checked : functionBounds limit first fd = true) {index : Nat} {block : Cfg.Block}
    (lookup : fd.blocks[index]? = some block) {instruction : Cfg.Instr}
    (member : instruction ∈ block.body) (reserved : Rc.reserved limit instruction = true)
    {slot : Nat} {action : Action} (decoded : decode limit instruction = some (slot, action)) :
    first ≤ slot ∧ (match action with | .inc x _ | .dec x => x < first) :=
  checked_action_operand reserved decoded
    (List.all_eq_true.mp (functionBounds_block checked lookup).2.1 instruction member)

/-- Every original block uses the original Fir variable bound. Marker
destinations remain above that bound even though the lowered function's
temporary namespace is larger. -/
theorem checked_source_bounds {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} (checked : checkScopedProgram F bodies P = true)
    {f : Nat} (range : f < F.size) {source : Fir.Fun} {fd : Cfg.Fun}
    (sourceLookup : F.fun? f = some source) (lookup : P.base.fun? f = some fd) :
    functionBounds P.base.size source.vars fd = true := by
  obtain ⟨actual, table, actualLookup, _, source', body, sourceLookup', _, lowering,
    bounds, _⟩ := checked_entry (checkScopedProgram_parts checked).1 range
  have hs : source' = source := Option.some.inj (sourceLookup'.symm.trans sourceLookup)
  have ht : actual = fd := Option.some.inj (actualLookup.symm.trans lookup)
  subst source'; subst actual
  rw [generate_size (checkProgram_parts (checkScopedProgram_parts checked).1).2]
  exact bounds

theorem checked_block_params {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} (checked : checkScopedProgram F bodies P = true)
    {f : Nat} (range : f < F.size) {source : Fir.Fun} {fd : Cfg.Fun}
    (sourceLookup : F.fun? f = some source) (lookup : P.base.fun? f = some fd)
    {index : Nat} {block : Cfg.Block} (blockLookup : fd.blocks[index]? = some block) :
    ∀ x ∈ block.params.map Prod.fst, x < source.vars :=
  functionBounds_params (checked_source_bounds checked range sourceLookup lookup) blockLookup

/-- The real original bound is below every native temporary supply: lowering
retains source.vars plus marker space, consumption retains vars, and supOf
includes the function vars field independently of syntactic occurrences. -/
theorem checked_consumed_sup {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} (checked : checkScopedProgram F bodies P = true)
    {f : Nat} (range : f < F.size) {source : Fir.Fun} {fd actual : Cfg.Fun}
    (sourceLookup : F.fun? f = some source) (lookup : P.base.fun? f = some fd)
    (consuming : consumeFunction P (layoutOf P) fd = .ok actual) :
    source.vars ≤ Rt.Proof.supOf actual := by
  obtain ⟨original, table, originalLookup, _, source', body, sourceLookup', _, lowering, _⟩ :=
    checked_entry (checkScopedProgram_parts checked).1 range
  have hs : source' = source := Option.some.inj (sourceLookup'.symm.trans sourceLookup)
  have ht : original = fd := Option.some.inj (originalLookup.symm.trans lookup)
  subst source'; subst original
  have vars : fd.vars = source.vars + actionCount body := by rw [lowering]; rfl
  have retained := (consumeFunction_parts consuming).2.2.1
  unfold Rt.Proof.supOf
  omega

theorem checked_marker_bounds {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} (checked : checkScopedProgram F bodies P = true)
    {f : Nat} (range : f < F.size) {source : Fir.Fun} {fd : Cfg.Fun}
    (sourceLookup : F.fun? f = some source) (lookup : P.base.fun? f = some fd)
    {index : Nat} {block : Cfg.Block} (blockLookup : fd.blocks[index]? = some block)
    {instruction : Cfg.Instr} (member : instruction ∈ block.body)
    (reserved : Rc.reserved P.base.size instruction = true) {slot : Nat} {action : Action}
    (decoded : decode P.base.size instruction = some (slot, action)) :
    source.vars ≤ slot ∧ (match action with | .inc x _ | .dec x => x < source.vars) := by
  cases action <;>
    exact functionBounds_marker (checked_source_bounds checked range sourceLookup lookup)
      blockLookup member reserved decoded

/-- Exact original block-zero data from the real checked lowering. -/
theorem checked_entry_block {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} (checked : checkScopedProgram F bodies P = true)
    {f : Nat} (range : f < F.size) {source : Fir.Fun} {body : Own.Plain.Code}
    (sourceLookup : F.fun? f = some source) (bodyLookup : bodies.get? f = some body) :
    ∃ fd block, P.base.fun? f = some fd ∧ fd.blocks[0]? = some block ∧
      block.params.map Prod.fst = source.params.map Prod.fst ∧
      block.params.length = source.params.length ∧
      block.body = Cfg.Proof.spine (skeleton P.base.size source.vars body) ∧
      functionBounds P.base.size source.vars fd = true := by
  obtain ⟨fd, table, lookup, _, source', body', sourceLookup', bodyLookup', lowering,
    bounds, _⟩ := checked_entry (checkScopedProgram_parts checked).1 range
  have hs : source' = source := Option.some.inj (sourceLookup'.symm.trans sourceLookup)
  have hc : body' = body := Option.some.inj (bodyLookup'.symm.trans bodyLookup)
  subst source'; subst body'
  let ownFd : Own.Fun := {Own.immFun source with
    body := skeleton F.size source.vars body, vars := source.vars + actionCount body}
  obtain ⟨terminal, entry⟩ := Cfg.Proof.block_zero f ownFd
  have params : (ownFd.params.zip ownFd.sig.params).map Prod.fst = ownFd.params :=
    Cfg.Proof.zip_fst (by simp [ownFd, Own.immFun])
  have size := generate_size (checkProgram_parts (checkScopedProgram_parts checked).1).2
  refine ⟨fd, {
    params := ownFd.params.zip ownFd.sig.params
    body := Cfg.Proof.spine ownFd.body
    term := terminal }, lookup, ?_, params, ?_, ?_, ?_⟩
  · simpa only [lowering, lowerFunction, Cfg.Fun.block?, ownFd] using entry
  · simp [ownFd, Own.immFun]
  · simp only [ownFd, size]
  · simpa only [size] using bounds

/-- Construct At at the exact block-zero frame selected by actual admission.
The statement includes the real source entry step and has no naming premise. -/
theorem checked_entry_at {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} (checked : checkScopedProgram F bodies P = true)
    {f : Nat} (range : f < F.size) {source : Fir.Fun} {body : Own.Plain.Code}
    (sourceLookup : F.fun? f = some source) (bodyLookup : bodies.get? f = some body)
    {fd : Cfg.Fun} {block : Cfg.Block} (lookup : P.base.fun? f = some fd)
    (blockLookup : fd.blocks[0]? = some block)
    (values : List Own.RVal) (arity : values.length = source.params.length)
    (callers : List (Cfg.Frame × Fir.Var)) (H : Own.Heap) :
    let entry : Cfg.Frame := {
      fn := f
      blk := 0
      rest := block.body
      env := Own.bindAll .leaf (source.params.map Prod.fst) values }
    step P (.call f values callers H) = .next (.run entry callers H) true ∧
      At F P entry (Own.bindAll .leaf (source.params.map Prod.fst) values) [] body := by
  obtain ⟨fd', block', lookup', blockLookup', params, length, _, _⟩ :=
    checked_entry_block checked range sourceLookup bodyLookup
  have sameFd : fd' = fd := Option.some.inj (lookup'.symm.trans lookup)
  subst fd'
  have sameBlock : block' = block := Option.some.inj (blockLookup'.symm.trans blockLookup)
  subst block'
  have actual := Cfg.Proof.step_call (pol := Own.AllocPol.rc) lookup blockLookup
    (arity.trans length.symm) (stk := callers) (H := H)
  rw [params] at actual
  obtain ⟨frame, sourceStep, layout⟩ := checked_entry_step checked range sourceLookup bodyLookup
    values arity callers H
  have equal := sourceStep.symm.trans actual
  have frameEq := (Cfg.State.run.inj (Sem.Step.next.inj equal).1).1
  subst frame
  exact ⟨actual, layout⟩







end IxCC.Cfg.Rc.Native.Spec
