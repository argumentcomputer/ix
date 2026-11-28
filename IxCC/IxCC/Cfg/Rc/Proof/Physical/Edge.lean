import IxCC.Cfg.Rc.Proof.Native.ConsumedCursor
import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedBindings
import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedOperands
import IxCC.Cfg.Rc.Proof.Native.RawFacts
import IxCC.Cfg.Rc.Proof.Environment
import IxCC.Cfg.Proof.Sim
import IxCC.Rt.Proof.StepEdge

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Rt.Rc.Procs IxCC.Rt.Proof IxCC.Rt.Lower
open IxCC.Lir (Word)
open IxCC.Src (NatMap)

/-- Complete a locally proved reached edge with the actual dynamic argument
words and parameter binding. The total charge is the reached charges charge
plus the exact final jump charge. No heap invariant or target run is assumed.
Each argument reaches its parameter at the parameter's raw or tagged position (`fits`, from the
flow check), so a raw parameter holds its argument's raw word. -/
theorem dynamic_edge_complete
    {T : Tables} {addresses : AddressMap} {fd : Cfg.Fun} {bound f : Nat}
    {lp : Lir.Program} {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat}
    {C : List PBlock} {mem : X86.Memory} {ctx : Word} {rest : List Lir.Frame}
    {low : Nat} {s : Lir.State}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {e : Cfg.Edge} {pe : PEdge} {le : Lir.Edge}
    (hok : EdgeOk C f T e pe) (hres : resolveEdge f off starts pe = .ok le)
    {source : Own.Env} {target : Lir.Env}
    (reach : ReachesEdge lp fn F mem ctx rest low s le target)
    (registers : FusedWords addresses (Omit T f fd) bound source target)
    (raws : RawWords (T.rawVar f) source target)
    (fits : Cfg.Rc.Raw.argsFit (T.rawVar f) (T.rawParams f e.target) e.args = true)
    (live : ∀ a ∈ e.args, LiveArg (Fused T fd) a) {values : List Own.RVal}
    (evaluated : Own.evalArgs source e.args = some values)
    {params : List Nat} (flags : T.rawParams f e.target = params.map (T.rawVar f))
    (arity : params.length = values.length)
    (real : ∀ x ∈ params, x < bound) {offset : Nat} {block : Lir.Block}
    (start : starts.get? e.target = some offset)
    (lookup : F.blocks[offset]? = some block) (parameters : block.params = params)
    (back : e.back = true → offset ≤ low) :
    Sem.Fails (Lir.semStep lp) s ∨
      ∃ charges label words after,
        low ≤ label ∧
        SlotsRel addresses (params.map (T.rawVar f)) values words ∧
        Lir.bindParams target params words = some after ∧
        Sem.Star (Lir.semStep lp) s (charges + (decide (offset ≤ label)).toNat)
          (Lir.atState mem ctx fn offset 0 after rest) ∧
        e.back.toNat ≤ charges + (decide (offset ≤ label)).toNat ∧
        (e.back = true → decide (offset ≤ label) = true) ∧
        FusedWords addresses (Omit T f fd) bound (Own.bindAll source params values) after ∧
        RawWords (T.rawVar f) (Own.bindAll source params values) after := by
  obtain ⟨charges, label, pos, lower, trace, step⟩ := reach
  rcases hok with ⟨operands, lowered, rfl⟩ | ⟨cold, lowered, rfl, coldBlock⟩
  · simp only [resolveEdge, resolveTgt, start, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at hres
    subst hres
    obtain ⟨words, actual, represented, _⟩ :=
      slot_operands_words registers raws lowered fits live evaluated
    rw [flags] at represented
    obtain ⟨after, binding, related, rawsAfter⟩ :=
      slots_bindParams registers raws represented arity real
    have jump := step words block after actual lookup (parameters ▸ binding)
    have charged : e.back = true → decide (offset ≤ label) = true := by
      intro hb
      exact decide_eq_true (Nat.le_trans (back hb) lower)
    refine .inr ⟨charges, label, words, after, lower, represented, binding,
      trace.trans (Lir.star_of_step jump), ?_, charged, related, rawsAfter⟩
    cases hb : e.back
    · simp
    · rw [charged hb]
      simp
  · simp only [resolveEdge, resolveTgt, loc, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at hres
    subst hres
    obtain ⟨block, resolved, blockLookup⟩ := hH coldBlock
    obtain ⟨params, body, terminal⟩ := resolveBlock_ok resolved
    simp only [resolveTerm, pure, Except.pure, Except.ok.injEq] at terminal
    have jump := step [] block target rfl blockLookup (by simp [params, Lir.bindParams])
    refine .inl ⟨charges + (decide (off+cold ≤ label)).toNat, _, .natOverflow,
      trace.trans (Lir.star_of_step jump), ?_⟩
    exact Lir.semStep_fail.2 (Lir.fail_at hF blockLookup
      (by rw [← Array.length_toList, body]; rfl) terminal.symm)

/-- The accepted raw function layout determines the target chunk, target
parameter names, and source back-edge classification. The lexical and Cfg
environments stay related, with neither replaced by a projection. -/
theorem raw_take_edge {T : Tables} {P : Cfg.Program} {lp : Lir.Program}
    {fn blockId : Nat} {fd : Cfg.Fun} {block targetBlock : Cfg.Block} {F : Lir.Func}
    {starts : NatMap Nat} {off low : Nat} {C : List PBlock}
    (sourceLookup : P.fun? fn = some fd) (blockLookup : fd.blocks[blockId]? = some block)
    (functionLookup : lp.funcs[fn]? = some F) (layout : Lowered T fn fd F starts)
    (start : starts.get? blockId = some off) (held : Holds fn F off starts C) (lower : off ≤ low)
    {e : Cfg.Edge} (member : e ∈ block.term.edges)
    (targetLookup : fd.blocks[e.target]? = some targetBlock) {pe : PEdge} {le : Lir.Edge}
    (edge : EdgeOk C fn T e pe) (resolved : resolveEdge fn off starts pe = .ok le)
    {addresses : AddressMap} {bound : Nat} {lexical cfgEnv : Own.Env} {registerEnv : Lir.Env}
    (sub : EnvSub lexical cfgEnv)
    (registers : FusedWords addresses (Omit T fn fd) bound lexical registerEnv)
    (raws : RawWords (T.rawVar fn) lexical registerEnv)
    (fits : Cfg.Rc.Raw.argsFit (T.rawVar fn) (T.rawParams fn e.target) e.args = true)
    (flags : T.rawParams fn e.target = (targetBlock.params.map Prod.fst).map (T.rawVar fn))
    {values : List Own.RVal} (arguments : Own.evalArgs lexical e.args = some values)
    (arity : targetBlock.params.length = values.length)
    (real : ∀ x ∈ targetBlock.params.map Prod.fst, x < bound)
    {mem : X86.Memory} {context : Word} {callers : List Lir.Frame} {initial : Lir.State}
    (reached : ReachesEdge lp fn F mem context callers low initial le registerEnv) :
    Sem.Fails (Lir.semStep lp) initial ∨
      ∃ offset charges label words after,
        starts.get? e.target = some offset ∧ low ≤ label ∧
        SlotsRel addresses ((targetBlock.params.map Prod.fst).map (T.rawVar fn)) values words ∧
        Lir.bindParams registerEnv (targetBlock.params.map Prod.fst) words = some after ∧
        Sem.Star (Lir.semStep lp) initial (charges + (decide (offset ≤ label)).toNat)
          (Lir.atState mem context fn offset 0 after callers) ∧
        e.back = decide (e.target ≤ blockId) ∧
        e.back.toNat ≤ charges + (decide (offset ≤ label)).toNat ∧
        (e.back = true → decide (offset ≤ label) = true) ∧
        Cursor T P lp
          {fn, blk := e.target, rest := targetBlock.body,
            env := Own.bindAll cfgEnv (targetBlock.params.map Prod.fst) values}
          {fn, label := offset, pos := 0, env := after} ∧
        EnvSub (Own.bindAll lexical (targetBlock.params.map Prod.fst) values)
          (Own.bindAll cfgEnv (targetBlock.params.map Prod.fst) values) ∧
        FusedWords addresses (Omit T fn fd) bound
          (Own.bindAll lexical (targetBlock.params.map Prod.fst) values) after ∧
        RawWords (T.rawVar fn) (Own.bindAll lexical (targetBlock.params.map Prod.fst) values) after := by
  obtain ⟨offset, _, _, _, targetStart, _⟩ := layout.chunk targetLookup
  obtain ⟨physicalBlock, physicalLookup, params⟩ := layout.head targetLookup targetStart
  have head : headParams fd e.target targetBlock = targetBlock.params.map Prod.fst := by
    unfold headParams
    cases merged : mergedOf fd
    · simp
    · simp [merged_target merged blockLookup member]
  have back : e.back = true → offset ≤ low := by
    intro hb
    rw [layout.edges blockLookup member] at hb
    have := layout.mono targetStart start (of_decide_eq_true hb)
    omega
  rcases dynamic_edge_complete functionLookup held edge resolved reached registers raws fits
      (edge_live blockLookup member) arguments flags (by simpa using arity) real
      targetStart physicalLookup (params.trans head) back with failed | success
  · exact .inl failed
  · obtain ⟨charges, label, words, after, labelLower, represented, binding, trace,
      charge, charged, related, rawsAfter⟩ := success
    exact .inr ⟨offset, charges, label, words, after, targetStart, labelLower,
      represented, binding, trace, layout.edges blockLookup member, charge, charged,
      Cursor.head sourceLookup functionLookup layout targetLookup targetStart _ _,
      Cfg.Proof.Sub.bindAll sub _ _, related, rawsAfter⟩

/-- The raw flags of a block's parameters are its parameters' own, at a consumed function. -/
theorem rawParams_actual {P : Program} {pairs : List (Nat × Cfg.Fun)} {f b : Nat}
    {actual : Cfg.Fun} (actualLookup : (consumed P pairs).fun? f = some actual)
    {block : Cfg.Block} (blockLookup : actual.blocks[b]? = some block) :
    (tablesOf P pairs).rawParams f b = (block.params.map Prod.fst).map ((tablesOf P pairs).rawVar f) := by
  simp only [tablesOf, Raw.rawTables, Raw.paramsOf, actualLookup, blockLookup, List.map_map]
  rfl

/-- Preserve the whole actual Cfg register environment and restrict it to
the selected join's complete saved lexical environment. Original and consumed
block bodies are paired by the real consume receipt. No saved capture is
discarded and no separate saved-register assumption is required. The edge's arguments fit its
target's parameters (`fits`, from the accepted flow check). -/
theorem consumed_take_edge {P : Program} {pairs : List (Nat × Cfg.Fun)} {lp : Lir.Program}
    {fn blockId : Nat} {original actual : Cfg.Fun} {block targetBlock : Cfg.Block}
    {F : Lir.Func} {starts : NatMap Nat} {off low : Nat} {C : List PBlock}
    (consuming : consumeFunction P (layoutOf P) original = .ok actual)
    (actualLookup : (consumed P pairs).fun? fn = some actual)
    (blockLookup : original.blocks[blockId]? = some block)
    (functionLookup : lp.funcs[fn]? = some F)
    (layout : Lowered (tablesOf P pairs) fn actual F starts)
    (start : starts.get? blockId = some off) (held : Holds fn F off starts C) (lower : off ≤ low)
    {e : Cfg.Edge} (member : e ∈ block.term.edges)
    (targetLookup : original.blocks[e.target]? = some targetBlock)
    {pe : PEdge} {le : Lir.Edge} (edge : EdgeOk C fn (tablesOf P pairs) e pe)
    (resolved : resolveEdge fn off starts pe = .ok le)
    {addresses : AddressMap} {bound : Nat} {lexical saved cfgEnv : Own.Env}
    {registerEnv : Lir.Env}
    (sub : EnvSub lexical cfgEnv) (savedSub : EnvSub saved cfgEnv)
    (registers : FusedWords addresses (Omit (tablesOf P pairs) fn actual) bound cfgEnv registerEnv)
    (raws : RawWords ((tablesOf P pairs).rawVar fn) cfgEnv registerEnv)
    (fits : Raw.edgeOk P.raw (consumed P pairs) fn e = true)
    {values : List Own.RVal} (arguments : Own.evalArgs lexical e.args = some values)
    (arity : targetBlock.params.length = values.length)
    (real : ∀ x ∈ targetBlock.params.map Prod.fst, x < bound)
    {mem : X86.Memory} {context : Word} {callers : List Lir.Frame} {initial : Lir.State}
    (reached : ReachesEdge lp fn F mem context callers low initial le registerEnv) :
    Sem.Fails (Lir.semStep lp) initial ∨
      ∃ offset charges label words after,
        starts.get? e.target = some offset ∧ low ≤ label ∧
        SlotsRel addresses ((targetBlock.params.map Prod.fst).map ((tablesOf P pairs).rawVar fn))
          values words ∧
        Lir.bindParams registerEnv (targetBlock.params.map Prod.fst) words = some after ∧
        Sem.Star (Lir.semStep lp) initial (charges + (decide (offset ≤ label)).toNat)
          (Lir.atState mem context fn offset 0 after callers) ∧
        e.back = decide (e.target ≤ blockId) ∧
        e.back.toNat ≤ charges + (decide (offset ≤ label)).toNat ∧
        (e.back = true → decide (offset ≤ label) = true) ∧
        ConsumedCursor P pairs lp
          {fn, blk := e.target, rest := targetBlock.body,
            env := Own.bindAll cfgEnv (targetBlock.params.map Prod.fst) values}
          {fn, label := offset, pos := 0, env := after} ∧
        EnvSub (Own.bindAll saved (targetBlock.params.map Prod.fst) values)
          (Own.bindAll cfgEnv (targetBlock.params.map Prod.fst) values) ∧
        FusedWords addresses (Omit (tablesOf P pairs) fn actual) bound
          (Own.bindAll cfgEnv (targetBlock.params.map Prod.fst) values) after ∧
        RawWords ((tablesOf P pairs).rawVar fn)
          (Own.bindAll cfgEnv (targetBlock.params.map Prod.fst) values) after ∧
        FusedWords addresses (Omit (tablesOf P pairs) fn actual) bound
          (Own.bindAll saved (targetBlock.params.map Prod.fst) values) after ∧
        RawWords ((tablesOf P pairs).rawVar fn)
          (Own.bindAll saved (targetBlock.params.map Prod.fst) values) after := by
  obtain ⟨body, _, actualBlock⟩ := (consumeFunction_parts consuming).2.2.2.2.2 blockLookup
  obtain ⟨targetBody, consumedBody, actualTarget⟩ :=
    (consumeFunction_parts consuming).2.2.2.2.2 targetLookup
  have activeRegisters : FusedWords addresses (Omit (tablesOf P pairs) fn actual) bound lexical registerEnv :=
    ⟨fun h => registers.dom (sub _ _ h), fun h live => registers.word (sub _ _ h) live⟩
  have savedRegisters : FusedWords addresses (Omit (tablesOf P pairs) fn actual) bound saved registerEnv :=
    ⟨fun h => registers.dom (savedSub _ _ h), fun h live => registers.word (savedSub _ _ h) live⟩
  have flags := rawParams_actual actualLookup actualTarget
  rcases raw_take_edge actualLookup actualBlock functionLookup layout start held lower
      member actualTarget edge resolved sub activeRegisters (raws.restrict sub) fits flags
      arguments arity real reached with failed | success
  · exact .inl failed
  · obtain ⟨offset, charges, label, words, after, targetStart, labelLower, represented,
      binding, trace, back, charge, charged, cursor, _, _⟩ := success
    have length : (targetBlock.params.map Prod.fst).length = values.length := by simpa using arity
    obtain ⟨cfgWords, cfgRaws⟩ := slots_boundParams registers raws represented length real binding
    obtain ⟨savedWords, savedRaws⟩ :=
      slots_boundParams savedRegisters (raws.restrict savedSub) represented length real binding
    exact .inr ⟨offset, charges, label, words, after, targetStart, labelLower, represented,
      binding, trace, back, charge, charged, ⟨targetBody, consumedBody, cursor⟩,
      Cfg.Proof.Sub.bindAll savedSub _ _, cfgWords, cfgRaws, savedWords, savedRaws⟩

end IxCC.Cfg.Rc.Native.Spec
