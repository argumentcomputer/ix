import Compilatrix.Cfg.Rc.Proof.Native.ConsumedCursor
import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.FusedBindings
import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.FusedOperands
import Compilatrix.Cfg.Rc.Proof.Environment
import Compilatrix.Cfg.Proof.Sim
import Compilatrix.Rt.Proof.StepEdge

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native.Spec
open Compilatrix.Cfg.Rc.Proof.Physical.Bridge Compilatrix.Rt.Rc.Procs Compilatrix.Rt.Proof Compilatrix.Rt.Lower
open Compilatrix.Lir (Word)
open Compilatrix.Src (NatMap)

/-- Complete a locally proved reached edge with the actual dynamic argument
words and parameter binding. The total charge is the reached charges charge
plus the exact final jump charge. No heap invariant or target run is assumed. -/
theorem dynamic_edge_complete
    {addresses : AddressMap} {D : Nat → Prop} {bound f : Nat}
    {lp : Lir.Program} {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat}
    {C : List PBlock} {mem : X86.Memory} {ctx : Word} {rest : List Lir.Frame}
    {low : Nat} {s : Lir.State}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {e : Cfg.Edge} {pe : PEdge} {le : Lir.Edge}
    (hok : EdgeOk C f e pe) (hres : resolveEdge f off starts pe = .ok le)
    {source : Own.Env} {target : Lir.Env}
    (reach : ReachesEdge lp fn F mem ctx rest low s le target)
    (registers : FusedWords addresses D bound source target)
    (live : ∀ a ∈ e.args, LiveArg D a) {values : List Own.RVal}
    (evaluated : Own.evalArgs source e.args = some values)
    {params : List Nat} (arity : params.length = values.length)
    (real : ∀ x ∈ params, x < bound) {offset : Nat} {block : Lir.Block}
    (start : starts.get? e.target = some offset)
    (lookup : F.blocks[offset]? = some block) (parameters : block.params = params)
    (back : e.back = true → offset ≤ low) :
    Sem.Fails (Lir.semStep lp) s ∨
      ∃ charges label words after,
        low ≤ label ∧
        ListRel (fun value word => valueWord addresses value = some word) values words ∧
        Lir.bindParams target params words = some after ∧
        Sem.Star (Lir.semStep lp) s (charges + (decide (offset ≤ label)).toNat)
          (Lir.atState mem ctx fn offset 0 after rest) ∧
        e.back.toNat ≤ charges + (decide (offset ≤ label)).toNat ∧
        (e.back = true → decide (offset ≤ label) = true) ∧
        FusedWords addresses D bound (Own.bindAll source params values) after := by
  obtain ⟨charges, label, pos, lower, trace, step⟩ := reach
  rcases hok with ⟨operands, lowered, rfl⟩ | ⟨cold, lowered, rfl, coldBlock⟩
  · simp only [resolveEdge, resolveTgt, start, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at hres
    subst hres
    obtain ⟨words, actual, represented, _⟩ := fused_operands_words registers lowered live evaluated
    obtain ⟨after, binding, related⟩ := registers.bindParams represented arity real
    have jump := step words block after actual lookup (parameters ▸ binding)
    have charged : e.back = true → decide (offset ≤ label) = true := by
      intro hb
      exact decide_eq_true (Nat.le_trans (back hb) lower)
    refine .inr ⟨charges, label, words, after, lower, represented, binding,
      trace.trans (Lir.star_of_step jump), ?_, charged, related⟩
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
    (edge : EdgeOk C fn e pe) (resolved : resolveEdge fn off starts pe = .ok le)
    {addresses : AddressMap} {bound : Nat} {lexical cfgEnv : Own.Env} {registerEnv : Lir.Env}
    (sub : EnvSub lexical cfgEnv)
    (registers : FusedWords addresses (Fused T fd) bound lexical registerEnv)
    {values : List Own.RVal} (arguments : Own.evalArgs lexical e.args = some values)
    (arity : targetBlock.params.length = values.length)
    (real : ∀ x ∈ targetBlock.params.map Prod.fst, x < bound)
    {mem : X86.Memory} {context : Word} {callers : List Lir.Frame} {initial : Lir.State}
    (reached : ReachesEdge lp fn F mem context callers low initial le registerEnv) :
    Sem.Fails (Lir.semStep lp) initial ∨
      ∃ offset charges label words after,
        starts.get? e.target = some offset ∧ low ≤ label ∧
        ListRel (fun value word => valueWord addresses value = some word) values words ∧
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
        FusedWords addresses (Fused T fd) bound
          (Own.bindAll lexical (targetBlock.params.map Prod.fst) values) after := by
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
  rcases dynamic_edge_complete functionLookup held edge resolved reached registers
      (edge_live blockLookup member) arguments (by simpa using arity) real
      targetStart physicalLookup (params.trans head) back with failed | success
  · exact .inl failed
  · obtain ⟨charges, label, words, after, labelLower, represented, binding, trace,
      charge, charged, related⟩ := success
    exact .inr ⟨offset, charges, label, words, after, targetStart, labelLower,
      represented, binding, trace, layout.edges blockLookup member, charge, charged,
      Cursor.head sourceLookup functionLookup layout targetLookup targetStart _ _,
      Cfg.Proof.Sub.bindAll sub _ _, related⟩

/-- Preserve the whole actual Cfg register environment and restrict it to
the selected join's complete saved lexical environment. Original and consumed
block bodies are paired by the real consume receipt. No saved capture is
discarded and no separate saved-register assumption is required. -/
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
    {pe : PEdge} {le : Lir.Edge} (edge : EdgeOk C fn e pe)
    (resolved : resolveEdge fn off starts pe = .ok le)
    {addresses : AddressMap} {bound : Nat} {lexical saved cfgEnv : Own.Env}
    {registerEnv : Lir.Env}
    (sub : EnvSub lexical cfgEnv) (savedSub : EnvSub saved cfgEnv)
    (registers : FusedWords addresses (Fused (tablesOf P pairs) actual) bound cfgEnv registerEnv)
    {values : List Own.RVal} (arguments : Own.evalArgs lexical e.args = some values)
    (arity : targetBlock.params.length = values.length)
    (real : ∀ x ∈ targetBlock.params.map Prod.fst, x < bound)
    {mem : X86.Memory} {context : Word} {callers : List Lir.Frame} {initial : Lir.State}
    (reached : ReachesEdge lp fn F mem context callers low initial le registerEnv) :
    Sem.Fails (Lir.semStep lp) initial ∨
      ∃ offset charges label words after,
        starts.get? e.target = some offset ∧ low ≤ label ∧
        ListRel (fun value word => valueWord addresses value = some word) values words ∧
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
        FusedWords addresses (Fused (tablesOf P pairs) actual) bound
          (Own.bindAll cfgEnv (targetBlock.params.map Prod.fst) values) after ∧
        FusedWords addresses (Fused (tablesOf P pairs) actual) bound
          (Own.bindAll saved (targetBlock.params.map Prod.fst) values) after := by
  obtain ⟨body, _, actualBlock⟩ := (consumeFunction_parts consuming).2.2.2.2.2 blockLookup
  obtain ⟨targetBody, consumedBody, actualTarget⟩ :=
    (consumeFunction_parts consuming).2.2.2.2.2 targetLookup
  have activeRegisters : FusedWords addresses (Fused (tablesOf P pairs) actual) bound lexical registerEnv :=
    ⟨fun h => registers.dom (sub _ _ h), fun h live => registers.word (sub _ _ h) live⟩
  have savedRegisters : FusedWords addresses (Fused (tablesOf P pairs) actual) bound saved registerEnv :=
    ⟨fun h => registers.dom (savedSub _ _ h), fun h live => registers.word (savedSub _ _ h) live⟩
  rcases raw_take_edge actualLookup actualBlock functionLookup layout start held lower
      member actualTarget edge resolved sub activeRegisters arguments arity real reached with failed | success
  · exact .inl failed
  · obtain ⟨offset, charges, label, words, after, targetStart, labelLower, represented,
      binding, trace, back, charge, charged, cursor, _, _⟩ := success
    exact .inr ⟨offset, charges, label, words, after, targetStart, labelLower, represented,
      binding, trace, back, charge, charged, ⟨targetBody, consumedBody, cursor⟩,
      Cfg.Proof.Sub.bindAll savedSub _ _,
      registers.boundParams represented (by simpa using arity) real binding,
      savedRegisters.boundParams represented (by simpa using arity) real binding⟩




end Compilatrix.Cfg.Rc.Native.Spec
