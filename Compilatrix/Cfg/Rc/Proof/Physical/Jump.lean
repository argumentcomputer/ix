import Compilatrix.Cfg.Rc.Proof.Physical.Edge
import Compilatrix.Rt.Proof.StepTerm

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native.Spec
open Compilatrix.Rt.Proof Compilatrix.Rt.Lower
open Compilatrix.Lir (Word)
open Compilatrix.Src (NatMap)

/-- The actual ordinary jump lowering supplies the same reached-edge receipt
as ordinary/fused switches, including its actual cold overflow edge. -/
theorem ordinary_jump_reaches {T : Tables} {lp : Lir.Program} {fn src : Nat}
    {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (lookup : lp.funcs[fn]? = some F) (held : Holds fn F off starts C)
    {e : Cfg.Edge} {state final : St}
    (lowered : (term fn T src (.jump e)).run state = .ok ((), final))
    (labels : Labels state) (opened : Open state) (extension : Ext C final)
    (mem : X86.Memory) (context : Word) (registers : Lir.Env) (callers : List Lir.Frame) :
    ∃ pe le, EdgeOk C fn e pe ∧ e.back = decide (e.target ≤ src) ∧
      resolveEdge fn off starts pe = .ok le ∧
      ReachesEdge lp fn F mem context callers (off+state.cur)
        (Lir.atState mem context fn (off+state.cur) state.acc.length registers callers) le registers := by
  obtain ⟨pe, after, edgeRun, rfl, _, sameCur, sameAcc⟩ := term_jump lowered labels opened
  obtain ⟨back, _, _, _, _, _, _, afterOpen, edgeOk⟩ := edge_facts edgeRun labels
  have correct := edgeOk (grows_close (afterOpen opened) _) extension
  obtain ⟨le, resolved, reached⟩ := closed_jump (mem := mem) (ctx := context) (rest := callers)
    lookup held (Grows.refl _) extension registers
  rw [sameCur, sameAcc] at reached
  exact ⟨pe, le, correct, back, resolved, reached⟩

/-- A finished actual raw cursor with an ordinary jump exposes its concrete
layout and reached-edge receipt. No target-execution input is required. -/
theorem Cursor.jump_reaches {T : Tables} {P : Cfg.Program} {lp : Lir.Program}
    {source : Cfg.Frame} {target : Lir.Frame} (cursor : Cursor T P lp source target)
    {fd : Cfg.Fun} {block : Cfg.Block}
    (sourceLookup : P.fun? source.fn = some fd) (blockLookup : fd.blocks[source.blk]? = some block)
    (finished : source.rest = []) {e : Cfg.Edge} (terminal : block.term = .jump e)
    (mem : X86.Memory) (context : Word) (callers : List Lir.Frame) :
    ∃ F starts off C low pe le,
      lp.funcs[source.fn]? = some F ∧ Lowered T source.fn fd F starts ∧
      starts.get? source.blk = some off ∧ Holds source.fn F off starts C ∧ off ≤ low ∧
      EdgeOk C source.fn e pe ∧ e.back = decide (e.target ≤ source.blk) ∧
      resolveEdge source.fn off starts pe = .ok le ∧
      ReachesEdge lp source.fn F mem context callers low
        (Lir.atState mem context target.fn target.label target.pos target.env callers) le target.env := by
  obtain ⟨fd', block', F, starts, off, C, state, final, hfd, hb, hF, layout, start,
    held, lowering, extension, labels, opened, _, _, fn, label, pos⟩ := cursor
  have sameFd : fd' = fd := Option.some.inj (hfd.symm.trans sourceLookup)
  subst fd'
  have sameBlock : block' = block := Option.some.inj (hb.symm.trans blockLookup)
  subst block'
  rw [finished] at lowering
  have code := rest_nil lowering
  have unfused : fusable T (useCounts fd) block = none := by
    cases fused : fusable T (useCounts fd) block with
    | none => rfl
    | some row =>
      obtain ⟨init, condition, left, right⟩ := row
      obtain ⟨x, op, alts, default, _, _, switch, _⟩ := fusable_some fused
      rw [terminal] at switch
      cases switch
  simp only [unfused, terminal] at code
  obtain ⟨pe, le, edge, back, resolved, reached⟩ :=
    ordinary_jump_reaches hF held code labels opened extension mem context target.env callers
  refine ⟨F, starts, off, C, off+state.cur, pe, le, hF, layout, start, held,
    Nat.le_add_right _ _, edge, back, resolved, ?_⟩
  simpa only [fn, label, pos] using reached

theorem ConsumedCursor.jump_reaches {P : Program} {pairs : List (Nat × Cfg.Fun)}
    (consuming : consumeAll P = .ok pairs) {lp : Lir.Program}
    {source : Cfg.Frame} {target : Lir.Frame} (cursor : ConsumedCursor P pairs lp source target)
    (range : source.fn < P.base.size) {fd actual : Cfg.Fun} {block : Cfg.Block}
    (sourceLookup : P.base.fun? source.fn = some fd)
    (actualLookup : (consumed P pairs).fun? source.fn = some actual)
    (blockLookup : fd.blocks[source.blk]? = some block)
    (finished : source.rest = []) {e : Cfg.Edge} (terminal : block.term = .jump e)
    (mem : X86.Memory) (context : Word) (callers : List Lir.Frame) :
    ∃ F starts off C low pe le,
      lp.funcs[source.fn]? = some F ∧ Lowered (tablesOf P pairs) source.fn actual F starts ∧
      starts.get? source.blk = some off ∧ Holds source.fn F off starts C ∧ off ≤ low ∧
      EdgeOk C source.fn e pe ∧ e.back = decide (e.target ≤ source.blk) ∧
      resolveEdge source.fn off starts pe = .ok le ∧
      ReachesEdge lp source.fn F mem context callers low
        (Lir.atState mem context target.fn target.label target.pos target.env callers) le target.env := by
  obtain ⟨original, consumedFd, originalLookup, receipt, consumedLookup⟩ := consumed_entry consuming range
  have sameSource : original = fd := Option.some.inj (originalLookup.symm.trans sourceLookup)
  subst original
  have sameTarget : consumedFd = actual := Option.some.inj (consumedLookup.symm.trans actualLookup)
  subst consumedFd
  obtain ⟨body, _, actualBlock⟩ := (consumeFunction_parts receipt).2.2.2.2.2 blockLookup
  obtain ⟨rest, consumeRest, position⟩ := cursor
  rw [finished] at consumeRest
  simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at consumeRest
  subst rest
  exact position.jump_reaches actualLookup actualBlock rfl terminal mem context callers




end Compilatrix.Cfg.Rc.Native.Spec
