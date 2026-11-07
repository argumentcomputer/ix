import IxCC.Cfg.Rc.Proof.Physical.Bridge.DynamicSwitch
import IxCC.Cfg.Rc.Proof.Physical.Bridge.ScalarSwitch
import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedSwitch
import IxCC.Cfg.Rc.Proof.Physical.Bridge.SwitchAdmission
import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedCtorEnv
import IxCC.Cfg.Rc.Proof.Physical.Jump

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Rt IxCC.Rt.Proof IxCC.Rt.Lower
open IxCC.Rt.Rc.Procs

/-- A finished raw switch cursor follows the selected source constructor.
Dynamic headers, scalar tags and omitted comparisons use their actual
lowering receipts; the fused overflow path remains an actual failure. -/
theorem Cursor.switch_reaches {T : Tables} {P : Cfg.Program} {lp : Lir.Program}
    {source : Cfg.Frame} {target : Lir.Frame} (cursor : Cursor T P lp source target)
    {fd : Cfg.Fun} {block : Cfg.Block}
    (sourceLookup : P.fun? source.fn = some fd) (blockLookup : fd.blocks[source.blk]? = some block)
    (finished : source.rest = []) {x : Nat} {alts : List (Key.CtorKey × Cfg.Edge)}
    {default : Option Cfg.Edge} (terminal : block.term = .switch x alts default)
    {heap : Own.Heap} {addresses : AddressMap} {mem : X86.Memory} {bound : Nat}
    (liveHeap : HeapLive heap addresses mem) (compatibleHeap : HeapCtorOk T heap)
    (registers : FusedWords addresses (Fused T fd) bound source.env target.env)
    (compatibleEnv : FusedCtorOk T (Fused T fd) source.env)
    (real : bound ≤ supOf fd) (done : FusedDone T fd block source)
    (pins : pinsApart T.known = true) (accepted : switchOk T alts default = true)
    {value : Own.RVal} (lookup : source.env.get? x = some value)
    {key : Key.CtorKey} {fields : List Own.RVal}
    (constructor : value.asCtor T.known heap = some (key, fields))
    {edge : Cfg.Edge} (selected : Cfg.selectEdge key alts default = some edge)
    (context : Lir.Word) (callers : List Lir.Frame) :
    (∃ F starts off C low pe le targetEnv,
      lp.funcs[source.fn]? = some F ∧ Lowered T source.fn fd F starts ∧
      starts.get? source.blk = some off ∧ Holds source.fn F off starts C ∧ off ≤ low ∧
      EdgeOk C source.fn edge pe ∧ edge.back = decide (edge.target ≤ source.blk) ∧
      resolveEdge source.fn off starts pe = .ok le ∧
      ReachesEdge lp source.fn F mem context callers low
        (Lir.atState mem context target.fn target.label target.pos target.env callers) le targetEnv ∧
      FusedWords addresses (Fused T fd) bound source.env targetEnv) ∨
    Sem.Fails (Lir.semStep lp)
      (Lir.atState mem context target.fn target.label target.pos target.env callers) := by
  obtain ⟨fd', block', F, starts, off, C, state, final, hfd, hb, hF, layout, start,
    held, lowering, extension, labels, opened, supply, _, fn, label, pos⟩ := cursor
  have sameFd : fd' = fd := Option.some.inj (hfd.symm.trans sourceLookup)
  subst fd'
  have sameBlock : block' = block := Option.some.inj (hb.symm.trans blockLookup)
  subst block'
  rw [finished] at lowering
  have code := rest_nil lowering
  cases fused : fusable T (useCounts fd) block with
  | some row =>
    obtain ⟨init, condition, left, right⟩ := row
    simp only [fused] at code
    rcases fused_switch hF held blockLookup fused finished done code labels opened
        (Grows.refl _) extension registers terminal lookup constructor selected with success | failure
    · obtain ⟨pe, le, targetEnv, edgeOk, back, resolved, reached, words⟩ := success
      refine .inl ⟨F, starts, off, C, off+state.cur, pe, le, targetEnv, hF, layout,
        start, held, Nat.le_add_right _ _, edgeOk, back, resolved, ?_, words⟩
      simpa only [fn, label, pos] using reached
    · exact .inr (by simpa only [fn, label, pos] using failure)
  | none =>
    simp only [fused, terminal, term] at code
    have materialized : ¬ Fused T fd x := by
      intro omitted
      have impossible := (fused_once omitted blockLookup).2 alts default terminal
      rw [fused] at impossible
      cases impossible
    have fresh : bound ≤ state.fresh := Nat.le_trans real supply
    have reaches : ∃ pe le targetEnv,
        EdgeOk C source.fn edge pe ∧ edge.back = decide (edge.target ≤ source.blk) ∧
        resolveEdge source.fn off starts pe = .ok le ∧
        ReachesEdge lp source.fn F mem context callers (off+state.cur)
          (Lir.atState mem context source.fn (off+state.cur) state.acc.length target.env callers)
          le targetEnv ∧ FusedWords addresses (Fused T fd) bound source.env targetEnv := by
      by_cases cell : ∃ location, value = .loc location
      · obtain ⟨location, rfl⟩ := cell
        exact dynamic_switch_checked hF held code labels opened (Grows.refl _) extension
          liveHeap registers fresh materialized lookup constructor selected compatibleHeap pins accepted
      · exact scalar_switch_checked hF held code labels opened (Grows.refl _) extension
          registers fresh materialized lookup constructor selected compatibleHeap pins accepted
          (compatibleEnv x value lookup materialized) (fun location equal => cell ⟨location, equal⟩)
    obtain ⟨pe, le, targetEnv, edgeOk, back, resolved, reached, words⟩ := reaches
    refine .inl ⟨F, starts, off, C, off+state.cur, pe, le, targetEnv, hF, layout,
      start, held, Nat.le_add_right _ _, edgeOk, back, resolved, ?_, words⟩
    simpa only [fn, label, pos] using reached


end IxCC.Cfg.Rc.Native.Spec
