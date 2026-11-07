import IxCC.Cfg.Rc.Proof.Physical.SwitchCursor
import IxCC.Cfg.Rc.Proof.Native.FrameState

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Rt.Proof IxCC.Rt.Lower
open IxCC.Rt.Rc.Procs

theorem ConsumedCursor.switch_reaches {P : Program} {pairs : List (Nat × Cfg.Fun)}
    (consuming : consumeAll P = .ok pairs) (switches : Rt.checkSwitches P.base = .ok ())
    {lp : Lir.Program} {source : Cfg.Frame} {target : Lir.Frame}
    {addresses : AddressMap} {heap : Own.Heap} {bound : Nat} {actual fd : Cfg.Fun}
    (frame : FrameState P pairs lp addresses heap.size bound actual source target)
    (range : source.fn < P.base.size) (sourceLookup : P.base.fun? source.fn = some fd)
    {block : Cfg.Block} (blockLookup : fd.blocks[source.blk]? = some block)
    (finished : source.rest = []) {x : Nat} {alts : List (Key.CtorKey × Cfg.Edge)}
    {default : Option Cfg.Edge} (terminal : block.term = .switch x alts default)
    {mem : X86.Memory} (liveHeap : HeapLive heap addresses mem)
    (compatibleHeap : HeapCtorOk (tablesOf P pairs) heap) (real : bound ≤ supOf actual)
    (done : ∀ block, actual.blocks[source.blk]? = some block →
      FusedDone (tablesOf P pairs) actual block source)
    {value : Own.RVal} (lookup : source.env.get? x = some value)
    {key : Key.CtorKey} {fields : List Own.RVal}
    (constructor : value.asCtor (tablesOf P pairs).known heap = some (key, fields))
    {edge : Cfg.Edge} (selected : Cfg.selectEdge key alts default = some edge)
    (context : Lir.Word) (callers : List Lir.Frame) :
    (∃ F starts off C low pe le targetEnv,
      lp.funcs[source.fn]? = some F ∧ Lowered (tablesOf P pairs) source.fn actual F starts ∧
      starts.get? source.blk = some off ∧ Holds source.fn F off starts C ∧ off ≤ low ∧
      EdgeOk C source.fn edge pe ∧ edge.back = decide (edge.target ≤ source.blk) ∧
      resolveEdge source.fn off starts pe = .ok le ∧
      ReachesEdge lp source.fn F mem context callers low
        (Lir.atState mem context target.fn target.label target.pos target.env callers) le targetEnv ∧
      FusedWords addresses (Fused (tablesOf P pairs) actual) bound source.env targetEnv) ∨
    Sem.Fails (Lir.semStep lp)
      (Lir.atState mem context target.fn target.label target.pos target.env callers) := by
  obtain ⟨original, consumedFd, originalLookup, receipt, consumedLookup⟩ := consumed_entry consuming range
  have sameSource : original = fd := Option.some.inj (originalLookup.symm.trans sourceLookup)
  subst original
  have sameTarget : consumedFd = actual := Option.some.inj (consumedLookup.symm.trans frame.lookup)
  subst consumedFd
  obtain ⟨body, _, actualBlock⟩ := (consumeFunction_parts receipt).2.2.2.2.2 blockLookup
  obtain ⟨rest, consumeRest, position⟩ := frame.cursor
  rw [finished] at consumeRest
  simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at consumeRest
  subst rest
  have cursor : Cursor (tablesOf P pairs) (consumed P pairs) lp source target := by
    have equal : {source with rest := []} = source := by cases source; simp_all
    rw [equal] at position
    exact position
  have admitted := admitted_switch_checks pairs switches sourceLookup blockLookup terminal
  exact cursor.switch_reaches frame.lookup actualBlock finished terminal liveHeap compatibleHeap
    frame.words frame.compatible real (done _ actualBlock) admitted.1 admitted.2 lookup constructor selected context callers


end IxCC.Cfg.Rc.Native.Spec
