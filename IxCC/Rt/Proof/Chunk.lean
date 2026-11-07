import IxCC.Rt.Lower
import IxCC.Src.Proof.NatMap
import IxCC.Lir.Proof.Eval

/-!
# Chunks under construction

`Rt.lower` builds each Cfg block's chunk in the state monad `Lower.M` over
`Lower.St`: finished blocks by local label (`done`), the open block (`cur`,
its parameters and body so far, reversed), the next free label and the next
free register. This module relates a state to the chunk the lowering
finally produces:

* `Ext C st`: the final chunk `C` contains every finished block of `st`
  and, if `st`'s block is open, a block at `cur` with `st`'s parameters
  whose body starts with what `st` has emitted;
* `Grows st st'`: `st'` comes later in the same construction (labels and
  registers only grow, finished blocks stay, and the open block is either
  still open with a longer body or finished with that body as a prefix), so
  `Ext C st' → Ext C st`;
* `Labels st`: `cur` and every finished label are below `next`.

Each action of the lowering monad gets a `run` equation (computed by
`rfl`) and these facts; `Holds` then reads a chunk off the Lir function at
its offset, so a position `(off + st.cur, st.acc.length)` of the Lir
function is where the code `st` will go on to emit starts.
-/

set_option autoImplicit false

namespace IxCC.Rt.Proof

open IxCC.Rt.Lower
open IxCC.Src (NatMap)

/-- `st`'s block is still open. -/
def Open (st : St) : Prop := st.done.get? st.cur = none

structure Labels (st : St) : Prop where
  cur : st.cur < st.next
  done : ∀ {j : Nat} {b : PBlock}, st.done.get? j = some b → j < st.next

structure Ext (C : List PBlock) (st : St) : Prop where
  done : ∀ {j : Nat} {b : PBlock}, st.done.get? j = some b → C[j]? = some b
  cur : Open st → ∃ b, C[st.cur]? = some b ∧ b.params = st.params ∧ st.acc.reverse <+: b.body

structure Grows (st st' : St) : Prop where
  next : st.next ≤ st'.next
  fresh : st.fresh ≤ st'.fresh
  done : ∀ {j : Nat} {b : PBlock}, st.done.get? j = some b → st'.done.get? j = some b
  cur : Open st →
    (st'.cur = st.cur ∧ Open st' ∧ st'.params = st.params ∧ st.acc.reverse <+: st'.acc.reverse) ∨
    (∃ b, st'.done.get? st.cur = some b ∧ b.params = st.params ∧ st.acc.reverse <+: b.body)

namespace Grows

theorem refl (st : St) : Grows st st where
  next := Nat.le_refl _
  fresh := Nat.le_refl _
  done h := h
  cur h := .inl ⟨rfl, h, rfl, List.prefix_refl _⟩

theorem trans {st st' st'' : St} (h : Grows st st') (h' : Grows st' st'') : Grows st st'' where
  next := Nat.le_trans h.next h'.next
  fresh := Nat.le_trans h.fresh h'.fresh
  done hj := h'.done (h.done hj)
  cur ho := by
    rcases h.cur ho with ⟨hc, ho', hp, hpre⟩ | ⟨b, hb, hp, hpre⟩
    · rcases h'.cur ho' with ⟨hc', ho'', hp', hpre'⟩ | ⟨b, hb, hp', hpre'⟩
      · exact .inl ⟨hc'.trans hc, ho'', hp'.trans hp, hpre.trans hpre'⟩
      · exact .inr ⟨b, hc ▸ hb, hp'.trans hp, hpre.trans hpre'⟩
    · exact .inr ⟨b, h'.done hb, hp, hpre⟩

theorem ext {st st' : St} (h : Grows st st') {C : List PBlock} (hC : Ext C st') : Ext C st where
  done hj := hC.done (h.done hj)
  cur ho := by
    rcases h.cur ho with ⟨hc, ho', hp, hpre⟩ | ⟨b, hb, hp, hpre⟩
    · obtain ⟨b, hb, hbp, hbpre⟩ := hC.cur ho'
      exact ⟨b, hc ▸ hb, hbp.trans hp, hpre.trans hbpre⟩
    · exact ⟨b, hC.done hb, hp, hpre⟩

end Grows

/-! ## Run equations of the actions -/

section run

variable (st : St)

theorem emit_run (s : Lir.Stmt) : (emit s).run st = .ok ((), { st with acc := s :: st.acc }) := rfl

theorem assign_run (x : Lir.VReg) (r : Lir.Rhs) :
    (assign x r).run st = .ok ((), { st with acc := .assign x r :: st.acc }) := rfl

theorem temp_run (r : Lir.Rhs) :
    (temp r).run st = .ok (.v st.fresh, { st with fresh := st.fresh + 1, acc := .assign st.fresh r :: st.acc }) :=
  rfl

theorem bin_run (o : Lir.BinOp) (a b : Lir.Arg) :
    (bin o a b).run st =
      .ok (.v st.fresh, { st with fresh := st.fresh + 1, acc := .assign st.fresh (.bin o .w64 a b) :: st.acc }) :=
  rfl

theorem untag_imm_run (w : Lir.Word) : (untag (.imm w)).run st = .ok (.imm (w >>> 1), st) := rfl

theorem untag_v_run (y : Lir.VReg) :
    (untag (.v y)).run st =
      .ok (.v st.fresh, { st with
        fresh := st.fresh + 1, acc := .assign st.fresh (.bin .shr .w64 (.v y) (.imm 1)) :: st.acc }) := rfl

theorem close_run (t : PTerm) :
    (close t).run st = .ok ((), { st with
      done := st.done.insert st.cur { params := st.params, body := st.acc.reverse, term := t },
      params := [], acc := [] }) := rfl

theorem openAt_run (l : Nat) (ps : List Lir.VReg) :
    (openAt l ps).run st = .ok ((), { st with cur := l, params := ps, acc := [] }) := rfl

theorem newLabel_run : newLabel.run st = .ok (st.next, { st with next := st.next + 1 }) := rfl

theorem coldBlock_run (t : PTerm) :
    (coldBlock t).run st = .ok (st.next, { st with
      done := st.done.insert st.next { term := t, cold := true }, next := st.next + 1 }) := rfl

/-- The state after a check: the failing edge to a new cold block, the
current block closed, continuing in a new block. -/
def checkSt (r : Sem.Resource) (mk : PEdge → PEdge → PTerm) : St :=
  { done := (st.done.insert st.next { term := .fail r, cold := true }).insert st.cur
      { params := st.params, body := st.acc.reverse, term := mk (loc (st.next + 1)) (loc st.next) },
    cur := st.next + 1, params := [], acc := [], next := st.next + 2, fresh := st.fresh }

theorem check_run (r : Sem.Resource) (mk : PEdge → PEdge → PTerm) :
    (check r mk).run st = .ok ((), checkSt st r mk) := rfl

end run

/-! ## Facts of the actions -/

/-- Emitting statements keeps the block open and extends it. -/
theorem grows_acc {st : St} (ss : List Lir.Stmt) (f : Nat) (hf : st.fresh ≤ f) :
    Grows st { st with acc := ss ++ st.acc, fresh := f } where
  next := Nat.le_refl _
  fresh := hf
  done h := h
  cur ho := .inl ⟨rfl, ho, rfl, by simp⟩

theorem labels_acc {st : St} (ss : List Lir.Stmt) (f : Nat) (h : Labels st) :
    Labels { st with acc := ss ++ st.acc, fresh := f } :=
  { cur := h.cur, done := h.done }

theorem open_acc {st : St} (ss : List Lir.Stmt) (f : Nat) (h : Open st) :
    Open { st with acc := ss ++ st.acc, fresh := f } := h

/-- A check finishes the open block and the cold block, and opens the
continuation. -/
theorem grows_check {st : St} (hl : Labels st) (ho : Open st) (r : Sem.Resource) (mk : PEdge → PEdge → PTerm) :
    Grows st (checkSt st r mk) where
  next := by simp [checkSt]
  fresh := Nat.le_refl _
  done {j b} h := by
    have := hl.done h
    simp only [checkSt, NatMap.get?_insert]
    rw [if_neg (by intro e; subst e; rw [ho] at h; cases h), if_neg (by omega)]
    exact h
  cur _ := .inr ⟨{ params := st.params, body := st.acc.reverse, term := mk (loc (st.next + 1)) (loc st.next) },
    by simp [checkSt, NatMap.get?_insert], rfl, List.prefix_refl _⟩

theorem labels_check {st : St} (hl : Labels st) (r : Sem.Resource) (mk : PEdge → PEdge → PTerm) :
    Labels (checkSt st r mk) where
  cur := by simp [checkSt]
  done {j b} h := by
    show j < st.next + 2
    simp only [checkSt, NatMap.get?_insert] at h
    split at h
    · have := hl.cur; omega
    · split at h
      · omega
      · have := hl.done h; omega

theorem open_check {st : St} (hl : Labels st) (r : Sem.Resource) (mk : PEdge → PEdge → PTerm) :
    Open (checkSt st r mk) := by
  simp only [Open, checkSt, NatMap.get?_insert]
  rw [if_neg (by have := hl.cur; omega), if_neg (by omega)]
  cases h : st.done.get? (st.next + 1) with
  | none => rfl
  | some b => have := hl.done h; omega

/-- What a check leaves in the final chunk: the closed block at `cur`, the
cold block, and the open continuation. -/
theorem ext_check {st : St} {C : List PBlock} {r : Sem.Resource} {mk : PEdge → PEdge → PTerm}
    (hC : Ext C (checkSt st r mk)) (hl : Labels st) :
    C[st.cur]? = some { params := st.params, body := st.acc.reverse, term := mk (loc (st.next + 1)) (loc st.next) } ∧
      C[st.next]? = some { term := .fail r, cold := true } ∧
      (Open (checkSt st r mk) → ∃ b, C[st.next + 1]? = some b ∧ b.params = []) := by
  refine ⟨hC.done (by simp [checkSt, NatMap.get?_insert]), hC.done ?_, fun ho => ?_⟩
  · simp only [checkSt, NatMap.get?_insert]
    rw [if_neg (by have := hl.cur; omega)]
    simp
  · obtain ⟨b, hb, hp, -⟩ := hC.cur ho
    exact ⟨b, hb, hp⟩

/-! ## Chunks in the Lir function -/

/-- The Lir function `F` holds chunk `C` at `off`, resolved against
`starts`. -/
def Holds (f : Fir.FunId) (F : Lir.Func) (off : Nat) (starts : NatMap Nat) (C : List PBlock) : Prop :=
  ∀ {j : Nat} {b : PBlock}, C[j]? = some b → ∃ lb, resolveBlock f off starts b = .ok lb ∧ F.blocks[off + j]? = some lb

theorem resolveBlock_ok {f off : Nat} {starts : NatMap Nat} {b : PBlock} {lb : Lir.Block}
    (h : resolveBlock f off starts b = .ok lb) :
    lb.params = b.params ∧ lb.body.toList = b.body ∧ resolveTerm f off starts b.term = .ok lb.term := by
  unfold resolveBlock at h
  cases ht : resolveTerm f off starts b.term with
  | error e => simp [ht, bind, Except.bind] at h
  | ok t =>
    simp only [ht, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, by simp, rfl⟩

/-- The open block of `st` in the Lir function: its body starts with what
`st` has emitted, then `ss`. -/
theorem holds_open {f off : Nat} {F : Lir.Func} {starts : NatMap Nat} {C : List PBlock} (hH : Holds f F off starts C)
    {st : St} (ss : List Lir.Stmt) (f' : Nat)
    (hC : Ext C { st with acc := ss.reverse ++ st.acc, fresh := f' }) (ho : Open st) :
    ∃ lb post, F.blocks[off + st.cur]? = some lb ∧ lb.params = st.params ∧
      lb.body.toList = st.acc.reverse ++ ss ++ post := by
  obtain ⟨b, hb, hp, hpre⟩ := hC.cur ho
  obtain ⟨lb, hres, hF⟩ := hH hb
  obtain ⟨hlp, hlb, -⟩ := resolveBlock_ok hres
  obtain ⟨post, hpost⟩ := hpre
  refine ⟨lb, post, hF, hlp.trans hp, ?_⟩
  rw [hlb, ← hpost]
  simp

end IxCC.Rt.Proof
