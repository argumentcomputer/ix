import IxCC.Rt.Proof.Edge

/-!
# Test chains

`chain x tests els` closes the open block with `x = w₁ ? e₁ : next`, then
each next block with the following test, the last one's else-edge `els`.
`chainPick` is the edge the chain takes for a word of `x`: the first test
whose immediate equals it, else `els`; `chain_reaches` runs Lir through the
chain to the block that takes that edge (every step forward, into a label
allocated later). `chainOr` is a chain with a default edge, or else (no
default) with its last test untested.
-/

set_option autoImplicit false

namespace IxCC.Rt.Proof

open IxCC.Lir (Word)
open IxCC.Rt.Lower
open IxCC.Src (NatMap)

/-- An immediate operand's word. -/
def immOf : Lir.Arg → Option Word
  | .imm w => some w
  | .v _ => none

/-- The edge a chain takes for the word `wx`. -/
def chainPick (wx : Word) : List (Lir.Arg × PEdge) → PEdge → PEdge
  | [], els => els
  | (a, pe) :: rest, els => if immOf a = some wx then pe else chainPick wx rest els

/-- The state after one test of a chain: the test's block closed, the next
one open at a new label. -/
def chainSt (st : St) (x w : Lir.Arg) (e : PEdge) : St :=
  { closeSt { st with next := st.next + 1 } (.br .eq x w e (loc st.next)) with
    cur := st.next, params := [], acc := [] }

theorem chain_nil_run (st : St) (x : Lir.Arg) (els : PEdge) :
    (chain x [] els).run st = .ok ((), closeSt st (.jump els)) := rfl

theorem chain_one_run (st : St) (x w : Lir.Arg) (e els : PEdge) :
    (chain x [(w, e)] els).run st = .ok ((), closeSt st (.br .eq x w e els)) := rfl

theorem chain_cons_run (st : St) (x w : Lir.Arg) (e : PEdge) (t : Lir.Arg × PEdge) (rest : List (Lir.Arg × PEdge))
    (els : PEdge) : (chain x ((w, e) :: t :: rest) els).run st = (chain x (t :: rest) els).run (chainSt st x w e) :=
  rfl

/-! ## Closing and opening blocks -/

theorem grows_close {st : St} (ho : Open st) (t : PTerm) : Grows st (closeSt st t) where
  next := Nat.le_refl _
  fresh := Nat.le_refl _
  done {j b} h := by
    simp only [closeSt, NatMap.get?_insert]
    rw [if_neg (by intro e; subst e; rw [ho] at h; cases h)]
    exact h
  cur _ := .inr ⟨{ params := st.params, body := st.acc.reverse, term := t }, by simp [closeSt, NatMap.get?_insert],
    rfl, List.prefix_refl _⟩

theorem labels_close {st : St} (hl : Labels st) (t : PTerm) : Labels (closeSt st t) where
  cur := hl.cur
  done {j b} h := by
    simp only [closeSt, NatMap.get?_insert] at h
    split at h
    · rename_i hj; subst hj; exact hl.cur
    · exact hl.done h

theorem not_open_close (st : St) (t : PTerm) : ¬ Open (closeSt st t) := by
  simp [Open, closeSt, NatMap.get?_insert]

theorem grows_chainSt {st : St} (hl : Labels st) (ho : Open st) (x w : Lir.Arg) (e : PEdge) :
    Grows st (chainSt st x w e) where
  next := by simp [chainSt, closeSt]
  fresh := Nat.le_refl _
  done {j b} h := by
    simp only [chainSt, closeSt, NatMap.get?_insert]
    rw [if_neg (by intro e; subst e; rw [ho] at h; cases h)]
    exact h
  cur _ := .inr ⟨{ params := st.params, body := st.acc.reverse, term := .br .eq x w e (loc st.next) },
    by simp [chainSt, closeSt, NatMap.get?_insert], rfl, List.prefix_refl _⟩

theorem labels_chainSt {st : St} (hl : Labels st) (x w : Lir.Arg) (e : PEdge) : Labels (chainSt st x w e) where
  cur := by simp [chainSt, closeSt]
  done {j b} h := by
    simp only [chainSt, closeSt, NatMap.get?_insert] at h
    show j < st.next + 1
    split at h
    · have := hl.cur; omega
    · have := hl.done h; omega

theorem open_chainSt {st : St} (hl : Labels st) (x w : Lir.Arg) (e : PEdge) : Open (chainSt st x w e) := by
  simp only [Open, chainSt, closeSt, NatMap.get?_insert]
  rw [if_neg (by have := hl.cur; omega)]
  cases h : st.done.get? st.next with
  | none => rfl
  | some b => have := hl.done h; omega

/-! ## Chains -/

/-- A chain finishes every block it opens. -/
theorem chain_grows {x : Lir.Arg} {els : PEdge} :
    ∀ {tests : List (Lir.Arg × PEdge)} {st st' : St}, (chain x tests els).run st = .ok ((), st') → Labels st →
      Open st → Grows st st' ∧ Labels st' ∧ ¬ Open st' ∧ st'.fresh = st.fresh
  | [], st, st', h, hl, ho => by
    rw [chain_nil_run] at h
    cases h
    exact ⟨grows_close ho _, labels_close hl _, not_open_close _ _, rfl⟩
  | [(w, e)], st, st', h, hl, ho => by
    rw [chain_one_run] at h
    cases h
    exact ⟨grows_close ho _, labels_close hl _, not_open_close _ _, rfl⟩
  | (w, e) :: t :: rest, st, st', h, hl, ho => by
    rw [chain_cons_run] at h
    obtain ⟨hg, hl', ho', hf⟩ := chain_grows h (labels_chainSt hl x w e) (open_chainSt hl x w e)
    exact ⟨(grows_chainSt hl ho x w e).trans hg, hl', ho', hf⟩

/-- The labels a chain finishes: its first block's and new ones. -/
def NewKeys (st st' : St) : Prop :=
  ∀ {j : Nat} {b : PBlock}, st'.done.get? j = some b → st.done.get? j = some b ∨ j = st.cur ∨ st.next ≤ j

theorem chain_keys {x : Lir.Arg} {els : PEdge} :
    ∀ {tests : List (Lir.Arg × PEdge)} {st st' : St}, (chain x tests els).run st = .ok ((), st') →
      NewKeys st st'
  | [], st, st', h, j, b, hj => by
    rw [chain_nil_run] at h
    cases h
    simp only [closeSt, NatMap.get?_insert] at hj
    split at hj
    · exact .inr (.inl (by assumption))
    · exact .inl hj
  | [(w, e)], st, st', h, j, b, hj => by
    rw [chain_one_run] at h
    cases h
    simp only [closeSt, NatMap.get?_insert] at hj
    split at hj
    · exact .inr (.inl (by assumption))
    · exact .inl hj
  | (w, e) :: t :: rest, st, st', h, j, b, hj => by
    rw [chain_cons_run] at h
    rcases chain_keys h hj with hj | rfl | hj
    · simp only [chainSt, closeSt, NatMap.get?_insert] at hj
      split at hj
      · exact .inr (.inl (by assumption))
      · exact .inl hj
    · exact .inr (.inr (by simp [chainSt]))
    · exact .inr (.inr (by simp [chainSt, closeSt] at hj; omega))

theorem chainOr_keys {x : Lir.Arg} {tests : List (Lir.Arg × PEdge)} {dd : Option PEdge} {st st' : St}
    (h : (chainOr x tests dd).run st = .ok ((), st')) : NewKeys st st' := by
  cases dd with
  | some d => exact chain_keys h
  | none =>
    simp only [chainOr] at h
    split at h
    · exact chain_keys h
    · have : (close .trap).run st = .ok ((), closeSt st .trap) := rfl
      rw [this] at h
      cases h
      intro j b hj
      simp only [closeSt, NatMap.get?_insert] at hj
      split at hj
      · exact .inr (.inl (by assumption))
      · exact .inl hj

/-- **A chain takes `chainPick`'s edge.** -/
theorem chain_reaches {f : Fir.FunId} {lp : Lir.Program} {fn : Nat} {F : Lir.Func} {off : Nat}
    {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {mem : X86.Memory} {ctx : Word} {rest : List Lir.Frame} {x : Lir.Arg} {els : PEdge} {ρl : Lir.Env} {wx : Word}
    (hx : x.eval ρl = some wx) :
    ∀ {tests : List (Lir.Arg × PEdge)} {st st' stF : St}, (chain x tests els).run st = .ok ((), st') →
      Labels st → Open st → Grows st' stF → Ext C stF → (∀ t ∈ tests, ∃ w, t.1 = .imm w) →
      ∃ le, resolveEdge f off starts (chainPick wx tests els) = .ok le ∧
        ReachesEdge lp fn F mem ctx rest (off + st.cur)
          (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest) le ρl
  | [], st, st', stF, h, hl, ho, hg, hC, _ => by
    rw [chain_nil_run] at h
    cases h
    obtain ⟨lb, hlb, -, hsize, hterm⟩ := closed_block hH (close_ext hg hC)
    simp only [resolveTerm, bind, Except.bind] at hterm
    cases hle : resolveEdge f off starts els with
    | error err => simp [hle] at hterm
    | ok le =>
      simp only [hle, pure, Except.pure, Except.ok.injEq] at hterm
      refine ⟨le, hle, ?_⟩
      rw [← hsize]
      exact reachesEdge_jump hF hlb hterm.symm
  | [(w, e)], st, st', stF, h, hl, ho, hg, hC, himm => by
    rw [chain_one_run] at h
    cases h
    obtain ⟨wi, hwi⟩ := himm (w, e) (by simp)
    simp only at hwi
    subst hwi
    obtain ⟨lb, hlb, -, hsize, hterm⟩ := closed_block hH (close_ext hg hC)
    simp only [resolveTerm, bind, Except.bind] at hterm
    cases hle : resolveEdge f off starts e with
    | error err => simp [hle] at hterm
    | ok le =>
      cases hle' : resolveEdge f off starts els with
      | error err => simp [hle, hle'] at hterm
      | ok le' =>
        simp only [hle, hle', pure, Except.pure, Except.ok.injEq] at hterm
        have := reachesEdge_br (mem := mem) (ctx := ctx) (rest := rest) hF hlb hterm.symm hx rfl
        rw [hsize] at this
        refine ⟨if immOf (.imm wi) = some wx then le else le', ?_, ?_⟩
        · simp only [chainPick]
          split <;> assumption
        · have heq : (if Lir.Cond.holds .eq .w64 wx wi then le else le') =
              (if immOf (.imm wi) = some wx then le else le') := by
            by_cases hw : wi = wx
            · subst hw; simp [immOf, Lir.holds_eq]
            · simp [immOf, Lir.holds_eq, hw, Ne.symm hw]
          rw [← heq]
          exact this
  | (w, e) :: t :: tests, st, st', stF, h, hl, ho, hg, hC, himm => by
    rw [chain_cons_run] at h
    have hl₂ := labels_chainSt hl x w e
    have ho₂ := open_chainSt hl x w e
    obtain ⟨hg₂, -, -, -⟩ := chain_grows h hl₂ ho₂
    obtain ⟨wi, hwi⟩ := himm (w, e) (by simp)
    simp only at hwi
    subst hwi
    -- the test's block
    have hCt : C[st.cur]? = some
        { params := st.params, body := st.acc.reverse, term := .br .eq x (.imm wi) e (loc st.next) } :=
      hC.done ((hg₂.trans hg).done (by simp [chainSt, closeSt, NatMap.get?_insert]))
    obtain ⟨lb, hlb, -, hsize, hterm⟩ := closed_block hH hCt
    simp only [resolveTerm, bind, Except.bind] at hterm
    cases hle : resolveEdge f off starts e with
    | error err => simp [hle] at hterm
    | ok le =>
      simp only [hle] at hterm
      simp only [resolveEdge, resolveTgt, loc, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hterm
      by_cases hw : wi = wx
      · subst hw
        refine ⟨le, by simp [chainPick, immOf, hle], ?_⟩
        have := reachesEdge_br (mem := mem) (ctx := ctx) (rest := rest) hF hlb hterm.symm hx rfl
        rw [hsize] at this
        simpa [Lir.holds_eq] using this
      · obtain ⟨le', hle', hreach⟩ := chain_reaches hF hH hx h hl₂ ho₂ hg hC
          (fun t' ht' => himm t' (List.mem_cons_of_mem _ ht'))
        refine ⟨le', by simpa [chainPick, immOf, hw] using hle', ?_⟩
        -- the test fails: on to the next block, at a later label
        obtain ⟨b₂, hb₂, hp₂, -⟩ := (Grows.ext (hg₂.trans hg) hC).cur ho₂
        obtain ⟨lb₂, hres₂, hlb₂⟩ := hH hb₂
        obtain ⟨hp₂', -, -⟩ := resolveBlock_ok hres₂
        have hstep := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρl)
          (e := { target := off + st.next, args := [] }) (vals := []) (ρ' := ρl) hF hlb hsize.symm hterm.symm hx
          rfl (by simp [Lir.holds_eq, Ne.symm hw]) rfl (by simpa [chainSt] using hlb₂)
          (by simp [hp₂', hp₂, chainSt, Lir.bindParams])
        have hcur : st.cur < st.next := hl.cur
        refine hreach.prepend (Lir.star_of_step hstep) (by simp [chainSt]; omega)

/-! ## Chains with a default -/

/-- The last element and the ones before it. -/
theorem unsnoc_eq {α : Type} : ∀ {l : List α} {init : List α} {last : α}, unsnoc l = some (init, last) →
    l = init ++ [last]
  | [a], init, last, h => by simp [unsnoc] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | a :: b :: l, init, last, h => by
    simp only [unsnoc, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨i, la⟩, hu, rfl, rfl⟩ := h
    rw [unsnoc_eq hu]
    rfl
  | [], _, _, h => by simp [unsnoc] at h

theorem unsnoc_none {α : Type} : ∀ {l : List α}, unsnoc l = none → l = []
  | [], _ => rfl
  | [a], h => by simp [unsnoc] at h
  | a :: b :: l, h => by
    simp only [unsnoc, Option.map_eq_none_iff] at h
    exact absurd (unsnoc_none h) (by simp)

/-- The edge `chainOr` takes: `none` for its `trap` (no tests, no default). -/
def chainOrPick (wx : Word) (tests : List (Lir.Arg × PEdge)) : Option PEdge → Option PEdge
  | some d => some (chainPick wx tests d)
  | none =>
    match unsnoc tests with
    | some (init, (_, last)) => some (chainPick wx init last)
    | none => none

theorem chainOr_grows {x : Lir.Arg} {tests : List (Lir.Arg × PEdge)} {dd : Option PEdge} {st st' : St}
    (h : (chainOr x tests dd).run st = .ok ((), st')) (hl : Labels st) (ho : Open st) :
    Grows st st' ∧ Labels st' ∧ ¬ Open st' ∧ st'.fresh = st.fresh := by
  cases dd with
  | some d => exact chain_grows h hl ho
  | none =>
    simp only [chainOr] at h
    split at h
    · exact chain_grows h hl ho
    · have : (close .trap).run st = .ok ((), closeSt st .trap) := rfl
      rw [this] at h
      cases h
      exact ⟨grows_close ho _, labels_close hl _, not_open_close _ _, rfl⟩

/-- **`chainOr` takes `chainOrPick`'s edge**, or traps where it has none. -/
theorem chainOr_reaches {f : Fir.FunId} {lp : Lir.Program} {fn : Nat} {F : Lir.Func} {off : Nat}
    {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {mem : X86.Memory} {ctx : Word} {rest : List Lir.Frame} {x : Lir.Arg} {ρl : Lir.Env} {wx : Word}
    (hx : x.eval ρl = some wx) {tests : List (Lir.Arg × PEdge)} {dd : Option PEdge} {st st' stF : St}
    (h : (chainOr x tests dd).run st = .ok ((), st')) (hl : Labels st) (ho : Open st) (hg : Grows st' stF)
    (hC : Ext C stF) (himm : ∀ t ∈ tests, ∃ w, t.1 = .imm w) {pe : PEdge} (hpick : chainOrPick wx tests dd = some pe) :
    ∃ le, resolveEdge f off starts pe = .ok le ∧
      ReachesEdge lp fn F mem ctx rest (off + st.cur) (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest) le ρl := by
  cases dd with
  | some d =>
    simp only [chainOrPick, Option.some.injEq] at hpick
    subst hpick
    exact chain_reaches hF hH hx h hl ho hg hC himm
  | none =>
    simp only [chainOrPick] at hpick
    simp only [chainOr] at h
    cases hu : unsnoc tests with
    | none => simp [hu] at hpick
    | some p =>
      obtain ⟨init, a, last⟩ := p
      simp only [hu, Option.some.injEq] at hpick h
      subst hpick
      have := unsnoc_eq hu
      exact chain_reaches hF hH hx h hl ho hg hC (fun t ht => himm t (by rw [this]; simp [ht]))

end IxCC.Rt.Proof
