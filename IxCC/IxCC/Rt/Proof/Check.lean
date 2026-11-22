import IxCC.Rt.Proof.Ops

/-!
# Expansions that end their block with a check

`natAdd` (a carry), `natMul` and `natShl` (a computed overflow flag) and
the allocation (the limit) end the open block with a branch whose failing
edge goes to a new cold `fail` block, and continue in a new block. After
`lower_run`, the state such an expansion leaves has the shape `CheckSt`;
`check_code` reads the three blocks off the Lir function, and
`check_br_sim`/`check_ovf_sim` give `RhsSim` from the statements before
and after the check.
-/

set_option autoImplicit false

namespace IxCC.Rt.Proof

open IxCC.Lir (Word)
open IxCC.Rt.Lower
open IxCC.Src (NatMap)

/-- The state a checked expansion leaves: `ss1` and the check closed the
open block, the cold `fail r` block at `next`, the continuation at
`next + 1` holding `ss2`. -/
def CheckSt (st : St) (r : Sem.Resource) (ss1 ss2 : List Lir.Stmt) (t : PTerm) (f' : Nat) : St :=
  { done := (st.done.insert st.next { term := .fail r, cold := true }).insert st.cur
      { params := st.params, body := (ss1.reverse ++ st.acc).reverse, term := t },
    cur := st.next + 1, params := [], acc := ss2.reverse, next := st.next + 1 + 1, fresh := f' }

theorem check_code {f : Fir.FunId} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hH : Holds f F off starts C) {st : St} {r : Sem.Resource} {ss1 ss2 : List Lir.Stmt} {t : PTerm} {f' : Nat}
    (hC : Ext C (CheckSt st r ss1 ss2 t f')) (hl : Labels st) (ho : Open st) :
    (∃ lb, F.blocks[off + st.cur]? = some lb ∧ lb.body.toList = st.acc.reverse ++ ss1 ∧
      resolveTerm f off starts t = .ok lb.term) ∧
    F.blocks[off + st.next]? = some { term := .fail r, cold := true } ∧
    (∃ cb post, F.blocks[off + (st.next + 1)]? = some cb ∧ cb.params = [] ∧ cb.body.toList = ss2 ++ post) := by
  have hcur := hl.cur
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨lb, hres, hlb⟩ := hH (hC.done (j := st.cur)
      (b := { params := st.params, body := (ss1.reverse ++ st.acc).reverse, term := t })
      (by simp [CheckSt, NatMap.get?_insert]))
    obtain ⟨-, hbody, hterm⟩ := resolveBlock_ok hres
    exact ⟨lb, hlb, by rw [hbody]; simp, hterm⟩
  · obtain ⟨lb, hres, hlb⟩ := hH (hC.done (j := st.next) (b := { term := .fail r, cold := true }) (by
      simp only [CheckSt, NatMap.get?_insert]
      rw [if_neg (by omega)]
      simp))
    simp only [resolveBlock, resolveTerm, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hres
    rw [← hres] at hlb
    exact hlb
  · have hopen : Open (CheckSt st r ss1 ss2 t f') := by
      simp only [Open, CheckSt, NatMap.get?_insert]
      rw [if_neg (by omega), if_neg (by omega)]
      cases h : st.done.get? (st.next + 1) with
      | none => rfl
      | some b => have := hl.done h; omega
    obtain ⟨b, hb, hbp, hpre⟩ := hC.cur hopen
    obtain ⟨cb, hres, hcb⟩ := hH hb
    obtain ⟨hcp, hcbody, -⟩ := resolveBlock_ok hres
    obtain ⟨post, hpost⟩ := hpre
    refine ⟨cb, post, hcb, hcp.trans hbp, ?_⟩
    rw [hcbody, ← hpost]
    simp [CheckSt]

/-- A check by `br c a b bad ok`: the statements before it, the branch
(taken to the cold block when `c` holds), the statements after it. -/
theorem check_br_sim {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st : St} {r : Sem.Resource} {ss1 ss2 : List Lir.Stmt} {c : Lir.Cond}
    {ca cb : Lir.Arg} {f' : Nat}
    (hC : Ext C (CheckSt st r ss1 ss2 (.br c ca cb (loc st.next) (loc (st.next + 1))) f'))
    (hl : Labels st) (ho : Open st) (hnc1 : ∀ s ∈ ss1, s.isCall = false) (hnc2 : ∀ s ∈ ss2, s.isCall = false)
    {x : Nat} {rhs : Own.Rhs}
    (hsem : ∀ (P : List Word) (H : Own.Heap) (ρ : Own.Env) (ρl : Lir.Env) (mem : X86.Memory) (v : Own.RVal)
        (H' : Own.Heap), HeapInv T P H ctx mem → EnvRel T P D sup ρ ρl →
        Own.evalRhs .immortal (ownTables T) ρ H rhs = .ok (v, H') →
        ∃ ρl₁ mem₁ wa wb, Lir.execList ρl mem ctx ss1 = some (ρl₁, mem₁) ∧ ca.eval ρl₁ = some wa ∧
          cb.eval ρl₁ = some wb ∧
          (c.holds .w64 wa wb = false → ∃ ρl' mem' P', Lir.execList ρl₁ mem₁ ctx ss2 = some (ρl', mem') ∧
            HeapInv T P' H' ctx mem' ∧ P <+: P' ∧ EnvRel T P' D sup (ρ.insert x v) ρl')) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + (st.next + 1)) ss2.length x rhs := by
  obtain ⟨⟨lb, hlb, hbody, hterm⟩, hbad, ⟨cbk, post, hcb, hcp, hcbody⟩⟩ := check_code hH hC hl ho
  simp only [resolveTerm, resolveEdge, resolveTgt, loc, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hterm
  intro P H ρ ρl mem rest v H' hheap hρ hr
  obtain ⟨ρl₁, mem₁, wa, wb, hx1, hca, hcbv, hok⟩ := hsem P H ρ ρl mem v H' hheap hρ hr
  have h1 := Lir.stmts_at (p := lp) (ctx := ctx) (rest := rest) (pre := st.acc.reverse) (post := []) hF hlb
    (by simpa using hbody) hnc1 hx1
  simp only [List.length_reverse] at h1
  have hpos : st.acc.length + ss1.length = lb.body.size := by
    rw [← Array.length_toList, hbody]; simp
  cases hz : c.holds .w64 wa wb with
  | false =>
    obtain ⟨ρl', mem', P', hx2, hheap', hP, hρ'⟩ := hok hz
    have h2 := Lir.br_at (p := lp) (mem := mem₁) (ctx := ctx) (rest := rest) (ρ := ρl₁) (ρ' := ρl₁)
      (e := ⟨off + (st.next + 1), []⟩) (vals := []) (va := wa) (vb := wb) hF hlb hpos hterm.symm hca hcbv
      (by simp [hz]) rfl hcb (by simp [hcp, Lir.bindParams])
    have h3 := Lir.stmts_at (p := lp) (ctx := ctx) (rest := rest) (pre := []) (post := post) hF hcb
      (by simpa using hcbody) hnc2 hx2
    refine .inl ⟨_, ρl', mem', P', h1.trans ((Lir.star_of_step h2).trans (by simpa using h3)), hheap', hP, hρ'⟩
  | true =>
    have h2 := Lir.br_at (p := lp) (mem := mem₁) (ctx := ctx) (rest := rest) (ρ := ρl₁) (ρ' := ρl₁)
      (e := ⟨off + st.next, []⟩) (vals := []) (va := wa) (vb := wb) hF hlb hpos hterm.symm hca hcbv
      (by simp [hz]) rfl hbad rfl
    have h3 := Lir.fail_at (p := lp) (mem := mem₁) (ctx := ctx) (rest := rest) (pos := 0) (ρ := ρl₁) hF hbad rfl rfl
    exact .inr (Lir.fails_of_star (h1.trans (Lir.star_of_step h2)) h3)

/-- `natAdd`'s check: `brOvf addC x a b ok bad` binds `x` on both edges. -/
theorem check_ovf_sim {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st : St} {ss1 : List Lir.Stmt} {x : Nat} {ca cb : Lir.Arg} {f' : Nat}
    (hC : Ext C (CheckSt st .natOverflow ss1 [] (.brOvf .addC x ca cb (loc (st.next + 1)) (loc st.next)) f'))
    (hl : Labels st) (ho : Open st) (hnc1 : ∀ s ∈ ss1, s.isCall = false) {rhs : Own.Rhs}
    (hsem : ∀ (P : List Word) (H : Own.Heap) (ρ : Own.Env) (ρl : Lir.Env) (mem : X86.Memory) (v : Own.RVal)
        (H' : Own.Heap), HeapInv T P H ctx mem → EnvRel T P D sup ρ ρl →
        Own.evalRhs .immortal (ownTables T) ρ H rhs = .ok (v, H') →
        H' = H ∧ ∃ ρl₁ wa wb, Lir.execList ρl mem ctx ss1 = some (ρl₁, mem) ∧ ca.eval ρl₁ = some wa ∧
          cb.eval ρl₁ = some wb ∧
          (¬ (wa + wb < wa) → EnvRel T P D sup (ρ.insert x v) (ρl₁.insert x (wa + wb)))) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + (st.next + 1)) ([] : List Lir.Stmt).length x rhs := by
  obtain ⟨⟨lb, hlb, hbody, hterm⟩, hbad, ⟨cbk, post, hcb, hcp, -⟩⟩ := check_code hH hC hl ho
  simp only [resolveTerm, resolveEdge, resolveTgt, loc, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hterm
  intro P H ρ ρl mem rest v H' hheap hρ hr
  obtain ⟨rfl, ρl₁, wa, wb, hx1, hca, hcbv, hok⟩ := hsem P H ρ ρl mem v H' hheap hρ hr
  have h1 := Lir.stmts_at (p := lp) (ctx := ctx) (rest := rest) (pre := st.acc.reverse) (post := []) hF hlb
    (by simpa using hbody) hnc1 hx1
  simp only [List.length_reverse] at h1
  have hpos : st.acc.length + ss1.length = lb.body.size := by
    rw [← Array.length_toList, hbody]; simp
  by_cases hcar : wa + wb < wa
  · have h2 := Lir.brOvf_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρl₁)
      (ρ' := ρl₁.insert x (wa + wb)) (e := ⟨off + st.next, []⟩) (vals := []) (va := wa) (vb := wb) hF hlb hpos
      hterm.symm hca hcbv (by simp [Lir.Ovf.eval, hcar]) rfl hbad (by simp [Lir.Ovf.eval, Lir.bindParams])
    have h3 := Lir.fail_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (pos := 0)
      (ρ := ρl₁.insert x (wa + wb)) hF hbad rfl rfl
    exact .inr (Lir.fails_of_star (h1.trans (Lir.star_of_step h2)) h3)
  · have h2 := Lir.brOvf_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρl₁)
      (ρ' := ρl₁.insert x (wa + wb)) (e := ⟨off + (st.next + 1), []⟩) (vals := []) (va := wa) (vb := wb) hF hlb
      hpos hterm.symm hca hcbv (by simp [Lir.Ovf.eval, hcar]) rfl hcb
      (by simp [Lir.Ovf.eval, Lir.bindParams, hcp])
    exact .inl ⟨_, ρl₁.insert x (wa + wb), mem, P, h1.trans (Lir.star_of_step h2), hheap, List.prefix_refl _,
      hok hcar⟩

end IxCC.Rt.Proof
