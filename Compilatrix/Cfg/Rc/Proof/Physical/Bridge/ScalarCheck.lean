import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.ScalarSem
import Compilatrix.Rt.Proof.Check

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Proof.Physical.Bridge.Scalar
open Compilatrix Compilatrix.Rt Compilatrix.Rt.Proof Compilatrix.Rt.Lower
open Compilatrix.Rt.Rc.Procs
open Compilatrix.Lir (Word)
open Compilatrix.Src (NatMap)

theorem check_br_sim {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st : St} {r : Sem.Resource} {ss1 ss2 : List Lir.Stmt} {c : Lir.Cond}
    {ca cb : Lir.Arg} {f' : Nat}
    (hC : Ext C (CheckSt st r ss1 ss2 (.br c ca cb (loc st.next) (loc (st.next + 1))) f'))
    (hl : Labels st) (ho : Open st) (hnc1 : ∀ s ∈ ss1, s.isCall = false) (hnc2 : ∀ s ∈ ss2, s.isCall = false)
    {x : Nat} {rhs : Own.Rhs}
    (hsem : ∀ (P : AddressMap) (H : Own.Heap) (ρ : Own.Env) (ρl : Lir.Env) (mem : X86.Memory) (v : Own.RVal)
        (H' : Own.Heap), EnvRel T P D sup ρ ρl →
        Own.evalRhs .rc (ownTables T) ρ H rhs = .ok (v, H') →
        ∃ ρl₁ wa wb, Lir.execList ρl mem ctx ss1 = some (ρl₁, mem) ∧ ca.eval ρl₁ = some wa ∧
          cb.eval ρl₁ = some wb ∧
          (c.holds .w64 wa wb = false → ∃ ρl', Lir.execList ρl₁ mem ctx ss2 = some (ρl', mem) ∧
            EnvRel T P D sup (ρ.insert x v) ρl')) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + (st.next + 1)) ss2.length x rhs := by
  obtain ⟨⟨lb, hlb, hbody, hterm⟩, hbad, ⟨cbk, post, hcb, hcp, hcbody⟩⟩ := check_code hH hC hl ho
  simp only [resolveTerm, resolveEdge, resolveTgt, loc, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hterm
  intro P H ρ ρl mem rest v H' hρ hr
  obtain ⟨ρl₁, wa, wb, hx1, hca, hcbv, hok⟩ := hsem P H ρ ρl mem v H' hρ hr
  have h1 := Lir.stmts_at (p := lp) (ctx := ctx) (rest := rest) (pre := st.acc.reverse) (post := []) hF hlb
    (by simpa using hbody) hnc1 hx1
  simp only [List.length_reverse] at h1
  have hpos : st.acc.length + ss1.length = lb.body.size := by
    rw [← Array.length_toList, hbody]; simp
  cases hz : c.holds .w64 wa wb with
  | false =>
    obtain ⟨ρl', hx2, hρ'⟩ := hok hz
    have h2 := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρl₁) (ρ' := ρl₁)
      (e := ⟨off + (st.next + 1), []⟩) (vals := []) (va := wa) (vb := wb) hF hlb hpos hterm.symm hca hcbv
      (by simp [hz]) rfl hcb (by simp [hcp, Lir.bindParams])
    have h3 := Lir.stmts_at (p := lp) (ctx := ctx) (rest := rest) (pre := []) (post := post) hF hcb
      (by simpa using hcbody) hnc2 hx2
    refine .inl ⟨_, ρl', h1.trans ((Lir.star_of_step h2).trans (by simpa using h3)), hρ'⟩
  | true =>
    have h2 := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρl₁) (ρ' := ρl₁)
      (e := ⟨off + st.next, []⟩) (vals := []) (va := wa) (vb := wb) hF hlb hpos hterm.symm hca hcbv
      (by simp [hz]) rfl hbad rfl
    have h3 := Lir.fail_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (pos := 0) (ρ := ρl₁) hF hbad rfl rfl
    exact .inr (Lir.fails_of_star (h1.trans (Lir.star_of_step h2)) h3)

/-- `natAdd`'s check: `brOvf addC x a b ok bad` binds `x` on both edges. -/
theorem check_ovf_sim {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st : St} {ss1 : List Lir.Stmt} {x : Nat} {ca cb : Lir.Arg} {f' : Nat}
    (hC : Ext C (CheckSt st .natOverflow ss1 [] (.brOvf .addC x ca cb (loc (st.next + 1)) (loc st.next)) f'))
    (hl : Labels st) (ho : Open st) (hnc1 : ∀ s ∈ ss1, s.isCall = false) {rhs : Own.Rhs}
    (hsem : ∀ (P : AddressMap) (H : Own.Heap) (ρ : Own.Env) (ρl : Lir.Env) (mem : X86.Memory) (v : Own.RVal)
        (H' : Own.Heap), EnvRel T P D sup ρ ρl →
        Own.evalRhs .rc (ownTables T) ρ H rhs = .ok (v, H') →
        H' = H ∧ ∃ ρl₁ wa wb, Lir.execList ρl mem ctx ss1 = some (ρl₁, mem) ∧ ca.eval ρl₁ = some wa ∧
          cb.eval ρl₁ = some wb ∧
          (¬ (wa + wb < wa) → EnvRel T P D sup (ρ.insert x v) (ρl₁.insert x (wa + wb)))) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + (st.next + 1)) ([] : List Lir.Stmt).length x rhs := by
  obtain ⟨⟨lb, hlb, hbody, hterm⟩, hbad, ⟨cbk, post, hcb, hcp, -⟩⟩ := check_code hH hC hl ho
  simp only [resolveTerm, resolveEdge, resolveTgt, loc, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hterm
  intro P H ρ ρl mem rest v H' hρ hr
  obtain ⟨rfl, ρl₁, wa, wb, hx1, hca, hcbv, hok⟩ := hsem P H ρ ρl mem v H' hρ hr
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
    exact .inl ⟨_, ρl₁.insert x (wa + wb), h1.trans (Lir.star_of_step h2), hok hcar⟩


end Compilatrix.Cfg.Rc.Proof.Physical.Bridge.Scalar
