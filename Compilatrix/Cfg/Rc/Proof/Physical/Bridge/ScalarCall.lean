import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.ScalarSem
import Compilatrix.Rt.Proof.OpsCall

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Proof.Physical.Bridge.Scalar
open Compilatrix Compilatrix.Rt Compilatrix.Rt.Proof Compilatrix.Rt.Lower
open Compilatrix.Rt.Rc.Procs
open Compilatrix.Lir (Word)
open Compilatrix.Src (NatMap)

theorem procCall_sim {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st : St} {x : Nat} {la lb : Lir.Arg} {as : List Fir.Arg} {g : Nat}
    {proc : Lir.Func} (hg : lp.funcs[g]? = some proc) (hparams : proc.params = [0, 1])
    (hC : Ext C { st with acc := [Lir.Stmt.call [x] g [la, lb]].reverse ++ st.acc, fresh := st.fresh })
    (ho : Open st) (hx : x < sup) (hops : operands f as = .ok (some [la, lb])) (hlive : ∀ a ∈ as, LiveArg D a)
    {op : Lam.Prim} (hop : op ≠ .natBeq ∧ op ≠ .natBle ∧ op ≠ .natBlt) (h : Nat → Nat → Nat)
    (hsem : ∀ p q, op.sem [p, q] = some (.nat (h p q)))
    (hspec : ∀ (mem : X86.Memory) (rest : List Lir.Frame) (p q : Nat) (wa wb : Word), natWord p = some wa →
      natWord q = some wb →
      ProcReturns lp g proc (Lir.atState mem ctx g 0 0 ((({} : Lir.Env).insert 0 wa).insert 1 wb) rest) mem ctx
          rest (fun w => natWord (h p q) = some w) ∨
        Sem.Fails (Lir.semStep lp) (Lir.atState mem ctx g 0 0 ((({} : Lir.Env).insert 0 wa).insert 1 wb) rest)) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st.cur)
      ([Lir.Stmt.call [x] g [la, lb]].reverse ++ st.acc).length x (.fir (.prim op as)) := by
  intro P H ρ ρl mem rest v H' hρ hr
  obtain ⟨rfl, ⟨p, q, n, wa, wb, ha, hb, hwa, hwb, hs, rfl, -, -⟩⟩ := bin2_of hρ hops hlive (sem_not_bool op hop) hr
  rw [hsem] at hs
  cases hs
  obtain ⟨lbk, post, hlb, -, hbody⟩ := holds_open hH [Lir.Stmt.call [x] g [la, lb]] st.fresh hC ho
  have hpos : st.acc.length < lbk.body.size := by
    rw [← Array.length_toList, hbody]; simp
  have hcall : lbk.body[st.acc.length] = .call [x] g [la, lb] := by
    rw [← Array.getElem_toList (h := hpos)]
    simp only [hbody]
    rw [List.getElem_append_left (by simp), List.getElem_append_right (by simp)]
    simp
  have hargs : Lir.evalArgs ρl [la, lb] = some [wa, wb] := by
    simp only [Lir.evalArgs_cons, Lir.evalArgs_nil, ha, hb, Option.bind_eq_bind, Option.bind_some]; rfl
  let cf : Lir.Frame := { fn, label := off + st.cur, pos := st.acc.length, env := ρl }
  have hstep := Lir.step_call (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (fr := cf) hF hlb hpos hcall
    hargs (enter_proc hg hparams wa wb)
  rcases hspec mem ({ cf with pos := cf.pos + 1, dsts := [x] } :: rest) p q wa wb hwa hwb with
    ⟨c, L, B, a, ρ', w, hB, hterm, hstar, hev, hw⟩ | hfail
  · have := call_proc (p := lp) (mem := mem) (ctx := ctx) (cf := cf) (rest := rest) (x := x) (w := w)
      (frEnd := { fn := g, label := L, pos := B.body.size, env := ρ' }) hstep hstar hg hB rfl hterm hev
    refine .inl ⟨1 + c + 0, ρl.insert x w, ?_, hρ.insert hx hw⟩
    simpa [cf] using this
  · exact .inr (fails_prepend (Lir.star_of_step hstep) hfail)

/-- **`natPow` simulates Cfg's**: a call of `rt_nat_pow`. -/
theorem prim_natPow {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) (hpow : lp.funcs[T.natPow]? = some Procs.natPow) {st st' : St} {x : Nat}
    {la lb : Lir.Arg} {as : List Fir.Arg}
    (hrun : (primitive f T x .natPow [la, lb]).run st = .ok ((), st')) (hC : Ext C st') (ho : Open st)
    (hx : x < sup) (hops : operands f as = .ok (some [la, lb])) (hlive : ∀ a ∈ as, LiveArg D a) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim .natPow as)) := by
  lower_run at hrun
  subst hrun
  exact procCall_sim hF hH hpow natPow_params hC ho hx hops hlive (by decide) (· ^ ·)
    (sem_nat2 .natPow (by decide)) (fun mem rest p q wa wb hwa hwb => natPow_spec hpow hwa hwb)

/-- **`natGcd` simulates Cfg's**: a call of `rt_nat_gcd`. -/
theorem prim_natGcd {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) (hgcd : lp.funcs[T.natGcd]? = some Procs.natGcd) {st st' : St} {x : Nat}
    {la lb : Lir.Arg} {as : List Fir.Arg}
    (hrun : (primitive f T x .natGcd [la, lb]).run st = .ok ((), st')) (hC : Ext C st') (ho : Open st)
    (hx : x < sup) (hops : operands f as = .ok (some [la, lb])) (hlive : ∀ a ∈ as, LiveArg D a) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim .natGcd as)) := by
  lower_run at hrun
  subst hrun
  exact procCall_sim hF hH hgcd natGcd_params hC ho hx hops hlive (by decide) Nat.gcd
    (sem_nat2 .natGcd (by decide)) (fun mem rest p q wa wb hwa hwb => .inl (natGcd_returns hgcd hwa hwb))


end Compilatrix.Cfg.Rc.Proof.Physical.Bridge.Scalar
