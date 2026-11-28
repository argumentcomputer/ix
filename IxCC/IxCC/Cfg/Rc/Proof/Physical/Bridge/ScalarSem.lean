import IxCC.Cfg.Rc.Proof.Physical.Bridge.ScalarEnv
import IxCC.Rt.Proof.Ops

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
open IxCC IxCC.Rt IxCC.Rt.Proof IxCC.Rt.Lower
open IxCC.Rt.Rc.Procs
open IxCC.Lir (Word)
open IxCC.Src (NatMap)

/-- Scalar expansion with unchanged actual memory and current dynamic
addresses. The full caller stack is preserved, including procedure calls.
Source heap equality follows separately from the actual pure RHS effect. -/
def RhsSim (T : Tables) (lp : Lir.Program) (ctx : Word) (D : Nat → Prop) (sup : Nat)
    (fn L p L' p' x : Nat) (r : Own.Rhs) : Prop :=
  ∀ (P : AddressMap) (H : Own.Heap) (ρ : Own.Env) (ρl : Lir.Env) (mem : X86.Memory)
    (rest : List Lir.Frame) (v : Own.RVal) (H' : Own.Heap),
    EnvRel T P D sup ρ ρl →
    Own.evalRhs .rc (ownTables T) ρ H r = .ok (v, H') →
    (∃ charge after, Sem.Star (Lir.semStep lp) (Lir.atState mem ctx fn L p ρl rest) charge
      (Lir.atState mem ctx fn L' p' after rest) ∧ EnvRel T P D sup (ρ.insert x v) after) ∨
    Sem.Fails (Lir.semStep lp) (Lir.atState mem ctx fn L p ρl rest)

theorem straight_sim {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st : St} {ss : List Lir.Stmt} {f' : Nat}
    (hC : Ext C { st with acc := ss.reverse ++ st.acc, fresh := f' }) (ho : Open st)
    (hnc : ∀ s ∈ ss, s.isCall = false) {x : Nat} {r : Own.Rhs}
    (hsem : ∀ (P : AddressMap) (H : Own.Heap) (ρ : Own.Env) (ρl : Lir.Env) (mem : X86.Memory) (v : Own.RVal)
        (H' : Own.Heap), EnvRel T P D sup ρ ρl → Own.evalRhs .rc (ownTables T) ρ H r = .ok (v, H') →
        H' = H ∧ ∃ ρl', Lir.execList ρl mem ctx ss = some (ρl', mem) ∧ EnvRel T P D sup (ρ.insert x v) ρl') :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st.cur) (ss.reverse ++ st.acc).length x r := by
  intro P H ρ ρl mem rest v H' hρ hr
  obtain ⟨rfl, ρl', hx, hρ'⟩ := hsem P H ρ ρl mem v H' hρ hr
  exact .inl ⟨0, ρl', straight_star hF hH hC ho hnc hx, hρ'⟩

theorem bin2_of {T : Tables} {P : AddressMap} {D : Nat → Prop} {sup : Nat} {ρ : Own.Env} {ρl : Lir.Env}
    (hρ : EnvRel T P D sup ρ ρl) {f : Fir.FunId} {as : List Fir.Arg} {la lb : Lir.Arg}
    (hops : operands f as = .ok (some [la, lb])) (hlive : ∀ a ∈ as, LiveArg D a) {op : Lam.Prim}
    (hop : ∀ ns b, op.sem ns ≠ some (.bool b)) {H H' : Own.Heap} {v : Own.RVal}
    (hr : Own.evalRhs .rc (ownTables T) ρ H (.fir (.prim op as)) = .ok (v, H')) :
    H' = H ∧ Bin2 T [] sup ρl op la lb v := by
  obtain ⟨rfl, vs, hvs, hres⟩ := evalRhs_prim hr
  obtain ⟨ws, hws, hrel, hreads⟩ := operands_rel hρ hops hlive hvs
  simp only [Lir.evalArgs_cons, Lir.evalArgs_nil, Option.bind_eq_bind] at hws
  cases ha : la.eval ρl with
  | none => simp [ha] at hws
  | some wa =>
    cases hb : lb.eval ρl with
    | none => simp [ha, hb] at hws
    | some wb =>
      simp [ha, hb] at hws
      subst hws
      rcases hrel with _ | ⟨hva, hrel'⟩
      rcases hrel' with _ | ⟨hvb, hnil⟩
      rcases hnil
      obtain ⟨p, q, n, rfl, rfl, hsem, rfl⟩ := primResult_nat2 hres hop
      exact ⟨rfl, ⟨p, q, n, wa, wb, ha, hb, hva, hvb, hsem, rfl, hreads la (by simp),
        hreads lb (by simp)⟩⟩

theorem bool_rel {T : Tables} (hT : BoolsOk T) {t e : Word} (hte : T.bools = some (t, e)) {P : AddressMap}
    {b : Bool} {v : Own.RVal}
    (hv : (match (if b then T.known.boolTrue else T.known.boolFalse) with
      | some c => Sem.Result.ofOption (Own.ctor0Of (ownTables T) c)
      | none => .stuck) = .ok v) :
    ValRel T P v (if b then t else e) := by
  obtain ⟨⟨kt, ct, hkt, hct, hnt, htt, rfl⟩, ⟨kf, cf, hkf, hcf, hnf, htf, rfl⟩⟩ := hT t e hte
  cases b with
  | true =>
    simp only [↓reduceIte, hkt, Own.ctor0Of, ownTables, hct] at hv
    split at hv
    · rename_i hfl
      simp only [Sem.Result.ofOption, Sem.Result.ok.injEq] at hv
      subst hv
      exact ⟨rfl, ⟨by rw [ofKey_key hct]; exact hct, by rw [ofKey_key hct]; exact hnt, htt⟩, hfl⟩
    · simp [Sem.Result.ofOption] at hv
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, hkf, Own.ctor0Of, ownTables, hcf] at hv
    split at hv
    · rename_i hfl
      simp only [Sem.Result.ofOption, Sem.Result.ok.injEq] at hv
      subst hv
      exact ⟨rfl, ⟨by rw [ofKey_key hcf]; exact hcf, by rw [ofKey_key hcf]; exact hnf, htf⟩, hfl⟩
    · simp [Sem.Result.ofOption] at hv





end IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
