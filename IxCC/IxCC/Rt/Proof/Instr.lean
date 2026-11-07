import IxCC.Rt.Proof.OpsDiv
import IxCC.Rt.Proof.OpsCheck
import IxCC.Rt.Proof.OpsProj
import IxCC.Rt.Proof.OpsCall

/-!
# One Cfg instruction

`instr_sim`: the lowering of an instruction other than a call, run from a
state with an open block to one that continues (`true`), is an `RhsSim`
from the position where its code starts to the position after it. Every
`Lam.Prim` goes to its expansion's lemma (`primitive_sim`). `instr_fails`:
an instruction whose lowering ended the block (`false`: a literal without
a word) leaves Lir at a `fail natOverflow` terminator.
-/

set_option autoImplicit false

namespace IxCC.Rt.Proof

open IxCC.Lir (Word)
open IxCC.Rt.Lower
open IxCC.Src (NatMap)

/-! ## Operands -/

/-- The state after closing the open block with `t`. -/
def closeSt (st : St) (t : PTerm) : St :=
  { st with done := st.done.insert st.cur { params := st.params, body := st.acc.reverse, term := t },
            params := [], acc := [] }

theorem withOperands_run {f : Fir.FunId} {as : List Fir.Arg} {k : List Lir.Arg → M Unit} {st st' : St} {b : Bool}
    (h : (withOperands f as k).run st = .ok (b, st')) :
    (∃ las, operands f as = .ok (some las) ∧ b = true ∧ (k las).run st = .ok ((), st')) ∨
    (operands f as = .ok none ∧ b = false ∧ st' = closeSt st (.fail .natOverflow)) := by
  unfold withOperands at h
  cases hop : operands f as with
  | error e =>
    simp [hop, bind, StateT.bind, StateT.run, MonadLift.monadLift, liftM, monadLift, StateT.lift, Except.bind] at h
  | ok o =>
    cases o with
    | none =>
      simp [hop, bind, StateT.bind, StateT.run, MonadLift.monadLift, liftM, monadLift, StateT.lift, Except.bind,
        close, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, MonadState.modifyGet, pure, StateT.pure,
        Except.pure] at h
      exact .inr ⟨rfl, h.1, h.2.symm⟩
    | some las =>
      simp [hop, bind, StateT.bind, StateT.run, MonadLift.monadLift, liftM, monadLift, StateT.lift, Except.bind,
        pure, StateT.pure, Except.pure] at h
      cases hk : k las st with
      | error e => simp [hk] at h
      | ok v =>
        simp only [hk, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .inl ⟨las, rfl, rfl, by rw [StateT.run, hk]⟩

theorem operands_one {f : Fir.FunId} {a : Fir.Arg} {las : List Lir.Arg} (h : operands f [a] = .ok (some las)) :
    ∃ la, las = [la] ∧ operand f a = .ok (some la) := by
  simp only [operands, bind, Except.bind, pure, Except.pure] at h
  cases ha : operand f a with
  | error e => simp [ha] at h
  | ok o =>
    cases o with
    | none => simp [ha] at h
    | some la => simp only [ha, Except.ok.injEq, Option.some.injEq] at h; exact ⟨la, h.symm, rfl⟩

/-- Variables read by live operands. -/
theorem liveArgs_of {D : Nat → Prop} : ∀ {as : List Fir.Arg}, (∀ y ∈ Cfg.Check.argVars as, ¬ D y) →
    ∀ a ∈ as, LiveArg D a
  | [], _, _, h => nomatch h
  | a :: as, h, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · intro y hy
      subst hy
      exact h y (by simp [Cfg.Check.argVars])
    · refine liveArgs_of (fun y hy => h y ?_) b hb
      cases a <;> simp [Cfg.Check.argVars, hy]

/-! ## Primitives -/

/-- A throwing action never runs to a state. -/
macro "bad_shape" : tactic =>
  `(tactic| (simp only [primitive] at *; simp [throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind, bind,
      StateT.bind, StateT.run] at *))

/-- **Every primitive's expansion simulates Cfg's primitive.** -/
theorem primitive_sim {T : Tables} (hT : BoolsOk T) {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {D : Nat → Prop} {sup : Nat} {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    (hpow : lp.funcs[T.natPow]? = some Procs.natPow) (hgcd : lp.funcs[T.natGcd]? = some Procs.natGcd)
    {st st' : St} {x : Nat} {op : Lam.Prim} {las : List Lir.Arg} {as : List Fir.Arg}
    (hrun : (primitive f T x op las).run st = .ok ((), st')) (hC : Ext C st') (hl : Labels st) (ho : Open st)
    (hsup : sup ≤ st.fresh) (hx : x < sup) (hops : operands f as = .ok (some las))
    (hlive : ∀ a ∈ as, LiveArg D a) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim op as)) := by
  rcases las with _ | ⟨la, _ | ⟨lb, _ | ⟨lc, las⟩⟩⟩
  · cases op <;> bad_shape
  · cases op
    case natPred => exact prim_natPred hF hH hrun hC ho hsup hx hops hlive
    all_goals bad_shape
  · cases op
    case natAdd => exact prim_natAdd hF hH hrun hC hl ho hsup hx hops hlive
    case natSub => exact prim_natSub hF hH hrun hC ho hsup hx hops hlive
    case natMul => exact prim_natMul hF hH hrun hC hl ho hsup hx hops hlive
    case natDiv => exact prim_natDiv hF hH hrun hC ho hsup hx hops hlive
    case natMod => exact prim_natMod hF hH hrun hC ho hsup hx hops hlive
    case natPow => exact prim_natPow hF hH hpow hrun hC ho hx hops hlive
    case natGcd => exact prim_natGcd hF hH hgcd hrun hC ho hx hops hlive
    case natBeq => exact prim_cmp hT hF hH rfl hrun hC ho hx hops hlive
    case natBle => exact prim_cmp hT hF hH rfl hrun hC ho hx hops hlive
    case natBlt => exact prim_cmp hT hF hH rfl hrun hC ho hx hops hlive
    case natLand => exact prim_natLand hF hH hrun hC ho hsup hx hops hlive
    case natLor => exact prim_natLor hF hH hrun hC ho hsup hx hops hlive
    case natXor => exact prim_natXor hF hH hrun hC ho hsup hx hops hlive
    case natShl => exact prim_natShl hF hH hrun hC hl ho hsup hx hops hlive
    case natShr => exact prim_natShr hF hH hrun hC ho hsup hx hops hlive
    case natPred => bad_shape
  · cases op <;> bad_shape

/-! ## Instructions -/

/-- **An instruction other than a call simulates Cfg's**, from where its
code starts to where the next instruction's starts. -/
theorem instr_sim {T : Tables} (hT : BoolsOk T) {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {D : Nat → Prop} {sup : Nat} {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    (hpow : lp.funcs[T.natPow]? = some Procs.natPow) (hgcd : lp.funcs[T.natGcd]? = some Procs.natGcd)
    {st st' : St} {x : Nat} {r : Own.Rhs} (hnc : ∀ g as, r ≠ .fir (.call g as))
    (hrun : (instr f T (.bind x r)).run st = .ok (true, st')) (hC : Ext C st') (hl : Labels st) (ho : Open st)
    (hsup : sup ≤ st.fresh) (hx : x < sup) (hlive : ∀ y ∈ Cfg.Check.rhsVars r, ¬ D y) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x r := by
  match r, hnc, hrun, hlive with
  | .fir (.arg a), _, hrun, hlive =>
    rcases withOperands_run hrun with ⟨las, hops, -, hk⟩ | ⟨-, h, -⟩
    · obtain ⟨la, rfl, hop⟩ := operands_one hops
      simp only [assign_run, Except.ok.injEq, Prod.mk.injEq, true_and] at hk
      subst hk
      exact arg_sim hF hH hC ho hx hop (liveArgs_of hlive a (by simp))
    · cases h
  | .fir (.prim op as), _, hrun, hlive =>
    rcases withOperands_run hrun with ⟨las, hops, -, hk⟩ | ⟨-, h, -⟩
    · exact primitive_sim hT hF hH hpow hgcd hk hC hl ho hsup hx hops (liveArgs_of hlive)
    · cases h
  | .fir (.call g as), hnc, _, _ => exact absurd rfl (hnc g as)
  | .fir (.ctor ..), _, hrun, _ =>
    simp [instr, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind, bind, StateT.bind, StateT.run] at hrun
  | .fir (.proj ..), _, hrun, _ =>
    simp [instr, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind, bind, StateT.bind, StateT.run] at hrun
  | .alloc c as κ, _, hrun, hlive =>
    rcases withOperands_run hrun with ⟨las, hops, -, hk⟩ | ⟨-, h, -⟩
    · exact alloc_sim hF hH hk hC hl ho hsup hx hops (liveArgs_of hlive)
    · cases h
  | .proj y c i, _, hrun, hlive =>
    have hrun' : (Lower.proj f T x y c i).run st = .ok ((), st') := by
      simp only [instr, bind, StateT.bind, StateT.run, pure, StateT.pure, Except.bind, Except.pure] at hrun
      revert hrun
      cases h : Lower.proj f T x y c i st with
      | error e => simp
      | ok v => intro hrun; simp only [Except.ok.injEq, Prod.mk.injEq] at hrun; rw [StateT.run, h, ← hrun.2]
    exact proj_sim hF hH hrun' hC ho hx (hlive y (by simp [Cfg.Check.rhsVars]))

/-- An instruction whose lowering ended the block closed it with `fail
natOverflow`. -/
theorem instr_false {T : Tables} {f : Fir.FunId} {st st' : St} {i : Cfg.Instr}
    (hrun : (instr f T i).run st = .ok (false, st')) : st' = closeSt st (.fail .natOverflow) := by
  match i, hrun with
  | .bind x (.fir (.arg a)), hrun =>
    rcases withOperands_run hrun with ⟨_, _, h, _⟩ | ⟨-, -, h⟩
    · cases h
    · exact h
  | .bind x (.fir (.prim op as)), hrun =>
    rcases withOperands_run hrun with ⟨_, _, h, _⟩ | ⟨-, -, h⟩
    · cases h
    · exact h
  | .bind x (.fir (.call g as)), hrun =>
    rcases withOperands_run hrun with ⟨_, _, h, _⟩ | ⟨-, -, h⟩
    · cases h
    · exact h
  | .bind x (.alloc c as κ), hrun =>
    rcases withOperands_run hrun with ⟨_, _, h, _⟩ | ⟨-, -, h⟩
    · cases h
    · exact h
  | .bind x (.fir (.ctor ..)), hrun =>
    simp [instr, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind, bind, StateT.bind, StateT.run]
      at hrun
  | .bind x (.fir (.proj ..)), hrun =>
    simp [instr, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind, bind, StateT.bind, StateT.run]
      at hrun
  | .bind x (.proj y c i), hrun =>
    exfalso
    simp only [instr, bind, StateT.bind, StateT.run, pure, StateT.pure, Except.bind, Except.pure] at hrun
    revert hrun
    cases Lower.proj f T x y c i st <;> simp

/-- An instruction whose lowering ended the block leaves Lir at its
`fail natOverflow`. -/
theorem instr_fails {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {fn : Nat} {F : Lir.Func}
    {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {i : Cfg.Instr} (hrun : (instr f T i).run st = .ok (false, st')) (hC : Ext C st')
    (ho : Open st) (mem : X86.Memory) (ρl : Lir.Env) (rest : List Lir.Frame) :
    Sem.Fails (Lir.semStep lp) (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest) := by
  have hst := instr_false hrun
  subst hst
  have hb := hC.done (j := st.cur) (b := { params := st.params, body := st.acc.reverse, term := .fail .natOverflow })
    (by simp [closeSt, Src.NatMap.get?_insert])
  obtain ⟨lb, hres, hlb⟩ := hH hb
  obtain ⟨-, hbody, hterm⟩ := resolveBlock_ok hres
  simp only [resolveTerm, pure, Except.pure, Except.ok.injEq] at hterm
  refine ⟨0, _, .natOverflow, .refl _, ?_⟩
  exact Lir.semStep_fail.2 (Lir.fail_at hF hlb (by rw [← Array.length_toList, hbody]; simp) hterm.symm)

end IxCC.Rt.Proof
