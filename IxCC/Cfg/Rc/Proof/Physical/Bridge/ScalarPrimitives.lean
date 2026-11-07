import IxCC.Cfg.Rc.Proof.Physical.Bridge.ScalarChecked
import IxCC.Cfg.Rc.Proof.Physical.Bridge.ScalarDiv
import IxCC.Cfg.Rc.Proof.Physical.Bridge.ScalarCall
import IxCC.Rt.Proof.Instr

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
open IxCC IxCC.Rt IxCC.Rt.Proof IxCC.Rt.Lower
open IxCC.Rt.Rc.Procs
open IxCC.Lir (Word)
open IxCC.Src (NatMap)

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


end IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
