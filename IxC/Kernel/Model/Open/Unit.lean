module

public import IxC.Kernel.Model.Open.Certs
public import IxC.Kernel.Model.Open.Irrel

@[expose] public section

/-!
# The rules' soundness over the public `Model`: unit-like families

* `DefEq.unitLikeTy`: `a`'s type reduces to a unit-like family at its parameters, certified
  against the family's telescope, and `b`'s type is definitionally equal to `a`'s. The
  certificate's walk is the parameters' fit (`WalkFits.fits`, at the family's arity,
  `StoredArities`), so the unit-like law (`Model.unit_like`) makes the two members equal.
  The law holds at every stored family with the flag, the basis `PUnit` among them.
* `DefEq.unitLike`: both sides' types reduce to the built-in `PUnit`, at levels the rule
  never compares. The law that `PUnit` has one member, the same at every level
  (`Model.punit_unit`), makes the two members equal.
-/

namespace Ix.Kernel.Open

open SetTheory Ix.Kernel.SetModel
open Ix.Kernel.Rules
open Ix.Kernel.Model.Rules (Frame LeavesSub)

universe w

variable {V : Type w} [SetTheory V] {env : Env md} {M : Model V env} {φ : LevelParam → Nat}

/-- **Members of a certified unit-like family's instance are equal**: a graded, framed reading
of `.const T us` applied to arguments whose certificate walk fits `T`'s telescope holds at
most one member. -/
theorem unitLike_members (hsc : StoredClosed env) (har : StoredArities env) {d : Nat} {lic : Bool}
    {w : Expr md} {T : Key md} {us : List Level} {cvT : ConstantVal md} {caps : IndCaps md}
    (hhead : w.getAppFn = .const T us) (hT : env.find? T = some (.indInfo cvT caps))
    (hunit : caps.unitlike = true) (hlen : w.getAppArgs.length = caps.unitParams)
    (hcerts : CertsS M φ d lic (cvT.type.instantiateLevelParams cvT.levelParams us)
      w.getAppArgs)
    (hfw : Frame d w) {σ : Nat → V} (hCw : Ctx M φ σ w) {W : V} (hW : Den M φ σ w W)
    (hgw : Gr M φ σ w) {x y : V} (hx : x ∈ˢ W) (hy : y ∈ˢ W) : x = y := by
  have hsp := eq_mkAppN_of_getAppFn hhead
  have hW' : Den M φ σ (Expr.mkAppN (.const T us) w.getAppArgs) W := by rw [← hsp]; exact hW
  have hgw' : Gr M φ σ (Expr.mkAppN (.const T us) w.getAppArgs) := by rw [← hsp]; exact hgw
  obtain ⟨F, ts, hF, hts, rfl⟩ := Den.mkAppN_inv hW'
  have hlenT : us.length = cvT.levelParams.length := by
    cases hF with
    | const hf hl => rw [hT] at hf; cases hf; exact hl
  obtain ⟨TT, hc, hTT, hgTT, hFT⟩ := const_typed (M := M) (φ := φ) hsc hT hlenT σ
  obtain rfl := DenotesO.functional hF hc
  have htyF : (cvT.type.instantiateLevelParams cvT.levelParams us).hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]
    exact (hsc _ (List.mem_of_find?_eq_some hT)).1.1
  have hfargs := Frame.getAppArgs hfw
  have hwalk := hcerts (const_type_frame (d := d) (us := us) hsc hT).1 hfargs σ
    (Ctx.of_closed htyF) (fun z hz => hCw.getAppArgs z hz) TT hTT hgTT ts hts
    (Gr.mkAppN_args hgw') (fun _ => ⟨_, hFT, spineOk_of_graded hgw' hc hts⟩)
  obtain ⟨σT, R, hfit⟩ := hwalk.fits hts (fun z hz => (hfargs z hz).2.1)
    (by
      rw [hlen]
      exact Expr.stripPis_instantiateLevelParams_isSome _ _ _ ((har.1 T cvT caps hT).1 hunit))
    htyF
  exact M.unit_like T cvT caps hT hunit us φ ρ₀ σT ts R _ x y hlenT
    (by rw [← hts.length_eq, hlen]) (DenotesO.to_denotes hc rfl) hfit hx hy

/-- **Unit-likeness at a compared type** (`DefEq.unitLikeTy`). -/
theorem DefEq.unitLikeTy_sound (hsc : StoredClosed env) (har : StoredArities env) {d : Nat}
    {a ta wta b tb : Expr md} {T : Key md} {us : List Level} {cvT : ConstantVal md}
    {caps : IndCaps md}
    (ha : InferIOS M φ d a ta) (hw : RedS M φ d ta wta) (hhead : wta.getAppFn = .const T us)
    (hT : env.find? T = some (.indInfo cvT caps)) (hunit : caps.unitlike = true)
    (hlen : wta.getAppArgs.length = caps.unitParams)
    (hcerts : CertsS M φ d true (cvT.type.instantiateLevelParams cvT.levelParams us)
      wta.getAppArgs)
    (hb : InferIOS M φ d b tb) (hd : DefEqS M φ d ta tb) : DefEqS M φ d a b := by
  intro hfa hfb σ hCa hCb x y hx hy hga hgb
  obtain ⟨hfta, hsubta, ka⟩ := ha hfa
  obtain ⟨hfw, hsubw, kw⟩ := hw hfta
  obtain ⟨Ta, hTa, hgTa, hxTa⟩ := ka σ hCa x hx hga
  have hCta : Ctx M φ σ ta := hCa.of_subset hsubta
  obtain ⟨hTw, hgw⟩ := kw σ hCta Ta hTa hgTa
  obtain ⟨hftb, hsubtb, kb⟩ := hb hfb
  obtain ⟨Tb, hTb, hgTb, hyTb⟩ := kb σ hCb y hy hgb
  obtain rfl := hd hfta hftb σ hCta (hCb.of_subset hsubtb) Ta Tb hTa hTb hgTa hgTb
  exact unitLike_members hsc har hhead hT hunit hlen hcerts hfw (hCta.of_subset hsubw) hTw hgw
    hxTa hyTb

/-- **A unit-like structure** (`DefEq.structUnit`): `a`'s type reduces to a certified unit-like
family instance and `b`'s reduced type is definitionally equal to it. -/
theorem DefEq.structUnit_sound (hsc : StoredClosed env) (har : StoredArities env) {d : Nat}
    {a ta wta b tb wtb : Expr md} {T : Key md} {us' : List Level} {cvT : ConstantVal md}
    {caps : IndCaps md}
    (ha : InferIOS M φ d a ta) (hwa : RedS M φ d ta wta) (hhead : wta.getAppFn = .const T us')
    (hT : env.find? T = some (.indInfo cvT caps)) (hunit : caps.unitlike = true)
    (hlen : wta.getAppArgs.length = caps.unitParams)
    (hb : InferIOS M φ d b tb) (hwb : RedS M φ d tb wtb) (hd : DefEqS M φ d wta wtb)
    (hcerts : CertsS M φ d false (cvT.type.instantiateLevelParams cvT.levelParams us')
      wta.getAppArgs) :
    DefEqS M φ d a b := by
  intro hfa hfb σ hCa hCb x y hx hy hga hgb
  obtain ⟨hfta, hsubta, ka⟩ := ha hfa
  obtain ⟨hfwa, hsubwa, kwa⟩ := hwa hfta
  obtain ⟨Ta, hTa, hgTa, hxTa⟩ := ka σ hCa x hx hga
  have hCta : Ctx M φ σ ta := hCa.of_subset hsubta
  obtain ⟨hTwa, hgwa⟩ := kwa σ hCta Ta hTa hgTa
  obtain ⟨hftb, hsubtb, kb⟩ := hb hfb
  obtain ⟨hfwb, hsubwb, kwb⟩ := hwb hftb
  obtain ⟨Tb, hTb, hgTb, hyTb⟩ := kb σ hCb y hy hgb
  have hCtb : Ctx M φ σ tb := hCb.of_subset hsubtb
  obtain ⟨hTwb, hgwb⟩ := kwb σ hCtb Tb hTb hgTb
  obtain rfl := hd hfwa hfwb σ (hCta.of_subset hsubwa) (hCtb.of_subset hsubwb) Ta Tb hTwa hTwb
    hgwa hgwb
  exact unitLike_members hsc har hhead hT hunit hlen hcerts hfwa (hCta.of_subset hsubwa) hTwa
    hgwa hxTa hyTb

/-- **Unit-likeness at the built-in `PUnit`** (`DefEq.unitLike`): both sides' types reduce to
`PUnit`, at whatever levels, and `PUnit` has one member at every level. -/
theorem DefEq.unitLike_sound {d : Nat} {a ta wta b tb wtb : Expr md}
    (ha : InferIOS M φ d a ta) (hwa : RedS M φ d ta wta) (hua : isUnitLikeTy env wta = true)
    (hb : InferIOS M φ d b tb) (hwb : RedS M φ d tb wtb) (hub : isUnitLikeTy env wtb = true) :
    DefEqS M φ d a b := by
  intro hfa hfb σ hCa hCb x y hx hy hga hgb
  obtain ⟨hfta, hsubta, ka⟩ := ha hfa
  obtain ⟨-, -, kwa⟩ := hwa hfta
  obtain ⟨Ta, hTa, hgTa, hxTa⟩ := ka σ hCa x hx hga
  obtain ⟨hTwa, -⟩ := kwa σ (hCa.of_subset hsubta) Ta hTa hgTa
  obtain ⟨hftb, hsubtb, kb⟩ := hb hfb
  obtain ⟨-, -, kwb⟩ := hwb hftb
  obtain ⟨Tb, hTb, hgTb, hyTb⟩ := kb σ hCb y hy hgb
  obtain ⟨hTwb, -⟩ := kwb σ (hCb.of_subset hsubtb) Tb hTb hgTb
  obtain ⟨us, -, -, -, -, -, -, rfl, -⟩ := isUnitLikeTy_inv hua
  obtain ⟨vs, -, -, -, -, -, -, rfl, -⟩ := isUnitLikeTy_inv hub
  exact M.punit_unit us vs φ φ ρ₀ ρ₀ Ta Tb x y (DenotesO.to_denotes hTwa rfl)
    (DenotesO.to_denotes hTwb rfl) hxTa hyTb

end Ix.Kernel.Open
