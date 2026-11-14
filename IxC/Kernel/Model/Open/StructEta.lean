module

public import IxC.Kernel.Model.Open.ProjType

@[expose] public section

/-!
# The rules' soundness over the public `Model`: structure η

`DefEq.structEta`: `a` is a fully applied constructor of an η-capable stored structure, `b`'s
type reduces to the structure at levels that agree with `a`'s, `a`'s parameters are that
type's and `a`'s fields are `b`'s projections. The certified type application fits the
structure's telescope, so an η law makes `b` the constructor at the parameters and its own
projections:

* at table-backed fields, the projection law's η clause (`Model.proj_law`); the projections
  are `.proj` nodes, which read the table;
* at a family modeled with projection functions (and at a family with no field), the η law
  through projection functions (`Model.eta_fn`); the projections are the functions applied to
  the parameters and `b`, whose certified spines (`EtaProjCerts`) denote and are graded.
-/

namespace Ix.Kernel.Open

open SetTheory Ix.Kernel.SetModel
open Ix.Kernel.Rules
open Ix.Kernel.Model.Rules (Frame LeavesSub)

universe w

variable {V : Type w} [SetTheory V] {env : Env md} {M : Model V env} {φ : LevelParam → Nat}

/-! ## Spines -/

theorem Frame.mkAppN {d : Nat} : ∀ {as : List (Expr md)} {f : Expr md}, Frame d f →
    (∀ x ∈ as, Frame d x) → Frame d (Expr.mkAppN f as)
  | [], _, hf, _ => hf
  | a :: as, f, hf, ha =>
    Frame.mkAppN (as := as) (f := .app f a) (Frame.app_iff.2 ⟨hf, ha a List.mem_cons_self⟩)
      (fun x hx => ha x (List.mem_cons_of_mem _ hx))

theorem Ctx.mkAppN {σ : Nat → V} : ∀ {as : List (Expr md)} {f : Expr md}, Ctx M φ σ f →
    (∀ x ∈ as, Ctx M φ σ x) → Ctx M φ σ (Expr.mkAppN f as)
  | [], _, hf, _ => hf
  | a :: as, f, hf, ha =>
    Ctx.mkAppN (as := as) (f := .app f a)
      (fun l hl => by
        simp only [Expr.fvarLeaves, List.mem_append] at hl
        exact hl.elim (hf l) (ha a List.mem_cons_self l))
      (fun x hx => ha x (List.mem_cons_of_mem _ hx))

/-! ## Structure η -/

/-- **Structure η** (`DefEq.structEta`). -/
theorem DefEq.structEta_sound (hse : StoredEnv env) {d : Nat} {a b tb wtb : Expr md}
    {c : Key md} {us : List Level} {cvc : ConstantVal md} {cnP cnF : Nat} {T : Key md}
    {us' : List Level} {cvT : ConstantVal md} {caps : IndCaps md}
    (hb : InferIOS M φ d b tb) (hwb : RedS M φ d tb wtb)
    (hhead : a.getAppFn = .const c us) (hc : env.find? c = some (.ctorInfo cvc cnP cnF))
    (_hlen : a.getAppArgs.length = cnP + cnF)
    (hthead : wtb.getAppFn = .const T us') (hT : env.find? T = some (.indInfo cvT caps))
    (heta : caps.eta = true) (hctor : caps.etaCtor = some c)
    (hresT : reservedBasisNames.contains T = false)
    (hresc : reservedBasisNames.contains c = false)
    (htlen : wtb.getAppArgs.length = caps.etaParams)
    (hlv : us'.length = cvT.levelParams.length) (hlps : cvc.levelParams = cvT.levelParams)
    (hslots : (towerSlotsAll env T caps.etaFields || recSlotsAll env T caps.etaFields) = true)
    (hus : ∀ φ, Level.EvalEqList φ us us')
    (hcerts : CertsS M φ d false (cvT.type.instantiateLevelParams cvT.levelParams us')
      wtb.getAppArgs)
    (hpc : towerSlotsAll env T caps.etaFields = false →
      EtaProjCertsS M φ d T us' wtb.getAppArgs b cvT.levelParams (List.range caps.etaFields))
    (hparams : DefEqListS M φ d (a.getAppArgs.take caps.etaParams) wtb.getAppArgs)
    (hfields : DefEqListS M φ d (a.getAppArgs.drop caps.etaParams)
      (etaProjs env T us' wtb.getAppArgs b caps.etaFields)) :
    DefEqS M φ d a b := by
  intro hfa hfb σ hCa hCb x y hx hy hga hgb
  -- `b`'s type, reduced: the family at its parameters
  obtain ⟨hftb, hsubtb, kb⟩ := hb hfb
  obtain ⟨Tb, hTb, hgTb, hyTb⟩ := kb σ hCb y hy hgb
  have hCtb : Ctx M φ σ tb := hCb.of_subset hsubtb
  obtain ⟨hfw, hsubw, kw⟩ := hwb hftb
  obtain ⟨hTw, hgw⟩ := kw σ hCtb Tb hTb hgTb
  have hCw : Ctx M φ σ wtb := hCtb.of_subset hsubw
  have hspT := eq_mkAppN_of_getAppFn hthead
  have hTw' : Den M φ σ (Expr.mkAppN (.const T us') wtb.getAppArgs) Tb := by
    rw [← hspT]; exact hTw
  have hgw' : Gr M φ σ (Expr.mkAppN (.const T us') wtb.getAppArgs) := by
    rw [← hspT]; exact hgw
  obtain ⟨F, ts, hF, hts, rfl⟩ := Den.mkAppN_inv hTw'
  have hFv : F = M.cval T (Level.substFn φ cvT.levelParams us') := by
    cases hF with
    | const hf _ => rw [hT] at hf; cases hf; rfl
  -- `a` is the constructor at its arguments, read at the family's levels
  have hspa := eq_mkAppN_of_getAppFn hhead
  have hx' : Den M φ σ (Expr.mkAppN (.const c us) a.getAppArgs) x := by
    rw [← hspa]; exact hx
  have hga' : Gr M φ σ (Expr.mkAppN (.const c us) a.getAppArgs) := by
    rw [← hspa]; exact hga
  obtain ⟨K, vs, hK, hvs, rfl⟩ := Den.mkAppN_inv hx'
  have hKv : K = M.cval c (Level.substFn φ cvT.levelParams us') := by
    cases hK with
    | const hf _ =>
      rw [hc] at hf
      cases hf
      show M.cval c (Level.substFn φ cvc.levelParams us) = _
      rw [hlps, Ix.Kernel.Level.substFn_congr (hus φ)]
  -- the parameters fit the family's telescope
  obtain ⟨TT, -, hTT, hgTT, -⟩ := const_typed (M := M) (φ := φ) hse.closed hT hlv σ
  have htyF : (cvT.type.instantiateLevelParams cvT.levelParams us').hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]
    exact (hse.closed _ (List.mem_of_find?_eq_some hT)).1.1
  have hfwargs := Frame.getAppArgs hfw
  have hwalk := hcerts (const_type_frame (d := d) (us := us') hse.closed hT).1 hfwargs σ
    (Ctx.of_closed htyF) (fun z hz => hCw.getAppArgs z hz) TT hTT hgTT ts hts
    (Gr.mkAppN_args hgw') (fun h => nomatch h)
  obtain ⟨σT, R, hfit⟩ := hwalk.fits hts (fun z hz => (hfwargs z hz).2.1)
    (by
      rw [htlen]
      exact Expr.stripPis_instantiateLevelParams_isSome _ _ _
        ((hse.arities.1 T cvT caps hT).2 heta))
    htyF
  have htslen : ts.length = caps.etaParams := by rw [← hts.length_eq, htlen]
  have hyF : y ∈ˢ ts.foldl app (M.cval T (Level.substFn φ cvT.levelParams us')) := by
    rw [← hFv]; exact hyTb
  -- `a`'s parameters are the type's
  have hfaargs := Frame.getAppArgs hfa
  have hvtake : vs.take caps.etaParams = ts :=
    hparams.2 (fun z hz => hfaargs z (List.mem_of_mem_take hz)) hfwargs σ
      (fun z hz => hCa.getAppArgs z (List.mem_of_mem_take hz)) (fun z hz => hCw.getAppArgs z hz)
      _ _ (hvs.take _) hts (fun z hz => Gr.mkAppN_args hga' z (List.mem_of_mem_take hz))
      (Gr.mkAppN_args hgw')
  have hfdrop : ∀ z ∈ a.getAppArgs.drop caps.etaParams, Frame d z :=
    fun z hz => hfaargs z (List.mem_of_mem_drop hz)
  have hCdrop : ∀ z ∈ a.getAppArgs.drop caps.etaParams, Ctx M φ σ z :=
    fun z hz => hCa.getAppArgs z (List.mem_of_mem_drop hz)
  have hgdrop : ∀ z ∈ a.getAppArgs.drop caps.etaParams, Gr M φ σ z :=
    fun z hz => Gr.mkAppN_args hga' z (List.mem_of_mem_drop hz)
  by_cases htow : towerSlotsAll env T caps.etaFields = true ∧ 0 < caps.etaFields
  · -- TABLE-BACKED FIELDS: the projection law's η clause
    obtain ⟨htow, hpos⟩ := htow
    have hts' : (List.range caps.etaFields).all (fun j => (env.findProj? T j).isSome) = true :=
      htow
    have hslot : ∀ j, j < caps.etaFields → ∃ e, env.findProj? T j = some e := fun j hj =>
      Option.isSome_iff_exists.mp (List.all_eq_true.mp hts' j (List.mem_range.mpr hj))
    obtain ⟨e0, he0⟩ := hslot 0 hpos
    obtain ⟨-, -, hTst, -⟩ := hse.tables T 0 e0 he0
    obtain ⟨cvT', capsT', hci, hetaT⟩ := hTst _ hT
    obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj hci
    obtain ⟨hec, hpar, hfld⟩ := hetaT heta
    rw [hctor] at hec
    obtain rfl := Option.some.inj hec
    obtain ⟨hlpsT, -, _cvC, -, -, -, hlaw⟩ := M.proj_law T 0 e0 cvT caps he0 hT
    have hoff : ∀ j ej, env.findProj? T j = some ej → ej.off = e0.off := by
      intro j ej hej
      obtain ⟨t1, h1, -, rfl⟩ := Env.findProj?_some hej
      obtain ⟨t0, h0, -, rfl⟩ := Env.findProj?_some he0
      rw [h1] at h0
      cases h0
      rfl
    have hK' : Denotes M.cval env φ ρ₀ (.const e0.ctor us')
        (M.cval e0.ctor (Level.substFn φ cvT.levelParams us')) := by
      rw [← hlps]
      exact .const hc (show us'.length = cvc.levelParams.length by rw [hlps]; exact hlv)
    obtain ⟨-, hη⟩ := hlaw us' φ ρ₀ F _ (by rw [← hlpsT]; exact hlv)
      (DenotesO.to_denotes hF rfl) hK'
    have hyeta := hη σT R ts y (by rw [htslen, hpar]) hfit hyTb
    -- `b`'s projections denote its fields
    have hetaP : etaProjs env T us' wtb.getAppArgs b caps.etaFields =
        (List.range caps.etaFields).map fun j => Expr.proj T j b := by
      unfold etaProjs
      rw [if_pos htow]
    rw [hetaP] at hfields
    have hmemP : ∀ z ∈ (List.range caps.etaFields).map (fun j => Expr.proj T j b),
        ∃ j, z = Expr.proj T j b := fun z hz => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hz
      exact ⟨j, rfl⟩
    have hpl : DenList M φ σ ((List.range caps.etaFields).map fun j => Expr.proj T j b)
        ((List.range caps.etaFields).map fun j => field (j + e0.off) y) := by
      refine DenList.map_mem _ fun j hj => ?_
      obtain ⟨ej, hej⟩ := hslot j (List.mem_range.mp hj)
      rw [← hoff j ej hej]
      exact .proj_table hej hy
    have hvdrop : vs.drop caps.etaParams =
        (List.range caps.etaFields).map fun j => field (j + e0.off) y :=
      hfields.2 hfdrop
        (fun z hz => by obtain ⟨j, rfl⟩ := hmemP z hz; exact Frame.proj_iff.2 hfb) σ hCdrop
        (fun z hz => by
          obtain ⟨j, rfl⟩ := hmemP z hz
          exact hCb.of_subset fun l hl => by simpa [Expr.fvarLeaves] using hl)
        _ _ (hvs.drop _) hpl hgdrop
        (fun z hz => by obtain ⟨j, rfl⟩ := hmemP z hz; exact hgb)
    rw [← List.take_append_drop caps.etaParams vs, hvtake, hvdrop, hKv, hfld]
    exact hyeta.symm
  · -- PROJECTION FUNCTIONS (or no field): the η law through projection functions
    have hto : 0 < caps.etaFields → towerSlotsAll env T caps.etaFields = false := by
      intro hpos
      cases h : towerSlotsAll env T caps.etaFields
      · rfl
      · exact absurd ⟨h, hpos⟩ htow
    have hrecs : ∀ j, j < caps.etaFields → ∃ (cv : ConstantVal md) (mI rP : Nat)
        (rules : List (RecRule md)), env.find? (projFnName T j) = some (.recInfo cv mI rP rules) := by
      intro j hj
      have hrec : recSlotsAll env T caps.etaFields = true := by
        simpa [hto (by omega)] using hslots
      exact Ix.Kernel.recSlotsAll_slot hrec j hj
    have hyeta := M.eta_fn T cvT caps c hT heta hresT hctor hresc ⟨cvc, cnP, cnF, hc⟩ hrecs us' φ
      ρ₀ σT R ts y hlv htslen hfit hyF
    have hetaP : etaProjs env T us' wtb.getAppArgs b caps.etaFields =
        (List.range caps.etaFields).map fun j =>
          Expr.mkAppN (.const (projFnName T j) us') (wtb.getAppArgs ++ [b]) := by
      unfold etaProjs
      split
      · next h =>
        rcases Nat.eq_zero_or_pos caps.etaFields with h0 | h0
        · rw [h0]; rfl
        · exact absurd ⟨h, h0⟩ htow
      · rfl
    rw [hetaP] at hfields
    -- the projection functions' spines denote their values, and are graded
    have hargs' : ∀ z ∈ wtb.getAppArgs ++ [b], Frame d z ∧ Ctx M φ σ z ∧ Gr M φ σ z := by
      intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact ⟨hfwargs z hz, hCw.getAppArgs z hz, Gr.mkAppN_args hgw' z hz⟩
      · rw [List.mem_singleton.mp hz]
        exact ⟨hfb, hCb, hgb⟩
    have hspine : ∀ j ∈ List.range caps.etaFields,
        Den M φ σ (Expr.mkAppN (.const (projFnName T j) us') (wtb.getAppArgs ++ [b]))
            ((ts ++ [y]).foldl app (M.cval (projFnName T j) (Level.substFn φ cvT.levelParams us'))) ∧
          Gr M φ σ (Expr.mkAppN (.const (projFnName T j) us') (wtb.getAppArgs ++ [b])) := by
      intro j hj
      obtain ⟨cvp, mI', rP', rules', hfp, hlpp, -, hcp⟩ :=
        hpc (hto (Nat.lt_of_le_of_lt (Nat.zero_le j) (List.mem_range.mp hj))) j hj
      have h := certs_spine_sound hse.closed hfp
        (show us'.length = cvp.levelParams.length by rw [hlpp]; exact hlv) hcp
        (fun z hz => (hargs' z hz).1) (fun z hz => (hargs' z hz).2.1)
        (hts.append (.cons hy .nil)) (fun z hz => (hargs' z hz).2.2)
      rw [show (ConstantInfo.recInfo cvp mI' rP' rules').toConstantVal.levelParams
        = cvT.levelParams from hlpp] at h
      exact h
    have hmemP : ∀ z ∈ (List.range caps.etaFields).map (fun j =>
          Expr.mkAppN (.const (projFnName T j) us') (wtb.getAppArgs ++ [b])),
        ∃ j ∈ List.range caps.etaFields,
          z = Expr.mkAppN (.const (projFnName T j) us') (wtb.getAppArgs ++ [b]) := fun z hz => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
      exact ⟨j, hj, rfl⟩
    have hvdrop : vs.drop caps.etaParams = (List.range caps.etaFields).map fun j =>
        (ts ++ [y]).foldl app (M.cval (projFnName T j) (Level.substFn φ cvT.levelParams us')) :=
      hfields.2 hfdrop
        (fun z hz => by
          obtain ⟨j, -, rfl⟩ := hmemP z hz
          exact Frame.mkAppN (Frame.of_closed rfl rfl) fun w hw => (hargs' w hw).1)
        σ hCdrop
        (fun z hz => by
          obtain ⟨j, -, rfl⟩ := hmemP z hz
          exact Ctx.mkAppN (fun l hl => by simp [Expr.fvarLeaves] at hl)
            fun w hw => (hargs' w hw).2.1)
        _ _ (hvs.drop _) (DenList.map_mem _ fun j hj => (hspine j hj).1) hgdrop
        (fun z hz => by obtain ⟨j, hj, rfl⟩ := hmemP z hz; exact (hspine j hj).2)
    rw [← List.take_append_drop caps.etaParams vs, hvtake, hvdrop, hKv]
    exact hyeta.symm

end Ix.Kernel.Open
