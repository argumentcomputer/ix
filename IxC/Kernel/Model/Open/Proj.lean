module

public import IxC.Kernel.Model.Open.Tables

@[expose] public section

/-!
# The rules' soundness over the public `Model`: projections and structure η

* `Red.proj`: a projection of a certified constructor application is the field. The node
  reads the table (`Denotes.proj_table`); the certificate's walk is the arguments' fit to the
  constructor's type, whose residual is the structure at the parameters, so the structure is
  stored; the projection law's ι clause (`Model.proj_law`), under the table's guard
  (`FireSem` and `TowerO5`), gives the field.
* `DefEq.structEtaTy`: a constructor application of an η-capable structure with table-backed
  fields equals any `b` of its type whose projections are its fields. The projection law's
  η clause makes `b` the constructor at the parameters and `b`'s own fields, which the
  projection nodes read.
-/

namespace Ix.Kernel.Open

open SetTheory Ix.Kernel.SetModel
open Ix.Kernel.Rules
open Ix.Kernel.Model.Rules (Frame LeavesSub)

universe w

variable {V : Type w} [SetTheory V] {env : Env md} {M : Model V env} {φ : LevelParam → Nat}

/-! ## Lists -/

theorem getD_mem_of_lt {α : Type _} : ∀ {l : List α} {k : Nat} (d : α), k < l.length →
    l.getD k d ∈ l
  | [], _, _, hk => absurd hk (Nat.not_lt_zero _)
  | _ :: _, 0, _, _ => by rw [List.getD_cons_zero]; exact List.mem_cons_self
  | _ :: xs, k + 1, d, hk => by
    rw [List.getD_cons_succ]
    exact List.mem_cons_of_mem _ (getD_mem_of_lt (l := xs) d (Nat.lt_of_succ_lt_succ hk))

theorem DenList.getD {σ : Nat → V} : ∀ {es : List (Expr md)} {vs : List V},
    DenList M φ σ es vs → ∀ {k : Nat}, k < es.length →
      Den M φ σ (es.getD k (.bvar 0)) (vs.getD k empty)
  | _, _, .nil, _, hk => absurd hk (Nat.not_lt_zero _)
  | _, _, .cons hx _, 0, _ => by rw [List.getD_cons_zero, List.getD_cons_zero]; exact hx
  | _, _, .cons _ hxs, k + 1, hk => by
    rw [List.getD_cons_succ, List.getD_cons_succ]
    exact DenList.getD hxs (Nat.lt_of_succ_lt_succ hk)

theorem DenList.take {σ : Nat → V} : ∀ {es : List (Expr md)} {vs : List V},
    DenList M φ σ es vs → ∀ k, DenList M φ σ (es.take k) (vs.take k)
  | _, _, .nil, _ => by rw [List.take_nil, List.take_nil]; exact .nil
  | _, _, .cons _ _, 0 => .nil
  | _, _, .cons hx hxs, k + 1 => .cons hx (DenList.take hxs k)

theorem DenList.drop {σ : Nat → V} : ∀ {es : List (Expr md)} {vs : List V},
    DenList M φ σ es vs → ∀ k, DenList M φ σ (es.drop k) (vs.drop k)
  | _, _, .nil, _ => by rw [List.drop_nil, List.drop_nil]; exact .nil
  | _, _, h, 0 => h
  | _, _, .cons _ hxs, k + 1 => DenList.drop hxs k

theorem DenList.functional {σ : Nat → V} : ∀ {es : List (Expr md)} {vs ws : List V},
    DenList M φ σ es vs → DenList M φ σ es ws → vs = ws
  | _, _, _, .nil, .nil => rfl
  | _, _, _, .cons hx hxs, .cons hy hys => by
    rw [DenotesO.functional hx hy, DenList.functional hxs hys]

theorem DenList.map_mem {σ : Nat → V} {f : Nat → Expr md} {g : Nat → V} :
    ∀ (l : List Nat), (∀ j ∈ l, Den M φ σ (f j) (g j)) → DenList M φ σ (l.map f) (l.map g)
  | [], _ => .nil
  | j :: l, h => .cons (h j List.mem_cons_self)
      (DenList.map_mem l fun k hk => h k (List.mem_cons_of_mem _ hk))

/-! ## Fits -/

/-- A fit walks the telescope's binders: the residual is what `stripPis` leaves. -/
theorem Fits.stripPis_eq {cval : Key md → (LevelParam → Nat) → V} {ρ ρ' : BVarIdx → V}
    {T R : Expr md} {xs : List V} (h : Fits cval env φ ρ T xs ρ' R) :
    ∃ bs, T.stripPis xs.length = some (bs, R) := by
  induction h with
  | nil => exact ⟨[], rfl⟩
  | @cons ρ ρ' A B R m X x xs hA hx _ ih =>
    obtain ⟨bs, hs⟩ := ih
    exact ⟨(A, m) :: bs, by simp [Expr.stripPis, hs]⟩

/-- **The residual of a fit denotes** when the telescope does: each member is in the domain
the binder's body is read on. -/
theorem Fits.residual {cval : Key md → (LevelParam → Nat) → V} {ρ ρ' : BVarIdx → V}
    {T R : Expr md} {xs : List V} (h : Fits cval env φ ρ T xs ρ' R) :
    ∀ {W : V}, Denotes cval env φ ρ T W → ∃ W', Denotes cval env φ ρ' R W' := by
  induction h with
  | nil => exact fun hW => ⟨_, hW⟩
  | cons hA hx _ ih =>
    intro W hW
    cases hW with
    | pi hA' hB _ =>
      obtain rfl := Denotes_functional hA hA'
      exact ih (hB _ hx)

/-- A spine that denotes has a head that denotes. -/
theorem Denotes.mkAppN_head {cval : Key md → (LevelParam → Nat) → V} {ρ : BVarIdx → V} :
    ∀ {as : List (Expr md)} {f : Expr md} {W : V}, Denotes cval env φ ρ (Expr.mkAppN f as) W →
      ∃ F, Denotes cval env φ ρ f F
  | [], _, _, h => ⟨_, h⟩
  | a :: as, f, _, h => by
    obtain ⟨F, hF⟩ := Denotes.mkAppN_head (as := as) (f := .app f a) h
    cases hF with
    | app hf _ => exact ⟨_, hf⟩

/-! ## Projection of a constructor -/

/-- **The projection of a certified constructor application** (`Red.proj`). -/
theorem Red.proj_sound (hse : StoredEnv env) {d : Nat} {sn : Key md} {i : Nat} {e : Expr md}
    {entry : ProjEntry md} {us : List Level} {cvC : ConstantVal md} {nP nF : Nat}
    (hP : env.findProj? sn i = some entry) (hhead : e.getAppFn = .const entry.ctor us)
    (hi : i < entry.numFields)
    (hlen : e.getAppArgs.length = entry.numParams + entry.numFields)
    (hus : us.length = entry.levelParams.length) (hfire : FireSem entry us)
    (hC : env.find? entry.ctor = some (.ctorInfo cvC nP nF))
    (hcerts : CertsS M φ d true (cvC.type.instantiateLevelParams cvC.levelParams us)
      e.getAppArgs) :
    RedS M φ d (.proj sn i e) (e.getAppArgs.getD (entry.numParams + i) (.bvar 0)) := by
  obtain ⟨-, hO5, hTst, hCst⟩ := hse.tables sn i entry hP
  obtain ⟨rfl, rfl, hlpsC, bsC, hsC⟩ := hCst cvC nP nF hC
  have hk : entry.numParams + i < e.getAppArgs.length := by omega
  have hmemk := getD_mem_of_lt (.bvar 0) hk
  intro hfr
  have hfe : Frame d e := Frame.proj_iff.1 hfr
  have hfargs := Frame.getAppArgs hfe
  refine ⟨hfargs _ hmemk, fun l hl => ?_, fun σ hCx v hv hg => ?_⟩
  · simp only [Expr.fvarLeaves]
    exact fvarLeaves_getAppArgs hmemk l hl
  have hCe : Ctx M φ σ e := hCx.of_subset fun l hl => by simpa [Expr.fvarLeaves] using hl
  have hge : Gr M φ σ e := hg
  -- the node reads the table
  obtain ⟨P, hPe, rfl⟩ : ∃ P, Den M φ σ e P ∧ v = field (i + entry.off) P := by
    cases hv with
    | proj_table ht he => rw [hP] at ht; cases ht; exact ⟨_, he, rfl⟩
    | proj_fst ht _ => rw [hP] at ht; exact nomatch ht
    | proj_snd ht _ => rw [hP] at ht; exact nomatch ht
  have hsp := eq_mkAppN_of_getAppFn hhead
  have hPe' : Den M φ σ (Expr.mkAppN (.const entry.ctor us) e.getAppArgs) P := by
    rw [← hsp]; exact hPe
  have hge' : Gr M φ σ (Expr.mkAppN (.const entry.ctor us) e.getAppArgs) := by
    rw [← hsp]; exact hge
  obtain ⟨K, vs, hK, hvs, rfl⟩ := Den.mkAppN_inv hPe'
  have hlenC : us.length = cvC.levelParams.length := by rw [hlpsC]; exact hus
  obtain ⟨TT, hc, hTT, hgTT, hKT⟩ := const_typed (M := M) (φ := φ) hse.closed hC hlenC σ
  have htyF : (cvC.type.instantiateLevelParams cvC.levelParams us).hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]
    exact (hse.closed _ (List.mem_of_find?_eq_some hC)).1.1
  -- the walk is the arguments' fit
  have hwalk := hcerts (const_type_frame (d := d) (us := us) hse.closed hC).1 hfargs σ
    (Ctx.of_closed htyF) (fun z hz => hCe.getAppArgs z hz) TT hTT hgTT vs hvs
    (Gr.mkAppN_args hge')
    (fun _ => ⟨K, by rw [DenotesO.functional hK hc]; exact hKT, spineOk_of_graded hge' hK hvs⟩)
  obtain ⟨σC, R, hfit⟩ := hwalk.fits hvs (fun z hz => (hfargs z hz).2.1)
    (by
      rw [hlen]
      exact Expr.stripPis_instantiateLevelParams_isSome _ _ _ (by rw [hsC]; rfl))
    htyF
  have hlenvs : vs.length = entry.numParams + entry.numFields := by
    rw [← hvs.length_eq, hlen]
  -- the fit's residual is the structure at the parameters, so the structure is stored
  obtain ⟨bs', hs'⟩ := Fits.stripPis_eq hfit
  rw [hlenvs] at hs'
  obtain ⟨hReq, -⟩ := Expr.stripPis_instantiateLevelParams_eq cvC.levelParams us _ hsC hs'
  obtain ⟨W, hW⟩ := Fits.residual hfit (DenotesO.to_denotes hTT htyF)
  rw [hReq, instantiateLevelParams_mkAppN] at hW
  obtain ⟨F0, hF0⟩ := Denotes.mkAppN_head hW
  simp only [Expr.instantiateLevelParams] at hF0
  obtain ⟨ciT, hfT⟩ : ∃ ci, env.find? sn = some ci := by
    cases hF0 with
    | const hf _ => exact ⟨_, hf⟩
  obtain ⟨cvT, capsT, rfl, -⟩ := hTst ciT hfT
  -- the projection law's ι clause
  obtain ⟨hlpsT, -, cvC', hfC', -, -, hlaw⟩ := M.proj_law sn i entry cvT capsT hP hfT
  rw [hC] at hfC'
  obtain ⟨rfl, -, -⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hfC')
  have hFT : Denotes M.cval env φ ρ₀ (.const sn us) (M.cval sn
      (Level.substFn φ (ConstantInfo.indInfo cvT capsT).toConstantVal.levelParams us)) :=
    .const hfT (by show us.length = cvT.levelParams.length; rw [hlpsT]; exact hus)
  obtain ⟨hproj, -⟩ := hlaw us φ ρ₀ _ K hus hFT (DenotesO.to_denotes hK rfl)
  have heq := hproj (Ix.Kernel.Model.towerGuardAt_of_sem hO5 hfire) σC R vs hlenvs hfit
  rw [heq]
  exact ⟨DenList.getD hvs hk, Gr.mkAppN_args hge' _ hmemk⟩

/-! ## Structure η at a compared type -/

/-- **Structure η at a compared type** (`DefEq.structEtaTy`): `b`'s type is `a`'s, the
structure at `a`'s levels and parameters, so the projection law's η clause makes `b` the
constructor at the parameters and `b`'s fields, which `b`'s projections denote and are
`a`'s fields. -/
theorem DefEq.structEtaTy_sound (hse : StoredEnv env) {d : Nat} {a b ta tb : Expr md}
    {c : Key md} {us : List Level} {cvc : ConstantVal md} {cnP cnF : Nat} {T : Key md}
    {cvT : ConstantVal md} {caps : IndCaps md}
    (hhead : a.getAppFn = .const c us) (hc : env.find? c = some (.ctorInfo cvc cnP cnF))
    (hlen : a.getAppArgs.length = cnP + cnF) (hT : env.find? T = some (.indInfo cvT caps))
    (heta : caps.eta = true) (hctor : caps.etaCtor = some c) (hpos : 0 < cnF)
    (hslots : towerSlotsAll env T cnF = true)
    (ha : InferIOS M φ d a ta)
    (hred : RedS M φ d ta (Expr.mkAppN (.const T us) (a.getAppArgs.take cnP)))
    (hcerts : CertsS M φ d true (cvT.type.instantiateLevelParams cvT.levelParams us)
      (a.getAppArgs.take cnP))
    (hb : InferIOS M φ d b tb) (hd : DefEqS M φ d tb ta)
    (hfs : DefEqListS M φ d ((List.range cnF).map fun i => .proj T i b)
      (a.getAppArgs.drop cnP)) :
    DefEqS M φ d b a := by
  have hslots' : (List.range cnF).all (fun j => (env.findProj? T j).isSome) = true := hslots
  have hslot : ∀ j, j < cnF → ∃ e, env.findProj? T j = some e := fun j hj =>
    Option.isSome_iff_exists.mp (List.all_eq_true.mp hslots' j (List.mem_range.mpr hj))
  obtain ⟨e0, he0⟩ := hslot 0 hpos
  obtain ⟨-, -, hTst, hCst⟩ := hse.tables T 0 e0 he0
  obtain ⟨cvT', capsT', hci, hetaT⟩ := hTst _ hT
  obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj hci
  obtain ⟨hec, -, -⟩ := hetaT heta
  rw [hctor] at hec
  obtain rfl := Option.some.inj hec
  obtain ⟨rfl, rfl, -, -⟩ := hCst cvc cnP cnF hc
  obtain ⟨hlpsT, ⟨bsT, hsT⟩, cvC', hfC', -, -, hlaw⟩ := M.proj_law T 0 e0 cvT caps he0 hT
  rw [hc] at hfC'
  obtain ⟨rfl, -, -⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hfC')
  have hoff : ∀ j ej, env.findProj? T j = some ej → ej.off = e0.off := by
    intro j ej hej
    obtain ⟨t1, h1, -, rfl⟩ := Env.findProj?_some hej
    obtain ⟨t0, h0, -, rfl⟩ := Env.findProj?_some he0
    rw [h1] at h0
    cases h0
    rfl
  intro hfb hfa σ hCb hCa x y hx hy hgb hga
  obtain ⟨hftb, hsubtb, kb⟩ := hb hfb
  obtain ⟨Tb, hTb, hgTb, hxTb⟩ := kb σ hCb x hx hgb
  obtain ⟨hfta, hsubta, ka⟩ := ha hfa
  obtain ⟨Ta, hTa, hgTa, -⟩ := ka σ hCa y hy hga
  have hCta : Ctx M φ σ ta := hCa.of_subset hsubta
  obtain rfl := hd hftb hfta σ (hCb.of_subset hsubtb) hCta Tb Ta hTb hTa hgTb hgTa
  obtain ⟨-, -, kW⟩ := hred hfta
  obtain ⟨hTW, hgW⟩ := kW σ hCta Tb hTa hgTa
  obtain ⟨F, ts, hF, hts, rfl⟩ := Den.mkAppN_inv hTW
  have hsp := eq_mkAppN_of_getAppFn hhead
  have hy' : Den M φ σ (Expr.mkAppN (.const e0.ctor us) a.getAppArgs) y := by
    rw [← hsp]; exact hy
  have hga' : Gr M φ σ (Expr.mkAppN (.const e0.ctor us) a.getAppArgs) := by
    rw [← hsp]; exact hga
  obtain ⟨K, vs, hK, hvs, rfl⟩ := Den.mkAppN_inv hy'
  have hlenT : us.length = cvT.levelParams.length := by
    cases hF with
    | const hf hl => rw [hT] at hf; cases hf; exact hl
  have hus : us.length = e0.levelParams.length := by rw [← hlpsT]; exact hlenT
  obtain ⟨TT, hcT, hTT, hgTT, hFT⟩ := const_typed (M := M) (φ := φ) hse.closed hT hlenT σ
  have htyF : (cvT.type.instantiateLevelParams cvT.levelParams us).hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]
    exact (hse.closed _ (List.mem_of_find?_eq_some hT)).1.1
  have hfargs := Frame.getAppArgs hfa
  have hfpar : ∀ z ∈ a.getAppArgs.take e0.numParams, Frame d z :=
    fun z hz => hfargs z (List.mem_of_mem_take hz)
  -- the parameters fit the structure's telescope
  have hwalk := hcerts (const_type_frame (d := d) (us := us) hse.closed hT).1 hfpar σ
    (Ctx.of_closed htyF) (fun z hz => hCa.getAppArgs z (List.mem_of_mem_take hz)) TT hTT hgTT
    ts hts (Gr.mkAppN_args hgW)
    (fun _ => ⟨F, by rw [DenotesO.functional hF hcT]; exact hFT, spineOk_of_graded hgW hF hts⟩)
  have hlenp : (a.getAppArgs.take e0.numParams).length = e0.numParams := by
    rw [List.length_take, hlen]; exact Nat.min_eq_left (Nat.le_add_right _ _)
  obtain ⟨σT, R, hfit⟩ := hwalk.fits hts (fun z hz => (hfpar z hz).2.1)
    (by
      rw [hlenp]
      exact Expr.stripPis_instantiateLevelParams_isSome _ _ _ (by rw [hsT]; rfl))
    htyF
  have htslen : ts.length = e0.numParams := by rw [← hts.length_eq, hlenp]
  -- `b` is the constructor at the parameters and its own fields
  obtain ⟨-, hηlaw⟩ := hlaw us φ ρ₀ F K hus (DenotesO.to_denotes hF rfl)
    (DenotesO.to_denotes hK rfl)
  have hxeta := hηlaw σT R ts x htslen hfit hxTb
  -- `b`'s projections denote its fields, and are `a`'s fields
  have hmemP : ∀ z ∈ (List.range e0.numFields).map (fun j => Expr.proj T j b),
      ∃ j, z = Expr.proj T j b := fun z hz => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hz
    exact ⟨j, rfl⟩
  have hpl : DenList M φ σ ((List.range e0.numFields).map fun j => Expr.proj T j b)
      ((List.range e0.numFields).map fun j => field (j + e0.off) x) := by
    refine DenList.map_mem _ fun j hj => ?_
    obtain ⟨ej, hej⟩ := hslot j (List.mem_range.mp hj)
    rw [← hoff j ej hej]
    exact .proj_table hej hx
  have hfeq := hfs.2
    (fun z hz => by obtain ⟨j, rfl⟩ := hmemP z hz; exact Frame.proj_iff.2 hfb)
    (fun z hz => hfargs z (List.mem_of_mem_drop hz)) σ
    (fun z hz => by
      obtain ⟨j, rfl⟩ := hmemP z hz
      exact hCb.of_subset fun l hl => by simpa [Expr.fvarLeaves] using hl)
    (fun z hz => hCa.getAppArgs z (List.mem_of_mem_drop hz)) _ _ hpl (hvs.drop _)
    (fun z hz => by obtain ⟨j, rfl⟩ := hmemP z hz; exact hgb)
    (fun z hz => Gr.mkAppN_args hga' z (List.mem_of_mem_drop hz))
  have htake : ts = vs.take e0.numParams := DenList.functional hts (hvs.take _)
  rw [hxeta, hfeq, htake, List.take_append_drop]

end Ix.Kernel.Open
