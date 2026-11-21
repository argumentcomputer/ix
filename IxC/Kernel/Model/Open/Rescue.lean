module

public import IxC.Kernel.Model.Open.Proj
import IxC.Kernel.Verify.Shift

@[expose] public section

/-!
# The rules' soundness over the public `Model`: the major premise's rescues

Each rescue (`Red.rescueK`, `Red.rescueAnd`, `Red.rescueEta`) fabricates a constructor
application and equates it with the major premise by its last premise (`DefEq fab major`).
So the reduction is sound once the fabrication denotes and is graded (`fab_sound`):

* its arguments denote and are graded: the parameters of the major's reduced type, and the
  major's projections (`.proj` nodes read through the table, or projection-function spines
  certified by their own walks);
* the fabrication's certificate walks the constructor's telescope, so each application in it
  is on its domain (`WalkFits.graded`);
* the rescue's scope guards frame it, inside the major's free variables.

No law of `Model` is read: the equation is the `DefEq` premise's.
-/

namespace Ix.Kernel.Open

open SetTheory Ix.Kernel.SetModel
open Ix.Kernel.Rules
open Ix.Kernel.Model.Rules (Frame LeavesSub)

universe w

variable {V : Type w} [SetTheory V] {env : Env md} {M : Model V env} {φ : LevelParam → Nat}

/-! ## Spines -/

theorem DenList.append {σ : Nat → V} : ∀ {as bs : List (Expr md)} {vs ws : List V},
    DenList M φ σ as vs → DenList M φ σ bs ws → DenList M φ σ (as ++ bs) (vs ++ ws)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons hx hxs, h => .cons hx (DenList.append hxs h)

theorem DenList.of_forall {σ : Nat → V} :
    ∀ (l : List (Expr md)), (∀ x ∈ l, ∃ w, Den M φ σ x w) → ∃ ws, DenList M φ σ l ws
  | [], _ => ⟨[], .nil⟩
  | x :: l, h => by
    obtain ⟨w, hw⟩ := h x List.mem_cons_self
    obtain ⟨ws, hws⟩ := DenList.of_forall l fun y hy => h y (List.mem_cons_of_mem _ hy)
    exact ⟨w :: ws, .cons hw hws⟩

/-- A head applied along its arguments denotes the head's value applied along theirs. -/
theorem Den.mkAppN {σ : Nat → V} : ∀ {as : List (Expr md)} {f : Expr md} {F : V} {vs : List V},
    Den M φ σ f F → DenList M φ σ as vs → Den M φ σ (Expr.mkAppN f as) (vs.foldl app F)
  | [], _, _, _, hF, .nil => hF
  | a :: as, f, _, _, hF, .cons hx hxs => by
    have h := Den.mkAppN (as := as) (f := .app f a) (DenotesO.app hF hx) hxs
    exact h

/-- **A walk grades the spine**: a member of the telescope's denotation, applied along the
walk's values, applies each function on its domain. -/
theorem WalkFits.graded {σ : Nat → V} {d : Nat} :
    ∀ {T : Expr md} {args : List (Expr md)} {vs : List V}, WalkFits M φ σ T args vs →
      ∀ {f : Expr md} {F TT : V}, Frame d T → (∀ x ∈ args, Frame d x) →
        Den M φ σ f F → Gr M φ σ f → Den M φ σ T TT → Gr M φ σ T → F ∈ˢ TT →
        DenList M φ σ args vs → (∀ x ∈ args, Gr M φ σ x) → Gr M φ σ (Expr.mkAppN f args) := by
  intro T args vs h
  induction h with
  | nil => intro f F TT _ _ _ hgf _ _ _ _ _; exact hgf
  | @cons ty body a mb as A x xs hA hx _ ih =>
    intro f F TT hfT hargs hF hgf hTT hgT hFT hvs hgargs
    cases hvs with
    | cons hxa hxs =>
      cases hTT with
      | pi hA' hB hP =>
        obtain rfl := DenotesO.functional hA hA'
        have hfa := hargs a List.mem_cons_self
        obtain ⟨hgapp, hBx, hgB, hmem⟩ := app_typed hfa hF hxa hgf (hgargs a List.mem_cons_self)
          hA hB hP hgT hFT hx
        exact ih (f := .app f a) ((Frame.pi_parts hfT).subst hfa).1
          (fun y hy => hargs y (List.mem_cons_of_mem _ hy)) (.app hF hxa) hgapp hBx hgB hmem hxs
          (fun y hy => hgargs y (List.mem_cons_of_mem _ hy))

/-- **A certified spine of a stored constant** (an unlicensed walk) denotes and is graded. -/
theorem certs_spine_sound (hsc : StoredClosed env) {d : Nat} {c : Key md} {us : List Level}
    {ci : ConstantInfo md} {args : List (Expr md)} {σ : Nat → V} {vs : List V}
    (hc : env.find? c = some ci) (hus : us.length = ci.toConstantVal.levelParams.length)
    (hcerts : CertsS M φ d false
      (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us) args)
    (hfargs : ∀ x ∈ args, Frame d x) (hCargs : ∀ x ∈ args, Ctx M φ σ x)
    (hvs : DenList M φ σ args vs) (hgargs : ∀ x ∈ args, Gr M φ σ x) :
    Den M φ σ (Expr.mkAppN (.const c us) args)
        (vs.foldl app (M.cval c (Level.substFn φ ci.toConstantVal.levelParams us))) ∧
      Gr M φ σ (Expr.mkAppN (.const c us) args) := by
  obtain ⟨TT, hcT, hTT, hgTT, hKT⟩ := const_typed (M := M) (φ := φ) hsc hc hus σ
  have htyF : (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams
      us).hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]
    exact (hsc _ (List.mem_of_find?_eq_some hc)).1.1
  have hfT := (const_type_frame (d := d) (us := us) hsc hc).1
  have hwalk := hcerts hfT hfargs σ (Ctx.of_closed htyF) hCargs TT hTT hgTT vs hvs hgargs
    (fun h => nomatch h)
  exact ⟨Den.mkAppN hcT hvs, hwalk.graded hfT hfargs hcT True.intro hTT hgTT hKT hvs hgargs⟩

/-! ## The fabrication -/

/-- **A fabricated constructor application equated with the major premise** is a sound
reduct of it, once its arguments denote and are graded wherever the major does. -/
theorem fab_sound (hsc : StoredClosed env) {d : Nat} {major : Expr md} {c : Key md}
    {us : List Level} {ci : ConstantInfo md} {args : List (Expr md)}
    (hc : env.find? c = some ci) (hus : us.length = ci.toConstantVal.levelParams.length)
    (hws : (Expr.mkAppN (.const c us) args).wscopedB d = true)
    (hlb : (Expr.mkAppN (.const c us) args).looseBVarsBounded 0 = true)
    (hleaves : (Expr.mkAppN (.const c us) args).fvarLeaves.all
      (fun l => major.fvarLeaves.contains l) = true)
    (hcerts : CertsS M φ d false
      (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us) args)
    (hargs : Frame d major → ∀ σ, Ctx M φ σ major → ∀ v, Den M φ σ major v →
      Gr M φ σ major → ∃ vs, DenList M φ σ args vs ∧ ∀ x ∈ args, Gr M φ σ x)
    (hfm : DefEqS M φ d (Expr.mkAppN (.const c us) args) major) :
    RedS M φ d major (Expr.mkAppN (.const c us) args) := by
  have hsub : LeavesSub (Expr.mkAppN (.const c us) args) major := fun l hl => by
    have := List.all_eq_true.mp hleaves l hl
    simpa using this
  have hmem : ∀ x ∈ args, x ∈ (Expr.mkAppN (.const c us) args).getAppArgs := fun x hx => by
    rw [Expr.getAppArgs_mkAppN]
    simpa [Expr.getAppArgs] using hx
  intro hfM
  have hfF : Frame d (Expr.mkAppN (.const c us) args) :=
    ⟨Expr.WScoped.of_wscopedB hws, hlb, fun l hl => hfM.2.2 l (hsub l hl)⟩
  refine ⟨hfF, hsub, fun σ hCM v hv hgM => ?_⟩
  have hCF : Ctx M φ σ (Expr.mkAppN (.const c us) args) := hCM.of_subset hsub
  obtain ⟨vs, hvs, hgargs⟩ := hargs hfM σ hCM v hv hgM
  obtain ⟨hdF, hgF⟩ := certs_spine_sound hsc hc hus hcerts
    (fun x hx => Frame.getAppArgs hfF x (hmem x hx)) (fun x hx => hCF.getAppArgs x (hmem x hx))
    hvs hgargs
  obtain rfl := hfm hfF hfM σ hCF hCM _ _ hdF hv hgF hgM
  exact ⟨hdF, hgF⟩

/-- **The parameters of the major's reduced type** are framed, satisfied, graded, and denote. -/
theorem majorType_spine {d : Nat} {major tm tmaj : Expr md} {T : Key md} {ust : List Level}
    (hmaj : InferIOS M φ d major tm) (hred : RedS M φ d tm tmaj)
    (hhead : tmaj.getAppFn = .const T ust) (hfM : Frame d major) {σ : Nat → V}
    (hCM : Ctx M φ σ major) {v : V} (hv : Den M φ σ major v) (hgM : Gr M φ σ major) :
    (∀ x ∈ tmaj.getAppArgs, Frame d x ∧ Ctx M φ σ x ∧ Gr M φ σ x) ∧
      ∃ ws, DenList M φ σ tmaj.getAppArgs ws := by
  obtain ⟨hftm, hsubtm, k⟩ := hmaj hfM
  obtain ⟨Tm, hTm, hgTm, -⟩ := k σ hCM v hv hgM
  have hCtm : Ctx M φ σ tm := hCM.of_subset hsubtm
  obtain ⟨hftj, hsubtj, kr⟩ := hred hftm
  obtain ⟨hTj, hgj⟩ := kr σ hCtm Tm hTm hgTm
  have hCtj : Ctx M φ σ tmaj := hCtm.of_subset hsubtj
  have hsp := eq_mkAppN_of_getAppFn hhead
  have hTj' : Den M φ σ (Expr.mkAppN (.const T ust) tmaj.getAppArgs) Tm := by
    rw [← hsp]; exact hTj
  have hgj' : Gr M φ σ (Expr.mkAppN (.const T ust) tmaj.getAppArgs) := by
    rw [← hsp]; exact hgj
  obtain ⟨-, ws, -, hws, -⟩ := Den.mkAppN_inv hTj'
  exact ⟨fun x hx => ⟨Frame.getAppArgs hftj x hx, hCtj.getAppArgs x hx,
    Gr.mkAppN_args hgj' x hx⟩, ws, hws⟩

/-! ## The three rescues -/

/-- **The K rescue** (`Red.rescueK`). -/
theorem Red.rescueK_sound (hsc : StoredClosed env) {d : Nat} {major tm tmaj fab : Expr md}
    {rl : RecRule md} {cvj : ConstantVal md} {cnP cnF : Nat} {T : Key md} {ust : List Level}
    (hctor : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (hmaj : InferIOS M φ d major tm) (hred : RedS M φ d tm tmaj)
    (hhead : tmaj.getAppFn = .const T ust) (hlv : cvj.levelParams.length = ust.length)
    (hfab : fab = Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP))
    (hws : fab.wscopedB d = true) (hlb : fab.looseBVarsBounded 0 = true)
    (hleaves : fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) = true)
    (hcerts : CertsS M φ d false (cvj.type.instantiateLevelParams cvj.levelParams ust)
      (tmaj.getAppArgs.take cnP))
    (hfm : DefEqS M φ d fab major) : RedS M φ d major fab := by
  subst hfab
  refine fab_sound hsc hctor hlv.symm hws hlb hleaves hcerts
    (fun hfM σ hCM v hv hgM => ?_) hfm
  obtain ⟨hparts, ws, hdl⟩ := majorType_spine hmaj hred hhead hfM hCM hv hgM
  exact ⟨ws.take cnP, hdl.take cnP, fun x hx => (hparts x (List.mem_of_mem_take hx)).2.2⟩

/-- **The `And` rescue** (`Red.rescueAnd`). -/
theorem Red.rescueAnd_sound (hsc : StoredClosed env) {d : Nat} {major tm tmaj fab : Expr md}
    {rl : RecRule md} {cvj : ConstantVal md} {cnP cnF : Nat} {ust : List Level}
    (hctor : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (hmaj : InferIOS M φ d major tm) (hred : RedS M φ d tm tmaj)
    (hhead : tmaj.getAppFn = .const andName ust) (hlv : cvj.levelParams.length = ust.length)
    (hslots : AndRescueSlotsSem env rl.ctor cnP ust)
    (hfab : fab = Expr.mkAppN (.const rl.ctor ust)
      (tmaj.getAppArgs ++ [.proj andName 0 major, .proj andName 1 major]))
    (hws : fab.wscopedB d = true) (hlb : fab.looseBVarsBounded 0 = true)
    (hleaves : fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) = true)
    (hcerts : CertsS M φ d false (cvj.type.instantiateLevelParams cvj.levelParams ust)
      (tmaj.getAppArgs ++ [.proj andName 0 major, .proj andName 1 major]))
    (hfm : DefEqS M φ d fab major) : RedS M φ d major fab := by
  subst hfab
  refine fab_sound hsc hctor hlv.symm hws hlb hleaves hcerts
    (fun hfM σ hCM v hv hgM => ?_) hfm
  obtain ⟨hparts, ws, hdl⟩ := majorType_spine hmaj hred hhead hfM hCM hv hgM
  obtain ⟨e0, he0, -⟩ := hslots 0 (by decide)
  obtain ⟨e1, he1, -⟩ := hslots 1 (by decide)
  refine ⟨ws ++ [_, _], hdl.append (.cons (.proj_table he0 hv) (.cons (.proj_table he1 hv) .nil)),
    fun x hx => ?_⟩
  rcases List.mem_append.mp hx with hx | hx
  · exact (hparts x hx).2.2
  · obtain rfl | rfl : x = .proj andName 0 major ∨ x = .proj andName 1 major := by
      simpa using hx
    · exact hgM
    · exact hgM

/-- **The structure-η rescue** (`Red.rescueEta`): the fabricated fields are the major's
projections, through the table or through the projection functions, whose spines their own
certificates walk. -/
theorem Red.rescueEta_sound (hse : StoredEnv env) {d : Nat} {major tm tmaj fab : Expr md}
    {recName : Key md} {cv : ConstantVal md} {mI rP : Nat} {rl : RecRule md}
    {cvj : ConstantVal md} {cnP cnF : Nat} {T : Key md} {tus ust : List Level}
    {cvT : ConstantVal md} {caps : IndCaps md}
    (hrec : env.find? recName = some (.recInfo cv mI rP [rl])) (heta : rl.eta = true)
    (hctor : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (hpres : (cvj.type.piResult).getAppFn = .const T tus)
    (hT : env.find? T = some (.indInfo cvT caps))
    (hmaj : InferIOS M φ d major tm) (hred : RedS M φ d tm tmaj)
    (hhead : tmaj.getAppFn = .const T ust) (hlv : ust.length = cvT.levelParams.length)
    (hfab : fab = Expr.mkAppN (.const rl.ctor ust)
      (etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields))
    (hws : fab.wscopedB d = true) (hlb : fab.looseBVarsBounded 0 = true)
    (hleaves : fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) = true)
    (hcerts : CertsS M φ d false (cvj.type.instantiateLevelParams cvj.levelParams ust)
      (etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields))
    (hpc : towerSlotsAll env T caps.etaFields = false →
      EtaProjCertsS M φ d T ust tmaj.getAppArgs major cvT.levelParams
        (List.range caps.etaFields))
    (hfm : DefEqS M φ d fab major) : RedS M φ d major fab := by
  subst hfab
  have hlpj : ust.length = cvj.levelParams.length := by
    rw [hse.etaRules recName cv mI rP [rl] rl hrec List.mem_cons_self heta cvj cnP cnF hctor T tus
      cvT caps hpres hT]
    exact hlv
  refine fab_sound hse.closed hctor hlpj hws hlb hleaves hcerts
    (fun hfM σ hCM v hv hgM => ?_) hfm
  obtain ⟨hparts, ws, hdl⟩ := majorType_spine hmaj hred hhead hfM hCM hv hgM
  have hprojs : ∀ x ∈ etaProjs env T ust tmaj.getAppArgs major caps.etaFields,
      (∃ w, Den M φ σ x w) ∧ Gr M φ σ x := by
    intro x hx
    unfold etaProjs at hx
    by_cases hts : towerSlotsAll env T caps.etaFields = true
    · rw [if_pos hts] at hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      have hts' : (List.range caps.etaFields).all (fun j => (env.findProj? T j).isSome) = true :=
        hts
      obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp hts' j hj)
      exact ⟨⟨_, .proj_table he hv⟩, hgM⟩
    · rw [if_neg hts] at hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      obtain ⟨cvp, mI', rP', rules', hfp, hlpp, -, hcp⟩ := hpc (by simpa using hts) j hj
      have hargs' : ∀ y ∈ tmaj.getAppArgs ++ [major], Frame d y ∧ Ctx M φ σ y ∧ Gr M φ σ y := by
        intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hparts y hy
        · rw [List.mem_singleton.mp hy]
          exact ⟨hfM, hCM, hgM⟩
      obtain ⟨hden, hgr⟩ := certs_spine_sound hse.closed hfp
        (show ust.length = cvp.levelParams.length by rw [hlpp]; exact hlv) hcp
        (fun y hy => (hargs' y hy).1) (fun y hy => (hargs' y hy).2.1)
        (hdl.append (.cons hv .nil)) (fun y hy => (hargs' y hy).2.2)
      exact ⟨⟨_, hden⟩, hgr⟩
  obtain ⟨ps, hps⟩ := DenList.of_forall _ fun x hx => (hprojs x hx).1
  show ∃ vs, DenList M φ σ
      (tmaj.getAppArgs ++ etaProjs env T ust tmaj.getAppArgs major caps.etaFields) vs ∧
    ∀ x ∈ tmaj.getAppArgs ++ etaProjs env T ust tmaj.getAppArgs major caps.etaFields,
      Gr M φ σ x
  refine ⟨ws ++ ps, hdl.append hps, fun x hx => ?_⟩
  rcases List.mem_append.mp hx with hx | hx
  · exact (hparts x hx).2.2
  · exact (hprojs x hx).2

end Ix.Kernel.Open
