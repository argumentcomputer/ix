import Ix.Cert.ValueFits
import IxC.Kernel.Model.WellDenotedTransport
import IxC.Kernel.Model.Inductives.FixRecRead

/-! # Strong models satisfy the value-level Source laws

A strong model of an environment (`Ix.Kernel.Cached.StrongModel`) satisfies the
value-level recursor rules and capability laws of that environment
(`RecRuleLaws`, `CapabilityLaws`) at its own public values. Each public law is
read off the matching law of the model's internal invariant:
* the recursor rules from `RecRuleLaw` (through `StrongModel.rec_rule`);
* structure η from `EtaLaw` (projection-function families) or `TowerEtaLaw`
  (families with a projection table);
* unit-likeness from `UnitLaw`;
* the projection law from the tower entry's law (`TowerEntryLaw`).

The arguments the internal laws take are readings. The proof takes bound
variables, read at an ambient valuation that lists the given values:
* the recursor's leading arguments at the bottom, as the stored instantiations of
  a nested rule expect them;
* the constructor's arguments next;
* the recursor's indices above them.

Public fits become internal fits (`Ix.Cert.ValueFits`). The indices are read off
the constructor's residual type, the nested instantiations off their canonical
opening, and the public denotations of both match their readings through the
kernel's bridge (`Model.Denotes_of_denoteMeta`). -/

namespace Ix.Cert.StrongValueLaws

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model Ix.Kernel.SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel.Expr (closeN)
open Ix.Kernel.Term
open Ix.Cert.ValueFits

universe w

variable {md : Mode} {V : Type w} [SetTheory V] {env : Env md}

/-! ## Readings of stored types -/

/-- **A stored constant's type, at level arguments, reads graded**, and has no free
or loose bound variable. -/
theorem typeReading (M : Cached.StrongModel V env) {k : Key md} {ci : Ix.Kernel.ConstantInfo md}
    (hf : env.find? k = some ci) (φ : LevelParam → Nat) (us : List Ix.Kernel.Level) :
    ∃ ta, denoteMeta M.internal.base2.acval env φ 0
        (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us) = some ta ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
      (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us).hasFvar
        = false ∧
      (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us).looseBVarsBounded
        0 = true := by
  have hmem := Semantics.Env.find?_mem hf
  obtain ⟨ta, hta⟩ := M.internal.type_reads ci hmem
    (Ix.Kernel.Level.substFn φ ci.toConstantVal.levelParams us)
  have hwf := M.internal.base2.wf ci hmem
  refine ⟨ta, ?_, M.internal.type_wellDenotedV ci hmem _ ta hta, ?_, ?_⟩
  · rw [denotePInstLevels]
    exact hta
  · rw [Expr.hasFvar_instantiateLevelParams]
    exact hwf.1
  · rw [Expr.looseBVarsBounded_instantiateLevelParams]
    exact hwf.2.2.2.1

/-! ## Lists of bound variables -/

/-- A bound variable is graded. -/
theorem wellDenotedV_bvar (ρ : Nat → V) (i : Nat) : WellDenotedV V ρ (.bvar i) :=
  ⟨by simp, by simp⟩

/-- A list's `getD` inside its range is its element. -/
theorem getD_of_lt {α : Type _} {l : List α} {i : Nat} (d : α) (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- Interpreting a list member is taking the interpreted list's member. -/
theorem interp_getD {ρ : Nat → V} {as : List AnnotTerm} {i : Nat} (h : i < as.length) :
    interp V ρ (as.getD i default) = (as.map (interp V ρ)).getD i SetTheory.empty := by
  rw [getD_of_lt _ h, getD_of_lt _ (by simpa using h), List.getElem_map]

/-- An application spine of readings interprets to the value spine. -/
theorem interp_mkAppN_spine (ρ : Nat → V) (f : AnnotTerm) (as : List AnnotTerm) :
    interp V ρ (AnnotTerm.mkAppN f as) = spineV (interp V ρ f) (as.map (interp V ρ)) := by
  rw [interp_mkAppN, spineV, List.foldl_map]

/-! ## Instantiating the canonical opening -/

theorem fvarsBelow_instSeq_openFvars :
    ∀ (m j D t : Nat) (e : Ix.Kernel.Expr md), j + m ≤ D → Expr.fvarsBelow D e →
      Expr.fvarsBelow D (Expr.instSeq (Verify.openFvars j m) t e)
  | 0, _, _, _, _, _, he => he
  | m + 1, j, D, t, e, hle, he => by
    rw [Verify.openFvars_succ]
    exact fvarsBelow_instSeq_openFvars m (j + 1) D (t - 1) _ (by omega)
      (Expr.fvarsBelow_instantiate1_gen (by simp only [Expr.fvarsBelow]; omega) t he)

theorem looseBVarsBounded_instSeq_openFvars :
    ∀ (m j : Nat) (e : Ix.Kernel.Expr md), e.looseBVarsBounded m = true →
      (Expr.instSeq (Verify.openFvars j m) (m - 1) e).looseBVarsBounded 0 = true
  | 0, _, _, he => he
  | m + 1, j, e, he => by
    rw [Verify.openFvars_succ, show m + 1 - 1 = m from by omega]
    exact looseBVarsBounded_instSeq_openFvars m (j + 1) _
      (Ix.Kernel.looseBVarsBounded_instantiate1 e m he)

/-! ## The recursor rules -/

section Iota

variable (M : Cached.StrongModel V env)

/-- The ambient valuation of the ι law: the `rP` leading arguments at the bottom
(innermost last), the `n` constructor arguments next (innermost last), the
recursor's indices above. -/
noncomputable def iotaVal (rP n : Nat) (xs ys : List V) (i : Nat) : V :=
  if i < rP then xs.getD (rP - 1 - i) SetTheory.empty
  else if i < rP + n then ys.getD (rP + n - 1 - i) SetTheory.empty
  else xs.getD (i - n) SetTheory.empty

/-- The recursor's arguments as bound variables of `iotaVal`. -/
def iotaXs (rP n mI : Nat) : List AnnotTerm :=
  (List.range mI).map fun j => if j < rP then AnnotTerm.bvar (rP - 1 - j) else AnnotTerm.bvar (n + j)

/-- The constructor's arguments as bound variables of `iotaVal`. -/
def iotaYs (rP n : Nat) : List AnnotTerm :=
  (List.range n).map fun k => AnnotTerm.bvar (rP + n - 1 - k)

theorem iotaXs_interp {rP n mI : Nat} {xs ys : List V} (hxl : xs.length = mI) :
    (iotaXs rP n mI).map (interp V (iotaVal rP n xs ys)) = xs := by
  apply List.ext_getElem (by simp [iotaXs, hxl])
  intro j h1 h2
  simp only [iotaXs, List.getElem_map, List.getElem_range, List.length_map, List.length_range]
    at h1 ⊢
  by_cases hj : j < rP
  · rw [ite_eq_left hj, interp_bvar]
    simp only [iotaVal, ite_eq_left (show rP - 1 - j < rP from by omega),
      show rP - 1 - (rP - 1 - j) = j from by omega]
    exact getD_of_lt _ h2
  · rw [ite_eq_right hj, interp_bvar]
    simp only [iotaVal, ite_eq_right (show ¬ n + j < rP from by omega),
      ite_eq_right (show ¬ n + j < rP + n from by omega), show n + j - n = j from by omega]
    exact getD_of_lt _ h2

theorem iotaYs_interp {rP : Nat} {xs ys : List V} :
    (iotaYs rP ys.length).map (interp V (iotaVal rP ys.length xs ys)) = ys := by
  apply List.ext_getElem (by simp [iotaYs])
  intro k h1 h2
  simp only [iotaYs, List.getElem_map, List.getElem_range, List.length_map, List.length_range]
    at h1 ⊢
  rw [interp_bvar]
  simp only [iotaVal, ite_eq_right (show ¬ rP + ys.length - 1 - k < rP from by omega),
    ite_eq_left (show rP + ys.length - 1 - k < rP + ys.length from by omega),
    show rP + ys.length - 1 - (rP + ys.length - 1 - k) = k from by omega]
  exact getD_of_lt _ h2

theorem openFvars_scoped {j m D : Nat} (h : j + m ≤ D) :
    ∀ a ∈ Verify.openFvars (md := md) j m, Expr.WScoped D a ∧ a.looseBVarsBounded 0 = true := by
  intro a ha
  obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp ha
  exact ⟨openFvars_WScoped h q a hq, Verify.openFvars_bounded j m a ha⟩

/-- `iotaVal` above the leading arguments is the constructor's arguments, then
the indices: shifted past the leading arguments, it is the constructor's
arguments pushed onto the indices. -/
theorem iotaVal_shift {rP : Nat} {xs ys : List V} :
    shiftE rP 0 (iotaVal rP ys.length xs ys) =
      consN ys (fun i => iotaVal rP ys.length xs ys (i + rP + ys.length)) := by
  funext i
  rw [shiftE_zero]
  by_cases hi : i < ys.length
  · have h := consN_getElem? ys (fun i => iotaVal rP ys.length xs ys (i + rP + ys.length)) i hi
    rw [List.getElem?_eq_getElem (by omega)] at h
    rw [← Option.some.inj h]
    simp only [iotaVal, ite_eq_right (show ¬ i + rP < rP from by omega),
      ite_eq_left (show i + rP < rP + ys.length from by omega),
      show rP + ys.length - 1 - (i + rP) = ys.length - 1 - i from by omega]
    exact getD_of_lt _ (by omega)
  · have h := consN_shift ys (fun i => iotaVal rP ys.length xs ys (i + rP + ys.length))
      (i - ys.length)
    rw [show i - ys.length + ys.length = i from by omega] at h
    rw [h, show i - ys.length + rP + ys.length = i + rP from by omega]

/-- **A strong model satisfies each fired rule's value-level law.** -/
theorem recRuleLaw {c : Key md} {cv : Ix.Kernel.ConstantVal md} {mI rP : Nat}
    {rules : List (Ix.Kernel.RecRule md)} (hfind : env.find? c = some (.recInfo cv mI rP rules))
    {rl : Ix.Kernel.RecRule md} (hrl : rl ∈ rules) (hfire : rl.fire ≠ .inert) :
    RecRuleLaw M.model.cval env c cv mI rP rl := by
  intro φ us hus cvj cnP cnF hctor usj husj hlv ρ ρx ρy Rx Ry xs ys hxl hyl hfy hfx hpar hnest
    hidxl hidx R hR
  have hcl := M.internal.base2.cval_closedL
  have hacl := M.internal.base2.acval_closed
  have hainst : ∀ (n : Key md) (ψ : LevelParam → Nat) (y : AnnotTerm) (k : Nat),
      (M.internal.base2.acval n ψ).inst y k = M.internal.base2.acval n ψ :=
    fun n ψ y k => acval_inst_self M.internal.base2 n ψ y k
  obtain ⟨hrP, hlaw⟩ := M.rec_rule φ hfind hrl hfire
  obtain ⟨Ra, hRa, -, hnestG, hmain⟩ := hlaw us hus
  have hmem := Semantics.Env.find?_mem hfind
  have hwfr := (M.internal.base2.wf _ hmem).2.2.2.2.2.1 cv mI rP rules rfl rl hrl
  -- the ambient valuation and the bound-variable arguments
  have hxint : (iotaXs rP ys.length mI).map (interp V (iotaVal rP ys.length xs ys)) = xs :=
    iotaXs_interp hxl
  have hyint : (iotaYs rP ys.length).map (interp V (iotaVal rP ys.length xs ys)) = ys :=
    iotaYs_interp
  have hxlen : (iotaXs rP ys.length mI).length = mI := by simp [iotaXs]
  have hylen : (iotaYs rP ys.length).length = ys.length := by simp [iotaYs]
  have hmaj : interp V (iotaVal rP ys.length xs ys)
      (AnnotTerm.mkAppN (M.internal.base2.acval rl.ctor (Ix.Kernel.Level.substFn φ cvj.levelParams usj))
        (iotaYs rP ys.length)) =
      spineV (M.model.cval rl.ctor (Ix.Kernel.Level.substFn φ cvj.levelParams usj)) ys := by
    rw [interp_mkAppN_spine, hyint, interp_cvalOf hcl]
    rfl
  -- the two types' readings
  obtain ⟨TVa, hTVa, hTVagr, hnfa, hlba⟩ := typeReading M hfind φ us
  obtain ⟨TVja, hTVja, hTVjagr, hnfj, hlbj⟩ := typeReading M hctor φ usj
  -- the public fits are internal fits
  obtain ⟨restXv, hfitXv⟩ := teleFit_of_fits_closed hcl hTVa hnfa hlba hTVagr hfx
    (iotaVal rP ys.length xs ys)
  obtain ⟨restR, hfitXPA⟩ := teleFitPA_of_teleFit
    (as := iotaXs rP ys.length mI ++ [AnnotTerm.mkAppN
      (M.internal.base2.acval rl.ctor (Ix.Kernel.Level.substFn φ cvj.levelParams usj))
      (iotaYs rP ys.length)])
    (by
      have h := piChain_of_teleFit hfitXv
      simpa [hxlen, hxl] using h)
    (by
      rw [List.map_append, hxint, List.map_cons, List.map_nil, hmaj]
      exact hfitXv)
  obtain ⟨restYv, hfitYv⟩ := teleFit_of_fits_closed hcl hTVja hnfj hlbj hTVjagr hfy
    (iotaVal rP ys.length xs ys)
  obtain ⟨restC, hfitYPA⟩ := teleFitPA_of_teleFit (as := iotaYs rP ys.length)
    (by
      have h := piChain_of_teleFit hfitYv
      simpa [hylen] using h)
    (by rw [hyint]; exact hfitYv)
  -- the parameters
  have hpar' : rl.paramsBlind = false → rl.fire = .plain →
      ∀ i, i < rl.ctorParams → i < mI →
        interp V (iotaVal rP ys.length xs ys) ((iotaYs rP ys.length).getD i default) =
          interp V (iotaVal rP ys.length xs ys) ((iotaXs rP ys.length mI).getD i default) := by
    intro hb hp i hi him
    rw [interp_getD (by omega), interp_getD (by omega), hyint, hxint]
    exact hpar hb hp i hi him
  -- the nested instantiations
  have hnest' : ∀ lvls pins, rl.fire = .nested lvls pins → ∀ i, i < rl.ctorParams →
      ∀ vpa : AnnotTerm, denoteMeta M.internal.base2.acval env φ rP
          (Verify.openRev 0 rP ((pins.getD i default).instantiateLevelParams cv.levelParams us))
          = some vpa →
        interp V (iotaVal rP ys.length xs ys) ((iotaYs rP ys.length).getD i default) =
          interp V (iotaVal rP ys.length xs ys)
            (AnnotTerm.instRevChain ((iotaXs rP ys.length mI).take rP) vpa) := by
    intro lvls pins hnf i hi vpa hvpa
    obtain ⟨-, -, hpins, -⟩ := hwfr.2.2.2.2 lvls pins hnf
    have hpinF : ((pins.getD i default).instantiateLevelParams cv.levelParams us).hasFvar = false ∧
        ((pins.getD i default).instantiateLevelParams cv.levelParams us).looseBVarsBounded rP
          = true := by
      by_cases hil : i < pins.length
      · obtain ⟨h1, -, -, h4⟩ := hpins (pins.getD i default)
          (by rw [getD_of_lt _ hil]; exact List.getElem_mem hil)
        exact ⟨by rw [Expr.hasFvar_instantiateLevelParams]; exact h1,
          by rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact h4⟩
      · have hd : pins.getD i default = .bvar 0 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
          rfl
        rw [hd] at hvpa ⊢
        rcases Nat.eq_zero_or_pos rP with h0 | hpos
        · subst h0
          simp [Verify.openRev, Expr.instantiateLevelParams, denoteMeta] at hvpa
        · simp [Expr.instantiateLevelParams, Expr.hasFvar, Ix.Kernel.Expr.looseBVarsBounded, hpos]
    -- the grading of the instantiated reading
    obtain ⟨vpa', hvpa', hgr⟩ := hnestG lvls pins hnf i hi
    obtain rfl : vpa = vpa' := Option.some.inj (hvpa.symm.trans hvpa')
    have hxtake : ((iotaXs rP ys.length mI).take rP) =
        (List.range rP).map fun q => AnnotTerm.bvar (rP - 1 - (0 + q)) := by
      apply List.ext_getElem (by simp [iotaXs]; omega)
      intro q h1 h2
      simp only [iotaXs, List.getElem_take, List.getElem_map, List.getElem_range]
      have hq : q < rP := by simpa using h2
      rw [ite_eq_left hq, Nat.zero_add]
    have hgrad : WellDenotedV V (iotaVal rP ys.length xs ys)
        (AnnotTerm.instRevChain ((iotaXs rP ys.length mI).take rP) vpa) := by
      obtain ⟨mid, hmid⟩ := TeleFitPA.take hfitXPA rP
      rw [List.take_append_of_le_length (by omega)] at hmid
      refine hgr _ _ TVa mid (by simp [iotaXs]; omega) ?_ hTVa hmid
      intro z hz
      rw [hxtake] at hz
      obtain ⟨q, -, rfl⟩ := List.mem_map.mp hz
      exact wellDenotedV_bvar _ _
    -- the instantiated reading, through the canonical opening
    have hsp : DenoteMetaSpine M.internal.base2.acval env φ rP (Verify.openFvars 0 rP)
        ((iotaXs rP ys.length mI).take rP) := by
      rw [hxtake]
      exact denoteMetaSpine_openFvars rP 0 rP (by omega)
    have hkey := Rules.denoteMeta_openRev hacl hainst (Verify.openFvars 0 rP)
      (e := (pins.getD i default).instantiateLevelParams cv.levelParams us) (d := rP)
      (fun a ha => ⟨(openFvars_scoped (j := 0) (m := rP) (D := rP) (by omega) a ha).1,
        (openFvars_scoped (j := 0) (m := rP) (D := rP) (by omega) a ha).2⟩)
      (Expr.WScoped.of_not_hasFvar hpinF.1).fvarsBelow
      (by rw [Verify.openFvars_length]; exact hpinF.2) hsp
    have hbase := Rules.denoteMeta_openRev_base (env := env) (φ := φ)
      (cval := fun n ψ => (M.internal.base2.acval n ψ).erase)
      hacl (fun _ _ => rfl) hcl hpinF.1 hpinF.2 rP
    rw [Verify.openFvars_length, hbase, hvpa] at hkey
    -- the public denotation of the stored instantiation
    have hden := Denotes_of_denoteMeta (V := V) hcl rP _ hkey
      (fvarsBelow_instSeq_openFvars rP 0 rP (rP - 1) _ (by omega)
        (Expr.WScoped.of_not_hasFvar hpinF.1).fvarsBelow)
      (looseBVarsBounded_instSeq_openFvars rP 0 _ hpinF.2) _ hgrad
    have hcl' := closeN_instSeq_openFvars rP 0 _ (Expr.WScoped.of_not_hasFvar hpinF.1).fvarsBelow
      hpinF.2
    rw [Nat.zero_add, Expr.closeN_of_hasFvar _ 0 rP hpinF.1] at hcl'
    rw [hcl'] at hden
    have hpub := Denotes.congr_below (hnest lvls pins hnf i hi) rP (iotaVal rP ys.length xs ys)
      hpinF.2 (fun j hj => by simp only [iotaVal, leadVal, ite_eq_left hj])
    rw [interp_getD (by omega), hyint]
    exact Denotes_functional hpub hden
  -- the indices
  have hidx' : IotaIndexPin (V := V) (iotaVal rP ys.length xs ys) restC rl.ctorParams mI rP
      (iotaXs rP ys.length mI) := by
    by_cases hmr : mI = rP
    · exact ⟨restC, [], rfl, Or.inl hmr, fun i hi => absurd hi (by omega)⟩
    · -- the constructor's residual type, read at the ambient depth
      obtain ⟨-, args, eR, taR, hlen, hshape, hargs, hpr, hweR, hlbR, hRy, hrd, hgrR, hagree⟩ :=
        fits_read hcl ys 0 _ (fun i => iotaVal rP ys.length xs ys (i + rP + ys.length)) ρ ρy Ry
          hTVja (Expr.WScoped.of_not_hasFvar hnfj) hlbj (hTVjagr _)
          (fun _ h => absurd h (Nat.not_lt_zero _))
          (by rw [Expr.closeN_of_hasFvar _ 0 0 hnfj]; exact hfy)
      simp only [Nat.zero_add] at hshape hargs hweR hRy hrd hagree
      have hTVjaD : denoteMeta M.internal.base2.acval env φ (rP + ys.length)
          (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TVja :=
        denoteMeta_depth_of_closed hacl hnfj
          (fun k => denoteMeta_closed (cval := fun n ψ => (M.internal.base2.acval n ψ).erase)
            (fun _ _ => rfl) hcl hnfj hlbj hTVja 1 k) hTVja (rP + ys.length)
      have hspY : DenoteMetaSpine M.internal.base2.acval env φ (rP + ys.length) args
          (iotaYs rP ys.length) := by
        refine DenoteMetaSpine.of_getD args _ (by rw [hlen, hylen]) ?_
        intro q hq
        rw [hlen] at hq
        obtain ⟨ty, hty⟩ := hshape q hq
        rw [List.getD_eq_getElem?_getD, hty, Option.getD_some, denoteMeta_fvar,
          getD_of_lt _ (by rw [hylen]; exact hq)]
        simp [iotaYs]
      have hres := Rules.teleFitPA_residualK hacl hainst (ρ := iotaVal rP ys.length xs ys)
        (d := rP + ys.length) args hpr (Expr.WScoped.of_not_hasFvar hnfj)
        (fun a ha => ⟨((hargs a ha).1).mono (by omega), (hargs a ha).2⟩) hTVjaD hspY hfitYPA
      have hlift := denoteMeta_lift (env := env) (φ := φ) hacl hweR (rP + ys.length) (by omega)
      rw [hres, hrd, show rP + ys.length - ys.length = rP from by omega] at hlift
      have hrestC : restC = taR.liftN rP 0 := Option.some.inj hlift
      obtain ⟨fa, vsR, hfa, hspR, rfl⟩ := denoteMeta_mkAppN_inv
        (by rw [Ix.Kernel.Expr.mkAppN_getApp]; exact hrd)
      have hlenR : Ry.getAppArgs.length = eR.getAppArgs.length := by
        rw [hRy, getAppArgs_closeN, List.length_map]
      refine ⟨fa.liftN rP 0, vsR.map fun a => a.liftN rP 0, by rw [hrestC, liftN_mkAppN], ?_, ?_⟩
      · right
        rw [List.length_map, ← hspR.length, ← hlenR]
        exact hidxl.resolve_left hmr
      · intro i hi
        have hj : rl.ctorParams + i < eR.getAppArgs.length := by
          have h := hidxl.resolve_left hmr
          rw [hlenR] at h
          omega
        have hjv : rl.ctorParams + i < vsR.length := by rw [← hspR.length]; exact hj
        -- the index argument's reading, and its public denotation
        have hread := hspR.getD_read hj
        have hgr := wellDenotedV_mkAppN_args vsR fa hgrR (vsR.getD (rl.ctorParams + i) default)
          (by rw [getD_of_lt _ hjv]; exact List.getElem_mem hjv)
        have hmemArg : eR.getAppArgs.getD (rl.ctorParams + i) (.bvar 0) ∈ eR.getAppArgs := by
          rw [getD_of_lt _ hj]; exact List.getElem_mem hj
        have hwArg := Ix.Kernel.Expr.WScoped.getAppArgs hweR _ hmemArg
        have hlbArg := looseBVarsBounded_getAppArgs hlbR _ hmemArg
        have hden := Denotes_of_denoteMeta (V := V) hcl ys.length _ hread hwArg.fvarsBelow hlbArg
          _ hgr
        have hclA : closeN ys.length (eR.getAppArgs.getD (rl.ctorParams + i) (.bvar 0)) 0 =
            Ry.getAppArgs.getD (rl.ctorParams + i) (.bvar 0) := by
          rw [hRy, getAppArgs_closeN, getD_of_lt _ hj, getD_of_lt _ (by simpa using hj),
            List.getElem_map]
        have hden' := Denotes.congr_below hden ys.length ρy
          (by simpa using closeN_looseBVarsBounded ys.length _ 0 hwArg.fvarsBelow hlbArg)
          (fun k hk => (hagree k hk).symm)
        rw [hclA] at hden'
        rw [getD_of_lt _ (by simpa using hjv), List.getElem_map, interp_liftN, iotaVal_shift,
          ← getD_of_lt default hjv, interp_getD (as := iotaXs rP ys.length mI) (by rw [hxlen]; omega),
          hxint]
        exact Denotes_functional hden' (hidx i hi)
  have heq := (hmain cvj cnP cnF hctor usj (iotaVal rP ys.length xs ys) (iotaXs rP ys.length mI)
    (iotaYs rP ys.length) TVa TVja restR restC hxlen (by rw [hylen, hyl]) husj hlv hpar' hnest'
    hidx' hTVa hTVja hfitXPA hfitYPA).1
  rw [interp_mkAppN_spine, interp_mkAppN_spine, interp_cvalOf hcl, List.map_append, hxint,
    List.map_cons, List.map_nil, hmaj, List.map_append, List.map_take, List.map_drop, hxint,
    hyint] at heq
  -- the right-hand side's public denotation is its reading's
  obtain ⟨Ra', hRa', -, hrhs⟩ := M.rec_rhs φ hfind hrl hfire us hus
  obtain rfl : Ra' = Ra := Option.some.inj (hRa'.symm.trans hRa)
  have hrlb : (rl.rhs.instantiateLevelParams cv.levelParams us).looseBVarsBounded 0 = true := by
    rw [Expr.looseBVarsBounded_instantiateLevelParams]
    exact hwfr.2.2.2.1
  have hRv : R = interp V (iotaVal rP ys.length xs ys) Ra' :=
    Denotes_functional (Denotes.congr_closed hR hrlb _) (hrhs _)
  rw [hRv]
  exact heq

end Iota

/-! ## The capability laws -/

section Caps

variable (M : Cached.StrongModel V env)

/-- **A head applied to fitting arguments is graded.** -/
theorem wellDenotedV_spine {ρ : Nat → V} :
    ∀ {σ : Nat → V} {T : AnnotTerm} {vals : List V} {rest : V}, TeleFit V σ T vals rest →
      WellDenotedV V σ T → ∀ (f : AnnotTerm) (as : List AnnotTerm), as.map (interp V ρ) = vals →
      (∀ a ∈ as, WellDenotedV V ρ a) → WellDenotedV V ρ f → interp V ρ f ∈ˢ interp V σ T →
      WellDenotedV V ρ (AnnotTerm.mkAppN f as) := by
  intro σ T vals rest h
  induction h with
  | nil =>
    intro _ f as has _ hf _
    obtain rfl : as = [] := List.map_eq_nil_iff.mp has
    exact hf
  | @cons σ u v A B x xs rest hx _ ih =>
    intro hT f as has hga hf hmem
    match as, has with
    | a :: as', has =>
      simp only [List.map_cons, List.cons.injEq] at has
      obtain ⟨hax, has'⟩ := has
      obtain ⟨hw1, hw2⟩ := hT
      rw [WellDenoted_pi] at hw1
      rw [AnnotValid_pi] at hw2
      rw [interp_pi] at hmem
      have hga' : WellDenotedV V ρ a := hga a (by simp)
      have hfa : WellDenotedV V ρ (.app f a) := by
        refine ⟨?_, ?_⟩
        · rw [WellDenoted_app]
          exact ⟨hf.1, hga'.1, v, interp V σ A, fun y => interp V (cons y σ) B, hmem,
            by rw [hax]; exact hx, hw2.2.2⟩
        · rw [AnnotValid_app]
          exact ⟨hf.2, hga'.2⟩
      refine ih ⟨hw1.2 x hx, hw2.2.1 x hx⟩ (.app f a) as' has'
        (fun b hb => hga b (by simp [hb])) hfa ?_
      rw [interp_app, hax]
      exact SetModel.app_mem_piR hmem hx hw2.2.2

/-- **A strong model satisfies structure η at the level of values.** -/
theorem etaLaw {T : Key md} {cvT : Ix.Kernel.ConstantVal md} {caps : Ix.Kernel.IndCaps md}
    (hT : env.find? T = some (.indInfo cvT caps)) (heta : caps.eta = true)
    (hres : reservedBasisNames.contains T = false)
    (hslots : (towerSlotsAll env T caps.etaFields || recSlotsAll env T caps.etaFields) = true) :
    EtaLaw M.model.cval env T cvT caps := by
  intro C hC hCres hCstored φ us hus ρ ρ' R ts x htl hfit hx
  have hcl := M.internal.base2.cval_closedL
  obtain ⟨_, -, -, hnf, hlb⟩ := typeReading M hT φ us
  by_cases htw : towerSlotsAll env T caps.etaFields = true ∧ 0 < caps.etaFields
  · -- a family with a projection table: the tower's η law
    obtain ⟨htw, hpos⟩ := htw
    have h0 : (env.findProj? T 0).isSome = true := by
      unfold towerSlotsAll at htw
      exact List.all_eq_true.mp htw 0 (List.mem_range.mpr hpos)
    obtain ⟨entry, hentry⟩ := Option.isSome_iff_exists.mp h0
    obtain ⟨-, -, -, ⟨cvT', capsT', hT', hlps, hcaps⟩, -, -, -, -, -, htowerEta⟩ :=
      M.internal.tower_ok φ T 0 entry hentry
    rw [hT] at hT'
    cases hT'
    obtain ⟨-, hCe, hpe, hfe⟩ := hcaps heta
    rw [hC] at hCe
    obtain rfl : C = entry.ctor := Option.some.inj hCe
    obtain ⟨TVa, hTVa, hTVagr, hlaw⟩ := htowerEta cvT caps hT us (by rw [← hlps]; exact hus)
    obtain ⟨rest, hfitV⟩ := teleFit_of_fits_closed hcl hTVa hnf hlb hTVagr hfit
      (fun _ => SetTheory.empty)
    have hx' : x ∈ˢ ts.foldl SetTheory.app (interp V (fun _ => SetTheory.empty)
        (M.internal.base2.acval T (Ix.Kernel.Level.substFn φ entry.levelParams us))) := by
      rw [interp_cvalOf hcl, ← hlps]
      exact hx
    have h := hlaw _ ts rest x (by rw [htl, hpe]) hfitV hx'
    rw [interp_cvalOf hcl, ← hlps] at h
    refine h.trans ?_
    rw [spineV, etaFieldVals, ite_eq_left htw, hentry, Option.map_some, Option.getD_some, hfe]
    simp only [field_eq_projS]
    rfl
  · -- a family with projection functions: the modeled η law
    have hstored : EtaFamilyStored env T caps := by
      refine ⟨C, hC, hCres, hCstored, fun j hj => ?_⟩
      have hrec : recSlotsAll env T caps.etaFields = true := by
        cases htw' : towerSlotsAll env T caps.etaFields
        · simpa [htw'] using hslots
        · exact absurd ⟨htw', by omega⟩ htw
      unfold recSlotsAll at hrec
      have h := List.all_eq_true.mp hrec j (List.mem_range.mpr hj)
      split at h
      · rename_i cv mI rP rules hfj
        exact ⟨cv, mI, rP, rules, hfj⟩
      · exact absurd h (by simp)
    obtain ⟨TVa, hTVa, hTVagr, hlaw⟩ := M.internal.caps_ok.1 T cvT caps hT heta hres hstored φ C hC
      us hus
    obtain ⟨rest, hfitV⟩ := teleFit_of_fits_closed hcl hTVa hnf hlb hTVagr hfit
      (fun _ => SetTheory.empty)
    have hx' : x ∈ˢ ts.foldl SetTheory.app (interp V (fun _ => SetTheory.empty)
        (M.internal.base2.acval T (Ix.Kernel.Level.substFn φ cvT.levelParams us))) := by
      rw [interp_cvalOf hcl]
      exact hx
    have h := hlaw _ ts rest x htl hfitV hx'
    rw [interp_cvalOf hcl] at h
    refine h.trans ?_
    rw [spineV, etaFieldVals]
    by_cases htw' : towerSlotsAll env T caps.etaFields = true
    · have hz : caps.etaFields = 0 := by
        by_contra hne
        exact htw ⟨htw', Nat.pos_of_ne_zero hne⟩
      rw [ite_eq_left htw', hz]
      simp only [etaFabArgsV, projSpines, List.range_zero, List.map_nil]
      rfl
    · rw [ite_eq_right htw']
      simp only [etaFabArgsV, projSpines, spineV, interp_cvalOf hcl]
      rfl

/-- **A strong model satisfies the unit-like law at the level of values.** -/
theorem unitLaw {T : Key md} {cvT : Ix.Kernel.ConstantVal md} {caps : Ix.Kernel.IndCaps md}
    (hT : env.find? T = some (.indInfo cvT caps)) (hunit : caps.unitlike = true)
    (hres : reservedBasisNames.contains T = false) :
    UnitLaw M.model.cval env T cvT caps := by
  intro φ us hus ρ ρ' R ts x y htl hfit hx hy
  have hcl := M.internal.base2.cval_closedL
  obtain ⟨_, -, -, hnf, hlb⟩ := typeReading M hT φ us
  obtain ⟨TVa, hTVa, hTVagr, hlaw⟩ := M.internal.caps_ok.2 T cvT caps hT hunit hres φ us hus
  obtain ⟨rest, hfitV⟩ := teleFit_of_fits_closed hcl hTVa hnf hlb hTVagr hfit
    (fun _ => SetTheory.empty)
  exact hlaw _ ts rest x y htl hfitV (by rw [interp_cvalOf hcl]; exact hx)
    (by rw [interp_cvalOf hcl]; exact hy)

/-- **A strong model satisfies the projection law at the level of values.** -/
theorem projLaw {sn : Key md} {i : Nat} {entry : Ix.Kernel.ProjEntry md}
    (hent : env.findProj? sn i = some entry) : ProjLaw M.model.cval env entry i := by
  intro φ us hus hfire cvC' nP' nF' hctor' ρ ρ' R ys hyl hfit
  have hcl := M.internal.base2.cval_closedL
  obtain ⟨-, -, hi, -, hsortBound, cvC, hctor, hlpsC, hlaws, -⟩ := M.internal.tower_ok φ sn i entry hent
  rw [hctor] at hctor'
  simp only [Option.some.injEq, Ix.Kernel.ConstantInfo.ctorInfo.injEq] at hctor'
  obtain ⟨rfl, -, -⟩ := hctor'
  obtain ⟨-, TCa, hTCa, hB⟩ := hlaws us hus
  obtain ⟨TCa', hTCa', hgrC, hnfC, hlbC⟩ := typeReading M hctor φ us
  obtain rfl : TCa = TCa' := Option.some.inj (hTCa.symm.trans hTCa')
  have hyint : (iotaYs 0 ys.length).map (interp V (iotaVal 0 ys.length ([] : List V) ys)) = ys :=
    iotaYs_interp
  obtain ⟨rest, hfitV⟩ := teleFit_of_fits_closed hcl hTCa hnfC hlbC hgrC hfit
    (iotaVal 0 ys.length ([] : List V) ys)
  -- the constructor's value inhabits its type's reading
  have hmemC := Semantics.Env.find?_mem hctor
  have hname : (Ix.Kernel.ConstantInfo.ctorInfo cvC entry.numParams entry.numFields).name =
      entry.ctor := Semantics.Env.find?_name hctor
  have hread0 : denoteMeta M.internal.base2.acval env
      (Ix.Kernel.Level.substFn φ cvC.levelParams us) 0 cvC.type = some TCa := by
    rw [← denotePInstLevels]
    exact hTCa
  have hmemT := M.internal.mem_type _ hmemC _ TCa hread0 (iotaVal 0 ys.length ([] : List V) ys)
  rw [hname] at hmemT
  have hspine := wellDenotedV_spine hfitV (hgrC _)
    (M.internal.base2.acval entry.ctor (Ix.Kernel.Level.substFn φ cvC.levelParams us))
    (iotaYs 0 ys.length) hyint
    (fun a ha => by
      obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha
      exact wellDenotedV_bvar _ _)
    ⟨M.internal.base2.acval_wellDenoted _ _ _, M.internal.acval_validV _ _ _⟩ hmemT
  rw [hlpsC] at hspine
  have hB' := hB (towerGuardAt_of_fireOk hsortBound hfire) _ (iotaYs 0 ys.length) rest
    (by simp [iotaYs, hyl]) hspine (by rw [hyint]; exact hfitV)
  rw [projAV_interp, interp_mkAppN_spine, hyint, interp_cvalOf hcl,
    interp_getD (by simp [iotaYs, hyl]; omega), hyint] at hB'
  rw [field_eq_projS]
  exact hB'

end Caps

/-! ## The laws -/

/-- **A strong model satisfies the value-level recursor rules** of its environment. -/
theorem recRuleLaws (M : Cached.StrongModel V env) : RecRuleLaws M.model.cval env :=
  fun _ _ _ _ _ hfind _ hrl hfire => recRuleLaw M hfind hrl hfire

/-- **A strong model satisfies the value-level capability laws** of its environment. -/
theorem capabilityLaws (M : Cached.StrongModel V env) : CapabilityLaws M.model.cval env :=
  ⟨fun _ _ _ hT heta hres hslots => etaLaw M hT heta hres hslots,
    fun _ _ _ hT hunit hres => unitLaw M hT hunit hres,
    fun _ _ _ hent => projLaw M hent⟩

end Ix.Cert.StrongValueLaws
