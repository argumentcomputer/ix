import Ix.Tc.Verify.Whnf.Beta.ArgumentAlignment

/-!
# One-pass translation of simultaneous beta substitution

This is the concrete half of `BetaPrefixMeaning`.  It follows
`simulSubstSpec` structurally once, using the dependent `KInsts` lookup
theorems for variables.  No sequential concrete intermediate is constructed,
so the proof consumes exactly production's original `WalkerRequest.Bounds`.
-/

namespace Ix.Tc

open Lean4Lean

private theorem toNat_toUInt64_cc (value : Nat) :
    value.toUInt64.toNat = value % UInt64.size := by
  unfold Nat.toUInt64
  rfl

private theorem instBetaArgs_natLit_cc (value : Nat)
    (arguments : List VExpr) (depth : Nat) :
    VExpr.instBetaArgs (VExpr.natLit value) arguments depth =
      VExpr.natLit value := by
  induction value with
  | zero => exact VExpr.instBetaArgs_const _ _ _ _
  | succ value ih =>
      rw [VExpr.natLit, VExpr.instBetaArgs_app, ih]
      exact congrArg (fun fn => VExpr.app fn (VExpr.natLit value))
        (VExpr.instBetaArgs_const _ _ _ _)

private theorem instBetaArgs_listCharLit_cc (value : List Char)
    (arguments : List VExpr) (depth : Nat) :
    VExpr.instBetaArgs (VExpr.listCharLit value) arguments depth =
      VExpr.listCharLit value := by
  induction value with
  | nil =>
      simp [VExpr.listCharLit, VExpr.listCharNil, VExpr.char,
        VExpr.instBetaArgs_app]
  | cons char value ih =>
      simp [VExpr.listCharLit, VExpr.listCharCons, VExpr.charOfNat,
        VExpr.char, VExpr.instBetaArgs_app, ih,
        instBetaArgs_natLit_cc]

private theorem instBetaArgs_trLiteral_cc (literal : Lean.Literal)
    (arguments : List VExpr) (depth : Nat) :
    VExpr.instBetaArgs (VExpr.trLiteral literal) arguments depth =
      VExpr.trLiteral literal := by
  cases literal with
  | natVal value => exact instBetaArgs_natLit_cc value arguments depth
  | strVal value =>
      rw [VExpr.trLiteral, VExpr.instBetaArgs_app,
        instBetaArgs_listCharLit_cc]
      exact congrArg (fun fn => VExpr.app fn (VExpr.listCharLit value.toList))
        (VExpr.instBetaArgs_const _ _ _ _)

/-- Structural translation commutes with one production simultaneous-
substitution pass under its exact request bound. -/
theorem TrKExprS.simulSubstBeta
    {env : VEnv} {uvars : Nat} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel}
    (henv : env.Ordered)
    (htp : ∀ {Γ Γ' : List VExpr} {n k : Nat} {s : Lean.Name} {i : Nat}
      {e e' : VExpr}, Lean4Lean.Ctx.LiftN n k Γ Γ' →
      trProj uvars Γ s i e e' →
      trProj uvars Γ' s i (e.liftN n k) (e'.liftN n k))
    (htpI : ∀ {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {position : Nat}
      {Γ₁ Γ : List VExpr} {s : Lean.Name} {i : Nat} {e e' : VExpr},
      env.HasType uvars Γ₀ e₀ A₀ →
      Lean4Lean.Ctx.InstN Γ₀ e₀ A₀ position Γ₁ Γ →
      trProj uvars Γ₁ s i e e' →
      trProj uvars Γ s i (e.inst e₀ position) (e'.inst e₀ position))
    {base : KVLCtx} {substs : Array (KExpr .anon)}
    {arguments : List VExpr}
    (harguments : RecM.SimulArgs env uvars nameOf trProj base substs arguments)
    {source : KVLCtx} {body : KExpr .anon} {bodyV : VExpr}
    (H : TrKExprS env uvars nameOf trProj source body bodyV) :
    ∀ {target : KVLCtx} {dk k : Nat} {depth : UInt64},
      KVLCtx.KInsts env uvars base arguments dk k source target →
      KVLCtx.KBVLift base target dk 0 k 0 →
      WalkerRequest.Bounds (.simulSubst body substs depth) →
      depth.toNat = dk →
      TrKExprS env uvars nameOf trProj target
        (KExpr.simulSubstSpec body substs depth)
        (VExpr.instBetaArgs bodyV arguments k) := by
  induction H with
  | @var source index name info value type hfind =>
      intro target dk k depth hinsts hlift hbounds hdepth
      obtain ⟨hbody, hsubsts, hsizes, hwalk, helem⟩ := hbounds
      cases hbody with
      | @var _ _ _ hindex =>
        rw [KExpr.size] at hwalk
        have hsizeNat : substs.size.toUInt64.toNat = substs.size := by
          rw [toNat_toUInt64_cc]
          exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hwalk)
        have hboundary : (depth + substs.size.toUInt64).toNat =
            depth.toNat + substs.size := by
          rw [UInt64.toNat_add, hsizeNat]
          exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hwalk)
        rw [KExpr.simulSubstSpec]
        split
        · next hwindow =>
          obtain ⟨hgeB, hltB⟩ := Bool.and_eq_true_iff.mp hwindow
          have hge : depth.toNat ≤ index.toNat :=
            UInt64.le_iff_toNat_le.mp (of_decide_eq_true hgeB)
          have hlt : index.toNat < depth.toNat + substs.size := by
            have hlt' := UInt64.lt_iff_toNat_lt.mp
              (of_decide_eq_true hltB)
            rwa [hboundary] at hlt'
          have hoffsetNat : (index - depth).toNat =
              index.toNat - depth.toNat :=
            UInt64.toNat_sub_of_le index depth
              (UInt64.le_iff_toNat_le.mpr hge)
          have hoffset : (index - depth).toNat < substs.size := by omega
          have hvalueBound : (index - depth).toNat < arguments.length := by
            rw [← harguments.size_eq]
            exact hoffset
          have hlookupIndex : index.toNat =
              dk + (index - depth).toNat := by
            rw [← hdepth, hoffsetNat]
            omega
          obtain ⟨argumentV, hget, hmeaning⟩ :=
            hinsts.find?_window hvalueBound (hlookupIndex ▸ hfind)
          have hvalueEq :
              arguments.reverse[(index - depth).toNat]! = argumentV := by
            have hreverseBound :
                (index - depth).toNat < arguments.reverse.length := by
              simpa using hvalueBound
            rw [getElem!_pos arguments.reverse (index - depth).toNat
              hreverseBound]
            rw [getElem?_pos arguments.reverse (index - depth).toNat
              hreverseBound] at hget
            exact Option.some.inj hget
          have hargumentTr := harguments.translate _ hoffset
          rw [hvalueEq] at hargumentTr
          have hliftTr := TrKExprS.weakBV_lbr henv htp
            (hsubsts _ hoffset) hargumentTr hlift hdepth rfl
            (by rw [show (0 : UInt64).toNat = 0 from rfl];
                simpa using hsizes _ hoffset)
            (by have := helem _ hoffset; omega)
          rw [hmeaning]
          exact hliftTr
        · next hnotWindow =>
          split
          · next haboveU =>
            have habove : dk + arguments.length ≤ index.toNat := by
              have h := UInt64.le_iff_toNat_le.mp haboveU
              rw [hboundary, hdepth, harguments.size_eq] at h
              exact h
            have htargetFind := hinsts.find?_above habove hfind
            have hsubNat : (index - substs.size.toUInt64).toNat =
                index.toNat - arguments.length := by
              rw [UInt64.toNat_sub_of_le index substs.size.toUInt64
                (UInt64.le_iff_toNat_le.mpr (by
                  rw [hsizeNat, harguments.size_eq]
                  omega)), hsizeNat, harguments.size_eq]
            rw [KExpr.mkVar_shape]
            exact .var (hsubNat ▸ htargetFind)
          · next hnotAbove =>
            have hbelow : index.toNat < dk := by
              by_contra hnotBelow
              have hge : depth ≤ index :=
                UInt64.le_iff_toNat_le.mpr (by
                  rw [hdepth]
                  omega)
              have hlt : index < depth + substs.size.toUInt64 := by
                exact UInt64.lt_iff_toNat_lt.mpr (by
                  rw [hboundary, hdepth]
                  have hnle : ¬depth.toNat + substs.size ≤ index.toNat :=
                    fun hle => hnotAbove
                      (UInt64.le_iff_toNat_le.mpr (by
                        rw [hboundary]
                        exact hle))
                  omega)
              exact hnotWindow (Bool.and_eq_true_iff.mpr
                ⟨decide_eq_true hge, decide_eq_true hlt⟩)
            exact .var (hinsts.find?_below hbelow hfind)
  | @fvar source fv name info value type hfind =>
      intro target dk k depth hinsts hlift hbounds hdepth
      exact .fvar (hinsts.find?_fvar hfind)
  | @sort source level info hlevel =>
      intro target dk k depth hinsts hlift hbounds hdepth
      simpa only [KExpr.simulSubstSpec, VExpr.instBetaArgs_sort] using
        (TrKExprS.sort (env := env) (nameOf := nameOf) (trProj := trProj)
          (Δ := target) (md := info) hlevel)
  | @const source id levels info constName ci hname hconst hlevels hlength =>
      intro target dk k depth hinsts hlift hbounds hdepth
      simpa only [KExpr.simulSubstSpec, VExpr.instBetaArgs_const] using
        (TrKExprS.const (env := env) (nameOf := nameOf) (trProj := trProj)
          (Δ := target) (md := info) hname hconst hlevels hlength)
  | @app source fn arg info fnV argV A B hfun harg hfnTr hargTr ihfn iharg =>
      intro target dk k depth hinsts hlift hbounds hdepth
      obtain ⟨hbody, hsubsts, hsizes, hwalk, helem⟩ := hbounds
      cases hbody with
      | app hfn hargCon =>
        rw [KExpr.size] at hwalk
        have hfnBounds : WalkerRequest.Bounds (.simulSubst fn substs depth) :=
          ⟨hfn, hsubsts, hsizes, by omega, fun index hindex => by
            have h := helem index hindex
            rw [KExpr.size] at h
            omega⟩
        have hargBounds : WalkerRequest.Bounds (.simulSubst arg substs depth) :=
          ⟨hargCon, hsubsts, hsizes, by omega, fun index hindex => by
            have h := helem index hindex
            rw [KExpr.size] at h
            omega⟩
        rw [KExpr.simulSubstSpec, KExpr.mkApp_shape,
          VExpr.instBetaArgs_app]
        have hfun' := hinsts.hasType henv hfun
        rw [VExpr.instBetaArgs_forallE] at hfun'
        exact .app hfun' (hinsts.hasType henv harg)
          (ihfn hinsts hlift hfnBounds hdepth)
          (iharg hinsts hlift hargBounds hdepth)
  | @lam source name bi ty body info tyV bodyV hty htyTr hbodyTr
      ihty ihbody =>
      intro target dk k depth hinsts hlift hbounds hdepth
      obtain ⟨hcon, hsubsts, hsizes, hwalk, helem⟩ := hbounds
      cases hcon with
      | lam htyCon hbodyCon =>
        rw [KExpr.size] at hwalk
        have htyBounds : WalkerRequest.Bounds (.simulSubst ty substs depth) :=
          ⟨htyCon, hsubsts, hsizes, by omega, fun index hindex => by
            have h := helem index hindex
            rw [KExpr.size] at h
            omega⟩
        have hdepth1 : (depth + 1).toNat = dk + 1 := by
          rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl,
            hdepth]
          exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hwalk)
        have hbodyBounds :
            WalkerRequest.Bounds (.simulSubst body substs (depth + 1)) :=
          ⟨hbodyCon, hsubsts, hsizes, by rw [hdepth1]; omega,
            fun index hindex => by
              have h := helem index hindex
              rw [KExpr.size] at h
              rw [hdepth1]
              omega⟩
        let tyV' := VExpr.instBetaArgs tyV arguments k
        have hinstsBody := hinsts.succ (.vlam tyV)
        have hliftBody := KVLCtx.KBVLift.skip
          ((VLocalDecl.vlam tyV).instBetaArgs arguments k) hlift
        rw [VLocalDecl.instBetaArgs_depth] at hliftBody
        rw [KExpr.simulSubstSpec, KExpr.mkLam_shape,
          VExpr.instBetaArgs_lam]
        exact .lam (hinsts.isType henv hty)
          (ihty hinsts hlift htyBounds hdepth)
          (by
            simpa [tyV', VLocalDecl.instBetaArgs, VLocalDecl.depth] using
              ihbody hinstsBody hliftBody hbodyBounds hdepth1)
  | @all source name bi ty body info tyV bodyV hty hbodyTy htyTr hbodyTr
      ihty ihbody =>
      intro target dk k depth hinsts hlift hbounds hdepth
      obtain ⟨hcon, hsubsts, hsizes, hwalk, helem⟩ := hbounds
      cases hcon with
      | all htyCon hbodyCon =>
        rw [KExpr.size] at hwalk
        have htyBounds : WalkerRequest.Bounds (.simulSubst ty substs depth) :=
          ⟨htyCon, hsubsts, hsizes, by omega, fun index hindex => by
            have h := helem index hindex
            rw [KExpr.size] at h
            omega⟩
        have hdepth1 : (depth + 1).toNat = dk + 1 := by
          rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl,
            hdepth]
          exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hwalk)
        have hbodyBounds :
            WalkerRequest.Bounds (.simulSubst body substs (depth + 1)) :=
          ⟨hbodyCon, hsubsts, hsizes, by rw [hdepth1]; omega,
            fun index hindex => by
              have h := helem index hindex
              rw [KExpr.size] at h
              rw [hdepth1]
              omega⟩
        let tyV' := VExpr.instBetaArgs tyV arguments k
        have hinstsBody := hinsts.succ (.vlam tyV)
        have hliftBody := KVLCtx.KBVLift.skip
          ((VLocalDecl.vlam tyV).instBetaArgs arguments k) hlift
        rw [VLocalDecl.instBetaArgs_depth] at hliftBody
        rw [KExpr.simulSubstSpec, KExpr.mkAll_shape,
          VExpr.instBetaArgs_forallE]
        exact .all (hinsts.isType henv hty)
          (by
            simpa [tyV', VLocalDecl.instBetaArgs, VLocalDecl.depth,
              KVLCtx.toCtx] using
              hinstsBody.isType henv hbodyTy)
          (ihty hinsts hlift htyBounds hdepth)
          (by
            simpa [tyV', VLocalDecl.instBetaArgs, VLocalDecl.depth] using
              ihbody hinstsBody hliftBody hbodyBounds hdepth1)
  | @letE source name ty val body nondep info tyV valV bodyV hvalTy htyTr
      hvalTr hbodyTr ihty ihval ihbody =>
      intro target dk k depth hinsts hlift hbounds hdepth
      obtain ⟨hcon, hsubsts, hsizes, hwalk, helem⟩ := hbounds
      cases hcon with
      | letE htyCon hvalCon hbodyCon =>
        rw [KExpr.size] at hwalk
        have htyBounds : WalkerRequest.Bounds (.simulSubst ty substs depth) :=
          ⟨htyCon, hsubsts, hsizes, by omega, fun index hindex => by
            have h := helem index hindex
            rw [KExpr.size] at h
            omega⟩
        have hvalBounds : WalkerRequest.Bounds (.simulSubst val substs depth) :=
          ⟨hvalCon, hsubsts, hsizes, by omega, fun index hindex => by
            have h := helem index hindex
            rw [KExpr.size] at h
            omega⟩
        have hdepth1 : (depth + 1).toNat = dk + 1 := by
          rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl,
            hdepth]
          exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hwalk)
        have hbodyBounds :
            WalkerRequest.Bounds (.simulSubst body substs (depth + 1)) :=
          ⟨hbodyCon, hsubsts, hsizes, by rw [hdepth1]; omega,
            fun index hindex => by
              have h := helem index hindex
              rw [KExpr.size] at h
              rw [hdepth1]
              omega⟩
        let tyV' := VExpr.instBetaArgs tyV arguments k
        let valV' := VExpr.instBetaArgs valV arguments k
        have hinstsBody := hinsts.succ (.vlet tyV valV)
        have hliftBody := KVLCtx.KBVLift.skip
          ((VLocalDecl.vlet tyV valV).instBetaArgs arguments k) hlift
        rw [VLocalDecl.instBetaArgs_depth] at hliftBody
        rw [KExpr.simulSubstSpec, KExpr.mkLet_shape]
        exact .letE (hinsts.hasType henv hvalTy)
          (ihty hinsts hlift htyBounds hdepth)
          (ihval hinsts hlift hvalBounds hdepth)
          (by
            simpa [tyV', valV', VLocalDecl.instBetaArgs,
              VLocalDecl.depth] using
              ihbody hinstsBody hliftBody hbodyBounds hdepth1)
  | @prj source id field val info structName valueV resultV hname hvalTr
      hproj ihval =>
      intro target dk k depth hinsts hlift hbounds hdepth
      obtain ⟨hcon, hsubsts, hsizes, hwalk, helem⟩ := hbounds
      cases hcon with
      | prj hvalCon =>
        rw [KExpr.size] at hwalk
        have hvalBounds : WalkerRequest.Bounds (.simulSubst val substs depth) :=
          ⟨hvalCon, hsubsts, hsizes, by omega, fun index hindex => by
            have h := helem index hindex
            rw [KExpr.size] at h
            omega⟩
        rw [KExpr.simulSubstSpec, KExpr.mkPrj_shape]
        exact .prj hname (ihval hinsts hlift hvalBounds hdepth)
          (hinsts.projection htpI hproj)
  | @nat source value blob info hlit =>
      intro target dk k depth hinsts hlift hbounds hdepth
      rw [instBetaArgs_natLit_cc]
      exact .nat hlit
  | @str source value blob info hlit =>
      intro target dk k depth hinsts hlift hbounds hdepth
      rw [instBetaArgs_trLiteral_cc]
      exact .str hlit

end Ix.Tc
