module

public import IxC.Kernel.Model.Inductives.FixChains
import IxC.Kernel.Semantics.Frame
public section
/-!
# The reflexive telescopes' bounds (task #202 Stage B)

A reflexive field's type is a Π-tower over its telescope of the family
at the calls' tuples; at a `Type`-valued block (`w ≠ 0`) the family's
slot at such a field is the nested product `piTele w` over the
telescope, which lives in `univ w` only when every telescope domain
does.  The install checks each field's sort against the block's
(`checkStructFieldSortsI`: `imax` of the domains' sorts and the
family's, at most `resSort`); at `w ≠ 0` the `imax` is a `max`, so
every domain's sort is at most `resSort` (`piDoms_of_infer`, the
Π-inference walked along the opening), and the sort claim of the
tuple tier (`sortRow`) reads each domain, at the frame under the
earlier ones, into `univ w` (`teleBound_walk`, the context discipline
opened binder by binder).  `fixTeleBound_of` states this at the
constructor data: at a shadow-fitting field spine and a fitting
telescope prefix, the next domain's reading is bounded at the family's
regime.
-/

namespace Ix.Kernel.Model
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel

open Ix.Kernel.Term Ix.Kernel.Verify SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (Env Expr Key Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w'

variable {V : Type w'} [SetTheory V] {μ : CheckMode} {env : Env md}

/-! ## The domains' sorts along a Π-inference -/

omit [SetTheory V] in
/-- **The Π-prefix's domains' sorts**: along an opening of an inferred
type, each binder's domain infers a sort at most the whole type's
whenever the whole's is nonzero (`imax` is then `max`). -/
theorem piDomsJ {J : Judgements md} (hI : JudgeInv J) :
    ∀ (n : Nat) {d : Nat} {e t : Expr md} {v₀ : Level} {fvs : List (Expr md)} {opened : Expr md},
      Ix.Kernel.openPisAtFvars n e d = some (fvs, opened) →
      J.infer env d e t → J.sort env d t v₀ →
      ∀ (k : Nat) (a : Expr md), fvs[k]? = some a →
        ∃ (t' : Expr md) (u : Level),
          J.infer env (d + k) a.fvarTypeD t' ∧ J.sort env (d + k) t' u ∧
          ∀ φ, Level.eval φ v₀ ≠ 0 → Level.eval φ u ≤ Level.eval φ v₀
  | 0, d, e, t, v₀, fvs, opened, hop, _, _, k, a, hk => by
    simp only [Ix.Kernel.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, -⟩ := hop
    exact nomatch hk
  | n + 1, d, e, t, v₀, fvs, opened, hop, h, hens, k, a, hk => by
    match e, hop, h with
    | .forallE dom body mb, hop, h =>
      obtain ⟨tty, u, bt, v, hdom, hdomS, hbt, hensb, -, rfl⟩ := hI.infer_forallE h
      have hv₀ : v₀ = .imax u v := hI.sort_sort hens
      subst hv₀
      simp only [Ix.Kernel.openPisAtFvars] at hop
      split at hop
      · next fvs' e' hop' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        cases k with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
          subst hk
          refine ⟨tty, u, hdom, hdomS, fun φ hne => ?_⟩
          have hv : Level.eval φ v ≠ 0 := fun h0 => hne ((eval_imax_eq_zero_iff φ u v).mpr h0)
          simp only [Level.eval, if_neg hv]
          exact Nat.le_max_left _ _
        | succ k =>
          simp only [List.getElem?_cons_succ] at hk
          obtain ⟨t', u', h1, h2, h3⟩ := piDomsJ hI n hop' hbt hensb k a hk
          refine ⟨t', u', by rw [show d + (k + 1) = d + 1 + k from by omega]; exact h1,
            by rw [show d + (k + 1) = d + 1 + k from by omega]; exact h2, fun φ hne => ?_⟩
          have hv : Level.eval φ v ≠ 0 := fun h0 => hne ((eval_imax_eq_zero_iff φ u v).mpr h0)
          have := h3 φ hv
          simp only [Level.eval, if_neg hv]
          exact Nat.le_trans this (Nat.le_max_right _ _)
      · exact nomatch hop
    | .bvar _, hop, _ | .fvar _ _, hop, _ | .sort _, hop, _
    | .const _ _, hop, _ | .app _ _, hop, _ | .lam _ _ _, hop, _
    | .letE _ _ _ _, hop, _ | .lit _, hop, _ | .proj _ _ _, hop, _ =>
      simp [Ix.Kernel.openPisAtFvars] at hop

/-! ## The bound, walked along the telescope -/

/-- **The telescope's domains are bounded**, binder by binder: at a
frame satisfying the earlier domains, the next domain's reading is
graded and lies in `univ w` — the sort claim at the context opened by
the earlier binders. -/
theorem teleBound_walkJ {J : Judgements md} {m : EnvModel V env} (ψ : LevelParam → Nat)
    (hS : SortClaimJ J m ψ)
    {w : Nat} :
    ∀ (n : Nat) {d : Nat} {e : Expr md} {fvs : List (Expr md)} {o : Expr md} {Δ : List AnnotTerm}
      {tl : List (Nat × Nat × AnnotTerm)},
      Ix.Kernel.openPisAtFvars n e d = some (fvs, o) → tl.length = n →
      CtxOk m ψ d Δ e → Expr.WScoped d e → e.looseBVarsBounded 0 = true →
      Expr.LeavesBounded e →
      (∀ k a, fvs[k]? = some a →
        denoteMeta m.acval env ψ (d + k) a.fvarTypeD = some (tl.getD k default).2.2) →
      (∀ k a, fvs[k]? = some a → ∃ (t : Expr md) (u : Level),
        J.infer env (d + k) a.fvarTypeD t ∧
        J.sort env (d + k) t u ∧ Level.eval ψ u ≤ w) →
      ∀ k, k < n → ∀ ρ : Nat → V, Sat V (((tl.take k).map (·.2.2)).reverse ++ Δ) ρ →
        WellDenotedV V ρ (tl.getD k default).2.2 ∧ interp V ρ (tl.getD k default).2.2 ∈ˢ (univ w : V)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, k, hk, _, _ => absurd hk (Nat.not_lt_zero k)
  | n + 1, d, e, fvs, o, Δ, tl, hop, hlen, hC, hws, hb, hL, hread, hinf, k, hk, ρ, hρ => by
    match e, hop, hws, hb with
    | .forallE ty body mb, hop, hws, hb =>
      simp only [Ix.Kernel.openPisAtFvars] at hop
      split at hop
      · next fvs' o' hop' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        cases tl with
        | nil => exact absurd hlen (by simp)
        | cons t0 tl' =>
        have hlen' : tl'.length = n := by simpa using hlen
        have hws2 : Expr.WScoped d ty ∧ Expr.WScoped d body := by
          simp only [Expr.WScoped] at hws; exact hws
        -- the first domain's frame conditions
        have hbty : ty.looseBVarsBounded 0 = true := by
          simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb; exact hb.1
        have hbb : body.looseBVarsBounded 1 = true := by
          simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb; exact hb.2
        have hLty : Expr.LeavesBounded ty := fun l hl =>
          hL l (by rw [Expr.fvarLeaves]; exact List.mem_append_left _ hl)
        have hLbody : Expr.LeavesBounded body := fun l hl =>
          hL l (by rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl)
        -- the first domain's row
        have hread0 : denoteMeta m.acval env ψ d ty = some t0.2.2 := by
          have := hread 0 _ rfl
          simpa [Expr.fvarTypeD] using this
        obtain ⟨t, u, hi, hens, hle⟩ := hinf 0 _ rfl
        simp only [Nat.add_zero, Expr.fvarTypeD] at hi hens
        have hCty := hC.forallE_ty
        have hrow := sortRowJ hS hi hens hws2.1 hbty hLty hCty hread0
        cases k with
        | zero =>
          simp only [List.take_zero, List.map_nil, List.reverse_nil, List.nil_append] at hρ
          exact ⟨(hrow ρ hρ).1, univ_mono hle _ (hrow ρ hρ).2⟩
        | succ k =>
          -- open the binder, walk on
          have hC' : CtxOk m ψ (d + 1) (t0.2.2 :: Δ) (body.instantiate1 (.fvar d ty)) :=
            CtxOk.open hC.forallE_body hCty hread0 fun ρ hρ => (hrow ρ hρ).1
          obtain ⟨hws', hb', hL'⟩ := frame_open2 hws2.1 hbty hws2.2 hbb hLty hLbody
          have hread' : ∀ k a, fvs'[k]? = some a →
              denoteMeta m.acval env ψ (d + 1 + k) a.fvarTypeD = some (tl'.getD k default).2.2 := by
            intro k a hk
            have := hread (k + 1) a (by simpa using hk)
            rwa [show d + (k + 1) = d + 1 + k from by omega] at this
          have hinf' : ∀ k a, fvs'[k]? = some a → ∃ (t : Expr md) (u : Level),
              J.infer env (d + 1 + k) a.fvarTypeD t ∧
              J.sort env (d + 1 + k) t u ∧ Level.eval ψ u ≤ w := by
            intro k a hk
            obtain ⟨t, u, h1, h2, h3⟩ := hinf (k + 1) a (by simpa using hk)
            rw [show d + (k + 1) = d + 1 + k from by omega] at h1 h2
            exact ⟨t, u, h1, h2, h3⟩
          have hρ' : Sat V (((tl'.take k).map (·.2.2)).reverse ++ (t0.2.2 :: Δ)) ρ := by
            simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using hρ
          have := teleBound_walkJ ψ hS n hop' hlen' hC' hws' hb' hL' hread' hinf' k (by omega) ρ hρ'
          simpa using this
      · exact nomatch hop
    | .bvar _, hop, _, _ | .fvar _ _, hop, _, _ | .sort _, hop, _, _
    | .const _ _, hop, _, _ | .app _ _, hop, _, _ | .lam _ _ _, hop, _, _
    | .letE _ _ _ _, hop, _, _ | .lit _, hop, _, _ | .proj _ _ _, hop, _, _ =>
      simp [Ix.Kernel.openPisAtFvars] at hop

/-! ## The bound at the constructor data -/

/-- **A reflexive field's telescope domains are bounded at the family's
regime** (task #202 Stage B): at a `Type`-valued block, at a
shadow-fitting field spine and a fitting prefix of the telescope, the
next domain's reading lies in `univ w`.  The install's field-sort
check bounds the field's Π-type's sort by the block's, hence (the
family's sort being nonzero) every domain's. -/
theorem fixTeleBoundJ {J : Judgements md} {m : EnvModel V env} (hJ : JudgeSound J m)
    (hI : JudgeInv J) (hS : ∀ ψ, SortClaimJ J m ψ)
    {T : Key md} {lps : List LevelParam} {nP nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {cvC cvTa cvCa : ConstantVal md} {env₀ env₁ : Env md}
    {sorts : List Level}
    (hCtor : SumCtorRunJ J env₁ env T lps nP nIdx resSort isProp large cvC nF cvTa cvCa sorts)
    (hProp : isProp = true → (Level.isEquiv resSort .zero == some true) = true)
    {idxArgs : List (Expr md)} {ds : (LevelParam → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (LevelParam → Nat) → List AnnotTerm} {srcs : List (Option Nat)} {ks : List RecFieldKind}
    {fvsP xFvs : List (Expr md)} {xrest : Expr md} {Eiss : (LevelParam → Nat) → List (List AnnotTerm)}
    {tss : (LevelParam → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (hD : FixCtorDataI m env₀ T lps cvCa nP nF nIdx resSort isProp large idxArgs ds Es
      srcs ks fvsP xFvs xrest Eiss tss)
    (ψ : LevelParam → Nat) (hw : resSort.eval ψ ≠ 0) {i : Nat} (hi : i < nF)
    (hk : ks.getD i .ordinary = .reflexive) {ρp : Nat → V}
    (hρp' : Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρp) {as' : List V}
    (hsp' : SpineFit ρp ((shadowFs nP ks nF (((ds ψ).drop nP).map (·.2.2))).take i) as') :
    ∀ k, k < ((tss ψ).getD i []).length → ∀ bs : List V,
      SpineFit (consList as' ρp) ((((tss ψ).getD i []).take k).map (·.2.2)) bs →
      WellDenoted V (consList bs (consList as' ρp)) (((tss ψ).getD i []).getD k default).2.2 ∧
      interp V (consList bs (consList as' ρp)) (((tss ψ).getD i []).getD k default).2.2
        ∈ˢ (univ (resSort.eval ψ) : V) := by
  -- the run's pieces
  obtain ⟨_, hccvW⟩ := hCtor.check
  obtain ⟨-, -, fvsP', crest', tfvs, trest, xFvs', idxArgs', hopC, -, -, hopX, -, -, -,
    hsorts⟩ := id hCtor
  obtain ⟨crest, hopP, hopXX⟩ := hD.opens
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hopP.symm.trans hopC))
  obtain ⟨rfl, hxrest⟩ := Prod.mk.inj (Option.some.inj (hopXX.symm.trans hopX))
  obtain ⟨-, hfields⟩ := hsorts
  obtain ⟨hcf, -, -, hcb⟩ := hccvW.typeWF hJ.toJudgeFrames
  have hopAll : Ix.Kernel.openPisAtFvars (nP + nF) cvCa.type 0 = some (fvsP ++ xFvs, xrest) :=
    openPisAtFvars_add nP hopP (by rw [Nat.zero_add]; exact hopXX)
  have hO : Opened m ψ (nP + nF) cvCa.type (fvsP ++ xFvs) xrest
      (((ds ψ).map (·.2.2)).reverse) (ctorBodyAVI m T nP nF ψ (Es ψ)) :=
    opened_of_peel hopAll hcf hcb (hD.read ψ) (hD.len ψ) (hD.okTy ψ)
  have hlenDs := hD.len ψ
  have hlenAll : (fvsP ++ xFvs).length = nP + nF := by
    rw [List.length_append, hD.pLen, hD.xLen]
  -- the shadow gradings
  obtain ⟨hkey, -⟩ := fixShadowGradingJ hJ hI hS hCtor hProp hD ψ
  -- a recursive variable is a leaf of no later domain
  have hrecGet : ∀ i, recAt nP ks (nP + i) → i < nF → ∃ x, xFvs[i]? = some x ∧
      (∀ y ∈ xFvs.drop (i + 1), y.fvarTypeD.mentionsFvar (nP + i) = false) := by
    intro i hr hi
    have hx : xFvs[i]? = some (xFvs[i]'(by rw [hD.xLen]; exact hi)) :=
      List.getElem?_eq_getElem _
    have hk := hr.2
    rw [Nat.add_sub_cancel_left] at hk
    rcases hk with hk | hk
    · obtain ⟨-, -, -, -, hlater, -⟩ := hD.opened.recF i _ hx hk
      exact ⟨_, hx, hlater⟩
    · obtain ⟨-, -, -, -, -, -, -, -, -, hlater, -⟩ := hD.opened.reflF i _ hx hk
      exact ⟨_, hx, hlater⟩
  -- the field: its variable, scoped, leaf-free of the recursive variables
  have hil : i < xFvs.length := by rw [hD.xLen]; exact hi
  obtain ⟨x, hx⟩ : ∃ x, xFvs[i]? = some x := ⟨_, List.getElem?_eq_getElem hil⟩
  have hxA : (fvsP ++ xFvs)[nP + i]? = some x := by
    rw [List.getElem?_append_right (by rw [hD.pLen]; omega), hD.pLen, Nat.add_sub_cancel_left]
    exact hx
  obtain ⟨-, hws, hbnd, hL, hleaf⟩ := hO.var (nP + i) _ hxA
  have hnorec : ∀ l ∈ x.fvarTypeD.fvarLeaves, ¬ recAt nP ks l.1 := by
    intro l hl hr
    have hge := hr.1
    have hlt : l.1 < nP + i := Expr.fvarLeaves_lt_of_wscoped hws l hl
    obtain ⟨x', hx', hlater⟩ := hrecGet (l.1 - nP)
      (by rw [show nP + (l.1 - nP) = l.1 from by omega]; exact hr) (by omega)
    have hmem : x ∈ xFvs.drop (l.1 - nP + 1) := by
      refine List.mem_of_getElem? (i := i - (l.1 - nP + 1)) ?_
      rw [List.getElem?_drop, show l.1 - nP + 1 + (i - (l.1 - nP + 1)) = i from by omega]
      exact hx
    exact mentionsFvar_false (hlater x hmem) l hl (by omega)
  -- the context discipline at the field
  have hC : CtxOk m ψ (nP + i)
      ((shadowCtx nP ks (nP + nF) (((ds ψ).map (·.2.2)).reverse)).drop (nP + nF - (nP + i)))
      x.fvarTypeD :=
    shadowCtxOk hO hlenAll (nP := nP) (ks := ks) (by omega) hws hleaf hnorec
      (fun i' hi' _ ρ' hρ' => (hkey i' (by omega) ρ' hρ').1)
  -- the telescope's opening and readings
  obtain ⟨afvs, body, hop, hlenPi, hdoms, -⟩ := hD.reflOpen ψ i x hx hk
  have hlenT : ((tss ψ).getD i []).length = afvs.length := (openPisAtFvars_length _ hop).symm
  -- the field's sort row
  obtain ⟨fv, ty, u, hfv, -, hinf, hens, hleq, -⟩ := hfields i hi
  obtain rfl := Option.some.inj (hx.symm.trans hfv)
  have hnp : isProp = false := by
    cases hp : isProp
    · rfl
    · exfalso
      have h0 := Level.isEquiv_sound (beq_iff_eq.mp (hProp hp)) ψ
      exact hw (by simpa [Level.eval] using h0)
  have hle := hleq hnp ψ
  -- the field's sort is nonzero: the telescope's bits are at the
  -- family's regime, and exact against the innermost body's sort
  have hu : Level.eval ψ u ≠ 0 := by
    obtain ⟨-, vb, -, -, hv, hbits⟩ := piBitsJ hI _ hop hinf hens
    intro hu0
    have hvb : Level.eval ψ vb = 0 := (hv ψ).mp hu0
    obtain ⟨afvs', body', hop', hne, -, -, -, -, -, -, -⟩ := hD.opened.reflF i x hx hk
    have hread := hO.doms (nP + i) x hxA
    rw [reverse_getD_field hlenDs hi, drop_map_getD hlenDs hi, hD.reflEntry ψ i hk hi] at hread
    have hst := stripPisAV_mkPisAV ((tss ψ).getD i [])
      (AnnotTerm.mkAppN (m.acval T ψ)
        (paramBvarsAt nP (nP + i + ((tss ψ).getD i []).length) ++ (Eiss ψ).getD i []))
    have hb := stripPisAV_bits _ (hbits ψ) hread hst
    have hne' : (tss ψ).getD i [] ≠ [] := by
      intro htl
      have : afvs.length = 0 := by rw [← hlenT, htl]; rfl
      have hm : afvs'.length = afvs.length := by
        rw [openPisAtFvars_length _ hop', openPisAtFvars_length _ hop, hlenPi]
      exact hne (by rw [hm, this])
    obtain ⟨d0, tl', htl⟩ := List.exists_cons_of_ne_nil hne'
    have hmem : d0 ∈ (tss ψ).getD i [] := by rw [htl]; exact List.mem_cons_self
    have h1 := hb d0 hmem
    have h2 := hD.tssBits ψ i d0 hmem
    exact hw (h2.mp (h1.mpr hvb))
  -- the domains' sorts
  have hinfD : ∀ k a, afvs[k]? = some a → ∃ (t : Expr md) (u' : Level),
      J.infer env (nP + i + k) a.fvarTypeD t ∧
      J.sort env (nP + i + k) t u' ∧ Level.eval ψ u' ≤ resSort.eval ψ := by
    intro k a hka
    obtain ⟨t', u', h1, h2, h3⟩ := piDomsJ hI _ hop hinf hens k a hka
    exact ⟨t', u', h1, h2, Nat.le_trans (h3 ψ hu) hle⟩
  -- the walk
  intro k hkT bs hbs
  have hsat : Sat V ((shadowCtx nP ks (nP + nF) (((ds ψ).map (·.2.2)).reverse)).drop
      (nP + nF - (nP + i))) (consList as' ρp) := by
    rw [shadowCtx_drop_fields hlenDs (Nat.le_of_lt hi)]
    exact sat_of_spineFit hρp' hsp'
  have hρ := sat_of_spineFit hsat hbs
  have := teleBound_walkJ ψ (hS ψ) (w := resSort.eval ψ) ((tss ψ).getD i []).length hop rfl hC hws hbnd hL
    hdoms hinfD k hkT _ hρ
  exact ⟨this.1.1, this.2⟩


/-- The reflexive field's telescope bound from the constructor's stage run:
`fixTeleBoundJ` at the kernel's runs. -/
theorem fixTeleBound_of (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {T : Key md} {lps : List LevelParam} {nP nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {cvC cvTa cvCa : ConstantVal md} {env₀ env₁ : Env md}
    {sorts : List Level}
    (hCtor : Ix.Kernel.checkSumCtor (Ix.Kernel.fueledOps μ F) env₁ env T lps nP nIdx resSort
      isProp large cvC nF cvTa = .ok (cvCa, sorts))
    (hProp : isProp = true → (Level.isEquiv resSort .zero == some true) = true)
    {idxArgs : List (Expr md)} {ds : (LevelParam → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (LevelParam → Nat) → List AnnotTerm} {srcs : List (Option Nat)} {ks : List RecFieldKind}
    {fvsP xFvs : List (Expr md)} {xrest : Expr md} {Eiss : (LevelParam → Nat) → List (List AnnotTerm)}
    {tss : (LevelParam → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (hD : FixCtorDataI mp.base2 env₀ T lps cvCa nP nF nIdx resSort isProp large idxArgs ds Es
      srcs ks fvsP xFvs xrest Eiss tss)
    (ψ : LevelParam → Nat) (hw : resSort.eval ψ ≠ 0) {i : Nat} (hi : i < nF)
    (hk : ks.getD i .ordinary = .reflexive) {ρp : Nat → V}
    (hρp' : Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρp) {as' : List V}
    (hsp' : SpineFit ρp ((shadowFs nP ks nF (((ds ψ).drop nP).map (·.2.2))).take i) as') :
    ∀ k, k < ((tss ψ).getD i []).length → ∀ bs : List V,
      SpineFit (consList as' ρp) ((((tss ψ).getD i []).take k).map (·.2.2)) bs →
      WellDenoted V (consList bs (consList as' ρp)) (((tss ψ).getD i []).getD k default).2.2 ∧
      interp V (consList bs (consList as' ρp)) (((tss ψ).getD i []).getD k default).2.2
        ∈ˢ (univ (resSort.eval ψ) : V) :=
  fixTeleBoundJ (judgeSound_runJ hμ mp F) (judgeInv_runJ hμ F) (sortClaim_runJ hμ mp F)
    (Ix.Kernel.Semantics.sumCtorRunJ_of_run hCtor) hProp hD ψ hw hi hk hρp' hsp'

end Ix.Kernel.Model
