module

public import ConLeche.Model.Inductives.FixChains
import ConLeche.Semantics.Frame
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

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w'

variable {V : Type w'} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The domains' sorts along a Π-inference -/

omit [SetTheory V] in
/-- **The Π-prefix's domains' sorts**: along an opening of an inferred
type, each binder's domain infers a sort at most the whole type's
whenever the whole's is nonzero (`imax` is then `max`). -/
theorem piDoms_of_infer {mode : CheckMode} :
    ∀ (n : Nat) {F d : Nat} {e t : Expr} {v₀ : Level} {fvs : List Expr} {opened : Expr},
      ConLeche.openPisAtFvars n e d = some (fvs, opened) →
      ConLeche.inferTypeCore mode env F d e = .ok t →
      ConLeche.ensureSortCore mode env F d t = .ok v₀ →
      ∀ (k : Nat) (a : Expr), fvs[k]? = some a →
        ∃ (F' : Nat) (t' : Expr) (u : Level),
          ConLeche.inferTypeCore mode env F' (d + k) a.fvarTypeD = .ok t' ∧
          ConLeche.ensureSortCore mode env F' (d + k) t' = .ok u ∧
          ∀ φ, Level.eval φ v₀ ≠ 0 → Level.eval φ u ≤ Level.eval φ v₀
  | 0, F, d, e, t, v₀, fvs, opened, hop, _, _, k, a, hk => by
    simp only [ConLeche.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, -⟩ := hop
    exact nomatch hk
  | n + 1, F, d, e, t, v₀, fvs, opened, hop, h, hens, k, a, hk => by
    match e, hop, h with
    | .forallE dom body mb, hop, h =>
      match F, h with
      | 0, h => rw [ConLeche.inferTypeCore_zero] at h; exact nomatch h
      | F + 1, h =>
        obtain ⟨tty, u, bt, v, hdom, hwh, hbt, hensb, -, rfl⟩ := ConLeche.inferTypeCore_forall_inv h
        have hv₀ : v₀ = .imax u v := ensureSortCore_sort_eq hens
        subst hv₀
        simp only [ConLeche.openPisAtFvars] at hop
        split at hop
        · next fvs' e' hop' =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hop
          obtain ⟨rfl, rfl⟩ := hop
          cases k with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
            subst hk
            refine ⟨F, tty, u, hdom, ?_, fun φ hne => ?_⟩
            · rw [Nat.add_zero, ConLeche.ensureSortCore_eq, hwh]; rfl
            · have hv : Level.eval φ v ≠ 0 := fun h0 => hne ((eval_imax_eq_zero_iff φ u v).mpr h0)
              simp only [Level.eval, if_neg hv]
              exact Nat.le_max_left _ _
          | succ k =>
            simp only [List.getElem?_cons_succ] at hk
            obtain ⟨F', t', u', h1, h2, h3⟩ := piDoms_of_infer n hop' hbt hensb k a hk
            refine ⟨F', t', u', by rw [show d + (k + 1) = d + 1 + k from by omega]; exact h1,
              by rw [show d + (k + 1) = d + 1 + k from by omega]; exact h2, fun φ hne => ?_⟩
            have hv : Level.eval φ v ≠ 0 := fun h0 => hne ((eval_imax_eq_zero_iff φ u v).mpr h0)
            have := h3 φ hv
            simp only [Level.eval, if_neg hv]
            exact Nat.le_trans this (Nat.le_max_right _ _)
        · exact nomatch hop
    | .bvar _, hop, _ | .fvar _ _, hop, _ | .sort _, hop, _
    | .const _ _, hop, _ | .app _ _, hop, _ | .lam _ _ _, hop, _
    | .letE _ _ _, hop, _ | .lit _, hop, _ | .proj _ _ _, hop, _ =>
      simp [ConLeche.openPisAtFvars] at hop

/-! ## The bound, walked along the telescope -/

/-- **The telescope's domains are bounded**, binder by binder: at a
frame satisfying the earlier domains, the next domain's reading is
graded and lies in `univ w` — the sort claim at the context opened by
the earlier binders. -/
theorem teleBound_walk (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env) (ψ : Name → Nat)
    {w : Nat} :
    ∀ (n : Nat) {d : Nat} {e : Expr} {fvs : List Expr} {o : Expr} {Δ : List AnnotTerm}
      {tl : List (Nat × Nat × AnnotTerm)},
      ConLeche.openPisAtFvars n e d = some (fvs, o) → tl.length = n →
      CtxOk mp.base2 ψ d Δ e → Expr.WScoped d e → e.looseBVarsBounded 0 = true →
      Expr.LeavesBounded e →
      (∀ k a, fvs[k]? = some a →
        denoteMeta mp.base2.acval env ψ (d + k) a.fvarTypeD = some (tl.getD k default).2.2) →
      (∀ k a, fvs[k]? = some a → ∃ (F : Nat) (t : Expr) (u : Level),
        ConLeche.inferTypeCore μ env F (d + k) a.fvarTypeD = .ok t ∧
        ConLeche.ensureSortCore μ env F (d + k) t = .ok u ∧ Level.eval ψ u ≤ w) →
      ∀ k, k < n → ∀ ρ : Nat → V, Sat V (((tl.take k).map (·.2.2)).reverse ++ Δ) ρ →
        WellDenotedV V ρ (tl.getD k default).2.2 ∧ interp V ρ (tl.getD k default).2.2 ∈ˢ (univ w : V)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, k, hk, _, _ => absurd hk (Nat.not_lt_zero k)
  | n + 1, d, e, fvs, o, Δ, tl, hop, hlen, hC, hws, hb, hL, hread, hinf, k, hk, ρ, hρ => by
    match e, hop, hws, hb with
    | .forallE ty body mb, hop, hws, hb =>
      simp only [ConLeche.openPisAtFvars] at hop
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
        have hread0 : denoteMeta mp.base2.acval env ψ d ty = some t0.2.2 := by
          have := hread 0 _ rfl
          simpa [Expr.fvarTypeD] using this
        obtain ⟨F, t, u, hi, hens, hle⟩ := hinf 0 _ rfl
        simp only [Nat.add_zero, Expr.fvarTypeD] at hi hens
        have hCty := hC.forallE_ty
        have hrow := (claimsAt_of hμ mp ψ F).sortRow hi hens hws2.1 hbty hLty hCty hread0
        cases k with
        | zero =>
          simp only [List.take_zero, List.map_nil, List.reverse_nil, List.nil_append] at hρ
          exact ⟨(hrow ρ hρ).1, univ_mono hle _ (hrow ρ hρ).2⟩
        | succ k =>
          -- open the binder, walk on
          have hC' : CtxOk mp.base2 ψ (d + 1) (t0.2.2 :: Δ) (body.instantiate1 (.fvar d ty)) :=
            CtxOk.open hC.forallE_body hCty hread0 fun ρ hρ => (hrow ρ hρ).1
          obtain ⟨hws', hb', hL'⟩ := frame_open2 hws2.1 hbty hws2.2 hbb hLty hLbody
          have hread' : ∀ k a, fvs'[k]? = some a →
              denoteMeta mp.base2.acval env ψ (d + 1 + k) a.fvarTypeD = some (tl'.getD k default).2.2 := by
            intro k a hk
            have := hread (k + 1) a (by simpa using hk)
            rwa [show d + (k + 1) = d + 1 + k from by omega] at this
          have hinf' : ∀ k a, fvs'[k]? = some a → ∃ (F : Nat) (t : Expr) (u : Level),
              ConLeche.inferTypeCore μ env F (d + 1 + k) a.fvarTypeD = .ok t ∧
              ConLeche.ensureSortCore μ env F (d + 1 + k) t = .ok u ∧ Level.eval ψ u ≤ w := by
            intro k a hk
            obtain ⟨F, t, u, h1, h2, h3⟩ := hinf (k + 1) a (by simpa using hk)
            rw [show d + (k + 1) = d + 1 + k from by omega] at h1 h2
            exact ⟨F, t, u, h1, h2, h3⟩
          have hρ' : Sat V (((tl'.take k).map (·.2.2)).reverse ++ (t0.2.2 :: Δ)) ρ := by
            simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using hρ
          have := teleBound_walk hμ mp ψ n hop' hlen' hC' hws' hb' hL' hread' hinf' k (by omega) ρ hρ'
          simpa using this
      · exact nomatch hop
    | .bvar _, hop, _, _ | .fvar _ _, hop, _, _ | .sort _, hop, _, _
    | .const _ _, hop, _, _ | .app _ _, hop, _, _ | .lam _ _ _, hop, _, _
    | .letE _ _ _, hop, _, _ | .lit _, hop, _, _ | .proj _ _ _, hop, _, _ =>
      simp [ConLeche.openPisAtFvars] at hop

/-! ## The bound at the constructor data -/

/-- **A reflexive field's telescope domains are bounded at the family's
regime** (task #202 Stage B): at a `Type`-valued block, at a
shadow-fitting field spine and a fitting prefix of the telescope, the
next domain's reading lies in `univ w`.  The install's field-sort
check bounds the field's Π-type's sort by the block's, hence (the
family's sort being nonzero) every domain's. -/
theorem fixTeleBound_of (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {T : Name} {lps : List Name} {nP nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {cvC cvTa cvCa : ConstantVal} {env₀ env₁ : Env}
    {sorts : List Level}
    (hCtor : ConLeche.checkSumCtor (ConLeche.fueledOps μ F) env₁ env T lps nP nIdx resSort
      isProp large cvC nF cvTa = .ok (cvCa, sorts))
    (hProp : isProp = true → (Level.isEquiv resSort .zero == some true) = true)
    {idxArgs : List Expr} {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (Name → Nat) → List AnnotTerm} {srcs : List (Option Nat)} {ks : List RecFieldKind}
    {fvsP xFvs : List Expr} {xrest : Expr} {Eiss : (Name → Nat) → List (List AnnotTerm)}
    {tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (hD : FixCtorDataI mp.base2 env₀ T lps cvCa nP nF nIdx resSort isProp large idxArgs ds Es
      srcs ks fvsP xFvs xrest Eiss tss)
    (ψ : Name → Nat) (hw : resSort.eval ψ ≠ 0) {i : Nat} (hi : i < nF)
    (hk : ks.getD i .ordinary = .reflexive) {ρp : Nat → V}
    (hρp' : Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρp) {as' : List V}
    (hsp' : SpineFit ρp ((shadowFs nP ks nF (((ds ψ).drop nP).map (·.2.2))).take i) as') :
    ∀ k, k < ((tss ψ).getD i []).length → ∀ bs : List V,
      SpineFit (consList as' ρp) ((((tss ψ).getD i []).take k).map (·.2.2)) bs →
      WellDenoted V (consList bs (consList as' ρp)) (((tss ψ).getD i []).getD k default).2.2 ∧
      interp V (consList bs (consList as' ρp)) (((tss ψ).getD i []).getD k default).2.2
        ∈ˢ (univ (resSort.eval ψ) : V) := by
  -- the run's pieces
  obtain ⟨⟨_, hccv⟩, -, fvsP', crest', tfvs, trest, xFvs', idxArgs', hopC, -, -, hopX, -, -, -,
    hsorts⟩ := ConLeche.checkSumCtor_shape hCtor
  obtain ⟨crest, hopP, hopXX⟩ := hD.opens
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hopP.symm.trans hopC))
  obtain ⟨rfl, hxrest⟩ := Prod.mk.inj (Option.some.inj (hopXX.symm.trans hopX))
  obtain ⟨-, hfields⟩ := ConLeche.checkStructFieldSortsI_inv hsorts
  obtain ⟨hcf, -, -, hcb⟩ := ConLeche.direct_sum_ctor_typeWF hCtor
  have hopAll : ConLeche.openPisAtFvars (nP + nF) cvCa.type 0 = some (fvsP ++ xFvs, xrest) :=
    openPisAtFvars_add nP hopP (by rw [Nat.zero_add]; exact hopXX)
  have hO : Opened mp.base2 ψ (nP + nF) cvCa.type (fvsP ++ xFvs) xrest
      (((ds ψ).map (·.2.2)).reverse) (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ)) :=
    opened_of_peel hopAll hcf hcb (hD.read ψ) (hD.len ψ) (hD.okTy ψ)
  have hlenDs := hD.len ψ
  have hlenAll : (fvsP ++ xFvs).length = nP + nF := by
    rw [List.length_append, hD.pLen, hD.xLen]
  -- the shadow gradings
  obtain ⟨hkey, -⟩ := fixShadowGrading hμ mp hCtor hProp hD ψ
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
  have hC : CtxOk mp.base2 ψ (nP + i)
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
  have hle := Level.leq_sound (hleq hnp) ψ
  -- the field's sort is nonzero: the telescope's bits are at the
  -- family's regime, and exact against the innermost body's sort
  have hu : Level.eval ψ u ≠ 0 := by
    obtain ⟨-, -, vb, -, -, hv, hbits⟩ := piBits_of_infer hμ _ hop hinf hens
    intro hu0
    have hvb : Level.eval ψ vb = 0 := (hv ψ).mp hu0
    obtain ⟨afvs', body', hop', hne, -, -, -, -, -, -, -⟩ := hD.opened.reflF i x hx hk
    have hread := hO.doms (nP + i) x hxA
    rw [reverse_getD_field hlenDs hi, drop_map_getD hlenDs hi, hD.reflEntry ψ i hk hi] at hread
    have hst := stripPisAV_mkPisAV ((tss ψ).getD i [])
      (AnnotTerm.mkAppN (mp.base2.acval T ψ)
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
  have hinfD : ∀ k a, afvs[k]? = some a → ∃ (F : Nat) (t : Expr) (u' : Level),
      ConLeche.inferTypeCore μ env F (nP + i + k) a.fvarTypeD = .ok t ∧
      ConLeche.ensureSortCore μ env F (nP + i + k) t = .ok u' ∧ Level.eval ψ u' ≤ resSort.eval ψ := by
    intro k a hka
    obtain ⟨F', t', u', h1, h2, h3⟩ := piDoms_of_infer _ hop hinf hens k a hka
    exact ⟨F', t', u', h1, h2, Nat.le_trans (h3 ψ hu) hle⟩
  -- the walk
  intro k hkT bs hbs
  have hsat : Sat V ((shadowCtx nP ks (nP + nF) (((ds ψ).map (·.2.2)).reverse)).drop
      (nP + nF - (nP + i))) (consList as' ρp) := by
    rw [shadowCtx_drop_fields hlenDs (Nat.le_of_lt hi)]
    exact sat_of_spineFit hρp' hsp'
  have hρ := sat_of_spineFit hsat hbs
  have := teleBound_walk hμ mp ψ (w := resSort.eval ψ) ((tss ψ).getD i []).length hop rfl hC hws hbnd hL
    hdoms hinfD k hkT _ hρ
  exact ⟨this.1.1, this.2⟩

end ConLeche.Model
