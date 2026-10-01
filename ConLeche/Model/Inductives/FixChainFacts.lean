module

import ConLeche.Model.Inductives.FixChains
public import ConLeche.Model.Inductives.FixTeleBound
public section

/-!
# The chain facts of a recursive constructor, and the index telescope
(task #188)

The walk's inputs (`ChainFacts`) from a recursive constructor's data
at a carrier storing the former as a λ-tower over the parameters
(`fixChainFacts_of`): the no-mention facts from the opened-form guard
through `noBVar_of_leaf_free`, the shadow gradings from
`fixShadowGrading`, the recursive slots' index fit from the family's
λ-tower shape (as the sum route's `ctorFramesGen`).  And the former's
index telescope graded and bounded at the parameter frame
(`idxOk_of`): the index binders' sorts the install read
(`checkStructFieldSortsI` at the former's opened telescope), joined
into the tuple universe `idxUniv`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w'

variable {V : Type w'} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## Kit -/

/-- The tuple universe: the join of the index binders' sorts. -/
def idxUniv (ψ : Name → Nat) (isorts : List Level) : Nat :=
  (isorts.map (Level.eval ψ)).foldl max 0

omit [SetTheory V] in
theorem le_foldl_max : ∀ (l : List Nat) (a x : Nat), x ∈ l → x ≤ l.foldl max a
  | [], _, _, h => nomatch h
  | y :: l, a, x, h => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right a x) (foldl_max_ge l _)
    · exact le_foldl_max l (max a y) x h
where
  foldl_max_ge : ∀ (l : List Nat) (a : Nat), a ≤ l.foldl max a
    | [], _ => Nat.le_refl _
    | y :: l, a => by
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left a y) (foldl_max_ge l _)

omit [SetTheory V] in
theorem eval_le_idxUniv {ψ : Name → Nat} {isorts : List Level} {j : Nat} {s : Level}
    (h : isorts[j]? = some s) : s.eval ψ ≤ idxUniv ψ isorts :=
  le_foldl_max _ 0 _ (List.mem_map.mpr ⟨s, List.mem_of_getElem? h, rfl⟩)

/-! ## The index telescope -/

/-- **The former's index telescope**, graded and bounded by the tuple
universe at every parameter frame. -/
theorem idxOk_of (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {nP nIdx : Nat} {resSort : Level} {cvTa : ConstantVal} {T : Name}
    {caps : IndCaps} (hfT : env.find? T = some (.indInfo cvTa caps))
    {tfvs : List Expr} {trest : Expr}
    (hopT : openPisAtFvars (nP + nIdx) cvTa.type 0 = some (tfvs, trest))
    {isorts : List Level}
    (hsorts : ConLeche.checkStructFieldSortsI (ConLeche.fueledOps μ F) env true false resSort nP
      (tfvs.drop nP) [] nIdx = .ok isorts)
    {ppsAll : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData mp.base2 cvTa (nP + nIdx) resSort ppsAll)
    (ψ : Name → Nat) (ρp : Nat → V)
    (hρp : Sat V (((ppsAll ψ).take nP).map (·.2.2)).reverse ρp) :
    IdxOk (idxUniv ψ isorts) ρp (((ppsAll ψ).drop nP).map (·.2.2)) := by
  obtain ⟨hTf, -, -, hTb, -⟩ := mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfT)
  simp only [ConstantInfo.toConstantVal] at hTf hTb
  have hT : Opened mp.base2 ψ (nP + nIdx) cvTa.type tfvs trest
      (((ppsAll ψ).map (·.2.2)).reverse) (.sort (resSort.eval ψ)) :=
    opened_of_peel hopT hTf hTb (hFD.read ψ) (hFD.len ψ) (hFD.okTy ψ)
  have hc := claimsAt_of hμ mp ψ F
  obtain ⟨-, hrows⟩ := ConLeche.checkStructFieldSortsI_inv hsorts
  have hlenT : tfvs.length = nP + nIdx := openPisAtFvars_length _ hopT
  have hΓ : (((ppsAll ψ).map (·.2.2)).reverse).length = nP + nIdx := by simp [hFD.len ψ]
  -- the index binders' universes at their frames
  have hbnd : ∀ j, j < nIdx → ∀ ρ : Nat → V,
      Sat V ((((ppsAll ψ).map (·.2.2)).reverse).drop (nP + nIdx - (nP + j))) ρ →
      interp V ρ ((((ppsAll ψ).map (·.2.2)).reverse).getD (nP + nIdx - 1 - (nP + j)) default)
        ∈ˢ (univ (idxUniv ψ isorts) : V) := by
    intro j hj ρ hρ
    obtain ⟨fv, ty, u, hfv, hu, hi, hens, -, -⟩ := hrows j hj
    have hfvT : tfvs[nP + j]? = some fv := by
      rw [List.getElem?_drop] at hfv; exact hfv
    obtain ⟨-, hws, hb, hL, hleaf⟩ := hT.var (nP + j) fv hfvT
    have hCtx := hT.ctx (i := nP + j) (by omega) hws hleaf
    have hread := hT.doms (nP + j) fv hfvT
    have hrow := hc.sortRow hi hens hws hb hL hCtx hread ρ hρ
    exact univ_mono (eval_le_idxUniv (ψ := ψ) hu) _ hrow.2
  have hρp' : Sat V ((((ppsAll ψ).map (·.2.2)).reverse).drop (nP + nIdx - (nP + 0))) ρp := by
    rw [Nat.add_zero, drop_fields_eq (hFD.len ψ) nP (Nat.le_refl _), Nat.sub_self, List.drop_zero]
    exact hρp
  have hok := fieldsOkB_of_frame rfl hΓ hT.okΓ (fun j hj ρ hρ _ => hbnd j hj ρ hρ) 0 (Nat.zero_le _)
    ρp hρp'
  have hbd := fieldsBound_of_frame rfl hΓ hbnd 0 (Nat.zero_le _) ρp hρp'
  rw [fieldsFrom_eq_drop (hFD.len ψ)] at hok hbd
  exact ⟨hok, hbd⟩

/-! ## Kit for the chain facts -/

omit [SetTheory V] in
theorem WScoped_of_mem_getAppArgs : ∀ (e a : Expr) {d : Nat}, Expr.WScoped d e →
    a ∈ e.getAppArgs → Expr.WScoped d a
  | .app f a', a, d, hw, ha => by
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at ha
    simp only [Expr.WScoped] at hw
    rcases ha with ha | rfl
    · exact WScoped_of_mem_getAppArgs f a hw.1 ha
    · exact hw.2
  | .bvar _, _, _, _, ha => absurd ha (by simp [Expr.getAppArgs])
  | .fvar _ _, _, _, _, ha => absurd ha (by simp [Expr.getAppArgs])
  | .sort _, _, _, _, ha => absurd ha (by simp [Expr.getAppArgs])
  | .const _ _, _, _, _, ha => absurd ha (by simp [Expr.getAppArgs])
  | .lam _ _ _, _, _, _, ha => absurd ha (by simp [Expr.getAppArgs])
  | .forallE _ _ _, _, _, _, ha => absurd ha (by simp [Expr.getAppArgs])
  | .letE _ _ _, _, _, _, ha => absurd ha (by simp [Expr.getAppArgs])
  | .proj _ _ _, _, _, _, ha => absurd ha (by simp [Expr.getAppArgs])
  | .lit _, _, _, _, ha => absurd ha (by simp [Expr.getAppArgs])

/-- Every reading of a read spine is the reading of one of its terms. -/
theorem DenoteMetaSpine.mem_inv {acval : Name → (Name → Nat) → AnnotTerm} {φ : Name → Nat} {d : Nat} :
    ∀ {as : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine acval env φ d as vs →
      ∀ v ∈ vs, ∃ a ∈ as, denoteMeta acval env φ d a = some v
  | _, _, .nil, _, hv => nomatch hv
  | a :: as, v' :: vs, .cons ha h, v, hv => by
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨a, List.mem_cons_self, ha⟩
    · obtain ⟨a', ha', hr⟩ := DenoteMetaSpine.mem_inv h v hv
      exact ⟨a', List.mem_cons_of_mem _ ha', hr⟩

/-- **The opened pieces' leaves** are the term's or at the opening
depth and above. -/
theorem openPisAtFvars_leaf_bound {n : Nat} {e : Expr} {d : Nat} {fvs : List Expr} {o : Expr}
    (h : openPisAtFvars n e d = some (fvs, o)) :
    (∀ x ∈ fvs, ∀ l ∈ x.fvarTypeD.fvarLeaves, l ∈ e.fvarLeaves ∨ d ≤ l.1) ∧
    (∀ l ∈ o.fvarLeaves, l ∈ e.fvarLeaves ∨ d ≤ l.1) := by
  have key : ∀ l : Nat × Expr, Expr.fvar l.1 l.2 ∈ fvs → d ≤ l.1 := by
    intro l hl
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hl
    obtain ⟨ty, heq⟩ := openPisAtFvars_index n e d h j _ hj
    have : l.1 = d + j := by
      have := congrArg (fun e => match e with | .fvar i _ => i | _ => 0) heq
      simpa using this
    omega
  refine ⟨fun x hx l hl => ?_, fun l hl => ?_⟩
  · obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
    obtain ⟨ty, rfl⟩ := openPisAtFvars_index n e d h j _ hj
    have hl' : l ∈ (Expr.fvar (d + j) ty).fvarLeaves := by
      simp only [Expr.fvarLeaves]
      exact List.mem_cons_of_mem _ hl
    rcases openPisAtFvars_leaves n h l (Or.inr ⟨_, hx, hl'⟩) with h' | h'
    · exact Or.inl h'
    · exact Or.inr (key l h')
  · rcases openPisAtFvars_leaves n h l (Or.inl hl) with h' | h'
    · exact Or.inl h'
    · exact Or.inr (key l h')

/-! ## The chain facts -/

set_option maxHeartbeats 1600000 in
/-- **The walk's inputs**, from a recursive constructor's data at a
carrier storing the former as a λ-tower over the parameters. -/
theorem fixChainFacts_of (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {T : Name} {lps : List Name} {nP nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {cvC cvTa cvCa : ConstantVal} {env₀ env₁ : Env} {caps : IndCaps}
    {sorts : List Level}
    (hCtor : ConLeche.checkSumCtor (ConLeche.fueledOps μ F) env₁ env T lps nP nIdx resSort
      isProp large cvC nF cvTa = .ok (cvCa, sorts))
    (hfT : env.find? T = some (.indInfo cvTa caps))
    (hProp : isProp = true → (Level.isEquiv resSort .zero == some true) = true)
    {ppsAll : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData mp.base2 cvTa (nP + nIdx) resSort ppsAll)
    (hleafT : ∀ ψ, ∃ B, mp.base2.acval T ψ = mkLamsC (resSort.eval ψ + 1) (ppsAll ψ) B)
    {idxArgs : List Expr} {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (Name → Nat) → List AnnotTerm} {srcs : List (Option Nat)} {ks : List RecFieldKind}
    {fvsP xFvs : List Expr} {xrest : Expr} {Eiss : (Name → Nat) → List (List AnnotTerm)}
    {tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (hD : FixCtorDataI mp.base2 env₀ T lps cvCa nP nF nIdx resSort isProp large idxArgs ds Es
      srcs ks fvsP xFvs xrest Eiss tss)
    (u : Nat) (ψ : Name → Nat) (ρp : Nat → V)
    (hρp : Sat V (((ppsAll ψ).take nP).map (·.2.2)).reverse ρp) :
    ChainFacts u (resSort.eval ψ) nP nF ρp (((ppsAll ψ).drop nP).map (·.2.2)) ks (tss ψ)
      (((ds ψ).drop nP).map (·.2.2)) (Eiss ψ) (Es ψ) := by
  -- the openings, the opened record
  obtain ⟨crest, hopP, hopX⟩ := hD.opens
  obtain ⟨hcf, -, -, hcb⟩ := ConLeche.direct_sum_ctor_typeWF hCtor
  have hopAll : openPisAtFvars (nP + nF) cvCa.type 0 = some (fvsP ++ xFvs, xrest) :=
    openPisAtFvars_add nP hopP (by rw [Nat.zero_add]; exact hopX)
  have hO : Opened mp.base2 ψ (nP + nF) cvCa.type (fvsP ++ xFvs) xrest
      (((ds ψ).map (·.2.2)).reverse) (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ)) :=
    opened_of_peel hopAll hcf hcb (hD.read ψ) (hD.len ψ) (hD.okTy ψ)
  have hlenDs := hD.len ψ
  have hlenFs : ((((ds ψ).drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
  have hlenIds : ((((ppsAll ψ).drop nP).map (·.2.2))).length = nIdx := by
    simp [hFD.len ψ]
  -- the parameter frames identified
  have hiff := (ctorFramesGen hμ mp hCtor hfT hProp hFD hD.toCtorDataI hleafT).1 ψ ρp
  have hρp' : Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρp := hiff.mp hρp
  -- the shadow gradings
  obtain ⟨hkey, hkeyR⟩ := fixShadowGrading hμ mp hCtor hProp hD ψ
  -- a recursive variable is a leaf of no later domain nor of the residual
  have hrecGet : ∀ i, recAt nP ks (nP + i) → i < nF → ∃ x, xFvs[i]? = some x ∧
      (∀ y ∈ xFvs.drop (i + 1), y.fvarTypeD.mentionsFvar (nP + i) = false) ∧
      xrest.mentionsFvar (nP + i) = false := by
    intro i hr hi
    have hx : xFvs[i]? = some (xFvs[i]'(by rw [hD.xLen]; exact hi)) :=
      List.getElem?_eq_getElem _
    have hk := hr.2
    rw [Nat.add_sub_cancel_left] at hk
    rcases hk with hk | hk
    · obtain ⟨-, -, -, -, hlater, hres⟩ := hD.opened.recF i _ hx hk
      exact ⟨_, hx, hlater, hres⟩
    · obtain ⟨-, -, -, -, -, -, -, -, -, hlater, hres⟩ := hD.opened.reflF i _ hx hk
      exact ⟨_, hx, hlater, hres⟩
  -- field `i`'s opened domain: scoped, leaf-free of the recursive
  -- variables below it
  have hdom : ∀ i, i < nF → ∃ x, xFvs[i]? = some x ∧ Expr.WScoped (nP + i) x.fvarTypeD ∧
      (∀ l ∈ x.fvarTypeD.fvarLeaves, ¬ (recAt nP ks l.1 ∧ l.1 < nP + i)) := by
    intro i hi
    have hx : xFvs[i]? = some (xFvs[i]'(by rw [hD.xLen]; exact hi)) :=
      List.getElem?_eq_getElem _
    have hxA : (fvsP ++ xFvs)[nP + i]? = some (xFvs[i]'(by rw [hD.xLen]; exact hi)) := by
      rw [List.getElem?_append_right (by rw [hD.pLen]; omega), hD.pLen, Nat.add_sub_cancel_left]
      exact hx
    obtain ⟨-, hws, -, -, -⟩ := hO.var (nP + i) _ hxA
    refine ⟨_, hx, hws, ?_⟩
    intro l hl ⟨hr, hlt⟩
    have hge := hr.1
    obtain ⟨x', hx', hlater, -⟩ := hrecGet (l.1 - nP)
      (by rw [show nP + (l.1 - nP) = l.1 from by omega]; exact hr) (by omega)
    have hmem : (xFvs[i]'(by rw [hD.xLen]; exact hi)) ∈ xFvs.drop (l.1 - nP + 1) := by
      refine List.mem_of_getElem? (i := i - (l.1 - nP + 1)) ?_
      rw [List.getElem?_drop, show l.1 - nP + 1 + (i - (l.1 - nP + 1)) = i from by omega]
      exact hx
    exact mentionsFvar_false (hlater _ hmem) l hl (by omega)
  -- a reflexive field's opened telescope (task #202): its domains and
  -- body are scoped and leaf-free of the recursive variables below
  -- the field, and read to the telescope entries and the readings
  have hreflGet : ∀ i x, xFvs[i]? = some x → ks.getD i .ordinary = .reflexive → i < nF →
      ∃ afvs body,
        openPisAtFvars ((tss ψ).getD i []).length x.fvarTypeD (nP + i) = some (afvs, body) ∧
        (∀ k a, afvs[k]? = some a → Expr.WScoped (nP + i + k) a.fvarTypeD ∧
          (∀ l ∈ a.fvarTypeD.fvarLeaves, ¬ (recAt nP ks l.1 ∧ l.1 < nP + i)) ∧
          denoteMeta mp.base2.acval env ψ (nP + i + k) a.fvarTypeD
            = some (((tss ψ).getD i []).getD k default).2.2) ∧
        Expr.WScoped (nP + i + ((tss ψ).getD i []).length) body ∧
        (∀ l ∈ body.fvarLeaves, ¬ (recAt nP ks l.1 ∧ l.1 < nP + i)) ∧
        DenoteMetaSpine mp.base2.acval env ψ (nP + i + ((tss ψ).getD i []).length)
          (body.getAppArgs.drop nP) ((Eiss ψ).getD i []) := by
    intro i x hx hk hi
    obtain ⟨afvs, body, hop, -, hdoms, hsp⟩ := hD.reflOpen ψ i x hx hk
    obtain ⟨x', hx', hws, hlf⟩ := hdom i hi
    rw [hx] at hx'
    obtain rfl := Option.some.inj hx'
    have hleaves := openPisAtFvars_leaf_bound hop
    have hwsAll := openPisAtFvars_WScoped _ _ _ hop hws
    refine ⟨afvs, body, hop, fun k a hk' => ⟨openPisAtFvars_typeWScoped _ hop hws k a hk',
      fun l hl ⟨hr, hlt⟩ => ?_, hdoms k a hk'⟩, hwsAll.2, fun l hl ⟨hr, hlt⟩ => ?_, hsp⟩
    · rcases hleaves.1 a (List.mem_of_getElem? hk') l hl with h | h
      · exact hlf l h ⟨hr, hlt⟩
      · omega
    · rcases hleaves.2 l hl with h | h
      · exact hlf l h ⟨hr, hlt⟩
      · omega
  have hQlt : ∀ i q, recAt nP ks q ∧ q < nP + i → q < nP + i := fun _ _ h => h.2
  have hne_refl : ∀ i, ks.getD i .ordinary = .recursive → ks.getD i .ordinary ≠ .reflexive := by
    intro i hk h
    rw [hk] at h
    cases h
  refine ⟨hD.ksLen, hlenFs, by rw [hD.lenE ψ, hlenIds], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the entries mention no recursive slot below them
    intro i hi
    obtain ⟨x, hx, hws, hlf⟩ := hdom i hi
    rw [drop_map_getD hlenDs hi]
    exact noBVar_of_leaf_free mp.base2 (nP + i) x.fvarTypeD hws (hQlt i) hlf (hD.domRead ψ i x hx)
  · -- nor do a reflexive field's telescope domains
    intro i hi hr k d hkd
    have hk := hr.2
    rw [Nat.add_sub_cancel_left] at hk
    rcases hk with hk | hk
    · rw [hD.tssNone ψ i (hne_refl i hk)] at hkd
      exact nomatch hkd
    · obtain ⟨x, hx, -, -⟩ := hrecGet i hr hi
      obtain ⟨afvs, body, hop, hdoms, -, -, -⟩ := hreflGet i x hx hk hi
      have hlenA := openPisAtFvars_length _ hop
      have hk' : k < afvs.length := by
        rw [hlenA]; exact (List.getElem?_eq_some_iff.mp hkd).1
      obtain ⟨hws, hlf, hread⟩ := hdoms k _ (List.getElem?_eq_getElem hk')
      have hd : d.2.2 = (((tss ψ).getD i []).getD k default).2.2 := by
        rw [List.getD_eq_getElem?_getD, hkd]; rfl
      rw [hd]
      exact noBVar_of_leaf_free mp.base2 (nP + i + k) _ hws (fun q h => by have := h.2; omega)
        hlf hread
  · -- nor do the recursive slots' index expressions
    intro i hi hr E hE
    have hk := hr.2
    rw [Nat.add_sub_cancel_left] at hk
    obtain ⟨x, hx, hws, hlf⟩ := hdom i hi
    rcases hk with hk | hk
    · rw [hD.tssNone ψ i (hne_refl i hk), List.length_nil, Nat.add_zero]
      obtain ⟨a, ha, hra⟩ := DenoteMetaSpine.mem_inv (hD.eisRead ψ i x hx hk) E hE
      have ha' : a ∈ x.fvarTypeD.getAppArgs := List.mem_of_mem_drop ha
      exact noBVar_of_leaf_free mp.base2 (nP + i) a (WScoped_of_mem_getAppArgs _ a hws ha')
        (hQlt i) (fun l hl => hlf l (mem_fvarLeaves_of_getAppArgs _ a ha' l hl)) hra
    · obtain ⟨afvs, body, hop, -, hwsB, hlfB, hspB⟩ := hreflGet i x hx hk hi
      obtain ⟨a, ha, hra⟩ := DenoteMetaSpine.mem_inv hspB E hE
      have ha' : a ∈ body.getAppArgs := List.mem_of_mem_drop ha
      exact noBVar_of_leaf_free mp.base2 _ a (WScoped_of_mem_getAppArgs _ a hwsB ha')
        (fun q h => by have := h.2; omega)
        (fun l hl => hlfB l (mem_fvarLeaves_of_getAppArgs _ a ha' l hl)) hra
  · -- nor do the residual's index readings
    intro E hE
    obtain ⟨a, ha, hra⟩ := DenoteMetaSpine.mem_inv (hD.idxRead ψ) E hE
    rw [hD.idxEq] at ha
    have ha' : a ∈ xrest.getAppArgs := List.mem_of_mem_drop ha
    refine noBVar_of_leaf_free mp.base2 (nP + nF) a
      (WScoped_of_mem_getAppArgs _ a hO.bodyScoped.1 ha') (hQlt nF) ?_ hra
    intro l hl ⟨hr, hlt⟩
    have hge := hr.1
    obtain ⟨-, -, -, hres⟩ := hrecGet (l.1 - nP)
      (by rw [show nP + (l.1 - nP) = l.1 from by omega]; exact hr) (by omega)
    exact mentionsFvar_false hres l (mem_fvarLeaves_of_getAppArgs _ a ha' l hl) (by omega)
  · -- the entries, graded at a shadow-fitting spine
    intro i hi as' hsp'
    have hlenA : as'.length = i := by
      rw [hsp'.length_eq, List.length_take, shadowFs_length]; omega
    have hsat : Sat V ((shadowCtx nP ks (nP + nF) (((ds ψ).map (·.2.2)).reverse)).drop
        (nP + nF - (nP + i))) (consList as' ρp) := by
      rw [shadowCtx_drop_fields hlenDs (Nat.le_of_lt hi)]
      exact sat_of_spineFit hρp' hsp'
    obtain ⟨hokP, hbnd⟩ := hkey (nP + i) (by omega) _ hsat
    rw [reverse_getD_field hlenDs hi] at hokP hbnd
    refine ⟨hokP.1, fun hnr hw => hbnd (Nat.le_add_right _ _) hnr hw, fun hr => ?_⟩
    -- the fit, through the family's λ-tower, at a frame reading the
    -- parameters below `e` field-and-telescope values
    have fitAt : ∀ (σas : List V) (e : Nat), σas.length = e →
        WellDenoted V (consList σas ρp) (AnnotTerm.mkAppN (mp.base2.acval T ψ)
          (paramBvarsAt nP (nP + e) ++ (Eiss ψ).getD i [])) →
        ((Eiss ψ).getD i []).length = nIdx →
        (∀ E ∈ (Eiss ψ).getD i [], WellDenoted V (consList σas ρp) E) ∧
        SpineFit ρp (((ppsAll ψ).drop nP).map (·.2.2))
          (((Eiss ψ).getD i []).map (interp V (consList σas ρp))) := by
      intro σas e he hokA hEl
      obtain ⟨-, hargs⟩ := WellDenoted.mkAppN_inv hokA
      refine ⟨fun E hE => hargs E (List.mem_append_right _ hE), ?_⟩
      obtain ⟨B, hB⟩ := hleafT ψ
      have hK : Term.bvarsBelow 0 (mp.base2.acval T ψ).erase := mp.base2.cval_closedL T ψ
      rw [hB] at hK
      have hf : interp V (consList σas ρp) (mp.base2.acval T ψ)
          = interp V (fun j => ρp (j + nP)) (mkLamsC (resSort.eval ψ + 1) (ppsAll ψ) B) := by
        rw [hB]; exact interp_closed (V := V) hK _ _
      have hlenArgs : (paramBvarsAt nP (nP + e) ++ (Eiss ψ).getD i []).length = nP + nIdx := by
        rw [List.getD_eq_getElem?_getD] at hEl
        simp [paramBvarsAt, hEl]
      have hfit := spineFit_of_wellDenoted_lams (u := resSort.eval ψ + 1) (Nat.succ_ne_zero _) (b := B)
        (args := paramBvarsAt nP (nP + e) ++ (Eiss ψ).getD i []) (ds := ppsAll ψ)
        (σ := fun j => ρp (j + nP)) (ρ := consList σas ρp) (f := mp.base2.acval T ψ)
        (by rw [hlenArgs, hFD.len ψ]; exact Nat.le_refl _) hokA hf
      rw [hlenArgs, List.take_of_length_le (by rw [hFD.len ψ]; exact Nat.le_refl _),
        ← List.take_append_drop nP (ppsAll ψ), List.map_append, List.map_append] at hfit
      obtain ⟨as₁, as₂, heq, h1, h2⟩ := spineFit_append_inv hfit
      have hlen₁ : as₁.length = nP := by
        rw [h1.length_eq, List.length_map, List.length_take, hFD.len ψ]; omega
      have hps : (paramBvarsAt nP (nP + e)).map (interp V (consList σas ρp))
          = (List.range nP).reverse.map ρp := by
        apply map_paramBvarsAt_interp
        intro j
        rw [← he]; exact consList_apply_add σas ρp j
      obtain ⟨rfl, rfl⟩ := List.append_inj heq (by rw [hlen₁]; simp [paramBvarsAt])
      rw [hps, consList_range_reverse] at h2
      exact h2
    have hk := hr.2
    rw [Nat.add_sub_cancel_left] at hk
    rcases hk with hk | hk
    · -- a finitary field: the entry is the family at the readings
      rw [hD.tssNone ψ i (hne_refl i hk)]
      have hentry := hD.recEntry ψ i hk hi
      rw [drop_map_getD hlenDs hi, hentry] at hokP
      obtain ⟨hok, hfit⟩ := fitAt as' i hlenA hokP.1 (hD.eisLen ψ i hk hi)
      exact SlotFit.of_fin hok hfit
    · -- a reflexive field (task #202): the entry a Π-tower over the
      -- telescope; at a `Type`-valued block the telescope's domains are
      -- bounded at the family's regime (`fixTeleBound_of`, Stage B)
      have hentry := hD.reflEntry ψ i hk hi
      rw [drop_map_getD hlenDs hi, hentry] at hokP
      obtain ⟨hF, hB⟩ := WellDenoted_mkPisAV_inv hokP.1
      refine ⟨?_, fun d hd => hD.tssBits ψ i d hd, fun bs hsp => ?_⟩
      · refine fieldsOkB_of_pointwise fun k hkT bs hbs => ?_
        rw [List.length_map] at hkT
        rw [getD_map_snd hkT]
        have hbs' : SpineFit (consList as' ρp) ((((tss ψ).getD i []).take k).map (·.2.2)) bs := by
          rw [List.map_take]; exact hbs
        refine ⟨?_, fun hw => (fixTeleBound_of hμ mp hCtor hProp hD ψ hw hi hk hρp' hsp' k hkT bs hbs').2⟩
        have := hF.wellDenoted_at k (by rw [List.length_map]; exact hkT) bs hbs
        rwa [getD_map_snd hkT] at this
      · have hokB := hB bs hsp
        rw [← consList_append] at hokB
        have hlenAB : (as' ++ bs).length = i + ((tss ψ).getD i []).length := by
          rw [List.length_append, hlenA, hsp.length_eq, List.length_map]
        rw [Nat.add_assoc] at hokB
        exact fitAt (as' ++ bs) _ hlenAB hokB (hD.eisLenRefl ψ i hk hi)
  · -- the residual's index readings, graded at a shadow-fitting field spine
    intro as' hsp' E hE
    have hsat : Sat V (shadowCtx nP ks (nP + nF) (((ds ψ).map (·.2.2)).reverse))
        (consList as' ρp) := by
      have := shadowCtx_drop_fields (ks := ks) hlenDs (Nat.le_refl nF)
      rw [Nat.sub_self, List.drop_zero,
        List.take_of_length_le (by rw [shadowFs_length]; exact Nat.le_refl _)] at this
      rw [this]
      exact sat_of_spineFit hρp' hsp'
    have hokR := hkeyR _ hsat
    unfold ctorBodyAVI at hokR
    obtain ⟨-, hargs⟩ := WellDenoted.mkAppN_inv hokR.1
    exact hargs E (List.mem_append_right _ hE)

end ConLeche.Model
