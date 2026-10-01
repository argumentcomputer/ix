module

public import ConLeche.Model.IndCross
public import ConLeche.Verify.BridgeWfImp
import ConLeche.Model.Annot.BitInst
import ConLeche.Verify.Denote.OpenRevDenote

public section

/-!
# The zipper's field-branch core, at the reading (task #161, part 4)

`zipFieldTermEq`'s transpose: the scattered constructor run's
`cnP + j`-th domain reads at *its own* frame depth `rP + j`, its leaves
sit among the first `rP + j` openers, and its spine instantiation at
the fired statement values is the constructor tower's own domain
instantiated at the mixed spine.

The constructor run's spine `sp` is **abstract**, as in v1: on a
`.plain` fire its parameter positions are the frame's own openers, on
a `.nested` one the instantiated pins.  The stage reads them only
through the leaf/scope discipline (`hspLeaf`/`hspScope`) and the
crossing datum `hmixsp`.

**One conjunct changes shape, and it is the part-4 tax.**  v1 concludes
`Expr.fvarsBelow (rP + j)` for the domain; the P stage concludes
`Expr.WScoped (rP + j)`, because `denoteMeta_lift` — the step that turns
the frame-depth reading into the low-depth one — needs the annotations
scoped too.  The extra strength costs one `WScoped_sharpen` against the
same leaf bound v1 already establishes, so the *work* is unchanged;
what changes is that the conclusion has to say it.

`TVj`'s closedness is the **lifting equation**, not `Term.Closed`:
that is the currency the reading's carrier stores, and
`instSeqAV_eq_self_of_closed` consumes it directly.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name BinderMeta)

universe w

variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AnnotTerm}

set_option maxHeartbeats 3200000 in
/-- **The field domain, crossed, at the reading** (`zipFieldTermEq`). -/
theorem zipFieldTermEq
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (acval n ψ).inst y k = acval n ψ)
    {rP cnP cnF : Nat} {fvs : List Expr}
    {ctyR : Expr} (hCwR : ctyR.hasFvar = false)
    (hCbR : ctyR.looseBVarsBounded 0 = true)
    {TVj : AnnotTerm}
    (hTVjK : denoteMeta acval env φ (rP + cnF) ctyR = some TVj)
    (hTVjcl : ∀ k : Nat, TVj.liftN 1 k = TVj)
    {Γj : List AnnotTerm} {Rj : AnnotTerm}
    (htowerJ : PiTeleAV (cnP + cnF) TVj Γj Rj)
    {sp : List Expr} (hsplen : sp.length = cnP + cnF)
    (hspLeaf : ∀ (q : Nat) (x : Expr), sp[q]? = some x →
      ∀ l ∈ x.fvarLeaves,
        Expr.fvar l.1 l.2 ∈ fvs ∧ l.1 < rP + (q + 1 - cnP))
    (hspScope : ∀ (q : Nat) (x : Expr), sp[q]? = some x →
      Expr.WScoped (rP + cnF) x ∧ x.looseBVarsBounded 0 = true)
    {cdoms : List Expr} {cres : Expr}
    (hcinst : Expr.instPisAt sp ctyR = some (cdoms, cres))
    {zs : List AnnotTerm} (hzslen : zs.length = rP + cnF)
    {mix : List AnnotTerm} (hmixlen : mix.length = cnP + cnF)
    (hmixsp : ∀ (q : Nat) (x : Expr), sp[q]? = some x →
      ∃ w0, denoteMeta acval env φ (rP + cnF) x = some w0 ∧
        mix[q]? = some (AnnotTerm.instSeq zs (rP + cnF - 1) w0))
    {j : Nat} (hj : j < cnF) :
    Expr.WScoped (rP + j) (cdoms.getD (cnP + j) default) ∧
    (∀ l ∈ (cdoms.getD (cnP + j) default).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ fvs ∧ l.1 < rP + j) ∧
    ∃ vdomLow,
      denoteMeta acval env φ (rP + j) (cdoms.getD (cnP + j) default)
        = some vdomLow ∧
      AnnotTerm.instSeq (zs.take (rP + j)) (rP + j - 1) vdomLow
        = AnnotTerm.instSeq (mix.take (cnP + j)) (cnP + j - 1)
            (Γj.getD (cnP + cnF - 1 - (cnP + j)) default) := by
  have hΓjlen : Γj.length = cnP + cnF := htowerJ.length
  -- the scattered spine's per-element facts
  have hspFacts : ∀ (q : Nat) (x : Expr), sp[q]? = some x →
      (∃ w, denoteMeta acval env φ (rP + cnF) x = some w) ∧
        Expr.WScoped (rP + cnF) x ∧ x.looseBVarsBounded 0 = true := by
    intro q x hx
    obtain ⟨w0, hw0, _⟩ := hmixsp q x hx
    exact ⟨⟨w0, hw0⟩, hspScope q x hx⟩
  -- truncate the scattered run at `cnP + j`
  obtain ⟨midJ, htr, hdr⟩ := instPisAt_take sp (cnP + j) hcinst
  obtain ⟨x0, sp', hsp0⟩ : ∃ x sp', sp.drop (cnP + j) = x :: sp' := by
    rcases hsp : sp.drop (cnP + j) with _ | ⟨x, sp'⟩
    · exfalso
      have := congrArg List.length hsp
      rw [List.length_drop, hsplen] at this
      simp at this
      omega
    · exact ⟨x, sp', rfl⟩
  rw [hsp0] at hdr
  obtain ⟨domJ, bodyJ, mbJ, rfl, hds⟩ : ∃ domJ bodyJ mbJ,
      midJ = .forallE domJ bodyJ mbJ ∧
      (cdoms.drop (cnP + j))[0]? = some domJ := by
    cases midJ with
    | forallE domJ bodyJ mbJ =>
      simp only [Expr.instPisAt] at hdr
      rcases hrec : Expr.instPisAt sp' (bodyJ.instantiate1 x0)
        with _ | ⟨ds', rs'⟩
      · rw [hrec] at hdr
        exact nomatch hdr
      · rw [hrec] at hdr
        have hdr' : (some (domJ :: ds', rs') :
            Option (List Expr × Expr))
            = some (cdoms.drop (cnP + j), cres) := hdr
        injection hdr' with hdr''
        have h1 : domJ :: ds' = cdoms.drop (cnP + j) :=
          congrArg Prod.fst hdr''
        refine ⟨domJ, bodyJ, mbJ, rfl, ?_⟩
        rw [← h1]
        rfl
    | bvar i => simp [Expr.instPisAt] at hdr
    | sort u => simp [Expr.instPisAt] at hdr
    | const c us => simp [Expr.instPisAt] at hdr
    | fvar a c => simp [Expr.instPisAt] at hdr
    | lam b c d => simp [Expr.instPisAt] at hdr
    | app a b => simp [Expr.instPisAt] at hdr
    | letE b c d => simp [Expr.instPisAt] at hdr
    | proj a b c => simp [Expr.instPisAt] at hdr
    | lit l => simp [Expr.instPisAt] at hdr
  have hcdlen : cdoms.length = cnP + cnF := by
    have h := instPisAt_length _ hcinst
    rw [hsplen] at h
    omega
  have hdomJidx : cdoms[cnP + j]? = some domJ := by
    have h0 : (cdoms.drop (cnP + j))[0]? = some domJ := hds
    rwa [List.getElem?_drop, Nat.add_zero] at h0
  have hdomJ : cdoms.getD (cnP + j) default = domJ := by
    rw [List.getD, hdomJidx]
    rfl
  -- leaves of the domain: among the first `rP + j` openers
  have hleafDom : ∀ l ∈ domJ.fvarLeaves,
      Expr.fvar l.1 l.2 ∈ fvs ∧ l.1 < rP + j := by
    intro l hl
    have hlmid : l ∈ (Expr.forallE domJ bodyJ mbJ).fvarLeaves := by
      rw [Expr.fvarLeaves]
      exact List.mem_append_left _ hl
    rcases instPisAt_leaves _ htr l (Or.inr hlmid) with hty | ⟨a, ha, hla⟩
    · exfalso
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hCwR] at hty
      exact nomatch hty
    · obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
      have hqm : q < cnP + j := by
        rcases Nat.lt_or_ge q (cnP + j) with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none (by rw [List.length_take]; omega)]
            at hq
          exact nomatch hq
      have hq' : sp[q]? = some a := by
        rw [← List.getElem?_take_of_lt hqm]
        exact hq
      obtain ⟨hmem, hlt⟩ := hspLeaf q a hq' l hla
      exact ⟨hmem, by omega⟩
  -- the domain's scope, sharpened from the leaves (the part-4 tax)
  have hwsCty : Expr.WScoped (rP + cnF) ctyR :=
    Expr.WScoped.of_not_hasFvar hCwR
  have hwsDomBig : Expr.WScoped (rP + cnF + (cnP + j)) domJ :=
    instPisAt_index_WScoped sp hcinst hwsCty
      (fun i a ha => ((hspScope i a ha).1).mono (by omega))
      (cnP + j) domJ hdomJidx
  have hwsDom : Expr.WScoped (rP + j) domJ :=
    WScoped_sharpen hwsDomBig (fun l hl => (hleafDom l hl).2)
  -- the truncated residual reads at the frame depth
  have hfbCty : Expr.fvarsBelow (rP + cnF) ctyR := by
    refine Expr.fvarsBelow_of_fvarLeaves fun l hl => ?_
    rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hCwR] at hl
    exact nomatch hl
  have hspTake : ∀ (q : Nat) (x : Expr),
      (sp.take (cnP + j))[q]? = some x → sp[q]? = some x ∧ q < cnP + j := by
    intro q x hx
    have hqm : q < cnP + j := by
      rcases Nat.lt_or_ge q (cnP + j) with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none (by rw [List.length_take]; omega)]
          at hx
        exact nomatch hx
    rw [List.getElem?_take_of_lt hqm] at hx
    exact ⟨hx, hqm⟩
  obtain ⟨vMid, hvMid⟩ := instPisAt_denoteMeta_defined hacl hainst _ htr
    (D := rP + cnF)
    (fun q x hx => hspFacts q x (hspTake q x hx).1)
    hfbCty hCbR hTVjK
  -- read the pi apart: the domain reads at depth `K`
  rw [denoteMeta_forallE] at hvMid
  rcases hvd : denoteMeta acval env φ (rP + cnF) domJ with _ | vDomK
  · rw [hvd] at hvMid
    exact nomatch hvMid
  rw [hvd] at hvMid
  rcases hvb : denoteMeta acval env φ (rP + cnF + 1)
      (bodyJ.instantiate1 (.fvar (rP + cnF) domJ)) with _ | vBodyK
  · rw [hvb] at hvMid
    exact nomatch hvMid
  rw [hvb] at hvMid
  obtain rfl : vMid = .pi 0 (pwBit φ mbJ.pw) vDomK vBodyK :=
    (Option.some.inj hvMid).symm
  -- the domain at its own depth, lifted
  have hlow := denoteMeta_lift (acval := acval) (env := env) (φ := φ) hacl
    (p := rP + j) (e := domJ) hwsDom (rP + cnF) (by omega)
  rw [hvd] at hlow
  rcases hvl : denoteMeta acval env φ (rP + j) domJ with _ | vdomLow
  · rw [hvl] at hlow
    exact nomatch hlow
  rw [hvl] at hlow
  have hVK : vDomK = AnnotTerm.liftN (rP + cnF - (rP + j)) vdomLow 0 :=
    Option.some.inj hlow
  refine ⟨by rw [hdomJ]; exact hwsDom, by rw [hdomJ]; exact hleafDom,
    vdomLow, by rw [hdomJ]; exact hvl, ?_⟩
  -- the mid tower of the constructor
  obtain ⟨mid', hpre, hpost⟩ := htowerJ.prefix (cnP + j) (by omega)
  have hlenTake : (sp.take (cnP + j)).length = cnP + j := by
    rw [List.length_take, hsplen]
    omega
  have htow : PiTeleAV (sp.take (cnP + j)).length
      (AnnotTerm.instSeq zs (rP + cnF - 1) TVj)
      (Γj.drop (cnP + cnF - (cnP + j))) mid' := by
    rw [hlenTake, instSeqAV_eq_self_of_closed hTVjcl]
    exact hpre
  have hwsCond : ∀ (q : Nat) (x : Expr),
      (sp.take (cnP + j))[q]? = some x →
      ∃ w0, denoteMeta acval env φ (rP + cnF) x = some w0 ∧
        (mix.take (cnP + j))[q]? = some
          (AnnotTerm.instSeq zs (rP + cnF - 1) w0) := by
    intro q x hx
    obtain ⟨hx', hqm⟩ := hspTake q x hx
    obtain ⟨w0, hw0, hmx⟩ := hmixsp q x hx'
    exact ⟨w0, hw0, by rw [List.getElem?_take_of_lt hqm]; exact hmx⟩
  have hvMid' : denoteMeta acval env φ (rP + cnF)
      (Expr.forallE domJ bodyJ mbJ)
      = some (.pi 0 (pwBit φ mbJ.pw) vDomK vBodyK) := by
    rw [denoteMeta_forallE, hvd, hvb]
    rfl
  have hcross := instPisAt_denoteMeta_cross hacl hainst _ htr
    (D := rP + cnF) (vals := zs) hzslen
    (fun q x hx => ((hspFacts q x (hspTake q x hx).1).2))
    hfbCty hCbR hTVjK hvMid'
    (ws := mix.take (cnP + j))
    (by rw [List.length_take, List.length_take, hmixlen, hsplen])
    hwsCond htow
  -- split the crossed pis and read the domains apart
  obtain ⟨uN, vN, Anext, Bnext, rfl, hAnext⟩ :
      ∃ uN vN A B, mid' = .pi uN vN A B ∧
        A = Γj.getD (cnP + cnF - 1 - (cnP + j)) default := by
    have hcnt : cnP + cnF - (cnP + j) = (cnF - j - 1) + 1 := by omega
    rw [hcnt] at hpost
    generalize hg : List.take (cnF - j - 1 + 1) Γj = Γt at hpost
    obtain ⟨uN, vN, A, B, Γ'', rfl, hΓt, htl⟩ := hpost.succ_inv
    refine ⟨uN, vN, A, B, rfl, ?_⟩
    have h1 : (Γ'' ++ [A]).getD Γ''.length default = A := by
      rw [List.getD, List.getElem?_append_right (Nat.le_refl _),
        Nat.sub_self]
      rfl
    have hΓ''len : Γ''.length = cnF - j - 1 := htl.length
    have h2 : (List.take (cnF - j - 1 + 1) Γj).getD
        (cnF - j - 1) default = Γj.getD (cnF - j - 1) default := by
      rw [List.getD, List.getD, List.getElem?_take_of_lt (by omega)]
    rw [show cnP + cnF - 1 - (cnP + j) = cnF - j - 1 from by omega,
      ← h2, hg, hΓt, ← hΓ''len, h1]
  rw [instSeqAV_pi _ _ _ _ _ _ (by rw [hzslen]; omega),
    instSeqAV_pi _ _ _ _ _ _ (by
      rw [List.length_take, hmixlen]
      omega)] at hcross
  have hdomEq : AnnotTerm.instSeq zs (rP + cnF - 1) vDomK
      = AnnotTerm.instSeq (mix.take (cnP + j)) (cnP + j - 1) Anext := by
    injection hcross with _ _ h3 _
    rw [show (List.take (cnP + j) mix).length = cnP + j from by
      rw [List.length_take, hmixlen]
      omega] at h3
    exact h3
  have habs : AnnotTerm.instSeq zs (rP + cnF - 1)
      (AnnotTerm.liftN (rP + cnF - (rP + j)) vdomLow 0)
      = AnnotTerm.instSeq (zs.take (rP + j)) (rP + j - 1) vdomLow :=
    instSeqAV_absorb_left hzslen (by omega)
  calc AnnotTerm.instSeq (zs.take (rP + j)) (rP + j - 1) vdomLow
      = AnnotTerm.instSeq zs (rP + cnF - 1)
          (AnnotTerm.liftN (rP + cnF - (rP + j)) vdomLow 0) := habs.symm
    _ = AnnotTerm.instSeq zs (rP + cnF - 1) vDomK := by rw [← hVK]
    _ = AnnotTerm.instSeq (mix.take (cnP + j)) (cnP + j - 1) Anext :=
        hdomEq
    _ = AnnotTerm.instSeq (mix.take (cnP + j)) (cnP + j - 1)
          (Γj.getD (cnP + cnF - 1 - (cnP + j)) default) := by
        rw [← hAnext]

end ConLeche.Model
