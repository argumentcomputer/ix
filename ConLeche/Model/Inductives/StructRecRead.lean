module

public import ConLeche.Model.Inductives.StructRecKit2
public import ConLeche.Verify.Inductives.StructRec
import ConLeche.Model.Annot.BitInst
public section

/-!
# The generated recursor, read (task #175 S2)

The direct install stores the recursor it generates
(`structRecTy`/`structRecRhs`), so its reading is **syntactic**: the
generated type reads to the Π-tower

    mkPisAV (params (bit ℓ) ++ [motive, minor, major]) (motive t)

whose three special entries are spelled out (`motiveAV`, `minorAV`,
`majorAV`) over the type former's and the constructor's readings, and
the generated rule reads to the λ-tower over the same data
(`denoteP_structRecRhs`).  No frame pin is consumed: the recursor's
data (`recData_of`) comes from these readings, the fabricated type's
own inference run (its grading, `inferRow`) and the elimination datum
the generator wrote (its bits, `zeronessOf_sound`).

The two generic pieces are the readings of the binder walks
(`denoteMeta_replacePisPw`, `denoteMeta_pisToLamsPw`): a walk over an
opened telescope reads to the tower over the telescope's own domain
readings, bits reset, over the body instantiated at the opening's
variables.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps StructParts
  BinderMeta PropWhen)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AnnotTerm}

/-! ## Bits reset -/

/-- Binder data with every codomain bit reset to `b`. -/
@[expose] def rebit (b : Nat) (ds : List (Nat × Nat × AnnotTerm)) : List (Nat × Nat × AnnotTerm) :=
  ds.map fun d => (d.1, b, d.2.2)

@[simp] theorem rebit_nil (b : Nat) : rebit b [] = [] := rfl

@[simp] theorem rebit_cons (b : Nat) (d : Nat × Nat × AnnotTerm) (ds : List (Nat × Nat × AnnotTerm)) :
    rebit b (d :: ds) = (d.1, b, d.2.2) :: rebit b ds := rfl

@[simp] theorem rebit_length (b : Nat) (ds : List (Nat × Nat × AnnotTerm)) :
    (rebit b ds).length = ds.length := by simp [rebit]

@[simp] theorem rebit_map_dom (b : Nat) (ds : List (Nat × Nat × AnnotTerm)) :
    (rebit b ds).map (·.2.2) = ds.map (·.2.2) := by simp [rebit]

theorem rebit_getD (b : Nat) (ds : List (Nat × Nat × AnnotTerm)) (j : Nat) (hj : j < ds.length) :
    (rebit b ds).getD j default = ((ds.getD j default).1, b, (ds.getD j default).2.2) := by
  simp only [rebit, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj,
    Option.map_some, Option.getD_some]

theorem mem_rebit {b : Nat} {ds : List (Nat × Nat × AnnotTerm)} {d : Nat × Nat × AnnotTerm}
    (h : d ∈ rebit b ds) : d.2.1 = b := by
  obtain ⟨d', -, rfl⟩ := List.mem_map.mp h
  rfl

/-! ## The binder walks, read -/

/-- **The `∀`-walk's reading**: the telescope's own domain readings,
bits reset, over the body at the opening's variables. -/
theorem denoteMeta_replacePisPw {pw : PropWhen} :
    ∀ (k : Nat) {d : Nat} {e b r : Expr} {fvs : List Expr} {o : Expr} {ea : AnnotTerm}
      {pds : List (Nat × Nat × AnnotTerm)} {R : AnnotTerm},
      Expr.replacePisPw pw k e b = some r →
      openPisAtFvars k e d = some (fvs, o) →
      denoteMeta acval env φ d e = some ea →
      stripPisAV k ea = some (pds, R) →
      denoteMeta acval env φ d r
        = (denoteMeta acval env φ (d + k) (Expr.instSeq fvs (k - 1) b)).map
            (mkPisAV (rebit (pwBit φ pw) pds))
  | 0, d, e, b, r, fvs, o, ea, pds, R, hr, hop, _, hst => by
    simp only [Expr.replacePisPw, Option.some.injEq] at hr
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    simp only [stripPisAV, Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, -⟩ := hop
    obtain ⟨rfl, -⟩ := hst
    subst hr
    simp only [Nat.add_zero, Expr.instSeq, rebit_nil, mkPisAV, Option.map_id']
  | k + 1, d, e, b, r, fvs, o, ea, pds, R, hr, hop, hea, hst => by
    match e, hr, hop with
    | .forallE ty rest m, hr, hop =>
      simp only [Expr.replacePisPw, Option.map_eq_some_iff] at hr
      obtain ⟨r', hr', rfl⟩ := hr
      simp only [openPisAtFvars] at hop
      split at hop
      · next fvs' o' hop' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hea
        simp only [stripPisAV, Option.map_eq_some_iff] at hst
        obtain ⟨⟨pds', R'⟩, hst', heq⟩ := hst
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        have hr'' := ConLeche.replacePisPw_instantiate1 (v := .fvar d ty) k 0 hr'
        rw [Nat.zero_add] at hr''
        have ih := denoteMeta_replacePisPw k hr'' hop' hba hst'
        rw [denoteMeta_forallE, hta]
        show (denoteMeta acval env φ (d + 1) (r'.instantiate1 (.fvar d ty)) >>= fun ba =>
          some (AnnotTerm.pi 0 (pwBit φ pw) ta ba)) = _
        rw [ih, show d + (k + 1) = d + 1 + k from by omega]
        show _ = (denoteMeta acval env φ (d + 1 + k)
          (Expr.instSeq fvs' (k + 1 - 1 - 1) (b.instantiate1 (.fvar d ty) (k + 1 - 1)))).map _
        rw [show k + 1 - 1 = k from rfl]
        cases denoteMeta acval env φ (d + 1 + k)
            (Expr.instSeq fvs' (k - 1) (b.instantiate1 (.fvar d ty) k)) <;> rfl
      · exact nomatch hop
    | .bvar _, hr, _ | .fvar _ _, hr, _ | .sort _, hr, _ | .const _ _, hr, _
    | .app _ _, hr, _ | .lam _ _ _, hr, _ | .letE _ _ _, hr, _ | .lit _, hr, _
    | .proj _ _ _, hr, _ => simp [Expr.replacePisPw] at hr

/-- **The `λ`-walk's reading**: the λ-tower over the telescope's
domain readings with bit `pw`, over the body at the opening's
variables. -/
theorem denoteMeta_pisToLamsPw {pw : PropWhen} :
    ∀ (k : Nat) {d : Nat} {e b r : Expr} {fvs : List Expr} {o : Expr} {ea : AnnotTerm}
      {pds : List (Nat × Nat × AnnotTerm)} {R : AnnotTerm},
      Expr.pisToLamsPw pw k e b = some r →
      openPisAtFvars k e d = some (fvs, o) →
      denoteMeta acval env φ d e = some ea →
      stripPisAV k ea = some (pds, R) →
      denoteMeta acval env φ d r
        = (denoteMeta acval env φ (d + k) (Expr.instSeq fvs (k - 1) b)).map
            (mkLamsAV (pds.map fun p => (pwBit φ pw, p.2.2)))
  | 0, d, e, b, r, fvs, o, ea, pds, R, hr, hop, _, hst => by
    simp only [Expr.pisToLamsPw, Option.some.injEq] at hr
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    simp only [stripPisAV, Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, -⟩ := hop
    obtain ⟨rfl, -⟩ := hst
    subst hr
    simp only [Nat.add_zero, Expr.instSeq, List.map_nil, mkLamsAV, Option.map_id']
  | k + 1, d, e, b, r, fvs, o, ea, pds, R, hr, hop, hea, hst => by
    match e, hr, hop with
    | .forallE ty rest m, hr, hop =>
      simp only [Expr.pisToLamsPw, Option.map_eq_some_iff] at hr
      obtain ⟨r', hr', rfl⟩ := hr
      simp only [openPisAtFvars] at hop
      split at hop
      · next fvs' o' hop' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hea
        simp only [stripPisAV, Option.map_eq_some_iff] at hst
        obtain ⟨⟨pds', R'⟩, hst', heq⟩ := hst
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        have hr'' := ConLeche.pisToLamsPw_instantiate1 (v := .fvar d ty) k 0 hr'
        rw [Nat.zero_add] at hr''
        have ih := denoteMeta_pisToLamsPw k hr'' hop' hba hst'
        rw [denoteMeta_lam, hta]
        show (denoteMeta acval env φ (d + 1) (r'.instantiate1 (.fvar d ty)) >>= fun ba =>
          some (AnnotTerm.lam (pwBit φ pw) ta ba)) = _
        rw [ih, show d + (k + 1) = d + 1 + k from by omega]
        show _ = (denoteMeta acval env φ (d + 1 + k)
          (Expr.instSeq fvs' (k + 1 - 1 - 1) (b.instantiate1 (.fvar d ty) (k + 1 - 1)))).map _
        rw [show k + 1 - 1 = k from rfl]
        cases denoteMeta acval env φ (d + 1 + k)
            (Expr.instSeq fvs' (k - 1) (b.instantiate1 (.fvar d ty) k)) <;> rfl
      · exact nomatch hop
    | .bvar _, hr, _ | .fvar _ _, hr, _ | .sort _, hr, _ | .const _ _, hr, _
    | .app _ _, hr, _ | .lam _ _ _, hr, _ | .letE _ _ _, hr, _ | .lit _, hr, _
    | .proj _ _ _, hr, _ => simp [Expr.pisToLamsPw] at hr

/-! ## Syntactic bookkeeping -/

/-- A closed-argument instantiation sequence keeps a telescope's strip. -/
theorem instSeq_stripPis_isSome :
    ∀ (sp : List Expr) (t : Nat) {e : Expr} {n : Nat},
      (e.stripPis n).isSome = true → ((Expr.instSeq sp t e).stripPis n).isSome = true
  | [], _, _, _, h => h
  | a :: sp, t, _, n, h =>
    instSeq_stripPis_isSome sp (t - 1) (Expr.stripPis_instantiate1_isSome (v := a) n t h)

/-- The tail of a longer strip strips the remainder. -/
theorem stripPis_isSome_drop :
    ∀ (k : Nat) {m : Nat} {e : Expr} {bs : List (Expr × BinderMeta)} {mid : Expr},
      (e.stripPis (k + m)).isSome = true → e.stripPis k = some (bs, mid) →
      (mid.stripPis m).isSome = true
  | 0, m, e, bs, mid, h, hs => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, rfl⟩ := hs
    simpa using h
  | k + 1, m, e, bs, mid, h, hs => by
    rw [show k + 1 + m = (k + m) + 1 from by omega] at h
    match e, h, hs with
    | .forallE ty rest mb, h, hs =>
      simp only [Expr.stripPis, Option.isSome_map] at h
      simp only [Expr.stripPis] at hs
      cases hs' : rest.stripPis k with
      | none => rw [hs'] at hs; exact nomatch hs
      | some q =>
        rw [hs'] at hs
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨-, rfl⟩ := hs
        exact stripPis_isSome_drop k h hs'
    | .bvar _, h, _ | .fvar _ _, h, _ | .sort _, h, _ | .const _ _, h, _
    | .app _ _, h, _ | .lam _ _ _, h, _ | .letE _ _ _, h, _ | .lit _, h, _
    | .proj _ _ _, h, _ => simp [Expr.stripPis] at h

/-- An instantiation sequence's index is immaterial at the empty
sequence. -/
theorem instSeq_idx_congr {sp : List Expr} {t t' : Nat} (e : Expr)
    (h : sp = [] ∨ t = t') : Expr.instSeq sp t e = Expr.instSeq sp t' e := by
  rcases h with rfl | rfl <;> rfl

/-- The variables of an opening at depth `0` are closed and indexed by
position, scoped one above their index. -/
theorem opening_vars {n : Nat} {e : Expr} {fvs : List Expr} {o : Expr}
    (hop : openPisAtFvars n e 0 = some (fvs, o)) (hcl : e.hasFvar = false) :
    fvs.length = n ∧
    (∀ (k : Nat) (x : Expr), fvs[k]? = some x → ∃ ty, x = Expr.fvar k ty) ∧
    (∀ a ∈ fvs, a.looseBVarsBounded 0 = true) ∧
    (∀ (i : Nat) (a : Expr), fvs[i]? = some a → Expr.WScoped (0 + i + 1) a) := by
  have hidx := openPisAtFvars_index n e 0 hop
  refine ⟨openPisAtFvars_length n hop, fun k x hx => by
    obtain ⟨ty, h⟩ := hidx k x hx
    exact ⟨ty, by rw [h, Nat.zero_add]⟩, ?_, ?_⟩
  · intro a ha
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, rfl⟩ := hidx q a hq
    rfl
  · intro i a ha
    obtain ⟨ty, rfl⟩ := hidx i a ha
    have hw := openPisAtFvars_typeWScoped n hop (Expr.WScoped.of_not_hasFvar hcl) i _ ha
    simp only [Expr.fvarTypeD, Nat.zero_add] at hw
    simp only [Expr.WScoped, Nat.zero_add]
    exact ⟨Nat.lt_succ_self i, hw⟩

/-- The variables of an opening at any depth: one per binder, indexed
by position from the depth, closed. -/
theorem opening_vars_at {n d : Nat} {e : Expr} {fvs : List Expr} {o : Expr}
    (hop : openPisAtFvars n e d = some (fvs, o)) :
    fvs.length = n ∧
    (∀ (k : Nat) (x : Expr), fvs[k]? = some x → ∃ ty, x = Expr.fvar (d + k) ty) ∧
    (∀ a ∈ fvs, a.looseBVarsBounded 0 = true) :=
  ⟨openPisAtFvars_length n hop, openPisAtFvars_index n e d hop, fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, rfl⟩ := openPisAtFvars_index n e d hop q a hq
    rfl⟩

/-! ## The three special entries -/

/-- The field variables' spine at the minor's core. -/
@[expose] def fieldBvars (nF : Nat) : List AnnotTerm :=
  (List.range nF).map fun k => AnnotTerm.bvar (nF - 1 - k)

/-! ## The constructor telescope's residual -/

/-- The constructor's field telescope at the parameter variables: its
reading at depth `nP`, its scoping, and its strip. -/
theorem ctorResidual {m : EnvModel V env} {ψ : Name → Nat} {nP nF : Nat} {cty : Expr}
    (hCf : cty.hasFvar = false)
    {ds : List (Nat × Nat × AnnotTerm)} {bodyC : AnnotTerm}
    (hCread : denoteMeta m.acval env ψ 0 cty = some (mkPisAV ds bodyC))
    (hlenD : ds.length = nP + nF)
    {cbs : List (Expr × BinderMeta)} {crest0 : Expr}
    (hsC : cty.stripPis nP = some (cbs, crest0))
    (hstripC : (cty.stripPis (nP + nF)).isSome = true)
    {tfvs : List Expr} (hlenT : tfvs.length = nP)
    (hidxT : ∀ (k : Nat) (x : Expr), tfvs[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (hspW : ∀ (i : Nat) (a : Expr), tfvs[i]? = some a → Expr.WScoped (0 + i + 1) a) :
    denoteMeta m.acval env ψ nP (Expr.instSeq tfvs (nP - 1) crest0)
        = some (mkPisAV (ds.drop nP) bodyC) ∧
      Expr.WScoped nP (Expr.instSeq tfvs (nP - 1) crest0) ∧
      ((Expr.instSeq tfvs (nP - 1) crest0).stripPis nF).isSome = true := by
  obtain ⟨cdoms, hci⟩ := ConLeche.instPisAt_of_stripPis tfvs (by rw [hlenT]; exact hsC)
  rw [hlenT] at hci
  have hidxT' : ∀ (q : Nat) (x : Expr), tfvs[q]? = some x → ∃ t, x = Expr.fvar (0 + q) t :=
    fun q x hx => by
      obtain ⟨t, h⟩ := hidxT q x hx
      exact ⟨t, by rw [h, Nat.zero_add]⟩
  have hteleP := piTeleAV_of_stripPisAV (stripPisAV_mkPisAV_take nP ds bodyC (by omega))
  refine ⟨?_, ?_, ?_⟩
  · have := instPisAt_openerRes tfvs hci hidxT' hCread (by rw [hlenT]; exact hteleP)
    rwa [hlenT, Nat.zero_add] at this
  · have := instPisAt_res_WScoped tfvs (d := 0) hci (Expr.WScoped.of_not_hasFvar hCf) hspW
    rwa [hlenT, Nat.zero_add] at this
  · exact instSeq_stripPis_isSome tfvs (nP - 1) (stripPis_isSome_drop nP hstripC hsC)

/-- The reading of the constructor's residual, one under (the motive):
the field data lifted once. -/
theorem ctorResidual_read_lift {m : EnvModel V env} {ψ : Name → Nat} {nP nF : Nat}
    {crest : Expr} {ds : List (Nat × Nat × AnnotTerm)} {bodyC : AnnotTerm}
    (hread : denoteMeta m.acval env ψ nP crest = some (mkPisAV (ds.drop nP) bodyC))
    (hw : Expr.WScoped nP crest) (hlenD : ds.length = nP + nF) (e : Nat) :
    denoteMeta m.acval env ψ (nP + e) crest
      = some (mkPisAV (liftDoms e 0 (ds.drop nP)) (bodyC.liftN e nF)) := by
  rw [denoteMeta_lift m.acval_closed hw (nP + e) (by omega), hread, Option.map_some,
    show nP + e - nP = e from by omega, liftN_mkPisAV, Nat.zero_add]
  congr 3
  simp [hlenD]

/-! ## The generated type -/

/-! ## The generated rule -/

theorem mkLamsAV_append :
    ∀ (l₁ l₂ : List (Nat × AnnotTerm)) (b : AnnotTerm),
      mkLamsAV (l₁ ++ l₂) b = mkLamsAV l₁ (mkLamsAV l₂ b)
  | [], _, _ => rfl
  | d :: l₁, l₂, b => by simp [mkLamsAV, mkLamsAV_append l₁ l₂ b]

theorem rebit_map_lam (b : Nat) (ds : List (Nat × Nat × AnnotTerm)) :
    (rebit b ds).map (fun d : Nat × Nat × AnnotTerm => (d.2.1, d.2.2))
      = ds.map fun d => (b, d.2.2) := by
  simp [rebit, List.map_map, Function.comp_def]

/-! ## The recursor's data, from the stage -/

end ConLeche.Model
