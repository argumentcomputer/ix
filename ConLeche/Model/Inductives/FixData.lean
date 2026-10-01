module

public import ConLeche.Model.Inductives.SumData
import ConLeche.Model.Inductives.StructBodyFrames
public import ConLeche.Verify.Inductives.FixWF
public section

/-!
# The recursive constructor's data (task #188)

A recursive constructor's data at a carrier storing the former: the
sum's data (`CtorDataI`, the readings of the constructor's telescope)
together with what the recursive route's field-kinds guard pins on the
OPENED annotated type (`nativeOpenedOk`, read positionally:
`FixOpened`), and the readings it yields — every field's opened domain
reads to its entry (`domRead`); a recursive field's domain is the
family at the parameter variables and index expressions whose
readings `Eis` are read at the field's own depth (`eisRead`), the entry
being the former's leaf at the parameter variables and those readings
(`recEntry`); an ordinary field's domain resolves before the block, so
its reading is the same at every carrier storing the former; a
recursive field's variable is a leaf of no later domain nor of the
residual, so the later entries and the residual's index readings are
lifts over its slot.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The opened-form guard, positionally -/

/-- `nativeOpenedOk`, read positionally. -/
structure FixOpened (env₀ : Env) (T : Name) (lps : List Name) (nP nIdx nF : Nat)
    (ks : List RecFieldKind) (fvsP xFvs : List Expr) (xrest : Expr) : Prop where
  residRes : ∀ e ∈ xrest.getAppArgs.drop nP, e.constsResolve env₀ = true
  ord : ∀ i x, xFvs[i]? = some x → ks.getD i .ordinary = .ordinary →
    x.fvarTypeD.constsResolve env₀ = true
  recF : ∀ i x, xFvs[i]? = some x → ks.getD i .ordinary = .recursive →
    x.fvarTypeD.getAppFn = Expr.const T (lps.map .param) ∧
    x.fvarTypeD.getAppArgs.take nP = fvsP ∧
    x.fvarTypeD.getAppArgs.length = nP + nIdx ∧
    (∀ e ∈ x.fvarTypeD.getAppArgs.drop nP, e.constsResolve env₀ = true) ∧
    (∀ y ∈ xFvs.drop (i + 1), y.fvarTypeD.mentionsFvar (nP + i) = false) ∧
    xrest.mentionsFvar (nP + i) = false
  /-- a REFLEXIVE field (task #202): its own telescope opened at
  variables at the field's depth, the domains resolving before the
  block, the body the family at the parameter variables and index
  expressions resolving before the block; the variable a leaf of no
  later domain nor of the residual -/
  reflF : ∀ i x, xFvs[i]? = some x → ks.getD i .ordinary = .reflexive →
    ∃ afvs body,
      openPisAtFvars (x.fvarTypeD.piBinders).1.length x.fvarTypeD (nP + i) = some (afvs, body) ∧
      afvs.length ≠ 0 ∧
      (∀ a ∈ afvs, a.fvarTypeD.constsResolve env₀ = true) ∧
      body.getAppFn = Expr.const T (lps.map .param) ∧
      body.getAppArgs.take nP = fvsP ∧
      body.getAppArgs.length = nP + nIdx ∧
      (∀ e ∈ body.getAppArgs.drop nP, e.constsResolve env₀ = true) ∧
      (∀ y ∈ xFvs.drop (i + 1), y.fvarTypeD.mentionsFvar (nP + i) = false) ∧
      xrest.mentionsFvar (nP + i) = false
  kinds : ∀ i, i < nF → ks.getD i .ordinary = .ordinary ∨ ks.getD i .ordinary = .recursive ∨
    ks.getD i .ordinary = .reflexive

theorem fixOpened_of {env₀ : Env} {T : Name} {lps : List Name} {nP nIdx : Nat} {cty : Expr}
    {nF : Nat} {ks : List RecFieldKind}
    (h : ConLeche.nativeOpenedOk env₀ T lps nP nIdx cty nF ks = true) :
    ∃ (fvsP : List Expr) (crest : Expr) (xFvs : List Expr) (xrest : Expr),
      openPisAtFvars nP cty 0 = some (fvsP, crest) ∧
      openPisAtFvars nF crest nP = some (xFvs, xrest) ∧
      FixOpened env₀ T lps nP nIdx nF ks fvsP xFvs xrest := by
  unfold ConLeche.nativeOpenedOk at h
  split at h
  · next fvsP crest hop =>
    split at h
    · next xFvs xrest hox =>
      simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
      obtain ⟨hres, hall⟩ := h
      have hlenX : xFvs.length = nF := openPisAtFvars_length _ hox
      refine ⟨fvsP, crest, xFvs, xrest, hop, hox, ⟨hres, ?_, ?_, ?_, ?_⟩⟩
      · intro i x hx hk
        have hi : i < nF := by
          rw [← hlenX]; exact (List.getElem?_eq_some_iff.mp hx).1
        have := hall i hi
        rw [hx, hk] at this
        exact this
      · intro i x hx hk
        have hi : i < nF := by
          rw [← hlenX]; exact (List.getElem?_eq_some_iff.mp hx).1
        have := hall i hi
        rw [hx, hk] at this
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.not_eq_eq_eq_not,
          Bool.not_true, List.any_eq_false] at this
        obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := this
        exact ⟨h1, h2, h3, h4, fun y hy => by simpa using h5 y hy, h6⟩
      · intro i x hx hk
        have hi : i < nF := by
          rw [← hlenX]; exact (List.getElem?_eq_some_iff.mp hx).1
        have := hall i hi
        rw [hx, hk] at this
        dsimp only at this
        cases hopA : openPisAtFvars (x.fvarTypeD.piBinders).1.length x.fvarTypeD (nP + i) with
        | none => rw [hopA] at this; exact nomatch this
        | some q =>
          obtain ⟨afvs, body⟩ := q
          rw [hopA] at this
          simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.not_eq_eq_eq_not,
            Bool.not_true, List.any_eq_false, bne_iff_ne, ne_eq] at this
          obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := this
          exact ⟨afvs, body, rfl, h1, h2, h3, h4, h5, h6, fun y hy => by simpa using h7 y hy, h8⟩
      · intro i hi
        have := hall i hi
        cases hx : xFvs[i]? with
        | none => rw [hx] at this; exact nomatch this
        | some x =>
          rw [hx] at this
          cases hk : ks.getD i .ordinary with
          | ordinary => exact Or.inl rfl
          | recursive => exact Or.inr (Or.inl rfl)
          | reflexive => exact Or.inr (Or.inr rfl)
          | negative => rw [hk] at this; exact nomatch this
          | unsupported => rw [hk] at this; exact nomatch this
    · exact nomatch h
  · exact nomatch h

/-! ## The constructor's data -/

/-- The leading Π-entries of a Π-telescope's reading carry the reading's
bits: domain bit `0`, codomain bit a `pwBit` (so at most `1`). -/
theorem stripPisAV_denoteMeta_bits {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} :
    ∀ (n : Nat) {d : Nat} {e : Expr} {fvs : List Expr} {o : Expr} {ea : AnnotTerm}
      {pps : List (Nat × Nat × AnnotTerm)} {b : AnnotTerm},
      openPisAtFvars n e d = some (fvs, o) → denoteMeta acval env φ d e = some ea →
      stripPisAV n ea = some (pps, b) → ∀ p ∈ pps, p.1 = 0 ∧ p.2.1 ≤ 1
  | 0, _, _, _, _, _, _, _, _, _, hst => by
    simp only [stripPisAV, Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, -⟩ := hst
    exact fun _ h => nomatch h
  | n + 1, d, e, fvs, o, ea, pps, b, hop, hr, hst => by
    match e, hop with
    | .forallE ty bd mb, hop =>
      obtain ⟨ta, ba, -, hba, rfl⟩ := denoteMeta_forallE_inv hr
      simp only [openPisAtFvars] at hop
      split at hop
      · next fvs' o' hop' =>
        simp only [stripPisAV] at hst
        cases hst' : stripPisAV n ba with
        | none => rw [hst'] at hst; exact nomatch hst
        | some q =>
          rw [hst'] at hst
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hst
          obtain ⟨rfl, -⟩ := hst
          intro p hp
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · refine ⟨rfl, ?_⟩
            show pwBit φ mb.pw ≤ 1
            unfold pwBit; split <;> omega
          · exact stripPisAV_denoteMeta_bits n hop' hba hst' p hp
      · exact nomatch hop
    | .bvar _, hop => nomatch hop
    | .fvar _ _, hop => nomatch hop
    | .sort _, hop => nomatch hop
    | .const _ _, hop => nomatch hop
    | .app _ _, hop => nomatch hop
    | .lam _ _ _, hop => nomatch hop
    | .letE _ _ _, hop => nomatch hop
    | .proj _ _ _, hop => nomatch hop
    | .lit _, hop => nomatch hop

/-- **A recursive constructor's data** at a carrier storing the former
(see the module docstring). -/
structure FixCtorDataI {env : Env} (m : EnvModel V env) (env₀ : Env) (T : Name)
    (lps : List Name) (cvC : ConstantVal) (nP nF nIdx : Nat) (resSort : Level)
    (isProp large : Bool) (idxArgs : List Expr)
    (ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)) (Es : (Name → Nat) → List AnnotTerm)
    (srcs : List (Option Nat)) (ks : List RecFieldKind) (fvsP xFvs : List Expr) (xrest : Expr)
    (Eiss : (Name → Nat) → List (List AnnotTerm))
    (tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))) : Prop
    extends CtorDataI m T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs where
  opened : FixOpened env₀ T lps nP nIdx nF ks fvsP xFvs xrest
  opens : ∃ crest, openPisAtFvars nP cvC.type 0 = some (fvsP, crest) ∧
    openPisAtFvars nF crest nP = some (xFvs, xrest)
  ksLen : ks.length = nF
  xLen : xFvs.length = nF
  pLen : fvsP.length = nP
  xIdx : ∀ k x, xFvs[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty
  pIdx : ∀ k x, fvsP[k]? = some x → ∃ ty, x = Expr.fvar k ty
  idxEq : idxArgs = xrest.getAppArgs.drop nP
  domRead : ∀ ψ i x, xFvs[i]? = some x →
    denoteMeta m.acval env ψ (nP + i) x.fvarTypeD = some ((ds ψ).getD (nP + i) default).2.2
  eissLen : ∀ ψ, (Eiss ψ).length = nF
  eisRead : ∀ ψ i x, xFvs[i]? = some x → ks.getD i .ordinary = .recursive →
    DenoteMetaSpine m.acval env ψ (nP + i) (x.fvarTypeD.getAppArgs.drop nP) ((Eiss ψ).getD i [])
  eisLen : ∀ ψ i, ks.getD i .ordinary = .recursive → i < nF → ((Eiss ψ).getD i []).length = nIdx
  recEntry : ∀ ψ i, ks.getD i .ordinary = .recursive → i < nF →
    ((ds ψ).getD (nP + i) default).2.2
      = AnnotTerm.mkAppN (m.acval T ψ) (paramBvarsAt nP (nP + i) ++ (Eiss ψ).getD i [])
  eissParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvC.levelParams, ψ₁ q = ψ₂ q) → Eiss ψ₁ = Eiss ψ₂
  /-- an index expression is read under the field's telescope (empty at
  a finitary field) -/
  eissBelow : ∀ ψ i, ∀ E ∈ (Eiss ψ).getD i [],
    Term.bvarsBelow (nP + i + ((tss ψ).getD i []).length) E.erase
  ordNone : ∀ ψ i, ks.getD i .ordinary ≠ .recursive → ks.getD i .ordinary ≠ .reflexive →
    (Eiss ψ).getD i [] = []
  /-- the reflexive fields' telescopes (task #202): one list per field,
  empty at a non-reflexive one -/
  tssLen : ∀ ψ, (tss ψ).length = nF
  tssNone : ∀ ψ i, ks.getD i .ordinary ≠ .reflexive → (tss ψ).getD i [] = []
  /-- the telescope's codomain bits are at the family's regime -/
  tssBits : ∀ ψ i, ∀ d ∈ (tss ψ).getD i [], (d.2.1 = 0 ↔ resSort.eval ψ = 0)
  /-- the telescope entries are readings' Π-entries: domain bit `0`,
  codomain bit at most `1` -/
  tssPiBits : ∀ ψ i, ∀ d ∈ (tss ψ).getD i [], d.1 = 0 ∧ d.2.1 ≤ 1
  tssBelow : ∀ ψ i, DomsBelow (nP + i) ((tss ψ).getD i [])
  tssParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvC.levelParams, ψ₁ q = ψ₂ q) → tss ψ₁ = tss ψ₂
  /-- a reflexive field's telescope, opened at the field's depth: its
  domains read to the telescope's entries, its body's index
  expressions read to the field's readings under the telescope -/
  reflOpen : ∀ ψ i x, xFvs[i]? = some x → ks.getD i .ordinary = .reflexive →
    ∃ afvs body,
      openPisAtFvars ((tss ψ).getD i []).length x.fvarTypeD (nP + i) = some (afvs, body) ∧
      ((tss ψ).getD i []).length = (x.fvarTypeD.piBinders).1.length ∧
      (∀ k a, afvs[k]? = some a →
        denoteMeta m.acval env ψ (nP + i + k) a.fvarTypeD
          = some (((tss ψ).getD i []).getD k default).2.2) ∧
      DenoteMetaSpine m.acval env ψ (nP + i + ((tss ψ).getD i []).length)
        (body.getAppArgs.drop nP) ((Eiss ψ).getD i [])
  eisLenRefl : ∀ ψ i, ks.getD i .ordinary = .reflexive → i < nF → ((Eiss ψ).getD i []).length = nIdx
  /-- a reflexive field's entry: the Π-tower over its telescope of the
  former's leaf at the parameter variables (under the telescope) and
  the readings -/
  reflEntry : ∀ ψ i, ks.getD i .ordinary = .reflexive → i < nF →
    ((ds ψ).getD (nP + i) default).2.2
      = mkPisAV ((tss ψ).getD i [])
          (AnnotTerm.mkAppN (m.acval T ψ)
            (paramBvarsAt nP (nP + i + ((tss ψ).getD i []).length) ++ (Eiss ψ).getD i []))

end ConLeche.Model

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w'

variable {V : Type w'} [SetTheory V] {μ : CheckMode} {env : Env}

/-- The parameter variables read to the parameter spine at depth `D`. -/
theorem denoteMetaSpine_params {acval : Name → (Name → Nat) → AnnotTerm} {φ : Name → Nat}
    (D : Nat) {fvsP : List Expr} {nP : Nat} (hlen : fvsP.length = nP)
    (hidx : ∀ k x, fvsP[k]? = some x → ∃ ty, x = Expr.fvar k ty) :
    DenoteMetaSpine acval env φ D fvsP (paramBvarsAt nP D) := by
  have := denoteMetaSpine_fvars (acval := acval) (env := env) (φ := φ) D fvsP 0
    (fun k x hx => by
      obtain ⟨ty, h⟩ := hidx k x hx
      exact ⟨ty, by rw [h, Nat.zero_add]⟩)
  rw [hlen] at this
  have he : ((List.range nP).map fun k => AnnotTerm.bvar (D - 1 - (0 + k))) = paramBvarsAt nP D := by
    unfold paramBvarsAt
    apply List.map_congr_left
    intro k _
    rw [Nat.zero_add]
  rwa [he] at this

/-- The Π-tower's closedness, inverted: the domains under the earlier
ones, the body under all. -/
theorem bvarsBelow_mkPisAV_inv {k : Nat} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {b : AnnotTerm}, Term.bvarsBelow k (mkPisAV ds b).erase →
      DomsBelow k ds ∧ Term.bvarsBelow (k + ds.length) b.erase
  | [], _, h => ⟨trivial, by simpa [mkPisAV] using h⟩
  | d :: ds, b, h => by
    simp only [mkPisAV, AnnotTerm.erase_pi] at h
    obtain ⟨hd, hb⟩ := h
    obtain ⟨h1, h2⟩ := bvarsBelow_mkPisAV_inv (k := k + 1) (ds := ds) hb
    exact ⟨⟨hd, h1⟩, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h2⟩

/-- **The recursive constructor's data**, from its stage run at the
environment holding the former and the opened-form guard. -/
theorem fixCtorData_of (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {T : Name} {lps : List Name} {nP nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {cvC cvTa cvCa : ConstantVal} {env₀ env₁ : Env} {caps : IndCaps}
    {bs : List (Expr × BinderMeta)} {ks : List RecFieldKind}
    {sorts : List Level}
    (hCtor : ConLeche.checkSumCtor (ConLeche.fueledOps μ F) env₁ env T lps nP nIdx resSort
      isProp large cvC nF cvTa = .ok (cvCa, sorts))
    (hfT : env.find? T = some (.indInfo cvTa caps))
    (hlpsT : cvTa.levelParams = lps)
    (hstripT : cvTa.type.stripPis (nP + nIdx) = some (bs, .sort resSort))
    (hks : ks.length = nF)
    (hopened : ConLeche.nativeOpenedOk env₀ T lps nP nIdx cvCa.type nF ks = true) :
    ∃ (idxArgs : List Expr) (ds : (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (Es : (Name → Nat) → List AnnotTerm) (srcs : List (Option Nat))
      (fvsP xFvs : List Expr) (xrest : Expr) (Eiss : (Name → Nat) → List (List AnnotTerm))
      (tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))),
      FixCtorDataI mp.base2 env₀ T lps cvCa nP nF nIdx resSort isProp large idxArgs ds Es srcs
        ks fvsP xFvs xrest Eiss tss := by
  obtain ⟨idxArgs, ds, Es, srcs, -, ⟨fvsP, crest, xFvs, xrest, hopP, hopX, hidxEq⟩, hCD⟩ :=
    sumCtorData_of hμ mp hCtor hfT hlpsT hstripT
  obtain ⟨fvsP', crest', xFvs', xrest', hopP', hopX', hO⟩ := fixOpened_of hopened
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hopP.symm.trans hopP'))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hopX.symm.trans hopX'))
  obtain ⟨hcf, -, -, hcb⟩ := ConLeche.direct_sum_ctor_typeWF hCtor
  obtain ⟨hlenP, hidxP, -⟩ := opening_vars_at hopP
  obtain ⟨hlenX, hidxX, -⟩ := opening_vars_at hopX
  -- the fields' sort rows (task #202: the reflexive telescopes' bits)
  obtain ⟨-, -, fvsP₂, crest₂, tfvs, trest, xFvs₂, idxArgs₂, hopC, -, -, hopX₂, -, -, -, hsorts⟩ :=
    ConLeche.checkSumCtor_shape hCtor
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hopP.symm.trans hopC))
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj (hopX.symm.trans hopX₂))
  obtain ⟨-, hrows⟩ := ConLeche.checkStructFieldSortsI_inv hsorts
  have hidxX' : ∀ k x, xFvs[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty := hidxX
  have hidxP' : ∀ k x, fvsP[k]? = some x → ∃ ty, x = Expr.fvar k ty := fun k x hx => by
    obtain ⟨ty, h⟩ := hidxP k x hx
    exact ⟨ty, by rw [h, Nat.zero_add]⟩
  have hopAll : openPisAtFvars (nP + nF) cvCa.type 0 = some (fvsP ++ xFvs, xrest) :=
    openPisAtFvars_add nP hopP (by rw [Nat.zero_add]; exact hopX)
  -- every field's opened domain reads to its entry
  have hdomRead : ∀ ψ i x, xFvs[i]? = some x →
      denoteMeta mp.base2.acval env ψ (nP + i) x.fvarTypeD
        = some ((ds ψ).getD (nP + i) default).2.2 := by
    intro ψ i x hx
    have hO := opened_of_peel hopAll hcf hcb (hCD.read ψ) (hCD.len ψ) (hCD.okTy ψ)
    have hxA : (fvsP ++ xFvs)[nP + i]? = some x := by
      rw [List.getElem?_append_right (by omega), hlenP, Nat.add_sub_cancel_left]
      exact hx
    have hi : i < nF := by rw [← hlenX]; exact (List.getElem?_eq_some_iff.mp hx).1
    have hd := hO.doms (nP + i) x hxA
    have hget : (ds ψ)[nP + i]? = some ((ds ψ).getD (nP + i) default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hCD.len ψ]; omega)]
      rfl
    rw [getD_reverse_of_peel (hCD.len ψ) (by omega) hget] at hd
    exact hd
  -- the entries' closedness
  have hentryBelow : ∀ ψ i, i < nF → Term.bvarsBelow (nP + i) ((ds ψ).getD (nP + i) default).2.2.erase := by
    intro ψ i hi
    have hb := DomsBelow.getD_below (nP + i) (hCD.below ψ) (by rw [hCD.len ψ]; omega)
    rwa [Nat.zero_add] at hb
  -- the former at the parameter variables followed by the index expressions
  have hfamRead : ∀ ψ (d : Nat) (body : Expr), body.getAppFn = Expr.const T (lps.map .param) →
      body.getAppArgs.take nP = fvsP → body.getAppArgs.length = nP + nIdx →
      ∀ R, denoteMeta mp.base2.acval env ψ d body = some R →
      ∃ Eis : List AnnotTerm, Eis.length = nIdx ∧
        DenoteMetaSpine mp.base2.acval env ψ d (body.getAppArgs.drop nP) Eis ∧
        R = AnnotTerm.mkAppN (mp.base2.acval T ψ) (paramBvarsAt nP d ++ Eis) := by
    intro ψ d body hfn htake hlenA R hread
    have hshape : body
        = Expr.mkAppN (.const T (lps.map .param)) (fvsP ++ body.getAppArgs.drop nP) := by
      conv => lhs; rw [← Expr.mkAppN_getApp body]
      rw [hfn, ← htake, List.take_append_drop]
    rw [hshape] at hread
    obtain ⟨fa, vs, hfa, hsp, hea⟩ := denoteMeta_mkAppN_inv hread
    have hlpsT' : (ConstantInfo.indInfo cvTa caps).toConstantVal.levelParams = lps := by
      simpa [ConstantInfo.toConstantVal] using hlpsT
    have hfa' : fa = mp.base2.acval T ψ := by
      rw [denoteMeta_const hfT (by rw [hlpsT']; simp), hlpsT', Level.substFn_param_self] at hfa
      exact (Option.some.inj hfa).symm
    obtain ⟨vs₁, vs₂, rfl, hsp₁, hsp₂⟩ := DenoteMetaSpine.append_inv hsp
    have hvs₁ : vs₁ = paramBvarsAt nP d :=
      DenoteMetaSpine.unique hsp₁ (denoteMetaSpine_params d hlenP hidxP')
    refine ⟨vs₂, ?_, hsp₂, ?_⟩
    · rw [← hsp₂.length, List.length_drop, hlenA]; omega
    · rw [hea, hfa', hvs₁]
  -- a recursive field's index readings
  have hex : ∀ (ψ : Name → Nat) (i : Nat), ks.getD i .ordinary = .recursive → i < nF →
      ∃ Eis : List AnnotTerm, Eis.length = nIdx ∧
        (∀ x, xFvs[i]? = some x →
          DenoteMetaSpine mp.base2.acval env ψ (nP + i) (x.fvarTypeD.getAppArgs.drop nP) Eis) ∧
        ((ds ψ).getD (nP + i) default).2.2
          = AnnotTerm.mkAppN (mp.base2.acval T ψ) (paramBvarsAt nP (nP + i) ++ Eis) := by
    intro ψ i hk hi
    have hil : i < xFvs.length := by omega
    obtain ⟨x, hx⟩ : ∃ x, xFvs[i]? = some x := ⟨_, List.getElem?_eq_getElem hil⟩
    obtain ⟨hfn, htake, hlenA, -, -, -⟩ := hO.recF i x hx hk
    obtain ⟨Eis, hlen, hsp, heq⟩ := hfamRead ψ (nP + i) x.fvarTypeD hfn htake hlenA _ (hdomRead ψ i x hx)
    refine ⟨Eis, hlen, fun x' hx' => ?_, heq⟩
    obtain rfl := Option.some.inj (hx.symm.trans hx')
    exact hsp
  -- a reflexive field's telescope and index readings (task #202)
  have hexR : ∀ (ψ : Name → Nat) (i : Nat), ks.getD i .ordinary = .reflexive → i < nF →
      ∃ (tl : List (Nat × Nat × AnnotTerm)) (Eis : List AnnotTerm),
        Eis.length = nIdx ∧
        (∀ x, xFvs[i]? = some x → tl.length = (x.fvarTypeD.piBinders).1.length) ∧
        (∀ x, xFvs[i]? = some x → ∃ afvs body,
          openPisAtFvars tl.length x.fvarTypeD (nP + i) = some (afvs, body) ∧
          (∀ k a, afvs[k]? = some a →
            denoteMeta mp.base2.acval env ψ (nP + i + k) a.fvarTypeD = some (tl.getD k default).2.2) ∧
          DenoteMetaSpine mp.base2.acval env ψ (nP + i + tl.length) (body.getAppArgs.drop nP) Eis) ∧
        ((ds ψ).getD (nP + i) default).2.2
          = mkPisAV tl (AnnotTerm.mkAppN (mp.base2.acval T ψ) (paramBvarsAt nP (nP + i + tl.length) ++ Eis)) ∧
        (∀ d ∈ tl, (d.2.1 = 0 ↔ resSort.eval ψ = 0)) ∧
        (∀ d ∈ tl, d.1 = 0 ∧ d.2.1 ≤ 1) := by
    intro ψ i hk hi
    have hil : i < xFvs.length := by omega
    obtain ⟨x, hx⟩ : ∃ x, xFvs[i]? = some x := ⟨_, List.getElem?_eq_getElem hil⟩
    obtain ⟨afvs, body, hopA, -, -, hfn, htake, hlenA, -, -, -⟩ := hO.reflF i x hx hk
    have hm : afvs.length = (x.fvarTypeD.piBinders).1.length := openPisAtFvars_length _ hopA
    obtain ⟨tl, R, hst, hbody, hlenT, hdoms⟩ := denoteMeta_openPis _ hopA (hdomRead ψ i x hx)
    obtain ⟨Eis, hlen, hsp, hR⟩ := hfamRead ψ _ body hfn htake hlenA R hbody
    obtain ⟨hentry, -⟩ := stripPisAV_eq_mkPis hst
    -- the telescope's bits: the field's sort row, walked through the binders
    obtain ⟨fv, ty, u, hfv, -, hinf, hens, -, -⟩ := hrows i hi
    obtain rfl := Option.some.inj (hx.symm.trans hfv)
    obtain ⟨F', tb, vb, hib, hensb, -, hbits⟩ := piBits_of_infer hμ _ hopA hinf hens
    have hshape : body
        = Expr.mkAppN (.const T (lps.map .param)) (fvsP ++ body.getAppArgs.drop nP) := by
      conv => lhs; rw [← Expr.mkAppN_getApp body]
      rw [hfn, ← htake, List.take_append_drop]
    rw [hshape] at hib
    obtain ⟨tf, htf⟩ := inferTypeCore_mkAppN_fn_inv (fvsP ++ body.getAppArgs.drop nP) hib
    obtain ⟨ci, hfci, -, rfl⟩ := ConLeche.inferTypeCore_const_inv htf
    obtain rfl : ci = .indInfo cvTa caps := Option.some.inj (hfci.symm.trans hfT)
    have htfT : ConLeche.inferTypeCore μ env F' (nP + i + (x.fvarTypeD.piBinders).1.length)
        (.const T (lps.map .param)) = .ok cvTa.type := by
      have := htf
      rw [show (ConstantInfo.indInfo cvTa caps).toConstantVal = cvTa from rfl,
        hlpsT, Expr.instantiateLevelParams_self] at this
      exact this
    obtain rfl := inferTypeCore_mkAppN_sort (fvsP ++ body.getAppArgs.drop nP) htfT
      (by rw [List.length_append, hlenP, List.length_drop, hlenA, Nat.add_sub_cancel_left]; exact hstripT) hib
    have hvb := ensureSortCore_sort_eq hensb
    rw [hvb] at hbits
    refine ⟨tl, Eis, hlen, fun x' hx' => ?_, fun x' hx' => ?_, by rw [hentry, hR, hlenT], ?_,
      stripPisAV_denoteMeta_bits _ hopA (hdomRead ψ i x hx) hst⟩
    · obtain rfl := Option.some.inj (hx.symm.trans hx')
      exact hlenT
    · obtain rfl := Option.some.inj (hx.symm.trans hx')
      refine ⟨afvs, body, by rw [hlenT]; exact hopA, fun k a hka => ?_, by rw [hlenT]; exact hsp⟩
      obtain ⟨p, hp, -, hread⟩ := hdoms k a hka
      rw [List.getD_eq_getElem?_getD, hp]
      exact hread
    · intro d hd
      exact stripPisAV_bits _ (hbits ψ) (hdomRead ψ i x hx) hst d hd
  -- the readings, chosen
  let Eis : (Name → Nat) → Nat → List AnnotTerm := fun ψ i =>
    if h : ks.getD i .ordinary = .recursive ∧ i < nF then Classical.choose (hex ψ i h.1 h.2)
    else if h' : ks.getD i .ordinary = .reflexive ∧ i < nF then
      Classical.choose (Classical.choose_spec (hexR ψ i h'.1 h'.2))
    else []
  let Tl : (Name → Nat) → Nat → List (Nat × Nat × AnnotTerm) := fun ψ i =>
    if h' : ks.getD i .ordinary = .reflexive ∧ i < nF then Classical.choose (hexR ψ i h'.1 h'.2)
    else []
  have hnotboth : ∀ i, ks.getD i .ordinary = .recursive → ¬ ks.getD i .ordinary = .reflexive := by
    intro i h1 h2; rw [h1] at h2; exact nomatch h2
  have hEis : ∀ ψ i (h : ks.getD i .ordinary = .recursive ∧ i < nF),
      (Eis ψ i).length = nIdx ∧
      (∀ x, xFvs[i]? = some x →
        DenoteMetaSpine mp.base2.acval env ψ (nP + i) (x.fvarTypeD.getAppArgs.drop nP) (Eis ψ i)) ∧
      ((ds ψ).getD (nP + i) default).2.2
        = AnnotTerm.mkAppN (mp.base2.acval T ψ) (paramBvarsAt nP (nP + i) ++ Eis ψ i) := by
    intro ψ i h
    simp only [Eis, dif_pos h]
    exact Classical.choose_spec (hex ψ i h.1 h.2)
  have hEisR : ∀ ψ i (h : ks.getD i .ordinary = .reflexive ∧ i < nF),
      (Eis ψ i).length = nIdx ∧
      (∀ x, xFvs[i]? = some x → (Tl ψ i).length = (x.fvarTypeD.piBinders).1.length) ∧
      (∀ x, xFvs[i]? = some x → ∃ afvs body,
        openPisAtFvars (Tl ψ i).length x.fvarTypeD (nP + i) = some (afvs, body) ∧
        (∀ k a, afvs[k]? = some a →
          denoteMeta mp.base2.acval env ψ (nP + i + k) a.fvarTypeD = some ((Tl ψ i).getD k default).2.2) ∧
        DenoteMetaSpine mp.base2.acval env ψ (nP + i + (Tl ψ i).length) (body.getAppArgs.drop nP) (Eis ψ i)) ∧
      ((ds ψ).getD (nP + i) default).2.2
        = mkPisAV (Tl ψ i) (AnnotTerm.mkAppN (mp.base2.acval T ψ) (paramBvarsAt nP (nP + i + (Tl ψ i).length) ++ Eis ψ i)) ∧
      (∀ d ∈ Tl ψ i, (d.2.1 = 0 ↔ resSort.eval ψ = 0)) ∧
      (∀ d ∈ Tl ψ i, d.1 = 0 ∧ d.2.1 ≤ 1) := by
    intro ψ i h
    have hnr : ¬ (ks.getD i .ordinary = .recursive ∧ i < nF) := fun hh => hnotboth i hh.1 h.1
    simp only [Eis, Tl, dif_neg hnr, dif_pos h]
    exact Classical.choose_spec (Classical.choose_spec (hexR ψ i h.1 h.2))
  have hEisNone : ∀ ψ i, ks.getD i .ordinary ≠ .recursive → ks.getD i .ordinary ≠ .reflexive →
      Eis ψ i = [] := by
    intro ψ i h h'
    simp only [Eis]
    rw [dif_neg (fun hh => h hh.1), dif_neg (fun hh => h' hh.1)]
  have hTlNone : ∀ ψ i, ks.getD i .ordinary ≠ .reflexive → Tl ψ i = [] := by
    intro ψ i h
    simp only [Tl]
    rw [dif_neg (fun hh => h hh.1)]
  let Eiss : (Name → Nat) → List (List AnnotTerm) := fun ψ => (List.range nF).map (Eis ψ)
  let Tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm)) := fun ψ => (List.range nF).map (Tl ψ)
  have hEissGet : ∀ ψ i, i < nF → (Eiss ψ).getD i [] = Eis ψ i := by
    intro ψ i hi
    simp only [Eiss, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some]
  have hEissGet' : ∀ ψ i, (Eiss ψ).getD i [] = if i < nF then Eis ψ i else [] := by
    intro ψ i
    split
    · next hi => exact hEissGet ψ i hi
    · next hi =>
      simp only [Eiss, List.getD_eq_getElem?_getD, List.getElem?_map]
      rw [List.getElem?_eq_none (by simp; omega)]
      rfl
  have hTssGet : ∀ ψ i, i < nF → (Tss ψ).getD i [] = Tl ψ i := by
    intro ψ i hi
    simp only [Tss, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some]
  have hTssGet' : ∀ ψ i, (Tss ψ).getD i [] = if i < nF then Tl ψ i else [] := by
    intro ψ i
    split
    · next hi => exact hTssGet ψ i hi
    · next hi =>
      simp only [Tss, List.getD_eq_getElem?_getD, List.getElem?_map]
      rw [List.getElem?_eq_none (by simp; omega)]
      rfl
  -- the entries of a reflexive field, closed
  have hreflBelow : ∀ ψ i (h : ks.getD i .ordinary = .reflexive ∧ i < nF),
      DomsBelow (nP + i) (Tl ψ i) ∧
      ∀ E ∈ Eis ψ i, Term.bvarsBelow (nP + i + (Tl ψ i).length) E.erase := by
    intro ψ i h
    have hb := hentryBelow ψ i h.2
    rw [(hEisR ψ i h).2.2.2.1] at hb
    obtain ⟨h1, h2⟩ := bvarsBelow_mkPisAV_inv hb
    rw [AnnotTerm.erase_mkAppN] at h2
    obtain ⟨-, hall⟩ := bvarsBelow_mkAppN_inv h2
    exact ⟨h1, fun E hE => hall E.erase (List.mem_map.mpr ⟨E, List.mem_append_right _ hE, rfl⟩)⟩
  refine ⟨idxArgs, ds, Es, srcs, fvsP, xFvs, xrest, Eiss, Tss, ⟨hCD, hO, ⟨crest, hopP, hopX⟩, hks,
    hlenX, hlenP, hidxX',
    hidxP', hidxEq, hdomRead, fun ψ => by simp [Eiss], ?_, ?_, ?_, ?_, ?_, ?_, fun ψ => by simp [Tss],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro ψ i x hx hk
    have hi : i < nF := by rw [← hlenX]; exact (List.getElem?_eq_some_iff.mp hx).1
    rw [hEissGet ψ i hi]
    exact (hEis ψ i ⟨hk, hi⟩).2.1 x hx
  · intro ψ i hk hi
    rw [hEissGet ψ i hi]
    exact (hEis ψ i ⟨hk, hi⟩).1
  · intro ψ i hk hi
    rw [hEissGet ψ i hi]
    exact (hEis ψ i ⟨hk, hi⟩).2.2
  · intro ψ₁ ψ₂ hφ
    have hds := (hCD.params ψ₁ ψ₂ hφ).1
    simp only [Eiss]
    apply List.map_congr_left
    intro i hi
    have hi' : i < nF := List.mem_range.mp hi
    by_cases hk : ks.getD i .ordinary = .recursive
    · have h1 := (hEis ψ₁ i ⟨hk, hi'⟩).2.2
      have h2 := (hEis ψ₂ i ⟨hk, hi'⟩).2.2
      rw [hds] at h1
      have heq := h1.symm.trans h2
      have hl : (paramBvarsAt nP (nP + i) ++ Eis ψ₁ i).length
          = (paramBvarsAt nP (nP + i) ++ Eis ψ₂ i).length := by
        simp [(hEis ψ₁ i ⟨hk, hi'⟩).1, (hEis ψ₂ i ⟨hk, hi'⟩).1]
      exact List.append_cancel_left (mkAppN_inj_args heq hl).2
    · by_cases hk' : ks.getD i .ordinary = .reflexive
      · have h1 := (hEisR ψ₁ i ⟨hk', hi'⟩).2.2.2.1
        have h2 := (hEisR ψ₂ i ⟨hk', hi'⟩).2.2.2.1
        rw [hds] at h1
        have heq := h1.symm.trans h2
        obtain ⟨x, hx⟩ : ∃ x, xFvs[i]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have hlt : (Tl ψ₁ i).length = (Tl ψ₂ i).length := by
          rw [(hEisR ψ₁ i ⟨hk', hi'⟩).2.1 x hx, (hEisR ψ₂ i ⟨hk', hi'⟩).2.1 x hx]
        obtain ⟨hteq, hbeq⟩ := mkPisAV_inj hlt heq
        rw [hteq] at hbeq
        have hl : (paramBvarsAt nP (nP + i + (Tl ψ₂ i).length) ++ Eis ψ₁ i).length
            = (paramBvarsAt nP (nP + i + (Tl ψ₂ i).length) ++ Eis ψ₂ i).length := by
          simp [(hEisR ψ₁ i ⟨hk', hi'⟩).1, (hEisR ψ₂ i ⟨hk', hi'⟩).1]
        exact List.append_cancel_left (mkAppN_inj_args hbeq hl).2
      · rw [hEisNone ψ₁ i hk hk', hEisNone ψ₂ i hk hk']
  · intro ψ i E hE
    rw [hEissGet' ψ i] at hE
    rw [hTssGet' ψ i]
    split at hE
    · next hi =>
      rw [if_pos hi]
      by_cases hk : ks.getD i .ordinary = .recursive
      · have hentry := (hEis ψ i ⟨hk, hi⟩).2.2
        have hb := hentryBelow ψ i hi
        rw [hentry, AnnotTerm.erase_mkAppN] at hb
        obtain ⟨-, hall⟩ := bvarsBelow_mkAppN_inv hb
        rw [hTlNone ψ i (hnotboth i hk), List.length_nil, Nat.add_zero]
        exact hall E.erase (List.mem_map.mpr ⟨E, List.mem_append_right _ hE, rfl⟩)
      · by_cases hk' : ks.getD i .ordinary = .reflexive
        · exact (hreflBelow ψ i ⟨hk', hi⟩).2 E hE
        · rw [hEisNone ψ i hk hk'] at hE
          exact nomatch hE
    · exact nomatch hE
  · intro ψ i hk hk'
    rw [hEissGet' ψ i]
    split
    · exact hEisNone ψ i hk hk'
    · rfl
  · intro ψ i hk
    rw [hTssGet' ψ i]
    split
    · exact hTlNone ψ i hk
    · rfl
  · intro ψ i d hd
    rw [hTssGet' ψ i] at hd
    split at hd
    · next hi =>
      by_cases hk' : ks.getD i .ordinary = .reflexive
      · exact (hEisR ψ i ⟨hk', hi⟩).2.2.2.2.1 d hd
      · rw [hTlNone ψ i hk'] at hd
        exact nomatch hd
    · exact nomatch hd
  · intro ψ i d hd
    rw [hTssGet' ψ i] at hd
    split at hd
    · next hi =>
      by_cases hk' : ks.getD i .ordinary = .reflexive
      · exact (hEisR ψ i ⟨hk', hi⟩).2.2.2.2.2 d hd
      · rw [hTlNone ψ i hk'] at hd
        exact nomatch hd
    · exact nomatch hd
  · intro ψ i
    rw [hTssGet' ψ i]
    split
    · next hi =>
      by_cases hk' : ks.getD i .ordinary = .reflexive
      · exact (hreflBelow ψ i ⟨hk', hi⟩).1
      · rw [hTlNone ψ i hk']; trivial
    · trivial
  · intro ψ₁ ψ₂ hφ
    have hds := (hCD.params ψ₁ ψ₂ hφ).1
    simp only [Tss]
    apply List.map_congr_left
    intro i hi
    have hi' : i < nF := List.mem_range.mp hi
    by_cases hk' : ks.getD i .ordinary = .reflexive
    · have h1 := (hEisR ψ₁ i ⟨hk', hi'⟩).2.2.2.1
      have h2 := (hEisR ψ₂ i ⟨hk', hi'⟩).2.2.2.1
      rw [hds] at h1
      have heq := h1.symm.trans h2
      obtain ⟨x, hx⟩ : ∃ x, xFvs[i]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hlt : (Tl ψ₁ i).length = (Tl ψ₂ i).length := by
        rw [(hEisR ψ₁ i ⟨hk', hi'⟩).2.1 x hx, (hEisR ψ₂ i ⟨hk', hi'⟩).2.1 x hx]
      exact (mkPisAV_inj hlt heq).1
    · rw [hTlNone ψ₁ i hk', hTlNone ψ₂ i hk']
  · intro ψ i x hx hk
    have hi : i < nF := by rw [← hlenX]; exact (List.getElem?_eq_some_iff.mp hx).1
    rw [hTssGet ψ i hi, hEissGet ψ i hi]
    obtain ⟨afvs, body, hop, hdoms, hsp⟩ := (hEisR ψ i ⟨hk, hi⟩).2.2.1 x hx
    exact ⟨afvs, body, hop, (hEisR ψ i ⟨hk, hi⟩).2.1 x hx, hdoms, hsp⟩
  · intro ψ i hk hi
    rw [hEissGet ψ i hi]
    exact (hEisR ψ i ⟨hk, hi⟩).1
  · intro ψ i hk hi
    rw [hTssGet ψ i hi, hEissGet ψ i hi]
    exact (hEisR ψ i ⟨hk, hi⟩).2.2.2.1

end ConLeche.Model
