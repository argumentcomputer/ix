module

public import ConLeche.Model.IndPinGrade
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Annot.BitRename
public section

/-!
# The projection bottom's kit, at the reading (task #161, IND TIER part 9)

The five kit lemmas the projection bottom needs and that parts 4–8 did
not have to transpose, written *alongside* their first consumer per the
part-7 producer-side ledger entry, plus the one piece of genuinely new
P-tier reasoning the part-8 seal named.

* `stripLams_denotePTele` — `stripPis_denotePTele`'s λ twin, move for
  move, with `LamTele` (`IndTowerReadP.lean`) in place of v1's
  `lamCtx` constructor;
* `PiTeleAV.det` — a read Π-tower is determined by its arity and
  subject;
* `towerCtxEqDAV`/`towerCtxEqAV` — two canonically-opened towers whose
  raw domains *read* equally (resp. are equal) have the same read
  context.  This is the projection install's substitute for the
  `DefEqListW` walks the iota install runs;
* `projBodyValueAV`/`projRhsValueAV` — the rule tower's β-contractum and
  the statement's right side are the field's bound/frame variable.

**The new reasoning: `projSpineMem`.**  The projection statement
records no walks, so `point`'s `hspMem` cannot come from a ladder.  It
comes from the *syntactic* identification the install checks: with
`cnP = rP` the fire's spine **is** the statement frame's openers
(`fvs.take cnP ++ fvs.drop rP = fvs`), so the constructor run's `q`-th
domain reads at depth `q` to the tower slot `Γ.getD (K - 1 - q)` —
`instPisAt_openerDoms`, which is `stripPis_denotePTele`'s move at an
`instPisAt` run — and the membership is then the frame's own `Sat`
slot transported across `denoteMeta_lift`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name BinderMeta)

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AnnotTerm}

/-! ## The read Π-tower is determined -/

/-- **A `PiTeleAV` is determined by its arity and subject**
(`PiTele.det`). -/
theorem PiTeleAV.det : ∀ {k : Nat} {T : AnnotTerm} {Γ Γ' : List AnnotTerm}
    {R R' : AnnotTerm}, PiTeleAV k T Γ R → PiTeleAV k T Γ' R' →
    Γ = Γ' ∧ R = R' := by
  intro k
  induction k with
  | zero =>
    intro T Γ Γ' R R' h h'
    cases h
    cases h'
    exact ⟨rfl, rfl⟩
  | succ k ih =>
    intro T Γ Γ' R R' h h'
    cases h with
    | @cons _ _ _ A B _ Γ0 h0 =>
      cases h' with
      | @cons _ _ _ _ _ _ Γ0' h0' =>
        obtain ⟨h1, h2⟩ := ih h0 h0'
        exact ⟨by rw [h1], h2⟩

/-! ## The λ telescope, stripped and read -/

set_option maxHeartbeats 1600000 in
/-- **The λ-tower, read** (`stripLams_denoteTele`): a reading λ-tower
is a `LamTele` at its domains' readings, with the body and each raw
domain read under the anonymous openers (`openFvars`) — the reading is
blind to an opener's name and annotation, so any same-index opener
family produces the same tower. -/
theorem stripLams_denotePTele :
    ∀ (k : Nat) {e : Expr} {j : Nat}
      {bs : List (Expr × BinderMeta)} {body : Expr}
      {E : AnnotTerm},
      e.stripLams k = some (bs, body) →
      denoteMeta acval env φ j e = some E →
      ∃ (Γ : List AnnotTerm) (C : AnnotTerm),
        LamTele k E Γ C ∧ Γ.length = k ∧
        denoteMeta acval env φ (j + k)
          (Expr.instSeq (openFvars j k) (k - 1) body) = some C ∧
        ∀ (i0 : Nat) (b : Expr × BinderMeta), bs[i0]? = some b →
          denoteMeta acval env φ (j + i0)
            (Expr.instSeq (openFvars j i0) (i0 - 1) b.1) =
            some (Γ.getD (k - 1 - i0) default) := by
  intro k
  induction k with
  | zero =>
    intro e j bs body E h hE
    simp only [ConLeche.Expr.stripLams, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], E, .nil, rfl, hE, fun i0 b hb => nomatch hb⟩
  | succ k ih =>
    intro e j bs body E h hE
    match e, h with
    | .lam dom bodyE mb, h =>
      simp only [ConLeche.Expr.stripLams] at h
      cases hs : bodyE.stripLams k with
      | none => rw [hs] at h; exact nomatch h
      | some p => ?_
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [denoteMeta_lam] at hE
      cases hA : denoteMeta acval env φ j dom with
      | none => rw [hA] at hE; exact nomatch hE
      | some A => ?_
      rw [hA] at hE
      cases hB : denoteMeta acval env φ (j + 1)
          (bodyE.instantiate1 (.fvar j dom)) with
      | none => rw [hB] at hE; exact nomatch hE
      | some Bv => ?_
      rw [hB] at hE
      obtain rfl : E = .lam (pwBit φ mb.pw) A Bv := by
        simpa using hE.symm
      -- re-open at the anonymous opener (the reading is blind to it)
      have hB' : denoteMeta acval env φ (j + 1)
          (bodyE.instantiate1 (.fvar j (.sort .zero)))
          = some Bv := by
        rw [denoteMeta_erasedEq (ConLeche.Expr.ErasedEq.instantiate1
          (ConLeche.Expr.ErasedEq.rfl bodyE)
          (show ConLeche.Expr.ErasedEq
              (.fvar j (.sort .zero)) (.fvar j dom)
            from by constructor)) (j + 1)]
        exact hB
      have hsI : ((bodyE.instantiate1 (.fvar j
          (.sort .zero))).stripLams k).isSome :=
        ConLeche.Expr.stripLams_instantiate1_isSome k 0 (by rw [hs]; rfl)
      obtain ⟨bs', body', hsI2⟩ : ∃ bs' body',
          (bodyE.instantiate1 (.fvar j
            (.sort .zero))).stripLams k = some (bs', body') := by
        cases hq : (bodyE.instantiate1 (.fvar j
            (.sort .zero))).stripLams k with
        | none => rw [hq] at hsI; exact nomatch hsI
        | some q => exact ⟨q.1, q.2, rfl⟩
      obtain ⟨hbody', hdoms'⟩ :=
        ConLeche.Expr.stripLams_instantiate1_eq k 0 hs hsI2
      obtain ⟨Γ', C, htele, hΓlen, hbody, hdoms⟩ := ih hsI2 hB'
      have hbslen' : bs'.length = k :=
        ConLeche.Expr.stripLams_length k hsI2
      refine ⟨Γ' ++ [A], C, .cons htele, by simp [hΓlen], ?_, ?_⟩
      · show denoteMeta acval env φ (j + (k + 1))
          (Expr.instSeq (openFvars j (k + 1)) (k + 1 - 1) p.2)
          = some C
        rw [show openFvars j (k + 1) = .fvar j
            (.sort .zero) :: openFvars (j + 1) k from rfl,
          show Expr.instSeq (.fvar j (.sort .zero)
              :: openFvars (j + 1) k) (k + 1 - 1) p.2 =
            Expr.instSeq (openFvars (j + 1) k) (k - 1)
              (p.2.instantiate1 (.fvar j (.sort .zero))
                k) from by simp [Expr.instSeq],
          show j + (k + 1) = j + 1 + k from by omega,
          show p.2.instantiate1 (.fvar j (.sort .zero))
              k = body' from by
            rw [hbody']
            simp only [Nat.zero_add]]
        exact hbody
      · intro i0 b hb
        cases i0 with
        | zero =>
          obtain rfl : (dom, mb) = b := by simpa using hb
          show denoteMeta acval env φ (j + 0)
            (Expr.instSeq (openFvars j 0) (0 - 1) dom) = _
          rw [show (Γ' ++ [A]).getD (k + 1 - 1 - 0) default = A from by
            simp only [Nat.sub_zero, Nat.add_sub_cancel, List.getD]
            rw [List.getElem?_append_right (by omega), hΓlen,
              Nat.sub_self]
            rfl]
          exact hA
        | succ i0 =>
          rw [List.getElem?_cons_succ] at hb
          have hik : i0 < k := by
            rcases Nat.lt_or_ge i0 k with h' | h'
            · exact h'
            · rw [List.getElem?_eq_none
                (by rw [ConLeche.Expr.stripLams_length k hs]; omega)] at hb
              exact nomatch hb
          have hb' : bs'[i0]? = some (bs'[i0]'(by omega)) :=
            List.getElem?_eq_getElem (by omega)
          have hdomEq := hdoms' i0 b (bs'[i0]'(by omega)) hb hb'
          have h1 := hdoms i0 _ hb'
          rw [hdomEq] at h1
          rw [show (Γ' ++ [A]).getD (k + 1 - 1 - (i0 + 1)) default =
              Γ'.getD (k - 1 - i0) default from by
            simp only [List.getD]
            rw [show k + 1 - 1 - (i0 + 1) = k - 1 - i0 from by omega,
              List.getElem?_append_left (by omega)]]
          show denoteMeta acval env φ (j + (i0 + 1))
            (Expr.instSeq (openFvars j (i0 + 1)) (i0 + 1 - 1) b.1)
            = _
          rw [show openFvars j (i0 + 1) = .fvar j
              (.sort .zero) :: openFvars (j + 1) i0 from rfl,
            show Expr.instSeq (.fvar j (.sort .zero)
                :: openFvars (j + 1) i0) (i0 + 1 - 1) b.1 =
              Expr.instSeq (openFvars (j + 1) i0) (i0 - 1)
                (b.1.instantiate1 (.fvar j
                  (.sort .zero)) i0) from by
              simp [Expr.instSeq],
            show j + (i0 + 1) = j + 1 + i0 from by omega]
          rw [show (0 : Nat) + i0 = i0 from by omega] at h1
          exact h1

/-! ## The two towers, identified syntactically -/

/-- **Two canonically-opened towers whose raw domains read equally at
their own depths have the same read context** (`towerCtxEqD`).  The
reading-level form is what a *renamed* domain pin needs — the
projection statement's telescope is the constructor's renamed, not
equal to it. -/
theorem towerCtxEqDAV {k : Nat} {Γβ Γc : List AnnotTerm}
    {rbinders cbinders : List (Expr × BinderMeta)}
    (hrblen : rbinders.length = k) (hcblen : cbinders.length = k)
    (hΓβlen : Γβ.length = k) (hΓclen : Γc.length = k)
    (hβdoms : ∀ (i0 : Nat) (b : Expr × BinderMeta),
      rbinders[i0]? = some b →
      denoteMeta acval env φ (0 + i0)
        (Expr.instSeq (openFvars 0 i0) (i0 - 1) b.1) =
        some (Γβ.getD (k - 1 - i0) default))
    (hcdoms : ∀ (i0 : Nat) (b : Expr × BinderMeta),
      cbinders[i0]? = some b →
      denoteMeta acval env φ (0 + i0)
        (Expr.instSeq (openFvars 0 i0) (i0 - 1) b.1) =
        some (Γc.getD (k - 1 - i0) default))
    (hrdomsEq : ∀ (i0 : Nat) (b b' : Expr × BinderMeta),
      i0 < k → rbinders[i0]? = some b →
      cbinders[i0]? = some b' →
      denoteMeta acval env φ (0 + i0)
          (Expr.instSeq (openFvars 0 i0) (i0 - 1) b.1) =
        denoteMeta acval env φ (0 + i0)
          (Expr.instSeq (openFvars 0 i0) (i0 - 1) b'.1)) :
    Γβ = Γc := by
  refine List.ext_getElem (by omega) ?_
  intro q h1 h2
  have hq : q < k := by omega
  have hbβlt : k - 1 - q < rbinders.length := by omega
  have hbclt : k - 1 - q < cbinders.length := by omega
  obtain ⟨bβ, hbβ⟩ : ∃ b, rbinders[k - 1 - q]? = some b :=
    ⟨rbinders[k - 1 - q]'hbβlt, List.getElem?_eq_getElem hbβlt⟩
  obtain ⟨bc, hbc⟩ : ∃ b, cbinders[k - 1 - q]? = some b :=
    ⟨cbinders[k - 1 - q]'hbclt, List.getElem?_eq_getElem hbclt⟩
  have hβq := hβdoms (k - 1 - q) bβ hbβ
  have hcq := hcdoms (k - 1 - q) bc hbc
  have hdomeq := hrdomsEq (k - 1 - q) bβ bc (by omega) hbβ hbc
  rw [hdomeq] at hβq
  have h3 : Γβ.getD (k - 1 - (k - 1 - q)) default =
      Γc.getD (k - 1 - (k - 1 - q)) default :=
    Option.some.inj (hβq.symm.trans hcq)
  rw [show k - 1 - (k - 1 - q) = q from by omega] at h3
  rw [show Γβ[q] = Γβ.getD q default from by
      simp [List.getD, List.getElem?_eq_getElem h1],
    show Γc[q] = Γc.getD q default from by
      simp [List.getD, List.getElem?_eq_getElem h2]]
  exact h3

/-- **Two canonically-opened towers with pointwise-equal raw domains
have the same read context** (`towerCtxEq`). -/
theorem towerCtxEqAV {k : Nat} {Γβ Γc : List AnnotTerm}
    {rbinders cbinders : List (Expr × BinderMeta)}
    (hrblen : rbinders.length = k) (hcblen : cbinders.length = k)
    (hΓβlen : Γβ.length = k) (hΓclen : Γc.length = k)
    (hβdoms : ∀ (i0 : Nat) (b : Expr × BinderMeta),
      rbinders[i0]? = some b →
      denoteMeta acval env φ (0 + i0)
        (Expr.instSeq (openFvars 0 i0) (i0 - 1) b.1) =
        some (Γβ.getD (k - 1 - i0) default))
    (hcdoms : ∀ (i0 : Nat) (b : Expr × BinderMeta),
      cbinders[i0]? = some b →
      denoteMeta acval env φ (0 + i0)
        (Expr.instSeq (openFvars 0 i0) (i0 - 1) b.1) =
        some (Γc.getD (k - 1 - i0) default))
    (hrdomsEq : ∀ (i0 : Nat) (b b' : Expr × BinderMeta),
      i0 < k → rbinders[i0]? = some b →
      cbinders[i0]? = some b' → b.1 = b'.1) :
    Γβ = Γc :=
  towerCtxEqDAV hrblen hcblen hΓβlen hΓclen hβdoms hcdoms
    (fun i0 b b' hi hb hb' => by rw [hrdomsEq i0 b b' hi hb hb'])

/-! ## The projection rule's two values -/

/-- **The projection rule's opened body reads to the field's bound
variable** (`projBodyValue`). -/
theorem projBodyValueAV {cnP cnF i : Nat} (hilt : i < cnF) {Cβ : AnnotTerm}
    (hCβden : denoteMeta acval env φ (0 + (cnP + cnF))
      (Expr.instSeq (openFvars 0 (cnP + cnF)) (cnP + cnF - 1)
        (.bvar (cnF - 1 - i))) = some Cβ) :
    Cβ = .bvar (cnP + cnF - 1 - (cnP + i)) := by
  have hhit := Expr.instSeq_bvar (openFvars 0 (cnP + cnF))
    (cnP + cnF - 1) (cnF - 1 - i)
    (openFvars_bounded 0 (cnP + cnF)) (by omega)
    (by rw [openFvars_length]; omega)
  rw [openFvars_getElem? (d := 0) (k := cnP + cnF)
    (i := cnP + cnF - 1 - (cnF - 1 - i)) (by omega)] at hhit
  rw [show cnP + cnF - 1 - (cnF - 1 - i) = cnP + i from by omega] at hhit
  have h2 := hCβden
  rw [← Option.some.inj hhit, denoteMeta_fvar] at h2
  rw [← Option.some.inj h2]
  simp only [Nat.zero_add]

/-- **The projection statement's right side reads to the field's frame
variable** (`projRhsValue`). -/
theorem projRhsValueAV {fvs : List Expr} {rP cnF i : Nat} {vR : AnnotTerm}
    (hshapeS : ∀ (i0 : Nat) (x : Expr), fvs[i0]? = some x →
      ∃ ty, x = Expr.fvar i0 ty)
    (hfvslen : fvs.length = rP + cnF) (hilt : i < cnF)
    (hRden : denoteMeta acval env φ (rP + cnF)
      (fvs.getD (rP + i) default) = some vR) :
    vR = .bvar (rP + cnF - 1 - (rP + i)) := by
  obtain ⟨t, hsh⟩ := hshapeS (rP + i) fvs[rP + i]
    (List.getElem?_eq_getElem (show rP + i < fvs.length from by omega))
  rw [show fvs.getD (rP + i) default = fvs[rP + i] from by
      simp [List.getD, List.getElem?_eq_getElem
        (show rP + i < fvs.length from by omega)],
    hsh, denoteMeta_fvar] at hRden
  exact (Option.some.inj hRden).symm

/-! ## The run's domains at an opener spine

The projection install checks no domain *walks*; what it checks is that
the statement's telescope domains **are** the constructor's, renamed.
With `cnP = rP` the fire's spine is the frame's own openers, so the
constructor run's domains are the constructor tower's own domains, read
at their own depths.  That is `stripPis_denotePTele`'s move, run at an
`instPisAt` rather than a `stripPis`. -/

/-- **An `instPisAt` run at an opener spine reads its domains to the
tower's slots.**  No carrier equation is consumed: the only step that
touches the spine is `denoteMeta_erasedEq`, and the reading is blind to an
opener's name and annotation. -/
theorem instPisAt_openerDoms :
    ∀ (sp : List Expr) {ty : Expr} {ds : List Expr} {rs : Expr},
      Expr.instPisAt sp ty = some (ds, rs) →
      ∀ {j : Nat} {T : AnnotTerm},
        (∀ (q : Nat) (x : Expr), sp[q]? = some x →
          ∃ t, x = Expr.fvar (j + q) t) →
        denoteMeta acval env φ j ty = some T →
        ∀ {Γ : List AnnotTerm} {R : AnnotTerm}, PiTeleAV sp.length T Γ R →
        ∀ q, q < sp.length →
          denoteMeta acval env φ (j + q) (ds.getD q default)
            = some (Γ.getD (sp.length - 1 - q) default) := by
  intro sp
  induction sp with
  | nil =>
    intro ty ds rs _ j T _ _ Γ R _ q hq
    exact absurd hq (by simp)
  | cons a sp ih =>
    intro ty ds rs h j T hshape hT Γ R htele q hq
    obtain ⟨t0, rfl⟩ := hshape 0 a rfl
    match ty, h with
    | .forallE dom bodyE mb, h =>
      simp only [Expr.instPisAt] at h
      cases h1 : Expr.instPisAt sp (bodyE.instantiate1
          (.fvar (j + 0) t0)) with
      | none => rw [h1] at h; exact nomatch h
      | some p => ?_
      rw [h1] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [denoteMeta_forallE] at hT
      cases hA : denoteMeta acval env φ j dom with
      | none => rw [hA] at hT; exact nomatch hT
      | some A => ?_
      rw [hA] at hT
      cases hB : denoteMeta acval env φ (j + 1)
          (bodyE.instantiate1 (.fvar j dom)) with
      | none => rw [hB] at hT; exact nomatch hT
      | some Bv => ?_
      rw [hB] at hT
      obtain rfl : T = .pi 0 (pwBit φ mb.pw) A Bv := by
        simpa using hT.symm
      obtain ⟨u', v', A', B', Γ', heqT, rfl, htele'⟩ := htele.succ_inv
      -- note: this `obtain` eliminates `A`/`Bv`, so the text below is
      -- written in the surviving names `A'`/`B'`
      obtain ⟨rfl, rfl⟩ : A' = A ∧ B' = Bv := by
        injection heqT with _ _ hA' hB'
        exact ⟨hA'.symm, hB'.symm⟩
      have hΓ'len : Γ'.length = sp.length := htele'.length
      cases q with
      | zero =>
        simp only [List.length_cons, Nat.add_zero]
        rw [show ((dom :: p.1).getD 0 default) = dom from rfl,
          show (Γ' ++ [A']).getD (sp.length + 1 - 1 - 0) default = A' from by
            simp only [Nat.sub_zero, Nat.add_sub_cancel, List.getD]
            rw [List.getElem?_append_right (by omega), hΓ'len,
              Nat.sub_self]
            rfl]
        exact hA
      | succ q =>
        simp only [List.length_cons] at hq ⊢
        have hqs : q < sp.length := by omega
        -- the recursion runs at the *spine's* opener; the reading is
        -- blind to it
        have hB' : denoteMeta acval env φ (j + 1)
            (bodyE.instantiate1 (.fvar (j + 0) t0)) = some B' := by
          rw [denoteMeta_erasedEq (ConLeche.Expr.ErasedEq.instantiate1
            (ConLeche.Expr.ErasedEq.rfl bodyE)
            (show ConLeche.Expr.ErasedEq (.fvar (j + 0) t0)
                (.fvar j dom) from by
              rw [Nat.add_zero]; constructor)) (j + 1)]
          exact hB
        have hshape' : ∀ (q0 : Nat) (x : Expr), sp[q0]? = some x →
            ∃ t, x = Expr.fvar (j + 1 + q0) t := by
          intro q0 x hx
          obtain ⟨t', hx'⟩ := hshape (q0 + 1) x (by simpa using hx)
          exact ⟨t', by rw [hx']; congr 1; omega⟩
        have hrec := ih h1 hshape' hB' htele' q hqs
        rw [show (dom :: p.1).getD (q + 1) default
            = p.1.getD q default from rfl,
          show j + (q + 1) = j + 1 + q from by omega, hrec,
          show (Γ' ++ [A']).getD (sp.length + 1 - 1 - (q + 1)) default
              = Γ'.getD (sp.length - 1 - q) default from by
            simp only [List.getD]
            rw [show sp.length + 1 - 1 - (q + 1) = sp.length - 1 - q from by
                omega,
              List.getElem?_append_left (by omega)]]

set_option maxHeartbeats 1600000 in
/-- **The projection fire's spine memberships** — `point`'s `hspMem`,
supplied without a walk.  The spine is the frame's own openers, so each
position's reading is a `.bvar` and the run's `q`-th domain reads (at
depth `q`) to the tower slot the frame's `Sat` already inhabits;
`denoteMeta_lift` moves both to the frame depth. -/
theorem projSpineMem
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    {K : Nat} {fvs : List Expr} (hfvslen : fvs.length = K)
    (hshapeS : ∀ (q : Nat) (x : Expr), fvs[q]? = some x →
      ∃ ty, x = Expr.fvar q ty)
    (hwsTy : ∀ (q : Nat) (ty : Expr),
      Expr.fvar q ty ∈ fvs → Expr.WScoped q ty)
    {ctyR : Expr} (hCwR : ctyR.hasFvar = false)
    {cdoms : List Expr} {cres : Expr}
    (hcinst : Expr.instPisAt fvs ctyR = some (cdoms, cres))
    {Γs : List AnnotTerm} (hΓslen : Γs.length = K)
    (hdomsLow : ∀ q, q < K →
      denoteMeta acval env φ q (cdoms.getD q default)
        = some (Γs.getD (K - 1 - q) default)) :
    ∀ σ : Nat → V, Sat V Γs σ →
      ∀ (q : Nat) (x : Expr), fvs[q]? = some x →
        ∃ w, denoteMeta acval env φ K x = some w ∧ WellDenotedV V σ w ∧
          ∀ dw, denoteMeta acval env φ K (cdoms.getD q default) = some dw →
            interp V σ w ∈ˢ interp V σ dw := by
  have hcdlen : cdoms.length = K := by
    have h := instPisAt_length _ hcinst
    omega
  -- each run domain is scoped at its own index (`d := 0`)
  have hwsDom : ∀ q, q < K → Expr.WScoped q (cdoms.getD q default) := by
    intro q hq
    rcases hr : cdoms[q]? with _ | r
    · rw [List.getElem?_eq_none_iff] at hr; omega
    have h := instPisAt_index_WScoped fvs hcinst
      (d := 0) (Expr.WScoped.of_not_hasFvar hCwR)
      (fun i a ha => by
        obtain ⟨t0, rfl⟩ := hshapeS i a ha
        have hty := hwsTy i t0 (List.mem_of_getElem? ha)
        simp only [Expr.WScoped]
        exact ⟨by omega, hty⟩)
      q r hr
    rw [show cdoms.getD q default = r from by rw [List.getD, hr]; rfl,
      ← show (0 : Nat) + q = q from Nat.zero_add q]
    exact h
  intro σ hσ q x hx
  have hq : q < K := by
    rcases Nat.lt_or_ge q K with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none (by omega)] at hx
      exact nomatch hx
  obtain ⟨ty, rfl⟩ := hshapeS q x hx
  refine ⟨.bvar (K - 1 - q), denoteMeta_fvar acval K q ty,
    ⟨by simp, by simp⟩, ?_⟩
  intro dw hdw
  -- the domain at the frame depth is its own-depth reading, lifted
  have hlift := denoteMeta_lift (acval := acval) (env := env) (φ := φ) hacl
    (hwsDom q hq) K (by omega)
  rw [hdw, hdomsLow q hq] at hlift
  obtain rfl : dw = AnnotTerm.liftN (K - q)
      (Γs.getD (K - 1 - q) default) 0 := Option.some.inj hlift
  have hslot := hσ (K - 1 - q) (Γs.getD (K - 1 - q) default) (by
    rw [List.getD]
    rcases hg : Γs[K - 1 - q]? with _ | A
    · rw [List.getElem?_eq_none_iff] at hg; omega
    · rfl)
  rw [interp_bvar, interp_liftN]
  rw [show shiftE (K - q) 0 σ
      = (fun j => σ (j + (K - 1 - q) + 1)) from by
    funext j
    show (if j < 0 then σ j else σ (j + (K - q))) = _
    rw [if_neg (Nat.not_lt_zero j)]
    congr 1
    omega]
  exact hslot

end ConLeche.Model
