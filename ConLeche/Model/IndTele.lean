module

public import ConLeche.Model.IndMembers
import ConLeche.Model.Annot.Laws
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Annot.BitRename

public section

/-!
# The reading's ∀-telescope (task #161, IND TIER part 2)

The capability keys read a *stored theorem's* type — a syntactic
∀-telescope whose binders `checkEtaThm`/`checkUnitThm` pinned — and
fire it at a spine.  v1 does this with `stripPis_denoteTele`
(`Verify/Denote/IndFrame.lean`), whose output is a `PiTele` plus the
opened domain and body readings; this file is that lemma's transpose,
and the transposition is **near-verbatim** for one reason recorded in
part 1's `BitRename.lean`:

> `denoteMeta`'s binder clauses instantiate with the binder's *own* name
> and type, exactly as `denote`'s do, and `denoteMeta_erasedEq` is blind
> to both — so the re-opening at the anonymous opener (`openFvars`)
> that v1's induction performs transposes move for move.

The one shape delta: `denoteMeta` reads a `∀` to `.pi 0 (pwBit φ mb.pw)`,
so the reading's telescope carries *bits*, and `PiTeleAV`'s `cons`
quantifies them existentially.  Nothing downstream reads them — the
consumers are `TeleFit` (which quantifies its own) and
`wellDenotedV_mkAppN_of_fit` (which takes them from the grading).

Also here: the two consumers the keys need and the campaign did not
yet own —

* `memFoldl_of_teleFit`, the *value-level* twin of
  `wellDenotedV_mkAppN_of_fit`.  The caps laws quantify their spines as
  bare `V`s (the divmod-leg lesson, frozen), so the applied-membership
  walk cannot go through the `AnnotTerm` form; it is the same induction
  with the grading conjuncts deleted, and it needs the type's grading
  only for `app_mem_piR`'s `v = 0` fibre premise.
* `teleFitP_of_piTeleP`, which rebuilds a fit at a *second* telescope
  from the memberships of a fit at the first.  The keys need it
  because the fit they are *given* is at the family former's type and
  the fit they must *fire* is at the checked statement's, and the two
  agree only through the pins' domain equalities.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics ConLeche.SetModel
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AnnotTerm}

/-! ## The reading's telescope -/

/-- **`PiTele`'s transpose at the reading.**  The bits are existential
(see the module docstring): a `∀` reads to `.pi 0 (pwBit φ mb.pw)` and
no consumer of this file reads either component. -/
inductive PiTeleAV : Nat → AnnotTerm → List AnnotTerm → AnnotTerm → Prop
  | nil {T : AnnotTerm} : PiTeleAV 0 T [] T
  | cons {k u v : Nat} {A B R : AnnotTerm} {Γ : List AnnotTerm} :
      PiTeleAV k B Γ R → PiTeleAV (k + 1) (.pi u v A B) (Γ ++ [A]) R

theorem PiTeleAV.length : ∀ {k : Nat} {T : AnnotTerm} {Γ : List AnnotTerm}
    {R : AnnotTerm}, PiTeleAV k T Γ R → Γ.length = k := by
  intro k T Γ R h
  induction h with
  | nil => rfl
  | cons _ ih => simp [ih]

/-- A telescope of positive length exposes its head `.pi`. -/
theorem PiTeleAV.succ_inv {k : Nat} {T : AnnotTerm} {Γ : List AnnotTerm}
    {R : AnnotTerm} (h : PiTeleAV (k + 1) T Γ R) :
    ∃ (u v : Nat) (A B : AnnotTerm) (Γ' : List AnnotTerm),
      T = .pi u v A B ∧ Γ = Γ' ++ [A] ∧ PiTeleAV k B Γ' R := by
  cases h with
  | cons h' => exact ⟨_, _, _, _, _, rfl, rfl, h'⟩

/-! ## The strip, read

`stripPis_denoteTele`'s transpose, move for move. -/

theorem stripPis_denotePTele :
    ∀ (k : Nat) {e : Expr} {j : Nat}
      {bs : List (Expr × BinderMeta)} {body : Expr}
      {E : AnnotTerm},
      e.stripPis k = some (bs, body) →
      denoteMeta acval env φ j e = some E →
      ∃ (Γ : List AnnotTerm) (C : AnnotTerm),
        PiTeleAV k E Γ C ∧ Γ.length = k ∧
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
    simp only [ConLeche.Expr.stripPis, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], E, .nil, rfl, hE, fun i0 b hb => nomatch hb⟩
  | succ k ih =>
    intro e j bs body E h hE
    match e, h with
    | .forallE dom bodyE mb, h =>
      simp only [ConLeche.Expr.stripPis] at h
      cases hs : bodyE.stripPis k with
      | none => rw [hs] at h; exact nomatch h
      | some p => ?_
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [denoteMeta_forallE] at hE
      cases hA : denoteMeta acval env φ j dom with
      | none => rw [hA] at hE; exact nomatch hE
      | some A => ?_
      rw [hA] at hE
      cases hB : denoteMeta acval env φ (j + 1)
          (bodyE.instantiate1 (.fvar j dom)) with
      | none => rw [hB] at hE; exact nomatch hE
      | some Bv => ?_
      rw [hB] at hE
      obtain rfl : E = .pi 0 (pwBit φ mb.pw) A Bv := by
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
          (.sort .zero))).stripPis k).isSome :=
        ConLeche.Expr.stripPis_instantiate1_isSome k 0 (by rw [hs]; rfl)
      obtain ⟨bs', body', hsI2⟩ : ∃ bs' body',
          (bodyE.instantiate1 (.fvar j
            (.sort .zero))).stripPis k = some (bs', body') := by
        cases hq : (bodyE.instantiate1 (.fvar j
            (.sort .zero))).stripPis k with
        | none => rw [hq] at hsI; exact nomatch hsI
        | some q => exact ⟨q.1, q.2, rfl⟩
      obtain ⟨hbody', hdoms'⟩ :=
        ConLeche.Expr.stripPis_instantiate1_eq k 0 hs hsI2
      obtain ⟨Γ', C, htele, hΓlen, hbody, hdoms⟩ := ih hsI2 hB'
      have hbslen : p.1.length = k := ConLeche.Expr.stripPis_length k hs
      have hbslen' : bs'.length = k :=
        ConLeche.Expr.stripPis_length k hsI2
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
            rw [hbody']; simp only [Nat.zero_add]]
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
            · rw [List.getElem?_eq_none (by omega)] at hb
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

/-! ## From a fit to an applied membership, at bare values

`wellDenotedV_mkAppN_of_fit`'s value-level twin: the caps laws' spines are
bare `V`s (frozen), so the applied-membership walk cannot be routed
through the `AnnotTerm` form.  Same induction, grading conjuncts deleted;
the type's grading survives only as `app_mem_piR`'s `v = 0` fibre
premise. -/

theorem memFoldl_of_teleFit :
    ∀ (ts : List V) {ρ : Nat → V} {Ta : AnnotTerm} {f rest : V},
      WellDenotedV V ρ Ta →
      f ∈ˢ interp V ρ Ta →
      TeleFit V ρ Ta ts rest →
      ts.foldl SetTheory.app f ∈ˢ rest := by
  intro ts
  induction ts with
  | nil =>
    intro ρ Ta f rest _ hmem hfit
    obtain rfl : rest = interp V ρ Ta := teleFit_nil_inv hfit
    exact hmem
  | cons t tsr ih =>
    intro ρ Ta f rest hokT hmem hfit
    cases hfit with
    | @cons _ u v A B _ _ _ ht hfit' =>
      have hokB : ∀ y, y ∈ˢ interp V ρ A → WellDenotedV V (cons y ρ) B :=
        fun y hy =>
          ⟨((WellDenoted_pi V ρ u v A B) ▸ hokT.1).2 y hy,
            ((AnnotValid_pi V ρ u v A B) ▸ hokT.2).2.1 y hy⟩
      have hfib : v = 0 → ∀ y, y ∈ˢ interp V ρ A →
          interp V (cons y ρ) B ∈ˢ (univZero : V) :=
        ((AnnotValid_pi V ρ u v A B) ▸ hokT.2).2.2
      rw [interp_pi] at hmem
      exact ih (hokB _ ht) (app_mem_piR hmem ht hfib) hfit'

/-! ## Fitting a *second* telescope from the first's memberships

The keys' central move.  The fit they are **given** is at the family
former's type; the fit they must **fire** is at the checked statement's
type, and the two coincide only through the pins' domain equalities
(`checkEtaThm`/`checkUnitThm`'s `hsdoms` conjunct, which is a
*syntactic* equality of the binder domains and therefore an equality of
their readings).  `teleFit_congr` moves the fit across; `consN` names
the environment the fit ends in, so the residual of the second
telescope can be spoken about at all. -/

/-- The environment a fit ends in: the arguments consed in order. -/
@[expose] def consN : List V → (Nat → V) → (Nat → V)
  | [], ρ => ρ
  | t :: ts, ρ => consN ts (cons t ρ)

omit [SetTheory V] in
@[simp] theorem consN_nil (ρ : Nat → V) : consN [] ρ = ρ := rfl

omit [SetTheory V] in
@[simp] theorem consN_cons (t : V) (ts : List V) (ρ : Nat → V) :
    consN (t :: ts) ρ = consN ts (cons t ρ) := rfl

/-- A fit's residual is its telescope's body, read at `consN`. -/
theorem teleFit_residual :
    ∀ (ts : List V) {ρ : Nat → V} {Ta : AnnotTerm} {Γ : List AnnotTerm}
      {R : AnnotTerm} {rest : V},
      PiTeleAV ts.length Ta Γ R → TeleFit V ρ Ta ts rest →
      rest = interp V (consN ts ρ) R := by
  intro ts
  induction ts with
  | nil =>
    intro ρ Ta Γ R rest hT hfit
    cases hT
    exact teleFit_nil_inv hfit
  | cons t tsr ih =>
    intro ρ Ta Γ R rest hT hfit
    obtain ⟨u, v, A, B, Γ', rfl, hΓ, hT'⟩ := hT.succ_inv
    cases hfit with
    | @cons _ _ _ _ _ _ _ _ _ hfit' => exact ih hT' hfit'

omit [SetTheory V] in
/-- Above the spine `consN` is the ambient environment, shifted. -/
theorem consN_append (as bs : List V) (ρ : Nat → V) :
    consN (as ++ bs) ρ = consN bs (consN as ρ) := by
  induction as generalizing ρ with
  | nil => rfl
  | cons a asr ih => simpa using ih (cons a ρ)

omit [SetTheory V] in
/-- Above the spine `consN` is the ambient environment, shifted. -/
theorem consN_shift : ∀ (ts : List V) (ρ : Nat → V) (j : Nat),
    consN ts ρ (j + ts.length) = ρ j := by
  intro ts
  induction ts with
  | nil => intro ρ j; rfl
  | cons t tsr ih =>
    intro ρ j
    rw [consN_cons,
      show j + (t :: tsr).length = (j + 1) + tsr.length from by
        simp only [List.length_cons]; omega,
      ih (cons t ρ) (j + 1)]
    rfl

omit [SetTheory V] in
/-- `consN`'s action below the spine: index `j` names argument
`ts.length - 1 - j` (the last argument consed is `.bvar 0`). -/
theorem consN_getElem? : ∀ (ts : List V) (ρ : Nat → V) (j : Nat),
    j < ts.length → ts[ts.length - 1 - j]? = some (consN ts ρ j) := by
  intro ts
  induction ts with
  | nil => intro ρ j hj; exact absurd hj (by simp)
  | cons t tsr ih =>
    intro ρ j hj
    rw [consN_cons]
    rcases Nat.lt_or_ge j tsr.length with h | h
    · rw [show (t :: tsr).length - 1 - j = (tsr.length - 1 - j) + 1 from by
        simp only [List.length_cons]; omega,
        List.getElem?_cons_succ]
      exact ih (cons t ρ) j h
    · have hj' : j = tsr.length := by
        simp only [List.length_cons] at hj; omega
      subst hj'
      have hs := consN_shift tsr (cons t ρ) 0
      rw [Nat.zero_add] at hs
      rw [hs, show (t :: tsr).length - 1 - tsr.length = 0 from by
        simp only [List.length_cons]; omega]
      rfl

/-! ## Splitting a telescope -/

/-- A telescope of length `a + b` is an `a`-telescope onto a
`b`-telescope.  The domain lists concatenate the *other* way round —
`PiTeleAV`'s cons appends, so the outermost domain sits last. -/
theorem PiTeleAV.split :
    ∀ (a b : Nat) {E : AnnotTerm} {Γ : List AnnotTerm} {C : AnnotTerm},
      PiTeleAV (a + b) E Γ C →
      ∃ (Γ₁ Γ₂ : List AnnotTerm) (M : AnnotTerm),
        Γ = Γ₁ ++ Γ₂ ∧ Γ₂.length = a ∧ Γ₁.length = b ∧
        PiTeleAV a E Γ₂ M ∧ PiTeleAV b M Γ₁ C := by
  intro a
  induction a with
  | zero =>
    intro b E Γ C h
    rw [Nat.zero_add] at h
    exact ⟨Γ, [], E, by simp, rfl, h.length, .nil, h⟩
  | succ a ih =>
    intro b E Γ C h
    rw [show a + 1 + b = (a + b) + 1 from by omega] at h
    obtain ⟨u, v, A, B, Γ', rfl, hΓ, h'⟩ := h.succ_inv
    obtain ⟨Γ₁, Γ₂, M, rfl, hl2, hl1, hA, hB⟩ := ih b h'
    exact ⟨Γ₁, Γ₂ ++ [A], M, by rw [hΓ, List.append_assoc],
      by simp [hl2], hl1, .cons hA, hB⟩

/-- **The fit, moved across two telescopes with equal domains.** -/
theorem teleFit_congr :
    ∀ (ts : List V) {ρ : Nat → V} {Ta Sa : AnnotTerm}
      {Γ Δ : List AnnotTerm} {R C : AnnotTerm} {rest : V},
      PiTeleAV ts.length Ta Γ R →
      PiTeleAV ts.length Sa Δ C →
      (∀ i, i < ts.length → Γ.getD i default = Δ.getD i default) →
      TeleFit V ρ Ta ts rest →
      TeleFit V ρ Sa ts (interp V (consN ts ρ) C) := by
  intro ts
  induction ts with
  | nil =>
    intro ρ Ta Sa Γ Δ R C rest _ hS _ _
    cases hS
    exact TeleFit.nil
  | cons t tsr ih =>
    intro ρ Ta Sa Γ Δ R C rest hT hS hdoms hfit
    obtain ⟨u₁, v₁, A₁, B₁, Γ', rfl, hΓ, hT'⟩ := hT.succ_inv
    obtain ⟨u₂, v₂, A₂, B₂, Δ', rfl, hΔ, hS'⟩ := hS.succ_inv
    have hΓl : Γ'.length = tsr.length := hT'.length
    have hΔl : Δ'.length = tsr.length := hS'.length
    cases hfit with
    | @cons _ _ _ _ _ _ _ _ ht hfit' =>
      refine TeleFit.cons ?_ (ih hT' hS' ?_ hfit')
      · -- the head domains sit last in both lists
        have h := hdoms tsr.length (by simp)
        rw [hΓ, hΔ, List.getD, List.getD,
          List.getElem?_append_right (by omega),
          List.getElem?_append_right (by omega), hΓl, hΔl,
          Nat.sub_self] at h
        simp only [List.getElem?_cons_zero, Option.getD_some] at h
        rw [← h]
        exact ht
      · intro i hi
        have h := hdoms i (by simp only [List.length_cons]; omega)
        rwa [hΓ, hΔ, List.getD, List.getD,
          List.getElem?_append_left (by omega),
          List.getElem?_append_left (by omega)] at h

/-- **The fit, moved across and then continued.**  `teleFit_congr`
with the second telescope's *remaining* binders fitted too — the shape
the keys consume, since a capability statement's telescope is the
family former's parameters followed by the statement's own members. -/
theorem teleFit_congr_ext :
    ∀ (ts : List V) {ρ : Nat → V} {Ta Sa : AnnotTerm}
      {Γ Δ : List AnnotTerm} {R M : AnnotTerm} {rest : V}
      {more : List V} {r : V},
      PiTeleAV ts.length Ta Γ R →
      PiTeleAV ts.length Sa Δ M →
      (∀ i, i < ts.length → Γ.getD i default = Δ.getD i default) →
      TeleFit V ρ Ta ts rest →
      TeleFit V (consN ts ρ) M more r →
      TeleFit V ρ Sa (ts ++ more) r := by
  intro ts
  induction ts with
  | nil =>
    intro ρ Ta Sa Γ Δ R M rest more r _ hS _ _ hmore
    cases hS
    exact hmore
  | cons t tsr ih =>
    intro ρ Ta Sa Γ Δ R M rest more r hT hS hdoms hfit hmore
    obtain ⟨u₁, v₁, A₁, B₁, Γ', rfl, hΓ, hT'⟩ := hT.succ_inv
    obtain ⟨u₂, v₂, A₂, B₂, Δ', rfl, hΔ, hS'⟩ := hS.succ_inv
    have hΓl : Γ'.length = tsr.length := hT'.length
    have hΔl : Δ'.length = tsr.length := hS'.length
    cases hfit with
    | @cons _ _ _ _ _ _ _ _ ht hfit' =>
      refine TeleFit.cons ?_ (ih hT' hS' ?_ hfit' hmore)
      · have h := hdoms tsr.length (by simp)
        rw [hΓ, hΔ, List.getD, List.getD,
          List.getElem?_append_right (by omega),
          List.getElem?_append_right (by omega), hΓl, hΔl,
          Nat.sub_self] at h
        simp only [List.getElem?_cons_zero, Option.getD_some] at h
        rw [← h]
        exact ht
      · intro i hi
        have h := hdoms i (by simp only [List.length_cons]; omega)
        rwa [hΓ, hΔ, List.getD, List.getD,
          List.getElem?_append_left (by omega),
          List.getElem?_append_left (by omega)] at h

/-- **The fit moved across *semantically* agreeing domains** (task
#161 IND TIER part 2, landed for item 2).

The capability keys need only the syntactic form above: `checkEtaThm`
and `checkUnitThm` pin the statement's parameter domains to be
*literally* the model former's (`hsdoms` is an `Expr` equality), so
their readings are the same `AnnotTerm`.  **The recursor group is not like
that**: `IotaThmR`'s corresponding conjuncts are `DefEqListW` walks —
recorded `isDefEq` runs — so the two telescopes' domains agree only up
to the certificate, which at the P currency is an `interp` equality
and not an `AnnotTerm` one.

The fit never inspects a domain except through `∈ˢ interp`, so the
weakening is free; recording it here means item 2 does not have to
discover it mid-proof.  `teleFit_congr_ext` is the special case where
the readings coincide. -/
theorem teleFit_congr_extS :
    ∀ (ts : List V) {ρ : Nat → V} {Ta Sa : AnnotTerm}
      {Γ Δ : List AnnotTerm} {R M : AnnotTerm} {rest : V}
      {more : List V} {r : V},
      PiTeleAV ts.length Ta Γ R →
      PiTeleAV ts.length Sa Δ M →
      (∀ i, i < ts.length → ∀ σ : Nat → V,
        interp V σ (Γ.getD i default) = interp V σ (Δ.getD i default)) →
      TeleFit V ρ Ta ts rest →
      TeleFit V (consN ts ρ) M more r →
      TeleFit V ρ Sa (ts ++ more) r := by
  intro ts
  induction ts with
  | nil =>
    intro ρ Ta Sa Γ Δ R M rest more r _ hS _ _ hmore
    cases hS
    exact hmore
  | cons t tsr ih =>
    intro ρ Ta Sa Γ Δ R M rest more r hT hS hdoms hfit hmore
    obtain ⟨u₁, v₁, A₁, B₁, Γ', rfl, hΓ, hT'⟩ := hT.succ_inv
    obtain ⟨u₂, v₂, A₂, B₂, Δ', rfl, hΔ, hS'⟩ := hS.succ_inv
    have hΓl : Γ'.length = tsr.length := hT'.length
    have hΔl : Δ'.length = tsr.length := hS'.length
    cases hfit with
    | @cons _ _ _ _ _ _ _ _ ht hfit' =>
      refine TeleFit.cons ?_ (ih hT' hS' ?_ hfit' hmore)
      · have h := hdoms tsr.length (by simp) ρ
        rw [hΓ, hΔ, List.getD, List.getD,
          List.getElem?_append_right (by omega),
          List.getElem?_append_right (by omega), hΓl, hΔl,
          Nat.sub_self] at h
        simp only [List.getElem?_cons_zero, Option.getD_some] at h
        rw [← h]
        exact ht
      · intro i hi σ
        have h := hdoms i (by simp only [List.length_cons]; omega) σ
        rwa [hΓ, hΔ, List.getD, List.getD,
          List.getElem?_append_left (by omega),
          List.getElem?_append_left (by omega)] at h

/-- The residual of a fitted telescope is graded, at the environment
the fit ends in. -/
theorem teleFit_wellDenotedV_residual :
    ∀ (ts : List V) {ρ : Nat → V} {Ta : AnnotTerm} {Γ : List AnnotTerm}
      {R : AnnotTerm} {rest : V},
      PiTeleAV ts.length Ta Γ R → WellDenotedV V ρ Ta →
      TeleFit V ρ Ta ts rest → WellDenotedV V (consN ts ρ) R := by
  intro ts
  induction ts with
  | nil =>
    intro ρ Ta Γ R rest hT hok _
    cases hT
    exact hok
  | cons t tsr ih =>
    intro ρ Ta Γ R rest hT hok hfit
    obtain ⟨u, v, A, B, Γ', rfl, hΓ, hT'⟩ := hT.succ_inv
    cases hfit with
    | @cons _ _ _ _ _ _ _ _ ht hfit' =>
      refine ih hT' ⟨?_, ?_⟩ hfit'
      · exact ((WellDenoted_pi V ρ u v A B) ▸ hok.1).2 t ht
      · exact ((AnnotValid_pi V ρ u v A B) ▸ hok.2).2.1 t ht

/-! ## The opened parameter spine

Every capability statement pins its type slot to the model former
applied to the telescope's parameters, and the *same* opened spine
appears at three depths (the η/unit statements' member binders and the
equation's type slot).  These two lemmas read it and evaluate it once
and for all, with the depth carried as an offset `m`. -/

/-- The canonical opener, read: `openFvars j k` denotes to the
descending bound variables at depth `d`. -/
theorem denoteMetaSpine_openFvars :
    ∀ (k j d : Nat), j + k ≤ d →
      DenoteMetaSpine acval env φ d (openFvars j k)
        ((List.range k).map fun q => AnnotTerm.bvar (d - 1 - (j + q))) := by
  intro k
  induction k with
  | zero => intro j d _; exact DenoteMetaSpine.nil
  | succ k ih =>
    intro j d hd
    have hlist : ((List.range (k + 1)).map fun q =>
          (AnnotTerm.bvar (d - 1 - (j + q)) : AnnotTerm))
        = AnnotTerm.bvar (d - 1 - j)
            :: ((List.range k).map fun q =>
              (AnnotTerm.bvar (d - 1 - (j + 1 + q)) : AnnotTerm)) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      refine congrArg (fun l => (AnnotTerm.bvar (d - 1 - (j + 0)) : AnnotTerm) :: l)
        (List.map_congr_left fun q _ => ?_)
      dsimp only [Function.comp]
      congr 1
      omega
    rw [show openFvars j (k + 1)
      = ConLeche.Expr.fvar j (.sort .zero)
        :: openFvars (j + 1) k from rfl, hlist]
    exact DenoteMetaSpine.cons
      (denoteMeta_fvar acval d j (.sort .zero))
      (ih (j + 1) d (by omega))

/-- The opened parameter spine, evaluated: it applies the head to the
fit's own arguments, at every one of the three depths. -/
theorem interp_bvarSpine :
    ∀ (ts : List V) {ρ σ : Nat → V} {K : AnnotTerm} (g : Nat → Nat),
      (∀ q, q < ts.length → σ (g q) = consN ts ρ (ts.length - 1 - q)) →
      interp V σ K = interp V ρ K →
      interp V σ (AnnotTerm.mkAppN K
          ((List.range ts.length).map fun q => AnnotTerm.bvar (g q)))
        = ts.foldl SetTheory.app (interp V ρ K) := by
  intro ts ρ σ K g hσ hK
  have hmap : ((List.range ts.length).map fun q =>
      (AnnotTerm.bvar (g q) : AnnotTerm)).map (interp V σ) = ts := by
    refine List.ext_getElem (by simp) ?_
    intro q h1 h2
    have hq : q < ts.length := by simpa using h1
    rw [List.getElem_map, List.getElem_map, List.getElem_range,
      interp_bvar, hσ q hq]
    have := consN_getElem? ts ρ (ts.length - 1 - q) (by omega)
    rw [show ts.length - 1 - (ts.length - 1 - q) = q from by omega,
      List.getElem?_eq_getElem hq] at this
    exact (Option.some.inj this).symm
  rw [interp_mkAppN, hK,
    show ∀ (as : List AnnotTerm) (b : V),
      as.foldl (fun r a => SetTheory.app r (interp V σ a)) b
        = (as.map (interp V σ)).foldl SetTheory.app b from by
      intro as
      induction as with
      | nil => intro b; rfl
      | cons a asr ihas => intro b; simpa using ihas _,
    hmap]

end ConLeche.Model
