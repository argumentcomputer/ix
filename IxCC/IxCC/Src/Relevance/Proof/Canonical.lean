import IxCC.Src.Relevance.Proof.Sound

/-! # L1: the relevance checks' facts as propositions

`Proof.Sound` gives the tier-S facts of `Relevance.check` (`check_sound`). This module gives the
rest of what the verifier's relevance checks decide, as propositions (PLAN-2 §4.3's L1):

* **(a) Tier C**, `check_soundC`. `TermC` beside `TermS`: what the walk `Check.term` decides at
  each relevant position, at the instance's profile: C0 (a binder or `let` written erased is
  irrelevant), C1 (a variable at a relevant position is bound at a binder relevant at the
  instance), C2 (at a constant head against the callee's parameter classes at the callee's
  profile, at a β-redex against the λ binders), C3 (each minor of a saturated eliminator against
  the constructor whose fields it receives, paired as `Check.elimShape?` pairs them: at a recursor
  each rule with the minor it dispatches, `elimShape_recr_minors`; an eliminator with a rule for a
  constructor that writes a field erased occurs only at a saturated spine; a projection reads no field
  dropped at every instance), C4 (an irrelevant major only at a subsingleton or empty eliminator),
  C5 (a constant at a relevant position has a relevant result) and C7 (no sort or Π at a relevant
  position: `TermC` has no case for one). `WellAnnotatedC` adds them at every reached instance to
  `WellAnnotated`.
* **(b) `checkCanonical_sound`**: from `checkCanonical p ann ch = []`, the canonical constant and
  constructor records, the header agreement of every run body and `csimp` redirect, the special
  heads' reads, the forwarding clause on recursor rules, no `csimp` redirect to an eliminator
  over a field written erased, and canonical tags on every reached
  runtime term; the structure the kernel ensures (no constant at or above the program's size,
  rule `j` of a reached eliminator's recursor for constructor `j`, universe-argument counts, a
  record for every reached constructor, F3's field count, `Fin.mk`'s proof field dropped where a
  word entry is reached); then the three facts about positions written erased that relevance
  preservation consumes (`param_erased_irr`, `field_erased_dropped`, `arg_erased_irr`).

Not here, and not yet a theorem: that the evaluator never yields the irrelevance marker at a
position that is read (relevance preservation, P1). These are the checks' facts only.

Every statement names whether a position is *written erased* only through `writtenErased` (a
binder), `letWrittenErased` (a `let`), `Check.Canonical.erasedParams` (a telescope) and
`Check.fieldWrittenErased` (a constructor field); when modes are read from records these change
accessor and the statements do not change. `KernelFront.erasedAt` (the annotator's) is not used:
the checks recompute from the program. -/

set_option autoImplicit false

namespace IxCC.Src.Relevance.Proof

open Check Check.Canonical

/-! ## Written erased: the accessors that move at the format change -/

/-- A binder written erased (`0`). -/
abbrev writtenErased (b : Binder) : Bool := b.contract.uses == .erased

/-- A `let` written erased. -/
abbrev letWrittenErased (c : Ixon.V3.LetContract) : Bool := c.binder.uses == .erased

/-! ## (a) Tier C at one term -/

/-- C2 at a constant head (`Check.paramArgs`): over the leading arguments and the callee's
parameter classes at the callee's profile `q`, an argument is irrelevant at the instance exactly
when its parameter is. -/
def ParamsC (prof q : Profile) : List Term.Arg → List Rel → Prop
  | (_, _, a) :: args, r :: params => r.irrP q = a.irrP prof ∧ ParamsC prof q args params
  | _, _ => True

/-- C2 at a β-redex (`Check.lamHead`): each argument against the λ binder it meets, at the
instance's profile. -/
def BetaC (prof : Profile) (args : List Term.Arg) (binders : List Rel) : Prop :=
  ∀ (i : Nat) (a : Term.Arg) (r : Rel), args[i]? = some a → binders[i]? = some r → r.irrP prof = a.2.2.irrP prof

/-- C3 at one minor (`Check.minorBinders`): its leading binders `bs` against the fields of
constructor `k` (classes `fields`, decided at the constructor's profile `qc`): a field dropped
there is bound by a binder irrelevant at the instance, and the binders cover every field written
erased. -/
def MinorC (p : Program) (prof qc : Profile) (k : CId) (bs : List Rel) (fields : List FieldClass) :
    Prop :=
  (∀ (i : Nat) (b : Rel) (cls : FieldClass), bs[i]? = some b → fields[i]? = some cls →
      cls.dropP qc = true → b.irrP prof = true) ∧
  (∀ i, i < fields.length → bs.length ≤ i → fieldWrittenErased p k i = false)

/-- C4 and C3 at an eliminator spine (`Check.knownHead`). Shorter than the eliminator's arity, the
eliminator has no rule for a constructor that writes a field erased (`Check.erasedMinors`;
`Check.partialElim`). Saturated, the minors are paired as `Check.elimShape?` pairs them: at a
`case` entry minor `j` with constructor `j`; at a recursor each rule with the minor it dispatches
(`Check.ruleDispatch`; `elimShape_recr_minors` below). -/
def ElimC (p : Program) (ann : Ann) (prof : Profile) (c : CId) (us : List Ixon.Univ)
    (args : List Term.Arg) : Prop :=
  ∀ shape, elimShape? p c = some shape →
    (args.length < shape.arity → erasedMinors p shape = false) ∧
    (shape.arity ≤ args.length →
      (∀ a : Term.Arg, args[shape.major]? = some a → a.2.2.irrP prof = true →
        (((p.table.recKindOf shape.recr).map (fun k => RecKind.atProfile (prof.inst us) k)).getD
          .ordinary).allowsIrrMajor = true) ∧
      (∀ pos j rule, (pos, j, rule) ∈ shape.minors →
        ∀ (minor : Term) (m : Mode) (a : Rel) (k : CId) (fields : List FieldClass),
          args[pos]? = some (minor, m, a) → ruleCtorFields p ann shape.recr rule = some (k, fields) →
          a.irrP prof = false →
          MinorC p prof (ctorProfile p shape.recr (prof.inst us)) k (lamRels minor) fields))

/-- The tier-C facts at an application spine's head (`Check.appRule`). -/
def HeadC (p : Program) (ann : Ann) (prof : Profile) : Term → List Term.Arg → Prop
  | .const c us, args =>
    (∀ rel, ann.constRel? c = some rel → ParamsC prof (prof.inst us) args rel.params) ∧
      ElimC p ann prof c us args
  | .lam b d t, args => BetaC prof args (lamRels (.lam b d t))
  | _, _ => True

mutual

/-- The tier-C facts over the relevant positions of a term at an instance of profile `prof`, under
binder classes `bs` (innermost first), as `Check.term` visits them (beside `TermS`). -/
inductive TermC (p : Program) (ann : Ann) (prof : Profile) : List Rel → Term → Prop
  /-- C1. -/
  | var {bs : List Rel} {i : Nat} :
      (∀ r, bs[i]? = some r → r.irrP prof = false) → TermC p ann prof bs (.var i)
  /-- C5, and C3 at a bare eliminator (`Check.bareHead`). -/
  | const {bs : List Rel} {c : CId} {us : List Ixon.Univ} :
      (∀ rel, ann.constRel? c = some rel → rel.result.irrP (prof.inst us) = false) →
      (∀ shape, elimShape? p c = some shape → erasedMinors p shape = false) →
      TermC p ann prof bs (.const c us)
  /-- C0 at a λ (C6 is `TermS.lam`'s). -/
  | lam {bs : List Rel} {b : Binder} {d t : Term} :
      (writtenErased b = true → b.rel.irrP prof = true) →
      TermC p ann prof (b.rel :: bs) t → TermC p ann prof bs (.lam b d t)
  /-- C0 at a `let`. -/
  | letE {bs : List Rel} {c : Ixon.V3.LetContract} {r : Rel} {ty v b : Term} :
      (letWrittenErased c = true → r.irrP prof = true) →
      (r.irrP prof = false → TermC p ann prof bs v) →
      TermC p ann prof (r :: bs) b → TermC p ann prof bs (.letE c r ty v b)
  /-- C3 at a projection. -/
  | proj {bs : List Rel} {s i : Nat} {e : Term} :
      (∀ k rel cls, onlyCtor? p s = some k → ann.ctorRel? k = some rel → rel.fields[i]? = some cls →
        cls.alwaysDropped = false) →
      TermC p ann prof bs e → TermC p ann prof bs (.proj s i e)
  /-- C2, C3, C4 at the spine's head. -/
  | app {bs : List Rel} {f a : Term} {m : Mode} {r : Rel} :
      HeadC p ann prof (Term.app f a m r).spineL.1 (Term.app f a m r).spineL.2 →
      SpineC p ann prof bs f → (r.irrP prof = false → TermC p ann prof bs a) →
      TermC p ann prof bs (.app f a m r)
  -- No case for a sort or a Π (C7).
  | natLit {bs : List Rel} {n : Nat} : TermC p ann prof bs (.natLit n)
  | strLit {bs : List Rel} {s : String} : TermC p ann prof bs (.strLit s)

/-- The same facts over the rest of an application spine (`Check.rest`): a constant head has C5
(its spine's facts are `HeadC`'s), any other head its term's facts. -/
inductive SpineC (p : Program) (ann : Ann) (prof : Profile) : List Rel → Term → Prop
  | app {bs : List Rel} {f a : Term} {m : Mode} {r : Rel} :
      SpineC p ann prof bs f → (r.irrP prof = false → TermC p ann prof bs a) →
      SpineC p ann prof bs (.app f a m r)
  | const {bs : List Rel} {c : CId} {us : List Ixon.Univ} :
      (∀ rel, ann.constRel? c = some rel → rel.result.irrP (prof.inst us) = false) →
      SpineC p ann prof bs (.const c us)
  | head {bs : List Rel} {t : Term} : (∀ f a m r, t ≠ .app f a m r) → (∀ c us, t ≠ .const c us) →
      TermC p ann prof bs t → SpineC p ann prof bs t

end


/-! ### The walk's rules, one at a time -/

section Rules

variable (ctx : Ctx)

private theorem varRule_nilC (bs : List Rel) (errs : List RelError) (i : Nat)
    (e : varRule ctx bs errs i = []) : ∀ r, bs[i]? = some r → r.irrP ctx.prof = false := by
  intro r hr
  unfold varRule at e
  rw [hr] at e
  dsimp only at e
  split at e
  · cases e
  · next h => simpa using h

private theorem constHead_nilC (c : CId) (us : List Ixon.Univ) (errs : List RelError)
    (e : constHead ctx c us errs = []) :
    ∀ rel, ctx.ann.constRel? c = some rel → rel.result.irrP (ctx.prof.inst us) = false := by
  intro rel hr
  unfold constHead at e
  rw [hr] at e
  dsimp only at e
  split at e
  · cases e
  · next h => simpa using h

private theorem lamRule_nilC (errs : List RelError) (b : Binder) (e : (lamRule ctx errs b).1 = []) :
    writtenErased b = true → b.rel.irrP ctx.prof = true := by
  intro hw
  cases hi' : b.rel.irrP ctx.prof with
  | true => rfl
  | false =>
    exfalso
    unfold lamRule at e
    dsimp only at e
    have h2 : (b.contract.uses == .erased && !b.rel.irrP ctx.prof) = true := by
      rw [hi']; simpa [writtenErased] using hw
    simp only [h2, ↓reduceIte] at e
    split at e <;> simp at e

private theorem letRule_nilC (errs : List RelError) (c : Ixon.V3.LetContract) (r : Rel)
    (e : letRule ctx errs c r = []) : letWrittenErased c = true → r.irrP ctx.prof = true := by
  intro hw
  cases hi' : r.irrP ctx.prof with
  | true => rfl
  | false =>
    exfalso
    unfold letRule at e
    dsimp only at e
    have h2 : (c.binder.uses == .erased && !r.irrP ctx.prof) = true := by
      rw [hi']; simpa [letWrittenErased] using hw
    simp only [h2, ↓reduceIte] at e
    cases e

private theorem projRule_nilC (errs : List RelError) (s i : Nat) (e : projRule ctx errs s i = []) :
    ∀ k rel cls, onlyCtor? ctx.p s = some k → ctx.ann.ctorRel? k = some rel →
      rel.fields[i]? = some cls → cls.alwaysDropped = false := by
  intro k rel cls hk hrel hcls
  unfold projRule at e
  rw [hk] at e
  dsimp only at e
  rw [hrel] at e
  dsimp only at e
  rw [hcls] at e
  dsimp only at e
  split at e
  · cases e
  · next h => simpa using h

private theorem paramArgs_nilC (c : CId) (q : Profile) :
    ∀ (args : List Term.Arg) (params : List Rel) (errs : List RelError),
      paramArgs ctx c q args params errs = [] → ParamsC ctx.prof q args params
  | (x, m, a) :: args, r :: params, errs, e => by
    simp only [paramArgs] at e
    refine ⟨?_, paramArgs_nilC c q args params _ e⟩
    have h := (adds_paramArgs ctx c q args params).nil e
    cases hr : r.irrP q <;> cases ha : a.irrP ctx.prof <;> simp_all
  | [], _, _, _ => trivial
  | _ :: _, [], _, _ => trivial

private theorem mem_zip_of_getElem? {α β : Type} :
    ∀ {l₁ : List α} {l₂ : List β} {i : Nat} {a : α} {b : β},
      l₁[i]? = some a → l₂[i]? = some b → (a, b) ∈ l₁.zip l₂
  | _ :: _, _ :: _, 0, _, _, h₁, h₂ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h₁ h₂
    subst h₁ h₂
    rw [List.zip_cons_cons]
    exact List.mem_cons_self
  | _ :: _, _ :: _, _ + 1, _, _, h₁, h₂ => by
    simp only [List.getElem?_cons_succ] at h₁ h₂
    rw [List.zip_cons_cons]
    exact List.mem_cons_of_mem _ (mem_zip_of_getElem? h₁ h₂)
  | [], _, _, _, _, h₁, _ => by simp at h₁
  | _ :: _, [], _, _, _, _, h₂ => by simp at h₂

private theorem lamHead_nilC (errs : List RelError) (head : Term) (args : List Term.Arg)
    (e : lamHead ctx errs head args = []) : BetaC ctx.prof args (lamRels head) := by
  unfold lamHead at e
  dsimp only at e
  obtain ⟨-, h⟩ := foldl_nil
    (P := fun (x : Term.Arg × Rel) => x.2.irrP ctx.prof = x.1.2.2.irrP ctx.prof)
    (fun errs x e => by
      obtain ⟨⟨_, _, a⟩, r⟩ := x
      dsimp only at e ⊢
      cases hr : r.irrP ctx.prof <;> cases ha : a.irrP ctx.prof <;> simp_all) _ _ e
  intro i a r ha hr
  exact h (a, r) (mem_zip_of_getElem? ha hr)

private theorem minorBinders_nilC (k : CId) (j : Nat) (qc : Profile) :
    ∀ (i : Nat) (bs : List Rel) (fields : List FieldClass) (errs : List RelError),
      minorBinders ctx k j qc i bs fields errs = [] →
      (∀ (n : Nat) (b : Rel) (cls : FieldClass), bs[n]? = some b → fields[n]? = some cls →
        cls.dropP qc = true → b.irrP ctx.prof = true) ∧
      (∀ n, n < fields.length → bs.length ≤ n → fieldWrittenErased ctx.p k (i + n) = false)
  | i, b :: bs, cls :: fields, errs, e => by
    simp only [minorBinders] at e
    obtain ⟨h₁, h₂⟩ := minorBinders_nilC k j qc (i + 1) bs fields _ e
    have h := (adds_minorBinders ctx k j qc (i + 1) bs fields).nil e
    refine ⟨fun n b' cls' hb hc hd => ?_, fun n hn hl => ?_⟩
    · cases n with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hb hc
        rw [← hb]
        rw [← hc] at hd
        cases hbi : b.irrP ctx.prof
        · simp [hd, hbi] at h
        · rfl
      | succ n => exact h₁ n b' cls' (by simpa using hb) (by simpa using hc) hd
    · cases n with
      | zero => simp at hl
      | succ n =>
        have := h₂ n (by simpa using hn) (by simpa using hl)
        rwa [show i + 1 + n = i + (n + 1) by omega] at this
  | i, [], cls :: fields, errs, e => by
    simp only [minorBinders] at e
    split at e
    · cases e
    · next hw =>
      obtain ⟨-, h₂⟩ := minorBinders_nilC k j qc (i + 1) [] fields _ e
      refine ⟨fun n b _ hb => by simp at hb, fun n hn _ => ?_⟩
      cases n with
      | zero => simpa using hw
      | succ n =>
        have := h₂ n (by simpa using hn) (by simp)
        rwa [show i + 1 + n = i + (n + 1) by omega] at this
  | _, [], [], _, _ => ⟨fun _ _ _ hb => by simp at hb, fun _ hn _ => by simp at hn⟩
  | _, _ :: _, [], _, _ => ⟨fun _ _ _ _ hc => by simp at hc, fun _ hn _ => by simp at hn⟩

private theorem partialElim_nilC (shape : ElimShape) (errs : List RelError)
    (e : partialElim ctx shape errs = []) : errs = [] ∧ erasedMinors ctx.p shape = false := by
  unfold partialElim at e
  split at e
  · cases e
  · next h => exact ⟨e, by simpa using h⟩

private theorem bareHead_nilC (c : CId) (us : List Ixon.Univ) (errs : List RelError)
    (e : bareHead ctx c us errs = []) :
    ∀ shape, elimShape? ctx.p c = some shape → erasedMinors ctx.p shape = false := by
  intro shape hs
  unfold bareHead at e
  rw [hs] at e
  exact (partialElim_nilC ctx shape _ e).2

private theorem knownHead_nilC (errs : List RelError) (c : CId) (us : List Ixon.Univ)
    (args : List Term.Arg) (e : knownHead ctx errs c us args = []) :
    (∀ rel, ctx.ann.constRel? c = some rel →
      ParamsC ctx.prof (ctx.prof.inst us) args rel.params) ∧
      ElimC ctx.p ctx.ann ctx.prof c us args := by
  unfold knownHead at e
  dsimp only at e
  have htail : ∀ E : List RelError, (match elimShape? ctx.p c with
      | none => E
      | some shape =>
        if args.length < shape.arity then partialElim ctx shape E else
        (shape.minors.foldl (init := match args[shape.major]? with
          | some (_, _, a) =>
            if a.irrP ctx.prof &&
                !(((ctx.p.table.recKindOf shape.recr).map
                  (fun k => RecKind.atProfile (ctx.prof.inst us) k)).getD .ordinary).allowsIrrMajor
            then err ctx "C4" "an ordinary eliminator with an irrelevant major" (some shape.recr) :: E
            else E
          | none => E) fun errs (pos, j, rule) =>
          match args[pos]?, ruleCtorFields ctx.p ctx.ann shape.recr rule with
          | some (minor, _, a), some (k, fields) =>
            if a.irrP ctx.prof then errs
            else minorBinders ctx k j (ctorProfile ctx.p shape.recr (ctx.prof.inst us)) 0
              (lamRels minor) fields errs
          | _, _ => errs)) = [] → E = [] ∧ ElimC ctx.p ctx.ann ctx.prof c us args := by
    intro E hE
    generalize hs : elimShape? ctx.p c = os at hE
    cases os with
    | none =>
      exact ⟨hE, fun shape h => by rw [hs] at h; cases h⟩
    | some shape =>
      dsimp only at hE
      by_cases har : args.length < shape.arity
      · simp only [har, ↓reduceIte] at hE
        obtain ⟨hE', hpe⟩ := partialElim_nilC ctx shape E hE
        exact ⟨hE', fun shape' hs' => by
          rw [hs] at hs'
          cases hs'
          exact ⟨fun _ => hpe, fun har' => absurd har' (by omega)⟩⟩
      · simp only [har, ↓reduceIte] at hE
        obtain ⟨h₁, h₂⟩ := foldl_nil (P := fun (x : Nat × Nat × Nat) =>
            ∀ (minor : Term) (m : Mode) (a : Rel) (k : CId) (fields : List FieldClass),
              args[x.1]? = some (minor, m, a) →
              ruleCtorFields ctx.p ctx.ann shape.recr x.2.2 = some (k, fields) →
              a.irrP ctx.prof = false →
              MinorC ctx.p ctx.prof (ctorProfile ctx.p shape.recr (ctx.prof.inst us)) k
                (lamRels minor) fields)
          (fun errs x e => by
            obtain ⟨pos, j, rule⟩ := x
            dsimp only at e ⊢
            cases hp : args[pos]? with
            | none =>
              rw [hp] at e
              exact ⟨e, fun _ _ _ _ _ h => by cases h⟩
            | some arg =>
              obtain ⟨minor, m, a⟩ := arg
              cases hr : ruleCtorFields ctx.p ctx.ann shape.recr rule with
              | none =>
                rw [hp, hr] at e
                exact ⟨e, fun _ _ _ _ _ _ h => by cases h⟩
              | some kf =>
                obtain ⟨k, fields⟩ := kf
                rw [hp, hr] at e
                dsimp only at e
                by_cases ha : a.irrP ctx.prof = true
                · simp only [ha, ↓reduceIte] at e
                  refine ⟨e, fun minor' m' a' k' fields' hp' _ ha' => ?_⟩
                  cases hp'
                  rw [ha] at ha'
                  cases ha'
                · simp only [ha, Bool.false_eq_true, ↓reduceIte] at e
                  obtain ⟨h₁, h₂⟩ := minorBinders_nilC ctx k j _ 0 (lamRels minor) fields errs e
                  refine ⟨(adds_minorBinders ctx k j _ 0 (lamRels minor) fields).nil e,
                    fun minor' m' a' k' fields' hp' hr' _ => ?_⟩
                  cases hp'
                  cases hr'
                  exact ⟨h₁, fun n hn hl => by simpa using h₂ n hn hl⟩)
          shape.minors _ hE
        refine ⟨?_, fun shape' hs' => ?_⟩
        · cases hm : args[shape.major]? with
          | none => rw [hm] at h₁; exact h₁
          | some x =>
            obtain ⟨_, _, a⟩ := x
            rw [hm] at h₁
            dsimp only at h₁
            split at h₁
            · cases h₁
            · exact h₁
        · rw [hs] at hs'
          cases hs'
          refine ⟨fun h => absurd h har, fun _ => ⟨fun a ha hirr => ?_,
            fun pos j rule hmem minor m a k fields hpos hrc hrel =>
              h₂ (pos, j, rule) hmem minor m a k fields hpos hrc hrel⟩⟩
          rw [ha] at h₁
          obtain ⟨_, _, a⟩ := a
          dsimp only at h₁ hirr
          cases hk : (((ctx.p.table.recKindOf shape.recr).map
              (fun k => RecKind.atProfile (ctx.prof.inst us) k)).getD .ordinary).allowsIrrMajor
          · simp [hirr, hk] at h₁
          · rfl
  obtain ⟨hE2, hElim⟩ := htail _ e
  refine ⟨fun rel hrel => ?_, hElim⟩
  have hE1 : (match ctx.ann.constRel? c with
      | some rel => paramArgs ctx c (ctx.prof.inst us) args rel.params errs
      | none => errs) = [] := by
    cases hd : ctx.p.decl? c with
    | none => simp only [hd] at hE2; exact hE2
    | some d =>
      cases d with
      | ctor sf lv ind cidx np nf ty =>
        cases hr : ctx.ann.ctorRel? c with
        | none => simp only [hd, hr] at hE2; cases hE2
        | some rel' =>
          simp only [hd, hr] at hE2
          exact (adds_fieldArgs ctx c _ 0 _ _).nil hE2
      | _ => simp only [hd] at hE2; exact hE2
  rw [hrel] at hE1
  exact paramArgs_nilC ctx c _ args rel.params errs hE1

private theorem appRule_nilC (errs : List RelError) (t : Term) (r : Rel)
    (e : appRule ctx errs t r = []) : HeadC ctx.p ctx.ann ctx.prof t.spineL.1 t.spineL.2 := by
  unfold appRule at e
  generalize t.spineL = sp at e ⊢
  obtain ⟨hd, args⟩ := sp
  dsimp only at e ⊢
  have hE := (argRule_nil ctx _ r e).1
  cases hd with
  | const c us => exact knownHead_nilC ctx _ _ _ _ hE
  | lam b d body => exact lamHead_nilC ctx _ _ _ hE
  | _ => trivial

end Rules

/-! ### The walk -/

section Walk

variable (ctx : Ctx)

mutual

private theorem term_nilC' : ∀ (bs : List Rel) (errs : List RelError) (t : Term),
    term ctx bs errs t = [] → TermC ctx.p ctx.ann ctx.prof bs t
  | bs, errs, .var i, e => by
    unfold term at e
    exact .var (varRule_nilC ctx bs errs i e)
  | bs, errs, .const c us, e => by
    unfold term at e
    exact .const (constHead_nilC ctx c us errs (bareHead_constHead ctx c us errs e))
      (bareHead_nilC ctx c us errs e)
  | bs, errs, .lam b d t, e => by
    unfold term at e
    rcases hl : lamRule ctx errs b with ⟨errs', enter⟩
    rw [hl] at e
    dsimp only at e
    cases enter with
    | true =>
      simp only [↓reduceIte] at e
      have h₁ := (term_nil ctx (b.rel :: bs) errs' t e).1
      exact .lam (lamRule_nilC ctx errs b (by rw [hl]; exact h₁)) (term_nilC' (b.rel :: bs) errs' t e)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at e
      have := (lamRule_nil ctx errs b (by rw [hl]; exact e)).2.2.2.2
      rw [hl] at this
      cases this
  | bs, errs, .letE c r ty v b, e => by
    unfold term at e
    dsimp only at e
    have hb := term_nilC' (r :: bs) _ b e
    have h₁ := (term_nil ctx (r :: bs) _ b e).1
    by_cases hr : r.irrP ctx.prof = true
    · simp only [hr, ↓reduceIte] at h₁
      exact .letE (letRule_nilC ctx errs c r h₁) (fun h => by rw [hr] at h; cases h) hb
    · simp only [hr, Bool.false_eq_true, ↓reduceIte] at h₁
      have hv := term_nilC' bs _ v h₁
      have h₃ := (term_nil ctx bs _ v h₁).1
      exact .letE (letRule_nilC ctx errs c r h₃) (fun _ => hv) hb
  | bs, errs, .proj s i e', e => by
    unfold term at e
    have h₁ := (term_nil ctx bs _ e' e).1
    exact .proj (projRule_nilC ctx errs s i h₁) (term_nilC' bs _ e' e)
  | bs, errs, .app f a m r, e => by
    unfold term at e
    dsimp only at e
    have hrest : ∀ E, rest ctx bs E f = [] → appRule ctx errs (.app f a m r) r = E →
        HeadC ctx.p ctx.ann ctx.prof (Term.app f a m r).spineL.1 (Term.app f a m r).spineL.2 ∧
          SpineC ctx.p ctx.ann ctx.prof bs f := fun E hE hE' => by
      have h₁ := (rest_nil ctx bs E f hE).1
      subst h₁
      exact ⟨appRule_nilC ctx errs _ r hE', rest_nilC' bs _ f hE⟩
    by_cases hr : r.irrP ctx.prof = true
    · simp only [hr, ↓reduceIte] at e
      obtain ⟨h₁, h₂⟩ := hrest _ e rfl
      exact .app h₁ h₂ fun h => by rw [hr] at h; cases h
    · simp only [hr, Bool.false_eq_true, ↓reduceIte] at e
      have ha := term_nilC' bs _ a e
      have h₅ := (term_nil ctx bs _ a e).1
      obtain ⟨h₁, h₂⟩ := hrest _ h₅ rfl
      exact .app h₁ h₂ fun _ => ha
  | bs, errs, .sort u, e => by unfold term sortRule at e; cases e
  | bs, errs, .pi b res d c, e => by unfold term sortRule at e; cases e
  | bs, errs, .natLit n, _ => .natLit
  | bs, errs, .strLit s, _ => .strLit

private theorem rest_nilC' : ∀ (bs : List Rel) (errs : List RelError) (t : Term),
    rest ctx bs errs t = [] → SpineC ctx.p ctx.ann ctx.prof bs t
  | bs, errs, .app f a m r, e => by
    unfold rest at e
    dsimp only at e
    by_cases hr : r.irrP ctx.prof = true
    · simp only [hr, ↓reduceIte] at e
      exact .app (rest_nilC' bs _ f e) fun h => by rw [hr] at h; cases h
    · simp only [hr, Bool.false_eq_true, ↓reduceIte] at e
      have ha := term_nilC' bs _ a e
      have h₅ := (term_nil ctx bs _ a e).1
      exact .app (rest_nilC' bs _ f h₅) fun _ => ha
  | bs, errs, .var i, e => by
    unfold rest at e
    exact .head (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h) (.var (varRule_nilC ctx bs errs i e))
  | bs, errs, .const c us, e => by
    unfold rest at e
    exact .const (constHead_nilC ctx c us errs e)
  | bs, errs, .lam b d t, e => by
    unfold rest at e
    rcases hl : lamRule ctx errs b with ⟨errs', enter⟩
    rw [hl] at e
    dsimp only at e
    cases enter with
    | true =>
      simp only [↓reduceIte] at e
      have h₁ := (term_nil ctx (b.rel :: bs) errs' t e).1
      exact .head (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
        (.lam (lamRule_nilC ctx errs b (by rw [hl]; exact h₁)) (term_nilC' (b.rel :: bs) errs' t e))
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at e
      have := (lamRule_nil ctx errs b (by rw [hl]; exact e)).2.2.2.2
      rw [hl] at this
      cases this
  | bs, errs, .letE c r ty v b, e => by
    unfold rest at e
    dsimp only at e
    have hb := term_nilC' (r :: bs) _ b e
    have h₁ := (term_nil ctx (r :: bs) _ b e).1
    by_cases hr : r.irrP ctx.prof = true
    · simp only [hr, ↓reduceIte] at h₁
      exact .head (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
        (.letE (letRule_nilC ctx errs c r h₁) (fun h => by rw [hr] at h; cases h) hb)
    · simp only [hr, Bool.false_eq_true, ↓reduceIte] at h₁
      have hv := term_nilC' bs _ v h₁
      have h₃ := (term_nil ctx bs _ v h₁).1
      exact .head (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h) (.letE (letRule_nilC ctx errs c r h₃) (fun _ => hv) hb)
  | bs, errs, .proj s i e', e => by
    unfold rest at e
    have h₁ := (term_nil ctx bs _ e' e).1
    exact .head (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h) (.proj (projRule_nilC ctx errs s i h₁) (term_nilC' bs _ e' e))
  | bs, errs, .sort u, e => by unfold rest sortRule at e; cases e
  | bs, errs, .pi b res d c, e => by unfold rest sortRule at e; cases e
  | bs, errs, .natLit n, _ => .head (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h) .natLit
  | bs, errs, .strLit s, _ => .head (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h) .strLit

end

end Walk

/-- The walk's tier-C facts: an empty error list after a term's walk. -/
theorem term_nilC (ctx : Ctx) (bs : List Rel) (errs : List RelError) (t : Term)
    (e : term ctx bs errs t = []) : TermC ctx.p ctx.ann ctx.prof bs t :=
  term_nilC' ctx bs errs t e

/-- The tier-C facts at one reached instance. -/
structure InstC (p : Program) (ann : Ann) (c : CId) (prof : Profile) : Prop where
  terms : ∀ key ∈ p.runtimeKeys c, ∀ t, p.termOf key = some t → TermC p ann prof [] t

/-- What `check` establishes, tiers S and C. -/
structure WellAnnotatedC (p : Program) (ann : Ann) (c : Checked) : Prop
    extends WellAnnotated p ann c where
  instsC : ∀ inst ∈ c.instances, InstC p ann inst.1 inst.2

theorem check_soundC {p : Program} {ann : Ann} {c : Checked} (h : check p ann = .ok c) :
    WellAnnotatedC p ann c :=
  { toWellAnnotated := check_sound h
    instsC := fun inst hi => ⟨check_instsQ (fun _ prof t => TermC p ann prof [] t)
      (fun _ _ _ _ _ e => ⟨(term_nil _ _ _ _ e).1, term_nilC _ _ _ _ e⟩) h inst hi⟩ }

/-- Membership in `zipIdx` from position `n`. -/
private theorem mem_zipIdx_iff {α : Type} : ∀ (l : List α) (n i : Nat) (x : α),
    (x, i) ∈ l.zipIdx n ↔ n ≤ i ∧ l[i - n]? = some x
  | [], n, i, x => by simp
  | y :: l, n, i, x => by
    rw [List.zipIdx_cons, List.mem_cons, mem_zipIdx_iff l (n + 1) i x, Prod.mk.injEq]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨h₁, h₂⟩)
      · simp
      · refine ⟨by omega, ?_⟩
        rw [show i - n = (i - (n + 1)) + 1 by omega]
        simpa using h₂
    · rintro ⟨h₁, h₂⟩
      by_cases h : i = n
      · subst h
        left
        simp at h₂
        exact ⟨h₂.symm, rfl⟩
      · right
        refine ⟨by omega, ?_⟩
        rw [show i - n = (i - (n + 1)) + 1 by omega] at h₂
        simpa using h₂

/-- The pairing C3 uses at a raw recursor: each rule with the minor it dispatches. -/
theorem elimShape_recr_minors {p : Program} {r : CId} {sf k : Bool}
    {lv np nmot nmin ni : Nat} {ind : CId} {rules : List Rule} {ty : Term}
    (hres : p.table.resolveOf r = none)
    (hd : p.decl? r = some (.recr sf k lv np nmot nmin ni ind rules ty)) :
    ∃ shape, elimShape? p r = some shape ∧ shape.recr = r ∧
      shape.major = np + nmot + nmin + ni ∧ shape.arity = np + nmot + nmin + ni + 1 ∧
      ∀ pos j kidx, (pos, j, kidx) ∈ shape.minors ↔
        ∃ rule, rules[kidx]? = some rule ∧ ruleDispatch p r rule = some j ∧ pos = np + nmot + j :=
  by
  refine ⟨{ recr := r
            minors := rules.zipIdx.filterMap fun (rule, k) =>
              (ruleDispatch p r rule).map fun j => (np + nmot + j, j, k)
            major := np + nmot + nmin + ni, arity := np + nmot + nmin + ni + 1 },
    ?_, rfl, rfl, rfl, ?_⟩
  · simp only [elimShape?, hres, hd]
  · intro pos j kidx
    rw [List.mem_filterMap]
    constructor
    · rintro ⟨⟨rule, k⟩, hmem, h⟩
      dsimp only at h
      cases hj : ruleDispatch p r rule with
      | none => rw [hj] at h; cases h
      | some j' =>
        rw [hj] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨rule, by simpa using ((mem_zipIdx_iff rules 0 k rule).1 hmem).2, hj, rfl⟩
    · rintro ⟨rule, hrule, hj, rfl⟩
      refine ⟨(rule, kidx), (mem_zipIdx_iff rules 0 kidx rule).2 ⟨Nat.zero_le _, by simpa using hrule⟩,
        ?_⟩
      dsimp only
      rw [hj]
      rfl

/-! ## (b) `checkCanonical` -/

/-- `headerAgreement ty t params = none`: `t`'s leading λs cover every parameter `ty` writes erased,
and each covered λ has its parameter's class. -/
def HeaderOk (ty t : Term) (params : List Rel) : Prop :=
  (∀ i ∈ erasedParams ty, i < (lamRels t).length) ∧
  ∀ (i : Nat) (b r : Rel), (lamRels t)[i]? = some b → params[i]? = some r → b = r

/-- `readsErased? p ann c = none`: the special head `c` runs as reads no parameter its type writes
erased. -/
def ReadsOk (p : Program) (ann : Ann) (c : CId) : Prop :=
  ∀ h d, specialHead? p c = some h → p.decl? c = some d →
    ∀ i ∈ erasedParams d.type, readsAt p ann c h i = false

/-- The field count SrcEval passes to rule `rule` (F2 applies the rule to the constructor value's
fields): its constructor's, or the rule's own where the constructor is not one. -/
def ctorFields (p : Program) (rule : Rule) : Nat :=
  match p.decl? rule.ctor with
  | some (.ctor _ _ _ _ _ nf _) => nf
  | _ => rule.fields

/-- `forwardsErased? p r = none`: every rule of the recursor `r` uses a field its constructor
writes erased only as that field's argument to the minor the rule dispatches; such a rule binds
as many fields as its constructor has. -/
def ForwardOk (p : Program) (r : CId) : Prop :=
  ∀ sf k lv np nmot nmin ni ind rules ty,
    p.decl? r = some (.recr sf k lv np nmot nmin ni ind rules ty) →
    ∀ (kidx : Nat) (rule : Rule), rules[kidx]? = some rule →
      ∀ i, i < ctorFields p rule → fieldWrittenErased p rule.ctor i = true →
        rule.fields = ctorFields p rule ∧
        ∃ body j, peelLamsN (np + nmot + nmin + rule.fields) rule.rhs = some body ∧
          ruleDispatch p r rule = some j ∧
          mentionsVar (rule.fields - 1 - i) body.spineL.1 = false ∧
          ∀ (n : Nat) (a : Term.Arg), body.spineL.2[n]? = some a →
            (n = i ∧ a.1 = .var (rule.fields - 1 - i)) ∨ mentionsVar (rule.fields - 1 - i) a.1 = false

/-- The canonical constant record of `c` (`checkCanonical`'s `okConsts`): its parameter classes
are its type's telescope classified, each tag agreeing (`tagOk`), its result class the
classification of its conclusion, and a primitive or word entry all relevant. -/
def ConstCanon (p : Program) (c : CId) (cr : ConstRel) : Prop :=
  ∃ d, p.decl? c = some d ∧
    (classifyTelescope p [] (d.type.piCount + 1) d.type).1.length = cr.params.length ∧
    (∀ (i : Nat) (actual : Rel) (b : Binder) (exp : Option Rel), cr.params[i]? = some actual →
      (classifyTelescope p [] (d.type.piCount + 1) d.type).1[i]? = some (b, exp) →
      tagOk b exp false actual = true) ∧
    cr.result = ((classifyTelescope p [] (d.type.piCount + 1) d.type).2.getD .rel) ∧
    (∀ op, p.table.resolveOf c = some (.prim op) →
      cr.result = .rel ∧ cr.params = List.replicate op.arity .rel) ∧
    (∀ w op thm, p.table.resolveOf c = some (.word w op thm) →
      cr.result = .rel ∧ cr.params = List.replicate op.arity .rel)

/-- The canonical constructor record of `c` (`okCtors`). -/
def CtorCanon (p : Program) (ann : Ann) (c : CId) (kr : CtorRel) : Prop :=
  ∃ sf lv ind cidx np nf ty, p.decl? c = some (.ctor sf lv ind cidx np nf ty) ∧
    kr.fields.length = nf ∧
    ((classifyTelescope p [] (ty.piCount + 1) ty).1.drop np).length = nf ∧
    (∀ cr, ann.constRel? c = some cr → (cr.params.drop np).map FieldClass.ofRel = kr.fields) ∧
    ∀ (i : Nat) (actual : FieldClass) (b : Binder) (exp : Option Rel), kr.fields[i]? = some actual →
      ((classifyTelescope p [] (ty.piCount + 1) ty).1.drop np)[i]? = some (b, exp) →
      actual ≠ .proof .never ∧
      (if writtenErased b then actual.alwaysDropped = true
       else actual = (match exp with | some e => FieldClass.ofRel e | none => .keep))

/-- `rulesShape? p r = none`: rule `j` of the recursor `r` is for constructor `j` of its inductive
and binds as many fields as that constructor has. -/
def RulesOk (p : Program) (r : CId) : Prop :=
  ∀ sf k lv np nmot nmin ni ind rules ty,
    p.decl? r = some (.recr sf k lv np nmot nmin ni ind rules ty) →
    ∀ (j : Nat) (rule : Rule), rules[j]? = some rule →
      ∃ sf' lv' np' ty', p.decl? rule.ctor = some (.ctor sf' lv' ind j np' rule.fields ty')

/-- What `checkCanonical p ann ch = []` establishes. -/
structure Canonical (p : Program) (ann : Ann) (ch : Checked) : Prop where
  consts : ∀ c cr, ann.constRel? c = some cr → ConstCanon p c cr
  ctors : ∀ c kr, ann.ctorRel? c = some kr → CtorCanon p ann c kr
  /-- A run body (a value, an equation's body) agrees with its constant's header. -/
  bodies : ∀ c ∈ ch.reached, ∀ cr d, ann.constRel? c = some cr → p.decl? c = some d →
    ∀ key t, (key, t) ∈ runBodies p c → HeaderOk d.type t cr.params
  /-- A `csimp` subject writes no parameter erased. -/
  csimp : ∀ c ∈ ch.reached, ∀ cr d g us thm, ann.constRel? c = some cr → p.decl? c = some d →
    p.table.resolveOf c = some (.csimp g us thm) → erasedParams d.type = []
  reads : ∀ c ∈ ch.reached, ReadsOk p ann c
  forwards : ∀ c ∈ ch.reached, ForwardOk p c
  /-- A `csimp` subject's target is no eliminator with a rule for a constructor that writes a
  field erased (`redirectsErased?`: its minors would meet no C3 check). -/
  redirects : ∀ c ∈ ch.reached, ∀ g us thm, p.table.resolveOf c = some (.csimp g us thm) →
    ∀ shape, elimShape? p g = some shape → erasedMinors p shape = false
  /-- Every reached constant has a record, and its run bodies' and rules' tags are canonical. -/
  reachedRecord : ∀ c ∈ ch.reached, (ann.constRel? c).isSome = true
  tags : ∀ c ∈ ch.reached,
    (∀ key t, (key, t) ∈ runBodies p c → checkTermBinders p ann [] t [] = true) ∧
    ∀ sf k lv np nmot nmin ni ind rules ty,
      p.decl? c = some (.recr sf k lv np nmot nmin ni ind rules ty) →
      ∀ rule ∈ rules, checkTermBinders p ann [] rule.rhs [] = true
  /-- No constant and no table entry at or above the program's size (the closure loop skips an
  instance there, `Handled`). -/
  dense : ∀ c, p.size ≤ c → p.entry? c = none ∧ p.table.resolveOf c = none
  /-- Rule `j` of a reached eliminator's recursor (a raw recursor's own, a `case` key's
  recursor's) is for constructor `j` of its inductive (`rulesShape?`; erasure's `ruleAlt`). -/
  rules : ∀ c ∈ ch.reached, ∀ shape, elimShape? p c = some shape → RulesOk p shape.recr
  /-- Universe-argument counts (`univsOk`) on a reached constant's runtime terms and on its
  `csimp` redirect's target (erasure's `erase-univs`). -/
  univs : ∀ c ∈ ch.reached,
    (∀ key ∈ p.runtimeKeys c, ∀ t, p.termOf key = some t → univsOk p t = true) ∧
    ∀ g us thm, p.table.resolveOf c = some (.csimp g us thm) → univsOk p (.const g us) = true
  /-- A reached constructor has a constructor record (unannotated, every field reads as kept). -/
  ctorRecords : ∀ c ∈ ch.reached, ∀ sf lv ind j np nf ty,
    p.decl? c = some (.ctor sf lv ind j np nf ty) → (ann.ctorRel? c).isSome = true
  /-- A reached subsingleton eliminator's field sources (F3) are as many as the fields of its
  rule 0's constructor (`subsingletonSrcs?`). -/
  subsingletonFields : ∀ c ∈ ch.reached, ∀ shape, elimShape? p c = some shape →
    ∀ sf k lv np nmot nmin ni ind rules ty w srcs rule,
      p.decl? shape.recr = some (.recr sf k lv np nmot nmin ni ind rules ty) →
      p.table.recKindOf shape.recr = some (.subsingleton w srcs) → rules[0]? = some rule →
      srcs.length = ctorFields p rule
  /-- Where a word entry is reached, the pinned `Fin.mk` drops its proof field at the empty
  profile (F6w builds a word's tower with `irr` there, `Program.mkWord?`). -/
  finProof : ∀ c ∈ ch.reached, ∀ w op thm, p.table.resolveOf c = some (.word w op thm) →
    ∀ fin, p.known.finMk = some fin → ch.keepsP fin [] 1 = false


/-! ### Helpers for `checkCanonical_sound` -/

/- The records' classes compare with their derived `BEq`; these make it lawful in this file only. -/

private theorem propWhen_lawfulBEq : LawfulBEq PropWhen where
  rfl := by
    intro a
    cases a with
    | never => rfl
    | allZero ps => show (ps == ps) = true; exact beq_self_eq_true ps
  eq_of_beq := by
    intro a b h
    cases a with
    | never => cases b with
      | never => rfl
      | allZero _ => cases h
    | allZero ps => cases b with
      | never => cases h
      | allZero qs => exact congrArg _ (beq_iff_eq.1 (show (ps == qs) = true from h))

attribute [local instance] propWhen_lawfulBEq

private theorem rel_lawfulBEq : LawfulBEq Rel where
  rfl := by
    intro a
    cases a with
    | rel => rfl
    | proof w => show (w == w) = true; exact beq_self_eq_true w
    | type => rfl
  eq_of_beq := by
    intro a b h
    cases a with
    | rel => cases b with
      | rel => rfl
      | proof _ => cases h
      | type => cases h
    | proof w => cases b with
      | rel => cases h
      | proof w' => exact congrArg _ (beq_iff_eq.1 (show (w == w') = true from h))
      | type => cases h
    | type => cases b with
      | rel => cases h
      | proof _ => cases h
      | type => rfl

attribute [local instance] rel_lawfulBEq

private theorem fieldClass_lawfulBEq : LawfulBEq FieldClass where
  rfl := by
    intro a
    cases a with
    | keep => rfl
    | proof w => show (w == w) = true; exact beq_self_eq_true w
    | type => rfl
  eq_of_beq := by
    intro a b h
    cases a with
    | keep => cases b with
      | keep => rfl
      | proof _ => cases h
      | type => cases h
    | proof w => cases b with
      | keep => cases h
      | proof w' => exact congrArg _ (beq_iff_eq.1 (show (w == w') = true from h))
      | type => cases h
    | type => cases b with
      | keep => cases h
      | proof _ => cases h
      | type => rfl

attribute [local instance] fieldClass_lawfulBEq



private theorem term_eq_var {a : Term} {v : Nat} (h : (a == Term.var v) = true) : a = .var v := by
  cases a with
  | var i => exact congrArg _ (beq_iff_eq.1 h)
  | _ => cases h

private theorem toList_nil {α : Type} {o : Option α} (h : o.toList = []) : o = none := by
  cases o with
  | none => rfl
  | some _ => simp at h

private theorem getElem?_zip_of {α β : Type} :
    ∀ {l₁ : List α} {l₂ : List β} {i : Nat} {a : α} {b : β},
      l₁[i]? = some a → l₂[i]? = some b → (l₁.zip l₂)[i]? = some (a, b)
  | _ :: _, _ :: _, 0, _, _, h₁, h₂ => by simp_all
  | _ :: _, _ :: _, _ + 1, _, _, h₁, h₂ => by
    simp only [List.getElem?_cons_succ, List.zip_cons_cons] at h₁ h₂ ⊢
    exact getElem?_zip_of h₁ h₂
  | [], _, _, _, _, h₁, _ => by simp at h₁
  | _ :: _, [], _, _, _, _, h₂ => by simp at h₂

private theorem headerOk_of_none {ty t : Term} {params : List Rel} {what : String}
    (h : headerAgreement ty t params what = none) : HeaderOk ty t params := by
  unfold headerAgreement at h
  dsimp only at h
  split at h
  · cases h
  · next hf =>
    split at h
    · cases h
    · next hg =>
      refine ⟨fun i hi => ?_, fun i b r hb hr => ?_⟩
      · have := List.find?_eq_none.1 hf i hi
        simpa using this
      · have := List.find?_eq_none.1 hg ((b, r), i)
          ((mem_zipIdx_iff _ 0 i (b, r)).2 ⟨Nat.zero_le _, by simpa using getElem?_zip_of hb hr⟩)
        simpa using this

theorem checkCanonical_sound {p : Program} {ann : Ann} {ch : Checked}
    (h : checkCanonical p ann ch = []) : Canonical p ann ch := by
  unfold checkCanonical at h
  dsimp only at h
  simp only [List.append_eq_nil_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hread, hfwd⟩, hred⟩, hhdr⟩, hdenseE⟩, hruleE⟩, hunivE⟩, hrecE⟩, hsrcsE⟩, hfinE⟩,
    hokE⟩ := h
  split at hokE
  · rename_i hall
    simp only [Bool.and_eq_true, List.all_eq_true] at hall
    obtain ⟨⟨hconsts, hctors⟩, hreached⟩ := hall
    have hhdr' := List.flatMap_eq_nil_iff.1 hhdr
    have hread' := List.filterMap_eq_nil_iff.1 hread
    have hfwd' := List.filterMap_eq_nil_iff.1 hfwd
    have hred' := List.filterMap_eq_nil_iff.1 hred
    have hruleE' := List.filterMap_eq_nil_iff.1 hruleE
    have hunivE' := List.flatMap_eq_nil_iff.1 hunivE
    have hrecE' := List.filterMap_eq_nil_iff.1 hrecE
    have hsrcsE' := List.filterMap_eq_nil_iff.1 hsrcsE
    have hfinE' := List.filterMap_eq_nil_iff.1 hfinE
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- the constant records
    · intro c cr hcr
      have hx := hconsts (c, cr) (NatMap.mem_toList hcr)
      dsimp only at hx
      cases hd : p.decl? c with
      | none => rw [hd] at hx; cases hx
      | some d =>
        rw [hd] at hx
        dsimp only at hx
        refine ⟨d, hd, ?_⟩
        generalize classifyTelescope p [] (d.type.piCount + 1) d.type = cl at hx ⊢
        obtain ⟨ps, res⟩ := cl
        dsimp only at hx ⊢
        simp only [Bool.and_eq_true] at hx
        obtain ⟨⟨⟨hprim, hlen⟩, hzip⟩, hres⟩ := hx
        refine ⟨(beq_iff_eq.1 hlen).symm, fun i actual b exp ha hp => ?_, ?_, fun op hop => ?_,
          fun w op thm hop => ?_⟩
        · exact List.all_eq_true.1 hzip (actual, (b, exp)) (mem_zip_of_getElem? ha hp)
        · cases res <;> simpa using hres
        · rw [hop] at hprim; simpa using hprim
        · rw [hop] at hprim; simpa using hprim
    -- the constructor records
    · intro c kr hkr
      have hx := hctors (c, kr) (NatMap.mem_toList hkr)
      dsimp only at hx
      cases hd : p.decl? c with
      | none => rw [hd] at hx; cases hx
      | some d =>
        cases d with
        | ctor sf lv ind cidx np nf ty =>
          rw [hd] at hx
          dsimp only at hx
          refine ⟨sf, lv, ind, cidx, np, nf, ty, hd, ?_⟩
          generalize classifyTelescope p [] (ty.piCount + 1) ty = cl at hx ⊢
          obtain ⟨ps, res⟩ := cl
          dsimp only at hx ⊢
          simp only [Bool.and_eq_true] at hx
          obtain ⟨⟨⟨hwc, hlen⟩, hflen⟩, hzip⟩ := hx
          refine ⟨beq_iff_eq.1 hlen, beq_iff_eq.1 hflen, fun cr hcr => ?_,
            fun i actual b exp ha hp => ?_⟩
          · rw [hcr] at hwc; simpa using hwc
          · have hf := List.all_eq_true.1 hzip (actual, (b, exp)) (mem_zip_of_getElem? ha hp)
            dsimp only at hf
            simp only [Bool.and_eq_true] at hf
            obtain ⟨hne, hif⟩ := hf
            refine ⟨by simpa using hne, ?_⟩
            split at hif <;> split
            · exact hif
            · contradiction
            · contradiction
            · cases exp <;> simpa using hif
        | _ => rw [hd] at hx; simp at hx
    -- run bodies agree with their headers
    · intro c hc cr d hcr hd key t hkt
      have h1 := hhdr' c hc
      rw [hcr, hd] at h1
      dsimp only at h1
      rw [List.append_eq_nil_iff] at h1
      have h2 := List.filterMap_eq_nil_iff.1 h1.2 (key, t) hkt
      dsimp only at h2
      exact headerOk_of_none (Option.map_eq_none_iff.1 h2)
    -- a csimp subject writes no parameter erased
    · intro c hc cr d g us thm hcr hd hres
      have h1 := hhdr' c hc
      rw [hcr, hd] at h1
      dsimp only at h1
      rw [List.append_eq_nil_iff] at h1
      have h2 := h1.1
      rw [hres] at h2
      dsimp only at h2
      have h3 := headerOk_of_none (toList_nil (List.map_eq_nil_iff.1 h2))
      exact List.eq_nil_iff_forall_not_mem.2 fun i hi => by
        have := h3.1 i hi
        simp [lamRels] at this
    -- special heads read no parameter written erased
    · intro c hc h d hh hd i hi
      have hn := Option.map_eq_none_iff.1 (hread' c hc)
      cases hf : (erasedParams d.type).find? (readsAt p ann c h) with
      | none => simpa using List.find?_eq_none.1 hf i hi
      | some j =>
        exfalso
        simp [readsErased?, hh, hd, hf] at hn
    -- the forwarding clause
    · intro c hc sf k lv np nmot nmin ni ind rules ty hd kidx rule hrule i hi hw
      have hn := Option.map_eq_none_iff.1 (hfwd' c hc)
      unfold forwardsErased? at hn
      rw [hd] at hn
      simp only [Option.bind_eq_bind, Option.bind_some] at hn
      have hg := List.findSome?_eq_none_iff.1 hn (rule, kidx)
        ((mem_zipIdx_iff rules 0 kidx rule).2 ⟨Nat.zero_le _, by simpa using hrule⟩)
      -- the field count `forwardsErased?` reads: one case per declaration of the rule's
      -- constructor, each running the same script
      generalize hD : p.decl? rule.ctor = D at hg
      rcases D with _ | (_ | _ | _ | _ | _ | _)
      all_goals
        simp only [ctorFields, hD] at hi
        dsimp only at hg
        split at hg
        · next heq =>
          exact absurd hw (by simpa using (List.filter_eq_nil_iff.1 heq) i (List.mem_range.2 hi))
        · next i₀ rest heq =>
          have hmem : i ∈ i₀ :: rest := by
            rw [← heq]
            exact List.mem_filter.2 ⟨List.mem_range.2 hi, hw⟩
          split at hg
          · cases hg
          · next hne =>
            have hne' := hne
            simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne'
            refine ⟨by simp only [ctorFields, hD] <;> exact hne'.symm, ?_⟩
            split at hg
            · next body j hpeel hdisp =>
              refine ⟨body, j, hpeel, hdisp, ?_⟩
              have hi' := List.findSome?_eq_none_iff.1 hg i hmem
              split at hi'
              · next hok =>
                simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hok
                obtain ⟨hh, hargs⟩ := hok
                refine ⟨hh, fun n a ha => ?_⟩
                have := hargs (a, n)
                  ((mem_zipIdx_iff _ 0 n a).2 ⟨Nat.zero_le _, by simpa using ha⟩)
                obtain ⟨a1, a2, a3⟩ := a
                simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at this
                rcases this with ⟨h1, h2⟩ | h3
                · exact Or.inl ⟨h1, term_eq_var h2⟩
                · exact Or.inr h3
              · cases hi'
            · cases hg
            · cases hg
    -- no csimp redirect to an eliminator whose minors C3 must see
    · intro c hc g us thm hres shape hs
      have hn := Option.map_eq_none_iff.1 (hred' c hc)
      unfold redirectsErased? at hn
      rw [hres] at hn
      dsimp only at hn
      rw [hs] at hn
      dsimp only at hn
      split at hn
      · cases hn
      · next hfalse => simpa using hfalse
    -- every reached constant has a record
    · intro c hc
      have hx := hreached c hc
      cases hcr : ann.constRel? c with
      | none => rw [hcr] at hx; cases hx
      | some _ => rfl
    -- canonical tags on run bodies and rules
    · intro c hc
      have hx := hreached c hc
      cases hcr : ann.constRel? c with
      | none => rw [hcr] at hx; cases hx
      | some cr =>
        rw [hcr] at hx
        dsimp only at hx
        simp only [Bool.and_eq_true, List.all_eq_true] at hx
        obtain ⟨hb, hr⟩ := hx
        refine ⟨fun key t hkt => hb (key, t) hkt,
          fun sf k lv np nmot nmin ni ind rules ty hd rule hrule => ?_⟩
        rw [hd] at hr
        exact hr rule.rhs (List.mem_map.2 ⟨rule, hrule, rfl⟩)
    -- no constant or table entry at or above the size
    · intro c hc
      split at hdenseE
      · next hd =>
        simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hd
        refine ⟨?_, ?_⟩
        · cases he : p.entry? c with
          | none => rfl
          | some e => exact absurd (hd.1 (c, e) (NatMap.mem_toList (m := p.consts) he)) (Nat.not_lt.2 hc)
        · cases hr : p.table.resolveOf c with
          | none => rfl
          | some e =>
            exact absurd (hd.2 (c, e) (NatMap.mem_toList (m := p.table.resolve) hr)) (Nat.not_lt.2 hc)
      · cases hdenseE
    -- rule `j` of a reached eliminator's recursor is for constructor `j`
    · intro c hc shape hs
      unfold RulesOk
      intro sf k lv np nmot nmin ni ind rules ty hd j rule hrule
      have h1 := hruleE' c hc
      rw [hs] at h1
      dsimp only at h1
      have hn := Option.map_eq_none_iff.1 h1
      unfold rulesShape? at hn
      rw [hd] at hn
      simp only [Option.bind_eq_bind, Option.bind_some] at hn
      have hg := List.findSome?_eq_none_iff.1 hn (rule, j)
        ((mem_zipIdx_iff rules 0 j rule).2 ⟨Nat.zero_le _, by simpa using hrule⟩)
      dsimp only at hg
      cases hD : p.decl? rule.ctor with
      | none => rw [hD] at hg; simp at hg
      | some d =>
        rw [hD] at hg
        cases d with
        | ctor sf' lv' ind' cidx np' nf ty' =>
          dsimp only at hg
          split at hg
          · next hok =>
            simp only [Bool.and_eq_true, beq_iff_eq] at hok
            obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hok
            exact ⟨sf', lv', np', ty', by rw [h₁, h₂, h₃]⟩
          · cases hg
        | _ => simp at hg
    -- universe-argument counts
    · intro c hc
      have h1 := hunivE' c hc
      unfold univsErrs at h1
      dsimp only at h1
      rw [List.append_eq_nil_iff] at h1
      refine ⟨fun key hk t ht => ?_, fun g us thm hres => ?_⟩
      · have h2 := List.filterMap_eq_nil_iff.1 h1.1 key hk
        rw [ht] at h2
        dsimp only at h2
        split at h2
        · next hok => exact hok
        · cases h2
      · have h2 := h1.2
        rw [hres] at h2
        dsimp only at h2
        split at h2
        · next hok => exact hok
        · cases h2
    -- a reached constructor has a record
    · intro c hc sf lv ind j np nf ty hd
      have h1 := hrecE' c hc
      rw [hd] at h1
      cases hk : ann.ctorRel? c with
      | none => rw [hk] at h1; simp at h1
      | some _ => rfl
    -- F3's field sources
    · intro c hc shape hs sf k lv np nmot nmin ni ind rules ty w srcs rule hd hk hr0
      have h1 := hsrcsE' c hc
      rw [hs] at h1
      dsimp only at h1
      have hn := Option.map_eq_none_iff.1 h1
      unfold subsingletonSrcs? at hn
      rw [hd, hk] at hn
      dsimp only at hn
      rw [hr0] at hn
      dsimp only at hn
      unfold ctorFields
      -- the field count `subsingletonSrcs?` reads: one case per declaration of the rule's
      -- constructor, each running the same script
      generalize p.decl? rule.ctor = D at hn ⊢
      rcases D with _ | (_ | _ | _ | _ | _ | _)
      all_goals
        dsimp only at hn ⊢
        split at hn
        · next heq => exact beq_iff_eq.1 heq
        · cases hn
    -- `Fin.mk`'s proof field where a word entry is reached
    · intro c hc w op thm hres fin hfin
      have h1 := hfinE' c hc
      rw [hres, hfin] at h1
      dsimp only at h1
      cases hk : ch.keepsP fin [] 1 with
      | false => rfl
      | true => rw [hk] at h1; simp at h1
  · cases hokE

/-! ## The erased facts P1 consumes, from the canonical records -/

/-! ### The classified telescope has the type's binders -/

private theorem pis_pi (b : Binder) (res : Ixon.V3.ValueContract) (d body : Term) :
    (Term.pi b res d body).pis.1 = (b, d) :: body.pis.1 := rfl

private theorem classifyTelescope_pi (p : Program) (ctx : List (Term × Option Ixon.Univ))
    (fuel : Nat) (b : Binder) (res : Ixon.V3.ValueContract) (d body : Term) :
    ∃ ctx', (classifyTelescope p ctx (fuel + 1) (.pi b res d body)).1 =
      (b, classifyDomain p ctx b d) :: (classifyTelescope p ctx' fuel body).1 := ⟨_, rfl⟩

private theorem classifyTelescope_binders (p : Program) (ty : Term) :
    ∀ (ctx : List (Term × Option Ixon.Univ)) (fuel : Nat), ty.piCount < fuel →
      (classifyTelescope p ctx fuel ty).1.map Prod.fst = ty.pis.1.map Prod.fst := by
  induction ty with
  | pi b res d body _ ihb =>
    intro ctx fuel h
    cases fuel with
    | zero => exact absurd h (Nat.not_lt_zero _)
    | succ fuel =>
      obtain ⟨ctx', e⟩ := classifyTelescope_pi p ctx fuel b res d body
      simp only [Term.piCount] at h
      rw [e, pis_pi, List.map_cons, List.map_cons, ihb ctx' fuel (by omega)]
  | _ =>
    intro ctx fuel h
    cases fuel with
    | zero => exact absurd h (Nat.not_lt_zero _)
    | succ fuel => rfl

/-- Position `i` of the classified telescope, from position `i` of the type's. -/
private theorem classified_at {p : Program} {ty : Term} {i : Nat} {b : Binder} {dom : Term}
    (h : ty.pis.1[i]? = some (b, dom)) :
    ∃ exp, (classifyTelescope p [] (ty.piCount + 1) ty).1[i]? = some (b, exp) := by
  have hfst : ((classifyTelescope p [] (ty.piCount + 1) ty).1.map Prod.fst)[i]? = some b := by
    simp only [classifyTelescope_binders p ty [] (ty.piCount + 1) (Nat.lt_succ_self _),
      List.getElem?_map, h, Option.map_some]
  rw [List.getElem?_map] at hfst
  obtain ⟨⟨b', exp⟩, hps, hb'⟩ := Option.map_eq_some_iff.1 hfst
  dsimp only at hb'
  rw [hb'] at hps
  exact ⟨exp, hps⟩

private theorem mem_erasedParams {ty : Term} {i : Nat} (hi : i ∈ erasedParams ty) :
    ∃ b dom, ty.pis.1[i]? = some (b, dom) ∧ (b.contract.uses == .erased) = true := by
  unfold erasedParams at hi
  obtain ⟨⟨⟨b, dom⟩, j⟩, hmem, rfl⟩ := List.mem_map.1 hi
  obtain ⟨hz, hw⟩ := List.mem_filter.1 hmem
  exact ⟨b, dom, by simpa using ((mem_zipIdx_iff _ 0 _ _).1 hz).2, hw⟩

private theorem paramsC_getElem {prof q : Profile} :
    ∀ {args : List Term.Arg} {params : List Rel} {i : Nat} {a : Term.Arg} {r : Rel},
      ParamsC prof q args params → args[i]? = some a → params[i]? = some r →
        r.irrP q = a.2.2.irrP prof
  | (_, _, _) :: _, _ :: _, 0, _, _, h, ha, hr => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hr
    subst ha hr
    exact h.1
  | (_, _, _) :: _, _ :: _, _ + 1, _, _, h, ha, hr => by
    simp only [List.getElem?_cons_succ] at ha hr
    exact paramsC_getElem h.2 ha hr
  | [], _, _, _, _, _, ha, _ => by simp at ha
  | _ :: _, [], _, _, _, _, _, hr => by simp at hr

private theorem alwaysIrr_irrP {r : Rel} (h : r.alwaysIrr = true) (q : Profile) :
    r.irrP q = true := by
  unfold Rel.alwaysIrr at h
  unfold Rel.irrP
  rw [beq_iff_eq.1 h]
  rfl

/-- A parameter written erased has a class irrelevant at every instance. -/
theorem param_erased_irr {p : Program} {c : CId} {cr : ConstRel} {d : Decl}
    (hc : ConstCanon p c cr) (hd : p.decl? c = some d) {i : Nat} (hi : i ∈ erasedParams d.type) :
    ∃ r, cr.params[i]? = some r ∧ r.alwaysIrr = true := by
  obtain ⟨d', hd', hlen, htag, -, -, -⟩ := hc
  have hdd : d' = d := Option.some.inj (hd'.symm.trans hd)
  rw [hdd] at hlen htag
  obtain ⟨b, dom, hbd, hw⟩ := mem_erasedParams hi
  obtain ⟨exp, hps⟩ := classified_at (p := p) hbd
  have hlt : i < cr.params.length := by
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.1 hps).1
  refine ⟨cr.params[i], List.getElem?_eq_getElem hlt, ?_⟩
  have ht := htag i _ b exp (List.getElem?_eq_getElem hlt) hps
  unfold tagOk at ht
  simp only [Bool.and_eq_true, hw, ↓reduceIte] at ht
  exact ht.2

/-- A constructor field written erased is dropped at every instance. -/
theorem field_erased_dropped {p : Program} {ann : Ann} {k : CId} {kr : CtorRel}
    (hk : CtorCanon p ann k kr) {i : Nat} (hi : fieldWrittenErased p k i = true) :
    ∃ cls, kr.fields[i]? = some cls ∧ cls.alwaysDropped = true := by
  obtain ⟨sf, lv, ind, cidx, np, nf, ty, hd, hlen, hflen, -, hfld⟩ := hk
  unfold fieldWrittenErased at hi
  rw [hd] at hi
  dsimp only at hi
  cases hpi : ty.pis.1[np + i]? with
  | none => rw [hpi] at hi; cases hi
  | some bd =>
    obtain ⟨b, dom⟩ := bd
    rw [hpi] at hi
    simp only [Option.any_some] at hi
    obtain ⟨exp, hps⟩ := classified_at (p := p) hpi
    have hdrop : ((classifyTelescope p [] (ty.piCount + 1) ty).1.drop np)[i]? = some (b, exp) := by
      rw [List.getElem?_drop]
      exact hps
    have hlt : i < kr.fields.length := by
      rw [hlen, ← hflen]
      exact (List.getElem?_eq_some_iff.1 hdrop).1
    refine ⟨kr.fields[i], List.getElem?_eq_getElem hlt, ?_⟩
    have h := (hfld i _ b exp (List.getElem?_eq_getElem hlt) hdrop).2
    simp only [writtenErased, hi, ↓reduceIte] at h
    exact h

/-- The caller's side: a constant head's argument at a parameter written erased is irrelevant at
every instance (C2 with `param_erased_irr`). -/
theorem arg_erased_irr {p : Program} {prof : Profile} {c : CId} {us : List Ixon.Univ}
    {cr : ConstRel} {d : Decl} {args : List Term.Arg}
    (hc : ConstCanon p c cr) (hd : p.decl? c = some d)
    (hargs : ParamsC prof (prof.inst us) args cr.params) {i : Nat} (hi : i ∈ erasedParams d.type)
    {a : Term.Arg} (ha : args[i]? = some a) : a.2.2.irrP prof = true := by
  obtain ⟨r, hr, hirr⟩ := param_erased_irr hc hd hi
  rw [← paramsC_getElem hargs ha hr]
  exact alwaysIrr_irrP hirr _

end IxCC.Src.Relevance.Proof
