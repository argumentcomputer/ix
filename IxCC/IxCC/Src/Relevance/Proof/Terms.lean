import IxCC.Src.Relevance.Check

/-! # What the relevance checker decides of one term

The checker walks each runtime term of an instance, adding an error for
every violated rule (`Check.term`/`Check.rest`). An empty error list
therefore gives the tier-S facts at every relevant
position the walk visits: S1 (variables in scope, constant and constructor
records present, conditions within the constant's levels) and S2 (a
constructor spine passes an argument irrelevant at the instance at every
field dropped at the constructor's profile), as the inductive `TermS`. -/

set_option autoImplicit false

namespace IxCC.Src.Relevance.Proof

open Check

/-- S2 over a constructor's fields at profile `q`, arguments decided at the
instance's profile `prof`. -/
def FieldsS (prof q : Profile) : List Term.Arg → List FieldClass → Prop
  | (_, _, a) :: args, cls :: fields =>
    (cls.dropP q = true → a.irrP prof = true) ∧ FieldsS prof q args fields
  | _, _ => True

/-- The tier-S facts at an application spine's head: a constructor has its
record, and S2 holds over its fields. -/
def HeadS (p : Program) (ann : Ann) (prof : Profile) : Term → List Term.Arg → Prop
  | .const c us, args =>
    match p.decl? c with
    | some (.ctor _ _ _ _ np _ _) =>
      ∃ rel, ann.ctorRel? c = some rel ∧ FieldsS prof (prof.inst us) (args.drop np) rel.fields
    | _ => True
  | _, _ => True

mutual

/-- The tier-S facts over the relevant positions of a term at an instance
(`lvls`, `prof`), under binder classes `bs` (innermost first). -/
inductive TermS (p : Program) (ann : Ann) (lvls : Nat) (prof : Profile) : List Rel → Term → Prop
  | var {bs : List Rel} {i : Nat} : i < bs.length → TermS p ann lvls prof bs (.var i)
  | const {bs : List Rel} {c : CId} {us : List Ixon.Univ} :
      (ann.constRel? c).isSome = true → TermS p ann lvls prof bs (.const c us)
  | lam {bs : List Rel} {b : Binder} {d t : Term} :
      pwOk lvls b.propWhen = true → relOk lvls b.rel = true → b.propWhen.holdsP prof = false →
      TermS p ann lvls prof (b.rel :: bs) t → TermS p ann lvls prof bs (.lam b d t)
  | letE {bs : List Rel} {c : Ixon.V3.LetContract} {r : Rel} {ty v b : Term} :
      relOk lvls r = true → (r.irrP prof = false → TermS p ann lvls prof bs v) →
      TermS p ann lvls prof (r :: bs) b → TermS p ann lvls prof bs (.letE c r ty v b)
  | proj {bs : List Rel} {s i : Nat} {e : Term} :
      (∃ k rel cls, onlyCtor? p s = some k ∧ ann.ctorRel? k = some rel ∧
        rel.fields[i]? = some cls) →
      TermS p ann lvls prof bs e → TermS p ann lvls prof bs (.proj s i e)
  | app {bs : List Rel} {f a : Term} {m : Mode} {r : Rel} :
      HeadS p ann prof (Term.app f a m r).spineL.1 (Term.app f a m r).spineL.2 →
      relOk lvls r = true → SpineS p ann lvls prof bs f →
      (r.irrP prof = false → TermS p ann lvls prof bs a) →
      TermS p ann lvls prof bs (.app f a m r)
  | sort {bs : List Rel} {u : Ixon.Univ} : TermS p ann lvls prof bs (.sort u)
  | pi {bs : List Rel} {b : Binder} {res : Ixon.V3.ValueContract} {d c : Term} :
      TermS p ann lvls prof bs (.pi b res d c)
  | natLit {bs : List Rel} {n : Nat} : TermS p ann lvls prof bs (.natLit n)
  | strLit {bs : List Rel} {s : String} : TermS p ann lvls prof bs (.strLit s)

/-- The same facts over the rest of an application spine (`Check.rest`). -/
inductive SpineS (p : Program) (ann : Ann) (lvls : Nat) (prof : Profile) : List Rel → Term → Prop
  | app {bs : List Rel} {f a : Term} {m : Mode} {r : Rel} :
      relOk lvls r = true → SpineS p ann lvls prof bs f →
      (r.irrP prof = false → TermS p ann lvls prof bs a) →
      SpineS p ann lvls prof bs (.app f a m r)
  | head {bs : List Rel} {t : Term} : (∀ f a m r, t ≠ .app f a m r) →
      TermS p ann lvls prof bs t → SpineS p ann lvls prof bs t

end

/-! ## Errors only accumulate -/

/-- A step that only prepends errors. -/
def Adds (g : List RelError → List RelError) : Prop := ∀ errs, ∃ l, g errs = l ++ errs

theorem Adds.nil {g : List RelError → List RelError} (h : Adds g) {errs : List RelError}
    (e : g errs = []) : errs = [] := by
  obtain ⟨l, hl⟩ := h errs
  rw [hl] at e
  exact (List.append_eq_nil_iff.1 e).2

theorem Adds.id : Adds fun errs => errs := fun _ => ⟨[], rfl⟩

theorem Adds.cons (e : RelError) : Adds fun errs => e :: errs := fun _ => ⟨[e], rfl⟩

theorem Adds.comp {g h : List RelError → List RelError} (hg : Adds g) (hh : Adds h) :
    Adds fun errs => g (h errs) := fun errs => by
  obtain ⟨l₁, h₁⟩ := hh errs
  obtain ⟨l₂, h₂⟩ := hg (h errs)
  exact ⟨l₂ ++ l₁, by show g (h errs) = _; rw [h₂, h₁, List.append_assoc]⟩

theorem Adds.foldl {α : Type} {g : List RelError → α → List RelError}
    (hg : ∀ x, Adds fun errs => g errs x) : ∀ (xs : List α), Adds fun errs => xs.foldl g errs
  | [] => Adds.id
  | x :: xs => by
    simp only [List.foldl_cons]
    exact (Adds.foldl hg xs).comp (hg x)

section Rules

variable (ctx : Ctx)

theorem adds_paramArgs (c : CId) (q : Profile) :
    ∀ (args : List Term.Arg) (params : List Rel), Adds fun errs => paramArgs ctx c q args params errs
  | (_, _, a) :: args, r :: params => by
    intro errs
    simp only [paramArgs]
    obtain ⟨l, hl⟩ := adds_paramArgs c q args params
      (if r.irrP q && !a.irrP ctx.prof then err ctx "C2"
          s!"a {relName r} parameter gets a relevant argument" (some c) :: errs
        else if a.irrP ctx.prof && !r.irrP q then err ctx "C2"
          s!"a {relName a} argument for a parameter relevant at this instance" (some c) :: errs
        else errs)
    dsimp only at hl
    rw [hl]
    split
    · exact ⟨_, List.append_cons _ _ _⟩
    · split
      · exact ⟨_, List.append_cons _ _ _⟩
      · exact ⟨l, rfl⟩
  | [], _ => fun errs => ⟨[], by simp [paramArgs]⟩
  | _ :: _, [] => fun errs => ⟨[], by simp [paramArgs]⟩

theorem fieldArgs_nil (c : CId) (q : Profile) :
    ∀ (j : Nat) (args : List Term.Arg) (fields : List FieldClass) (errs : List RelError),
      fieldArgs ctx c q j args fields errs = [] → errs = [] ∧ FieldsS ctx.prof q args fields
  | j, (x, m, a) :: args, cls :: fields, errs, e => by
    simp only [fieldArgs] at e
    obtain ⟨h₁, h₂⟩ := fieldArgs_nil c q (j + 1) args fields _ e
    split at h₁
    · cases h₁
    · next hc =>
      refine ⟨h₁, fun hd => ?_, h₂⟩
      simp only [hd, Bool.true_and, Bool.not_eq_true', Bool.not_eq_false] at hc
      simpa using hc
  | _, [], _, errs, e => by simp only [fieldArgs] at e; exact ⟨e, trivial⟩
  | _, _ :: _, [], errs, e => by simp only [fieldArgs] at e; exact ⟨e, trivial⟩

theorem adds_fieldArgs (c : CId) (q : Profile) :
    ∀ (j : Nat) (args : List Term.Arg) (fields : List FieldClass),
      Adds fun errs => fieldArgs ctx c q j args fields errs
  | j, (_, _, a) :: args, cls :: fields => by
    intro errs
    simp only [fieldArgs]
    obtain ⟨l, hl⟩ := adds_fieldArgs c q (j + 1) args fields
      (if cls.dropP q && !a.irrP ctx.prof then err ctx "S2"
          s!"field {j} is dropped but built from a relevant argument" (some c) :: errs
        else errs)
    dsimp only at hl
    rw [hl]
    split
    · exact ⟨_, List.append_cons _ _ _⟩
    · exact ⟨l, rfl⟩
  | _, [], _ => fun errs => ⟨[], by simp [fieldArgs]⟩
  | _, _ :: _, [] => fun errs => ⟨[], by simp [fieldArgs]⟩

theorem adds_minorBinders (k : CId) (j : Nat) (qc : Profile) :
    ∀ (i : Nat) (bs : List Rel) (fields : List FieldClass),
      Adds fun errs => minorBinders ctx k j qc i bs fields errs
  | i, b :: bs, cls :: fields => by
    intro errs
    simp only [minorBinders]
    obtain ⟨l, hl⟩ := adds_minorBinders k j qc (i + 1) bs fields
      (if cls.dropP qc && !b.irrP ctx.prof then err ctx "C3"
          s!"minor {j} binds dropped field {i} relevantly" (some k) :: errs
        else errs)
    dsimp only at hl
    rw [hl]
    split
    · exact ⟨_, List.append_cons _ _ _⟩
    · exact ⟨l, rfl⟩
  | i, [], _ :: fields => by
    intro errs
    simp only [minorBinders]
    split
    · exact ⟨[_], rfl⟩
    · exact adds_minorBinders k j qc (i + 1) [] fields errs
  | _, [], [] => fun errs => ⟨[], by simp [minorBinders]⟩
  | _, _ :: _, [] => fun errs => ⟨[], by simp [minorBinders]⟩

theorem adds_partialElim (shape : ElimShape) : Adds fun errs => partialElim ctx shape errs := by
  intro errs
  unfold partialElim
  split
  · exact ⟨[_], rfl⟩
  · exact ⟨[], rfl⟩

theorem bareHead_constHead (c : CId) (us : List Ixon.Univ) (errs : List RelError)
    (e : bareHead ctx c us errs = []) : constHead ctx c us errs = [] := by
  unfold bareHead at e
  dsimp only at e
  split at e
  · exact (adds_partialElim ctx _).nil e
  · exact e

theorem varRule_nil (bs : List Rel) (errs : List RelError) (i : Nat)
    (e : varRule ctx bs errs i = []) : errs = [] ∧ i < bs.length := by
  unfold varRule at e
  split at e
  · next r hr =>
    split at e
    · cases e
    · exact ⟨e, (List.getElem?_eq_some_iff.1 hr).1⟩
  · cases e

theorem constHead_nil (c : CId) (us : List Ixon.Univ) (errs : List RelError)
    (e : constHead ctx c us errs = []) : errs = [] ∧ (ctx.ann.constRel? c).isSome = true := by
  unfold constHead at e
  split at e
  · next rel hr =>
    split at e
    · cases e
    · exact ⟨e, by rw [hr]; rfl⟩
  · cases e

theorem lamRule_nil (errs : List RelError) (b : Binder) (e : (lamRule ctx errs b).1 = []) :
    errs = [] ∧ pwOk ctx.lvls b.propWhen = true ∧ relOk ctx.lvls b.rel = true ∧
      b.propWhen.holdsP ctx.prof = false ∧ (lamRule ctx errs b).2 = true := by
  unfold lamRule at e ⊢
  dsimp only at e ⊢
  by_cases hh : b.propWhen.holdsP ctx.prof = true
  · simp only [hh, ↓reduceIte] at e
    cases e
  · simp only [hh, Bool.false_eq_true, ↓reduceIte] at e ⊢
    by_cases h1 : (pwOk ctx.lvls b.propWhen && relOk ctx.lvls b.rel) = true
    · by_cases h2 : (b.contract.uses == .erased && !b.rel.irrP ctx.prof) = true
      · simp only [h1, h2, ↓reduceIte] at e
        cases e
      · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte] at e
        exact ⟨e, (Bool.and_eq_true_iff.1 h1).1, (Bool.and_eq_true_iff.1 h1).2, by simp,
          trivial⟩
    · simp only [h1, Bool.false_eq_true, ↓reduceIte] at e
      split at e <;> cases e

theorem letRule_nil (errs : List RelError) (c : Ixon.V3.LetContract) (r : Rel)
    (e : letRule ctx errs c r = []) : errs = [] ∧ relOk ctx.lvls r = true := by
  unfold letRule at e
  dsimp only at e
  split at e
  · cases e
  · split at e
    · next h => exact ⟨e, h⟩
    · cases e

theorem projRule_nil (errs : List RelError) (s i : Nat) (e : projRule ctx errs s i = []) :
    errs = [] ∧ ∃ k rel cls, onlyCtor? ctx.p s = some k ∧ ctx.ann.ctorRel? k = some rel ∧
      rel.fields[i]? = some cls := by
  unfold projRule at e
  split at e
  · next k hk =>
    split at e
    · next rel hrel =>
      split at e
      · next cls hcls =>
        split at e
        · cases e
        · exact ⟨e, k, rel, cls, hk, hrel, hcls⟩
      · cases e
    · cases e
  · cases e

theorem argRule_nil (errs : List RelError) (r : Rel) (e : argRule ctx errs r = []) :
    errs = [] ∧ relOk ctx.lvls r = true := by
  unfold argRule at e
  split at e
  · next h => exact ⟨e, h⟩
  · cases e

theorem adds_lamHead (head : Term) (args : List Term.Arg) :
    Adds fun errs => lamHead ctx errs head args := by
  intro errs
  unfold lamHead
  dsimp only
  refine Adds.foldl (fun x => ?_) _ errs
  obtain ⟨⟨_, _, a⟩, r⟩ := x
  intro errs
  dsimp only
  split
  · exact ⟨[_], rfl⟩
  · split
    · exact ⟨[_], rfl⟩
    · exact ⟨[], rfl⟩

theorem knownHead_nil (errs : List RelError) (c : CId) (us : List Ixon.Univ)
    (args : List Term.Arg) (e : knownHead ctx errs c us args = []) :
    errs = [] ∧ HeadS ctx.p ctx.ann ctx.prof (.const c us) args := by
  unfold knownHead at e
  dsimp only at e
  -- The eliminator rules only add errors.
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
          | _, _ => errs)) = [] → E = [] := by
    intro E hE
    split at hE
    · exact hE
    · split at hE
      · exact (adds_partialElim ctx _).nil hE
      · have hf := (Adds.foldl (g := fun errs (x : Nat × Nat × Nat) =>
          match args[x.1]?, ruleCtorFields ctx.p ctx.ann _ x.2.2 with
          | some (minor, _, a), some (k, fields) =>
            if a.irrP ctx.prof then errs
            else minorBinders ctx k x.2.1 (ctorProfile ctx.p _ (ctx.prof.inst us)) 0
              (lamRels minor) fields errs
          | _, _ => errs) (fun x => by
            intro errs
            dsimp only
            split
            · split
              · exact ⟨[], rfl⟩
              · exact adds_minorBinders ctx _ _ _ _ _ _ errs
            · exact ⟨[], rfl⟩) _).nil hE
        split at hf
        · split at hf
          · cases hf
          · exact hf
        · exact hf
  have hE2 := htail _ e
  have hE1 : ∀ E, (match ctx.ann.constRel? c with
      | some rel => paramArgs ctx c (ctx.prof.inst us) args rel.params E
      | none => E) = [] → E = [] := fun E h => by
    split at h
    · exact (adds_paramArgs ctx c _ args _).nil h
    · exact h
  cases hd : ctx.p.decl? c with
  | none =>
    simp only [hd] at hE2
    exact ⟨hE1 _ hE2, by simp [HeadS, hd]⟩
  | some d =>
    cases d with
    | ctor sf lv ind cidx np nf ty =>
      cases hr : ctx.ann.ctorRel? c with
      | none => simp only [hd, hr] at hE2; cases hE2
      | some rel =>
        simp only [hd, hr] at hE2
        obtain ⟨h₁, hF⟩ := fieldArgs_nil ctx c _ 0 _ _ _ hE2
        exact ⟨hE1 _ h₁, by simp only [HeadS, hd]; exact ⟨rel, hr, hF⟩⟩
    | _ =>
      simp only [hd] at hE2
      exact ⟨hE1 _ hE2, by simp [HeadS, hd]⟩

theorem appRule_nil (errs : List RelError) (t : Term) (r : Rel) (e : appRule ctx errs t r = []) :
    errs = [] ∧ HeadS ctx.p ctx.ann ctx.prof t.spineL.1 t.spineL.2 ∧ relOk ctx.lvls r = true := by
  unfold appRule at e
  generalize t.spineL = sp at e ⊢
  obtain ⟨hd, args⟩ := sp
  dsimp only at e ⊢
  obtain ⟨hE, hr⟩ := argRule_nil ctx _ r e
  cases hd with
  | const c us =>
    obtain ⟨h₁, h₂⟩ := knownHead_nil ctx _ _ _ _ hE
    exact ⟨h₁, h₂, hr⟩
  | lam b d body => exact ⟨(adds_lamHead ctx _ _).nil hE, trivial, hr⟩
  | var _ => exact ⟨hE, trivial, hr⟩
  | sort _ => exact ⟨hE, trivial, hr⟩
  | app f a m r' => exact ⟨hE, trivial, hr⟩
  | pi b res d c => exact ⟨hE, trivial, hr⟩
  | letE c r' ty v b => exact ⟨hE, trivial, hr⟩
  | proj s i e' => exact ⟨hE, trivial, hr⟩
  | natLit _ => exact ⟨hE, trivial, hr⟩
  | strLit _ => exact ⟨hE, trivial, hr⟩


end Rules

section Walk

variable (ctx : Ctx)

mutual

/-- An empty error list after a term's walk gives its tier-S facts. -/
theorem term_nil : ∀ (bs : List Rel) (errs : List RelError) (t : Term),
    term ctx bs errs t = [] → errs = [] ∧ TermS ctx.p ctx.ann ctx.lvls ctx.prof bs t
  | bs, errs, .var i, e => by
    unfold term at e
    obtain ⟨h₁, h₂⟩ := varRule_nil ctx bs errs i e
    exact ⟨h₁, .var h₂⟩
  | bs, errs, .const c us, e => by
    unfold term at e
    obtain ⟨h₁, h₂⟩ := constHead_nil ctx c us errs (bareHead_constHead ctx c us errs e)
    exact ⟨h₁, .const h₂⟩
  | bs, errs, .lam b d t, e => by
    unfold term at e
    rcases hl : lamRule ctx errs b with ⟨errs', enter⟩
    rw [hl] at e
    dsimp only at e
    cases enter with
    | true =>
      simp only [↓reduceIte] at e
      obtain ⟨h₁, h₂⟩ := term_nil (b.rel :: bs) errs' t e
      obtain ⟨h₃, h₄, h₅, h₆, _⟩ := lamRule_nil ctx errs b (by rw [hl]; exact h₁)
      exact ⟨h₃, .lam h₄ h₅ h₆ h₂⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at e
      have := (lamRule_nil ctx errs b (by rw [hl]; exact e)).2.2.2.2
      rw [hl] at this
      cases this
  | bs, errs, .letE c r ty v b, e => by
    unfold term at e
    dsimp only at e
    obtain ⟨h₁, h₂⟩ := term_nil (r :: bs) _ b e
    by_cases hr : r.irrP ctx.prof = true
    · simp only [hr, ↓reduceIte] at h₁
      obtain ⟨h₃, h₄⟩ := letRule_nil ctx errs c r h₁
      exact ⟨h₃, .letE h₄ (fun h => by rw [hr] at h; cases h) h₂⟩
    · simp only [hr, Bool.false_eq_true, ↓reduceIte] at h₁
      obtain ⟨h₃, h₄⟩ := term_nil bs _ v h₁
      obtain ⟨h₅, h₆⟩ := letRule_nil ctx errs c r h₃
      exact ⟨h₅, .letE h₆ (fun _ => h₄) h₂⟩
  | bs, errs, .proj s i e', e => by
    unfold term at e
    obtain ⟨h₁, h₂⟩ := term_nil bs _ e' e
    obtain ⟨h₃, h₄⟩ := projRule_nil ctx errs s i h₁
    exact ⟨h₃, .proj h₄ h₂⟩
  | bs, errs, .app f a m r, e => by
    unfold term at e
    dsimp only at e
    have hrest : ∀ E, rest ctx bs E f = [] →
        (appRule ctx errs (.app f a m r) r = E) →
        errs = [] ∧ HeadS ctx.p ctx.ann ctx.prof (Term.app f a m r).spineL.1
          (Term.app f a m r).spineL.2 ∧ relOk ctx.lvls r = true ∧
          SpineS ctx.p ctx.ann ctx.lvls ctx.prof bs f := fun E hE hE' => by
      obtain ⟨h₁, h₂⟩ := rest_nil bs E f hE
      subst h₁
      obtain ⟨h₃, h₄, h₅⟩ := appRule_nil ctx errs _ r hE'
      exact ⟨h₃, h₄, h₅, h₂⟩
    by_cases hr : r.irrP ctx.prof = true
    · simp only [hr, ↓reduceIte] at e
      obtain ⟨h₁, h₂, h₃, h₄⟩ := hrest _ e rfl
      exact ⟨h₁, .app h₂ h₃ h₄ fun h => by rw [hr] at h; cases h⟩
    · simp only [hr, Bool.false_eq_true, ↓reduceIte] at e
      obtain ⟨h₅, h₆⟩ := term_nil bs _ a e
      obtain ⟨h₁, h₂, h₃, h₄⟩ := hrest _ h₅ rfl
      exact ⟨h₁, .app h₂ h₃ h₄ fun _ => h₆⟩
  | bs, errs, .sort u, e => by unfold term at e; exact ⟨e, .sort⟩
  | bs, errs, .pi b res d c, e => by unfold term at e; exact ⟨e, .pi⟩
  | bs, errs, .natLit n, e => by unfold term at e; exact ⟨e, .natLit⟩
  | bs, errs, .strLit s, e => by unfold term at e; exact ⟨e, .strLit⟩

/-- The same for the rest of an application spine. -/
theorem rest_nil : ∀ (bs : List Rel) (errs : List RelError) (t : Term),
    rest ctx bs errs t = [] → errs = [] ∧ SpineS ctx.p ctx.ann ctx.lvls ctx.prof bs t
  | bs, errs, .app f a m r, e => by
    unfold rest at e
    dsimp only at e
    by_cases hr : r.irrP ctx.prof = true
    · simp only [hr, ↓reduceIte] at e
      obtain ⟨h₁, h₂⟩ := rest_nil bs _ f e
      obtain ⟨h₃, h₄⟩ := argRule_nil ctx errs r h₁
      exact ⟨h₃, .app h₄ h₂ fun h => by rw [hr] at h; cases h⟩
    · simp only [hr, Bool.false_eq_true, ↓reduceIte] at e
      obtain ⟨h₅, h₆⟩ := term_nil bs _ a e
      obtain ⟨h₁, h₂⟩ := rest_nil bs _ f h₅
      obtain ⟨h₃, h₄⟩ := argRule_nil ctx errs r h₁
      exact ⟨h₃, .app h₄ h₂ fun _ => h₆⟩
  | bs, errs, .var i, e => by
    unfold rest at e
    obtain ⟨h₁, h₂⟩ := varRule_nil ctx bs errs i e
    exact ⟨h₁, .head (fun _ _ _ _ h => by cases h) (.var h₂)⟩
  | bs, errs, .const c us, e => by
    unfold rest at e
    obtain ⟨h₁, h₂⟩ := constHead_nil ctx c us errs e
    exact ⟨h₁, .head (fun _ _ _ _ h => by cases h) (.const h₂)⟩
  | bs, errs, .lam b d t, e => by
    unfold rest at e
    rcases hl : lamRule ctx errs b with ⟨errs', enter⟩
    rw [hl] at e
    dsimp only at e
    cases enter with
    | true =>
      simp only [↓reduceIte] at e
      obtain ⟨h₁, h₂⟩ := term_nil (b.rel :: bs) errs' t e
      obtain ⟨h₃, h₄, h₅, h₆, _⟩ := lamRule_nil ctx errs b (by rw [hl]; exact h₁)
      exact ⟨h₃, .head (fun _ _ _ _ h => by cases h) (.lam h₄ h₅ h₆ h₂)⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at e
      have := (lamRule_nil ctx errs b (by rw [hl]; exact e)).2.2.2.2
      rw [hl] at this
      cases this
  | bs, errs, .letE c r ty v b, e => by
    unfold rest at e
    dsimp only at e
    obtain ⟨h₁, h₂⟩ := term_nil (r :: bs) _ b e
    by_cases hr : r.irrP ctx.prof = true
    · simp only [hr, ↓reduceIte] at h₁
      obtain ⟨h₃, h₄⟩ := letRule_nil ctx errs c r h₁
      exact ⟨h₃, .head (fun _ _ _ _ h => by cases h)
        (.letE h₄ (fun h => by rw [hr] at h; cases h) h₂)⟩
    · simp only [hr, Bool.false_eq_true, ↓reduceIte] at h₁
      obtain ⟨h₃, h₄⟩ := term_nil bs _ v h₁
      obtain ⟨h₅, h₆⟩ := letRule_nil ctx errs c r h₃
      exact ⟨h₅, .head (fun _ _ _ _ h => by cases h) (.letE h₆ (fun _ => h₄) h₂)⟩
  | bs, errs, .proj s i e', e => by
    unfold rest at e
    obtain ⟨h₁, h₂⟩ := term_nil bs _ e' e
    obtain ⟨h₃, h₄⟩ := projRule_nil ctx errs s i h₁
    exact ⟨h₃, .head (fun _ _ _ _ h => by cases h) (.proj h₄ h₂)⟩
  | bs, errs, .sort u, e => by
    unfold rest at e; exact ⟨e, .head (fun _ _ _ _ h => by cases h) .sort⟩
  | bs, errs, .pi b res d c, e => by
    unfold rest at e; exact ⟨e, .head (fun _ _ _ _ h => by cases h) .pi⟩
  | bs, errs, .natLit n, e => by
    unfold rest at e; exact ⟨e, .head (fun _ _ _ _ h => by cases h) .natLit⟩
  | bs, errs, .strLit s, e => by
    unfold rest at e; exact ⟨e, .head (fun _ _ _ _ h => by cases h) .strLit⟩

end

end Walk

end IxCC.Src.Relevance.Proof
