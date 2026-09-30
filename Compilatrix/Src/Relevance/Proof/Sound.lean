import Compilatrix.Src.Relevance.Proof.Terms
import Compilatrix.Src.Proof.NatMap

/-! # The relevance checker is sound: `check_sound`

`Relevance.check p ann = .ok c` gives the tier-S facts (design note 02
§3.3) as a Prop, `WellAnnotated p ann c`, per profile: the records are well
shaped (S1), every reached instance `(constant, profile)` has its record,
its runtime terms annotated and their relevant positions satisfying S1 and
S2 at that profile (`TermS`), and S4 at a subsingleton eliminator; the
reached instances contain the roots and are closed under the references a
relevant position makes at the reaching profile (`Program.instRefs`), so
they are the instances SrcEval can reach (M2.2). -/

set_option autoImplicit false

namespace Compilatrix.Src.Relevance.Proof

open Check

/-- A constant's level count. -/
abbrev lvlsOf (p : Program) (c : CId) : Nat := ((p.decl? c).map Decl.lvls).getD 0

/-- S1 on the records: parameter classes within the telescope and the
levels, field classes as many as the fields and within the levels. -/
structure RecordsS (p : Program) (ann : Ann) : Prop where
  consts : ∀ c, c < p.size → ∀ rel, ann.constRel? c = some rel →
    rel.params.length ≤ ((p.decl? c).map fun d => d.type.piCount).getD 0 ∧
      ∀ r ∈ rel.result :: rel.params, relOk (lvlsOf p c) r = true
  ctors : ∀ c, c < p.size → ∀ rel, ann.ctorRel? c = some rel →
    ∃ sf lv ind cidx np nf ty, p.decl? c = some (.ctor sf lv ind cidx np nf ty) ∧
      rel.fields.length = nf ∧ ∀ cls ∈ rel.fields, pwOk (lvlsOf p c) cls.dropWhen = true

/-- S4 at a recursor instance: at a profile where it is a subsingleton
eliminator, its constructor keeps only fields read from an index. -/
def SubS (p : Program) (ann : Ann) (r : CId) (q : Profile) : Prop :=
  ∀ sf k lv np nmot nmin ni ind rules ty w srcs rule rel,
    p.decl? r = some (.recr sf k lv np nmot nmin ni ind rules ty) →
    (p.table.recKindOf r).map (fun k => RecKind.atProfile q k) = some (.subsingleton w srcs) →
    rules.head? = some rule → ann.ctorRel? rule.ctor = some rel →
    ∀ (j : Nat) (cls : FieldClass), rel.fields[j]? = some cls →
      cls.dropP (ctorProfile p r q) = false →
      ∃ i, srcs[j]? = some (FieldSrc.index i)

/-- The tier-S facts at one reached instance. -/
structure InstS (p : Program) (ann : Ann) (c : CId) (prof : Profile) : Prop where
  record : (ann.constRel? c).isSome = true
  annotated : ∀ key ∈ p.runtimeKeys c, ∃ tags, (key, tags) ∈ ann.nodes
  terms : ∀ key ∈ p.runtimeKeys c, ∀ t, p.termOf key = some t →
    TermS p ann (lvlsOf p c) prof [] t
  sub : SubS p ann c prof

/-- An instance reference that the closure has handled: out of the
program, or reached at its normalised profile. -/
def Handled (p : Program) (order : List Inst) (r : Inst) : Prop :=
  r.1 ≥ p.size ∨ (r.1, r.2.normalize (lvlsOf p r.1)) ∈ order

/-- What `check` establishes (tier S), per profile. -/
structure WellAnnotated (p : Program) (ann : Ann) (c : Checked) : Prop where
  consts : c.consts = ann.consts
  ctors : c.ctors = ann.ctors
  records : RecordsS p ann
  insts : ∀ inst ∈ c.instances, InstS p ann inst.1 inst.2
  roots : ∀ r ∈ p.roots, Handled p c.instances (p.instOf r.2 [])
  closed : ∀ inst ∈ c.instances, ∀ r ∈ p.instRefs inst.1 inst.2, Handled p c.instances r

/-! ## Folds that only add errors -/

theorem foldl_nil {α : Type} {f : List RelError → α → List RelError} {P : α → Prop}
    (hf : ∀ errs x, f errs x = [] → errs = [] ∧ P x) :
    ∀ (xs : List α) (errs : List RelError), xs.foldl f errs = [] → errs = [] ∧ ∀ x ∈ xs, P x
  | [], errs, e => ⟨e, fun _ h => by cases h⟩
  | x :: xs, errs, e => by
    rw [List.foldl_cons] at e
    obtain ⟨h₁, h₂⟩ := foldl_nil hf xs _ e
    obtain ⟨h₃, h₄⟩ := hf errs x h₁
    exact ⟨h₃, fun y hy => (List.mem_cons.1 hy).elim (fun e => e ▸ h₄) (h₂ y)⟩

theorem foldl_zipIdx_nil {α : Type} {f : List RelError → α × Nat → List RelError}
    {P : Nat → α → Prop} (hf : ∀ errs x j, f errs (x, j) = [] → errs = [] ∧ P j x) :
    ∀ (xs : List α) (n : Nat) (errs : List RelError), (xs.zipIdx n).foldl f errs = [] →
      errs = [] ∧ ∀ j x, xs[j]? = some x → P (n + j) x
  | [], _, errs, e => ⟨e, fun _ _ h => by simp at h⟩
  | x :: xs, n, errs, e => by
    rw [List.zipIdx_cons, List.foldl_cons] at e
    obtain ⟨h₁, h₂⟩ := foldl_zipIdx_nil hf xs (n + 1) _ e
    obtain ⟨h₃, h₄⟩ := hf errs x n h₁
    refine ⟨h₃, fun j y hy => ?_⟩
    cases j with
    | zero => simp at hy; subst hy; simpa using h₄
    | succ j =>
      simp only [List.getElem?_cons_succ] at hy
      have := h₂ j y hy
      rwa [show n + 1 + j = n + (j + 1) by omega] at this

theorem TermKey.eq_of_beq {a b : TermKey} (h : (a == b) = true) : a = b := by
  cases a with
  | value c =>
    cases b with
    | value d => exact congrArg _ (beq_iff_eq.1 (show (c == d) = true from h))
    | _ => cases h
  | eqn c =>
    cases b with
    | eqn d => exact congrArg _ (beq_iff_eq.1 (show (c == d) = true from h))
    | _ => cases h
  | rule c i =>
    cases b with
    | rule d j =>
      have h' : (c == d && i == j) = true := h
      obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.1 h'
      rw [beq_iff_eq.1 h₁, beq_iff_eq.1 h₂]
    | _ => cases h

/-! ## S4 -/

theorem subsingletonFields_nil (p : Program) (ann : Ann) (r : CId) (q : Profile)
    (errs : List RelError) (e : subsingletonFields p ann r q errs = []) :
    errs = [] ∧ SubS p ann r q := by
  unfold subsingletonFields at e
  split at e
  · next sf k lv np nmot nmin ni ind rules ty w srcs hd hk =>
    split at e
    · next rule hr =>
      split at e
      · next rel hrel =>
        dsimp only at e
        obtain ⟨h₁, h₂⟩ := foldl_zipIdx_nil (P := fun j cls =>
          cls.dropP (ctorProfile p r q) = false → ∃ i, srcs[j]? = some (FieldSrc.index i))
          (fun errs cls j he => by
            dsimp only at he
            split at he
            · next hdrop => exact ⟨he, fun h => by rw [hdrop] at h; cases h⟩
            · split at he
              · next i hi => exact ⟨he, fun _ => ⟨i, hi⟩⟩
              · cases he) rel.fields 0 errs e
        refine ⟨h₁, fun sf' k' lv' np' nmot' nmin' ni' ind' rules' ty' w' srcs' rule' rel' hd' hk' hr'
          hrel' j cls hj hdrop => ?_⟩
        rw [hd] at hd'
        cases hd'
        rw [hk] at hk'
        cases hk'
        rw [hr] at hr'
        cases hr'
        rw [hrel] at hrel'
        cases hrel'
        simpa using h₂ j cls hj hdrop
      · next hrel =>
        exact ⟨e, fun _ _ _ _ _ _ _ _ _ _ _ _ rule' rel' hd' hk' hr' hrel' => by
          rw [hd] at hd'; cases hd'; rw [hr] at hr'; cases hr'; rw [hrel] at hrel'; cases hrel'⟩
    · next hr =>
      exact ⟨e, fun _ _ _ _ _ _ _ _ _ _ _ _ rule' _ hd' _ hr' => by
        rw [hd] at hd'; cases hd'; rw [hr] at hr'; cases hr'⟩
  · next hne =>
    exact ⟨e, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd' hk' =>
      (hne _ _ _ _ _ _ _ _ _ _ _ _ hd' hk').elim⟩

/-! ## One instance -/

theorem contains_mem {α : Type} [BEq α] {a : α} :
    ∀ {l : List α}, l.contains a = true → ∃ b ∈ l, (a == b) = true
  | [], h => by simp at h
  | b :: l, h => by
    simp only [List.contains, List.elem] at h
    split at h
    · next hb => exact ⟨b, List.mem_cons_self, hb⟩
    · obtain ⟨b', hb', e⟩ := contains_mem (l := l) h
      exact ⟨b', List.mem_cons_of_mem _ hb', e⟩

/-- A fold over the runtime keys that keeps the closure's bookkeeping and
only adds errors. -/
theorem foldl_st {f : St → TermKey → St} {P : TermKey → Prop}
    (hseen : ∀ s k, (f s k).seen = s.seen) (hord : ∀ s k, (f s k).order = s.order)
    (hf : ∀ s k, (f s k).errs = [] → s.errs = [] ∧ P k) :
    ∀ (xs : List TermKey) (s : St), (xs.foldl f s).seen = s.seen ∧
      (xs.foldl f s).order = s.order ∧
      ((xs.foldl f s).errs = [] → s.errs = [] ∧ ∀ k ∈ xs, P k)
  | [], s => ⟨rfl, rfl, fun h => ⟨h, fun _ h => by cases h⟩⟩
  | x :: xs, s => by
    rw [List.foldl_cons]
    obtain ⟨h₁, h₂, h₃⟩ := foldl_st hseen hord hf xs (f s x)
    refine ⟨h₁.trans (hseen s x), h₂.trans (hord s x), fun e => ?_⟩
    obtain ⟨h₄, h₅⟩ := h₃ e
    obtain ⟨h₆, h₇⟩ := hf s x h₄
    exact ⟨h₆, fun k hk => (List.mem_cons.1 hk).elim (fun e => e ▸ h₇) (h₅ k)⟩

theorem visit_spec (p : Program) (ann : Ann) (annotated : NatMap (List TermKey)) (c : CId)
    (prof : Profile) (lvls : Nat) (first : Bool) (s : St) :
    (visit p ann annotated c prof lvls first s).1.seen = s.seen ∧
      (visit p ann annotated c prof lvls first s).1.order = s.order ∧
      (visit p ann annotated c prof lvls first s).2 = p.instRefs c prof ∧
      ((visit p ann annotated c prof lvls first s).1.errs = [] → s.errs = [] ∧
        (first = true → (ann.constRel? c).isSome = true ∧
          ∀ key ∈ p.runtimeKeys c, ((annotated.get? c).getD []).contains key = true) ∧
        (∀ key ∈ p.runtimeKeys c, ((annotated.get? c).getD []).contains key = true →
          ∀ t, p.termOf key = some t → TermS p ann lvls prof [] t) ∧
        SubS p ann c prof) := by
  unfold visit
  dsimp only
  generalize hs₁ : (if (first && (ann.constRel? c).isNone) = true then
      { s with errs := RelError.of "S1" "reached constant without a record" (some c) :: s.errs }
    else s) = s₁
  have hs₁seen : s₁.seen = s.seen := by rw [← hs₁]; split <;> rfl
  have hs₁ord : s₁.order = s.order := by rw [← hs₁]; split <;> rfl
  have hs₁errs : s₁.errs = [] → s.errs = [] ∧ (first = true → (ann.constRel? c).isSome = true) :=
    fun e => by
      rw [← hs₁] at e
      split at e
      · cases e
      · next h =>
        refine ⟨e, fun hf => ?_⟩
        simp only [hf, Bool.true_and, Option.isNone_iff_eq_none] at h
        cases hc : ann.constRel? c with
        | none => exact absurd hc h
        | some _ => rfl
  obtain ⟨h₁, h₂, h₃⟩ := foldl_st (f := visitKey p ann ((annotated.get? c).getD []) prof lvls first)
    (P := fun key =>
      (first = true → ((annotated.get? c).getD []).contains key = true) ∧
      (((annotated.get? c).getD []).contains key = true →
        ∀ t, p.termOf key = some t → TermS p ann lvls prof [] t))
    (fun s k => by
      unfold visitKey
      split
      · split <;> rfl
      · cases p.termOf k <;> cases first <;> rfl)
    (fun s k => by
      unfold visitKey
      split
      · split <;> rfl
      · cases p.termOf k <;> cases first <;> rfl)
    (fun s k e => by
      unfold visitKey at e
      by_cases hm : ((annotated.get? c).getD []).contains k = true
      · simp only [hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at e
        refine ⟨?_, fun _ => hm, fun _ t ht => ?_⟩
        · cases ht' : p.termOf k with
          | none => rw [ht'] at e; cases first <;> exact e
          | some t' =>
            rw [ht'] at e
            dsimp only at e
            cases first <;> exact (term_nil _ _ _ _ e).1
        · rw [ht] at e
          dsimp only at e
          cases first <;> exact (term_nil _ _ _ _ e).2
      · have hm' : ((annotated.get? c).getD []).contains k = false := by simpa using hm
        simp only [hm', Bool.not_false, ↓reduceIte] at e
        cases first with
        | true => cases e
        | false => exact ⟨e, fun h => Bool.noConfusion h, fun h => absurd h hm⟩) (p.runtimeKeys c) s₁
  refine ⟨h₁.trans hs₁seen, h₂.trans hs₁ord, rfl, fun e => ?_⟩
  obtain ⟨h₄, h₅⟩ := subsingletonFields_nil p ann c prof _ e
  obtain ⟨h₆, h₇⟩ := h₃ h₄
  obtain ⟨h₈, h₉⟩ := hs₁errs h₆
  exact ⟨h₈, fun hf => ⟨h₉ hf, fun k hk => (h₇ k hk).1 hf⟩, fun k hk hm => (h₇ k hk).2 hm, h₅⟩

/-! ## The records -/

theorem records_nil {p : Program} {ann : Ann} (e : records p ann = []) : RecordsS p ann := by
  unfold records at e
  obtain ⟨-, h⟩ := foldl_nil (P := fun c =>
      (∀ rel, ann.constRel? c = some rel →
        rel.params.length ≤ ((p.decl? c).map fun d => d.type.piCount).getD 0 ∧
          ∀ r ∈ rel.result :: rel.params, relOk (lvlsOf p c) r = true) ∧
      (∀ rel, ann.ctorRel? c = some rel →
        ∃ sf lv ind cidx np nf ty, p.decl? c = some (.ctor sf lv ind cidx np nf ty) ∧
          rel.fields.length = nf ∧ ∀ cls ∈ rel.fields, pwOk (lvlsOf p c) cls.dropWhen = true))
    (fun errs c e => by
      dsimp only at e
      have hconst : ∀ (M : List RelError), M = [] →
          (M = (match ann.constRel? c with
            | some rel =>
              if (rel.result :: rel.params).all (relOk (lvlsOf p c)) = true then
                (if rel.params.length ≤ ((p.decl? c).map fun d => d.type.piCount).getD 0 then errs
                  else RelError.of "S1" "more parameter classes than binders" (some c) :: errs)
              else RelError.of "S1" "a parameter class names a level beyond the constant's" (some c) ::
                (if rel.params.length ≤ ((p.decl? c).map fun d => d.type.piCount).getD 0 then errs
                  else RelError.of "S1" "more parameter classes than binders" (some c) :: errs)
            | none => errs)) →
          errs = [] ∧ ∀ rel, ann.constRel? c = some rel →
            rel.params.length ≤ ((p.decl? c).map fun d => d.type.piCount).getD 0 ∧
              ∀ r ∈ rel.result :: rel.params, relOk (lvlsOf p c) r = true := by
        intro M hM e'
        subst hM
        cases hco : ann.constRel? c with
        | none =>
          rw [hco] at e'
          exact ⟨e'.symm, fun _ h => by cases h⟩
        | some rel =>
          rw [hco] at e'
          dsimp only at e'
          split at e'
          · next hQ =>
            split at e'
            · next hP =>
              refine ⟨e'.symm, fun rel' h => ?_⟩
              cases h
              exact ⟨hP, fun r hr => List.all_eq_true.1 hQ r hr⟩
            · cases e'
          · cases e'
      cases hct : ann.ctorRel? c with
      | none =>
        rw [hct] at e
        dsimp only at e
        obtain ⟨h₁, h₂⟩ := hconst _ e rfl
        exact ⟨h₁, h₂, fun _ h => by cases h⟩
      | some rel =>
        rw [hct] at e
        dsimp only at e
        split at e
        · next sf lv ind cidx np nf ty hd =>
          split at e
          · next hA =>
            split at e
            · next hB =>
              obtain ⟨h₁, h₂⟩ := hconst _ e rfl
              refine ⟨h₁, h₂, fun rel' h => ?_⟩
              cases h
              exact ⟨sf, lv, ind, cidx, np, nf, ty, hd, beq_iff_eq.1 hB,
                fun cls hc => List.all_eq_true.1 hA cls hc⟩
            · cases e
          · cases e
        · cases e) _ _ e
  exact ⟨fun c hc => (h c (List.mem_range.2 hc)).1, fun c hc => (h c (List.mem_range.2 hc)).2⟩

/-! ## The annotation lookup -/

theorem annotated_inv {nodes : List (TermKey × List Tag)}
    {f : NatMap (List TermKey) → TermKey × List Tag → NatMap (List TermKey)}
    (hf : ∀ m x c k, k ∈ ((f m x).get? c).getD [] → k = x.1 ∨ k ∈ (m.get? c).getD []) :
    ∀ (l : List (TermKey × List Tag)) (m : NatMap (List TermKey)),
      (∀ c k, k ∈ (m.get? c).getD [] → ∃ tags, (k, tags) ∈ nodes) → (∀ x ∈ l, x ∈ nodes) →
      ∀ c k, k ∈ ((l.foldl f m).get? c).getD [] → ∃ tags, (k, tags) ∈ nodes
  | [], _, hm, _ => hm
  | x :: l, m, hm, hl => by
    rw [List.foldl_cons]
    refine annotated_inv hf l (f m x) (fun c k hk => ?_) (fun y hy => hl y (List.mem_cons_of_mem _ hy))
    rcases hf m x c k hk with h | h
    · subst h
      exact ⟨x.2, hl x List.mem_cons_self⟩
    · exact hm c k h

theorem mem_insert_cons {m : NatMap (List TermKey)} {c₀ c : Nat} {key k : TermKey}
    (hk : k ∈ ((m.insert c₀ (key :: (m.get? c₀).getD [])).get? c).getD []) :
    k = key ∨ k ∈ (m.get? c).getD [] := by
  rw [NatMap.get?_insert] at hk
  split at hk
  · next hc =>
    subst hc
    simpa only [Option.getD_some, List.mem_cons] using hk
  · exact Or.inr hk

/-! ## The closure loop -/

theorem Handled.mono {p : Program} {o o' : List Inst} {r : Inst} (h : Handled p o r)
    (ho : ∀ x ∈ o, x ∈ o') : Handled p o' r :=
  h.imp id (ho _)

/-- A reference handled, or still queued. -/
def Pending (p : Program) (order front back : List Inst) (r : Inst) : Prop :=
  Handled p order r ∨ r ∈ front ∨ r ∈ back

/-- What one visit establishes, with the check's annotation lookup. -/
structure Visited (p : Program) (ann : Ann) (annotated : NatMap (List TermKey)) (c : CId)
    (prof : Profile) : Prop where
  record : (ann.constRel? c).isSome = true
  marked : ∀ key ∈ p.runtimeKeys c, ((annotated.get? c).getD []).contains key = true
  terms : ∀ key ∈ p.runtimeKeys c, ∀ t, p.termOf key = some t →
    TermS p ann (lvlsOf p c) prof [] t
  sub : SubS p ann c prof

/-- The closure loop's invariant. -/
structure LoopInv (p : Program) (ann : Ann) (annotated : NatMap (List TermKey))
    (roots : List Inst) (s : St) (front back : List Inst) : Prop where
  seen : ∀ c prof, prof ∈ (s.seen.get? c).getD [] ↔ (c, prof) ∈ s.order
  closed : ∀ inst ∈ s.order, ∀ r ∈ p.instRefs inst.1 inst.2, Pending p s.order front back r
  roots : ∀ r ∈ roots, Pending p s.order front back r
  facts : s.errs = [] → ∀ inst ∈ s.order, Visited p ann annotated inst.1 inst.2

section Loop

variable (p : Program) (ann : Ann) (annotated : NatMap (List TermKey)) (roots : List Inst)

theorem LoopInv.transfer {s : St} {front back front' back' : List Inst}
    (h : LoopInv p ann annotated roots s front back)
    (hq : ∀ r, Pending p s.order front back r → Pending p s.order front' back' r) :
    LoopInv p ann annotated roots s front' back' :=
  ⟨h.seen, fun i hi r hr => hq r (h.closed i hi r hr), fun r hr => hq r (h.roots r hr), h.facts⟩

theorem loop_visit (s : St) (c : CId) (prof0 : Profile) (front back : List Inst)
    (hc : c < p.size) (hn : ((s.seen.get? c).getD []).contains (prof0.normalize (lvlsOf p c)) = false)
    (h : LoopInv p ann annotated roots s ((c, prof0) :: front) back) :
    LoopInv p ann annotated roots
      (visit p ann annotated c (prof0.normalize (lvlsOf p c)) (lvlsOf p c)
        ((s.seen.get? c).getD []).isEmpty
        { s with seen := s.seen.insert c (prof0.normalize (lvlsOf p c) :: (s.seen.get? c).getD []),
                 order := (c, prof0.normalize (lvlsOf p c)) :: s.order }).1
      front
      ((visit p ann annotated c (prof0.normalize (lvlsOf p c)) (lvlsOf p c)
        ((s.seen.get? c).getD []).isEmpty
        { s with seen := s.seen.insert c (prof0.normalize (lvlsOf p c) :: (s.seen.get? c).getD []),
                 order := (c, prof0.normalize (lvlsOf p c)) :: s.order }).2.reverse ++ back) := by
  obtain ⟨hv₁, hv₂, hv₃, hv₄⟩ := visit_spec p ann annotated c (prof0.normalize (lvlsOf p c))
    (lvlsOf p c) ((s.seen.get? c).getD []).isEmpty
    { s with seen := s.seen.insert c (prof0.normalize (lvlsOf p c) :: (s.seen.get? c).getD []),
             order := (c, prof0.normalize (lvlsOf p c)) :: s.order }
  rw [hv₃]
  generalize visit p ann annotated c (prof0.normalize (lvlsOf p c)) (lvlsOf p c)
    ((s.seen.get? c).getD []).isEmpty
    { s with seen := s.seen.insert c (prof0.normalize (lvlsOf p c) :: (s.seen.get? c).getD []),
             order := (c, prof0.normalize (lvlsOf p c)) :: s.order } = v at hv₁ hv₂ hv₄
  dsimp only at hv₁ hv₂ hv₄
  have hord : ∀ x ∈ s.order, x ∈ v.1.order := fun x hx => by
    rw [hv₂]; exact List.mem_cons_of_mem _ hx
  have hq : ∀ r, Pending p s.order ((c, prof0) :: front) back r →
      Pending p v.1.order front ((p.instRefs c (prof0.normalize (lvlsOf p c))).reverse ++ back) r := by
    intro r hr
    rcases hr with hr | hr | hr
    · exact Or.inl (hr.mono hord)
    · rcases List.mem_cons.1 hr with hr | hr
      · subst hr
        refine Or.inl (Or.inr ?_)
        rw [hv₂]
        exact List.mem_cons_self
      · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr (List.mem_append_right _ hr))
  refine ⟨fun c' prof' => ?_, fun i hi r hr => ?_, fun r hr => hq r (h.roots r hr), fun e i hi => ?_⟩
  · rw [hv₁, hv₂, NatMap.get?_insert]
    by_cases hc' : c' = c
    · subst hc'
      simp only [↓reduceIte, Option.getD_some, List.mem_cons, h.seen, Prod.mk.injEq, true_and]
    · simp only [hc', ↓reduceIte, h.seen, List.mem_cons, Prod.mk.injEq, false_and, false_or]
  · rw [hv₂] at hi
    rcases List.mem_cons.1 hi with hi | hi
    · subst hi
      exact Or.inr (Or.inr (List.mem_append_left _ (List.mem_reverse.2 hr)))
    · exact hq r (h.closed i hi r hr)
  · obtain ⟨e₁, hfirst, hterms, hsub⟩ := hv₄ e
    have e₀ : s.errs = [] := e₁
    rw [hv₂] at hi
    rcases List.mem_cons.1 hi with hi | hi
    · subst hi
      have hrm : (ann.constRel? c).isSome = true ∧
          ∀ key ∈ p.runtimeKeys c, ((annotated.get? c).getD []).contains key = true := by
        cases hs : ((s.seen.get? c).getD []) with
        | nil => exact hfirst (by rw [hs]; rfl)
        | cons q qs =>
          have hq' : (c, q) ∈ s.order := (h.seen c q).1 (by rw [hs]; exact List.mem_cons_self)
          have hvq := h.facts e₀ (c, q) hq'
          exact ⟨hvq.record, hvq.marked⟩
      exact ⟨hrm.1, hrm.2, fun key hk t ht => hterms key hk (hrm.2 key hk) t ht, hsub⟩
    · exact h.facts e₀ i hi

theorem loop_spec : ∀ (n : Nat) (s : St) (front back : List Inst),
    LoopInv p ann annotated roots s front back → (loop p ann annotated n s front back).errs = [] →
    LoopInv p ann annotated roots (loop p ann annotated n s front back) [] []
  | 0, s, front, back, _, e => by
    simp only [loop] at e
    cases e
  | n + 1, s, [], [], h, _ => by
    simp only [loop]
    exact h
  | n + 1, s, [], b :: bs, h, e => by
    simp only [loop] at e ⊢
    refine loop_spec n s _ [] (h.transfer p ann annotated roots fun r hr => ?_) e
    rcases hr with hr | hr | hr
    · exact Or.inl hr
    · cases hr
    · exact Or.inr (Or.inl (List.mem_reverse.2 hr))
  | n + 1, s, (c, prof0) :: front, back, h, e => by
    simp only [loop] at e ⊢
    split
    · next hskip =>
      simp only [hskip, ↓reduceIte] at e
      refine loop_spec n s front back (h.transfer p ann annotated roots fun r hr => ?_) e
      have hh : Handled p s.order (c, prof0) := by
        rcases Bool.or_eq_true_iff.1 hskip with hs | hs
        · exact Or.inl (of_decide_eq_true hs)
        · exact Or.inr ((h.seen c _).1 (List.contains_iff_mem.1 hs))
      rcases hr with hr | hr | hr
      · exact Or.inl hr
      · rcases List.mem_cons.1 hr with hr | hr
        · subst hr; exact Or.inl hh
        · exact Or.inr (Or.inl hr)
      · exact Or.inr (Or.inr hr)
    · next hskip =>
      simp only [hskip, Bool.false_eq_true, ↓reduceIte] at e
      have hs' := hskip
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at hs'
      exact loop_spec n _ front _ (loop_visit p ann annotated roots s c prof0 front back hs'.1
        (by simpa using hs'.2) h) e

end Loop

/-! ## Soundness -/

theorem wellAnnotated_of_loop {p : Program} {ann : Ann} {annotated : NatMap (List TermKey)}
    {roots : List Inst} (keys : List TermKey) (reached : List CId)
    (hann : ∀ c k, k ∈ (annotated.get? c).getD [] → ∃ tags, (k, tags) ∈ ann.nodes)
    (hroots : ∀ r ∈ p.roots, p.instOf r.2 [] ∈ roots)
    (e : (loop p ann annotated fuel {} roots []).errs = []) (hrec : records p ann = []) :
    WellAnnotated p ann
      { keys := keys, reached := reached,
        instances := (loop p ann annotated fuel {} roots []).order.reverse,
        consts := ann.consts, ctors := ann.ctors } := by
  have h0 : LoopInv p ann annotated roots {} roots [] :=
    ⟨fun c prof => (by simp [NatMap.get?]), fun _ h => (nomatch h),
      fun r hr => Or.inr (Or.inl hr), fun _ _ h => (nomatch h)⟩
  have hL := loop_spec p ann annotated roots fuel {} roots [] h0 e
  have hH : ∀ r, Pending p (loop p ann annotated fuel {} roots []).order [] [] r →
      Handled p (loop p ann annotated fuel {} roots []).order.reverse r := by
    intro r hr
    rcases hr with hr | hr | hr
    · exact hr.mono fun x hx => List.mem_reverse.2 hx
    · cases hr
    · cases hr
  refine ⟨rfl, rfl, records_nil hrec, fun i hi => ?_, fun r hr => hH _ (hL.roots _ (hroots r hr)),
    fun i hi r hr => hH _ (hL.closed i (List.mem_reverse.1 hi) r hr)⟩
  have hv := hL.facts e i (List.mem_reverse.1 hi)
  refine ⟨hv.record, fun key hk => ?_, hv.terms, hv.sub⟩
  obtain ⟨b, hb, hkb⟩ := contains_mem (hv.marked key hk)
  rw [TermKey.eq_of_beq hkb]
  exact hann _ _ hb

theorem errs_nil {xs ys : List RelError} (h : ¬(!(xs.reverse ++ ys.reverse).isEmpty) = true) :
    xs = [] ∧ ys = [] := by
  cases xs with
  | nil =>
    cases ys with
    | nil => exact ⟨rfl, rfl⟩
    | cons y ys => simp at h
  | cons x xs => simp at h

/-- **`check_sound`**: an accepted annotation is well annotated (tier S). -/
theorem check_sound {p : Program} {ann : Ann} {c : Checked} (h : check p ann = .ok c) :
    WellAnnotated p ann c := by
  unfold check at h
  dsimp only at h
  split at h
  · cases h
  · next he =>
    injection h with h
    subst h
    obtain ⟨e₁, e₂⟩ := errs_nil he
    refine wellAnnotated_of_loop _ _ ?_ ?_ e₁ e₂
    · refine annotated_inv (fun m x c k hk => ?_) ann.nodes NatMap.leaf
        (fun c k hk => by simp [NatMap.get?] at hk) (fun x hx => hx)
      exact mem_insert_cons hk
    · intro r hr
      obtain ⟨a, b⟩ := r
      exact List.mem_map.2 ⟨(a, b), hr, rfl⟩

end Compilatrix.Src.Relevance.Proof
