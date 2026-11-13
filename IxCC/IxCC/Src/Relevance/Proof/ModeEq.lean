import IxCC.Src.Proof.Lazify
import IxCC.Src.Proof.TermBEq
import IxCC.Src.Relevance.Check

/-! # The relevance checks do not read application modes

`Src.Lazify` changes only the modes of application nodes (`Program.ModeEq`), after the checks have
run on the installed program. This module proves that the checks would have given the same verdict
on any program equal to it up to modes: `check_modeEq` (`check p₀ ann = check p ann`) and
`checkCanonical_modeEq`, for `Program.ModeEq p₀ p`. With L1 (`check_soundC`,
`checkCanonical_sound`) on `p`, the facts the checks establish hold of the program SrcEval runs.

Every function the checks call on the program is shown to give the same answer, or a term equal
up to modes, on `p₀` and `p` and on arguments equal up to modes. One comparison reads modes:
`applyPis`'s loop test `whnfType p 4 ty == ty`. On the two programs the tests can disagree only when
a four-step reduction returns its input up to modes (a cycle through a definition that unfolds to
itself), and then neither side ever reaches a sort or a Π: `applyPis_cycle`, by induction on the
fuel. -/

set_option autoImplicit false

namespace IxCC.Src.Relevance.Proof.ModeEq

open IxCC.Src
open IxCC.Src.Relevance.Check IxCC.Src.Relevance.Check.Canonical
open IxCC.Ixon (Univ)

/-! ## Terms equal up to modes -/

abbrev ME := Term.ModeEq

theorem ME.symm {t u : Term} (h : ME t u) : ME u t := by
  induction h with
  | var i => exact .var i
  | sort u => exact .sort u
  | const c us => exact .const c us
  | app m m' r _ _ ihf iha => exact .app m' m r ihf iha
  | lam bd _ _ ihd iht => exact .lam bd ihd iht
  | pi bd res _ _ ihd iht => exact .pi bd res ihd iht
  | letE c r _ _ _ ih₁ ih₂ ih₃ => exact .letE c r ih₁ ih₂ ih₃
  | proj s i _ ih => exact .proj s i ih
  | natLit n => exact .natLit n
  | strLit s => exact .strLit s

theorem liftTerm_me {t u : Term} (h : ME t u) : ∀ (n k : Nat), ME (liftTerm n k t) (liftTerm n k u) := by
  induction h with
  | app m m' r _ _ ihf iha => intro n k; exact .app m m' r (ihf n k) (iha n k)
  | lam bd _ _ ihd iht => intro n k; exact .lam bd (ihd n k) (iht n (k + 1))
  | pi bd res _ _ ihd iht => intro n k; exact .pi bd res (ihd n k) (iht n (k + 1))
  | letE c r _ _ _ ih₁ ih₂ ih₃ => intro n k; exact .letE c r (ih₁ n k) (ih₂ n k) (ih₃ n (k + 1))
  | proj s i _ ih => intro n k; exact .proj s i (ih n k)
  | var | sort | const | natLit | strLit => intro n k; exact Term.ModeEq.refl _

theorem substTerm_me {a b : Term} (hab : ME a b) {t u : Term} (h : ME t u) :
    ∀ k : Nat, ME (substTerm a k t) (substTerm b k u) := by
  induction h with
  | var i =>
    intro k
    simp only [substTerm]
    split
    · exact liftTerm_me hab k 0
    · exact Term.ModeEq.refl _
  | app m m' r _ _ ihf iha => intro k; exact .app m m' r (ihf k) (iha k)
  | lam bd _ _ ihd iht => intro k; exact .lam bd (ihd k) (iht (k + 1))
  | pi bd res _ _ ihd iht => intro k; exact .pi bd res (ihd k) (iht (k + 1))
  | letE c r _ _ _ ih₁ ih₂ ih₃ => intro k; exact .letE c r (ih₁ k) (ih₂ k) (ih₃ (k + 1))
  | proj s i _ ih => intro k; exact .proj s i (ih k)
  | sort | const | natLit | strLit => intro k; exact Term.ModeEq.refl _

theorem instUnivsTerm_me (us : List Univ) {t u : Term} (h : ME t u) :
    ME (instUnivsTerm us t) (instUnivsTerm us u) := by
  induction h with
  | app m m' r _ _ ihf iha => exact .app m m' r ihf iha
  | lam bd _ _ ihd iht => exact .lam bd ihd iht
  | pi bd res _ _ ihd iht => exact .pi bd res ihd iht
  | letE c r _ _ _ ih₁ ih₂ ih₃ => exact .letE c r ih₁ ih₂ ih₃
  | proj s i _ ih => exact .proj s i ih
  | var | sort | const | natLit | strLit => exact Term.ModeEq.refl _

/-- Argument lists with the same relevance tags and terms equal up to modes. -/
inductive ArgsME : List Term.Arg → List Term.Arg → Prop
  | nil : ArgsME [] []
  | cons {a b : Term} {m m' : Mode} {r : Rel} {xs ys : List Term.Arg} :
      ME a b → ArgsME xs ys → ArgsME ((a, m, r) :: xs) ((b, m', r) :: ys)

theorem ArgsME.refl : ∀ xs : List Term.Arg, ArgsME xs xs
  | [] => .nil
  | (a, _, _) :: xs => .cons (Term.ModeEq.refl a) (ArgsME.refl xs)

theorem ArgsME.symm {xs ys : List Term.Arg} (h : ArgsME xs ys) : ArgsME ys xs := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (ME.symm hab) ih

theorem ArgsME.length_eq {xs ys : List Term.Arg} (h : ArgsME xs ys) : xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem ArgsME.isEmpty_eq {xs ys : List Term.Arg} (h : ArgsME xs ys) : xs.isEmpty = ys.isEmpty := by
  cases h <;> rfl

theorem ArgsME.rels {xs ys : List Term.Arg} (h : ArgsME xs ys) :
    xs.map (·.2.2) = ys.map (·.2.2) := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem ArgsME.getElem? {xs ys : List Term.Arg} (h : ArgsME xs ys) : ∀ i : Nat,
    (xs[i]? = none ∧ ys[i]? = none) ∨
    ∃ a b m m' r, xs[i]? = some (a, m, r) ∧ ys[i]? = some (b, m', r) ∧ ME a b := by
  induction h with
  | nil => intro i; left; simp
  | cons hab _ ih =>
    intro i
    cases i with
    | zero => right; exact ⟨_, _, _, _, _, rfl, rfl, hab⟩
    | succ i => simpa using ih i

theorem ArgsME.drop {xs ys : List Term.Arg} (h : ArgsME xs ys) : ∀ n : Nat,
    ArgsME (xs.drop n) (ys.drop n) := by
  induction h with
  | nil => intro n; simpa using ArgsME.nil
  | cons hab hr ih =>
    intro n
    cases n with
    | zero => exact .cons hab hr
    | succ n => simpa using ih n

theorem ArgsME.take {xs ys : List Term.Arg} (h : ArgsME xs ys) : ∀ n : Nat,
    ArgsME (xs.take n) (ys.take n) := by
  induction h with
  | nil => intro n; simpa using ArgsME.nil
  | cons hab _ ih =>
    intro n
    cases n with
    | zero => simpa using ArgsME.nil
    | succ n => simpa using ArgsME.cons hab (ih n)

theorem ArgsME.append {xs ys xs' ys' : List Term.Arg} (h : ArgsME xs ys) (h' : ArgsME xs' ys') :
    ArgsME (xs ++ xs') (ys ++ ys') := by
  induction h with
  | nil => simpa using h'
  | cons hab _ ih => exact .cons hab ih

theorem mkApps_me {h h' : Term} (hh : ME h h') {xs ys : List Term.Arg} (hx : ArgsME xs ys) :
    ME (Term.mkApps h xs) (Term.mkApps h' ys) := by
  induction hx generalizing h h' with
  | nil => exact hh
  | cons hab _ ih =>
    simp only [Term.mkApps, List.foldl_cons]
    exact ih (.app _ _ _ hh hab)

theorem spine_go_me {t u : Term} (h : ME t u) : ∀ {acc acc' : List Term.Arg}, ArgsME acc acc' →
    ME (Term.spine.go t acc).1 (Term.spine.go u acc').1 ∧
      ArgsME (Term.spine.go t acc).2 (Term.spine.go u acc').2 := by
  induction h with
  | app m m' r _ hab ihf _ => intro acc acc' hacc; exact ihf (.cons hab hacc)
  | var i => intro acc acc' hacc; exact ⟨.var i, hacc⟩
  | sort s => intro acc acc' hacc; exact ⟨.sort s, hacc⟩
  | const c us => intro acc acc' hacc; exact ⟨.const c us, hacc⟩
  | lam bd hd ht => intro acc acc' hacc; exact ⟨.lam bd hd ht, hacc⟩
  | pi bd res hd ht => intro acc acc' hacc; exact ⟨.pi bd res hd ht, hacc⟩
  | letE c r h₁ h₂ h₃ => intro acc acc' hacc; exact ⟨.letE c r h₁ h₂ h₃, hacc⟩
  | proj s i he => intro acc acc' hacc; exact ⟨.proj s i he, hacc⟩
  | natLit n => intro acc acc' hacc; exact ⟨.natLit n, hacc⟩
  | strLit s => intro acc acc' hacc; exact ⟨.strLit s, hacc⟩

theorem spine_me {t u : Term} (h : ME t u) :
    ME t.spine.1 u.spine.1 ∧ ArgsME t.spine.2 u.spine.2 :=
  spine_go_me h .nil

theorem betaApps_nil (t : Term) : betaApps t [] = t := by cases t <;> rfl

theorem betaApps_cons_nonlam {t : Term} (x : Term.Arg) (xs : List Term.Arg)
    (ht : ∀ b d body, t ≠ .lam b d body) : betaApps t (x :: xs) = Term.mkApps t (x :: xs) := by
  cases t with
  | lam b d body => exact absurd rfl (ht b d body)
  | _ => rfl

theorem me_lam_iff {t u : Term} (h : ME t u) : (∃ b d body, t = .lam b d body) ↔ ∃ b d body, u = .lam b d body := by
  cases h <;> simp

theorem betaApps_me {xs ys : List Term.Arg} (hx : ArgsME xs ys) :
    ∀ {t u : Term}, ME t u → ME (betaApps t xs) (betaApps u ys) := by
  induction hx with
  | nil => intro t u h; rw [betaApps_nil, betaApps_nil]; exact h
  | cons hab hr ih =>
    intro t u h
    by_cases hl : ∃ b d body, t = .lam b d body
    · obtain ⟨b, d, body, rfl⟩ := hl
      cases h with
      | lam bd hd hb => exact ih (substTerm_me hab hb 0)
    · have hu : ¬ ∃ b d body, u = .lam b d body := fun hu => hl ((me_lam_iff h).2 hu)
      rw [betaApps_cons_nonlam _ _ fun b d body he => hl ⟨b, d, body, he⟩,
        betaApps_cons_nonlam _ _ fun b d body he => hu ⟨b, d, body, he⟩]
      exact mkApps_me h (.cons hab hr)

theorem lamRels_me {t u : Term} (h : ME t u) : lamRels t = lamRels u := by
  induction h with
  | lam bd _ _ _ iht => simp [lamRels, iht]
  | _ => rfl

theorem mentionsVar_me {t u : Term} (h : ME t u) : ∀ k : Nat, mentionsVar k t = mentionsVar k u := by
  induction h with
  | app m m' r _ _ ihf iha => intro k; simp [mentionsVar, ihf, iha]
  | lam bd _ _ ihd iht => intro k; simp [mentionsVar, ihd, iht]
  | pi bd res _ _ ihd iht => intro k; simp [mentionsVar, ihd, iht]
  | letE c r _ _ _ ih₁ ih₂ ih₃ => intro k; simp [mentionsVar, ih₁, ih₂, ih₃]
  | proj s i _ ih => intro k; simp [mentionsVar, ih]
  | _ => intro k; rfl

theorem relevantRefs_me {t u : Term} (h : ME t u) :
    ∀ (prof : Profile) (acc : List Inst), t.relevantRefs prof acc = u.relevantRefs prof acc := by
  induction h with
  | app m m' r _ _ ihf iha => intro prof acc; simp [Term.relevantRefs, ihf, iha]
  | lam bd _ _ _ iht => intro prof acc; simp [Term.relevantRefs, iht]
  | letE c r _ _ _ _ ih₂ ih₃ => intro prof acc; simp [Term.relevantRefs, ih₂, ih₃]
  | proj s i _ ih => intro prof acc; simp [Term.relevantRefs, ih]
  | _ => intro prof acc; rfl

/-- Equal up to modes, under an option. -/
def OptME : Option Term → Option Term → Prop
  | some t, some u => ME t u
  | none, none => True
  | _, _ => False

theorem peelLamsN_me : ∀ (n : Nat) {t u : Term}, ME t u → OptME (peelLamsN n t) (peelLamsN n u)
  | 0, _, _, h => h
  | n + 1, _, _, h => by
    cases h with
    | lam bd _ hb => exact peelLamsN_me n hb
    | _ => trivial

theorem me_sort_iff {t u : Term} (h : ME t u) (s : Univ) : t = .sort s ↔ u = .sort s := by
  cases h <;> simp

theorem me_pi_iff {t u : Term} (h : ME t u) : (∃ b r d body, t = .pi b r d body) ↔ ∃ b r d body, u = .pi b r d body := by
  cases h <;> simp

theorem me_letE_iff {t u : Term} (h : ME t u) :
    (∃ c r ty v b, t = .letE c r ty v b) ↔ ∃ c r ty v b, u = .letE c r ty v b := by
  cases h <;> simp

/-- `.pis.2` of terms equal up to modes is a sort on both sides or on neither. -/
theorem pis_snd_me {t u : Term} (h : ME t u) : ME t.pis.2 u.pis.2 := by
  induction h with
  | pi bd res _ _ _ iht => exact iht
  | var i => exact .var i
  | sort s => exact .sort s
  | const c us => exact .const c us
  | app m m' r hf ha => exact .app m m' r hf ha
  | lam bd hd ht => exact .lam bd hd ht
  | letE c r h₁ h₂ h₃ => exact .letE c r h₁ h₂ h₃
  | proj s i he => exact .proj s i he
  | natLit n => exact .natLit n
  | strLit s => exact .strLit s

/-- The sort a term's conclusion is, as the classifier reads it (`dSort`). -/
def sortOf (t : Term) : Option Univ :=
  match t.pis.2 with
  | .sort u => some u
  | _ => none

theorem sortOf_me {t u : Term} (h : ME t u) : sortOf t = sortOf u := by
  have hp := pis_snd_me h
  simp only [sortOf]
  generalize t.pis.2 = a at hp
  generalize u.pis.2 = b at hp
  cases hp <;> rfl

/-! ## Programs equal up to modes -/

variable {p₀ p : Program}

/-- What `Program.ModeEq` says of one declaration, by cases. -/
theorem decl?_cases (hme : Program.ModeEq p₀ p) (c : CId) :
    p₀.decl? c = p.decl? c ∨
    (∃ k s l ty v v', p₀.decl? c = some (.defn k s l ty v) ∧ p.decl? c = some (.defn k s l ty v') ∧
      ME v v') ∨
    (∃ sf kk l np nmot nmin ni ind rs rs' ty,
      p₀.decl? c = some (.recr sf kk l np nmot nmin ni ind rs ty) ∧
      p.decl? c = some (.recr sf kk l np nmot nmin ni ind rs' ty) ∧ RulesModeEq rs rs') := by
  have he := hme.entry c
  simp only [Program.decl?]
  cases h₀ : p₀.entry? c with
  | none =>
    cases h : p.entry? c with
    | none => left; rfl
    | some e => rw [h₀, h] at he; exact he.elim
  | some e₀ =>
    cases h : p.entry? c with
    | none => rw [h₀, h] at he; exact he.elim
    | some e =>
      rw [h₀, h] at he
      obtain ⟨-, -, hd⟩ := he
      simp only [Option.map_some]
      generalize e₀.decl = d₀ at hd ⊢
      generalize e.decl = d at hd ⊢
      cases hd with
      | refl => left; rfl
      | defn k s l ty hv => right; left; exact ⟨_, _, _, _, _, _, rfl, rfl, hv⟩
      | recr sf kk l np nmot nmin ni ind ty hr =>
        right; right; exact ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, rfl, hr⟩

theorem decl?_type (hme : Program.ModeEq p₀ p) (c : CId) :
    (p₀.decl? c).map Decl.type = (p.decl? c).map Decl.type := by
  rcases decl?_cases hme c with h | ⟨k, s, l, ty, v, v', h₀, h, -⟩ |
      ⟨sf, kk, l, np, nmot, nmin, ni, ind, rs, rs', ty, h₀, h, -⟩
  · rw [h]
  · rw [h₀, h]; rfl
  · rw [h₀, h]; rfl

theorem decl?_lvls (hme : Program.ModeEq p₀ p) (c : CId) :
    (p₀.decl? c).map Decl.lvls = (p.decl? c).map Decl.lvls := by
  rcases decl?_cases hme c with h | ⟨k, s, l, ty, v, v', h₀, h, -⟩ |
      ⟨sf, kk, l, np, nmot, nmin, ni, ind, rs, rs', ty, h₀, h, -⟩
  · rw [h]
  · rw [h₀, h]; rfl
  · rw [h₀, h]; rfl

theorem recKindOf_eq (hme : Program.ModeEq p₀ p) (c : CId) :
    p₀.table.recKindOf c = p.table.recKindOf c := by
  simp only [Table.recKindOf, hme.recKind]

/-! ## The classifier: `whnfType`, `isTypeFormerP`, `applyPis` -/

/-- `whnfType`'s step at a term that is not a `let`. -/
def whnfBody (q : Program) (fuel : Nat) (t : Term) : Term :=
  match t.spine with
  | (head, args) =>
    match head with
    | .lam .. => if args.isEmpty then t else whnfType q fuel (betaApps head args)
    | .const c us =>
      match q.decl? c with
      | some (.defn .defn .safe _ _ val) => whnfType q fuel (betaApps (instUnivsTerm us val) args)
      | _ => t
    | _ => t

theorem whnfType_succ (q : Program) (fuel : Nat) {t : Term}
    (ht : ¬ ∃ c r ty v b, t = .letE c r ty v b) : whnfType q (fuel + 1) t = whnfBody q fuel t := by
  cases t with
  | letE c r ty v b => exact absurd ⟨c, r, ty, v, b, rfl⟩ ht
  | _ => rfl

theorem whnfType_me (hme : Program.ModeEq p₀ p) :
    ∀ (n : Nat) {t u : Term}, ME t u → ME (whnfType p₀ n t) (whnfType p n u)
  | 0, _, _, h => h
  | n + 1, t, u, h => by
    by_cases hl : ∃ c r ty v b, t = .letE c r ty v b
    · obtain ⟨c, r, ty, v, b, rfl⟩ := hl
      cases h with
      | letE _ _ hty hv hb => exact whnfType_me hme n (substTerm_me hv hb 0)
    · have hu : ¬ ∃ c r ty v b, u = .letE c r ty v b := fun hu => hl ((me_letE_iff h).2 hu)
      rw [whnfType_succ _ _ hl, whnfType_succ _ _ hu]
      obtain ⟨hh, ha⟩ := spine_me h
      unfold whnfBody
      generalize t.spine = s₀ at hh ha ⊢
      generalize u.spine = s₁ at hh ha ⊢
      obtain ⟨h₀, a₀⟩ := s₀
      obtain ⟨h₁, a₁⟩ := s₁
      dsimp only at hh ha ⊢
      cases hh with
      | lam bd hd hb =>
        rw [ha.isEmpty_eq]
        cases a₁.isEmpty
        · exact whnfType_me hme n (betaApps_me ha (.lam bd hd hb))
        · exact h
      | const c us =>
        dsimp only
        rcases decl?_cases hme c with hc | ⟨k, s, l, ty, v, v', hc₀, hc, hv⟩ |
            ⟨sf, kk, l, np, nmot, nmin, ni, ind, rs, rs', ty, hc₀, hc, -⟩
        · rw [hc]
          split
          · exact whnfType_me hme n (betaApps_me ha (instUnivsTerm_me us (Term.ModeEq.refl _)))
          · exact h
        · rw [hc₀, hc]
          cases k <;> cases s <;>
            first
            | exact whnfType_me hme n (betaApps_me ha (instUnivsTerm_me us hv))
            | exact h
        · rw [hc₀, hc]
          exact h
      | _ => exact h

theorem whnfType_me_refl (q : Program) (n : Nat) {t u : Term} (h : ME t u) :
    ME (whnfType q n t) (whnfType q n u) :=
  whnfType_me (Program.ModeEq.refl q) n h

/-- Classifier contexts equal up to modes: the same sorts, the types equal up to modes. -/
inductive CtxME : List (Term × Option Univ) → List (Term × Option Univ) → Prop
  | nil : CtxME [] []
  | cons {a b : Term} {s : Option Univ} {xs ys : List (Term × Option Univ)} :
      ME a b → CtxME xs ys → CtxME ((a, s) :: xs) ((b, s) :: ys)

theorem CtxME.refl : ∀ xs : List (Term × Option Univ), CtxME xs xs
  | [] => .nil
  | (a, _) :: xs => .cons (Term.ModeEq.refl a) (CtxME.refl xs)

theorem CtxME.getElem? {xs ys : List (Term × Option Univ)} (h : CtxME xs ys) : ∀ i : Nat,
    (xs[i]? = none ∧ ys[i]? = none) ∨
    ∃ a b s, xs[i]? = some (a, s) ∧ ys[i]? = some (b, s) ∧ ME a b := by
  induction h with
  | nil => intro i; left; simp
  | cons hab _ ih =>
    intro i
    cases i with
    | zero => right; exact ⟨_, _, _, rfl, rfl, hab⟩
    | succ i => simpa using ih i

theorem isTypeFormerP_me (hme : Program.ModeEq p₀ p) :
    ∀ (n : Nat) (ctx₀ ctx : List (Term × Option Univ)) {t u : Term}, ME t u →
      isTypeFormerP p₀ ctx₀ n t = isTypeFormerP p ctx n u
  | 0, _, _, _, _, _ => rfl
  | n + 1, ctx₀, ctx, t, u, h => by
    have hw := whnfType_me hme 8 h
    simp only [isTypeFormerP]
    generalize whnfType p₀ 8 t = w₀ at hw
    generalize whnfType p 8 u = w at hw
    cases hw with
    | pi bd res hd hb => exact isTypeFormerP_me hme n _ _ hb
    | _ => rfl

/-! ### `applyPis`: the loop test compares modes -/

/-- `applyPis`'s last case: neither a sort with no argument left nor a Π with one. -/
abbrev Plain (ty : Term) (rest : List Term.Arg) : Prop :=
  (∀ s, ty = .sort s → rest ≠ []) ∧ (∀ b r d body, ty = .pi b r d body → rest = [])

theorem applyPis_plain (q : Program) (k : Nat) {ty : Term} {rest : List Term.Arg} (h : Plain ty rest) :
    applyPis q (k + 1) ty rest =
      if whnfType q 4 ty == ty then none else applyPis q k (whnfType q 4 ty) rest := by
  obtain ⟨h₁, h₂⟩ := h
  cases ty <;> cases rest <;>
    first
    | rfl
    | exact absurd rfl (h₁ _ rfl)
    | exact absurd (h₂ _ _ _ _ rfl) (List.cons_ne_nil _ _)

theorem Plain.of_me {t u : Term} (h : ME t u) {rest rest' : List Term.Arg} (hr : ArgsME rest rest')
    (hp : Plain u rest') : Plain t rest := by
  obtain ⟨h₁, h₂⟩ := hp
  refine ⟨fun s hs => ?_, fun b r d body hb => ?_⟩
  · subst hs
    cases h with
    | sort => intro he; subst he; cases hr; exact h₁ s rfl rfl
  · subst hb
    cases h with
    | pi bd res hd ht => have := h₂ _ _ _ _ rfl; subst this; cases hr; rfl

/-- **The cycle.** If a four-step reduction returns `v` up to modes, `applyPis` from any term
equal to `v` up to modes never reaches a sort or a Π: every iteration returns a term equal to `v`
up to modes, so the loop ends by its test or its fuel. -/
theorem applyPis_cycle (q : Program) {v : Term} {rest : List Term.Arg} (hv : Plain v rest)
    (hw : ME (whnfType q 4 v) v) : ∀ (k : Nat) {u : Term}, ME u v → applyPis q k u rest = none
  | 0, _, _ => rfl
  | k + 1, u, hu => by
    rw [applyPis_plain q k (Plain.of_me hu (ArgsME.refl rest) hv)]
    split
    · rfl
    · exact applyPis_cycle q hv hw k ((whnfType_me_refl q 4 hu).trans hw)

/-- **`applyPis` does not see modes.** The loop test may disagree on the two programs; then one
side returned its input, so both sides are in a cycle (`applyPis_cycle`) and return `none`. -/
theorem applyPis_me (hme : Program.ModeEq p₀ p) :
    ∀ (k : Nat) {ty₀ ty : Term} {r₀ r : List Term.Arg}, ME ty₀ ty → ArgsME r₀ r →
      applyPis p₀ k ty₀ r₀ = applyPis p k ty r
  | 0, _, _, _, _, _, _ => rfl
  | k + 1, ty₀, ty, r₀, r, h, hr => by
    by_cases hp : Plain ty r
    · have hp₀ := Plain.of_me h hr hp
      rw [applyPis_plain p₀ k hp₀, applyPis_plain p k hp]
      have hw := whnfType_me hme 4 h
      cases e₀ : (whnfType p₀ 4 ty₀ == ty₀) <;> cases e : (whnfType p 4 ty == ty)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact applyPis_me hme k hw hr
      · -- `p` returned its input: `p₀`'s next term is `ty₀` up to modes, a cycle
        simp only [Bool.false_eq_true, ↓reduceIte]
        have he : whnfType p 4 ty = ty := eq_of_beq e
        rw [he] at hw
        have hc : ME (whnfType p₀ 4 ty₀) ty₀ := hw.trans (ME.symm h)
        exact applyPis_cycle p₀ hp₀ hc k hc
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have he : whnfType p₀ 4 ty₀ = ty₀ := eq_of_beq e₀
        rw [he] at hw
        have hc : ME (whnfType p 4 ty) ty := (ME.symm hw).trans h
        exact (applyPis_cycle p hp hc k hc).symm
      · rfl
    · -- a sort with no argument left, or a Π with one: the same case on both sides
      cases h with
      | sort s =>
        cases hr with
        | nil => rfl
        | cons hab hr' =>
          exact absurd ⟨fun _ _ => List.cons_ne_nil _ _, fun _ _ _ _ he => (by cases he)⟩ hp
      | pi bd res hd hbody =>
        cases hr with
        | nil => exact absurd ⟨fun _ he => (by cases he), fun _ _ _ _ _ => rfl⟩ hp
        | cons hab hr' => exact applyPis_me hme k (substTerm_me hab hbody 0) hr'
      | _ => exact absurd ⟨fun _ he => (by cases he), fun _ _ _ _ he => (by cases he)⟩ hp

/-! ### The rest of the classifier -/

theorem projFieldSort?_eq (hme : Program.ModeEq p₀ p) (s i n : Nat) :
    projFieldSort? p₀ s i n = projFieldSort? p s i n := sorry

theorem inferTypeSort_me (hme : Program.ModeEq p₀ p) :
    ∀ (n : Nat) {ctx₀ ctx : List (Term × Option Univ)}, CtxME ctx₀ ctx → ∀ {t u : Term}, ME t u →
      inferTypeSort p₀ ctx₀ n t = inferTypeSort p ctx n u := sorry

theorem classifyDomain_me (hme : Program.ModeEq p₀ p) {ctx₀ ctx : List (Term × Option Univ)}
    (hc : CtxME ctx₀ ctx) (b : Binder) {t u : Term} (h : ME t u) :
    classifyDomain p₀ ctx₀ b t = classifyDomain p ctx b u := sorry

theorem classifyTelescope_me (hme : Program.ModeEq p₀ p) :
    ∀ (n : Nat) {ctx₀ ctx : List (Term × Option Univ)}, CtxME ctx₀ ctx → ∀ {t u : Term}, ME t u →
      classifyTelescope p₀ ctx₀ n t = classifyTelescope p ctx n u := sorry

theorem checkTermBinders_me (hme : Program.ModeEq p₀ p) (ann : Ann) :
    ∀ {t u : Term} {ctx₀ ctx : List (Term × Option Univ)} {xs ys : List Term.Arg}, ME t u →
      CtxME ctx₀ ctx → ArgsME xs ys → checkTermBinders p₀ ann ctx₀ t xs = checkTermBinders p ann ctx u ys :=
  sorry

/-! ## The program's other readers -/

theorem resolveOf_cases (hme : Program.ModeEq p₀ p) (c : CId) :
    p₀.table.resolveOf c = p.table.resolveOf c ∨
    ∃ thm b b', p₀.table.resolveOf c = some (.eqn thm b) ∧ p.table.resolveOf c = some (.eqn thm b') ∧
      ME b b' := by
  have hr := hme.resolve c
  generalize p₀.table.resolveOf c = r₀ at hr ⊢
  generalize p.table.resolveOf c = r at hr ⊢
  cases hr with
  | refl => left; rfl
  | eqn thm hb => right; exact ⟨_, _, _, rfl, rfl, hb⟩

theorem short_eq (hme : Program.ModeEq p₀ p) (c : CId) : p₀.short c = p.short c := sorry
theorem elimShape?_eq (hme : Program.ModeEq p₀ p) (c : CId) : elimShape? p₀ c = elimShape? p c := sorry
theorem ruleCtorFields_eq (hme : Program.ModeEq p₀ p) (ann : Ann) (r j : Nat) :
    ruleCtorFields p₀ ann r j = ruleCtorFields p ann r j := sorry
theorem ctorProfile_eq (hme : Program.ModeEq p₀ p) (r : CId) (q : Profile) :
    ctorProfile p₀ r q = ctorProfile p r q := sorry
theorem onlyCtor?_eq (hme : Program.ModeEq p₀ p) (s : CId) : onlyCtor? p₀ s = onlyCtor? p s := sorry
theorem fieldWrittenErased_eq (hme : Program.ModeEq p₀ p) (k i : Nat) :
    fieldWrittenErased p₀ k i = fieldWrittenErased p k i := sorry
theorem erasedMinors_eq (hme : Program.ModeEq p₀ p) (shape : ElimShape) :
    erasedMinors p₀ shape = erasedMinors p shape := sorry
theorem readsErased?_eq (hme : Program.ModeEq p₀ p) (ann : Ann) (c : CId) :
    readsErased? p₀ ann c = readsErased? p ann c := sorry
theorem forwardsErased?_eq (hme : Program.ModeEq p₀ p) (r : CId) :
    forwardsErased? p₀ r = forwardsErased? p r := sorry
theorem redirectsErased?_eq (hme : Program.ModeEq p₀ p) (c : CId) :
    redirectsErased? p₀ c = redirectsErased? p c := sorry
theorem rulesShape?_eq (hme : Program.ModeEq p₀ p) (r : CId) : rulesShape? p₀ r = rulesShape? p r := sorry
theorem univsErrs_eq (hme : Program.ModeEq p₀ p) (c : CId) : univsErrs p₀ c = univsErrs p c := sorry
theorem subsingletonSrcs?_eq (hme : Program.ModeEq p₀ p) (r : CId) :
    subsingletonSrcs? p₀ r = subsingletonSrcs? p r := sorry
theorem runtimeKeys_eq (hme : Program.ModeEq p₀ p) (c : CId) : p₀.runtimeKeys c = p.runtimeKeys c := sorry
theorem instOf_eq (hme : Program.ModeEq p₀ p) (c : CId) (prof : Profile) :
    p₀.instOf c prof = p.instOf c prof := sorry
theorem instRefs_eq (hme : Program.ModeEq p₀ p) (c : CId) (prof : Profile) :
    p₀.instRefs c prof = p.instRefs c prof := sorry
theorem subsingletonFields_eq (hme : Program.ModeEq p₀ p) (ann : Ann) (r : CId) (q : Profile)
    (errs : List RelError) : subsingletonFields p₀ ann r q errs = subsingletonFields p ann r q errs := sorry
theorem records_eq (hme : Program.ModeEq p₀ p) (ann : Ann) : records p₀ ann = records p ann := sorry

theorem termOf_me (hme : Program.ModeEq p₀ p) (key : TermKey) : OptME (p₀.termOf key) (p.termOf key) := by
  cases h₀ : p₀.termOf key with
  | some t =>
    obtain ⟨t', h, hm⟩ := hme.termOf h₀
    rw [h]; exact hm
  | none =>
    cases h : p.termOf key with
    | none => trivial
    | some t =>
      obtain ⟨t', h', _⟩ := (Program.ModeEq.symm' hme).termOf h
      rw [h₀] at h'; cases h'

/-- Run bodies with the same keys and terms equal up to modes. -/
inductive BodiesME : List (TermKey × Term) → List (TermKey × Term) → Prop
  | nil : BodiesME [] []
  | cons {k : TermKey} {t u : Term} {xs ys : List (TermKey × Term)} :
      ME t u → BodiesME xs ys → BodiesME ((k, t) :: xs) ((k, u) :: ys)

theorem runBodies_me (hme : Program.ModeEq p₀ p) (c : CId) : BodiesME (runBodies p₀ c) (runBodies p c) :=
  sorry

/-! ## `check` -/

section check

variable (ann : Ann) (key : TermKey) (lvls : Nat) (prof : Profile)

theorem term_me (hme : Program.ModeEq p₀ p) {t u : Term} (h : ME t u) :
    ∀ (bs : List Rel) (errs : List RelError),
      Check.term ⟨p₀, ann, key, lvls, prof⟩ bs errs t = Check.term ⟨p, ann, key, lvls, prof⟩ bs errs u ∧
      Check.rest ⟨p₀, ann, key, lvls, prof⟩ bs errs t = Check.rest ⟨p, ann, key, lvls, prof⟩ bs errs u :=
  sorry

theorem visitKey_eq (hme : Program.ModeEq p₀ p) (marked : List TermKey) (first : Bool) :
    visitKey p₀ ann marked prof lvls first = visitKey p ann marked prof lvls first := by
  funext s key
  unfold visitKey
  have hk := termOf_me hme key
  generalize p₀.termOf key = o₀ at hk ⊢
  generalize p.termOf key = o at hk ⊢
  cases o₀ <;> cases o
  · rfl
  · exact hk.elim
  · exact hk.elim
  · rename_i t₀ t
    simp only [(term_me ann key lvls prof hme hk [] _).1]

theorem visit_eq (hme : Program.ModeEq p₀ p) (annotated : NatMap (List TermKey)) (c : CId)
    (first : Bool) (s : St) :
    visit p₀ ann annotated c prof lvls first s = visit p ann annotated c prof lvls first s := by
  simp only [visit, runtimeKeys_eq hme, visitKey_eq ann lvls prof hme, subsingletonFields_eq hme,
    instRefs_eq hme]

theorem loop_eq (hme : Program.ModeEq p₀ p) (annotated : NatMap (List TermKey)) :
    ∀ (n : Nat) (s : St) (front back : List Inst),
      loop p₀ ann annotated n s front back = loop p ann annotated n s front back
  | 0, _, _, _ => rfl
  | n + 1, s, front, back => by
    simp only [loop, decl?_lvls hme, hme.size, visit_eq ann _ _ hme, loop_eq hme annotated n]

end check

/-- **`check` does not read modes.** -/
theorem check_modeEq (hme : Program.ModeEq p₀ p) (ann : Ann) : check p₀ ann = check p ann := by
  simp only [check, hme.roots, instOf_eq hme, loop_eq ann hme, records_eq hme]

/-- `check`'s reached constants are its instances' constants. -/
theorem check_reached {q : Program} {ann : Ann} {ch : Checked} (h : check q ann = .ok ch) :
    ∀ inst ∈ ch.instances, inst.1 ∈ ch.reached := sorry

/-! ## `checkCanonical` -/

namespace CC

/-! `checkCanonical`'s clauses, copied (`checkCanonical_split` checks the copies by `rfl`). -/

def okConsts (p : Program) (ann : Ann) : Bool :=
  ann.consts.toList.all fun (c, cr) =>
    match p.decl? c with
    | some d =>
      let (ps, res) := classifyTelescope p [] (d.type.piCount + 1) d.type
      let okPrim := match p.table.resolveOf c with
        | some (.prim op) => cr.result == .rel && cr.params == List.replicate op.arity .rel
        | some (.word _ op _) => cr.result == .rel && cr.params == List.replicate op.arity .rel
        | _ => true
      okPrim &&
      cr.params.length == ps.length &&
      (cr.params.zip ps).all (fun (actual, (b, exp)) =>
        tagOk b exp false actual) &&
      (match res with | some e => cr.result == e | none => cr.result == .rel)
    | none => false

def okCtors (p : Program) (ann : Ann) : Bool :=
  ann.ctors.toList.all fun (c, kr) =>
    match p.decl? c with
    | some (.ctor _ _ _ _ np nf ty) =>
      let (ps, _) := classifyTelescope p [] (ty.piCount + 1) ty
      let flds := ps.drop np
      let okWithConst := match ann.constRel? c with
        | some cr => (cr.params.drop np).map FieldClass.ofRel == kr.fields
        | none => true
      okWithConst &&
      kr.fields.length == nf &&
      flds.length == nf &&
      (kr.fields.zip flds).all (fun (actual, (b, exp)) =>
        actual != .proof .never &&
          if b.contract.uses == .erased then actual.alwaysDropped
          else match exp with | some e => actual == FieldClass.ofRel e | none => actual == .keep)
    | _ => false

def headerErrs (p : Program) (ann : Ann) (ch : Checked) : List RelError :=
  ch.reached.flatMap fun c =>
    match ann.constRel? c, p.decl? c with
    | some cr, some d =>
      let redirect := match p.table.resolveOf c with
        | some (.csimp g us _) =>
          (headerAgreement d.type (.const g us) cr.params s!"the csimp redirect to {p.short g}").toList.map
            fun msg => RelError.of "S1" msg (some c)
        | _ => []
      redirect ++ (runBodies p c).filterMap fun (key, t) =>
        (headerAgreement d.type t cr.params).map fun msg => RelError.of "S1" msg none (some key)
    | _, _ => []

def readErrs (p : Program) (ann : Ann) (ch : Checked) : List RelError :=
  ch.reached.filterMap fun c =>
    (readsErased? p ann c).map fun msg => RelError.of "S1" msg (some c)

def forwardErrs (p : Program) (ch : Checked) : List RelError :=
  ch.reached.filterMap fun c =>
    (forwardsErased? p c).map fun msg => RelError.of "S1" msg (some c)

def redirectErrs (p : Program) (ch : Checked) : List RelError :=
  ch.reached.filterMap fun c =>
    (redirectsErased? p c).map fun msg => RelError.of "C3" msg (some c)

def okReached (p : Program) (ann : Ann) (ch : Checked) : Bool :=
  ch.reached.all fun c =>
    match ann.constRel? c with
    | none => false
    | some _ =>
      let ruleTerms : List Term :=
        match p.decl? c with
        | some (.recr _ _ _ _ _ _ _ _ rules _) => rules.map (·.rhs)
        | _ => []
      ((runBodies p c).all fun (_, t) => checkTermBinders p ann [] t []) &&
      (ruleTerms.all fun t => checkTermBinders p ann [] t [])

def denseErrs (p : Program) : List RelError :=
  if p.consts.toList.all (·.1 < p.size) && p.table.resolve.toList.all (·.1 < p.size) then []
  else [RelError.of "S1" "a constant or table entry at or above the program's size: the \
    closure walk skips it, and SrcEval would run it unchecked"]

def ruleErrs (p : Program) (ch : Checked) : List RelError :=
  ch.reached.filterMap fun c =>
    match elimShape? p c with
    | some shape => (rulesShape? p shape.recr).map fun msg => RelError.of "S1" msg (some shape.recr)
    | none => none

def univErrs (p : Program) (ch : Checked) : List RelError := ch.reached.flatMap (univsErrs p)

def recordErrs (p : Program) (ann : Ann) (ch : Checked) : List RelError :=
  ch.reached.filterMap fun c =>
    match p.decl? c, ann.ctorRel? c with
    | some (.ctor ..), none =>
      some (RelError.of "S1" "a reached constructor without a constructor record" (some c))
    | _, _ => none

def srcsErrs (p : Program) (ch : Checked) : List RelError :=
  ch.reached.filterMap fun c =>
    match elimShape? p c with
    | some shape =>
      (subsingletonSrcs? p shape.recr).map fun msg => RelError.of "S1" msg (some shape.recr)
    | none => none

def finErrs (p : Program) (ch : Checked) : List RelError :=
  ch.reached.filterMap fun c =>
    match p.table.resolveOf c, p.known.finMk with
    | some (.word ..), some fin =>
      if ch.keepsP fin [] 1 then
        some (RelError.of "S1" "a word operation builds its tower with `irr` as Fin.mk's proof \
          field, which the pinned Fin.mk's record keeps at the empty profile" (some fin))
      else none
    | _, _ => none

end CC

theorem checkCanonical_split (q : Program) (ann : Ann) (ch : Checked) :
    checkCanonical q ann ch =
      CC.readErrs q ann ch ++ CC.forwardErrs q ch ++ CC.redirectErrs q ch ++ CC.headerErrs q ann ch ++
        CC.denseErrs q ++ CC.ruleErrs q ch ++ CC.univErrs q ch ++ CC.recordErrs q ann ch ++
        CC.srcsErrs q ch ++ CC.finErrs q ch ++
        if CC.okConsts q ann && CC.okCtors q ann && CC.okReached q ann ch then []
        else [RelError.of "S1" "non-canonical relevance annotation"] := rfl

section clauses

variable (hme : Program.ModeEq p₀ p) (ann : Ann) (ch : Checked)
include hme

theorem CC.readErrs_eq : CC.readErrs p₀ ann ch = CC.readErrs p ann ch := by
  simp only [CC.readErrs, readsErased?_eq hme]
theorem CC.forwardErrs_eq : CC.forwardErrs p₀ ch = CC.forwardErrs p ch := by
  simp only [CC.forwardErrs, forwardsErased?_eq hme]
theorem CC.redirectErrs_eq : CC.redirectErrs p₀ ch = CC.redirectErrs p ch := by
  simp only [CC.redirectErrs, redirectsErased?_eq hme]
theorem CC.headerErrs_eq : CC.headerErrs p₀ ann ch = CC.headerErrs p ann ch := sorry
theorem CC.denseErrs_eq : CC.denseErrs p₀ = CC.denseErrs p := sorry
theorem CC.ruleErrs_eq : CC.ruleErrs p₀ ch = CC.ruleErrs p ch := by
  simp only [CC.ruleErrs, elimShape?_eq hme, rulesShape?_eq hme]
theorem CC.univErrs_eq : CC.univErrs p₀ ch = CC.univErrs p ch := by
  simp only [CC.univErrs, univsErrs_eq hme]
theorem CC.recordErrs_eq : CC.recordErrs p₀ ann ch = CC.recordErrs p ann ch := sorry
theorem CC.srcsErrs_eq : CC.srcsErrs p₀ ch = CC.srcsErrs p ch := by
  simp only [CC.srcsErrs, elimShape?_eq hme, subsingletonSrcs?_eq hme]
theorem CC.finErrs_eq : CC.finErrs p₀ ch = CC.finErrs p ch := sorry
theorem CC.okConsts_eq : CC.okConsts p₀ ann = CC.okConsts p ann := sorry
theorem CC.okCtors_eq : CC.okCtors p₀ ann = CC.okCtors p ann := sorry
theorem CC.okReached_eq : CC.okReached p₀ ann ch = CC.okReached p ann ch := sorry

end clauses

/-- **`checkCanonical` does not read modes.** -/
theorem checkCanonical_modeEq (hme : Program.ModeEq p₀ p) (ann : Ann) (ch : Checked) :
    checkCanonical p₀ ann ch = checkCanonical p ann ch := by
  rw [checkCanonical_split, checkCanonical_split, CC.readErrs_eq hme, CC.forwardErrs_eq hme,
    CC.redirectErrs_eq hme, CC.headerErrs_eq hme, CC.denseErrs_eq hme, CC.ruleErrs_eq hme,
    CC.univErrs_eq hme, CC.recordErrs_eq hme, CC.srcsErrs_eq hme, CC.finErrs_eq hme,
    CC.okConsts_eq hme, CC.okCtors_eq hme, CC.okReached_eq hme]

end IxCC.Src.Relevance.Proof.ModeEq
