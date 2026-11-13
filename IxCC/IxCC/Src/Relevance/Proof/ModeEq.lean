import IxCC.Src.Proof.Lazify
import IxCC.Src.Proof.TermBEq
import IxCC.Src.Relevance.Check
import IxCC.Src.Relevance.Proof.Canonical

/-! # The relevance checks do not read application modes

`Src.Lazify` changes only the modes of application nodes (`Program.ModeEq`), after the checks have
run on the installed program. This module proves, for `Program.ModeEq p₀ p`, that `check` gives the
same result on both (`check_modeEq`, unconditional) and that the facts `checkCanonical` establishes
transport (`canonical_modeEq : Canonical p₀ ann ch → Canonical p ann ch`, field by field).
`checkCanonical p₀ = checkCanonical p` itself is false for some such pairs: its `dense` clause reads
the maps' `toList`, which also lists a value stored at a zero-child's root that no lookup reads and
`Program.ModeEq` does not constrain (no program ingress builds has one). With L1 (`check_soundC`,
`checkCanonical_sound`) this gives L1's facts on the program SrcEval runs (`P1.facts_modeEq`).

Every function the checks call on the program is shown to give the same answer, or a term equal
up to modes, on `p₀` and `p` and on arguments equal up to modes (`term_me` for C0-C7 and S1-S2,
`checkTermBinders_me` for the tags, `whnfType_me`, `applyPis_me` and `classifyTelescope_me` for the
classifier). One comparison reads modes: `applyPis`'s loop test `whnfType p 4 ty == ty`. On the two
programs the tests can disagree only when a four-step reduction returns its input up to modes (a
cycle through a definition that unfolds to itself), and then neither side ever reaches a sort or a
Π (`applyPis_cycle`, by induction on the fuel). `IxCCTests.Src.Relevance.ModeFlip` plants that
cycle. The other lemmas are private. -/

set_option autoImplicit false

namespace IxCC.Src.Relevance.Proof.ModeEq

open IxCC.Src
open IxCC.Src.Relevance.Check IxCC.Src.Relevance.Check.Canonical
open IxCC.Ixon (Univ)

/-! ## Terms equal up to modes -/

abbrev ME := Term.ModeEq

private theorem ME.symm {t u : Term} (h : ME t u) : ME u t := by
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

private theorem liftTerm_me {t u : Term} (h : ME t u) : ∀ (n k : Nat), ME (liftTerm n k t) (liftTerm n k u) := by
  induction h with
  | app m m' r _ _ ihf iha => intro n k; exact .app m m' r (ihf n k) (iha n k)
  | lam bd _ _ ihd iht => intro n k; exact .lam bd (ihd n k) (iht n (k + 1))
  | pi bd res _ _ ihd iht => intro n k; exact .pi bd res (ihd n k) (iht n (k + 1))
  | letE c r _ _ _ ih₁ ih₂ ih₃ => intro n k; exact .letE c r (ih₁ n k) (ih₂ n k) (ih₃ n (k + 1))
  | proj s i _ ih => intro n k; exact .proj s i (ih n k)
  | var | sort | const | natLit | strLit => intro n k; exact Term.ModeEq.refl _

private theorem substTerm_me {a b : Term} (hab : ME a b) {t u : Term} (h : ME t u) :
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

private theorem instUnivsTerm_me (us : List Univ) {t u : Term} (h : ME t u) :
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

private theorem ArgsME.refl : ∀ xs : List Term.Arg, ArgsME xs xs
  | [] => .nil
  | (a, _, _) :: xs => .cons (Term.ModeEq.refl a) (ArgsME.refl xs)

private theorem ArgsME.symm {xs ys : List Term.Arg} (h : ArgsME xs ys) : ArgsME ys xs := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (ME.symm hab) ih

private theorem ArgsME.length_eq {xs ys : List Term.Arg} (h : ArgsME xs ys) : xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

private theorem ArgsME.isEmpty_eq {xs ys : List Term.Arg} (h : ArgsME xs ys) : xs.isEmpty = ys.isEmpty := by
  cases h <;> rfl

private theorem ArgsME.rels {xs ys : List Term.Arg} (h : ArgsME xs ys) :
    xs.map (·.2.2) = ys.map (·.2.2) := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

private theorem ArgsME.getElem? {xs ys : List Term.Arg} (h : ArgsME xs ys) : ∀ i : Nat,
    (xs[i]? = none ∧ ys[i]? = none) ∨
    ∃ a b m m' r, xs[i]? = some (a, m, r) ∧ ys[i]? = some (b, m', r) ∧ ME a b := by
  induction h with
  | nil => intro i; left; simp
  | cons hab _ ih =>
    intro i
    cases i with
    | zero => right; exact ⟨_, _, _, _, _, rfl, rfl, hab⟩
    | succ i => simpa using ih i

private theorem ArgsME.drop {xs ys : List Term.Arg} (h : ArgsME xs ys) : ∀ n : Nat,
    ArgsME (xs.drop n) (ys.drop n) := by
  induction h with
  | nil => intro n; simpa using ArgsME.nil
  | cons hab hr ih =>
    intro n
    cases n with
    | zero => exact .cons hab hr
    | succ n => simpa using ih n

private theorem ArgsME.take {xs ys : List Term.Arg} (h : ArgsME xs ys) : ∀ n : Nat,
    ArgsME (xs.take n) (ys.take n) := by
  induction h with
  | nil => intro n; simpa using ArgsME.nil
  | cons hab _ ih =>
    intro n
    cases n with
    | zero => simpa using ArgsME.nil
    | succ n => simpa using ArgsME.cons hab (ih n)

private theorem ArgsME.append {xs ys xs' ys' : List Term.Arg} (h : ArgsME xs ys) (h' : ArgsME xs' ys') :
    ArgsME (xs ++ xs') (ys ++ ys') := by
  induction h with
  | nil => simpa using h'
  | cons hab _ ih => exact .cons hab ih

private theorem mkApps_me {h h' : Term} (hh : ME h h') {xs ys : List Term.Arg} (hx : ArgsME xs ys) :
    ME (Term.mkApps h xs) (Term.mkApps h' ys) := by
  induction hx generalizing h h' with
  | nil => exact hh
  | cons hab _ ih =>
    simp only [Term.mkApps, List.foldl_cons]
    exact ih (.app _ _ _ hh hab)

private theorem spine_go_me {t u : Term} (h : ME t u) : ∀ {acc acc' : List Term.Arg}, ArgsME acc acc' →
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

private theorem spine_me {t u : Term} (h : ME t u) :
    ME t.spine.1 u.spine.1 ∧ ArgsME t.spine.2 u.spine.2 :=
  spine_go_me h .nil

private theorem betaApps_nil (t : Term) : betaApps t [] = t := by cases t <;> rfl

private theorem betaApps_cons_nonlam {t : Term} (x : Term.Arg) (xs : List Term.Arg)
    (ht : ∀ b d body, t ≠ .lam b d body) : betaApps t (x :: xs) = Term.mkApps t (x :: xs) := by
  cases t with
  | lam b d body => exact absurd rfl (ht b d body)
  | _ => rfl

private theorem me_lam_iff {t u : Term} (h : ME t u) : (∃ b d body, t = .lam b d body) ↔ ∃ b d body, u = .lam b d body := by
  cases h <;> simp

private theorem betaApps_me {xs ys : List Term.Arg} (hx : ArgsME xs ys) :
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

private theorem lamRels_me {t u : Term} (h : ME t u) : lamRels t = lamRels u := by
  induction h with
  | lam bd _ _ _ iht => simp [lamRels, iht]
  | _ => rfl

private theorem mentionsVar_me {t u : Term} (h : ME t u) : ∀ k : Nat, mentionsVar k t = mentionsVar k u := by
  induction h with
  | app m m' r _ _ ihf iha => intro k; simp [mentionsVar, ihf, iha]
  | lam bd _ _ ihd iht => intro k; simp [mentionsVar, ihd, iht]
  | pi bd res _ _ ihd iht => intro k; simp [mentionsVar, ihd, iht]
  | letE c r _ _ _ ih₁ ih₂ ih₃ => intro k; simp [mentionsVar, ih₁, ih₂, ih₃]
  | proj s i _ ih => intro k; simp [mentionsVar, ih]
  | _ => intro k; rfl

private theorem relevantRefs_me {t u : Term} (h : ME t u) :
    ∀ (prof : Profile) (acc : List Inst), t.relevantRefs prof acc = u.relevantRefs prof acc := by
  induction h with
  | app m m' r _ _ ihf iha => intro prof acc; simp [Term.relevantRefs, ihf, iha]
  | lam bd _ _ _ iht => intro prof acc; simp [Term.relevantRefs, iht]
  | letE c r _ _ _ _ ih₂ ih₃ => intro prof acc; simp [Term.relevantRefs, ih₂, ih₃]
  | proj s i _ ih => intro prof acc; simp [Term.relevantRefs, ih]
  | _ => intro prof acc; rfl

/-- Equal up to modes, under an option. -/
private def OptME : Option Term → Option Term → Prop
  | some t, some u => ME t u
  | none, none => True
  | _, _ => False

private theorem peelLamsN_me : ∀ (n : Nat) {t u : Term}, ME t u → OptME (peelLamsN n t) (peelLamsN n u)
  | 0, _, _, h => h
  | n + 1, _, _, h => by
    cases h with
    | lam bd _ hb => exact peelLamsN_me n hb
    | _ => trivial

private theorem me_sort_iff {t u : Term} (h : ME t u) (s : Univ) : t = .sort s ↔ u = .sort s := by
  cases h <;> simp

private theorem me_pi_iff {t u : Term} (h : ME t u) : (∃ b r d body, t = .pi b r d body) ↔ ∃ b r d body, u = .pi b r d body := by
  cases h <;> simp

private theorem me_letE_iff {t u : Term} (h : ME t u) :
    (∃ c r ty v b, t = .letE c r ty v b) ↔ ∃ c r ty v b, u = .letE c r ty v b := by
  cases h <;> simp

/-- `.pis.2` of terms equal up to modes is a sort on both sides or on neither. -/
private theorem pis_snd_me {t u : Term} (h : ME t u) : ME t.pis.2 u.pis.2 := by
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
private def sortOf (t : Term) : Option Univ :=
  match t.pis.2 with
  | .sort u => some u
  | _ => none

private theorem sortOf_me {t u : Term} (h : ME t u) : sortOf t = sortOf u := by
  have hp := pis_snd_me h
  simp only [sortOf]
  generalize t.pis.2 = a at hp
  generalize u.pis.2 = b at hp
  cases hp <;> rfl

/-! ## Programs equal up to modes -/

variable {p₀ p : Program}

/-- What `Program.ModeEq` says of one declaration, by cases. -/
private theorem decl?_cases (hme : Program.ModeEq p₀ p) (c : CId) :
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

private theorem decl?_type (hme : Program.ModeEq p₀ p) (c : CId) :
    (p₀.decl? c).map Decl.type = (p.decl? c).map Decl.type := by
  rcases decl?_cases hme c with h | ⟨k, s, l, ty, v, v', h₀, h, -⟩ |
      ⟨sf, kk, l, np, nmot, nmin, ni, ind, rs, rs', ty, h₀, h, -⟩
  · rw [h]
  · rw [h₀, h]; rfl
  · rw [h₀, h]; rfl

private theorem decl?_lvls (hme : Program.ModeEq p₀ p) (c : CId) :
    (p₀.decl? c).map Decl.lvls = (p.decl? c).map Decl.lvls := by
  rcases decl?_cases hme c with h | ⟨k, s, l, ty, v, v', h₀, h, -⟩ |
      ⟨sf, kk, l, np, nmot, nmin, ni, ind, rs, rs', ty, h₀, h, -⟩
  · rw [h]
  · rw [h₀, h]; rfl
  · rw [h₀, h]; rfl

private theorem recKindOf_eq (hme : Program.ModeEq p₀ p) (c : CId) :
    p₀.table.recKindOf c = p.table.recKindOf c := by
  simp only [Table.recKindOf, hme.recKind]

/-! ## The classifier: `whnfType`, `isTypeFormerP`, `applyPis` -/

/-- `whnfType`'s step at a term that is not a `let`. -/
private def whnfBody (q : Program) (fuel : Nat) (t : Term) : Term :=
  match t.spine with
  | (head, args) =>
    match head with
    | .lam .. => if args.isEmpty then t else whnfType q fuel (betaApps head args)
    | .const c us =>
      match q.decl? c with
      | some (.defn .defn .safe _ _ val) => whnfType q fuel (betaApps (instUnivsTerm us val) args)
      | _ => t
    | _ => t

private theorem whnfType_succ (q : Program) (fuel : Nat) {t : Term}
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

private theorem whnfType_me_refl (q : Program) (n : Nat) {t u : Term} (h : ME t u) :
    ME (whnfType q n t) (whnfType q n u) :=
  whnfType_me (Program.ModeEq.refl q) n h

/-- Classifier contexts equal up to modes: the same sorts, the types equal up to modes. -/
inductive CtxME : List (Term × Option Univ) → List (Term × Option Univ) → Prop
  | nil : CtxME [] []
  | cons {a b : Term} {s : Option Univ} {xs ys : List (Term × Option Univ)} :
      ME a b → CtxME xs ys → CtxME ((a, s) :: xs) ((b, s) :: ys)

private theorem CtxME.refl : ∀ xs : List (Term × Option Univ), CtxME xs xs
  | [] => .nil
  | (a, _) :: xs => .cons (Term.ModeEq.refl a) (CtxME.refl xs)

private theorem CtxME.getElem? {xs ys : List (Term × Option Univ)} (h : CtxME xs ys) : ∀ i : Nat,
    (xs[i]? = none ∧ ys[i]? = none) ∨
    ∃ a b s, xs[i]? = some (a, s) ∧ ys[i]? = some (b, s) ∧ ME a b := by
  induction h with
  | nil => intro i; left; simp
  | cons hab _ ih =>
    intro i
    cases i with
    | zero => right; exact ⟨_, _, _, rfl, rfl, hab⟩
    | succ i => simpa using ih i

private theorem isTypeFormerP_me (hme : Program.ModeEq p₀ p) :
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
private abbrev Plain (ty : Term) (rest : List Term.Arg) : Prop :=
  (∀ s, ty = .sort s → rest ≠ []) ∧ (∀ b r d body, ty = .pi b r d body → rest = [])

private theorem applyPis_plain (q : Program) (k : Nat) {ty : Term} {rest : List Term.Arg} (h : Plain ty rest) :
    applyPis q (k + 1) ty rest =
      if whnfType q 4 ty == ty then none else applyPis q k (whnfType q 4 ty) rest := by
  obtain ⟨h₁, h₂⟩ := h
  cases ty <;> cases rest <;>
    first
    | rfl
    | exact absurd rfl (h₁ _ rfl)
    | exact absurd (h₂ _ _ _ _ rfl) (List.cons_ne_nil _ _)

private theorem Plain.of_me {t u : Term} (h : ME t u) {rest rest' : List Term.Arg} (hr : ArgsME rest rest')
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
private theorem applyPis_cycle (q : Program) {v : Term} {rest : List Term.Arg} (hv : Plain v rest)
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


private theorem resolveOf_cases (hme : Program.ModeEq p₀ p) (c : CId) :
    p₀.table.resolveOf c = p.table.resolveOf c ∨
    ∃ thm b b', p₀.table.resolveOf c = some (.eqn thm b) ∧ p.table.resolveOf c = some (.eqn thm b') ∧
      ME b b' := by
  have hr := hme.resolve c
  generalize p₀.table.resolveOf c = r₀ at hr ⊢
  generalize p.table.resolveOf c = r at hr ⊢
  cases hr with
  | refl => left; rfl
  | eqn thm hb => right; exact ⟨_, _, _, rfl, rfl, hb⟩

private theorem RulesModeEq.symm' {rs rs' : List Rule} (h : RulesModeEq rs rs') : RulesModeEq rs' rs :=
  ⟨h.1.symm, fun j r r' h₁ h₂ => by
    obtain ⟨hc, hf, hm⟩ := h.2 j r' r h₂ h₁
    exact ⟨hc.symm, hf.symm, ME.symm hm⟩⟩

theorem _root_.IxCC.Src.Program.ModeEq.symm {q q' : Program} (h : Program.ModeEq q q') : Program.ModeEq q' q := by
  refine ⟨h.size.symm, h.roots.symm, h.known.symm, h.resource.symm, h.recKind.symm, h.lazy.symm,
    h.inline.symm, h.opaqueByValue.symm, fun c => ?_, fun c => ?_⟩
  · have hr := h.resolve c
    generalize q.table.resolveOf c = r₀ at hr ⊢
    generalize q'.table.resolveOf c = r at hr ⊢
    cases hr with
    | refl => exact .refl _
    | eqn thm hb => exact .eqn thm (ME.symm hb)
  · have he := h.entry c
    generalize q.entry? c = e₀ at he ⊢
    generalize q'.entry? c = e at he ⊢
    cases e₀ <;> cases e
    · trivial
    · exact he.elim
    · exact he.elim
    · obtain ⟨hr, ha, hd⟩ := he
      refine ⟨hr.symm, ha.symm, ?_⟩
      rename_i a b
      generalize a.decl = d₀ at hd ⊢
      generalize b.decl = d at hd ⊢
      cases hd with
      | refl => exact .refl _
      | defn k s l ty hv => exact .defn k s l ty (ME.symm hv)
      | recr sf kk l np nmot nmin ni ind ty hr' => exact .recr sf kk l np nmot nmin ni ind ty (RulesModeEq.symm' hr')

/-! ### Rules, declarations and table entries, by how they relate -/

/-- Rule lists equal up to the modes of their right-hand sides (`RulesModeEq`, as a list relation). -/
private inductive RulesME : List Rule → List Rule → Prop
  | nil : RulesME [] []
  | cons {r r' : Rule} {rs rs' : List Rule} : r.ctor = r'.ctor → r.fields = r'.fields →
      ME r.rhs r'.rhs → RulesME rs rs' → RulesME (r :: rs) (r' :: rs')

private theorem RulesME.refl : ∀ rs : List Rule, RulesME rs rs
  | [] => .nil
  | r :: rs => .cons rfl rfl (Term.ModeEq.refl r.rhs) (RulesME.refl rs)

private theorem RulesME.of : ∀ {rs rs' : List Rule}, RulesModeEq rs rs' → RulesME rs rs'
  | [], [], _ => .nil
  | [], _ :: _, h => absurd h.1 (by simp)
  | _ :: _, [], h => absurd h.1 (by simp)
  | r :: rs, r' :: rs', h => by
    obtain ⟨hc, hf, hm⟩ := h.2 0 r r' rfl rfl
    exact .cons hc hf hm (RulesME.of ⟨by simpa using h.1,
      fun j a b ha hb => h.2 (j + 1) a b (by simpa using ha) (by simpa using hb)⟩)

private theorem RulesME.length_eq {rs rs' : List Rule} (h : RulesME rs rs') : rs.length = rs'.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ ih => simp [ih]

private theorem RulesME.getElem? {rs rs' : List Rule} (h : RulesME rs rs') : ∀ j : Nat,
    (rs[j]? = none ∧ rs'[j]? = none) ∨
    ∃ r r', rs[j]? = some r ∧ rs'[j]? = some r' ∧ r.ctor = r'.ctor ∧ r.fields = r'.fields ∧
      ME r.rhs r'.rhs := by
  induction h with
  | nil => intro j; left; simp
  | cons hc hf hm _ ih =>
    intro j
    cases j with
    | zero => right; exact ⟨_, _, rfl, rfl, hc, hf, hm⟩
    | succ j => simpa using ih j

/-- The per-rule premise of the list lemmas: `F₀` and `F` agree on related rules. -/
private abbrev RulesAgree {β : Type} (F₀ F : Rule → β) : Prop :=
  ∀ r r', r.ctor = r'.ctor → r.fields = r'.fields → ME r.rhs r'.rhs → F₀ r = F r'

private theorem RulesME.map {β : Type} {rs rs' : List Rule} (h : RulesME rs rs') {F₀ F : Rule → β}
    (hF : RulesAgree F₀ F) : rs.map F₀ = rs'.map F := by
  induction h with
  | nil => rfl
  | cons hc hf hm _ ih => simp only [List.map_cons, hF _ _ hc hf hm, ih]

private theorem RulesME.any {rs rs' : List Rule} (h : RulesME rs rs') {F₀ F : Rule → Bool}
    (hF : RulesAgree F₀ F) : rs.any F₀ = rs'.any F := by
  induction h with
  | nil => rfl
  | cons hc hf hm _ ih => simp only [List.any_cons, hF _ _ hc hf hm, ih]

private theorem RulesME.zipIdx_filterMap {β : Type} {rs rs' : List Rule} (h : RulesME rs rs')
    {F₀ F : Rule × Nat → Option β} (hF : ∀ k, RulesAgree (fun r => F₀ (r, k)) (fun r => F (r, k))) :
    ∀ n : Nat, (rs.zipIdx n).filterMap F₀ = (rs'.zipIdx n).filterMap F := by
  induction h with
  | nil => intro n; rfl
  | cons hc hf hm _ ih =>
    intro n
    simp only [List.zipIdx_cons, List.filterMap_cons, ih (n + 1)]
    rw [show F₀ (_, n) = F (_, n) from hF n _ _ hc hf hm]

private theorem RulesME.zipIdx_findSome? {β : Type} {rs rs' : List Rule} (h : RulesME rs rs')
    {F₀ F : Rule × Nat → Option β} (hF : ∀ k, RulesAgree (fun r => F₀ (r, k)) (fun r => F (r, k))) :
    ∀ n : Nat, (rs.zipIdx n).findSome? F₀ = (rs'.zipIdx n).findSome? F := by
  induction h with
  | nil => intro n; rfl
  | cons hc hf hm _ ih =>
    intro n
    simp only [List.zipIdx_cons, List.findSome?_cons, ih (n + 1)]
    rw [show F₀ (_, n) = F (_, n) from hF n _ _ hc hf hm]

/-- How the declarations of a constant on two programs equal up to modes relate. -/
private inductive DeclME : Option Decl → Option Decl → Prop
  | none : DeclME none none
  | same (d : Decl) : DeclME (some d) (some d)
  | defn (k : Ixon.DefKind) (s : Ixon.DefinitionSafety) (l : Nat) (ty : Term) {v v' : Term} :
      ME v v' → DeclME (some (.defn k s l ty v)) (some (.defn k s l ty v'))
  | recr (sf kk : Bool) (l np nmot nmin ni : Nat) (ind : CId) (ty : Term) {rs rs' : List Rule} :
      RulesME rs rs' →
      DeclME (some (.recr sf kk l np nmot nmin ni ind rs ty)) (some (.recr sf kk l np nmot nmin ni ind rs' ty))

private theorem decl?_me (hme : Program.ModeEq p₀ p) (c : CId) : DeclME (p₀.decl? c) (p.decl? c) := by
  rcases decl?_cases hme c with h | ⟨k, s, l, ty, v, v', h₀, h, hv⟩ |
      ⟨sf, kk, l, np, nmot, nmin, ni, ind, rs, rs', ty, h₀, h, hr⟩
  · rw [h]
    cases p.decl? c with
    | none => exact .none
    | some d => exact .same d
  · rw [h₀, h]; exact .defn k s l ty hv
  · rw [h₀, h]; exact .recr sf kk l np nmot nmin ni ind ty (RulesME.of hr)

/-- Split on how `p₀.decl? c` and `p.decl? c` relate, generalizing both. -/
local macro "decl_me " p₀:term:max p:term:max hme:term:max c:term:max : tactic =>
  `(tactic| (have hd := decl?_me $hme $c
             generalize Program.decl? $p₀ $c = d₀ at hd ⊢
             generalize Program.decl? $p $c = d at hd ⊢
             cases hd))

/-- `decl_me`, and the same declaration split by its kind. -/
local macro "decl_me! " p₀:term:max p:term:max hme:term:max c:term:max : tactic =>
  `(tactic| (have hd := decl?_me $hme $c
             generalize Program.decl? $p₀ $c = d₀ at hd ⊢
             generalize Program.decl? $p $c = d at hd ⊢
             rcases hd with _ | ⟨_ | _ | _ | _ | _ | _⟩ | _ | _))

/-- Split on how `p₀.table.resolveOf c` and `p.table.resolveOf c` relate, generalizing both. -/
local macro "res_me " p₀:term:max p:term:max hme:term:max c:term:max : tactic =>
  `(tactic| (have hr := Program.ModeEq.resolve $hme $c
             generalize Table.resolveOf (Program.table $p₀) $c = r₀ at hr ⊢
             generalize Table.resolveOf (Program.table $p) $c = r at hr ⊢
             cases hr))

private theorem ctorFieldsIs_eq (hme : Program.ModeEq p₀ p) (c n : Nat) :
    ctorFieldsIs p₀ c n = ctorFieldsIs p c n := by
  unfold ctorFieldsIs
  decl_me p₀ p hme c <;> rfl

private theorem onlyCtor?_eq (hme : Program.ModeEq p₀ p) (s : CId) : onlyCtor? p₀ s = onlyCtor? p s := by
  unfold onlyCtor?
  decl_me p₀ p hme s <;> rfl

private theorem fieldWrittenErased_eq (hme : Program.ModeEq p₀ p) (k i : Nat) :
    fieldWrittenErased p₀ k i = fieldWrittenErased p k i := by
  unfold fieldWrittenErased
  decl_me p₀ p hme k <;> rfl

private theorem ctorProfile_eq (hme : Program.ModeEq p₀ p) (r : CId) (q : Profile) :
    ctorProfile p₀ r q = ctorProfile p r q := by
  simp only [ctorProfile, Program.majorUnivs]
  decl_me p₀ p hme r <;> rfl

private theorem specialHead?_eq (hme : Program.ModeEq p₀ p) (c : CId) : specialHead? p₀ c = specialHead? p c := by
  unfold specialHead?
  decl_me p₀ p hme c <;> res_me p₀ p hme c <;> rfl

private theorem appliedAt_eq (hme : Program.ModeEq p₀ p) (c pos : Nat) : appliedAt p₀ c pos = appliedAt p c pos := by
  unfold appliedAt
  rw [specialHead?_eq hme]
  res_me p₀ p hme c
  · rename_i ro
    rcases ro with _ | ⟨_ | _ | _ | r | _⟩ <;> try rfl
    dsimp only
    decl_me p₀ p hme r <;> rfl
  · rfl

private theorem headArityOf_eq' (hme : Program.ModeEq p₀ p) (h : Head) : headArityOf p₀ h = headArityOf p h := by
  cases h with
  | ctor c => simp only [headArityOf]; decl_me p₀ p hme c <;> rfl
  | recr r => simp only [headArityOf]; decl_me p₀ p hme r <;> rfl
  | cases c =>
    simp only [headArityOf]
    res_me p₀ p hme c
    · rename_i ro
      rcases ro with _ | ⟨_ | _ | _ | r | _⟩ <;> try rfl
      dsimp only
      decl_me p₀ p hme r <;> rfl
    · rfl
  | _ => rfl

private theorem headReadsWith_eq (hme : Program.ModeEq p₀ p) (h : Head) (i : Nat) :
    headReadsWith p₀.decl? p₀.table.resolveOf h i = headReadsWith p.decl? p.table.resolveOf h i := by
  cases h with
  | ctor c => simp only [headReadsWith]; decl_me p₀ p hme c <;> rfl
  | cases c =>
    simp only [headReadsWith]
    res_me p₀ p hme c
    · rename_i ro
      rcases ro with _ | ⟨_ | _ | _ | r | _⟩ <;> try rfl
      dsimp only
      decl_me p₀ p hme r <;> rfl
    · rfl
  | _ => rfl

private theorem readsAt_eq (hme : Program.ModeEq p₀ p) (ann : Ann) (c : CId) (h : Head) (i : Nat) :
    readsAt p₀ ann c h i = readsAt p ann c h i := by
  unfold readsAt
  rw [headArityOf_eq' hme, headReadsWith_eq hme, hme.known]
  cases h <;> decl_me p₀ p hme c <;> rfl

private theorem readsAt_fun_eq (hme : Program.ModeEq p₀ p) (ann : Ann) (c : CId) (h : Head) :
    readsAt p₀ ann c h = readsAt p ann c h := funext (readsAt_eq hme ann c h)

private theorem readerName_eq (hme : Program.ModeEq p₀ p) (h : Head) (i : Nat) :
    readerName p₀ h i = readerName p h i := by
  simp only [readerName, headArityOf_eq' hme]

private theorem readsErased?_eq (hme : Program.ModeEq p₀ p) (ann : Ann) (c : CId) :
    readsErased? p₀ ann c = readsErased? p ann c := by
  simp only [readsErased?, specialHead?_eq hme, readsAt_fun_eq hme, readerName_eq hme]
  decl_me p₀ p hme c <;> rfl

private theorem short_eq (hme : Program.ModeEq p₀ p) (c : CId) : p₀.short c = p.short c := by
  have he := hme.entry c
  simp only [Program.short, Program.addr]
  generalize p₀.entry? c = e₀ at he ⊢
  generalize p.entry? c = e at he ⊢
  cases e₀ <;> cases e
  · rfl
  · exact he.elim
  · exact he.elim
  · obtain ⟨-, ha, -⟩ := he
    simp only [Option.map_some, ha]

/-- `ruleDispatch`'s body at a recursor's counts (a copy; `ruleDispatch_def` checks it by `rfl`). -/
private def dispatchOf (np nmot nmin fields : Nat) (rhs : Term) : Option Nat :=
  let total := np + nmot + nmin + fields
  match peelLamsN total rhs with
  | some body =>
    match body.spineL.1 with
    | .var i =>
      if i < total && np + nmot ≤ total - 1 - i && total - 1 - i < np + nmot + nmin then
        some (total - 1 - i - (np + nmot))
      else none
    | _ => none
  | none => none

private theorem ruleDispatch_def (q : Program) (r : CId) (rule : Rule) :
    ruleDispatch q r rule = match q.decl? r with
      | some (.recr _ _ _ np nmot nmin _ _ _ _) => dispatchOf np nmot nmin rule.fields rule.rhs
      | _ => none := rfl

private theorem dispatchOf_me (np nmot nmin f : Nat) {t u : Term} (h : ME t u) :
    dispatchOf np nmot nmin f t = dispatchOf np nmot nmin f u := by
  dsimp only [dispatchOf]
  have hp := peelLamsN_me (np + nmot + nmin + f) h
  generalize peelLamsN (np + nmot + nmin + f) t = o₀ at hp ⊢
  generalize peelLamsN (np + nmot + nmin + f) u = o at hp ⊢
  cases o₀ <;> cases o
  · rfl
  · exact hp.elim
  · exact hp.elim
  · rename_i b₀ b
    dsimp only
    have hh := (spine_me hp).1
    generalize b₀.spineL.1 = h₀ at hh ⊢
    generalize b.spineL.1 = h₁ at hh ⊢
    cases hh <;> rfl

private theorem ruleDispatch_me (hme : Program.ModeEq p₀ p) (r : CId) {rule rule' : Rule}
    (hf : rule.fields = rule'.fields) (hm : ME rule.rhs rule'.rhs) :
    ruleDispatch p₀ r rule = ruleDispatch p r rule' := by
  rw [ruleDispatch_def, ruleDispatch_def, hf]
  decl_me! p₀ p hme r <;> first | rfl | exact dispatchOf_me _ _ _ _ hm

private theorem elimShape?_eq (hme : Program.ModeEq p₀ p) (c : CId) : elimShape? p₀ c = elimShape? p c := by
  unfold elimShape?
  res_me p₀ p hme c
  · rename_i ro
    rcases ro with _ | ⟨_ | _ | _ | r | _⟩ <;> try rfl
    · dsimp only
      decl_me! p₀ p hme c <;> try rfl
      all_goals
        simp only [Option.some.injEq, ElimShape.mk.injEq, true_and, and_true]
      · exact (RulesME.refl _).zipIdx_filterMap
          (fun k a b _ hf hm => by simp only [ruleDispatch_me hme c hf hm]) 0
      · rename_i hr
        exact hr.zipIdx_filterMap (fun k a b _ hf hm => by simp only [ruleDispatch_me hme c hf hm]) 0
    · dsimp only
      decl_me p₀ p hme r <;> rfl
  · rfl

private theorem ruleCtorFields_eq (hme : Program.ModeEq p₀ p) (ann : Ann) (r j : Nat) :
    ruleCtorFields p₀ ann r j = ruleCtorFields p ann r j := by
  unfold ruleCtorFields
  decl_me p₀ p hme r <;> try rfl
  rename_i hr
  rcases hr.getElem? j with ⟨h₁, h₂⟩ | ⟨a, b, h₁, h₂, hc, -, -⟩
  · simp [h₁, h₂]
  · simp [h₁, h₂, hc]

private theorem erasedMinors_eq (hme : Program.ModeEq p₀ p) (shape : ElimShape) :
    erasedMinors p₀ shape = erasedMinors p shape := by
  unfold erasedMinors
  simp only [fieldWrittenErased_eq hme]
  have hF : RulesAgree
      (fun rule => match p₀.decl? rule.ctor with
        | some (.ctor _ _ _ _ _ nf _) => (List.range nf).any (fieldWrittenErased p rule.ctor ·)
        | _ => false)
      (fun rule => match p.decl? rule.ctor with
        | some (.ctor _ _ _ _ _ nf _) => (List.range nf).any (fieldWrittenErased p rule.ctor ·)
        | _ => false) := by
    intro a b hc _ _
    simp only [hc]
    decl_me p₀ p hme b.ctor <;> rfl
  decl_me! p₀ p hme shape.recr <;> try rfl
  · exact (RulesME.refl _).any hF
  · rename_i hr; exact hr.any hF
private theorem termOf_me (hme : Program.ModeEq p₀ p) (key : TermKey) : OptME (p₀.termOf key) (p.termOf key) := by
  cases h₀ : p₀.termOf key with
  | some t =>
    obtain ⟨t', h, hm⟩ := hme.termOf h₀
    rw [h]; exact hm
  | none =>
    cases h : p.termOf key with
    | none => trivial
    | some t =>
      obtain ⟨t', h', _⟩ := hme.symm.termOf h
      rw [h₀] at h'; cases h'

/-- Run bodies with the same keys and terms equal up to modes. -/
private inductive BodiesME : List (TermKey × Term) → List (TermKey × Term) → Prop
  | nil : BodiesME [] []
  | cons {k : TermKey} {t u : Term} {xs ys : List (TermKey × Term)} :
      ME t u → BodiesME xs ys → BodiesME ((k, t) :: xs) ((k, u) :: ys)

private theorem BodiesME.refl : ∀ xs : List (TermKey × Term), BodiesME xs xs
  | [] => .nil
  | (_, t) :: xs => .cons (Term.ModeEq.refl t) (BodiesME.refl xs)

private theorem runBodies_me (hme : Program.ModeEq p₀ p) (c : CId) : BodiesME (runBodies p₀ c) (runBodies p c) := by
  simp only [runBodies, Table.isOpaqueByValue, hme.opaqueByValue]
  res_me p₀ p hme c
  · rename_i ro
    rcases ro with _ | ⟨_ | _ | ⟨thm, b⟩ | _ | _⟩ <;> try exact .nil
    · dsimp only
      decl_me! p₀ p hme c <;> try exact BodiesME.refl _
      rename_i k s _ _ _ _ hv
      cases k <;> cases s <;> try exact .nil
      all_goals first
        | exact .cons hv .nil
        | (dsimp only
           by_cases hb : NatMap.contains p.table.opaqueByValue c = true <;>
             simp only [hb, ↓reduceIte, Bool.false_eq_true] <;>
             first | exact .nil | exact .cons hv .nil)
    · exact BodiesME.refl _
  · rename_i hb; exact .cons hb .nil

private theorem isEvaluatedBody_eq (hme : Program.ModeEq p₀ p) (c : CId) :
    p₀.isEvaluatedBody c = p.isEvaluatedBody c := by
  simp only [Program.isEvaluatedBody, Table.isOpaqueByValue, hme.opaqueByValue]
  decl_me p₀ p hme c <;> try rfl
  rename_i k s _ _ _ _ _
  cases k <;> cases s <;> rfl

private theorem runtimeKeys_eq (hme : Program.ModeEq p₀ p) (c : CId) : p₀.runtimeKeys c = p.runtimeKeys c := by
  simp only [Program.runtimeKeys, isEvaluatedBody_eq hme]
  res_me p₀ p hme c
  · rename_i ro
    rcases ro with _ | ⟨_ | _ | _ | _ | _⟩ <;> try rfl
    dsimp only
    decl_me! p₀ p hme c <;> try rfl
    rename_i hr
    simp only [hr.length_eq]
  · rfl

private theorem instOf_eq (hme : Program.ModeEq p₀ p) (c : CId) (prof : Profile) :
    p₀.instOf c prof = p.instOf c prof := by
  simp only [Program.instOf, decl?_lvls hme]

private theorem runtimeRefs_eq (hme : Program.ModeEq p₀ p) (c : CId) : p₀.runtimeRefs c = p.runtimeRefs c := by
  simp only [Program.runtimeRefs, hme.known, decl?_lvls hme]
  res_me p₀ p hme c <;> rfl

private theorem termsFold_eq (hme : Program.ModeEq p₀ p) (prof : Profile) :
    ∀ (keys : List TermKey) (acc : List Inst),
      List.foldl (fun acc t => t.relevantRefs prof acc) acc (keys.filterMap p₀.termOf) =
        List.foldl (fun acc t => t.relevantRefs prof acc) acc (keys.filterMap p.termOf)
  | [], _ => rfl
  | k :: ks, acc => by
    have hk := termOf_me hme k
    simp only [List.filterMap_cons]
    generalize p₀.termOf k = o₀ at hk ⊢
    generalize p.termOf k = o at hk ⊢
    cases o₀ <;> cases o
    · exact termsFold_eq hme prof ks acc
    · exact hk.elim
    · exact hk.elim
    · simp only [List.foldl_cons]
      rw [relevantRefs_me hk]
      exact termsFold_eq hme prof ks _

private theorem instRefs_eq (hme : Program.ModeEq p₀ p) (c : CId) (prof : Profile) :
    p₀.instRefs c prof = p.instRefs c prof := by
  simp only [Program.instRefs, runtimeKeys_eq hme, runtimeRefs_eq hme, termsFold_eq hme]

private theorem subsingletonFields_eq (hme : Program.ModeEq p₀ p) (ann : Ann) (r : CId) (q : Profile)
    (errs : List RelError) : subsingletonFields p₀ ann r q errs = subsingletonFields p ann r q errs := by
  simp only [subsingletonFields, recKindOf_eq hme, ctorProfile_eq hme]
  generalize Option.map (fun k => RecKind.atProfile q k) (p.table.recKindOf r) = rk
  decl_me! p₀ p hme r <;> try rfl
  rename_i hr
  cases hr with
  | nil => rfl
  | cons hc _ _ _ =>
    cases rk with
    | none => rfl
    | some k => cases k <;> simp only [List.head?_cons, hc]

private theorem records_eq (hme : Program.ModeEq p₀ p) (ann : Ann) : records p₀ ann = records p ann := by
  simp only [records, hme.size]
  congr 1
  funext errs c
  decl_me p₀ p hme c <;> rfl

private theorem subsingletonSrcs?_eq (hme : Program.ModeEq p₀ p) (r : CId) :
    subsingletonSrcs? p₀ r = subsingletonSrcs? p r := by
  simp only [subsingletonSrcs?, recKindOf_eq hme]
  generalize p.table.recKindOf r = rk
  decl_me! p₀ p hme r <;> try rfl
  · rename_i rules _
    cases rk with
    | none => rfl
    | some k =>
      cases k <;> try rfl
      dsimp only
      cases rules[0]? with
      | none => rfl
      | some rule => dsimp only; decl_me p₀ p hme rule.ctor <;> rfl
  · rename_i hr
    cases rk with
    | none => rfl
    | some k =>
      cases k <;> try rfl
      dsimp only
      rcases hr.getElem? 0 with ⟨h₁, h₂⟩ | ⟨a, b, h₁, h₂, hc, hf, -⟩
      · rw [h₁, h₂]
      · rw [h₁, h₂]
        dsimp only
        rw [hc, hf]
        decl_me p₀ p hme b.ctor <;> rfl

private theorem rulesShape?_eq (hme : Program.ModeEq p₀ p) (r : CId) : rulesShape? p₀ r = rulesShape? p r := by
  unfold rulesShape?
  decl_me! p₀ p hme r <;> try rfl
  all_goals first
    | refine (RulesME.refl _).zipIdx_findSome? ?_ 0
    | (rename_i hr; refine hr.zipIdx_findSome? ?_ 0)
  all_goals
    intro k a b hc hf _
    simp only [hc, hf, short_eq hme]
    decl_me p₀ p hme b.ctor <;> rfl

private theorem univsOk_me (hme : Program.ModeEq p₀ p) {t u : Term} (h : ME t u) : univsOk p₀ t = univsOk p u := by
  induction h with
  | const c us => simp only [univsOk, decl?_lvls hme]
  | app m m' r _ _ ihf iha => simp only [univsOk, ihf, iha]
  | lam bd _ _ _ iht => simp only [univsOk, iht]
  | letE c r _ _ _ _ ih₂ ih₃ => simp only [univsOk, ih₂, ih₃]
  | proj s i _ ih => simp only [univsOk, ih]
  | _ => rfl

private theorem univsOk_eq (hme : Program.ModeEq p₀ p) (t : Term) : univsOk p₀ t = univsOk p t :=
  univsOk_me hme (Term.ModeEq.refl t)

private theorem univsErrs_eq (hme : Program.ModeEq p₀ p) (c : CId) : univsErrs p₀ c = univsErrs p c := by
  simp only [univsErrs, runtimeKeys_eq hme, univsOk_eq hme, short_eq hme]
  congr 1
  · congr 1
    funext key
    have hk := termOf_me hme key
    generalize p₀.termOf key = o₀ at hk ⊢
    generalize p.termOf key = o at hk ⊢
    cases o₀ <;> cases o
    · rfl
    · exact hk.elim
    · exact hk.elim
    · dsimp only
      rw [univsOk_me (Program.ModeEq.refl p) hk]
  · res_me p₀ p hme c <;> rfl

private theorem redirectsErased?_eq (hme : Program.ModeEq p₀ p) (c : CId) :
    redirectsErased? p₀ c = redirectsErased? p c := by
  simp only [redirectsErased?, elimShape?_eq hme, erasedMinors_eq hme, short_eq hme]
  res_me p₀ p hme c <;> rfl

/-! ### The rest of the classifier -/

private theorem projFieldSort?_eq (hme : Program.ModeEq p₀ p) (s i n : Nat) :
    projFieldSort? p₀ s i n = projFieldSort? p s i n := by
  unfold projFieldSort?
  rw [onlyCtor?_eq hme]
  cases onlyCtor? p s with
  | none => rfl
  | some k =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    decl_me p₀ p hme k <;> rfl

/-- `inferTypeSort`'s step at a constant's declaration, over the argument count `len` and the
recursive call `R` on the unfolded value. -/
private def inferDeclG (d : Decl) (us : List Univ) (len : Nat) (R : Term → Option Univ) : Option Univ :=
  let (pis, concl) := d.type.pis
  match concl with
  | .sort u =>
    if len == pis.length then some (instUniv us u)
    else
      match d with
      | .defn .defn .safe _ _ val => R val
      | _ => none
  | _ =>
    match d with
    | .defn .defn .safe _ _ val => R val
    | _ => none

/-- `inferTypeSort`'s step at a term that is not a sort, a Π or a `let`. -/
private def inferBody (q : Program) (ctx : List (Term × Option Univ)) (fuel : Nat) (t : Term) : Option Univ :=
  let (head, args) := t.spine
  match head with
  | .var idx =>
    match ctx[idx]? with
    | some (varTy, u?) =>
      if args.isEmpty then u?
      else applyPis q 16 (liftTerm (idx + 1) 0 varTy) args
    | _ => none
  | .const c us =>
    match q.decl? c with
    | some d =>
      inferDeclG d us args.length fun val => inferTypeSort q ctx fuel (betaApps (instUnivsTerm us val) args)
    | none => none
  | .proj s i _ => projFieldSort? q s i args.length
  | _ => none

private theorem inferTypeSort_succ (q : Program) (ctx : List (Term × Option Univ)) (fuel : Nat) {t : Term}
    (h₁ : ¬ ∃ s, t = .sort s) (h₂ : ¬ ∃ b r d body, t = .pi b r d body)
    (h₃ : ¬ ∃ c r ty v b, t = .letE c r ty v b) :
    inferTypeSort q ctx (fuel + 1) t = inferBody q ctx fuel t := by
  cases t with
  | sort s => exact absurd ⟨s, rfl⟩ h₁
  | pi b r d body => exact absurd ⟨b, r, d, body, rfl⟩ h₂
  | letE c r ty v b => exact absurd ⟨c, r, ty, v, b, rfl⟩ h₃
  | _ => rfl

private theorem inferDeclG_me {d d' : Decl} (hd : DeclME (some d) (some d')) (us : List Univ) (len : Nat)
    {R R' : Term → Option Univ} (hR : ∀ {v v' : Term}, ME v v' → R v = R' v') :
    inferDeclG d us len R = inferDeclG d' us len R' := by
  cases hd with
  | same d =>
    have : R = R' := funext fun v => hR (Term.ModeEq.refl v)
    rw [this]
  | defn k s l ty hv =>
    unfold inferDeclG
    cases k <;> cases s <;> first | rfl | (simp only [hR hv, Decl.type] <;> rfl)
  | recr => rfl

private theorem inferBody_me (hme : Program.ModeEq p₀ p) {n : Nat}
    (IH : ∀ {ctx₀ ctx : List (Term × Option Univ)}, CtxME ctx₀ ctx → ∀ {t u : Term}, ME t u →
      inferTypeSort p₀ ctx₀ n t = inferTypeSort p ctx n u)
    {ctx₀ ctx : List (Term × Option Univ)} (hc : CtxME ctx₀ ctx) {t u : Term} (h : ME t u) :
    inferBody p₀ ctx₀ n t = inferBody p ctx n u := by
  unfold inferBody
  obtain ⟨hh, ha⟩ := spine_me h
  generalize t.spine = s₀ at hh ha ⊢
  generalize u.spine = s₁ at hh ha ⊢
  obtain ⟨h₀, a₀⟩ := s₀
  obtain ⟨h₁, a₁⟩ := s₁
  dsimp only at hh ha ⊢
  cases hh with
  | var i =>
    dsimp only
    rcases hc.getElem? i with ⟨e₀, e₁⟩ | ⟨a, b, s, e₀, e₁, hab⟩
    · rw [e₀, e₁]
    · rw [e₀, e₁]
      dsimp only
      rw [ha.isEmpty_eq]
      cases a₁.isEmpty
      · exact applyPis_me hme 16 (liftTerm_me hab _ _) ha
      · rfl
  | const c us =>
    dsimp only
    rw [ha.length_eq]
    have hd := decl?_me hme c
    generalize p₀.decl? c = d₀ at hd ⊢
    generalize p.decl? c = d₁ at hd ⊢
    cases hd with
    | none => rfl
    | same d =>
      exact inferDeclG_me (.same d) us _ fun hv => IH hc (betaApps_me ha (instUnivsTerm_me us hv))
    | defn k s l ty hv =>
      exact inferDeclG_me (.defn k s l ty hv) us _ fun hv => IH hc (betaApps_me ha (instUnivsTerm_me us hv))
    | recr sf kk l np nmot nmin ni ind ty hr =>
      exact inferDeclG_me (.recr sf kk l np nmot nmin ni ind ty hr) us _
        fun hv => IH hc (betaApps_me ha (instUnivsTerm_me us hv))
  | proj s i he => dsimp only; rw [projFieldSort?_eq hme, ha.length_eq]
  | _ => rfl

private theorem inferTypeSort_me (hme : Program.ModeEq p₀ p) :
    ∀ (n : Nat) {ctx₀ ctx : List (Term × Option Univ)}, CtxME ctx₀ ctx → ∀ {t u : Term}, ME t u →
      inferTypeSort p₀ ctx₀ n t = inferTypeSort p ctx n u
  | 0, _, _, _, _, _, _ => rfl
  | n + 1, ctx₀, ctx, hc, t, u, h => by
    by_cases hs : ∃ s, t = .sort s
    · obtain ⟨s, rfl⟩ := hs
      cases h
      rfl
    by_cases hp : ∃ b r d body, t = .pi b r d body
    · obtain ⟨b, r, d, body, rfl⟩ := hp
      obtain ⟨d', body', rfl, hd, hb⟩ : ∃ d' body', u = .pi b r d' body' ∧ ME d d' ∧ ME body body' := by
        cases h with
        | pi _ _ hd hb => exact ⟨_, _, rfl, hd, hb⟩
      simp only [inferTypeSort]
      rw [inferTypeSort_me hme n hc hd]
      have hS := pis_snd_me (whnfType_me hme 8 hd)
      generalize (whnfType p₀ 8 d).pis.2 = S₀ at hS ⊢
      generalize (whnfType p 8 d').pis.2 = S₁ at hS ⊢
      cases hS <;> dsimp only <;> rw [inferTypeSort_me hme n (.cons hd hc) hb]
    by_cases hl : ∃ c r ty v b, t = .letE c r ty v b
    · obtain ⟨c, r, ty, v, b, rfl⟩ := hl
      cases h with
      | letE _ _ _ hv hb => exact inferTypeSort_me hme n hc (substTerm_me hv hb 0)
    have hs' : ¬ ∃ s, u = .sort s := fun ⟨s, he⟩ => hs ⟨s, (me_sort_iff h s).2 he⟩
    have hp' : ¬ ∃ b r d body, u = .pi b r d body := fun he => hp ((me_pi_iff h).2 he)
    have hl' : ¬ ∃ c r ty v b, u = .letE c r ty v b := fun he => hl ((me_letE_iff h).2 he)
    rw [inferTypeSort_succ _ _ _ hs hp hl, inferTypeSort_succ _ _ _ hs' hp' hl']
    exact inferBody_me hme (inferTypeSort_me hme n) hc h

private theorem classifyDomain_me (hme : Program.ModeEq p₀ p) {ctx₀ ctx : List (Term × Option Univ)}
    (hc : CtxME ctx₀ ctx) (b : Binder) {t u : Term} (h : ME t u) :
    classifyDomain p₀ ctx₀ b t = classifyDomain p ctx b u := by
  simp only [classifyDomain, inferTypeSort_me hme 16 hc h, isTypeFormerP_me hme 16 ctx₀ ctx h]

private theorem classifyTelescope_nonpi (q : Program) (ctx : List (Term × Option Univ)) (n : Nat) {t : Term}
    (ht : ¬ ∃ b r d body, t = .pi b r d body) :
    classifyTelescope q ctx (n + 1) t = ([], classifyDomain q ctx {} t) := by
  cases t with
  | pi b r d body => exact absurd ⟨b, r, d, body, rfl⟩ ht
  | _ => rfl

theorem classifyTelescope_me (hme : Program.ModeEq p₀ p) :
    ∀ (n : Nat) {ctx₀ ctx : List (Term × Option Univ)}, CtxME ctx₀ ctx → ∀ {t u : Term}, ME t u →
      classifyTelescope p₀ ctx₀ n t = classifyTelescope p ctx n u
  | 0, _, _, _, _, _, _ => rfl
  | n + 1, ctx₀, ctx, hc, t, u, h => by
    by_cases hp : ∃ b r d body, t = .pi b r d body
    · obtain ⟨b, r, d, body, rfl⟩ := hp
      obtain ⟨d', body', rfl, hd, hb⟩ : ∃ d' body', u = .pi b r d' body' ∧ ME d d' ∧ ME body body' := by
        cases h with
        | pi _ _ hd hb => exact ⟨_, _, rfl, hd, hb⟩
      simp only [classifyTelescope]
      rw [classifyDomain_me hme hc b hd]
      have hS := pis_snd_me (whnfType_me hme 8 hd)
      generalize (whnfType p₀ 8 d).pis.2 = S₀ at hS ⊢
      generalize (whnfType p 8 d').pis.2 = S₁ at hS ⊢
      cases hS <;> dsimp only <;> rw [classifyTelescope_me hme n (.cons hd hc) hb]
    · have hp' : ¬ ∃ b r d body, u = .pi b r d body := fun he => hp ((me_pi_iff h).2 he)
      rw [classifyTelescope_nonpi _ _ _ hp, classifyTelescope_nonpi _ _ _ hp', classifyDomain_me hme hc {} h]

/-! ### `checkTermBinders` -/

/-- Term lists equal up to modes, pointwise. -/
private inductive TermsME : List Term → List Term → Prop
  | nil : TermsME [] []
  | cons {a b : Term} {xs ys : List Term} : ME a b → TermsME xs ys → TermsME (a :: xs) (b :: ys)

private theorem TermsME.refl : ∀ xs : List Term, TermsME xs xs
  | [] => .nil
  | a :: xs => .cons (Term.ModeEq.refl a) (TermsME.refl xs)

private theorem TermsME.append {xs ys xs' ys' : List Term} (h : TermsME xs ys) (h' : TermsME xs' ys') :
    TermsME (xs ++ xs') (ys ++ ys') := by
  induction h with
  | nil => simpa using h'
  | cons hab _ ih => exact .cons hab ih

private theorem ArgsME.terms {xs ys : List Term.Arg} (h : ArgsME xs ys) :
    TermsME (xs.map (·.1)) (ys.map (·.1)) := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons hab ih

private theorem OptME.refl : ∀ o : Option Term, OptME o o
  | some t => Term.ModeEq.refl t
  | none => trivial

private theorem OptME.ite {c : Prop} [Decidable c] {a b a' b' : Option Term} (h₁ : c → OptME a a')
    (h₂ : ¬c → OptME b b') : OptME (if c then a else b) (if c then a' else b') := by
  by_cases hc : c
  · rw [ite_eq_left hc, ite_eq_left hc]; exact h₁ hc
  · rw [ite_eq_right hc, ite_eq_right hc]; exact h₂ hc

private theorem argsRelevant_me {xs ys : List Term.Arg} (h : ArgsME xs ys) : argsRelevant xs = argsRelevant ys := by
  induction h with
  | nil => rfl
  | cons _ _ ih =>
    simp only [argsRelevant, List.all_cons] at ih ⊢
    rw [ih]

private theorem checkSpineArgs_me (hme : Program.ModeEq p₀ p) {ctx₀ ctx : List (Term × Option Univ)}
    (hc : CtxME ctx₀ ctx) {xs ys : List Term.Arg} (hx : ArgsME xs ys) :
    ∀ (cov : Nat) {f g : Term}, ME f g → checkSpineArgs p₀ ctx₀ cov f xs = checkSpineArgs p ctx cov g ys := by
  induction hx with
  | nil => intro cov f g _; rfl
  | cons hab _ ih =>
    intro cov f g hfg
    simp only [checkSpineArgs]
    have hw := whnfType_me hme 8 hfg
    generalize whnfType p₀ 8 f = w₀ at hw ⊢
    generalize whnfType p 8 g = w at hw ⊢
    cases hw with
    | pi bd res hd hb =>
      dsimp only
      rw [classifyDomain_me hme hc _ hd, ih _ (substTerm_me hab hb 0)]
    | _ => dsimp only; rw [ih _ hfg]

private theorem peelSubstPis_me (hme : Program.ModeEq p₀ p) {as bs : List Term} (h : TermsME as bs) :
    ∀ {t u : Term}, ME t u → OptME (peelSubstPis p₀ as t) (peelSubstPis p bs u) := by
  induction h with
  | nil =>
    intro t u htu
    simp only [peelSubstPis]
    have hw := whnfType_me hme 8 htu
    generalize whnfType p₀ 8 t = w₀ at hw ⊢
    generalize whnfType p 8 u = w at hw ⊢
    cases hw with
    | pi bd res hd hb => exact hd
    | _ => trivial
  | cons hab _ ih =>
    intro t u htu
    simp only [peelSubstPis]
    have hw := whnfType_me hme 8 htu
    generalize whnfType p₀ 8 t = w₀ at hw ⊢
    generalize whnfType p 8 u = w at hw ⊢
    cases hw with
    | pi bd res hd hb => exact ih (substTerm_me hab hb 0)
    | _ => trivial

private theorem applyTypeArgs_me (hme : Program.ModeEq p₀ p) {xs ys : List Term.Arg} (h : ArgsME xs ys) :
    ∀ {t u : Term}, ME t u → OptME (applyTypeArgs p₀ t xs) (applyTypeArgs p u ys) := by
  induction h with
  | nil => intro t u htu; simp only [applyTypeArgs]; exact htu
  | cons hab _ ih =>
    intro t u htu
    simp only [applyTypeArgs]
    have hw := whnfType_me hme 8 htu
    generalize whnfType p₀ 8 t = w₀ at hw ⊢
    generalize whnfType p 8 u = w at hw ⊢
    cases hw with
    | pi bd res hd hb => exact ih (substTerm_me hab hb 0)
    | _ => trivial

/-- `inferSimpleType`'s head type at fuel `fuel + 1` (a copy of its `headTy?`;
`inferSimpleType_succ` checks it by `rfl`). -/
private def simpleHeadTy (q : Program) (ctx : List (Term × Option Univ)) (fuel : Nat) (head : Term) :
    Option Term :=
  match head with
  | .var idx => ctx[idx]?.map fun (varTy, _) => liftTerm (idx + 1) 0 varTy
  | .const c us => (q.decl? c).map fun d => instUnivsTerm us d.type
  | .proj s i e => do
    let k ← onlyCtor? q s
    let .ctor _ lvls _ _ np nf ctorTy ← q.decl? k | none
    if i ≥ nf then none else
    let flds := (List.range i).map (Term.proj s · e)
    match inferSimpleType q ctx fuel e with
    | some eTy =>
      let (sHead, sArgs) := (whnfType q 8 eTy).spine
      match sHead with
      | .const s' us =>
        if s' == s && sArgs.length ≥ np then
          peelSubstPis q ((sArgs.take np).map (·.1) ++ flds) (instUnivsTerm us ctorTy)
        else if lvls == 0 then
          peelSubstPis q (List.replicate np (.natLit 0) ++ flds) ctorTy
        else none
      | _ =>
        if lvls == 0 then peelSubstPis q (List.replicate np (.natLit 0) ++ flds) ctorTy
        else none
    | none =>
      if lvls == 0 then peelSubstPis q (List.replicate np (.natLit 0) ++ flds) ctorTy
      else none
  | _ => none

private theorem inferSimpleType_succ (q : Program) (ctx : List (Term × Option Univ)) (fuel : Nat) {t : Term}
    (h : ¬ ∃ c r ty v b, t = .letE c r ty v b) :
    inferSimpleType q ctx (fuel + 1) t =
      match simpleHeadTy q ctx fuel t.spine.1 with
      | some hTy => applyTypeArgs q hTy t.spine.2
      | none => none := by
  cases t with
  | letE c r ty v b => exact absurd ⟨c, r, ty, v, b, rfl⟩ h
  | _ => rfl

private theorem flds_me (s : Nat) {e e' : Term} (he : ME e e') :
    ∀ i : Nat, TermsME ((List.range i).map (Term.proj s · e)) ((List.range i).map (Term.proj s · e'))
  | 0 => by simpa using TermsME.nil
  | i + 1 => by
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    exact (flds_me s he i).append (.cons (.proj s i he) .nil)

private theorem simpleHeadTy_me (hme : Program.ModeEq p₀ p) {n : Nat} {ctx₀ ctx : List (Term × Option Univ)}
    (IH : ∀ {t u : Term}, ME t u → OptME (inferSimpleType p₀ ctx₀ n t) (inferSimpleType p ctx n u))
    (hc : CtxME ctx₀ ctx) {h₀ h₁ : Term} (hh : ME h₀ h₁) :
    OptME (simpleHeadTy p₀ ctx₀ n h₀) (simpleHeadTy p ctx n h₁) := by
  cases hh with
  | var i =>
    simp only [simpleHeadTy]
    rcases hc.getElem? i with ⟨e₀, e₁⟩ | ⟨a, b, s, e₀, e₁, hab⟩
    · rw [e₀, e₁]; trivial
    · rw [e₀, e₁]; exact liftTerm_me hab _ _
  | const c us =>
    simp only [simpleHeadTy]
    decl_me p₀ p hme c <;> exact OptME.refl _
  | @proj s i e e' he =>
    simp only [simpleHeadTy, onlyCtor?_eq hme]
    cases onlyCtor? p s with
    | none => trivial
    | some k =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      decl_me! p₀ p hme k <;> try exact OptME.refl _
      rename_i sf lv ind cidx np nf ty
      simp only [Option.bind_some]
      refine OptME.ite (fun _ => trivial) (fun _ => ?_)
      have hf := flds_me s he i
      have he' := IH he
      generalize inferSimpleType p₀ ctx₀ n e = o₀ at he' ⊢
      generalize inferSimpleType p ctx n e' = o at he' ⊢
      have hrep := peelSubstPis_me hme (TermsME.append (TermsME.refl (List.replicate np (.natLit 0))) hf)
        (Term.ModeEq.refl ty)
      cases o₀ <;> cases o
      · exact OptME.ite (fun _ => hrep) (fun _ => trivial)
      · exact he'.elim
      · exact he'.elim
      · rename_i eTy₀ eTy
        obtain ⟨hsh, hsa⟩ := spine_me (whnfType_me hme 8 he')
        dsimp only
        generalize (whnfType p₀ 8 eTy₀).spine = sp₀ at hsh hsa ⊢
        generalize (whnfType p 8 eTy).spine = sp at hsh hsa ⊢
        obtain ⟨sh₀, sa₀⟩ := sp₀
        obtain ⟨sh, sa⟩ := sp
        dsimp only at hsh hsa ⊢
        cases hsh with
        | const s' us =>
          dsimp only
          rw [hsa.length_eq]
          exact OptME.ite
            (fun _ => peelSubstPis_me hme (TermsME.append (hsa.take np).terms hf) (Term.ModeEq.refl _))
            (fun _ => OptME.ite (fun _ => hrep) (fun _ => trivial))
        | _ => dsimp only; exact OptME.ite (fun _ => hrep) (fun _ => trivial)
  | _ => trivial

private theorem inferSimpleType_me (hme : Program.ModeEq p₀ p) :
    ∀ (n : Nat) {ctx₀ ctx : List (Term × Option Univ)}, CtxME ctx₀ ctx → ∀ {t u : Term}, ME t u →
      OptME (inferSimpleType p₀ ctx₀ n t) (inferSimpleType p ctx n u)
  | 0, _, _, _, _, _, _ => trivial
  | n + 1, ctx₀, ctx, hc, t, u, h => by
    by_cases hl : ∃ c r ty v b, t = .letE c r ty v b
    · obtain ⟨c, r, ty, v, b, rfl⟩ := hl
      cases h with
      | letE _ _ _ hv hb => exact inferSimpleType_me hme n hc (substTerm_me hv hb 0)
    have hl' : ¬ ∃ c r ty v b, u = .letE c r ty v b := fun he => hl ((me_letE_iff h).2 he)
    rw [inferSimpleType_succ _ _ _ hl, inferSimpleType_succ _ _ _ hl']
    obtain ⟨hh, ha⟩ := spine_me h
    have hH := simpleHeadTy_me hme (inferSimpleType_me hme n hc) hc hh
    generalize simpleHeadTy p₀ ctx₀ n t.spine.1 = o₀ at hH ⊢
    generalize simpleHeadTy p ctx n u.spine.1 = o at hH ⊢
    cases o₀ <;> cases o
    · trivial
    · exact hH.elim
    · exact hH.elim
    · exact applyTypeArgs_me hme ha hH

private theorem checkBetaArgs_me (hme : Program.ModeEq p₀ p) {ctx₀ ctx : List (Term × Option Univ)}
    (hc : CtxME ctx₀ ctx) {xs ys : List Term.Arg} (hx : ArgsME xs ys) :
    ∀ {t u : Term}, ME t u → checkBetaArgs p₀ ctx₀ t xs = checkBetaArgs p ctx u ys := by
  induction hx with
  | nil => intro t u _; first | rfl | simp only [checkBetaArgs]
  | cons hab _ ih =>
    intro t u h
    cases h with
    | lam bd hd hb =>
      simp only [checkBetaArgs]
      rw [classifyDomain_me hme hc bd hd, ih (substTerm_me hab hb 0)]
    | _ => rfl

private theorem checkReducedSpine_me (hme : Program.ModeEq p₀ p) {ctx₀ ctx : List (Term × Option Univ)}
    (hc : CtxME ctx₀ ctx) {t u : Term} (h : ME t u) {xs ys : List Term.Arg} (hx : ArgsME xs ys) :
    checkReducedSpine p₀ ctx₀ t xs = checkReducedSpine p ctx u ys := by
  unfold checkReducedSpine
  rw [hx.isEmpty_eq]
  obtain ⟨hh, ha⟩ := spine_me h
  generalize t.spine = s₀ at hh ha ⊢
  generalize u.spine = s₁ at hh ha ⊢
  obtain ⟨h₀, a₀⟩ := s₀
  obtain ⟨h₁, a₁⟩ := s₁
  dsimp only at hh ha ⊢
  have happ := ha.append hx
  cases hh with
  | const c us =>
    dsimp only
    rw [ha.length_eq]
    decl_me p₀ p hme c
    · rfl
    all_goals exact congrArg (fun z => ys.isEmpty || z) (checkSpineArgs_me hme hc happ _ (Term.ModeEq.refl _))
  | var i =>
    dsimp only
    rcases hc.getElem? i with ⟨e₀, e₁⟩ | ⟨a, b, s, e₀, e₁, hab⟩
    · rw [e₀, e₁]
    · rw [e₀, e₁]
      dsimp only
      rw [ha.length_eq, checkSpineArgs_me hme hc happ _ (liftTerm_me hab _ _)]
  | @proj s i e e' he =>
    dsimp only
    have hS := inferSimpleType_me hme 8 hc (.proj s i he)
    generalize inferSimpleType p₀ ctx₀ 8 (.proj s i e) = o₀ at hS ⊢
    generalize inferSimpleType p ctx 8 (.proj s i e') = o at hS ⊢
    cases o₀ <;> cases o
    · dsimp only; rw [argsRelevant_me hx]
    · exact hS.elim
    · exact hS.elim
    · dsimp only; rw [ha.length_eq, checkSpineArgs_me hme hc happ _ hS]
  | _ => dsimp only; rw [argsRelevant_me hx]

theorem checkTermBinders_me (hme : Program.ModeEq p₀ p) (ann : Ann) :
    ∀ {t u : Term} {ctx₀ ctx : List (Term × Option Univ)} {xs ys : List Term.Arg}, ME t u →
      CtxME ctx₀ ctx → ArgsME xs ys → checkTermBinders p₀ ann ctx₀ t xs = checkTermBinders p ann ctx u ys := by
  intro t u ctx₀ ctx xs ys h
  induction h generalizing ctx₀ ctx xs ys with
  | app m m' r hf ha ihf iha =>
    intro hc hx
    simp only [checkTermBinders]
    rw [iha hc .nil, ihf hc (.cons ha hx)]
  | @lam bd d d' b b' hd hb ihd ihb =>
    intro hc hx
    simp only [checkTermBinders]
    have hl := lamRels_me (Term.ModeEq.lam bd hd hb)
    rw [hl, checkBetaArgs_me hme hc (hx.take _) (.lam bd hd hb),
      checkReducedSpine_me hme hc (betaApps_me (hx.take _) (.lam bd hd hb)) (hx.drop _),
      classifyDomain_me hme hc bd hd]
    have hS := pis_snd_me (whnfType_me hme 8 hd)
    generalize (whnfType p₀ 8 d).pis.2 = S₀ at hS ⊢
    generalize (whnfType p 8 d').pis.2 = S₁ at hS ⊢
    cases hS <;> dsimp only <;> rw [ihb (.cons hd hc) .nil]
  | @letE c r ty ty' v v' b b' h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    intro hc hx
    simp only [checkTermBinders]
    rw [argsRelevant_me hx, classifyDomain_me hme hc _ h₁, ih₂ hc .nil]
    have hS := pis_snd_me (whnfType_me hme 8 h₁)
    generalize (whnfType p₀ 8 ty).pis.2 = S₀ at hS ⊢
    generalize (whnfType p 8 ty').pis.2 = S₁ at hS ⊢
    cases hS <;> dsimp only <;> rw [ih₃ (.cons h₁ hc) .nil]
  | const c us =>
    intro hc hx
    simp only [checkTermBinders]
    decl_me p₀ p hme c
    · rfl
    all_goals exact checkSpineArgs_me hme hc hx _ (Term.ModeEq.refl _)
  | var i =>
    intro hc hx
    simp only [checkTermBinders]
    rcases hc.getElem? i with ⟨e₀, e₁⟩ | ⟨a, b, s, e₀, e₁, hab⟩
    · rw [e₀, e₁]
    · rw [e₀, e₁]
      exact checkSpineArgs_me hme hc hx _ (liftTerm_me hab _ _)
  | @proj s i e e' he ih =>
    intro hc hx
    simp only [checkTermBinders]
    rw [hx.isEmpty_eq, ih hc .nil]
    have hS := inferSimpleType_me hme 8 hc (.proj s i he)
    generalize inferSimpleType p₀ ctx₀ 8 (.proj s i e) = o₀ at hS ⊢
    generalize inferSimpleType p ctx 8 (.proj s i e') = o at hS ⊢
    cases o₀ <;> cases o
    · dsimp only; rw [argsRelevant_me hx]
    · exact hS.elim
    · exact hS.elim
    · dsimp only; rw [checkSpineArgs_me hme hc hx _ hS]
  | sort | natLit | strLit => intro hc hx; simp only [checkTermBinders]; rw [argsRelevant_me hx]
  | pi bd res _ _ _ _ => intro hc hx; simp only [checkTermBinders]; rw [argsRelevant_me hx]

/-! ## `check` -/

/-! ### The rules at a term: only the argument tags and the minors' binders are read -/

section rules

variable {ann : Ann} {key : TermKey} {lvls : Nat} {prof : Profile}

private theorem paramArgs_me (q₀ q : Program) {xs ys : List Term.Arg} (h : ArgsME xs ys) :
    ∀ (c : CId) (qq : Profile) (params : List Rel) (errs : List RelError),
      paramArgs ⟨q₀, ann, key, lvls, prof⟩ c qq xs params errs =
        paramArgs ⟨q, ann, key, lvls, prof⟩ c qq ys params errs := by
  induction h with
  | nil => intro c qq params errs; cases params <;> rfl
  | cons hab _ ih =>
    intro c qq params errs
    cases params with
    | nil => rfl
    | cons r params => simp only [paramArgs, err]; rw [ih]

private theorem fieldArgs_me (q₀ q : Program) {xs ys : List Term.Arg} (h : ArgsME xs ys) :
    ∀ (c : CId) (qq : Profile) (j : Nat) (fields : List FieldClass) (errs : List RelError),
      fieldArgs ⟨q₀, ann, key, lvls, prof⟩ c qq j xs fields errs =
        fieldArgs ⟨q, ann, key, lvls, prof⟩ c qq j ys fields errs := by
  induction h with
  | nil => intro c qq j fields errs; cases fields <;> rfl
  | cons hab _ ih =>
    intro c qq j fields errs
    cases fields with
    | nil => rfl
    | cons cls fields => simp only [fieldArgs, err]; rw [ih]

private theorem fieldArgs_drop_me (q₀ q : Program) {xs ys : List Term.Arg} (h : ArgsME xs ys) :
    ∀ (n : Nat) (c : CId) (qq : Profile) (j : Nat) (fields : List FieldClass) (errs : List RelError),
      fieldArgs ⟨q₀, ann, key, lvls, prof⟩ c qq j (xs.drop n) fields errs =
        fieldArgs ⟨q, ann, key, lvls, prof⟩ c qq j (ys.drop n) fields errs :=
  fun n => fieldArgs_me q₀ q (h.drop n)

private theorem minorBinders_me (hme : Program.ModeEq p₀ p) (k : CId) (j : Nat) (qc : Profile) :
    ∀ (fields : List FieldClass) (i : Nat) (bs : List Rel) (errs : List RelError),
      minorBinders ⟨p₀, ann, key, lvls, prof⟩ k j qc i bs fields errs =
        minorBinders ⟨p, ann, key, lvls, prof⟩ k j qc i bs fields errs
  | [], i, bs, errs => by cases bs <;> rfl
  | cls :: fields, i, [], errs => by
    simp only [minorBinders, err, fieldWrittenErased_eq hme, minorBinders_me hme k j qc fields]
  | cls :: fields, i, b :: bs, errs => by
    simp only [minorBinders, err, minorBinders_me hme k j qc fields]

private theorem lamHead_me (q₀ q : Program) (errs : List RelError) {h h' : Term} (hh : lamRels h = lamRels h')
    {xs ys : List Term.Arg} (hx : ArgsME xs ys) :
    lamHead ⟨q₀, ann, key, lvls, prof⟩ errs h xs = lamHead ⟨q, ann, key, lvls, prof⟩ errs h' ys := by
  simp only [lamHead, err, hh]
  generalize lamRels h' = bs
  induction hx generalizing bs errs with
  | nil => rfl
  | cons hab _ ih =>
    cases bs with
    | nil => rfl
    | cons b bs => simp only [List.zip_cons_cons, List.foldl_cons]; exact ih _ _

private theorem knownHead_me (hme : Program.ModeEq p₀ p) (errs : List RelError) (c : CId) (us : List Univ)
    {xs ys : List Term.Arg} (hx : ArgsME xs ys) :
    knownHead ⟨p₀, ann, key, lvls, prof⟩ errs c us xs = knownHead ⟨p, ann, key, lvls, prof⟩ errs c us ys := by
  simp only [knownHead, err, partialElim, elimShape?_eq hme, recKindOf_eq hme, ctorProfile_eq hme,
    ruleCtorFields_eq hme, erasedMinors_eq hme, paramArgs_me p₀ p hx, fieldArgs_drop_me p₀ p hx,
    minorBinders_me hme, hx.length_eq]
  decl_me! p₀ p hme c <;> try dsimp only
  all_goals
    cases elimShape? p c with
    | none => rfl
    | some shape =>
      dsimp only
      by_cases hlt : ys.length < shape.arity
      · simp only [hlt, ↓reduceIte]
      · simp only [hlt, ↓reduceIte]
        rcases hx.getElem? shape.major with ⟨h1, h2⟩ | ⟨a, b, m, m', r, h1, h2, hab⟩ <;>
          simp only [h1, h2] <;>
          congr 1 <;>
          funext errs x <;>
          obtain ⟨pos, j, rule⟩ := x <;>
          dsimp only <;>
          rcases hx.getElem? pos with ⟨g1, g2⟩ | ⟨a', b', n, n', r', g1, g2, hab'⟩ <;>
          simp only [g1, g2] <;>
          cases ruleCtorFields p ann shape.recr rule <;>
          first | rfl | (dsimp only; rw [lamRels_me hab'])

private theorem appRule_me (hme : Program.ModeEq p₀ p) (errs : List RelError) {t u : Term} (h : ME t u) (r : Rel) :
    appRule ⟨p₀, ann, key, lvls, prof⟩ errs t r = appRule ⟨p, ann, key, lvls, prof⟩ errs u r := by
  simp only [appRule, argRule, err]
  obtain ⟨hh, ha⟩ := spine_me h
  generalize t.spine = s₀ at hh ha ⊢
  generalize u.spine = s₁ at hh ha ⊢
  obtain ⟨h₀, a₀⟩ := s₀
  obtain ⟨h₁, a₁⟩ := s₁
  dsimp only at hh ha ⊢
  cases hh with
  | const c us => dsimp only; rw [knownHead_me hme errs c us ha]
  | lam bd hd hb => dsimp only; rw [lamHead_me p₀ p errs (lamRels_me (.lam bd hd hb)) ha]
  | _ => rfl

end rules

section check

variable (ann : Ann) (key : TermKey) (lvls : Nat) (prof : Profile)

theorem term_me (hme : Program.ModeEq p₀ p) {t u : Term} (h : ME t u) :
    ∀ (bs : List Rel) (errs : List RelError),
      Check.term ⟨p₀, ann, key, lvls, prof⟩ bs errs t = Check.term ⟨p, ann, key, lvls, prof⟩ bs errs u ∧
      Check.rest ⟨p₀, ann, key, lvls, prof⟩ bs errs t = Check.rest ⟨p, ann, key, lvls, prof⟩ bs errs u := by
  induction h with
  | var i => intro bs errs; exact ⟨rfl, rfl⟩
  | sort s => intro bs errs; exact ⟨rfl, rfl⟩
  | natLit n => intro bs errs; exact ⟨rfl, rfl⟩
  | strLit s => intro bs errs; exact ⟨rfl, rfl⟩
  | pi bd res _ _ _ _ => intro bs errs; exact ⟨rfl, rfl⟩
  | const c us =>
    intro bs errs
    refine ⟨?_, rfl⟩
    simp only [Check.term, bareHead, constHead, partialElim, err, elimShape?_eq hme, erasedMinors_eq hme]
  | app m m' r hf ha ihf iha =>
    intro bs errs
    have ihf2 := fun bs errs => (ihf bs errs).2
    have iha1 := fun bs errs => (iha bs errs).1
    constructor
    · simp only [Check.term, appRule_me hme errs (.app m m' r hf ha) r, ihf2, iha1]
    · simp only [Check.rest, argRule, err, ihf2, iha1]
  | lam bd hd ht ihd iht =>
    intro bs errs
    have iht1 := fun bs errs => (iht bs errs).1
    have hl : lamRule ⟨p₀, ann, key, lvls, prof⟩ errs bd = lamRule ⟨p, ann, key, lvls, prof⟩ errs bd := rfl
    constructor
    · simp only [Check.term]
      rw [hl]
      generalize lamRule ⟨p, ann, key, lvls, prof⟩ errs bd = lr
      obtain ⟨e, b⟩ := lr
      dsimp only
      rw [iht1]
    · simp only [Check.rest]
      rw [hl]
      generalize lamRule ⟨p, ann, key, lvls, prof⟩ errs bd = lr
      obtain ⟨e, b⟩ := lr
      dsimp only
      rw [iht1]
  | letE c r h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    intro bs errs
    have ih₂1 := fun bs errs => (ih₂ bs errs).1
    have ih₃1 := fun bs errs => (ih₃ bs errs).1
    constructor
    · simp only [Check.term, letRule, err, ih₂1, ih₃1]
    · simp only [Check.rest, letRule, err, ih₂1, ih₃1]
  | proj s i he ih =>
    intro bs errs
    have ih1 := fun bs errs => (ih bs errs).1
    constructor
    · simp only [Check.term, projRule, err, onlyCtor?_eq hme, ih1]
    · simp only [Check.rest, projRule, err, onlyCtor?_eq hme, ih1]

private theorem visitKey_eq (hme : Program.ModeEq p₀ p) (marked : List TermKey) (first : Bool) :
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

private theorem visit_eq (hme : Program.ModeEq p₀ p) (annotated : NatMap (List TermKey)) (c : CId)
    (first : Bool) (s : St) :
    visit p₀ ann annotated c prof lvls first s = visit p ann annotated c prof lvls first s := by
  simp only [visit, runtimeKeys_eq hme, visitKey_eq ann lvls prof hme, subsingletonFields_eq hme,
    instRefs_eq hme]

private theorem loop_eq (hme : Program.ModeEq p₀ p) (annotated : NatMap (List TermKey)) :
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
private theorem foldl_keeps {f : List CId → Inst → List CId}
    (hf : ∀ acc x, (∀ c ∈ acc, c ∈ f acc x) ∧ x.1 ∈ f acc x) :
    ∀ (l : List Inst) (acc : List CId), (∀ c ∈ acc, c ∈ l.foldl f acc) ∧ ∀ x ∈ l, x.1 ∈ l.foldl f acc
  | [], _ => ⟨fun _ h => h, fun _ h => by cases h⟩
  | y :: ys, acc => by
    obtain ⟨h1, h2⟩ := foldl_keeps hf ys (f acc y)
    refine ⟨fun c hc => h1 c ((hf acc y).1 c hc), fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h1 _ (hf acc x).2
    · exact h2 x hx

theorem check_reached {q : Program} {ann : Ann} {ch : Checked} (h : check q ann = .ok ch) :
    ∀ inst ∈ ch.instances, inst.1 ∈ ch.reached := by
  unfold check at h
  dsimp only at h
  split at h
  · cases h
  · cases h
    intro inst hi
    rw [List.mem_reverse]
    refine (foldl_keeps (fun acc x => ?_) _ []).2 inst hi
    obtain ⟨c, prof⟩ := x
    dsimp only
    split <;> simp_all

/-! ## `Canonical`, field by field -/

private theorem decl?_back (hme : Program.ModeEq p₀ p) {c : CId} {d : Decl} (h : p.decl? c = some d) :
    ∃ d₀, p₀.decl? c = some d₀ ∧ d₀.type = d.type ∧ DeclME (some d₀) (some d) := by
  have hd := decl?_me hme c
  rw [h] at hd
  generalize p₀.decl? c = o at hd ⊢
  cases hd with
  | same d => exact ⟨d, rfl, rfl, .same d⟩
  | defn k s l ty hv => exact ⟨_, rfl, rfl, .defn k s l ty hv⟩
  | recr sf kk l np nmot nmin ni ind ty hr => exact ⟨_, rfl, rfl, .recr sf kk l np nmot nmin ni ind ty hr⟩

private theorem ctor_back (hme : Program.ModeEq p₀ p) {c : CId} {sf : Bool} {lv : Nat} {ind : CId}
    {j np nf : Nat} {ty : Term} (h : p.decl? c = some (.ctor sf lv ind j np nf ty)) :
    p₀.decl? c = some (.ctor sf lv ind j np nf ty) := by
  obtain ⟨d₀, h₀, -, hd⟩ := decl?_back hme h
  cases hd
  exact h₀

private theorem resolve_back (hme : Program.ModeEq p₀ p) {c : CId} {r : Resolve} (h : p.table.resolveOf c = some r)
    (hr : ∀ thm b, r ≠ .eqn thm b) : p₀.table.resolveOf c = some r := by
  have hm := hme.resolve c
  rw [h] at hm
  generalize p₀.table.resolveOf c = o at hm ⊢
  cases hm with
  | refl => rfl
  | eqn thm hb => exact absurd rfl (hr thm _)

private theorem recr_back (hme : Program.ModeEq p₀ p) {r : CId} {sf k : Bool} {lv np nmot nmin ni : Nat} {ind : CId}
    {rules : List Rule} {ty : Term} (h : p.decl? r = some (.recr sf k lv np nmot nmin ni ind rules ty)) :
    ∃ rules₀, p₀.decl? r = some (.recr sf k lv np nmot nmin ni ind rules₀ ty) ∧ RulesME rules₀ rules := by
  have hd := decl?_me hme r
  rw [h] at hd
  generalize p₀.decl? r = o at hd ⊢
  cases hd with
  | same d => exact ⟨rules, rfl, RulesME.refl _⟩
  | recr _ _ _ _ _ _ _ _ _ hr => exact ⟨_, rfl, hr⟩

private theorem RulesME.mem_back {rs rs' : List Rule} (h : RulesME rs rs') {r' : Rule} (hm : r' ∈ rs') :
    ∃ r ∈ rs, ME r.rhs r'.rhs := by
  induction h with
  | nil => cases hm
  | cons hc hf hmm _ ih =>
    rcases List.mem_cons.1 hm with rfl | hm
    · exact ⟨_, List.mem_cons.2 (Or.inl rfl), hmm⟩
    · obtain ⟨r, hr, h⟩ := ih hm
      exact ⟨r, List.mem_cons.2 (Or.inr hr), h⟩

private theorem BodiesME.mem_back {xs ys : List (TermKey × Term)} (h : BodiesME xs ys) {key : TermKey} {t : Term}
    (hm : (key, t) ∈ ys) : ∃ t₀, (key, t₀) ∈ xs ∧ ME t₀ t := by
  induction h with
  | nil => cases hm
  | cons hab _ ih =>
    rcases List.mem_cons.1 hm with he | hm
    · cases he
      exact ⟨_, List.mem_cons.2 (Or.inl rfl), hab⟩
    · obtain ⟨t₀, h₀, h⟩ := ih hm
      exact ⟨t₀, List.mem_cons.2 (Or.inr h₀), h⟩

private theorem ctorFields_me (hme : Program.ModeEq p₀ p) {rule rule' : Rule} (hc : rule.ctor = rule'.ctor)
    (hf : rule.fields = rule'.fields) : ctorFields p₀ rule = ctorFields p rule' := by
  unfold ctorFields
  rw [hc, hf]
  decl_me p₀ p hme rule'.ctor <;> rfl

private theorem me_var {v : Nat} {b : Term} (h : ME (.var v) b) : b = .var v := by
  cases h; rfl

/-- **`Canonical` transports along `Program.ModeEq`.** (`checkCanonical` itself does not: its `dense`
clause reads the maps' `toList`, which `Program.ModeEq` does not constrain.) -/
theorem canonical_modeEq (hme : Program.ModeEq p₀ p) {ann : Ann} {ch : Checked}
    (h : Canonical p₀ ann ch) : Canonical p ann ch := by
  have hme' := hme.symm
  refine ⟨?consts, ?ctors, ?bodies, ?csimp, ?reads, ?forwards, ?redirects, h.reachedRecord, ?tags,
    ?dense, ?rules, ?univs, ?ctorRecords, ?subsingletonFields, ?finProof, ?minorsRead, ?subRecords⟩
  case dense =>
    intro c hc
    obtain ⟨h1, h2⟩ := h.dense c (by rw [hme.size]; exact hc)
    refine ⟨?_, ?_⟩
    · have he := hme.entry c
      rw [h1] at he
      cases hq : p.entry? c with
      | none => rfl
      | some _ => rw [hq] at he; exact he.elim
    · have hr := hme.resolve c
      rw [h2] at hr
      generalize p.table.resolveOf c = r at hr ⊢
      cases hr
      rfl
  case ctorRecords =>
    intro c hc sf lv ind j np nf ty hd
    exact h.ctorRecords c hc sf lv ind j np nf ty (ctor_back hme hd)
  case minorsRead =>
    intro inst hi cr hcr pos r hap hr
    exact h.minorsRead inst hi cr hcr pos r (by rw [appliedAt_eq hme]; exact hap) hr
  case csimp =>
    intro c hc cr d g us thm hcr hd hres
    obtain ⟨d₀, hd₀, hty, -⟩ := decl?_back hme hd
    rw [← hty]
    exact h.csimp c hc cr d₀ g us thm hcr hd₀ (resolve_back hme hres fun _ _ he => by cases he)
  case redirects =>
    intro c hc g us thm hres shape hs
    rw [← erasedMinors_eq hme]
    exact h.redirects c hc g us thm (resolve_back hme hres fun _ _ he => by cases he) shape
      (by rw [elimShape?_eq hme]; exact hs)
  case finProof =>
    intro c hc w op thm hres fin hfin
    obtain ⟨⟨sf, lv, ind, cidx, np, ty, hd⟩, hk⟩ :=
      h.finProof c hc w op thm (resolve_back hme hres fun _ _ he => by cases he) fin
        (by rw [hme.known]; exact hfin)
    exact ⟨⟨sf, lv, ind, cidx, np, ty, ctor_back hme' hd⟩, hk⟩
  case reads =>
    intro c hc hh d hsh hd i hi
    obtain ⟨d₀, hd₀, hty, -⟩ := decl?_back hme hd
    rw [← readsAt_eq hme]
    exact h.reads c hc hh d₀ (by rw [specialHead?_eq hme]; exact hsh) hd₀ i (by rw [hty]; exact hi)
  case consts =>
    intro c cr hcr
    obtain ⟨d, hd, h1, h2, h3, h4, h5⟩ := h.consts c cr hcr
    obtain ⟨d', hd', hty, -⟩ := decl?_back hme' hd
    have hct : ∀ n, classifyTelescope p [] n d.type = classifyTelescope p₀ [] n d.type := fun n =>
      (classifyTelescope_me hme n .nil (Term.ModeEq.refl _)).symm
    refine ⟨d', hd', ?_⟩
    rw [hty, hct]
    exact ⟨h1, h2, h3, fun op hop => h4 op (resolve_back hme hop fun _ _ he => by cases he),
      fun w op thm hw => h5 w op thm (resolve_back hme hw fun _ _ he => by cases he)⟩
  case ctors =>
    intro c kr hkr
    obtain ⟨sf, lv, ind, cidx, np, nf, ty, hd, h1, h2, h3, h4⟩ := h.ctors c kr hkr
    have hct : ∀ n, classifyTelescope p [] n ty = classifyTelescope p₀ [] n ty := fun n =>
      (classifyTelescope_me hme n .nil (Term.ModeEq.refl _)).symm
    refine ⟨sf, lv, ind, cidx, np, nf, ty, ctor_back hme' hd, h1, ?_, h3, ?_⟩
    · rw [hct]; exact h2
    · intro i actual b exp ha hb
      rw [hct] at hb
      exact h4 i actual b exp ha hb
  case bodies =>
    intro c hc cr d hcr hd key t hmem
    obtain ⟨d₀, hd₀, hty, -⟩ := decl?_back hme hd
    obtain ⟨t₀, hm₀, ht⟩ := (runBodies_me hme c).mem_back hmem
    have hh := h.bodies c hc cr d₀ hcr hd₀ key t₀ hm₀
    rw [hty] at hh
    unfold HeaderOk at hh ⊢
    rw [← lamRels_me ht]
    exact hh
  case tags =>
    intro c hc
    obtain ⟨h1, h2⟩ := h.tags c hc
    refine ⟨fun key t hm => ?_, fun sf k lv np nmot nmin ni ind rules ty hd rule hr => ?_⟩
    · obtain ⟨t₀, hm₀, ht⟩ := (runBodies_me hme c).mem_back hm
      rw [← checkTermBinders_me hme ann ht .nil .nil]
      exact h1 key t₀ hm₀
    · obtain ⟨rules₀, hd₀, hrs⟩ := recr_back hme hd
      obtain ⟨rule₀, hr₀, hm⟩ := hrs.mem_back hr
      rw [← checkTermBinders_me hme ann hm .nil .nil]
      exact h2 sf k lv np nmot nmin ni ind rules₀ ty hd₀ rule₀ hr₀
  case rules =>
    intro c hc shape hs sf k lv np nmot nmin ni ind rules ty hd j rule hrule
    have hR := h.rules c hc shape ((elimShape?_eq hme c).trans hs)
    obtain ⟨rules₀, hd₀, hrs⟩ := recr_back hme hd
    rcases hrs.getElem? j with ⟨h1, h2⟩ | ⟨rule₀, rule', h1, h2, hc', hf', -⟩
    · rw [h2] at hrule; cases hrule
    · have hrr : rule' = rule := Option.some.inj (h2.symm.trans hrule)
      rw [hrr] at hc' hf'
      obtain ⟨sf', lv', np', ty', hk⟩ := hR sf k lv np nmot nmin ni ind rules₀ ty hd₀ j rule₀ h1
      rw [hc', hf'] at hk
      exact ⟨sf', lv', np', ty', ctor_back hme' hk⟩
  case univs =>
    intro c hc
    obtain ⟨h1, h2⟩ := h.univs c hc
    refine ⟨fun key hk t ht => ?_, fun g us thm hres => ?_⟩
    · rw [← runtimeKeys_eq hme] at hk
      obtain ⟨t₀, ht₀, hm⟩ := hme'.termOf ht
      rw [← univsOk_me hme (ME.symm hm)]
      exact h1 key hk t₀ ht₀
    · rw [← univsOk_eq hme]
      exact h2 g us thm (resolve_back hme hres fun _ _ he => by cases he)
  case subRecords =>
    intro c hc shape hs w srcs sf k lv np nmot nmin ni ind rules ty rule hk hd hr
    obtain ⟨rules₀, hd₀, hrs⟩ := recr_back hme hd
    rcases hrs.getElem? 0 with ⟨h1, h2⟩ | ⟨rule₀, rule', h1, h2, hc', -, -⟩
    · rw [h2] at hr; cases hr
    · have hrr : rule' = rule := Option.some.inj (h2.symm.trans hr)
      rw [hrr] at hc'
      rw [← hc']
      exact h.subRecords c hc shape ((elimShape?_eq hme c).trans hs) w srcs sf k lv np nmot nmin ni ind
        rules₀ ty rule₀ ((recKindOf_eq hme _).trans hk) hd₀ h1
  case subsingletonFields =>
    intro c hc shape hs sf k lv np nmot nmin ni ind rules ty w srcs rule hd hk hr
    obtain ⟨rules₀, hd₀, hrs⟩ := recr_back hme hd
    rcases hrs.getElem? 0 with ⟨h1, h2⟩ | ⟨rule₀, rule', h1, h2, hc', hf', -⟩
    · rw [h2] at hr; cases hr
    · have hrr : rule' = rule := Option.some.inj (h2.symm.trans hr)
      rw [hrr] at hc' hf'
      rw [← ctorFields_me hme hc' hf']
      exact h.subsingletonFields c hc shape ((elimShape?_eq hme c).trans hs) sf k lv np nmot nmin ni ind
        rules₀ ty w srcs rule₀ hd₀ ((recKindOf_eq hme _).trans hk) h1
  case forwards =>
    intro c hc sf k lv np nmot nmin ni ind rules ty hd kidx rule hrule i hi hw
    obtain ⟨rules₀, hd₀, hrs⟩ := recr_back hme hd
    rcases hrs.getElem? kidx with ⟨h1, h2⟩ | ⟨rule₀, rule', h1, h2, hc', hf', hm⟩
    · rw [h2] at hrule; cases hrule
    · have hrr : rule' = rule := Option.some.inj (h2.symm.trans hrule)
      rw [hrr] at hc' hf' hm
      have hcf := ctorFields_me hme hc' hf'
      have hwe : fieldWrittenErased p₀ rule₀.ctor i = true := by
        rw [fieldWrittenErased_eq hme, hc']; exact hw
      obtain ⟨hfe, body₀, j, hpeel, hdisp, hmv, hargs⟩ :=
        h.forwards c hc sf k lv np nmot nmin ni ind rules₀ ty hd₀ kidx rule₀ h1 i (by rw [hcf]; exact hi) hwe
      rw [hf'] at hpeel hmv hargs
      have hpl := peelLamsN_me (np + nmot + nmin + rule.fields) hm
      rw [hpeel] at hpl
      cases hq : peelLamsN (np + nmot + nmin + rule.fields) rule.rhs with
      | none => rw [hq] at hpl; exact hpl.elim
      | some body =>
        rw [hq] at hpl
        have hb : ME body₀ body := hpl
        obtain ⟨hsh, hsa⟩ := spine_me hb
        refine ⟨by rw [← hf', ← hcf]; exact hfe, body, j, rfl, (ruleDispatch_me hme c hf' hm).symm.trans hdisp,
          (mentionsVar_me hsh _).symm.trans hmv, fun n a ha => ?_⟩
        rcases hsa.getElem? n with ⟨e₀, e₁⟩ | ⟨a₀, b, m, m', r, e₀, e₁, hab⟩
        · have : body.spine.2[n]? = some a := ha
          rw [e₁] at this; cases this
        · have : body.spine.2[n]? = some a := ha
          rw [e₁] at this
          obtain rfl := Option.some.inj this
          rcases hargs n (a₀, m, r) e₀ with ⟨hn, hv⟩ | hv
          · left
            have hv' : a₀ = .var (rule.fields - 1 - i) := hv
            exact ⟨hn, by rw [hv'] at hab; exact me_var hab⟩
          · right
            exact (mentionsVar_me hab _).symm.trans hv


end IxCC.Src.Relevance.Proof.ModeEq
