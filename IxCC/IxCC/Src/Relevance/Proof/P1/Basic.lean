import IxCC.Src.Relevance.Proof.P1.Defs

/-! # P1, relevance preservation: first lemmas of the core

Facts the core's cases share (`IxCC.Src.Relevance.Proof.P1.Defs` for the definitions): tier C
through a rule's or a closure's leading λs (`termC_peel`), a term with tier C's facts has a `Whole`
value's shape (`wholeTerm_of_termC`), the environment invariant under one more binder
(`envOk_lam`, with `not_shieldedIn_lam`), and, for a recursor fired as δ makes it, no table entry
(`resolve_none_of_recr`), its rules with tier C at its reached instances (`ruleTermC`) and no
parameter written erased (`recr_no_erased`); through leading λs, the binder count, universe
counts and references (`lamRels_length_of_peel`, `univsOk_peel`, `refs_peel` with C6), a runtime
term's references handled (`refsHandled_runtime`, `WellAnnotated.closed`), an environment read
backwards (`rev_get`), and a variable a spine's head does not mention found among its arguments
(`mentionsVar_arg`). P1 itself is not proved. -/

set_option autoImplicit false

namespace IxCC.Src.Relevance.Proof.P1

open IxCC.Src
open Check Check.Canonical

variable {p : Program} {ann : Ann} {ch : Checked}
/-- Tier C through `n` leading λs: the body's binder classes are the λs' classes, innermost first,
before the outer ones. -/
theorem termC_peel {q : Profile} : ∀ (n : Nat) (t body : Term) (bs : List Rel),
    peelLams n t = some body → TermC p ann q bs t →
    TermC p ann q (((lamRels t).take n).reverse ++ bs) body
  | 0, t, body, bs, h, ht => by
    simp only [peelLams, Option.some.injEq] at h
    subst h
    simpa using ht
  | n + 1, t, body, bs, h, ht => by
    cases t with
    | lam b d t =>
      simp only [peelLams] at h
      cases ht with
      | lam _ ht' =>
        have := termC_peel n t body (b.rel :: bs) h ht'
        simpa [lamRels, List.take_succ_cons, List.reverse_cons, List.append_assoc] using this
    | _ => simp [peelLams] at h

/-- A term with tier C's facts has a `Whole` value's shape: no eliminator over a field written
erased heads a spine shorter than its arity (`ElimC`), and none occurs bare (`TermC.const`). -/
theorem wholeTerm_of_termC {q : Profile} {bs : List Rel} {t : Term} (h : TermC p ann q bs t) :
    WholeTerm p t := by
  intro c us shape hhd hs he
  cases h with
  | app hhead _ _ =>
    rw [hhd] at hhead
    obtain ⟨-, helim⟩ := hhead
    have h1 := (helim shape hs).1
    refine Nat.le_of_not_lt fun hlt => ?_
    rw [h1 hlt] at he
    cases he
  | const _ hel =>
    simp only [Term.spineL, Term.spine, Term.spine.go, Term.const.injEq] at hhd
    obtain ⟨rfl, rfl⟩ := hhd
    rw [hel shape hs] at he
    cases he
  | _ => simp [Term.spineL, Term.spine, Term.spine.go] at hhd

/-- No variable is shielded in a λ: its spine's head is the λ itself. -/
theorem not_shieldedIn_lam {x : Nat} {ρ : Env} {b : Binder} {d body : Term} :
    ¬ ShieldedIn x ρ (.lam b d body) := by
  rintro ⟨h, n, s, hh, -⟩
  simp [Term.spineL, Term.spine, Term.spine.go] at hh

/-- The environment invariant under one more binder (β, F2's λs): the new slot is `LiveSlot`
where its binder is relevant. -/
theorem envOk_lam {ls : Levels} {bs : List Rel} {ρ : Env} {b : Binder} {d body : Term} {s : Slot}
    (he : EnvOk p ann ch ls bs ρ (.lam b d body))
    (hs : b.rel.irrAt ls = false → LiveSlot p ann ch s) :
    EnvOk p ann ch ls (b.rel :: bs) (s :: ρ) body := by
  obtain ⟨hlen, hsl⟩ := he
  refine ⟨by simp [hlen], ?_⟩
  intro x s' r hx hr hirr hm _
  cases x with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hr
    subst hx; subst hr
    exact hs hirr
  | succ x =>
    simp only [List.getElem?_cons_succ] at hx hr
    exact hsl x s' r hx hr hirr (by simp [mentionsVar, hm]) not_shieldedIn_lam

/-- A constant whose δ head is a recursor has no table entry. -/
theorem resolve_none_of_recr {r : CId} (hsp : specialHead? p r = some (.recr r)) :
    p.table.resolveOf r = none := by
  cases hr : p.table.resolveOf r with
  | none => rfl
  | some e =>
    unfold specialHead? at hsp
    rw [hr] at hsp
    cases e <;> simp at hsp

/-- The rules of a recursor fired as δ makes it have tier C at its reached instances: they are its
runtime terms. -/
theorem ruleTermC (hf : Facts p ann ch) {r : CId} {q : Profile} (hi : (r, q) ∈ ch.instances)
    (hsp : specialHead? p r = some (.recr r)) {sf kk : Bool} {lv np nmot nmin ni : Nat} {ind : CId}
    {rules : List Rule} {ty : Term} (hd : p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty))
    {j : Nat} {rule : Rule} (hj : rules[j]? = some rule) : TermC p ann q [] rule.rhs := by
  have hres := resolve_none_of_recr hsp
  apply (hf.wa.instsC _ hi).terms (.rule r j)
  · simp only [Program.runtimeKeys, hres, hd, List.mem_map, List.mem_range]
    exact ⟨j, (List.getElem?_eq_some_iff.1 hj).1, rfl⟩
  · simp [Program.termOf, hd, hj]

/-- A reached recursor fired as δ makes it writes no parameter erased: its rules receive every
argument (`readsAt (.recr _) = true`, `Canonical.reads`). F2's pre slots are therefore never
`RecSlotErased`'s first or third clause. -/
theorem recr_no_erased (hf : Facts p ann ch) {r : CId} (hr : r ∈ ch.reached)
    (hsp : specialHead? p r = some (.recr r)) {d : Decl} (hd : p.decl? r = some d) (i : Nat) :
    i ∉ erasedParams d.type := by
  intro hi
  have h := hf.canon.reads r hr (.recr r) d hsp hd i hi
  simp [readsAt, headReadsWith] at h

/-! ## Peeling λs, references, indexing and spines -/


theorem peelLams_eq_peelLamsN : ∀ (n : Nat) (t : Term), peelLams n t = peelLamsN n t
  | 0, t => by simp [peelLams, peelLamsN]
  | n + 1, t => by
    cases t <;> simp [peelLams, peelLamsN, peelLams_eq_peelLamsN n]

theorem lamRels_length_of_peel : ∀ (n : Nat) (t body : Term), peelLams n t = some body →
    n ≤ (lamRels t).length
  | 0, _, _, _ => Nat.zero_le _
  | n + 1, t, body, h => by
    cases t with
    | lam b d t =>
      simp only [peelLams] at h
      have := lamRels_length_of_peel n t body h
      simp only [lamRels, List.length_cons]
      omega
    | _ => simp [peelLams] at h

theorem univsOk_peel : ∀ (n : Nat) (t body : Term), peelLams n t = some body →
    univsOk p t = true → univsOk p body = true
  | 0, t, body, h, hu => by
    simp only [peelLams, Option.some.injEq] at h
    subst h
    exact hu
  | n + 1, t, body, h, hu => by
    cases t with
    | lam b d t =>
      simp only [peelLams] at h
      exact univsOk_peel n t body h (by simpa [univsOk] using hu)
    | _ => simp [peelLams] at h

theorem relevantRefs_append (q : Profile) (t : Term) :
    ∀ acc : List Inst, t.relevantRefs q acc = t.relevantRefs q [] ++ acc := by
  induction t with
  | app f a m r ihf iha =>
    intro acc
    cases hr : r.irrP q
    · simp only [Term.relevantRefs, hr]
      simp only [Bool.false_eq_true, ite_false]
      rw [iha (f.relevantRefs q acc), ihf acc, iha (f.relevantRefs q [])]
      simp
    · simp only [Term.relevantRefs, hr, ite_true]
      exact ihf acc
  | lam b d t _ iht =>
    intro acc
    cases hb : b.propWhen.holdsP q
    · simp only [Term.relevantRefs, hb, Bool.false_eq_true, ite_false]
      exact iht acc
    · simp [Term.relevantRefs, hb]
  | letE c r ty v b _ ihv ihb =>
    intro acc
    cases hr : r.irrP q
    · simp only [Term.relevantRefs, hr, Bool.false_eq_true, ite_false]
      rw [ihb (v.relevantRefs q acc), ihv acc, ihb (v.relevantRefs q [])]
      simp
    · simp only [Term.relevantRefs, hr, ite_true]
      exact ihb acc
  | proj s i e ih =>
    intro acc
    exact ih acc
  | const c us => intro acc; simp [Term.relevantRefs]
  | var _ => intro acc; simp [Term.relevantRefs]
  | sort _ => intro acc; simp [Term.relevantRefs]
  | pi _ _ _ _ _ _ => intro acc; simp [Term.relevantRefs]
  | natLit _ => intro acc; simp [Term.relevantRefs]
  | strLit _ => intro acc; simp [Term.relevantRefs]

theorem mem_foldl_relevantRefs (q : Profile) {x : Inst} : ∀ (ts : List Term) (acc : List Inst),
    (x ∈ acc ∨ ∃ t ∈ ts, x ∈ t.relevantRefs q []) →
      x ∈ ts.foldl (fun acc t => t.relevantRefs q acc) acc
  | [], acc, h => by simpa using h
  | t :: ts, acc, h => by
    simp only [List.foldl_cons]
    apply mem_foldl_relevantRefs q ts
    rw [relevantRefs_append q t acc]
    rcases h with h | ⟨t', ht', hx⟩
    · exact Or.inl (List.mem_append_right _ h)
    · rcases List.mem_cons.1 ht' with rfl | ht'
      · exact Or.inl (List.mem_append_left _ hx)
      · exact Or.inr ⟨t', ht', hx⟩

/-- A runtime term of a reached instance has its references handled (`WellAnnotated.closed`). -/
theorem refsHandled_runtime (hf : Facts p ann ch) {c : CId} {q : Profile} (hi : (c, q) ∈ ch.instances)
    {key : TermKey} (hk : key ∈ p.runtimeKeys c) {t : Term} (ht : p.termOf key = some t) :
    RefsHandled p ch q t := by
  intro x hx
  apply hf.wa.closed (c, q) hi
  simp only [Program.instRefs, List.mem_append, List.mem_reverse]
  left
  exact mem_foldl_relevantRefs q _ [] (Or.inr ⟨t, List.mem_filterMap.2 ⟨key, hk, ht⟩, hx⟩)

/-- Under leading λs that are not proofs at `q` (C6, `TermS.lam`), a body's references are its
term's. -/
theorem refs_peel {lvls : Nat} {q : Profile} : ∀ (n : Nat) (t body : Term) (bs : List Rel),
    peelLams n t = some body → TermS p ann lvls q bs t →
    ∀ x ∈ body.relevantRefs q [], x ∈ t.relevantRefs q []
  | 0, t, body, bs, h, _ => by
    simp only [peelLams, Option.some.injEq] at h
    subst h
    exact fun x hx => hx
  | n + 1, t, body, bs, h, hs => by
    cases t with
    | lam b d t =>
      simp only [peelLams] at h
      cases hs with
      | lam _ _ hp hs' =>
        intro x hx
        simpa [Term.relevantRefs, hp] using refs_peel n t body _ h hs' x hx
    | _ => simp [peelLams] at h

theorem rev_get {α : Type} {l : List α} {x : Nat} {a : α} (h : l.reverse[x]? = some a) :
    x < l.length ∧ l[l.length - 1 - x]? = some a := by
  have hx : x < l.length := by
    have := (List.getElem?_eq_some_iff.1 h).1
    simpa using this
  refine ⟨hx, ?_⟩
  rwa [List.getElem?_reverse hx] at h

theorem mentionsVar_go (x : Nat) : ∀ (t : Term) (acc : List Term.Arg),
    (mentionsVar x (Term.spine.go t acc).1 || (Term.spine.go t acc).2.any (fun (a : Term.Arg) => mentionsVar x a.1)) =
      (mentionsVar x t || acc.any (fun (a : Term.Arg) => mentionsVar x a.1))
  | .app f a m r, acc => by
    simp only [Term.spine.go]
    rw [mentionsVar_go x f]
    simp only [List.any_cons, mentionsVar, Bool.or_assoc]
  | .var _, _ | .sort _, _ | .const .., _ | .lam .., _ | .pi .., _ | .letE .., _ | .proj .., _
  | .natLit _, _ | .strLit _, _ => rfl

/-- A variable a spine mentions but its head does not is mentioned by one of its arguments. -/
theorem mentionsVar_arg {x : Nat} {t : Term} (hm : mentionsVar x t = true)
    (hh : mentionsVar x t.spineL.1 = false) :
    ∃ (m : Nat) (a : Term.Arg), t.spineL.2[m]? = some a ∧ mentionsVar x a.1 = true := by
  have e := mentionsVar_go x t []
  simp only [List.any_nil, Bool.or_false] at e
  have e' : (mentionsVar x t.spineL.1 || t.spineL.2.any fun (a : Term.Arg) => mentionsVar x a.1) = true := by
    rw [← hm, ← e]
    rfl
  rw [hh, Bool.false_or] at e'
  obtain ⟨a, ha, hx⟩ := List.any_eq_true.1 e'
  obtain ⟨m, hm'⟩ := List.mem_iff_getElem?.1 ha
  exact ⟨m, a, hm', hx⟩

end IxCC.Src.Relevance.Proof.P1
