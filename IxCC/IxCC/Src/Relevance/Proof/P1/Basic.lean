import IxCC.Src.Relevance.Proof.P1.Defs

/-! # P1, relevance preservation: first lemmas of the core

Facts the core's cases share (`IxCC.Src.Relevance.Proof.P1.Defs` for the definitions): tier C
through a rule's or a closure's leading λs (`termC_peel`), a term with tier C's facts has a `Whole`
value's shape (`wholeTerm_of_termC`), the environment invariant under one more binder
(`envOk_lam`, with `not_shieldedIn_lam`), and, for a recursor fired as δ makes it, no table entry
(`resolve_none_of_recr`), its rules with tier C at its reached instances (`ruleTermC`) and no
parameter written erased (`recr_no_erased`). P1 itself is not proved. -/

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

end IxCC.Src.Relevance.Proof.P1
