import IxVMRefinement.StatementRel.ReadsMono

/-! # A reading needs the store only at its record, blocks and inductive projections

`ReadsIn.mono` carries a reading to a larger store. The binding fold also needs the other
direction, for stores that differ by records no reading looks inside: inside a reading the store
is read only at blocks (`MemberAt`, a constructor's block) and at inductive projection records
(`IndKeyAt`). So a reading over one store is a reading over another that holds the reading's own
record and every block and inductive projection record of the first (`readsIn_of_agree`).

In the fold, the store before a group's role unit and the store after it differ by the record of
an operation (a definition) or of a standard axiom; neither is a block or an inductive
projection, so every other address reads alike over both.
-/

namespace IxVM.Refinement.Binding

open Ix.Kernel Ix.Kernel.Reader
open IxVM.Consistency
open IxVM.Refinement.ReaderReads

section Agree

variable {t : RoleTable} {store store' : Store}
  {blob blob' : _root_.Address → Option ByteArray}

theorem memberAt_agree
    (hs : ∀ x c, store x = some c →
      (∃ ms, c.info = .muts ms) ∨ (∃ p, c.info = .iPrj p) → store' x = some c)
    {a : _root_.Address} {c : Ixon.Constant} {B : _root_.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {i : Nat} {m : Ixon.MutConst}
    (h : MemberAt store a c B cb ms i m) : MemberAt store' a c B cb ms i m := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  unfold MemberAt
  exact ⟨hs _ _ h1 (Or.inl ⟨ms, h2⟩), h2, h3, h4, h5, h6⟩

theorem indKeyAt_agree
    (hs : ∀ x c, store x = some c →
      (∃ ms, c.info = .muts ms) ∨ (∃ p, c.info = .iPrj p) → store' x = some c)
    {k : Key .anon} {B : _root_.Address} {i : Nat} {ind : Ixon.Inductive}
    (h : IndKeyAt t store k B i ind) : IndKeyAt t store' k B i ind := by
  obtain ⟨a, c, p, cb, ms, h1, h2, h3, h4, h5, h6⟩ := h
  unfold IndKeyAt
  exact ⟨a, c, p, cb, ms, h1, hs _ _ h2 (Or.inr ⟨p, h3⟩), h3, h4, h5, memberAt_agree hs h6⟩

private theorem forall₂_imp' {α β : Type} {R S : α → β → Prop} (H : ∀ a b, R a b → S a b) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → List.Forall₂ S l₁ l₂
  | _, _, .nil => .nil
  | _, _, .cons h rest => .cons (H _ _ h) (forall₂_imp' H rest)

theorem recReads_agree
    (hs : ∀ x c, store x = some c →
      (∃ ms, c.info = .muts ms) ∨ (∃ p, c.info = .iPrj p) → store' x = some c)
    (hb : ∀ x b, blob x = some b → blob' x = some b) {src : Ixon.Constant}
    {self : Nat → Option (ReadM (CName .anon))} {name : Key .anon} {rc : Ixon.Recursor}
    {ci₀ : ConstantInfo .anon}
    (h : RecReads t store blob src self name rc ci₀) :
    RecReads t store' blob' src self name rc ci₀ := by
  obtain ⟨tyP, ty, kF, kM, B, Bm, i, im, ind, indM, ps, rules, h1, h2, h3, h4, h5, h6, h7,
    h8, h9, h10⟩ := h
  unfold RecReads
  exact ⟨tyP, ty, kF, kM, B, Bm, i, im, ind, indM, ps, rules, exprReader_mono hb h1, h2,
    indKeyAt_agree hs h3, h4, indKeyAt_agree hs h5, h6, exprReader_mono hb h7, h8,
    forall₂_imp' (fun _ _ hr => ruleReads_mono hb hr) h9, h10⟩

end Agree

/-- **A reading needs the store only at its record, blocks and inductive projections**
(module docstring). -/
theorem readsIn_of_agree {t : RoleTable} {store store' : Store}
    {blob blob' : _root_.Address → Option ByteArray}
    (hs : ∀ x c, store x = some c →
      (∃ ms, c.info = .muts ms) ∨ (∃ p, c.info = .iPrj p) → store' x = some c)
    (hb : ∀ x b, blob x = some b → blob' x = some b) {a : _root_.Address}
    (htop : ∀ c, store a = some c → store' a = some c)
    {ci₀ : ConstantInfo .anon} (h : ReadsIn t store blob a ci₀) :
    ReadsIn t store' blob' a ci₀ := by
  obtain ⟨c, hc, h⟩ := h
  refine Exists.intro c (And.intro (htop _ hc) ?_)
  generalize c.info = info at h ⊢
  cases info with
  | defn d =>
    obtain ⟨h1, h2⟩ := h
    exact And.intro h1 (defnReads_mono hb h2)
  | axio ax =>
    obtain ⟨h1, h2⟩ := h
    exact And.intro h1 (axiomReads_mono hb h2)
  | quot q => exact quotReads_mono hb h
  | recr rc =>
    obtain ⟨h1, h2⟩ := h
    exact And.intro h1 (recReads_agree hs hb h2)
  | dPrj p =>
    obtain ⟨cb, ms, d, hm, hr⟩ := h
    exact Exists.intro cb (Exists.intro ms (Exists.intro d
      (And.intro (memberAt_agree hs hm) (defnReads_mono hb hr))))
  | iPrj p =>
    obtain ⟨cb, ms, ind, hm, hr⟩ := h
    exact Exists.intro cb (Exists.intro ms (Exists.intro ind
      (And.intro (memberAt_agree hs hm) (indReads_mono hb hr))))
  | cPrj p =>
    obtain ⟨cb, ms, ind, ct, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
    exact Exists.intro cb (Exists.intro ms (Exists.intro ind (Exists.intro ct
      (And.intro (hs _ _ h1 (Or.inl ⟨ms, h2⟩)) (And.intro h2 (And.intro h3 (And.intro h4
        (And.intro h5 (And.intro h6 (And.intro h7 (And.intro h8
          (ctorReads_mono hb h9))))))))))))
  | rPrj p =>
    obtain ⟨cb, ms, rc, hm, hr⟩ := h
    exact Exists.intro cb (Exists.intro ms (Exists.intro rc
      (And.intro (memberAt_agree hs hm) (recReads_agree hs hb hr))))
  | muts ms => exact False.elim h

end IxVM.Refinement.Binding
