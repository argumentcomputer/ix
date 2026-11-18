import IxVMRefinement.FamilyGraph.ProducersEdges

/-! # The family graph's edges have no cycle

`rankEdges_of` gives `RankEdges` at the edges `FamEdge K rank` up to acyclicity. This module
proves acyclicity with a potential `FamRunCtx.pot`, four numbers compared lexicographically, that
grows along every edge into a record that has an edge out (`edge_pot`; a family record with no
member has none):

* a top-walked record bound to a role of the quotient package (`QBound`): `(0, 0, rank, 0)`;
  what it uses is covered or again such a record (`BatchGives.quotBound`);
* a non-empty block of recursors that is the record of a scope check (`RecAnch`: a block's
  family record, a twin): `(rank B + 1, 1, 0, 2)` at the scope's block `B` (one block, by
  `blockOf`), not at its own walk rank;
* a top-walked projection record: its block's potential, the fourth number plus one (a
  projection record the walk checked is canonical and uses nothing);
* any other record: `(μ + 1, τ, ν, 0)`, with `μ` the least of its walk rank (where top-walked)
  and the ranks of the blocks of the scope checks it is a local record of, `τ` 0 where a scope
  check attains `μ` (else 1), `ν` the least position among those.

The scope's block is no local record of any scope check, so its potential is
`(rank B + 1, 1, 0, 0)`; its local records lie at or below it, and what they use lies below them
by the batch's reference facts (`familyRefs`, `adviceRefs`, `contWitness`). -/

universe u

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

set_option linter.unusedVariables false

/-! ## Four numbers, lexicographically -/

/-- A potential: four numbers, compared lexicographically. -/
abbrev Pot := Nat × Nat × Nat × Nat

/-- The lexicographic order on potentials. -/
def PotLt (a b : Pot) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧
    (a.2.2.1 < b.2.2.1 ∨ (a.2.2.1 = b.2.2.1 ∧ a.2.2.2 < b.2.2.2)))))

theorem PotLt.trans {a b c : Pot} (h₁ : PotLt a b) (h₂ : PotLt b c) : PotLt a c := by
  unfold PotLt at *
  omega

theorem PotLt.irrefl (a : Pot) : ¬ PotLt a a := by
  unfold PotLt
  omega

/-- The potential one step above: the fourth number plus one. -/
def Pot.bump (a : Pot) : Pot := (a.1, a.2.1, a.2.2.1, a.2.2.2 + 1)

theorem potLt_bump (a : Pot) : PotLt a a.bump :=
  Or.inr ⟨rfl, Or.inr ⟨rfl, Or.inr ⟨rfl, Nat.lt_succ_self _⟩⟩⟩

@[simp] theorem Pot.bump_fst (a : Pot) : a.bump.1 = a.1 := rfl

/-- Equal in the first three numbers, smaller in the fourth. -/
theorem potLt_fourth {a b c d d' : Nat} (h : d < d') : PotLt (a, b, c, d) (a, b, c, d') :=
  Or.inr ⟨rfl, Or.inr ⟨rfl, Or.inr ⟨rfl, h⟩⟩⟩

/-- Equal in the first two numbers, smaller in the third. -/
theorem potLt_third {a b c c' d d' : Nat} (h : c < c') : PotLt (a, b, c, d) (a, b, c', d') :=
  Or.inr ⟨rfl, Or.inr ⟨rfl, Or.inl h⟩⟩

/-- **At most a local record's potential of the scope at `B`, at position `q`**: below the
block's first number, or equal there with second number 0 and third at most `q`. -/
def LocBound (rank : _root_.Address → Nat) (v : Pot) (B : _root_.Address) (q : Nat) : Prop :=
  v.1 < rank B + 1 ∨ (v.1 = rank B + 1 ∧ v.2.1 = 0 ∧ v.2.2.1 ≤ q)

theorem LocBound.bump {rank : _root_.Address → Nat} {v : Pot} {B : _root_.Address} {q : Nat}
    (h : LocBound rank v B q) : LocBound rank v.bump B q :=
  h

theorem LocBound.lt_local {rank : _root_.Address → Nat} {v : Pot} {B : _root_.Address}
    {q p : Nat} (h : LocBound rank v B q) (hq : q < p) : PotLt v (rank B + 1, 0, p, 0) := by
  rcases h with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, Or.inr ⟨h2, Or.inl (Nat.lt_of_le_of_lt h3 hq)⟩⟩

theorem LocBound.lt_block {rank : _root_.Address → Nat} {v : Pot} {B : _root_.Address}
    {q : Nat} (h : LocBound rank v B q) (w : Nat) : PotLt v (rank B + 1, 1, 0, w) := by
  rcases h with h | ⟨h1, h2, -⟩
  · exact Or.inl h
  · refine Or.inr ⟨h1, Or.inl ?_⟩
    show v.2.1 < 1
    rw [h2]
    exact Nat.zero_lt_one

/-! ## The potential -/

namespace FamRunCtx

variable (K : FamRunCtx) (rank : _root_.Address → Nat)

/-- A top-walked record bound to no walked role and to a role of the quotient package. -/
def QBound (n : _root_.Address) : Prop :=
  K.Top n ∧ ¬ Covered K.t n ∧ ∃ ro, quotRole ro = true ∧ K.t.addressOf? ro = some n

/-- A non-empty block of recursors that is the record of a scope check. -/
def RecAnch (n : _root_.Address) : Prop :=
  ∃ B cs, K.ScopeAt B n cs ∧ RecBlock K.E₀ n

/-- `k` is the walk rank of the record (top-walked), or the rank of the block of a scope check it
is a local record of. -/
def Anchor (n : _root_.Address) (k : Nat) : Prop :=
  (K.Top n ∧ k = rank n) ∨ ∃ B rb cs p, K.ScopeAt B rb cs ∧ K.LocalAt B rb cs n p ∧ k = rank B

open Classical in
/-- The least anchor. -/
noncomputable def mu (n : _root_.Address) : Nat :=
  if h : ∃ k, K.Anchor rank n k then Nat.find h else 0

/-- A scope check attaining the least anchor has the record local at position `p`. -/
def AtMu (n : _root_.Address) (p : Nat) : Prop :=
  ∃ B rb cs, K.ScopeAt B rb cs ∧ K.LocalAt B rb cs n p ∧ rank B = K.mu rank n

open Classical in
/-- The least position at a scope check attaining the least anchor. -/
noncomputable def nu (n : _root_.Address) : Nat :=
  if h : ∃ p, K.AtMu rank n p then Nat.find h else 0

open Classical in
/-- The potential of a record that is no top-walked projection record. -/
noncomputable def pot0 (n : _root_.Address) : Pot :=
  if _hq : K.QBound n then (0, 0, rank n, 0)
  else if h : K.RecAnch n then (rank (Classical.choose h) + 1, 1, 0, 2)
  else (K.mu rank n + 1, (if _ha : ∃ p, K.AtMu rank n p then 0 else 1), K.nu rank n, 0)

/-- A top-walked projection record. -/
def TopProj (n : _root_.Address) : Prop :=
  K.Top n ∧ ∃ c, recordOf K.E₀ n = some c ∧ IsProj c

open Classical in
/-- **The potential** (module docstring). -/
noncomputable def pot (n : _root_.Address) : Pot :=
  if h : K.TopProj n then (K.pot0 rank (Ix.Cert.ownerOf n (Classical.choose h.2))).bump
  else K.pot0 rank n

end FamRunCtx

section Potential

variable {K : FamRunCtx} {seeds : List _root_.Address} {rank : _root_.Address → Nat}

/-! ### Unfolding the potential -/

theorem FamRunCtx.mu_le {n : _root_.Address} {k : Nat} (h : K.Anchor rank n k) :
    K.mu rank n ≤ k := by
  classical
  have hex : ∃ k, K.Anchor rank n k := ⟨k, h⟩
  unfold FamRunCtx.mu
  rw [dite_eq_left hex]
  exact Nat.find_min' hex h

theorem FamRunCtx.mu_spec {n : _root_.Address} (hex : ∃ k, K.Anchor rank n k) :
    K.Anchor rank n (K.mu rank n) := by
  classical
  unfold FamRunCtx.mu
  rw [dite_eq_left hex]
  exact Nat.find_spec hex

theorem FamRunCtx.nu_le {n : _root_.Address} {p : Nat} (h : K.AtMu rank n p) :
    K.nu rank n ≤ p := by
  classical
  have hex : ∃ p, K.AtMu rank n p := ⟨p, h⟩
  unfold FamRunCtx.nu
  rw [dite_eq_left hex]
  exact Nat.find_min' hex h

theorem FamRunCtx.nu_spec {n : _root_.Address} (hex : ∃ p, K.AtMu rank n p) :
    K.AtMu rank n (K.nu rank n) := by
  classical
  unfold FamRunCtx.nu
  rw [dite_eq_left hex]
  exact Nat.find_spec hex

theorem FamRunCtx.nu_none {n : _root_.Address} (hex : ¬ ∃ p, K.AtMu rank n p) :
    K.nu rank n = 0 := by
  unfold FamRunCtx.nu
  rw [dite_eq_right hex]

theorem FamRunCtx.pot0_Q {n : _root_.Address} (hq : K.QBound n) :
    K.pot0 rank n = (0, 0, rank n, 0) := by
  unfold FamRunCtx.pot0
  rw [dite_eq_left hq]

theorem FamRunCtx.pot0_rec {n B : _root_.Address} (hq : ¬ K.QBound n) (hr : K.RecAnch n)
    (hu : ∀ B' cs', K.ScopeAt B' n cs' → B' = B) :
    K.pot0 rank n = (rank B + 1, 1, 0, 2) := by
  unfold FamRunCtx.pot0
  rw [dite_eq_right hq, dite_eq_left hr]
  obtain ⟨cs, hS, -⟩ := Classical.choose_spec hr
  rw [hu _ cs hS]

theorem FamRunCtx.pot0_at {n : _root_.Address} (hq : ¬ K.QBound n) (hr : ¬ K.RecAnch n)
    (ha : ∃ p, K.AtMu rank n p) :
    K.pot0 rank n = (K.mu rank n + 1, 0, K.nu rank n, 0) := by
  unfold FamRunCtx.pot0
  rw [dite_eq_right hq, dite_eq_right hr, dite_eq_left ha]

theorem FamRunCtx.pot0_own {n : _root_.Address} (hq : ¬ K.QBound n) (hr : ¬ K.RecAnch n)
    (ha : ¬ ∃ p, K.AtMu rank n p) :
    K.pot0 rank n = (K.mu rank n + 1, 1, 0, 0) := by
  unfold FamRunCtx.pot0
  rw [dite_eq_right hq, dite_eq_right hr, dite_eq_right ha, FamRunCtx.nu_none ha]

theorem FamRunCtx.pot0_fst {n : _root_.Address} (hq : ¬ K.QBound n) (hr : ¬ K.RecAnch n) :
    (K.pot0 rank n).1 = K.mu rank n + 1 := by
  by_cases ha : ∃ p, K.AtMu rank n p
  · rw [FamRunCtx.pot0_at hq hr ha]
  · rw [FamRunCtx.pot0_own hq hr ha]

theorem FamRunCtx.pot_proj {n : _root_.Address} {c : Ixon.Constant} (hT : K.Top n)
    (hc : recordOf K.E₀ n = some c) (hp : IsProj c) :
    K.pot rank n = (K.pot0 rank (Ix.Cert.ownerOf n c)).bump := by
  have h : K.TopProj n := ⟨hT, c, hc, hp⟩
  unfold FamRunCtx.pot
  rw [dite_eq_left h]
  have e : Classical.choose h.2 = c :=
    Option.some.inj ((Classical.choose_spec h.2).1.symm.trans hc)
  rw [e]

theorem FamRunCtx.pot_nproj {n : _root_.Address} (h : ¬ K.TopProj n) :
    K.pot rank n = K.pot0 rank n := by
  unfold FamRunCtx.pot
  rw [dite_eq_right h]

/-! ### Kinds of records -/

/-- A record that is no projection record is no top-walked projection record. -/
theorem FamRunCtx.not_topProj {n : _root_.Address} {c : Ixon.Constant}
    (hc : recordOf K.E₀ n = some c) (hnp : ¬ IsProj c) : ¬ K.TopProj n := by
  rintro ⟨-, c', hc', hp⟩
  rw [hc] at hc'
  cases hc'
  exact hnp hp

theorem notProj_of_block {c : Ixon.Constant} {ms : Array Ixon.MutConst} (h : c.info = .muts ms) :
    ¬ IsProj c :=
  fun hp => proj_not_block hp ⟨ms, h⟩

theorem notProj_of_standalone {c : Ixon.Constant} (h : Standalone c) : ¬ IsProj c :=
  fun hp => standalone_not_proj h hp

/-- A quotient-bound record is standalone (`quotBound`). -/
theorem FamRunCtx.QBound.standalone (hG : TopGraph K.t K.E₀ seeds K.Top rank)
    (hB : BatchGives K) {n : _root_.Address} (hq : K.QBound n) :
    ∃ c, recordOf K.E₀ n = some c ∧ Standalone c := by
  obtain ⟨hT, -, ro, hro, ha⟩ := hq
  obtain ⟨c, hc⟩ := hG.record n hT
  exact ⟨c, hc, (hB.quotBound n ro c hT hro ha hc).1⟩

theorem FamRunCtx.not_Q_of_block (hG : TopGraph K.t K.E₀ seeds K.Top rank)
    (hB : BatchGives K) {n : _root_.Address} {c : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hc : recordOf K.E₀ n = some c) (hms : c.info = .muts ms) : ¬ K.QBound n := by
  intro hq
  obtain ⟨c', hc', hs⟩ := FamRunCtx.QBound.standalone hG hB hq
  rw [hc] at hc'
  cases hc'
  exact standalone_not_block hs ⟨ms, hms⟩

theorem FamRunCtx.not_Q_of_proj (hG : TopGraph K.t K.E₀ seeds K.Top rank)
    (hB : BatchGives K) {n : _root_.Address} {c : Ixon.Constant}
    (hc : recordOf K.E₀ n = some c) (hp : IsProj c) : ¬ K.QBound n := by
  intro hq
  obtain ⟨c', hc', hs⟩ := FamRunCtx.QBound.standalone hG hB hq
  rw [hc] at hc'
  cases hc'
  exact standalone_not_proj hs hp

theorem FamRunCtx.not_recAnch_of_record {n : _root_.Address} {c : Ixon.Constant}
    (hc : recordOf K.E₀ n = some c) (h : ∀ rs, c.info = .muts rs → ¬ 0 < rs.size ∨
      ¬ ∀ m ∈ rs.toList, ∃ r, m = Ixon.MutConst.recr r) : ¬ K.RecAnch n := by
  rintro ⟨B, cs, -, c', rs, hc', hrs, hpos, hall⟩
  rw [hc] at hc'
  cases hc'
  rcases h rs hrs with h | h
  · exact h hpos
  · exact h hall

theorem FamRunCtx.not_recAnch_of_standalone {n : _root_.Address} {c : Ixon.Constant}
    (hc : recordOf K.E₀ n = some c) (hs : Standalone c) : ¬ K.RecAnch n :=
  FamRunCtx.not_recAnch_of_record hc fun rs hrs => (standalone_not_block hs ⟨rs, hrs⟩).elim

theorem FamRunCtx.not_recAnch_of_indBlock {n : _root_.Address} (h : IndBlock K.E₀ n) :
    ¬ K.RecAnch n := by
  rintro ⟨B, cs, -, hRB⟩
  exact hRB.not_indBlock h

/-- **The block of a record of scope checks is one**: two scope checks with a non-empty record
are of one block (`blockOf`). -/
theorem FamRunCtx.recAnch_unique (hB : BatchGives K) {n B B' : _root_.Address}
    {cs cs' : List (Call F)} (hRB : RecBlock K.E₀ n) (hS : K.ScopeAt B n cs)
    (hS' : K.ScopeAt B' n cs') : B' = B :=
  FamRunCtx.block_unique hB hRB ⟨cs', hS'.1⟩ ⟨cs, hS.1⟩

theorem FamRunCtx.pot0_scopeRec (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K)
    {n B : _root_.Address} {cs : List (Call F)} (hS : K.ScopeAt B n cs)
    (hRB : RecBlock K.E₀ n) : K.pot0 rank n = (rank B + 1, 1, 0, 2) := by
  obtain ⟨c, rs, hc, hrs, -, -⟩ := id hRB
  exact FamRunCtx.pot0_rec (FamRunCtx.not_Q_of_block hG hB hc hrs) ⟨B, cs, hS, hRB⟩
    fun B' cs' hS' => FamRunCtx.recAnch_unique hB hRB hS hS'

theorem FamRunCtx.pot_scopeRec (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K)
    {n B : _root_.Address} {cs : List (Call F)} (hS : K.ScopeAt B n cs)
    (hRB : RecBlock K.E₀ n) : K.pot rank n = (rank B + 1, 1, 0, 2) := by
  obtain ⟨c, rs, hc, hrs, -, -⟩ := id hRB
  rw [FamRunCtx.pot_nproj (FamRunCtx.not_topProj hc (notProj_of_block hrs))]
  exact FamRunCtx.pot0_scopeRec hG hB hS hRB

/-- A local record has a record that is no projection record. -/
theorem FamRunCtx.localAt_notProj {B rb : _root_.Address} {cs : List (Call F)}
    {a : _root_.Address} {p : Nat} (h : K.LocalAt B rb cs a p) :
    ∃ c, recordOf K.E₀ a = some c ∧ ¬ IsProj c := by
  rcases h with ⟨-, -, -, -, -, -, -, ca, x, hca, hx⟩ | ⟨-, -, -, ca, hca, hs⟩ |
    ⟨-, -, x, ca, -, -, hca, hx⟩
  · exact ⟨ca, hca, constAddr_not_proj hx⟩
  · exact ⟨ca, hca, notProj_of_standalone hs⟩
  · exact ⟨ca, hca, constAddr_not_proj hx⟩

/-- **The block of a scope check is no local record of any scope check**: no own advice walk
lists it (`listedNotScope`), it is no standalone record, and it is no twin (a block of
inductive types). -/
theorem FamRunCtx.scope_not_local (hB : BatchGives K) {B rb : _root_.Address}
    {cs : List (Call F)} (hS : K.ScopeAt B rb cs) {B' rb' : _root_.Address}
    {cs' : List (Call F)} {p : Nat} (hS' : K.ScopeAt B' rb' cs') :
    ¬ K.LocalAt B' rb' cs' B p := by
  obtain ⟨cb, ms, hcb, hms, hpos, hall⟩ := hS.2.2.1
  rintro (⟨advAs, k, b, hown, hb, hba, -⟩ | ⟨-, -, -, ca, hca, hs⟩ | ⟨-, ⟨B'', htw⟩, -⟩)
  · exact hB.listedNotScope B rb cs B' rb' cs' advAs k b hS hS' hown hb hba
  · rw [hcb] at hca
    cases hca
    exact standalone_not_block hs ⟨ms, hms⟩
  · exact (FamRunCtx.twin_facts htw).1.not_indBlock hS.2.2.1

/-- **The potential of a scope check's block**: `(rank B + 1, 1, 0, 0)`. -/
theorem FamRunCtx.pot0_scope (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K)
    {B rb : _root_.Address} {cs : List (Call F)} (hS : K.ScopeAt B rb cs) :
    K.pot0 rank B = (rank B + 1, 1, 0, 0) := by
  obtain ⟨cb, ms, hcb, hms, hpos, hall⟩ := hS.2.2.1
  have hq := FamRunCtx.not_Q_of_block hG hB hcb hms
  have hr := FamRunCtx.not_recAnch_of_indBlock (K := K) hS.2.2.1
  have hna : ¬ ∃ p, K.AtMu rank B p := by
    rintro ⟨p, B', rb', cs', hS', hl, -⟩
    exact FamRunCtx.scope_not_local hB hS hS' hl
  rw [FamRunCtx.pot0_own hq hr hna]
  have hmu : K.mu rank B = rank B := by
    rcases FamRunCtx.mu_spec (K := K) (rank := rank) ⟨rank B, Or.inl ⟨hS.2.1, rfl⟩⟩ with
      ⟨-, h⟩ | ⟨B', rb', cs', p, hS', hl, -⟩
    · exact h
    · exact (FamRunCtx.scope_not_local hB hS hS' hl).elim
  rw [hmu]

theorem FamRunCtx.pot_scope (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K)
    {B rb : _root_.Address} {cs : List (Call F)} (hS : K.ScopeAt B rb cs) :
    K.pot rank B = (rank B + 1, 1, 0, 0) := by
  obtain ⟨cb, ms, hcb, hms, -, -⟩ := hS.2.2.1
  rw [FamRunCtx.pot_nproj (FamRunCtx.not_topProj hcb (notProj_of_block hms))]
  exact FamRunCtx.pot0_scope hG hB hS

/-! ### Walk facts -/

/-- **A non-empty record of a scope check lies above its block in the walk** (`recUsesBlock`). -/
theorem FamRunCtx.rec_above
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K)
    {B n : _root_.Address} {cs : List (Call F)} (hS : K.ScopeAt B n cs)
    (hRB : RecBlock K.E₀ n) (hT : K.Top n) : Relation.TransGen (WStep K) B n := by
  obtain ⟨c, rs, hc, hrs, hpos, -⟩ := hRB
  obtain ⟨cb, y, hcb, hy, hcy, huy⟩ := hB.recUsesBlock B n cs hS c rs hc hrs hpos
  have hTy : K.Top y := by
    rcases hW.closed n y hT huy with ⟨h, -⟩ | h
    · exact h
    · exact absurd h hcy
  rcases hy with ⟨-, hs⟩ | ⟨ms', i, m, hms', hm, hyx⟩
  · obtain ⟨cb', ms, hcb', hms, -, -⟩ := hS.2.2.1
    rw [hcb] at hcb'
    cases hcb'
    exact (standalone_not_block hs ⟨ms, hms⟩).elim
  · obtain ⟨P, hP, hPp, hPo⟩ := hG.block_record hS.2.1 hcb hms' hm hyx
    exact .tail (.single ⟨hTy, hS.2.1, Or.inr ⟨P, hP, hPp, hPo.symm⟩⟩)
      ⟨hT, hTy, Or.inl ⟨huy, hcy⟩⟩

/-- The first number of a top-walked record's potential is at most its walk rank plus one. -/
theorem FamRunCtx.pot0_fst_le
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K)
    {m : _root_.Address} (hT : K.Top m) : (K.pot0 rank m).1 ≤ rank m + 1 := by
  by_cases hq : K.QBound m
  · rw [FamRunCtx.pot0_Q hq]
    exact Nat.zero_le _
  by_cases hr : K.RecAnch m
  · obtain ⟨B, cs, hS, hRB⟩ := hr
    rw [FamRunCtx.pot0_scopeRec hG hB hS hRB]
    have := transGen_rank_lt hW (FamRunCtx.rec_above hW hG hB hS hRB hT)
    show rank B + 1 ≤ rank m + 1
    omega
  · rw [FamRunCtx.pot0_fst hq hr]
    have := FamRunCtx.mu_le (K := K) (rank := rank) (Or.inl ⟨hT, rfl⟩ : K.Anchor rank m (rank m))
    omega

theorem FamRunCtx.pot_fst_le
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K)
    {w : _root_.Address} (hT : K.Top w) : (K.pot rank w).1 ≤ rank w + 1 := by
  by_cases hp : K.TopProj w
  · obtain ⟨-, c, hc, hpc⟩ := hp
    rw [FamRunCtx.pot_proj hT hc hpc, Pot.bump_fst]
    obtain ⟨hTo, hr⟩ := hW.owner w c hT hc hpc
    have := FamRunCtx.pot0_fst_le hW hG hB hTo
    omega
  · rw [FamRunCtx.pot_nproj hp]
    exact FamRunCtx.pot0_fst_le hW hG hB hT

/-- **A top-walked record below `B` has a potential below `B`'s in the first number.** -/
theorem FamRunCtx.below_bound
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K)
    {w B : _root_.Address} (hT : K.Top w) (hwB : Relation.TransGen (WStep K) w B) :
    (K.pot rank w).1 < rank B + 1 := by
  have h1 := FamRunCtx.pot_fst_le hW hG hB hT
  have h2 := transGen_rank_lt hW hwB
  omega

/-- A constant address of a top-walked record is the record itself or holds a projection
record of it. -/
theorem constAddr_cases_top (hG : TopGraph K.t K.E₀ seeds K.Top rank)
    {D w : _root_.Address} {cD : Ixon.Constant} (hT : K.Top D)
    (hc : recordOf K.E₀ D = some cD) (hw : ConstAddrOf D cD w) :
    (w = D ∧ Standalone cD) ∨
      ∃ P, recordOf K.E₀ w = some P ∧ IsProj P ∧ Ix.Cert.ownerOf w P = D := by
  rcases hw with h | ⟨ms, i, m, hms, hm, hx⟩
  · exact Or.inl h
  · exact Or.inr (hG.block_record hT hc hms hm hx)

/-- **A top-walked constant address of a top-walked record below `B` has a potential below
`B`'s in the first number.** -/
theorem FamRunCtx.constAddr_bound
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K)
    {D w B : _root_.Address} {cD : Ixon.Constant} (hTD : K.Top D)
    (hc : recordOf K.E₀ D = some cD) (hw : ConstAddrOf D cD w) (hTw : K.Top w)
    (hDB : Relation.TransGen (WStep K) D B) : (K.pot rank w).1 < rank B + 1 := by
  rcases constAddr_cases_top hG hTD hc hw with ⟨rfl, -⟩ | ⟨P, hP, hPp, hPo⟩
  · exact FamRunCtx.below_bound hW hG hB hTD hDB
  · rw [FamRunCtx.pot_proj hTw hP hPp, Pot.bump_fst, hPo]
    have h1 := FamRunCtx.pot0_fst_le hW hG hB hTD
    have h2 := transGen_rank_lt hW hDB
    omega

/-- A canonical projection record uses nothing. -/
theorem memberProjection_noUse {E₀ : Ixon.Env} {z y D : _root_.Address} {i : Nat}
    {m : Ixon.MutConst} (hz : recordOf E₀ z = some (memberProjection D i m)) :
    ¬ UsedRef E₀ z y := by
  rintro ⟨c, k, hc, hk, -⟩
  rw [hz] at hc
  cases hc
  cases m <;> exact absurd hk (by simp [IxVM.Consistency.usedRefIdxs, memberProjection])

theorem constructorProjection_noUse {E₀ : Ixon.Env} {z y D : _root_.Address} {i j : Nat}
    (hz : recordOf E₀ z = some (constructorProjection D i j)) : ¬ UsedRef E₀ z y := by
  rintro ⟨c, k, hc, hk, -⟩
  rw [hz] at hc
  cases hc
  exact absurd hk (by simp [IxVM.Consistency.usedRefIdxs, constructorProjection])

/-- **A top-walked projection record uses nothing**: it is its block's canonical projection
record (`TopGraph.projMember`, `TopGraph.members`). -/
theorem FamRunCtx.topProj_noUse
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) {z y : _root_.Address} {c : Ixon.Constant}
    (hT : K.Top z) (hc : recordOf K.E₀ z = some c) (hp : IsProj c) : ¬ UsedRef K.E₀ z y := by
  obtain ⟨hTo, -⟩ := hW.owner z c hT hc hp
  obtain ⟨cb, hcb, hz⟩ := hG.projMember z c hT hc hp
  rcases hz with ⟨h, hs⟩ | ⟨ms, i, m, hms, hm, hx⟩
  · rw [← h, hc] at hcb
    cases hcb
    exact absurd hp (notProj_of_standalone hs)
  · obtain ⟨hmem, hctor⟩ := hG.members _ cb ms hTo hcb hms i m hm
    rcases hx with hx | ⟨ind, j, hind, hj, hx⟩
    · rw [hx]
      exact memberProjection_noUse hmem
    · rw [hx]
      exact constructorProjection_noUse (hctor ind j hind hj)

/-- The block of a top-walked projection record is no projection record. -/
theorem FamRunCtx.owner_notTopProj
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) {z : _root_.Address} {c : Ixon.Constant}
    (hT : K.Top z) (hc : recordOf K.E₀ z = some c) (hp : IsProj c) :
    ¬ K.TopProj (Ix.Cert.ownerOf z c) := by
  obtain ⟨cb, hcb, hz⟩ := hG.projMember z c hT hc hp
  rcases hz with ⟨h, hs⟩ | ⟨ms, i, m, hms, hm, hx⟩
  · rw [← h, hc] at hcb
    cases hcb
    exact absurd hp (notProj_of_standalone hs)
  · exact FamRunCtx.not_topProj hcb (notProj_of_block hms)

/-! ### Local records and their references -/

/-- **A twin witnessed as a container's recursor of a scope check is a twin of a block below the
scope's block**: the witness is a constant address of a block of recursors whose family check
with the block it eliminates is among the scope check's calls (`contWitness`), that block of
recursors is the twin (both hold the witness's projection record), and its family checks are of
one block. -/
theorem FamRunCtx.twinLocal_below
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hB : BatchGives K) {B rb : _root_.Address} {cs : List (Call F)} (hS : K.ScopeAt B rb cs)
    {a x B' : _root_.Address} {ca : Ixon.Constant} (htw : K.twin a = some B')
    (hwit : K.ContWitness cs B x) (hcov : ¬ Covered K.t x) (hca : recordOf K.E₀ a = some ca)
    (hxa : ConstAddrOf a ca x) : Relation.TransGen (WStep K) B' B := by
  obtain ⟨hRB, -, -, hFC⟩ := FamRunCtx.twin_facts htw
  obtain ⟨crb, rs, hF⟩ := hB.record B' a hFC
  have e : crb = ca := Option.some.inj (hF.record.symm.trans hca)
  rw [← e] at hxa
  obtain ⟨P, hP, hPp, hPo⟩ := hF.constAddr hxa
  obtain ⟨ib, hdep, -, -, -, hkind⟩ := hB.contWitness B rb cs x hS hwit hcov
  obtain ⟨-, hiB⟩ := dep_top hW hdep hS.2.1
  rcases hkind with ⟨cx, hcx, hs⟩ | ⟨a', ca', cs', hca', hxa', hRB', hFC', -⟩
  · rw [hcx] at hP
    cases hP
    exact absurd hPp (notProj_of_standalone hs)
  · obtain ⟨crb', rs', hF'⟩ := hB.record ib a' ⟨cs', hFC'⟩
    have e' : crb' = ca' := Option.some.inj (hF'.record.symm.trans hca')
    rw [← e'] at hxa'
    obtain ⟨P', hP', -, hPo'⟩ := hF'.constAddr hxa'
    rw [hP] at hP'
    cases hP'
    have haa : a' = a := hPo'.symm.trans hPo
    rw [haa] at hFC'
    have hib : ib = B' := FamRunCtx.block_unique hB hRB ⟨cs', hFC'⟩ hFC
    rw [← hib]
    exact hiB

/-- A twin is the record of a scope check of its block. -/
theorem FamRunCtx.twin_scope {a B' : _root_.Address} (htw : K.twin a = some B') :
    ∃ cs, K.ScopeAt B' a cs := by
  rcases FamRunCtx.twin_some htw with hto | ⟨-, hTB, hIB, B₀, rb₀, hR, cs₀, hc₀, cs', hc', hsub⟩
  · exact ⟨K.famCalls B' a, FamRunCtx.famCalls_spec hto.2.2.2.2.1, hto.2.2.2.2.2.1,
      hto.2.2.2.2.2.2.2, B', a, K.famCalls B' a, .top hto,
      FamRunCtx.famCalls_spec hto.2.2.2.2.1, fun _ h => h⟩
  · exact ⟨cs', hc', hTB, hIB, B₀, rb₀, cs₀, hR, hc₀, hsub⟩

/-- **A local record's potential is at most a local record's of its scope at its position.** -/
theorem FamRunCtx.local_bound
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K)
    {B rb : _root_.Address} {cs : List (Call F)} {ℓ : _root_.Address} {q : Nat}
    (hS : K.ScopeAt B rb cs) (hl : K.LocalAt B rb cs ℓ q) :
    LocBound rank (K.pot rank ℓ) B q := by
  obtain ⟨cℓ, hcℓ, hnp⟩ := FamRunCtx.localAt_notProj hl
  rw [FamRunCtx.pot_nproj (FamRunCtx.not_topProj hcℓ hnp)]
  by_cases hq : K.QBound ℓ
  · rw [FamRunCtx.pot0_Q hq]
    exact Or.inl (Nat.succ_pos _)
  -- a twin: at its own block, below the scope's block
  by_cases htw : ∃ B', K.twin ℓ = some B'
  · obtain ⟨B', htw⟩ := htw
    obtain ⟨cs', hS'⟩ := FamRunCtx.twin_scope htw
    rw [FamRunCtx.pot0_scopeRec hG hB hS' (FamRunCtx.twin_facts htw).1]
    have hbelow : Relation.TransGen (WStep K) B' B := by
      rcases hl with ⟨advAs, k, b, hown, hb, hba, -⟩ | ⟨-, -, -, ca, hca, hs⟩ |
        ⟨-, -, x, ca, hwit, hcov, hca, hxa⟩
      · -- listed advice is no block of recursors
        exact (hB.listedNotRec B rb cs advAs k b hS hown hb
          (by rw [hba]; exact (FamRunCtx.twin_facts htw).1)).elim
      · exact (FamRunCtx.not_recAnch_of_standalone hca hs
          ⟨B', cs', hS', (FamRunCtx.twin_facts htw).1⟩).elim
      · exact FamRunCtx.twinLocal_below hW hB hS htw hwit hcov hca hxa
    have := transGen_rank_lt hW hbelow
    exact Or.inl (by show rank B' + 1 < rank B + 1; omega)
  · -- no block of recursors of a scope check: listed advice or a standalone witness
    have hr : ¬ K.RecAnch ℓ := by
      rintro ⟨B', cs', hS', hRB⟩
      rcases hl with ⟨advAs, k, b, hown, hb, hba, -⟩ | ⟨-, -, -, ca, hca, hs⟩ | ⟨-, htw', -⟩
      · exact hB.listedNotRec B rb cs advAs k b hS hown hb (by rw [hba]; exact hRB)
      · exact FamRunCtx.not_recAnch_of_standalone hca hs ⟨B', cs', hS', hRB⟩
      · exact htw htw'
    have hmu : K.mu rank ℓ ≤ rank B :=
      FamRunCtx.mu_le (Or.inr ⟨B, rb, cs, q, hS, hl, rfl⟩)
    rcases Nat.lt_or_eq_of_le hmu with hlt | heq
    · refine Or.inl ?_
      rw [FamRunCtx.pot0_fst hq hr]
      omega
    · have hat : K.AtMu rank ℓ q := ⟨B, rb, cs, hS, hl, heq.symm⟩
      rw [FamRunCtx.pot0_at hq hr ⟨q, hat⟩]
      exact Or.inr ⟨by rw [heq], rfl, FamRunCtx.nu_le hat⟩

/-- **A container's recursor a scope check witnesses, top-walked and bound to no walked role, has
a potential at most a local record's at position 0**: a standalone one is a local record; any
other is a projection record of a non-empty block of recursors whose family check with a block
below the scope's block is among the scope check's calls, anchored at that block. -/
theorem FamRunCtx.cont_bound
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K)
    {B rb : _root_.Address} {cs : List (Call F)} {z : _root_.Address}
    (hS : K.ScopeAt B rb cs) (hwit : K.ContWitness cs B z) (hTz : K.Top z)
    (hcov : ¬ Covered K.t z) : LocBound rank (K.pot rank z) B 0 := by
  obtain ⟨ib, hdep, hIB, -, -, hkind⟩ := hB.contWitness B rb cs z hS hwit hcov
  obtain ⟨hTi, hiB⟩ := dep_top hW hdep hS.2.1
  rcases hkind with ⟨cz, hcz, hs⟩ | ⟨a, ca, cs', hca, hza, hRB, hFC, hsub⟩
  · exact FamRunCtx.local_bound hW hG hB hS (Or.inr (Or.inl ⟨rfl, hwit, hcov, cz, hcz, hs⟩))
  · obtain ⟨crb, rs, hF⟩ := hB.record ib a ⟨cs', hFC⟩
    have e : crb = ca := Option.some.inj (hF.record.symm.trans hca)
    rw [← e] at hza
    obtain ⟨P, hP, hPp, hPo⟩ := hF.constAddr hza
    obtain ⟨B₀, rb₀, cs₀, hR, hc₀, hsub₀⟩ := hS.2.2.2
    have hSa : K.ScopeAt ib a cs' :=
      ⟨hFC, hTi, hIB, B₀, rb₀, cs₀, hR, hc₀, fun cl h => hsub₀ cl (hsub cl h)⟩
    rw [FamRunCtx.pot_proj hTz hP hPp, hPo, FamRunCtx.pot0_scopeRec hG hB hSa hRB]
    have := transGen_rank_lt hW hiB
    exact Or.inl (by show rank ib + 1 < rank B + 1; omega)

set_option maxRecDepth 100000 in
/-- The basis roles are walked or of the quotient package. -/
theorem basisRoles_walked_or_quot :
    ∀ r ∈ basisRoles, walkedRole r = true ∨ quotRole r = true := by
  decide +kernel

/-- **A witness of a kind other than 2, top-walked and bound to no walked role, has a potential
below the scope's block in the first number**: bound to a role of the quotient package, below
the block, or a constant address of a block below it. -/
theorem FamRunCtx.witBase_bound
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K)
    {B z : _root_.Address} (hTB : K.Top B) (hwb : K.WitBase B z) (hTz : K.Top z)
    (hcov : ¬ Covered K.t z) : (K.pot rank z).1 < rank B + 1 := by
  rcases hwb with ⟨ro, hro, ha⟩ | hc | hdep | ⟨ib, cib, hdep, hcib, hzi⟩
  · rcases basisRoles_walked_or_quot ro hro with hw | hq
    · exact (hcov ⟨ro, ha, hw⟩).elim
    · have hQ : K.QBound z := ⟨hTz, hcov, ro, hq, ha⟩
      obtain ⟨c, hc, hs⟩ := FamRunCtx.QBound.standalone hG hB hQ
      rw [FamRunCtx.pot_nproj (FamRunCtx.not_topProj hc (notProj_of_standalone hs)),
        FamRunCtx.pot0_Q hQ]
      exact Nat.succ_pos _
  · exact absurd hc hcov
  · obtain ⟨-, hzB⟩ := dep_top hW hdep hTB
    exact FamRunCtx.below_bound hW hG hB hTz hzB
  · obtain ⟨hTi, hiB⟩ := dep_top hW hdep hTB
    exact FamRunCtx.constAddr_bound hW hG hB hTi hcib hzi hTz hiB

/-- **A reference of a top-walked block's closure, top-walked and bound to no walked role, has a
potential below the block's in the first number, or one step above the block's** (a constant
address of the block). -/
theorem FamRunCtx.blockRef_bound
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K)
    {A z : _root_.Address} (hTA : K.Top A) (hIA : IndBlock K.E₀ A) (hbr : K.BlockRef A z)
    (hTz : K.Top z) (hcov : ¬ Covered K.t z) :
    (K.pot rank z).1 < rank A + 1 ∨ K.pot rank z = (K.pot0 rank A).bump := by
  rcases hbr with hu | ⟨cA, hcA, hzA⟩ | ⟨q, cq, cD, huq, hcq, hpq, hcD, hzD, hcq'⟩
  · exact Or.inl (FamRunCtx.below_bound hW hG hB hTz (.single ⟨hTA, hTz, Or.inl ⟨hu, hcov⟩⟩))
  · rcases constAddr_cases_top hG hTA hcA hzA with ⟨-, hs⟩ | ⟨P, hP, hPp, hPo⟩
    · obtain ⟨cb, ms, hcb, hms, -, -⟩ := hIA
      rw [hcA] at hcb
      cases hcb
      exact (standalone_not_block hs ⟨ms, hms⟩).elim
    · exact Or.inr (by rw [FamRunCtx.pot_proj hTz hP hPp, hPo])
  · have hncq : ¬ Covered K.t q := fun h => hcov (hcq' h)
    rcases hW.closed A q hTA huq with ⟨hTq, -⟩ | h
    · have hTo := (hW.owner q cq hTq hcq hpq).1
      exact Or.inl (FamRunCtx.constAddr_bound hW hG hB hTo hcD hzD hTz
        (.tail (.single ⟨hTq, hTo, Or.inr ⟨cq, hcq, hpq, rfl⟩⟩) ⟨hTA, hTq, Or.inl ⟨huq, hncq⟩⟩))
    · exact absurd h hncq

/-- A constant address of a checked record is the record itself or holds a projection record of
it (`TopGraph.block_record` for a top-walked record, `innerMembers_of` for an inner one). -/
theorem FamRunCtx.constAddr_cases_walked
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K)
    {D w : _root_.Address} {cD : Ixon.Constant} (hWD : Walked K.Top K.Inner D)
    (hc : recordOf K.E₀ D = some cD) (hw : ConstAddrOf D cD w) :
    (w = D ∧ Standalone cD) ∨
      ∃ P, recordOf K.E₀ w = some P ∧ IsProj P ∧ Ix.Cert.ownerOf w P = D := by
  rcases hWD with hT | hI
  · exact constAddr_cases_top hG hT hc hw
  · rcases hw with h | ⟨ms, i, m, hms, hm, hx⟩
    · exact Or.inl h
    · obtain ⟨hmem, hctor⟩ := FamRunCtx.innerMembers_of hW hB D cD ms hI hc hms i m hm
      rcases hx with hx | ⟨ind, j, hind, hj, hx⟩
      · rw [hx]
        exact Or.inr ⟨_, hmem, memberProjection_isProj D i m, ownerOf_memberProjection _ D i m⟩
      · rw [hx]
        exact Or.inr ⟨_, hctor ind j hind hj, constructorProjection_isProj D i j,
          ownerOf_constructorProjection _ D i j⟩

/-! ### What a record of a scope check, an advice record and a container's recursor use -/

/-- **What a record of a scope check uses** (`familyRefs`), top-walked and bound to no walked
role, is below a record of that scope check in the potential. -/
theorem FamRunCtx.recRef_bound
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K)
    {B rb z : _root_.Address} {cs : List (Call F)} (hS : K.ScopeAt B rb cs)
    (hu : UsedRef K.E₀ rb z) (hTz : K.Top z) (hcov : ¬ Covered K.t z) :
    PotLt (K.pot rank z) (rank B + 1, 1, 0, 2) := by
  rcases hB.familyRefs B rb cs hS z hu with hbr | hwb | hwit
  · rcases FamRunCtx.blockRef_bound hW hG hB hS.2.1 hS.2.2.1 hbr hTz hcov with h | h
    · exact Or.inl h
    · rw [h, FamRunCtx.pot0_scope hG hB hS]
      show PotLt (rank B + 1, 1, 0, 0 + 1) (rank B + 1, 1, 0, 2)
      exact potLt_fourth (by decide)
  · exact Or.inl (FamRunCtx.witBase_bound hW hG hB hS.2.1 hwb hTz hcov)
  · exact (FamRunCtx.cont_bound hW hG hB hS hwit hTz hcov).lt_block 2

/-- **What the `k`-th advice record of a scope check's own list uses** (`adviceRefs`), top-walked
and bound to no walked role, is at most a local record's potential at an earlier position. -/
theorem FamRunCtx.advRef_bound
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K)
    {B rb z : _root_.Address} {cs : List (Call F)} {advAs} {k : Nat} {b}
    (hS : K.ScopeAt B rb cs) (hown : FamilyCallOwn K.calls K.bAddr K.t B rb K.lim cs advAs)
    (hb : advAs[k]? = some b) (hTa : K.Top (Core.ixAddr b))
    (hu : UsedRef K.E₀ (Core.ixAddr b) z) (hTz : K.Top z) (hcov : ¬ Covered K.t z) :
    ∃ q, q < k + 1 ∧ LocBound rank (K.pot rank z) B q := by
  rcases hB.adviceRefs B rb cs advAs hS hown k b hb z hu with
    ⟨j, b', hj, hb', hb'z, hnp⟩ | ⟨j, b', c', hj, hb', hc', hz'⟩ | hwb | hwit
  · -- an earlier listed record: used by a top-walked record, so no block; standalone
    obtain ⟨cz, hcz⟩ := hG.record z hTz
    have hnb : ¬ IsBlock cz := hW.refsNotBlock _ z hTa hu hcov cz hcz
    have hs : Standalone cz := by
      rcases kind_cases cz with h | h | h
      · exact h
      · exact absurd h (hnp cz hcz)
      · exact absurd h hnb
    subst hb'z
    exact ⟨j + 1, by omega, FamRunCtx.local_bound hW hG hB hS
      (Or.inl ⟨advAs, j, b', hown, hb', rfl, rfl, cz, _, hcz, Or.inl ⟨rfl, hs⟩⟩)⟩
  · -- a constant address of an earlier listed record: the record or its projection record
    have hl : K.LocalAt B rb cs (Core.ixAddr b') (j + 1) :=
      Or.inl ⟨advAs, j, b', hown, hb', rfl, rfl, c', z, hc', hz'⟩
    have hb1 := FamRunCtx.local_bound hW hG hB hS hl
    refine ⟨j + 1, by omega, ?_⟩
    rcases FamRunCtx.constAddr_cases_walked hW hG hB
        (FamRunCtx.walked_of_listed hS hown hb' ⟨c', z, hc', hz'⟩) hc' hz' with
      ⟨h, -⟩ | ⟨P, hP, hPp, hPo⟩
    · rw [h]
      exact hb1
    · rw [FamRunCtx.pot_proj hTz hP hPp, hPo]
      rw [FamRunCtx.pot_nproj (FamRunCtx.not_topProj hc' (constAddr_not_proj hz'))] at hb1
      exact hb1.bump
  · exact ⟨0, by omega, Or.inl (FamRunCtx.witBase_bound hW hG hB hS.2.1 hwb hTz hcov)⟩
  · exact ⟨0, by omega, FamRunCtx.cont_bound hW hG hB hS hwit hTz hcov⟩

/-- **What a standalone container's recursor a scope check witnesses uses** (`contWitness`),
top-walked and bound to no walked role, is below the scope's block in the first number: a
reference of the closure of the block its family eliminates (below the scope's block), or a
witness of a kind other than 2. -/
theorem FamRunCtx.contRef_bound
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K)
    {B rb y z : _root_.Address} {cs : List (Call F)} {cy : Ixon.Constant}
    (hS : K.ScopeAt B rb cs) (hwit : K.ContWitness cs B y) (hcy : ¬ Covered K.t y)
    (hcyr : recordOf K.E₀ y = some cy) (hs : Standalone cy) (hu : UsedRef K.E₀ y z)
    (hTz : K.Top z) (hcov : ¬ Covered K.t z) : (K.pot rank z).1 < rank B + 1 := by
  obtain ⟨ib, hdep, hIB, -, hrefs, -⟩ := hB.contWitness B rb cs y hS hwit hcy
  obtain ⟨hTi, hiB⟩ := dep_top hW hdep hS.2.1
  have hr := transGen_rank_lt hW hiB
  rcases hrefs cy hcyr hs z hu with hbr | hwb
  · rcases FamRunCtx.blockRef_bound hW hG hB hTi hIB hbr hTz hcov with h | h
    · omega
    · rw [h, Pot.bump_fst]
      have := FamRunCtx.pot0_fst_le hW hG hB hTi
      omega
  · exact FamRunCtx.witBase_bound hW hG hB hS.2.1 hwb hTz hcov

/-! ### The potential grows along the edges -/

/-- **The potential grows along the walk's steps.** -/
theorem FamRunCtx.walk_pot
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K)
    {z y : _root_.Address} (h : WStep K z y) : PotLt (K.pot rank z) (K.pot rank y) := by
  have hr := h.rank_lt hW
  obtain ⟨hTy, hTz, hstep⟩ := h
  -- a projection record: the step is from its block
  by_cases hp : K.TopProj y
  · obtain ⟨-, c, hc, hpc⟩ := hp
    rcases hstep with ⟨hu, -⟩ | ⟨c', hc', -, rfl⟩
    · exact absurd hu (FamRunCtx.topProj_noUse hW hG hTy hc hpc)
    · rw [hc] at hc'
      cases hc'
      rw [FamRunCtx.pot_proj hTy hc hpc,
        FamRunCtx.pot_nproj (FamRunCtx.owner_notTopProj hW hG hTy hc hpc)]
      exact potLt_bump _
  obtain ⟨hu, hcov⟩ : UsedRef K.E₀ y z ∧ ¬ Covered K.t z := by
    rcases hstep with h | ⟨c, hc, hpc, -⟩
    · exact h
    · exact (hp ⟨hTy, c, hc, hpc⟩).elim
  rw [FamRunCtx.pot_nproj hp]
  -- a quotient-bound record: what it uses is quotient-bound
  by_cases hq : K.QBound y
  · obtain ⟨cy, hcy, hsy⟩ := FamRunCtx.QBound.standalone hG hB hq
    obtain ⟨ro, hro, ha⟩ := hq.2.2
    rcases (hB.quotBound y ro cy hTy hro ha hcy).2 z hu with hc | ⟨ro', hro', ha'⟩
    · exact absurd hc hcov
    · have hqz : K.QBound z := ⟨hTz, hcov, ro', hro', ha'⟩
      obtain ⟨cz, hcz, hsz⟩ := FamRunCtx.QBound.standalone hG hB hqz
      rw [FamRunCtx.pot_nproj (FamRunCtx.not_topProj hcz (notProj_of_standalone hsz)),
        FamRunCtx.pot0_Q hqz, FamRunCtx.pot0_Q hq]
      exact potLt_third hr
  -- a record of a scope check (a block's family record, a twin)
  by_cases hra : K.RecAnch y
  · obtain ⟨B, cs, hS, hRB⟩ := hra
    rw [FamRunCtx.pot0_scopeRec hG hB hS hRB]
    exact FamRunCtx.recRef_bound hW hG hB hS hu hTz hcov
  -- any other record: at its first scope check, or at its own walk rank
  by_cases ha : ∃ p, K.AtMu rank y p
  · rw [FamRunCtx.pot0_at hq hra ha]
    obtain ⟨B, rb, cs, hS, hl, hmu⟩ := FamRunCtx.nu_spec ha
    rw [← hmu]
    rcases hl with ⟨advAs, k, b, hown, hb, hba, hp', -⟩ | ⟨hp', hwit, hcy, cy, hcyr, hs⟩ |
      ⟨-, ⟨B', htw⟩, -⟩
    · subst hba
      obtain ⟨q, hq', hbd⟩ := FamRunCtx.advRef_bound hW hG hB hS hown hb hTy hu hTz hcov
      rw [hp']
      exact hbd.lt_local hq'
    · exact Or.inl (FamRunCtx.contRef_bound hW hG hB hS hwit hcy hcyr hs hu hTz hcov)
    · obtain ⟨cs', hS'⟩ := FamRunCtx.twin_scope htw
      exact (hra ⟨B', cs', hS', (FamRunCtx.twin_facts htw).1⟩).elim
  · rw [FamRunCtx.pot0_own hq hra ha]
    have hmu : K.mu rank y = rank y := by
      rcases FamRunCtx.mu_spec (K := K) (rank := rank) ⟨rank y, Or.inl ⟨hTy, rfl⟩⟩ with
        ⟨-, h⟩ | ⟨B, rb, cs, p, hS, hl, h⟩
      · exact h
      · exact (ha ⟨p, B, rb, cs, hS, hl, h.symm⟩).elim
    rw [hmu]
    have := FamRunCtx.pot_fst_le hW hG hB hTz
    exact Or.inl (by show (K.pot rank z).1 < rank y + 1; omega)

/-- A twin's block is a non-empty block of inductive types. -/
theorem FamRunCtx.twin_block_ind {rb' B : _root_.Address} (h : K.twin rb' = some B) :
    IndBlock K.E₀ B := by
  rcases FamRunCtx.twin_some h with ⟨-, -, -, -, -, -, -, hI⟩ | ⟨-, -, hI, -⟩
  · exact hI
  · exact hI

/-- A local record that is a block is non-empty. -/
theorem FamRunCtx.localAt_pos {B rb : _root_.Address} {cs : List (Call F)}
    {a : _root_.Address} {p : Nat} (h : K.LocalAt B rb cs a p) {c : Ixon.Constant}
    {rs : Array Ixon.MutConst} (hc : recordOf K.E₀ a = some c) (hrs : c.info = .muts rs) :
    0 < rs.size := by
  rcases h with ⟨-, -, -, -, -, -, -, ca, x, hca, hx⟩ | ⟨-, -, -, ca, hca, hs⟩ |
    ⟨-, -, x, ca, -, -, hca, hx⟩
  · rw [hc] at hca
    cases hca
    exact constAddr_muts_pos hrs hx
  · rw [hc] at hca
    cases hca
    exact (standalone_not_block hs ⟨rs, hrs⟩).elim
  · rw [hc] at hca
    cases hca
    exact constAddr_muts_pos hrs hx

theorem indBlock_pos {E₀ : Ixon.Env} {B : _root_.Address} (h : IndBlock E₀ B)
    {c : Ixon.Constant} {rs : Array Ixon.MutConst} (hc : recordOf E₀ B = some c)
    (hrs : c.info = .muts rs) : 0 < rs.size := by
  obtain ⟨cb, ms, hcb, hms, hpos, -⟩ := h
  rw [hc] at hcb
  cases hcb
  rw [hrs] at hms
  cases hms
  exact hpos

/-- **A block with an edge out of it is non-empty**: what the walk steps from is no block or the
block of a projection record; a block with a family record or a twin is a block of inductive
types; a local record or an owner has a constant address. -/
theorem FamRunCtx.out_nonempty
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank)
    {y w : _root_.Address} (h : FamEdge K rank y w) {crb : Ixon.Constant}
    {rs : Array Ixon.MutConst} (hc : recordOf K.E₀ y = some crb) (hrs : crb.info = .muts rs) :
    0 < rs.size := by
  cases h with
  | walk hs =>
    obtain ⟨hTw, hTy, ⟨hu, hcov⟩ | ⟨c, hcw, hp, hy⟩⟩ := hs
    · exact (hW.refsNotBlock w y hTw hu hcov crb hc ⟨rs, hrs⟩).elim
    · obtain ⟨cb, hcb, hx⟩ := hG.projMember w c hTw hcw hp
      rw [← hy, hc] at hcb
      cases hcb
      rw [← hy] at hx
      exact constAddr_muts_pos hrs hx
  | famRec h _ => exact indBlock_pos (FamRunCtx.fam_some h).1.2.2.1 hc hrs
  | twinRec h => exact indBlock_pos (FamRunCtx.twin_block_ind h) hc hrs
  | loc _ hl => exact FamRunCtx.localAt_pos hl hc hrs
  | owner _ _ _ _ _ hown =>
    obtain ⟨c, hc', hx | ⟨rb, crb', hrb, -, -⟩⟩ := hown
    · rw [hc] at hc'
      cases hc'
      exact constAddr_muts_pos hrs hx
    · exact indBlock_pos (FamRunCtx.fam_some hrb).1.2.2.1 hc hrs
  | earlier _ _ _ hl _ _ _ _ _ => exact FamRunCtx.localAt_pos hl hc hrs

/-- An inner record that is no twin is no record of a scope check, no top-walked record and no
quotient-bound record, and is a local record of some scope check. -/
theorem FamRunCtx.inner_plain (hB : BatchGives K) {a : _root_.Address} (hI : K.Inner a)
    (htw : ¬ ∃ B', K.twin a = some B') :
    ¬ K.TopProj a ∧ ¬ K.QBound a ∧ ¬ K.RecAnch a ∧
      ∃ B rb cs p, K.ScopeAt B rb cs ∧ K.LocalAt B rb cs a p := by
  obtain ⟨hTa, ⟨ca, y, hca, hy⟩, ⟨B, rb, cs, hS, hchk⟩ | ⟨B', hN⟩⟩ := hI
  · refine ⟨fun h => hTa h.1, fun h => hTa h.1, ?_, ?_⟩
    · rintro ⟨B'', cs'', hS'', hRB⟩
      rcases hchk with ⟨advAs, hown, b, hbm, hba⟩ | ⟨-, -, -, cx, hcx, hs⟩
      · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hbm
        exact hB.listedNotRec B rb cs advAs k b hS hown hk (by rw [hba]; exact hRB)
      · exact FamRunCtx.not_recAnch_of_standalone hcx hs ⟨B'', cs'', hS'', hRB⟩
    · rcases hchk with ⟨advAs, hown, b, hbm, hba⟩ | ⟨hwit, -, hcov, cx, hcx, hs⟩
      · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hbm
        exact ⟨B, rb, cs, k + 1, hS, Or.inl ⟨advAs, k, b, hown, hk, hba, rfl, ca, y, hca, hy⟩⟩
      · exact ⟨B, rb, cs, 0, hS, Or.inr (Or.inl ⟨rfl, hwit, hcov, cx, hcx, hs⟩)⟩
  · exact absurd (FamRunCtx.nestedTwin_of hN) htw

/-- A block before its checked family record: anchored at the block, one step past the block's
potential in the fourth number; an empty family record has no edge out. -/
theorem FamRunCtx.famRec_pot
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K)
    {B rb : _root_.Address} (h : K.fam B = some rb) :
    PotLt (K.pot rank B) (K.pot rank rb) ∨ ∀ w, ¬ FamEdge K rank rb w := by
  obtain ⟨crb, rs, hF⟩ := hB.record B rb (FamRunCtx.fam_some h).2.1
  by_cases hpos : 0 < rs.size
  · have hRB : RecBlock K.E₀ rb := ⟨crb, rs, hF.record, hF.muts, hpos, hF.recrs⟩
    rw [FamRunCtx.pot_scopeRec hG hB (FamRunCtx.scope_of_fam h) hRB,
      FamRunCtx.pot_scope hG hB (FamRunCtx.scope_of_fam h)]
    exact Or.inl (potLt_fourth (by decide))
  · exact Or.inr fun w hw' => hpos (FamRunCtx.out_nonempty hW hG hw' hF.record hF.muts)

/-- A block before its twin: the twin is anchored at the block. -/
theorem FamRunCtx.twinRec_pot (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K)
    {B rb' : _root_.Address} (h : K.twin rb' = some B) :
    PotLt (K.pot rank B) (K.pot rank rb') := by
  obtain ⟨cs', hS'⟩ := FamRunCtx.twin_scope h
  rw [FamRunCtx.pot_scopeRec hG hB hS' (FamRunCtx.twin_facts h).1,
    FamRunCtx.pot_scope hG hB hS']
  exact potLt_fourth (by decide)

/-- A local record before its scope's block. -/
theorem FamRunCtx.loc_pot
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K)
    {B rb : _root_.Address} {cs : List (Call F)} {a : _root_.Address} {p : Nat}
    (hS : K.ScopeAt B rb cs) (hl : K.LocalAt B rb cs a p) :
    PotLt (K.pot rank a) (K.pot rank B) := by
  rw [FamRunCtx.pot_scope hG hB hS]
  exact (FamRunCtx.local_bound hW hG hB hS hl).lt_block 0

/-- A top-walked owner below the block of every scope check an inner record (no twin) is local to,
before that record. -/
theorem FamRunCtx.owner_pot
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K)
    {D a : _root_.Address} (hI : K.Inner a) (htw : ¬ ∃ B', K.twin a = some B')
    (hT : K.Top D)
    (hall : ∀ B rb cs p, K.ScopeAt B rb cs → K.LocalAt B rb cs a p → rank D < rank B) :
    PotLt (K.pot rank D) (K.pot rank a) := by
  obtain ⟨hnp, hnq, hnr, B, rb, cs, p, hS, hl⟩ := FamRunCtx.inner_plain hB hI htw
  rw [FamRunCtx.pot_nproj hnp]
  rcases FamRunCtx.mu_spec (K := K) (rank := rank)
      ⟨rank B, Or.inr ⟨B, rb, cs, p, hS, hl, rfl⟩⟩ with
    ⟨hTa, -⟩ | ⟨B', rb', cs', p', hS', hl', hmu⟩
  · exact (hI.1 hTa).elim
  · have h1 := hall B' rb' cs' p' hS' hl'
    have h2 := FamRunCtx.pot_fst_le hW hG hB hT
    have h3 := FamRunCtx.pot0_fst (K := K) (rank := rank) hnq hnr
    exact Or.inl (by omega)

/-- A local record of an inner record's first scope check (no twin), at an earlier position,
before that record. -/
theorem FamRunCtx.earlier_pot
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K)
    {B rb : _root_.Address} {cs : List (Call F)} {a₁ a₂ : _root_.Address} {p₁ p₂ : Nat}
    (hI : K.Inner a₂) (htw : ¬ ∃ B', K.twin a₂ = some B') (hS : K.ScopeAt B rb cs)
    (hl₁ : K.LocalAt B rb cs a₁ p₁) (hl₂ : K.LocalAt B rb cs a₂ p₂) (hp : p₁ < p₂)
    (hall : ∀ B' rb' cs' p', K.ScopeAt B' rb' cs' → K.LocalAt B' rb' cs' a₂ p' →
      rank B < rank B' ∨ (rank B = rank B' ∧ p₂ ≤ p')) :
    PotLt (K.pot rank a₁) (K.pot rank a₂) := by
  obtain ⟨hnp, hnq, hnr, -⟩ := FamRunCtx.inner_plain hB hI htw
  rw [FamRunCtx.pot_nproj hnp]
  -- the first scope check attains the least anchor and the least position
  have hmu : K.mu rank a₂ = rank B := by
    have hle := FamRunCtx.mu_le (K := K) (rank := rank)
      (Or.inr ⟨B, rb, cs, p₂, hS, hl₂, rfl⟩ : K.Anchor rank a₂ (rank B))
    rcases FamRunCtx.mu_spec (K := K) (rank := rank)
        ⟨rank B, Or.inr ⟨B, rb, cs, p₂, hS, hl₂, rfl⟩⟩ with
      ⟨hTa, -⟩ | ⟨B', rb', cs', p', hS', hl', hmu⟩
    · exact (hI.1 hTa).elim
    · rcases hall B' rb' cs' p' hS' hl' with h | ⟨h, -⟩ <;> omega
  have hat : K.AtMu rank a₂ p₂ := ⟨B, rb, cs, hS, hl₂, hmu.symm⟩
  have hnu : K.nu rank a₂ = p₂ := by
    have hle := FamRunCtx.nu_le hat
    obtain ⟨B', rb', cs', hS', hl', hrk⟩ := FamRunCtx.nu_spec ⟨p₂, hat⟩
    rcases hall B' rb' cs' _ hS' hl' with h | ⟨-, h⟩ <;> omega
  rw [FamRunCtx.pot0_at hnq hnr ⟨p₂, hat⟩, hmu, hnu]
  exact (FamRunCtx.local_bound hW hG hB hS hl₁).lt_local hp

/-- **The potential grows along every edge into a record with an edge out.** -/
theorem FamRunCtx.edge_pot
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K)
    {z y : _root_.Address} (h : FamEdge K rank z y) :
    PotLt (K.pot rank z) (K.pot rank y) ∨ ∀ w, ¬ FamEdge K rank y w := by
  cases h with
  | walk h => exact Or.inl (FamRunCtx.walk_pot hW hG hB h)
  | famRec h _ => exact FamRunCtx.famRec_pot hW hG hB h
  | twinRec h => exact Or.inl (FamRunCtx.twinRec_pot hG hB h)
  | loc hS hl => exact Or.inl (FamRunCtx.loc_pot hW hG hB hS hl)
  | owner hI htw hT hall _ _ => exact Or.inl (FamRunCtx.owner_pot hW hG hB hI htw hT hall)
  | earlier hI htw hS hl₁ hl₂ hp hall _ _ =>
    exact Or.inl (FamRunCtx.earlier_pot hW hG hB hI htw hS hl₁ hl₂ hp hall)

/-- **The family graph's edges have no cycle**: along a chain into a record with an edge out the
potential grows (`edge_pot`), and every record of a cycle has an edge out. -/
theorem FamRunCtx.famEdge_acyclic
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K) :
    ∀ z, ¬ Relation.TransGen (FamEdge K rank) z z := by
  have key : ∀ a b, Relation.TransGen (FamEdge K rank) a b →
      (∃ w, FamEdge K rank b w) → PotLt (K.pot rank a) (K.pot rank b) := by
    intro a b h
    induction h with
    | single h =>
      rintro ⟨w, hw⟩
      rcases FamRunCtx.edge_pot hW hG hB h with h' | h'
      · exact h'
      · exact (h' w hw).elim
    | tail _ h ih =>
      rintro ⟨w, hw⟩
      have h1 := ih ⟨_, h⟩
      rcases FamRunCtx.edge_pot hW hG hB h with h' | h'
      · exact h1.trans h'
      · exact (h' w hw).elim
  intro z hz
  obtain ⟨w, hw⟩ := transGen_head hz
  exact PotLt.irrefl _ (key z z hz ⟨w, hw⟩)

end Potential

/-! ## The ranking -/

/-- **The ranking, from what the batch's functions give**: at every walk and witness, the edges
`FamEdge` order the family graph (`rankEdges_of`, `famEdge_acyclic`), and the number of the run's
store's addresses below an address is a rank of it (`familyRanked_of_edges`). -/
theorem familyRanking_of (Pref : _root_.Address → _root_.Address → Prop)
    (batch : AtWalk.{u} Pref fun K _ => BatchGives K) : FamilyRanking.{u} Pref := by
  intro calls bAddr t seeds E₀ lim Top rank hW hG R envT hshape
  have hB := batch calls bAddr t seeds E₀ lim Top rank hW hG R envT hshape
  exact ⟨_, familyRanked_of_edges hW
    (rankEdges_of hW hG hB hshape (FamRunCtx.famEdge_acyclic hW hG hB))⟩

/-- **Row `familyGraph` from what the run's functions give**, the ranking proved: the batch's
(`BatchGives`), the facts of unchanged functions not yet proved here (`NoBatchFields`), and the
stored twins' field (to be restated). -/
theorem familyGraphRow_of_batch (Pref : _root_.Address → _root_.Address → Prop)
    (batch : AtWalk.{u} Pref fun K _ => BatchGives K)
    (noBatch : AtWalk.{u} Pref fun K _ => NoBatchFields K)
    (storedTwin : AtWalk.{u} Pref fun K _ => StoredTwinField K) :
    FamilyGraphRow.{u} :=
  familyGraphRow_of_parts Pref batch noBatch (familyRanking_of Pref batch) storedTwin

end IxVM.Refinement.Typing
