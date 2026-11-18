import IxVMRefinement.FamilyGraph.ProducersGraph

/-! # The family graph's rank from an acyclic relation over the run's store

`FamilyRanked` asks a rank of strict comparisons: the walk's edges (a used reference and a
projection record's block below the record), advice below its block, a block below its family
record and its twins, and, for what a family record or an inner record uses, an owner below the
block or the record. Any relation `E` that contains these comparisons and has no cycle gives such
a rank: the number of addresses of the run's store strictly below an address in `E`
(`belowCount`), which grows strictly along `E` because the store is finite and a relation without
a cycle never puts an address below itself.

* `belowCount`, `belowCount_lt`: the rank and its strictness along `Relation.TransGen E`;
* `RankEdges`: what a relation must contain and that it has no cycle;
* `familyRanked_of_edges`: `FamilyRanked` at `belowCount E` from `RankEdges` and the walk. -/

universe u

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

set_option linter.unusedVariables false

/-! ## The rank below a relation -/

/-- An address the store holds a record at is one of the store's keys. -/
theorem mem_keys_of_recordOf {E₀ : Ixon.Env} {a : _root_.Address} {c : Ixon.Constant}
    (h : recordOf E₀ a = some c) : a ∈ E₀.consts.keys := by
  rw [Std.HashMap.mem_keys, Std.HashMap.mem_iff_contains, Std.HashMap.contains_eq_isSome_getElem?]
  unfold recordOf at h
  rw [Std.HashMap.get?_eq_getElem?] at h
  cases e : E₀.consts[a]? with
  | none => rw [e] at h; cases h
  | some _ => rfl

theorem transGen_trans {E : _root_.Address → _root_.Address → Prop} {a b c : _root_.Address}
    (h₁ : Relation.TransGen E a b) (h₂ : Relation.TransGen E b c) : Relation.TransGen E a c := by
  induction h₂ with
  | single h => exact .tail h₁ h
  | tail _ h ih => exact .tail ih h

/-- The first step of a chain. -/
theorem transGen_head {E : _root_.Address → _root_.Address → Prop} {a c : _root_.Address}
    (h : Relation.TransGen E a c) : ∃ b, E a b := by
  induction h with
  | single h => exact ⟨_, h⟩
  | tail _ _ ih => exact ih

theorem countP_lt_of_imp {α : Type} {L : List α} {p q : α → Bool}
    (hqp : ∀ x, q x = true → p x = true) {y : α} (hy : y ∈ L) (hp : p y = true)
    (hq : q y = false) : L.countP q < L.countP p := by
  induction L with
  | nil => cases hy
  | cons x L ih =>
    rw [List.countP_cons, List.countP_cons]
    have hle : L.countP q ≤ L.countP p := List.countP_mono_left fun x _ h => hqp x h
    have hx : (if q x = true then 1 else 0) ≤ (if p x = true then 1 else 0) := by
      by_cases h : q x = true
      · simp [h, hqp x h]
      · simp [h]
    rcases List.mem_cons.mp hy with rfl | hy
    · simp [hq, hp]; omega
    · have := ih hy; omega

open Classical in
/-- **The rank of `y` below the relation `E` over the addresses `S`**: how many addresses of `S`
lie strictly below `y` (`Relation.TransGen E`). -/
noncomputable def belowCount (E : _root_.Address → _root_.Address → Prop)
    (S : List _root_.Address) (y : _root_.Address) : Nat :=
  S.countP fun z => decide (Relation.TransGen E z y)

/-- **The rank grows strictly along the relation** at an address of `S` that is not below
itself. -/
theorem belowCount_lt {E : _root_.Address → _root_.Address → Prop} {S : List _root_.Address}
    {z y : _root_.Address} (h : Relation.TransGen E z y) (hz : z ∈ S)
    (hacyc : ¬ Relation.TransGen E z z) : belowCount E S z < belowCount E S y := by
  unfold belowCount
  refine countP_lt_of_imp (y := z) ?_ hz ?_ ?_
  · intro x hx
    simp only [decide_eq_true_eq] at hx ⊢
    exact transGen_trans hx h
  · simpa using h
  · simpa using hacyc

/-! ## A relation that orders the family graph -/

/-- **A relation that orders the family graph at the choices `K`** (module docstring): it has no
cycle, every address below another holds a record of the run's store, and it puts below each other
a top-walked used reference that is not covered and its user (a covered one needs no rank), a
top-walked projection record's block and the record,
an advice record and its block, a block and its family record where that is checked, a block with
a family record and its twin; and what a family record or an inner record uses is stored,
covered, its own (for a family record also its block's), or owned by a checked unclaimed record
below the block or the inner record. -/
structure RankEdges (K : FamRunCtx) (E : _root_.Address → _root_.Address → Prop) : Prop where
  acyclic : ∀ z, ¬ Relation.TransGen E z z
  source : ∀ z y, E z y → ∃ c, recordOf K.E₀ z = some c
  walkUse : ∀ a x, K.Top a → K.Top x → ¬ Covered K.t x → UsedRef K.E₀ a x → E x a
  walkOwner : ∀ a c, K.Top a → recordOf K.E₀ a = some c → IsProj c → E (Ix.Cert.ownerOf a c) a
  after : ∀ B rb, K.fam B = some rb → Walked K.Top K.Inner rb → E B rb
  advBelow : ∀ B a, K.adv B a → E a B
  twinAfter : ∀ rb' B rb, K.twin rb' = some B → K.fam B = some rb → E B rb'
  famClosed : ∀ B rb x, K.fam B = some rb → UsedRef K.E₀ rb x → NeedOk K.E₀ x →
    StoredAt K.t K.envT x ∨ Covered K.t x ∨
      (∃ cb, recordOf K.E₀ B = some cb ∧ ConstAddrOf B cb x) ∨
      (∃ crb, recordOf K.E₀ rb = some crb ∧ ConstAddrOf rb crb x) ∨
      ∃ D, Walked K.Top K.Inner D ∧ Unclaimed K.fam D ∧ FamOwns K.E₀ K.fam D x ∧
        Relation.TransGen E D B
  innerClosed : ∀ a x, K.Inner a → UsedRef K.E₀ a x → NeedOk K.E₀ x →
    StoredAt K.t K.envT x ∨ Covered K.t x ∨
      (∃ c, recordOf K.E₀ a = some c ∧ ConstAddrOf a c x) ∨
      ∃ D, Walked K.Top K.Inner D ∧ Unclaimed K.fam D ∧ FamOwns K.E₀ K.fam D x ∧
        Relation.TransGen E D a

/-- **The rank of the family graph from a relation that orders it**: the number of the run's
store's addresses below an address (`belowCount`). The walk gives that a used reference of a
top-walked record is top-walked or covered and that a projection record's block is top-walked. -/
theorem familyRanked_of_edges {K : FamRunCtx} {E : _root_.Address → _root_.Address → Prop}
    {seeds : List _root_.Address} {rank : _root_.Address → Nat}
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hE : RankEdges K E) : FamilyRanked K (belowCount E K.E₀.consts.keys) := by
  have lt : ∀ {z y}, Relation.TransGen E z y →
      belowCount E K.E₀.consts.keys z < belowCount E K.E₀.consts.keys y := by
    intro z y h
    obtain ⟨b, hb⟩ := transGen_head h
    obtain ⟨c, hc⟩ := hE.source z b hb
    exact belowCount_lt h (mem_keys_of_recordOf hc) (hE.acyclic z)
  have owned : ∀ {x n}, (∃ D, Walked K.Top K.Inner D ∧ Unclaimed K.fam D ∧
      FamOwns K.E₀ K.fam D x ∧ Relation.TransGen E D n) →
      OwnedBelow K.E₀ K.Top K.Inner (belowCount E K.E₀.consts.keys) K.fam
        (belowCount E K.E₀.consts.keys n) x := by
    rintro x n ⟨D, hWD, hU, hown, hD⟩
    exact ⟨D, hWD, hU, lt hD, hown⟩
  refine
    { closed := fun a x hT hu => ?_
      owner := fun a c hT hc hp => ?_
      after := fun B rb h hw => lt (.single (hE.after B rb h hw))
      advBelow := fun B a h => lt (.single (hE.advBelow B a h))
      twinAfter := fun rb' B rb h h' => lt (.single (hE.twinAfter rb' B rb h h'))
      famClosed := fun B rb x h hu hok => ?_
      innerClosed := fun a x h hu hok => ?_ }
  · by_cases hcov : Covered K.t x
    · exact Or.inr hcov
    · rcases hW.closed a x hT hu with ⟨hTx, -⟩ | hcov'
      · exact Or.inl ⟨hTx, lt (.single (hE.walkUse a x hT hTx hcov hu))⟩
      · exact absurd hcov' hcov
  · exact ⟨(hW.owner a c hT hc hp).1, lt (.single (hE.walkOwner a c hT hc hp))⟩
  · rcases hE.famClosed B rb x h hu hok with h1 | h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (owned h1))))
  · rcases hE.innerClosed a x h hu hok with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr (owned h1)))

/-! ## The basis roles are stored -/

set_option maxRecDepth 100000 in
private theorem basisRoles_kept : ∀ r ∈ basisRoles, r ∈ preludeRoles ∨ r ∈ shapeAnchors := by
  decide +kernel

/-- **A witness of kind 0 is stored by a valid table's environment**: the basis roles are
prelude roles (`Nat`, `Eq`, `PUnit` with their constructors and recursors, the quotient package)
or shape anchors (`String`, `Char`), whose constants the table's shape keeps. -/
theorem basis_stored {t : Ix.Kernel.RoleTable} {R : Ixon.Env} {envT : Ix.Kernel.Env .anon}
    (hshape : TableShape.{u} t (fun _ => True) R envT) (htwf : t.wf = true)
    {ro : Ix.Kernel.Role} {x : _root_.Address} (hro : ro ∈ basisRoles)
    (ha : t.addressOf? ro = some x) : StoredAt t envT x := by
  rcases basisRoles_kept ro hro with hp | hs
  · obtain ⟨ci, hfind, -⟩ := hshape.preludeKept (Ix.SpecDigest.groupOf ro) ro x trivial
      (role_mem_roleGroup ro) hp ha
    exact storedAt_of_role htwf ha (Ix.Kernel.Semantics.Env.find?_mem hfind)
      (Ix.Kernel.Semantics.Env.find?_name hfind)
  · obtain ⟨ci, hfind, -⟩ := hshape.kept (Ix.SpecDigest.groupOf ro) ro x trivial
      (role_mem_roleGroup ro) (Or.inl (Or.inr hs)) ha
    exact storedAt_of_role htwf ha (Ix.Kernel.Semantics.Env.find?_mem hfind)
      (Ix.Kernel.Semantics.Env.find?_name hfind)

/-! ## The walk's steps -/

/-- **A step of the walk between top-walked records**: from the record at `z` to a used
reference `y` that is not covered, or from a projection record to its block. -/
def WStep (K : FamRunCtx) (y z : _root_.Address) : Prop :=
  K.Top z ∧ K.Top y ∧
    ((UsedRef K.E₀ z y ∧ ¬ Covered K.t y) ∨
      ∃ c, recordOf K.E₀ z = some c ∧ IsProj c ∧ y = Ix.Cert.ownerOf z c)

section Edges

variable {K : FamRunCtx} {seeds : List _root_.Address} {rank : _root_.Address → Nat}

/-- The walk's rank grows along a step. -/
theorem WStep.rank_lt
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    {y z : _root_.Address} (h : WStep K y z) : rank y < rank z := by
  obtain ⟨hTz, -, ⟨hu, hcov⟩ | ⟨c, hc, hp, rfl⟩⟩ := h
  · rcases hW.closed z y hTz hu with ⟨-, hr⟩ | hc'
    · exact hr
    · exact absurd hc' hcov
  · exact (hW.owner z c hTz hc hp).2

theorem transGen_rank_lt
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    {y z : _root_.Address} (h : Relation.TransGen (WStep K) y z) : rank y < rank z := by
  induction h with
  | single h => exact h.rank_lt hW
  | tail _ h ih => exact Nat.lt_trans ih (h.rank_lt hW)

/-- **A dependency path's step from a top-walked record is a step of the walk.** -/
theorem depStep_wstep
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    {y z : _root_.Address} (hz : K.Top z) (h : K.DepStep y z) : WStep K y z := by
  obtain ⟨-, hcy, hu | ⟨c, hc, hp, rfl⟩⟩ := h
  · rcases hW.closed z y hz hu with ⟨hTy, -⟩ | hcov
    · exact ⟨hz, hTy, Or.inl ⟨hu, hcy⟩⟩
    · exact absurd hcov hcy
  · exact ⟨hz, (hW.owner z c hz hc hp).1, Or.inr ⟨c, hc, hp, rfl⟩⟩

/-- **What a dependency path from a top-walked record reaches is top-walked below it.** -/
theorem dep_top
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    {B x : _root_.Address} (h : K.DepPath B x) :
    K.Top B → K.Top x ∧ Relation.TransGen (WStep K) x B := by
  unfold FamRunCtx.DepPath at h
  induction h with
  | single h =>
    intro hB
    have hs := depStep_wstep hW hB h
    exact ⟨hs.2.1, .single hs⟩
  | tail _ h ih =>
    intro hc
    have hs := depStep_wstep hW hc h
    obtain ⟨hT, ht⟩ := ih hs.2.1
    exact ⟨hT, .tail ht hs⟩

/-! ## Owners below a block -/

/-- **A constant address of a top-walked record is owned by a top-walked unclaimed record at or
below it**: the record itself where no block claims it, else the block that claims it, which the
record (non-empty, having that address) uses a constant address of (`recUsesBlock`). -/
theorem owner_of_constAddr
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K)
    {D' x : _root_.Address} {cD' : Ixon.Constant} (hT : K.Top D')
    (hc : recordOf K.E₀ D' = some cD') (hx : ConstAddrOf D' cD' x) :
    ∃ D, K.Top D ∧ Unclaimed K.fam D ∧ FamOwns K.E₀ K.fam D x ∧
      (D = D' ∨ Relation.TransGen (WStep K) D D') := by
  by_cases hcl : ∃ B'', K.fam B'' = some D'
  · obtain ⟨B'', hB''⟩ := hcl
    obtain ⟨⟨hTB, -, ⟨cb, ms, hcb, hms, hpos, hall⟩, -⟩, hFC, -⟩ := FamRunCtx.fam_some hB''
    have hU : Unclaimed K.fam B'' := fun B₃ h₃ => by
      obtain ⟨crb, rs, hF⟩ := hB.record B₃ B'' (FamRunCtx.fam_some h₃).2.1
      exact hF.not_indBlock ⟨cb, ms, hcb, hms, hpos, hall⟩
    obtain ⟨crb, rs, hF⟩ := hB.record B'' D' hFC
    have e : crb = cD' := Option.some.inj (hF.record.symm.trans hc)
    rw [← e] at hx
    obtain ⟨cb', y, hcb', hy, hcy, huy⟩ := hB.recUsesBlock B'' D' _
      (FamRunCtx.scope_of_fam hB'') crb rs hF.record hF.muts (constAddr_muts_pos hF.muts hx)
    have e' : cb' = cb := Option.some.inj (hcb'.symm.trans hcb)
    rw [e'] at hy
    have hTy : K.Top y := by
      rcases hW.closed D' y hT huy with ⟨h, -⟩ | h
      · exact h
      · exact absurd h hcy
    rcases hy with ⟨-, hs⟩ | ⟨ms', i, m, hms', hm, hyx⟩
    · exact (standalone_not_block hs ⟨ms, hms⟩).elim
    · obtain ⟨P, hP, hPp, hPo⟩ := hG.block_record hTB hcb hms' hm hyx
      refine ⟨B'', hTB, hU, ⟨cb, hcb, Or.inr ⟨D', crb, hB'', hF.record, hx⟩⟩, Or.inr ?_⟩
      exact .tail (.single ⟨hTy, hTB, Or.inr ⟨P, hP, hPp, hPo.symm⟩⟩) ⟨hT, hTy, Or.inl ⟨huy, hcy⟩⟩
  · exact ⟨D', hT, fun B h => hcl ⟨B, h⟩, ⟨cD', hc, Or.inl hx⟩, Or.inl rfl⟩

/-- **A top-walked reference a step has to find is owned by a top-walked unclaimed record at or
below it**: a standalone record itself (or its claimer), a projection record's block (or its
claimer). -/
theorem owner_of_top
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K)
    {x : _root_.Address} (hT : K.Top x) (hok : NeedOk K.E₀ x) :
    ∃ D, K.Top D ∧ Unclaimed K.fam D ∧ FamOwns K.E₀ K.fam D x ∧
      (D = x ∨ Relation.TransGen (WStep K) D x) := by
  obtain ⟨cx, hcx, hnb, -, -⟩ := hok
  rcases kind_cases cx with hs | hp | hb
  · exact owner_of_constAddr hW hG hB hT hcx (Or.inl ⟨rfl, hs⟩)
  · obtain ⟨hTo, -⟩ := hW.owner x cx hT hcx hp
    obtain ⟨cb, hcb, hxo⟩ := hG.projMember x cx hT hcx hp
    obtain ⟨D, hTD, hU, hown, hrel⟩ := owner_of_constAddr hW hG hB hTo hcb hxo
    have hs : WStep K (Ix.Cert.ownerOf x cx) x := ⟨hT, hTo, Or.inr ⟨cx, hcx, hp, rfl⟩⟩
    refine ⟨D, hTD, hU, hown, Or.inr ?_⟩
    rcases hrel with rfl | ht
    · exact .single hs
    · exact .tail ht hs
  · exact absurd hb hnb

/-- A top-walked reference below `B` is owned below `B`. -/
theorem owned_of_top_below
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K)
    {x B : _root_.Address} (hT : K.Top x) (hok : NeedOk K.E₀ x)
    (hxB : Relation.TransGen (WStep K) x B) :
    ∃ D, K.Top D ∧ Unclaimed K.fam D ∧ FamOwns K.E₀ K.fam D x ∧
      Relation.TransGen (WStep K) D B := by
  obtain ⟨D, hTD, hU, hown, hrel⟩ := owner_of_top hW hG hB hT hok
  refine ⟨D, hTD, hU, hown, ?_⟩
  rcases hrel with rfl | ht
  · exact hxB
  · exact transGen_trans ht hxB

/-- A constant address of a top-walked record below `B` is owned below `B`. -/
theorem owned_of_block_below
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K)
    {D' x B : _root_.Address} {cD' : Ixon.Constant} (hT : K.Top D')
    (hc : recordOf K.E₀ D' = some cD') (hx : ConstAddrOf D' cD' x)
    (hDB : Relation.TransGen (WStep K) D' B) :
    ∃ D, K.Top D ∧ Unclaimed K.fam D ∧ FamOwns K.E₀ K.fam D x ∧
      Relation.TransGen (WStep K) D B := by
  obtain ⟨D, hTD, hU, hown, hrel⟩ := owner_of_constAddr hW hG hB hT hc hx
  refine ⟨D, hTD, hU, hown, ?_⟩
  rcases hrel with rfl | ht
  · exact hDB
  · exact transGen_trans ht hDB

/-- **What lies below a top-walked block is stored, covered, or owned below it**: a used
reference of the block, a type or constructor of a block one of its used references projects
from, a witness of a kind other than 2. -/
theorem below_owned
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K) {R : Ixon.Env}
    (hshape : TableShape.{u} K.t (fun _ => True) R K.envT)
    {B x : _root_.Address} (hTB : K.Top B) (hok : NeedOk K.E₀ x)
    (h : UsedRef K.E₀ B x ∨ K.ProjOfRef B x ∨ K.WitBase B x) :
    StoredAt K.t K.envT x ∨ Covered K.t x ∨
      ∃ D, K.Top D ∧ Unclaimed K.fam D ∧ FamOwns K.E₀ K.fam D x ∧
        Relation.TransGen (WStep K) D B := by
  have htwf : K.t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [hW.check_ok]
    rfl
  by_cases hcov : Covered K.t x
  · exact Or.inr (Or.inl hcov)
  rcases h with hu | ⟨q, cq, cD, huq, hcq, hpq, hcD, hxD, hcq'⟩ |
    (⟨ro, hro, ha⟩ | hc | hdep | ⟨ib, cib, hdep, hcib, hxi⟩)
  · rcases hW.closed B x hTB hu with ⟨hTx, -⟩ | hc
    · exact Or.inr (Or.inr (owned_of_top_below hW hG hB hTx hok
        (.single ⟨hTB, hTx, Or.inl ⟨hu, hcov⟩⟩)))
    · exact absurd hc hcov
  · have hncq : ¬ Covered K.t q := fun h => hcov (hcq' h)
    rcases hW.closed B q hTB huq with ⟨hTq, -⟩ | h
    · have hTo := (hW.owner q cq hTq hcq hpq).1
      exact Or.inr (Or.inr (owned_of_block_below hW hG hB hTo hcD hxD
        (.tail (.single ⟨hTq, hTo, Or.inr ⟨cq, hcq, hpq, rfl⟩⟩) ⟨hTB, hTq, Or.inl ⟨huq, hncq⟩⟩)))
    · exact absurd h hncq
  · exact Or.inl (basis_stored hshape htwf hro ha)
  · exact absurd hc hcov
  · obtain ⟨hTx, hxB⟩ := dep_top hW hdep hTB
    exact Or.inr (Or.inr (owned_of_top_below hW hG hB hTx hok hxB))
  · obtain ⟨hTi, hiB⟩ := dep_top hW hdep hTB
    exact Or.inr (Or.inr (owned_of_block_below hW hG hB hTi hcib hxi hiB))

/-- **A container's recursor a scope check witnesses is stored, covered, owned below the
scope's block, or owned by a local record of the scope check at position 0**: a standalone one is
itself such a local record; any other is a constant address of a non-empty block of recursors
whose family check is among the scope check's calls, so that block is the family record of the
block it eliminates (below the scope's block), or a twin of it. -/
theorem cont_owned
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hB : BatchGives K) {B rb : _root_.Address} {cs : List (Call F)} {x : _root_.Address}
    (hS : K.ScopeAt B rb cs) (hwit : K.ContWitness cs B x) :
    StoredAt K.t K.envT x ∨ Covered K.t x ∨
      (∃ D, K.Top D ∧ Unclaimed K.fam D ∧ FamOwns K.E₀ K.fam D x ∧
        Relation.TransGen (WStep K) D B) ∨
      ∃ D, K.LocalAt B rb cs D 0 ∧ Walked K.Top K.Inner D ∧ Unclaimed K.fam D ∧
        FamOwns K.E₀ K.fam D x := by
  by_cases hcov : Covered K.t x
  · exact Or.inr (Or.inl hcov)
  by_cases hst : StoredAt K.t K.envT x
  · exact Or.inl hst
  obtain ⟨ib, hdep, hIB, -, -, hkind⟩ := hB.contWitness B rb cs x hS hwit hcov
  obtain ⟨hTi, hiB⟩ := dep_top hW hdep hS.2.1
  refine Or.inr (Or.inr ?_)
  rcases hkind with ⟨cx, hcx, hs⟩ | ⟨a, ca, cs', hca, hxa, hRB, hFC, hsub⟩
  · -- a standalone container's recursor: a local record of the scope check
    have hxx : ConstAddrOf x cx x := Or.inl ⟨rfl, hs⟩
    refine Or.inr ⟨x, Or.inr (Or.inl ⟨rfl, hwit, hcov, cx, hcx, hs⟩), ?_, ?_,
      ⟨cx, hcx, Or.inl hxx⟩⟩
    · by_cases hT : K.Top x
      · exact Or.inl hT
      · exact Or.inr ⟨hT, ⟨cx, x, hcx, hxx⟩, Or.inl ⟨B, rb, cs, hS,
          Or.inr ⟨hwit, ⟨cx, x, hcx, hxx, hst⟩, hcov, cx, hcx, hs⟩⟩⟩
    · intro B' h
      obtain ⟨crb, rs, hF⟩ := hB.record B' x (FamRunCtx.fam_some h).2.1
      have e : crb = cx := Option.some.inj (hF.record.symm.trans hcx)
      have hm : cx.info = .muts rs := by
        rw [← e]
        exact hF.muts
      exact standalone_not_block hs ⟨rs, hm⟩
  · have hFCa : K.FamCheck ib a := ⟨cs', hFC⟩
    have hUn : K.Unstored a := ⟨ca, x, hca, hxa, hst⟩
    by_cases hcl : ∃ B₂, K.fam B₂ = some a
    · -- the record is the family record of the eliminated block, below the scope's block
      obtain ⟨B₂, hB₂⟩ := hcl
      have e : B₂ = ib := FamRunCtx.block_unique hB hRB (FamRunCtx.fam_some hB₂).2.1 hFCa
      rw [e] at hB₂
      obtain ⟨cib, ms, hcib, hms, hpos, hall⟩ := hIB
      refine Or.inl ⟨ib, hTi, fun B₃ h₃ => ?_, ⟨cib, hcib, Or.inr ⟨a, ca, hB₂, hca, hxa⟩⟩, hiB⟩
      obtain ⟨crb, rs, hF⟩ := hB.record B₃ ib (FamRunCtx.fam_some h₃).2.1
      exact hF.not_indBlock ⟨cib, ms, hcib, hms, hpos, hall⟩
    · -- an unclaimed record: a twin of the eliminated block, top-walked or nested
      have hU : Unclaimed K.fam a := fun B₂ h => hcl ⟨B₂, h⟩
      have htw : ∃ B', K.twin a = some B' := by
        by_cases hTa : K.Top a
        · obtain ⟨B₃, hFC3, hT3, hM3, hI3⟩ := hB.recArm a hTa hRB
          have e : B₃ = ib := FamRunCtx.block_unique hB hRB hFC3 hFCa
          rw [e] at hM3
          exact FamRunCtx.twin_of ⟨hTa, hRB, hUn, hU, hFCa, hTi, hM3, hIB⟩
        · obtain ⟨B₀, rb₀, cs₀, hR, hc₀, hsub₀⟩ := hS.2.2.2
          exact FamRunCtx.nestedTwin_of ⟨⟨hTa, hRB, hUn, hU⟩, hTi, hIB, B₀, rb₀, hR, cs₀, hc₀,
            cs', hFC, fun cl h => hsub₀ cl (hsub cl h)⟩
      refine Or.inr ⟨a, Or.inr (Or.inr ⟨rfl, htw, x, ca, hwit, hcov, hca, hxa⟩), ?_, hU,
        ⟨ca, hca, Or.inl hxa⟩⟩
      by_cases hTa : K.Top a
      · exact Or.inl hTa
      · obtain ⟨B', h'⟩ := htw
        exact Or.inr (FamRunCtx.inner_of_twin h' hTa)

/-- **What the record of a scope check uses** (`familyRefs`) is stored, covered, a constant
address of the scope's block, owned below the block, or owned by a local record of the scope
check. -/
theorem scope_owned
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K) {R : Ixon.Env}
    (hshape : TableShape.{u} K.t (fun _ => True) R K.envT)
    {B rb : _root_.Address} {cs : List (Call F)} {x : _root_.Address}
    (hS : K.ScopeAt B rb cs) (hu : UsedRef K.E₀ rb x) (hok : NeedOk K.E₀ x) :
    StoredAt K.t K.envT x ∨ Covered K.t x ∨
      (∃ cB, recordOf K.E₀ B = some cB ∧ ConstAddrOf B cB x) ∨
      (∃ D, K.Top D ∧ Unclaimed K.fam D ∧ FamOwns K.E₀ K.fam D x ∧
        Relation.TransGen (WStep K) D B) ∨
      ∃ D p, K.LocalAt B rb cs D p ∧ Walked K.Top K.Inner D ∧ Unclaimed K.fam D ∧
        FamOwns K.E₀ K.fam D x := by
  have lift : (StoredAt K.t K.envT x ∨ Covered K.t x ∨
      ∃ D, K.Top D ∧ Unclaimed K.fam D ∧ FamOwns K.E₀ K.fam D x ∧
        Relation.TransGen (WStep K) D B) →
      StoredAt K.t K.envT x ∨ Covered K.t x ∨
        (∃ cB, recordOf K.E₀ B = some cB ∧ ConstAddrOf B cB x) ∨
        (∃ D, K.Top D ∧ Unclaimed K.fam D ∧ FamOwns K.E₀ K.fam D x ∧
          Relation.TransGen (WStep K) D B) ∨
        ∃ D p, K.LocalAt B rb cs D p ∧ Walked K.Top K.Inner D ∧ Unclaimed K.fam D ∧
          FamOwns K.E₀ K.fam D x := by
    rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  rcases hB.familyRefs B rb cs hS x hu with (hub | hown | hproj) | hwb | hwit
  · exact lift (below_owned hW hG hB hshape hS.2.1 hok (Or.inl hub))
  · exact Or.inr (Or.inr (Or.inl hown))
  · exact lift (below_owned hW hG hB hshape hS.2.1 hok (Or.inr (Or.inl hproj)))
  · exact lift (below_owned hW hG hB hshape hS.2.1 hok (Or.inr (Or.inr hwb)))
  · rcases cont_owned hW hB hS hwit with h | h | h | ⟨D, hl, hw, hU, hown⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨D, 0, hl, hw, hU, hown⟩)))

/-! ## The edges -/

/-- **The edges of the family graph's order** at the walk's rank `rank`: the walk's steps; a
block before its family record (where checked) and before its twins; a local record of a scope
check before the scope's block; an inner record after a top-walked owner of what it uses that lies
below the block of every scope check the record is local to; and an inner record after a local
record of its first scope check (least block rank, then least position) at an earlier position,
whose constant address it uses. -/
inductive FamEdge (K : FamRunCtx) (rank : _root_.Address → Nat) :
    _root_.Address → _root_.Address → Prop
  | walk {y z : _root_.Address} : WStep K y z → FamEdge K rank y z
  | famRec {B rb : _root_.Address} : K.fam B = some rb → Walked K.Top K.Inner rb →
      FamEdge K rank B rb
  | twinRec {B rb' : _root_.Address} : K.twin rb' = some B → FamEdge K rank B rb'
  | loc {B rb : _root_.Address} {cs : List (Call F)} {a : _root_.Address} {p : Nat} :
      K.ScopeAt B rb cs → K.LocalAt B rb cs a p → FamEdge K rank a B
  | owner {D a x : _root_.Address} : K.Inner a → K.Top D →
      (∀ B rb cs p, K.ScopeAt B rb cs → K.LocalAt B rb cs a p → rank D < rank B) →
      UsedRef K.E₀ a x → FamOwns K.E₀ K.fam D x → FamEdge K rank D a
  | earlier {B rb : _root_.Address} {cs : List (Call F)} {a₁ a₂ x : _root_.Address}
      {p₁ p₂ : Nat} : K.Inner a₂ → K.ScopeAt B rb cs → K.LocalAt B rb cs a₁ p₁ →
      K.LocalAt B rb cs a₂ p₂ → p₁ < p₂ →
      (∀ B' rb' cs' p', K.ScopeAt B' rb' cs' → K.LocalAt B' rb' cs' a₂ p' →
        rank B < rank B' ∨ (rank B = rank B' ∧ p₂ ≤ p')) →
      UsedRef K.E₀ a₂ x → FamOwns K.E₀ K.fam a₁ x → FamEdge K rank a₁ a₂

theorem walk_transGen {y z : _root_.Address} (h : Relation.TransGen (WStep K) y z) :
    Relation.TransGen (FamEdge K rank) y z := by
  induction h with
  | single h => exact .single (.walk h)
  | tail _ h ih => exact .tail ih (.walk h)

/-- A twin's block is top-walked. -/
theorem FamRunCtx.twin_block_top {rb' B : _root_.Address} (h : K.twin rb' = some B) :
    K.Top B := by
  rcases FamRunCtx.twin_some h with ⟨-, -, -, -, -, hT, -⟩ | ⟨-, hT, -⟩
  · exact hT
  · exact hT

/-- A local record is a record of the run's store. -/
theorem FamRunCtx.localAt_record {B rb : _root_.Address} {cs : List (Call F)}
    {a : _root_.Address} {p : Nat} (h : K.LocalAt B rb cs a p) :
    ∃ c, recordOf K.E₀ a = some c := by
  rcases h with ⟨-, -, -, -, -, -, -, ca, -, hca, -⟩ | ⟨-, -, -, ca, hca, -⟩ |
    ⟨-, -, -, ca, -, -, hca, -⟩
  · exact ⟨ca, hca⟩
  · exact ⟨ca, hca⟩
  · exact ⟨ca, hca⟩

/-- **The least pair**, lexicographically, of a non-empty set of pairs of numbers. -/
theorem lex_min {P : Nat → Nat → Prop} (h : ∃ n p, P n p) :
    ∃ n p, P n p ∧ ∀ n' p', P n' p' → n < n' ∨ (n = n' ∧ p ≤ p') := by
  classical
  have hn : ∃ p, P (Nat.find h) p := Nat.find_spec h
  refine ⟨Nat.find h, Nat.find hn, Nat.find_spec hn, fun n' p' hp' => ?_⟩
  have hle : Nat.find h ≤ n' := Nat.find_min' h ⟨p', hp'⟩
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · exact Or.inl hlt
  · refine Or.inr ⟨heq, ?_⟩
    rw [← heq] at hp'
    exact Nat.find_min' hn hp'

/-- A listed advice record with a constant address is top-walked or inner. -/
theorem FamRunCtx.walked_of_listed {B rb : _root_.Address} {cs : List (Call F)} {advAs}
    {j : Nat} {b} (hS : K.ScopeAt B rb cs)
    (hown : FamilyCallOwn K.calls K.bAddr K.t B rb K.lim cs advAs) (hb : advAs[j]? = some b)
    (hconst : ∃ ca y, recordOf K.E₀ (Core.ixAddr b) = some ca ∧ ConstAddrOf (Core.ixAddr b) ca y) :
    Walked K.Top K.Inner (Core.ixAddr b) := by
  by_cases hT : K.Top (Core.ixAddr b)
  · exact Or.inl hT
  · exact Or.inr ⟨hT, hconst, Or.inl ⟨B, rb, cs, hS,
      Or.inl ⟨advAs, hown, b, List.mem_of_getElem? hb, rfl⟩⟩⟩

/-- **What an inner record uses** is stored, covered, its own, or owned by a checked unclaimed
record below it in the edges: a nested twin through the scope check of its own family check (its
block before it); any other inner record through its first scope check (least block rank, then
least position), by `adviceRefs` or `contWitness`. -/
theorem innerClosed_of
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K) {R : Ixon.Env}
    (hshape : TableShape.{u} K.t (fun _ => True) R K.envT)
    {a x : _root_.Address} (hI : K.Inner a) (hu : UsedRef K.E₀ a x) (hok : NeedOk K.E₀ x) :
    StoredAt K.t K.envT x ∨ Covered K.t x ∨
      (∃ c, recordOf K.E₀ a = some c ∧ ConstAddrOf a c x) ∨
      ∃ D, Walked K.Top K.Inner D ∧ Unclaimed K.fam D ∧ FamOwns K.E₀ K.fam D x ∧
        Relation.TransGen (FamEdge K rank) D a := by
  by_cases htw : ∃ B', K.twin a = some B'
  · -- a nested twin: through the scope check of its own family check, then its block
    obtain ⟨B', htw⟩ := htw
    rcases FamRunCtx.twin_some htw with hto | ⟨-, hTB', hIB', B₀, rb₀, hR, cs₀, hc₀, cs', hc',
      hsub⟩
    · exact absurd hto.1 hI.1
    have hS : K.ScopeAt B' a cs' := ⟨hc', hTB', hIB', B₀, rb₀, cs₀, hR, hc₀, hsub⟩
    have hE : FamEdge K rank B' a := .twinRec htw
    rcases scope_owned hW hG hB hshape hS hu hok with h1 | h1 | ⟨cB, hcB, hxB⟩ |
      ⟨D, hTD, hU, hown, hD⟩ | ⟨D, p, hl, hw, hU, hown⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · obtain ⟨cb, ms, hcb, hms, hpos, hall⟩ := hIB'
      refine Or.inr (Or.inr (Or.inr ⟨B', Or.inl hTB', fun B₃ h₃ => ?_,
        ⟨cB, hcB, Or.inl hxB⟩, .single hE⟩))
      obtain ⟨crb, rs, hF⟩ := hB.record B₃ B' (FamRunCtx.fam_some h₃).2.1
      exact hF.not_indBlock ⟨cb, ms, hcb, hms, hpos, hall⟩
    · exact Or.inr (Or.inr (Or.inr ⟨D, Or.inl hTD, hU, hown, .tail (walk_transGen hD) hE⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨D, hw, hU, hown, .tail (.single (.loc hS hl)) hE⟩))
  · -- a local record of a scope check: at its first scope check
    have hloc : ∃ n p, ∃ B rb cs, K.ScopeAt B rb cs ∧ K.LocalAt B rb cs a p ∧ rank B = n := by
      obtain ⟨hTa, ⟨ca, y, hca, hy⟩, ⟨B, rb, cs, hS, hchk⟩ | ⟨B', hN⟩⟩ := hI
      · rcases hchk with ⟨advAs, hown, b, hb, hba⟩ | ⟨hwit, -, hcov, cx, hcx, hs⟩
        · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hb
          exact ⟨rank B, k + 1, B, rb, cs, hS,
            Or.inl ⟨advAs, k, b, hown, hk, hba, rfl, ca, y, hca, hy⟩, rfl⟩
        · exact ⟨rank B, 0, B, rb, cs, hS, Or.inr (Or.inl ⟨rfl, hwit, hcov, cx, hcx, hs⟩), rfl⟩
      · exact absurd (FamRunCtx.nestedTwin_of hN) htw
    obtain ⟨n, p, ⟨B, rb, cs, hS, hl, hn⟩, hmin⟩ := lex_min hloc
    have hall : ∀ B' rb' cs' p', K.ScopeAt B' rb' cs' → K.LocalAt B' rb' cs' a p' →
        rank B < rank B' ∨ (rank B = rank B' ∧ p ≤ p') := by
      intro B' rb' cs' p' hS' hl'
      rw [hn]
      exact hmin (rank B') p' ⟨B', rb', cs', hS', hl', rfl⟩
    have hle : ∀ B' rb' cs' p', K.ScopeAt B' rb' cs' → K.LocalAt B' rb' cs' a p' →
        rank B ≤ rank B' := by
      intro B' rb' cs' p' hS' hl'
      rcases hall B' rb' cs' p' hS' hl' with h | ⟨h, -⟩ <;> omega
    -- a top-walked owner below the scope's block: the owner edge
    have viaOwner : ∀ T, (T = B ∨ Relation.TransGen (WStep K) T B) →
        (StoredAt K.t K.envT x ∨ Covered K.t x ∨
          ∃ D, K.Top D ∧ Unclaimed K.fam D ∧ FamOwns K.E₀ K.fam D x ∧
            Relation.TransGen (WStep K) D T) →
        StoredAt K.t K.envT x ∨ Covered K.t x ∨
          (∃ c, recordOf K.E₀ a = some c ∧ ConstAddrOf a c x) ∨
          ∃ D, Walked K.Top K.Inner D ∧ Unclaimed K.fam D ∧ FamOwns K.E₀ K.fam D x ∧
            Relation.TransGen (FamEdge K rank) D a := by
      intro T hTB h
      rcases h with h | h | ⟨D, hTD, hU, hown, hD⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · have hDB : Relation.TransGen (WStep K) D B := by
          rcases hTB with rfl | hT
          · exact hD
          · exact transGen_trans hD hT
        have hr : rank D < rank B := transGen_rank_lt hW hDB
        exact Or.inr (Or.inr (Or.inr ⟨D, Or.inl hTD, hU, hown, .single (.owner hI hTD
          (fun B' rb' cs' p' hS' hl' => Nat.lt_of_lt_of_le hr (hle B' rb' cs' p' hS' hl'))
          hu hown)⟩))
    -- a local record of the scope check at an earlier position: the earlier edge
    have viaEarlier : ∀ D q, K.LocalAt B rb cs D q → q < p → Walked K.Top K.Inner D →
        Unclaimed K.fam D → FamOwns K.E₀ K.fam D x →
        StoredAt K.t K.envT x ∨ Covered K.t x ∨
          (∃ c, recordOf K.E₀ a = some c ∧ ConstAddrOf a c x) ∨
          ∃ D, Walked K.Top K.Inner D ∧ Unclaimed K.fam D ∧ FamOwns K.E₀ K.fam D x ∧
            Relation.TransGen (FamEdge K rank) D a := by
      intro D q hlD hq hw hU hown
      exact Or.inr (Or.inr (Or.inr ⟨D, hw, hU, hown,
        .single (.earlier hI hS hlD hl hq hall hu hown)⟩))
    rcases hl with ⟨advAs, k, b, hown, hb, hba, hp, -⟩ | ⟨hp, hwit, hcov, cx, hcx, hs⟩ |
      ⟨-, htw', -⟩
    · -- a listed advice record: `adviceRefs`
      have hu' : UsedRef K.E₀ (Core.ixAddr b) x := by
        rw [hba]
        exact hu
      rcases hB.adviceRefs B rb cs advAs hS hown k b hb x hu' with
        ⟨j, b', hj, hb', hb'x, hnp⟩ | ⟨j, b', c', hj, hb', hc', hx'⟩ | hwb | hwit
      · obtain ⟨cx, hcx, hnb, -, -⟩ := hok
        have hs : Standalone cx := by
          rcases kind_cases cx with h | h | h
          · exact h
          · exact absurd h (hnp cx hcx)
          · exact absurd h hnb
        subst hb'x
        have hxx : ConstAddrOf (Core.ixAddr b') cx (Core.ixAddr b') := Or.inl ⟨rfl, hs⟩
        exact viaEarlier _ (j + 1)
          (Or.inl ⟨advAs, j, b', hown, hb', rfl, rfl, cx, _, hcx, hxx⟩) (by omega)
          (FamRunCtx.walked_of_listed hS hown hb' ⟨cx, _, hcx, hxx⟩)
          (hB.listedUnclaimed B rb cs advAs j b' hS hown hb' ⟨cx, _, hcx, hxx⟩)
          ⟨cx, hcx, Or.inl hxx⟩
      · exact viaEarlier _ (j + 1)
          (Or.inl ⟨advAs, j, b', hown, hb', rfl, rfl, c', x, hc', hx'⟩) (by omega)
          (FamRunCtx.walked_of_listed hS hown hb' ⟨c', x, hc', hx'⟩)
          (hB.listedUnclaimed B rb cs advAs j b' hS hown hb' ⟨c', x, hc', hx'⟩)
          ⟨c', hc', Or.inl hx'⟩
      · exact viaOwner B (Or.inl rfl)
          (below_owned hW hG hB hshape hS.2.1 hok (Or.inr (Or.inr hwb)))
      · rcases cont_owned hW hB hS hwit with h | h | h | ⟨D, hlD, hw, hU, hown⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact viaOwner B (Or.inl rfl) (Or.inr (Or.inr h))
        · exact viaEarlier D 0 hlD (by omega) hw hU hown
    · -- a standalone container's recursor: `contWitness`
      obtain ⟨ib, hdep, -, -, hrefs, -⟩ := hB.contWitness B rb cs a hS hwit hcov
      obtain ⟨hTi, hiB⟩ := dep_top hW hdep hS.2.1
      rcases hrefs cx hcx hs x hu with (hub | ⟨cib, hcib, hxi⟩ | hproj) | hwb
      · exact viaOwner ib (Or.inr hiB) (below_owned hW hG hB hshape hTi hok (Or.inl hub))
      · obtain ⟨D, hTD, hU, hown, hrel⟩ := owner_of_constAddr hW hG hB hTi hcib hxi
        refine viaOwner B (Or.inl rfl) (Or.inr (Or.inr ⟨D, hTD, hU, hown, ?_⟩))
        rcases hrel with rfl | ht
        · exact hiB
        · exact transGen_trans ht hiB
      · exact viaOwner ib (Or.inr hiB)
          (below_owned hW hG hB hshape hTi hok (Or.inr (Or.inl hproj)))
      · exact viaOwner B (Or.inl rfl)
          (below_owned hW hG hB hshape hS.2.1 hok (Or.inr (Or.inr hwb)))
    · exact absurd htw' htw

/-- **The edges order the family graph, up to acyclicity** (`RankEdges` from its `acyclic`
field): the walk's steps are edges; a block precedes its checked family record and its twins;
advice precedes its block (a local record of the block's family check); what a family record
uses is owned below its block (`scope_owned`); what an inner record uses is owned below it
(`innerClosed_of`). -/
theorem rankEdges_of
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : BatchGives K) {R : Ixon.Env}
    (hshape : TableShape.{u} K.t (fun _ => True) R K.envT)
    (hacyc : ∀ z, ¬ Relation.TransGen (FamEdge K rank) z z) :
    RankEdges K (FamEdge K rank) where
  acyclic := hacyc
  source := fun z y h => by
    cases h with
    | walk h => exact hG.record z h.2.1
    | famRec h _ => exact hG.record z (FamRunCtx.fam_some h).1.1
    | twinRec h => exact hG.record z (FamRunCtx.twin_block_top h)
    | loc _ hl => exact FamRunCtx.localAt_record hl
    | owner _ hT _ _ _ => exact hG.record z hT
    | earlier _ _ hl _ _ _ _ _ => exact FamRunCtx.localAt_record hl
  walkUse := fun a x hTa hTx hcov hu => .walk ⟨hTa, hTx, Or.inl ⟨hu, hcov⟩⟩
  walkOwner := fun a c hTa hc hp =>
    .walk ⟨hTa, (hW.owner a c hTa hc hp).1, Or.inr ⟨c, hc, hp, rfl⟩⟩
  after := fun B rb h hw => .famRec h hw
  advBelow := fun B a h => by
    obtain ⟨rb, hrb, ⟨b, hb, hba⟩, ca, x, hca, hx⟩ := h
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hb
    exact .loc (FamRunCtx.scope_of_fam hrb) (Or.inl ⟨K.ownList B rb, k, b,
      FamRunCtx.ownList_spec (hB.ownWalk B rb (FamRunCtx.fam_some hrb).2.1), hk, hba, rfl,
      ca, x, hca, hx⟩)
  twinAfter := fun rb' B rb h _ => .twinRec h
  famClosed := fun B rb x h hu hok => by
    rcases scope_owned hW hG hB hshape (FamRunCtx.scope_of_fam h) hu hok with
      h1 | h1 | h1 | ⟨D, hTD, hU, hown, hD⟩ | ⟨D, p, hl, hw, hU, hown⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨D, Or.inl hTD, hU, hown, walk_transGen hD⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨D, hw, hU, hown,
        .single (.loc (FamRunCtx.scope_of_fam h) hl)⟩)))
  innerClosed := fun a x h hu hok => innerClosed_of hW hG hB hshape h hu hok

end Edges

end IxVM.Refinement.Typing
