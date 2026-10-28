import Ix.Cert.ClosureLayout
import Ix.Cert.ClosureClaims
import Ix.Cert.LayoutRefs

/-! # `Layout.extra`: the edges the fold follows without a reference

`ClosureLayout.Layout.extra` asks that the edges the check order follows from a record of a
closure group's name without a reference lead to records of names of groups: an inductive
block's recursors (`RecursorEdge`) and the ground of a `Nat` operation or a literal
(`GroundEdge`).

**Recursors.** The artifact's recursor index (`artifactRecIndex`, `Ix.Kernel.Reader.buildIndex`)
files a recursor under the block its type's first motive carrier names, and only under a block
record (`buildIndex_muts`). So both records of a name whose block has indexed recursors resolve
to that block (`blockAt_indexed`). The recursors the index files there are published recursors
of that name's family (`RecursorsOwned`, a compile-report check), and the closure takes every
recursor of the family of each of its inductives, constructors and recursors (`DependsOn`,
`family_recursor_sub`). Their names are names of groups (`name_grouped`). -/

namespace Ix.Cert.LayoutExtra

open Ix.LeanIngress (Group)
open Ix.Kernel.Reader (Store RecIndex BlockShape buildIndex)
open Ix.Cert.ClosureLayout

/-! ## The premise: the index's recursors are the family's -/

/-- The first inductive of the family of an input inductive, constructor or recursor: its
`all[0]`, its inductive's, or its `all[0]`'s. -/
def FamilyFirst (env : Ix.Environment) (x first : Ix.Name) : Prop :=
  (∃ iv, env.consts.get? x = some (.inductInfo iv) ∧ iv.all[0]? = some first) ∨
  (∃ cv iv, env.consts.get? x = some (.ctorInfo cv) ∧ env.consts.get? cv.induct = some (.inductInfo iv) ∧
    iv.all[0]? = some first) ∨
  (∃ rv i iv, env.consts.get? x = some (.recInfo rv) ∧ rv.all[0]? = some i ∧
    env.consts.get? i = some (.inductInfo iv) ∧ iv.all[0]? = some first)

/-- **The index's recursors are the family's**: every input name published in a block the
artifact's recursor index files recursors under (at the block or at a projection of it) has a
family, and every recursor the index files there is a published recursor of that family. -/
def RecursorsOwned (env : Ix.Environment) (ixe : Ixon.Env) : Prop :=
  ∀ (a : Address) (shape : BlockShape), (artifactRecIndex ixe).blocks[a]? = some shape →
    ∀ (x : Ix.Name) (p : Address), env.consts.contains x = true → addrOf ixe x = some p → blockAt ixe p = a →
      ∃ first, FamilyFirst env x first ∧ ∀ r ∈ shape.recs, ∃ (rn : Ix.Name) (rv : Ix.RecursorVal),
        env.consts.get? rn = some (.recInfo rv) ∧ rv.all[0]? = some first ∧ r.block ∈ nameRecords ixe rn

/-! ## The index files recursors only under block records -/

/-- `store` holds a block record at `b`. -/
def MutsAt (store : Store) (b : Address) : Prop :=
  ∃ c ms, store b = some c ∧ c.info = .muts ms

/-- The index's state: every block it files, or has found recursors for, is a block record. -/
def Filed (store : Store) (s : RecIndex × Std.HashMap Address (Array (Nat × Ix.Kernel.ConstRef Address))) :
    Prop :=
  ∀ b, (s.1.blocks.contains b = true ∨ s.2.contains b = true) → MutsAt store b

/-- A loop over an array in `Id` and its continuation: an invariant the loop keeps gives what
the continuation concludes. -/
theorem forIn_array_bind {α σ τ : Type} (I : σ → Prop) (P : τ → Prop) {f : α → σ → Id (ForInStep σ)}
    (K : σ → Id τ) (xs : Array α) (step : ∀ x ∈ xs, ∀ s, I s → I (f x s).value)
    (concl : ∀ s, I s → P (Id.run (K s))) (s : σ) (hs : I s) : P (Id.run (forIn xs s f >>= K)) := by
  rw [← Array.forIn_toList]
  exact SourceStoredNames.forIn_id_prop (Q := fun s => P (Id.run (K s))) I xs.toList
    (fun x hx => step x (Array.mem_toList_iff.mp hx)) concl s hs

/-- `forIn_array_bind` over a list. -/
theorem forIn_list_bind {α σ τ : Type} (I : σ → Prop) (P : τ → Prop) {f : α → σ → Id (ForInStep σ)}
    (K : σ → Id τ) (xs : List α) (step : ∀ x ∈ xs, ∀ s, I s → I (f x s).value)
    (concl : ∀ s, I s → P (Id.run (K s))) (s : σ) (hs : I s) : P (Id.run (forIn xs s f >>= K)) :=
  SourceStoredNames.forIn_id_prop (Q := fun s => P (Id.run (K s))) I xs step concl s hs

/-- A block record, from its lookup and its kind. -/
theorem mutsAt_of {store : Store} {b : Address} {c : Ixon.Constant} {ms : Array Ixon.MutConst}
    (h : store b = some c) (hm : c.info = .muts ms) : MutsAt store b :=
  ⟨c, ms, h, hm⟩

/-- A step that files the block record `b` keeps the index's state filed. -/
theorem filed_add {store : Store}
    {s : RecIndex × Std.HashMap Address (Array (Nat × Ix.Kernel.ConstRef Address))} (hs : Filed store s)
    {b : Address} (hb : MutsAt store b) (idx : RecIndex) (v : Array (Nat × Ix.Kernel.ConstRef Address))
    (hidx : ∀ b', idx.blocks.contains b' = true → s.1.blocks.contains b' = true ∨ b' = b) :
    Filed store (idx, s.2.insert b v) := by
  intro b' h
  rcases h with h | h
  · rcases hidx b' h with h | rfl
    · exact hs b' (.inl h)
    · exact hb
  · rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact hb
    · exact hs b' (.inr h)

/-- A loop step that continues with `x`. -/
theorem yield_value {σ : Type} (x : σ) : (pure (ForInStep.yield x) : Id (ForInStep σ)).value = x := rfl

/-- **The index files recursors only under block records.** -/
theorem buildIndex_muts (store : Store) (records : Array (Address × Ixon.Constant)) {a : Address}
    {shape : BlockShape} (h : (buildIndex store records).blocks[a]? = some shape) : MutsAt store a := by
  unfold buildIndex at h
  dsimp only at h
  revert h
  refine forIn_array_bind (Filed store) (fun (idx : RecIndex) => idx.blocks[a]? = some shape → MutsAt store a)
    _ records ?_ ?_ _ ?_
  · intro x _ s hs
    rcases x with ⟨owner, c⟩
    dsimp only
    refine forIn_array_bind (Filed store)
      (fun (st : ForInStep (RecIndex × Std.HashMap Address (Array (Nat × Ix.Kernel.ConstRef Address)))) =>
        Filed store st.value) _ _ ?_ ?_ _ hs
    · intro y _ s hs
      rcases y with ⟨j, r⟩
      dsimp only
      repeat' split
      all_goals simp only [yield_value]
      all_goals first
        | (with_reducible exact hs)
        | (with_reducible refine filed_add hs (mutsAt_of (by assumption) (by assumption)) _ _ (fun b' h => .inl h))
        | (with_reducible refine filed_add hs (mutsAt_of (by assumption) (by assumption)) _ _ (fun b' h => ?_)
           dsimp only at h
           rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq] at h
           rcases h with rfl | h
           · exact .inr rfl
           · exact .inl h)
    · intro s hs
      exact hs
  · intro s hs
    refine forIn_list_bind (fun (idx : RecIndex) => ∀ b, idx.blocks.contains b = true → MutsAt store b)
      (fun (idx : RecIndex) => idx.blocks[a]? = some shape → MutsAt store a) _ _ ?_ ?_ _
      (fun b h => hs b (.inl h))
    · intro x hx idx hidx
      rcases x with ⟨b, rs⟩
      dsimp only
      intro b' h
      have h' : (idx.blocks.insert b _).contains b' = true := h
      rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq] at h'
      rcases h' with rfl | h'
      · refine hs _ (.inr ?_)
        have hmem := (Std.HashMap.mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some.mp hx).2
        rw [Std.HashMap.contains_eq_isSome_getElem?, hmem]
        rfl
      · exact hidx b' h'
    · intro idx hidx hget
      have hget' : idx.blocks[a]? = some shape := hget
      refine hidx a ?_
      rw [Std.HashMap.contains_eq_isSome_getElem?, hget']
      rfl
  · intro b hb
    simp at hb

/-- **A block the index files recursors under is its own block.** -/
theorem blockAt_indexed {ixe : Ixon.Env} {a : Address} {shape : BlockShape}
    (h : (artifactRecIndex ixe).blocks[a]? = some shape) : blockAt ixe a = a := by
  obtain ⟨c, ms, hc, hm⟩ := buildIndex_muts _ _ h
  unfold blockAt
  rw [hc]
  unfold ownerOf
  simp only [hm]

/-! ## Group names and closure names -/

/-- **A group name of quotient Source's graph of an accepted closure is a name the closure
stores a constant under.** -/
theorem groupName_stored {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ)
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint} {i : Nat} {gr : Group}
    (hgr : (quotientGraph ixe t hints sub).groups[i]? = some gr) {n : Ix.Name} (hn : n ∈ gr.names) :
    ∃ ci, (n, ci) ∈ sub.consts.toList := by
  obtain ⟨-, pre, ds, -, hprep, -⟩ := P.source
  have hcol := SourceDeclares.preparedAt_collapsed hprep
  have hg : gr ∈ Ix.LeanIngress.groupsOf sub (blocksOf sub) := Array.mem_of_getElem? hgr
  obtain ⟨c, hc⟩ := SourceStoredNames.prepared_converts hcol gr hg
  obtain ⟨k, ci, hk, hown⟩ := SourceStoredNames.groupsOf_stored sub _ gr hg c hc n hn
  have hname := inputsNamed P.compiled k ci (SourceStoredNames.stored_input P hk)
  rw [hown] at hname
  subst hname
  exact ⟨ci, hk⟩

/-- **A name the closure stores a constant under is a name of a group** of quotient Source's
graph. -/
theorem name_grouped {ixe : Ixon.Env} {t : Ix.Kernel.RoleTable}
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint} {sub : Ix.Environment}
    {n : Ix.Name} {ci : Ix.ConstantInfo} (hn : (n, ci) ∈ sub.consts.toList) :
    ∃ (j : Nat) (gr : Group), (quotientGraph ixe t hints sub).groups[j]? = some gr ∧ n ∈ gr.names := by
  obtain ⟨gr, hg, hng⟩ := SourceDeclares.stored_grouped sub (blocksOf sub) hn
  obtain ⟨j, hj, he⟩ := Array.getElem_of_mem hg
  refine ⟨j, gr, ?_, hng⟩
  show (Ix.LeanIngress.groupsOf sub (blocksOf sub))[j]? = some gr
  rw [← he]
  exact Array.getElem?_eq_getElem hj

/-- Names that hash alike have the same records. -/
theorem nameRecords_congr {ixe : Ixon.Env} {k m : Ix.Name} (h : (k == m) = true) :
    nameRecords ixe k = nameRecords ixe m := by
  unfold nameRecords
  rw [LayoutRefs.addrOf_congr h]

/-- A name the closure holds is stored under a name that hashes like it. -/
theorem stored_key {sub : Ix.Environment} {n : Ix.Name} (h : ClosureClaims.InSub sub n) :
    ∃ k ci, (k, ci) ∈ sub.consts.toList ∧ (n == k) = true := by
  unfold ClosureClaims.InSub at h
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp h
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList] at hci
  obtain ⟨k, hk, hmem⟩ := hci
  exact ⟨k, ci, hmem, hk⟩

/-! ## Recursors -/

/-- The first element of an array is among its elements, by `contains`. -/
theorem contains_head {l : Array Ix.Name} {i : Ix.Name} (h : l[0]? = some i) : l.contains i = true :=
  Array.contains_iff_exists_mem_beq.mpr
    ⟨i, Array.mem_of_getElem? h, show (i.getHash == i.getHash) = true from beq_self_eq_true _⟩

/-- **The closure takes every recursor of the family of each of its inductives, constructors
and recursors.** -/
theorem family_recursor_sub {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    (hcl : IsClosure env roots sub) {x first : Ix.Name} (hx : ClosureClaims.InSub sub x)
    (hfam : FamilyFirst env x first) {rn : Ix.Name} {rv : Ix.RecursorVal}
    (hrn : env.consts.get? rn = some (.recInfo rv)) (hall : rv.all[0]? = some first) :
    ClosureClaims.InSub sub rn := by
  have hrx := ClosureClaims.reaches_of_sub hcl hx
  have key : ∃ i iv, Reaches env roots i ∧ env.consts.get? i = some (.inductInfo iv) ∧
      iv.all[0]? = some first := by
    rcases hfam with ⟨iv, hiv, h0⟩ | ⟨cv, iv, hcv, hiv, h0⟩ | ⟨rv', i, iv, hrv', hi, hiv, h0⟩
    · exact ⟨x, iv, hrx, hiv, h0⟩
    · exact ⟨cv.induct, iv, .step hrx ⟨_, hcv, Or.inl (ClosureClaims.refsOf_ctor cv)⟩, hiv, h0⟩
    · exact ⟨i, iv, .step hrx ⟨_, hrv', Or.inr (Or.inr (show rv'.all.contains i = true from contains_head hi))⟩, hiv, h0⟩
  obtain ⟨i, iv, hri, hiv, h0⟩ := key
  have hr : Reaches env roots rn :=
    .step hri ⟨_, hiv, Or.inr (Or.inr (Or.inr ⟨first, rv, h0, hrn, hall⟩))⟩
  exact ClosureClaims.sub_of_reaches hcl hr (by rw [hrn]; rfl)

/-- **`Layout.extra` for recursor edges**: a recursor the artifact's index files under the block
of a record of a group's name is a record of a name of a group, given that the index's recursors
are the family's (`RecursorsOwned`). -/
theorem recursor_extra {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ) (owned : RecursorsOwned env ixe)
    (hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint) :
    ∀ (i : Nat) (gr : Group), (quotientGraph ixe t hints sub).groups[i]? = some gr → ∀ n ∈ gr.names,
      ∀ a ∈ nameRecords ixe n, ∀ b, RecursorEdge ixe a b →
        ∃ (j : Nat) (gr' : Group), (quotientGraph ixe t hints sub).groups[j]? = some gr' ∧
          ∃ m ∈ gr'.names, b ∈ nameRecords ixe m := by
  rintro i gr hgr n hn a ha b ⟨-, -, shape, hshape, r, hr, hrb⟩
  obtain ⟨ci, hci⟩ := groupName_stored P hgr hn
  cases hA : addrOf ixe n with
  | none =>
    simp only [nameRecords, hA, List.not_mem_nil] at ha
  | some A =>
    have hblk : blockAt ixe A = a := by
      simp only [nameRecords, hA, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact blockAt_indexed hshape
      · rfl
    have hin : env.consts.contains n = true := by
      rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?,
        SourceStoredNames.stored_get (SourceStoredNames.stored_input P hci)]
      rfl
    obtain ⟨first, hfam, hrecs⟩ := owned a shape hshape n A hin hA hblk
    obtain ⟨rn, rv, hrn, hall, hrec⟩ := hrecs r hr
    have hsub : ClosureClaims.InSub sub rn := by
      refine family_recursor_sub P.source.1 ?_ hfam hrn hall
      unfold ClosureClaims.InSub
      rw [SourceStoredNames.stored_get hci]
      rfl
    obtain ⟨k, ck, hk, hkn⟩ := stored_key hsub
    obtain ⟨j, gr', hgr', hkg⟩ := name_grouped (ixe := ixe) (t := t) (hints := hints) hk
    refine ⟨j, gr', hgr', k, hkg, ?_⟩
    rw [← nameRecords_congr hkn, ← hrb]
    exact hrec

end Ix.Cert.LayoutExtra

/--
info: 'Ix.Cert.LayoutExtra.recursor_extra' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Cert.LayoutExtra.recursor_extra
