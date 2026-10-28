import Ix.Cert.ClosureLayout
import Ix.Cert.ClosureClaims
import Ix.Cert.LayoutRefs
import Ix.Cert.SourceTotality
import Ix.Cert.DefinitionPremises
import Ix.Cert.SourceOrigin
import Ix.Cert.CtxAgree
import Ix.Cert.BlockLayout
import Ix.Cert.BlockWire

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
`family_recursor_sub`). Their names are names of groups (`name_grouped`).

**Ground.** A `Nat` operation's record is a standalone definition (`RoleRecordKinds`, a
compile-report check), so a ground edge starts at a group name's own published record
(`block_role`). That name has the operation's key (`quotientKey_role`), quotient Source declares
the key by a definition (`OpsDeclared`), and the definition's install guard found every ground
role installed (`op_deps_installed`). The fold installs only names its stream declares besides
the prelude's (`installed_over`), the stream declares a role key only for a closure name with
that key (`stream_role`), and that name is published at the role's address (`role_published`).

**Kinds.** A closure name published at a standalone definition record of kind `defn` is an
input definition (`claimed_definition`), since a lone constant's compile makes such a block only
of a definition (`lone_defn`) and a mutual block only of a single member its members' loop made
of an input definition (`compileMutualBlock_defn`, `members_defn`). A name with `sorryAx`'s key
sits at the role's axiom record (`not_sorryAx`). -/

namespace Ix.Cert.LayoutExtra

open Ix.LeanIngress (Graph Group FiberMap Converted graphCollapsed scheduleOf lower)
open Ix.Kernel.Reader (State Read)
open Ix.Cert.SourcePrelude (Scheduled)
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


/-! ## Ground edges: the premises -/

/-- **The stored record at a bound role's address has its specification's kind**, under the
default table: at a `Nat` operation's address (an `ops` specification) a standalone definition,
at an axiom role's address an axiom. Every other role, and an address the artifact stores
nothing at, is unconstrained. -/
def RoleRecordKinds (ixe : Ixon.Env) : Prop :=
  ∀ t, Ix.Kernel.Reader.defaultTable = .ok t →
    ∀ (r : Ix.Kernel.Role) (p : Address) (c : Ixon.Constant),
      t.addressOf? r = some p → (ixe.consts.get? p).bind (·.get?) = some c →
        ((Ix.Kernel.Role.spec (md := .anon) r).kind = .ops →
            ∃ d : Ixon.Definition, c.info = .defn d ∧ d.kind = .defn) ∧
        ((Ix.Kernel.Role.spec (md := .anon) r).kind = .axiom → ∃ ax : Ixon.Axiom, c.info = .axio ax)

/-- **A stream declares a `Nat` operation's role only by a definition**: every declaration
that names the key of a role with an `ops` specification is a definition. -/
def OpsDeclared (ds : List (Ix.Kernel.Declaration .source)) : Prop :=
  ∀ d ∈ ds, ∀ r : Ix.Kernel.Role, (Ix.Kernel.Role.spec (md := .anon) r).kind = .ops →
    (Ix.Kernel.Key.role r : Ix.Kernel.Key .source) ∈ d.names →
      ∃ cv value hint, d = .defnDecl cv value hint

/-! ## Ground edges: the roles -/

/-- A `Nat` operation's ground: the operation is one, its specification is an `ops` one, the
ground role's key is among its dependencies, and the ground role is not the prelude's. -/
theorem groundRoles_op {r : Ix.Kernel.Role} :
    ∀ s ∈ groundRoles r,
      ((Ix.Kernel.natOpNames : List (Ix.Kernel.Key .source)).contains (.role r) = true ∨
        (Ix.Kernel.natDivModNames : List (Ix.Kernel.Key .source)).contains (.role r) = true) ∧
      (Ix.Kernel.Role.spec (md := .anon) r).kind = .ops ∧
      (Ix.Kernel.Key.role s : Ix.Kernel.Key .source) ∈ Ix.Kernel.natOpDeps (.role r) ∧
      s ∉ Ix.Kernel.preludeRoles ∧ s ∉ Ix.Kernel.preludeShape.flatten := by
  cases r <;> decide

/-! ## Ground edges: the table rule -/

open Ix.LeanIngress (sourceAddrs fiberMembers repAt roleAtMap) in
/-- **A name published at the address the table binds a role to has that role's key.** -/
theorem quotientKey_role {ixe : Ixon.Env} {t : Ix.Kernel.RoleTable} (checked : t.check = .ok ())
    (bound : PublishedRolesBound t ixe) (agree : PublishedAgree ixe) {n : Ix.Name} {named : Ixon.Named}
    (hn : (n, named) ∈ ixe.named.toList) {r : Ix.Kernel.Role} (hr : t.addressOf? r = some named.addr) :
    quotientKey ixe t n = .role r := by
  have tb := tableBound_of checked bound
  have ha := agree n named hn
  have hne : (fiberMembers (sourceAddrs ixe)).getD named.addr [] ≠ [] := by
    intro h
    have := Ix.LeanIngress.mem_fiberMembers.mpr ha
    rw [h] at this
    cases this
  obtain ⟨rep, hrep⟩ := Ix.LeanIngress.repAt_isSome (bound := (roleAtMap t)[named.addr]?) hne
    fun x hx r hxr => tb x r named.addr (Ix.LeanIngress.mem_fiberMembers.mp hx) hxr
  have hroles : (roleAtMap t)[named.addr]? = some r := (Ix.LeanIngress.roleAtMap_spec checked).mpr hr
  have hrep' := hrep
  rw [hroles] at hrep'
  simp only [repAt] at hrep'
  split at hrep'
  · cases hrep'
    unfold quotientKey Ix.LeanIngress.ingressKey
    exact Ix.LeanIngress.fiberAliasAt_subst ha hrep
  · cases hrep'

/-- **A name with a role's key is published at the address the table binds the role to.** -/
theorem role_published {ixe : Ixon.Env} {t : Ix.Kernel.RoleTable} (checked : t.check = .ok ())
    (bound : PublishedRolesBound t ixe) (agree : PublishedAgree ixe) {m : Ix.Name} {named : Ixon.Named}
    (hm : (m, named) ∈ ixe.named.toList) {s : Ix.Kernel.Role} (hk : quotientKey ixe t m = .role s) :
    t.addressOf? s = some named.addr := by
  have h := ReadingKeys.keyAddress_quotientKey checked bound agree hm
  rw [hk] at h
  exact h

/-! ## Ground edges: what the fold installs -/

/-- **A reference accept installs only names over its declarations' names**, or the prelude's
roles. -/
theorem installed_over {md : Ix.Kernel.Mode} {μ : Ix.Kernel.CheckMode} {ev : Ix.Kernel.Evidences md}
    {ds : List (Ix.Kernel.Declaration md)} {env : Ix.Kernel.Env md}
    (h : Ix.Kernel.Cached.AcceptsRef μ ev ds env) {c : Ix.Kernel.ConstantInfo md} (hc : c ∈ env.consts) :
    Ix.Kernel.Over (ds.flatMap Ix.Kernel.Declaration.names) c.name := by
  obtain ⟨F, h⟩ := h
  obtain ⟨new, hnew, hall, -⟩ :=
    Ix.Kernel.foldlM_checkDecl_post μ (Ix.Kernel.fueledOps μ F) ev ds Ix.Kernel.Env.empty env h
  rw [hnew] at hc
  rcases List.mem_append.mp hc with hc | hc
  · exact (hall c hc).1
  · exact absurd hc List.not_mem_nil

/-- **An accepted `Nat` operation's dependencies are installed**: its install guard
(`natOpGuard` with `natOpStoredOk`, or `divModEnvGuard`) found each stored as a definition. -/
theorem op_deps_installed {μ : Ix.Kernel.CheckMode} {ev : Ix.Kernel.Evidences .source}
    {ds : List (Ix.Kernel.Declaration .source)} {env : Ix.Kernel.Env .source}
    (h : Ix.Kernel.Cached.AcceptsRef μ ev ds env) {cv : Ix.Kernel.ConstantVal .source}
    {value : Ix.Kernel.Expr .source} {hint : Ix.Kernel.ReducibilityHint}
    (hd : Ix.Kernel.Declaration.defnDecl cv value hint ∈ ds)
    (hop : (Ix.Kernel.natOpNames : List (Ix.Kernel.Key .source)).contains cv.name = true ∨
      (Ix.Kernel.natDivModNames : List (Ix.Kernel.Key .source)).contains cv.name = true) :
    ∀ k ∈ Ix.Kernel.natOpDeps cv.name, ∃ c ∈ env.consts, c.name = k := by
  obtain ⟨F, h⟩ := h
  obtain ⟨e₀, e₁, step, keep⟩ :=
    SourceInstalls.foldlM_steps (mode := μ) (ops := Ix.Kernel.fueledOps μ F) ev ds _ _ h _ hd
  obtain ⟨type', value', -, -, -, hnat, hdm⟩ := Ix.Kernel.Semantics.checkDeclRun_ofEnvFactsE step
  have stored : (Ix.Kernel.natOpDeps cv.name).all (Ix.Kernel.natOpStoredOk e₁) = true := by
    rcases hop with hop | hop
    · exact (hnat hop).2.1
    · have g := (hdm hop).1
      simp only [Ix.Kernel.divModEnvGuard, Bool.and_eq_true] at g
      exact g.1.1.1.2
  intro k hk
  have hok := List.all_eq_true.mp stored k hk
  unfold Ix.Kernel.natOpStoredOk at hok
  split at hok
  · rename_i hfind
    unfold Ix.Kernel.Env.find? at hfind
    have hmem := List.mem_of_find?_eq_some hfind
    have hname := List.find?_some hfind
    exact ⟨_, keep _ hmem, beq_iff_eq.mp hname⟩
  · cases hok

/-! ## Ground edges: the stream's keys -/

/-- A key that is not derived is its own base. -/
theorem base_of_not_aux {md : Ix.Kernel.Mode} {k : Ix.Kernel.Key md} (h : k.isAux = false) : k.base = k := by
  cases k <;> simp_all [Ix.Kernel.Key.base, Ix.Kernel.Key.isAux]

/-- An ordinary lowering generates nothing. -/
theorem lower_generated_zero {st : State .source} {c : Converted} {r : Read .source}
    (h : lower st c = .ok r) (hc : ∀ rb, c ≠ .inductive rb) : r.generated = 0 := by
  cases c with
  | «inductive» rb => exact absurd rfl (hc rb)
  | definitions ms =>
    unfold lower at h
    delta Ix.LeanIngress.lower.match_6 at h
    dsimp only at h
    split at h
    · rename_i hsz
      obtain ⟨l⟩ := ms
      obtain _ | ⟨m, _ | ⟨_, _⟩⟩ := l
      · cases hsz
      · obtain ⟨_, _, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
        cases h; rfl
      · simp at hsz
    · obtain ⟨_, _, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
      cases h; rfl
  | «axiom» cv => cases h; rfl
  | quot kind cv => cases h; rfl

/-- The modeller's block's names are the block's own. -/
theorem blockRec_names {rb : Ix.Kernel.Reader.BlockRead .source} {y : Ix.Kernel.Key .source}
    (hy : y ∈ (CtxAgree.blockRecOf rb).types.map (·.cv.name) ++ (CtxAgree.blockRecOf rb).ctors.map (·.cv.name) ++
      (CtxAgree.blockRecOf rb).recs.map (·.cv.name)) :
    (∃ e ∈ rb.types, y = e.1.name) ∨ (∃ e ∈ rb.ctors, y = e.1.name) ∨ ∃ e ∈ rb.recs, y = e.1.name := by
  simp only [CtxAgree.blockRecOf, List.map_map, List.mem_append, List.mem_map, Function.comp_def] at hy
  rcases hy with (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩
  · exact .inl ⟨e.1, Array.mem_def.mpr (List.of_mem_zip he).1, rfl⟩
  · exact .inr (.inl ⟨e, Array.mem_def.mpr he, rfl⟩)
  · exact .inr (.inr ⟨e, Array.mem_def.mpr he, rfl⟩)

/-- **A scheduled group's lowering declares only keys over its names' quotient keys**, derived
ones included (the generator roots every name it emits at a block name). -/
theorem lowered_bases {ρ : FiberMap} {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Environment} {blocks : Ix.CondensedBlocks} {x : Scheduled} {conv : Converted}
    (hx : x ∈ (scheduleOf (graphCollapsed ρ hints env blocks)).zipIdx.toList) (hc : x.1.2 = .ok conv)
    {st : State .source} {raw : Read .source} (hl : lower st conv = .ok raw) :
    ∀ d ∈ raw.decls.toList, ∀ k ∈ d.names,
      ∃ n₀ ∈ namesAt (graphCollapsed ρ hints env blocks) x, k.base = (qkey ρ n₀).base := by
  obtain ⟨gr, c, hgr, hconv, heq⟩ := scheduled_conversion hx hc
  have hnames : namesAt (graphCollapsed ρ hints env blocks) x = gr.names := by
    unfold namesAt; rw [getElem!_of_getElem? hgr]
  rw [hnames]
  have hK : ReaderUnits.ConvertedKeys (fun k => ∃ n₀ ∈ gr.names, k = qkey ρ n₀) conv := by
    refine convertedKeys_of_mem fun k hk => ?_
    rw [heq] at hk
    obtain ⟨k', hk', rfl⟩ := convKeys_quotient_inv hk
    rw [SourceDeclares.convKeys_withHints hints] at hk'
    obtain ⟨n, hn, rfl⟩ := convertedKeys_mem (ReaderUnits.convert_keys hconv) k' hk'
    exact ⟨n, hn, rfl⟩
  have direct : ∀ k, (∃ n₀ ∈ gr.names, k = qkey ρ n₀) → ∃ n₀ ∈ gr.names, k.base = (qkey ρ n₀).base := by
    rintro k ⟨n₀, hn₀, rfl⟩
    exact ⟨n₀, hn₀, rfl⟩
  intro d hd k hk
  cases conv with
  | «inductive» rb =>
    obtain ⟨tk, ck, rk⟩ := hK
    have hli : Ix.Kernel.Reader.lowerInductive st rb = .ok raw := hl
    obtain ⟨gens, hdecls, -, -, hgen⟩ := CtxAgree.lowerInductive_ok hli
    obtain ⟨gens₂, d₂, hd₂, -, hn₂⟩ := ReaderUnits.lowerInductive_decls hli
    have hlist : raw.decls.toList = gens ++ [CtxAgree.indDeclOf rb] := by
      rw [hdecls]
      simp
    rw [hlist] at hd₂
    obtain ⟨-, hlast⟩ := List.append_inj' hd₂ rfl
    have hd₂eq : d₂ = CtxAgree.indDeclOf rb := (List.singleton_inj.mp hlast).symm
    have nameK : ∀ y, ((∃ e ∈ rb.types, y = e.1.name) ∨ (∃ e ∈ rb.ctors, y = e.1.name) ∨
        ∃ e ∈ rb.recs, y = e.1.name) → ∃ n₀ ∈ gr.names, y = qkey ρ n₀ := by
      rintro y (⟨e, he, hy⟩ | ⟨e, he, hy⟩ | ⟨e, he, hy⟩)
      · rw [hy]; exact tk e he
      · rw [hy]; exact ck e he
      · rw [hy]; exact rk e he
    rw [hlist] at hd
    rcases List.mem_append.mp hd with hd | hd
    · rcases hgen with ⟨-, hgen⟩ | ⟨-, rfl⟩
      · have hb := SourceOrigin.generate_bases hgen d hd k hk
        unfold SourceOrigin.roots at hb
        obtain ⟨y, hy, hyb⟩ := List.mem_map.mp hb
        obtain ⟨n₀, hn₀, rfl⟩ := nameK y (blockRec_names hy)
        exact ⟨n₀, hn₀, hyb.symm⟩
      · cases hd
    · rw [List.mem_singleton] at hd
      subst hd
      rw [← hd₂eq, hn₂] at hk
      simp only [List.mem_append, List.mem_map] at hk
      refine direct k (nameK k ?_)
      rcases hk with (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩
      · exact .inl ⟨e, Array.mem_def.mpr he, rfl⟩
      · exact .inr (.inl ⟨e, Array.mem_def.mpr he, rfl⟩)
      · exact .inr (.inr ⟨e, Array.mem_def.mpr he, rfl⟩)
  | definitions ms =>
    rcases ReaderUnits.lower_lowering hK hl with ⟨-, hall⟩ | ⟨gens, d0, hdecls, hgl, hk0⟩
    · exact direct k (hall d hd k hk)
    · rw [lower_generated_zero hl (fun rb h => by cases h)] at hgl
      rw [List.eq_nil_of_length_eq_zero hgl.symm, List.nil_append] at hdecls
      rw [hdecls, List.mem_singleton] at hd
      subst hd
      exact direct k (hk0 k hk)
  | «axiom» cv =>
    rcases ReaderUnits.lower_lowering hK hl with ⟨-, hall⟩ | ⟨gens, d0, hdecls, hgl, hk0⟩
    · exact direct k (hall d hd k hk)
    · rw [lower_generated_zero hl (fun rb h => by cases h)] at hgl
      rw [List.eq_nil_of_length_eq_zero hgl.symm, List.nil_append] at hdecls
      rw [hdecls, List.mem_singleton] at hd
      subst hd
      exact direct k (hk0 k hk)
  | quot kind cv =>
    rcases ReaderUnits.lower_lowering hK hl with ⟨-, hall⟩ | ⟨gens, d0, hdecls, hgl, hk0⟩
    · exact direct k (hall d hd k hk)
    · rw [lower_generated_zero hl (fun rb h => by cases h)] at hgl
      rw [List.eq_nil_of_length_eq_zero hgl.symm, List.nil_append] at hdecls
      rw [hdecls, List.mem_singleton] at hd
      subst hd
      exact direct k (hk0 k hk)

/-- **Every read a trace keeps is part of a scheduled item's lowering.** -/
theorem trace_reads {g : Graph} {start st : State .source} {xs : List Scheduled} {rs : List (Read .source)}
    {s : Ix.LeanIngress.CollapseState} {kb : Ix.LeanIngress.KeptBlocks}
    (h : SourcePrelude.Trace g start xs rs st s kb) :
    ∀ r ∈ rs, ∃ x ∈ xs, ∃ conv st' raw, x.1.2 = .ok conv ∧ lower st' conv = .ok raw ∧
      ∀ d ∈ r.decls.toList, d ∈ raw.decls.toList := by
  induction h with
  | nil => intro r hr; cases hr
  | «alias» _ _ ih =>
    intro r hr
    obtain ⟨x, hx, rest⟩ := ih r hr
    exact ⟨x, List.mem_append_left _ hx, rest⟩
  | lowered _ hc hl hr _ ih =>
    intro r' hr'
    rcases List.mem_append.mp hr' with hr' | hr'
    · obtain ⟨x, hx, rest⟩ := ih r' hr'
      exact ⟨x, List.mem_append_left _ hx, rest⟩
    · rw [List.mem_singleton] at hr'
      subst hr'
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), _, _, _, hc, hl,
        (SourcePrelude.collapseRead_facts hr).2.2.2.1⟩

/-- **Quotient Source's stream declares a role key only for a closure name with that key**, or
in its prelude. -/
theorem stream_role {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ) {pre : Ix.Kernel.Reader.Prelude .source}
    {ds : Array (Ix.Kernel.Declaration .source)} (hpre : Ix.Kernel.Reader.builtinPrelude = .ok pre)
    (hprep : Ix.LeanIngress.prepareSourceCollapsedAt ixe t ((Ix.LeanIngress.fiberHintsMap ixe)[·]?) pre sub
      (blocksOf sub) = .ok ds)
    {d : Ix.Kernel.Declaration .source} (hd : d ∈ ds.toList) {k : Ix.Kernel.Key .source} (hk : k ∈ d.names)
    {s : Ix.Kernel.Role} (hs : k.base = .role s) (notPre : s ∉ Ix.Kernel.preludeShape.flatten) :
    ∃ m ci, (m, ci) ∈ sub.consts.toList ∧ quotientKey ixe t m = .role s := by
  have hcol := SourceDeclares.preparedAt_collapsed hprep
  obtain ⟨fin, decls, hl, -, hds⟩ := Ix.LeanIngress.prepareSourceCollapsed_keepsPrelude hcol
  obtain ⟨extra, hextra, perm⟩ := Ix.Kernel.Frontend.preparePrelude_perm pre.ix decls
  rw [hds] at hd
  rcases List.mem_append.mp (perm.mem_iff.mp hd) with hd | hd
  · obtain ⟨rs, s', kb, ht, -, -, hdecls⟩ := SourcePrelude.lowerAllCollapsed_trace hl
    rw [hdecls] at hd
    obtain ⟨r, hr, hdr⟩ := List.mem_flatMap.mp hd
    obtain ⟨x, hx, conv, st', raw, hc, hlow, hsub⟩ := trace_reads ht r hr
    obtain ⟨n₀, hn₀, hbase⟩ := lowered_bases hx hc hlow d (hsub d hdr) k hk
    obtain ⟨gr, c, hgr, -, -⟩ := scheduled_conversion hx hc
    have hnames : namesAt (quotientGraph ixe t ((Ix.LeanIngress.fiberHintsMap ixe)[·]?) sub) x = gr.names := by
      unfold namesAt; rw [getElem!_of_getElem? hgr]
    rw [hnames] at hn₀
    obtain ⟨ci, hci⟩ := groupName_stored P hgr hn₀
    refine ⟨n₀, ci, hci, ?_⟩
    rw [hs, base_of_not_aux (qkey_not_aux n₀)] at hbase
    exact hbase.symm
  · have hp := hextra d hd
    have shape := SourceInstalls.builtinPrelude_shape hpre
    have hm : d.names ∈ pre.ix.decls.toList.map (·.names) := List.mem_map.mpr ⟨d, hp, rfl⟩
    rw [shape] at hm
    obtain ⟨rs, hrs, hnr⟩ := List.mem_map.mp hm
    rw [← hnr] at hk
    obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hk
    have same : s' = s := by simpa [Ix.Kernel.Key.base] using hs
    subst same
    exact absurd (List.mem_flatten.mpr ⟨rs, hrs, hs'⟩) notPre

/-! ## Ground edges: a block with a projection row is a block record -/

section Rows

open Ix.CompileM Ix.CompileCert
open Ix.Cert.BlockRecords (Returns)

/-- **A block whose rows include a projection is a block record** (`muts`). -/
def RowsMuts (r : BlockResult) : Prop :=
  ∀ p ∈ r.projections, p.2.1 ≠ r.block → ∃ ms, r.block.info = .muts ms

theorem finishConstant_rows (info : Ixon.ConstantInfo) (blockMeta : Ixon.ConstantMeta) :
    Returns RowsMuts (finishConstantInfoWithSharing info blockMeta) := by
  intro ctx s x s' ran
  unfold finishConstantInfoWithSharing finishConstantWithSharing at ran
  obtain ⟨cache, mid, -, ran⟩ := bind_ok ran
  obtain ⟨block, mid', hb, ran⟩ := bind_ok ran
  rw [rawRun_pure] at ran
  cases ran
  intro p hp
  simp [BlockResult.mk'] at hp

theorem finishInductive_rows (i : Ix.InductiveVal) (ind : Ixon.Inductive) (indMeta : Ixon.ConstantMeta)
    (pairs : Array (Ix.Name × Ixon.ConstantMeta)) :
    Returns RowsMuts (finishInductiveFamilyBlock i ind indMeta pairs) := by
  intro ctx s x s' ran
  unfold finishInductiveFamilyBlock at ran
  obtain ⟨_, _, -, ran⟩ := bind_ok ran
  obtain ⟨_, _, -, ran⟩ := bind_ok ran
  obtain ⟨cache, mid, -, ran⟩ := bind_ok ran
  obtain ⟨block, mid', hb, ran⟩ := bind_ok ran
  rw [rawRun_pure] at ran
  cases ran
  intro _ _ _
  obtain ⟨targets, h, -⟩ :=
    ProjectionLayout.sharing_mutual_shape _ _ _ _ _ (BlockLayout.buildBlockConstant_ok hb)
  exact ⟨targets, h⟩

theorem buildMutual_rows {limits : Ix.Sharing.Exact.Limits} {classes : List (List MutConst)}
    {payloads : Array Ixon.MutConst} {metas : Array (Ix.Name × Ixon.ConstantMeta)} {cache : BlockState}
    {out : BlockResult} (ran : buildCompiledMutualBlock limits classes payloads metas cache = .ok out) :
    RowsMuts out := by
  unfold buildCompiledMutualBlock at ran
  cases hs : standaloneMutConstInfo? payloads with
  | some info =>
    rw [hs] at ran
    obtain ⟨block, hb, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases Except.ok.inj returned
    intro p hp hne
    exfalso
    apply hne
    have logical : (p.1, p.2.1) ∈ MutualProjections.logicalRows
        (buildStandaloneMutualProjections classes block metas) :=
      List.mem_map.mpr ⟨p, Array.mem_toList_iff.mpr hp, rfl⟩
    rw [MutualProjections.standalone_rows] at logical
    obtain ⟨_, _, e⟩ := List.mem_map.mp logical
    exact (Prod.mk.inj e).2.symm
  | none =>
    rw [hs] at ran
    obtain ⟨block, hb, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases Except.ok.inj returned
    intro _ _ _
    obtain ⟨targets, h, -⟩ := ProjectionLayout.sharing_mutual_shape _ _ _ _ _ hb
    exact ⟨targets, h⟩

theorem compileMutualBlock_rows (classes : List (List MutConst)) :
    Returns RowsMuts (compileMutualBlock classes) := by
  intro ctx s x s' ran
  unfold compileMutualBlock at ran
  dsimp only at ran
  unfold withMutCtx at ran
  rw [rawRun_withBlockEnv] at ran
  obtain ⟨_, _, -, compiled⟩ := bind_ok ran
  unfold compileMutualPayload at compiled
  obtain ⟨_, _, -, finished⟩ := bind_ok compiled
  exact buildMutual_rows (ProjectionLayout.finish_mutual_ok _ _ _ _ finished).2.2

theorem defnBlock_rows (d : Ix.Def) : Returns RowsMuts (compileDefinitionDataInfo d) := by
  unfold compileDefinitionDataInfo compileDefinitionDataBlock
  exact BlockRecords.Returns.bind fun _ => BlockRecords.Returns.bind fun _ => finishConstant_rows _ _

theorem inductiveInfo_rows (v : Ix.InductiveVal) : Returns RowsMuts (compileInductiveInfo v) := by
  unfold compileInductiveInfo
  refine BlockRecords.Returns.bind fun _ => BlockLayout.Returns.withBlockEnv ?_
  unfold compileInductiveFamilyInfo compileInductiveFamilyBlock
  exact BlockRecords.Returns.bind fun _ => BlockRecords.Returns.bind fun _ => finishInductive_rows _ _ _ _

theorem compileConstantInfo_rows (const : Ix.ConstantInfo) :
    Returns RowsMuts (compileConstantInfo const) := by
  cases const with
  | defnInfo v =>
    unfold compileConstantInfo compileDefinitionConstantInfo withMutCtx
    refine BlockLayout.Returns.withBlockEnv ?_
    unfold compileDefinitionInfo compileDefinitionBlock
    exact BlockRecords.Returns.bind fun _ => BlockRecords.Returns.bind fun _ => finishConstant_rows _ _
  | thmInfo v =>
    unfold compileConstantInfo compileTheoremConstantInfo withMutCtx
    exact BlockLayout.Returns.withBlockEnv (defnBlock_rows _)
  | opaqueInfo v =>
    unfold compileConstantInfo compileOpaqueConstantInfo withMutCtx
    exact BlockLayout.Returns.withBlockEnv (defnBlock_rows _)
  | quotInfo v =>
    unfold compileConstantInfo compileQuotientConstantInfo withMutCtx
    refine BlockLayout.Returns.withBlockEnv ?_
    unfold compileQuotientInfo compileQuotientBlock
    exact BlockRecords.Returns.bind fun _ => BlockRecords.Returns.bind fun _ => finishConstant_rows _ _
  | recInfo v =>
    unfold compileConstantInfo compileRecursorConstantInfo withMutCtx
    refine BlockLayout.Returns.withBlockEnv ?_
    unfold compileRecursorInfo compileRecursorBlock
    exact BlockRecords.Returns.bind fun _ => BlockRecords.Returns.bind fun _ => finishConstant_rows _ _
  | inductInfo v =>
    unfold compileConstantInfo compileInductiveConstantInfo withMutCtx
    exact BlockLayout.Returns.withBlockEnv (inductiveInfo_rows v)
  | ctorInfo v =>
    unfold compileConstantInfo compileConstructorConstantInfo withMutCtx
    refine BlockLayout.Returns.withBlockEnv ?_
    unfold compileConstructorInfo
    refine BlockRecords.Returns.bind fun c => ?_
    split
    · exact inductiveInfo_rows _
    · intro ctx s x s' ran
      cases ran
  | axiomInfo v =>
    unfold compileConstantInfo compileConstantInfoCore withMutCtx
    refine BlockLayout.Returns.withBlockEnv ?_
    unfold compileAxiomInfo compileAxiomBlock
    exact BlockRecords.Returns.bind fun _ => BlockRecords.Returns.bind fun _ => finishConstant_rows _ _

/-- **A block `runBlock` returns with a projection row is a block record.** -/
theorem runBlock_rows {cenv : CompileEnv} {all : Ix.Set Ix.Name} {lo : Ix.Name} {r : BlockResult}
    {c : BlockState} {layout : Option Ixon.AuxLayout} (h : runBlock cenv all lo = .ok (r, c, layout)) :
    RowsMuts r := by
  obtain ⟨const, -, rest⟩ := BlockRecords.runBlockWithAux_records h
  have transfer : ∀ out, RowsMuts out → BlockRecords.recordsOf r = BlockRecords.recordsOf out → RowsMuts r := by
    intro out rows same
    simp only [BlockRecords.recordsOf, Prod.mk.injEq] at same
    obtain ⟨hblock, -, -, hrows⟩ := same
    intro p hp hne
    have hm : (p.1, p.2.1) ∈ out.projections.map fun p => (p.1, p.2.1) := by
      rw [← hrows]; exact Array.mem_map.mpr ⟨p, hp, rfl⟩
    obtain ⟨q, hq, e⟩ := Array.mem_map.mp hm
    have he : q.2.1 = p.2.1 := (Prod.mk.inj e).2
    rw [hblock]
    exact rows q hq (by rw [he, ← hblock]; exact hne)
  rcases rest with ⟨r', s₂, run, same⟩ | ⟨cs, out, s₄, run, same⟩
  · exact transfer r' (compileConstantInfo_rows const _ _ _ _ run) same
  · exact transfer out (compileMutualBlock_rows _ _ _ _ _ run) same

end Rows

/-- **A role bound at a closure name's block is bound at the name's own record**: if a role
with an `ops` specification is bound at the block of the record a group name is published at,
that record is its own block. Otherwise the record is a projection row of its block, the block
a block record (`runBlock_rows`), and the role's record a standalone definition
(`RoleRecordKinds`). -/
theorem block_role {ixe : Ixon.Env} {t : Ix.Kernel.RoleTable} (htable : Ix.Kernel.Reader.defaultTable = .ok t)
    (kinds : RoleRecordKinds ixe) {n : Ix.Name} {A : Address} (claimed : BlockLayout.ClaimedAt ixe n A)
    {r : Ix.Kernel.Role} (hspec : (Ix.Kernel.Role.spec (md := .anon) r).kind = .ops)
    (hrole : t.addressOf? r = some (blockAt ixe A)) : blockAt ixe A = A := by
  obtain ⟨cenv, all, k, res, c, layout, bytes, hr, hclaim, hstored, hblock⟩ := claimed
  have shape := BlockLayout.runBlock_shape hr
  have wire := BlockWire.blocksWire _ _ _ _ _ _ hr
  have blockRec : recordAt ixe res.blockAddr = some res.block := by
    rw [shape.bytes] at hblock
    exact BlockLayout.recordAt_ser wire hblock
  have selfBlock : blockAt ixe res.blockAddr = res.blockAddr := by
    unfold blockAt
    rw [blockRec]
    exact shape.built.owner _
  unfold Resolution.claimWrites at hclaim
  split at hclaim
  · simp only [List.mem_toArray, List.mem_singleton, Prod.mk.injEq] at hclaim
    obtain ⟨-, rfl, rfl⟩ := hclaim
    exact selfBlock
  · obtain ⟨q, hq, e⟩ := Array.mem_map.mp hclaim
    simp only [Prod.mk.injEq] at e
    obtain ⟨-, rfl, rfl⟩ := e
    by_cases same : q.2.1 = res.block
    · rw [same, ← shape.bytes, ← shape.addr]
      exact selfBlock
    · exfalso
      rcases shape.rows q hq with h | ⟨pwire, -, powner⟩
      · exact same h
      have prec := BlockLayout.recordAt_ser pwire hstored
      have hat : blockAt ixe (Address.admissionHash (Ixon.ser q.2.1)) = res.blockAddr := by
        unfold blockAt
        rw [prec]
        exact powner _
      rw [hat] at hrole
      obtain ⟨ms, hms⟩ := runBlock_rows hr q hq same
      obtain ⟨d, hd, -⟩ := (kinds t htable r _ _ hrole blockRec).1 hspec
      rw [hms] at hd
      cases hd

/-! ## Ground edges -/

/-- **`Layout.extra` for ground edges**: from a record of a group's name, the record of a role
the fold reads when it installs a `Nat` operation bound at that record, or at a projection
that record owns, is a record of a name of a group.

The role's record is a standalone definition (`RoleRecordKinds`), so it owns nothing and is not
a block record: it is the group name's own published record (`block_role`). The name then has
the operation's key (`quotientKey_role`), quotient Source declares that key by a definition
(`OpsDeclared`), and the definition's install guard found every ground role installed
(`op_deps_installed`). The fold installs only names its stream declares besides the prelude's
(`installed_over`), and the stream declares a role key only for a closure name with that key
(`stream_role`), published at the role's address (`role_published`).

`claimed` is `Layout.block`'s premise (`BlockLayout.layoutBlock_of_claimed`): a group name's
published record is a primary claim of its block. -/
theorem ground_extra {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ) (kinds : RoleRecordKinds ixe)
    (opsDeclared : ∀ pre ds, Ix.Kernel.Reader.builtinPrelude = .ok pre →
      Ix.LeanIngress.prepareSourceCollapsedAt ixe t ((Ix.LeanIngress.fiberHintsMap ixe)[·]?) pre sub
        (blocksOf sub) = .ok ds → OpsDeclared ds.toList)
    (hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint)
    (claimed : ∀ (i : Nat) (gr : Group), (quotientGraph ixe t hints sub).groups[i]? = some gr →
      ∀ n ∈ gr.names, ∀ a, addrOf ixe n = some a → BlockLayout.ClaimedAt ixe n a) :
    ∀ (i : Nat) (gr : Group), (quotientGraph ixe t hints sub).groups[i]? = some gr → ∀ n ∈ gr.names,
      ∀ a ∈ nameRecords ixe n, ∀ (b : Address) (t' : Ix.Kernel.RoleTable), Ix.Kernel.Reader.defaultTable = .ok t' →
        ∀ (s r : Ix.Kernel.Role) (p : Address), t'.addressOf? s = some b → t'.addressOf? r = some p →
          s ∈ groundRoles r → (p = a ∨ ∃ c, recordAt ixe p = some c ∧ ownerOf p c = a) →
            ∃ (j : Nat) (gr' : Group), (quotientGraph ixe t hints sub).groups[j]? = some gr' ∧
              ∃ m ∈ gr'.names, b ∈ nameRecords ixe m := by
  intro i gr hgr n hn a ha b t' ht' s r p hsb hrp hs hpa
  have tt : t = t' := by
    rw [P.table] at ht'
    exact Except.ok.inj ht'
  subst tt
  have checked := defaultTable_check P.table
  obtain ⟨hop, hspec, hdep, hnotPre, hnotShape⟩ := groundRoles_op s hs
  obtain ⟨ci, hci⟩ := groupName_stored P hgr hn
  obtain ⟨named, hmem, hget⟩ := SourceStoredNames.stored_published P hci
  have hA : addrOf ixe n = some named.addr := by
    unfold addrOf
    rw [hget]
    rfl
  -- the role's record owns nothing, so the edge starts at it
  have hpa' : p = a := by
    rcases hpa with h | ⟨c, hc, ho⟩
    · exact h
    · obtain ⟨d, hd, -⟩ := (kinds t P.table r p c hrp hc).1 hspec
      rw [← ho]
      unfold ownerOf
      rw [hd]
  subst hpa'
  -- and it is the name's published record, not its block
  have hpA : p = named.addr := by
    simp only [nameRecords, hA, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with h | h
    · exact h
    · rw [h] at hrp ⊢
      exact block_role P.table kinds (claimed i gr hgr n hn _ hA) hspec hrp
  subst hpA
  -- the name has the operation's key, which quotient Source declares by a definition
  have hkey := quotientKey_role checked P.bound P.agree hmem hrp
  obtain ⟨-, pre, ds, hpre, hprep, hacc⟩ := P.source
  obtain ⟨d, hd, hkd⟩ := SourceDeclares.preparedAt_declares hprep hci
  have hkd' : (Ix.Kernel.Key.role r : Ix.Kernel.Key .source) ∈ d.names := by
    rw [← hkey]
    exact hkd
  obtain ⟨cv, value, hint, rfl⟩ := opsDeclared pre ds hpre hprep d hd r hspec hkd'
  have hname : cv.name = .role r := by
    simp only [Ix.Kernel.Declaration.names, List.mem_singleton] at hkd'
    exact hkd'.symm
  -- its install guard installed the ground role
  obtain ⟨c, hc, hcn⟩ := op_deps_installed hacc hd (by rw [hname]; exact hop) (.role s)
    (by rw [hname]; exact hdep)
  have hover := installed_over hacc hc
  rw [hcn] at hover
  rcases hover with hb | ⟨r', hr', hbase⟩
  · -- a declared name of the stream, so a closure name's key
    obtain ⟨k', hk', hbase⟩ := List.mem_map.mp hb
    obtain ⟨d', hd', hk'd⟩ := List.mem_flatMap.mp hk'
    obtain ⟨m, cm, hm, hmkey⟩ := stream_role P hpre hprep hd' hk'd hbase hnotShape
    obtain ⟨namedm, hmemm, hgetm⟩ := SourceStoredNames.stored_published P hm
    have hs' := role_published checked P.bound P.agree hmemm hmkey
    obtain rfl : b = namedm.addr := Option.some.inj (hsb.symm.trans hs')
    obtain ⟨j, gr', hgr', hmg⟩ := name_grouped (ixe := ixe) (t := t) (hints := hints) hm
    refine ⟨j, gr', hgr', m, hmg, ?_⟩
    have hAm : addrOf ixe m = some namedm.addr := by
      unfold addrOf
      rw [hgetm]
      rfl
    simp only [nameRecords, hAm, List.mem_cons, true_or]
  · -- a prelude role, which no ground role is
    have same : s = r' := by simpa [Ix.Kernel.Key.base] using hbase
    subst same
    exact absurd hr' hnotPre

/-! ## Compile kinds: a standalone definition record is an input definition's -/

section Kinds

open Ix.CompileM Ix.CompileCert
open Ix.CompileCert.Emission (Yields)

/-- **A definition-like payload keeps its source's kind.** -/
theorem definitionData_kind (d : Ix.Def) :
    Yields (compileDefinitionData d) (fun o => o.1.kind = d.kind) := by
  unfold compileDefinitionData
  refine Yields.withCurrent _ (Yields.withUnivCtx _ (Yields.bindAny _ fun _ => Yields.bindAny _ fun typed => ?_))
  obtain ⟨typeExpr, typeRoot⟩ := typed
  dsimp only
  refine Yields.bindAny _ fun valued => ?_
  obtain ⟨valueExpr, valueRoot⟩ := valued
  dsimp only
  unfold finishDefinitionDataCompilation
  repeat' first
    | exact Yields.pure rfl
    | refine Yields.bindAny _ (fun _ => ?_)

/-- The canonical sharing keeps a constant's payload up to its roots. -/
theorem finishConstant_erase (info : Ixon.ConstantInfo) (blockMeta : Ixon.ConstantMeta) :
    Yields (finishConstantInfoWithSharing info blockMeta)
      (fun r => SharingRoots.erase r.block.info = SharingRoots.erase info ∧ r.projections = #[]) := by
  intro ctx s x s' ran
  unfold finishConstantInfoWithSharing finishConstantWithSharing at ran
  obtain ⟨cache, mid, -, ran⟩ := bind_ok ran
  obtain ⟨block, mid', hb, ran⟩ := bind_ok ran
  rw [rawRun_pure] at ran
  cases ran
  exact ⟨(SharingRoots.build_roots (md := .anon) _ _ _ _ _ (BlockLayout.buildBlockConstant_ok hb)).1, rfl⟩

theorem erase_defn_kind {info : Ixon.ConstantInfo} {d₀ : Ixon.Definition}
    (h : SharingRoots.erase info = SharingRoots.erase (.defn d₀)) {d : Ixon.Definition} (hd : info = .defn d) :
    d.kind = d₀.kind := by
  subst hd
  have inner : Ixon.ConstantInfo.defn { d with typ := .sort 0, value := .sort 0 } =
      .defn { d₀ with typ := .sort 0, value := .sort 0 } := h
  have fields := congrArg Ixon.Definition.kind (Ixon.ConstantInfo.defn.inj inner)
  exact fields

theorem erase_not_defn {info src : Ixon.ConstantInfo} (h : SharingRoots.erase info = SharingRoots.erase src)
    (hs : ∀ d, src ≠ .defn d) {d : Ixon.Definition} (hd : info = .defn d) : False := by
  subst hd
  cases src with
  | defn d' => exact hs d' rfl
  | _ => cases h

/-- What a lone constant's compile says when its block is a standalone definition of kind
`defn`: the constant is a definition and the block has no projection rows. -/
def DefnOut (const : Ix.ConstantInfo) (r : BlockResult) : Prop :=
  ∀ d, r.block.info = .defn d → d.kind = .defn → (∃ v, const = .defnInfo v) ∧ r.projections = #[]

theorem finishConstant_defn {const : Ix.ConstantInfo} {info : Ixon.ConstantInfo} (blockMeta : Ixon.ConstantMeta)
    (hinfo : ∀ d, info = .defn d → d.kind = .defn → ∃ v, const = .defnInfo v) :
    Yields (finishConstantInfoWithSharing info blockMeta) (DefnOut const) := by
  intro ctx s x s' ran
  obtain ⟨erased, proj⟩ := finishConstant_erase info blockMeta ctx s x s' ran
  intro d hd hk
  refine ⟨?_, proj⟩
  cases info with
  | defn d₀ => exact hinfo d₀ rfl (by rw [← erase_defn_kind erased hd]; exact hk)
  | _ => exact (erase_not_defn erased (fun _ h => by cases h) hd).elim

theorem finishInductive_defn {const : Ix.ConstantInfo} (i : Ix.InductiveVal) (ind : Ixon.Inductive)
    (indMeta : Ixon.ConstantMeta) (pairs : Array (Ix.Name × Ixon.ConstantMeta)) :
    Yields (finishInductiveFamilyBlock i ind indMeta pairs) (DefnOut const) := by
  intro ctx s x s' ran
  unfold finishInductiveFamilyBlock at ran
  obtain ⟨_, _, -, ran⟩ := bind_ok ran
  obtain ⟨_, _, -, ran⟩ := bind_ok ran
  obtain ⟨cache, mid, -, ran⟩ := bind_ok ran
  obtain ⟨block, mid', hb, ran⟩ := bind_ok ran
  rw [rawRun_pure] at ran
  cases ran
  intro d hd _
  obtain ⟨targets, h, -⟩ :=
    ProjectionLayout.sharing_mutual_shape _ _ _ _ _ (BlockLayout.buildBlockConstant_ok hb)
  exact absurd (h.symm.trans hd) (by intro e; cases e)

theorem inductiveInfo_defn {const : Ix.ConstantInfo} (v : Ix.InductiveVal) :
    Yields (compileInductiveInfo v) (DefnOut const) := by
  unfold compileInductiveInfo
  refine Yields.bindAny _ fun _ => Yields.withBlockEnv _ ?_
  unfold compileInductiveFamilyInfo compileInductiveFamilyBlock
  exact Yields.bindAny _ fun _ => Yields.bindAny _ fun _ => finishInductive_defn _ _ _ _

/-- **A lone constant whose block is a standalone definition of kind `defn` is a definition**,
and its block has no projection rows. -/
theorem lone_defn (const : Ix.ConstantInfo) : Yields (compileConstantInfo const) (DefnOut const) := by
  cases const with
  | defnInfo v =>
    unfold compileConstantInfo compileDefinitionConstantInfo withMutCtx
    refine Yields.withBlockEnv _ ?_
    unfold compileDefinitionInfo compileDefinitionBlock
    refine Yields.bindAny _ fun _ => Yields.bindAny _ fun x => ?_
    obtain ⟨defn, cmeta, t, val⟩ := x
    exact finishConstant_defn _ fun _ _ _ => ⟨v, rfl⟩
  | thmInfo v =>
    unfold compileConstantInfo compileTheoremConstantInfo withMutCtx
    refine Yields.withBlockEnv _ ?_
    unfold compileTheoremInfo compileDefinitionDataInfo compileDefinitionDataBlock
    refine Yields.bindAny _ fun _ => Yields.bind (definitionData_kind _) fun x hk => ?_
    obtain ⟨defn, cmeta, t, val⟩ := x
    refine finishConstant_defn _ fun d hd hkd => ?_
    cases hd
    simp only [theoremValData] at hk
    rw [hk] at hkd
    cases hkd
  | opaqueInfo v =>
    unfold compileConstantInfo compileOpaqueConstantInfo withMutCtx
    refine Yields.withBlockEnv _ ?_
    unfold compileOpaqueInfo compileDefinitionDataInfo compileDefinitionDataBlock
    refine Yields.bindAny _ fun _ => Yields.bind (definitionData_kind _) fun x hk => ?_
    obtain ⟨defn, cmeta, t, val⟩ := x
    refine finishConstant_defn _ fun d hd hkd => ?_
    cases hd
    simp only [opaqueValData] at hk
    rw [hk] at hkd
    cases hkd
  | quotInfo v =>
    unfold compileConstantInfo compileQuotientConstantInfo withMutCtx
    refine Yields.withBlockEnv _ ?_
    unfold compileQuotientInfo compileQuotientBlock
    refine Yields.bindAny _ fun _ => Yields.bindAny _ fun x => ?_
    obtain ⟨q, cmeta, t⟩ := x
    exact finishConstant_defn _ fun d hd => by cases hd
  | recInfo v =>
    unfold compileConstantInfo compileRecursorConstantInfo withMutCtx
    refine Yields.withBlockEnv _ ?_
    unfold compileRecursorInfo compileRecursorBlock
    refine Yields.bindAny _ fun _ => Yields.bindAny _ fun x => ?_
    obtain ⟨q, cmeta, t⟩ := x
    exact finishConstant_defn _ fun d hd => by cases hd
  | inductInfo v =>
    unfold compileConstantInfo compileInductiveConstantInfo withMutCtx
    exact Yields.withBlockEnv _ (inductiveInfo_defn v)
  | ctorInfo v =>
    unfold compileConstantInfo compileConstructorConstantInfo withMutCtx
    refine Yields.withBlockEnv _ ?_
    unfold compileConstructorInfo
    refine Yields.bindAny _ fun c => ?_
    split
    · exact inductiveInfo_defn _
    · intro ctx s x s' ran
      cases ran
  | axiomInfo v =>
    unfold compileConstantInfo compileConstantInfoCore withMutCtx
    refine Yields.withBlockEnv _ ?_
    unfold compileAxiomInfo compileAxiomBlock
    refine Yields.bindAny _ fun _ => Yields.bindAny _ fun x => ?_
    obtain ⟨q, cmeta, t⟩ := x
    exact finishConstant_defn _ fun d hd => by cases hd


/-- A mutual member's definition kind, if it is a definition. -/
def srcKind : MutConst → Option Ix.DefKind
  | .defn d => some d.kind
  | _ => none

/-- A compiled mutual payload's definition kind, if it is a definition. -/
def payloadKind : Ixon.MutConst → Option Ix.DefKind
  | .defn d => some d.kind
  | _ => none

theorem member_kind (source : MutConst) : Yields (compileMutConstMember source)
    (fun output => payloadKind output.payload = srcKind source) := by
  cases source with
  | defn value =>
    exact Yields.bind (Yields.withCurrent value.name (definitionData_kind value)) fun x hk =>
      Yields.pure (congrArg some hk)
  | recr value =>
    exact Yields.bindAny _ fun _ => Yields.pure rfl
  | indc value =>
    exact Yields.bindAny _ fun _ => Yields.pure rfl

theorem class_kinds (sources : List MutConst) (initial : MutConstCompileState) :
    Yields (compileMutConstClass sources initial) (fun output =>
      output.payloads.toList.map payloadKind = initial.payloads.toList.map payloadKind ++
        sources.head?.toList.map srcKind) := by
  cases sources with
  | nil => exact Yields.pure (by simp)
  | cons source rest =>
    rw [compileMutConstClass]
    exact Yields.bind (member_kind source) fun member kind =>
      fun context before output after ran => by
        have same := ProjectionLayout.equivalents_payloads rest (initial.addRepresentative member) context
          before output after ran
        simp [same, MutConstCompileState.addRepresentative, kind]

theorem classes_kinds (sources : List (List MutConst)) (initial : MutConstCompileState) :
    Yields (compileMutConstClasses sources initial) (fun output =>
      output.payloads.toList.map payloadKind = initial.payloads.toList.map payloadKind ++
        (sources.filterMap List.head?).map srcKind) := by
  induction sources generalizing initial with
  | nil => exact Yields.pure (by simp)
  | cons source rest ih =>
    intro context before output after ran
    rw [compileMutConstClasses] at ran
    obtain ⟨middle, state, firstRun, lastRun⟩ := bind_ok ran
    have first := class_kinds source initial context before middle state firstRun
    have last := ih middle context state output after lastRun
    cases source <;> simpa [first, List.append_assoc, List.filterMap] using last

/-- **The retained payloads have the representatives' definition kinds**, one per non-empty
class, in class order. -/
theorem payload_kinds (sources : List (List MutConst)) : Yields (compileMutConsts sources)
    (fun output => output.1.toList.map payloadKind = (sources.filterMap List.head?).map srcKind) := by
  unfold compileMutConsts
  exact Yields.bind (classes_kinds sources {}) fun compiled kinds =>
    Yields.pure (by simpa using kinds)

/-- What a mutual block's compile says when its block is a standalone definition of kind
`defn`: one class, its representative a definition of kind `defn`, and rows named after the
classes' members, at least one. -/
def MutDefnOut (classes : List (List MutConst)) (out : BlockResult) : Prop :=
  ∀ d, out.block.info = .defn d → d.kind = .defn →
    ∃ x, classes.filterMap List.head? = [x] ∧ srcKind x = some .defn ∧
      out.projections ≠ #[] ∧ ∀ p ∈ out.projections, p.1 ∈ classes.flatten.map MutConst.name

theorem buildMutual_defn {limits : Ix.Sharing.Exact.Limits} {classes : List (List MutConst)}
    {payloads : Array Ixon.MutConst} {metas : Array (Ix.Name × Ixon.ConstantMeta)} {cache : BlockState}
    {out : BlockResult}
    (kinds : payloads.toList.map payloadKind = (classes.filterMap List.head?).map srcKind)
    (ran : buildCompiledMutualBlock limits classes payloads metas cache = .ok out) : MutDefnOut classes out := by
  unfold buildCompiledMutualBlock at ran
  cases hs : standaloneMutConstInfo? payloads with
  | some info =>
    rw [hs] at ran
    obtain ⟨block, hb, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases Except.ok.inj returned
    intro d hd hk
    have erased := (SharingRoots.build_roots (md := .anon) _ _ _ _ _ hb).1
    have rows : ∀ p ∈ buildStandaloneMutualProjections classes block metas,
        (p.1, p.2.1) ∈ classes.flatten.map (fun source => (source.name, block)) := by
      intro p hp
      rw [← MutualProjections.standalone_rows]
      exact List.mem_map.mpr ⟨p, Array.mem_toList_iff.mpr hp, rfl⟩
    rcases payloads with ⟨l⟩
    rcases l with _ | ⟨m, _ | ⟨m₂, rest⟩⟩
    · cases hs
    rotate_left
    · cases hs
    cases m with
    | indc i => cases hs
    | recr r =>
      cases hs
      exact (erase_not_defn erased (fun _ h => by cases h) hd).elim
    | defn definition =>
      cases hs
      have hkd := erase_defn_kind erased hd
      rw [hk] at hkd
      change [some definition.kind] = _ at kinds
      generalize hL : classes.filterMap List.head? = L at kinds
      rcases L with _ | ⟨x, _ | ⟨y, L⟩⟩
      · simp at kinds
      · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at kinds
        have hx : x ∈ classes.flatten := by
          obtain ⟨cl, hcl, hh⟩ := List.mem_filterMap.mp (hL ▸ List.mem_singleton_self x)
          exact List.mem_flatten.mpr ⟨cl, hcl, List.mem_of_mem_head? hh⟩
        refine ⟨x, rfl, by rw [← kinds, ← hkd], ?_, ?_⟩
        · intro he
          have hm : (x.name, block) ∈ (buildStandaloneMutualProjections classes block metas).toList.map
              (fun p => (p.1, p.2.1)) := by
            rw [← MutualProjections.logicalRows, MutualProjections.standalone_rows]
            exact List.mem_map.mpr ⟨x, hx, rfl⟩
          simp only [BlockResult.mk'] at he
          rw [he] at hm
          simp at hm
        · intro p hp
          obtain ⟨y, hy, e⟩ := List.mem_map.mp (rows p hp)
          exact List.mem_map.mpr ⟨y, hy, (Prod.mk.inj e).1⟩
      · simp at kinds
  | none =>
    rw [hs] at ran
    obtain ⟨block, hb, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases Except.ok.inj returned
    intro d hd _
    obtain ⟨targets, h, -⟩ := ProjectionLayout.sharing_mutual_shape _ _ _ _ _ hb
    exact absurd (h.symm.trans hd) (by intro e; cases e)

theorem compileMutualBlock_defn (classes : List (List MutConst)) :
    Yields (compileMutualBlock classes) (MutDefnOut classes) := by
  intro ctx s x s' ran
  unfold compileMutualBlock at ran
  dsimp only at ran
  unfold withMutCtx at ran
  rw [rawRun_withBlockEnv] at ran
  obtain ⟨_, _, -, compiled⟩ := bind_ok ran
  unfold compileMutualPayload at compiled
  obtain ⟨⟨payloads, roots, metas⟩, mid, hp, finished⟩ := bind_ok compiled
  have kinds := payload_kinds classes _ _ _ _ hp
  exact buildMutual_defn kinds (ProjectionLayout.finish_mutual_ok _ _ _ _ finished).2.2

/-- Lean's order puts each member in a class of its own. -/
theorem sourceClasses_flat (cs : Array MutConst) :
    (sourceClasses cs).filterMap List.head? = (sourceClasses cs).flatten ∧
      ∀ y ∈ (sourceClasses cs).flatten, y ∈ cs := by
  unfold sourceClasses
  dsimp only
  generalize hL : (cs.zipIdx.qsort _).toList = L
  have mem : ∀ e ∈ L, e.1 ∈ cs := by
    intro e he
    rw [← hL] at he
    have := Ix.CompileCert.Canon.mem_qsort.mp (Array.mem_toList_iff.mp he)
    exact Array.mem_of_getElem? (Array.mem_zipIdx_iff_getElem?.mp this)
  clear hL
  induction L with
  | nil => exact ⟨rfl, fun y hy => by simp at hy⟩
  | cons e L ih =>
    obtain ⟨ih₁, ih₂⟩ := ih fun e' he' => mem e' (List.mem_cons_of_mem _ he')
    refine ⟨?_, fun y hy => ?_⟩
    · simp only [List.map_cons, List.filterMap_cons, List.head?_cons, List.flatten_cons]
      rw [ih₁]
      rfl
    · simp only [List.map_cons, List.flatten_cons, List.mem_append, List.mem_singleton] at hy
      rcases hy with rfl | hy
      · exact mem e List.mem_cons_self
      · exact ih₂ y hy

/-- An invariant a loop's steps keep holds of its result. -/
theorem forIn_rawRun_inv {α σ : Type} (I : σ → Prop) {body : α → σ → CompileM (ForInStep σ)}
    {ctx : CompileEnv × BlockEnv}
    (step : ∀ x s₀ acc acc' s₁, I acc → rawRun (body x acc) ctx s₀ = (.ok acc', s₁) → I acc'.value) :
    ∀ (l : List α) (init : σ) (s s' : BlockState) (out : σ), I init →
      rawRun (forIn l init body) ctx s = (.ok out, s') → I out
  | [], init, s, s', out, hi, h => by
    rw [List.forIn_nil, rawRun_pure] at h
    cases h
    exact hi
  | x :: l, init, s, s', out, hi, h => by
    rw [List.forIn_cons] at h
    obtain ⟨st, mid, hb, h⟩ := bind_ok h
    have hst := step x s init st mid hi hb
    cases st with
    | done b =>
      rw [rawRun_pure] at h
      cases h
      exact hst
    | yield b => exact forIn_rawRun_inv I step l b mid s' out hst h

/-- **A block's members' loop makes a definition of kind `defn` only of an input definition.** -/
theorem members_defn {ctx : CompileEnv × BlockEnv} {all : Ix.Set Ix.Name} {s s' : BlockState}
    {cs : Array Ix.MutConst}
    (h : rawRun (forIn all #[] fun n (acc : Array Ix.MutConst) => do
            match ← findConst n with
            | .inductInfo val => pure (ForInStep.yield (acc.push (← MutConst.mkIndc val)))
            | .defnInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromDefinitionVal val)))
            | .opaqueInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromOpaqueVal val)))
            | .thmInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromTheoremVal val)))
            | .recInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.recr val)))
            | _ => pure (ForInStep.yield acc)) ctx s = (.ok cs, s')) :
    ∀ x ∈ cs, srcKind x = some .defn →
      ∃ m val, ctx.1.env.get? m = some (.defnInfo val) ∧ x = Ix.MutConst.fromDefinitionVal val := by
  rw [Std.HashSet.forIn_eq_forIn_toList] at h
  refine forIn_rawRun_inv (fun (acc : Array Ix.MutConst) => ∀ x ∈ acc, srcKind x = some .defn →
      ∃ m val, ctx.1.env.get? m = some (.defnInfo val) ∧ x = Ix.MutConst.fromDefinitionVal val)
    ?_ all.toList #[] s s' cs (fun x hx => by simp at hx) h
  intro n s₀ acc acc' s₁ hacc ran
  obtain ⟨c, mid, hfind, ran⟩ := bind_ok ran
  have hc := BlockRecords.findConst_ok hfind
  have push : ∀ y, (srcKind y = some .defn → ∃ m val, ctx.1.env.get? m = some (.defnInfo val) ∧
      y = Ix.MutConst.fromDefinitionVal val) →
      ∀ x ∈ acc.push y, srcKind x = some .defn →
        ∃ m val, ctx.1.env.get? m = some (.defnInfo val) ∧ x = Ix.MutConst.fromDefinitionVal val := by
    intro y hy x hx
    rcases Array.mem_push.mp hx with hx | rfl
    · exact hacc x hx
    · exact hy
  cases c with
  | inductInfo val =>
    obtain ⟨y, mid', hy, ran⟩ := bind_ok ran
    rw [rawRun_pure] at ran
    cases ran
    refine push y fun hk => ?_
    unfold MutConst.mkIndc at hy
    obtain ⟨_, _, -, hy⟩ := bind_ok hy
    rw [rawRun_pure] at hy
    cases hy
    cases hk
  | defnInfo val =>
    rw [rawRun_pure] at ran
    cases ran
    exact push _ fun _ => ⟨n, val, hc, rfl⟩
  | opaqueInfo val =>
    rw [rawRun_pure] at ran
    cases ran
    exact push _ fun hk => by cases hk
  | thmInfo val =>
    rw [rawRun_pure] at ran
    cases ran
    exact push _ fun hk => by cases hk
  | recInfo val =>
    rw [rawRun_pure] at ran
    cases ran
    exact push _ fun hk => by cases hk
  | _ =>
    rw [rawRun_pure] at ran
    cases ran
    exact hacc

/-- **A group name's published record is a primary claim of its block's compile**, run in a
compile environment that reads the input's constants: `BlockLayout.ClaimedAt` with the
environment the fold's states keep. -/
def ClaimedIn (env : Ix.Environment) (ixe : Ixon.Env) (n : Ix.Name) (a : Address) : Prop :=
  ∃ (cenv : CompileEnv) (A : Ix.Set Ix.Name) (k : Ix.Name) (r : BlockResult) (c : BlockState)
    (layout : Option Ixon.AuxLayout) (b : ByteArray),
    (∀ x, cenv.env.get? x = env.consts.get? x) ∧
    runBlock cenv A k = .ok (r, c, layout) ∧ (n, a, b) ∈ Resolution.claimWrites k r ∧
    ixe.consts.get? a = some { buf := b, len := b.size } ∧
    ixe.consts.get? r.blockAddr = some { buf := r.blockBytes, len := r.blockBytes.size }

theorem ClaimedIn.claimedAt {env : Ix.Environment} {ixe : Ixon.Env} {n : Ix.Name} {a : Address}
    (h : ClaimedIn env ixe n a) : BlockLayout.ClaimedAt ixe n a := by
  obtain ⟨cenv, A, k, r, c, layout, b, -, rest⟩ := h
  exact ⟨cenv, A, k, r, c, layout, b, rest⟩

/-- A definition record is its own owner, so it projects into no block. -/
theorem defn_not_projects {c : Ixon.Constant} {d : Ixon.Definition} (hd : c.info = .defn d) (owner : Address) :
    ¬ BlockLayout.ProjectsTo owner c := by
  rintro ⟨-, -, powner⟩
  have h₁ : (⟨ByteArray.empty⟩ : Address) = owner := by
    have := powner ⟨ByteArray.empty⟩
    unfold ownerOf at this
    rw [hd] at this
    exact this
  have h₂ : (⟨⟨#[0]⟩⟩ : Address) = owner := by
    have := powner ⟨⟨#[0]⟩⟩
    unfold ownerOf at this
    rw [hd] at this
    exact this
  have same := congrArg (fun a : Address => a.hash.size) (h₁.trans h₂.symm)
  exact absurd same (by decide)

/-- **A closure name published at a standalone definition record of kind `defn` is an input
definition.** The record is the claim's block itself: a lone constant's compile makes one only
of a definition (`lone_defn`), a mutual block's only of a single member that the block's members'
loop made of an input definition (`compileMutualBlock_defn`, `members_defn`). -/
theorem claimed_definition {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (compiled : compileReport env = .ok (ixe, failures)) {n : Ix.Name} {A : Address}
    (claimed : ClaimedIn env ixe n A) {c : Ixon.Constant} (hc : recordAt ixe A = some c)
    {d : Ixon.Definition} (hd : c.info = .defn d) (hk : d.kind = .defn) :
    ∃ v, env.consts.get? n = some (.defnInfo v) := by
  obtain ⟨cenv, all, k, res, cst, layout, bytes, henv, hr, hclaim, hstored, hblock⟩ := claimed
  have shape := BlockLayout.runBlock_shape hr
  have wire := BlockWire.blocksWire _ _ _ _ _ _ hr
  have blockRec : recordAt ixe res.blockAddr = some res.block := by
    rw [shape.bytes] at hblock
    exact BlockLayout.recordAt_ser wire hblock
  -- the claim is the block record, as the block's key or as one of its rows
  have claimBlock : res.block.info = .defn d ∧
      ((res.projections = #[] ∧ n = k) ∨ ∃ q ∈ res.projections, n = q.1) := by
    unfold Resolution.claimWrites at hclaim
    split at hclaim
    · rename_i hempty
      simp only [List.mem_toArray, List.mem_singleton, Prod.mk.injEq] at hclaim
      obtain ⟨rfl, rfl, rfl⟩ := hclaim
      rw [blockRec] at hc
      cases hc
      exact ⟨hd, .inl ⟨Array.isEmpty_iff.mp hempty, rfl⟩⟩
    · obtain ⟨q, hq, e⟩ := Array.mem_map.mp hclaim
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      rcases shape.rows q hq with same | proj
      · rw [same, ← shape.bytes, ← shape.addr, blockRec] at hc
        cases hc
        exact ⟨hd, .inr ⟨q, hq, rfl⟩⟩
      · have prec := BlockLayout.recordAt_ser proj.1 hstored
        rw [prec] at hc
        cases hc
        exact (defn_not_projects hd _ proj).elim
  obtain ⟨hinfo, hname⟩ := claimBlock
  obtain ⟨const, s₁, hfind, rest⟩ := BlockRecords.compileBlockWithAux_result
    (Ix.CompileCert.run_success (BlockRecords.runBlockWithAux_compiles hr))
  have hconst := BlockRecords.findConst_ok hfind
  rcases rest with ⟨s₂, lone⟩ | ⟨cs, s₂, out, s₄, loop, hmut, same⟩
  · obtain ⟨⟨v, rfl⟩, hempty⟩ := lone_defn const _ _ _ _ lone d hinfo hk
    rcases hname with ⟨-, rfl⟩ | ⟨q, hq, -⟩
    · exact ⟨v, (henv _).symm.trans hconst⟩
    · rw [hempty] at hq
      exact absurd hq (Array.not_mem_empty _)
  · simp only [BlockRecords.recordsOf, Prod.mk.injEq] at same
    obtain ⟨hblock', -, -, hrows⟩ := same
    obtain ⟨x, hx, hxk, hne, hrowsName⟩ :=
      compileMutualBlock_defn _ _ _ _ _ hmut d (hblock' ▸ hinfo) hk
    obtain ⟨flat, inCs⟩ := sourceClasses_flat cs
    have hxcs : x ∈ cs := inCs x (by rw [← flat, hx]; exact List.mem_singleton_self x)
    obtain ⟨m, val, hm, rfl⟩ := members_defn loop x hxcs hxk
    have hn : n = val.cnst.name := by
      rcases hname with ⟨hempty, -⟩ | ⟨q, hq, rfl⟩
      · exfalso
        apply hne
        have : out.projections.map (fun p => (p.1, p.2.1)) = #[] := by rw [← hrows, hempty, Array.map_empty]
        exact Array.map_eq_empty_iff.mp this
      · have hm' : (q.1, q.2.1) ∈ out.projections.map (fun p => (p.1, p.2.1)) := by
          rw [← hrows]
          exact Array.mem_map.mpr ⟨q, hq, rfl⟩
        obtain ⟨q', hq', e⟩ := Array.mem_map.mp hm'
        have hq1 : q'.1 = q.1 := (Prod.mk.inj e).1
        have hnm := hrowsName q' hq'
        rw [hq1, ← flat, hx] at hnm
        simpa [Ix.MutConst.fromDefinitionVal, Ix.MutConst.name] using hnm
    rw [henv] at hm
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList] at hm
    obtain ⟨k', -, hk'⟩ := hm
    have hname' := inputsNamed compiled k' _ hk'
    refine ⟨val, ?_⟩
    rw [hn, show val.cnst.name = k' from hname']
    exact SourceStoredNames.stored_get hk'
end Kinds

/-! ## `sorryAx`'s key -/

/-- **A published name whose record is no axiom record does not have `sorryAx`'s key**: a name
with that key sits at the address the table binds `sorryAx` to (`role_published`), where the
record is an axiom (`RoleRecordKinds`). A member of a block of several definitions is
published at its `dPrj` row (`BlockPublication.member_published`), so this is `sameKey`'s
`notSorry` for the members of `exactNames`. -/
theorem not_sorryAx {ixe : Ixon.Env} {t : Ix.Kernel.RoleTable} (htable : Ix.Kernel.Reader.defaultTable = .ok t)
    (bound : PublishedRolesBound t ixe) (agree : PublishedAgree ixe) (kinds : RoleRecordKinds ixe)
    {m : Ix.Name} {named : Ixon.Named} (hm : (m, named) ∈ ixe.named.toList) {c : Ixon.Constant}
    (hc : recordAt ixe named.addr = some c) (notAxiom : ∀ ax, c.info ≠ .axio ax) :
    quotientKey ixe t m ≠ Ix.Kernel.sorryAxName := by
  intro hkey
  have hs := role_published (defaultTable_check htable) bound agree hm hkey
  obtain ⟨ax, hax⟩ := (kinds t htable .sorryAx _ _ hs hc).2 rfl
  exact notAxiom ax hax
end Ix.Cert.LayoutExtra

/--
info: 'Ix.Cert.LayoutExtra.recursor_extra' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Cert.LayoutExtra.recursor_extra

/--
info: 'Ix.Cert.LayoutExtra.ground_extra' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Cert.LayoutExtra.ground_extra

/--
info: 'Ix.Cert.LayoutExtra.claimed_definition' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Cert.LayoutExtra.claimed_definition

/--
info: 'Ix.Cert.LayoutExtra.not_sorryAx' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Cert.LayoutExtra.not_sorryAx
