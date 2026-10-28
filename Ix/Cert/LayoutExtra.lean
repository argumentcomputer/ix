import Ix.Cert.ReportChecks
import Ix.Cert.LiteralSources
import Ix.Cert.FreshSnapshot
import Ix.Cert.ClosureLayout
import Ix.Cert.ClosureClaims
import Ix.Cert.LayoutRefs
import Ix.Cert.SourceTotality
import Ix.Cert.DefinitionPremises
import Ix.Cert.SourceOrigin
import Ix.Cert.CtxAgree
import Ix.Cert.BlockLayout
import Ix.Cert.BlockWire
import Ix.Cert.RecordReadings

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
of an input definition (`compileMutualBlock_defn`, `members_defn`). Quotient Source then declares
an operation's key by a definition (`stream_defn`): a group's names are stored constants of the
group's kind (`groupsOf_kinded`), so an inductive, axiom or quotient group has no definition
with the key, and a definitions group lowers each member at its own kind. Together they give
`OpsDeclared` (`opsDeclared_of`), so the ground edges follow from the claims
(`ground_extra_of`). A name with `sorryAx`'s key sits at the role's axiom record (`not_sorryAx`).

**Literals.** A group name's records are its block's record or bare projections, which hold no
literal (`claimed_records`, `RowsMuts`). The block's record holds a literal only where a term its
compile reads does (`LiteralSources.runBlock_lits`): a term of the block's key or members, which
are closure names (`ClaimedIn`'s `MembersIn`), or of a constructor an inductive member lists.
That constant depends on the literal's support names (`literalSupport`), so they are reached
(`literal_reaches`), and a support role's stored record is its name's (`LiteralRolesNamed`, a
compile-report check), so the edge's target is a closure name's record (`literal_extra`). The
three cases together are `layout_extra`. -/

namespace Ix.Cert.LayoutExtra

open Ix.LeanIngress (Graph Group FiberMap Converted graphCollapsed scheduleOf lower)
open Ix.Kernel.Reader (State Read)
open Ix.Cert.SourcePrelude (Scheduled)
open Ix.Kernel.Reader (Store RecIndex BlockShape buildIndex)
open Ix.Cert.ClosureLayout

/-! ## The premise: the index's recursors are the family's -/

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

/-- **A block whose rows include a projection is a block record** (`muts`), and the projection
holds no literal (a bare projection: no sharing table, no expressions). -/
def RowsMuts (r : BlockResult) : Prop :=
  ∀ p ∈ r.projections, p.2.1 ≠ r.block →
    (∃ ms, r.block.info = .muts ms) ∧ Ix.Kernel.Reader.literalKinds p.2.1 = (false, false)

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
  intro p hp _
  obtain ⟨targets, h, -⟩ :=
    ProjectionLayout.sharing_mutual_shape _ _ _ _ _ (BlockLayout.buildBlockConstant_ok hb)
  refine ⟨⟨targets, h⟩, ?_⟩
  simp only [BlockResult.mk'] at hp
  unfold buildInductiveProjections at hp
  rcases Array.mem_append.mp hp with hp | hp
  · simp at hp
    subst hp
    rfl
  · obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hp
    rw [Array.getElem_mapIdx]
    split
    rfl

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
    intro p hp _
    obtain ⟨targets, h, -⟩ := ProjectionLayout.sharing_mutual_shape _ _ _ _ _ hb
    refine ⟨⟨targets, h⟩, ?_⟩
    have logical : (p.1, p.2.1) ∈ MutualProjections.logicalRows
        (buildMutualProjections classes (Address.admissionHash (Ixon.ser block)) metas) :=
      List.mem_map.mpr ⟨p, Array.mem_toList_iff.mpr hp, rfl⟩
    rw [MutualProjections.build_rows, MutualProjections.expectedRows] at logical
    obtain ⟨⟨members, index⟩, -, inClass⟩ := List.mem_flatMap.mp logical
    obtain ⟨source, -, generated⟩ := List.mem_flatMap.mp inClass
    unfold MutualProjections.sourceRows at generated
    rcases List.mem_cons.mp generated with e | rest
    · rw [(Prod.mk.inj e).2]
      cases source <;> rfl
    · obtain ⟨⟨ctor, ctorIndex⟩, -, e⟩ := List.mem_map.mp rest
      rw [← (Prod.mk.inj e).2]
      rfl

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
    {c : BlockState} (h : runBlock cenv all lo = .ok (r, c)) :
    RowsMuts r := by
  obtain ⟨const, -, rest⟩ := BlockRecords.runBlock_records h
  have transfer : ∀ out, RowsMuts out → BlockRecords.recordsOf r = BlockRecords.recordsOf out → RowsMuts r := by
    intro out rows same
    simp only [BlockRecords.recordsOf, Prod.mk.injEq] at same
    obtain ⟨hblock, -, -, hrows⟩ := same
    intro p hp hne
    have hm : (p.1, p.2.1) ∈ out.projections.map fun p => (p.1, p.2.1) := by
      rw [← hrows]; exact Array.mem_map.mpr ⟨p, hp, rfl⟩
    obtain ⟨q, hq, e⟩ := Array.mem_map.mp hm
    have he : q.2.1 = p.2.1 := (Prod.mk.inj e).2
    have row := rows q hq (by rw [he, ← hblock]; exact hne)
    rw [he] at row
    rw [hblock]
    exact row
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
  obtain ⟨cenv, all, k, res, c, bytes, hr, hclaim, hstored, hblock⟩ := claimed
  have shape := BlockLayout.runBlock_shape hr
  have wire := BlockWire.blocksWire _ _ _ _ _ hr
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
      obtain ⟨⟨ms, hms⟩, -⟩ := runBlock_rows hr q hq same
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

/-- **A block's member names are closure names**: every name of the compiled block's member set
is a key of the closure. -/
def MembersIn (sub : Ix.Environment) (A : Ix.Set Ix.Name) : Prop :=
  ∀ x, A.contains x = true → ∃ ci, (x, ci) ∈ sub.consts.toList

/-- **A group name's published record is a primary claim of its block's compile**, run in a
compile environment that reads the input's constants: `BlockLayout.ClaimedAt` with the
environment the fold's states keep, and with the block's key and members closure names. -/
def ClaimedIn (env sub : Ix.Environment) (ixe : Ixon.Env) (n : Ix.Name) (a : Address) : Prop :=
  ∃ (cenv : CompileEnv) (A : Ix.Set Ix.Name) (k : Ix.Name) (r : BlockResult) (c : BlockState)
    (b : ByteArray),
    (∀ x, cenv.env.get? x = env.consts.get? x) ∧ A.contains k = true ∧ MembersIn sub A ∧
    runBlock cenv A k = .ok (r, c) ∧ (n, a, b) ∈ Resolution.claimWrites k r ∧
    ixe.consts.get? a = some { buf := b, len := b.size } ∧
    ixe.consts.get? r.blockAddr = some { buf := r.blockBytes, len := r.blockBytes.size }

theorem ClaimedIn.claimedAt {env sub : Ix.Environment} {ixe : Ixon.Env} {n : Ix.Name} {a : Address}
    (h : ClaimedIn env sub ixe n a) : BlockLayout.ClaimedAt ixe n a := by
  obtain ⟨cenv, A, k, r, c, b, -, -, -, rest⟩ := h
  exact ⟨cenv, A, k, r, c, b, rest⟩

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
theorem claimed_definition {env sub : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (compiled : compileReport env = .ok (ixe, failures)) {n : Ix.Name} {A : Address}
    (claimed : ClaimedIn env sub ixe n A) {c : Ixon.Constant} (hc : recordAt ixe A = some c)
    {d : Ixon.Definition} (hd : c.info = .defn d) (hk : d.kind = .defn) :
    ∃ v, env.consts.get? n = some (.defnInfo v) := by
  obtain ⟨cenv, all, k, res, cst, bytes, henv, -, -, hr, hclaim, hstored, hblock⟩ := claimed
  have shape := BlockLayout.runBlock_shape hr
  have wire := BlockWire.blocksWire _ _ _ _ _ hr
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
  obtain ⟨const, s₁, hfind, rest⟩ := BlockRecords.compileBlock_result
    (Ix.CompileCert.run_success (BlockRecords.runBlock_compiles hr))
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

/-! ## Source kinds: a group's names are stored constants of the group's kind -/

section SourceKinds

open Ix.LeanIngress
open Ix.CompileCert.Loop (idBind idPure except_bind_ok)
open SourceStoredNames (forIn_id_prop forIn_id_prop_array lookup_stored Pending blockRecursors_mem)

/-- The kind a group's constants have: an inductive group's are inductives, constructors or
recursors; a definitions group's are its members; an axiom or quotient group's its constant. -/
def GroupKind : Group → Ix.ConstantInfo → Prop
  | .inductive _ _ _, ci => isFamily ci = true
  | .definitions ms, ci => ci ∈ ms
  | .axiom v, ci => ci = .axiomInfo v
  | .quot v, ci => ci = .quotInfo v
  | .invalid _ _, _ => True

/-- **A group's names are own names of stored constants of the group's kind**
(`SourceStoredNames.NamesStored`, with the kind kept). -/
def NamesKinded (env : Ix.Environment) (g : Group) : Prop :=
  (∀ x ∈ g.names, ∃ k ci, (k, ci) ∈ env.consts.toList ∧ ci.getCnst.name = x ∧ GroupKind g ci) ∧
    ∀ ms, g = .definitions ms → ∀ ci ∈ ms, ∃ k, (k, ci) ∈ env.consts.toList

theorem kinded_of_others {env : Ix.Environment} {g : Group} {others : Array Ix.ConstantInfo}
    (stored : ∀ ci ∈ others, ∃ k, (k, ci) ∈ env.consts.toList)
    (names : g.names = others.map (·.getCnst.name)) (kinds : ∀ ci ∈ others, GroupKind g ci)
    (members : ∀ ms, g = .definitions ms → ∀ ci ∈ ms, ci ∈ others) : NamesKinded env g := by
  refine ⟨fun x hx => ?_, fun ms hg ci hci => stored ci (members ms hg ci hci)⟩
  rw [names] at hx
  obtain ⟨ci, hci, rfl⟩ := Array.mem_map.mp hx
  obtain ⟨k, hk⟩ := stored ci hci
  exact ⟨k, ci, hk, rfl, kinds ci hci⟩

theorem componentGroup_kinded {env : Ix.Environment} {members : Ix.Set Ix.Name} {g : Group}
    (h : componentGroup env members = some g) : NamesKinded env g := by
  rw [Ix.Cert.SourceGroupPlan.component_default] at h
  unfold componentGroupUsing at h
  generalize hcis : (Array.filterMapM (m := Id) (fun x => env.consts.get? x) members.toArray :
    Array Ix.ConstantInfo) = cis at h
  dsimp only [Id.run, bind, pure] at h
  have stored : ∀ ci ∈ Id.run cis, ∃ k, (k, ci) ∈ env.consts.toList := by
    intro ci hci
    rw [← hcis] at hci
    have hm : ci ∈ members.toArray.filterMap (fun x => env.consts.get? x) := hci
    obtain ⟨x, -, hx⟩ := Array.mem_filterMap.mp hm
    exact lookup_stored hx
  generalize hothers : (cis.filter (fun x => !isFamily x)).qsort
    (fun a b => Ix.sourceOrderLt (a.blockPosition, a.getCnst.name)
      (b.blockPosition, b.getCnst.name)) = others at h
  have storedOthers : ∀ ci ∈ others, ∃ k, (k, ci) ∈ env.consts.toList := by
    intro ci hci
    rw [← hothers] at hci
    exact stored ci (Array.mem_filter.mp (Ix.CompileCert.Canon.mem_qsort.mp hci)).1
  split at h
  · cases h
  · split at h
    · cases h
      exact kinded_of_others storedOthers rfl (fun _ _ => trivial) (fun _ h => by cases h)
    · split at h
      · cases h
        exact kinded_of_others storedOthers rfl (fun _ h => h) (fun _ h => by cases h; exact fun _ h => h)
      · obtain ⟨l⟩ := others
        rcases l with _ | ⟨c, _ | ⟨c₂, rest⟩⟩
        · cases h
          exact kinded_of_others storedOthers rfl (fun _ _ => trivial) (fun _ h => by cases h)
        · cases c <;> cases h
          all_goals first
            | exact kinded_of_others storedOthers rfl (fun _ _ => trivial) (fun _ h => by cases h)
            | exact kinded_of_others storedOthers (by simp [Group.names, Ix.ConstantInfo.getCnst])
                (fun ci hci => by simpa [GroupKind] using hci) (fun _ h => by cases h)
        · cases h
          exact kinded_of_others storedOthers rfl (fun _ _ => trivial) (fun _ h => by cases h)

theorem inductiveGroup_kinded {env : Ix.Environment} {first : Ix.InductiveVal}
    {cands : Array Ix.RecursorVal}
    (hc : ∀ r ∈ cands, ∃ k, (k, Ix.ConstantInfo.recInfo r) ∈ env.consts.toList) {c : Converted}
    (conv : convert (inductiveGroup env first cands) = .ok c) :
    NamesKinded env (inductiveGroup env first cands) := by
  generalize hg : inductiveGroup env first cands = g at conv ⊢
  rw [Ix.Cert.SourceGroupPlan.inductive_default] at hg
  unfold inductiveGroupUsing at hg
  simp only [Id.run, idBind, idPure] at hg
  split at hg
  · rename_i r hr
    have pend : Pending (some r) := by
      rw [← hr]
      refine forIn_id_prop_array (I := fun s : Option Group × Array Ix.InductiveVal => Pending s.1)
        (Q := fun t => Pending t.1) _ ?_ (fun _ h => h) _ (.inl rfl)
      intro x _ s _
      split
      · split
        · exact .inl rfl
        · exact .inr ⟨_, _, rfl⟩
      · exact .inr ⟨_, _, rfl⟩
    rcases pend with h0 | ⟨cl, e, he⟩
    · cases h0
    · cases he
      subst hg
      cases conv
  · split at hg
    · rename_i r hr
      have pend : Pending (some r) := by
        rw [← hr]
        refine forIn_id_prop_array
          (I := fun s : Option Group × Array (Array Ix.ConstructorVal) => Pending s.1)
          (Q := fun t => Pending t.1) _ ?_ (fun _ h => h) _ (.inl rfl)
        intro v _ s _
        split
        · rename_i r' hr'
          show Pending (some r')
          rw [← hr']
          refine forIn_id_prop_array (I := fun s : Option Group × Array Ix.ConstructorVal => Pending s.1)
            (Q := fun t => Pending t.1) _ ?_ (fun _ h => h) _ (.inl rfl)
          intro x _ s _
          split
          · split
            · split
              · exact .inl rfl
              · exact .inr ⟨_, _, rfl⟩
            · exact .inr ⟨_, _, rfl⟩
          · exact .inr ⟨_, _, rfl⟩
        · exact .inl rfl
      rcases pend with h0 | ⟨cl, e, he⟩
      · cases h0
      · cases he
        subst hg
        cases conv
    · split at hg
      · rename_i recs hrecs
        subst hg
        refine ⟨fun x hx => ?_, fun ms h => by cases h⟩
        unfold Group.names at hx
        rcases Array.mem_append.mp hx with hx | hx
        · rcases Array.mem_append.mp hx with hx | hx
          · obtain ⟨v, hv, rfl⟩ := Array.mem_map.mp hx
            refine (forIn_id_prop_array
              (I := fun s : Option Group × Array Ix.InductiveVal =>
                ∀ v ∈ s.2, ∃ k, (k, Ix.ConstantInfo.inductInfo v) ∈ env.consts.toList)
              (Q := fun t => ∀ v ∈ t.2, ∃ k ci, (k, ci) ∈ env.consts.toList ∧ ci.getCnst.name = v.cnst.name ∧
                isFamily ci = true)
              _ ?_ ?_ _ ?_) v hv
            · intro y _ s hs
              split
              · rename_i v' hv'
                split
                · intro w hw
                  rcases Array.mem_push.mp hw with hw | rfl
                  · exact hs w hw
                  · exact lookup_stored hv'
                · exact hs
              · exact hs
            · intro t ht v hv
              obtain ⟨k, hk⟩ := ht v hv
              exact ⟨k, _, hk, rfl, rfl⟩
            · intro v hv
              exact absurd hv (Array.not_mem_empty _)
          · obtain ⟨cs, hcs, hx⟩ := Array.mem_flatMap.mp hx
            obtain ⟨cv, hcv, rfl⟩ := Array.mem_map.mp hx
            refine (forIn_id_prop_array
              (I := fun s : Option Group × Array (Array Ix.ConstructorVal) =>
                ∀ cs ∈ s.2, ∀ cv ∈ cs, ∃ k, (k, Ix.ConstantInfo.ctorInfo cv) ∈ env.consts.toList)
              (Q := fun t => ∀ cs ∈ t.2, ∀ cv ∈ cs,
                ∃ k ci, (k, ci) ∈ env.consts.toList ∧ ci.getCnst.name = cv.cnst.name ∧ isFamily ci = true)
              _ ?_ ?_ _ ?_) cs hcs cv hcv
            · intro v _ s hs
              split
              · exact hs
              · intro cs hcs
                rcases Array.mem_push.mp hcs with hcs | rfl
                · exact hs cs hcs
                · refine forIn_id_prop_array
                    (I := fun s : Option Group × Array Ix.ConstructorVal =>
                      ∀ cv ∈ s.2, ∃ k, (k, Ix.ConstantInfo.ctorInfo cv) ∈ env.consts.toList)
                    (Q := fun t => ∀ cv ∈ t.2, ∃ k, (k, Ix.ConstantInfo.ctorInfo cv) ∈ env.consts.toList)
                    _ ?_ (fun _ h => h) _ ?_
                  · intro y _ s hs
                    split
                    · rename_i cv' hcv'
                      split
                      · split
                        · intro w hw
                          rcases Array.mem_push.mp hw with hw | rfl
                          · exact hs w hw
                          · exact lookup_stored hcv'
                        · exact hs
                      · exact hs
                    · exact hs
                  · intro cv hcv
                    exact absurd hcv (Array.not_mem_empty _)
            · intro t ht cs hcs cv hcv
              obtain ⟨k, hk⟩ := ht cs hcs cv hcv
              exact ⟨k, _, hk, rfl, rfl⟩
            · intro cs hcs
              exact absurd hcs (Array.not_mem_empty _)
        · obtain ⟨r, hr, rfl⟩ := Array.mem_map.mp hx
          obtain ⟨k, hk⟩ := hc r (blockRecursors_mem hrecs r hr)
          exact ⟨k, _, hk, rfl, rfl⟩
      · subst hg
        cases conv

/-- **Every converted group's names are own names of stored constants of its kind.** -/
theorem groupsOf_kinded (env : Ix.Environment) (blocks : Ix.CondensedBlocks) :
    ∀ g ∈ groupsOf env blocks, ∀ c, convert g = .ok c → NamesKinded env g := by
  unfold groupsOf
  simp only [Id.run, Std.HashMap.forIn_eq_forIn_toList, idBind, idPure]
  refine forIn_id_prop (I := fun acc : Array Group => ∀ g ∈ acc, ∀ c, convert g = .ok c → NamesKinded env g)
    _ ?_ (fun _ h => h) _ ?_
  · intro x _ s hs
    split
    · exact hs
    · intro g hg c hc
      rcases Array.mem_push.mp hg with hg | rfl
      · exact hs g hg c hc
      · unfold unplaced at hc
        split at hc <;> cases hc
  · refine forIn_id_prop (I := fun acc : Array Group => ∀ g ∈ acc, ∀ c, convert g = .ok c → NamesKinded env g)
      _ ?_ (fun _ h => h) _ ?_
    · intro x _ s hs
      split
      · rename_i g' hg'
        intro g hg c hc
        rcases Array.mem_push.mp hg with hg | rfl
        · exact hs g hg c hc
        · exact componentGroup_kinded hg'
      · exact hs
    · refine forIn_id_prop
        (I := fun acc : Array Group => ∀ g ∈ acc, ∀ c, convert g = .ok c → NamesKinded env g)
        _ ?_ (fun _ h => h) _ ?_
      · intro x _ s hs
        split
        · split
          · intro g hg c hc
            rcases Array.mem_push.mp hg with hg | rfl
            · exact hs g hg c hc
            · refine inductiveGroup_kinded ?_ hc
              intro r hr
              refine (forIn_id_prop
                (I := fun m : Ix.Map TableName (Array Ix.RecursorVal) =>
                  ∀ key, ∀ r ∈ m.getD key #[], ∃ k, (k, Ix.ConstantInfo.recInfo r) ∈ env.consts.toList)
                (Q := fun m => ∀ r ∈ m.getD x.fst #[],
                  ∃ k, (k, Ix.ConstantInfo.recInfo r) ∈ env.consts.toList)
                _ ?_ (fun t ht => ht x.fst) _ ?_) r hr
              · intro y hy m hm
                split
                · rename_i rv hrv
                  split
                  · intro key r' hr'
                    simp only [ForInStep.value] at hr'
                    rw [Std.HashMap.getD_insert] at hr'
                    split at hr'
                    · rcases Array.mem_push.mp hr' with hr' | rfl
                      · exact hm _ r' hr'
                      · obtain ⟨a, b⟩ := y
                        simp only at hrv
                        subst hrv
                        exact ⟨a, hy⟩
                    · exact hm key r' hr'
                  · exact hm
                · exact hm
              · intro key r' hr'
                simp at hr'
          · exact hs
        · exact hs
      · intro g hg
        exact absurd hg (Array.not_mem_empty _)


/-- **A definitions group converts each member at its own kind**: every converted member has
a member's key and the kind `definitionShape` gives that member. -/
theorem convertDefinitions_kinds {members : Array Ix.ConstantInfo} {conv : Converted}
    (ran : convertDefinitions members = .ok conv) :
    ∃ ms : Array DefMember, conv = .definitions ms ∧
      ∀ m ∈ ms, ∃ ci ∈ members, m.cv.name = ingressKey ci.getCnst.name ∧
        ∃ s h, definitionShape ci = some (m.kind, s, h) := by
  unfold convertDefinitions at ran
  obtain ⟨shapes, hshapes, ran⟩ := except_bind_ok.mp ran
  have shapesOf : ∀ x ∈ shapes, x.1 ∈ members ∧ definitionShape x.1 = some x.2.1 := by
    intro x hx
    obtain ⟨ci, hci, hf⟩ := ReaderUnits.forall₂_mem_right (ReaderUnits.array_mapM_ok hshapes) x
      (Array.mem_toList_iff.mpr hx)
    split at hf
    · rename_i s v hs hv
      simp only [pure, Except.pure, Except.ok.injEq] at hf
      subst hf
      exact ⟨Array.mem_toList_iff.mp hci, hs⟩
    · cases hf
  dsimp only at ran
  rcases ReaderUnits.ite_ok ran with ran | ran <;>
    try (split at ran; exact (ReaderUnits.fail_bind ran).elim)
  all_goals
    obtain ⟨ks, -, ran⟩ := except_bind_ok.mp ran
    rcases ReaderUnits.ite_ok ran with ran | ran
    · simp only [pure, Except.pure, Except.ok.injEq] at ran
      subst ran
      refine ⟨_, rfl, fun m hm => ?_⟩
      obtain ⟨⟨⟨ci, ⟨kind, safety, hint⟩, v⟩, j⟩, hx, rfl⟩ := Array.mem_map.mp hm
      obtain ⟨hmem, hshape⟩ := shapesOf _ (Array.fst_mem_of_mem_zipIdx hx)
      exact ⟨ci, hmem, rfl, safety, hint, hshape⟩
    · split at ran
      · rename_i order horder
        simp only [pure, Except.pure, Except.ok.injEq] at ran
        subst ran
        refine ⟨_, rfl, fun m hm => ?_⟩
        obtain ⟨i, hi, rfl⟩ := Array.mem_map.mp hm
        have hlt := ReaderUnits.defOrder_lt horder i hi
        rw [Array.size_map] at hlt
        obtain ⟨⟨⟨ci, ⟨kind, safety, hint⟩, v⟩, j⟩, hx, he⟩ :=
          Array.mem_map.mp (ReaderUnits.getElem!_mem hlt)
        rw [← he]
        obtain ⟨hmem, hshape⟩ := shapesOf _ (Array.fst_mem_of_mem_zipIdx hx)
        exact ⟨ci, hmem, rfl, safety, hint, hshape⟩
      · cases ran

/-- The hint override and the quotient renaming keep a definitions group's members' kinds and
rename their keys. -/
theorem quotient_definitions (ρ : FiberMap) (hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint)
    (ms : Array DefMember) :
    ∃ ms', ((Converted.definitions ms).withHints hints).quotient ρ = .definitions ms' ∧
      ∀ m ∈ ms', ∃ m₀ ∈ ms, m.kind = m₀.kind ∧ m.cv.name = Key.subst ρ m₀.cv.name := by
  refine ⟨_, rfl, fun m hm => ?_⟩
  simp only [Array.map_map] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := Array.mem_map.mp hm
  refine ⟨m₀, hm₀, ?_, ?_⟩
  · simp only [Function.comp_def, RecordReadings.defMember_canon, DefMember.substKeys]
    split <;> rfl
  · simp only [Function.comp_def, RecordReadings.defMember_canon, DefMember.substKeys,
      ConstantVal.substKeys]
    split <;> rfl

/-- A definition member's declaration declares the member's key, and is a definition when
the member's kind is. -/
theorem lowerDefinition_kind {hint : Option Ix.Kernel.ReducibilityHint} {st : State .source}
    {heights : Ix.Kernel.Reader.CName .source → Nat} {cv : Ix.Kernel.Reader.CVal .source}
    {value : Ix.Kernel.Reader.CExpr .source} {kind : Ix.DefKind} {safety : Ix.DefinitionSafety}
    {decl : Ix.Kernel.Reader.CDecl .source} {rw : Bool}
    (h : Ix.Kernel.Reader.lowerDefinition hint st heights cv value kind safety = .ok (decl, rw)) :
    decl.names = [cv.name] ∧ (kind = .defn → ∃ cv' value' hint', decl = .defnDecl cv' value' hint') := by
  refine ⟨ReaderUnits.lowerDefinition_names h, fun hk => ?_⟩
  subst hk
  unfold Ix.Kernel.Reader.lowerDefinition at h
  dsimp only at h
  split at h
  · simp [Ix.Kernel.Reader.declined, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨_, _, _, rfl⟩

/-- **A definitions group lowers each member to one declaration of the member's key**, a
definition when the member's kind is. -/
theorem lower_definitions_kinds {st : State .source} {ms : Array DefMember} {raw : Read .source}
    (h : lower st (.definitions ms) = .ok raw) :
    ∀ d ∈ raw.decls.toList, ∃ m ∈ ms, d.names = [m.cv.name] ∧
      (m.kind = .defn → ∃ cv value hint, d = .defnDecl cv value hint) := by
  unfold lower at h
  delta Ix.LeanIngress.lower.match_6 at h
  dsimp only at h
  split at h
  · rename_i hsz
    obtain ⟨l⟩ := ms
    obtain _ | ⟨m, _ | ⟨_, _⟩⟩ := l
    · cases hsz
    · simp only at h
      obtain ⟨⟨decl, rw⟩, hd, h⟩ := except_bind_ok.mp h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      intro d hd'
      simp at hd'
      subst hd'
      obtain ⟨hn, hdef⟩ := lowerDefinition_kind hd
      exact ⟨m, by simp, hn, hdef⟩
    · simp at hsz
  · obtain ⟨s, hs, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have pushed := ReaderUnits.forIn_pushes (fun s => s.2.1)
      (fun d => ∃ m ∈ ms, d.names = [m.cv.name] ∧ (m.kind = .defn → ∃ cv value hint, d = .defnDecl cv value hint))
      _ _
      (fun m hm s q hq => by
        obtain ⟨⟨decl, rw⟩, hd, hq⟩ := except_bind_ok.mp hq
        obtain ⟨hn, hdef⟩ := lowerDefinition_kind hd
        dsimp only at hq
        split at hq <;> split at hq <;>
        · simp only [pure, Except.pure, Except.ok.injEq] at hq
          subst hq
          refine ⟨_, rfl, fun e he => ?_⟩
          rcases Array.mem_push.mp he with he | rfl
          · exact .inl he
          · exact .inr ⟨m, Array.mem_def.mpr hm, hn, hdef⟩)
      (fun e he => by simp at he) hs
    exact fun d hd => pushed d (Array.mem_def.mpr hd)

/-- No role with an `ops` specification is a prelude role. -/
theorem ops_not_prelude (r : Ix.Kernel.Role) (h : (Ix.Kernel.Role.spec (md := .anon) r).kind = .ops) :
    r ∉ Ix.Kernel.preludeShape.flatten := by
  revert h
  cases r <;> decide

/-- **Quotient Source declares an `ops` role's key only by a definition**, when every closure
name with that key is an input definition. A prelude declaration names only prelude roles. A
lowered declaration naming the key names a group name's key: an inductive, axiom or quotient
group's names are stored constants of the group's kind (`groupsOf_kinded`), so not
definitions; a definitions group lowers each member at its own kind
(`convertDefinitions_kinds`, `quotient_definitions`, `lower_definitions_kinds`). -/
theorem stream_defn {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ) {pre : Ix.Kernel.Reader.Prelude .source}
    {ds : Array (Ix.Kernel.Declaration .source)} (hpre : Ix.Kernel.Reader.builtinPrelude = .ok pre)
    (hprep : Ix.LeanIngress.prepareSourceCollapsedAt ixe t ((Ix.LeanIngress.fiberHintsMap ixe)[·]?) pre sub
      (blocksOf sub) = .ok ds)
    {d : Ix.Kernel.Declaration .source} (hd : d ∈ ds.toList) {r : Ix.Kernel.Role}
    (hspec : (Ix.Kernel.Role.spec (md := .anon) r).kind = .ops)
    (hk : (Ix.Kernel.Key.role r : Ix.Kernel.Key .source) ∈ d.names)
    (defns : ∀ m ci, (m, ci) ∈ sub.consts.toList → quotientKey ixe t m = .role r → ∃ v, ci = .defnInfo v) :
    ∃ cv value hint, d = .defnDecl cv value hint := by
  have hcol := SourceDeclares.preparedAt_collapsed hprep
  obtain ⟨fin, decls, hl, -, hds⟩ := Ix.LeanIngress.prepareSourceCollapsed_keepsPrelude hcol
  obtain ⟨extra, hextra, perm⟩ := Ix.Kernel.Frontend.preparePrelude_perm pre.ix decls
  rw [hds] at hd
  -- a stored closure constant under a name is the constant at that name
  have named : ∀ k ci, (k, ci) ∈ sub.consts.toList → (ci.getCnst.name, ci) ∈ sub.consts.toList := by
    intro k ci hk
    have := inputsNamed P.compiled k ci (SourceStoredNames.stored_input P hk)
    rw [this]
    exact hk
  rcases List.mem_append.mp (perm.mem_iff.mp hd) with hd | hd
  · obtain ⟨rs, s', kb, ht, -, -, hdecls⟩ := SourcePrelude.lowerAllCollapsed_trace hl
    rw [hdecls] at hd
    obtain ⟨rd, hr, hdr⟩ := List.mem_flatMap.mp hd
    obtain ⟨x, hx, conv, st', raw, hc, hlow, hsub⟩ := trace_reads ht rd hr
    have hdraw := hsub d hdr
    obtain ⟨gr, c, hgr, hconv, heq⟩ := scheduled_conversion hx hc
    have hg : gr ∈ groupsOf sub (blocksOf sub) := Array.mem_of_getElem? hgr
    have kinded := groupsOf_kinded sub _ gr hg c hconv
    by_cases hdef : ∃ members, gr = .definitions members
    · obtain ⟨members, rfl⟩ := hdef
      obtain ⟨ms, rfl, hms⟩ := convertDefinitions_kinds hconv
      obtain ⟨ms', hconvq, hkind'⟩ := quotient_definitions (fiberAliasAt ixe (roleAtMap t))
        ((fiberHintsMap ixe)[·]?) ms
      rw [heq, hconvq] at hlow
      obtain ⟨m, hm, hnames, hdefn⟩ := lower_definitions_kinds hlow d hdraw
      rw [hnames, List.mem_singleton] at hk
      obtain ⟨m₀, hm₀, hkm, hname₀⟩ := hkind' m hm
      obtain ⟨ci, hci, hcin, s, h, hshape⟩ := hms m₀ hm₀
      obtain ⟨k, hkci⟩ := kinded.2 members rfl ci hci
      have hq : quotientKey ixe t ci.getCnst.name = .role r := by
        rw [hk, hname₀, hcin]
        rfl
      obtain ⟨v, rfl⟩ := defns _ ci (named k ci hkci) hq
      simp only [definitionShape, Option.some.injEq, Prod.mk.injEq] at hshape
      exact hdefn (hkm.trans hshape.1.symm)
    · exfalso
      obtain ⟨n₀, hn₀, hq⟩ := lowered_keys hx hc hlow d hdraw (.role r) hk rfl
      have hnames : namesAt (quotientGraph ixe t ((fiberHintsMap ixe)[·]?) sub) x = gr.names := by
        unfold namesAt
        rw [getElem!_of_getElem? hgr]
      rw [hnames] at hn₀
      obtain ⟨k, ci, hkci, hname, hkind⟩ := kinded.1 n₀ hn₀
      have hsub' : (n₀, ci) ∈ sub.consts.toList := by
        have := named k ci hkci
        rw [hname] at this
        exact this
      obtain ⟨v, rfl⟩ := defns n₀ ci hsub' hq.symm
      cases gr with
      | definitions ms => exact hdef ⟨ms, rfl⟩
      | «inductive» _ _ _ => cases hkind
      | «axiom» _ => cases hkind
      | quot _ => cases hkind
      | invalid _ _ => cases hconv
  · have hp := hextra d hd
    have shape := SourceInstalls.builtinPrelude_shape hpre
    have hm : d.names ∈ pre.ix.decls.toList.map (·.names) := List.mem_map.mpr ⟨d, hp, rfl⟩
    rw [shape] at hm
    obtain ⟨rs, hrs, hnr⟩ := List.mem_map.mp hm
    rw [← hnr] at hk
    obtain ⟨s', hs', he⟩ := List.mem_map.mp hk
    cases he
    exact absurd (List.mem_flatten.mpr ⟨rs, hrs, hs'⟩) (ops_not_prelude r hspec)

/-- A claimed record is stored and decodes. -/
theorem claimed_record {env sub : Ix.Environment} {ixe : Ixon.Env} {n : Ix.Name} {A : Address}
    (claimed : ClaimedIn env sub ixe n A) : ∃ c, recordAt ixe A = some c := by
  obtain ⟨cenv, all, k, res, cst, bytes, -, -, -, hr, hclaim, hstored, hblock⟩ := claimed
  have shape := BlockLayout.runBlock_shape hr
  have wire := BlockWire.blocksWire _ _ _ _ _ hr
  unfold Resolution.claimWrites at hclaim
  split at hclaim
  · simp only [List.mem_toArray, List.mem_singleton, Prod.mk.injEq] at hclaim
    obtain ⟨-, rfl, rfl⟩ := hclaim
    rw [shape.bytes] at hblock
    exact ⟨_, BlockLayout.recordAt_ser wire hblock⟩
  · obtain ⟨q, hq, e⟩ := Array.mem_map.mp hclaim
    simp only [Prod.mk.injEq] at e
    obtain ⟨-, rfl, rfl⟩ := e
    rcases shape.rows q hq with same | proj
    · exact ⟨_, BlockLayout.recordAt_ser (by rw [same]; exact wire) hstored⟩
    · exact ⟨_, BlockLayout.recordAt_ser proj.1 hstored⟩

/-- **Quotient Source declares an `ops` role's key only by a definition** (`OpsDeclared`), from
the role's record kind (`RoleRecordKinds`) and the closure names' claims (`ClaimedIn`): every
closure name with the key sits at the role's address, whose record is a standalone definition
of kind `defn`, so it is an input definition (`claimed_definition`), and the stream declares
the key by a definition (`stream_defn`). -/
theorem opsDeclared_of {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ) (kinds : RoleRecordKinds ixe)
    (claimed : ∀ m ci, (m, ci) ∈ sub.consts.toList → ∀ a, ClosureLayout.addrOf ixe m = some a →
      ClaimedIn env sub ixe m a) :
    ∀ pre ds, Ix.Kernel.Reader.builtinPrelude = .ok pre →
      Ix.LeanIngress.prepareSourceCollapsedAt ixe t ((Ix.LeanIngress.fiberHintsMap ixe)[·]?) pre sub
        (blocksOf sub) = .ok ds → OpsDeclared ds.toList := by
  intro pre ds hpre hprep d hd r hspec hk
  refine stream_defn P hpre hprep hd hspec hk fun m ci hm hq => ?_
  have checked := defaultTable_check P.table
  obtain ⟨named, hmem, hget⟩ := SourceStoredNames.stored_published P hm
  have hp := role_published checked P.bound P.agree hmem hq
  have hA : ClosureLayout.addrOf ixe m = some named.addr := by
    unfold ClosureLayout.addrOf
    rw [hget]
    rfl
  have hcl := claimed m ci hm _ hA
  obtain ⟨c, hc⟩ := claimed_record hcl
  obtain ⟨d', hd', hk'⟩ := (kinds t P.table r _ c hp hc).1 hspec
  obtain ⟨v, hv⟩ := claimed_definition P.compiled hcl hc hd' hk'
  have henv := P.source.1.mem_env (SourceStoredNames.stored_get hm)
  rw [hv] at henv
  cases henv
  exact ⟨v, rfl⟩
end SourceKinds

/-! ## Ground edges, from the claims -/

/-- **`Layout.extra` for ground edges, from the compile's claims**: `ground_extra` with its
stream premise discharged (`opsDeclared_of`) and its block premise read off `ClaimedIn`, the
claims of the closure's names. -/
theorem ground_extra_of {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ) (kinds : RoleRecordKinds ixe)
    (claimed : ∀ m ci, (m, ci) ∈ sub.consts.toList → ∀ a, addrOf ixe m = some a → ClaimedIn env sub ixe m a)
    (hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint) :
    ∀ (i : Nat) (gr : Group), (quotientGraph ixe t hints sub).groups[i]? = some gr → ∀ n ∈ gr.names,
      ∀ a ∈ nameRecords ixe n, ∀ (b : Address) (t' : Ix.Kernel.RoleTable), Ix.Kernel.Reader.defaultTable = .ok t' →
        ∀ (s r : Ix.Kernel.Role) (p : Address), t'.addressOf? s = some b → t'.addressOf? r = some p →
          s ∈ groundRoles r → (p = a ∨ ∃ c, recordAt ixe p = some c ∧ ownerOf p c = a) →
            ∃ (j : Nat) (gr' : Group), (quotientGraph ixe t hints sub).groups[j]? = some gr' ∧
              ∃ m ∈ gr'.names, b ∈ nameRecords ixe m :=
  ground_extra P kinds (opsDeclared_of P kinds claimed) hints fun _ _ hgr n hn a ha => by
    obtain ⟨ci, hci⟩ := groupName_stored P hgr hn
    exact (claimed n ci hci a ha).claimedAt

/-! ## Literal edges -/

section Literals

open Ix.CompileM Ix.CompileCert

/-- The input name `literalSupport` gives a literal-support role (`supportNames`' spelling). -/
def literalRoleName (s : Ix.Kernel.Role) : Ix.Name :=
  Ix.Name.fromLeanName (Ix.RoleEvidence.toLeanName (Ix.Kernel.Key.role s : Ix.Kernel.Key .source))

/-- **A stored literal-support role's record is its name's**, under the default role table:
when the artifact stores a record at the address of a role a literal is checked against (the
`Nat` basis and the string support, `Ix.Kernel.Reader.strLitSupportNames`), that role's name
is an input constant published at that address. Every other address, and every unbound role,
is unconstrained. -/
def LiteralRolesNamed (env : Ix.Environment) (ixe : Ixon.Env) : Prop :=
  ∀ t, Ix.Kernel.Reader.defaultTable = .ok t →
    ∀ s ∈ keyRoles (Ix.Kernel.Reader.strLitSupportNames : List (Ix.Kernel.Key .anon)), ∀ b,
      t.addressOf? s = some b → ixe.consts.contains b = true →
        env.consts.contains (literalRoleName s) = true ∧ addrOf ixe (literalRoleName s) = some b

/-- A role among a list's keys is one of its keys. -/
theorem role_of_keyRoles {md : Ix.Kernel.Mode} {L : List (Ix.Kernel.Key md)} {s : Ix.Kernel.Role}
    (h : s ∈ keyRoles L) : (Ix.Kernel.Key.role s : Ix.Kernel.Key md) ∈ L := by
  unfold keyRoles at h
  obtain ⟨k, hk, e⟩ := List.mem_filterMap.mp h
  cases k with
  | role r =>
    simp only [Option.some.injEq] at e
    subst e
    exact hk
  | _ => simp at e

/-- A support role's name is among the support names. -/
theorem supportNames_contains {L : List (Ix.Kernel.Key .source)} {s : Ix.Kernel.Role}
    (h : (Ix.Kernel.Key.role s : Ix.Kernel.Key .source) ∈ L) :
    (supportNames L).contains (literalRoleName s) = true :=
  Array.contains_iff_exists_mem_beq.mpr ⟨literalRoleName s,
    Array.mem_map.mpr ⟨_, by simpa using h, rfl⟩,
    show ((literalRoleName s).getHash == (literalRoleName s).getHash) = true from beq_self_eq_true _⟩

/-- **A constant with a literal of a kind depends on the roles that kind is checked against**,
by name (`literalSupport`). -/
theorem support_contains {ci : Ix.ConstantInfo} {e : Ix.Expr} (he : e ∈ termsOf ci) (k : Bool)
    {s : Ix.Kernel.Role} (hk : LiteralSources.hasK k e = true)
    (hs : s ∈ keyRoles (if k then (Ix.Kernel.Reader.strLitSupportNames : List (Ix.Kernel.Key .anon))
      else Ix.Kernel.Reader.natLitSupportNames)) :
    (literalSupport ci).contains (literalRoleName s) = true := by
  have hany : ∀ (f : Ix.Expr → Bool), f e = true → (termsOf ci).any f = true :=
    fun f hf => List.any_eq_true.mpr ⟨e, he, hf⟩
  have nat_str : ∀ x, x ∈ (Ix.Kernel.Reader.natLitSupportNames : List (Ix.Kernel.Key .source)) →
      x ∈ (Ix.Kernel.Reader.strLitSupportNames : List (Ix.Kernel.Key .source)) :=
    fun x hx => List.mem_append_left _ hx
  cases k
  · have hrole : (Ix.Kernel.Key.role s : Ix.Kernel.Key .source) ∈ Ix.Kernel.Reader.natLitSupportNames :=
      role_of_keyRoles (L := (Ix.Kernel.Reader.natLitSupportNames : List (Ix.Kernel.Key .source))) hs
    unfold literalSupport
    split
    · exact supportNames_contains (nat_str _ hrole)
    · simp only [hany hasNatLit (by simpa [LiteralSources.hasK] using hk), ↓reduceIte]
      exact supportNames_contains hrole
  · have hrole : (Ix.Kernel.Key.role s : Ix.Kernel.Key .source) ∈ Ix.Kernel.Reader.strLitSupportNames :=
      role_of_keyRoles (L := (Ix.Kernel.Reader.strLitSupportNames : List (Ix.Kernel.Key .source))) hs
    unfold literalSupport
    simp only [hany hasStrLit (by simpa [LiteralSources.hasK] using hk), ↓reduceIte]
    exact supportNames_contains hrole

/-- **A record's literal roles come from a literal of one kind**: `literalRoles c` is the
string support's when `c` holds a `String` literal, the `Nat` basis's when it holds only a `Nat`
literal, and empty otherwise. -/
theorem literalRoles_kind {c : Ixon.Constant} {s : Ix.Kernel.Role} (hs : s ∈ literalRoles c) :
    ∃ k, LiteralSources.kindOf k (Ix.Kernel.Reader.literalKinds c) = true ∧
      s ∈ keyRoles (if k then (Ix.Kernel.Reader.strLitSupportNames : List (Ix.Kernel.Key .anon))
        else Ix.Kernel.Reader.natLitSupportNames) := by
  unfold literalRoles at hs
  dsimp only at hs
  split at hs
  · rename_i h2
    exact ⟨true, h2, hs⟩
  · split at hs
    · rename_i _ h1
      exact ⟨false, h1, hs⟩
    · simp [keyRoles] at hs

/-- The support roles of either kind are among the string support's. -/
theorem kind_roles_str {k : Bool} {s : Ix.Kernel.Role}
    (hs : s ∈ keyRoles (if k then (Ix.Kernel.Reader.strLitSupportNames : List (Ix.Kernel.Key .anon))
      else Ix.Kernel.Reader.natLitSupportNames)) :
    s ∈ keyRoles (Ix.Kernel.Reader.strLitSupportNames : List (Ix.Kernel.Key .anon)) := by
  cases k
  · unfold keyRoles at hs ⊢
    exact List.mem_filterMap.mpr (by
      obtain ⟨x, hx, e⟩ := List.mem_filterMap.mp hs
      exact ⟨x, List.mem_append_left _ hx, e⟩)
  · exact hs

/-- **The records of a claimed name are its block's record or bare projections.** -/
theorem claimed_records {ixe : Ixon.Env} {n : Ix.Name} {A : Address} {cenv : CompileEnv}
    {all : Ix.Set Ix.Name} {k : Ix.Name} {r : BlockResult} {cst : BlockState} {bytes : ByteArray}
    (hr : runBlock cenv all k = .ok (r, cst)) (hclaim : (n, A, bytes) ∈ Resolution.claimWrites k r)
    (hstored : ixe.consts.get? A = some { buf := bytes, len := bytes.size })
    (hblock : ixe.consts.get? r.blockAddr = some { buf := r.blockBytes, len := r.blockBytes.size })
    {a : Address} (ha : a = A ∨ a = blockAt ixe A) {c : Ixon.Constant} (hc : recordAt ixe a = some c) :
    c = r.block ∨ Ix.Kernel.Reader.literalKinds c = (false, false) := by
  have shape := BlockLayout.runBlock_shape hr
  have wire := BlockWire.blocksWire _ _ _ _ _ hr
  have blockRec : recordAt ixe r.blockAddr = some r.block := by
    rw [shape.bytes] at hblock
    exact BlockLayout.recordAt_ser wire hblock
  have selfBlock : blockAt ixe r.blockAddr = r.blockAddr := by
    unfold blockAt
    rw [blockRec]
    exact shape.built.owner _
  have key : (recordAt ixe A = some r.block ∧ blockAt ixe A = r.blockAddr) ∨
      ∃ q, recordAt ixe A = some q ∧ blockAt ixe A = r.blockAddr ∧
        Ix.Kernel.Reader.literalKinds q = (false, false) := by
    unfold Resolution.claimWrites at hclaim
    split at hclaim
    · simp only [List.mem_toArray, List.mem_singleton, Prod.mk.injEq] at hclaim
      obtain ⟨-, rfl, rfl⟩ := hclaim
      exact .inl ⟨blockRec, selfBlock⟩
    · obtain ⟨q, hq, e⟩ := Array.mem_map.mp hclaim
      simp only [Prod.mk.injEq] at e
      obtain ⟨-, rfl, rfl⟩ := e
      by_cases same : q.2.1 = r.block
      · rw [same, ← shape.bytes, ← shape.addr]
        exact .inl ⟨blockRec, selfBlock⟩
      · rcases shape.rows q hq with h | ⟨pwire, -, powner⟩
        · exact absurd h same
        have prec := BlockLayout.recordAt_ser pwire hstored
        refine .inr ⟨q.2.1, prec, ?_, (runBlock_rows hr q hq same).2⟩
        unfold blockAt
        rw [prec]
        exact powner _
  rcases ha with rfl | rfl
  · rcases key with ⟨h, -⟩ | ⟨q, h, -, hq⟩
    · rw [h] at hc
      cases hc
      exact .inl rfl
    · rw [h] at hc
      cases hc
      exact .inr hq
  · rcases key with ⟨-, h⟩ | ⟨q, -, h, -⟩
    · rw [h, blockRec] at hc
      cases hc
      exact .inl rfl
    · rw [h, blockRec] at hc
      cases hc
      exact .inl rfl

/-- **A literal role of a claimed block's record is reached by name**: the block's record holds
a literal only where a term its compile reads does (`LiteralSources.runBlock_lits`), that term
is a constant's of the closure (the block's key and members, or a constructor an inductive
member lists), and the constant depends on the role's name (`literalSupport`). -/
theorem literal_reaches {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    (hcl : IsClosure env roots sub) {cenv : CompileEnv} {all : Ix.Set Ix.Name} {k : Ix.Name}
    {r : BlockResult} {cst : BlockState} (henv : ∀ x, cenv.env.get? x = env.consts.get? x)
    (hk : all.contains k = true) (hmembers : MembersIn sub all) (hr : runBlock cenv all k = .ok (r, cst))
    {s : Ix.Kernel.Role} (hs : s ∈ literalRoles r.block) :
    Reaches env roots (literalRoleName s) ∧
      s ∈ keyRoles (Ix.Kernel.Reader.strLitSupportNames : List (Ix.Kernel.Key .anon)) := by
  obtain ⟨kk, hkind, hroles⟩ := literalRoles_kind hs
  refine ⟨?_, kind_roles_str hroles⟩
  obtain ⟨src, ⟨x, hx, ci, hci, hterm⟩, hsrc⟩ := LiteralSources.runBlock_lits hr kk hkind
  have hxsub : ClosureClaims.InSub sub x := by
    have hxa : all.contains x = true := by
      rcases hx with hx | rfl
      · exact hx
      · exact hk
    obtain ⟨ci₀, hci₀⟩ := hmembers x hxa
    unfold ClosureClaims.InSub
    rw [SourceStoredNames.stored_get hci₀]
    rfl
  have hrx := ClosureClaims.reaches_of_sub hcl hxsub
  rw [henv] at hci
  rcases hterm with hterm | ⟨iv, c, cv, rfl, hc, hcv, rfl⟩
  · exact .step hrx ⟨ci, hci, .inr (.inl (support_contains hterm kk hsrc hroles))⟩
  · rw [henv] at hcv
    have hrc : Reaches env roots c := .step hrx ⟨_, hci, .inl (FreshSnapshot.refsOf_induct iv hc)⟩
    exact .step hrc ⟨_, hcv, .inr (.inl (support_contains (by simp [termsOf, Ix.ConstantInfo.getCnst]) kk hsrc
      hroles))⟩

/-- **`Layout.extra` for literal edges**: from a record of a group's name that holds a literal,
the record of a role the literal is checked against is a record of a name of a group.

A group name's records are its block's record or bare projections (`claimed_records`), so the
literal is the block record's. The literal's role is then reached by name (`literal_reaches`),
and that name is an input constant published at the role's address (`LiteralRolesNamed`), so it
is a closure name, which a group holds. -/
theorem literal_extra {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ) (named : LiteralRolesNamed env ixe)
    (claimed : ∀ m ci, (m, ci) ∈ sub.consts.toList → ∀ a, addrOf ixe m = some a → ClaimedIn env sub ixe m a)
    (hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint) :
    ∀ (i : Nat) (gr : Group), (quotientGraph ixe t hints sub).groups[i]? = some gr → ∀ n ∈ gr.names,
      ∀ a ∈ nameRecords ixe n, ∀ (b : Address) (t' : Ix.Kernel.RoleTable), Ix.Kernel.Reader.defaultTable = .ok t' →
        ∀ (s : Ix.Kernel.Role), t'.addressOf? s = some b → ixe.consts.contains b = true →
          ∀ c, recordAt ixe a = some c → s ∈ literalRoles c →
            ∃ (j : Nat) (gr' : Group), (quotientGraph ixe t hints sub).groups[j]? = some gr' ∧
              ∃ m ∈ gr'.names, b ∈ nameRecords ixe m := by
  intro i gr hgr n hn a ha b t' ht' s hsb hcb c hc hs
  have tt : t = t' := by
    rw [P.table] at ht'
    exact Except.ok.inj ht'
  subst tt
  have hcl : IsClosure env roots sub := P.source.1
  obtain ⟨ci, hci⟩ := groupName_stored P hgr hn
  obtain ⟨named', -, hget⟩ := SourceStoredNames.stored_published P hci
  have hA : addrOf ixe n = some named'.addr := by
    unfold addrOf
    rw [hget]
    rfl
  obtain ⟨cenv, all, k, r, cst, bytes, henv, hk, hmembers, hr, hclaim, hstored, hblock⟩ :=
    claimed n ci hci named'.addr hA
  have ha' : a = named'.addr ∨ a = blockAt ixe named'.addr := by
    simpa [nameRecords, hA] using ha
  rcases claimed_records hr hclaim hstored hblock ha' hc with rfl | bare
  · obtain ⟨hreach, hrole⟩ := literal_reaches hcl henv hk hmembers hr hs
    obtain ⟨hin, haddr⟩ := named t P.table s hrole b hsb hcb
    have hsub : ClosureClaims.InSub sub (literalRoleName s) := ClosureClaims.sub_of_reaches hcl hreach
      (by rw [Std.HashMap.get?_eq_getElem?, ← Std.HashMap.contains_eq_isSome_getElem?]; exact hin)
    obtain ⟨m, cm, hm, hbeq⟩ := stored_key hsub
    obtain ⟨j, gr', hgr', hmg⟩ := name_grouped (ixe := ixe) (t := t) (hints := hints) hm
    refine ⟨j, gr', hgr', m, hmg, ?_⟩
    rw [← nameRecords_congr hbeq]
    simp [nameRecords, haddr]
  · exfalso
    unfold literalRoles at hs
    dsimp only at hs
    rw [bare] at hs
    simp [keyRoles] at hs

/-- **`Layout.extra`**: the ground, literal and recursor edges from a record of a group's name
lead to records of names of groups, given the compile-report checks `RoleRecordKinds`,
`RecursorsOwned` and `LiteralRolesNamed`, and each closure name's claim (`ClaimedIn`). -/
theorem layout_extra {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ) (kinds : RoleRecordKinds ixe)
    (owned : RecursorsOwned env ixe) (named : LiteralRolesNamed env ixe)
    (claimed : ∀ m ci, (m, ci) ∈ sub.consts.toList → ∀ a, addrOf ixe m = some a → ClaimedIn env sub ixe m a)
    (hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint) :
    ∀ (i : Nat) (gr : Group), (quotientGraph ixe t hints sub).groups[i]? = some gr → ∀ n ∈ gr.names,
      ∀ a ∈ nameRecords ixe n, ∀ b, (GroundEdge ixe a b ∨ RecursorEdge ixe a b) →
        ∃ (j : Nat) (gr' : Group), (quotientGraph ixe t hints sub).groups[j]? = some gr' ∧
          ∃ m ∈ gr'.names, b ∈ nameRecords ixe m := by
  intro i gr hgr n hn a ha b hedge
  rcases hedge with ⟨hcb, t', ht', s, hsb, ⟨r, p, hrp, hs, hpa⟩ | ⟨c, hc, hs⟩⟩ | hrec
  · exact ground_extra_of P kinds claimed hints i gr hgr n hn a ha b t' ht' s r p hsb hrp hs hpa
  · exact literal_extra P named claimed hints i gr hgr n hn a ha b t' ht' s hsb hcb c hc hs
  · exact recursor_extra P owned hints i gr hgr n hn a ha b hrec

end Literals

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

/--
info: 'Ix.Cert.LayoutExtra.opsDeclared_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Cert.LayoutExtra.opsDeclared_of

/--
info: 'Ix.Cert.LayoutExtra.ground_extra_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Cert.LayoutExtra.ground_extra_of

/--
info: 'Ix.Cert.LayoutExtra.literal_extra' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Cert.LayoutExtra.literal_extra

/--
info: 'Ix.Cert.LayoutExtra.layout_extra' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Cert.LayoutExtra.layout_extra
