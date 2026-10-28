import Ix.Cert.CompiledRefs
import Ix.Cert.LayoutExtra

/-! # A closure group's names are its compile block's members

Quotient Source groups the closure `sub` by the condensation of its own grounded reference
graph (`blocksOf sub`); the compiler compiles the input by the condensation of the input's
(`CompiledRefs.envBlocks env`). Along closure names the two graphs agree (`path_transfer`), so a
closure name's two blocks have the same members (`block_agree`), when the schedule places every
closure name in a block of the closure's condensation (`scheduled`, `CompiledRefs.placed`):

* every closure name is a node of the input's grounded graph (`env_node`): the compile reports
  the ground filter's constants as failed, and no closure name fails;
* a closure name that is no constructor is a member of a block of the input's condensation
  (`member_of_claim`): its published record is a claim of a block the fold compiled, and the
  block's claims are its members' names or its inductives' constructors' (`Claims.compileBlock_names`).

A definitions, axiom or quotient group is the component group of a block of the closure's
condensation (`component_of_groups`), with no family constant (`component_names`). Its names
are then the names of the input's constants in the compile's block of any of its names
(`group_names`). For a definitions group these are the members the block's loop reads
(`loop_definitions`, `definitions_members`), one definition per class in Lean's order
(`definitions_defs`); a single-name group's block holds only that name (`single_block`). -/

namespace Ix.Cert.GroupBlocks

open Ix.CompileM Ix.Cert.Resolution Ix.Cert.Schedule
open Ix.Cert.Condense (Path)
open Ix.LeanIngress (Graph Group scheduleOf groupsOf componentGroup componentGroupUsing isFamily isDefinition)
open Ix.Cert.ClosureLayout (addrOf quotientGraph)
open Ix.CompileCert.Loop (idBind idPure)

/-! ## Closure names are nodes of the input's grounded graph -/

/-- An inserting fold holds every key it inserts, and every key of its start. -/
theorem foldl_insert_contains {β γ : Type} (f : Ix.Name × γ → β) :
    ∀ (l : List (Ix.Name × γ)) (m : Std.HashMap Ix.Name β) (k : Ix.Name),
      (m.contains k = true ∨ ∃ p ∈ l, (p.1 == k) = true) →
        (l.foldl (fun b a => b.insert a.1 (f a)) m).contains k = true
  | [], m, k, h => by
    rcases h with h | ⟨p, hp, -⟩
    · exact h
    · cases hp
  | p :: l, m, k, h => by
    rw [List.foldl_cons]
    apply foldl_insert_contains f l _ k
    rcases h with h | ⟨q, hq, e⟩
    · left
      rw [Std.HashMap.contains_insert, h, Bool.or_true]
    · rcases List.mem_cons.mp hq with rfl | hq
      · left
        rw [Std.HashMap.contains_insert, e, Bool.true_or]
      · exact .inr ⟨q, hq, e⟩

/-- A skipping, inserting fold holds every key it does not skip. -/
theorem foldl_skip_contains {β γ : Type} (skip : Ix.Name → Bool) (f : Ix.Name × γ → β)
    (congr : ∀ a b, (a == b) = true → skip a = skip b) :
    ∀ (l : List (Ix.Name × γ)) (m : Std.HashMap Ix.Name β) (k : Ix.Name), skip k = false →
      (m.contains k = true ∨ ∃ p ∈ l, (p.1 == k) = true) →
        (l.foldl (fun b a => if skip a.1 then b else b.insert a.1 (f a)) m).contains k = true
  | [], m, k, _, h => by
    rcases h with h | ⟨p, hp, -⟩
    · exact h
    · cases hp
  | p :: l, m, k, hk, h => by
    rw [List.foldl_cons]
    apply foldl_skip_contains skip f congr l _ k hk
    rcases h with h | ⟨q, hq, e⟩
    · left
      split
      · exact h
      · rw [Std.HashMap.contains_insert, h, Bool.or_true]
    · rcases List.mem_cons.mp hq with rfl | hq
      · left
        have hs : skip q.1 = false := by rw [congr _ _ e]; exact hk
        simp only [hs, Bool.false_eq_true, ↓reduceIte]
        rw [Std.HashMap.contains_insert, e, Bool.true_or]
      · exact .inr ⟨q, hq, e⟩

/-- A key of a map's entries list. -/
theorem entry_of_contains {β : Type} {m : Std.HashMap Ix.Name β} {k : Ix.Name} (h : m.contains k = true) :
    ∃ p ∈ m.toList, (p.1 == k) = true := by
  rw [Std.HashMap.contains_eq_isSome_getElem?] at h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  rw [Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList] at hv
  obtain ⟨k', e, hm⟩ := hv
  exact ⟨(k', v), hm, BEq.symm e⟩

/-- **The reference map holds every input constant.** -/
theorem envSerial_contains {E : Ix.Environment} {x : Ix.Name} (h : E.consts.contains x = true) :
    (Ix.GraphM.envSerial E).contains x = true := by
  unfold Ix.GraphM.envSerial
  simp only [Id.run, Std.HashMap.forIn_eq_forIn_toList, List.forIn_pure_yield_eq_foldl]
  exact foldl_insert_contains _ _ _ _ (.inr (entry_of_contains h))

/-- **The ground split keeps every constant the ground filter does not remove.** -/
theorem groundSplit_node {E : Ix.Environment} {x : Ix.Name} (hs : E.consts.contains x = true)
    (hu : (groundSplit E).2.contains x = false) : (groundSplit E).1.contains x = true := by
  have hser := envSerial_contains hs
  unfold groundSplit at hu ⊢
  dsimp only at hu ⊢
  split
  · exact hser
  · rename_i hne
    simp only [hne] at hu
    rw [Std.HashMap.fold_eq_foldl_toList]
    exact foldl_skip_contains _ _ (fun a b e => Std.HashMap.contains_congr e) _ _ _ hu
      (.inr (entry_of_contains hser))

/-- **The compile reports the ground filter's constants as failed.** -/
theorem ungrounded_failed {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    {cenv : CompileEnv} (hu : compileUnchecked env = .ok (ixe, failures, cenv)) {x : Ix.Name}
    (h : (groundSplit { consts := env.consts }).2.contains x = true) : failures.failed x = true := by
  unfold compileUnchecked at hu
  simp only [bind, Except.bind, pure, Except.pure] at hu
  split at hu
  · cases hu
  · rename_i r _
    obtain ⟨ixe', bytes, cenv'⟩ := r
    simp only [Except.ok.injEq, Prod.mk.injEq] at hu
    obtain ⟨-, rfl, -⟩ := hu
    unfold Failures.failed
    rw [Bool.or_eq_true]
    left
    dsimp only
    rw [Std.HashMap.fold_eq_foldl_toList]
    exact foldl_insert_contains _ _ _ _ (.inr (entry_of_contains h))

/-- **Every closure name is a node of the input's grounded graph**: no closure name fails, and
the compile reports the ground filter's constants as failed. -/
theorem env_node {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ) {x : Ix.Name} (hx : (sub.consts.get? x).isSome = true) :
    (groundSplit { consts := env.consts }).1.contains x = true := by
  have hcl : IsClosure env roots sub := P.source.1
  obtain ⟨cenv, hu, -⟩ := Ix.Cert.compileReport_ok P.compiled
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hx
  have hin : ({ consts := env.consts } : Ix.Environment).consts.contains x = true := by
    show env.consts.contains x = true
    rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?,
      ← CompiledRefs.closure_same hcl hx, hci]
    rfl
  refine groundSplit_node hin ?_
  cases hg : (groundSplit { consts := env.consts }).2.contains x
  · rfl
  · have failed := ungrounded_failed hu hg
    rw [P.none x ci hci] at failed
    cases failed

/-- **Every closure name is a node of the closure's grounded graph**, under the schedule. -/
theorem sub_node {ixe : Ixon.Env} {t : Ix.Kernel.RoleTable}
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint} {sub : Ix.Environment}
    (scheduled : ∀ x ∈ (scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList, ∃ conv, x.1.2 = .ok conv)
    {x : Ix.Name} (hx : (sub.consts.get? x).isSome = true) : (groundSplit sub).1.contains x = true := by
  obtain ⟨lo, all, -, hall, hxa⟩ := CompiledRefs.placed scheduled hx
  exact CompiledRefs.key_of_member hall hxa

/-! ## A closure name's two blocks -/

/-- **A closure name's block of the input's condensation and its block of the closure's have the
same members**: the input's block's members are in the closure's, and the closure's members
that are in some block of the input's condensation are in the input's block. Members of a block
reach each other (`Condense.condense_scc`), the paths stay in the closure and transfer between
the two graphs (`path_transfer`), and mutually reachable members share a block (`same_block`). -/
theorem block_agree {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ)
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint}
    (scheduled : ∀ x ∈ (scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList, ∃ conv, x.1.2 = .ok conv)
    {n : Ix.Name} (hn : (sub.consts.get? n).isSome = true)
    {repE : Ix.Name} {allE : Ix.Set Ix.Name} (hE : (CompiledRefs.envBlocks env).blocks.get? repE = some allE)
    (hnE : allE.contains n = true)
    {repS : Ix.Name} {allS : Ix.Set Ix.Name} (hS : (blocksOf sub).blocks.get? repS = some allS)
    (hnS : allS.contains n = true) :
    (∀ x, allE.contains x = true → allS.contains x = true) ∧
      ∀ x, allS.contains x = true → FreshSnapshot.Member (CompiledRefs.envBlocks env) x →
        allE.contains x = true := by
  have hcl : IsClosure env roots sub := P.source.1
  refine ⟨fun x hx => ?_, fun x hx hmem => ?_⟩
  · have p₁ := Condense.condense_scc hE hnE hx
    have p₂ := Condense.condense_scc hE hx hnE
    have hxs := Condense.closure_path hcl p₁ hn
    have transfer := fun {a b : Ix.Name} (p : Path (groundSplit { consts := env.consts }).1 a b)
        (ha : (sub.consts.get? a).isSome = true) =>
      CompiledRefs.path_transfer (E₁ := { consts := env.consts }) (E₂ := sub)
        (fun z => (sub.consts.get? z).isSome = true) (CompiledRefs.closure_closed_env hcl)
        (fun z hz => sub_node scheduled hz) (fun z hz => CompiledRefs.closure_same hcl hz) p ha
    obtain ⟨lo, allx, -, hallx, hxallx⟩ := CompiledRefs.placed scheduled hxs
    exact CompiledRefs.same_block hS hnS hallx hxallx (transfer p₁ hn) (transfer p₂ hxs)
  · have p₁ := Condense.condense_scc hS hnS hx
    have p₂ := Condense.condense_scc hS hx hnS
    have hxs : (sub.consts.get? x).isSome = true := by
      have hk := CompiledRefs.key_of_member hS hx
      exact CompiledRefs.node_const (by
        rw [Std.HashMap.get?_eq_getElem?, ← Std.HashMap.contains_eq_isSome_getElem?]; exact hk)
    have transfer := fun {a b : Ix.Name} (p : Path (groundSplit sub).1 a b)
        (ha : (sub.consts.get? a).isSome = true) =>
      CompiledRefs.path_transfer (E₁ := sub) (E₂ := { consts := env.consts })
        (fun z => (sub.consts.get? z).isSome = true) CompiledRefs.closure_closed_sub
        (fun z hz => env_node P hz) (fun z hz => (CompiledRefs.closure_same hcl hz).symm) p ha
    obtain ⟨repx, allx, hallx, hxallx⟩ := hmem
    exact CompiledRefs.same_block hE hnE hallx hxallx (transfer p₁ hn) (transfer p₂ hxs)

/-! ## A claimed name that is no constructor is a member of its block -/

/-- **A block's claim of a name that is no constructor is a member's**: the block's key, or a
row name, which names a member (`Claims.compileBlock_names`); a constructor's row names a
constructor. -/
theorem claim_member {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (compiled : compileReport env = .ok (ixe, failures)) {cenv : CompileEnv}
    (henv : ∀ x, cenv.env.get? x = env.consts.get? x) {all : Ix.Set Ix.Name} {key : Ix.Name}
    (hkey : all.contains key = true) {r : BlockResult} {c : BlockState} (hr : runBlock cenv all key = .ok (r, c))
    {k : Ix.Name} {a : Address} {b : ByteArray} (hclaim : (k, a, b) ∈ Resolution.claimWrites key r)
    (notCtor : ∀ cv, env.consts.get? k ≠ some (.ctorInfo cv)) : all.contains k = true := by
  rcases ClosureClaims.claim_name hclaim with rfl | ⟨row, hrow, e⟩
  · exact hkey
  · have names := Claims.compileBlock_names (Ix.CompileCert.run_success (BlockRecords.runBlock_compiles hr))
      row hrow
    obtain ⟨m, ⟨n', ci, hn', hci, hname, hctors⟩, hx⟩ := names
    rw [henv] at hci
    obtain ⟨k', hk'⟩ := SourceStoredNames.lookup_stored hci
    have hk'name := Ix.Cert.inputsNamed compiled k' ci hk'
    rcases hx with hx | ⟨ctor, hctor, hx⟩
    · -- a member's name: the member's input key
      have hk : k = k' := by rw [← e, hx, hname, hk'name]
      subst hk
      have hbeq : (n' == k) = true := by
        have hfound := hci
        rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList] at hfound
        obtain ⟨k'', e'', hm''⟩ := hfound
        have := Ix.Cert.inputsNamed compiled k'' ci hm''
        rw [hk'name] at this
        rw [← this] at e''
        exact e''
      rw [← Std.HashSet.contains_congr hbeq]
      exact hn'
    · -- a constructor's name: its input key holds the constructor
      exfalso
      obtain ⟨iv, cn, -, -, hcn⟩ := hctors ctor hctor
      rw [henv] at hcn
      obtain ⟨c', hc'⟩ := SourceStoredNames.lookup_stored hcn
      have hc'name := Ix.Cert.inputsNamed compiled c' _ hc'
      have hk : k = c' := by
        rw [← e, hx]
        simpa [Ix.ConstantInfo.getCnst] using hc'name
      subst hk
      exact notCtor ctor (SourceStoredNames.stored_get hc')

/-- **A closure name that is no constructor is a member of a block of the input's
condensation**: its published record is a claim of a block the fold compiled
(`compileReport_owned_block`), of which it is a member (`claim_member`). -/
theorem member_of_claim {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ) {x : Ix.Name} (hx : (sub.consts.get? x).isSome = true)
    (notCtor : ∀ cv, env.consts.get? x ≠ some (.ctorInfo cv)) :
    FreshSnapshot.Member (CompiledRefs.envBlocks env) x := by
  have hcl : IsClosure env roots sub := P.source.1
  obtain ⟨k, ci, hk, hxk⟩ := LayoutExtra.stored_key hx
  obtain ⟨cenv, blocks, cenv₀, sched, hu, hblocks, hrun, -, owned⟩ :=
    Ix.Cert.compileReport_owned_block P.compiled hcl P.none
  obtain ⟨named, hmem, hget⟩ := SourceStoredNames.stored_published P hk
  have hin : env.consts.contains k = true := by
    rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?,
      SourceStoredNames.stored_get (SourceStoredNames.stored_input P hk)]
    rfl
  have hn := LayoutExtra.published_resolved P.compiled hu hmem hget hin
  have hs : (sub.consts.get? k).isSome = true := by
    rw [SourceStoredNames.stored_get hk]
    rfl
  obtain ⟨-, snap, rep, all, r, c, b, hsnap, hall, -, -, hr, hclaim, -, -, -, -, -⟩ :=
    owned k named.addr hn hs
  obtain ⟨-, -, henv, -⟩ := hrun
  have hE : ∀ y, snap.cenv.env.get? y = env.consts.get? y := fun y => by
    rw [reach_env (onRun_reach hsnap), henv, ClosureClaims.view_get, ClosureClaims.input_get]
  subst hblocks
  have notCtor' : ∀ cv, env.consts.get? k ≠ some (.ctorInfo cv) := by
    intro cv h
    apply notCtor cv
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_congr hxk, ← Std.HashMap.get?_eq_getElem?]
    exact h
  have hka := claim_member P.compiled hE (blockKey_mem (Condense.condense_nonempty hall)) hr hclaim notCtor'
  exact ⟨rep, all, hall, by rw [Std.HashSet.contains_congr hxk]; exact hka⟩


/-! ## Quotient Source's component groups -/

/-- A group of a strongly connected component's constants outside the families: definitions,
an axiom or a quotient. -/
def Component : Group → Prop
  | .definitions _ | .axiom _ | .quot _ => True
  | _ => False

/-- An inductive block's group is no component group. -/
theorem inductiveGroup_not_component {E : Ix.Environment} {first : Ix.InductiveVal}
    {cands : Array Ix.RecursorVal} : ¬ Component (Ix.LeanIngress.inductiveGroup E first cands) := by
  generalize hg : Ix.LeanIngress.inductiveGroup E first cands = g
  rw [Ix.Cert.SourceStoredNames.inductive_default] at hg
  unfold Ix.LeanIngress.inductiveGroupUsing at hg
  simp only [Id.run, idBind, idPure] at hg
  split at hg
  · rename_i r hr
    have pend : SourceStoredNames.Pending (some r) := by
      rw [← hr]
      refine SourceStoredNames.forIn_id_prop_array
        (I := fun s : Option Group × Array Ix.InductiveVal => SourceStoredNames.Pending s.1)
        (Q := fun t => SourceStoredNames.Pending t.1) _ ?_ (fun _ h => h) _ (.inl rfl)
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
      exact id
  · split at hg
    · rename_i r hr
      have pend : SourceStoredNames.Pending (some r) := by
        rw [← hr]
        refine SourceStoredNames.forIn_id_prop_array
          (I := fun s : Option Group × Array (Array Ix.ConstructorVal) => SourceStoredNames.Pending s.1)
          (Q := fun t => SourceStoredNames.Pending t.1) _ ?_ (fun _ h => h) _ (.inl rfl)
        intro v _ s _
        split
        · rename_i r' hr'
          show SourceStoredNames.Pending (some r')
          rw [← hr']
          refine SourceStoredNames.forIn_id_prop_array
            (I := fun s : Option Group × Array Ix.ConstructorVal => SourceStoredNames.Pending s.1)
            (Q := fun t => SourceStoredNames.Pending t.1) _ ?_ (fun _ h => h) _ (.inl rfl)
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
        exact id
    · split at hg
      · subst hg
        exact id
      · subst hg
        exact id

/-- **A component group is a block's**: a definitions, axiom or quotient group of quotient
Source is the component group of a block of the condensation. -/
theorem component_of_groups (E : Ix.Environment) (blocks : Ix.CondensedBlocks) :
    ∀ g ∈ groupsOf E blocks, Component g →
      ∃ rep all, blocks.blocks.get? rep = some all ∧ componentGroup E all = some g := by
  unfold groupsOf
  simp only [Id.run, Std.HashMap.forIn_eq_forIn_toList, idBind, idPure]
  refine SourceStoredNames.forIn_id_prop (I := fun acc : Array Group => ∀ g ∈ acc, Component g →
      ∃ rep all, blocks.blocks.get? rep = some all ∧ componentGroup E all = some g) _ ?_ (fun _ h => h) _ ?_
  · intro x _ s hs
    split
    · exact hs
    · intro g hg hc
      rcases Array.mem_push.mp hg with hg | rfl
      · exact hs g hg hc
      · unfold Ix.LeanIngress.unplaced at hc
        split at hc <;> exact hc.elim
  · refine SourceStoredNames.forIn_id_prop (I := fun acc : Array Group => ∀ g ∈ acc, Component g →
        ∃ rep all, blocks.blocks.get? rep = some all ∧ componentGroup E all = some g) _ ?_ (fun _ h => h) _ ?_
    · intro x hx s hs
      split
      · rename_i g' hg'
        intro g hg hc
        rcases Array.mem_push.mp hg with hg | rfl
        · exact hs g hg hc
        · refine ⟨x.1, x.2, ?_, hg'⟩
          rw [Std.HashMap.get?_eq_getElem?]
          exact (Std.HashMap.mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some.mp hx).2
      · exact hs
    · refine SourceStoredNames.forIn_id_prop (I := fun acc : Array Group => ∀ g ∈ acc, Component g →
          ∃ rep all, blocks.blocks.get? rep = some all ∧ componentGroup E all = some g) _ ?_ (fun _ h => h) _ ?_
      · intro x _ s hs
        split
        · split
          · intro g hg hc
            rcases Array.mem_push.mp hg with hg | rfl
            · exact hs g hg hc
            · exact (inductiveGroup_not_component hc).elim
          · exact hs
        · exact hs
      · intro g hg
        exact absurd hg (Array.not_mem_empty _)

/-- **A component group's names are its block's constants' names**, and the block has no family
constant. -/
theorem component_names {E : Ix.Environment} {members : Ix.Set Ix.Name} {g : Group}
    (h : componentGroup E members = some g) (hc : Component g) :
    (∀ x, x ∈ g.names ↔ ∃ k ci, members.contains k = true ∧ E.consts.get? k = some ci ∧ x = ci.getCnst.name) ∧
      (∀ k ci, members.contains k = true → E.consts.get? k = some ci → isFamily ci = false) ∧
      ∀ ms, g = .definitions ms → ∀ k ci, members.contains k = true → E.consts.get? k = some ci →
        isDefinition ci = true := by
  rw [Ix.Cert.SourceStoredNames.component_default] at h
  unfold componentGroupUsing at h
  generalize hcis : (Array.filterMapM (m := Id) (fun x => E.consts.get? x) members.toArray :
    Array Ix.ConstantInfo) = cis at h
  dsimp only [Id.run, bind, pure] at h
  have inCis : ∀ ci, ci ∈ Id.run cis ↔ ∃ k, members.contains k = true ∧ E.consts.get? k = some ci := by
    intro ci
    rw [← hcis]
    show ci ∈ members.toArray.filterMap (fun x => E.consts.get? x) ↔ _
    rw [Array.mem_filterMap]
    constructor
    · rintro ⟨k, hk, e⟩
      exact ⟨k, Std.HashSet.contains_of_mem_toArray hk, e⟩
    · rintro ⟨k, hk, e⟩
      have hk' : members.toArray.contains k = true := by rw [Std.HashSet.contains_toArray]; exact hk
      obtain ⟨k', hk'm, e'⟩ := Array.contains_iff_exists_mem_beq.mp hk'
      refine ⟨k', hk'm, ?_⟩
      rw [Std.HashMap.get?_eq_getElem?, ← Std.HashMap.getElem?_congr e', ← Std.HashMap.get?_eq_getElem?]
      exact e
  generalize hothers : (cis.filter (fun x => !isFamily x)).qsort
    (fun a b => Ix.sourceOrderLt (a.blockPosition, a.getCnst.name)
      (b.blockPosition, b.getCnst.name)) = others at h
  have inOthers : ∀ ci, ci ∈ others ↔ ci ∈ Id.run cis ∧ isFamily ci = false := by
    intro ci
    rw [← hothers, Ix.CompileCert.Canon.mem_qsort, Array.mem_filter]
    show ci ∈ Id.run cis ∧ (!isFamily ci) = true ↔ ci ∈ Id.run cis ∧ isFamily ci = false
    simp
  split at h
  · cases h
  · split at h
    · cases h
      exact hc.elim
    · rename_i hfam
      have nofam : ∀ k ci, members.contains k = true → E.consts.get? k = some ci → isFamily ci = false := by
        intro k ci hk hci
        cases e : isFamily ci
        · rfl
        · exact absurd (Array.any_eq_true'.mpr ⟨ci, (inCis ci).mpr ⟨k, hk, hci⟩, e⟩) hfam
      have names : ∀ x, x ∈ (others.map (·.getCnst.name)) ↔
          ∃ k ci, members.contains k = true ∧ E.consts.get? k = some ci ∧ x = ci.getCnst.name := by
        intro x
        rw [Array.mem_map]
        constructor
        · rintro ⟨ci, hci, rfl⟩
          obtain ⟨k, hk, hkc⟩ := (inCis ci).mp ((inOthers ci).mp hci).1
          exact ⟨k, ci, hk, hkc, rfl⟩
        · rintro ⟨k, ci, hk, hkc, rfl⟩
          exact ⟨ci, (inOthers ci).mpr ⟨(inCis ci).mpr ⟨k, hk, hkc⟩, nofam k ci hk hkc⟩, rfl⟩
      split at h
      · rename_i hall
        cases h
        refine ⟨names, nofam, fun ms _ k ci hk hci => ?_⟩
        exact Array.all_eq_true'.mp hall ci ((inOthers ci).mpr ⟨(inCis ci).mpr ⟨k, hk, hci⟩, nofam k ci hk hci⟩)
      · obtain ⟨l⟩ := others
        rcases l with _ | ⟨c, _ | ⟨c₂, rest⟩⟩
        · cases h
          exact hc.elim
        · cases c <;> cases h
          all_goals first
            | exact hc.elim
            | exact ⟨fun x => by
                rw [← names x]
                simp [Group.names, Ix.ConstantInfo.getCnst], nofam, fun ms hms => by cases hms⟩
        · cases h
          exact hc.elim

/-! ## A component group's names are its compile block's -/

/-- **A component group's names are the names of the input's constants in the compile's block**
of one of its names: the group is a block's of the closure's condensation (`component_of_groups`)
whose constants are no family's, so its members are the compile block's (`block_agree`,
`member_of_claim`). -/
theorem group_names {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ)
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint}
    (scheduled : ∀ x ∈ (scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList, ∃ conv, x.1.2 = .ok conv)
    {i : Nat} {gr : Group} (hgr : (quotientGraph ixe t hints sub).groups[i]? = some gr) (hc : Component gr)
    {repE : Ix.Name} {allE : Ix.Set Ix.Name} (hE : (CompiledRefs.envBlocks env).blocks.get? repE = some allE)
    {n : Ix.Name} (hn : n ∈ gr.names) (hnE : allE.contains n = true) :
    (∀ x, x ∈ gr.names ↔
      ∃ k ci, allE.contains k = true ∧ env.consts.get? k = some ci ∧ x = ci.getCnst.name) ∧
      (∀ k ci, allE.contains k = true → env.consts.get? k = some ci → isFamily ci = false) ∧
      ∀ ms, gr = .definitions ms → ∀ k ci, allE.contains k = true → env.consts.get? k = some ci →
        isDefinition ci = true := by
  have hcl : IsClosure env roots sub := P.source.1
  have hmem : gr ∈ groupsOf sub (blocksOf sub) := Array.mem_of_getElem? hgr
  obtain ⟨repS, allS, hS, hcomp⟩ := component_of_groups sub (blocksOf sub) gr hmem hc
  obtain ⟨names, nofam, defs⟩ := component_names hcomp hc
  -- a member of the closure's block is a closure name, stored under a key that hashes like it
  have inSub : ∀ k, allS.contains k = true → (sub.consts.get? k).isSome = true := fun k hk =>
    CompiledRefs.node_const (by
      rw [Std.HashMap.get?_eq_getElem?, ← Std.HashMap.contains_eq_isSome_getElem?]
      exact CompiledRefs.key_of_member hS hk)
  have named : ∀ k ci, env.consts.get? k = some ci → (k == ci.getCnst.name) = true := by
    intro k ci hci
    have hfound := hci
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList] at hfound
    obtain ⟨k', e', hm'⟩ := hfound
    rw [Ix.Cert.inputsNamed P.compiled k' ci hm']
    exact e'
  -- the group's name is in the closure's block
  obtain ⟨k₀, ci₀, hk₀, hci₀, rfl⟩ := (names n).mp hn
  have hci₀' : env.consts.get? k₀ = some ci₀ := by
    rw [← CompiledRefs.closure_same hcl (inSub k₀ hk₀)]
    exact hci₀
  have hnS : allS.contains ci₀.getCnst.name = true := by
    rw [← Std.HashSet.contains_congr (named k₀ ci₀ hci₀')]
    exact hk₀
  have hns : (sub.consts.get? ci₀.getCnst.name).isSome = true := by
    rw [Std.HashMap.get?_eq_getElem?, ← Std.HashMap.getElem?_congr (named k₀ ci₀ hci₀'),
      ← Std.HashMap.get?_eq_getElem?]
    exact inSub k₀ hk₀
  obtain ⟨toS, toE⟩ := block_agree P scheduled hns hE hnE hS hnS
  have famE : ∀ k ci, allE.contains k = true → env.consts.get? k = some ci → isFamily ci = false := by
    intro k ci hk hci
    have hkS := toS k hk
    rw [← CompiledRefs.closure_same hcl (inSub k hkS)] at hci
    exact nofam k ci hkS hci
  have defE : ∀ ms, gr = .definitions ms → ∀ k ci, allE.contains k = true → env.consts.get? k = some ci →
      isDefinition ci = true := by
    intro ms hms k ci hk hci
    have hkS := toS k hk
    rw [← CompiledRefs.closure_same hcl (inSub k hkS)] at hci
    exact defs ms hms k ci hkS hci
  refine ⟨fun x => ?_, famE, defE⟩
  rw [names x]
  constructor
  · rintro ⟨k, ci, hk, hci, rfl⟩
    have hci' : env.consts.get? k = some ci := by
      rw [← CompiledRefs.closure_same hcl (inSub k hk)]
      exact hci
    have notCtor : ∀ cv, env.consts.get? k ≠ some (.ctorInfo cv) := by
      intro cv h
      rw [h] at hci'
      cases hci'
      have := nofam k _ hk hci
      simp [isFamily] at this
    exact ⟨k, ci, toE k hk (member_of_claim P (inSub k hk) notCtor), hci', rfl⟩
  · rintro ⟨k, ci, hk, hci, rfl⟩
    have hkS := toS k hk
    refine ⟨k, ci, hkS, ?_, rfl⟩
    rw [CompiledRefs.closure_same hcl (inSub k hkS)]
    exact hci

/-! ## The per-kind forms -/

/-- **A single-name group's compile block is that name alone.** -/
theorem single_block {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ)
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint}
    (scheduled : ∀ x ∈ (scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList, ∃ conv, x.1.2 = .ok conv)
    {i : Nat} {gr : Group} (hgr : (quotientGraph ixe t hints sub).groups[i]? = some gr) (hc : Component gr)
    {n : Ix.Name} (hsingle : gr.names = #[n])
    {repE : Ix.Name} {allE : Ix.Set Ix.Name} (hE : (CompiledRefs.envBlocks env).blocks.get? repE = some allE)
    (hnE : allE.contains n = true) :
    ∀ x, allE.contains x = true → (x == n) = true := by
  obtain ⟨names, -, -⟩ := group_names P scheduled hgr hc hE (by rw [hsingle]; simp) hnE
  intro x hx
  have hfound : (env.consts.get? x).isSome = true := by
    have hk := CompiledRefs.key_of_member hE hx
    exact CompiledRefs.node_const (E := { consts := env.consts }) (by
      rw [Std.HashMap.get?_eq_getElem?, ← Std.HashMap.contains_eq_isSome_getElem?]; exact hk)
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hfound
  have hin := (names ci.getCnst.name).mpr ⟨x, ci, hx, hci, rfl⟩
  rw [hsingle] at hin
  have e : ci.getCnst.name = n := by simpa using hin
  have hfound' := hci
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList] at hfound'
  obtain ⟨k', e', hm'⟩ := hfound'
  rw [← e, Ix.Cert.inputsNamed P.compiled k' ci hm']
  exact e'


/-! ## The compile's members loop reads every definition -/

/-- A definition-like member. -/
def IsDefn : MutConst → Prop
  | .defn _ => True
  | _ => False

/-- The block compile's members loop, over a list of names. -/
abbrev membersLoop (l : List Ix.Name) (init : Array MutConst) : CompileM (Array MutConst) :=
  forIn l init fun n (acc : Array Ix.MutConst) => do
    match ← findConst n with
    | .inductInfo val => pure (ForInStep.yield (acc.push (← MutConst.mkIndc val)))
    | .defnInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromDefinitionVal val)))
    | .opaqueInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromOpaqueVal val)))
    | .thmInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromTheoremVal val)))
    | .recInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.recr val)))
    | _ => pure (ForInStep.yield acc)

/-- **The members loop keeps what it has and reads every definition**, and makes only
definition-like members of definitions. -/
theorem loop_definitions (ctx : CompileEnv × BlockEnv) :
    ∀ (l : List Ix.Name) (init : Array MutConst) (s s' : BlockState) (cs : Array MutConst),
      Ix.CompileCert.rawRun (membersLoop l init) ctx s = (.ok cs, s') →
        (∀ m ∈ init, m ∈ cs) ∧
        (∀ k ∈ l, ∀ ci, ctx.1.env.get? k = some ci → isDefinition ci = true → ∃ m ∈ cs, m.name = ci.getCnst.name) ∧
        ((∀ m ∈ init, IsDefn m) → (∀ k ∈ l, ∀ ci, ctx.1.env.get? k = some ci → isDefinition ci = true) →
          ∀ m ∈ cs, IsDefn m)
  | [], init, s, s', cs, h => by
    unfold membersLoop at h
    rw [List.forIn_nil, Ix.CompileCert.rawRun_pure] at h
    cases h
    exact ⟨fun m hm => hm, ⟨fun k hk => absurd hk List.not_mem_nil, fun h _ => h⟩⟩
  | k :: l, init, s, s', cs, h => by
    unfold membersLoop at h
    rw [List.forIn_cons] at h
    obtain ⟨st, mid, hb, h⟩ := Ix.CompileCert.bind_ok h
    obtain ⟨c, mid₀, hc, hb⟩ := Ix.CompileCert.bind_ok hb
    have hfound := BlockRecords.findConst_ok hc
    have step : ∃ acc', st = .yield acc' ∧ (∀ m ∈ init, m ∈ acc') ∧
        (∀ ci, ctx.1.env.get? k = some ci → isDefinition ci = true → ∃ m ∈ acc', m.name = ci.getCnst.name) ∧
        ((∀ m ∈ init, IsDefn m) → (∀ ci, ctx.1.env.get? k = some ci → isDefinition ci = true) →
          ∀ m ∈ acc', IsDefn m) := by
      have keep : ∀ (m : MutConst), ∀ m' ∈ init, m' ∈ init.push m := fun m m' hm => Array.mem_push_of_mem _ hm
      cases c with
      | inductInfo val =>
        obtain ⟨y, mid', hy, hb⟩ := Ix.CompileCert.bind_ok hb
        rw [Ix.CompileCert.rawRun_pure] at hb
        cases hb
        refine ⟨_, rfl, keep y, fun ci hci hd => ?_, fun _ hall => ?_⟩
        · rw [hfound] at hci
          cases hci
          simp [isDefinition] at hd
        · have := hall _ hfound
          simp [isDefinition] at this
      | defnInfo val =>
        rw [Ix.CompileCert.rawRun_pure] at hb
        cases hb
        refine ⟨_, rfl, keep _, fun ci hci _ => ⟨_, Array.mem_push_self, ?_⟩, fun hinit _ m hm => ?_⟩
        · rw [hfound] at hci
          cases hci
          rfl
        · rcases Array.mem_push.mp hm with hm | rfl
          · exact hinit m hm
          · exact trivial
      | opaqueInfo val =>
        rw [Ix.CompileCert.rawRun_pure] at hb
        cases hb
        refine ⟨_, rfl, keep _, fun ci hci _ => ⟨_, Array.mem_push_self, ?_⟩, fun hinit _ m hm => ?_⟩
        · rw [hfound] at hci
          cases hci
          rfl
        · rcases Array.mem_push.mp hm with hm | rfl
          · exact hinit m hm
          · exact trivial
      | thmInfo val =>
        rw [Ix.CompileCert.rawRun_pure] at hb
        cases hb
        refine ⟨_, rfl, keep _, fun ci hci _ => ⟨_, Array.mem_push_self, ?_⟩, fun hinit _ m hm => ?_⟩
        · rw [hfound] at hci
          cases hci
          rfl
        · rcases Array.mem_push.mp hm with hm | rfl
          · exact hinit m hm
          · exact trivial
      | recInfo val =>
        rw [Ix.CompileCert.rawRun_pure] at hb
        cases hb
        refine ⟨_, rfl, keep _, fun ci hci hd => ?_, fun _ hall => ?_⟩
        · rw [hfound] at hci
          cases hci
          simp [isDefinition] at hd
        · have := hall _ hfound
          simp [isDefinition] at this
      | _ =>
        rw [Ix.CompileCert.rawRun_pure] at hb
        cases hb
        refine ⟨_, rfl, fun _ h => h, fun ci hci hd => ?_, fun hinit _ => hinit⟩
        all_goals (rw [hfound] at hci; cases hci; simp [isDefinition] at hd)
    obtain ⟨acc', rfl, hinit, hk, hdefn⟩ := step
    obtain ⟨rest₁, rest₂, rest₃⟩ := loop_definitions ctx l acc' mid s' cs h
    refine ⟨fun m hm => rest₁ m (hinit m hm), fun k' hk' ci hci hd => ?_, fun hi hall => ?_⟩
    · rcases List.mem_cons.mp hk' with rfl | hk'
      · obtain ⟨m, hm, e⟩ := hk ci hci hd
        exact ⟨m, rest₁ m hm, e⟩
      · exact rest₂ k' hk' ci hci hd
    · exact rest₃ (hdefn hi (hall k List.mem_cons_self)) fun k' hk' => hall k' (List.mem_cons_of_mem _ hk')

/-- **A definitions group's names are its compile block's members' names**, for the members the
block's loop reads (`membersLoop` over the block, as `compileBlock` runs it), all of which are
definition-like. -/
theorem definitions_members {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ)
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint}
    (scheduled : ∀ x ∈ (scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList, ∃ conv, x.1.2 = .ok conv)
    {i : Nat} {gr : Group} (hgr : (quotientGraph ixe t hints sub).groups[i]? = some gr)
    {ms : Array Ix.ConstantInfo} (hdef : gr = .definitions ms)
    {repE : Ix.Name} {allE : Ix.Set Ix.Name} (hE : (CompiledRefs.envBlocks env).blocks.get? repE = some allE)
    {n : Ix.Name} (hn : n ∈ gr.names) (hnE : allE.contains n = true)
    {ctx : CompileEnv × BlockEnv} (henv : ∀ x, ctx.1.env.get? x = env.consts.get? x) {s s' : BlockState}
    {cs : Array MutConst} (hloop : Ix.CompileCert.rawRun (forIn allE #[] fun n (acc : Array Ix.MutConst) => do
        match ← findConst n with
        | .inductInfo val => pure (ForInStep.yield (acc.push (← MutConst.mkIndc val)))
        | .defnInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromDefinitionVal val)))
        | .opaqueInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromOpaqueVal val)))
        | .thmInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromTheoremVal val)))
        | .recInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.recr val)))
        | _ => pure (ForInStep.yield acc)) ctx s = (.ok cs, s')) :
    (∀ x, x ∈ gr.names ↔ ∃ m ∈ cs, m.name = x) ∧ ∀ m ∈ cs, IsDefn m := by
  have hcs : Ix.CompileCert.rawRun (membersLoop allE.toList #[]) ctx s = (.ok cs, s') := by
    rw [Std.HashSet.forIn_eq_forIn_toList] at hloop
    exact hloop
  obtain ⟨names, -, defs⟩ := group_names P scheduled hgr (by rw [hdef]; trivial) hE hn hnE
  have defE := defs ms hdef
  obtain ⟨-, reads, kinds⟩ := loop_definitions ctx allE.toList #[] s s' cs hcs
  -- a member of the block is listed, under a key that hashes like it
  have listed : ∀ k, allE.contains k = true → ∃ k' ∈ allE.toList, (k == k') = true := by
    intro k hk
    have hl : allE.toList.contains k = true := by rw [Std.HashSet.contains_toList]; exact hk
    exact List.contains_iff_exists_mem_beq.mp hl
  have members : ∀ m ∈ cs, ∃ k ci, allE.contains k = true ∧ env.consts.get? k = some ci ∧ m.name = ci.getCnst.name := by
    intro m hm
    obtain ⟨n', ci, hn', hci, hname, -⟩ := Claims.members_post ctx allE s cs s' hloop m hm
    exact ⟨n', ci, hn', by rw [← henv]; exact hci, hname⟩
  refine ⟨fun x => ?_, kinds (fun m hm => by simp at hm) fun k hk ci hci => ?_⟩
  · rw [names x]
    constructor
    · rintro ⟨k, ci, hk, hci, rfl⟩
      obtain ⟨k', hk', e⟩ := listed k hk
      have hci' : ctx.1.env.get? k' = some ci := by
        rw [henv, Std.HashMap.get?_eq_getElem?, ← Std.HashMap.getElem?_congr e, ← Std.HashMap.get?_eq_getElem?]
        exact hci
      exact reads k' hk' ci hci' (defE k ci hk hci)
    · rintro ⟨m, hm, rfl⟩
      exact members m hm
  · rw [henv] at hci
    exact defE k ci (Std.HashSet.mem_iff_contains.1 (Std.HashSet.mem_of_mem_toList hk)) hci


/-- The definition a definition-like member holds. -/
def toDef : MutConst → Option Ix.Def
  | .defn d => some d
  | _ => none

theorem defs_map : ∀ L : List MutConst, (∀ m ∈ L, IsDefn m) → (L.filterMap toDef).map MutConst.defn = L
  | [], _ => rfl
  | m :: rest, h => by
    have hm := h m List.mem_cons_self
    have hr := defs_map rest fun m' hm' => h m' (List.mem_cons_of_mem _ hm')
    cases m with
    | defn d => simp only [List.filterMap_cons, toDef, List.map_cons, hr]
    | _ => exact hm.elim

/-- **Lean's order of a block of definition-like members is a list of definitions**, one per
class, holding exactly the members. -/
theorem sourceMembers_defs {cs : Array MutConst} (hd : ∀ m ∈ cs, IsDefn m) :
    ∃ defs : List Ix.Def, sourceMembers cs = defs.map MutConst.defn ∧
      ∀ m, m ∈ cs ↔ ∃ d ∈ defs, MutConst.defn d = m := by
  unfold sourceMembers
  dsimp only
  generalize hL : (cs.zipIdx.qsort _).toList = L
  have mem : ∀ e, e ∈ L ↔ e ∈ cs.zipIdx := by
    intro e
    rw [← hL, Array.mem_toList_iff, Ix.CompileCert.Canon.mem_qsort]
  have inCs : ∀ e ∈ L, e.1 ∈ cs := fun e he =>
    Array.mem_of_getElem? (Array.mem_zipIdx_iff_getElem?.mp ((mem e).mp he))
  have all : ∀ m ∈ L.map (·.1), IsDefn m := by
    intro m hm
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
    exact hd _ (inCs e he)
  refine ⟨(L.map (·.1)).filterMap toDef, ?_, fun m => ?_⟩
  · exact (defs_map _ all).symm
  · rw [← List.mem_map (f := MutConst.defn), defs_map _ all]
    constructor
    · intro hm
      obtain ⟨i, hi⟩ := Array.mem_iff_getElem?.mp hm
      exact List.mem_map.mpr ⟨(m, i), (mem _).mpr (Array.mem_zipIdx_iff_getElem?.mpr hi), rfl⟩
    · intro hm
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
      exact inCs e he

/-- **A definitions group's names are its compile block's definitions'**, in the form the
definition-block readings take: the block's members in Lean's order (`sourceMembers`) are one
definition per class, `defs`, and the group's names are theirs. -/
theorem definitions_defs {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ)
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint}
    (scheduled : ∀ x ∈ (scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList, ∃ conv, x.1.2 = .ok conv)
    {i : Nat} {gr : Group} (hgr : (quotientGraph ixe t hints sub).groups[i]? = some gr)
    {ms : Array Ix.ConstantInfo} (hdef : gr = .definitions ms)
    {repE : Ix.Name} {allE : Ix.Set Ix.Name} (hE : (CompiledRefs.envBlocks env).blocks.get? repE = some allE)
    {n : Ix.Name} (hn : n ∈ gr.names) (hnE : allE.contains n = true)
    {ctx : CompileEnv × BlockEnv} (henv : ∀ x, ctx.1.env.get? x = env.consts.get? x) {s s' : BlockState}
    {cs : Array MutConst} (hloop : Ix.CompileCert.rawRun (forIn allE #[] fun n (acc : Array Ix.MutConst) => do
        match ← findConst n with
        | .inductInfo val => pure (ForInStep.yield (acc.push (← MutConst.mkIndc val)))
        | .defnInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromDefinitionVal val)))
        | .opaqueInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromOpaqueVal val)))
        | .thmInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromTheoremVal val)))
        | .recInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.recr val)))
        | _ => pure (ForInStep.yield acc)) ctx s = (.ok cs, s')) :
    ∃ defs : List Ix.Def, sourceMembers cs = defs.map MutConst.defn ∧
      ∀ x, x ∈ gr.names ↔ ∃ (j : Nat) (_ : j < defs.length), defs[j].name = x := by
  obtain ⟨names, kinds⟩ := definitions_members P scheduled hgr hdef hE hn hnE henv hloop
  obtain ⟨defs, hcls, hmem⟩ := sourceMembers_defs kinds
  refine ⟨defs, hcls, fun x => ?_⟩
  rw [names x]
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨d, hd, rfl⟩ := (hmem m).mp hm
    obtain ⟨j, hj, e⟩ := List.mem_iff_getElem.mp hd
    exact ⟨j, hj, by rw [e]; rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨.defn defs[j], (hmem _).mpr ⟨defs[j], List.getElem_mem hj, rfl⟩, rfl⟩

end Ix.Cert.GroupBlocks

/--
info: 'Ix.Cert.GroupBlocks.block_agree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Cert.GroupBlocks.block_agree

/--
info: 'Ix.Cert.GroupBlocks.definitions_defs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Cert.GroupBlocks.definitions_defs

/--
info: 'Ix.Cert.GroupBlocks.single_block' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Cert.GroupBlocks.single_block
