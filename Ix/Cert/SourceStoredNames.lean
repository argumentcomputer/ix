import Ix.Cert.SourceInstalls
import Ix.CompileCert.Canon.QSort
import Ix.Cert.Composition

/-! # A stored name of an accepted closure is the environment's key

Quotient Source accepts a closure only if every name the closure stores a constant
under is spelled as a name of one of its groups (`SourceDeclares.stored_grouped`), and
every group converts. A converted group's names are the own names (`getCnst.name`)
of constants the closure stores: an inductive group's types and constructors are
looked up, its recursors come from the closure's recursors, and a component group's
members are looked up (`groupsOf_stored`). The compile's input-name check makes every
own name the input key it is stored under, spelled exactly (`inputsNamed`), so a name
the closure stores a constant under is the input's key for it (`stored_input`). -/

namespace Ix.Cert.SourceStoredNames

open Ix.LeanIngress
open Ix.CompileCert.Loop (idBind idPure except_bind_ok)

/-! ## Groups over the environment's lookup -/

/-- `inductiveGroup` is `inductiveGroupUsing` over the environment's lookup, in `Id`. -/
theorem inductive_default (env : Ix.Environment) (first : Ix.InductiveVal) (candidates : Array Ix.RecursorVal) :
    inductiveGroup env first candidates =
      Id.run (inductiveGroupUsing (m := Id) (env.consts.get? ·) first candidates) := rfl

/-- `componentGroup` is `componentGroupUsing` over the environment's lookup, in `Id`. -/
theorem component_default (env : Ix.Environment) (members : Ix.Set Ix.Name) :
    componentGroup env members = Id.run (componentGroupUsing (m := Id) (env.consts.get? ·) members) := rfl

/-! ## Loops in `Id` -/

/-- An invariant of an `Id` loop's states holds of its result. -/
theorem forIn_id_prop {α σ : Type} (I : σ → Prop) {Q : σ → Prop} {f : α → σ → Id (ForInStep σ)} :
    ∀ (l : List α), (∀ x ∈ l, ∀ s, I s → I (f x s).value) → (∀ t, I t → Q t) →
      ∀ s, I s → Q (Id.run (forIn l s f))
  | [], _, concl, s, hs => concl s hs
  | x :: l, step, concl, s, hs => by
    rw [List.forIn_cons]
    have hx := step x List.mem_cons_self s hs
    generalize f x s = v at hx ⊢
    cases v with
    | done b => exact concl b hx
    | yield b =>
      exact forIn_id_prop I l (fun y hy => step y (List.mem_cons_of_mem _ hy)) concl b hx

theorem forIn_id_prop_array {α σ : Type} (I : σ → Prop) {Q : σ → Prop} {f : α → σ → Id (ForInStep σ)}
    (xs : Array α) (step : ∀ x ∈ xs.toList, ∀ s, I s → I (f x s).value) (concl : ∀ t, I t → Q t)
    (s : σ) (hs : I s) : Q (Id.run (forIn xs s f)) := by
  rw [← Array.forIn_toList]
  exact forIn_id_prop I xs.toList step concl s hs

/-! ## Stored constants -/

/-- A constant a lookup returns is stored under some key. -/
theorem lookup_stored {env : Ix.Environment} {x : Ix.Name} {ci : Ix.ConstantInfo}
    (h : env.consts.get? x = some ci) : ∃ k, (k, ci) ∈ env.consts.toList := by
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList] at h
  obtain ⟨k, -, hk⟩ := h
  exact ⟨k, hk⟩

/-- A stored entry is what a lookup of its key returns. -/
theorem stored_get {env : Ix.Environment} {n : Ix.Name} {ci : Ix.ConstantInfo}
    (h : (n, ci) ∈ env.consts.toList) : env.consts.get? n = some ci := by
  rw [Std.HashMap.get?_eq_getElem?]
  exact (Std.HashMap.mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some.mp h).2

/-- A group's names are own names of constants the environment stores. -/
def NamesStored (env : Ix.Environment) (g : Group) : Prop :=
  ∀ x ∈ g.names, ∃ k ci, (k, ci) ∈ env.consts.toList ∧ ci.getCnst.name = x

/-- A loop state with no early result, or an invalid group as its early result. -/
abbrev Pending (o : Option Group) : Prop := o = none ∨ ∃ c e, o = some (.invalid c e)

/-! ## Component groups -/

/-- **A component group's names are its members' own names**, each a constant the
environment stores. -/
theorem componentGroup_stored {env : Ix.Environment} {members : Ix.Set Ix.Name} {g : Group}
    (h : componentGroup env members = some g) : NamesStored env g := by
  rw [component_default] at h
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
  have names : g.names = others.map (·.getCnst.name) := by
    split at h
    · cases h
    · split at h
      · cases h
        rfl
      · split at h
        · cases h
          rfl
        · obtain ⟨l⟩ := others
          rcases l with _ | ⟨c, _ | ⟨c₂, rest⟩⟩
          · cases h
            rfl
          · cases c <;> (cases h; simp [Group.names, Ix.ConstantInfo.getCnst])
          · cases h
            rfl
  intro x hx
  rw [names] at hx
  obtain ⟨ci, hci, rfl⟩ := Array.mem_map.mp hx
  obtain ⟨k, hk⟩ := storedOthers ci hci
  exact ⟨k, ci, hk, rfl⟩

/-! ## Inductive groups -/

/-- A block's recursors are among its candidates. -/
theorem blockRecursors_mem {first : Ix.InductiveVal} {cands recs : Array Ix.RecursorVal}
    (h : blockRecursors first cands = .ok recs) : ∀ r ∈ recs, r ∈ cands := by
  unfold blockRecursors at h
  obtain ⟨own, hown, h⟩ := except_bind_ok.mp h
  obtain ⟨aux, haux, h⟩ := except_bind_ok.mp h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  intro r hr
  rcases Array.mem_append.mp hr with hr | hr
  · obtain ⟨x, -, hx⟩ := ReaderUnits.forall₂_mem_right (ReaderUnits.array_mapM_ok hown) r
      (Array.mem_toList_iff.mpr hr)
    dsimp only at hx
    split at hx
    · rename_i r' hr'
      cases hx
      exact Array.mem_of_find?_eq_some hr'
    · cases hx
  · obtain ⟨x, -, hx⟩ := ReaderUnits.forall₂_mem_right (ReaderUnits.array_mapM_ok haux) r
      (Array.mem_toList_iff.mpr hr)
    dsimp only at hx
    split at hx
    · rename_i r' hr'
      cases hx
      exact Array.mem_of_find?_eq_some hr'
    · cases hx

/-- **A converted inductive group's names are own names of stored constants**, when its
recursor candidates are stored recursors. -/
theorem inductiveGroup_stored {env : Ix.Environment} {first : Ix.InductiveVal}
    {cands : Array Ix.RecursorVal}
    (hc : ∀ r ∈ cands, ∃ k, (k, Ix.ConstantInfo.recInfo r) ∈ env.consts.toList) {c : Converted}
    (conv : convert (inductiveGroup env first cands) = .ok c) :
    NamesStored env (inductiveGroup env first cands) := by
  generalize hg : inductiveGroup env first cands = g at conv ⊢
  rw [inductive_default] at hg
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
        intro x hx
        unfold Group.names at hx
        rcases Array.mem_append.mp hx with hx | hx
        · rcases Array.mem_append.mp hx with hx | hx
          · obtain ⟨v, hv, rfl⟩ := Array.mem_map.mp hx
            refine (forIn_id_prop_array
              (I := fun s : Option Group × Array Ix.InductiveVal =>
                ∀ v ∈ s.2, ∃ k, (k, Ix.ConstantInfo.inductInfo v) ∈ env.consts.toList)
              (Q := fun t => ∀ v ∈ t.2, ∃ k ci, (k, ci) ∈ env.consts.toList ∧ ci.getCnst.name = v.cnst.name)
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
              exact ⟨k, _, hk, rfl⟩
            · intro v hv
              exact absurd hv (Array.not_mem_empty _)
          · obtain ⟨cs, hcs, hx⟩ := Array.mem_flatMap.mp hx
            obtain ⟨cv, hcv, rfl⟩ := Array.mem_map.mp hx
            refine (forIn_id_prop_array
              (I := fun s : Option Group × Array (Array Ix.ConstructorVal) =>
                ∀ cs ∈ s.2, ∀ cv ∈ cs, ∃ k, (k, Ix.ConstantInfo.ctorInfo cv) ∈ env.consts.toList)
              (Q := fun t => ∀ cs ∈ t.2, ∀ cv ∈ cs,
                ∃ k ci, (k, ci) ∈ env.consts.toList ∧ ci.getCnst.name = cv.cnst.name)
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
              exact ⟨k, _, hk, rfl⟩
            · intro cs hcs
              exact absurd hcs (Array.not_mem_empty _)
        · obtain ⟨r, hr, rfl⟩ := Array.mem_map.mp hx
          obtain ⟨k, hk⟩ := hc r (blockRecursors_mem hrecs r hr)
          exact ⟨k, _, hk, rfl⟩
      · subst hg
        cases conv

/-! ## The groups -/

/-- **Every converted group's names are own names of stored constants.** -/
theorem groupsOf_stored (env : Ix.Environment) (blocks : Ix.CondensedBlocks) :
    ∀ g ∈ groupsOf env blocks, ∀ c, convert g = .ok c → NamesStored env g := by
  unfold groupsOf
  simp only [Id.run, Std.HashMap.forIn_eq_forIn_toList, idBind, idPure]
  refine forIn_id_prop (I := fun acc : Array Group => ∀ g ∈ acc, ∀ c, convert g = .ok c → NamesStored env g)
    _ ?_ (fun _ h => h) _ ?_
  · intro x _ s hs
    split
    · exact hs
    · intro g hg c hc
      rcases Array.mem_push.mp hg with hg | rfl
      · exact hs g hg c hc
      · unfold unplaced at hc
        split at hc <;> cases hc
  · refine forIn_id_prop (I := fun acc : Array Group => ∀ g ∈ acc, ∀ c, convert g = .ok c → NamesStored env g)
      _ ?_ (fun _ h => h) _ ?_
    · intro x _ s hs
      split
      · rename_i g' hg'
        intro g hg c hc
        rcases Array.mem_push.mp hg with hg | rfl
        · exact hs g hg c hc
        · exact componentGroup_stored hg'
      · exact hs
    · refine forIn_id_prop
        (I := fun acc : Array Group => ∀ g ∈ acc, ∀ c, convert g = .ok c → NamesStored env g)
        _ ?_ (fun _ h => h) _ ?_
      · intro x _ s hs
        split
        · split
          · intro g hg c hc
            rcases Array.mem_push.mp hg with hg | rfl
            · exact hs g hg c hc
            · refine inductiveGroup_stored ?_ hc
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

/-! ## Stored names -/

/-- **A successful preparation converted every group** of its environment. -/
theorem prepared_converts {ρ : FiberMap} {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint}
    {pre : Ix.Kernel.Reader.Prelude .source} {env : Ix.Environment} {blocks : Ix.CondensedBlocks}
    {ds : Array (Ix.Kernel.Declaration .source)} (h : prepareSourceCollapsed ρ hints pre env blocks = .ok ds) :
    ∀ g ∈ groupsOf env blocks, ∃ c, convert g = .ok c := by
  obtain ⟨fin, decls, hl, -, -⟩ := prepareSourceCollapsed_keepsPrelude h
  obtain ⟨rs, s, kb, ht, -, -, -⟩ := Ix.Cert.SourcePrelude.lowerAllCollapsed_trace hl
  intro g hg
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hg
  have hgroups : (graphCollapsed ρ hints env blocks).groups = groupsOf env blocks := by
    show (graph env blocks).groups = _
    exact ReaderUnits.graph_groups env blocks
  have hi' : i < (graphCollapsed ρ hints env blocks).groups.size := by rw [hgroups]; exact hi
  obtain ⟨c, hcmem⟩ := scheduleOf_complete _ hi'
  obtain ⟨j, hj, hjeq⟩ := Array.getElem_of_mem hcmem
  have hx : ((i, c), j) ∈ (scheduleOf (graphCollapsed ρ hints env blocks)).zipIdx.toList :=
    Array.mem_toList_iff.mpr (Array.mem_zipIdx_iff_getElem?.mpr (by simp [hj, hjeq]))
  obtain ⟨-, covered⟩ := SourceDeclares.trace_declares ht
  obtain ⟨conv, hconv, -⟩ := covered _ hx
  have hcv := ReaderUnits.scheduleOf_ok (Array.mem_toList_iff.mpr hcmem) hconv
  obtain ⟨gr', c0, hgr', hc0, -⟩ := Ix.Cert.SourceTrace.graph_conversion hcv
  have same : gr' = (groupsOf env blocks)[i] := by
    rw [ReaderUnits.graph_groups, Array.getElem?_eq_getElem hi] at hgr'
    exact (Option.some.inj hgr').symm
  subst same
  exact ⟨c0, hc0⟩

/-- **A name an accepted closure stores a constant under is the input's key for it**,
spelled exactly. -/
theorem stored_input {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (hP : Premises env roots sub ixe failures t envQ) {n : Ix.Name} {ci : Ix.ConstantInfo}
    (hn : (n, ci) ∈ sub.consts.toList) : (n, ci) ∈ env.consts.toList := by
  obtain ⟨closure, pre, ds, -, hprep, -⟩ := hP.source
  have hcol := SourceDeclares.preparedAt_collapsed hprep
  obtain ⟨g, hg, hng⟩ := SourceDeclares.stored_grouped sub (blocksOf sub) hn
  obtain ⟨c, hc⟩ := prepared_converts hcol g hg
  obtain ⟨k, ci', hk, hown⟩ := groupsOf_stored sub _ g hg c hc n hng
  obtain ⟨k', hk'⟩ := lookup_stored (closure.mem_env (stored_get hk))
  have hname := inputsNamed hP.compiled k' ci' hk'
  rw [hown] at hname
  subst hname
  have same := closure.mem_env (stored_get hn)
  rw [stored_get hk'] at same
  cases same
  exact hk'

/-- **A name an accepted closure stores a constant under is published under that exact
name.** -/
theorem stored_published {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (hP : Premises env roots sub ixe failures t envQ) {n : Ix.Name} {ci : Ix.ConstantInfo}
    (hn : (n, ci) ∈ sub.consts.toList) :
    ∃ named, (n, named) ∈ ixe.named.toList ∧ ixe.named.get? n = some named := by
  have henv := stored_input hP hn
  obtain ⟨named, hnamed⟩ := (compileCovers env ixe failures hP.compiled n ci
    (stored_get henv)).mpr (hP.none n ci (stored_get hn))
  have hfound := hnamed
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList] at hfound
  obtain ⟨m, hmn, hm⟩ := hfound
  have keyOf : ∀ {β : Type} {mp : Std.HashMap Ix.Name β} {a : Ix.Name} {b : β}, (a, b) ∈ mp.toList →
      a ∈ mp.keys := fun h => by
    rw [← Std.HashMap.map_fst_toList_eq_keys]
    exact List.mem_map_of_mem (f := Prod.fst) h
  have heq : m = n := nameHashes_distinct hP.compiled m (List.mem_append_right _ (keyOf hm))
    n (List.mem_append_left _ (keyOf henv)) (name_beq_iff.mp hmn).symm
  subst heq
  exact ⟨named, hm, hnamed⟩

/-- info: 'Ix.Cert.SourceStoredNames.stored_published' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stored_published

end Ix.Cert.SourceStoredNames
