import Ix.Cert.GroupBlocks
import Ix.Cert.ReportChecks

/-! # An inductive group's compile blocks

Quotient Source groups an inductive family by its first type's Lean block: the types its `all`
lists, their constructors, and the recursors that name the block (`inductiveGroupUsing`). The
compiler compiles the strongly connected components of the input's reference graph
(`CompiledRefs.envBlocks`). On crafted input the two can differ: a recursor's own `all` joins
it to another family's recursors in the reference graph, and Source reads only `all[0]`. The
compile report therefore checks that every component holding a family member is one family's
(`FamilyBlocks`, `familyBlocks`). With it:

* the compile block of a Source inductive group's first type holds exactly the group's types and
  constructors (`inductive_block`; any block holding one of its types does, `inductive_block_at`);
* the compile block of one of its recursors holds exactly the group's recursors
  (`recursor_block`): every input recursor whose block's first member is the group's is in the
  closure (`DependsOn`), in some group (`SourceDeclares.stored_grouped`) that converts, and that
  group can only be this one (`groups_origin`, `recsTable`). Any block holding one of its
  recursors does (`recursor_block_at`).

The group's shape is read off its loops (`inductiveGroup_shape`: `TypesOf`, `CtorsOf`), and a
group of `groupsOf` is an inductive block's, a component's or an unplaced constant's
(`groups_origin`). -/

namespace Ix.Cert.FamilyGroups

open Ix.CompileM Ix.Cert.Resolution Ix.Cert.Schedule
open Ix.LeanIngress (Group TableName groupsOf inductiveGroup inductiveGroupUsing componentGroup
  componentGroupUsing blockRecursors unplaced convert isFamily)
open Ix.Cert.ClosureLayout (quotientGraph)
open Ix.CompileCert.Loop (idBind idPure except_bind_ok)
open Ix.Cert.GroupBlocks (Component)

/-! ## Loops that collect -/

/-- **A loop that collects one element per item, or stops with a result**: when it does not stop,
it collects one element `P`-related to each item, in order. -/
theorem forIn_collect {α β γ : Type} (P : α → β → Prop)
    {f : α → Option γ × Array β → Id (ForInStep (Option γ × Array β))}
    (hf : ∀ x s, (∃ b, P x b ∧ f x s = .yield (none, s.snd.push b)) ∨ ∃ g t, f x s = .done (some g, t)) :
    ∀ (l : List α) (acc : Array β), (forIn (m := Id) l ((none : Option γ), acc) f).fst = none →
      ∃ bs : List β, (forIn (m := Id) l ((none : Option γ), acc) f).snd.toList = acc.toList ++ bs ∧
        List.Forall₂ P l bs
  | [], acc, _ => ⟨[], (List.append_nil _).symm, .nil⟩
  | x :: l, acc, h => by
    rw [List.forIn_cons] at h ⊢
    rcases hf x (none, acc) with ⟨b, hb, e⟩ | ⟨g, t, e⟩
    · rw [e] at h ⊢
      obtain ⟨bs, hbs, hall⟩ := forIn_collect P hf l (acc.push b) h
      exact ⟨b :: bs, hbs.trans (by simp), .cons hb hall⟩
    · rw [e] at h
      nomatch h

/-- `forIn_collect` over an array, from the empty collection. -/
theorem forIn_collect_array {α β γ : Type} (P : α → β → Prop)
    {f : α → Option γ × Array β → Id (ForInStep (Option γ × Array β))} {xs : Array α}
    (hn : (forIn (m := Id) xs ((none : Option γ), (#[] : Array β)) f).fst = none)
    (hf : ∀ x s, (∃ b, P x b ∧ f x s = .yield (none, s.snd.push b)) ∨ ∃ g t, f x s = .done (some g, t)) :
    List.Forall₂ P xs.toList (forIn (m := Id) xs ((none : Option γ), (#[] : Array β)) f).snd.toList := by
  rw [← Array.forIn_toList] at hn ⊢
  obtain ⟨bs, hbs, hall⟩ := forIn_collect P hf xs.toList #[] hn
  rw [hbs]
  simpa using hall

/-! ## An inductive group's shape -/

/-- An inductive group's types: the inductives its first type's block lists, in order, each
naming that block. -/
def TypesOf (E : Ix.Environment) (first : Ix.InductiveVal) (types : Array Ix.InductiveVal) : Prop :=
  List.Forall₂ (fun n v => E.consts.get? n = some (.inductInfo v) ∧ v.all.isEqv first.all Ix.Name.beqRaw = true)
    first.all.toList types.toList

/-- An inductive group's constructors: for each type, the constructors it lists, in order, each a
constructor of that type at its position. -/
def CtorsOf (E : Ix.Environment) (types : Array Ix.InductiveVal) (ctors : Array (Array Ix.ConstructorVal)) :
    Prop :=
  List.Forall₂ (fun (v : Ix.InductiveVal) (cs : Array Ix.ConstructorVal) =>
    List.Forall₂ (fun (x : Ix.Name × Nat) cv => E.consts.get? x.1 = some (.ctorInfo cv) ∧
      cv.induct.beqRaw v.cnst.name = true ∧ (cv.cidx == x.2) = true) v.ctors.zipIdx.toList cs.toList)
    types.toList ctors.toList

/-- **An inductive block's group is refused or has its block's shape**: its types are the
inductives the block lists (`TypesOf`), its constructors theirs (`CtorsOf`), and its recursors
`blockRecursors`'. -/
theorem inductiveGroup_shape {E : Ix.Environment} {first : Ix.InductiveVal} {cands : Array Ix.RecursorVal}
    {g : Group} (h : inductiveGroup E first cands = g) :
    (∃ ns e, g = .invalid ns e) ∨ ∃ types ctors recs, g = .inductive types ctors recs ∧
      TypesOf E first types ∧ CtorsOf E types ctors ∧ blockRecursors first cands = .ok recs := by
  rw [Ix.Cert.SourceStoredNames.inductive_default] at h
  unfold inductiveGroupUsing at h
  simp only [Id.run, idBind, idPure] at h
  split at h
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
      exact .inl ⟨cl, e, h.symm⟩
  · split at h
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
        exact .inl ⟨cl, e, h.symm⟩
    · split at h
      · rename_i _ htypes _ hctors _ recs hrecs
        subst h
        refine .inr ⟨_, _, recs, rfl, ?_, ?_, hrecs⟩
        · unfold TypesOf
          refine forIn_collect_array _ htypes fun n s => ?_
          split
          · split
            · exact .inl ⟨_, ⟨‹_›, ‹_›⟩, rfl⟩
            · exact .inr ⟨_, _, rfl⟩
          · exact .inr ⟨_, _, rfl⟩
        · unfold CtorsOf
          refine forIn_collect_array _ hctors fun v s => ?_
          split
          · exact .inr ⟨_, _, rfl⟩
          · rename_i hin
            refine .inl ⟨_, forIn_collect_array _ hin fun x s => ?_, rfl⟩
            split
            · split
              · split
                · exact .inl ⟨_, ⟨‹_›, ‹_›, ‹_›⟩, rfl⟩
                · exact .inr ⟨_, _, rfl⟩
              · exact .inr ⟨_, _, rfl⟩
            · exact .inr ⟨_, _, rfl⟩
      · exact .inl ⟨_, _, h.symm⟩

/-- A block's recursors, when its first type's block lists a first member, include one. -/
theorem blockRecursors_nonempty {first : Ix.InductiveVal} {cands recs : Array Ix.RecursorVal}
    (h : blockRecursors first cands = .ok recs) {n : Ix.Name} (head : first.all[0]? = some n) :
    ∃ r, r ∈ recs := by
  unfold blockRecursors at h
  obtain ⟨own, hown, h⟩ := except_bind_ok.mp h
  obtain ⟨aux, -, h⟩ := except_bind_ok.mp h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨r, hr, -⟩ := SourceDeclares.forall₂_mem_left (ReaderUnits.array_mapM_ok hown) n
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? head))
  exact ⟨r, Array.mem_append.mpr (.inl (Array.mem_toList_iff.mp hr))⟩

/-! ## `groupsOf`'s groups -/

/-- One step of `groupsOf`'s table of the recursors by their block's first member. -/
def recsStep (x : Ix.Name × Ix.ConstantInfo) (m : Ix.Map TableName (Array Ix.RecursorVal)) :
    Ix.Map TableName (Array Ix.RecursorVal) :=
  match x.2 with
  | .recInfo rv =>
    match rv.all[0]? with
    | some first => m.insert first ((m.getD first #[]).push rv)
    | none => m
  | _ => m

/-- **`groupsOf`'s table of the recursors**, keyed by their block's first member. -/
def recsTable (E : Ix.Environment) : Ix.Map TableName (Array Ix.RecursorVal) :=
  E.consts.toList.foldl (fun m x => recsStep x m) {}

/-- An `Id` loop that always continues is a fold. -/
theorem forIn_yield_foldl {α σ : Type} {f : α → σ → Id (ForInStep σ)} (g : α → σ → σ)
    (hf : ∀ x s, f x s = .yield (g x s)) :
    ∀ (l : List α) (s : σ), forIn (m := Id) l s f = l.foldl (fun s x => g x s) s
  | [], _ => rfl
  | x :: l, s => by
    rw [List.forIn_cons, hf]
    exact forIn_yield_foldl g hf l (g x s)

/-- A table key, read as the name it is. -/
def keyName (k : TableName) : Ix.Name := k

/-- **A recursor `groupsOf` tables under a name is a stored recursor whose block's first member is
that name.** -/
theorem recsTable_mem {E : Ix.Environment} {key : Ix.Name} {r : Ix.RecursorVal}
    (h : r ∈ (recsTable E).getD key #[]) :
    ∃ k, (k, Ix.ConstantInfo.recInfo r) ∈ E.consts.toList ∧ r.all[0]? = some key := by
  unfold recsTable at h
  suffices ∀ (l : List (Ix.Name × Ix.ConstantInfo)) (m : Ix.Map TableName (Array Ix.RecursorVal)),
      (∀ x ∈ l, x ∈ E.consts.toList) →
      (∀ (key : TableName) r, r ∈ m.getD key #[] →
        ∃ k, (k, Ix.ConstantInfo.recInfo r) ∈ E.consts.toList ∧ r.all[0]? = some (keyName key)) →
      ∀ (key : TableName) r, r ∈ (l.foldl (fun m x => recsStep x m) m).getD key #[] →
        ∃ k, (k, Ix.ConstantInfo.recInfo r) ∈ E.consts.toList ∧ r.all[0]? = some (keyName key) from
    this _ {} (fun _ h => h)
      (fun key r hr => by rw [Std.HashMap.getD_empty] at hr; exact absurd hr (Array.not_mem_empty _)) key r h
  intro l
  induction l with
  | nil => intro m _ hm; exact hm
  | cons x l ih =>
    intro m hl hm
    refine ih (recsStep x m) (fun y hy => hl y (List.mem_cons_of_mem _ hy)) ?_
    intro key' r' hr'
    obtain ⟨n, ci⟩ := x
    cases ci with
    | recInfo rv =>
      unfold recsStep at hr'
      dsimp only at hr'
      split at hr'
      · rename_i first hfirst
        rw [Std.HashMap.getD_insert] at hr'
        split at hr'
        · rename_i e
          have hfk : first = key' := eq_of_beq e
          subst hfk
          rcases Array.mem_push.mp hr' with hr' | rfl
          · exact hm _ r' hr'
          · exact ⟨n, hl _ List.mem_cons_self, hfirst⟩
        · exact hm key' r' hr'
      · exact hm key' r' hr'
    | _ => exact hm key' r' hr'

/-- A block's first member's test, read back. -/
theorem head_of_any {xs : Array Ix.Name} {n : Ix.Name} (h : (xs[0]?.any fun y => Ix.Name.beqRaw y n) = true) :
    xs[0]? = some n := by
  cases e : xs[0]? with
  | none => rw [e] at h; cases h
  | some a => rw [e] at h; exact congrArg some (Ix.Name.beqRaw_iff.mp h)

/-- Where a group of `groupsOf` comes from: an inductive stored at the head of its block, with the
recursors tabled under it; a component of the condensation; or a constant no group claims. -/
def Origin (E : Ix.Environment) (blocks : Ix.CondensedBlocks) (g : Group) : Prop :=
  (∃ n v, (n, Ix.ConstantInfo.inductInfo v) ∈ E.consts.toList ∧ v.all[0]? = some n ∧
    inductiveGroup E v ((recsTable E).getD n #[]) = g) ∨
  (∃ rep all, blocks.blocks.get? rep = some all ∧ componentGroup E all = some g) ∨
  ∃ n ci, unplaced n ci = g

/-- **Every group of `groupsOf` has its origin.** -/
theorem groups_origin (E : Ix.Environment) (blocks : Ix.CondensedBlocks) :
    ∀ g ∈ groupsOf E blocks, Origin E blocks g := by
  unfold groupsOf
  simp only [Id.run, Std.HashMap.forIn_eq_forIn_toList, idBind, idPure]
  rw [forIn_yield_foldl recsStep ?step]
  · refine SourceStoredNames.forIn_id_prop (I := fun acc : Array Group => ∀ g ∈ acc, Origin E blocks g)
      _ ?_ (fun _ h => h) _ ?_
    · intro x _ s hs
      split
      · exact hs
      · intro g hg
        rcases Array.mem_push.mp hg with hg | rfl
        · exact hs g hg
        · exact .inr (.inr ⟨_, _, rfl⟩)
    · refine SourceStoredNames.forIn_id_prop (I := fun acc : Array Group => ∀ g ∈ acc, Origin E blocks g)
        _ ?_ (fun _ h => h) _ ?_
      · intro x hx s hs
        split
        · rename_i g' hg'
          intro g hg
          rcases Array.mem_push.mp hg with hg | rfl
          · exact hs g hg
          · refine .inr (.inl ⟨x.1, x.2, ?_, hg'⟩)
            rw [Std.HashMap.get?_eq_getElem?]
            exact (Std.HashMap.mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some.mp hx).2
        · exact hs
      · refine SourceStoredNames.forIn_id_prop (I := fun acc : Array Group => ∀ g ∈ acc, Origin E blocks g)
          _ ?_ (fun _ h => h) _ ?_
        · intro x hx s hs
          split
          · rename_i v hv
            split
            · rename_i hhead
              intro g hg
              rcases Array.mem_push.mp hg with hg | rfl
              · exact hs g hg
              · obtain ⟨n, ci⟩ := x
                simp only at hv
                subst hv
                exact .inl ⟨n, v, hx, head_of_any hhead, rfl⟩
            · exact hs
          · exact hs
        · intro g hg
          exact absurd hg (Array.not_mem_empty _)
  · intro x m
    obtain ⟨n, ci⟩ := x
    cases ci with
    | recInfo rv =>
      simp only [recsStep]
      split <;> split <;> simp_all
    | _ => rfl

/-- A component group is a component's, or refused. -/
theorem componentGroup_cases {E : Ix.Environment} {members : Ix.Set Ix.Name} {g : Group}
    (h : componentGroup E members = some g) : Component g ∨ ∃ ns e, g = .invalid ns e := by
  rw [Ix.Cert.SourceStoredNames.component_default] at h
  unfold componentGroupUsing at h
  generalize (Array.filterMapM (m := Id) (fun x => E.consts.get? x) members.toArray :
    Array Ix.ConstantInfo) = cis at h
  dsimp only [Id.run, bind, pure] at h
  generalize (cis.filter (fun x => !isFamily x)).qsort
    (fun a b => Ix.sourceOrderLt (a.blockPosition, a.getCnst.name)
      (b.blockPosition, b.getCnst.name)) = others at h
  split at h
  · cases h
  · split at h
    · cases h
      exact .inr ⟨_, _, rfl⟩
    · split at h
      · cases h
        exact .inl trivial
      · obtain ⟨l⟩ := others
        rcases l with _ | ⟨c, _ | ⟨c₂, rest⟩⟩
        · cases h
          exact .inr ⟨_, _, rfl⟩
        · cases c <;> cases h
          all_goals first
            | exact .inl trivial
            | exact .inr ⟨_, _, rfl⟩
        · cases h
          exact .inr ⟨_, _, rfl⟩

/-- **An inductive group of `groupsOf` is its block's first inductive's**, with the tabled
recursors as candidates. -/
theorem inductive_origin {E : Ix.Environment} {blocks : Ix.CondensedBlocks}
    {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)} {recs : Array Ix.RecursorVal}
    (h : Group.inductive types ctors recs ∈ groupsOf E blocks) :
    ∃ n v, (n, Ix.ConstantInfo.inductInfo v) ∈ E.consts.toList ∧ v.all[0]? = some n ∧
      inductiveGroup E v ((recsTable E).getD n #[]) = .inductive types ctors recs := by
  rcases groups_origin E blocks _ h with o | ⟨_, _, -, hc⟩ | ⟨n, ci, hu⟩
  · exact o
  · rcases componentGroup_cases hc with hC | ⟨_, _, e⟩
    · exact (hC : False).elim
    · cases e
  · unfold unplaced at hu
    split at hu <;> cases hu

/-! ## Stored names -/

/-- A looked-up input constant's name is the lookup's name, up to `==`. -/
theorem named_of_get {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (compiled : compileReport env = .ok (ixe, failures)) {x : Ix.Name} {ci : Ix.ConstantInfo}
    (h : env.consts.get? x = some ci) : (ci.getCnst.name == x) = true := by
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList] at h
  obtain ⟨k, e, hk⟩ := h
  rw [inputsNamed compiled k ci hk]
  exact BEq.symm e

/-- A looked-up input constant named `k` is the one stored under `k`. -/
theorem same_stored {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (compiled : compileReport env = .ok (ixe, failures)) {k m : Ix.Name} {ci ci' : Ix.ConstantInfo}
    (hk : (k, ci) ∈ env.consts.toList) (hm : env.consts.get? m = some ci') (hname : ci'.getCnst.name = k) :
    ci' = ci := by
  obtain ⟨k', hk'⟩ := SourceStoredNames.lookup_stored hm
  have e := inputsNamed compiled k' ci' hk'
  rw [hname] at e
  subst e
  have h₁ := SourceStoredNames.stored_get hk
  rw [SourceStoredNames.stored_get hk'] at h₁
  exact Option.some.inj h₁

/-- A closure name is reached from the roots. -/
theorem reaches_of_sub {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    (hcl : IsClosure env roots sub) {n : Ix.Name} (h : (sub.consts.get? n).isSome = true) :
    Reaches env roots n :=
  Classical.byContradiction fun hr => by
    rw [(hcl n).2 hr] at h
    cases h

/-- An input constant is stored under its own name. -/
theorem get_own {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (compiled : compileReport env = .ok (ixe, failures)) {x : Ix.Name} {ci : Ix.ConstantInfo}
    (h : env.consts.get? x = some ci) : env.consts.get? ci.getCnst.name = some ci := by
  obtain ⟨k, hk⟩ := SourceStoredNames.lookup_stored h
  rw [inputsNamed compiled k ci hk]
  exact SourceStoredNames.stored_get hk

/-- Two arrays of names equal up to `beqRaw` are equal. -/
theorem eq_of_isEqv_raw {xs ys : Array Ix.Name} (h : xs.isEqv ys Ix.Name.beqRaw = true) : xs = ys := by
  obtain ⟨hsize, hall⟩ := Array.isEqv_iff_rel.mp h
  exact Array.ext hsize fun i h₁ h₂ => Ix.Name.beqRaw_iff.mp (hall i h₁)

/-! ## The two blocks -/

/-- **A compile block holding one of a Source inductive group's types holds exactly the group's
types and constructors.** -/
theorem inductive_block_at {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ) (fb : FamilyBlocks env)
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint} {i : Nat}
    {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)} {recs : Array Ix.RecursorVal}
    (hgr : (quotientGraph ixe t hints sub).groups[i]? = some (.inductive types ctors recs))
    {rep : Ix.Name} {all : Ix.Set Ix.Name} (hall : (CompiledRefs.envBlocks env).blocks.get? rep = some all)
    {j : Nat} (hj : j < types.size) (hn : all.contains types[j].cnst.name = true) :
    ∀ x, all.contains x = true ↔
      (∃ (i : Nat) (_ : i < types.size), (types[i].cnst.name == x) = true) ∨
      ∃ (i : Nat) (hi : i < ctors.size) (k : Nat) (_ : k < ctors[i].size), (ctors[i][k].cnst.name == x) = true := by
  have hcl : IsClosure env roots sub := P.source.1
  have hmem : Group.inductive types ctors recs ∈ groupsOf sub (blocksOf sub) := Array.mem_of_getElem? hgr
  obtain ⟨n, v, hnv, -, hg⟩ := inductive_origin hmem
  rcases inductiveGroup_shape hg with ⟨_, _, e⟩ | ⟨_, _, _, e, htypes, hctors, -⟩
  · cases e
  obtain ⟨e₁, e₂, -⟩ := Group.inductive.inj e
  rw [← e₁] at htypes hctors
  rw [← e₂] at hctors
  -- a looked-up closure constant's name is the lookup's
  have nameS : ∀ {m : Ix.Name} {ci : Ix.ConstantInfo}, sub.consts.get? m = some ci →
      (ci.getCnst.name == m) = true := fun hm => named_of_get P.compiled (hcl.mem_env hm)
  -- the types and the block's names
  have T1 := ReaderUnits.forall₂_mem_right htypes
  have T2 := SourceDeclares.forall₂_mem_left htypes
  have C1 := ReaderUnits.forall₂_mem_right hctors
  have C2 := SourceDeclares.forall₂_mem_left hctors
  obtain ⟨m₀, -, hget₀, heqv₀⟩ := T1 types[j] (Array.mem_toList_iff.mpr (Array.getElem_mem hj))
  have hjE : env.consts.get? types[j].cnst.name = some (.inductInfo types[j]) :=
    get_own P.compiled (hcl.mem_env hget₀)
  have fam := (fb rep all hall _ hn).1 types[j] hjE
  rw [eq_of_isEqv_raw heqv₀] at fam
  refine fun x => (fam x).trans ?_
  constructor
  · rintro (⟨m, hm, hmx⟩ | ⟨m, hm, iv, hiv, c, hc, hcx⟩)
    · obtain ⟨ty, hty, hget, -⟩ := T2 m (Array.mem_toList_iff.mpr hm)
      obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hty)
      exact .inl ⟨j, hj, BEq.trans (nameS hget) hmx⟩
    · obtain ⟨ty, hty, hget, -⟩ := T2 m (Array.mem_toList_iff.mpr hm)
      have hivty : iv = ty := by
        rw [hcl.mem_env hget] at hiv
        exact (Ix.ConstantInfo.inductInfo.inj (Option.some.inj hiv)).symm
      rw [hivty] at hc
      obtain ⟨cs, hcs, hall₂⟩ := C2 ty hty
      obtain ⟨jc, hjc, rfl⟩ := Array.mem_iff_getElem.mp hc
      obtain ⟨cv, hcv, hcget, -⟩ := SourceDeclares.forall₂_mem_left hall₂ (ty.ctors[jc], jc)
        (Array.mem_toList_iff.mpr (Array.mem_zipIdx_iff_getElem?.mpr (Array.getElem?_eq_getElem hjc)))
      obtain ⟨a, ha, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hcs)
      obtain ⟨b, hb, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hcv)
      exact .inr ⟨a, ha, b, hb, BEq.trans (nameS hcget) hcx⟩
  · rintro (⟨j, hj, hjx⟩ | ⟨a, ha, b, hb, hbx⟩)
    · obtain ⟨m, hm, hget, -⟩ := T1 types[j] (Array.mem_toList_iff.mpr (Array.getElem_mem hj))
      exact .inl ⟨m, Array.mem_toList_iff.mp hm, BEq.trans (BEq.symm (nameS hget)) hjx⟩
    · obtain ⟨ty, hty, hall₂⟩ := C1 ctors[a] (Array.mem_toList_iff.mpr (Array.getElem_mem ha))
      obtain ⟨p, hp, hpget, -, -⟩ := ReaderUnits.forall₂_mem_right hall₂ ctors[a][b]
        (Array.mem_toList_iff.mpr (Array.getElem_mem hb))
      obtain ⟨m, hm, hget, -⟩ := T1 ty hty
      have hpc : p.1 ∈ ty.ctors := Array.mem_of_getElem? (Array.mem_zipIdx_iff_getElem?.mp
        (Array.mem_toList_iff.mp hp))
      exact .inr ⟨m, Array.mem_toList_iff.mp hm, ty, hcl.mem_env hget, p.1, hpc,
        BEq.trans (BEq.symm (nameS hpget)) hbx⟩

/-- **The compile block of a Source inductive group's first type holds exactly the group's types
and constructors.** -/
theorem inductive_block {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ) (fb : FamilyBlocks env)
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint} {i : Nat}
    {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)} {recs : Array Ix.RecursorVal}
    (hgr : (quotientGraph ixe t hints sub).groups[i]? = some (.inductive types ctors recs)) :
    ∃ (rep₁ : Ix.Name) (all₁ : Ix.Set Ix.Name), (CompiledRefs.envBlocks env).blocks.get? rep₁ = some all₁ ∧
      ∀ x, all₁.contains x = true ↔
        (∃ (i : Nat) (_ : i < types.size), (types[i].cnst.name == x) = true) ∨
        ∃ (i : Nat) (hi : i < ctors.size) (k : Nat) (_ : k < ctors[i].size), (ctors[i][k].cnst.name == x) = true := by
  have hcl : IsClosure env roots sub := P.source.1
  have hmem : Group.inductive types ctors recs ∈ groupsOf sub (blocksOf sub) := Array.mem_of_getElem? hgr
  obtain ⟨n, v, hnv, head, hg⟩ := inductive_origin hmem
  rcases inductiveGroup_shape hg with ⟨_, _, e⟩ | ⟨_, _, _, e, htypes, -, -⟩
  · cases e
  rw [← (Group.inductive.inj e).1] at htypes
  have hnS : sub.consts.get? n = some (.inductInfo v) := SourceStoredNames.stored_get hnv
  have hnE : env.consts.get? n = some (.inductInfo v) := hcl.mem_env hnS
  obtain ⟨rep, all, hall, hn⟩ := GroupBlocks.member_of_claim P (by rw [hnS]; rfl)
    (fun cv h => by rw [hnE] at h; cases h)
  -- the block's first member is a type of the group
  obtain ⟨ty, hty, hget, -⟩ := SourceDeclares.forall₂_mem_left htypes n
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? head))
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hty)
  have hjn : (types[j].cnst.name == n) = true := named_of_get P.compiled (hcl.mem_env hget)
  exact ⟨rep, all, hall, inductive_block_at P fb hgr hall hj (by rw [Std.HashSet.contains_congr hjn]; exact hn)⟩

/-- **A compile block holding one of a Source inductive group's recursors holds exactly the group's
recursors.** -/
theorem recursor_block_at {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ) (fb : FamilyBlocks env)
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint} {i : Nat}
    {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)} {recs : Array Ix.RecursorVal}
    (hgr : (quotientGraph ixe t hints sub).groups[i]? = some (.inductive types ctors recs))
    {rep : Ix.Name} {all : Ix.Set Ix.Name} (hall : (CompiledRefs.envBlocks env).blocks.get? rep = some all)
    {j₀ : Nat} (hj₀ : j₀ < recs.size) (hx₀ : all.contains recs[j₀].cnst.name = true) :
    ∀ x, all.contains x = true ↔ ∃ (j : Nat) (_ : j < recs.size), (recs[j].cnst.name == x) = true := by
  have hcl : IsClosure env roots sub := P.source.1
  obtain ⟨-, pre, ds, -, hprep, -⟩ := P.source
  have hcol := SourceDeclares.preparedAt_collapsed hprep
  have hmem : Group.inductive types ctors recs ∈ groupsOf sub (blocksOf sub) := Array.mem_of_getElem? hgr
  obtain ⟨n, v, hnv, head, hg⟩ := inductive_origin hmem
  have hrecs : blockRecursors v ((recsTable sub).getD n #[]) = .ok recs := by
    rcases inductiveGroup_shape hg with ⟨_, _, e⟩ | ⟨_, _, _, e, -, -, hrecs⟩
    · cases e
    · rw [(Group.inductive.inj e).2.2]
      exact hrecs
  have hnS : sub.consts.get? n = some (.inductInfo v) := SourceStoredNames.stored_get hnv
  have hnE : env.consts.get? n = some (.inductInfo v) := hcl.mem_env hnS
  -- the group's recursors are stored recursors of the block
  have cand : ∀ r ∈ recs, ∃ k, (k, Ix.ConstantInfo.recInfo r) ∈ sub.consts.toList ∧ r.all[0]? = some n :=
    fun r hr => recsTable_mem (SourceStoredNames.blockRecursors_mem hrecs r hr)
  obtain ⟨k₀, hk₀, hr₀n⟩ := cand recs[j₀] (Array.getElem_mem hj₀)
  have hk₀E := SourceStoredNames.stored_input P hk₀
  have hk₀name : recs[j₀].cnst.name = k₀ := inputsNamed P.compiled k₀ _ hk₀E
  obtain ⟨first, _, hfirst, -, -, -, fam⟩ := (fb rep all hall _ hx₀).2.2 recs[j₀]
    (by rw [hk₀name]; exact SourceStoredNames.stored_get hk₀E)
  have hfn : first = n := Option.some.inj (hfirst.symm.trans hr₀n)
  rw [hfn] at fam
  refine fun x => (fam x).trans ⟨?_, ?_⟩
  · rintro ⟨rv, hx, hrv⟩
    -- the recursor is in the closure
    have reach : Reaches env roots x :=
      .step (reaches_of_sub hcl (by rw [hnS]; rfl)) ⟨_, hnE, .inr (.inr (.inr ⟨n, rv, head, hx, hrv⟩))⟩
    have hxS : sub.consts.get? x = some (.recInfo rv) := ((hcl x).1 reach).trans hx
    obtain ⟨kx, hkx⟩ := SourceStoredNames.lookup_stored hxS
    have hkxE := SourceStoredNames.stored_input P hkx
    have hxname : (rv.cnst.name == x) = true := named_of_get P.compiled hx
    -- and in a group that converts, which is this one
    obtain ⟨g', hg', hkxg'⟩ := SourceDeclares.stored_grouped sub (blocksOf sub) hkx
    obtain ⟨c', hc'⟩ := SourceStoredNames.prepared_converts hcol g' hg'
    -- a stored constant named `kx` is the recursor
    have only : ∀ {m : Ix.Name} {ci : Ix.ConstantInfo}, sub.consts.get? m = some ci → ci.getCnst.name = kx →
        ci = .recInfo rv := fun hm hname => same_stored P.compiled hkxE (hcl.mem_env hm) hname
    rcases groups_origin sub (blocksOf sub) g' hg' with ⟨n', v', hnv', -, hg''⟩ | ⟨_, _, -, hcomp⟩ |
        ⟨m, ci, rfl⟩
    · rcases inductiveGroup_shape hg'' with ⟨_, _, rfl⟩ | ⟨types', ctors', recs', rfl, htypes', hctors', hrecs'⟩
      · cases hc'
      simp only [Group.names, Array.mem_append, Array.mem_map, Array.mem_flatMap] at hkxg'
      rcases hkxg' with (⟨ty, hty, e⟩ | ⟨cs, hcs, cv, hcv, e⟩) | ⟨r', hr', e⟩
      · obtain ⟨_, -, hget, -⟩ := ReaderUnits.forall₂_mem_right htypes' ty (Array.mem_toList_iff.mpr hty)
        cases only hget e
      · obtain ⟨_, -, hall₂⟩ := ReaderUnits.forall₂_mem_right hctors' cs (Array.mem_toList_iff.mpr hcs)
        obtain ⟨_, -, hget, -⟩ := ReaderUnits.forall₂_mem_right hall₂ cv (Array.mem_toList_iff.mpr hcv)
        cases only hget e
      · -- the recursor is a candidate of the group at `n'`, so `n' = n` and the group is this one
        obtain ⟨k', hk', hr'n'⟩ := recsTable_mem (SourceStoredNames.blockRecursors_mem hrecs' r' hr')
        have hr'rv : r' = rv := Ix.ConstantInfo.recInfo.inj (only (SourceStoredNames.stored_get hk') e)
        have hnn : n' = n := by
          rw [hr'rv, hrv] at hr'n'
          exact (Option.some.inj hr'n').symm
        rw [hnn] at hnv' hg''
        have hvv : v' = v := by
          have h₁ := SourceStoredNames.stored_get hnv'
          rw [SourceStoredNames.stored_get hnv] at h₁
          exact (Ix.ConstantInfo.inductInfo.inj (Option.some.inj h₁)).symm
        rw [hvv] at hg''
        have e₃ := (Group.inductive.inj (hg.symm.trans hg'')).2.2
        rw [← e₃, hr'rv] at hr'
        obtain ⟨j, hj, hjr⟩ := Array.mem_iff_getElem.mp hr'
        exact ⟨j, hj, by rw [hjr]; exact hxname⟩
    · rcases componentGroup_cases hcomp with hC | ⟨_, _, rfl⟩
      · obtain ⟨names, nofam, -⟩ := GroupBlocks.component_names hcomp hC
        obtain ⟨k, ci, hk, hci, e⟩ := (names kx).mp hkxg'
        have := nofam k ci hk hci
        rw [only hci e.symm] at this
        cases this
      · cases hc'
    · unfold unplaced at hc'
      split at hc' <;> cases hc'
  · rintro ⟨j, hj, hjx⟩
    obtain ⟨k, hk, hkn⟩ := cand recs[j] (Array.getElem_mem hj)
    have hkE := SourceStoredNames.stored_input P hk
    have hname : recs[j].cnst.name = k := inputsNamed P.compiled k _ hkE
    rw [hname] at hjx
    refine ⟨recs[j], ?_, hkn⟩
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_congr (BEq.symm hjx), ← Std.HashMap.get?_eq_getElem?]
    exact SourceStoredNames.stored_get hkE

/-- **The compile block of a Source inductive group's recursor holds exactly the group's
recursors.** -/
theorem recursor_block {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ) (fb : FamilyBlocks env)
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint} {i : Nat}
    {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)} {recs : Array Ix.RecursorVal}
    (hgr : (quotientGraph ixe t hints sub).groups[i]? = some (.inductive types ctors recs)) :
    ∃ (rep₂ : Ix.Name) (all₂ : Ix.Set Ix.Name), (CompiledRefs.envBlocks env).blocks.get? rep₂ = some all₂ ∧
      ∀ x, all₂.contains x = true ↔ ∃ (j : Nat) (_ : j < recs.size), (recs[j].cnst.name == x) = true := by
  have hmem : Group.inductive types ctors recs ∈ groupsOf sub (blocksOf sub) := Array.mem_of_getElem? hgr
  obtain ⟨n, v, -, head, hg⟩ := inductive_origin hmem
  have hrecs : blockRecursors v ((recsTable sub).getD n #[]) = .ok recs := by
    rcases inductiveGroup_shape hg with ⟨_, _, e⟩ | ⟨_, _, _, e, -, -, hrecs⟩
    · cases e
    · rw [(Group.inductive.inj e).2.2]
      exact hrecs
  obtain ⟨r₀, hr₀⟩ := blockRecursors_nonempty hrecs head
  obtain ⟨j₀, hj₀, rfl⟩ := Array.mem_iff_getElem.mp hr₀
  obtain ⟨k₀, hk₀, -⟩ := recsTable_mem (SourceStoredNames.blockRecursors_mem hrecs _ hr₀)
  have hk₀E := SourceStoredNames.stored_input P hk₀
  have hk₀name : recs[j₀].cnst.name = k₀ := inputsNamed P.compiled k₀ _ hk₀E
  obtain ⟨rep, all, hall, hk₀all⟩ := GroupBlocks.member_of_claim P
    (by rw [SourceStoredNames.stored_get hk₀]; rfl)
    (fun cv h => by rw [SourceStoredNames.stored_get hk₀E] at h; cases h)
  exact ⟨rep, all, hall, recursor_block_at P fb hgr hall hj₀ (by rw [hk₀name]; exact hk₀all)⟩

end Ix.Cert.FamilyGroups
