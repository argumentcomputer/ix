import Ix.Kernel.DefinitionDependencies
import Ix.Kernel.Verify.Expr

/-!
The dependency certificate returned by the production admission check.
Every completed declaration is fresh and all its direct dependencies occur
earlier. Root coverage is carried through the actual depth-first worklist.
Lookup agreement may be instantiated with a concrete immutable source model;
the unconditional ordering theorem does not assume declaration validity.
-/

namespace Ix.Kernel

namespace DefinitionDependencies

def Listed (address : Address) (entries : Array (KId m × KConst m)) : Prop :=
  address ∈ entries.toList.map (fun entry => entry.1.addr)

@[simp] theorem listed_empty : ¬ Listed address (#[] : Array (KId m × KConst m)) := by
  simp [Listed]

@[simp] theorem listed_push {entries : Array (KId m × KConst m)}
    {id : KId m} {declaration : KConst m} :
    Listed address (entries.push (id, declaration)) ↔
      Listed address entries ∨ address = id.addr := by
  simp [Listed]

theorem listed_of_mem {entries : Array (KId m × KConst m)}
    {entry : KId m × KConst m} (member : entry ∈ entries) : Listed entry.1.addr entries :=
  List.mem_map.mpr ⟨entry, by simpa using member, rfl⟩

/-- An inductive topological order: each appended declaration is fresh and
all the references collected from its type and value are already present. -/
inductive Ordered : Array (KId m × KConst m) → Prop where
  | empty : Ordered #[]
  | push {entries : Array (KId m × KConst m)} {id : KId m} {declaration : KConst m}
      (prior : Ordered entries) (fresh : ¬ Listed id.addr entries)
      (dependencies : ∀ dependency ∈ declaration.definitionDependencies,
        Listed dependency.addr entries) : Ordered (entries.push (id, declaration))

theorem Ordered.closed {entries : Array (KId m × KConst m)} (ordered : Ordered entries) :
    ∀ entry ∈ entries, ∀ dependency ∈ entry.2.definitionDependencies,
      Listed dependency.addr entries := by
  induction ordered with
  | empty => simp
  | @push entries id declaration prior fresh dependencies ih =>
      intro entry member dependency dependencyMember
      simp only [Array.mem_push] at member
      apply listed_push.mpr
      left
      rcases member with member | member
      · exact ih entry member dependency dependencyMember
      · cases member; exact dependencies dependency dependencyMember

/-- A natural-number rank decreases strictly along every recorded edge.
This converts the incremental certificate into a well-founded dependency
relation, without assuming that the declarations have already been checked. -/
theorem Ordered.ranked {entries : Array (KId m × KConst m)} (ordered : Ordered entries) :
    ∃ rank : Address → Nat,
      (∀ address, Listed address entries → rank address < entries.size) ∧
      (∀ entry ∈ entries, ∀ dependency ∈ entry.2.definitionDependencies,
        rank dependency.addr < rank entry.1.addr) := by
  classical
  induction ordered with
  | empty => exact ⟨fun _ => 0, by simp, by simp⟩
  | @push entries id declaration prior fresh dependencies ih =>
      obtain ⟨rank, bound, decreasing⟩ := ih
      have different (address : Address) (listed : Listed address entries) : address ≠ id.addr := by
        intro equality
        subst address
        exact fresh listed
      refine ⟨fun address => if address = id.addr then entries.size else rank address, ?_, ?_⟩
      · intro address listed
        rcases listed_push.mp listed with listed | equality
        · simp only [if_neg (different address listed), Array.size_push]
          exact Nat.lt_succ_of_lt (bound address listed)
        · subst address
          simp
      · intro entry member dependency dependencyMember
        simp only [Array.mem_push] at member
        rcases member with member | equality
        · simp only [if_neg (different entry.1.addr (listed_of_mem member)),
            if_neg (different dependency.addr (prior.closed entry member dependency dependencyMember))]
          exact decreasing entry member dependency dependencyMember
        · cases equality
          simp only [if_neg (different dependency.addr
            (dependencies dependency dependencyMember))]
          exact bound dependency.addr (dependencies dependency dependencyMember)

def Edge (entries : Array (KId m × KConst m)) (dependency user : Address) : Prop :=
  ∃ entry ∈ entries, entry.1.addr = user ∧
    ∃ target ∈ entry.2.definitionDependencies, target.addr = dependency

theorem Ordered.wellFounded {entries : Array (KId m × KConst m)}
    (ordered : Ordered entries) : WellFounded (Edge entries) := by
  obtain ⟨rank, _, decreasing⟩ := ordered.ranked
  apply Subrelation.wf (r := InvImage Nat.lt rank) ?_ (InvImage.wf rank Nat.lt_wfRel.wf)
  rintro dependency user ⟨entry, member, rfl, target, targetMember, rfl⟩
  exact decreasing entry member target targetMember

def TaskAddress : DefinitionDependencyTask m → Address
  | .enter id | .finish id _ => id.addr

def Queued (address : Address) (pending : List (DefinitionDependencyTask m)) : Prop :=
  address ∈ pending.map TaskAddress

@[simp] theorem queued_nil : ¬ Queued address ([] : List (DefinitionDependencyTask m)) := by
  simp [Queued]

@[simp] theorem queued_cons : Queued address (task :: pending) ↔
    address = TaskAddress task ∨ Queued address pending := by
  simp [Queued]

@[simp] theorem queued_append : Queued address (left ++ right) ↔
    Queued address left ∨ Queued address right := by
  simp [Queued]

structure WalkInvariant (read : KId m → KConst m → Prop)
    (roots : Array (KId m)) (walk : DefinitionDependencyState m) : Prop where
  ordered : Ordered walk.ordered
  finished : ∀ address, walk.finished.contains address = true ↔ Listed address walk.ordered
  reads : ∀ entry ∈ walk.ordered, read entry.1 entry.2
  pendingReads : ∀ id declaration, .finish id declaration ∈ walk.pending → read id declaration
  covers : ∀ root ∈ roots,
    walk.finished.contains root.addr = true ∨ Queued root.addr walk.pending

/-- The certificate refers to the declarations actually obtained by lookup. -/
structure Certificate (read : KId m → KConst m → Prop)
    (roots : Array (KId m)) (entries : Array (KId m × KConst m)) : Prop where
  ordered : Ordered entries
  covers : ∀ root ∈ roots, Listed root.addr entries
  reads : ∀ entry ∈ entries, read entry.1 entry.2

private theorem bind_success {α β : Type} {action : TcM m α}
    {next : α → TcM m β} {before after : TcState m} {result : β}
    (run : EStateM.bind action next before = .ok result after) :
    ∃ value middle, action before = .ok value middle ∧ next value middle = .ok result after := by
  unfold EStateM.bind at run
  cases step : action before with
  | error error state => rw [step] at run; contradiction
  | ok value middle =>
      rw [step] at run
      exact ⟨value, middle, rfl, run⟩

private theorem finish_not_in_enters (id : KId m) (declaration : KConst m)
    (dependencies : Array (KId m)) :
    .finish id declaration ∉ dependencies.toList.map DefinitionDependencyTask.enter := by
  simp

theorem WalkInvariant.initial (read : KId m → KConst m → Prop) (roots : Array (KId m)) :
    WalkInvariant read roots { pending := roots.toList.map DefinitionDependencyTask.enter } := by
  constructor
  · exact .empty
  · intro address; simp [Listed]
  · simp
  · intro id declaration h; exact False.elim (finish_not_in_enters id declaration roots h)
  · intro root hroot
    right
    exact List.mem_map.mpr ⟨.enter root,
      List.mem_map.mpr ⟨root, by simpa using hroot, rfl⟩, rfl⟩

theorem WalkInvariant.skip {read : KId m → KConst m → Prop}
    {roots : Array (KId m)} {walk : DefinitionDependencyState m}
    (valid : WalkInvariant read roots walk) {id : KId m}
    {pending : List (DefinitionDependencyTask m)}
    (tasks : walk.pending = .enter id :: pending)
    (finished : walk.finished.contains id.addr = true) :
    WalkInvariant read roots { walk with pending } := by
  refine ⟨valid.ordered, valid.finished, valid.reads, ?_, ?_⟩
  · intro target declaration h
    exact valid.pendingReads target declaration (by rw [tasks]; exact .tail _ h)
  · intro root hroot
    rcases valid.covers root hroot with h | h
    · exact .inl h
    · rw [tasks, queued_cons] at h
      rcases h with h | h
      · exact .inl (by simpa [TaskAddress] using h ▸ finished)
      · exact .inr h

theorem WalkInvariant.enter {read : KId m → KConst m → Prop}
    {roots : Array (KId m)} {walk : DefinitionDependencyState m}
    (valid : WalkInvariant read roots walk) {id : KId m} {declaration : KConst m}
    {pending : List (DefinitionDependencyTask m)}
    (tasks : walk.pending = .enter id :: pending) (loaded : read id declaration) :
    WalkInvariant read roots { walk with
      pending := declaration.definitionDependencies.toList.map DefinitionDependencyTask.enter ++
        .finish id declaration :: pending
      active := walk.active.insert id.addr } := by
  refine ⟨valid.ordered, valid.finished, valid.reads, ?_, ?_⟩
  · intro target concrete h
    simp only [List.mem_append, List.mem_cons] at h
    rcases h with h | h | h
    · exact False.elim (finish_not_in_enters target concrete _ h)
    · cases h; exact loaded
    · exact valid.pendingReads target concrete (by rw [tasks]; exact .tail _ h)
  · intro root hroot
    rcases valid.covers root hroot with h | h
    · exact .inl h
    · right
      rw [tasks, queued_cons] at h
      exact queued_append.mpr (.inr (queued_cons.mpr h))

theorem WalkInvariant.finish {read : KId m → KConst m → Prop}
    {roots : Array (KId m)} {walk : DefinitionDependencyState m}
    (valid : WalkInvariant read roots walk) {id : KId m} {declaration : KConst m}
    {pending : List (DefinitionDependencyTask m)}
    (tasks : walk.pending = .finish id declaration :: pending)
    (fresh : walk.finished.contains id.addr = false)
    (dependencies : ∀ dependency ∈ declaration.definitionDependencies,
      walk.finished.contains dependency.addr = true) :
    WalkInvariant read roots { walk with
      pending := pending
      active := walk.active.erase id.addr
      finished := walk.finished.insert id.addr
      ordered := walk.ordered.push (id, declaration) } := by
  have loaded := valid.pendingReads id declaration (by rw [tasks]; exact .head _)
  refine ⟨.push valid.ordered ?_ ?_, ?_, ?_, ?_, ?_⟩
  · intro listed
    have := (valid.finished id.addr).mpr listed
    simp [fresh] at this
  · intro dependency h
    exact (valid.finished _).mp (dependencies dependency h)
  · intro address
    simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, listed_push]
    rw [valid.finished]
    rw [eq_comm (a := id.addr), or_comm]
  · intro entry h
    simp only [Array.mem_push] at h
    rcases h with h | h
    · exact valid.reads entry h
    · cases h; exact loaded
  · intro target concrete h
    exact valid.pendingReads target concrete (by rw [tasks]; exact .tail _ h)
  · intro root hroot
    rcases valid.covers root hroot with h | h
    · left
      simp only [Std.HashSet.contains_insert, Bool.or_eq_true]
      exact .inr h
    · rw [tasks, queued_cons] at h
      rcases h with h | h
      · left
        simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq]
        exact .inl h.symm
      · exact .inr h

/-- Successful production steps preserve the order and the exact lookup
relation. The lookup premise is operational and is used only at an actual
`getConst` call, including its returned state. -/
theorem step_certificate {read : KId m → KConst m → Prop}
    {stateInvariant : TcState m → Prop}
    (lookup : ∀ id before declaration after, stateInvariant before →
      TcM.getConst id before = .ok declaration after →
      stateInvariant after ∧ read id declaration)
    {roots : Array (KId m)} {walk : DefinitionDependencyState m}
    (valid : WalkInvariant read roots walk) {methods : Methods m}
    {before after : TcState m} (state : stateInvariant before)
    {result : RecM.BoundedStep (DefinitionDependencyState m) (Array (KId m × KConst m))}
    (run : (RecM.definitionDependencyStep walk).run methods before = .ok result after) :
    stateInvariant after ∧ match result with
      | .next next => WalkInvariant read roots next
      | .done entries => Certificate read roots entries := by
  unfold RecM.definitionDependencyStep at run
  split at run
  · rename_i tasks
    cases run
    refine ⟨state, valid.ordered, ?_, valid.reads⟩
    intro root hroot
    rcases valid.covers root hroot with h | h
    · exact (valid.finished _).mp h
    · simp [tasks] at h
  · rename_i id pending tasks
    split at run
    · rename_i finished
      cases run
      exact ⟨state, valid.skip tasks finished⟩
    · split at run
      · contradiction
      · change EStateM.bind (TcM.getConst id) _ before = _ at run
        obtain ⟨declaration, middle, loaded, run⟩ := bind_success run
        obtain ⟨nextState, read⟩ := lookup id before declaration middle state loaded
        cases run
        exact ⟨nextState, valid.enter tasks read⟩
  · rename_i id declaration pending tasks
    split at run
    · contradiction
    · rename_i guards
      have guards : walk.finished.contains id.addr = false ∧
          declaration.definitionDependencies.all
            (fun dependency => walk.finished.contains dependency.addr) = true := by
        simpa only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_true,
          Bool.not_eq_false] using guards
      cases run
      exact ⟨state, valid.finish tasks guards.1
        (Array.all_eq_true_iff_forall_mem.mp guards.2)⟩

theorem loop_certificate {read : KId m → KConst m → Prop}
    {stateInvariant : TcState m → Prop}
    (lookup : ∀ id before declaration after, stateInvariant before →
      TcM.getConst id before = .ok declaration after →
      stateInvariant after ∧ read id declaration)
    {roots : Array (KId m)} {methods : Methods m} :
    ∀ fuel {walk : DefinitionDependencyState m} (_valid : WalkInvariant read roots walk)
      {before after : TcState m} (_state : stateInvariant before)
      {entries : Array (KId m × KConst m)},
      (RecM.runBounded RecM.definitionDependencyStep fuel walk).run methods before =
        .ok entries after → stateInvariant after ∧ Certificate read roots entries
  | 0, _, _, _, _, _, _, run => by contradiction
  | fuel + 1, walk, valid, before, after, state, entries, run => by
      rw [RecM.runBounded] at run
      change EStateM.bind _ _ before = _ at run
      obtain ⟨step, middle, stepRun, rest⟩ := bind_success run
      have stepValid := step_certificate lookup valid state stepRun
      cases step with
      | next next => exact loop_certificate lookup fuel stepValid.2 stepValid.1 rest
      | done entries =>
          cases rest
          exact stepValid

theorem order_certificate {read : KId m → KConst m → Prop}
    {stateInvariant : TcState m → Prop}
    (lookup : ∀ id before declaration after, stateInvariant before →
      TcM.getConst id before = .ok declaration after →
      stateInvariant after ∧ read id declaration)
    {roots : Array (KId m)} {methods : Methods m} {before after : TcState m}
    (state : stateInvariant before) {entries : Array (KId m × KConst m)}
    (run : (RecM.definitionDependencyOrder roots).run methods before = .ok entries after) :
    stateInvariant after ∧ Certificate read roots entries :=
  loop_certificate lookup maxDefinitionDependencySteps (WalkInvariant.initial read roots) state run

/-- No validity premise is required for the actual successful traversal's
ordering or root coverage. -/
theorem order_sound {roots : Array (KId m)} {methods : Methods m}
    {before after : TcState m} {entries : Array (KId m × KConst m)}
    (run : (RecM.definitionDependencyOrder roots).run methods before = .ok entries after) :
    Certificate (fun _ _ => True) roots entries :=
  (order_certificate (stateInvariant := fun _ => True)
    (fun _ _ _ _ _ _ => ⟨trivial, trivial⟩) trivial run).2

end DefinitionDependencies
end Ix.Kernel
