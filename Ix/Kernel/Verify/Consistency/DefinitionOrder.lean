import Ix.Kernel.Check

/-!
The production definition-block guard computes a dependency order. Its
successful result contains every pending safe definition and gives every
internal dependency a strictly smaller rank. No ordering certificate is
supplied by a caller, and no claim about external dependencies is hidden in
this local block theorem.
-/

namespace Ix.Kernel.Consistency

namespace DefinitionOrder

private theorem pairwise_of_all {α : Type} {R : α → α → Prop}
    {xs : List α} (all : ∀ a ∈ xs, ∀ b ∈ xs, R a b) : xs.Pairwise R := by
  induction xs with
  | nil => exact .nil
  | cons a rest ih =>
      exact .cons (fun b hb => all a (by simp) b (by simp [hb]))
        (ih (fun b hb c hc => all b (by simp [hb]) c (by simp [hc])))

/-- Every member selected in one peeling round is independent of the
complete pending set, including itself and all other selected members. -/
theorem ready_independent {pending : List (SafeDefinition m)}
    {definition dependency : SafeDefinition m}
    (selected : definition ∈ pending.filter (SafeDefinition.ready pending))
    (member : dependency ∈ pending) : definition.mentions dependency.id = false := by
  have ready := (List.mem_filter.mp selected).2
  have noRef := List.all_eq_true.mp ready dependency member
  simpa using noRef

/-- A successful production sort preserves every member and orders all
internal references from later members to earlier members. -/
theorem order?_sound {fuel : Nat} {pending ordered : List (SafeDefinition m)}
    (run : SafeDefinition.order? fuel pending = some ordered) :
    (∀ definition, definition ∈ ordered ↔ definition ∈ pending) ∧
    (∀ definition ∈ ordered, definition.mentions definition.id = false) ∧
    ordered.Pairwise (fun definition dependency => definition.mentions dependency.id = false) := by
  induction fuel generalizing pending ordered with
  | zero =>
      cases pending with
      | nil => simp [SafeDefinition.order?] at run; subst ordered; simp
      | cons definition rest => simp [SafeDefinition.order?] at run
  | succ fuel ih =>
      cases pending with
      | nil => simp [SafeDefinition.order?] at run; subst ordered; simp
      | cons definition rest =>
          let pending := definition :: rest
          let selected := pending.filter (SafeDefinition.ready pending)
          let remaining := pending.filter fun d => !d.ready pending
          change (if selected.isEmpty then none else
            (SafeDefinition.order? fuel remaining).map (selected ++ ·)) = some ordered at run
          split at run
          · contradiction
          · cases next : SafeDefinition.order? fuel remaining with
            | none => simp [next] at run
            | some tail =>
                simp only [next, Option.map_some, Option.some.injEq] at run
                subst ordered
                obtain ⟨members, noSelf, pairwise⟩ := ih next
                have selected_mem {d : SafeDefinition m} (hd : d ∈ selected) : d ∈ pending :=
                  (List.mem_filter.mp hd).1
                have tail_mem {d : SafeDefinition m} (hd : d ∈ tail) : d ∈ pending :=
                  (List.mem_filter.mp ((members d).mp hd)).1
                refine ⟨?_, ?_, ?_⟩
                · intro d
                  simp only [List.mem_append, members, selected, remaining, List.mem_filter]
                  cases d.ready pending <;> simp [pending]
                · intro d hd
                  rcases List.mem_append.mp hd with hs | ht
                  · exact ready_independent hs (selected_mem hs)
                  · exact noSelf d ht
                · apply List.pairwise_append.mpr
                  refine ⟨pairwise_of_all (fun d hd dep hp =>
                    ready_independent hd (selected_mem hp)), pairwise, ?_⟩
                  intro d hd dep hp
                  exact ready_independent hd (tail_mem hp)

/-- Finite ranks obtained from the computed order, rather than assumed as
an environment invariant. The scope is precisely the supplied pending set. -/
theorem order?_rank {fuel : Nat} {pending ordered : List (SafeDefinition m)}
    (run : SafeDefinition.order? fuel pending = some ordered) :
    ∃ rank : SafeDefinition m → Nat,
      ∀ definition ∈ pending, ∀ dependency ∈ pending,
        definition.mentions dependency.id = true → rank dependency < rank definition := by
  classical
  obtain ⟨members, noSelf, pairwise⟩ := order?_sound run
  refine ⟨fun definition => ordered.idxOf definition, ?_⟩
  intro definition hd dependency hp mentions
  have hd := (members definition).mpr hd
  have hp := (members dependency).mpr hp
  have hdBound := List.idxOf_lt_length_of_mem hd
  have hpBound := List.idxOf_lt_length_of_mem hp
  have hdGet := List.getElem_idxOf hdBound
  have hpGet := List.getElem_idxOf hpBound
  by_contra notEarlier
  dsimp only at notEarlier
  have le : ordered.idxOf definition ≤ ordered.idxOf dependency := by omega
  by_cases same : ordered.idxOf definition = ordered.idxOf dependency
  · have equal : definition = dependency := by
      rw [← hdGet, ← hpGet]
      simp only [same]
    subst dependency
    simp [noSelf definition hd] at mentions
  · have lt : ordered.idxOf definition < ordered.idxOf dependency := by omega
    have noRef := List.pairwise_iff_getElem.mp pairwise
      (ordered.idxOf definition) (ordered.idxOf dependency) hdBound hpBound lt
    rw [hdGet, hpGet] at noRef
    simp [noRef] at mentions

theorem acyclic_rank {pending : List (SafeDefinition m)}
    (accepted : SafeDefinition.acyclic pending = true) :
    ∃ rank : SafeDefinition m → Nat,
      ∀ definition ∈ pending, ∀ dependency ∈ pending,
        definition.mentions dependency.id = true → rank dependency < rank definition := by
  unfold SafeDefinition.acyclic at accepted
  cases run : SafeDefinition.order? pending.length pending with
  | none => simp [run] at accepted
  | some ordered => exact order?_rank run

/-- Every safe declaration found at a requested member key occurs in the
computed pending set. The successful read also verifies that all other
member keys exist and contain definitions. -/
theorem member_of_read {env : KEnv m} {ids : List (KId m)}
    {pending : List (SafeDefinition m)}
    (run : env.safeDefinitions? ids = some pending)
    {id : KId m} {declaration : KConst m} {definition : SafeDefinition m}
    (member : id ∈ ids) (loaded : env.consts[id]? = some declaration)
    (safe : SafeDefinition.ofConst? id declaration = some definition) :
    definition ∈ pending := by
  induction ids generalizing pending with
  | nil => simp at member
  | cons head rest ih =>
      cases headRead : env.consts[head]? with
      | none => simp [KEnv.safeDefinitions?, headRead] at run
      | some entry =>
          cases entry <;> try simp [KEnv.safeDefinitions?, headRead] at run
          case defn name params kind safety hints levels ty val all block =>
            cases tailRead : env.safeDefinitions? rest with
            | none => simp [tailRead] at run
            | some tail =>
                cases headSafe : SafeDefinition.ofConst? head
                    (.defn name params kind safety hints levels ty val all block) with
                | none =>
                    simp only [Option.bind_some, tailRead, headSafe, Option.some.injEq] at run
                    subst pending
                    rcases List.mem_cons.mp member with same | later
                    · subst id
                      have equal := Option.some.inj (headRead.symm.trans loaded)
                      subst declaration
                      simp [headSafe] at safe
                    · exact ih tailRead later
                | some first =>
                    simp only [Option.bind_some, tailRead, headSafe, Option.some.injEq] at run
                    subst pending
                    rcases List.mem_cons.mp member with same | later
                    · subst id
                      have equal := Option.some.inj (headRead.symm.trans loaded)
                      subst declaration
                      have equal := Option.some.inj (headSafe.symm.trans safe)
                      simp [← equal]
                    · exact List.mem_cons_of_mem _ (ih tailRead later)

/-- Safe member success excludes self-reference in both the type and value,
for arbitrary universe arities and either kernel representation mode. -/
theorem member_no_self {methods : Methods m} {id : KId m} {constant : KConst m}
    {definition : SafeDefinition m} {before after : TcState m}
    (selected : SafeDefinition.ofConst? id constant = some definition)
    (run : (RecM.checkConstMember id constant).run methods before = .ok () after) :
    definition.mentions id = false := by
  cases constant <;> try simp [SafeDefinition.ofConst?] at selected
  case defn name params kind safety hints levels ty val all block =>
    cases safety <;> try simp at selected
    case safe =>
      subst definition
      unfold RecM.checkConstMember at run
      simp only [KConst.levelParams] at run
      by_cases duplicates : params.hasDups
      · simp only [duplicates, if_true] at run
        contradiction
      · simp only [duplicates, Bool.false_eq_true, if_false, ReaderT.run_bind] at run
        change EStateM.bind ((RecM.validateConstWellScoped
          (.defn name params kind .safe hints levels ty val all block)).run methods)
          _ before = _ at run
        unfold EStateM.bind at run
        cases validated : (RecM.validateConstWellScoped
            (.defn name params kind .safe hints levels ty val all block)).run methods before with
        | error error state => rw [validated] at run; contradiction
        | ok _ state =>
            rw [validated] at run
            change (exprMentionsAddr ty id.addr || exprMentionsAddr val id.addr) = false
            cases mentions : (exprMentionsAddr ty id.addr || exprMentionsAddr val id.addr) with
            | false => rfl
            | true =>
                have same : ((Ix.DefinitionSafety.safe : Ix.DefinitionSafety) == .safe) = true := rfl
                simp only [same, Bool.true_and, mentions, if_true] at run
                contradiction

/-- The guard is extracted from the exact production block execution. It
runs before member checking and leaves the state unchanged. -/
theorem block_guard {methods : Methods m} {block : KId m}
    {members : Array (KId m)} {before after : TcState m}
    (run : (RecM.checkClassifiedBlock .defn block members).run methods before =
      .ok () after) : before.env.definitionBlockAcyclic members = true := by
  cases guard : before.env.definitionBlockAcyclic members with
  | true => rfl
  | false =>
      have same : ((CheckBlockKind.defn : CheckBlockKind) != .defn) = false := rfl
      simp only [RecM.checkClassifiedBlock, same, Bool.false_eq_true, if_false,
        ReaderT.run_bind] at run
      change ((if (!before.env.definitionBlockAcyclic members) = true then _ else _) :
        RecM m Unit).run methods before = EStateM.Result.ok () after at run
      simp only [guard, Bool.not_false, if_true] at run
      contradiction

/-- Actual block success supplies the pending declarations and their finite
rank function. Neither is an additional acceptance premise. -/
theorem block_rank {methods : Methods m} {block : KId m}
    {members : Array (KId m)} {before after : TcState m}
    (run : (RecM.checkClassifiedBlock .defn block members).run methods before =
      .ok () after) :
    ∃ pending : List (SafeDefinition m), ∃ rank : SafeDefinition m → Nat,
      before.env.safeDefinitions? members.toList = some pending ∧
      ∀ definition ∈ pending, ∀ dependency ∈ pending,
        definition.mentions dependency.id = true → rank dependency < rank definition := by
  have accepted := block_guard run
  unfold KEnv.definitionBlockAcyclic at accepted
  cases read : before.env.safeDefinitions? members.toList with
  | none => simp [read] at accepted
  | some pending =>
      simp only [read] at accepted
      obtain ⟨rank, descending⟩ := acyclic_rank accepted
      exact ⟨pending, rank, rfl, descending⟩

/-- A safe definition actually loaded at a member key of this block. -/
def LoadedMember (env : KEnv m) (members : Array (KId m))
    (definition : SafeDefinition m) : Prop :=
  definition.id ∈ members ∧ ∃ declaration,
    env.consts[definition.id]? = some declaration ∧
      SafeDefinition.ofConst? definition.id declaration = some definition

/-- Dependency direction: the referenced declaration precedes its user. -/
def Dependency (env : KEnv m) (members : Array (KId m))
    (dependency definition : SafeDefinition m) : Prop :=
  LoadedMember env members definition ∧ LoadedMember env members dependency ∧
    definition.mentions dependency.id = true

/-- No cycle of safe definitions can be hidden inside a successfully checked
definition block. The relation reads the actual pre-check environment. -/
theorem block_wellFounded {methods : Methods m} {block : KId m}
    {members : Array (KId m)} {before after : TcState m}
    (run : (RecM.checkClassifiedBlock .defn block members).run methods before =
      .ok () after) : WellFounded (Dependency before.env members) := by
  obtain ⟨pending, rank, read, descending⟩ := block_rank run
  refine Subrelation.wf (r := fun dependency definition => rank dependency < rank definition)
    ?_ (InvImage.wf rank Nat.lt_wfRel.wf)
  intro dependency definition edge
  rcases edge with ⟨⟨hd, cd, hdRead, hdSafe⟩, ⟨hp, cp, hpRead, hpSafe⟩, mentions⟩
  exact descending definition (member_of_read read (by simpa using hd) hdRead hdSafe)
    dependency (member_of_read read (by simpa using hp) hpRead hpSafe) mentions

private theorem accessible_no_self {α : Sort u} {relation : α → α → Prop}
    {value : α} (accessible : Acc relation value) : ¬relation value value := by
  induction accessible with
  | intro value _ ih =>
      intro cycle
      exact ih value cycle cycle

/-- Explicit exclusion of every nonempty dependency cycle, of any length. -/
theorem block_no_cycle {methods : Methods m} {block : KId m}
    {members : Array (KId m)} {before after : TcState m}
    (run : (RecM.checkClassifiedBlock .defn block members).run methods before =
      .ok () after) (definition : SafeDefinition m) :
    ¬Relation.TransGen (Dependency before.env members) definition definition :=
  accessible_no_self ((block_wellFounded run).transGen.apply definition)

end DefinitionOrder

end Ix.Kernel.Consistency
