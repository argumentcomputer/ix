import Ix.CompileCert.ExpressionState
import Ix.CompileCert.PreseedKeys

/-! Successful preseed collection retains every required external reference
and literal address, relative to its fixed lookup bindings. The proof covers
all expression constructors and the root loop, and derives cache readiness
from empty initialization. Universe coverage, sorting/insertion and source
semantic correspondence remain separate obligations. -/

namespace Ix.CompileCert.PreseedReferences

open Ix Ix.CompileM Ix.CompileCert.HeadWriterFrame

abbrev BindingFrame (action : CompileM α) : Prop := UniversePipeline.Preserves ExpressionState.bindingView action

theorem BindingFrame.compileUniv (source : Level) : BindingFrame (compileUniv source) := by
  intro context before
  have frame := UniversePipeline.compileUniv_frame source context before
  have projected := congrArg ExpressionState.bindingView frame
  exact projected

theorem BindingFrame.lookup (name : Name) : BindingFrame (lookupConstAddr name) := by
  intro context before
  rw [ExpressionState.lookupConstAddr_state]

theorem BindingFrame.blob (bytes : ByteArray) : BindingFrame (storeBlob bytes) := by
  intro context before
  have frame := (BlobWrites.storeBlob_preserves bytes context before).1
  have projected := congrArg ExpressionState.bindingView frame
  exact projected

theorem BindingFrame.levels (levels : List Level) (initial : Array Ixon.Univ) :
    BindingFrame (collectExprTableUnivs levels initial) := by
  induction levels generalizing initial with
  | nil => exact UniversePipeline.Preserves.pure _ _
  | cons level rest ih =>
    rw [collectExprTableUnivs]
    exact UniversePipeline.Preserves.bind (BindingFrame.compileUniv level) (fun value => ih (initial.push value))

theorem BindingFrame.structural (hint : Address) (mutualContext : MutCtx) (params : List Name)
    (source : Expr) (initial : ExprTableCollection) :
    BindingFrame (collectExprTablesStructural hint mutualContext params source initial) := by
  induction source generalizing initial
  all_goals try cases ‹Lean.Literal›
  all_goals
    rcases initial with ⟨refs, univs, seen⟩
    rw [collectExprTablesStructural]
    split
    · exact UniversePipeline.Preserves.pure _ _
    · with_reducible repeat' first
        | exact UniversePipeline.Preserves.pure _ _
        | exact UniversePipeline.Preserves.throw _ _
        | exact BindingFrame.compileUniv _
        | exact BindingFrame.lookup _
        | exact BindingFrame.blob _
        | exact BindingFrame.levels _ _
        | refine UniversePipeline.Preserves.bind ?_ (fun value => ?_)
        | dsimp only
        | split
        | apply_assumption

def Named (resolve : Name → Option Address) (refs : Array Address) (name : Name) : Prop :=
  ∃ address, resolve name = some address ∧ address ∈ refs

/-- Structural reference requirements of the collector. Failed name lookup
and unsupported expression forms cannot satisfy coverage vacuously. -/
def Covered (resolve : Name → Option Address) (mutualContext : MutCtx) (refs : Array Address) : Expr → Prop
  | .bvar .. | .sort .. => True
  | .const name _ _ =>
    if (mutualContext.get? name).isNone then Named resolve refs name else True
  | .app fn arg _ => Covered resolve mutualContext refs fn ∧ Covered resolve mutualContext refs arg
  | .lam _ type body _ _ | .forallE _ type body _ _ =>
    Covered resolve mutualContext refs type ∧ Covered resolve mutualContext refs body
  | .letE _ type value body _ _ =>
    Covered resolve mutualContext refs type ∧ Covered resolve mutualContext refs value ∧ Covered resolve mutualContext refs body
  | .lit (.natVal value) _ => Address.blake3 (ByteArray.mk (Nat.toBytesLE value)) ∈ refs
  | .lit (.strVal value) _ => Address.blake3 value.toUTF8 ∈ refs
  | .proj name _ value _ => Named resolve refs name ∧ Covered resolve mutualContext refs value
  | .mdata _ value _ => Covered resolve mutualContext refs value
  | .fvar .. | .mvar .. => False

theorem Named.mono {resolve : Name → Option Address} {before after : Array Address} {name : Name}
    (prior : Named resolve before name) (growth : ∀ address ∈ before, address ∈ after) : Named resolve after name := by
  obtain ⟨address, resolved, member⟩ := prior
  exact ⟨address, resolved, growth address member⟩

theorem Covered.mono (resolve : Name → Option Address) (mutualContext : MutCtx)
    (before after : Array Address) (growth : ∀ address ∈ before, address ∈ after)
    (source : Expr) (prior : Covered resolve mutualContext before source) : Covered resolve mutualContext after source := by
  induction source with
  | bvar _ _ | sort _ _ => trivial
  | fvar _ _ | mvar _ _ => exact prior.elim
  | const name levels hash =>
    dsimp only [Covered] at prior ⊢
    by_cases external : (mutualContext.get? name).isNone = true
    · simp only [external, ↓reduceIte] at prior ⊢
      exact prior.mono growth
    · rw [ite_eq_right external]
      trivial
  | app _ _ _ first second => exact ⟨first prior.1, second prior.2⟩
  | lam _ _ _ _ _ first second | forallE _ _ _ _ _ first second => exact ⟨first prior.1, second prior.2⟩
  | letE _ _ _ _ _ _ first second third => exact ⟨first prior.1, second prior.2.1, third prior.2.2⟩
  | lit value hash => cases value <;> exact growth _ prior
  | proj _ _ _ _ child => exact ⟨prior.1.mono growth, child prior.2⟩
  | mdata _ _ _ child => exact child prior

theorem lookup_value (context : CompileEnv × BlockEnv) (before : BlockState) (name : Name) (address : Address)
    (success : (rawRun (lookupConstAddr name) context before).1 = .ok address) :
    ExpressionState.lookupBinding context.1 (ExpressionState.bindingView before) name = some address := by
  rw [ExpressionState.lookupConstAddr_run] at success
  cases found : ExpressionState.lookupBinding context.1 (ExpressionState.bindingView before) name with
  | none => rw [found] at success; cases success
  | some value =>
    rw [found] at success
    cases Except.ok.inj success
    rfl

theorem named_push (context : CompileEnv × BlockEnv) (before : BlockState) (name : Name)
    (refs : Array Address) (address : Address)
    (success : (rawRun (lookupConstAddr name) context before).1 = .ok address) :
    Named (ExpressionState.lookupBinding context.1 (ExpressionState.bindingView before)) (refs.push address) name :=
  ⟨address, lookup_value context before name address success, by simp⟩

theorem blob_value (context : CompileEnv × BlockEnv) (before : BlockState) (bytes : ByteArray) (address : Address)
    (success : (rawRun (storeBlob bytes) context before).1 = .ok address) : address = Address.blake3 bytes := by
  rw [BlobWrites.storeBlob_run] at success
  cases stored : before.storeBlob context.1.blobs (Address.blake3 bytes) bytes with
  | error error => rw [stored] at success; cases success
  | ok after =>
    rw [stored] at success
    exact (Except.ok.inj success).symm

def Added (resolve : Name → Option Address) (mutualContext : MutCtx)
    (before after : PreseedKeys.Seen) (refs : Array Address) : Prop :=
  ∀ key, after.contains key = true → before.contains key = true ∨ Covered resolve mutualContext refs key.expr

theorem Added.refl (resolve : Name → Option Address) (mutualContext : MutCtx)
    (seen : PreseedKeys.Seen) (refs : Array Address) : Added resolve mutualContext seen seen refs :=
  fun _ found => Or.inl found

theorem Added.mono {resolve : Name → Option Address} {mutualContext : MutCtx}
    {before after : PreseedKeys.Seen} {first last : Array Address}
    (added : Added resolve mutualContext before after first) (growth : ∀ address ∈ first, address ∈ last) :
    Added resolve mutualContext before after last := by
  intro key found
  rcases added key found with prior | covered
  · exact Or.inl prior
  · exact Or.inr (covered.mono resolve mutualContext first last growth key.expr)

theorem Added.trans {resolve : Name → Option Address} {mutualContext : MutCtx}
    {before middle after : PreseedKeys.Seen} {first last : Array Address}
    (head : Added resolve mutualContext before middle first)
    (tail : Added resolve mutualContext middle after last)
    (growth : ∀ address ∈ first, address ∈ last) : Added resolve mutualContext before after last := by
  intro key found
  rcases tail key found with prior | covered
  · exact head.mono growth key prior
  · exact Or.inr covered

theorem Added.close_parent {resolve : Name → Option Address} {mutualContext : MutCtx}
    (key : Ix.Compile.ExactKey.PreseedKey) {before after : PreseedKeys.Seen} {refs : Array Address}
    (children : Added resolve mutualContext (before.insert key ()) after refs)
    (parent : Covered resolve mutualContext refs key.expr) : Added resolve mutualContext before after refs := by
  intro query found
  rcases children query found with pending | covered
  · rw [Std.HashMap.contains_insert, Bool.or_eq_true] at pending
    rcases pending with same | old
    · have same : key = query := eq_of_beq same
      subst query
      exact Or.inr parent
    · exact Or.inl old
  · exact Or.inr covered

theorem Added.ready {resolve : Name → Option Address} {mutualContext : MutCtx}
    {before after : PreseedKeys.Seen} {first last : Array Address} (bound : Nat)
    (ready : PreseedKeys.CoveredBelow bound (fun key => Covered resolve mutualContext first key.expr) before)
    (added : Added resolve mutualContext before after last) (growth : ∀ address ∈ first, address ∈ last) :
    PreseedKeys.CoveredBelow bound (fun key => Covered resolve mutualContext last key.expr) after := by
  intro key small found
  rcases added key found with prior | covered
  · exact (ready key small prior).mono resolve mutualContext first last growth key.expr
  · exact covered

structure Result (resolve : Name → Option Address) (mutualContext : MutCtx) (source : Expr)
    (before after : ExprTableCollection) : Prop where
  grows : ∀ address ∈ before.1, address ∈ after.1
  covered : Covered resolve mutualContext after.1 source
  added : Added resolve mutualContext before.2.2 after.2.2 after.1

theorem Result.cached (resolve : Name → Option Address) (mutualContext : MutCtx)
    (hint : Address) (params : List Name) (source : Expr) (acc : ExprTableCollection)
    (ready : PreseedKeys.CoveredBelow (sizeOf source + 1)
      (fun key => Covered resolve mutualContext acc.1 key.expr) acc.2.2)
    (hit : acc.2.2.contains ⟨source, params, hint⟩ = true) : Result resolve mutualContext source acc acc := by
  refine ⟨fun _ member => member, ?_, Added.refl resolve mutualContext acc.2.2 acc.1⟩
  exact PreseedKeys.CoveredBelow.lookup ⟨source, params, hint⟩ ready hit

theorem Result.insert (resolve : Name → Option Address) (mutualContext : MutCtx)
    (hint : Address) (params : List Name) (source : Expr) (before : ExprTableCollection)
    (refs : Array Address) (univs : Array Ixon.Univ)
    (growth : ∀ address ∈ before.1, address ∈ refs) (covered : Covered resolve mutualContext refs source) :
    Result resolve mutualContext source before (refs, univs, before.2.2.insert ⟨source, params, hint⟩ ()) := by
  refine ⟨growth, covered, ?_⟩
  exact Added.close_parent ⟨source, params, hint⟩
    (Added.refl resolve mutualContext (before.2.2.insert ⟨source, params, hint⟩ ()) refs) covered

theorem bind_ok (action : CompileM α) (next : α → CompileM β)
    (context : CompileEnv × BlockEnv) (before : BlockState) (value : β) (after : BlockState)
    (success : rawRun (action >>= next) context before = (.ok value, after)) :
    ∃ first middle, rawRun action context before = (.ok first, middle) ∧
      rawRun (next first) context middle = (.ok value, after) := by
  rw [rawRun_bind] at success
  cases ran : rawRun action context before with
  | mk outcome middle =>
    rw [ran] at success
    cases outcome with
    | error error => cases success
    | ok first => exact ⟨first, middle, rfl, success⟩

theorem prepare_child (resolve : Name → Option Address) (mutualContext : MutCtx)
    (hint : Address) (params : List Name) (parent child : Expr) (acc : ExprTableCollection)
    (ready : PreseedKeys.CoveredBelow (sizeOf parent + 1)
      (fun key => Covered resolve mutualContext acc.1 key.expr) acc.2.2)
    (smaller : sizeOf child < sizeOf parent) :
    PreseedKeys.CoveredBelow (sizeOf child + 1)
      (fun key => Covered resolve mutualContext acc.1 key.expr) (acc.2.2.insert ⟨parent, params, hint⟩ ()) := by
  have restricted := ready.restrict (after := sizeOf child + 1) (by omega)
  exact restricted.insert_above ⟨parent, params, hint⟩ (by dsimp only; omega)

theorem cached_run (resolve : Name → Option Address) (context : CompileEnv × BlockEnv)
    (before after : BlockState) (hint : Address) (mutualContext : MutCtx) (params : List Name)
    (source : Expr) (initial output : ExprTableCollection)
    (ready : PreseedKeys.CoveredBelow (sizeOf source + 1)
      (fun key => Covered resolve mutualContext initial.1 key.expr) initial.2.2)
    (hit : initial.2.2.contains ⟨source, params, hint⟩ = true)
    (ran : rawRun (collectExprTablesStructural hint mutualContext params source initial) context before = (.ok output, after)) :
    Result resolve mutualContext source initial output := by
  rcases initial with ⟨refs, univs, seen⟩
  rw [PreseedKeys.collect_hit hint mutualContext params source refs univs seen hit, rawRun_pure] at ran
  obtain ⟨equal, _⟩ := Prod.mk.inj ran
  cases Except.ok.inj equal
  exact Result.cached resolve mutualContext hint params source _ ready hit

section Collection

variable (context : CompileEnv × BlockEnv) (bindings : ExpressionState.Bindings)
  (hint : Address) (mutualContext : MutCtx) (params : List Name)
local notation "resolve" => ExpressionState.lookupBinding (Prod.fst context) bindings
local notation "collector" => collectExprTablesStructural hint mutualContext params

def Correct (source : Expr) : Prop :=
  ∀ (before after : BlockState) (initial output : ExprTableCollection),
    ExpressionState.bindingView before = bindings →
    PreseedKeys.CoveredBelow (sizeOf source + 1)
      (fun key => Covered resolve mutualContext initial.1 key.expr) initial.2.2 →
    rawRun (collector source initial) context before = (.ok output, after) →
    Result resolve mutualContext source initial output

theorem binding_after (source : Expr) (initial output : ExprTableCollection)
    (before after : BlockState) (view : ExpressionState.bindingView before = bindings)
    (ran : rawRun (collector source initial) context before = (.ok output, after)) :
    ExpressionState.bindingView after = bindings := by
  have frame := BindingFrame.structural hint mutualContext params source initial context before
  rw [ran] at frame
  exact frame.trans view

theorem binary (parent first last : Expr)
    (firstCorrect : Correct context bindings hint mutualContext params first)
    (lastCorrect : Correct context bindings hint mutualContext params last)
    (firstSmall : sizeOf first < sizeOf parent) (lastSmall : sizeOf last < sizeOf parent)
    (assemble : ∀ refs, Covered resolve mutualContext refs first →
      Covered resolve mutualContext refs last → Covered resolve mutualContext refs parent)
    (before after : BlockState) (initial output : ExprTableCollection)
    (view : ExpressionState.bindingView before = bindings)
    (ready : PreseedKeys.CoveredBelow (sizeOf parent + 1)
      (fun key => Covered resolve mutualContext initial.1 key.expr) initial.2.2)
    (ran : rawRun (do
      let middle ← collector first (initial.1, initial.2.1, initial.2.2.insert ⟨parent, params, hint⟩ ())
      collector last middle) context before = (.ok output, after)) :
    Result resolve mutualContext parent initial output := by
  obtain ⟨middle, state, firstRan, lastRan⟩ := bind_ok _ _ context before output after ran
  have firstReady := prepare_child resolve mutualContext hint params parent first initial ready firstSmall
  have checkedFirst := firstCorrect before state _ middle view firstReady firstRan
  have nextView := binding_after context bindings hint mutualContext params first _ middle before state view firstRan
  have lastReady := checkedFirst.added.ready (sizeOf last + 1)
    (prepare_child resolve mutualContext hint params parent last initial ready lastSmall) checkedFirst.grows
  have checkedLast := lastCorrect state after middle output nextView lastReady lastRan
  have parentCovered := assemble output.1
    (checkedFirst.covered.mono resolve mutualContext middle.1 output.1 checkedLast.grows first) checkedLast.covered
  refine ⟨fun address member => checkedLast.grows address (checkedFirst.grows address member), parentCovered, ?_⟩
  exact Added.close_parent ⟨parent, params, hint⟩
    (checkedFirst.added.trans checkedLast.added checkedLast.grows) parentCovered

theorem unary (parent child : Expr)
    (childCorrect : Correct context bindings hint mutualContext params child)
    (smaller : sizeOf child < sizeOf parent)
    (before after : BlockState) (initial output : ExprTableCollection)
    (refs : Array Address) (univs : Array Ixon.Univ)
    (growth : ∀ address ∈ initial.1, address ∈ refs)
    (assemble : ∀ finalRefs, (∀ address ∈ refs, address ∈ finalRefs) →
      Covered resolve mutualContext finalRefs child → Covered resolve mutualContext finalRefs parent)
    (view : ExpressionState.bindingView before = bindings)
    (ready : PreseedKeys.CoveredBelow (sizeOf parent + 1)
      (fun key => Covered resolve mutualContext initial.1 key.expr) initial.2.2)
    (ran : rawRun (collector child (refs, univs, initial.2.2.insert ⟨parent, params, hint⟩ ())) context before = (.ok output, after)) :
    Result resolve mutualContext parent initial output := by
  have childReady := (prepare_child resolve mutualContext hint params parent child initial ready smaller).mono
    (fun key covered => covered.mono resolve mutualContext initial.1 refs growth key.expr)
  have checked := childCorrect before after _ output view childReady ran
  have parentCovered := assemble output.1 checked.grows checked.covered
  exact ⟨fun address member => checked.grows address (growth address member), parentCovered,
    Added.close_parent ⟨parent, params, hint⟩ checked.added parentCovered⟩

theorem ternary (parent first middle last : Expr)
    (firstCorrect : Correct context bindings hint mutualContext params first)
    (middleCorrect : Correct context bindings hint mutualContext params middle)
    (lastCorrect : Correct context bindings hint mutualContext params last)
    (firstSmall : sizeOf first < sizeOf parent) (middleSmall : sizeOf middle < sizeOf parent)
    (lastSmall : sizeOf last < sizeOf parent)
    (assemble : ∀ refs, Covered resolve mutualContext refs first → Covered resolve mutualContext refs middle →
      Covered resolve mutualContext refs last → Covered resolve mutualContext refs parent)
    (before after : BlockState) (initial output : ExprTableCollection)
    (view : ExpressionState.bindingView before = bindings)
    (ready : PreseedKeys.CoveredBelow (sizeOf parent + 1)
      (fun key => Covered resolve mutualContext initial.1 key.expr) initial.2.2)
    (ran : rawRun (do
      let one ← collector first (initial.1, initial.2.1, initial.2.2.insert ⟨parent, params, hint⟩ ())
      let two ← collector middle one
      collector last two) context before = (.ok output, after)) :
    Result resolve mutualContext parent initial output := by
  obtain ⟨one, stateOne, firstRan, tailRan⟩ := bind_ok _ _ context before output after ran
  obtain ⟨two, stateTwo, middleRan, lastRan⟩ := bind_ok _ _ context stateOne output after tailRan
  have checkedFirst := firstCorrect before stateOne _ one view
    (prepare_child resolve mutualContext hint params parent first initial ready firstSmall) firstRan
  have viewOne := binding_after context bindings hint mutualContext params first _ one before stateOne view firstRan
  have checkedMiddle := middleCorrect stateOne stateTwo one two viewOne
    (checkedFirst.added.ready (sizeOf middle + 1)
      (prepare_child resolve mutualContext hint params parent middle initial ready middleSmall) checkedFirst.grows) middleRan
  have viewTwo := binding_after context bindings hint mutualContext params middle one two stateOne stateTwo viewOne middleRan
  have combined := checkedFirst.added.trans checkedMiddle.added checkedMiddle.grows
  have growth : ∀ address ∈ initial.1, address ∈ two.1 :=
    fun address member => checkedMiddle.grows address (checkedFirst.grows address member)
  have checkedLast := lastCorrect stateTwo after two output viewTwo
    (combined.ready (sizeOf last + 1)
      (prepare_child resolve mutualContext hint params parent last initial ready lastSmall) growth) lastRan
  have parentCovered := assemble output.1
    (checkedFirst.covered.mono resolve mutualContext one.1 output.1
      (fun address member => checkedLast.grows address (checkedMiddle.grows address member)) first)
    (checkedMiddle.covered.mono resolve mutualContext two.1 output.1 checkedLast.grows middle) checkedLast.covered
  exact ⟨fun address member => checkedLast.grows address (growth address member), parentCovered,
    Added.close_parent ⟨parent, params, hint⟩ (combined.trans checkedLast.added checkedLast.grows) parentCovered⟩

theorem Correct.of_miss (source : Expr)
    (check : ∀ (before after : BlockState) (initial output : ExprTableCollection),
      ExpressionState.bindingView before = bindings →
      PreseedKeys.CoveredBelow (sizeOf source + 1)
        (fun key => Covered resolve mutualContext initial.1 key.expr) initial.2.2 →
      ¬initial.2.2.contains ⟨source, params, hint⟩ = true →
      rawRun (collector source initial) context before = (.ok output, after) →
      Result resolve mutualContext source initial output) : Correct context bindings hint mutualContext params source := by
  intro before after initial output view ready ran
  by_cases hit : initial.2.2.contains ⟨source, params, hint⟩ = true
  · exact cached_run resolve context before after hint mutualContext params source initial output ready hit ran
  · exact check before after initial output view ready hit ran

theorem collect_correct (source : Expr) : Correct context bindings hint mutualContext params source := by
  induction source
  all_goals
    apply Correct.of_miss
    intro before after initial output view ready missing ran
    rcases initial with ⟨refs, univs, seen⟩
    rw [collectExprTablesStructural] at ran
    simp only [missing, Bool.false_eq_true, ↓reduceIte] at ran
  case bvar index hash =>
    rw [rawRun_pure] at ran
    cases Except.ok.inj (congrArg Prod.fst ran)
    exact Result.insert resolve mutualContext hint params _ _ _ _ (fun _ member => member) True.intro
  case fvar name hash => cases ran
  case mvar name hash => cases ran
  case sort level hash =>
    obtain ⟨value, middle, _, returned⟩ := bind_ok _ _ context before output after ran
    rw [rawRun_pure] at returned
    cases Except.ok.inj (congrArg Prod.fst returned)
    exact Result.insert resolve mutualContext hint params _ _ _ _ (fun _ member => member) True.intro
  case const name levels hash =>
    obtain ⟨values, middle, levelsRan, tailRan⟩ := bind_ok _ _ context before output after ran
    have middleView := BindingFrame.levels levels.toList univs context before
    rw [levelsRan] at middleView
    have aligned := middleView.trans view
    by_cases external : (mutualContext.get? name).isNone = true
    · simp only [external, ↓reduceIte] at tailRan
      obtain ⟨address, named, looked, returned⟩ := bind_ok _ _ context middle output after tailRan
      rw [rawRun_pure] at returned
      cases Except.ok.inj (congrArg Prod.fst returned)
      apply Result.insert resolve mutualContext hint params _ _ _ _ (fun _ member => by simp [member])
      change if (mutualContext.get? name).isNone = true then _ else True
      rw [ite_eq_left external]
      have found := lookup_value context middle name address (congrArg Prod.fst looked)
      rw [aligned] at found
      exact ⟨address, found, by simp⟩
    · rw [ite_eq_right external, rawRun_pure] at tailRan
      cases Except.ok.inj (congrArg Prod.fst tailRan)
      apply Result.insert resolve mutualContext hint params _ _ _ _ (fun _ member => member)
      change if (mutualContext.get? name).isNone = true then _ else True
      rw [ite_eq_right external]
      trivial
  case app first last hash firstIH lastIH =>
    exact binary context bindings hint mutualContext params (.app first last hash) first last firstIH lastIH
      (by simp_wf; omega) (by simp_wf; omega) (fun _ a b => ⟨a, b⟩) before after _ output view ready ran
  case lam name type body info hash typeIH bodyIH =>
    exact binary context bindings hint mutualContext params (.lam name type body info hash) type body typeIH bodyIH
      (by simp_wf; omega) (by simp_wf; omega) (fun _ a b => ⟨a, b⟩) before after _ output view ready ran
  case forallE name type body info hash typeIH bodyIH =>
    exact binary context bindings hint mutualContext params (.forallE name type body info hash) type body typeIH bodyIH
      (by simp_wf; omega) (by simp_wf; omega) (fun _ a b => ⟨a, b⟩) before after _ output view ready ran
  case letE name type value body nonDep hash typeIH valueIH bodyIH =>
    exact ternary context bindings hint mutualContext params (.letE name type value body nonDep hash)
      type value body typeIH valueIH bodyIH (by simp_wf; omega) (by simp_wf; omega) (by simp_wf; omega)
      (fun _ a b c => ⟨a, b, c⟩) before after _ output view ready ran
  case lit literal hash =>
    cases literal with
    | natVal value =>
      obtain ⟨address, middle, stored, returned⟩ := bind_ok _ _ context before output after ran
      rw [rawRun_pure] at returned
      cases Except.ok.inj (congrArg Prod.fst returned)
      apply Result.insert resolve mutualContext hint params _ _ _ _ (fun _ member => by simp [member])
      have same := blob_value context before (ByteArray.mk (Nat.toBytesLE value)) address (congrArg Prod.fst stored)
      change Address.blake3 (ByteArray.mk (Nat.toBytesLE value)) ∈ refs.push address
      rw [← same]
      simp
    | strVal value =>
      obtain ⟨address, middle, stored, returned⟩ := bind_ok _ _ context before output after ran
      rw [rawRun_pure] at returned
      cases Except.ok.inj (congrArg Prod.fst returned)
      apply Result.insert resolve mutualContext hint params _ _ _ _ (fun _ member => by simp [member])
      have same := blob_value context before value.toUTF8 address (congrArg Prod.fst stored)
      change Address.blake3 value.toUTF8 ∈ refs.push address
      rw [← same]
      simp
  case mdata metadata child hash childIH =>
    exact unary context bindings hint mutualContext params (.mdata metadata child hash) child childIH
      (by simp_wf; omega) before after _ output refs univs (fun _ member => member)
      (fun _ _ covered => covered) view ready ran
  case proj name index child hash childIH =>
    obtain ⟨address, middle, looked, childRan⟩ := bind_ok _ _ context before output after ran
    have same := ExpressionState.lookupConstAddr_state name context before
    rw [looked] at same
    dsimp only at same
    subst middle
    have named := named_push context before name refs address (congrArg Prod.fst looked)
    rw [view] at named
    exact unary context bindings hint mutualContext params (.proj name index child hash) child childIH
      (by simp_wf; omega) before after _ output (refs.push address) univs (fun _ member => by simp [member])
      (fun _ grows covered => ⟨named.mono grows, covered⟩) view ready childRan

end Collection

def Complete (resolve : Name → Option Address) (mutualContext : MutCtx) (acc : ExprTableCollection) : Prop :=
  ∀ key, acc.2.2.contains key = true → Covered resolve mutualContext acc.1 key.expr

theorem Complete.empty (resolve : Name → Option Address) (mutualContext : MutCtx)
    (refs : Array Address) (univs : Array Ixon.Univ) : Complete resolve mutualContext (refs, univs, {}) := by
  intro key found
  simp at found

theorem Complete.below {resolve : Name → Option Address} {mutualContext : MutCtx} {acc : ExprTableCollection}
    (ready : Complete resolve mutualContext acc) (bound : Nat) :
    PreseedKeys.CoveredBelow bound (fun key => Covered resolve mutualContext acc.1 key.expr) acc.2.2 :=
  fun key _ found => ready key found

theorem Complete.after {resolve : Name → Option Address} {mutualContext : MutCtx}
    {source : Expr} {initial output : ExprTableCollection}
    (ready : Complete resolve mutualContext initial) (checked : Result resolve mutualContext source initial output) :
    Complete resolve mutualContext output := by
  intro key found
  rcases checked.added key found with old | covered
  · exact (ready key old).mono resolve mutualContext initial.1 output.1 checked.grows key.expr
  · exact covered

theorem public_correct (context : CompileEnv × BlockEnv) (before after : BlockState)
    (hint : Address) (source : Expr) (initial output : ExprTableCollection)
    (ready : Complete (ExpressionState.lookupBinding context.1 (ExpressionState.bindingView before)) context.2.mutCtx initial)
    (ran : rawRun (collectExprTables source hint initial) context before = (.ok output, after)) :
    Result (ExpressionState.lookupBinding context.1 (ExpressionState.bindingView before)) context.2.mutCtx source initial output := by
  exact collect_correct context (ExpressionState.bindingView before) hint context.2.mutCtx context.2.univCtx source
    before after initial output rfl (ready.below _) ran

theorem root_run (context : CompileEnv × BlockEnv) (before : BlockState)
    (source : Expr) (params : List Name) (initial : ExprTableCollection) :
    rawRun (withUnivCtx params (collectExprTables source (univParamsKey params) initial)) context before =
      rawRun (collectExprTablesStructural (univParamsKey params) context.2.mutCtx params source initial)
        (context.1, { context.2 with univCtx := params }) { before with univCache := {} } := rfl

theorem root_correct (context : CompileEnv × BlockEnv) (bindings : ExpressionState.Bindings)
    (before after : BlockState) (source : Expr) (params : List Name) (initial output : ExprTableCollection)
    (view : ExpressionState.bindingView before = bindings)
    (ready : Complete (ExpressionState.lookupBinding context.1 bindings) context.2.mutCtx initial)
    (ran : rawRun (withUnivCtx params (collectExprTables source (univParamsKey params) initial)) context before = (.ok output, after)) :
    ExpressionState.bindingView after = bindings ∧
      Result (ExpressionState.lookupBinding context.1 bindings) context.2.mutCtx source initial output ∧
      Complete (ExpressionState.lookupBinding context.1 bindings) context.2.mutCtx output := by
  rw [root_run] at ran
  have checked := collect_correct (context.1, { context.2 with univCtx := params }) bindings
    (univParamsKey params) context.2.mutCtx params source { before with univCache := {} } after
    initial output view (ready.below _) ran
  have frame := binding_after (context.1, { context.2 with univCtx := params }) bindings
    (univParamsKey params) context.2.mutCtx params source initial output
    { before with univCache := {} } after view ran
  exact ⟨frame, checked, ready.after checked⟩

theorem roots_correct (context : CompileEnv × BlockEnv) (bindings : ExpressionState.Bindings)
    (roots : List (Expr × List Name)) (before after : BlockState) (initial output : ExprTableCollection)
    (view : ExpressionState.bindingView before = bindings)
    (ready : Complete (ExpressionState.lookupBinding context.1 bindings) context.2.mutCtx initial)
    (ran : rawRun (collectPreseedExprs roots initial) context before = (.ok output, after)) :
    ExpressionState.bindingView after = bindings ∧
      (∀ address ∈ initial.1, address ∈ output.1) ∧
      (∀ root ∈ roots, Covered (ExpressionState.lookupBinding context.1 bindings) context.2.mutCtx output.1 root.1) ∧
      Complete (ExpressionState.lookupBinding context.1 bindings) context.2.mutCtx output := by
  induction roots generalizing before after initial output with
  | nil =>
    simp only [collectPreseedExprs, rawRun_pure] at ran
    obtain ⟨result, rfl⟩ := Prod.mk.inj ran
    cases Except.ok.inj result
    exact ⟨view, fun _ member => member, by simp, ready⟩
  | cons root rest ih =>
    rcases root with ⟨source, params⟩
    rw [collectPreseedExprs] at ran
    obtain ⟨middle, state, rootRan, restRan⟩ := bind_ok _ _ context before output after ran
    obtain ⟨stateView, first, nextReady⟩ := root_correct context bindings before state source params initial middle view ready rootRan
    obtain ⟨afterView, grows, tail, complete⟩ := ih state after middle output stateView nextReady restRan
    refine ⟨afterView, fun address member => grows address (first.grows address member), ?_, complete⟩
    intro root member
    rcases List.mem_cons.mp member with same | remaining
    · subst root
      exact first.covered.mono _ _ middle.1 output.1 grows source
    · exact tail root remaining

theorem public_initial (context : CompileEnv × BlockEnv) (before after : BlockState)
    (hint : Address) (source : Expr) (output : ExprTableCollection)
    (ran : rawRun (collectExprTables source hint (#[], #[], {})) context before = (.ok output, after)) :
    Covered (ExpressionState.lookupBinding context.1 (ExpressionState.bindingView before)) context.2.mutCtx output.1 source :=
  (public_correct context before after hint source _ output (Complete.empty _ _ _ _) ran).covered

theorem worklist_initial (context : CompileEnv × BlockEnv) (before after : BlockState)
    (hint : Address) (source : Expr) (output : ExprTableCollection)
    (ran : rawRun (collectExprTablesWorklist source hint (#[], #[], {})) context before = (.ok output, after)) :
    Covered (ExpressionState.lookupBinding context.1 (ExpressionState.bindingView before)) context.2.mutCtx output.1 source := by
  rw [← collectExprTables_eq_worklist] at ran
  exact public_initial context before after hint source output ran

theorem roots_initial (context : CompileEnv × BlockEnv) (before after : BlockState)
    (roots : List (Expr × List Name)) (output : ExprTableCollection)
    (ran : rawRun (collectPreseedExprs roots (#[], #[], {})) context before = (.ok output, after)) :
    ∀ root ∈ roots,
      Covered (ExpressionState.lookupBinding context.1 (ExpressionState.bindingView before)) context.2.mutCtx output.1 root.1 :=
  (roots_correct context (ExpressionState.bindingView before) roots before after _ output rfl
    (Complete.empty _ _ _ _) ran).2.2.1

end Ix.CompileCert.PreseedReferences
