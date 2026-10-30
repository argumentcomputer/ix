module
public import Ix.CompileDriver
public import Ix.Compile.WorkerSuccess
public import Ix.Compile.TaskWindow
public import Ix.Compile.Parallel
import all Init.Util
import all Ix.CompileDriver
import all Ix.CompileM
import all Ix.Compile.WorkerContext
import all Ix.Compile.WorkerSuccess
public import Std.Data.HashSet.Lemmas

/-! # Bounded computation with ordered publication

The task window predicts dependency inputs while the original fold keeps its
wave snapshots, readiness rule and publication order. A successful candidate
is reused only after exact source, address and blob checks; every refusal or
mismatch runs the original block worker. Pure completion handoffs drain all
predictions before replacing a window or returning, including error exits.
One block lane is reserved for sequential fallback. Nested sharing tasks are
independent of this bound on simultaneous block computations.
-/

public section

open Ix.CompileM
namespace Ix.Compile.WorkerReplay
open Ix.Compile.WorkerSuccess
open Ix.Compile.WorkerContext (run)
open scoped Ix.Compile.WorkerSuccess

theorem Successful.forIn_set (items : Ix.Set Ix.Name) (initial : α)
    (body : Ix.Name → α → CompileM (ForInStep α)) (stable : ∀ item acc, Successful (body item acc)) :
    Successful (forIn items initial body) := by
  rw [Std.HashSet.forIn_eq_forIn_toList]
  exact Successful.forIn_list items.toList initial body stable

theorem registerMutsEntry_success (sources : List Ix.MutConst) (address : Address) :
    Successful (registerMutsEntry sources address) := by
  unfold registerMutsEntry
  finish_steps

theorem compileBlock_success (name : Ix.Name) (all : Ix.Set Ix.Name) :
    Successful (compileBlock name all) := by
  unfold compileBlock
  with_reducible repeat' first
    | exact compileConstantInfo_success _
    | exact compileMutualBlock_success _
    | exact registerMutsEntry_success _ _
    | exact mkIndc_success _
    | refine Successful.forIn_set _ _ _ (fun _ _ => ?_)
    | finish_step

theorem compileM_success (action : CompileM α) (env : CompileEnv) (block : BlockEnv)
    (before after : BlockState) (value : α) :
    CompileM.run env block before action = .ok (value, after) ↔
      run action (env, block) before = (.ok value, after) := by
  change (match run action (env, block) before with
    | (.ok value, after) => Except.ok (value, after)
    | (.error error, _) => Except.error error) = Except.ok (value, after) ↔ _
  cases ran : run action (env, block) before with
  | mk outcome final => cases outcome <;> simp

theorem runBlock_success (left right : CompileEnv) (same : SameInputs left right)
    (all : Ix.Set Ix.Name) (name : Ix.Name) (result : BlockResult) (cache : BlockState)
    (success : runBlock left all name = .ok (result, cache))
    (compatible : Compatible right.blobs cache.blockBlobs) :
    runBlock right all name = .ok (result, cache) := by
  let block : BlockEnv := { all, current := name, mutCtx := default, univCtx := [] }
  unfold runBlock at success ⊢
  change (CompileM.run left block {} (compileBlock name all) >>= fun pair =>
    if blockUnivsFit pair.1 then pure pair else
      throw (.resourceLimit "record universe expansion exceeds the loader's node budget")) = .ok (result, cache) at success
  change (CompileM.run right block {} (compileBlock name all) >>= fun pair =>
    if blockUnivsFit pair.1 then pure pair else
      throw (.resourceLimit "record universe expansion exceeds the loader's node budget")) = .ok (result, cache)
  cases ran : CompileM.run left block {} (compileBlock name all) with
  | error error => simp only [ran, bind, Except.bind] at success; cases success
  | ok pair =>
    simp only [ran, bind, Except.bind] at success
    split at success
    · rename_i fits
      cases Except.ok.inj success
      have raw := (compileM_success _ left block {} cache result).mp ran
      have shifted := (compileBlock_success name all).transfer left right same block {} result cache raw compatible
      rw [(compileM_success _ right block {} cache result).mpr shifted]
      simp only [bind, Except.bind, fits, ↓reduceIte, pure, Except.pure]
    · cases success


/-- Inputs that stay fixed while the driver publishes blocks. -/
structure FixedInput where
  env : Ix.Environment
  sharingLimits : Ix.Sharing.Exact.Limits

def FixedInput.ofEnv (env : CompileEnv) : FixedInput := ⟨env.env, env.sharingLimits⟩

def FixedInput.Matches (input : FixedInput) (env : CompileEnv) : Prop :=
  env.env = input.env ∧ env.sharingLimits = input.sharingLimits

def FixedInput.view (input : FixedInput)
    (addresses : Std.HashMap Ix.Compile.ExactKey.ExactName Address) : CompileEnv :=
  { CompileEnv.new input.env with nameToAddr := addresses, sharingLimits := input.sharingLimits }

/-- A worker's provenance is checked by the kernel and erased from its runtime
value. A failed speculative run retains no result and is never replayed. -/
structure Candidate (input : FixedInput) where
  key : Ix.Name
  members : Ix.Set Ix.Name
  addresses : Std.HashMap Ix.Compile.ExactKey.ExactName Address
  compiled : Option (BlockResult × BlockState)
  computed : compiled = (runBlock (input.view addresses) members key).toOption

def speculate (input : FixedInput) (key : Ix.Name) (members : Ix.Set Ix.Name)
    (addresses : Std.HashMap Ix.Compile.ExactKey.ExactName Address) : Candidate input :=
  { key, members, addresses
    compiled := (runBlock (input.view addresses) members key).toOption
    computed := rfl }

-- Source identity includes the exact set representation, so neither set
-- iteration order nor any stored name hash is assumed irrelevant.
def memberListDec {α : Type} [DecidableEq α] : (left right : Std.DHashMap.Internal.AssocList α (fun _ => Unit)) → Decidable (left = right)
  | .nil, .nil => .isTrue rfl
  | .nil, .cons .. => .isFalse (by intro same; cases same)
  | .cons .., .nil => .isFalse (by intro same; cases same)
  | .cons a () as, .cons b () bs =>
    if key : a = b then
      match memberListDec as bs with
      | .isTrue tail => .isTrue (by cases key; cases tail; rfl)
      | .isFalse tail => .isFalse (by intro same; cases same; exact tail rfl)
    else .isFalse (by intro same; cases same; exact key rfl)
termination_by left _right => sizeOf left

-- The recursive comparison is supplied explicitly to the array comparator.
def memberSetDec {α : Type} [BEq α] [Hashable α] [DecidableEq α]
    (left right : Std.HashSet α) : Decidable (left = right) := by
  letI : DecidableEq (Std.DHashMap.Internal.AssocList α (fun _ => Unit)) := memberListDec
  let l := left.inner.inner.inner
  let r := right.inner.inner.inner
  if same : l.size = r.size ∧ l.buckets = r.buckets then
    apply isTrue
    cases left with | mk left =>
      cases right with | mk right =>
        cases left with | mk left =>
          cases right with | mk right =>
            cases left with | mk left lw =>
              cases right with | mk right rw =>
                cases left
                cases right
                cases same.1
                cases same.2
                rfl
  else
    apply isFalse
    intro equal
    cases equal
    exact same ⟨rfl, rfl⟩

/-- Exact source identity and successful read-frame checks justify reuse.
Every failure or mismatch reruns the original worker against this wave. -/
def checkedOutcome (input : FixedInput) (actual : CompileEnv) (key : Ix.Name)
    (members : Ix.Set Ix.Name) (candidate : Candidate input) : AuxBlockOutcome :=
  letI : DecidableEq (Ix.Set Ix.Name) := fun left right =>
    withPtrEqDecEq left right (fun _ => memberSetDec left right)
  if candidate.key = key then
    if candidate.members = members then
      match candidate.compiled with
      | none => auxBlockOutcome actual key members
      | some (result, cache) =>
        if checkExtension candidate.addresses actual.nameToAddr && checkCompatible actual.blobs cache.blockBlobs then
          .compiled result cache
        else auxBlockOutcome actual key members
    else auxBlockOutcome actual key members
  else auxBlockOutcome actual key members

theorem checkedOutcome_eq (input : FixedInput) (actual : CompileEnv)
    (fixed : input.Matches actual) (key : Ix.Name) (members : Ix.Set Ix.Name)
    (candidate : Candidate input) :
    checkedOutcome input actual key members candidate = auxBlockOutcome actual key members := by
  unfold checkedOutcome
  split
  · rename_i keySame
    split
    · rename_i membersSame
      cases result : candidate.compiled with
      | none => rfl
      | some pair =>
        simp only
        split
        · rename_i checked
          have checks := Bool.and_eq_true_iff.mp checked
          have ran : runBlock (input.view candidate.addresses) members key = .ok pair := by
            have computed := candidate.computed
            rw [result, keySame, membersSame] at computed
            cases ran : runBlock (input.view candidate.addresses) members key <;> simp_all [Except.toOption]
          have transported := runBlock_success (input.view candidate.addresses) actual
            ⟨fixed.1.symm, checkExtension_sound _ _ checks.1, fixed.2.symm⟩
            members key pair.1 pair.2 ran (checkCompatible_sound _ _ checks.2)
          simp only [auxBlockOutcome, transported]
        · rfl
    · rfl
  · rfl

abbrev AddressTable := Std.HashMap Ix.Compile.ExactKey.ExactName Address
abbrev WaveBlocks := Array (Ix.Name × Ix.Name × Ix.Set Ix.Name)
abbrev CandidateBank (input : FixedInput) :=
  Std.HashMap Ix.Compile.ExactKey.ExactName (Task (Candidate input))

/-- A speculative claim is only a proposed address. The real wave frame
check, followed by the original publication checks, decides whether it is usable. -/
def candidateClaims (candidate : Candidate input) : AddressTable :=
  match candidate.compiled with
  | none => {}
  | some (result, _) =>
    (primaryClaims candidate.key result).foldl (fun table (name, address) =>
      table.insert name address) {}

structure ParentTask where
  claims : Task AddressTable
  completion : Task Unit
  group : Nat
  level : Nat

def initialReady (blocks : Ix.CondensedBlocks) (sched : FoldSchedule) (st : FoldState) : WaveBlocks := Id.run do
  let mut ready := #[]
  for rep in st.candidates do
    if let some all := blocks.blocks.get? rep then
      let deps := sched.deps.getD rep {}
      let valid := Id.run do
        for name in deps do
          if !auxDependencyReady blocks.lowLinks.contains st.acc.cenv st.settled name then return false
        return true
      if valid then ready := ready.push (blockKey rep all, rep, all)
  return ready.qsort fun a b => Ix.nameCompare a.1 b.1 == .lt

/-- Only the counters predict future work. Readiness and settlement of the
real driver remain authoritative; predictions may miss and then fall back. -/
def predictedNext (blocks : Ix.CondensedBlocks) (sched : FoldSchedule)
    (unmet : Std.HashMap Ix.Name Nat) (ready : WaveBlocks) :
    Std.HashMap Ix.Name Nat × WaveBlocks := Id.run do
  let mut unmet := unmet
  let mut next := #[]
  for (_, _, all) in ready do
    for name in all do
      for waiter in sched.waiters.getD name #[] do
        match unmet.get? waiter with
        | some 1 =>
          unmet := unmet.erase waiter
          if let some members := blocks.blocks.get? waiter then
            next := next.push (blockKey waiter members, waiter, members)
        | some count => unmet := unmet.insert waiter (count - 1)
        | none => pure ()
  return (unmet, next.qsort fun a b => Ix.nameCompare a.1 b.1 == .lt)

/-- A few source-dependency levels, with a fixed extra-result budget. -/
structure WindowConfig where
  levels : Nat := 4
  lookahead : Nat := 8192
  groupSize : Nat := 32

structure PlannedBlock where
  key : Ix.Name
  representative : Ix.Name
  members : Ix.Set Ix.Name
  addresses : AddressTable
  dependencies : Array Ix.Name

structure WindowPlan where
  levels : Array (Array PlannedBlock) := #[]

/-- Prepare compact sparse inputs on the driver thread. No live publication
map enters the plan that will cross the completion handoff. -/
def planWindow (config : WindowConfig) (blocks : Ix.CondensedBlocks) (sched : FoldSchedule)
    (st : FoldState) : WindowPlan := Id.run do
  let first := initialReady blocks sched st
  let capacity := first.size + config.lookahead
  let mut levels := #[]
  let mut ready := first
  let mut unmet := st.unmet
  let mut planned := 0
  for _ in [:max 1 config.levels] do
    if ready.isEmpty || ready.size > capacity - planned then return { levels }
    let level := ready.map fun (key, representative, members) => Id.run do
      let dependencies := (sched.deps.getD representative {}).toArray
      let mut addresses : AddressTable := {}
      for name in dependencies do
        if let some address := st.acc.cenv.nameToAddr.get? name then
          addresses := addresses.insert name address
      return { key, representative, members, addresses, dependencies : PlannedBlock }
    levels := levels.push level
    planned := planned + ready.size
    let (nextUnmet, nextReady) := predictedNext blocks sched unmet ready
    unmet := nextUnmet
    ready := nextReady
  return { levels }

/-- One window owns its results and the completion token for every task it
launched, including predictions the real fold never consumes. -/
structure WindowTasks (input : FixedInput) where
  bank : CandidateBank input := {}
  completion : Task Unit := Task.pure ()
  levels : Nat := 0

/-- Start only the compact plan received after the preceding window drains.
Reserve one lane for the main-thread fallback: width zero or one uses the
sequential path, and wider folds have at most width-minus-one speculative
block computations. Each block's nested sharing tasks are separate. -/
def launchWindow (config : WindowConfig) (input : FixedInput) (width : Nat)
    (plan : WindowPlan) : WindowTasks input := Id.run do
  if width ≤ 1 then return { levels := 1 }
  let count := plan.levels.foldl (fun count level => count + level.size) 0
  let lanes := max 1 (min count (width - 1))
  let groupSize := max 1 config.groupSize
  let mut laneTokens : Array (Task Unit) := Array.replicate lanes (Task.pure ())
  let mut bank : CandidateBank input := {}
  let mut parents : Std.HashMap Ix.Compile.ExactKey.ExactName ParentTask := {}
  let mut prefixes : Array (Task Unit) := #[]
  let mut issued := 0
  let mut nextGroup := 0
  for level in [:plan.levels.size] do
    let ready := plan.levels.getD level #[]
    let parentView := parents
    let mut levelTokens : Array (Task Unit) := #[]
    let groupCount := (ready.size + groupSize - 1) / groupSize
    for groupIndex in [:groupCount] do
      let group := ready.extract (groupIndex * groupSize) ((groupIndex + 1) * groupSize)
      let mut groupClaims : Array (Task AddressTable) := #[]
      let mut membersAndClaims : Array (Ix.Set Ix.Name × Task AddressTable) := #[]
      for node in group do
        let { key, representative, members, addresses, dependencies } := node
        let mut pending : Array (Ix.Name × Task AddressTable) := #[]
        let mut waitGroups : Std.HashSet Nat := {}
        let mut waits := #[laneTokens.getD (issued % lanes) (Task.pure ())]
        if level ≥ 2 then waits := waits.push (prefixes.getD (level - 2) (Task.pure ()))
        for name in dependencies do
          if let some parent := parentView.get? name then
            pending := pending.push (name, parent.claims)
            if parent.level + 2 > level && !waitGroups.contains parent.group then
              waitGroups := waitGroups.insert parent.group
              waits := waits.push parent.completion
        let worker := Ix.Compile.TaskWindow.afterAll waits.toList fun _ =>
          let addresses := pending.foldl (fun table (name, parent) =>
            match parent.get.get? name with
            | none => table
            | some address => table.insert name address) addresses
          speculate input key members addresses
        let claims := worker.map candidateClaims (sync := true)
        bank := bank.insert representative worker
        laneTokens := laneTokens.set! (issued % lanes) (Ix.Compile.TaskWindow.completed claims)
        issued := issued + 1
        groupClaims := groupClaims.push claims
        membersAndClaims := membersAndClaims.push (members, claims)
      let completion := Ix.Compile.TaskWindow.token groupClaims.toList
      levelTokens := levelTokens.push completion
      for (members, claims) in membersAndClaims do
        for name in members do
          parents := parents.insert name { claims, completion, group := nextGroup, level }
      nextGroup := nextGroup + 1
    let prior := prefixes.back?.getD (Task.pure ())
    prefixes := prefixes.push (Ix.Compile.TaskWindow.token (prior :: levelTokens.toList))
  return { bank, completion := prefixes.back?.getD (Task.pure ()), levels := plan.levels.size }

/-- Plan first, await the old window through that compact value, and only
then launch new workers. The live driver state stays outside the handoff. -/
def refreshWindow (config : WindowConfig) (input : FixedInput) (blocks : Ix.CondensedBlocks)
    (sched : FoldSchedule) (width : Nat) (st : FoldState) (completion : Task Unit) : WindowTasks input :=
  let plan := if width ≤ 1 then ({} : WindowPlan) else planWindow config blocks sched st
  let released := Ix.Compile.TaskWindow.finish completion plan
  launchWindow config input width released

/-- Terminal values await every outstanding worker, even on errors or when
the real fold finishes before all of its speculative predictions are used. -/
def finishWindow (window : WindowTasks input) (result : Except String FoldState) : Except String FoldState :=
  Ix.Compile.TaskWindow.finish window.completion result

theorem finishWindow_eq (window : WindowTasks input) (result : Except String FoldState) :
    finishWindow window result = result := by
  unfold finishWindow
  exact Ix.Compile.TaskWindow.finish_eq _ _

/-- Apply the original block transition in the original order, checking each
candidate against the single real snapshot of this wave. -/
def applyWindow (input : FixedInput) (bank : CandidateBank input) (snapshot : CompileEnv)
    (ready : WaveBlocks) (acc : DriverAcc) : DriverAcc :=
  ready.foldl (fun acc (key, rep, members) =>
    let outcome := match bank.get? rep with
      | none => auxBlockOutcome snapshot key members
      | some task => checkedOutcome input snapshot key members task.get
    (applyAuxBlockOutcome acc key members outcome).1) acc

def applyOriginal (snapshot : CompileEnv) (ready : WaveBlocks) (acc : DriverAcc) : DriverAcc :=
  ready.foldl (fun acc (key, _, members) =>
    (applyAuxBlockOutcome acc key members (auxBlockOutcome snapshot key members)).1) acc

theorem applyWindow_eq (input : FixedInput) (bank : CandidateBank input) (snapshot : CompileEnv)
    (fixed : input.Matches snapshot) (ready : WaveBlocks) (acc : DriverAcc) :
    applyWindow input bank snapshot ready acc = applyOriginal snapshot ready acc := by
  unfold applyWindow applyOriginal
  congr 1
  funext before entry
  obtain ⟨key, rep, members⟩ := entry
  dsimp only
  cases found : bank.get? rep with
  | none => rfl
  | some task =>
    dsimp only
    rw [checkedOutcome_eq input snapshot fixed]
theorem forInKeepsList {α σ : Type} (I : σ → Prop) (f : α → σ → Id (ForInStep σ)) :
    ∀ (l : List α), (∀ x ∈ l, ∀ s, I s → I (f x s).value) →
      ∀ s, I s → I (forIn (m := Id) l s f) := by
  intro l
  induction l with
  | nil => intro _ s hs; exact hs
  | cons x l ih =>
    intro hstep s hs
    rw [List.forIn_cons]
    have hx := hstep x List.mem_cons_self s hs
    cases hf : f x s with
    | done s' => rw [hf] at hx; exact hx
    | yield s' =>
      rw [hf] at hx
      exact ih (fun y hy => hstep y (List.mem_cons_of_mem _ hy)) s' hx

/-- `forInKeepsList` over an array. -/
theorem forInKeepsArray {α σ : Type} (I : σ → Prop) (f : α → σ → Id (ForInStep σ)) (xs : Array α)
    (step : ∀ x ∈ xs, ∀ s, I s → I (f x s).value) (s : σ) (hs : I s) :
    I (forIn (m := Id) xs s f) := by
  rw [← Array.forIn_toList]
  exact forInKeepsList I f xs.toList (fun x hx => step x (Array.mem_toList_iff.mp hx)) s hs

/-- A loop over an array followed by its continuation: the continuation of
every state the invariant holds of has `P`. Stated on the bind, so that it
unifies with an elaborated `do` block's loop and continuation. -/
theorem loopThen {α σ β : Type} (xs : Array α) (init : σ) (f : α → σ → Id (ForInStep σ))
    (k : σ → Id β) (I : σ → Prop) (P : β → Prop)
    (hinit : I init) (body : ∀ x ∈ xs, ∀ s, I s → I (f x s).value) (cont : ∀ L, I L → P (k L)) :
    P (forIn (m := Id) xs init f >>= k) :=
  cont _ (forInKeepsArray I f xs body init hinit)


set_option hygiene false in
local macro "keep_merge_tail" initial:term : tactic => `(tactic| (
  refine loopThen (P := fun d : DriverAcc => input.Matches d.cenv)
    (I := fun c : CompileEnv => input.Matches c) _ _ _ _ ?_ ?_ ?_
  · exact $initial
  · intro _ _ state fixed; split <;> exact fixed
  · intro after afterFixed
    split
    · refine loopThen (P := fun d : DriverAcc => input.Matches d.cenv)
        (I := fun c : CompileEnv => input.Matches c) _ _ _ _ afterFixed ?_ ?_
      · intro cls _ state fixed
        exact forInKeepsArray (fun c : CompileEnv => input.Matches c) _ cls
          (by intro _ _ state fixed; exact fixed) state fixed
      · intro final fixed; exact fixed
    · exact afterFixed))

theorem mergeCompiledBlock_fixed (input : FixedInput) (acc : DriverAcc)
    (fixed : input.Matches acc.cenv) (key : Ix.Name) (result : BlockResult) (cache : BlockState) :
    input.Matches (mergeCompiledBlock acc key result cache).cenv := by
  unfold mergeCompiledBlock
  simp only [Id.run]
  split
  · split <;> keep_merge_tail fixed
  · refine loopThen (P := fun d : DriverAcc => input.Matches d.cenv)
      (I := fun c : CompileEnv => input.Matches c) _ _ _ _ fixed ?_ ?_
    · intro entry _ state stateFixed
      split <;> exact stateFixed
    · intro after afterFixed
      keep_merge_tail afterFixed

theorem matchesPure {input : FixedInput} {acc : DriverAcc} {names : Array Ix.Name} {failed : Bool}
    (fixed : input.Matches acc.cenv) :
    input.Matches (pure (acc, names, failed) : Id (DriverAcc × Array Ix.Name × Bool)).1.cenv := fixed

theorem namesThen {input : FixedInput} {α : Type} (items : Array α) (initial : Array Ix.Name)
    (body : α → Array Ix.Name → Id (ForInStep (Array Ix.Name)))
    (next : Array Ix.Name → Id (DriverAcc × Array Ix.Name × Bool))
    (fixed : ∀ names, input.Matches (next names).1.cenv) :
    input.Matches (forIn (m := Id) items initial body >>= next).1.cenv :=
  loopThen items initial body next (fun _ => True) (fun result => input.Matches result.1.cenv)
    trivial (fun _ _ _ _ => trivial) (fun names _ => fixed names)

theorem applyOutcome_fixed (input : FixedInput) (acc : DriverAcc)
    (fixed : input.Matches acc.cenv) (key : Ix.Name) (members : Ix.Set Ix.Name) (outcome : AuxBlockOutcome) :
    input.Matches (applyAuxBlockOutcome acc key members outcome).1.cenv := by
  cases outcome with
  | compiled result cache =>
    unfold applyAuxBlockOutcome
    simp only [Id.run]
    split
    · refine matchesPure ?_
      refine loopThen (P := fun d : DriverAcc => input.Matches d.cenv)
        (I := fun d : DriverAcc => input.Matches d.cenv) _ _ _ _ fixed ?_ ?_
      · intro _ _ state stateFixed; exact stateFixed
      · intro after afterFixed; exact afterFixed
    · have merged := mergeCompiledBlock_fixed input acc fixed key result cache
      split
      · refine namesThen _ _ _ _ ?_
        intro names; exact matchesPure merged
      · refine namesThen _ _ _ _ ?_
        intro names
        refine namesThen _ _ _ _ ?_
        intro names; exact matchesPure merged
  | failed message =>
    unfold applyAuxBlockOutcome
    simp only [Id.run]
    refine matchesPure ?_
    refine loopThen (P := fun d : DriverAcc => input.Matches d.cenv)
      (I := fun d : DriverAcc => input.Matches d.cenv) _ _ _ _ fixed ?_ ?_
    · intro _ _ state stateFixed; exact stateFixed
    · intro after afterFixed; exact afterFixed

theorem applyOriginal_fixed (input : FixedInput) (snapshot : CompileEnv) (ready : WaveBlocks)
    (acc : DriverAcc) (fixed : input.Matches acc.cenv) :
    input.Matches (applyOriginal snapshot ready acc).cenv := by
  unfold applyOriginal
  rw [← Array.foldl_toList]
  induction ready.toList generalizing acc with
  | nil => exact fixed
  | cons entry rest ih =>
    rw [List.foldl_cons]
    exact ih _ (applyOutcome_fixed input acc fixed _ _ _)

/-- The original chunked application, factored only for the equality proof. -/
def applyChunked (width : Nat) (snapshot : CompileEnv) (ready : WaveBlocks) (acc : DriverAcc) : DriverAcc := Id.run do
  let tasks := waveTasks width snapshot ready
  let mut acc := acc
  for task in tasks do
    for (key, members, outcome) in task.get do
      acc := (applyAuxBlockOutcome acc key members outcome).1
  return acc

theorem chunks_outcomes (width : Nat) (snapshot : CompileEnv) (ready : WaveBlocks) :
    ((waveTasks width snapshot ready).map Task.get).flatten =
      ready.map fun (key, _, members) => (key, members, auxBlockOutcome snapshot key members) := by
  unfold waveTasks
  simp only [Array.map_map, Function.comp_def]
  exact Ix.Compile.Parallel.slices_map _ ready _ _ (Ix.Compile.Parallel.chunks_cover ready.size (max 1 width)
    (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 width)))

theorem applyChunked_eq (width : Nat) (snapshot : CompileEnv) (ready : WaveBlocks) (acc : DriverAcc) :
    applyChunked width snapshot ready acc = applyOriginal snapshot ready acc := by
  unfold applyChunked applyOriginal
  simp only [Id.run, bind_pure, pure_bind, Array.forIn_pure_yield_eq_foldl]
  have flat := congrArg
    (fun xs => Array.foldl (fun acc (entry : Ix.Name × Ix.Set Ix.Name × AuxBlockOutcome) =>
      (applyAuxBlockOutcome acc entry.1 entry.2.1 entry.2.2).1) acc xs)
    (chunks_outcomes width snapshot ready)
  simp only [Array.foldl_flatten, Array.foldl_map] at flat
  exact flat
def foldWaveUsing (apply : CompileEnv → Array (Name × Name × Set Name) → DriverAcc → DriverAcc)
    (blocks : Ix.CondensedBlocks) (sched : FoldSchedule) (st : FoldState) : Except String FoldState := Id.run do
  let { acc, settled, unmet, candidates, remaining, waves } := st
  let sourceOwned := blocks.lowLinks.contains
  let mut ready : Array (Name × Name × Set Name) := #[]
  let mut parked : Array Name := #[]
  for rep in candidates do
    let some all := blocks.blocks.get? rep
      | return .error s!"wave driver: block {rep.pretty} is not in the condensation"
    let deps := (sched.deps.get? rep).getD {}
    let depsOk := Id.run do
      for d in deps do
        if !auxDependencyReady sourceOwned acc.cenv settled d then return false
      return true
    if depsOk then ready := ready.push (blockKey rep all, rep, all)
    else parked := parked.push rep
  if ready.isEmpty then
    return .error s!"Circular dependency detected: {remaining} blocks remaining but none ready"
  ready := ready.qsort fun a b => Ix.nameCompare a.1 b.1 == .lt
  let acc := apply acc.cenv ready acc
  let mut settled := settled
  let mut unmet := unmet
  let mut next := parked
  for (_, _, all) in ready do
    for m in all do
      settled := settled.insert m
  for (_, _, all) in ready do
    for m in all do
      for w in (sched.waiters.get? m).getD #[] do
        match unmet.get? w with
        | some 1 =>
          unmet := unmet.erase w
          next := next.push w
        | some k => unmet := unmet.insert w (k - 1)
        | none => pure ()
  return .ok { acc, settled, unmet, candidates := next,
               remaining := remaining - ready.size, waves := waves + 1 }


theorem foldWave_eq_using (blocks : Ix.CondensedBlocks) (sched : FoldSchedule)
    (width : Nat) (dbg : Bool) (st : FoldState) :
    foldWave blocks sched width dbg st = foldWaveUsing (applyChunked width) blocks sched st := by
  cases dbg <;> rfl

theorem foldWaveUsing_congr (left right : CompileEnv → WaveBlocks → DriverAcc → DriverAcc)
    (blocks : Ix.CondensedBlocks) (sched : FoldSchedule) (st : FoldState)
    (same : ∀ ready acc, left st.acc.cenv ready acc = right st.acc.cenv ready acc) :
    foldWaveUsing left blocks sched st = foldWaveUsing right blocks sched st := by
  simp only [foldWaveUsing, same]

def prepareWaveCandidates (blocks : Ix.CondensedBlocks) (sched : FoldSchedule) (st : FoldState) :
    Option (Except String FoldState) × Array (Name × Name × Set Name) × Array Name :=
  let { acc, settled, candidates, .. } := st
  let sourceOwned := blocks.lowLinks.contains
  Id.run <| forIn candidates (none, #[], #[]) fun rep r => do
    let ready := r.2.1
    let parked := r.2.2
    let some all := blocks.blocks.get? rep
      | return .done (some (.error s!"wave driver: block {rep.pretty} is not in the condensation"), ready, parked)
    let deps := (sched.deps.get? rep).getD {}
    let depsOk := Id.run do
      for d in deps do
        if !auxDependencyReady sourceOwned acc.cenv settled d then return false
      return true
    if depsOk then
      return .yield (none, ready.push (blockKey rep all, rep, all), parked)
    else
      return .yield (none, ready, parked.push rep)

def finishWave (sched : FoldSchedule) (st : FoldState)
    (ready : Array (Name × Name × Set Name)) (parked : Array Name) (acc : DriverAcc) : FoldState := Id.run do
  let { settled, unmet, remaining, waves, .. } := st
  let mut settled := settled
  let mut unmet := unmet
  let mut next := parked
  for (_, _, all) in ready do
    for m in all do
      settled := settled.insert m
  for (_, _, all) in ready do
    for m in all do
      for w in (sched.waiters.get? m).getD #[] do
        match unmet.get? w with
        | some 1 =>
          unmet := unmet.erase w
          next := next.push w
        | some k => unmet := unmet.insert w (k - 1)
        | none => pure ()
  return { acc, settled, unmet, candidates := next,
           remaining := remaining - ready.size, waves := waves + 1 }

theorem foldWaveUsing_eq_split (apply : CompileEnv → Array (Name × Name × Set Name) → DriverAcc → DriverAcc)
    (blocks : Ix.CondensedBlocks) (sched : FoldSchedule) (st : FoldState) :
    foldWaveUsing apply blocks sched st =
      let final := prepareWaveCandidates blocks sched st
      match final.1 with
      | some err => err
      | none =>
        if final.2.1.isEmpty then
          .error s!"Circular dependency detected: {st.remaining} blocks remaining but none ready"
        else
          let ready := final.2.1.qsort fun a b => Ix.nameCompare a.1 b.1 == .lt
          .ok (finishWave sched st ready final.2.2 (apply st.acc.cenv ready st.acc)) := by
  unfold foldWaveUsing prepareWaveCandidates finishWave
  cases st
  dsimp only [Id.run, Bind.bind, Pure.pure, Monad.toBind, Monad.toApplicative,
    Applicative.toPure, Id.instMonad]
  split <;> simp_all

theorem foldWaveUsing_acc (apply : CompileEnv → WaveBlocks → DriverAcc → DriverAcc)
    (blocks : Ix.CondensedBlocks) (sched : FoldSchedule) (st after : FoldState)
    (success : foldWaveUsing apply blocks sched st = .ok after) :
    ∃ ready, after.acc = apply st.acc.cenv ready st.acc := by
  unfold foldWaveUsing at success
  simp only [Id.run] at success
  revert success
  refine loopThen (P := fun result => result = Except.ok after →
      ∃ ready, after.acc = apply st.acc.cenv ready st.acc)
    (I := fun state : Option (Except String FoldState) × WaveBlocks × Array Ix.Name =>
      state.1 = none ∨ ∃ error, state.1 = some (.error error)) _ _ _ _ ?_ ?_ ?_
  · exact .inl rfl
  · intro rep _ state _
    split
    · split <;> exact .inl rfl
    · exact .inr ⟨_, rfl⟩
  · intro final exits success
    rcases exits with normal | ⟨error, failed⟩
    · rw [normal] at success
      dsimp only at success
      split at success
      · cases success
      · have equal := Except.ok.inj success
        subst equal
        exact ⟨_, rfl⟩
    · rw [failed] at success
      cases success

def applyWindowTraced (input : FixedInput) (bank : CandidateBank input)
    (dbg : Bool) (waves remaining : Nat) (snapshot : CompileEnv)
    (ready : WaveBlocks) (acc : DriverAcc) : DriverAcc := Id.run do
  if dbg then
    dbg_trace s!"  [compile-lean] wave {waves + 1}: {ready.size} blocks ready, \
{remaining - ready.size} after it"
    pure ()
  return applyWindow input bank snapshot ready acc

def foldWaveWindow (input : FixedInput) (bank : CandidateBank input)
    (blocks : Ix.CondensedBlocks) (sched : FoldSchedule) (dbg : Bool) (st : FoldState) :
    Except String FoldState :=
  foldWaveUsing (applyWindowTraced input bank dbg st.waves st.remaining) blocks sched st

theorem foldWaveWindow_eq (input : FixedInput) (bank : CandidateBank input)
    (blocks : Ix.CondensedBlocks) (sched : FoldSchedule) (width : Nat) (dbg : Bool)
    (st : FoldState) (fixed : input.Matches st.acc.cenv) :
    foldWaveWindow input bank blocks sched dbg st = foldWave blocks sched width dbg st := by
  rw [foldWave_eq_using]
  apply foldWaveUsing_congr
  intro ready acc
  rw [applyChunked_eq]
  cases dbg <;> exact applyWindow_eq input bank st.acc.cenv fixed ready acc

theorem foldWave_fixed (input : FixedInput) (blocks : Ix.CondensedBlocks)
    (sched : FoldSchedule) (width : Nat) (dbg : Bool) (st after : FoldState)
    (fixed : input.Matches st.acc.cenv)
    (success : foldWave blocks sched width dbg st = .ok after) : input.Matches after.acc.cenv := by
  rw [foldWave_eq_using] at success
  obtain ⟨ready, same⟩ := foldWaveUsing_acc _ blocks sched st after success
  rw [same, applyChunked_eq]
  exact applyOriginal_fixed input st.acc.cenv ready st.acc fixed

/-- Retain one finite window and drain it before replacement or any return.
The logical fold's fuel, stopping rules, errors and application order stay
unchanged. Completion waits do not rely on cancellation of unused tasks. -/
def foldWavesCached (config : WindowConfig) (input : FixedInput) (blocks : Ix.CondensedBlocks) (sched : FoldSchedule)
    (width : Nat) (dbg : Bool) : Nat → FoldState → WindowTasks input → Nat → Except String FoldState
  | 0, st, window, _ =>
    finishWindow window <| if st.remaining == 0 then .ok st
      else .error s!"Only compiled {blocks.blocks.size - st.remaining}/{blocks.blocks.size} \
blocks - circular dependency?"
  | fuel + 1, st, window, available =>
    if st.remaining == 0 then finishWindow window (.ok st)
    else
      let selected := if available == 0 then
        refreshWindow config input blocks sched width st window.completion else window
      let available := if available == 0 then selected.levels else available
      match foldWaveWindow input selected.bank blocks sched dbg st with
      | .error error => finishWindow selected (.error error)
      | .ok after => foldWavesCached config input blocks sched width dbg fuel after selected (available - 1)

theorem foldWavesCached_eq (config : WindowConfig) (input : FixedInput) (blocks : Ix.CondensedBlocks) (sched : FoldSchedule)
    (width : Nat) (dbg : Bool) (fuel : Nat) : ∀ st window available,
    input.Matches st.acc.cenv →
      foldWavesCached config input blocks sched width dbg fuel st window available = foldWaves blocks sched width dbg fuel st := by
  induction fuel with
  | zero =>
    intro st window available fixed
    simp only [foldWavesCached, foldWaves, finishWindow_eq]
  | succ fuel ih =>
    intro st window available fixed
    unfold foldWavesCached foldWaves
    simp only [finishWindow_eq]
    split
    · rfl
    · rw [foldWaveWindow_eq input _ blocks sched width dbg st fixed]
      cases step : foldWave blocks sched width dbg st with
      | error error => rfl
      | ok after =>
        exact ih after _ _ (foldWave_fixed input blocks sched width dbg st after fixed step)

def foldWavesWindowedWith (config : WindowConfig) (blocks : Ix.CondensedBlocks) (sched : FoldSchedule)
    (width : Nat) (dbg : Bool) (fuel : Nat) (st : FoldState) : Except String FoldState :=
  foldWavesCached config (FixedInput.ofEnv st.acc.cenv) blocks sched width dbg fuel st {} 0

theorem foldWavesWindowedWith_eq (config : WindowConfig) (blocks : Ix.CondensedBlocks) (sched : FoldSchedule)
    (width : Nat) (dbg : Bool) (fuel : Nat) (st : FoldState) :
    foldWavesWindowedWith config blocks sched width dbg fuel st = foldWaves blocks sched width dbg fuel st :=
  foldWavesCached_eq config (FixedInput.ofEnv st.acc.cenv) blocks sched width dbg fuel st {} 0 ⟨rfl, rfl⟩

def foldWavesWindowed (blocks : Ix.CondensedBlocks) (sched : FoldSchedule)
    (width : Nat) (dbg : Bool) (fuel : Nat) (st : FoldState) : Except String FoldState :=
  foldWavesWindowedWith {} blocks sched width dbg fuel st

theorem foldWaves_eq_windowed : @foldWaves = @foldWavesWindowed := by
  funext blocks sched width dbg fuel st
  exact (foldWavesWindowedWith_eq {} blocks sched width dbg fuel st).symm

/-- The environment driver with configurable computation windows. Validation,
publication, finalization and returned environment are the original driver's. -/
def compileEnvFoldWindowedWith (config : WindowConfig) (env : Ix.Environment)
    (blocks : Ix.CondensedBlocks) (dbg : Bool := false)
    (sharingLimits : Ix.Sharing.Exact.Limits := compilerSharingLimits)
    (width : Nat := foldWaveTasks) : Except String (Ixon.Env × Nat × CompileEnv) := do
  if let some message := missingBlockRefs? blocks then throw message
  validateInductiveFlags env
  validateMutualSafety env blocks
  let view : Ix.Environment := { consts := {}, fallback? := some env.get? }
  let sched := FoldSchedule.of blocks
  let initial := { CompileEnv.new view with sharingLimits }
  let state ← foldWavesWindowedWith config blocks sched width dbg (blocks.blocks.size + 1)
    (FoldState.init initial blocks sched)
  let (artifact, bytes, final) ← finalizeEnv state.acc
  return (artifact, bytes, { final with env })

theorem compileEnvFoldWindowedWith_eq (config : WindowConfig) (env : Ix.Environment)
    (blocks : Ix.CondensedBlocks) (dbg : Bool) (sharingLimits : Ix.Sharing.Exact.Limits) (width : Nat) :
    compileEnvFoldWindowedWith config env blocks dbg sharingLimits width =
      compileEnvFold env blocks dbg sharingLimits width := by
  unfold compileEnvFoldWindowedWith compileEnvFold
  simp only [foldWavesWindowedWith_eq]
  rfl

def compileEnvFoldWindowed (env : Ix.Environment) (blocks : Ix.CondensedBlocks)
    (dbg : Bool := false) (sharingLimits : Ix.Sharing.Exact.Limits := compilerSharingLimits)
    (width : Nat := foldWaveTasks) : Except String (Ixon.Env × Nat × CompileEnv) :=
  compileEnvFoldWindowedWith {} env blocks dbg sharingLimits width

theorem compileEnvFold_eq_windowed : @compileEnvFold = @compileEnvFoldWindowed := by
  funext env blocks dbg sharingLimits width
  exact (compileEnvFoldWindowedWith_eq {} env blocks dbg sharingLimits width).symm

end Ix.Compile.WorkerReplay
