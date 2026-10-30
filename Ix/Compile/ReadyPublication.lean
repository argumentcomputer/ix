module

public import Ix.Compile.WorkerReplay
public import Ix.Cert.Compile
import all Ix.CompileDriver
import all Ix.Compile.WorkerReplay

/-! # Ordered publication of independently scheduled block candidates

An IO scheduler supplies candidates in any computation order. Each candidate
is checked against the original frozen snapshot before the original live
publication transition runs. The returned value carries equality to the pure
driver. Scheduler errors remain IO errors rather than compiler refusals.
-/

public section

namespace Ix.Compile.ReadyPublication

open Ix.CompileM Ix.Compile.WorkerReplay

abbrev Choose (input : FixedInput) := Ix.Name → IO (Option (Candidate input))

inductive Disposition where
  | reused | absent | sourceMismatch | workerFailed | addressMismatch | blobMismatch
  deriving Repr, BEq, Inhabited

/-- The frame predicates run once. The disposition reports why a prediction
was reused or why the reference worker had to run against the real snapshot. -/
def selectOutcome (input : FixedInput) (snapshot : CompileEnv) (key : Ix.Name)
    (members : Ix.Set Ix.Name) (candidate : Option (Candidate input)) :
    AuxBlockOutcome × Disposition :=
  letI : DecidableEq (Ix.Set Ix.Name) := fun left right =>
    withPtrEqDecEq left right (fun _ => memberSetDec left right)
  match candidate with
  | none => (auxBlockOutcome snapshot key members, .absent)
  | some candidate =>
    if candidate.key = key then
      if candidate.members = members then
        match candidate.compiled with
        | none => (auxBlockOutcome snapshot key members, .workerFailed)
        | some (result, cache) =>
          let addresses := Ix.Compile.WorkerSuccess.checkExtension candidate.addresses snapshot.nameToAddr
          let blobs := Ix.Compile.WorkerSuccess.checkCompatible snapshot.blobs cache.blockBlobs
          if addresses && blobs then (.compiled result cache, .reused)
          else if addresses then (auxBlockOutcome snapshot key members, .blobMismatch)
          else (auxBlockOutcome snapshot key members, .addressMismatch)
      else (auxBlockOutcome snapshot key members, .sourceMismatch)
    else (auxBlockOutcome snapshot key members, .sourceMismatch)

def outcome (input : FixedInput) (snapshot : CompileEnv) (key : Ix.Name)
    (members : Ix.Set Ix.Name) (candidate : Option (Candidate input)) : AuxBlockOutcome :=
  match candidate with
  | none => auxBlockOutcome snapshot key members
  | some candidate => checkedOutcome input snapshot key members candidate

theorem selectOutcome_fst (input : FixedInput) (snapshot : CompileEnv) (key : Ix.Name)
    (members : Ix.Set Ix.Name) (candidate : Option (Candidate input)) :
    (selectOutcome input snapshot key members candidate).1 =
      outcome input snapshot key members candidate := by
  cases candidate with
  | none => rfl
  | some candidate =>
    dsimp only [selectOutcome, outcome, checkedOutcome]
    split
    · split
      · cases compiled : candidate.compiled with
        | none => rfl
        | some pair =>
          obtain ⟨result, cache⟩ := pair
          dsimp only
          split
          · rfl
          · split <;> rfl
      · rfl
    · rfl

theorem outcome_eq (input : FixedInput) (snapshot : CompileEnv)
    (fixed : input.Matches snapshot) (key : Ix.Name) (members : Ix.Set Ix.Name)
    (candidate : Option (Candidate input)) :
    outcome input snapshot key members candidate = auxBlockOutcome snapshot key members := by
  cases candidate with
  | none => rfl
  | some candidate => exact checkedOutcome_eq input snapshot fixed key members candidate

def applyRows (snapshot : CompileEnv) : List (Ix.Name × Ix.Name × Ix.Set Ix.Name) →
    DriverAcc → DriverAcc
  | [], acc => acc
  | (key, _, members) :: rest, acc =>
    applyRows snapshot rest (applyAuxBlockOutcome acc key members
      (auxBlockOutcome snapshot key members)).1

theorem applyRows_eq (snapshot : CompileEnv) (rows : List (Ix.Name × Ix.Name × Ix.Set Ix.Name))
    (acc : DriverAcc) :
    applyRows snapshot rows acc = rows.foldl (fun acc (key, _, members) =>
      (applyAuxBlockOutcome acc key members (auxBlockOutcome snapshot key members)).1) acc := by
  induction rows generalizing acc with
  | nil => rfl
  | cons row rows ih =>
    obtain ⟨key, rep, members⟩ := row
    exact ih _

/-- Publication advances once per original row, independently of execution
readiness. The callback sees only the representative, never the live maps. -/
def applyRowsIO (input : FixedInput) (snapshot : CompileEnv) (fixed : input.Matches snapshot)
    (choose : Choose input) (published : Ix.Name → IO Unit) (observe : Disposition → IO Unit) :
    (rows : List (Ix.Name × Ix.Name × Ix.Set Ix.Name)) → (acc : DriverAcc) →
    IO { result : DriverAcc // result = applyRows snapshot rows acc }
  | [], acc => pure ⟨acc, rfl⟩
  | (key, rep, members) :: rest, acc => do
    let candidate ← choose rep
    let selected := selectOutcome input snapshot key members candidate
    observe selected.2
    let next := (applyAuxBlockOutcome acc key members selected.1).1
    published rep
    let result ← applyRowsIO input snapshot fixed choose published observe rest next
    return ⟨result.val, by
      simpa only [applyRows, next, selected, selectOutcome_fst, outcome_eq input snapshot fixed]
        using result.property⟩

def applyReadyIO (input : FixedInput) (snapshot : CompileEnv) (fixed : input.Matches snapshot)
    (choose : Choose input) (published : Ix.Name → IO Unit) (observe : Disposition → IO Unit)
    (ready : WaveBlocks) (acc : DriverAcc) :
    IO { result : DriverAcc // result = applyOriginal snapshot ready acc } := do
  let result ← applyRowsIO input snapshot fixed choose published observe ready.toList acc
  return ⟨result.val, by
    simpa only [applyRows_eq, applyOriginal, Array.foldl_toList] using result.property⟩

/-- The wave calls its publisher exactly once with the original accumulator. -/
theorem foldWaveUsing_congrAt (left right : CompileEnv → WaveBlocks → DriverAcc → DriverAcc)
    (blocks : Ix.CondensedBlocks) (sched : FoldSchedule) (st : FoldState)
    (same : ∀ ready, left st.acc.cenv ready st.acc = right st.acc.cenv ready st.acc) :
    foldWaveUsing left blocks sched st = foldWaveUsing right blocks sched st := by
  simp only [foldWaveUsing, same]

private def waveDec : DecidableEq WaveBlocks := fun left right =>
  letI : DecidableEq (Ix.Set Ix.Name) := fun a b =>
    withPtrEqDecEq a b (fun _ => memberSetDec a b)
  withPtrEqDecEq left right (fun _ => inferInstance)

/-- Reuse the checked accumulator only for exactly the rows it published.
The original readiness/error and settlement code remains authoritative. The
second readiness pass is inexpensive and avoids assuming that a predictor
recognizes every malformed input. -/
def foldWaveIO (input : FixedInput) (blocks : Ix.CondensedBlocks) (sched : FoldSchedule)
    (width : Nat) (dbg : Bool) (choose : Choose input) (published : Ix.Name → IO Unit)
    (observe : Disposition → IO Unit)
    (st : FoldState) (fixed : input.Matches st.acc.cenv) :
    IO { result : Except String FoldState // result = foldWave blocks sched width dbg st } := do
  let ready := initialReady blocks sched st
  let after ← applyReadyIO input st.acc.cenv fixed choose published observe ready st.acc
  letI : DecidableEq WaveBlocks := waveDec
  let apply := fun (_ : CompileEnv) (current : WaveBlocks) (_ : DriverAcc) =>
    if current = ready then after.val else applyOriginal st.acc.cenv current st.acc
  let result := foldWaveUsing apply blocks sched st
  return ⟨result, by
    rw [foldWave_eq_using]
    apply foldWaveUsing_congrAt
    intro current
    simp only [apply, applyChunked_eq]
    split
    · rename_i same
      subst current
      exact after.property
    · rfl⟩

def foldWavesIO (input : FixedInput) (blocks : Ix.CondensedBlocks) (sched : FoldSchedule)
    (width : Nat) (dbg : Bool) (choose : Choose input) (published : Ix.Name → IO Unit) :
    (observe : Disposition → IO Unit) →
    (fuel : Nat) → (st : FoldState) → input.Matches st.acc.cenv →
    IO { result : Except String FoldState // result = foldWaves blocks sched width dbg fuel st }
  | _, 0, st, _ => pure ⟨if st.remaining == 0 then .ok st else
      .error s!"Only compiled {blocks.blocks.size - st.remaining}/{blocks.blocks.size} \
blocks - circular dependency?", rfl⟩
  | observe, fuel + 1, st, fixed => do
    if done : st.remaining == 0 then
      return ⟨.ok st, by simp only [foldWaves, done, ↓reduceIte]⟩
    else
      let wave ← foldWaveIO input blocks sched width dbg choose published observe st fixed
      match ran : wave.val with
      | .error message =>
        return ⟨.error message, by
          simp only [foldWaves, done, ← wave.property, ran]
          rfl⟩
      | .ok after =>
        have success : foldWave blocks sched width dbg st = .ok after := wave.property.symm.trans ran
        let result ← foldWavesIO input blocks sched width dbg choose published observe fuel after
          (foldWave_fixed input blocks sched width dbg st after fixed success)
        return ⟨result.val, by
          simp only [foldWaves, done, success]
          exact result.property⟩

end Ix.Compile.ReadyPublication
