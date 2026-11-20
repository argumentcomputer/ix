import IxAI
import IxAI.Examples

open IxAI IxAI.Examples

def showOutcome : Outcome → String
  | .accepted a => s!"accepted as {a}"
  | .rejected v => s!"rejected: {repr v}"
  | .unknownGoal => "rejected: not a spec goal"
  | .alreadyProved n => s!"skipped: already proved by {n}"
  | .deduplicated n => s!"deduplicated: same statement as {n}"

def section_ (title : String) : IO Unit := IO.println s!"\n== {title} =="

def main : IO Unit := do
  section_ "1. Orchestration: statements first, delegated proofs, acceptance by address"
  let (proj, outcomes) := runSubmissions project
  for ((w, g, c), o) in submissions.zip outcomes do
    IO.println s!"{w} → {g} ({c.name}): {showOutcome o}"
  let (proj, dup) := proj.submitHelper "w7" duplicateHelper
  IO.println s!"w7 → helper ({duplicateHelper.name}): {showOutcome dup}"
  let (done, total) := proj.progress
  IO.println s!"progress: {done}/{total} spec statements proved; open: {proj.openGoals.map (·.name)}"

  section_ "2. Training: tasks carved from the store, kernel-checked rewards"
  let tasks := proj.store.entries.map (mkTask proj.store · .standard)
  for t in tasks do
    IO.println s!"task {t.id}: interface exposes {t.interfaceSize} of {proj.store.entries.length} constants (statements only)"
  for agent in [honest, hacker] do
    let r := runEpisode tasks agent
    IO.println s!"{agent.name}: accept rate {r.acceptRate}, promoted {r.promoted.length}"
    for ro in r.rollouts do
      unless ro.verdict.isAccepted do
        IO.println s!"  {ro.task}/{ro.candidate}: {repr ro.verdict}"

  section_ "3. Promotion and light clients"
  let some chainGoal := proj.goalFor? "chain" | throw (IO.userError "missing goal")
  let some cert := proj.certify mock chainGoal | throw (IO.userError "certification failed")
  let root := proj.store.root
  let ok := lightClientAccepts mock root chain Policy.standard.allowedAxioms cert
  IO.println s!"light client, given only the statement and root {root}: accepts = {ok}"
  IO.println s!"mock certificate carries the whole store ({mock.size cert} bytes, grows with the proof);"
  IO.println "an Ix terminal certificate has a fixed size (864 B) whatever the store's size"
  let some e := proj.store.find? impTransAddr | throw (IO.userError "missing lemma")
  let some path := proj.store.membership? impTransAddr | throw (IO.userError "no path")
  IO.println s!"membership of {e.name}: {path.siblings.length} sibling hashes, verifies = {path.verify root e.addr}"
  let tampered := { cert with witness := { entries := proj.store.entries.take 2 } }
  IO.println s!"certificate from a different store: accepts = {lightClientAccepts mock root chain [] tampered}"

  section_ "4. Typed decisions behind a certified gate"
  for ans in [⟨[950, 30, 20]⟩, ⟨[600, 300, 100]⟩, ⟨[100, 450, 450]⟩] do
    let a : ChoiceAnswer := ans
    IO.println s!"{a.permille}: concentration {a.concentration}‰ → {repr (approvalGate.decide a)}"
