import IxAI.Task
import IxAI.Cert

/-!
# The RL loop and the promotion boundary

Inside the loop the rewarder kernel-checks each candidate against the task interface; proving
every rollout would be wasted work, since most candidates are discarded. Accepted candidates that
add something new are *promoted*: they become store entries, and certificates are produced for
them once, for every later consumer.
-/

namespace IxAI

/-- A model, as the harness sees it: a task in, candidates out. -/
structure Agent where
  name : String
  propose : Task → List Candidate

structure Rollout where
  task : String
  candidate : String
  verdict : Verdict
  deriving Repr

structure EpisodeResult where
  rollouts : List Rollout
  /-- Accepted candidates kept for training data and promotion, one per task. -/
  promoted : List Candidate
  deriving Repr

/-- Scalar reward. Timeouts carry no signal rather than a negative one. -/
def Verdict.score : Verdict → Option Float
  | .accepted => some 1.0
  | .timeout => none
  | _ => some 0.0

def runEpisode (tasks : List Task) (agent : Agent) : EpisodeResult :=
  tasks.foldl (init := ⟨[], []⟩) fun acc t =>
    let cands := agent.propose t
    let rs := cands.map fun c => (c, reward t c)
    let rollouts := rs.map fun (c, v) => ⟨t.id, c.name, v⟩
    let firstWin := (rs.find? (·.2.isAccepted)).map (·.1)
    ⟨acc.rollouts ++ rollouts, acc.promoted ++ firstWin.toList⟩

def EpisodeResult.acceptRate (r : EpisodeResult) : Float :=
  if r.rollouts.isEmpty then 0.0
  else (r.rollouts.countP (·.verdict.isAccepted)).toFloat / r.rollouts.length.toFloat

/-- A dataset claim: every item is a checked constant of the store with this root. One
certificate serves every training run, ablation and external buyer that uses the dataset. -/
structure DatasetClaim where
  root : Digest
  items : List Address
  allowedAxioms : List String
  deriving Repr

def DatasetClaim.holdsIn (d : DatasetClaim) (s : Store) : Bool :=
  s.root == d.root && s.checkAll &&
    d.items.all fun a => s.entries.any fun e =>
      e.addr == a && e.axioms.all (d.allowedAxioms.contains ·)

end IxAI
