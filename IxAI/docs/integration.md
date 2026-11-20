# Lane, ixvc and IxAI together

How the agent workbench (`lane.md`), Ix version control (`ixvc.md`) and the IxAI pipeline
(`plan.md`, `rl.md`) fit into one system. Lane and `ixvc` are local experiments; this document is
about how they should connect, not a record of shipped work.

## Three layers, one store

| Layer | Role | Owns |
|---|---|---|
| `ixvc` (substrate) | What exists and who said so | Ixon objects in the Truth Mines store: constants, namespaces, changes, conflicts, claims, certificates, refs |
| Lane (agent front end) | How agents act on Lean | Sessions and capabilities, goals, probe and prove, fuel, per-declaration merge, admission |
| IxAI (specs and models) | What is wanted, and how learning is certified | Specs, decision models, rewards, `train spec config = W` claims, safety gates |

The joining rule: Lane's blob store and change records are `ixvc` objects in the same store.
A Lane handoff is then an `ixvc` change and Lane's `submit` is `ixvc`'s admission step. The Lane
fork already addresses blobs with the BLAKE3 that Ix uses and roots snapshots as Merkle trees, so
this is a change of object format, not of design.

## Where they meet IxAI

### 1. Proof search as a certified RL environment

- An episode is a lane. Actions are tactics through `prove-session`, each bounded by
  deterministic heartbeat fuel (`--max-heartbeats`), so the same attempt costs the same on any
  machine and under any load.
- The reward is a Lean function in the spec over the verify records that `submit
  --require ix-checked` computes in the main agent's process. A worker never reports its own
  success; what enters the store is an IxC check record, which can be certified, with the change
  record as the trajectory.
- The triage argument carries over: nothing enters the store unless Ix accepted it, whatever the
  policy does, so a gap in the reward can cost efficiency but not soundness.
- `rl.md`'s exact-expected-advantage update needs a finite typed action set. A tactic menu with a
  fixed fuel budget is one, so the certified RL chain moves from triage routing to tactic choice
  unchanged.
- Prerequisite: worker containment (Lane change 9). Without it a policy can read answer keys or
  the admin token, which is the remaining route to reward hacking.

### 2. Decision models as routers in the agent loop

A Jev-style typed decision model chooses where to spend effort before any LLM call or
elaboration: `decide`, a capped search, an LLM attempt, or defer. This is the triage gate again:
the router only routes, a checker confirms before anything is published, the router's weights
have an Ixon address, and each routing decision is a decision receipt. `prop-hard` already has
this shape: a sound certificate where one fires, the model otherwise.

### 3. A data flywheel with lineage

Accepted changes carry the constants their proofs use (`lane premises`), which become
premise-selection labels. A dataset is a namespace root; retraining yields a claim
`train spec config D = W` attached to the change that records `W`. Model lineage (data, traces,
model, next model) is `ixvc` history with proofs, so anyone can check which data and which reward
produced which model.

### 4. A shared tactic-outcome cache

With goals returned as Ixon addresses (Lane change 10), every
`(env, goal, tactic, fuel) → outcome` is a store object. One agent's failed attempt is every other
agent's cache hit, and the cache doubles as supervised and RL training data with deterministic
labels.

### 5. Orchestrating the project itself

- Agents hand each other change addresses instead of transcripts; the receiver fetches lazily,
  reads the linked context and checks the claims.
- GPU and proving jobs go to `ixvc`'s local-mode job runner, which admits jobs by memory budget as
  ix's own aggregate controller does (`ix.ci-merge-tests/docs/prover-resource-defaults.md`). Lane
  leases elaboration slots from that runner rather than scheduling work itself; a swarm's
  in-process elaboration and the GPU prover then share one memory budget.
- A checkpoint is a `catalog` certificate over the namespace plus the model's training
  certificate: this model was trained on exactly this dataset root under this spec, and only
  checker-admitted outputs entered the store.

### 6. Generation as a sequence of typed decisions

A decision model can generate programs and proofs, not only classify them, if the environment
supplies the legal moves. Keep a partial term with typed holes; at each step the environment lists
the well-typed ways to fill one hole of type `T` (a local, a constructor of `T`, a constant whose
type fits and leaves holes for its arguments, a `λ` or `match`, or for proofs a tactic run with
fixed fuel); the model chooses one with a probability; when no holes remain the kernel checks the
term against its specification (a theorem it must satisfy, or tests).

- **No strings.** The term is an Ixon tree, alpha-invariant and addressed. Syntax errors, unknown
  identifiers and ill-typed terms cannot occur; only semantic failure remains, and the kernel
  catches it.
- **Every step is a Jev-shaped question**: a Choice over answers known before the model runs.
- **Exact reward**: the kernel accepts the specification or not, under deterministic fuel.
- **Free supervised data**: every constant in the store decomposes into the choice sequence that
  builds it.
- **Shared search states**: partial terms have addresses, so states deduplicate and cache across
  agents (section 4 generalised).
- **Reuse**: choosing which constant to apply at a hole is premise selection; tactic routing is
  the special case where the moves are tactics. Programs and proofs are the same problem: a
  constant that must typecheck against a type.

What makes it hard:

- Action sets at a Mathlib hole run to hundreds of thousands of constants, so the head ranks
  candidates filtered by type unification rather than choosing from a fixed list.
- Fully elaborated kernel terms are long (implicit arguments, instances); practical moves are
  macro actions (apply a lemma, run a tactic, add a case) with unification filling the rest.
- Dependent types make filling one hole change the others' types, so the environment needs
  unification: Lean's elaborator through Lane until Ix has its own.
- A greedy pass rarely succeeds; search guided by calibrated probabilities, with defer, does the
  work.
- The current Fx16 model is too small; this needs an encoder that reads Ixon, the same one premise
  selection needs.

#### First experiment: typed synthesis in the M2b λ-calculus

Everything in `IxAICore`, so the environment, the model, training and the reward are
kernel-evaluable and certifiable as for supervised training.

1. **Language.** The simply typed λ-calculus already in `IxAICore/Typed.lean` (`Ty`, `Term`,
   `infer`, with `infer_iff` proved), extended with primitive recursion `natRec` so that programs
   are total and interesting (addition, doubling, parity, comparison) while every program
   terminates within a fuel the spec fixes.
2. **Environment.** Terms with typed holes; `moves Γ T` lists the hole fillers: variables of type
   `T`, constructors, `λ` at arrow types, `ite`, `natRec` and application of a variable or
   library function. Theorem: every move preserves well-typedness and every well-typed term is
   reachable (`moves_sound`, `moves_complete`), so the model only ever chooses, and the search is
   complete.
3. **Tasks.** A target function given by its type and input–output examples, checked by a proven
   evaluator with fuel; task sets drawn from a seed (hidden target programs of bounded size), with
   a held-out split by target shape.
4. **Model.** The Fx16 decision model scoring each move from features of the hole type, the
   context, the move kind and the examples; a Choice over the move list at every step.
5. **Training.** Supervised on the choice sequences of the hidden targets, then the certified RL
   loop of `rl.md` with reward = all examples pass, exact expected advantage over the finite move
   list at each step.
6. **Measured.** Success rate within a fixed node budget against breadth-first enumeration (the
   no-model baseline) and against Opus 5.5 writing the term as text through a sub-agent, scored by
   the same checker; calibration of the per-step choices; and certificates for a training run and
   for one synthesised program's correctness.

The step after it moves the same loop to Lean kernel terms over a small Mathlib slice, with
lemmas as moves ranked by the premise scorer and Lane supplying unification.

## First steps

1. **A tool-using IxBench baseline through Lane.** Opus sub-agents with Lane tools on generated
   statements whose proofs are not on disk, scored only by `submit --require ix-checked` and
   recorded as `(statement address, proof BLAKE3, Ixon address, check outcome)`, digested without
   wall clock or tokens. This is the fair comparison for the M2b families, where a tool-using
   model could otherwise call `decide`.
2. **Lane's blob store in the Truth Mines store,** with change, conflict and verify records written
   as Ixon objects (`ixvc.md`, First steps 1).
3. **Goal, tactic and outcome triples from those runs logged to the store,** seeding the cache and
   an RL dataset.
4. **The triage RL loop on a small fixed tactic menu over M2b goals,** certified by the same chain
   as supervised training.
5. **Typed synthesis in the M2b λ-calculus** (section 6), the first generator.

## Open questions

- Is Lane `ixvc`'s front end with `ixvc` as the backend, or does `ixvc` absorb Lane's
  operations? This document assumes the first.
- One Lane server per repository or one per machine over a shared store?
- How a Claude Code sub-agent's sandbox lets Lane calls reach the socket while sources, `.lane`
  internals and answer keys stay unreadable, without repo-local `.claude/` configuration.
- Which statement classes give honest tool-using baselines.
- Whether reward functions over check records need their own refinement proofs, as the training
  step has, or can be evaluated directly as Ix Eval claims.
