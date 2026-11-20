import IxAICore.Decision

/-!
# Certifying training one step at a time

`train` folds the step function over the schedule. A trainer can instead report the run as a
chain of links `(before, batch, after)`. If every link applies the step function correctly and
starts where the previous one ended, the chain ends at exactly `train`'s result
(`train_eq_of_chain`).

Each link is an independent Ix `Eval` claim, `stepFn before batch = after`, with `before` and
`after` literal constants. Consecutive links share a constant, and so its content address, which
is what chains the claims. Links can be proved in parallel, incrementally, or by different
provers, and none of them has to re-run the data generation: the examples, the schedule and the
initial weights are certified once, by their own `Eval` claims.
-/

namespace IxAICore

structure Link (σ β : Type) where
  before : σ
  input : β
  after : σ

def ChainOK {σ β : Type} (f : σ → β → σ) : σ → List (Link σ β) → Prop
  | _, [] => True
  | s, l :: ls => l.before = s ∧ l.after = f l.before l.input ∧ ChainOK f l.after ls

def chainEnd {σ β : Type} : σ → List (Link σ β) → σ
  | s, [] => s
  | _, l :: ls => chainEnd l.after ls

theorem chain_eq_fold {σ β : Type} (f : σ → β → σ) :
    ∀ (s : σ) (ls : List (Link σ β)), ChainOK f s ls →
      chainEnd s ls = (ls.map (·.input)).foldl f s
  | _, [], _ => rfl
  | s, l :: ls, ⟨hb, ha, hr⟩ => by
    simp only [chainEnd, List.map_cons, List.foldl_cons]
    rw [chain_eq_fold f l.after ls hr, ha, hb]

/-- A chain of correctly applied steps over the certified examples, following the configured
schedule from the configured initial weights, ends at the specified training result. -/
theorem train_eq_of_chain {σ : Type} [Inhabited σ] (s : Spec σ) (c : Config)
    (examples : List (List Fx × List Fx)) (links : List (Link Model (List Nat)))
    (hex : (c.data s).map s.example = examples)
    (hsched : links.map (·.input) = c.schedule)
    (hchain : ChainOK (c.stepFn s examples) (c.init s) links) :
    chainEnd (c.init s) links = train s c := by
  rw [chain_eq_fold _ _ _ hchain, hsched]
  simp only [train, hex]

/-! ## The schedule, one epoch at a time -/

theorem schedule_eq_go (c : Config) :
    c.schedule = Config.schedule.go c c.epochs (Rng.seeded (c.seed + 7)) := rfl

theorem schedule_go_succ (c : Config) (e : Nat) (r : Rng) :
    Config.schedule.go c (e + 1) r =
      chunk c.batch (shuffle (List.range c.trainSize) r).1 c.trainSize ++
        Config.schedule.go c e (shuffle (List.range c.trainSize) r).2 := rfl

theorem schedule_go_zero (c : Config) (r : Rng) : Config.schedule.go c 0 r = [] := rfl

end IxAICore
