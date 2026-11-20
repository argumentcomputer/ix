import IxAI.Data
import IxAI.Model

/-!
# Training claims

A training run is specified by a config: seed, sizes, learning rate, epochs, batch size. The
seed fixes the initial weights and the batch schedule, and the dataset root fixes the data. The
run's result is then a pure function of the config and the dataset, `TrainConfig.spec`.

An untrusted trainer reports the run as a chain of steps. `chain_eq_fold` shows that a chain whose
every link checks ends exactly at the specified result. Checking is per step, so steps can be
verified independently and in parallel (and, with Ix, proved independently and aggregated).
-/

namespace IxAI

/-! ## Chains of steps, for any step function -/

structure Link (σ β : Type) where
  before : σ
  input : β
  after : σ
  deriving Repr

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

/-- Executable check of a chain, with an invariant required after every step. -/
def chainCheck {σ β : Type} [DecidableEq σ] (f : σ → β → σ) (inv : σ → Bool) :
    σ → List (Link σ β) → Bool
  | _, [] => true
  | s, l :: ls =>
    decide (l.before = s) && decide (l.after = f l.before l.input) && inv l.after &&
      chainCheck f inv l.after ls

theorem chainCheck_sound {σ β : Type} [DecidableEq σ] (f : σ → β → σ) (inv : σ → Bool) :
    ∀ (s : σ) (ls : List (Link σ β)), chainCheck f inv s ls = true →
      ChainOK f s ls ∧ (inv s = true → inv (chainEnd s ls) = true)
  | _, [], _ => ⟨trivial, id⟩
  | s, l :: ls, h => by
    simp only [chainCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hb, ha⟩, hi⟩, hr⟩ := h
    obtain ⟨hok, hinv⟩ := chainCheck_sound f inv l.after ls hr
    exact ⟨⟨hb, ha, hok⟩, fun _ => hinv hi⟩

/-- A checked chain from `s` ends at the specified fold, and the invariant holds at the end. -/
theorem chainCheck_spec {σ β : Type} [DecidableEq σ] (f : σ → β → σ) (inv : σ → Bool)
    (s : σ) (ls : List (Link σ β)) (h : chainCheck f inv s ls = true) (hs : inv s = true) :
    chainEnd s ls = (ls.map (·.input)).foldl f s ∧ inv (chainEnd s ls) = true :=
  let ⟨hok, hinv⟩ := chainCheck_sound f inv s ls h
  ⟨chain_eq_fold f s ls hok, hinv hs⟩

/-! ## The MLP training run -/

structure TrainConfig where
  seed : UInt64
  hidden : Nat
  /-- Learning rate as `lrRaw / 256`, already divided by the batch size. -/
  lrRaw : Int
  epochs : Nat
  batchSize : Nat
  /-- Every parameter must be finite and within `±bound / 256` after every step. -/
  bound : Int
  deriving Repr

/-- Fisher–Yates shuffle driven by the specified generator. -/
def shuffle (n : Nat) (r : Rng) : Array Nat × Rng := Id.run do
  let mut a := Array.range n
  let mut r := r
  for i' in [0:n] do
    let i := n - 1 - i'
    if i == 0 then break
    let (j, r') := r.below (i + 1)
    r := r'
    a := a.swapIfInBounds i j
  return (a, r)

/-- Batches of dataset indices for every epoch: each epoch is a fresh shuffle cut into batches. -/
def TrainConfig.schedule (c : TrainConfig) (n : Nat) : List (List Nat) := Id.run do
  let mut r := Rng.seeded (c.seed ^^^ 0x53434844)
  let mut out := #[]
  for _ in [0:c.epochs] do
    let (perm, r') := shuffle n r
    r := r'
    let l := perm.toList
    for b in [0:(n + c.batchSize - 1) / c.batchSize] do
      out := out.push ((l.drop (b * c.batchSize)).take c.batchSize)
  return out.toList

/-- The raw draws for the initial weights: uniform in `[-16, 16]`, in parameter order. -/
def TrainConfig.initDraws (c : TrainConfig) : List Int := Id.run do
  let mut r := Rng.seeded (c.seed ^^^ 0x494E4954)
  let mut draw : Array Int := #[]
  for _ in [0:c.hidden * numFeatures + 2 * c.hidden + 1] do
    let (v, r') := r.below 33
    r := r'
    draw := draw.push ((v : Int) - 16)
  return draw.toList

variable {α : Type} [Arith α] [DecidableEq α] [Enc α]

/-- Parameters in `MLP.params` order, reshaped. -/
def MLP.ofList (hidden : Nat) (p : List α) : MLP α :=
  { w1 := (List.range hidden).map fun j => (p.drop (j * numFeatures)).take numFeatures
    b1 := (p.drop (hidden * numFeatures)).take hidden
    w2 := (p.drop (hidden * numFeatures + hidden)).take hidden
    b2 := (p.drop (hidden * numFeatures + 2 * hidden)).headD Arith.zero }

def TrainConfig.init (c : TrainConfig) : MLP α :=
  MLP.ofList c.hidden (c.initDraws.map (Arith.ofScaled ·))

def TrainConfig.lr (c : TrainConfig) : α := Arith.ofScaled c.lrRaw

def TrainConfig.inv (c : TrainConfig) (m : MLP α) : Bool :=
  m.params.all fun p => Arith.within p c.bound.toNat

def Dataset.batch (d : Dataset) (idx : List Nat) : List (Example α) :=
  idx.filterMap fun i => (d.items[i]?).map Item.example

/-- The step function the chain is checked against: inputs are batch indices into the dataset. -/
def TrainConfig.stepFn (c : TrainConfig) (d : Dataset) (m : MLP α) (idx : List Nat) : MLP α :=
  MLP.step c.lr m (d.batch idx)

/-- The specified result of the run. -/
def TrainConfig.spec (c : TrainConfig) (d : Dataset) : MLP α :=
  (c.schedule d.items.size).foldl (c.stepFn d) c.init

/-- Weight commitment: BLAKE3 of the parameters' canonical encoding. -/
def MLP.commit (m : MLP α) : Digest := digestOf "weights" m.params

/-- The public statement of a run. -/
structure TrainClaim where
  datasetRoot : Digest
  config : TrainConfig
  finalCommit : Digest
  deriving Repr

/-- Verify a reported run by checking every step. The inputs must follow the config's schedule,
the dataset must match its root and pass its claim, and the chain must start at the specified
initial weights. -/
def verifyRun (claim : TrainClaim) (d : Dataset) (links : List (Link (MLP α) (List Nat))) : Bool :=
  d.root == claim.datasetRoot && d.check &&
    links.map (·.input) == claim.config.schedule d.items.size &&
    claim.config.inv (claim.config.init : MLP α) &&
    chainCheck (claim.config.stepFn d) claim.config.inv claim.config.init links &&
    (chainEnd claim.config.init links).commit == claim.finalCommit

/-- An accepted run ends at exactly the specified weights, which satisfy the invariant. -/
theorem verifyRun_sound (claim : TrainClaim) (d : Dataset) (links : List (Link (MLP α) (List Nat)))
    (h : verifyRun claim d links = true) :
    chainEnd claim.config.init links = (claim.config.spec d : MLP α) ∧
      claim.config.inv (chainEnd claim.config.init links) = true ∧
      d.check = true ∧ d.root = claim.datasetRoot := by
  simp only [verifyRun, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hroot, hcheck⟩, hsched⟩, hinit⟩, hchain⟩, _⟩ := h
  obtain ⟨hend, hinv⟩ := chainCheck_spec _ _ _ _ hchain hinit
  refine ⟨?_, hinv, hcheck, hroot⟩
  rw [hend, hsched]
  rfl

/-- Reference trainer: produces the chain an honest trainer would report. -/
def TrainConfig.run (c : TrainConfig) (d : Dataset) : List (Link (MLP α) (List Nat)) :=
  ((c.schedule d.items.size).foldl (init := ((c.init : MLP α), #[])) fun (m, acc) idx =>
    let m' := c.stepFn d m idx
    (m', acc.push ⟨m, idx, m'⟩)).2.toList

/-- Fraction of the dataset classified correctly (output sign against label), in percent. -/
def MLP.accuracy (m : MLP α) (d : Dataset) : Nat :=
  let ok := d.items.toList.countP fun i =>
    Arith.pos (m.forward (i.example : Example α).x) == i.label
  if d.items.size == 0 then 0 else ok * 100 / d.items.size

end IxAI
