import IxAIData.Rules

/-!
# Premise relevance as a typed decision

The featurizer maps a statement to a fixed-length `List Int`: hashed counts of the constants it
mentions, bucketed by their content address (`key`, the leading address bytes), so renaming a
constant or a bound variable changes nothing; then the counts of the twelve expression node kinds.
Constant buckets are indicators and node-kind counts are squashed to `⌊log₂ (n + 1)⌋`, at most 3,
so that inputs stay small for an 8-bit fixed-point learning rate.

A pair (statement, premise) is the statement's features, the premise's features, and their
overlap: per bucket, whether both mention a constant of that bucket; and a `PairContext`: the
premise's prior, the exact count of shared constant addresses (all and rare ones), and locality.
The decision model answers one
question about a pair, `relevant : Bool`; it is trained by `IxAICore.train` on positive pairs (a
premise the proof uses) and hard negatives (accessible premises it does not use). Premises are
ranked by the model's margin for `true`.
-/

namespace IxAIData

open IxAICore

def squash (cap n : Nat) : Int := Int.ofNat (min (Nat.log2 (n + 1)) cap)

/-- Add `k` at position `i`. -/
def addAt : List Nat → Nat → Nat → List Nat
  | [], _, _ => []
  | a :: as, 0, k => (a + k) :: as
  | a :: as, i + 1, k => a :: addAt as i k

def constCounts {α : Type} (buckets : Nat) (key : α → Nat) (s : Statement α) : List Nat :=
  s.consts.foldl (fun acc (c, k) => addAt acc (key c % buckets) k) (List.replicate buckets 0)

def stmtFeatures {α : Type} (buckets : Nat) (key : α → Nat) (s : Statement α) : List Int :=
  (constCounts buckets key s).map (squash 1) ++ (s.kinds.take 12).map (squash 3) ++
    List.replicate (12 - s.kinds.length) 0

/-- What relates a premise to a theorem beyond their statements: the premise's prior (how many
training theorems use it), the constants both statements mention (all, and those mentioned by at
most `rareBound` library statements), and declaration locality. -/
structure PairContext where
  prior : Nat
  shared : Nat
  sharedRare : Nat
  sameModule : Bool
  /-- Declarations between the premise and the theorem, when in the same module. -/
  distance : Nat

def contextFeatures (c : PairContext) : List Int :=
  [squash 3 c.prior, squash 3 c.shared, squash 3 c.sharedRare, if c.sameModule then 1 else 0,
   if c.sameModule && c.distance ≤ 8 then 1 else 0, if c.sameModule && c.distance ≤ 64 then 1 else 0]

def numContextFeatures : Nat := 6

/-- The pair featurizer's shape: hash buckets, and whether each statement's own features are
included or only the pair's overlap and context. -/
structure Features where
  buckets : Nat
  statements : Bool
  deriving DecidableEq, Repr

def Features.width (f : Features) : Nat := if f.statements then f.buckets + 12 else 0

def numPairFeatures (f : Features) : Nat := 2 * f.width + f.buckets + numContextFeatures

def pairFeatures {α : Type} (f : Features) (key : α → Nat) (s p : Statement α) (c : PairContext) :
    List Int :=
  (if f.statements then stmtFeatures f.buckets key s ++ stmtFeatures f.buckets key p else []) ++
    List.zipWith (fun a b => squash 1 (min a b)) (constCounts f.buckets key s) (constCounts f.buckets key p) ++
    contextFeatures c

/-- A training example: the pair's features and whether the proof uses the premise. -/
structure Pair where
  x : List Int
  relevant : Bool
  deriving Repr, Inhabited

def relevantQ : Question Pair Bool := ⟨"relevant", Pair.relevant⟩

/-- The relevance spec over a fixed list of training pairs: a state is a uniformly drawn pair. -/
def spec (f : Features) (pairs : List Pair) : Spec Pair :=
  { name := "premise-relevance"
    features := Pair.x
    numFeatures := numPairFeatures f
    slots := [relevantQ.slot]
    sample := fun r =>
      let (i, r) := r.below (max pairs.length 1)
      (getD pairs i default, r) }

/-- The model's margin for `relevant = true`, in units of `1/256`. -/
def score (m : Model) (x : List Int) : Int :=
  let os := m.outputs (x.map Fx.ofInt)
  (getD os 1 Fx.zero).raw - (getD os 0 Fx.zero).raw

/-! ## Ranking metrics -/

/-- Insert into a list sorted by descending score; ties keep the earlier element first. -/
def insertDesc {β : Type} (x : Int × β) : List (Int × β) → List (Int × β)
  | [] => [x]
  | y :: ys => if x.1 > y.1 then x :: y :: ys else y :: insertDesc x ys

/-- The `k` highest-scoring candidates, best first; ties keep candidate order. -/
def topK {β : Type} (k : Nat) (xs : List (Int × β)) : List β :=
  (xs.foldl (fun acc x => (insertDesc x acc).take k) []).map (·.2)

/-- `R@k` as a fraction `(hits, gold)`: how many of the gold premises are in the top `k`. -/
def recallAt {α : Type} [DecidableEq α] (k : Nat) (ranked : List α) (gold : List α) : Nat × Nat :=
  ((gold.filter fun g => (ranked.take k).contains g).length, gold.length)

end IxAIData
