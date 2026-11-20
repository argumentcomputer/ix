import IxAI.Num

/-!
# A tiny MLP and its training step

One hidden ReLU layer, one output, squared-error loss, plain SGD. Backpropagation is written out
by hand so the specification is a short, reviewable program. The same definitions run on any
`Arith` format.
-/

namespace IxAI

structure MLP (α : Type) where
  /-- `hidden` rows of `inputs` weights. -/
  w1 : List (List α)
  b1 : List α
  w2 : List α
  b2 : α
  deriving DecidableEq, Hashable, Repr

/-- One training example: features and a target. -/
structure Example (α : Type) where
  x : List α
  t : α
  deriving Repr

variable {α : Type} [Arith α]

open Arith

def MLP.preact (m : MLP α) (x : List α) : List α :=
  block (List.zipWith (fun row b => add (dot row x) b) m.w1 m.b1)

/-- A scalar rounded as a one-element block. -/
def blockScalar (x : α) : α := (block [x]).headD x

def MLP.forward (m : MLP α) (x : List α) : α :=
  add (dot m.w2 ((m.preact x).map relu)) m.b2

/-- What one example contributes to the batch gradient of `½ (y − t)²`: its input, hidden
activations, hidden deltas and output delta. -/
structure Delta (α : Type) where
  x : List α
  h : List α
  dz : List α
  dy : α

def MLP.delta (m : MLP α) (e : Example α) : Delta α :=
  let z := m.preact e.x
  let h := z.map relu
  let dy := blockScalar (sub (add (dot m.w2 h) m.b2) e.t)
  let dz := block (List.zipWith (fun w zj => if pos zj then mul dy w else zero) m.w2 z)
  ⟨e.x, h, dz, dy⟩

/-- `Σ xᵢ`, accumulated exactly and rounded once. -/
def sumExact (xs : List α) : α := dot xs (xs.map fun _ => ofInt 1)

/-- One SGD step on a batch. Every batch gradient entry is an exact sum over the batch's
examples, rounded once, so the order of examples within a batch does not affect the result in any
format. `lr` absorbs the batch-size division. -/
def MLP.step (lr : α) (m : MLP α) (batch : List (Example α)) : MLP α :=
  if batch.isEmpty then m else
  let ds := batch.map m.delta
  let col := fun (f : Delta α → List α) (j : Nat) => ds.map fun d => (f d).getD j zero
  let dys := ds.map (·.dy)
  let upd := fun (w g : α) => sub w (mul lr g)
  { w1 := m.w1.zipIdx.map fun (row, j) =>
      block (row.zipIdx.map fun (w, k) => upd w (dot (col (·.dz) j) (col (·.x) k)))
    b1 := block (m.b1.zipIdx.map fun (b, j) => upd b (sumExact (col (·.dz) j)))
    w2 := block (m.w2.zipIdx.map fun (w, j) => upd w (dot dys (col (·.h) j)))
    b2 := blockScalar (upd m.b2 (sumExact dys)) }

def MLP.train (lr : α) (m : MLP α) (batches : List (List (Example α))) : MLP α :=
  batches.foldl (MLP.step lr) m

def MLP.params (m : MLP α) : List α := m.w1.flatten ++ m.b1 ++ m.w2 ++ [m.b2]

def MLP.shapeOk (m : MLP α) (inputs hidden : Nat) : Bool :=
  m.w1.length == hidden && m.w1.all (·.length == inputs) && m.b1.length == hidden &&
    m.w2.length == hidden

end IxAI
