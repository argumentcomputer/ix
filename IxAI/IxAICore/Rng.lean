/-!
# A specified random number generator

xorshift64* on `Nat` with explicit reduction mod 2^64, so the kernel, compiled Lean and any other
implementation produce the same stream from the same seed.
-/

namespace IxAICore

def u64 (n : Nat) : Nat := n % 18446744073709551616

structure Rng where
  state : Nat
  deriving Repr, DecidableEq

def Rng.seeded (seed : Nat) : Rng := ⟨if u64 seed == 0 then 11400714819323198485 else u64 seed⟩

def Rng.next (r : Rng) : Nat × Rng :=
  let x := r.state
  let x := x ^^^ (x >>> 12)
  let x := u64 (x ^^^ (x <<< 25))
  let x := x ^^^ (x >>> 27)
  (u64 (x * 2685821657736338717), ⟨x⟩)

/-- A value in `[0, n)`. -/
def Rng.below (r : Rng) (n : Nat) : Nat × Rng :=
  let (v, r) := r.next
  (v % n, r)

/-- `count` values in `[0, n)`. -/
def Rng.draws (r : Rng) (n : Nat) : Nat → List Nat × Rng
  | 0 => ([], r)
  | k + 1 =>
    let (v, r) := r.below n
    let (vs, r) := r.draws n k
    (v :: vs, r)

/-- Replace element `i`. -/
def setAt {α : Type} : List α → Nat → α → List α
  | [], _, _ => []
  | _ :: as, 0, v => v :: as
  | a :: as, i + 1, v => a :: setAt as i v

/-- Fisher–Yates on a list: for `i = n-1 … 1`, swap position `i` with a uniform `j ≤ i`. -/
def shuffleAux {α : Type} [Inhabited α] : Nat → List α → Rng → List α × Rng
  | 0, l, r => (l, r)
  | i + 1, l, r =>
    let (j, r) := r.below (i + 2)
    let a := (l.drop (i + 1)).headD default
    let b := (l.drop j).headD default
    shuffleAux i (setAt (setAt l (i + 1) b) j a) r

def shuffle {α : Type} [Inhabited α] (l : List α) (r : Rng) : List α × Rng :=
  shuffleAux (l.length - 1) l r

end IxAICore
