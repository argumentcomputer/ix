import IxCC.Xv.Validate.NatMap
import IxCC.Xv.Syntax
import IxCC.Xv.Slots

/-!
# The validator's abstract state

`AState` maps each location to the set of virtual registers whose
current value it holds: `v ∈ a[l]` means that, in the matching runs, the Xl
location `l` equals Xv's `ρ v`. A missing location holds nothing known;
there is no `Top` (regalloc2 gap 2), and `≤` is pointwise inclusion, so a
smaller state claims less. The soundness argument (`Validate.sound`)
needs only that `Agree` is antitone in `≤` and preserved by each transfer
function below.

Everything here is kernel-evaluable (D17): locations are keyed by `Nat` in a
`NatMap`, sets are sorted lists, and every function recurses structurally.

- `stepMove`: a move copies the source's set to the destination; a move from
  a location holding nothing known leaves the destination holding nothing
  known (regalloc2 gap 1).
- `define`: a definition removes its register from every location (its old
  value is gone), then the destination holds exactly it.
- `bindParams`: an edge's parallel binding of block parameters, as a
  symbolic move over registers (regalloc2 `checker.rs:562-599`): each
  location loses the parameters and gains every parameter whose argument it
  holds. -/

namespace IxCC.Xv.Validate

open IxCC.Lir (VReg)

/-! ## Locations as keys -/

/-- An injective key: registers `0–15`, then slots, incoming and outgoing
cells interleaved. -/
def locKey : Loc → Nat
  | .reg r => gprIndex r
  | .slot i => 16 + 3 * i
  | .inArg i => 17 + 3 * i
  | .outArg i => 18 + 3 * i

/-- Whether a key is an outgoing cell's. -/
def isOutArgKey (k : Nat) : Bool := decide (18 ≤ k) && (k - 18) % 3 == 0

/-! ## Sets of registers (sorted, without duplicates) -/

abbrev VSet := List VReg

namespace VSet

def mem (x : VReg) : VSet → Bool
  | [] => false
  | y :: ys => if x == y then true else if x < y then false else mem x ys

def insert (x : VReg) : VSet → VSet
  | [] => [x]
  | y :: ys => if x == y then y :: ys else if x < y then x :: y :: ys else y :: insert x ys

/-- `xs` without `x`. A filter: on the sorted sets built here it is the
same as stopping at `x`'s place, and it is correct without sortedness, which
`Validate.sound` then need not track. -/
def erase (x : VReg) (xs : VSet) : VSet := xs.filter (· != x)

def subset (xs ys : VSet) : Bool := xs.all (mem · ys)

def ofList (xs : List VReg) : VSet := xs.foldl (fun s x => insert x s) []

/-! ### Compiled forms

The definitions above are what the proofs follow. The compiled code uses the
forms below, proved equal to them (`csimp`): `insert` as a loop, and `ofList`
and `subset` in linear time on the strictly increasing lists the validator
works with (it checks that a certificate's facts are; the sets it builds
from them stay so). -/

/-- Whether a list is strictly increasing. A loop. -/
def strictlyAsc : List VReg → Bool
  | a :: b :: rest => decide (a < b) && strictlyAsc (b :: rest)
  | _ => true

/-- `insert`, keeping the prefix it passes reversed in `acc`. -/
def insertGo (x : VReg) : VSet → VSet → VSet
  | acc, [] => acc.reverseAux [x]
  | acc, y :: ys =>
    if x == y then acc.reverseAux (y :: ys)
    else if x < y then acc.reverseAux (x :: y :: ys)
    else insertGo x (y :: acc) ys

theorem insertGo_eq (x : VReg) : ∀ (acc s : VSet), insertGo x acc s = acc.reverse ++ insert x s
  | acc, [] => by simp [insertGo, insert, List.reverseAux_eq]
  | acc, y :: ys => by
    simp only [insertGo, insert]
    by_cases h1 : (x == y) = true
    · simp [h1, List.reverseAux_eq]
    · by_cases h2 : x < y
      · simp [h1, h2, List.reverseAux_eq]
      · simp [h1, h2, insertGo_eq x (y :: acc) ys]

def insertTR (x : VReg) (s : VSet) : VSet := insertGo x [] s

@[csimp] theorem insert_eq_insertTR : @insert = @insertTR := by
  funext x s
  simp [insertTR, insertGo_eq]

theorem insert_of_lt {x : VReg} : ∀ {s : VSet}, (∀ y ∈ s, y < x) → insert x s = s ++ [x]
  | [], _ => rfl
  | y :: ys, h => by
    have hy : y < x := h y (by simp)
    have hne : (x == y) = false := beq_false_of_ne (Nat.ne_of_gt hy)
    have hnlt : ¬ x < y := Nat.not_lt.mpr (Nat.le_of_lt hy)
    simp only [insert, hne, hnlt, Bool.false_eq_true, ↓reduceIte, List.cons_append]
    rw [insert_of_lt fun z hz => h z (by simp [hz])]

theorem strictlyAsc_cons {a : VReg} {s : List VReg} (h : strictlyAsc (a :: s) = true) :
    strictlyAsc s = true ∧ ∀ y ∈ s, a < y := by
  induction s generalizing a with
  | nil => simp [strictlyAsc]
  | cons b rest ih =>
    simp only [strictlyAsc, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hab, hrest⟩ := h
    obtain ⟨-, hb⟩ := ih hrest
    refine ⟨hrest, fun y hy => ?_⟩
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hab
    · exact Nat.lt_trans hab (hb y hy)

theorem strictlyAsc_append {s t : List VReg} (h : strictlyAsc (s ++ t) = true) :
    strictlyAsc t = true ∧ ∀ y ∈ s, ∀ z ∈ t, y < z := by
  induction s with
  | nil => simpa using h
  | cons a s ih =>
    obtain ⟨hrest, ha⟩ := strictlyAsc_cons (by simpa using h)
    obtain ⟨ht, hst⟩ := ih hrest
    refine ⟨ht, fun y hy z hz => ?_⟩
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact ha z (by simp [hz])
    · exact hst y hy z hz

theorem foldl_insert_asc : ∀ (xs s : List VReg), strictlyAsc (s ++ xs) = true →
    xs.foldl (fun s x => insert x s) s = s ++ xs
  | [], s, _ => by simp
  | x :: xs, s, h => by
    have hlt : ∀ y ∈ s, y < x := fun y hy => (strictlyAsc_append h).2 y hy x (by simp)
    simp only [List.foldl_cons, insert_of_lt hlt]
    rw [foldl_insert_asc xs (s ++ [x]) (by simpa using h)]
    simp

def ofListTR (xs : List VReg) : VSet :=
  if strictlyAsc xs then xs else xs.foldl (fun s x => insert x s) []

@[csimp] theorem ofList_eq_ofListTR : @ofList = @ofListTR := by
  funext xs
  unfold ofList ofListTR
  split
  · next h => exact foldl_insert_asc xs [] (by simpa using h)
  · rfl

/-- `xs ⊆ ys` on strictly increasing lists, by one merge. -/
def subsetSorted : VSet → VSet → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
    if x == y then subsetSorted xs ys
    else if x < y then false
    else subsetSorted (x :: xs) ys

theorem mem_of_gt {z y : VReg} {ys : VSet} (h : y < z) : mem z (y :: ys) = mem z ys := by
  have hne : (z == y) = false := beq_false_of_ne (Nat.ne_of_gt h)
  have hnlt : ¬ z < y := Nat.not_lt.mpr (Nat.le_of_lt h)
  simp only [mem, hne, hnlt, Bool.false_eq_true, ↓reduceIte]

theorem all_mem_congr {ys ys' : VSet} : ∀ {xs : List VReg}, (∀ z ∈ xs, mem z ys = mem z ys') →
    xs.all (mem · ys) = xs.all (mem · ys')
  | [], _ => rfl
  | a :: as, h => by
    have hrest : as.all (mem · ys) = as.all (mem · ys') :=
      all_mem_congr fun z hz => h z (List.mem_cons_of_mem a hz)
    simp only [List.all_cons, h a (List.mem_cons_self), hrest]

theorem subsetSorted_eq : ∀ (xs ys : VSet), strictlyAsc xs = true → strictlyAsc ys = true →
    subsetSorted xs ys = xs.all (mem · ys)
  | [], _, _, _ => by simp [subsetSorted]
  | x :: xs, [], _, _ => by simp [subsetSorted, mem]
  | x :: xs, y :: ys, hx, hy => by
    obtain ⟨hxs, hxlt⟩ := strictlyAsc_cons hx
    obtain ⟨hys, _⟩ := strictlyAsc_cons hy
    by_cases h1 : x = y
    · subst h1
      have hmem : mem x (x :: ys) = true := by simp [mem]
      have hrest : xs.all (mem · (x :: ys)) = xs.all (mem · ys) :=
        all_mem_congr fun z hz => mem_of_gt (hxlt z hz)
      rw [List.all_cons, hmem, Bool.true_and, hrest]
      simp only [subsetSorted, beq_self_eq_true, ↓reduceIte]
      exact subsetSorted_eq xs ys hxs hys
    · have hbeq : (x == y) = false := beq_false_of_ne h1
      by_cases h2 : x < y
      · have hmem : mem x (y :: ys) = false := by
          simp only [mem, hbeq, h2, Bool.false_eq_true, ↓reduceIte]
        rw [List.all_cons, hmem, Bool.false_and]
        simp only [subsetSorted, hbeq, h2, Bool.false_eq_true, ↓reduceIte]
      · have hyx : y < x := Nat.lt_of_le_of_ne (Nat.not_lt.mp h2) (Ne.symm h1)
        have hall : (x :: xs).all (mem · (y :: ys)) = (x :: xs).all (mem · ys) :=
          all_mem_congr fun z hz => by
            simp only [List.mem_cons] at hz
            rcases hz with rfl | hz
            · exact mem_of_gt hyx
            · exact mem_of_gt (Nat.lt_trans hyx (hxlt z hz))
        rw [hall]
        simp only [subsetSorted, hbeq, h2, Bool.false_eq_true, ↓reduceIte]
        exact subsetSorted_eq (x :: xs) ys hx hys

def subsetTR (xs ys : VSet) : Bool :=
  if strictlyAsc xs && strictlyAsc ys then subsetSorted xs ys else xs.all (mem · ys)

@[csimp] theorem subset_eq_subsetTR : @subset = @subsetTR := by
  funext xs ys
  unfold subset subsetTR
  split
  · next h =>
    simp only [Bool.and_eq_true] at h
    exact (subsetSorted_eq xs ys h.1 h.2).symm
  · rfl

end VSet

/-! ## States -/

/-- Locations (by `locKey`) to the registers they hold; absent is `∅`. -/
abbrev AState := NatMap VSet

namespace AState

def empty : AState := .leaf

def get (a : AState) (l : Loc) : VSet := (a.find? (locKey l)).getD []

/-- Set a location's registers; `∅` removes the entry. -/
def set (a : AState) (l : Loc) (vs : VSet) : AState :=
  match vs with
  | [] => a.erase (locKey l)
  | _ => a.insert (locKey l) vs

def holds (a : AState) (l : Loc) (v : VReg) : Bool := VSet.mem v (a.get l)

/-- `a ≤ b`: every fact of `a` is a fact of `b`. -/
def le (a b : AState) : Bool :=
  a.all fun k vs => VSet.subset vs ((b.find? k).getD [])

/-- A move `dst ← src` (gap 1: an unknown source leaves `dst` unknown). -/
def stepMove (a : AState) (dst src : Loc) : AState := a.set dst (a.get src)

/-- Forget `v` everywhere (its value is about to change). -/
def forget (a : AState) (v : VReg) : AState :=
  a.filterMap fun _ vs => match VSet.erase v vs with
    | [] => none
    | vs => some vs

/-- Forget whatever a location holds. -/
def clear (a : AState) (l : Loc) : AState := a.erase (locKey l)

/-- Forget every outgoing stack cell (a call releases them). -/
def clearOutArgs (a : AState) : AState :=
  a.filterMap fun k vs => if isOutArgKey k then none else some vs

/-- Definitions `(v, l)`: forget each `v`, clear the clobbered registers,
then each `l` holds exactly its `v`. -/
def define (a : AState) (defs : List (VReg × Loc)) (clobbers : List Loc) : AState :=
  let a := defs.foldl (fun a (v, _) => a.forget v) a
  let a := clobbers.foldl clear a
  defs.foldl (fun a (v, l) => a.set l [v]) a

/-- The parameters bound by an edge with arguments `args`, in parallel. -/
def bindParams (a : AState) (params args : List VReg) : AState :=
  let pairs := params.zip args
  a.filterMap fun _ vs =>
    let kept := vs.filter fun v => !params.contains v
    let gained := pairs.foldl (fun s (p, x) => if VSet.mem x vs then VSet.insert p s else s) kept
    match gained with
    | [] => none
    | gs => some gs

/-- A state from explicit facts (a certificate). -/
def ofList (facts : List (Loc × List VReg)) : AState :=
  facts.foldl (fun a (l, vs) => a.set l (VSet.ofList (vs ++ a.get l))) empty

/-- The facts of a state, by key. -/
def facts (a : AState) : List (Nat × VSet) := a.toList

end AState

end IxCC.Xv.Validate
