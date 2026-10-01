import Ix.Kernel.Verify.Level
import Ix.Kernel.Verify.LevelGeran
import Ix.IxonUniv

/-! # The kernel's level comparison against brute-force evaluation

`Ix.Kernel.Level.leq` is nanoda's comparison with Géran's sublevels as the
fallback of its `(param, max)` case (`Ix/Kernel/Level.lean`,
`Ix/Kernel/LevelGeran.lean`). `leqCore_sound` proves a `true` verdict
pointwise; `Geran.leq_iff` proves the fallback a decision. This host-only
gate checks that the whole comparison is complete in practice too. For every
pair below it compares `Level.leq`, `Level.isEquiv` and `Level.Geran.leq`
(at offsets `-2‥2`) with evaluation (`Level.eval`) at every valuation of the
parameters in a range:

* exhaustively: every level of up to five constructors over two parameters
  and of up to four over three, at values `0‥M`, where `M` is four above the
  pair's largest `succ` nesting;
* on 100,000 random pairs of up to sixteen constructors over three
  parameters, with each pair's `max` commuted and an `imax` absorbed (so
  that true equalities are frequent), at values `{0, 1, 2, M - 1, M}`;
* on 20,000 random levels of up to twelve constructors over three
  parameters, biased towards `imax` by a parameter (the shape of canonical
  forms), against the same level rewritten by laws of the semantics
  (equal by construction), at the same values;
* on 20,000 such levels through Ixon's canonical form (`Ix/IxonUniv.lean`,
  the form the reader hands the checker): a level against its canonical
  form, and the canonical form of a `max`, `imax` or `succ` against the
  constructor over canonical forms, as type inference builds them
  (`RatFunc.liftOn_def` is `max (canon W) 1` against `canon (max 1 W)`).
  These pairs are not all equalities: `canonUniv` changes the value of some
  levels (the smallest found is `imax (imax (imax u w + 1) u) v`, whose
  canonical form is `2` at `u = 0, v = 1, w = 2` where the level is `1`),
  counted, not failures;
* on the recorded witnesses: Ixon's canonical levels of `RatFunc.liftOn_def`
  and the equality Ix.Tc's subsumption misses.

Some valuation at values in `{0, 1, M}` is a counterexample whenever one
exists, at offsets up to `2` (the separating valuations of
`Geran.dominated_of_le` work with any `N` above the other side's
`valueBound`), so the oracle is exact. A `true` verdict that some valuation
refutes is unsound; a `false` verdict that no valuation refutes is
incomplete; a `none` is an internal error. Each is a failure. Output is one
summary line; the exit code is nonzero on any failure. -/

namespace Tests.Ix.Kernel.LevelComparison

open _root_.Ix.Kernel (Level Name)

def param (i : Nat) : Level := .param (.str .anonymous s!"u{i}")

/-- Every level with exactly `size` constructors over `params` parameters. -/
partial def levelsOfSize (params : Nat) (size : Nat) : Array Level :=
  if size = 0 then #[]
  else if size = 1 then #[.zero] ++ (List.range params).toArray.map param
  else Id.run do
    let mut out : Array Level := (levelsOfSize params (size - 1)).map .succ
    for i in [1:size - 1] do
      let left := levelsOfSize params i
      let right := levelsOfSize params (size - 1 - i)
      for a in left do
        for b in right do
          out := out.push (.max a b) |>.push (.imax a b)
    return out

def levelsUpTo (params size : Nat) : Array Level :=
  (List.range (size + 1)).foldl (fun acc n => acc ++ levelsOfSize params n) #[]

/-- The largest `succ` nesting. -/
def offset : Level → Nat
  | .zero | .param _ => 0
  | .succ l => offset l + 1
  | .max a b | .imax a b => Max.max (offset a) (offset b)

/-- Every valuation of `params` parameters with values in `values`. -/
def valuations (params : Nat) (values : List Nat) : List (Name → Nat) :=
  let tuples := (List.range params).foldr
    (fun _ rest => values.flatMap fun v => rest.map (v :: ·)) [[]]
  tuples.map fun vs n => match n with
    | .str .anonymous s =>
      match (s.drop 1).toNat? with
      | some i => vs.getD i 0
      | none => 0
    | _ => 0

/-- `a ≤ b + diff` at every valuation in `vals`. -/
def bruteLe (vals : List (Name → Nat)) (a b : Level) (diff : Int) : Bool :=
  vals.all fun φ => (Level.eval φ a : Int) ≤ Level.eval φ b + diff

partial def levelString : Level → String
  | .zero => "0"
  | .succ l => s!"{levelString l}+1"
  | .max a b => s!"max({levelString a},{levelString b})"
  | .imax a b => s!"imax({levelString a},{levelString b})"
  | .param (.str _ s) => s
  | .param _ => "?"

structure Counts where
  pairs : Nat := 0
  unsound : Nat := 0
  incomplete : Nat := 0
  internal : Nat := 0
  geranWrong : Nat := 0
  equalities : Nat := 0
  /-- canonical forms that differ in value from their level (not a failure
  here: `Ix/IxonUniv.lean`'s, see the canonical family) -/
  canonChanged : Nat := 0
  witness : Option String := none
  deriving Inhabited

def Counts.note (c : Counts) (w : String) : Counts :=
  { c with witness := c.witness <|> some w }

/-- Record one verdict against the truth. -/
def Counts.verdict (c : Counts) (what : String) (v : Option Bool) (truth : Bool) : Counts :=
  match v, truth with
  | some true, false => { c with unsound := c.unsound + 1 }.note s!"unsound: {what}"
  | some false, true => { c with incomplete := c.incomplete + 1 }.note s!"incomplete: {what}"
  | none, _ => { c with internal := c.internal + 1 }.note s!"internal error: {what}"
  | _, _ => c

/-- One pair, against the valuations `vals`: `leq` both ways, `isEquiv`, and
`Geran.leq` at offsets `-2‥2`. -/
def check (vals : List (Name → Nat)) (c : Counts) (a b : Level) : Counts := Id.run do
  let sa := levelString a
  let sb := levelString b
  let le := bruteLe vals a b 0
  let ge := bruteLe vals b a 0
  let mut c := { c with pairs := c.pairs + 1 }
  if le && ge then c := { c with equalities := c.equalities + 1 }
  c := c.verdict s!"leq {sa} {sb}" (Level.leq a b) le
  c := c.verdict s!"leq {sb} {sa}" (Level.leq b a) ge
  c := c.verdict s!"isEquiv {sa} {sb}" (Level.isEquiv a b) (le && ge)
  for d in [-2, -1, 0, 1, 2] do
    if Level.Geran.leq a b d != bruteLe vals a b d then
      c := { c with geranWrong := c.geranWrong + 1 }.note s!"Geran.leq {sa} {sb} {d}"
  return c

/-- Exhaustively, at values `0‥M`. -/
def exhaustive (params size : Nat) (c : Counts) : Counts := Id.run do
  let levels := levelsUpTo params size
  let mut c := c
  for a in levels do
    for b in levels do
      let m := Max.max (offset a) (offset b) + 4
      c := check (valuations params (List.range (m + 1))) c a b
  return c

/-- A deterministic pseudo-random level of at most `size` constructors. -/
partial def randomLevel (params : Nat) (size : Nat) (seed : UInt64) : Level × UInt64 :=
  let seed := seed * 6364136223846793005 + 1442695040888963407
  let pick := ((seed >>> 33) % 8).toNat
  if size ≤ 1 || pick < 2 then
    (if pick % 2 = 0 then .zero else param (((seed >>> 40).toNat) % params), seed)
  else if pick < 3 then
    let (a, seed) := randomLevel params (size - 1) seed
    (.succ a, seed)
  else
    let (a, seed) := randomLevel params (size / 2) seed
    let (b, seed) := randomLevel params (size / 2) seed
    (if pick < 5 then .max a b else .imax a b, seed)

/-- Random pairs, each also with its `max` commuted and an `imax` absorbed,
at values `{0, 1, 2, M - 1, M}`. -/
def random (params size count : Nat) (c : Counts) : Counts := Id.run do
  let mut c := c
  let mut seed : UInt64 := 17
  for _ in [0:count] do
    let (a, s1) := randomLevel params size seed
    let (b, s2) := randomLevel params size s1
    seed := s2
    let m := Max.max (offset a) (offset b) + 4
    let vals := valuations params [0, 1, 2, m - 1, m]
    for (x, y) in [(a, b), (Level.max a b, Level.max b a), (Level.max a (.imax a b), Level.max a b)] do
      c := check vals c x y
  return c

def next (seed : UInt64) : UInt64 := seed * 6364136223846793005 + 1442695040888963407

/-- A pseudo-random level biased towards the shapes of canonical forms:
`imax` by a parameter, offsets and `max`. -/
partial def biasedLevel (params size : Nat) (seed : UInt64) : Level × UInt64 :=
  let seed := next seed
  let pick := ((seed >>> 33) % 10).toNat
  let p := param (((seed >>> 40).toNat) % params)
  if size ≤ 1 || pick < 2 then (if pick = 0 then .zero else p, seed)
  else if pick < 4 then
    let (a, seed) := biasedLevel params (size - 1) seed
    (.succ a, seed)
  else if pick < 6 then
    let (a, seed) := biasedLevel params (size / 2) seed
    let (b, seed) := biasedLevel params (size / 2) seed
    (.max a b, seed)
  else if pick < 9 then
    let (a, seed) := biasedLevel params (size - 1) seed
    (.imax a p, seed)
  else
    let (a, seed) := biasedLevel params (size / 2) seed
    let (b, seed) := biasedLevel params (size / 2) seed
    (.imax a b, seed)

/-- Rewrite by laws of the semantics at pseudo-random positions:
`succ` over `max`, `max` commuted, `imax a b ≤ max a b`, `imax` over a `max`
or an `imax` on its right, `imax a (succ c) = max a (succ c)`,
`b ≤ imax a b`, and `imax (max a b) b = imax a b`. -/
partial def rewrite (l : Level) (seed : UInt64) : Level × UInt64 :=
  let seed := next seed
  let pick := ((seed >>> 33) % 8).toNat
  match l with
  | .succ a =>
    let (a, seed) := rewrite a seed
    match a with
    | .max x y => if pick < 3 then (.max (.succ x) (.succ y), seed) else (.succ a, seed)
    | a => (.succ a, seed)
  | .max a b =>
    let (a, seed) := rewrite a seed
    let (b, seed) := rewrite b seed
    match pick with
    | 0 | 1 => (.max b a, seed)
    | 2 => (.max (.max a b) (.imax a b), seed)
    | _ => (.max a b, seed)
  | .imax a b =>
    let (a, seed) := rewrite a seed
    let (b, seed) := rewrite b seed
    match b, pick with
    | .max x y, 0 | .max x y, 1 => (.max (.imax a x) (.imax a y), seed)
    | .imax x y, 0 | .imax x y, 1 => (.max (.imax a y) (.imax x y), seed)
    | .succ _, 0 | .succ _, 1 => (.max a b, seed)
    | _, 2 => (.max (.imax a b) b, seed)
    | _, 3 => (.imax (.max a b) b, seed)
    | _, _ => (.imax a b, seed)
  | l => (l, seed)

/-- Biased random levels against two rounds of rewriting (an equality by
construction), and against a further round, at values
`{0, 1, 2, M - 1, M}`. -/
def rewrites (params size count : Nat) (c : Counts) : Counts := Id.run do
  let mut c := c
  let mut seed : UInt64 := 29
  for _ in [0:count] do
    let (a, s) := biasedLevel params size seed
    let (b, s) := rewrite a s
    let (b, s) := rewrite b s
    let (b', s) := rewrite b s
    seed := s
    let m := Max.max (Max.max (offset a) (offset b)) (offset b') + 4
    let vals := valuations params [0, 1, 2, m - 1, m]
    c := check vals (check vals c a b) b' a
  return c

/-- Ixon's universe of a level over `param`s (`u{i}` is `var i`), and back,
as the reader converts it (`Ix.Kernel.IxonReader.convUniv`). -/
def toUniv : Level → Ixon.Univ
  | .zero => .zero
  | .succ l => .succ (toUniv l)
  | .max a b => .max (toUniv a) (toUniv b)
  | .imax a b => .imax (toUniv a) (toUniv b)
  | .param (.str .anonymous s) => .var ((s.drop 1).toNat?.getD 0).toUInt64
  | .param _ => .var 0

def ofUniv : Ixon.Univ → Level
  | .zero => .zero
  | .succ u => .succ (ofUniv u)
  | .max a b => .max (ofUniv a) (ofUniv b)
  | .imax a b => .imax (ofUniv a) (ofUniv b)
  | .var i => param i.toNat

/-- Ixon's canonical form of a level (`Ix/IxonUniv.lean`), the form the
reader hands the checker. -/
def canon (l : Level) : Level := ofUniv (Ixon.canonUniv (toUniv l))

/-- Canonical forms against levels built from them, as the checker meets
them: a canonical level against itself, and the canonical form of a
`max`, `imax` or `succ` against the same constructor over canonical forms
(`RatFunc.liftOn_def` is `max (canon W) 1` against `canon (max 1 W)`), on
biased random levels, at values `{0, 1, 2, M - 1, M}`. -/
def canonical (params size count : Nat) (c : Counts) : Counts := Id.run do
  let mut c := c
  let mut seed : UInt64 := 41
  for _ in [0:count] do
    let (a, s) := biasedLevel params size seed
    let (b, s) := biasedLevel params size s
    seed := s
    let one := Level.succ .zero
    let pairs := [(a, canon a), (Level.max (canon a) one, canon (.max one a)),
      (Level.max (canon a) (canon b), canon (.max a b)),
      (Level.imax (canon a) (canon b), canon (.imax a b)),
      (Level.succ (canon a), canon (.succ a))]
    let m := pairs.foldl (fun m (x, y) => Max.max m (Max.max (offset x) (offset y))) 0 + 4
    let vals := valuations params [0, 1, 2, m - 1, m]
    unless bruteLe vals a (canon a) 0 && bruteLe vals (canon a) a 0 do
      c := { c with canonChanged := c.canonChanged + 1 }
    for (x, y) in pairs do c := check vals c x y
  return c

def succN (l : Level) : Nat → Level
  | 0 => l
  | k + 1 => .succ (succN l k)

/-- The recorded witnesses. -/
def witnesses (c : Counts) : Counts :=
  let u := param 0
  let v := param 1
  -- Ixon's canonical levels in `RatFunc.liftOn_def`
  let subtypeLevel := Level.max (.imax (.max (succN u 2) (succN v 1)) v) (succN .zero 1)
  let eqLevel := Level.max (succN v 1) (.imax (succN u 2) v)
  -- equal; Ix.Tc's `univEq` misses it
  let tcX := Level.max (succN v 1) (.imax (.imax (succN .zero 2) u) v)
  let tcY := Level.max (succN v 1) (.imax u v)
  let vals := valuations 2 (List.range 8)
  check vals (check vals c subtypeLevel eqLevel) tcX tcY

def main : IO UInt32 := do
  let c := witnesses {}
  let wOk := c.equalities == 2 && c.unsound + c.incomplete + c.internal + c.geranWrong == 0
  let c := exhaustive 3 4 (exhaustive 2 5 c)
  let c := random 3 16 100000 c
  let c := rewrites 3 12 20000 c
  let c := canonical 3 10 20000 c
  IO.println s!"Level comparison against evaluation: {c.pairs} pairs, {c.equalities} \
    equalities; unsound {c.unsound}; incomplete {c.incomplete}; internal errors \
    {c.internal}; Geran.leq disagreements {c.geranWrong}; canonical forms that change \
    their level's value {c.canonChanged}"
  if let some w := c.witness then IO.eprintln s!"first failure: {w}"
  unless wOk do IO.eprintln "a recorded witness is not decided as an equality"
  let failed := c.unsound + c.incomplete + c.internal + c.geranWrong
  return if failed == 0 && wOk then 0 else 1

end Tests.Ix.Kernel.LevelComparison

def main : IO UInt32 := Tests.Ix.Kernel.LevelComparison.main
