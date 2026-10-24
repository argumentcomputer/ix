import IxC.Kernel.Units
import IxC.Kernel.Frontend.NatOpGround

/-! # The units check on hand-built declaration lists

`Ix.Kernel.checkUnits` (run by the fold after it accepts) on Source-mode
declaration lists. Only the declarations' names and kinds matter to it, so the
cases are axioms under chosen keys:

* passed: single declarations; a block's generated records (every name
  derived) followed by the block's own declaration, one unit;
* declined, each with its position and the colliding base named:
  - a **split block**: a generated record separated from its block by another
    declaration (a generated record over a base its unit's closing
    declaration does not declare), or after it (a run no declaration closes);
  - a **unit base equal to a front base** (the front's declarations are units
    of their own);
  - a **prelude-role base** declared again after the front;
  - the fold's own **basis record** in the rest;
  - a **prelude role past the front** (its first `preludeSize` declarations). -/

open Ix.Kernel

namespace Tests.Ix.Kernel.UnitsFixtures

def key (s : String) : Key .source := .id (.str .anonymous s)
def ax (k : Key .source) : Declaration .source := .axiomDecl ⟨k, [], .sort .zero⟩
/-- A generated record over `T` (a derived name). -/
def gen (T : String) (d : Derived := .model) : Declaration .source := ax (.aux (key T) d)

/-- Whether the check passes. -/
def passes (ds : List (Declaration .source)) : Bool :=
  (checkUnits ds.toArray).isOk

/-- Whether the check declines at position `i`, its message containing every
string of `parts`. -/
def declinedAt (ds : List (Declaration .source)) (i : Nat) (parts : List String) : Bool :=
  match checkUnits ds.toArray with
  | .ok _ => false
  | .error (e@(.notImplemented _), j) =>
    let s := toString e
    i == j && parts.all fun p => (s.splitOn p).length > 1
  | .error _ => false

/-! ## Passed -/

#guard passes []
#guard passes [ax (key "A"), ax (key "B")]
-- A block's generated records, then the block: one unit.
#guard passes [ax (key "A"), gen "T", gen "T" .tag, ax (key "T"), ax (key "B")]
#guard unitsOf [ax (key "A"), gen "T", gen "T" .tag, ax (key "T"), ax (key "B")] ==
  [[ax (key "A")], [gen "T", gen "T" .tag, ax (key "T")], [ax (key "B")]]
-- A front whose prelude roles the rest does not declare again.
#guard passes [ax (.role .nat), ax (.role .bool), ax (key "A")]

/-! ## Declined -/

-- A split block: `T`'s generated record, then `A`, then `T` (units
-- `[gen T, A]` and `[T]`): the first unit's generated record is over `T`, which
-- its closing declaration `A` does not declare.
#guard declinedAt [gen "T", ax (key "A"), ax (key "T")] 0 ["units:", "generated record", "T"]
-- A block's generated record after the block: a run no declaration closes.
#guard declinedAt [ax (key "T"), gen "T"] 1 ["units:", "not closed by a block"]
-- A unit base equal to a front base (`P` in the front, again in the rest).
#guard declinedAt [ax (key "P"), ax (key "Q"), ax (key "A"), ax (key "P")] 3 ["units:", "P"]
-- A prelude-role base declared again after the front.
#guard declinedAt [ax (.role .nat), ax (key "A"), ax (.role .nat)] 2 ["units:"]
-- The fold's own basis record in the rest.
#guard declinedAt [ax (key "A"), .basisDecl .natK] 1 ["units:", "basis record"]

/-- Twelve front declarations (the front is `preludeSize` long). -/
def front12 : List (Declaration .source) := (List.range preludeSize).map fun n => ax (key s!"F{n}")

#guard preludeSize == 12
-- A prelude role declared past the front (by a unit at position 12), though no
-- front declaration declares it.
#guard declinedAt (front12 ++ [ax (.role .andIntro)]) 12 ["units:", "prelude role", "past the front"]
-- The same role in the front passes.
#guard passes (ax (.role .andIntro) :: front12)

/-! ## The ground hoist keeps units whole

The hoist (`Ix.Kernel.Frontend.hoistNatOpGround`) moves a pinned `Nat`
operation's ground ahead of it. When a record it would move belongs to a
lowering of several declarations (here `Nat.pred`'s, a generated record then
the declaration), it leaves the stream as it is (`splitsUnit`): the fold then
meets `Nat.sub` before its ground `Nat.pred` and declines at it (its ground is
not installed), where the hoisted stream would have declined at `Nat.pred`'s
lowering, its generated record left behind: a decline either way, now with the
unit whole and in order. -/

open Ix.Kernel.Frontend in
/-- A definition named `k`, of type and value `Prop`. -/
def defn (k : Key .source) : Declaration .source := .defnDecl ⟨k, [], .sort .zero⟩ (.sort .zero) .opaque

/-- `Nat.sub`, then `Nat.pred`'s lowering: a generated record and its declaration. -/
def splitCase : List (Declaration .source) :=
  [defn natSubName, ax (.aux natPredName .model), defn natPredName]

-- the hoist would move `Nat.pred` (one record) out of its unit: the guard fires
#guard Ix.Kernel.Frontend.hoistReport splitCase.toArray == (1, true)
-- and the stream stays as it was
#guard (Ix.Kernel.Frontend.hoistNatOpGround splitCase.toArray).1.toList == splitCase
-- without the guard the move would split the unit
#guard (Ix.Kernel.Frontend.applyHoist splitCase.toArray
  (Ix.Kernel.Frontend.hoistTargets splitCase.toArray)).1.toList ==
  [defn natPredName, defn natSubName, ax (.aux natPredName .model)]

/-- `Nat.sub`, then an unrelated declaration, then `Nat.pred` alone. -/
def moveCase : List (Declaration .source) := [defn natSubName, ax (key "A"), defn natPredName]

-- a single-declaration unit moves as before
#guard Ix.Kernel.Frontend.hoistReport moveCase.toArray == (1, false)
#guard (Ix.Kernel.Frontend.hoistNatOpGround moveCase.toArray).1.toList ==
  [defn natPredName, defn natSubName, ax (key "A")]

end Tests.Ix.Kernel.UnitsFixtures
