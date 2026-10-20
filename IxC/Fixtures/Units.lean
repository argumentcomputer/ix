import IxC.Kernel.Units

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

end Tests.Ix.Kernel.UnitsFixtures
