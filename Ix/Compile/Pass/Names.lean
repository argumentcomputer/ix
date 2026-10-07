/- # Pass 3: reserved names (D14) and the switch

## Contract
Input: Lean names (`Ix.Name`). Output: the reserved display names of the
faithful rewrite and the predicates on them.

* `_ix` is the reserved name component (D14). A Lean input name with a
  component that is `_ix` or starts with `_ix` is rejected under the switch
  (`reservedInput?`), so every reserved name below is fresh.
* The Ix auxiliaries of a changed block (Pass 2's canonical `rec`,
  `casesOn`, `recOn`, `below`, `brecOn`, `.go`, `.eq`, `_N`, and the
  canonical `IndPredBelow` family) are displayed as `x._ix.S` for the Lean
  name `x.S` (`x` a member of the Lean block, `S` the suffix): `A._ix.rec`,
  `A._ix.casesOn`. A nested auxiliary `all₀.rec_j` (Lean's source index `j`)
  is displayed by its canonical position `i` in its component:
  `rep₀._ix.rec_i`, where `rep₀` is the component's first class
  representative (`ixAuxName`).
* The image of a Lean auxiliary `a` (Def 3.4, Def 3.5) is stored under the
  Lean name `a` itself (decision 3, design document §4.5), so a bare or
  partial occurrence needs no other name. `imageName` (`a._ix`) is the
  spelling of the retired "residual image"; no compile emits it (the same
  spelling is `ixFormName`'s, for a definition that is never an image-kind
  head).
* The check of input names runs over the condensation the driver is given
  (`Ix.CompileM.pass3ReservedInput?`): in `ix compile-lean` that is the
  grounded condensation, so an ungrounded input name (which is not compiled)
  is not checked. When several input names are reserved, the message names
  the first met in the iteration order of `CondensedBlocks.blocks`, not a
  canonical choice (the Rust compiler names the least by pretty name).
* The decompile record of a rewritten call site is the metadata key pair
  `_ix.inline` (index of the source occurrence in `metaSharing`) and
  `_ix.inline_meta` (its arena root); the rewrite leaves the placeholder
  `[(_ix.inline, n)]` that the compiler replaces (`Ix.CompileM.compileKVMap`).
* The switch: Pass 3 is the default (the flip, M6, 2026-10-06); `IX_PASS3=off`
  selects the legacy call-site surgery, kept as the comparison mode for the
  gates against the Rust compiler until it implements Pass 3 (M6R);
  `IX_PASS3=images`, or the variable unset, selects Pass 3; any other value
  is refused (`switchVar`, `switchMode?`, `switchOn`, `switchFromEnv`).

## Faithfulness
Names are metadata: no definition here changes a term or an address.

## Canonicity
The reserved names depend on the canonical form only (class representatives
and canonical nested positions), never on addresses.

## Side condition and fallback
An input name with a reserved component makes the compile fail with a message
naming it (no fallback: a silent clash would bind a user name to an Ix
auxiliary).

## Non-canonical set and evidence
None. Evidence: the `pass3` suite checks the `_ix` names of every changed
block's auxiliaries.
-/
module
public import Ix.Environment
public section

namespace Ix.Compile.Pass

open Ix (Name)

/-- The environment variable that selects the mode (Pass 3 or the legacy surgery). -/
def switchVar : String := "IX_PASS3"

/-- The value of `IX_PASS3` that selects Pass 3 explicitly (the default). -/
def switchValue : String := "images"

/-- The value of `IX_PASS3` that selects the legacy call-site surgery (the
    Rust-aligned comparison mode until M6R). -/
def switchOffValue : String := "off"

/-- The mode when `IX_PASS3` is unset: Pass 3 (the flip, M6). -/
def switchDefault : Bool := true

/-- The mode a value of `IX_PASS3` selects: `some true` for Pass 3 (unset,
    or `images`), `some false` for the surgery (`off`), `none` for any other
    value (refused by `switchFromEnv`: a mistyped value must not silently
    select either mode). -/
def switchMode? : Option String → Option Bool
  | none => some switchDefault
  | some v =>
    if v == switchValue then some true
    else if v == switchOffValue then some false
    else none

/-- Is Pass 3 selected by this value of `IX_PASS3`? An unrecognised value
    selects neither mode; the drivers refuse it first (`switchFromEnv`). -/
def switchOn (v : Option String) : Bool := switchMode? v == some true

/-- The refusal of an unrecognised `IX_PASS3` value. -/
def switchRefusal (v : String) : String :=
  s!"{switchVar}={v} is not a mode: use {switchValue} (Pass 3, the default) or \
{switchOffValue} (the legacy surgery, the comparison mode against the Rust compiler)"

/-- The mode `IX_PASS3` selects in this process, or the refusal of an
    unrecognised value. -/
def switchFromEnv : IO (Except String Bool) := do
  let v ← IO.getEnv switchVar
  return match switchMode? v with
    | some b => .ok b
    | none => .error (switchRefusal (v.getD ""))

/-- The mode, for logs. -/
def switchLabel (on : Bool) : String :=
  if on then s!"on (Pass 3, the default; {switchVar}={switchValue} or unset)"
  else s!"off (legacy surgery, {switchVar}={switchOffValue})"

/-- The reserved component (D14). -/
def ixComponent : String := "_ix"

/-- A component that is reserved: `_ix` or any string starting with it. -/
def isReservedComponent (s : String) : Bool := s.startsWith ixComponent

/-- Some component of `n` is reserved. -/
def hasReserved : Name → Bool
  | .anonymous _ => false
  | .str p s _ => isReservedComponent s || hasReserved p
  | .num p _ _ => hasReserved p

/-- The rejection message of a Lean input name with a reserved component. -/
def reservedInput? (n : Name) : Option String :=
  if hasReserved n then
    some s!"input name '{n.pretty}' contains the reserved component `_ix` \
      (D14: `_ix` names the Ix auxiliaries and images of the faithful rewrite)"
  else none

/-- `_ix.inline`: the decompile record's `metaSharing` index (and, before
compilation, the placeholder index of the source occurrence). -/
def inlineKey : Name := Name.mkStr (Name.mkStr Name.mkAnon ixComponent) "inline"

/-- `_ix.inline_meta`: the decompile record's arena root. -/
def inlineMetaKey : Name := Name.mkStr (Name.mkStr Name.mkAnon ixComponent) "inline_meta"

/-- `a._ix`: the retired display name of a separately stored image of the
Lean auxiliary `a` (images are stored under `a` itself; unused by the
compile). -/
def imageName (a : Name) : Name := Name.mkStr a ixComponent

/-- The canonical form of the Lean constant `c` written by a proof-justified
pass (O7–O12, decision 5, D1): `c._ix`, the same shape as `imageName` (images
are stored under their Lean names, so the two never meet: a pass writes the
canonical form of a definition that is not an image-kind auxiliary). -/
def ixFormName (c : Name) : Name := Name.mkStr c ixComponent

/-- The reserved component of a structural handler re-typed by a
proof-justified pass (O9, O10, O12): `_ix_retyped`. It starts with `_ix`, so
no Lean input name carries it (`reservedInput?`), and it differs from
`ixComponent`, so the re-typed handler of Lean's `p.s` never has the
spelling `p._ix.s` that the clique hook gives the canonical counterpart of
Lean's encoding constant `p.s` (`Cliques.cliqueIxName`: `A.len._ix._f`). The
compile's check that a reserved name already bound is bound to the same
bytes (`Driver.compileCanon`) stays as the guard. -/
def retypedComponent : String := "_ix_retyped"

/-- The reserved name of the re-typed handler of the Lean constant `p.s`:
`p._ix_retyped.s` (`retypedComponent`). -/
def retypedName : Name → Option Name
  | .str p s _ => some (Name.mkStr (Name.mkStr p retypedComponent) s)
  | _ => none

/-- A name component. -/
inductive Comp where
  | s (x : String)
  | n (x : Nat)
  deriving BEq, Inhabited

/-- The components of a name, outermost first. -/
def comps : Name → List Comp
  | .anonymous _ => []
  | .str p s _ => comps p ++ [.s s]
  | .num p n _ => comps p ++ [.n n]

/-- Append components to a name. -/
def appendComps (n : Name) : List Comp → Name
  | [] => n
  | .s x :: rest => appendComps (Name.mkStr n x) rest
  | .n x :: rest => appendComps (Name.mkNat n x) rest

/-- Rebuild a name from its components. -/
def ofComps (cs : List Comp) : Name := appendComps Name.mkAnon cs

/-- `x ++ cs` with `x`'s components as a prefix of `n`'s: the rest. -/
def stripPrefix? (x n : Name) : Option (List Comp) :=
  let xs := comps x
  let ns := comps n
  if xs.length ≤ ns.length && ns.take xs.length == xs then some (ns.drop xs.length)
  else none

/-- A nested-index suffix component `kind_j` (`kind` one of `rec`, `below`,
`brecOn`, `j ≥ 1`): `(kind, j)`. -/
def nestedComp? : Comp → Option (String × Nat)
  | .s x =>
    ["rec", "below", "brecOn"].findSome? fun k =>
      if x.startsWith (k ++ "_") then
        ((x.drop (k.length + 1)).toNat?).bind fun j => if j ≥ 1 then some (k, j) else none
      else none
  | .n _ => none

/-- The display name of an Ix auxiliary of a changed block whose Lean name
is `n`. `members` is the Lean block's `all`; `rep₀` the first class
representative of the component that owns `n`; `perm` the component's source
permutation (`perm[j - 1] = some i`: Lean's `all₀.kind_j` is the component's
canonical nested auxiliary `i`). `none` when `n` hangs off no member. -/
def ixAuxName (members : Array Name) (rep₀ : Name) (perm : Array (Option Nat))
    (n : Name) : Option Name := Id.run do
  -- the longest member prefix
  let mut best : Option (Name × List Comp) := none
  for x in members do
    if let some rest := stripPrefix? x n then
      if !rest.isEmpty then
        match best with
        | some (_, r) => if rest.length < r.length then best := some (x, rest)
        | none => best := some (x, rest)
  let some (x, rest) := best | return none
  -- a nested auxiliary `all₀.kind_j…`: its canonical position
  if let some all0 := members[0]? then
    if x == all0 then
      if let some (c :: tl) := some rest then
        if let some (k, j) := nestedComp? c then
          if let some (some i) := perm[j - 1]? then
            return some (appendComps (Name.mkStr rep₀ ixComponent) (.s s!"{k}_{i + 1}" :: tl))
  return some (appendComps (Name.mkStr x ixComponent) rest)

/-- The Lean auxiliaries of a block that have images (design document §4.5):
`x.rec`, `x.casesOn`, `x.recOn`, `x.below`, `x.brecOn`, `x.brecOn.go`,
`x.brecOn.eq` for each member `x`, and `all₀.rec_j`, `all₀.below_j`,
`all₀.brecOn_j`, `all₀.brecOn_j.go`, `all₀.brecOn_j.eq` for each nested
auxiliary `j`, restricted to the names Lean has, with Lean's kind: a
recursor of the block for `rec`, a definition or theorem otherwise (an
`IndPredBelow` `x.below` is an inductive: it has no closed image and is
compiled as its own block, §4.6). -/
def imageKinds (const? : Name → Option Ix.ConstantInfo) (all : Array Name) :
    Array Name := Id.run do
  let some all0 := all[0]? | return #[]
  let numNested := match const? all0 with
    | some (.inductInfo v) => v.numNested
    | _ => 0
  -- Lean generates the `below`/`brecOn` family only for a recursive block
  -- (`isRec` is block-wide); otherwise such a name is the user's (SurgName)
  let recBlock := match const? all0 with
    | some (.inductInfo v) => v.isRec
    | _ => false
  let isRecOfBlock (n : Name) : Bool := match const? n with
    | some (.recInfo rv) => rv.all == all
    | _ => false
  let isDef (n : Name) : Bool := match const? n with
    | some (.defnInfo _) | some (.thmInfo _) => true
    | _ => false
  let mut out : Array Name := #[]
  let family (brecOn : Name) : Array Name :=
    #[brecOn, Name.mkStr brecOn "go", Name.mkStr brecOn "eq"]
  for x in all do
    let r := Name.mkStr x "rec"
    if isRecOfBlock r then out := out.push r
    for s in ["casesOn", "recOn"] do
      let n := Name.mkStr x s
      if isDef n then out := out.push n
    if recBlock then
      if isDef (Name.mkStr x "below") then out := out.push (Name.mkStr x "below")
      for n in family (Name.mkStr x "brecOn") do
        if isDef n then out := out.push n
  for j in [1:numNested + 1] do
    let r := Name.mkStr all0 s!"rec_{j}"
    if isRecOfBlock r then out := out.push r
    if recBlock then
      let b := Name.mkStr all0 s!"below_{j}"
      if isDef b then out := out.push b
      for n in family (Name.mkStr all0 s!"brecOn_{j}") do
        if isDef n then out := out.push n
  return out

end Ix.Compile.Pass

end
