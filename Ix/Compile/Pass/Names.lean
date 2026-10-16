/- # Pass 3: reserved names

## Contract
Input: Lean names (`Ix.Name`). Output: the reserved display names of the
faithful rewrite and the predicates on them.

* `_ix` is the reserved name component. A Lean input name with a
  component that is `_ix` or starts with `_ix` is refused (`reservedInput?`),
  and so is an input constant with a metadata key that has such a component
  (`reservedMetadataInput`): every reserved name below is then fresh, and no
  source metadata stands for a placeholder or decompile record. The IO
  pipeline (`Ix.CompileM.compileDecoratedConsts`) and the Rust compiler
  (`compile_env`) check both before compiling, over the grounded input;
  when several inputs are reserved both name the least message by its text
  (`Ix.CompileM.reservedInputRefusal?`, Rust `reserved_input_in`), an
  ordering of diagnostics, not a claim that pretty names identify names.
* The Ix auxiliaries of a changed block (Pass 2's canonical `rec`,
  `casesOn`, `recOn`, `below`, `brecOn`, `.go`, `.eq`, `_N`, and the
  canonical `IndPredBelow` family) are displayed as `x._ix.S` for the Lean
  name `x.S` (`x` a member of the Lean block, `S` the suffix): `A._ix.rec`,
  `A._ix.casesOn`. A nested auxiliary `all₀.rec_j` (Lean's source index `j`)
  is displayed by its canonical position `i` in its component:
  `rep₀._ix.rec_i`, where `rep₀` is the component's first class
  representative (`ixAuxName`).
* The image of a Lean auxiliary `a` is stored under the Lean name `a`
  itself, so a bare or partial occurrence needs no other name
  (`imageKinds` lists the auxiliaries that have images).
* The decompile record of a rewritten call site is the metadata key pair
  `_ix.inline` (index of the source occurrence in `metaSharing`) and
  `_ix.inline_meta` (its arena root); the rewrite leaves the placeholder
  `[(_ix.inline, n)]` that the compiler replaces.

Pass 3 is not wired yet: nothing here is read by the compile except the two
refusals.

## Faithfulness
Names are metadata: no definition here changes a term or an address.

## Canonicity
The reserved names depend on the canonical form only (class representatives
and canonical nested positions), never on addresses.

## Side condition and fallback
A reserved input name or metadata key makes the compile fail with a message
naming the constant (no fallback: a silent clash would bind a user name to an
Ix auxiliary, or a user annotation to a decompile record).
-/
module
public import Ix.Environment
public section

namespace Ix.Compile.Pass

open Ix (Name)

/-- The reserved component. -/
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
      (`_ix` names the Ix auxiliaries and images of the faithful rewrite)"
  else none

/-- The rejection message of a Lean input constant with a metadata key that
    has a reserved component (such a key could stand for the placeholder or
    decompile record of `inlineKey`). -/
def reservedMetadataInput (n : Name) : String :=
  s!"input constant '{n.pretty}' has a metadata key with the reserved component `_ix` \
    (`_ix` names the Ix auxiliaries and images of the faithful rewrite)"

/-- `_ix.inline`: the decompile record's `metaSharing` index (and, before
compilation, the placeholder index of the source occurrence). -/
def inlineKey : Name := Name.mkStr (Name.mkStr Name.mkAnon ixComponent) "inline"

/-- `_ix.inline_meta`: the decompile record's arena root. -/
def inlineMetaKey : Name := Name.mkStr (Name.mkStr Name.mkAnon ixComponent) "inline_meta"

/-- The canonical form of the Lean constant `c` written by a proof-justified
pass (O7–O12, decision 5, D1): `c._ix`. Images are stored under their Lean
names, so this name never clashes with an image: a pass writes the canonical
form of a definition that is not an image-kind auxiliary. -/
def ixFormName (c : Name) : Name := Name.mkStr c ixComponent

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

/-- `x ++ cs` with `x`'s components as a prefix of `n`'s: the rest. The
prefix is compared by components (strings and numbers), never by a stored
hash. -/
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
    if comps x == comps all0 then
      if let some (c :: tl) := some rest then
        if let some (k, j) := nestedComp? c then
          if let some (some i) := perm[j - 1]? then
            return some (appendComps (Name.mkStr rep₀ ixComponent) (.s s!"{k}_{i + 1}" :: tl))
  return some (appendComps (Name.mkStr x ixComponent) rest)

/-- The Lean auxiliaries of a block that have images: `x.rec`, `x.casesOn`,
`x.recOn`, `x.below`, `x.brecOn`, `x.brecOn.go`, `x.brecOn.eq` for each
member `x`, and `all₀.rec_j`, `all₀.below_j`, `all₀.brecOn_j`,
`all₀.brecOn_j.go`, `all₀.brecOn_j.eq` for each nested auxiliary `j`,
restricted to the names Lean has, with Lean's kind: a recursor of the block
for `rec`, a definition or theorem otherwise (an `IndPredBelow` `x.below` is
an inductive: it has no closed image and is compiled as its own block). -/
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
    | some (.recInfo rv) => rv.all.map comps == all.map comps
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
