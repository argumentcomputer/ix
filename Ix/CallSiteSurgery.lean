/-
  Ix.CallSiteSurgery: the classification of Lean's auto-generated
  auxiliaries by name, and the existence rule of the `.below`/`.brecOn`
  families.

  The call-site surgery this module was named for is deleted (CQ3.5): since
  Pass 3 no compile registers a call-site plan. What remains is used by the
  compiler, AuxGen and the decompiler:
  - `AuxKind`, `classifyAuxGen` and `isAuxGenSuffix` (Rust
    `classify_aux_gen`/`is_aux_gen_suffix`, decompile.rs);
  - `isPropFormer`, `belowFamilyLeanExists` and `blockLabel` (Rust
    `is_prop_former`, `below_family_lean_exists`, `aux_gen::block_label`),
    moved here from the deleted `Ix.CallSitePlan`.

  It lives below `Ix.CompileM` as a leaf module. Namespace `Ix.AuxGen`.
-/
module
public import Ix.Common
public import Ix.Address
public import Ix.Environment
public import Ix.Ixon
public import Ix.AuxGen.ExprUtils
public section

namespace Ix.AuxGen

/-- Kind of a Lean auto-generated auxiliary, as classified by name
    suffix. Mirrors Rust `AuxKind` (decompile.rs). Constructor-name
    renames forced by Lean's auto-generated declarations on this very
    inductive (`AuxKind.rec`/`recOn`/`casesOn` would collide):
    `Rec → recr`, `RecOn → recOnAux`, `CasesOn → casesOnAux`; the rest
    keep Rust's names. -/
inductive AuxKind where
  | recr | recOnAux | casesOnAux | below | belowRec
  | brecOn | brecOnGo | brecOnEq
  deriving BEq, Repr, Inhabited

/-- Classify an aux_gen constant by suffix, returning
    `(kind, root inductive)` — the base inductive the auxiliary is
    derived from. Mirrors Rust `classify_aux_gen` (decompile.rs:2157)
    branch-for-branch. -/
def classifyAuxGen (name : Name) : Option (AuxKind × Name) :=
  match name with
  | .str p1 s1 _ =>
    if s1 == "rec" || s1.startsWith "rec_" then
      -- X.rec / X.rec_N or X.below.rec / X.below_N.rec
      match p1 with
      | .str gp ps _ =>
        if ps == "below" || ps.startsWith "below_" then
          some (.belowRec, gp)
        else
          some (.recr, p1)
      | _ => some (.recr, p1)
    else if s1 == "recOn" || s1.startsWith "recOn_" then
      some (.recOnAux, p1)
    else if s1 == "casesOn" || s1.startsWith "casesOn_" then
      -- X.casesOn / X.casesOn_N or X.below.casesOn. The below wrapper
      -- roots under the FAMILY (like `X.below.rec` above) so it joins
      -- the family block's aux members and the decompiler's Phase 3b
      -- can regenerate it against the canonical below-rec.
      match p1 with
      | .str gp ps _ =>
        if ps == "below" || ps.startsWith "below_" then
          some (.casesOnAux, gp)
        else
          some (.casesOnAux, p1)
      | _ => some (.casesOnAux, p1)
    else if s1 == "below" || s1.startsWith "below_" then
      some (.below, p1)
    else if s1 == "brecOn" || s1.startsWith "brecOn_" then
      some (.brecOn, p1)
    else if s1 == "go" then
      -- X.brecOn.go or X.brecOn_N.go (nested auxiliary)
      match p1 with
      | .str gp ps _ =>
        if ps == "brecOn" || ps.startsWith "brecOn_" then
          some (.brecOnGo, gp)
        else
          none
      | _ => none
    else if s1 == "eq" then
      -- X.brecOn.eq or X.brecOn_N.eq (nested auxiliary)
      match p1 with
      | .str gp ps _ =>
        if ps == "brecOn" || ps.startsWith "brecOn_" then
          some (.brecOnEq, gp)
        else
          none
      | _ => none
    else
      none
  | _ => none

/-- Is `name` a Lean auto-generated auxiliary that aux-gen regenerates
    (`.rec`/`.rec_N`, `.recOn*`, `.casesOn*`, `.below*`, `.below.rec`,
    `.brecOn*`, `.brecOn*.go`, `.brecOn*.eq`)?

    Boolean projection of `classifyAuxGen` — Rust `is_aux_gen_suffix`
    (decompile.rs:2151). Used by the decompiler's Pass-1 skip and the
    roundtrip's aux classification. -/
def isAuxGenSuffix (name : Name) : Bool :=
  (classifyAuxGen name).isSome

/-! ## Existence of the `.below`/`.brecOn` families (A0, WB-B1) -/

/-- Whether a type is a Prop former: a forall telescope ending in `Prop`
    (Lean's `isPropFormerType` on an inductive's type, a syntactic telescope
    for every inductive the elaborator emits). Mirrors Rust
    `is_prop_former` (aux_gen.rs). -/
def isPropFormer (typ : Expr) : Bool := Id.run do
  let mut cur := typ
  repeat
    match cur with
    | .forallE _ _ body _ _ => cur := body
    | .sort (.zero _) _ => return true
    | _ => return false
  return false -- unreachable: the loop always returns

/-- Whether Lean generates the `.below`/`.brecOn` families (and their nested
    `_N` members) for the Lean mutual block `originalAll`, by Lean's own
    conditions, never by name shape:

    - Type-level (`Lean.Meta.mkBelow`/`mkBRecOn`): the inductive is
      recursive (`isRec`) and not a Prop former;
    - Prop-level (`Lean.Meta.IndPredBelow.mkBelow`): the inductive predicate
      is recursive and not `unsafe` (Lean also skips classes, which the
      compiler's environment does not record).

    `isRec` is a property of the whole Lean block, so the first member found
    decides. A user constant named `T.below`/`T.brecOn` for a non-recursive
    `T` (a definition, or a structure field accessor such as
    `IndPredBelow.NewDecl.below`) is therefore never taken for the
    auxiliary. Mirrors Rust `below_family_lean_exists` (aux_gen.rs). -/
def belowFamilyLeanExists (lookup : Name → Option ConstantInfo)
    (originalAll : Array Name) : Bool := Id.run do
  for n in originalAll do
    match lookup n with
    | some (.inductInfo v) =>
      return v.isRec && !(v.isUnsafe && isPropFormer v.cnst.type)
    | _ => pure ()
  return false

/-- The block a refusal names: the first member of its first canonical
    class. Mirrors Rust `aux_gen::block_label`. -/
def blockLabel (sortedClasses : Array (Array Name)) : String :=
  match sortedClasses[0]? >>= (·[0]?) with
  | some n => n.pretty
  | none => "<empty>"

end Ix.AuxGen
