/-
  Ix.CallSitePlan: call-site surgery plan data model.

  Mirrors the plan structures of `crates/compile/src/compile/surgery.rs`
  (:50-175). Lives BELOW `Ix.CompileM` as a leaf module (unlike Rust,
  where everything shares one crate): the plans are COMPUTED by
  `Ix.AuxGen.Surgery` (which imports CompileM) but CONSUMED by
  `Ix.CompileM.compileExpr`'s call-site arms — so the type definitions
  must sit below both. Namespace stays `Ix.AuxGen` (the natural home;
  moving the defs here is layout only).
-/
module
public import Ix.Common
public import Ix.Address
public import Ix.Environment
public import Ix.Ixon
public section

namespace Ix.AuxGen

/-! ## Plan data model (surgery.rs:50-175)

Declaration order deviation: Rust declares `CallSitePlan` (surgery.rs:56)
before `AuxHeadRewrite` (surgery.rs:101); Lean needs the dependency
first. Field-for-field identical. -/

structure AuxHeadRewrite where
  /-- The external inductive's recursor (the alias target, e.g. `List.rec`). -/
  targetRec : Name
  /-- Source motive position of the evaporated aux (`nUserMotives + j`). -/
  targetMotivePos : Nat
  deriving Repr, Nonempty, Inhabited, BEq

/-- Per-auxiliary surgery plan for call-site argument reordering.

    Computed per original recursor name (not per equivalence class),
    because the choice of which collapsed motive to keep depends on which
    member of the equivalence class the recursor "belongs to".
    Mirrors Rust `CallSitePlan` (surgery.rs:56). -/
structure CallSitePlan where
  /-- Number of parameters (unchanged between source and canonical). -/
  nParams : Nat
  /-- Source-order motive count (from original `rec.all.size`). -/
  nSourceMotives : Nat
  /-- Source-order minor count. -/
  nSourceMinors : Nat
  /-- Number of indices (between minors and major premise). -/
  nIndices : Nat
  /-- `keep[i]`: true if source motive `i` survives collapse.
      For `A.rec`, `keep[A_pos]` = true. For `B.rec`, `keep[B_pos]` = true. -/
  motiveKeep : Array Bool
  /-- `keep[i]`: true if source minor `i` survives collapse. -/
  minorKeep : Array Bool
  /-- `sourceToCanonMotive[i]` = canonical position of source motive `i`.
      Collapsed positions share the canonical index of their representative. -/
  sourceToCanonMotive : Array Nat
  /-- Same for minors. -/
  sourceToCanonMinor : Array Nat
  /-- `true` when the source motive belongs to this canonical SCC.

      Source recursor types use Lean's original `all` block, but canonical
      recursors are generated per minimal SCC. A source motive can
      therefore be present in the source telescope while absent from this
      canonical block. Call-site minor adaptation uses this bit to
      distinguish "canonical recursor supplies an IH binder" from "the IH
      must be synthesized by a recursive call into another canonical
      block". -/
  sourceInBlock : Array Bool
  /-- `true` when source minor `i` belongs to a source motive of this
      canonical SCC (`sourceInBlock` of its parent motive). A dropped minor
      with this bit set is a collapse drop: its canonical slot is held by a
      kept sibling, and the call site must show the two equal
      (`collapsePartner`). A dropped minor without it belongs to another SCC
      (split) or to the evaporated head-rewrite telescope. Mirrors Rust
      `CallSitePlan::minor_in_block`. -/
  minorInBlock : Array Bool
  /-- `some` when the callee is an EVAPORATED aux recursor — a
      `<all0>.rec_N` whose nested occurrence lost every spec-param
      inductive to another SCC. Its claim is aliased to the external
      inductive's own recursor (see the evaporated-aux alias pass in
      `aux_gen.rs`), so the call spine must be rebuilt onto that
      telescope:

        source: params… motives… minors… indices… major   (over-merged)
        target: specs…  motive   minors′… indices… major  (external rec)

      The spec args and extended level list are derived at the apply site
      from the source recursor's type instantiated with the call-site args
      (`deriveHeadRewriteApp`). -/
  headRewrite : Option AuxHeadRewrite
  deriving Repr, Nonempty, Inhabited, BEq

namespace CallSitePlan

/-- Number of canonical (kept) motives.
    Mirrors Rust `CallSitePlan::n_canonical_motives` (surgery.rs:110). -/
def nCanonicalMotives (plan : CallSitePlan) : Nat :=
  plan.motiveKeep.foldl (fun acc k => if k then acc + 1 else acc) 0

/-- Number of canonical (kept) minors.
    Mirrors Rust `CallSitePlan::n_canonical_minors` (surgery.rs:115). -/
def nCanonicalMinors (plan : CallSitePlan) : Nat :=
  plan.minorKeep.foldl (fun acc k => if k then acc + 1 else acc) 0

/-- Total canonical args in the telescope (params + kept motives + kept
    minors + indices + 1 major).
    Mirrors Rust `CallSitePlan::n_canonical_args` (surgery.rs:120). -/
def nCanonicalArgs (plan : CallSitePlan) : Nat :=
  plan.nParams
    + plan.nCanonicalMotives
    + plan.nCanonicalMinors
    + plan.nIndices
    + 1 -- major premise

/-- Smallest source-order prefix whose residual telescope is unchanged by
    recursor surgery. Once motives+minors are all applied, the remaining
    indices+major suffix is identity-mapped. Mirrors Rust
    `CallSitePlan::minimal_full_prefix`. -/
def minimalFullPrefix (plan : CallSitePlan) : Nat :=
  plan.nParams + plan.nSourceMotives + plan.nSourceMinors

/-- Whether this plan is an identity (no reordering, no collapse).
    Mirrors Rust `CallSitePlan::is_identity` (surgery.rs:129). -/
def isIdentity (plan : CallSitePlan) : Bool :=
  plan.headRewrite.isNone
    && plan.motiveKeep.all (fun k => k)
    && plan.minorKeep.all (fun k => k)
    && plan.sourceToCanonMotive.zipIdx.all (fun (c, i) => c == i)
    && plan.sourceToCanonMinor.zipIdx.all (fun (c, i) => c == i)

end CallSitePlan

/-- Call-site surgery plan for `.brecOn` / `.brecOn_N`.

    `.rec` telescope layout is:
    `params, motives, minors, indices, major`.

    `.brecOn` telescope layout is:
    `params, motives, indices, major, handlers`, with one handler per
    motive. The motive permutation/drop decision is the same as the
    corresponding recursor plan, and the handlers mirror that motive
    layout. Mirrors Rust `BRecOnCallSitePlan` (surgery.rs:148). -/
structure BRecOnCallSitePlan where
  nParams : Nat
  nSourceMotives : Nat
  nIndices : Nat
  motiveKeep : Array Bool
  sourceToCanonMotive : Array Nat
  /-- The recursor plan's `sourceInBlock`: a dropped motive (and handler)
      with this bit set is a collapse drop, checked at the call site. -/
  sourceInBlock : Array Bool
  deriving Repr, Nonempty, Inhabited, BEq

namespace BRecOnCallSitePlan

/-- Mirrors Rust `BRecOnCallSitePlan::from_rec_plan` (surgery.rs:157). -/
def fromRecPlan (plan : CallSitePlan) : BRecOnCallSitePlan :=
  { nParams := plan.nParams
    nSourceMotives := plan.nSourceMotives
    nIndices := plan.nIndices
    motiveKeep := plan.motiveKeep
    sourceToCanonMotive := plan.sourceToCanonMotive
    sourceInBlock := plan.sourceInBlock }

/-- Mirrors Rust `BRecOnCallSitePlan::n_canonical_motives` (surgery.rs:167). -/
def nCanonicalMotives (plan : BRecOnCallSitePlan) : Nat :=
  plan.motiveKeep.foldl (fun acc k => if k then acc + 1 else acc) 0

/-- Smallest safe prefix for a `.below`-family plan: params+motives.
    Mirrors Rust `BRecOnCallSitePlan::below_minimal_full_prefix`. -/
def belowMinimalFullPrefix (plan : BRecOnCallSitePlan) : Nat :=
  plan.nParams + plan.nSourceMotives

/-- Smallest safe prefix for `.brecOn`: its trailing handlers are a second
    permuted motive band, so the complete public telescope is required.
    Mirrors Rust `BRecOnCallSitePlan::brecon_minimal_full_prefix`. -/
def brecOnMinimalFullPrefix (plan : BRecOnCallSitePlan) : Nat :=
  plan.nParams + plan.nSourceMotives + plan.nIndices + 1
    + plan.nSourceMotives

/-- Mirrors Rust `BRecOnCallSitePlan::is_identity` (surgery.rs:171). -/
def isIdentity (plan : BRecOnCallSitePlan) : Bool :=
  plan.motiveKeep.all (fun k => k)
    && plan.sourceToCanonMotive.zipIdx.all (fun (c, i) => c == i)

end BRecOnCallSitePlan

/-- Whether a `belowCallSitePlans` key is the `.below`/`.below_N` HEAD
    (telescope `params, motives, indices, major` — surgery requires the
    full floor) as opposed to a Prop-below FAMILY member (a `.below`
    constructor or `.below.casesOn`, whose telescope starts with the
    below params — parent params then parent motives — and has no
    major-premise floor: a field-less below ctor is fully applied at
    exactly params+motives). Mirrors Rust `below_plan_key_is_head`
    (surgery.rs). -/
def belowPlanKeyIsHead (name : Name) : Bool :=
  match name with
  | .str _ s _ => s == "below" || s.startsWith "below_"
  | _ => false

/-! ## Collapse drops (A0, WB-B4)

A plan drops the motives and minors (and `.brecOn` handlers) of collapsed
members: their canonical slot is held by one kept argument. The drop is
sound only when the dropped argument compiles to the same Ixon as the kept
argument at its slot; otherwise the rebuilt spine runs the kept member's
code at the dropped member's nodes (the `SurgCollapse` miscompile). The
comparison is on compiled forms, not Lean terms: the motives of collapsed
members are written over different Lean types (`A` vs `B`) and become equal
only after compilation, where collapsed members share one projection
address. Mirrors the Rust helpers of `surgery.rs` (`ArgSlot`,
`CollapseCheck`, `collapse_partner`, `collapse_checks`). -/

/-- The message of every refused collapse drop (both compilers). -/
def collapseDropError : String := "collapse call site drops distinct arguments"

/-- The message of a refused eta-wrapped partial application of a plan head
    that drops collapsed arguments (both compilers): the wrapper's dropped
    arguments are bound variables, distinct from the kept ones by
    construction. -/
def collapseEtaError : String := "collapse call site is a partial application"

/-- Whether the plan drops a motive of a collapsed member of this SCC (its
    minors follow the motive). Mirrors Rust `CallSitePlan::drops_collapsed`. -/
def CallSitePlan.dropsCollapsed (plan : CallSitePlan) : Bool :=
  (plan.motiveKeep.zip plan.sourceInBlock).any fun (k, b) => !k && b

/-- Mirrors Rust `BRecOnCallSitePlan::drops_collapsed`. -/
def BRecOnCallSitePlan.dropsCollapsed (plan : BRecOnCallSitePlan) : Bool :=
  (plan.motiveKeep.zip plan.sourceInBlock).any fun (k, b) => !k && b

/-- Where the compiled form of one source argument of a surgered call site
    lives: at a canonical position of the rebuilt spine, or in the call
    site's collapsed list (which also holds the source form of a kept,
    split-adapted minor). Mirrors Rust `ArgSlot`. -/
inductive ArgSlot where
  | canon (i : Nat)
  | collapsed (i : Nat)
  deriving Repr, Inhabited, BEq

/-- One obligation of a collapse drop: the compiled form of the dropped
    source argument `src` must equal that of the kept argument `keptSrc` at
    the same canonical slot. Mirrors Rust `CollapseCheck`. -/
structure CollapseCheck where
  what : String
  src : Nat
  keptSrc : Nat
  dropped : ArgSlot
  kept : ArgSlot
  deriving Repr, Inhabited

/-- The kept source argument whose canonical slot a dropped one shares:
    `.ok none` when `i` is kept or dropped without being a collapse drop
    (its motive belongs to another SCC), `.ok (some j)` for a collapse drop
    with kept partner `j`, `.error ()` for a collapse drop with no kept
    argument at its slot. Mirrors Rust `collapse_partner`. -/
def collapsePartner (keep : Array Bool) (sourceToCanon : Array Nat)
    (inBlock : Array Bool) (i : Nat) : Except Unit (Option Nat) :=
  if keep.getD i true || !(inBlock.getD i false) then
    .ok none
  else
    match sourceToCanon[i]? with
    | none => .error ()
    | some slot =>
      match (List.range keep.size).find? fun j =>
          keep[j]! && sourceToCanon[j]? == some slot with
      | some j => .ok (some j)
      | none => .error ()

/-- The collapse checks of one band of a call site (`what` names the band:
    motive, minor or handler); `slots[i]` is where source argument `i` of the
    band was compiled. A drop with no kept partner is an error (the message
    names `compiling` and `head`). Mirrors Rust `collapse_checks`. -/
def collapseChecks (what : String) (keep : Array Bool) (sourceToCanon : Array Nat)
    (inBlock : Array Bool) (slots : Array ArgSlot) (compiling head : String) :
    Except String (Array CollapseCheck) := do
  let mut out : Array CollapseCheck := #[]
  for i in [0:slots.size] do
    match collapsePartner keep sourceToCanon inBlock i with
    | .ok none => pure ()
    | .ok (some j) =>
      out := out.push { what, src := i, keptSrc := j, dropped := slots[i]!,
                        kept := slots[j]! }
    | .error () =>
      throw s!"{collapseDropError}: compiling '{compiling}', call-site head \
'{head}': dropped {what} #{i} has no kept argument at its canonical slot"
  return out

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
