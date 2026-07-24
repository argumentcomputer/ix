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
  deriving Repr, Nonempty, Inhabited

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
  deriving Repr, Nonempty, Inhabited

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
  deriving Repr, Nonempty, Inhabited

namespace BRecOnCallSitePlan

/-- Mirrors Rust `BRecOnCallSitePlan::from_rec_plan` (surgery.rs:157). -/
def fromRecPlan (plan : CallSitePlan) : BRecOnCallSitePlan :=
  { nParams := plan.nParams
    nSourceMotives := plan.nSourceMotives
    nIndices := plan.nIndices
    motiveKeep := plan.motiveKeep
    sourceToCanonMotive := plan.sourceToCanonMotive }

/-- Mirrors Rust `BRecOnCallSitePlan::n_canonical_motives` (surgery.rs:167). -/
def nCanonicalMotives (plan : BRecOnCallSitePlan) : Nat :=
  plan.motiveKeep.foldl (fun acc k => if k then acc + 1 else acc) 0

/-- Mirrors Rust `BRecOnCallSitePlan::is_identity` (surgery.rs:171). -/
def isIdentity (plan : BRecOnCallSitePlan) : Bool :=
  plan.motiveKeep.all (fun k => k)
    && plan.sourceToCanonMotive.zipIdx.all (fun (c, i) => c == i)

end BRecOnCallSitePlan

end Ix.AuxGen
