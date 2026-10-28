module

public import IxC.Kernel.Env

@[expose] public section

/-!
# The typing tier: its data

IxC's logical tier (`Ix.Kernel.Cached.checkDecls`) checks safe declarations
and gives each a model. A `partial` or `unsafe` declaration has no model, and
the front ends decline it. The **typing tier** gives such declarations a
second verdict, `typed`: *the declaration is well-typed, with every tier
constant opaque, including itself and its own block*. It is a derivation in
the rules tier (`Rules.Infer`, `Rules.DefEq`) over the logical environment
extended by the tier's constants as `axiomInfo`
(`IxC/Kernel/Verify/Tier.lean`), and it says nothing about meaning.

* The tier never touches the logical environment. `checkDecls` runs on the
  safe declarations alone, exactly as without the tier; the tier runs
  afterwards, on the logical environment, and returns its constants
  separately (`TierConst`, newest first). So `model_exists` and every
  theorem about the logical tier apply to the logical result unchanged.
* **The fence is structural**: a tier constant is never in the logical
  environment, and every term the logical fold accepts resolves in it, so a
  safe declaration that names a tier constant is refused there.
* A tier constant is installed as `axiomInfo`: no δ, no ι. Lean's kernel
  unfolds partial and unsafe definitions in conversion (`is_delta`,
  `type_checker.cpp:555-563`); the tier refuses that relaxation, so a
  declaration that types only by such an unfolding declines.

This module is the data; the fold is `Ix.Kernel.Tier.checkTierC`
(`IxC/Kernel/Tier/Check.lean`). Both stages are built: blocks of `partial`
definitions (Lean's `_unsafe_rec` companions, always a `mutualDefnDecl`
with `safety := .partial`), and, staged after them as Lean's lattice
requires, unsafe opaques (checked in Lean's safe mode), unsafe definition
blocks and unsafe axioms. Unsafe inductives stay declined: the front ends
never route them here (`Ix.Kernel.Tier.indC`, `Tier/Ind.lean`, checks them typing
only, with no verdict, for resource typing's uncertified part).
See `docs/kernel.md`, "The typing tier".
-/

namespace Ix.Kernel.Tier

open Ix.Kernel

/-- A tier declaration's safety (Lean's `DefinitionSafety` minus `safe`). -/
inductive Safety where
  | part
  | unsaf
  deriving DecidableEq, Repr, Inhabited

/-- The safety's word, as a verdict reports it (`typed partial`). -/
def Safety.word : Safety → String
  | .part => "partial"
  | .unsaf => "unsafe"

/-- **An admitted tier constant**: its checked header (the annotated type)
and its safety. It is installed as `axiomInfo`: never unfolded. -/
structure TierConst (md : Mode) where
  cv : ConstantVal md
  safety : Safety
  deriving Inhabited

/-- **What a front end hands the tier.** -/
inductive TierDecl (md : Mode) where
  /-- A definition block: its safety and its members, each with its value. A
  singleton is a block of one: Lean's partial definitions are always a
  `mutualDefnDecl`, and Lean adds a block's members, or an unsafe singleton,
  before it checks their bodies (`add_mutual`, `environment.cpp:254-267`;
  `add_definition`, `:163-178`). -/
  | defs (safety : Safety) (members : List (ConstantVal md × Expr md))
  /-- An unsafe opaque, with its value: Lean checks it in safe mode
  (`add_opaque`, `environment.cpp:211-223`), so it may name no tier
  constant. -/
  | unsafeOpaque (cv : ConstantVal md) (value : Expr md)
  /-- An unsafe axiom: its header only, checked in unsafe mode (`add_axiom`,
  `environment.cpp:152-158`). -/
  | unsafeAxiom (cv : ConstantVal md)
  deriving Inhabited

/-- The constants a tier declaration declares. -/
def TierDecl.names : TierDecl md → List (Key md)
  | .defs _ ms => ms.map (·.1.name)
  | .unsafeOpaque cv _ | .unsafeAxiom cv => [cv.name]

/-- The headers a tier declaration declares, in order. -/
def TierDecl.headers : TierDecl md → List (ConstantVal md)
  | .defs _ ms => ms.map (·.1)
  | .unsafeOpaque cv _ | .unsafeAxiom cv => [cv]

/-- A tier declaration's safety: a block's own, `unsafe` for an opaque or an
axiom. -/
def TierDecl.safety : TierDecl md → Safety
  | .defs s _ => s
  | .unsafeOpaque .. | .unsafeAxiom _ => .unsaf

/-- The tier constants as the environment stores them: `axiomInfo` of each
header, newest first. -/
def TierConst.infos (ts : List (TierConst md)) : List (ConstantInfo md) :=
  ts.map fun c => .axiomInfo c.cv

/-- **The opaque extension**: the logical environment with the tier
constants `ts` (newest first) in front, as `axiomInfo`. A tier verdict is
stated in it. -/
def _root_.Ix.Kernel.Env.extendOpaque (env : Env md) (ts : List (TierConst md)) : Env md :=
  ⟨TierConst.infos ts ++ env.consts⟩

end Ix.Kernel.Tier
