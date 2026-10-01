module

public import ConLeche.Kernel.DeclCheck

@[expose] public section

/-!
# The projection table's checks, through the index

`ConLeche/Kernel/Inductives/StructInstall.lean`'s survivors over an `FEnv` (the
mirrors the cached drivers run) and the `StructWalkers` record the
fixpoint installer takes its constant walks from (task #214 P3).  The
simple-structure installer these once mirrored was deleted at task
#210 Part C.
-/

namespace ConLeche

variable (mode : CheckMode)

section Mirrors

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-! ### The direct simple-structure path, through the index -/

/-- `checkStructDomsAt` through the index. -/
def checkStructDomsAtF (ops : CheckerOps m) (fe : FEnv) (off : Nat)
    (fvs doms : List Expr) : Nat → m Unit
  | 0 => pure ()
  | j + 1 => do
    let a ← unwrapOr fvs[j]? (.internal "direct structure: domain index")
    let b ← unwrapOr doms[j]? (.internal "direct structure: domain index")
    unless ← ops.isDefEq fe.env (off + j) a.fvarTypeD b do
      throw (.notImplemented "direct structure: binder domain mismatch")
    checkStructDomsAtF ops fe off fvs doms j

/-- `checkStructDomsAtF` over arrays (see `checkStructFieldUnivFA`).
Equal to it at `List.toArray`: `checkStructDomsAtFA_eq`. -/
def checkStructDomsAtFA (ops : CheckerOps m) (fe : FEnv) (off : Nat)
    (fvs doms : Array Expr) : Nat → m Unit
  | 0 => pure ()
  | j + 1 => do
    let a ← unwrapOr fvs[j]? (.internal "direct structure: domain index")
    let b ← unwrapOr doms[j]? (.internal "direct structure: domain index")
    unless ← ops.isDefEq fe.env (off + j) a.fvarTypeD b do
      throw (.notImplemented "direct structure: binder domain mismatch")
    checkStructDomsAtFA ops fe off fvs doms j

/-- **The tree walkers an index-side installer takes from its
driver** (task #214, after the JZero audit): the constant-resolution
gate over constructor binder domains and the projection-body builder
over the constructor telescope are the two whole-tree traversals of
the direct install, and on a heavily DAG-shared block (Mathlib's
`ModularCurve.JZeroGoodReductionSpecialization_alt`: a 3.3 k-node DAG
unfolding to 19.6 M nodes) they are what the tree-size budget exists
for.  The cached driver supplies its memoised twins
(`ConLeche.Cached.structWalkersC`: `constsResolveFC`,
`structProjBodiesC`); the specification is `StructWalkers.plain`, to
which the driver's record is equal (`structWalkersC_eq_plain`,
`ConLeche/Verify/Cached/WalkersC.lean`).  The pure installers never see
this record. -/
structure StructWalkers where
  /-- `Expr.constsResolveF` or its memoised twin -/
  resolve : FEnv → Expr → Bool
  /-- `structProjBodies` or its memoised twin -/
  projBodies : Name → Nat → Nat → Expr → Option (Array Expr)

/-- The plain walkers: the specification. -/
def StructWalkers.plain : StructWalkers :=
  ⟨fun fe e => e.constsResolveF fe, structProjBodies⟩

/-- `checkStructProjTable` through the index (task #175 S1). -/
def checkStructProjTableF (w : StructWalkers) (T C : Name) (lps : List Name) (nP nF : Nat)
    (resSort : Level) (guards : List Level) (off : Nat) (cvCa : ConstantVal) (fe : FEnv) :
    m FEnv := do
  let bodies ← unwrapOr (w.projBodies T nP nF cvCa.type)
    (.internal "direct structure: projection bodies")
  -- the bodies' scoping, validated once at insertion (the stage's own
  -- guard, what `EnvWF`'s table clause records): fvar-free, level
  -- parameters within the structure's, resolving, scoped at the
  -- parameters and the subject; one per field
  unless bodies.size = nF ∧ bodies.all (fun b => !b.hasFvar &&
      b.allLevelParamsDefined lps && w.resolve fe b &&
      b.looseBVarsBounded (nP + 1)) do
    throw (.internal "direct structure: projection body scoping")
  -- the projection-function name family (the modeled route's, the key
  -- of its η-family predicate) must be free too: a direct family has
  -- no projection functions, and the model's η law for the block is
  -- discharged by the tower, never by `EtaFamilyStored`
  unless (List.range nF).all (fun j => (fe.find? (projFnName T j)).isNone) do
    throw (.invalid "projection name family taken")
  unless (fe.find? (projTableName T)).isNone do
    throw (.invalid "projection table taken")
  pure (fe.push (.projInfo ⟨T, lps, nP, C, nF, resSort, bodies, guards, off⟩))

end Mirrors
