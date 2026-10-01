module

public import ConLeche.Kernel.Inductives.Modeled
public import ConLeche.Kernel.TrustAxioms

@[expose] public section

/-!
# The projection table's checks (pure fueled checker)

What survives of the simple-structure installer (deleted at task #210
Part C): the field-domain walk and the projection TABLE the fixpoint
route stores at a structure-like block (`checkNativeTable`,
`ConLeche/Kernel/Inductives/NativeInstall.lean`).  The index-threaded twins
are `ConLeche/Kernel/Inductives/StructInstallF.lean`.
-/

namespace ConLeche

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]
variable (mode : CheckMode)

/-! ## The structure-shaped block's reference checks

A block recognised by `structParts?` (`ConLeche/Kernel/Direct.lean`)
consumes no `_model` artifact.  What this layer contributes are the
reference checks that need inference and definitional equality — the
per-field universe bound and the definitional pins of the recursor's
binder domains against the constructor's.
-/

/-- The reference kernels' binder-domain comparisons, run binder by
binder **at its own frame**: the `j`-th opened variable's annotation
against the `j`-th expected domain, at frame `off + j`.

Domain `j` is scoped at `off + j` — it mentions the binders before it
and nothing else — so that frame is exactly the context the references
compare it in, with those binders in scope and no more.  Because each
telescope is opened at its **own** variables, neither side's
annotations are borrowed from the other, which is what lets the model's
walks carry their own frame conditions at every stage.  Walks from the
last binder to the first, like `checkStructFieldUniv`. -/
def checkStructDomsAt (ops : CheckerOps m) (env : Env) (off : Nat)
    (fvs doms : List Expr) : Nat → m Unit
  | 0 => pure ()
  | j + 1 => do
    let a ← unwrapOr fvs[j]? (.internal "direct structure: domain index")
    let b ← unwrapOr doms[j]? (.internal "direct structure: domain index")
    unless ← ops.isDefEq env (off + j) a.fvarTypeD b do
      throw (.notImplemented "direct structure: binder domain mismatch")
    checkStructDomsAt ops env off fvs doms j

/-- Stage 5: **the projection table** (task #175 S1).  One constant
per structure: the fields' result-type bodies read off the
*annotated* constructor type by substitution alone
(`structProjBodies`), the per-field guard levels
(`structProjGuards`), the constructor and the counts.  Nothing is
annotated, inferred or pinned here — a `.proj T i e` use instantiates
`bodies[i]` at its own arguments (`ProjEntry.typeAt`) after the
official `infer_proj` guard test, and a slot with no legal
instantiation (a used-later data field of a `Prop` structure) simply
fails that guard at every use (`invalid`, as official).  The body
walk cannot fail on a constructor type `checkStructCtor` accepted
(it peels exactly `nP + nF` binders), so its failure is internal. -/
def checkStructProjTable (T C : Name) (lps : List Name) (nP nF : Nat)
    (resSort : Level) (guards : List Level) (off : Nat) (cvCa : ConstantVal) (env : Env) :
    m Env := do
  let bodies ← unwrapOr (structProjBodies T nP nF cvCa.type)
    (.internal "direct structure: projection bodies")
  -- the bodies' scoping, validated once at insertion (the stage's own
  -- guard, what `EnvWF`'s table clause records): fvar-free, level
  -- parameters within the structure's, resolving, scoped at the
  -- parameters and the subject; one per field
  unless bodies.size = nF ∧ bodies.all (fun b => !b.hasFvar &&
      b.allLevelParamsDefined lps && b.constsResolve env &&
      b.looseBVarsBounded (nP + 1)) do
    throw (.internal "direct structure: projection body scoping")
  -- the projection-function name family (the modeled route's, the key
  -- of its η-family predicate) must be free too: a direct family has
  -- no projection functions, and the model's η law for the block is
  -- discharged by the tower, never by `EtaFamilyStored`
  unless (List.range nF).all (fun j => (env.find? (projFnName T j)).isNone) do
    throw (.invalid "projection name family taken")
  unless (env.find? (projTableName T)).isNone do
    throw (.invalid "projection table taken")
  pure ⟨.projInfo ⟨T, lps, nP, C, nF, resSort, bodies, guards, off⟩ :: env.consts⟩

end ConLeche
