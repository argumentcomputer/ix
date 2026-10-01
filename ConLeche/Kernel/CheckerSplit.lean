module

public import ConLeche.Kernel.Checker

@[expose] public section

/-!
# The declaration checker, split at the install/check seam (task #253)

`checkDecl` (`ConLeche/Kernel/Checker.lean`) installs a declaration and
checks it in one run.  For a `defn`, `thm` or `opaque` the two halves
are separable: the **install half** runs the syntactic guards and the
annotation of the type — and, for a definition or an opaque, of the
value — and pushes the constant; the **check half** runs the
inferences and the conversion — the type's sort, the theorem's
is-a-proposition test, for a theorem the value's guards and annotation
(a theorem is installed by its statement; its value reaches the check
half raw), the value's type against the declared one — and reads only
the environment the constant was installed at and the data the
install half produced.  Every
other kind (axioms, inductive and basis blocks, and the pinned
`Nat`-operation and `reduce*` branches, whose certificates are checked
as they are installed) is not separable and its install half IS
`checkDecl`.

`installConstantVal`, `installValue` and `checkValueGroup` are the two
halves as pure functions over `CheckerOps`, the specification the
fold's cached twins (`annotValueC`, `checkPending`,
`ConLeche/Cached/Installed.lean`) simulate; `checkDecl_of_split_*`
(`ConLeche/Verify/CheckerSplit.lean`) say the two halves are `checkDecl`.
`ValueGroup` is the datum that crosses the seam.
-/

namespace ConLeche

/-- The three declaration kinds whose value check is separable from
their install. -/
inductive ValueKind where
  | defn
  | thm
  | opaque
  deriving DecidableEq, Repr

/-- The kind's word in `checkDecl`'s type-mismatch message. -/
def ValueKind.word : ValueKind → String
  | .defn => "definition"
  | .thm => "theorem"
  | .opaque => "opaque"

/-- What the install half hands the check half: the kind, the header
with its type annotated, and the value — ANNOTATED for a definition or
an opaque (the install half annotated it and stored it), RAW for a
theorem (the install half never looked at it: a theorem is stored by
its statement, and the check half annotates the value itself,
`checkValueGroup`). -/
structure ValueGroup where
  kind : ValueKind
  cvA : ConstantVal
  jv : Expr

variable (mode : CheckMode)
variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- `checkConstantVal` minus its inference: the syntactic guards and
the annotation of the type. -/
def installConstantVal (ops : CheckerOps m) (env : Env) (cv : ConstantVal) :
    m ConstantVal := do
  if (env.find? cv.name).isSome then
    throw (.invalid s!"duplicate declaration {cv.name}")
  if reservedBasisNames.contains cv.name then
    throw (.invalid s!"reserved basis name {cv.name}")
  if cv.name.isProjFnShape then
    throw (.invalid s!"reserved projection name {cv.name}")
  unless Name.nodup cv.levelParams do
    throw (.invalid s!"duplicate universe parameters in {cv.name}")
  unless cv.type.looseBVarsBounded 0 do
    throw (.invalid s!"loose bound variable in type of {cv.name}")
  if cv.type.hasFvar then
    throw (.invalid s!"unexpected free variable in type of {cv.name}")
  let type ← ops.annotate env 0 cv.type
  unless type.allLevelParamsDefined cv.levelParams do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  unless type.constsResolve env do
    throw (unresolvedConstsError s!"type of {cv.name}" type)
  pure { cv with type := type }

/-- The value half of `check{Defn,Thm,Opaque}Val` minus its inference:
the guards and the annotation of the value. -/
def installValue (ops : CheckerOps m) (env : Env) (cv : ConstantVal)
    (value : Expr) : m Expr := do
  unless value.looseBVarsBounded 0 do
    throw (.invalid s!"loose bound variable in value of {cv.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cv.name}")
  let value ← ops.annotate env 0 value
  unless value.allLevelParamsDefined cv.levelParams do
    throw (.invalid s!"undeclared universe parameter in value of {cv.name}")
  unless value.constsResolve env do
    throw (unresolvedConstsError s!"value of {cv.name}" value)
  pure value

/-- **The check half of a value declaration**, at the environment the
constant was installed at: the type's sort, the theorem's
is-a-proposition test, for a theorem the value's guards and annotation
(`installValue`: a theorem's value reaches the check half raw), and
the value's type against the declared one — the inference and
conversion calls of `checkConstantVal` and `check{Defn,Thm,Opaque}Val`,
in their order, with their messages. -/
def checkValueGroup (ops : CheckerOps m) (env : Env) (g : ValueGroup) : m Unit := do
  let stype ← ops.inferType env 0 g.cvA.type
  let u ← ops.ensureSort env 0 stype
  let jv ← if g.kind = .thm then do
      unless (← liftFueled "level comparison" (Level.isEquiv u .zero)) do
        throw (.invalid s!"type of theorem {g.cvA.name} is not a proposition")
      installValue ops env g.cvA g.jv
    else pure g.jv
  let vtype ← ops.inferType env 0 jv
  unless ← ops.isDefEq env 0 vtype g.cvA.type do
    throw (.invalid s!"type mismatch in {g.kind.word} {g.cvA.name}")

end ConLeche
