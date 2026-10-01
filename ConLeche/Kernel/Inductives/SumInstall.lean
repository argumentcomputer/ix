module

public import ConLeche.Kernel.Inductives.StructInstall
public import ConLeche.Kernel.Inductives.SumParts

@[expose] public section

/-!
# The shared install stages (pure fueled checker)

The former, constructor and rule-shape stages the fixpoint route runs
(`checkNative`, `ConLeche/Kernel/Inductives/NativeInstall.lean`): the
type former read at the placeholder sort, one constructor stage per
constructor, the constructors consed, the rules' shape.  Written for
the sum route (task #175), which was deleted at task #210 Part C; the
stages are the one route's now.  No projection
table, no eta, no unit-likeness — a sum has no structure-like
capability (the official kernel's `is_structure_like` needs one
constructor and no index); the former is stored with the capability
record `sumCaps` (only `ruleK`, official's `is_K_target`: a
`Prop` family with one constructor taking only the parameters — `Eq`'s
shape) and the recursor's rules are the block's only definitional
content.

The per-constructor stage is `checkStructCtor` with the constructor
made explicit (the direct structure route's stage reads it off its
`StructParts`) and the residual widened to the family at the
parameters followed by `nIdx` index expressions; the field-sort walk
(`checkStructFieldSortsI`) carries official's subsingleton-elimination
criterion for a large eliminator at a `Prop` family with one
constructor (a field that is not a proposition must be one of the
index expressions); the domain pins are shared (`checkStructDomsAt`).
Every constructor's type is checked at the environment holding the
type former alone and the constructors are consed afterwards: they
never mention each other, and this order keeps the install soundness
one-pass (each constructor's reading is taken at the one environment,
and crossed).  The index-threaded twins are
`ConLeche/Kernel/Inductives/SumInstallF.lean`.
-/

namespace ConLeche

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]

/-- **Official's telescope loop** (`check_inductive_types`,
`inductive.cpp`; task #195): peel `n` Π binders off `e`, reducing the
residual to weak head normal form before each binder and at the end,
where it must be a sort.  Binder `i` is opened at the free variable
`i` (its domain instantiated at the earlier ones, as `openPisAtFvars`
does), so the returned binder domains and the sort are scoped at the
free variables `0 ..< n`.  A residual that does not reduce to a Π, or
finally to a sort, is INVALID input — official fails there too. -/
def whnfTelescope (ops : CheckerOps m) (env : Env) :
    Nat → Nat → Expr → m (List (Expr × BinderMeta) × Level)
  | i, 0, e => do
    let e' ← ops.whnf env i e
    match e' with
    | .sort s => pure ([], s)
    | _ => throw (.invalid "direct sum: type former does not reduce to a sort \
        after its parameters and indices")
  | i, n + 1, e => do
    let e' ← ops.whnf env i e
    match e' with
    | .forallE dom body bm =>
      let (bs, s) ← whnfTelescope ops env (i + 1) n (body.instantiate1 (.fvar i dom))
      pure ((dom, bm) :: bs, s)
    | _ => throw (.invalid "direct sum: type former does not reduce to a telescope \
        of its parameters and indices")

/-- Close a telescope opened at the free variables `i ..< i + bs.length`
back into a syntactic Π-telescope over `body`: innermost binder first,
each abstraction turning the binder's own free variable into the bound
one (`abstract1`; the domains of the inner binders are closed by the
outer abstractions, which descend into binder domains). -/
def closeTelescope : List (Expr × BinderMeta) → Nat → Expr → Expr
  | [], _, body => body
  | (dom, bm) :: bs, i, body =>
    .forallE dom ((closeTelescope bs (i + 1) body).abstract1 i 0) bm

/-- The type former's TELESCOPE (task #195): the checked declared type
when it is already a syntactic telescope of `n` Π binders ending in a
sort, else the declared type's whnf'd telescope (`whnfTelescope`),
closed and checked as the former's type in its place —
`checkConstantVal` from scratch, so nothing about the reduction is
trusted: the stored type is the one this run annotated, inferred and
sorted.  Returns the checked constant and the result sort. -/
def checkSumTele (ops : CheckerOps m) (env : Env) (cv : ConstantVal) (n : Nat)
    (cvTa₀ : ConstantVal) : m (ConstantVal × Level) :=
  match cvTa₀.type.stripPis n with
  | some (_, .sort s) => pure (cvTa₀, s)
  | _ => do
    let (bs, s) ← whnfTelescope ops env 0 n cvTa₀.type
    let cvTa ← checkConstantVal ops env { cv with type := closeTelescope bs 0 (.sort s) }
    pure (cvTa, s)

/-- Stage 1: the type former, stored with the block's capability
record — `capsOf` at the completed record: `sumCaps` on the sum
route, `nativeCaps` on the fixpoint route (task #210 Part A) — at
its telescope (`checkSumTele`); returns the record completed
with the result sort (`InductiveShape.withSort`), which every later
stage runs on. -/
def checkSumInd (ops : CheckerOps m) (env : Env) (p : InductiveShape)
    (capsOf : InductiveShape → IndCaps) :
    m (Env × ConstantVal × InductiveShape) := do
  let cvTa₀ ← checkConstantVal ops env p.cvT
  let (cvTa, s) ← checkSumTele ops env p.cvT (p.nP + p.nIdx) cvTa₀
  let (_, tbody) ← unwrapOr (cvTa.type.stripPis (p.nP + p.nIdx))
    (.internal "direct sum: type former telescope")
  unless tbody == Expr.sort s do
    throw (.internal "direct sum: type former result sort")
  let p' := p.withSort s
  pure (⟨.indInfo cvTa (capsOf p') :: env.consts⟩, cvTa, p')

/-- The fields' sorts over the opened constructor telescope, with the
official per-field universe bound unless the family is
propositional (`checkStructFieldSorts` at an indexed family): at a
`Prop` family with a large eliminator every field must be a
proposition OR one of the residual's index expressions — official's
`elim_only_at_universe_zero` for one constructor (the subsingleton-
elimination criterion, `Eq`'s rule; `inductive.cpp`).  A block with
two or more constructors never reaches this walk with a large
eliminator (`checkSum`'s front guard).  Walks the fields from
the last to the first and returns the sorts in field order. -/
def checkStructFieldSortsI (ops : CheckerOps m) (env : Env) (isProp large : Bool)
    (s : Level) (nP : Nat) (fvs idxArgs : List Expr) : Nat → m (List Level)
  | 0 => pure []
  | j + 1 => do
    let fv ← unwrapOr fvs[j]? (.internal "direct sum: field index")
    let ty ← ops.inferType env (nP + j) fv.fvarTypeD
    let u ← ops.ensureSort env (nP + j) ty
    if !isProp then
      unless ← liftFueled "level comparison" (Level.leq u s) do
        throw (.invalid "direct sum: field universe too large")
    else if large then
      unless Level.isEquiv u .zero == some true || idxArgs.contains fv do
        throw (.invalid "direct sum: large eliminator with a non-propositional \
          field outside the indices")
    let rest ← checkStructFieldSortsI ops env isProp large s nP fvs idxArgs j
    pure (rest ++ [u])

/-- **Official's positivity walk, as a normalisation** (task #210 Part
D, audit #206-A5): `check_positivity` (`inductive.cpp`) reduces a
constructor field's type to weak head normal form before classifying
it, and again under every Π binder of a reflexive field.  A field whose
type only whnf's to an occurrence of the block (`Id' T`, `Nat → Id' T`)
is recursive for official and invisible to a syntactic reading.  So the
field's domain is REPLACED by the form official classifies: whnf'd at
its own depth, and — while the block occurs — walked under its Π
binders (a Π domain mentioning the block is official's "non positive
occurrence", INVALID), each body whnf'd in turn.  A domain the block
does not occur in is kept as declared, unreduced (official whnf's it
too, and discards the result: reduction cannot introduce the block);
one it occurs in only before whnf (`idf (T → Type) (fun _ => N) t`,
which official classifies as an ordinary field) is REPLACED by the
whnf'd form, so that the field no longer mentions the block nor, with
it, any earlier recursive field (`structUsedLater`).  The result is
definitionally equal to the declared domain; the constructor is
re-checked from scratch on the rebuilt type (`normCtorVal`), so
nothing about the reduction is trusted — task #195's arrangement at
the type former, now at the fields.  `fuel` bounds the Π walk (a
reflexive field's own telescope); exhaustion is a positive decline. -/
def normPosDom (ops : CheckerOps m) (env : Env) (T : Name) : Nat → Nat → Expr → m Expr
  | _, 0, _ => throw (.notImplemented "direct sum: positivity walk fuel")
  | d, fuel + 1, e => do
    if !e.mentionsConst T then pure e else
    let w ← ops.whnf env d e
    if !w.mentionsConst T then pure w else
    match w with
    | .forallE dom body bm =>
      if dom.mentionsConst T then
        throw (.invalid "direct sum: non positive occurrence of the inductive type")
      else do
        let body' ← normPosDom ops env T (d + 1) fuel (body.instantiate1 (.fvar d dom))
        pure (.forallE dom (body'.abstract1 d) bm)
    | _ => pure w

/-- The constructor's field binders with their domains normalised
(`normPosDom`), opened at the free variables `i ..< i + n` as
`whnfTelescope` opens the former's; the residual returned scoped at
those variables. -/
def normFieldDoms (ops : CheckerOps m) (env : Env) (T : Name) :
    Nat → Nat → Expr → m (List (Expr × BinderMeta) × Expr)
  | _, 0, e => pure ([], e)
  | i, n + 1, .forallE dom body bm => do
    let dom' ← normPosDom ops env T i 1024 dom
    let (bs, r) ← normFieldDoms ops env T (i + 1) n (body.instantiate1 (.fvar i dom))
    pure ((dom', bm) :: bs, r)
  | _, _ + 1, _ => throw (.notImplemented "direct sum: constructor field telescope")

/-- The checked constructor with its field domains normalised: the
parameter binders as declared, the field binders through
`normFieldDoms`, closed back into a telescope (`closeTelescope`) and
— when anything changed — checked as the constructor's type in its
place, from scratch. -/
def normCtorVal (ops : CheckerOps m) (env : Env) (T : Name) (nP nF : Nat)
    (cvC cvCa : ConstantVal) : m ConstantVal := do
  let (cbs, _) ← unwrapOr (cvCa.type.stripPis nP)
    (.notImplemented "direct sum: constructor telescope")
  let (fvsP, crest) ← unwrapOr (openPisAtFvars nP cvCa.type 0)
    (.notImplemented "direct sum: constructor telescope")
  let pbs := List.zipWith (fun (x : Expr) (b : Expr × BinderMeta) => (x.fvarTypeD, b.2)) fvsP cbs
  let (fbs, resid) ← normFieldDoms ops env T nP nF crest
  let ty' := closeTelescope (pbs ++ fbs) 0 resid
  if ty' == cvCa.type then pure cvCa
  else checkConstantVal ops env { cvC with type := ty' }

/-- Stage 2, one constructor's type: the ordinary constant check, the
annotated result shape (the family at the parameters followed by
`nIdx` index expressions), the parameter pins against the type
former's opened telescope, the pre-block resolution of the field
domains, and the per-field universe bound (`checkStructCtor`, the
constructor made explicit; `env₀` is the pre-block environment, `env`
the one holding the type former).  Every constructor is checked at
the environment holding the type former alone — the constructors do
not mention each other — and the block conses them afterwards
(`checkSum`).  Returns the annotated constructor and its fields'
sorts (task #210 Part A: the projection table's guard levels at a
structure-like block on the fixpoint route are computed from them). -/
def checkSumCtor (ops : CheckerOps m) (env₀ env : Env) (T : Name)
    (lps : List Name) (nP nIdx : Nat) (resSort : Level) (isProp large : Bool)
    (cvC : ConstantVal) (nF : Nat) (cvTa : ConstantVal) : m (ConstantVal × List Level) := do
  let cvCa₀ ← checkConstantVal ops env cvC
  let cvCa ← normCtorVal ops env T nP nF cvC cvCa₀
  let (_, cbody) ← unwrapOr (cvCa.type.stripPis (nP + nF))
    (.notImplemented "direct sum: constructor telescope")
  -- official's `is_valid_ind_app` on the constructor's result
  -- ("invalid return type for 'C'", `check_constructors`): a REJECT,
  -- not a decline (task #220) — the head must be the block at its own
  -- level parameters, applied to exactly the parameters and `nIdx`
  -- further arguments
  unless structCtorResidOk T lps nP nF nIdx cbody do
    throw (.invalid "direct sum: invalid constructor return type")
  let cq ← unwrapOr (openPisAtFvars nP cvCa.type 0)
    (.notImplemented "direct sum: constructor telescope")
  let tq ← unwrapOr (openPisAtFvars nP cvTa.type 0)
    (.notImplemented "direct sum: type former telescope")
  checkStructDomsAt ops env 0 cq.1 (tq.1.map Expr.fvarTypeD) nP
  let xq ← unwrapOr (openPisAtFvars nF cq.2 nP)
    (.notImplemented "direct sum: constructor field telescope")
  -- the opened residual is the family at the opened parameter
  -- variables followed by the index expressions
  unless xq.2.getAppFn == Expr.const T (lps.map .param) &&
      xq.2.getAppArgs.take nP == cq.1 && xq.2.getAppArgs.length == nP + nIdx do
    throw (.notImplemented "direct sum: opened constructor residual")
  unless xq.1.all fun x => x.fvarTypeD.constsResolve env₀ do
    throw (.notImplemented "direct sum: field domain after the block")
  -- the index expressions never mention the block (official
  -- `is_valid_ind_app`: no inductive occurrence in an index argument)
  unless (xq.2.getAppArgs.drop nP).all fun e => e.constsResolve env₀ do
    throw (.invalid "direct sum: index expression mentions the block")
  let sorts ← checkStructFieldSortsI ops env isProp large resSort nP xq.1
    (xq.2.getAppArgs.drop nP) nF
  pure (cvCa, sorts)

/-- Stage 2, all constructors' types, at the environment holding the
type former; returns the annotated constructors with their field
counts, and beside them the constructors' field sorts. -/
def checkSumCtors (ops : CheckerOps m) (env₀ env : Env) (T : Name)
    (lps : List Name) (nP nIdx : Nat) (resSort : Level) (isProp large : Bool)
    (cvTa : ConstantVal) :
    List (ConstantVal × Nat) → m (List (ConstantVal × Nat) × List (List Level))
  | [] => pure ([], [])
  | c :: cs => do
    let (cvCa, sorts) ← checkSumCtor ops env₀ env T lps nP nIdx resSort isProp large c.1 c.2
      cvTa
    let (rest, srest) ← checkSumCtors ops env₀ env T lps nP nIdx resSort isProp large cvTa cs
    pure ((cvCa, c.2) :: rest, sorts :: srest)

/-- The constructors' conses, in order (the first constructor deepest). -/
def consSumCtors (nP : Nat) : List (ConstantVal × Nat) → Env → Env
  | [], env => env
  | c :: cs, env => consSumCtors nP cs ⟨.ctorInfo c.1 nP c.2 :: env.consts⟩

/-- The stored rules: constructor `j`'s with the generated right-hand
side `j`, plain when the generated type's major is the family at the
parameters (always, by construction), carrying the two rescue bits
`recRuleBits` reads off the block's own store — the family and its
constructors are installed before the recursor — and `paramsBlind`,
because the route's rule law holds at any pair of fitting parameter
spines. -/
def sumRules (find? : Name → Option ConstantInfo) (recName : Name)
    (nP mI rP : Nat) (recTy : Expr) :
    List (ConstantVal × Nat) → List Expr → List RecRule
  | c :: cs, rhs :: rhss =>
    recRuleBits find? recName
      { ctor := c.1.name, nfields := c.2, ctorParams := nP,
        fire := if Expr.recRulePlain recTy mI rP nP then .plain else .inert,
        rhs := rhs, paramsBlind := true }
      :: sumRules find? recName nP mI rP recTy cs rhss
  | _, _ => []

/-- The recursor's rule prefix (parameters, motive, minors) and its
major index (the rule prefix, then the indices). -/
def InductiveShape.rulePrefix (p : InductiveShape) : Nat := p.nP + 1 + p.ctors.length
def InductiveShape.majorIdx (p : InductiveShape) : Nat := p.rulePrefix + p.nIdx

@[simp] theorem InductiveShape.withSort_rulePrefix (p : InductiveShape) (s : Level) :
    (p.withSort s).rulePrefix = p.rulePrefix := rfl
@[simp] theorem InductiveShape.withSort_majorIdx (p : InductiveShape) (s : Level) :
    (p.withSort s).majorIdx = p.majorIdx := rfl

end ConLeche
