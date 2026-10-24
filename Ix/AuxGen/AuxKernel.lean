/- AuxGen's checked Source interface. Scopes are immutable values; all
queries and installs use the supplied checked capability. Configuration
errors precede query-refusal accounting and cannot authorize a retry. -/
module
public import Ix.AuxGen.Kernel
public import Ix.AuxGen.Oracle
public import Ix.AuxGen.FlatBlock
public import Ix.AuxGen.LevelEgress
public import Ix.AuxGen.FastPaths
public import Ix.AuxGen.Configuration
public import Ix.AuxGen.Nested
public section

namespace Ix.AuxGen

open Ix.CompileM (CompileM CompileError)

/-- The checked kernel and compile-side address view for one aux tail. -/
inductive AuxKernel where
  | ixc (maps : AddrMaps) (oracle : AuxOracle)

def AuxKernel.maps : AuxKernel → AddrMaps
  | .ixc maps _ => maps

/-- Reject unsupported flags before any callback or query-refusal region. -/
def AuxKernel.validate (k : AuxKernel) : KBridgeM Unit := do
  let .ixc _ o := k
  match Configuration.validateCapability o with
  | .ok () => pure ()
  | .error e => throw e.toCompileError

/-- The generator that opens a checked scope. -/
inductive AuxRoute where
  | below
  /-- `.brecOn`'s scopes (AuxGen M3) -/
  | brecOn
  /-- the recursor generator's scopes (AuxGen M4): lazy, and `whnf` with
      names (`OracleScope.whnfNamed`) -/
  | recursor
  deriving BEq, Inhabited

/-- A route's scopes, for a refusal's cause (AuxGen M5c). -/
def AuxRoute.label : AuxRoute → String
  | .below => ".below's scope"
  | .brecOn => ".brecOn's scope"
  | .recursor => "the recursor generator's scope"

/-- The checked scope capability. -/
inductive AuxScopeBackend where
  | ixc (scope : OracleScope)

/-- A local context as a value. It denotes `(levelParams, locals)`. -/
structure AuxScope where
  kernel : AuxKernel
  levelParams : Array Name
  /-- Outermost first: the outer context, then the pushed locals. -/
  locals : Array LocalDecl
  /-- The locals from `new`; `pop` cannot remove them. -/
  nOuter : Nat
  backend : AuxScopeBackend
  /-- the generator that opened it -/
  route : AuxRoute

/-! ## The IxC arm's bookkeeping -/

/-- Update the tail's IxC counts. -/
def bumpIxc (f : IxcStats → IxcStats) : KBridgeM Unit :=
  modify fun k => { k with ixcStats := f k.ixcStats }

/-- **An IxC refusal under `failClosed`** (AuxGen M5c), with a named cause:
the generator's scope (`scope`: its route and depth, or the install), the
question (`question`) and IxC's reason. The cause goes into the block's state
(`BlockReport.refusal`), which the throw keeps, so the driver can tell an IxC
refusal from any other failure and name the block
(`Ix.CompileM.runAuxTail`); then the refusal is thrown as before. -/
def refuseIxc (scope question reason : String) : KBridgeM α := do
  Ix.CompileM.modifyBlockState fun st =>
    { st with auxReport := { st.auxReport with refusal := some { scope, question, reason } } }
  throwBridge (.kernel (.ixc s!"{question} in {scope}") reason)

/-- A term's head, for a refusal's question. -/
def headOf (e : Expr) : String :=
  match (decomposeApps (stripMdataRef e)).1 with
  | .const n _ _ => n.pretty
  | .fvar n _ => s!"local {n.pretty}"
  | .sort .. => "a sort"
  | .forallE .. => "a ∀"
  | .lam .. => "a λ"
  | .letE .. => "a let"
  | .proj n i _ _ => s!"projection {n.pretty}.{i}"
  | .lit .. => "a literal"
  | _ => "a term"

/-- A telescope as the oracle takes it. -/
def oracleLocals (decls : Array LocalDecl) : Array (Name × Expr) :=
  decls.map fun d => (d.fvarName, d.domain)

namespace AuxScope

/-- The scope's depth: its number of locals. -/
def depth (s : AuxScope) : Nat := s.locals.size

/-- The scope, for a refusal's cause (AuxGen M5c). -/
def label (s : AuxScope) : String := s!"{s.route.label} at depth {s.depth}"

/-- Duplicate outer identities and universe parameters are refused. -/
private def checkScopeNames (ctx : Array LocalDecl) (lps : Array Name) : KBridgeM Unit := do
  let mut seenParams : Std.HashSet Name := {}
  for name in lps do
    if seenParams.contains name then throwBridge (.duplicateLevelParam name)
    seenParams := seenParams.insert name
  let mut seen : Std.HashSet Name := {}
  for decl in ctx do
    if seen.contains decl.fvarName then throwBridge (.duplicateOuterFVar decl.fvarName)
    seen := seen.insert decl.fvarName

/-- IxC's scope over `ctx`, or `none` (counted) when IxC refuses it. -/
private def ixcNew (o : AuxOracle) (ctx : Array LocalDecl) (lps : Array Name) :
    KBridgeM (Option OracleScope × Option String) := do
  match o.newScope lps (oracleLocals ctx) with
  | .ok s => return (some s, none)
  | .error e =>
    bumpIxc fun st => (st.sample s!"scope new: {e}") |> fun st =>
      { st with scopesRefused := st.scopesRefused + 1 }
    return (none, some e)

/-- Open a scope over `ctx` with level parameters `lps`, for the generator
    `route`. On the `recursor` route, IxC's lazy scope reads `overlay` (the
    recursor generator's overlay: a nested block's synthetic auxiliaries)
    before the input's declarations (AuxGen M5c); other routes ignore it. -/
def new (k : AuxKernel) (ctx : Array LocalDecl) (lps : Array Name)
    (route : AuxRoute) (overlay : Name → Option ConstantInfo := fun _ => none) :
    KBridgeM AuxScope := do
  k.validate
  checkScopeNames ctx lps
  let .ixc _ o := k
  let scope ← match route with
    | .recursor => pure (o.newLazyScope overlay lps (oracleLocals ctx))
    | .below | .brecOn =>
      match ← ixcNew o ctx lps with
      | (some scope, _) => pure scope
      | (none, e) => refuseIxc route.label s!"the scope over {ctx.size} locals" (e.getD "")
  return { kernel := k, levelParams := lps, locals := ctx, nOuter := ctx.size,
           backend := .ixc scope, route }

/-- Push a telescope onto the scope. -/
def push (s : AuxScope) (decls : Array LocalDecl) : KBridgeM AuxScope := do
  match s.backend with
  | .ixc o =>
    for decl in decls do
      if s.locals.any (·.fvarName == decl.fvarName) then
        throwBridge (.duplicatePushedFVar decl.fvarName)
    match o.push (oracleLocals decls) with
    | .ok o' => return { s with locals := s.locals ++ decls, backend := .ixc o' }
    | .error e =>
      refuseIxc s.label s!"the push of {decls.size} locals \
        ({", ".intercalate (decls.toList.map (·.fvarName.pretty))})" e

/-- Pop the most recently pushed telescope `decls`. -/
def pop (s : AuxScope) (decls : Array LocalDecl) : KBridgeM AuxScope := do
  -- `popLocals` refuses a pop beyond the pushed locals or out of order, so
  -- the truncation below removes exactly `decls`.
  let keep := s.locals.size - decls.size
  match s.backend with
  | .ixc o =>
    -- the same refusals as `popLocals`
    if decls.size > s.locals.size - s.nOuter then throwBridge .popExceedsPushed
    for (decl, i) in decls.zipIdx do
      if (s.locals[keep + i]?.map (·.fvarName == decl.fvarName)) != some true then
        throwBridge (.popNotLifo decl.fvarName)
    match o.pop decls.size with
    | .ok o' => return { s with locals := s.locals.extract 0 keep, backend := .ixc o' }
    | .error e => refuseIxc s.label s!"the pop of {decls.size} locals" e

/-- The sort level of a type in the scope (contract clause 3; fail closed). -/
def getLevel (s : AuxScope) (ty : Expr) : KBridgeM Level := do
  match s.backend with
  | .ixc o =>
    bumpIxc fun st => { st with queries := st.queries + 1 }
    match o.getLevel ty with
    | .ok (l, fast, _) =>
      bumpIxc fun st => { st with answered := st.answered + 1,
                                  ixcFast := st.ixcFast + (if fast then 1 else 0) }
      return l
    | .error e =>
      bumpIxc fun st => (st.sample s!"getLevel refused: {e}") |> fun st =>
        { st with refused := st.refused + 1 }
      refuseIxc s.label s!"getLevel of a type headed by {headOf ty}" e

/-- An IxC-only scope's answer to an expression question (`failClosed`): a
    refusal fails the block. -/
private def ixcExprOnly (op : String) (scope question : String) (o : OracleScope)
    (ask : OracleScope → Except String (Expr × OracleScope)) : KBridgeM (Option Expr) := do
  bumpIxc fun st => { st with exprQueries := st.exprQueries + 1 }
  match ask o with
  | .ok (e, _) =>
    bumpIxc fun st => { st with exprAnswered := st.exprAnswered + 1 }
    return some e
  | .error err =>
    bumpIxc fun st => (st.sample s!"{op} refused: {err}") |> fun st =>
      { st with refused := st.refused + 1 }
    refuseIxc scope question err

/-- Count how IxC answered a named `whnf` (AuxGen M4). -/
private def bumpHow (how : WhnfHow) : KBridgeM Unit :=
  bumpIxc fun st => match how with
    | .stuck => { st with recStuck := st.recStuck + 1 }
    | .same => { st with recSame := st.recSame + 1, recForced := st.recForced + 1 }
    | .replayed => { st with recReplayed := st.recReplayed + 1, recForced := st.recForced + 1 }
    | .beta => { st with recBeta := st.recBeta + 1 }

/-- An IxC refusal of a named `whnf`, counted. -/
private def bumpRecRefused (err : String) : KBridgeM Unit :=
  bumpIxc fun st => (st.sample s!"rec whnf refused: {err}") |> fun st =>
    { st with recRefused := st.recRefused + 1, recForced := st.recForced + 1 }

/-- Named WHNF for the recursor generator; refusal fails the tail. -/
def whnfRec? (s : AuxScope) (e : Expr) : KBridgeM (Option Expr) := do
  match s.backend with
  | .ixc o =>
    bumpIxc fun st => { st with recWhnf := st.recWhnf + 1 }
    match o.whnfNamed e with
    | .ok (w, how, _) =>
      bumpHow how
      return some w
    | .error err =>
      bumpRecRefused err
      refuseIxc s.label s!"whnf of a term headed by {headOf e}" err

/-- AuxGen M4: a `recursor` scope on IxC, where `findRecTarget` skips the
    Phase 2 of a field that names no member of the block's classes. -/
def skipsUnmentioned (s : AuxScope) : Bool :=
  s.route == .recursor

/-- The weak head normal form in the scope; `none` when the kernel gives no
    answer (clause 4). IxC's answer is decision-grade (AuxGen M3: its binder
    names are anonymous; only `.brecOn.eq`'s unit-like test reads it). -/
def whnf? (s : AuxScope) (e : Expr) : KBridgeM (Option Expr) := do
  if s.route == .recursor then return ← s.whnfRec? e
  match s.backend with
  | .ixc o => ixcExprOnly "whnf" s.label s!"whnf of a term headed by {headOf e}" o (·.whnf e)

/-- Definitional equality in the scope; `none` when the kernel gives no
    answer (clause 5). Refusals fail the checked tail. -/
def isDefEq? (s : AuxScope) (a b : Expr) : KBridgeM (Option Bool) := do
  match s.backend with
  | .ixc o =>
    bumpIxc fun st => { st with decisions := st.decisions + 1 }
    match o.isDefEq a b with
    | .ok (q, _) => return some q
    | .error err =>
      bumpIxc fun st => (st.sample s!"isDefEq refused: {err}") |> fun st =>
        { st with refused := st.refused + 1 }
      refuseIxc s.label s!"isDefEq of terms headed by {headOf a} and {headOf b}" err

/-- The type of a term in the scope, for decisions only; `none` when the
    kernel gives no answer (clause 6). IxC's answer is decision-grade, as
    `whnf?`'s. -/
def inferType? (s : AuxScope) (e : Expr) : KBridgeM (Option Expr) := do
  match s.backend with
  | .ixc o =>
    ixcExprOnly "inferType" s.label s!"inferType of a term headed by {headOf e}" o (·.infer e)

/-- The normal form, keeping the interface's explicit absent-answer default. -/
def whnfOrInput (s : AuxScope) (e : Expr) : KBridgeM Expr := do
  if s.route == .recursor then return (← s.whnfRec? e).getD e
  return (← s.whnf? e).getD e

/-- D-12's fail-open default for `isDefEq?`: `false` when the kernel gives
    no answer. -/
def isDefEqOrFalse (s : AuxScope) (a b : Expr) : KBridgeM Bool :=
  return (← s.isDefEq? a b).getD false

end AuxScope

namespace AuxKernel

/-! ### The elimination decision on IxC (AuxGen M4)

`Ix.Tc`'s `RecM.getResultSortLevel` and `RecM.isLargeEliminator` (Lean's
`elim_only_at_universe_zero`), ported onto an IxC lazy scope: telescopes
peeled syntactically, through `whnf` where a head is stuck; levels by
`getLevel` (its `inferAppType` fast path first). IxC's acceptance of the
generated recursor (the canonical block, M4) validates the decision; the
complete captured references retain its previous output. -/

/-- Always zero, whatever the parameters (`Ix.Tc`'s `isSemanticZero`, and
`univEq _ zero`). -/
def levelAlwaysZero : Level → Bool
  | .zero _ => true
  | .max a b _ => levelAlwaysZero a && levelAlwaysZero b
  | .imax _ b _ => levelAlwaysZero b
  | _ => false

/-- Never zero (`Ix.Tc`'s `KUniv.isNeverZero`). -/
def levelNeverZero : Level → Bool
  | .succ _ _ => true
  | .max a b _ => levelNeverZero a || levelNeverZero b
  | .imax _ b _ => levelNeverZero b
  | _ => false

/-- The decision's fresh local names. -/
private def elimLocal (s : String) (i : Nat) : Name :=
  Name.mkNat (Name.mkStr (Name.mkStr Name.mkAnon "_ixelim") s) i

/-- Peel one `∀` of `ty` into `sc` (through `whnf` when the head is not a
`∀`): the scope with the binder pushed, the body instantiated, the domain,
whether the service was needed; `none` when there is no `∀`. -/
private def elimPeel (sc : OracleScope) (ty : Expr) (name : Name) :
    Except String (Option (OracleScope × Expr × Expr × Bool)) := do
  let (w, forced) ← match ty with
    | .forallE .. => pure (ty, false)
    | _ => do
      let (w, how, _) ← sc.whnfNamed ty
      pure (w, !(how matches .stuck | .beta))
  match w with
  | .forallE _ dom body _ _ =>
    let sc ← sc.push #[(name, dom)]
    return some (sc, instantiate1 body (Expr.mkFVar name), dom, forced)
  | _ => return none

/-- **The elimination decision from IxC's services**, and whether the
service was needed (a question escaped the fast paths). -/
def ixcElimDecision (o : AuxOracle) (originals : Array (InductiveVal × Array ConstructorVal))
    (nParams nFlat : Nat) : Except String (ElimDecision × Bool) := do
  Configuration.validateCapability o |>.mapError Configuration.Error.render
  let some (first, ctors0) := originals[0]? | throw "elimination: no class"
  let lps := first.cnst.levelParams
  let mut forced := false
  -- the result sort, after the parameters and indices
  let mut sc := o.newLazyScope (fun _ => none) lps #[]
  let mut ty := first.cnst.type
  for i in [0:nParams + first.numIndices] do
    match ← elimPeel sc ty (elimLocal "r" i) with
    | some (sc', body, _, f) =>
      sc := sc'
      ty := body
      forced := forced || f
    | none => throw s!"get_result_sort_level: expected {nParams + first.numIndices} foralls, \
        only found {i}"
  let w ← match ty with
    | .sort .. => pure ty
    | _ => do
      let (w, how, _) ← sc.whnfNamed ty
      forced := forced || !(how matches .stuck | .beta)
      pure w
  let .sort u _ := w | throw "get_result_sort_level: not a sort"
  let resultLevel := Egress.normalize u
  let isProp := levelAlwaysZero resultLevel
  if !levelNeverZero resultLevel && nFlat != 1 then
    return ({ isLarge := false, isProp }, forced)
  -- `isLargeEliminator`
  if levelNeverZero resultLevel then return ({ isLarge := true, isProp }, forced)
  if originals.size != 1 then return ({ isLarge := false, isProp }, forced)
  match ctors0.size with
  | 0 => return ({ isLarge := true, isProp }, forced)
  | 1 =>
    let some ctor := ctors0[0]? | throw "elimination: constructor"
    if ctor.numFields == 0 then return ({ isLarge := true, isProp }, forced)
    sc := o.newLazyScope (fun _ => none) lps #[]
    ty := ctor.cnst.type
    let mut nonTrivial : Array Nat := #[]
    let mut fields : Array Name := #[]
    for i in [0:nParams + ctor.numFields] do
      let name := elimLocal "f" i
      match ← elimPeel sc ty name with
      | some (sc', body, dom, f) =>
        forced := forced || f
        if i ≥ nParams then
          let (lvl, fast, _) ← sc.getLevel dom
          forced := forced || !fast
          if !levelAlwaysZero lvl then nonTrivial := nonTrivial.push (i - nParams)
          fields := fields.push name
        sc := sc'
        ty := body
      | none => break
    let (_, retArgs) := decomposeApps ty
    let isLarge := nonTrivial.all fun fi =>
      match fields[fi]? with
      | some target => retArgs.any fun arg => match arg with
        | .fvar n _ => Ix.Compile.ExactKey.nameEq n target
        | _ => false
      | none => false
    return ({ isLarge, isProp }, forced)
  | _ => return ({ isLarge := false, isProp }, forced)

/-- Install the actual Prop-level family for its checked recursor generation. -/
def withFamily (k : AuxKernel) (types : Array (InductiveVal × Array ConstructorVal)) :
    KBridgeM AuxKernel := do
  k.validate
  let .ixc maps o := k
  match o.withFamily types with
  | .ok o' =>
    bumpIxc fun st => { st with familyInstalled := st.familyInstalled + 1 }
    return .ixc maps o'
  | .error e =>
    bumpIxc fun st => (st.sample s!"Prop-level .below family refused: {e}") |> fun st =>
      { st with familyRefused := st.familyRefused + 1 }
    refuseIxc "the Prop-level .below family's install" s!"the family of \
      {((types[0]?).map (·.1.cnst.name.pretty)).getD "[no member]"}" e

/-- The checked elimination decision over the actual expanded block. -/
def elimDecision (k : AuxKernel)
    (originals : Array (InductiveVal × Array ConstructorVal)) (nParams nFlat : Nat) :
    KBridgeM ElimDecision := do
  k.validate
  let .ixc _ o := k
  bumpIxc fun st => { st with elim := st.elim + 1 }
  match ixcElimDecision o originals nParams nFlat with
  | .ok (d, forced) =>
    if forced then bumpIxc fun st => { st with recForced := st.recForced + 1 }
    return d
  | .error e =>
    bumpIxc fun st => (st.sample s!"elimination refused: {e}") |> fun st =>
      { st with elimRefused := st.elimRefused + 1 }
    refuseIxc "the block's elimination decision" s!"the elimination decision of \
      {((originals[0]?).map (·.1.cnst.name.pretty)).getD "[no class]"}" e

/-- Admit generated Type-level definitions and forward the actual successor.
Prop families are installed separately by withFamily. -/
def admitGenerated (k : AuxKernel) (consts : Array BelowConstant) : KBridgeM AuxKernel := do
  k.validate
  match k with
  | .ixc maps o =>
    let defs := consts.filterMap fun | .defn d => some d | .indc _ => none
    if defs.isEmpty then return k
    match o.admitBelow defs with
    | .ok (o', ok, bad) =>
      bumpIxc fun st => { st with belowAdmitted := st.belowAdmitted + ok,
                                  belowRefused := st.belowRefused + bad }
      return .ixc maps o'
    | .error e =>
      bumpIxc fun st => (st.sample s!"admit .below: {e}") |> fun st =>
        { st with belowRefused := st.belowRefused + defs.size }
      return k

/-- Install the canonical flat block when its layout differs from Lean's. -/
def withFlatBlockVerdict (k : AuxKernel) (classes : Array (Array Name)) (originalAll : Array Name)
    (canonicalRecs : Array (Name × RecursorVal)) :
    KBridgeM (AuxKernel × Option CanonicalVerdict) := do
  k.validate
  match k with
  | .ixc maps o =>
    match o.withFlat classes originalAll canonicalRecs with
    | .ok none => return (k, none)
    | .ok (some o') =>
      bumpIxc fun st => { st with flatInstalled := st.flatInstalled + 1 }
      return (.ixc maps o', some .installed)
    | .error e =>
      bumpIxc fun st => (st.sample s!"flat block: {e}") |> fun st =>
        { st with flatRefused := st.flatRefused + 1 }
      refuseIxc "the canonical flat block's install" s!"the install of the flat block of \
        {((classes[0]?.bind (·[0]?)).map (·.pretty)).getD "[no class]"}" e

/-- `withFlatBlockVerdict`'s kernel. -/
def withFlatBlock (k : AuxKernel) (classes : Array (Array Name)) (originalAll : Array Name)
    (canonicalRecs : Array (Name × RecursorVal)) : KBridgeM AuxKernel :=
  Prod.fst <$> k.withFlatBlockVerdict classes originalAll canonicalRecs

/-- Two recursors equal as declarations, names and binder data included. -/
def sameRecursor (a b : RecursorVal) : Bool :=
  open Ix.Compile.ExactKey in
  nameEq a.cnst.name b.cnst.name && a.cnst.levelParams.isEqv b.cnst.levelParams nameEq
    && exprEq a.cnst.type b.cnst.type && a.all.isEqv b.all nameEq
    && a.numParams == b.numParams && a.numIndices == b.numIndices
    && a.numMotives == b.numMotives && a.numMinors == b.numMinors
    && a.k == b.k && a.isUnsafe == b.isUnsafe && a.rules.size == b.rules.size
    && (a.rules.zip b.rules).all fun (r, s) =>
      nameEq r.ctor s.ctor && r.nfields == s.nfields && exprEq r.rhs s.rhs

/-- **The canonical block checked by Source mode** (AuxGen M4a; production's
since M4b, with `AuxOracle.recursors`), right after the recursors are
generated: for a block whose layout is not Lean's, its canonical flat block,
the generated recursors included, installed through σ (`withFlatBlock`;
IxC's install is the check, counted as `flat` installed or refused); for a
block whose layout is Lean's, each generated recursor compared with Lean's
own (`leanRecSame`, `leanRecDiffer`), whose acceptance is the input's. The
kernel after it, and whether the check ran (then `.below` needs no second
install). The verdict is left in the bridge context (`AuxKernelCtx.canonical`,
AuxGen M4c) for the driver to record. -/
def checkCanonicalBlock (k : AuxKernel) (classes : Array (Array Name))
    (originalAll : Array Name) (canonicalRecs : Array (Name × RecursorVal)) :
    KBridgeM (AuxKernel × Bool) := do
  k.validate
  match k with
  | .ixc _ _ =>
    let nClasses := classes.size
    let auxNames := (canonicalRecs.extract nClasses canonicalRecs.size).map (·.1)
    let leanNested ← match originalAll[0]? with
      | some n => do
        match ← lookupConst? n with
        | some (.inductInfo v) => pure v.numNested
        | _ => pure 0
      | none => pure 0
    if Flat.needed classes originalAll auxNames leanNested then
      let (k', verdict) ← k.withFlatBlockVerdict classes originalAll canonicalRecs
      let installed : Option AuxOracle := match verdict, k' with
        | some .installed, .ixc _ o' => some o'
        | _, _ => none
      modify fun c => { c with canonical := verdict, canonicalOracle := installed }
      return (k', true)
    let mut same := 0
    let mut differ : Option String := none
    for (n, rv) in canonicalRecs do
      match ← lookupConst? n with
      | some (.recInfo lean) =>
        if sameRecursor rv lean then
          same := same + 1
          bumpIxc fun st => { st with leanRecSame := st.leanRecSame + 1 }
        else
          differ := differ.orElse fun _ => some n.pretty
          bumpIxc fun st => (st.sample s!"canonical recursor differs from Lean's: {n.pretty}") |>
            fun st => { st with leanRecDiffer := st.leanRecDiffer + 1 }
      | _ =>
        differ := differ.orElse fun _ => some s!"{n.pretty} (no Lean recursor)"
        bumpIxc fun st => (st.sample s!"no Lean recursor: {n.pretty}") |>
          fun st => { st with leanRecDiffer := st.leanRecDiffer + 1 }
    let verdict : CanonicalVerdict := match differ with
      | some first => .leanDiffer first
      | none => .leanSame same
    modify fun c => { c with canonical := some verdict }
    return (k, true)

end AuxKernel

end Ix.AuxGen

end
