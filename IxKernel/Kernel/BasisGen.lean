module

public meta import Lean
public meta import IxKernel.Kernel.TypeChecker

/- `public section`, deliberately NOT `@[expose]`: every definition here is
elaboration-time machinery whose body no importer unfolds, and an exposed
body may not mention the module's `private` helpers (`splice`, the quoters,
the `evalX` wrappers). -/
public section

/-!
# `#annotate_basis` — the pinned declarations, annotated at elaboration time

The pinned basis blocks, the standard-axiom prerequisite families and
the compiler-trust pins are *stored annotated*: the installation
(`installBasisDecl`, `IxKernel/Kernel/Checker.lean`) puts them into the
environment verbatim, and the model proofs read their `pw` data off
the stored constants.  The annotated forms are not a second source of
truth — they are what **this checker's own annotation pass**
(`annotateCore` at `.verified`) computes from the raw pins.

Until 2026-09-06 that computation lived in an offline generator
(`AnnotateBasis.lean`, a `[[lean_exe]]`) whose `Repr` output was pasted
into the pin modules as ~1 900 lines of fully-qualified constructor
spellings.  The literals were therefore a *committed cache with no
checked relation to their source*: nothing in the build re-ran the
generator, and a stale paste would have been invisible.

`#annotate_basis` replaces the paste.  It runs the same recipe while
the pin module elaborates and defines the annotated constants with
`addDecl`/`compileDecl`, so the definition's value is the very term
`annotateCore` produced — the same closed literal the `decide`/`rfl`
consumers in `IxKernel/Kernel/Model/*` saw before, now *derived* rather than
transcribed, and re-derived on every build.  An annotation failure is
an elaboration error, never a silently stale constant.

## The recipe

Exactly what `checkDecl`'s `.basisDecl` install would do, in
dependency order:

* the constant's **type** is annotated over the environment holding
  the pins annotated so far (`over` gives that environment's tail);
* for a recursor, the install-computed rule fields are filled first —
  `ctorParams` from the stored constructor, `fire` from
  `Expr.recRulePlain` — and then each rule's **rhs** is annotated over
  the environment extended by the recursor itself (a rule's rhs may
  mention it, as `Nat.rec`'s successor rule does);
* the result is appended to the environment for the next entry.

## The two commands

```
#annotate_basis over <env : List ConstantInfo>
  | eqA := eqRaw
  | ...
```
defines `ConstantInfo` constants and threads each one into the
environment for the entries that follow.

```
#annotate_pins over <env : List ConstantInfo>
  | propextA := propextRaw
  | ...
```
defines `ConstantVal` constants (the two standard axioms and the four
compiler-trust pins), each annotated over the *same* environment; a
pin that must be visible to a later one is passed in the next
command's `over`.

The `over` term is elaborated and evaluated at `List ConstantInfo`, so
it may name constants this command defined earlier in the file.
-/

/- The whole module is elaboration-time code: quoters, the `#eval`-style
evaluators and the two command elaborators.  The module system wants a
`CommandElab` to be `meta` (`Cannot add attribute … must be marked as
`meta``), and `meta section` is how a file that is meta THROUGHOUT says
so once. -/
meta section

namespace Ix.Kernel.BasisGen

open Lean Elab Command Term Meta

/-! ## Quoting a `Ix.Kernel` value back into a `Lean.Expr`

The annotation runs on real `Ix.Kernel` values; the definition it splices
must carry them as terms.  These are the structural quoters — one
constructor application each, with no sharing (the pins are small; the
biggest is `Quot.lift`'s rule, a few hundred nodes). -/

private def qBool : Bool → Lean.Expr
  | true => mkConst ``Bool.true
  | false => mkConst ``Bool.false

private def qList (ty : Lean.Expr) (xs : List Lean.Expr) : Lean.Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [Lean.Level.zero]) ty x acc)
    (mkApp (mkConst ``List.nil [Lean.Level.zero]) ty)

private def nameTy : Lean.Expr := mkConst ``Ix.Kernel.Name
private def levelTy : Lean.Expr := mkConst ``Ix.Kernel.Level
private def exprTy : Lean.Expr := mkConst ``Ix.Kernel.Expr
private def recRuleTy : Lean.Expr := mkConst ``Ix.Kernel.RecRule
private def constantInfoTy : Lean.Expr := mkConst ``Ix.Kernel.ConstantInfo
private def constantValTy : Lean.Expr := mkConst ``Ix.Kernel.ConstantVal

private def qName : Ix.Kernel.Name → Lean.Expr
  | .anonymous => mkConst ``Ix.Kernel.Name.anonymous
  | .str p s => mkApp2 (mkConst ``Ix.Kernel.Name.str) (qName p) (mkStrLit s)
  | .num p i => mkApp2 (mkConst ``Ix.Kernel.Name.num) (qName p) (mkRawNatLit i)

private def qNames (ns : List Ix.Kernel.Name) : Lean.Expr :=
  qList nameTy (ns.map qName)

private def qLevel : Ix.Kernel.Level → Lean.Expr
  | .zero => mkConst ``Ix.Kernel.Level.zero
  | .succ a => mkApp (mkConst ``Ix.Kernel.Level.succ) (qLevel a)
  | .max a b => mkApp2 (mkConst ``Ix.Kernel.Level.max) (qLevel a) (qLevel b)
  | .imax a b => mkApp2 (mkConst ``Ix.Kernel.Level.imax) (qLevel a) (qLevel b)
  | .param n => mkApp (mkConst ``Ix.Kernel.Level.param) (qName n)

private def qLevels (us : List Ix.Kernel.Level) : Lean.Expr :=
  qList levelTy (us.map qLevel)

/-- The zero-ness datum through its public API (the representation is
`private` to `IxKernel/Kernel/PropWhen.lean`): `never`, or `ifAllZero`
of its parameter list. -/
private def qPropWhen (pw : Ix.Kernel.PropWhen) : Lean.Expr :=
  match pw.toList? with
  | none => mkConst ``Ix.Kernel.PropWhen.never
  | some ps => mkApp (mkConst ``Ix.Kernel.PropWhen.ifAllZero) (qNames ps)

private def qBinderMeta (m : Ix.Kernel.BinderMeta) : Lean.Expr :=
  mkApp (mkConst ``Ix.Kernel.BinderMeta.mk) (qPropWhen m.pw)

private def qLiteral : Ix.Kernel.Literal → Lean.Expr
  | .natVal n => mkApp (mkConst ``Ix.Kernel.Literal.natVal) (mkRawNatLit n)
  | .strVal s => mkApp (mkConst ``Ix.Kernel.Literal.strVal) (mkStrLit s)

private def qExpr : Ix.Kernel.Expr → Lean.Expr
  | .bvar i => mkApp (mkConst ``Ix.Kernel.Expr.bvar) (mkRawNatLit i)
  | .fvar i ty => mkApp2 (mkConst ``Ix.Kernel.Expr.fvar) (mkRawNatLit i) (qExpr ty)
  | .sort u => mkApp (mkConst ``Ix.Kernel.Expr.sort) (qLevel u)
  | .const n us => mkApp2 (mkConst ``Ix.Kernel.Expr.const) (qName n) (qLevels us)
  | .app f a => mkApp2 (mkConst ``Ix.Kernel.Expr.app) (qExpr f) (qExpr a)
  | .lam ty b m =>
    mkApp3 (mkConst ``Ix.Kernel.Expr.lam) (qExpr ty) (qExpr b) (qBinderMeta m)
  | .forallE ty b m =>
    mkApp3 (mkConst ``Ix.Kernel.Expr.forallE) (qExpr ty) (qExpr b) (qBinderMeta m)
  | .letE ty v b =>
    mkApp3 (mkConst ``Ix.Kernel.Expr.letE) (qExpr ty) (qExpr v) (qExpr b)
  | .lit l => mkApp (mkConst ``Ix.Kernel.Expr.lit) (qLiteral l)
  | .proj s i e =>
    mkApp3 (mkConst ``Ix.Kernel.Expr.proj) (qName s) (mkRawNatLit i) (qExpr e)

private def qConstantVal (cv : Ix.Kernel.ConstantVal) : Lean.Expr :=
  mkApp3 (mkConst ``Ix.Kernel.ConstantVal.mk) (qName cv.name)
    (qNames cv.levelParams) (qExpr cv.type)

private def qRecRuleFire : Ix.Kernel.RecRuleFire → Lean.Expr
  | .inert => mkConst ``Ix.Kernel.RecRuleFire.inert
  | .plain => mkConst ``Ix.Kernel.RecRuleFire.plain
  | .nested lvls pins =>
    mkApp2 (mkConst ``Ix.Kernel.RecRuleFire.nested) (qLevels lvls)
      (qList exprTy (pins.map qExpr))

private def qRecRule (r : Ix.Kernel.RecRule) : Lean.Expr :=
  mkAppN (mkConst ``Ix.Kernel.RecRule.mk)
    #[qName r.ctor, mkRawNatLit r.nfields, mkRawNatLit r.ctorParams,
      qRecRuleFire r.fire, qExpr r.rhs, qBool r.k, qBool r.eta,
      qBool r.paramsBlind]

private def qIndCaps (c : Ix.Kernel.IndCaps) : Lean.Expr :=
  mkAppN (mkConst ``Ix.Kernel.IndCaps.mk)
    #[qBool c.eta, qName c.etaCtor, mkRawNatLit c.etaParams,
      mkRawNatLit c.etaFields, qBool c.unitlike, mkRawNatLit c.unitParams,
      qBool c.ruleK, qPropWhen c.sortZ]

private def qReducibilityHint : Ix.Kernel.ReducibilityHint → Lean.Expr
  | .«opaque» => mkConst ``Ix.Kernel.ReducibilityHint.«opaque»
  | .«abbrev» => mkConst ``Ix.Kernel.ReducibilityHint.«abbrev»
  | .regular h => mkApp (mkConst ``Ix.Kernel.ReducibilityHint.regular) (mkRawNatLit h)

private def qConstantInfo : Ix.Kernel.ConstantInfo → CoreM Lean.Expr
  | .axiomInfo cv => pure (mkApp (mkConst ``Ix.Kernel.ConstantInfo.axiomInfo) (qConstantVal cv))
  | .defnInfo cv v h =>
    pure (mkApp3 (mkConst ``Ix.Kernel.ConstantInfo.defnInfo) (qConstantVal cv)
      (qExpr v) (qReducibilityHint h))
  | .thmInfo cv v =>
    pure (mkApp2 (mkConst ``Ix.Kernel.ConstantInfo.thmInfo) (qConstantVal cv) (qExpr v))
  | .indInfo cv caps =>
    pure (mkApp2 (mkConst ``Ix.Kernel.ConstantInfo.indInfo) (qConstantVal cv) (qIndCaps caps))
  | .ctorInfo cv nP nF =>
    pure (mkApp3 (mkConst ``Ix.Kernel.ConstantInfo.ctorInfo) (qConstantVal cv)
      (mkRawNatLit nP) (mkRawNatLit nF))
  | .recInfo cv mI rP rules =>
    pure (mkAppN (mkConst ``Ix.Kernel.ConstantInfo.recInfo)
      #[qConstantVal cv, mkRawNatLit mI, mkRawNatLit rP,
        qList recRuleTy (rules.map qRecRule)])
  | .projInfo _ =>
    throwError "#annotate_basis: a projection table is not a pinnable declaration"

/-! ## The recipe -/

/-- Annotate one raw `ConstantInfo` over `env`, exactly as the basis
install does: the type first, then — for a recursor — the
install-computed rule fields (`ctorParams` off the stored constructor,
`fire` off `Expr.recRulePlain`) and the rules' right-hand sides over
the environment extended with the recursor itself. -/
def annotateInfo (env : Ix.Kernel.Env) (ci : Ix.Kernel.ConstantInfo) :
    Ix.Kernel.CheckM Ix.Kernel.ConstantInfo := do
  let cv := ci.toConstantVal
  let ty' ← Ix.Kernel.annotateCore .verified env Ix.Kernel.checkFuel 0 cv.type
  let cv' : Ix.Kernel.ConstantVal := { cv with type := ty' }
  match ci with
  | .indInfo _ caps => return .indInfo cv' caps
  | .ctorInfo _ nP nF => return .ctorInfo cv' nP nF
  | .axiomInfo _ => return .axiomInfo cv'
  | .defnInfo _ v h => return .defnInfo cv' v h
  | .thmInfo _ v => return .thmInfo cv' v
  | .projInfo tbl => return .projInfo tbl
  | .recInfo _ mI rP rules =>
    let rules := rules.map fun r =>
      let cnP := match env.find? r.ctor with
        | some (.ctorInfo _ nP _) => nP
        | _ => 0
      Ix.Kernel.recRuleBits env.find? cv'.name
        { r with ctorParams := cnP,
                 fire := if Ix.Kernel.Expr.recRulePlain ty' mI rP cnP then .plain else .inert,
                 paramsBlind := true }
    let envSelf : Ix.Kernel.Env := ⟨.recInfo cv' mI rP rules :: env.consts⟩
    let mut out : List Ix.Kernel.RecRule := []
    for r in rules do
      let rhs' ← Ix.Kernel.annotateCore .verified envSelf Ix.Kernel.checkFuel 0 r.rhs
      out := out ++ [{ r with rhs := rhs' }]
    return .recInfo cv' mI rP out

/-- Annotate one raw `ConstantVal` pin's type over `env`. -/
def annotateVal (env : Ix.Kernel.Env) (cv : Ix.Kernel.ConstantVal) :
    Ix.Kernel.CheckM Ix.Kernel.ConstantVal := do
  let ty' ← Ix.Kernel.annotateCore .verified env Ix.Kernel.checkFuel 0 cv.type
  return { cv with type := ty' }

/-! ## Evaluating the raw pins

`Lean.Elab.Term.evalTerm` is `unsafe`; the safe wrappers below are the
standard `@[implemented_by]` pairing (their own bodies are never run —
`implemented_by` replaces the compiled code). -/

private unsafe def evalInfoUnsafe (stx : Syntax) : TermElabM Ix.Kernel.ConstantInfo :=
  Term.evalTerm Ix.Kernel.ConstantInfo constantInfoTy stx

@[implemented_by evalInfoUnsafe]
private def evalInfo (_stx : Syntax) : TermElabM Ix.Kernel.ConstantInfo :=
  throwError "unreachable"

private unsafe def evalValUnsafe (stx : Syntax) : TermElabM Ix.Kernel.ConstantVal :=
  Term.evalTerm Ix.Kernel.ConstantVal constantValTy stx

@[implemented_by evalValUnsafe]
private def evalVal (_stx : Syntax) : TermElabM Ix.Kernel.ConstantVal :=
  throwError "unreachable"

private unsafe def evalEnvUnsafe (stx : Syntax) : TermElabM (List Ix.Kernel.ConstantInfo) :=
  Term.evalTerm (List Ix.Kernel.ConstantInfo)
    (mkApp (mkConst ``List [Lean.Level.zero]) constantInfoTy) stx

@[implemented_by evalEnvUnsafe]
private def evalEnv (_stx : Syntax) : TermElabM (List Ix.Kernel.ConstantInfo) :=
  throwError "unreachable"

/-! ## Splicing -/

/-- Define `declName : ty := value` (kernel-checked, then compiled),
with the reducibility hint an ordinary `def` of the same body would
get. -/
private def splice (declName : Lean.Name) (ty value : Lean.Expr) :
    TermElabM Unit := do
  let hints : Lean.ReducibilityHints := .regular (getMaxHeight (← getEnv) value + 1)
  let decl : Lean.Declaration := .defnDecl
    (← mkDefinitionValInferringUnsafe declName [] ty value hints)
  -- MODULE SYSTEM (task #231).  A spliced constant must land in the *public*
  -- scope with its body exposed, exactly as the `def` it replaces would:
  -- `addDecl` otherwise derives an opaque `axiom` presentation for the public
  -- view (`Lean/AddDecl.lean`), and downstream `rfl`/`decide` proofs over the
  -- pins — every `Model/Basis*` consumer — would lose the value they read.
  withExporting (isExporting := true) do
    addDecl decl (forceExpose := true)
  compileDecl decl

/-! ## The commands -/

/-- One `| name := rawTerm` entry.  The leading `|` is what keeps the
entries from being parsed as one applied term. -/
syntax annotEntry := " | " ident " := " term

/-- `#annotate_basis over <env> | nameA := nameRaw ...` — annotate raw
`ConstantInfo` pins in order, each over the environment of `<env>`
extended by the ones already annotated, and define the results. -/
syntax (name := annotateBasisCmd)
  "#annotate_basis" " over " term (annotEntry)+ : command

/-- `#annotate_pins over <env> | nameA := nameRaw ...` — annotate raw
`ConstantVal` pins, each over the *same* environment, and define the
results. -/
syntax (name := annotatePinsCmd)
  "#annotate_pins" " over " term (annotEntry)+ : command

@[command_elab annotateBasisCmd]
def elabAnnotateBasis : CommandElab := fun stx => do
  let entries := stx[3].getArgs
  let mut consts : List Ix.Kernel.ConstantInfo ←
    liftTermElabM (evalEnv stx[2])
  for e in entries do
    let id := e[1]
    let rawStx := e[3]
    let raw ← liftTermElabM (evalInfo rawStx)
    let ci ←
      match annotateInfo ⟨consts⟩ raw with
      | .ok ci => pure ci
      | .error err =>
        throwErrorAt rawStx
          "#annotate_basis: annotating {id.getId} failed: {toString err}"
    liftTermElabM do
      splice ((← getCurrNamespace) ++ id.getId) constantInfoTy (← qConstantInfo ci)
    consts := ci :: consts

@[command_elab annotatePinsCmd]
def elabAnnotatePins : CommandElab := fun stx => do
  let entries := stx[3].getArgs
  let consts : List Ix.Kernel.ConstantInfo ← liftTermElabM (evalEnv stx[2])
  for e in entries do
    let id := e[1]
    let rawStx := e[3]
    let raw ← liftTermElabM (evalVal rawStx)
    let cv ←
      match annotateVal ⟨consts⟩ raw with
      | .ok cv => pure cv
      | .error err =>
        throwErrorAt rawStx
          "#annotate_pins: annotating {id.getId} failed: {toString err}"
    liftTermElabM do
      splice ((← getCurrNamespace) ++ id.getId) constantValTy (qConstantVal cv)

end Ix.Kernel.BasisGen

end  -- meta section
