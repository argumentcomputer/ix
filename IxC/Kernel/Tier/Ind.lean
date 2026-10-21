module

public import IxC.Kernel.Tier.Check
public import IxC.Kernel.Inductives.StructParts

@[expose] public section

/-!
# The typing tier: an inductive block, typing only (M7 Q1)

An unsafe inductive block has no model, and the front ends decline it. AuxGen
still asks questions about such a block (its `.below` levels, its recursors'
`whnf`, the elimination decision), and about the Prop-level `.below` family
of any block before that family has recursors. `indC` checks such a block
**typing only**, at the index `fe` of the environment it is installed over:

1. **the shape** (`indShape`): a type former first; distinct keys, every one
   an input key; one list of universe parameters for the formers and the
   constructors; every constructor names a former of the block;
2. **the formers** (`typeC`), each at `fe`: `checkConstantValC` (the guards,
   the annotation, the type a sort), and the type a sort after its parameters
   and indices (syntactically); every former's parameters are the first
   former's;
3. **the formers pushed** as `indInfo` with **no capability**;
4. **the constructors** (`ctorC`), each at the index with the formers: the
   header checked; its parameters syntactically its former's; its result the
   former at those parameters and its index count of arguments; every
   field's sort within the result sort unless that is `Prop` (official's
   universe rule). **Positivity is not checked**, as official skips it for
   an unsafe block;
5. **the constructors pushed** as `ctorInfo`, and a **projection table** for
   each structure-like former (one constructor, no indices: what official's
   `infer_proj` types `.proj` on), built as the direct structure route
   builds its table (`structProjBodies`, `structProjGuards`);
6. **the given recursor records**, if any: each header checked, all pushed
   **without rules**; then each rule (`ruleC`): its constructor stored, its
   field count, its right-hand side annotated (`annotValC`), and **typed**:
   at the recursor's prefix and the constructor's fields opened as free
   variables, the rule's two sides (the recursor at the constructor
   application, the right-hand side at the prefix and the fields) have
   definitionally equal types. A rule whose major is not the block's own
   former at the recursor's parameters is a nested auxiliary's, read at the
   instantiations of the recursor's major premise (`nestedPins`).

The records are **given**, not generated: an unsafe block's are the input's,
a regenerated family's are AuxGen's. IxC generates recursors for one family
only (`structRecTyR`), and the shadow comparison of every answer with Lean's
checks the records' use.

**No theorem and no verdict.** Nothing here is a statement: what passes is
installed only where AuxGen's questions are answered (the Source service,
`Ix.AuxGen`), never in the logical environment, and the result is never
reported as accepted. The check view it returns has the block's constants
**opaque** (no capability, no ι rule): only the projection tables'
structural rule fires there. The δ and ι forms the answers need are
`Ix.Kernel.Tier.Answer`'s, which no checking path imports
(`Tests/Ix/Kernel/Layering.lean`, the answers fence).
-/

namespace Ix.Kernel.Tier

open Ix.Kernel Ix.Kernel.Cached

/-- A recursor record's counts. -/
structure TierRecShape where
  params : Nat
  motives : Nat
  minors : Nat
  indices : Nat
  deriving Inhabited, Repr

/-- The major premise's position (`params + motives + minors + indices`). -/
def TierRecShape.majorIdx (s : TierRecShape) : Nat := s.params + s.motives + s.minors + s.indices

/-- The rule prefix's length (`params + motives + minors`). -/
def TierRecShape.rulePrefix (s : TierRecShape) : Nat := s.params + s.motives + s.minors

/-- **An inductive block for the tier**, as a front end converts it. -/
structure TierInd (md : Mode) where
  numParams : Nat
  /-- each type former's header and index count, in block order -/
  types : List (ConstantVal md × Nat)
  /-- each constructor's header, its former's position in `types` and its
  field count, in block order -/
  ctors : List (ConstantVal md × Nat × Nat)
  /-- the given recursor records (none for a family installed before its
  recursors exist): header, counts, rules at their parse placeholders -/
  recs : List (ConstantVal md × TierRecShape × List (RecRule md))
  deriving Inhabited

/-- **What `indC` returns.** -/
structure TierIndOut (md : Mode) where
  numParams : Nat
  /-- the annotated formers: header, index count, result sort -/
  types : List (ConstantVal md × Nat × Level)
  /-- the annotated constructors: header, former position, field count -/
  ctors : List (ConstantVal md × Nat × Nat)
  /-- the annotated recursors: header, counts, and the rules with their
  annotated right-hand sides, constructor parameter counts and firing modes
  (`.plain` at the recursor's own parameters, `.nested` at the major's
  instantiations) -/
  recs : List (ConstantVal md × TierRecShape × List (RecRule md))
  /-- the structure-like formers' projection tables -/
  tables : List (ProjTable md)
  deriving Inhabited

/-- The records `infos` pushed onto `fe`, in order. -/
def pushAll (fe : FEnv md) : List (ConstantInfo md) → FEnv md
  | [] => fe
  | ci :: cis => pushAll (fe.push ci) cis

/-- A cached check from the empty memo state. -/
def runC (act : (CheckCM md) α) : Except (CheckError md) α :=
  match act {} with
  | .ok (a, _) => .ok a
  | .error e => .error e

/-- The formers' records in the check view: no capability. -/
def TierIndOut.typeInfos (o : TierIndOut md) : List (ConstantInfo md) :=
  o.types.map fun (cv, _, _) => .indInfo cv {}

/-- The constructors' records. -/
def TierIndOut.ctorInfos (o : TierIndOut md) : List (ConstantInfo md) :=
  o.ctors.map fun (cv, _, nF) => .ctorInfo cv o.numParams nF

/-- The recursors' records in the check view: no rule. -/
def TierIndOut.recInfosBare (o : TierIndOut md) : List (ConstantInfo md) :=
  o.recs.map fun (cv, sh, _) => .recInfo cv sh.majorIdx sh.rulePrefix []

/-- **The check view's records** of a checked block, in push order: the
formers (no capability), the constructors, the projection tables, the
recursors (no rule). -/
def TierIndOut.checkInfos (o : TierIndOut md) : List (ConstantInfo md) :=
  o.typeInfos ++ o.ctorInfos ++ o.tables.map .projInfo ++ o.recInfosBare

/-- The block's headers, in block order (formers, constructors, recursors). -/
def TierIndOut.headers (o : TierIndOut md) : List (ConstantVal md) :=
  o.types.map (·.1) ++ o.ctors.map (·.1) ++ o.recs.map (·.1)

/-! ## The checks -/

/-- **The shape**: the first former's universe parameters, after the
block-wide guards. -/
def indShape (b : TierInd md) : Except (CheckError md) (List LevelParam) := do
  let some (cv₀, _) := b.types.head?
    | throw (.notImplemented "tier: an inductive block without a type former")
  let names := b.types.map (·.1.name) ++ b.ctors.map (·.1.name) ++ b.recs.map (·.1.name)
  unless decide names.Nodup do
    throw (.notImplemented msg!"tier: an inductive block declares a key twice ({cv₀.name})")
  for k in names do
    match k with
    | .id _ => pure ()
    | k => throw (.notImplemented msg!"tier: a role key or a generated key ({k})")
  for (cv, _) in b.types do
    unless cv.levelParams == cv₀.levelParams do
      throw (.notImplemented msg!"tier: the formers of a block disagree on their universe parameters ({cv.name})")
  for (cv, i, _) in b.ctors do
    unless cv.levelParams == cv₀.levelParams do
      throw (.notImplemented msg!"tier: a constructor's universe parameters are not its block's ({cv.name})")
    unless i < b.types.length do
      throw (.notImplemented msg!"tier: a constructor of no former of its block ({cv.name})")
  pure cv₀.levelParams

/-- **A former** at `fe`: its header checked, its type a sort after its
parameters and indices; the annotated header and that sort. -/
def typeC (fe : FEnv md) (nP : Nat) (cv : ConstantVal md) (nIdx : Nat) :
    Except (CheckError md) (ConstantVal md × Level) := do
  let (cvA, _) ← runC (checkConstantValC .verified fe cv)
  let some (_, body) := cvA.type.stripPis (nP + nIdx)
    | throw (.notImplemented msg!"tier: the type of {cv.name} has fewer binders than its parameters and indices")
  let .sort s := body
    | throw (.notImplemented msg!"tier: the type of {cv.name} is not a sort after its parameters and indices")
  pure (cvA, s)

/-- The first `n` binder domains of a type, syntactically. -/
def paramDoms (n : Nat) (ty : Expr md) : Option (List (Expr md)) :=
  (ty.stripPis n).map fun (bs, _) => bs.map (·.1)

/-- **A constructor's fields' sorts**, each field's domain inferred at its
depth (the parameters and the earlier fields), within the result sort `s`
unless `s` is `Prop` (official's rule: a field's universe is at most the
result's). -/
def fieldSortsC (fe : FEnv md) (s : Level) (cname : Key md) :
    Nat → List (Expr md) → (CheckCM md) (List Level)
  | _, [] => pure []
  | d, fv :: fvs => do
    let r := coreKnotI .verified fe checkFuel
    let ty ← r.infer d fv.fvarTypeD
    let u ← ensureSortI r d ty
    unless Level.isEquiv s .zero == some true do
      unless Level.leq u s == some true do
        throw (.invalid msg!"tier: a field of {cname} lives in a universe above its type's")
    let us ← fieldSortsC fe s cname (d + 1) fvs
    pure (u :: us)

/-- **A constructor** at `fe` (the formers installed): its header checked;
its parameters its former's; its result its former at those parameters with
the former's index count of arguments; its fields' sorts. -/
def ctorC (fe : FEnv md) (nP : Nat) (tys : List (ConstantVal md × Nat × Level))
    (cv : ConstantVal md) (i nF : Nat) : Except (CheckError md) (ConstantVal md × List Level) := do
  let some (cvT, nIdx, s) := tys[i]?
    | throw (.internal msg!"tier: the former of {cv.name}")
  let (cvA, _) ← runC (checkConstantValC .verified fe cv)
  let some (fvs, body) := openPisAtFvars (nP + nF) cvA.type 0
    | throw (.notImplemented msg!"tier: the type of {cv.name} has fewer binders than its parameters and fields")
  unless paramDoms nP cvA.type == paramDoms nP cvT.type do
    throw (.notImplemented msg!"tier: the parameters of {cv.name} are not its former's ({cvT.name})")
  unless body.getAppFn == .const cvT.name (cvT.levelParams.map .param) do
    throw (.notImplemented msg!"tier: {cv.name} does not return its former {cvT.name}")
  let args := body.getAppArgs
  unless args.length == nP + nIdx && args.take nP == fvs.take nP do
    throw (.notImplemented msg!"tier: {cv.name} does not return {cvT.name} at its parameters and indices")
  let sorts ← runC (fieldSortsC fe s cv.name nP (fvs.drop nP))
  pure (cvA, sorts)

/-- **A structure-like former's projection table** (one constructor, no
indices), built as the direct structure route builds it. -/
def tableOf (lps : List LevelParam) (nP : Nat) (T : ConstantVal md × Nat × Level)
    (cs : List (ConstantVal md × Nat × Nat × List Level)) : Except (CheckError md) (Option (ProjTable md)) :=
  let (cvT, nIdx, s) := T
  match cs with
  | [(cvC, _, nF, sorts)] =>
    if nIdx == 0 then
      match structProjBodies cvT.name nP nF cvC.type with
      | some bodies =>
        .ok (some ⟨cvT.name, lps, nP, cvC.name, nF, s, bodies, structProjGuards cvC.type nP nF sorts, 0⟩)
      | none => .error (.internal msg!"tier: the projection bodies of {cvT.name}")
    else .ok none
  | _ => .ok none

/-- **A nested auxiliary rule's instantiations** (`nestedRuleShape`'s, with
no model): the major premise's former applied to `cnP` arguments that mention
no index variable, then to the index variables; its levels and those
arguments, scoped at the rule prefix. -/
def nestedPins (tyA : Expr md) (mI rP cnP : Nat) : Option (List Level × List (Expr md)) :=
  if rP ≤ mI then
    match tyA.stripPis mI with
    | some (_, .forallE dom _ _) =>
      match dom.getAppFn with
      | .const _ lvls =>
        let args := dom.getAppArgs
        let k := mI - rP
        let pins := (args.take cnP).map (Expr.lowerBVars k 0)
        if args.length == cnP + k && args.take cnP == pins.map (Expr.liftLooseBVars k 0) &&
            args.drop cnP == (List.range k).map (fun i => Expr.bvar (k - 1 - i)) &&
            pins.all (fun p => !p.hasFvar && p.looseBVarsBounded rP) then
          some (lvls, pins)
        else none
      | _ => none
    | _ => none
  else none

/-- **A rule, typed** at `fe` (the block installed, its recursors without
rules): the rule with its right-hand side annotated, its constructor's
parameter count and its firing mode. -/
def ruleC (fe : FEnv md) (cvR : ConstantVal md) (sh : TierRecShape) (rl : RecRule md) :
    Except (CheckError md) (RecRule md) := do
  let mI := sh.majorIdx
  let rP := sh.rulePrefix
  let some (.ctorInfo cvj cnP cnF) := fe.find? rl.ctor
    | throw (.invalid msg!"tier: the constructor {rl.ctor} of a rule of {cvR.name} is not stored")
  unless rl.nfields == cnF do
    throw (.invalid msg!"tier: a rule of {cvR.name} declares a field count that is not {rl.ctor}'s")
  let rhsA ← runC (annotValC .verified fe cvR rl.rhs)
  let some (fvs, _) := openPisAtFvars rP cvR.type 0
    | throw (.notImplemented msg!"tier: the type of {cvR.name} has fewer binders than its rule prefix")
  let plain := Expr.recRulePlain cvR.type mI rP cnP
  let (fire, lvls, cps) ← if plain then
      pure (RecRuleFire.plain, cvj.levelParams.map Level.param, fvs.take cnP)
    else match nestedPins cvR.type mI rP cnP with
      | some (lvls, pins) =>
        pure (RecRuleFire.nested lvls pins, lvls, pins.map (·.instantiateList fvs.reverse))
      | none => throw (.notImplemented msg!"tier: a rule of {cvR.name} whose major is not recognised")
  runC (do
    let r := coreKnotI .verified fe checkFuel
    let c0 := Expr.mkAppN (.const rl.ctor lvls) cps
    let cty ← r.infer rP c0
    let some (ffs, cbody) := openPisAtFvars cnF cty rP
      | throw (.notImplemented msg!"tier: the fields of {rl.ctor} in a rule of {cvR.name}")
    let idx := cbody.getAppArgs.drop cnP
    unless idx.length == sh.indices do
      throw (.notImplemented msg!"tier: the indices of {rl.ctor} in a rule of {cvR.name}")
    let d := rP + cnF
    let lhs := Expr.mkAppN (.const cvR.name (cvR.levelParams.map Level.param))
      (fvs ++ idx ++ [Expr.mkAppN c0 ffs])
    let rhs := Expr.mkAppN rhsA (fvs ++ ffs)
    let tl ← r.infer d lhs
    let tr ← r.infer d rhs
    unless ← r.defeq d tl tr do
      throw (.notImplemented msg!"tier: the rule of {rl.ctor} in {cvR.name} does not have its equation's type"))
  pure { rl with rhs := rhsA, ctorParams := cnP, fire := fire, paramsBlind := plain }

/-- Each item checked in order, the first failure the result's. -/
def mapC (f : α → Except ε β) : List α → Except ε (List β)
  | [] => .ok []
  | a :: as => do
    let b ← f a
    let bs ← mapC f as
    pure (b :: bs)

/-- **The typing-only check of an inductive block** at `fe` (see the
module's documentation). -/
def indC (fe : FEnv md) (b : TierInd md) : Except (CheckError md) (TierIndOut md) := do
  let lps ← indShape b
  let nP := b.numParams
  -- the formers, each at `fe`
  let tys ← mapC (fun (cv, nIdx) => do
      let (cvA, s) ← typeC fe nP cv nIdx
      pure (cvA, nIdx, s)) b.types
  let some (cv₀, _, _) := tys.head? | throw (.internal "tier: no former")
  for (cvA, _, _) in tys do
    unless paramDoms nP cvA.type == paramDoms nP cv₀.type do
      throw (.notImplemented msg!"tier: the formers of a block disagree on their parameters ({cvA.name})")
  let fe₁ := pushAll fe (tys.map fun (cv, _, _) => .indInfo cv {})
  -- the constructors, each at the formers' index
  let cts ← mapC (fun (cv, i, nF) => do
      let (cvA, sorts) ← ctorC fe₁ nP tys cv i nF
      pure (cvA, i, nF, sorts)) b.ctors
  let fe₂ := pushAll fe₁ (cts.map fun (cv, _, nF, _) => .ctorInfo cv nP nF)
  let tables ← mapC (fun (iT : Nat × (ConstantVal md × Nat × Level)) =>
      tableOf lps nP iT.2 (cts.filter (·.2.1 == iT.1))) (tys.zipIdx.map fun (t, i) => (i, t))
  let tables := tables.filterMap id
  for t in tables do
    if (fe₂.find? (projTableName t.structName)).isSome then
      throw (.invalid msg!"tier: the projection table of {t.structName} is taken")
  let fe₂ := pushAll fe₂ (tables.map .projInfo)
  -- the recursors' headers, each at the block's index; then their rules
  let rhs ← mapC (fun (cv, sh, rules) => do
      let (cvA, _) ← runC (checkConstantValC .verified fe₂ cv)
      unless cvA.levelParams.take lps.length == lps && cvA.levelParams.length ≤ lps.length + 1 do
        throw (.notImplemented msg!"tier: the universe parameters of {cv.name} are not its block's")
      unless (cvA.type.stripPis (sh.majorIdx + 1)).isSome do
        throw (.notImplemented msg!"tier: the type of {cv.name} has fewer binders than its counts")
      pure (cvA, sh, rules)) b.recs
  let fe₃ := pushAll fe₂ (rhs.map fun (cv, sh, _) => .recInfo cv sh.majorIdx sh.rulePrefix [])
  let recs ← mapC (fun (cvA, sh, rules) => do
      let rules' ← mapC (ruleC fe₃ cvA sh) rules
      pure (cvA, sh, rules')) rhs
  pure { numParams := nP, types := tys, ctors := cts.map fun (cv, i, nF, _) => (cv, i, nF),
         recs, tables }

end Ix.Kernel.Tier
