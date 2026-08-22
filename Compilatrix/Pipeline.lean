import Compilatrix.Ixon.UsageCheck
import Compilatrix.Erase
import Compilatrix.EraseValidator
import Compilatrix.IxIR1.Lower

/-!
# Checked source-to-IxIR₁ pipeline

The first executable composition of the three previously independent
gatekeepers:

1. every Ixon constant passes `UsageCheck.checkConstant` against the
   same closed-world resolver;
2. the checked program is erased by `Erase.eraseProgram`;
3. the actual erased declarations are lowered by `IxIR1.lowerAll`.

`compile` is that engineering gate, not yet the end-to-end theorem:
UsageCheck's recorded higher-order limitations remain, erasure is
unvalidated (it deliberately accepts out-of-fragment programs the
proof-producing validator cannot yet certify), and IxIR₀ → IxIR₁ is
differentially tested rather than proved. `compileValidated` closes
the middle seam: it runs the same composition but certifies the exact
erased output against the simulation relation
(`EraseValidator.certifyProgram` / `certifySharedProgram`), failing
closed on the first declaration the validator rejects. Keeping the
composition in one API makes those obligations explicit and prevents
callers from accidentally skipping the usage check.
-/

namespace Compilatrix.Pipeline

open Compilatrix.Ixon (Address Constant Owned)

inductive Error where
  | usage (address : Address) (error : Ixon.UsageCheck.UsageErr)
  | erase (error : Erase.EraseErr)
  /-- The erasure validator rejected this declaration (or the main
  entry) with the given diagnostic — `compileValidated` only. -/
  | validate (address : Address) (message : String)
  | lower (message : String)
  deriving BEq, Repr

/-- Non-constant inputs needed while erasing a closed Ixon program. -/
structure Config where
  blobs : Address → Option Ixon.Eval.Blob := fun _ => none
  natBlock : Option Address := none

/-- The two executable compiler boundaries, retained together so
tests and future validators can inspect the exact intermediate. -/
structure Artifact where
  erasedDecls : List (Address × IxIR0.Decl)
  targetDecls : List (Address × IxIR1.Decl)
  main : IxIR1.Code

/-- Turn an enumerable closed world into the proof-friendly resolver
shared by checking and erasure. -/
def resolverOf (constants : List (Address × Constant)) :
    Address → Option Constant :=
  fun address =>
    (constants.find? (fun entry => entry.1 == address)).map (·.2)

/-- Check every constant, reporting which address failed. -/
def checkProgram (constants : List (Address × Constant))
    (fuel : Nat := Ixon.UsageCheck.defaultFuel) : Except Error Unit := do
  let resolve := resolverOf constants
  for (address, constant) in constants do
    match Ixon.UsageCheck.checkConstant resolve constant fuel with
    | .ok _ => pure ()
    | .error error => throw (.usage address error)

/-- Check, erase, and lower a closed program. `mainAddress` names the
closed entry value or computation in the source environment; lowering
rejects an unknown address or an entry incompatible with the requested
result demand.

The erasure step is **unvalidated**: this entry point accepts
out-of-fragment programs (externs, axioms, opaque definitions, shapes
beyond the current `Covered`/`PErase` fragment) that the
proof-producing validator cannot yet certify. Use `compileValidated`
when every declaration must carry a simulation certificate. -/
def compile (constants : List (Address × Constant))
    (mainAddress : Address) (config : Config := {})
    (mainWorld : Owned := .shared)
    (checkFuel : Nat := Ixon.UsageCheck.defaultFuel)
    (eraseFuel : Nat := Erase.defaultFuel)
    (lowerFuel : Nat := 10000) : Except Error Artifact := do
  checkProgram constants checkFuel
  let resolve := resolverOf constants
  let eraseCtx : Erase.EraseCtx :=
    { resolve, blobs := config.blobs, natBlock := config.natBlock }
  let erasedDecls ←
    match Erase.eraseProgram eraseCtx constants eraseFuel with
    | .ok decls => pure decls
    | .error error => throw (.erase error)
  match IxIR1.Lower.lowerAll erasedDecls (.ref mainAddress) mainWorld lowerFuel with
  | .ok (targetDecls, main) =>
    pure { erasedDecls, targetDecls, main }
  | .error message => throw (.lower message)

/-! ## The validator-gated entry point

`compile` runs the eraser unvalidated, so the proof-producing
`EraseValidator` is bypassable in the composed path.
`compileValidated` closes that seam: after the usage gate and the
(strict) eraser it requires a `Covered` certificate for **every**
non-block constant against the exact erased environment, obtained
through the sanctioned program entry points
(`EraseValidator.certifyProgram`, or `certifySharedProgram` when any
constant carries a sharing table). Mutual blocks themselves have no
block-level judgment — their members are certified through the
projection constants (`iPrj`/`cPrj`/`rPrj`/`dPrj`); an erased direct
member reference without a certified projection fails closed at the
referencing declaration. -/

/-- One fixpoint round of coverage validation: attempt every pending
address against the current database, extending it in place. Returns
the grown database, this round's successes (in attempt order), and the
still-rejected addresses with their diagnostics (in attempt order). -/
private def coverageRound (ectx : Ixon.Eval.EvalCtx) (ictx : IxIR0.Ctx)
    (validateFuel : Nat) (db : EraseValidator.CoverageDB ectx ictx) :
    List Address →
      EraseValidator.CoverageDB ectx ictx × List Address ×
        List (Address × String)
  | [] => (db, [], [])
  | address :: rest =>
    match EraseValidator.validateCovered ectx ictx db validateFuel address with
    | .ok ha =>
      let (db', oks, failed) := coverageRound ectx ictx validateFuel
        ({ address, covered := ha.down } :: db) rest
      (db', address :: oks, failed)
    | .error message =>
      let (db', oks, failed) := coverageRound ectx ictx validateFuel db rest
      (db', oks, (address, message) :: failed)

/-- Discover a dependency order for `certifyProgram` by fixpoint:
repeat `coverageRound` until every candidate validates. Fail-closed —
a round without progress reports the first still-rejected address and
its validator diagnostic. At most `candidates + 1` rounds are needed,
since a productive round covers at least one address. -/
private def coveragePlan (ectx : Ixon.Eval.EvalCtx) (ictx : IxIR0.Ctx)
    (validateFuel : Nat) :
    Nat → EraseValidator.CoverageDB ectx ictx → List Address →
      List Address → Except (Address × String) (List Address)
  | _, _, done, [] => .ok done.reverse
  | 0, _, _, address :: _ =>
    .error (address, "coverage validation did not converge")
  | rounds + 1, db, done, pending =>
    let (db', oks, failed) := coverageRound ectx ictx validateFuel db pending
    if oks.isEmpty then
      match failed with
      | (address, message) :: _ => .error (address, message)
      | [] => .ok done.reverse
    else
      coveragePlan ectx ictx validateFuel rounds db'
        (oks.reverse ++ done) (failed.map (·.1))

/-- Check, erase, **validate the exact erased output**, and lower.

The composition of `compile` with the proof-producing erasure
validator: after `checkProgram` and the strict eraser, every non-block
constant must earn a `Covered` certificate against the erased
environment, the whole program is re-certified through
`EraseValidator.certifyProgram`/`certifySharedProgram` (whose result
records the erasure equation for exactly this constant list), and only
then are the erased declarations lowered. The first declaration the
validator rejects is reported as `Error.validate` with the validator's
own diagnostic; `mainAddress` itself must be a certifiable declaration.
Out-of-fragment programs belong to `compile`. -/
def compileValidated (constants : List (Address × Constant))
    (mainAddress : Address) (config : Config := {})
    (mainWorld : Owned := .shared)
    (checkFuel : Nat := Ixon.UsageCheck.defaultFuel)
    (eraseFuel : Nat := Erase.defaultFuel)
    (validateFuel : Nat := Erase.defaultFuel)
    (lowerFuel : Nat := 10000) : Except Error Artifact := do
  checkProgram constants checkFuel
  let resolve := resolverOf constants
  let ectx : Ixon.Eval.EvalCtx :=
    { resolve, blobs := config.blobs, natBlock := config.natBlock }
  -- the artifact of record: the strict pipeline eraser (split
  -- constructor spines already fail closed here)
  let eraseCtx : Erase.EraseCtx :=
    { resolve, blobs := config.blobs, natBlock := config.natBlock }
  let erasedDecls ←
    match Erase.eraseProgram eraseCtx constants eraseFuel with
    | .ok decls => pure decls
    | .error error => throw (.erase error)
  let ictx : IxIR0.Ctx := { env := IxIR0.Env.ofList erasedDecls }
  -- blocks carry no block-level judgment; everything else must certify
  let candidates := constants.filterMap fun entry =>
    match entry.2.info with
    | .muts _ => none
    | _ => some entry.1
  unless candidates.contains mainAddress do
    throw (.validate mainAddress "main address is not a certifiable declaration")
  let rounds := candidates.length + 1
  let certifiedTarget ←
    if constants.any (fun entry => entry.2.sharing.size > 0) then
      -- sharing-aware: coverage facts live on the inlined resolver
      match coveragePlan ectx.inlineSharing ictx validateFuel rounds [] []
          candidates with
      | .error (address, message) => throw (.validate address message)
      | .ok order =>
        match EraseValidator.certifySharedProgram ectx constants order
            eraseFuel validateFuel with
        | .error (.erase error) => throw (.erase error)
        | .error (.relation message) => throw (.validate mainAddress message)
        | .ok cert => pure cert.target
    else
      match coveragePlan ectx ictx validateFuel rounds [] [] candidates with
      | .error (address, message) => throw (.validate address message)
      | .ok order =>
        match EraseValidator.certifyProgram ectx constants order
            eraseFuel validateFuel with
        | .error (.erase error) => throw (.erase error)
        | .error (.relation message) => throw (.validate mainAddress message)
        | .ok cert => pure cert.target
  -- the certificate re-runs the (validator-configured) eraser; its
  -- recorded target must be exactly what this pipeline lowers
  unless certifiedTarget == erasedDecls do
    throw (.validate mainAddress
      "certified erasure differs from the compiled erasure")
  match IxIR1.Lower.lowerAll erasedDecls (.ref mainAddress) mainWorld lowerFuel with
  | .ok (targetDecls, main) =>
    pure { erasedDecls, targetDecls, main }
  | .error message => throw (.lower message)

/-! ## End-to-end integration fixture

A two-constructor `Box` block gives the first constructor a unique
result/field world and the second a shared result/field world. Its
identity-like recursor rebuilds either major with the shared constructor.
`dropFirst : Box →ᵃ Box →ω Box`
discards its affine first argument and returns its shared second one;
`main` constructs both boxes, calls `dropFirst`, then runs the block
recursor on the survivor.

The fixture forces all integration seams at once: the checker accepts
the mixed modes, the eraser emits a real recursor declaration, the
lowerer consumes that declaration, and the IxIR₁ runtime observes one
unique deep-free plus shared RC traffic. -/

section Guards

private def address (byte : UInt8) : Address := Address.replicate byte

private def aBlock := address 0x70
private def aBox := address 0x71
private def aCtor := address 0x72
private def aRec := address 0x73
private def aDropFirst := address 0x74
private def aMain := address 0x75
private def aEleven := address 0x76
private def aTwentyTwo := address 0x77
private def aSharedCtor := address 0x79

private def boxType : Ixon.Expr := .ref 0 #[]

private def boxInductive : Ixon.Inductive :=
  { isUnsafe := false, lvls := 0, params := 0, indices := 0
    typ := .sort 0
    ctors := #[
      { isUnsafe := false, lvls := 0, cidx := 0, params := 0, fields := 1
        typ := .all .affine .unique (.sort 0) (.recur 0 #[]) },
      { isUnsafe := false, lvls := 0, cidx := 1, params := 0, fields := 1
        typ := .all .many .shared (.sort 0) (.recur 0 #[]) }
    ] }

/-- `Box.rec box = Box.mk box.field`, deliberately nontrivial so the
lowered case body allocates a fresh shared result. -/
private def boxRecursor : Ixon.Recursor :=
  { k := false, isUnsafe := false, lvls := 0
    params := 0, indices := 0, motives := 0, minors := 0
    typ := .all .many .shared (.recur 0 #[]) (.recur 0 #[])
    rules := #[
      { fields := 1
        rhs := .lam .many (.sort 0) (.app (.ref 0 #[]) (.var 0)) },
      { fields := 1
        rhs := .lam .many (.sort 0) (.app (.ref 0 #[]) (.var 0)) }
    ] }

private def cBlock : Constant :=
  { info := .muts #[.indc boxInductive, .recr boxRecursor]
    sharing := #[], refs := #[aSharedCtor], univs := #[.zero] }

private def projection (info : Ixon.ConstantInfo) : Constant :=
  { info, sharing := #[], refs := #[], univs := #[] }

private def cBox :=
  projection (.iPrj { idx := 0, block := aBlock })

private def cCtor :=
  projection (.cPrj { idx := 0, cidx := 0, block := aBlock })

private def cSharedCtor :=
  projection (.cPrj { idx := 0, cidx := 1, block := aBlock })

private def cRec :=
  projection (.rPrj { idx := 1, block := aBlock })

private def dropFirstValue : Ixon.Expr :=
  .lam .affine boxType (.lam .many boxType (.var 0))

private def cDropFirst : Constant :=
  { info := .defn
      { kind := .defn, safety := .safe, lvls := 0
        typ := .all .affine .shared boxType
          (.all .many .shared boxType boxType)
        value := dropFirstValue }
    sharing := #[], refs := #[aBox], univs := #[.zero] }

private def boxOfNat (blobRef : UInt64) : Ixon.Expr :=
  .app (.ref 2 #[]) (.nat blobRef)

/-- Manufacture a checker-shared, computational Nat field without an
implicit freeze: projection is a shared borrow, and its temporary unique
box is lowered in the projection's shared demand. -/
private def sharedBoxOfNat (blobRef : UInt64) : Ixon.Expr :=
  .app (.ref 6 #[]) (.prj 0 0 (boxOfNat blobRef))

private def cMain : Constant :=
  { info := .defn
      { kind := .defn, safety := .safe, lvls := 0
        typ := .ref 0 #[]
        value := .app (.ref 3 #[])
          (.app (.app (.ref 1 #[]) (boxOfNat 4)) (sharedBoxOfNat 5)) }
    sharing := #[]
    refs := #[aBox, aDropFirst, aCtor, aRec, aEleven, aTwentyTwo,
      aSharedCtor]
    univs := #[.zero] }

private def constants : List (Address × Constant) :=
  [(aBlock, cBlock), (aBox, cBox), (aCtor, cCtor),
   (aSharedCtor, cSharedCtor), (aRec, cRec),
   (aDropFirst, cDropFirst), (aMain, cMain)]

private def blobs : Address → Option Ixon.Eval.Blob := fun a =>
  if a == aEleven then some (.natB 11)
  else if a == aTwentyTwo then some (.natB 22)
  else none

private def compiled : Except Error Artifact :=
  compile constants aMain { blobs }

/-- The source evaluator returns the box built from the second
argument, after rebuilding it through the recursor. -/
private def sourceAgrees : Bool :=
  let ctx : Ixon.Eval.EvalCtx := { resolve := resolverOf constants, blobs }
  let frame : Ixon.Eval.Frame := { refs := #[aMain] }
  match Ixon.Eval.evalClosed ctx frame (.ref 0 #[]) with
  | .ok (.ctorV block 0 1 [.litV (.natL 22)]) => block == aBlock
  | _ => false

/-- The actual erased recursor reaches IxIR₁ as a unary `case`
function; this is not a hand-written IxIR₀ recursor fixture. -/
private def recursorCrossesBothPasses : Bool :=
  match compiled with
  | .error _ => false
  | .ok artifact =>
    let member := Erase.memberAddr aBlock 1
    match artifact.erasedDecls.find? (fun entry => entry.1 == member),
        artifact.targetDecls.find? (fun entry => entry.1 == member) with
    | some (_, .recursor 0 false rules), some (_, .fn fn) =>
      rules.size == 2 && fn.arity == 1 &&
        match fn.body with
        | .case _ false alts => alts.size == 2
        | _ => false
    | _, _ => false

/-- Runtime result and cost facts for the composed pipeline. Before
releasing the result: two input boxes + one pap + one rebuilt box were
allocated; the unique input, pap, and shared major were reclaimed.
Releasing the result leaves an empty store. -/
private def targetAgrees : Bool :=
  match compiled with
  | .error _ => false
  | .ok artifact =>
    let ctx : IxIR1.Ctx := { decls := IxIR1.Env.ofList artifact.targetDecls }
    match IxIR1.runMain ctx artifact.main with
    | .ok (store, value@(.loc location)) =>
      let shape := match store.get? location with
        | some box =>
          match box.node with
          | .ctorN cid fields =>
            cid.block == aSharedCtor && cid.cidx == 1 &&
              fields.toList == [.lit (.nat 22)]
          | _ => false
        | none => false
      shape && store.allocs == 5 && store.frees == 4 &&
        store.rcops == 3 && store.live == 1 &&
        match IxIR1.dropVal ctx 100000 store value with
        | .ok released =>
          released.allocs == 5 && released.frees == 5 &&
            released.rcops == 4 && released.live == 0
        | .error _ => false
    | _ => false

/-- A double use of the affine parameter is stopped at the first
pipeline gate, before erasure or lowering can observe the program. -/
private def badDropFirst : Constant :=
  { cDropFirst with
    info := .defn
      { kind := .defn, safety := .safe, lvls := 0
        typ := .all .affine .shared boxType
          (.all .many .shared boxType boxType)
        value := .lam .affine boxType
          (.lam .many boxType (.app (.var 1) (.var 1))) } }

private def rejectsBadUsage : Bool :=
  let bad := constants.map fun entry =>
    if entry.1 == aDropFirst then (aDropFirst, badDropFirst) else entry
  match compile bad aMain { blobs } with
  | .error (.usage address (.binderCovers .affine .many)) =>
    address == aDropFirst
  | _ => false

#guard sourceAgrees
#guard recursorCrossesBothPasses
#guard targetAgrees
#guard rejectsBadUsage

/-! ### The validated entry point

The same mixed-mode/add fixture must compile identically through
`compileValidated` (every constant of the fixture is inside the
validator's fragment), and one out-of-fragment declaration must flip
the verdict between the two entry points. -/

private def validated : Except Error Artifact :=
  compileValidated constants aMain { blobs }

/-- `compileValidated` reproduces `compile` on the in-fragment
fixture: the same erased declarations, the same target addresses, and
the same runtime result and cost facts as `targetAgrees` pins. -/
private def validatedAgrees : Bool :=
  match compiled, validated with
  | .ok direct, .ok gated =>
    direct.erasedDecls == gated.erasedDecls &&
    direct.targetDecls.map (·.1) == gated.targetDecls.map (·.1) &&
    (let ctx : IxIR1.Ctx := { decls := IxIR1.Env.ofList gated.targetDecls }
     match IxIR1.runMain ctx gated.main with
     | .ok (store, .loc location) =>
       (match store.get? location with
        | some box =>
          match box.node with
          | .ctorN cid fields =>
            cid.block == aSharedCtor && cid.cidx == 1 &&
              fields.toList == [.lit (.nat 22)]
          | _ => false
        | none => false) &&
       store.allocs == 5 && store.frees == 4 && store.rcops == 3 &&
       store.live == 1
     | _ => false)
  | _, _ => false

/-- An axiom is UsageCheck-clean and erases to an extern, so the
unvalidated pipeline accepts it — but the validator has no `Covered`
judgment for axioms, so the gated pipeline must fail closed, naming
the axiom and the validator's own diagnostic. -/
private def aGhostAxiom := address 0x78

private def cGhostAxiom : Constant :=
  { info := .axio { isUnsafe := false, lvls := 0, typ := .sort 0 }
    sharing := #[], refs := #[], univs := #[] }

private def outOfFragment : List (Address × Constant) :=
  constants ++ [(aGhostAxiom, cGhostAxiom)]

private def acceptsOutOfFragment : Bool :=
  match compile outOfFragment aMain { blobs } with
  | .ok _ => true
  | .error _ => false

private def rejectsOutOfFragment : Bool :=
  match compileValidated outOfFragment aMain { blobs } with
  | .error (.validate rejected message) =>
    rejected == aGhostAxiom &&
      message == "constant kind is outside the current Covered fragment"
  | _ => false

#guard validatedAgrees
#guard acceptsOutOfFragment
#guard rejectsOutOfFragment

end Guards

end Compilatrix.Pipeline
