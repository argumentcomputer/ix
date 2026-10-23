/-
  Ix.AuxGen.Oracle: the IxC oracle AuxGen's `.below` asks, as closures over
  Lean terms (AuxGen on IxC, M2a and M2b; AUXGEN-IXC §3.2–§3.3; the plan is
  `auxgen-m2.md`).

  ## Why closures

  The oracle answers `.below`'s level questions in IxC Source mode, over a
  snapshot of the drivers' Source service (`Ix.AuxGen.Source`) with the
  block's own canonical flat block installed. Its implementation
  (`Ix.AuxGen.Ixc`) runs IxC's cached checker. AuxGen asks it through this
  module's two object types, whose operations are closures over Lean terms
  and levels only:
  * **The compile environment holds it.** The wave fold
    (`Ix.CompileM.compileEnvFoldWithSource`) gives each block's aux tail its
    oracle through `CompileEnv.auxOracle`. `Ix.CompileM` cannot import IxC's kernel
    or the Source ingress: the kernel would make every IxC edit rebuild the
    compiler, and `Ix.LeanIngress.Expr` would enter the compiled-code
    audit's scope (`IxSharingVerify/Audit/CompiledCode.lean`). This module
    imports only `Ix.Environment` and AuxGen's data (`Ix.AuxGen.Types`, and
    `Ix.AuxGen.Report`, which imports only `Ix.Environment`).
  * **AuxGen asks no more than these.** AuxGen's IxC arm
    (`Ix.AuxGen.AuxKernel.ixc`) only calls the closures; the fold builds
    them (`Ix.AuxGen.Ixc.oracleOfRun`), so `Ix.Cert.compile` reaches IxC's
    checker through the fold (`Ix/Cert/RuntimeAudit.lean`), not through
    AuxGen.

  ## The objects

  * `OracleScope`: a local context, as an object. `getLevel` answers the sort
    level of a type in it, spelled as `Ix.Tc` would have built it, and says
    whether the `inferAppType` fast path gave it. `push` and `pop` return the
    context after them. The context a query leaves (its memo state) is
    returned too; AuxGen's scope values do not thread it back, so a query
    starts from the memo state of the last `push`.
  * `AuxOracle`: one block's oracle. `newScope` opens a context; `withFlat`
    installs the block's own canonical flat block when its layout is not
    Lean's (`Ix.AuxGen.Flat.needed`), and returns the oracle over the
    environment after it (`none`: Lean's layout, nothing to install).

  Both are built by structural recursion on a fuel bound
  (`Ix.AuxGen.Ixc.ofScope`, `Ix.AuxGen.Ixc.oracleOf`). An operation past the
  bound is a refusal, so the builders are total.
-/
module
public import Ix.Environment
public import Ix.AuxGen.Types
public import Ix.AuxGen.Report
public section

namespace Ix.AuxGen

/-- How AuxGen M2's IxC arm uses IxC's answers to `.below`'s level questions.
`Ix.Tc` stays the kernel of every other generator. -/
inductive IxcMode where
  /-- Both kernels answer; `Ix.Tc`'s answer is used, and the two are
  compared. The compile is `Ix.Tc`'s, by construction. -/
  | shadow
  /-- IxC answers first; `Ix.Tc` is asked a question only where IxC refuses it,
  and its answer is used there. Production's mode, for safe blocks: IxC's
  answers are the compile's wherever IxC answers, and a Source coverage gap
  (a selected closure without what Source mode needs) still compiles. Lazy
  since AuxGen M3 (`fallbackEager` was M2b's): `Ix.Tc`'s scopes are still
  opened, pushed and popped, but it faults in only what its answers behind a
  refusal need. Adopted on equal bytes with `fallbackEager` on the fixtures,
  Init+Std and Mathlib (`auxgen-m3.md` §11). -/
  | fallback
  /-- IxC alone answers the routed questions; a refusal fails the block.
  `Ix.Tc` is not asked them. Not production's until Source mode covers every
  input the compiler takes (closures included). -/
  | failClosed
  /-- Both kernels answer every question; IxC's answer is used where IxC
  answers, `Ix.Tc`'s where it refuses (AuxGen M2b's production mode; a
  measurement since M3). `Ix.Tc`'s environment evolves as on the `Ix.Tc`
  arm. -/
  | fallbackEager
  deriving BEq, Inhabited, Repr

namespace IxcMode

def ofString? : String → Option IxcMode
  | "shadow" => some .shadow
  | "fallback" => some .fallback
  | "fallbackEager" => some .fallbackEager
  | "failClosed" => some .failClosed
  | _ => none

instance : ToString IxcMode where
  toString
    | .shadow => "shadow"
    | .fallback => "fallback"
    | .fallbackEager => "fallbackEager"
    | .failClosed => "failClosed"

end IxcMode

/-- **How a named `whnf` was answered** (AuxGen M4). -/
inductive WhnfHow where
  /-- the head is syntactically stuck (a free variable, a sort, a `∀`, a
  literal, an unapplied `λ`, or an inductive, constructor, axiom, opaque or
  `Quot` head): its own whnf, and the service is not asked -/
  | stuck
  /-- IxC did not reduce it -/
  | same
  /-- IxC reduced it, and the named replay reproduced IxC's result -/
  | replayed
  /-- a `λ` applied at the head whose syntactic β-reduct has a stuck head
  (AuxGen M5c): that reduct, spelled as the named replay spells it, and the
  service is not asked -/
  | beta
  deriving BEq, Inhabited, Repr

/-- **What Source mode said of a block's canonical recursors** (AuxGen M4c):
the verdict of `AuxKernel.checkCanonicalBlock`, which a safe block's aux tail
runs right after generating its recursors when they are on IxC. The wave fold
records it per block, by the block's canonical key
(`Ix.CompileM.CompileEnv.auxReport`). -/
inductive CanonicalVerdict where
  /-- the block's layout is not Lean's: its canonical flat block, the generated
  recursors included, installed in Source mode (IxC's install is the check) -/
  | installed
  /-- the canonical flat block refused by Source mode, and why (`fallback`
  then keeps `Ix.Tc`'s answers for the block's tail) -/
  | refused (why : String)
  /-- the block's layout is Lean's: each of its `n` generated recursors equals
  Lean's own, whose acceptance is the input's -/
  | leanSame (n : Nat)
  /-- the block's layout is Lean's, and a generated recursor differs from
  Lean's own (the first one, named) -/
  | leanDiffer (first : String)
  deriving BEq, Inhabited, Repr

/-- **The canonical verdicts in summary** (AuxGen M4c), as the compile report
prints them. -/
structure CanonicalSummary where
  /-- non-Lean layouts: canonical flat blocks installed, and refused -/
  installed : Nat := 0
  refused : Nat := 0
  /-- Lean layouts: the blocks whose generated recursors all equal Lean's own,
  those recursors, and the blocks with one that differs -/
  leanSame : Nat := 0
  leanRecursors : Nat := 0
  leanDiffer : Nat := 0
  /-- the refusals and differences by block key, in `Ix.nameCompare` order:
  the first `CanonicalSummary.cap` -/
  findings : Array (Name × String) := #[]
  deriving Inhabited, BEq

namespace CanonicalSummary

/-- How many findings a summary names. -/
def cap : Nat := 64

/-- The summary of the verdicts, by block key. -/
def ofArray (verdicts : Array (Name × CanonicalVerdict)) : CanonicalSummary := Id.run do
  let mut s : CanonicalSummary := {}
  let mut findings : Array (Name × String) := #[]
  for (key, v) in verdicts do
    match v with
    | .installed => s := { s with installed := s.installed + 1 }
    | .refused why =>
      s := { s with refused := s.refused + 1 }
      findings := findings.push (key, s!"flat block refused: {why}")
    | .leanSame n =>
      s := { s with leanSame := s.leanSame + 1, leanRecursors := s.leanRecursors + n }
    | .leanDiffer first =>
      s := { s with leanDiffer := s.leanDiffer + 1 }
      findings := findings.push (key, s!"recursor differs from Lean's: {first}")
  let sorted := findings.qsort fun a b => Ix.nameCompare a.1 b.1 == .lt
  return { s with findings := sorted.extract 0 cap }

/-- One line. -/
def line (s : CanonicalSummary) : String :=
  s!"{s.installed} flat blocks installed, {s.refused} refused; {s.leanSame} Lean-layout blocks \
    with all {s.leanRecursors} recursors equal to Lean's, {s.leanDiffer} with one that differs"

end CanonicalSummary

/-- **An IxC refusal that stopped a tail under `failClosed`** (AuxGen M5c): the
generator's scope (its route and depth, or the install), the question asked in
it, and IxC's reason. The driver names the block (`Ix.CompileM.runAuxTail`). -/
structure IxcRefusal where
  scope : String
  question : String
  reason : String
  deriving Inhabited, BEq

/-- The refusal as the failure report names it. -/
def IxcRefusal.render (r : IxcRefusal) : String :=
  s!"IxC refused {r.question} in {r.scope}: {r.reason}"

/-- **What a block's aux tail reports** (AuxGen M4c; M5 adds its generated
auxiliaries' acceptance), carried in the block's state
(`Ix.CompileM.BlockState.auxReport`) and merged into the compile's
(`CompileReport.addBlock`). No byte depends on it. -/
structure BlockReport where
  /-- the canonical-block check's verdict (`AuxKernel.checkCanonicalBlock`),
  when it ran -/
  canonical : Option CanonicalVerdict := none
  /-- AuxGen M5: the auxiliaries the tail generated, with their kinds -/
  generated : Array (Name × GeneratedKind) := #[]
  /-- AuxGen M5: the verdict on each auxiliary the tail checked: `accepted`,
  `refused` with Source mode's reason, or `exempt` (blocked behind an unsafe
  constant) -/
  admitted : Array (Name × AuxVerdict) := #[]
  /-- AuxGen M5: why the tail's auxiliaries are outside every statement (an
  unsafe block), if they are -/
  exempt : Option String := none
  /-- AuxGen M5: the generated auxiliaries Pass 3 moved to display names (a
  changed block's), with the names they are published at -/
  display : Array (Name × Name) := #[]
  /-- AuxGen M5c: the IxC refusal that stopped the tail under `failClosed`,
  written where IxC refused, before the throw (the block state survives it), so
  the driver tells an IxC refusal from any other failure -/
  refusal : Option IxcRefusal := none
  /-- AuxGen M5c: why Source mode does not accept the block, when its tail
  stopped on an IxC refusal and re-ran on `fallback` (`AuxOracle.retry`) -/
  retried : Option String := none
  deriving Inhabited

/-- **AuxGen's part of the compile report** (AuxGen M4c and M5), merged from
the blocks that compile, in the fold's order (`Ix.CompileM.CompileEnv.auxReport`,
`mergeCompiledBlock`), and from the driver's original-form promotions
(`addIdentity`). Not serialized: no byte depends on it. -/
structure CompileReport where
  /-- each block's canonical-block verdict, by the block's canonical key -/
  canonical : Array (Name × CanonicalVerdict) := #[]
  /-- AuxGen M5: the facts of the acceptance table (`AuxTable.ofFacts`) -/
  generated : Array (Name × GeneratedKind) := #[]
  admitted : Array (Name × AuxVerdict) := #[]
  exempt : Array (Name × String) := #[]
  /-- AuxGen M5 and B9d: each promoted name, whether its published record is
  byte-identical to its original form's, and that record's address (the
  `Named.addr` the driver compared). A name can have more than one row
  (`IdentityStats`) -/
  identity : Array (Name × Bool × Address) := #[]
  display : Array (Name × Name) := #[]
  /-- AuxGen M5c: the blocks whose tail re-ran on `fallback` (not accepted by
  Source mode), by canonical key, with the reason and the block's generated
  auxiliaries -/
  retried : Array (Name × String × Array Name) := #[]
  deriving Inhabited

/-- A compiled block's report merged in, under the block's canonical key. -/
def CompileReport.addBlock (r : CompileReport) (key : Name) (b : BlockReport) : CompileReport :=
  let r := match b.canonical with
    | some verdict => { r with canonical := r.canonical.push (key, verdict) }
    | none => r
  let r := match b.retried with
    | some why => { r with retried := r.retried.push (key, why, b.generated.map (·.1)) }
    | none => r
  let r := if b.generated.isEmpty then r else { r with generated := r.generated ++ b.generated }
  let r := if b.admitted.isEmpty then r else { r with admitted := r.admitted ++ b.admitted }
  let r := if b.display.isEmpty then r else { r with display := r.display ++ b.display }
  match b.exempt with
  | some why => { r with exempt := r.exempt ++ b.generated.map fun (n, _) => (n, why) }
  | none => r

/-- AuxGen M5: the driver's byte comparisons at an original-form promotion
merged in, each with the compared record's address (B9d). -/
def CompileReport.addIdentity (r : CompileReport) (same : Array (Name × Bool × Address)) :
    CompileReport :=
  if same.isEmpty then r else { r with identity := r.identity ++ same }

/-- AuxGen B9d: the identity rows against the artifact's final `named`
(`published?`, a name's final address). -/
def CompileReport.identityStats (r : CompileReport) (published? : Name → Option Address) :
    IdentityStats :=
  Ix.AuxGen.identityStats r.identity published?

/-- The canonical-block verdicts in summary. -/
def CompileReport.canonicalSummary (r : CompileReport) : CanonicalSummary :=
  CanonicalSummary.ofArray r.canonical

/-- **The acceptance table** (AuxGen M5, `Ix.AuxGen.AuxTable`): one row per
promoted name and per displayed auxiliary of a changed block, sorted by
`Ix.Name.cmpRaw` (Pass 3's images under Lean names have none, by design).
Computed from the gathered facts; a consumer computes it once. -/
def CompileReport.table (r : CompileReport) : AuxTable :=
  AuxTable.ofFacts r.identity r.generated r.admitted r.exempt r.display

/-- **A local context IxC answers in**, as an object: each operation returns
the context after it. Free variables are named by their `LocalDecl.fvarName`
(`Ix.AuxGen.LocalDecl`), level parameters by their names.

`mk getLevel push pop infer whnf isDefEq whnfNamed`:
* `getLevel ty`: the sort level of the type `ty` in the context, spelled as
  `Ix.Tc` builds levels; whether the `inferAppType` fast path gave it; the
  context after the query;
* `push locals`: the context with a telescope pushed, `(fvarName, domain)`,
  outermost first, each domain over the context before it;
* `pop n`: the context with the most recently pushed `n` locals popped;
* `infer e`, `whnf e`: the type, the weak head normal form of `e` in the
  context, **decision-grade** (AuxGen M3): the result denotes the right
  term over the context, but its binder names are anonymous; AuxGen reads
  such results only to decide (`.brecOn.eq`'s unit-like test), never emits
  them;
* `isDefEq a b`: definitional equality in the context;
* `whnfNamed e`: the weak head normal form of `e` **with names** (AuxGen
  M4), for the recursor generator, whose `whnf` results reach generated
  binder names: the input itself, mdata dropped and levels spelled as
  `Ix.Tc` builds them, when nothing reduces; otherwise the **named
  replay** (delta with the Lean definition, β, `let`, the same spelling),
  accepted only when it ingresses to IxC's result; how it was answered. -/
inductive OracleScope where
  | mk (getLevel : Expr → Except String (Level × Bool × OracleScope))
      (push : Array (Name × Expr) → Except String OracleScope)
      (pop : Nat → Except String OracleScope)
      (infer : Expr → Except String (Expr × OracleScope))
      (whnf : Expr → Except String (Expr × OracleScope))
      (isDefEq : Expr → Expr → Except String (Bool × OracleScope))
      (whnfNamed : Expr → Except String (Expr × WhnfHow × OracleScope))

namespace OracleScope

def getLevel : OracleScope → Expr → Except String (Level × Bool × OracleScope)
  | .mk f _ _ _ _ _ _ => f

def push : OracleScope → Array (Name × Expr) → Except String OracleScope
  | .mk _ f _ _ _ _ _ => f

def pop : OracleScope → Nat → Except String OracleScope
  | .mk _ _ f _ _ _ _ => f

def infer : OracleScope → Expr → Except String (Expr × OracleScope)
  | .mk _ _ _ f _ _ _ => f

def whnf : OracleScope → Expr → Except String (Expr × OracleScope)
  | .mk _ _ _ _ f _ _ => f

def isDefEq : OracleScope → Expr → Expr → Except String (Bool × OracleScope)
  | .mk _ _ _ _ _ f _ => f

def whnfNamed : OracleScope → Expr → Except String (Expr × WhnfHow × OracleScope)
  | .mk _ _ _ _ _ _ f => f

end OracleScope

/-- **A generated declaration for Source acceptance** (AuxGen M5): a definition
or a theorem (`thm`), checked under its fresh name through σ; or a family of
inductives with their constructors and their generated recursors, installed
as a block under fresh names (a regenerated Prop-level `.below` family). -/
inductive GeneratedDecl where
  | defn (name : Name) (levelParams : Array Name) (type value : Expr) (thm : Bool)
  | family (types : Array (InductiveVal × Array ConstructorVal))
      (recs : Array (Name × RecursorVal))
  deriving Inhabited

/-- **One block's IxC oracle** (AuxGen M2a).

`mk mode trace newScope withFlat admitBelow recursors asked newLazyScope admit blockStatus retry
  withFamily`:
* `mode`: how AuxGen uses the answers;
* `trace`: whether the tail traces its counts (the measurement modes);
* `newScope lps locals`: a context over the level parameters `lps` and the
  outer locals `(fvarName, domain)`, outermost first;
* `withFlat classes originalAll canonicalRecs`: the block's own canonical
  flat block installed, from its canonical classes (restricted to Lean's
  `all`), Lean's `all` and its canonical recursors: the oracle after it, or
  `none` when the block's layout is Lean's and nothing is installed;
* `admitBelow defs`: the block's generated Type-level `.below` definitions
  made visible to later questions (AuxGen M3; the `AuxKernel` contract's
  clause 9), each admitted through σ under its fresh name: the oracle after
  them, and how many were admitted and refused. (A Prop-level family is not
  admitted: the Prop-level `.brecOn` asks the kernel nothing.)
* `recursors`: whether the recursor generator and the elimination decision
  ask IxC (AuxGen M4a as a measurement; production's since M4b);
* `asked`: whether the drivers' run-ahead asked for the block (a block it
  did not ask for folds its groups on its own copy at its first question);
* `newLazyScope overlay lps locals`: `newScope`, lazily (AuxGen M4): nothing
  is asked of the service until a question escapes the fast paths (the
  `inferAppType` level, a syntactically stuck `whnf`, after syntactic β-steps
  at the head), and a refusal surfaces at that question. The fast paths read
  `overlay` before the input's declarations (AuxGen M5c): the recursor
  generator's overlay, where a nested block's synthetic auxiliaries
  (`<all0>._nested.<Ext>_N`) live, so they are stuck inductives there, as
  for `Ix.Tc`; the service never sees them.
* `admit decls`: the generated declarations accepted by Source mode in
  order, each later one seeing the earlier ones through σ (AuxGen M5): the
  oracle after them, and each declaration's verdict (`none` accepted, `some`
  the reason it was refused; a refused declaration is not installed); an
  error when the oracle has no service.
* `blockStatus ()`: why the block's own groups are not accepted in Source
  mode, if they are not (refused, blocked behind a refused group with that
  group's reason, or not folded; AuxGen M5b): the block's input is then outside
  `SourceAccepts`, so its auxiliaries are exempt.
* `retry`: the block's oracle in `fallback` over the same service (AuxGen
  M5c): a block Source mode does not accept, whose tail stopped on an IxC
  refusal under `failClosed`, re-runs over it. `none` on the oracles an install
  returns.
* `withFamily types` (M7 Q1): a family's types and constructors (a regenerated
  Prop-level `.below` family, the block's or an unsafe block's), with no
  recursors, installed typing only under fresh names through σ on the
  oracle's own service copy: the oracle over it, whose scopes answer with the
  family in view, so AuxGen's generator can build its recursors. No status
  and no verdict: `admit`'s `.family` gives the family's.

An unsafe block's oracle (its groups installed by the tier, M7 Q1) answers
over the tier's answer view, where tier definitions unfold and the block's
recursors fire, as Lean's kernel answers; `withFlat`, `admitBelow` and
`admit` install through the tier; `blockStatus` says it is an unsafe block. -/
inductive AuxOracle where
  | mk (mode : IxcMode) (trace : Bool)
      (newScope : Array Name → Array (Name × Expr) → Except String OracleScope)
      (withFlat : Array (Array Name) → Array Name → Array (Name × RecursorVal) →
        Except String (Option AuxOracle))
      (admitBelow : Array BelowDef → Except String (AuxOracle × Nat × Nat))
      (recursors asked : Bool)
      (newLazyScope : (Name → Option ConstantInfo) → Array Name → Array (Name × Expr) →
        OracleScope)
      (admit : Array GeneratedDecl → Except String (AuxOracle × Array (Name × Option String)))
      (blockStatus : Unit → Option String)
      (retry : Option AuxOracle)
      (withFamily : Array (InductiveVal × Array ConstructorVal) → Except String AuxOracle)

/-- An original source owner's capability, fixed for one compilation input.
Local installs return private successors; the provider's base stays immutable. -/
abbrev SourceFamilyOracle := Name → Except String AuxOracle

namespace AuxOracle

def mode : AuxOracle → IxcMode
  | .mk m _ _ _ _ _ _ _ _ _ _ _ => m

def trace : AuxOracle → Bool
  | .mk _ t _ _ _ _ _ _ _ _ _ _ => t

def newScope : AuxOracle → Array Name → Array (Name × Expr) → Except String OracleScope
  | .mk _ _ f _ _ _ _ _ _ _ _ _ => f

def withFlat : AuxOracle → Array (Array Name) → Array Name → Array (Name × RecursorVal) →
    Except String (Option AuxOracle)
  | .mk _ _ _ f _ _ _ _ _ _ _ _ => f

def admitBelow : AuxOracle → Array BelowDef → Except String (AuxOracle × Nat × Nat)
  | .mk _ _ _ _ f _ _ _ _ _ _ _ => f

def recursors : AuxOracle → Bool
  | .mk _ _ _ _ _ r _ _ _ _ _ _ => r

def asked : AuxOracle → Bool
  | .mk _ _ _ _ _ _ a _ _ _ _ _ => a

def newLazyScope : AuxOracle → (Name → Option ConstantInfo) → Array Name →
    Array (Name × Expr) → OracleScope
  | .mk _ _ _ _ _ _ _ f _ _ _ _ => f

def admit : AuxOracle → Array GeneratedDecl → Except String (AuxOracle × Array (Name × Option String))
  | .mk _ _ _ _ _ _ _ _ f _ _ _ => f

def blockStatus : AuxOracle → Unit → Option String
  | .mk _ _ _ _ _ _ _ _ _ f _ _ => f

def retry : AuxOracle → Option AuxOracle
  | .mk _ _ _ _ _ _ _ _ _ _ f _ => f

def withFamily : AuxOracle → Array (InductiveVal × Array ConstructorVal) → Except String AuxOracle
  | .mk _ _ _ _ _ _ _ _ _ _ _ f => f

/-- The block status of an unsafe block whose groups the service's tier
installed (M7 Q1; `Ix.AuxGen.Ixc.blockStatus?`). -/
def tierBlockStatus : String := "an unsafe block (tier-installed)"

end AuxOracle

end Ix.AuxGen

end
