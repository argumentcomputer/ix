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
    imports only `Ix.Environment`.
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

/-- **What a block's aux tail reports** (AuxGen M4c; M5 adds its generated
auxiliaries' acceptance), carried in the block's state
(`Ix.CompileM.BlockState.auxReport`) and merged into the compile's
(`CompileReport.addBlock`). No byte depends on it. -/
structure BlockReport where
  /-- the canonical-block check's verdict (`AuxKernel.checkCanonicalBlock`),
  when it ran -/
  canonical : Option CanonicalVerdict := none
  deriving Inhabited

/-- **AuxGen's part of the compile report** (AuxGen M4c), merged from the
blocks that compile, in the fold's order (`Ix.CompileM.CompileEnv.auxReport`,
`mergeCompiledBlock`). Not serialized: no byte depends on it. -/
structure CompileReport where
  /-- each block's canonical-block verdict, by the block's canonical key -/
  canonical : Array (Name × CanonicalVerdict) := #[]
  deriving Inhabited

/-- A compiled block's report merged in, under the block's canonical key. -/
def CompileReport.addBlock (r : CompileReport) (key : Name) (b : BlockReport) : CompileReport :=
  match b.canonical with
  | some verdict => { r with canonical := r.canonical.push (key, verdict) }
  | none => r

/-- The canonical-block verdicts in summary. -/
def CompileReport.canonicalSummary (r : CompileReport) : CanonicalSummary :=
  CanonicalSummary.ofArray r.canonical

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

`mk mode trace newScope withFlat admitBelow recursors asked newLazyScope admit`:
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
* `newLazyScope lps locals`: `newScope`, lazily (AuxGen M4): nothing is
  asked of the service until a question escapes the fast paths (the
  `inferAppType` level, a syntactically stuck `whnf`), and a refusal
  surfaces at that question. 
* `admit decls`: the generated declarations accepted by Source mode in
  order, each later one seeing the earlier ones through σ (AuxGen M5): the
  oracle after them, and each declaration's verdict (`none` accepted, `some`
  the reason it was refused; a refused declaration is not installed); an
  error when the oracle has no service. -/
inductive AuxOracle where
  | mk (mode : IxcMode) (trace : Bool)
      (newScope : Array Name → Array (Name × Expr) → Except String OracleScope)
      (withFlat : Array (Array Name) → Array Name → Array (Name × RecursorVal) →
        Except String (Option AuxOracle))
      (admitBelow : Array BelowDef → Except String (AuxOracle × Nat × Nat))
      (recursors asked : Bool)
      (newLazyScope : Array Name → Array (Name × Expr) → OracleScope)
      (admit : Array GeneratedDecl → Except String (AuxOracle × Array (Name × Option String)))

namespace AuxOracle

def mode : AuxOracle → IxcMode
  | .mk m _ _ _ _ _ _ _ _ => m

def trace : AuxOracle → Bool
  | .mk _ t _ _ _ _ _ _ _ => t

def newScope : AuxOracle → Array Name → Array (Name × Expr) → Except String OracleScope
  | .mk _ _ f _ _ _ _ _ _ => f

def withFlat : AuxOracle → Array (Array Name) → Array Name → Array (Name × RecursorVal) →
    Except String (Option AuxOracle)
  | .mk _ _ _ f _ _ _ _ _ => f

def admitBelow : AuxOracle → Array BelowDef → Except String (AuxOracle × Nat × Nat)
  | .mk _ _ _ _ f _ _ _ _ => f

def recursors : AuxOracle → Bool
  | .mk _ _ _ _ _ r _ _ _ => r

def asked : AuxOracle → Bool
  | .mk _ _ _ _ _ _ a _ _ => a

def newLazyScope : AuxOracle → Array Name → Array (Name × Expr) → OracleScope
  | .mk _ _ _ _ _ _ _ f _ => f

def admit : AuxOracle → Array GeneratedDecl → Except String (AuxOracle × Array (Name × Option String))
  | .mk _ _ _ _ _ _ _ _ f => f

end AuxOracle

end Ix.AuxGen

end
