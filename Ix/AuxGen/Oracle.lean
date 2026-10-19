/-
  Ix.AuxGen.Oracle: the IxC oracle AuxGen's `.below` asks in AuxGen M2a's
  measurement mode, as closures over Lean terms (AuxGen on IxC, M2a;
  AUXGEN-IXC §3.2–§3.3; the plan is `auxgen-m2.md`).

  ## Why closures

  The oracle answers `.below`'s level questions in IxC Source mode, over a
  snapshot of the drivers' Source service (`Ix.AuxGen.Source`) with the
  block's own canonical flat block installed. Its implementation
  (`Ix.AuxGen.Ixc`) runs IxC's cached checker. AuxGen asks it through this
  module's two object types, whose operations are closures over Lean terms
  and levels only, for two reasons:
  * **The compile environment holds it.** The measurement fold
    (`Ix.CompileM.compileEnvFoldIxc`) gives each block's aux tail its oracle
    through `CompileEnv.auxOracle`. `Ix.CompileM` cannot import IxC's kernel
    or the Source ingress: the kernel would make every IxC edit rebuild the
    compiler, and `Ix.LeanIngress.Expr` would enter the compiled-code
    audit's scope (`IxSharingVerify/Audit/CompiledCode.lean`). This module
    imports only `Ix.Environment`.
  * **No production path reaches IxC through it.** AuxGen's IxC arm
    (`Ix.AuxGen.AuxKernel.ixc`) only calls these closures, and only the
    measurement fold and the tests build them. So the runtime closure of
    `Ix.Cert.compile` (`Ix/Cert/RuntimeAudit.lean`) reaches no oracle code.

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
public section

namespace Ix.AuxGen

/-- How AuxGen M2's IxC arm uses IxC's answers to `.below`'s level questions.
`Ix.Tc` stays the kernel of every other generator. -/
inductive IxcMode where
  /-- Both kernels answer; `Ix.Tc`'s answer is used, and the two are
  compared. The compile is `Ix.Tc`'s, by construction. -/
  | shadow
  /-- Both kernels answer; IxC's answer is used where IxC answers, `Ix.Tc`'s
  where it refuses. `Ix.Tc` still answers every query, so its environment
  evolves as in production (`Ix.Tc`'s later answers depend on what it has
  faulted in). -/
  | fallback
  /-- IxC alone answers `.below`'s questions; a refusal fails the block.
  `Ix.Tc` is not asked them. -/
  | failClosed
  deriving BEq, Inhabited, Repr

namespace IxcMode

def ofString? : String → Option IxcMode
  | "shadow" => some .shadow
  | "fallback" => some .fallback
  | "failClosed" => some .failClosed
  | _ => none

instance : ToString IxcMode where
  toString
    | .shadow => "shadow"
    | .fallback => "fallback"
    | .failClosed => "failClosed"

end IxcMode

/-- **A local context IxC answers in**, as an object: each operation returns
the context after it. Free variables are named by their `LocalDecl.fvarName`
(`Ix.AuxGen.LocalDecl`), level parameters by their names.

`mk getLevel push pop`:
* `getLevel ty`: the sort level of the type `ty` in the context, spelled as
  `Ix.Tc` builds levels; whether the `inferAppType` fast path gave it; the
  context after the query;
* `push locals`: the context with a telescope pushed, `(fvarName, domain)`,
  outermost first, each domain over the context before it;
* `pop n`: the context with the most recently pushed `n` locals popped. -/
inductive OracleScope where
  | mk (getLevel : Expr → Except String (Level × Bool × OracleScope))
      (push : Array (Name × Expr) → Except String OracleScope)
      (pop : Nat → Except String OracleScope)

namespace OracleScope

def getLevel : OracleScope → Expr → Except String (Level × Bool × OracleScope)
  | .mk f _ _ => f

def push : OracleScope → Array (Name × Expr) → Except String OracleScope
  | .mk _ f _ => f

def pop : OracleScope → Nat → Except String OracleScope
  | .mk _ _ f => f

end OracleScope

/-- **One block's IxC oracle** (AuxGen M2a).

`mk mode newScope withFlat`:
* `mode`: how AuxGen uses the answers;
* `newScope lps locals`: a context over the level parameters `lps` and the
  outer locals `(fvarName, domain)`, outermost first;
* `withFlat classes originalAll canonicalRecs`: the block's own canonical
  flat block installed, from its canonical classes (restricted to Lean's
  `all`), Lean's `all` and its canonical recursors: the oracle after it, or
  `none` when the block's layout is Lean's and nothing is installed. -/
inductive AuxOracle where
  | mk (mode : IxcMode)
      (newScope : Array Name → Array (Name × Expr) → Except String OracleScope)
      (withFlat : Array (Array Name) → Array Name → Array (Name × RecursorVal) →
        Except String (Option AuxOracle))

namespace AuxOracle

def mode : AuxOracle → IxcMode
  | .mk m _ _ => m

def newScope : AuxOracle → Array Name → Array (Name × Expr) → Except String OracleScope
  | .mk _ f _ => f

def withFlat : AuxOracle → Array (Array Name) → Array Name → Array (Name × RecursorVal) →
    Except String (Option AuxOracle)
  | .mk _ _ f => f

end AuxOracle

end Ix.AuxGen

end
