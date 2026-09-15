import Compilatrix.IxIR1.Lower
import Compilatrix.IxIR0.Examples

namespace Compilatrix.IxIR1.Lower

open Compilatrix.Ixon (Address Owned Uses)
open Compilatrix.IxIR0 (Literal)

/-- Target-side oracle mirroring the corpus ledger entry. -/
def tgtOracle : Address → List RVal → Option RVal := fun a args =>
  if a == IxIR0.Examples.natAddExt then
    match args with
    | [.lit (.nat m), .lit (.nat n)] => some (.lit (.nat (m + n)))
    | _ => none
  else none

/-- Pinned cross-IR stuck-message pairs (source, target) — every stuck
agreement the corpus exercises, by exact text. An unlisted pair counts
as divergence: extend the table deliberately when a new fixture
legitimately sticks on both sides. -/
def stuckPairs : List (String × String) :=
  [("application of a non-function value", "apply of a non-node value"),
   ("projection 5 out of bounds", "fetch field 5 out of range")]

/-- Deliberate error-agreement mapping between the two semantics
(`lowersErr`'s exactness, extended across IRs):

- `fuel` pairs only with `fuel` (a stuck side against a diverging side
  is a divergence, not agreement);
- unknown references pair by exact address;
- the IxIR₀ `oracleMissing` boundary pairs with the two ways IxIR₁
  refuses the *same* extern call: a `none` oracle answer on scalar
  arguments (surfaced as `unknownRef`, matched by address) or the
  scalar-only ABI's `mem` rejection of heap arguments (which the
  literals-only source oracle observes as a domain miss) — pinned to
  that exact ABI message;
- stuck messages pair only through `stuckPairs`;
- everything else — including IxIR₁ `mem` discipline faults, which
  have no source counterpart — disagrees. -/
def errAgree : IxIR0.Err → Err → Bool
  | .fuel, .fuel => true
  | .unknownRef a, .unknownRef b => a == b
  | .oracleMissing a, .unknownRef b => a == b
  | .oracleMissing _, .mem msg =>
    msg == "extern heap arguments require an ownership policy"
  | .stuck msg, .stuck msg' => stuckPairs.contains (msg, msg')
  | _, _ => false

/-- The differential check: lower the corpus + `e` (main at world
`mainW`), run both semantics; on success the readback trees must
agree AND releasing the result must leave the store empty
(leak-freedom of the inserted memory ops); on failure both sides must
fail with errors related by the `errAgree` mapping. No leak check runs
on error runs: the evaluator's `Except Err` aborts without returning a
store, so the state at an error is unobservable at this API (a
transactional evaluator would make it checkable; today only successful
runs carry a store to audit). -/
def diffExpr (e : IxIR0.Expr) (mainW : Owned := .shared)
    (runFuel : Nat := 100000) : Bool :=
  match lowerAllIndexed IxIR0.Examples.declList e mainW with
  | .error _ => false
  | .ok (ds, mainC) =>
    let targetIndex := Env.Index.ofList ds
    let tctx : Ctx := { decls := targetIndex.toEnv, oracle := tgtOracle }
    match IxIR0.Examples.ctx.run e runFuel, runMain tctx mainC runFuel with
    | .ok v, .ok (store, r) =>
      (match treeOfVal 1000 v, treeOfR store 1000 r with
       | some a, some b => Tree.agree a b
       | _, _ => false)
      && (match releaseResult tctx runFuel store r with
          | .ok s => s.live == 0
          | .error _ => false)
    | .error source, .error target => errAgree source target
    | _, _ => false

/-- Target-only run for counter guards. -/
def checkLowered (e : IxIR0.Expr) (mainW : Owned)
    (p : Store → RVal → Bool) : Bool :=
  match lowerAllIndexed IxIR0.Examples.declList e mainW with
  | .error _ => false
  | .ok (ds, mainC) =>
    let targetIndex := Env.Index.ofList ds
    match runMain { decls := targetIndex.toEnv, oracle := tgtOracle } mainC with
    | .ok (store, r) => p store r
    | .error _ => false

/-- The lowering statically rejects `e` at the given main world with
the expected diagnostic. Keeping the message in the assertion stops
one mode error from accidentally satisfying a guard for another. -/
def lowersErr (e : IxIR0.Expr) (mainW : Owned) (expected : String) : Bool :=
  match lowerAllIndexed IxIR0.Examples.declList e mainW with
  | .error msg => msg == expected
  | .ok _ => false

end Compilatrix.IxIR1.Lower
