import Ix.Compiler.IxIR1.Lower
import Ix.Compiler.IxIR1.Readdress

/-!
# Content-addressed IxIR₁ lowering boundary

`Lower.lowerAllAction` remains the theorem-facing compiler action: generated
lambdas and constructor wrappers carry fresh transient names while their
bodies are being assembled.  This module consumes its final state and runs
`Readdress.run`, so no transient generated name escapes through the production
artifact boundary.

Keeping the boundary separate is also operationally necessary while BLAKE3 is
native: the extensive pure lowering `#guard` corpus can continue to elaborate,
whereas this post-pass runs in the compiled pipeline and test executable.
-/

namespace Ix.Compiler.IxIR1.Lower

/-- Recover the source-backed prefix from the raw whole-program result and
the final generated-declaration suffix.  Successful lowering results have
exactly this suffix; exposing the helper lets the semantic companion state
the post-pass call without unfolding the production wrapper. -/
def sourcePrefix
    (raw generated : List (Ixon.Address × Decl)) :
    List (Ixon.Address × Decl) :=
  raw.take (raw.length - generated.length)

@[simp] theorem sourcePrefix_append
    (source generated : List (Ixon.Address × Decl)) :
    sourcePrefix (source ++ generated) generated = source := by
  simp [sourcePrefix]

private def finishAddressing
    (reserved : List Ixon.Address)
    (run : EStateM.Result String LowSt
      (List (Ixon.Address × Decl) × Code)) :
    Except String Readdress.Result :=
  match run with
  | .error message _ => .error message
  | .ok (raw, main) state =>
      Readdress.runProtected reserved
        (sourcePrefix raw state.extra) state.extra main

/-- Lower with the transparent source environment, then replace every
generated temporary name by the content address of its finished declaration.
The result retains the complete old-to-new provenance map. -/
def lowerAllAddressed (decls : List (Ixon.Address × IxIR0.Decl))
    (main : IxIR0.Expr) (mainW : Ixon.Owned := .shared)
    (fuel : Nat := 10000) : Except String Readdress.Result :=
  finishAddressing (decls.map Prod.fst)
    ((lowerAllAction decls main mainW fuel).run {})

/-- Invert a successful production boundary once the theorem-facing raw
compiler run is known.  This is the exact `Readdress.run` invocation hidden
by `lowerAllAddressed`; no evaluator or hashing property is assumed here. -/
theorem readdress_run_of_lowerAllAddressed_eq_ok
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainW : Ixon.Owned} {fuel : Nat}
    {raw : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : Readdress.Result}
    (hlower : (lowerAllAction decls main mainW fuel).run {} =
      .ok (raw, mainCode) finalState)
    (hresult : lowerAllAddressed decls main mainW fuel = .ok result) :
    Readdress.runProtected (decls.map Prod.fst)
        (sourcePrefix raw finalState.extra) finalState.extra mainCode =
      .ok result := by
  simpa only [lowerAllAddressed, finishAddressing, hlower] using hresult

/-- Indexed-source variant used by the production pipeline. -/
def lowerAllIndexedAddressed
    (decls : List (Ixon.Address × IxIR0.Decl))
    (main : IxIR0.Expr) (mainW : Ixon.Owned := .shared)
    (fuel : Nat := 10000) : Except String Readdress.Result :=
  finishAddressing (decls.map Prod.fst)
    ((lowerAllIndexedAction decls main mainW fuel).run {})

/-- Building the lookup index changes neither the transparent compiler action
nor the content-addressed production result. -/
theorem lowerAllIndexedAddressed_eq_lowerAllAddressed
    (decls : List (Ixon.Address × IxIR0.Decl)) (main : IxIR0.Expr)
    (mainW : Ixon.Owned) (fuel : Nat) :
    lowerAllIndexedAddressed decls main mainW fuel =
      lowerAllAddressed decls main mainW fuel := by
  simp only [lowerAllIndexedAddressed, lowerAllAddressed,
    lowerAllIndexedAction, lowerAllAction, IxIR0.Env.Index.toEnv_ofList]

/-- Indexed analogue of `readdress_run_of_lowerAllAddressed_eq_ok`. -/
theorem readdress_run_of_lowerAllIndexedAddressed_eq_ok
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainW : Ixon.Owned} {fuel : Nat}
    {raw : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : Readdress.Result}
    (hlower : (lowerAllIndexedAction decls main mainW fuel).run {} =
      .ok (raw, mainCode) finalState)
    (hresult : lowerAllIndexedAddressed decls main mainW fuel = .ok result) :
    Readdress.runProtected (decls.map Prod.fst)
        (sourcePrefix raw finalState.extra) finalState.extra mainCode =
      .ok result := by
  simpa only [lowerAllIndexedAddressed, finishAddressing, hlower] using
    hresult

end Ix.Compiler.IxIR1.Lower
