import Ix.Compiler.IxIR1.Lower
import Ix.Compiler.IxIR1.ReaddressAll

/-!
# Fully content-addressed IxIR₁ lowering boundary

The existing `LowerAddressed` boundary rekeys generated declarations while
retaining source function keys for its established proof interface.  This
companion consumes the same raw whole-pass output and applies
`ReaddressAll` across source and generated functions together.  Constructor
keys, which have no IxIR₁ declaration entry, are explicitly reserved;
extern declarations are retained as stable ABI artifacts by `ReaddressAll`.
-/

namespace Ix.Compiler.IxIR1.Lower

open Ix.Compiler.Ixon (Address Owned)

/-- Source identities used by constructor nodes but absent from the target
declaration environment. -/
def constructorIdentities
    (decls : List (Address × IxIR0.Decl)) : List Address :=
  decls.filterMap fun
    | (address, .ctor _ _) => some address
    | _ => none

private def finishFullAddressing
    (reserved : List Address)
    (lowered : EStateM.Result String LowSt
      (List (Address × Decl) × Code)) :
    Except String ReaddressAll.Result :=
  match lowered with
  | .error message _ => .error message
  | .ok (raw, main) _ => ReaddressAll.run reserved raw main

/-- Transparent-environment whole-program lowering followed by SCC-aware
source/generated function readdressing. -/
def lowerAllFullyAddressed
    (decls : List (Address × IxIR0.Decl))
    (main : IxIR0.Expr) (mainWorld : Owned := .shared)
    (fuel : Nat := 10000) : Except String ReaddressAll.Result :=
  finishFullAddressing (constructorIdentities decls)
    ((lowerAllAction decls main mainWorld fuel).run {})

/-- Indexed production analogue. -/
def lowerAllIndexedFullyAddressed
    (decls : List (Address × IxIR0.Decl))
    (main : IxIR0.Expr) (mainWorld : Owned := .shared)
    (fuel : Nat := 10000) : Except String ReaddressAll.Result :=
  finishFullAddressing (constructorIdentities decls)
    ((lowerAllIndexedAction decls main mainWorld fuel).run {})

/-- Proof-facing execution record for the production lowering boundary.
`lowerAllIndexedFullyAddressed` deliberately returns only the emitted graph;
this companion retains the exact raw declarations, main code, and final
compiler state consumed by the semantic theorems without running the lowerer
twice.  Proof fields are erased by code generation. -/
structure FullyAddressedTrace
    (decls : List (Address × IxIR0.Decl)) (main : IxIR0.Expr)
    (mainWorld : Owned) (fuel : Nat) where
  raw : List (Address × Decl)
  mainCode : Code
  finalState : LowSt
  result : ReaddressAll.Result
  lowerRun :
    (lowerAllIndexedAction decls main mainWorld fuel).run {} =
      .ok (raw, mainCode) finalState
  addressedRun :
    lowerAllIndexedFullyAddressed decls main mainWorld fuel = .ok result

/-- Execute indexed lowering and full SCC addressing once while preserving
the stateful run equation needed by whole-pass proofs. -/
def lowerAllIndexedFullyAddressedWithTrace
    (decls : List (Address × IxIR0.Decl))
    (main : IxIR0.Expr) (mainWorld : Owned := .shared)
    (fuel : Nat := 10000) :
    Except String (FullyAddressedTrace decls main mainWorld fuel) :=
  match hlower : (lowerAllIndexedAction decls main mainWorld fuel).run {} with
  | .error message _ => .error message
  | .ok (raw, mainCode) finalState =>
    match haddressed : ReaddressAll.run (constructorIdentities decls)
        raw mainCode with
    | .error message => .error message
    | .ok result =>
      .ok
        { raw, mainCode, finalState, result
          lowerRun := hlower
          addressedRun := by
            simp only [lowerAllIndexedFullyAddressed,
              finishFullAddressing, hlower, haddressed] }

theorem lowerAllIndexedFullyAddressed_eq_lowerAllFullyAddressed
    (decls : List (Address × IxIR0.Decl)) (main : IxIR0.Expr)
    (mainWorld : Owned) (fuel : Nat) :
    lowerAllIndexedFullyAddressed decls main mainWorld fuel =
      lowerAllFullyAddressed decls main mainWorld fuel := by
  simp only [lowerAllIndexedFullyAddressed, lowerAllFullyAddressed,
    lowerAllIndexedAction, lowerAllAction, IxIR0.Env.Index.toEnv_ofList]

/-- Expose the exact SCC pass hidden behind a successful raw compiler run. -/
theorem readdressAll_run_of_lowerAllFullyAddressed_eq_ok
    {decls : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {fuel : Nat}
    {raw : List (Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : ReaddressAll.Result}
    (hlower : (lowerAllAction decls main mainWorld fuel).run {} =
      .ok (raw, mainCode) finalState)
    (hresult : lowerAllFullyAddressed decls main mainWorld fuel =
      .ok result) :
    ReaddressAll.run (constructorIdentities decls) raw mainCode =
      .ok result := by
  simpa only [lowerAllFullyAddressed, finishFullAddressing, hlower] using
    hresult

theorem readdressAll_run_of_lowerAllIndexedFullyAddressed_eq_ok
    {decls : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {fuel : Nat}
    {raw : List (Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : ReaddressAll.Result}
    (hlower : (lowerAllIndexedAction decls main mainWorld fuel).run {} =
      .ok (raw, mainCode) finalState)
    (hresult : lowerAllIndexedFullyAddressed decls main mainWorld fuel =
      .ok result) :
    ReaddressAll.run (constructorIdentities decls) raw mainCode =
      .ok result := by
  simpa only [lowerAllIndexedFullyAddressed, finishFullAddressing, hlower]
    using hresult

end Ix.Compiler.IxIR1.Lower
