import Ix.Compiler.IxIR2.Validate

/-!
# Executable IxIR₂ validator fixtures

These guards are intentionally small enough to audit by eye.  Together they
pin the accepted credit paths and the major fail-closed ownership boundaries.
-/

namespace Ix.Compiler.IxIR2.Validate.Examples

open Ix.Compiler.Ixon (Address Owned)
open Ix.Compiler.IxIR2

private def blockAddress : Address := Address.replicate 0x21
private def functionAddress : Address := Address.replicate 0x31
private def harnessAddress : Address := Address.replicate 0x32
private def externAddress : Address := Address.replicate 0x41
private def uniqueLayout : LayoutId := Address.replicate 0x51
private def sharedLayout : LayoutId := Address.replicate 0x52
private def otherLayout : LayoutId := Address.replicate 0x53

private def nodeCtor : CtorId :=
  { block := blockAddress, indIdx := 0, cidx := 0 }

private def otherCtor : CtorId :=
  { block := blockAddress, indIdx := 0, cidx := 1 }

private def schemas : Owned → CtorId → Option CtorSchema
  | .unique, cid =>
      if cid == nodeCtor then
        some { layout := uniqueLayout, fields := #[.unique] }
      else if cid == otherCtor then
        some { layout := otherLayout, fields := #[.unique] }
      else
        none
  | .shared, cid =>
      if cid == nodeCtor then
        some { layout := sharedLayout, fields := #[.shared] }
      else
        none

private def context : Context := { schemas }

private def unarySignature (world : Owned) : Signature :=
  { params := #[{ world, passing := .owned }]
    result := world
    papSafe := false }

private def nullarySignature (result : Owned := .shared) : Signature :=
  { params := #[], result, papSafe := false }

/-- Keep the inner ownership fixtures unary and auditably small while checking
them as genuine nullary-main programs. -/
private def closeFixture (program : Program) : Program :=
  match program.main.signature.params with
  | #[{ world, passing := .owned }] =>
      { declarations := (harnessAddress, .fn program.main) :: program.declarations
        main :=
          { signature := nullarySignature program.main.signature.result
            blocks := #[
              { valueParams := #[]
                creditParams := #[]
                instructions := #[
                  .alloc world nodeCtor #[.lit (.nat 0)],
                  .call harnessAddress #[.reg 0]]
                terminator := .ret (.reg 1) }] } }
  | _ => program

private def accepts (program : Program) : Bool :=
  match validate context (closeFixture program) with
  | .ok _ => true
  | .error _ => false

private def rejectsAs (violation : Violation) (program : Program) : Bool :=
  match validate context (closeFixture program) with
  | .error (.invalid _ actual _) => actual == violation
  | _ => false

/-! A complete owner transfer across an ordinary two-block edge. -/

private def simpleJump : Program :=
  { declarations := []
    main :=
      { signature := unarySignature .unique
        blocks := #[
          { valueParams := #[.owned .unique]
            creditParams := #[]
            instructions := #[]
            terminator := .jump
              { target := 1, values := #[.reg 0], credits := #[] } },
          { valueParams := #[.owned .unique]
            creditParams := #[]
            instructions := #[]
            terminator := .ret (.reg 0) }] } }

#guard accepts simpleJump

#guard match validate context simpleJump with
  | .error (.invalid _ .signature _) => true
  | _ => false

/-! Required credit: destructive take, exact-layout reuse, return. -/

private def requiredReuse : Program :=
  { declarations := []
    main :=
      { signature := unarySignature .unique
        blocks := #[
          { valueParams := #[.owned .unique]
            creditParams := #[]
            instructions := #[
              .takeUnique (.reg 0) nodeCtor,
              .allocWith 0 .unique nodeCtor #[.reg 1]]
            terminator := .ret (.reg 2) }] } }

#guard accepts requiredReuse

private def discardTakenCredit : Program :=
  { declarations := []
    main :=
      { signature := unarySignature .unique
        blocks := #[
          { valueParams := #[.owned .unique]
            creditParams := #[]
            instructions := #[
              .takeUnique (.reg 0) nodeCtor,
              .discardCredit 0]
            terminator := .ret (.reg 1) }] } }

#guard accepts discardTakenCredit

/-! Optional shared reset: the some branch refines to required, both paths
widen at the join, and `allocWith` consumes the joined optional credit. -/

private def optionalDiamond : Program :=
  { declarations := []
    main :=
      { signature := unarySignature .shared
        blocks := #[
          { valueParams := #[.owned .shared]
            creditParams := #[]
            instructions := #[.resetShared (.reg 0) nodeCtor]
            terminator := .branchCredit 0
              { target := 1, values := #[.reg 1], credits := #[0] }
              { target := 2, values := #[.reg 1], credits := #[0] } },
          { valueParams := #[.owned .shared]
            creditParams := #[.required sharedLayout]
            instructions := #[]
            terminator := .jump
              { target := 3, values := #[.reg 0], credits := #[0] } },
          { valueParams := #[.owned .shared]
            creditParams := #[.optional sharedLayout]
            instructions := #[]
            terminator := .jump
              { target := 3, values := #[.reg 0], credits := #[0] } },
          { valueParams := #[.owned .shared]
            creditParams := #[.optional sharedLayout]
            instructions := #[.allocWith 0 .shared nodeCtor #[.reg 0]]
            terminator := .ret (.reg 1) }] } }

#guard accepts optionalDiamond

/-! One dynamic IxIR₁ scrutinee can select a constructor edge or a peeled Nat
edge.  The successor block receives its implicit predecessor first. -/

private def combinedSwitch : Program :=
  { declarations := []
    main :=
      { signature := unarySignature .unique
        blocks := #[
          { valueParams := #[.owned .unique]
            creditParams := #[]
            instructions := #[]
            terminator := .switchValue (.reg 0)
              #[{ cid := nodeCtor
                  edge := { target := 1, values := #[.reg 0], credits := #[] } }]
              (some
                { zero := { target := 1, values := #[.reg 0], credits := #[] }
                  succ := { target := 2, values := #[.reg 0], credits := #[] } }) },
          { valueParams := #[.owned .unique]
            creditParams := #[]
            instructions := #[]
            terminator := .ret (.reg 0) },
          { valueParams := #[.scalar, .owned .unique]
            creditParams := #[]
            instructions := #[]
            terminator := .ret (.reg 1) }] } }

#guard accepts combinedSwitch

/-! Self calls use the containing signature, and tail-self transfer leaves no
local owner behind. -/

private def selfCall : Program :=
  { declarations := []
    main :=
      { signature := unarySignature .unique
        blocks := #[
          { valueParams := #[.owned .unique]
            creditParams := #[]
            instructions := #[.callSelf #[.reg 0]]
            terminator := .ret (.reg 1) }] } }

private def tailSelf : Program :=
  { declarations := []
    main :=
      { signature := unarySignature .unique
        blocks := #[
          { valueParams := #[.owned .unique]
            creditParams := #[]
            instructions := #[]
            terminator := .tailCallSelf #[.reg 0] }] } }

#guard accepts selfCall
#guard accepts tailSelf

private def loopAndTailSelf : Program :=
  { declarations := []
    main :=
      { signature := unarySignature .unique
        blocks := #[
          { valueParams := #[.owned .unique]
            creditParams := #[]
            instructions := #[]
            terminator := .jump
              { target := 1, values := #[.reg 0], credits := #[] } },
          { valueParams := #[.owned .unique]
            creditParams := #[]
            instructions := #[]
            terminator := .switchValue (.reg 0)
              #[{ cid := nodeCtor
                  edge := { target := 1, values := #[.reg 0], credits := #[] } }]
              (some
                { zero := { target := 2, values := #[.reg 0], credits := #[] }
                  succ := { target := 3, values := #[.reg 0], credits := #[] } }) },
          { valueParams := #[.owned .unique]
            creditParams := #[]
            instructions := #[]
            terminator := .tailCallSelf #[.reg 0] },
          { valueParams := #[.scalar, .owned .unique]
            creditParams := #[]
            instructions := #[]
            terminator := .tailCallSelf #[.reg 1] }] } }

#guard accepts loopAndTailSelf

private def borrowedCallee : Function :=
  { signature :=
      { params := #[{ world := .unique, passing := .borrowed }]
        result := .unique
        papSafe := false }
    blocks := #[
      { valueParams := #[.borrowed .unique .caller]
        creditParams := #[]
        instructions := #[]
        terminator := .ret (.lit (.nat 0)) }] }

private def directBorrowedCall : Program :=
  { declarations := [(functionAddress, .fn borrowedCallee)]
    main :=
      { signature := unarySignature .unique
        blocks := #[
          { valueParams := #[.owned .unique]
            creditParams := #[]
            instructions := #[
              .call functionAddress #[.reg 0],
              .dropUnique (.reg 0)]
            terminator := .ret (.reg 1) }] } }

#guard accepts directBorrowedCall

/-! The leaf sidecar is exact in owner, block, value, and constructor. -/

private def scalarLeafContext : Context :=
  { schemas
    scalarLeaves :=
      [{ owner := .declaration harnessAddress
         block := 0
         value := 0
         cid := nodeCtor }] }

private def scalarLeafFree : Program :=
  { declarations := []
    main :=
      { signature := unarySignature .unique
        blocks := #[
          { valueParams := #[.owned .unique]
            creditParams := #[]
            instructions := #[.freeUnique (.reg 0) nodeCtor]
            terminator := .ret (.lit (.nat 0)) }] } }

#guard match validate scalarLeafContext (closeFixture scalarLeafFree) with
  | .ok _ => true
  | .error _ => false

/-! ## Fail-closed fixtures -/

private def duplicateCredit : Program :=
  { declarations := []
    main :=
      { signature := unarySignature .unique
        blocks := #[
          { valueParams := #[.owned .unique]
            creditParams := #[]
            instructions := #[.takeUnique (.reg 0) nodeCtor]
            terminator := .jump
              { target := 1, values := #[.reg 1], credits := #[0, 0] } },
          { valueParams := #[.owned .unique]
            creditParams := #[.required uniqueLayout, .required uniqueLayout]
            instructions := #[.discardCredit 0, .discardCredit 1]
            terminator := .ret (.reg 0) }] } }

#guard rejectsAs .credit duplicateCredit

private def liveCreditAtReturn : Program :=
  { declarations := []
    main :=
      { signature := unarySignature .unique
        blocks := #[
          { valueParams := #[.owned .unique]
            creditParams := #[]
            instructions := #[.takeUnique (.reg 0) nodeCtor]
            terminator := .ret (.reg 1) }] } }

#guard rejectsAs .resources liveCreditAtReturn

private def liveCreditAtCall : Program :=
  { declarations :=
      [(functionAddress,
        .fn
          { signature := unarySignature .unique
            blocks := #[
              { valueParams := #[.owned .unique]
                creditParams := #[]
                instructions := #[]
                terminator := .ret (.reg 0) }] })]
    main :=
      { signature := unarySignature .unique
        blocks := #[
          { valueParams := #[.owned .unique]
            creditParams := #[]
            instructions := #[
              .takeUnique (.reg 0) nodeCtor,
              .call functionAddress #[.reg 1]]
            terminator := .ret (.reg 2) }] } }

#guard rejectsAs .credit liveCreditAtCall

private def useAfterTake : Program :=
  { declarations := []
    main :=
      { signature := unarySignature .unique
        blocks := #[
          { valueParams := #[.owned .unique]
            creditParams := #[]
            instructions := #[
              .takeUnique (.reg 0) nodeCtor,
              .move (.reg 0)]
            terminator := .ret (.reg 1) }] } }

#guard rejectsAs .ownership useAfterTake

private def consumeLiveLender : Program :=
  { declarations := []
    main :=
      { signature := unarySignature .unique
        blocks := #[
          { valueParams := #[.owned .unique]
            creditParams := #[]
            instructions := #[
              .fetch (.reg 0) nodeCtor 0,
              .dropUnique (.reg 0),
              .move (.reg 1)]
            terminator := .ret (.lit (.nat 0)) }] } }

#guard rejectsAs .borrow consumeLiveLender

private def incompatibleLayout : Program :=
  { declarations := []
    main :=
      { signature := unarySignature .unique
        blocks := #[
          { valueParams := #[.owned .unique]
            creditParams := #[]
            instructions := #[
              .takeUnique (.reg 0) nodeCtor,
              .allocWith 0 .unique otherCtor #[.reg 1]]
            terminator := .ret (.reg 2) }] } }

#guard rejectsAs .credit incompatibleLayout

private def optionalToRequired : Program :=
  { declarations := []
    main :=
      { signature := unarySignature .shared
        blocks := #[
          { valueParams := #[.owned .shared]
            creditParams := #[]
            instructions := #[.resetShared (.reg 0) nodeCtor]
            terminator := .jump
              { target := 1, values := #[.reg 1], credits := #[0] } },
          { valueParams := #[.owned .shared]
            creditParams := #[.required sharedLayout]
            instructions := #[.discardCredit 0]
            terminator := .ret (.reg 0) }] } }

#guard rejectsAs .credit optionalToRequired

private def missingTarget : Program :=
  { declarations := []
    main :=
      { signature := unarySignature .unique
        blocks := #[
          { valueParams := #[.owned .unique]
            creditParams := #[]
            instructions := #[]
            terminator := .jump
              { target := 7, values := #[.reg 0], credits := #[] } }] } }

#guard rejectsAs .controlFlow missingTarget

private def malformedNatSuccessor : Program :=
  { declarations := []
    main :=
      { signature := unarySignature .unique
        blocks := #[
          { valueParams := #[.owned .unique]
            creditParams := #[]
            instructions := #[]
            terminator := .switchValue (.reg 0) #[]
              (some
                { zero := { target := 1, values := #[.reg 0], credits := #[] }
                  succ := { target := 2, values := #[.reg 0], credits := #[] } }) },
          { valueParams := #[.owned .unique]
            creditParams := #[]
            instructions := #[]
            terminator := .ret (.reg 0) },
          { valueParams := #[.owned .unique, .owned .unique]
            creditParams := #[]
            instructions := #[]
            terminator := .ret (.reg 1) }] } }

#guard rejectsAs .controlFlow malformedNatSuccessor

private def borrowedTailEscape : Program :=
  { declarations :=
      [(functionAddress,
        .fn
          { signature :=
              { params := #[{ world := .unique, passing := .borrowed }]
                result := .unique
                papSafe := false }
            blocks := #[
              { valueParams := #[.borrowed .unique .caller]
                creditParams := #[]
                instructions := #[]
                terminator := .ret (.lit (.nat 0)) }] })]
    main :=
      { signature := unarySignature .unique
        blocks := #[
          { valueParams := #[.owned .unique]
            creditParams := #[]
            instructions := #[.fetch (.reg 0) nodeCtor 0]
            terminator := .tailCall functionAddress #[.reg 1] }] } }

#guard rejectsAs .borrow borrowedTailEscape

private def mismatchedTailResult : Program :=
  { declarations :=
      [(functionAddress,
        .fn
          { signature := nullarySignature .unique
            blocks := #[
              { valueParams := #[]
                creditParams := #[]
                instructions := #[]
                terminator := .ret .erased }] })]
    main :=
      { signature := nullarySignature .shared
        blocks := #[
          { valueParams := #[]
            creditParams := #[]
            instructions := #[]
            terminator := .tailCall functionAddress #[] }] } }

#guard rejectsAs .call mismatchedTailResult

private def borrowedDynamicEntry : Program :=
  { declarations := [(functionAddress, .fn borrowedCallee)]
    main :=
      { signature := unarySignature .unique
        blocks := #[
          { valueParams := #[.owned .unique]
            creditParams := #[]
            instructions := #[.papp functionAddress #[]]
            terminator := .ret (.reg 1) }] } }

#guard rejectsAs .call borrowedDynamicEntry

private def borrowedReturn : Program :=
  { declarations := []
    main :=
      { signature := unarySignature .unique
        blocks := #[
          { valueParams := #[.owned .unique]
            creditParams := #[]
            instructions := #[.fetch (.reg 0) nodeCtor 0]
            terminator := .ret (.reg 1) }] } }

#guard rejectsAs .ownership borrowedReturn

private def forbiddenExtern : Program :=
  { declarations := [(externAddress, .extern 0)]
    main :=
      { signature := nullarySignature
        blocks := #[
          { valueParams := #[]
            creditParams := #[]
            instructions := #[.extern externAddress #[]]
            terminator := .ret (.reg 0) }] } }

#guard rejectsAs .externBoundary forbiddenExtern

#guard match validateWith { defaultLimits with maxBlocks := 1 } context
    (closeFixture simpleJump) with
  | .error (.limit _ .blocks 3 1) => true
  | _ => false

end Ix.Compiler.IxIR2.Validate.Examples
