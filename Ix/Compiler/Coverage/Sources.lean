import Ix.Compiler.X86.ValidatedScalar

/-! Fixed, bounded Ixon inputs for the source-coverage gate. These inputs are
synthetic; the production-writer contact is loaded separately without rewriting
its bytes. Every constructed constant crosses the canonical source address gate.
No intermediate IR is supplied by these fixtures. -/

namespace Ix.Compiler.Coverage

open Ix.Compiler.Ixon

structure Policy where
  limits : Pipeline.Limits
  checkFuel : Nat := 500
  eraseFuel : Nat := 500
  validateFuel : Nat := 500
  lowerFuel : Nat := 500
  maxDepth : Nat := 500
  evalFuel : Nat := 1000
  controlFuel : Nat := 1000
  heapFuel : Nat := 1000

def sourcePolicy : Policy :=
  { limits :=
      { maxConstants := 16, maxExpressionUnits := 512, maxExpandedExpressionUnits := 512
        maxLayer1NodeVisits := 65536, maxErasedDeclarations := 128, maxErasureAppendCells := 8192
        maxCertificateCandidates := 32, maxCertificateValidationAttempts := 1024
        maxCertificateSourceNodeWork := 524288, maxUsageFuel := 500, maxErasureFuel := 500
        maxValidationFuel := 500, maxLoweringFuel := 500 } }

inductive Expected where
  | scalar (number : Nat) (selected : Bool)
  | usageFreeze
  | externRejected
  deriving BEq, Repr

structure Source where
  name : String
  constants : List (Address × Constant)
  root : Address
  literals : List Nat
  natBlock : Option Address := none
  policy : Policy := sourcePolicy
  expected : Expected

def Source.config (source : Source) : Pipeline.Config :=
  { blobs := fun address =>
      (source.literals.find? fun number =>
        address == X86.ValidatedScalar.literalAddress number).map .natB
    natBlock := source.natBlock
    limits := source.policy.limits }

abbrev Source.Attached (source : Source) :=
  IxIR2.Pipeline.Attached source.constants source.root source.config .shared
    source.policy.eraseFuel source.policy.lowerFuel

def Source.compile (source : Source) : Except IxIR2.Pipeline.Error source.Attached :=
  IxIR2.Pipeline.compileValidated source.constants source.root source.config .shared
    source.policy.checkFuel source.policy.eraseFuel source.policy.validateFuel
    source.policy.lowerFuel source.policy.maxDepth

/-- Canonicalize the synthetic expression table before crossing the ordinary
bounded semantic address gate. Production contact bytes never use this helper. -/
def addressed (constant : Constant) : Except String (Address × Constant) := do
  let some compressed := Sharing.compress? (Sharing.inlineBodies constant)
    | throw "synthetic source compression failed"
  let some info := ConstantIdentityLaws.replaceInfoExprs? constant.info compressed.bodies.toList
    | throw "synthetic source body restoration failed"
  let canonical := { constant with info, sharing := compressed.table }
  match canonical.addressChecked with
  | .error error => throw s!"synthetic source address rejected: {repr error}"
  | .ok address => return (address, canonical)

private def definition (value : Expr) (refs : Array Address := #[])
    (typ : Expr := .sort 0) : Constant :=
  { info := .defn { kind := .defn, safety := .safe, lvls := 0, typ, value }
    sharing := #[], refs, univs := #[.zero] }

private def ghost (value : Expr) : Expr :=
  .app (.lam .erased (.sort 0) value) (.sort 0)

private def projection (info : ConstantInfo) : Constant :=
  { info, sharing := #[], refs := #[], univs := #[] }

private def natInductive : Ixon.Inductive :=
  { isUnsafe := false, lvls := 0, params := 0, indices := 0
    typ := .sort 0
    ctors := #[
      { isUnsafe := false, lvls := 0, cidx := 0, params := 0, fields := 0
        typ := .recur 0 #[] },
      { isUnsafe := false, lvls := 0, cidx := 1, params := 0, fields := 1
        typ := .all .many .shared (.recur 0 #[]) (.recur 0 #[]) }] }

/-- A two-way recursor returns 11 for zero and 22 for successor. Its field
is intentionally unused; both alternatives must still execute through the
checked constructor/Nat dispatch path. -/
private def tagRecursor : Recursor :=
  { k := false, isUnsafe := false, lvls := 0
    params := 0, indices := 0, motives := 0, minors := 0
    typ := .all .many .shared (.recur 0 #[]) (.sort 0)
    rules := #[
      { fields := 0, rhs := .nat 0 },
      { fields := 1, rhs := .lam .many (.recur 0 #[]) (.nat 1) }] }

def scalar (name : String) (number : Nat) (selected : Bool) : Except String Source := do
  let entry ← addressed (X86.ValidatedScalar.constant number)
  return {
    name, constants := [entry], root := entry.1, literals := [number]
    policy := { limits := (X86.ValidatedScalar.config number).limits
                checkFuel := 100, eraseFuel := 100, validateFuel := 100
                lowerFuel := 100, maxDepth := 100 }
    expected := .scalar number selected }

/-- Two uses of a known identity force an ordinary direct call followed by a
tail call. Its Nat argument is computed through the shared PAP path. -/
def directCall : Except String Source := do
  let block ← addressed
    { info := .muts #[.indc natInductive], sharing := #[], refs := #[], univs := #[.zero] }
  let natType ← addressed (projection (.iPrj { idx := 0, block := block.1 }))
  let worker ← addressed (definition (.lam .many (.ref 0 #[]) (.var 0))
    #[natType.1] (.all .many .shared (.ref 0 #[]) (.ref 0 #[])))
  let entry ← addressed (definition
    (.app (.ref 0 #[]) (.app (.ref 0 #[]) (ghost (.nat 1))))
    #[worker.1, X86.ValidatedScalar.literalAddress 42, natType.1] (.ref 2 #[]))
  return {
    name := "direct-call", constants := [block, natType, worker, entry]
    root := entry.1, literals := [42], expected := .scalar 42 false }

def dispatch (literal successorCase : Bool) : Except String Source := do
  let block ← addressed
    { info := .muts #[.indc natInductive, .recr tagRecursor]
      sharing := #[]
      refs := #[X86.ValidatedScalar.literalAddress 11, X86.ValidatedScalar.literalAddress 22]
      univs := #[.zero] }
  let recursor ← addressed (projection (.rPrj { idx := 1, block := block.1 }))
  let zero ← addressed (projection (.cPrj { idx := 0, cidx := 0, block := block.1 }))
  let successor ← addressed (projection (.cPrj { idx := 0, cidx := 1, block := block.1 }))
  let number := if successorCase then 3 else 0
  let major := if literal then ghost (.nat 1)
    else if successorCase then .app (.ref 3 #[]) (ghost (.nat 1))
    else ghost (.ref 2 #[])
  let entry ← addressed (definition (.app (.ref 0 #[]) major)
    #[recursor.1, X86.ValidatedScalar.literalAddress number, zero.1, successor.1])
  return {
    name := s!"{if literal then "nat" else "ctor"}-{if successorCase then "succ" else "zero"}"
    constants := [block, recursor, zero, successor, entry], root := entry.1
    literals := [number, 11, 22], natBlock := if literal then some block.1 else none
    expected := .scalar (if successorCase then 22 else 11) false }

def bareLiteral : Except String Source := do
  let entry ← addressed (X86.ValidatedScalar.constant 42 false)
  return { name := "bare-literal", constants := [entry], root := entry.1
           literals := [42], expected := .usageFreeze }

def externSource : Except String Source := do
  let entry ← addressed
    { info := .axio { isUnsafe := false, lvls := 0, typ := .sort 0 }
      sharing := #[], refs := #[], univs := #[.zero] }
  return { name := "extern", constants := [entry], root := entry.1
           literals := [], expected := .externRejected }

def sources : Except String (List Source) := do
  return [← scalar "scalar-zero" 0 true, ← scalar "scalar-42" 42 true,
    ← scalar "scalar-max" (UInt64.size - 1) true,
    ← scalar "scalar-overflow" UInt64.size false,
    ← directCall, ← dispatch false false, ← dispatch false true,
    ← dispatch true false, ← dispatch true true, ← bareLiteral, ← externSource]

end Ix.Compiler.Coverage
