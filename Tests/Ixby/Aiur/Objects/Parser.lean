module
import Tests.Ixby.Aiur.Objects.Parser.Readers
import Tests.Ixby.Aiur.Objects.Parser.Identity
import Tests.Ixby.Aiur.Objects.Parser.Unique
import Tests.Ixby.Aiur.Objects.Parser.Declarations
import Tests.Ixby.Aiur.Objects.Parser.Admission
import Tests.Ixby.Aiur.Objects.Parser.ProgramPrefix
import Tests.Ixby.Aiur.Objects.Parser.CodeHeaders
import Tests.Ixby.Aiur.Objects.Parser.Operands

/-! Structural certificate and bytecode-contract tests. Forged byte cells and
mutated functions are diagnostic fixtures, not production advice or new keys.
The zero-count certificate remains deliberately partial; the separate full
declaration and advice-loader certificates check both branches and their
required callees. Forged natural metadata tests document Lean evaluator
premises, not claims about native execution or the AIR's range constraints.
The program-prefix certificate binds only the first sixty operations; positive
suffix/control mutations deliberately test that limited boundary. Code-header
certificates extend the program count checks and cover function/block headers,
not instruction decoding or complete function-table admission. Separate full
scalar/leaf-operand certificates cover canonical fields, concrete value layouts,
frame guards and loader composition, not operand lists or whole instructions. -/

namespace Tests.Ixby.Aiur.Objects.Parser

open Ix.Ixby Ix.Ixby.AiurBackend
open Ix.Ixby.AiurBackend.Objects.Memory Ix.Ixby.AiurBackend.Objects.Table Ix.Ixby.AiurBackend.Objects.Parser
open Ix.Ixby.AiurBackend.Objects.Identity
open Ix.Ixby.AiurBackend.Objects.Equality Ix.Ixby.AiurBackend.Objects.Unique
open Ix.Ixby.AiurBackend.Objects.Declarations
open Ix.Ixby.AiurBackend.Objects.Admission
open Aiur.Bytecode.Eval

public def suite : IO UInt32 := runChecks "ixby-objects-parser" do
  IO.println "IxBy bytecode parser proof components"
  let layout ← Operands.layoutChecks
  let result : Except String (List Check) := do
    let source ← objectsToplevel
    let compiled ← source.compile
    let pruned ← (source.prune [`ib_load, `ib_u32, `is_run]).compile
    let (_, byte) ← function pruned `ib_byte
    let (reader, _) ← function pruned `ib_byte
    let (_, word) ← function pruned `ib_u32
    let (_, identity) ← function pruned `is_read_id
    let (_, parser) ← function pruned `is_read_ctors
    let (comparer, cmp) ← function pruned `is_id_eq
    let (self, unique) ← function pruned `is_unique_id
    let shapes ← certificateChecks compiled
    let bytes ← byteChecks compiled
    let identities ← identityChecks compiled
    let comparisons ← comparisonChecks compiled
    let uniqueness ← uniquenessChecks compiled
    let declarations ← declarationCertificates compiled
    let declarationRuntime ← declarationChecks compiled
    let prunedCode ← declarationCode pruned
    let loaders ← loaderCertificates compiled
    let loaderFailures ← loaderFailureChecks compiled "full"
    let prunedFailures ← loaderFailureChecks pruned "pruned"
    let prunedLoader ← loaderCode pruned
    let programCertificates ← ProgramPrefix.certificates compiled "full"
    let prunedProgramCertificates ← ProgramPrefix.certificates pruned "pruned"
    let headerCertificates ← CodeHeaders.certificates compiled "full"
    let prunedHeaderCertificates ← CodeHeaders.certificates pruned "pruned"
    let headerContinuations ← CodeHeaders.continuationChecks compiled "full"
    let prunedHeaderContinuations ← CodeHeaders.continuationChecks pruned "pruned"
    let scalarCertificates ← Operands.certificates compiled "full"
    let prunedScalarCertificates ← Operands.certificates pruned "pruned"
    let scalarFailures ← Operands.failureChecks compiled "full"
    let prunedScalarFailures ← Operands.failureChecks pruned "pruned"
    return shapes ++ bytes ++ wordChecks compiled ++ identities ++ comparisons ++ uniqueness ++ emptyChecks compiled ++
      declarations ++ declarationRuntime ++ declarationSuccessChecks compiled "full" ++ declarationSuccessChecks pruned "pruned" ++
      loaders ++ loaderFailures ++ prunedFailures ++ loaderSuccessChecks compiled "full" ++ loaderSuccessChecks pruned "pruned" ++
      loadedDeclarationChecks compiled "full" ++ loadedDeclarationChecks pruned "pruned" ++
      programCertificates ++ prunedProgramCertificates ++
      ProgramPrefix.successChecks compiled "full" ++ ProgramPrefix.successChecks pruned "pruned" ++
      ProgramPrefix.failureChecks compiled "full" ++ ProgramPrefix.failureChecks pruned "pruned" ++
      ProgramPrefix.loadedChecks compiled "full" ++ ProgramPrefix.loadedChecks pruned "pruned" ++
      headerCertificates ++ prunedHeaderCertificates ++
      CodeHeaders.headerChecks compiled "full" ++ CodeHeaders.headerChecks pruned "pruned" ++
      CodeHeaders.zeroChecks compiled "full" ++ CodeHeaders.zeroChecks pruned "pruned" ++
      CodeHeaders.programChecks compiled "full" ++ CodeHeaders.programChecks pruned "pruned" ++
      CodeHeaders.loadedChecks compiled "full" ++ CodeHeaders.loadedChecks pruned "pruned" ++
      headerContinuations ++ prunedHeaderContinuations ++ scalarCertificates ++ prunedScalarCertificates ++
      Operands.scalarChecks compiled "full" ++ Operands.scalarChecks pruned "pruned" ++
      Operands.operandChecks compiled "full" ++ Operands.operandChecks pruned "pruned" ++
      scalarFailures ++ prunedScalarFailures ++ layout ++
      Operands.loadedChecks compiled "full" ++ Operands.loadedChecks pruned "pruned" ++ [
      ("pruned byte-reader certificate", checkByteReader byte 0),
      ("pruned u32-reader certificate with relocated callee", checkWordReader word reader 0),
      ("pruned identity-reader certificate with relocated callee", checkIdReader identity reader 0),
      ("pruned zero-count parser certificate", checkEmptyTableParser parser 0),
      ("pruned comparator certificate", checkIdEq cmp 0),
      ("pruned uniqueness certificate with both relocated callees", checkUnique unique comparer self 0 1),
      ("pruned complete declaration code certificate with all relocated callees", checkDeclarationCode pruned.bytecode prunedCode),
      ("pruned loader bundle with both relocated functions", checkLoaderCode pruned.bytecode prunedLoader)]
  match result with
  | .ok checks => return checks
  | .error error => return [(s!"parser fixtures: {error}", false)]

end Tests.Ixby.Aiur.Objects.Parser
