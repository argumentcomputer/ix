/-
  Ix/Frontend.lean

  Top-level entry point for the pure, deterministic Ix frontend:
  1. `Text -> Ix.Syntax` (`parseSource`, `parseModule`)
  2. `Ix.Syntax -> ModuleIndex -> ScheduledSCCs` (`buildModuleIndex`, `scheduleModuleDecls`)
  3. `Ix.Syntax -> IxElabEnv` (`elabModuleSyntax`, `elabSource`)
     - Substructural usage (`0`, `1`, `&`, unmarked `many`), ownership (`!`, unmarked `shared`),
       and relative locality (`~`, unmarked `unrestricted`), plus `let borrow`.
     - Order-free and `mutual`-free declarations via Tarjan SCC condensation.
     - In-elaborator block and constructor canonicalization (breaking constructor α-ties
       by source declaration order to avoid call-site rewrites).
     - Surgery-free generation of `.rec`, `.recOn`, `.casesOn`, `._ctorIdx`, and structure projections.
     - First-class content-hash references (`#<64-hex>`) and programmable `map Name := #<hash>` imports.
  4. `IxElabEnv -> Ixon.Env` (`compileElabEnvToIxon`, `compileSourceToIxon`)
  5. `Ixon.Env -> Ix.Resource.AddressedProgram` (`checkSourceResources`)
-/
module

public import Ix.Frontend.Syntax
public import Ix.Frontend.Parser.Trie
public import Ix.Frontend.Parser.Types
public import Ix.Frontend.Parser.Basic
public import Ix.Frontend.Parser.Term
public import Ix.Frontend.Parser.Command
public import Ix.Frontend.Scope
public import Ix.Frontend.SccPass
public import Ix.Frontend.Elab.Monad
public import Ix.Frontend.Elab.Meta
public import Ix.Frontend.CanonBlock
public import Ix.Frontend.AuxGen
public import Ix.Frontend.Elab.Tactic
public import Ix.Frontend.Elab.Term
public import Ix.Frontend.Elab.Command
public import Ix.Frontend.Merge
public import Ix.Frontend.Format
public import Ix.Claim
public import Ix.GraphM
public import Ix.CondenseM
public import Ix.CompileDriver
public import Ix.DecompileM
public import Ix.Cert.Compile
public import Ix.Resource.Addressed

@[expose] public section

namespace Ix.Frontend

open Parser Elab

/-- Hydrate an `IxElabEnv` from a compiled `Ixon.Env` (decompiling constants, reconstructing
    `StructInfo` tables, and registering `Name -> Address` mappings in `importMap`). -/
def IxElabEnv.ofIxonEnv (ixe : Ixon.Env) : IxElabEnv :=
  let (rawConsts, _errs) := Ix.DecompileM.decompileAllParallel ixe
  let initIxEnv : Ix.Environment :=
    { consts := @Std.HashMap.emptyWithCapacity Ix.Name Ix.ConstantInfo Ix.Name.instBEq Ix.Name.instHashable rawConsts.size }
  let ixEnv := rawConsts.fold (fun acc nm ci =>
    { consts := acc.consts.insert (Name.rehash nm) (Expr.ConstantInfo.rehash ci) }) initIxEnv
  let base := IxElabEnv.ofIxEnvironment ixEnv
  let impMap := ixe.named.fold (fun acc nm named => acc.insertName nm named.addr) base.importMap
  base.withImportMap impMap

/-- Parse an Ix source string into a concrete syntax tree (`SyntaxKind.moduleKind`). -/
def parseSource (input : String) (fileName : String := "<input>")
    (pEnv : IxParserEnv := defaultParserEnv) :
    Except String (Ix.Syntax × IxParserEnv) :=
  parseModuleWithEnv input fileName pEnv

/-- Compile an elaborated `IxElabEnv` into a canonical `Ixon.Env` and `Ix.CompileM.CompileEnv`
    using the pure Lean compilation pipeline (`GraphM.envSerial` -> `CondenseM.run` -> `compileEnvFold`). -/
def compileElabEnvToIxon (elabEnv : IxElabEnv) :
    Except String (Ixon.Env × Ix.CompileM.CompileEnv) := do
  let ixEnv := elabEnv.toIxEnvironment
  let outRefs := Ix.GraphM.envSerial ixEnv
  let condensed := Ix.CondenseM.run outRefs
  let (ixonEnv, _totalBytes, cenv) ← Ix.CompileM.compileEnvFold ixEnv condensed (width := 1)
  if !cenv.ungrounded.isEmpty then
    let firstErr := match cenv.ungrounded.toList.head? with
      | some (nm, msg) => s!"{nm}: {msg}"
      | none => "<unknown>"
    throw s!"compileElabEnvToIxon: {cenv.ungrounded.size} ungrounded constant(s), first: {firstErr}"
  return (ixonEnv, cenv)

/-- Compile an elaborated `IxElabEnv` through the formally certified compiler (`Ix.Cert.compileReport`). -/
def compileElabEnvCertified (elabEnv : IxElabEnv) :
    Except String (Ixon.Env × Ix.Cert.Failures) := do
  let (ixonEnv, failures) ← Ix.Cert.compileReport elabEnv.toIxEnvironment
  if !failures.isEmpty then
    throw s!"compileElabEnvCertified: {failures.toMap.size} failure(s) in Ix.Cert.compileReport"
  return (ixonEnv, failures)

/-- Parse, elaborate, canonicalize, and compile an Ix source string to `Ixon.Env` purely. -/
def compileSourceToIxon (input : String)
    (fileName : String := "<input>")
    (initElabEnv : IxElabEnv := IxElabEnv.empty)
    (initParserEnv : IxParserEnv := defaultParserEnv)
    (seedPrelude : Bool := true) :
    Except String (Ix.Syntax × IxElabEnv × Ixon.Env × Ix.CompileM.CompileEnv) := do
  let (stx, _pEnv) ← parseModuleWithEnv input fileName initParserEnv
  let elabEnv ← elabModuleSyntax stx initElabEnv seedPrelude
  let (ixonEnv, cenv) ← compileElabEnvToIxon elabEnv
  return (stx, elabEnv, ixonEnv, cenv)

/-- Parse, elaborate, canonicalize, and compile an Ix source string through `Ix.Cert.compileReport`. -/
def compileSourceCertified (input : String)
    (fileName : String := "<input>")
    (initElabEnv : IxElabEnv := IxElabEnv.empty)
    (initParserEnv : IxParserEnv := defaultParserEnv)
    (seedPrelude : Bool := true) :
    Except String (Ix.Syntax × IxElabEnv × Ixon.Env × Ix.Cert.Failures) := do
  let (stx, _pEnv) ← parseModuleWithEnv input fileName initParserEnv
  let elabEnv ← elabModuleSyntax stx initElabEnv seedPrelude
  let (ixonEnv, failures) ← compileElabEnvCertified elabEnv
  return (stx, elabEnv, ixonEnv, failures)

/-- Topologically elaborate a multi-module DAG and compile the resulting environment to `Ixon.Env`. -/
def compileModuleDAGToIxon (modules : List (Ix.Name × String))
    (initElabEnv : IxElabEnv := IxElabEnv.empty)
    (initParserEnv : IxParserEnv := defaultParserEnv)
    (seedPrelude : Bool := true) :
    Except String (IxElabEnv × IxParserEnv × Ixon.Env × Ix.CompileM.CompileEnv) := do
  let (elabEnv, parserEnv) ← elabModuleDAG modules initElabEnv initParserEnv seedPrelude
  let (ixonEnv, cenv) ← compileElabEnvToIxon elabEnv
  return (elabEnv, parserEnv, ixonEnv, cenv)

/-- Topologically elaborate a multi-module DAG and compile through `Ix.Cert.compileReport`. -/
def compileModuleDAGCertified (modules : List (Ix.Name × String))
    (initElabEnv : IxElabEnv := IxElabEnv.empty)
    (initParserEnv : IxParserEnv := defaultParserEnv)
    (seedPrelude : Bool := true) :
    Except String (IxElabEnv × IxParserEnv × Ixon.Env × Ix.Cert.Failures) := do
  let (elabEnv, parserEnv) ← elabModuleDAG modules initElabEnv initParserEnv seedPrelude
  let (ixonEnv, failures) ← compileElabEnvCertified elabEnv
  return (elabEnv, parserEnv, ixonEnv, failures)

/-- Parse, elaborate, canonicalize, compile to `Ixon.Env`, and run deterministic
    substructural resource checking (`Ix.Resource.Addressed.checkResources`). -/
def checkSourceResources (input : String)
    (profile : Ix.Resource.Profile := {})
    (fileName : String := "<input>")
    (initElabEnv : IxElabEnv := IxElabEnv.empty)
    (initParserEnv : IxParserEnv := defaultParserEnv)
    (seedPrelude : Bool := true) :
    Except String (Ix.Syntax × IxElabEnv × Ixon.Env × Ix.Resource.AddressedProgram) := do
  let (stx, elabEnv, ixonEnv, _cenv) ←
    compileSourceToIxon input fileName initElabEnv initParserEnv seedPrelude
  let addressed ← Ix.Resource.Addressed.checkResources ixonEnv profile
  return (stx, elabEnv, ixonEnv, addressed)

/-- Compute the content address of a source string (BLAKE3 over UTF-8 bytes). -/
def hashSourceText (input : String) : Address :=
  Address.admissionHash input.toUTF8

/-- Compute the canonical content address of an `Ix.Syntax` tree (BLAKE3 Merkle hash). -/
def hashSyntax : Ix.Syntax → Address
  | .missing =>
    Address.admissionHash (ByteArray.mk #[0x00])
  | .atom _ val =>
    Address.admissionHash (ByteArray.mk #[0x01] ++ val.toUTF8)
  | .ident _ _ val _ =>
    Address.admissionHash (ByteArray.mk #[0x02] ++ (Name.computeHash val).hash)
  | .node _ kind args =>
    let header := ByteArray.mk #[0x03] ++ (Name.computeHash kind).hash
    let payload := args.attach.foldl (fun acc ⟨a, _⟩ => acc ++ (hashSyntax a).hash) header
    Address.admissionHash payload

/-- Compute the canonical commitment address of a compiled `Ixon.Env` (BLAKE3 over `Ixon.serEnv`). -/
def hashIxonEnv (ixonEnv : Ixon.Env) : Except String Address := do
  let bytes ← Ixon.serEnv ixonEnv
  return Address.admissionHash bytes

/-- Construct an `ElabClaim` from a source string by running the pure Ix parser,
    elaborator, canonicalizer, and Ixon compiler. -/
def mkElabClaimFromSource (input : String)
    (ctx : Ix.ClaimContext := default)
    (assumptions : Option Address := none)
    (fileName : String := "<input>")
    (initElabEnv : IxElabEnv := IxElabEnv.empty)
    (initParserEnv : IxParserEnv := defaultParserEnv)
    (seedPrelude : Bool := true) :
    Except String (Ix.ElabClaim × Ix.Syntax × IxElabEnv × Ixon.Env) := do
  let (stx, elabEnv, ixonEnv, _cenv) ←
    compileSourceToIxon input fileName initElabEnv initParserEnv seedPrelude
  let sourceAddr := hashSourceText input
  let syntaxAddr := hashSyntax stx
  let envAddr ← hashIxonEnv ixonEnv
  let claim : Ix.ElabClaim := {
    ctx, sourceAddr, syntaxAddr, envAddr, assumptions
  }
  return (claim, stx, elabEnv, ixonEnv)

/-- Purely verify an `ElabClaim` against a source text string:
    1. Checks `hashSourceText input == claim.sourceAddr`
    2. Parses `input -> stx` and checks `hashSyntax stx == claim.syntaxAddr`
    3. Elaborates and compiles `stx -> ixonEnv` and checks `hashIxonEnv ixonEnv == claim.envAddr` -/
def verifyElabClaimPure (claim : Ix.ElabClaim) (input : String)
    (fileName : String := "<input>")
    (initElabEnv : IxElabEnv := IxElabEnv.empty)
    (initParserEnv : IxParserEnv := defaultParserEnv)
    (seedPrelude : Bool := true) : Except String Bool := do
  if hashSourceText input != claim.sourceAddr then
    return false
  let (stx, _pEnv) ← parseModuleWithEnv input fileName initParserEnv
  if hashSyntax stx != claim.syntaxAddr then
    return false
  let elabEnv ← elabModuleSyntax stx initElabEnv seedPrelude
  let (ixonEnv, _cenv) ← compileElabEnvToIxon elabEnv
  let envAddr ← hashIxonEnv ixonEnv
  return envAddr == claim.envAddr

/-- Purely verify an `ElabClaim` against a source text string using certificate-guided
    elaboration (`elabModuleWithHints`) for `O(|stx|)` zero-metavariable verification. -/
def verifyElabClaimWithHintsPure (claim : Ix.ElabClaim) (input : String)
    (hints : ElabHints)
    (fileName : String := "<input>")
    (initElabEnv : IxElabEnv := IxElabEnv.empty)
    (initParserEnv : IxParserEnv := defaultParserEnv)
    (seedPrelude : Bool := true) : Except String Bool := do
  if hashSourceText input != claim.sourceAddr then
    return false
  let (stx, _pEnv) ← parseModuleWithEnv input fileName initParserEnv
  if hashSyntax stx != claim.syntaxAddr then
    return false
  let elabEnv ← elabModuleWithHints stx hints initElabEnv seedPrelude
  let (ixonEnv, _cenv) ← compileElabEnvToIxon elabEnv
  let envAddr ← hashIxonEnv ixonEnv
  return envAddr == claim.envAddr

end Ix.Frontend

end
