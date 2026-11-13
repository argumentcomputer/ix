import Ix.Claim
import Ix.ClaimContext
import Ix.CompileM
import Ix.CompileCertified
import Ix.Cli.CatalogCmd
import IxC.Kernel.Ixon.Prelude

/-! # The claims `ix verify` and `ix compress` refuse, through the `ix` binary

`claim-policy-cli`, in a temporary `HOME`, over stored proof wrappers that carry
no proof, with IxVM and aggregation artifact paths that name no file. The policy
runs before verification, so each case is decided by whether the claim is
refused (`refused:`, and the flag or option the refusal names); an accepted claim
then fails at verification only.

* `ix verify`: an unconditional `check` claim under the default role table is
  accepted. Each kind of claim that states no typing is refused, naming its flag,
  accepted under that flag and refused under another kind's. A catalog is refused
  under every flag, naming `--ixc`, and so is `ix verify --aggregate` of one. A
  claim naming another specification set than this build's is refused under every
  flag, a binding claim under its own flag included.
* `ix compress`: an input that is not a `CheckEnv` proof is refused before the
  policy runs; a `CheckEnv` claim under another specification set is refused.
* `ix verify --aggregate --ixc`: a one-member catalog whose member depends on a
  user axiom is refused, naming the member and `--allow-axioms`, and accepted
  under that flag; a catalog whose member does not is accepted.

Needs `.lake/build/bin/ix` (`lake build ix`). -/

namespace Tests.ClaimPolicyCli

private def addr (s : String) : Address := Address.blake3 s.toUTF8

private def mentions (s text : String) : Bool := (s.splitOn text).length > 1

/-- Store `bytes` where `ix` reads its store under `home`. -/
private def storeUnder (home : System.FilePath) (bytes : ByteArray) : IO Address := do
  let address := Address.blake3 bytes
  let hex := toString address
  let dir := home / ".ix" / "store" / (hex.take 2).toString / ((hex.drop 2).take 2).toString /
    ((hex.drop 4).take 2).toString
  IO.FS.createDirAll dir
  IO.FS.writeBinFile (dir / (hex.drop 6).toString) bytes
  return address

/-- A stored wrapper of `claim` with no proof. -/
private def wrapperOf (home : System.FilePath) (claim : Ix.Claim) : IO Address :=
  storeUnder home (Ixon.Proof.ser { claim, proof := "no proof".toUTF8 })

/-! ## Catalog pieces -/

private def nN : Lean.Name := `TClaimPolicy.N
private def nE : Lean.Name := `TClaimPolicy.Empty

/-- A piece's constants, from a kernel environment without `Init`: an inductive
and a definition over it, and with `withAxiom` an empty proposition and an axiom
of it. -/
private def pieceConsts (withAxiom : Bool) : IO (List (Lean.Name × Lean.ConstantInfo)) := do
  let cN : Lean.Expr := .const nN []
  let idN : Lean.Name := `TClaimPolicy.idN
  let base : List Lean.Declaration := [
    .inductDecl [] 0 [{
      name := nN
      type := .sort (.succ .zero)
      ctors := [{ name := `TClaimPolicy.N.zero, type := cN }] }] false,
    .defnDecl {
      name := idN
      levelParams := []
      type := .forallE `n cN cN .default
      value := .lam `n cN (.bvar 0) .default
      hints := .regular 1
      safety := .safe
      all := [idN] }]
  let extra : List Lean.Declaration := if withAxiom then [
      .inductDecl [] 0 [{ name := nE, type := .sort .zero, ctors := [] }] false,
      .axiomDecl {
        name := `TClaimPolicy.bad
        levelParams := []
        type := .const nE []
        isUnsafe := false }]
    else []
  let env ← Lean.mkEmptyEnvironment
  let mut kenv := env.toKernelEnv
  for decl in base ++ extra do
    match kenv.addDecl {} decl with
    | .ok kenv' => kenv := kenv'
    | .error _ => throw (IO.userError "claim-policy-cli: the kernel rejected a fixture declaration")
  return kenv.constants.fold (init := []) fun acc name info => (name, info) :: acc

/-- Compile `consts` into a piece bound to the default role table at `path`. -/
private def writePiece (consts : List (Lean.Name × Lean.ConstantInfo)) (path : System.FilePath) :
    IO Unit := do
  let (env, failures) ← IO.ofExcept (Ix.Cert.compileReport (Ix.CompileM.canonInput consts.toArray 4))
  unless failures.isEmpty do
    throw (IO.userError s!"claim-policy-cli: the fixture does not compile \
      ({failures.toMap.size} failures)")
  let bytes ← IO.ofExcept Ix.Kernel.Reader.defaultTableBytes
  let address ← IO.ofExcept Ix.Kernel.Reader.defaultTableAddress
  IO.FS.writeBinFile path
    (← IO.ofExcept (Ixon.serEnv { env with roleBinding := some { address, bytes } }))

/-- A one-member catalog of a piece at `ixc`, and whether its member names user
axioms. -/
private def catalog (dir : System.FilePath) (label : String) (withAxiom : Bool) :
    IO (System.FilePath × Bool) := do
  let piece := dir / s!"{label}.ixe"
  writePiece (← pieceConsts withAxiom) piece
  let ixc := dir / s!"{label}.ixc"
  let members := Lean.Json.arr #[Lean.Json.mkObj [("path", .str piece.toString), ("label", .str label)]]
  discard <| Ix.Cli.CatalogCmd.rsCatalogAssembleFFI ixc.toString members.compress
  -- the member's context as `ix verify --ixc` reads it from the piece
  let env ← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile (ixc / s!"{label}.ixe")))
  let ctx ← IO.ofExcept (Ix.ClaimContext.ofEnv env)
  return (ixc, ctx.axioms.isSome)

/-- The runner. -/
def run : IO UInt32 := do
  let ixExe : System.FilePath := ".lake" / "build" / "bin" / "ix"
  unless (← ixExe.pathExists) do
    IO.eprintln s!"{ixExe} missing: run `lake build ix` first"
    return 1
  let ix ← IO.FS.realPath ixExe
  let spec ← IO.ofExcept Ix.SpecDigest.specDigest
  let ctx ← IO.ofExcept Ix.ClaimContext.ofDefaultTable
  let otherSpec := addr "another specification set"
  let failures ← IO.mkRef (#[] : Array String)
  let dir ← IO.FS.createTempDir
  try
    let home := dir / "home"
    let absent := (dir / "absent.ixa").toString
    let artifacts := #["--aiur-artifact", absent, "--aggr-artifact", absent]
    let invoke (args : Array String) : IO String := do
      -- the setup `ix compress` checks before it reads its input, as `compression-cli` runs it
      let out ← IO.Process.output {
        cmd := ix.toString
        args := args
        env := #[("HOME", some home.toString), ("IX_KZG_SRS", none), ("IX_KZG_SRS_CACHE", none),
          ("IX_PARAMS_DIR", some (home / "params").toString), ("IX_GROTH16_ARTIFACTS", none)] }
      return out.stdout ++ out.stderr
    let check (label : String) (ok : Bool) (out : String) : IO Unit := do
      IO.println s!"[claim-policy-cli] {if ok then "ok" else "FAILED"}: {label}"
      unless ok do
        IO.eprintln out
        failures.modify (·.push label)
    let verify (proof : Address) (extra : Array String) : IO String :=
      invoke (#["verify", toString proof] ++ artifacts ++ extra)
    -- an unconditional typing claim under the default role table
    let unconditional ← wrapperOf home (.check ctx (addr "constant") none)
    let o ← verify unconditional #[]
    check "an unconditional check claim under the default role table is accepted"
      (!mentions o "refused:") o
    -- each kind that states no typing
    let kinds : List (String × Ix.Claim) := [
      ("reveal", .reveal (addr "commitment") (.axio none none none)),
      ("contains", .contains (addr "tree") (addr "constant")),
      ("binding", .binding spec ctx.binding)]
    for (kind, claim) in kinds do
      let w ← wrapperOf home claim
      let flag := s!"--allow-{kind}-claim"
      let other := if kind == "contains" then "--allow-reveal-claim" else "--allow-contains-claim"
      let o ← verify w #[]
      check s!"a {kind} claim is refused, naming {flag}" (mentions o "refused:" && mentions o flag) o
      let o ← verify w #[flag]
      check s!"  and accepted under {flag}" (!mentions o "refused:") o
      let o ← verify w #[other]
      check s!"  and refused under {other}" (mentions o "refused:") o
    -- a catalog
    let catalogRoot ← wrapperOf home (.catalog (addr "members"))
    let everyFlag := #["--allow-custom-binding", "--allow-axioms", "--allow-assumed-binding",
      "--allow-assumptions", "--allow-reveal-claim", "--allow-contains-claim",
      "--allow-binding-claim"]
    let o ← verify catalogRoot #[]
    check "a catalog claim is refused, naming --ixc" (mentions o "refused:" && mentions o "--ixc") o
    let o ← verify catalogRoot everyFlag
    check "  under every flag" (mentions o "refused:") o
    let o ← invoke (#["verify", "--aggregate", toString catalogRoot] ++ artifacts ++ everyFlag)
    check "  and as an aggregate root without --ixc" (mentions o "refused:" && mentions o "--ixc") o
    -- another specification set
    let stale ← wrapperOf home (.checkEnv { ctx with spec := otherSpec } (addr "root") none)
    let o ← verify stale everyFlag
    check "a claim under another specification set is refused under every flag"
      (mentions o "refused:" && mentions o "specification set") o
    let staleBinding ← wrapperOf home (.binding otherSpec ctx.binding)
    let o ← verify staleBinding #["--allow-binding-claim"]
    check "  and a binding claim under it, under --allow-binding-claim"
      (mentions o "refused:" && mentions o "specification set") o
    -- `ix compress`
    let contains ← wrapperOf home (.contains (addr "tree") (addr "constant"))
    let compress (proof : Address) : IO String :=
      invoke (#["compress", toString proof, "--dev-kzg-srs", "--out", (dir / "run").toString]
        ++ artifacts)
    let o ← compress contains
    check "ix compress refuses an input other than a CheckEnv proof before the policy"
      (mentions o "aggregate CheckEnv proof" && !mentions o "refused:") o
    let o ← compress stale
    check "ix compress refuses a CheckEnv claim under another specification set"
      (mentions o "refused:" && mentions o "specification set") o
    -- `ix verify --aggregate --ixc`: each member under the policy
    let (bad, badAxioms) ← catalog dir "axiom" true
    let (good, goodAxioms) ← catalog dir "clean" false
    check "the fixture: one member names user axioms, the other none" (badAxioms && !goodAxioms) ""
    let ixc (catalogDir : System.FilePath) (extra : Array String) : IO String :=
      invoke (#["verify", "--aggregate", toString catalogRoot, "--ixc", catalogDir.toString]
        ++ artifacts ++ extra)
    let o ← ixc bad #[]
    check "a catalog whose member depends on a user axiom is refused, naming the member"
      (mentions o "refused:" && mentions o "member axiom" && mentions o "--allow-axioms") o
    let o ← ixc bad #["--allow-axioms"]
    check "  and its member accepted under --allow-axioms" (!mentions o "refused:") o
    let o ← ixc good #[]
    check "a catalog whose member depends on no user axiom is accepted" (!mentions o "refused:") o
  finally
    IO.FS.removeDirAll dir
  let failed ← failures.get
  for f in failed do IO.eprintln s!"[claim-policy-cli] FAILED: {f}"
  return if failed.isEmpty then 0 else 1

end Tests.ClaimPolicyCli
