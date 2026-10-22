module
public import Lean.ToExpr
public import Lean.Data.Json.FromToJson

public import Ix.Commit
public import Ix.Meta
public import Ix.Aiur.Compiler
public import Ix.IxVM.Toplevel
public import Ix.IxVM.FunctionGroups
public import Ix.IxVM.ClaimHarness

public section
namespace ZKVoting

inductive Candidate where
  | alice | bob | charlie
  deriving Inhabited, Lean.ToExpr, Repr, BEq

/-- The receipt commits to the whole ballot, including a fresh 256-bit salt. -/
structure Ballot where
  salt : Nat
  choice : Candidate
  deriving Lean.ToExpr

structure Result where
  alice : Nat
  bob : Nat
  charlie : Nat
  deriving Inhabited, Lean.ToExpr, Repr, BEq, Lean.ToJson, Lean.FromJson

/-- The agreed program: each list entry contributes exactly one vote. -/
def runElection : List Ballot → Result
  | [] => ⟨0, 0, 0⟩
  | ballot :: rest =>
    let result := runElection rest
    match ballot.choice with
    | .alice => { result with alice := Nat.succ result.alice }
    | .bob => { result with bob := Nat.succ result.bob }
    | .charlie => { result with charlie := Nat.succ result.charlie }

/-- Public data only: no ballot bodies, salts, or witness environment. -/
structure Board where
  format : Nat := 1
  receipts : Array String
  tally : Result
  deriving Lean.ToJson, Lean.FromJson

def parseReceipt (s : String) : Except String Address := do
  let some addr := Address.fromString s | throw s!"Invalid ballot receipt: {s}"
  unless toString addr == s do throw "Receipt must be canonical lowercase hex"
  return addr

/-- Compile the agreed program independently on both sides. The verifier never
imports a prover-supplied program or private environment. -/
def compileElection (env : Lean.Environment) : IO Ix.CompileM.CompilePhases := do
  let mut seen : Lean.NameSet := {}
  let mut entries := #[]
  for name in #[``runElection, ``Ballot.mk, ``Result.mk] ++ IxVM.ClaimHarness.synthesizedPrimNames do
    for entry in Lean.collectDependencies name env.constants do
      unless seen.contains entry.1 do
        seen := seen.insert entry.1
        entries := entries.push entry
  Ix.CompileM.rsCompilePhasesOf entries.toList

/-- Reconstruct both endpoint hashes from public data. Never trust a supplied
claim's function, input list, output, or typing assumptions. -/
def expectedClaim (base : Ix.CompileM.CompileEnv) (board : Board) :
    Except String (Ix.Claim × Ix.CompileM.CompileEnv) := do
  unless board.format == 1 do throw "Unsupported election format"
  if board.receipts.isEmpty then throw "The election has no ballots"
  let receipts ← board.receipts.mapM parseReceipt
  let mut seen : Std.HashSet Address := {}
  let mut cache := base
  for receipt in receipts do
    if seen.contains receipt then throw "Duplicate ballot receipt"
    seen := seen.insert receipt
    -- Register the reference without its private definition. IxVM authenticates
    -- and typechecks the ballot when evaluating the claim.
    let (name, _) := (Ix.CanonM.canonName (Address.toUniqueName receipt)).run {}
    cache := { cache with
      nameToAddr := cache.nameToAddr.insert name receipt
      nameToNamed := cache.nameToNamed.insert name { addr := receipt, constMeta := .empty } }
  let tally := board.tally
  unless tally.alice + tally.bob + tally.charlie == receipts.size do
    throw "Tally total does not match the ballot count"
  let ballot := Lean.mkConst ``Ballot
  let values := receipts.foldr (init := Lean.mkApp (Lean.mkConst ``List.nil [.zero]) ballot)
    fun receipt tail => Lean.mkApp3 (Lean.mkConst ``List.cons [.zero]) ballot
      (Lean.mkConst (Address.toUniqueName receipt)) tail
  let input := Lean.mkApp (Lean.mkConst ``runElection) values
  -- Eval requires a normal-form output. `ToExpr Nat` introduces frontend OfNat
  -- applications, so encode the counts as raw kernel literals instead.
  let output := Lean.mkApp3 (Lean.mkConst ``Result.mk)
    (.lit (.natVal tally.alice)) (.lit (.natVal tally.bob)) (.lit (.natVal tally.charlie))
  Ix.Commit.evalClaimWithEnv cache [] input output (Lean.mkConst ``Result)

def checkStatement (base : Ix.CompileM.CompileEnv) (board : Board)
    (claim : Ix.Claim) (ownReceipts : Array String := #[]) : Except String Unit := do
  let (expected, _) ← expectedClaim base board
  unless Ix.Claim.ser claim == Ix.Claim.ser expected do
    throw "Proof claim does not match the published ballot list, tally, and agreed program"
  for own in ownReceipts do
    let _ ← parseReceipt own
    unless board.receipts.contains own do throw s!"Your ballot receipt is missing: {own}"

def materialize (base : Ixon.Env) (cache : Ix.CompileM.CompileEnv) : Except String Ixon.Env := do
  let mut env := { base with blobs := cache.blobs }
  for (addr, bytes) in cache.constants.toArray do
    unless env.consts.contains addr do
      let c : Ixon.Constant ← Ixon.de bytes
      env := env.storeConst addr c
      env := { env with anonHints := env.anonHints.insert addr (.regular 0) }
  return env

def compileVM : IO Aiur.CompiledToplevel := do
  let vm ← IO.ofExcept (IxVM.ixVM.mapError toString)
  IO.ofExcept (vm.compileWithGroups IxVM.functionGroups)

def buildSystem (vm : Aiur.CompiledToplevel) : Aiur.AiurSystem :=
  Aiur.AiurSystem.build vm.bytecode Aiur.defaultCommitmentParameters Aiur.defaultFriParameters

def verifyProof (system : Aiur.AiurSystem) (vm : Aiur.CompiledToplevel)
    (base : Ix.CompileM.CompileEnv) (board : Board) (wrapper : Ixon.Proof)
    (ownReceipts : Array String := #[]) : Except String Unit := do
  checkStatement base board wrapper.claim ownReceipts
  let proof ← Aiur.Proof.ofBytesChecked wrapper.proof
  let some idx := vm.getFuncIdx `verify_claim | throw "Missing verify_claim entrypoint"
  let digest := IxVM.ClaimHarness.packedDigestKey (Address.blake3 (Ix.Claim.ser wrapper.claim))
  (system.verify (Aiur.buildClaim idx digest #[]) proof).mapError toString

private def showTally (result : Result) : String :=
  s!"Alice {result.alice} | Bob {result.bob} | Charlie {result.charlie}"

def proveElection (args : List String) : IO Unit := do
  let dir :: args := args
    | throw <| IO.userError "Usage: Prover DIRECTORY [--execute-only] [alice bob charlie ...]"
  let executeOnly := args.contains "--execute-only"
  let choices := args.filter (· != "--execute-only")
  let choices := if choices.isEmpty then ["alice", "alice", "bob"] else choices
  let choices ← IO.ofExcept (choices.mapM fun
    | "alice" => .ok Candidate.alice
    | "bob" => .ok .bob
    | "charlie" => .ok .charlie
    | s => .error s!"Unknown candidate '{s}'; use alice, bob, or charlie")
  let dir : System.FilePath := dir
  if ← dir.pathExists then throw <| IO.userError s!"{dir} already exists; choose a fresh demo directory"
  IO.println "Preparing ballots with fresh random salts..."
  let phases ← compileElection (← get_env!)
  let mut cache := Ix.Commit.mkCompileEnv phases
  let mut receipts := #[]
  let mut ballots := []
  for choice in choices do
    let saltBytes ← IO.getRandomBytes 32
    let salt := saltBytes.data.foldl (fun n b => n * 256 + b.toNat) 0
    let ballot : Ballot := ⟨salt, choice⟩
    let (receipt, next) ← IO.ofExcept (Ix.Commit.compileDef cache []
      (Lean.mkConst ``Ballot) (Lean.toExpr ballot))
    cache := next
    receipts := receipts.push (toString receipt)
    ballots := ballot :: ballots
    IO.println s!"Voter {receipts.size} receipt: {receipt}"
  let board : Board := { receipts, tally := runElection ballots.reverse }
  let (claim, finalCache) ← IO.ofExcept (expectedClaim cache board)
  let env ← IO.ofExcept (materialize phases.compileEnv finalCache)
  let witness ← IO.ofExcept (IxVM.ClaimHarness.buildClaimWitness env claim)
  let vm ← compileVM
  let some idx := vm.getFuncIdx `verify_claim | throw <| IO.userError "Missing verify_claim"
  IO.println s!"Tally: {showTally board.tally}"
  IO.println "Executing the unconditional Eval claim in IxVM..."
  let (out, _, _) ← IO.ofExcept
    ((vm.bytecode.executeIxVM idx witness.input witness.inputIOBuffer).mapError toString)
  unless out.isEmpty do throw <| IO.userError "Unexpected IxVM output"
  IO.println "PASS: IxVM checked the ballots and computed the published tally."
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "board.json") ((Lean.toJson board).pretty ++ "\n")
  -- These files model the copies kept independently by individual voters.
  for i in [:receipts.size] do
    IO.FS.writeFile (dir / s!"voter-{i+1}.receipt") (receipts[i]! ++ "\n")
  if executeOnly then
    IO.println "Rehearsal complete. No proof was generated; the verifier will not accept this directory."
    return
  IO.println "Generating the proof..."
  (← IO.getStdout).flush
  let setupStarted ← IO.monoMsNow
  -- Force the pure FFI setup before starting the proof timer; Lean can otherwise
  -- move it past `monoMsNow` to its first use in `proveIxVM`.
  let systemRef ← IO.mkRef (buildSystem vm)
  let system ← systemRef.get
  let setupElapsed := (← IO.monoMsNow) - setupStarted
  IO.println s!"Prover setup: {setupElapsed} ms."
  let proofStarted ← IO.monoMsNow
  let (_, proof, _) ← IO.ofExcept (system.proveIxVM idx witness.input witness.inputIOBuffer)
  let proofElapsed := (← IO.monoMsNow) - proofStarted
  IO.println s!"Proof generation: {proofElapsed} ms (includes IxVM execution inside the prover)."
  let wrapper : Ixon.Proof := { claim, proof := proof.toBytes }
  IO.ofExcept (verifyProof system vm (Ix.Commit.mkCompileEnv phases) board wrapper)
  IO.FS.writeBinFile (dir / "election.proof") (Ixon.Proof.ser wrapper)
  IO.println s!"Proof generated and verified. Public artifacts: {dir}"
  IO.println "Demo limitation: the current backend is not zero-knowledge; use synthetic ballots only."

def verifyElection (args : List String) : IO Unit := do
  let dir :: args := args
    | throw <| IO.userError "Usage: Verifier DIRECTORY [VOTER.receipt ...] [--show-tampering]"
  let dir : System.FilePath := dir
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (dir / "board.json")))
  let board : Board ← IO.ofExcept (Lean.fromJson? json)
  let wrapper ← IO.ofExcept (Ixon.Proof.de (← IO.FS.readBinFile (dir / "election.proof")))
  let mut own := #[]
  for path in args.filter (· != "--show-tampering") do
    own := own.push ((← IO.FS.readFile path).trimAscii.toString)
  IO.println s!"Published ballot list ({board.receipts.size} receipts):"
  for i in [:board.receipts.size] do
    IO.println s!"  {i+1}. {board.receipts[i]!}"
  let phases ← compileElection (← get_env!)
  let base := Ix.Commit.mkCompileEnv phases
  let vm ← compileVM
  let system := buildSystem vm
  IO.ofExcept (verifyProof system vm base board wrapper own)
  IO.println "PASS: proof binds this exact ballot list to the agreed election program."
  for receipt in own do IO.println s!"PASS: your receipt is included exactly once: {receipt}"
  IO.println s!"Verified tally: {showTally board.tally}"
  if args.contains "--show-tampering" then
    let replacement := toString (Address.blake3 "a substituted ballot".toUTF8)
    let tally := board.tally
    let changedTally : Result := if tally.alice > 0 then
        { tally with alice := tally.alice - 1, bob := tally.bob + 1 }
      else if tally.bob > 0 then
        { tally with bob := tally.bob - 1, charlie := tally.charlie + 1 }
      else { tally with charlie := tally.charlie - 1, alice := tally.alice + 1 }
    for (label, altered) in [
        ("changed tally", { board with tally := changedTally }),
        ("substituted ballot", { board with receipts := board.receipts.set! 0 replacement }),
        ("omitted ballot", { board with receipts := board.receipts.pop }),
        ("duplicated ballot", { board with receipts := board.receipts.push board.receipts[0]! })] do
      match verifyProof system vm base altered wrapper with
      | .error _ => IO.println s!"REJECTED: {label}"
      | .ok _ => throw <| IO.userError s!"Tampering was accepted: {label}"
    let (rewritten, _) ← IO.ofExcept (expectedClaim base { board with tally := changedTally })
    match verifyProof system vm base { board with tally := changedTally }
        { wrapper with claim := rewritten } with
    | .error _ => IO.println "REJECTED: reused proof with a rewritten claim"
    | .ok _ => throw <| IO.userError "Proof replay was accepted"
    let forged := { wrapper with proof := wrapper.proof.extract 0 (wrapper.proof.size / 2) }
    match verifyProof system vm base board forged with
    | .error _ => IO.println "REJECTED: corrupted proof"
    | .ok _ => throw <| IO.userError "Corrupted proof was accepted"

end ZKVoting
