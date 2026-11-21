import Tests.Ix.IxVM.Harness

/-! # Safety of the references a claim or binding walk traverses

Sharing-table entries participate even when conversion never reaches them. A safe source
checks each uncovered target and its projection owner; unsafe-origin walks retain their
behavior. Operation certificates must be standalone theorem records, so their raw reference
walk covers the proof value actually checked after substitution.
-/

namespace Tests.Ix.IxVM.SafeReferences
open IxVM.ClaimHarness

private def recordMessage := "safe walked source references an unsafe or partial record"
private def ownerMessage := "safe walked source references an unsafe or partial owner"
private def certificateMessage := "an operation certificate is not a standalone theorem"

private def put (env : Ixon.Env) (c : Ixon.Constant) : Ixon.Env × Address :=
  let a := Address.blake3 (Ixon.serConstant c)
  let env := env.storeConst a c
  let env := match c.info with
    | .defn _ | .dPrj _ => { env with anonHints := env.anonHints.insert a .opaque }
    | _ => env
  (env, a)

private def base : Except String Ixon.Env := do
  withRoleTable {} (← Ix.Kernel.Reader.defaultTableBytes)

private def unsafeAxiom : Ixon.Constant :=
  ⟨.axio ⟨true, 0, .sort 0⟩, #[], #[], #[.zero], #[]⟩

private def simpleDefinition (safety : Ix.DefinitionSafety) : Ixon.Definition :=
  ⟨.defn, safety, {}, 0, .sort 1, .sort 0⟩

private def unused (target : Address) : Ixon.Constant :=
  ⟨.defn (simpleDefinition .safe), #[.ref 0 #[]], #[target], #[.zero, .succ .zero], #[]⟩

private def typingCase (label : String) (env : Ixon.Env) (target : Address)
    (assumed environment accept : Bool) (reject : Option String := none) : Except String Case := do
  let some binding := env.roleBinding | throw "missing role binding"
  let ctx ← Ix.ClaimContext.ofBinding binding.address assumed
  if environment then
    let some tree := Ix.AssumptionTree.canonical #[target] | throw "empty owned tree"
    Case.ofClaim label env (.checkEnv ctx tree.root none)
      (({} : Std.HashMap Address Ix.AssumptionTree).insert tree.root tree) accept reject
  else
    Case.ofClaim label env (.check ctx target none) {} accept reject

private def sharingCase (guarded assumed environment : Bool) (mode : Nat) : Except String Case := do
  let env ← base
  let ax := { unsafeAxiom with info := .axio ⟨mode != 2, 0, .sort 0⟩ }
  let (env, x) := put env ax
  let reachable := mode == 3
  let c : Ixon.Constant :=
    ⟨.defn { simpleDefinition .safe with
        typ := if reachable then .sort 0 else .sort 1
        value := if reachable then .ref 0 #[] else .sort 0 },
      (if mode == 0 then #[] else #[.ref 0 #[]]),
      (if mode == 0 then #[] else #[x]), #[.zero, .succ .zero], #[]⟩
  let (env, a) := put env c
  let target := if mode == 4 then x else a
  let label := match mode with
    | 0 => "safe definition without a sharing reference"
    | 1 => "unused sharing reference to an unsafe unbound axiom"
    | 2 => "unused sharing reference to a safe unbound axiom"
    | 3 => "reachable unsafe reference"
    | _ => "unsafe direct seed"
  let reject := match mode with
    | 1 => if guarded then some recordMessage else
        if environment then some "claim seed is unsafe or partial" else none
    | 2 => some "an axiom that is not one of Lean's standard axioms"
    | 3 => some "safe constant references an unsafe constant"
    | 4 => some "claim seed is unsafe or partial"
    | _ => none
  typingCase s!"checkEnv={environment}, assumed={assumed}: {label}" env target assumed environment
    (mode == 0 || (mode == 1 && !guarded && !environment)) reject

private def ownerCase (guarded assumed unsafeOwner : Bool) : Except String Case := do
  let env ← base
  let block : Ixon.Constant :=
    ⟨.muts #[.defn (simpleDefinition (if unsafeOwner then .unsaf else .safe))],
      #[], #[], #[.zero, .succ .zero], #[]⟩
  let (env, b) := put env block
  let (env, p) := put env ⟨.dPrj ⟨0, b⟩, #[], #[], #[], #[]⟩
  let (env, a) := put env (unused p)
  typingCase s!"assumed={assumed}: unused projection reference, unsafe owner={unsafeOwner}"
    env a assumed false (!unsafeOwner || !guarded)
    (if unsafeOwner && guarded then some ownerMessage else none)

private def coveredCase : Except String Case := do
  let env ← base
  let table ← Ix.Kernel.Reader.defaultTable
  let (env, x) := put env unsafeAxiom
  let table := { table with bound := table.bound.map fun (r, a) =>
    (r, if r == Ix.Kernel.Role.natPred then x else a) }
  table.check
  let env ← withRoleTable env table.toBytes
  let (env, a) := put env (unused x)
  typingCase "assumed table: covered operation reference stays unwalked" env a true false true

private def inertCase (assumed : Bool) : Except String Case := do
  let env ← base
  let table ← Ix.Kernel.Reader.defaultTable
  let some x := table.addressOf? .trustCompiler | throw "missing trustCompiler"
  let (env, a) := put env (unused x)
  typingCase s!"assumed={assumed}: inert reference retains its refusal" env a assumed false false
    (some "a constant uses an inert axiom")

private def assumedLeafCase (guarded assumed environment : Bool) : Except String Case := do
  let env ← base
  let (env, x) := put env unsafeAxiom
  let (env, a) := put env (unused x)
  let some binding := env.roleBinding | throw "missing binding"
  let ctx ← Ix.ClaimContext.ofBinding binding.address assumed
  let some asm := Ix.AssumptionTree.canonical #[x] | throw "empty assumptions"
  let some owned := Ix.AssumptionTree.canonical #[a] | throw "empty owned tree"
  let trees := (({} : Std.HashMap Address Ix.AssumptionTree).insert asm.root asm).insert owned.root owned
  let claim := if environment then .checkEnv ctx owned.root (some asm.root)
    else .check ctx a (some asm.root)
  let c ← Case.ofClaim s!"checkEnv={environment}, assumed={assumed}: assumed leaf stays unloaded"
    env claim trees true
  return { c with exercises := if guarded then some "KernelClaim::assert_safe_record_refs_under" else none }

private def bindingCase (label : String) (env : Ixon.Env) (accept : Bool)
    (reject : Option String := none) : Except String Case := do
  let some binding := env.roleBinding | throw "missing role binding"
  Case.ofClaim label env (.binding (← Ix.SpecDigest.specDigest) binding.address) {} accept reject

private def standardAxiomCase (guarded : Bool) : Except String Case := do
  let env ← base
  let table ← Ix.Kernel.Reader.defaultTable
  let some a := table.addressOf? .propext | throw "missing propext"
  let some c := env.getConst? a | throw "missing propext record"
  let (env, x) := put env unsafeAxiom
  let c := { c with sharing := c.sharing.push (.ref c.refs.size.toUInt64 #[]), refs := c.refs.push x }
  let (env, a') := put env c
  let table := { table with bound := table.bound.map fun (r, b) =>
    (r, if r == Ix.Kernel.Role.propext then a' else b) }
  let env ← withRoleTable env table.toBytes
  bindingCase "binding: standard axiom has an unused unsafe reference" env false
    (some (if guarded then recordMessage else "an axiom that is not one of Lean's standard axioms"))

private def certificateCase (guarded : Bool) (mode : Nat) : Except String Case := do
  let env ← base
  let table ← Ix.Kernel.Reader.defaultTable
  let mut selected : Option (Ix.Kernel.Role × Nat × Address) := none
  for (r, entries) in table.evidence do
    if selected.isNone then
      if let .ops := (r.spec (md := .anon)).kind then
        for (e, i) in entries.zipIdx do
          if selected.isNone then
            if let .proof a := e then selected := some (r, i, a)
  let some (r, index, a) := selected | throw "no operation proof certificate"
  let some c := env.getConst? a | throw "missing certificate"
  let .defn d := c.info | throw "default certificate is not standalone"
  if d.kind != .thm then throw "default certificate is not a theorem"
  let (env, replacement) ← if mode == 0 then do
      let (env, x) := put env unsafeAxiom
      pure (put env { c with
        sharing := c.sharing.push (.ref c.refs.size.toUInt64 #[])
        refs := c.refs.push x })
    else do
      let ms := if mode == 1 then #[.defn d]
        else #[.defn d, .defn (simpleDefinition .unsaf)]
      let (env, b) := put env { c with info := .muts ms }
      pure (put env ⟨.dPrj ⟨0, b⟩, #[], #[], #[], #[]⟩)
  let table := { table with evidence := table.evidence.map fun (role, es) =>
    (role, if role == r then (es : Array (Ix.Kernel.Evidence Address)).set! index (.proof replacement) else es) }
  table.check
  let env ← withRoleTable env table.toBytes
  let label := match mode with
    | 0 => "standalone certificate with an unused unsafe reference"
    | 1 => "projected theorem certificate with a safe owner"
    | _ => "projected theorem certificate with an unsafe owner"
  bindingCase s!"binding: {label}" env (!guarded && mode != 2)
    (if guarded then some (if mode == 0 then recordMessage else certificateMessage)
      else if mode == 2 then some "mutual block mixes safe members with unsafe or partial ones" else none)

/-- The same fixtures can be compared with a retained pre-guard artifact explicitly. -/
def runWithGuard (guarded : Bool) : IO UInt32 := do
  let mut cases : Array Builder := #[]
  for environment in [false, true] do
    for assumed in [false, true] do
      for mode in List.range 5 do
        cases := cases.push (fun _ => sharingCase guarded assumed environment mode)
  for environment in [false, true] do
    for assumed in [false, true] do
      cases := cases.push (fun _ => assumedLeafCase guarded assumed environment)
  for assumed in [false, true] do
    for unsafeOwner in [false, true] do
      cases := cases.push (fun _ => ownerCase guarded assumed unsafeOwner)
    cases := cases.push (fun _ => inertCase assumed)
  cases := cases.push (fun _ => coveredCase)
  cases := cases.push (fun _ => do bindingCase "binding: unchanged full default table" (← base) true)
  cases := cases.push (fun _ => standardAxiomCase guarded)
  for mode in List.range 3 do cases := cases.push (fun _ => certificateCase guarded mode)
  runCases "ixvm-safe-references" cases (jobs := 4) (circuit := some true)

/-- PR fast suite: all out-of-scope (`assumed = true`) reference checks plus
representative `assumed = false` host smokes. The five full `.binding` runs
(whose soundness is proved by `CircuitComposed` and whose default-table run is
pinned in `ixvm-kernel-checks`) stay in `runFull` (`ci:nightly`). -/
def run : IO UInt32 := do
  let mut cases : Array Builder := #[]
  for environment in [false, true] do
    for mode in List.range 5 do
      cases := cases.push (fun _ => sharingCase true true environment mode)
    cases := cases.push (fun _ => assumedLeafCase true true environment)
  -- Representative `assumed = false` Rust-host smokes.
  cases := cases.push (fun _ => sharingCase true false false 0)
  cases := cases.push (fun _ => assumedLeafCase true false false)
  for unsafeOwner in [false, true] do
    cases := cases.push (fun _ => ownerCase true true unsafeOwner)
  cases := cases.push (fun _ => ownerCase true false true)
  cases := cases.push (fun _ => inertCase true)
  cases := cases.push (fun _ => coveredCase)
  runCases "ixvm-safe-references" cases (jobs := 4) (circuit := some true)

/-- Full nightly suite, including all five `.binding` runs. -/
def runFull : IO UInt32 := runWithGuard true

/-- A direct transitive walk is allowed to originate outside the logic. These controls use
`IX_AIUR_WALK_ARTIFACT`, an export containing `IxVM::verify_transitive`, rather than a claim
entry that must reject every unsafe seed. -/
def runUnsafeOrigins : IO UInt32 := do
  let some artifact ← IO.getEnv "IX_AIUR_WALK_ARTIFACT"
    | throw (IO.userError "IX_AIUR_WALK_ARTIFACT must name a verify_transitive artifact")
  let host ← programHost
  let go (dir : System.FilePath) : IO UInt32 := do
    IO.FS.createDirAll dir
    let mut cases : Array Ix.AiurInvocation.Case := #[]
    for projection in [false, true] do
      let env ← IO.ofExcept base
      let (env, x) := put env unsafeAxiom
      let body : Ixon.Constant :=
        ⟨(if projection then .muts #[.defn (simpleDefinition .unsaf)]
          else .defn (simpleDefinition .unsaf)),
          #[.ref 0 #[]], #[x], #[.zero, .succ .zero], #[]⟩
      let (env, a) := put env body
      let (env, target) := if projection then put env ⟨.dPrj ⟨0, a⟩, #[], #[], #[], #[]⟩
        else (env, a)
      let env ← IO.ofExcept (withDefaultRoleBinding env)
      let buffer := addEntries env (closureFrom env target true).contains (seedBinding env default)
      cases := cases.push {
        label := s!"unsafe-origin transitive walk, projection={projection}"
        accept := true
        exercises := some "KernelClaim::assert_safe_record_refs_under"
        invocation := Ix.Cli.FormalAiur.invocation (target.hash.data.map Aiur.G.ofUInt8)
          buffer "IxVM::verify_transitive" }
    let path := dir / "unsafe-origins.ixt"
    IO.FS.writeBinFile path (Ix.AiurInvocation.encodeCases cases)
    let out ← IO.Process.output {
      cmd := host
      args := #["test", artifact, path.toString]
      env := #[(circuitVerdictVar, some "1")] }
    IO.print out.stdout
    IO.eprint out.stderr
    unless (circuitAcknowledgement out.stdout).any (· > 0) do
      throw (IO.userError "host did not enforce deferred assertions")
    return out.exitCode
  match ← IO.getEnv "IX_TEST_OUTPUT_DIR" with
  | some dir => go (System.FilePath.mk dir / "unsafe-origins")
  | none => IO.FS.withTempDir go

end Tests.Ix.IxVM.SafeReferences
