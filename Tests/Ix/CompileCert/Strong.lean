import Ix.CompileCert.StrongCertifier
import Ix.CompileDriver
import Tests.Ix.CompileCert.Compiled
import Tests.Ix.CompileCert.LoweringDefs

/-! The certifier's S path (`Ix/CompileCert/StrongCertifier.lean`) on real
compiler output: the lane's fixture roots (the `compiled` mode's eight
`BlockDefs` roots) and KB's mutual and nested structure-likes
(`LoweringDefs`), compiled here by the Lean compiler. Every root's cone is
decided by the certifier's own `Strong.runCone` (cone input, W association,
Lean-kernel-checked lowering witnesses, normalised source installation,
proposal, `decideStrongCone`). Negative controls, each beside its valid
neighbour (the same cone, accepted first):

* a forged lowering receipt (a witness Lean's kernel accepts but whose subject
  binder is spelled `id (T p⃗)`): the source installation refuses it;
* a mutated target value: (a) the strong check on the cone's real installed
  environments with one target definition body changed refuses; (b) the
  certifier on a record store in which that definition's record is replaced
  refuses the cone;
* a dropped support declaration: the decision without the cone's support
  declaration refuses.
-/

namespace Tests.Ix.CompileCert.Strong

open _root_.Ix.CompileCert _root_.Ix.CompileCert.Strong _root_.Ix.CompileCert.Certifier
open Benchmarks.Kernel.CheckIxeStep

def loweringPrefix : Lean.Name := `Tests.Ix.CompileCert.LoweringDefs

def loweringRoots : List Lean.Name :=
  [`Sized.n, `Sized.vec, `Sized.rest, `Bag.more, `Rose.root, `Rose.children].map (loweringPrefix ++ ·)

/-- Roots whose cone is refused, with the expected class (a stale expectation fails). -/
def expectedRefusals : List (Lean.Name × String) :=
  [(loweringPrefix ++ `Sized.ok, "cone W association refused")]

structure Fixture where
  env : Lean.Environment
  produced : Ixon.Env
  store : RecordStore
  namedAddr : Std.HashMap Lean.Name Address
  refs : Std.HashMap Lean.Name (Array Lean.Name)

def fixture : IO Fixture := do
  let env ← getCompileEnv #[Compiled.prefixName, loweringPrefix]
  let roots := Compiled.roots ++ loweringRoots ++ expectedRefusals.map (·.1)
  let captured ← IO.ofExcept (captureCone env.find? roots 128)
  let compiled ← match ← _root_.Ix.CompileM.compileLeanConsts
      (captured.source.declarations.map (fun ci => (ci.name, ci))) (numWorkers := 1) with
    | .ok out => pure out
    | .error e => throw (IO.userError s!"compiler failed: {e}")
  unless compiled.ungroundedCount == 0 do throw (IO.userError "compiler output contains ungrounded declarations")
  let produced ← IO.ofExcept (Ixon.deEnv compiled.bytes)
  IO.println s!"compiled {captured.source.declarations.length} declarations: {compiled.bytes.size} bytes; Blake3 {Address.blake3 compiled.bytes}"
  let mut store : RecordStore := {}
  for (address, lazy) in produced.consts.toList do
    store := store.insert address (← IO.ofExcept lazy.get)
  let mut namedAddr : Std.HashMap Lean.Name Address := {}
  let mut refs : Std.HashMap Lean.Name (Array Lean.Name) := {}
  for ci in captured.source.declarations do
    let some named := produced.named[_root_.Ix.Name.fromLeanName ci.name]?
      | throw (IO.userError s!"producer omitted {ci.name}")
    namedAddr := namedAddr.insert ci.name named.addr
    refs := refs.insert ci.name (refsOf ci)
  return { env, produced, store, namedAddr, refs }

def Fixture.cone (fx : Fixture) (root : Lean.Name) : Array Lean.Name :=
  (coneOf fx.refs fx.namedAddr.contains #[root]).1

/-- The cone's lowering witnesses, built and checked by Lean's kernel as the
certifier does; with `tamper`, that function's witness is built tampered (and
kept only if Lean's kernel accepts it). -/
def witnessesFor (fx : Fixture) (members : Array Lean.Name)
    (tamper : Option (Lean.Name × _root_.Ix.CompileCert.LoweringLean.LoweringTamper) := none) :
    IO LoweringWitnesses := do
  let functions := _root_.Ix.CompileCert.LoweringLean.projectionFunctionsIn fx.env
    (members.toList.filterMap fx.env.find?)
  let mut out : LoweringWitnesses := []
  for f in functions do
    let how := match tamper with
      | some (g, t) => if g == f then t else .none
      | none => .none
    let witness ← IO.ofExcept (← _root_.Ix.CompileCert.LoweringLean.runMeta fx.env
      (_root_.Ix.CompileCert.LoweringLean.buildLoweringWitness f how))
    match ← _root_.Ix.CompileCert.LoweringLean.admitLoweringWitness fx.env witness with
    | .ok _ => out := out ++ [witness]
    | .error _ => pure ()
  return out

def Fixture.run (fx : Fixture) (root : Lean.Name) (witnesses : LoweringWitnesses)
    (store : RecordStore := fx.store) : IO (ConeOutcome × ConeStats) :=
  runCone fx.env fx.produced store fx.namedAddr 1 root (fx.cone root) witnesses

def outcomeLabel : ConeOutcome → String
  | .certified members => s!"certified ({members.size} declarations)"
  | .failed cls culprit _ => s!"refused: {cls} (at {culprit})"

/-- The cone's pieces, as `runCone` builds them, for the decision-level controls. -/
structure Pieces where
  input : Input
  accepted : AcceptedAssociation input
  installed : SourceNormalizedInstallation input.source input.roots
  proposal : StrongProposal

def Fixture.pieces (fx : Fixture) (root : Lean.Name) (witnesses : LoweringWitnesses) : IO Pieces := do
  let input ← IO.ofExcept (coneInput fx.env fx.produced fx.store fx.namedAddr [root] (fx.cone root))
  let accepted ← match checkCompiled input with
    | .ok a => pure a
    | .error e => throw (IO.userError s!"W on {root}: {Compiled.declineLabel e}")
  let installed ← match installSourceNormalizedWith (sourcePins input accepted.pins) input.source input.roots witnesses with
    | .ok i => pure i
    | .error e => throw (IO.userError s!"installation of {root}: {(sourceErrorLabel e).1}")
  let proposal ← IO.ofExcept (propose accepted installed)
  return ⟨input, accepted, installed, proposal⟩

/-- Replace the innermost body of a λ-telescope that is the variable `i` by `j`. -/
def swapBody (i j : Nat) : _root_.Ix.Kernel.Expr → _root_.Ix.Kernel.Expr
  | .lam d b m => .lam d (swapBody i j b) m
  | .bvar k => if k = i then .bvar j else .bvar k
  | e => e

def require (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"S control failed: {label}")
  IO.println s!"PASS: {label}"

def run : IO Unit := do
  let fx ← fixture
  -- positive: every root's cone S-certified by the certifier's own path
  let roots := Compiled.roots ++ loweringRoots
  let mut certified := 0
  for root in roots do
    let members := fx.cone root
    let witnesses ← witnessesFor fx members
    let (outcome, stats) ← fx.run root witnesses
    IO.println s!"S {root}: {outcomeLabel outcome}; records={stats.records} support={stats.support} witnesses={stats.witnesses}"
    match outcome with
    | .certified _ => certified := certified + 1
    | .failed .. => throw (IO.userError s!"S cone refused: {root}")
  for (root, expected) in expectedRefusals do
    let (outcome, _) ← fx.run root (← witnessesFor fx (fx.cone root))
    let input ← IO.ofExcept (coneInput fx.env fx.produced fx.store fx.namedAddr [root] (fx.cone root))
    let why := match checkCompiled input with
      | .ok _ => "W accepts"
      | .error e => Compiled.declineLabel e
    match outcome with
    | .failed cls _ _ =>
      require s!"expected refusal {root}: {cls} (W: {why})" (cls == expected)
    | .certified _ => throw (IO.userError s!"stale expectation: {root} is now S-certified")
  -- 1. forged lowering receipt, beside its valid neighbour (certified above)
  let mut forged := 0
  for f in [loweringPrefix ++ `Sized.vec, loweringPrefix ++ `Rose.children] do
    let members := fx.cone f
    let tampered ← witnessesFor fx members (some (f, .domain))
    let functions := _root_.Ix.CompileCert.LoweringLean.projectionFunctionsIn fx.env
      (members.toList.filterMap fx.env.find?)
    -- Lean's kernel accepts the tampered equation (the domain is only convertible)
    require s!"forged receipt for {f}: Lean's kernel accepts the tampered equation"
      (tampered.length == functions.length)
    match (← fx.run f tampered).1 with
    | .failed cls _ _ =>
      require s!"forged receipt for {f} refused ({cls}); valid neighbour certified"
        (cls.startsWith "source installation")
      forged := forged + 1
    | .certified _ => throw (IO.userError s!"forged receipt accepted for {f}")
  -- 2a. mutated target value, at the strong check on the cone's real environments
  let first := Compiled.prefixName ++ `first
  let p ← fx.pieces first []
  let bundle ← match admitSupport p.accepted.toAdmittedArtifact p.proposal.support with
    | .ok b => pure b
    | .error e => throw (IO.userError s!"support of {first}: {supportLabel e}")
  let check (target : _root_.Ix.Kernel.Env) := checkStrongAssociation p.installed.env target p.proposal.names
    p.proposal.certificates p.proposal.operationCertificates p.proposal.elementCertificates p.proposal.levels
  let targetFirst := p.proposal.names (sourceName first)
  let mut mutatedRows := 0
  let mutatedConsts := bundle.env.consts.map fun entry => match entry with
    | .defnInfo header value hint =>
      if header.name = targetFirst then .defnInfo header (swapBody 1 0 value) hint else entry
    | _ => entry
  for (a, b) in bundle.env.consts.zip mutatedConsts do
    unless decide (a = b) do mutatedRows := mutatedRows + 1
  require s!"mutated target value: one target row changed ({targetFirst})" (mutatedRows == 1)
  require "mutated target value: valid neighbour, the strong check accepts the real environments"
    (check bundle.env == some true)
  require "mutated target value: the strong check refuses the mutated target"
    (check ⟨mutatedConsts⟩ == some false)
  -- 2b. mutated target value, at the certifier: the definition's record replaced
  let some addrFirst := fx.namedAddr[first]? | throw (IO.userError "no address for first")
  let some addrOther := fx.namedAddr[Compiled.prefixName ++ `getFst]? | throw (IO.userError "no address")
  let some otherRecord := fx.store[addrOther]? | throw (IO.userError "no record")
  match (← fx.run first [] (fx.store.insert addrFirst otherRecord)).1 with
  | .failed cls _ _ => require s!"mutated target record for {first} refused ({cls}); valid neighbour certified" true
  | .certified _ => throw (IO.userError "mutated target record accepted")
  -- 3. dropped support declaration
  let node := Compiled.prefixName ++ `Node.val
  let q ← fx.pieces node (← witnessesFor fx (fx.cone node))
  require s!"dropped support: {node}'s cone needs support ({q.proposal.support.size} declarations)"
    (q.proposal.support.size > 0)
  let valid := decideStrongCone q.accepted q.installed q.proposal
  require "dropped support: valid neighbour, the decision accepts the proposed support"
    (match valid with | .ok _ => true | .error _ => false)
  let dropped := decideStrongCone q.accepted q.installed { q.proposal with support := #[] }
  require "dropped support: the decision refuses without it"
    (match dropped with | .error (.strong _) => true | _ => false)
  IO.println s!"strong model: {certified}/{roots.length} roots S-certified on compiler output; \
    {forged} forged receipts, 2 mutated target values and 1 dropped support declaration refused beside their valid neighbours"

end Tests.Ix.CompileCert.Strong
