import Ix.CompileCert.StrongCertifier
import Ix.CompileCert.SourcePinGen
import Ix.CompileDriver
import IxC.Kernel.PinGen.Certs
import Tests.Ix.CompileCert.Compiled
import Tests.Ix.CompileCert.NatOpDefs

/-! The source-named Nat-operation pins (`Ix/CompileCert/SourcePinGen.lean`,
`SourceNatOpPinData.lean`) and the pinned `Eq` basis under `Quot`, in the
source installation of the strong-model endpoint S:

1. **The committed data** decodes, and equals the variant regenerated from the
   Lean environment of `IxC.Kernel.PinGen.Certs` (a drift tripwire).
2. **The source fold, per operation** (`SourcePinGen.installCone`: the
   normalised source installation, the S route): the operation's source cone
   with the committed variant is accepted (the valid neighbour of each negative
   below, on the same declarations), and the operation is refused (the fold's
   decline names it) with (a) another operation's certificates in its slot,
   valid proofs stated over the wrong operation; (b) its own certificates
   rotated, each a valid proof offered for another of its recurrences; for
   `Nat.div` also (c) `Nat.mod`'s pin and (c') `Nat.sub`'s value in its pin slot; for `Nat.shiftLeft` also
   (d) its recursion certificate with `Nat.mul` read as `Nat.add` (a tampered
   recurrence); and the cone is refused with no pins (M4-d's form).
3. **`Eq` under `Quot`**: a cone with `Quot` installs when Lean's `Eq` (the
   pinned basis, `basisPinHit`) is met first; it is refused when `Quot` is met
   first, when the cone has no `Eq` (the basis completion appends the pinned
   `Eq` after the stream), and when the `Eq` met first is not the pinned basis.
4. **S on compiler output**: the fixture's roots (`NatOpDefs`) and the eight
   operations, compiled here by the Lean→Ix compiler, each decided by the
   certifier's own `Strong.runCone` over the certifier's cone (`coneMembers`):
   all S-certified. Beside them: `Blur.mk` with M4-d's cone (no `Eq` added) is
   refused; `half`'s cone installed with no source pins is refused, and its
   decision with the committed pins accepts.
-/

namespace Tests.Ix.CompileCert.StrongPins

open _root_.Ix.CompileCert _root_.Ix.CompileCert.Strong _root_.Ix.CompileCert.Certifier
open Benchmarks.Kernel.CheckIxeStep

abbrev KName := _root_.Ix.Kernel.Name
abbrev KExpr := _root_.Ix.Kernel.Expr
abbrev PinSet := _root_.Ix.Kernel.NatOpPinSet

def fixturePrefix : Lean.Name := `Tests.Ix.CompileCert.NatOpDefs

def fixtureRoots : List Lean.Name :=
  [`half, `parity, `common, `both, `either, `differ, `double, `halve, `mixed, `Parity.val,
   `Blur.mk].map (fixturePrefix ++ ·)

def require (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"source pins control failed: {label}")
  IO.println s!"PASS: {label}"

def mentions (text needle : String) : Bool := (text.splitOn needle).length > 1

/-- The variant with one operation's pin and proofs replaced. -/
def setOp (ps : PinSet) (opK : KName) (pin : KExpr) (proofs : List KExpr) : PinSet :=
  if opK = _root_.Ix.Kernel.natDivName then { ps with divPin := pin, divProofs := proofs }
  else if opK = _root_.Ix.Kernel.natModName then { ps with modPin := pin, modProofs := proofs }
  else if opK = _root_.Ix.Kernel.natGcdName then { ps with gcdPin := pin, gcdProofs := proofs }
  else if opK = _root_.Ix.Kernel.natLandName then { ps with landPin := pin, landProofs := proofs }
  else if opK = _root_.Ix.Kernel.natLorName then { ps with lorPin := pin, lorProofs := proofs }
  else if opK = _root_.Ix.Kernel.natXorName then { ps with xorPin := pin, xorProofs := proofs }
  else if opK = _root_.Ix.Kernel.natShiftLeftName then
    { ps with shiftLeftPin := pin, shiftLeftProofs := proofs }
  else { ps with shiftRightPin := pin, shiftRightProofs := proofs }

/-- Another operation with as many certificate statements ("stated over the wrong operation"). -/
def partner (op : Lean.Name) : Lean.Name :=
  if op == `Nat.div then `Nat.mod else if op == `Nat.mod then `Nat.div
  else if op == `Nat.gcd then `Nat.land else if op == `Nat.land then `Nat.lor
  else if op == `Nat.lor then `Nat.xor else if op == `Nat.xor then `Nat.land
  else if op == `Nat.shiftLeft then `Nat.shiftRight else `Nat.shiftLeft

def rotate : List KExpr → List KExpr
  | [] => []
  | x :: xs => xs ++ [x]

/-- The operations and their certificate ground, as roots of a source cone. -/
def groundRoots (env : Lean.Environment) (ps : PinSet) (ops : List Lean.Name) : List Lean.Name :=
  (ops.flatMap fun op => op :: (SourcePinGen.groundOf env.find? ps (sourceName op)).toList).eraseDups

/-- Part 1: the committed data against a regeneration. -/
def committedChecks (env : Lean.Environment) : IO PinSet := do
  let committed ← IO.ofExcept SourcePinGen.committedSourceNatOpPins
  let toolchain := (← IO.FS.readFile "lean-toolchain").trimAscii.toString
  let (fresh, log) ← IO.ofExcept (SourcePinGen.generate env.find? toolchain)
  for line in log do IO.println s!"regenerated: {line}"
  require s!"committed source pins ({committed.toolchain}) equal the variant regenerated from the Lean environment"
    (SourcePinGen.sameVariant committed fresh)
  return committed

/-- One refusal at `op` beside its valid neighbour (the same roots with the committed variant). -/
def refusedAt (env : Lean.Environment) (committed : PinSet) (op : Lean.Name) (label : String)
    (tampered : PinSet) (roots : List Lean.Name) : IO Unit := do
  match ← SourcePinGen.installCone env [committed] roots with
  | .ok _ => pure ()
  | .error why => throw (IO.userError s!"{op}: {label}: the valid neighbour is refused: {why}")
  match ← SourcePinGen.installCone env [tampered] roots with
  | .ok _ => throw (IO.userError s!"{op}: {label}: accepted")
  | .error why =>
    require s!"{op}: {label}: refused at {op}, valid neighbour accepted ({why.take 220})"
      (mentions why s!"({op}: no pin variant matched")

/-- Part 2: the source fold per operation. Returns the number of negatives refused. -/
def foldChecks (env : Lean.Environment) (committed : PinSet) : IO Nat := do
  let mut negatives := 0
  for (op, opK, _) in SourcePinGen.certSpecs do
    let roots := groundRoots env committed [op]
    match ← SourcePinGen.installCone env [committed] roots with
    | .ok n => require s!"{op}: source cone ({n} installed declarations) accepted with the committed source pins" true
    | .error why => throw (IO.userError s!"{op}: refused with the committed source pins: {why}")
    match ← SourcePinGen.installCone env [] roots with
    | .ok _ => throw (IO.userError s!"{op}: accepted with no pins")
    | .error why =>
      require s!"{op}: refused with no pins ({why.take 160})" (mentions why "no pin variant matched")
      negatives := negatives + 1
    let (pin, proofs) := SourcePinGen.opEntry committed opK
    -- (a) the certificates of another operation
    let other := partner op
    let (_, otherProofs) := SourcePinGen.opEntry committed (sourceName other)
    refusedAt env committed op s!"(a) the certificates of {other} in its slot"
      (setOp committed opK pin otherProofs) (groundRoots env committed [op, other])
    -- (b) its own certificates rotated
    refusedAt env committed op "(b) its certificates rotated (each offered for another recurrence)"
      (setOp committed opK pin (rotate proofs)) roots
    negatives := negatives + 2
  -- (c) `Nat.div` with `Nat.mod`'s pin
  let (_, divProofs) := SourcePinGen.opEntry committed _root_.Ix.Kernel.natDivName
  let (modPin, _) := SourcePinGen.opEntry committed _root_.Ix.Kernel.natModName
  refusedAt env committed `Nat.div "(c) the pin of Nat.mod in its slot"
    (setOp committed _root_.Ix.Kernel.natDivName modPin divProofs)
    (groundRoots env committed [`Nat.div, `Nat.mod])
  -- (c') `Nat.div` with the value of `Nat.sub` (installed before it) as its pin
  let some (.defnInfo sub) := env.find? `Nat.sub | throw (IO.userError "no Nat.sub")
  let subPin ← IO.ofExcept (exportSourceExpr sub.levelParams sub.value)
  refusedAt env committed `Nat.div "(c') the value of Nat.sub as its pin"
    (setOp committed _root_.Ix.Kernel.natDivName subPin divProofs)
    (groundRoots env committed [`Nat.div])
  -- (d) `Nat.shiftLeft`'s recursion certificate with `Nat.mul` read as `Nat.add`
  let (slPin, slProofs) := SourcePinGen.opEntry committed _root_.Ix.Kernel.natShiftLeftName
  let tampered := match slProofs with
    | p :: rest => kernelRenameAll (fun n => if n = _root_.Ix.Kernel.natMulName then _root_.Ix.Kernel.natAddName else n) p :: rest
    | [] => []
  require "(d) the tamper changes Nat.shiftLeft's recursion certificate" (!decide (tampered = slProofs))
  refusedAt env committed `Nat.shiftLeft "(d) its recursion certificate with Nat.mul read as Nat.add"
    (setOp committed _root_.Ix.Kernel.natShiftLeftName slPin tampered)
    (groundRoots env committed [`Nat.shiftLeft])
  return negatives + 3

/-- Install a source given by its declaration names in this order (the source
order of round-0 groups is the order of the names). -/
def installNames (env : Lean.Environment) (pins : List PinSet) (names : List Lean.Name)
    (roots : List Lean.Name) (extra : List Lean.ConstantInfo := []) : IO (Except String Nat) := do
  let source : Source := ⟨extra ++ names.filterMap env.find?⟩
  if h : CompleteSource source roots then
    let witnesses ← LoweringLean.sourceWitnesses env source
    return match installSourceNormalizedComplete h pins witnesses with
      | .ok installed => .ok installed.declarations.length
      | .error (.checking error position) => .error s!"source fold at {position}: {error}"
      | .error error => .error (sourceErrorLabel error).1
  else return .error "source is not closed"

/-- Part 3: `Eq` under `Quot`. Returns the number of negatives refused. -/
def quotChecks (env : Lean.Environment) (committed : PinSet) : IO Nat := do
  let pins := [committed]
  let quotMessage := "quotient basis requires the pinned Eq basis"
  -- a cone with `Eq` of its own (`Quot.lift`'s type)
  let val := fixturePrefix ++ `Parity.val
  let names ← IO.ofExcept (SourcePinGen.leanCone env.find? [val])
  require s!"{val}: its cone has Quot and Eq" (names.contains `Quot && names.contains `Eq)
  match ← installNames env pins (eqFirst names).toList [val] with
  | .ok n => require s!"{val}: Eq's block first: accepted ({n} installed declarations)" true
  | .error why => throw (IO.userError s!"{val}: Eq first refused: {why}")
  let quotFirst := #[`Quot] ++ names.filter (· != `Quot)
  match ← installNames env pins quotFirst.toList [val] with
  | .ok _ => throw (IO.userError s!"{val}: Quot before Eq accepted")
  | .error why =>
    require s!"{val}: the same declarations with Quot first: refused ({why.take 160})" (mentions why quotMessage)
  -- a cone without `Eq`
  let blur := fixturePrefix ++ `Blur.mk
  let bare ← IO.ofExcept (SourcePinGen.leanCone env.find? [blur])
  require s!"{blur}: its cone has Quot and no Eq" (bare.contains `Quot && !bare.contains `Eq)
  match ← installNames env pins bare.toList [blur] with
  | .ok _ => throw (IO.userError s!"{blur}: accepted with the pinned Eq appended after Quot")
  | .error why =>
    require s!"{blur}: no Eq in the cone (the completion appends the pinned Eq after Quot): refused ({why.take 160})"
      (mentions why quotMessage)
  let withEq ← IO.ofExcept (SourcePinGen.leanCone env.find? [blur, `Eq])
  match ← installNames env pins (eqFirst withEq).toList [blur] with
  | .ok n => require s!"{blur}: with Lean's Eq first (the pinned basis): accepted ({n} installed declarations)" true
  | .error why => throw (IO.userError s!"{blur}: Lean's Eq first refused: {why}")
  -- an `Eq` that is not the pinned basis, met first
  let notPinned : Lean.ConstantInfo := .axiomInfo
    { name := `Eq, levelParams := [], type := .sort .zero, isUnsafe := false }
  match ← installNames env pins bare.toList [blur] [notPinned] with
  | .ok _ => throw (IO.userError s!"{blur}: accepted over a non-pinned Eq")
  | .error why => require s!"{blur}: over a non-pinned Eq (an axiom Eq : Prop, met first): refused ({why.take 160})" true
  return 3

structure Fixture where
  env : Lean.Environment
  produced : Ixon.Env
  store : RecordStore
  namedAddr : Std.HashMap Lean.Name Address
  refs : Std.HashMap Lean.Name (Array Lean.Name)
  names : Array Lean.Name

/-- The fixture's roots, the eight operations and their certificate ground, compiled here. -/
def fixture (env : Lean.Environment) (committed : PinSet) : IO Fixture := do
  let ops := SourcePinGen.certSpecs.map (·.1)
  let roots := fixtureRoots ++ groundRoots env committed ops ++ [`Nat.pred, `Eq, `sorryAx]
  let names ← IO.ofExcept (SourcePinGen.leanCone env.find? roots)
  let declarations := names.toList.filterMap env.find?
  let compiled ← match ← _root_.Ix.CompileM.compileLeanConsts
      (declarations.map (fun ci => (ci.name, ci))) (numWorkers := 1) with
    | .ok out => pure out
    | .error e => throw (IO.userError s!"compiler failed: {e}")
  unless compiled.ungroundedCount == 0 do throw (IO.userError "compiler output contains ungrounded declarations")
  let produced ← IO.ofExcept (Ixon.deEnv compiled.bytes)
  IO.println s!"compiled {declarations.length} declarations: {compiled.bytes.size} bytes; Blake3 {Address.blake3 compiled.bytes}"
  let mut store : RecordStore := {}
  for (address, lazy) in produced.consts.toList do
    store := store.insert address (← IO.ofExcept lazy.get)
  let mut namedAddr : Std.HashMap Lean.Name Address := {}
  let mut refs : Std.HashMap Lean.Name (Array Lean.Name) := {}
  for ci in declarations do
    let some named := produced.named[_root_.Ix.Name.fromLeanName ci.name]?
      | throw (IO.userError s!"producer omitted {ci.name}")
    namedAddr := namedAddr.insert ci.name named.addr
    refs := refs.insert ci.name (refsOf ci)
  return { env, produced, store, namedAddr, refs, names }

def witnessesFor (env : Lean.Environment) (members : Array Lean.Name) : IO LoweringWitnesses := do
  IO.ofExcept (← LoweringLean.kernelCheckedWitnesses env
    (LoweringLean.projectionFunctionsIn env (members.toList.filterMap env.find?)))

def outcomeLabel : ConeOutcome → String
  | .certified members => s!"certified ({members.size} declarations)"
  | .failed cls culprit _ => s!"refused: {cls} (at {culprit})"

/-- Part 4: S on compiler output. Returns (certified roots, roots, refusals). -/
def strongChecks (env : Lean.Environment) (committed : PinSet) : IO (Nat × Nat × Nat) := do
  let fx ← fixture env committed
  let readerPins ← IO.ofExcept _root_.Ix.Kernel.Reader.defaultPins
  let ground := natOpPinGround fx.env fx.store fx.namedAddr readerPins fx.names (fun _ => true)
  let roots := fixtureRoots ++ SourcePinGen.certSpecs.map (·.1) ++ [`sorryAx]
  let mut certified := 0
  for root in roots do
    let (members, missing) := coneMembers fx.refs fx.namedAddr.contains ground root
    unless missing.isEmpty do throw (IO.userError s!"S {root}: cone references outside the fixture: {missing}")
    let (outcome, stats) ← runCone fx.env fx.produced fx.store fx.namedAddr 1 root members
      (← witnessesFor fx.env members)
    IO.println s!"S {root}: {outcomeLabel outcome}; records={stats.records} support={stats.support} \
      witnesses={stats.witnesses}; ms: W {stats.msW}, installation {stats.msInstall}, strong {stats.msStrong}"
    match outcome with
    | .certified _ => certified := certified + 1
    | .failed .. => throw (IO.userError s!"S cone refused: {root}")
  -- M4-d's cone for `Blur.mk`: no `Eq` added, discovery order
  let blur := fixturePrefix ++ `Blur.mk
  let (bare, _) := coneOf fx.refs fx.namedAddr.contains #[blur]
  require s!"{blur}: M4-d's cone has no Eq" (!bare.contains `Eq)
  match (← runCone fx.env fx.produced fx.store fx.namedAddr 1 blur bare (← witnessesFor fx.env bare)).1 with
  | .failed cls _ _ =>
    require s!"{blur}: M4-d's cone refused ({cls}); the certifier's cone (Eq first) certified above"
      (mentions cls "quotient basis requires the pinned Eq basis")
  | .certified _ => throw (IO.userError s!"{blur}: M4-d's cone certified")
  -- `half` with no source pins, beside the committed ones
  let half := fixturePrefix ++ `half
  let (members, _) := coneMembers fx.refs fx.namedAddr.contains ground half
  let witnesses ← witnessesFor fx.env members
  let input ← IO.ofExcept (coneInput fx.env fx.produced fx.store fx.namedAddr [half] members)
  let accepted ← match checkCompiled input with
    | .ok a => pure a
    | .error e => throw (IO.userError s!"W on {half}: {Compiled.declineLabel e}")
  match installSourceNormalizedWith [] input.source input.roots witnesses with
  | .ok _ => throw (IO.userError s!"{half}: installed with no source pins")
  | .error e =>
    let (cls, _) := sourceErrorLabel e
    require s!"{half}: the cone's source installation with no pins refused ({cls.take 160})"
      (mentions cls "no pin variant matched")
  let installed ← match installSourceNormalizedWith (sourcePins input accepted.pins) input.source input.roots witnesses with
    | .ok i => pure i
    | .error e => throw (IO.userError s!"{half}: installation with the committed pins: {(sourceErrorLabel e).1}")
  let proposal ← IO.ofExcept (propose accepted installed)
  require s!"{half}: valid neighbour, the decision with the committed source pins accepts"
    (match decideStrongCone accepted installed proposal with | .ok _ => true | .error _ => false)
  -- `sorryAx`: the checker skips its record on both sides, so the source has no row to pull
  -- back and the proposal adds no support (certified above); beside it, (i) a support axiom
  -- row is refused by the support fold, (ii) a `sorryAx` of another shape is refused by W
  let sorry_ := `sorryAx
  let (sMembers, _) := coneMembers fx.refs fx.namedAddr.contains ground sorry_
  let sInput ← IO.ofExcept (coneInput fx.env fx.produced fx.store fx.namedAddr [sorry_] sMembers)
  let sAccepted ← match checkCompiled sInput with
    | .ok a => pure a
    | .error e => throw (IO.userError s!"W on sorryAx: {Compiled.declineLabel e}")
  let sInstalled ← match installSourceNormalizedWith (sourcePins sInput sAccepted.pins) sInput.source sInput.roots [] with
    | .ok i => pure i
    | .error e => throw (IO.userError s!"installation of sorryAx's cone: {(sourceErrorLabel e).1}")
  require "sorryAx: the source fold installs no row for it, the target fold none either"
    ((sInstalled.env.find? (sourceName sorry_)).isNone &&
      (sAccepted.env.find? (sourceName sorry_)).isNone)
  let sProposal ← IO.ofExcept (propose sAccepted sInstalled)
  require "sorryAx: no support proposed; valid neighbour, the decision accepts"
    (sProposal.support.isEmpty &&
      match decideStrongCone sAccepted sInstalled sProposal with | .ok _ => true | .error _ => false)
  let axiomRow : _root_.Ix.Kernel.Declaration :=
    .axiomDecl ⟨(sourceName sorry_).str "_ix_support", [], .sort .zero⟩
  match decideStrongCone sAccepted sInstalled { sProposal with support := #[axiomRow] } with
  | .error (.support e) => require s!"sorryAx: a support axiom row refused by the support fold ({supportLabel e})" true
  | .error (.strong _) => throw (IO.userError "sorryAx: the support axiom row was admitted")
  | .ok _ => throw (IO.userError "sorryAx: the decision accepted a support axiom row")
  let tampered : Source := ⟨sInput.source.declarations.map fun ci => match ci with
    | .axiomInfo v => if v.name == sorry_ then .axiomInfo { v with type := .sort .zero } else ci
    | _ => ci⟩
  match checkCompiled { sInput with source := tampered } with
  | .error e => require s!"sorryAx stated as `Prop`: refused by W ({Compiled.declineLabel e |>.take 160})" true
  | .ok _ => throw (IO.userError "sorryAx of another shape accepted by W")
  return (certified, roots.length, 4)

def run : IO Unit := do
  let env ← getCompileEnv #[fixturePrefix, `IxC.Kernel.PinGen.Certs]
  let committed ← committedChecks env
  let foldNegatives ← foldChecks env committed
  let quotNegatives ← quotChecks env committed
  let (certified, roots, coneNegatives) ← strongChecks env committed
  IO.println s!"source pins: committed variant equals its regeneration; 8/8 operations accepted by the source \
    fold, {foldNegatives} tampered or absent variants refused beside their valid neighbours; Eq under Quot: \
    accepted first, {quotNegatives} refusals beside it; S: {certified}/{roots} roots S-certified on compiler \
    output, {coneNegatives} certifier-level controls refused beside their valid neighbours"

end Tests.Ix.CompileCert.StrongPins
