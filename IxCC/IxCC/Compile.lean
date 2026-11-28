import IxCC.Recheck
import IxCC.Recheck.Rc.Produce
import IxCC.Src.AutoHints
import IxCC.Exe
import IxCC.X86.Exe.Cert

/-! # `compile`: the compiler as one pure function (`IxCC.Compile`)

```text
compile : (envBytes : ByteArray) → (target : Ixon.Address) → (opts : Options) → Except Err Output
```

The function an argument-carrying executable's argument is about: a pure, total
function of the committed environment's bytes, the address of the constant to
compile, and the options. No `IO`, no environment variable, no clock, no file, no
process, and no input beside its three arguments: the unfolding hints a sidecar
used to supply are derived inside (`Src.AutoHints.discover`, from the theorem
statements of the environment itself).

```text
envBytes ─decode─→ ─kernel acceptance, N5 modes─→ ─hints derived, reach, read─→ Input      (ingress)
  ─deterministic producer (untrusted)─→ certificate ─the proved checker─→ Artifact
  ─the seed closure through the kernel's logical entry (KF-4)─                            (check)
  ─[hook (a): shape decision]─ ─[hook (b): grounding checks]─
  ─Exe.build / Exe.buildMachine (written and checked)─→ executable bytes, claim           (build)
```

**The certificate is an internal value.** `compile` is the deterministic producer
followed by the certificate checker (`Recheck.run` or `RcReplay.run`, behind Stage A
and the definition assertions: `checkZero`, `checkPlain`). The executable is built
from the artifact the checker made, never from anything the producer computed, so
`compile … = .ok out` implies that the checker accepted a certificate for the
ingested program, and the checker's soundness theorems apply with no statement
about any producer heuristic (`IxCC.Compile.Proof`, `IxCCCorrect.Compile`). The
certificate's file text is returned beside the executable (`Output.cert`) for the
developer path that embeds it; it is not part of the claim.

**Two stages.** `check` is everything up to and including the certificate checker;
`build` writes the executable and makes the claim. `compile` is `check` then
`build`. The seam between them is where the two further decisions of the certified
route are called (marked `HOOK` in `compile` below): they read what `check`
returns and only refuse, so the function assembled with them has `compile`'s
signature and refines it.

**Scope.** The default certified pipeline: the zero-RC-format certificate on the
immortal backend, the plain-RC certificate, and the automatic choice between them.
Not here: `--opt` (the `Lir.Opt` passes; see the note on `compile`), and the
uncertified `--bignat` path, whose library comes from outside the process.

**Checks.** Inside `compile`: the certified kernel's acceptance of the whole
environment at `opts.kernelLimits` and the N5 mode check (ingress); that the
program's first root is `target`; the function-parameter refusal; Stage A (the
certificate's relevance annotation is the annotator's); the replay; the decoded
definition assertions; the seed-closure check of `CompileClaim.verifyBytes` and
`verify-exe` (`seedClosure`: the kernel a second time, through its logical entry,
on the records the target and the table's theorems reach, under the committed
default role table, which the environment's must restrict); the executable's own
fragment (`Exe.fragment` or `Exe.machine`: all-`Nat` parameters, a result the
shell renders), which implies the root checks of `CompileClaim.verifyProgram`; and
the written file's structural and shell checks. So a file `compile` returns,
packaged with its certificate, is one `verify-exe` accepts: `compile` refuses
exactly where the verifier would. -/

set_option autoImplicit false

namespace IxCC.Compile

open IxCC.Recheck

/-! ## Options, claim, output -/

/-- The reference-counting policy request (`ixcc compile --rc`). -/
inductive Rc where
  /-- A zero-RC-format certificate on the immortal backend (nothing is freed). -/
  | off
  /-- Plain reference counting; a program outside its domain is declined. -/
  | on
  /-- Zero RC when `Own.Plain.selectRcPolicyForSrc` selects it; plain RC when it
  selects that and the plain-RC certificate is produced and replayed; otherwise the
  immortal backend. -/
  | auto
  deriving DecidableEq, Repr, Inhabited

/-- **The options**: exactly the inputs, beside the environment and the target,
that may change the output. Each is a field of the claim (`Claim.options`). -/
structure Options where
  /-- The policy request. It selects the producer (and with it the certificate's
  format and the checker that replays it), so it can change every byte of the
  object. The policy compiled under is a function of the request and the program
  (`Checked.policy`). -/
  rc : Rc := .off
  /-- The executable's kind: `plain` (decimal arguments, the result printed) or
  `machine` (a numeric state machine run by the generic shell). It selects the
  shell written around the object. -/
  kind : X86.Exe.Cert.ExeKind := .plain
  /-- The program stack and the heap region the file reserves, in bytes
  (`X86.Exe.Layout`). They are in the file's program headers and in the shell's
  constants. -/
  layout : X86.Exe.Layout := {}
  /-- The certified kernel's batch limits at ingress. A limit only turns an
  acceptance into a decline, so an output made under some limits is the output
  under any larger ones; `workers` (how many tasks the kernel's second phase
  runs on) cannot change a verdict at all (`Ix.Kernel.Admission.Limits`). -/
  kernelLimits : Ix.Kernel.Admission.Limits := Src.KernelFront.defaultLimits
  /-- The root's name: the object's symbol `cx_<name>` and the name the certificate
  gives the root. `none` names it `root0`. It changes the object and the certificate
  (not the executable's behaviour), so it is an option and in the claim; the command
  line passes the name a `--root NAME=ADDR` (or a named envelope's `--root NAME`) gives. -/
  name : Option String := none
  deriving Repr

instance : Inhabited Options := ⟨{}⟩

/-- **The claim**: what `compile` says about its output, as public data. The
first five fields are the claim proper: the environment, the target, the
options, the executable's digest (the compiler's own address is not something a
Lean function can name; it is the verifying key of whatever evaluates `compile`).
The last four are functions of those, stated for a consumer. -/
structure Claim where
  /-- Merkle root of the environment's constants (`Ixon.V3.Env.root`). -/
  env : Ixon.Address
  /-- Address of the environment's role table (`Ixon.V3.Env.bindingAddress`; the
  kernel admits only role-bound environments). -/
  roleTable : Ixon.Address
  /-- Address of the compiled constant. -/
  target : Ixon.Address
  /-- The options the executable was compiled under. -/
  options : Options
  /-- BLAKE3 of the executable's bytes (`Output.exe`). -/
  exe : Ixon.Address
  /-- The policy compiled under. -/
  policy : CompilePolicy
  /-- The root's parameter count: the number of decimal arguments of a plain
  executable. -/
  arity : Nat
  /-- How a plain executable renders its result. -/
  result : X86.Exe.ResultKind
  /-- BLAKE3 of the relocatable object the executable's text was taken from
  (today's `CompileClaim.elfHash`). -/
  object : Ixon.Address
  deriving Repr

/-- Today's six-field claim of the same compile (`IxCC.CompileClaim`), which the
`.ix.cert` v1 payload of the developer path carries. -/
def Claim.legacy (c : Claim) : CompileClaim :=
  { env := c.env, roleTable := some c.roleTable, target := c.target, policy := c.policy
    abiArity := c.arity, elfHash := c.object }

/-- **What `compile` returns.** -/
structure Output where
  claim : Claim
  /-- The standalone executable: a static x86-64 Linux `ET_EXEC` file with no
  section table, exactly the bytes `Exe.build` (or `Exe.buildMachine`) wrote and
  checked. -/
  exe : ByteArray
  /-- The certificate's file text the checker accepted. Not part of the claim; the
  developer path embeds it (`X86.Exe.Cert`, mode `0x01`). -/
  cert : String

/-! ## Small steps -/

/-- Refuse with `e` unless `cond`. -/
def require (cond : Bool) (e : Err) : Except Err Unit :=
  if cond then .ok () else .error e

/-- The value of an option, or the refusal `e`. -/
def orRefuse {α : Type} (e : Err) : Option α → Except Err α
  | some a => .ok a
  | none => .error e

def ingressErr (code message : String) : Err := { stage := .ingress, code, message }

/-! ## Ingress, with the hints derived inside -/

/-- **Ingress of a decoded environment for chosen roots, with no sidecar**: the
certified kernel's acceptance of the whole environment under `limits`
(`Src.KernelFront.accept`; only a role-bound environment is accepted), the N5 mode
check, the unfolding proposals discovered from the environment's theorem
statements under the admitted role table's pins (`Src.AutoHints.discover`), the
records the roots, the pins and the proposals reach (`Src.Ingress.reach`), IxCC's
reading of them (`Src.Ingress.readConsts`), and the program read against the
kernel's reading (`Src.KernelFront.Reading.build`). A root without a name is named
`root<i>`. This is `Recheck.ingress` with the sidecar's proposals replaced by the
derived ones; it is the pure function the command line's `ingressAuto` computes. -/
def ingressRoots (env : Ixon.V3.Env) (chosen : Array (Ixon.Address × Option String))
    (limits : Ix.Kernel.Admission.Limits) : Except Err Input := do
  let acc ← (Src.KernelFront.accept env limits).mapError fun r =>
    { stage := .ingress, code := (r.limit.map kernelLimitCode).getD "kernel", message := r.report }
  let () ← (Src.KernelFront.defaultModeCheck acc).mapError fun r =>
    { stage := .ingress, code := "mode-check", message := r.report }
  let pins := Src.KernelFront.pinsOfTable acc.table
  let names := chosen.toList.zipIdx.map fun ((_, n), i) => n.getD s!"root{i}"
  let namedRoots := chosen.zipIdx.map fun ((a, n), i) => (a, some (n.getD s!"root{i}"))
  let hints : Src.Hints := { roots := namedRoots, proposals := Src.AutoHints.discover env pins }
  let records ← (Src.Ingress.reach env (Src.Ingress.Seeds.of hints pins)).mapError fun m =>
    ingressErr "decode" m
  let p ← (Src.Ingress.readConsts env records (namedRoots.map (·.1))).mapError fun m =>
    ingressErr "ingress" m
  let p := { p with known := { pins } }
  let p := { p with known := Src.Pinned.known p }
  let rd ← (Src.KernelFront.Reading.build acc p).mapError fun m => ingressErr "faithful" m
  pure { env, hints, program := p, names, kernel := { acc, rd, fe := Ix.Kernel.mkFEnv acc.env } }

/-- **Ingress of the environment's bytes for one target named `name`**: the envelope
decoded (`Ixon.V3.decodeAnonymousEnv`: every constant and blob under its address), the
target a constant of it, and `ingressRoots` with the target as the only root. -/
def ingressAs (envBytes : ByteArray) (target : Ixon.Address) (name : Option String)
    (limits : Ix.Kernel.Admission.Limits) : Except Err Input := do
  let env ← (Ixon.V3.decodeAnonymousEnv envBytes).mapError fun m => ingressErr "decode" m
  let () ← require (env.consts.contains target)
    (ingressErr "roots" s!"target {target} is not a constant of the environment")
  ingressRoots env #[(target, name)] limits

/-- `ingressAs` with the root unnamed (`root0`). -/
def ingress (envBytes : ByteArray) (target : Ixon.Address)
    (limits : Ix.Kernel.Admission.Limits) : Except Err Input :=
  ingressAs envBytes target none limits

/-! ## The certificate checker -/

/-- What the certificate checker accepted: the certificate and what its replay
made. For a plain-RC certificate, also the artifact in the immortal replay's shape
(`RcReplay.Artifact.toRecheckArtifact`), which the executable is built from. -/
inductive Replay where
  | zero (cert : Recheck.Cert) (artifact : Recheck.Artifact)
  | plain (cert : RcReplay.Cert) (rc : RcReplay.Artifact) (artifact : Recheck.Artifact)

/-- The artifact the executable is built from. -/
def Replay.artifact : Replay → Recheck.Artifact
  | .zero _ a => a
  | .plain _ _ a => a

/-- The accepted certificate's unfolding table (what `CompileClaim.tableCertOfText`
reads from its text under the policy). -/
def Replay.table : Replay → Src.Table.TableCert
  | .zero cert _ => cert.table
  | .plain cert _ _ => cert.base.table

def relevanceErr : Err :=
  { stage := .relevance, code := "relevance-canonical"
    message := "certificate relevance annotation does not match canonical annotator output" }

/-- **The certificate checker on a zero-RC-format certificate** (`check-cert`'s
verifier after its reader): Stage A (`checkCanonicalRelevance`), the replay
(`Recheck.run`) and the decoded definition assertions (`DefAsserts`). -/
def checkZero (cfg : Config) (inp : Input) (cert : Recheck.Cert) : Except Err Recheck.Artifact := do
  let () ← require (checkCanonicalRelevance cfg inp cert.table cert.relevance) relevanceErr
  DefAsserts.runWithReading cfg inp.program inp.kernel.rd cert

/-- **The certificate checker on a plain-RC certificate**: Stage A, the replay
(`RcReplay.run`), the definition assertions, and the artifact in the immortal
replay's shape. -/
def checkPlain (cfg : Config) (inp : Input) (cert : RcReplay.Cert) :
    Except Err (RcReplay.Artifact × Recheck.Artifact) := do
  let () ← require (checkCanonicalRelevance cfg inp cert.base.table cert.base.relevance) relevanceErr
  let rc ← DefAsserts.runRcWithReading cfg inp.program inp.kernel.rd cert
  let a ← rc.toRecheckArtifact cert
  pure (rc, a)

/-- Whether the checked program selects the zero-RC policy
(`Own.Plain.selectRcPolicyForSrc`). -/
def selectsZeroRc (a : Recheck.Artifact) : Bool :=
  Own.Plain.selectRcPolicyForSrc a.src a.front.fir == .zeroRc

/-- The contract recheck the zero-RC claim stands on: the contract-aware ownership
check within the parameter limit. Given the replay, this is the verdict of
`Recheck.runWithContracts` (and of `Exe.Cert.policyOfArtifact`, which `verify-exe`
replays). -/
def zeroRcContractsOk (a : Recheck.Artifact) : Bool :=
  (Own.Plain.Certificate.checkParamTotal Anf.maxParamTotal a.fir).isOk && a.checkContractOwn

/-- Whether an artifact of the immortal replay is one the zero-RC policy claims:
the checked program selects zero RC and passes the contract recheck. This is the
selection that `CompileClaim.verifyProgram` requires of a `.zeroRc` claim. -/
def zeroRcOk (a : Recheck.Artifact) : Bool :=
  selectsZeroRc a && zeroRcContractsOk a

/-- The refusal of a program that selects zero RC and whose contract recheck refuses
it (`exe.cert.policy`, as `Exe.Cert.policyOfArtifact` and the command line's
`--embed-cert` refuse it): a failed policy recheck is an error, never a weaker label. -/
def policyErr : Err :=
  { stage := .cert, code := "exe.cert.policy"
    message := "the program selects the zero-RC policy, and the contract recheck its claim stands \
      on (the contract-aware ownership check within the parameter limit) refuses it" }

/-- **The policy of a zero-RC-format artifact**: `.zeroRc` when the program selects
zero RC and the contract recheck accepts; a refusal (`policyErr`) when it selects
zero RC and the recheck refuses; `.immortal` when it does not select zero RC (a
program that selects plain RC, compiled on the immortal backend). -/
def zeroPolicy (a : Recheck.Artifact) : Except Err CompilePolicy :=
  if selectsZeroRc a then
    if zeroRcContractsOk a then .ok .zeroRc else .error policyErr
  else .ok .immortal

/-- What `certify` returns: the certificate, the checker's verdict on it, and the
producer's reports. -/
structure Certified where
  /-- The configuration the checker accepted under: the input's, or that without the
  middle end's inline-round retry (`withRetry`). The checker reads its table
  configuration, root names, clobber sets and provenance; the budgets are the
  producer's. -/
  cfg : Config
  /-- The policy compiled under. -/
  policy : CompilePolicy
  /-- The certificate's file text, which the certificate replayed was read back
  from. -/
  cert : String
  replay : Replay
  /-- Reports only (the command line prints them): the allocation outcomes, the
  word hints after admission, and under `Rc.auto` why plain RC was refused. -/
  alloc : List Xv.Alloc.Outcome := []
  wordHints : Array Src.Diag := #[]
  note : Option String := none

/-- A produced zero-RC-format certificate through its checker, with its policy
(`zeroPolicy`): `.zeroRc` when the checked program selects zero RC and passes the
contract recheck, `.immortal` when it does not select zero RC, and a refusal when it
selects zero RC and the recheck refuses (never relabelled `.immortal`). -/
def certifyZero (cfg : Config) (inp : Input) (p : Recheck.Produced) (note : Option String) :
    Except Err Certified := do
  let a ← checkZero cfg inp p.cert
  let policy ← zeroPolicy a
  pure { cfg, policy, cert := p.text
         replay := .zero p.cert a, alloc := p.alloc, wordHints := p.wordHints, note }

/-- A produced plain-RC certificate that its replay accepted (`rc`): Stage A, and
the artifact in the immortal replay's shape. -/
def certifyPlain (cfg : Config) (inp : Input) (p : RcReplay.Produced) (rc : RcReplay.Artifact) :
    Except Err Certified := do
  let () ← require (checkCanonicalRelevance cfg inp p.cert.base.table p.cert.base.relevance) relevanceErr
  let a ← rc.toRecheckArtifact p.cert
  pure { cfg, policy := .plainRc, cert := p.text, replay := .plain p.cert rc a, alloc := p.alloc
         wordHints := p.front.wordHints }

/-- `Rc.on`: the plain-RC producer, then its checker. -/
def certifyOn (cfg : Config) (inp : Input) : Except Err Certified := do
  let p ← RcReplay.produceWith cfg inp
  let (rc, a) ← checkPlain cfg inp p.cert
  pure { cfg, policy := .plainRc, cert := p.text, replay := .plain p.cert rc a, alloc := p.alloc
         wordHints := p.front.wordHints }

/-- `Rc.auto` once the front half is produced: zero RC when selected; plain RC when
selected and its certificate is produced and replayed (`RcReplay.producePlain`);
otherwise the immortal backend, with the refusal as a note. -/
def certifyAuto (cfg : Config) (inp : Input) (front : RcReplay.ProducedFir) : Except Err Certified :=
  match Own.Plain.selectRcPolicyForSrc front.src front.fir with
  | .zeroRc => (RcReplay.finishZeroRcCert cfg front) >>= fun p => certifyZero cfg inp p none
  | .plainRc =>
    match RcReplay.producePlain cfg inp front with
    | .ok (p, rc) => certifyPlain cfg inp p rc
    | .error reason =>
      (if reason.code.startsWith "assert." then .error reason
       else RcReplay.finishZeroRcCert cfg front) >>= fun p =>
        certifyZero cfg inp p
          (some s!"immortal (plain RC refused: {reason.stage.name}: {reason.code}: {reason.message})")

/-- **The deterministic producer, then the certificate checker**, at one
configuration, under policy request `rc`. Every search is the producer's
(`Recheck.produceWith`, `RcReplay.produceWith`, `RcReplay.produceFir` and its
finishers); what is returned is the checker's verdict on the producer's
certificate. -/
def certify (rc : Rc) (cfg : Config) (inp : Input) : Except Err Certified :=
  match rc with
  | .off => (Recheck.produceWith cfg inp) >>= fun p => certifyZero cfg inp p none
  | .on => certifyOn cfg inp
  | .auto => (RcReplay.produceFir cfg inp) >>= fun front => certifyAuto cfg inp front

/-- `attempt` at `cfg` and, if the configuration asks for the middle end's
inline-round retry and that fails at any stage, at the configuration without it
(a retried round's larger program may fail a budget that the program without it
passes). Each run is the whole of `attempt` at its own configuration. -/
def withRetry {α : Type} (cfg : Config) (attempt : Config → Except Err α) : Except Err α :=
  if cfg.budgets.retryInline then
    match attempt cfg with
    | .ok a => .ok a
    | .error _ => attempt cfg.noRetry
  else attempt cfg

/-! ## The two stages -/

/-- **What `check` returns**: the ingested input and the checker's verdict. The
command line's reports (`--stats`, `--dump-ir`, `--signatures`, the object for
`-o`) read it; `build` makes the executable from it. -/
structure Checked extends Certified where
  inp : Input
  /-- The role table's address (the environment is role-bound). -/
  roleTable : Ixon.Address

/-- **The seed-closure check** (`KF-4` + `SP-0`, `CompileClaim.checkSeedClosure`):
the records the target and the theorems of the accepted certificate's table reach,
admitted by the certified kernel's pure logical entry under the committed prelude
and the committed default role table (which the environment's table must restrict),
with the `N5` mode check. `verify-exe` runs it (`exe.cert.kf4`), so `compile` runs
it too: what `compile` returns is what the verifier accepts. -/
def seedClosure (inp : Input) (target : Ixon.Address) (tc : Src.Table.TableCert)
    (limits : Ix.Kernel.Admission.Limits) : Except Err Unit :=
  seedClosureOf (CompileClaim.checkSeedClosure inp target tc limits)
where
  /-- The check's verdict as a refusal (a separate function, so that statements about it
  never unfold the check). -/
  seedClosureOf {α : Type} : Except String α → Except Err Unit
    | .ok _ => .ok ()
    | .error m => .error { stage := .ingress, code := "kf4", message := m }

/-- Whether the program's first root is the constant at `target`. -/
def targetIsRoot (inp : Input) (target : Ixon.Address) : Bool :=
  match inp.program.roots.head? with
  | some (a, _) => a == target
  | none => false

/-- **Stage 1: ingress, the producer and the certificate checker.** The first root
of the ingested program is `target` (`targetIsRoot`: `readConsts` resolves the one
root by address, so this cannot refuse; it is checked so that the claim's target
needs no lemma about ingress); a root whose caller would pass a closure is refused
before anything is produced (`checkFnParams`); then `certify` under the input's
configuration, with the inline-round retry; then the seed-closure check on the
accepted certificate's table (`seedClosure`). -/
def check (envBytes : ByteArray) (target : Ixon.Address) (opts : Options) : Except Err Checked := do
  let inp ← ingressAs envBytes target opts.name opts.kernelLimits
  let () ← require (targetIsRoot inp target)
    (ingressErr "roots" "the ingested program's first root is not the target")
  let roleTable ← orRefuse (ingressErr "kernel" "the environment is not role-bound") inp.env.bindingAddress
  let cfg := Config.forInput {} inp
  let () ← checkFnParams cfg.names inp.program
  let c ← withRetry cfg fun cfg => certify opts.rc cfg inp
  let () ← seedClosure inp target c.replay.table opts.kernelLimits
  pure { c with inp, roleTable }

/-- An executable's bytes with the root's parameter count and rendering. -/
structure Executable where
  bytes : ByteArray
  arity : Nat
  result : X86.Exe.ResultKind

/-- The standalone executable of an artifact's first root: `Exe.build` (written,
then checked structurally and by the independent shell decoder) or
`Exe.buildMachine`. -/
def executable (kind : X86.Exe.Cert.ExeKind) (layout : X86.Exe.Layout) (a : Recheck.Artifact) :
    Except Err Executable :=
  match kind with
  | .plain =>
    match Exe.build a layout with
    | .ok b => .ok { bytes := b.2.bytes, arity := b.1.arity, result := b.1.result }
    | .error e => .error e
  | .machine =>
    match Exe.buildMachine a { stack := layout.stack, region := layout.region } with
    | .ok b => .ok { bytes := b.2.checked.bytes, arity := b.1.params, result := .nat }
    | .error e => .error e

/-- **Stage 2: the executable and the claim**, from what the checker accepted. -/
def build (target : Ixon.Address) (opts : Options) (c : Checked) : Except Err Output := do
  let x ← executable opts.kind opts.layout c.replay.artifact
  pure {
    claim := {
      env := c.inp.env.root
      roleTable := c.roleTable
      target
      options := opts
      exe := Ixon.Address.blake3Pure x.bytes
      policy := c.policy
      arity := x.arity
      result := x.result
      object := Ixon.Address.blake3Pure c.replay.artifact.object }
    exe := x.bytes
    cert := c.cert }

/-- **The compiler.** `check`, then `build`.

The two decisions of the certified route that are not implemented here are called
between the stages, on `c : Checked`; each only refuses.

* **HOOK (a), the shape decision** (`IxCCCorrect.ShapeHook` of the source-progress
  lane): a shape certificate produced for, and checked against, the checked source
  the replay made (`c.replay.artifact.src` with its roots), so that acceptance
  implies the source evaluator is never stuck on the target's inputs and the
  "source goes wrong" case of the checker's soundness theorem is empty.
* **HOOK (b), the grounding checks** (`IxCCGrounding`): that the checked source's
  table and constants agree with the kernel's reading of the admitted environment
  (`c.inp.kernel`). The target's logical tier is established in `check` already
  (`seedClosure`).

Production may not import either library, so the function with both checks is
assembled where they may be imported, as
`fun envBytes target opts => check envBytes target opts >>= shape >>= ground >>= build target opts`
with `shape, ground : Checked → Except Err Checked` returning their argument.

**`--opt` is not here.** `Lir.Opt.run` is a total function with a clocked
simulation of its input (`Lir.Opt.run_sim`: `Sem.Sim Eq runClock`, stated of
`Lir.eval`, the program's `main`), and `Backend.compileOpt_refines_main` composes it
with selection, the producer's own allocation (`Alloc.run`) and emission, for the
main export. The replay theorems (`Recheck.sound`, `RcReplay.sound`) are stated of
the object `Backend.finish` makes from the unoptimized Lir program, under
allocation, frame-layout and block-order certificates validated against that
program, for every export. Including the passes needs: (1) the optimizer run inside
the replay (`Recheck.runLir` and `RcReplay.runFront`, after the runtime lowering and
before selection), so that the certificate's back-end fields are produced for and
validated against the optimized program, and the definition assertions are checked
on it; (2) `run_sim` composed between the front theorem and the back theorem of the
replay, which needs it at the functions the exports enter, not only at `main`, and
the facts the back half assumes of the lowering's output re-established for the
optimizer's (well-formedness is `Lir.Opt.run_wellFormed`; the export list and the
representations must be shown unchanged); (3) the kernel-style audit of
`Recheck.run` extended over `Lir.Opt`; and (4) an `Options` field, since it changes
the output. -/
def compile (envBytes : ByteArray) (target : Ixon.Address) (opts : Options) : Except Err Output := do
  let c ← check envBytes target opts
  -- HOOK (a): the shape decision on `c.replay.artifact.src` (never stuck).
  -- HOOK (b): the grounding checks on `c.inp.kernel` and `c.replay.artifact.src`.
  build target opts c

end IxCC.Compile
