module
public import Ix.Aiur.Protocol

/-!
The formal Aiur prover (`crates/ix-prover`) linked into this process,
through the adapter in `crates/ffi/src/formal.rs`. Manifests and their
aggregation run on the Rust aggregate controller (`proveLanes`,
`aggregate`); single claims are proven, checked and verified on the
program and system handles a command selected. Registries, programs,
systems, environments and requests are opaque Rust-owned handles.
Configuration and results are typed records read and built field by field by
the adapter; a job's JSON report is rendered only when the caller asks for
it, as a diagnostic.

A `Registry` belongs to one command. It loads each selected program once
and prepares each program's `System` (its verifying backend and key under
explicit `ProtocolParameters`) once, however many checks, key queries and
verifications use it.

These are runtime operations outside the formal development. They return
data and proof bytes, never Lean proofs about the Rust execution, and trusted
artifacts and expected claims are still selected and checked by the caller.
-/

public section

namespace Ix.FormalProver

private opaque EnvNonempty : NonemptyType
/-- A Rust-owned environment, shared by the requests that name it. -/
def Env : Type := EnvNonempty.type
instance : Nonempty Env := EnvNonempty.property

private opaque RegistryNonempty : NonemptyType
/-- The programs and systems one command selected. -/
def Registry : Type := RegistryNonempty.type
instance : Nonempty Registry := RegistryNonempty.property

private opaque ProgramNonempty : NonemptyType
/-- A checked compiler output: bytecode, circuits and population plans. -/
def Program : Type := ProgramNonempty.type
instance : Nonempty Program := ProgramNonempty.property

private opaque SystemNonempty : NonemptyType
/-- A program under explicit STARK parameters, with its verifying backend
and key. -/
def System : Type := SystemNonempty.type
instance : Nonempty System := SystemNonempty.property

/-- The STARK parameters a system is prepared for. -/
structure ProtocolParameters where
  logBlowup : Nat := 2
  numQueries : Nat := 100

@[extern "rs_formal_registry_new"]
opaque Registry.new : IO Registry

/-- Diagnostic: the legacy JSON compiler artifact at `path`, loaded and
checked once per registry. -/
@[extern "rs_formal_registry_load_json"]
opaque Registry.loadJson (registry : @& Registry) (path : @& String) : IO Program

/-- `program` under `params`, prepared once per registry. -/
@[extern "rs_formal_registry_system"]
opaque Registry.system (registry : @& Registry) (program : @& Program)
  (params : @& ProtocolParameters) : IO System

/-- The trusted artifact file at `path`, decoded once per registry. -/
@[extern "rs_formal_registry_load_binary"]
opaque Registry.loadBinary (registry : @& Registry) (path : @& String) : IO Program

/-- Persist `program` as a binary artifact at `path`, atomically, with its
metadata: a name, the compiler identity and the source digest. -/
@[extern "rs_formal_program_save"]
opaque Program.save (program : @& Program) (path : @& String) (name compiler : @& String)
  (source : @& ByteArray) : IO Unit

/-- The 32-byte identity a program was registered under. -/
@[extern "rs_formal_program_identity"]
opaque Program.identity (program : @& Program) : IO ByteArray

/-- The executor `program` runs on (`interpreter`, or the linked native
executor generated from exactly this program, such as `native-ixvm`) and
the program's native fingerprint. -/
@[extern "rs_formal_program_executor"]
opaque Program.executor (program : @& Program) : IO (String × String)

/-- The generated sources of the formal program `name` (`ixvm`, `verifier`
or `aggregation`) that `lake build ix` compiles: its native executor, and
with `cuda` its trace writers, as paths relative to the generated directory
with their contents. `source` is the digest of the source bundle the program
was compiled from. -/
@[extern "rs_formal_program_codegen"]
opaque Program.codegen (program : @& Program) (name : @& String) (source : @& ByteArray)
  (cuda : Bool) : IO (Array (String × String))

/-- Diagnostic: compare `program` with the JSON compiler artifact at `path`
and with its own binary round trip. Returns the first difference, or an
empty string when all three agree. -/
@[extern "rs_formal_program_compare"]
opaque Program.compare (program : @& Program) (path : @& String) : IO String

/-- The certified programs the linked compiler builds. -/
inductive Target where
  | ixvm | verifier | aggregation
  deriving BEq, Repr, Inhabited

/-- One program for the linked compiler: its target, source bundle text and
lookup key. -/
structure CompileJob where
  target : Target
  source : String
  key : ByteArray

/-- The compiler linked into an executable: its identity, and a function
that compiles targets' source bundle texts into a registry under their
lookup keys, concurrently, with the frontend's build taken from the checkout
`root`. An executable that does not import `Ix.FormalCompiler` has none. -/
structure Compiler where
  /-- Lowercase hex digest of the compiler code linked into this executable. -/
  identity : String
  compile : Registry → (root : String) → Array CompileJob → IO (Array Program)

initialize compilerRef : IO.Ref (Option Compiler) ← IO.mkRef none

/-- The linked compiler, which `Ix.FormalCompiler` registers when it is
initialized. -/
def compiler : IO Compiler := do
  let some c ← compilerRef.get
    | throw (IO.userError "this executable does not link the certified Aiur compiler")
  return c

/-- Programs, trace plans, systems and proving backends this process has
constructed. -/
@[extern "rs_formal_counters"]
opaque counters : IO (Nat × Nat × Nat × Nat)

/-- How a proof retains trace shards between its stages. -/
inductive Retention where
  | auto | retain | regenerate
  deriving Inhabited, BEq, Repr

/-- Planner options of one job: a row bound, a RAM budget, the CUDA device
(`none`: the CPU) and the retention policy. -/
structure JobOptions where
  maxRows : Option Nat := none
  maxRamBytes : Option Nat := none
  device : Option Nat := none
  retention : Retention := .auto

/-- Available host memory, when known, and logical cores. -/
structure Resources where
  availableBytes : Option Nat
  cores : Nat

/-- What a job's plan decided: its estimated peaks and whether it fits; a
caller that splits claims splits into `suggestedParts` when `canSplit`. -/
structure PlanSummary where
  suggestedParts : Nat
  generationPeakBytes : Nat
  provingPeakBytes : Nat
  fits : Bool
  canSplit : Bool

/-- The result of one job: its plan (none for execution alone), a JSON
report when one was requested (otherwise empty), and its status (0, or 75
when no plan fits the budget). -/
structure Outcome where
  plan : Option PlanSummary
  report : String
  status : UInt32

/-- `ix prove --lanes` as configured. `maxRamBytes` zero detects the host's
allowance. `select` restricts a `claimsOnly` run to these shard ids. A
`bindingProof` is the store address of the environment's `Binding` proof:
claims assume their binding and the root discharges it. -/
structure LaneConfig where
  manifest : String
  lanes : Nat
  device : Option Nat
  maxRamBytes : Nat
  execJobs : Nat
  structuralAbove : Nat
  outManifest : Option String
  select : Option (Array Nat)
  bindingProof : Option ByteArray
  options : JobOptions
  useCache : Bool
  useIndex : Bool
  claimsOnly : Bool
  assumeBinding : Bool

/-- What a lane run proved: the verified root's store address, or with
`claimsOnly` each proven claim's shard id and proof address. -/
inductive LaneResult where
  | root (address : ByteArray)
  | claims (proven : Array (Nat × ByteArray))

/-- `ix aggregate` as configured. `proofs` are store addresses of claim and
plan-slot proofs; `bindingProof` the store address of a binding proof. -/
structure AggregateConfig where
  manifest : String
  proofs : Array ByteArray
  lanes : Nat
  device : Option Nat
  execAhead : Nat
  structuralAbove : Nat
  reproveSlot : Option Nat
  subtree : Option Nat
  bindingProof : Option ByteArray
  options : JobOptions
  planOnly : Bool
  useCache : Bool
  writeOutputs : Bool
  wrapRoot : Bool
  assumeBinding : Bool

/-- A catalog member: its label, its claim (`Ix.Claim.ser`), its role
binding section and its literal class's address. -/
structure CatalogMember where
  label : String
  claim : ByteArray
  bindingSection : ByteArray
  literalClass : Option ByteArray

/-- `ix aggregate --ixc` as configured: the members in manifest order, the
store addresses of their roots and the root claim (`Ix.Claim.ser`) the
caller's plan reaches. -/
structure CatalogConfig where
  members : Array CatalogMember
  proofs : Array ByteArray
  expectedRoot : ByteArray
  device : Option Nat
  options : JobOptions
  useCache : Bool
  writeOutputs : Bool

/-- `ix compress` normalization as configured. -/
structure NormalizeConfig where
  device : Option Nat
  options : JobOptions

private opaque RequestNonempty : NonemptyType
/-- What a prover executes: a claim prepared from an environment,
or an existing witness held as compact advice. -/
def Request : Type := RequestNonempty.type
instance : Nonempty Request := RequestNonempty.property

/-- Copy the environment of an `Aiur.EnvHandle` (`Ix.Check.loadBoundIxe`, or
one compiled in Lean); constant bytes are shared, not copied. The prover
never opens `.ixe` files itself, so it checks exactly the environment Lean
checks. -/
@[extern "rs_formal_env_of_handle"]
opaque Env.ofHandle (handle : @& Aiur.EnvHandle) : IO Env

/-- `Check target` without assumptions. The prover recomputes the claim
from the target and rejects the job unless it equals `claim`
(`Ix.Claim.ser` bytes). -/
@[extern "rs_formal_request_check"]
opaque Request.check (env : @& Env) (target claim : @& ByteArray) : IO Request

/-- A shard `CheckEnv` over the constants that the manifest `blocks`
(concatenated 32-byte addresses) own. The prover builds the witness and
rejects the job unless the recomputed claim equals `claim`. -/
@[extern "rs_formal_request_shard"]
opaque Request.shard (env : @& Env) (blocks claim : @& ByteArray) : IO Request

/-- An existing witness. `layout` holds little-endian `UInt64`s, per stream
its channel, payload kind (0 bytes, 1 numeric words), key length, key and
payload length; byte payloads are consecutive in `bytes`, numeric payloads
consecutive little-endian words in `words`. Buffers are validated and
copied once. -/
@[extern "rs_formal_request_buffers"]
opaque Request.buffers (entry : @& String) (args : @& Array UInt64)
  (layout bytes words : @& ByteArray) : IO Request

/-- Prove one IxVM claim within the options' device and RAM budget on
`threads` threads (0: all), writing the proof, key and claims next to
`output`. With `report`, the outcome carries the JSON report. -/
@[extern "rs_formal_system_prove"]
opaque System.prove (system : @& System) (request : @& Request) (output : @& String)
  (options : @& JobOptions) (threads : @& Nat) (report : Bool) : IO Outcome

@[extern "rs_formal_resources"]
opaque resources : IO Resources

/-- The executors linked into this build: `interpreter`, and the committed
native executors. -/
@[extern "rs_formal_executors"]
opaque executors : IO (Array String)

/-- Verify a proof of `entry(args)` against a system's circuits on the
CPU, independently of CUDA settings. IxVM proofs carry their `IXAIUR2`
prefix; recursive proofs are raw. Returns the number of trace shards. -/
@[extern "rs_formal_system_verify"]
opaque System.verify (system : @& System) (entry : @& String) (args : @& Array UInt64)
  (proof : @& ByteArray) : IO Nat

/-- A system's verifying key. -/
@[extern "rs_formal_system_key"]
opaque System.key (system : @& System) : IO ByteArray

/-- A system's verifying key, function index and call channel. -/
@[extern "rs_formal_system_identity"]
opaque System.identity (system : @& System) (recursive : Bool) : IO (ByteArray × Nat × Nat)

/-- Execute an IxVM request without proving. -/
@[extern "rs_formal_program_check"]
opaque Program.check (program : @& Program) (request : @& Request) (threads : @& Nat)
  (report : Bool) : IO Outcome

/-- Execute an IxVM request and plan its proof within the options' budget,
without proving. -/
@[extern "rs_formal_system_plan"]
opaque System.plan (system : @& System) (request : @& Request) (options : @& JobOptions)
  (threads : @& Nat) (report : Bool) : IO Outcome

/-- Prove a manifest over `env` (`Ix.Check.loadBoundIxe`) on the aggregate
controller with the IxVM and aggregation systems. Returns the address of a
root the controller verified natively, or the proven claims; the caller
still checks a root against the statement it expects. -/
@[extern "rs_formal_prove_lanes"]
opaque proveLanes (ixvm aggr : @& System) (env : @& Aiur.EnvHandle) (config : @& LaneConfig) :
  IO LaneResult

/-- `ix aggregate` over `env` (`Ix.Check.loadBoundIxe`): nothing for a
plan, otherwise the address of the proof it produced and the proof's encoded
`Ixon.Proof` wrapper when the run did not write it to the store (empty
otherwise). `bindingProof` is the encoded wrapper of a binding proof for a
run that writes nothing. A result still has to pass the caller's acceptance
check. -/
@[extern "rs_formal_aggregate"]
opaque aggregate (ixvm aggr : @& System) (env : @& Aiur.EnvHandle) (config : @& AggregateConfig)
  (bindingProof : @& Option ByteArray) : IO (Option (ByteArray × ByteArray))

/-- `ix aggregate --ixc`: every join of the catalog's plan, proven from its
members' roots, and the store address of the root's proof wrapper. The root
still has to pass the caller's acceptance check. -/
@[extern "rs_formal_aggregate_catalog"]
opaque aggregateCatalog (ixvm aggr : @& System) (config : @& CatalogConfig) : IO ByteArray

/-- The fixed normalization layout (`ix-fixed-root-layout-v1` JSON) of one
more wrap of `proof`, a raw one-shard proof of the aggregation system `aggr`:
the root's heights raised by `headroom` doublings, fixed tables at their
own heights, two rows for circuits the root leaves inactive, and the memory
circuits the root closes. -/
@[extern "rs_formal_fixed_root_layout"]
opaque fixedRootLayout (aggr : @& System) (proof : @& ByteArray) (headroom : UInt8) : IO String

/-- Wrap the aggregate root `proof` (an encoded `IXAGGR2` proof) of `claim`
once more with `ix_aggr` and prove the wrap as one all-active trace shard at
the heights of the fixed layout `layout` (`ix compress layout` JSON). The root is verified
first and the normalized proof after; returns the raw normalized proof. -/
@[extern "rs_formal_normalize_root"]
opaque normalizeRoot (ixvm aggr : @& System) (config : @& NormalizeConfig) (layout : @& String)
  (claim proof : @& ByteArray) : IO ByteArray

end Ix.FormalProver

end
