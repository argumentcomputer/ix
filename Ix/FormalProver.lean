module
public import Lean.Data.Json
public import Ix.Aiur.Protocol

/-!
The formal Aiur prover (`crates/ix-prover`) linked into this process,
through the adapter in `crates/ffi/src/formal.rs`. Manifests and their
aggregation run on the Rust aggregate controller (`proveLanes`,
`aggregate`); single claims are proven, checked and verified by stateless
calls. Environments and requests are opaque Rust-owned handles; reports are
JSON diagnostics.

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
`output`. Returns a status (0 proven, 75 no trace-shard plan fits) and a
JSON report. -/
@[extern "rs_formal_prove"]
opaque prove (artifact : @& String) (request : @& Request) (output options : @& String)
  (threads : @& Nat) : IO (UInt32 × String)

@[extern "rs_formal_resources"]
private opaque resourcesFFI : IO String

/-- Available host memory (`available_bytes`) and logical cores (`cores`). -/
def resources : IO Lean.Json := do
  IO.ofExcept (Lean.Json.parse (← resourcesFFI))

/-- The executors linked into this build: `interpreter`, and the native
kernels when built with them. -/
@[extern "rs_formal_executors"]
opaque executors : IO (Array String)

/-- Verify a proof of `entry(args)` against an artifact's circuits on the
CPU, independently of CUDA settings. IxVM proofs carry their `IXAIUR2`
prefix; recursive proofs are raw. Returns the number of trace shards. -/
@[extern "rs_formal_verify"]
opaque verify (artifact entry : @& String) (args : @& Array UInt64) (proof : @& ByteArray) : IO Nat

/-- An artifact's verifying key, function index and call channel. -/
@[extern "rs_formal_identity"]
opaque identity (artifact : @& String) (recursive : Bool) : IO (ByteArray × Nat × Nat)

/-- Execute an IxVM request without proving; with `plan`, also plan its
proof within the options' budget. Returns a status and JSON report. -/
@[extern "rs_formal_check"]
opaque check (plan : Bool) (artifact : @& String) (request : @& Request)
  (options : @& String) (threads : @& Nat) : IO (UInt32 × String)

/-- Prove a manifest over `env` (`Ix.Check.loadBoundIxe`) on the aggregate
controller from its JSON configuration (`ix_prover::aggregate::LaneConfig`).
Returns the store address of a root the controller verified natively; the
caller still checks it against the statement it expects. -/
@[extern "rs_formal_prove_lanes"]
opaque proveLanes (env : @& Aiur.EnvHandle) (config : @& String) : IO String

/-- `ix aggregate` over `env` (`Ix.Check.loadBoundIxe`) from its JSON
configuration (`ix_prover::aggregate::AggregateConfig`): the address of the
proof it produced, or an empty string for a plan, and the proof's encoded
`Ixon.Proof` wrapper when the run did not write it to the store (empty
otherwise). A result still has to pass the caller's acceptance check. -/
@[extern "rs_formal_aggregate"]
opaque aggregate (env : @& Aiur.EnvHandle) (config : @& String) : IO (String × ByteArray)

/-- `ix aggregate --ixc` from its JSON configuration
(`ix_prover::aggregate::CatalogConfig`): every join of the catalog's plan,
proven from its members' roots, and the store address of the root's proof
wrapper. The root still has to pass the caller's acceptance check. -/
@[extern "rs_formal_aggregate_catalog"]
opaque aggregateCatalog (config : @& String) : IO String

/-- The fixed normalization layout (`ix-fixed-root-layout-v1` JSON) of one
more wrap of `proof`, a raw one-shard proof of the aggregation `artifact`:
the root's heights raised by `headroom` doublings, fixed tables at their
own heights, two rows for circuits the root leaves inactive, and the memory
circuits the root closes. -/
@[extern "rs_formal_fixed_root_layout"]
opaque fixedRootLayout (artifact : @& String) (proof : @& ByteArray) (headroom : UInt8) : IO String

/-- Wrap the aggregate root `proof` (an encoded `IXAGGR2` proof) of `claim`
once more with `ix_aggr` and prove the wrap as one all-active trace shard at
the heights of the fixed layout `layout`, from the JSON configuration
`config` (`ix_prover::aggregate::NormalizeConfig`). The root is verified
first and the normalized proof after; returns the raw normalized proof. -/
@[extern "rs_formal_normalize_root"]
opaque normalizeRoot (config layout : @& String) (claim proof : @& ByteArray) : IO ByteArray

end Ix.FormalProver

end
