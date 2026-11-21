import Ix.Cert.MultiStark.Types

/-! # Multi-STARK Batch Preamble & Security-Envelope Validator (`Ix.Cert.MultiStark.Preamble`)

Enforces every semantic and cryptographic precondition required by
`Aiur.Audit.depth_grouped_activated_heap_sound_goldilocks_observed` and
`MultiStark/MultiStark/Modules/StarkVerifier.lean:623-761`:
1. Protocol parameters: `capHeight = 0`, `logFinalPolyLen = 0`, `maxLogArity = 1`, `logBlowup ≥ 1`.
2. Shard count: `1 ≤ headers.size ≤ 2^16` (`MAX_BATCH_SHARDS`) and `proofs.size = headers.size`.
3. Per-circuit lookup bound: `circuit.lookups.size < 2^24` (`MAX_CIRCUIT_LOOKUPS`).
4. Total batch row bound: `Σ_{s, active c} 2^{logDeg} ≤ 2^39` (`MAX_BATCH_ROWS`) and `logDeg ≤ maxLogDeg`.
5. `MEMSEG = 16` closure-pair validation (`assert_closure_pairs`, `StarkVerifier.lean:706-731`):
   messages pair into `(-1, [16, w, a])` followed by `(+1, [16, w, b])` with `a ≤ b < p`
   in strictly ascending `(w, [a, b))` order (guaranteeing disjoint half-open intervals and `I(p - 1) = 0`).
-/

namespace Ix.Cert.MultiStark

open CertiFri.P3

/-- Check fixed protocol parameter invariants enforced by `StarkVerifier.lean:739-741`. -/
def checkParams (p : StarkParams) : Bool :=
  p.capHeight == 0
    && p.logFinalPolyLen == 0
    && p.maxLogArity == 1
    && p.logBlowup ≥ 1
    && p.numQueries ≥ 1

/-- Check static system invariants: matching `preprocessedIndices`, lookup count `< 2^24`,
valid `preprocessedCommit` cap length (`1` if `some`). -/
def checkSystem (sys : StarkSystem) : Bool :=
  checkParams sys.params
    && sys.preprocessedIndices.size == sys.circuits.size
    && (match sys.preprocessedCommit with
        | none => sys.preprocessedIndices.all (·.isNone)
        | some cap => cap.size == 1)
    && sys.circuits.all fun c =>
        c.lookups.size < MAX_CIRCUIT_LOOKUPS
          && c.lookupGroupSize ≥ 1
          && (c.preprocessedHeight == 0 ||
              (c.preprocessedHeight > 0 && c.preprocessedHeight &&& (c.preprocessedHeight - 1) == 0))

/-- Validate `MEMSEG = 16` closure pairs (`StarkVerifier.lean:706-731`):
even message list paired as `(pull -1 [16, w, a], push +1 [16, w, b])` with
`a ≤ b` and strictly ascending widths or non-overlapping intervals `prevB ≤ a`. -/
def checkClosurePairs (messages : Array BatchMessage) : Bool :=
  if messages.size % 2 != 0 then false
  else
    let numPairs := messages.size / 2
    Id.run do
      let mut prevW : Nat := 0
      let mut prevB : Nat := 0
      let mut hasPrev := false
      for i in [0:numPairs] do
        let pull := messages[2 * i]!
        let push := messages[2 * i + 1]!
        if pull.multiplicity.add Goldilocks.one != Goldilocks.zero then return false
        if push.multiplicity != Goldilocks.one then return false
        if pull.args.size != 3 || push.args.size != 3 then return false
        if pull.args[0]!.toNat != MEMSEG_CHANNEL || push.args[0]!.toNat != MEMSEG_CHANNEL then
          return false
        let w := pull.args[1]!.toNat
        if push.args[1]!.toNat != w then return false
        let a := pull.args[2]!.toNat
        let b := push.args[2]!.toNat
        if a > b then return false
        if hasPrev then
          if w < prevW then return false
          if w == prevW && a < prevB then return false
        prevW := w
        prevB := b
        hasPrev := true
      return true

/-- Validate batch preamble bounds (`StarkVerifier.lean:623-686, 795-801`),
returning `true` iff shard count, total batch rows `≤ MAX_BATCH_ROWS`, per-shard
activation/degree counts, and `MEMSEG` closure pairs all hold.
Optional `maxLogDeg` caps trace log-degree (default `31`, ensuring `logDeg + logBlowup ≤ 32`
for `logBlowup ≤ 1` or `32 - logBlowup` in general). -/
def validatePreamble (sys : StarkSystem) (batch : BatchProof)
    (maxLogDeg : Nat := 32 - sys.params.logBlowup) : Bool :=
  let headers := batch.preamble.headers
  if !checkSystem sys then false
  else if headers.size == 0 || headers.size > MAX_BATCH_SHARDS then false
  else if batch.proofs.size != headers.size then false
  else if !checkClosurePairs batch.preamble.messages then false
  else
    Id.run do
      let mut totalRows : Nat := 0
      for h in headers do
        if h.active.size != sys.circuits.size then return false
        let activeCount := h.active.foldl (fun acc b => if b then acc + 1 else acc) 0
        if activeCount == 0 || h.logDegrees.size != activeCount then return false
        if h.stage1Trace.size != 1 then return false
        for ld in h.logDegrees do
          if ld > maxLogDeg || ld + sys.params.logBlowup > 32 then return false
          totalRows := totalRows + (1 <<< ld)
          if totalRows > MAX_BATCH_ROWS then return false
      return true

end Ix.Cert.MultiStark
