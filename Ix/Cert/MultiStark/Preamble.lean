import Ix.Cert.MultiStark.Types
import Ix.Aiur.Parameters

/-! # Multi-STARK Batch Preamble & Security-Envelope Validator (`Ix.Cert.MultiStark.Preamble`)

Enforces every semantic and cryptographic precondition required by
`Aiur.Audit.depth_grouped_activated_heap_sound_goldilocks_observed`,
`crates/stark-key/src/security.rs`, `crates/aiur/src/trace/stark/batch.rs`, and
`MultiStark/MultiStark/Modules/StarkVerifier.lean`:
1. Protocol parameters: `capHeight = 0`, `logFinalPolyLen = 0`, `maxLogArity = 1`, `1 ≤ logBlowup ≤ 4`,
   and the production Aiur security floor (`Aiur.meetsSecurityFloor`: per-`logBlowup` query floor,
   PoW ceiling `≤ 32`, `≥ 220` conjectured bits, `≥ 80` provable UD bits, `≥ 100` Johnson bits).
   (`checkParamsWithFloor ... true` is provided strictly as a test-harness waiver for toy fixtures.)
2. Shard count: `1 ≤ headers.size ≤ 2^16` (`MAX_BATCH_SHARDS`) and `proofs.size = headers.size`.
3. Per-circuit lookup bound: `circuit.lookups.size < 2^24` (`MAX_CIRCUIT_LOOKUPS`), and no
   inactive preprocessed/fixed-table circuits (`StarkVerifier.lean:470,484`, `batch.rs:283`).
4. Total batch row bound: `Σ_{s, active c} weight(c) * 2^{logDeg} ≤ 2^39` (`MAX_BATCH_ROWS`)
   and `logDeg ≤ maxLogDeg`.
5. `MEMSEG = 16` closure-pair validation (`assert_closure_pairs`, `StarkVerifier.lean:841-901`):
   messages pair into `(-1, [16, w, a])` followed by `(+1, [16, w, b])` with strict `a < b < p`
   in ascending `(w, [a, b))` order (guaranteeing disjoint half-open intervals and `I(p - 1) = 0`).
-/

namespace Ix.Cert.MultiStark

open CertiFri.P3

/-- Check fixed structural protocol parameter invariants enforced by `StarkVerifier.lean:909-911`
(without the cryptographic security floor; use `checkParams` for production). -/
def checkParamsStructural (p : StarkParams) : Bool :=
  p.capHeight == 0
    && p.logFinalPolyLen == 0
    && p.maxLogArity == 1
    && p.logBlowup ≥ 1
    && p.numQueries ≥ 1

/-- Check structural parameter invariants and (unless `allowBelowFloor = true` in test harnesses
for toy fixtures) the full production Aiur security floor (`Aiur.meetsSecurityFloor`). -/
def checkParamsWithFloor (p : StarkParams) (allowBelowFloor : Bool := false) : Bool :=
  checkParamsStructural p
    && (allowBelowFloor
      || Aiur.meetsSecurityFloor
          ⟨p.logBlowup, p.capHeight⟩
          ⟨p.logFinalPolyLen, p.maxLogArity, p.numQueries, p.commitPowBits, p.queryPowBits⟩)

/-- Production parameter check: enforces both structural protocol invariants and the full
Aiur security floor (`Aiur.meetsSecurityFloor`). -/
def checkParams (p : StarkParams) : Bool :=
  checkParamsWithFloor p false

/-- Check static system invariants: parameter checks (with optional test-harness floor waiver),
matching `preprocessedIndices`, lookup count `< 2^24`, valid `preprocessedCommit` cap length (`1` if `some`). -/
def checkSystemWithFloor (sys : StarkSystem) (allowBelowFloor : Bool := false) : Bool :=
  checkParamsWithFloor sys.params allowBelowFloor
    && sys.preprocessedIndices.size == sys.circuits.size
    && (match sys.preprocessedCommit with
        | none => sys.preprocessedIndices.all (·.isNone)
        | some cap => cap.size == 1)
    && sys.circuits.all fun c =>
        c.lookups.size < MAX_CIRCUIT_LOOKUPS
          && c.lookupGroupSize ≥ 1
          && (c.preprocessedHeight == 0 ||
              (c.preprocessedHeight > 0 && c.preprocessedHeight &&& (c.preprocessedHeight - 1) == 0))

/-- Production static system check (enforcing the full Aiur security floor). -/
def checkSystem (sys : StarkSystem) : Bool :=
  checkSystemWithFloor sys false

/-- `C6` vectorized ROM lane schedule (`crates/aiur/src/trace/stark/rom.rs`):
`8` lanes for `w ≤ 4`, `4` lanes for `5 ≤ w ≤ 12`, `1` lane otherwise. -/
def romLanes (w : Nat) : Nat :=
  if w ≤ 4 then 8
  else if w ≤ 12 then 4
  else 1

/-- If `c` carries a `MEMSEG = 16` lookup `[16, w, addr]` with constant tag and width,
return `some w`. Matches `crates/aiur/src/trace/stark/batch.rs:circuit_memseg_width` and
`StarkVerifier.lean:circuit_memseg_width`. -/
def circuitMemsegWidth? (c : SysCircuit) : Option Nat := Id.run do
  for lk in c.lookups do
    if lk.args.size == 3 then
      match lk.args[0]?, lk.args[1]? with
      | some tagId, some wId =>
        match c.nodes[tagId]?, c.nodes[wId]? with
        | some (GraphNode.const tagVal), some (GraphNode.const wVal) =>
          if tagVal.toNat == MEMSEG_CHANNEL then
            return some wVal.toNat
        | _, _ => pure ()
      | _, _ => pure ()
  return none

/-- Per-row entry weight for a circuit when enforcing the global `≤ 2^39` row/ROM invariant:
a `C6` vectorized `<ROM:w>` circuit packs `K = romLanes w` entries per row when
`c.mainWidth == 1 + K * (w + 2)`; all other circuits contribute `1` entry per row. -/
def circuitRowWeight (c : SysCircuit) : Nat :=
  match circuitMemsegWidth? c with
  | some w =>
    let k := romLanes w
    if k > 1 && c.mainWidth == 1 + k * (w + 2) then k else 1
  | none => 1

/-- Collect all distinct `MEMSEG = 16` ROM payload widths declared by `sys.circuits`. -/
def romWidthsOfSystem (sys : StarkSystem) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for c in sys.circuits do
    if let some w := circuitMemsegWidth? c then
      if !out.contains w then
        out := out.push w
  return out

/-- Validate `MEMSEG = 16` closure pairs (`StarkVerifier.lean:706-731`, `batch.rs`):
even message list (at most `MAX_CLOSURE_PAIRS` pairs) paired as
`(pull -1 [16, w, a], push +1 [16, w, b])` with **strict** `a < b` (rejecting empty
`a == b` no-op grinding intervals) and strictly ascending widths or non-overlapping
intervals `prevB ≤ a`. -/
def checkClosurePairs (messages : Array BatchMessage) : Bool :=
  if messages.size % 2 != 0 || messages.size > 2 * MAX_CLOSURE_PAIRS then false
  else
    let numPairs := messages.size / 2
    Id.run do
      let mut prevW : Nat := 0
      let mut prevB : Nat := 0
      let mut hasPrev := false
      for i in [0:numPairs] do
        let some pull := messages[2 * i]? | return false
        let some push := messages[2 * i + 1]? | return false
        if pull.multiplicity.add Goldilocks.one != Goldilocks.zero then return false
        if push.multiplicity != Goldilocks.one then return false
        if pull.args.size != 3 || push.args.size != 3 then return false
        let some pullCh := pull.args[0]? | return false
        let some pushCh := push.args[0]? | return false
        if pullCh.toNat != MEMSEG_CHANNEL || pushCh.toNat != MEMSEG_CHANNEL then
          return false
        let some pullW := pull.args[1]? | return false
        let some pushW := push.args[1]? | return false
        let w := pullW.toNat
        if pushW.toNat != w then return false
        let some pullA := pull.args[2]? | return false
        let some pushB := push.args[2]? | return false
        let a := pullA.toNat
        let b := pushB.toNat
        if a ≥ b then return false
        if hasPrev then
          if w < prevW then return false
          if w == prevW && a < prevB then return false
        prevW := w
        prevB := b
        hasPrev := true
      return true

/-- Validate batch preamble bounds (`StarkVerifier.lean:815-901`, `batch.rs`),
returning `true` iff shard count, `C6`-weighted total batch rows `≤ MAX_BATCH_ROWS`,
per-shard activation/degree counts, active fixed-table requirements (rejecting inactive
preprocessed circuits unless `allowInactivePrep = true` in a raw `multi-stark` test harness),
`MEMSEG` closure pairs, and closure-pair ROM widths + shard-proportional pair count bound all hold.
When `allowBelowFloor = false` (default), also enforces the full Aiur security floor
(`checkSystem`). Optional `maxLogDeg` caps trace log-degree (default `32 - logBlowup`). -/
def validatePreambleWithFloor (sys : StarkSystem) (batch : BatchProof)
    (maxLogDeg : Nat := 32 - sys.params.logBlowup)
    (allowBelowFloor : Bool := false)
    (allowInactivePrep : Bool := false) : Bool :=
  let headers := batch.preamble.headers
  let messages := batch.preamble.messages
  if !checkSystemWithFloor sys allowBelowFloor then false
  else if headers.size == 0 || headers.size > MAX_BATCH_SHARDS then false
  else if batch.proofs.size != headers.size then false
  else if !checkClosurePairs messages then false
  else
    Id.run do
      let romWidths := romWidthsOfSystem sys
      let numPairs := messages.size / 2
      if numPairs > headers.size * romWidths.size then return false
      for i in [0:numPairs] do
        let some pull := messages[2 * i]? | return false
        let some wVal := pull.args[1]? | return false
        if !romWidths.contains wVal.toNat then return false
      let mut totalRows : Nat := 0
      for h in headers do
        if h.active.size != sys.circuits.size then return false
        let activeCount := h.active.foldl (fun acc b => if b then acc + 1 else acc) 0
        if activeCount == 0 || h.logDegrees.size != activeCount then return false
        if h.stage1Trace.size != 1 then return false
        let mut degPos : Nat := 0
        for ci in [0:sys.circuits.size] do
          let some act := h.active[ci]? | return false
          let some c := sys.circuits[ci]? | return false
          let some prepIdx := sys.preprocessedIndices[ci]? | return false
          if act then
            let some ld := h.logDegrees[degPos]? | return false
            degPos := degPos + 1
            if ld > maxLogDeg || ld + sys.params.logBlowup > 32 then return false
            if c.preprocessedHeight != 0 && (1 <<< ld) != c.preprocessedHeight then return false
            totalRows := totalRows + (1 <<< ld) * circuitRowWeight c
            if totalRows > MAX_BATCH_ROWS then return false
          else
            -- Reject inactive preprocessed/fixed-table circuits (parity with `StarkVerifier.lean:470,484` & `batch.rs:283`)
            if !allowInactivePrep && (c.preprocessedHeight != 0 || prepIdx.isSome) then return false
      return true

/-- Production batch preamble validation (strictly enforcing the Aiur security floor
and rejecting inactive preprocessed circuits). -/
def validatePreamble (sys : StarkSystem) (batch : BatchProof)
    (maxLogDeg : Nat := 32 - sys.params.logBlowup) : Bool :=
  validatePreambleWithFloor sys batch maxLogDeg false false

end Ix.Cert.MultiStark
