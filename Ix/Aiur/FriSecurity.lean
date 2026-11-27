module
public import Lean.Data.Json
public import Ix.Aiur.Parameters

/-!
# FRI soundness estimates

Soundness terms for a FRI-based STARK instance under candidate parameters, in
the unique-decoding, Johnson (list-decoding) and conjectured regimes. The input
is the instance statistics a key and a proof expose: `stark-verifier statistics
KEY PROOF` for an Aiur proof, or `fri_sizing --statistics outer-vk.bin` for the
compression stage's FRI key. `lake exe fri-security` (`Scripts/FriSecurity.lean`)
prints the terms.

The formulas follow `p3-security` at Plonky3 3152b14a for the unique-decoding,
conjectured and DEEP/ALI terms. The Johnson commit and batching terms are given
both in that revision's BCHKS25 form and in the DKT26 line-count form of Plonky3
main at 4615dcd. Lookups use multi-stark's documented `(W + 2) N / |F|` bound.
Each regime's security is its weakest term, as `p3-security` reports it.
-/

public section

namespace Aiur.FriSecurity

/-- The degree-3 Goldilocks extension: about 192 bits (default when `extensionDegree = 3`). -/
def fieldBits : Float := 192
/-- Field bit-width for a degree-`extensionDegree` Goldilocks extension (`64 * extensionDegree`). -/
def fieldBitsFor (extensionDegree : Nat) : Float := 64.0 * Float.ofNat (max extensionDegree 1)
/-- Classical collision resistance in bits of a sponge digest of `digestBytes`
bytes: the `log₂ N` at which CertiFRI's collision bound `3N²/(2·2^(8·digestBytes))`
reaches 1 (`P3/DigestCard.lean`, `digest_sponge_collision_exceeds_one_at_128`),
`8·digestBytes/2 − log₂(3/2)/2`: about 127.71 for 32 bytes, 191.71 for 48 and
255.71 for 64. -/
def collisionBitsFor (digestBytes : Nat) : Float :=
  4.0 * Float.ofNat digestBytes - Float.log2 1.5 / 2.0
/-- Collision resistance of the production 32-byte BLAKE3 digest (about 127.71 bits). -/
def collisionBits : Float := collisionBitsFor 32

/-- One circuit of an instance, as the statistics JSON gives it. -/
structure Circuit where
  main : Nat
  pre : Nat
  stage2 : Nat
  height : Nat
  lookups : Nat
  group : Nat
  maxDegree : Nat
  zeros : Nat
  maxLookupWidth : Nat
  deriving Inhabited

/-- The FRI parameters the terms depend on. -/
structure Parameters where
  logBlowup : Nat
  queries : Nat
  queryPow : Nat
  commitPow : Nat
  logArity : Nat
  extensionDegree : Nat := 3
  digestBytes : Nat := 32
  deriving Inhabited

/-- The parameters every Aiur proof uses (`Aiur.defaultFriParameters`). -/
def Parameters.default : Parameters where
  logBlowup := defaultCommitmentParameters.logBlowup
  queries := defaultFriParameters.numQueries
  queryPow := defaultFriParameters.queryProofOfWorkBits
  commitPow := defaultFriParameters.commitProofOfWorkBits
  logArity := defaultFriParameters.maxLogArity
  extensionDegree := 3
  digestBytes := 32

/-- `log_blowup · queries + query_pow`, the ethSTARK conjecture's metric. -/
def Parameters.conjecturedBits (p : Parameters) : Nat :=
  p.logBlowup * p.queries + p.queryPow

/-- Statistics of a key, and of a proof when it has trace heights. -/
structure Key where
  parameters : Parameters
  circuits : Array Circuit
  shards : Option Nat := none
  proofBytes : Option Nat := none
  deriving Inhabited

/-- The facts the bounds need. -/
structure Instance where
  logTrace : Nat
  columns : Nat
  constraints : Nat
  maxDegree : Nat
  lookupRows : Nat
  lookupWidth : Nat
  combo : Nat := 2
  /-- Minimum trace log-height across active circuits (`none` defaults to `logTrace`).
  Determines the tightest CertiFRI `DecodeMarginOff` `1/|D|` degree-slack term. -/
  minLogTrace : Option Nat := none
  /-- Total FRI opening claims `(Fri.claimRefs ...).length = 2*(main + pre + stage2) + extDeg*quotient`
  (`none` conservatively defaults to `2 * columns`). -/
  claimRefs : Option Nat := none
  /-- Maximum quotient-chunk count across circuits (`none` derived from `maxDegree`). -/
  maxQuotient : Option Nat := none
  deriving Inhabited

open Lean in
def Circuit.fromJson? (j : Json) : Except String Circuit := do
  return {
    main := ← j.getObjValAs? Nat "main", pre := ← j.getObjValAs? Nat "pre"
    stage2 := ← j.getObjValAs? Nat "stage2", height := ← j.getObjValAs? Nat "height"
    lookups := ← j.getObjValAs? Nat "lookups", group := ← j.getObjValAs? Nat "group"
    maxDegree := ← j.getObjValAs? Nat "max_degree", zeros := ← j.getObjValAs? Nat "zeros"
    maxLookupWidth := ← j.getObjValAs? Nat "max_lookup_width" }

open Lean in
def Key.fromJson? (j : Json) : Except String Key := do
  let circuits ← (← j.getObjValAs? (Array Json) "circuits").mapM Circuit.fromJson?
  return {
    parameters := {
      logBlowup := ← j.getObjValAs? Nat "log_blowup", queries := ← j.getObjValAs? Nat "num_queries"
      queryPow := ← j.getObjValAs? Nat "query_pow", commitPow := ← j.getObjValAs? Nat "commit_pow"
      logArity := ← j.getObjValAs? Nat "max_log_arity"
      extensionDegree := (j.getObjValAs? Nat "extension_degree").toOption.getD 3
      digestBytes := (j.getObjValAs? Nat "digest_bytes").toOption.getD 32 }
    circuits
    shards := (j.getObjValAs? Nat "shards").toOption
    proofBytes := (j.getObjValAs? Nat "proof_bytes").toOption }

/-- Omit the circuits at `drop` and give the circuits in `sets` a new
`(log height, main width)`, for hypothetical shapes. -/
def applyOverrides (circuits : Array Circuit) (drop : List Nat)
    (sets : List (Nat × Nat × Nat)) : Array Circuit := Id.run do
  let mut out := #[]
  for (c, i) in circuits.zipIdx do
    if drop.contains i then continue
    out := out.push <| match sets.find? (·.1 == i) with
      | some (_, logHeight, main) => { c with height := 2 ^ logHeight, main }
      | none => c
  return out

private def bitLength (n : Nat) : Nat := if n = 0 then 0 else n.log2 + 1

/-- Quotient chunks: the next power of two of `max_degree - 1`. -/
def Circuit.quotient (c : Circuit) : Nat := 2 ^ bitLength (max c.maxDegree 2 - 2)

/-- Effective minimum trace log-height across active circuits. -/
def Instance.effectiveMinLogTrace (inst : Instance) : Nat :=
  inst.minLogTrace.getD inst.logTrace

/-- Effective FRI opening claim count `(Fri.claimRefs ...).length`:
`2 * (main + pre + stage2) + extDeg * quotient` (conservatively `2 * columns` when omitted). -/
def Instance.effectiveClaimRefs (inst : Instance) : Nat :=
  inst.claimRefs.getD (2 * inst.columns)

/-- Effective maximum quotient-chunk count (`nextPow2 (max maxDegree 2 - 1)`). -/
def Instance.effectiveQuotient (inst : Instance) : Nat :=
  inst.maxQuotient.getD (2 ^ bitLength (max inst.maxDegree 2 - 2))

def instanceOf (circuits : Array Circuit) (extensionDegree : Nat := 3) : Instance where
  logTrace := (circuits.foldl (fun m (c : Circuit) => max m c.height) 0).log2
  columns := circuits.foldl
    (fun s (c : Circuit) => s + c.main + c.pre + c.stage2 + extensionDegree * c.quotient) 0
  constraints := circuits.foldl
    (fun s (c : Circuit) => s + c.zeros +
      extensionDegree * max 1 ((c.lookups + c.group - 1) / max c.group 1)) 0
  maxDegree := circuits.foldl (fun m (c : Circuit) => max m c.maxDegree) 0
  lookupRows := circuits.foldl (fun s (c : Circuit) => s + c.height * c.lookups) 0
  lookupWidth := circuits.foldl (fun m (c : Circuit) => max m c.maxLookupWidth) 0
  minLogTrace :=
    (circuits.foldl (fun acc (c : Circuit) =>
      if c.height == 0 then acc
      else match acc with
        | none => some c.height
        | some m => some (min m c.height)) none).map Nat.log2
  claimRefs := some <| circuits.foldl
    (fun s (c : Circuit) =>
      s + 2 * (c.main + c.pre + c.stage2) + extensionDegree * c.quotient) 0
  maxQuotient := some <| circuits.foldl (fun m (c : Circuit) => max m c.quotient) 1

private def log2 (x : Float) : Float := Float.log2 x
private def nat (n : Nat) : Float := Float.ofNat n
private def pow2 (x : Float) : Float := Float.pow 2 x

/-- Minimum trace log-height `ℓ` at which CertiFRI's `DecodeMarginOff`
(`2δ + ρ + 1 / 2^{ℓ + logBlowup} ≤ 1`) admits a positive decoding radius `δ > 0`. -/
def minPositiveUdLogTrace (logBlowup : Nat) : Nat :=
  if logBlowup ≤ 1 then 1 else 0

/-- CertiFRI `DecodeMarginOff` unique-decoding radius
`δ(ℓ) = max(0, (1 - 2^{-logBlowup} - 2^{-(ℓ + logBlowup)}) / 2)`,
accounting for CertiFRI's `+1` degree-slack term `1/|D|` (`2δ + ρ + 1/|D| ≤ 1`). -/
def certDeltaUd (logTrace logBlowup : Nat) : Float :=
  let lb := nat logBlowup
  let rho := pow2 (-lb)
  let d := pow2 (nat logTrace + lb)
  max 0.0 ((1.0 - rho - 1.0 / d) / 2.0)

/-- Minimum trace log-height `ℓ` (searching `0..32`) at which CertiFRI's `DecodeMarginOff`
query soundness reaches `targetBits` (default `Aiur.minProvableUdBits = 80`). -/
def minLogTraceForUdBits (p : Parameters)
    (targetBits : Float := Float.ofNat Aiur.minProvableUdBits) : Option Nat := Id.run do
  let queries := nat p.queries
  let queryPow := nat p.queryPow
  for ell in [0:33] do
    let delta := certDeltaUd ell p.logBlowup
    if delta > 0.0 then
      let qBits := queryPow - queries * log2 (1.0 - delta)
      if qBits ≥ targetBits then
        return some ell
  return none

/-- One regime's terms, in bits. -/
structure Regime where
  name : String
  terms : Array (String × Float)

/-- The weakest term. -/
def Regime.limit (r : Regime) : String × Float :=
  r.terms.foldl (fun best t => if t.2 < best.2 then t else best) ("none", 1.0e300)

/-- Every regime's terms for `inst` under `p`:
1. `CertiFRI proven UD`: matches the exact Lean-verified theorems
   (`goldilocks_pruned_fri_soundness` quadratic Berlekamp–Welch batching/commit over
   `(Fri.claimRefs ...).length` with folding arity `2^logArity`, `DecodeMarginOff`
   `2δ + ρ + 1/|D_min| ≤ 1` degree-slack radius at `ℓ_min`, `fractionLE_zeta_ood`
   tight off-domain `2*|D| + max(degreeTerm, (quotient + 1) * k)`, and
   `fractionLE_logup_pair_or_zero_denom` `(lookupWidth + 2) * lookupRows / |K|`).
2. `unique decoding`: ideal linear unique-decoding bound (`p3-security`).
3. `Johnson, BCHKS25` and `Johnson, DKT26`: list-decoding bounds (including `- log2 list`
   on ALI, DEEP, and lookup; DKT26 falls back to BCHKS25 when `logTrace = 0`).
4. `conjectured (2025/2010)`: ethSTARK / proximity-gap conjecture. -/
def terms (inst : Instance) (p : Parameters) : Array Regime := Id.run do
  let F := fieldBitsFor p.extensionDegree
  let colBits := collisionBitsFor p.digestBytes
  let lt := nat inst.logTrace
  let lb := nat p.logBlowup
  let n := pow2 (lt + lb)
  let k := pow2 lt
  let fold := max (pow2 (nat p.logArity) - 1) 1
  let arity := pow2 (nat (max p.logArity 1))
  let rho := pow2 (-lb)
  let combo := nat inst.combo
  let commitPow := nat p.commitPow
  let queryPow := nat p.queryPow
  let queries := nat p.queries
  let degreeTerm := nat inst.maxDegree * (k + combo - 1) + (k - 1)
  let certDegreeTerm := max degreeTerm ((nat inst.effectiveQuotient + 1.0) * k)
  let ali := F - log2 (max (nat inst.constraints) 1)
  let deep := F - log2 (max degreeTerm 1)
  let lookup := F - log2 (max ((nat inst.lookupWidth + 2) * nat inst.lookupRows) 1)
  let nf := max (nat inst.columns) 2
  let certClaims := max (nat inst.effectiveClaimRefs) 2
  let ellMin := inst.effectiveMinLogTrace
  let deltaUd := certDeltaUd ellMin p.logBlowup
  let certQuad := n * (deltaUd * n + 1.0) + 1.0
  let certDeep := F - log2 (max (2.0 * n + certDegreeTerm) 1)
  let certLookup := F - log2 (max ((nat inst.lookupWidth + 2) * nat inst.lookupRows) 1)
  let certBatch := F - log2 (max (certClaims * certQuad) 1)
  let certCommit := F - log2 (max (arity * certQuad) 1) + commitPow
  let certQuery := queryPow - queries * log2 (1.0 - deltaUd)
  let alpha := (1 + (k + combo) / n) / 2
  let udrCommit := F - log2 (max (fold * (n + 1)) 1) + commitPow
  let mut regimes := #[
    { name := "CertiFRI proven UD"
      terms := #[("ALI", ali), ("DEEP", certDeep), ("lookup", certLookup),
        ("batching", certBatch), ("commit", certCommit),
        ("query", certQuery), ("collision", colBits)] },
    { name := "unique decoding"
      terms := #[("ALI", ali), ("DEEP", deep), ("lookup", lookup),
        ("batching", F - ((lt + lb) + log2 (nf - 1))), ("commit", udrCommit),
        ("query", queryPow - queries * log2 alpha), ("collision", colBits)] }]
  for (label, lineCount) in [("Johnson, BCHKS25 (3152b14a)", false),
      ("Johnson, DKT26 (4615dcd)", true)] do
    let useLineCount := lineCount && inst.logTrace > 0
    let mut best : Option (Nat × Regime) := none
    for m in [3:300] do
      let ms := nat m + 0.5
      let (commitLinear, batching) :=
        if useLineCount then
          let lc := 3 + (lt + lb) + 3 * log2 ms - log2 3 - (log2 (1 - pow2 (-lt)) - lb)
          (F - lc - log2 fold + commitPow, F - (lc + log2 (nf - 1)))
        else
          let pp := 1 - Float.sqrt rho * (1 + 0.5 / nat m)
          let eps := ((2 * Float.pow ms 5 + 3 * ms * pp * rho) * n / (3 * rho * Float.sqrt rho)
            + ms / Float.sqrt rho) * fold
          (F - log2 (max eps 1) + commitPow,
            F - ((lt + lb) + log2 (2 * Float.pow ms 5 / 3) + 1.5 * lb + log2 (nf - 1)))
      let commit := min commitLinear
        (F - nat p.logArity - log2 (n + 1) - log2 (2 * nat m + 1) + 0.5 * log2 rho + commitPow)
      let list := ms / Float.sqrt rho
      let regime : Regime := {
        name := if lineCount && !useLineCount then
          "Johnson, DKT26 (lt=0 BCHKS25 fallback)" else label
        terms := #[("ALI", F - log2 list - log2 (max (nat inst.constraints) 1)),
          ("DEEP", F - log2 list - log2 (max degreeTerm 1)),
          ("lookup", lookup - log2 list),
          ("batching", batching), ("commit", commit),
          ("query", queryPow - queries * log2 ((1 + 0.5 / nat m) * Float.sqrt rho)),
          ("collision", colBits)] }
      match best with
      | some (_, b) => if regime.limit.2 > b.limit.2 then best := some (m, regime)
      | none => best := some (m, regime)
    if let some (m, r) := best then
      regimes := regimes.push { r with name := s!"{r.name}, m={m}" }
  let eta := ((log2 (Float.exp 1) + lb) * rho) / F
  regimes := regimes.push {
    name := "conjectured (2025/2010)"
    terms := #[("ALI", ali), ("DEEP", deep), ("lookup", lookup), ("commit", udrCommit),
      ("query", queries * (-log2 (rho + eta)) + queryPow), ("collision", colBits)] }
  return regimes

/-- `x` to two decimals. -/
def fmt (x : Float) : String :=
  if x.isNaN then "nan" else if x.isInf then (if x > 0 then "inf" else "-inf") else
  let r := (x * 100).round
  let sign := if r < 0 then "-" else ""
  let n := r.abs.toUInt64.toNat
  let frac := toString (n % 100)
  s!"{sign}{n / 100}.{if frac.length < 2 then "0" ++ frac else frac}"

/-- One parameter set's report: every regime's terms for `inst` (described by
`source`) under `p`. -/
def report (source : String) (inst : Instance) (p : Parameters) : String := Id.run do
  let ellMin := inst.effectiveMinLogTrace
  let minUdStr := match minLogTraceForUdBits p with
    | some ell => s!"ℓ ≥ {ell}"
    | none => "unreachable"
  let mut lines := #[
    s!"key: {source}, ext Fp^{p.extensionDegree}, blowup 2^{p.logBlowup}, " ++
      s!"{p.queries} queries, query pow {p.queryPow}, commit pow {p.commitPow}, " ++
      s!"arity 2^{p.logArity}, {p.conjecturedBits} conjectured query bits",
    s!"instance: trace 2^{inst.logTrace} (min trace 2^{ellMin}), {inst.columns} batched columns " ++
      s!"({inst.effectiveClaimRefs} FRI claim refs), {inst.constraints} constraints, " ++
      s!"max degree {inst.maxDegree} (quotient {inst.effectiveQuotient}), " ++
      s!"lookup rows {inst.lookupRows}, lookup width {inst.lookupWidth}",
    s!"CertiFRI DecodeMarginOff: δ(ℓ_min={ellMin}) = {fmt (certDeltaUd ellMin p.logBlowup)}, " ++
      s!"min ℓ for δ > 0: ℓ ≥ {minPositiveUdLogTrace p.logBlowup}, " ++
      s!"min ℓ for ≥{Aiur.minProvableUdBits}b UD: {minUdStr}"]
  for r in terms inst p do
    let (name, bits) := r.limit
    let detail := "  ".intercalate (r.terms.toList.map fun (t, b) => s!"{t} {fmt b}")
    lines := lines.push s!"  {r.name}: {fmt bits} bits (limited by {name})   {detail}"
  return "\n".intercalate lines.toList

/-- Security regime targeted by `--require-min-bits` / `--regime`. -/
inductive RegimeKind where
  | proven
  | johnson
  | conjectured
  deriving BEq, Repr

def RegimeKind.parse? : String → Option RegimeKind
  | "proven" => some .proven
  | "johnson" => some .johnson
  | "conjectured" => some .conjectured
  | _ => none

def RegimeKind.label : RegimeKind → String
  | .proven => "proven"
  | .johnson => "johnson"
  | .conjectured => "conjectured"

/-- Conservative (weakest) security bound in bits for `kind` on `(inst, p)`.
Returns `(regimeName, limitingTerm, bits)`. -/
def regimeSecurity (inst : Instance) (p : Parameters) (kind : RegimeKind) :
    String × String × Float :=
  let rs : Array Regime := terms inst p
  let selected : Array Regime := match kind with
    | .proven => rs.filter fun (r : Regime) => r.name == "CertiFRI proven UD"
    | .johnson => rs.filter fun (r : Regime) => r.name.startsWith "Johnson"
    | .conjectured => rs.filter fun (r : Regime) => r.name.startsWith "conjectured"
  selected.foldl (init := ("none", "none", 1.0e300)) fun best (r : Regime) =>
    let (termName, bits) := r.limit
    if bits < best.2.2 then (r.name, termName, bits) else best

/-- Check that `(inst, p)` achieves at least `minBits` in `kind`. -/
def checkMinBits (inst : Instance) (p : Parameters) (kind : RegimeKind) (minBits : Nat) :
    Except String (String × String × Float) :=
  let (rName, termName, bits) := regimeSecurity inst p kind
  if rName == "none" then
    .error s!"no matching regime for '{kind.label}'"
  else if bits ≥ Float.ofNat minBits then
    .ok (rName, termName, bits)
  else
    .error s!"regime '{kind.label}' ({rName}) yields {fmt bits} bits (limited by {termName}), below required {minBits} bits"

end Aiur.FriSecurity

end
