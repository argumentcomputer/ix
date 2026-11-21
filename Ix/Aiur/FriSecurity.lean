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

/-- The degree-2 Goldilocks extension: about 128 bits. -/
def fieldBits : Float := 128
/-- BLAKE3 collision resistance. -/
def collisionBits : Float := 128

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
  deriving Inhabited

/-- The parameters every Aiur proof uses (`Aiur.defaultFriParameters`). -/
def Parameters.default : Parameters where
  logBlowup := defaultCommitmentParameters.logBlowup
  queries := defaultFriParameters.numQueries
  queryPow := defaultFriParameters.queryProofOfWorkBits
  commitPow := defaultFriParameters.commitProofOfWorkBits
  logArity := defaultFriParameters.maxLogArity

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
      logArity := ← j.getObjValAs? Nat "max_log_arity" }
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

def instanceOf (circuits : Array Circuit) : Instance where
  logTrace := (circuits.foldl (fun m (c : Circuit) => max m c.height) 0).log2
  columns := circuits.foldl (fun s (c : Circuit) => s + c.main + c.pre + c.stage2 + 2 * c.quotient) 0
  constraints := circuits.foldl
    (fun s (c : Circuit) => s + c.zeros + 2 * max 1 ((c.lookups + c.group - 1) / max c.group 1)) 0
  maxDegree := circuits.foldl (fun m (c : Circuit) => max m c.maxDegree) 0
  lookupRows := circuits.foldl (fun s (c : Circuit) => s + c.height * c.lookups) 0
  lookupWidth := circuits.foldl (fun m (c : Circuit) => max m c.maxLookupWidth) 0

private def log2 (x : Float) : Float := Float.log2 x
private def nat (n : Nat) : Float := Float.ofNat n
private def pow2 (x : Float) : Float := Float.pow 2 x

/-- One regime's terms, in bits. -/
structure Regime where
  name : String
  terms : Array (String × Float)

/-- The weakest term. -/
def Regime.limit (r : Regime) : String × Float :=
  r.terms.foldl (fun best t => if t.2 < best.2 then t else best) ("none", 1.0e300)

/-- Every regime's terms for `inst` under `p`. -/
def terms (inst : Instance) (p : Parameters) : Array Regime := Id.run do
  let F := fieldBits
  let lt := nat inst.logTrace
  let lb := nat p.logBlowup
  let n := pow2 (lt + lb)
  let k := pow2 lt
  let fold := pow2 (nat p.logArity) - 1
  let rho := pow2 (-lb)
  let combo := nat inst.combo
  let commitPow := nat p.commitPow
  let queryPow := nat p.queryPow
  let queries := nat p.queries
  let degreeTerm := nat inst.maxDegree * (k + combo - 1) + (k - 1)
  let ali := F - log2 (nat inst.constraints)
  let deep := F - log2 degreeTerm
  let lookup := F - log2 ((nat inst.lookupWidth + 2) * nat inst.lookupRows)
  let nf := nat inst.columns
  let alpha := (1 + (k + combo) / n) / 2
  let udrCommit := F - log2 (fold * (n + 1)) + commitPow
  let mut regimes := #[{
    name := "unique decoding"
    terms := #[("ALI", ali), ("DEEP", deep), ("lookup", lookup),
      ("batching", F - ((lt + lb) + log2 (nf - 1))), ("commit", udrCommit),
      ("query", queryPow - queries * log2 alpha), ("collision", collisionBits)] }]
  for (label, lineCount) in [("Johnson, BCHKS25 (3152b14a)", false),
      ("Johnson, DKT26 (4615dcd)", true)] do
    let mut best : Option (Nat × Regime) := none
    for m in [3:300] do
      let ms := nat m + 0.5
      let (commitLinear, batching) :=
        if lineCount then
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
        name := label
        terms := #[("ALI", F - log2 list - log2 (nat inst.constraints)),
          ("DEEP", F - log2 list - log2 degreeTerm), ("lookup", lookup),
          ("batching", batching), ("commit", commit),
          ("query", queryPow - queries * log2 ((1 + 0.5 / nat m) * Float.sqrt rho)),
          ("collision", collisionBits)] }
      match best with
      | some (_, b) => if regime.limit.2 > b.limit.2 then best := some (m, regime)
      | none => best := some (m, regime)
    if let some (m, r) := best then
      regimes := regimes.push { r with name := s!"{label}, m={m}" }
  let eta := ((log2 (Float.exp 1) + lb) * rho) / F
  regimes := regimes.push {
    name := "conjectured (2025/2010)"
    terms := #[("ALI", ali), ("DEEP", deep), ("lookup", lookup), ("commit", udrCommit),
      ("query", queries * (-log2 (rho + eta)) + queryPow), ("collision", collisionBits)] }
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
  let mut lines := #[
    s!"key: {source}, blowup 2^{p.logBlowup}, " ++
      s!"{p.queries} queries, query pow {p.queryPow}, commit pow {p.commitPow}, " ++
      s!"arity 2^{p.logArity}, {p.conjecturedBits} conjectured query bits",
    s!"instance: trace 2^{inst.logTrace}, {inst.columns} batched columns, " ++
      s!"{inst.constraints} constraints, max degree {inst.maxDegree}, " ++
      s!"lookup rows {inst.lookupRows}, lookup width {inst.lookupWidth}"]
  for r in terms inst p do
    let (name, bits) := r.limit
    let detail := "  ".intercalate (r.terms.toList.map fun (t, b) => s!"{t} {fmt b}")
    lines := lines.push s!"  {r.name}: {fmt bits} bits (limited by {name})   {detail}"
  return "\n".intercalate lines.toList

end Aiur.FriSecurity

end
