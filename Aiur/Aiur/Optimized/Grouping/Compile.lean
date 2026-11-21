import Aiur.Optimized.Grouping.Packets

namespace Aiur.Optimized.Grouping
open Circuit

variable {F : Type} [Field F] [DecidableEq F]

/-- Zero-coefficient terms are discarded. The remaining supports deliberately
ignore cancellation: this heuristic only chooses columns; `silent` checks it. -/
private def supports : Polynomial F → List (List Nat)
  | .const x => if x = 0 then [] else [[]]
  | .var v => [[v]]
  | .add a b | .sub a b => supports a ++ supports b
  | .mul a b => (supports a).flatMap fun x => (supports b).map fun y => (x ++ y).dedup

/-- Select the smallest-degree form while keeping the original expression
order. In particular `(1 - branch) * x` can become `(member - branch) * x`
when `branch` is private, avoiding a cubic lookup and its lifted column.
The row and packet certificates check the resulting expressions. -/
def selectArgument (selector : Nat) (privateCols : List Nat) (p : Polynomial F) : Polynomial F :=
  let direct := (gate selector privateCols p).simplify
  let better := fun a b : Polynomial F => if a.degree < b.degree then a else b
  if direct.degree ≤ 1 || silent privateCols p then direct else match p with
  | .add a b => better (Polynomial.simplify (.add (selectArgument selector privateCols a)
      (selectArgument selector privateCols b))) direct
  | .sub a b => better (Polynomial.simplify (.sub (selectArgument selector privateCols a)
      (selectArgument selector privateCols b))) direct
  | .mul a b =>
      let left := Polynomial.simplify (.mul (selectArgument selector privateCols a) b)
      let right := Polynomial.simplify (.mul a (selectArgument selector privateCols b))
      better left (better right direct)
  | _ => direct

def privateColumns (source : Chip F) (selector : Nat)
    (lookupArgs : List (Polynomial F) := []) (maxConstraintDegree : Nat := 3) :
    Except String (List Nat) := do
  let quiet := source.sends.map (·.enable) ++ source.memory.map (·.enable)
  let threshold := maxConstraintDegree - 1
  let required := source.constraints.filter (·.degree > threshold) ++ quiet
  let mut columns := [selector]
  let mut terms := (required.flatMap supports).filter fun xs => !xs.contains selector
  for _ in List.range source.numVars do
    if terms.isEmpty then break
    let candidates := terms.flatten.dedup
    let best := candidates.foldl (fun (best : Nat × Nat) v =>
      let score := terms.countP (·.contains v)
      if score > best.2 then (v, score) else best) (selector, 0)
    if best.2 == 0 then break
    columns := best.1 :: columns
    terms := terms.filter fun xs => !xs.contains best.1
  -- Cancellation can leave an empty support. A conservative fallback is still
  -- cheap for such uncommon chips, and the result is checked independently.
  for p in required do
    unless silent columns p do columns := (columns ++ Polynomial.vars p).dedup
  -- One additional private factor can silence many quadratic arguments.
  -- Keep only steps that remove at least one distinct materialization: the
  -- private-plus-lifted width cannot increase, and the shared width can shrink.
  let mut pending := (lookupArgs.filter fun p => (selectArgument selector columns p).degree > 2).dedup
  for _ in List.range source.numVars do
    let candidates := (pending.flatMap Polynomial.vars).dedup.filter fun v => !columns.contains v
    let best := candidates.foldl (fun (best : Nat × Nat) v =>
      let score := pending.countP fun p => (selectArgument selector (v :: columns) p).degree ≤ 2
      if score > best.2 then (v, score) else best) (selector, 0)
    if best.2 == 0 then break
    let next := best.1 :: columns
    let remaining := pending.filter fun p => (selectArgument selector next p).degree > 2
    if remaining.length ≥ pending.length then break
    columns := next
    pending := remaining
  unless required.all (silent columns) do throw s!"cannot silence group member {source.name}"
  unless columns.all (· < source.numVars) do throw "group private column out of bounds"
  return columns.mergeSort (· ≤ ·)

/-! ### `C7a` / `C7b` / `C2` Heuristics (all verified downstream by `Grouping.certify`) -/

private structure BucketSortKey where
  maxArgDeg : Nat
  enableDeg : Nat
  width : Nat
  channelTag : Nat
  channelId : Nat
  origIdx : Nat

private def bucketSortKeyLe (a b : BucketSortKey) : Bool :=
  if a.maxArgDeg != b.maxArgDeg then a.maxArgDeg > b.maxArgDeg
  else if a.enableDeg != b.enableDeg then a.enableDeg > b.enableDeg
  else if a.width != b.width then a.width > b.width
  else if a.channelTag != b.channelTag then a.channelTag < b.channelTag
  else if a.channelId != b.channelId then a.channelId < b.channelId
  else a.origIdx ≤ b.origIdx

private def lookupChannelKey (id : String → Except String Nat) (origin : Chip F) (k : Nat) :
    Nat × Nat :=
  if hk : k < origin.sends.length then
    let s := origin.sends[k]'hk
    (1, (id s.channel).toOption.getD 0)
  else if hm : k - origin.sends.length < origin.memory.length then
    let mem := origin.memory[k - origin.sends.length]'hm
    (2, mem.value.words.length)
  else
    (3, k)

private def minChannelKey (id : String → Except String Nat) (origin : Chip F) (B : List Nat) :
    Nat × Nat :=
  match B with
  | [] => (3, 0)
  | k :: ks =>
      ks.foldl (fun best j =>
        let cand := lookupChannelKey id origin j
        if cand.1 < best.1 || (cand.1 == best.1 && cand.2 < best.2) then cand else best)
        (lookupChannelKey id origin k)

/-- Build intra-chip mutually-exclusive raw-packet buckets (`C2`) for one member.
Returns a partition of `List.range origRequired.length` where every bucket is
sorted in ascending index order. Deg-1-only buckets that would rise to deg-2
only merge when `bucket.length ≥ 3` (so `retune` `g=4→2` strictly wins), while
deg-2 buckets (or merges staying deg ≤ 1) merge freely (`≥ 2`). -/
private def buildCompactBuckets (origin : Chip F) (selector : Nat) (privateCols : List Nat)
    (origRequired actRequired : List (Lookup F)) (optimizeLookups : Bool) :
    List (List Nat) := Id.run do
  let n := origRequired.length
  if n < 2 then return (List.range n).map fun k => [k]
  let ctx := ExclCtx.ofConstraints origin.constraints
  let selFn (p : Polynomial F) : Polynomial F :=
    if optimizeLookups then selectArgument selector privateCols p
    else (gate selector privateCols p).simplify
  let mut eligible : List (Nat × Nat × Nat × Nat) := []
  let mut singletons : List (List Nat) := []
  for k in List.range n do
    let origL := lookupAt origRequired k
    let actL := lookupAt actRequired k
    let origArgDeg := origL.args.foldl (fun acc w => max acc w.degree) 0
    if ctx.isBool origL.enable then
      let mut ok := true
      let mut gDeg := 0
      for w in actL.args do
        let raw :=
          if ctx.isZeroWhenOff origL.enable w then w
          else Polynomial.simplify (.mul actL.enable w)
        let sel := selFn raw
        if sel.degree > 2 then
          ok := false
          break
        gDeg := max gDeg sel.degree
      if ok then
        eligible := eligible ++ [(k, origArgDeg, gDeg, actL.args.length)]
      else
        singletons := singletons ++ [[k]]
    else
      singletons := singletons ++ [[k]]
  if eligible.length < 2 then return (List.range n).map fun k => [k]
  -- Pack deg-2 and wider lookups first so compatible partners join them.
  let sortedElig := eligible.mergeSort fun a b =>
    if a.2.1 != b.2.1 then a.2.1 > b.2.1
    else if a.2.2.2 != b.2.2.2 then a.2.2.2 > b.2.2.2
    else a.1 ≤ b.1
  let mut buckets : List (List (Nat × Nat × Nat × Nat)) := []
  for item in sortedElig do
    let k := item.1
    let ek := (lookupAt origRequired k).enable
    let mut bestIdx : Option Nat := none
    let mut bestScore : Nat × Nat := (0, 0)
    for (b, bIdx) in buckets.zipIdx do
      let compat := b.all fun prev =>
        let ep := (lookupAt origRequired prev.1).enable
        ctx.isExcl ep ek && ctx.isExcl ek ep
      if compat then
        let curMaxW := b.foldl (fun acc x => max acc x.2.2.2) 0
        let newMaxW := max curMaxW item.2.2.2
        let extraW := newMaxW - curMaxW
        let hasDeg2 := if b.any (fun x => x.2.1 ≥ 2) then 0 else 1
        let score := (hasDeg2, extraW)
        match bestIdx with
        | none =>
            bestIdx := some bIdx
            bestScore := score
        | some _ =>
            if score.1 < bestScore.1 || (score.1 == bestScore.1 && score.2 < bestScore.2) then
              bestIdx := some bIdx
              bestScore := score
    match bestIdx with
    | some idx =>
        buckets := buckets.modify idx fun b => b ++ [item]
    | none =>
        buckets := buckets ++ [[item]]
  let mut finalBuckets : List (List Nat) := singletons
  for b in buckets do
    let ks := (b.map Prod.fst).mergeSort (· ≤ ·)
    if ks.length ≤ 1 then
      finalBuckets := finalBuckets ++ [ks]
    else
      let hadDeg2 := b.any fun x => x.2.1 ≥ 2
      let mergedDeg := b.foldl (fun acc x => max acc x.2.2.1) 0
      let profitable := hadDeg2 || mergedDeg ≤ 1 || ks.length ≥ 3
      let certOK := profitable &&
        ctx.allPairwiseExcl (ks.map fun k => (lookupAt origRequired k).enable)
      if certOK then
        finalBuckets := finalBuckets ++ [ks]
      else
        finalBuckets := finalBuckets ++ (ks.map fun k => [k])
  return finalBuckets

/-- Local mirror of `lookup_groups::retune`'s `q = 4` dominance check (at standard
`blowup = 4`, `extDegree = 2`) used by `C7b` to decide whether a group already
runs at quotient degree `q = 4` (so allowing constraint degree up to `5` is free). -/
private def divCeilNat (a b : Nat) : Nat :=
  let b' := max b 1
  (a + b' - 1) / b'

private def nextPow2Nat (n : Nat) : Nat :=
  if n = 0 then 0
  else if n ≤ 1 then 1
  else 2 ^ (Nat.log2 (n - 1) + 1)

private def chunkLogupDeg (degs : List (Nat × Nat)) : Nat :=
  let sumP := (degs.map Prod.snd).sum
  let prod := sumP + 1
  let mult := degs.foldl (fun acc (md, pd) => max acc (md + sumP - pd)) 0
  max prod mult

private def logupDegChunks (degs : List (Nat × Nat)) (groupSize : Nat) : Nat :=
  let step := max groupSize 1
  let rec go : Nat → List (Nat × Nat) → Nat → Nat
    | 0, _, acc => acc
    | _ + 1, [], acc => acc
    | fuel + 1, ys, acc =>
        go fuel (ys.drop step) (max acc (chunkLogupDeg (ys.take step)))
  if degs.isEmpty then 1 else go degs.length degs 0

private def fftCostFor (stage2 quotient : Nat) (blowup : Nat := 4) (extDeg : Nat := 2) :
    Nat × Nat × Nat × Nat :=
  let logQ := Nat.log2 quotient
  let logB := Nat.log2 blowup
  let qd := quotient * extDeg
  let trace := (blowup + 1) * stage2
  let slope := (blowup + 1) * (stage2 + qd)
  let intercept := qd * (logQ + blowup * logB)
  let one := trace + qd * (max logQ 1 + blowup * max logB 1)
  let two := slope + intercept
  (one, two, slope, intercept)

private def costNoWorse (a b : Nat × Nat × Nat × Nat) : Bool :=
  a.1 ≤ b.1 && a.2.1 ≤ b.2.1 && a.2.2.1 ≤ b.2.2.1

private def costScoreLt (a b : Nat × Nat × Nat × Nat) : Bool :=
  a.2.2.1 < b.2.2.1 ||
    (a.2.2.1 == b.2.2.1 &&
      (a.2.2.2 < b.2.2.2 || (a.2.2.2 == b.2.2.2 && a.1 < b.1)))

/-- Returns `true` when `lookup_groups::retune` (at standard `blowup = 4`,
`extDegree = 2`) already selects quotient degree `q ≥ 4` for `layout`. -/
def layoutUsesQuotientFour (layout : Layout F) (blowup : Nat := 4) (extDeg : Nat := 2) : Bool :=
  let userMax := max 2 (layout.constraints.foldl (fun acc p => max acc p.degree) 0)
  let recvArgDeg := layout.receive.foldl (fun acc p => max acc p.degree) 0
  let sendDegs := layout.sends.map fun s =>
    (s.enable.degree, s.args.foldl (fun acc p => max acc p.degree) 0)
  let degs := (1, recvArgDeg) :: sendDegs
  let n := degs.length
  let initMaxDeg := max userMax (logupDegChunks degs 1)
  let initQ := nextPow2Nat (max initMaxDeg 2 - 1)
  if initQ ≥ 4 then true
  else
    let initS2 := max (divCeilNat n 1) 1 * extDeg
    let initCost := fftCostFor initS2 initQ blowup extDeg
    let maxGroup := max 1 (min n 8)
    let (_, bestQ) := (List.range maxGroup).foldl (fun (bestCost, bestQ) g0 =>
      let g := g0 + 1
      let maxD := max userMax (logupDegChunks degs g)
      let q := nextPow2Nat (max maxD 2 - 1)
      if q > blowup then (bestCost, bestQ)
      else
        let s2 := max (divCeilNat n g) 1 * extDeg
        let c := fftCostFor s2 q blowup extDeg
        if costNoWorse c bestCost && costScoreLt c bestCost then (c, q)
        else (bestCost, bestQ)) (initCost, initQ)
    bestQ ≥ 4

/-- Build a candidate grouped layout with an explicit maximum constraint degree
budget `constraintCap` (normally `3` for `q = 2` groups or `5` for `q = 4` groups). -/
def candidateWithCap (name : String) (id : String → Except String Nat)
    (sources : List (Chip F)) (optimizeLookups : Bool := true)
    (compactRaw : Bool := true) (constraintCap : Nat := 3) : Except String (Layout F) := do
  unless sources.length ≥ 1 do throw "a function group needs at least one member"
  let selected ← sources.mapM fun origin => do
    let chip := Activation.compile origin
    let (provided, required) ← messages id chip
    let args := if optimizeLookups then provided ++ required.flatMap (·.args) else []
    return (origin, ← privateColumns chip origin.numVars args constraintCap)
  let shared := selected.foldl (fun n (origin, privateCols) =>
    max n (origin.numVars + 1 - privateCols.length)) 0
  let mut next := shared
  let mut members : List (Member F) := []
  let mut receive : List (Polynomial F) := []
  let mut sends : List (Lookup F) := []
  for (origin, privateCols) in selected do
    let chip := Activation.compile origin
    let selector := origin.numVars
    let sharedCols := (List.range chip.numVars).filter fun v => !privateCols.contains v
    let columns := (List.range chip.numVars).map fun v =>
      if privateCols.contains v then next + privateCols.idxOf v else sharedCols.idxOf v
    next := next + privateCols.length
    let columns := columns.toArray
    let root := columns[selector]?.getD 0
    let ren := rename columns
    let (_, origRequired) ← messages id origin
    let (provided, actRequired) ← messages id chip
    let mut writes : List (Nat × Polynomial F) := []
    let mut recvOut : List (Polynomial F) := []
    for p in provided do
      unless p.degree ≤ 2 do throw s!"lookup degree exceeds two in {chip.name}"
      let sel := if optimizeLookups then selectArgument selector privateCols p
        else (gate selector privateCols p).simplify
      let value ← if sel.degree ≤ 2 then
        pure (ren sel).simplify
      else do
        let rp := ren p
        if let some (column, _) := writes.find? (fun (_, value) => value == rp) then
          pure (.var column)
        else
          let column := next
          next := next + 1
          writes := writes ++ [(column, rp)]
          pure (.var column)
      recvOut := recvOut ++ [value]
    receive := plusArgs receive recvOut
    let numLookups := actRequired.length
    let rawBuckets :=
      if compactRaw then
        buildCompactBuckets origin selector privateCols origRequired actRequired optimizeLookups
      else
        (List.range numLookups).map fun k => [k]
    let needCtx := rawBuckets.any fun B => B.length > 1
    let ctxOpt : Option (ExclCtx F) :=
      if needCtx then some (ExclCtx.ofConstraints origin.constraints) else none
    let mut builtBuckets : List (List Nat × Lookup F × BucketSortKey) := []
    for B in rawBuckets do
      match B with
      | [] => pure ()
      | [k] =>
          let actL := lookupAt actRequired k
          let mut out : List (Polynomial F) := []
          for p in actL.args do
            unless p.degree ≤ 2 do throw s!"lookup degree exceeds two in {chip.name}"
            let sel := if optimizeLookups then selectArgument selector privateCols p
              else (gate selector privateCols p).simplify
            let value ← if sel.degree ≤ 2 then
              pure (ren sel).simplify
            else do
              let rp := ren p
              if let some (column, _) := writes.find? (fun (_, value) => value == rp) then
                pure (.var column)
              else
                let column := next
                next := next + 1
                writes := writes ++ [(column, rp)]
                pure (.var column)
            out := out ++ [value]
          let en := (ren actL.enable).simplify
          let lk := Lookup.mk en out
          let (tag, chId) := lookupChannelKey id origin k
          let key : BucketSortKey := {
            maxArgDeg := out.foldl (fun acc p => max acc p.degree) 0
            enableDeg := en.degree
            width := out.length
            channelTag := tag
            channelId := chId
            origIdx := k }
          builtBuckets := builtBuckets ++ [([k], lk, key)]
      | _ =>
          let ctx := ctxOpt.getD (ExclCtx.ofConstraints origin.constraints)
          let maxW := B.foldl (fun acc k => max acc (lookupAt actRequired k).args.length) 0
          let mut out : List (Polynomial F) := []
          for w in List.range maxW do
            let mut accWord : Polynomial F := .const 0
            for k in B do
              let origL := lookupAt origRequired k
              let actL := lookupAt actRequired k
              let p := word actL.args w
              let raw :=
                if ctx.isZeroWhenOff origL.enable p then p
                else Polynomial.simplify (.mul actL.enable p)
              let sel := if optimizeLookups then selectArgument selector privateCols raw
                else (gate selector privateCols raw).simplify
              let value ← if sel.degree ≤ 2 then
                pure (ren sel).simplify
              else do
                let rp := ren raw
                if let some (column, _) := writes.find? (fun (_, value) => value == rp) then
                  pure (.var column)
                else
                  let column := next
                  next := next + 1
                  writes := writes ++ [(column, rp)]
                  pure (.var column)
              accWord := plus accWord value
            out := out ++ [accWord]
          let en := sum (B.map fun k => (ren (lookupAt actRequired k).enable).simplify)
          let lk := Lookup.mk en out
          let (tag, chId) := minChannelKey id origin B
          let key : BucketSortKey := {
            maxArgDeg := out.foldl (fun acc p => max acc p.degree) 0
            enableDeg := en.degree
            width := out.length
            channelTag := tag
            channelId := chId
            origIdx := B.headD 0 }
          builtBuckets := builtBuckets ++ [(B, lk, key)]
    -- `C7a`: Sort buckets by `(maxArgDeg desc, enableDeg desc, width desc, channel)`
    -- so degree-2 lookups align across members instead of smearing across degree-1 slots.
    let sortedBuckets :=
      if optimizeLookups then
        builtBuckets.mergeSort fun a b => bucketSortKeyLe a.2.2 b.2.2
      else
        builtBuckets
    let mut slotArr := Array.replicate numLookups 0
    for ((B, _, _), s) in sortedBuckets.zipIdx do
      for k in B do
        if k < slotArr.size then
          slotArr := slotArr.set! k s
    let isIdentity := (List.range numLookups).all fun k => slotArr[k]?.getD k == k
    let slotMap := if isIdentity then #[] else slotArr
    let memberLookups := sortedBuckets.map fun (_, lk, _) => lk
    sends := (List.range (max sends.length memberLookups.length)).map fun i =>
      let a := sends[i]?.getD ⟨.const 0, []⟩
      let b := memberLookups[i]?.getD ⟨.const 0, []⟩
      ⟨plus a.enable b.enable, plusArgs a.args b.args⟩
    members := members ++ [⟨chip.name, columns, root, writes, origin, privateCols, slotMap⟩]
  let layout := Layout.mk name next members receive sends
  unless layout.constraints.all (fun p => p.degree ≤ constraintCap && p.inBounds next) do
    throw s!"group {name} exceeds degree or column budget"
  unless (receive ++ sends.flatMap (·.args)).all (fun p => p.degree ≤ 2 && p.inBounds next) &&
      sends.all (fun s => s.enable.degree ≤ 2 && s.enable.inBounds next) do
    throw s!"group {name} has invalid lookup expressions"
  return layout

/-- Members retain their call identities, even when several typed functions
already share one physical chip. Activate each source before choosing columns.
When `maxConstraintDegree` is `none` and `optimizeLookups` is enabled, `C7b`
automatically relaxes the constraint degree budget from `3` to `5` whenever the
group already runs at quotient degree `q = 4` and the relaxation strictly
reduces width. -/
def candidate (name : String) (id : String → Except String Nat)
    (sources : List (Chip F)) (optimizeLookups : Bool := true)
    (compactRaw : Bool := true) (maxConstraintDegree : Option Nat := none) :
    Except String (Layout F) := do
  match maxConstraintDegree with
  | some cap =>
      candidateWithCap name id sources optimizeLookups compactRaw cap
  | none =>
      let base ← candidateWithCap name id sources optimizeLookups compactRaw 3
      if optimizeLookups && layoutUsesQuotientFour base then
        match candidateWithCap name id sources optimizeLookups compactRaw 5 with
        | .ok relaxed =>
            if relaxed.width < base.width then return relaxed else return base
        | .error _ => return base
      else
        return base

/-- The compiler returns a proof-bearing result; uncertified layouts cannot
reach the exporter. Column selection remains an untrusted heuristic. -/
def compile (name : String) (id : String → Except String Nat) (sources : List (Chip F))
    (optimizeLookups : Bool := true) (compactRaw : Bool := true)
    (maxConstraintDegree : Option Nat := none) :
    Except String (Checked sources id) := do
  certify sources id (← candidate name id sources optimizeLookups compactRaw maxConstraintDegree)

end Aiur.Optimized.Grouping
