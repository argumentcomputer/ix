import Ix.Compile.CircuitContract

/-! # Pure Annotated Lean 4 `MultiStark/BN/KzgAlgebra` Vertical Slice (`KzgAlgebraPure`)

Faithful, idiomatic pure Lean 4 port of `MultiStark/MultiStark/BN/KzgAlgebra.lean`
(together with `KzgDeserialize::Node`, `KzgDeserialize::Lookup`, and `KzgShape::power2`),
annotated with `open scoped Ix.Circuit` directives (`@[circuit_inline]`,
`@[circuit_noinline]`, `@[circuit_budget ...]`).

## Design Notes

* **Zero forbidden constructs**: pure total Lean 4 only — every recursive function
  uses structural recursion (`termination_by structural`), with zero `sorry`,
  `admit`, `axiom`, `partial`, `unsafe`, `native_decide`, `bv_decide`,
  `@[extern]`, or `@[implemented_by]`.
* **Monomorphic recursive ADTs**: `IxCC.Fir.ShapeInfer` assigns one monovariant
  `DataDecl` per Lean inductive type. Domain-specific monomorphic types (`FList`,
  `Node`, `NodeList`, `Lookup`, `LookupList`, `Context`, `GroupSummaryResult`,
  `FrameInput`) mirror Formal Aiur's monomorphized `Lists::List<T>` enums and
  keep every struct and list strictly unboxed (zero fallback to universal `Obj`).
* **Bounded structural DAG depth (`Depth.Structural` = 0 depth columns)**:
  `evalAt` counts down a structural depth fuel (`fuel + 1 => fuel`), `expPower2`
  and `power2Mod` count down `log`, `groupSummary` counts down `remaining`,
  `foldLookupsFuel` counts down group fuel, and `fListGet`, `nodeListGet`,
  `fingerprint`, `polynomial`, `foldRoots`, `lookupFingerprint` descend
  structurally on their list arguments.
* **Parameteric prime modulus `p`**: every algebraic operation is parameterized
  over a prime `p : Nat` with canonical field representatives `< p`. Pure Lean
  `#guard` tests verify exact semantics across `p = 65537` (`2^16 + 1`),
  28-bit NTT prime `p = 167772161` (`5 * 2^25 + 1`, `(p - 1)^2 < 2^56`),
  **BN254 `Fr`** (exact `two_adic_gen(28)` from `KzgAlgebra.lean`), and
  **BLS12-381 `Fr`** (exact 32-adic generator).
* **Two `Nat`-argument STARK benchmark entrypoints** (over `p = 65537`,
  where `(p - 1)^2 = 2^32 < 2^56` fits `mul_56`/`divmod_56` under
  `TableTier.byte256`):
  1. `KzgAlgebraPure.entryEvalFold (zeta main0 q0 q1 : Nat) : Nat` — exercises
     `expPower2`, `evalAt` over all 10 `Node` constructors (all 6 row selectors
     and all 4 public columns), `foldRoots`, and `polynomial` Horner evaluation,
     returning `1` iff the vanishing/selector and quotient relations hold.
  2. `KzgAlgebraPure.entryFullFrame (zeta main0 stage2_0 q0 : Nat) : Nat` —
     exercises the complete `verifyFrameQuotient` pipeline (`expPower2`,
     `twoAdicGen`, `power2Mod`, `evalAt`, `foldRoots`, `lookupFingerprint`,
     multi-group `groupSummary`, `foldLookups`, `polynomial`, and the quotient
     equality check), returning `1` on valid frames and `0` on any tampered
     challenge, opening, running sum, or quotient.
-/

set_option autoImplicit false

open scoped Ix.Circuit

namespace KzgAlgebraPure

/-! ## Monomorphic AST, Lists, and Evaluation Context (`ShapeInfer`-unboxed) -/

/-- Monomorphic list of field elements (`Lists::List<Field>` / `KzgAlgebra::Values`). -/
inductive FList where
  | nil
  | cons (head : Nat) (tail : FList)
  deriving BEq, DecidableEq, Repr

/-- Monomorphic list of field-element lists (`Lists::List<Values>` for `claimsAccumulator`). -/
inductive FListList where
  | nil
  | cons (head : FList) (tail : FListList)
  deriving BEq, DecidableEq, Repr

/-- AIR constraint expression DAG node (`KzgDeserialize::Node`).
`var source offset column` uses `source ∈ {0: fixed, 1: main, 2: stage2}` and
`offset ∈ {0: current row, 1: next row}` matching `KzgAlgebra::eval_at`. -/
inductive Node where
  | const (value : Nat)
  | var (source offset column : Nat)
  | pub (index : Nat)
  | first
  | last
  | transition
  | add (a b : Nat)
  | sub (a b : Nat)
  | mul (a b : Nat)
  | neg (a : Nat)
  deriving BEq, DecidableEq, Repr

/-- Monomorphic list of AIR DAG nodes (`Lists::List<KzgDeserialize::Node>`). -/
inductive NodeList where
  | nil
  | cons (head : Node) (tail : NodeList)
  deriving BEq, DecidableEq, Repr

/-- One logUp lookup descriptor (`KzgDeserialize::Lookup::Mk(multiplicity, args)`). -/
structure Lookup where
  multiplicity : Nat
  args : FList
  deriving BEq, DecidableEq, Repr

/-- Monomorphic list of logUp lookups (`Lists::List<KzgDeserialize::Lookup>`). -/
inductive LookupList where
  | nil
  | cons (head : Lookup) (tail : LookupList)
  deriving BEq, DecidableEq, Repr

/-- Evaluation context for `evalAt` (`KzgAlgebra::Context`), holding current/next
opened trace rows, the 4 public inputs `[beta, gamma, acc, nextAcc]`, and
Lagrange/transition selectors `(first, last, transition)`. -/
structure Context where
  main : FList
  mainNext : FList
  fixed : FList
  fixedNext : FList
  stage2 : FList
  stage2Next : FList
  pub0 : Nat
  pub1 : Nat
  pub2 : Nat
  pub3 : Nat
  first : Nat
  last : Nat
  transition : Nat
  deriving BEq, DecidableEq, Repr

/-- Monomorphic result of `groupSummary`, mirroring `(Field, Field, Lists::List<Lookup>)`. -/
structure GroupSummaryResult where
  product : Nat
  numerator : Nat
  rest : LookupList
  deriving BEq, DecidableEq, Repr

/-- Complete single-frame input for `verifyFrameQuotient` (`KzgShape::Frame` +
verified inverse/selector witnesses matching Formal Aiur's field divisions). -/
structure FrameInput where
  nodes : NodeList
  roots : FList
  lookups : LookupList
  groupSize : Nat
  maxDepth : Nat
  log : Nat
  genMax : Nat
  maxLog : Nat
  invG : Nat
  first : Nat
  last : Nat
  injection : Nat
  main : FList
  mainNext : FList
  fixed : FList
  fixedNext : FList
  stage2 : FList
  stage2Next : FList
  quotientOpen : FList
  beta : Nat
  gamma : Nat
  alpha : Nat
  zeta : Nat
  acc : Nat
  nextAcc : Nat
  deriving BEq, DecidableEq, Repr

/-! ## Modular Field Arithmetic over Prime `p` (Canonical Inputs `< p`) -/

/-- Field addition `(a + b) mod p`.
Branchless formulation avoids join-point splitting inside recursive callers
(`groupSummary`, `foldLookupsFuel`), keeping every recursive chip self-recursive
with 0 depth columns under `Depth.Structural`. -/
@[circuit_noinline]
def addMod (p a b : Nat) : Nat :=
  (a + b) % p

/-- Field subtraction `(a - b) mod p` for canonical `b ≤ p`.
Branchless formulation avoids `Nat` underflow and keeps every recursive caller
join-point-free (0 depth columns under `Depth.Structural`). -/
@[circuit_noinline]
def subMod (p a b : Nat) : Nat :=
  (a + p - b) % p

/-- Field negation `(-a) mod p` for canonical `a < p`. -/
@[circuit_inline]
def negMod (p a : Nat) : Nat :=
  if a == 0 then 0 else p - a

/-- Field multiplication `(a * b) mod p`.
Dedicated `@[circuit_noinline]` chip isolating `mul_56` + `divmod_56` cost
(the exact operations eliminated by `Rep.field` in Phase 3.4). -/
@[circuit_noinline]
def mulMod (p a b : Nat) : Nat :=
  (a * b) % p

/-- Repeated squaring `value^(2^log) mod p` (`KzgAlgebra::exp_power2`). -/
@[circuit_noinline]
def expPower2 (p value : Nat) : Nat → Nat
  | 0 => value
  | log + 1 => expPower2 p (mulMod p value value) log
termination_by structural log => log

/-- Primitive `2^log`-th root of unity from a `2^maxLog`-th generator
(`KzgAlgebra::two_adic_gen`, rewritten as countdown `expPower2` so
`Depth.Structural` assigns 0 depth columns). -/
@[circuit_inline]
def twoAdicGen (p genMax maxLog log : Nat) : Nat :=
  expPower2 p genMax (maxLog - log)

/-- Domain size `2^log mod p` (`KzgShape::power2`). -/
@[circuit_noinline]
def power2Mod (p : Nat) : Nat → Nat
  | 0 => 1
  | log + 1 =>
    let half := power2Mod p log
    addMod p half half
termination_by structural log => log

/-- Pure-Lean structural binary exponentiation `acc * base^exp mod p`
(used by `invMod` and multi-prime `#guard` checks across BN254 & BLS12-381). -/
def powModFuel (p : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel + 1, base, exp, acc =>
    match exp with
    | 0 => acc
    | _ =>
      let nextAcc := if exp % 2 == 1 then mulMod p acc base else acc
      powModFuel p fuel (mulMod p base base) (exp / 2) nextAcc
termination_by structural fuel => fuel

/-- Fermat modular inverse `a^(p - 2) mod p` for any prime `p < 2^256`. -/
def invMod (p a : Nat) : Nat :=
  powModFuel p 256 (a % p) (p - 2) 1

/-! ## Monomorphic List Indexing & Length Helpers (`Lists::*`) -/

/-- Index lookup in `FList` (`Lists::lookup` for `Values`). -/
@[circuit_noinline]
def fListGet (xs : FList) (idx : Nat) : Nat :=
  match xs with
  | .nil => 0
  | .cons v rest =>
    match idx with
    | 0 => v
    | k + 1 => fListGet rest k
termination_by structural xs

/-- Index lookup in `NodeList` (`Lists::lookup` for `Nodes`). -/
@[circuit_noinline]
def nodeListGet (nodes : NodeList) (idx : Nat) : Node :=
  match nodes with
  | .nil => .const 0
  | .cons n rest =>
    match idx with
    | 0 => n
    | k + 1 => nodeListGet rest k
termination_by structural nodes

/-- Length of a `LookupList` (`Lists::length`). -/
@[circuit_noinline]
def lookupLength : LookupList → Nat
  | .nil => 0
  | .cons _ rest => lookupLength rest + 1
termination_by structural xs => xs

/-- Empty test on `LookupList` returning `1` iff empty (`Lists::is_empty`). -/
@[circuit_inline]
def isEmptyLookups (xs : LookupList) : Nat :=
  match xs with
  | .nil => 1
  | .cons _ _ => 0

/-! ## Core `KzgAlgebra` Functions (`MultiStark/BN/KzgAlgebra.lean`) -/

/-- Right-to-left Horner fingerprint `v0 + gamma * (v1 + ...)` (`KzgAlgebra::fingerprint`). -/
@[circuit_noinline]
def fingerprint (p : Nat) (values : FList) (gamma : Nat) : Nat :=
  match values with
  | .nil => 0
  | .cons v rest => addMod p v (mulMod p gamma (fingerprint p rest gamma))
termination_by structural values

/-- Right-to-left Horner polynomial evaluation `c0 + point * (c1 + ...)` (`KzgAlgebra::polynomial`). -/
@[circuit_noinline]
def polynomial (p : Nat) (values : FList) (point : Nat) : Nat :=
  match values with
  | .nil => 0
  | .cons v rest => addMod p v (mulMod p point (polynomial p rest point))
termination_by structural values

/-- LogUp claims accumulator `∑ 1 / (beta + fingerprint(claim, gamma))`
(`KzgAlgebra::claims_accumulator`, pure-Lean reference using `invMod`). -/
def claimsAccumulator (p : Nat) (claims : FListList) (beta gamma : Nat) : Nat :=
  match claims with
  | .nil => 0
  | .cons claim rest =>
    let denom := addMod p beta (fingerprint p claim gamma)
    addMod p (invMod p denom) (claimsAccumulator p rest beta gamma)
termination_by structural claims

/-- Select the opened trace row for `Node.var source offset _` (`KzgAlgebra::eval_at`).
Uses `source + source + offset` rather than `2 * source + offset` to avoid `mul_56`. -/
@[circuit_inline]
def selectRow (ctx : Context) (source offset : Nat) : FList :=
  match source + source + offset with
  | 0 => ctx.fixed
  | 1 => ctx.fixedNext
  | 2 => ctx.main
  | 3 => ctx.mainNext
  | 4 => ctx.stage2
  | _ => ctx.stage2Next

/-- Select one of the 4 public inputs (`KzgAlgebra::eval_at` `Node::Public`). -/
@[circuit_inline]
def pubAt (ctx : Context) (index : Nat) : Nat :=
  match index with
  | 0 => ctx.pub0
  | 1 => ctx.pub1
  | 2 => ctx.pub2
  | _ => ctx.pub3

/-- Bounded-depth AIR DAG evaluator (`KzgAlgebra::eval_at`).
Counts down `fuel : Nat` structurally so `Depth.Structural` assigns 0 depth columns. -/
@[circuit_noinline]
def evalAt (p : Nat) (nodes : NodeList) (ctx : Context) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, idx =>
    match nodeListGet nodes idx with
    | .const v => v
    | .var source offset column =>
      fListGet (selectRow ctx source offset) column
    | .pub i => pubAt ctx i
    | .first => ctx.first
    | .last => ctx.last
    | .transition => ctx.transition
    | .add a b => addMod p (evalAt p nodes ctx fuel a) (evalAt p nodes ctx fuel b)
    | .sub a b => subMod p (evalAt p nodes ctx fuel a) (evalAt p nodes ctx fuel b)
    | .mul a b => mulMod p (evalAt p nodes ctx fuel a) (evalAt p nodes ctx fuel b)
    | .neg a => negMod p (evalAt p nodes ctx fuel a)
termination_by structural fuel => fuel

/-- Left-to-right Horner folding of evaluated AIR constraint roots (`KzgAlgebra::fold_roots`). -/
@[circuit_noinline]
def foldRoots (p : Nat) (roots : FList) (nodes : NodeList) (ctx : Context)
    (maxDepth alpha acc : Nat) : Nat :=
  match roots with
  | .nil => acc
  | .cons root rest =>
    let e := evalAt p nodes ctx maxDepth root
    let nextAcc := addMod p (mulMod p acc alpha) e
    foldRoots p rest nodes ctx maxDepth alpha nextAcc
termination_by structural roots

/-- Right-to-left Horner fingerprint over DAG-evaluated lookup arguments
(`KzgAlgebra::lookup_fingerprint`). -/
@[circuit_noinline]
def lookupFingerprint (p : Nat) (args : FList) (nodes : NodeList) (ctx : Context)
    (maxDepth gamma : Nat) : Nat :=
  match args with
  | .nil => 0
  | .cons arg rest =>
    let e := evalAt p nodes ctx maxDepth arg
    let tailFp := lookupFingerprint p rest nodes ctx maxDepth gamma
    addMod p e (mulMod p gamma tailFp)
termination_by structural args

/-- Accumulate up to `remaining` lookups into a grouped rational sum
`numerator / product = ∑ m_i / (beta + lookupFingerprint(args_i, gamma))`
(`KzgAlgebra::group_summary`). -/
@[circuit_noinline]
def groupSummary (p : Nat) (lookups : LookupList) (remaining : Nat)
    (nodes : NodeList) (ctx : Context) (maxDepth beta gamma product numerator : Nat) :
    GroupSummaryResult :=
  match remaining with
  | 0 => { product := product, numerator := numerator, rest := lookups }
  | rem + 1 =>
    match lookups with
    | .nil => { product := product, numerator := numerator, rest := .nil }
    | .cons lk rest =>
      let fp := lookupFingerprint p lk.args nodes ctx maxDepth gamma
      let message := addMod p beta fp
      let multVal := evalAt p nodes ctx maxDepth lk.multiplicity
      let nextProd := mulMod p product message
      let nextNum := addMod p (mulMod p numerator message) (mulMod p multVal product)
      groupSummary p rest rem nodes ctx maxDepth beta gamma nextProd nextNum
termination_by structural remaining

/-- Countdown-fuelled worker for grouped logUp constraint folding (`KzgAlgebra::fold_lookups`). -/
@[circuit_noinline]
def foldLookupsFuel (p : Nat) (fuel : Nat) (lookups : LookupList) (size index : Nat)
    (nodes : NodeList) (ctx : Context) (maxDepth beta gamma alpha : Nat)
    (current next : FList) (injection acc : Nat) : Nat :=
  match fuel with
  | 0 => acc
  | fuel' + 1 =>
    match lookups with
    | .nil =>
      let diff := subMod p (fListGet next 0) (fListGet current 0)
      let term := addMod p diff injection
      addMod p (mulMod p acc alpha) term
    | .cons _ _ =>
      let gs := groupSummary p lookups size nodes ctx maxDepth beta gamma 1 0
      let curIdx := fListGet current index
      match gs.rest with
      | .nil =>
        let target := addMod p (fListGet next 0) injection
        let delta := subMod p target curIdx
        let value := subMod p (mulMod p gs.product delta) gs.numerator
        addMod p (mulMod p acc alpha) value
      | rest =>
        let target := fListGet current (index + 1)
        let delta := subMod p target curIdx
        let value := subMod p (mulMod p gs.product delta) gs.numerator
        let nextAcc := addMod p (mulMod p acc alpha) value
        foldLookupsFuel p fuel' rest size (index + 1) nodes ctx maxDepth
          beta gamma alpha current next injection nextAcc
termination_by structural fuel

/-- Grouped logUp constraint folder (`KzgAlgebra::fold_lookups`).
Passes `lookupLength lookups + 1` as structural fuel, which always suffices
for both empty (`nil`) and any `size ≥ 1` non-empty lookup list. -/
@[circuit_inline]
def foldLookups (p : Nat) (lookups : LookupList) (size index : Nat)
    (nodes : NodeList) (ctx : Context) (maxDepth beta gamma alpha : Nat)
    (current next : FList) (injection acc : Nat) : Nat :=
  foldLookupsFuel p (lookupLength lookups + 1) lookups size index nodes ctx
    maxDepth beta gamma alpha current next injection acc

/-- Single-frame KZG algebraic quotient verifier (`KzgAlgebra::verify_frames` loop body).
Verifies:
1. `vanishing = zeta^(2^log) - 1 ≠ 0` (challenge off trace domain)
2. `g * invG == 1` where `g = twoAdicGen(log)`
3. `first * (zeta - 1) == vanishing`
4. `last * (zeta - invG) == vanishing`
5. `injection * (2^log * g) == last * (nextAcc - acc)`
6. `folded == vanishing * polynomial(quotientOpen, zeta^(2^log)) (mod p)`
where `folded` combines `foldRoots` and `foldLookups`. Returns `1` iff valid, else `0`. -/
@[circuit_noinline]
def verifyFrameQuotient (p : Nat) (f : FrameInput) : Nat :=
  let zN := expPower2 p f.zeta f.log
  let vanishing := subMod p zN 1
  if vanishing == 0 then 0
  else
    let g := twoAdicGen p f.genMax f.maxLog f.log
    if mulMod p g f.invG == 1 then
      let transition := subMod p f.zeta f.invG
      if mulMod p f.first (subMod p f.zeta 1) == vanishing then
        if mulMod p f.last transition == vanishing then
          let domSize := power2Mod p f.log
          let injLhs := mulMod p f.injection (mulMod p domSize g)
          let injRhs := mulMod p f.last (subMod p f.nextAcc f.acc)
          if injLhs == injRhs then
            let ctx : Context :=
              { main := f.main, mainNext := f.mainNext
                fixed := f.fixed, fixedNext := f.fixedNext
                stage2 := f.stage2, stage2Next := f.stage2Next
                pub0 := f.beta, pub1 := f.gamma
                pub2 := f.acc, pub3 := f.nextAcc
                first := f.first, last := f.last, transition := transition }
            let folded0 := foldRoots p f.roots f.nodes ctx f.maxDepth f.alpha 0
            let folded := foldLookups p f.lookups f.groupSize 0 f.nodes ctx
              f.maxDepth f.beta f.gamma f.alpha f.stage2 f.stage2Next f.injection folded0
            let quotient := polynomial p f.quotientOpen zN
            if folded == mulMod p vanishing quotient then 1 else 0
          else 0
        else 0
      else 0
    else 0

/-- Pure-Lean direct frame verifier computing `invG`, `first`, `last`, and
`injection` via `invMod` before delegating to `verifyFrameQuotient`
(used for multi-prime `#guard` checks including BN254 `Fr` and BLS12-381 `Fr`). -/
def verifyFrameDirect (p : Nat) (nodes : NodeList) (roots : FList) (lookups : LookupList)
    (groupSize maxDepth log genMax maxLog : Nat)
    (main mainNext fixed fixedNext stage2 stage2Next quotientOpen : FList)
    (beta gamma alpha zeta acc nextAcc : Nat) : Nat :=
  let zN := expPower2 p zeta log
  let vanishing := subMod p zN 1
  if vanishing == 0 then 0
  else
    let g := twoAdicGen p genMax maxLog log
    let invG := invMod p g
    let transition := subMod p zeta invG
    let first := mulMod p vanishing (invMod p (subMod p zeta 1))
    let last := mulMod p vanishing (invMod p transition)
    let domSize := power2Mod p log
    let injection := mulMod p (mulMod p last (subMod p nextAcc acc))
      (invMod p (mulMod p domSize g))
    verifyFrameQuotient p
      { nodes, roots, lookups, groupSize, maxDepth, log, genMax, maxLog
        invG, first, last, injection
        main, mainNext, fixed, fixedNext, stage2, stage2Next, quotientOpen
        beta, gamma, alpha, zeta, acc, nextAcc }

/-! ## Canonical Benchmark AIR Circuit (`p = 65537`, `log = 2`, 27-node DAG, 3 Lookups)

* `p = 65537 = 2^16 + 1`: Fermat prime with `(p - 1)^2 = 2^32 < 2^56`, fitting
  `mul_56` / `divmod_56` cleanly under `TableTier.byte256` (256-row byte table).
* `sampleAirNodes` exercises all 10 `Node` constructors (`const`, `var` across all
  6 trace rows `fixed`/`fixedNext`/`main`/`mainNext`/`stage2`/`stage2Next`,
  `pub` across all 4 indices `0..3`, `first`, `last`, `transition`, `add`, `sub`,
  `mul`, `neg`) with topological depth 5 (`maxDepth = 5`).
* `sampleLookups` has 3 lookups with `groupSize = 2`, exercising both a full
  2-lookup intermediate group (`isLast = 0`, targeting `current[1]`) and a partial
  1-lookup terminal group (`isLast = 1`, targeting `next[0] + injection`).
-/

/-- Small 2-adic prime `F_4 = 2^16 + 1 = 65537` (`(p - 1)^2 = 2^32 < 2^56`). -/
@[circuit_inline]
def testPrime : Nat := 65537

/-- Unified 27-node AIR constraint DAG (depth 5, all 10 `Node` constructors live). -/
@[circuit_noinline]
def sampleAirNodes : NodeList :=
  .cons (.var 1 0 0)        -- 0:  main[0]
  (.cons (.var 1 1 0)       -- 1:  mainNext[0]
  (.cons (.var 0 0 0)       -- 2:  fixed[0]
  (.cons (.var 0 1 0)       -- 3:  fixedNext[0]
  (.cons (.var 2 0 0)       -- 4:  stage2[0]
  (.cons (.var 2 1 0)       -- 5:  stage2Next[0]
  (.cons (.const 1)         -- 6:  Const(1)
  (.cons (.pub 0)           -- 7:  beta
  (.cons (.pub 1)           -- 8:  gamma
  (.cons (.pub 2)           -- 9:  acc
  (.cons (.pub 3)           -- 10: nextAcc
  (.cons .first             -- 11: First
  (.cons .last              -- 12: Last
  (.cons .transition        -- 13: Transition
  (.cons (.add 0 2)         -- 14: main[0] + fixed[0]
  (.cons (.sub 1 14)        -- 15: mainNext[0] - (main[0] + fixed[0])
  (.cons (.mul 13 15)       -- 16: transition * (mainNext[0] - (main[0] + fixed[0])) [root 0]
  (.cons (.neg 6)           -- 17: -1
  (.cons (.add 0 17)        -- 18: main[0] + (-1)
  (.cons (.mul 11 18)       -- 19: first * (main[0] - 1) [root 1]
  (.cons (.sub 4 7)         -- 20: stage2[0] - pub0
  (.cons (.add 5 8)         -- 21: stage2Next[0] + pub1
  (.cons (.sub 20 3)        -- 22: (stage2[0] - pub0) - fixedNext[0]
  (.cons (.add 9 10)        -- 23: pub2 + pub3
  (.cons (.sub 21 23)       -- 24: (stage2Next[0] + pub1) - (pub2 + pub3)
  (.cons (.add 22 24)       -- 25: ((stage2[0] - pub0) - fixedNext[0]) + ((stage2Next[0] + pub1) - (pub2 + pub3))
  (.cons (.mul 12 25)       -- 26: last * (...) [root 2]
  .nil))))))))))))))))))))))))))

/-- Three AIR constraint root indices into `sampleAirNodes`. -/
@[circuit_inline]
def sampleAirRoots : FList :=
  .cons 16 (.cons 19 (.cons 26 .nil))

/-- Three logUp lookups (`groupSize = 2` splits into 2 groups: `[0, 1]` and `[2]`). -/
@[circuit_noinline]
def sampleLookups : LookupList :=
  .cons { multiplicity := 6, args := .cons 0 (.cons 2 .nil) }
  (.cons { multiplicity := 17, args := .cons 1 (.cons 3 .nil) }
  (.cons { multiplicity := 6, args := .cons 14 .nil }
  .nil))

/-- **Entrypoint 1 (`entryEvalFold`)**: exercises `expPower2`, `evalAt` across
all 10 `Node` constructors (6 row selectors + 4 public inputs), `foldRoots`,
and `polynomial` Horner evaluation over `p = 65537`. Returns `1` iff all
inputs are canonical (`< 65537`), `zeta` lies off the `N = 4` trace domain,
Lagrange selectors satisfy their defining equations, and
`folded == vanishing * polynomial([q0, q1], zeta^4) (mod 65537)`.

Valid witness: `(7, 11, 14206, 17) → 1`. -/
@[circuit_budget 15 128 24 48 400]
def entryEvalFold (zeta main0 q0 q1 : Nat) : Nat :=
  let p := testPrime
  if zeta < p then
    if main0 < p then
      if q0 < p then
        if q1 < p then
          let zN := expPower2 p zeta 2
          let vanishing := subMod p zN 1
          if vanishing == 0 then 0
          else
            let invG := 65281
            let transition := subMod p zeta invG
            let first := 400
            let last := 53585
            if mulMod p first (subMod p zeta 1) == vanishing then
              if mulMod p last transition == vanishing then
                let ctx : Context :=
                  { main := .cons main0 (.cons 23 .nil)
                    mainNext := .cons 29 (.cons 31 .nil)
                    fixed := .cons 13 (.cons 17 .nil)
                    fixedNext := .cons 19 (.cons 21 .nil)
                    stage2 := .cons 42 (.cons 55 .nil)
                    stage2Next := .cons 61 (.cons 73 .nil)
                    pub0 := 3, pub1 := 5, pub2 := 10, pub3 := 20
                    first := first, last := last, transition := transition }
                let folded := foldRoots p sampleAirRoots sampleAirNodes ctx 5 13 0
                let quotient := polynomial p (.cons q0 (.cons q1 .nil)) zN
                if folded == mulMod p vanishing quotient then 1 else 0
              else 0
            else 0
        else 0
      else 0
    else 0
  else 0

/-- **Entrypoint 2 (`entryFullFrame`)**: exercises the full `KzgAlgebra` frame
verification pipeline (`verifyFrameQuotient`: `expPower2` + `twoAdicGen` +
`power2Mod` + `evalAt` + `foldRoots` + `lookupFingerprint` + multi-group
`groupSummary` + `foldLookups` + `polynomial` + vanishing/selector/injection/
quotient equality checks) over `p = 65537`.

Valid witness: `(7, 11, 42, 11215) → 1`. -/
@[circuit_budget 24 160 36 56 760]
def entryFullFrame (zeta main0 stage2_0 q0 : Nat) : Nat :=
  let p := testPrime
  if zeta < p then
    if main0 < p then
      if stage2_0 < p then
        if q0 < p then
          verifyFrameQuotient p
            { nodes := sampleAirNodes
              roots := sampleAirRoots
              lookups := sampleLookups
              groupSize := 2
              maxDepth := 5
              log := 2
              genMax := 4
              maxLog := 4
              invG := 65281
              first := 400
              last := 53585
              injection := 46988
              main := .cons main0 (.cons 23 .nil)
              mainNext := .cons 29 (.cons 31 .nil)
              fixed := .cons 13 (.cons 17 .nil)
              fixedNext := .cons 19 (.cons 21 .nil)
              stage2 := .cons stage2_0 (.cons 55 .nil)
              stage2Next := .cons 61 (.cons 73 .nil)
              quotientOpen := .cons q0 (.cons 17 .nil)
              beta := 3
              gamma := 5
              alpha := 13
              zeta := zeta
              acc := 10
              nextAcc := 20 }
        else 0
      else 0
    else 0
  else 0

/-! ## Pure Lean Self-Checks (`#guard`): Small Prime, 28-bit Prime, BN254 `Fr`, BLS12-381 `Fr` -/

-- 1. Entrypoint 1 (`entryEvalFold`): valid witness returns 1; tampered challenge,
--    on-domain challenge, tampered opening, tampered quotient, or non-canonical >= p returns 0.
#guard entryEvalFold 7 11 14206 17 == 1
#guard entryEvalFold 8 11 14206 17 == 0
#guard entryEvalFold 1 11 14206 17 == 0
#guard entryEvalFold 256 11 14206 17 == 0
#guard entryEvalFold 7 12 14206 17 == 0
#guard entryEvalFold 7 11 14207 17 == 0
#guard entryEvalFold 7 11 14206 18 == 0
#guard entryEvalFold 7 11 (14206 + 65537) 17 == 0

-- 2. Entrypoint 2 (`entryFullFrame`): valid frame returns 1; tampered challenge,
--    on-domain challenge, tampered main opening, tampered stage2 running sum,
--    tampered quotient, or non-canonical >= p returns 0.
#guard entryFullFrame 7 11 42 11215 == 1
#guard entryFullFrame 8 11 42 11215 == 0
#guard entryFullFrame 1 11 42 11215 == 0
#guard entryFullFrame 256 11 42 11215 == 0
#guard entryFullFrame 7 12 42 11215 == 0
#guard entryFullFrame 7 11 43 11215 == 0
#guard entryFullFrame 7 11 42 11216 == 0
#guard entryFullFrame 7 11 42 (11215 + 65537) == 0

-- 3. Empty-lookup branch of `foldLookups` (`lookups = .nil`) over `p = 65537`.
#guard verifyFrameDirect 65537 sampleAirNodes sampleAirRoots .nil 2 5 2 4 4
  (.cons 11 (.cons 23 .nil)) (.cons 29 (.cons 31 .nil))
  (.cons 13 (.cons 17 .nil)) (.cons 19 (.cons 21 .nil))
  (.cons 42 (.cons 55 .nil)) (.cons 61 (.cons 73 .nil))
  (.cons 24149 .nil) 3 5 13 7 10 20 == 1
#guard verifyFrameDirect 65537 sampleAirNodes sampleAirRoots .nil 2 5 2 4 4
  (.cons 11 (.cons 23 .nil)) (.cons 29 (.cons 31 .nil))
  (.cons 13 (.cons 17 .nil)) (.cons 19 (.cons 21 .nil))
  (.cons 42 (.cons 55 .nil)) (.cons 61 (.cons 73 .nil))
  (.cons 24150 .nil) 3 5 13 7 10 20 == 0

-- 4. Exact agreement between `fingerprint` and `lookupFingerprint` on evaluated nodes.
#guard
  let ctx : Context :=
    { main := .cons 11 (.cons 23 .nil), mainNext := .cons 29 (.cons 31 .nil)
      fixed := .cons 13 (.cons 17 .nil), fixedNext := .cons 19 (.cons 21 .nil)
      stage2 := .cons 42 (.cons 55 .nil), stage2Next := .cons 61 (.cons 73 .nil)
      pub0 := 3, pub1 := 5, pub2 := 10, pub3 := 20
      first := 400, last := 53585, transition := 263 }
  lookupFingerprint 65537 (.cons 0 (.cons 2 .nil)) sampleAirNodes ctx 5 5 ==
    fingerprint 65537 (.cons 11 (.cons 13 .nil)) 5
#guard isEmptyLookups .nil == 1
#guard isEmptyLookups sampleLookups == 0
#guard lookupLength sampleLookups == 3
#guard polynomial 65537 (.cons 3 (.cons 5 (.cons 7 .nil))) 2 == 3 + 5 * 2 + 7 * 4
#guard addMod 65537 65530 10 == 3
#guard subMod 65537 3 10 == 65530
#guard negMod 65537 0 == 0
#guard negMod 65537 5 == 65532
#guard mulMod 65537 256 65281 == 1

-- 5. 28-bit NTT prime `p = 167772161 = 5 * 2^25 + 1` (`(p - 1)^2 < 2^56`, 25-adic).
private def p28 : Nat := 167772161
private def p28Gen25 : Nat := 243

#guard expPower2 p28 p28Gen25 25 == 1
#guard expPower2 p28 p28Gen25 24 == p28 - 1
#guard verifyFrameDirect p28 sampleAirNodes sampleAirRoots sampleLookups 2 5 3 p28Gen25 25
  (.cons 11 (.cons 23 .nil)) (.cons 29 (.cons 31 .nil))
  (.cons 13 (.cons 17 .nil)) (.cons 19 (.cons 21 .nil))
  (.cons 42 (.cons 55 .nil)) (.cons 61 (.cons 73 .nil))
  (.cons 62671760 (.cons 42 .nil)) 111 222 333 123456789 77 99 == 1
#guard verifyFrameDirect p28 sampleAirNodes sampleAirRoots sampleLookups 2 5 3 p28Gen25 25
  (.cons 11 (.cons 23 .nil)) (.cons 29 (.cons 31 .nil))
  (.cons 13 (.cons 17 .nil)) (.cons 19 (.cons 21 .nil))
  (.cons 42 (.cons 55 .nil)) (.cons 61 (.cons 73 .nil))
  (.cons 62671761 (.cons 42 .nil)) 111 222 333 123456789 77 99 == 0
#guard claimsAccumulator p28
  (.cons (.cons 11 (.cons 13 .nil)) (.cons (.cons 29 (.cons 19 .nil)) .nil)) 111 222 == 78889518

-- 6. Real BN254 scalar field `Fr` with exact `two_adic_gen(28)` from `MultiStark/BN/KzgAlgebra.lean`!
private def bn254Fr : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

private def bn254TwoAdicGen28 : Nat :=
  19103219067921713944291392827692070036145651957329286315305642004821462161904

#guard twoAdicGen bn254Fr bn254TwoAdicGen28 28 0 == 1
#guard twoAdicGen bn254Fr bn254TwoAdicGen28 28 1 == bn254Fr - 1
#guard verifyFrameDirect bn254Fr sampleAirNodes sampleAirRoots sampleLookups 2 5 3 bn254TwoAdicGen28 28
  (.cons 11 (.cons 23 .nil)) (.cons 29 (.cons 31 .nil))
  (.cons 13 (.cons 17 .nil)) (.cons 19 (.cons 21 .nil))
  (.cons 42 (.cons 55 .nil)) (.cons 61 (.cons 73 .nil))
  (.cons 19178980027282371858735728425478441444252595536923897929835332410646997469797 (.cons 42 .nil))
  111 222 333 123456789 77 99 == 1
#guard verifyFrameDirect bn254Fr sampleAirNodes sampleAirRoots sampleLookups 2 5 3 bn254TwoAdicGen28 28
  (.cons 11 (.cons 23 .nil)) (.cons 29 (.cons 31 .nil))
  (.cons 13 (.cons 17 .nil)) (.cons 19 (.cons 21 .nil))
  (.cons 42 (.cons 55 .nil)) (.cons 61 (.cons 73 .nil))
  (.cons 19178980027282371858735728425478441444252595536923897929835332410646997469798 (.cons 42 .nil))
  111 222 333 123456789 77 99 == 0
#guard claimsAccumulator bn254Fr
  (.cons (.cons 11 (.cons 13 .nil)) (.cons (.cons 29 (.cons 19 .nil)) .nil)) 111 222 ==
  11581653804616111110795461136109183399335258384890232915413316423843931226819

-- 7. Real BLS12-381 scalar field `Fr` with exact 32-adic generator `7^((r - 1) / 2^32) mod r`!
private def bls12381Fr : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

private def bls12381TwoAdicGen32 : Nat :=
  10238227357739495823651030575849232062558860180284477541189508159991286009131

#guard twoAdicGen bls12381Fr bls12381TwoAdicGen32 32 0 == 1
#guard twoAdicGen bls12381Fr bls12381TwoAdicGen32 32 1 == bls12381Fr - 1
#guard verifyFrameDirect bls12381Fr sampleAirNodes sampleAirRoots sampleLookups 2 5 3 bls12381TwoAdicGen32 32
  (.cons 11 (.cons 23 .nil)) (.cons 29 (.cons 31 .nil))
  (.cons 13 (.cons 17 .nil)) (.cons 19 (.cons 21 .nil))
  (.cons 42 (.cons 55 .nil)) (.cons 61 (.cons 73 .nil))
  (.cons 48830519577227491529239292953252347222655331472926284386474825284086568434183 (.cons 42 .nil))
  111 222 333 123456789 77 99 == 1
#guard verifyFrameDirect bls12381Fr sampleAirNodes sampleAirRoots sampleLookups 2 5 3 bls12381TwoAdicGen32 32
  (.cons 11 (.cons 23 .nil)) (.cons 29 (.cons 31 .nil))
  (.cons 13 (.cons 17 .nil)) (.cons 19 (.cons 21 .nil))
  (.cons 42 (.cons 55 .nil)) (.cons 61 (.cons 73 .nil))
  (.cons 48830519577227491529239292953252347222655331472926284386474825284086568434184 (.cons 42 .nil))
  111 222 333 123456789 77 99 == 0
#guard claimsAccumulator bls12381Fr
  (.cons (.cons 11 (.cons 13 .nil)) (.cons (.cons 29 (.cons 19 .nil)) .nil)) 111 222 ==
  38908447036158770819810509373375310631497472675848750207504765988776630613722

end KzgAlgebraPure
