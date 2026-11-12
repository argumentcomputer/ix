import IxCCTests.IxonV3.Builder

/-! The resource checker's step budget bounds its work: the regression for
an exponential validator, with the same generated constants as ix's
`Tests/Ix/ResourceBudget.lean`. Each constant is framed as a one-constant `.ixe`
file and read through the byte boundary `check-ixon-v3` uses. The suite asserts
the outcome and the steps the definition consumed; printed times are for
reading only.

- `letChain k`: reducing its declared type builds a value of about
  `2^k` nodes, and every node visited costs a step, so from `k = 16` the
  definition runs out of its 100,000 steps.
- `sharingChain k` (`A`): an ill-typed sharing chain
  `s_j = s_{j-1} s_{j-1}`; substitution keeps `s_k` as one `.share` node and
  the mismatch is found in steps linear in `k`.
- `reducingChain k`: a well-typed chain
  `s_j = (fun (_ _ : Type 1) => Type) s_{j-1} s_{j-1}`, accepted in a few steps.
- `canonicalLetChain k`: `letChain` with its arrow in a sharing table. -/

namespace IxCCTests.IxonV3.ResourceBudget

open IxCC.Ixon IxCC.Ixon.V3 Builder

def linear : BinderContract := ⟨.linear, .shared⟩
def many : BinderContract := {}

def doublingTable (k : Nat) : Array E := Id.run do
  let mut table : Array E := #[.sort 0]
  for j in [1:k+1] do
    table := table.push (.app (.share (j - 1).toUInt64) (.share (j - 1).toUInt64))
  return table

/-- `(fun (x : linear) => (fun (y : linear) => y) x) s` over the domain `domain`. -/
def doubleBeta (domain s : E) : E :=
  .app (.lam linear domain (.app (.lam linear domain (.var 0)) (.var 0))) s

def sharingChain (k : Nat) : C :=
  ⟨.defn ⟨.defn, .safe, 0, doubleBeta (.sort 0) (.share k.toUInt64), .sort 0⟩,
    doublingTable k, #[], #[.zero]⟩

def reducingTable (k : Nat) : Array E := Id.run do
  let constant : E := .lam many (.sort 2) (.lam many (.sort 2) (.sort 1))
  let mut table : Array E := #[.sort 1]
  for j in [1:k+1] do
    table := table.push
      (.app (.app constant (.share (j - 1).toUInt64)) (.share (j - 1).toUInt64))
  return table

def reducingChain (k : Nat) : C :=
  ⟨.defn ⟨.defn, .safe, 0, doubleBeta (.sort 2) (.share k.toUInt64), .sort 0⟩,
    reducingTable k, #[], #[.zero, .succ .zero, .succ (.succ .zero)]⟩

def letType (k : Nat) (arrow : E) : E := Id.run do
  let mut body : E := .sort 1
  for _ in [0:k] do
    body := .letE { nonDep := false } (.sort 1) arrow body
  return .letE { nonDep := false, binder := linear } (.sort 1) (.sort 0) body

def letChain (k : Nat) : C :=
  ⟨.defn ⟨.defn, .safe, 0, letType k (.all many {} (.var 0) (.var 1)), .sort 0⟩,
    #[], #[], #[.zero, .succ .zero]⟩

def canonicalLetChain (k : Nat) : C :=
  ⟨.defn ⟨.defn, .safe, 0, letType k (.share 0), .sort 0⟩,
    #[.all many {} (.var 0) (.var 1)], #[], #[.zero, .succ .zero]⟩

inductive Expect where
  | accept (steps : Nat)
  | reject (error : Resource.Error) (steps : Nat)
  | budget

structure Case where
  label : String
  constant : C
  expect : Expect
  steps : Nat := 100000
  /-- Also time the combined `validate` (only where resources refuse first). -/
  validate : Bool := false

/-- The sizes timed first, then larger ones (minutes to hours each before
the fix). `k ≤ 14` let chains are accepted, as at the merge base. -/
def cases : Array Case := Id.run do
  let mut cases : Array Case := #[]
  let mismatch := Expect.reject .typeMismatch 2000
  for k in [12, 14] do
    cases := cases.push ⟨s!"let chain k={k}", letChain k, .accept 100000, 100000, false⟩
  for k in [16, 20, 24, 26, 28, 30] do
    cases := cases.push ⟨s!"let chain k={k}", letChain k, .budget, 100000, true⟩
  cases := cases.push ⟨"let chain k=30 steps=1000", letChain 30, .budget, 1000, false⟩
  cases := cases.push ⟨"canonical let chain k=28", canonicalLetChain 28, .budget, 100000, false⟩
  for k in [20, 24, 28] do
    cases := cases.push ⟨s!"sharing chain k={k}", sharingChain k, mismatch, 100000, true⟩
  cases := cases.push ⟨"reducing chain k=24", reducingChain 24, .accept 2000, 100000, false⟩
  cases := cases.push ⟨"let chain k=40", letChain 40, .budget, 100000, true⟩
  cases := cases.push ⟨"canonical let chain k=40", canonicalLetChain 40, .budget, 100000, false⟩
  for k in [30, 40, 60] do
    cases := cases.push ⟨s!"sharing chain k={k}", sharingChain k, mismatch, 100000, true⟩
  for k in [40, 60] do
    cases := cases.push ⟨s!"reducing chain k={k}", reducingChain k, .accept 2000, 100000, false⟩
  return cases

def runCase (c : Case) : IO Bool := do
  let raw := bytes (store {} c.constant).1
  let profile : Resource.Profile := { limits := { depth := 256, steps := c.steps } }
  let t0 ← IO.monoMsNow
  let env ← IO.ofExcept (decodeAnonymousEnv raw)
  let resolved ← IO.ofExcept (Resource.Addressed.prepare env profile)
  -- One constant, the definition: declaration 0.
  let (result, used) ← IO.lazyPure fun _ =>
    Resource.checkDefinitionCounted resolved.program 0 profile.limits
  let admitted ← IO.lazyPure fun _ => admitResources raw profile.bytes
  let t1 ← IO.monoMsNow
  let admittedBudget := match admitted with
    | .error message => (message.splitOn "budget").length > 1
    | .ok _ => false
  let mut ok := match c.expect, result with
    | .accept bound, .ok () => used ≤ bound && admitted.toOption.isSome
    | .reject expected bound, .error e =>
      e == expected && used ≤ bound && admitted.toOption.isNone && !admittedBudget
    | .budget, .error .budget => used == c.steps && admittedBudget
    | _, _ => false
  let outcome := match result with
    | .ok () => "accepted"
    | .error e => s!"refused {(repr e).pretty}"
  IO.println s!"  {c.label}: {outcome} after {used} of {c.steps} steps, {t1 - t0} ms{if ok then "" else "  (unexpected)"}"
  if c.validate then
    let t2 ← IO.monoMsNow
    let combined ← IO.lazyPure fun _ => validate raw profile.bytes
    let t3 ← IO.monoMsNow
    let refused := combined.toOption.isNone
    IO.println s!"    validate: {if refused then "refused" else "accepted"} in {t3 - t2} ms"
    ok := ok && refused
  (← IO.getStdout).flush
  return ok

def run : IO Nat := do
  IO.println "ixon-v3 resource budget: generated constants under the default profile"
  let mut failed : Array String := #[]
  for c in cases do
    unless ← runCase c do failed := failed.push c.label
  unless failed.isEmpty do
    throw (IO.userError s!"resource budget: unexpected outcome for {failed}")
  return cases.size

end IxCCTests.IxonV3.ResourceBudget
