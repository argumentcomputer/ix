module

public import Ix.Resource.Validate

/-!
# The resource checker's step budget bounds its work

Regression for the exponential checks of review findings B4-1 and R3: constants
of a few hundred bytes whose resource analysis took time exponential in their
size, outside the step budget. Each constant is serialized as a one-constant
environment and read back with ix's own reader, as a supplied file would be,
then checked under the standard profile. The suite asserts the outcome and the
number of steps the definition consumed; the times it prints are for reading,
not asserted.

- `letChain k` (R3's `L`): no sharing table. Its declared type is
  `let a0 : Type := Prop; let a1 : Type := a0 → a0; …; let ak := a(k-1) → a(k-1); Type`
  with a linear first binder. Reducing it builds `a k`, whose tree has about
  `2^k` nodes; every node visited costs a step, so from `k = 16` the definition
  runs out of its 100,000 steps, as at the merge base `3d725c8c0`.
- `sharingChain k` (B4's and R3's `A`): `s_0 = Sort 0`, `s_j = s_{j-1} s_{j-1}`,
  declared type `(fun (x : linear) => (fun (y : linear) => y) x) s_k`. It is
  ill typed. Substitution keeps `s_k` as one `.share` node, so the mismatch is
  found in steps linear in `k`.
- `reducingChain k`: a well-typed chain
  `s_j = (fun (_ _ : Type 1) => Type) s_{j-1} s_{j-1}` in the same position. Its
  declared type reduces to `Type` after one expansion, so it is accepted in a
  few steps, whatever `k`. (The merge base expanded `s_k` fully and ran out of
  budget from `k = 16`; the branch tip accepted it after walking `2^k` nodes
  without charging them.)
- `canonicalLetChain k`: `letChain` with its repeated arrow in a sharing table,
  as ix's canonical sharing writes it (R3's `canon` probe).
-/

public section

namespace Tests.ResourceBudget

open Ixon Ix.Resource

def linear : BinderContract := ⟨.linear, .shared⟩
def many : BinderContract := {}

/-- `s_0 = Sort 0`, `s_j = s_{j-1} s_{j-1}`: entry `j` expands to `2^(j+1) - 1` nodes. -/
def doublingTable (k : Nat) : Array Ixon.Expr := Id.run do
  let mut table : Array Ixon.Expr := #[.sort 0]
  for j in [1:k+1] do
    table := table.push (.app (.share (j - 1).toUInt64) (.share (j - 1).toUInt64))
  return table

/-- `(fun (x : linear) => (fun (y : linear) => y) x) s` over the domain `domain`. -/
def doubleBeta (domain s : Ixon.Expr) : Ixon.Expr :=
  .app (.lam linear domain (.app (.lam linear domain (.var 0)) (.var 0))) s

def sharingChain (k : Nat) : Constant := {
  info := .defn ⟨.defn, .safe, 0, doubleBeta (.sort 0) (.share k.toUInt64), .sort 0⟩
  sharing := doublingTable k, refs := #[], univs := #[.zero] }

/-- Universes: `0 = Prop`, `1 = Type`, `2 = Type 1`. `s_0 = Type`,
`s_j = (fun (_ _ : Type 1) => Type) s_{j-1} s_{j-1}`. -/
def reducingTable (k : Nat) : Array Ixon.Expr := Id.run do
  let constant : Ixon.Expr := .lam many (.sort 2) (.lam many (.sort 2) (.sort 1))
  let mut table : Array Ixon.Expr := #[.sort 1]
  for j in [1:k+1] do
    table := table.push
      (.app (.app constant (.share (j - 1).toUInt64)) (.share (j - 1).toUInt64))
  return table

def reducingChain (k : Nat) : Constant := {
  info := .defn ⟨.defn, .safe, 0, doubleBeta (.sort 2) (.share k.toUInt64), .sort 0⟩
  sharing := reducingTable k, refs := #[], univs := #[.zero, .succ .zero, .succ (.succ .zero)] }

/-- `let a0 : Type := Prop; let a(j+1) : Type := aj → aj; …; Type`, the arrow
written as `arrow` (inline, or a `.share` of it). -/
def letType (k : Nat) (arrow : Ixon.Expr) : Ixon.Expr := Id.run do
  let mut body : Ixon.Expr := .sort 1
  for _ in [0:k] do
    body := .letE { nonDep := false } (.sort 1) arrow body
  return .letE { nonDep := false, binder := linear } (.sort 1) (.sort 0) body

def letChain (k : Nat) : Constant := {
  info := .defn ⟨.defn, .safe, 0, letType k (.all many {} (.var 0) (.var 1)), .sort 0⟩
  sharing := #[], refs := #[], univs := #[.zero, .succ .zero] }

def canonicalLetChain (k : Nat) : Constant := {
  info := .defn ⟨.defn, .safe, 0, letType k (.share 0), .sort 0⟩
  sharing := #[.all many {} (.var 0) (.var 1)], refs := #[], univs := #[.zero, .succ .zero] }

/-- A one-constant environment, written with `serEnv` and read back with
ix's `.ixe` reader. -/
def envOf (c : Constant) : Except String Ixon.Env := do
  let address := Address.blake3 (serConstant c)
  let bytes ← Ixon.serEnv (({} : Ixon.Env).storeConst address c)
  let env ← Ixon.deEnv bytes
  let some decoded := env.getConst? address | throw "constant missing after decoding"
  unless serConstant decoded == serConstant c do throw "decoded constant differs"
  return env

inductive Expect where
  /-- Accepted within `steps` steps. -/
  | accept (steps : Nat)
  /-- Refused with `error` within `steps` steps. -/
  | reject (error : Error) (steps : Nat)
  /-- Refused for budget after consuming the whole step limit. -/
  | budget

structure Case where
  label : String
  constant : Constant
  expect : Expect
  steps : Nat := 100000
  /-- Also time the combined `validate`. Only for cases the resource half
  refuses, which `validate` checks before typing. -/
  validate : Bool := false

/-- The sizes R3 timed first, then larger ones (minutes to hours each before
the fix). `k ≤ 14` let chains are accepted, as at the merge base. -/
def cases : Array Case := Id.run do
  let mut cases : Array Case := #[]
  let mismatch := Expect.reject .typeMismatch 2000
  for k in [12, 14] do
    cases := cases.push ⟨s!"let chain k={k}", letChain k, .accept 100000, 100000, false⟩
  for k in [16, 20, 22, 23, 24] do
    cases := cases.push ⟨s!"let chain k={k}", letChain k, .budget, 100000, true⟩
  cases := cases.push ⟨"let chain k=23 steps=1000", letChain 23, .budget, 1000, false⟩
  cases := cases.push ⟨"canonical let chain k=23", canonicalLetChain 23, .budget, 100000, false⟩
  for k in [12, 16, 20, 22, 23, 24] do
    cases := cases.push ⟨s!"sharing chain k={k}", sharingChain k, mismatch, 100000, true⟩
  cases := cases.push
    ⟨"sharing chain k=23 steps=1000", sharingChain 23, .reject .typeMismatch 1000, 1000, false⟩
  cases := cases.push ⟨"reducing chain k=24", reducingChain 24, .accept 2000, 100000, false⟩
  for k in [30, 40] do
    cases := cases.push ⟨s!"let chain k={k}", letChain k, .budget, 100000, true⟩
  cases := cases.push ⟨"canonical let chain k=40", canonicalLetChain 40, .budget, 100000, false⟩
  for k in [28, 40, 60] do
    cases := cases.push ⟨s!"sharing chain k={k}", sharingChain k, mismatch, 100000, true⟩
  for k in [40, 60] do
    cases := cases.push ⟨s!"reducing chain k={k}", reducingChain k, .accept 2000, 100000, false⟩
  return cases

def errorName (e : Error) : String := (repr e).pretty

def runCase (c : Case) : IO Bool := do
  let env ← IO.ofExcept (envOf c.constant)
  let profile := { standardProfile env with limits := { depth := 256, steps := c.steps } }
  let t0 ← IO.monoMsNow
  let resolved ← IO.ofExcept (Addressed.prepare env profile)
  -- The environment holds one constant, the definition, so it is declaration 0.
  let (result, used) ← IO.lazyPure fun _ => checkDefinitionCounted resolved.program 0 profile.limits
  let boundary ← IO.lazyPure fun _ => Addressed.checkResources env profile
  let t1 ← IO.monoMsNow
  let outcome := match result with
    | .ok () => "accepted"
    | .error e => s!"refused {errorName e}"
  let boundaryBudget := match boundary with
    | .error message => (message.splitOn "budget").length > 1
    | .ok _ => false
  let mut ok := match c.expect, result with
    | .accept bound, .ok () => used ≤ bound && boundary.toOption.isSome
    | .reject expected bound, .error e =>
      e == expected && used ≤ bound && boundary.toOption.isNone && !boundaryBudget
    | .budget, .error .budget => used == c.steps && boundaryBudget
    | _, _ => false
  IO.println s!"  {c.label}: {outcome} after {used} of {c.steps} steps, {t1 - t0} ms{if ok then "" else "  FAILED"}"
  if c.validate then
    let t2 ← IO.monoMsNow
    let combined ← IO.lazyPure fun _ => validate env profile
    let t3 ← IO.monoMsNow
    let refused := combined.toOption.isNone
    IO.println s!"    validate: {if refused then "refused" else "ACCEPTED"} in {t3 - t2} ms"
    ok := ok && refused
  (← IO.getStdout).flush
  return ok

def run : IO UInt32 := do
  IO.println "resource-budget: generated constants under the standard profile"
  let mut failed := 0
  for c in cases do
    unless ← runCase c do failed := failed + 1
  if failed == 0 then
    IO.println s!"resource-budget: {cases.size} cases end within their step budget"
    return 0
  IO.eprintln s!"resource-budget: {failed} of {cases.size} cases failed"
  return 1

end Tests.ResourceBudget

end
