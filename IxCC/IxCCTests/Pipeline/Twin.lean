import IxCCTests.Pipeline.Support
import IxCCTests.Support.Rng
import IxCCTests.Fixtures.K1

/-! The compiled K1 roots against their Lean-compiled twin.

`k1.ixe` is compiled with its five roots into one object; each root runs on
generated inputs and must agree with the same definition compiled by Lean
(the test module `IxCCTests/Fixtures/K1.lean`), with the
`2⁶³` boundary of the Phase 1 `Nat` representation:

* an argument of at least `2⁶³` has no word: the entry wrapper returns
  status 3 (`natOverflow`) before the root runs (natively and on the
  machines; Lir never sees it);
* a result of at least `2⁶³` has no word either: status 3
  (`ack 0 (2⁶³ − 1)` is `2⁶³`; `ack 0 (2⁶³ − 2)` is the largest word);
* an intermediate value of at least `2⁶³` may fail the run with status 3
  too, an allowed resource failure (`tak` decides `y < x` as `y + 1 ≤ x`, so
  `y = 2⁶³ − 1` overflows although the result fits); these are counted;
* everything else returns status 0 and the twin's value.

The inputs are drawn per root (small values, values near `2⁶³` where the
root's cost does not grow with them, and the boundary cases), run at Lir
(from `cx_init`'s memory; arguments below `2⁶³`) and, with `--cc`, natively
under the runtime driver, where the status must also be Lir's. -/

namespace IxCCTests.Pipeline.Twin

open IxCC IxCC.Recheck IxCCTests.Src
open IxCCTests.Support (RngM Rng)

def limit : Nat := 2 ^ 63

/-- The Lean-compiled twin. -/
def twin : String → List Nat → Option Nat
  | "K1.fib", [n] => some (K1.fib n)
  | "K1.sumLoop", [n] => some (K1.sumLoop n)
  | "K1.ack", [m, n] => some (K1.ack m n)
  | "K1.tak", [f, x, y, z] => some (K1.tak f x y z)
  | "K1.gcd", [a, b] => some (K1.gcd a b)
  | _, _ => none

/-- A value: small, below `2⁶³` anywhere, or near the boundary. -/
def value : RngM Nat := do
  match ← RngM.below 4 with
  | 0 => RngM.below 30
  | 1 => RngM.below (1 <<< 32)
  | 2 => RngM.below limit
  | _ => return limit - 1 - (← RngM.below 4)

/-- Generated inputs for a root (their cost stays small natively and in
Lean), then its boundary cases. -/
def generate (root : String) (count : Nat) : RngM (List (List Nat)) := do
  let gen : RngM (List Nat) := match root with
    | "K1.fib" => do return [← RngM.below 28]
    | "K1.sumLoop" => do
      return [← (do if ← RngM.chance 70 then RngM.below 1000 else RngM.below 3000000)]
    | "K1.ack" => do
      match ← RngM.below 4 with
      | 3 => return [3, ← RngM.below 8]
      | 2 => return [2, ← RngM.below 300]
      | 1 => return [1, ← RngM.below 3000]
      | _ => return [0, ← value]
    | "K1.tak" => do return [← RngM.below 9, ← value, ← value, ← value]
    | _ => do return [← value, ← value]
  let drawn ← (List.range count).mapM fun _ => gen
  let edges := match root with
    | "K1.fib" => [[0], [1], [2], [limit], [limit + 5]]
    | "K1.sumLoop" => [[0], [1], [2], [limit]]
    | "K1.ack" => [[0, 0], [0, limit - 2], [0, limit - 1], [0, limit], [limit, 0], [3, 5]]
    | "K1.tak" => [[3, limit - 1, limit - 2, 5], [8, limit - 1, 0, limit - 1], [0, 0, 0, limit], [limit, 1, 2, 3]]
    | _ => [[limit - 1, limit - 2], [0, limit - 1], [limit - 1, 0], [limit, 1], [1, limit]]
  return drawn ++ edges

/-- What the compiled root must return: status 3 when an argument or the
twin's result has no word (`true`), else the twin's result, where status 3 is
also allowed (an intermediate value without a word). -/
def expected (root : String) (xs : List Nat) : Option (Bool × Nat) :=
  if xs.any (· ≥ limit) then some (true, 0)
  else (twin root xs).map fun r => if r ≥ limit then (true, 0) else (false, r)

structure Tally where
  runs : Nat := 0
  lir : Nat := 0
  native : Nat := 0
  wrapper : Nat := 0
  noWord : Nat := 0
  /-- Status 3 on inputs whose arguments and result have words. -/
  midOverflow : Nat := 0
  examples : List (List Nat) := []

/-- Judge one outcome (status and value) against the twin: status 3 where
it is required; otherwise the twin's value, or status 3 (allowed). -/
def judge (a : Assert) (label : String) (xs : List Nat) (must : Bool) (value status got : Nat) : IO Unit := do
  if must then expect a (status == 3) s!"{label} {xs}: status {status}, expected 3 (no word)"
  else if status != 3 then
    expect a (status == 0 && got == value) s!"{label} {xs}: status {status} value {got}, twin {value}"

def run (a : Assert) (native : Option Rt.Native.Tools) (count seed : Nat) : IO (Array String) := do
  let inp ← ingressFile k1Ixe k1Eqs (k1Roots.map (·.1))
  let (_, art) ← compileIn "k1" inp
  let mem ← IO.ofExcept (IxCCTests.Rt.initRegion art.lowered)
  let mut out := #[]
  let mut total : Tally := {}
  for (root, (name, _)) in art.roots.zip k1Roots do
    let (inputs, _) := (generate name count).run (Rng.ofSeed (UInt64.ofNat (seed + name.length)))
    let mut t : Tally := {}
    -- Lir, below the wrapper (arguments with words; short loops)
    let mut rows : List (List Nat × Bool × Nat × Option Nat) := []
    for xs in inputs do
      let some (must, value) := expected name xs | throw (IO.userError s!"{name}: no twin")
      let mut lirStatus := none
      if !(xs.any (· ≥ limit)) && !(name == "K1.sumLoop" && xs.head! > 100000) then
        let r ← IxCCTests.Rt.runLir art.lowered root.fn (1 <<< 40) xs mem
        let (status, got) ← match r with
          | .ok ([w], _) => pure (0, w.toNat / 2)
          | .resource .natOverflow => pure (3, 0)
          | r => do expect a false s!"{name} {xs} at Lir: {IxCCTests.Rt.lirOutcome r}"; pure (0, 0)
        judge a s!"{name} at Lir" xs must value status got
        lirStatus := some status
        t := { t with lir := t.lir + 1 }
      rows := rows ++ [(xs, must, value, lirStatus)]
    -- natively under the driver, and the same status as at Lir
    let mut nativeStatus : List (Option Nat) := rows.map fun _ => none
    if let some nt := native then
      let exe ← link nt s!"twin_{name.replace "." "_"}" art.object root.symbol
      let lines ← Rt.Native.run exe { stack := 1 <<< 28, ty := root.ty } (rows.map (·.1))
      for ((xs, must, value, lirStatus), l) in rows.zip lines do
        expect a l.ok s!"{name} {xs} natively: registers not restored"
        judge a s!"{name} natively" xs must value l.status.toNat ((l.obs.bind String.toNat?).getD 0)
        if let some s := lirStatus then
          expect a (s == l.status.toNat) s!"{name} {xs}: status {l.status} natively, {s} at Lir"
      nativeStatus := lines.map fun l => some l.status.toNat
      t := { t with native := t.native + lines.length }
    for ((xs, must, _, lirStatus), ns) in rows.zip nativeStatus do
      t := { t with runs := t.runs + 1 }
      if xs.any (· ≥ limit) then t := { t with wrapper := t.wrapper + 1 }
      else if must then t := { t with noWord := t.noWord + 1 }
      else if lirStatus == some 3 || ns == some 3 then
        -- only `tak`'s `y + 1` can leave the words on these inputs: every
        -- other intermediate value is at most an argument or the result
        expect a (name == "K1.tak" && (xs.drop 1).contains (limit - 1))
          s!"{name} {xs}: status 3, but no intermediate value can reach 2^63"
        t := { t with midOverflow := t.midOverflow + 1
                      examples := if t.examples.length < 2 then t.examples ++ [xs] else t.examples }
    let eg := if t.examples.isEmpty then "" else s!", e.g. {t.examples}"
    out := out.push s!"{name} ({root.symbol}): {t.runs} inputs ({t.wrapper} with an argument ≥ 2^63, \
      {t.noWord} with a result ≥ 2^63, {t.midOverflow} with an intermediate value ≥ 2^63{eg}): \
      {t.lir} at Lir, {t.native} natively agree with Lean"
    total := { runs := total.runs + t.runs, lir := total.lir + t.lir, native := total.native + t.native
               wrapper := total.wrapper + t.wrapper, noWord := total.noWord + t.noWord
               midOverflow := total.midOverflow + t.midOverflow }
  return #[s!"{total.runs} inputs over the five roots: {total.lir} at Lir, {total.native} natively; \
    status 3 from the wrapper on {total.wrapper}, from a result without a word on {total.noWord}, \
    from an intermediate value without a word on {total.midOverflow}"] ++ out

end IxCCTests.Pipeline.Twin
