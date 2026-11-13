import IxCC.Anf.Pipeline
import IxCC.Anf.Print
import IxCCTests.Src.Support

/-! The shrink walk's bound on literal folding (`Anf.Walk.foldable`, `foldBits` = 1024). Unbounded,
`Lam.Prim.sem` on literals computed `a ^ b` and `a * 2 ^ b` whatever their size: the runtime's
`Nat.pow` aborts the process past an exponent of `2 ^ 32 − 1` (the producer and the verifier's replay
alike), builds the number below it, and a chain of folded squarings doubles its literal at each
step. The fixture-level reproducers (an artifact `ix compile` wrote, through `ixcc compile` and
`check-cert`) are `tests-exe`'s fold-guard part (`fixtures/fold`).

* **The decision at its boundaries**: each clause (every operand below `2 ^ 1024`; `natPow`'s exponent
  and base; `natShl`'s shift and value) admits the last case inside it and refuses the first past it.
* **Mutants**: each bound one too generous, the `natPow` or the `natShl` clause dropped, or the
  operand bound dropped, disagrees with that table somewhere. Only decisions are compared: no mutant
  folds anything.
* **Exactness**: wherever `foldable` admits a case of a grid of operands, `fold` gives the result an
  independent computation gives (repeated multiplication for `natPow`, `Nat.shiftLeft` for `natShl`),
  below `2 ^ 1024` for those two and below `2 ^ 2048` for every primitive; elsewhere `none`.
* **The middle end on one-global programs**: `Anf.Pipeline.produce` (what `ixcc compile` runs) and
  `Anf.Pipeline.run` on its certificate (what `check-cert` replays) finish, within a time bound, on
  `natPow`/`natShl` at the bound, at and past `2 ^ 32 − 1` and at `2 ^ 64`, on a chain of 32 folded
  squarings and on an oversized literal, keeping the primitive past the bound; a certificate made on
  one side of the bound replays on a program on the other. The part's peak memory is bounded too. -/

namespace IxCCTests.Anf.FoldGuard

open IxCC IxCC.Anf IxCCTests.Src

abbrev K : Nat := Walk.foldBits

/-- A decision procedure with `Walk.foldable`'s type. -/
abbrev Guard := Lam.Prim → List Nat → Bool

/-- The boundary table: each case and the decision `Walk.foldable` must make. -/
def table : List (Lam.Prim × List Nat × Bool) :=
  [(.natAdd, [2 ^ K - 1, 0], true), (.natAdd, [2 ^ K, 0], false), (.natAdd, [0, 2 ^ K], false),
   (.natMul, [2 ^ K - 1, 2 ^ K - 1], true), (.natMul, [2 ^ K, 1], false),
   (.natMod, [2 ^ 1100, 7], false), (.natMod, [2 ^ 1000, 7], true),
   (.natPow, [7, 0], true), (.natPow, [2 ^ K - 1, 0], true), (.natPow, [2 ^ K, 0], false),
   (.natPow, [2 ^ K - 1, 1], true), (.natPow, [1, K], true), (.natPow, [1, K + 1], false),
   (.natPow, [0, K + 1], false), (.natPow, [2, K / 2], true), (.natPow, [2, K / 2 + 1], false),
   (.natPow, [3, K / 2], true), (.natPow, [4, K / 2], false), (.natPow, [0, 2 ^ 32 - 1], false),
   (.natPow, [1, 2 ^ 32], false), (.natPow, [2, 2 ^ 64], false),
   (.natShl, [1, K - 1], true), (.natShl, [1, K], false), (.natShl, [0, K], true),
   (.natShl, [0, K + 1], false), (.natShl, [2 ^ (K - 1) - 1, 1], true),
   (.natShl, [2 ^ (K - 1), 1], false), (.natShl, [2 ^ K - 1, 0], true), (.natShl, [1, 2 ^ 32], false),
   (.word .w64 .add, [1, 2], true), (.word .w64 .ofNat, [2 ^ 70], true)]

/-- The cases of `table` where `g` decides otherwise. -/
def misses (g : Guard) : List (Lam.Prim × List Nat) :=
  table.filterMap fun (p, ns, want) => if g p ns == want then none else some (p, ns)

/-- `Walk.foldable` with one change. -/
def mutant (limit : Nat := 2 ^ K) (powB : Nat := K) (powA : Nat → Nat := fun e => e)
    (shlB : Nat := K) (shlA : Nat → Nat := fun e => e) (pow shl : Bool := true) : Guard :=
  fun p ns =>
    ns.all (· < limit) &&
      match p, ns with
      | .natPow, [a, b] => !pow || b == 0 || (b ≤ powB && a < 2 ^ powA (K / b))
      | .natShl, [a, b] => !shl || (b ≤ shlB && a < 2 ^ shlA (K - b))
      | _, _ => true

def mutants : List (String × Guard) :=
  [("the operand bound one bit too generous", mutant (limit := 2 ^ (K + 1))),
   ("the operand bound dropped", mutant (limit := 2 ^ 100000)),
   ("natPow's exponent bound one too generous", mutant (powB := K + 1)),
   ("natPow's base bound one bit too generous", mutant (powA := (· + 1))),
   ("natShl's shift bound one too generous", mutant (shlB := K + 1)),
   ("natShl's value bound one bit too generous", mutant (shlA := (· + 1))),
   ("natPow's clause dropped", mutant (pow := false)),
   ("natShl's clause dropped", mutant (shl := false))]

/-- `a ^ b` by repeated multiplication (an oracle independent of `Nat.pow`). -/
def powRef (a b : Nat) : Nat := (List.replicate b a).foldl (· * ·) 1

def litOpds (ns : List Nat) : List Opd := ns.map fun n => .lit (.nat n)

/-- Exactness on a grid: `(cases, folded, misses)`. -/
def exactness : Nat × Nat × List String := Id.run do
  let bases := [0, 1, 2, 3, 7, 2 ^ 62, 2 ^ 511, 2 ^ 1023, 2 ^ K - 1, 2 ^ K, 2 ^ 1100]
  let exps := [0, 1, 2, 63, 64, 511, 512, 513, 1022, 1023, 1024, 1025, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 64]
  let others : List Lam.Prim := [.natAdd, .natSub, .natMul, .natDiv, .natMod, .natGcd, .natBeq,
    .natBle, .natBlt, .natLand, .natLor, .natXor, .natShr]
  let mut cases := 0
  let mut folded := 0
  let mut bad : List String := []
  for p in [Lam.Prim.natPow, .natShl] do
    for a in bases do
      for b in exps do
        cases := cases + 1
        let ns := [a, b]
        match Walk.foldable p ns, Walk.fold p (litOpds ns) with
        | true, some (.nat r) =>
          folded := folded + 1
          let want := if p == .natPow then powRef a b else a <<< b
          unless r == want && r < 2 ^ K do bad := bad ++ [s!"{p.name} [{a.log2}, {b}]"]
        | false, none => pure ()
        | _, _ => bad := bad ++ [s!"{p.name} [log2 {a.log2}, {b}]: fold and foldable disagree"]
  for p in others do
    for a in bases do
      for b in bases do
        cases := cases + 1
        let ns := [a, b]
        let inside := a < 2 ^ K && b < 2 ^ K
        match Walk.fold p (litOpds ns) with
        | some (.nat r) =>
          folded := folded + 1
          unless inside && some (.nat r) == p.sem ns && r < 2 ^ (2 * K) do
            bad := bad ++ [s!"{p.name} [log2 {a.log2}, log2 {b.log2}]"]
        | some (.bool _) =>
          folded := folded + 1
          unless inside do bad := bad ++ [s!"{p.name} [log2 {a.log2}, log2 {b.log2}] past the bound"]
        | none => unless !inside do bad := bad ++ [s!"{p.name} [log2 {a.log2}, log2 {b.log2}] not folded"]
  return (cases, folded, bad)

/-! ## The middle end on one-global programs -/

def prog (body : Lam.Term) : Lam.Program :=
  let g : Lam.Global := { key := .const 0 [], body }
  { globals := Src.NatMap.ofList [(0, g)], size := 1, roots := [0], ctors := [], known := {} }

def lit (n : Nat) : Lam.Term := .lit (.nat n)

def prim2 (p : Lam.Prim) (a b : Lam.Term) : Lam.Term := .prim p [a, b]

/-- `k` squarings of `2 ^ 62` in `let`s, then `% 7`. -/
def mulChain (k : Nat) : Lam.Term :=
  let rec go : Nat → Lam.Term
    | 0 => prim2 .natMod (.var 0) (lit 7)
    | n + 1 => .letE { nonDep := true } (prim2 .natMul (.var 0) (.var 0)) (go n)
  .letE { nonDep := true } (lit (2 ^ 62)) (go k)

mutual
/-- The primitives and the literals of an Anf expression. -/
partial def scan : Exp → List Lam.Prim × List Nat
  | .bind _ b e =>
    let (ps, ls) := scanBind b
    let (ps', ls') := scan e
    (ps ++ ps', ls ++ ls')
  | .join _ _ b e =>
    let (ps, ls) := scan b
    let (ps', ls') := scan e
    (ps ++ ps', ls ++ ls')
  | .jump _ as => ([], atomLits as)
  | .case x alts d =>
    let r := (alts.map fun (.mk _ _ b) => scan b) ++ (d.map scan).toList
    (r.flatMap (·.1), atomLits [x] ++ r.flatMap (·.2))
  | .ret a => ([], atomLits [a])
  | .tick e => scan e
  | .trap => ([], [])
partial def scanBind : Bind → List Lam.Prim × List Nat
  | .atom a => ([], atomLits [a])
  | .prim p as => ([p], atomLits as)
  | .con _ as | .call _ as => ([], atomLits as)
  | .app f as => ([], atomLits (f :: as))
  | .proj _ _ x => ([], atomLits [x])
  | .fn _ b => scan b
  | .glob _ => ([], [])
partial def atomLits (as : List Atom) : List Nat :=
  as.filterMap fun | .lit (.nat n) => some n | _ => none
end

/-- The primitives and the largest literal of a program. -/
def summary (A : Program) : List Lam.Prim × Nat :=
  let r := A.globalList.map fun (_, gd) => scan gd.body
  (r.flatMap (·.1), (r.flatMap (·.2)).foldl max 0)

/-- The process's peak resident memory (`VmHWM`, kB), or 0 off Linux. -/
def peakKb : IO Nat := do
  try
    let s ← IO.FS.readFile "/proc/self/status"
    let some l := (s.splitOn "\n").find? (·.startsWith "VmHWM:") | return 0
    let digits := (l.splitOn " ").filter fun t => !t.isEmpty && t.all Char.isDigit
    return (digits.headD "0").toNat!
  catch _ => return 0

/-- Milliseconds one program may take through `produce` and `run` (measured at most a few: the
bound is loose for a loaded machine). -/
def msBound : Nat := 2000

/-- The part's peak memory may rise by at most this (kB) over the process's peak before it. -/
def kbBound : Nat := 1048576

def run (a : Assert) : IO (Array String) := do
  let mut out := #[]
  -- the decision
  let realMisses := misses Walk.foldable
  expect a realMisses.isEmpty s!"foldable decides otherwise than the table at {realMisses.map (·.1.name)}"
  let mut caught := #[]
  for (label, g) in mutants do
    let m := (misses g).length
    expect a (m > 0) s!"the mutant with {label} decides every boundary case as foldable does"
    caught := caught.push s!"{label} {m}"
  out := out.push s!"foldable: {table.length} boundary cases decided as written; mutants caught \
    (cases they miss): {", ".intercalate caught.toList}"
  let (cases, folded, bad) := exactness
  expect a bad.isEmpty s!"folding inexact or past its bound at {bad}"
  out := out.push s!"exactness: {cases} cases, {folded} folded, each equal to the independent value \
    and within its bound, the rest not folded"
  -- the middle end
  let before ← peakKb
  let progs : List (String × Lam.Term × Bool) :=
    [("natPow [1, K]", prim2 .natPow (lit 1) (lit K), true),
     ("natPow [1, K + 1]", prim2 .natPow (lit 1) (lit (K + 1)), false),
     ("natPow [2, K / 2]", prim2 .natPow (lit 2) (lit (K / 2)), true),
     ("natPow [2, K / 2 + 1]", prim2 .natPow (lit 2) (lit (K / 2 + 1)), false),
     ("natShl [1, K - 1]", prim2 .natShl (lit 1) (lit (K - 1)), true),
     ("natShl [1, K]", prim2 .natShl (lit 1) (lit K), false)] ++
    ([0, 1, 2].flatMap fun b =>
      [(s!"natPow [{b}, 2^32 - 1]", prim2 .natPow (lit b) (lit (2 ^ 32 - 1)), false),
       (s!"natPow [{b}, 2^32]", prim2 .natPow (lit b) (lit (2 ^ 32)), false),
       (s!"natShl [{b}, 2^32 - 1]", prim2 .natShl (lit b) (lit (2 ^ 32 - 1)), false),
       (s!"natShl [{b}, 2^32]", prim2 .natShl (lit b) (lit (2 ^ 32)), false)]) ++
    [("natPow [1, 2^64]", prim2 .natPow (lit 1) (lit (2 ^ 64)), false),
     ("natMod [natPow [2, 100], 7]", prim2 .natMod (prim2 .natPow (lit 2) (lit 100)) (lit 7), true),
     ("natMod [natPow [2, 513], 7]", prim2 .natMod (prim2 .natPow (lit 2) (lit 513)) (lit 7), false),
     ("natMod [2^1100, 7]", prim2 .natMod (lit (2 ^ 1100)) (lit 7), false),
     ("32 chained squarings of 2^62, then % 7", mulChain 32, false)]
  let mut certs : List (String × Pipeline.Cert) := []
  let mut slowest := 0
  for (label, body, folds) in progs do
    let L := prog body
    let ((t, A), ms) ← timed do
      let t ← IO.ofExcept (← IO.lazyPure fun _ => Pipeline.produce {} L)
      let A ← IO.ofExcept (← IO.lazyPure fun _ => Pipeline.run t.cert L)
      pure (t, A)
    slowest := max slowest ms
    expect a (ms ≤ msBound) s!"{label}: produce and run took {ms} ms (bound {msBound})"
    let final := ((t.stages.getLast?).map (·.2)).getD default
    expect a (final.render == A.render) s!"{label}: the replay differs from the producer's program"
    let (ps, maxLit) := summary A
    expect a (maxLit < 2 ^ (2 * K)) s!"{label}: a literal of {maxLit.log2 + 1} bits"
    -- folded: no primitive left; refused: the primitive the bound refuses is still there
    expect a (folds == ps.isEmpty) s!"{label}: primitives left {ps.map (·.name)}, expected folded {folds}"
    certs := certs ++ [(label, t.cert)]
  -- a certificate made on one side of the bound, replayed on a program on the other
  let cross : List (String × String × Lam.Term) :=
    [("natPow [1, K]", "natPow [1, K + 1]", prim2 .natPow (lit 1) (lit (K + 1))),
     ("natPow [1, K + 1]", "natPow [1, K]", prim2 .natPow (lit 1) (lit K)),
     ("natShl [1, K - 1]", "natShl [1, K]", prim2 .natShl (lit 1) (lit K)),
     ("natPow [1, 2^32 - 1]", "natPow [1, 2^32]", prim2 .natPow (lit 1) (lit (2 ^ 32)))]
  for (from_, onto, body) in cross do
    match certs.lookup from_ with
    | none => expect a false s!"no certificate of {from_}"
    | some cert =>
      let (r, ms) ← timed (IO.lazyPure fun _ => Pipeline.run cert (prog body))
      match r with
      | .ok A =>
        let (ps, maxLit) := summary A
        expect a (ms ≤ msBound && maxLit < 2 ^ (2 * K))
          s!"{from_}'s certificate on {onto}: {ms} ms, a literal of {maxLit.log2 + 1} bits"
        -- on the refused side the primitive is never folded, whatever the certificate's rounds
        if onto != "natPow [1, K]" then
          expect a (!ps.isEmpty) s!"{from_}'s certificate on {onto}: folded past the bound"
      | .error e => expect a false s!"{from_}'s certificate on {onto}: refused ({e})"
  let after ← peakKb
  expect a (after ≤ before + kbBound)
    s!"peak memory rose from {before} kB to {after} kB (bound {kbBound} kB more)"
  out := out.push s!"produce and run: {progs.length} one-global programs, the slowest {slowest} ms \
    (bound {msBound}); the bound's refusals keep their primitive; {cross.length} certificates replayed \
    across the bound; peak memory {before} kB before, {after} kB after"
  return out

end IxCCTests.Anf.FoldGuard
