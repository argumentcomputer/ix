import IxCC.Src.AutoHints
import IxCC.Src.Load
import IxCCTests.Src.Support

/-! # Auto-Hints (`IxCC.Src.AutoHints`) unit, synthetic, timing, and equivalence tests

Covers:
1. `Hints.toK1Json` / `Hints.ofK1Json` canonical round-trip.
2. `AutoHints.parseRootSpec` & `AutoHints.resolveRoots` on anonymous and named `.ixe` closures
   (bare `<64-hex>`, `<NAME>=<64-hex>`, bare `<NAME>`, default `"entry"`, negative/invalid specs).
3. Synthetic competing-theorem tests: partial lemma `f 0 = 1`, reflexivity `f x = f x`,
   commutativity `g x y = g y x`, non-`Eq` theorem, real `f.eq_def`, `.share`-wrapped `eq_def`,
   and `Table.build` non-shadowing when an earlier `.eqn` proposal fails `checkEqn`.
4. Closure-wide discovery coverage, determinism, sub-millisecond/low-ms timing, and
   `Src.loadAuto` vs `Src.load` table equivalence across K1 (`bench-k1`, `k1.ixe`),
   fixed-width words (`src-words/words.ixe`), and RC (`fixtures/rc/real-source/anonymous.ixe`). -/

set_option autoImplicit false

namespace IxCCTests.Src.AutoHints

open IxCC IxCC.Src IxCC.Src.AutoHints IxCC.Ixon IxCCTests.Src
open System

/-- Build a minimal §4/§5 metadata blob naming a list of `(name, addr)` pairs against
`env.consts` (for testing named `.ixe` resolution without external tools). -/
def mkNamedMetadata (env : V3.Env) (entries : List (String × Ixon.Address)) : ByteArray :=
  let constOrder : Array Ixon.Address :=
    (env.consts.toArray.map (·.1)).qsort fun a b => a.cmpBytes b == .lt
  let rankOf (a : Ixon.Address) : Option Nat :=
    constOrder.findIdx? (· == a)
  let resolved := entries.filterMap fun (nm, a) => (rankOf a).map (nm, ·)
  _root_.Ixon.runPut do
    -- §4: Names
    _root_.Ixon.putTagN 0 0 resolved.length.toUInt64
    for (nm, _) in resolved do
      let nmBytes := nm.toUTF8
      let nmAddr := Ixon.Address.blake3Pure nmBytes
      _root_.Ixon.putBytes nmAddr.hash
      _root_.Ixon.putU8 1 -- Name.str
      _root_.Ixon.putBytes (Ixon.Address.replicate 0).hash -- anon parent
      _root_.Ixon.putTagN 0 0 nmBytes.size.toUInt64
      _root_.Ixon.putBytes nmBytes
    -- §5: Named
    _root_.Ixon.putTagN 0 0 resolved.length.toUInt64
    for ((_, rank), idx) in resolved.zipIdx do
      _root_.Ixon.putTagN 0 0 idx.toUInt64
      _root_.Ixon.putTagN 0 0 rank.toUInt64
      _root_.Ixon.putTagN 0 0 0 -- hint
      _root_.Ixon.putTagN 0 0 0 -- metaLen

/-- Attach named §4/§5 metadata to raw `.ixe` bytes (replacing any trailing metadata). -/
def withNamedMetadata (bytes : ByteArray) (entries : List (String × Ixon.Address)) :
    Except String ByteArray := do
  let env ← V3.decodeAnonymousEnv bytes
  let prefixBytes := bytes.extract 0 (bytes.size - env.metadata.size)
  let metaBytes := mkNamedMetadata env entries
  pure (prefixBytes ++ metaBytes)

/-! ## 1. `Hints.toK1Json` round-trip -/

def testK1JsonRoundTrip (a : Assert) : IO Unit := do
  let a1 := Ixon.Address.blake3Pure "root1".toUTF8
  let a2 := Ixon.Address.blake3Pure "def1".toUTF8
  let a3 := Ixon.Address.blake3Pure "thm1".toUTF8
  let a4 := Ixon.Address.blake3Pure "wop1".toUTF8
  let a5 := Ixon.Address.blake3Pure "wthm1".toUTF8
  let h : Hints := {
    roots := #[(a1, some "entry")]
    proposals := #[
      { kind := .eqn, subject := a2, theorem? := some a3, name? := some "My.f" },
      { kind := .word, subject := a4, theorem? := some a5, name? := some "UInt64.add" }
    ]
  }
  let json := Hints.toK1Json h
  let text := json.compress
  match Hints.ofK1String text with
  | .error e => expect a false s!"toK1Json round-trip failed: {e}"
  | .ok h' =>
    expectEq a h'.roots.size 1 "toK1Json roots size"
    expect a (h'.roots[0]? == some (a1, some "entry")) "toK1Json root 0"
    expectEq a h'.proposals.size 2 "toK1Json proposals size"
    let hasEqn := h'.proposals.any fun p => p.kind == .eqn && p.subject == a2 && p.theorem? == some a3
    let hasWord := h'.proposals.any fun p => p.kind == .word && p.subject == a4 && p.theorem? == some a5
    expect a (hasEqn && hasWord) "toK1Json preserved eqn and word proposals"

/-! ## 2. Root spec parsing and resolution (anonymous & named `.ixe`) -/

def testRootResolution (a : Assert) : IO Unit := do
  let fibBytes ← IO.FS.readBinFile (fixtures / "bench-k1/fib.ixe")
  let fibEnv ← IO.ofExcept (V3.decodeAnonymousEnv fibBytes)
  let fibEqJson ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (fixtures / "bench-k1/fib.equations.json")))
  let fibSidecar ← IO.ofExcept (Hints.ofK1Json fibEqJson)
  let some (entryAddr, _) := fibSidecar.roots[0]?
    | throw (IO.userError "fib.equations.json missing entry root")
  let entryHex := toString entryAddr
  -- parseRootSpec positive cases
  expect a ((parseRootSpec entryHex).toOption == some (.byAddr entryAddr none)) "parseRootSpec bare 64-hex"
  expect a ((parseRootSpec s!"entry={entryHex}").toOption == some (.byAddr entryAddr (some "entry")))
    "parseRootSpec NAME=64-hex"
  expect a ((parseRootSpec "K1.fib").toOption == some (.byName "K1.fib")) "parseRootSpec bare NAME"
  -- parseRootSpec negative cases
  for bad in ["", "=deadbeef", "entry=not-valid-hex", "entry=deadbeef",
              "a=b=c", s!"0x{entryHex}"] do
    expect a (!(parseRootSpec bad).isOk) s!"parseRootSpec should reject '{bad}'"
  -- resolveRoots on anonymous fib.ixe
  match resolveRoots fibEnv [s!"entry={entryHex}"] with
  | .ok rs => expect a (rs == #[(entryAddr, some "entry")]) "resolveRoots anon NAME=hex"
  | .error e => expect a false s!"resolveRoots anon NAME=hex failed: {e}"
  match resolveRoots fibEnv [entryHex] with
  | .ok rs => expect a (rs == #[(entryAddr, none)]) "resolveRoots anon bare hex"
  | .error e => expect a false s!"resolveRoots anon bare hex failed: {e}"
  -- bare name on anonymous .ixe must fail cleanly
  match resolveRoots fibEnv ["entry"] with
  | .ok _ => expect a false "resolveRoots anon bare name should fail"
  | .error e => expect a ((e.splitOn "anonymous").length > 1) s!"expected anonymous error, got: {e}"
  -- omitted --root on anonymous .ixe without main must fail cleanly
  expect a (!(resolveRoots fibEnv []).isOk) "resolveRoots anon empty must fail"
  -- absent valid 64-hex address must fail cleanly
  let absentHex := toString (Ixon.Address.replicate 0)
  expect a (!(resolveRoots fibEnv [s!"entry={absentHex}"]).isOk) "resolveRoots absent addr must fail"
  -- duplicate export name must fail cleanly
  expect a (!(resolveRoots fibEnv [s!"entry={entryHex}", s!"entry={entryHex}"]).isOk)
    "resolveRoots duplicate name must fail"
  -- Named .ixe constructed from fib.ixe
  let namedBytes ← IO.ofExcept (withNamedMetadata fibBytes [("entry", entryAddr)])
  let namedEnv ← IO.ofExcept (V3.decodeAnonymousEnv namedBytes)
  match resolveRoots namedEnv ["entry"] with
  | .ok rs => expect a (rs == #[(entryAddr, some "entry")]) "resolveRoots named bare name"
  | .error e => expect a false s!"resolveRoots named bare name failed: {e}"
  match resolveRoots namedEnv [] with
  | .ok rs => expect a (rs == #[(entryAddr, some "entry")]) "resolveRoots named default entry"
  | .error e => expect a false s!"resolveRoots named default entry failed: {e}"
  expect a (!(resolveRoots namedEnv ["nonexistent"]).isOk) "resolveRoots named unknown must fail"
  match resolveRoots namedEnv [s!"custom={entryHex}"] with
  | .ok rs => expect a (rs == #[(entryAddr, some "custom")]) "resolveRoots named NAME=hex"
  | .error e => expect a false s!"resolveRoots named NAME=hex failed: {e}"

/-! ## 3. Synthetic competing theorems, `.share` handling, and `Table.build` non-shadowing -/

private def mkConstRecord (c : V3.Constant) : Ixon.Address × ByteArray :=
  let bs := V3.constantBytes c
  (Ixon.Address.blake3Pure bs, bs)

def testSyntheticCompeting (a : Assert) : IO Unit := do
  let pins := Pins.fixed
  let eqAddr := Pinned.addrOfNat (pins.eq.getD 0)
  let natAddr := Pinned.addrOfNat (pins.nat.getD 0)
  let natType : V3.Expr := .ref 0 #[]
  -- Safe definition `f : Nat → Nat := fun x => x`
  let fConst : V3.Constant := {
    info := .defn { kind := .defn, safety := .safe, lvls := 0,
                    typ := .all natType natType, value := .lam natType (.var 0) }
    sharing := #[], refs := #[natAddr], univs := #[]
  }
  let (fAddr, fBytes) := mkConstRecord fConst
  -- Safe 2-arg definition `g : Nat → Nat → Nat := fun x y => x`
  let gConst : V3.Constant := {
    info := .defn { kind := .defn, safety := .safe, lvls := 0,
                    typ := .all natType (.all natType natType),
                    value := .lam natType (.lam natType (.var 1)) }
    sharing := #[], refs := #[natAddr], univs := #[]
  }
  let (gAddr, gBytes) := mkConstRecord gConst
  let eqApp (eqIdx natIdx : UInt64) (lhs rhs : V3.Expr) : V3.Expr :=
    .app (.app (.app (.ref eqIdx #[0]) (.ref natIdx #[])) lhs) rhs
  -- 1. Partial lemma: `f 0 = 1` (LHS arg is `.nat 0`, NOT `.var 0`) -> MUST be filtered out
  let partialThm : V3.Constant := {
    info := .defn { kind := .thm, safety := .safe, lvls := 0,
                    typ := eqApp 1 0 (.app (.ref 2 #[]) (.nat 3)) (.nat 4),
                    value := .var 0 }
    sharing := #[], refs := #[natAddr, eqAddr, fAddr, Ixon.Address.replicate 1, Ixon.Address.replicate 2],
    univs := #[.succ .zero]
  }
  let (partialAddr, partialBytes) := mkConstRecord partialThm
  -- 2. Reflexivity lemma: `∀ x : Nat, f x = f x` -> MUST be filtered out
  let reflThm : V3.Constant := {
    info := .defn { kind := .thm, safety := .safe, lvls := 0,
                    typ := .all (.ref 0 #[]) (eqApp 1 0 (.app (.ref 2 #[]) (.var 0)) (.app (.ref 2 #[]) (.var 0))),
                    value := .var 0 }
    sharing := #[], refs := #[natAddr, eqAddr, fAddr], univs := #[.succ .zero]
  }
  let (reflAddr, reflBytes) := mkConstRecord reflThm
  -- 3. Commutative self-cycle lemma: `∀ x y : Nat, g x y = g y x` -> MUST be filtered out
  let swapThm : V3.Constant := {
    info := .defn { kind := .thm, safety := .safe, lvls := 0,
                    typ := .all (.ref 0 #[]) (.all (.ref 0 #[])
                      (eqApp 1 0 (.app (.app (.ref 2 #[]) (.var 1)) (.var 0))
                                 (.app (.app (.ref 2 #[]) (.var 0)) (.var 1)))),
                    value := .var 0 }
    sharing := #[], refs := #[natAddr, eqAddr, gAddr], univs := #[.succ .zero]
  }
  let (swapAddr, swapBytes) := mkConstRecord swapThm
  -- 4. Non-Eq theorem: `∀ x : Nat, Nat` -> MUST be filtered out
  let nonEqThm : V3.Constant := {
    info := .defn { kind := .thm, safety := .safe, lvls := 0,
                    typ := .all (.ref 0 #[]) (.ref 0 #[]), value := .var 0 }
    sharing := #[], refs := #[natAddr], univs := #[]
  }
  let (nonEqAddr, nonEqBytes) := mkConstRecord nonEqThm
  -- 5. Real unfolding theorem: `∀ x : Nat, f x = x` -> MUST be discovered
  let realThm : V3.Constant := {
    info := .defn { kind := .thm, safety := .safe, lvls := 0,
                    typ := .all (.ref 0 #[]) (eqApp 1 0 (.app (.ref 2 #[]) (.var 0)) (.var 0)),
                    value := .var 0 }
    sharing := #[], refs := #[natAddr, eqAddr, fAddr], univs := #[.succ .zero]
  }
  let (realAddr, realBytes) := mkConstRecord realThm
  -- 6. Share-wrapped unfolding theorem for `g`: `∀ x y : Nat, g x y = x` via `.share` nodes
  let shareThm : V3.Constant := {
    info := .defn { kind := .thm, safety := .safe, lvls := 0,
                    typ := .all (.ref 0 #[]) (.share 0),
                    value := .var 0 }
    sharing := #[
      .all (.ref 0 #[]) (.share 1),
      .app (.app (.share 2) (.share 3)) (.var 1),
      .app (.ref 1 #[0]) (.ref 0 #[]),
      .app (.app (.ref 2 #[]) (.share 4)) (.var 0),
      .var 1
    ]
    refs := #[natAddr, eqAddr, gAddr], univs := #[.succ .zero]
  }
  let (shareAddr, shareBytes) := mkConstRecord shareThm
  let mut consts : Std.HashMap Ixon.Address ByteArray := {}
  for (k, v) in [(fAddr, fBytes), (gAddr, gBytes), (partialAddr, partialBytes),
                 (reflAddr, reflBytes), (swapAddr, swapBytes), (nonEqAddr, nonEqBytes),
                 (realAddr, realBytes), (shareAddr, shareBytes)] do
    consts := consts.insert k v
  let synEnv : V3.Env := { consts }
  let props := AutoHints.discover synEnv pins
  expectEq a props.size 2 "synthetic discover should emit exactly 2 proposals (real + share)"
  expect a (props.any fun p => p.kind == .eqn && p.subject == fAddr && p.theorem? == some realAddr)
    "synthetic discover must find real f.eq_def"
  expect a (props.any fun p => p.kind == .eqn && p.subject == gAddr && p.theorem? == some shareAddr)
    "synthetic discover must find share-wrapped g.eq_def"
  expect a (!props.any fun p => p.theorem? == some partialAddr || p.theorem? == some reflAddr ||
      p.theorem? == some swapAddr || p.theorem? == some nonEqAddr)
    "synthetic discover must filter partial, refl, swap, and non-Eq theorems"
  -- Verify Table.build non-shadowing: a failing earlier `.eqn` proposal for `K1.fib` does not
  -- prevent a subsequent valid `K1.fib.eq_def` proposal from resolving `K1.fib`.
  let fibEqJson ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (fixtures / "bench-k1/fib.equations.json")))
  let fibSidecar ← IO.ofExcept (Hints.ofK1Json fibEqJson)
  let some fibProp := fibSidecar.proposals.find? (·.name? == some "K1.fib")
    | throw (IO.userError "fib.equations.json missing K1.fib proposal")
  let some badProp := fibSidecar.proposals.find? (·.name? == some "Nat.add")
    | throw (IO.userError "fib.equations.json missing Nat.add proposal")
  let bogusFirst : Proposal := { kind := .eqn, subject := fibProp.subject, theorem? := badProp.theorem?, name? := some "bogus-first" }
  let fibLoaded ← loadBench "fib"
  let (tab, _, st) := Table.build {} fibLoaded.program (#[bogusFirst] ++ fibSidecar.proposals)
  let some fibCid := fibLoaded.program.lookup fibProp.subject
    | throw (IO.userError "fib CId lookup failed")
  expect a (tab.resolveOf fibCid matches some (.eqn ..))
    "Table.build must fall through to valid eq_def when earlier proposal for same subject fails"
  expect a (st.eqnRefused.any fun (c, _) => c == fibCid)
    "Table.build should record refusal of bogus earlier proposal"

/-! ## 4. Closure-wide coverage, timing, determinism, and `loadAuto` vs `load` parity -/

private def checkClosureDiscovery (a : Assert) (label : String) (ixe eqs : FilePath) : IO String := do
  let bytes ← IO.FS.readBinFile ixe
  let env ← IO.ofExcept (V3.decodeAnonymousEnv bytes)
  let eqJson ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile eqs))
  let sidecar ← IO.ofExcept (Hints.ofK1Json eqJson)
  let pins := Pins.fixed
  let t0 ← IO.monoNanosNow
  let props ← IO.lazyPure fun _ => AutoHints.discover env pins
  let t1 ← IO.monoNanosNow
  let props2 ← IO.lazyPure fun _ => AutoHints.discover env pins
  let us := (t1 - t0) / 1000
  -- Determinism
  expect a (props.size == props2.size &&
      (props.toList.zip props2.toList).all fun (x, y) =>
        x.kind == y.kind && x.subject == y.subject && x.theorem? == y.theorem?)
    s!"{label}: AutoHints.discover must be 100% deterministic"
  -- Coverage: every sidecar `.eqn` and `.word` proposal must be discovered!
  let mut missingEqn := 0
  let mut missingWord := 0
  for sp in sidecar.proposals do
    let hit := props.any fun p => p.kind == sp.kind && p.subject == sp.subject && p.theorem? == sp.theorem?
    if !hit then
      if sp.kind == .eqn then missingEqn := missingEqn + 1
      else if sp.kind == .word then missingWord := missingWord + 1
  expectEq a missingEqn 0 s!"{label}: missing sidecar .eqn proposals"
  expectEq a missingWord 0 s!"{label}: missing sidecar .word proposals"
  let nEqn := props.foldl (fun n p => if p.kind == .eqn then n + 1 else n) 0
  let nWord := props.foldl (fun n p => if p.kind == .word then n + 1 else n) 0
  let sideEqn := sidecar.proposals.foldl (fun n p => if p.kind == .eqn then n + 1 else n) 0
  let sideWord := sidecar.proposals.foldl (fun n p => if p.kind == .word then n + 1 else n) 0
  pure s!"{label}: {env.consts.size} recs -> {props.size} proposals ({nEqn} eqn [sidecar {sideEqn}], {nWord} word [sidecar {sideWord}]) in {us} us"

/-- Verify `Src.loadAuto` preserves every resolved unfolding table entry (`prim`, `word`,
`eqn`, `csimp`, `case`) of `Src.load` with `--equations` (allowing extra kernel-verified
`.eqn` entries for non-recursive definitions that also carry an `Eq` theorem in the `.ixe`),
matches `wordHints`, and agrees on `Src.run` evaluation when sample args are supplied. -/
private def checkLoadAutoParity (a : Assert) (label : String) (ixe eqs : FilePath)
    (evalCase? : Option (List Nat × Nat) := none) : IO String := do
  let bytes ← IO.FS.readBinFile ixe
  let eqJson ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile eqs))
  let sidecar ← IO.ofExcept (Hints.ofK1Json eqJson)
  let rootSpecs := sidecar.roots.toList.map fun (addr, nm?) =>
    match nm? with
    | some n => s!"{n}={addr}"
    | none => toString addr
  let loadedEq ← match load bytes eqJson with
    | .ok l => pure l
    | .error d => throw (IO.userError s!"{label} load: {d}")
  let loadedAuto ← match loadAuto bytes rootSpecs with
    | .ok l => pure l
    | .error d => throw (IO.userError s!"{label} loadAuto: {d}")
  expectEq a loadedAuto.admitted.reached.size loadedEq.admitted.reached.size
    s!"{label}: loadAuto reached count vs load"
  let renderResolve (p : Program) (c : CId) : Option String :=
    match p.table.resolveOf c with
    | some (.prim op) => some s!"prim:{op.name}"
    | some (.word w op _) => some s!"word:{op.leanName w}"
    | some (.eqn thm _) => some s!"eqn:{p.addr thm}"
    | some (.csimp g _ _) => some s!"csimp:{p.addr g}"
    | some (.case r) => some s!"case:{p.addr r}"
    | none => none
  let eqMap : Std.HashMap Ixon.Address (Option String) :=
    loadedEq.admitted.reached.foldl (init := {}) fun m c =>
      m.insert (loadedEq.program.addr c) (renderResolve loadedEq.program c)
  let mut extraEqns := 0
  for c in loadedAuto.admitted.reached do
    let addr := loadedAuto.program.addr c
    let tag := renderResolve loadedAuto.program c
    match eqMap[addr]? with
    | none => expect a false s!"{label}: reached constant {addr} missing from sidecar load"
    | some (some expected) =>
      expect a (tag == some expected)
        s!"{label}: resolve mismatch at {addr}: auto={tag}, sidecar={some expected}"
    | some none =>
      match loadedAuto.program.table.resolveOf c with
      | none => pure ()
      | some (.eqn ..) => extraEqns := extraEqns + 1
      | some _ => expect a false s!"{label}: unexpected non-eqn resolve at {addr}: auto={tag}"
  expectEq a loadedAuto.wordHints.size loadedEq.wordHints.size
    s!"{label}: wordHints count mismatch"
  if let some (args, want) := evalCase? then
    let some rAuto := loadedAuto.root? | throw (IO.userError s!"{label}: loadAuto missing root")
    let some rEq := loadedEq.root? | throw (IO.userError s!"{label}: load missing root")
    let resAuto ← runRoot loadedAuto.program 100000 rAuto args
    let resEq ← runRoot loadedEq.program 100000 rEq args
    expectEq a (natOf resAuto) (some want) s!"{label}: loadAuto Src.run {args}"
    expectEq a (natOf resEq) (some want) s!"{label}: load Src.run {args}"
  pure s!"{label}: loadAuto == load ({loadedAuto.admitted.reached.size} reached, \
    {loadedAuto.tableStats.eqnAccepted.size} eqn [+{extraEqns} extra], \
    {loadedAuto.tableStats.wordAccepted.size} word)"

def run (a : Assert) : IO (Array String) := do
  testK1JsonRoundTrip a
  testRootResolution a
  testSyntheticCompeting a
  let mut out := #["unit + synthetic competing-theorem + root-resolution checks passed"]
  let closures : List (String × FilePath × FilePath) := [
    ("fib", fixtures / "bench-k1/fib.ixe", fixtures / "bench-k1/fib.equations.json"),
    ("sfib", fixtures / "bench-k1/sfib.ixe", fixtures / "bench-k1/sfib.equations.json"),
    ("even-odd", fixtures / "bench-k1/even-odd.ixe", fixtures / "bench-k1/even-odd.equations.json"),
    ("gcd", fixtures / "bench-k1/gcd.ixe", fixtures / "bench-k1/gcd.equations.json"),
    ("tak", fixtures / "bench-k1/tak.ixe", fixtures / "bench-k1/tak.equations.json"),
    ("ackermann", fixtures / "bench-k1/ackermann.ixe", fixtures / "bench-k1/ackermann.equations.json"),
    ("collatz", fixtures / "bench-k1/collatz.ixe", fixtures / "bench-k1/collatz.equations.json"),
    ("prime-count", fixtures / "bench-k1/prime-count.ixe", fixtures / "bench-k1/prime-count.equations.json"),
    ("sum-loop", fixtures / "bench-k1/sum-loop.ixe", fixtures / "bench-k1/sum-loop.equations.json"),
    ("k1", fixtures / "k1/k1.ixe", fixtures / "k1/equations.json"),
    ("src-words", fixtures / "src-words/words.ixe", fixtures / "src-words/words.equations.json"),
    ("rc-real-source", "fixtures/rc/real-source/anonymous.ixe", "fixtures/rc/real-source/consumer.equations.json")
  ]
  for (label, ixe, eqs) in closures do
    out := out.push (← checkClosureDiscovery a label ixe eqs)
  for (label, ixe, eqs, evalCase?) in [
    ("fib", fixtures / "bench-k1/fib.ixe", fixtures / "bench-k1/fib.equations.json", some ([10], 55)),
    ("even-odd", fixtures / "bench-k1/even-odd.ixe", fixtures / "bench-k1/even-odd.equations.json", none),
    ("gcd", fixtures / "bench-k1/gcd.ixe", fixtures / "bench-k1/gcd.equations.json", some ([48, 18], 6)),
    ("src-words", fixtures / "src-words/words.ixe", fixtures / "src-words/words.equations.json", none)
  ] do
    out := out.push (← checkLoadAutoParity a label ixe eqs evalCase?)
  return out

def main : IO UInt32 := do
  let a ← IO.mkRef 0
  try
    let (lines, ms) ← timed (run a)
    IO.println s!"tests-src (auto-hints): {← a.get} assertions passed in {ms} ms"
    for l in lines do IO.println s!"    {l}"
    return 0
  catch e =>
    IO.eprintln s!"tests-src (auto-hints): FAILED after {← a.get} assertions: {e}"
    return 1

end IxCCTests.Src.AutoHints
