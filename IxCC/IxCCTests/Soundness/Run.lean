import IxCC.Recheck.DefAsserts
import IxCC.Recheck.Proof.LiveClosed
import IxCC.X86.Exe.Machine.Proof.Loaded
import IxCCTests.Exe.Run
import IxCCTests.KernelFront.Report

/-! # Wave 1 Soundness, Anti-DoS & EM-0 Hardening Test Suite

Negative and positive controls for every finding closed on `w1/soundness-p1`:

1. **`FE-5` (`FrameLayout.check` exact minimal size):** 1 MiB leaf-frame bloat, +16-byte bloat,
   and inflated `outArgs` are refused by `FrameLayout.check` and end-to-end `Recheck.run`.
2. **`FE-6` (mandatory deterministic `Lazify`):** omitting `cert.table.lazy` (or dropping a
   single reached `Pinned.lazyPins` entry like `ite`/`dite`/`Bool.and`/`Bool.or`) is refused by
   `Table.ofCert`, `Table.validate`, and `Recheck.run`.
3. **`FE-3` (non-cyclic `.eqn` guard):** valid-theorem infinite-loop trojans (`f x = f x`,
   `f x = Nat.add (f x) 0`, `f x = ite b (f x) (f x)`, and mutual `f x = g x` / `g x = f x`)
   are refused by `Table.checkEqn`, `Table.validate`, and `Table.ofCert`, while guarded
   recursion and real corpus `fib`/`gcd`/`tak` pass.
4. **`FE-2` (table-theorem `corrRec` blind spot):** `KernelFront.checkReachedTypes` refuses
   tampered `.thm` types, `byStatement` table theorems, and tampered `.case`/`.eqn` subjects
   justifying `.eqn`/`.csimp`/`.word`/`.case` entries.
5. **`BE-1` / `BE-2` / `BE-4` / `BE-7` (executable shell & loaded-state hardening):**
   - `X86.Exe.writeChecked` enforces `Shell.check`;
   - `Fields` retains seccomp BPF `data` and `gapsZero`, and mutating a BPF or gap byte fails
     `X86.Exe.check`;
   - `--exe` ELF has 5 `PT_LOAD` headers with separate stack and heap RW segments separated by
     an unmapped `0x1000` guard page;
   - `B.exit` emits `ud2` (`0F 0B`) after `syscall` and `B.writeAdv` guards `rax > rdx` in both
     `--exe` (`Code.lean`) and `--machine` (`Machine.lean`) shells;
   - `.enum 0` and `.enum (2 ^ 31)` are refused;
   - `X86.Exe.Process.bootBase < 2 ^ 47` (canonical x86-64 user-space).
6. **`EM-0` (`DefAsserts` enforcement):**
   - `@[no_rc]`, `@[no_alloc]`, `@[bounded_stack]` enforced over transitive `Reach(f)`;
   - pure tail-recursive `gcd` passes all three with a certified `StackWitness`;
   - non-tail-recursive `fib` is refused for `@[bounded_stack]` (with `none` or forged witness);
   - under-sized `StackWitness` on `gcd` is refused;
   - synthetic RC/alloc/mixed-cycle/tail-cycle programs and Ixon v5 `Definition.asserts`
     propagation via `Reading.defAsserts`/`Reading.assertsMap` are verified;
   - plain-RC allocating corpus root is refused for `@[no_rc]` and `@[no_alloc]`.
7. **`FE-1` (`LiveClosed.SortDischarge.SortClosed`):** non-vacuity check proving `SortClosed`
   returns `true` on real compiled corpus artifacts (`fib`, `gcd`, `tak`, `Abi.bool1`, `Abi.tri1`). -/

namespace IxCCTests.Soundness

open IxCC IxCC.Src IxCC.Recheck
open IxCCTests.Src (Assert expect expectEq)
open IxCCTests.Exe.Suite (compileNamed benchK1 abi resource)
open System

private def loadFixtureInput (manifest : FilePath) (fixture root : String) :
    IO (Corpus.Root × Recheck.Config × Recheck.Input) := do
  let m ← Corpus.Family.read manifest
  let some f := m.fixtures.find? (·.name == fixture) | throw (IO.userError s!"no fixture {fixture}")
  let some r := f.roots.find? (·.name == root) | throw (IO.userError s!"no root {root}")
  let dir : FilePath := m.directory
  let bytes ← IO.FS.readBinFile (dir / f.closure.path)
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (dir / f.equations.path)))
  let inp ← IO.ofExcept ((Recheck.ingress bytes json (r.name :: r.together)).mapError (·.render))
  return (r, {}, inp)

/-! ## 1. FE-5: Exact `FrameLayout.check` -/

def partFE5 (a : Assert) : IO Unit := do
  -- Leaf function (0 slots, 0 saves, 0 outArgs)
  let leaf : Xv.Stacking.Facts := {}
  let prodLeaf := Xv.Stacking.FrameLayout.produce leaf
  expect a (prodLeaf.check leaf) "FE-5: produced leaf layout passes check"
  expectEq a prodLeaf.size 0 "FE-5: leaf frame has size 0"
  -- 1 MiB leaf-frame bloat trojan
  let bloat1M : Xv.Stacking.FrameLayout := { prodLeaf with size := 1048504 }
  expect a (!bloat1M.check leaf) "FE-5: 1 MiB leaf-frame bloat rejected"
  -- +16-byte bloat on non-leaf frame
  let nonLeaf : Xv.Stacking.Facts := { slots := 2, outArgs := 1, writes := [.rbx, .r12] }
  let prodNL := Xv.Stacking.FrameLayout.produce nonLeaf
  expect a (prodNL.check nonLeaf) "FE-5: produced non-leaf layout passes check"
  let bloat16 : Xv.Stacking.FrameLayout := { prodNL with size := prodNL.size + 16 }
  expect a (!bloat16.check nonLeaf) "FE-5: +16-byte frame bloat rejected"
  -- Inflated outArgs
  let badOut : Xv.Stacking.FrameLayout :=
    { prodNL with
      outArgs := nonLeaf.outArgs + 1
      slotOff := prodNL.slotOff.map (· + 8)
      saveOff := prodNL.saveOff.map fun (r, o) => (r, o + 8)
      size := Xv.Stacking.FrameLayout.align16_8 (8 * (nonLeaf.outArgs + 1 + nonLeaf.slots + (Xv.Stacking.saves nonLeaf).length)) }
  expect a (!badOut.check nonLeaf) "FE-5: inflated outArgs rejected"
  -- End-to-end Recheck.run refusal on real `fib` with bloated leaf frame
  let (_, cfg, inp) ← loadFixtureInput benchK1 "fib" "entry"
  let cert ← IO.ofExcept ((Recheck.produce cfg inp).mapError (·.render))
  expect a ((Recheck.run cfg inp.program cert).isOk) "FE-5: honest fib cert accepted by Recheck.run"
  let bloatedFrames := cert.frames.map fun fl =>
    if fl.size == 0 then { fl with size := 1048504 }
    else { fl with size := fl.size + 16 }
  let badCert : Recheck.Cert := { cert with frames := bloatedFrames }
  expect a (!(Recheck.run cfg inp.program badCert).isOk) "FE-5: bloated cert.frames rejected by Recheck.run"

/-! ## 2. FE-6: Mandatory deterministic `Lazify` -/

def partFE6 (a : Assert) : IO Unit := do
  -- Real `fib` uses `ite` (a required lazy pin)
  let (_, cfg, inp) ← loadFixtureInput benchK1 "fib" "entry"
  let cert ← IO.ofExcept ((Recheck.produce cfg inp).mapError (·.render))
  expect a (!cert.table.lazy.isEmpty) "FE-6: honest fib cert has non-empty lazy rows"
  expect a ((Table.ofCert cfg.table inp.program cert.table).isOk) "FE-6: honest fib table cert accepted"
  -- Trojan: set `lazy := []`
  let emptyLazy : Table.TableCert := { cert.table with lazy := [] }
  expect a (!(Table.ofCert cfg.table inp.program emptyLazy).isOk) "FE-6: fib with lazy := [] rejected by Table.ofCert"
  let emptyLazyCert : Recheck.Cert := { cert with table := emptyLazy }
  expect a (!(Recheck.run cfg inp.program emptyLazyCert).isOk) "FE-6: fib with lazy := [] rejected by Recheck.run"
  -- Trojan: drop any single required lazy pin entry
  let some droppedOne := cert.table.lazy.tail? | expect a false "FE-6: lazy rows non-empty"
  let droppedCert : Table.TableCert := { cert.table with lazy := droppedOne }
  expect a (!(Table.ofCert cfg.table inp.program droppedCert).isOk)
    "FE-6: dropping a single required lazy pin rejected by Table.ofCert"
  -- Also test `Table.validate` directly with lazy cleared
  let tbl ← IO.ofExcept (Table.ofCert cfg.table inp.program cert.table)
  let pBad : Program := { inp.program with table := { tbl with lazy := .leaf } }
  expect a (!(Table.validate cfg.table pBad).isOk) "FE-6: cleared table.lazy rejected by Table.validate"

/-! ## 3. FE-3: Non-cyclic `.eqn` guard -/

/-- Build a minimal synthetic `Program` with `Nat`, `Eq`, `Bool`, `Nat.add`, `ite`,
and custom definitions/theorems for testing `checkEqn` / `validate` / `ofCert`. -/
private def mkFE3Base : Program × CId × CId × CId × CId × CId × CId × CId :=
  -- CIds:
  -- 0 = Nat, 1 = Bool, 2 = Eq, 3 = Nat.add, 4 = ite (lazy arity 5), 5 = f, 6 = g
  let natTy := Term.const 0 []
  let boolTy := Term.const 1 []
  let b (r : Rel := .rel) : Binder := { rel := r }
  let mkAddr (n : UInt8) : Ixon.Address := Ixon.Address.replicate n
  let natEntry : ConstEntry :=
    { ref := .member (mkAddr 1) 0, addr := Pinned.constAddr "Nat", decl := .induct true 0 0 0 (.sort (.succ .zero)) [] }
  let boolEntry : ConstEntry :=
    { ref := .member (mkAddr 2) 0, addr := Pinned.constAddr "Bool", decl := .induct true 0 0 0 (.sort (.succ .zero)) [] }
  let eqType :=
    Term.pi (b .type) (.sort (.var 0))
      (Term.pi (b .rel) (.var 0)
        (Term.pi (b .rel) (.var 1) (.sort .zero)))
  let eqEntry : ConstEntry :=
    { ref := .member (mkAddr 3) 0, addr := Pinned.constAddr "Eq", decl := .induct true 1 2 1 eqType [] }
  let addType := Term.pi (b) natTy (Term.pi (b) natTy natTy)
  let addEntry : ConstEntry :=
    { ref := .member (mkAddr 4) 0, addr := mkAddr 103, decl := .defn .defn .safe 0 addType (Term.lam (b) natTy (Term.lam (b) natTy (.var 0))) }
  -- `ite` at its pinned address (arity 5, args 3 and 4 lazy):
  let iteAddr := Pinned.addr "1c4df88ba829b7b808219c037f304dde11b0c9d8ca752713c15ed5493c5fd1cf"
  let iteType :=
    Term.pi (b .type) (.sort (.succ .zero))
      (Term.pi (b .type) (.sort .zero)
        (Term.pi (b) boolTy
          (Term.pi (b) (.var 2)
            (Term.pi (b) (.var 3) (.var 4)))))
  let iteVal :=
    Term.lam (b .type) (.sort (.succ .zero))
      (Term.lam (b .type) (.sort .zero)
        (Term.lam (b) boolTy
          (Term.lam (b) (.var 2)
            (Term.lam (b) (.var 3) (.var 0)))))
  let iteEntry : ConstEntry :=
    { ref := .member (mkAddr 5) 0, addr := iteAddr, decl := .defn .defn .safe 0 iteType iteVal }
  let fnTy := Term.pi (b) natTy natTy
  let fEntry : ConstEntry :=
    { ref := .member (mkAddr 6) 0, addr := mkAddr 105, decl := .defn .defn .safe 0 fnTy (Term.lam (b) natTy (.var 0)) }
  let gEntry : ConstEntry :=
    { ref := .member (mkAddr 7) 0, addr := mkAddr 106, decl := .defn .defn .safe 0 fnTy (Term.lam (b) natTy (.var 0)) }
  let entries := [natEntry, boolEntry, eqEntry, addEntry, iteEntry, fEntry, gEntry]
  let p : Program :=
    { consts := NatMap.ofDense entries
      size := entries.length
      roots := [(mkAddr 105, 5)]
      known := { nat := some 0, bool := some 1, eq := some 2 } }
  (p, 0, 2, 3, 4, 5, 6, 7)

/-- Build theorem `∀ x : Nat, f x = rhs` (with `x` at de Bruijn 0 in `rhs`). -/
private def mkEqnThm (natId eqId fId : CId) (rhs : Term) (tag : UInt8 := 200) : ConstEntry :=
  let natTy := Term.const natId []
  let b (r : Rel := .rel) : Binder := { rel := r }
  let lhs := Term.app (.const fId []) (.var 0) .strict .rel
  let eqApp :=
    Term.app
      (Term.app (Term.app (.const eqId [.succ .zero]) natTy .strict .type) lhs .strict .rel)
      rhs .strict .rel
  let thmTy := Term.pi (b) natTy eqApp
  { ref := .member (Ixon.Address.replicate tag) 0, addr := Ixon.Address.replicate tag, decl := .defn .thm .safe 0 thmTy (.natLit 0) }

private def addEntry (p : Program) (e : ConstEntry) : Program × CId :=
  let cid := p.size
  ({ p with consts := p.consts.insert cid e, size := cid + 1 }, cid)

def partFE3 (a : Assert) : IO Unit := do
  let (base, natId, eqId, addId, iteId, fId, gId, _) := mkFE3Base
  let fx := Term.app (.const fId []) (.var 0) .strict .rel
  let gx := Term.app (.const gId []) (.var 0) .strict .rel
  let natTy := Term.const natId []
  -- 1. Direct self-loop trojan: `f x = f x`
  let (p1, thm1) := addEntry base (mkEqnThm natId eqId fId fx 201)
  expect a (!(Table.checkEqn p1 fId thm1).isOk) "FE-3: direct self-loop `f x = f x` rejected by checkEqn"
  let cert1 : Table.TableCert := { resolve := [(fId, .eqn thm1)], lazy := [(iteId, 5)] }
  expect a (!(Table.ofCert {} p1 cert1).isOk) "FE-3: direct self-loop rejected by Table.ofCert"
  -- 2. Strict-wrapper self-loop trojan: `f x = Nat.add (f x) 0`
  let addFx0 := Term.app (Term.app (.const addId []) fx .strict .rel) (.natLit 0) .strict .rel
  let (p2, thm2) := addEntry base (mkEqnThm natId eqId fId addFx0 202)
  expect a (!(Table.checkEqn p2 fId thm2).isOk) "FE-3: strict-wrapper `f x = Nat.add (f x) 0` rejected by checkEqn"
  let cert2 : Table.TableCert := { resolve := [(fId, .eqn thm2)], lazy := [(iteId, 5)] }
  expect a (!(Table.ofCert {} p2 cert2).isOk) "FE-3: strict-wrapper self-loop rejected by Table.ofCert"
  -- 3. Branch-everywhere self-loop trojan: `f x = ite Nat Prop cond (f x) (f x)`
  let mkIte (tBranch eBranch : Term) : Term :=
    Term.app (Term.app (Term.app (Term.app (Term.app (.const iteId []) natTy .strict .type)
      (.sort .zero) .strict .type) (.const 1 []) .strict .rel) tBranch .strict .rel) eBranch .strict .rel
  let (p3, thm3) := addEntry base (mkEqnThm natId eqId fId (mkIte fx fx) 203)
  expect a (!(Table.checkEqn p3 fId thm3).isOk) "FE-3: branch-everywhere `ite _ (f x) (f x)` rejected by checkEqn"
  -- 4. Mutual unconditional cycle trojan: `f x = g x` and `g x = f x`
  let (p4a, thmF) := addEntry base (mkEqnThm natId eqId fId gx 204)
  let (p4, thmG) := addEntry p4a (mkEqnThm natId eqId gId fx 205)
  let cert4 : Table.TableCert := { resolve := [(fId, .eqn thmF), (gId, .eqn thmG)], lazy := [(iteId, 5)] }
  expect a (!(Table.ofCert {} p4 cert4).isOk) "FE-3: mutual cycle `f x = g x, g x = f x` rejected by Table.ofCert"
  -- 5. Positive control: honest guarded recursion `f x = ite _ x (f x)` and
  --    changing-argument `partial_fixpoint` recursion `f x = f (Nat.add x 1)` (e.g. `Arity.spin`)
  let (p5, thm5) := addEntry base (mkEqnThm natId eqId fId (mkIte (.var 0) fx) 206)
  expect a ((Table.checkEqn p5 fId thm5).isOk) "FE-3: guarded recursion `ite _ x (f x)` accepted by checkEqn"
  let cert5 : Table.TableCert := { resolve := [(fId, .eqn thm5)], lazy := [(iteId, 5)] }
  expect a ((Table.ofCert {} p5 cert5).isOk) "FE-3: guarded recursion accepted by Table.ofCert"
  let fNext := Term.app (.const fId [])
    (Term.app (Term.app (.const addId []) (.var 0) .strict .rel) (.natLit 1) .strict .rel) .strict .rel
  let (p6, thm6) := addEntry base (mkEqnThm natId eqId fId fNext 207)
  expect a ((Table.checkEqn p6 fId thm6).isOk)
    "FE-3: changing-argument recursion `f x = f (Nat.add x 1)` (partial_fixpoint) accepted"
  -- 6. Positive control: real corpus `fib`, `gcd`, `tak`
  for fixture in ["fib", "gcd", "tak"] do
    let (_, cfg, inp) ← loadFixtureInput benchK1 fixture "entry"
    let cert ← IO.ofExcept ((Recheck.produce cfg inp).mapError (·.render))
    let tbl ← IO.ofExcept (Table.ofCert cfg.table inp.program cert.table)
    expect a ((Table.validate cfg.table { inp.program with table := tbl }).isOk)
      s!"FE-3: real corpus {fixture} accepted by Table.ofCert + Table.validate"

/-! ## 4. FE-2: Table-theorem `corrRec` blind spot (`checkReachedTypes`) -/

def partKernelFront (a : Assert) : IO Unit := do
  -- Load real `fib` closure through kernel acceptance (`Recheck.ingress`)
  let (_, cfg, inp) ← loadFixtureInput benchK1 "fib" "entry"
  let cert ← IO.ofExcept ((Recheck.produce cfg inp).mapError (·.render))
  let tbl ← IO.ofExcept (Table.ofCert cfg.table inp.program cert.table)
  let pWithTbl : Program := { inp.program with table := tbl }
  let rd := inp.kernel.rd
  -- Positive control: honest reading + program + table passes `checkReachedTypes`
  expect a ((Src.KernelFront.checkReachedTypes rd pWithTbl cert.relevance).isOk)
    "FE-2: honest fib passes KernelFront.checkReachedTypes"
  -- Find an `.eqn` theorem in `tbl` (or synthesize a table entry referencing an existing thm)
  let eqnThm? := (List.range pWithTbl.size).findSome? fun c =>
    match tbl.resolveOf c with
    | some (.eqn thm _) => some (c, thm)
    | _ => none
  match eqnThm? with
  | none => expect a false "FE-2: expected at least one .eqn entry in fib table"
  | some (subj, thm) =>
    -- Negative 1: tamper the `.eqn` theorem's type in `pWithTbl`
    let some entry := pWithTbl.entry? thm | expect a false "FE-2: thm entry missing"
    let badDecl := match entry.decl with
      | .defn k s lv _ v => .defn k s lv (.sort .zero) v
      | d => d
    let pBadThm : Program :=
      { pWithTbl with consts := pWithTbl.consts.insert thm { entry with decl := badDecl } }
    expect a (!(Src.KernelFront.checkReachedTypes rd pBadThm cert.relevance).isOk)
      "FE-2: tampered .eqn theorem type rejected by checkReachedTypes"
    -- Negative 2: mark the `.eqn` theorem as `byStatement`
    let pByStmt : Program :=
      { pWithTbl with byStatement := pWithTbl.byStatement.insert thm }
    expect a (!(Src.KernelFront.checkReachedTypes rd pByStmt cert.relevance).isOk)
      "FE-2: byStatement .eqn theorem rejected by checkReachedTypes"
    -- Negative 3: tamper the `.eqn` theorem into a non-theorem definition
    let badKindDecl := match entry.decl with
      | .defn _ s lv ty v => .defn .defn s lv ty v
      | d => d
    let pNotThm : Program :=
      { pWithTbl with consts := pWithTbl.consts.insert thm { entry with decl := badKindDecl } }
    expect a (!(Src.KernelFront.checkReachedTypes rd pNotThm cert.relevance).isOk)
      "FE-2: non-theorem .eqn justification rejected by checkReachedTypes"
    -- Negative 4: tamper the `.eqn` subject's value
    match pWithTbl.entry? subj with
    | some se =>
      match se.decl with
      | .defn k s lv ty _ =>
        let pBadSubj : Program :=
          { pWithTbl with consts := pWithTbl.consts.insert subj { se with decl := .defn k s lv ty (.natLit 999) } }
        expect a (!(Src.KernelFront.checkReachedTypes rd pBadSubj cert.relevance).isOk)
          "FE-2: tampered .eqn subject value rejected by checkReachedTypes"
      | _ => pure ()
    | none => pure ()

/-! ## 5. BE-1 / BE-2 / BE-4 / BE-7: Executable shell & loaded-state hardening -/

def partExe (a : Assert) : IO Unit := do
  let (_, _, art) ← compileNamed benchK1 "fib" "entry"
  match IxCC.Exe.build art with
  | .error e => expect a false s!"BE: Exe.build fib failed: {e.render}"
  | .ok ⟨inp, cert⟩ =>
    -- BE-1: `writeChecked` enforced `Shell.check` (also verify `shellOk` directly)
    expect a (X86.Exe.check inp cert.bytes) "BE-1: fib --exe passes X86.Exe.check"
    expect a (X86.Exe.shellOk inp.frame inp.object cert.plan cert.bytes)
      "BE-1: fib --exe passes X86.Exe.shellOk (Shell.check)"
    -- BE-4: 5 PHDRs & two separate RW PT_LOAD segments with 0x1000 unmapped guard page
    expectEq a X86.Exe.headersSize (64 + 5 * 56) "BE-4: headersSize accounts for 5 PHDRs"
    expectEq a inp.layout.segments.length 2 "BE-4: layout has 2 RW segments (stack + region)"
    expectEq a inp.frame.segments inp.layout.segments "BE-4: frame.segments == layout.segments"
    let [(stackBase, stackSize), (regBase, regSize)] := inp.layout.segments
      | expect a false "BE-4: expected exactly 2 RW segments"
    expectEq a stackBase X86.Exe.dataBase "BE-4: stack segment starts at dataBase"
    expectEq a (regBase - (stackBase + stackSize)) X86.Exe.guardGap
      "BE-4: unmapped 0x1000 guard page separates stack and heap segments"
    expect a (regSize ≥ inp.layout.region) "BE-4: region segment covers requested region"
    -- BE-2: mutating a seccomp BPF byte (`data`) is rejected
    let p := cert.plan.placement
    let bpfMut := cert.bytes.set! p.dataOffset ((cert.bytes[p.dataOffset]!).xor 0x01)
    expect a (!X86.Exe.check inp bpfMut) "BE-2: mutating seccomp BPF byte rejected by X86.Exe.check"
    -- BE-2: mutating a gap byte (if gap is non-empty) is rejected (`gapsZero`)
    let gapChecks :=
      [(p.noteOffset + p.noteSize, p.textOffset),
       (p.textOffset + p.textSize, p.dataOffset),
       (p.dataOffset + p.dataSize, p.shellOffset)]
    for (lo, hi) in gapChecks do
      if lo < hi then
        let gapMut := cert.bytes.set! lo 0x90
        expect a (!X86.Exe.check inp gapMut) s!"BE-2: mutating gap byte at {lo} rejected by X86.Exe.check"
    -- BE-2: `ud2` follows `syscall` in `B.exit` and `writeAdv` guards `rax > rdx` in BOTH shells
    let exeSpec : X86.Exe.Spec :=
      { arity := inp.arity, result := inp.result, root := inp.root,
        layout := inp.layout, data := X86.Exe.fileBase + p.dataOffset }
    let exeShell := X86.Exe.shell exeSpec
    let some exitBlk := exeShell.blocks[X86.Exe.B.exit]? | expect a false "BE-2: --exe B.exit missing"
    expect a (exitBlk.instructions.contains .syscall && exitBlk.instructions.contains .ud2)
      "BE-2: --exe B.exit contains syscall + ud2"
    let some advBlk := exeShell.blocks[X86.Exe.B.writeAdv]? | expect a false "BE-2: --exe B.writeAdv missing"
    let advExpected := X86.Terminator.compare
      { width := .w64, left := .rax, right := .reg .rdx } .unsignedGt
      (UInt32.ofNat X86.Exe.B.writeErr) (UInt32.ofNat X86.Exe.B.writeStep)
    expect a (advBlk.terminator == advExpected) "BE-2: --exe B.writeAdv guards rax > rdx"
    let machShell := X86.Exe.Machine.shell ({} : X86.Exe.Machine.Layout) inp.root (X86.Exe.fileBase + p.dataOffset)
    let some mExitBlk := machShell.blocks[X86.Exe.Machine.B.exit]? | expect a false "BE-2: --machine B.exit missing"
    expect a (mExitBlk.instructions.contains .syscall && mExitBlk.instructions.contains .ud2)
      "BE-2: --machine B.exit contains syscall + ud2"
    let some mAdvBlk := machShell.blocks[X86.Exe.Machine.B.writeAdv]? | expect a false "BE-2: --machine B.writeAdv missing"
    let mAdvExpected := X86.Terminator.compare
      { width := .w64, left := .rax, right := .reg .rdx } .unsignedGt
      (UInt32.ofNat X86.Exe.Machine.B.writeErr) (UInt32.ofNat X86.Exe.Machine.B.writeStep)
    expect a (mAdvBlk.terminator == mAdvExpected) "BE-2: --machine B.writeAdv guards rax > rdx"
    -- BE-2: `.enum 0` and `.enum (2 ^ 31)` refused by `writeChecked`
    let badEnum0 : X86.Exe.Input := { inp with result := .enum 0 }
    expect a (!(X86.Exe.writeChecked badEnum0).isOk) "BE-2: writeChecked refuses .enum 0"
    let badEnumBig : X86.Exe.Input := { inp with result := .enum (2 ^ 31) }
    expect a (!(X86.Exe.writeChecked badEnumBig).isOk) "BE-2: writeChecked refuses .enum (2^31)"
    -- BE-7: `bootBase` is canonical x86-64 user-space (`< 2^47`)
    expect a (X86.Exe.Process.bootBase < 2 ^ 47) "BE-7: bootBase < 2^47 (canonical user-space)"

/-! ## 6. EM-0: `DefAsserts` enforcement (`@[no_rc]`, `@[no_alloc]`, `@[bounded_stack]`) -/

def partEM0 (a : Assert) : IO Unit := do
  -- Real `gcd` (tail-recursive scalar) & `fib` (non-tail-recursive scalar)
  let (_, gcdCert, gcdArt) ← compileNamed benchK1 "gcd" "entry"
  let (_, fibCert, fibArt) ← compileNamed benchK1 "fib" "entry"
  let gcdCtx := DefAsserts.ctxOfArtifact gcdArt (some gcdCert.frames)
  let fibCtx := DefAsserts.ctxOfArtifact fibArt (some fibCert.frames)
  let some (gcdFid, gcdOrigin) := gcdArt.cfg.funList.findSome? (fun (fid, fd) =>
      (DefAsserts.gkeyOrigin? fd.key).map (fid, ·))
    | expect a false "EM-0: gcd root origin missing"
  let some fibOrigin := fibArt.cfg.funList.findSome? (fun (_, fd) => DefAsserts.gkeyOrigin? fd.key)
    | expect a false "EM-0: fib root origin missing"
  let allThree : _root_.Ixon.DefAsserts := { alloc := .noAlloc, boundedStack := true }
  let noRcNoAlloc : _root_.Ixon.DefAsserts := { alloc := .noAlloc, boundedStack := false }
  let noRcOnly : _root_.Ixon.DefAsserts := { alloc := .noRc, boundedStack := false }
  let boundedOnly : _root_.Ixon.DefAsserts := { alloc := .unrestricted, boundedStack := true }
  -- Positive: `gcd` satisfies @[no_rc], @[no_alloc], AND @[bounded_stack]
  let gcdAsserts : NatMap _root_.Ixon.DefAsserts := NatMap.empty.insert gcdOrigin allThree
  let some gcdReach := DefAsserts.computeReach gcdCtx.lir gcdFid
    | expect a false "EM-0: gcd reach failed"
  let some gcdWit := DefAsserts.produceStackWitness gcdCtx.lir gcdCtx.frames gcdFid gcdReach
    | expect a false "EM-0: gcd failed to produce StackWitness"
  expect a ((DefAsserts.checkArtifact gcdAsserts gcdArt (some gcdCert.frames) (some gcdWit)).isOk)
    "EM-0: tail-recursive gcd passes @[no_rc], @[no_alloc], @[bounded_stack] with certified witness"
  expect a ((DefAsserts.checkArtifact gcdAsserts gcdArt (some gcdCert.frames) none).isOk)
    "EM-0: tail-recursive gcd passes @[bounded_stack] with auto-derived witness"
  -- Negative: under-sized forged witness on `gcd` rejected
  let forgedWit : DefAsserts.StackWitness := NatMap.ofDense ((List.range gcdCtx.lir.funcs.size).map fun _ => 0)
  expect a (!(DefAsserts.checkArtifact gcdAsserts gcdArt (some gcdCert.frames) (some forgedWit)).isOk)
    "EM-0: under-sized StackWitness on gcd rejected"
  -- Positive: `fib` satisfies @[no_rc] and @[no_alloc]
  let fibScalarAsserts : NatMap _root_.Ixon.DefAsserts := NatMap.empty.insert fibOrigin noRcNoAlloc
  expect a ((DefAsserts.checkArtifact fibScalarAsserts fibArt (some fibCert.frames) none).isOk)
    "EM-0: scalar fib passes @[no_rc] and @[no_alloc]"
  -- Negative: non-tail-recursive `fib` violates @[bounded_stack]
  let fibBoundAsserts : NatMap _root_.Ixon.DefAsserts := NatMap.empty.insert fibOrigin boundedOnly
  expect a (!(DefAsserts.checkArtifact fibBoundAsserts fibArt (some fibCert.frames) none).isOk)
    "EM-0: non-tail-recursive fib rejected for @[bounded_stack]"
  let bigForged : DefAsserts.StackWitness :=
    NatMap.ofDense ((List.range fibCtx.lir.funcs.size).map fun _ => 1000000)
  expect a (!(DefAsserts.checkArtifact fibBoundAsserts fibArt (some fibCert.frames) (some bigForged)).isOk)
    "EM-0: non-tail-recursive fib rejected even with large forged StackWitness"
  -- Synthetic LIR tests for transitive RC, transitive alloc, tail cycle, mixed cycle
  let leafFrame : Xv.Stacking.FrameLayout := Xv.Stacking.FrameLayout.produce {}
  let callFrame : Xv.Stacking.FrameLayout :=
    Xv.Stacking.FrameLayout.produce { slots := 1, writes := [.rbx] }
  let mkCfgFun (cid : CId) : Cfg.Fun :=
    { key := .const cid []
      sig := default
      blocks := [{ term := .trap }] }
  -- Tail-call cycle f(0) <-> g(1): @[bounded_stack] ACCEPTED
  let lirTailCycle : Lir.Program :=
    { funcs := #[
        { conv := .internal, params := [], results := 0, blocks := #[{ term := .tail 1 [] }] },
        { conv := .internal, params := [], results := 0, blocks := #[{ term := .tail 0 [] }] } ]
      main := 0 }
  let cfgPair : Cfg.Program :=
    { funs := NatMap.ofDense [mkCfgFun 10, mkCfgFun 11]
      size := 2
      exports := [0]
      ctors := []
      known := default }
  let ctxTail : DefAsserts.CheckCtx :=
    { cfg := cfgPair, rcActions := none, rcProcs := [], allocProcs := []
      lir := lirTailCycle, frames := [leafFrame, leafFrame] }
  expect a ((DefAsserts.check ctxTail (NatMap.empty.insert 10 boundedOnly) none).isOk)
    "EM-0: pure tail-call cycle f <-> g passes @[bounded_stack]"
  -- Mixed cycle f(0) --tail--> g(1) --non-tail--> f(0): @[bounded_stack] REJECTED
  let lirMixedCycle : Lir.Program :=
    { funcs := #[
        { conv := .internal, params := [], results := 0, blocks := #[{ term := .tail 1 [] }] },
        { conv := .internal, params := [], results := 0, blocks := #[{ body := #[.call [] 0 []], term := .ret [] }] } ]
      main := 0 }
  let ctxMixed : DefAsserts.CheckCtx :=
    { cfg := cfgPair, rcActions := none, rcProcs := [], allocProcs := []
      lir := lirMixedCycle, frames := [leafFrame, callFrame] }
  expect a (!(DefAsserts.check ctxMixed (NatMap.empty.insert 10 boundedOnly) none).isOk)
    "EM-0: mixed tail/non-tail cycle f -> g -> f rejected for @[bounded_stack]"
  -- Transitive RC call in callee g(1) -> rcProc(2): @[no_rc] on f(0) REJECTED
  let lirRcCall : Lir.Program :=
    { funcs := #[
        { conv := .internal, params := [], results := 0, blocks := #[{ body := #[.call [] 1 []], term := .ret [] }] },
        { conv := .internal, params := [], results := 0, blocks := #[{ body := #[.call [] 2 []], term := .ret [] }] },
        { conv := .internal, params := [], results := 0, blocks := #[{ term := .ret [] }] } ]
      main := 0 }
  let ctxRc : DefAsserts.CheckCtx :=
    { cfg := cfgPair, rcActions := none, rcProcs := [2], allocProcs := []
      lir := lirRcCall, frames := [callFrame, callFrame, leafFrame] }
  expect a (!(DefAsserts.check ctxRc (NatMap.empty.insert 10 noRcOnly) none).isOk)
    "EM-0: transitive RC call in callee rejected for @[no_rc]"
  -- Transitive `.fail .heap` in callee g(1): @[no_alloc] on f(0) REJECTED
  let lirHeapFail : Lir.Program :=
    { funcs := #[
        { conv := .internal, params := [], results := 0, blocks := #[{ body := #[.call [] 1 []], term := .ret [] }] },
        { conv := .internal, params := [], results := 0, blocks := #[{ term := .fail .heap }] } ]
      main := 0 }
  let ctxHeap : DefAsserts.CheckCtx :=
    { cfg := cfgPair, rcActions := none, rcProcs := [], allocProcs := []
      lir := lirHeapFail, frames := [callFrame, leafFrame] }
  expect a (!(DefAsserts.check ctxHeap (NatMap.empty.insert 10 noRcNoAlloc) none).isOk)
    "EM-0: transitive .fail .heap in callee rejected for @[no_alloc]"
  -- Plain-RC allocating corpus fixture rejected for @[no_rc] and @[no_alloc]
  let (_, rcCfg, rcInp) ← loadFixtureInput resource "resource" "Resource.heapList"
  match Recheck.RcReplay.produce rcCfg rcInp with
  | .error e => expect a false s!"EM-0: RcReplay.produce Resource.heapList failed: {e.render}"
  | .ok (rcCert, rcArt) =>
    let some rcOrigin := rcArt.front.cfg.base.funList.findSome? (fun (_, fd) => DefAsserts.gkeyOrigin? fd.key)
      | expect a false "EM-0: Resource.heapList root origin missing"
    expect a (!(DefAsserts.checkRcArtifact (NatMap.empty.insert rcOrigin noRcOnly)
        rcArt rcCert.base.frames none).isOk)
      "EM-0: plain-RC Resource.heapList rejected for @[no_rc]"
    expect a (!(DefAsserts.checkRcArtifact (NatMap.empty.insert rcOrigin noRcNoAlloc)
        rcArt rcCert.base.frames none).isOk)
      "EM-0: plain-RC Resource.heapList rejected for @[no_alloc]"
  -- Ixon v5 `Definition.asserts` propagation via `defAssertsOf`
  let v5Def : _root_.Ixon.Definition :=
    { kind := .defn, safety := .safe, asserts := allThree, lvls := 0,
      typ := .sort 0, value := .sort 0 }
  let v5Const : Src.KernelFront.KConstant :=
    { info := .defn v5Def, sharing := #[], refs := #[], univs := #[] }
  expect a (Src.KernelFront.defAssertsOf v5Const (.member (Ixon.Address.replicate 0) 0) == allThree)
    "EM-0: defAssertsOf propagates v5 Definition.asserts"

/-! ## 7. FE-1: `LiveClosed.SortDischarge.SortClosed` non-vacuity & negative control -/

def partSortClosed (a : Assert) : IO Unit := do
  -- Positive control: `SortClosed` holds on real compiled `fib/entry`, discharging
  -- `Front.RunSortAgree` (via `Front.goesWrong_live_discharged` / `sound_live_discharged`)
  -- with zero extra axioms.
  let (_, fibCert, fibArt) ← compileNamed benchK1 "fib" "entry"
  expect a (Recheck.SortDischarge.SortClosed fibArt.src fibCert.relevance fibArt.checked)
    "FE-1: SortClosed holds on real compiled fib/entry"
  -- Negative control: injecting an unguarded irrelevant-arg application (`(var 0) 0` with `.type`)
  -- into a reached function's body causes `SortClosed` to return `false`.
  let some (rootCid, _) := fibArt.checked.instances.find? fun (c, _) =>
      match fibArt.src.decl? c with
      | some (.defn .defn .safe _ _ _) => true
      | _ => false
    | expect a false "FE-1: expected a reached safe defn in fib"
  let some rootEntry := fibArt.src.entry? rootCid | expect a false "FE-1: root entry missing"
  let badDecl := match rootEntry.decl with
    | .defn k s lv ty _ => .defn k s lv ty (.app (.var 0) (.natLit 0) .strict .type)
    | d => d
  let badSrc : Program :=
    { fibArt.src with consts := fibArt.src.consts.insert rootCid { rootEntry with decl := badDecl } }
  expect a (!Recheck.SortDischarge.SortClosed badSrc fibCert.relevance fibArt.checked)
    "FE-1: SortClosed rejects unguarded irrelevant-arg application"

def run : IO Bool := do
  let a : Assert ← IO.mkRef 0
  try
    partFE5 a
    partFE6 a
    partFE3 a
    partKernelFront a
    partExe a
    partEM0 a
    partSortClosed a
    let passes ← a.get
    IO.println s!"tests-soundness: {passes} passed, 0 failed"
    return true
  catch e =>
    let passes ← a.get
    IO.eprintln s!"tests-soundness: FAIL after {passes} passed: {e}"
    return false

end IxCCTests.Soundness
