import IxCC.Lir.Opt.Driver
import IxCC.Lir.Print
import IxCC.Backend
import IxCCTests.Lir.Gen
import IxCCTests.Lir.Props
import IxCCTests.Lir.Kernels
import IxCCTests.Pipeline.Support
import IxCCTests.Rt.Cases

/-!
# Comprehensive test, negative-control, fuzz, and K1/K2/K3 benchmark suite for `Lir.Opt`

Exercises:
1. **Unit tests** for every pass: algebraic simplification (w8–w64), GVN/CSE,
   copy & constant propagation, DCE, dominating branch/interval/brOvf folding,
   natural-loop LICM (invariant param sub, single-entry & multi-entry preheaders,
   pure hoisting, invariant `.fail`-guard hoisting), constant unsigned division/modulo
   strength reduction (power-of-2 + 64-bit & 32-bit Granlund–Montgomery Case 1 & Case 2,
   including `10` and `10^19`), store-to-load forwarding, load CSE across disjoint stores,
   and intra-block DSE.
2. **Negative-control mutant tests** verifying `Lir.Opt.check` rejects 15 unsound mutants.
3. **`Lir.Gen` property-based fuzz tests** verifying `check`, `wellFormed`, and full
   `Lir.eval` (values + heap + ctx memory) parity across generated SSA programs.
4. **K1 (`fib`, `sum-loop`, `gcd`, `collatz`, `prime-count`, `sfib`, `ackermann`, `tak`,
   `even-odd`) & K2/K3 (heap-allocating list/tree & `BigNat`/div-10) before-vs-after
   measurements** on typed x86 and `ByteEval` machines via `Backend.compileOpt`.
-/

namespace IxCCTests.Lir.Opt

open IxCC IxCC.Lir IxCC.Lir.Opt
open IxCCTests.Lir.Props (digest Digest)

/-! ## Test helpers -/

private def mkProg (f : Func) : Program := { funcs := #[f], main := 0 }

private def mkFunc (params : List VReg) (results : Nat) (blocks : Array Block)
    (name : String := "f") : Func :=
  { name, params, results, blocks }

private def countStmts (p : Program) : Nat :=
  p.funcs.foldl (fun acc f => f.blocks.foldl (fun a b => a + b.body.size) acc) 0

private def countBlocks (p : Program) : Nat :=
  p.funcs.foldl (fun acc f => acc + f.blocks.size) 0

private def hasDivRem (p : Program) : Bool :=
  p.funcs.any fun f => f.blocks.any fun b => b.body.any fun
    | .assign _ (.bin .udiv ..) | .assign _ (.bin .urem ..) => true
    | _ => false

private def flatMem : X86.Memory := IxCCTests.Lir.Region.initial 0

private def testCtx : Word := IxCCTests.Lir.Region.ctx

private def evalEqual (p q : Program) (argss : List (List Word)) (clock : Nat := 2000) :
    Except String Unit := do
  for args in argss do
    let d1 := digest (Lir.eval p clock args flatMem testCtx)
    let d2 := digest (Lir.eval q clock args flatMem testCtx)
    unless d1 == d2 do
      throw s!"eval mismatch on args {args.map (·.toNat)}: orig={repr d1}, opt={repr d2}"

private def expectOk (label : String) (p : Program) (argss : List (List Word))
    (extraCheck : Program → Except String Unit := fun _ => .ok ()) : IO Unit := do
  match p.check with
  | .error e => throw (IO.userError s!"[{label}] source not wellFormed: {e}")
  | .ok () => pure ()
  let q := Lir.Opt.run p
  unless q.wellFormed do
    throw (IO.userError s!"[{label}] optimized program failed wellFormed: {q.check}")
  unless Lir.Opt.check p q do
    throw (IO.userError s!"[{label}] Lir.Opt.check rejected Lir.Opt.run output")
  match Lir.Opt.validateCert p q with
  | .error e => throw (IO.userError s!"[{label}] validateCert failed: {e}")
  | .ok _ => pure ()
  match evalEqual p q argss with
  | .error e => throw (IO.userError s!"[{label}] {e}")
  | .ok () => pure ()
  match extraCheck q with
  | .error e => throw (IO.userError s!"[{label}] property check failed: {e}")
  | .ok () => pure ()

private def expectRejected (label : String) (p mutant : Program) : IO Unit := do
  if Lir.Opt.check p mutant then
    throw (IO.userError s!"[NEGATIVE CONTROL FAILED: {label}] Lir.Opt.check ACCEPTED unsound mutant!")

/-! ## 1. Unit tests covering every optimization -/

/-- Algebraic simplification + GVN/CSE + copy prop + DCE + narrow-width safety. -/
def unitAlgGvn : IO Unit := do
  -- 1a. w64 algebraic identities + commutative GVN + copy prop + DCE
  let p1 := mkProg <| mkFunc [0, 1] 1 #[
    { params := []
      body := #[
        .assign 2 (.bin .add .w64 (.v 0) (.imm 0)),        -- v2 = v0
        .assign 3 (.bin .mul .w64 (.v 2) (.imm 1)),        -- v3 = v0
        .assign 4 (.bin .mul .w64 (.v 3) (.imm 8)),        -- v4 = v0 << 3
        .assign 5 (.bin .sub .w64 (.v 1) (.v 1)),          -- v5 = 0
        .assign 6 (.bin .and .w64 (.v 4) (.v 4)),          -- v6 = v4
        .assign 7 (.bin .add .w64 (.v 6) (.v 1)),          -- v7 = v4 + v1
        .assign 8 (.bin .add .w64 (.v 1) (.v 4)),          -- duplicate (commuted) -> CSE to v7!
        .assign 9 (.bin .xor .w64 (.v 7) (.v 8)),          -- v7 ^ v7 = 0
        .assign 10 (.bin .or .w64 (.v 7) (.v 5)),          -- v7 | 0 = v7
        .assign 11 (.bin .add .w64 (.v 10) (.v 9))         -- v7 + 0 = v7
      ]
      term := .ret [.v 11] }
  ]
  expectOk "alg+gvn+dce" p1
    [[0, 0], [1, 2], [7, 19], [0x123456789abcdef, 0xfedcba9876543210], [0xffffffffffffffff, 1]]
    fun q => do
      let n := countStmts q
      -- Should shrink from 10 stmts down to 2 (`shl` + `add`)!
      unless n ≤ 3 do throw s!"expected ≤ 3 stmts after alg+gvn+dce, got {n}"

  -- 1b. Narrow-width truncation safety: `add.32 v0, 0` MUST keep zero-extension of low 32 bits!
  let pNarrow := mkProg <| mkFunc [0] 1 #[
    { params := []
      body := #[.assign 1 (.bin .add .w32 (.v 0) (.imm 0))]
      term := .ret [.v 1] }
  ]
  expectOk "narrow-w32-preserve" pNarrow
    [[0], [1], [0xffffffff], [0x100000000], [0xdeadbeef12345678]]

  -- 1c. Dominating branch folding (`gcd` duplicate check + `sfib` unsigned interval)
  let pBranch := mkProg <| mkFunc [0] 1 #[
    -- b0: if 100 <= v0 then b3 else b1  (so on b1: v0 < 100)
    { params := [], body := #[], term := .br .ule .w64 (.imm 100) (.v 0) ⟨3, []⟩ ⟨1, []⟩ },
    -- b1: if v0 > 200 then b4 else b2  (redundant! interval proves false -> jump b2)
    { params := [], body := #[], term := .br .ugt .w64 (.v 0) (.imm 200) ⟨4, []⟩ ⟨2, []⟩ },
    { params := [], body := #[], term := .ret [.v 0] },
    { params := [], body := #[], term := .ret [.imm 100] },
    { params := [], body := #[], term := .ret [.imm 999] }
  ]
  expectOk "interval-branch-fold" pBranch [[0], [50], [99], [100], [201], [0xffffffffffffffff]]
    fun q => do
      unless countBlocks q == 4 do
        throw s!"expected b4 pruned and 4 blocks left (b0..b3), got {countBlocks q}"

  -- 1d. Non-overflowing `brOvf` folding (`collatz`-style `addr [v0 + v0*2 - 2]` + `addC 2`)
  let pCollatz := mkProg <| mkFunc [0] 1 #[
    -- b0: if v0 < 4 then b3 else b1
    { params := [], body := #[], term := .br .ult .w64 (.v 0) (.imm 4) ⟨3, []⟩ ⟨1, []⟩ },
    -- b1: if v0 > 0x5555555555555555 then b4 else b2
    { params := [], body := #[], term := .br .ugt .w64 (.v 0) (.imm 0x5555555555555555) ⟨4, []⟩ ⟨2, []⟩ },
    -- b2: v1 = addr [v0 + v0*2 - 2]; brOvf addC v2 = v1, 2 -> b5, b6
    { params := []
      body := #[.assign 1 (.addr { base := some (.v 0), index := some (0, .two), disp := -2 })]
      term := .brOvf .addC 2 (.v 1) (.imm 2) ⟨5, []⟩ ⟨6, []⟩ },
    { params := [], body := #[], term := .ret [.imm 0] },
    { params := [], body := #[], term := .fail .natOverflow },
    { params := [], body := #[], term := .ret [.v 2] },
    { params := [], body := #[], term := .fail .natOverflow }
  ]
  expectOk "collatz-brovf-fold" pCollatz
    [[0], [3], [4], [27], [1000], [0x5555555555555555], [0x5555555555555556]]
    fun q => do
      let hasBrOvf := q.funcs[0]!.blocks.any fun b => match b.term with | .brOvf .. => true | _ => false
      if hasBrOvf then throw "expected brOvf to be folded away!"

/-- LICM: invariant block-param substitution, pure hoisting, multi-entry preheader, fail-guard hoisting. -/
def unitLicm : IO Unit := do
  -- 2a. Single-entry loop with invariant block param & hoistable `shr` (`prime-count` pattern)
  let pLicm1 := mkProg <| mkFunc [0, 1] 1 #[
    -- b0 (preheader): jump b1(v0, v1, 0)
    { params := [], body := #[], term := .jump ⟨1, [.v 0, .v 1, .imm 0]⟩ },
    -- b1 (header): params (v2=inv v0, v3=counter, v4=acc)
    { params := [2, 3, 4], body := #[], term := .br .eq .w64 (.v 3) (.imm 0) ⟨3, []⟩ ⟨2, []⟩ },
    -- b2 (body): v5 = shr v2 1 (LOOP INVARIANT after v2 -> v0!); acc += v5; counter -= 1; jump b1(v2, counter, acc)
    { params := []
      body := #[
        .assign 5 (.bin .shr .w64 (.v 2) (.imm 1)),
        .assign 6 (.bin .add .w64 (.v 4) (.v 5)),
        .assign 7 (.bin .sub .w64 (.v 3) (.imm 1))
      ]
      term := .jump ⟨1, [.v 2, .v 7, .v 6]⟩ },
    -- b3 (exit): ret v4
    { params := [], body := #[], term := .ret [.v 4] }
  ]
  expectOk "licm-inv-param-hoist" pLicm1 [[100, 0], [100, 5], [777, 20]]
    fun q => do
      -- `shr` should be hoisted into block 0 (`b0.body.size ≥ 1`)!
      let b0sz := q.funcs[0]!.blocks[0]!.body.size
      unless b0sz ≥ 1 do throw s!"expected hoisted stmt in preheader b0, got size {b0sz}"

  -- 2b. Multi-entry loop requiring inserted preheader
  let pMulti := mkProg <| mkFunc [0, 1] 1 #[
    { params := [], body := #[], term := .br .eq .w64 (.v 0) (.imm 0) ⟨1, []⟩ ⟨2, []⟩ },
    { params := [], body := #[], term := .jump ⟨3, [.v 1, .imm 0]⟩ },
    { params := [], body := #[], term := .jump ⟨3, [.v 1, .imm 10]⟩ },
    -- b3 (loop header with 2 outside entries b1, b2 + back-edge b4)
    { params := [2, 3], body := #[], term := .br .eq .w64 (.v 2) (.imm 0) ⟨5, []⟩ ⟨4, []⟩ },
    { params := []
      body := #[
        .assign 4 (.bin .mul .w64 (.v 0) (.imm 3)), -- loop-invariant (v0 dominates both entries!)
        .assign 5 (.bin .add .w64 (.v 3) (.v 4)),
        .assign 6 (.bin .sub .w64 (.v 2) (.imm 1))
      ]
      term := .jump ⟨3, [.v 6, .v 5]⟩ },
    { params := [], body := #[], term := .ret [.v 3] }
  ]
  expectOk "licm-multi-entry-preheader" pMulti [[0, 4], [5, 0], [5, 7]]
    fun q => do
      -- Preheader inserted before header so loop body shrunk!
      unless q.funcs[0]!.blocks.size ≥ 7 do
        throw s!"expected inserted preheader (≥ 7 blocks), got {q.funcs[0]!.blocks.size}"

  -- 2c. Invariant `.fail` guard hoisting (with trampoline hop, zero critical edges!)
  let pGuard := mkProg <| mkFunc [0, 1] 1 #[
    -- b0 (preheader): jump b1(v1, 0)
    { params := [], body := #[], term := .jump ⟨1, [.v 1, .imm 0]⟩ },
    -- b1 (header): unconditional invariant guard `v0 > 1000 -> fail natOverflow`
    { params := [2, 3], body := #[], term := .br .ugt .w64 (.v 0) (.imm 1000) ⟨4, []⟩ ⟨2, []⟩ },
    -- b2: loop exit check
    { params := [], body := #[], term := .br .eq .w64 (.v 2) (.imm 0) ⟨5, []⟩ ⟨3, []⟩ },
    -- b3: body
    { params := []
      body := #[
        .assign 4 (.bin .add .w64 (.v 3) (.v 0)),
        .assign 5 (.bin .sub .w64 (.v 2) (.imm 1))
      ]
      term := .jump ⟨1, [.v 5, .v 4]⟩ },
    { params := [], body := #[], term := .fail .natOverflow },
    { params := [], body := #[], term := .ret [.v 3] }
  ]
  expectOk "licm-fail-guard-hoist" pGuard [[10, 0], [10, 5], [1000, 3], [1001, 0], [1001, 5]]
    fun q => do
      -- Block 0 should now carry the hoisted `.br` guard!
      match q.funcs[0]!.blocks[0]!.term with
      | .br .. => pure ()
      | t => throw s!"expected hoisted .br guard in preheader b0, got {repr t}"

/-- Constant unsigned division & modulo strength reduction (pow2 + 64-bit & 32-bit magic). -/
def unitDivMagic : IO Unit := do
  let edgeWords (d : Word) : List (List Word) :=
    [[0], [1], [2], [d - 1], [d], [d + 1], [100], [0xffffffff], [0x100000000],
     [0x7fffffffffffffff], [0x8000000000000000], [0xfffffffffffffffe], [0xffffffffffffffff]]
  -- 3a. 64-bit powers of 2
  for d in ([2, 8, 64, 0x8000000000000000] : List Word) do
    let p := mkProg <| mkFunc [0] 2 #[
      { params := []
        body := #[
          .assign 1 (.bin .udiv .w64 (.v 0) (.imm d)),
          .assign 2 (.bin .urem .w64 (.v 0) (.imm d))
        ]
        term := .ret [.v 1, .v 2] }
    ]
    expectOk s!"div-pow2-w64-{d.toNat}" p (edgeWords d) fun q => do
      if hasDivRem q then throw s!"udiv/urem by {d.toNat} was not reduced!"

  -- 3b. 64-bit Granlund–Montgomery Case 1 (`3`, `5`, `10`, `10^19`) & Case 2 (`7`, `13`, `2^64-1`)
  for d in ([3, 5, 7, 10, 13, 100, 1000000007, 10000000000000000000, 0xffffffffffffffff] : List Word) do
    let p := mkProg <| mkFunc [0] 2 #[
      { params := []
        body := #[
          .assign 1 (.bin .udiv .w64 (.v 0) (.imm d)),
          .assign 2 (.bin .urem .w64 (.v 0) (.imm d))
        ]
        term := .ret [.v 1, .v 2] }
    ]
    expectOk s!"div-magic-w64-{d.toNat}" p (edgeWords d) fun q => do
      if hasDivRem q then throw s!"w64 udiv/urem by {d.toNat} was not strength-reduced!"

  -- 3c. 32-bit Granlund–Montgomery (`3`, `7`, `10`, `1000000007`) with dirty upper 32 bits!
  for d in ([3, 7, 10, 1000000007] : List Word) do
    let p := mkProg <| mkFunc [0] 2 #[
      { params := []
        body := #[
          .assign 1 (.bin .udiv .w32 (.v 0) (.imm d)),
          .assign 2 (.bin .urem .w32 (.v 0) (.imm d))
        ]
        term := .ret [.v 1, .v 2] }
    ]
    expectOk s!"div-magic-w32-{d.toNat}" p
      [[0], [1], [d - 1], [d], [d + 1], [0xffffffff], [0xdeadbeef00000000 + d], [0xffffffffffffffff]]
      fun q => do
        if hasDivRem q then throw s!"w32 udiv/urem by {d.toNat} was not strength-reduced!"

  -- 3d. Narrow widths (w8, w16) power-of-2 reduction
  let pSmall := mkProg <| mkFunc [0] 2 #[
    { params := []
      body := #[
        .assign 1 (.bin .udiv .w8 (.v 0) (.imm 8)),
        .assign 2 (.bin .urem .w16 (.v 0) (.imm 16))
      ]
      term := .ret [.v 1, .v 2] }
  ]
  expectOk "div-pow2-w8-w16" pSmall [[0], [7], [8], [255], [0xdeadbeef]] fun q => do
    if hasDivRem q then throw "w8/w16 pow2 udiv/urem was not reduced!"

  -- 3e. Nested div/mod inside retag & arithmetic expressions (`BigNat.toDecimal` / `Rt.lower` pattern)
  let pNested := mkProg <| mkFunc [0] 2 #[
    { params := []
      body := #[
        .assign 1 (.bin .shr .w64 (.v 0) (.imm 1)),
        .assign 2 (.bin .udiv .w64 (.v 1) (.imm 10)),
        .assign 3 (.bin .urem .w64 (.v 1) (.imm 10)),
        .assign 4 (.addr { base := some (.v 2), index := some (2, .one), disp := 1 }),
        .assign 5 (.addr { base := some (.v 3), index := some (3, .one), disp := 1 })
      ]
      term := .ret [.v 4, .v 5] }
  ]
  expectOk "div-magic-nested-retag-10" pNested
    [[1], [3], [21], [201], [246913579], [0xffffffffffffffff]] fun q => do
      if hasDivRem q then throw "nested retag(udiv/urem 10) was not reduced!"

/-- Memory optimizations: store-to-load forwarding, load CSE across disjoint stores, intra-block DSE. -/
def unitMemory : IO Unit := do
  -- Base pointer `v0` points to heap start (`IxCCTests.Lir.Region.heap`)
  let hbase : Word := IxCCTests.Lir.Region.heap
  let pMem := mkProg <| mkFunc [0, 1, 2] 2 #[
    { params := []
      body := #[
        -- Store v1 at [v0 + 0], then dead-store overwritten later after disjoint accesses!
        .store .w64 { base := some (.v 0), disp := 0 } (.v 1),
        -- Store v2 at disjoint [v0 + 8]
        .store .w64 { base := some (.v 0), disp := 8 } (.v 2),
        -- Load [v0 + 0] -> store-to-load forward v1!
        .assign 3 (.load .w64 .zero { base := some (.v 0), disp := 0 }),
        -- Load [v0 + 16] twice across disjoint store [v0 + 24] -> Load CSE!
        .assign 4 (.load .w64 .zero { base := some (.v 0), disp := 16 }),
        .store .w64 { base := some (.v 0), disp := 24 } (.v 3),
        .assign 5 (.load .w64 .zero { base := some (.v 0), disp := 16 }),
        -- Overwrite [v0 + 0] with v2 -> makes the FIRST store [v0 + 0] DEAD (after forwarding v3 -> v1)!
        .store .w64 { base := some (.v 0), disp := 0 } (.v 2),
        .assign 6 (.bin .add .w64 (.v 3) (.v 4)),
        .assign 7 (.bin .add .w64 (.v 6) (.v 5))
      ]
      term := .ret [.v 7, .v 3] }
  ]
  expectOk "mem-fwd-cse-dse" pMem [[hbase, 11, 22], [hbase, 0x1234, 0x5678]]
    fun q => do
      let b0 := q.funcs[0]!.blocks[0]!.body
      let stores := b0.foldl (fun n s => match s with | .store .. => n + 1 | _ => n) 0
      let loads := b0.foldl (fun n s => match s with | .assign _ (.load ..) => n + 1 | _ => n) 0
      -- Originally 4 stores & 3 loads; after forwarding + load CSE + DSE: 3 stores & 1 load!
      unless stores == 3 && loads == 1 do
        throw s!"expected 3 stores & 1 load after fwd+cse+dse, got {stores} stores & {loads} loads"

/-! ## 2. Negative-control unsound mutant suite -/

def negativeControls : IO Nat := do
  let mut count := 0
  let checkMut (label : String) (p m : Program) : IO Unit := do
    expectRejected label p m
  -- M1: Wrong magic multiplier (m + 1 for d = 10)
  let pDiv10 := mkProg <| mkFunc [0] 1 #[
    { params := [], body := #[.assign 1 (.bin .udiv .w64 (.v 0) (.imm 10))], term := .ret [.v 1] }
  ]
  let m1 := mkProg <| mkFunc [0] 1 #[
    { params := []
      body := #[
        .limb 2 3 (.mulWide64 (.v 0) (.imm (0xcccccccccccccccd + 1))),
        .assign 1 (.bin .shr .w64 (.v 3) (.imm 3))
      ]
      term := .ret [.v 1] }
  ]
  checkMut "magic-m+1" pDiv10 m1; count := count + 1

  -- M2: Wrong magic shift (s - 1 for d = 10)
  let m2 := mkProg <| mkFunc [0] 1 #[
    { params := []
      body := #[
        .limb 2 3 (.mulWide64 (.v 0) (.imm 0xcccccccccccccccd)),
        .assign 1 (.bin .shr .w64 (.v 3) (.imm 2))
      ]
      term := .ret [.v 1] }
  ]
  checkMut "magic-s-1" pDiv10 m2; count := count + 1

  -- M3: Unsound narrow-width identity (`add.32 v0 0 -> v0`)
  let pNarrow := mkProg <| mkFunc [0] 1 #[
    { params := [], body := #[.assign 1 (.bin .add .w32 (.v 0) (.imm 0))], term := .ret [.v 1] }
  ]
  let m3 := mkProg <| mkFunc [0] 1 #[
    { params := [], body := #[], term := .ret [.v 0] }
  ]
  checkMut "narrow-add32-id" pNarrow m3; count := count + 1

  -- M4: Unsound hoisting of variable-divisor `udiv` into preheader
  let pHoistDiv := mkProg <| mkFunc [0, 1, 2] 1 #[
    { params := [], body := #[], term := .jump ⟨1, [.v 2, .imm 0]⟩ },
    { params := [3, 4], body := #[], term := .br .eq .w64 (.v 3) (.imm 0) ⟨3, []⟩ ⟨2, []⟩ },
    { params := []
      body := #[
        .assign 5 (.bin .udiv .w64 (.v 0) (.v 1)),
        .assign 6 (.bin .add .w64 (.v 4) (.v 5)),
        .assign 7 (.bin .sub .w64 (.v 3) (.imm 1))
      ]
      term := .jump ⟨1, [.v 7, .v 6]⟩ },
    { params := [], body := #[], term := .ret [.v 4] }
  ]
  let m4 := mkProg <| mkFunc [0, 1, 2] 1 #[
    { params := [], body := #[.assign 5 (.bin .udiv .w64 (.v 0) (.v 1))], term := .jump ⟨1, [.v 2, .imm 0]⟩ },
    { params := [3, 4], body := #[], term := .br .eq .w64 (.v 3) (.imm 0) ⟨3, []⟩ ⟨2, []⟩ },
    { params := []
      body := #[
        .assign 6 (.bin .add .w64 (.v 4) (.v 5)),
        .assign 7 (.bin .sub .w64 (.v 3) (.imm 1))
      ]
      term := .jump ⟨1, [.v 7, .v 6]⟩ },
    { params := [], body := #[], term := .ret [.v 4] }
  ]
  checkMut "hoist-var-udiv" pHoistDiv m4; count := count + 1

  -- M5: Unsound hoisting of `.load` into preheader
  let pHoistLoad := mkProg <| mkFunc [0, 1] 1 #[
    { params := [], body := #[], term := .jump ⟨1, [.v 1, .imm 0]⟩ },
    { params := [2, 3], body := #[], term := .br .eq .w64 (.v 2) (.imm 0) ⟨3, []⟩ ⟨2, []⟩ },
    { params := []
      body := #[
        .assign 4 (.load .w64 .zero { base := some (.v 0), disp := 0 }),
        .assign 5 (.bin .add .w64 (.v 3) (.v 4)),
        .assign 6 (.bin .sub .w64 (.v 2) (.imm 1))
      ]
      term := .jump ⟨1, [.v 6, .v 5]⟩ },
    { params := [], body := #[], term := .ret [.v 3] }
  ]
  let m5 := mkProg <| mkFunc [0, 1] 1 #[
    { params := [], body := #[.assign 4 (.load .w64 .zero { base := some (.v 0), disp := 0 })],
      term := .jump ⟨1, [.v 1, .imm 0]⟩ },
    { params := [2, 3], body := #[], term := .br .eq .w64 (.v 2) (.imm 0) ⟨3, []⟩ ⟨2, []⟩ },
    { params := []
      body := #[
        .assign 5 (.bin .add .w64 (.v 3) (.v 4)),
        .assign 6 (.bin .sub .w64 (.v 2) (.imm 1))
      ]
      term := .jump ⟨1, [.v 6, .v 5]⟩ },
    { params := [], body := #[], term := .ret [.v 3] }
  ]
  checkMut "hoist-load" pHoistLoad m5; count := count + 1

  -- M6: Unsound DSE deleting a live store
  let pLiveStore := mkProg <| mkFunc [0, 1] 1 #[
    { params := []
      body := #[.store .w64 { base := some (.v 0), disp := 0 } (.v 1)]
      term := .ret [.imm 0] }
  ]
  let m6 := mkProg <| mkFunc [0, 1] 1 #[
    { params := [], body := #[], term := .ret [.imm 0] }
  ]
  checkMut "dse-live-store" pLiveStore m6; count := count + 1

  -- M7: Unsound DSE across may-aliasing load from unknown base `v1`
  let pAliasLoad := mkProg <| mkFunc [0, 1, 2, 3] 1 #[
    { params := []
      body := #[
        .store .w64 { base := some (.v 0), disp := 0 } (.v 2),
        .assign 4 (.load .w64 .zero { base := some (.v 1), disp := 0 }),
        .store .w64 { base := some (.v 0), disp := 0 } (.v 3)
      ]
      term := .ret [.v 4] }
  ]
  let m7 := mkProg <| mkFunc [0, 1, 2, 3] 1 #[
    { params := []
      body := #[
        .assign 4 (.load .w64 .zero { base := some (.v 1), disp := 0 }),
        .store .w64 { base := some (.v 0), disp := 0 } (.v 3)
      ]
      term := .ret [.v 4] }
  ]
  checkMut "dse-across-alias-load" pAliasLoad m7; count := count + 1

  -- M8: Unsound store-to-load forwarding across may-aliasing store
  let pAliasStore := mkProg <| mkFunc [0, 1, 2, 3] 1 #[
    { params := []
      body := #[
        .store .w64 { base := some (.v 0), disp := 0 } (.v 2),
        .store .w64 { base := some (.v 1), disp := 0 } (.v 3),
        .assign 4 (.load .w64 .zero { base := some (.v 0), disp := 0 })
      ]
      term := .ret [.v 4] }
  ]
  let m8 := mkProg <| mkFunc [0, 1, 2, 3] 1 #[
    { params := []
      body := #[
        .store .w64 { base := some (.v 0), disp := 0 } (.v 2),
        .store .w64 { base := some (.v 1), disp := 0 } (.v 3)
      ]
      term := .ret [.v 2] }
  ]
  checkMut "fwd-across-alias-store" pAliasStore m8; count := count + 1

  -- M9: Unsound branch fold without dominating fact
  let pBr := mkProg <| mkFunc [0] 1 #[
    { params := [], body := #[], term := .br .eq .w64 (.v 0) (.imm 1) ⟨1, []⟩ ⟨2, []⟩ },
    { params := [], body := #[], term := .ret [.imm 10] },
    { params := [], body := #[], term := .ret [.imm 20] }
  ]
  let m9 := mkProg <| mkFunc [0] 1 #[
    { params := [], body := #[], term := .jump ⟨1, []⟩ },
    { params := [], body := #[], term := .ret [.imm 10] }
  ]
  checkMut "unfounded-br-fold" pBr m9; count := count + 1

  -- M10: Unsound `brOvf` fold without interval proof
  let pOvf := mkProg <| mkFunc [0] 1 #[
    { params := [], body := #[], term := .brOvf .addC 1 (.v 0) (.imm 1) ⟨1, []⟩ ⟨2, []⟩ },
    { params := [], body := #[], term := .ret [.v 1] },
    { params := [], body := #[], term := .fail .natOverflow }
  ]
  let m10 := mkProg <| mkFunc [0] 1 #[
    { params := [], body := #[.assign 1 (.bin .add .w64 (.v 0) (.imm 1))], term := .jump ⟨1, []⟩ },
    { params := [], body := #[], term := .ret [.v 1] }
  ]
  checkMut "unfounded-brovf-fold" pOvf m10; count := count + 1

  -- M11: Dropping a back-edge clock charge (turning back-edge `1 -> 1` into forward edge `0 -> 1` -> infinite loop)
  let pLoop := mkProg <| mkFunc [0] 1 #[
    { params := [], body := #[], term := .jump ⟨1, [.v 0]⟩ },
    { params := [1], body := #[], term := .jump ⟨1, [.v 1]⟩ }
  ]
  let m11 := mkProg <| mkFunc [0] 1 #[
    { params := [], body := #[], term := .jump ⟨1, [.v 0]⟩ },
    { params := [1], body := #[], term := .ret [.v 1] }
  ]
  checkMut "drop-backedge-loop" pLoop m11; count := count + 1

  -- M12: Dropped `.call` statement
  let pCall : Program :=
    { main := 0
      funcs := #[
        mkFunc [0] 1 #[{ params := [], body := #[.call [1] 1 [.v 0]], term := .ret [.v 1] }] "caller",
        mkFunc [0] 1 #[{ params := [], body := #[], term := .ret [.v 0] }] "callee"
      ] }
  let m12 : Program :=
    { main := 0
      funcs := #[
        mkFunc [0] 1 #[{ params := [], body := #[], term := .ret [.v 0] }] "caller",
        mkFunc [0] 1 #[{ params := [], body := #[], term := .ret [.v 0] }] "callee"
      ] }
  checkMut "dropped-call" pCall m12; count := count + 1

  -- M13: Corrupted `.call` argument
  let m13 : Program :=
    { main := 0
      funcs := #[
        mkFunc [0] 1 #[{ params := [], body := #[.call [1] 1 [.imm 0]], term := .ret [.v 1] }] "caller",
        mkFunc [0] 1 #[{ params := [], body := #[], term := .ret [.v 0] }] "callee"
      ] }
  checkMut "corrupted-call-arg" pCall m13; count := count + 1

  -- M14: Corrupted `.fail` resource tag (`.heap` vs `.stack`)
  let pFail := mkProg <| mkFunc [0] 1 #[{ params := [], body := #[], term := .fail .heap }]
  let m14 := mkProg <| mkFunc [0] 1 #[{ params := [], body := #[], term := .fail .stack }]
  checkMut "corrupted-fail-tag" pFail m14; count := count + 1

  -- M15: Wrong return value
  let pRet := mkProg <| mkFunc [0] 1 #[{ params := [], body := #[], term := .ret [.v 0] }]
  let m15 := mkProg <| mkFunc [0] 1 #[{ params := [], body := #[], term := .ret [.imm 0] }]
  checkMut "wrong-ret-val" pRet m15; count := count + 1

  pure count

/-! ## 3. `Lir.Gen` property-based fuzz testing -/

def fuzzSuite (numPrograms : Nat := 100) : IO (Nat × Nat) := do
  let mut checked := 0
  let mut changed := 0
  for i in [:numPrograms] do
    let seed : UInt64 := UInt64.ofNat (0x9e3779b97f4a7c15 * (i + 1) + 42)
    let raw := (IxCCTests.Lir.Gen.program {} seed).1
    let p := raw.splitCriticalEdges
    if p.wellFormed then
      let q := Lir.Opt.run p
      unless q.wellFormed do
        throw (IO.userError s!"[fuzz #{i}] Lir.Opt.run produced ill-formed program: {q.check}")
      unless Lir.Opt.check p q do
        let plan := inferProgPlan p q
        let mut diag := ""
        for fi in [:p.funcs.size] do
          let F := p.funcs[fi]!; let G := q.funcs[fi]!; let fp := plan.funcs[fi]!
          unless checkFuncWithPlan F G fp do
            let badBlks := (List.range F.blocks.size).filter fun L =>
              match fp.blocks[L]? with
              | some (some bp) => !checkBlock F G fp L bp
              | some none => false
              | none => true
            let detail := match badBlks.head? with
              | some L =>
                  match fp.blocks[L]?, F.blocks[L]? with
                  | some (some bp), some b1 =>
                      let (seg1, calls1) := splitByCalls b1.body.toList
                      let segOk := (checkSeg bp.entryInv seg1 seg1).isSome
                      s!" blk{L}(segOk={segOk},calls={calls1.length},afterCalls={bp.afterCalls.length},params={b1.params},term={repr b1.term},srcDef={bp.entryInv.srcDef.length},tgtOf={bp.entryInv.tgtOf.length},srcEq={bp.entryInv.srcEq.length},facts={bp.entryInv.facts.length})"
                  | _, _ => s!" blk{L}(missing)"
              | none => " entryFail"
            diag := diag ++ s!" fn{fi}(same={F==G},blks={F.blocks.size},bad={badBlks.take 5},{detail})"
        throw (IO.userError s!"[fuzz #{i}] Lir.Opt.check rejected Lir.Opt.run output:{diag}")
      if q != p then changed := changed + 1
      let mainF := p.funcs[p.main]!
      let args := (List.range mainF.params.length).map fun j => UInt64.ofNat ((i * 17 + j * 31 + 3) % 97)
      for clk in [0, 5, 50, 200] do
        let d1 := digest (Lir.eval p clk args flatMem testCtx)
        let d2 := digest (Lir.eval q clk args flatMem testCtx)
        -- Allow target resource failure only if source didn't succeed? Actually our optimizer only hoists
        -- unconditional fail guards, and `Lir.Gen` has exact agreement unless stuck!
        if d1 != .stuck then
          unless d1 == d2 do
            throw (IO.userError s!"[fuzz #{i} clk={clk}] eval mismatch: orig={repr d1}, opt={repr d2}")
      checked := checked + 1
  pure (checked, changed)

/-! ## 4. K1 & K2/K3 before-vs-after measurement harness -/

private def compileLoweredOpt (l : IxCC.Rt.Lowered) : Except String IxCCTests.Rt.Machine.Compiled := do
  let optProg := Lir.Opt.run l.program
  let lOpt : IxCC.Rt.Lowered := { l with program := optProg }
  let (xv, _) ← (Xv.Select.run optProg).mapError fun e => s!"selection: {e.form}: {e.reason}"
  let r ← (Xv.Alloc.run {} xv).mapError (s!"allocation: " ++ ·)
  let a ← (Backend.emit r.program (lOpt.config IxCCTests.Rt.Machine.testProvenance)).mapError toString
  let whole ← (Backend.compileOpt l.program (l.config IxCCTests.Rt.Machine.testProvenance)).mapError toString
  unless whole.object == a.object do throw "Backend.compileOpt produced a different object than emit!"
  pure { lir := lOpt, xv, xl := r.program, artifact := a }

private def measureOne (name : String) (l : IxCC.Rt.Lowered) (sym : String) (args : List Nat)
    (fuel : Nat := 1 <<< 30) : IO String := do
  let pOrig := l.program
  let pOpt := Lir.Opt.run pOrig
  unless pOpt.wellFormed do
    throw (IO.userError s!"[{name}] optimized Lir not wellFormed: {pOpt.check}")
  unless Lir.Opt.check pOrig pOpt do
    throw (IO.userError s!"[{name}] Lir.Opt.check rejected optimized Lir!")
  let ccOrig ← IO.ofExcept (IxCCTests.Rt.Machine.compile l)
  let ccOpt ← IO.ofExcept (compileLoweredOpt l)
  let msOrig ← IO.ofExcept (IxCCTests.Rt.Machine.initMachines ccOrig)
  let (eOrig, msOrig') ← IO.ofExcept <| ← IO.lazyPure fun _ =>
    IxCCTests.Rt.Machine.runExport ccOrig sym (args.map UInt64.ofNat) msOrig fuel
  let msOpt ← IO.ofExcept (IxCCTests.Rt.Machine.initMachines ccOpt)
  let (eOpt, msOpt') ← IO.ofExcept <| ← IO.lazyPure fun _ =>
    IxCCTests.Rt.Machine.runExport ccOpt sym (args.map UInt64.ofNat) msOpt fuel
  unless eOrig.status == eOpt.status && eOrig.value == eOpt.value do
    throw (IO.userError s!"[{name}] result mismatch! orig=({eOrig.status},{eOrig.value}) opt=({eOpt.status},{eOpt.value})")
  let stmtsBefore := countStmts pOrig
  let stmtsAfter := countStmts pOpt
  let bytesBefore := ccOrig.artifact.encoded.text.size
  let bytesAfter := ccOpt.artifact.encoded.text.size
  let typedBefore := msOrig'.typedSteps - msOrig.typedSteps
  let typedAfter := msOpt'.typedSteps - msOpt.typedSteps
  let bstepsBefore := msOrig'.byteSteps - msOrig.byteSteps
  let bstepsAfter := msOpt'.byteSteps - msOpt.byteSteps
  let pct (b a : Nat) : String :=
    if b == 0 then "0.0%"
    else if a ≤ b then
      let d := (b - a) * 1000 / b
      s!"-{d / 10}.{d % 10}%"
    else
      let d := (a - b) * 1000 / b
      s!"+{d / 10}.{d % 10}%"
  pure s!"  {name} {args}: stmts {stmtsBefore}→{stmtsAfter} ({pct stmtsBefore stmtsAfter}), \
    text {bytesBefore}→{bytesAfter}B ({pct bytesBefore bytesAfter}), \
    typed {typedBefore}→{typedAfter} ({pct typedBefore typedAfter}), \
    bytes {bstepsBefore}→{bstepsAfter} ({pct bstepsBefore bstepsAfter}), \
    status={eOpt.status.toNat}, val={eOpt.value.toNat}"

def benchK1 : IO (Array String) := do
  let runs : List (String × List Nat) :=
    [("sum-loop", [5000]), ("collatz", [27]), ("prime-count", [100]),
     ("gcd", [1071, 462]), ("fib", [13]), ("sfib", [1000]),
     ("ackermann", [3, 3]), ("tak", [12, 12, 8, 4]), ("even-odd", [1001])]
  let mut out := #[]
  for (name, args) in runs do
    let (_, art) ← IxCCTests.Pipeline.compileIn name (← IxCCTests.Pipeline.benchInput name)
    let some root := art.roots.head? | throw (IO.userError s!"{name}: no root")
    let line ← measureOne name art.lowered root.symbol args
    out := out.push line
  pure out

def benchK2K3 : IO (Array String) := do
  let mut out := #[]
  -- K2: heap-allocating list & tree program from `IxCCTests.Rt.Cases` (`values'`)
  let cVal := IxCCTests.Rt.Cases.cfgOf IxCCTests.Rt.Cases.values'
  let (lVal, _) ← IxCCTests.Rt.Cases.lirOf cVal
  -- Function 2 builds a list, function 4 builds a binary tree!
  for (label, fnIdx, args) in [("k2-list-build", 2, [20]), ("k2-tree-build", 4, [4])] do
    let some sym := lVal.roots.lookup fnIdx
      | throw (IO.userError s!"{label}: root {fnIdx} not found")
    let line ← measureOne label lVal sym args
    out := out.push line
  -- K3-style constant division by 10 & 10^19 (`BigNat.toDecimal` pattern!)
  let div10Prog := IxCCTests.Rt.Cases.prog [
    ([0], .bind 1 (.prim .natDiv [IxCCTests.Rt.Cases.v 0, IxCCTests.Rt.Cases.n 10]) (.ret (IxCCTests.Rt.Cases.v 1)))
  ]
  let mod10Prog := IxCCTests.Rt.Cases.prog [
    ([0], .bind 1 (.prim .natMod [IxCCTests.Rt.Cases.v 0, IxCCTests.Rt.Cases.n 10]) (.ret (IxCCTests.Rt.Cases.v 1)))
  ]
  for (label, fp, args) in [("k3-natDiv10", div10Prog, [123456789]), ("k3-natMod10", mod10Prog, [123456789])] do
    let (l, _) ← IxCCTests.Rt.Cases.lirOf (IxCCTests.Rt.Cases.cfgOf fp)
    let some (_, sym) := l.roots.head? | throw (IO.userError s!"{label}: no root")
    let line ← measureOne label l sym args
    out := out.push line
  pure out

end IxCCTests.Lir.Opt
