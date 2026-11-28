import IxCC.Xv.Stacking.Emit

/-!
# The SysV export wrapper and the exit group

An export `cx_root(void *region, uint64_t a1, …, a5)` returns `{status,
value}` in `rax:rdx`. Stacking emits one wrapper per `sysvExport` function
and one exit group per program:

```text
cx_root:  push rbx; push rbp; push r12; push r13; push r14; push r15; sub rsp, 8   ; rsp = S₀ − 56
          lea r15, [rdi + 64]; mov [r15 − 64], rsp          ; ctx; entrySp := rsp
          mov r11, rsp; sub r11, [r15 − 48]; mov [r15 − 56], r11   ; stackLimit := rsp − stackBudget
          mov r11, a₁; or r11, a₂; …; test r11, r11; jl fail₃      ; a Nat argument ≥ 2^63
          lea rdi, [a₁ + a₁ + 1]; …                         ; tag into the internal argument registers
          call entry
          mov rdx, rax; xor eax, eax                        ; status 0, value
          add rsp, 8; pop r15; pop r14; pop r13; pop r12; pop rbp; pop rbx; ret
fail_k:   mov eax, k; jmp failExit                          ; k = 1 heap, 2 stack, 3 natOverflow, 4 trap
failExit: unwind [r15 − 64]; xor edx, edx                   ; rsp := entrySp, value 0
          add rsp, 8; pop r15; pop r14; pop r13; pop r12; pop rbp; pop rbx; ret
```

The epilogue is inlined in both places instead of shared, which saves the
success path a jump. All wrappers save the same registers in the same
order, so one exit group serves every export; `r15` still holds the
context at `failExit` because internal code never writes it.

**Arguments**. The internal convention puts argument `i` in
`rdi, rsi, rdx, rcx, r8` (`Lir.Conv.argRegs`), the C caller in the SysV
register after the region pointer; each is moved one register down, in
order, so no source is overwritten before it is read. A `Nat` argument is
checked below 2^63 (the OR of all of them has its sign bit clear) and
tagged `2n+1`; a `word` argument passes unchanged. -/

namespace IxCC.Xv.Stacking

open IxCC.Lir (FunId)

/-- How an export passes an argument. -/
inductive ArgRep where
  /-- A `Nat` below 2^63, tagged `2n+1`; a larger one fails with
  status 3 (natOverflow). -/
  | nat
  /-- An untagged word, passed as is. -/
  | word
  deriving DecidableEq, Repr, Inhabited

/-- The SysV argument registers after the region pointer in `rdi`. -/
def sysvArgs : List X86.GPR := [.rsi, .rdx, .rcx, .r8, .r9]

/-- The registers every wrapper saves, in push order. -/
def wrapperSaves : List X86.GPR := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- `add rsp, 8` and the pops, in reverse push order. -/
def wrapperEpilogue : List X86.Instr := addRsp 8 :: wrapperSaves.reverse.map X86.Instr.pop

/-- The exit group at block `base`: `fail_k` at `base + k − 1` for `k =
1..4`, and `failExit` at `base + 4`. -/
def exitGroup (base : Nat) : List X86.Block :=
  ((List.range 4).map fun j =>
    { instructions := #[X86.Instr.mov .w32 .rax (.imm (UInt64.ofNat (j + 1)))]
      terminator := .jump (UInt32.ofNat (base + 4)) }) ++
  [{ instructions := (X86.Instr.unwind entrySpCell :: X86.Instr.alu .xor .w32 .rdx (.reg .rdx) ::
        wrapperEpilogue).toArray
     terminator := .ret }]

/-- The number of blocks in the exit group. -/
def exitBlocks : Nat := 5

/-- `lea dst, [src + src + 1]`: tag a `Nat`. -/
def tagInto (dst src : X86.GPR) : Except String X86.Instr :=
  match indexReg src with
  | some index => pure (X86.Instr.lea dst { base := some src, index := some index, displacement := 1 })
  | none => throw "rsp cannot be an index"

/-- Whether an export needs its argument check (and so two blocks). -/
def hasNatArg (reps : List ArgRep) : Bool := reps.contains .nat

/-- The number of blocks of an export's wrapper. -/
def wrapperBlocks (reps : List ArgRep) : Nat := if hasNatArg reps then 2 else 1

/-- The wrapper of an export at block `start`, calling `entry`, with the
exit group's `fail₃` block for a `Nat` argument out of range. -/
def wrapper (entry fail₃ : X86.BlockId) (reps : List ArgRep) (start : Nat) : Except String (List X86.Block) := do
  unless reps.length ≤ sysvArgs.length do throw s!"an export takes at most {sysvArgs.length} arguments"
  let head := wrapperSaves.map X86.Instr.push ++
    [subRsp 8, X86.Instr.lea .r15 { base := some .rdi, displacement := 64 },
      X86.Instr.store .w64 entrySpCell .rsp, X86.Instr.mov .w64 .r11 (.reg .rsp),
      .op subRM [.reg .r11, .mem stackBudgetCell], X86.Instr.store .w64 stackLimitCell .r11]
  let pairs := (sysvArgs.zip Lir.Conv.argRegs).zip reps
  let marshal ← pairs.mapM fun ((src, dst), rep) =>
    match rep with
    | .nat => tagInto dst src
    | .word => pure (X86.Instr.mov .w64 dst (.reg src))
  let call := marshal ++
    [.call entry, X86.Instr.mov .w64 .rdx (.reg .rax), X86.Instr.alu .xor .w32 .rax (.reg .rax)] ++ wrapperEpilogue
  match pairs.filterMap fun ((src, _), rep) => if rep == .nat then some src else none with
  | [] => pure [{ instructions := (head ++ call).toArray, terminator := .ret }]
  | first :: rest =>
      let merged := X86.Instr.mov .w64 .r11 (.reg first) :: rest.map fun r => .op orMR [.reg .r11, .reg r]
      pure [{ instructions := (head ++ merged).toArray
              terminator := .branch testMR [.reg .r11, .reg .r11] .signedLt fail₃ (UInt32.ofNat (start + 1)) },
            { instructions := call.toArray, terminator := .ret }]

end IxCC.Xv.Stacking
