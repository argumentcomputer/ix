import IxCC.Xv.Select.Amode
import IxCC.Xv.Select.Cond

/-!
# Flag producers (rules 1–3)

The row that sets the flags for a Lir condition `c w a b`, shared by the
branch (`jcc`), `select` (`cmovcc`) and `test` (`setcc`) rules. It writes
nothing but flags (`Op.flagsOnly`), as a fused pair requires.

| Condition | Producer | Rule |
| --- | --- | --- |
| a comparison, `b` an immediate whose low `w` bits are 0 | `test a, a` (the same flags as `cmp a, 0`) | 1 (`cmp.testSelf`) |
| a comparison | `cmp r/m, r`, `cmp r/m, imm8` (83 /7) or `imm32` (81 /7); swapped for an immediate on the left | 1 (`cmp.*`, `cmp.swap`) |
| `tz`/`tnz` with an immediate | `test r/m, imm` at the narrowest width holding the immediate's low `w` bits (8, 32 or `w`) | 2 (`test.imm`) |
| `tz`/`tnz` with registers | `test r/m, r` | 2 (`test.rr`) |
| either, with a single-use load operand | the load's address in the r/m slot, the condition swapped if it was on the right | 3 (`cmp.mem*`, `test.mem*`) |
-/

namespace IxCC.Xv.Select

open IxCC.Lir (VReg Word)

/-- `op r/m, r` or `op r/m, imm` with `a` in the r/m slot: the row and its
arguments, materializing an immediate that does not fit. `imm8`: the row
has an `MI8` form (`test` has none). -/
def producerArgs (mn : X86.Mnemonic) (w : X86.Width) (a : XArg VReg) (b : Lir.Arg) (tag : String)
    (imm8 : Bool := true) : SelM (X86.Op × List (XArg VReg) × List (Inst VReg)) := do
  match b with
  | .v b =>
      fire s!"{tag}.rr"
      return (row mn w .MR, [a, .r b], [])
  | .imm k =>
      match if imm8 then imm8? w k else none with
      | some c =>
          fire s!"{tag}.imm8"
          return (row mn w .MI8, [a, .i c], [])
      | none =>
      match immFull? w k with
      | some c =>
          fire s!"{tag}.imm32"
          return (row mn w .MI, [a, .i c], [])
      | none =>
          let (t, pre) ← materialize k
          fire s!"{tag}.rr"
          return (row mn w .MR, [a, .r t], pre)

/-- A flag producer: instructions before it, its row and arguments, and the
x86 condition to test. -/
structure Producer where
  pre : List (Inst VReg)
  op : X86.Op
  args : List (XArg VReg)
  cond : X86.Condition

/-- The narrowest `test` width at which `a &&& k` is zero exactly when its
low `w` bits are: 8 if `k`'s low `w` bits fit a byte, 32 if they fit a
doubleword, else `w`. -/
def testWidth (w : X86.Width) (k : Word) : X86.Width :=
  let k := w.truncate k
  if k.toNat < 256 then .w8 else if k.toNat < 2 ^ 32 && w == .w64 then .w32 else w

/-- Rules 1 and 3 for the ten comparisons. -/
def cmpProducer (cx : X86.Condition) (w : X86.Width) (a b : Lir.Arg) (site : Nat) : SelM Producer := do
  if let .v a' := a then
    if let some m ← sinkLoad? a' site w.bytes then
      let (p, args, pre) ← producerArgs .cmp w (.m m) b "cmp.mem"
      return ⟨pre, p, args, cx⟩
  if let .v b' := b then
    if let some m ← sinkLoad? b' site w.bytes then
      let (p, args, pre) ← producerArgs .cmp w (.m m) a "cmp.mem"
      return ⟨pre, p, args, swapCond cx⟩
  match a, b with
  | .v a, .imm k =>
      if w.truncate k == 0 then
        fire "cmp.testSelf"
        return ⟨[], row .test w .MR, [.r a, .r a], cx⟩
      let (p, args, pre) ← producerArgs .cmp w (.r a) (.imm k) "cmp"
      return ⟨pre, p, args, cx⟩
  | .v a, .v b =>
      let (p, args, pre) ← producerArgs .cmp w (.r a) (.v b) "cmp"
      return ⟨pre, p, args, cx⟩
  | .imm k, .v b =>
      if w.truncate k == 0 then
        fire "cmp.testSelf"
        return ⟨[], row .test w .MR, [.r b, .r b], swapCond cx⟩
      fire "cmp.swap"
      let (p, args, pre) ← producerArgs .cmp w (.r b) (.imm k) "cmp"
      return ⟨pre, p, args, swapCond cx⟩
  | .imm ka, .imm kb =>
      let (x, pre₁) ← materialize ka
      let (p, args, pre₂) ← producerArgs .cmp w (.r x) (.imm kb) "cmp"
      return ⟨pre₁ ++ pre₂, p, args, cx⟩

/-- `test a, k` for `tz`/`tnz`, narrowed (rule 2), with a single-use load
folded into the r/m slot (rule 3). -/
def testImm (cc : X86.Condition) (w : X86.Width) (a : VReg) (k : Word) (site : Nat) : SelM Producer := do
  let k := w.truncate k
  let w' := testWidth w k
  let target ← match ← sinkLoad? a site w'.bytes with
    | some m => do
        fire "test.mem"
        pure (XArg.m m)
    | none => pure (.r a)
  match immFull? w' k with
  | some c =>
      fire "test.imm"
      return ⟨[], row .test w' .MI, [target, .i c], cc⟩
  | none =>
      let (t, pre) ← materialize k
      fire "test.rr"
      return ⟨pre, row .test w .MR, [target, .r t], cc⟩

/-- Rules 2 and 3 for `tz` (`zero`) and `tnz`. -/
def testProducer (zero : Bool) (w : X86.Width) (a b : Lir.Arg) (site : Nat) : SelM Producer := do
  let cc : X86.Condition := if zero then .eq else .ne
  match a, b with
  | .v a, .v b =>
      if let some m ← sinkLoad? a site w.bytes then
        fire "test.mem"
        return ⟨[], row .test w .MR, [.m m, .r b], cc⟩
      if let some m ← sinkLoad? b site w.bytes then
        fire "test.mem"
        return ⟨[], row .test w .MR, [.m m, .r a], cc⟩
      fire "test.rr"
      return ⟨[], row .test w .MR, [.r a, .r b], cc⟩
  | .v a, .imm k | .imm k, .v a => testImm cc w a k site
  | .imm ka, .imm kb =>
      let (x, pre) ← materialize ka
      let p ← testImm cc w x kb site
      return { p with pre := pre ++ p.pre }

/-- The flag producer for the Lir condition `c w a b` at the current site. -/
def compareProducer (c : Lir.Cond) (w : X86.Width) (a b : Lir.Arg) : SelM Producer := do
  let site ← sitePos
  match condX86 c with
  | some cx => cmpProducer cx w a b site
  | none => testProducer (c == .tz) w a b site

end IxCC.Xv.Select
