import IxCC.Cfg.WellFormed
import IxCC.Fir.Rep
import IxCC.Lir.SplitEdges
import IxCC.Rt.Procs.Entry
import IxCC.Rt.Procs.Nat
import IxCC.Rt.Rc.Array.Wire

/-! # Cfg → Lir (`Rt.lower`, the Phase 1 fragment)

The data refinement from Cfg's abstract heap to Lir's memory, for
Cfg programs of the immortal fragment: no RC operation,
no credit, no closure. On the recheck path in style P (proved once, re-run), so it is written in
kernel-evaluable style (D17): structural recursion over lists, `Src.NatMap`/`NatSet`, a state monad
over plain data, no `HashMap`, no array indexing, no well-founded recursion. It reads no
certificate.

**Values** (`Rt.Layout`): a `Nat` literal `n` is the immediate
`2n + 1`, and one at or above 2^63 fails with `natOverflow` where Cfg would
evaluate it; □ is `1`; a field-less constructor is `2·tag + 1`; a cell is
its address. Cfg variables keep their numbers as virtual registers;
temporaries and fresh parameters come from above the function's supply.

**Blocks.** Each Cfg block becomes a contiguous run of Lir labels (its
*chunk*): its head, then the blocks its instructions and terminator open,
each at a higher label than the block that jumps to it. Chunks keep Cfg's
order, so a Cfg forward edge stays forward and a back edge (a self tail
call or a recursive jump, which Cfg's labels put at or below its source)
stays backward: Lir charges exactly Cfg's back edges, and calls and tail
calls map to `call` and `tail`, so the clock map is the identity from the
entry on. Block 0 carries the function's parameters; when some
edge enters it, a fresh parameterless entry block binds the parameters and
jumps to it (Lir entries have no predecessors). Blocks no path reaches (Cfg
allows dead join points; Lir does not) are dropped, keeping the order, and
`Lir.Func.splitCriticalEdges` splits whatever critical edges remain.

**Instructions.**
* `alloc` of a field-less constructor is its immediate; otherwise the
  immortal bump allocation: load `bump`, add the cell size, compare with
  `limit` (`fail heap` above it), store `bump`, the static header (`scan =
  fields`, `cls = 0`, `rc = INT32_MIN`, as two 32-bit stores) and the
  fields.
* `proj` is a load at `8 + 8i`; the `Nat` successor's field is `v − 2`.
* Primitives on tagged words: `natAdd` by `brOvf addC` on `a − 1`
  and `b` (carry: `fail natOverflow`); `natSub` and `natPred` truncate with a
  `select`; `natMul` untags one side, multiplies, and checks the product by
  division; `natDiv`/`natMod` untag, divide by a nonzero divisor, and select
  `n / 0 = 0`, `n % 0 = n`; comparisons compare the words (tagging is
  monotone) and select the `Bool` words; `natLand`/`natLor` keep the tag
  bit, `natXor` restores it; `natShr` shifts by the untagged count (a count
  above 63 gives 0); `natShl` shifts `2p` and checks that shifting back
  restores it; `natPow` and `natGcd` call the runtime procedures
  `rt_nat_pow` and `rt_nat_gcd` (`Rt.Procs.Nat`).
* The fixed-width word primitives (stage W1) on tagged words: below width
  64 a word congruent to the tagged result, masked; at width 64 the untagged
  wrapped result, `natOverflow` at or above 2^63 (`word`, below).
* A comparison whose only use is the block's `switch` on `Bool` becomes
  the branch itself.

**Switch**: on `Nat` keys, the zero test `v = 1`; on
field-less keys, a compare chain against `2·tag + 1`; on keys with fields,
the header's tag (`u16` at offset 2); mixed, the low bit first. Without a
default the last alternative is taken without a test (a value no
alternative names is stuck in Cfg). Keys are forgotten, tags kept.

`Rt.lower` appends `cx_init` and the two procedures (`Rt.Procs`) after the
program's functions, and marks each exported root `sysvExport
"cx_<name>"`. -/

namespace IxCC.Rt

open IxCC.Fir (FunId)
open IxCC.Lir (VReg Label Word)

/-- Why `Rt.lower` declines a program. -/
inductive Error where
  | noExports
  | missingFun (f : FunId)
  | missingBlock (f : FunId) (b : Nat)
  /-- A string literal: string objects are planned. -/
  | string (f : FunId)
  /-- A primitive without a Phase 1 lowering. -/
  | prim (f : FunId) (op : Lam.Prim)
  /-- A `Bool`-valued primitive in a program without the pinned `Bool`
  constructors (Cfg is stuck there). -/
  | noBool (f : FunId)
  /-- A right-hand side Cfg is stuck on (a Fir `ctor`/`proj`, a projection
  outside the constructor, an allocation of the wrong arity). -/
  | form (f : FunId) (what : String)
  /-- A constructor outside the layout limits of `Rt.Layout`. -/
  | layout (f : FunId) (what : String)
  | switch (f : FunId) (b : Nat) (what : String)
  /-- An edge whose back flag disagrees with Cfg's label order (the clock
  map needs it). -/
  | edgeOrder (f : FunId) (b : Nat)
  /-- A chunk label left unfilled (a bug in the lowering). -/
  | internal (f : FunId) (what : String)
  /-- A function numbered at or beyond the program's size (Lir numbers the
  runtime procedures from there). -/
  | funRange (f : FunId)
  deriving Repr, Inhabited

def Error.render : Error → String
  | .noExports => "rt.exports: the program exports nothing"
  | .missingFun f => s!"rt.missing: function {f} is absent"
  | .missingBlock f b => s!"rt.missing: function {f} has no block {b}"
  | .string f => s!"rt.string: function {f} uses a string literal (statics are Phase 2)"
  | .prim f op => s!"rt.prim: function {f}: {op.name} has no Phase 1 lowering"
  | .noBool f => s!"rt.bool: function {f}: a Boolean primitive without the pinned Bool constructors"
  | .form f what => s!"rt.form: function {f}: {what}"
  | .layout f what => s!"rt.layout: function {f}: {what}"
  | .switch f b what => s!"rt.switch: function {f} block {b}: {what}"
  | .edgeOrder f b => s!"rt.edge: function {f} block {b}: a back flag disagrees with the label order"
  | .internal f what => s!"rt.internal: function {f}: {what}"
  | .funRange f => s!"rt.funs: function {f} is numbered beyond the program's size"

instance : ToString Error := ⟨Error.render⟩

/-- Names for the exported roots: `cx_<name>` per `Cfg.Program.exports`
entry, `root<i>` where a name is missing, plus optional fixed `.rodata` base
address for DR1/DR4 zero-allocation static string literals. -/
structure Config where
  names : List String := []
  rodataBase : Option Word := none
  deriving Inhabited

/-- `Rt.lower`'s output: the Lir program (its `main` the first root), the
runtime procedures' functions (`cx_init`, `rt_nat_pow`, `rt_nat_gcd`, right
after the program's), each root's function and symbol in export order, and
optional DR1 `.rodata` bytes & symbols for static literals. -/
structure Lowered where
  program : Lir.Program
  init : Lir.FunId
  natPow : Lir.FunId
  natGcd : Lir.FunId
  roots : List (Lir.FunId × String)
  rodata : Option ByteArray := none
  rodataExports : List X86.ELF.RodataSymbol := []
  deriving Inhabited

namespace Lower

/-! ## The tables -/

structure Tables where
  ctors : List Lam.CtorInfo
  known : Lam.Known
  /-- The words of `true` and `false`, if the program pins `Bool`. -/
  bools : Option (Word × Word)
  /-- The runtime procedures' functions. -/
  natPow : FunId
  natGcd : FunId
  /-- The registers each function holds as raw 64-bit words (`[0, 2^64)`, untagged): the
  reference-counted route's word layout (`Cfg.Rc.Raw`). None on the immortal route. -/
  rawVar : FunId → VReg → Bool := fun _ _ => false
  /-- The raw flags of a block's parameters, in order (block 0: the function's parameters). -/
  rawParams : FunId → Nat → List Bool := fun _ _ => []
  /-- Whether a function returns a raw word. -/
  rawRet : FunId → Bool := fun _ => false

/-- No register, parameter or result is raw: the immortal route's tables. -/
structure NoRaw (T : Tables) : Prop where
  var : ∀ f x, T.rawVar f x = false
  params : ∀ f b, T.rawParams f b = []
  ret : ∀ f, T.rawRet f = false

def tables (P : Cfg.Program) : Tables :=
  -- a `Bool` word only for a key outside `Nat`'s, within the tag limit (the
  -- value relation of `Rt.lower_correct` needs both)
  let word := fun (k : Option Key.CtorKey) =>
    k.bind fun k =>
      if P.known.natZero == some k || P.known.natSucc == some k then none
      else (Fir.CtorInfo.ofKey P.ctors k).bind fun c =>
        if c.tag ≤ maxTag then some (ctor0Word c.tag) else none
  { ctors := P.ctors, known := P.known
    bools := match word P.known.boolTrue, word P.known.boolFalse with
      | some t, some f => some (t, f)
      | _, _ => none
    natPow := P.size + 1, natGcd := P.size + 2 }

/-! ## Chunks before labels are fixed -/

/-- An edge target: a label of the current chunk, or a Cfg block. -/
inductive Tgt where
  | loc (j : Nat)
  | blk (b : Nat)
  deriving Inhabited

structure PEdge where
  tgt : Tgt
  args : List Lir.Arg := []
  deriving Inhabited

/-- Lir terminators over chunk targets (comparisons are 64-bit). -/
inductive PTerm where
  | jump (e : PEdge)
  | br (c : Lir.Cond) (a b : Lir.Arg) (t f : PEdge)
  | brOvf (o : Lir.Ovf) (x : VReg) (a b : Lir.Arg) (ok ovf : PEdge)
  | ret (a : Lir.Arg)
  | tail (f : FunId) (as : List Lir.Arg)
  | fail (r : Sem.Resource)
  | trap
  deriving Inhabited

structure PBlock where
  params : List VReg := []
  body : List Lir.Stmt := []
  term : PTerm
  cold : Bool := false
  deriving Inhabited

/-- One chunk being built: finished blocks by local label, the open block
(label, parameters, body reversed), the next free label and the next
fresh register. -/
structure St where
  done : Src.NatMap PBlock := .leaf
  cur : Nat := 0
  params : List VReg := []
  acc : List Lir.Stmt := []
  next : Nat := 1
  fresh : VReg
  deriving Inhabited

abbrev M := StateT St (Except Error)

def emit (s : Lir.Stmt) : M Unit := modify fun st => { st with acc := s :: st.acc }

def freshReg : M VReg := modifyGet fun st => (st.fresh, { st with fresh := st.fresh + 1 })

def newLabel : M Nat := modifyGet fun st => (st.next, { st with next := st.next + 1 })

def put (l : Nat) (b : PBlock) : M Unit := modify fun st => { st with done := st.done.insert l b }

/-- End the open block with `t`. -/
def close (t : PTerm) : M Unit := modify fun st =>
  { st with done := st.done.insert st.cur { params := st.params, body := st.acc.reverse, term := t }
            params := [], acc := [] }

/-- Continue in the block at `l`. -/
def openAt (l : Nat) (params : List VReg := []) : M Unit :=
  modify fun st => { st with cur := l, params, acc := [] }

/-- A cold block ending in `t`, at a new label. -/
def coldBlock (t : PTerm) : M Nat := do
  let l ← newLabel
  put l { term := t, cold := true }
  pure l

def loc (l : Nat) : PEdge := ⟨.loc l, []⟩

/-- End the open block with a check whose failing edge goes to a new cold
`fail r` block, and continue in a new block. -/
def check (r : Sem.Resource) (mk : PEdge → PEdge → PTerm) : M Unit := do
  let bad ← coldBlock (.fail r)
  let cont ← newLabel
  close (mk (loc cont) (loc bad))
  openAt cont

def assign (x : VReg) (r : Lir.Rhs) : M Unit := emit (.assign x r)

/-- A fresh register holding `r`. -/
def temp (r : Lir.Rhs) : M Lir.Arg := do
  let t ← freshReg
  assign t r
  pure (.v t)

def bin (o : Lir.BinOp) (a b : Lir.Arg) : M Lir.Arg := temp (.bin o .w64 a b)

def ctxAt (d : Int) : Lir.Addr := { base := some .ctx, disp := d }

def mem (x : VReg) (d : Int) : Lir.Addr := { base := some (.v x), disp := d }

/-! ## Operands -/

/-- A Cfg operand; `none` for a `Nat` literal without an immediate word. -/
def operand (f : FunId) : Fir.Arg → Except Error (Option Lir.Arg)
  | .var x => pure (some (.v x))
  | .lit (.nat n) => pure ((natWord n).map .imm)
  | .lit (.str _) => throw (.string f)
  | .erased => pure (some (.imm erasedWord))

def operands (f : FunId) : List Fir.Arg → Except Error (Option (List Lir.Arg))
  | [] => pure (some [])
  | a :: as => do
    let x ← operand f a
    let xs ← operands f as
    pure (match x, xs with
      | some x, some xs => some (x :: xs)
      | _, _ => none)

/-- Lower the operands and continue with `k`, or end the block with `fail
natOverflow` where a literal has no word (Cfg evaluates it here). Returns
whether the block goes on. -/
def withOperands (f : FunId) (as : List Fir.Arg) (k : List Lir.Arg → M Unit) : M Bool := do
  match ← operands f as with
  | some ls => k ls; pure true
  | none => close (.fail .natOverflow); pure false

/-- An operand at a position held raw (`Tables.rawVar`): a variable as it is (the route that
sets raw positions checks that only raw registers reach one), a `Nat` literal below `2^64` as
its untagged word; `none` (the block fails with `natOverflow`) for anything else. -/
def rawOperand (f : FunId) : Fir.Arg → Except Error (Option Lir.Arg)
  | .var x => pure (some (.v x))
  | .lit (.nat n) => pure (if n < 2 ^ 64 then some (.imm (UInt64.ofNat n)) else none)
  | .lit (.str _) => throw (.string f)
  | .erased => pure none

/-- An operand at a position that is raw or not (a variable is its register either way). -/
def operandAt (f : FunId) (raw : Bool) : Fir.Arg → Except Error (Option Lir.Arg)
  | .var x => pure (some (.v x))
  | a => if raw then rawOperand f a else operand f a

/-- Operands at positions with the given raw flags (a missing flag is `false`). -/
def operandsAt (f : FunId) (raw : List Bool) : List Fir.Arg → Except Error (Option (List Lir.Arg))
  | [] => pure (some [])
  | a :: as => do
    let x ← operandAt f (raw.headD false) a
    let xs ← operandsAt f raw.tail as
    pure (match x, xs with
      | some x, some xs => some (x :: xs)
      | _, _ => none)

/-- `withOperands` at positions with the given raw flags. -/
def withOperandsAt (f : FunId) (raw : List Bool) (as : List Fir.Arg) (k : List Lir.Arg → M Unit) :
    M Bool := do
  match ← operandsAt f raw as with
  | some ls => k ls; pure true
  | none => close (.fail .natOverflow); pure false

/-! ## Primitives on tagged words -/

/-- The untagged value of a word (`w >>> 1`). -/
def untag : Lir.Arg → M Lir.Arg
  | .imm w => pure (.imm (w >>> 1))
  | a => bin .shr a (.imm 1)

/-- `2q + 1` (`lea [q + q + 1]`). -/
def retag : Lir.Arg → Lir.Rhs
  | .imm w => .arg (.imm (2 * w + 1))
  | .v q => .addr { base := some (.v q), index := some (q, .one), disp := 1 }

/-- General variable-divisor division/remainder: cold zero-divisor guard,
32-bit `div r32` fast path when `(u | y) < 2^32`, and cold 64-bit fallback. -/
def divModVar (x : VReg) (o : Lir.BinOp) (zero : Lir.Arg → Lir.Arg) (a b : Lir.Arg) : M Unit := do
  let nz ← newLabel
  let fast32 ← newLabel
  let slow64 ← newLabel
  let zBlk ← newLabel
  let join ← newLabel
  close (.br .eq b (.imm 1) (loc zBlk) (loc nz))
  openAt nz
  let u ← untag a
  let y ← untag b
  let uy ← bin .or u y
  let hi ← bin .shr uy (.imm 32)
  close (.br .ne hi (.imm 0) (loc slow64) (loc fast32))
  let q32 ← freshReg
  let r32 ← freshReg
  put fast32 {
    body := [.assign q32 (.bin o .w32 u y), .assign r32 (retag (.v q32))],
    term := .jump ⟨.loc join, [.v r32]⟩
  }
  let q64 ← freshReg
  let r64 ← freshReg
  put slow64 {
    body := [.assign q64 (.bin o .w64 u y), .assign r64 (retag (.v q64))],
    term := .jump ⟨.loc join, [.v r64]⟩,
    cold := true
  }
  put zBlk { term := .jump ⟨.loc join, [zero a]⟩, cold := true }
  openAt join [x]

/-- `a / b` or `a % b`, with `n / 0 = 0` and `n % 0 = n` (`zero a` is the
result for a zero divisor). -/
def divMod (x : VReg) (o : Lir.BinOp) (zero : Lir.Arg → Lir.Arg) (a b : Lir.Arg) : M Unit :=
  match b with
  | .imm w =>
    if w == 1 then assign x (.arg (zero a))
    else if w == 3 then
      match o with
      | .udiv => assign x (.arg a)
      | _ => assign x (.arg (.imm 1))
    else if w == 5 then
      match o with
      | .udiv => do
        let u ← untag a
        assign x (.bin .or .w64 u (.imm 1))
      | _ => assign x (.bin .and .w64 a (.imm 3))
    else if w == 9 then
      match o with
      | .udiv => do
        let u ← bin .shr a (.imm 2)
        assign x (.bin .or .w64 u (.imm 1))
      | _ => assign x (.bin .and .w64 a (.imm 7))
    else do
      let u ← untag a
      let q ← bin o u (.imm (w >>> 1))
      assign x (retag q)
  | b => divModVar x o zero a b

/-! ## Fixed-width words on tagged words (stage W1)

A word of width `w` is the tagged immediate `2n + 1` of its number `n < 2^w`, as a `Nat` is
(the primitive is stuck on a number at or above `2^w`, as SrcEval's rule F6w is, so nothing is
owed there). `div`, `mod`, `land`, `lor` and `xor` are the `Nat` codes at every width (their
results stay in range). Below width 64 every other operation computes, in 64-bit arithmetic, a
word congruent to the tagged result modulo `2^(w+1)` (which divides `2^64`, so a 64-bit wrap
changes nothing) and reduces it with the *tagged mask* `2^(w+1) − 1`; it never fails. At width 64
such an operation computes the untagged 64-bit result `r` (wrapping, the width's own reduction)
and fails with `natOverflow` unless `r < 2^63`: a `UInt64` has a tagged word only below `2^63`.
Shift amounts are reduced with `bits − 1`. Operands are untagged by a shift even when
immediate, so the code has one shape whatever the operands are. -/

/-- The tagged mask of a width below 64: `(2n + 1) &&& tagMask w = 2 (n mod 2^w) + 1`. -/
def tagMask (w : Src.Width) : Word := UInt64.ofNat (2 * w.size - 1)

/-- The shift amount of width `w` from a tagged count: `(b >>> 1) &&& (bits − 1)`. -/
def wordCount (w : Src.Width) (b : Lir.Arg) : M Lir.Arg := do
  let y ← bin .shr b (.imm 1)
  bin .and y (.imm (UInt64.ofNat (w.bits - 1)))

/-- Width 64's result `r` (untagged): `natOverflow` unless `r < 2^63`, then `x := 2r + 1`. -/
def checked64 (x : VReg) (r : Lir.Arg) : M Unit := do
  check .natOverflow fun ok bad => .br .ugt r (.imm 0x7fffffffffffffff) bad ok
  assign x (retag r)

/-- Count leading zeros of an untagged 64-bit word `u` via `Lir.Rhs.bsr64`: returns `64` when
`u = 0`, else `63 - bsr64 u` (retagged to `2r + 1` when `tagged = true`). -/
def clz64Code (x : VReg) (u : Lir.Arg) (tagged : Bool) : M Unit := do
  let zBlk ← newLabel
  let nzBlk ← newLabel
  let join ← newLabel
  close (.br .eq u (.imm 0) (loc zBlk) (loc nzBlk))
  put zBlk { term := .jump ⟨.loc join, [.imm (if tagged then 129 else 64)]⟩, cold := true }
  let b ← freshReg
  let r ← freshReg
  if tagged then
    let t ← freshReg
    put nzBlk {
      body := [.assign b (.bsr64 u), .assign r (.bin .sub .w64 (.imm 63) (.v b)),
               .assign t (retag (.v r))]
      term := .jump ⟨.loc join, [.v t]⟩
    }
  else
    put nzBlk {
      body := [.assign b (.bsr64 u), .assign r (.bin .sub .w64 (.imm 63) (.v b))]
      term := .jump ⟨.loc join, [.v r]⟩
    }
  openAt join [x]

/-- A width-64 operation that can leave `[0, 2^63)` (and the 9 scalar 64-bit limb-component
primitives), on tagged operands (stage W1 / shared `PrimCore`). -/
def word64 (f : FunId) (x : VReg) (op : Src.WordOp) (as : List Lir.Arg) : M Unit :=
  match op, as with
  | .add, [a, b] => do
    let u ← bin .shr a (.imm 1)
    let v ← bin .shr b (.imm 1)
    checked64 x (← bin .add u v)
  | .sub, [a, b] => do
    let u ← bin .shr a (.imm 1)
    let v ← bin .shr b (.imm 1)
    checked64 x (← bin .sub u v)
  | .mul, [a, b] => do
    let u ← bin .shr a (.imm 1)
    let v ← bin .shr b (.imm 1)
    checked64 x (← bin .mul u v)
  | .shiftLeft, [a, b] => do
    let s ← wordCount .w64 b
    let u ← bin .shr a (.imm 1)
    checked64 x (← bin .shl u s)
  | .complement, [a] => do
    let u ← bin .shr a (.imm 1)
    checked64 x (← bin .xor u (.imm 0xFFFFFFFFFFFFFFFF))
  | .neg, [a] => do
    let u ← bin .shr a (.imm 1)
    checked64 x (← bin .sub (.imm 0) u)
  | .ofNat, [a] => assign x (.arg a)
  | .clz64, [a] => do
    let u ← bin .shr a (.imm 1)
    clz64Code x u true
  | .mulWideLo, [a, b] => do
    let u ← bin .shr a (.imm 1)
    let v ← bin .shr b (.imm 1)
    let lo ← freshReg
    let hi ← freshReg
    emit (.limb lo hi (.mulWide64 u v))
    checked64 x (.v lo)
  | .mulWideHi, [a, b] => do
    let u ← bin .shr a (.imm 1)
    let v ← bin .shr b (.imm 1)
    let lo ← freshReg
    let hi ← freshReg
    emit (.limb lo hi (.mulWide64 u v))
    checked64 x (.v hi)
  | .divWideQ, [hi, lo, d] => do
    let uhi ← bin .shr hi (.imm 1)
    let ulo ← bin .shr lo (.imm 1)
    let ud ← bin .shr d (.imm 1)
    let q ← freshReg
    let r ← freshReg
    emit (.limb q r (.divWide64 uhi ulo ud))
    checked64 x (.v q)
  | .divWideR, [hi, lo, d] => do
    let uhi ← bin .shr hi (.imm 1)
    let ulo ← bin .shr lo (.imm 1)
    let ud ← bin .shr d (.imm 1)
    let q ← freshReg
    let r ← freshReg
    emit (.limb q r (.divWide64 uhi ulo ud))
    checked64 x (.v r)
  | .addCarryLo, [a, b, c] => do
    let ua ← bin .shr a (.imm 1)
    let ub ← bin .shr b (.imm 1)
    let uc ← bin .shr c (.imm 1)
    let s ← freshReg
    let co ← freshReg
    emit (.limb s co (.addCarry64 ua ub uc))
    checked64 x (.v s)
  | .addCarryOut, [a, b, c] => do
    let ua ← bin .shr a (.imm 1)
    let ub ← bin .shr b (.imm 1)
    let uc ← bin .shr c (.imm 1)
    let s ← freshReg
    let co ← freshReg
    emit (.limb s co (.addCarry64 ua ub uc))
    assign x (retag (.v co))
  | .subBorrowLo, [a, b, c] => do
    let ua ← bin .shr a (.imm 1)
    let ub ← bin .shr b (.imm 1)
    let uc ← bin .shr c (.imm 1)
    let d ← freshReg
    let bo ← freshReg
    emit (.limb d bo (.subBorrow64 ua ub uc))
    checked64 x (.v d)
  | .subBorrowOut, [a, b, c] => do
    let ua ← bin .shr a (.imm 1)
    let ub ← bin .shr b (.imm 1)
    let uc ← bin .shr c (.imm 1)
    let d ← freshReg
    let bo ← freshReg
    emit (.limb d bo (.subBorrow64 ua ub uc))
    assign x (retag (.v bo))
  | op, _ => throw (.prim f (.word .w64 op))

/-- The same operations below width 64, on tagged operands: a word congruent to the tagged
result, then the tagged mask. -/
def wordNarrow (f : FunId) (x : VReg) (w : Src.Width) (op : Src.WordOp) (as : List Lir.Arg) : M Unit :=
  match op, as with
  | .add, [a, b] => do
    let s ← bin .add a b
    let t ← bin .sub s (.imm 1)
    assign x (.bin .and .w64 t (.imm (tagMask w)))
  | .sub, [a, b] => do
    let d ← bin .sub a b
    let t ← bin .or d (.imm 1)
    assign x (.bin .and .w64 t (.imm (tagMask w)))
  | .mul, [a, b] => do
    let u ← bin .shr a (.imm 1)
    let c ← bin .sub b (.imm 1)
    let m ← bin .mul u c
    let t ← bin .or m (.imm 1)
    assign x (.bin .and .w64 t (.imm (tagMask w)))
  | .shiftLeft, [a, b] => do
    let s ← wordCount w b
    let c ← bin .sub a (.imm 1)
    let m ← bin .shl c s
    let t ← bin .or m (.imm 1)
    assign x (.bin .and .w64 t (.imm (tagMask w)))
  | .complement, [a] => do
    let t ← bin .xor a (.imm (tagMask w - 1))
    assign x (.bin .and .w64 t (.imm (tagMask w)))
  | .neg, [a] => do
    let t ← bin .sub (.imm 2) a
    assign x (.bin .and .w64 t (.imm (tagMask w)))
  | .ofNat, [a] => assign x (.bin .and .w64 a (.imm (tagMask w)))
  | op, _ => throw (.prim f (.word w op))

/-- A fixed-width word operation on tagged operands (stage W1); the decisions have no
expansion (they are not primitives). -/
def word (f : FunId) (x : VReg) (w : Src.Width) (op : Src.WordOp) (as : List Lir.Arg) : M Unit :=
  match op, as with
  | .div, [a, b] => divMod x .udiv (fun _ => .imm 1) a b
  | .mod, [a, b] => divMod x .urem id a b
  | .land, [a, b] => assign x (.bin .and .w64 a b)
  | .lor, [a, b] => assign x (.bin .or .w64 a b)
  | .xor, [a, b] => do
    let d ← bin .xor a b
    assign x (.bin .or .w64 d (.imm 1))
  | .shiftRight, [a, b] => do
    let s ← wordCount w b
    let r ← bin .shr a s
    assign x (.bin .or .w64 r (.imm 1))
  | .toNat, [a] => assign x (.arg a)
  | .convert w', [a] =>
    if w.bits ≤ w'.bits then assign x (.arg a) else assign x (.bin .and .w64 a (.imm (tagMask w')))
  | op, as => if w = .w64 then word64 f x op as else wordNarrow f x w op as

end Lower

namespace LowerRep

open Lower

/-- Raw 64-bit unsigned division / remainder with `n / 0 = 0` and `n % 0 = n` over full `[0, 2^64)`. -/
def divModRaw64 (x : VReg) (o : Lir.BinOp) (zero : Lir.Arg → Lir.Arg) (a b : Lir.Arg) : M Unit := do
  let nz ← newLabel
  let zBlk ← newLabel
  let join ← newLabel
  close (.br .eq b (.imm 0) (loc zBlk) (loc nz))
  let q ← freshReg
  put nz {
    body := [.assign q (.bin o .w64 a b)]
    term := .jump ⟨.loc join, [.v q]⟩
  }
  put zBlk { term := .jump ⟨.loc join, [zero a]⟩, cold := true }
  openAt join [x]

/-- Emit a raw 64-bit `UInt64` or hardware limb-component operation on raw 64-bit operands,
producing a raw 64-bit result in `x` (zero tagging, zero `natOverflow`). -/
def wordRaw64 (f : FunId) (x : VReg) (op : Src.WordOp) (as : List Lir.Arg) : M Unit :=
  match op, as with
  | .add, [a, b] => assign x (.bin .add .w64 a b)
  | .sub, [a, b] => assign x (.bin .sub .w64 a b)
  | .mul, [a, b] => assign x (.bin .mul .w64 a b)
  | .div, [a, b] => divModRaw64 x .udiv (fun _ => .imm 0) a b
  | .mod, [a, b] => divModRaw64 x .urem id a b
  | .land, [a, b] => assign x (.bin .and .w64 a b)
  | .lor, [a, b] => assign x (.bin .or .w64 a b)
  | .xor, [a, b] => assign x (.bin .xor .w64 a b)
  | .shiftLeft, [a, b] => do
    let s ← bin .and b (.imm 63)
    assign x (.bin .shl .w64 a s)
  | .shiftRight, [a, b] => do
    let s ← bin .and b (.imm 63)
    assign x (.bin .shr .w64 a s)
  | .complement, [a] => assign x (.bin .xor .w64 a (.imm 0xFFFFFFFFFFFFFFFF))
  | .neg, [a] => assign x (.bin .sub .w64 (.imm 0) a)
  | .ofNat, [a] => assign x (.arg a)
  | .toNat, [a] => assign x (.arg a)
  | .convert .w64, [a] => assign x (.arg a)
  | .convert w', [a] => assign x (.bin .and .w64 a (.imm (UInt64.ofNat (w'.size - 1))))
  | .clz64, [a] => clz64Code x a false
  | .mulWideLo, [a, b] => do
    let hi ← freshReg
    emit (.limb x hi (.mulWide64 a b))
  | .mulWideHi, [a, b] => do
    let lo ← freshReg
    emit (.limb lo x (.mulWide64 a b))
  | .divWideQ, [hi, lo, d] => do
    let r ← freshReg
    emit (.limb x r (.divWide64 hi lo d))
  | .divWideR, [hi, lo, d] => do
    let q ← freshReg
    emit (.limb q x (.divWide64 hi lo d))
  | .addCarryLo, [a, b, c] => do
    let co ← freshReg
    emit (.limb x co (.addCarry64 a b c))
  | .addCarryOut, [a, b, c] => do
    let s ← freshReg
    emit (.limb s x (.addCarry64 a b c))
  | .subBorrowLo, [a, b, c] => do
    let bo ← freshReg
    emit (.limb x bo (.subBorrow64 a b c))
  | .subBorrowOut, [a, b, c] => do
    let d ← freshReg
    emit (.limb d x (.subBorrow64 a b c))
  | op, _ => throw (.prim f (.word .w64 op))

end LowerRep

namespace Lower

def primitive (f : FunId) (T : Tables) (x : VReg) (op : Lam.Prim) (as : List Lir.Arg) : M Unit := do
  let bool := fun (c : Lir.Cond) (a b : Lir.Arg) => do
    let some (t, e) := T.bools | throw (.noBool f)
    assign x (.select c .w64 a b (.imm t) (.imm e))
  match op, as with
  | .natAdd, [a, b] =>
    -- (2p+1) + (2q+1 − 1), carry iff p + q ≥ 2^63; subtracting 1 from `b` keeps
    -- accumulator `a` off the two-op dependency chain in loops like `sum-loop`.
    let (a, b) ← match a, b with
      | a, .imm w => pure (a, Lir.Arg.imm (w - 1))
      | .imm w, b => pure (b, Lir.Arg.imm (w - 1))
      | a, b => do pure (a, ← bin .sub b (.imm 1))
    check .natOverflow fun ok bad => .brOvf .addC x a b ok bad
  | .natSub, [a, b] =>
    let d ← bin .sub a b
    let r ← bin .or d (.imm 1)
    assign x (.select .ult .w64 a b (.imm 1) r)
  | .natMul, [a, b] =>
    -- p · 2q, checked by hardware widening `mul` (`brOvf .mulOvf`, OF/CF)
    let mulGen := do
      let u ← untag a
      let t ← bin .sub b (.imm 1)
      let p ← freshReg
      check .natOverflow fun ok bad => .brOvf .mulOvf p u t ok bad
      assign x (.bin .or .w64 (.v p) (.imm 1))
    match a with
    | .imm w =>
      if w == 5 then do
        check .natOverflow fun ok bad => .br .ugt b (.imm 0x7fffffffffffffff) bad ok
        match b with
        | .imm wb => assign x (.arg (.imm (2 * wb - 1)))
        | .v y => assign x (.addr { base := some (.v y), index := some (y, .one), disp := -1 })
      else if w == 7 then do
        check .natOverflow fun ok bad => .br .ugt b (.imm 0x5555555555555555) bad ok
        match b with
        | .imm wb => assign x (.arg (.imm (3 * wb - 2)))
        | .v y => assign x (.addr { base := some (.v y), index := some (y, .two), disp := -2 })
      else mulGen
    | .v ya =>
      match b with
      | .v yb =>
        if ya == yb then do
          check .natOverflow fun ok bad => .br .ugt (.v ya) (.imm 0x16a09e667) bad ok
          let u ← bin .shr (.v ya) (.imm 1)
          let t ← bin .sub (.v ya) (.imm 1)
          let p ← bin .mul u t
          assign x (.bin .or .w64 p (.imm 1))
        else mulGen
      | _ => mulGen
  | .natDiv, [a, b] => divMod x .udiv (fun _ => .imm 1) a b
  | .natMod, [a, b] => divMod x .urem id a b
  | .natBeq, [a, b] => bool .eq a b
  | .natBle, [a, b] => bool .ule a b
  | .natBlt, [a, b] => bool .ult a b
  | .natLand, [a, b] => assign x (.bin .and .w64 a b)
  | .natLor, [a, b] => assign x (.bin .or .w64 a b)
  | .natXor, [a, b] =>
    let d ← bin .xor a b
    assign x (.bin .or .w64 d (.imm 1))
  | .natPred, [a] =>
    let d ← bin .sub a (.imm 2)
    assign x (.select .eq .w64 a (.imm 1) (.imm 1) d)
  | .natShr, [a, b] =>
    let y ← untag b
    let s ← bin .shr a y
    let r ← bin .or s (.imm 1)
    assign x (.select .ugt .w64 y (.imm 63) (.imm 1) r)
  | .natShl, [a, b] =>
    -- 2p · 2^y, which overflows iff p ≠ 0 and y > 63 or a bit is lost
    let y ← untag b
    let t ← bin .sub a (.imm 1)
    let s ← bin .shl t y
    let back ← bin .shr s y
    let c1 ← temp (.test .ne .w64 back t)
    let c2 ← temp (.test .ugt .w64 y (.imm 63))
    let c3 ← bin .or c1 c2
    let c4 ← temp (.test .ne .w64 t (.imm 0))
    let c ← bin .and c3 c4
    check .natOverflow fun ok bad => .br .ne c (.imm 0) bad ok
    assign x (.bin .or .w64 s (.imm 1))
  | .natPow, [a, b] => emit (.call [x] T.natPow [a, b])
  | .natGcd, [a, b] => emit (.call [x] T.natGcd [a, b])
  | .word w o, as => word f x w o as
  | op, _ => throw (.prim f op)

/-- The comparison a fused `Bool` switch branches on. -/
def compareOf : Lam.Prim → Option Lir.Cond
  | .natBeq => some .eq
  | .natBle => some .ule
  | .natBlt => some .ult
  | _ => none

/-! ## Raw 64-bit words (the reference-counted route's word layout)

A register `Tables.rawVar` names holds the untagged word `n` of a `UInt64` (`n < 2^64`): no
tag, no `natOverflow`. A 64-bit word operation that reads or writes one runs on raw operands
(`LowerRep.wordRaw64`): a raw register as it is, a tagged one untagged (`w >>> 1`), a literal
below `2^64` as its word. Its result goes to a raw destination as it is, and to a tagged one
through `checked64` (`natOverflow` at or above `2^63`, the tagged word's limit). -/

/-- How a word operation reads an operand: a raw register and a literal raw (`rawOperand`), a
tagged register as it is (then untagged by `untagAt`). -/
def rawFlag (T : Tables) (f : FunId) : Fir.Arg → Bool
  | .var y => T.rawVar f y
  | _ => true

/-- Untag the operands read from tagged registers (`w >>> 1`). -/
def untagAt (T : Tables) (f : FunId) : List Fir.Arg → List Lir.Arg → M (List Lir.Arg)
  | a :: as, la :: las => do
    let u ← if rawFlag T f a then pure la else bin .shr la (.imm 1)
    let us ← untagAt T f as las
    pure (u :: us)
  | _, _ => pure []

/-- Whether a primitive binding takes the raw path: a 64-bit word operation with a raw
destination or a raw operand. -/
def rawPrim (T : Tables) (f : FunId) (x : VReg) : Lam.Prim → List Fir.Arg → Bool
  | .word .w64 _, as => T.rawVar f x || as.any fun
    | .var y => T.rawVar f y
    | _ => false
  | _, _ => false

/-- The raw path of a 64-bit word operation: the operation on raw operands, its result raw, or
tagged through `checked64`; `false` if the block ended with `fail natOverflow` (a literal at or
above `2^64`). -/
def rawWord (f : FunId) (T : Tables) (x : VReg) (op : Src.WordOp) (as : List Fir.Arg) : M Bool :=
  withOperandsAt f (as.map (rawFlag T f)) as fun las => do
    let us ← untagAt T f as las
    if T.rawVar f x then LowerRep.wordRaw64 f x op us
    else do
      let r ← freshReg
      LowerRep.wordRaw64 f r op us
      checked64 x (.v r)

/-- A primitive binding's code: the raw path where `rawPrim` says, today's otherwise. -/
def rawPrimCode (f : FunId) (T : Tables) (x : VReg) : Lam.Prim → List Fir.Arg → M Bool
  | .word .w64 op, as => rawWord f T x op as
  | op, as => withOperands f as (primitive f T x op)

/-! ## Allocation and projection -/

def isNatKey (T : Tables) (k : Key.CtorKey) : Bool :=
  T.known.natZero == some k || T.known.natSucc == some k

/-- The immortal bump allocation. -/
def alloc (f : FunId) (T : Tables) (x : VReg) (c : Fir.CtorInfo) (as : List Lir.Arg) : M Unit := do
  if isNatKey T c.key then throw (.layout f "a Nat constructor cell (Nat values are literals)")
  if c.nscalar != 0 then throw (.layout f "scalar fields are Phase 2")
  if as.length != c.arity then throw (.form f s!"an allocation of {as.length} fields for {c.arity}")
  -- the switch lowering reads tags from the table (`Cfg.WellFormed` checks this too)
  if Fir.CtorInfo.ofKey T.ctors c.key != some c then throw (.form f "allocation info is not the table's")
  -- the bump pointer is written to `x` before the fields are stored
  if as.any (· == .v x) then throw (.form f "an allocation reads the variable it defines")
  if c.tag > maxTag then throw (.layout f s!"constructor tag {c.tag} above {maxTag}")
  if c.fieldless then assign x (.arg (.imm (ctor0Word c.tag)))
  else
    if c.arity > maxFields then throw (.layout f s!"{c.arity} fields, above {maxFields}")
    assign x (.load .w64 .zero (ctxAt bumpOff))
    let e ← freshReg
    assign e (.addr (mem x (cellBytes c.arity)))
    let l ← temp (.load .w64 .zero (ctxAt limitOff))
    check .heap fun ok bad => .br .ugt (.v e) l bad ok
    emit (.store .w64 (ctxAt bumpOff) (.v e))
    emit (.store .w32 (mem x 0) (.imm (UInt64.ofNat (headerLow c.arity 0 c.tag))))
    emit (.store .w32 (mem x 4) (.imm (UInt64.ofNat immortalRc)))
    as.zipIdx.forM fun (a, i) => emit (.store .w64 (mem x (fieldOffset i)) a)

def proj (f : FunId) (T : Tables) (x y : VReg) (c : Key.CtorKey) (i : Nat) : M Unit := do
  if T.known.natSucc == some c then
    if i == 0 then assign x (.bin .sub .w64 (.v y) (.imm 2))
    else throw (.form f "a projection past the Nat successor's field")
  else if T.known.natZero == some c then throw (.form f "a projection of Nat.zero")
  else
    match Fir.CtorInfo.ofKey T.ctors c with
    | some info =>
      if i < info.arity then assign x (.load .w64 .zero (mem y (fieldOffset i)))
      else throw (.form f s!"field {i} of a constructor with {info.arity}")
    | none => throw (.form f "a projection key outside the table")

/-! ## Instructions -/

/-- One instruction; `false` if the block ended with `fail natOverflow`. -/
def instr (f : FunId) (T : Tables) : Cfg.Instr → M Bool
  | .bind x (.fir (.arg a)) => withOperandsAt f [T.rawVar f x] [a] fun
    | [a] => assign x (.arg a)
    | _ => pure ()
  | .bind x (.fir (.prim op as)) =>
    if rawPrim T f x op as then rawPrimCode f T x op as else withOperands f as (primitive f T x op)
  | .bind x (.fir (.call g as)) => withOperandsAt f (T.rawParams g 0) as fun as => emit (.call [x] g as)
  | .bind _ (.fir (.ctor ..)) => throw (.form f "a Fir constructor in Cfg")
  | .bind _ (.fir (.proj ..)) => throw (.form f "a Fir projection in Cfg")
  | .bind x (.alloc c as _) => withOperands f as (alloc f T x c)
  | .bind x (.proj y c i) => do proj f T x y c i; pure true

def instrs (f : FunId) (T : Tables) : List Cfg.Instr → M Bool
  | [] => pure true
  | i :: is => do if ← instr f T i then instrs f T is else pure false

/-! ## Terminators -/

/-- A Cfg edge from block `src`: to the target's chunk, or to a new cold
`fail natOverflow` block if an argument has no word. -/
def edge (f : FunId) (T : Tables) (src : Nat) (e : Cfg.Edge) : M PEdge := do
  unless e.back == decide (e.target ≤ src) do throw (.edgeOrder f src)
  match ← operandsAt f (T.rawParams f e.target) e.args with
  | some as => pure ⟨.blk e.target, as⟩
  | none => pure (loc (← coldBlock (.fail .natOverflow)))

/-- Tests in order, each `x = w` taking its edge; `els` if none holds. -/
def chain (x : Lir.Arg) : List (Lir.Arg × PEdge) → PEdge → M Unit
  | [], els => close (.jump els)
  | [(w, e)], els => close (.br .eq x w e els)
  | (w, e) :: rest, els => do
    let l ← newLabel
    close (.br .eq x w e (loc l))
    openAt l
    chain x rest els

/-- The last element and the ones before it. -/
def unsnoc {α : Type} : List α → Option (List α × α)
  | [] => none
  | [a] => some ([], a)
  | a :: as => (unsnoc as).map fun (init, last) => (a :: init, last)

/-- A chain whose `else` is the default, or else the last alternative. -/
def chainOr (x : Lir.Arg) (tests : List (Lir.Arg × PEdge)) : Option PEdge → M Unit
  | some d => chain x tests d
  | none =>
    match unsnoc tests with
    | some (init, (_, last)) => chain x init last
    | none => close .trap

inductive KeyKind where
  | zero
  | succ
  | imm (w : Word)
  | cell (tag : Nat)
  deriving Inhabited

def keyKind (T : Tables) (k : Key.CtorKey) : Option KeyKind :=
  if T.known.natZero == some k then some .zero
  else if T.known.natSucc == some k then some .succ
  else (Fir.CtorInfo.ofKey T.ctors k).map fun c =>
    if c.fieldless then .imm (ctor0Word c.tag) else .cell c.tag

def KeyKind.isNat : KeyKind → Bool
  | .zero | .succ => true
  | _ => false

/-- An alternative's key kind and lowered edge. -/
def switchAlt (f : FunId) (T : Tables) (src : Nat) (ke : Key.CtorKey × Cfg.Edge) : M (KeyKind × PEdge) := do
  let some kind := keyKind T ke.1 | throw (.switch f src "a key outside the constructor table")
  pure (kind, ← edge f T src ke.2)

/-- Whether a lowered alternative has the zero key. -/
def isZero : KeyKind × PEdge → Bool
  | (.zero, _) => true
  | _ => false

/-- The first alternative of a `Nat` switch with the zero key. -/
def zeroEdge (es : List (KeyKind × PEdge)) : Option PEdge := (es.find? isZero).map (·.2)

/-- Whether a lowered alternative has the successor key. -/
def isSucc : KeyKind × PEdge → Bool
  | (.succ, _) => true
  | _ => false

/-- The first alternative of a `Nat` switch with the successor key. -/
def succEdge (es : List (KeyKind × PEdge)) : Option PEdge := (es.find? isSucc).map (·.2)

/-- A switch on `Nat` keys: one zero test. -/
def natSwitch (x : VReg) (es : List (KeyKind × PEdge)) (dd : Option PEdge) : M Unit :=
  match zeroEdge es, succEdge es, dd with
  | some ez, some es, _ => close (.br .eq (.v x) (.imm 1) ez es)
  | some ez, none, some ed => close (.br .eq (.v x) (.imm 1) ez ed)
  | none, some es, some ed => close (.br .eq (.v x) (.imm 1) ed es)
  | some e, none, none | none, some e, none | none, none, some e => close (.jump e)
  | none, none, none => close .trap

/-- The test on a field-less constructor's word. -/
def immTest : KeyKind × PEdge → Option (Lir.Arg × PEdge)
  | (.imm w, e) => some (Lir.Arg.imm w, e)
  | _ => none

/-- The tests on field-less constructors' words. -/
def immTests (es : List (KeyKind × PEdge)) : List (Lir.Arg × PEdge) := es.filterMap immTest

/-- The test on a cell's tag. -/
def cellTest : KeyKind × PEdge → Option (Lir.Arg × PEdge)
  | (.cell t, e) => some (Lir.Arg.imm (UInt64.ofNat t), e)
  | _ => none

/-- The tests on cells' tags. -/
def cellTests (es : List (KeyKind × PEdge)) : List (Lir.Arg × PEdge) := es.filterMap cellTest

/-- A cell's tag, loaded into a fresh register. -/
def loadTag (x : VReg) : M Lir.Arg := temp (.load .w16 .zero (mem x tagOffset))

/-- A switch on other keys: a chain on words, a chain on loaded tags, or
the low bit first and both. -/
def tagSwitch (x : VReg) (es : List (KeyKind × PEdge)) (dd : Option PEdge) : M Unit :=
  match cellTests es, immTests es, dd with
  | [], imms, dd => chainOr (.v x) imms dd
  | cells, [], none => do chainOr (← loadTag x) cells none
  | cells, imms, dd => do
    -- the low bit first: an even word is a cell
    let p ← newLabel
    let i ← newLabel
    close (.br .tz (.v x) (.imm 1) (loc p) (loc i))
    openAt p
    chainOr (← loadTag x) cells dd
    openAt i
    chainOr (.v x) imms dd

def switch (f : FunId) (T : Tables) (src : Nat) (x : VReg) (alts : List (Key.CtorKey × Cfg.Edge))
    (d : Option Cfg.Edge) : M Unit := do
  let es ← alts.mapM (switchAlt f T src)
  let dd ← d.mapM (edge f T src)
  let nats := es.filter (·.1.isNat)
  if !nats.isEmpty then
    unless nats.length == es.length do throw (.switch f src "Nat keys mixed with other keys")
    natSwitch x es dd
  else tagSwitch x es dd

/-- The edge a `switch` on `Bool` takes for the key `k`: its first
alternative, else the default. -/
def boolEdge (alts : List (Key.CtorKey × Cfg.Edge)) (d : Option Cfg.Edge) (k : Option Key.CtorKey) :
    Option Cfg.Edge :=
  match (alts.find? fun (k', _) => k == some k').map (·.2) with
  | some e => some e
  | none => d

/-- Close a fused switch's block with its branch on the two lowered
edges. -/
def fusedClose (c : Lir.Cond) (a b : Lir.Arg) (te fe : Option PEdge) : M Unit :=
  match te, fe with
  | some t, some e => close (.br c a b t e)
  | some t, none | none, some t => close (.jump t)
  | none, none => close .trap

/-- A switch on the `Bool` a comparison just produced, as the branch. -/
def fusedSwitch (f : FunId) (T : Tables) (src : Nat) (c : Lir.Cond) (a b : Lir.Arg)
    (alts : List (Key.CtorKey × Cfg.Edge)) (d : Option Cfg.Edge) : M Unit := do
  let te ← (boolEdge alts d T.known.boolTrue).mapM (edge f T src)
  let fe ← (boolEdge alts d T.known.boolFalse).mapM (edge f T src)
  fusedClose c a b te fe

def term (f : FunId) (T : Tables) (src : Nat) : Cfg.Term → M Unit
  | .jump e => do close (.jump (← edge f T src e))
  | .switch x alts d => switch f T src x alts d
  | .ret a => do
    let _ ← withOperandsAt f [T.rawRet f] [a] fun
      | [a] => close (.ret a)
      | _ => pure ()
  | .tcall g as => do
    let _ ← withOperandsAt f (T.rawParams g 0) as fun as => close (.tail g as)
  | .trap => close .trap

/-! ## Blocks and functions -/

/-- The variables an instruction reads. -/
def instrUses : Cfg.Instr → List VReg
  | .bind _ r => Cfg.Check.rhsVars r

/-- The variables a block reads, each read once per occurrence. -/
def blockUses (b : Cfg.Block) : List VReg := b.body.flatMap instrUses ++ Cfg.Check.termVars b.term

/-- Uses of each variable in a function (instructions and terminators). -/
def useCounts (fd : Cfg.Fun) : Src.NatMap Nat :=
  (fd.blocks.flatMap blockUses).foldl (fun m x => m.insert x (m.getD x 0 + 1)) .leaf

/-- A block ending in a `Bool` comparison whose only use is the block's
`switch` on `Bool` keys: the instructions before it, and the comparison. -/
def fusable (T : Tables) (uses : Src.NatMap Nat) (b : Cfg.Block) :
    Option (List Cfg.Instr × Lir.Cond × Fir.Arg × Fir.Arg) :=
  match unsnoc b.body, b.term with
  | some (init, .bind x (.fir (.prim op [a, a']))), .switch y alts _ =>
    match compareOf op with
    | some c =>
      let bools := alts.all fun (k, _) => T.known.boolTrue == some k || T.known.boolFalse == some k
      if x == y && uses.getD x 0 == 1 && bools then some (init, c, a, a') else none
    | none => none
  | _, _ => none

/-- A fused block's end: the comparison's operands, then the branch. -/
def fusedEnd (f : FunId) (T : Tables) (src : Nat) (b : Cfg.Block) (c : Lir.Cond) (a a' : Fir.Arg) : M Unit := do
  match ← operands f [a, a'] with
  | some [a, a'] =>
    match b.term with
    | .switch _ alts d => fusedSwitch f T src c a a' alts d
    | t => term f T src t
  | _ => close (.fail .natOverflow)

/-- A Cfg block's code, in the open block. -/
def blockCode (f : FunId) (T : Tables) (uses : Src.NatMap Nat) (src : Nat) (b : Cfg.Block) : M Unit :=
  match fusable T uses b with
  | some (init, c, a, a') => do if ← instrs f T init then fusedEnd f T src b c a a'
  | none => do if ← instrs f T b.body then term f T src b.term

/-- A Cfg block's chunk (from label 0; `entry`: it is the function's entry,
whose parameters are the function's). -/
def block (f : FunId) (T : Tables) (uses : Src.NatMap Nat) (src : Nat) (entry : Bool)
    (b : Cfg.Block) : M Unit := do
  openAt 0 (if entry then [] else b.params.map (·.1))
  blockCode f T uses src b

/-- The chunk's blocks in label order. -/
def chunkBlocks (f : FunId) (st : St) : Except Error (List PBlock) := do
  -- every label below `next` (what `chunkBlocks` reads), the last block closed
  unless st.done.toList.all (·.1 < st.next) && (st.done.get? st.cur).isSome do
    throw (.internal f "a chunk label past the next free one, or its last block open")
  (List.range st.next).mapM fun j =>
    match st.done.get? j with
    | some b => pure b
    | none => throw (.internal f s!"chunk label {j} left open")

/-- Every block's chunk, threading the register supply. -/
def chunks (f : FunId) (T : Tables) (uses : Src.NatMap Nat) (merged : Bool) :
    List (Cfg.Block × Nat) → VReg → Except Error (List (List PBlock) × VReg)
  | [], fresh => pure ([], fresh)
  | (b, i) :: bs, fresh => do
    let ((), st) ← (block f T uses i (merged && i == 0) b).run { fresh }
    let blocks ← chunkBlocks f st
    let (rest, fresh) ← chunks f T uses merged bs st.fresh
    pure (blocks :: rest, fresh)

/-! ## Labels -/

def resolveTgt (f : FunId) (off : Nat) (starts : Src.NatMap Nat) : Tgt → Except Error Label
  | .loc j => pure (off + j)
  | .blk b =>
    match starts.get? b with
    | some l => pure l
    | none => throw (.missingBlock f b)

def resolveEdge (f : FunId) (off : Nat) (starts : Src.NatMap Nat) (e : PEdge) : Except Error Lir.Edge := do
  pure { target := ← resolveTgt f off starts e.tgt, args := e.args }

def resolveTerm (f : FunId) (off : Nat) (starts : Src.NatMap Nat) : PTerm → Except Error Lir.Term
  | .jump e => do pure (.jump (← resolveEdge f off starts e))
  | .br c a b t e => do pure (.br c .w64 a b (← resolveEdge f off starts t) (← resolveEdge f off starts e))
  | .brOvf o x a b ok ovf => do
    pure (.brOvf o x a b (← resolveEdge f off starts ok) (← resolveEdge f off starts ovf))
  | .ret a => pure (.ret [a])
  | .tail g as => pure (.tail g as)
  | .fail r => pure (.fail r)
  | .trap => pure .trap

def resolveBlock (f : FunId) (off : Nat) (starts : Src.NatMap Nat) (b : PBlock) : Except Error Lir.Block := do
  pure { params := b.params, body := b.body.toArray, term := ← resolveTerm f off starts b.term, cold := b.cold }

/-- The first label of each chunk, from `first`, and the label after the
last. -/
def chunkStarts (first : Nat) (cs : List (List PBlock)) : Src.NatMap Nat × Nat :=
  cs.zipIdx.foldl (fun (m, l) (c, i) => (m.insert i l, l + c.length)) (.leaf, first)

def resolveChunks (f : FunId) (starts : Src.NatMap Nat) : List (List PBlock × Nat) → Except Error (List Lir.Block)
  | [] => pure []
  | (c, i) :: cs => do
    let off := starts.getD i 0
    let bs ← c.mapM (resolveBlock f off starts)
    pure (bs ++ (← resolveChunks f starts cs))

/-! ## Reachability -/

/-- Blocks reachable from label 0 (a worklist; each label is queued once,
so `n + 1` steps suffice). -/
def reach (succ : Src.NatMap (List Label)) : Nat → List Label → Src.NatSet → Src.NatSet
  | 0, _, seen => seen
  | _, [], seen => seen
  | fuel + 1, l :: ls, seen =>
    let (seen, new) := (succ.getD l []).foldl
      (fun (s, acc) t => if s.contains t then (s, acc) else (s.insert t, t :: acc)) (seen, [])
    reach succ fuel (new ++ ls) seen

/-- The labels reached from label 0. -/
def reachable (blocks : List Lir.Block) : Src.NatSet :=
  let succ : Src.NatMap (List Label) := Src.NatMap.ofDense (blocks.map (·.term.succs))
  reach succ (blocks.length + 1) [0] (Src.NatSet.ofList [0])

/-- Every successor of a reached block is reached: what `prune` needs of
`seen` (`function` checks it rather than relying on `reach`'s step
bound). -/
def reachClosed (blocks : List Lir.Block) (seen : Src.NatSet) : Bool :=
  blocks.zipIdx.all fun (b, l) => !seen.contains l || b.term.succs.all seen.contains

/-- Keep the blocks in `seen`, in order, renumbering the edges. -/
def pruneWith (seen : Src.NatSet) (blocks : List Lir.Block) : List Lir.Block :=
  let kept := blocks.zipIdx.filter fun (_, l) => seen.contains l
  let rank : Src.NatMap Label := Src.NatMap.ofList (kept.zipIdx.map fun ((_, l), r) => (l, r))
  kept.map fun (b, _) =>
    { b with term := b.term.setEdges (b.term.edges.map fun e => { e with target := rank.getD e.target 0 }) }

/-- Drop the blocks no path from the entry reaches, keeping the order of the
rest (so forward edges stay forward and back edges backward). -/
def prune (blocks : List Lir.Block) : List Lir.Block := pruneWith (reachable blocks) blocks

/-! ## Functions -/

/-- The largest variable a function defines. -/
def maxVar (fd : Cfg.Fun) : Nat := (fd.blocks.flatMap Cfg.Check.blockDefs).foldl max 0

/-- The first block with an edge whose back flag disagrees with the label
order (every block, lowered or not: Cfg's step bound needs them all). -/
def misordered (fd : Cfg.Fun) : Option Nat :=
  (fd.blocks.zipIdx.find? fun (b, i) => !(b.term.edges.all fun e => e.back == decide (e.target ≤ i))).map (·.2)

/-- A function's parameters and its blocks before pruning: the fresh entry
block (if block 0 has predecessors), then each Cfg block's chunk. -/
def functionRaw (T : Tables) (f : FunId) (fd : Cfg.Fun) : Except Error (List VReg × List Lir.Block) := do
  let some b0 := fd.blocks.head? | throw (.missingBlock f 0)
  if let some b := misordered fd then throw (.edgeOrder f b)
  -- no edge enters block 0: it is the Lir entry itself
  let merged := !(fd.blocks.any fun b => b.term.edges.any (·.target == 0))
  let supply := max fd.vars (maxVar fd + 1)
  let arity := b0.params.length
  let (params, supply) :=
    if merged then (b0.params.map (·.1), supply)
    else ((List.range arity).map (supply + ·), supply + arity)
  let uses := useCounts fd
  let (cs, _) ← chunks f T uses merged fd.blocks.zipIdx supply
  let (starts, _) := chunkStarts (if merged then 0 else 1) cs
  let body ← resolveChunks f starts cs.zipIdx
  let entry : List Lir.Block :=
    if merged then [] else [{ term := .jump { target := starts.getD 0 1, args := params.map .v } }]
  pure (params, entry ++ body)

def function (T : Tables) (f : FunId) (fd : Cfg.Fun) (conv : Lir.Conv) : Except Error Lir.Func := do
  let (params, raw) ← functionRaw T f fd
  let seen := reachable raw
  unless reachClosed raw seen do throw (.internal f "a reached block has an unreached successor")
  pure (Lir.Func.splitCriticalEdges
    { name := s!"f{f}", params, results := 1, blocks := (pruneWith seen raw).toArray, conv })

/-- A root's symbol: `cx_` and its name, with characters outside
`[A-Za-z0-9_]` replaced by `_` (and `init`, `cx_init`'s, renamed). -/
def symbolOf (name : String) : String :=
  let clean := String.ofList (name.toList.map fun c => if c.isAlphanum || c == '_' then c else '_')
  if clean == "init" then "cx_root_init" else s!"cx_{clean}"

def functions (T : Tables) (P : Cfg.Program) (roots : List (FunId × String)) :
    List Nat → Except Error (List Lir.Func)
  | [] => pure []
  | f :: fs => do
    let some fd := P.fun? f | throw (.missingFun f)
    let conv := match roots.lookup f with
      | some s => .sysvExport s
      | none => .internal
    pure ((← function T f fd conv) :: (← functions T P roots fs))

end Lower

/-! ## DR1 / DR4 Static String Collection, `.rodata` Table & Hoisting (`LowerStr`)

Collects distinct string literals from a `Cfg.Program` in deterministic order, builds
their immortal `.rodata` section (`X86.ELFRodata.RodataTable.addString`, `rc = 0x80000000`,
`tag = 0x7F02`, `scan = 0`), and provides `hoistStrings` so `Rt.lower` lowers programs
with string literals via position-independent `Rt.Rc.Array.strLitProc` materializers
while keeping `Rt.Lower.*` completely untouched for `Cfg.Rc`. -/

namespace LowerStr

open Lower

def addStr (acc : List String) (s : String) : List String :=
  if acc.contains s then acc else acc ++ [s]

def collectArg (acc : List String) : Fir.Arg → List String
  | .lit (.str s) => addStr acc s
  | _ => acc

def collectArgs (acc : List String) (as : List Fir.Arg) : List String :=
  as.foldl collectArg acc

def collectRhs (acc : List String) : Own.Rhs → List String
  | .fir (.arg a) => collectArg acc a
  | .fir (.ctor _ as) | .fir (.prim _ as) | .fir (.call _ as) => collectArgs acc as
  | .fir (.proj ..) => acc
  | .alloc _ as _ => collectArgs acc as
  | .proj .. => acc

def collectInstr (acc : List String) : Cfg.Instr → List String
  | .bind _ r => collectRhs acc r

def collectEdge (acc : List String) (e : Cfg.Edge) : List String :=
  collectArgs acc e.args

def collectTerm (acc : List String) : Cfg.Term → List String
  | .jump e => collectEdge acc e
  | .switch _ alts d =>
    let a1 := alts.foldl (fun s (_, e) => collectEdge s e) acc
    match d with
    | some e => collectEdge a1 e
    | none => a1
  | .ret a => collectArg acc a
  | .tcall _ as => collectArgs acc as
  | .trap => acc

def collectBlock (acc : List String) (b : Cfg.Block) : List String :=
  collectTerm (b.body.foldl collectInstr acc) b.term

def collectFun (acc : List String) (fd : Cfg.Fun) : List String :=
  fd.blocks.foldl collectBlock acc

/-- All distinct string literals occurring in functions `0 ..< P.size` of `P`, in deterministic order. -/
def collectStrings (P : Cfg.Program) : List String :=
  (List.range P.size).foldl (init := []) fun acc f =>
    match P.fun? f with
    | some fd => collectFun acc fd
    | none => acc

/-- Build the `.rodata` section table and per-string byte offsets for `strs` (`cx_str_0`, ...). -/
def buildStringRodata (strs : List String) : X86.ELFRodata.RodataTable × List (String × Nat) :=
  strs.zipIdx.foldl (init := (X86.ELFRodata.RodataTable.empty, [])) fun (tbl, offs) (s, i) =>
    let (tbl', off) := tbl.addString s!"cx_str_{i}" s
    (tbl', offs ++ [(s, off)])

/-- Kernel-evaluable version of `buildStringRodata` (zero `ByteArray` copies on `Recheck.run`). -/
def buildStringRodataK (strs : List String) : X86.ELFRodata.RodataTable × List (String × Nat) :=
  let (tbl, offs) :=
    strs.zipIdx.foldl (init := (X86.ELFRodata.RodataTableK.empty, [])) fun (tbl, offs) (s, i) =>
      let (tbl', off) := tbl.addString s!"cx_str_{i}" s
      (tbl', offs ++ [(s, off)])
  (tbl.toRodataTable, offs)

def hoistArg (strFns : List (String × FunId)) (fresh : VReg) :
    Fir.Arg → List Cfg.Instr × Fir.Arg × VReg
  | .lit (.str s) =>
    match strFns.lookup s with
    | some fnId => ([.bind fresh (.fir (.call fnId []))], .var fresh, fresh + 1)
    | none => ([], .lit (.str s), fresh)
  | a => ([], a, fresh)

def hoistArgs (strFns : List (String × FunId)) (fresh : VReg) :
    List Fir.Arg → List Cfg.Instr × List Fir.Arg × VReg
  | [] => ([], [], fresh)
  | a :: as =>
    let (pre1, a', f1) := hoistArg strFns fresh a
    let (pre2, as', f2) := hoistArgs strFns f1 as
    (pre1 ++ pre2, a' :: as', f2)

def hoistRhs (strFns : List (String × FunId)) (fresh : VReg) :
    Own.Rhs → List Cfg.Instr × Own.Rhs × VReg
  | .fir (.arg a) =>
    let (pre, a', f') := hoistArg strFns fresh a
    (pre, .fir (.arg a'), f')
  | .fir (.prim op as) =>
    let (pre, as', f') := hoistArgs strFns fresh as
    (pre, .fir (.prim op as'), f')
  | .fir (.call g as) =>
    let (pre, as', f') := hoistArgs strFns fresh as
    (pre, .fir (.call g as'), f')
  | .fir (.ctor c as) =>
    let (pre, as', f') := hoistArgs strFns fresh as
    (pre, .fir (.ctor c as'), f')
  | .alloc c as k =>
    let (pre, as', f') := hoistArgs strFns fresh as
    (pre, .alloc c as' k, f')
  | r => ([], r, fresh)

def hoistInstr (strFns : List (String × FunId)) (fresh : VReg) :
    Cfg.Instr → List Cfg.Instr × VReg
  | .bind x r =>
    let (pre, r', f') := hoistRhs strFns fresh r
    (pre ++ [.bind x r'], f')

def hoistInstrs (strFns : List (String × FunId)) (fresh : VReg) :
    List Cfg.Instr → List Cfg.Instr × VReg
  | [] => ([], fresh)
  | i :: is =>
    let (is1, f1) := hoistInstr strFns fresh i
    let (is2, f2) := hoistInstrs strFns f1 is
    (is1 ++ is2, f2)

def hoistEdge (strFns : List (String × FunId)) (fresh : VReg) (e : Cfg.Edge) :
    List Cfg.Instr × Cfg.Edge × VReg :=
  let (pre, as', f') := hoistArgs strFns fresh e.args
  (pre, { e with args := as' }, f')

def hoistAlts (strFns : List (String × FunId)) (fresh : VReg) :
    List (Key.CtorKey × Cfg.Edge) → List Cfg.Instr × List (Key.CtorKey × Cfg.Edge) × VReg
  | [] => ([], [], fresh)
  | (k, e) :: rest =>
    let (pre1, e', f1) := hoistEdge strFns fresh e
    let (pre2, rest', f2) := hoistAlts strFns f1 rest
    (pre1 ++ pre2, (k, e') :: rest', f2)

def hoistOptEdge (strFns : List (String × FunId)) (fresh : VReg) :
    Option Cfg.Edge → List Cfg.Instr × Option Cfg.Edge × VReg
  | none => ([], none, fresh)
  | some e =>
    let (pre, e', f') := hoistEdge strFns fresh e
    (pre, some e', f')

def hoistTerm (strFns : List (String × FunId)) (fresh : VReg) :
    Cfg.Term → List Cfg.Instr × Cfg.Term × VReg
  | .jump e =>
    let (pre, e', f') := hoistEdge strFns fresh e
    (pre, .jump e', f')
  | .switch x alts d =>
    let (pre1, alts', f1) := hoistAlts strFns fresh alts
    let (pre2, d', f2) := hoistOptEdge strFns f1 d
    (pre1 ++ pre2, .switch x alts' d', f2)
  | .ret a =>
    let (pre, a', f') := hoistArg strFns fresh a
    (pre, .ret a', f')
  | .tcall g as =>
    let (pre, as', f') := hoistArgs strFns fresh as
    (pre, .tcall g as', f')
  | .trap => ([], .trap, fresh)

def hoistBlock (T : Tables) (uses : Src.NatMap Nat) (strFns : List (String × FunId))
    (fresh : VReg) (b : Cfg.Block) : Cfg.Block × VReg :=
  match fusable T uses b, unsnoc b.body with
  | some _, some (init, cmp) =>
    let (init', f1) := hoistInstrs strFns fresh init
    let (termPre, term', f2) := hoistTerm strFns f1 b.term
    let (cmp', f3) := hoistInstr strFns f2 cmp
    ({ b with body := init' ++ termPre ++ cmp', term := term' }, f3)
  | _, _ =>
    let (body', f1) := hoistInstrs strFns fresh b.body
    let (termPre, term', f2) := hoistTerm strFns f1 b.term
    ({ b with body := body' ++ termPre, term := term' }, f2)

def hoistBlocks (T : Tables) (uses : Src.NatMap Nat) (strFns : List (String × FunId))
    (fresh : VReg) : List Cfg.Block → List Cfg.Block × VReg
  | [] => ([], fresh)
  | b :: bs =>
    let (b', f1) := hoistBlock T uses strFns fresh b
    let (bs', f2) := hoistBlocks T uses strFns f1 bs
    (b' :: bs', f2)

def hoistFun (T : Tables) (strFns : List (String × FunId)) (fd : Cfg.Fun) : Cfg.Fun :=
  let uses := useCounts fd
  let supply := max fd.vars (maxVar fd + 1)
  let (blocks', supply') := hoistBlocks T uses strFns supply fd.blocks
  { fd with vars := supply', blocks := blocks' }

def hoistStrings (P : Cfg.Program) (strFns : List (String × FunId)) : Cfg.Program :=
  let T := tables P
  let funs' := (List.range P.size).foldl (init := P.funs) fun m f =>
    match P.fun? f with
    | some fd => m.insert f (hoistFun T strFns fd)
    | none => m
  { P with funs := funs' }

end LowerStr

/-- Distinct string literals occurring in `P`. -/
def lowerStrs (P : Cfg.Program) : List String :=
  LowerStr.collectStrings P

/-- Mapping from each distinct string literal in `P` to its `strLitProc` `FunId` (`P.size + 3 + i`). -/
def lowerStrFns (P : Cfg.Program) : List (String × FunId) :=
  (lowerStrs P).zipIdx.map fun (s, i) => (s, P.size + 3 + i)

/-- The `strLitProc` materializer functions appended after `rt_nat_gcd` for `P`'s string literals. -/
def lowerStrProcs (P : Cfg.Program) : List Lir.Func :=
  (lowerStrs P).zipIdx.map fun (s, i) => Rt.Rc.Array.strLitProc i s

/-- The Cfg program lowered by `Rt.lower`: identical to `P` when `P` has no string literals,
otherwise `LowerStr.hoistStrings P (lowerStrFns P)`. -/
def lowerCfg (P : Cfg.Program) : Cfg.Program :=
  if (lowerStrs P).isEmpty then P
  else LowerStr.hoistStrings P (lowerStrFns P)

/-- Core lowering body of `Rt.lower`: unchanged Phase 1 lowering when `P` contains no
string literals; hoists string literals to `Rt.Rc.Array.strLitProc` materializers and
populates `.rodata` bytes & symbols when string literals are present. -/
def lowerCore (P : Cfg.Program) (roots : List (FunId × String)) :
    Except Error (List Lir.Func × Option ByteArray × List X86.ELF.RodataSymbol) := do
  let strs := lowerStrs P
  let P' := lowerCfg P
  let funcs ← Lower.functions (Lower.tables P') P' roots (List.range P.size)
  if strs.isEmpty then
    pure (funcs ++ [Procs.cxInit, Procs.natPow, Procs.natGcd], none, [])
  else
    let (rtbl, _) := LowerStr.buildStringRodataK strs
    pure (funcs ++ [Procs.cxInit, Procs.natPow, Procs.natGcd] ++ lowerStrProcs P,
          some rtbl.bytes, rtbl.symbols)

open Lower in
/-- Cfg (the immortal fragment) → Lir, with `cx_init` after the program's
functions, plus DR1/DR4 static string literal lowering when strings occur. -/
def lower (cfg : Config) (P : Cfg.Program) : Except Error Lowered := do
  let some main := P.exports.head? | throw .noExports
  if let some (f, _) := P.funs.toList.find? (P.size ≤ ·.1) then throw (.funRange f)
  let named := P.exports.zipIdx.map fun (f, i) => (f, symbolOf ((cfg.names[i]?).getD s!"root{i}"))
  -- a function exported twice keeps its first name (one wrapper per function)
  let roots := named.map fun (f, s) => (f, (named.lookup f).getD s)
  let res ← lowerCore P roots
  pure { program := { funcs := res.1.toArray, main }
         init := P.size, natPow := P.size + 1, natGcd := P.size + 2, roots
         rodata := res.2.1, rodataExports := res.2.2 }

/-! ## DR2 Stage W2: Raw 64-bit `UInt64`, `box`/`unbox`, `nscalar > 0`, and Zero-Alloc Limb Fusion

`Rt.lowerRep cfg cert P` lowers a `Cfg.Program` under a checked Stage W2 representation
certificate `cert : Fir.Rep.Cert`:

* Variables, parameters, join-point parameters, function returns, and constructor scalar-tail
  fields annotated `.word` live as raw unboxed 64-bit words `[0, 2^64)` in registers and stack
  slots — zero tagging, zero `natOverflow`.
* Crossing `.word → .obj` (uniform/polymorphic positions) allocates a 1-scalar-word cell
  `⟨nobj = 0, nscalar = 1, tag = 0⟩` (`box64`: 16 bytes, `scan = 0`, raw payload at `+8`).
* Crossing `.obj → .word` runs `unbox64` (`if odd then w >>> 1 else load64 [w + 8]`), uniform
  for both boxed 1-scalar-word cells and odd tagged immediates `< 2^63`.
* Constructors with `CtorRep` scalar tails (`nscalar > 0`) emit `headerLow nobj 0 tag` and
  `cellBytes (nobj + nscalar)`, storing raw 64-bit words directly in trailing slots.
* Adjacent pairs of scalar limb-component ops (`mulWideLo`/`mulWideHi`, `divWideQ`/`divWideR`,
  `addCarryLo`/`addCarryOut`, `subBorrowLo`/`subBorrowOut`) fuse directly into a single
  `Lir.Stmt.limb r1 r2 op` with zero heap `Prod` allocation. -/

namespace LowerRep

open Lower

/-- Allocate a 1-scalar-word boxed `UInt64` cell (`nobj = 0, nscalar = 1, tag = 0`, 16 bytes,
`scan = 0`, raw 64-bit word at `+8`). Never fails with `natOverflow`. -/
def box64 (x : VReg) (r : Lir.Arg) : M Unit := do
  let rv ← if r == .v x then temp (.arg r) else pure r
  assign x (.load .w64 .zero (ctxAt bumpOff))
  let e ← freshReg
  assign e (.addr (mem x (cellBytes 1)))
  let l ← temp (.load .w64 .zero (ctxAt limitOff))
  check .heap fun ok bad => .br .ugt (.v e) l bad ok
  emit (.store .w64 (ctxAt bumpOff) (.v e))
  emit (.store .w32 (mem x 0) (.imm (UInt64.ofNat (headerLow 0 0 0))))
  emit (.store .w32 (mem x 4) (.imm (UInt64.ofNat immortalRc)))
  emit (.store .w64 (mem x (fieldOffset 0)) rv)

/-- Unbox a `.obj`/`.tobj` value into a raw 64-bit word: odd tagged immediate `2n + 1` becomes
`w >>> 1`; even pointer to a 1-scalar-word cell loads `[w + 8]`. Works for ALL `[0, 2^64)`. -/
def unbox64 (x : VReg) (a : Lir.Arg) : M Unit :=
  match a with
  | .imm w => assign x (.arg (.imm (w >>> 1)))
  | .v y => do
    let immBlk ← newLabel
    let boxBlk ← newLabel
    let join ← newLabel
    close (.br .tz (.v y) (.imm 1) (loc boxBlk) (loc immBlk))
    let rImm ← freshReg
    put immBlk {
      body := [.assign rImm (.bin .shr .w64 (.v y) (.imm 1))]
      term := .jump ⟨.loc join, [.v rImm]⟩
    }
    let rBox ← freshReg
    put boxBlk {
      body := [.assign rBox (.load .w64 .zero (mem y (fieldOffset 0)))]
      term := .jump ⟨.loc join, [.v rBox]⟩
    }
    openAt join [x]

/-- Deliver a raw 64-bit result `r` into destination variable `x` of representation `rx`. -/
def finishRaw64 (x : VReg) (rx : Fir.Rep) (r : Lir.Arg) : M Unit :=
  match rx with
  | .word => assign x (.arg r)
  | .obj => box64 x r
  | .tobj => checked64 x r
  | .erased => assign x (.arg r)

/-- Evaluate operand `a` as a raw 64-bit word (unboxing/untagging as needed); `none` only for a
`Nat` literal `≥ 2^64` (unless `reduceMod64 = true`, as for `UInt64.ofNat`). -/
def operandRaw64 (f : FunId) (fc : Fir.Rep.FunCert) (a : Fir.Arg)
    (reduceMod64 : Bool := false) : M (Option Lir.Arg) :=
  match a with
  | .var y =>
    match fc.varRep y with
    | .word => pure (some (.v y))
    | .tobj => do pure (some (← bin .shr (.v y) (.imm 1)))
    | .obj => do
      let r ← freshReg
      unbox64 r (.v y)
      pure (some (.v r))
    | .erased => pure (some (.v y))
  | .lit (.nat n) =>
    if reduceMod64 then pure (some (.imm (UInt64.ofNat (n % 2 ^ 64))))
    else if n < 2 ^ 64 then pure (some (.imm (UInt64.ofNat n)))
    else pure none
  | .lit (.str _) => throw (.string f)
  | .erased => pure (some (.imm 0))

/-- String literal lowering context for `LowerRep` (DR1/DR4): either direct `.rodata`
addresses when `Config.rodataBase = some base`, or position-independent `strLitProc` `FunId`s. -/
structure StrCtx where
  rodataAddrs : List (String × Word) := []
  strFns : List (String × FunId) := []
  deriving Inhabited

/-- Aliasing-safe dynamic-array mini-RC context for a function in `LowerRep` (DR3). -/
structure RcCtx where
  enabled : Bool := false
  arrBase : FunId := 0
  /-- Per-function parameter mutability/escape flags (`true` = may mutate or escape via return). -/
  paramMut : Src.NatMap (List Bool) := .leaf
  /-- Variables in the current function that may flow to a mutating op or return. -/
  tainted : Src.NatSet := .leaf
  /-- Live-in variables (excluding block params) per block id. -/
  liveIn : Src.NatMap Src.NatSet := .leaf
  /-- Parameter lists per block id. -/
  blockParams : Src.NatMap (List VReg) := .leaf
  deriving Inhabited

/-- Emit `rt_arr_inc_val(y)` when `rc.enabled` and `y` is not a raw `.word` register. -/
def emitIncVal (rc : RcCtx) (fc : Fir.Rep.FunCert) (y : VReg) : M Unit := do
  if rc.enabled && fc.varRep y != .word then
    emit (.call [] (rc.arrBase + Rt.Rc.Array.fnIncVal) [.v y])

def countVarInArgs (y : VReg) (as : List Fir.Arg) : Nat :=
  as.foldl (fun n a => if a == .var y then n + 1 else n) 0

/-- Compute the exact multiset of variable arguments requiring `rt_arr_inc_val` before a call
or constructor allocation: for each distinct non-`.word` variable `y` appearing `k ≥ 1` times in
mutating/escaping positions (`mutFlags[i] = true`), emit `k` increments if `y` is still live
after the operation or also appears in a non-mutating argument, else `k - 1` increments. -/
def callIncVars (rc : RcCtx) (fc : Fir.Rep.FunCert) (liveAfter : Src.NatSet)
    (as : List Fir.Arg) (mutFlags : List Bool) : List VReg :=
  if !rc.enabled then []
  else
    let pairs := as.zipIdx.map fun (a, i) => (a, mutFlags.getD i true)
    let rec collect (seen : List VReg) : List Fir.Arg → List VReg
      | [] => []
      | .var y :: rest =>
        if fc.varRep y == .word || seen.contains y then collect seen rest
        else
          let kMut := pairs.foldl (fun n (a, m) => if a == .var y && m then n + 1 else n) 0
          let kNonMut := pairs.foldl (fun n (a, m) => if a == .var y && !m then n + 1 else n) 0
          let needed :=
            if kMut == 0 then 0
            else if liveAfter.contains y || kNonMut > 0 then kMut
            else kMut - 1
          List.replicate needed y ++ collect (y :: seen) rest
      | _ :: rest => collect seen rest
    collect [] as

/-- Emit `rt_arr_inc_val` for each variable argument in `as` according to `callIncVars`. -/
def emitIncCallArgs (rc : RcCtx) (fc : Fir.Rep.FunCert) (liveAfter : Src.NatSet)
    (as : List Fir.Arg) (mutFlags : List Bool) : M Unit :=
  (callIncVars rc fc liveAfter as mutFlags).forM fun y =>
    emit (.call [] (rc.arrBase + Rt.Rc.Array.fnIncVal) [.v y])

/-- Whether `y` has any remaining use in `rest` other than a projection of a different field `j ≠ i`
of the same constructor `c`. -/
def hasConflictProjUse (y : VReg) (c : Key.CtorKey) (i : Nat) : List Cfg.Instr → Bool
  | [] => false
  | .bind _ (.proj y' c' j) :: rest =>
    if y' == y then
      if c' == c && j != i then hasConflictProjUse y c i rest else true
    else hasConflictProjUse y c i rest
  | .bind _ r :: rest =>
    if (Cfg.Check.rhsVars r).contains y then true
    else hasConflictProjUse y c i rest

/-- Evaluate operand `a` at target representation `expected`, inserting `box64`, `unbox64`,
or static string materialization when needed. -/
def operandAtRep (f : FunId) (fc : Fir.Rep.FunCert) (a : Fir.Arg) (expected : Fir.Rep)
    (sc : StrCtx := {}) : M (Option Lir.Arg) :=
  let lowerStr (s : String) : M (Option Lir.Arg) :=
    match sc.rodataAddrs.lookup s with
    | some addr => pure (some (.imm addr))
    | none =>
      match sc.strFns.lookup s with
      | some fnId => do
        let t ← freshReg
        emit (.call [t] fnId [])
        pure (some (.v t))
      | none => throw (.string f)
  match expected with
  | .word => operandRaw64 f fc a false
  | .tobj =>
    match a with
    | .lit (.str s) => lowerStr s
    | _ => do
      match ← Lower.operand f a with
      | some la => pure (some la)
      | none => pure none
  | .obj =>
    match a with
    | .var y =>
      if fc.varRep y == .word then do
        let b ← freshReg
        box64 b (.v y)
        pure (some (.v b))
      else pure (some (.v y))
    | .lit (.nat n) =>
      if n < natLimit then pure (some (.imm (UInt64.ofNat (2 * n + 1))))
      else if n < 2 ^ 64 then do
        let b ← freshReg
        box64 b (.imm (UInt64.ofNat n))
        pure (some (.v b))
      else pure none
    | .lit (.str s) => lowerStr s
    | .erased => pure (some (.imm erasedWord))
  | .erased => pure (some (.imm erasedWord))

def operandsAtReps (f : FunId) (fc : Fir.Rep.FunCert)
    (as : List Fir.Arg) (rs : List Fir.Rep) (sc : StrCtx := {}) : M (Option (List Lir.Arg)) :=
  match as with
  | [] => pure (some [])
  | a :: as => do
    let r := rs.headD .tobj
    match ← operandAtRep f fc a r sc with
    | none => pure none
    | some la =>
      match ← operandsAtReps f fc as rs.tail sc with
      | none => pure none
      | some las => pure (some (la :: las))

def withOperandsAtReps (f : FunId) (fc : Fir.Rep.FunCert) (as : List Fir.Arg)
    (rs : List Fir.Rep) (k : List Lir.Arg → M Unit) (sc : StrCtx := {}) : M Bool := do
  match ← operandsAtReps f fc as rs sc with
  | some las => k las; pure true
  | none => close (.fail .natOverflow); pure false

/-- Evaluate a list of operands as raw 64-bit words. -/
def operandsRaw64 (f : FunId) (fc : Fir.Rep.FunCert) (reduceMod64 : Bool) :
    List Fir.Arg → M (Option (List Lir.Arg))
  | [] => pure (some [])
  | a :: as => do
    match ← operandRaw64 f fc a reduceMod64 with
    | none => pure none
    | some la =>
      match ← operandsRaw64 f fc false as with
      | none => pure none
      | some las => pure (some (la :: las))

/-! ### Zero-Alloc Limb Pair Fusion -/

/-- The four pair-returning hardware 64-bit limb primitives. -/
inductive LimbPairKind where
  | mulWide
  | divWide
  | addCarry
  | subBorrow
  deriving DecidableEq, Repr

/-- Match two adjacent Cfg instructions computing both halves of the same 64-bit limb primitive
on identical operands, binding distinct variables neither of which is read by the operands.
Returns `(kind, r1_lo_or_q, r2_hi_or_r_or_carry, args)`. -/
def matchLimbPair (i1 i2 : Cfg.Instr) :
    Option (LimbPairKind × VReg × VReg × List Fir.Arg) :=
  match i1, i2 with
  | .bind x1 (.fir (.prim (.word .w64 o1) as1)),
    .bind x2 (.fir (.prim (.word .w64 o2) as2)) =>
    if x1 == x2 || as1 != as2 || as1.any (· == .var x1) then none
    else match o1, o2, as1 with
      | .mulWideLo, .mulWideHi, [_, _] => some (.mulWide, x1, x2, as1)
      | .mulWideHi, .mulWideLo, [_, _] => some (.mulWide, x2, x1, as1)
      | .divWideQ, .divWideR, [_, _, _] => some (.divWide, x1, x2, as1)
      | .divWideR, .divWideQ, [_, _, _] => some (.divWide, x2, x1, as1)
      | .addCarryLo, .addCarryOut, [_, _, _] => some (.addCarry, x1, x2, as1)
      | .addCarryOut, .addCarryLo, [_, _, _] => some (.addCarry, x2, x1, as1)
      | .subBorrowLo, .subBorrowOut, [_, _, _] => some (.subBorrow, x1, x2, as1)
      | .subBorrowOut, .subBorrowLo, [_, _, _] => some (.subBorrow, x2, x1, as1)
      | _, _, _ => none
  | _, _ => none

/-- Emit a single fused `Lir.Stmt.limb` instruction for a matched limb pair (zero heap allocation;
when both destinations are `.word`, emits directly into `(r1, r2)` with zero moves). -/
def emitLimbPair (f : FunId) (fc : Fir.Rep.FunCert) (kind : LimbPairKind)
    (r1 r2 : VReg) (as : List Fir.Arg) : M Bool := do
  match ← operandsRaw64 f fc false as with
  | none => close (.fail .natOverflow); pure false
  | some las =>
    let op? : Option Lir.LimbOp := match kind, las with
      | .mulWide, [a, b] => some (.mulWide64 a b)
      | .divWide, [hi, lo, d] => some (.divWide64 hi lo d)
      | .addCarry, [a, b, c] => some (.addCarry64 a b c)
      | .subBorrow, [a, b, c] => some (.subBorrow64 a b c)
      | _, _ => none
    match op? with
    | none => throw (.form f "limb pair arity mismatch")
    | some lop =>
      let rep1 := fc.varRep r1
      let rep2 := fc.varRep r2
      let t1 ← if rep1 == .word then pure r1 else freshReg
      let t2 ← if rep2 == .word then pure r2 else freshReg
      emit (.limb t1 t2 lop)
      if rep1 != .word then finishRaw64 r1 rep1 (.v t1)
      if rep2 != .word then finishRaw64 r2 rep2 (.v t2)
      pure true

/-! ### Stage W2 Primitives, Scalar-Tail Allocation & Projection -/

/-- Whether a `Fir.Arg` is directly in `.word` representation (or a `< 2^64` literal). -/
def isWordArg (fc : Fir.Rep.FunCert) : Fir.Arg → Bool
  | .var y => fc.varRep y == .word
  | .lit (.nat n) => decide (n < 2 ^ 64)
  | _ => false

/-- Whether a `Fir.Arg` has any numeric representation (`.word`, `.obj`, `.tobj`, or `< 2^64` literal). -/
def isNumericRepArg (fc : Fir.Rep.FunCert) : Fir.Arg → Bool
  | .var y => Fir.Rep.isValidRep (fc.varRep y)
  | .lit (.nat n) => decide (n < 2 ^ 64)
  | _ => false

/-- Whether a comparison's two arguments should be compared as raw 64-bit unsigned words
(unboxing `.obj` 1-scalar-word `UInt64` cells and untagging `.tobj` as needed). -/
def cmpIsRaw64 (fc : Fir.Rep.FunCert) (a b : Fir.Arg) : Bool :=
  (match a with
    | .var y => fc.varRep y == .word || fc.varRep y == .obj
    | .lit (.nat n) => decide (natLimit ≤ n ∧ n < 2 ^ 64)
    | _ => false) ||
  (match b with
    | .var y => fc.varRep y == .word || fc.varRep y == .obj
    | .lit (.nat n) => decide (natLimit ≤ n ∧ n < 2 ^ 64)
    | _ => false)

/-- Convert operand `a` to an odd tagged immediate `2v + 1` expected by narrow `Lower.word`
(`w ≠ .w64`), respecting `fc.varRep y` (`.word` → `retag`, `.obj` → `unbox64` + `retag`,
`.tobj` → as-is). -/
def operandNarrowRep (f : FunId) (fc : Fir.Rep.FunCert) (a : Fir.Arg) : M (Option Lir.Arg) :=
  match a with
  | .var y =>
    match fc.varRep y with
    | .word => do pure (some (← temp (retag (.v y))))
    | .obj => do
      let u ← freshReg
      unbox64 u (.v y)
      pure (some (← temp (retag (.v u))))
    | .tobj | .erased => pure (some (.v y))
  | _ => do pure (← Lower.operand f a)

def operandsNarrowRep (f : FunId) (fc : Fir.Rep.FunCert) : List Fir.Arg → M (Option (List Lir.Arg))
  | [] => pure (some [])
  | a :: as => do
    match ← operandNarrowRep f fc a with
    | none => pure none
    | some la =>
      match ← operandsNarrowRep f fc as with
      | none => pure none
      | some las => pure (some (la :: las))

def withOperandsNarrowRep (f : FunId) (fc : Fir.Rep.FunCert) (as : List Fir.Arg)
    (k : List Lir.Arg → M Unit) : M Bool := do
  match ← operandsNarrowRep f fc as with
  | some las => k las; pure true
  | none => close (.fail .natOverflow); pure false

/-- Lower a primitive in Stage W2 (`Rt.lowerRep`). -/
def primitiveRep (f : FunId) (T : Tables) (fc : Fir.Rep.FunCert) (x : VReg)
    (op : Lam.Prim) (as : List Fir.Arg) : M Bool := do
  let rx := fc.varRep x
  match op with
  | .word .w64 wo =>
    if wo.isDecision then throw (.prim f (.word .w64 wo))
    match ← operandsRaw64 f fc (wo == .ofNat) as with
    | none => close (.fail .natOverflow); pure false
    | some las =>
      match wo with
      | .convert w' =>
        if w' == .w64 then
          match las with
          | [a] => finishRaw64 x rx a; pure true
          | _ => throw (.prim f (.word .w64 wo))
        else
          -- Narrowing `UInt64.toUInt8/16/32`: mask raw 64-bit value, retag for `.tobj`/`.obj`, NEVER box64!
          match las with
          | [a] =>
            let m ← bin .and a (.imm (UInt64.ofNat (w'.size - 1)))
            match rx with
            | .word => assign x (.arg m)
            | .tobj | .obj => assign x (retag m)
            | .erased => assign x (.arg m)
            pure true
          | _ => throw (.prim f (.word .w64 wo))
      | _ =>
        if rx == .word then
          wordRaw64 f x wo las; pure true
        else
          let tmp ← freshReg
          wordRaw64 f tmp wo las
          finishRaw64 x rx (.v tmp)
          pure true
  | .word w (.convert .w64) =>
    -- Widening `UInt8/16/32.toUInt64`: always fits `[0, 2^32) ⊂ [0, 2^64)`, zero overflow!
    match ← operandsRaw64 f fc false as with
    | none => close (.fail .natOverflow); pure false
    | some [a] => finishRaw64 x rx a; pure true
    | some _ => throw (.prim f (.word w (.convert .w64)))
  | .word w wo =>
    if rx == .word then
      -- Narrow word op producing a `.word` register: compute tagged then untag.
      withOperandsNarrowRep f fc as fun las => do
        let tmp ← freshReg
        Lower.word f tmp w wo las
        assign x (.bin .shr .w64 (.v tmp) (.imm 1))
    else
      withOperandsNarrowRep f fc as (Lower.word f x w wo)
  | op =>
    match compareOf op, as with
    | some cond, [a, b] =>
      if cmpIsRaw64 fc a b && isNumericRepArg fc a && isNumericRepArg fc b then
        match ← operandsRaw64 f fc false [a, b] with
        | none => close (.fail .natOverflow); pure false
        | some [la, lb] =>
          let some (t, e) := T.bools | throw (.noBool f)
          assign x (.select cond .w64 la lb (.imm t) (.imm e))
          pure true
        | some _ => throw (.prim f op)
      else
        withOperands f [a, b] (Lower.primitive f T x op)
    | _, _ =>
      withOperands f as (Lower.primitive f T x op)

/-- Stage W2 + DR3 allocation supporting `CtorInfo.nscalar > 0` scalar tails, `Array.mk`
(`arrOfListBoxed` / `arrOfListLimbs`), `ByteArray.mk` (`byteArrOfArr`), and aliasing-safe
mini-RC on live array fields. -/
def allocRep (f : FunId) (T : Tables) (cert : Fir.Rep.Cert) (fc : Fir.Rep.FunCert)
    (x : VReg) (c : Fir.CtorInfo) (as : List Fir.Arg)
    (sc : StrCtx := {}) (rc : RcCtx := {}) (liveAfter : Src.NatSet := .leaf) : M Bool := do
  if rc.enabled && cert.arrayMkKey == some c.key then
    match as with
    | [xs] =>
      let callee := rc.arrBase +
        if cert.arrayMkKind == .limbs then Rt.Rc.Array.fnArrOfListLimbs
        else Rt.Rc.Array.fnArrOfListBoxed
      withOperandsAtReps f fc [xs] [.obj] (fun
        | [lxs] => emit (.call [x] callee [lxs])
        | _ => pure ()) sc
    | _ => throw (.form f s!"Array.mk expected 1 field, got {as.length}")
  else if rc.enabled && cert.byteArrayMkKey == some c.key then
    match as with
    | [arr] =>
      withOperandsAtReps f fc [arr] [.obj] (fun
        | [larr] => emit (.call [x] (rc.arrBase + Rt.Rc.Array.fnByteArrOfArr) [larr])
        | _ => pure ()) sc
    | _ => throw (.form f s!"ByteArray.mk expected 1 field, got {as.length}")
  else
    if isNatKey T c.key then throw (.layout f "a Nat constructor cell (Nat values are literals)")
    let some baseInfo := Fir.CtorInfo.ofKey T.ctors c.key
      | throw (.form f "allocation key outside the table")
    let (nobj, nscalar, fieldReps) : Nat × Nat × List Fir.Rep := match cert.ctorRep? c.key with
      | some cr =>
        (cr.nobj, cr.nscalar, List.replicate cr.nobj cr.objRep ++ List.replicate cr.nscalar Fir.Rep.word)
      | none =>
        (c.nobj, c.nscalar, List.replicate c.nobj Fir.Rep.tobj ++ List.replicate c.nscalar Fir.Rep.word)
    let totalArity := nobj + nscalar
    if as.length != totalArity || totalArity != baseInfo.arity then
      throw (.form f s!"an allocation of {as.length} fields for {totalArity}")
    if baseInfo.tag > maxTag then throw (.layout f s!"constructor tag {baseInfo.tag} above {maxTag}")
    if totalArity == 0 then
      assign x (.arg (.imm (ctor0Word baseInfo.tag)))
      pure true
    else
      if totalArity > maxFields then throw (.layout f s!"{totalArity} fields, above {maxFields}")
      emitIncCallArgs rc fc liveAfter as (List.replicate nobj true ++ List.replicate nscalar false)
      withOperandsAtReps f fc as fieldReps (fun las => do
        if las.any (· == .v x) then throw (.form f "an allocation reads the variable it defines")
        assign x (.load .w64 .zero (ctxAt bumpOff))
        let e ← freshReg
        assign e (.addr (mem x (cellBytes totalArity)))
        let l ← temp (.load .w64 .zero (ctxAt limitOff))
        check .heap fun ok bad => .br .ugt (.v e) l bad ok
        emit (.store .w64 (ctxAt bumpOff) (.v e))
        emit (.store .w32 (mem x 0) (.imm (UInt64.ofNat (headerLow nobj 0 baseInfo.tag))))
        emit (.store .w32 (mem x 4) (.imm (UInt64.ofNat immortalRc)))
        las.zipIdx.forM fun (a, i) => emit (.store .w64 (mem x (fieldOffset i)) a)) sc

/-- Stage W2 + DR3 projection supporting raw 64-bit scalar-tail fields (`i ≥ nobj`),
`Array.toList` (`arrToListBoxed` / `arrToListLimbs`), `ByteArray.data` (`byteArrToArr`),
and aliasing-safe mini-RC when the container `y` has conflicting remaining uses. -/
def projRep (f : FunId) (T : Tables) (cert : Fir.Rep.Cert) (fc : Fir.Rep.FunCert)
    (x y : VReg) (c : Key.CtorKey) (i : Nat)
    (rc : RcCtx := {}) (liveAfter : Src.NatSet := .leaf) (liveTerm : Src.NatSet := .leaf)
    (rest : List Cfg.Instr := []) : M Unit := do
  if rc.enabled && cert.arrayMkKey == some c && i == 0 then
    let callee := rc.arrBase +
      if cert.arrayMkKind == .limbs then Rt.Rc.Array.fnArrToListLimbs
      else Rt.Rc.Array.fnArrToListBoxed
    emit (.call [x] callee [.v y])
  else if rc.enabled && cert.byteArrayMkKey == some c && i == 0 then
    emit (.call [x] (rc.arrBase + Rt.Rc.Array.fnByteArrToArr) [.v y])
  else if T.known.natSucc == some c then
    if i == 0 then assign x (.bin .sub .w64 (.v y) (.imm 2))
    else throw (.form f "a projection past the Nat successor's field")
  else if T.known.natZero == some c then throw (.form f "a projection of Nat.zero")
  else
    match Fir.CtorInfo.ofKey T.ctors c with
    | some info =>
      if i < info.arity then
        let fr := cert.fieldRep c i
        let rx := fc.varRep x
        if fr == .word && rx == .obj then
          let tmp ← freshReg
          assign tmp (.load .w64 .zero (mem y (fieldOffset i)))
          box64 x (.v tmp)
        else
          assign x (.load .w64 .zero (mem y (fieldOffset i)))
          if rc.enabled && rx != .word && (rc.tainted.contains x || rc.tainted.contains y) &&
              liveAfter.contains y &&
              (liveTerm.contains y || hasConflictProjUse y c i rest) then
            emit (.call [] (rc.arrBase + Rt.Rc.Array.fnIncVal) [.v x])
      else throw (.form f s!"field {i} of a constructor with {info.arity}")
    | none => throw (.form f "a projection key outside the table")

/-- Stage W2 + DR3 single instruction lowering. -/
def instrRep (f : FunId) (T : Tables) (cert : Fir.Rep.Cert) (fc : Fir.Rep.FunCert)
    (ins : Cfg.Instr) (sc : StrCtx := {}) (rc : RcCtx := {})
    (liveAfter : Src.NatSet := .leaf) (liveTerm : Src.NatSet := .leaf)
    (rest : List Cfg.Instr := []) : M Bool :=
  match ins with
  | .bind x (.fir (.arg a)) => do
    match a with
    | .var y =>
      if rc.enabled && fc.varRep y != .word && liveAfter.contains y &&
          (rc.tainted.contains x || rc.tainted.contains y) then
        emit (.call [] (rc.arrBase + Rt.Rc.Array.fnIncVal) [.v y])
    | _ => pure ()
    withOperandsAtReps f fc [a] [fc.varRep x] (fun
      | [la] => assign x (.arg la)
      | _ => pure ()) sc
  | .bind x (.fir (.prim op as)) => primitiveRep f T fc x op as
  | .bind x (.fir (.call g as)) => do
    let gc := cert.funCert g
    let mutFlags := rc.paramMut.getD g (List.replicate as.length true)
    emitIncCallArgs rc fc liveAfter as mutFlags
    withOperandsAtReps f fc as gc.params (fun las => do
      let rx := fc.varRep x
      if gc.ret == .word && rx == .obj then
        let tmp ← freshReg
        emit (.call [tmp] g las)
        box64 x (.v tmp)
      else if gc.ret == .word && rx == .tobj then
        let tmp ← freshReg
        emit (.call [tmp] g las)
        checked64 x (.v tmp)
      else
        emit (.call [x] g las)) sc
  | .bind _ (.fir (.ctor ..)) => throw (.form f "a Fir constructor in Cfg")
  | .bind _ (.fir (.proj ..)) => throw (.form f "a Fir projection in Cfg")
  | .bind x (.alloc c as _) => allocRep f T cert fc x c as sc rc liveAfter
  | .bind x (.proj y c i) => do projRep f T cert fc x y c i rc liveAfter liveTerm rest; pure true

/-- Lower a block's instruction list with adjacent limb-pair fusion (`matchLimbPair`)
and per-instruction liveness sets. -/
def instrsRepAnn (f : FunId) (T : Tables) (cert : Fir.Rep.Cert) (fc : Fir.Rep.FunCert)
    (sc : StrCtx) (rc : RcCtx) (liveTerm : Src.NatSet) :
    List (Cfg.Instr × Src.NatSet) → M Bool
  | [] => pure true
  | [(i, la)] => instrRep f T cert fc i sc rc la liveTerm []
  | (i1, la1) :: (i2, la2) :: rest =>
    match matchLimbPair i1 i2 with
    | some (kind, r1, r2, as) => do
      if ← emitLimbPair f fc kind r1 r2 as then instrsRepAnn f T cert fc sc rc liveTerm rest
      else pure false
    | none => do
      let restInstrs := i2 :: rest.map (·.1)
      if ← instrRep f T cert fc i1 sc rc la1 liveTerm restInstrs then
        instrsRepAnn f T cert fc sc rc liveTerm ((i2, la2) :: rest)
      else pure false

/-- Lower a block's instruction list (compatibility entry without liveness annotations). -/
def instrsRep (f : FunId) (T : Tables) (cert : Fir.Rep.Cert) (fc : Fir.Rep.FunCert)
    (is : List Cfg.Instr) (sc : StrCtx := {}) : M Bool :=
  instrsRepAnn f T cert fc sc {} .leaf (is.map (·, .leaf))

/-! ### Stage W2 + DR3/DR4 Edges, Switches, and Terminators -/

/-- Pure operand lowering when no `box64`/`unbox64`/string-materializer side effects are required. -/
def pureOperandAtRep (f : FunId) (fc : Fir.Rep.FunCert) (a : Fir.Arg) (expected : Fir.Rep)
    (sc : StrCtx := {}) : Except Error (Option (Option Lir.Arg)) :=
  let pureStr (s : String) : Except Error (Option (Option Lir.Arg)) :=
    match sc.rodataAddrs.lookup s with
    | some addr => pure (some (some (.imm addr)))
    | none =>
      if (sc.strFns.lookup s).isSome then pure none else throw (.string f)
  match expected with
  | .word =>
    match a with
    | .var y => if fc.varRep y == .word then pure (some (some (.v y))) else pure none
    | .lit (.nat n) => if n < 2 ^ 64 then pure (some (some (.imm (UInt64.ofNat n)))) else pure (some none)
    | .lit (.str _) => throw (.string f)
    | .erased => pure (some (some (.imm 0)))
  | .tobj =>
    match a with
    | .lit (.str s) => pureStr s
    | _ => do pure (some (← Lower.operand f a))
  | .obj =>
    match a with
    | .var y => if fc.varRep y == .word then pure none else pure (some (some (.v y)))
    | .lit (.nat n) =>
      if n < natLimit then pure (some (some (.imm (UInt64.ofNat (2 * n + 1)))))
      else if n < 2 ^ 64 then pure none
      else pure (some none)
    | .lit (.str s) => pureStr s
    | .erased => pure (some (some (.imm erasedWord)))
  | .erased => pure (some (some (.imm erasedWord)))

def pureOperandsAtReps (f : FunId) (fc : Fir.Rep.FunCert)
    (as : List Fir.Arg) (rs : List Fir.Rep) (sc : StrCtx := {}) :
    Except Error (Option (Option (List Lir.Arg))) :=
  match as with
  | [] => pure (some (some []))
  | a :: as => do
    match ← pureOperandAtRep f fc a (rs.headD .tobj) sc with
    | none => pure none
    | some none => pure (some none)
    | some (some la) =>
      match ← pureOperandsAtReps f fc as rs.tail sc with
      | none => pure none
      | some none => pure (some none)
      | some (some las) => pure (some (some (la :: las)))

/-- Exact multiset of edge arguments requiring `rt_arr_inc_val`: for each distinct non-`.word`
variable `y` appearing `k ≥ 1` times in tainted target-parameter positions, emit `k` increments
if `y` is also live-through at `e.target` or passed to an untainted parameter, else `k - 1`
increments; if `k = 0` but `y` is live-through, tainted, and passed to an untainted parameter,
emit `1` increment so the live-through mutation cannot corrupt the untainted alias. -/
def edgeIncVars (fc : Fir.Rep.FunCert) (rc : RcCtx) (e : Cfg.Edge) : List VReg :=
  if !rc.enabled then []
  else
    let liveThru := rc.liveIn.getD e.target .leaf
    let tParams := rc.blockParams.getD e.target []
    let pairs := e.args.zipIdx.map fun (a, i) =>
      let pTainted := match tParams[i]? with | some p => rc.tainted.contains p | none => false
      (a, pTainted)
    let rec collect (seen : List VReg) : List Fir.Arg → List VReg
      | [] => []
      | .var y :: rest =>
        if fc.varRep y == .word || seen.contains y then collect seen rest
        else
          let kMut := pairs.foldl (fun n (a, m) => if a == .var y && m then n + 1 else n) 0
          let kNonMut := pairs.foldl (fun n (a, m) => if a == .var y && !m then n + 1 else n) 0
          let needed :=
            if kMut > 0 then
              if liveThru.contains y || kNonMut > 0 then kMut else kMut - 1
            else if liveThru.contains y && rc.tainted.contains y && kNonMut > 0 then
              1
            else 0
          List.replicate needed y ++ collect (y :: seen) rest
      | _ :: rest => collect seen rest
    collect [] e.args

/-- Lower a Cfg edge under Stage W2 + DR3/DR4 representations, emitting a trampoline block only
if an edge argument requires `box64`, `unbox64`, string materialization, or alias `fnIncVal`. -/
def edgeRep (f : FunId) (fc : Fir.Rep.FunCert) (blockReps : Src.NatMap (List Fir.Rep))
    (src : Nat) (e : Cfg.Edge) (sc : StrCtx := {}) (rc : RcCtx := {}) : M PEdge := do
  unless e.back == decide (e.target ≤ src) do throw (.edgeOrder f src)
  let targetReps := blockReps.getD e.target (List.replicate e.args.length .tobj)
  let incVars := edgeIncVars fc rc e
  let pureRes ← if incVars.isEmpty then pureOperandsAtReps f fc e.args targetReps sc else pure none
  match pureRes with
  | some (some las) => pure ⟨.blk e.target, las⟩
  | some none => pure (loc (← coldBlock (.fail .natOverflow)))
  | none =>
    let saved ← get
    let tramp ← newLabel
    modify fun st => { st with cur := tramp, params := [], acc := [] }
    incVars.forM fun y => emit (.call [] (rc.arrBase + Rt.Rc.Array.fnIncVal) [.v y])
    let ok ← withOperandsAtReps f fc e.args targetReps (fun las =>
      close (.jump ⟨.blk e.target, las⟩)) sc
    let _ := ok
    modify fun st => { st with cur := saved.cur, params := saved.params, acc := saved.acc }
    pure (loc tramp)

def switchAltRep (f : FunId) (T : Tables) (fc : Fir.Rep.FunCert)
    (blockReps : Src.NatMap (List Fir.Rep)) (src : Nat) (ke : Key.CtorKey × Cfg.Edge)
    (sc : StrCtx := {}) (rc : RcCtx := {}) : M (KeyKind × PEdge) := do
  let some kind := keyKind T ke.1 | throw (.switch f src "a key outside the constructor table")
  pure (kind, ← edgeRep f fc blockReps src ke.2 sc rc)

def switchRep (f : FunId) (T : Tables) (cert : Fir.Rep.Cert) (fc : Fir.Rep.FunCert)
    (blockReps : Src.NatMap (List Fir.Rep)) (src : Nat) (x : VReg)
    (alts : List (Key.CtorKey × Cfg.Edge)) (d : Option Cfg.Edge)
    (sc : StrCtx := {}) (rc : RcCtx := {}) : M Unit := do
  -- Single-constructor `Array.mk` / `ByteArray.mk` switches jump directly without loading a tag.
  match alts, d with
  | [(k, e)], none =>
    if rc.enabled && (cert.arrayMkKey == some k || cert.byteArrayMkKey == some k) then
      close (.jump (← edgeRep f fc blockReps src e sc rc))
      return
  | _, _ => pure ()
  let es ← alts.mapM (switchAltRep f T fc blockReps src · sc rc)
  let dd ← d.mapM (edgeRep f fc blockReps src · sc rc)
  let nats := es.filter (·.1.isNat)
  if !nats.isEmpty then
    unless nats.length == es.length do throw (.switch f src "Nat keys mixed with other keys")
    natSwitch x es dd
  else tagSwitch x es dd

def fusedSwitchRep (f : FunId) (T : Tables) (fc : Fir.Rep.FunCert)
    (blockReps : Src.NatMap (List Fir.Rep)) (src : Nat) (c : Lir.Cond) (a b : Lir.Arg)
    (alts : List (Key.CtorKey × Cfg.Edge)) (d : Option Cfg.Edge)
    (sc : StrCtx := {}) (rc : RcCtx := {}) : M Unit := do
  let te ← (boolEdge alts d T.known.boolTrue).mapM (edgeRep f fc blockReps src · sc rc)
  let fe ← (boolEdge alts d T.known.boolFalse).mapM (edgeRep f fc blockReps src · sc rc)
  fusedClose c a b te fe

def termRep (f : FunId) (T : Tables) (cert : Fir.Rep.Cert) (fc : Fir.Rep.FunCert)
    (blockReps : Src.NatMap (List Fir.Rep)) (src : Nat) (t : Cfg.Term)
    (sc : StrCtx := {}) (rc : RcCtx := {}) : M Unit :=
  match t with
  | .jump e => do close (.jump (← edgeRep f fc blockReps src e sc rc))
  | .switch x alts d => switchRep f T cert fc blockReps src x alts d sc rc
  | .ret a => do
    let _ ← withOperandsAtReps f fc [a] [fc.ret] (fun
      | [la] => close (.ret la)
      | _ => pure ()) sc
  | .tcall g as => do
    let gc := cert.funCert g
    let mutFlags := rc.paramMut.getD g (List.replicate as.length true)
    emitIncCallArgs rc fc .leaf as mutFlags
    let _ ← withOperandsAtReps f fc as gc.params (fun las => close (.tail g las)) sc
  | .trap => close .trap

def fusedEndRep (f : FunId) (T : Tables) (cert : Fir.Rep.Cert) (fc : Fir.Rep.FunCert)
    (blockReps : Src.NatMap (List Fir.Rep)) (src : Nat) (b : Cfg.Block)
    (c : Lir.Cond) (a a' : Fir.Arg) (sc : StrCtx := {}) (rc : RcCtx := {}) : M Unit := do
  let raw := cmpIsRaw64 fc a a' && isNumericRepArg fc a && isNumericRepArg fc a'
  let args? ← if raw then operandsRaw64 f fc false [a, a'] else do pure (← Lower.operands f [a, a'])
  match args? with
  | some [la, la'] =>
    match b.term with
    | .switch _ alts d => fusedSwitchRep f T fc blockReps src c la la' alts d sc rc
    | t => termRep f T cert fc blockReps src t sc rc
  | _ => close (.fail .natOverflow)

/-! ### DR3 Backward Liveness & Per-Parameter Mutability Analysis

Three analyses decide where an array is protected (`rt_arr_inc_val`) before an in-place update:
the variables live after each instruction (`computeLiveIn`), the variables that may flow to a
mutating parameter or to the result (`computeTainted`), and the parameters a function may mutate
or return (`computeParamMutates`). Each grows its sets from empty, so a result taken before its
fixpoint is too small: a protection is missing and a shared array is updated in place. Each
therefore runs rounds until one changes nothing (`fixpoint`), within a bound that provably
suffices, because every round only adds elements of a finite universe the program fixes:

* `computeLiveIn` (round-robin over the blocks, each block's live-in from the previous round's;
  monotone, so the rounds increase from `.leaf`): its elements are pairs of a block and a variable
  the function reads (`usedVars`: rounds add only variables of right-hand sides and terminators,
  and carry them back from successors). `liveInBound = |blocks| · |usedVars| + 2` rounds suffice:
  the first gives every block its entry, each further round that changes anything adds a pair, and
  the last changes nothing.
* `computeTainted` (each round only inserts, and only variables the function reads):
  `taintedBound = |usedVars| + 1`.
* `computeParamMutates` (each round only turns flags from `false` to `true`, one per parameter of
  every function that is not a native array primitive; each round runs `computeTainted` to its own
  fixpoint): `paramMutBound = Σ |params| + 1`.

Sets are compared by their elements (`setElems`), not as tries (`erase` leaves empty nodes). If a
bound were ever reached without convergence, `checkArrayAnalyses` refuses the program
(`rt.internal`); `ixcc compile --bignat` and `Rt.BigNat.compileLibrary` run it before lowering, so
no lowering runs on a partial result. The totals the lowerings call (`computeLiveIn`,
`computeTainted`, `computeParamMutates`) return the same fixpoints, and on that unreachable
non-convergence the most conservative answer instead (every variable read live everywhere, every
variable read tainted, every parameter mutated), never a partial one. -/

private def setUnion (a b : Src.NatSet) : Src.NatSet :=
  b.toList.foldl (fun s (k, _) => s.insert k) a

private def setDiff (a : Src.NatSet) (xs : List VReg) : Src.NatSet :=
  xs.foldl (fun s x => s.erase x) a

private def setAddList (a : Src.NatSet) (xs : List VReg) : Src.NatSet :=
  xs.foldl (fun s x => s.insert x) a

private def liveAtTerm (liveIn : Src.NatMap Src.NatSet) (b : Cfg.Block) : Src.NatSet :=
  let fromEdges := b.term.edges.foldl (init := Src.NatMap.leaf) fun s e =>
    setUnion s (liveIn.getD e.target .leaf)
  setAddList fromEdges (Cfg.Check.termVars b.term)

/-- Rounds of `step` from `x` until one changes nothing (`same (step y) y`), at most `fuel` of
them: the fixpoint and the rounds run (`n` plus the rounds here, the last the one that changed
nothing), or `stuck` when all `fuel` rounds changed something. Structural on `fuel`. -/
def fixpoint {α : Type} (same : α → α → Bool) (step : α → Except Error α) (stuck : Error) :
    Nat → α → Nat → Except Error (α × Nat)
  | 0, _, _ => throw stuck
  | fuel + 1, x, n => do
    let y ← step x
    if same y x then pure (x, n + 1) else fixpoint same step stuck fuel y (n + 1)

/-- A set's elements in the trie's order: equal sets give equal lists, whatever their history. -/
def setElems (s : Src.NatSet) : List Nat := s.toList.map (·.1)

/-- Equal elements (not equal tries). -/
def sameSet (a b : Src.NatSet) : Bool := setElems a == setElems b

/-- Equal keys, each with equal elements. -/
def sameSetMap (a b : Src.NatMap Src.NatSet) : Bool :=
  a.toList.map (fun (k, s) => (k, setElems s)) == b.toList.map (fun (k, s) => (k, setElems s))

/-- Equal keys, each with equal flags. -/
def sameFlags (a b : Src.NatMap (List Bool)) : Bool := a.toList == b.toList

/-- The distinct variables `fd` reads (its right-hand sides' and terminators' variables): the
analyses below add no other variable. -/
def usedVars (fd : Cfg.Fun) : Src.NatSet := Src.NatSet.ofList (fd.blocks.flatMap blockUses)

/-- One round of `computeLiveIn`: every block's live-in from the previous round's. -/
def liveInStep (fd : Cfg.Fun) (m : Src.NatMap Src.NatSet) : Src.NatMap Src.NatSet :=
  fd.blocks.zipIdx.foldl (init := m) fun acc (b, idx) =>
    let lt := liveAtTerm m b
    let beforeBody := b.body.reverse.foldl (init := lt) fun s => fun
      | .bind x r => setAddList (s.erase x) (Cfg.Check.rhsVars r)
    let li := setDiff beforeBody (b.params.map (·.1))
    acc.insert idx li

/-- Rounds that suffice for `computeLiveIn` (the section's comment). -/
def liveInBound (fd : Cfg.Fun) : Nat := fd.blocks.length * (usedVars fd).size + 2

/-- `computeLiveIn`'s fixpoint and its rounds; `rt.internal` (for function `f`) if `fuel` rounds
do not reach it. -/
def liveInFix (f : FunId) (fd : Cfg.Fun) (fuel : Nat := liveInBound fd) :
    Except Error (Src.NatMap Src.NatSet × Nat) :=
  fixpoint sameSetMap (fun m => pure (liveInStep fd m))
    (.internal f s!"array liveness did not converge within {fuel} rounds") fuel .leaf 0

/-- Backward dataflow `liveIn[b]` (excluding `b`'s own parameters) for every block of `fd`, to
its fixpoint, or refused (`rt.internal`). -/
def computeLiveIn? (f : FunId) (fd : Cfg.Fun) : Except Error (Src.NatMap Src.NatSet) :=
  (·.1) <$> liveInFix f fd

/-- Compute backward dataflow `liveIn[b]` (excluding `b`'s own parameters) for every block of
`fd`: `computeLiveIn?`'s fixpoint; were it not reached, every variable `fd` reads, live at every
block (more protection, never less). -/
def computeLiveIn (fd : Cfg.Fun) : Src.NatMap Src.NatSet :=
  match computeLiveIn? 0 fd with
  | .ok m => m
  | .error _ =>
    let all := usedVars fd
    Src.NatMap.ofDense (fd.blocks.map fun _ => all)

/-- Annotate each instruction of `is` with the exact set of variables live immediately after it. -/
def annotateBody (liveTerm : Src.NatSet) (is : List Cfg.Instr) : List (Cfg.Instr × Src.NatSet) :=
  let rec go : List Cfg.Instr → Src.NatSet → List (Cfg.Instr × Src.NatSet) → List (Cfg.Instr × Src.NatSet)
    | [], _, acc => acc
    | (.bind x r) :: rest, la, acc =>
      let lb := setAddList (la.erase x) (Cfg.Check.rhsVars r)
      go rest lb ((.bind x r, la) :: acc)
  go is.reverse liveTerm []

/-- Initial per-parameter mutability flags for a native `ArrayPrimSpec`. -/
def arrayPrimParamMut (arity : Nat) (spec : Fir.Rep.ArrayPrimSpec) : List Bool :=
  let mutIdx : List Nat := match spec.op with
    | .emptyCap | .size | .get | .getBang | .extract => []
    | .pop | .swap => spec.argIdx.take 1
    | .set =>
      match spec.kind, spec.argIdx with
      | .boxed, [ai, _, vi] => [ai, vi]
      | _, ai :: _ => [ai]
      | _, [] => []
    | .push =>
      match spec.kind, spec.argIdx with
      | .boxed, [ai, vi] => [ai, vi]
      | _, ai :: _ => [ai]
      | _, [] => []
    | .copySlice =>
      match spec.argIdx with
      | [_, _, di, _, _] => [di]
      | _ => []
  (List.range arity).map fun i => mutIdx.contains i

/-- Rounds that suffice for `computeTainted` (the section's comment). -/
def taintedBound (fd : Cfg.Fun) : Nat := (usedVars fd).size + 1

/-- `computeTainted`'s fixpoint under `paramMut` and its rounds; `rt.internal` (for function `f`)
if `fuel` rounds do not reach it. -/
def taintedFix (f : FunId) (fd : Cfg.Fun) (paramMut : Src.NatMap (List Bool))
    (fuel : Nat := taintedBound fd) : Except Error (Src.NatSet × Nat) :=
  let bParams : Src.NatMap (List VReg) :=
    Src.NatMap.ofDense (fd.blocks.map fun b => b.params.map (·.1))
  let seedFromArgs (t : Src.NatSet) (as : List Fir.Arg) (fs : List Bool) : Src.NatSet :=
    (as.zip fs).foldl (init := t) fun s (a, m) =>
      match a, m with
      | .var y, true => s.insert y
      | _, _ => s
  let step (t : Src.NatSet) : Src.NatSet :=
    fd.blocks.foldl (init := t) fun acc b =>
      let acc1 := match b.term with
        | .ret (.var y) => acc.insert y
        | .tcall g as => seedFromArgs acc as (paramMut.getD g (List.replicate as.length true))
        | _ => acc
      let acc2 := b.term.edges.foldl (init := acc1) fun s e =>
        let ps := bParams.getD e.target []
        (e.args.zip ps).foldl (init := s) fun s' (a, p) =>
          match a with
          | .var y => if s'.contains p then s'.insert y else s'
          | _ => s'
      b.body.reverse.foldl (init := acc2) fun s => fun
        | .bind x (.fir (.arg (.var y))) => if s.contains x then s.insert y else s
        | .bind x (.proj y _ _) => if s.contains x then s.insert y else s
        | .bind x (.alloc _ as _) =>
          if s.contains x then setAddList s (Cfg.Check.argVars as) else s
        | .bind _ (.fir (.call g as)) =>
          seedFromArgs s as (paramMut.getD g (List.replicate as.length true))
        | _ => s
  fixpoint sameSet (fun t => pure (step t))
    (.internal f s!"array taint did not converge within {fuel} rounds") fuel .leaf 0

/-- The variables inside `fd` that may flow to a mutating/escaping parameter or return value, to
the fixpoint, or refused (`rt.internal`). -/
def computeTainted? (f : FunId) (fd : Cfg.Fun) (paramMut : Src.NatMap (List Bool)) :
    Except Error Src.NatSet :=
  (·.1) <$> taintedFix f fd paramMut

/-- Compute variables inside `fd` that may flow to a mutating/escaping parameter or return value:
`computeTainted?`'s fixpoint; were it not reached, every variable `fd` reads. -/
def computeTainted (fd : Cfg.Fun) (paramMut : Src.NatMap (List Bool)) : Src.NatSet :=
  match computeTainted? 0 fd paramMut with
  | .ok t => t
  | .error _ => usedVars fd

/-- `computeParamMutates`' starting flags: a native array primitive's from its spec
(`arrayPrimParamMut`), every other function's parameters `false`. -/
def paramMutInit (P : Cfg.Program) (cert : Fir.Rep.Cert) : Src.NatMap (List Bool) :=
  (List.range P.size).foldl (init := .leaf) fun m f =>
    match P.fun? f with
    | some fd =>
      match cert.arrayPrims.get? f with
      | some spec => m.insert f (arrayPrimParamMut fd.params.length spec)
      | none => m.insert f (List.replicate fd.params.length false)
    | none => m

/-- Rounds that suffice for `computeParamMutates` (the section's comment): one more than the
parameters of the functions that are not native array primitives. -/
def paramMutBound (P : Cfg.Program) (cert : Fir.Rep.Cert) : Nat :=
  (List.range P.size).foldl (init := 1) fun n f =>
    match P.fun? f with
    | some fd => if (cert.arrayPrims.get? f).isSome then n else n + fd.params.length
    | none => n

/-- `computeParamMutates`' fixpoint and its rounds; `rt.internal` if `fuel` rounds do not reach
it, or if a round's `computeTainted` does not reach its own. -/
def paramMutFix (P : Cfg.Program) (cert : Fir.Rep.Cert) (fuel : Nat := paramMutBound P cert) :
    Except Error (Src.NatMap (List Bool) × Nat) :=
  let refineOnce (pm : Src.NatMap (List Bool)) : Except Error (Src.NatMap (List Bool)) :=
    (List.range P.size).foldlM (init := pm) fun acc f =>
      match P.fun? f with
      | some fd =>
        if (cert.arrayPrims.get? f).isSome then pure acc
        else do
          let tainted ← computeTainted? f fd pm
          let old := pm.getD f (List.replicate fd.params.length false)
          let updated := (fd.params.zip old).map fun (v, b) => b || tainted.contains v
          pure (acc.insert f updated)
      | none => pure acc
  fixpoint sameFlags refineOnce
    (.internal (P.exports.headD 0)
      s!"array parameter mutability (interprocedural) did not converge within {fuel} rounds")
    fuel (paramMutInit P cert) 0

/-- `computeParamMutates`, to the fixpoint, or refused (`rt.internal`). -/
def computeParamMutates? (P : Cfg.Program) (cert : Fir.Rep.Cert) :
    Except Error (Src.NatMap (List Bool)) :=
  (·.1) <$> paramMutFix P cert

/-- Interprocedural fixed-point computing `paramMut[f][k]` (`true` = param `k` of `f` may be
mutated in place or escape via return value). Read-only helpers (`scanRight`, `scanLeft`,
`isSorted`, `checksum`, `blockWords`, `subtree`, `compress`) infer `false` for read-only array
params so callers incur zero `fnIncVal` and zero copies. `computeParamMutates?`'s fixpoint; were
it not reached, every parameter of every function but the native array primitives `true`. -/
def computeParamMutates (P : Cfg.Program) (cert : Fir.Rep.Cert) : Src.NatMap (List Bool) :=
  match computeParamMutates? P cert with
  | .ok pm => pm
  | .error _ =>
    (List.range P.size).foldl (init := paramMutInit P cert) fun m f =>
      match P.fun? f with
      | some fd =>
        if (cert.arrayPrims.get? f).isSome then m
        else m.insert f (List.replicate fd.params.length true)
      | none => m

/-- Refuse (`rt.internal`) an array program (`cert.hasArrays`) on which an analysis `lowerRep` or
`Rt.BigNat.lowerRepBig` runs would not reach its fixpoint within its bound: the parameter flags,
then each function's taint and liveness (every function but the native array primitives, which
the lowerings generate instead). Run before lowering, so that no lowering uses a partial result.
A program without arrays runs none of the analyses. -/
def checkArrayAnalyses (cert : Fir.Rep.Cert) (P : Cfg.Program) : Except Error Unit := do
  if !cert.hasArrays then return
  let pm ← computeParamMutates? P cert
  for f in List.range P.size do
    if let some fd := P.fun? f then
      if (cert.arrayPrims.get? f).isNone then
        let _ ← computeTainted? f fd pm
        let _ ← computeLiveIn? f fd

/-! ### DR3 Native Array Primitive Wrapper Generator (`arrayPrimFunc`) -/

private def toRawWordParam (reg : VReg) (rep : Fir.Rep) : M Lir.Arg :=
  match rep with
  | .word => pure (.v reg)
  | .tobj => bin .shr (.v reg) (.imm 1)
  | .obj => do
    let r ← freshReg
    unbox64 r (.v reg)
    pure (.v r)
  | .erased => pure (.imm 0)

private def paramRegRep (f : FunId) (params : List VReg) (fc : Fir.Rep.FunCert) (idx : Nat) :
    M (VReg × Fir.Rep) := do
  let some reg := params[idx]? | throw (.form f s!"array prim param index {idx} out of range")
  pure (reg, fc.params.getD idx .tobj)

/-- Generate a thin O(1) LIR wrapper function for a pinned `Array` / `ByteArray` / `Array UInt64`
primitive (`spec : Fir.Rep.ArrayPrimSpec`), delegating directly to the relocated native runtime
at `arrBase + fn*` (`Rt.Rc.Array.Procs` + `Wire`). -/
def arrayPrimFunc (arrBase : FunId) (f : FunId) (fd : Cfg.Fun) (fc : Fir.Rep.FunCert)
    (spec : Fir.Rep.ArrayPrimSpec) (conv : Lir.Conv) : Except Error Lir.Func := do
  let some b0 := fd.blocks.head? | throw (.missingBlock f 0)
  let params := b0.params.map (·.1)
  let supply := max fd.vars (maxVar fd + 1)
  let bodyM : M Unit := do
    openAt 0 []
    match spec.op, spec.argIdx with
    | .emptyCap, [] =>
      let callee := arrBase + match spec.kind with
        | .boxed => Rt.Rc.Array.fnEmptyCapBoxed
        | .limbs => Rt.Rc.Array.fnEmptyCapLimbs
        | .bytes => Rt.Rc.Array.fnByteEmptyCap
      let res ← freshReg
      emit (.call [res] callee [.imm 0])
      close (.ret (.v res))
    | .emptyCap, [ci] =>
      let (creg, crep) ← paramRegRep f params fc ci
      let cap ← toRawWordParam creg crep
      let callee := arrBase + match spec.kind with
        | .boxed => Rt.Rc.Array.fnEmptyCapBoxed
        | .limbs => Rt.Rc.Array.fnEmptyCapLimbs
        | .bytes => Rt.Rc.Array.fnByteEmptyCap
      let res ← freshReg
      emit (.call [res] callee [cap])
      close (.ret (.v res))
    | .size, [ai] =>
      let (areg, _) ← paramRegRep f params fc ai
      let raw ← freshReg
      emit (.call [raw] (arrBase + Rt.Rc.Array.fnSize) [.v areg])
      if fc.ret == .word then
        close (.ret (.v raw))
      else
        let out ← freshReg
        checked64 out (.v raw)
        close (.ret (.v out))
    | .get, [ai, ii] =>
      let (areg, _) ← paramRegRep f params fc ai
      let (ireg, irep) ← paramRegRep f params fc ii
      let idx ← toRawWordParam ireg irep
      match spec.kind with
      | .bytes =>
        let raw ← freshReg
        emit (.call [raw] (arrBase + Rt.Rc.Array.fnByteGet) [.v areg, idx])
        if fc.ret == .word then close (.ret (.v raw))
        else
          let out ← temp (retag (.v raw))
          close (.ret out)
      | .limbs =>
        let raw ← freshReg
        emit (.call [raw] (arrBase + Rt.Rc.Array.fnGetWord) [.v areg, idx])
        let out ← freshReg
        finishRaw64 out fc.ret (.v raw)
        close (.ret (.v out))
      | .boxed =>
        let res ← freshReg
        emit (.call [res] (arrBase + Rt.Rc.Array.fnGetWord) [.v areg, idx])
        -- Aliasing rule 3: reading a boxed element shares it with the containing array.
        emit (.call [] (arrBase + Rt.Rc.Array.fnIncVal) [.v res])
        if fc.ret == .word then
          let out ← freshReg
          unbox64 out (.v res)
          close (.ret (.v out))
        else
          close (.ret (.v res))
    | .getBang, [ai, ii] =>
      unless spec.kind == .bytes do
        throw (.form f "array prim getBang is only supported for ByteArray (.bytes)")
      let (areg, _) ← paramRegRep f params fc ai
      let (ireg, irep) ← paramRegRep f params fc ii
      let idx ← toRawWordParam ireg irep
      let sz ← freshReg
      emit (.call [sz] (arrBase + Rt.Rc.Array.fnSize) [.v areg])
      let inB ← newLabel
      let oobB ← newLabel
      close (.br .ult idx (.v sz) (loc inB) (loc oobB))
      openAt inB []
      let raw ← freshReg
      emit (.call [raw] (arrBase + Rt.Rc.Array.fnByteGet) [.v areg, idx])
      if fc.ret == .word then close (.ret (.v raw))
      else
        let out ← temp (retag (.v raw))
        close (.ret out)
      openAt oobB []
      if fc.ret == .word then close (.ret (.imm 0))
      else close (.ret (.imm (UInt64.ofNat 1)))
    | .set, [ai, ii, vi] =>
      let (areg, _) ← paramRegRep f params fc ai
      let (ireg, irep) ← paramRegRep f params fc ii
      let (vreg, vrep) ← paramRegRep f params fc vi
      let idx ← toRawWordParam ireg irep
      let res ← freshReg
      match spec.kind with
      | .bytes =>
        let b ← toRawWordParam vreg vrep
        emit (.call [res] (arrBase + Rt.Rc.Array.fnByteSet) [.v areg, idx, b])
      | .limbs =>
        let w ← toRawWordParam vreg vrep
        emit (.call [res] (arrBase + Rt.Rc.Array.fnSetLimbs) [.v areg, idx, w])
      | .boxed =>
        let va ← if vrep == .word then do
            let b ← freshReg; box64 b (.v vreg); pure (.v b)
          else pure (.v vreg)
        emit (.call [res] (arrBase + Rt.Rc.Array.fnSetBoxed) [.v areg, idx, va])
      close (.ret (.v res))
    | .push, [ai, vi] =>
      let (areg, _) ← paramRegRep f params fc ai
      let (vreg, vrep) ← paramRegRep f params fc vi
      let res ← freshReg
      match spec.kind with
      | .bytes =>
        let b ← toRawWordParam vreg vrep
        emit (.call [res] (arrBase + Rt.Rc.Array.fnBytePush) [.v areg, b])
      | .limbs =>
        let w ← toRawWordParam vreg vrep
        emit (.call [res] (arrBase + Rt.Rc.Array.fnPushLimbs) [.v areg, w])
      | .boxed =>
        let va ← if vrep == .word then do
            let b ← freshReg; box64 b (.v vreg); pure (.v b)
          else pure (.v vreg)
        emit (.call [res] (arrBase + Rt.Rc.Array.fnPushBoxed) [.v areg, va])
      close (.ret (.v res))
    | .pop, [ai] =>
      let (areg, _) ← paramRegRep f params fc ai
      let callee := arrBase + match spec.kind with
        | .boxed => Rt.Rc.Array.fnPopBoxed
        | .limbs => Rt.Rc.Array.fnPopLimbs
        | .bytes => Rt.Rc.Array.fnBytePop
      let res ← freshReg
      emit (.call [res] callee [.v areg])
      close (.ret (.v res))
    | .extract, [ai, bi, ei] =>
      let (areg, _) ← paramRegRep f params fc ai
      let (breg, brep) ← paramRegRep f params fc bi
      let (ereg, erep) ← paramRegRep f params fc ei
      let bRaw ← toRawWordParam breg brep
      let eRaw ← toRawWordParam ereg erep
      let callee := arrBase + match spec.kind with
        | .boxed => Rt.Rc.Array.fnExtractBoxed
        | .limbs => Rt.Rc.Array.fnExtractLimbs
        | .bytes => Rt.Rc.Array.fnByteExtract
      let res ← freshReg
      emit (.call [res] callee [.v areg, bRaw, eRaw])
      close (.ret (.v res))
    | .copySlice, [si, soi, di, doi, li] =>
      let (sreg, _) ← paramRegRep f params fc si
      let (soreg, sorep) ← paramRegRep f params fc soi
      let (dreg, _) ← paramRegRep f params fc di
      let (doreg, dorep) ← paramRegRep f params fc doi
      let (lreg, lrep) ← paramRegRep f params fc li
      let soRaw ← toRawWordParam soreg sorep
      let doRaw ← toRawWordParam doreg dorep
      let lRaw ← toRawWordParam lreg lrep
      let callee := arrBase + match spec.kind with
        | .boxed => Rt.Rc.Array.fnCopySliceBoxed
        | .limbs => Rt.Rc.Array.fnCopySliceLimbs
        | .bytes => Rt.Rc.Array.fnByteCopySlice
      let res ← freshReg
      emit (.call [res] callee [.v sreg, soRaw, .v dreg, doRaw, lRaw])
      close (.ret (.v res))
    | .swap, [ai, ii, ji] =>
      let (areg, _) ← paramRegRep f params fc ai
      let (ireg, irep) ← paramRegRep f params fc ii
      let (jreg, jrep) ← paramRegRep f params fc ji
      let iRaw ← toRawWordParam ireg irep
      let jRaw ← toRawWordParam jreg jrep
      let callee := arrBase + match spec.kind with
        | .limbs => Rt.Rc.Array.fnSwapLimbs
        | _ => Rt.Rc.Array.fnSwapBoxed
      let res ← freshReg
      emit (.call [res] callee [.v areg, iRaw, jRaw])
      close (.ret (.v res))
    | _, _ => throw (.form f "array prim spec arity mismatch")
  let ((), st) ← bodyM.run { fresh := supply }
  let pblocks ← chunkBlocks f st
  let (starts, _) := chunkStarts 0 [pblocks]
  let raw ← resolveChunks f starts [(pblocks, 0)]
  let seen := reachable raw
  unless reachClosed raw seen do throw (.internal f "array prim wrapper has unreached successor")
  pure (Lir.Func.splitCriticalEdges
    { name := s!"f{f}", params, results := 1, blocks := (pruneWith seen raw).toArray, conv })

def blockCodeRep (f : FunId) (T : Tables) (cert : Fir.Rep.Cert) (fc : Fir.Rep.FunCert)
    (blockReps : Src.NatMap (List Fir.Rep)) (uses : Src.NatMap Nat) (src : Nat)
    (b : Cfg.Block) (sc : StrCtx := {}) (rc : RcCtx := {}) : M Unit :=
  let lt := if rc.enabled then liveAtTerm rc.liveIn b else .leaf
  match fusable T uses b with
  | some (init, c, a, a') => do
    let ann := if rc.enabled then annotateBody (setAddList lt (Cfg.Check.argVars [a, a'])) init
               else init.map (·, .leaf)
    if ← instrsRepAnn f T cert fc sc rc lt ann then
      fusedEndRep f T cert fc blockReps src b c a a' sc rc
  | none => do
    let ann := if rc.enabled then annotateBody lt b.body else b.body.map (·, .leaf)
    if ← instrsRepAnn f T cert fc sc rc lt ann then
      termRep f T cert fc blockReps src b.term sc rc

def blockRep (f : FunId) (T : Tables) (cert : Fir.Rep.Cert) (fc : Fir.Rep.FunCert)
    (blockReps : Src.NatMap (List Fir.Rep)) (uses : Src.NatMap Nat) (src : Nat)
    (entry : Bool) (b : Cfg.Block) (sc : StrCtx := {}) (rc : RcCtx := {}) : M Unit := do
  openAt 0 (if entry then [] else b.params.map (·.1))
  blockCodeRep f T cert fc blockReps uses src b sc rc

def chunksRep (f : FunId) (T : Tables) (cert : Fir.Rep.Cert) (fc : Fir.Rep.FunCert)
    (blockReps : Src.NatMap (List Fir.Rep)) (uses : Src.NatMap Nat) (merged : Bool)
    (bs : List (Cfg.Block × Nat)) (fresh : VReg) (sc : StrCtx := {}) (rc : RcCtx := {}) :
    Except Error (List (List PBlock) × VReg) :=
  match bs with
  | [] => pure ([], fresh)
  | (b, i) :: bs => do
    let ((), st) ← (blockRep f T cert fc blockReps uses i (merged && i == 0) b sc rc).run { fresh }
    let blocks ← chunkBlocks f st
    let (rest, fresh) ← chunksRep f T cert fc blockReps uses merged bs st.fresh sc rc
    pure (blocks :: rest, fresh)

def functionRawRep (T : Tables) (cert : Fir.Rep.Cert) (f : FunId) (fd : Cfg.Fun)
    (sc : StrCtx := {}) (rc : RcCtx := {}) : Except Error (List VReg × List Lir.Block) := do
  let some b0 := fd.blocks.head? | throw (.missingBlock f 0)
  if let some b := misordered fd then throw (.edgeOrder f b)
  let fc := cert.funCert f
  let blockReps : Src.NatMap (List Fir.Rep) :=
    Src.NatMap.ofDense (fd.blocks.map fun b => b.params.map fun (v, _) => fc.varRep v)
  let rcFun : RcCtx :=
    if !rc.enabled then rc
    else
      { rc with
        tainted := computeTainted fd rc.paramMut
        liveIn := computeLiveIn fd
        blockParams := Src.NatMap.ofDense (fd.blocks.map fun b => b.params.map (·.1)) }
  let merged := !(fd.blocks.any fun b => b.term.edges.any (·.target == 0))
  let supply := max fd.vars (maxVar fd + 1)
  let arity := b0.params.length
  let (params, supply) :=
    if merged then (b0.params.map (·.1), supply)
    else ((List.range arity).map (supply + ·), supply + arity)
  let uses := useCounts fd
  let (cs, _) ← chunksRep f T cert fc blockReps uses merged fd.blocks.zipIdx supply sc rcFun
  let (starts, _) := chunkStarts (if merged then 0 else 1) cs
  let body ← resolveChunks f starts cs.zipIdx
  let entry : List Lir.Block :=
    if merged then [] else [{ term := .jump { target := starts.getD 0 1, args := params.map .v } }]
  pure (params, entry ++ body)

def functionRep (T : Tables) (cert : Fir.Rep.Cert) (f : FunId) (fd : Cfg.Fun)
    (conv : Lir.Conv) (sc : StrCtx := {}) (rc : RcCtx := {}) : Except Error Lir.Func := do
  if rc.enabled then
    match cert.arrayPrims.get? f with
    | some spec => return ← arrayPrimFunc rc.arrBase f fd (cert.funCert f) spec conv
    | none => pure ()
  let (params, raw) ← functionRawRep T cert f fd sc rc
  let seen := reachable raw
  unless reachClosed raw seen do throw (.internal f "a reached block has an unreached successor")
  pure (Lir.Func.splitCriticalEdges
    { name := s!"f{f}", params, results := 1, blocks := (pruneWith seen raw).toArray, conv })

def functionsRep (T : Tables) (cert : Fir.Rep.Cert) (P : Cfg.Program)
    (roots : List (FunId × String)) (fs : List Nat) (sc : StrCtx := {}) (rc : RcCtx := {}) :
    Except Error (List Lir.Func) :=
  match fs with
  | [] => pure []
  | f :: fs => do
    let some fd := P.fun? f | throw (.missingFun f)
    let conv := match roots.lookup f with
      | some s => .sysvExport s
      | none => .internal
    pure ((← functionRep T cert f fd conv sc rc) :: (← functionsRep T cert P roots fs sc rc))

end LowerRep

open Lower LowerRep in
/-- **DR2 Stage W2 + DR3 Native Arrays + DR1/DR4 Static Strings lowering**:
Cfg + checked `Fir.Rep.Cert` → Lir with:
* raw 64-bit `UInt64` registers, `box64`/`unbox64`, `nscalar > 0` scalar tails, and
  zero-alloc hardware limb-pair fusion (`Lir.Stmt.limb`, `Lir.Rhs.bsr64`);
* DR3 O(1) contiguous `Array α`, `ByteArray`, and unboxed `Array UInt64` (`LimbArray`)
  via relocated `Rt.Rc.Array.extendedArrayRuntimeFuncs` and aliasing-safe mini-RC;
* DR1/DR4 `.rodata` static UTF-8 string literals (direct `.imm (base + off)` when
  `cfg.rodataBase = some base`, or position-independent `strLitProc` when `none`). -/
def lowerRep (cfg : Config) (cert : Fir.Rep.Cert) (P : Cfg.Program) : Except Error Lowered := do
  let some main := P.exports.head? | throw .noExports
  if let some (f, _) := P.funs.toList.find? (P.size ≤ ·.1) then throw (.funRange f)
  let named := P.exports.zipIdx.map fun (f, i) => (f, symbolOf ((cfg.names[i]?).getD s!"root{i}"))
  let roots := named.map fun (f, s) => (f, (named.lookup f).getD s)
  let hasArr := cert.hasArrays
  let arrBase := P.size + 3
  let arrProcs : List Lir.Func :=
    if hasArr then Rt.Rc.Array.extendedArrayRuntimeFuncs arrBase cert.listNilTag cert.listConsTag
    else []
  let rc : RcCtx :=
    if hasArr then { enabled := true, arrBase, paramMut := computeParamMutates P cert }
    else {}
  let strs := LowerStr.collectStrings P
  let strBase := arrBase + arrProcs.length
  let (sc, strProcs, rodata, rodataExports) :
      StrCtx × List Lir.Func × Option ByteArray × List X86.ELF.RodataSymbol :=
    if strs.isEmpty then ({}, [], none, [])
    else
      let (rtbl, strOffs) := LowerStr.buildStringRodata strs
      match cfg.rodataBase with
      | some base =>
        ({ rodataAddrs := strOffs.map fun (s, off) => (s, base + UInt64.ofNat off) },
         [], some rtbl.bytes, rtbl.symbols)
      | none =>
        ({ strFns := strOffs.zipIdx.map fun ((s, _), i) => (s, strBase + i) },
         strOffs.zipIdx.map fun ((s, _), i) => Rt.Rc.Array.strLitProc i s,
         some rtbl.bytes, rtbl.symbols)
  let funcs ← functionsRep (tables P) cert P roots (List.range P.size) sc rc
  let allFuncs := funcs ++ [Procs.cxInit, Procs.natPow, Procs.natGcd] ++ arrProcs ++ strProcs
  pure { program := { funcs := allFuncs.toArray, main }
         init := P.size, natPow := P.size + 1, natGcd := P.size + 2, roots
         rodata, rodataExports }

end IxCC.Rt
