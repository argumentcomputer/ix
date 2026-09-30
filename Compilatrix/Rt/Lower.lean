import Compilatrix.Cfg.WellFormed
import Compilatrix.Lir.SplitEdges
import Compilatrix.Rt.Procs.Entry
import Compilatrix.Rt.Procs.Nat

/-! # Cfg → Lir (`Rt.lower`, the Phase 1 fragment)

The data refinement of design note `plans/x86-v2/04-runtime.md` §8, for
Cfg programs of the immortal fragment (03 §4.4, 04 §8.1): no RC operation,
no credit, no closure. On the recheck path in style P (proved once, re-run;
04 §10), so it is written in kernel-evaluable style (D17): structural
recursion over lists, `Src.NatMap`/`NatSet`, a state monad over plain data,
no `HashMap`, no array indexing, no well-founded recursion. It reads no
certificate.

**Values** (`Rt.Layout`, 04 §2): a `Nat` literal `n` is the immediate
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
entry on (06 S32). Block 0 carries the function's parameters; when some
edge enters it, a fresh parameterless entry block binds the parameters and
jumps to it (Lir entries have no predecessors). Blocks no path reaches (Cfg
allows dead join points; Lir does not) are dropped, keeping the order, and
`Lir.Func.splitCriticalEdges` splits whatever critical edges remain.

**Instructions.**
* `alloc` of a field-less constructor is its immediate; otherwise the
  immortal bump of 04 §8.1: load `bump`, add the cell size, compare with
  `limit` (`fail heap` above it), store `bump`, the static header (`scan =
  fields`, `cls = 0`, `rc = INT32_MIN`, as two 32-bit stores) and the
  fields.
* `proj` is a load at `8 + 8i`; the `Nat` successor's field is `v − 2`.
* Primitives on tagged words (04 §2): `natAdd` by `brOvf addC` on `a − 1`
  and `b` (carry: `fail natOverflow`); `natSub` and `natPred` truncate with a
  `select`; `natMul` untags one side, multiplies, and checks the product by
  division; `natDiv`/`natMod` untag, divide by a nonzero divisor, and select
  `n / 0 = 0`, `n % 0 = n`; comparisons compare the words (tagging is
  monotone) and select the `Bool` words; `natLand`/`natLor` keep the tag
  bit, `natXor` restores it; `natShr` shifts by the untagged count (a count
  above 63 gives 0); `natShl` shifts `2p` and checks that shifting back
  restores it; `natPow` and `natGcd` call the runtime procedures
  `rt_nat_pow` and `rt_nat_gcd` (`Rt.Procs.Nat`).
* A comparison whose only use is the block's `switch` on `Bool` becomes
  the branch itself.

**Switch** (04 §8 "Control"): on `Nat` keys, the zero test `v = 1`; on
field-less keys, a compare chain against `2·tag + 1`; on keys with fields,
the header's tag (`u16` at offset 2); mixed, the low bit first. Without a
default the last alternative is taken without a test (a value no
alternative names is stuck in Cfg). Keys are forgotten, tags kept.

`Rt.lower` appends `cx_init` and the two procedures (`Rt.Procs`) after the
program's functions, and marks each exported root `sysvExport
"cx_<name>"`. -/

namespace Compilatrix.Rt

open Compilatrix.Fir (FunId)
open Compilatrix.Lir (VReg Label Word)

/-- Why `Rt.lower` declines a program. -/
inductive Error where
  | noExports
  | missingFun (f : FunId)
  | missingBlock (f : FunId) (b : Nat)
  /-- A string literal: statics are Phase 2 (BCK-6). -/
  | string (f : FunId)
  /-- A primitive without a Phase 1 lowering. -/
  | prim (f : FunId) (op : Lam.Prim)
  /-- A `Bool`-valued primitive in a program without the pinned `Bool`
  constructors (Cfg is stuck there). -/
  | noBool (f : FunId)
  /-- A right-hand side Cfg is stuck on (a Fir `ctor`/`proj`, a projection
  outside the constructor, an allocation of the wrong arity). -/
  | form (f : FunId) (what : String)
  /-- A constructor outside the layout limits of 04 §3. -/
  | layout (f : FunId) (what : String)
  | switch (f : FunId) (b : Nat) (what : String)
  /-- An edge whose back flag disagrees with Cfg's label order (the clock
  map needs it). -/
  | edgeOrder (f : FunId) (b : Nat)
  /-- A chunk label left unfilled (a bug in the lowering). -/
  | internal (f : FunId) (what : String)
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

instance : ToString Error := ⟨Error.render⟩

/-- Names for the exported roots: `cx_<name>` per `Cfg.Program.exports`
entry, `root<i>` where a name is missing. -/
structure Config where
  names : List String := []
  deriving Inhabited

/-- `Rt.lower`'s output: the Lir program (its `main` the first root), the
runtime procedures' functions (`cx_init`, `rt_nat_pow`, `rt_nat_gcd`, right
after the program's), and each root's function and symbol, in export order. -/
structure Lowered where
  program : Lir.Program
  init : Lir.FunId
  natPow : Lir.FunId
  natGcd : Lir.FunId
  roots : List (Lir.FunId × String)
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

def tables (P : Cfg.Program) : Tables :=
  let word := fun (k : Option Key.CtorKey) =>
    k.bind fun k => (Fir.CtorInfo.ofKey P.ctors k).map fun c => ctor0Word c.tag
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

/-! ## Primitives on tagged words (04 §2) -/

/-- The untagged value of a word (`w >>> 1`). -/
def untag : Lir.Arg → M Lir.Arg
  | .imm w => pure (.imm (w >>> 1))
  | a => bin .shr a (.imm 1)

/-- `2q + 1` (`lea [q + q + 1]`). -/
def retag : Lir.Arg → Lir.Rhs
  | .imm w => .arg (.imm (2 * w + 1))
  | .v q => .addr { base := some (.v q), index := some (q, .one), disp := 1 }

/-- `a / b` or `a % b`, with `n / 0 = 0` and `n % 0 = n` (`zero a` is the
result for a zero divisor). -/
def divMod (x : VReg) (o : Lir.BinOp) (zero : Lir.Arg → Lir.Arg) (a b : Lir.Arg) : M Unit :=
  match b with
  | .imm w =>
    if w == 1 then assign x (.arg (zero a))
    else do
      let u ← untag a
      let q ← bin o u (.imm (w >>> 1))
      assign x (retag q)
  | b => do
    let u ← untag a
    let y ← untag b
    -- a zero divisor becomes 1, and its result is then replaced
    let y1 ← temp (.select .eq .w64 b (.imm 1) (.imm 1) y)
    let q ← bin o u y1
    let r ← temp (retag q)
    assign x (.select .eq .w64 b (.imm 1) (zero a) r)

def primitive (f : FunId) (T : Tables) (x : VReg) (op : Lam.Prim) (as : List Lir.Arg) : M Unit := do
  let bool := fun (c : Lir.Cond) (a b : Lir.Arg) => do
    let some (t, e) := T.bools | throw (.noBool f)
    assign x (.select c .w64 a b (.imm t) (.imm e))
  match op, as with
  | .natAdd, [a, b] =>
    -- (2p+1 − 1) + (2q+1), carry iff p + q ≥ 2^63
    let (a, b) ← match a, b with
      | a, .imm w => pure (a, Lir.Arg.imm (w - 1))
      | .imm w, b => pure (b, Lir.Arg.imm (w - 1))
      | a, b => do pure (← bin .sub a (.imm 1), b)
    check .natOverflow fun ok bad => .brOvf .addC x a b ok bad
  | .natSub, [a, b] =>
    let d ← bin .sub a b
    let r ← bin .or d (.imm 1)
    assign x (.select .ult .w64 a b (.imm 1) r)
  | .natMul, [a, b] =>
    -- p · 2q, checked by division (Lir has no carry-out multiply)
    let u ← untag a
    let t ← bin .sub b (.imm 1)
    let p ← bin .mul u t
    let u1 ← temp (.select .eq .w64 u (.imm 0) (.imm 1) u)
    let q ← bin .udiv p u1
    let c1 ← temp (.test .ne .w64 q t)
    let c2 ← temp (.test .ne .w64 u (.imm 0))
    let c ← bin .and c1 c2
    check .natOverflow fun ok bad => .br .ne c (.imm 0) bad ok
    assign x (.bin .or .w64 p (.imm 1))
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
  | op, _ => throw (.prim f op)

/-- The comparison a fused `Bool` switch branches on. -/
def compareOf : Lam.Prim → Option Lir.Cond
  | .natBeq => some .eq
  | .natBle => some .ule
  | .natBlt => some .ult
  | _ => none

/-! ## Allocation and projection -/

def isNatKey (T : Tables) (k : Key.CtorKey) : Bool :=
  T.known.natZero == some k || T.known.natSucc == some k

/-- The immortal bump allocation of 04 §8.1. -/
def alloc (f : FunId) (T : Tables) (x : VReg) (c : Fir.CtorInfo) (as : List Lir.Arg) : M Unit := do
  if isNatKey T c.key then throw (.layout f "a Nat constructor cell (Nat values are literals)")
  if c.nscalar != 0 then throw (.layout f "scalar fields are Phase 2")
  if as.length != c.arity then throw (.form f s!"an allocation of {as.length} fields for {c.arity}")
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
  | .bind x (.fir (.arg a)) => withOperands f [a] fun
    | [a] => assign x (.arg a)
    | _ => pure ()
  | .bind x (.fir (.prim op as)) => withOperands f as (primitive f T x op)
  | .bind x (.fir (.call g as)) => withOperands f as fun as => emit (.call [x] g as)
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
def edge (f : FunId) (src : Nat) (e : Cfg.Edge) : M PEdge := do
  unless e.back == decide (e.target ≤ src) do throw (.edgeOrder f src)
  match ← operands f e.args with
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

def switch (f : FunId) (T : Tables) (src : Nat) (x : VReg) (alts : List (Key.CtorKey × Cfg.Edge))
    (d : Option Cfg.Edge) : M Unit := do
  let es ← alts.mapM fun (k, e) => do
    let some kind := keyKind T k | throw (.switch f src "a key outside the constructor table")
    pure (kind, ← edge f src e)
  let dd ← d.mapM (edge f src)
  let nats := es.filter (·.1.isNat)
  if !nats.isEmpty then
    unless nats.length == es.length do throw (.switch f src "Nat keys mixed with other keys")
    let z := (es.find? fun (k, _) => match k with | .zero => true | _ => false).map (·.2)
    let s := (es.find? fun (k, _) => match k with | .succ => true | _ => false).map (·.2)
    match z, s, dd with
    | some ez, some es, _ => close (.br .eq (.v x) (.imm 1) ez es)
    | some ez, none, some ed => close (.br .eq (.v x) (.imm 1) ez ed)
    | none, some es, some ed => close (.br .eq (.v x) (.imm 1) ed es)
    | some e, none, none | none, some e, none | none, none, some e => close (.jump e)
    | none, none, none => close .trap
  else
    let imms := es.filterMap fun (k, e) => match k with
      | .imm w => some (Lir.Arg.imm w, e)
      | _ => none
    let cells := es.filterMap fun (k, e) => match k with
      | .cell t => some (Lir.Arg.imm (UInt64.ofNat t), e)
      | _ => none
    let loadTag : M Lir.Arg := temp (.load .w16 .zero (mem x tagOffset))
    match cells, imms, dd with
    | [], _, _ => chainOr (.v x) imms dd
    | _, [], none => do chainOr (← loadTag) cells none
    | _, _, _ =>
      -- the low bit first: an even word is a cell
      let p ← newLabel
      let i ← newLabel
      close (.br .tz (.v x) (.imm 1) (loc p) (loc i))
      openAt p
      chainOr (← loadTag) cells dd
      openAt i
      chainOr (.v x) imms dd

/-- A switch on the `Bool` a comparison just produced, as the branch. -/
def fusedSwitch (f : FunId) (T : Tables) (src : Nat) (c : Lir.Cond) (a b : Lir.Arg)
    (alts : List (Key.CtorKey × Cfg.Edge)) (d : Option Cfg.Edge) : M Unit := do
  let pick := fun (k : Option Key.CtorKey) =>
    match (alts.find? fun (k', _) => k == some k').map (·.2) with
    | some e => some e
    | none => d
  let te ← (pick T.known.boolTrue).mapM (edge f src)
  let fe ← (pick T.known.boolFalse).mapM (edge f src)
  match te, fe with
  | some t, some e => close (.br c a b t e)
  | some t, none | none, some t => close (.jump t)
  | none, none => close .trap

def term (f : FunId) (T : Tables) (src : Nat) : Cfg.Term → M Unit
  | .jump e => do close (.jump (← edge f src e))
  | .switch x alts d => switch f T src x alts d
  | .ret a => do
    let _ ← withOperands f [a] fun
      | [a] => close (.ret a)
      | _ => pure ()
  | .tcall g as => do
    let _ ← withOperands f as fun as => close (.tail g as)
  | .trap => close .trap

/-! ## Blocks and functions -/

/-- Uses of each variable in a function (instructions and terminators). -/
def useCounts (fd : Cfg.Fun) : Src.NatMap Nat :=
  let vars := fd.blocks.flatMap fun b =>
    b.body.flatMap (fun | .bind _ r => Cfg.Check.rhsVars r) ++ Cfg.Check.termVars b.term
  vars.foldl (fun m x => m.insert x (m.getD x 0 + 1)) .leaf

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

/-- A Cfg block's chunk (from label 0; `entry`: it is the function's entry,
whose parameters are the function's). -/
def block (f : FunId) (T : Tables) (uses : Src.NatMap Nat) (src : Nat) (entry : Bool)
    (b : Cfg.Block) : M Unit := do
  openAt 0 (if entry then [] else b.params.map (·.1))
  match fusable T uses b with
  | some (init, c, a, a') =>
    if ← instrs f T init then
      match ← operands f [a, a'] with
      | some [a, a'] =>
        match b.term with
        | .switch _ alts d => fusedSwitch f T src c a a' alts d
        | t => term f T src t
      | _ => close (.fail .natOverflow)
  | none => if ← instrs f T b.body then term f T src b.term

/-- The chunk's blocks in label order. -/
def chunkBlocks (f : FunId) (st : St) : Except Error (List PBlock) :=
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

/-- Drop the blocks no path from the entry reaches, keeping the order of the
rest (so forward edges stay forward and back edges backward). -/
def prune (blocks : List Lir.Block) : List Lir.Block :=
  let n := blocks.length
  let succ : Src.NatMap (List Label) := Src.NatMap.ofDense (blocks.map (·.term.succs))
  let seen := reach succ (n + 1) [0] (Src.NatSet.ofList [0])
  let kept := blocks.zipIdx.filter fun (_, l) => seen.contains l
  let rank : Src.NatMap Label := Src.NatMap.ofList (kept.zipIdx.map fun ((_, l), r) => (l, r))
  kept.map fun (b, _) =>
    { b with term := b.term.setEdges (b.term.edges.map fun e => { e with target := rank.getD e.target 0 }) }

/-! ## Functions -/

/-- The largest variable a function defines. -/
def maxVar (fd : Cfg.Fun) : Nat := (fd.blocks.flatMap Cfg.Check.blockDefs).foldl max 0

def function (T : Tables) (f : FunId) (fd : Cfg.Fun) (conv : Lir.Conv) : Except Error Lir.Func := do
  let some b0 := fd.blocks.head? | throw (.missingBlock f 0)
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
  let blocks := prune (entry ++ body)
  pure (Lir.Func.splitCriticalEdges
    { name := s!"f{f}", params, results := 1, blocks := blocks.toArray, conv })

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

open Lower in
/-- Cfg (the immortal fragment) → Lir, with `cx_init` after the program's
functions (04 §8.1). -/
def lower (cfg : Config) (P : Cfg.Program) : Except Error Lowered := do
  let some main := P.exports.head? | throw .noExports
  let named := P.exports.zipIdx.map fun (f, i) => (f, symbolOf ((cfg.names[i]?).getD s!"root{i}"))
  -- a function exported twice keeps its first name (one wrapper per function)
  let roots := named.map fun (f, s) => (f, (named.lookup f).getD s)
  let funcs ← functions (tables P) P roots (List.range P.size)
  pure { program := { funcs := (funcs ++ [Procs.cxInit, Procs.natPow, Procs.natGcd]).toArray, main }
         init := P.size, natPow := P.size + 1, natGcd := P.size + 2, roots }

end Compilatrix.Rt
