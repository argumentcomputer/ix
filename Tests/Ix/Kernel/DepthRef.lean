import IxCK.Kernel.Admission.Depth

/-! # The depth scan before KI's rewrite: the oracle of `kernel-depth`'s `differential` case

`Ix.Kernel.Admission.Depth`'s scan as it was first written (engineer KH, at `32c4b10d1`): one
`Slot` object per pending read, every tag and byte read by the codec's own readers (`readAt
(getTagN f)`, `readAt getU8`), one loop run per expression. The kernel's scan now keeps its pending
reads as words, reads one- and two-byte headers in place (`Depth.tagAt_eq`) and runs one loop per
table; `differential` checks that both return the same on every record it generates, at several
limits, and on the same bytes mutated. -/

namespace Tests.Ix.Kernel.DepthRef

open Ixon
open Ix.Kernel.Admission.Depth (Stop readAt lift)

/-- A pending read of the scan, with the level its root is at. -/
inductive Slot where
  /-- one expression -/
  | expr (level : Nat)
  /-- the `k`-th (from 0) of the `n` arguments of an application at `level` -/
  | arg (k n level : Nat)
  /-- the `k`-th (from 0) of the `n` binders of a λ telescope at `level` -/
  | lam (k n level : Nat)
  /-- the `k`-th (from 0) of the `n` binders of a ∀ telescope at `level` -/
  | all (k n level : Nat)
  /-- one universe -/
  | univ (level : Nat)

/-- Skip `n` TagN integers with no flag bits from byte `i`. -/
def skipTagN0 (bytes : ByteArray) : Nat → Nat → Option Nat
  | 0, i => some i
  | n + 1, i =>
    match readAt (getTagN 0) bytes i with
    | some (_, i) => skipTagN0 bytes n i
    | none => none

/-- The scan's loop over its stack of pending reads, at most `fuel` steps from
byte `i`: the index after the last read and the deepest level met. Each step
reads a tag, or turns a telescope or spine slot into one expression slot, so
`2 * bytes + 2` steps suffice for any bytes. Every call of itself is a tail
call: the loop runs in constant native stack. -/
def loop (bytes : ByteArray) (limit : Nat) :
    Nat → Nat → Array Slot → Nat → Except Stop (Nat × Nat)
  | 0, _, _, _ => .error .unreadable
  | fuel + 1, i, stack, deepest =>
    match stack.back? with
    | none => .ok (i, deepest)
    | some slot =>
      let stack := stack.pop
      match slot with
      | .expr level =>
        if limit < level then .error .deep else
        match readAt (getTagN 4) bytes i with
        | none => .error .unreadable
        | some (tag, i) =>
          let deepest := max deepest level
          let n := tag.value.toNat
          match tag.flag with
          | 0x0 | 0x1 | 0x5 | 0x6 | 0xB => loop bytes limit fuel i stack deepest
          | 0x2 | 0x3 =>
            match skipTagN0 bytes (n + 1) i with
            | some i => loop bytes limit fuel i stack deepest
            | none => .error .unreadable
          | 0x4 =>
            match readAt (getTagN 0) bytes i with
            | some (_, i) => loop bytes limit fuel i (stack.push (.expr (level + 1))) deepest
            | none => .error .unreadable
          | 0x7 =>
            if n == 0 || bytes.size < n then .error .unreadable else
            loop bytes limit fuel i ((stack.push (.arg 0 n level)).push (.expr (level + n))) deepest
          | 0x8 =>
            if n == 0 || bytes.size < n then .error .unreadable else
            loop bytes limit fuel i (stack.push (.lam 0 n level)) deepest
          | 0x9 =>
            if n == 0 || bytes.size < n then .error .unreadable else
            loop bytes limit fuel i (stack.push (.all 0 n level)) deepest
          | 0xA =>
            match readAt getU8 bytes i with
            | some (_, i) =>
              let child := Slot.expr (level + 1)
              loop bytes limit fuel i (((stack.push child).push child).push child) deepest
            | none => .error .unreadable
          | _ => .error .unreadable
      | .arg k n level =>
        let stack := if k + 1 < n then stack.push (.arg (k + 1) n level) else stack
        loop bytes limit fuel i (stack.push (.expr (level + n - k))) deepest
      | .lam k n level =>
        match readAt getU8 bytes i with
        | some (_, i) =>
          let next := if k + 1 < n then Slot.lam (k + 1) n level else Slot.expr (level + n)
          loop bytes limit fuel i ((stack.push next).push (.expr (level + k + 1))) deepest
        | none => .error .unreadable
      | .all k n level =>
        match readAt getU8 bytes i with
        | some (_, i) =>
          let next := if k + 1 < n then Slot.all (k + 1) n level else Slot.expr (level + n)
          loop bytes limit fuel i ((stack.push next).push (.expr (level + k + 1))) deepest
        | none => .error .unreadable
      | .univ level =>
        if limit < level then .error .deep else
        match readAt (getTagN 2) bytes i with
        | none => .error .unreadable
        | some (tag, i) =>
          let deepest := max deepest level
          match tag.flag with
          | 0 =>
            if tag.value == 0 then loop bytes limit fuel i stack deepest
            else loop bytes limit fuel i (stack.push (.univ (level + tag.value.toNat))) deepest
          | 1 | 2 =>
            let child := Slot.univ (level + 1)
            loop bytes limit fuel i ((stack.push child).push child) deepest
          | 3 => loop bytes limit fuel i stack deepest
          | _ => .error .unreadable

/-- The scan's monad: the codec's cursor, and a stop. -/
abbrev ScanM := Ix.Kernel.Admission.Depth.ScanM

/-- The loop from `start` at the cursor: the deepest level of what it read. -/
@[inline] def run (limit : Nat) (start : Slot) : ScanM Nat := fun s =>
  match loop s.bytes limit (2 * (s.bytes.size - s.idx) + 2) s.idx #[start] 0 with
  | .ok (i, d) => .ok d { s with idx := i }
  | .error e => .error e s

/-- One expression (`Ixon.getExpr`). -/
def expr (limit : Nat) : ScanM Nat := run limit (.expr 1)

/-- One universe (`Ixon.getUniv`). -/
def univ (limit : Nat) : ScanM Nat := run limit (.univ 1)

/-- `Ixon.getDefinition`. -/
def definition (limit : Nat) : ScanM Nat := do
  let _ ← lift getU8
  let _ ← lift (getTagN 0)
  let typ ← expr limit
  let value ← expr limit
  return max typ value

/-- `Ixon.getRecursor`. -/
def recursor (limit : Nat) : ScanM Nat := do
  let _ ← lift getU8
  for _ in [0:5] do
    discard <| lift (getTagN 0)
  let mut deepest ← expr limit
  let rules := (← lift (getTagN 0)).value.toNat
  for _ in [0:rules] do
    discard <| lift (getTagN 0)
    deepest := max deepest (← expr limit)
  return deepest

/-- `Ixon.getConstructor`. -/
def ctor (limit : Nat) : ScanM Nat := do
  let _ ← lift (Serialize.get (α := Bool))
  for _ in [0:4] do
    discard <| lift (getTagN 0)
  expr limit

/-- `Ixon.getInductive`. -/
def inductive_ (limit : Nat) : ScanM Nat := do
  let _ ← lift (Serialize.get (α := Bool))
  for _ in [0:3] do
    discard <| lift (getTagN 0)
  let mut deepest ← expr limit
  let ctors := (← lift (getTagN 0)).value.toNat
  for _ in [0:ctors] do
    deepest := max deepest (← ctor limit)
  return deepest

/-- `Ixon.getMutConst`. -/
def mutConst (limit : Nat) : ScanM Nat := do
  match ← lift getU8 with
  | 0 => definition limit
  | 1 => inductive_ limit
  | 2 => recursor limit
  | _ => throw .unreadable

/-- `Ixon.getConstantInfo`. -/
def info (limit : Nat) : ScanM Nat := do
  let tag ← lift (getTagN 4)
  if tag.flag == Constant.FLAG_MUTS then
    let mut deepest := 0
    for _ in [0:tag.value.toNat] do
      deepest := max deepest (← mutConst limit)
    return deepest
  else if tag.flag == Constant.FLAG then
    match tag.value with
    | 0 => definition limit
    | 1 => recursor limit
    | 2 => do
      let _ ← lift (Serialize.get (α := Bool))
      let _ ← lift (getTagN 0)
      expr limit
    | 3 => do
      let _ ← lift getU8
      let _ ← lift (getTagN 0)
      expr limit
    | 4 => do let _ ← lift getConstructorProj; return 0
    | 5 => do let _ ← lift getRecursorProj; return 0
    | 6 => do let _ ← lift getInductiveProj; return 0
    | 7 => do let _ ← lift getDefinitionProj; return 0
    | _ => throw .unreadable
  else throw .unreadable

/-- `Ixon.getConstantWithUnivs`: the payload, the sharing table, the
references, the universe table. -/
def constant (limit : Nat) : ScanM Nat := do
  let mut deepest ← info limit
  let sharing := (← lift (getTagN 0)).value.toNat
  for _ in [0:sharing] do
    deepest := max deepest (← expr limit)
  let refs := (← lift (getTagN 0)).value.toNat
  for _ in [0:refs] do
    discard <| lift (Serialize.get (α := Address))
  let univs := (← lift (getTagN 0)).value.toNat
  for _ in [0:univs] do
    deepest := max deepest (← univ limit)
  return deepest

/-- **The scan of one record's bytes**: the deepest level of its expressions
(shares as leaves) and universes; `.deep` at the first past `limit`;
`.unreadable` if the bytes do not read in the grammar. -/
def record (limit : Nat) (bytes : ByteArray) : Except Stop Nat :=
  match (constant limit).run { idx := 0, bytes } with
  | .ok d _ => .ok d
  | .error e _ => .error e

/-- A record's stored nesting is within `limit`: the scan meets no level past
it (bytes it cannot read are within: the decoder rejects them). -/
def withinRef (limit : Nat) (bytes : ByteArray) : Bool :=
  match record limit bytes with
  | .error .deep => false
  | _ => true

/-! ## The expanded check before KI's rewrite (the measurement's "before": `kernel-depth-case old-*`) -/

inductive Visit where
  /-- measure an expression -/
  | enter (e : Ixon.Expr)
  /-- the last `k` measured are a node's children: replace them by one more than their deepest -/
  | leave (k : Nat)
  /-- the last measured is sharing entry `i`'s depth -/
  | share (i : Nat)

/-- The largest of the last `k` values of `vals` (and `m`), and `vals` without them; in place
when `vals` is not shared. -/
def popMax (vals : Array Nat) : Nat → Nat → Nat × Array Nat
  | 0, m => (m, vals)
  | k + 1, m => popMax vals.pop k (max m (vals.back?.getD 0))

/-- The post-order over `stack`, at most `fuel` steps: the depths measured
(`vals`) and the sharing entries' memo, or `none` when a depth passes `limit`,
a share reaches itself, or the fuel runs out. Every call of itself is a tail
call. -/
def expandLoop (sharing : Array Ixon.Expr) (limit : Nat) :
    Nat → Array Visit → Array Nat → Array (Option Nat) → Array Bool →
      Option (Array Nat × Array (Option Nat) × Array Bool)
  | 0, _, _, _, _ => none
  | fuel + 1, stack, vals, memo, active =>
    match stack.back? with
    | none => some (vals, memo, active)
    | some visit =>
      let stack := stack.pop
      match visit with
      | .enter (.share i) =>
        let i := i.toNat
        match sharing[i]? with
        | none => expandLoop sharing limit fuel stack (vals.push 1) memo active
        | some s =>
          match memo[i]? with
          | some (some h) => expandLoop sharing limit fuel stack (vals.push h) memo active
          | _ =>
            if active[i]?.getD false then none
            else
              expandLoop sharing limit fuel ((stack.push (.share i)).push (.enter s)) vals memo
                (active.set! i true)
      | .enter e =>
        let cs := Ix.Kernel.Admission.Depth.children e
        if cs.isEmpty then expandLoop sharing limit fuel stack (vals.push 1) memo active
        else
          expandLoop sharing limit fuel
            (cs.foldl (fun st c => st.push (.enter c)) (stack.push (.leave cs.length))) vals memo
            active
      | .leave k =>
        let (deepest, vals) := popMax vals k 0
        let h := deepest + 1
        if limit < h then none
        else expandLoop sharing limit fuel stack (vals.push h) memo active
      | .share i =>
        expandLoop sharing limit fuel stack vals (memo.set! i (some (vals.back?.getD 0)))
          (active.set! i false)

/-- **A decoded record's expressions with shares expanded are within
`limit`**: its payload and its sharing table, each sharing entry measured
once; false past the limit or on a share that reaches itself. `fuel` bounds the
post-order's steps (each stored node is entered and left once, each share
entered and recorded once: eight per byte of the record suffice, a spine
or telescope of n decoded nodes having n + 1 tags; the caller passes a bound
from the record byte limit). -/
def expandedWithinRef (limit fuel : Nat) (c : Ixon.Constant) : Bool :=
  let stack := (Ix.Kernel.Admission.Depth.payload c).foldl (fun st e => st.push (Visit.enter e)) #[]
  let stack := (List.range c.sharing.size).foldl
    (fun st i => st.push (Visit.enter (.share i.toUInt64))) stack
  match expandLoop c.sharing limit fuel stack #[] (Array.replicate c.sharing.size none)
      (Array.replicate c.sharing.size false) with
  | some (vals, _, _) => vals.all (· ≤ limit)
  | none => false


end Tests.Ix.Kernel.DepthRef
