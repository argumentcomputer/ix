module

public import IxCK.Ixon.Codec

/-! # How deep a record nests

The executed kernel recurses on the native stack: the codec as it decodes an
expression or a universe, the reader as it expands shares, the typing core as
it walks a term. The depth limit (`Ix.Kernel.Admission.Limits.maxDepth`) bounds
the nesting of the input, in two places of the byte stage
(`Ix.Kernel.Admission.decodeWithin`):

* **before decoding**, `Depth.within` reads a record's bytes in the codec's
  grammar (`Ixon.getConstantWithUnivs` and the readers it calls) without
  building anything, and stops at the first expression or universe nested past
  the limit. Shares are leaves here. It keeps its pending reads in an array of
  words, so it takes no native stack per level and allocates nothing per read;
  the codec then decodes only records whose stored nesting is within the limit.
* **after decoding**, `Depth.expandedWithin` measures each decoded record's
  expressions with their shares expanded, as the reader will build them: the
  sharing entries in order, each against the depths of the entries before it
  (the only ones the reader lets it use), then the payload. This walk recurses
  on the native stack, one call per stored level: no deeper than the stored
  nesting the scan has just admitted under the same limit, through which the
  decoder has just recursed with larger frames, and never past one level beyond
  the limit. A table in which an entry refers to itself or to a later entry
  (which the reader refuses) is measured by the general post-order
  (`expandedPost`: explicit stack, each entry memoised, a share that reaches
  itself past any limit).

Levels count as the kernel's terms nest, the root at level 1: an application of
`n` arguments has its head `n` levels below it and its `k`-th argument
`n - k + 1` levels below (the kernel's spine is binary), a telescope of `n`
binders its `k`-th binder type `k` levels below and its body `n` levels below,
every other child (a `let`'s three, a projection's value, a `max`'s or `imax`'s
two) one level below; a universe `succ^k u` has `u` `k` levels below it.

Both are coverage bounds, not validity checks: no theorem depends on what they
compute (they only add declines). Bytes the scan cannot read are left to the
decoder, which rejects them; the scan reads with the decoder's own readers
(its one- and two-byte integer headers read in place, equal to the codec's
reader: `tagAt_eq`) and validates less, so it reads at least as far into any
record as the decoder does.
-/

@[expose] public section

namespace Ix.Kernel.Admission.Depth

open Ixon

/-- Why the scan stopped before the end of a record. -/
inductive Stop where
  /-- an expression or a universe nested past the limit -/
  | deep
  /-- bytes the scan cannot read: left to the decoder, which rejects them -/
  | unreadable
  deriving Repr, DecidableEq

/-- The codec's reader `r` run at byte `i`: its value and the next index. -/
@[inline] def readAt {α : Type} (r : GetM α) (bytes : ByteArray) (i : Nat) : Option (α × Nat) :=
  match r.run { idx := i, bytes } with
  | .ok a s => some (a, s.idx)
  | .error _ _ => none

/-- `getU8` at byte `i`, read in place (`u8At_eq`). -/
@[inline] def u8At (bytes : ByteArray) (i : Nat) : Option (UInt8 × Nat) :=
  if h : i < bytes.size then some (bytes[i], i + 1) else none

/-- `getTagN f` at byte `i` (`tagAt_eq`): a one- or two-byte header read in place with the
codec's own arithmetic, a wider one by the codec's reader. Inlined at a literal `f`, its powers
fold to constants. -/
@[inline] def tagAt (f : Nat) (bytes : ByteArray) (i : Nat) : Option (TagN × Nat) :=
  if h : i < bytes.size then
    let b := bytes[i]
    let flag := (b.toNat / 2 ^ (8 - f)).toUInt8
    let p := b.toNat % 2 ^ (8 - f)
    if p < 2 ^ (8 - f - 1) then some (⟨flag, p.toUInt64⟩, i + 1)
    else if p - 2 ^ (8 - f - 1) < 2 ^ (8 - f - 2) then
      if h' : i + 1 < bytes.size then
        some (⟨flag, (2 ^ (8 - f - 1) + (p - 2 ^ (8 - f - 1)) * 256 + bytes[i + 1].toNat).toUInt64⟩,
          i + 1 + 1)
      else none
    else readAt (getTagN f) bytes i
  else none

/-- Skip `n` TagN integers with no flag bits from byte `i`. -/
def skipTagN0 (bytes : ByteArray) : Nat → Nat → Option Nat
  | 0, i => some i
  | n + 1, i =>
    match tagAt 0 bytes i with
    | some (_, i) => skipTagN0 bytes n i
    | none => none

/-! ### The scan's pending reads

The scan's stack holds words; the top word of each pending read carries its kind
in its low three bits:

* `8 * L`: one expression at level `L`;
* `8 * L + 1`: one universe at level `L`;
* `L, n, 8 * k + 2` (top last): the `k`-th (from 0) of the `n` arguments of an
  application at level `L`; `8 * k + 3` a λ telescope's `k`-th binder, `8 * k + 4`
  a ∀ telescope's;
* `8 * r + 5`: `r` more expressions at level 1, one after another (a sharing
  table); `8 * r + 6`: `r` more universes at level 1 (a universe table).

The words are naturals in an array the loop owns, so a read pushes, pops and
rewrites them in place and allocates nothing. -/

/-- The scan's loop over its stack of pending reads, at most `fuel` steps from
byte `i`: the index after the last read and the deepest level met. Each step
reads a tag, or turns a pending argument or binder into one expression, or
takes the next expression or universe of a table, so `2 * bytes + count + 2`
steps suffice for any bytes holding a table of `count` (the caller's fuel).
Every call of itself is a tail call: the loop runs in constant native stack. -/
def loop (bytes : ByteArray) (limit : Nat) :
    Nat → Nat → Array Nat → Nat → Except Stop (Nat × Nat)
  | 0, _, _, _ => .error .unreadable
  | fuel + 1, i, stack, deepest =>
    if h : 0 < stack.size then
      let w := stack[stack.size - 1]
      let kind := w % 8
      if kind == 0 then
        let level := w / 8
        let stack := stack.pop
        if limit < level then .error .deep else
        match tagAt 4 bytes i with
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
            match tagAt 0 bytes i with
            | some (_, i) => loop bytes limit fuel i (stack.push (8 * (level + 1))) deepest
            | none => .error .unreadable
          | 0x7 =>
            if n == 0 || bytes.size < n then .error .unreadable else
            loop bytes limit fuel i ((((stack.push level).push n).push 2).push (8 * (level + n)))
              deepest
          | 0x8 =>
            if n == 0 || bytes.size < n then .error .unreadable else
            loop bytes limit fuel i (((stack.push level).push n).push 3) deepest
          | 0x9 =>
            if n == 0 || bytes.size < n then .error .unreadable else
            loop bytes limit fuel i (((stack.push level).push n).push 4) deepest
          | 0xA =>
            match u8At bytes i with
            | some (_, i) =>
              let child := 8 * (level + 1)
              loop bytes limit fuel i (((stack.push child).push child).push child) deepest
            | none => .error .unreadable
          | _ => .error .unreadable
      else if kind == 1 then
        let level := w / 8
        let stack := stack.pop
        if limit < level then .error .deep else
        match tagAt 2 bytes i with
        | none => .error .unreadable
        | some (tag, i) =>
          let deepest := max deepest level
          match tag.flag with
          | 0 =>
            if tag.value == 0 then loop bytes limit fuel i stack deepest
            else loop bytes limit fuel i (stack.push (8 * (level + tag.value.toNat) + 1)) deepest
          | 1 | 2 =>
            let child := 8 * (level + 1) + 1
            loop bytes limit fuel i ((stack.push child).push child) deepest
          | 3 => loop bytes limit fuel i stack deepest
          | _ => .error .unreadable
      else if kind == 5 || kind == 6 then
        let r := w / 8
        if r == 0 then loop bytes limit fuel i stack.pop deepest
        else
          loop bytes limit fuel i
            ((stack.set! (stack.size - 1) (8 * (r - 1) + kind)).push (if kind == 5 then 8 else 9))
            deepest
      else
        let k := w / 8
        let n := stack[stack.size - 2]!
        let level := stack[stack.size - 3]!
        if kind == 2 then
          let stack := if k + 1 < n then stack.set! (stack.size - 1) (8 * (k + 1) + 2)
            else stack.pop.pop.pop
          loop bytes limit fuel i (stack.push (8 * (level + n - k))) deepest
        else
          match u8At bytes i with
          | some (_, i) =>
            let stack := if k + 1 < n then stack.set! (stack.size - 1) (8 * (k + 1) + kind)
              else stack.pop.pop.pop.push (8 * (level + n))
            loop bytes limit fuel i (stack.push (8 * (level + k + 1))) deepest
          | none => .error .unreadable
    else .ok (i, deepest)

/-- The scan's monad: the codec's cursor, and a stop. -/
abbrev ScanM := EStateM Stop GetState

/-- A codec reader in the scan; its failure is an unreadable stop. -/
@[inline] def lift {α : Type} (r : GetM α) : ScanM α := fun s =>
  match EStateM.run r s with
  | .ok a s => .ok a s
  | .error _ s => .error .unreadable s

/-- The loop from the pending read `start` at the cursor, holding a table of `count`: the
deepest level of what it read. -/
@[inline] def run (limit start count : Nat) : ScanM Nat := fun s =>
  match loop s.bytes limit (2 * (s.bytes.size - s.idx) + count + 2) s.idx #[start] 0 with
  | .ok (i, d) => .ok d { s with idx := i }
  | .error e => .error e s

/-- One expression (`Ixon.getExpr`). -/
def expr (limit : Nat) : ScanM Nat := run limit 8 0

/-- `count` expressions one after another (`Ixon.getArray Ixon.getExpr`). -/
def exprs (limit count : Nat) : ScanM Nat := run limit (8 * count + 5) count

/-- `count` universes one after another (`Ixon.getArray Ixon.getUniv`). -/
def univs (limit count : Nat) : ScanM Nat := run limit (8 * count + 6) count

/-- `n` bytes skipped, if the record holds them (`Ixon.getBytes`'s test). -/
def skip (n : Nat) : ScanM Unit := fun s =>
  if s.idx + n ≤ s.bytes.size then .ok () { s with idx := s.idx + n } else .error .unreadable s

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
references (32 bytes each, skipped), the universe table. -/
def constant (limit : Nat) : ScanM Nat := do
  let deepest ← info limit
  let sharing := (← lift (getTagN 0)).value.toNat
  let deepest := max deepest (← exprs limit sharing)
  let refs := (← lift (getTagN 0)).value.toNat
  skip (32 * refs)
  let count := (← lift (getTagN 0)).value.toNat
  return max deepest (← univs limit count)

/-- **The scan of one record's bytes**: the deepest level of its expressions
(shares as leaves) and universes; `.deep` at the first past `limit`;
`.unreadable` if the bytes do not read in the grammar. -/
def record (limit : Nat) (bytes : ByteArray) : Except Stop Nat :=
  match (constant limit).run { idx := 0, bytes } with
  | .ok d _ => .ok d
  | .error e _ => .error e

/-- A record's stored nesting is within `limit`: the scan meets no level past
it (bytes it cannot read are within: the decoder rejects them). -/
def within (limit : Nat) (bytes : ByteArray) : Bool :=
  match record limit bytes with
  | .error .deep => false
  | _ => true

/-! ## Shares expanded -/

/-- The children of a decoded expression (the kernel's: one level below). -/
def children : Ixon.Expr → List Ixon.Expr
  | .prj _ _ b => [b]
  | .app f a => [f, a]
  | .lam _ t b | .all _ _ t b => [t, b]
  | .letE _ t v b => [t, v, b]
  | _ => []

/-- The expressions of a decoded record's payload. -/
def payload (c : Ixon.Constant) : Array Ixon.Expr :=
  let defn := fun (d : Ixon.Definition) => #[d.typ, d.value]
  let recr := fun (r : Ixon.Recursor) => #[r.typ] ++ r.rules.map (·.rhs)
  let indc := fun (i : Ixon.Inductive) => #[i.typ] ++ i.ctors.map (·.typ)
  match c.info with
  | .defn d => defn d
  | .recr r => recr r
  | .axio a => #[a.typ]
  | .quot q => #[q.typ]
  | .muts ms => ms.flatMap fun
      | .defn d => defn d
      | .indc i => indc i
      | .recr r => recr r
  | _ => #[]

/-- The deepest level among `e`'s nodes with its shares expanded, `e`'s root at
`level`: a share of an entry below `memo.size` stands for that entry, of depth
`memo[i]`; a share past the table is a leaf (as the post-order counts it; the
reader refuses it); `0` for a share of an entry at or past `memo.size` and within
the table (the caller then measures the record by the post-order). A level past
`limit` is returned as soon as it is met, without descending further, so the
recursion nests at most as deep as `e` is stored, and at most `limit + 1` calls. -/
def walk (memo : Array Nat) (size limit level : Nat) : Ixon.Expr → Nat
  | .share i =>
    let j := i.toNat
    if h : j < memo.size then level - 1 + memo[j]
    else if j < size then 0 else level
  | .prj _ _ b => if limit < level then level else walk memo size limit (level + 1) b
  | .app f a =>
    if limit < level then level else
    let x := walk memo size limit (level + 1) f
    if x == 0 || limit < x then x else
    let y := walk memo size limit (level + 1) a
    if y == 0 then 0 else max x y
  | .lam _ t b =>
    if limit < level then level else
    let x := walk memo size limit (level + 1) t
    if x == 0 || limit < x then x else
    let y := walk memo size limit (level + 1) b
    if y == 0 then 0 else max x y
  | .all _ _ t b =>
    if limit < level then level else
    let x := walk memo size limit (level + 1) t
    if x == 0 || limit < x then x else
    let y := walk memo size limit (level + 1) b
    if y == 0 then 0 else max x y
  | .letE _ t v b =>
    if limit < level then level else
    let x := walk memo size limit (level + 1) t
    if x == 0 || limit < x then x else
    let y := walk memo size limit (level + 1) v
    if y == 0 || limit < y then y else
    let z := walk memo size limit (level + 1) b
    if z == 0 then 0 else max x (max y z)
  | _ => level

/-- The sharing entries in order, each measured against the entries before it,
then the payload: `some true` when every one is within `limit`, `some false` at
the first past it, `none` when an entry refers to itself or a later entry. -/
def expandedInOrder (limit : Nat) (c : Ixon.Constant) : Option Bool := Id.run do
  let size := c.sharing.size
  let mut memo : Array Nat := Array.mkEmpty size
  for e in c.sharing do
    let d := walk memo size limit 1 e
    if d == 0 then return none
    if limit < d then return some false
    memo := memo.push d
  for e in payload c do
    if limit < walk memo size limit 1 e then return some false
  return some true

/-- A step of the post-order. -/
inductive Visit where
  /-- measure an expression -/
  | enter (e : Ixon.Expr)
  /-- the last `k` measured are a node's children: replace them by one more than their deepest -/
  | leave (k : Nat)
  /-- the last measured is sharing entry `i`'s depth -/
  | share (i : Nat)

/-- The largest of the last `k` values of `vals` (and `m`), and `vals` without them. Each value is
read before it is popped, so the pop is in place when `vals` is not shared. -/
def popMax (vals : Array Nat) : Nat → Nat → Nat × Array Nat
  | 0, m => (m, vals)
  | k + 1, m =>
    let top := vals.back?.getD 0
    popMax vals.pop k (max m top)

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
        let cs := children e
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

/-- **The general post-order**: a decoded record's payload and sharing table
with shares expanded, each sharing entry measured once, false past `limit` or on
a share that reaches itself. `fuel` bounds the post-order's steps (each stored
node is entered and left once, each share entered and recorded once: eight per
byte of the record suffice, a spine or telescope of n decoded nodes having n + 1
tags; the caller passes a bound from the record byte limit). -/
def expandedPost (limit fuel : Nat) (c : Ixon.Constant) : Bool :=
  let stack := (payload c).foldl (fun st e => st.push (Visit.enter e)) #[]
  let stack := (List.range c.sharing.size).foldl
    (fun st i => st.push (Visit.enter (.share i.toUInt64))) stack
  match expandLoop c.sharing limit fuel stack #[] (Array.replicate c.sharing.size none)
      (Array.replicate c.sharing.size false) with
  | some (vals, _, _) => vals.all (· ≤ limit)
  | none => false

/-- **A decoded record's expressions with shares expanded are within
`limit`**: its payload and its sharing table, each sharing entry measured once
(`expandedInOrder`; `expandedPost` when an entry refers to itself or a later
entry); false past the limit or on a share that reaches itself. -/
def expandedWithin (limit fuel : Nat) (c : Ixon.Constant) : Bool :=
  match expandedInOrder limit c with
  | some b => b
  | none => expandedPost limit fuel c

end Ix.Kernel.Admission.Depth

end
