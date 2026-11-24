import IxCC.Src.Hints
import IxCC.Src.Pinned
import IxCC.Ixon.V3.Env
import IxCC.Ixon.V3.Keys
import Std.Data.HashMap

/-! # Fast `.ixe` equation & word auto-discovery (`IxCC.Src.AutoHints`)

Discovers untrusted `Proposal`s (`.eqn` unfolding equations and `.word` fixed-width word
equations) directly from a decoded `Ixon.V3.Env` without requiring an external
`--equations EQ.json` sidecar, plus root resolution (`--root NAME`, `--root <64-hex>`,
`--root NAME=<64-hex>`) against named or anonymous `.ixe` closures.

## Design properties

* **Zero TCB expansion**: every emitted proposal is still gated by the existing verified
  `Table.Check` (`checkEqn`, `checkWord`) and revalidated by `Table.validate` / `Recheck`.
* **Statement-only `O(#theorems)` scan**: non-theorem records are skipped in O(1) via their
  2-byte Ixon v5 header; theorem proof terms (`d.value`) and unused sharing entries are
  skipped in place without allocating AST nodes, preserving `Ingress.reach`'s lazy proof
  loading via `Seeds.of`.
* **100% deterministic**: output proposals are canonically sorted by `(kind, subject, theorem)`
  using `Ixon.Address.cmpBytes`, independent of `HashMap` bucket order. -/

set_option autoImplicit false

namespace IxCC.Src.AutoHints

open IxCC.Ixon

/-! ## Wire-level statement-only skipping (never decodes proof terms) -/

/-- Skip one TagN (`f = 0`) value in raw bytes without allocating; returns `bytes.size + 1` on error. -/
@[inline] private def skipTagN0At (bytes : ByteArray) (idx : Nat) : Nat :=
  if idx < bytes.size then
    let b := (bytes.get! idx).toNat
    if b < 128 then idx + 1
    else if b < 192 then if idx + 2 ≤ bytes.size then idx + 2 else bytes.size + 1
    else if b == 192 then if idx + 3 ≤ bytes.size then idx + 3 else bytes.size + 1
    else if b == 193 then if idx + 4 ≤ bytes.size then idx + 4 else bytes.size + 1
    else if b == 194 then if idx + 5 ≤ bytes.size then idx + 5 else bytes.size + 1
    else if b == 195 then if idx + 9 ≤ bytes.size then idx + 9 else bytes.size + 1
    else bytes.size + 1
  else bytes.size + 1

private def readLEAt (bytes : ByteArray) (idx : Nat) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | k + 1, shift, acc =>
    readLEAt bytes (idx + 1) k (shift + 8) (acc ||| ((bytes.get! idx).toNat <<< shift))

/-- Skip `count` TagN (`f = 0`) values in raw bytes without allocating. -/
private def skipTagN0sAt (bytes : ByteArray) : Nat → Nat → Nat
  | 0, idx => idx
  | count + 1, idx =>
    let next := skipTagN0At bytes idx
    if next > bytes.size then bytes.size + 1
    else skipTagN0sAt bytes count next

/-- Decode TagN (`f = 4`) payload width & value at `idx` when `p ≥ 8`; returns `(val, nextIdx)`. -/
@[inline] private def readTagN4WideAt (bytes : ByteArray) (idx p : Nat) : Nat × Nat :=
  if p < 12 then
    if idx + 2 ≤ bytes.size then
      (8 + (p - 8) * 256 + (bytes.get! (idx + 1)).toNat, idx + 2)
    else (0, bytes.size + 1)
  else if p == 12 then
    if idx + 3 ≤ bytes.size then (1032 + readLEAt bytes (idx + 1) 2 0 0, idx + 3)
    else (0, bytes.size + 1)
  else if p == 13 then
    if idx + 4 ≤ bytes.size then (66568 + readLEAt bytes (idx + 1) 3 0 0, idx + 4)
    else (0, bytes.size + 1)
  else if p == 14 then
    if idx + 5 ≤ bytes.size then (16843784 + readLEAt bytes (idx + 1) 4 0 0, idx + 5)
    else (0, bytes.size + 1)
  else
    if idx + 9 ≤ bytes.size then (4311811080 + readLEAt bytes (idx + 1) 8 0 0, idx + 9)
    else (0, bytes.size + 1)

/-- Fast zero-allocation byte skipper for one Ixon v5 `Expr`. Tail-recursive with a single
`remaining` counter and explicit byte-length fuel; returns `bytes.size + 1` on error. -/
private def skipExprFastAux (bytes : ByteArray) : Nat → Nat → Nat → Nat
  | _, 0, idx => idx
  | 0, _ + 1, _ => bytes.size + 1
  | fuel + 1, rem + 1, idx =>
    if idx ≥ bytes.size then bytes.size + 1
    else
      let b := (bytes.get! idx).toNat
      let flag := b >>> 4
      let p := b &&& 0x0F
      match flag with
      | 0x0 | 0x1 | 0x5 | 0x6 | 0xB =>
        let next :=
          if p < 8 then idx + 1
          else if p < 12 then idx + 2
          else if p == 12 then idx + 3
          else if p == 13 then idx + 4
          else if p == 14 then idx + 5
          else idx + 9
        if next > bytes.size then bytes.size + 1
        else skipExprFastAux bytes fuel rem next
      | 0x2 | 0x3 =>
        let (val, next1) := if p < 8 then (p, idx + 1) else readTagN4WideAt bytes idx p
        if next1 > bytes.size || val > bytes.size - next1 then bytes.size + 1
        else
          let next2 := skipTagN0sAt bytes (val + 1) next1
          if next2 > bytes.size then bytes.size + 1
          else skipExprFastAux bytes fuel rem next2
      | 0x4 =>
        let next1 :=
          if p < 8 then idx + 1
          else if p < 12 then idx + 2
          else if p == 12 then idx + 3
          else if p == 13 then idx + 4
          else if p == 14 then idx + 5
          else idx + 9
        if next1 > bytes.size then bytes.size + 1
        else
          let next2 := skipTagN0At bytes next1
          if next2 > bytes.size then bytes.size + 1
          else skipExprFastAux bytes fuel (rem + 1) next2
      | 0x7 =>
        let (val, next) := if p < 8 then (p, idx + 1) else readTagN4WideAt bytes idx p
        if val == 0 || next > bytes.size || val > bytes.size - next then bytes.size + 1
        else skipExprFastAux bytes fuel (rem + 1 + val) next
      | 0x8 | 0x9 =>
        let (val, next) := if p < 8 then (p, idx + 1) else readTagN4WideAt bytes idx p
        if val == 0 || next > bytes.size || val > bytes.size - next then bytes.size + 1
        else skipExprFastAux bytes fuel (rem + val + 1) next
      | 0xA =>
        let next :=
          if p < 8 then idx + 1
          else if p < 12 then idx + 2
          else if p == 12 then idx + 3
          else if p == 13 then idx + 4
          else if p == 14 then idx + 5
          else idx + 9
        if next > bytes.size then bytes.size + 1
        else skipExprFastAux bytes fuel (rem + 3) next
      | _ => bytes.size + 1

private def skipExpr : _root_.Ixon.GetM Unit := do
  let st ← get
  let next := skipExprFastAux st.bytes (st.bytes.size - st.idx + 1) 1 st.idx
  if next > st.bytes.size then
    throw "auto-hints: skipExpr failed"
  set { st with idx := next }

/-- Skip `count` TagN (`f = 0`) values in place. -/
private def skipTagN0s (count : Nat) : _root_.Ixon.GetM Unit := do
  let st ← get
  let next := skipTagN0sAt st.bytes count st.idx
  if next > st.bytes.size then
    throw "auto-hints: skipTagN0s failed"
  set { st with idx := next }

/-- Skip `n` raw bytes at the cursor. -/
private def skipBytes (n : Nat) : _root_.Ixon.GetM Unit := do
  let st ← get
  if st.idx + n > st.bytes.size then
    throw "auto-hints: unexpected EOF while skipping bytes"
  set { st with idx := st.idx + n }

private def skipInductive : _root_.Ixon.GetM Unit := do
  let _ ← _root_.Ixon.getU8 -- isUnsafe
  skipTagN0s 3 -- lvls, params, indices
  skipExpr -- typ
  let numCtors := (← _root_.Ixon.getTagN 0).value
  _root_.Ixon.checkCount numCtors 6
  for _ in [0:numCtors.toNat] do
    let flags ← _root_.Ixon.getU8
    let _ ← _root_.Ixon.getTagN 0 -- lvls
    let _ ← _root_.Ixon.getTagN 0 -- cidx
    let _ ← _root_.Ixon.getTagN 0 -- params
    let fields := (← _root_.Ixon.getTagN 0).value
    if (flags &&& 2) == 2 then
      skipBytes fields.toNat
    skipExpr -- ctor typ

private def skipRecursor : _root_.Ixon.GetM Unit := do
  let _ ← _root_.Ixon.getU8 -- flags
  skipTagN0s 5 -- lvls, params, indices, motives, minors
  skipExpr -- typ
  let numRules := (← _root_.Ixon.getTagN 0).value
  _root_.Ixon.checkCount numRules 2
  for _ in [0:numRules.toNat] do
    let _ ← _root_.Ixon.getTagN 0 -- fields
    skipExpr -- rhs

private def skipMutConst : _root_.Ixon.GetM Unit := do
  match ← _root_.Ixon.getU8 with
  | 0 =>
    let _ ← _root_.Ixon.getU8 -- flags
    let _ ← _root_.Ixon.getTagN 0 -- lvls
    skipExpr -- typ
    skipExpr -- value
  | 1 => skipInductive
  | 2 => skipRecursor
  | t => throw s!"auto-hints: invalid mut const tag {t}"

/-! ## Checking whether an address is a safe definition in `env` -/

/-- Whether `blockAddr` holds a `.muts` block whose `memberIdx`-th member is a safe `.defn`
with universe parameter count `expectedLvls`. -/
private def checkMutMemberSafeDefn (bytes : ByteArray) (memberIdx : Nat)
    (expectedLvls : UInt64) : Bool :=
  let m : _root_.Ixon.GetM Bool := do
    let tag ← _root_.Ixon.getTagN 4
    unless tag.flag == V3.Constant.FLAG_MUTS && memberIdx < tag.value.toNat do
      return false
    for _ in [0:memberIdx] do
      skipMutConst
    let mtag ← _root_.Ixon.getU8
    if mtag != 0 then return false
    let flags ← _root_.Ixon.getU8
    if (flags &&& 0x0F) != 0x01 then return false
    let lvls := (← _root_.Ixon.getTagN 0).value
    return lvls == expectedLvls
  match m.run { bytes, idx := 0 } with
  | .ok b _ => b
  | .error _ _ => false

/-- Check whether `fAddr` in `env` is a safe definition (standalone `.defn` or mutual `dPrj`)
with universe parameter count `expectedLvls`. Runs in O(1) for standalone definitions. -/
private def isSafeDefnWithLvls (env : V3.Env) (fAddr : Ixon.Address)
    (expectedLvls : UInt64) : Bool :=
  match env.consts[fAddr]? with
  | none => false
  | some bytes =>
    if bytes.size ≥ 2 && bytes.get! 0 == 0xD0 then
      -- Standalone definition: low nibble 0x01 = (DefKind.defn <<< 2) ||| DefinitionSafety.safe
      if (bytes.get! 1 &&& 0x0F) != 0x01 then false
      else
        match (_root_.Ixon.getTagN 0).run { bytes, idx := 2 } with
        | .ok tag _ => tag.value == expectedLvls
        | .error _ _ => false
    else if bytes.size ≥ 34 && bytes.get! 0 == 0xD7 then
      -- Definition projection (`dPrj`) into a mutual block
      let parseProj : _root_.Ixon.GetM (Nat × Ixon.Address) := do
        let idx := (← _root_.Ixon.getTagN 0).value.toNat
        let raw ← _root_.Ixon.getBytes 32
        match Ixon.Address.ofBytes? raw with
        | some block => pure (idx, block)
        | none => throw "truncated dPrj block"
      match parseProj.run { bytes, idx := 1 } with
      | .ok (idx, blockAddr) _ =>
        match env.consts[blockAddr]? with
        | some blockBytes => checkMutMemberSafeDefn blockBytes idx expectedLvls
        | none => false
      | .error _ _ => false
    else
      false

/-! ## Expression inspection helpers (share-aware, total) -/

private def exprHasShare : _root_.Ixon.Expr → Bool
  | .share _ => true
  | .prj _ _ e => exprHasShare e
  | .app f a => exprHasShare f || exprHasShare a
  | .lam t b | .all t b => exprHasShare t || exprHasShare b
  | .letE _ _ t v b => exprHasShare t || exprHasShare v || exprHasShare b
  | _ => false

private def unshare (resolve : UInt64 → Option _root_.Ixon.Expr) :
    Nat → _root_.Ixon.Expr → _root_.Ixon.Expr
  | 0, e => e
  | fuel + 1, .share i =>
    match resolve i with
    | some e' => unshare resolve fuel e'
    | none => .share i
  | _, e => e

private def stripAlls (resolve : UInt64 → Option _root_.Ixon.Expr) :
    Nat → Nat → _root_.Ixon.Expr → Nat × _root_.Ixon.Expr
  | 0, k, e => (k, e)
  | fuel + 1, k, e =>
    match unshare resolve 64 e with
    | .all _ body => stripAlls resolve fuel (k + 1) body
    | e' => (k, e')

private def spineUnshared (resolve : UInt64 → Option _root_.Ixon.Expr) :
    Nat → _root_.Ixon.Expr → List _root_.Ixon.Expr → _root_.Ixon.Expr × Array _root_.Ixon.Expr
  | 0, e, acc => (e, acc.toArray)
  | fuel + 1, e, acc =>
    match unshare resolve 64 e with
    | .app f a => spineUnshared resolve fuel f (a :: acc)
    | e' => (e', acc.toArray)

private def isVar (resolve : UInt64 → Option _root_.Ixon.Expr)
    (e : _root_.Ixon.Expr) (idx : Nat) : Bool :=
  match unshare resolve 64 e with
  | .var j => j.toNat == idx
  | _ => false

/-- Check whether `e` is `ofNat_w (.var idx)` (used by `Table.Word.wordEqnType`). -/
private def isOfNatVar (resolve : UInt64 → Option _root_.Ixon.Expr)
    (refAt : UInt64 → Option Ixon.Address) (ofNatAddr? : Option Ixon.Address)
    (e : _root_.Ixon.Expr) (idx : Nat) : Bool :=
  match spineUnshared resolve 64 e [] with
  | (.ref rIdx us, args) =>
    us.isEmpty && args.size == 1 &&
      refAt rIdx == ofNatAddr? &&
      isVar resolve (args[0]!) idx
  | _ => false

/-- Fast pre-filter run on a standalone theorem's `typ` BEFORE skipping `d.value` or
`sharing`/`refs`. Returns `true` only when `typ` is provably neither an `Eq` unfolding
equation nor a word equation (zero false negatives: any `.share` on the relevant spine
conservatively returns `false`). -/
private def quickRejectStandaloneTyp (typ : _root_.Ixon.Expr) : Bool :=
  let noShare : UInt64 → Option _root_.Ixon.Expr := fun _ => none
  let (_, body) := stripAlls noShare 2048 0 typ
  match body with
  | .share _ => false
  | _ =>
    let (eqHead, eqArgs) := spineUnshared noShare 2048 body []
    match eqHead with
    | .share _ => false
    | .ref _ us =>
      if us.size != 1 || eqArgs.size != 3 then true
      else
        let lhs := eqArgs[1]!
        let (lhsHead, _) := spineUnshared noShare 2048 lhs []
        match lhsHead with
        | .share _ | .ref _ _ => false
        | _ => true
    | _ => true

/-- Whether `rhs` is a trivial self-call `f v₀ … vₖ₋₁` where every argument is a bare
LHS bound variable `< k` (filters out reflexivity `f x = f x` and commutativity lemmas
like `Nat.add x y = Nat.add y x` which `checkEqn` unconditionally rejects under `FE-3`). -/
private def isTrivialSelfRhs (resolve : UInt64 → Option _root_.Ixon.Expr)
    (refAt : UInt64 → Option Ixon.Address) (blockAddr? : Option Ixon.Address)
    (fAddr : Ixon.Address) (k : Nat) (rhs : _root_.Ixon.Expr) : Bool :=
  let (head, args) := spineUnshared resolve 2048 rhs []
  let headIsF := match head with
    | .ref idx _ => refAt idx == some fAddr
    | .recur idx _ =>
      match blockAddr? with
      | some ba => V3.defnProjAddr ba idx == fAddr
      | none => false
    | _ => false
  if !headIsF || args.size != k then false
  else args.all fun a =>
    match unshare resolve 64 a with
    | .var j => j.toNat < k
    | _ => false

/-! ## Candidate theorem classification -/

private structure PinIndex where
  eqAddr? : Option Ixon.Address
  wordOps : Std.HashMap Ixon.Address (Width × WordOp)
  wordOfNat : Std.HashMap Width Ixon.Address

private def PinIndex.of (pins : Pins) : PinIndex :=
  let eqAddr? := pins.eq.map Pinned.addrOfNat
  let wordOps := pins.wordOps.foldl (init := ({} : Std.HashMap Ixon.Address (Width × WordOp)))
    fun m ((w, op), n) => m.insert (Pinned.addrOfNat n) (w, op)
  let wordOfNat := pins.wordOps.foldl (init := ({} : Std.HashMap Width Ixon.Address))
    fun m ((w, op), n) => if op == .ofNat then m.insert w (Pinned.addrOfNat n) else m
  { eqAddr?, wordOps, wordOfNat }

/-- Classify one safe theorem `(thmAddr, lvls, typ)` into an optional `.word` or `.eqn`
`Proposal` without touching its proof term. -/
private def classifyTheorem (env : V3.Env) (pidx : PinIndex)
    (resolve : UInt64 → Option _root_.Ixon.Expr)
    (refAt : UInt64 → Option Ixon.Address)
    (blockAddr? : Option Ixon.Address)
    (thmAddr : Ixon.Address) (lvls : UInt64) (typ : _root_.Ixon.Expr) : Option Proposal := do
  let eqAddr ← pidx.eqAddr?
  let (k, body) := stripAlls resolve 2048 0 typ
  let (eqHead, eqArgs) := spineUnshared resolve 2048 body []
  let .ref eqIdx eqUs := eqHead | none
  guard (eqUs.size == 1 && eqArgs.size == 3 && refAt eqIdx == some eqAddr)
  let lhs := eqArgs[1]!
  let rhs := eqArgs[2]!
  let (lhsHead, lhsArgs) := spineUnshared resolve 2048 lhs []
  let (fAddr, fus) ← match lhsHead with
    | .ref fIdx us => (refAt fIdx).map (·, us)
    | .recur mIdx us => blockAddr?.map fun ba => (V3.defnProjAddr ba mIdx, us)
    | _ => none
  -- 1. Check fixed-width word equations (`ProposalKind.word`) first.
  if lvls == 0 && fus.isEmpty then
    if let some (w, op) := pidx.wordOps[fAddr]? then
      if op.isPrimitive then
        let ofNatAddr? := pidx.wordOfNat[w]?
        let wordMatch := match op with
          | .ofNat => k == 2 && lhsArgs.size == 1 && isVar resolve (lhsArgs[0]!) 1
          | _ =>
            if op.arity == 1 then
              k == 1 && lhsArgs.size == 1 &&
                isOfNatVar resolve refAt ofNatAddr? (lhsArgs[0]!) 0
            else if op.arity == 2 then
              k == 2 && lhsArgs.size == 2 &&
                isOfNatVar resolve refAt ofNatAddr? (lhsArgs[0]!) 1 &&
                isOfNatVar resolve refAt ofNatAddr? (lhsArgs[1]!) 0
            else false
        if wordMatch then
          return { kind := .word, subject := fAddr, theorem? := some thmAddr }
  -- 2. Check unfolding equations (`ProposalKind.eqn`): LHS must be `f #k-1 … #0`.
  guard (fus.size == lvls.toNat && lhsArgs.size == k)
  let varsOk := Id.run do
    for i in [0:k] do
      if !isVar resolve (lhsArgs[i]!) (k - 1 - i) then
        return false
    return true
  guard varsOk
  guard (isSafeDefnWithLvls env fAddr lvls)
  guard (!isTrivialSelfRhs resolve refAt blockAddr? fAddr k rhs)
  return { kind := .eqn, subject := fAddr, theorem? := some thmAddr }

/-- Scan the `sharing` and `refs` tables starting at the current cursor, returning
`(sharingOffsets, refsOffset, numRefs)`. When `recordSharing = false`, sharing entries
are skipped without allocating an offsets array. -/
private def scanSharingAndRefs (recordSharing : Bool) :
    _root_.Ixon.GetM (Array Nat × Nat × Nat) := do
  let numSharing := (← _root_.Ixon.getTagN 0).value.toNat
  _root_.Ixon.checkCount numSharing.toUInt64
  let mut offsets : Array Nat := if recordSharing then Array.mkEmpty numSharing else #[]
  for _ in [0:numSharing] do
    if recordSharing then
      offsets := offsets.push (← get).idx
    skipExpr
  let numRefs := (← _root_.Ixon.getTagN 0).value.toNat
  _root_.Ixon.checkCount numRefs.toUInt64 32
  let refsOffset := (← get).idx
  return (offsets, refsOffset, numRefs)

/-- Lazy on-demand sharing-entry decoder using pre-recorded wire offsets. -/
private def shareAt (bytes : ByteArray) (offsets : Array Nat) (i : UInt64) :
    Option _root_.Ixon.Expr := do
  let off ← offsets[i.toNat]?
  match _root_.Ixon.getExpr.run { bytes, idx := off } with
  | .ok e _ => some e
  | .error _ _ => none

/-- O(1) direct 32-byte slice lookup in a constant's `refs` table. -/
private def refSliceAt (bytes : ByteArray) (refsOffset numRefs : Nat) (i : UInt64) :
    Option Ixon.Address :=
  if i.toNat < numRefs then
    let start := refsOffset + i.toNat * 32
    if start + 32 ≤ bytes.size then
      Ixon.Address.ofBytes? (bytes.extract start (start + 32))
    else none
  else none

/-- Inspect one standalone safe theorem record (`bytes[0] == 0xD0`, low nibble of
`bytes[1]` == `0x09`), without decoding its proof term. -/
private def inspectStandaloneThm (env : V3.Env) (pidx : PinIndex)
    (thmAddr : Ixon.Address) (bytes : ByteArray) : Option Proposal :=
  let m : _root_.Ixon.GetM (Option Proposal) := do
    -- Byte 0 is 0xD0, byte 1 is flags; start at byte 2 (`lvls`).
    let lvls := (← _root_.Ixon.getTagN 0).value
    let typ ← _root_.Ixon.getExpr
    if quickRejectStandaloneTyp typ then
      return none
    -- Skip `d.value` (the proof term) without allocating any AST nodes.
    skipExpr
    let needShare := exprHasShare typ
    let (offsets, refsOffset, numRefs) ← scanSharingAndRefs needShare
    let resolve := if needShare then shareAt bytes offsets else fun _ => none
    let refAt := refSliceAt bytes refsOffset numRefs
    return classifyTheorem env pidx resolve refAt none thmAddr lvls typ
  match m.run { bytes, idx := 2 } with
  | .ok p _ => p
  | .error _ _ => none

/-- Inspect a `.muts` block for any safe theorem members, skipping all non-theorem
expressions and all proof terms. -/
private def inspectMutsBlock (env : V3.Env) (pidx : PinIndex)
    (blockAddr : Ixon.Address) (bytes : ByteArray) : Array Proposal :=
  let m : _root_.Ixon.GetM (Array Proposal) := do
    let tag ← _root_.Ixon.getTagN 4
    unless tag.flag == V3.Constant.FLAG_MUTS do return #[]
    let count := tag.value.toNat
    _root_.Ixon.checkCount tag.value
    let mut thms : Array (UInt64 × UInt64 × _root_.Ixon.Expr) := #[]
    for i in [0:count] do
      match ← _root_.Ixon.getU8 with
      | 0 =>
        let flags ← _root_.Ixon.getU8
        let lvls := (← _root_.Ixon.getTagN 0).value
        if (flags &&& 0x0F) == 0x09 then
          let typ ← _root_.Ixon.getExpr
          skipExpr -- skip proof term
          thms := thms.push (i.toUInt64, lvls, typ)
        else
          skipExpr
          skipExpr
      | 1 => skipInductive
      | 2 => skipRecursor
      | _ => return #[]
    if thms.isEmpty then return #[]
    let needShare := thms.any fun (_, _, t) => exprHasShare t
    let (offsets, refsOffset, numRefs) ← scanSharingAndRefs needShare
    let resolve := if needShare then shareAt bytes offsets else fun _ => none
    let refAt := refSliceAt bytes refsOffset numRefs
    let mut out : Array Proposal := #[]
    for (mIdx, lvls, typ) in thms do
      let thmAddr := V3.defnProjAddr blockAddr mIdx
      if let some prop := classifyTheorem env pidx resolve refAt (some blockAddr) thmAddr lvls typ then
        out := out.push prop
    return out
  match m.run { bytes, idx := 0 } with
  | .ok ps _ => ps
  | .error _ _ => #[]

private def kindRank : ProposalKind → Nat
  | .word => 0
  | .csimp => 1
  | .eqn => 2
  | .case => 3
  | .lazy => 4
  | .inline => 5

private def cmpProposal (a b : Proposal) : Ordering :=
  match compare (kindRank a.kind) (kindRank b.kind) with
  | .eq =>
    match a.subject.cmpBytes b.subject with
    | .eq =>
      match a.theorem?, b.theorem? with
      | some ta, some tb => ta.cmpBytes tb
      | none, some _ => .lt
      | some _, none => .gt
      | none, none => .eq
    | o => o
  | o => o

/-- **Fast `O(#theorems)` auto-discovery** over a decoded `Ixon.V3.Env`: scans theorem
records inspecting ONLY their statement types (`d.typ`, never loading proof terms),
emitting `.word` and `.eqn` proposals in canonical deterministic order. -/
def discover (env : V3.Env) (pins : Pins) : Array Proposal := Id.run do
  let pidx := PinIndex.of pins
  if pidx.eqAddr?.isNone then return #[]
  let mut found : Array Proposal := #[]
  for (addr, bytes) in env.consts do
    if bytes.size ≥ 2 && bytes.get! 0 == 0xD0 then
      -- Standalone definition: only inspect safe theorems (`low nibble == 0x09`).
      if (bytes.get! 1 &&& 0x0F) == 0x09 then
        if let some prop := inspectStandaloneThm env pidx addr bytes then
          found := found.push prop
    else if bytes.size ≥ 1 && (bytes.get! 0 >>> 4) == V3.Constant.FLAG_MUTS then
      let ps := inspectMutsBlock env pidx addr bytes
      if !ps.isEmpty then
        found := found ++ ps
  return found.qsort fun a b => cmpProposal a b == .lt

/-! ## Named `.ixe` metadata table (§4 names + §5 named → §2 constant rank) -/

private def natFromBytesLE (bs : ByteArray) : Nat := Id.run do
  let mut acc : Nat := 0
  let mut shift : Nat := 0
  for i in [0:bs.size] do
    acc := acc ||| ((bs.get! i).toNat <<< shift)
    shift := shift + 8
  return acc

/-- Extract the optional `name → Address` table from a `.ixe` environment's §4/§5 metadata.
Returns an empty map on anonymous `.ixe` closures (empty metadata or `numNamed == 0`). -/
def extractNamedMap (env : V3.Env) : Except String (Std.HashMap String Ixon.Address) := do
  if env.metadata.isEmpty then
    return {}
  let constOrder : Array Ixon.Address :=
    (env.consts.toArray.map (·.1)).qsort fun a b => a.cmpBytes b == .lt
  let parseMeta : _root_.Ixon.GetM (Std.HashMap String Ixon.Address) := do
    let numNames := (← _root_.Ixon.getTagN 0).value
    _root_.Ixon.checkCount numNames 33
    let mut namesLookup : Std.HashMap Ixon.Address String := Std.HashMap.emptyWithCapacity numNames.toNat
    let mut nameRev : Array String := Array.mkEmpty numNames.toNat
    for _ in [0:numNames.toNat] do
      let addrBytes ← _root_.Ixon.getBytes 32
      let some nmAddr := Ixon.Address.ofBytes? addrBytes | throw "§4 truncated name address"
      let tag ← _root_.Ixon.getU8
      let nm ← match tag with
        | 0 => pure ""
        | 1 =>
          let pBytes ← _root_.Ixon.getBytes 32
          let some pAddr := Ixon.Address.ofBytes? pBytes | throw "§4 truncated parent address"
          let len := (← _root_.Ixon.getTagN 0).value
          _root_.Ixon.checkCount len
          let sBytes ← _root_.Ixon.getBytes len.toNat
          let some s := String.fromUTF8? sBytes | throw "§4 invalid UTF-8 name"
          let parent := namesLookup.getD pAddr ""
          pure (if parent.isEmpty then s else s!"{parent}.{s}")
        | 2 =>
          let pBytes ← _root_.Ixon.getBytes 32
          let some pAddr := Ixon.Address.ofBytes? pBytes | throw "§4 truncated parent address"
          let len := (← _root_.Ixon.getTagN 0).value
          _root_.Ixon.checkCount len
          let nBytes ← _root_.Ixon.getBytes len.toNat
          let n := natFromBytesLE nBytes
          let parent := namesLookup.getD pAddr ""
          pure (if parent.isEmpty then toString n else s!"{parent}.{n}")
        | t => throw s!"§4 invalid name component tag {t}"
      nameRev := nameRev.push nm
      namesLookup := namesLookup.insert nmAddr nm
    let numNamed := (← _root_.Ixon.getTagN 0).value
    _root_.Ixon.checkCount numNamed 4
    let mut out : Std.HashMap String Ixon.Address := Std.HashMap.emptyWithCapacity numNamed.toNat
    for _ in [0:numNamed.toNat] do
      let nameIdx := (← _root_.Ixon.getTagN 0).value.toNat
      let constRank := (← _root_.Ixon.getTagN 0).value.toNat
      let _hint ← _root_.Ixon.getTagN 0
      let metaLen := (← _root_.Ixon.getTagN 0).value
      _root_.Ixon.checkCount metaLen
      skipBytes metaLen.toNat
      if let (some nm, some addr) := (nameRev[nameIdx]?, constOrder[constRank]?) then
        out := out.insert nm addr
    return out
  match parseMeta.run { bytes := env.metadata, idx := 0 } with
  | .ok m _ => .ok m
  | .error e _ => .error s!"closure metadata: {e}"

/-! ## Root specification parsing & resolution without `--equations` -/

/-- A parsed `--root` specification when no `--equations` sidecar is supplied. -/
inductive RootSpec where
  | byName (name : String)
  | byAddr (addr : Ixon.Address) (name? : Option String)
  deriving BEq, Repr, Inhabited

/-- Parse one `--root` argument:
* `<NAME>=<64-hex-addr>` → `byAddr addr (some NAME)`
* `<64-hex-addr>` → `byAddr addr none` (exports `cx_root<i>`)
* `<NAME>` → `byName NAME` (resolved against `.ixe` §4/§5 metadata) -/
def parseRootSpec (spec : String) : Except String RootSpec := do
  if spec.isEmpty then
    throw "empty --root specification"
  let parts := spec.splitOn "="
  match parts with
  | [single] =>
    if single.startsWith "0x" || single.startsWith "0X" then
      throw s!"invalid --root address '{single}': expected 64 hex digits without '0x' prefix"
    match Ixon.Address.fromString single with
    | some addr => pure (.byAddr addr none)
    | none => pure (.byName single)
  | [name, hex] =>
    if name.isEmpty then
      throw s!"invalid --root specification '{spec}': empty root name before '='"
    match Ixon.Address.fromString hex with
    | some addr => pure (.byAddr addr (some name))
    | none =>
      throw s!"invalid --root address in '{spec}': expected 64-character hex BLAKE3 address"
  | _ =>
    throw s!"invalid --root specification '{spec}': multiple '=' separators"

/-- Resolve `--root` specifications against `env` (without `--equations`).
* If `specs` is empty: defaults to `"entry"` when present in the `.ixe` name table, else
  `env.main` when set, else fails cleanly with guidance.
* For `--root <NAME>`: resolves against the `.ixe` §4/§5 name table, failing cleanly with a
  helpful message on anonymous `.ixe` files.
* For `--root <64-hex>` and `--root <NAME>=<64-hex>`: resolves directly against `env.consts`
  on both anonymous and named `.ixe` files.
* Validates that every resolved address exists in `env.consts` and no export name is repeated. -/
def resolveRoots (env : V3.Env) (specs : List String) :
    Except String (Array (Ixon.Address × Option String)) := do
  let parsed ← specs.mapM parseRootSpec
  let needNamed := parsed.isEmpty || parsed.any fun
    | .byName _ => true
    | .byAddr _ _ => false
  let namedMap ← if needNamed then extractNamedMap env else pure {}
  if parsed.isEmpty then
    if let some addr := namedMap["entry"]? then
      unless env.consts.contains addr do
        throw s!"default root 'entry' ({addr}) is not present in closure"
      return #[(addr, some "entry")]
    else if let some addr := env.main then
      unless env.consts.contains addr do
        throw s!"default main root ({addr}) is not present in closure"
      return #[(addr, some "main")]
    else if namedMap.isEmpty then
      throw "no --root given: anonymous .ixe has no name table or main \
        (pass --root <64-hex-addr> or --root <NAME>=<64-hex-addr>, or supply --equations)"
    else
      throw "no --root given and no 'entry' constant found in closure metadata \
        (pass --root <NAME> or --root <NAME>=<64-hex-addr>)"
  let mut out : Array (Ixon.Address × Option String) := Array.mkEmpty parsed.length
  let mut usedNames : Array String := Array.mkEmpty parsed.length
  for spec in parsed do
    let i := out.size
    let (addr, name?) ← match spec with
      | .byAddr addr name? =>
        unless env.consts.contains addr do
          throw s!"root address {addr} is not present in closure"
        pure (addr, name?)
      | .byName name =>
        if namedMap.isEmpty then
          throw s!"anonymous .ixe closure has no name table; cannot resolve '--root {name}' by name \
            (pass --root <64-hex-addr> or --root <NAME>=<64-hex-addr>)"
        match namedMap[name]? with
        | some addr =>
          unless env.consts.contains addr do
            throw s!"root '{name}' ({addr}) is not present in closure"
          pure (addr, some name)
        | none =>
          throw s!"no root named '{name}' in closure metadata \
            (pass a valid constant name or 64-hex address)"
    let effective := name?.getD s!"root{i}"
    if usedNames.contains effective then
      throw s!"root {effective} is named twice"
    usedNames := usedNames.push effective
    out := out.push (addr, name?)
  return out

/-- Attach diagnostic names from a named `.ixe` metadata table (when present) to proposals
that lack a name. No-op on anonymous `.ixe` files. -/
def attachNames (namedMap : Std.HashMap String Ixon.Address) (proposals : Array Proposal) :
    Array Proposal :=
  if namedMap.isEmpty then proposals
  else
    let rev : Std.HashMap Ixon.Address String :=
      namedMap.fold (init := Std.HashMap.emptyWithCapacity namedMap.size) fun m nm addr =>
        match m[addr]? with
        | some prev => if nm < prev then m.insert addr nm else m
        | none => m.insert addr nm
    proposals.map fun p =>
      if p.name?.isSome then p else { p with name? := rev[p.subject]? }

end IxCC.Src.AutoHints
