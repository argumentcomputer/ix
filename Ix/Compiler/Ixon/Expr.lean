import Ix.Compiler.Ixon.Serialize
import Ix.Compiler.Ixon.Uses

/-!
# Ixon expressions, v2

ix's alpha-invariant `Expr` with modes as first-class data on the
binder nodes: `lam` carries its binder `Uses`; `all` carries binder
`Uses` and result `Owned`. The Lean 4 fragment is `many` binders with
`shared` results (`Expr.leanFragment`).

Because the constructors are unified (no separate annotated variants),
v2 consumes **no new tags**: `Expr` flags stay `0x0`–`0xB`. (The tag
namespace is shared object-wide: `Const` uses `0xC` for mutual blocks
and `0xD` for constants, so `0xE`/`0xF` are the truly free flags —
candidates: borrow node, region node, modal-inductive block.) The
telescope encodings are ix's, with one mode byte per telescope binder:

- `lam`: `Tag4(LAM, n)`, then per binder `[uses:u8][type]`, then base —
  uses in the low 2 bits, values `0–3`.
- `all`: `Tag4(ALL, n)`, then per binder `[mode:u8][type]`, then base —
  `uses | owned <<< 2`, values `0–7`.

The v1→v2 reencoder is therefore mechanical: insert `0x03` (`many`)
per lam binder and `0x07` (`many`+`shared`) per all binder.

Decoding is strict beyond `Serialize`'s size canonicity: telescopes
must be nonempty and maximal (a decoded base may not repeat the
telescope's constructor), mode bytes must be in range, and `letE`'s
nonDep flag must be `0` or `1`. Writers use structurally terminating
spine helpers; the input-driven decoder is fueled by remaining bytes.
-/

namespace Ix.Compiler.Ixon

/-- Expression in the Ixon v2 format. Alpha-invariant: names are
stripped, presentation metadata lives in the metadata arena (as in ix).
`str`/`nat` reference the blob table; `ref`/`recur` reference the refs
table with universe-table instantiation indices; `share` references the
sharing table. -/
inductive Expr where
  | sort : UInt64 → Expr
  | var : UInt64 → Expr
  | ref : UInt64 → Array UInt64 → Expr
  | recur : UInt64 → Array UInt64 → Expr
  | prj : UInt64 → UInt64 → Expr → Expr
  | str : UInt64 → Expr
  | nat : UInt64 → Expr
  | app : Expr → Expr → Expr
  | lam : Uses → Expr → Expr → Expr
  | all : Uses → Owned → Expr → Expr → Expr
  | letE : Bool → Expr → Expr → Expr → Expr
  | share : UInt64 → Expr
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

namespace Expr

def FLAG_SORT : UInt8 := 0x0
def FLAG_VAR : UInt8 := 0x1
def FLAG_REF : UInt8 := 0x2
def FLAG_REC : UInt8 := 0x3
def FLAG_PRJ : UInt8 := 0x4
def FLAG_STR : UInt8 := 0x5
def FLAG_NAT : UInt8 := 0x6
def FLAG_APP : UInt8 := 0x7
def FLAG_LAM : UInt8 := 0x8
def FLAG_ALL : UInt8 := 0x9
def FLAG_LET : UInt8 := 0xA
def FLAG_SHARE : UInt8 := 0xB

/-- Collect a lambda telescope: binder (uses, type) list plus base. -/
def collectLam : Expr → List (Uses × Expr) × Expr
  | .lam u ty body =>
    let (bs, base) := collectLam body
    ((u, ty) :: bs, base)
  | e => ([], e)

/-- Collect an application spine (arguments in application order). -/
def collectApp : Expr → List Expr × Expr
  | .app f a =>
    let (args, base) := collectApp f
    (args ++ [a], base)
  | e => ([], e)

/-- The Lean 4 fragment: every binder `many`, every result `shared`. -/
def leanFragment : Expr → Bool
  | .lam .many d b => leanFragment d && leanFragment b
  | .lam .. => false
  | .all .many .shared d c => leanFragment d && leanFragment c
  | .all .. => false
  | .app f a => leanFragment f && leanFragment a
  | .prj _ _ e => leanFragment e
  | .letE _ t v b => leanFragment t && leanFragment v && leanFragment b
  | _ => true

/-- Expression-constructor count, used as the structural termination measure
for the mutually recursive canonical-spine writers. -/
def codecSize : Expr → Nat
  | .sort _ | .var _ | .ref _ _ | .recur _ _ | .str _ | .nat _ | .share _ => 1
  | .prj _ _ e => e.codecSize + 1
  | .app f a => f.codecSize + a.codecSize + 1
  | .lam _ d b | .all _ _ d b => d.codecSize + b.codecSize + 1
  | .letE _ t v b => t.codecSize + v.codecSize + b.codecSize + 1

def appCount : Expr → Nat
  | .app f _ => f.appCount + 1
  | _ => 0

def lamCount : Expr → Nat
  | .lam _ _ b => b.lamCount + 1
  | _ => 0

def allCount : Expr → Nat
  | .all _ _ _ b => b.allCount + 1
  | _ => 0

/-- Every structural count written through a `UInt64` is representable.

Lean arrays and inductive spines are mathematically unbounded even on a
64-bit runtime, so this is the exact domain on which encoder-to-decoder
roundtrip can hold for the v2 count fields. -/
def wireWF : Expr → Prop
  | .sort _ | .var _ | .str _ | .nat _ | .share _ => True
  | .ref _ idxs | .recur _ idxs => idxs.size < UInt64.size
  | .prj _ _ val => val.wireWF
  | .app fn arg =>
    fn.wireWF ∧ arg.wireWF ∧ fn.appCount + 1 < UInt64.size
  | .lam _ ty body =>
    ty.wireWF ∧ body.wireWF ∧ body.lamCount + 1 < UInt64.size
  | .all _ _ ty body =>
    ty.wireWF ∧ body.wireWF ∧ body.allCount + 1 < UInt64.size
  | .letE _ ty val body => ty.wireWF ∧ val.wireWF ∧ body.wireWF

end Expr

/-- Canonical concatenation of a universe-index list. -/
def tag0ListBytes : List UInt64 → ByteArray
  | [] => ByteArray.empty
  | idx :: idxs => tag0Bytes ⟨idx⟩ ++ tag0ListBytes idxs

/-- Canonical lambda mode byte. -/
def lamModeBytes (u : Uses) : ByteArray :=
  u8Bytes u.toBits

/-- Canonical forall mode byte. -/
def allModeByte (u : Uses) (o : Owned) : UInt8 :=
  u.toBits ||| (o.toBits <<< 2)

def allModeBytes (u : Uses) (o : Owned) : ByteArray :=
  u8Bytes (allModeByte u o)

mutual
  /-- Pure canonical expression encoder. Exposing bytes independently of the
  state writer makes exact-output and converse-reader proofs compositional. -/
  def exprBytes : Expr → ByteArray
    | .sort idx => tag4Bytes ⟨Expr.FLAG_SORT, idx⟩
    | .var idx => tag4Bytes ⟨Expr.FLAG_VAR, idx⟩
    | .ref refIdx univIdxs =>
      tag4Bytes ⟨Expr.FLAG_REF, univIdxs.size.toUInt64⟩ ++
        tag0Bytes ⟨refIdx⟩ ++ tag0ListBytes univIdxs.toList
    | .recur recIdx univIdxs =>
      tag4Bytes ⟨Expr.FLAG_REC, univIdxs.size.toUInt64⟩ ++
        tag0Bytes ⟨recIdx⟩ ++ tag0ListBytes univIdxs.toList
    | .prj typeRefIdx fieldIdx val =>
      tag4Bytes ⟨Expr.FLAG_PRJ, fieldIdx⟩ ++
        tag0Bytes ⟨typeRefIdx⟩ ++ exprBytes val
    | .str refIdx => tag4Bytes ⟨Expr.FLAG_STR, refIdx⟩
    | .nat refIdx => tag4Bytes ⟨Expr.FLAG_NAT, refIdx⟩
    | .app f a =>
      tag4Bytes ⟨Expr.FLAG_APP, (f.appCount + 1).toUInt64⟩ ++
        appSpineBytes f ++ exprBytes a
    | .lam u ty body =>
      tag4Bytes ⟨Expr.FLAG_LAM, (body.lamCount + 1).toUInt64⟩ ++
        lamModeBytes u ++ exprBytes ty ++ lamTailBytes body
    | .all u o ty body =>
      tag4Bytes ⟨Expr.FLAG_ALL, (body.allCount + 1).toUInt64⟩ ++
        allModeBytes u o ++ exprBytes ty ++ allTailBytes body
    | .letE nonDep ty val body =>
      tag4Bytes ⟨Expr.FLAG_LET, if nonDep then 1 else 0⟩ ++
        exprBytes ty ++ exprBytes val ++ exprBytes body
    | .share idx => tag4Bytes ⟨Expr.FLAG_SHARE, idx⟩
  termination_by e => (e.codecSize, 0)
  decreasing_by
    all_goals apply Prod.Lex.left <;> simp [Expr.codecSize] <;> omega

  /-- Application base followed by arguments in source order. -/
  def appSpineBytes : Expr → ByteArray
    | .app f a => appSpineBytes f ++ exprBytes a
    | base => exprBytes base
  termination_by e => (e.codecSize, 1)
  decreasing_by
    all_goals first
      | apply Prod.Lex.left <;> simp [Expr.codecSize] <;> omega
      | apply Prod.Lex.right <;> omega

  /-- Remaining lambda binders followed by the non-lambda body. -/
  def lamTailBytes : Expr → ByteArray
    | .lam u ty body =>
      lamModeBytes u ++ exprBytes ty ++ lamTailBytes body
    | base => exprBytes base
  termination_by e => (e.codecSize, 1)
  decreasing_by
    all_goals first
      | apply Prod.Lex.left <;> simp [Expr.codecSize] <;> omega
      | apply Prod.Lex.right <;> omega

  /-- Remaining forall binders followed by the non-forall codomain. -/
  def allTailBytes : Expr → ByteArray
    | .all u o ty body =>
      allModeBytes u o ++ exprBytes ty ++ allTailBytes body
    | base => exprBytes base
  termination_by e => (e.codecSize, 1)
  decreasing_by
    all_goals first
      | apply Prod.Lex.left <;> simp [Expr.codecSize] <;> omega
      | apply Prod.Lex.right <;> omega
end

/-- Total expression writer over the pure canonical encoder. -/
def putExpr (e : Expr) : PutM Unit := putBytes (exprBytes e)

theorem putExpr_spec (e : Expr) : PutSpec (putExpr e) (exprBytes e) :=
  putBytes_spec _

def getTag0List : Nat → GetM (List UInt64)
  | 0 => pure []
  | count + 1 => do
    let idx := (← getTag0).size
    return idx :: (← getTag0List count)

def getLamMode : GetM Uses := do
  let mb ← getU8
  match Uses.ofBits? mb with
  | none => throw s!"getExpr: invalid lam mode byte {mb}"
  | some u => return u

def getAllMode : GetM (Uses × Owned) := do
  let mb ← getU8
  if mb >= 8 then throw s!"getExpr: invalid all mode byte {mb}"
  match Uses.ofBits? (mb &&& 0x3), Owned.ofBits? (mb >>> 2) with
  | some u, some o => return (u, o)
  | _, _ => throw s!"getExpr: invalid all mode byte {mb}"

/-- Parse `extra + 1` flattened application arguments. The base check occurs
at the unique innermost step. -/
def getAppRunSucc (recur : GetM Expr) : Nat → GetM Expr
  | 0 => do
    let base ← recur
    match base with
    | .app .. => throw "getExpr: non-canonical app base"
    | _ =>
      let arg ← recur
      return .app base arg
  | extra + 1 => do
    let fn ← getAppRunSucc recur extra
    let arg ← recur
    return .app fn arg

def getAppRun (recur : GetM Expr) : Nat → GetM Expr
  | 0 => throw "getExpr: empty app spine"
  | count + 1 => getAppRunSucc recur count

/-- Parse `extra + 1` flattened lambda binders, checking the body only at the
unique innermost step. -/
def getLamRunSucc (recur : GetM Expr) : Nat → GetM Expr
  | 0 => do
    let u ← getLamMode
    let ty ← recur
    let body ← recur
    match body with
    | .lam .. => throw "getExpr: non-canonical lam telescope"
    | _ => return .lam u ty body
  | extra + 1 => do
    let u ← getLamMode
    let ty ← recur
    return .lam u ty (← getLamRunSucc recur extra)

def getLamRun (recur : GetM Expr) : Nat → GetM Expr
  | 0 => throw "getExpr: empty lam telescope"
  | count + 1 => getLamRunSucc recur count

/-- Parse `extra + 1` flattened forall binders, checking the codomain only at
the unique innermost step. -/
def getAllRunSucc (recur : GetM Expr) : Nat → GetM Expr
  | 0 => do
    let (u, o) ← getAllMode
    let ty ← recur
    let body ← recur
    match body with
    | .all .. => throw "getExpr: non-canonical all telescope"
    | _ => return .all u o ty body
  | extra + 1 => do
    let (u, o) ← getAllMode
    let ty ← recur
    return .all u o ty (← getAllRunSucc recur extra)

def getAllRun (recur : GetM Expr) : Nat → GetM Expr
  | 0 => throw "getExpr: empty all telescope"
  | count + 1 => getAllRunSucc recur count

/-- Interpret one already-decoded expression header. -/
def getExprTag (recur : GetM Expr) (tag : Tag4) : GetM Expr := do
  match tag.flag with
  | 0x0 => return .sort tag.size
  | 0x1 => return .var tag.size
  | 0x2 => do
    let refIdx := (← getTag0).size
    return .ref refIdx (← getTag0List tag.size.toNat).toArray
  | 0x3 => do
    let recIdx := (← getTag0).size
    return .recur recIdx (← getTag0List tag.size.toNat).toArray
  | 0x4 => do
    let typeRefIdx := (← getTag0).size
    return .prj typeRefIdx tag.size (← recur)
  | 0x5 => return .str tag.size
  | 0x6 => return .nat tag.size
  | 0x7 => getAppRun recur tag.size.toNat
  | 0x8 => getLamRun recur tag.size.toNat
  | 0x9 => getAllRun recur tag.size.toNat
  | 0xA => do
    if tag.size > 1 then throw s!"getExpr: invalid letE nonDep {tag.size}"
    let nonDep := tag.size == 1
    let ty ← recur
    let val ← recur
    return .letE nonDep ty val (← recur)
  | 0xB => return .share tag.size
  | f => throw s!"getExpr: invalid flag {f}"

def getExprFuel : Nat → GetM Expr
  | 0 => throw "getExpr: recursion limit"
  | fuel + 1 => do
    let tag ← getTag4
    getExprTag (getExprFuel fuel) tag

def getExpr : GetM Expr := do
  let st ← get
  getExprFuel (st.bytes.size - st.idx + 1)

instance : Serialize Expr where
  put := putExpr
  get := getExpr

namespace ExprLaws

attribute [local simp] tag0ListBytes

theorem GetSpec.map {get : GetM α} {input : ByteArray} {value : α}
    (h : GetSpec get input value) (f : α → β) :
    GetSpec (f <$> get) input (f value) := by
  let finish : α → GetM β := fun decoded => pure (f decoded)
  have hfinish : GetSpec (finish value) ByteArray.empty (f value) :=
    GetSpec.pure _
  have htotal := GetSpec.bind (next := finish) h hfinish
  simpa [finish] using htotal

theorem GetCanonical.bind_inv {get : GetM α} {next : α → GetM β}
    {encode : α → ByteArray} (hget : GetCanonical get encode)
    (pre rest : ByteArray) {result : β} {st' : GetState}
    (h : (get >>= next).run ⟨pre ++ rest, pre.size⟩ = .ok (result, st')) :
    ∃ value after,
      rest = encode value ++ after ∧
      (next value).run
        ⟨(pre ++ encode value) ++ after, (pre ++ encode value).size⟩ =
          .ok (result, st') := by
  simp only [StateT.run_bind] at h
  cases hg : get.run ⟨pre ++ rest, pre.size⟩ with
  | error err =>
    rw [hg] at h
    contradiction
  | ok valueState =>
    rcases valueState with ⟨value, afterValue⟩
    rw [hg] at h
    simp only [bind, Except.bind] at h
    obtain ⟨after, hrest, hstate⟩ := hget pre rest hg
    refine ⟨value, after, hrest, ?_⟩
    rw [hstate] at h
    simpa [hrest, ByteArray.append_assoc,
      ByteArray.size_append] using h

theorem getTag0List_spec (idxs : List UInt64) :
    GetSpec (getTag0List idxs.length) (tag0ListBytes idxs) idxs := by
  induction idxs with
  | nil => exact GetSpec.pure []
  | cons idx idxs ih =>
    intro pre suffix
    simp only [List.length_cons, getTag0List, StateT.run_bind]
    have hbytes :
        pre ++ tag0ListBytes (idx :: idxs) ++ suffix =
          pre ++ tag0Bytes ⟨idx⟩ ++ (tag0ListBytes idxs ++ suffix) := by
      simp [tag0ListBytes, ByteArray.append_assoc]
    rw [hbytes]
    rw [getTag0_encoded_spec ⟨idx⟩ pre (tag0ListBytes idxs ++ suffix)]
    simp only [bind, Except.bind]
    have htail := ih (pre ++ tag0Bytes ⟨idx⟩) suffix
    have htail' :
        (getTag0List idxs.length).run
            ⟨pre ++ tag0Bytes ⟨idx⟩ ++ (tag0ListBytes idxs ++ suffix),
              pre.size + (tag0Bytes ⟨idx⟩).size⟩ =
          .ok (idxs,
            ⟨pre ++ tag0Bytes ⟨idx⟩ ++ (tag0ListBytes idxs ++ suffix),
              pre.size + (tag0Bytes ⟨idx⟩).size +
                (tag0ListBytes idxs).size⟩) := by
      simpa [ByteArray.append_assoc, ByteArray.size_append,
        Nat.add_assoc] using htail
    rw [htail']
    simp [tag0ListBytes, ByteArray.size_append, Nat.add_assoc]
    rfl

theorem getTag0List_canonical (count : Nat) :
    GetCanonical (getTag0List count) tag0ListBytes := by
  induction count with
  | zero =>
    intro pre rest value st' h
    simp [getTag0List] at h
    cases h
    exact ⟨rest, by simp [tag0ListBytes], by simp [tag0ListBytes]⟩
  | succ count ih =>
    intro pre rest value st' h
    simp only [getTag0List, StateT.run_bind] at h
    cases hh : getTag0.run ⟨pre ++ rest, pre.size⟩ with
    | error err =>
      rw [hh] at h
      contradiction
    | ok result =>
      rcases result with ⟨tag, afterHead⟩
      rw [hh] at h
      simp only [bind, Except.bind] at h
      obtain ⟨afterHeadBytes, hrestHead, hafterHead⟩ :=
        getTag0_canonical pre rest hh
      let headPre := pre ++ tag0Bytes tag
      have hafterHead' :
          afterHead = ⟨headPre ++ afterHeadBytes, headPre.size⟩ := by
        rw [hafterHead]
        simp [headPre, hrestHead, ByteArray.append_assoc]
      rw [hafterHead'] at h
      cases ht : (getTag0List count).run
          ⟨headPre ++ afterHeadBytes, headPre.size⟩ with
      | error err =>
        rw [ht] at h
        contradiction
      | ok tailResult =>
        rcases tailResult with ⟨tail, afterTail⟩
        rw [ht] at h
        simp at h
        cases h
        obtain ⟨suffix, hrestTail, hafterTail⟩ :=
          ih headPre afterHeadBytes ht
        refine ⟨suffix, ?_, ?_⟩
        · rw [hrestHead, hrestTail]
          simp [tag0ListBytes, ByteArray.append_assoc]
        · simpa [headPre, hrestHead, hrestTail, tag0ListBytes,
            ByteArray.append_assoc, ByteArray.size_append,
            Nat.add_assoc] using hafterTail

theorem getTag0List_success_length (count : Nat) :
    ∀ (initial : GetState) {idxs : List UInt64} {st' : GetState},
      (getTag0List count).run initial = .ok (idxs, st') →
      idxs.length = count := by
  induction count with
  | zero =>
    intro initial idxs st' h
    simp [getTag0List] at h
    cases h
    rfl
  | succ count ih =>
    intro initial idxs st' h
    simp only [getTag0List, StateT.run_bind] at h
    cases hh : getTag0.run initial with
    | error err => rw [hh] at h; contradiction
    | ok headState =>
      rcases headState with ⟨head, afterHead⟩
      rw [hh] at h
      simp only [bind, Except.bind] at h
      cases ht : (getTag0List count).run afterHead with
      | error err => rw [ht] at h; contradiction
      | ok tailState =>
        rcases tailState with ⟨tail, afterTail⟩
        rw [ht] at h
        simp at h
        cases h
        simp [ih afterHead ht]

theorem uses_byte_eq_of_decode {mb : UInt8} {u : Uses}
    (h : Uses.ofBits? mb = some u) : mb = u.toBits := by
  cases u <;> simp only [Uses.ofBits?] at h
  all_goals split at h <;> simp_all [Uses.toBits]

theorem owned_byte_eq_of_decode {mb : UInt8} {o : Owned}
    (h : Owned.ofBits? mb = some o) : mb = o.toBits := by
  cases o <;> simp only [Owned.ofBits?] at h
  all_goals split at h <;> simp_all [Owned.toBits]

private theorem u8_split_low2 (byte : UInt8) :
    ((byte >>> 2) <<< 2) ||| (byte &&& 0x3) = byte := by
  apply UInt8.toBitVec_inj.1
  ext i hi
  simp only [UInt8.toBitVec_or, UInt8.toBitVec_and,
    UInt8.toBitVec_shiftLeft, UInt8.toBitVec_shiftRight,
    BitVec.getElem_or, BitVec.getElem_and, UInt8.toBitVec_ofNat]
  have hiCases :
      i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
    omega
  rcases hiCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

theorem getLamMode_spec (u : Uses) :
    GetSpec getLamMode (lamModeBytes u) u := by
  intro pre suffix
  simp only [getLamMode, lamModeBytes, StateT.run_bind]
  rw [getU8_spec u.toBits pre suffix]
  simp only [bind, Except.bind]
  rw [Uses.ofBits?_toBits]
  rfl

theorem allModeByte_lt_eight (u : Uses) (o : Owned) :
    allModeByte u o < 8 := by
  cases u <;> cases o <;> decide

theorem getAllMode_spec (u : Uses) (o : Owned) :
    GetSpec getAllMode (allModeBytes u o) (u, o) := by
  intro pre suffix
  simp only [getAllMode, allModeBytes, StateT.run_bind]
  rw [getU8_spec (allModeByte u o) pre suffix]
  simp only [bind, Except.bind]
  have hnot : ¬allModeByte u o >= 8 := by
    cases u <;> cases o <;> decide
  simp only [hnot, if_false]
  cases u <;> cases o <;> simp [allModeByte, Uses.ofBits?, Owned.ofBits?]
  all_goals rfl

theorem getLamMode_canonical : GetCanonical getLamMode lamModeBytes := by
  intro pre rest u st' h
  simp only [getLamMode, StateT.run_bind] at h
  cases hb : getU8.run ⟨pre ++ rest, pre.size⟩ with
  | error err =>
    rw [hb] at h
    contradiction
  | ok result =>
    rcases result with ⟨mb, afterByte⟩
    rw [hb] at h
    simp only [bind, Except.bind] at h
    cases hm : Uses.ofBits? mb with
    | none =>
      simp [hm] at h
      change (Except.error _) = Except.ok (u, st') at h
      contradiction
    | some decoded =>
      simp [hm] at h
      cases h
      obtain ⟨suffix, hrest, hstate⟩ := getU8_canonical pre rest hb
      have hmb := uses_byte_eq_of_decode hm
      subst mb
      exact ⟨suffix, by simpa [lamModeBytes] using hrest,
        by simpa [lamModeBytes] using hstate⟩

theorem all_mode_byte_eq_of_decode {mb : UInt8} {u : Uses} {o : Owned}
    (_hlt : mb < 8)
    (hu : Uses.ofBits? (mb &&& 0x3) = some u)
    (ho : Owned.ofBits? (mb >>> 2) = some o) :
    mb = allModeByte u o := by
  have hu' := uses_byte_eq_of_decode hu
  have ho' := owned_byte_eq_of_decode ho
  change mb = u.toBits ||| (o.toBits <<< 2)
  rw [← hu', ← ho']
  exact (u8_split_low2 mb).symm.trans (UInt8.or_comm _ _)

theorem getAllMode_canonical :
    GetCanonical getAllMode (fun mode => allModeBytes mode.1 mode.2) := by
  intro pre rest mode st' h
  simp only [getAllMode, StateT.run_bind] at h
  cases hb : getU8.run ⟨pre ++ rest, pre.size⟩ with
  | error err =>
    rw [hb] at h
    contradiction
  | ok result =>
    rcases result with ⟨mb, afterByte⟩
    rw [hb] at h
    simp only [bind, Except.bind] at h
    by_cases hbad : mb >= 8
    · simp [hbad] at h
      change (Except.error _) = Except.ok (mode, st') at h
      contradiction
    · simp only [hbad, if_false] at h
      cases hu : Uses.ofBits? (mb &&& 0x3) with
      | none =>
        simp [hu] at h
        change (Except.error _) = Except.ok (mode, st') at h
        contradiction
      | some u =>
        cases ho : Owned.ofBits? (mb >>> 2) with
        | none =>
          simp [hu, ho] at h
          change (Except.error _) = Except.ok (mode, st') at h
          contradiction
        | some o =>
          simp [hu, ho] at h
          cases h
          obtain ⟨suffix, hrest, hstate⟩ := getU8_canonical pre rest hb
          have hlt : mb < 8 := by
            rw [UInt8.lt_iff_toNat_lt]
            change mb.toNat < 8
            have hbad' : ¬(8 : UInt8) ≤ mb := hbad
            rw [UInt8.le_iff_toNat_le] at hbad'
            change ¬8 ≤ mb.toNat at hbad'
            omega
          have hmb := all_mode_byte_eq_of_decode hlt hu ho
          subst mb
          exact ⟨suffix, by simpa [allModeBytes] using hrest,
            by simpa [allModeBytes] using hstate⟩

def AppBase : Expr → Prop
  | .app .. => False
  | _ => True

def LamBase : Expr → Prop
  | .lam .. => False
  | _ => True

def AllBase : Expr → Prop
  | .all .. => False
  | _ => True

theorem getAppRunSucc_zero_of_specs (recur : GetM Expr)
    (base arg : Expr) (hbase : AppBase base)
    (hbaseSpec : GetSpec recur (exprBytes base) base)
    (hargSpec : GetSpec recur (exprBytes arg) arg) :
    GetSpec (getAppRunSucc recur 0)
      (exprBytes base ++ exprBytes arg) (.app base arg) := by
  let finish : Expr → Expr → GetM Expr := fun decodedBase decodedArg =>
    pure (.app decodedBase decodedArg)
  have hfinish : GetSpec (finish base arg) ByteArray.empty (.app base arg) := by
    exact GetSpec.pure _
  have harg := GetSpec.bind (next := finish base) hargSpec hfinish
  simp only [ByteArray.append_empty] at harg
  let afterBase : Expr → GetM Expr := fun decoded =>
    match decoded with
    | .app .. => throw "getExpr: non-canonical app base"
    | _ => recur >>= finish decoded
  have hafter : GetSpec (afterBase base) (exprBytes arg) (.app base arg) := by
    cases base <;> simp_all [AppBase, afterBase, finish]
  have htotal := GetSpec.bind (next := afterBase) hbaseSpec hafter
  have hrun : getAppRunSucc recur 0 = recur >>= afterBase := by
    funext st
    simp [getAppRunSucc, afterBase, finish]
  rw [hrun]
  exact htotal

theorem getAppRunSucc_step_of_specs (recur : GetM Expr)
    (fn arg : Expr) (count : Nat)
    (hfn : GetSpec (getAppRunSucc recur count)
      (appSpineBytes fn) fn)
    (harg : GetSpec recur (exprBytes arg) arg) :
    GetSpec (getAppRunSucc recur (count + 1))
      (appSpineBytes fn ++ exprBytes arg) (.app fn arg) := by
  let finish : Expr → Expr → GetM Expr := fun decodedFn decodedArg =>
    pure (.app decodedFn decodedArg)
  have hfinish : GetSpec (finish fn arg) ByteArray.empty (.app fn arg) :=
    GetSpec.pure _
  have hright := GetSpec.bind (next := finish fn) harg hfinish
  simp only [ByteArray.append_empty] at hright
  let afterFn : Expr → GetM Expr := fun decodedFn =>
    recur >>= finish decodedFn
  have hafter : GetSpec (afterFn fn) (exprBytes arg) (.app fn arg) := by
    simpa [afterFn, finish] using hright
  have htotal := GetSpec.bind (next := afterFn) hfn hafter
  simpa [getAppRunSucc, afterFn, finish] using htotal

theorem getLamRunSucc_zero_of_specs (recur : GetM Expr)
    (u : Uses) (ty body : Expr) (hbody : LamBase body)
    (hty : GetSpec recur (exprBytes ty) ty)
    (hbodySpec : GetSpec recur (exprBytes body) body) :
    GetSpec (getLamRunSucc recur 0)
      (lamModeBytes u ++ exprBytes ty ++ exprBytes body)
      (.lam u ty body) := by
  let finish : Uses → Expr → Expr → GetM Expr :=
      fun decodedU decodedTy decodedBody =>
    match decodedBody with
    | .lam .. => throw "getExpr: non-canonical lam telescope"
    | _ => pure (.lam decodedU decodedTy decodedBody)
  have hfinish :
      GetSpec (finish u ty body) ByteArray.empty (.lam u ty body) := by
    cases body <;> simp_all [LamBase, finish] <;> exact GetSpec.pure _
  have hbody' := GetSpec.bind (next := finish u ty) hbodySpec hfinish
  simp only [ByteArray.append_empty] at hbody'
  let afterTy : Uses → Expr → GetM Expr := fun decodedU decodedTy =>
    recur >>= finish decodedU decodedTy
  have hafterTy :
      GetSpec (afterTy u ty) (exprBytes body) (.lam u ty body) := by
    simpa [afterTy, finish] using hbody'
  have hchildren := GetSpec.bind (next := afterTy u) hty hafterTy
  let afterMode : Uses → GetM Expr := fun decodedU =>
    recur >>= afterTy decodedU
  have hafterMode :
      GetSpec (afterMode u) (exprBytes ty ++ exprBytes body)
        (.lam u ty body) := by
    simpa [afterMode, afterTy] using hchildren
  have htotal := GetSpec.bind (next := afterMode) (getLamMode_spec u) hafterMode
  have hrun : getLamRunSucc recur 0 = getLamMode >>= afterMode := by
    funext st
    simp [getLamRunSucc, afterMode, afterTy, finish]
  rw [hrun]
  simpa [ByteArray.append_assoc] using htotal

theorem getLamRunSucc_step_of_specs (recur : GetM Expr)
    (u : Uses) (ty body : Expr) (count : Nat)
    (hty : GetSpec recur (exprBytes ty) ty)
    (htail : GetSpec (getLamRunSucc recur count)
      (lamTailBytes body) body) :
    GetSpec (getLamRunSucc recur (count + 1))
      (lamModeBytes u ++ exprBytes ty ++ lamTailBytes body)
      (.lam u ty body) := by
  let finish : Uses → Expr → Expr → GetM Expr :=
      fun decodedU decodedTy decodedBody =>
    pure (.lam decodedU decodedTy decodedBody)
  have hfinish :
      GetSpec (finish u ty body) ByteArray.empty (.lam u ty body) :=
    GetSpec.pure _
  have htail' := GetSpec.bind (next := finish u ty) htail hfinish
  simp only [ByteArray.append_empty] at htail'
  let afterTy : Uses → Expr → GetM Expr := fun decodedU decodedTy =>
    getLamRunSucc recur count >>= finish decodedU decodedTy
  have hafterTy :
      GetSpec (afterTy u ty) (lamTailBytes body) (.lam u ty body) := by
    simpa [afterTy, finish] using htail'
  have hchildren := GetSpec.bind (next := afterTy u) hty hafterTy
  let afterMode : Uses → GetM Expr := fun decodedU =>
    recur >>= afterTy decodedU
  have hafterMode :
      GetSpec (afterMode u) (exprBytes ty ++ lamTailBytes body)
        (.lam u ty body) := by
    simpa [afterMode, afterTy] using hchildren
  have htotal := GetSpec.bind (next := afterMode) (getLamMode_spec u) hafterMode
  simpa [getLamRunSucc, afterMode, afterTy, finish,
    ByteArray.append_assoc] using htotal

theorem getAllRunSucc_zero_of_specs (recur : GetM Expr)
    (u : Uses) (o : Owned) (ty body : Expr) (hbody : AllBase body)
    (hty : GetSpec recur (exprBytes ty) ty)
    (hbodySpec : GetSpec recur (exprBytes body) body) :
    GetSpec (getAllRunSucc recur 0)
      (allModeBytes u o ++ exprBytes ty ++ exprBytes body)
      (.all u o ty body) := by
  let finish : Uses × Owned → Expr → Expr → GetM Expr :=
      fun decodedMode decodedTy decodedBody =>
    match decodedBody with
    | .all .. => throw "getExpr: non-canonical all telescope"
    | _ => pure (.all decodedMode.1 decodedMode.2 decodedTy decodedBody)
  have hfinish :
      GetSpec (finish (u, o) ty body) ByteArray.empty (.all u o ty body) := by
    cases body <;> simp_all [AllBase, finish] <;> exact GetSpec.pure _
  have hbody' := GetSpec.bind (next := finish (u, o) ty) hbodySpec hfinish
  simp only [ByteArray.append_empty] at hbody'
  let afterTy : Uses × Owned → Expr → GetM Expr :=
      fun decodedMode decodedTy => recur >>= finish decodedMode decodedTy
  have hafterTy :
      GetSpec (afterTy (u, o) ty) (exprBytes body) (.all u o ty body) := by
    simpa [afterTy, finish] using hbody'
  have hchildren := GetSpec.bind (next := afterTy (u, o)) hty hafterTy
  let afterMode : Uses × Owned → GetM Expr := fun decodedMode =>
    recur >>= afterTy decodedMode
  have hafterMode :
      GetSpec (afterMode (u, o)) (exprBytes ty ++ exprBytes body)
        (.all u o ty body) := by
    simpa [afterMode, afterTy] using hchildren
  have htotal := GetSpec.bind (next := afterMode) (getAllMode_spec u o) hafterMode
  have hrun : getAllRunSucc recur 0 = getAllMode >>= afterMode := by
    funext st
    simp [getAllRunSucc, afterMode, afterTy, finish]
  rw [hrun]
  simpa [ByteArray.append_assoc] using htotal

theorem getAllRunSucc_step_of_specs (recur : GetM Expr)
    (u : Uses) (o : Owned) (ty body : Expr) (count : Nat)
    (hty : GetSpec recur (exprBytes ty) ty)
    (htail : GetSpec (getAllRunSucc recur count)
      (allTailBytes body) body) :
    GetSpec (getAllRunSucc recur (count + 1))
      (allModeBytes u o ++ exprBytes ty ++ allTailBytes body)
      (.all u o ty body) := by
  let finish : Uses × Owned → Expr → Expr → GetM Expr :=
      fun decodedMode decodedTy decodedBody =>
    pure (.all decodedMode.1 decodedMode.2 decodedTy decodedBody)
  have hfinish :
      GetSpec (finish (u, o) ty body) ByteArray.empty (.all u o ty body) :=
    GetSpec.pure _
  have htail' := GetSpec.bind (next := finish (u, o) ty) htail hfinish
  simp only [ByteArray.append_empty] at htail'
  let afterTy : Uses × Owned → Expr → GetM Expr :=
      fun decodedMode decodedTy =>
    getAllRunSucc recur count >>= finish decodedMode decodedTy
  have hafterTy :
      GetSpec (afterTy (u, o) ty) (allTailBytes body) (.all u o ty body) := by
    simpa [afterTy, finish] using htail'
  have hchildren := GetSpec.bind (next := afterTy (u, o)) hty hafterTy
  let afterMode : Uses × Owned → GetM Expr := fun decodedMode =>
    recur >>= afterTy decodedMode
  have hafterMode :
      GetSpec (afterMode (u, o)) (exprBytes ty ++ allTailBytes body)
        (.all u o ty body) := by
    simpa [afterMode, afterTy] using hchildren
  have htotal := GetSpec.bind (next := afterMode) (getAllMode_spec u o) hafterMode
  simpa [getAllRunSucc, afterMode, afterTy, finish,
    ByteArray.append_assoc] using htotal

theorem tag4Bytes_size_pos (t : Tag4) : 0 < (tag4Bytes t).size := by
  simp only [tag4Bytes]
  split
  · simp [u8Bytes]
  · simp [u8Bytes, ByteArray.size_append]
    omega

theorem exprBytes_size_pos (e : Expr) : 0 < (exprBytes e).size := by
  cases e with
  | sort idx =>
    simpa only [exprBytes] using
      tag4Bytes_size_pos ⟨Expr.FLAG_SORT, idx⟩
  | var idx =>
    simpa only [exprBytes] using
      tag4Bytes_size_pos ⟨Expr.FLAG_VAR, idx⟩
  | ref refIdx idxs =>
    simp only [exprBytes, ByteArray.size_append]
    have h := tag4Bytes_size_pos
      ⟨Expr.FLAG_REF, idxs.size.toUInt64⟩
    omega
  | recur recIdx idxs =>
    simp only [exprBytes, ByteArray.size_append]
    have h := tag4Bytes_size_pos
      ⟨Expr.FLAG_REC, idxs.size.toUInt64⟩
    omega
  | prj typeRefIdx fieldIdx val =>
    simp only [exprBytes, ByteArray.size_append]
    have h := tag4Bytes_size_pos ⟨Expr.FLAG_PRJ, fieldIdx⟩
    omega
  | str idx =>
    simpa only [exprBytes] using
      tag4Bytes_size_pos ⟨Expr.FLAG_STR, idx⟩
  | nat idx =>
    simpa only [exprBytes] using
      tag4Bytes_size_pos ⟨Expr.FLAG_NAT, idx⟩
  | app fn arg =>
    simp only [exprBytes, ByteArray.size_append]
    have h := tag4Bytes_size_pos
      ⟨Expr.FLAG_APP, (fn.appCount + 1).toUInt64⟩
    omega
  | lam u ty body =>
    simp only [exprBytes, ByteArray.size_append]
    have h := tag4Bytes_size_pos
      ⟨Expr.FLAG_LAM, (body.lamCount + 1).toUInt64⟩
    omega
  | all u o ty body =>
    simp only [exprBytes, ByteArray.size_append]
    have h := tag4Bytes_size_pos
      ⟨Expr.FLAG_ALL, (body.allCount + 1).toUInt64⟩
    omega
  | letE nonDep ty val body =>
    simp only [exprBytes, ByteArray.size_append]
    have h := tag4Bytes_size_pos
      ⟨Expr.FLAG_LET, if nonDep then 1 else 0⟩
    omega
  | share idx =>
    simpa only [exprBytes] using
      tag4Bytes_size_pos ⟨Expr.FLAG_SHARE, idx⟩

theorem getExprHeader_of_spec (recur : GetM Expr) (tag : Tag4)
    (hflag : tag.flag < 16) {payload : ByteArray} {value : Expr}
    (hpayload : GetSpec (getExprTag recur tag) payload value) :
    GetSpec (do
      let decodedTag ← getTag4
      getExprTag recur decodedTag)
      (tag4Bytes tag ++ payload) value := by
  exact GetSpec.bind (next := getExprTag recur)
    (getTag4_encoded_spec tag hflag) hpayload

theorem getExprTag_ref_spec (recur : GetM Expr)
    (refIdx : UInt64) (idxs : List UInt64)
    (hcount : idxs.length < UInt64.size) :
    GetSpec
      (getExprTag recur ⟨Expr.FLAG_REF, idxs.length.toUInt64⟩)
      (tag0Bytes ⟨refIdx⟩ ++ tag0ListBytes idxs)
      (.ref refIdx idxs.toArray) := by
  let finish : List UInt64 → GetM Expr := fun decoded =>
    pure (.ref refIdx decoded.toArray)
  have hfinish :
      GetSpec (finish idxs) ByteArray.empty (.ref refIdx idxs.toArray) :=
    GetSpec.pure _
  have htail := GetSpec.bind (next := finish) (getTag0List_spec idxs) hfinish
  simp only [ByteArray.append_empty] at htail
  let afterRef : Tag0 → GetM Expr := fun decoded =>
    getTag0List idxs.length >>= fun values =>
      pure (.ref decoded.size values.toArray)
  have hafter :
      GetSpec (afterRef ⟨refIdx⟩) (tag0ListBytes idxs)
        (.ref refIdx idxs.toArray) := by
    simpa [afterRef, finish] using htail
  have htotal := GetSpec.bind (next := afterRef)
    (getTag0_encoded_spec ⟨refIdx⟩) hafter
  have hround : idxs.length.toUInt64.toNat = idxs.length :=
    UInt64.toNat_ofNat_of_lt hcount
  simpa [getExprTag, Expr.FLAG_REF, hround, afterRef,
    ByteArray.append_assoc] using htotal

theorem getExprTag_recur_spec (recur : GetM Expr)
    (recIdx : UInt64) (idxs : List UInt64)
    (hcount : idxs.length < UInt64.size) :
    GetSpec
      (getExprTag recur ⟨Expr.FLAG_REC, idxs.length.toUInt64⟩)
      (tag0Bytes ⟨recIdx⟩ ++ tag0ListBytes idxs)
      (.recur recIdx idxs.toArray) := by
  let finish : List UInt64 → GetM Expr := fun decoded =>
    pure (.recur recIdx decoded.toArray)
  have hfinish :
      GetSpec (finish idxs) ByteArray.empty (.recur recIdx idxs.toArray) :=
    GetSpec.pure _
  have htail := GetSpec.bind (next := finish) (getTag0List_spec idxs) hfinish
  simp only [ByteArray.append_empty] at htail
  let afterRef : Tag0 → GetM Expr := fun decoded =>
    getTag0List idxs.length >>= fun values =>
      pure (.recur decoded.size values.toArray)
  have hafter :
      GetSpec (afterRef ⟨recIdx⟩) (tag0ListBytes idxs)
        (.recur recIdx idxs.toArray) := by
    simpa [afterRef, finish] using htail
  have htotal := GetSpec.bind (next := afterRef)
    (getTag0_encoded_spec ⟨recIdx⟩) hafter
  have hround : idxs.length.toUInt64.toNat = idxs.length :=
    UInt64.toNat_ofNat_of_lt hcount
  simpa [getExprTag, Expr.FLAG_REC, hround, afterRef,
    ByteArray.append_assoc] using htotal

theorem getExprTag_prj_spec (recur : GetM Expr)
    (typeRefIdx fieldIdx : UInt64) (val : Expr)
    (hval : GetSpec recur (exprBytes val) val) :
    GetSpec (getExprTag recur ⟨Expr.FLAG_PRJ, fieldIdx⟩)
      (tag0Bytes ⟨typeRefIdx⟩ ++ exprBytes val)
      (.prj typeRefIdx fieldIdx val) := by
  let finish : UInt64 → Expr → GetM Expr :=
    fun decodedRef decodedVal => pure (.prj decodedRef fieldIdx decodedVal)
  have hfinish :
      GetSpec (finish typeRefIdx val) ByteArray.empty
        (.prj typeRefIdx fieldIdx val) := GetSpec.pure _
  have hval' := GetSpec.bind (next := finish typeRefIdx) hval hfinish
  simp only [ByteArray.append_empty] at hval'
  let afterRef : Tag0 → GetM Expr := fun decoded =>
    recur >>= finish decoded.size
  have hafter : GetSpec (afterRef ⟨typeRefIdx⟩) (exprBytes val)
      (.prj typeRefIdx fieldIdx val) := by
    simpa [afterRef, finish] using hval'
  have htotal := GetSpec.bind (next := afterRef)
    (getTag0_encoded_spec ⟨typeRefIdx⟩) hafter
  simpa [getExprTag, Expr.FLAG_PRJ, afterRef, finish] using htotal

theorem getExprTag_let_spec (recur : GetM Expr)
    (nonDep : Bool) (ty val body : Expr)
    (hty : GetSpec recur (exprBytes ty) ty)
    (hval : GetSpec recur (exprBytes val) val)
    (hbody : GetSpec recur (exprBytes body) body) :
    GetSpec
      (getExprTag recur ⟨Expr.FLAG_LET, if nonDep then 1 else 0⟩)
      (exprBytes ty ++ exprBytes val ++ exprBytes body)
      (.letE nonDep ty val body) := by
  let finish : Expr → Expr → Expr → GetM Expr :=
    fun decodedTy decodedVal decodedBody =>
      pure (.letE nonDep decodedTy decodedVal decodedBody)
  have hfinish : GetSpec (finish ty val body) ByteArray.empty
      (.letE nonDep ty val body) := GetSpec.pure _
  have hbody' := GetSpec.bind (next := finish ty val) hbody hfinish
  simp only [ByteArray.append_empty] at hbody'
  let afterVal : Expr → GetM Expr := fun decodedVal =>
    recur >>= finish ty decodedVal
  have hafterVal : GetSpec (afterVal val) (exprBytes body)
      (.letE nonDep ty val body) := by
    simpa [afterVal, finish] using hbody'
  have hvalBody := GetSpec.bind (next := afterVal) hval hafterVal
  let afterTy : Expr → GetM Expr := fun decodedTy =>
    recur >>= fun decodedVal => recur >>= finish decodedTy decodedVal
  have hafterTy : GetSpec (afterTy ty)
      (exprBytes val ++ exprBytes body) (.letE nonDep ty val body) := by
    simpa [afterTy, afterVal, finish] using hvalBody
  have htotal := GetSpec.bind (next := afterTy) hty hafterTy
  cases nonDep <;>
    simpa [getExprTag, Expr.FLAG_LET, afterTy, finish,
      ByteArray.append_assoc] using htotal

theorem payload_lt_of_header {header payload : ByteArray} {fuel : Nat}
    (hheader : 0 < header.size)
    (hfull : (header ++ payload).size < fuel + 1) :
    payload.size < fuel := by
  simp only [ByteArray.size_append] at hfull
  omega

mutual
  theorem getFuel_expr_spec (e : Expr) (fuel : Nat)
      (hwf : e.wireWF) (hfuel : (exprBytes e).size < fuel) :
      GetSpec (getExprFuel fuel) (exprBytes e) e := by
    cases fuel with
    | zero =>
      have hpos := exprBytes_size_pos e
      omega
    | succ fuel =>
      cases e with
      | sort idx =>
        have hpayload :
            GetSpec
              (getExprTag (getExprFuel fuel) ⟨Expr.FLAG_SORT, idx⟩)
              ByteArray.empty (.sort idx) := by
          simpa [getExprTag, Expr.FLAG_SORT] using
            GetSpec.pure (Expr.sort idx)
        have htotal := getExprHeader_of_spec (getExprFuel fuel)
          ⟨Expr.FLAG_SORT, idx⟩ (by simp [Expr.FLAG_SORT]) hpayload
        simpa [getExprFuel, exprBytes] using htotal
      | var idx =>
        have hpayload :
            GetSpec
              (getExprTag (getExprFuel fuel) ⟨Expr.FLAG_VAR, idx⟩)
              ByteArray.empty (.var idx) := by
          simpa [getExprTag, Expr.FLAG_VAR] using
            GetSpec.pure (Expr.var idx)
        have htotal := getExprHeader_of_spec (getExprFuel fuel)
          ⟨Expr.FLAG_VAR, idx⟩ (by simp [Expr.FLAG_VAR]) hpayload
        simpa [getExprFuel, exprBytes] using htotal
      | ref refIdx idxs =>
        have hcount : idxs.toList.length < UInt64.size := by
          simpa [Expr.wireWF] using hwf
        have hpayload := getExprTag_ref_spec (getExprFuel fuel)
          refIdx idxs.toList hcount
        have htotal := getExprHeader_of_spec (getExprFuel fuel)
          ⟨Expr.FLAG_REF, idxs.size.toUInt64⟩
          (by simp [Expr.FLAG_REF]) (by simpa using hpayload)
        simpa [getExprFuel, exprBytes, ByteArray.append_assoc] using htotal
      | recur recIdx idxs =>
        have hcount : idxs.toList.length < UInt64.size := by
          simpa [Expr.wireWF] using hwf
        have hpayload := getExprTag_recur_spec (getExprFuel fuel)
          recIdx idxs.toList hcount
        have htotal := getExprHeader_of_spec (getExprFuel fuel)
          ⟨Expr.FLAG_REC, idxs.size.toUInt64⟩
          (by simp [Expr.FLAG_REC]) (by simpa using hpayload)
        simpa [getExprFuel, exprBytes, ByteArray.append_assoc] using htotal
      | prj typeRefIdx fieldIdx val =>
        have htag := tag4Bytes_size_pos ⟨Expr.FLAG_PRJ, fieldIdx⟩
        have hvalFuel : (exprBytes val).size < fuel := by
          simp only [exprBytes, ByteArray.size_append] at hfuel
          omega
        have hval := getFuel_expr_spec val fuel
          (by simpa [Expr.wireWF] using hwf) hvalFuel
        have hpayload := getExprTag_prj_spec (getExprFuel fuel)
          typeRefIdx fieldIdx val hval
        have htotal := getExprHeader_of_spec (getExprFuel fuel)
          ⟨Expr.FLAG_PRJ, fieldIdx⟩ (by simp [Expr.FLAG_PRJ]) hpayload
        simpa [getExprFuel, exprBytes, ByteArray.append_assoc] using htotal
      | str idx =>
        have hpayload :
            GetSpec
              (getExprTag (getExprFuel fuel) ⟨Expr.FLAG_STR, idx⟩)
              ByteArray.empty (.str idx) := by
          simpa [getExprTag, Expr.FLAG_STR] using
            GetSpec.pure (Expr.str idx)
        have htotal := getExprHeader_of_spec (getExprFuel fuel)
          ⟨Expr.FLAG_STR, idx⟩ (by simp [Expr.FLAG_STR]) hpayload
        simpa [getExprFuel, exprBytes] using htotal
      | nat idx =>
        have hpayload :
            GetSpec
              (getExprTag (getExprFuel fuel) ⟨Expr.FLAG_NAT, idx⟩)
              ByteArray.empty (.nat idx) := by
          simpa [getExprTag, Expr.FLAG_NAT] using
            GetSpec.pure (Expr.nat idx)
        have htotal := getExprHeader_of_spec (getExprFuel fuel)
          ⟨Expr.FLAG_NAT, idx⟩ (by simp [Expr.FLAG_NAT]) hpayload
        simpa [getExprFuel, exprBytes] using htotal
      | app fn arg =>
        rcases hwf with ⟨hfnWF, hargWF, hcount⟩
        have htag := tag4Bytes_size_pos
          ⟨Expr.FLAG_APP, (fn.appCount + 1).toUInt64⟩
        have hpayload :
            (appSpineBytes fn ++ exprBytes arg).size < fuel := by
          apply payload_lt_of_header htag
          simpa only [exprBytes, ByteArray.append_assoc] using hfuel
        have hrun := getFuel_app_spec fn arg fuel hfnWF hargWF hpayload
        have hround :
            (fn.appCount + 1).toUInt64.toNat = fn.appCount + 1 :=
          UInt64.toNat_ofNat_of_lt hcount
        have htagPayload :
            GetSpec
              (getExprTag (getExprFuel fuel)
                ⟨Expr.FLAG_APP, (fn.appCount + 1).toUInt64⟩)
              (appSpineBytes fn ++ exprBytes arg) (.app fn arg) := by
          change GetSpec
            (getAppRun (getExprFuel fuel)
              (fn.appCount + 1).toUInt64.toNat)
            (appSpineBytes fn ++ exprBytes arg) (.app fn arg)
          rw [hround]
          simpa only [getAppRun] using hrun
        have htotal := getExprHeader_of_spec (getExprFuel fuel)
          ⟨Expr.FLAG_APP, (fn.appCount + 1).toUInt64⟩
          (by simp [Expr.FLAG_APP]) htagPayload
        simpa [getExprFuel, exprBytes, ByteArray.append_assoc] using htotal
      | lam u ty body =>
        rcases hwf with ⟨htyWF, hbodyWF, hcount⟩
        have htag := tag4Bytes_size_pos
          ⟨Expr.FLAG_LAM, (body.lamCount + 1).toUInt64⟩
        have hpayload :
            (lamModeBytes u ++ exprBytes ty ++ lamTailBytes body).size < fuel := by
          apply payload_lt_of_header htag
          simpa only [exprBytes, ByteArray.append_assoc] using hfuel
        have hrun := getFuel_lam_spec u ty body fuel htyWF hbodyWF hpayload
        have hround :
            (body.lamCount + 1).toUInt64.toNat = body.lamCount + 1 :=
          UInt64.toNat_ofNat_of_lt hcount
        have htagPayload :
            GetSpec
              (getExprTag (getExprFuel fuel)
                ⟨Expr.FLAG_LAM, (body.lamCount + 1).toUInt64⟩)
              (lamModeBytes u ++ exprBytes ty ++ lamTailBytes body)
              (.lam u ty body) := by
          change GetSpec
            (getLamRun (getExprFuel fuel)
              (body.lamCount + 1).toUInt64.toNat)
            (lamModeBytes u ++ exprBytes ty ++ lamTailBytes body)
            (.lam u ty body)
          rw [hround]
          simpa only [getLamRun] using hrun
        have htotal := getExprHeader_of_spec (getExprFuel fuel)
          ⟨Expr.FLAG_LAM, (body.lamCount + 1).toUInt64⟩
          (by simp [Expr.FLAG_LAM]) htagPayload
        simpa [getExprFuel, exprBytes, ByteArray.append_assoc] using htotal
      | all u o ty body =>
        rcases hwf with ⟨htyWF, hbodyWF, hcount⟩
        have htag := tag4Bytes_size_pos
          ⟨Expr.FLAG_ALL, (body.allCount + 1).toUInt64⟩
        have hpayload :
            (allModeBytes u o ++ exprBytes ty ++ allTailBytes body).size < fuel := by
          apply payload_lt_of_header htag
          simpa only [exprBytes, ByteArray.append_assoc] using hfuel
        have hrun := getFuel_all_spec u o ty body fuel htyWF hbodyWF hpayload
        have hround :
            (body.allCount + 1).toUInt64.toNat = body.allCount + 1 :=
          UInt64.toNat_ofNat_of_lt hcount
        have htagPayload :
            GetSpec
              (getExprTag (getExprFuel fuel)
                ⟨Expr.FLAG_ALL, (body.allCount + 1).toUInt64⟩)
              (allModeBytes u o ++ exprBytes ty ++ allTailBytes body)
              (.all u o ty body) := by
          change GetSpec
            (getAllRun (getExprFuel fuel)
              (body.allCount + 1).toUInt64.toNat)
            (allModeBytes u o ++ exprBytes ty ++ allTailBytes body)
            (.all u o ty body)
          rw [hround]
          simpa only [getAllRun] using hrun
        have htotal := getExprHeader_of_spec (getExprFuel fuel)
          ⟨Expr.FLAG_ALL, (body.allCount + 1).toUInt64⟩
          (by simp [Expr.FLAG_ALL]) htagPayload
        simpa [getExprFuel, exprBytes, ByteArray.append_assoc] using htotal
      | letE nonDep ty val body =>
        rcases hwf with ⟨htyWF, hvalWF, hbodyWF⟩
        have htag := tag4Bytes_size_pos
          ⟨Expr.FLAG_LET, if nonDep then 1 else 0⟩
        have htyFuel : (exprBytes ty).size < fuel := by
          simp only [exprBytes, ByteArray.size_append] at hfuel
          omega
        have hvalFuel : (exprBytes val).size < fuel := by
          simp only [exprBytes, ByteArray.size_append] at hfuel
          omega
        have hbodyFuel : (exprBytes body).size < fuel := by
          simp only [exprBytes, ByteArray.size_append] at hfuel
          omega
        have hty := getFuel_expr_spec ty fuel htyWF htyFuel
        have hval := getFuel_expr_spec val fuel hvalWF hvalFuel
        have hbody := getFuel_expr_spec body fuel hbodyWF hbodyFuel
        have hpayload := getExprTag_let_spec (getExprFuel fuel)
          nonDep ty val body hty hval hbody
        have htotal := getExprHeader_of_spec (getExprFuel fuel)
          ⟨Expr.FLAG_LET, if nonDep then 1 else 0⟩
          (by simp [Expr.FLAG_LET]) hpayload
        simpa [getExprFuel, exprBytes, ByteArray.append_assoc] using htotal
      | share idx =>
        have hpayload :
            GetSpec
              (getExprTag (getExprFuel fuel) ⟨Expr.FLAG_SHARE, idx⟩)
              ByteArray.empty (.share idx) := by
          simpa [getExprTag, Expr.FLAG_SHARE] using
            GetSpec.pure (Expr.share idx)
        have htotal := getExprHeader_of_spec (getExprFuel fuel)
          ⟨Expr.FLAG_SHARE, idx⟩ (by simp [Expr.FLAG_SHARE]) hpayload
        simpa [getExprFuel, exprBytes] using htotal
  termination_by (e.codecSize, 1)
  decreasing_by
    all_goals subst_vars
    all_goals first
      | apply Prod.Lex.left <;> simp [Expr.codecSize] <;> omega
      | apply Prod.Lex.right <;> omega

  theorem getFuel_app_spec (fn arg : Expr) (fuel : Nat)
      (hfnWF : fn.wireWF) (hargWF : arg.wireWF)
      (hfuel : (appSpineBytes fn ++ exprBytes arg).size < fuel) :
      GetSpec (getAppRunSucc (getExprFuel fuel) fn.appCount)
        (appSpineBytes fn ++ exprBytes arg) (.app fn arg) := by
    by_cases hbase : AppBase fn
    · have hfnFuel : (exprBytes fn).size < fuel := by
        cases fn <;> simp_all [AppBase, appSpineBytes, ByteArray.size_append]
        all_goals omega
      have hargFuel : (exprBytes arg).size < fuel := by
        cases fn <;> simp_all [AppBase, appSpineBytes, ByteArray.size_append]
        all_goals omega
      have hfn := getFuel_expr_spec fn fuel hfnWF hfnFuel
      have harg := getFuel_expr_spec arg fuel hargWF hargFuel
      have hzero := getAppRunSucc_zero_of_specs (getExprFuel fuel)
        fn arg hbase hfn harg
      cases fn <;> simp_all [AppBase, Expr.appCount, appSpineBytes]
    · cases fn <;> simp [AppBase] at hbase
      rename_i innerFn innerArg
      rcases hfnWF with ⟨hinnerFnWF, hinnerArgWF, hinnerCount⟩
      have hinnerFuel :
          (appSpineBytes innerFn ++ exprBytes innerArg).size < fuel := by
        simp only [appSpineBytes, ByteArray.size_append] at hfuel ⊢
        omega
      have hargFuel : (exprBytes arg).size < fuel := by
        simp only [appSpineBytes, ByteArray.size_append] at hfuel
        omega
      have hinner := getFuel_app_spec innerFn innerArg fuel
        hinnerFnWF hinnerArgWF hinnerFuel
      have harg := getFuel_expr_spec arg fuel hargWF hargFuel
      have hinner' :
          GetSpec (getAppRunSucc (getExprFuel fuel) innerFn.appCount)
            (appSpineBytes (.app innerFn innerArg))
            (.app innerFn innerArg) := by
        simpa only [appSpineBytes] using hinner
      have hstep := getAppRunSucc_step_of_specs (getExprFuel fuel)
        (.app innerFn innerArg) arg innerFn.appCount hinner' harg
      simpa [Expr.appCount, appSpineBytes, ByteArray.append_assoc] using hstep
  termination_by ((Expr.app fn arg).codecSize, 0)
  decreasing_by
    all_goals subst_vars
    all_goals first
      | apply Prod.Lex.left <;> simp [Expr.codecSize] <;> omega
      | apply Prod.Lex.right <;> omega

  theorem getFuel_lam_spec (u : Uses) (ty body : Expr) (fuel : Nat)
      (htyWF : ty.wireWF) (hbodyWF : body.wireWF)
      (hfuel :
        (lamModeBytes u ++ exprBytes ty ++ lamTailBytes body).size < fuel) :
      GetSpec (getLamRunSucc (getExprFuel fuel) body.lamCount)
        (lamModeBytes u ++ exprBytes ty ++ lamTailBytes body)
        (.lam u ty body) := by
    by_cases hbase : LamBase body
    · have htyFuel : (exprBytes ty).size < fuel := by
        simp only [ByteArray.size_append] at hfuel
        omega
      have hbodyFuel : (exprBytes body).size < fuel := by
        cases body <;> simp_all [LamBase, lamTailBytes, ByteArray.size_append]
        all_goals omega
      have hty := getFuel_expr_spec ty fuel htyWF htyFuel
      have hbody := getFuel_expr_spec body fuel hbodyWF hbodyFuel
      have hzero := getLamRunSucc_zero_of_specs (getExprFuel fuel)
        u ty body hbase hty hbody
      cases body <;> simp_all [LamBase, Expr.lamCount, lamTailBytes]
    · cases body <;> simp [LamBase] at hbase
      rename_i innerU innerTy innerBody
      rcases hbodyWF with ⟨hinnerTyWF, hinnerBodyWF, hinnerCount⟩
      have htyFuel : (exprBytes ty).size < fuel := by
        simp only [lamTailBytes, ByteArray.size_append] at hfuel
        omega
      have hinnerFuel :
          (lamModeBytes innerU ++ exprBytes innerTy ++
            lamTailBytes innerBody).size < fuel := by
        simp only [lamTailBytes, ByteArray.size_append] at hfuel ⊢
        omega
      have hty := getFuel_expr_spec ty fuel htyWF htyFuel
      have hinner := getFuel_lam_spec innerU innerTy innerBody fuel
        hinnerTyWF hinnerBodyWF hinnerFuel
      have hinner' :
          GetSpec (getLamRunSucc (getExprFuel fuel) innerBody.lamCount)
            (lamTailBytes (.lam innerU innerTy innerBody))
            (.lam innerU innerTy innerBody) := by
        simpa only [lamTailBytes] using hinner
      have hstep := getLamRunSucc_step_of_specs (getExprFuel fuel)
        u ty (.lam innerU innerTy innerBody) innerBody.lamCount hty hinner'
      simpa [Expr.lamCount, lamTailBytes, ByteArray.append_assoc] using hstep
  termination_by ((Expr.lam u ty body).codecSize, 0)
  decreasing_by
    all_goals subst_vars
    all_goals first
      | apply Prod.Lex.left <;> simp [Expr.codecSize] <;> omega
      | apply Prod.Lex.right <;> omega

  theorem getFuel_all_spec (u : Uses) (o : Owned) (ty body : Expr)
      (fuel : Nat) (htyWF : ty.wireWF) (hbodyWF : body.wireWF)
      (hfuel :
        (allModeBytes u o ++ exprBytes ty ++ allTailBytes body).size < fuel) :
      GetSpec (getAllRunSucc (getExprFuel fuel) body.allCount)
        (allModeBytes u o ++ exprBytes ty ++ allTailBytes body)
        (.all u o ty body) := by
    by_cases hbase : AllBase body
    · have htyFuel : (exprBytes ty).size < fuel := by
        simp only [ByteArray.size_append] at hfuel
        omega
      have hbodyFuel : (exprBytes body).size < fuel := by
        cases body <;> simp_all [AllBase, allTailBytes, ByteArray.size_append]
        all_goals omega
      have hty := getFuel_expr_spec ty fuel htyWF htyFuel
      have hbody := getFuel_expr_spec body fuel hbodyWF hbodyFuel
      have hzero := getAllRunSucc_zero_of_specs (getExprFuel fuel)
        u o ty body hbase hty hbody
      cases body <;> simp_all [AllBase, Expr.allCount, allTailBytes]
    · cases body <;> simp [AllBase] at hbase
      rename_i innerU innerO innerTy innerBody
      rcases hbodyWF with ⟨hinnerTyWF, hinnerBodyWF, hinnerCount⟩
      have htyFuel : (exprBytes ty).size < fuel := by
        simp only [allTailBytes, ByteArray.size_append] at hfuel
        omega
      have hinnerFuel :
          (allModeBytes innerU innerO ++ exprBytes innerTy ++
            allTailBytes innerBody).size < fuel := by
        simp only [allTailBytes, ByteArray.size_append] at hfuel ⊢
        omega
      have hty := getFuel_expr_spec ty fuel htyWF htyFuel
      have hinner := getFuel_all_spec innerU innerO innerTy innerBody fuel
        hinnerTyWF hinnerBodyWF hinnerFuel
      have hinner' :
          GetSpec (getAllRunSucc (getExprFuel fuel) innerBody.allCount)
            (allTailBytes (.all innerU innerO innerTy innerBody))
            (.all innerU innerO innerTy innerBody) := by
        simpa only [allTailBytes] using hinner
      have hstep := getAllRunSucc_step_of_specs (getExprFuel fuel)
        u o ty (.all innerU innerO innerTy innerBody)
        innerBody.allCount hty hinner'
      simpa [Expr.allCount, allTailBytes, ByteArray.append_assoc] using hstep
  termination_by ((Expr.all u o ty body).codecSize, 0)
  decreasing_by
    all_goals subst_vars
    all_goals first
      | apply Prod.Lex.left <;> simp [Expr.codecSize] <;> omega
      | apply Prod.Lex.right <;> omega
end

theorem getAppRunSucc_canonical_of (recur : GetM Expr)
    (hrecur : GetCanonical recur exprBytes) (extra : Nat) :
    GetCanonical (getAppRunSucc recur extra) appSpineBytes := by
  induction extra with
  | zero =>
    intro pre rest value st' h
    let afterBase : Expr → GetM Expr := fun base =>
      match base with
      | .app .. => throw "getExpr: non-canonical app base"
      | _ => do
        let arg ← recur
        return .app base arg
    change (recur >>= afterBase).run ⟨pre ++ rest, pre.size⟩ =
      .ok (value, st') at h
    obtain ⟨base, afterBaseBytes, hrestBase, hafterBase⟩ :=
      GetCanonical.bind_inv hrecur pre rest h
    have hbase : AppBase base := by
      cases base with
      | app fn arg =>
        simp [afterBase] at hafterBase
        change (Except.error _) = Except.ok (value, st') at hafterBase
        contradiction
      | _ => trivial
    let basePre := pre ++ exprBytes base
    let finish : Expr → GetM Expr := fun arg => pure (.app base arg)
    have hafterBase' :
        (recur >>= finish).run
          ⟨basePre ++ afterBaseBytes, basePre.size⟩ = .ok (value, st') := by
      cases base with
      | app fn arg => simp [AppBase] at hbase
      | _ =>
        simpa [afterBase, finish, basePre] using hafterBase
    obtain ⟨arg, suffix, hrestArg, hfinish⟩ :=
      GetCanonical.bind_inv hrecur basePre afterBaseBytes hafterBase'
    simp [finish] at hfinish
    cases hfinish
    refine ⟨suffix, ?_, ?_⟩
    · rw [hrestBase, hrestArg]
      cases base <;> simp_all [AppBase, appSpineBytes,
        ByteArray.append_assoc]
    · cases base <;> simp_all [AppBase, appSpineBytes, basePre,
        ByteArray.append_assoc,
        ByteArray.size_append, Nat.add_assoc]
  | succ extra ih =>
    intro pre rest value st' h
    let afterFn : Expr → GetM Expr := fun fn => do
      let arg ← recur
      return .app fn arg
    change (getAppRunSucc recur extra >>= afterFn).run
      ⟨pre ++ rest, pre.size⟩ = .ok (value, st') at h
    obtain ⟨fn, afterFnBytes, hrestFn, hafterFn⟩ :=
      GetCanonical.bind_inv ih pre rest h
    let fnPre := pre ++ appSpineBytes fn
    let finish : Expr → GetM Expr := fun arg => pure (.app fn arg)
    have hafterFn' :
        (recur >>= finish).run
          ⟨fnPre ++ afterFnBytes, fnPre.size⟩ = .ok (value, st') := by
      simpa [afterFn, finish, fnPre] using hafterFn
    obtain ⟨arg, suffix, hrestArg, hfinish⟩ :=
      GetCanonical.bind_inv hrecur fnPre afterFnBytes hafterFn'
    simp [finish] at hfinish
    cases hfinish
    refine ⟨suffix, ?_, ?_⟩
    · rw [hrestFn, hrestArg]
      simp [appSpineBytes, ByteArray.append_assoc]
    · simp [appSpineBytes, fnPre, hrestFn, hrestArg,
        ByteArray.append_assoc, ByteArray.size_append,
        Nat.add_assoc]

theorem getAppRunSucc_success_count (recur : GetM Expr) (extra : Nat) :
    ∀ (initial : GetState) {value : Expr} {st' : GetState},
      (getAppRunSucc recur extra).run initial = .ok (value, st') →
      ∃ fn arg, value = .app fn arg ∧ value.appCount = extra + 1 := by
  induction extra with
  | zero =>
    intro initial value st' h
    simp only [getAppRunSucc, StateT.run_bind] at h
    cases hb : recur.run initial with
    | error err => rw [hb] at h; contradiction
    | ok baseState =>
      rcases baseState with ⟨base, afterBase⟩
      rw [hb] at h
      simp only [bind, Except.bind] at h
      have hbase : AppBase base := by
        cases base with
        | app fn arg =>
          change (Except.error _) = Except.ok (value, st') at h
          contradiction
        | _ => trivial
      have hcont :
          (recur >>= fun arg => pure (.app base arg)).run afterBase =
            .ok (value, st') := by
        cases base with
        | app fn arg => simp [AppBase] at hbase
        | _ =>
          exact h
      simp only [StateT.run_bind] at hcont
      cases ha : recur.run afterBase with
      | error err => rw [ha] at hcont; contradiction
      | ok argState =>
        rcases argState with ⟨arg, afterArg⟩
        rw [ha] at hcont
        simp at hcont
        cases hcont
        have hbaseCount : base.appCount = 0 := by
          cases base <;> simp_all [AppBase, Expr.appCount]
        exact ⟨base, arg, rfl, by simp [Expr.appCount, hbaseCount]⟩
  | succ extra ih =>
    intro initial value st' h
    simp only [getAppRunSucc, StateT.run_bind] at h
    cases hf : (getAppRunSucc recur extra).run initial with
    | error err => rw [hf] at h; contradiction
    | ok fnState =>
      rcases fnState with ⟨fn, afterFn⟩
      rw [hf] at h
      simp only [bind, Except.bind] at h
      cases ha : recur.run afterFn with
      | error err => rw [ha] at h; contradiction
      | ok argState =>
        rcases argState with ⟨arg, afterArg⟩
        rw [ha] at h
        simp at h
        cases h
        obtain ⟨innerFn, innerArg, hfn, hcount⟩ := ih initial hf
        refine ⟨fn, arg, rfl, ?_⟩
        simp [Expr.appCount, hcount]

theorem getAppRun_canonical_of (recur : GetM Expr)
    (hrecur : GetCanonical recur exprBytes) (count : Nat) :
    GetCanonical (getAppRun recur count) appSpineBytes := by
  cases count with
  | zero =>
    intro pre rest value st' h
    simp [getAppRun] at h
    change (Except.error _) = Except.ok (value, st') at h
    contradiction
  | succ extra =>
    simpa [getAppRun] using getAppRunSucc_canonical_of recur hrecur extra

theorem getAppRun_success_count (recur : GetM Expr) (count : Nat)
    (initial : GetState) {value : Expr} {st' : GetState}
    (h : (getAppRun recur count).run initial = .ok (value, st')) :
    ∃ fn arg, value = .app fn arg ∧ value.appCount = count := by
  cases count with
  | zero =>
    simp [getAppRun] at h
    change (Except.error _) = Except.ok (value, st') at h
    contradiction
  | succ extra =>
    have h' : (getAppRunSucc recur extra).run initial = .ok (value, st') := by
      simpa [getAppRun] using h
    obtain ⟨fn, arg, hvalue, hcount⟩ :=
      getAppRunSucc_success_count recur extra initial h'
    exact ⟨fn, arg, hvalue, by simpa using hcount⟩

theorem getLamRunSucc_canonical_of (recur : GetM Expr)
    (hrecur : GetCanonical recur exprBytes) (extra : Nat) :
    GetCanonical (getLamRunSucc recur extra) lamTailBytes := by
  induction extra with
  | zero =>
    intro pre rest value st' h
    let afterMode : Uses → GetM Expr := fun u => do
      let ty ← recur
      let body ← recur
      match body with
      | .lam .. => throw "getExpr: non-canonical lam telescope"
      | _ => return .lam u ty body
    change (getLamMode >>= afterMode).run ⟨pre ++ rest, pre.size⟩ =
      .ok (value, st') at h
    obtain ⟨u, afterModeBytes, hrestMode, hafterMode⟩ :=
      GetCanonical.bind_inv getLamMode_canonical pre rest h
    let modePre := pre ++ lamModeBytes u
    let afterTy : Expr → GetM Expr := fun ty => do
      let body ← recur
      match body with
      | .lam .. => throw "getExpr: non-canonical lam telescope"
      | _ => return .lam u ty body
    have hafterMode' :
        (recur >>= afterTy).run
          ⟨modePre ++ afterModeBytes, modePre.size⟩ = .ok (value, st') := by
      simpa [afterMode, afterTy, modePre] using hafterMode
    obtain ⟨ty, afterTyBytes, hrestTy, hafterTy⟩ :=
      GetCanonical.bind_inv hrecur modePre afterModeBytes hafterMode'
    let tyPre := modePre ++ exprBytes ty
    let finish : Expr → GetM Expr := fun body =>
      match body with
      | .lam .. => throw "getExpr: non-canonical lam telescope"
      | _ => pure (.lam u ty body)
    have hafterTy' :
        (recur >>= finish).run
          ⟨tyPre ++ afterTyBytes, tyPre.size⟩ = .ok (value, st') := by
      simpa [afterTy, finish, tyPre] using hafterTy
    obtain ⟨body, suffix, hrestBody, hfinish⟩ :=
      GetCanonical.bind_inv hrecur tyPre afterTyBytes hafterTy'
    have hbody : LamBase body := by
      cases body with
      | lam u' ty' body' =>
        change (Except.error _) = Except.ok (value, st') at hfinish
        contradiction
      | _ => trivial
    have hpure :
        (pure (.lam u ty body) : GetM Expr).run
          ⟨(tyPre ++ exprBytes body) ++ suffix,
            (tyPre ++ exprBytes body).size⟩ = .ok (value, st') := by
      cases body with
      | lam u' ty' body' => simp [LamBase] at hbody
      | _ => exact hfinish
    simp at hpure
    cases hpure
    refine ⟨suffix, ?_, ?_⟩
    · rw [hrestMode, hrestTy, hrestBody]
      cases body <;> simp_all [LamBase, lamTailBytes,
        ByteArray.append_assoc]
    · cases body <;> simp_all [LamBase, lamTailBytes, modePre, tyPre,
        ByteArray.append_assoc,
        ByteArray.size_append, Nat.add_assoc]
  | succ extra ih =>
    intro pre rest value st' h
    let afterMode : Uses → GetM Expr := fun u => do
      let ty ← recur
      return .lam u ty (← getLamRunSucc recur extra)
    change (getLamMode >>= afterMode).run ⟨pre ++ rest, pre.size⟩ =
      .ok (value, st') at h
    obtain ⟨u, afterModeBytes, hrestMode, hafterMode⟩ :=
      GetCanonical.bind_inv getLamMode_canonical pre rest h
    let modePre := pre ++ lamModeBytes u
    let afterTy : Expr → GetM Expr := fun ty => do
      let body ← getLamRunSucc recur extra
      return .lam u ty body
    have hafterMode' :
        (recur >>= afterTy).run
          ⟨modePre ++ afterModeBytes, modePre.size⟩ = .ok (value, st') := by
      simpa [afterMode, afterTy, modePre] using hafterMode
    obtain ⟨ty, afterTyBytes, hrestTy, hafterTy⟩ :=
      GetCanonical.bind_inv hrecur modePre afterModeBytes hafterMode'
    let tyPre := modePre ++ exprBytes ty
    let finish : Expr → GetM Expr := fun body => pure (.lam u ty body)
    have hafterTy' :
        (getLamRunSucc recur extra >>= finish).run
          ⟨tyPre ++ afterTyBytes, tyPre.size⟩ = .ok (value, st') := by
      simpa [afterTy, finish, tyPre] using hafterTy
    obtain ⟨body, suffix, hrestBody, hfinish⟩ :=
      GetCanonical.bind_inv ih tyPre afterTyBytes hafterTy'
    simp [finish] at hfinish
    cases hfinish
    refine ⟨suffix, ?_, ?_⟩
    · rw [hrestMode, hrestTy, hrestBody]
      simp [lamTailBytes, ByteArray.append_assoc]
    · simp [lamTailBytes, modePre, tyPre, hrestMode, hrestTy,
        hrestBody, ByteArray.append_assoc, ByteArray.size_append,
        Nat.add_assoc]

theorem getLamRun_canonical_of (recur : GetM Expr)
    (hrecur : GetCanonical recur exprBytes) (count : Nat) :
    GetCanonical (getLamRun recur count) lamTailBytes := by
  cases count with
  | zero =>
    intro pre rest value st' h
    simp [getLamRun] at h
    change (Except.error _) = Except.ok (value, st') at h
    contradiction
  | succ extra =>
    simpa [getLamRun] using getLamRunSucc_canonical_of recur hrecur extra

theorem getLamRunSucc_success_count (recur : GetM Expr) (extra : Nat) :
    ∀ (initial : GetState) {value : Expr} {st' : GetState},
      (getLamRunSucc recur extra).run initial = .ok (value, st') →
      ∃ u ty body,
        value = .lam u ty body ∧ value.lamCount = extra + 1 := by
  induction extra with
  | zero =>
    intro initial value st' h
    simp only [getLamRunSucc, StateT.run_bind] at h
    cases hm : getLamMode.run initial with
    | error err => rw [hm] at h; contradiction
    | ok modeState =>
      rcases modeState with ⟨u, afterMode⟩
      rw [hm] at h
      simp only [bind, Except.bind] at h
      cases ht : recur.run afterMode with
      | error err => rw [ht] at h; contradiction
      | ok tyState =>
        rcases tyState with ⟨ty, afterTy⟩
        rw [ht] at h
        simp only at h
        cases hb : recur.run afterTy with
        | error err => rw [hb] at h; contradiction
        | ok bodyState =>
          rcases bodyState with ⟨body, afterBody⟩
          rw [hb] at h
          simp only at h
          have hbase : LamBase body := by
            cases body with
            | lam u' ty' body' =>
              change (Except.error _) = Except.ok (value, st') at h
              contradiction
            | _ => trivial
          have hpure :
              (pure (.lam u ty body) : GetM Expr).run afterBody =
                .ok (value, st') := by
            cases body with
            | lam u' ty' body' => simp [LamBase] at hbase
            | _ => exact h
          simp at hpure
          cases hpure
          have hbodyCount : body.lamCount = 0 := by
            cases body <;> simp_all [LamBase, Expr.lamCount]
          exact ⟨u, ty, body, rfl, by simp [Expr.lamCount, hbodyCount]⟩
  | succ extra ih =>
    intro initial value st' h
    simp only [getLamRunSucc, StateT.run_bind] at h
    cases hm : getLamMode.run initial with
    | error err => rw [hm] at h; contradiction
    | ok modeState =>
      rcases modeState with ⟨u, afterMode⟩
      rw [hm] at h
      simp only [bind, Except.bind] at h
      cases ht : recur.run afterMode with
      | error err => rw [ht] at h; contradiction
      | ok tyState =>
        rcases tyState with ⟨ty, afterTy⟩
        rw [ht] at h
        simp only at h
        cases hb : (getLamRunSucc recur extra).run afterTy with
        | error err => rw [hb] at h; contradiction
        | ok bodyState =>
          rcases bodyState with ⟨body, afterBody⟩
          rw [hb] at h
          simp at h
          cases h
          obtain ⟨innerU, innerTy, innerBody, hbody, hcount⟩ :=
            ih afterTy hb
          refine ⟨u, ty, body, rfl, ?_⟩
          simp [Expr.lamCount, hcount]

theorem getLamRun_success_count (recur : GetM Expr) (count : Nat)
    (initial : GetState) {value : Expr} {st' : GetState}
    (h : (getLamRun recur count).run initial = .ok (value, st')) :
    ∃ u ty body, value = .lam u ty body ∧ value.lamCount = count := by
  cases count with
  | zero =>
    simp [getLamRun] at h
    change (Except.error _) = Except.ok (value, st') at h
    contradiction
  | succ extra =>
    have h' : (getLamRunSucc recur extra).run initial = .ok (value, st') := by
      simpa [getLamRun] using h
    obtain ⟨u, ty, body, hvalue, hcount⟩ :=
      getLamRunSucc_success_count recur extra initial h'
    exact ⟨u, ty, body, hvalue, by simpa using hcount⟩

theorem getAllRunSucc_canonical_of (recur : GetM Expr)
    (hrecur : GetCanonical recur exprBytes) (extra : Nat) :
    GetCanonical (getAllRunSucc recur extra) allTailBytes := by
  induction extra with
  | zero =>
    intro pre rest value st' h
    let afterMode : Uses × Owned → GetM Expr := fun mode => do
      let ty ← recur
      let body ← recur
      match body with
      | .all .. => throw "getExpr: non-canonical all telescope"
      | _ => return .all mode.1 mode.2 ty body
    change (getAllMode >>= afterMode).run ⟨pre ++ rest, pre.size⟩ =
      .ok (value, st') at h
    obtain ⟨mode, afterModeBytes, hrestMode, hafterMode⟩ :=
      GetCanonical.bind_inv getAllMode_canonical pre rest h
    let modePre := pre ++ allModeBytes mode.1 mode.2
    let afterTy : Expr → GetM Expr := fun ty => do
      let body ← recur
      match body with
      | .all .. => throw "getExpr: non-canonical all telescope"
      | _ => return .all mode.1 mode.2 ty body
    have hafterMode' :
        (recur >>= afterTy).run
          ⟨modePre ++ afterModeBytes, modePre.size⟩ = .ok (value, st') := by
      simpa [afterMode, afterTy, modePre] using hafterMode
    obtain ⟨ty, afterTyBytes, hrestTy, hafterTy⟩ :=
      GetCanonical.bind_inv hrecur modePre afterModeBytes hafterMode'
    let tyPre := modePre ++ exprBytes ty
    let finish : Expr → GetM Expr := fun body =>
      match body with
      | .all .. => throw "getExpr: non-canonical all telescope"
      | _ => pure (.all mode.1 mode.2 ty body)
    have hafterTy' :
        (recur >>= finish).run
          ⟨tyPre ++ afterTyBytes, tyPre.size⟩ = .ok (value, st') := by
      simpa [afterTy, finish, tyPre] using hafterTy
    obtain ⟨body, suffix, hrestBody, hfinish⟩ :=
      GetCanonical.bind_inv hrecur tyPre afterTyBytes hafterTy'
    have hbody : AllBase body := by
      cases body with
      | all u' o' ty' body' =>
        change (Except.error _) = Except.ok (value, st') at hfinish
        contradiction
      | _ => trivial
    have hpure :
        (pure (.all mode.1 mode.2 ty body) : GetM Expr).run
          ⟨(tyPre ++ exprBytes body) ++ suffix,
            (tyPre ++ exprBytes body).size⟩ = .ok (value, st') := by
      cases body with
      | all u' o' ty' body' => simp [AllBase] at hbody
      | _ => exact hfinish
    simp at hpure
    cases hpure
    refine ⟨suffix, ?_, ?_⟩
    · rw [hrestMode, hrestTy, hrestBody]
      cases body <;> simp_all [AllBase, allTailBytes,
        ByteArray.append_assoc]
    · cases body <;> simp_all [AllBase, allTailBytes, modePre, tyPre,
        ByteArray.append_assoc,
        ByteArray.size_append, Nat.add_assoc]
  | succ extra ih =>
    intro pre rest value st' h
    let afterMode : Uses × Owned → GetM Expr := fun mode => do
      let ty ← recur
      return .all mode.1 mode.2 ty (← getAllRunSucc recur extra)
    change (getAllMode >>= afterMode).run ⟨pre ++ rest, pre.size⟩ =
      .ok (value, st') at h
    obtain ⟨mode, afterModeBytes, hrestMode, hafterMode⟩ :=
      GetCanonical.bind_inv getAllMode_canonical pre rest h
    let modePre := pre ++ allModeBytes mode.1 mode.2
    let afterTy : Expr → GetM Expr := fun ty => do
      let body ← getAllRunSucc recur extra
      return .all mode.1 mode.2 ty body
    have hafterMode' :
        (recur >>= afterTy).run
          ⟨modePre ++ afterModeBytes, modePre.size⟩ = .ok (value, st') := by
      simpa [afterMode, afterTy, modePre] using hafterMode
    obtain ⟨ty, afterTyBytes, hrestTy, hafterTy⟩ :=
      GetCanonical.bind_inv hrecur modePre afterModeBytes hafterMode'
    let tyPre := modePre ++ exprBytes ty
    let finish : Expr → GetM Expr := fun body =>
      pure (.all mode.1 mode.2 ty body)
    have hafterTy' :
        (getAllRunSucc recur extra >>= finish).run
          ⟨tyPre ++ afterTyBytes, tyPre.size⟩ = .ok (value, st') := by
      simpa [afterTy, finish, tyPre] using hafterTy
    obtain ⟨body, suffix, hrestBody, hfinish⟩ :=
      GetCanonical.bind_inv ih tyPre afterTyBytes hafterTy'
    simp [finish] at hfinish
    cases hfinish
    refine ⟨suffix, ?_, ?_⟩
    · rw [hrestMode, hrestTy, hrestBody]
      simp [allTailBytes, ByteArray.append_assoc]
    · simp [allTailBytes, modePre, tyPre, hrestMode, hrestTy,
        hrestBody, ByteArray.append_assoc, ByteArray.size_append,
        Nat.add_assoc]

theorem getAllRun_canonical_of (recur : GetM Expr)
    (hrecur : GetCanonical recur exprBytes) (count : Nat) :
    GetCanonical (getAllRun recur count) allTailBytes := by
  cases count with
  | zero =>
    intro pre rest value st' h
    simp [getAllRun] at h
    change (Except.error _) = Except.ok (value, st') at h
    contradiction
  | succ extra =>
    simpa [getAllRun] using getAllRunSucc_canonical_of recur hrecur extra

theorem getAllRunSucc_success_count (recur : GetM Expr) (extra : Nat) :
    ∀ (initial : GetState) {value : Expr} {st' : GetState},
      (getAllRunSucc recur extra).run initial = .ok (value, st') →
      ∃ u o ty body,
        value = .all u o ty body ∧ value.allCount = extra + 1 := by
  induction extra with
  | zero =>
    intro initial value st' h
    simp only [getAllRunSucc, StateT.run_bind] at h
    cases hm : getAllMode.run initial with
    | error err => rw [hm] at h; contradiction
    | ok modeState =>
      rcases modeState with ⟨mode, afterMode⟩
      rw [hm] at h
      simp only [bind, Except.bind] at h
      cases ht : recur.run afterMode with
      | error err => rw [ht] at h; contradiction
      | ok tyState =>
        rcases tyState with ⟨ty, afterTy⟩
        rw [ht] at h
        simp only at h
        cases hb : recur.run afterTy with
        | error err => rw [hb] at h; contradiction
        | ok bodyState =>
          rcases bodyState with ⟨body, afterBody⟩
          rw [hb] at h
          simp only at h
          have hbase : AllBase body := by
            cases body with
            | all u' o' ty' body' =>
              change (Except.error _) = Except.ok (value, st') at h
              contradiction
            | _ => trivial
          have hpure :
              (pure (.all mode.1 mode.2 ty body) : GetM Expr).run afterBody =
                .ok (value, st') := by
            cases body with
            | all u' o' ty' body' => simp [AllBase] at hbase
            | _ => exact h
          simp at hpure
          cases hpure
          have hbodyCount : body.allCount = 0 := by
            cases body <;> simp_all [AllBase, Expr.allCount]
          exact ⟨mode.1, mode.2, ty, body, rfl,
            by simp [Expr.allCount, hbodyCount]⟩
  | succ extra ih =>
    intro initial value st' h
    simp only [getAllRunSucc, StateT.run_bind] at h
    cases hm : getAllMode.run initial with
    | error err => rw [hm] at h; contradiction
    | ok modeState =>
      rcases modeState with ⟨mode, afterMode⟩
      rw [hm] at h
      simp only [bind, Except.bind] at h
      cases ht : recur.run afterMode with
      | error err => rw [ht] at h; contradiction
      | ok tyState =>
        rcases tyState with ⟨ty, afterTy⟩
        rw [ht] at h
        simp only at h
        cases hb : (getAllRunSucc recur extra).run afterTy with
        | error err => rw [hb] at h; contradiction
        | ok bodyState =>
          rcases bodyState with ⟨body, afterBody⟩
          rw [hb] at h
          simp at h
          cases h
          obtain ⟨innerU, innerO, innerTy, innerBody, hbody, hcount⟩ :=
            ih afterTy hb
          refine ⟨mode.1, mode.2, ty, body, rfl, ?_⟩
          simp [Expr.allCount, hcount]

theorem getAllRun_success_count (recur : GetM Expr) (count : Nat)
    (initial : GetState) {value : Expr} {st' : GetState}
    (h : (getAllRun recur count).run initial = .ok (value, st')) :
    ∃ u o ty body,
      value = .all u o ty body ∧ value.allCount = count := by
  cases count with
  | zero =>
    simp [getAllRun] at h
    change (Except.error _) = Except.ok (value, st') at h
    contradiction
  | succ extra =>
    have h' : (getAllRunSucc recur extra).run initial = .ok (value, st') := by
      simpa [getAllRun] using h
    obtain ⟨u, o, ty, body, hvalue, hcount⟩ :=
      getAllRunSucc_success_count recur extra initial h'
    exact ⟨u, o, ty, body, hvalue, by simpa using hcount⟩

def ExprTagCanonical (recur : GetM Expr) (tag : Tag4) : Prop :=
  ∀ (pre rest : ByteArray) {value : Expr} {st' : GetState},
    (getExprTag recur tag).run ⟨pre ++ rest, pre.size⟩ = .ok (value, st') →
    ∃ payload suffix,
      rest = payload ++ suffix ∧
      tag4Bytes tag ++ payload = exprBytes value ∧
      st' = ⟨pre ++ rest, pre.size + payload.size⟩

theorem getExprTag_ref_canonical (recur : GetM Expr) (size : UInt64) :
    ExprTagCanonical recur ⟨Expr.FLAG_REF, size⟩ := by
  intro pre rest value st' h
  let afterRef : Tag0 → GetM Expr := fun refTag => do
    let idxs ← getTag0List size.toNat
    return .ref refTag.size idxs.toArray
  change (getTag0 >>= afterRef).run ⟨pre ++ rest, pre.size⟩ =
    .ok (value, st') at h
  obtain ⟨refTag, afterRefBytes, hrestRef, hafterRef⟩ :=
    GetCanonical.bind_inv getTag0_canonical pre rest h
  let refPre := pre ++ tag0Bytes refTag
  change (getTag0List size.toNat >>= fun idxs =>
    pure (.ref refTag.size idxs.toArray)).run
      ⟨refPre ++ afterRefBytes, refPre.size⟩ = .ok (value, st') at hafterRef
  simp only [StateT.run_bind] at hafterRef
  cases hi : (getTag0List size.toNat).run
      ⟨refPre ++ afterRefBytes, refPre.size⟩ with
  | error err => rw [hi] at hafterRef; contradiction
  | ok idxState =>
    rcases idxState with ⟨idxs, afterIdxs⟩
    rw [hi] at hafterRef
    simp at hafterRef
    cases hafterRef
    obtain ⟨suffix, hrestIdxs, hafterIdxs⟩ :=
      getTag0List_canonical size.toNat refPre afterRefBytes hi
    have hlength := getTag0List_success_length size.toNat
      ⟨refPre ++ afterRefBytes, refPre.size⟩ hi
    have hsize : idxs.length.toUInt64 = size := by
      rw [hlength]
      exact UInt64.ofNat_toNat
    let payload := tag0Bytes refTag ++ tag0ListBytes idxs
    refine ⟨payload, suffix, ?_, ?_, ?_⟩
    · simp [payload, hrestRef, hrestIdxs, ByteArray.append_assoc]
    · simp [payload, exprBytes, hsize, ByteArray.append_assoc]
    · simpa [payload, refPre, hrestRef, hrestIdxs,
        ByteArray.append_assoc, ByteArray.size_append,
        Nat.add_assoc] using hafterIdxs

theorem getExprTag_recur_canonical (recur : GetM Expr) (size : UInt64) :
    ExprTagCanonical recur ⟨Expr.FLAG_REC, size⟩ := by
  intro pre rest value st' h
  let afterRef : Tag0 → GetM Expr := fun refTag => do
    let idxs ← getTag0List size.toNat
    return .recur refTag.size idxs.toArray
  change (getTag0 >>= afterRef).run ⟨pre ++ rest, pre.size⟩ =
    .ok (value, st') at h
  obtain ⟨refTag, afterRefBytes, hrestRef, hafterRef⟩ :=
    GetCanonical.bind_inv getTag0_canonical pre rest h
  let refPre := pre ++ tag0Bytes refTag
  change (getTag0List size.toNat >>= fun idxs =>
    pure (.recur refTag.size idxs.toArray)).run
      ⟨refPre ++ afterRefBytes, refPre.size⟩ = .ok (value, st') at hafterRef
  simp only [StateT.run_bind] at hafterRef
  cases hi : (getTag0List size.toNat).run
      ⟨refPre ++ afterRefBytes, refPre.size⟩ with
  | error err => rw [hi] at hafterRef; contradiction
  | ok idxState =>
    rcases idxState with ⟨idxs, afterIdxs⟩
    rw [hi] at hafterRef
    simp at hafterRef
    cases hafterRef
    obtain ⟨suffix, hrestIdxs, hafterIdxs⟩ :=
      getTag0List_canonical size.toNat refPre afterRefBytes hi
    have hlength := getTag0List_success_length size.toNat
      ⟨refPre ++ afterRefBytes, refPre.size⟩ hi
    have hsize : idxs.length.toUInt64 = size := by
      rw [hlength]
      exact UInt64.ofNat_toNat
    let payload := tag0Bytes refTag ++ tag0ListBytes idxs
    refine ⟨payload, suffix, ?_, ?_, ?_⟩
    · simp [payload, hrestRef, hrestIdxs, ByteArray.append_assoc]
    · simp [payload, exprBytes, hsize, ByteArray.append_assoc]
    · simpa [payload, refPre, hrestRef, hrestIdxs,
        ByteArray.append_assoc, ByteArray.size_append,
        Nat.add_assoc] using hafterIdxs

theorem getExprTag_prj_canonical (recur : GetM Expr)
    (hrecur : GetCanonical recur exprBytes) (fieldIdx : UInt64) :
    ExprTagCanonical recur ⟨Expr.FLAG_PRJ, fieldIdx⟩ := by
  intro pre rest value st' h
  let afterRef : Tag0 → GetM Expr := fun refTag => do
    let val ← recur
    return .prj refTag.size fieldIdx val
  change (getTag0 >>= afterRef).run ⟨pre ++ rest, pre.size⟩ =
    .ok (value, st') at h
  obtain ⟨refTag, afterRefBytes, hrestRef, hafterRef⟩ :=
    GetCanonical.bind_inv getTag0_canonical pre rest h
  let refPre := pre ++ tag0Bytes refTag
  let finish : Expr → GetM Expr := fun val =>
    pure (.prj refTag.size fieldIdx val)
  have hafterRef' :
      (recur >>= finish).run ⟨refPre ++ afterRefBytes, refPre.size⟩ =
        .ok (value, st') := by
    simpa [afterRef, finish, refPre] using hafterRef
  obtain ⟨val, suffix, hrestVal, hfinish⟩ :=
    GetCanonical.bind_inv hrecur refPre afterRefBytes hafterRef'
  simp [finish] at hfinish
  cases hfinish
  let payload := tag0Bytes refTag ++ exprBytes val
  refine ⟨payload, suffix, ?_, ?_, ?_⟩
  · simp [payload, hrestRef, hrestVal, ByteArray.append_assoc]
  · simp [payload, exprBytes, ByteArray.append_assoc]
  · simp [payload, refPre, hrestRef, hrestVal,
      ByteArray.append_assoc, ByteArray.size_append,
      Nat.add_assoc]

theorem getExprTag_let_canonical (recur : GetM Expr)
    (hrecur : GetCanonical recur exprBytes) (size : UInt64)
    (hsize : ¬size > 1) :
    ExprTagCanonical recur ⟨Expr.FLAG_LET, size⟩ := by
  intro pre rest value st' h
  let nonDep := size == 1
  let afterTy : Expr → GetM Expr := fun ty => do
    let val ← recur
    let body ← recur
    return .letE nonDep ty val body
  simp only [getExprTag, Expr.FLAG_LET, hsize, if_false] at h
  change (recur >>= afterTy).run ⟨pre ++ rest, pre.size⟩ =
    .ok (value, st') at h
  obtain ⟨ty, afterTyBytes, hrestTy, hafterTy⟩ :=
    GetCanonical.bind_inv hrecur pre rest h
  let tyPre := pre ++ exprBytes ty
  let afterVal : Expr → GetM Expr := fun val => do
    let body ← recur
    return .letE nonDep ty val body
  have hafterTy' :
      (recur >>= afterVal).run
        ⟨tyPre ++ afterTyBytes, tyPre.size⟩ = .ok (value, st') := by
    simpa [afterTy, afterVal, tyPre] using hafterTy
  obtain ⟨val, afterValBytes, hrestVal, hafterVal⟩ :=
    GetCanonical.bind_inv hrecur tyPre afterTyBytes hafterTy'
  let valPre := tyPre ++ exprBytes val
  let finish : Expr → GetM Expr := fun body =>
    pure (.letE nonDep ty val body)
  have hafterVal' :
      (recur >>= finish).run
        ⟨valPre ++ afterValBytes, valPre.size⟩ = .ok (value, st') := by
    simpa [afterVal, finish, valPre] using hafterVal
  obtain ⟨body, suffix, hrestBody, hfinish⟩ :=
    GetCanonical.bind_inv hrecur valPre afterValBytes hafterVal'
  simp [finish] at hfinish
  cases hfinish
  have hencodedSize : (if nonDep then 1 else 0) = size := by
    dsimp [nonDep]
    have hsize' : ¬1 < size.toNat := by
      simpa [UInt64.lt_iff_toNat_lt] using hsize
    have hcases : size.toNat = 0 ∨ size.toNat = 1 := by omega
    rcases hcases with hzero | hone
    · have : size = 0 := UInt64.toNat_inj.1 (by simpa using hzero)
      subst size
      rfl
    · have : size = 1 := UInt64.toNat_inj.1 (by simpa using hone)
      subst size
      rfl
  let payload := exprBytes ty ++ exprBytes val ++ exprBytes body
  refine ⟨payload, suffix, ?_, ?_, ?_⟩
  · simp [payload, hrestTy, hrestVal, hrestBody,
      ByteArray.append_assoc]
  · simp [payload, exprBytes, hencodedSize, ByteArray.append_assoc]
  · simp [payload, tyPre, valPre, hrestTy, hrestVal, hrestBody,
      ByteArray.append_assoc, ByteArray.size_append,
      Nat.add_assoc]

theorem getExprTag_app_canonical (recur : GetM Expr)
    (hrecur : GetCanonical recur exprBytes) (size : UInt64) :
    ExprTagCanonical recur ⟨Expr.FLAG_APP, size⟩ := by
  intro pre rest value st' h
  change (getAppRun recur size.toNat).run ⟨pre ++ rest, pre.size⟩ =
    .ok (value, st') at h
  obtain ⟨suffix, hrest, hstate⟩ :=
    getAppRun_canonical_of recur hrecur size.toNat pre rest h
  obtain ⟨fn, arg, hvalue, hcount⟩ :=
    getAppRun_success_count recur size.toNat
      ⟨pre ++ rest, pre.size⟩ h
  subst value
  have hsize : (fn.appCount + 1).toUInt64 = size := by
    change (Expr.appCount (.app fn arg)).toUInt64 = size
    rw [hcount]
    exact UInt64.ofNat_toNat
  exact ⟨appSpineBytes (.app fn arg), suffix, hrest,
    by simp [exprBytes, appSpineBytes, hsize, ByteArray.append_assoc], hstate⟩

theorem getExprTag_lam_canonical (recur : GetM Expr)
    (hrecur : GetCanonical recur exprBytes) (size : UInt64) :
    ExprTagCanonical recur ⟨Expr.FLAG_LAM, size⟩ := by
  intro pre rest value st' h
  change (getLamRun recur size.toNat).run ⟨pre ++ rest, pre.size⟩ =
    .ok (value, st') at h
  obtain ⟨suffix, hrest, hstate⟩ :=
    getLamRun_canonical_of recur hrecur size.toNat pre rest h
  obtain ⟨u, ty, body, hvalue, hcount⟩ :=
    getLamRun_success_count recur size.toNat
      ⟨pre ++ rest, pre.size⟩ h
  subst value
  have hsize : (body.lamCount + 1).toUInt64 = size := by
    change (Expr.lamCount (.lam u ty body)).toUInt64 = size
    rw [hcount]
    exact UInt64.ofNat_toNat
  exact ⟨lamTailBytes (.lam u ty body), suffix, hrest,
    by simp [exprBytes, lamTailBytes, hsize, ByteArray.append_assoc], hstate⟩

theorem getExprTag_all_canonical (recur : GetM Expr)
    (hrecur : GetCanonical recur exprBytes) (size : UInt64) :
    ExprTagCanonical recur ⟨Expr.FLAG_ALL, size⟩ := by
  intro pre rest value st' h
  change (getAllRun recur size.toNat).run ⟨pre ++ rest, pre.size⟩ =
    .ok (value, st') at h
  obtain ⟨suffix, hrest, hstate⟩ :=
    getAllRun_canonical_of recur hrecur size.toNat pre rest h
  obtain ⟨u, o, ty, body, hvalue, hcount⟩ :=
    getAllRun_success_count recur size.toNat
      ⟨pre ++ rest, pre.size⟩ h
  subst value
  have hsize : (body.allCount + 1).toUInt64 = size := by
    change (Expr.allCount (.all u o ty body)).toUInt64 = size
    rw [hcount]
    exact UInt64.ofNat_toNat
  exact ⟨allTailBytes (.all u o ty body), suffix, hrest,
    by simp [exprBytes, allTailBytes, hsize, ByteArray.append_assoc], hstate⟩

theorem getExprTag_canonical_of (recur : GetM Expr)
    (hrecur : GetCanonical recur exprBytes) (tag : Tag4) :
    ExprTagCanonical recur tag := by
  rcases tag with ⟨flag, size⟩
  intro pre rest value st' h
  by_cases h0 : flag = 0
  · subst flag
    simp [getExprTag] at h
    cases h
    exact ⟨ByteArray.empty, rest, by simp,
      by simp [exprBytes, Expr.FLAG_SORT], by simp⟩
  by_cases h1 : flag = 1
  · subst flag
    simp [getExprTag] at h
    cases h
    exact ⟨ByteArray.empty, rest, by simp,
      by simp [exprBytes, Expr.FLAG_VAR], by simp⟩
  by_cases h2 : flag = 2
  · subst flag
    exact getExprTag_ref_canonical recur size pre rest h
  by_cases h3 : flag = 3
  · subst flag
    exact getExprTag_recur_canonical recur size pre rest h
  by_cases h4 : flag = 4
  · subst flag
    exact getExprTag_prj_canonical recur hrecur size pre rest h
  by_cases h5 : flag = 5
  · subst flag
    simp [getExprTag] at h
    cases h
    exact ⟨ByteArray.empty, rest, by simp,
      by simp [exprBytes, Expr.FLAG_STR], by simp⟩
  by_cases h6 : flag = 6
  · subst flag
    simp [getExprTag] at h
    cases h
    exact ⟨ByteArray.empty, rest, by simp,
      by simp [exprBytes, Expr.FLAG_NAT], by simp⟩
  by_cases h7 : flag = 7
  · subst flag
    exact getExprTag_app_canonical recur hrecur size pre rest h
  by_cases h8 : flag = 8
  · subst flag
    exact getExprTag_lam_canonical recur hrecur size pre rest h
  by_cases h9 : flag = 9
  · subst flag
    exact getExprTag_all_canonical recur hrecur size pre rest h
  by_cases h10 : flag = 10
  · subst flag
    by_cases hsize : size > 1
    · simp [getExprTag, hsize] at h
      change (Except.error _) = Except.ok (value, st') at h
      contradiction
    · exact getExprTag_let_canonical recur hrecur size hsize pre rest h
  by_cases h11 : flag = 11
  · subst flag
    simp [getExprTag] at h
    cases h
    exact ⟨ByteArray.empty, rest, by simp,
      by simp [exprBytes, Expr.FLAG_SHARE], by simp⟩
  · simp [getExprTag] at h
    change (Except.error _) = Except.ok (value, st') at h
    contradiction

theorem getExprFuel_canonical (fuel : Nat) :
    GetCanonical (getExprFuel fuel) exprBytes := by
  induction fuel with
  | zero =>
    intro pre rest value st' h
    simp [getExprFuel] at h
    change (Except.error _) = Except.ok (value, st') at h
    contradiction
  | succ fuel ih =>
    intro pre rest value st' h
    simp only [getExprFuel, StateT.run_bind] at h
    cases ht : getTag4.run ⟨pre ++ rest, pre.size⟩ with
    | error err =>
      rw [ht] at h
      contradiction
    | ok tagState =>
      rcases tagState with ⟨tag, afterTag⟩
      rw [ht] at h
      simp only [bind, Except.bind] at h
      obtain ⟨afterTagBytes, hrestTag, hafterTag⟩ :=
        getTag4_canonical pre rest ht
      let tagPre := pre ++ tag4Bytes tag
      have hafterTag' :
          afterTag = ⟨tagPre ++ afterTagBytes, tagPre.size⟩ := by
        rw [hafterTag]
        simp [tagPre, hrestTag, ByteArray.append_assoc]
      rw [hafterTag'] at h
      obtain ⟨payload, suffix, hrestPayload, hencoding, hstate⟩ :=
        getExprTag_canonical_of (getExprFuel fuel) ih tag
          tagPre afterTagBytes h
      refine ⟨suffix, ?_, ?_⟩
      · calc
          rest = tag4Bytes tag ++ afterTagBytes := hrestTag
          _ = (tag4Bytes tag ++ payload) ++ suffix := by
            rw [hrestPayload]
            simp [ByteArray.append_assoc]
          _ = exprBytes value ++ suffix := by rw [hencoding]
      · simpa [tagPre, hrestTag, hrestPayload, ← hencoding,
          ByteArray.append_assoc, ByteArray.size_append,
          Nat.add_assoc] using hstate

theorem getExpr_canonical : GetCanonical getExpr exprBytes := by
  intro pre rest value st' h
  have hfuel : (pre ++ rest).size - pre.size + 1 = rest.size + 1 := by
    simp [ByteArray.size_append]
  change (getExprFuel ((pre ++ rest).size - pre.size + 1)).run
    ⟨pre ++ rest, pre.size⟩ = .ok (value, st') at h
  rw [hfuel] at h
  exact getExprFuel_canonical (rest.size + 1) pre rest h

theorem canonicalLaw : CanonicalLaw Expr := by
  intro input value h
  change runGet getExpr input = .ok value at h
  change runPut (putExpr value) = input
  rw [runPut_eq_of_spec (putExpr_spec value)]
  simp only [runGet] at h
  cases hg : getExpr.run ⟨input, 0⟩ with
  | error err =>
    rw [hg] at h
    contradiction
  | ok result =>
    rcases result with ⟨decoded, st⟩
    rw [hg] at h
    simp only [bind, Except.bind] at h
    obtain ⟨suffix, hinput, hst⟩ :=
      getExpr_canonical ByteArray.empty input hg
    by_cases hfull : st.idx = st.bytes.size
    · simp [hfull] at h
      cases h
      have hsize : (exprBytes value).size = input.size := by
        have hidx := congrArg GetState.idx hst
        have hbytes := congrArg GetState.bytes hst
        simp at hidx hbytes
        rw [hfull, hbytes] at hidx
        exact hidx.symm
      have hsuffix : suffix = ByteArray.empty := by
        have hsizes := congrArg ByteArray.size hinput
        simpa [ByteArray.size_append, hsize] using hsizes
      simpa [hsuffix] using hinput.symm
    · simp [hfull] at h

theorem getExpr_spec (e : Expr) (hwf : e.wireWF) :
    GetSpec getExpr (exprBytes e) e := by
  intro pre suffix
  let fuel := (pre ++ exprBytes e ++ suffix).size - pre.size + 1
  have hfuel : (exprBytes e).size < fuel := by
    dsimp [fuel]
    simp only [ByteArray.size_append]
    omega
  have hspec := getFuel_expr_spec e fuel hwf hfuel
  have hrun := hspec pre suffix
  change (getExprFuel fuel).run
    ⟨pre ++ exprBytes e ++ suffix, pre.size⟩ = _ at hrun
  simpa [getExpr, fuel, ByteArray.size_append] using hrun

end ExprLaws

namespace Expr

/-- Roundtrip holds on exactly the recursively count-representable expression
domain. Unbounded Lean `Nat` counts outside this domain cannot fit v2's u64
headers. -/
def RoundtripLaw : Prop :=
  ∀ e : Expr, e.wireWF → de (ser e) = .ok e

theorem roundtripLaw : RoundtripLaw := by
  intro e hwf
  change runGet getExpr (runPut (putExpr e)) = .ok e
  rw [runPut_eq_of_spec (putExpr_spec e)]
  exact runGet_eq_ok_of_spec (ExprLaws.getExpr_spec e hwf)

/-- Every accepted expression byte string is its unique canonical encoding. -/
theorem canonicalLaw : Ixon.CanonicalLaw Expr :=
  ExprLaws.canonicalLaw

end Expr

/-! Elaboration-time roundtrip and canonicity checks. -/

private def roundtrips (e : Expr) : Bool :=
  match (de (ser e) : Except String Expr) with
  | .ok e' => e' == e
  | .error _ => false

#guard roundtrips (.sort 0)
#guard roundtrips (.var 300)
#guard roundtrips (.ref 1 #[0, 2, 200])
#guard roundtrips (.recur 2 #[1])
#guard roundtrips (.prj 3 1 (.var 0))
#guard roundtrips (.str 5)
#guard roundtrips (.nat 7)
#guard roundtrips (.share 12)
#guard roundtrips (.lam .linear (.sort 0) (.var 0))
#guard roundtrips (.lam .many (.sort 0) (.lam .erased (.sort 1) (.var 1)))
#guard roundtrips
  (.all .many .shared (.sort 1) (.all .linear .unique (.var 0) (.var 1)))
#guard roundtrips (.app (.app (.var 0) (.var 1)) (.var 2))
#guard roundtrips (.letE true (.sort 0) (.var 2) (.app (.var 0) (.var 1)))
#guard roundtrips
  (.lam .affine (.all .erased .shared (.sort 0) (.sort 0)) (.share 3))

private def rejects (bytes : Array UInt8) : Bool :=
  match (de (ByteArray.mk bytes) : Except String Expr) with
  | .ok _ => false
  | .error _ => true

-- empty lam telescope (LAM tag, count 0, then var 0)
#guard rejects #[0x80, 0x10]
-- lam mode byte out of range (LAM count 1, mode 0x04, sort 0, var 0)
#guard rejects #[0x81, 0x04, 0x00, 0x10]
-- all mode byte out of range (ALL count 1, mode 0x08, sort 0, var 0)
#guard rejects #[0x91, 0x08, 0x00, 0x10]
-- non-minimal var size (large form for a size that fits small form)
#guard rejects #[0x18, 0x05]
-- letE with nonDep flag 2
#guard rejects #[0xA2, 0x00, 0x10, 0x10]
-- trailing bytes after a complete term
#guard rejects #[0x10, 0x10]

end Ix.Compiler.Ixon
