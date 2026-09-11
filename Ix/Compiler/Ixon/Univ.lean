import Ix.Compiler.Ixon.Serialize

/-!
# Universe levels

Unchanged from ix's Ixon — the v2 codec for `Univ` is byte-identical
(only `Expr` rolls in v2), modulo the strict-decoding discipline from
`Serialize` plus telescope canonicity: a run-length-encoded succ chain
must be maximal, so a decoded succ base may not itself be a succ. Recursive
decoding is bounded by remaining input, and a single compressed succ run is
limited before allocation; `getUniv_bounded` exposes the proved invariant.
-/

namespace Ix.Compiler.Ixon

/-- Universe levels for Lean's type system. -/
inductive Univ where
  | zero : Univ
  | succ : Univ → Univ
  | max : Univ → Univ → Univ
  | imax : Univ → Univ → Univ
  | var : UInt64 → Univ
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

namespace Univ

def FLAG_ZERO_SUCC : UInt8 := 0
def FLAG_MAX : UInt8 := 1
def FLAG_IMAX : UInt8 := 2
def FLAG_VAR : UInt8 := 3

/-- Build exactly `n` successors around a base. -/
def addSucc : Nat → Univ → Univ
  | 0, u => u
  | n + 1, u => addSucc n (.succ u)

/-- Maximum constructor depth, used as the structural termination measure. -/
def codecDepth : Univ → Nat
  | .zero | .var _ => 1
  | .succ u => u.codecDepth + 1
  | .max a b | .imax a b => a.codecDepth + b.codecDepth + 1

end Univ

/-- A single RLE header may expand to at most this many `.succ` nodes.
Longer source runs are uniquely split into nested full chunks. Without a
per-header bound, nine hostile bytes can request `UInt64.max` heap cells. -/
def maxSuccExpansion : Nat := 4096

mutual
  /-- Canonical universe bytes. Keeping the structural encoder pure makes its
  exact output available to both the writer specification and decoder proof. -/
  def univBytes : Univ → ByteArray
    | .zero => tag2Bytes ⟨Univ.FLAG_ZERO_SUCC, 0⟩
    | .succ u => univSuccBytes 1 u
    | .max a b =>
      tag2Bytes ⟨Univ.FLAG_MAX, 0⟩ ++ univBytes a ++ univBytes b
    | .imax a b =>
      tag2Bytes ⟨Univ.FLAG_IMAX, 0⟩ ++ univBytes a ++ univBytes b
    | .var idx => tag2Bytes ⟨Univ.FLAG_VAR, idx⟩
  termination_by u => (u.codecDepth, 0)
  decreasing_by
    all_goals apply Prod.Lex.left <;> simp [Univ.codecDepth] <;> omega

  /-- Accumulate one maximal successor run, then encode its base. -/
  def univSuccBytes (count : Nat) : Univ → ByteArray
    | current@(.succ u) =>
      if count == maxSuccExpansion then
        tag2Bytes ⟨Univ.FLAG_ZERO_SUCC, count.toUInt64⟩ ++
          univBytes current
      else
        univSuccBytes (count + 1) u
    | base =>
      tag2Bytes ⟨Univ.FLAG_ZERO_SUCC, count.toUInt64⟩ ++ univBytes base
  termination_by u => (u.codecDepth, 1)
  decreasing_by
    all_goals subst_vars
    all_goals first
      | apply Prod.Lex.left <;> simp [Univ.codecDepth] <;> omega
      | apply Prod.Lex.right <;> omega
end

/-- Total universe writer. -/
def putUniv (u : Univ) : PutM Unit :=
  putBytes (univBytes u)

theorem putUniv_spec (u : Univ) : PutSpec (putUniv u) (univBytes u) := by
  exact putBytes_spec _

/-- Every decoded succ run is bounded, recursively through max/imax. -/
inductive SuccBounded (limit : Nat) : Univ → Prop where
  | zero : SuccBounded limit .zero
  | var (idx : UInt64) : SuccBounded limit (.var idx)
  | succRun (n : Nat) (base : Univ) : n ≤ limit → SuccBounded limit base →
      SuccBounded limit (Univ.addSucc n base)
  | max {a b : Univ} : SuccBounded limit a → SuccBounded limit b →
      SuccBounded limit (.max a b)
  | imax {a b : Univ} : SuccBounded limit a → SuccBounded limit b →
      SuccBounded limit (.imax a b)

/-- A decoded universe paired with the resource invariant established by
the decoder that built it. -/
structure DecodedUniv (limit : Nat) where
  value : Univ
  bounded : SuccBounded limit value

/-- Interpret one already-decoded universe header. `recur` is the recursive
decoder at the next-smaller fuel; naming this nonrecursive continuation keeps
the executable definition and its compositional proof boundary aligned. -/
def getUnivSucc (recur : GetM (DecodedUniv maxSuccExpansion))
    (count : Nat) (hcount : count ≤ maxSuccExpansion) :
    GetM (DecodedUniv maxSuccExpansion) := do
  let base ← recur
  match base.value with
  | .succ _ =>
    if count = maxSuccExpansion then
      return ⟨Univ.addSucc count base.value,
        .succRun count base.value hcount base.bounded⟩
    else
      throw "getUniv: non-canonical short succ chunk"
  | _ =>
    return ⟨Univ.addSucc count base.value,
      .succRun count base.value hcount base.bounded⟩

def getUnivTag (recur : GetM (DecodedUniv maxSuccExpansion))
    (tag : Tag2) : GetM (DecodedUniv maxSuccExpansion) :=
  match tag.flag with
  | 0 => do
    if tag.size == 0 then
      return ⟨.zero, .zero⟩
    else if hn : tag.size.toNat ≤ maxSuccExpansion then
      getUnivSucc recur tag.size.toNat hn
    else
      throw s!"getUniv: succ expansion {tag.size} exceeds limit {maxSuccExpansion}"
  | 1 => do
    if tag.size != 0 then throw s!"getUniv: non-canonical max size {tag.size}"
    let a ← recur
    let b ← recur
    return ⟨.max a.value b.value, .max a.bounded b.bounded⟩
  | 2 => do
    if tag.size != 0 then throw s!"getUniv: non-canonical imax size {tag.size}"
    let a ← recur
    let b ← recur
    return ⟨.imax a.value b.value, .imax a.bounded b.bounded⟩
  | 3 => return ⟨.var tag.size, .var tag.size⟩
  | f => throw s!"getUniv: invalid flag {f}"

def getUnivFuel : Nat → GetM (DecodedUniv maxSuccExpansion)
  | 0 => throw "getUniv: recursion limit"
  | fuel + 1 => do
    let tag ← getTag2
    getUnivTag (getUnivFuel fuel) tag

def getUnivCertified : GetM (DecodedUniv maxSuccExpansion) := do
  let st ← get
  getUnivFuel (st.bytes.size - st.idx + 1)

def getUniv : GetM Univ := fun st =>
  match getUnivCertified st with
  | .error err => .error err
  | .ok (decoded, st') => .ok (decoded.value, st')

/-- Every successful public decode satisfies the recursive succ-expansion
bound. The proof is carried by `getUnivCertified`, then erased from the API. -/
theorem getUniv_bounded {st st' : GetState} {u : Univ}
    (h : getUniv.run st = .ok (u, st')) :
    SuccBounded maxSuccExpansion u := by
  change getUniv st = .ok (u, st') at h
  unfold getUniv at h
  cases hc : getUnivCertified st with
  | error err => rw [hc] at h; contradiction
  | ok result =>
    rcases result with ⟨decoded, st''⟩
    rw [hc] at h
    cases h
    exact decoded.bounded

instance : Serialize Univ where
  put := putUniv
  get := getUniv

/-! Elaboration-time roundtrip and canonicity checks. -/

private def univRoundtrips (u : Univ) : Bool :=
  match (de (ser u) : Except String Univ) with
  | .ok u' => u' == u
  | .error _ => false

#guard univRoundtrips .zero
#guard univRoundtrips (.succ (.succ .zero))
#guard univRoundtrips (.succ (.max (.var 0) (.var 1)))
#guard univRoundtrips (.max (.var 0) (.succ (.var 1)))
#guard univRoundtrips (.imax .zero (.var 40))

private def chunkedSucc : Univ :=
  Univ.addSucc (maxSuccExpansion + 1) .zero

-- The boundary is canonical: one full chunk, then a final run of one.
#guard ser chunkedSucc == ByteArray.mk #[0x21, 0x00, 0x10, 0x01, 0x00]
#guard univRoundtrips chunkedSucc

private def univRejects (bytes : Array UInt8) : Bool :=
  match (de (ByteArray.mk bytes) : Except String Univ) with
  | .ok _ => false
  | .error _ => true

-- succ(size 1) over a base that is itself an encoded succ: non-canonical
#guard univRejects #[0x01, 0x01, 0x00]

-- max/imax with a nonzero size field: non-canonical (the encoder always
-- writes 0; accepting other sizes would split one value across addresses)
#guard univRejects #[0x41, 0x00, 0x00]        -- max, small-form size 1
#guard univRejects #[0x81, 0x00, 0x00]        -- imax, small-form size 1
#guard univRejects #[0x60, 0x20, 0x00, 0x00]  -- max, large-form size 32

private def oversizedSucc : ByteArray := runPut do
  putTag2 ⟨Univ.FLAG_ZERO_SUCC, (maxSuccExpansion + 1).toUInt64⟩
  putTag2 ⟨Univ.FLAG_ZERO_SUCC, 0⟩

-- The RLE count is rejected before allocating any successor nodes.
#guard (match (de oversizedSucc : Except String Univ) with
  | .error msg => msg == s!"getUniv: succ expansion {maxSuccExpansion + 1} exceeds limit {maxSuccExpansion}"
  | .ok _ => false)

namespace UnivLaws

local notation "bytes" => univBytes
local notation "succBytes" => univSuccBytes

attribute [local simp] univBytes.eq_1 univBytes.eq_2 univBytes.eq_3
  univBytes.eq_4 univBytes.eq_5 univSuccBytes.eq_1 univSuccBytes.eq_2

theorem tag2Bytes_size_pos (t : Tag2) : 0 < (tag2Bytes t).size := by
  simp only [tag2Bytes]
  split
  · simp [u8Bytes]
  · simp [u8Bytes, ByteArray.size_append]
    omega

theorem getFuel_zero_spec (fuel : Nat)
    (hfuel : (bytes .zero).size < fuel) :
    GetSpec (getUnivFuel fuel) (bytes .zero)
      ⟨.zero, SuccBounded.zero⟩ := by
  cases fuel with
  | zero => simp at hfuel
  | succ fuel =>
    intro pre suffix
    simp [getUnivFuel, StateT.run_bind]
    rw [getTag2_encoded_spec ⟨Univ.FLAG_ZERO_SUCC, 0⟩ (by decide) pre suffix]
    simp [Univ.FLAG_ZERO_SUCC]
    rfl

theorem getFuel_var_spec (idx : UInt64) (fuel : Nat)
    (hfuel : (bytes (.var idx)).size < fuel) :
    GetSpec (getUnivFuel fuel) (bytes (.var idx))
      ⟨.var idx, SuccBounded.var idx⟩ := by
  cases fuel with
  | zero => simp at hfuel
  | succ fuel =>
    intro pre suffix
    simp [getUnivFuel, StateT.run_bind]
    rw [getTag2_encoded_spec ⟨Univ.FLAG_VAR, idx⟩
      (by simp [Univ.FLAG_VAR]) pre suffix]
    simp [Univ.FLAG_VAR]
    rfl

theorem getFuel_max_of_specs (a b : Univ) (fuel : Nat)
    {haBound : SuccBounded maxSuccExpansion a}
    {hbBound : SuccBounded maxSuccExpansion b}
    (ha : GetSpec (getUnivFuel fuel) (bytes a) ⟨a, haBound⟩)
    (hb : GetSpec (getUnivFuel fuel) (bytes b) ⟨b, hbBound⟩) :
    GetSpec (getUnivFuel (fuel + 1)) (bytes (.max a b))
      ⟨.max a b, .max haBound hbBound⟩ := by
  let finish : DecodedUniv maxSuccExpansion →
      GetM (DecodedUniv maxSuccExpansion) := fun decoded =>
    pure ⟨.max a decoded.value, .max haBound decoded.bounded⟩
  have hfinish : GetSpec (finish ⟨b, hbBound⟩) ByteArray.empty
      ⟨.max a b, .max haBound hbBound⟩ := by
    simpa [finish] using GetSpec.pure
      (DecodedUniv.mk (.max a b) (.max haBound hbBound))
  have hright := GetSpec.bind (next := finish) hb hfinish
  simp only [ByteArray.append_empty] at hright
  let afterLeft : DecodedUniv maxSuccExpansion →
      GetM (DecodedUniv maxSuccExpansion) := fun decoded => do
    let right ← getUnivFuel fuel
    return ⟨.max decoded.value right.value,
      .max decoded.bounded right.bounded⟩
  have hafterLeft : GetSpec (afterLeft ⟨a, haBound⟩) (bytes b)
      ⟨.max a b, .max haBound hbBound⟩ := by
    simpa [afterLeft, finish] using hright
  have hchildren := GetSpec.bind (next := afterLeft) ha hafterLeft
  have htag := getTag2_encoded_spec ⟨Univ.FLAG_MAX, 0⟩
    (by simp [Univ.FLAG_MAX])
  have hcontinuation :
      GetSpec
        (getUnivTag (getUnivFuel fuel) ⟨Univ.FLAG_MAX, 0⟩)
        (bytes a ++ bytes b)
        ⟨.max a b, .max haBound hbBound⟩ := by
    simpa [getUnivTag, Univ.FLAG_MAX, afterLeft] using hchildren
  have htotal := GetSpec.bind
    (next := getUnivTag (getUnivFuel fuel)) htag hcontinuation
  simpa [getUnivFuel, ByteArray.append_assoc] using htotal

theorem getFuel_imax_of_specs (a b : Univ) (fuel : Nat)
    {haBound : SuccBounded maxSuccExpansion a}
    {hbBound : SuccBounded maxSuccExpansion b}
    (ha : GetSpec (getUnivFuel fuel) (bytes a) ⟨a, haBound⟩)
    (hb : GetSpec (getUnivFuel fuel) (bytes b) ⟨b, hbBound⟩) :
    GetSpec (getUnivFuel (fuel + 1)) (bytes (.imax a b))
      ⟨.imax a b, .imax haBound hbBound⟩ := by
  let finish : DecodedUniv maxSuccExpansion →
      GetM (DecodedUniv maxSuccExpansion) := fun decoded =>
    pure ⟨.imax a decoded.value, .imax haBound decoded.bounded⟩
  have hfinish : GetSpec (finish ⟨b, hbBound⟩) ByteArray.empty
      ⟨.imax a b, .imax haBound hbBound⟩ := by
    simpa [finish] using GetSpec.pure
      (DecodedUniv.mk (.imax a b) (.imax haBound hbBound))
  have hright := GetSpec.bind (next := finish) hb hfinish
  simp only [ByteArray.append_empty] at hright
  let afterLeft : DecodedUniv maxSuccExpansion →
      GetM (DecodedUniv maxSuccExpansion) := fun decoded => do
    let right ← getUnivFuel fuel
    return ⟨.imax decoded.value right.value,
      .imax decoded.bounded right.bounded⟩
  have hafterLeft : GetSpec (afterLeft ⟨a, haBound⟩) (bytes b)
      ⟨.imax a b, .imax haBound hbBound⟩ := by
    simpa [afterLeft, finish] using hright
  have hchildren := GetSpec.bind (next := afterLeft) ha hafterLeft
  have htag := getTag2_encoded_spec ⟨Univ.FLAG_IMAX, 0⟩
    (by simp [Univ.FLAG_IMAX])
  have hcontinuation :
      GetSpec
        (getUnivTag (getUnivFuel fuel) ⟨Univ.FLAG_IMAX, 0⟩)
        (bytes a ++ bytes b)
        ⟨.imax a b, .imax haBound hbBound⟩ := by
    simpa [getUnivTag, Univ.FLAG_IMAX, afterLeft] using hchildren
  have htotal := GetSpec.bind
    (next := getUnivTag (getUnivFuel fuel)) htag hcontinuation
  simpa [getUnivFuel, ByteArray.append_assoc] using htotal

def SuccChunkCanonical (count : Nat) : Univ → Prop
  | .succ _ => count = maxSuccExpansion
  | _ => True

theorem toUInt64_toNat_of_le_limit (count : Nat)
    (hle : count ≤ maxSuccExpansion) : count.toUInt64.toNat = count := by
  change count % 18446744073709551616 = count
  apply Nat.mod_eq_of_lt
  simp [maxSuccExpansion] at hle
  omega

theorem getUnivSucc_of_spec (count : Nat) (base : Univ) (fuel : Nat)
    (hle : count ≤ maxSuccExpansion)
    (hcanonical : SuccChunkCanonical count base)
    {baseBound : SuccBounded maxSuccExpansion base}
    (hbase : GetSpec (getUnivFuel fuel) (bytes base) ⟨base, baseBound⟩) :
    GetSpec (getUnivSucc (getUnivFuel fuel) count hle) (bytes base)
      ⟨Univ.addSucc count base,
        .succRun count base hle baseBound⟩ := by
  let finish : DecodedUniv maxSuccExpansion →
      GetM (DecodedUniv maxSuccExpansion) := fun decoded =>
    match decoded.value with
    | .succ _ =>
      if count = maxSuccExpansion then
        pure ⟨Univ.addSucc count decoded.value,
          .succRun count decoded.value hle decoded.bounded⟩
      else
        throw "getUniv: non-canonical short succ chunk"
    | _ =>
      pure ⟨Univ.addSucc count decoded.value,
        .succRun count decoded.value hle decoded.bounded⟩
  have hfinish : GetSpec (finish ⟨base, baseBound⟩) ByteArray.empty
      ⟨Univ.addSucc count base, .succRun count base hle baseBound⟩ := by
    cases base <;>
      simp_all [finish, SuccChunkCanonical] <;>
      exact GetSpec.pure _
  have hparsed := GetSpec.bind (next := finish) hbase hfinish
  simp only [ByteArray.append_empty] at hparsed
  change GetSpec (getUnivFuel fuel >>= finish) (bytes base)
    ⟨Univ.addSucc count base, .succRun count base hle baseBound⟩
  exact hparsed

theorem getFuel_succ_of_spec (count : Nat) (base : Univ) (fuel : Nat)
    (hpos : 0 < count) (hle : count ≤ maxSuccExpansion)
    (hcanonical : SuccChunkCanonical count base)
    {baseBound : SuccBounded maxSuccExpansion base}
    (hbase : GetSpec (getUnivFuel fuel) (bytes base) ⟨base, baseBound⟩) :
    GetSpec (getUnivFuel (fuel + 1))
      (tag2Bytes ⟨Univ.FLAG_ZERO_SUCC, count.toUInt64⟩ ++ bytes base)
      ⟨Univ.addSucc count base,
        .succRun count base hle baseBound⟩ := by
  have hcount := toUInt64_toNat_of_le_limit count hle
  have hsizeNe : count.toUInt64 ≠ 0 := by
    intro hzero
    have := congrArg UInt64.toNat hzero
    simp [hcount] at this
    omega
  have hparsed := getUnivSucc_of_spec count base fuel hle hcanonical hbase
  have hcontinuation :
      GetSpec
        (getUnivTag (getUnivFuel fuel)
          ⟨Univ.FLAG_ZERO_SUCC, count.toUInt64⟩)
        (bytes base)
        ⟨Univ.addSucc count base,
          .succRun count base hle baseBound⟩ := by
    simpa [getUnivTag, Univ.FLAG_ZERO_SUCC, hcount, hsizeNe, hle,
      getUnivSucc] using hparsed
  have htag := getTag2_encoded_spec
    ⟨Univ.FLAG_ZERO_SUCC, count.toUInt64⟩
    (by simp [Univ.FLAG_ZERO_SUCC])
  have htotal := GetSpec.bind
    (next := getUnivTag (getUnivFuel fuel)) htag hcontinuation
  simpa [getUnivFuel, ByteArray.append_assoc] using htotal

@[simp] theorem addSucc_one (u : Univ) : Univ.addSucc 1 u = .succ u := rfl

theorem addSucc_succ (count : Nat) (u : Univ) :
    Univ.addSucc count (.succ u) = Univ.addSucc (count + 1) u := by
  induction count with
  | zero => rfl
  | succ count ih => simp [Univ.addSucc]

mutual
  theorem getFuel_bytes_spec (u : Univ) (fuel : Nat)
      (hfuel : (bytes u).size < fuel) :
      ∃ bounded : SuccBounded maxSuccExpansion u,
        GetSpec (getUnivFuel fuel) (bytes u) ⟨u, bounded⟩ := by
    cases u with
    | zero =>
      exact ⟨.zero, getFuel_zero_spec fuel hfuel⟩
    | succ u =>
      have h := getFuel_succBytes_spec 1 u (by omega)
        (by simp [maxSuccExpansion]) fuel (by simpa using hfuel)
      simpa using h
    | max a b =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel =>
        have htag := tag2Bytes_size_pos ⟨Univ.FLAG_MAX, 0⟩
        have haFuel : (bytes a).size < fuel := by
          simp only [univBytes.eq_3, ByteArray.size_append] at hfuel
          omega
        have hbFuel : (bytes b).size < fuel := by
          simp only [univBytes.eq_3, ByteArray.size_append] at hfuel
          omega
        obtain ⟨haBound, ha⟩ := getFuel_bytes_spec a fuel haFuel
        obtain ⟨hbBound, hb⟩ := getFuel_bytes_spec b fuel hbFuel
        exact ⟨.max haBound hbBound, getFuel_max_of_specs a b fuel ha hb⟩
    | imax a b =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel =>
        have htag := tag2Bytes_size_pos ⟨Univ.FLAG_IMAX, 0⟩
        have haFuel : (bytes a).size < fuel := by
          simp only [univBytes.eq_4, ByteArray.size_append] at hfuel
          omega
        have hbFuel : (bytes b).size < fuel := by
          simp only [univBytes.eq_4, ByteArray.size_append] at hfuel
          omega
        obtain ⟨haBound, ha⟩ := getFuel_bytes_spec a fuel haFuel
        obtain ⟨hbBound, hb⟩ := getFuel_bytes_spec b fuel hbFuel
        exact ⟨.imax haBound hbBound, getFuel_imax_of_specs a b fuel ha hb⟩
    | var idx =>
      exact ⟨.var idx, getFuel_var_spec idx fuel hfuel⟩
  termination_by (u.codecDepth, 0)
  decreasing_by
    all_goals subst_vars
    all_goals first
      | apply Prod.Lex.left <;> simp [Univ.codecDepth] <;> omega
      | apply Prod.Lex.right <;> omega

  theorem getFuel_succBytes_spec (count : Nat) (u : Univ)
      (hpos : 0 < count) (hle : count ≤ maxSuccExpansion)
      (fuel : Nat) (hfuel : (succBytes count u).size < fuel) :
      ∃ bounded : SuccBounded maxSuccExpansion (Univ.addSucc count u),
        GetSpec (getUnivFuel fuel) (succBytes count u)
          ⟨Univ.addSucc count u, bounded⟩ := by
    cases u with
    | succ u =>
      by_cases hfull : count = maxSuccExpansion
      · subst count
        cases fuel with
        | zero => simp at hfuel
        | succ fuel =>
          have htag : 0 < (tag2Bytes
              ⟨Univ.FLAG_ZERO_SUCC, UInt64.ofNat maxSuccExpansion⟩).size :=
            tag2Bytes_size_pos _
          have hbaseFuel : (bytes (.succ u)).size < fuel := by
            rw [univBytes.eq_2]
            simp [ByteArray.size_append] at hfuel
            omega
          obtain ⟨baseBound, hbase⟩ :=
            getFuel_bytes_spec (.succ u) fuel hbaseFuel
          have hparse := getFuel_succ_of_spec maxSuccExpansion (.succ u)
            fuel hpos hle
            (by simp [SuccChunkCanonical]) hbase
          exact ⟨.succRun maxSuccExpansion (.succ u) hle baseBound,
            by simpa using hparse⟩
      · have hle' : count + 1 ≤ maxSuccExpansion := by omega
        have hrec := getFuel_succBytes_spec (count + 1) u (by omega) hle'
          fuel (by simpa [hfull] using hfuel)
        simpa [hfull, addSucc_succ] using hrec
    | zero =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel =>
        have htag := tag2Bytes_size_pos
          ⟨Univ.FLAG_ZERO_SUCC, count.toUInt64⟩
        have hbaseFuel : (bytes .zero).size < fuel := by
          simp only [univSuccBytes.eq_2, ByteArray.size_append] at hfuel
          omega
        obtain ⟨baseBound, hbase⟩ := getFuel_bytes_spec .zero fuel hbaseFuel
        exact ⟨.succRun count .zero hle baseBound,
          by simpa using
            getFuel_succ_of_spec count .zero fuel hpos hle (by trivial) hbase⟩
    | max a b =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel =>
        have htag := tag2Bytes_size_pos
          ⟨Univ.FLAG_ZERO_SUCC, count.toUInt64⟩
        have hbaseFuel : (bytes (.max a b)).size < fuel := by
          simp only [univSuccBytes.eq_2, ByteArray.size_append] at hfuel
          omega
        obtain ⟨baseBound, hbase⟩ :=
          getFuel_bytes_spec (.max a b) fuel hbaseFuel
        exact ⟨.succRun count (.max a b) hle baseBound,
          by simpa using
            getFuel_succ_of_spec count (.max a b) fuel hpos hle (by trivial) hbase⟩
    | imax a b =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel =>
        have htag := tag2Bytes_size_pos
          ⟨Univ.FLAG_ZERO_SUCC, count.toUInt64⟩
        have hbaseFuel : (bytes (.imax a b)).size < fuel := by
          simp only [univSuccBytes.eq_2, ByteArray.size_append] at hfuel
          omega
        obtain ⟨baseBound, hbase⟩ :=
          getFuel_bytes_spec (.imax a b) fuel hbaseFuel
        exact ⟨.succRun count (.imax a b) hle baseBound,
          by simpa using
            getFuel_succ_of_spec count (.imax a b) fuel hpos hle (by trivial) hbase⟩
    | var idx =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel =>
        have htag := tag2Bytes_size_pos
          ⟨Univ.FLAG_ZERO_SUCC, count.toUInt64⟩
        have hbaseFuel : (bytes (.var idx)).size < fuel := by
          simp only [univSuccBytes.eq_2, ByteArray.size_append] at hfuel
          omega
        obtain ⟨baseBound, hbase⟩ :=
          getFuel_bytes_spec (.var idx) fuel hbaseFuel
        exact ⟨.succRun count (.var idx) hle baseBound,
          by simpa using
            getFuel_succ_of_spec count (.var idx) fuel hpos hle (by trivial) hbase⟩
  termination_by (u.codecDepth, 1)
  decreasing_by
    all_goals subst_vars
    all_goals first
      | apply Prod.Lex.left <;> simp [Univ.codecDepth] <;> omega
      | apply Prod.Lex.right <;> omega
end

theorem allBounded (u : Univ) : SuccBounded maxSuccExpansion u := by
  induction u with
  | zero => exact .zero
  | succ u ih =>
    simpa using SuccBounded.succRun 1 u (by simp [maxSuccExpansion]) ih
  | max a b ha hb => exact .max ha hb
  | imax a b ha hb => exact .imax ha hb
  | var idx => exact .var idx

theorem getCertified_spec (u : Univ) :
    GetSpec getUnivCertified (bytes u) ⟨u, allBounded u⟩ := by
  intro pre suffix
  let fuel := (pre ++ bytes u ++ suffix).size - pre.size + 1
  have hfuel : (bytes u).size < fuel := by
    dsimp [fuel]
    simp only [ByteArray.size_append]
    omega
  obtain ⟨bounded, hspec⟩ := getFuel_bytes_spec u fuel hfuel
  have hrun := hspec pre suffix
  change (getUnivFuel fuel).run
    ⟨pre ++ bytes u ++ suffix, pre.size⟩ = _
  simpa [fuel] using hrun

theorem getUniv_spec (u : Univ) : GetSpec getUniv (bytes u) u := by
  intro pre suffix
  have h := getCertified_spec u pre suffix
  change getUniv ⟨pre ++ bytes u ++ suffix, pre.size⟩ = _
  unfold getUniv
  change getUnivCertified ⟨pre ++ bytes u ++ suffix, pre.size⟩ = _ at h
  rw [h]

/-! ## Canonical decoding

The converse proof follows arbitrary successful parses. Each reader exposes
the canonical prefix it consumed; recursive universe cases compose those
prefixes and strict top-level consumption rules out a residual suffix. -/

theorem univBytes_addSucc_eq_succBytes (count : Nat) (base : Univ)
    (hpos : 0 < count) (hle : count ≤ maxSuccExpansion) :
    univBytes (Univ.addSucc count base) = univSuccBytes count base := by
  induction count generalizing base with
  | zero => omega
  | succ count ih =>
    cases count with
    | zero => simp [Univ.addSucc]
    | succ count =>
      rw [Univ.addSucc]
      rw [ih (.succ base) (by omega) (by omega)]
      rw [univSuccBytes.eq_1]
      simp only [show ¬(count + 1 == maxSuccExpansion) = true by
        simp [maxSuccExpansion] at hle ⊢; omega, Bool.false_eq_true,
        if_false]

theorem univSuccBytes_canonical (count : Nat) (base : Univ)
    (hcanonical : UnivLaws.SuccChunkCanonical count base) :
    univSuccBytes count base =
      tag2Bytes ⟨Univ.FLAG_ZERO_SUCC, count.toUInt64⟩ ++ univBytes base := by
  cases base with
  | succ u =>
    simp only [UnivLaws.SuccChunkCanonical] at hcanonical
    subst count
    rw [univSuccBytes.eq_1]
    simp
  | zero | max | imax | var =>
    exact univSuccBytes.eq_2 count _ (by intro u h; cases h)

theorem univBytes_addSucc_canonical (count : Nat) (base : Univ)
    (hpos : 0 < count) (hle : count ≤ maxSuccExpansion)
    (hcanonical : UnivLaws.SuccChunkCanonical count base) :
    univBytes (Univ.addSucc count base) =
      tag2Bytes ⟨Univ.FLAG_ZERO_SUCC, count.toUInt64⟩ ++ univBytes base := by
  rw [univBytes_addSucc_eq_succBytes count base hpos hle]
  exact univSuccBytes_canonical count base hcanonical

set_option maxRecDepth 10000 in
theorem getUnivSucc_success_canonical
    (recur : GetM (DecodedUniv maxSuccExpansion)) (count : Nat)
    (hle : count ≤ maxSuccExpansion) (base : DecodedUniv maxSuccExpansion)
    (initial afterBase st' : GetState)
    (decoded : DecodedUniv maxSuccExpansion)
    (hr : recur.run initial = .ok (base, afterBase))
    (h : (getUnivSucc recur count hle).run initial = .ok (decoded, st')) :
    UnivLaws.SuccChunkCanonical count base.value ∧
      decoded.value = Univ.addSucc count base.value ∧ st' = afterBase := by
  unfold getUnivSucc at h
  simp only [StateT.run_bind] at h
  rw [hr] at h
  simp only [bind, Except.bind] at h
  cases hv : base.value with
  | succ u =>
    by_cases hfull : count = maxSuccExpansion
    · simp [hv, hfull] at h
      have hd := congrArg
        (fun result : Except String
            (DecodedUniv maxSuccExpansion × GetState) =>
          match result with
          | .ok (value, _) => value.value
          | .error _ => .zero) h
      have hs := congrArg
        (fun result : Except String
            (DecodedUniv maxSuccExpansion × GetState) =>
          match result with
          | .ok (_, state) => some state
          | .error _ => none) h
      refine ⟨by simpa [UnivLaws.SuccChunkCanonical] using hfull, ?_, ?_⟩
      · exact hd.symm.trans
          (congrArg (fun n => Univ.addSucc n (.succ u)) hfull.symm)
      · change some afterBase = some st' at hs
        exact (Option.some.inj hs).symm
    · simp [hv, hfull] at h
      change (Except.error _) = Except.ok (decoded, st') at h
      contradiction
  | zero | max | imax | var =>
    simp [hv] at h
    cases h
    exact ⟨by simp [UnivLaws.SuccChunkCanonical], rfl, rfl⟩

def UnivTagCanonical
    (recur : GetM (DecodedUniv maxSuccExpansion)) (tag : Tag2) : Prop :=
  ∀ (pre rest : ByteArray) {decoded : DecodedUniv maxSuccExpansion}
      {st' : GetState},
    (getUnivTag recur tag).run ⟨pre ++ rest, pre.size⟩ = .ok (decoded, st') →
    ∃ payload suffix,
      rest = payload ++ suffix ∧
      tag2Bytes tag ++ payload = univBytes decoded.value ∧
      st' = ⟨pre ++ rest, pre.size + payload.size⟩

theorem getUnivTag_canonical_of
    (recur : GetM (DecodedUniv maxSuccExpansion))
    (hrecur : GetCanonical recur (fun decoded => univBytes decoded.value))
    (tag : Tag2) : UnivTagCanonical recur tag := by
  rcases tag with ⟨flag, size⟩
  intro pre rest decoded st' h
  by_cases h0 : flag = 0
  · subst flag
    by_cases hsize0 : size = 0
    · subst size
      simp [getUnivTag] at h
      cases h
      exact ⟨ByteArray.empty, rest, by simp,
        by simp [Univ.FLAG_ZERO_SUCC], by simp⟩
    · by_cases hle : size.toNat ≤ maxSuccExpansion
      · have hsucc :
            (getUnivSucc recur size.toNat hle).run
                ⟨pre ++ rest, pre.size⟩ = .ok (decoded, st') := by
          simpa [getUnivTag, hsize0, hle] using h
        cases hr : recur.run ⟨pre ++ rest, pre.size⟩ with
        | error err =>
          unfold getUnivSucc at hsucc
          simp only [StateT.run_bind] at hsucc
          rw [hr] at hsucc
          contradiction
        | ok baseResult =>
          rcases baseResult with ⟨base, afterBase⟩
          obtain ⟨suffix, hrestBase, hafterBase⟩ :=
            hrecur pre rest hr
          obtain ⟨hcanonical, hvalue, hstate⟩ :=
            getUnivSucc_success_canonical recur size.toNat hle base
              ⟨pre ++ rest, pre.size⟩ afterBase st' decoded hr hsucc
          have hpos : 0 < size.toNat := by
            apply Nat.pos_of_ne_zero
            intro hzero
            have hs := UInt64.ofNat_toNat (x := size)
            rw [hzero] at hs
            exact hsize0 hs.symm
          have hcount : size.toNat.toUInt64 = size := by
            exact UInt64.ofNat_toNat
          refine ⟨univBytes base.value, suffix, hrestBase, ?_, ?_⟩
          · rw [hvalue]
            rw [univBytes_addSucc_canonical size.toNat base.value hpos hle
              hcanonical]
            simp [Univ.FLAG_ZERO_SUCC, hcount]
          · exact hstate.trans hafterBase
      · simp [getUnivTag, hsize0, hle] at h
        change (Except.error _) = Except.ok (decoded, st') at h
        contradiction
  by_cases h1 : flag = 1
  · subst flag
    by_cases hsize0 : size = 0
    · subst size
      let afterLeft : DecodedUniv maxSuccExpansion →
          GetM (DecodedUniv maxSuccExpansion) := fun a => do
        let b ← recur
        return ⟨.max a.value b.value, .max a.bounded b.bounded⟩
      change (recur >>= afterLeft).run ⟨pre ++ rest, pre.size⟩ =
        .ok (decoded, st') at h
      simp only [StateT.run_bind] at h
      cases ha : recur.run ⟨pre ++ rest, pre.size⟩ with
      | error err =>
        rw [ha] at h
        contradiction
      | ok leftResult =>
        rcases leftResult with ⟨a, afterA⟩
        rw [ha] at h
        simp only [bind, Except.bind] at h
        obtain ⟨afterLeftBytes, hrestA, hafterA⟩ :=
          hrecur pre rest ha
        let leftPre := pre ++ univBytes a.value
        have hafterA' :
            afterA = ⟨leftPre ++ afterLeftBytes, leftPre.size⟩ := by
          rw [hafterA]
          simp [leftPre, hrestA, ByteArray.append_assoc]
        rw [hafterA'] at h
        let finish : DecodedUniv maxSuccExpansion →
            GetM (DecodedUniv maxSuccExpansion) := fun b =>
          pure ⟨.max a.value b.value, .max a.bounded b.bounded⟩
        change (recur >>= finish).run
          ⟨leftPre ++ afterLeftBytes, leftPre.size⟩ =
            .ok (decoded, st') at h
        simp only [StateT.run_bind] at h
        cases hb : recur.run
            ⟨leftPre ++ afterLeftBytes, leftPre.size⟩ with
        | error err =>
          rw [hb] at h
          contradiction
        | ok rightResult =>
          rcases rightResult with ⟨b, afterB⟩
          rw [hb] at h
          simp [finish] at h
          cases h
          obtain ⟨suffix, hrestB, hafterB⟩ :=
            hrecur leftPre afterLeftBytes hb
          let payload := univBytes a.value ++ univBytes b.value
          refine ⟨payload, suffix, ?_, ?_, ?_⟩
          · simp [payload, hrestA, hrestB, ByteArray.append_assoc]
          · simp [payload, Univ.FLAG_MAX, ByteArray.append_assoc]
          · simpa [payload, leftPre, hrestA, hrestB,
              ByteArray.append_assoc, ByteArray.size_append, Nat.add_assoc]
              using hafterB
    · simp [getUnivTag, hsize0] at h
      change (Except.error _) = Except.ok (decoded, st') at h
      contradiction
  by_cases h2 : flag = 2
  · subst flag
    by_cases hsize0 : size = 0
    · subst size
      let afterLeft : DecodedUniv maxSuccExpansion →
          GetM (DecodedUniv maxSuccExpansion) := fun a => do
        let b ← recur
        return ⟨.imax a.value b.value, .imax a.bounded b.bounded⟩
      change (recur >>= afterLeft).run ⟨pre ++ rest, pre.size⟩ =
        .ok (decoded, st') at h
      simp only [StateT.run_bind] at h
      cases ha : recur.run ⟨pre ++ rest, pre.size⟩ with
      | error err =>
        rw [ha] at h
        contradiction
      | ok leftResult =>
        rcases leftResult with ⟨a, afterA⟩
        rw [ha] at h
        simp only [bind, Except.bind] at h
        obtain ⟨afterLeftBytes, hrestA, hafterA⟩ :=
          hrecur pre rest ha
        let leftPre := pre ++ univBytes a.value
        have hafterA' :
            afterA = ⟨leftPre ++ afterLeftBytes, leftPre.size⟩ := by
          rw [hafterA]
          simp [leftPre, hrestA, ByteArray.append_assoc]
        rw [hafterA'] at h
        let finish : DecodedUniv maxSuccExpansion →
            GetM (DecodedUniv maxSuccExpansion) := fun b =>
          pure ⟨.imax a.value b.value, .imax a.bounded b.bounded⟩
        change (recur >>= finish).run
          ⟨leftPre ++ afterLeftBytes, leftPre.size⟩ =
            .ok (decoded, st') at h
        simp only [StateT.run_bind] at h
        cases hb : recur.run
            ⟨leftPre ++ afterLeftBytes, leftPre.size⟩ with
        | error err =>
          rw [hb] at h
          contradiction
        | ok rightResult =>
          rcases rightResult with ⟨b, afterB⟩
          rw [hb] at h
          simp [finish] at h
          cases h
          obtain ⟨suffix, hrestB, hafterB⟩ :=
            hrecur leftPre afterLeftBytes hb
          let payload := univBytes a.value ++ univBytes b.value
          refine ⟨payload, suffix, ?_, ?_, ?_⟩
          · simp [payload, hrestA, hrestB, ByteArray.append_assoc]
          · simp [payload, Univ.FLAG_IMAX, ByteArray.append_assoc]
          · simpa [payload, leftPre, hrestA, hrestB,
              ByteArray.append_assoc, ByteArray.size_append, Nat.add_assoc]
              using hafterB
    · simp [getUnivTag, hsize0] at h
      change (Except.error _) = Except.ok (decoded, st') at h
      contradiction
  by_cases h3 : flag = 3
  · subst flag
    simp [getUnivTag] at h
    cases h
    exact ⟨ByteArray.empty, rest, by simp,
      by simp [Univ.FLAG_VAR], by simp⟩
  · simp [getUnivTag] at h
    change (Except.error _) = Except.ok (decoded, st') at h
    contradiction

theorem getUnivFuel_canonical (fuel : Nat) :
    GetCanonical (getUnivFuel fuel)
      (fun decoded => univBytes decoded.value) := by
  induction fuel with
  | zero =>
    intro pre rest decoded st' h
    simp [getUnivFuel] at h
    change (Except.error _) = Except.ok (decoded, st') at h
    contradiction
  | succ fuel ih =>
    intro pre rest decoded st' h
    simp only [getUnivFuel, StateT.run_bind] at h
    cases ht : getTag2.run ⟨pre ++ rest, pre.size⟩ with
    | error err =>
      rw [ht] at h
      contradiction
    | ok tagResult =>
      rcases tagResult with ⟨tag, afterTag⟩
      rw [ht] at h
      simp only [bind, Except.bind] at h
      obtain ⟨afterTagBytes, hrestTag, hafterTag⟩ :=
        getTag2_canonical pre rest ht
      let tagPre := pre ++ tag2Bytes tag
      have hafterTag' :
          afterTag = ⟨tagPre ++ afterTagBytes, tagPre.size⟩ := by
        rw [hafterTag]
        simp [tagPre, hrestTag, ByteArray.append_assoc]
      rw [hafterTag'] at h
      obtain ⟨payload, suffix, hrestPayload, hencoding, hstate⟩ :=
        getUnivTag_canonical_of (getUnivFuel fuel) ih tag
          tagPre afterTagBytes h
      refine ⟨suffix, ?_, ?_⟩
      · calc
          rest = tag2Bytes tag ++ afterTagBytes := hrestTag
          _ = (tag2Bytes tag ++ payload) ++ suffix := by
            rw [hrestPayload]
            simp [ByteArray.append_assoc]
          _ = univBytes decoded.value ++ suffix := by rw [hencoding]
      · simpa [tagPre, hrestTag, hrestPayload, ← hencoding,
          ByteArray.append_assoc, ByteArray.size_append, Nat.add_assoc]
          using hstate

theorem getUnivCertified_canonical :
    GetCanonical getUnivCertified
      (fun decoded => univBytes decoded.value) := by
  intro pre rest decoded st' h
  change (getUnivFuel
      ((pre ++ rest).size - pre.size + 1)).run
        ⟨pre ++ rest, pre.size⟩ = .ok (decoded, st') at h
  have hfuel : (pre ++ rest).size - pre.size + 1 = rest.size + 1 := by
    simp [ByteArray.size_append]
  rw [hfuel] at h
  exact getUnivFuel_canonical (rest.size + 1) pre rest h

theorem getUniv_canonical : GetCanonical getUniv univBytes := by
  intro pre rest value st' h
  change getUniv ⟨pre ++ rest, pre.size⟩ = .ok (value, st') at h
  unfold getUniv at h
  cases hc : getUnivCertified ⟨pre ++ rest, pre.size⟩ with
  | error err =>
    rw [hc] at h
    contradiction
  | ok result =>
    rcases result with ⟨decoded, afterDecoded⟩
    rw [hc] at h
    cases h
    exact getUnivCertified_canonical pre rest hc

theorem canonicalLaw : CanonicalLaw Univ := by
  intro input value h
  change runGet getUniv input = .ok value at h
  change runPut (putUniv value) = input
  rw [runPut_eq_of_spec (putUniv_spec value)]
  simp only [runGet] at h
  cases hg : getUniv.run ⟨input, 0⟩ with
  | error err =>
    rw [hg] at h
    contradiction
  | ok result =>
    rcases result with ⟨decoded, st⟩
    rw [hg] at h
    simp only [bind, Except.bind] at h
    obtain ⟨suffix, hinput, hst⟩ :=
      getUniv_canonical ByteArray.empty input hg
    by_cases hfull : st.idx = st.bytes.size
    · simp [hfull] at h
      cases h
      have hsize : (univBytes value).size = input.size := by
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

end UnivLaws

namespace Univ

/-- The canonical universe codec decodes every universe it encodes. -/
theorem roundtripLaw : Ixon.RoundtripLaw Univ := by
  intro u
  change runGet getUniv (runPut (putUniv u)) = .ok u
  rw [runPut_eq_of_spec (putUniv_spec u)]
  exact runGet_eq_ok_of_spec (UnivLaws.getUniv_spec u)

/-- Every accepted universe byte string is its unique canonical encoding. -/
theorem canonicalLaw : Ixon.CanonicalLaw Univ :=
  UnivLaws.canonicalLaw

end Univ

end Ix.Compiler.Ixon
