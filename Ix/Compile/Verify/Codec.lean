import Ix.Ixon
import Std.Tactic.BVDecide

/-!
# Proof-visible Ixon codecs

These X1 slices make universe serialization kernel-visible end to end.
`Reads` records exact cursor movement in arbitrary surrounding bytes, while
`Writes` records append-only writer behavior.  The public theorem covers both
every TagN (`f = 2`) rung, subject only to the format's
necessary `UInt64` bound on compressed successor chains.  The smaller theorem
for `Sort 1` remains as a compatibility corollary.
-/

namespace Ix.Compile.Verify.Codec


def Reads (getm : Ixon.GetM α) (bytes : ByteArray) (value : α) : Prop :=
  ∀ before after,
    getm {
      idx := before.size
      bytes := before ++ bytes ++ after
    } = .ok value {
      idx := before.size + bytes.size
      bytes := before ++ bytes ++ after
    }

theorem Reads.bind {getm : Ixon.GetM α} {next : α → Ixon.GetM β}
    {left right : ByteArray} {middle : α} {value : β}
    (hleft : Reads getm left middle)
    (hright : Reads (next middle) right value) :
    Reads (getm >>= next) (left ++ right) value := by
  intro before after
  change (EStateM.bind getm next) _ = _
  rw [show before ++ (left ++ right) ++ after =
      before ++ left ++ (right ++ after) by
    simp [ByteArray.append_assoc]]
  rw [EStateM.bind, hleft before (right ++ after)]
  simpa [ByteArray.append_assoc, Nat.add_assoc] using
    hright (before ++ left) after

theorem Reads.pure (value : α) :
    Reads (pure value : Ixon.GetM α) ByteArray.empty value := by
  intro before after
  change (EStateM.pure value) _ = _
  simp [EStateM.pure]

/-- A validated count does not consume bytes and succeeds whenever the
following canonical payload supplies the required minimum bytes. -/
theorem Reads.checkCount {getm : Ixon.GetM α} {bytes : ByteArray} {value : α}
    (count : UInt64) (minBytes : Nat)
    (hsize : count.toNat * minBytes ≤ bytes.size)
    (hread : Reads getm bytes value) :
    Reads (do Ixon.checkCount count minBytes; getm) bytes value := by
  intro before after
  have hremaining : ¬ count.toNat * minBytes >
      (before ++ bytes ++ after).size - before.size := by
    simp only [ByteArray.size_append]
    omega
  have hcheck : Ixon.checkCount count minBytes
      { idx := before.size, bytes := before ++ bytes ++ after } =
      .ok () { idx := before.size, bytes := before ++ bytes ++ after } := by
    unfold Ixon.checkCount
    change (EStateM.bind EStateM.get _) _ = _
    simp only [EStateM.bind, EStateM.get]
    rw [if_neg hremaining]
    rfl
  change (EStateM.bind (Ixon.checkCount count minBytes) _) _ = _
  rw [EStateM.bind, hcheck]
  exact hread before after

def Writes (putm : Ixon.PutM Unit) (bytes : ByteArray) : Prop :=
  ∀ before, putm.run before = ((), before ++ bytes)

theorem Writes.bind {leftM rightM : Ixon.PutM Unit}
    {left right : ByteArray}
    (hleft : Writes leftM left) (hright : Writes rightM right) :
    Writes (leftM >>= fun _ => rightM) (left ++ right) := by
  intro before
  change StateT.bind leftM (fun _ => rightM) before = _
  have hl := hleft before
  change leftM before = ((), before ++ left) at hl
  have hr := hright (before ++ left)
  change rightM (before ++ left) =
    ((), (before ++ left) ++ right) at hr
  rw [StateT.bind, hl]
  change rightM (before ++ left) = _
  rw [hr]
  simp [ByteArray.append_assoc]

theorem Writes.runPut {putm : Ixon.PutM Unit} {bytes : ByteArray}
    (h : Writes putm bytes) : Ixon.runPut putm = bytes := by
  rw [Ixon.runPut, h ByteArray.empty]
  simp

theorem getU8_reads (byte : UInt8) :
    Reads Ixon.getU8 [byte].toByteArray byte := by
  intro before after
  unfold Ixon.getU8
  change (EStateM.bind EStateM.get _) ({
    idx := before.size
    bytes := before ++ [byte].toByteArray ++ after
  } : Ixon.GetState) = _
  simp only [EStateM.bind, EStateM.get]
  rw [if_pos (by
    simp only [ByteArray.size_append, List.size_toByteArray, List.length_cons,
      List.length_nil]
    omega)]
  change (EStateM.bind (EStateM.set _) _) _ = _
  simp only [EStateM.bind, EStateM.set]
  change (EStateM.pure _) _ = _
  simp only [EStateM.pure, EStateM.Result.ok.injEq]
  constructor
  · rw [getElem!_pos _ _ (by
      simp only [ByteArray.size_append, List.size_toByteArray,
        List.length_cons, List.length_nil]
      omega)]
    rw [ByteArray.getElem_append_left (by
      simp only [ByteArray.size_append, List.size_toByteArray,
        List.length_cons, List.length_nil]
      omega)]
    rw [ByteArray.getElem_append_right (by omega)]
    simp
  · simp

private theorem uint8_cases4 (flag : UInt8) (h : flag < 4) :
    flag = 0 ∨ flag = 1 ∨ flag = 2 ∨ flag = 3 := by
  simp only [← UInt8.toNat_inj, UInt8.lt_iff_toNat_lt,
    UInt8.toNat_ofNat] at h ⊢
  omega

private theorem uint64_cases32 (size : UInt64) (h : size < 32) :
    size = 0 ∨ size = 1 ∨ size = 2 ∨ size = 3 ∨
    size = 4 ∨ size = 5 ∨ size = 6 ∨ size = 7 ∨
    size = 8 ∨ size = 9 ∨ size = 10 ∨ size = 11 ∨
    size = 12 ∨ size = 13 ∨ size = 14 ∨ size = 15 ∨
    size = 16 ∨ size = 17 ∨ size = 18 ∨ size = 19 ∨
    size = 20 ∨ size = 21 ∨ size = 22 ∨ size = 23 ∨
    size = 24 ∨ size = 25 ∨ size = 26 ∨ size = 27 ∨
    size = 28 ∨ size = 29 ∨ size = 30 ∨ size = 31 := by
  simp only [← UInt64.toNat_inj, UInt64.lt_iff_toNat_lt,
    UInt64.toNat_ofNat] at h ⊢
  omega

theorem putU8_writes (byte : UInt8) :
    Writes (Ixon.putU8 byte) [byte].toByteArray := by
  intro before
  simp only [Ixon.putU8, StateT.run]
  change StateT.modifyGet _ before = _
  simp [StateT.modifyGet]
  change ((), before.push byte) = _
  rfl

/-- Splitting off the low byte and shifting the remainder back reconstructs
    the original word.  This is the arithmetic core of trimmed decoding. -/
theorem uint64_lowByte_or_shifted (x : UInt64) :
    x.toUInt8.toUInt64 ||| ((x >>> 8) <<< 8) = x := by
  rw [← UInt64.toNat_inj]
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft,
    UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.reduceMod,
    Nat.reducePow]
  change x.toNat % 256 |||
      (x.toNat >>> 8 <<< 8) % 18446744073709551616 = x.toNat
  have hhigh : x.toNat >>> 8 <<< 8 < 18446744073709551616 := by
    apply Nat.lt_of_le_of_lt _ x.toNat_lt
    simpa [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq] using
      Nat.div_mul_le_self x.toNat (2 ^ 8)
  rw [Nat.mod_eq_of_lt hhigh, Nat.or_comm,
    ← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by decide))]
  simpa [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.mul_comm,
    Nat.add_comm] using
    Nat.mod_add_div x.toNat 256

/-- The low `len` bytes emitted for `x`, least significant first. -/
def trimmedBytes : UInt64 → Nat → ByteArray
  | _, 0 => ByteArray.empty
  | x, len + 1 =>
    [x.toUInt8].toByteArray ++ trimmedBytes (x >>> 8) len

/-- Drop `len` low bytes from a word. -/
def shiftBytes : UInt64 → Nat → UInt64
  | x, 0 => x
  | x, len + 1 => shiftBytes (x >>> 8) len

theorem shiftBytes_toNat (x : UInt64) (len : Nat) :
    (shiftBytes x len).toNat = x.toNat >>> (8 * len) := by
  induction len generalizing x with
  | zero => simp [shiftBytes]
  | succ len ih =>
    simp only [shiftBytes, ih, UInt64.toNat_shiftRight,
      UInt64.reduceToNat, Nat.reduceMod]
    rw [← Nat.shiftRight_add]
    congr 1
    omega

theorem shiftBytes_eq_zero_of_lt (x : UInt64) (len : Nat)
    (h : x.toNat < 2 ^ (8 * len)) :
    shiftBytes x len = 0 := by
  rw [← UInt64.toNat_inj]
  simp only [shiftBytes_toNat, UInt64.reduceToNat]
  exact Nat.shiftRight_eq_zero _ _ h

theorem Writes.pure :
    Writes (pure () : Ixon.PutM Unit) ByteArray.empty := by
  intro before
  change (StateT.pure () : Ixon.PutM Unit) before = _
  simp only [ByteArray.append_empty]
  rfl

theorem putU64TrimmedLEAux_writes (x : UInt64) (len : Nat) :
    Writes (Ixon.putU64TrimmedLEAux x len) (trimmedBytes x len) := by
  induction len generalizing x with
  | zero =>
    simpa [Ixon.putU64TrimmedLEAux, trimmedBytes] using Writes.pure
  | succ len ih =>
    simpa [Ixon.putU64TrimmedLEAux, trimmedBytes] using
      (putU8_writes x.toUInt8).bind (ih (x >>> 8))

theorem getU64TrimmedLEAux_reads (x : UInt64) (len : Nat)
    (hshift : shiftBytes x len = 0) :
    Reads (Ixon.getU64TrimmedLEAux len) (trimmedBytes x len) x := by
  induction len generalizing x with
  | zero =>
    simp only [shiftBytes] at hshift
    subst x
    simpa [Ixon.getU64TrimmedLEAux, trimmedBytes] using
      (Reads.pure (0 : UInt64))
  | succ len ih =>
    have hhigh : shiftBytes (x >>> 8) len = 0 := by
      simpa [shiftBytes] using hshift
    have hreadHigh := ih (x >>> 8) hhigh
    have hreturn : Reads
        (pure (x.toUInt8.toUInt64 ||| ((x >>> 8) <<< 8)) : Ixon.GetM UInt64)
        ByteArray.empty x := by
      rw [uint64_lowByte_or_shifted]
      exact Reads.pure x
    have hafterHigh : Reads
        (do
          let high ← Ixon.getU64TrimmedLEAux len
          return x.toUInt8.toUInt64 ||| (high <<< 8))
        (trimmedBytes (x >>> 8) len) x := by
      simpa using Reads.bind
        (next := fun high : UInt64 =>
          (pure (x.toUInt8.toUInt64 ||| (high <<< 8)) : Ixon.GetM UInt64))
        hreadHigh hreturn
    have hall := Reads.bind
      (next := fun low : UInt8 => do
        let high ← Ixon.getU64TrimmedLEAux len
        return low.toUInt64 ||| (high <<< 8))
      (getU8_reads x.toUInt8) hafterHigh
    simpa [Ixon.getU64TrimmedLEAux, trimmedBytes] using hall

/-! ## Writer -/

/-- The bytes written by `putTagN`. -/
def tagNBytes (f : Nat) (flag : UInt8) (value : UInt64) : ByteArray :=
  let v := value.toNat
  let lead := 2 ^ (8 - f - 1)
  let mbit := 2 ^ (8 - f - 2)
  if v < Ixon.tagNEnd1 f then
    [Ixon.tagNHeader f flag v].toByteArray
  else if v < Ixon.tagNEnd2 f then
    [Ixon.tagNHeader f flag (lead + (v - Ixon.tagNEnd1 f) / 256)].toByteArray ++
      [((v - Ixon.tagNEnd1 f) % 256).toUInt8].toByteArray
  else if v < Ixon.tagNEnd3 f then
    [Ixon.tagNHeader f flag (lead + mbit)].toByteArray ++
      trimmedBytes (v - Ixon.tagNEnd2 f).toUInt64 2
  else if v < Ixon.tagNEnd4 f then
    [Ixon.tagNHeader f flag (lead + mbit + 1)].toByteArray ++
      trimmedBytes (v - Ixon.tagNEnd3 f).toUInt64 3
  else if v < Ixon.tagNEnd5 f then
    [Ixon.tagNHeader f flag (lead + mbit + 2)].toByteArray ++
      trimmedBytes (v - Ixon.tagNEnd4 f).toUInt64 4
  else
    [Ixon.tagNHeader f flag (lead + mbit + 3)].toByteArray ++
      trimmedBytes (v - Ixon.tagNEnd5 f).toUInt64 8

theorem putTagN_writes (f : Nat) (flag : UInt8) (value : UInt64) :
    Writes (Ixon.putTagN f flag value) (tagNBytes f flag value) := by
  unfold Ixon.putTagN tagNBytes
  simp only
  by_cases h1 : value.toNat < Ixon.tagNEnd1 f
  · simp only [h1, ↓reduceIte]
    exact putU8_writes _
  by_cases h2 : value.toNat < Ixon.tagNEnd2 f
  · simp only [h1, h2, ↓reduceIte]
    exact (putU8_writes _).bind (putU8_writes _)
  by_cases h3 : value.toNat < Ixon.tagNEnd3 f
  · simp only [h1, h2, h3, ↓reduceIte]
    exact (putU8_writes _).bind (putU64TrimmedLEAux_writes _ _)
  by_cases h4 : value.toNat < Ixon.tagNEnd4 f
  · simp only [h1, h2, h3, h4, ↓reduceIte]
    exact (putU8_writes _).bind (putU64TrimmedLEAux_writes _ _)
  by_cases h5 : value.toNat < Ixon.tagNEnd5 f
  · simp only [h1, h2, h3, h4, h5, ↓reduceIte]
    exact (putU8_writes _).bind (putU64TrimmedLEAux_writes _ _)
  · simp only [h1, h2, h3, h4, h5, ↓reduceIte]
    exact (putU8_writes _).bind (putU64TrimmedLEAux_writes _ _)

theorem runPut_putTagN (f : Nat) (flag : UInt8) (value : UInt64) :
    Ixon.runPut (Ixon.putTagN f flag value) = tagNBytes f flag value :=
  (putTagN_writes f flag value).runPut

theorem trimmedBytes_size (x : UInt64) (len : Nat) : (trimmedBytes x len).size = len := by
  induction len generalizing x with
  | zero => rfl
  | succ len ih => simp [trimmedBytes, ih]; omega

/-- The encoded length is the TagN width function. -/
theorem tagNBytes_size (f : Nat) (flag : UInt8) (value : UInt64) :
    (tagNBytes f flag value).size = Ixon.tagNByteWidth f value.toNat := by
  unfold tagNBytes Ixon.tagNByteWidth
  simp only
  repeat' split
  all_goals simp [trimmedBytes_size]

theorem tagNBytes_size_pos (f : Nat) (flag : UInt8) (value : UInt64) :
    0 < (tagNBytes f flag value).size := by
  rw [tagNBytes_size]
  unfold Ixon.tagNByteWidth
  repeat' split
  all_goals omega

theorem runPut_putTagN_size (f : Nat) (flag : UInt8) (value : UInt64) :
    (Ixon.runPut (Ixon.putTagN f flag value)).size =
      Ixon.tagNByteWidth f value.toNat := by
  rw [runPut_putTagN, tagNBytes_size]

/-! ## Header arithmetic -/

/-- The constants of the supported flag widths, as linear facts. -/
theorem tagN_consts (f : Nat) (hf : f = 0 ∨ f = 2 ∨ f = 4) :
    2 ^ (8 - f) = 2 * 2 ^ (8 - f - 1) ∧ 2 ^ (8 - f - 1) = 2 * 2 ^ (8 - f - 2) ∧
      4 ≤ 2 ^ (8 - f - 2) ∧ Ixon.tagNEnd1 f = 2 ^ (8 - f - 1) ∧
      Ixon.tagNEnd2 f = Ixon.tagNEnd1 f + 2 ^ (8 - f - 2) * 256 ∧
      Ixon.tagNEnd3 f = Ixon.tagNEnd2 f + 65536 ∧
      Ixon.tagNEnd4 f = Ixon.tagNEnd3 f + 16777216 ∧
      Ixon.tagNEnd5 f = Ixon.tagNEnd4 f + 4294967296 ∧
      Ixon.tagNEnd5 f < 2 ^ 33 := by
  rcases hf with rfl | rfl | rfl <;> decide

theorem tagNHeader_fields (f : Nat) (hf : f = 0 ∨ f = 2 ∨ f = 4) (flag : UInt8)
    (hflag : flag.toNat < 2 ^ f) (payload : Nat) (hp : payload < 2 ^ (8 - f)) :
    (Ixon.tagNHeader f flag payload).toNat / 2 ^ (8 - f) = flag.toNat ∧
      (Ixon.tagNHeader f flag payload).toNat % 2 ^ (8 - f) = payload := by
  have key : ∀ n : Nat, (n.toUInt8).toNat = n % 256 := fun n => by simp
  unfold Ixon.tagNHeader
  rw [key]
  rcases hf with rfl | rfl | rfl <;>
    simp only [Nat.reduceSub, Nat.reducePow] at hflag hp ⊢ <;>
    constructor <;> omega

/-! ## Reads -/

theorem Reads.pure_of_eq {a b : α} (h : a = b) :
    Reads (Pure.pure a : Ixon.GetM α) ByteArray.empty b := by
  subst h
  exact Reads.pure a

theorem tagN_mk_eq {flag : UInt8} {value : UInt64} {n m : Nat}
    (hn : n = flag.toNat) (hm : m = value.toNat) :
    (⟨n.toUInt8, m.toUInt64⟩ : Ixon.TagN) = ⟨flag, value⟩ := by
  subst hn hm
  simp

/-- `getTagN` reads the bytes of `putTagN` back, in any surrounding input. -/
theorem getTagN_reads (f : Nat) (hf : f = 0 ∨ f = 2 ∨ f = 4) (flag : UInt8)
    (hflag : flag.toNat < 2 ^ f) (value : UInt64) :
    Reads (Ixon.getTagN f) (tagNBytes f flag value) ⟨flag, value⟩ := by
  obtain ⟨hR, hlead, hmbit, hE1, hE2, hE3, hE4, hE5, hE5lt⟩ := tagN_consts f hf
  have hv := value.toNat_lt
  unfold tagNBytes Ixon.getTagN
  simp only
  by_cases h1 : value.toNat < Ixon.tagNEnd1 f
  · rw [if_pos h1, ← ByteArray.append_empty (b := [_].toByteArray)]
    refine Reads.bind (getU8_reads _) ?_
    obtain ⟨hdiv, hmod⟩ := tagNHeader_fields f hf flag hflag value.toNat (by omega)
    simp only [hdiv, hmod]
    rw [if_pos (by omega)]
    exact Reads.pure_of_eq (tagN_mk_eq rfl rfl)
  by_cases h2 : value.toNat < Ixon.tagNEnd2 f
  · rw [if_neg h1, if_pos h2]
    refine Reads.bind (getU8_reads _) ?_
    obtain ⟨hdiv, hmod⟩ := tagNHeader_fields f hf flag hflag
      (2 ^ (8 - f - 1) + (value.toNat - Ixon.tagNEnd1 f) / 256) (by omega)
    simp only [hdiv, hmod]
    rw [if_neg (by omega), if_pos (by omega), ← ByteArray.append_empty (b := [_].toByteArray)]
    refine Reads.bind (getU8_reads _) ?_
    exact Reads.pure_of_eq (tagN_mk_eq rfl (by simp; omega))
  by_cases h3 : value.toNat < Ixon.tagNEnd3 f
  · rw [if_neg h1, if_neg h2, if_pos h3]
    refine Reads.bind (getU8_reads _) ?_
    obtain ⟨hdiv, hmod⟩ := tagNHeader_fields f hf flag hflag
      (2 ^ (8 - f - 1) + 2 ^ (8 - f - 2)) (by omega)
    simp only [hdiv, hmod]
    rw [if_neg (by omega), if_neg (by omega)]
    unfold Ixon.getTagNWide
    rw [if_pos (by omega), ← ByteArray.append_empty (b := trimmedBytes _ _)]
    have hx : ((value.toNat - Ixon.tagNEnd2 f).toUInt64).toNat =
        value.toNat - Ixon.tagNEnd2 f := by simp; omega
    refine Reads.bind (getU64TrimmedLEAux_reads _ 2
      (shiftBytes_eq_zero_of_lt _ _ (by rw [hx]; omega))) ?_
    exact Reads.pure_of_eq (tagN_mk_eq rfl (by rw [hx]; omega))
  by_cases h4 : value.toNat < Ixon.tagNEnd4 f
  · rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
    refine Reads.bind (getU8_reads _) ?_
    obtain ⟨hdiv, hmod⟩ := tagNHeader_fields f hf flag hflag
      (2 ^ (8 - f - 1) + 2 ^ (8 - f - 2) + 1) (by omega)
    simp only [hdiv, hmod]
    rw [if_neg (by omega), if_neg (by omega)]
    unfold Ixon.getTagNWide
    rw [if_neg (by omega), if_pos (by omega),
      ← ByteArray.append_empty (b := trimmedBytes _ _)]
    have hx : ((value.toNat - Ixon.tagNEnd3 f).toUInt64).toNat =
        value.toNat - Ixon.tagNEnd3 f := by simp; omega
    refine Reads.bind (getU64TrimmedLEAux_reads _ 3
      (shiftBytes_eq_zero_of_lt _ _ (by rw [hx]; omega))) ?_
    exact Reads.pure_of_eq (tagN_mk_eq rfl (by rw [hx]; omega))
  by_cases h5 : value.toNat < Ixon.tagNEnd5 f
  · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]
    refine Reads.bind (getU8_reads _) ?_
    obtain ⟨hdiv, hmod⟩ := tagNHeader_fields f hf flag hflag
      (2 ^ (8 - f - 1) + 2 ^ (8 - f - 2) + 2) (by omega)
    simp only [hdiv, hmod]
    rw [if_neg (by omega), if_neg (by omega)]
    unfold Ixon.getTagNWide
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
      ← ByteArray.append_empty (b := trimmedBytes _ _)]
    have hx : ((value.toNat - Ixon.tagNEnd4 f).toUInt64).toNat =
        value.toNat - Ixon.tagNEnd4 f := by simp; omega
    refine Reads.bind (getU64TrimmedLEAux_reads _ 4
      (shiftBytes_eq_zero_of_lt _ _ (by rw [hx]; omega))) ?_
    exact Reads.pure_of_eq (tagN_mk_eq rfl (by rw [hx]; omega))
  · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]
    refine Reads.bind (getU8_reads _) ?_
    obtain ⟨hdiv, hmod⟩ := tagNHeader_fields f hf flag hflag
      (2 ^ (8 - f - 1) + 2 ^ (8 - f - 2) + 3) (by omega)
    simp only [hdiv, hmod]
    rw [if_neg (by omega), if_neg (by omega)]
    unfold Ixon.getTagNWide
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
      ← ByteArray.append_empty (b := trimmedBytes _ _)]
    have hx : ((value.toNat - Ixon.tagNEnd5 f).toUInt64).toNat =
        value.toNat - Ixon.tagNEnd5 f := by simp; omega
    refine Reads.bind (getU64TrimmedLEAux_reads _ 8
      (shiftBytes_eq_zero_of_lt _ _ (by rw [hx]; omega))) ?_
    rw [if_pos (by rw [hx]; omega)]
    exact Reads.pure_of_eq (tagN_mk_eq rfl (by rw [hx]; omega))

/-- A read law gives the exact full-buffer decode. -/
theorem Reads.runGetExact {getm : Ixon.GetM α} {bytes : ByteArray} {value : α}
    (h : Reads getm bytes value) : Ixon.runGetExact getm bytes = .ok value := by
  have hread := h ByteArray.empty ByteArray.empty
  simp only [ByteArray.empty_append, ByteArray.append_empty,
    ByteArray.size_empty, Nat.zero_add] at hread
  unfold Ixon.runGetExact
  change EStateM.run getm { bytes := bytes } = _ at hread
  rw [hread]
  simp

/-- Exact roundtrip of the TagN code. -/
theorem runGetExact_getTagN_putTagN (f : Nat) (hf : f = 0 ∨ f = 2 ∨ f = 4)
    (flag : UInt8) (hflag : flag.toNat < 2 ^ f) (value : UInt64) :
    Ixon.runGetExact (Ixon.getTagN f) (Ixon.runPut (Ixon.putTagN f flag value)) =
      .ok ⟨flag, value⟩ := by
  rw [runPut_putTagN]
  exact Reads.runGetExact (getTagN_reads f hf flag hflag value)

/-! ## The wire's integer fields

Every integer field of the wire format is a TagN integer: `f = 2` for
universe terms, `f = 0` (no flag) for counts and indices, `f = 4` for
expression and constant headers. -/

/-- The bytes of a universe header (`Ixon.putTagN 2`). -/
def tag2Bytes (flag : UInt8) (size : UInt64) : ByteArray := tagNBytes 2 flag size

/-- The bytes of a count or index (`Ixon.putTagN 0 0`). -/
def tag0Bytes (size : UInt64) : ByteArray := tagNBytes 0 0 size

/-- The bytes of an expression or constant header (`Ixon.putTagN 4`). -/
def tag4Bytes (flag : UInt8) (size : UInt64) : ByteArray := tagNBytes 4 flag size

theorem putTag2_writes (flag : UInt8) (size : UInt64) :
    Writes (Ixon.putTagN 2 flag size) (tag2Bytes flag size) :=
  putTagN_writes 2 flag size

theorem getTag2_reads (flag : UInt8) (size : UInt64) (hflag : flag < 4) :
    Reads (Ixon.getTagN 2) (tag2Bytes flag size) ⟨flag, size⟩ :=
  getTagN_reads 2 (by decide) flag (by simpa [UInt8.lt_iff_toNat_lt] using hflag) size

theorem putTag0_writes (size : UInt64) :
    Writes (Ixon.putTagN 0 0 size) (tag0Bytes size) :=
  putTagN_writes 0 0 size

theorem getTag0_reads (size : UInt64) :
    Reads (Ixon.getTagN 0) (tag0Bytes size) ⟨0, size⟩ :=
  getTagN_reads 0 (by decide) 0 (by decide) size

theorem putTag4_writes (flag : UInt8) (size : UInt64) :
    Writes (Ixon.putTagN 4 flag size) (tag4Bytes flag size) :=
  putTagN_writes 4 flag size

theorem getTag4_reads (flag : UInt8) (size : UInt64) (hflag : flag < 16) :
    Reads (Ixon.getTagN 4) (tag4Bytes flag size) ⟨flag, size⟩ :=
  getTagN_reads 4 (by decide) flag (by simpa [UInt8.lt_iff_toNat_lt] using hflag) size

/-- A small universe header is one byte: the flag in the top two bits, the
value below. -/
theorem tag2Bytes_small (flag : UInt8) (size : UInt64)
    (hflag : flag < 4) (hsize : size < 32) :
    tag2Bytes flag size = [((flag <<< 6) ||| size.toUInt8)].toByteArray := by
  have hs : size.toNat < Ixon.tagNEnd1 2 := by
    simpa [UInt64.lt_iff_toNat_lt, show Ixon.tagNEnd1 2 = 32 by decide] using hsize
  unfold tag2Bytes tagNBytes
  simp only [if_pos hs]
  congr 1
  rcases uint8_cases4 flag hflag with rfl | rfl | rfl | rfl <;>
    rcases uint64_cases32 size hsize with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem getTag2_reads_small (flag : UInt8) (size : UInt64)
    (hflag : flag < 4) (hsize : size < 32) :
    Reads (Ixon.getTagN 2) [((flag <<< 6) ||| size.toUInt8)].toByteArray ⟨flag, size⟩ := by
  rw [← tag2Bytes_small flag size hflag hsize]
  exact getTag2_reads flag size hflag

theorem putTag2_writes_small (flag : UInt8) (size : UInt64)
    (hflag : flag < 4) (hsize : size < 32) :
    Writes (Ixon.putTagN 2 flag size) [((flag <<< 6) ||| size.toUInt8)].toByteArray := by
  rw [← tag2Bytes_small flag size hflag hsize]
  exact putTag2_writes flag size

theorem nat_toUInt64_lt_32 {n : Nat} (h : n < 32) :
    n.toUInt64 < 32 := by
  change UInt64.ofNat n < UInt64.ofNat 32
  rw [UInt64.lt_ofNat_iff (by decide)]
  rw [UInt64.toNat_ofNat_of_lt' (Nat.lt_trans h (by decide))]
  exact h

theorem tag2_zero_header (size : UInt64) :
    (Ixon.Univ.FLAG_ZERO_SUCC <<< 6) ||| size.toUInt8 = size.toUInt8 := by
  simp only [Ixon.Univ.FLAG_ZERO_SUCC]
  bv_decide

theorem tag2_max_zero_header :
    (Ixon.Univ.FLAG_MAX <<< 6) ||| (0 : UInt64).toUInt8 = 0x40 := by
  decide

theorem tag2_imax_zero_header :
    (Ixon.Univ.FLAG_IMAX <<< 6) ||| (0 : UInt64).toUInt8 = 0x80 := by
  decide

theorem tag2_var_header (idx : UInt64) :
    (Ixon.Univ.FLAG_VAR <<< 6) ||| idx.toUInt8 = 0xc0 ||| idx.toUInt8 := by
  simp only [Ixon.Univ.FLAG_VAR]
  bv_decide

namespace Ixon.Univ

def SmallWireWF : Ixon.Univ → Prop
  | .zero => True
  | u@(.succ inner) => u.succCountNat < 32 ∧ SmallWireWF inner
  | .max left right => SmallWireWF left ∧ SmallWireWF right
  | .imax left right => SmallWireWF left ∧ SmallWireWF right
  | .var idx => idx < 32

theorem addSucc_succCountNat_succBase (u : Ixon.Univ) :
    u.succBase.addSucc u.succCountNat = u := by
  induction u with
  | zero => rfl
  | succ u ih =>
    rw [Ixon.Univ.succCountNat, Nat.add_comm]
    simp [Ixon.Univ.succBase, Ixon.Univ.addSucc, ih]
  | max left right => rfl
  | imax left right => rfl
  | var idx => rfl

theorem SmallWireWF.succBase {u : Ixon.Univ} (h : SmallWireWF u) :
    SmallWireWF u.succBase := by
  induction u with
  | zero => exact h
  | succ u ih =>
    change SmallWireWF u.succBase
    exact ih h.2
  | max left right => exact h
  | imax left right => exact h
  | var idx => exact h

def smallEncode : Ixon.Univ → ByteArray
  | .zero => [0].toByteArray
  | u@(.succ _) =>
    [u.succCount.toUInt8].toByteArray ++ smallEncode u.succBase
  | .max left right =>
    [0x40].toByteArray ++ smallEncode left ++ smallEncode right
  | .imax left right =>
    [0x80].toByteArray ++ smallEncode left ++ smallEncode right
  | .var idx => [0xc0 ||| idx.toUInt8].toByteArray
termination_by u => sizeOf u
decreasing_by
  all_goals simp_wf
  all_goals try omega
  rename_i inner heq
  subst u
  change sizeOf inner.succBase < 1 + sizeOf inner
  have hbase := Ixon.Univ.succBase_sizeOf_le inner
  omega

theorem smallEncode_size_pos (u : Ixon.Univ) :
    0 < (smallEncode u).size := by
  fun_induction smallEncode u <;> simp_all <;> omega

theorem putUniv_writes_small (u : Ixon.Univ) (h : SmallWireWF u) :
    Writes (Ixon.putUniv u) (smallEncode u) := by
  revert h
  refine WellFounded.induction
    (C := fun u : Ixon.Univ =>
      SmallWireWF u → Writes (Ixon.putUniv u) (smallEncode u))
    (measure (fun u : Ixon.Univ => sizeOf u)).wf u ?_
  intro u ih h
  cases u with
  | zero =>
    simpa [Ixon.putUniv, smallEncode, Ixon.Univ.FLAG_ZERO_SUCC] using
      putTag2_writes_small Ixon.Univ.FLAG_ZERO_SUCC 0 (by decide) (by decide)
  | succ inner =>
    let u : Ixon.Univ := .succ inner
    have hcount : u.succCount < 32 := by
      exact nat_toUInt64_lt_32 h.1
    have htag : Writes (Ixon.putTagN 2 Ixon.Univ.FLAG_ZERO_SUCC u.succCount) [u.succCount.toUInt8].toByteArray := by
      simpa only [tag2_zero_header] using
        putTag2_writes_small Ixon.Univ.FLAG_ZERO_SUCC u.succCount (by decide) hcount
    have hlt : sizeOf u.succBase < sizeOf u := by
      change sizeOf inner.succBase < 1 + sizeOf inner
      have hsize := Ixon.Univ.succBase_sizeOf_le inner
      omega
    have hbase := ih u.succBase hlt h.succBase
    simpa [u, Ixon.putUniv, smallEncode] using htag.bind hbase
  | max left right =>
    have htag : Writes (Ixon.putTagN 2 Ixon.Univ.FLAG_MAX 0)
        [0x40].toByteArray := by
      simpa only [tag2_max_zero_header] using
        putTag2_writes_small Ixon.Univ.FLAG_MAX 0 (by decide) (by decide)
    have hleft := ih left (by simp_wf; omega) h.1
    have hright := ih right (by simp_wf; omega) h.2
    simpa [Ixon.putUniv, smallEncode, ByteArray.append_assoc] using
      htag.bind (hleft.bind hright)
  | imax left right =>
    have htag : Writes (Ixon.putTagN 2 Ixon.Univ.FLAG_IMAX 0)
        [0x80].toByteArray := by
      simpa only [tag2_imax_zero_header] using
        putTag2_writes_small Ixon.Univ.FLAG_IMAX 0 (by decide) (by decide)
    have hleft := ih left (by simp_wf; omega) h.1
    have hright := ih right (by simp_wf; omega) h.2
    simpa [Ixon.putUniv, smallEncode, ByteArray.append_assoc] using
      htag.bind (hleft.bind hright)
  | var idx =>
    simpa only [Ixon.putUniv, smallEncode, tag2_var_header] using
      putTag2_writes_small Ixon.Univ.FLAG_VAR idx (by decide) h

theorem getUnivFuel_reads_small (u : Ixon.Univ) (h : SmallWireWF u)
    (fuel : Nat) (hfuel : (smallEncode u).size ≤ fuel) :
    Reads (Ixon.getUnivFuel fuel) (smallEncode u) u := by
  revert h fuel
  refine WellFounded.induction
    (C := fun u : Ixon.Univ => ∀ (_ : SmallWireWF u) (fuel : Nat),
      (smallEncode u).size ≤ fuel →
        Reads (Ixon.getUnivFuel fuel) (smallEncode u) u)
    (measure (fun u : Ixon.Univ => sizeOf u)).wf u ?_
  intro u ih h fuel hfuel
  cases fuel with
  | zero =>
    have hpos := smallEncode_size_pos u
    omega
  | succ fuel =>
    cases u with
    | zero =>
      have htag : Reads (Ixon.getTagN 2) [0].toByteArray
          ⟨Ixon.Univ.FLAG_ZERO_SUCC, 0⟩ := by
        simpa [Ixon.Univ.FLAG_ZERO_SUCC] using
          getTag2_reads_small Ixon.Univ.FLAG_ZERO_SUCC 0
            (by decide) (by decide)
      have htail : Reads
          (Ixon.getUnivFromTag (Ixon.getUnivFuel fuel)
            ⟨Ixon.Univ.FLAG_ZERO_SUCC, 0⟩)
          ByteArray.empty Ixon.Univ.zero := by
        simpa [Ixon.getUnivFromTag, Ixon.Univ.FLAG_ZERO_SUCC] using
          Reads.pure Ixon.Univ.zero
      have hall := Reads.bind
        (next := Ixon.getUnivFromTag (Ixon.getUnivFuel fuel)) htag htail
      simpa [Ixon.getUnivFuel, smallEncode, Ixon.Univ.FLAG_ZERO_SUCC] using hall
    | succ inner =>
      let whole : Ixon.Univ := .succ inner
      have hcount : whole.succCount < 32 := nat_toUInt64_lt_32 h.1
      have htag : Reads (Ixon.getTagN 2)
          [whole.succCount.toUInt8].toByteArray
          ⟨Ixon.Univ.FLAG_ZERO_SUCC, whole.succCount⟩ := by
        simpa only [tag2_zero_header] using
          getTag2_reads_small Ixon.Univ.FLAG_ZERO_SUCC whole.succCount
            (by decide) hcount
      have hsizes : 1 + (smallEncode whole.succBase).size ≤ fuel + 1 := by
        simpa only [whole, smallEncode, ByteArray.size_append,
          List.size_toByteArray, List.length_cons, List.length_nil] using hfuel
      have hbaseFuel : (smallEncode whole.succBase).size ≤ fuel := by omega
      have hlt : sizeOf whole.succBase < sizeOf whole := by
        change sizeOf inner.succBase < 1 + sizeOf inner
        have hsize := Ixon.Univ.succBase_sizeOf_le inner
        omega
      have hbase := ih whole.succBase hlt h.succBase fuel hbaseFuel
      have hcountToNat : whole.succCount.toNat = whole.succCountNat := by
        simp only [Ixon.Univ.succCount]
        rw [UInt64.toNat_ofNat_of_lt'
          (Nat.lt_trans h.1 (by decide))]
      have hcountNe : whole.succCount ≠ 0 := by
        intro heq
        have hzero : whole.succCount.toNat = 0 := by
          simpa using congrArg UInt64.toNat heq
        rw [hcountToNat] at hzero
        have hpos : 0 < whole.succCountNat := by
          change 0 < 1 + inner.succCountNat
          omega
        omega
      have hreturn : Reads
          (pure (whole.succBase.addSucc whole.succCount.toNat) : Ixon.GetM _)
          ByteArray.empty whole := by
        simpa [hcountToNat,
          Ixon.Univ.addSucc_succCountNat_succBase whole] using
          Reads.pure whole
      have hafterBase := Reads.bind
        (next := fun base : Ixon.Univ =>
          (pure (Ixon.Univ.addSucc whole.succCount.toNat base) : Ixon.GetM _))
        hbase hreturn
      have htail : Reads
          (Ixon.getUnivFromTag (Ixon.getUnivFuel fuel)
            ⟨Ixon.Univ.FLAG_ZERO_SUCC, whole.succCount⟩)
          (smallEncode whole.succBase) whole := by
        simpa [Ixon.getUnivFromTag, Ixon.Univ.FLAG_ZERO_SUCC, hcountNe] using
          hafterBase
      have hall := Reads.bind
        (next := Ixon.getUnivFromTag (Ixon.getUnivFuel fuel)) htag htail
      simpa [whole, Ixon.getUnivFuel, smallEncode,
        Ixon.Univ.FLAG_ZERO_SUCC, hcountNe, ByteArray.append_assoc] using hall
    | max left right =>
      have htag : Reads (Ixon.getTagN 2) [0x40].toByteArray
          ⟨Ixon.Univ.FLAG_MAX, 0⟩ := by
        simpa only [tag2_max_zero_header] using
          getTag2_reads_small Ixon.Univ.FLAG_MAX 0 (by decide) (by decide)
      have hsizes :
          1 + (smallEncode left).size + (smallEncode right).size ≤
            fuel + 1 := by
        simpa only [smallEncode, ByteArray.size_append,
          List.size_toByteArray, List.length_cons, List.length_nil] using hfuel
      have hleft := ih left (by simp_wf; omega) h.1 fuel (by omega)
      have hright := ih right (by simp_wf; omega) h.2 fuel (by omega)
      have hreturn := Reads.pure (Ixon.Univ.max left right)
      have hafterRight := Reads.bind
        (next := fun right : Ixon.Univ =>
          (pure (Ixon.Univ.max left right) : Ixon.GetM _))
        hright hreturn
      have hafterLeft := Reads.bind
        (next := fun left => do
          let right ← Ixon.getUnivFuel fuel
          return Ixon.Univ.max left right)
        hleft hafterRight
      have htail : Reads
          (Ixon.getUnivFromTag (Ixon.getUnivFuel fuel)
            ⟨Ixon.Univ.FLAG_MAX, 0⟩)
          (smallEncode left ++ smallEncode right)
          (Ixon.Univ.max left right) := by
        simpa [Ixon.getUnivFromTag, Ixon.Univ.FLAG_MAX] using hafterLeft
      have hall := Reads.bind
        (next := Ixon.getUnivFromTag (Ixon.getUnivFuel fuel)) htag htail
      simpa [Ixon.getUnivFuel, smallEncode, Ixon.Univ.FLAG_MAX,
        ByteArray.append_assoc] using hall
    | imax left right =>
      have htag : Reads (Ixon.getTagN 2) [0x80].toByteArray
          ⟨Ixon.Univ.FLAG_IMAX, 0⟩ := by
        simpa only [tag2_imax_zero_header] using
          getTag2_reads_small Ixon.Univ.FLAG_IMAX 0 (by decide) (by decide)
      have hsizes :
          1 + (smallEncode left).size + (smallEncode right).size ≤
            fuel + 1 := by
        simpa only [smallEncode, ByteArray.size_append,
          List.size_toByteArray, List.length_cons, List.length_nil] using hfuel
      have hleft := ih left (by simp_wf; omega) h.1 fuel (by omega)
      have hright := ih right (by simp_wf; omega) h.2 fuel (by omega)
      have hreturn := Reads.pure (Ixon.Univ.imax left right)
      have hafterRight := Reads.bind
        (next := fun right : Ixon.Univ =>
          (pure (Ixon.Univ.imax left right) : Ixon.GetM _))
        hright hreturn
      have hafterLeft := Reads.bind
        (next := fun left => do
          let right ← Ixon.getUnivFuel fuel
          return Ixon.Univ.imax left right)
        hleft hafterRight
      have htail : Reads
          (Ixon.getUnivFromTag (Ixon.getUnivFuel fuel)
            ⟨Ixon.Univ.FLAG_IMAX, 0⟩)
          (smallEncode left ++ smallEncode right)
          (Ixon.Univ.imax left right) := by
        simpa [Ixon.getUnivFromTag, Ixon.Univ.FLAG_IMAX] using hafterLeft
      have hall := Reads.bind
        (next := Ixon.getUnivFromTag (Ixon.getUnivFuel fuel)) htag htail
      simpa [Ixon.getUnivFuel, smallEncode, Ixon.Univ.FLAG_IMAX,
        ByteArray.append_assoc] using hall
    | var idx =>
      have htag : Reads (Ixon.getTagN 2)
          [0xc0 ||| idx.toUInt8].toByteArray
          ⟨Ixon.Univ.FLAG_VAR, idx⟩ := by
        simpa only [tag2_var_header] using
          getTag2_reads_small Ixon.Univ.FLAG_VAR idx (by decide) h
      have htail : Reads
          (Ixon.getUnivFromTag (Ixon.getUnivFuel fuel)
            ⟨Ixon.Univ.FLAG_VAR, idx⟩)
          ByteArray.empty (Ixon.Univ.var idx) := by
        simpa [Ixon.getUnivFromTag, Ixon.Univ.FLAG_VAR] using
          Reads.pure (Ixon.Univ.var idx)
      have hall := Reads.bind
        (next := Ixon.getUnivFromTag (Ixon.getUnivFuel fuel)) htag htail
      simpa [Ixon.getUnivFuel, smallEncode, Ixon.Univ.FLAG_VAR] using hall

theorem serUniv_eq_smallEncode (u : Ixon.Univ) (h : SmallWireWF u) :
    Ixon.serUniv u = smallEncode u := by
  exact (putUniv_writes_small u h).runPut

theorem getUniv_reads_small (u : Ixon.Univ) (h : SmallWireWF u) :
    Reads Ixon.getUniv (smallEncode u) u := by
  intro before after
  unfold Ixon.getUniv
  change (EStateM.bind EStateM.get _) _ = _
  simp only [EStateM.bind, EStateM.get]
  have hfuel : (smallEncode u).size ≤
      (before ++ smallEncode u ++ after).size - before.size + 1 := by
    simp only [ByteArray.size_append]
    omega
  have hread := getUnivFuel_reads_small u h _ hfuel before after
  exact hread

theorem deUniv_serUniv_small (u : Ixon.Univ) (h : SmallWireWF u) :
    Ixon.deUniv (Ixon.serUniv u) = .ok u := by
  rw [serUniv_eq_smallEncode u h]
  unfold Ixon.deUniv Ixon.runGetExact
  have hread := getUniv_reads_small u h ByteArray.empty ByteArray.empty
  simp only [ByteArray.empty_append, ByteArray.append_empty,
    ByteArray.size_empty, Nat.zero_add] at hread
  change EStateM.run Ixon.getUniv { bytes := smallEncode u } = _ at hread
  rw [hread]
  simp

end Ixon.Univ

namespace Ixon.Univ

/-- Universes whose compressed successor-chain counts are representable on
    the v2 wire.  All explicit universe variables are already `UInt64`. -/
def WireWF : Ixon.Univ → Prop
  | .zero => True
  | u@(.succ inner) =>
    u.succCountNat < UInt64.size ∧ WireWF inner
  | .max left right => WireWF left ∧ WireWF right
  | .imax left right => WireWF left ∧ WireWF right
  | .var _ => True

theorem WireWF.succBase {u : Ixon.Univ} (h : WireWF u) :
    WireWF u.succBase := by
  induction u with
  | zero => exact h
  | succ u ih =>
    change WireWF u.succBase
    exact ih h.2
  | max left right => exact h
  | imax left right => exact h
  | var idx => exact h

/-- Exact production bytes for a wire-well-formed universe. -/
def wireEncode : Ixon.Univ → ByteArray
  | .zero => tag2Bytes Ixon.Univ.FLAG_ZERO_SUCC 0
  | u@(.succ _) =>
    tag2Bytes Ixon.Univ.FLAG_ZERO_SUCC u.succCount ++
      wireEncode u.succBase
  | .max left right =>
    tag2Bytes Ixon.Univ.FLAG_MAX 0 ++ wireEncode left ++ wireEncode right
  | .imax left right =>
    tag2Bytes Ixon.Univ.FLAG_IMAX 0 ++ wireEncode left ++ wireEncode right
  | .var idx => tag2Bytes Ixon.Univ.FLAG_VAR idx
termination_by u => sizeOf u
decreasing_by
  all_goals simp_wf
  all_goals try omega
  rename_i inner heq
  subst u
  change sizeOf inner.succBase < 1 + sizeOf inner
  have hbase := Ixon.Univ.succBase_sizeOf_le inner
  omega

theorem tag2Bytes_size_pos (flag : UInt8) (size : UInt64) :
    0 < (tag2Bytes flag size).size := tagNBytes_size_pos 2 flag size

theorem wireEncode_size_pos (u : Ixon.Univ) :
    0 < (wireEncode u).size := by
  fun_induction wireEncode u <;>
    simp_all only [ByteArray.size_append, tag2Bytes_size_pos] <;> omega

theorem putUniv_writes (u : Ixon.Univ) (h : WireWF u) :
    Writes (Ixon.putUniv u) (wireEncode u) := by
  revert h
  refine WellFounded.induction
    (C := fun u : Ixon.Univ =>
      WireWF u → Writes (Ixon.putUniv u) (wireEncode u))
    (measure (fun u : Ixon.Univ => sizeOf u)).wf u ?_
  intro u ih h
  cases u with
  | zero =>
    simpa [Ixon.putUniv, wireEncode] using
      putTag2_writes Ixon.Univ.FLAG_ZERO_SUCC 0
  | succ inner =>
    let u : Ixon.Univ := .succ inner
    have htag := putTag2_writes Ixon.Univ.FLAG_ZERO_SUCC u.succCount
    have hlt : sizeOf u.succBase < sizeOf u := by
      change sizeOf inner.succBase < 1 + sizeOf inner
      have hsize := Ixon.Univ.succBase_sizeOf_le inner
      omega
    have hbase := ih u.succBase hlt h.succBase
    simpa [u, Ixon.putUniv, wireEncode] using htag.bind hbase
  | max left right =>
    have htag := putTag2_writes Ixon.Univ.FLAG_MAX 0
    have hleft := ih left (by simp_wf; omega) h.1
    have hright := ih right (by simp_wf; omega) h.2
    simpa [Ixon.putUniv, wireEncode, ByteArray.append_assoc] using
      htag.bind (hleft.bind hright)
  | imax left right =>
    have htag := putTag2_writes Ixon.Univ.FLAG_IMAX 0
    have hleft := ih left (by simp_wf; omega) h.1
    have hright := ih right (by simp_wf; omega) h.2
    simpa [Ixon.putUniv, wireEncode, ByteArray.append_assoc] using
      htag.bind (hleft.bind hright)
  | var idx =>
    simpa [Ixon.putUniv, wireEncode] using
      putTag2_writes Ixon.Univ.FLAG_VAR idx

theorem getUnivFuel_reads (u : Ixon.Univ) (h : WireWF u)
    (fuel : Nat) (hfuel : (wireEncode u).size ≤ fuel) :
    Reads (Ixon.getUnivFuel fuel) (wireEncode u) u := by
  revert h fuel
  refine WellFounded.induction
    (C := fun u : Ixon.Univ => ∀ (_ : WireWF u) (fuel : Nat),
      (wireEncode u).size ≤ fuel →
        Reads (Ixon.getUnivFuel fuel) (wireEncode u) u)
    (measure (fun u : Ixon.Univ => sizeOf u)).wf u ?_
  intro u ih h fuel hfuel
  cases fuel with
  | zero =>
    have hpos := wireEncode_size_pos u
    omega
  | succ fuel =>
    cases u with
    | zero =>
      have htag : Reads (Ixon.getTagN 2)
          (tag2Bytes Ixon.Univ.FLAG_ZERO_SUCC 0)
          ⟨Ixon.Univ.FLAG_ZERO_SUCC, 0⟩ :=
        getTag2_reads Ixon.Univ.FLAG_ZERO_SUCC 0 (by decide)
      have htail : Reads
          (Ixon.getUnivFromTag (Ixon.getUnivFuel fuel)
            ⟨Ixon.Univ.FLAG_ZERO_SUCC, 0⟩)
          ByteArray.empty Ixon.Univ.zero := by
        simpa [Ixon.getUnivFromTag, Ixon.Univ.FLAG_ZERO_SUCC] using
          Reads.pure Ixon.Univ.zero
      have hall := Reads.bind
        (next := Ixon.getUnivFromTag (Ixon.getUnivFuel fuel)) htag htail
      simpa [Ixon.getUnivFuel, wireEncode,
        Ixon.Univ.FLAG_ZERO_SUCC] using hall
    | succ inner =>
      let whole : Ixon.Univ := .succ inner
      have htag : Reads (Ixon.getTagN 2)
          (tag2Bytes Ixon.Univ.FLAG_ZERO_SUCC whole.succCount)
          ⟨Ixon.Univ.FLAG_ZERO_SUCC, whole.succCount⟩ :=
        getTag2_reads Ixon.Univ.FLAG_ZERO_SUCC whole.succCount (by decide)
      have hsizes :
          (tag2Bytes Ixon.Univ.FLAG_ZERO_SUCC whole.succCount).size +
              (wireEncode whole.succBase).size ≤ fuel + 1 := by
        simpa only [whole, wireEncode, ByteArray.size_append] using hfuel
      have htagPos := tag2Bytes_size_pos
        Ixon.Univ.FLAG_ZERO_SUCC whole.succCount
      have hbaseFuel : (wireEncode whole.succBase).size ≤ fuel := by
        omega
      have hlt : sizeOf whole.succBase < sizeOf whole := by
        change sizeOf inner.succBase < 1 + sizeOf inner
        have hsize := Ixon.Univ.succBase_sizeOf_le inner
        omega
      have hbase := ih whole.succBase hlt h.succBase fuel hbaseFuel
      have hcountToNat : whole.succCount.toNat = whole.succCountNat := by
        simp only [Ixon.Univ.succCount]
        rw [UInt64.toNat_ofNat_of_lt' h.1]
      have hcountNe : whole.succCount ≠ 0 := by
        intro heq
        have hzero : whole.succCount.toNat = 0 := by
          simpa using congrArg UInt64.toNat heq
        rw [hcountToNat] at hzero
        have hpos : 0 < whole.succCountNat := by
          change 0 < 1 + inner.succCountNat
          omega
        omega
      have hreturn : Reads
          (pure (whole.succBase.addSucc whole.succCount.toNat) : Ixon.GetM _)
          ByteArray.empty whole := by
        simpa [hcountToNat, addSucc_succCountNat_succBase whole] using
          Reads.pure whole
      have hafterBase := Reads.bind
        (next := fun base : Ixon.Univ =>
          (pure (Ixon.Univ.addSucc whole.succCount.toNat base) : Ixon.GetM _))
        hbase hreturn
      have htail : Reads
          (Ixon.getUnivFromTag (Ixon.getUnivFuel fuel)
            ⟨Ixon.Univ.FLAG_ZERO_SUCC, whole.succCount⟩)
          (wireEncode whole.succBase) whole := by
        simpa [Ixon.getUnivFromTag, Ixon.Univ.FLAG_ZERO_SUCC, hcountNe] using
          hafterBase
      have hall := Reads.bind
        (next := Ixon.getUnivFromTag (Ixon.getUnivFuel fuel)) htag htail
      simpa [whole, Ixon.getUnivFuel, wireEncode,
        Ixon.Univ.FLAG_ZERO_SUCC, hcountNe, ByteArray.append_assoc] using hall
    | max left right =>
      have htag : Reads (Ixon.getTagN 2)
          (tag2Bytes Ixon.Univ.FLAG_MAX 0)
          ⟨Ixon.Univ.FLAG_MAX, 0⟩ :=
        getTag2_reads Ixon.Univ.FLAG_MAX 0 (by decide)
      have hsizes :
          (tag2Bytes Ixon.Univ.FLAG_MAX 0).size +
              (wireEncode left).size + (wireEncode right).size ≤ fuel + 1 := by
        simpa only [wireEncode, ByteArray.size_append] using hfuel
      have htagPos := tag2Bytes_size_pos Ixon.Univ.FLAG_MAX 0
      have hleft := ih left (by simp_wf; omega) h.1 fuel (by omega)
      have hright := ih right (by simp_wf; omega) h.2 fuel (by omega)
      have hreturn := Reads.pure (Ixon.Univ.max left right)
      have hafterRight := Reads.bind
        (next := fun right : Ixon.Univ =>
          (pure (Ixon.Univ.max left right) : Ixon.GetM _))
        hright hreturn
      have hafterLeft := Reads.bind
        (next := fun left => do
          let right ← Ixon.getUnivFuel fuel
          return Ixon.Univ.max left right)
        hleft hafterRight
      have htail : Reads
          (Ixon.getUnivFromTag (Ixon.getUnivFuel fuel)
            ⟨Ixon.Univ.FLAG_MAX, 0⟩)
          (wireEncode left ++ wireEncode right)
          (Ixon.Univ.max left right) := by
        simpa [Ixon.getUnivFromTag, Ixon.Univ.FLAG_MAX] using hafterLeft
      have hall := Reads.bind
        (next := Ixon.getUnivFromTag (Ixon.getUnivFuel fuel)) htag htail
      simpa [Ixon.getUnivFuel, wireEncode, Ixon.Univ.FLAG_MAX,
        ByteArray.append_assoc] using hall
    | imax left right =>
      have htag : Reads (Ixon.getTagN 2)
          (tag2Bytes Ixon.Univ.FLAG_IMAX 0)
          ⟨Ixon.Univ.FLAG_IMAX, 0⟩ :=
        getTag2_reads Ixon.Univ.FLAG_IMAX 0 (by decide)
      have hsizes :
          (tag2Bytes Ixon.Univ.FLAG_IMAX 0).size +
              (wireEncode left).size + (wireEncode right).size ≤ fuel + 1 := by
        simpa only [wireEncode, ByteArray.size_append] using hfuel
      have htagPos := tag2Bytes_size_pos Ixon.Univ.FLAG_IMAX 0
      have hleft := ih left (by simp_wf; omega) h.1 fuel (by omega)
      have hright := ih right (by simp_wf; omega) h.2 fuel (by omega)
      have hreturn := Reads.pure (Ixon.Univ.imax left right)
      have hafterRight := Reads.bind
        (next := fun right : Ixon.Univ =>
          (pure (Ixon.Univ.imax left right) : Ixon.GetM _))
        hright hreturn
      have hafterLeft := Reads.bind
        (next := fun left => do
          let right ← Ixon.getUnivFuel fuel
          return Ixon.Univ.imax left right)
        hleft hafterRight
      have htail : Reads
          (Ixon.getUnivFromTag (Ixon.getUnivFuel fuel)
            ⟨Ixon.Univ.FLAG_IMAX, 0⟩)
          (wireEncode left ++ wireEncode right)
          (Ixon.Univ.imax left right) := by
        simpa [Ixon.getUnivFromTag, Ixon.Univ.FLAG_IMAX] using hafterLeft
      have hall := Reads.bind
        (next := Ixon.getUnivFromTag (Ixon.getUnivFuel fuel)) htag htail
      simpa [Ixon.getUnivFuel, wireEncode, Ixon.Univ.FLAG_IMAX,
        ByteArray.append_assoc] using hall
    | var idx =>
      have htag : Reads (Ixon.getTagN 2)
          (tag2Bytes Ixon.Univ.FLAG_VAR idx)
          ⟨Ixon.Univ.FLAG_VAR, idx⟩ :=
        getTag2_reads Ixon.Univ.FLAG_VAR idx (by decide)
      have htail : Reads
          (Ixon.getUnivFromTag (Ixon.getUnivFuel fuel)
            ⟨Ixon.Univ.FLAG_VAR, idx⟩)
          ByteArray.empty (Ixon.Univ.var idx) := by
        simpa [Ixon.getUnivFromTag, Ixon.Univ.FLAG_VAR] using
          Reads.pure (Ixon.Univ.var idx)
      have hall := Reads.bind
        (next := Ixon.getUnivFromTag (Ixon.getUnivFuel fuel)) htag htail
      simpa [Ixon.getUnivFuel, wireEncode, Ixon.Univ.FLAG_VAR] using hall

theorem serUniv_eq_wireEncode (u : Ixon.Univ) (h : WireWF u) :
    Ixon.serUniv u = wireEncode u := by
  exact (putUniv_writes u h).runPut

theorem getUniv_reads (u : Ixon.Univ) (h : WireWF u) :
    Reads Ixon.getUniv (wireEncode u) u := by
  intro before after
  unfold Ixon.getUniv
  change (EStateM.bind EStateM.get _) _ = _
  simp only [EStateM.bind, EStateM.get]
  have hfuel : (wireEncode u).size ≤
      (before ++ wireEncode u ++ after).size - before.size + 1 := by
    simp only [ByteArray.size_append]
    omega
  have hread := getUnivFuel_reads u h _ hfuel before after
  exact hread

/-- X1-U64: exact full-buffer universe round trip for every representable
    compressed successor count. -/
theorem deUniv_serUniv (u : Ixon.Univ) (h : WireWF u) :
    Ixon.deUniv (Ixon.serUniv u) = .ok u := by
  rw [serUniv_eq_wireEncode u h]
  unfold Ixon.deUniv Ixon.runGetExact
  have hread := getUniv_reads u h ByteArray.empty ByteArray.empty
  simp only [ByteArray.empty_append, ByteArray.append_empty,
    ByteArray.size_empty, Nat.zero_add] at hread
  change EStateM.run Ixon.getUniv { bytes := wireEncode u } = _ at hread
  rw [hread]
  simp

theorem SmallWireWF.toWireWF {u : Ixon.Univ} (h : SmallWireWF u) :
    WireWF u := by
  induction u with
  | zero => trivial
  | succ u ih =>
    constructor
    · exact Nat.lt_trans h.1 (by decide)
    · exact ih h.2
  | max left right ihLeft ihRight => exact ⟨ihLeft h.1, ihRight h.2⟩
  | imax left right ihLeft ihRight => exact ⟨ihLeft h.1, ihRight h.2⟩
  | var idx => trivial

theorem deUniv_serUniv_small_via_full (u : Ixon.Univ)
    (h : SmallWireWF u) :
    Ixon.deUniv (Ixon.serUniv u) = .ok u :=
  deUniv_serUniv u h.toWireWF

end Ixon.Univ

end Ix.Compile.Verify.Codec

namespace Ix.Compile.Verify

/-- Universe values whose compressed successor counts fit the v2 `UInt64`
    field.  Explicit variables are representable by construction. -/
abbrev UnivWireWF : Ixon.Univ → Prop :=
  Codec.Ixon.Univ.WireWF

/-- Universe values whose tags all use the one-byte TagN (`f = 2`) rung. -/
abbrev SmallUnivWireWF : Ixon.Univ → Prop :=
  Codec.Ixon.Univ.SmallWireWF

/-- X1-U64: exact full-buffer universe round trip across every TagN (`f = 2`)
    rung. -/
theorem deUniv_serUniv (u : Ixon.Univ) (h : UnivWireWF u) :
    Ixon.deUniv (Ixon.serUniv u) = .ok u :=
  Codec.Ixon.Univ.deUniv_serUniv u h

/-- X1-U8: exact full-buffer universe round trip for the one-byte tag domain.
    This domain contains `.succ .zero`, the encoding of `Sort 1`. -/
theorem deUniv_serUniv_small (u : Ixon.Univ) (h : SmallUnivWireWF u) :
    Ixon.deUniv (Ixon.serUniv u) = .ok u :=
  Codec.Ixon.Univ.deUniv_serUniv_small_via_full u h

/-- The first fixture's universe lies in the proved codec domain. -/
theorem sortOne_smallUnivWireWF :
    SmallUnivWireWF (.succ .zero) := by
  simp [SmallUnivWireWF, Codec.Ixon.Univ.SmallWireWF,
    Ixon.Univ.succCountNat]

theorem sortOne_univWireWF :
    UnivWireWF (.succ .zero) :=
  Codec.Ixon.Univ.SmallWireWF.toWireWF sortOne_smallUnivWireWF

theorem deUniv_serUniv_sortOne :
    Ixon.deUniv (Ixon.serUniv (.succ .zero)) = .ok (.succ .zero) :=
  deUniv_serUniv _ sortOne_univWireWF

end Ix.Compile.Verify
