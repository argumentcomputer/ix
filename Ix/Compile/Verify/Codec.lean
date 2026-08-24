import Ix.Ixon
import Std.Tactic.BVDecide

/-!
# Proof-visible v2 codecs

This first X1 slice makes universe serialization kernel-visible end to end.
`Reads` records exact cursor movement in arbitrary surrounding bytes, while
`Writes` records append-only writer behavior.  The public theorem covers the
one-byte `Tag2` domain, including the `Sort 1` universe needed by the first
standalone declaration fixture.  Larger trimmed tags remain a separate,
explicit arithmetic obligation.
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

theorem tag2_small_fields (flag : UInt8) (size : UInt64)
    (hflag : flag < 4) (hsize : size < 32) :
    (((flag <<< 6) ||| size.toUInt8) >>> 6) = flag ∧
    (((flag <<< 6) ||| size.toUInt8) &&& 0x20) = 0 ∧
    ((((flag <<< 6) ||| size.toUInt8) &&& 0x1f).toUInt64) = size := by
  rcases uint8_cases4 flag hflag with rfl | rfl | rfl | rfl <;>
    rcases uint64_cases32 size hsize with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem getTag2_reads_small (flag : UInt8) (size : UInt64)
    (hflag : flag < 4) (hsize : size < 32) :
    Reads Ixon.getTag2
      [((flag <<< 6) ||| size.toUInt8)].toByteArray
      ⟨flag, size⟩ := by
  intro before after
  unfold Ixon.getTag2
  change (EStateM.bind Ixon.getU8 _) _ = _
  rw [EStateM.bind, getU8_reads _ before after]
  obtain ⟨hdecodedFlag, hlarge, hdecodedSize⟩ :=
    tag2_small_fields flag size hflag hsize
  simp only [hdecodedFlag, hlarge]
  change (EStateM.bind (EStateM.pure _) _) _ = _
  simp only [EStateM.bind, EStateM.pure]
  change (EStateM.pure _) _ = _
  simp [EStateM.pure, hdecodedSize]

theorem runPut_putTag2_small (flag : UInt8) (size : UInt64)
    (hsize : size < 32) :
    Ixon.runPut (Ixon.putTag2 ⟨flag, size⟩) =
      [((flag <<< 6) ||| size.toUInt8)].toByteArray := by
  simp [Ixon.runPut, Ixon.putTag2, hsize, Ixon.putU8,
    StateT.run, StateT.modifyGet]
  change ByteArray.empty.push _ = _
  rfl

theorem putU8_writes (byte : UInt8) :
    Writes (Ixon.putU8 byte) [byte].toByteArray := by
  intro before
  simp only [Ixon.putU8, StateT.run]
  change StateT.modifyGet _ before = _
  simp [StateT.modifyGet]
  change ((), before.push byte) = _
  rfl

theorem putTag2_writes_small (flag : UInt8) (size : UInt64)
    (hsize : size < 32) :
    Writes (Ixon.putTag2 ⟨flag, size⟩)
      [((flag <<< 6) ||| size.toUInt8)].toByteArray := by
  unfold Ixon.putTag2
  rw [if_pos hsize]
  exact putU8_writes _

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
      putTag2_writes_small Ixon.Univ.FLAG_ZERO_SUCC 0 (by decide)
  | succ inner =>
    let u : Ixon.Univ := .succ inner
    have hcount : u.succCount < 32 := by
      exact nat_toUInt64_lt_32 h.1
    have htag : Writes (Ixon.putTag2 ⟨Ixon.Univ.FLAG_ZERO_SUCC,
        u.succCount⟩) [u.succCount.toUInt8].toByteArray := by
      simpa only [tag2_zero_header] using
        putTag2_writes_small Ixon.Univ.FLAG_ZERO_SUCC u.succCount hcount
    have hlt : sizeOf u.succBase < sizeOf u := by
      change sizeOf inner.succBase < 1 + sizeOf inner
      have hsize := Ixon.Univ.succBase_sizeOf_le inner
      omega
    have hbase := ih u.succBase hlt h.succBase
    simpa [u, Ixon.putUniv, smallEncode] using htag.bind hbase
  | max left right =>
    have htag : Writes (Ixon.putTag2 ⟨Ixon.Univ.FLAG_MAX, 0⟩)
        [0x40].toByteArray := by
      simpa only [tag2_max_zero_header] using
        putTag2_writes_small Ixon.Univ.FLAG_MAX 0 (by decide)
    have hleft := ih left (by simp_wf; omega) h.1
    have hright := ih right (by simp_wf; omega) h.2
    simpa [Ixon.putUniv, smallEncode, ByteArray.append_assoc] using
      htag.bind (hleft.bind hright)
  | imax left right =>
    have htag : Writes (Ixon.putTag2 ⟨Ixon.Univ.FLAG_IMAX, 0⟩)
        [0x80].toByteArray := by
      simpa only [tag2_imax_zero_header] using
        putTag2_writes_small Ixon.Univ.FLAG_IMAX 0 (by decide)
    have hleft := ih left (by simp_wf; omega) h.1
    have hright := ih right (by simp_wf; omega) h.2
    simpa [Ixon.putUniv, smallEncode, ByteArray.append_assoc] using
      htag.bind (hleft.bind hright)
  | var idx =>
    simpa only [Ixon.putUniv, smallEncode, tag2_var_header] using
      putTag2_writes_small Ixon.Univ.FLAG_VAR idx h

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
      have htag : Reads Ixon.getTag2 [0].toByteArray
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
      have htag : Reads Ixon.getTag2
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
      have htag : Reads Ixon.getTag2 [0x40].toByteArray
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
      have htag : Reads Ixon.getTag2 [0x80].toByteArray
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
      have htag : Reads Ixon.getTag2
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

end Ix.Compile.Verify.Codec

namespace Ix.Compile.Verify

/-- Universe values whose v2 tags all use the one-byte `Tag2` form. -/
abbrev SmallUnivWireWF : Ixon.Univ → Prop :=
  Codec.Ixon.Univ.SmallWireWF

/-- X1-U8: exact full-buffer universe round trip for the one-byte tag domain.
    This domain contains `.succ .zero`, the encoding of `Sort 1`. -/
theorem deUniv_serUniv_small (u : Ixon.Univ) (h : SmallUnivWireWF u) :
    Ixon.deUniv (Ixon.serUniv u) = .ok u :=
  Codec.Ixon.Univ.deUniv_serUniv_small u h

/-- The first fixture's universe lies in the proved codec domain. -/
theorem sortOne_smallUnivWireWF :
    SmallUnivWireWF (.succ .zero) := by
  simp [SmallUnivWireWF, Codec.Ixon.Univ.SmallWireWF,
    Ixon.Univ.succCountNat]

theorem deUniv_serUniv_sortOne :
    Ixon.deUniv (Ixon.serUniv (.succ .zero)) = .ok (.succ .zero) :=
  deUniv_serUniv_small _ sortOne_smallUnivWireWF

end Ix.Compile.Verify
