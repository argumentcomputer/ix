import IxCC.Rt.Readback
import IxCC.Rt.Rc.Array.Invariant
import IxCC.BigNat.Proof.Basic

/-! # Readback for Contiguous Arrays, ByteArrays, UTF-8 Strings, and BigNat Limb Cells

Extends `IxCC.Rt.Readback` to read back all three native contiguous array kinds
(both live dynamic cells in the counted heap and immortal static cells in ELF
`.rodata`):

* `readbackByteArray` / `readbackByteArrayObs`: reads a `ByteArray` cell
  (`scan = 0`, `tag = 0x7F02`) into `ByteArray` or `Sem.Obs.bytes`.
* `readbackString`: reads a `ByteArray` cell and validates UTF-8 via
  `String.fromUTF8?` (DR4).
* `readbackLimbArray`: reads an unboxed `Array UInt64` limb cell
  (`scan = 0`, `tag = 0x7F03`) into `Array UInt64`.
* `readbackBigNat`: unified `Nat` readback supporting BOTH small immediate odd
  words (`n < 2^63`, matching `Rt.readback`) AND canonical `BigNat` limb cells
  (`n ≥ 2^63`, dynamic or static `.rodata`), proving exact threshold separation
  and value agreement.
* `readbackBoxedArray`: reads a boxed `Array α` cell (`scan = 0xFF`,
  `tag = 0x7F01`) element-by-element via `Rt.readback`. -/

set_option autoImplicit false

namespace IxCC.Rt.Readback

open IxCC.Lir (Word)
open IxCC.Rt (Sig FoTy readback natWord natLimit)
open IxCC.Rt.Proof (WordAt addr_toNat)
open IxCC.Rt.Rc.Array
open IxCC.Sem (Obs)
open IxCC.X86 (Memory)

/-! ## Readback functions -/

/-- Helper: read `n` consecutive bytes starting at `addr + 24`. -/
def readBytesRange (m : Memory) (addr : Word) (n : Nat) : Option (List UInt8) :=
  (List.range n).mapM fun j =>
    match m.read? .w8 (addr + UInt64.ofNat (arrayPayloadOffset + j)) with
    | .ok w => some w.toUInt8
    | .error _ => none

/-- Helper: read `n` consecutive 64-bit words starting at `addr + 24`. -/
def readWordsRange (m : Memory) (addr : Word) (n : Nat) : Option (List Word) :=
  (List.range n).mapM fun j =>
    match m.read64? (addr + UInt64.ofNat (arrayPayloadOffset + 8 * j)) with
    | .ok w => some w
    | .error _ => none

/-- Read back a contiguous `ByteArray` cell (dynamic or static `.rodata`). -/
def readbackByteArray (m : Memory) (addr : Word) : Option ByteArray :=
  if addr &&& 1 == 1 then none
  else
    match m.read64? addr, m.read64? (addr + 8), m.read64? (addr + 16) with
    | .ok h, .ok sz, .ok cap =>
        let scan := (h &&& 0xFF).toNat
        let tag := ((h >>> 16) &&& 0xFFFF).toNat
        if scan == ArrayKind.bytes.scan && tag == ArrayKind.bytes.tag && sz.toNat ≤ cap.toNat then
          (readBytesRange m addr sz.toNat).map fun bs => ByteArray.mk bs.toArray
        else none
    | _, _, _ => none

/-- Read back a `ByteArray` cell directly as a `Sem.Obs.bytes` observation. -/
def readbackByteArrayObs (m : Memory) (addr : Word) : Option Obs :=
  (readbackByteArray m addr).map fun bs => .bytes bs.data.toList

/-- Read back a UTF-8 `String` cell (DR4) backed by a `ByteArray` cell. -/
def readbackString (m : Memory) (addr : Word) : Option String :=
  (readbackByteArray m addr).bind String.fromUTF8?

/-- Read back an unboxed `Array UInt64` / `BigNat` limb cell (dynamic or static `.rodata`). -/
def readbackLimbArray (m : Memory) (addr : Word) : Option (Array UInt64) :=
  if addr &&& 1 == 1 then none
  else
    match m.read64? addr, m.read64? (addr + 8), m.read64? (addr + 16) with
    | .ok h, .ok sz, .ok cap =>
        let scan := (h &&& 0xFF).toNat
        let tag := ((h >>> 16) &&& 0xFFFF).toNat
        if scan == ArrayKind.limbs.scan && tag == ArrayKind.limbs.tag && sz.toNat ≤ cap.toNat then
          (readWordsRange m addr sz.toNat).map List.toArray
        else none
    | _, _, _ => none

/-- Decidable canonical check for a non-empty `BigNat` (`WF` and `≥ 2^63`). -/
def isCanonicalBigNat (limbs : Array UInt64) : Bool :=
  if h : 0 < limbs.size then
    decide (limbs[limbs.size - 1]'(Nat.sub_lt h Nat.one_pos) ≠ 0) &&
      (BigNat.toSmall? limbs).isNone
  else false

/-- Unified `Nat` readback:
* odd word `2n + 1`: small `Nat` `n < 2^63` (exact match to `Rt.readback`);
* even pointer: canonical `BigNat` limb cell (`WF`, `toNat ≥ 2^63`) in dynamic
  heap or static `.rodata`. -/
def readbackBigNat (m : Memory) (w : Word) : Option Nat :=
  if w &&& 1 == 1 then
    some (w >>> 1).toNat
  else
    match readbackLimbArray m w with
    | some limbs =>
        if isCanonicalBigNat limbs then some (BigNat.toNat limbs) else none
    | none => none

/-- Unified `Nat` readback into `Sem.Obs.nat`. -/
def readbackBigNatObs (m : Memory) (w : Word) : Option Obs :=
  (readbackBigNat m w).map .nat

/-- Read back a boxed `Array α` cell element-by-element via `Rt.readback`. -/
def readbackBoxedArray (sig : Sig) (fuel : Nat) (m : Memory) (elemTy : FoTy) (addr : Word) :
    Option (List Obs) :=
  if addr &&& 1 == 1 then none
  else
    match m.read64? addr, m.read64? (addr + 8), m.read64? (addr + 16) with
    | .ok h, .ok sz, .ok cap =>
        let scan := (h &&& 0xFF).toNat
        let tag := ((h >>> 16) &&& 0xFFFF).toNat
        if scan == ArrayKind.boxed.scan && tag == ArrayKind.boxed.tag && sz.toNat ≤ cap.toNat then
          (readWordsRange m addr sz.toNat).bind fun ws =>
            ws.mapM (readback sig fuel m elemTy)
        else none
    | _, _, _ => none

/-! ## Range readback lemmas -/

private theorem mapM_range_eq_some {α : Type} (xs : List α) (f : Nat → Option α)
    (h : ∀ (j : Nat) (hj : j < xs.length), f j = some (xs[j]'hj)) :
    (List.range xs.length).mapM f = some xs := by
  have aux : ∀ (n : Nat) (hn : n ≤ xs.length),
      (List.range n).mapM f = some (xs.take n) := by
    intro n hn
    induction n with
    | zero => rfl
    | succ k ih =>
      rw [List.range_succ, List.mapM_append, ih (by omega)]
      simp only [List.mapM_cons, List.mapM_nil, bind, Option.bind, pure, h k (by omega)]
      congr 1
      exact (List.take_succ_eq_append_getElem (by omega : k < xs.length)).symm
  simpa [List.take_length] using aux xs.length (Nat.le_refl _)

theorem readBytesRange_of_payload {m : Memory} {addr : Word} {data : List UInt8}
    (hp : ArrayPayload m addr (.bytes data)) :
    readBytesRange m addr data.length = some data := by
  unfold readBytesRange
  apply mapM_range_eq_some
  intro j hj
  rw [(hp j hj).read8]
  dsimp only
  congr 1
  apply UInt8.toNat_inj.mp
  rw [UInt64.toNat_toUInt8, UInt8.toNat_toUInt64]
  exact Nat.mod_eq_of_lt (UInt8.toNat_lt _)

theorem readWordsRange_of_limbs {m : Memory} {addr : Word} {limbs : List Word}
    (hp : ArrayPayload m addr (.limbs limbs)) :
    readWordsRange m addr limbs.length = some limbs := by
  unfold readWordsRange
  apply mapM_range_eq_some
  intro j hj
  have hread := (hp j hj).read64
  change (match m.read? .w64 (addr + UInt64.ofNat (arrayPayloadOffset + 8 * j)) with
    | .ok w => some w
    | .error _ => none) = some limbs[j]
  rw [hread]

theorem readWordsRange_of_boxed {m : Memory} {addr : Word} {elems : List Word}
    (hp : ArrayPayload m addr (.boxed elems)) :
    readWordsRange m addr elems.length = some elems := by
  unfold readWordsRange
  apply mapM_range_eq_some
  intro j hj
  have hread := (hp j hj).read64
  change (match m.read? .w64 (addr + UInt64.ofNat (arrayPayloadOffset + 8 * j)) with
    | .ok w => some w
    | .error _ => none) = some elems[j]
  rw [hread]

private theorem even_word_tag_false {addr : Word} (hal : addr.toNat % 8 = 0) :
    (addr &&& 1 == 1) = false := by
  have hbit : (addr &&& 1).toNat = 0 := by
    rw [UInt64.toNat_and, show (UInt64.toNat 1) = 2 ^ 1 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    omega
  have hzero : addr &&& 1 = 0 := UInt64.toNat_inj.mp hbit
  rw [hzero]
  rfl

private theorem ofNat_toNat_lt63 {n : Nat} (h : n < 2 ^ 63) :
    (UInt64.ofNat n).toNat = n := by
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

/-! ## `ByteArray` and `String` readback proofs -/

theorem readbackByteArray_live {m : Memory} {addr : Word} {refs cls cap : Nat} {data : List UInt8}
    (h : LiveArrayCell m addr refs cls cap (.bytes data)) :
    readbackByteArray m addr = some (ByteArray.mk data.toArray) := by
  have hev := even_word_tag_false h.aligned
  have hhdr : m.read64? addr = .ok (arrayHeader .bytes cls refs) := h.header_word.read64
  have hsz : m.read64? (addr + 8) = .ok (UInt64.ofNat data.length) := h.size_word.read64
  have hcap : m.read64? (addr + 16) = .ok (UInt64.ofNat cap) := h.cap_word.read64
  have hf := arrayHeader_fields (k := .bytes) h.cls_hi h.refs_pos h.refs_le
  have hbytes := (arrayBytes_eq_classBytes h.cls_lo h.cls_hi).2
  have hcap_lt : cap < 2 ^ 63 := by
    have := h.fit; have := h.cap_fit; unfold arrayPayloadOffset at hbytes; omega
  have hsz_le : data.length ≤ cap := h.size_le
  have hsz_nat : (UInt64.ofNat data.length).toNat = data.length := ofNat_toNat_lt63 (by omega)
  have hcap_nat : (UInt64.ofNat cap).toNat = cap := ofNat_toNat_lt63 hcap_lt
  unfold readbackByteArray
  rw [hev, ite_eq_right (fun h => absurd h Bool.false_ne_true), hhdr, hsz, hcap]
  simp only [hf.1, hf.2.2.1, hsz_nat, hcap_nat, beq_self_eq_true, Bool.true_and,
    decide_eq_true hsz_le, ↓reduceIte, readBytesRange_of_payload h.payload, Option.map_some]

theorem readbackByteArray_static {m : Memory} {addr : Word} {cap : Nat} {data : List UInt8}
    (h : StaticArrayCell m addr cap (.bytes data)) :
    readbackByteArray m addr = some (ByteArray.mk data.toArray) := by
  have hev := even_word_tag_false h.aligned
  have hhdr : m.read64? addr = .ok (staticArrayHeader .bytes) := h.header_word.read64
  have hsz : m.read64? (addr + 8) = .ok (UInt64.ofNat data.length) := h.size_word.read64
  have hcap : m.read64? (addr + 16) = .ok (UInt64.ofNat cap) := h.cap_word.read64
  have hf := staticArrayHeader_fields .bytes
  have hcap_lt : cap < 2 ^ 63 := by
    have := h.fit; simp [arrayPayloadOffset] at this; omega
  have hsz_le : data.length ≤ cap := h.size_le
  have hsz_nat : (UInt64.ofNat data.length).toNat = data.length := ofNat_toNat_lt63 (by omega)
  have hcap_nat : (UInt64.ofNat cap).toNat = cap := ofNat_toNat_lt63 hcap_lt
  unfold readbackByteArray
  rw [hev, ite_eq_right (fun h => absurd h Bool.false_ne_true), hhdr, hsz, hcap]
  simp only [hf.1, hf.2.2.1, hsz_nat, hcap_nat, beq_self_eq_true, Bool.true_and,
    decide_eq_true hsz_le, ↓reduceIte, readBytesRange_of_payload h.payload, Option.map_some]

theorem readbackByteArrayObs_live {m : Memory} {addr : Word} {refs cls cap : Nat}
    {data : List UInt8} (h : LiveArrayCell m addr refs cls cap (.bytes data)) :
    readbackByteArrayObs m addr = some (.bytes data) := by
  simp [readbackByteArrayObs, readbackByteArray_live h]

theorem readbackByteArrayObs_static {m : Memory} {addr : Word} {cap : Nat}
    {data : List UInt8} (h : StaticArrayCell m addr cap (.bytes data)) :
    readbackByteArrayObs m addr = some (.bytes data) := by
  simp [readbackByteArrayObs, readbackByteArray_static h]

private theorem fromUTF8?_toByteArray_self (s : String) :
    String.fromUTF8? s.toByteArray = some s := by
  have h1 : String.fromUTF8 s.toByteArray s.isValidUTF8 = s := by cases s; rfl
  simp [String.fromUTF8?, s.isValidUTF8, h1]

theorem readbackString_static {m : Memory} {addr : Word} {cap : Nat} {s : String}
    (h : StaticArrayCell m addr cap (.bytes s.toByteArray.data.toList)) :
    readbackString m addr = some s := by
  have hbs : ByteArray.mk s.toByteArray.data.toList.toArray = s.toByteArray := by
    cases s.toByteArray with
    | mk arr => simp
  simp [readbackString, readbackByteArray_static h, hbs, fromUTF8?_toByteArray_self]

theorem readbackString_live {m : Memory} {addr : Word} {refs cls cap : Nat} {s : String}
    (h : LiveArrayCell m addr refs cls cap (.bytes s.toByteArray.data.toList)) :
    readbackString m addr = some s := by
  have hbs : ByteArray.mk s.toByteArray.data.toList.toArray = s.toByteArray := by
    cases s.toByteArray with
    | mk arr => simp
  simp [readbackString, readbackByteArray_live h, hbs, fromUTF8?_toByteArray_self]

/-! ## `Array UInt64` (`LimbArray`) and `BigNat` readback proofs -/

theorem readbackLimbArray_live {m : Memory} {addr : Word} {refs cls cap : Nat} {limbs : List Word}
    (h : LiveArrayCell m addr refs cls cap (.limbs limbs)) :
    readbackLimbArray m addr = some limbs.toArray := by
  have hev := even_word_tag_false h.aligned
  have hhdr : m.read64? addr = .ok (arrayHeader .limbs cls refs) := h.header_word.read64
  have hsz : m.read64? (addr + 8) = .ok (UInt64.ofNat limbs.length) := h.size_word.read64
  have hcap : m.read64? (addr + 16) = .ok (UInt64.ofNat cap) := h.cap_word.read64
  have hf := arrayHeader_fields (k := .limbs) h.cls_hi h.refs_pos h.refs_le
  have hbytes := (arrayBytes_eq_classBytes h.cls_lo h.cls_hi).1
  have hcap_lt : cap < 2 ^ 63 := by
    have := h.fit; have := h.cap_fit; unfold arrayPayloadOffset at hbytes; omega
  have hsz_le : limbs.length ≤ cap := h.size_le
  have hsz_nat : (UInt64.ofNat limbs.length).toNat = limbs.length := ofNat_toNat_lt63 (by omega)
  have hcap_nat : (UInt64.ofNat cap).toNat = cap := ofNat_toNat_lt63 hcap_lt
  unfold readbackLimbArray
  rw [hev, ite_eq_right (fun h => absurd h Bool.false_ne_true), hhdr, hsz, hcap]
  simp only [hf.1, hf.2.2.1, hsz_nat, hcap_nat, beq_self_eq_true, Bool.true_and,
    decide_eq_true hsz_le, ↓reduceIte, readWordsRange_of_limbs h.payload, Option.map_some]

theorem readbackLimbArray_static {m : Memory} {addr : Word} {cap : Nat} {limbs : List Word}
    (h : StaticArrayCell m addr cap (.limbs limbs)) :
    readbackLimbArray m addr = some limbs.toArray := by
  have hev := even_word_tag_false h.aligned
  have hhdr : m.read64? addr = .ok (staticArrayHeader .limbs) := h.header_word.read64
  have hsz : m.read64? (addr + 8) = .ok (UInt64.ofNat limbs.length) := h.size_word.read64
  have hcap : m.read64? (addr + 16) = .ok (UInt64.ofNat cap) := h.cap_word.read64
  have hf := staticArrayHeader_fields .limbs
  have hcap_lt : cap < 2 ^ 63 := by
    have := h.fit; simp [arrayPayloadOffset] at this; omega
  have hsz_le : limbs.length ≤ cap := h.size_le
  have hsz_nat : (UInt64.ofNat limbs.length).toNat = limbs.length := ofNat_toNat_lt63 (by omega)
  have hcap_nat : (UInt64.ofNat cap).toNat = cap := ofNat_toNat_lt63 hcap_lt
  unfold readbackLimbArray
  rw [hev, ite_eq_right (fun h => absurd h Bool.false_ne_true), hhdr, hsz, hcap]
  simp only [hf.1, hf.2.2.1, hsz_nat, hcap_nat, beq_self_eq_true, Bool.true_and,
    decide_eq_true hsz_le, ↓reduceIte, readWordsRange_of_limbs h.payload, Option.map_some]

theorem isCanonicalBigNat_iff (limbs : Array UInt64) :
    isCanonicalBigNat limbs = true ↔ BigNat.WF limbs ∧ 2 ^ 63 ≤ BigNat.toNat limbs := by
  unfold isCanonicalBigNat
  constructor
  · intro h
    split at h
    · rename_i hpos
      simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at h
      have hwf : BigNat.WF limbs := by
        right
        rw [BigNat.getLimb_lt (Nat.sub_lt hpos Nat.one_pos)]
        exact h.1
      have hsm := BigNat.toSmall?_spec limbs hwf
      rw [h.2] at hsm
      by_cases hlt : BigNat.toNat limbs < 2 ^ 63
      · simp [hlt] at hsm
      · exact ⟨hwf, by omega⟩
    · cases h
  · rintro ⟨hwf, hge⟩
    have hpos : 0 < limbs.size := by
      cases hsz : limbs.size with
      | zero =>
        have : BigNat.toNat limbs = 0 := by simp [BigNat.toNat, hsz]
        omega
      | succ _ => exact Nat.succ_pos _
    rw [dite_eq_left hpos]
    simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none]
    refine ⟨?_, ?_⟩
    · rcases hwf with h0 | htop
      · omega
      · rwa [BigNat.getLimb_lt (Nat.sub_lt hpos Nat.one_pos)] at htop
    · rw [BigNat.toSmall?_spec limbs hwf]
      have hnot : ¬ BigNat.toNat limbs < 2 ^ 63 := by omega
      simp [hnot]

/-- Small odd `Nat` words (`n < 2^63`) read back via `readbackBigNat` identically to `Rt.readback`. -/
theorem readbackBigNat_small {m : Memory} {n : Nat} {w : Word} (h : natWord n = some w) :
    readbackBigNat m w = some n := by
  obtain ⟨h1, h2⟩ := Rt.odd_word (Rt.natWord_toNat h)
  unfold readbackBigNat
  simp [h1, h2]

/-- A live dynamic `LimbArray` cell holding a canonical `BigNat` (`≥ 2^63`)
reads back to its exact mathematical `Nat` value. -/
theorem readbackBigNat_big_live {m : Memory} {addr : Word} {refs cls cap : Nat}
    {limbs : List Word} (h : LiveArrayCell m addr refs cls cap (.limbs limbs))
    (hwf : BigNat.WF limbs.toArray) (hge : 2 ^ 63 ≤ BigNat.toNat limbs.toArray) :
    readbackBigNat m addr = some (BigNat.toNat limbs.toArray) := by
  have hev := even_word_tag_false h.aligned
  unfold readbackBigNat
  rw [hev, ite_eq_right (fun h => absurd h Bool.false_ne_true), readbackLimbArray_live h]
  have hcan := (isCanonicalBigNat_iff limbs.toArray).mpr ⟨hwf, hge⟩
  simp [hcan]

/-- An immortal static `.rodata` `LimbArray` cell holding a canonical `BigNat`
(`≥ 2^63`) reads back to its exact mathematical `Nat` value. -/
theorem readbackBigNat_big_static {m : Memory} {addr : Word} {cap : Nat}
    {limbs : List Word} (h : StaticArrayCell m addr cap (.limbs limbs))
    (hwf : BigNat.WF limbs.toArray) (hge : 2 ^ 63 ≤ BigNat.toNat limbs.toArray) :
    readbackBigNat m addr = some (BigNat.toNat limbs.toArray) := by
  have hev := even_word_tag_false h.aligned
  unfold readbackBigNat
  rw [hev, ite_eq_right (fun h => absurd h Bool.false_ne_true), readbackLimbArray_static h]
  have hcan := (isCanonicalBigNat_iff limbs.toArray).mpr ⟨hwf, hge⟩
  simp [hcan]

/-- Exact threshold separation: odd words always denote `< 2^63`, while even
pointers read back by `readbackBigNat` always denote `≥ 2^63` with canonical
`limbs = BigNat.ofNat n`. -/
theorem readbackBigNat_threshold {m : Memory} {w : Word} {n : Nat}
    (h : readbackBigNat m w = some n) :
    (w &&& 1 = 1 ∧ n < 2 ^ 63) ∨
      (w &&& 1 = 0 ∧ 2 ^ 63 ≤ n ∧ readbackLimbArray m w = some (BigNat.ofNat n)) := by
  unfold readbackBigNat at h
  by_cases hodd : (w &&& 1 == 1) = true
  · simp only [hodd, ↓reduceIte] at h
    have hn : (w >>> 1).toNat = n := Option.some.inj h
    left
    refine ⟨beq_iff_eq.mp hodd, ?_⟩
    rw [← hn, UInt64.toNat_shiftRight, show (UInt64.toNat 1) % 64 = 1 from rfl,
      Nat.shiftRight_eq_div_pow]
    have hw := w.toNat_lt_size
    simp only [UInt64.size] at hw
    omega
  · have hodd_f : (w &&& 1 == 1) = false := Bool.eq_false_iff.mpr hodd
    simp only [hodd_f, Bool.false_eq_true, ↓reduceIte] at h
    have heven : w &&& 1 = 0 := by
      have hlt2 : (w &&& 1).toNat < 2 := by
        rw [UInt64.toNat_and, show (UInt64.toNat 1) = 2 ^ 1 - 1 from rfl,
          Nat.and_two_pow_sub_one_eq_mod]
        omega
      have hne1 : w &&& 1 ≠ 1 := by
        intro heq; rw [heq] at hodd_f; cases hodd_f
      apply UInt64.toNat_inj.mp
      have hne1' : (w &&& 1).toNat ≠ 1 := fun e => hne1 (UInt64.toNat_inj.mp e)
      rw [show (0 : Word).toNat = 0 from rfl]
      omega
    cases hl : readbackLimbArray m w with
    | none => rw [hl] at h; cases h
    | some limbs =>
      rw [hl] at h
      cases hcan : isCanonicalBigNat limbs with
      | false => simp only [hcan, Bool.false_eq_true, ↓reduceIte] at h; cases h
      | true =>
        simp only [hcan, ↓reduceIte] at h
        obtain ⟨hwf, hge⟩ := (isCanonicalBigNat_iff limbs).mp hcan
        have hn : BigNat.toNat limbs = n := Option.some.inj h
        have hlimbs_eq : limbs = BigNat.ofNat n := by
          apply BigNat.toNat_inj hwf (BigNat.wf_ofNat n)
          rw [hn, BigNat.toNat_ofNat]
        right
        exact ⟨heven, by omega, by rw [hlimbs_eq]⟩

/-! ## Boxed `Array` readback proofs -/

theorem readbackBoxedArray_live {sig : Sig} {fuel : Nat} {m : Memory} {elemTy : FoTy}
    {addr : Word} {refs cls cap : Nat} {elems : List Word}
    (h : LiveArrayCell m addr refs cls cap (.boxed elems)) :
    readbackBoxedArray sig fuel m elemTy addr = elems.mapM (readback sig fuel m elemTy) := by
  have hev := even_word_tag_false h.aligned
  have hhdr : m.read64? addr = .ok (arrayHeader .boxed cls refs) := h.header_word.read64
  have hsz : m.read64? (addr + 8) = .ok (UInt64.ofNat elems.length) := h.size_word.read64
  have hcap : m.read64? (addr + 16) = .ok (UInt64.ofNat cap) := h.cap_word.read64
  have hf := arrayHeader_fields (k := .boxed) h.cls_hi h.refs_pos h.refs_le
  have hbytes := (arrayBytes_eq_classBytes h.cls_lo h.cls_hi).1
  have hcap_lt : cap < 2 ^ 63 := by
    have := h.fit; have := h.cap_fit; unfold arrayPayloadOffset at hbytes; omega
  have hsz_le : elems.length ≤ cap := h.size_le
  have hsz_nat : (UInt64.ofNat elems.length).toNat = elems.length := ofNat_toNat_lt63 (by omega)
  have hcap_nat : (UInt64.ofNat cap).toNat = cap := ofNat_toNat_lt63 hcap_lt
  unfold readbackBoxedArray
  rw [hev, ite_eq_right (fun h => absurd h Bool.false_ne_true), hhdr, hsz, hcap]
  simp only [hf.1, hf.2.2.1, hsz_nat, hcap_nat, beq_self_eq_true, Bool.true_and,
    decide_eq_true hsz_le, ↓reduceIte, readWordsRange_of_boxed h.payload, Option.bind_some]

theorem readbackBoxedArray_static {sig : Sig} {fuel : Nat} {m : Memory} {elemTy : FoTy}
    {addr : Word} {cap : Nat} {elems : List Word}
    (h : StaticArrayCell m addr cap (.boxed elems)) :
    readbackBoxedArray sig fuel m elemTy addr = elems.mapM (readback sig fuel m elemTy) := by
  have hev := even_word_tag_false h.aligned
  have hhdr : m.read64? addr = .ok (staticArrayHeader .boxed) := h.header_word.read64
  have hsz : m.read64? (addr + 8) = .ok (UInt64.ofNat elems.length) := h.size_word.read64
  have hcap : m.read64? (addr + 16) = .ok (UInt64.ofNat cap) := h.cap_word.read64
  have hf := staticArrayHeader_fields .boxed
  have hcap_lt : cap < 2 ^ 63 := by
    have := h.fit; simp [arrayPayloadOffset] at this; omega
  have hsz_le : elems.length ≤ cap := h.size_le
  have hsz_nat : (UInt64.ofNat elems.length).toNat = elems.length := ofNat_toNat_lt63 (by omega)
  have hcap_nat : (UInt64.ofNat cap).toNat = cap := ofNat_toNat_lt63 hcap_lt
  unfold readbackBoxedArray
  rw [hev, ite_eq_right (fun h => absurd h Bool.false_ne_true), hhdr, hsz, hcap]
  simp only [hf.1, hf.2.2.1, hsz_nat, hcap_nat, beq_self_eq_true, Bool.true_and,
    decide_eq_true hsz_le, ↓reduceIte, readWordsRange_of_boxed h.payload, Option.bind_some]

end IxCC.Rt.Readback
