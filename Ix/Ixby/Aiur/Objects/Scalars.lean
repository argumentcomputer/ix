module
public import Ix.Ixby.Aiur.Objects.CodeHeaders
import all Ix.Aiur.Goldilocks

/-! Checked scalar-literal decoding for the object interpreter.

The statements concern the actual Lean bytecode evaluator. Genuine bytes
remain an explicit premise, supplied by the separate checked loader; no
compiler, gadget, trace, AIR, or authenticated whole-image theorem is assumed.
-/

namespace Ix.Ixby.AiurBackend.Objects.Scalars

deriving instance DecidableEq for Aiur.Bytecode.Op

public section
@[expose] section

open Aiur Aiur.Bytecode Aiur.Bytecode.Eval Ix.Ixby
open Objects.Refinement Objects.Memory Objects.Store Objects.Table Objects.Parser
open Objects.Identity Objects.Equality Objects.Unique Objects.CodeHeaders

/-- Eight genuine little-endian bytes, including noncanonical encodings. -/
structure FieldBytes where
  a : UInt8
  b : UInt8
  c : UInt8
  d : UInt8
  e : UInt8
  f : UInt8
  g : UInt8
  h : UInt8

def FieldBytes.bytes (w : FieldBytes) : List UInt8 :=
  [w.a, w.b, w.c, w.d, w.e, w.f, w.g, w.h]
def FieldBytes.value (w : FieldBytes) : Nat :=
  w.a.toNat + (256 * w.b.toNat + (65536 * w.c.toNat + (16777216 * w.d.toNat +
    (4294967296 * w.e.toNat + (1099511627776 * w.f.toNat +
      (281474976710656 * w.g.toNat + 72057594037927936 * w.h.toNat))))))
def packedField (a b c d e f g h : G) : G :=
  a + (256 * b + (65536 * c + (16777216 * d + (4294967296 * e +
    (1099511627776 * f + (281474976710656 * g + 72057594037927936 * h))))))
def FieldBytes.field (w : FieldBytes) : G :=
  packedField (.ofUInt8 w.a) (.ofUInt8 w.b) (.ofUInt8 w.c) (.ofUInt8 w.d)
    (.ofUInt8 w.e) (.ofUInt8 w.f) (.ofUInt8 w.g) (.ofUInt8 w.h)

theorem field_bytes_length (w : FieldBytes) : w.bytes.length = 8 := rfl

private theorem of_nat_add (a b : Nat) : G.ofNat a + G.ofNat b = G.ofNat (a + b) := by
  apply field_n_injective
  change (G.ofNat ((G.ofNat a).n + (G.ofNat b).n)).n = _
  simp only [field_of_nat_mod, Nat.add_mod, Nat.mod_mod]

private theorem of_nat_mul (a b : Nat) : G.ofNat a * G.ofNat b = G.ofNat (a * b) := by
  apply field_n_injective
  change (G.ofNat ((G.ofNat a).n * (G.ofNat b).n)).n = _
  simp only [field_of_nat_mod, Nat.mul_mod, Nat.mod_mod]

private theorem of_byte (a : UInt8) : G.ofUInt8 a = G.ofNat a.toNat := by
  apply field_n_injective
  rw [byte_field_exact, field_of_nat_exact _ (by have := a.toNat_lt; change a.toNat < 18446744069414584321; omega)]

/-- Packing itself reduces modulo p; the preceding guard is essential. -/
theorem packed_field_mod (w : FieldBytes) : w.field.n = w.value % goldilocksModulus := by
  simp only [FieldBytes.field, packedField, of_byte]
  change (G.ofNat w.a.toNat + (G.ofNat 256 * G.ofNat w.b.toNat +
    (G.ofNat 65536 * G.ofNat w.c.toNat + (G.ofNat 16777216 * G.ofNat w.d.toNat +
    (G.ofNat 4294967296 * G.ofNat w.e.toNat + (G.ofNat 1099511627776 * G.ofNat w.f.toNat +
    (G.ofNat 281474976710656 * G.ofNat w.g.toNat + G.ofNat 72057594037927936 * G.ofNat w.h.toNat))))))).n = _
  simp only [of_nat_mul, of_nat_add, field_of_nat_mod, FieldBytes.value]

theorem field_bytes_codec (w : FieldBytes) : w.value = natOfBytesLE w.bytes.toArray := by
  simp [FieldBytes.value, FieldBytes.bytes, natOfBytesLE]
  omega

theorem canonical_field_exact (w : FieldBytes) (canonical : w.value < goldilocksModulus) :
    w.field.n = w.value := by rw [packed_field_mod, Nat.mod_eq_of_lt canonical]

def highTest (e f g h : G) : G := e + (f + (g + (h - 1020)))
def lowTest (a b c d : G) : G := a + (b + (c + d))
def fieldGuard (a b c d e f g h : G) : G :=
  1 - (if (highTest e f g h).val == 0 then 1 else 0) *
    (1 - (if (lowTest a b c d).val == 0 then 1 else 0))

private theorem add_exact (a b : G) (bound : a.n + b.n < goldilocksModulus) :
    (a + b).n = a.n + b.n := field_of_nat_exact _ bound

private theorem high_test_zero (e f g h : UInt8) :
    (highTest (.ofUInt8 e) (.ofUInt8 f) (.ofUInt8 g) (.ofUInt8 h)).val = 0 ↔
      e.toNat + f.toNat + g.toNat + h.toNat = 1020 := by
  have he := e.toNat_lt
  have hf := f.toNat_lt
  have hg := g.toNat_lt
  have hh := h.toNat_lt
  have sub : (G.ofUInt8 h - 1020).n = h.toNat + goldilocksModulus - 1020 := by
    change (G.ofNat ((G.ofUInt8 h).n + gSize.toNat - (1020 : G).n)).n = _
    rw [byte_field_exact]
    exact field_of_nat_exact _ (by change h.toNat + 18446744069414584321 - 1020 < 18446744069414584321; omega)
  have s1 := add_exact (G.ofUInt8 g) (G.ofUInt8 h - 1020) (by
    rw [byte_field_exact, sub]; change g.toNat + (h.toNat + 18446744069414584321 - 1020) < 18446744069414584321; omega)
  have s2 := add_exact (G.ofUInt8 f) (G.ofUInt8 g + (G.ofUInt8 h - 1020)) (by
    rw [s1, byte_field_exact, byte_field_exact, sub]
    change f.toNat + (g.toNat + (h.toNat + 18446744069414584321 - 1020)) < 18446744069414584321; omega)
  have last : (highTest (.ofUInt8 e) (.ofUInt8 f) (.ofUInt8 g) (.ofUInt8 h)).n =
      (e.toNat + f.toNat + g.toNat + h.toNat + goldilocksModulus - 1020) % goldilocksModulus := by
    change (G.ofNat ((G.ofUInt8 e).n + (G.ofUInt8 f + (G.ofUInt8 g + (G.ofUInt8 h - 1020))).n)).n = _
    rw [field_of_nat_mod, s2, s1, byte_field_exact, byte_field_exact, byte_field_exact, sub]
    apply congrArg (fun n => n % goldilocksModulus)
    change e.toNat + (f.toNat + (g.toNat + (h.toNat + 18446744069414584321 - 1020))) =
      e.toNat + f.toNat + g.toNat + h.toNat + 18446744069414584321 - 1020
    omega
  rw [← UInt64.toNat_inj]
  change (highTest (.ofUInt8 e) (.ofUInt8 f) (.ofUInt8 g) (.ofUInt8 h)).n = 0 ↔ _
  rw [last]
  by_cases full : e.toNat + f.toNat + g.toNat + h.toNat = 1020
  · simp [full]
  · rw [Nat.mod_eq_of_lt (by change e.toNat + f.toNat + g.toNat + h.toNat + 18446744069414584321 - 1020 < 18446744069414584321; omega)]
    change e.toNat + f.toNat + g.toNat + h.toNat + 18446744069414584321 - 1020 = 0 ↔ _
    omega

private theorem low_test_zero (a b c d : UInt8) :
    (lowTest (.ofUInt8 a) (.ofUInt8 b) (.ofUInt8 c) (.ofUInt8 d)).val = 0 ↔
      a.toNat + b.toNat + c.toNat + d.toNat = 0 := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  have s1 := add_exact (G.ofUInt8 c) (G.ofUInt8 d) (by
    rw [byte_field_exact, byte_field_exact]; change c.toNat + d.toNat < 18446744069414584321; omega)
  have s2 := add_exact (G.ofUInt8 b) (G.ofUInt8 c + G.ofUInt8 d) (by
    rw [s1, byte_field_exact, byte_field_exact, byte_field_exact]
    change b.toNat + (c.toNat + d.toNat) < 18446744069414584321; omega)
  have s3 := add_exact (G.ofUInt8 a) (G.ofUInt8 b + (G.ofUInt8 c + G.ofUInt8 d)) (by
    rw [s2, s1, byte_field_exact, byte_field_exact, byte_field_exact, byte_field_exact]
    change a.toNat + (b.toNat + (c.toNat + d.toNat)) < 18446744069414584321; omega)
  rw [← UInt64.toNat_inj]
  change (lowTest _ _ _ _).n = 0 ↔ _
  rw [lowTest, s3, s2, s1, byte_field_exact, byte_field_exact, byte_field_exact, byte_field_exact]
  omega

theorem field_canonical_iff (w : FieldBytes) : w.value < goldilocksModulus ↔
    w.e.toNat + w.f.toNat + w.g.toNat + w.h.toNat ≠ 1020 ∨
      w.a.toNat + w.b.toNat + w.c.toNat + w.d.toNat = 0 := by
  have ha := w.a.toNat_lt
  have hb := w.b.toNat_lt
  have hc := w.c.toNat_lt
  have hd := w.d.toNat_lt
  have he := w.e.toNat_lt
  have hf := w.f.toNat_lt
  have hg := w.g.toNat_lt
  have hh := w.h.toNat_lt
  unfold FieldBytes.value goldilocksModulus
  omega

/-- The exact emitted `gl_lt_p` arithmetic accepts precisely canonical u64 encodings. -/
theorem field_guard_exact (w : FieldBytes) :
    fieldGuard (.ofUInt8 w.a) (.ofUInt8 w.b) (.ofUInt8 w.c) (.ofUInt8 w.d)
      (.ofUInt8 w.e) (.ofUInt8 w.f) (.ofUInt8 w.g) (.ofUInt8 w.h) =
      if w.value < goldilocksModulus then 1 else 0 := by
  simp only [field_canonical_iff]
  simp only [fieldGuard, beq_iff_eq, high_test_zero, low_test_zero]
  by_cases high : w.e.toNat + w.f.toNat + w.g.toNat + w.h.toNat = 1020 <;>
    by_cases low : w.a.toNat + w.b.toNat + w.c.toNat + w.d.toNat = 0 <;>
    simp only [ne_eq, high, low, not_true_eq_false, not_false_eq_true,
      true_or, false_or, ite_true, ite_false] <;> rfl

def fourByteOps (reader start idx : Nat) : Array Aiur.Bytecode.Op :=
  #[.call reader #[idx] 2 false, .call reader #[start + 1] 2 false,
    .call reader #[start + 3] 2 false, .call reader #[start + 5] 2 false]

/-- Four raw byte Calls without packing. Used both by fields and Word literals. -/
theorem four_byte_eval (t : Bytecode.Toplevel) (fuel selector reader idx : Nat) (st : EvalState)
    (f : Aiur.Bytecode.Function) (function : t.functions[reader]? = some f)
    (checked : checkByteReader f selector = true) (p0 p1 p2 p3 p4 a b c d : G)
    (argument : st.map[idx]? = some p0)
    (ha : memLoad st 3 p0.n = .ok #[0, a, p1])
    (hb : memLoad st 3 p1.n = .ok #[0, b, p2])
    (hc : memLoad st 3 p2.n = .ok #[0, c, p3])
    (hd : memLoad st 3 p3.n = .ok #[0, d, p4]) :
    runOps t (fuel + 1) (fourByteOps reader st.map.size idx) st 0 =
      .ok { st with map := st.map ++ #[a, p1, b, p2, c, p3, d, p4] } := by
  obtain ⟨input, body⟩ := byte_reader_checked f selector checked
  obtain ⟨bound, found⟩ := Array.getElem?_eq_some_iff.mp function
  simp +arith [fourByteOps, run_ops_list, Aiur.Bytecode.Eval.evalOp, readIdxs, readIdx,
    Bind.bind, Except.bind, Pure.pure, Except.pure, bound, found, input, body,
    evalBlock, byteReaderBody, evalCtrl, evalMatchArm, ha, hb, hc, hd, argument,
    appendMap, setIoBuffer, Array.getElem?_append, Array.append_assoc]

def fieldReadOps (reader : Nat) : Array Aiur.Bytecode.Op :=
  fourByteOps reader 1 0 ++ fourByteOps reader 9 8
def fieldGuardOps : Array Aiur.Bytecode.Op :=
  #[.const 1020, .sub 15 17, .add 13 18, .add 11 19, .add 9 20, .eqZero 21,
    .add 5 7, .add 3 23, .add 1 24, .eqZero 25, .const 1, .const 1,
    .sub 28 26, .mul 22 29, .sub 27 30, .const 1,
    .assertEq #[31] #[32] (some "IxBy noncanonical field")]
def fieldPackOps : Array Aiur.Bytecode.Op :=
  #[.const 256, .mul 33 3, .const 65536, .mul 35 5, .const 16777216, .mul 37 7,
    .const 4294967296, .mul 39 9, .const 1099511627776, .mul 41 11,
    .const 281474976710656, .mul 43 13, .const 72057594037927936, .mul 45 15,
    .add 44 46, .add 42 47, .add 40 48, .add 38 49, .add 36 50, .add 34 51, .add 1 52]
def fieldReaderBody (reader : Nat) : Aiur.Bytecode.Block := {
  ops := fieldReadOps reader ++ fieldGuardOps ++ fieldPackOps,
  ctrl := .return 0 #[53, 16] }

private def guardRegisters (a b c d e f g h : G) : Array G :=
  let lo : G := if (lowTest a b c d).val == 0 then 1 else 0
  let hi : G := if (highTest e f g h).val == 0 then 1 else 0
  #[1020, h - 1020, g + (h - 1020), f + (g + (h - 1020)), highTest e f g h, hi,
    c + d, b + (c + d), lowTest a b c d, lo, 1, 1, 1 - lo, hi * (1 - lo),
    fieldGuard a b c d e f g h, 1]

private theorem field_guard_eval (t : Bytecode.Toplevel) (fuel : Nat) (st : EvalState)
    (size : st.map.size = 17) (a b c d e f g h : G)
    (ha : st.map[1]? = some a) (hb : st.map[3]? = some b)
    (hc : st.map[5]? = some c) (hd : st.map[7]? = some d)
    (he : st.map[9]? = some e) (hf : st.map[11]? = some f)
    (hg : st.map[13]? = some g) (hh : st.map[15]? = some h) :
    runOps t fuel fieldGuardOps st 0 =
      if (fieldGuard a b c d e f g h).val = (1 : G).val then
        .ok { st with map := st.map ++ guardRegisters a b c d e f g h }
      else .error .assertFailed := by
  have av := (Array.getElem?_eq_some_iff.mp ha).2
  have bv := (Array.getElem?_eq_some_iff.mp hb).2
  have cv := (Array.getElem?_eq_some_iff.mp hc).2
  have dv := (Array.getElem?_eq_some_iff.mp hd).2
  have ev := (Array.getElem?_eq_some_iff.mp he).2
  have fv := (Array.getElem?_eq_some_iff.mp hf).2
  have gv := (Array.getElem?_eq_some_iff.mp hg).2
  have hv := (Array.getElem?_eq_some_iff.mp hh).2
  by_cases accepted : (fieldGuard a b c d e f g h).val = (1 : G).val <;>
    simp only [fieldGuard, highTest, lowTest, beq_iff_eq] at accepted <;>
    simp +arith [fieldGuardOps, guardRegisters, fieldGuard, highTest, lowTest, run_ops_list,
      Aiur.Bytecode.Eval.evalOp, readIdxs, readIdx, pushMap, Array.getElem?_push, Array.getElem_push,
      size, av, bv, cv, dv, ev, fv, gv, hv, accepted,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  apply Array.toList_inj.mp
  simp [List.append_assoc]

private theorem field_pack_eval (t : Bytecode.Toplevel) (fuel : Nat) (st : EvalState)
    (size : st.map.size = 33) (a b c d e f g h finish : G)
    (ha : st.map[1]? = some a) (hb : st.map[3]? = some b)
    (hc : st.map[5]? = some c) (hd : st.map[7]? = some d)
    (he : st.map[9]? = some e) (hf : st.map[11]? = some f)
    (hg : st.map[13]? = some g) (hh : st.map[15]? = some h)
    (suffix : st.map[16]? = some finish) :
    ∃ after, after.memory = st.memory ∧ after.ioBuffer = st.ioBuffer ∧
      evalBlock t fuel ⟨fieldPackOps, .return 0 #[53, 16]⟩ st =
        .error (.earlyReturn #[packedField a b c d e f g h, finish] after) := by
  have av := (Array.getElem?_eq_some_iff.mp ha).2
  have bv := (Array.getElem?_eq_some_iff.mp hb).2
  have cv := (Array.getElem?_eq_some_iff.mp hc).2
  have dv := (Array.getElem?_eq_some_iff.mp hd).2
  have ev := (Array.getElem?_eq_some_iff.mp he).2
  have fv := (Array.getElem?_eq_some_iff.mp hf).2
  have gv := (Array.getElem?_eq_some_iff.mp hg).2
  have hv := (Array.getElem?_eq_some_iff.mp hh).2
  have tail := (Array.getElem?_eq_some_iff.mp suffix).2
  simp +arith [fieldPackOps, packedField, evalBlock, run_ops_list,
    Aiur.Bytecode.Eval.evalOp, readIdxs, readIdx, pushMap, evalCtrl, Array.getElem?_push, Array.getElem_push,
    size, av, bv, cv, dv, ev, fv, gv, hv, tail,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

def checkFieldReader (f : Aiur.Bytecode.Function) (reader : Nat) : Bool :=
  decide (f.layout.inputSize = 1) && checkReturnBlock f.body (fieldReaderBody reader).ops 0 #[53, 16]

theorem field_reader_checked (f : Aiur.Bytecode.Function) (reader : Nat)
    (checked : checkFieldReader f reader = true) :
    f.layout.inputSize = 1 ∧ f.body = fieldReaderBody reader := by
  simp only [checkFieldReader, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact ⟨checked.1, return_block_checked _ _ _ _ checked.2⟩

/-- Raw behavior, retaining the pre-guard modular arithmetic as a condition.
This lemma does not infer byte ranges from successful loads. -/
theorem raw_field_reader (t : Bytecode.Toplevel) (fuel selector reader : Nat) (st : EvalState)
    (f : Aiur.Bytecode.Function) (function : t.functions[reader]? = some f)
    (checked : checkByteReader f selector = true)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 a b c d e g h k : G)
    (ha : memLoad st 3 p0.n = .ok #[0, a, p1])
    (hb : memLoad st 3 p1.n = .ok #[0, b, p2])
    (hc : memLoad st 3 p2.n = .ok #[0, c, p3])
    (hd : memLoad st 3 p3.n = .ok #[0, d, p4])
    (he : memLoad st 3 p4.n = .ok #[0, e, p5])
    (hg : memLoad st 3 p5.n = .ok #[0, g, p6])
    (hh : memLoad st 3 p6.n = .ok #[0, h, p7])
    (hk : memLoad st 3 p7.n = .ok #[0, k, p8]) :
    ∃ after, after.memory = st.memory ∧ after.ioBuffer = st.ioBuffer ∧
      evalBlock t (fuel + 1) (fieldReaderBody reader) { st with map := #[p0] } =
        if (fieldGuard a b c d e g h k).val = (1 : G).val then
          .error (.earlyReturn #[packedField a b c d e g h k, p8] after)
        else .error .assertFailed := by
  have reads : runOps t (fuel + 1) (fieldReadOps reader) { st with map := #[p0] } 0 =
      .ok { st with map := #[p0, a, p1, b, p2, c, p3, d, p4, e, p5, g, p6, h, p7, k, p8] } := by
    have first := four_byte_eval t fuel selector reader 0 { st with map := #[p0] }
      f function checked p0 p1 p2 p3 p4 a b c d rfl ha hb hc hd
    have second := four_byte_eval t fuel selector reader 8
      { st with map := #[p0, a, p1, b, p2, c, p3, d, p4] }
      f function checked p4 p5 p6 p7 p8 e g h k rfl he hg hh hk
    change runOps t (fuel + 1) (fourByteOps reader 1 0) { st with map := #[p0] } 0 =
      .ok { st with map := #[p0, a, p1, b, p2, c, p3, d, p4] } at first
    change runOps t (fuel + 1) (fourByteOps reader 9 8)
      { st with map := #[p0, a, p1, b, p2, c, p3, d, p4] } 0 = _ at second
    rw [fieldReadOps, run_ops_append, first]
    exact second
  let readSt : EvalState := { st with map := #[p0, a, p1, b, p2, c, p3, d, p4, e, p5, g, p6, h, p7, k, p8] }
  let guardSt : EvalState := { st with map := readSt.map ++ guardRegisters a b c d e g h k }
  have guardSize : guardSt.map.size = 33 := by simp [guardSt, readSt, guardRegisters]
  have preserved (idx : Nat) (small : idx < 17) : guardSt.map[idx]? = readSt.map[idx]? := by
    simp [guardSt, readSt, Array.getElem?_append, small]
  obtain ⟨after, memory, io, packed⟩ := field_pack_eval t (fuel + 1) guardSt guardSize
    a b c d e g h k p8 (by rw [preserved 1 (by decide)]; rfl)
    (by rw [preserved 3 (by decide)]; rfl) (by rw [preserved 5 (by decide)]; rfl)
    (by rw [preserved 7 (by decide)]; rfl) (by rw [preserved 9 (by decide)]; rfl)
    (by rw [preserved 11 (by decide)]; rfl) (by rw [preserved 13 (by decide)]; rfl)
    (by rw [preserved 15 (by decide)]; rfl) (by rw [preserved 16 (by decide)]; rfl)
  refine ⟨after, memory, io, ?_⟩
  have guard := field_guard_eval t (fuel + 1) readSt rfl a b c d e g h k rfl rfl rfl rfl rfl rfl rfl rfl
  dsimp only [readSt] at guard
  by_cases accepted : (fieldGuard a b c d e g h k).val = (1 : G).val
  · simpa only [fieldReaderBody, evalBlock, run_ops_append, reads, Except.bind,
      guard, accepted, ite_true, guardSt, readSt] using packed
  · simp only [fieldReaderBody, evalBlock, run_ops_append, reads, Except.bind,
      guard, accepted, ite_false]

/-- Expose one genuine byte to an actual typed-memory load. -/
theorem prefix_byte_load (st : EvalState) {pointer finish : G} {byte : UInt8} {bytes : List UInt8}
    (read : BytePrefix (bytecodeMemory st) pointer (byte :: bytes) finish) :
    ∃ tail, memLoad st 3 pointer.n = .ok #[0, G.ofUInt8 byte, tail] ∧
      BytePrefix (bytecodeMemory st) tail bytes finish := by
  obtain ⟨tail, loaded, rest⟩ := byte_prefix_head read
  refine ⟨tail, ?_, rest⟩
  unfold bytecodeMemory at loaded
  cases actual : memLoad st 3 pointer.n with
  | error error => simp [actual] at loaded
  | ok flat => simpa [actual] using loaded

/-- Actual complete field decoder: canonical acceptance, exact value and
suffix, and no memory/I/O changes. The endpoint need not be readable. -/
theorem checked_field_reader (t : Bytecode.Toplevel) (fuel selector reader : Nat) (st : EvalState)
    (byteFn : Aiur.Bytecode.Function) (byteFunction : t.functions[reader]? = some byteFn)
    (byteChecked : checkByteReader byteFn selector = true)
    (f : Aiur.Bytecode.Function) (checked : checkFieldReader f reader = true)
    (pointer finish : G) (w : FieldBytes)
    (read : BytePrefix (bytecodeMemory st) pointer w.bytes finish) :
    ∃ after, after.memory = st.memory ∧ after.ioBuffer = st.ioBuffer ∧
      evalBlock t (fuel + 1) f.body { st with map := #[pointer] } =
        if w.value < goldilocksModulus then .error (.earlyReturn #[w.field, finish] after)
        else .error .assertFailed := by
  obtain ⟨_, body⟩ := field_reader_checked f reader checked
  obtain ⟨p1, ha, rest⟩ := prefix_byte_load st read
  obtain ⟨p2, hb, rest⟩ := prefix_byte_load st rest
  obtain ⟨p3, hc, rest⟩ := prefix_byte_load st rest
  obtain ⟨p4, hd, rest⟩ := prefix_byte_load st rest
  obtain ⟨p5, he, rest⟩ := prefix_byte_load st rest
  obtain ⟨p6, hf, rest⟩ := prefix_byte_load st rest
  obtain ⟨p7, hg, rest⟩ := prefix_byte_load st rest
  obtain ⟨p8, hh, rest⟩ := prefix_byte_load st rest
  cases rest
  obtain ⟨after, memory, io, result⟩ := raw_field_reader t fuel selector reader st byteFn byteFunction byteChecked
    pointer p1 p2 p3 p4 p5 p6 p7 finish _ _ _ _ _ _ _ _ ha hb hc hd he hf hg hh
  refine ⟨after, memory, io, ?_⟩
  change evalBlock _ _ _ _ = if (fieldGuard _ _ _ _ _ _ _ _).val = (1 : G).val then
    .error (.earlyReturn #[w.field, finish] after) else .error .assertFailed at result
  rw [field_guard_exact] at result
  have different : (0 : G).val ≠ (1 : G).val := by decide
  by_cases valid : w.value < goldilocksModulus <;> simpa [body, valid, different] using result

/-- A read-only parser Call restores the caller registers on success and
propagates rejection. It does not assume a callee with an unchecked index. -/
theorem readonly_parser_call (t : Bytecode.Toplevel) (fuel callee : Nat) (st : EvalState)
    (f : Aiur.Bytecode.Function) (function : t.functions[callee]? = some f)
    (indices : Array Nat) (inputs outputs : Array G) (arguments : readIdxs st indices = .ok inputs)
    (arity : f.layout.inputSize = inputs.size) (accepted : Prop) [Decidable accepted]
    (after : EvalState) (memory : after.memory = st.memory) (io : after.ioBuffer = st.ioBuffer)
    (result : evalBlock t fuel f.body { st with map := inputs } =
      if accepted then .error (.earlyReturn outputs after) else .error .assertFailed)
    (unconstrained : Bool) :
    Aiur.Bytecode.Eval.evalOp t (fuel + 1) (.call callee indices outputs.size unconstrained) st =
      if accepted then .ok { st with map := st.map ++ outputs } else .error .assertFailed := by
  obtain ⟨bound, found⟩ := Array.getElem?_eq_some_iff.mp function
  by_cases valid : accepted <;>
    simp [Aiur.Bytecode.Eval.evalOp, arguments, bound, found, arity, result, valid, memory, io,
      appendMap, setIoBuffer, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem checked_field_call (t : Bytecode.Toplevel) (fuel selector reader callee idx : Nat) (st : EvalState)
    (byteFn : Aiur.Bytecode.Function) (byteFunction : t.functions[reader]? = some byteFn)
    (byteChecked : checkByteReader byteFn selector = true)
    (f : Aiur.Bytecode.Function) (function : t.functions[callee]? = some f)
    (checked : checkFieldReader f reader = true) (pointer finish : G) (w : FieldBytes)
    (argument : st.map[idx]? = some pointer)
    (read : BytePrefix (bytecodeMemory st) pointer w.bytes finish) (unconstrained : Bool) :
    Aiur.Bytecode.Eval.evalOp t (fuel + 2) (.call callee #[idx] 2 unconstrained) st =
      if w.value < goldilocksModulus then .ok { st with map := st.map ++ #[w.field, finish] }
      else .error .assertFailed := by
  obtain ⟨arity, _⟩ := field_reader_checked f reader checked
  obtain ⟨after, memory, io, result⟩ := checked_field_reader t fuel selector reader st
    byteFn byteFunction byteChecked f checked pointer finish w read
  exact readonly_parser_call t (fuel + 1) callee st f function #[idx] #[pointer] #[w.field, finish]
    (by simp [readIdxs, readIdx, argument, Bind.bind, Except.bind, Pure.pure, Except.pure])
    arity _ after memory io result unconstrained

theorem byte_boolean_exact (byte : UInt8) :
    (G.ofUInt8 byte * G.ofUInt8 byte).val = (G.ofUInt8 byte).val ↔ byte.toNat ≤ 1 := by
  have bounded := byte.toNat_lt
  have square : (G.ofUInt8 byte * G.ofUInt8 byte).n = byte.toNat * byte.toNat := by
    change (G.ofNat ((G.ofUInt8 byte).n * (G.ofUInt8 byte).n)).n = _
    rw [byte_field_exact]
    apply field_of_nat_exact
    have := Nat.mul_le_mul (Nat.le_of_lt bounded) (Nat.le_of_lt bounded)
    change byte.toNat * byte.toNat < 18446744069414584321
    omega
  rw [← UInt64.toNat_inj]
  change (G.ofUInt8 byte * G.ofUInt8 byte).n = (G.ofUInt8 byte).n ↔ _
  rw [square, byte_field_exact]
  constructor
  · intro equal
    by_cases small : byte.toNat ≤ 1
    · exact small
    · have twice := Nat.mul_le_mul_left byte.toNat (show 2 ≤ byte.toNat by omega)
      omega
  · intro small
    have cases : byte.toNat = 0 ∨ byte.toNat = 1 := by omega
    rcases cases with zero | one
    · simp [zero]
    · simp [one]

/-- A return-only match arm specification; equality never relies on bytecode BEq. -/
structure ReturnSpec where
  ops : Array Aiur.Bytecode.Op
  selector : Nat
  outputs : Array Nat

def ReturnSpec.block (s : ReturnSpec) : Aiur.Bytecode.Block := ⟨s.ops, .return s.selector s.outputs⟩
def checkReturnArms : List (G × Aiur.Bytecode.Block) → List (G × ReturnSpec) → Bool
  | [], [] => true
  | (tag, branch) :: rest, (expected, spec) :: specs =>
    decide (tag = expected) && checkReturnBlock branch spec.ops spec.selector spec.outputs &&
      checkReturnArms rest specs
  | _, _ => false

theorem return_arms_checked (actual : List (G × Aiur.Bytecode.Block)) (specs : List (G × ReturnSpec))
    (checked : checkReturnArms actual specs = true) :
    actual = specs.map (fun (tag, spec) => (tag, spec.block)) := by
  induction specs generalizing actual with
  | nil => cases actual <;> simp_all [checkReturnArms]
  | cons spec specs ih =>
    cases actual with
    | nil => simp [checkReturnArms] at checked
    | cons arm rest =>
      rcases spec with ⟨expected, spec⟩
      rcases arm with ⟨tag, branch⟩
      simp only [checkReturnArms, Bool.and_eq_true, decide_eq_true_eq] at checked
      have body := return_block_checked _ _ _ _ checked.1.2
      simp only [checked.1.1, body, ih rest checked.2, List.map_cons, ReturnSpec.block]

def dispatchBody (ops : Array Aiur.Bytecode.Op) (idx : Nat)
    (specs : List (G × ReturnSpec)) (fallback : ReturnSpec) : Aiur.Bytecode.Block :=
  ⟨ops, .match idx (specs.map (fun (tag, spec) => (tag, spec.block))).toArray (some fallback.block)⟩
def checkDispatch (f : Aiur.Bytecode.Function) (arity : Nat) (ops : Array Aiur.Bytecode.Op) (idx : Nat)
    (specs : List (G × ReturnSpec)) (fallback : ReturnSpec) : Bool :=
  match f.body.ctrl with
  | .match actual cases (some other) =>
    decide (f.layout.inputSize = arity ∧ f.body.ops = ops ∧ actual = idx) &&
      checkReturnArms cases.toList specs && checkReturnBlock other fallback.ops fallback.selector fallback.outputs
  | _ => false

theorem dispatch_checked (f : Aiur.Bytecode.Function) (arity : Nat) (ops : Array Aiur.Bytecode.Op) (idx : Nat)
    (specs : List (G × ReturnSpec)) (fallback : ReturnSpec)
    (checked : checkDispatch f arity ops idx specs fallback = true) :
    f.layout.inputSize = arity ∧ f.body = dispatchBody ops idx specs fallback := by
  unfold checkDispatch at checked
  split at checked
  · rename_i actual cases other ctrl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at checked
    obtain ⟨⟨⟨input, operations, index⟩, arms⟩, otherChecked⟩ := checked
    have branches : cases = (specs.map (fun (tag, spec) => (tag, spec.block))).toArray :=
      Array.toList_inj.mp (by simpa using return_arms_checked _ _ arms)
    have rest := return_block_checked _ _ _ _ otherChecked
    refine ⟨input, ?_⟩
    cases f with
    | mk b layout entry constrained => cases b; simp_all [dispatchBody, ReturnSpec.block]
  · simp at checked

def boolScalar (reader : Nat) : ReturnSpec :=
  ⟨#[.call reader #[2] 2 false, .mul 3 3,
    .assertEq #[5] #[3] (some "IxBy noncanonical Bool"), .const 0, .const 0], 0, #[6, 3, 7, 7, 7, 4]⟩
def wordScalar (reader : Nat) : ReturnSpec :=
  ⟨fourByteOps reader 3 2 ++ #[.const 1], 1, #[11, 3, 5, 7, 9, 10]⟩
def fieldScalar (field : Nat) : ReturnSpec :=
  ⟨#[.call field #[2] 2 false, .const 2, .const 0], 2, #[5, 3, 6, 6, 6, 4]⟩
def extScalar (field : Nat) : ReturnSpec :=
  ⟨#[.call field #[2] 2 false, .call field #[4] 2 false, .const 3, .const 0], 3, #[7, 3, 5, 8, 8, 6]⟩
def unsupportedScalar : ReturnSpec :=
  ⟨#[.const 0, .const 1, .assertEq #[3] #[4] (some "IxBy unsupported scalar"), .const 4, .const 4],
    4, #[5, 6, 6, 6, 6, 2]⟩
def scalarCases (reader field : Nat) : List (G × ReturnSpec) :=
  [(0, boolScalar reader), (1, wordScalar reader), (2, fieldScalar field), (3, extScalar field)]
def scalarReaderBody (reader field : Nat) : Aiur.Bytecode.Block :=
  dispatchBody #[.call reader #[0] 2 false] 1 (scalarCases reader field) unsupportedScalar
def checkScalarReader (f : Aiur.Bytecode.Function) (reader field : Nat) : Bool :=
  checkDispatch f 1 #[.call reader #[0] 2 false] 1 (scalarCases reader field) unsupportedScalar

theorem scalar_reader_checked (f : Aiur.Bytecode.Function) (reader field : Nat)
    (checked : checkScalarReader f reader field = true) :
    f.layout.inputSize = 1 ∧ f.body = scalarReaderBody reader field :=
  dispatch_checked f 1 _ 1 _ _ checked

structure ScalarCode where
  reader : Nat
  field : Nat
  scalar : Nat
  byteSelector : Nat := 0

structure CheckedScalars (t : Bytecode.Toplevel) (code : ScalarCode) where
  byteFn : Aiur.Bytecode.Function
  byteFunction : t.functions[code.reader]? = some byteFn
  byteChecked : checkByteReader byteFn code.byteSelector = true
  fieldFn : Aiur.Bytecode.Function
  fieldFunction : t.functions[code.field]? = some fieldFn
  fieldChecked : checkFieldReader fieldFn code.reader = true
  scalarFn : Aiur.Bytecode.Function
  scalarFunction : t.functions[code.scalar]? = some scalarFn
  scalarChecked : checkScalarReader scalarFn code.reader code.field = true

def checkScalarCode (t : Bytecode.Toplevel) (code : ScalarCode) : Bool :=
  match t.functions[code.reader]?, t.functions[code.field]?, t.functions[code.scalar]? with
  | some byteFn, some fieldFn, some scalarFn =>
    checkByteReader byteFn code.byteSelector && checkFieldReader fieldFn code.reader &&
      checkScalarReader scalarFn code.reader code.field
  | _, _, _ => false

theorem scalar_code_checked (t : Bytecode.Toplevel) (code : ScalarCode)
    (checked : checkScalarCode t code = true) : Nonempty (CheckedScalars t code) := by
  unfold checkScalarCode at checked
  split at checked
  · rename_i byteFn fieldFn scalarFn byteFound fieldFound scalarFound
    simp only [Bool.and_eq_true] at checked
    exact ⟨⟨byteFn, byteFound, checked.1.1, fieldFn, fieldFound, checked.1.2,
      scalarFn, scalarFound, checked.2⟩⟩
  · simp at checked

inductive ScalarBytes where
  | boolean (value : UInt8)
  | word (value : WordBytes)
  | field (value : FieldBytes)
  | extension (first second : FieldBytes)

def ScalarBytes.bytes : ScalarBytes → List UInt8
  | .boolean byte => [0, byte]
  | .word w => 1 :: w.bytes
  | .field w => 2 :: w.bytes
  | .extension first second => 3 :: (first.bytes ++ second.bytes)
def ScalarBytes.valid : ScalarBytes → Prop
  | .boolean byte => byte.toNat ≤ 1
  | .word _ => True
  | .field w => w.value < goldilocksModulus
  | .extension first second => first.value < goldilocksModulus ∧ second.value < goldilocksModulus
instance (s : ScalarBytes) : Decidable s.valid := by cases s <;> unfold ScalarBytes.valid <;> infer_instance
def ScalarBytes.flat : ScalarBytes → Array G
  | .boolean byte => #[0, .ofUInt8 byte, 0, 0, 0]
  | .word w => #[1, .ofUInt8 w.a, .ofUInt8 w.b, .ofUInt8 w.c, .ofUInt8 w.d]
  | .field w => #[2, w.field, 0, 0, 0]
  | .extension first second => #[3, first.field, second.field, 0, 0]
def ScalarBytes.atom : ScalarBytes → Atom
  | .boolean byte => .bool (byte.toNat == 1)
  | .word w => .word w.field.n.toUInt32
  | .field w => .field (fieldValue w.field)
  | .extension first second => .ext ⟨fieldValue first.field, fieldValue second.field⟩

theorem scalar_flat_size (s : ScalarBytes) : s.flat.size = 5 := by cases s <;> rfl

@[local simp] private theorem natTag0 : (0 : G).n = 0 := by decide
@[local simp] private theorem natTag1 : (1 : G).n = 1 := by decide
@[local simp] private theorem natTag2 : (2 : G).n = 2 := by decide
@[local simp] private theorem natTag3 : (3 : G).n = 3 := by decide

/-- Exact concrete IBValue decoding, including every zero-padding slot. -/
theorem scalar_flat_decoded (s : ScalarBytes) (valid : s.valid) :
    decodeAtom s.flat.toList = some s.atom := by
  cases s with
  | boolean byte =>
    have small : byte.toNat = 0 ∨ byte.toNat = 1 := by change byte.toNat ≤ 1 at valid; omega
    rcases small with zero | one
    · simp [ScalarBytes.flat, ScalarBytes.atom, decodeAtom, of_byte, zero]
      decide
    · simp [ScalarBytes.flat, ScalarBytes.atom, decodeAtom, of_byte, one]
      decide
  | word word =>
    have exactWord := (packed_word_exact (.ofUInt8 word.a) (.ofUInt8 word.b) (.ofUInt8 word.c) (.ofUInt8 word.d)
      (by simpa using word.a.toNat_lt) (by simpa using word.b.toNat_lt)
      (by simpa using word.c.toNat_lt) (by simpa using word.d.toNat_lt)).1
    simp [ScalarBytes.flat, ScalarBytes.atom, decodeAtom, word.a.toNat_lt, word.b.toNat_lt,
      word.c.toNat_lt, word.d.toNat_lt, WordBytes.field, exactWord]
  | field word => simp [ScalarBytes.flat, ScalarBytes.atom, decodeAtom]
  | extension first second => simp [ScalarBytes.flat, ScalarBytes.atom, decodeAtom]

@[local simp] private theorem tag01 : (0 : G).val ≠ (1 : G).val := by decide
@[local simp] private theorem tag02 : (0 : G).val ≠ (2 : G).val := by decide
@[local simp] private theorem tag03 : (0 : G).val ≠ (3 : G).val := by decide
@[local simp] private theorem tag12 : (1 : G).val ≠ (2 : G).val := by decide
@[local simp] private theorem tag13 : (1 : G).val ≠ (3 : G).val := by decide
@[local simp] private theorem tag23 : (2 : G).val ≠ (3 : G).val := by decide

private theorem scalar_dispatch (t : Bytecode.Toplevel) (code : ScalarCode) (checked : CheckedScalars t code)
    (fuel : Nat) (st : EvalState) (pointer tag rest : G)
    (loaded : memLoad st 3 pointer.n = .ok #[0, tag, rest]) :
    evalBlock t (fuel + 1) checked.scalarFn.body { st with map := #[pointer] } =
      evalCtrl t (fuel + 1) (scalarReaderBody code.reader code.field).ctrl
        { st with map := #[pointer, tag, rest] } := by
  obtain ⟨_, body⟩ := scalar_reader_checked checked.scalarFn code.reader code.field checked.scalarChecked
  have first := byte_reader_call t fuel code.byteSelector code.reader 0 { st with map := #[pointer] }
    checked.byteFn checked.byteFunction checked.byteChecked pointer tag rest rfl loaded false
  rw [body, evalBlock]
  simp [scalarReaderBody, dispatchBody, run_ops_list, first,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem checked_boolean_scalar (t : Bytecode.Toplevel) (code : ScalarCode) (checked : CheckedScalars t code)
    (fuel : Nat) (st : EvalState) (pointer finish : G) (byte : UInt8)
    (read : BytePrefix (bytecodeMemory st) pointer [0, byte] finish) :
    ∃ after, after.memory = st.memory ∧ after.ioBuffer = st.ioBuffer ∧
      evalBlock t (fuel + 1) checked.scalarFn.body { st with map := #[pointer] } =
        if byte.toNat ≤ 1 then .error (.earlyReturn #[0, .ofUInt8 byte, 0, 0, 0, finish] after)
        else .error .assertFailed := by
  obtain ⟨next, tag, rest⟩ := prefix_byte_load st read
  obtain ⟨tail, loaded, rest⟩ := prefix_byte_load st rest
  cases rest
  rw [scalar_dispatch t code checked fuel st pointer 0 next tag]
  have call := byte_reader_call t fuel code.byteSelector code.reader 2 { st with map := #[pointer, 0, next] }
    checked.byteFn checked.byteFunction checked.byteChecked next (.ofUInt8 byte) finish rfl loaded false
  refine ⟨{ st with map := #[pointer, 0, next, .ofUInt8 byte, finish,
    .ofUInt8 byte * .ofUInt8 byte, 0, 0] }, rfl, rfl, ?_⟩
  by_cases valid : byte.toNat ≤ 1 <;>
    simp [scalarReaderBody, dispatchBody, scalarCases, boolScalar, ReturnSpec.block,
      evalCtrl, evalMatchArm, evalBlock, run_ops_list, call, Aiur.Bytecode.Eval.evalOp,
      readIdx, readIdxs, pushMap, byte_boolean_exact, valid,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem checked_word_scalar (t : Bytecode.Toplevel) (code : ScalarCode) (checked : CheckedScalars t code)
    (fuel : Nat) (st : EvalState) (pointer finish : G) (w : WordBytes)
    (read : BytePrefix (bytecodeMemory st) pointer (1 :: w.bytes) finish) :
    ∃ after, after.memory = st.memory ∧ after.ioBuffer = st.ioBuffer ∧
      evalBlock t (fuel + 1) checked.scalarFn.body { st with map := #[pointer] } =
        .error (.earlyReturn #[1, .ofUInt8 w.a, .ofUInt8 w.b, .ofUInt8 w.c, .ofUInt8 w.d, finish] after) := by
  obtain ⟨next, tag, rest⟩ := prefix_byte_load st read
  obtain ⟨p1, ha, rest⟩ := prefix_byte_load st rest
  obtain ⟨p2, hb, rest⟩ := prefix_byte_load st rest
  obtain ⟨p3, hc, rest⟩ := prefix_byte_load st rest
  obtain ⟨p4, hd, rest⟩ := prefix_byte_load st rest
  cases rest
  rw [scalar_dispatch t code checked fuel st pointer 1 next tag]
  have words := four_byte_eval t fuel code.byteSelector code.reader 2 { st with map := #[pointer, 1, next] }
    checked.byteFn checked.byteFunction checked.byteChecked next p1 p2 p3 finish _ _ _ _ rfl ha hb hc hd
  change runOps t (fuel + 1) (fourByteOps code.reader 3 2) { st with map := #[pointer, 1, next] } 0 = _ at words
  let after : EvalState := { st with map := #[pointer, 1, next, .ofUInt8 w.a, p1, .ofUInt8 w.b, p2,
    .ofUInt8 w.c, p3, .ofUInt8 w.d, finish, 1] }
  have branch : evalBlock t (fuel + 1) (wordScalar code.reader).block { st with map := #[pointer, 1, next] } =
      .error (.earlyReturn #[1, .ofUInt8 w.a, .ofUInt8 w.b, .ofUInt8 w.c, .ofUInt8 w.d, finish] after) := by
    simp only [wordScalar, ReturnSpec.block, evalBlock, run_ops_append, words, Except.bind]
    simp [run_ops_list, Aiur.Bytecode.Eval.evalOp, readIdx, readIdxs, pushMap, evalCtrl, after,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨after, rfl, rfl, ?_⟩
  simp [scalarReaderBody, dispatchBody, scalarCases, evalCtrl, evalMatchArm, branch, readIdx]

theorem checked_field_scalar (t : Bytecode.Toplevel) (code : ScalarCode) (checked : CheckedScalars t code)
    (fuel : Nat) (st : EvalState) (pointer finish : G) (w : FieldBytes)
    (read : BytePrefix (bytecodeMemory st) pointer (2 :: w.bytes) finish) :
    ∃ after, after.memory = st.memory ∧ after.ioBuffer = st.ioBuffer ∧
      evalBlock t (fuel + 2) checked.scalarFn.body { st with map := #[pointer] } =
        if w.value < goldilocksModulus then .error (.earlyReturn #[2, w.field, 0, 0, 0, finish] after)
        else .error .assertFailed := by
  obtain ⟨next, tag, rest⟩ := prefix_byte_load st read
  rw [scalar_dispatch t code checked (fuel + 1) st pointer 2 next tag]
  have field := checked_field_call t fuel code.byteSelector code.reader code.field 2
    { st with map := #[pointer, 2, next] } checked.byteFn checked.byteFunction checked.byteChecked
    checked.fieldFn checked.fieldFunction checked.fieldChecked next finish w rfl rest false
  refine ⟨{ st with map := #[pointer, 2, next, w.field, finish, 2, 0] }, rfl, rfl, ?_⟩
  by_cases valid : w.value < goldilocksModulus <;>
    simp [scalarReaderBody, dispatchBody, scalarCases, fieldScalar, ReturnSpec.block,
      evalCtrl, evalMatchArm, evalBlock, run_ops_list, field, valid,
      Aiur.Bytecode.Eval.evalOp, readIdx, readIdxs, pushMap,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem checked_extension_scalar (t : Bytecode.Toplevel) (code : ScalarCode) (checked : CheckedScalars t code)
    (fuel : Nat) (st : EvalState) (pointer finish : G) (first second : FieldBytes)
    (read : BytePrefix (bytecodeMemory st) pointer (3 :: (first.bytes ++ second.bytes)) finish) :
    ∃ after, after.memory = st.memory ∧ after.ioBuffer = st.ioBuffer ∧
      evalBlock t (fuel + 2) checked.scalarFn.body { st with map := #[pointer] } =
        if first.value < goldilocksModulus ∧ second.value < goldilocksModulus then
          .error (.earlyReturn #[3, first.field, second.field, 0, 0, finish] after)
        else .error .assertFailed := by
  obtain ⟨next, tag, rest⟩ := prefix_byte_load st read
  obtain ⟨middle, firstRead, secondRead⟩ := byte_prefix_split rest
  rw [scalar_dispatch t code checked (fuel + 1) st pointer 3 next tag]
  have firstCall := checked_field_call t fuel code.byteSelector code.reader code.field 2
    { st with map := #[pointer, 3, next] } checked.byteFn checked.byteFunction checked.byteChecked
    checked.fieldFn checked.fieldFunction checked.fieldChecked next middle first rfl firstRead false
  have secondCall := checked_field_call t fuel code.byteSelector code.reader code.field 4
    { st with map := #[pointer, 3, next, first.field, middle] }
    checked.byteFn checked.byteFunction checked.byteChecked
    checked.fieldFn checked.fieldFunction checked.fieldChecked middle finish second rfl secondRead false
  refine ⟨{ st with map := #[pointer, 3, next, first.field, middle, second.field, finish, 3, 0] }, rfl, rfl, ?_⟩
  by_cases firstValid : first.value < goldilocksModulus <;>
    by_cases secondValid : second.value < goldilocksModulus <;>
    simp [scalarReaderBody, dispatchBody, scalarCases, extScalar, ReturnSpec.block,
      evalCtrl, evalMatchArm, evalBlock, run_ops_list, firstCall, secondCall, firstValid, secondValid,
      Aiur.Bytecode.Eval.evalOp, readIdx, readIdxs, pushMap,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- The default branch rejects every unsupported raw tag, without consuming a payload. -/
theorem checked_unsupported_scalar (t : Bytecode.Toplevel) (code : ScalarCode) (checked : CheckedScalars t code)
    (fuel : Nat) (st : EvalState) (pointer tag rest : G)
    (loaded : memLoad st 3 pointer.n = .ok #[0, tag, rest])
    (unsupported : tag ≠ 0 ∧ tag ≠ 1 ∧ tag ≠ 2 ∧ tag ≠ 3) :
    evalBlock t (fuel + 1) checked.scalarFn.body { st with map := #[pointer] } = .error .assertFailed := by
  have t0 : (0 : G).val ≠ tag.val := fun equal => unsupported.1 (Subtype.ext equal.symm)
  have t1 : (1 : G).val ≠ tag.val := fun equal => unsupported.2.1 (Subtype.ext equal.symm)
  have t2 : (2 : G).val ≠ tag.val := fun equal => unsupported.2.2.1 (Subtype.ext equal.symm)
  have t3 : (3 : G).val ≠ tag.val := fun equal => unsupported.2.2.2 (Subtype.ext equal.symm)
  rw [scalar_dispatch t code checked fuel st pointer tag rest loaded]
  simp [scalarReaderBody, dispatchBody, scalarCases, unsupportedScalar, ReturnSpec.block,
    evalCtrl, evalMatchArm, evalDefaultBlock, evalBlock, run_ops_list, t0, t1, t2, t3,
    Aiur.Bytecode.Eval.evalOp, readIdx, readIdxs, pushMap,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Complete supported scalar syntax; both extension limbs are independently
canonical. Invalid Bool/field encodings reject, rather than normalize. -/
theorem checked_scalar_reader (t : Bytecode.Toplevel) (code : ScalarCode) (checked : CheckedScalars t code)
    (fuel : Nat) (st : EvalState) (pointer finish : G) (s : ScalarBytes)
    (read : BytePrefix (bytecodeMemory st) pointer s.bytes finish) :
    ∃ after, after.memory = st.memory ∧ after.ioBuffer = st.ioBuffer ∧
      evalBlock t (fuel + 2) checked.scalarFn.body { st with map := #[pointer] } =
        if s.valid then .error (.earlyReturn (s.flat ++ #[finish]) after) else .error .assertFailed := by
  cases s with
  | boolean byte => simpa [ScalarBytes.valid, ScalarBytes.flat, Nat.add_assoc] using
      checked_boolean_scalar t code checked (fuel + 1) st pointer finish byte read
  | word word => simpa [ScalarBytes.valid, ScalarBytes.flat, Nat.add_assoc] using
      checked_word_scalar t code checked (fuel + 1) st pointer finish word read
  | field word => exact checked_field_scalar t code checked fuel st pointer finish word read
  | extension first second => exact checked_extension_scalar t code checked fuel st pointer finish first second read

/-- Actual same-toplevel scalar Call, with exact caller-register restoration. -/
theorem checked_scalar_call (t : Bytecode.Toplevel) (code : ScalarCode) (checked : CheckedScalars t code)
    (fuel idx : Nat) (st : EvalState) (pointer finish : G) (s : ScalarBytes)
    (argument : st.map[idx]? = some pointer)
    (read : BytePrefix (bytecodeMemory st) pointer s.bytes finish) (unconstrained : Bool) :
    Aiur.Bytecode.Eval.evalOp t (fuel + 3) (.call code.scalar #[idx] 6 unconstrained) st =
      if s.valid then .ok { st with map := st.map ++ (s.flat ++ #[finish]) } else .error .assertFailed := by
  obtain ⟨arity, _⟩ := scalar_reader_checked checked.scalarFn code.reader code.field checked.scalarChecked
  obtain ⟨after, memory, io, result⟩ := checked_scalar_reader t code checked fuel st pointer finish s read
  have call := readonly_parser_call t (fuel + 2) code.scalar st checked.scalarFn checked.scalarFunction
    #[idx] #[pointer] (s.flat ++ #[finish])
    (by simp [readIdxs, readIdx, argument, Bind.bind, Except.bind, Pure.pure, Except.pure])
    arity s.valid after memory io result unconstrained
  simpa [scalar_flat_size] using call

end
end
end Ix.Ixby.AiurBackend.Objects.Scalars
