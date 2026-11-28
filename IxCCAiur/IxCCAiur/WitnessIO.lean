import IxCCAiur.Blake3Spec
import IxCCAiur.Backward
import Aiur.Library.U32
import Aiur.Library.List
import Aiur.Library.Bytes
import Aiur.Library.Bytes.Correctness

/-! # Certified Existential Witness-Stream Ingress & NP Soundness (`IxCCAiur.WitnessIO`)

Provides Formal Aiur witness-stream ingress modules and certified NP existential
backward soundness theorems for recursive compression verifiers (`CompressWrap`,
`CompressGL`, `CompressNarrowFixed`, `CompressFinalNarrow`):

1. **Checked byte-list validity, representation relations & computable decoding (`byteListDecode`)**:
   - `isValidByteList`: every byte in a `List Nat` is strictly `< 256`.
   - `ByteStreamRel` (`Bytes::Stream = &Lists::Node<UInt8::U8>`, interoperable with
     `IxCC.AiurBackend.Blake3Spec.Stream`), `WordListRel` (`Lists::List<UInt32::U32>`),
     `KzgInputRel` (`KzgIO::Input = (Lists::List<UInt32::U32>, Field)`), and
     `DataByteListRel` (`Prog::D<id>` / `Prog::Bytes` direct enum byte lists).
   - Computable fuel-bounded `byteListDecode` (with proved soundness & completeness)
     relating both `Bytes::Stream` and `Prog::D<id>`/`Prog::Bytes` heap representations
     to Lean `List UInt8`.
2. **Formal Aiur `StarkIO` & `KzgIO` ingress modules**:
   - `starkIoReadStreamFn` (`StarkIO::read_byte_stream`) & `starkIoChannelFn`
     (`StarkIO::read_channel`) matching `MultiStark.Source.starkIO`'s exact channels
     (`"stark.io.info"`, `"stark.io.read1"`, `"stark.io.read8"`) with
     `UInt8::from_field` / `UInt8::from_fields` validation.
   - `kzgIoReadWordsFn`, `kzgIoReadByteFn`, `kzgIoSplit4Fn`, `kzgIoSizedChannelFn`
     (`KzgIO::sized_channel`), and `kzgIoReadStreamFn` (`KzgIO::read_stream`) matching
     `MultiStark.Source.kzgIO`'s exact channels (`"kzg.io.length"`, `"kzg.io.read4"`,
     `"kzg.io.read1"`, `"kzg.io.div"`) with `UInt8::from_field` / `UInt32::from_fields`
     validation.
   - All emitted functions are strictly plain (`Lower.isPlainExpr = true`).
3. **Certified NP existential backward soundness (`witness_stream_exists`, `witness_wrapper_sound`)**:
   - Independent of the untrusted host hint oracle, ANY finite Formal Aiur `EvalFn`
     derivation of `StarkIO::read_byte_stream`, `StarkIO::read_channel`,
     `KzgIO::sized_channel`, or `KzgIO::read_stream` extends the heap and produces
     a valid, finite `List UInt8` (`isValidByteList`).
   - Any wrapper entry reading witness channels and invoking a backward-sound inner
     predicate `check(pub, witnesses) = 1` (either `Field`-returning or `--assert-ok`
     `()`-returning) satisfies existential NP soundness:
     `EvalFn world wrapperEntry pub h (.field 1) h' → ∃ ws : List (List UInt8), ...`.

Strictly pure Lean 4, zero `sorry`, zero `admit`, zero `axiom`, zero `native_decide`,
zero `bv_decide`, zero `partial`. -/

set_option autoImplicit false

namespace IxCC.AiurBackend.WitnessIO

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library
open IxCC.AiurBackend.Lower
  (Expr Pat Fn vE litE letE seqE matchE callE addE subE assertion
   hasDoubleColon qualifyName qualifyExprF isPlainExpr isPlainList isPlainArms)
open IxCC.AiurBackend.Gadgets
  (WorldHasFn no_evalExit_of_plain evalFn_plain_inv
   evalExpr_literal_inv evalExpr_var_inv evalExpr_binary_inv evalExpr_index_inv
   evalExpr_call_inv evalExpr_call1_inv evalExpr_call2_inv evalExpr_tuple2_inv
   evalExpr_let_wildcard_inv evalExpr_let_bind_inv evalExpr_let_tuple2_inv)
open IxCC.AiurBackend.TypedGadgets (evalExpr_call3_inv)
open IxCC.AiurBackend.World
  (checkNoFunction checkMap checkTable checkNoFunction_sound checkMap_sound
   checkTable_sound worldHasFn_of_check)
open IxCC.AiurBackend.Backward
  (BytesRep EvalExprN EvalArgsN EvalFnN evalFnN_plain_inv evalExprN_literal_inv
   evalExprN_var_inv evalExprN_let_bind_inv evalExprN_let_wildcard_inv
   evalExprN_call_inv evalExprN_store_inv evalExprN_binary_inv)
open IxCC.AiurBackend.Blake3Spec
  (byteStreamEnum bv w4 wv w4_eq_wv bv_ofNat byte_lt toNat_ofNat_lt
   evalExpr_match_inv selectArm_nil_inv selectArm_cons_inv evalExpr_store_inv
   evalExpr_let_array4_inv)

/-! ## Section 1: Byte List Validity, Representation Predicates & `byteListDecode` -/

/-- Every natural byte in `bs` is strictly below `256`. -/
def isValidByteList (bs : List Nat) : Prop :=
  ∀ b ∈ bs, b < 256

theorem isValidByteList_nil : isValidByteList [] := by
  intro b hb; cases hb

theorem isValidByteList_cons {b : Nat} {bs : List Nat} (hb : b < 256)
    (hbs : isValidByteList bs) : isValidByteList (b :: bs) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx'
  · exact hb
  · exact hbs x hx'

theorem isValidByteList_ofUInt8List (bs : List UInt8) :
    isValidByteList (bs.map UInt8.toNat) := by
  intro b hb
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp hb
  exact u.toNat_lt

/-- Canonical monomorphized enum symbol for `Lists::Node<UInt32::U32>`. -/
def wordStreamEnum : String :=
  (Aiur.Generic.Instance.mk "Lists::Node" [.array .field 4]).symbol

section Representations

variable {F : Type} [Field F]

/-- Canonical `Bytes::Stream = &Lists::Node<UInt8::U8>` relation on heap `h`,
definitionally identical to `Blake3Spec.Stream` and `Aiur.Library.Bytes.RepByteStream`. -/
abbrev ByteStreamRel (h : Heap F) (bs : List UInt8) (ptr : SourceValue F) : Prop :=
  Aiur.Library.Bytes.RepByteStream byteStreamEnum h bs ptr

theorem ByteStreamRel.mono {h₁ h₂ : Heap F} (ext : Heap.Extends h₁ h₂)
    {bs : List UInt8} {ptr : SourceValue F} (hr : ByteStreamRel h₁ bs ptr) :
    ByteStreamRel h₂ bs ptr :=
  Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext hr

theorem ByteStreamRel.allocNil (h : Heap F) :
    ByteStreamRel (h ++ [.construct byteStreamEnum "Nil" []]) []
      (.ptr (.enum byteStreamEnum) h.length) :=
  .nil (by simp)

theorem ByteStreamRel.allocCons {h : Heap F} {b : UInt8} {bs : List UInt8}
    {tailPtr : SourceValue F} (htail : ByteStreamRel h bs tailPtr) :
    ByteStreamRel (h ++ [.construct byteStreamEnum "Cons" [bv b, tailPtr]]) (b :: bs)
      (.ptr (.enum byteStreamEnum) h.length) :=
  .cons (by simp) rfl (htail.mono (Heap.Extends.snoc h _))

/-- Canonical `Lists::List<UInt32::U32> = &Lists::Node<[Field; 4]>` relation on heap `h`. -/
abbrev WordListRel (h : Heap F) (ws : List UInt32) (ptr : SourceValue F) : Prop :=
  Aiur.Library.List.RepList wordStreamEnum (fun _ w v => v = wv w) h ws ptr

theorem WordListRel.mono {h₁ h₂ : Heap F} (ext : Heap.Extends h₁ h₂)
    {ws : List UInt32} {ptr : SourceValue F} (hr : WordListRel h₁ ws ptr) :
    WordListRel h₂ ws ptr :=
  Aiur.Library.List.repList_heapMono₂ wordStreamEnum (fun _ _ _ _ _ h => h) ext hr

theorem WordListRel.allocNil (h : Heap F) :
    WordListRel (h ++ [.construct wordStreamEnum "Nil" []]) []
      (.ptr (.enum wordStreamEnum) h.length) :=
  .nil (by simp)

theorem WordListRel.allocCons {h : Heap F} {w : UInt32} {ws : List UInt32}
    {tailPtr : SourceValue F} (htail : WordListRel h ws tailPtr) :
    WordListRel (h ++ [.construct wordStreamEnum "Cons" [wv w, tailPtr]]) (w :: ws)
      (.ptr (.enum wordStreamEnum) h.length) :=
  .cons (by simp) rfl (htail.mono (Heap.Extends.snoc h _))

/-- Flatten a list of little-endian 32-bit words into its exact `List UInt8` byte sequence. -/
def wordsToBytes (ws : List UInt32) : List UInt8 :=
  ws.flatMap fun w => (Blake3.Pure.wordBytes w).toList

/-- Canonical `KzgIO::Input = (Lists::List<UInt32::U32>, Field)` relation on heap `h`:
a word list `ws` paired with a leading byte offset `off < 4`, decoding to
`(wordsToBytes ws).drop off`. -/
def KzgInputRel (h : Heap F) (bs : List UInt8) (v : SourceValue F) : Prop :=
  ∃ (ws : List UInt32) (off : Nat) (ptr : SourceValue F),
    off < 4 ∧
    v = .tuple [ptr, .field (off : F)] ∧
    WordListRel h ws ptr ∧
    bs = (wordsToBytes ws).drop off

theorem KzgInputRel.mono {h₁ h₂ : Heap F} (ext : Heap.Extends h₁ h₂)
    {bs : List UInt8} {v : SourceValue F} (hr : KzgInputRel h₁ bs v) :
    KzgInputRel h₂ bs v := by
  obtain ⟨ws, off, ptr, hoff, rfl, hws, rfl⟩ := hr
  exact ⟨ws, off, ptr, hoff, rfl, hws.mono ext, rfl⟩

/-- Direct enum byte list representation for `Prog::D<id>` and `Prog::Bytes` on heap `h`:
`Nil` is `.construct enumName nilCtor []`, and `Cons b rest` is
`.construct enumName consCtor [.field b, .ptr (.enum enumName) addr]` where `h[addr]? = some tailVal`. -/
inductive DataByteListRel (enumName nilCtor consCtor : String) (h : Heap F) :
    List UInt8 → SourceValue F → Prop where
  | nil : DataByteListRel enumName nilCtor consCtor h [] (.construct enumName nilCtor [])
  | cons {b : UInt8} {bs : List UInt8} {addr : Nat} {tailVal : SourceValue F}
      (atAddr : h[addr]? = some tailVal)
      (tail : DataByteListRel enumName nilCtor consCtor h bs tailVal) :
      DataByteListRel enumName nilCtor consCtor h (b :: bs)
        (.construct enumName consCtor [.field (b.toNat : F), .ptr (.enum enumName) addr])

theorem DataByteListRel.mono {enumName nilCtor consCtor : String}
    {h₁ h₂ : Heap F} (ext : Heap.Extends h₁ h₂)
    {bs : List UInt8} {v : SourceValue F}
    (hr : DataByteListRel enumName nilCtor consCtor h₁ bs v) :
    DataByteListRel enumName nilCtor consCtor h₂ bs v := by
  induction hr with
  | nil => exact .nil
  | cons atAddr _ ih => exact .cons (ext.getElem?_eq atAddr) ih

/-- `DataByteListRel "Prog::Bytes" "Nil" "Cons"` coincides with `Backward.BytesRep`. -/
theorem dataByteListRel_iff_bytesRep {be : String} {h : Heap F} {bs : List UInt8}
    {v : SourceValue F} :
    DataByteListRel be "Nil" "Cons" h bs v ↔ BytesRep be h bs v := by
  constructor
  · intro hr
    induction hr with
    | nil => exact .nil
    | cons atAddr _ ih => exact .cons atAddr ih
  · intro hr
    induction hr with
    | nil => exact .nil
    | cons atAddr _ ih => exact .cons atAddr ih

/-! ### Computable `byteListDecode` for `Bytes::Stream` and `Prog::D<id>` / `Prog::Bytes` -/

/-- Decode a pointer-linked `Bytes::Stream` (`Lists::List<UInt8::U8>`) value from `h`
into a Lean `List UInt8`, validating every byte is `< 256` under `toNat`. -/
def byteStreamDecode (toNat : F → Nat) (h : Heap F) :
    Nat → SourceValue F → Option (List UInt8)
  | 0, _ => none
  | fuel + 1, .ptr (.enum en) addr =>
    if en == byteStreamEnum then
      match h[addr]? with
      | some (.construct en' "Nil" []) =>
        if en' == byteStreamEnum then some [] else none
      | some (.construct en' "Cons" [.field x, tailPtr]) =>
        if en' == byteStreamEnum then
          let n := toNat x
          if n < 256 then
            (byteStreamDecode toNat h fuel tailPtr).map (UInt8.ofNat n :: ·)
          else none
        else none
      | _ => none
    else none
  | _ + 1, _ => none

/-- Decode a direct enum byte list (`Prog::D<id>` or `Prog::Bytes`) from `h`
into a Lean `List UInt8`, validating every byte is `< 256` under `toNat`. -/
def dataByteListDecode (enumName nilCtor consCtor : String) (toNat : F → Nat)
    (h : Heap F) : Nat → SourceValue F → Option (List UInt8)
  | 0, _ => none
  | _ + 1, .construct en ctor [] =>
    if en == enumName && ctor == nilCtor then some [] else none
  | fuel + 1, .construct en ctor [.field x, .ptr (.enum enTail) addr] =>
    if en == enumName && ctor == consCtor && enTail == enumName then
      let n := toNat x
      if n < 256 then
        match h[addr]? with
        | some tailVal =>
          (dataByteListDecode enumName nilCtor consCtor toNat h fuel tailVal).map
            (UInt8.ofNat n :: ·)
        | none => none
      else none
    else none
  | _ + 1, _ => none

/-- Unified computable byte-list decoder covering BOTH pointer-linked `Bytes::Stream`
(`&Lists::Node<UInt8::U8>`) and direct enum lists (`Prog::D<id>` / `Prog::Bytes`). -/
def byteListDecode (enumName nilCtor consCtor : String) (toNat : F → Nat)
    (h : Heap F) (fuel : Nat) (v : SourceValue F) : Option (List UInt8) :=
  match v with
  | .ptr _ _ => byteStreamDecode toNat h fuel v
  | .construct _ _ _ => dataByteListDecode enumName nilCtor consCtor toNat h fuel v
  | _ => none

/-- Soundness of `byteStreamDecode`: any decoded `bs` satisfies `ByteStreamRel` and
`isValidByteList`, provided `toNat` is a right inverse of `Nat.cast` below `256`. -/
theorem byteStreamDecode_sound {toNat : F → Nat}
    (hCast : ∀ x : F, toNat x < 256 → ((toNat x : Nat) : F) = x)
    {h : Heap F} :
    ∀ {fuel : Nat} {v : SourceValue F} {bs : List UInt8},
      byteStreamDecode toNat h fuel v = some bs →
      ByteStreamRel h bs v ∧ isValidByteList (bs.map UInt8.toNat)
  | 0, _, _, hdec => by simp [byteStreamDecode] at hdec
  | fuel + 1, v, bs, hdec => by
    cases v with
    | ptr ty addr =>
      cases ty with
      | «enum» en =>
        simp only [byteStreamDecode] at hdec
        split at hdec
        · next hen =>
          have henEq : en = byteStreamEnum := beq_iff_eq.mp hen
          subst henEq
          cases hcell : h[addr]? with
          | none => simp [hcell] at hdec
          | some cell =>
            rw [hcell] at hdec
            cases cell with
            | construct en' ctor args =>
              cases args with
              | nil =>
                by_cases hnil : ctor = "Nil"
                · subst hnil
                  simp only at hdec
                  split at hdec
                  · next hen' =>
                    have hEq : en' = byteStreamEnum := beq_iff_eq.mp hen'
                    subst hEq
                    cases hdec
                    exact ⟨.nil hcell, isValidByteList_nil⟩
                  · simp at hdec
                · cases ctor; simp [hnil] at hdec
              | cons a rest =>
                cases rest with
                | nil =>
                  cases ctor; simp at hdec
                | cons tailPtr rest2 =>
                  cases rest2 with
                  | cons _ _ => cases ctor; simp at hdec
                  | nil =>
                    cases a with
                    | field x =>
                      by_cases hcons : ctor = "Cons"
                      · subst hcons
                        simp only at hdec
                        split at hdec
                        · next hen' =>
                          have hEq : en' = byteStreamEnum := beq_iff_eq.mp hen'
                          subst hEq
                          split at hdec
                          · next hlt =>
                            cases ht : byteStreamDecode toNat h fuel tailPtr with
                            | none => simp [ht] at hdec
                            | some tail =>
                              rw [ht] at hdec
                              simp only [Option.map_some, Option.some.injEq] at hdec
                              subst hdec
                              obtain ⟨htRel, _⟩ := byteStreamDecode_sound hCast ht
                              have hbx : (bv (UInt8.ofNat (toNat x)) : SourceValue F) = .field x := by
                                rw [bv_ofNat hlt, hCast x hlt]
                              have hRel : ByteStreamRel h (UInt8.ofNat (toNat x) :: tail)
                                  (.ptr (.enum byteStreamEnum) addr) :=
                                .cons hcell (by rw [Aiur.Library.RepU8]; exact hbx.symm) htRel
                              exact ⟨hRel, isValidByteList_ofUInt8List _⟩
                          · simp at hdec
                        · simp at hdec
                      · cases ctor; simp [hcons] at hdec
                    | tuple _ | ptr _ _ | construct _ _ _ =>
                      cases ctor; simp at hdec
            | field _ | tuple _ | ptr _ _ => simp at hdec
        · simp at hdec
      | field | tuple _ | ptr _ => simp [byteStreamDecode] at hdec
    | field _ | tuple _ | construct _ _ _ => simp [byteStreamDecode] at hdec

/-- Soundness of `dataByteListDecode`: any decoded `bs` satisfies `DataByteListRel` and
`isValidByteList`, provided `toNat` is a right inverse of `Nat.cast` below `256`. -/
theorem dataByteListDecode_sound {enumName nilCtor consCtor : String} {toNat : F → Nat}
    (hCast : ∀ x : F, toNat x < 256 → ((toNat x : Nat) : F) = x)
    {h : Heap F} :
    ∀ {fuel : Nat} {v : SourceValue F} {bs : List UInt8},
      dataByteListDecode enumName nilCtor consCtor toNat h fuel v = some bs →
      DataByteListRel enumName nilCtor consCtor h bs v ∧ isValidByteList (bs.map UInt8.toNat)
  | 0, _, _, hdec => by simp [dataByteListDecode] at hdec
  | fuel + 1, v, bs, hdec => by
    cases v with
    | construct en ctor args =>
      cases args with
      | nil =>
        simp only [dataByteListDecode] at hdec
        split at hdec
        · next hcond =>
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          obtain ⟨rfl, rfl⟩ := hcond
          cases hdec
          exact ⟨.nil, isValidByteList_nil⟩
        · simp at hdec
      | cons a rest =>
        cases rest with
        | nil => simp [dataByteListDecode] at hdec
        | cons tail rest2 =>
          cases rest2 with
          | cons _ _ => simp [dataByteListDecode] at hdec
          | nil =>
            cases a with
            | field x =>
              cases tail with
              | ptr ty addr =>
                cases ty with
                | «enum» enTail =>
                  simp only [dataByteListDecode] at hdec
                  split at hdec
                  · next hcond =>
                    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
                    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hcond
                    split at hdec
                    · next hlt =>
                      cases hcell : h[addr]? with
                      | none => simp [hcell] at hdec
                      | some tailVal =>
                        simp only [hcell] at hdec
                        cases ht : dataByteListDecode enTail nilCtor ctor toNat h fuel tailVal with
                        | none => simp [ht] at hdec
                        | some tailBs =>
                          simp only [ht, Option.map_some, Option.some.injEq] at hdec
                          subst hdec
                          obtain ⟨htRel, _⟩ := dataByteListDecode_sound hCast ht
                          have hx : ((UInt8.ofNat (toNat x)).toNat : F) = x := by
                            rw [toNat_ofNat_lt hlt, hCast x hlt]
                          have hCons : DataByteListRel enTail nilCtor ctor h
                              (UInt8.ofNat (toNat x) :: tailBs)
                              (.construct enTail ctor [.field ((UInt8.ofNat (toNat x)).toNat : F), .ptr (.enum enTail) addr]) :=
                            .cons hcell htRel
                          rw [hx] at hCons
                          exact ⟨hCons, isValidByteList_ofUInt8List _⟩
                    · simp at hdec
                  · simp at hdec
                | field | tuple _ | ptr _ => simp [dataByteListDecode] at hdec
              | field _ | tuple _ | construct _ _ _ => simp [dataByteListDecode] at hdec
            | tuple _ | ptr _ _ | construct _ _ _ => simp [dataByteListDecode] at hdec
    | field _ | tuple _ | ptr _ _ => simp [dataByteListDecode] at hdec

/-- Unified soundness of `byteListDecode` for both `Bytes::Stream` and `Prog::D<id>`. -/
theorem byteListDecode_sound {enumName nilCtor consCtor : String} {toNat : F → Nat}
    (hCast : ∀ x : F, toNat x < 256 → ((toNat x : Nat) : F) = x)
    {h : Heap F} {fuel : Nat} {v : SourceValue F} {bs : List UInt8}
    (hdec : byteListDecode enumName nilCtor consCtor toNat h fuel v = some bs) :
    (ByteStreamRel h bs v ∨ DataByteListRel enumName nilCtor consCtor h bs v) ∧
    isValidByteList (bs.map UInt8.toNat) := by
  cases v with
  | ptr _ _ =>
    obtain ⟨hr, hv⟩ := byteStreamDecode_sound hCast hdec
    exact ⟨.inl hr, hv⟩
  | construct _ _ _ =>
    obtain ⟨hr, hv⟩ := dataByteListDecode_sound hCast hdec
    exact ⟨.inr hr, hv⟩
  | field _ | tuple _ => simp [byteListDecode] at hdec

end Representations

/-- Completeness of `byteStreamDecode` over any prime field `ZMod p` with `256 ≤ p`. -/
theorem byteStreamDecode_complete {p : Nat} [Fact (Nat.Prime p)] (hp : 256 ≤ p)
    {h : Heap (ZMod p)} {bs : List UInt8} {v : SourceValue (ZMod p)}
    (hr : ByteStreamRel h bs v) :
    ∀ {fuel : Nat}, bs.length < fuel → byteStreamDecode ZMod.val h fuel v = some bs := by
  induction hr with
  | @nil addr hcell =>
    intro fuel hlt
    cases fuel with
    | zero => omega
    | succ f =>
      simp [byteStreamDecode, hcell]
  | @cons b bs addr headVal tailPtr hcell hhead _ ih =>
    intro fuel hlt
    cases fuel with
    | zero => omega
    | succ f =>
      have hheadEq : headVal = Value.field (b.toNat : ZMod p) := hhead
      subst hheadEq
      have hbLt : b.toNat < 256 := b.toNat_lt
      have hval : (b.toNat : ZMod p).val = b.toNat :=
        ZMod.val_natCast_of_lt (lt_of_lt_of_le hbLt hp)
      have hof : UInt8.ofNat b.toNat = b := UInt8.ofNat_toNat
      have hf : bs.length < f := by simp at hlt; omega
      simp [byteStreamDecode, hcell, hval, hbLt, ih hf, hof]

/-- Completeness of `dataByteListDecode` over any prime field `ZMod p` with `256 ≤ p`. -/
theorem dataByteListDecode_complete {p : Nat} [Fact (Nat.Prime p)] (hp : 256 ≤ p)
    {enumName nilCtor consCtor : String} {h : Heap (ZMod p)} {bs : List UInt8}
    {v : SourceValue (ZMod p)} (hr : DataByteListRel enumName nilCtor consCtor h bs v) :
    ∀ {fuel : Nat}, bs.length < fuel →
      dataByteListDecode enumName nilCtor consCtor ZMod.val h fuel v = some bs := by
  induction hr with
  | nil =>
    intro fuel hlt
    cases fuel with
    | zero => omega
    | succ f => simp [dataByteListDecode]
  | @cons b bs addr tailVal hcell _ ih =>
    intro fuel hlt
    cases fuel with
    | zero => omega
    | succ f =>
      have hbLt : b.toNat < 256 := b.toNat_lt
      have hval : (b.toNat : ZMod p).val = b.toNat :=
        ZMod.val_natCast_of_lt (lt_of_lt_of_le hbLt hp)
      have hof : UInt8.ofNat b.toNat = b := UInt8.ofNat_toNat
      have hf : bs.length < f := by simp at hlt; omega
      simp [dataByteListDecode, hcell, hval, hbLt, ih hf, hof]

/-! ## Section 2: Formal Aiur `StarkIO` & `KzgIO` Ingress Modules -/

/-- Source-level Formal Aiur type aliases for witness-stream modules. -/
def u8Ty : Lower.Ty := .named "UInt8::U8" []
def u32Ty : Lower.Ty := .named "UInt32::U32" []
def byteStreamTy : Lower.Ty := .named "Bytes::Stream" []
def wordListTy : Lower.Ty := .named "Lists::List" [u32Ty]
def kzgInputTy : Lower.Ty := .tuple [wordListTy, .field]

private def listNilE (elemTy : Lower.Ty) : Expr :=
  .store (.construct "Lists::Node" (some [elemTy]) "Nil" [])

private def listConsE (elemTy : Lower.Ty) (hd tl : Expr) : Expr :=
  .store (.construct "Lists::Node" (some [elemTy]) "Cons" [hd, tl])

private def starkIoRead1Arm (selfName : String) (elemTy : Lower.Ty) : Expr :=
  .letValue (.array [.bind "byte"])
    (.hint (.array .field 1) (.tuple [vE "channel", vE "idx"]) "stark.io.read1") <|
  letE "tail" (callE selfName [vE "channel", addE (vE "idx") (litE 1), subE (vE "len") (litE 1)]) <|
  listConsE elemTy (callE "UInt8::from_field" [vE "byte"]) (vE "tail")

private def starkIoRead8Arm (selfName : String) (elemTy : Lower.Ty) : Expr :=
  .letValue (.array [.bind "b0", .bind "b1", .bind "b2", .bind "b3",
                     .bind "b4", .bind "b5", .bind "b6", .bind "b7"])
    (.hint (.array .field 8) (.tuple [vE "channel", vE "idx"]) "stark.io.read8") <|
  .letValue (.tuple [.bind "c0", .bind "c1"]) (callE "UInt8::from_fields" [vE "b0", vE "b1"]) <|
  .letValue (.tuple [.bind "c2", .bind "c3"]) (callE "UInt8::from_fields" [vE "b2", vE "b3"]) <|
  .letValue (.tuple [.bind "c4", .bind "c5"]) (callE "UInt8::from_fields" [vE "b4", vE "b5"]) <|
  .letValue (.tuple [.bind "c6", .bind "c7"]) (callE "UInt8::from_fields" [vE "b6", vE "b7"]) <|
  letE "tail" (callE selfName [vE "channel", addE (vE "idx") (litE 8), subE (vE "len") (litE 8)]) <|
  listConsE elemTy (vE "c0") <|
  listConsE elemTy (vE "c1") <|
  listConsE elemTy (vE "c2") <|
  listConsE elemTy (vE "c3") <|
  listConsE elemTy (vE "c4") <|
  listConsE elemTy (vE "c5") <|
  listConsE elemTy (vE "c6") <|
  listConsE elemTy (vE "c7") (vE "tail")

private def starkIoReadStreamBody (selfName : String) (elemTy : Lower.Ty) : Expr :=
  let arm1 := starkIoRead1Arm selfName elemTy
  matchE (vE "len")
    [(.literal 0, listNilE elemTy),
     (.literal 1, arm1), (.literal 2, arm1), (.literal 3, arm1),
     (.literal 4, arm1), (.literal 5, arm1), (.literal 6, arm1), (.literal 7, arm1),
     (.wildcard, starkIoRead8Arm selfName elemTy)]

/-- `StarkIO::read_byte_stream(channel: Field, idx: Field, len: Field) -> Bytes::Stream`,
matching `MultiStark.Source.starkIO`'s exact channels (`"stark.io.read1"`, `"stark.io.read8"`)
and `UInt8::from_field` / `UInt8::from_fields` checked-byte validation. -/
def starkIoReadStreamFn : Fn :=
  { name := "read_byte_stream"
    params := [("channel", .field), ("idx", .field), ("len", .field)]
    result := byteStreamTy
    isInline := false
    body := starkIoReadStreamBody "read_byte_stream" u8Ty }

/-- `StarkIO::read_channel(channel: Field) -> Bytes::Stream`: queries `"stark.io.info"`
for `(idx, len)` and delegates to `StarkIO::read_byte_stream`. -/
def starkIoChannelFn : Fn :=
  { name := "read_channel"
    params := [("channel", .field)]
    result := byteStreamTy
    isInline := false
    body :=
      .letValue (.tuple [.bind "idx", .bind "len"])
        (.hint (.tuple [.field, .field]) (.tuple [vE "channel", litE 0]) "stark.io.info") <|
      callE "read_byte_stream" [vE "channel", vE "idx", vE "len"] }

/-- Formal Aiur module `StarkIO` exporting `read_byte_stream` and `read_channel`. -/
def starkIOModule : Aiur.Modules.Program Nat :=
  { modules := [{
      name := "StarkIO"
      body := .definitions {
        program := { functions := [starkIoReadStreamFn, starkIoChannelFn] }
      }
    }] }

/-! ### `KzgIO` Ingress Functions (`"kzg.io.length"`, `"kzg.io.read4"`, `"kzg.io.read1"`, `"kzg.io.div"`) -/

private def kzgReadWordsBody (selfName : String) (elemTy : Lower.Ty) : Expr :=
  matchE (vE "remaining")
    [(.literal 0, listNilE elemTy),
     (.wildcard,
      letE "word"
        (callE "UInt32::from_fields"
          [.hint (.array .field 4) (.tuple [vE "channel", vE "offset"]) "kzg.io.read4"]) <|
      listConsE elemTy (vE "word")
        (callE selfName [vE "channel", subE (vE "remaining") (litE 1), addE (vE "offset") (litE 4)]))]

/-- `KzgIO::read_words(channel: Field, remaining: Field, offset: Field) -> Lists::List<UInt32::U32>`. -/
def kzgIoReadWordsFn : Fn :=
  { name := "read_words"
    params := [("channel", .field), ("remaining", .field), ("offset", .field)]
    result := wordListTy
    isInline := false
    body := kzgReadWordsBody "read_words" u32Ty }

/-- `KzgIO::read_byte(channel: Field, offset: Field) -> UInt8::U8`. -/
def kzgIoReadByteFn : Fn :=
  { name := "read_byte"
    params := [("channel", .field), ("offset", .field)]
    result := u8Ty
    isInline := true
    body := callE "UInt8::from_field"
      [.hint .field (.tuple [vE "channel", vE "offset"]) "kzg.io.read1"] }

/-- `KzgIO::split4(count: Field) -> (Field, Field)`: splits `count = 4 * words + lead`
with `lead ∈ {0, 1, 2, 3}` via `"kzg.io.div"`. -/
def kzgIoSplit4Fn : Fn :=
  { name := "split4"
    params := [("count", .field)]
    result := .tuple [.field, .field]
    isInline := false
    body :=
      letE "words" (.hint .field (.tuple [vE "count", litE 4]) "kzg.io.div") <|
      letE "lead" (subE (vE "count") (.binary .mul (litE 4) (vE "words"))) <|
      matchE (vE "lead")
        [(.literal 0, .tuple [vE "words", litE 0]),
         (.literal 1, .tuple [vE "words", litE 1]),
         (.literal 2, .tuple [vE "words", litE 2]),
         (.literal 3, .tuple [vE "words", litE 3])] }

private def kzgSizedChannelBody (splitName readWordsName readByteName : String) (elemTy : Lower.Ty) : Expr :=
  letE "length" (.hint .field (vE "channel") "kzg.io.length") <|
  seqE (.builtin (.assertEq (assertion "KZG input exceeds 64 MiB"))
    [callE "UInt32::less_than_fields" [vE "length", litE 67108865], litE 1]) <|
  .letValue (.tuple [.bind "words", .bind "lead"]) (callE splitName [vE "length"]) <|
  letE "zero" (callE "UInt8::from_field" [litE 0]) <|
  letE "input"
    (matchE (vE "lead")
      [(.literal 0, .tuple [callE readWordsName [vE "channel", vE "words", litE 0], litE 0]),
       (.literal 1,
        .tuple [listConsE elemTy
          (callE "UInt32::from_bytes"
            [.array [vE "zero", vE "zero", vE "zero", callE readByteName [vE "channel", litE 0]]])
          (callE readWordsName [vE "channel", vE "words", litE 1]), litE 3]),
       (.literal 2,
        .tuple [listConsE elemTy
          (callE "UInt32::from_bytes"
            [.array [vE "zero", vE "zero",
              callE readByteName [vE "channel", litE 0],
              callE readByteName [vE "channel", litE 1]]])
          (callE readWordsName [vE "channel", vE "words", litE 2]), litE 2]),
       (.literal 3,
        .tuple [listConsE elemTy
          (callE "UInt32::from_bytes"
            [.array [vE "zero",
              callE readByteName [vE "channel", litE 0],
              callE readByteName [vE "channel", litE 1],
              callE readByteName [vE "channel", litE 2]]])
          (callE readWordsName [vE "channel", vE "words", litE 3]), litE 1])]) <|
  .tuple [vE "input", vE "length"]

/-- `KzgIO::sized_channel(channel: Field) -> ((Lists::List<UInt32::U32>, Field), Field)`,
matching `MultiStark.Source.kzgIO`'s exact channels (`"kzg.io.length"`, `"kzg.io.div"`,
`"kzg.io.read1"`, `"kzg.io.read4"`), 64 MiB upper bound, and checked `UInt8`/`UInt32` validation. -/
def kzgIoSizedChannelFn : Fn :=
  { name := "sized_channel"
    params := [("channel", .field)]
    result := .tuple [kzgInputTy, .field]
    isInline := false
    body := kzgSizedChannelBody "split4" "read_words" "read_byte" u32Ty }

private def kzgReadWordsStreamBody (selfName : String) (elemTy : Lower.Ty) : Expr :=
  matchE (vE "remaining")
    [(.literal 0, listNilE elemTy),
     (.wildcard,
      letE "word"
        (callE "UInt32::from_fields"
          [.hint (.array .field 4) (.tuple [vE "channel", vE "offset"]) "kzg.io.read4"]) <|
      letE "bs" (callE "UInt32::to_bytes" [vE "word"]) <|
      letE "tail"
        (callE selfName [vE "channel", subE (vE "remaining") (litE 1), addE (vE "offset") (litE 4)]) <|
      listConsE elemTy (.index (vE "bs") 0) <|
      listConsE elemTy (.index (vE "bs") 1) <|
      listConsE elemTy (.index (vE "bs") 2) <|
      listConsE elemTy (.index (vE "bs") 3) (vE "tail"))]

/-- `KzgIO::read_words_stream(channel: Field, remaining: Field, offset: Field) -> Bytes::Stream`:
reads `remaining` 4-byte checked words via `"kzg.io.read4"` directly into a `Bytes::Stream`. -/
def kzgIoReadWordsStreamFn : Fn :=
  { name := "read_words_stream"
    params := [("channel", .field), ("remaining", .field), ("offset", .field)]
    result := byteStreamTy
    isInline := false
    body := kzgReadWordsStreamBody "read_words_stream" u8Ty }

private def kzgReadStreamBody (splitName readWordsStreamName readByteName : String) (elemTy : Lower.Ty) : Expr :=
  letE "length" (.hint .field (vE "channel") "kzg.io.length") <|
  seqE (.builtin (.assertEq (assertion "KZG input exceeds 64 MiB"))
    [callE "UInt32::less_than_fields" [vE "length", litE 67108865], litE 1]) <|
  .letValue (.tuple [.bind "words", .bind "lead"]) (callE splitName [vE "length"]) <|
  matchE (vE "lead")
    [(.literal 0, callE readWordsStreamName [vE "channel", vE "words", litE 0]),
     (.literal 1,
      letE "b0" (callE readByteName [vE "channel", litE 0]) <|
      letE "tail" (callE readWordsStreamName [vE "channel", vE "words", litE 1]) <|
      listConsE elemTy (vE "b0") (vE "tail")),
     (.literal 2,
      letE "b0" (callE readByteName [vE "channel", litE 0]) <|
      letE "b1" (callE readByteName [vE "channel", litE 1]) <|
      letE "tail" (callE readWordsStreamName [vE "channel", vE "words", litE 2]) <|
      listConsE elemTy (vE "b0") (listConsE elemTy (vE "b1") (vE "tail"))),
     (.literal 3,
      letE "b0" (callE readByteName [vE "channel", litE 0]) <|
      letE "b1" (callE readByteName [vE "channel", litE 1]) <|
      letE "b2" (callE readByteName [vE "channel", litE 2]) <|
      letE "tail" (callE readWordsStreamName [vE "channel", vE "words", litE 3]) <|
      listConsE elemTy (vE "b0") (listConsE elemTy (vE "b1") (listConsE elemTy (vE "b2") (vE "tail"))))]

/-- `KzgIO::read_stream(channel: Field) -> Bytes::Stream`: reads a KZG channel directly into a
checked `Bytes::Stream` (`Lists::List<UInt8::U8>`) ready for `Blake3::hash` or pure-Lean decoding. -/
def kzgIoReadStreamFn : Fn :=
  { name := "read_stream"
    params := [("channel", .field)]
    result := byteStreamTy
    isInline := false
    body := kzgReadStreamBody "split4" "read_words_stream" "read_byte" u8Ty }

/-- Formal Aiur module `KzgIO` exporting `read_words`, `read_byte`, `split4`, `sized_channel`,
`read_words_stream`, and `read_stream`. -/
def kzgIOModule : Aiur.Modules.Program Nat :=
  { modules := [{
      name := "KzgIO"
      body := .definitions {
        program := {
          functions := [
            kzgIoReadWordsFn,
            kzgIoReadByteFn,
            kzgIoSplit4Fn,
            kzgIoSizedChannelFn,
            kzgIoReadWordsStreamFn,
            kzgIoReadStreamFn
          ]
        }
      }
    }] }

/-- Combined Formal Aiur witness-IO modules (`StarkIO` + `KzgIO`). -/
def witnessIOModules : Aiur.Modules.Program Nat :=
  starkIOModule.append kzgIOModule

/-! ### Plainness Proofs for All `StarkIO` / `KzgIO` Ingress Functions -/

theorem isPlainExpr_starkIoReadStreamFn : isPlainExpr starkIoReadStreamFn.body = true := rfl
theorem isPlainExpr_starkIoChannelFn : isPlainExpr starkIoChannelFn.body = true := rfl
theorem isPlainExpr_kzgIoReadWordsFn : isPlainExpr kzgIoReadWordsFn.body = true := rfl
theorem isPlainExpr_kzgIoReadByteFn : isPlainExpr kzgIoReadByteFn.body = true := rfl
theorem isPlainExpr_kzgIoSplit4Fn : isPlainExpr kzgIoSplit4Fn.body = true := rfl
theorem isPlainExpr_kzgIoSizedChannelFn : isPlainExpr kzgIoSizedChannelFn.body = true := rfl
theorem isPlainExpr_kzgIoReadWordsStreamFn : isPlainExpr kzgIoReadWordsStreamFn.body = true := rfl
theorem isPlainExpr_kzgIoReadStreamFn : isPlainExpr kzgIoReadStreamFn.body = true := rfl

/-! ## Section 3: Elaborated Bodies, World Hypotheses & Executable World Checkers -/

section WorldContracts

variable {F : Type} [Field F] [DecidableEq F]

/-- Elaborated body of `StarkIO::read_byte_stream` over `F`. -/
def starkIoReadStreamBodyF : Aiur.Generic.Expr F :=
  (starkIoReadStreamBody "StarkIO::read_byte_stream" .field).map (Nat.cast : Nat → F)

/-- Elaborated body of `StarkIO::read_channel` over `F`. -/
def starkIoChannelBodyF : Aiur.Generic.Expr F :=
  (Aiur.Generic.Expr.letValue (.tuple [.bind "idx", .bind "len"])
    (.hint (.tuple [.field, .field]) (.tuple [vE "channel", litE 0]) "stark.io.info")
    (callE "StarkIO::read_byte_stream" [vE "channel", vE "idx", vE "len"])).map (Nat.cast : Nat → F)

/-- Elaborated body of `KzgIO::read_words` over `F`. -/
def kzgIoReadWordsBodyF : Aiur.Generic.Expr F :=
  (kzgReadWordsBody "KzgIO::read_words" (.array .field 4)).map (Nat.cast : Nat → F)

/-- Elaborated body of `KzgIO::read_byte` over `F`. -/
def kzgIoReadByteBodyF : Aiur.Generic.Expr F :=
  kzgIoReadByteFn.body.map (Nat.cast : Nat → F)

/-- Elaborated body of `KzgIO::split4` over `F`. -/
def kzgIoSplit4BodyF : Aiur.Generic.Expr F :=
  kzgIoSplit4Fn.body.map (Nat.cast : Nat → F)

/-- Elaborated body of `KzgIO::sized_channel` over `F`. -/
def kzgIoSizedChannelBodyF : Aiur.Generic.Expr F :=
  (kzgSizedChannelBody "KzgIO::split4" "KzgIO::read_words" "KzgIO::read_byte"
    (.array .field 4)).map (Nat.cast : Nat → F)

/-- Elaborated body of `KzgIO::read_words_stream` over `F`. -/
def kzgIoReadWordsStreamBodyF : Aiur.Generic.Expr F :=
  (kzgReadWordsStreamBody "KzgIO::read_words_stream" .field).map (Nat.cast : Nat → F)

/-- Elaborated body of `KzgIO::read_stream` over `F`. -/
def kzgIoReadStreamBodyF : Aiur.Generic.Expr F :=
  (kzgReadStreamBody "KzgIO::split4" "KzgIO::read_words_stream" "KzgIO::read_byte"
    .field).map (Nat.cast : Nat → F)

omit [DecidableEq F] in
theorem isPlainExpr_starkIoReadStreamBodyF : isPlainExpr (starkIoReadStreamBodyF (F := F)) = true := by
  rw [starkIoReadStreamBodyF, Lower.isPlainExpr_map]; rfl
omit [DecidableEq F] in
theorem isPlainExpr_starkIoChannelBodyF : isPlainExpr (starkIoChannelBodyF (F := F)) = true := by
  rw [starkIoChannelBodyF, Lower.isPlainExpr_map]; rfl
omit [DecidableEq F] in
theorem isPlainExpr_kzgIoReadWordsBodyF : isPlainExpr (kzgIoReadWordsBodyF (F := F)) = true := by
  rw [kzgIoReadWordsBodyF, Lower.isPlainExpr_map]; rfl
omit [DecidableEq F] in
theorem isPlainExpr_kzgIoReadByteBodyF : isPlainExpr (kzgIoReadByteBodyF (F := F)) = true := by
  rw [kzgIoReadByteBodyF, Lower.isPlainExpr_map]; rfl
omit [DecidableEq F] in
theorem isPlainExpr_kzgIoSplit4BodyF : isPlainExpr (kzgIoSplit4BodyF (F := F)) = true := by
  rw [kzgIoSplit4BodyF, Lower.isPlainExpr_map]; rfl
omit [DecidableEq F] in
theorem isPlainExpr_kzgIoSizedChannelBodyF : isPlainExpr (kzgIoSizedChannelBodyF (F := F)) = true := by
  rw [kzgIoSizedChannelBodyF, Lower.isPlainExpr_map]; rfl
omit [DecidableEq F] in
theorem isPlainExpr_kzgIoReadWordsStreamBodyF : isPlainExpr (kzgIoReadWordsStreamBodyF (F := F)) = true := by
  rw [kzgIoReadWordsStreamBodyF, Lower.isPlainExpr_map]; rfl
omit [DecidableEq F] in
theorem isPlainExpr_kzgIoReadStreamBodyF : isPlainExpr (kzgIoReadStreamBodyF (F := F)) = true := by
  rw [kzgIoReadStreamBodyF, Lower.isPlainExpr_map]; rfl

/-- Checked byte-validation contracts required by `StarkIO` (`UInt8::from_field` and
`UInt8::from_fields`). Discharged directly from `Blake3Spec.Blake3LibraryWorld` or
`TypedWorld.U32LibraryContracts` + `UInt8::from_field` table check. -/
structure WitnessByteContracts (world : World F) : Prop where
  u8_from_field : ∀ v h r h',
    EvalFn world "UInt8::from_field" [v] h r h' →
    r = v ∧ h' = h ∧ ∃ b : Nat, b < 256 ∧ v = .field (b : F)
  u8_from_fields : ∀ v1 v2 h r h',
    EvalFn world "UInt8::from_fields" [v1, v2] h r h' →
    r = .tuple [v1, v2] ∧ h' = h ∧
    ∃ a b : Nat, a < 256 ∧ b < 256 ∧ v1 = .field (a : F) ∧ v2 = .field (b : F)

/-- Checked word-validation contracts required by `KzgIO` (`UInt8::from_field`,
`UInt32::from_fields`, `UInt32::from_bytes`, `UInt32::to_bytes`). -/
structure WitnessWordContracts (world : World F) : Prop where
  u8_from_field : ∀ v h r h',
    EvalFn world "UInt8::from_field" [v] h r h' →
    r = v ∧ h' = h ∧ ∃ b : Nat, b < 256 ∧ v = .field (b : F)
  u32_from_fields : ∀ v h r h',
    EvalFn world "UInt32::from_fields" [v] h r h' →
    h' = h ∧ ∃ w : UInt32, r = wv w
  u32_from_bytes : ∀ v h r h',
    EvalFn world "UInt32::from_bytes" [v] h r h' →
    r = v ∧ h' = h
  u32_to_bytes : ∀ v h r h',
    EvalFn world "UInt32::to_bytes" [v] h r h' →
    r = v ∧ h' = h

/-- World hypothesis for `StarkIO` ingress functions. -/
structure StarkIOWorld (world : World F) : Prop where
  bytes : WitnessByteContracts world
  read_byte_stream :
    WorldHasFn world "StarkIO::read_byte_stream" ["channel", "idx", "len"] starkIoReadStreamBodyF
  read_channel :
    WorldHasFn world "StarkIO::read_channel" ["channel"] starkIoChannelBodyF

/-- World hypothesis for `KzgIO` ingress functions. -/
structure KzgIOWorld (world : World F) : Prop where
  words : WitnessWordContracts world
  read_words :
    WorldHasFn world "KzgIO::read_words" ["channel", "remaining", "offset"] kzgIoReadWordsBodyF
  read_byte :
    WorldHasFn world "KzgIO::read_byte" ["channel", "offset"] kzgIoReadByteBodyF
  split4 :
    WorldHasFn world "KzgIO::split4" ["count"] kzgIoSplit4BodyF
  sized_channel :
    WorldHasFn world "KzgIO::sized_channel" ["channel"] kzgIoSizedChannelBodyF
  read_words_stream :
    WorldHasFn world "KzgIO::read_words_stream" ["channel", "remaining", "offset"] kzgIoReadWordsStreamBodyF
  read_stream :
    WorldHasFn world "KzgIO::read_stream" ["channel"] kzgIoReadStreamBodyF

private def checkFnBody (s : Generic.Source F) (nm : String) (ps : List String)
    (body : Aiur.Generic.Expr F) : Bool :=
  match s.program.findFunction? nm with
  | some f => f.typeParams.isEmpty && (f.params.map Prod.fst == ps) && (f.body == body)
  | none => false

/-- Executable check that `StarkIO::read_byte_stream` and `StarkIO::read_channel` are bound
in `s` with their exact elaborated bodies. -/
def checkStarkIOFunctions (s : Generic.Source F) : Bool :=
  checkFnBody s "StarkIO::read_byte_stream" ["channel", "idx", "len"] starkIoReadStreamBodyF &&
  checkFnBody s "StarkIO::read_channel" ["channel"] starkIoChannelBodyF

/-- Executable check that all 6 `KzgIO` ingress functions are bound in `s` with their exact
elaborated bodies. -/
def checkKzgIOFunctions (s : Generic.Source F) : Bool :=
  checkFnBody s "KzgIO::read_words" ["channel", "remaining", "offset"] kzgIoReadWordsBodyF &&
  checkFnBody s "KzgIO::read_byte" ["channel", "offset"] kzgIoReadByteBodyF &&
  checkFnBody s "KzgIO::split4" ["count"] kzgIoSplit4BodyF &&
  checkFnBody s "KzgIO::sized_channel" ["channel"] kzgIoSizedChannelBodyF &&
  checkFnBody s "KzgIO::read_words_stream" ["channel", "remaining", "offset"] kzgIoReadWordsStreamBodyF &&
  checkFnBody s "KzgIO::read_stream" ["channel"] kzgIoReadStreamBodyF

theorem starkIOWorld_of_check {s : Generic.Source F}
    (hb : WitnessByteContracts s.world) (h : checkStarkIOFunctions s = true) :
    StarkIOWorld s.world := by
  simp only [checkStarkIOFunctions, checkFnBody, Bool.and_eq_true] at h
  exact {
    bytes := hb
    read_byte_stream := worldHasFn_of_check s (by decide) h.1
    read_channel := worldHasFn_of_check s (by decide) h.2
  }

theorem kzgIOWorld_of_check {s : Generic.Source F}
    (hw : WitnessWordContracts s.world) (h : checkKzgIOFunctions s = true) :
    KzgIOWorld s.world := by
  simp only [checkKzgIOFunctions, checkFnBody, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact {
    words := hw
    read_words := worldHasFn_of_check s (by decide) h1
    read_byte := worldHasFn_of_check s (by decide) h2
    split4 := worldHasFn_of_check s (by decide) h3
    sized_channel := worldHasFn_of_check s (by decide) h4
    read_words_stream := worldHasFn_of_check s (by decide) h5
    read_stream := worldHasFn_of_check s (by decide) h6
  }

/-- Build `WitnessByteContracts` directly from `Blake3Spec.Blake3LibraryWorld`. -/
theorem witnessByteContracts_of_blake3 {world : World F}
    (lib : Blake3Spec.Blake3LibraryWorld world) : WitnessByteContracts world where
  u8_from_field := lib.maps.from_field
  u8_from_fields := fun v1 v2 h r h' ev => by
    obtain ⟨_, b⟩ := evalFn_plain_inv lib.u8_from_fields rfl ev
    obtain ⟨_, _, hcall, hret⟩ := evalExpr_let_wildcard_inv b
    obtain ⟨va, vb, _, _, eva, evb, hcal⟩ := evalExpr_call2_inv hcall
    obtain ⟨hla, rfl⟩ := evalExpr_var_inv eva
    obtain ⟨hlb, rfl⟩ := evalExpr_var_inv evb
    simp at hla hlb
    subst hla hlb
    obtain ⟨_, rfl, a, b', ha, hb, rfl, rfl⟩ := lib.maps.range_pair _ _ _ _ _ hcal
    obtain ⟨va', vb', _, eva', evb', rfl⟩ := evalExpr_tuple2_inv hret
    obtain ⟨hla', rfl⟩ := evalExpr_var_inv eva'
    obtain ⟨hlb', rfl⟩ := evalExpr_var_inv evb'
    simp at hla' hlb'
    subst hla' hlb'
    exact ⟨rfl, rfl, a, b', ha, hb, rfl, rfl⟩

/-- Build `WitnessWordContracts` directly from `Blake3Spec.Blake3LibraryWorld`. -/
theorem witnessWordContracts_of_blake3 {world : World F}
    (lib : Blake3Spec.Blake3LibraryWorld world) : WitnessWordContracts world where
  u8_from_field := lib.maps.from_field
  u32_from_fields := fun v h r h' ev => by
    obtain ⟨_, b⟩ := evalFn_plain_inv lib.u32_from_fields rfl ev
    obtain ⟨va, vb, h1, hcal1, rest1⟩ := evalExpr_let_tuple2_inv b
    obtain ⟨v0, v1, h2, h3, e0, e1, hc1⟩ := evalExpr_call2_inv hcal1
    obtain ⟨w0, ew0, _⟩ := evalExpr_index_inv e0
    obtain ⟨hl0, rfl⟩ := evalExpr_var_inv ew0
    simp at hl0; subst hl0
    obtain ⟨w1, ew1, _⟩ := evalExpr_index_inv e1
    obtain ⟨hl1, rfl⟩ := evalExpr_var_inv ew1
    simp at hl1; subst hl1
    have hb := witnessByteContracts_of_blake3 lib
    obtain ⟨htup1, rfl, a0, a1, ha0, ha1, rfl, rfl⟩ := hb.u8_from_fields _ _ _ _ _ hc1
    injection htup1 with hcons1
    injection hcons1 with hva hcons1'
    injection hcons1' with hvb _
    subst hva hvb
    obtain ⟨vc, vd, h4, hcal2, rest2⟩ := evalExpr_let_tuple2_inv rest1
    obtain ⟨v2, v3, h5, h6, e2, e3, hc2⟩ := evalExpr_call2_inv hcal2
    obtain ⟨w2, ew2, _⟩ := evalExpr_index_inv e2
    obtain ⟨hl2, rfl⟩ := evalExpr_var_inv ew2
    simp at hl2; subst hl2
    obtain ⟨w3, ew3, _⟩ := evalExpr_index_inv e3
    obtain ⟨hl3, rfl⟩ := evalExpr_var_inv ew3
    simp at hl3; subst hl3
    obtain ⟨htup2, rfl, a2, a3, ha2, ha3, rfl, rfl⟩ := hb.u8_from_fields _ _ _ _ _ hc2
    injection htup2 with hcons2
    injection hcons2 with hvc hcons2'
    injection hcons2' with hvd _
    subst hvc hvd
    cases rest2 with
    | array hargs =>
      cases hargs with | cons p0 t0 =>
      cases t0 with | cons p1 t1 =>
      cases t1 with | cons p2 t2 =>
      cases t2 with | cons p3 t3 =>
      cases t3
      obtain ⟨hlp0, rfl⟩ := evalExpr_var_inv p0
      obtain ⟨hlp1, rfl⟩ := evalExpr_var_inv p1
      obtain ⟨hlp2, rfl⟩ := evalExpr_var_inv p2
      obtain ⟨hlp3, rfl⟩ := evalExpr_var_inv p3
      simp at hlp0 hlp1 hlp2 hlp3
      subst hlp0 hlp1 hlp2 hlp3
      refine ⟨rfl, Aiur.Library.Blake3.wordOfBytes
        (UInt8.ofNat a0) (UInt8.ofNat a1) (UInt8.ofNat a2) (UInt8.ofNat a3), ?_⟩
      rw [Blake3Spec.wv_wordOfBytes, w4, bv_ofNat ha0, bv_ofNat ha1, bv_ofNat ha2, bv_ofNat ha3]
  u32_from_bytes := fun v h r h' ev => by
    obtain ⟨_, b⟩ := evalFn_plain_inv lib.u32_from_bytes rfl ev
    obtain ⟨hl, rfl⟩ := evalExpr_var_inv b
    simp at hl
    exact ⟨hl.symm, rfl⟩
  u32_to_bytes := fun v h r h' ev => by
    obtain ⟨_, b⟩ := evalFn_plain_inv lib.u32_to_bytes rfl ev
    obtain ⟨hl, rfl⟩ := evalExpr_var_inv b
    simp at hl
    exact ⟨hl.symm, rfl⟩

end WorldContracts

/-! ## Section 4: Certified Witness Stream Existence & NP Backward Soundness Theorems -/

section SoundnessProofs

variable {F : Type} [Field F] [DecidableEq F]

/-! ### Helper `EvalExprN` Inversion Lemmas -/

private theorem evalExprN_hint_inv {world : World F} {d : Nat} {types : Types}
    {locals : Environment F Nat} {ty : Generic.Ty} {e : Aiur.Generic.Expr F} {ch : String}
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d types locals (.hint ty e ch) h r h') :
    ∃ (inp : SourceValue F) (c : Constant F),
      EvalExprN world d types locals e h inp h' ∧
      world.typed (ty.subst types).toCore c = true ∧
      r = c.toValue := by
  cases ev with
  | hint hk hty => exact ⟨_, _, hk, hty, rfl⟩

private theorem evalExprN_match_inv {world : World F} {d : Nat} {types : Types}
    {locals : Environment F Nat} {scr : Aiur.Generic.Expr F}
    {arms : List (Aiur.Generic.Pattern F × Aiur.Generic.Expr F)}
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d types locals (.matchValue scr arms) h r h') :
    ∃ v hm bs body,
      EvalExprN world d types locals scr h v hm ∧
      selectArm world types hm v arms = .ok (some (bs, body)) ∧
      EvalExprN world d types (bs ++ locals) body hm r h' := by
  cases ev with
  | matchValue hv hsel hb => exact ⟨_, _, _, _, hv, hsel, hb⟩

private theorem evalExprN_let_tuple2_inv {world : World F} {d : Nat} {types : Types}
    {locals : Environment F Nat} {x y : String} {e b : Aiur.Generic.Expr F}
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d types locals
      (.letValue (.tuple [.bind x, .bind y]) e b) h r h') :
    ∃ vx vy hm,
      EvalExprN world d types locals e h (.tuple [vx, vy]) hm ∧
      EvalExprN world d types ((x, vx) :: (y, vy) :: locals) b hm r h' := by
  cases ev with
  | letValue hv hm hb =>
    rename_i inp _ bindings
    cases inp with
    | tuple vs =>
      rcases vs with _ | ⟨vx, _ | ⟨vy, _ | _⟩⟩ <;>
        simp [World.matchPattern, matchPatternWith, matchListWith] at hm
      subst hm
      exact ⟨vx, vy, _, hv, hb⟩
    | field _ | ptr _ _ | construct _ _ _ => simp [World.matchPattern, matchPatternWith] at hm

private theorem evalExprN_let_array1_inv {world : World F} {d : Nat} {types : Types}
    {locals : Environment F Nat} {x : String} {e b : Aiur.Generic.Expr F}
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d types locals (.letValue (.array [.bind x]) e b) h r h') :
    ∃ vx hm,
      EvalExprN world d types locals e h (.tuple [vx]) hm ∧
      EvalExprN world d types ((x, vx) :: locals) b hm r h' := by
  cases ev with
  | letValue hv hm hb =>
    rename_i inp _ bindings
    cases inp with
    | tuple vs =>
      rcases vs with _ | ⟨vx, _ | _⟩ <;>
        simp [World.matchPattern, matchPatternWith, matchListWith] at hm
      subst hm
      exact ⟨vx, _, hv, hb⟩
    | field _ | ptr _ _ | construct _ _ _ => simp [World.matchPattern, matchPatternWith] at hm

private theorem evalExprN_let_array8_inv {world : World F} {d : Nat} {types : Types}
    {locals : Environment F Nat} {x0 x1 x2 x3 x4 x5 x6 x7 : String}
    {e b : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d types locals
      (.letValue (.array [.bind x0, .bind x1, .bind x2, .bind x3,
                          .bind x4, .bind x5, .bind x6, .bind x7]) e b) h r h') :
    ∃ v0 v1 v2 v3 v4 v5 v6 v7 hm,
      EvalExprN world d types locals e h (.tuple [v0, v1, v2, v3, v4, v5, v6, v7]) hm ∧
      EvalExprN world d types
        ([(x0, v0), (x1, v1), (x2, v2), (x3, v3),
          (x4, v4), (x5, v5), (x6, v6), (x7, v7)] ++ locals) b hm r h' := by
  cases ev with
  | letValue hv hm hb =>
    rename_i inp _ bindings
    cases inp with
    | tuple vs =>
      rcases vs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, _ | ⟨v5, _ | ⟨v6, _ | ⟨v7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
        simp [World.matchPattern, matchPatternWith, matchListWith] at hm
      subst hm
      exact ⟨v0, v1, v2, v3, v4, v5, v6, v7, _, hv, hb⟩
    | field _ | ptr _ _ | construct _ _ _ => simp [World.matchPattern, matchPatternWith] at hm

private theorem evalExprN_call1_inv {world : World F} {d : Nat} {locals : Environment F Nat}
    {name : String} {e0 : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d [] locals (.call name (some []) [e0]) h r h') :
    ∃ d' v0 hm, d' < d ∧
      EvalExprN world d [] locals e0 h v0 hm ∧
      EvalFnN world d' name [v0] hm r h' := by
  obtain ⟨d', vs, hm, hlt, hargs, hcal⟩ := evalExprN_call_inv ev
  cases hargs with | cons h0 t0 =>
  cases t0
  exact ⟨d', _, hm, hlt, h0, hcal⟩

private theorem evalExprN_call2_inv {world : World F} {d : Nat} {locals : Environment F Nat}
    {name : String} {e0 e1 : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d [] locals (.call name (some []) [e0, e1]) h r h') :
    ∃ d' v0 v1 h1 hm, d' < d ∧
      EvalExprN world d [] locals e0 h v0 h1 ∧
      EvalExprN world d [] locals e1 h1 v1 hm ∧
      EvalFnN world d' name [v0, v1] hm r h' := by
  obtain ⟨d', vs, hm, hlt, hargs, hcal⟩ := evalExprN_call_inv ev
  cases hargs with | cons h0 t0 =>
  cases t0 with | cons h1 t1 =>
  cases t1
  exact ⟨d', _, _, _, hm, hlt, h0, h1, hcal⟩

private theorem evalExprN_call3_inv {world : World F} {d : Nat} {locals : Environment F Nat}
    {name : String} {e0 e1 e2 : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d [] locals (.call name (some []) [e0, e1, e2]) h r h') :
    ∃ d' v0 v1 v2 h1 h2 hm, d' < d ∧
      EvalExprN world d [] locals e0 h v0 h1 ∧
      EvalExprN world d [] locals e1 h1 v1 h2 ∧
      EvalExprN world d [] locals e2 h2 v2 hm ∧
      EvalFnN world d' name [v0, v1, v2] hm r h' := by
  obtain ⟨d', vs, hm, hlt, hargs, hcal⟩ := evalExprN_call_inv ev
  cases hargs with | cons h0 t0 =>
  cases t0 with | cons h1 t1 =>
  cases t1 with | cons h2 t2 =>
  cases t2
  exact ⟨d', _, _, _, _, _, hm, hlt, h0, h1, h2, hcal⟩

private theorem ty_subst_nil_field : Generic.Ty.field.subst [] = .field := by
  simp

private theorem ty_subst_nil_arr4 : (Generic.Ty.array .field 4).subst [] = .array .field 4 := by
  simp

private theorem evalExprN_store_listNil_inv {world : World F} {d : Nat}
    {locals : Environment F Nat} {elemTy : Generic.Ty} (hsub : elemTy.subst [] = elemTy)
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d [] locals
      (.store (.construct "Lists::Node" (some [elemTy]) "Nil" [])) h r h') :
    let en := (Aiur.Generic.Instance.mk "Lists::Node" [elemTy]).symbol
    r = .ptr (.enum en) h.length ∧ h' = h ++ [.construct en "Nil" []] := by
  obtain ⟨v, hm, evc, rfl, rfl⟩ := evalExprN_store_inv ev
  cases evc with
  | construct hargs =>
    cases hargs
    simp [instanceName, hsub]

private theorem evalExprN_store_listCons_inv {world : World F} {d : Nat}
    {locals : Environment F Nat} {elemTy : Generic.Ty}
    {ehd etl : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (hsub : elemTy.subst [] = elemTy)
    (ev : EvalExprN world d [] locals
      (.store (.construct "Lists::Node" (some [elemTy]) "Cons" [ehd, etl])) h r h') :
    let en := (Aiur.Generic.Instance.mk "Lists::Node" [elemTy]).symbol
    ∃ vhd vtl h1 hm,
      EvalExprN world d [] locals ehd h vhd h1 ∧
      EvalExprN world d [] locals etl h1 vtl hm ∧
      r = .ptr (.enum en) hm.length ∧
      h' = hm ++ [.construct en "Cons" [vhd, vtl]] := by
  obtain ⟨v, hm, evc, rfl, rfl⟩ := evalExprN_store_inv ev
  cases evc with
  | construct hargs =>
    cases hargs with | cons hhd t1 =>
    cases t1 with | cons htl t2 =>
    cases t2
    refine ⟨_, _, _, hm, hhd, htl, ?_, ?_⟩ <;> simp [instanceName, hsub]

private theorem evalExprN_tuple2_inv {world : World F} {d : Nat} {types : Types}
    {locals : Environment F Nat} {e0 e1 : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d types locals (.tuple [e0, e1]) h r h') :
    ∃ v0 v1 hm,
      EvalExprN world d types locals e0 h v0 hm ∧
      EvalExprN world d types locals e1 hm v1 h' ∧
      r = .tuple [v0, v1] := by
  cases ev with
  | tuple hargs =>
    cases hargs with | cons h0 t0 =>
    cases t0 with | cons h1 t1 =>
    cases t1
    exact ⟨_, _, _, h0, h1, rfl⟩

private theorem evalExprN_index_inv {world : World F} {d : Nat} {types : Types}
    {locals : Environment F Nat} {e : Aiur.Generic.Expr F} {idx : Nat}
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d types locals (.index e idx) h r h') :
    ∃ v, EvalExprN world d types locals e h v h' ∧ projectValue v idx = .ok r := by
  cases ev with | index hv hp => exact ⟨_, hv, hp⟩

omit [Field F] in
private theorem selectArm_lit_inv {world : World F} {types : Types} {h : Heap F}
    {v : SourceValue F} {c : F} {b : Aiur.Generic.Expr F}
    {rest : List (Aiur.Generic.Pattern F × Aiur.Generic.Expr F)}
    {bs : Environment F Nat} {body : Aiur.Generic.Expr F}
    (hsel : selectArm world types h v ((.literal c, b) :: rest) = .ok (some (bs, body))) :
    (bs = [] ∧ body = b) ∨ selectArm world types h v rest = .ok (some (bs, body)) := by
  rcases selectArm_cons_inv hsel with ⟨hm, rfl⟩ | ⟨_, hrest⟩
  · cases v with
    | field x =>
      simp only [World.matchPattern, matchPatternWith, Aiur.Pattern.bindings, pure, Except.pure] at hm
      split at hm
      · simp only [Except.ok.injEq, Option.some.injEq] at hm
        exact .inl ⟨hm.symm, rfl⟩
      · simp at hm
    | tuple _ | ptr _ _ | construct _ _ _ =>
      simp [World.matchPattern, matchPatternWith, Aiur.Pattern.bindings, pure, Except.pure] at hm
  · exact .inr hrest

omit [Field F] in
private theorem selectArm_wild_singleton_inv {world : World F} {types : Types} {h : Heap F}
    {v : SourceValue F} {b : Aiur.Generic.Expr F}
    {bs : Environment F Nat} {body : Aiur.Generic.Expr F}
    (hsel : selectArm world types h v [(.wildcard, b)] = .ok (some (bs, body))) :
    bs = [] ∧ body = b := by
  rcases selectArm_cons_inv hsel with ⟨hm, rfl⟩ | ⟨_, hrest⟩
  · simp only [World.matchPattern, matchPatternWith, pure, Except.pure,
      Except.ok.injEq, Option.some.injEq] at hm
    exact ⟨hm.symm, rfl⟩
  · exact False.elim (selectArm_nil_inv hrest)

/-! ### `StarkIO::read_byte_stream` & `StarkIO::read_channel` Soundness -/

private theorem heap_extends_snoc_right {F : Type} {h₁ h₂ : Heap F} (v : SourceValue F)
    (h : Heap.Extends h₁ h₂) : Heap.Extends h₁ (h₂ ++ [v]) :=
  h.trans (Heap.Extends.snoc h₂ v)

private theorem starkIo_read1Arm_sound
    {world : World F} {d : Nat} (hsio : StarkIOWorld world)
    (ih : ∀ d' < d, ∀ ch' idx' len' h0 r0 h1,
      EvalFnN world d' "StarkIO::read_byte_stream" [ch', idx', len'] h0 r0 h1 →
      Heap.Extends h0 h1 ∧ ∃ bs : List UInt8, ByteStreamRel h1 bs r0)
    {locals : Environment F Nat} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d [] locals
      ((starkIoRead1Arm "StarkIO::read_byte_stream" .field).map (Nat.cast : Nat → F)) h r h') :
    Heap.Extends h h' ∧ ∃ bs : List UInt8, ByteStreamRel h' bs r := by
  simp only [starkIoRead1Arm, letE, callE, vE, litE, addE, subE, listConsE,
    Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at ev
  obtain ⟨vByte, h1, evHint, evLetTail⟩ := evalExprN_let_array1_inv ev
  have ext01 : Heap.Extends h h1 := evHint.heap_extends
  obtain ⟨vTail, h2, evRecCall, evCons⟩ := evalExprN_let_bind_inv evLetTail
  obtain ⟨d', vc, vi, vl, h1a, h1b, h1c, hlt, ec, ei, el, evRec⟩ := evalExprN_call3_inv evRecCall
  have ext1c : Heap.Extends h1 h1c :=
    ec.heap_extends.trans (ei.heap_extends.trans el.heap_extends)
  obtain ⟨extTail, tailBs, hTailRel⟩ := ih d' hlt vc vi vl h1c vTail h2 evRec
  obtain ⟨vHd, vTl, h3, h4, evFromField, evTlVar, rfl, rfl⟩ :=
    evalExprN_store_listCons_inv ty_subst_nil_field evCons
  obtain ⟨d1, vb1, h2a, _, evBVar, evFF⟩ := evalExprN_call1_inv evFromField
  obtain ⟨_, rfl⟩ := evalExprN_var_inv evBVar
  obtain ⟨rfl, rfl, b, hbLt, rfl⟩ := hsio.bytes.u8_from_field _ _ _ _ evFF.toEvalFn
  obtain ⟨hlTl, rfl⟩ := evalExprN_var_inv evTlVar
  simp at hlTl
  subst hlTl
  have hRel := ByteStreamRel.allocCons (b := UInt8.ofNat b) hTailRel
  exact ⟨heap_extends_snoc_right _ (ext01.trans (ext1c.trans extTail)),
    UInt8.ofNat b :: tailBs, by simpa [byteStreamEnum, bv_ofNat hbLt] using hRel⟩

private theorem starkIo_read8Arm_sound
    {world : World F} {d : Nat} (hsio : StarkIOWorld world)
    (ih : ∀ d' < d, ∀ ch' idx' len' h0 r0 h1,
      EvalFnN world d' "StarkIO::read_byte_stream" [ch', idx', len'] h0 r0 h1 →
      Heap.Extends h0 h1 ∧ ∃ bs : List UInt8, ByteStreamRel h1 bs r0)
    {locals : Environment F Nat} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d [] locals
      ((starkIoRead8Arm "StarkIO::read_byte_stream" .field).map (Nat.cast : Nat → F)) h r h') :
    Heap.Extends h h' ∧ ∃ bs : List UInt8, ByteStreamRel h' bs r := by
  simp only [starkIoRead8Arm, letE, callE, vE, litE, addE, subE, listConsE,
    Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at ev
  obtain ⟨vb0, vb1, vb2, vb3, vb4, vb5, vb6, vb7, h1, evHint, ev01⟩ := evalExprN_let_array8_inv ev
  have ext01 : Heap.Extends h h1 := evHint.heap_extends
  -- Check pair (b0, b1) -> (c0, c1)
  obtain ⟨vc0, vc1, h2, evFF01, ev23⟩ := evalExprN_let_tuple2_inv ev01
  obtain ⟨_, _, _, _, _, _, e0, e1, hcal01⟩ := evalExprN_call2_inv evFF01
  obtain ⟨_, rfl⟩ := evalExprN_var_inv e0; obtain ⟨_, rfl⟩ := evalExprN_var_inv e1
  obtain ⟨ht01, rfl, a0, a1, ha0, ha1, rfl, rfl⟩ := hsio.bytes.u8_from_fields _ _ _ _ _ hcal01.toEvalFn
  injection ht01 with hc01; injection hc01 with hEqc0 hc01'; injection hc01' with hEqc1 _
  subst hEqc0 hEqc1
  -- Check pair (b2, b3) -> (c2, c3)
  obtain ⟨vc2, vc3, h3, evFF23, ev45⟩ := evalExprN_let_tuple2_inv ev23
  obtain ⟨_, _, _, _, _, _, e2, e3, hcal23⟩ := evalExprN_call2_inv evFF23
  obtain ⟨_, rfl⟩ := evalExprN_var_inv e2; obtain ⟨_, rfl⟩ := evalExprN_var_inv e3
  obtain ⟨ht23, rfl, a2, a3, ha2, ha3, rfl, rfl⟩ := hsio.bytes.u8_from_fields _ _ _ _ _ hcal23.toEvalFn
  injection ht23 with hc23; injection hc23 with hEqc2 hc23'; injection hc23' with hEqc3 _
  subst hEqc2 hEqc3
  -- Check pair (b4, b5) -> (c4, c5)
  obtain ⟨vc4, vc5, h4, evFF45, ev67⟩ := evalExprN_let_tuple2_inv ev45
  obtain ⟨_, _, _, _, _, _, e4, e5, hcal45⟩ := evalExprN_call2_inv evFF45
  obtain ⟨_, rfl⟩ := evalExprN_var_inv e4; obtain ⟨_, rfl⟩ := evalExprN_var_inv e5
  obtain ⟨ht45, rfl, a4, a5, ha4, ha5, rfl, rfl⟩ := hsio.bytes.u8_from_fields _ _ _ _ _ hcal45.toEvalFn
  injection ht45 with hc45; injection hc45 with hEqc4 hc45'; injection hc45' with hEqc5 _
  subst hEqc4 hEqc5
  -- Check pair (b6, b7) -> (c6, c7)
  obtain ⟨vc6, vc7, h5, evFF67, evTailLet⟩ := evalExprN_let_tuple2_inv ev67
  obtain ⟨_, _, _, _, _, _, e6, e7, hcal67⟩ := evalExprN_call2_inv evFF67
  obtain ⟨_, rfl⟩ := evalExprN_var_inv e6; obtain ⟨_, rfl⟩ := evalExprN_var_inv e7
  obtain ⟨ht67, rfl, a6, a7, ha6, ha7, rfl, rfl⟩ := hsio.bytes.u8_from_fields _ _ _ _ _ hcal67.toEvalFn
  injection ht67 with hc67; injection hc67 with hEqc6 hc67'; injection hc67' with hEqc7 _
  subst hEqc6 hEqc7
  -- Recursive tail call
  obtain ⟨vTail, h6, evRecCall, evCons0⟩ := evalExprN_let_bind_inv evTailLet
  obtain ⟨d', vc, vi, vl, _, _, h5c, hlt, ec, ei, el, evRec⟩ := evalExprN_call3_inv evRecCall
  have ext5c : Heap.Extends _ h5c :=
    ec.heap_extends.trans (ei.heap_extends.trans el.heap_extends)
  obtain ⟨extTail, tailBs, hTailRel⟩ := ih d' hlt vc vi vl h5c vTail h6 evRec
  -- 8 nested `Cons` heap stores
  obtain ⟨v0, vt0, _, _, evc0, evCons1, rfl, rfl⟩ := evalExprN_store_listCons_inv ty_subst_nil_field evCons0
  obtain ⟨hlc0, rfl⟩ := evalExprN_var_inv evc0; simp at hlc0; subst hlc0
  obtain ⟨v1, vt1, _, _, evc1, evCons2, rfl, rfl⟩ := evalExprN_store_listCons_inv ty_subst_nil_field evCons1
  obtain ⟨hlc1, rfl⟩ := evalExprN_var_inv evc1; simp at hlc1; subst hlc1
  obtain ⟨v2, vt2, _, _, evc2, evCons3, rfl, rfl⟩ := evalExprN_store_listCons_inv ty_subst_nil_field evCons2
  obtain ⟨hlc2, rfl⟩ := evalExprN_var_inv evc2; simp at hlc2; subst hlc2
  obtain ⟨v3, vt3, _, _, evc3, evCons4, rfl, rfl⟩ := evalExprN_store_listCons_inv ty_subst_nil_field evCons3
  obtain ⟨hlc3, rfl⟩ := evalExprN_var_inv evc3; simp at hlc3; subst hlc3
  obtain ⟨v4, vt4, _, _, evc4, evCons5, rfl, rfl⟩ := evalExprN_store_listCons_inv ty_subst_nil_field evCons4
  obtain ⟨hlc4, rfl⟩ := evalExprN_var_inv evc4; simp at hlc4; subst hlc4
  obtain ⟨v5, vt5, _, _, evc5, evCons6, rfl, rfl⟩ := evalExprN_store_listCons_inv ty_subst_nil_field evCons5
  obtain ⟨hlc5, rfl⟩ := evalExprN_var_inv evc5; simp at hlc5; subst hlc5
  obtain ⟨v6, vt6, _, _, evc6, evCons7, rfl, rfl⟩ := evalExprN_store_listCons_inv ty_subst_nil_field evCons6
  obtain ⟨hlc6, rfl⟩ := evalExprN_var_inv evc6; simp at hlc6; subst hlc6
  obtain ⟨v7, vt7, _, _, evc7, evTlVar, rfl, rfl⟩ := evalExprN_store_listCons_inv ty_subst_nil_field evCons7
  obtain ⟨hlc7, rfl⟩ := evalExprN_var_inv evc7; simp at hlc7; subst hlc7
  obtain ⟨hlTl, rfl⟩ := evalExprN_var_inv evTlVar; simp at hlTl; subst hlTl
  have hRel7 := ByteStreamRel.allocCons (b := UInt8.ofNat a7) hTailRel
  have hRel6 := ByteStreamRel.allocCons (b := UInt8.ofNat a6) hRel7
  have hRel5 := ByteStreamRel.allocCons (b := UInt8.ofNat a5) hRel6
  have hRel4 := ByteStreamRel.allocCons (b := UInt8.ofNat a4) hRel5
  have hRel3 := ByteStreamRel.allocCons (b := UInt8.ofNat a3) hRel4
  have hRel2 := ByteStreamRel.allocCons (b := UInt8.ofNat a2) hRel3
  have hRel1 := ByteStreamRel.allocCons (b := UInt8.ofNat a1) hRel2
  have hRel0 := ByteStreamRel.allocCons (b := UInt8.ofNat a0) hRel1
  exact ⟨heap_extends_snoc_right _ (heap_extends_snoc_right _ (heap_extends_snoc_right _
      (heap_extends_snoc_right _ (heap_extends_snoc_right _ (heap_extends_snoc_right _
        (heap_extends_snoc_right _ (heap_extends_snoc_right _
          (ext01.trans (ext5c.trans extTail))))))))), _, by
    simpa [byteStreamEnum, bv_ofNat ha0, bv_ofNat ha1, bv_ofNat ha2, bv_ofNat ha3,
           bv_ofNat ha4, bv_ofNat ha5, bv_ofNat ha6, bv_ofNat ha7] using hRel0⟩

private theorem starkIo_read_byte_stream_sound_N
    {world : World F} (hsio : StarkIOWorld world) :
    ∀ (d : Nat) (ch idx len : SourceValue F) (h r h'),
      EvalFnN world d "StarkIO::read_byte_stream" [ch, idx, len] h r h' →
      Heap.Extends h h' ∧ ∃ bs : List UInt8, ByteStreamRel h' bs r := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro ch idx len h r h' ev
    obtain ⟨_, body⟩ := evalFnN_plain_inv hsio.read_byte_stream isPlainExpr_starkIoReadStreamBodyF ev
    simp only [starkIoReadStreamBodyF, starkIoReadStreamBody, matchE, vE,
      Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at body
    obtain ⟨vlen, hm, _, _, evLen, hsel, evArm⟩ := evalExprN_match_inv body
    obtain ⟨_, rfl⟩ := evalExprN_var_inv evLen
    -- Arm 0: Nil
    rcases selectArm_lit_inv hsel with ⟨rfl, rfl⟩ | hsel1
    · simp only [listNilE, Aiur.Generic.Expr.map, List.map] at evArm
      obtain ⟨rfl, rfl⟩ := evalExprN_store_listNil_inv ty_subst_nil_field evArm
      exact ⟨Heap.Extends.snoc _ _, [], ByteStreamRel.allocNil _⟩
    -- Arms 1..7: read1
    rcases selectArm_lit_inv hsel1 with ⟨rfl, rfl⟩ | hsel2
    · exact starkIo_read1Arm_sound hsio ih (by simpa using evArm)
    rcases selectArm_lit_inv hsel2 with ⟨rfl, rfl⟩ | hsel3
    · exact starkIo_read1Arm_sound hsio ih (by simpa using evArm)
    rcases selectArm_lit_inv hsel3 with ⟨rfl, rfl⟩ | hsel4
    · exact starkIo_read1Arm_sound hsio ih (by simpa using evArm)
    rcases selectArm_lit_inv hsel4 with ⟨rfl, rfl⟩ | hsel5
    · exact starkIo_read1Arm_sound hsio ih (by simpa using evArm)
    rcases selectArm_lit_inv hsel5 with ⟨rfl, rfl⟩ | hsel6
    · exact starkIo_read1Arm_sound hsio ih (by simpa using evArm)
    rcases selectArm_lit_inv hsel6 with ⟨rfl, rfl⟩ | hsel7
    · exact starkIo_read1Arm_sound hsio ih (by simpa using evArm)
    rcases selectArm_lit_inv hsel7 with ⟨rfl, rfl⟩ | hselW
    · exact starkIo_read1Arm_sound hsio ih (by simpa using evArm)
    -- Wildcard arm: read8
    obtain ⟨rfl, rfl⟩ := selectArm_wild_singleton_inv hselW
    exact starkIo_read8Arm_sound hsio ih (by simpa using evArm)

/-- **Certified soundness of `StarkIO::read_byte_stream`**: regardless of untrusted hint answers,
any successful derivation extends the heap and produces a finite `List UInt8` satisfying
`ByteStreamRel` and `isValidByteList`. -/
theorem starkIo_read_byte_stream_sound
    {world : World F} (hsio : StarkIOWorld world)
    {ch idx len r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "StarkIO::read_byte_stream" [ch, idx, len] h r h') :
    Heap.Extends h h' ∧
    ∃ bs : List UInt8, ByteStreamRel h' bs r ∧ isValidByteList (bs.map UInt8.toNat) := by
  obtain ⟨d, evN⟩ := EvalFnN.ofEvalFn ev
  obtain ⟨ext, bs, hrel⟩ := starkIo_read_byte_stream_sound_N hsio d ch idx len h r h' evN
  exact ⟨ext, bs, hrel, isValidByteList_ofUInt8List bs⟩

/-- **Certified soundness of `StarkIO::read_channel`**: regardless of untrusted `"stark.io.info"`,
`"stark.io.read1"`, and `"stark.io.read8"` advice, any derivation extends the heap and yields
a valid finite `List UInt8` byte stream. -/
theorem starkIo_read_channel_sound
    {world : World F} (hsio : StarkIOWorld world)
    {ch r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "StarkIO::read_channel" [ch] h r h') :
    Heap.Extends h h' ∧
    ∃ bs : List UInt8, ByteStreamRel h' bs r ∧ isValidByteList (bs.map UInt8.toNat) := by
  obtain ⟨_, body⟩ := evalFn_plain_inv hsio.read_channel isPlainExpr_starkIoChannelBodyF ev
  simp only [starkIoChannelBodyF, callE, vE, litE,
    Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at body
  obtain ⟨vIdx, vLen, h1, evHint, evCall⟩ := evalExpr_let_tuple2_inv body
  generalize hrH : (Value.tuple [vIdx, vLen] : SourceValue F) = rh at evHint
  cases evHint with
  | hint evKey _ =>
    obtain ⟨vch, v0, hm, evCh, evLit0, _⟩ := evalExpr_tuple2_inv evKey
    obtain ⟨_, rfl⟩ := evalExpr_var_inv evCh
    obtain ⟨_, rfl⟩ := evalExpr_literal_inv evLit0
    obtain ⟨c0, c1, c2, _, _, _, e0, e1, e2, evRead⟩ := evalExpr_call3_inv evCall
    obtain ⟨_, rfl⟩ := evalExpr_var_inv e0
    obtain ⟨_, rfl⟩ := evalExpr_var_inv e1
    obtain ⟨_, rfl⟩ := evalExpr_var_inv e2
    exact starkIo_read_byte_stream_sound hsio evRead

/-! ### `KzgIO` Ingress Soundness (`read_words`, `read_byte`, `split4`, `sized_channel`, `read_stream`) -/

theorem kzgIo_read_byte_sound
    {world : World F} (hkio : KzgIOWorld world)
    {ch off r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "KzgIO::read_byte" [ch, off] h r h') :
    h' = h ∧ ∃ b : UInt8, r = bv b := by
  obtain ⟨_, body⟩ := evalFn_plain_inv hkio.read_byte isPlainExpr_kzgIoReadByteBodyF ev
  simp only [kzgIoReadByteBodyF, kzgIoReadByteFn, callE, vE,
    Aiur.Generic.Expr.map, List.map] at body
  obtain ⟨vHint, hm, evHint, evFF⟩ := evalExpr_call1_inv body
  cases evHint with
  | hint evKey _ =>
    obtain ⟨_, _, _, evC, evO, _⟩ := evalExpr_tuple2_inv evKey
    obtain ⟨_, rfl⟩ := evalExpr_var_inv evC
    obtain ⟨_, rfl⟩ := evalExpr_var_inv evO
    obtain ⟨rfl, rfl, b, hbLt, hbEq⟩ := hkio.words.u8_from_field _ _ _ _ evFF
    exact ⟨rfl, UInt8.ofNat b, by rw [hbEq, bv_ofNat hbLt]⟩

theorem kzgIo_split4_sound
    {world : World F} (hkio : KzgIOWorld world)
    {cnt r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "KzgIO::split4" [cnt] h r h') :
    h' = h ∧ ∃ (wVal : SourceValue F) (lead : Nat),
      lead < 4 ∧ r = .tuple [wVal, .field (lead : F)] := by
  obtain ⟨_, body⟩ := evalFn_plain_inv hkio.split4 isPlainExpr_kzgIoSplit4BodyF ev
  simp only [kzgIoSplit4BodyF, kzgIoSplit4Fn, letE, subE, matchE, vE, litE,
    Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at body
  obtain ⟨wVal, h1, evHint, evLeadLet⟩ := evalExpr_let_bind_inv body
  cases evHint with
  | hint evKey _ =>
    obtain ⟨_, _, _, evCnt, ev4, _⟩ := evalExpr_tuple2_inv evKey
    obtain ⟨_, rfl⟩ := evalExpr_var_inv evCnt
    obtain ⟨_, rfl⟩ := evalExpr_literal_inv ev4
    obtain ⟨lVal, h2, evLead, evMatch⟩ := evalExpr_let_bind_inv evLeadLet
    obtain ⟨_, _, _, evCnt2, evMul, _⟩ := evalExpr_binary_inv evLead
    obtain ⟨_, rfl⟩ := evalExpr_var_inv evCnt2
    obtain ⟨_, _, _, ev4', evW, _⟩ := evalExpr_binary_inv evMul
    obtain ⟨_, rfl⟩ := evalExpr_literal_inv ev4'
    obtain ⟨_, rfl⟩ := evalExpr_var_inv evW
    obtain ⟨_, _, bs, armBody, evLVar, hsel, evArm⟩ := evalExpr_match_inv evMatch
    obtain ⟨_, rfl⟩ := evalExpr_var_inv evLVar
    rcases selectArm_lit_inv hsel with ⟨rfl, rfl⟩ | hsel1
    · obtain ⟨v0, v1, _, ew, el, rfl⟩ := evalExpr_tuple2_inv evArm
      obtain ⟨_, rfl⟩ := evalExpr_var_inv ew; obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv el
      exact ⟨rfl, v0, 0, by omega, by simp⟩
    rcases selectArm_lit_inv hsel1 with ⟨rfl, rfl⟩ | hsel2
    · obtain ⟨v0, v1, _, ew, el, rfl⟩ := evalExpr_tuple2_inv evArm
      obtain ⟨_, rfl⟩ := evalExpr_var_inv ew; obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv el
      exact ⟨rfl, v0, 1, by omega, by simp⟩
    rcases selectArm_lit_inv hsel2 with ⟨rfl, rfl⟩ | hsel3
    · obtain ⟨v0, v1, _, ew, el, rfl⟩ := evalExpr_tuple2_inv evArm
      obtain ⟨_, rfl⟩ := evalExpr_var_inv ew; obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv el
      exact ⟨rfl, v0, 2, by omega, by simp⟩
    rcases selectArm_lit_inv hsel3 with ⟨rfl, rfl⟩ | hselNil
    · obtain ⟨v0, v1, _, ew, el, rfl⟩ := evalExpr_tuple2_inv evArm
      obtain ⟨_, rfl⟩ := evalExpr_var_inv ew; obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv el
      exact ⟨rfl, v0, 3, by omega, by simp⟩
    exact False.elim (selectArm_nil_inv hselNil)

private theorem kzgIo_read_words_sound_N
    {world : World F} (hkio : KzgIOWorld world) :
    ∀ (d : Nat) (ch rem off : SourceValue F) (h r h'),
      EvalFnN world d "KzgIO::read_words" [ch, rem, off] h r h' →
      Heap.Extends h h' ∧ ∃ ws : List UInt32, WordListRel h' ws r := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro ch rem off h r h' ev
    obtain ⟨_, body⟩ := evalFnN_plain_inv hkio.read_words isPlainExpr_kzgIoReadWordsBodyF ev
    simp only [kzgIoReadWordsBodyF, kzgReadWordsBody, matchE, vE,
      Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at body
    obtain ⟨_, _, _, _, evRem, hsel, evArm⟩ := evalExprN_match_inv body
    obtain ⟨_, rfl⟩ := evalExprN_var_inv evRem
    rcases selectArm_lit_inv hsel with ⟨rfl, rfl⟩ | hselW
    · simp only [listNilE, Aiur.Generic.Expr.map, List.map] at evArm
      obtain ⟨rfl, rfl⟩ := evalExprN_store_listNil_inv ty_subst_nil_arr4 evArm
      exact ⟨Heap.Extends.snoc _ _, [], WordListRel.allocNil _⟩
    · obtain ⟨rfl, rfl⟩ := selectArm_wild_singleton_inv hselW
      simp only [letE, callE, litE, addE, subE, listConsE,
        Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at evArm
      obtain ⟨vWord, h1, evWordCall, evCons⟩ := evalExprN_let_bind_inv evArm
      obtain ⟨_, vHint, h0a, _, evHint, evFF⟩ := evalExprN_call1_inv evWordCall
      have ext0a : Heap.Extends _ h0a := evHint.heap_extends
      obtain ⟨rfl, w, rfl⟩ := hkio.words.u32_from_fields _ _ _ _ evFF.toEvalFn
      obtain ⟨vhd, vtl, h2, h3, evWVar, evRecCall, rfl, rfl⟩ :=
        evalExprN_store_listCons_inv ty_subst_nil_arr4 evCons
      obtain ⟨hlW, rfl⟩ := evalExprN_var_inv evWVar
      simp at hlW; subst hlW
      obtain ⟨d', vc, vr, vo, _, _, h2c, hlt, ec, er, eo, evRec⟩ := evalExprN_call3_inv evRecCall
      have ext2c : Heap.Extends _ h2c :=
        ec.heap_extends.trans (er.heap_extends.trans eo.heap_extends)
      obtain ⟨extTail, ws, hWsRel⟩ := ih d' hlt vc vr vo h2c vtl h3 evRec
      have hExt : Heap.Extends _ (h3 ++ [.construct wordStreamEnum "Cons" [wv w, vtl]]) :=
        ext0a.trans (ext2c.trans (extTail.trans (Heap.Extends.snoc h3 _)))
      exact ⟨hExt, w :: ws, WordListRel.allocCons hWsRel⟩

/-- **Certified soundness of `KzgIO::read_words`**: any derivation extends the heap and yields
a finite checked `List UInt32` word list. -/
theorem kzgIo_read_words_sound
    {world : World F} (hkio : KzgIOWorld world)
    {ch rem off r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "KzgIO::read_words" [ch, rem, off] h r h') :
    Heap.Extends h h' ∧ ∃ ws : List UInt32, WordListRel h' ws r := by
  obtain ⟨d, evN⟩ := EvalFnN.ofEvalFn ev
  exact kzgIo_read_words_sound_N hkio d ch rem off h r h' evN

private theorem evalExpr_array4_inv {world : World F} {types : Types}
    {locals : Environment F Nat} {e0 e1 e2 e3 : Aiur.Generic.Expr F}
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (.array [e0, e1, e2, e3]) h r h') :
    ∃ v0 v1 v2 v3 h1 h2 h3,
      EvalExpr world types locals e0 h v0 h1 ∧
      EvalExpr world types locals e1 h1 v1 h2 ∧
      EvalExpr world types locals e2 h2 v2 h3 ∧
      EvalExpr world types locals e3 h3 v3 h' ∧
      r = .tuple [v0, v1, v2, v3] := by
  cases ev with
  | array hargs =>
    cases hargs with | cons h0 t0 =>
    cases t0 with | cons h1 t1 =>
    cases t1 with | cons h2 t2 =>
    cases t2 with | cons h3 t3 =>
    cases t3
    exact ⟨_, _, _, _, _, _, _, h0, h1, h2, h3, rfl⟩

/-- **Certified soundness of `KzgIO::sized_channel`**: regardless of untrusted `"kzg.io.length"`,
`"kzg.io.div"`, `"kzg.io.read1"`, and `"kzg.io.read4"` advice, any derivation extends the heap
and yields a valid finite `List UInt8` byte stream satisfying `KzgInputRel` and `isValidByteList`. -/
theorem kzgIo_sized_channel_sound
    {world : World F} (hkio : KzgIOWorld world)
    {ch r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "KzgIO::sized_channel" [ch] h r h') :
    Heap.Extends h h' ∧
    ∃ (bs : List UInt8) (inp lenVal : SourceValue F),
      r = .tuple [inp, lenVal] ∧ KzgInputRel h' bs inp ∧ isValidByteList (bs.map UInt8.toNat) := by
  obtain ⟨_, body⟩ := evalFn_plain_inv hkio.sized_channel isPlainExpr_kzgIoSizedChannelBodyF ev
  simp only [kzgIoSizedChannelBodyF, kzgSizedChannelBody, letE, seqE, matchE, callE, vE, litE,
    listConsE, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map, Nat.cast_zero] at body
  obtain ⟨lenVal, h1, evLenHint, evSeq⟩ := evalExpr_let_bind_inv body
  have ext01 : Heap.Extends h h1 := by
    cases evLenHint with | hint evCh _ =>
    obtain ⟨_, rfl⟩ := evalExpr_var_inv evCh; exact Heap.Extends.refl _
  obtain ⟨_, h2, evAssert, evSplitLet⟩ := evalExpr_let_wildcard_inv evSeq
  have ext12 : Heap.Extends h1 h2 := by
    obtain ⟨dA, evAN⟩ := Backward.EvalExprN.ofEvalExpr evAssert
    exact evAN.heap_extends
  obtain ⟨wVal, lVal, h3, evSplitCall, evZeroLet⟩ := evalExpr_let_tuple2_inv evSplitLet
  obtain ⟨_, _, evLV, evSplitFn⟩ := evalExpr_call1_inv evSplitCall
  obtain ⟨_, rfl⟩ := evalExpr_var_inv evLV
  obtain ⟨rfl, wVal', lead, _, hSplitEq⟩ := kzgIo_split4_sound hkio evSplitFn
  injection hSplitEq with hsc; injection hsc with hwEq hsc'; injection hsc' with hlEq _
  subst hwEq hlEq
  obtain ⟨zVal, h4, evZeroCall, evInpLet⟩ := evalExpr_let_bind_inv evZeroLet
  obtain ⟨_, _, evZ0, evZFF⟩ := evalExpr_call1_inv evZeroCall
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evZ0
  obtain ⟨rfl, rfl, bz, hbzLt, hbzEq⟩ := hkio.words.u8_from_field _ _ _ _ evZFF
  have hzBv : (.field (0 : F) : SourceValue F) = bv (UInt8.ofNat bz) := by
    rw [bv_ofNat hbzLt, ← hbzEq]
  obtain ⟨inpVal, h5, evInpMatch, evRet⟩ := evalExpr_let_bind_inv evInpLet
  obtain ⟨v0, v1, _, evIR, evLR, rfl⟩ := evalExpr_tuple2_inv evRet
  obtain ⟨hlIR, rfl⟩ := evalExpr_var_inv evIR; simp at hlIR; subst hlIR
  obtain ⟨hlLR, rfl⟩ := evalExpr_var_inv evLR; simp at hlLR; subst hlLR
  obtain ⟨_, _, _, _, evLeadVar, hsel, evArm⟩ := evalExpr_match_inv evInpMatch
  obtain ⟨_, rfl⟩ := evalExpr_var_inv evLeadVar
  -- Case split on the 4 arms `0 | 1 | 2 | 3`
  rcases selectArm_lit_inv hsel with ⟨rfl, rfl⟩ | hsel1
  · -- lead = 0
    obtain ⟨vp, voff, _, evRW, evLit0, rfl⟩ := evalExpr_tuple2_inv evArm
    obtain ⟨_, _, _, _, _, _, ec, ew, e0, evRWFn⟩ := evalExpr_call3_inv evRW
    obtain ⟨_, rfl⟩ := evalExpr_var_inv ec; obtain ⟨_, rfl⟩ := evalExpr_var_inv ew
    obtain ⟨_, rfl⟩ := evalExpr_literal_inv e0
    obtain ⟨extRW, ws, hWs⟩ := kzgIo_read_words_sound hkio evRWFn
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evLit0
    refine ⟨ext01.trans (ext12.trans extRW), wordsToBytes ws, _, lenVal, rfl,
      ⟨ws, 0, vp, by omega, by simp, hWs, by simp⟩, isValidByteList_ofUInt8List _⟩
  rcases selectArm_lit_inv hsel1 with ⟨rfl, rfl⟩ | hsel2
  · -- lead = 1
    obtain ⟨vp, voff, _, evCons, evLit3, rfl⟩ := evalExpr_tuple2_inv evArm
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evLit3
    obtain ⟨vNode, h5a, evCtor, rfl, rfl⟩ := evalExpr_store_inv evCons
    cases evCtor with
    | construct hargs =>
      cases hargs with | cons evW t1 =>
      cases t1 with | cons evRW t2 =>
      cases t2
      obtain ⟨vArr, _, evArr, evFB⟩ := evalExpr_call1_inv evW
      obtain ⟨a0, a1, a2, a3, _, _, _, e0, e1, e2, e3, rfl⟩ := evalExpr_array4_inv evArr
      obtain ⟨hl0, rfl⟩ := evalExpr_var_inv e0; simp at hl0; subst hl0
      obtain ⟨hl1, rfl⟩ := evalExpr_var_inv e1; simp at hl1; subst hl1
      obtain ⟨hl2, rfl⟩ := evalExpr_var_inv e2; simp at hl2; subst hl2
      obtain ⟨_, _, _, _, ec0, el0, evRB0⟩ := evalExpr_call2_inv e3
      obtain ⟨_, rfl⟩ := evalExpr_var_inv ec0; obtain ⟨_, rfl⟩ := evalExpr_literal_inv el0
      obtain ⟨rfl, b0, rfl⟩ := kzgIo_read_byte_sound hkio evRB0
      obtain ⟨rfl, rfl⟩ := hkio.words.u32_from_bytes _ _ _ _ evFB
      obtain ⟨_, _, _, _, _, _, ec, ew, e1', evRWFn⟩ := evalExpr_call3_inv evRW
      obtain ⟨_, rfl⟩ := evalExpr_var_inv ec; obtain ⟨_, rfl⟩ := evalExpr_var_inv ew
      obtain ⟨_, rfl⟩ := evalExpr_literal_inv e1'
      obtain ⟨extRW, ws, hWs⟩ := kzgIo_read_words_sound hkio evRWFn
      let w0 := Aiur.Library.Blake3.wordOfBytes (UInt8.ofNat bz) (UInt8.ofNat bz) (UInt8.ofNat bz) b0
      have hw0 : (.tuple [.field (0 : F), .field (0 : F), .field (0 : F), bv b0] : SourceValue F) = wv w0 := by
        rw [hzBv, Blake3Spec.wv_wordOfBytes]; rfl
      have hRel := WordListRel.allocCons (w := w0) hWs
      exact ⟨ext01.trans (ext12.trans (extRW.trans (Heap.Extends.snoc _ _))),
        (wordsToBytes (w0 :: ws)).drop 3, _, lenVal, rfl,
        ⟨w0 :: ws, 3, _, by omega, rfl,
          by simpa [wordStreamEnum, instanceName, ty_subst_nil_arr4, Value.type, hw0] using hRel, rfl⟩,
        isValidByteList_ofUInt8List _⟩
  rcases selectArm_lit_inv hsel2 with ⟨rfl, rfl⟩ | hsel3
  · -- lead = 2
    obtain ⟨vp, voff, _, evCons, evLit2, rfl⟩ := evalExpr_tuple2_inv evArm
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evLit2
    obtain ⟨vNode, h5a, evCtor, rfl, rfl⟩ := evalExpr_store_inv evCons
    cases evCtor with
    | construct hargs =>
      cases hargs with | cons evW t1 =>
      cases t1 with | cons evRW t2 =>
      cases t2
      obtain ⟨vArr, _, evArr, evFB⟩ := evalExpr_call1_inv evW
      obtain ⟨a0, a1, a2, a3, _, _, _, e0, e1, e2, e3, rfl⟩ := evalExpr_array4_inv evArr
      obtain ⟨hl0, rfl⟩ := evalExpr_var_inv e0; simp at hl0; subst hl0
      obtain ⟨hl1, rfl⟩ := evalExpr_var_inv e1; simp at hl1; subst hl1
      obtain ⟨_, _, _, _, ec0, el0, evRB0⟩ := evalExpr_call2_inv e2
      obtain ⟨_, rfl⟩ := evalExpr_var_inv ec0; obtain ⟨_, rfl⟩ := evalExpr_literal_inv el0
      obtain ⟨rfl, b0, rfl⟩ := kzgIo_read_byte_sound hkio evRB0
      obtain ⟨_, _, _, _, ec1, el1, evRB1⟩ := evalExpr_call2_inv e3
      obtain ⟨_, rfl⟩ := evalExpr_var_inv ec1; obtain ⟨_, rfl⟩ := evalExpr_literal_inv el1
      obtain ⟨rfl, b1, rfl⟩ := kzgIo_read_byte_sound hkio evRB1
      obtain ⟨rfl, rfl⟩ := hkio.words.u32_from_bytes _ _ _ _ evFB
      obtain ⟨_, _, _, _, _, _, ec, ew, e2', evRWFn⟩ := evalExpr_call3_inv evRW
      obtain ⟨_, rfl⟩ := evalExpr_var_inv ec; obtain ⟨_, rfl⟩ := evalExpr_var_inv ew
      obtain ⟨_, rfl⟩ := evalExpr_literal_inv e2'
      obtain ⟨extRW, ws, hWs⟩ := kzgIo_read_words_sound hkio evRWFn
      let w0 := Aiur.Library.Blake3.wordOfBytes (UInt8.ofNat bz) (UInt8.ofNat bz) b0 b1
      have hw0 : (.tuple [.field (0 : F), .field (0 : F), bv b0, bv b1] : SourceValue F) = wv w0 := by
        rw [hzBv, Blake3Spec.wv_wordOfBytes]; rfl
      have hRel := WordListRel.allocCons (w := w0) hWs
      exact ⟨ext01.trans (ext12.trans (extRW.trans (Heap.Extends.snoc _ _))),
        (wordsToBytes (w0 :: ws)).drop 2, _, lenVal, rfl,
        ⟨w0 :: ws, 2, _, by omega, rfl,
          by simpa [wordStreamEnum, instanceName, ty_subst_nil_arr4, Value.type, hw0] using hRel, rfl⟩,
        isValidByteList_ofUInt8List _⟩
  rcases selectArm_lit_inv hsel3 with ⟨rfl, rfl⟩ | hselNil
  · -- lead = 3
    obtain ⟨vp, voff, _, evCons, evLit1, rfl⟩ := evalExpr_tuple2_inv evArm
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evLit1
    obtain ⟨vNode, h5a, evCtor, rfl, rfl⟩ := evalExpr_store_inv evCons
    cases evCtor with
    | construct hargs =>
      cases hargs with | cons evW t1 =>
      cases t1 with | cons evRW t2 =>
      cases t2
      obtain ⟨vArr, _, evArr, evFB⟩ := evalExpr_call1_inv evW
      obtain ⟨a0, a1, a2, a3, _, _, _, e0, e1, e2, e3, rfl⟩ := evalExpr_array4_inv evArr
      obtain ⟨hl0, rfl⟩ := evalExpr_var_inv e0; simp at hl0; subst hl0
      obtain ⟨_, _, _, _, ec0, el0, evRB0⟩ := evalExpr_call2_inv e1
      obtain ⟨_, rfl⟩ := evalExpr_var_inv ec0; obtain ⟨_, rfl⟩ := evalExpr_literal_inv el0
      obtain ⟨rfl, b0, rfl⟩ := kzgIo_read_byte_sound hkio evRB0
      obtain ⟨_, _, _, _, ec1, el1, evRB1⟩ := evalExpr_call2_inv e2
      obtain ⟨_, rfl⟩ := evalExpr_var_inv ec1; obtain ⟨_, rfl⟩ := evalExpr_literal_inv el1
      obtain ⟨rfl, b1, rfl⟩ := kzgIo_read_byte_sound hkio evRB1
      obtain ⟨_, _, _, _, ec2, el2, evRB2⟩ := evalExpr_call2_inv e3
      obtain ⟨_, rfl⟩ := evalExpr_var_inv ec2; obtain ⟨_, rfl⟩ := evalExpr_literal_inv el2
      obtain ⟨rfl, b2, rfl⟩ := kzgIo_read_byte_sound hkio evRB2
      obtain ⟨rfl, rfl⟩ := hkio.words.u32_from_bytes _ _ _ _ evFB
      obtain ⟨_, _, _, _, _, _, ec, ew, e3', evRWFn⟩ := evalExpr_call3_inv evRW
      obtain ⟨_, rfl⟩ := evalExpr_var_inv ec; obtain ⟨_, rfl⟩ := evalExpr_var_inv ew
      obtain ⟨_, rfl⟩ := evalExpr_literal_inv e3'
      obtain ⟨extRW, ws, hWs⟩ := kzgIo_read_words_sound hkio evRWFn
      let w0 := Aiur.Library.Blake3.wordOfBytes (UInt8.ofNat bz) b0 b1 b2
      have hw0 : (.tuple [.field (0 : F), bv b0, bv b1, bv b2] : SourceValue F) = wv w0 := by
        rw [hzBv, Blake3Spec.wv_wordOfBytes]; rfl
      have hRel := WordListRel.allocCons (w := w0) hWs
      exact ⟨ext01.trans (ext12.trans (extRW.trans (Heap.Extends.snoc _ _))),
        (wordsToBytes (w0 :: ws)).drop 1, _, lenVal, rfl,
        ⟨w0 :: ws, 1, _, by omega, rfl,
          by simpa [wordStreamEnum, instanceName, ty_subst_nil_arr4, Value.type, hw0] using hRel, rfl⟩,
        isValidByteList_ofUInt8List _⟩
  exact False.elim (selectArm_nil_inv hselNil)

private theorem kzgIo_read_words_stream_sound_N
    {world : World F} (hkio : KzgIOWorld world) :
    ∀ (d : Nat) (ch rem off : SourceValue F) (h r h'),
      EvalFnN world d "KzgIO::read_words_stream" [ch, rem, off] h r h' →
      Heap.Extends h h' ∧ ∃ bs : List UInt8, ByteStreamRel h' bs r := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro ch rem off h r h' ev
    obtain ⟨_, body⟩ := evalFnN_plain_inv hkio.read_words_stream isPlainExpr_kzgIoReadWordsStreamBodyF ev
    simp only [kzgIoReadWordsStreamBodyF, kzgReadWordsStreamBody, matchE, vE,
      Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at body
    obtain ⟨_, _, _, _, evRem, hsel, evArm⟩ := evalExprN_match_inv body
    obtain ⟨_, rfl⟩ := evalExprN_var_inv evRem
    rcases selectArm_lit_inv hsel with ⟨rfl, rfl⟩ | hselW
    · simp only [listNilE, Aiur.Generic.Expr.map, List.map] at evArm
      obtain ⟨rfl, rfl⟩ := evalExprN_store_listNil_inv ty_subst_nil_field evArm
      exact ⟨Heap.Extends.snoc _ _, [], ByteStreamRel.allocNil _⟩
    · obtain ⟨rfl, rfl⟩ := selectArm_wild_singleton_inv hselW
      simp only [letE, callE, litE, addE, subE, listConsE,
        Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at evArm
      obtain ⟨vWord, h1, evWordCall, evBsLet⟩ := evalExprN_let_bind_inv evArm
      obtain ⟨_, _, h0a, _, evHint, evFF⟩ := evalExprN_call1_inv evWordCall
      have ext0a : Heap.Extends _ h0a := evHint.heap_extends
      obtain ⟨rfl, w, rfl⟩ := hkio.words.u32_from_fields _ _ _ _ evFF.toEvalFn
      obtain ⟨vBs, h2, evToBytes, evTailLet⟩ := evalExprN_let_bind_inv evBsLet
      obtain ⟨_, _, _, _, evWVar, evTB⟩ := evalExprN_call1_inv evToBytes
      obtain ⟨hlW, rfl⟩ := evalExprN_var_inv evWVar; simp at hlW; subst hlW
      obtain ⟨rfl, rfl⟩ := hkio.words.u32_to_bytes _ _ _ _ evTB.toEvalFn
      obtain ⟨vTail, h3, evRecCall, evCons0⟩ := evalExprN_let_bind_inv evTailLet
      obtain ⟨d', vc, vr, vo, _, _, h2c, hlt, ec, er, eo, evRec⟩ := evalExprN_call3_inv evRecCall
      have ext2c : Heap.Extends _ h2c :=
        ec.heap_extends.trans (er.heap_extends.trans eo.heap_extends)
      obtain ⟨extTail, tailBs, hTailRel⟩ := ih d' hlt vc vr vo h2c vTail h3 evRec
      -- 4 nested `Cons` heap stores for the 4 bytes of `w`
      obtain ⟨v0, _, _, _, ei0, evCons1, rfl, rfl⟩ := evalExprN_store_listCons_inv ty_subst_nil_field evCons0
      obtain ⟨_, evBs0, hp0⟩ := evalExprN_index_inv ei0
      obtain ⟨hlBs0, rfl⟩ := evalExprN_var_inv evBs0; simp at hlBs0; subst hlBs0
      have hv0 : v0 = bv (Blake3.Pure.wordBytes w)[0] := by
        have hproj : projectValue (wv w : SourceValue F) 0 = .ok (bv (Blake3.Pure.wordBytes w)[0]) := rfl
        exact (Except.ok.inj (hp0.symm.trans hproj))
      subst hv0
      obtain ⟨v1, _, _, _, ei1, evCons2, rfl, rfl⟩ := evalExprN_store_listCons_inv ty_subst_nil_field evCons1
      obtain ⟨_, evBs1, hp1⟩ := evalExprN_index_inv ei1
      obtain ⟨hlBs1, rfl⟩ := evalExprN_var_inv evBs1; simp at hlBs1; subst hlBs1
      have hv1 : v1 = bv (Blake3.Pure.wordBytes w)[1] := by
        have hproj : projectValue (wv w : SourceValue F) 1 = .ok (bv (Blake3.Pure.wordBytes w)[1]) := rfl
        exact (Except.ok.inj (hp1.symm.trans hproj))
      subst hv1
      obtain ⟨v2, _, _, _, ei2, evCons3, rfl, rfl⟩ := evalExprN_store_listCons_inv ty_subst_nil_field evCons2
      obtain ⟨_, evBs2, hp2⟩ := evalExprN_index_inv ei2
      obtain ⟨hlBs2, rfl⟩ := evalExprN_var_inv evBs2; simp at hlBs2; subst hlBs2
      have hv2 : v2 = bv (Blake3.Pure.wordBytes w)[2] := by
        have hproj : projectValue (wv w : SourceValue F) 2 = .ok (bv (Blake3.Pure.wordBytes w)[2]) := rfl
        exact (Except.ok.inj (hp2.symm.trans hproj))
      subst hv2
      obtain ⟨v3, _, _, _, ei3, evTlVar, rfl, rfl⟩ := evalExprN_store_listCons_inv ty_subst_nil_field evCons3
      obtain ⟨_, evBs3, hp3⟩ := evalExprN_index_inv ei3
      obtain ⟨hlBs3, rfl⟩ := evalExprN_var_inv evBs3; simp at hlBs3; subst hlBs3
      have hv3 : v3 = bv (Blake3.Pure.wordBytes w)[3] := by
        have hproj : projectValue (wv w : SourceValue F) 3 = .ok (bv (Blake3.Pure.wordBytes w)[3]) := rfl
        exact (Except.ok.inj (hp3.symm.trans hproj))
      subst hv3
      obtain ⟨hlTl, rfl⟩ := evalExprN_var_inv evTlVar; simp at hlTl; subst hlTl
      have hRel3 := ByteStreamRel.allocCons (b := (Blake3.Pure.wordBytes w)[3]) hTailRel
      have hRel2 := ByteStreamRel.allocCons (b := (Blake3.Pure.wordBytes w)[2]) hRel3
      have hRel1 := ByteStreamRel.allocCons (b := (Blake3.Pure.wordBytes w)[1]) hRel2
      have hRel0 := ByteStreamRel.allocCons (b := (Blake3.Pure.wordBytes w)[0]) hRel1
      exact ⟨heap_extends_snoc_right _ (heap_extends_snoc_right _ (heap_extends_snoc_right _
          (heap_extends_snoc_right _ (ext0a.trans (ext2c.trans extTail))))), _,
        by simpa [byteStreamEnum] using hRel0⟩

/-- **Certified soundness of `KzgIO::read_stream`**: regardless of untrusted `"kzg.io.*"` advice,
any derivation extends the heap and yields a valid finite `List UInt8` `Bytes::Stream`. -/
theorem kzgIo_read_stream_sound
    {world : World F} (hkio : KzgIOWorld world)
    {ch r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "KzgIO::read_stream" [ch] h r h') :
    Heap.Extends h h' ∧
    ∃ bs : List UInt8, ByteStreamRel h' bs r ∧ isValidByteList (bs.map UInt8.toNat) := by
  obtain ⟨_, body⟩ := evalFn_plain_inv hkio.read_stream isPlainExpr_kzgIoReadStreamBodyF ev
  simp only [kzgIoReadStreamBodyF, kzgReadStreamBody, letE, seqE, matchE, callE, vE, litE,
    listConsE, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at body
  obtain ⟨lenVal, h1, evLenHint, evSeq⟩ := evalExpr_let_bind_inv body
  have ext01 : Heap.Extends h h1 := by
    cases evLenHint with | hint evCh _ =>
    obtain ⟨_, rfl⟩ := evalExpr_var_inv evCh; exact Heap.Extends.refl _
  obtain ⟨_, h2, evAssert, evSplitLet⟩ := evalExpr_let_wildcard_inv evSeq
  have ext12 : Heap.Extends h1 h2 := by
    obtain ⟨dA, evAN⟩ := Backward.EvalExprN.ofEvalExpr evAssert
    exact evAN.heap_extends
  obtain ⟨wVal, lVal, h3, evSplitCall, evMatch⟩ := evalExpr_let_tuple2_inv evSplitLet
  obtain ⟨_, _, evLV, evSplitFn⟩ := evalExpr_call1_inv evSplitCall
  obtain ⟨_, rfl⟩ := evalExpr_var_inv evLV
  obtain ⟨rfl, wVal', lead, _, hSplitEq⟩ := kzgIo_split4_sound hkio evSplitFn
  injection hSplitEq with hsc; injection hsc with hwEq hsc'; injection hsc' with hlEq _
  subst hwEq hlEq
  obtain ⟨_, _, _, _, evLeadVar, hsel, evArm⟩ := evalExpr_match_inv evMatch
  obtain ⟨_, rfl⟩ := evalExpr_var_inv evLeadVar
  rcases selectArm_lit_inv hsel with ⟨rfl, rfl⟩ | hsel1
  · obtain ⟨_, _, _, _, _, _, ec, ew, e0, evRWFn⟩ := evalExpr_call3_inv evArm
    obtain ⟨_, rfl⟩ := evalExpr_var_inv ec; obtain ⟨_, rfl⟩ := evalExpr_var_inv ew
    obtain ⟨_, rfl⟩ := evalExpr_literal_inv e0
    obtain ⟨dR, evRWN⟩ := EvalFnN.ofEvalFn evRWFn
    obtain ⟨extRW, bs, hRel⟩ := kzgIo_read_words_stream_sound_N hkio dR _ _ _ _ _ _ evRWN
    exact ⟨ext01.trans (ext12.trans extRW), bs, hRel, isValidByteList_ofUInt8List bs⟩
  rcases selectArm_lit_inv hsel1 with ⟨rfl, rfl⟩ | hsel2
  · obtain ⟨vb0, _, evB0, evTlLet⟩ := evalExpr_let_bind_inv evArm
    obtain ⟨_, _, _, _, ec0, el0, evRB0⟩ := evalExpr_call2_inv evB0
    obtain ⟨_, rfl⟩ := evalExpr_var_inv ec0; obtain ⟨_, rfl⟩ := evalExpr_literal_inv el0
    obtain ⟨rfl, b0, rfl⟩ := kzgIo_read_byte_sound hkio evRB0
    obtain ⟨vTl, _, evTlCall, evCons0⟩ := evalExpr_let_bind_inv evTlLet
    obtain ⟨_, _, _, _, _, _, ec, ew, e1, evRWFn⟩ := evalExpr_call3_inv evTlCall
    obtain ⟨_, rfl⟩ := evalExpr_var_inv ec; obtain ⟨_, rfl⟩ := evalExpr_var_inv ew
    obtain ⟨_, rfl⟩ := evalExpr_literal_inv e1
    obtain ⟨dR, evRWN⟩ := EvalFnN.ofEvalFn evRWFn
    obtain ⟨extRW, bs, hRel⟩ := kzgIo_read_words_stream_sound_N hkio dR _ _ _ _ _ _ evRWN
    obtain ⟨dC, evCN⟩ := Backward.EvalExprN.ofEvalExpr evCons0
    obtain ⟨_, _, _, _, evb0, evtl, rfl, rfl⟩ := evalExprN_store_listCons_inv ty_subst_nil_field evCN
    obtain ⟨hl0, rfl⟩ := evalExprN_var_inv evb0; simp at hl0; subst hl0
    obtain ⟨hlt, rfl⟩ := evalExprN_var_inv evtl; simp at hlt; subst hlt
    exact ⟨ext01.trans (ext12.trans (extRW.trans (Heap.Extends.snoc _ _))),
      b0 :: bs, ByteStreamRel.allocCons hRel, isValidByteList_ofUInt8List _⟩
  rcases selectArm_lit_inv hsel2 with ⟨rfl, rfl⟩ | hsel3
  · obtain ⟨vb0, _, evB0, evB1Let⟩ := evalExpr_let_bind_inv evArm
    obtain ⟨_, _, _, _, ec0, el0, evRB0⟩ := evalExpr_call2_inv evB0
    obtain ⟨_, rfl⟩ := evalExpr_var_inv ec0; obtain ⟨_, rfl⟩ := evalExpr_literal_inv el0
    obtain ⟨rfl, b0, rfl⟩ := kzgIo_read_byte_sound hkio evRB0
    obtain ⟨vb1, _, evB1, evTlLet⟩ := evalExpr_let_bind_inv evB1Let
    obtain ⟨_, _, _, _, ec1, el1, evRB1⟩ := evalExpr_call2_inv evB1
    obtain ⟨_, rfl⟩ := evalExpr_var_inv ec1; obtain ⟨_, rfl⟩ := evalExpr_literal_inv el1
    obtain ⟨rfl, b1, rfl⟩ := kzgIo_read_byte_sound hkio evRB1
    obtain ⟨vTl, _, evTlCall, evCons0⟩ := evalExpr_let_bind_inv evTlLet
    obtain ⟨_, _, _, _, _, _, ec, ew, e2, evRWFn⟩ := evalExpr_call3_inv evTlCall
    obtain ⟨_, rfl⟩ := evalExpr_var_inv ec; obtain ⟨_, rfl⟩ := evalExpr_var_inv ew
    obtain ⟨_, rfl⟩ := evalExpr_literal_inv e2
    obtain ⟨dR, evRWN⟩ := EvalFnN.ofEvalFn evRWFn
    obtain ⟨extRW, bs, hRel⟩ := kzgIo_read_words_stream_sound_N hkio dR _ _ _ _ _ _ evRWN
    obtain ⟨dC, evCN⟩ := Backward.EvalExprN.ofEvalExpr evCons0
    obtain ⟨_, _, _, _, evb0, evCons1, rfl, rfl⟩ := evalExprN_store_listCons_inv ty_subst_nil_field evCN
    obtain ⟨hl0, rfl⟩ := evalExprN_var_inv evb0; simp at hl0; subst hl0
    obtain ⟨_, _, _, _, evb1, evtl, rfl, rfl⟩ := evalExprN_store_listCons_inv ty_subst_nil_field evCons1
    obtain ⟨hl1, rfl⟩ := evalExprN_var_inv evb1; simp at hl1; subst hl1
    obtain ⟨hlt, rfl⟩ := evalExprN_var_inv evtl; simp at hlt; subst hlt
    exact ⟨ext01.trans (ext12.trans (extRW.trans ((Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _)))),
      b0 :: b1 :: bs, ByteStreamRel.allocCons (ByteStreamRel.allocCons hRel),
      isValidByteList_ofUInt8List _⟩
  rcases selectArm_lit_inv hsel3 with ⟨rfl, rfl⟩ | hselNil
  · obtain ⟨vb0, _, evB0, evB1Let⟩ := evalExpr_let_bind_inv evArm
    obtain ⟨_, _, _, _, ec0, el0, evRB0⟩ := evalExpr_call2_inv evB0
    obtain ⟨_, rfl⟩ := evalExpr_var_inv ec0; obtain ⟨_, rfl⟩ := evalExpr_literal_inv el0
    obtain ⟨rfl, b0, rfl⟩ := kzgIo_read_byte_sound hkio evRB0
    obtain ⟨vb1, _, evB1, evB2Let⟩ := evalExpr_let_bind_inv evB1Let
    obtain ⟨_, _, _, _, ec1, el1, evRB1⟩ := evalExpr_call2_inv evB1
    obtain ⟨_, rfl⟩ := evalExpr_var_inv ec1; obtain ⟨_, rfl⟩ := evalExpr_literal_inv el1
    obtain ⟨rfl, b1, rfl⟩ := kzgIo_read_byte_sound hkio evRB1
    obtain ⟨vb2, _, evB2, evTlLet⟩ := evalExpr_let_bind_inv evB2Let
    obtain ⟨_, _, _, _, ec2, el2, evRB2⟩ := evalExpr_call2_inv evB2
    obtain ⟨_, rfl⟩ := evalExpr_var_inv ec2; obtain ⟨_, rfl⟩ := evalExpr_literal_inv el2
    obtain ⟨rfl, b2, rfl⟩ := kzgIo_read_byte_sound hkio evRB2
    obtain ⟨vTl, _, evTlCall, evCons0⟩ := evalExpr_let_bind_inv evTlLet
    obtain ⟨_, _, _, _, _, _, ec, ew, e3, evRWFn⟩ := evalExpr_call3_inv evTlCall
    obtain ⟨_, rfl⟩ := evalExpr_var_inv ec; obtain ⟨_, rfl⟩ := evalExpr_var_inv ew
    obtain ⟨_, rfl⟩ := evalExpr_literal_inv e3
    obtain ⟨dR, evRWN⟩ := EvalFnN.ofEvalFn evRWFn
    obtain ⟨extRW, bs, hRel⟩ := kzgIo_read_words_stream_sound_N hkio dR _ _ _ _ _ _ evRWN
    obtain ⟨dC, evCN⟩ := Backward.EvalExprN.ofEvalExpr evCons0
    obtain ⟨_, _, _, _, evb0, evCons1, rfl, rfl⟩ := evalExprN_store_listCons_inv ty_subst_nil_field evCN
    obtain ⟨hl0, rfl⟩ := evalExprN_var_inv evb0; simp at hl0; subst hl0
    obtain ⟨_, _, _, _, evb1, evCons2, rfl, rfl⟩ := evalExprN_store_listCons_inv ty_subst_nil_field evCons1
    obtain ⟨hl1, rfl⟩ := evalExprN_var_inv evb1; simp at hl1; subst hl1
    obtain ⟨_, _, _, _, evb2, evtl, rfl, rfl⟩ := evalExprN_store_listCons_inv ty_subst_nil_field evCons2
    obtain ⟨hl2, rfl⟩ := evalExprN_var_inv evb2; simp at hl2; subst hl2
    obtain ⟨hlt, rfl⟩ := evalExprN_var_inv evtl; simp at hlt; subst hlt
    exact ⟨ext01.trans (ext12.trans (extRW.trans
        ((Heap.Extends.snoc _ _).trans ((Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _))))),
      b0 :: b1 :: b2 :: bs,
      ByteStreamRel.allocCons (ByteStreamRel.allocCons (ByteStreamRel.allocCons hRel)),
      isValidByteList_ofUInt8List _⟩
  exact False.elim (selectArm_nil_inv hselNil)

/-! ### Unified `WitnessChannelKind` & Existential NP Soundness Theorems -/

/-- Witness-stream channel protocol (`StarkIO` vs `KzgIO`). -/
inductive WitnessChannelKind where
  | stark
  | kzg
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Qualified `Bytes::Stream` reader function name for a `WitnessChannelKind`. -/
def WitnessChannelKind.readerFn : WitnessChannelKind → String
  | .stark => "StarkIO::read_channel"
  | .kzg => "KzgIO::read_stream"

theorem qualifyName_readerFn (k : WitnessChannelKind) :
    qualifyName k.readerFn = k.readerFn := by
  cases k <;> rfl

/-- **Unified Witness-Stream Existence Theorem (`witness_stream_exists`)**:
for ANY checked witness channel (`StarkIO::read_channel` or `KzgIO::read_stream`),
regardless of untrusted prover hint answers, any successful Formal Aiur derivation
extends the heap and produces a finite, checked `List UInt8` satisfying
`ByteStreamRel` and `isValidByteList`. -/
theorem witness_stream_exists
    {world : World F} (hsio : StarkIOWorld world) (hkio : KzgIOWorld world)
    (kind : WitnessChannelKind) {ch r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world kind.readerFn [ch] h r h') :
    Heap.Extends h h' ∧
    ∃ bs : List UInt8, ByteStreamRel h' bs r ∧ isValidByteList (bs.map UInt8.toNat) := by
  cases kind with
  | stark => exact starkIo_read_channel_sound hsio ev
  | kzg => exact kzgIo_read_stream_sound hkio ev

/-- Fresh local variable name for witness stream `i` inside `witnessWrapperBody`. -/
def witnessVarName (i : Nat) : String :=
  String.ofList ('_' :: 'w' :: Lower.natDigits i)

private def witnessLetChain (idx : Nat) : List (WitnessChannelKind × Nat) → Expr → Expr
  | [], body => body
  | (kind, chId) :: rest, body =>
    letE (witnessVarName idx) (callE kind.readerFn [litE chId])
      (witnessLetChain (idx + 1) rest body)

/-- Body of an NP witness-ingesting wrapper entrypoint: reads each `(kind, channelId)` stream
via its checked `StarkIO` / `KzgIO` reader, then calls `checkFnName(pubParams..., witnesses...)`,
optionally wrapping with `assert_eq!(result, 1)` when `assertOk = true`. -/
def witnessWrapperBody (pubParamNames : List String)
    (channels : List (WitnessChannelKind × Nat))
    (checkFnName : String) (assertOk : Bool := false) : Expr :=
  let wNames := (List.range channels.length).map witnessVarName
  let callInner := callE checkFnName ((pubParamNames ++ wNames).map vE)
  let tail :=
    if assertOk then
      letE "_w_ok" callInner <|
      seqE (.builtin (.assertEq (assertion "witness verifier rejected")) [vE "_w_ok", litE 1])
        (.tuple [])
    else
      callInner
  witnessLetChain 0 channels tail

/-- Construct a complete Formal Aiur `Lower.Fn` witness wrapper entrypoint. -/
def witnessWrapperFn (wrapperName : String) (pubParams : List (String × Lower.Ty))
    (channels : List (WitnessChannelKind × Nat))
    (checkFnName : String) (assertOk : Bool := false) : Fn :=
  { name := wrapperName
    params := pubParams
    result := if assertOk then .tuple [] else .field
    isInline := false
    body := witnessWrapperBody (pubParams.map Prod.fst) channels checkFnName assertOk }

private theorem isPlainList_map_vE (ns : List String) :
    isPlainList (ns.map vE) = true := by
  induction ns with
  | nil => rfl
  | cons a tl ih => simp [vE, isPlainList, isPlainExpr, ih]

private theorem isPlainExpr_witnessLetChain (idx : Nat) (chs : List (WitnessChannelKind × Nat))
    {body : Expr} (hb : isPlainExpr body = true) :
    isPlainExpr (witnessLetChain idx chs body) = true := by
  induction chs generalizing idx with
  | nil => exact hb
  | cons c rest ih =>
    rcases c with ⟨kind, chId⟩
    simp only [witnessLetChain, letE, callE, litE, isPlainExpr, isPlainList, Bool.and_true,
      Bool.true_and]
    exact ih (idx + 1)

/-- `witnessWrapperBody` is strictly plain (`Lower.isPlainExpr = true`). -/
theorem isPlainExpr_witnessWrapperBody (pubParamNames : List String)
    (channels : List (WitnessChannelKind × Nat)) (checkFnName : String) (assertOk : Bool) :
    isPlainExpr (witnessWrapperBody pubParamNames channels checkFnName assertOk) = true := by
  unfold witnessWrapperBody
  apply isPlainExpr_witnessLetChain
  cases assertOk
  · simp only [Bool.false_eq_true, ↓reduceIte, callE, isPlainExpr]
    exact isPlainList_map_vE _
  · simp only [↓reduceIte, letE, seqE, callE, vE, litE, isPlainExpr, isPlainList, Bool.and_true]
    exact isPlainList_map_vE _

private theorem evalArgs_vars_eq {world : World F} {locals : Environment F Nat} :
    ∀ {names : List String} {vals : List (SourceValue F)} {h h' : Heap F}
      {res : List (SourceValue F)}
      (hlen : names.length = vals.length),
      (∀ i (hi : i < names.length),
        locals.find? (·.1 == names[i]) = some (names[i], vals[i]'(by rw [← hlen]; exact hi))) →
      EvalArgs world [] locals (names.map (fun nm => .var nm)) h res h' →
      res = vals ∧ h' = h
  | [], [], _, _, _, _, _, ev => by cases ev; exact ⟨rfl, rfl⟩
  | _ :: _, [], _, _, _, hlen, _, _ => by simp at hlen
  | [], _ :: _, _, _, _, hlen, _, _ => by simp at hlen
  | n :: ns, v :: vs, h, h', res, hlen, hlook, ev => by
    cases ev with
    | cons evHd evTl =>
      obtain ⟨hln, rfl⟩ := evalExpr_var_inv evHd
      have h0 := hlook 0 (by simp)
      simp only [List.getElem_cons_zero] at h0
      rw [h0, Option.some.injEq, Prod.mk.injEq] at hln
      have hvEq : v = _ := hln.2
      subst hvEq
      have hlook' : ∀ i (hi : i < ns.length),
          locals.find? (·.1 == ns[i]) = some (ns[i], vs[i]'(by simp at hlen; omega)) := by
        intro i hi
        have := hlook (i + 1) (by simp; omega)
        simpa using this
      obtain ⟨rfl, rfl⟩ := evalArgs_vars_eq (by simp at hlen; omega) hlook' evTl
      exact ⟨rfl, rfl⟩

omit [Field F] [DecidableEq F] in
private theorem find?_zip_nodup {names : List String} {vals : List (SourceValue F)}
    (hnd : names.Nodup) (hlen : names.length = vals.length) :
    ∀ i (hi : i < names.length),
      (names.zip vals).find? (·.1 == names[i]) = some (names[i], vals[i]'(by omega)) := by
  induction names generalizing vals with
  | nil => intro i hi; simp at hi
  | cons a tl ih =>
    cases vals with
    | nil => simp at hlen
    | cons v vs =>
      simp only [List.nodup_cons] at hnd
      intro i hi
      cases i with
      | zero => simp
      | succ j =>
        have hne : (a == tl[j]'(by simp at hi; omega)) = false := by
          apply beq_false_of_ne
          intro heq
          apply hnd.1
          rw [heq]
          exact List.getElem_mem _
        simp only [List.zip_cons_cons, List.find?_cons, hne, List.getElem_cons_succ]
        exact ih hnd.2 (by simp at hlen; omega) j (by simp at hi; omega)

omit [Field F] [DecidableEq F] in
private theorem find?_append_left_of_not_mem {env1 env2 : Environment F Nat}
    {nm : String} (hnot : nm ∉ env1.map Prod.fst) :
    (env1 ++ env2).find? (·.1 == nm) = env2.find? (·.1 == nm) := by
  induction env1 with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hnot
    have hne : (hd.1 == nm) = false := beq_false_of_ne (Ne.symm hnot.1)
    simp [hne, ih hnot.2]

private theorem witnessLetChain_inv
    {world : World F} (hsio : StarkIOWorld world) (hkio : KzgIOWorld world)
    (body : Expr) :
    ∀ (idx : Nat) (chs : List (WitnessChannelKind × Nat))
      (locals : Environment F Nat) (h h' : Heap F) (r : SourceValue F),
      EvalExpr world [] locals (qualifyExprF F (witnessLetChain idx chs body)) h r h' →
      ∃ (wPtrs : List (SourceValue F)) (ws : List (List UInt8)) (hMid : Heap F),
        wPtrs.length = chs.length ∧
        Heap.Extends h hMid ∧
        List.Forall₂ (ByteStreamRel hMid) ws wPtrs ∧
        EvalExpr world []
          ((((List.range chs.length).map (fun j => witnessVarName (idx + j))).zip wPtrs).reverse ++ locals)
          (qualifyExprF F body) hMid r h' := by
  intro idx chs
  induction chs generalizing idx with
  | nil =>
    intro locals h h' r ev
    exact ⟨[], [], h, rfl, Heap.Extends.refl h, .nil, by simpa [witnessLetChain] using ev⟩
  | cons hd tl ih =>
    rcases hd with ⟨kind, chId⟩
    intro locals h h' r ev
    simp only [witnessLetChain, letE, callE, litE, qualifyExprF, Lower.qualifyExpr,
      Lower.qualifyPat, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map,
      qualifyName_readerFn] at ev
    obtain ⟨wPtr, h1, evCall, evRest⟩ := evalExpr_let_bind_inv ev
    obtain ⟨_, _, evLit, evReader⟩ := evalExpr_call1_inv evCall
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evLit
    obtain ⟨ext01, bs, hBsRel, _⟩ := witness_stream_exists hsio hkio kind evReader
    obtain ⟨wPtrs, ws, hMid, hlenPtrs, ext1m, hTailRel, evBody⟩ :=
      ih (idx + 1) ((witnessVarName idx, wPtr) :: locals) h1 h' r evRest
    have hBsMid : ByteStreamRel hMid bs wPtr := hBsRel.mono ext1m
    refine ⟨wPtr :: wPtrs, bs :: ws, hMid, by simp [hlenPtrs], ext01.trans ext1m,
      .cons hBsMid hTailRel, ?_⟩
    have hEqZip :
        (((List.range (tl.length + 1)).map (fun j => witnessVarName (idx + j))).zip (wPtr :: wPtrs)).reverse ++ locals =
        (((List.range tl.length).map (fun j => witnessVarName (idx + 1 + j))).zip wPtrs).reverse ++
          (witnessVarName idx, wPtr) :: locals := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.zip_cons_cons,
          List.reverse_cons, List.append_assoc]
      congr 2
      congr 1
      apply List.map_congr_left
      intro j _
      simp only [Function.comp_def]
      congr 1; omega
    simpa [hEqZip] using evBody

omit [Field F] [DecidableEq F] in
private theorem find?_reverse_zip_nodup {names : List String} {vals : List (SourceValue F)}
    (hnd : names.Nodup) (hlen : names.length = vals.length) :
    ∀ i (hi : i < names.length),
      (names.zip vals).reverse.find? (·.1 == names[i]) = some (names[i], vals[i]'(by omega)) := by
  intro i hi
  have hrevMap : ((names.zip vals).reverse).map Prod.fst = names.reverse := by
    rw [List.map_reverse, List.map_fst_zip (by omega)]
  have hndRev : (((names.zip vals).reverse).map Prod.fst).Nodup := by
    rw [hrevMap]; exact List.nodup_reverse.mpr hnd
  have hmem : (names[i], vals[i]'(by omega)) ∈ (names.zip vals).reverse := by
    rw [List.mem_reverse]
    have hget : (names.zip vals)[i]'(by rw [List.length_zip, hlen, min_self]; omega) =
        (names[i], vals[i]'(by omega)) := by
      simp [List.getElem_zip]
    rw [← hget]
    exact List.getElem_mem _
  have aux : ∀ (l : Environment F Nat) (k : String) (v : SourceValue F),
      (l.map Prod.fst).Nodup → (k, v) ∈ l → l.find? (·.1 == k) = some (k, v) := by
    intro l k v hnod hM
    induction l with
    | nil => cases hM
    | cons hd tl ih =>
      simp only [List.map_cons, List.nodup_cons] at hnod
      rcases List.mem_cons.mp hM with rfl | hM'
      · simp
      · have hne : hd.1 ≠ k := by
          intro heq
          apply hnod.1
          rw [heq]
          exact List.mem_map.mpr ⟨(k, v), hM', rfl⟩
        simp [beq_false_of_ne hne, ih hnod.2 hM']
  exact aux _ _ _ hndRev hmem

omit [Field F] [DecidableEq F] in
private theorem find?_append_some_left {env1 env2 : Environment F Nat}
    {p : String × SourceValue F → Bool} {a : String × SourceValue F}
    (h : env1.find? p = some a) : (env1 ++ env2).find? p = some a := by
  induction env1 with
  | nil => simp at h
  | cons hd tl ih =>
    simp only [List.find?_cons] at h ⊢
    cases hp : p hd <;> simp_all

omit [DecidableEq F] in
private theorem qualifyExprF_map_vE (ns : List String) :
    ns.map (fun x => (Lower.qualifyExpr (vE x)).map (Nat.cast : Nat → F)) =
      ns.map (fun nm => .var nm) := by
  induction ns with
  | nil => rfl
  | cons a tl ih => simp [vE, Lower.qualifyExpr, Aiur.Generic.Expr.map]

private theorem witness_wrapper_eval_inner
    {world : World F} (hsio : StarkIOWorld world) (hkio : KzgIOWorld world)
    {wrapperEntry checkFnName : String}
    {pubParams : List String} {channels : List (WitnessChannelKind × Nat)}
    {assertOk : Bool}
    (hchkQual : hasDoubleColon checkFnName.toList = true)
    (hnd : (pubParams ++ (List.range channels.length).map witnessVarName).Nodup)
    (hwrap : WorldHasFn world wrapperEntry pubParams
      (qualifyExprF F (witnessWrapperBody pubParams channels checkFnName assertOk)))
    {pub : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalFn world wrapperEntry pub h r h') :
    ∃ (ws : List (List UInt8)) (wPtrs : List (SourceValue F)) (hMid : Heap F),
      ws.length = channels.length ∧
      Heap.Extends h hMid ∧
      List.Forall₂ (ByteStreamRel hMid) ws wPtrs ∧
      if assertOk then
        r = .tuple [] ∧ EvalFn world checkFnName (pub ++ wPtrs) hMid (.field 1) h'
      else
        EvalFn world checkFnName (pub ++ wPtrs) hMid r h' := by
  have hplain : isPlainExpr (qualifyExprF F (witnessWrapperBody pubParams channels checkFnName assertOk)) = true := by
    rw [Lower.isPlainExpr_qualifyExprF]
    exact isPlainExpr_witnessWrapperBody pubParams channels checkFnName assertOk
  obtain ⟨hlenPub, body⟩ := evalFn_plain_inv hwrap hplain ev
  unfold witnessWrapperBody at body
  obtain ⟨wPtrs, ws, hMid, hlenPtrs, extMid, hWsRel, evTail⟩ :=
    witnessLetChain_inv hsio hkio _ 0 channels (pubParams.zip pub) h h' r body
  have hWNamesEq : (List.range channels.length).map (fun j => witnessVarName (0 + j)) =
      (List.range channels.length).map witnessVarName := by
    apply List.map_congr_left; intro j _; simp
  rw [hWNamesEq] at evTail
  set wNames := (List.range channels.length).map witnessVarName
  have hndPub : pubParams.Nodup := (List.nodup_append.mp hnd).1
  have hndW : wNames.Nodup := (List.nodup_append.mp hnd).2.1
  have hdisj : ∀ a ∈ pubParams, ∀ b ∈ wNames, a ≠ b := (List.nodup_append.mp hnd).2.2
  have hlenW : wNames.length = wPtrs.length := by simp [wNames, hlenPtrs]
  have hlenWs : ws.length = channels.length := by
    rw [List.Forall₂.length_eq hWsRel, hlenPtrs]
  set envAll := (wNames.zip wPtrs).reverse ++ pubParams.zip pub
  have hlookAll : ∀ i (hi : i < (pubParams ++ wNames).length),
      envAll.find? (·.1 == (pubParams ++ wNames)[i]) =
        some ((pubParams ++ wNames)[i], (pub ++ wPtrs)[i]'(by simp [hlenPub, hlenW] at hi ⊢; omega)) := by
    intro i hi
    by_cases hlt : i < pubParams.length
    · have hgetL : (pubParams ++ wNames)[i] = pubParams[i] := List.getElem_append_left hlt
      have hgetR : (pub ++ wPtrs)[i]'(by simp [hlenPub, hlenW] at hi ⊢; omega) =
          pub[i]'(by omega) := List.getElem_append_left (by omega)
      rw [hgetL, hgetR]
      have hnot : pubParams[i] ∉ ((wNames.zip wPtrs).reverse).map Prod.fst := by
        rw [List.map_reverse, List.map_fst_zip (by omega), List.mem_reverse]
        intro hmem
        exact hdisj pubParams[i] (List.getElem_mem _) pubParams[i] hmem rfl
      rw [find?_append_left_of_not_mem hnot]
      exact find?_zip_nodup hndPub hlenPub.symm i hlt
    · have hj : i - pubParams.length < wNames.length := by simp at hi; omega
      have hgetL : (pubParams ++ wNames)[i] = wNames[i - pubParams.length] :=
        List.getElem_append_right (by omega)
      have hgetR : (pub ++ wPtrs)[i]'(by simp [hlenPub, hlenW] at hi ⊢; omega) =
          wPtrs[i - pubParams.length]'(by omega) := by
        have h1 : pub.length ≤ i := by omega
        rw [List.getElem_append_right h1]
        congr 1; omega
      rw [hgetL, hgetR]
      exact find?_append_some_left (find?_reverse_zip_nodup hndW hlenW (i - pubParams.length) hj)
  have hqName : qualifyName checkFnName = checkFnName := by
    simp [qualifyName, hchkQual]
  have hEvalInner : ∀ {h0 h1 : Heap F} {v : SourceValue F},
      EvalExpr world [] envAll
        (qualifyExprF F (callE checkFnName ((pubParams ++ wNames).map vE))) h0 v h1 →
      EvalFn world checkFnName (pub ++ wPtrs) h0 v h1 := by
    intro h0 h1 v evC
    simp only [callE, qualifyExprF, Lower.qualifyExpr, Aiur.Generic.Expr.map, hqName] at evC
    obtain ⟨vs, hm, evArgs, evFn⟩ := evalExpr_call_inv evC
    rw [List.map_map, List.map_map] at evArgs
    have evArgs' : EvalArgs world [] envAll ((pubParams ++ wNames).map (fun nm => .var nm)) h0 vs hm := by
      have hmap := qualifyExprF_map_vE (F := F) (pubParams ++ wNames)
      simpa [Function.comp_def, hmap] using evArgs
    obtain ⟨rfl, rfl⟩ := evalArgs_vars_eq (by simp [hlenPub, hlenW]) hlookAll evArgs'
    exact evFn
  cases assertOk
  · simp only [Bool.false_eq_true, ↓reduceIte] at evTail ⊢
    exact ⟨ws, wPtrs, hMid, hlenWs, extMid, hWsRel, hEvalInner evTail⟩
  · simp only [↓reduceIte] at evTail ⊢
    simp only [letE, seqE, vE, litE, qualifyExprF, Lower.qualifyExpr, Lower.qualifyPat,
      Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map, Nat.cast_one] at evTail
    obtain ⟨vOk, h1, evCall, evAssertSeq⟩ := evalExpr_let_bind_inv evTail
    have evFn := hEvalInner evCall
    obtain ⟨_, h2, evAssert, evUnit⟩ := evalExpr_let_wildcard_inv evAssertSeq
    cases evAssert with
    | builtin hargs happ =>
      cases hargs with | cons evVar t1 =>
      cases t1 with | cons evLit1 t2 =>
      cases t2
      obtain ⟨hlOk, rfl⟩ := evalExpr_var_inv evVar; simp at hlOk; subst hlOk
      obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evLit1
      simp only [Builtin.apply] at happ
      obtain ⟨_, hEq1, _⟩ := Aiur.evalAssertEq_ok.mp happ
      subst hEq1
      cases evUnit with
      | tuple htu =>
        cases htu
        exact ⟨ws, wPtrs, hMid, hlenWs, extMid, hWsRel, rfl, evFn⟩

/-- **Certified NP Existential Backward Soundness (`witness_wrapper_sound`)**:
if `wrapperEntry` reads checked `StarkIO` / `KzgIO` witness channels and delegates to any
backward-sound inner predicate `checkFnName`, then ANY accepted derivation
`EvalFn world wrapperEntry pub h (.field 1) h'` guarantees the existence of finite,
valid (`< 256`) byte-list witnesses `ws : List (List UInt8)` satisfying `Spec pub ws` —
regardless of untrusted host hint responses! -/
theorem witness_wrapper_sound
    {world : World F} (hsio : StarkIOWorld world) (hkio : KzgIOWorld world)
    {wrapperEntry checkFnName : String}
    {pubParams : List String} {channels : List (WitnessChannelKind × Nat)}
    (hchkQual : hasDoubleColon checkFnName.toList = true)
    (hnd : (pubParams ++ (List.range channels.length).map witnessVarName).Nodup)
    (hwrap : WorldHasFn world wrapperEntry pubParams
      (qualifyExprF F (witnessWrapperBody pubParams channels checkFnName false)))
    {Spec : List (SourceValue F) → List (List UInt8) → Prop}
    (hSpec : ∀ (pubArgs : List (SourceValue F)) (h1 h2 : Heap F)
      (wPtrs : List (SourceValue F)) (ws : List (List UInt8)),
      List.Forall₂ (ByteStreamRel h1) ws wPtrs →
      EvalFn world checkFnName (pubArgs ++ wPtrs) h1 (.field 1) h2 →
      Spec pubArgs ws)
    {pub : List (SourceValue F)} {h h' : Heap F}
    (ev : EvalFn world wrapperEntry pub h (.field 1) h') :
    ∃ ws : List (List UInt8),
      ws.length = channels.length ∧
      (∀ b ∈ ws, isValidByteList (b.map UInt8.toNat)) ∧
      Spec pub ws := by
  obtain ⟨ws, wPtrs, hMid, hlen, _, hRel, evInner⟩ :=
    witness_wrapper_eval_inner hsio hkio hchkQual hnd hwrap ev
  exact ⟨ws, hlen, fun b _ => isValidByteList_ofUInt8List b,
    hSpec pub hMid h' wPtrs ws hRel evInner⟩

/-- **Certified NP Existential Backward Soundness for `--assert-ok` (`()`-returning) wrappers**:
any successful `EvalFn world wrapperEntry pub h (.tuple []) h'` guarantees the existence of
finite, valid (`< 256`) byte-list witnesses `ws : List (List UInt8)` satisfying `Spec pub ws`. -/
theorem witness_wrapper_assertOk_sound
    {world : World F} (hsio : StarkIOWorld world) (hkio : KzgIOWorld world)
    {wrapperEntry checkFnName : String}
    {pubParams : List String} {channels : List (WitnessChannelKind × Nat)}
    (hchkQual : hasDoubleColon checkFnName.toList = true)
    (hnd : (pubParams ++ (List.range channels.length).map witnessVarName).Nodup)
    (hwrap : WorldHasFn world wrapperEntry pubParams
      (qualifyExprF F (witnessWrapperBody pubParams channels checkFnName true)))
    {Spec : List (SourceValue F) → List (List UInt8) → Prop}
    (hSpec : ∀ (pubArgs : List (SourceValue F)) (h1 h2 : Heap F)
      (wPtrs : List (SourceValue F)) (ws : List (List UInt8)),
      List.Forall₂ (ByteStreamRel h1) ws wPtrs →
      EvalFn world checkFnName (pubArgs ++ wPtrs) h1 (.field 1) h2 →
      Spec pubArgs ws)
    {pub : List (SourceValue F)} {h h' : Heap F}
    (ev : EvalFn world wrapperEntry pub h (.tuple []) h') :
    ∃ ws : List (List UInt8),
      ws.length = channels.length ∧
      (∀ b ∈ ws, isValidByteList (b.map UInt8.toNat)) ∧
      Spec pub ws := by
  obtain ⟨ws, wPtrs, hMid, hlen, _, hRel, _, evInner⟩ :=
    witness_wrapper_eval_inner hsio hkio hchkQual hnd hwrap ev
  exact ⟨ws, hlen, fun b _ => isValidByteList_ofUInt8List b,
    hSpec pub hMid h' wPtrs ws hRel evInner⟩

end SoundnessProofs

end IxCC.AiurBackend.WitnessIO
