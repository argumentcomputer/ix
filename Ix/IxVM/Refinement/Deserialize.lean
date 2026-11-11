import Ix.IxVM.Refinement.Mirrors.Deserialize
import Ix.IxVM.Refinement.TagNWide

/-! # The Deserialize slice: `UInt64` and `IxonDeserialize` primitives

On top of the generated
mirrors in `Ix.IxVM.Refinement.Mirrors.Deserialize`, this module establishes:

* `fromField_mapCall_inv` and `u64BytesMeasure_dec`: the decreasing measure on
  8-byte `UInt64` tuples for every count-recursive `IxonDeserialize` function
  guarded by `UInt64::is_zero` and decremented by `UInt64::saturating_pred`;
* `buildSuccChain_complete` and `getU64List_complete`: completeness of the two
  recursive mirrors `IxonDeserialize::build_succ_chain` and
  `IxonDeserialize::get_u64_list`;
* `*_run` and refinement theorems for the `UInt64` and `IxonDeserialize`
  leaf primitives (`UInt64::is_zero`, `UInt64::eq`, `UInt64::saturating_pred`,
  `UInt64::to_field`, `IxonDeserialize::read_byte`,
  `IxonDeserialize::assert_wire_bool`, `IxonDeserialize::get_quot_kind`,
  `IxonDeserialize::unpack_def_kind_safety`,
  `IxonDeserialize::value_contract_from_bits`,
  `IxonDeserialize::binder_contract_from_bits`). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace IxVM.Refinement.Deserialize

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.TagN

set_option linter.unusedSimpArgs false

@[simp] theorem value_type_construct (name ctor : String) (args : List (SourceValue F)) :
    (Value.construct name ctor args).type = .enum name := by
  rw [Value.type]

/-! ## Inversion of `UInt8::from_field` and the `UInt64` count measure -/

theorem mem_zip_map_iff {α β γ : Type} {l : List α} {f : α → β} {g : α → γ} {p : β × γ} :
    p ∈ (l.map f).zip (l.map g) ↔ ∃ x ∈ l, p = (f x, g x) := by
  induction l generalizing p with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨x, hx, rfl⟩)
      · exact ⟨a, .inl rfl, rfl⟩
      · exact ⟨x, .inr hx, rfl⟩
    · rintro ⟨x, rfl | hx, rfl⟩
      · exact .inl rfl
      · exact .inr ⟨x, hx, rfl⟩

theorem find_fromFieldMap :
    IxVM.coreTables.findMap? "UInt8::from_field" = some fromFieldMap := by
  decide +kernel

/-- **Any successful `UInt8::from_field` map call** returns its input unchanged,
leaves the heap unchanged, and witnesses that the input is a byte `< 256`. -/
theorem fromField_mapCall_inv {v w : SourceValue F} {h h' : Heap F}
    (hm : mapCall IxVM.source.tables "UInt8::from_field" [v] h = some (w, h')) :
    w = v ∧ h' = h ∧ ∃ x : Nat, x < 256 ∧ v = .field (x : F) := by
  unfold mapCall at hm
  cases looked : lookupMap IxVM.source.tables "UInt8::from_field" [v] with
  | error _ => simp [looked] at hm
  | ok row =>
    simp only [looked, Option.some.injEq, Prod.mk.injEq] at hm
    rcases hm with ⟨hrow, rfl⟩
    subst hrow
    obtain ⟨map, key, found, -, -, extracted, mem, -⟩ := Aiur.lookupMap_spec looked
    change IxVM.coreTables.findMap? "UInt8::from_field" = some map at found
    rw [find_fromFieldMap, Option.some.injEq] at found
    subst found
    have rows : IxVM.coreTables.mapRows fromFieldMap =
        IxVM.byteInputsTable.rows.zip IxVM.byteValuesTable.rows := by
      simp only [Aiur.Program.mapRows, show fromFieldMap.input = "UInt8::byte_inputs" from rfl,
        show fromFieldMap.output = "UInt8::byte_values" from rfl, IxVM.find_byteInputs,
        IxVM.find_byteValues]
    change (key, row) ∈ IxVM.coreTables.mapRows fromFieldMap at mem
    rw [rows] at mem
    simp only [IxVM.byteInputsTable, IxVM.byteValuesTable, List.map_map] at mem
    obtain ⟨x, hx, hkr⟩ := mem_zip_map_iff.mp mem
    simp only [List.mem_range] at hx
    simp only [Function.comp, IxVM.coreRow, IxVM.coreLeaf, List.map,
      Prod.mk.injEq] at hkr
    rcases hkr with ⟨rfl, rfl⟩
    have hv := Aiur.Value.toConstant_spec extracted
    simp [Constant.toValue, Value.mapAddress] at hv
    subst hv
    exact ⟨by simp [Constant.toValue, Value.mapAddress], rfl, x, hx, rfl⟩

theorem saturatingPred_step {b v w : SourceValue F} {h h' : Heap F} (hb : b ≠ .field 0)
    (op : evalBinOp .sub b (.field 1) = .ok v)
    (hm : mapCall IxVM.source.tables "UInt8::from_field" [v] h = some (w, h')) :
    u64Measure w < u64Measure b ∧ h' = h := by
  obtain ⟨rfl, rfl, -⟩ := fromField_mapCall_inv hm
  exact ⟨u64Measure_dec hb op, rfl⟩

/-- **Measure of an 8-byte `UInt64` value** for count-recursive deserializers:
the base-256 weighted sum of the 8 limbs' `u64Measure`s. -/
def u64BytesMeasure : SourceValue F → Nat
  | .tuple [b0, b1, b2, b3, b4, b5, b6, b7] =>
    u64Measure b0 + 256 * (u64Measure b1 + 256 * (u64Measure b2 + 256 * (u64Measure b3 +
      256 * (u64Measure b4 + 256 * (u64Measure b5 + 256 * (u64Measure b6 + 256 * u64Measure b7))))))
  | _ => 0

@[simp] theorem u64Measure_zero : u64Measure (.field 0 : SourceValue F) = 0 := rfl

@[simp] theorem u64Measure_255 : u64Measure (.field 255 : SourceValue F) = 255 := by
  decide +kernel

theorem saturatingPred_bind_inv {b : SourceValue F} {h : Heap F}
    {f : SourceValue F × Heap F → Option α} {res : α}
    (hb : b ≠ .field 0)
    (hrun : Option.bind
      (Option.bind
        (match evalBinOp .sub b (.field 1) with
          | .ok z => some (z, h)
          | .error _ => none)
        (fun x => mapCall IxVM.source.tables "UInt8::from_field" [x.1] x.2))
      f = some res) :
    ∃ w, u64Measure w < u64Measure b ∧ f (w, h) = some res := by
  cases op : evalBinOp .sub b (.field 1) with
  | error _ => simp [op, Option.bind] at hrun
  | ok v =>
    simp only [op, Option.bind] at hrun
    cases hm : mapCall IxVM.source.tables "UInt8::from_field" [v] h with
    | none => simp [hm, Option.bind] at hrun
    | some wh =>
      simp only [hm, Option.bind] at hrun
      rcases wh with ⟨w, h'⟩
      obtain ⟨hlt, rfl⟩ := saturatingPred_step hb op hm
      exact ⟨w, hlt, hrun⟩

/-- **When `UInt64::is_zero` returns `0`, `UInt64::saturating_pred` strictly
decreases `u64BytesMeasure`.** -/
theorem u64BytesMeasure_dec {x y : SourceValue F} {h1 h2 h3 h4 : Heap F}
    (hiz : EvalFn W "UInt64::is_zero" [x] h1 (.field 0) h2)
    (hsp : EvalFn W "UInt64::saturating_pred" [x] h3 y h4) :
    u64BytesMeasure y < u64BytesMeasure x := by
  obtain ⟨k1, hk1⟩ := Mirrors.«UInt64::is_zero».of_eval hiz
  have hiz_run := hk1 (k1 + 1) (by omega)
  have hne : x ≠ .tuple [.field 0, .field 0, .field 0, .field 0, .field 0, .field 0, .field 0, .field 0] := by
    intro heq
    subst heq
    simp [Mirrors.«UInt64::is_zero»] at hiz_run
  obtain ⟨k2, hk2⟩ := Mirrors.«UInt64::saturating_pred».of_eval hsp
  have hsp_run := hk2 (k2 + 2) (by omega)
  dsimp only [Mirrors.«UInt64::saturating_pred»] at hsp_run
  split at hsp_run
  · simp only [Mirrors.«UInt8::to_field», bind, Option.bind] at hsp_run
    split_ifs at hsp_run
    · subst_vars; exact (hne rfl).elim
    all_goals {
      obtain ⟨w, hlt, hsp_run⟩ := saturatingPred_bind_inv (by assumption) hsp_run
      simp only [Option.some.injEq, Prod.mk.injEq] at hsp_run
      rcases hsp_run with ⟨rfl, rfl⟩
      subst_vars
      simp only [u64BytesMeasure, u64Measure_zero, u64Measure_255]
      omega
    }
  · cases hsp_run

/-! ## Completeness of the recursive mirrors -/

/-- **Every derivation of `IxonDeserialize::build_succ_chain` is a run of its
mirror**, by strong induction on `u64BytesMeasure x_count`. -/
theorem buildSuccChain_complete : Mirrors.«IxonDeserialize::build_succ_chain».Complete := by
  suffices H : ∀ m, ∀ {x_base x_count : SourceValue F} {h h' : Heap F} {r : SourceValue F},
      u64BytesMeasure x_count = m →
      EvalFn W "IxonDeserialize::build_succ_chain" [x_base, x_count] h r h' →
      ∃ k0, ∀ k ≥ k0, Mirrors.«IxonDeserialize::build_succ_chain» k h x_base x_count = some (r, h') by
    intro x_base x_count h h' r ev
    exact H _ rfl ev
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro x_base x_count h h' r hm ev
  have body := ev.function_inv IxVM.IxonDeserialize.build_succ_chain.lookup
    (by simp [IxVM.IxonDeserialize.build_succ_chain, ControlLower.hasControl])
  simp only [IxVM.IxonDeserialize.build_succ_chain] at body
  obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
  obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
  obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
  obtain ⟨l15, rfl⟩ := d13.var_inv
  simp at l15
  subst l15
  obtain ⟨rfl, rfl⟩ := args14.nil_inv
  rw [instanceName_plain_some] at callee9
  obtain ⟨k16, hk17⟩ := Mirrors.«UInt64::is_zero».of_eval callee9
  rw [matchPattern_bind] at mt4
  simp only [Except.ok.injEq, Option.some.injEq] at mt4
  subst mt4
  obtain ⟨v18, m19, bs20, body21, d22, sel23, d24⟩ := d5.matchValue_inv
  obtain ⟨l25, rfl⟩ := d22.var_inv
  simp at l25
  subst l25
  rcases selectArm_literal_inv sel23 with ⟨hc26, rfl, rfl⟩ | ⟨hc26, sel27⟩
  · obtain ⟨l28, rfl⟩ := d24.var_inv
    simp at l28
    subst l28
    refine ⟨k16 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp (config := { decide := true, maxSteps := 10000000 })
      [Mirrors.«IxonDeserialize::build_succ_chain», hk17 k' (by omega), hc26]
  · rcases selectArm_literal_inv sel27 with ⟨hc28, rfl, rfl⟩ | ⟨hc28, sel29⟩
    · obtain ⟨v30, m31, bs32, d33, mt34, d35⟩ := d24.letValue_inv
      obtain ⟨vs36, m37, args38, callee39⟩ := d33.call_inv
      obtain ⟨v40, vs41, m42, rfl, d43, args44⟩ := args38.cons_inv
      obtain ⟨l45, rfl⟩ := d43.var_inv
      simp at l45
      subst l45
      obtain ⟨v46, vs47, m48, rfl, d49, args50⟩ := args44.cons_inv
      obtain ⟨vs51, m52, args53, callee54⟩ := d49.call_inv
      obtain ⟨v55, vs56, m57, rfl, d58, args59⟩ := args53.cons_inv
      obtain ⟨l60, rfl⟩ := d58.var_inv
      simp at l60
      subst l60
      obtain ⟨rfl, rfl⟩ := args59.nil_inv
      rw [instanceName_plain_some] at callee54
      obtain ⟨k61, hk62⟩ := Mirrors.«UInt64::saturating_pred».of_eval callee54
      obtain ⟨rfl, rfl⟩ := args50.nil_inv
      rw [instanceName_plain_some] at callee39
      have hdec : u64BytesMeasure v46 < m := hm ▸ u64BytesMeasure_dec (hc28 ▸ callee9) callee54
      obtain ⟨k63, hk64⟩ := ih (u64BytesMeasure v46) hdec rfl callee39
      rw [matchPattern_bind] at mt34
      simp only [Except.ok.injEq, Option.some.injEq] at mt34
      subst mt34
      obtain ⟨vs65, args66, rfl⟩ := d35.construct_inv
      obtain ⟨v67, vs68, m69, rfl, d70, args71⟩ := args66.cons_inv
      obtain ⟨v72, m73, d74, rfl, rfl⟩ := d70.store_inv
      obtain ⟨l75, rfl⟩ := d74.var_inv
      simp at l75
      subst l75
      obtain ⟨rfl, rfl⟩ := args71.nil_inv
      refine ⟨k16 + k61 + k63 + 1, fun k hk => ?_⟩
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp (config := { decide := true, maxSteps := 10000000 })
        [Mirrors.«IxonDeserialize::build_succ_chain», hk17 k' (by omega), hc26, hc28,
          hk62 k' (by omega), hk64 k' (by omega)]
    · simp [SourceSemantics.selectArm] at sel29

/-- **Every derivation of `IxonDeserialize::get_u64_list` is a run of its
mirror**, by strong induction on `u64BytesMeasure x_count`. -/
theorem getU64List_complete : Mirrors.«IxonDeserialize::get_u64_list».Complete := by
  suffices H : ∀ m, ∀ {x_stream x_count : SourceValue F} {h h' : Heap F} {r : SourceValue F},
      u64BytesMeasure x_count = m →
      EvalFn W "IxonDeserialize::get_u64_list" [x_stream, x_count] h r h' →
      ∃ k0, ∀ k ≥ k0, Mirrors.«IxonDeserialize::get_u64_list» k h x_stream x_count = some (r, h') by
    intro x_stream x_count h h' r ev
    exact H _ rfl ev
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro x_stream x_count h h' r hm ev
  have body := ev.function_inv IxVM.IxonDeserialize.get_u64_list.lookup
    (by simp [IxVM.IxonDeserialize.get_u64_list, ControlLower.hasControl])
  simp only [IxVM.IxonDeserialize.get_u64_list] at body
  obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
  obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
  obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
  obtain ⟨l15, rfl⟩ := d13.var_inv
  simp at l15
  subst l15
  obtain ⟨rfl, rfl⟩ := args14.nil_inv
  rw [instanceName_plain_some] at callee9
  obtain ⟨k16, hk17⟩ := Mirrors.«UInt64::is_zero».of_eval callee9
  rw [matchPattern_bind] at mt4
  simp only [Except.ok.injEq, Option.some.injEq] at mt4
  subst mt4
  obtain ⟨v18, m19, bs20, body21, d22, sel23, d24⟩ := d5.matchValue_inv
  obtain ⟨l25, rfl⟩ := d22.var_inv
  simp at l25
  subst l25
  rcases selectArm_literal_inv sel23 with ⟨hc26, rfl, rfl⟩ | ⟨hc26, sel27⟩
  · obtain ⟨vs28, args29, rfl⟩ := d24.tuple_inv
    obtain ⟨v30, vs31, m32, rfl, d33, args34⟩ := args29.cons_inv
    obtain ⟨v35, m36, d37, rfl, rfl⟩ := d33.store_inv
    obtain ⟨vs38, args39, rfl⟩ := d37.construct_inv
    obtain ⟨rfl, rfl⟩ := args39.nil_inv
    obtain ⟨v40, vs41, m42, rfl, d43, args44⟩ := args34.cons_inv
    obtain ⟨l45, rfl⟩ := d43.var_inv
    simp at l45
    subst l45
    obtain ⟨rfl, rfl⟩ := args44.nil_inv
    refine ⟨k16 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp (config := { decide := true, maxSteps := 10000000 })
      [Mirrors.«IxonDeserialize::get_u64_list», hk17 k' (by omega), hc26]
  · rcases selectArm_literal_inv sel27 with ⟨hc28, rfl, rfl⟩ | ⟨hc28, sel29⟩
    · obtain ⟨v30, m31, bs32, d33, mt34, d35⟩ := d24.letValue_inv
      obtain ⟨vs36, m37, args38, callee39⟩ := d33.call_inv
      obtain ⟨v40, vs41, m42, rfl, d43, args44⟩ := args38.cons_inv
      obtain ⟨l45, rfl⟩ := d43.var_inv
      simp at l45
      subst l45
      obtain ⟨rfl, rfl⟩ := args44.nil_inv
      rw [instanceName_plain_some] at callee39
      obtain ⟨k46, hk47⟩ := Mirrors.«IxonDeserialize::get_tagn0».of_eval getU64le_complete callee39
      obtain ⟨ys48, hp49, hl50, ml51⟩ := matchPattern_tuple_inv mt34
      rcases ys48 with _ | ⟨y52, _ | ⟨y53, _ | ⟨_, _⟩⟩⟩ <;> simp at hl50
      simp [matchListWith, matchPattern_bind, matchPattern_wildcard, bind, Except.bind, pure, Except.pure] at ml51
      subst ml51
      obtain ⟨v54, m55, bs56, d57, mt58, d59⟩ := d35.letValue_inv
      obtain ⟨vs60, m61, args62, callee63⟩ := d57.call_inv
      obtain ⟨v64, vs65, m66, rfl, d67, args68⟩ := args62.cons_inv
      obtain ⟨l69, rfl⟩ := d67.var_inv
      simp at l69
      subst l69
      obtain ⟨v70, vs71, m72, rfl, d73, args74⟩ := args68.cons_inv
      obtain ⟨vs75, m76, args77, callee78⟩ := d73.call_inv
      obtain ⟨v79, vs80, m81, rfl, d82, args83⟩ := args77.cons_inv
      obtain ⟨l84, rfl⟩ := d82.var_inv
      simp at l84
      subst l84
      obtain ⟨rfl, rfl⟩ := args83.nil_inv
      rw [instanceName_plain_some] at callee78
      obtain ⟨k85, hk86⟩ := Mirrors.«UInt64::saturating_pred».of_eval callee78
      obtain ⟨rfl, rfl⟩ := args74.nil_inv
      rw [instanceName_plain_some] at callee63
      have hdec : u64BytesMeasure v70 < m := hm ▸ u64BytesMeasure_dec (hc28 ▸ callee9) callee78
      obtain ⟨k87, hk88⟩ := ih (u64BytesMeasure v70) hdec rfl callee63
      obtain ⟨ys89, hp90, hl91, ml92⟩ := matchPattern_tuple_inv mt58
      rcases ys89 with _ | ⟨y93, _ | ⟨y94, _ | ⟨_, _⟩⟩⟩ <;> simp at hl91
      simp [matchListWith, matchPattern_bind, matchPattern_wildcard, bind, Except.bind, pure, Except.pure] at ml92
      subst ml92
      obtain ⟨vs95, args96, rfl⟩ := d59.tuple_inv
      obtain ⟨v97, vs98, m99, rfl, d100, args101⟩ := args96.cons_inv
      obtain ⟨v102, m103, d104, rfl, rfl⟩ := d100.store_inv
      obtain ⟨vs105, args106, rfl⟩ := d104.construct_inv
      obtain ⟨v107, vs108, m109, rfl, d110, args111⟩ := args106.cons_inv
      obtain ⟨l112, rfl⟩ := d110.var_inv
      simp at l112
      subst l112
      obtain ⟨v113, vs114, m115, rfl, d116, args117⟩ := args111.cons_inv
      obtain ⟨l118, rfl⟩ := d116.var_inv
      simp at l118
      subst l118
      obtain ⟨rfl, rfl⟩ := args117.nil_inv
      obtain ⟨v119, vs120, m121, rfl, d122, args123⟩ := args101.cons_inv
      obtain ⟨l124, rfl⟩ := d122.var_inv
      simp at l124
      subst l124
      obtain ⟨rfl, rfl⟩ := args123.nil_inv
      refine ⟨k16 + k46 + k85 + k87 + 1, fun k hk => ?_⟩
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp (config := { decide := true, maxSteps := 10000000 })
        [Mirrors.«IxonDeserialize::get_u64_list», hk17 k' (by omega), hc26, hc28,
          hk47 k' (by omega), hp49, hk86 k' (by omega), hk88 k' (by omega), hp90]
    · simp [SourceSemantics.selectArm] at sel29

/-! ## `UInt64` mirror behavior -/

/-- **`u64Value` is injective** on 64-bit naturals. -/
theorem u64Value_inj {a b : Nat} (ha : a < 18446744073709551616) (hb : b < 18446744073709551616) :
    u64Value a = u64Value b ↔ a = b := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  simp only [u64Value, Value.tuple.injEq, List.cons.injEq, Value.field.injEq, and_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  have e0 := IxVM.natCast_inj (by omega) (by omega) h0
  have e1 := IxVM.natCast_inj (by omega) (by omega) h1
  have e2 := IxVM.natCast_inj (by omega) (by omega) h2
  have e3 := IxVM.natCast_inj (by omega) (by omega) h3
  have e4 := IxVM.natCast_inj (by omega) (by omega) h4
  have e5 := IxVM.natCast_inj (by omega) (by omega) h5
  have e6 := IxVM.natCast_inj (by omega) (by omega) h6
  have e7 := IxVM.natCast_inj (by omega) (by omega) h7
  omega

theorem u64Value_zero :
    u64Value 0 = .tuple [.field 0, .field 0, .field 0, .field 0, .field 0, .field 0, .field 0, .field 0] := by
  simp [u64Value]

/-- **`UInt64::is_zero` on `u64Value n`** returns `1` if `n = 0` and `0` otherwise. -/
theorem u64IsZero_run {n : Nat} (hn : n < 18446744073709551616) (k : Nat) (h : Heap F) :
    Mirrors.«UInt64::is_zero» (k + 1) h (u64Value n) =
      some (.field (if n = 0 then 1 else 0), h) := by
  have heq : (u64Value n = .tuple [.field 0, .field 0, .field 0, .field 0, .field 0, .field 0, .field 0, .field 0]) ↔ n = 0 := by
    rw [← u64Value_zero, u64Value_inj hn (by omega)]
  simp only [Mirrors.«UInt64::is_zero», heq]
  split <;> rfl

/-- **`UInt64::eq` on `u64Value a` and `u64Value b`** returns `1` if `a = b` and `0` otherwise. -/
theorem u64Eq_run {a b : Nat} (ha : a < 18446744073709551616) (hb : b < 18446744073709551616)
    (k : Nat) (h : Heap F) :
    Mirrors.«UInt64::eq» (k + 2) h (u64Value a) (u64Value b) =
      some (.field (if a = b then 1 else 0), h) := by
  have heq : (Value.tuple [
      .field (((a % 256 : Nat) : F) - ((b % 256 : Nat) : F)),
      .field (((a / 256 % 256 : Nat) : F) - ((b / 256 % 256 : Nat) : F)),
      .field (((a / 65536 % 256 : Nat) : F) - ((b / 65536 % 256 : Nat) : F)),
      .field (((a / 16777216 % 256 : Nat) : F) - ((b / 16777216 % 256 : Nat) : F)),
      .field (((a / 4294967296 % 256 : Nat) : F) - ((b / 4294967296 % 256 : Nat) : F)),
      .field (((a / 1099511627776 % 256 : Nat) : F) - ((b / 1099511627776 % 256 : Nat) : F)),
      .field (((a / 281474976710656 % 256 : Nat) : F) - ((b / 281474976710656 % 256 : Nat) : F)),
      .field (((a / 72057594037927936 % 256 : Nat) : F) - ((b / 72057594037927936 % 256 : Nat) : F))] :
        SourceValue F) =
      Value.tuple [.field 0, .field 0, .field 0, .field 0, .field 0, .field 0, .field 0, .field 0] ↔
      a = b := by
    simp only [Value.tuple.injEq, List.cons.injEq, Value.field.injEq, sub_eq_zero, and_true]
    rw [← u64Value_inj ha hb]
    simp [u64Value]
  simp only [Mirrors.«UInt64::eq», u64Value, Mirrors.«UInt8::to_field», evalBinOp, bind, Option.bind, heq]
  split <;> rfl

/-- **`UInt64::to_field` on `u64Value n` for `n < 2^56`** returns `.field (n : F)`. -/
theorem u64ToField_run {n : Nat} (hn : n < 72057594037927936) (k : Nat) (h : Heap F) :
    Mirrors.«UInt64::to_field» (k + 2) h (u64Value n) = some (.field (n : F), h) := by
  have hb7 : n / 72057594037927936 % 256 = 0 := by omega
  have hsum : n % 256 + 256 * (n / 256 % 256) + 65536 * (n / 65536 % 256) +
      16777216 * (n / 16777216 % 256) + 4294967296 * (n / 4294967296 % 256) +
      1099511627776 * (n / 1099511627776 % 256) + 281474976710656 * (n / 281474976710656 % 256) = n := by
    omega
  have hcast := congrArg (Nat.cast (R := F)) hsum
  push_cast at hcast
  simp [Mirrors.«UInt64::to_field», u64Value, hb7, Mirrors.«UInt8::to_field»,
    Builtin.apply, evalAssertEq, Value.pointerFree, evalBinOp, bind, Option.bind]
  exact hcast

/-- **`UInt64::to_field` on `u64Value n` for `2^56 ≤ n < 2^64`** rejects (`none`). -/
theorem u64ToField_none {n : Nat} (hlo : 72057594037927936 ≤ n) (hhi : n < 18446744073709551616)
    (k : Nat) (h : Heap F) :
    Mirrors.«UInt64::to_field» k h (u64Value n) = none := by
  rcases k with _ | _ | k
  · rfl
  · simp [Mirrors.«UInt64::to_field», u64Value, Mirrors.«UInt8::to_field»]
  · have hb7 : ((n / 72057594037927936 % 256 : Nat) : F) ≠ 0 := by
      intro heq
      have := IxVM.natCast_inj (a := n / 72057594037927936 % 256) (b := 0)
        (by omega) (by omega) (by simpa using heq)
      omega
    simp [Mirrors.«UInt64::to_field», u64Value, Mirrors.«UInt8::to_field», Builtin.apply,
      evalAssertEq, Value.pointerFree, hb7]

theorem natCast_eq_iff {a b : Nat} (ha : a < 256) (hb : b < 256) :
    ((a : F) = (b : F)) ↔ a = b :=
  ⟨IxVM.natCast_inj (by omega) (by omega), fun e => congrArg Nat.cast e⟩

theorem natCast_eq_zero_iff {a : Nat} (ha : a < 256) :
    ((a : F) = 0) ↔ a = 0 := by
  rw [← Nat.cast_zero]
  exact natCast_eq_iff ha (by omega)

theorem natCast_eq_one_iff {a : Nat} (ha : a < 256) :
    ((a : F) = 1) ↔ a = 1 := by
  rw [← Nat.cast_one]
  exact natCast_eq_iff ha (by omega)

theorem natCast_eq_ofNat_iff {a n : Nat} [n.AtLeastTwo] (ha : a < 256) (hn : n < 256) :
    ((a : F) = (OfNat.ofNat n : F)) ↔ a = n := by
  rw [← Nat.cast_ofNat (n := n)]
  exact natCast_eq_iff ha hn

theorem natCast_eq_255_iff {a : Nat} (ha : a < 256) :
    ((a : F) = 255) ↔ a = 255 :=
  natCast_eq_ofNat_iff (n := 255) ha (by decide)

theorem fromField_sub_one {b : Nat} (hb : b < 256) (hne : b ≠ 0) (h : Heap F) :
    mapCall IxVM.source.tables "UInt8::from_field" [.field ((b : F) - 1)] h =
      some (.field ((b - 1 : Nat) : F), h) := by
  rcases b with _ | b
  · exact (hne rfl).elim
  · have hsub : ((b + 1 : Nat) : F) - 1 = (b : F) := by push_cast; ring
    rw [hsub]
    exact fromField_one (by omega) h

theorem fromField_add_one {b : Nat} (hb : b < 256) (hne : b ≠ 255) (h : Heap F) :
    mapCall IxVM.source.tables "UInt8::from_field" [.field ((b : F) + 1)] h =
      some (.field ((b + 1 : Nat) : F), h) := by
  have hadd : (b : F) + 1 = ((b + 1 : Nat) : F) := by push_cast; ring
  rw [hadd]
  exact fromField_one (by omega) h

/-- **`UInt64::saturating_pred` on `u64Value n`** returns `u64Value (n - 1)`. -/
theorem u64SaturatingPred_run {n : Nat} (hn : n < 18446744073709551616) (k : Nat) (h : Heap F) :
    Mirrors.«UInt64::saturating_pred» (k + 2) h (u64Value n) =
      some (u64Value (n - 1), h) := by
  unfold Mirrors.«UInt64::saturating_pred» u64Value
  simp only [Mirrors.«UInt8::to_field», bind, Option.bind, evalBinOp, Value.field.injEq,
    natCast_eq_zero_iff (Nat.mod_lt _ (by omega))]
  split_ifs <;> {
    try rw [fromField_sub_one (Nat.mod_lt _ (by omega)) (by assumption)]
    simp only [Option.some.injEq, Prod.mk.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.field.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first | exact (Nat.cast_zero.symm.trans (congrArg Nat.cast (by omega)))
            | exact ((show (255 : F) = ((255 : Nat) : F) by norm_num).trans (congrArg Nat.cast (by omega)))
            | exact congrArg Nat.cast (by omega)
  }

/-- **`UInt64::wrapping_succ` on `u64Value n`** returns `u64Value ((n + 1) % 2^64)`. -/
theorem u64WrappingSucc_run {n : Nat} (hn : n < 18446744073709551616) (k : Nat) (h : Heap F) :
    Mirrors.«UInt64::wrapping_succ» (k + 2) h (u64Value n) =
      some (u64Value ((n + 1) % 18446744073709551616), h) := by
  conv_lhs => unfold Mirrors.«UInt64::wrapping_succ» u64Value
  simp only [Mirrors.«UInt8::to_field», bind, Option.bind, evalBinOp, Value.field.injEq,
    natCast_eq_255_iff (Nat.mod_lt _ (by omega))]
  split_ifs <;> {
    try rw [fromField_add_one (Nat.mod_lt _ (by omega)) (by assumption)]
    (first | rw [show (n + 1) % 18446744073709551616 = 0 by omega]
           | rw [show (n + 1) % 18446744073709551616 = n + 1 by omega])
    unfold u64Value
    simp only [Option.some.injEq, Prod.mk.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.field.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first | exact (Nat.cast_zero.symm.trans (congrArg Nat.cast (by omega)))
            | exact congrArg Nat.cast (by omega)
  }

/-! ## `IxonDeserialize` leaf primitives -/

/-- **`IxonDeserialize::read_byte` on a non-empty byte stream** returns the head
byte and advances the stream pointer. -/
theorem readByte_run {b : UInt8} {rest : List UInt8} {stream : SourceValue F} {h : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (b :: rest) stream) :
    ∃ restPtr, Aiur.Library.Bytes.RepByteStream byteStreamEnum h rest restPtr ∧
      ∀ k, Mirrors.«IxonDeserialize::read_byte» (k + 1) h stream =
        some (.tuple [.field (b.toNat : F), restPtr], h) := by
  cases rep with
  | @cons _ _ addr headVal tailPtr cell headRep tailRep =>
    simp only [Aiur.Library.RepU8] at headRep
    subst headRep
    refine ⟨tailPtr, tailRep, fun k => ?_⟩
    simp [Mirrors.«IxonDeserialize::read_byte», loadValue_cell cell, node_ctor]

/-- **`IxonDeserialize::read_byte` on an empty byte stream** fails (`none`). -/
theorem readByte_nil {stream : SourceValue F} {h : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h [] stream) (k : Nat) :
    Mirrors.«IxonDeserialize::read_byte» k h stream = none := by
  cases k with
  | zero => rfl
  | succ k =>
    cases rep with
    | nil cell =>
      simp [Mirrors.«IxonDeserialize::read_byte», loadValue_cell cell]

/-- **`IxonDeserialize::assert_wire_bool`** accepts bytes `< 2` and rejects
bytes `≥ 2`. -/
theorem assertWireBool_run {b : Nat} (hb : b < 256) (k : Nat) (h : Heap F) :
    Mirrors.«IxonDeserialize::assert_wire_bool» (k + 3) h (.field (b : F)) =
      if b < 2 then some (.tuple [], h) else none := by
  have hlt := lessThan_run (a := b) (b := 2) hb (by norm_num) k h
  simp only [Nat.cast_ofNat] at hlt
  by_cases hb2 : b < 2
  · simp [Mirrors.«IxonDeserialize::assert_wire_bool», hlt, hb2, Builtin.apply, evalAssertEq,
      Value.pointerFree]
  · simp [Mirrors.«IxonDeserialize::assert_wire_bool», hlt, hb2, Builtin.apply, evalAssertEq,
      Value.pointerFree]

/-- **`IxonDeserialize::value_contract_from_bits`** on wire bits `b0, b1 ∈ {0, 1}`. -/
theorem valueContractFromBits_run {b0 b1 : Nat} (hb0 : b0 < 2) (hb1 : b1 < 2) (k : Nat) (h : Heap F) :
    Mirrors.«IxonDeserialize::value_contract_from_bits» (k + 1) h (.field (b0 : F)) (.field (b1 : F)) =
      some (.construct "Ixon::ValueContract" "Mk" [
        .construct "Ixon::Owned" (if b0 = 0 then "Unique" else "Shared") [],
        .construct "Ixon::Locality" (if b1 = 0 then "Unrestricted" else "Local") []], h) := by
  obtain rfl | rfl : b0 = 0 ∨ b0 = 1 := by omega
  all_goals
    obtain rfl | rfl : b1 = 0 ∨ b1 = 1 := by omega
    all_goals simp (config := { decide := true }) [Mirrors.«IxonDeserialize::value_contract_from_bits»]

/-- **`IxonDeserialize::binder_contract_from_bits`** on wire bits `b0, b1, b2, b3 ∈ {0, 1}`. -/
theorem binderContractFromBits_run {b0 b1 b2 b3 : Nat}
    (hb0 : b0 < 2) (hb1 : b1 < 2) (hb2 : b2 < 2) (hb3 : b3 < 2) (k : Nat) (h : Heap F) :
    Mirrors.«IxonDeserialize::binder_contract_from_bits» (k + 2) h
        (.field (b0 : F)) (.field (b1 : F)) (.field (b2 : F)) (.field (b3 : F)) =
      some (.construct "Ixon::BinderContract" "Mk" [
        .construct "Ixon::Uses"
          (match b0 + 2 * b1 with
            | 0 => "Erased" | 1 => "Linear" | 2 => "Affine" | _ => "Many") [],
        .construct "Ixon::ValueContract" "Mk" [
          .construct "Ixon::Owned" (if b2 = 0 then "Unique" else "Shared") [],
          .construct "Ixon::Locality" (if b3 = 0 then "Unrestricted" else "Local") []]], h) := by
  obtain rfl | rfl : b0 = 0 ∨ b0 = 1 := by omega
  all_goals
    obtain rfl | rfl : b1 = 0 ∨ b1 = 1 := by omega
    all_goals
      obtain rfl | rfl : b2 = 0 ∨ b2 = 1 := by omega
      all_goals
        obtain rfl | rfl : b3 = 0 ∨ b3 = 1 := by omega
        all_goals simp (config := { decide := true })
          [Mirrors.«IxonDeserialize::binder_contract_from_bits»,
            Mirrors.«IxonDeserialize::value_contract_from_bits», evalBinOp]

theorem natCast_ne_of_ne {a b : Nat} (ha : a < 256) (hb : b < 256) (hne : a ≠ b) :
    (a : F) ≠ (b : F) :=
  fun e => hne (IxVM.natCast_inj (by omega) (by omega) e)

/-- **`IxonDeserialize::get_quot_kind`** on a byte `b < 256`. -/
theorem getQuotKind_run {b : Nat} (hb : b < 256) (k : Nat) (h : Heap F) :
    Mirrors.«IxonDeserialize::get_quot_kind» (k + 2) h (.field (b : F)) =
      match b with
      | 0 => some (.construct "Ixon::QuotKind" "Typ" [], h)
      | 1 => some (.construct "Ixon::QuotKind" "Ctor" [], h)
      | 2 => some (.construct "Ixon::QuotKind" "Lift" [], h)
      | 3 => some (.construct "Ixon::QuotKind" "Ind" [], h)
      | _ => none := by
  simp only [Mirrors.«IxonDeserialize::get_quot_kind», Mirrors.«UInt8::to_field»,
    bind, Option.bind, Value.field.injEq,
    natCast_eq_zero_iff hb, natCast_eq_one_iff hb,
    natCast_eq_ofNat_iff (n := 2) hb (by omega),
    natCast_eq_ofNat_iff (n := 3) hb (by omega)]
  rcases b with _ | _ | _ | _ | b <;> simp

/-- **`IxonDeserialize::unpack_def_kind_safety`** on a byte `b < 256`. -/
theorem unpackDefKindSafety_run {b : Nat} (hb : b < 256) (k : Nat) (h : Heap F) :
    Mirrors.«IxonDeserialize::unpack_def_kind_safety» (k + 2) h (.field (b : F)) =
      match b with
      | 0 => some (.tuple [.construct "Ixon::DefKind" "Definition" [], .construct "Ixon::DefinitionSafety" "Unsafe" []], h)
      | 1 => some (.tuple [.construct "Ixon::DefKind" "Definition" [], .construct "Ixon::DefinitionSafety" "Safe" []], h)
      | 2 => some (.tuple [.construct "Ixon::DefKind" "Definition" [], .construct "Ixon::DefinitionSafety" "Partial" []], h)
      | 4 => some (.tuple [.construct "Ixon::DefKind" "Opaque" [], .construct "Ixon::DefinitionSafety" "Unsafe" []], h)
      | 5 => some (.tuple [.construct "Ixon::DefKind" "Opaque" [], .construct "Ixon::DefinitionSafety" "Safe" []], h)
      | 6 => some (.tuple [.construct "Ixon::DefKind" "Opaque" [], .construct "Ixon::DefinitionSafety" "Partial" []], h)
      | 8 => some (.tuple [.construct "Ixon::DefKind" "Theorem" [], .construct "Ixon::DefinitionSafety" "Unsafe" []], h)
      | 9 => some (.tuple [.construct "Ixon::DefKind" "Theorem" [], .construct "Ixon::DefinitionSafety" "Safe" []], h)
      | 10 => some (.tuple [.construct "Ixon::DefKind" "Theorem" [], .construct "Ixon::DefinitionSafety" "Partial" []], h)
      | _ => none := by
  simp only [Mirrors.«IxonDeserialize::unpack_def_kind_safety», Mirrors.«UInt8::to_field»,
    bind, Option.bind, Value.field.injEq,
    natCast_eq_zero_iff hb, natCast_eq_one_iff hb,
    natCast_eq_ofNat_iff (n := 2) hb (by omega),
    natCast_eq_ofNat_iff (n := 4) hb (by omega),
    natCast_eq_ofNat_iff (n := 5) hb (by omega),
    natCast_eq_ofNat_iff (n := 6) hb (by omega),
    natCast_eq_ofNat_iff (n := 8) hb (by omega),
    natCast_eq_ofNat_iff (n := 9) hb (by omega),
    natCast_eq_ofNat_iff (n := 10) hb (by omega)]
  rcases b with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | b <;> simp

/-- **`IxonDeserialize::get_lam_mode` on a non-empty byte stream** decodes a
4-bit binder contract when `b.toNat < 16` and rejects (`none`) when `b.toNat ≥ 16`. -/
theorem getLamMode_run {b : UInt8} {rest : List UInt8} {stream : SourceValue F} {h : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (b :: rest) stream) :
    ∃ restPtr, Aiur.Library.Bytes.RepByteStream byteStreamEnum h rest restPtr ∧
      ∀ k, Mirrors.«IxonDeserialize::get_lam_mode» (k + 3) h stream =
        if b.toNat < 16 then
          some (.tuple [
            .construct "Ixon::BinderContract" "Mk" [
              .construct "Ixon::Uses"
                (match b.toNat % 4 with
                  | 0 => "Erased" | 1 => "Linear" | 2 => "Affine" | _ => "Many") [],
              .construct "Ixon::ValueContract" "Mk" [
                .construct "Ixon::Owned" (if b.toNat / 4 % 2 = 0 then "Unique" else "Shared") [],
                .construct "Ixon::Locality" (if b.toNat / 8 % 2 = 0 then "Unrestricted" else "Local") []]],
            restPtr], h)
        else none := by
  obtain ⟨restPtr, tailRep, hread⟩ := readByte_run rep
  refine ⟨restPtr, tailRep, fun k => ?_⟩
  have hb := b.toNat_lt
  have hbits := bitDecomp_run hb (k + 1) h
  have hbc := binderContractFromBits_run (b0 := b.toNat % 2) (b1 := b.toNat / 2 % 2)
    (b2 := b.toNat / 4 % 2) (b3 := b.toNat / 8 % 2) (by omega) (by omega) (by omega) (by omega) k h
  rw [show b.toNat % 2 + 2 * (b.toNat / 2 % 2) = b.toNat % 4 by omega] at hbc
  by_cases hlt : b.toNat < 16
  · have hb4 : b.toNat / 16 % 2 = 0 := by omega
    have hb5 : b.toNat / 32 % 2 = 0 := by omega
    have hb6 : b.toNat / 64 % 2 = 0 := by omega
    have hb7 : b.toNat / 128 % 2 = 0 := by omega
    simp [Mirrors.«IxonDeserialize::get_lam_mode», hread (k + 1), hbits, hbc, hlt,
      hb4, hb5, hb6, hb7, evalBinOp, Builtin.apply, evalAssertEq, Value.pointerFree]
  · have he : b.toNat / 16 =
        b.toNat / 16 % 2 + 2 * (b.toNat / 32 % 2) + 4 * (b.toNat / 64 % 2) + 8 * (b.toNat / 128 % 2) := by omega
    have hsum_ne : (((b.toNat / 16 % 2 : Nat) : F) + ((b.toNat / 32 % 2 : Nat) : F) +
        ((b.toNat / 64 % 2 : Nat) : F) + ((b.toNat / 128 % 2 : Nat) : F)) ≠ 0 := by
      have hcast : (((b.toNat / 16 % 2 : Nat) : F) + ((b.toNat / 32 % 2 : Nat) : F) +
          ((b.toNat / 64 % 2 : Nat) : F) + ((b.toNat / 128 % 2 : Nat) : F)) =
          (((b.toNat / 16 % 2 + b.toNat / 32 % 2 + b.toNat / 64 % 2 + b.toNat / 128 % 2 : Nat)) : F) := by
        push_cast; ring
      rw [hcast]
      exact natCast_ne_of_ne (b := 0) (by omega) (by omega) (by omega)
    simp [Mirrors.«IxonDeserialize::get_lam_mode», hread (k + 1), hbits, hlt,
      evalBinOp, Builtin.apply, evalAssertEq, Value.pointerFree, hsum_ne]

/-- **`IxonDeserialize::get_all_mode` on a non-empty byte stream** decodes a
6-bit `(BinderContract, ValueContract)` pair when `b.toNat < 64` and rejects
(`none`) when `b.toNat ≥ 64`. -/
theorem getAllMode_run {b : UInt8} {rest : List UInt8} {stream : SourceValue F} {h : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (b :: rest) stream) :
    ∃ restPtr, Aiur.Library.Bytes.RepByteStream byteStreamEnum h rest restPtr ∧
      ∀ k, Mirrors.«IxonDeserialize::get_all_mode» (k + 3) h stream =
        if b.toNat < 64 then
          some (.tuple [
            .tuple [
              .construct "Ixon::BinderContract" "Mk" [
                .construct "Ixon::Uses"
                  (match b.toNat % 4 with
                    | 0 => "Erased" | 1 => "Linear" | 2 => "Affine" | _ => "Many") [],
                .construct "Ixon::ValueContract" "Mk" [
                  .construct "Ixon::Owned" (if b.toNat / 4 % 2 = 0 then "Unique" else "Shared") [],
                  .construct "Ixon::Locality" (if b.toNat / 8 % 2 = 0 then "Unrestricted" else "Local") []]],
              .construct "Ixon::ValueContract" "Mk" [
                .construct "Ixon::Owned" (if b.toNat / 16 % 2 = 0 then "Unique" else "Shared") [],
                .construct "Ixon::Locality" (if b.toNat / 32 % 2 = 0 then "Unrestricted" else "Local") []]],
            restPtr], h)
        else none := by
  obtain ⟨restPtr, tailRep, hread⟩ := readByte_run rep
  refine ⟨restPtr, tailRep, fun k => ?_⟩
  have hb := b.toNat_lt
  have hbits := bitDecomp_run hb (k + 1) h
  have hbc := binderContractFromBits_run (b0 := b.toNat % 2) (b1 := b.toNat / 2 % 2)
    (b2 := b.toNat / 4 % 2) (b3 := b.toNat / 8 % 2) (by omega) (by omega) (by omega) (by omega) k h
  rw [show b.toNat % 2 + 2 * (b.toNat / 2 % 2) = b.toNat % 4 by omega] at hbc
  have hvc := valueContractFromBits_run (b0 := b.toNat / 16 % 2) (b1 := b.toNat / 32 % 2)
    (by omega) (by omega) (k + 1) h
  by_cases hlt : b.toNat < 64
  · have hb6 : b.toNat / 64 % 2 = 0 := by omega
    have hb7 : b.toNat / 128 % 2 = 0 := by omega
    simp [Mirrors.«IxonDeserialize::get_all_mode», hread (k + 1), hbits, hbc, hvc, hlt,
      hb6, hb7, evalBinOp, Builtin.apply, evalAssertEq, Value.pointerFree]
  · have he : b.toNat / 64 = b.toNat / 64 % 2 + 2 * (b.toNat / 128 % 2) := by omega
    have hsum_ne : (((b.toNat / 64 % 2 : Nat) : F) + ((b.toNat / 128 % 2 : Nat) : F)) ≠ 0 := by
      have hcast : (((b.toNat / 64 % 2 : Nat) : F) + ((b.toNat / 128 % 2 : Nat) : F)) =
          (((b.toNat / 64 % 2 + b.toNat / 128 % 2 : Nat)) : F) := by
        push_cast; ring
      rw [hcast]
      exact natCast_ne_of_ne (b := 0) (by omega) (by omega) (by omega)
    simp [Mirrors.«IxonDeserialize::get_all_mode», hread (k + 1), hbits, hlt,
      evalBinOp, Builtin.apply, evalAssertEq, Value.pointerFree, hsum_ne]

/-- **Pure heap-allocating specification of `IxonDeserialize::build_succ_chain`.** -/
def buildSuccChainSpec (base : SourceValue F) : Nat → Heap F → SourceValue F × Heap F
  | 0, h => (base, h)
  | count + 1, h =>
    let (inner, h') := buildSuccChainSpec base count h
    (.construct "Ixon::Univ" "Succ" [.ptr inner.type h'.length], h' ++ [inner])

/-- **`IxonDeserialize::build_succ_chain` on `u64Value count`** computes
`buildSuccChainSpec base count h`. -/
theorem buildSuccChain_run (base : SourceValue F) {count : Nat}
    (hcount : count < 18446744073709551616) (k : Nat) (h : Heap F) :
    Mirrors.«IxonDeserialize::build_succ_chain» (k + count + 2) h base (u64Value count) =
      some (buildSuccChainSpec base count h) := by
  induction count generalizing k h with
  | zero =>
    simp [Mirrors.«IxonDeserialize::build_succ_chain», u64IsZero_run hcount (k + 0) h, buildSuccChainSpec]
  | succ count ih =>
    have hiz := u64IsZero_run hcount (k + count + 1) h
    have hsp := u64SaturatingPred_run hcount (k + count) h
    have hrec := ih (by omega) k h
    have h10 : (0 : F) ≠ 1 := by decide
    rw [show k + (count + 1) + 2 = (k + count + 2) + 1 by omega]
    unfold Mirrors.«IxonDeserialize::build_succ_chain»
    simp only [hiz, bind, Option.bind, Value.field.injEq, h10, ite_false, ite_true,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, hsp, Nat.add_sub_cancel, hrec,
      instanceName_plain_some, buildSuccChainSpec]

/-! ## `EvalFn` refinement theorems -/

/-- **Every terminating derivation of `IxonDeserialize::read_byte` on a valid
byte stream** requires the stream to be non-empty (`bytes = b :: rest`),
returns `(.tuple [.field (b.toNat : F), restPtr], h)`, and leaves the heap
unchanged. -/
theorem readByte_refines {bytes : List UInt8} {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h bytes stream)
    (ev : EvalFn W "IxonDeserialize::read_byte" [stream] h r h') :
    h' = h ∧ ∃ (b : UInt8) (rest : List UInt8) (restPtr : SourceValue F),
      bytes = b :: rest ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h rest restPtr ∧
      r = .tuple [.field (b.toNat : F), restPtr] := by
  obtain ⟨k0, hk0⟩ := Mirrors.«IxonDeserialize::read_byte».of_eval ev
  have run := hk0 (k0 + 1) (by omega)
  cases bytes with
  | nil =>
    rw [readByte_nil rep (k0 + 1)] at run
    cases run
  | cons b rest =>
    obtain ⟨restPtr, tailRep, hread⟩ := readByte_run rep
    rw [hread k0] at run
    simp only [Option.some.injEq, Prod.mk.injEq] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨rfl, b, rest, restPtr, rfl, tailRep, rfl⟩

/-- **Every terminating derivation of `IxonDeserialize::assert_wire_bool` on a
byte `< 256`** witnesses `b < 2`, returns `(.tuple [], h)`, and leaves the
heap unchanged. -/
theorem assertWireBool_refines {b : Nat} (hb : b < 256) {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn W "IxonDeserialize::assert_wire_bool" [.field (b : F)] h r h') :
    b < 2 ∧ r = .tuple [] ∧ h' = h := by
  obtain ⟨k0, hk0⟩ := Mirrors.«IxonDeserialize::assert_wire_bool».of_eval ev
  have run := hk0 (k0 + 3) (by omega)
  rw [assertWireBool_run hb k0 h] at run
  by_cases hlt : b < 2
  · simp only [hlt, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at run
    exact ⟨hlt, run.1.symm, run.2.symm⟩
  · simp [hlt] at run

/-- **Every terminating derivation of `IxonDeserialize::get_quot_kind` on a
byte `< 256`** witnesses `b < 4`, returns the matching `Ixon::QuotKind`
constructor, and leaves the heap unchanged. -/
theorem getQuotKind_refines {b : Nat} (hb : b < 256) {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn W "IxonDeserialize::get_quot_kind" [.field (b : F)] h r h') :
    b < 4 ∧ h' = h ∧
      r = .construct "Ixon::QuotKind"
        (match b with | 0 => "Typ" | 1 => "Ctor" | 2 => "Lift" | _ => "Ind") [] := by
  obtain ⟨k0, hk0⟩ := Mirrors.«IxonDeserialize::get_quot_kind».of_eval ev
  have run := hk0 (k0 + 2) (by omega)
  rw [getQuotKind_run hb k0 h] at run
  rcases b with _ | _ | _ | _ | b <;> simp at run
  all_goals {
    rcases run with ⟨rfl, rfl⟩
    exact ⟨by omega, rfl, rfl⟩
  }

/-- **Every terminating derivation of `IxonDeserialize::unpack_def_kind_safety`
on a byte `< 256`** witnesses `b / 4 < 3 ∧ b % 4 < 3` and returns the matching
`(DefKind, DefinitionSafety)` pair. -/
theorem unpackDefKindSafety_refines {b : Nat} (hb : b < 256) {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn W "IxonDeserialize::unpack_def_kind_safety" [.field (b : F)] h r h') :
    (b / 4 < 3 ∧ b % 4 < 3) ∧ h' = h ∧
      r = .tuple [
        .construct "Ixon::DefKind" (match b / 4 with | 0 => "Definition" | 1 => "Opaque" | _ => "Theorem") [],
        .construct "Ixon::DefinitionSafety" (match b % 4 with | 0 => "Unsafe" | 1 => "Safe" | _ => "Partial") []] := by
  obtain ⟨k0, hk0⟩ := Mirrors.«IxonDeserialize::unpack_def_kind_safety».of_eval ev
  have run := hk0 (k0 + 2) (by omega)
  rw [unpackDefKindSafety_run hb k0 h] at run
  rcases b with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | b <;> simp at run
  all_goals {
    rcases run with ⟨rfl, rfl⟩
    exact ⟨⟨by omega, by omega⟩, rfl, rfl⟩
  }

/-- **Every terminating derivation of `IxonDeserialize::get_lam_mode` on a
valid byte stream** requires `bytes = b :: rest` with `b.toNat < 16`, leaves
the heap unchanged, and returns the decoded `BinderContract` and tail stream. -/
theorem getLamMode_refines {bytes : List UInt8} {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h bytes stream)
    (ev : EvalFn W "IxonDeserialize::get_lam_mode" [stream] h r h') :
    h' = h ∧ ∃ (b : UInt8) (rest : List UInt8) (restPtr : SourceValue F),
      bytes = b :: rest ∧ b.toNat < 16 ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h rest restPtr ∧
      r = .tuple [
        .construct "Ixon::BinderContract" "Mk" [
          .construct "Ixon::Uses"
            (match b.toNat % 4 with
              | 0 => "Erased" | 1 => "Linear" | 2 => "Affine" | _ => "Many") [],
          .construct "Ixon::ValueContract" "Mk" [
            .construct "Ixon::Owned" (if b.toNat / 4 % 2 = 0 then "Unique" else "Shared") [],
            .construct "Ixon::Locality" (if b.toNat / 8 % 2 = 0 then "Unrestricted" else "Local") []]],
        restPtr] := by
  obtain ⟨k0, hk0⟩ := Mirrors.«IxonDeserialize::get_lam_mode».of_eval ev
  have run := hk0 (k0 + 3) (by omega)
  cases bytes with
  | nil =>
    simp [Mirrors.«IxonDeserialize::get_lam_mode», readByte_nil rep] at run
  | cons b rest =>
    obtain ⟨restPtr, tailRep, hmode⟩ := getLamMode_run rep
    rw [hmode k0] at run
    by_cases hlt : b.toNat < 16
    · simp only [hlt, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨rfl, b, rest, restPtr, rfl, hlt, tailRep, rfl⟩
    · simp [hlt] at run

/-- **Every terminating derivation of `IxonDeserialize::get_all_mode` on a
valid byte stream** requires `bytes = b :: rest` with `b.toNat < 64`, leaves
the heap unchanged, and returns the decoded `(BinderContract, ValueContract)`
pair and tail stream. -/
theorem getAllMode_refines {bytes : List UInt8} {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h bytes stream)
    (ev : EvalFn W "IxonDeserialize::get_all_mode" [stream] h r h') :
    h' = h ∧ ∃ (b : UInt8) (rest : List UInt8) (restPtr : SourceValue F),
      bytes = b :: rest ∧ b.toNat < 64 ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h rest restPtr ∧
      r = .tuple [
        .tuple [
          .construct "Ixon::BinderContract" "Mk" [
            .construct "Ixon::Uses"
              (match b.toNat % 4 with
                | 0 => "Erased" | 1 => "Linear" | 2 => "Affine" | _ => "Many") [],
            .construct "Ixon::ValueContract" "Mk" [
              .construct "Ixon::Owned" (if b.toNat / 4 % 2 = 0 then "Unique" else "Shared") [],
              .construct "Ixon::Locality" (if b.toNat / 8 % 2 = 0 then "Unrestricted" else "Local") []]],
          .construct "Ixon::ValueContract" "Mk" [
            .construct "Ixon::Owned" (if b.toNat / 16 % 2 = 0 then "Unique" else "Shared") [],
            .construct "Ixon::Locality" (if b.toNat / 32 % 2 = 0 then "Unrestricted" else "Local") []]],
        restPtr] := by
  obtain ⟨k0, hk0⟩ := Mirrors.«IxonDeserialize::get_all_mode».of_eval ev
  have run := hk0 (k0 + 3) (by omega)
  cases bytes with
  | nil =>
    simp [Mirrors.«IxonDeserialize::get_all_mode», readByte_nil rep] at run
  | cons b rest =>
    obtain ⟨restPtr, tailRep, hmode⟩ := getAllMode_run rep
    rw [hmode k0] at run
    by_cases hlt : b.toNat < 64
    · simp only [hlt, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨rfl, b, rest, restPtr, rfl, hlt, tailRep, rfl⟩
    · simp [hlt] at run

/-- **Every terminating derivation of `IxonDeserialize::build_succ_chain` on
`u64Value count`** computes `buildSuccChainSpec base count h`. -/
theorem buildSuccChain_refines (base : SourceValue F) {count : Nat}
    (hcount : count < 18446744073709551616) {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn W "IxonDeserialize::build_succ_chain" [base, u64Value count] h r h') :
    (r, h') = buildSuccChainSpec base count h := by
  obtain ⟨k0, hk0⟩ := buildSuccChain_complete ev
  have run := hk0 (k0 + count + 2) (by omega)
  rw [buildSuccChain_run base hcount k0 h] at run
  exact Option.some.inj run.symm

/-! ## `UInt32::less_than_fields` completeness -/

/-- The static map `UInt8::range_pair`. -/
def rangePairMap : Aiur.MapDecl := IxVM.coreTables.maps[2]'(by decide)

theorem find_rangePairMap :
    IxVM.coreTables.findMap? "UInt8::range_pair" = some rangePairMap := by
  decide +kernel

/-- **Any successful `UInt8::range_pair` map call** returns `.tuple []`, leaves
the heap unchanged, and witnesses that both inputs are bytes `< 256`. -/
theorem rangePair_mapCall_inv {v1 v2 w : SourceValue F} {h h' : Heap F}
    (hm : mapCall IxVM.source.tables "UInt8::range_pair" [v1, v2] h = some (w, h')) :
    w = .tuple [] ∧ h' = h ∧
      ∃ a b : Nat, a < 256 ∧ b < 256 ∧ v1 = .field (a : F) ∧ v2 = .field (b : F) := by
  unfold mapCall at hm
  cases looked : lookupMap IxVM.source.tables "UInt8::range_pair" [v1, v2] with
  | error _ => simp [looked] at hm
  | ok row =>
    simp only [looked, Option.some.injEq, Prod.mk.injEq] at hm
    rcases hm with ⟨hrow, rfl⟩
    subst hrow
    obtain ⟨map, key, found, -, -, extracted, mem, -⟩ := Aiur.lookupMap_spec looked
    change IxVM.coreTables.findMap? "UInt8::range_pair" = some map at found
    rw [find_rangePairMap, Option.some.injEq] at found
    subst found
    have rows : IxVM.coreTables.mapRows rangePairMap =
        IxVM.pairInputsTTable.rows.zip IxVM.pairUnitsTable.rows := by
      simp only [Aiur.Program.mapRows, show rangePairMap.input = "UInt8::pair_inputs" from rfl,
        show rangePairMap.output = "UInt8::pair_units" from rfl, IxVM.find_pairInputsT,
        IxVM.find_pairUnits]
    change (key, row) ∈ IxVM.coreTables.mapRows rangePairMap at mem
    rw [rows] at mem
    simp only [IxVM.pairInputsTTable, IxVM.pairUnitsTable, List.map_map] at mem
    obtain ⟨p, hp, hkr⟩ := mem_zip_map_iff.mp mem
    rcases p with ⟨a, b⟩
    simp only [IxVM.pairInputs, List.mem_flatMap, List.mem_map, List.mem_range,
      Prod.mk.injEq] at hp
    obtain ⟨a, ha, b, hb, rfl, rfl⟩ := hp
    simp only [Function.comp, IxVM.coreRow, IxVM.coreLeaf, List.map,
      Prod.mk.injEq] at hkr
    rcases hkr with ⟨rfl, rfl⟩
    have hv := Aiur.Value.toConstant_spec extracted
    simp only [Constant.toValue, Value.mapAddress, List.map, Value.tuple.injEq,
      List.cons.injEq, and_true] at hv
    rcases hv with ⟨rfl, rfl⟩
    exact ⟨by simp [Constant.toValue, Value.mapAddress], rfl, a, b, ha, hb, rfl, rfl⟩

theorem u8FromFields_eval_inv {x_a x_b r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn W "UInt8::from_fields" [x_a, x_b] h r h') :
    r = .tuple [x_a, x_b] ∧ h' = h ∧
      ∃ a b : Nat, a < 256 ∧ b < 256 ∧ x_a = .field (a : F) ∧ x_b = .field (b : F) := by
  obtain ⟨k0, hk0⟩ := Mirrors.«UInt8::from_fields».of_eval ev
  have run := hk0 (k0 + 1) (by omega)
  simp only [Mirrors.«UInt8::from_fields», bind, Option.bind] at run
  cases hm : mapCall IxVM.source.tables "UInt8::range_pair" [x_a, x_b] h with
  | none => simp [hm] at run
  | some wh =>
    simp only [hm, Option.some.injEq, Prod.mk.injEq] at run
    rcases wh with ⟨w, h1⟩
    obtain ⟨_, rfl, a, b, ha, hb, rfl, rfl⟩ := rangePair_mapCall_inv hm
    exact ⟨run.1.symm, run.2.symm, a, b, ha, hb, rfl, rfl⟩

theorem u32FromFields_eval_inv {raw r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn W "UInt32::from_fields" [raw] h r h') :
    h' = h ∧ ∃ b0 b1 b2 b3 : Nat,
      b0 < 256 ∧ b1 < 256 ∧ b2 < 256 ∧ b3 < 256 ∧
      r = .tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F)] := by
  have body := ev.function_inv IxVM.UInt32.from_fields.lookup
    (by simp [IxVM.UInt32.from_fields, ControlLower.hasControl])
  simp only [IxVM.UInt32.from_fields] at body
  obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
  obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
  obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
  obtain ⟨_, d15, _⟩ := d13.index_inv
  obtain ⟨_, rfl⟩ := d15.var_inv
  obtain ⟨v16, vs17, m18, rfl, d19, args20⟩ := args14.cons_inv
  obtain ⟨_, d21, _⟩ := d19.index_inv
  obtain ⟨_, rfl⟩ := d21.var_inv
  obtain ⟨rfl, rfl⟩ := args20.nil_inv
  rw [instanceName_plain_some] at callee9
  obtain ⟨rfl, rfl, b0, b1, hb0, hb1, rfl, rfl⟩ := u8FromFields_eval_inv callee9
  obtain ⟨ys22, hp23, hl24, ml25⟩ := matchPattern_tuple_inv mt4
  rcases ys22 with _ | ⟨y26, _ | ⟨y27, _ | ⟨_, _⟩⟩⟩ <;> simp at hl24
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hp23
  rcases hp23 with ⟨rfl, rfl⟩
  simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at ml25
  subst ml25
  obtain ⟨v28, m29, bs30, d31, mt32, d33⟩ := d5.letValue_inv
  obtain ⟨vs34, m35, args36, callee37⟩ := d31.call_inv
  obtain ⟨v38, vs39, m40, rfl, d41, args42⟩ := args36.cons_inv
  obtain ⟨_, d43, _⟩ := d41.index_inv
  obtain ⟨_, rfl⟩ := d43.var_inv
  obtain ⟨v44, vs45, m46, rfl, d47, args48⟩ := args42.cons_inv
  obtain ⟨_, d49, _⟩ := d47.index_inv
  obtain ⟨_, rfl⟩ := d49.var_inv
  obtain ⟨rfl, rfl⟩ := args48.nil_inv
  rw [instanceName_plain_some] at callee37
  obtain ⟨rfl, rfl, b2, b3, hb2, hb3, rfl, rfl⟩ := u8FromFields_eval_inv callee37
  obtain ⟨ys50, hp51, hl52, ml53⟩ := matchPattern_tuple_inv mt32
  rcases ys50 with _ | ⟨y54, _ | ⟨y55, _ | ⟨_, _⟩⟩⟩ <;> simp at hl52
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hp51
  rcases hp51 with ⟨rfl, rfl⟩
  simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at ml53
  subst ml53
  obtain ⟨vs56, args57, rfl⟩ := d33.array_inv
  obtain ⟨v58, vs59, m60, rfl, d61, args62⟩ := args57.cons_inv
  obtain ⟨l63, rfl⟩ := d61.var_inv; simp at l63; subst l63
  obtain ⟨v64, vs65, m66, rfl, d67, args68⟩ := args62.cons_inv
  obtain ⟨l69, rfl⟩ := d67.var_inv; simp at l69; subst l69
  obtain ⟨v70, vs71, m72, rfl, d73, args74⟩ := args68.cons_inv
  obtain ⟨l75, rfl⟩ := d73.var_inv; simp at l75; subst l75
  obtain ⟨v76, vs77, m78, rfl, d79, args80⟩ := args74.cons_inv
  obtain ⟨l81, rfl⟩ := d79.var_inv; simp at l81; subst l81
  obtain ⟨rfl, rfl⟩ := args80.nil_inv
  exact ⟨rfl, b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl⟩

theorem u32Compact_eval_inv {b0 b1 b2 b3 : Nat} {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn W "UInt32::compact"
      [.tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F)]] h r h') :
    r = .field ((Aiur.Library.U32.pack b0 b1 b2 b3 : Nat) : F) ∧ h' = h := by
  obtain ⟨k0, hk0⟩ := Mirrors.«UInt32::compact».of_eval ev
  have run := hk0 (k0 + 2) (by omega)
  simp [Mirrors.«UInt32::compact», Mirrors.«UInt8::to_field», projectValue, evalBinOp] at run
  rcases run with ⟨rfl, rfl⟩
  refine ⟨?_, rfl⟩
  congr 1
  unfold Aiur.Library.U32.pack
  push_cast
  ring

theorem zmod_val_natCast_of_lt {n : Nat} (hn : n < 4294967296) :
    ((n : F)).val = n := by
  have hm : n < Aiur.Library.U32.Goldilocks.modulus := by
    unfold Aiur.Library.U32.Goldilocks.modulus; omega
  exact ZMod.val_natCast_of_lt hm

/-- **Every derivation of `UInt32::less_than_fields` is a run of its
specification mirror**, using `Aiur.Library.U32.compare_fields_sound`. -/
theorem u32LessThanFields_complete : Mirrors.«UInt32::less_than_fields».Complete := by
  intro x_a x_b h h' r ev
  have body := ev.function_inv IxVM.UInt32.less_than_fields.lookup
    (by simp [IxVM.UInt32.less_than_fields, ControlLower.hasControl])
  simp only [IxVM.UInt32.less_than_fields] at body
  obtain ⟨v_raw, m0, bs0, d_hint, mt0, d1⟩ := body.letValue_inv
  obtain ⟨_, _, d_key, _, _⟩ := d_hint.hint_inv
  obtain ⟨_, args_key, _⟩ := d_key.tuple_inv
  obtain ⟨_, _, _, _, d_ka, args_key1⟩ := args_key.cons_inv
  obtain ⟨_, rfl⟩ := d_ka.var_inv
  obtain ⟨_, _, _, _, d_kb, args_key2⟩ := args_key1.cons_inv
  obtain ⟨_, rfl⟩ := d_kb.var_inv
  obtain ⟨_, rfl⟩ := args_key2.nil_inv
  rw [matchPattern_bind] at mt0
  simp only [Except.ok.injEq, Option.some.injEq] at mt0
  subst mt0
  obtain ⟨v_left, m1, bs1, d_left, mt1, d2⟩ := d1.letValue_inv
  obtain ⟨_, _, args_l, call_l⟩ := d_left.call_inv
  obtain ⟨_, _, _, rfl, d_arg_l, nil_l⟩ := args_l.cons_inv
  obtain ⟨_, d_var_l, _⟩ := d_arg_l.project_inv
  obtain ⟨_, rfl⟩ := d_var_l.var_inv
  obtain ⟨rfl, rfl⟩ := nil_l.nil_inv
  rw [instanceName_plain_some] at call_l
  obtain ⟨rfl, a0, a1, a2, a3, ha0, ha1, ha2, ha3, rfl⟩ := u32FromFields_eval_inv call_l
  rw [matchPattern_bind] at mt1
  simp only [Except.ok.injEq, Option.some.injEq] at mt1
  subst mt1
  obtain ⟨v_diff, m2, bs2, d_diff, mt2, d3⟩ := d2.letValue_inv
  obtain ⟨_, _, args_d, call_d⟩ := d_diff.call_inv
  obtain ⟨_, _, _, rfl, d_arg_d, nil_d⟩ := args_d.cons_inv
  obtain ⟨_, d_var_d, _⟩ := d_arg_d.project_inv
  obtain ⟨_, rfl⟩ := d_var_d.var_inv
  obtain ⟨rfl, rfl⟩ := nil_d.nil_inv
  rw [instanceName_plain_some] at call_d
  obtain ⟨rfl, d0, d1_b, d2_b, d3_b, hd0, hd1, hd2, hd3, rfl⟩ := u32FromFields_eval_inv call_d
  rw [matchPattern_bind] at mt2
  simp only [Except.ok.injEq, Option.some.injEq] at mt2
  subst mt2
  obtain ⟨v_right, m3, bs3, d_right, mt3, d4⟩ := d3.letValue_inv
  obtain ⟨_, _, args_r, call_r⟩ := d_right.call_inv
  obtain ⟨_, _, _, rfl, d_arg_r, nil_r⟩ := args_r.cons_inv
  obtain ⟨_, d_var_r, _⟩ := d_arg_r.project_inv
  obtain ⟨_, rfl⟩ := d_var_r.var_inv
  obtain ⟨rfl, rfl⟩ := nil_r.nil_inv
  rw [instanceName_plain_some] at call_r
  obtain ⟨rfl, b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl⟩ := u32FromFields_eval_inv call_r
  rw [matchPattern_bind] at mt3
  simp only [Except.ok.injEq, Option.some.injEq] at mt3
  subst mt3
  obtain ⟨_, m4, bs4, d_eq_l, mt4, d5⟩ := d4.letValue_inv
  obtain ⟨vs_eq_l, args_eq_l, app_eq_l⟩ := d_eq_l.builtin_inv
  obtain ⟨v_el1, _, _, rfl, d_el1, args_el1⟩ := args_eq_l.cons_inv
  obtain ⟨l_el1, rfl⟩ := d_el1.var_inv; simp at l_el1; subst l_el1
  obtain ⟨v_el2, _, _, rfl, d_el2, nil_el⟩ := args_el1.cons_inv
  obtain ⟨_, _, args_cl, call_cl⟩ := d_el2.call_inv
  obtain ⟨_, _, _, rfl, d_var_cl, nil_cl⟩ := args_cl.cons_inv
  obtain ⟨l_cl, rfl⟩ := d_var_cl.var_inv; simp at l_cl; subst l_cl
  obtain ⟨rfl, rfl⟩ := nil_cl.nil_inv
  rw [instanceName_plain_some] at call_cl
  obtain ⟨rfl, rfl⟩ := u32Compact_eval_inv call_cl
  obtain ⟨rfl, rfl⟩ := nil_el.nil_inv
  simp only [Builtin.apply, evalAssertEq, Value.pointerFree, Bool.and_self,
    ↓reduceIte] at app_eq_l
  split_ifs at app_eq_l with h_pf_a h_xa
  subst h_xa
  rw [matchPattern_wildcard] at mt4
  simp only [Except.ok.injEq, Option.some.injEq] at mt4
  subst mt4
  obtain ⟨_, m5, bs5, d_eq_r, mt5, d6⟩ := d5.letValue_inv
  obtain ⟨vs_eq_r, args_eq_r, app_eq_r⟩ := d_eq_r.builtin_inv
  obtain ⟨v_er1, _, _, rfl, d_er1, args_er1⟩ := args_eq_r.cons_inv
  obtain ⟨l_er1, rfl⟩ := d_er1.var_inv; simp at l_er1; subst l_er1
  obtain ⟨v_er2, _, _, rfl, d_er2, nil_er⟩ := args_er1.cons_inv
  obtain ⟨_, _, args_cr, call_cr⟩ := d_er2.call_inv
  obtain ⟨_, _, _, rfl, d_var_cr, nil_cr⟩ := args_cr.cons_inv
  obtain ⟨l_cr, rfl⟩ := d_var_cr.var_inv; simp at l_cr; subst l_cr
  obtain ⟨rfl, rfl⟩ := nil_cr.nil_inv
  rw [instanceName_plain_some] at call_cr
  obtain ⟨rfl, rfl⟩ := u32Compact_eval_inv call_cr
  obtain ⟨rfl, rfl⟩ := nil_er.nil_inv
  simp only [Builtin.apply, evalAssertEq, Value.pointerFree, Bool.and_self,
    ↓reduceIte] at app_eq_r
  split_ifs at app_eq_r with h_pf_b h_xb
  subst h_xb
  rw [matchPattern_wildcard] at mt5
  simp only [Except.ok.injEq, Option.some.injEq] at mt5
  subst mt5
  obtain ⟨v_borrow, m6, bs6, d_borrow, mt6, d7⟩ := d6.letValue_inv
  obtain ⟨x_num, y_den, _, d_num, d_den, op_div⟩ := d_borrow.binary_inv
  obtain ⟨x_add, y_sub, _, d_add, d_sub, op_sub⟩ := d_num.binary_inv
  obtain ⟨x_cd, y_add, _, d_cd, d_b, op_add⟩ := d_add.binary_inv
  obtain ⟨_, _, args_cd, call_cd⟩ := d_cd.call_inv
  obtain ⟨_, _, _, rfl, d_var_cd, nil_cd⟩ := args_cd.cons_inv
  obtain ⟨l_cd, rfl⟩ := d_var_cd.var_inv; simp at l_cd; subst l_cd
  obtain ⟨rfl, rfl⟩ := nil_cd.nil_inv
  rw [instanceName_plain_some] at call_cd
  obtain ⟨rfl, rfl⟩ := u32Compact_eval_inv call_cd
  obtain ⟨l_b, rfl⟩ := d_b.var_inv; simp at l_b; subst l_b
  obtain ⟨l_a, rfl⟩ := d_sub.var_inv; simp at l_a; subst l_a
  obtain ⟨rfl, rfl⟩ := d_den.literal_inv
  simp only [evalBinOp, Except.ok.injEq] at op_add
  subst op_add
  simp only [evalBinOp, Except.ok.injEq] at op_sub
  subst op_sub
  have hden_ne : (4294967296 : F) ≠ 0 := by decide
  simp only [evalBinOp, hden_ne, ↓reduceIte, Except.ok.injEq] at op_div
  subst op_div
  rw [matchPattern_bind] at mt6
  simp only [Except.ok.injEq, Option.some.injEq] at mt6
  subst mt6
  obtain ⟨_, m7, bs7, d_eq_b, mt7, d8⟩ := d7.letValue_inv
  obtain ⟨_, args_eq_b, app_eq_b⟩ := d_eq_b.builtin_inv
  obtain ⟨_, _, _, rfl, d_mul_b, args_eb1⟩ := args_eq_b.cons_inv
  obtain ⟨_, _, _, d_b1, d_b2, op_mul_b⟩ := d_mul_b.binary_inv
  obtain ⟨l_b1, rfl⟩ := d_b1.var_inv; simp at l_b1; subst l_b1
  obtain ⟨_, _, _, d_b21, d_b22, op_sub_b⟩ := d_b2.binary_inv
  obtain ⟨l_b21, rfl⟩ := d_b21.var_inv; simp at l_b21; subst l_b21
  obtain ⟨rfl, rfl⟩ := d_b22.literal_inv
  simp only [evalBinOp, Except.ok.injEq] at op_sub_b
  subst op_sub_b
  simp only [evalBinOp, Except.ok.injEq] at op_mul_b
  subst op_mul_b
  obtain ⟨_, _, _, rfl, d_zero_b, nil_eb⟩ := args_eb1.cons_inv
  obtain ⟨rfl, rfl⟩ := d_zero_b.literal_inv
  obtain ⟨rfl, rfl⟩ := nil_eb.nil_inv
  simp only [Builtin.apply, evalAssertEq, Value.pointerFree, Value.field.injEq] at app_eq_b
  split_ifs at app_eq_b with _ h_valid
  rw [matchPattern_wildcard] at mt7
  simp only [Except.ok.injEq, Option.some.injEq] at mt7
  subst mt7
  obtain ⟨l_ret, rfl⟩ := d8.var_inv; simp at l_ret; subst l_ret
  have ha_lt := Aiur.Library.U32.pack_lt ha0 ha1 ha2 ha3
  have hb_lt := Aiur.Library.U32.pack_lt hb0 hb1 hb2 hb3
  have hd_lt := Aiur.Library.U32.pack_lt hd0 hd1 hd2 hd3
  have hbase_cast : ((Aiur.Library.U32.base : Nat) : F) = (4294967296 : F) := by
    unfold Aiur.Library.U32.base; norm_num
  have hvalid' :
      let borrow := (((Aiur.Library.U32.pack d0 d1_b d2_b d3_b : Nat) : F) +
        ((Aiur.Library.U32.pack b0 b1 b2 b3 : Nat) : F) -
        ((Aiur.Library.U32.pack a0 a1 a2 a3 : Nat) : F)) / (Aiur.Library.U32.base : F)
      borrow * (borrow - 1) = 0 := by
    rw [hbase_cast]; exact h_valid
  have hcmp := Aiur.Library.U32.compare_fields_sound
    Aiur.Library.U32.Goldilocks.compatible
    ((Aiur.Library.U32.pack a0 a1 a2 a3 : Nat) : F)
    ((Aiur.Library.U32.pack b0 b1 b2 b3 : Nat) : F)
    ha_lt hb_lt hd_lt rfl rfl hvalid'
  rw [hbase_cast] at hcmp
  have ha_val : ((Aiur.Library.U32.pack a0 a1 a2 a3 : Nat) : F).val =
      Aiur.Library.U32.pack a0 a1 a2 a3 :=
    zmod_val_natCast_of_lt (by unfold Aiur.Library.U32.base at ha_lt; omega)
  have hb_val : ((Aiur.Library.U32.pack b0 b1 b2 b3 : Nat) : F).val =
      Aiur.Library.U32.pack b0 b1 b2 b3 :=
    zmod_val_natCast_of_lt (by unfold Aiur.Library.U32.base at hb_lt; omega)
  refine ⟨1, fun k hk => ?_⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [Mirrors.«UInt32::less_than_fields», ha_val, hb_val]
  have ha_lt' : Aiur.Library.U32.pack a0 a1 a2 a3 < 4294967296 := ha_lt
  have hb_lt' : Aiur.Library.U32.pack b0 b1 b2 b3 < 4294967296 := hb_lt
  simp [ha_lt', hb_lt', hcmp]

/-! ## `IxonDeserialize::get_address`, `get_address_list`, and projection deserializers -/

/-- **Every derivation of `IxonDeserialize::get_address_list` is a run of its
mirror**, by strong induction on `u64BytesMeasure x_count`. -/
theorem getAddressList_complete : Mirrors.«IxonDeserialize::get_address_list».Complete := by
  suffices H : ∀ m, ∀ {x_stream x_count : SourceValue F} {h h' : Heap F} {r : SourceValue F},
      u64BytesMeasure x_count = m →
      EvalFn W "IxonDeserialize::get_address_list" [x_stream, x_count] h r h' →
      ∃ k0, ∀ k ≥ k0, Mirrors.«IxonDeserialize::get_address_list» k h x_stream x_count = some (r, h') by
    intro x_stream x_count h h' r ev
    exact H _ rfl ev
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro x_stream x_count h h' r hm ev
  have body := ev.function_inv IxVM.IxonDeserialize.get_address_list.lookup
    (by simp [IxVM.IxonDeserialize.get_address_list, ControlLower.hasControl])
  simp only [IxVM.IxonDeserialize.get_address_list] at body
  obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
  obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
  obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
  obtain ⟨l15, rfl⟩ := d13.var_inv
  simp at l15
  subst l15
  obtain ⟨rfl, rfl⟩ := args14.nil_inv
  rw [instanceName_plain_some] at callee9
  obtain ⟨k16, hk17⟩ := Mirrors.«UInt64::is_zero».of_eval callee9
  rw [matchPattern_bind] at mt4
  simp only [Except.ok.injEq, Option.some.injEq] at mt4
  subst mt4
  obtain ⟨v18, m19, bs20, body21, d22, sel23, d24⟩ := d5.matchValue_inv
  obtain ⟨l25, rfl⟩ := d22.var_inv
  simp at l25
  subst l25
  rcases selectArm_literal_inv sel23 with ⟨hc26, rfl, rfl⟩ | ⟨hc26, sel27⟩
  · obtain ⟨vs28, args29, rfl⟩ := d24.tuple_inv
    obtain ⟨v30, vs31, m32, rfl, d33, args34⟩ := args29.cons_inv
    obtain ⟨v35, m36, d37, rfl, rfl⟩ := d33.store_inv
    obtain ⟨vs38, args39, rfl⟩ := d37.construct_inv
    obtain ⟨rfl, rfl⟩ := args39.nil_inv
    obtain ⟨v40, vs41, m42, rfl, d43, args44⟩ := args34.cons_inv
    obtain ⟨l45, rfl⟩ := d43.var_inv
    simp at l45
    subst l45
    obtain ⟨rfl, rfl⟩ := args44.nil_inv
    refine ⟨k16 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp (config := { decide := true, maxSteps := 10000000 })
      [Mirrors.«IxonDeserialize::get_address_list», hk17 k' (by omega), hc26]
  · rcases selectArm_literal_inv sel27 with ⟨hc28, rfl, rfl⟩ | ⟨hc28, sel29⟩
    · obtain ⟨v30, m31, bs32, d33, mt34, d35⟩ := d24.letValue_inv
      obtain ⟨vs36, m37, args38, callee39⟩ := d33.call_inv
      obtain ⟨v40, vs41, m42, rfl, d43, args44⟩ := args38.cons_inv
      obtain ⟨l45, rfl⟩ := d43.var_inv
      simp at l45
      subst l45
      obtain ⟨rfl, rfl⟩ := args44.nil_inv
      rw [instanceName_plain_some] at callee39
      obtain ⟨k46, hk47⟩ := Mirrors.«IxonDeserialize::get_address».of_eval callee39
      obtain ⟨ys48, hp49, hl50, ml51⟩ := matchPattern_tuple_inv mt34
      rcases ys48 with _ | ⟨y52, _ | ⟨y53, _ | ⟨_, _⟩⟩⟩ <;> simp at hl50
      simp [matchListWith, matchPattern_bind, matchPattern_wildcard, bind, Except.bind, pure, Except.pure] at ml51
      subst ml51
      obtain ⟨v54, m55, bs56, d57, mt58, d59⟩ := d35.letValue_inv
      obtain ⟨vs60, m61, args62, callee63⟩ := d57.call_inv
      obtain ⟨v64, vs65, m66, rfl, d67, args68⟩ := args62.cons_inv
      obtain ⟨l69, rfl⟩ := d67.var_inv
      simp at l69
      subst l69
      obtain ⟨v70, vs71, m72, rfl, d73, args74⟩ := args68.cons_inv
      obtain ⟨vs75, m76, args77, callee78⟩ := d73.call_inv
      obtain ⟨v79, vs80, m81, rfl, d82, args83⟩ := args77.cons_inv
      obtain ⟨l84, rfl⟩ := d82.var_inv
      simp at l84
      subst l84
      obtain ⟨rfl, rfl⟩ := args83.nil_inv
      rw [instanceName_plain_some] at callee78
      obtain ⟨k85, hk86⟩ := Mirrors.«UInt64::saturating_pred».of_eval callee78
      obtain ⟨rfl, rfl⟩ := args74.nil_inv
      rw [instanceName_plain_some] at callee63
      have hdec : u64BytesMeasure v70 < m := hm ▸ u64BytesMeasure_dec (hc28 ▸ callee9) callee78
      obtain ⟨k87, hk88⟩ := ih (u64BytesMeasure v70) hdec rfl callee63
      obtain ⟨ys89, hp90, hl91, ml92⟩ := matchPattern_tuple_inv mt58
      rcases ys89 with _ | ⟨y93, _ | ⟨y94, _ | ⟨_, _⟩⟩⟩ <;> simp at hl91
      simp [matchListWith, matchPattern_bind, matchPattern_wildcard, bind, Except.bind, pure, Except.pure] at ml92
      subst ml92
      obtain ⟨vs95, args96, rfl⟩ := d59.tuple_inv
      obtain ⟨v97, vs98, m99, rfl, d100, args101⟩ := args96.cons_inv
      obtain ⟨v102, m103, d104, rfl, rfl⟩ := d100.store_inv
      obtain ⟨vs105, args106, rfl⟩ := d104.construct_inv
      obtain ⟨v107, vs108, m109, rfl, d110, args111⟩ := args106.cons_inv
      obtain ⟨l112, rfl⟩ := d110.var_inv
      simp at l112
      subst l112
      obtain ⟨v113, vs114, m115, rfl, d116, args117⟩ := args111.cons_inv
      obtain ⟨l118, rfl⟩ := d116.var_inv
      simp at l118
      subst l118
      obtain ⟨rfl, rfl⟩ := args117.nil_inv
      obtain ⟨v119, vs120, m121, rfl, d122, args123⟩ := args101.cons_inv
      obtain ⟨l124, rfl⟩ := d122.var_inv
      simp at l124
      subst l124
      obtain ⟨rfl, rfl⟩ := args123.nil_inv
      refine ⟨k16 + k46 + k85 + k87 + 1, fun k hk => ?_⟩
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp (config := { decide := true, maxSteps := 10000000 })
        [Mirrors.«IxonDeserialize::get_address_list», hk17 k' (by omega), hc26, hc28,
          hk47 k' (by omega), hp49, hk86 k' (by omega), hk88 k' (by omega), hp90]
    · simp [SourceSemantics.selectArm] at sel29

/-- **`readStreamBytes n` on a byte stream of length `≥ n`** returns the first
`n` bytes as field values and a stream pointer to `bytes.drop n`. -/
theorem readStreamBytes_run :
    ∀ (n : Nat) {bytes : List UInt8} {stream : SourceValue F} {h : Heap F},
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h bytes stream →
      n ≤ bytes.length →
      ∃ restPtr, Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop n) restPtr ∧
        readStreamBytes n h stream =
          some ((bytes.take n).map (fun b => (.field (b.toNat : F) : SourceValue F)), restPtr)
  | 0, _, stream, _, rep, _ => ⟨stream, rep, rfl⟩
  | n + 1, _, _, h, rep, hlen => by
    cases rep with
    | nil _ => simp at hlen
    | @cons b rest addr headVal tailPtr cell headRep tailRep =>
      simp only [Aiur.Library.RepU8] at headRep
      subst headRep
      simp only [List.length_cons, Nat.add_le_add_iff_right] at hlen
      obtain ⟨restPtr, dropRep, hread⟩ := readStreamBytes_run n tailRep hlen
      refine ⟨restPtr, dropRep, ?_⟩
      simp [readStreamBytes_succ, loadValue_cell cell, node_ctor, hread]

/-- **`readStreamBytes n` on a byte stream of length `< n`** returns `none`. -/
theorem readStreamBytes_short :
    ∀ (n : Nat) {bytes : List UInt8} {stream : SourceValue F} {h : Heap F},
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h bytes stream →
      bytes.length < n →
      readStreamBytes n h stream = none
  | 0, _, _, _, _, hlt => by omega
  | n + 1, _, _, h, rep, hlt => by
    cases rep with
    | nil cell =>
      simp [readStreamBytes_succ, loadValue_cell cell, node_ctor]
    | @cons b rest addr headVal tailPtr cell headRep tailRep =>
      simp only [Aiur.Library.RepU8] at headRep
      subst headRep
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hlt
      have hread := readStreamBytes_short n tailRep hlt
      simp [readStreamBytes_succ, loadValue_cell cell, node_ctor, hread]

/-- Canonical `Aiur.Ty` of a 32-byte `Bytes::Address` cell (`[UInt8::U8; 32]`). -/
abbrev addressTy : Aiur.Ty := .tuple (List.replicate 32 .field)

/-- Extract the 32-byte `Aiur.Library.Bytes.Address` (`Vector UInt8 32`) prefix
from a byte list of length `≥ 32`. -/
def takeAddress (bytes : List UInt8) (hlen : 32 ≤ bytes.length) : Aiur.Library.Bytes.Address :=
  ⟨(bytes.take 32).toArray, by simp [Nat.min_eq_left hlen]⟩

/-- **`IxonDeserialize::get_address` on a byte stream of length `≥ 32`** reads
the first 32 bytes into a newly heap-allocated `Address` cell (`RepAddressRef`)
and advances the stream by 32 bytes. -/
theorem getAddress_run {bytes : List UInt8} {stream : SourceValue F} {h : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h bytes stream)
    (hlen : 32 ≤ bytes.length) :
    ∃ addrPtr restPtr h',
      Heap.Extends h h' ∧
      Aiur.Library.Bytes.RepAddressRef addressTy h' (takeAddress bytes hlen) addrPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop 32) restPtr ∧
      ∀ k, Mirrors.«IxonDeserialize::get_address» (k + 1) h stream =
        some (.tuple [addrPtr, restPtr], h') := by
  obtain ⟨restPtr, dropRep, hread⟩ := readStreamBytes_run 32 rep hlen
  let v : SourceValue F := .tuple ((bytes.take 32).map (fun b => (.field (b.toNat : F) : SourceValue F)))
  have ext : Heap.Extends h (h ++ [v]) := Heap.Extends.snoc h v
  have hlen32 : (bytes.take 32).length = 32 := by simp [Nat.min_eq_left hlen]
  have htype : v.type = addressTy := by
    dsimp only [v]
    rw [Value.type]
    have hfield : (fun x : UInt8 => Value.type (Value.field (x.toNat : F) : SourceValue F)) = fun _ => .field := by
      funext x; rw [Value.type]
    rw [List.map_map, Function.comp_def, hfield, List.map_const', hlen32]
  have hrepAddr : Aiur.Library.Bytes.RepAddressRef addressTy (h ++ [v]) (takeAddress bytes hlen) (.ptr v.type h.length) := by
    refine ⟨h.length, v, congrArg (Value.ptr · h.length) htype, by simp, ?_⟩
    simp [Aiur.Library.Bytes.RepAddress, takeAddress, v]
  exact ⟨.ptr v.type h.length, restPtr, h ++ [v], ext, hrepAddr,
    Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext dropRep,
    fun k => by rw [Mirrors.«IxonDeserialize::get_address», hread]; rfl⟩

/-- **`IxonDeserialize::get_address` on a byte stream of length `< 32`** fails (`none`). -/
theorem getAddress_short {bytes : List UInt8} {stream : SourceValue F} {h : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h bytes stream)
    (hlt : bytes.length < 32) (k : Nat) :
    Mirrors.«IxonDeserialize::get_address» k h stream = none := by
  cases k with
  | zero => rfl
  | succ k =>
    rw [Mirrors.«IxonDeserialize::get_address», readStreamBytes_short 32 rep hlt]
    rfl

/-- **Every terminating derivation of `IxonDeserialize::get_address` on a
valid byte stream** requires `32 ≤ bytes.length`, extends the heap with a
32-byte `RepAddressRef` cell for `takeAddress bytes`, and returns a stream pointer
to `bytes.drop 32`. -/
theorem getAddress_refines {bytes : List UInt8} {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h bytes stream)
    (ev : EvalFn W "IxonDeserialize::get_address" [stream] h r h') :
    Heap.Extends h h' ∧
    ∃ (hlen : 32 ≤ bytes.length) (addrPtr restPtr : SourceValue F),
      r = .tuple [addrPtr, restPtr] ∧
      Aiur.Library.Bytes.RepAddressRef addressTy h' (takeAddress bytes hlen) addrPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop 32) restPtr := by
  obtain ⟨k0, hk0⟩ := Mirrors.«IxonDeserialize::get_address».of_eval ev
  have run := hk0 (k0 + 1) (by omega)
  by_cases hlen : 32 ≤ bytes.length
  · obtain ⟨addrPtr, restPtr, h1, ext, addrRep, dropRep, hrun⟩ := getAddress_run rep hlen
    rw [hrun k0] at run
    simp only [Option.some.injEq, Prod.mk.injEq] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨ext, hlen, addrPtr, restPtr, rfl, addrRep, dropRep⟩
  · rw [getAddress_short rep (by omega) (k0 + 1)] at run
    cases run

/-- **Every terminating derivation of `IxonDeserialize::get_definition_proj` on
a valid byte stream** reads a TagN0 index `t` followed by a 32-byte block
address and returns `Ixon::DefinitionProj::Mk(u64Value t.value.toNat, addrPtr)`
with the remaining stream. -/
theorem getDefinitionProj_refines {bytes : List UInt8} {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h bytes stream)
    (ev : EvalFn W "IxonDeserialize::get_definition_proj" [stream] h r h') :
    Heap.Extends h h' ∧
    ∃ (t : Ixon.TagN) (n : Nat) (hlen : 32 ≤ (bytes.drop n).length) (addrPtr restPtr : SourceValue F),
      Ixon.getTagN 0 (start bytes) = .ok t { idx := n, bytes := ⟨bytes.toArray⟩ } ∧
      t.flag = 0 ∧
      Aiur.Library.Bytes.RepAddressRef addressTy h' (takeAddress (bytes.drop n) hlen) addrPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' ((bytes.drop n).drop 32) restPtr ∧
      r = .tuple [.construct "Ixon::DefinitionProj" "Mk" [u64Value t.value.toNat, addrPtr], restPtr] := by
  have body := ev.function_inv IxVM.IxonDeserialize.get_definition_proj.lookup
    (by simp [IxVM.IxonDeserialize.get_definition_proj, ControlLower.hasControl])
  simp only [IxVM.IxonDeserialize.get_definition_proj] at body
  obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
  obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
  obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
  obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
  obtain ⟨rfl, rfl⟩ := args14.nil_inv
  rw [instanceName_plain_some] at callee9
  obtain ⟨rfl, t, n, restPtr1, hok, hflag, hrep1, rfl⟩ := getTagN0_refines rep callee9
  obtain ⟨ys18, hp19, hl20, ml21⟩ := matchPattern_tuple_inv mt4
  rcases ys18 with _ | ⟨y22, _ | ⟨y23, _ | ⟨_, _⟩⟩⟩ <;> simp at hl20
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hp19
  rcases hp19 with ⟨rfl, rfl⟩
  simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at ml21
  subst ml21
  obtain ⟨v24, m25, bs26, d27, mt28, d29⟩ := d5.letValue_inv
  obtain ⟨vs30, m31, args32, callee33⟩ := d27.call_inv
  obtain ⟨v34, vs35, m36, rfl, d37, args38⟩ := args32.cons_inv
  obtain ⟨l39, rfl⟩ := d37.var_inv; simp at l39; subst l39
  obtain ⟨rfl, rfl⟩ := args38.nil_inv
  rw [instanceName_plain_some] at callee33
  obtain ⟨ext, hlen, addrPtr, restPtr2, rfl, addrRep, dropRep⟩ := getAddress_refines hrep1 callee33
  obtain ⟨ys42, hp43, hl44, ml45⟩ := matchPattern_tuple_inv mt28
  rcases ys42 with _ | ⟨y46, _ | ⟨y47, _ | ⟨_, _⟩⟩⟩ <;> simp at hl44
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hp43
  rcases hp43 with ⟨rfl, rfl⟩
  simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at ml45
  subst ml45
  obtain ⟨vs48, args49, rfl⟩ := d29.tuple_inv
  obtain ⟨v50, vs51, m52, rfl, d53, args54⟩ := args49.cons_inv
  obtain ⟨vs55, args56, rfl⟩ := d53.construct_inv
  obtain ⟨v57, vs58, m59, rfl, d60, args61⟩ := args56.cons_inv
  obtain ⟨l62, rfl⟩ := d60.var_inv; simp at l62; subst l62
  obtain ⟨v63, vs64, m65, rfl, d66, args67⟩ := args61.cons_inv
  obtain ⟨l68, rfl⟩ := d66.var_inv; simp at l68; subst l68
  obtain ⟨rfl, rfl⟩ := args67.nil_inv
  obtain ⟨v69, vs70, m71, rfl, d72, args73⟩ := args54.cons_inv
  obtain ⟨l74, rfl⟩ := d72.var_inv; simp at l74; subst l74
  obtain ⟨rfl, rfl⟩ := args73.nil_inv
  exact ⟨ext, t, n, hlen, addrPtr, restPtr2, hok, hflag, addrRep, dropRep, rfl⟩

/-- **Every terminating derivation of `IxonDeserialize::get_inductive_proj` on
a valid byte stream** reads a TagN0 index `t` followed by a 32-byte block
address and returns `Ixon::InductiveProj::Mk(u64Value t.value.toNat, addrPtr)`
with the remaining stream. -/
theorem getInductiveProj_refines {bytes : List UInt8} {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h bytes stream)
    (ev : EvalFn W "IxonDeserialize::get_inductive_proj" [stream] h r h') :
    Heap.Extends h h' ∧
    ∃ (t : Ixon.TagN) (n : Nat) (hlen : 32 ≤ (bytes.drop n).length) (addrPtr restPtr : SourceValue F),
      Ixon.getTagN 0 (start bytes) = .ok t { idx := n, bytes := ⟨bytes.toArray⟩ } ∧
      t.flag = 0 ∧
      Aiur.Library.Bytes.RepAddressRef addressTy h' (takeAddress (bytes.drop n) hlen) addrPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' ((bytes.drop n).drop 32) restPtr ∧
      r = .tuple [.construct "Ixon::InductiveProj" "Mk" [u64Value t.value.toNat, addrPtr], restPtr] := by
  have body := ev.function_inv IxVM.IxonDeserialize.get_inductive_proj.lookup
    (by simp [IxVM.IxonDeserialize.get_inductive_proj, ControlLower.hasControl])
  simp only [IxVM.IxonDeserialize.get_inductive_proj] at body
  obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
  obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
  obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
  obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
  obtain ⟨rfl, rfl⟩ := args14.nil_inv
  rw [instanceName_plain_some] at callee9
  obtain ⟨rfl, t, n, restPtr1, hok, hflag, hrep1, rfl⟩ := getTagN0_refines rep callee9
  obtain ⟨ys18, hp19, hl20, ml21⟩ := matchPattern_tuple_inv mt4
  rcases ys18 with _ | ⟨y22, _ | ⟨y23, _ | ⟨_, _⟩⟩⟩ <;> simp at hl20
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hp19
  rcases hp19 with ⟨rfl, rfl⟩
  simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at ml21
  subst ml21
  obtain ⟨v24, m25, bs26, d27, mt28, d29⟩ := d5.letValue_inv
  obtain ⟨vs30, m31, args32, callee33⟩ := d27.call_inv
  obtain ⟨v34, vs35, m36, rfl, d37, args38⟩ := args32.cons_inv
  obtain ⟨l39, rfl⟩ := d37.var_inv; simp at l39; subst l39
  obtain ⟨rfl, rfl⟩ := args38.nil_inv
  rw [instanceName_plain_some] at callee33
  obtain ⟨ext, hlen, addrPtr, restPtr2, rfl, addrRep, dropRep⟩ := getAddress_refines hrep1 callee33
  obtain ⟨ys42, hp43, hl44, ml45⟩ := matchPattern_tuple_inv mt28
  rcases ys42 with _ | ⟨y46, _ | ⟨y47, _ | ⟨_, _⟩⟩⟩ <;> simp at hl44
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hp43
  rcases hp43 with ⟨rfl, rfl⟩
  simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at ml45
  subst ml45
  obtain ⟨vs48, args49, rfl⟩ := d29.tuple_inv
  obtain ⟨v50, vs51, m52, rfl, d53, args54⟩ := args49.cons_inv
  obtain ⟨vs55, args56, rfl⟩ := d53.construct_inv
  obtain ⟨v57, vs58, m59, rfl, d60, args61⟩ := args56.cons_inv
  obtain ⟨l62, rfl⟩ := d60.var_inv; simp at l62; subst l62
  obtain ⟨v63, vs64, m65, rfl, d66, args67⟩ := args61.cons_inv
  obtain ⟨l68, rfl⟩ := d66.var_inv; simp at l68; subst l68
  obtain ⟨rfl, rfl⟩ := args67.nil_inv
  obtain ⟨v69, vs70, m71, rfl, d72, args73⟩ := args54.cons_inv
  obtain ⟨l74, rfl⟩ := d72.var_inv; simp at l74; subst l74
  obtain ⟨rfl, rfl⟩ := args73.nil_inv
  exact ⟨ext, t, n, hlen, addrPtr, restPtr2, hok, hflag, addrRep, dropRep, rfl⟩

/-- **Every terminating derivation of `IxonDeserialize::get_recursor_proj` on
a valid byte stream** reads a TagN0 index `t` followed by a 32-byte block
address and returns `Ixon::RecursorProj::Mk(u64Value t.value.toNat, addrPtr)`
with the remaining stream. -/
theorem getRecursorProj_refines {bytes : List UInt8} {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h bytes stream)
    (ev : EvalFn W "IxonDeserialize::get_recursor_proj" [stream] h r h') :
    Heap.Extends h h' ∧
    ∃ (t : Ixon.TagN) (n : Nat) (hlen : 32 ≤ (bytes.drop n).length) (addrPtr restPtr : SourceValue F),
      Ixon.getTagN 0 (start bytes) = .ok t { idx := n, bytes := ⟨bytes.toArray⟩ } ∧
      t.flag = 0 ∧
      Aiur.Library.Bytes.RepAddressRef addressTy h' (takeAddress (bytes.drop n) hlen) addrPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' ((bytes.drop n).drop 32) restPtr ∧
      r = .tuple [.construct "Ixon::RecursorProj" "Mk" [u64Value t.value.toNat, addrPtr], restPtr] := by
  have body := ev.function_inv IxVM.IxonDeserialize.get_recursor_proj.lookup
    (by simp [IxVM.IxonDeserialize.get_recursor_proj, ControlLower.hasControl])
  simp only [IxVM.IxonDeserialize.get_recursor_proj] at body
  obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
  obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
  obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
  obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
  obtain ⟨rfl, rfl⟩ := args14.nil_inv
  rw [instanceName_plain_some] at callee9
  obtain ⟨rfl, t, n, restPtr1, hok, hflag, hrep1, rfl⟩ := getTagN0_refines rep callee9
  obtain ⟨ys18, hp19, hl20, ml21⟩ := matchPattern_tuple_inv mt4
  rcases ys18 with _ | ⟨y22, _ | ⟨y23, _ | ⟨_, _⟩⟩⟩ <;> simp at hl20
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hp19
  rcases hp19 with ⟨rfl, rfl⟩
  simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at ml21
  subst ml21
  obtain ⟨v24, m25, bs26, d27, mt28, d29⟩ := d5.letValue_inv
  obtain ⟨vs30, m31, args32, callee33⟩ := d27.call_inv
  obtain ⟨v34, vs35, m36, rfl, d37, args38⟩ := args32.cons_inv
  obtain ⟨l39, rfl⟩ := d37.var_inv; simp at l39; subst l39
  obtain ⟨rfl, rfl⟩ := args38.nil_inv
  rw [instanceName_plain_some] at callee33
  obtain ⟨ext, hlen, addrPtr, restPtr2, rfl, addrRep, dropRep⟩ := getAddress_refines hrep1 callee33
  obtain ⟨ys42, hp43, hl44, ml45⟩ := matchPattern_tuple_inv mt28
  rcases ys42 with _ | ⟨y46, _ | ⟨y47, _ | ⟨_, _⟩⟩⟩ <;> simp at hl44
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hp43
  rcases hp43 with ⟨rfl, rfl⟩
  simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at ml45
  subst ml45
  obtain ⟨vs48, args49, rfl⟩ := d29.tuple_inv
  obtain ⟨v50, vs51, m52, rfl, d53, args54⟩ := args49.cons_inv
  obtain ⟨vs55, args56, rfl⟩ := d53.construct_inv
  obtain ⟨v57, vs58, m59, rfl, d60, args61⟩ := args56.cons_inv
  obtain ⟨l62, rfl⟩ := d60.var_inv; simp at l62; subst l62
  obtain ⟨v63, vs64, m65, rfl, d66, args67⟩ := args61.cons_inv
  obtain ⟨l68, rfl⟩ := d66.var_inv; simp at l68; subst l68
  obtain ⟨rfl, rfl⟩ := args67.nil_inv
  obtain ⟨v69, vs70, m71, rfl, d72, args73⟩ := args54.cons_inv
  obtain ⟨l74, rfl⟩ := d72.var_inv; simp at l74; subst l74
  obtain ⟨rfl, rfl⟩ := args73.nil_inv
  exact ⟨ext, t, n, hlen, addrPtr, restPtr2, hok, hflag, addrRep, dropRep, rfl⟩

/-- **Every terminating derivation of `IxonDeserialize::get_constructor_proj` on
a valid byte stream** reads two TagN0 indices `t1`, `t2` followed by a 32-byte
block address and returns
`Ixon::ConstructorProj::Mk(u64Value t1.value.toNat, u64Value t2.value.toNat, addrPtr)`
with the remaining stream. -/
theorem getConstructorProj_refines {bytes : List UInt8} {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h bytes stream)
    (ev : EvalFn W "IxonDeserialize::get_constructor_proj" [stream] h r h') :
    Heap.Extends h h' ∧
    ∃ (t1 t2 : Ixon.TagN) (n1 n2 : Nat) (hlen : 32 ≤ ((bytes.drop n1).drop n2).length) (addrPtr restPtr : SourceValue F),
      Ixon.getTagN 0 (start bytes) = .ok t1 { idx := n1, bytes := ⟨bytes.toArray⟩ } ∧
      t1.flag = 0 ∧
      Ixon.getTagN 0 (start (bytes.drop n1)) =
        .ok t2 { idx := n2, bytes := ⟨(bytes.drop n1).toArray⟩ } ∧
      t2.flag = 0 ∧
      Aiur.Library.Bytes.RepAddressRef addressTy h' (takeAddress ((bytes.drop n1).drop n2) hlen) addrPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (((bytes.drop n1).drop n2).drop 32) restPtr ∧
      r = .tuple [
        .construct "Ixon::ConstructorProj" "Mk"
          [u64Value t1.value.toNat, u64Value t2.value.toNat, addrPtr],
        restPtr] := by
  have body := ev.function_inv IxVM.IxonDeserialize.get_constructor_proj.lookup
    (by simp [IxVM.IxonDeserialize.get_constructor_proj, ControlLower.hasControl])
  simp only [IxVM.IxonDeserialize.get_constructor_proj] at body
  obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
  obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
  obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
  obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
  obtain ⟨rfl, rfl⟩ := args14.nil_inv
  rw [instanceName_plain_some] at callee9
  obtain ⟨rfl, t1, n1, restPtr1, hok1, hflag1, hrep1, rfl⟩ := getTagN0_refines rep callee9
  obtain ⟨ys18, hp19, hl20, ml21⟩ := matchPattern_tuple_inv mt4
  rcases ys18 with _ | ⟨y22, _ | ⟨y23, _ | ⟨_, _⟩⟩⟩ <;> simp at hl20
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hp19
  rcases hp19 with ⟨rfl, rfl⟩
  simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at ml21
  subst ml21
  obtain ⟨v24, m25, bs26, d27, mt28, d29⟩ := d5.letValue_inv
  obtain ⟨vs30, m31, args32, callee33⟩ := d27.call_inv
  obtain ⟨v34, vs35, m36, rfl, d37, args38⟩ := args32.cons_inv
  obtain ⟨l39, rfl⟩ := d37.var_inv; simp at l39; subst l39
  obtain ⟨rfl, rfl⟩ := args38.nil_inv
  rw [instanceName_plain_some] at callee33
  obtain ⟨rfl, t2, n2, restPtr2, hok2, hflag2, hrep2, rfl⟩ := getTagN0_refines hrep1 callee33
  obtain ⟨ys42, hp43, hl44, ml45⟩ := matchPattern_tuple_inv mt28
  rcases ys42 with _ | ⟨y46, _ | ⟨y47, _ | ⟨_, _⟩⟩⟩ <;> simp at hl44
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hp43
  rcases hp43 with ⟨rfl, rfl⟩
  simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at ml45
  subst ml45
  obtain ⟨v48, m49, bs50, d51, mt52, d53⟩ := d29.letValue_inv
  obtain ⟨vs54, m55, args56, callee57⟩ := d51.call_inv
  obtain ⟨v58, vs59, m60, rfl, d61, args62⟩ := args56.cons_inv
  obtain ⟨l63, rfl⟩ := d61.var_inv; simp at l63; subst l63
  obtain ⟨rfl, rfl⟩ := args62.nil_inv
  rw [instanceName_plain_some] at callee57
  obtain ⟨ext, hlen, addrPtr, restPtr3, rfl, addrRep, dropRep⟩ := getAddress_refines hrep2 callee57
  obtain ⟨ys66, hp67, hl68, ml69⟩ := matchPattern_tuple_inv mt52
  rcases ys66 with _ | ⟨y70, _ | ⟨y71, _ | ⟨_, _⟩⟩⟩ <;> simp at hl68
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hp67
  rcases hp67 with ⟨rfl, rfl⟩
  simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at ml69
  subst ml69
  obtain ⟨vs72, args73, rfl⟩ := d53.tuple_inv
  obtain ⟨v74, vs75, m76, rfl, d77, args78⟩ := args73.cons_inv
  obtain ⟨vs79, args80, rfl⟩ := d77.construct_inv
  obtain ⟨v81, vs82, m83, rfl, d84, args85⟩ := args80.cons_inv
  obtain ⟨l86, rfl⟩ := d84.var_inv; simp at l86; subst l86
  obtain ⟨v87, vs88, m89, rfl, d90, args91⟩ := args85.cons_inv
  obtain ⟨l92, rfl⟩ := d90.var_inv; simp at l92; subst l92
  obtain ⟨v93, vs94, m95, rfl, d96, args97⟩ := args91.cons_inv
  obtain ⟨l98, rfl⟩ := d96.var_inv; simp at l98; subst l98
  obtain ⟨rfl, rfl⟩ := args97.nil_inv
  obtain ⟨v99, vs100, m101, rfl, d102, args103⟩ := args78.cons_inv
  obtain ⟨l104, rfl⟩ := d102.var_inv; simp at l104; subst l104
  obtain ⟨rfl, rfl⟩ := args103.nil_inv
  exact ⟨ext, t1, t2, n1, n2, hlen, addrPtr, restPtr3, hok1, hflag1, hok2, hflag2, addrRep, dropRep, rfl⟩

/-! ## `IxonDeserialize::get_u64_list`, `get_address_list`, and `get_refs` refinements -/

/-- **Every terminating derivation of `UInt64::is_zero` on `u64Value n`**
returns `1` if `n = 0` and `0` otherwise, leaving the heap unchanged. -/
theorem u64IsZero_refines {n : Nat} (hn : n < 18446744073709551616) {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn W "UInt64::is_zero" [u64Value n] h r h') :
    r = .field (if n = 0 then 1 else 0) ∧ h' = h := by
  obtain ⟨k0, hk0⟩ := Mirrors.«UInt64::is_zero».of_eval ev
  have run := hk0 (k0 + 1) (by omega)
  rw [u64IsZero_run hn k0 h, Option.some.injEq, Prod.mk.injEq] at run
  exact ⟨run.1.symm, run.2.symm⟩

/-- **Every terminating derivation of `UInt64::saturating_pred` on `u64Value n`**
returns `u64Value (n - 1)` and leaves the heap unchanged. -/
theorem u64SaturatingPred_refines {n : Nat} (hn : n < 18446744073709551616) {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn W "UInt64::saturating_pred" [u64Value n] h r h') :
    r = u64Value (n - 1) ∧ h' = h := by
  obtain ⟨k0, hk0⟩ := Mirrors.«UInt64::saturating_pred».of_eval ev
  have run := hk0 (k0 + 2) (by omega)
  rw [u64SaturatingPred_run hn k0 h, Option.some.injEq, Prod.mk.injEq] at run
  exact ⟨run.1.symm, run.2.symm⟩

/-- `u64Value w.toNat` is the canonical `RepU64` representation of `w : UInt64`. -/
theorem repU64_u64Value (h : Heap F) (w : UInt64) :
    Aiur.Library.RepU64 h w (u64Value w.toNat) := by
  simp [Aiur.Library.RepU64, u64Value, List.range_succ]

/-- The prepared enum symbol for `Lists::Node<UInt64::U64>`. -/
abbrev u64ListEnum : String :=
  instanceName [] "Lists::Node" (some [(.array .field 8)])

/-- The prepared enum symbol for `Lists::Node<&Bytes::Address>`. -/
abbrev addressListEnum : String :=
  instanceName [] "Lists::Node" (some [(.ptr (.array .field 32))])

/-- **Every terminating derivation of `IxonDeserialize::get_u64_list` at reader
offset `i`** refines `Ixon.getTagN0Values count` at `i`, allocating a
`RepList u64ListEnum RepU64` of the decoded `UInt64`s and advancing the stream
pointer by the consumed bytes. -/
theorem getU64List_refines_at (count : Nat) (hcount : count < 18446744073709551616)
    {bytes : List UInt8} {i : Nat} {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : EvalFn W "IxonDeserialize::get_u64_list" [stream, u64Value count] h r h') :
    Heap.Extends h h' ∧
    ∃ (vals : List UInt64) (n : Nat) (listPtr restPtr : SourceValue F),
      Ixon.getTagN0Values count { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok vals { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      vals.length = count ∧
      r = .tuple [listPtr, restPtr] ∧
      Aiur.Library.List.RepList u64ListEnum Aiur.Library.RepU64 h' vals listPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  induction count generalizing i stream r h h' with
  | zero =>
    have body := ev.function_inv IxVM.IxonDeserialize.get_u64_list.lookup
      (by simp [IxVM.IxonDeserialize.get_u64_list, ControlLower.hasControl])
    simp only [IxVM.IxonDeserialize.get_u64_list] at body
    obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
    obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
    obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
    obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
    obtain ⟨rfl, rfl⟩ := args14.nil_inv
    rw [instanceName_plain_some] at callee9
    obtain ⟨hiz, rfl⟩ := u64IsZero_refines hcount callee9
    simp only [↓reduceIte] at hiz; subst hiz
    rw [matchPattern_bind] at mt4
    simp only [Except.ok.injEq, Option.some.injEq] at mt4; subst mt4
    obtain ⟨v18, m19, bs20, body21, d22, sel23, d24⟩ := d5.matchValue_inv
    obtain ⟨l25, rfl⟩ := d22.var_inv; simp at l25; subst l25
    rcases selectArm_literal_inv sel23 with ⟨_, rfl, rfl⟩ | ⟨hc26, _⟩
    · obtain ⟨vs28, args29, rfl⟩ := d24.tuple_inv
      obtain ⟨v30, vs31, m32, rfl, d33, args34⟩ := args29.cons_inv
      obtain ⟨v35, m36, d37, rfl, rfl⟩ := d33.store_inv
      obtain ⟨vs38, args39, rfl⟩ := d37.construct_inv
      obtain ⟨rfl, rfl⟩ := args39.nil_inv
      obtain ⟨v40, vs41, m42, rfl, d43, args44⟩ := args34.cons_inv
      obtain ⟨l45, rfl⟩ := d43.var_inv; simp at l45; subst l45
      obtain ⟨rfl, rfl⟩ := args44.nil_inv
      rw [value_type_construct]
      have ext := Aiur.Library.List.allocNil_extends u64ListEnum m36
      refine ⟨ext, [], 0, (Aiur.Library.List.allocNil u64ListEnum m36).1, stream,
        by simp [Ixon.getTagN0Values, pure, EStateM.pure], rfl, rfl,
        Aiur.Library.List.allocNil_rep u64ListEnum Aiur.Library.RepU64 m36,
        Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext rep⟩
    · exact (hc26 rfl).elim
  | succ count ih =>
    have body := ev.function_inv IxVM.IxonDeserialize.get_u64_list.lookup
      (by simp [IxVM.IxonDeserialize.get_u64_list, ControlLower.hasControl])
    simp only [IxVM.IxonDeserialize.get_u64_list] at body
    obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
    obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
    obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
    obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
    obtain ⟨rfl, rfl⟩ := args14.nil_inv
    rw [instanceName_plain_some] at callee9
    obtain ⟨hiz, rfl⟩ := u64IsZero_refines hcount callee9
    simp only [Nat.succ_ne_zero, ↓reduceIte] at hiz; subst hiz
    rw [matchPattern_bind] at mt4
    simp only [Except.ok.injEq, Option.some.injEq] at mt4; subst mt4
    obtain ⟨v18, m19, bs20, body21, d22, sel23, d24⟩ := d5.matchValue_inv
    obtain ⟨l25, rfl⟩ := d22.var_inv; simp at l25; subst l25
    rcases selectArm_literal_inv sel23 with ⟨hc26, _, _⟩ | ⟨_, sel27⟩
    · simp at hc26
    · rcases selectArm_literal_inv sel27 with ⟨_, rfl, rfl⟩ | ⟨hc28, _⟩
      · obtain ⟨v30, m31, bs32, d33, mt34, d35⟩ := d24.letValue_inv
        obtain ⟨vs36, m37, args38, callee39⟩ := d33.call_inv
        obtain ⟨v40, vs41, m42, rfl, d43, args44⟩ := args38.cons_inv
        obtain ⟨l45, rfl⟩ := d43.var_inv; simp at l45; subst l45
        obtain ⟨rfl, rfl⟩ := args44.nil_inv
        rw [instanceName_plain_some] at callee39
        obtain ⟨rfl, t, n1, restPtr1, hok1, _, hrep1, rfl⟩ := getTagN0_refines_at rep callee39
        obtain ⟨ys48, hp49, hl50, ml51⟩ := matchPattern_tuple_inv mt34
        rcases ys48 with _ | ⟨y52, _ | ⟨y53, _ | ⟨_, _⟩⟩⟩ <;> simp at hl50
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hp49
        rcases hp49 with ⟨rfl, rfl⟩
        simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at ml51
        subst ml51
        obtain ⟨v54, m55, bs56, d57, mt58, d59⟩ := d35.letValue_inv
        obtain ⟨vs60, m61, args62, callee63⟩ := d57.call_inv
        obtain ⟨v64, vs65, m66, rfl, d67, args68⟩ := args62.cons_inv
        obtain ⟨l69, rfl⟩ := d67.var_inv; simp at l69; subst l69
        obtain ⟨v70, vs71, m72, rfl, d73, args74⟩ := args68.cons_inv
        obtain ⟨vs75, m76, args77, callee78⟩ := d73.call_inv
        obtain ⟨v79, vs80, m81, rfl, d82, args83⟩ := args77.cons_inv
        obtain ⟨l84, rfl⟩ := d82.var_inv; simp at l84; subst l84
        obtain ⟨rfl, rfl⟩ := args83.nil_inv
        rw [instanceName_plain_some] at callee78
        obtain ⟨hsp, rfl⟩ := u64SaturatingPred_refines hcount callee78
        simp only [Nat.add_sub_cancel] at hsp; subst hsp
        obtain ⟨rfl, rfl⟩ := args74.nil_inv
        rw [instanceName_plain_some] at callee63
        obtain ⟨ext1, tailVals, n2, tailListPtr, restPtr2, hok2, hlen2, rfl, tailListRep, hrep2⟩ :=
          ih (by omega) hrep1 callee63
        obtain ⟨ys89, hp90, hl91, ml92⟩ := matchPattern_tuple_inv mt58
        rcases ys89 with _ | ⟨y93, _ | ⟨y94, _ | ⟨_, _⟩⟩⟩ <;> simp at hl91
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hp90
        rcases hp90 with ⟨rfl, rfl⟩
        simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at ml92
        subst ml92
        obtain ⟨vs95, args96, rfl⟩ := d59.tuple_inv
        obtain ⟨v97, vs98, m99, rfl, d100, args101⟩ := args96.cons_inv
        obtain ⟨v102, m103, d104, rfl, rfl⟩ := d100.store_inv
        obtain ⟨vs105, args106, rfl⟩ := d104.construct_inv
        obtain ⟨v107, vs108, m109, rfl, d110, args111⟩ := args106.cons_inv
        obtain ⟨l112, rfl⟩ := d110.var_inv; simp at l112; subst l112
        obtain ⟨v113, vs114, m115, rfl, d116, args117⟩ := args111.cons_inv
        obtain ⟨l118, rfl⟩ := d116.var_inv; simp at l118; subst l118
        obtain ⟨rfl, rfl⟩ := args117.nil_inv
        obtain ⟨v119, vs120, m121, rfl, d122, args123⟩ := args101.cons_inv
        obtain ⟨l124, rfl⟩ := d122.var_inv; simp at l124; subst l124
        obtain ⟨rfl, rfl⟩ := args123.nil_inv
        rw [value_type_construct]
        have ext2 := Aiur.Library.List.allocCons_extends u64ListEnum (u64Value t.value.toNat) tailListPtr m103
        refine ⟨ext1.trans ext2, t.value :: tailVals, n1 + n2,
          (Aiur.Library.List.allocCons u64ListEnum (u64Value t.value.toNat) tailListPtr m103).1, restPtr2,
          ?_, by simp [hlen2], rfl,
          Aiur.Library.List.allocCons_rep u64ListEnum Aiur.Library.repU64_heapMono₂
            (repU64_u64Value m103 t.value) tailListRep,
          by rw [← Nat.add_assoc]; exact Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext2 hrep2⟩
        simp [Ixon.getTagN0Values, bind, EStateM.bind, hok1, hok2, pure, EStateM.pure, Nat.add_assoc]
      · exact (hc28 rfl).elim

/-- **Every terminating derivation of `IxonDeserialize::get_u64_list` from the
start of `bytes`** refines `Ixon.getTagN0Values count (start bytes)`. -/
theorem getU64List_refines (count : Nat) (hcount : count < 18446744073709551616)
    {bytes : List UInt8} {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h bytes stream)
    (ev : EvalFn W "IxonDeserialize::get_u64_list" [stream, u64Value count] h r h') :
    Heap.Extends h h' ∧
    ∃ (vals : List UInt64) (n : Nat) (listPtr restPtr : SourceValue F),
      Ixon.getTagN0Values count (start bytes) =
        .ok vals { idx := n, bytes := ⟨bytes.toArray⟩ } ∧
      vals.length = count ∧
      r = .tuple [listPtr, restPtr] ∧
      Aiur.Library.List.RepList u64ListEnum Aiur.Library.RepU64 h' vals listPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop n) restPtr := by
  simpa [start] using getU64List_refines_at count hcount (i := 0) (by simpa using rep) ev

/-- **Every terminating derivation of `IxonDeserialize::get_address_list` on a
valid byte stream** requires `32 * count ≤ bytes.length`, allocates a
`RepList addressListEnum (RepAddressRef addressTy)` of `count` 32-byte
addresses, and advances the stream by `32 * count` bytes. -/
theorem getAddressList_refines (count : Nat) (hcount : count < 18446744073709551616)
    {bytes : List UInt8} {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h bytes stream)
    (ev : EvalFn W "IxonDeserialize::get_address_list" [stream, u64Value count] h r h') :
    Heap.Extends h h' ∧
    32 * count ≤ bytes.length ∧
    ∃ (addrs : List Aiur.Library.Bytes.Address) (listPtr restPtr : SourceValue F),
      addrs.length = count ∧
      r = .tuple [listPtr, restPtr] ∧
      Aiur.Library.List.RepList addressListEnum
        (Aiur.Library.Bytes.RepAddressRef addressTy) h' addrs listPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (32 * count)) restPtr := by
  induction count generalizing bytes stream r h h' with
  | zero =>
    have body := ev.function_inv IxVM.IxonDeserialize.get_address_list.lookup
      (by simp [IxVM.IxonDeserialize.get_address_list, ControlLower.hasControl])
    simp only [IxVM.IxonDeserialize.get_address_list] at body
    obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
    obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
    obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
    obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
    obtain ⟨rfl, rfl⟩ := args14.nil_inv
    rw [instanceName_plain_some] at callee9
    obtain ⟨hiz, rfl⟩ := u64IsZero_refines hcount callee9
    simp only [↓reduceIte] at hiz; subst hiz
    rw [matchPattern_bind] at mt4
    simp only [Except.ok.injEq, Option.some.injEq] at mt4; subst mt4
    obtain ⟨v18, m19, bs20, body21, d22, sel23, d24⟩ := d5.matchValue_inv
    obtain ⟨l25, rfl⟩ := d22.var_inv; simp at l25; subst l25
    rcases selectArm_literal_inv sel23 with ⟨_, rfl, rfl⟩ | ⟨hc26, _⟩
    · obtain ⟨vs28, args29, rfl⟩ := d24.tuple_inv
      obtain ⟨v30, vs31, m32, rfl, d33, args34⟩ := args29.cons_inv
      obtain ⟨v35, m36, d37, rfl, rfl⟩ := d33.store_inv
      obtain ⟨vs38, args39, rfl⟩ := d37.construct_inv
      obtain ⟨rfl, rfl⟩ := args39.nil_inv
      obtain ⟨v40, vs41, m42, rfl, d43, args44⟩ := args34.cons_inv
      obtain ⟨l45, rfl⟩ := d43.var_inv; simp at l45; subst l45
      obtain ⟨rfl, rfl⟩ := args44.nil_inv
      rw [value_type_construct]
      have ext := Aiur.Library.List.allocNil_extends addressListEnum m36
      refine ⟨ext, by omega, [], (Aiur.Library.List.allocNil addressListEnum m36).1, stream,
        rfl, rfl,
        Aiur.Library.List.allocNil_rep addressListEnum (Aiur.Library.Bytes.RepAddressRef addressTy) m36,
        Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext rep⟩
    · exact (hc26 rfl).elim
  | succ count ih =>
    have body := ev.function_inv IxVM.IxonDeserialize.get_address_list.lookup
      (by simp [IxVM.IxonDeserialize.get_address_list, ControlLower.hasControl])
    simp only [IxVM.IxonDeserialize.get_address_list] at body
    obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
    obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
    obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
    obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
    obtain ⟨rfl, rfl⟩ := args14.nil_inv
    rw [instanceName_plain_some] at callee9
    obtain ⟨hiz, rfl⟩ := u64IsZero_refines hcount callee9
    simp only [Nat.succ_ne_zero, ↓reduceIte] at hiz; subst hiz
    rw [matchPattern_bind] at mt4
    simp only [Except.ok.injEq, Option.some.injEq] at mt4; subst mt4
    obtain ⟨v18, m19, bs20, body21, d22, sel23, d24⟩ := d5.matchValue_inv
    obtain ⟨l25, rfl⟩ := d22.var_inv; simp at l25; subst l25
    rcases selectArm_literal_inv sel23 with ⟨hc26, _, _⟩ | ⟨_, sel27⟩
    · simp at hc26
    · rcases selectArm_literal_inv sel27 with ⟨_, rfl, rfl⟩ | ⟨hc28, _⟩
      · obtain ⟨v30, m31, bs32, d33, mt34, d35⟩ := d24.letValue_inv
        obtain ⟨vs36, m37, args38, callee39⟩ := d33.call_inv
        obtain ⟨v40, vs41, m42, rfl, d43, args44⟩ := args38.cons_inv
        obtain ⟨l45, rfl⟩ := d43.var_inv; simp at l45; subst l45
        obtain ⟨rfl, rfl⟩ := args44.nil_inv
        rw [instanceName_plain_some] at callee39
        obtain ⟨ext1, hlen1, addrPtr, restPtr1, rfl, addrRep, hrep1⟩ := getAddress_refines rep callee39
        obtain ⟨ys48, hp49, hl50, ml51⟩ := matchPattern_tuple_inv mt34
        rcases ys48 with _ | ⟨y52, _ | ⟨y53, _ | ⟨_, _⟩⟩⟩ <;> simp at hl50
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hp49
        rcases hp49 with ⟨rfl, rfl⟩
        simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at ml51
        subst ml51
        obtain ⟨v54, m55, bs56, d57, mt58, d59⟩ := d35.letValue_inv
        obtain ⟨vs60, m61, args62, callee63⟩ := d57.call_inv
        obtain ⟨v64, vs65, m66, rfl, d67, args68⟩ := args62.cons_inv
        obtain ⟨l69, rfl⟩ := d67.var_inv; simp at l69; subst l69
        obtain ⟨v70, vs71, m72, rfl, d73, args74⟩ := args68.cons_inv
        obtain ⟨vs75, m76, args77, callee78⟩ := d73.call_inv
        obtain ⟨v79, vs80, m81, rfl, d82, args83⟩ := args77.cons_inv
        obtain ⟨l84, rfl⟩ := d82.var_inv; simp at l84; subst l84
        obtain ⟨rfl, rfl⟩ := args83.nil_inv
        rw [instanceName_plain_some] at callee78
        obtain ⟨hsp, rfl⟩ := u64SaturatingPred_refines hcount callee78
        simp only [Nat.add_sub_cancel] at hsp; subst hsp
        obtain ⟨rfl, rfl⟩ := args74.nil_inv
        rw [instanceName_plain_some] at callee63
        obtain ⟨ext2, hlen2, tailAddrs, tailListPtr, restPtr2, hlenAddrs, rfl, tailListRep, hrep2⟩ :=
          ih (by omega) hrep1 callee63
        obtain ⟨ys89, hp90, hl91, ml92⟩ := matchPattern_tuple_inv mt58
        rcases ys89 with _ | ⟨y93, _ | ⟨y94, _ | ⟨_, _⟩⟩⟩ <;> simp at hl91
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hp90
        rcases hp90 with ⟨rfl, rfl⟩
        simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at ml92
        subst ml92
        obtain ⟨vs95, args96, rfl⟩ := d59.tuple_inv
        obtain ⟨v97, vs98, m99, rfl, d100, args101⟩ := args96.cons_inv
        obtain ⟨v102, m103, d104, rfl, rfl⟩ := d100.store_inv
        obtain ⟨vs105, args106, rfl⟩ := d104.construct_inv
        obtain ⟨v107, vs108, m109, rfl, d110, args111⟩ := args106.cons_inv
        obtain ⟨l112, rfl⟩ := d110.var_inv; simp at l112; subst l112
        obtain ⟨v113, vs114, m115, rfl, d116, args117⟩ := args111.cons_inv
        obtain ⟨l118, rfl⟩ := d116.var_inv; simp at l118; subst l118
        obtain ⟨rfl, rfl⟩ := args117.nil_inv
        obtain ⟨v119, vs120, m121, rfl, d122, args123⟩ := args101.cons_inv
        obtain ⟨l124, rfl⟩ := d122.var_inv; simp at l124; subst l124
        obtain ⟨rfl, rfl⟩ := args123.nil_inv
        rw [value_type_construct]
        have ext3 := Aiur.Library.List.allocCons_extends addressListEnum addrPtr tailListPtr m103
        have addrRep61 := Aiur.Library.Bytes.repAddressRef_heapMono₂ addressTy ext2 addrRep
        have hlenTotal : 32 * (count + 1) ≤ bytes.length := by
          simp only [List.length_drop] at hlen2
          omega
        have hdropTotal : (bytes.drop 32).drop (32 * count) = bytes.drop (32 * (count + 1)) := by
          rw [List.drop_drop, show 32 + 32 * count = 32 * (count + 1) by omega]
        rw [hdropTotal] at hrep2
        exact ⟨(ext1.trans ext2).trans ext3, hlenTotal, takeAddress bytes hlen1 :: tailAddrs,
          (Aiur.Library.List.allocCons addressListEnum addrPtr tailListPtr m103).1, restPtr2,
          by simp [hlenAddrs], rfl,
          Aiur.Library.List.allocCons_rep addressListEnum
            (Aiur.Library.Bytes.repAddressRef_heapMono₂ addressTy) addrRep61 tailListRep,
          Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext3 hrep2⟩
      · exact (hc28 rfl).elim

/-- **Every terminating derivation of `IxonDeserialize::get_refs` on a valid
byte stream** reads a TagN0 count `t` followed by `t.value.toNat` 32-byte
addresses into a `RepList addressListEnum (RepAddressRef addressTy)`. -/
theorem getRefs_refines {bytes : List UInt8} {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h bytes stream)
    (ev : EvalFn W "IxonDeserialize::get_refs" [stream] h r h') :
    Heap.Extends h h' ∧
    ∃ (t : Ixon.TagN) (n : Nat) (addrs : List Aiur.Library.Bytes.Address) (listPtr restPtr : SourceValue F),
      Ixon.getTagN 0 (start bytes) = .ok t { idx := n, bytes := ⟨bytes.toArray⟩ } ∧
      t.flag = 0 ∧
      32 * t.value.toNat ≤ (bytes.drop n).length ∧
      addrs.length = t.value.toNat ∧
      r = .tuple [listPtr, restPtr] ∧
      Aiur.Library.List.RepList addressListEnum
        (Aiur.Library.Bytes.RepAddressRef addressTy) h' addrs listPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' ((bytes.drop n).drop (32 * t.value.toNat)) restPtr := by
  have body := ev.function_inv IxVM.IxonDeserialize.get_refs.lookup
    (by simp [IxVM.IxonDeserialize.get_refs, ControlLower.hasControl])
  simp only [IxVM.IxonDeserialize.get_refs] at body
  obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
  obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
  obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
  obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
  obtain ⟨rfl, rfl⟩ := args14.nil_inv
  rw [instanceName_plain_some] at callee9
  obtain ⟨rfl, t, n, restPtr1, hok, hflag, hrep1, rfl⟩ := getTagN0_refines rep callee9
  obtain ⟨ys18, hp19, hl20, ml21⟩ := matchPattern_tuple_inv mt4
  rcases ys18 with _ | ⟨y22, _ | ⟨y23, _ | ⟨_, _⟩⟩⟩ <;> simp at hl20
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hp19
  rcases hp19 with ⟨rfl, rfl⟩
  simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at ml21
  subst ml21
  obtain ⟨vs24, m25, args26, callee27⟩ := d5.call_inv
  obtain ⟨v28, vs29, m30, rfl, d31, args32⟩ := args26.cons_inv
  obtain ⟨l33, rfl⟩ := d31.var_inv; simp at l33; subst l33
  obtain ⟨v34, vs35, m36, rfl, d37, args38⟩ := args32.cons_inv
  obtain ⟨l39, rfl⟩ := d37.var_inv; simp at l39; subst l39
  obtain ⟨rfl, rfl⟩ := args38.nil_inv
  rw [instanceName_plain_some] at callee27
  obtain ⟨ext, hlen, addrs, listPtr, restPtr2, hlenAddrs, rfl, listRep, dropRep⟩ :=
    getAddressList_refines t.value.toNat t.value.toNat_lt hrep1 callee27
  exact ⟨ext, t, n, addrs, listPtr, restPtr2, hok, hflag, hlen, hlenAddrs, rfl, listRep, dropRep⟩

/-! ## `getTag0_refines`, `getVecLen_refines`, and stream-progress helpers -/

/-- **`IxonDeserialize::get_tagn0` refines `Ixon.getTagN 0` at reader offset `i`.** -/
theorem getTag0_refines_at {stream r : SourceValue F} {heap h' : Heap F} {bytes : List UInt8}
    {i : Nat} (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum heap (bytes.drop i) stream)
    (ev : EvalFn W "IxonDeserialize::get_tagn0" [stream] heap r h') :
    h' = heap ∧ ∃ (t : Ixon.TagN) (n : Nat) (restPtr : SourceValue F),
      Ixon.getTagN 0 { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok t { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      t.flag = 0 ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum heap (bytes.drop (i + n)) restPtr ∧
      r = .tuple [u64Value t.value.toNat, restPtr] :=
  getTagN0_refines_at rep ev

/-- **`IxonDeserialize::get_tagn0` refines `Ixon.getTagN 0`** from the start of
`bytes`, returning `(u64Value t.value.toNat, restPtr)` with `t.flag = 0`. -/
theorem getTag0_refines {stream r : SourceValue F} {heap h' : Heap F} {bytes : List UInt8}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum heap bytes stream)
    (ev : EvalFn W "IxonDeserialize::get_tagn0" [stream] heap r h') :
    h' = heap ∧ ∃ (t : Ixon.TagN) (n : Nat) (restPtr : SourceValue F),
      Ixon.getTagN 0 (start bytes) = .ok t { idx := n, bytes := ⟨bytes.toArray⟩ } ∧
      t.flag = 0 ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum heap (bytes.drop n) restPtr ∧
      r = .tuple [u64Value t.value.toNat, restPtr] :=
  getTagN0_refines rep ev

/-- **`IxonDeserialize::get_tagn0` refines vector-length prefix decoding** at
reader offset `i`, returning the decoded count `t.value.toNat < 2^64` as
`u64Value t.value.toNat` together with the advanced stream pointer. -/
theorem getVecLen_refines_at {stream r : SourceValue F} {heap h' : Heap F} {bytes : List UInt8}
    {i : Nat} (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum heap (bytes.drop i) stream)
    (ev : EvalFn W "IxonDeserialize::get_tagn0" [stream] heap r h') :
    h' = heap ∧ ∃ (t : Ixon.TagN) (n : Nat) (restPtr : SourceValue F),
      Ixon.getTagN 0 { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok t { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      t.flag = 0 ∧
      t.value.toNat < 18446744073709551616 ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum heap (bytes.drop (i + n)) restPtr ∧
      r = .tuple [u64Value t.value.toNat, restPtr] := by
  obtain ⟨rfl, t, n, restPtr, hok, hflag, hrep, hr⟩ := getTagN0_refines_at rep ev
  exact ⟨rfl, t, n, restPtr, hok, hflag, t.value.toNat_lt, hrep, hr⟩

/-- **`IxonDeserialize::get_tagn0` refines vector-length prefix decoding** from
the start of `bytes`. -/
theorem getVecLen_refines {stream r : SourceValue F} {heap h' : Heap F} {bytes : List UInt8}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum heap bytes stream)
    (ev : EvalFn W "IxonDeserialize::get_tagn0" [stream] heap r h') :
    h' = heap ∧ ∃ (t : Ixon.TagN) (n : Nat) (restPtr : SourceValue F),
      Ixon.getTagN 0 (start bytes) = .ok t { idx := n, bytes := ⟨bytes.toArray⟩ } ∧
      t.flag = 0 ∧
      t.value.toNat < 18446744073709551616 ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum heap (bytes.drop n) restPtr ∧
      r = .tuple [u64Value t.value.toNat, restPtr] := by
  obtain ⟨rfl, t, n, restPtr, hok, hflag, hrep, hr⟩ := getTagN0_refines rep ev
  exact ⟨rfl, t, n, restPtr, hok, hflag, t.value.toNat_lt, hrep, hr⟩

theorem getTagNWide_pos {f : Nat} {flag : UInt8} {c : Nat} {bytes : List UInt8} {j n : Nat}
    {t : Ixon.TagN}
    (h : Ixon.getTagNWide f flag c { idx := j, bytes := ⟨bytes.toArray⟩ } =
      .ok t { idx := n, bytes := ⟨bytes.toArray⟩ }) :
    j < n := by
  have h' : Ixon.getTagNWide f flag c { idx := j, bytes := ⟨(bytes.drop 0).toArray⟩ } =
      .ok t { idx := n, bytes := ⟨(bytes.drop 0).toArray⟩ } := h
  unfold Ixon.getTagNWide at h'
  by_cases h0 : c = 0
  · rw [ite_eq_left h0] at h'
    obtain ⟨x, s1, hx, h'⟩ := Ixon.Verify.TagN.bind_ok_inv h'
    obtain ⟨rfl, hidx⟩ := Ixon.Verify.TagN.pure_ok_inv h'
    obtain ⟨hs1, _⟩ := getTrimmed_drop 2 hx
    rw [hs1] at hidx; cases hidx; omega
  rw [ite_eq_right h0] at h'
  by_cases h1 : c = 1
  · rw [ite_eq_left h1] at h'
    obtain ⟨x, s1, hx, h'⟩ := Ixon.Verify.TagN.bind_ok_inv h'
    obtain ⟨rfl, hidx⟩ := Ixon.Verify.TagN.pure_ok_inv h'
    obtain ⟨hs1, _⟩ := getTrimmed_drop 3 hx
    rw [hs1] at hidx; cases hidx; omega
  rw [ite_eq_right h1] at h'
  by_cases h2 : c = 2
  · rw [ite_eq_left h2] at h'
    obtain ⟨x, s1, hx, h'⟩ := Ixon.Verify.TagN.bind_ok_inv h'
    obtain ⟨rfl, hidx⟩ := Ixon.Verify.TagN.pure_ok_inv h'
    obtain ⟨hs1, _⟩ := getTrimmed_drop 4 hx
    rw [hs1] at hidx; cases hidx; omega
  rw [ite_eq_right h2] at h'
  by_cases h3 : c = 3
  · rw [ite_eq_left h3] at h'
    obtain ⟨x, s1, hx, h'⟩ := Ixon.Verify.TagN.bind_ok_inv h'
    obtain ⟨hs1, _⟩ := getTrimmed_drop 8 hx
    by_cases hlt : Ixon.tagNEnd5 f + x.toNat < 2 ^ 64
    · rw [ite_eq_left hlt] at h'
      obtain ⟨rfl, hidx⟩ := Ixon.Verify.TagN.pure_ok_inv h'
      rw [hs1] at hidx; cases hidx; omega
    · rw [ite_eq_right hlt] at h'
      exact (Ixon.Verify.TagN.throw_ok_false h').elim
  · rw [ite_eq_right h3] at h'
    exact (Ixon.Verify.TagN.throw_ok_false h').elim

/-- **Every successful `Ixon.getTagN` read consumes at least 1 byte** from a
non-empty buffer. -/
theorem getTagN_pos {f : Nat} {bytes : List UInt8} {n : Nat} {t : Ixon.TagN}
    (h : Ixon.getTagN f (start bytes) = .ok t { idx := n, bytes := ⟨bytes.toArray⟩ }) :
    0 < n ∧ 0 < bytes.length := by
  unfold start Ixon.getTagN at h
  obtain ⟨b, s1, hb, h⟩ := Ixon.Verify.TagN.bind_ok_inv h
  have hlen : 0 < bytes.length := by
    unfold Ixon.getU8 at hb
    change EStateM.bind EStateM.get _ _ = _ at hb
    simp only [EStateM.bind, EStateM.get] at hb
    split at hb
    · rename_i hlt; simpa [ByteArray.size] using hlt
    · cases hb
  obtain ⟨hs1, _⟩ := getU8_drop (i := 0) hb
  simp only [List.drop_zero, Nat.zero_add] at hs1
  subst hs1
  simp only at h
  by_cases h1 : b.toNat % 2 ^ (8 - f) < 2 ^ (8 - f - 1)
  · rw [ite_eq_left h1] at h
    obtain ⟨rfl, hidx⟩ := Ixon.Verify.TagN.pure_ok_inv h
    cases hidx
    exact ⟨by omega, hlen⟩
  rw [ite_eq_right h1] at h
  by_cases h2 : b.toNat % 2 ^ (8 - f) - 2 ^ (8 - f - 1) < 2 ^ (8 - f - 2)
  · rw [ite_eq_left h2] at h
    obtain ⟨lo, s2, hlo, h⟩ := Ixon.Verify.TagN.bind_ok_inv h
    obtain ⟨rfl, hidx⟩ := Ixon.Verify.TagN.pure_ok_inv h
    obtain ⟨hs2, _⟩ := getU8_drop (i := 0) hlo
    simp only [List.drop_zero] at hs2
    rw [hs2] at hidx
    cases hidx
    exact ⟨by omega, hlen⟩
  · rw [ite_eq_right h2] at h
    have hlt := getTagNWide_pos h
    exact ⟨by omega, hlen⟩

/-- **Dropping the `n` bytes consumed by `Ixon.getTagN` strictly decreases the
stream length.** -/
theorem drop_length_lt_of_getTagN {f : Nat} {bytes : List UInt8} {n : Nat} {t : Ixon.TagN}
    (h : Ixon.getTagN f (start bytes) = .ok t { idx := n, bytes := ⟨bytes.toArray⟩ }) :
    (bytes.drop n).length < bytes.length := by
  obtain ⟨hn, hlen⟩ := getTagN_pos h
  simp only [List.length_drop]
  omega

theorem matchPattern_tuple2_bind {types : Types} {heap : Heap F}
    {x y : String} {v v1 v2 : SourceValue F} {bs : Environment F Nat}
    (hv : v = .tuple [v1, v2])
    (mt : W.matchPattern types heap (.tuple [.bind x, .bind y]) v = .ok (some bs)) :
    bs = [(x, v1), (y, v2)] := by
  subst hv
  obtain ⟨ys, hp, hl, ml⟩ := matchPattern_tuple_inv mt
  rcases ys with _ | ⟨y1, _ | ⟨y2, _ | ⟨_, _⟩⟩⟩ <;> simp at hl
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hp
  rcases hp with ⟨rfl, rfl⟩
  simp only [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq, Option.some.injEq] at ml
  exact ml.symm

theorem evalExpr_assertEq_zero_one_false {types : Types} {locals : Environment F Nat}
    {msg : Option String} {rest : Generic.Expr F} {before after : Heap F} {result : SourceValue F}
    (ev : EvalExpr W types locals
      (.letValue .wildcard
        (.builtin (.assertEq { message := msg, runtimeCheck := true }) [(.literal 0), (.literal 1)])
        rest)
      before result after) : False := by
  obtain ⟨v0, m1, bs2, d3, _, _⟩ := ev.letValue_inv
  obtain ⟨vs4, args5, app6⟩ := d3.builtin_inv
  obtain ⟨v7, vs8, m9, rfl, d10, args11⟩ := args5.cons_inv
  obtain ⟨rfl, rfl⟩ := d10.literal_inv
  obtain ⟨v12, vs13, m14, rfl, d15, args16⟩ := args11.cons_inv
  obtain ⟨rfl, rfl⟩ := d15.literal_inv
  obtain ⟨rfl, rfl⟩ := args16.nil_inv
  simp [Builtin.apply, evalAssertEq, Value.pointerFree] at app6

theorem u8ToField_refines {x r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn W "UInt8::to_field" [x] h r h') :
    r = x ∧ h' = h := by
  obtain ⟨k0, hk0⟩ := Mirrors.«UInt8::to_field».of_eval ev
  have run := hk0 (k0 + 1) (by omega)
  rw [toField_run k0 h x, Option.some.injEq, Prod.mk.injEq] at run
  exact ⟨run.1.symm, run.2.symm⟩

theorem evalExpr_toField_var {types : Types} {locals : Environment F Nat}
    {name : String} {before after : Heap F} {result : SourceValue F}
    (ev : EvalExpr W types locals (.call "UInt8::to_field" (some []) [.var name]) before result after) :
    locals.find? (·.1 == name) = some (name, result) ∧ after = before := by
  obtain ⟨vs, m, args, callee⟩ := ev.call_inv
  obtain ⟨v, vs', m', rfl, d_var, args'⟩ := args.cons_inv
  obtain ⟨l, rfl⟩ := d_var.var_inv
  obtain ⟨rfl, rfl⟩ := args'.nil_inv
  rw [instanceName_plain_some] at callee
  obtain ⟨rfl, rfl⟩ := u8ToField_refines callee
  exact ⟨l, rfl⟩

theorem u8LessThan_refines {a b : Nat} (ha : a < 256) (hb : b < 256)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn W "UInt8::less_than" [.field (a : F), .field (b : F)] h r h') :
    r = .field ((if a < b then 1 else 0 : Nat) : F) ∧ h' = h := by
  obtain ⟨k0, hk0⟩ := Mirrors.«UInt8::less_than».of_eval ev
  have run := hk0 (k0 + 2) (by omega)
  rw [lessThan_run ha hb k0 h, Option.some.injEq, Prod.mk.injEq] at run
  exact ⟨run.1.symm, run.2.symm⟩

theorem u8BitDecomposition_refines {x : Nat} (hx : x < 256)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn W "UInt8::bit_decomposition" [.field (x : F)] h r h') :
    r = .tuple [.field ((x % 2 : Nat) : F), .field ((x / 2 % 2 : Nat) : F),
      .field ((x / 4 % 2 : Nat) : F), .field ((x / 8 % 2 : Nat) : F),
      .field ((x / 16 % 2 : Nat) : F), .field ((x / 32 % 2 : Nat) : F),
      .field ((x / 64 % 2 : Nat) : F), .field ((x / 128 % 2 : Nat) : F)] ∧ h' = h := by
  obtain ⟨k0, hk0⟩ := Mirrors.«UInt8::bit_decomposition».of_eval ev
  have run := hk0 (k0 + 1) (by omega)
  rw [bitDecomp_run hx k0 h, Option.some.injEq, Prod.mk.injEq] at run
  exact ⟨run.1.symm, run.2.symm⟩

theorem evalExpr_assert_u64_nonZero {types : Types} {locals : Environment F Nat}
    {sz : Nat} (hsz : sz < 18446744073709551616)
    (hlookup : locals.find? (·.1 == "size") = some ("size", u64Value sz))
    {msg : Option String} {rest : Generic.Expr F} {before after : Heap F} {result : SourceValue F}
    (ev : EvalExpr W types locals
      (.letValue .wildcard
        (.builtin (.assertEq { message := msg, runtimeCheck := true })
          [(.call "UInt64::is_zero" (some []) [(.var "size")]), (.literal 0)])
        rest)
      before result after) :
    sz ≠ 0 ∧ EvalExpr W types locals rest before result after := by
  obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := ev.letValue_inv
  obtain ⟨vs6, args7, app8⟩ := d3.builtin_inv
  obtain ⟨v9, vs10, m11, rfl, d12, args13⟩ := args7.cons_inv
  obtain ⟨vs14, m15, args16, callee17⟩ := d12.call_inv
  obtain ⟨v18, vs19, m20, rfl, d21, args22⟩ := args16.cons_inv
  obtain ⟨l23, rfl⟩ := d21.var_inv
  rw [hlookup, Option.some.injEq, Prod.mk.injEq] at l23
  rcases l23 with ⟨_, rfl⟩
  obtain ⟨rfl, rfl⟩ := args22.nil_inv
  rw [instanceName_plain_some] at callee17
  obtain ⟨rfl, rfl⟩ := u64IsZero_refines hsz callee17
  obtain ⟨v24, vs25, m26, rfl, d27, args28⟩ := args13.cons_inv
  obtain ⟨rfl, rfl⟩ := d27.literal_inv
  obtain ⟨rfl, rfl⟩ := args28.nil_inv
  have hne : sz ≠ 0 := by
    intro h0
    subst h0
    simp [Builtin.apply, evalAssertEq, Value.pointerFree] at app8
  rw [matchPattern_wildcard] at mt4
  simp only [Except.ok.injEq, Option.some.injEq] at mt4
  subst mt4
  exact ⟨hne, d5⟩

theorem evalExpr_store_unary_expr {types : Types} {locals : Environment F Nat}
    {ctor : String} {szVal sVal : SourceValue F}
    (hsz : locals.find? (·.1 == "size") = some ("size", szVal))
    (hs : locals.find? (·.1 == "s") = some ("s", sVal))
    {before after : Heap F} {result : SourceValue F}
    (ev : EvalExpr W types locals
      (.tuple [(.store (.construct "Ixon::Expr" (some []) ctor [(.var "size")])), (.var "s")])
      before result after) :
    let cell : SourceValue F := Value.construct (instanceName types "Ixon::Expr" (some [])) ctor [szVal]
    after = before ++ [cell] ∧
    result = .tuple [.ptr (.enum (instanceName types "Ixon::Expr" (some []))) before.length, sVal] := by
  obtain ⟨vs0, args1, rfl⟩ := ev.tuple_inv
  obtain ⟨v2, vs3, m4, rfl, d5, args6⟩ := args1.cons_inv
  obtain ⟨v7, m8, d9, rfl, rfl⟩ := d5.store_inv
  obtain ⟨vs10, args11, rfl⟩ := d9.construct_inv
  obtain ⟨v12, vs13, m14, rfl, d15, args16⟩ := args11.cons_inv
  obtain ⟨l17, rfl⟩ := d15.var_inv
  rw [hsz, Option.some.injEq, Prod.mk.injEq] at l17
  rcases l17 with ⟨_, rfl⟩
  obtain ⟨rfl, rfl⟩ := args16.nil_inv
  obtain ⟨v18, vs19, m20, rfl, d21, args22⟩ := args6.cons_inv
  obtain ⟨l23, rfl⟩ := d21.var_inv
  rw [hs, Option.some.injEq, Prod.mk.injEq] at l23
  rcases l23 with ⟨_, rfl⟩
  obtain ⟨rfl, rfl⟩ := args22.nil_inv
  rw [value_type_construct]
  exact ⟨rfl, rfl⟩

/-! ## Universe representation (`RepUniv`) and `deserializeUniv_refines` -/

/-- Canonical `SourceValue F` representation of an `Ixon.Univ` in `h : Heap F`.
Universe nodes are `Ixon::Univ` enum values whose recursive child fields
(`Succ`, `Max`, `IMax`) are heap pointers `.ptr (.enum "Ixon::Univ") addr`. -/
inductive RepUniv (h : Heap F) : Ixon.Univ → SourceValue F → Prop where
  | zero :
      RepUniv h .zero (.construct "Ixon::Univ" "Zero" [])
  | succ {u : Ixon.Univ} {addr : Nat} {v : SourceValue F}
      (cell : h[addr]? = some v)
      (innerRep : RepUniv h u v) :
      RepUniv h (.succ u) (.construct "Ixon::Univ" "Succ" [.ptr (.enum "Ixon::Univ") addr])
  | max {a b : Ixon.Univ} {addrA addrB : Nat} {va vb : SourceValue F}
      (cellA : h[addrA]? = some va)
      (cellB : h[addrB]? = some vb)
      (repA : RepUniv h a va)
      (repB : RepUniv h b vb) :
      RepUniv h (.max a b)
        (.construct "Ixon::Univ" "Max"
          [.ptr (.enum "Ixon::Univ") addrA, .ptr (.enum "Ixon::Univ") addrB])
  | imax {a b : Ixon.Univ} {addrA addrB : Nat} {va vb : SourceValue F}
      (cellA : h[addrA]? = some va)
      (cellB : h[addrB]? = some vb)
      (repA : RepUniv h a va)
      (repB : RepUniv h b vb) :
      RepUniv h (.imax a b)
        (.construct "Ixon::Univ" "IMax"
          [.ptr (.enum "Ixon::Univ") addrA, .ptr (.enum "Ixon::Univ") addrB])
  | var (idx : UInt64) :
      RepUniv h (.var idx) (.construct "Ixon::Univ" "Var" [u64Value idx.toNat])

theorem RepUniv.value_type {h : Heap F} {u : Ixon.Univ} {v : SourceValue F}
    (rep : RepUniv h u v) : v.type = .enum "Ixon::Univ" := by
  cases rep <;> simp [Value.type]

theorem RepUniv.mono {h₁ h₂ : Heap F} {u : Ixon.Univ} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepUniv h₁ u v) : RepUniv h₂ u v := by
  induction rep with
  | zero => exact .zero
  | succ cell _ ih => exact .succ (ext.getElem?_eq cell) ih
  | max cellA cellB _ _ ihA ihB =>
      exact .max (ext.getElem?_eq cellA) (ext.getElem?_eq cellB) ihA ihB
  | imax cellA cellB _ _ ihA ihB =>
      exact .imax (ext.getElem?_eq cellA) (ext.getElem?_eq cellB) ihA ihB
  | var idx => exact .var idx

theorem repUniv_heapMono₂ : HeapMono₂ RepUniv :=
  fun _ _ _ _ ext rep => rep.mono ext

theorem buildSuccChainSpec_extends (base : SourceValue F) (count : Nat) (h : Heap F) :
    Heap.Extends h (buildSuccChainSpec base count h).2 := by
  induction count with
  | zero => exact Heap.Extends.refl h
  | succ count ih =>
    dsimp only [buildSuccChainSpec]
    exact ih.trans (Heap.Extends.snoc _ _)

theorem buildSuccChainSpec_rep {base : SourceValue F} {u : Ixon.Univ} (count : Nat) {h : Heap F}
    (hrep : RepUniv h u base) :
    RepUniv (buildSuccChainSpec base count h).2 (u.addSucc count) (buildSuccChainSpec base count h).1 := by
  induction count with
  | zero => exact hrep
  | succ count ih =>
    dsimp only [buildSuccChainSpec, Ixon.Univ.addSucc]
    rw [ih.value_type]
    exact .succ (by simp) (ih.mono (Heap.Extends.snoc _ _))

/-- Canonical `SourceValue F` representation of a heap-allocated `&Ixon::Univ`
pointer (`(.ptr (.enum "Ixon::Univ") addr)` pointing to a `RepUniv` cell). -/
def RepUnivPtr (h : Heap F) (u : Ixon.Univ) (ptr : SourceValue F) : Prop :=
  ∃ addr v, ptr = .ptr (.enum "Ixon::Univ") addr ∧ h[addr]? = some v ∧ RepUniv h u v

theorem RepUnivPtr.mono {h₁ h₂ : Heap F} {u : Ixon.Univ} {ptr : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepUnivPtr h₁ u ptr) : RepUnivPtr h₂ u ptr := by
  rcases rep with ⟨addr, v, rfl, cell, uRep⟩
  exact ⟨addr, v, rfl, ext.getElem?_eq cell, uRep.mono ext⟩

theorem repUnivPtr_heapMono₂ : HeapMono₂ RepUnivPtr :=
  fun _ _ _ _ ext rep => rep.mono ext

/-- The prepared enum symbol for `Lists::Node<&Ixon::Univ>`. -/
abbrev univListEnum : String :=
  instanceName [] "Lists::Node" (some [(.ptr (.named "Ixon::Univ" []))])

/-- Read `count` universe levels in wire order using `Ixon.getUniv`. -/
def getUnivChildren : Nat → Ixon.GetM (List Ixon.Univ)
  | 0 => pure []
  | count + 1 => do
    let head ← Ixon.getUniv
    let tail ← getUnivChildren count
    return head :: tail

/-- **Every terminating derivation of `IxonDeserialize::get_univ` at reader
offset `i`** refines `Ixon.getUnivFuel fuel` for every `fuel > (bytes.drop i).length`,
extending the heap with a `RepUniv` value and advancing the stream by `n > 0`
bytes. -/
theorem deserializeUniv_refines_at {bytes : List UInt8} {i : Nat}
    {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : EvalFn W "IxonDeserialize::get_univ" [stream] h r h') :
    Heap.Extends h h' ∧
    ∃ (u : Ixon.Univ) (n : Nat) (uVal restPtr : SourceValue F),
      0 < n ∧
      (bytes.drop (i + n)).length < (bytes.drop i).length ∧
      (∀ fuel, (bytes.drop i).length < fuel →
        Ixon.getUnivFuel fuel { idx := i, bytes := ⟨bytes.toArray⟩ } =
          .ok u { idx := i + n, bytes := ⟨bytes.toArray⟩ }) ∧
      r = .tuple [uVal, restPtr] ∧
      RepUniv h' u uVal ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  suffices H : ∀ m, ∀ {i : Nat} {stream r : SourceValue F} {h h' : Heap F},
      (bytes.drop i).length = m →
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream →
      EvalFn W "IxonDeserialize::get_univ" [stream] h r h' →
      Heap.Extends h h' ∧
      ∃ (u : Ixon.Univ) (n : Nat) (uVal restPtr : SourceValue F),
        0 < n ∧
        (bytes.drop (i + n)).length < (bytes.drop i).length ∧
        (∀ fuel, (bytes.drop i).length < fuel →
          Ixon.getUnivFuel fuel { idx := i, bytes := ⟨bytes.toArray⟩ } =
            .ok u { idx := i + n, bytes := ⟨bytes.toArray⟩ }) ∧
        r = .tuple [uVal, restPtr] ∧
        RepUniv h' u uVal ∧
        Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr by
    exact H _ rfl rep ev
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro i stream r h h' hm rep ev
  have body := ev.function_inv IxVM.IxonDeserialize.get_univ.lookup
    (by simp [IxVM.IxonDeserialize.get_univ, ControlLower.hasControl])
  simp only [IxVM.IxonDeserialize.get_univ] at body
  obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
  obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
  obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
  obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
  obtain ⟨rfl, rfl⟩ := args14.nil_inv
  rw [instanceName_plain_some] at callee9
  obtain ⟨rfl, t, n1, restPtr1, hok_drop, hrep1, rfl⟩ := getTagN2_refines rep callee9
  have hok1 : Ixon.getTagN 2 { idx := i, bytes := ⟨bytes.toArray⟩ } =
      .ok t { idx := i + n1, bytes := ⟨bytes.toArray⟩ } := getTagN_drop hok_drop
  obtain ⟨hn1_pos, _⟩ := getTagN_pos hok_drop
  have hdrop_lt1 : (bytes.drop (i + n1)).length < (bytes.drop i).length := by
    rw [← List.drop_drop]
    exact drop_length_lt_of_getTagN hok_drop
  rw [List.drop_drop] at hrep1
  obtain rfl := matchPattern_tuple2_bind rfl mt4
  obtain ⟨v16, m17, bs18, d19, mt20, d21⟩ := d5.letValue_inv
  obtain ⟨l22, rfl⟩ := d19.var_inv; simp at l22; subst l22
  obtain rfl := matchPattern_tuple2_bind rfl mt20
  obtain ⟨v23, m24, bs25, body26, d27, sel28, d29⟩ := d21.matchValue_inv
  obtain ⟨l30, rfl⟩ := d27.var_inv; simp at l30; subst l30
  rcases selectArm_literal_inv sel28 with ⟨hc0, rfl, rfl⟩ | ⟨_, sel1⟩
  · have hflag0 : t.flag = 0 :=
      UInt8.ext ((natCast_eq_zero_iff t.flag.toNat_lt).mp (Value.field.inj hc0))
    obtain ⟨v31, m32, bs33, d34, mt35, d36⟩ := d29.letValue_inv
    obtain ⟨vs37, m38, args39, callee40⟩ := d34.call_inv
    obtain ⟨v41, vs42, m43, rfl, d44, args45⟩ := args39.cons_inv
    obtain ⟨l46, rfl⟩ := d44.var_inv; simp at l46; subst l46
    obtain ⟨rfl, rfl⟩ := args45.nil_inv
    rw [instanceName_plain_some] at callee40
    obtain ⟨rfl, rfl⟩ := u64IsZero_refines t.value.toNat_lt callee40
    rw [matchPattern_bind] at mt35
    simp only [Except.ok.injEq, Option.some.injEq] at mt35; subst mt35
    obtain ⟨v47, m48, bs49, body50, d51, sel52, d53⟩ := d36.matchValue_inv
    obtain ⟨l54, rfl⟩ := d51.var_inv; simp at l54; subst l54
    rcases selectArm_literal_inv sel52 with ⟨hiz1, rfl, rfl⟩ | ⟨_, sel53⟩
    · have hval0 : t.value = 0 := by
        apply UInt64.toNat_inj.mp
        by_contra hne
        simp [UInt64.toNat_zero] at hne
        simp [hne] at hiz1
      obtain ⟨vs55, args56, rfl⟩ := d53.tuple_inv
      obtain ⟨v57, vs58, m59, rfl, d60, args61⟩ := args56.cons_inv
      obtain ⟨vs62, args63, rfl⟩ := d60.construct_inv
      obtain ⟨rfl, rfl⟩ := args63.nil_inv
      obtain ⟨v64, vs65, m66, rfl, d67, args68⟩ := args61.cons_inv
      obtain ⟨l69, rfl⟩ := d67.var_inv; simp at l69; subst l69
      obtain ⟨rfl, rfl⟩ := args68.nil_inv
      refine ⟨Heap.Extends.refl h', .zero, n1, .construct "Ixon::Univ" "Zero" [], restPtr1,
        hn1_pos, hdrop_lt1, fun fuel hfuel => ?_, rfl, .zero, hrep1⟩
      obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
      simp [Ixon.getUnivFuel, Ixon.getUnivFromTag, hok1, hflag0, hval0,
        bind, EStateM.bind, pure, EStateM.pure]
    · rcases selectArm_literal_inv sel53 with ⟨hiz0, rfl, rfl⟩ | ⟨_, sel54⟩
      · have hval_ne : t.value ≠ 0 := by
          intro h0
          have h0' : t.value.toNat = 0 := congrArg UInt64.toNat h0
          simp [h0'] at hiz0
        obtain ⟨v55, m56, bs57, d58, mt59, d60⟩ := d53.letValue_inv
        obtain ⟨vs61, m62, args63, callee64⟩ := d58.call_inv
        obtain ⟨v65, vs66, m67, rfl, d68, args69⟩ := args63.cons_inv
        obtain ⟨l70, rfl⟩ := d68.var_inv; simp at l70; subst l70
        obtain ⟨rfl, rfl⟩ := args69.nil_inv
        rw [instanceName_plain_some] at callee64
        obtain ⟨ext1, base, n2, baseVal, restPtr2, hn2_pos, hdrop_lt2, hfuel_base, rfl, baseRep, hrep2⟩ :=
          ih _ (hm ▸ hdrop_lt1) rfl hrep1 callee64
        obtain rfl := matchPattern_tuple2_bind rfl mt59
        obtain ⟨vs71, args72, rfl⟩ := d60.tuple_inv
        obtain ⟨v73, vs74, m75, rfl, d76, args77⟩ := args72.cons_inv
        obtain ⟨vs78, m79, args80, callee81⟩ := d76.call_inv
        obtain ⟨v82, vs83, m84, rfl, d85, args86⟩ := args80.cons_inv
        obtain ⟨l87, rfl⟩ := d85.var_inv; simp at l87; subst l87
        obtain ⟨v88, vs89, m90, rfl, d91, args92⟩ := args86.cons_inv
        obtain ⟨l93, rfl⟩ := d91.var_inv; simp at l93; subst l93
        obtain ⟨rfl, rfl⟩ := args92.nil_inv
        rw [instanceName_plain_some] at callee81
        have hchain := buildSuccChain_refines baseVal t.value.toNat_lt callee81
        obtain ⟨v94, vs95, m96, rfl, d97, args98⟩ := args77.cons_inv
        obtain ⟨l99, rfl⟩ := d97.var_inv; simp at l99; subst l99
        obtain ⟨rfl, rfl⟩ := args98.nil_inv
        have hv73 : v73 = (buildSuccChainSpec baseVal t.value.toNat m79).1 := congrArg Prod.fst hchain
        have hh' : h' = (buildSuccChainSpec baseVal t.value.toNat m79).2 := congrArg Prod.snd hchain
        subst hv73 hh'
        have ext2 := buildSuccChainSpec_extends baseVal t.value.toNat m79
        rw [Nat.add_assoc] at hdrop_lt2 hrep2
        refine ⟨ext1.trans ext2, base.addSucc t.value.toNat, n1 + n2,
          (buildSuccChainSpec baseVal t.value.toNat m79).1, restPtr2,
          by omega, Nat.lt_trans hdrop_lt2 hdrop_lt1, fun fuel hfuel => ?_, rfl,
          buildSuccChainSpec_rep t.value.toNat baseRep,
          Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext2 hrep2⟩
        obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
        have hbase_ok := hfuel_base fuel' (by omega)
        rw [Nat.add_assoc] at hbase_ok
        simp [Ixon.getUnivFuel, Ixon.getUnivFromTag, hok1, hflag0, hval_ne, hbase_ok,
          bind, EStateM.bind, pure, EStateM.pure]
      · simp [SourceSemantics.selectArm] at sel54
  · rcases selectArm_literal_inv sel1 with ⟨hc1, rfl, rfl⟩ | ⟨_, sel2⟩
    · have hflag1 : t.flag = 1 :=
        UInt8.ext ((natCast_eq_one_iff t.flag.toNat_lt).mp (Value.field.inj hc1))
      obtain ⟨v31, m32, bs33, d34, mt35, d36⟩ := d29.letValue_inv
      obtain ⟨vs37, m38, args39, callee40⟩ := d34.call_inv
      obtain ⟨v41, vs42, m43, rfl, d44, args45⟩ := args39.cons_inv
      obtain ⟨l46, rfl⟩ := d44.var_inv; simp at l46; subst l46
      obtain ⟨rfl, rfl⟩ := args45.nil_inv
      rw [instanceName_plain_some] at callee40
      obtain ⟨ext1, a, n2, aVal, restPtr2, hn2_pos, hdrop_lt2, hfuel_a, rfl, repA, hrep2⟩ :=
        ih _ (hm ▸ hdrop_lt1) rfl hrep1 callee40
      obtain rfl := matchPattern_tuple2_bind rfl mt35
      obtain ⟨v47, m48, bs49, d50, mt51, d52⟩ := d36.letValue_inv
      obtain ⟨vs53, m54, args55, callee56⟩ := d50.call_inv
      obtain ⟨v57, vs58, m59, rfl, d60, args61⟩ := args55.cons_inv
      obtain ⟨l62, rfl⟩ := d60.var_inv; simp at l62; subst l62
      obtain ⟨rfl, rfl⟩ := args61.nil_inv
      rw [instanceName_plain_some] at callee56
      obtain ⟨ext2, b, n3, bVal, restPtr3, hn3_pos, hdrop_lt3, hfuel_b, rfl, repB, hrep3⟩ :=
        ih _ (hm ▸ Nat.lt_trans hdrop_lt2 hdrop_lt1) rfl hrep2 callee56
      obtain rfl := matchPattern_tuple2_bind rfl mt51
      obtain ⟨vs63, args64, rfl⟩ := d52.tuple_inv
      obtain ⟨v65, vs66, m67, rfl, d68, args69⟩ := args64.cons_inv
      obtain ⟨vs70, args71, rfl⟩ := d68.construct_inv
      obtain ⟨v72, vs73, m74, rfl, d75, args76⟩ := args71.cons_inv
      obtain ⟨v77, m78, d79, rfl, rfl⟩ := d75.store_inv
      obtain ⟨l80, rfl⟩ := d79.var_inv; simp at l80; subst l80
      obtain ⟨v81, vs82, m83, rfl, d84, args85⟩ := args76.cons_inv
      obtain ⟨v86, m87, d88, rfl, rfl⟩ := d84.store_inv
      obtain ⟨l89, rfl⟩ := d88.var_inv; simp at l89; subst l89
      obtain ⟨rfl, rfl⟩ := args85.nil_inv
      obtain ⟨v90, vs91, m92, rfl, d93, args94⟩ := args69.cons_inv
      obtain ⟨l95, rfl⟩ := d93.var_inv; simp at l95; subst l95
      obtain ⟨rfl, rfl⟩ := args94.nil_inv
      have ext_a := Heap.Extends.snoc m78 aVal
      have ext_b := Heap.Extends.snoc (m78 ++ [aVal]) bVal
      have cellA : ((m78 ++ [aVal]) ++ [bVal])[m78.length]? = some aVal :=
        ext_b.getElem?_eq (by simp)
      have cellB : ((m78 ++ [aVal]) ++ [bVal])[(m78 ++ [aVal]).length]? = some bVal := by simp
      have repA' := repA.mono ((ext2.trans ext_a).trans ext_b)
      have repB' := repB.mono (ext_a.trans ext_b)
      rw [repA.value_type, repB.value_type]
      have hdrop_total : (bytes.drop (i + (n1 + n2 + n3))).length < (bytes.drop i).length := by
        rw [show i + (n1 + n2 + n3) = i + n1 + n2 + n3 by omega]
        exact Nat.lt_trans hdrop_lt3 (Nat.lt_trans hdrop_lt2 hdrop_lt1)
      rw [show i + n1 + n2 + n3 = i + (n1 + n2 + n3) by omega] at hrep3
      refine ⟨((ext1.trans ext2).trans ext_a).trans ext_b, .max a b, n1 + n2 + n3,
        .construct "Ixon::Univ" "Max"
          [.ptr (.enum "Ixon::Univ") m78.length,
           .ptr (.enum "Ixon::Univ") (m78 ++ [aVal]).length],
        restPtr3, by omega, hdrop_total, fun fuel hfuel => ?_, rfl,
        .max cellA cellB repA' repB',
        Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum (ext_a.trans ext_b) hrep3⟩
      obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
      have ha_ok := hfuel_a fuel' (by omega)
      have hb_ok := hfuel_b fuel' (by omega)
      rw [show i + n1 + n2 + n3 = i + (n1 + n2 + n3) by omega] at hb_ok
      simp [Ixon.getUnivFuel, Ixon.getUnivFromTag, hok1, hflag1, ha_ok, hb_ok,
        bind, EStateM.bind, pure, EStateM.pure]
    · rcases selectArm_literal_inv sel2 with ⟨hc2, rfl, rfl⟩ | ⟨_, sel3⟩
      · have hflag2 : t.flag = 2 :=
          UInt8.ext ((natCast_eq_ofNat_iff (n := 2) t.flag.toNat_lt (by decide)).mp (Value.field.inj hc2))
        obtain ⟨v31, m32, bs33, d34, mt35, d36⟩ := d29.letValue_inv
        obtain ⟨vs37, m38, args39, callee40⟩ := d34.call_inv
        obtain ⟨v41, vs42, m43, rfl, d44, args45⟩ := args39.cons_inv
        obtain ⟨l46, rfl⟩ := d44.var_inv; simp at l46; subst l46
        obtain ⟨rfl, rfl⟩ := args45.nil_inv
        rw [instanceName_plain_some] at callee40
        obtain ⟨ext1, a, n2, aVal, restPtr2, hn2_pos, hdrop_lt2, hfuel_a, rfl, repA, hrep2⟩ :=
          ih _ (hm ▸ hdrop_lt1) rfl hrep1 callee40
        obtain rfl := matchPattern_tuple2_bind rfl mt35
        obtain ⟨v47, m48, bs49, d50, mt51, d52⟩ := d36.letValue_inv
        obtain ⟨vs53, m54, args55, callee56⟩ := d50.call_inv
        obtain ⟨v57, vs58, m59, rfl, d60, args61⟩ := args55.cons_inv
        obtain ⟨l62, rfl⟩ := d60.var_inv; simp at l62; subst l62
        obtain ⟨rfl, rfl⟩ := args61.nil_inv
        rw [instanceName_plain_some] at callee56
        obtain ⟨ext2, b, n3, bVal, restPtr3, hn3_pos, hdrop_lt3, hfuel_b, rfl, repB, hrep3⟩ :=
          ih _ (hm ▸ Nat.lt_trans hdrop_lt2 hdrop_lt1) rfl hrep2 callee56
        obtain rfl := matchPattern_tuple2_bind rfl mt51
        obtain ⟨vs63, args64, rfl⟩ := d52.tuple_inv
        obtain ⟨v65, vs66, m67, rfl, d68, args69⟩ := args64.cons_inv
        obtain ⟨vs70, args71, rfl⟩ := d68.construct_inv
        obtain ⟨v72, vs73, m74, rfl, d75, args76⟩ := args71.cons_inv
        obtain ⟨v77, m78, d79, rfl, rfl⟩ := d75.store_inv
        obtain ⟨l80, rfl⟩ := d79.var_inv; simp at l80; subst l80
        obtain ⟨v81, vs82, m83, rfl, d84, args85⟩ := args76.cons_inv
        obtain ⟨v86, m87, d88, rfl, rfl⟩ := d84.store_inv
        obtain ⟨l89, rfl⟩ := d88.var_inv; simp at l89; subst l89
        obtain ⟨rfl, rfl⟩ := args85.nil_inv
        obtain ⟨v90, vs91, m92, rfl, d93, args94⟩ := args69.cons_inv
        obtain ⟨l95, rfl⟩ := d93.var_inv; simp at l95; subst l95
        obtain ⟨rfl, rfl⟩ := args94.nil_inv
        have ext_a := Heap.Extends.snoc m78 aVal
        have ext_b := Heap.Extends.snoc (m78 ++ [aVal]) bVal
        have cellA : ((m78 ++ [aVal]) ++ [bVal])[m78.length]? = some aVal :=
          ext_b.getElem?_eq (by simp)
        have cellB : ((m78 ++ [aVal]) ++ [bVal])[(m78 ++ [aVal]).length]? = some bVal := by simp
        have repA' := repA.mono ((ext2.trans ext_a).trans ext_b)
        have repB' := repB.mono (ext_a.trans ext_b)
        rw [repA.value_type, repB.value_type]
        have hdrop_total : (bytes.drop (i + (n1 + n2 + n3))).length < (bytes.drop i).length := by
          rw [show i + (n1 + n2 + n3) = i + n1 + n2 + n3 by omega]
          exact Nat.lt_trans hdrop_lt3 (Nat.lt_trans hdrop_lt2 hdrop_lt1)
        rw [show i + n1 + n2 + n3 = i + (n1 + n2 + n3) by omega] at hrep3
        refine ⟨((ext1.trans ext2).trans ext_a).trans ext_b, .imax a b, n1 + n2 + n3,
          .construct "Ixon::Univ" "IMax"
            [.ptr (.enum "Ixon::Univ") m78.length,
             .ptr (.enum "Ixon::Univ") (m78 ++ [aVal]).length],
          restPtr3, by omega, hdrop_total, fun fuel hfuel => ?_, rfl,
          .imax cellA cellB repA' repB',
          Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum (ext_a.trans ext_b) hrep3⟩
        obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
        have ha_ok := hfuel_a fuel' (by omega)
        have hb_ok := hfuel_b fuel' (by omega)
        rw [show i + n1 + n2 + n3 = i + (n1 + n2 + n3) by omega] at hb_ok
        simp [Ixon.getUnivFuel, Ixon.getUnivFromTag, hok1, hflag2, ha_ok, hb_ok,
          bind, EStateM.bind, pure, EStateM.pure]
      · rcases selectArm_literal_inv sel3 with ⟨hc3, rfl, rfl⟩ | ⟨_, sel4⟩
        · have hflag3 : t.flag = 3 :=
            UInt8.ext ((natCast_eq_ofNat_iff (n := 3) t.flag.toNat_lt (by decide)).mp (Value.field.inj hc3))
          obtain ⟨vs31, args32, rfl⟩ := d29.tuple_inv
          obtain ⟨v33, vs34, m35, rfl, d36, args37⟩ := args32.cons_inv
          obtain ⟨vs38, args39, rfl⟩ := d36.construct_inv
          obtain ⟨v40, vs41, m42, rfl, d43, args44⟩ := args39.cons_inv
          obtain ⟨l45, rfl⟩ := d43.var_inv; simp at l45; subst l45
          obtain ⟨rfl, rfl⟩ := args44.nil_inv
          obtain ⟨v46, vs47, m48, rfl, d49, args50⟩ := args37.cons_inv
          obtain ⟨l51, rfl⟩ := d49.var_inv; simp at l51; subst l51
          obtain ⟨rfl, rfl⟩ := args50.nil_inv
          refine ⟨Heap.Extends.refl h', .var t.value, n1,
            .construct "Ixon::Univ" "Var" [u64Value t.value.toNat], restPtr1,
            hn1_pos, hdrop_lt1, fun fuel hfuel => ?_, rfl, .var t.value, hrep1⟩
          obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
          simp [Ixon.getUnivFuel, Ixon.getUnivFromTag, hok1, hflag3,
            bind, EStateM.bind, pure, EStateM.pure]
        · simp [SourceSemantics.selectArm] at sel4

/-- **Every terminating derivation of `IxonDeserialize::get_univ` at reader
offset `i`** refines `Ixon.getUniv` at `i`, producing a `RepUniv` value and the
advanced stream pointer. -/
theorem getUniv_refines_at {bytes : List UInt8} {i : Nat}
    {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : EvalFn W "IxonDeserialize::get_univ" [stream] h r h') :
    Heap.Extends h h' ∧
    ∃ (u : Ixon.Univ) (n : Nat) (uVal restPtr : SourceValue F),
      Ixon.getUniv { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok u { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [uVal, restPtr] ∧
      RepUniv h' u uVal ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  obtain ⟨ext, u, n, uVal, restPtr, _, _, hfuel, hr, uRep, restRep⟩ :=
    deserializeUniv_refines_at rep ev
  have hok : Ixon.getUniv { idx := i, bytes := ⟨bytes.toArray⟩ } =
      .ok u { idx := i + n, bytes := ⟨bytes.toArray⟩ } := by
    unfold Ixon.getUniv
    change Ixon.getUnivFuel ((ByteArray.mk bytes.toArray).size - i + 1)
      { idx := i, bytes := ⟨bytes.toArray⟩ } = _
    exact hfuel _ (by simp [ByteArray.size])
  exact ⟨ext, u, n, uVal, restPtr, hok, hr, uRep, restRep⟩

/-- **Every terminating derivation of `IxonDeserialize::get_univ` from the
start of `bytes`** refines `Ixon.getUniv (start bytes)`, producing a `RepUniv`
value and a stream pointer to the remaining bytes. -/
theorem deserializeUniv_refines {bytes : List UInt8}
    {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h bytes stream)
    (ev : EvalFn W "IxonDeserialize::get_univ" [stream] h r h') :
    Heap.Extends h h' ∧
    ∃ (u : Ixon.Univ) (n : Nat) (uVal restPtr : SourceValue F),
      Ixon.getUniv (start bytes) =
        .ok u { idx := n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [uVal, restPtr] ∧
      RepUniv h' u uVal ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop n) restPtr := by
  simpa [start] using getUniv_refines_at (i := 0) (by simpa using rep) ev

/-- Alias of `deserializeUniv_refines` matching the Aiur function name
`IxonDeserialize::get_univ`. -/
theorem getUniv_refines {bytes : List UInt8}
    {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h bytes stream)
    (ev : EvalFn W "IxonDeserialize::get_univ" [stream] h r h') :
    Heap.Extends h h' ∧
    ∃ (u : Ixon.Univ) (n : Nat) (uVal restPtr : SourceValue F),
      Ixon.getUniv (start bytes) =
        .ok u { idx := n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [uVal, restPtr] ∧
      RepUniv h' u uVal ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop n) restPtr :=
  deserializeUniv_refines rep ev

/-- **Every terminating derivation of `IxonDeserialize::get_univ_list` at
reader offset `i`** refines `getUnivChildren count` at `i`, allocating a
`RepList univListEnum RepUnivPtr` of the decoded universes and advancing the
stream pointer by the consumed bytes. -/
theorem getUnivList_refines_at (count : Nat) (hcount : count < 18446744073709551616)
    {bytes : List UInt8} {i : Nat} {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : EvalFn W "IxonDeserialize::get_univ_list" [stream, u64Value count] h r h') :
    Heap.Extends h h' ∧
    ∃ (univs : List Ixon.Univ) (n : Nat) (listPtr restPtr : SourceValue F),
      getUnivChildren count { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok univs { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      univs.length = count ∧
      r = .tuple [listPtr, restPtr] ∧
      Aiur.Library.List.RepList univListEnum RepUnivPtr h' univs listPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  induction count generalizing i stream r h h' with
  | zero =>
    have body := ev.function_inv IxVM.IxonDeserialize.get_univ_list.lookup
      (by simp [IxVM.IxonDeserialize.get_univ_list, ControlLower.hasControl])
    simp only [IxVM.IxonDeserialize.get_univ_list] at body
    obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
    obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
    obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
    obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
    obtain ⟨rfl, rfl⟩ := args14.nil_inv
    rw [instanceName_plain_some] at callee9
    obtain ⟨hiz, rfl⟩ := u64IsZero_refines hcount callee9
    simp only [↓reduceIte] at hiz; subst hiz
    rw [matchPattern_bind] at mt4
    simp only [Except.ok.injEq, Option.some.injEq] at mt4; subst mt4
    obtain ⟨v18, m19, bs20, body21, d22, sel23, d24⟩ := d5.matchValue_inv
    obtain ⟨l25, rfl⟩ := d22.var_inv; simp at l25; subst l25
    rcases selectArm_literal_inv sel23 with ⟨_, rfl, rfl⟩ | ⟨hc26, _⟩
    · obtain ⟨vs28, args29, rfl⟩ := d24.tuple_inv
      obtain ⟨v30, vs31, m32, rfl, d33, args34⟩ := args29.cons_inv
      obtain ⟨v35, m36, d37, rfl, rfl⟩ := d33.store_inv
      obtain ⟨vs38, args39, rfl⟩ := d37.construct_inv
      obtain ⟨rfl, rfl⟩ := args39.nil_inv
      obtain ⟨v40, vs41, m42, rfl, d43, args44⟩ := args34.cons_inv
      obtain ⟨l45, rfl⟩ := d43.var_inv; simp at l45; subst l45
      obtain ⟨rfl, rfl⟩ := args44.nil_inv
      rw [value_type_construct]
      have ext := Aiur.Library.List.allocNil_extends univListEnum m36
      refine ⟨ext, [], 0, (Aiur.Library.List.allocNil univListEnum m36).1, stream,
        by simp [getUnivChildren, pure, EStateM.pure], rfl, rfl,
        Aiur.Library.List.allocNil_rep univListEnum RepUnivPtr m36,
        Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext rep⟩
    · exact (hc26 rfl).elim
  | succ count ih =>
    have body := ev.function_inv IxVM.IxonDeserialize.get_univ_list.lookup
      (by simp [IxVM.IxonDeserialize.get_univ_list, ControlLower.hasControl])
    simp only [IxVM.IxonDeserialize.get_univ_list] at body
    obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
    obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
    obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
    obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
    obtain ⟨rfl, rfl⟩ := args14.nil_inv
    rw [instanceName_plain_some] at callee9
    obtain ⟨hiz, rfl⟩ := u64IsZero_refines hcount callee9
    simp only [Nat.succ_ne_zero, ↓reduceIte] at hiz; subst hiz
    rw [matchPattern_bind] at mt4
    simp only [Except.ok.injEq, Option.some.injEq] at mt4; subst mt4
    obtain ⟨v18, m19, bs20, body21, d22, sel23, d24⟩ := d5.matchValue_inv
    obtain ⟨l25, rfl⟩ := d22.var_inv; simp at l25; subst l25
    rcases selectArm_literal_inv sel23 with ⟨hc26, _, _⟩ | ⟨_, sel27⟩
    · simp at hc26
    · rcases selectArm_literal_inv sel27 with ⟨_, rfl, rfl⟩ | ⟨hc28, _⟩
      · obtain ⟨v30, m31, bs32, d33, mt34, d35⟩ := d24.letValue_inv
        obtain ⟨vs36, m37, args38, callee39⟩ := d33.call_inv
        obtain ⟨v40, vs41, m42, rfl, d43, args44⟩ := args38.cons_inv
        obtain ⟨l45, rfl⟩ := d43.var_inv; simp at l45; subst l45
        obtain ⟨rfl, rfl⟩ := args44.nil_inv
        rw [instanceName_plain_some] at callee39
        obtain ⟨ext1, u, n1, uVal, restPtr1, hok1, rfl, uRep, hrep1⟩ :=
          getUniv_refines_at rep callee39
        obtain rfl := matchPattern_tuple2_bind rfl mt34
        obtain ⟨v54, m55, bs56, d57, mt58, d59⟩ := d35.letValue_inv
        obtain ⟨vs60, m61, args62, callee63⟩ := d57.call_inv
        obtain ⟨v64, vs65, m66, rfl, d67, args68⟩ := args62.cons_inv
        obtain ⟨l69, rfl⟩ := d67.var_inv; simp at l69; subst l69
        obtain ⟨v70, vs71, m72, rfl, d73, args74⟩ := args68.cons_inv
        obtain ⟨vs75, m76, args77, callee78⟩ := d73.call_inv
        obtain ⟨v79, vs80, m81, rfl, d82, args83⟩ := args77.cons_inv
        obtain ⟨l84, rfl⟩ := d82.var_inv; simp at l84; subst l84
        obtain ⟨rfl, rfl⟩ := args83.nil_inv
        rw [instanceName_plain_some] at callee78
        obtain ⟨hsp, rfl⟩ := u64SaturatingPred_refines hcount callee78
        simp only [Nat.add_sub_cancel] at hsp; subst hsp
        obtain ⟨rfl, rfl⟩ := args74.nil_inv
        rw [instanceName_plain_some] at callee63
        obtain ⟨ext2, tailUnivs, n2, tailListPtr, restPtr2, hok2, hlen2, rfl, tailListRep, hrep2⟩ :=
          ih (by omega) hrep1 callee63
        obtain rfl := matchPattern_tuple2_bind rfl mt58
        obtain ⟨vs95, args96, rfl⟩ := d59.tuple_inv
        obtain ⟨v97, vs98, m99, rfl, d100, args101⟩ := args96.cons_inv
        obtain ⟨v102, m103, d104, rfl, rfl⟩ := d100.store_inv
        obtain ⟨vs105, args106, rfl⟩ := d104.construct_inv
        obtain ⟨v107, vs108, m109, rfl, d110, args111⟩ := args106.cons_inv
        obtain ⟨v112, m113, d114, rfl, rfl⟩ := d110.store_inv
        obtain ⟨l115, rfl⟩ := d114.var_inv; simp at l115; subst l115
        obtain ⟨v116, vs117, m118, rfl, d119, args120⟩ := args111.cons_inv
        obtain ⟨l121, rfl⟩ := d119.var_inv; simp at l121; subst l121
        obtain ⟨rfl, rfl⟩ := args120.nil_inv
        obtain ⟨v122, vs123, m124, rfl, d125, args126⟩ := args101.cons_inv
        obtain ⟨l127, rfl⟩ := d125.var_inv; simp at l127; subst l127
        obtain ⟨rfl, rfl⟩ := args126.nil_inv
        rw [value_type_construct, uRep.value_type]
        have ext_u := Heap.Extends.snoc m113 uVal
        let uPtr : SourceValue F := .ptr (.enum "Ixon::Univ") m113.length
        have uPtrRep : RepUnivPtr (m113 ++ [uVal]) u uPtr :=
          ⟨m113.length, uVal, rfl, by simp, uRep.mono (ext2.trans ext_u)⟩
        have tailListRep_u := tailListRep.mono repUnivPtr_heapMono₂ ext_u
        have ext3 := Aiur.Library.List.allocCons_extends univListEnum uPtr tailListPtr (m113 ++ [uVal])
        refine ⟨((ext1.trans ext2).trans ext_u).trans ext3, u :: tailUnivs, n1 + n2,
          (Aiur.Library.List.allocCons univListEnum uPtr tailListPtr (m113 ++ [uVal])).1, restPtr2,
          ?_, by simp [hlen2], rfl,
          Aiur.Library.List.allocCons_rep univListEnum repUnivPtr_heapMono₂ uPtrRep tailListRep_u,
          by rw [← Nat.add_assoc]; exact Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum (ext_u.trans ext3) hrep2⟩
        simp [getUnivChildren, bind, EStateM.bind, hok1, hok2, pure, EStateM.pure, Nat.add_assoc]
      · exact (hc28 rfl).elim

/-- **Every terminating derivation of `IxonDeserialize::get_univ_list` from the
start of `bytes`** refines `getUnivChildren count (start bytes)`, allocating a
`RepList univListEnum RepUnivPtr` of `count` universes and advancing the stream. -/
theorem deserializeUnivChildren_refines (count : Nat) (hcount : count < 18446744073709551616)
    {bytes : List UInt8} {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h bytes stream)
    (ev : EvalFn W "IxonDeserialize::get_univ_list" [stream, u64Value count] h r h') :
    Heap.Extends h h' ∧
    ∃ (univs : List Ixon.Univ) (n : Nat) (listPtr restPtr : SourceValue F),
      getUnivChildren count (start bytes) =
        .ok univs { idx := n, bytes := ⟨bytes.toArray⟩ } ∧
      univs.length = count ∧
      r = .tuple [listPtr, restPtr] ∧
      Aiur.Library.List.RepList univListEnum RepUnivPtr h' univs listPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop n) restPtr := by
  simpa [start] using getUnivList_refines_at count hcount (i := 0) (by simpa using rep) ev

/-- Alias of `deserializeUnivChildren_refines` matching the Aiur function name
`IxonDeserialize::get_univ_list`. -/
theorem getUnivList_refines (count : Nat) (hcount : count < 18446744073709551616)
    {bytes : List UInt8} {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h bytes stream)
    (ev : EvalFn W "IxonDeserialize::get_univ_list" [stream, u64Value count] h r h') :
    Heap.Extends h h' ∧
    ∃ (univs : List Ixon.Univ) (n : Nat) (listPtr restPtr : SourceValue F),
      getUnivChildren count (start bytes) =
        .ok univs { idx := n, bytes := ⟨bytes.toArray⟩ } ∧
      univs.length = count ∧
      r = .tuple [listPtr, restPtr] ∧
      Aiur.Library.List.RepList univListEnum RepUnivPtr h' univs listPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop n) restPtr :=
  deserializeUnivChildren_refines count hcount rep ev

/-- **Every terminating derivation of `IxonDeserialize::get_univs` on a valid
byte stream** reads a TagN0 count `t` followed by `t.value.toNat` universe
levels into a `RepList univListEnum RepUnivPtr`. -/
theorem getUnivs_refines {bytes : List UInt8} {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h bytes stream)
    (ev : EvalFn W "IxonDeserialize::get_univs" [stream] h r h') :
    Heap.Extends h h' ∧
    ∃ (t : Ixon.TagN) (n1 n2 : Nat) (univs : List Ixon.Univ) (listPtr restPtr : SourceValue F),
      Ixon.getTagN 0 (start bytes) = .ok t { idx := n1, bytes := ⟨bytes.toArray⟩ } ∧
      t.flag = 0 ∧
      getUnivChildren t.value.toNat (start (bytes.drop n1)) =
        .ok univs { idx := n2, bytes := ⟨(bytes.drop n1).toArray⟩ } ∧
      univs.length = t.value.toNat ∧
      r = .tuple [listPtr, restPtr] ∧
      Aiur.Library.List.RepList univListEnum RepUnivPtr h' univs listPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' ((bytes.drop n1).drop n2) restPtr := by
  have body := ev.function_inv IxVM.IxonDeserialize.get_univs.lookup
    (by simp [IxVM.IxonDeserialize.get_univs, ControlLower.hasControl])
  simp only [IxVM.IxonDeserialize.get_univs] at body
  obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
  obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
  obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
  obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
  obtain ⟨rfl, rfl⟩ := args14.nil_inv
  rw [instanceName_plain_some] at callee9
  obtain ⟨rfl, t, n1, restPtr1, hok1, hflag, hrep1, rfl⟩ := getTagN0_refines rep callee9
  obtain rfl := matchPattern_tuple2_bind rfl mt4
  obtain ⟨vs24, m25, args26, callee27⟩ := d5.call_inv
  obtain ⟨v28, vs29, m30, rfl, d31, args32⟩ := args26.cons_inv
  obtain ⟨l33, rfl⟩ := d31.var_inv; simp at l33; subst l33
  obtain ⟨v34, vs35, m36, rfl, d37, args38⟩ := args32.cons_inv
  obtain ⟨l39, rfl⟩ := d37.var_inv; simp at l39; subst l39
  obtain ⟨rfl, rfl⟩ := args38.nil_inv
  rw [instanceName_plain_some] at callee27
  obtain ⟨ext, univs, n2, listPtr, restPtr2, hok2, hlen, rfl, listRep, dropRep⟩ :=
    deserializeUnivChildren_refines t.value.toNat t.value.toNat_lt hrep1 callee27
  exact ⟨ext, t, n1, n2, univs, listPtr, restPtr2, hok1, hflag, hok2, hlen, rfl, listRep, dropRep⟩

/-! ### Contract Value Encodings and Representation of `Ixon.Expr` / `RepShareVec` -/

/-- Source-level encoding of `Ixon.Uses` as an `Ixon::Uses` enum value. -/
def usesValue : Ixon.Uses → SourceValue F
  | .erased => .construct "Ixon::Uses" "Erased" []
  | .linear => .construct "Ixon::Uses" "Linear" []
  | .affine => .construct "Ixon::Uses" "Affine" []
  | .many   => .construct "Ixon::Uses" "Many" []

/-- Source-level encoding of `Ixon.Owned` as an `Ixon::Owned` enum value. -/
def ownedValue : Ixon.Owned → SourceValue F
  | .unique => .construct "Ixon::Owned" "Unique" []
  | .shared => .construct "Ixon::Owned" "Shared" []

/-- Source-level encoding of `Ixon.Locality` as an `Ixon::Locality` enum value. -/
def localityValue : Ixon.Locality → SourceValue F
  | .unrestricted => .construct "Ixon::Locality" "Unrestricted" []
  | .local        => .construct "Ixon::Locality" "Local" []

/-- Source-level encoding of `Ixon.ValueContract` as `Ixon::ValueContract::Mk(owned, locality)`. -/
def valueContractValue (vc : Ixon.ValueContract) : SourceValue F :=
  .construct "Ixon::ValueContract" "Mk" [ownedValue vc.owned, localityValue vc.locality]

/-- Source-level encoding of `Ixon.BinderContract` as `Ixon::BinderContract::Mk(uses, value)`. -/
def binderContractValue (bc : Ixon.BinderContract) : SourceValue F :=
  .construct "Ixon::BinderContract" "Mk" [usesValue bc.uses, valueContractValue bc.value]

/-- Source-level encoding of `Ixon.LetKind` as an `Ixon::LetKind` enum value. -/
def letKindValue : Ixon.LetKind → SourceValue F
  | .value        => .construct "Ixon::LetKind" "Value" []
  | .borrowShared => .construct "Ixon::LetKind" "BorrowShared" []

/-- Source-level encoding of `Ixon.LetContract` as `Ixon::LetContract::Mk(nonDep, kind, binder)`. -/
def letContractValue (lc : Ixon.LetContract) : SourceValue F :=
  .construct "Ixon::LetContract" "Mk"
    [.field (if lc.nonDep then 1 else 0), letKindValue lc.kind, binderContractValue lc.binder]

/-- Aliases matching the `encode*` naming convention. -/
abbrev encodeUses : Ixon.Uses → SourceValue F := usesValue
abbrev encodeOwned : Ixon.Owned → SourceValue F := ownedValue
abbrev encodeLocality : Ixon.Locality → SourceValue F := localityValue
abbrev encodeValueContract : Ixon.ValueContract → SourceValue F := valueContractValue
abbrev encodeBinderContract : Ixon.BinderContract → SourceValue F := binderContractValue
abbrev encodeLetKind : Ixon.LetKind → SourceValue F := letKindValue
abbrev encodeLetContract : Ixon.LetContract → SourceValue F := letContractValue

/-- Decode a `BinderContract` from the low 4 bits of a mode byte `b`. -/
def binderContractOfByte (b : Nat) : Ixon.BinderContract :=
  let uses : Ixon.Uses :=
    match b % 4 with
    | 0 => .erased
    | 1 => .linear
    | 2 => .affine
    | _ => .many
  let owned : Ixon.Owned := if b / 4 % 2 = 0 then .unique else .shared
  let locality : Ixon.Locality := if b / 8 % 2 = 0 then .unrestricted else .local
  { uses, value := { owned, locality } }

/-- Decode a `ValueContract` from bits 4 and 5 of a mode byte `b`. -/
def valueContractOfHighBits (b : Nat) : Ixon.ValueContract :=
  let owned : Ixon.Owned := if b / 16 % 2 = 0 then .unique else .shared
  let locality : Ixon.Locality := if b / 32 % 2 = 0 then .unrestricted else .local
  { owned, locality }

/-- Decode a `LetContract` from 2-bit `flags` (`< 4`) and a `BinderContract`. -/
def letContractOfFlags (flags : Nat) (binder : Ixon.BinderContract) : Ixon.LetContract :=
  { nonDep := flags % 2 != 0
  , kind := if flags / 2 % 2 = 0 then .value else .borrowShared
  , binder }

theorem binderContractValue_ofByte (b : Nat) :
    binderContractValue (binderContractOfByte b) =
      .construct "Ixon::BinderContract" "Mk" [
        .construct "Ixon::Uses"
          (match b % 4 with
            | 0 => "Erased" | 1 => "Linear" | 2 => "Affine" | _ => "Many") [],
        .construct "Ixon::ValueContract" "Mk" [
          .construct "Ixon::Owned" (if b / 4 % 2 = 0 then "Unique" else "Shared") [],
          .construct "Ixon::Locality" (if b / 8 % 2 = 0 then "Unrestricted" else "Local") []]] := by
  dsimp [binderContractOfByte, binderContractValue, usesValue, valueContractValue,
    ownedValue, localityValue]
  have h4 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
  have hb2 : b / 4 % 2 = 0 ∨ b / 4 % 2 = 1 := Nat.mod_two_eq_zero_or_one (b / 4)
  have hb3 : b / 8 % 2 = 0 ∨ b / 8 % 2 = 1 := Nat.mod_two_eq_zero_or_one (b / 8)
  rcases h4 with h | h | h | h <;> rcases hb2 with h2 | h2 <;> rcases hb3 with h3 | h3 <;>
    simp [h, h2, h3]

theorem valueContractValue_ofHighBits (b : Nat) :
    valueContractValue (valueContractOfHighBits b) =
      .construct "Ixon::ValueContract" "Mk" [
        .construct "Ixon::Owned" (if b / 16 % 2 = 0 then "Unique" else "Shared") [],
        .construct "Ixon::Locality" (if b / 32 % 2 = 0 then "Unrestricted" else "Local") []] := by
  dsimp [valueContractOfHighBits, valueContractValue, ownedValue, localityValue]
  have hb4 : b / 16 % 2 = 0 ∨ b / 16 % 2 = 1 := Nat.mod_two_eq_zero_or_one (b / 16)
  have hb5 : b / 32 % 2 = 0 ∨ b / 32 % 2 = 1 := Nat.mod_two_eq_zero_or_one (b / 32)
  rcases hb4 with h4 | h4 <;> rcases hb5 with h5 | h5 <;> simp [h4, h5]

theorem letContractValue_ofFlags (flags : Nat) (bc : Ixon.BinderContract) :
    letContractValue (letContractOfFlags flags bc) =
      .construct "Ixon::LetContract" "Mk" [
        .field ((flags % 2 : Nat) : F),
        .construct "Ixon::LetKind" (if flags / 2 % 2 = 0 then "Value" else "BorrowShared") [],
        binderContractValue bc] := by
  dsimp [letContractOfFlags, letContractValue, letKindValue]
  have hb0 : flags % 2 = 0 ∨ flags % 2 = 1 := Nat.mod_two_eq_zero_or_one flags
  have hb1 : flags / 2 % 2 = 0 ∨ flags / 2 % 2 = 1 := Nat.mod_two_eq_zero_or_one (flags / 2)
  rcases hb0 with h0 | h0 <;> rcases hb1 with h1 | h1 <;> simp [h0, h1]

theorem binderContract_ofBits?_of_lt16 {b : UInt8} (hb : b.toNat < 16) :
    Ixon.BinderContract.ofBits? b = some (binderContractOfByte b.toNat) := by
  have hb_eq : UInt8.ofNat b.toNat = b := UInt8.ofNat_toNat
  rw [← hb_eq]
  generalize b.toNat = n at hb
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
  all_goals try omega
  all_goals rfl

theorem unpackAllContract?_of_lt64 {b : UInt8} (hb : b.toNat < 64) :
    Ixon.unpackAllContract? b =
      some (binderContractOfByte b.toNat, valueContractOfHighBits b.toNat) := by
  have hb_eq : UInt8.ofNat b.toNat = b := UInt8.ofNat_toNat
  rw [← hb_eq]
  generalize b.toNat = n at hb
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
    _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
    _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
    _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
  all_goals try omega
  all_goals rfl

theorem letContract_ofFlags?_of_lt4 {sz : UInt64} (hsz : sz.toNat < 4) (bc : Ixon.BinderContract) :
    Ixon.LetContract.ofFlags? sz bc = some (letContractOfFlags sz.toNat bc) := by
  have hsz_eq : UInt64.ofNat sz.toNat = sz := UInt64.ofNat_toNat
  rw [← hsz_eq]
  generalize sz.toNat = n at hsz
  rcases n with _ | _ | _ | _ | n
  all_goals try omega
  all_goals rfl

/-- `RepExpr h e v` asserts that `v` is a heap pointer `.ptr (.enum "Ixon::Expr") addr`
in `h : Heap F` pointing to an `Ixon::Expr` constructor cell representing `e : Ixon.Expr`. -/
inductive RepExpr (h : Heap F) : Ixon.Expr → SourceValue F → Prop where
  | sort {idx : UInt64} {addr : Nat}
      (cell : h[addr]? = some (.construct "Ixon::Expr" "Srt" [u64Value idx.toNat])) :
      RepExpr h (.sort idx) (.ptr (.enum "Ixon::Expr") addr)
  | var {idx : UInt64} {addr : Nat}
      (cell : h[addr]? = some (.construct "Ixon::Expr" "Var" [u64Value idx.toNat])) :
      RepExpr h (.var idx) (.ptr (.enum "Ixon::Expr") addr)
  | ref {idx : UInt64} {univs : Array UInt64} {listPtr : SourceValue F} {addr : Nat}
      (cell : h[addr]? = some (.construct "Ixon::Expr" "Ref" [u64Value idx.toNat, listPtr]))
      (listRep : Aiur.Library.List.RepList u64ListEnum Aiur.Library.RepU64 h univs.toList listPtr) :
      RepExpr h (.ref idx univs) (.ptr (.enum "Ixon::Expr") addr)
  | recur {idx : UInt64} {univs : Array UInt64} {listPtr : SourceValue F} {addr : Nat}
      (cell : h[addr]? = some (.construct "Ixon::Expr" "Rec" [u64Value idx.toNat, listPtr]))
      (listRep : Aiur.Library.List.RepList u64ListEnum Aiur.Library.RepU64 h univs.toList listPtr) :
      RepExpr h (.recur idx univs) (.ptr (.enum "Ixon::Expr") addr)
  | prj {tIdx fIdx : UInt64} {val : Ixon.Expr} {valPtr : SourceValue F} {addr : Nat}
      (cell : h[addr]? = some (.construct "Ixon::Expr" "Prj" [u64Value tIdx.toNat, u64Value fIdx.toNat, valPtr]))
      (valRep : RepExpr h val valPtr) :
      RepExpr h (.prj tIdx fIdx val) (.ptr (.enum "Ixon::Expr") addr)
  | str {idx : UInt64} {addr : Nat}
      (cell : h[addr]? = some (.construct "Ixon::Expr" "Str" [u64Value idx.toNat])) :
      RepExpr h (.str idx) (.ptr (.enum "Ixon::Expr") addr)
  | nat {idx : UInt64} {addr : Nat}
      (cell : h[addr]? = some (.construct "Ixon::Expr" "Nat" [u64Value idx.toNat])) :
      RepExpr h (.nat idx) (.ptr (.enum "Ixon::Expr") addr)
  | app {fnE arg : Ixon.Expr} {fnPtr argPtr : SourceValue F} {addr : Nat}
      (cell : h[addr]? = some (.construct "Ixon::Expr" "App" [fnPtr, argPtr]))
      (fnRep : RepExpr h fnE fnPtr)
      (argRep : RepExpr h arg argPtr) :
      RepExpr h (.app fnE arg) (.ptr (.enum "Ixon::Expr") addr)
  | lam {bc : Ixon.BinderContract} {ty body : Ixon.Expr} {tyPtr bodyPtr : SourceValue F} {addr : Nat}
      (cell : h[addr]? = some (.construct "Ixon::Expr" "Lam" [binderContractValue bc, tyPtr, bodyPtr]))
      (tyRep : RepExpr h ty tyPtr)
      (bodyRep : RepExpr h body bodyPtr) :
      RepExpr h (.lam bc ty body) (.ptr (.enum "Ixon::Expr") addr)
  | all {bc : Ixon.BinderContract} {vc : Ixon.ValueContract} {ty body : Ixon.Expr}
      {tyPtr bodyPtr : SourceValue F} {addr : Nat}
      (cell : h[addr]? = some (.construct "Ixon::Expr" "All" [binderContractValue bc, valueContractValue vc, tyPtr, bodyPtr]))
      (tyRep : RepExpr h ty tyPtr)
      (bodyRep : RepExpr h body bodyPtr) :
      RepExpr h (.all bc vc ty body) (.ptr (.enum "Ixon::Expr") addr)
  | letE {lc : Ixon.LetContract} {ty val body : Ixon.Expr}
      {tyPtr valPtr bodyPtr : SourceValue F} {addr : Nat}
      (cell : h[addr]? = some (.construct "Ixon::Expr" "Let" [letContractValue lc, tyPtr, valPtr, bodyPtr]))
      (tyRep : RepExpr h ty tyPtr)
      (valRep : RepExpr h val valPtr)
      (bodyRep : RepExpr h body bodyPtr) :
      RepExpr h (.letE lc ty val body) (.ptr (.enum "Ixon::Expr") addr)
  | share {idx : UInt64} {addr : Nat}
      (cell : h[addr]? = some (.construct "Ixon::Expr" "Share" [u64Value idx.toNat])) :
      RepExpr h (.share idx) (.ptr (.enum "Ixon::Expr") addr)

theorem RepExpr.mono {h₁ h₂ : Heap F} {e : Ixon.Expr} {ptr : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepExpr h₁ e ptr) : RepExpr h₂ e ptr := by
  induction rep with
  | sort cell => exact .sort (ext.getElem?_eq cell)
  | var cell => exact .var (ext.getElem?_eq cell)
  | ref cell listRep =>
    exact .ref (ext.getElem?_eq cell)
      (listRep.mono Aiur.Library.repU64_heapMono₂ ext)
  | recur cell listRep =>
    exact .recur (ext.getElem?_eq cell)
      (listRep.mono Aiur.Library.repU64_heapMono₂ ext)
  | prj cell _ ih => exact .prj (ext.getElem?_eq cell) ih
  | str cell => exact .str (ext.getElem?_eq cell)
  | nat cell => exact .nat (ext.getElem?_eq cell)
  | app cell _ _ ih1 ih2 => exact .app (ext.getElem?_eq cell) ih1 ih2
  | lam cell _ _ ih1 ih2 => exact .lam (ext.getElem?_eq cell) ih1 ih2
  | all cell _ _ ih1 ih2 => exact .all (ext.getElem?_eq cell) ih1 ih2
  | letE cell _ _ _ ih1 ih2 ih3 => exact .letE (ext.getElem?_eq cell) ih1 ih2 ih3
  | share cell => exact .share (ext.getElem?_eq cell)

theorem repExpr_heapMono₂ : HeapMono₂ RepExpr :=
  fun _ _ _ _ ext rep => rep.mono ext

/-- The prepared enum symbol for `Lists::Node<&Ixon::Expr>`. -/
abbrev exprListEnum : String :=
  instanceName [] "Lists::Node" (some [(.ptr (.named "Ixon::Expr" []))])

/-- `RepShareVec h exprs v` asserts that `v` is a `Lists::Node<&Ixon::Expr>` linked list
in `h` representing `exprs : List Ixon.Expr`. -/
abbrev RepShareVec (h : Heap F) (exprs : List Ixon.Expr) (v : SourceValue F) : Prop :=
  Aiur.Library.List.RepList exprListEnum RepExpr h exprs v

theorem RepShareVec.mono {h₁ h₂ : Heap F} {exprs : List Ixon.Expr} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepShareVec h₁ exprs v) : RepShareVec h₂ exprs v :=
  Aiur.Library.List.repList_heapMono₂ exprListEnum repExpr_heapMono₂ ext rep

theorem repShareVec_heapMono₂ : HeapMono₂ RepShareVec :=
  fun _ _ _ _ ext rep => RepShareVec.mono ext rep

/-! ### Mutual / Telescopic Refinement for `Expr` and `ShareVec` Deserialization -/

theorem getU8_of_drop_cons {bytes : List UInt8} {i : Nat} {b : UInt8} {rest : List UInt8}
    (hcons : bytes.drop i = b :: rest) :
    Ixon.getU8 { idx := i, bytes := ⟨bytes.toArray⟩ } =
      .ok b { idx := i + 1, bytes := ⟨bytes.toArray⟩ } ∧
    bytes.drop (i + 1) = rest ∧
    (bytes.drop (i + 1)).length < (bytes.drop i).length := by
  have hlen : 0 < (bytes.drop i).length := by simp [hcons]
  have hi : i < bytes.length := by rw [List.length_drop] at hlen; omega
  have hget : bytes[i] = b := by
    have h0 : (bytes.drop i)[0]? = some b := by simp [hcons]
    rw [List.getElem?_drop, Nat.add_zero, List.getElem?_eq_getElem hi, Option.some.injEq] at h0
    exact h0
  have hdrop : bytes.drop (i + 1) = rest := by
    rw [← List.drop_drop, hcons, List.drop_succ_cons, List.drop_zero]
  refine ⟨?_, hdrop, ?_⟩
  · rw [getU8_at hi, hget]
  · rw [hdrop, hcons, List.length_cons]; omega

theorem checkCount_ok {bytes : List UInt8} {i : Nat} {count : UInt64} {minBytes : Nat}
    (hle : count.toNat * minBytes ≤ (bytes.drop i).length) :
    Ixon.checkCount count minBytes { idx := i, bytes := ⟨bytes.toArray⟩ } =
      .ok () { idx := i, bytes := ⟨bytes.toArray⟩ } := by
  have hng : ¬ (count.toNat * minBytes > (ByteArray.mk bytes.toArray).size - i) := by
    simp only [ByteArray.size, List.size_toArray]
    rw [List.length_drop] at hle
    omega
  simp [Ixon.checkCount, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    pure, EStateM.pure, hng]

/-- Strengthening of `getU64List_refines_at` recording that reading `count`
`TagN 0` values consumes at least `count` bytes and shrinks `bytes.drop` by at
least `count`. -/
theorem getU64List_progress (count : Nat) (hcount : count < 18446744073709551616)
    {bytes : List UInt8} {i : Nat} {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : EvalFn W "IxonDeserialize::get_u64_list" [stream, u64Value count] h r h') :
    Heap.Extends h h' ∧
    ∃ (vals : List UInt64) (n : Nat) (listPtr restPtr : SourceValue F),
      (bytes.drop (i + n)).length + count ≤ (bytes.drop i).length ∧
      Ixon.getTagN0Values count { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok vals { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      vals.length = count ∧
      r = .tuple [listPtr, restPtr] ∧
      Aiur.Library.List.RepList u64ListEnum Aiur.Library.RepU64 h' vals listPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  induction count generalizing i stream r h h' with
  | zero =>
    obtain ⟨ext, vals, n, listPtr, restPtr, hok, hlen, hr, listRep, dropRep⟩ :=
      getU64List_refines_at 0 hcount rep ev
    simp only [Ixon.getTagN0Values, pure, EStateM.pure] at hok
    injection hok with hvals hs
    have hn : n = 0 := by
      have hidx := congrArg Ixon.GetState.idx hs
      dsimp at hidx
      omega
    subst hn hvals
    refine ⟨ext, [], 0, listPtr, restPtr, by simp,
      by simp [Ixon.getTagN0Values, pure, EStateM.pure], hlen, hr, listRep, dropRep⟩
  | succ count ih =>
    have body := ev.function_inv IxVM.IxonDeserialize.get_u64_list.lookup
      (by simp [IxVM.IxonDeserialize.get_u64_list, ControlLower.hasControl])
    simp only [IxVM.IxonDeserialize.get_u64_list] at body
    obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
    obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
    obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
    obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
    obtain ⟨rfl, rfl⟩ := args14.nil_inv
    rw [instanceName_plain_some] at callee9
    obtain ⟨hiz, rfl⟩ := u64IsZero_refines hcount callee9
    simp only [Nat.succ_ne_zero, ↓reduceIte] at hiz; subst hiz
    rw [matchPattern_bind] at mt4
    simp only [Except.ok.injEq, Option.some.injEq] at mt4; subst mt4
    obtain ⟨v18, m19, bs20, body21, d22, sel23, d24⟩ := d5.matchValue_inv
    obtain ⟨l25, rfl⟩ := d22.var_inv; simp at l25; subst l25
    rcases selectArm_literal_inv sel23 with ⟨hc26, _, _⟩ | ⟨_, sel27⟩
    · simp at hc26
    · rcases selectArm_literal_inv sel27 with ⟨_, rfl, rfl⟩ | ⟨hc28, _⟩
      · obtain ⟨v30, m31, bs32, d33, mt34, d35⟩ := d24.letValue_inv
        obtain ⟨vs36, m37, args38, callee39⟩ := d33.call_inv
        obtain ⟨v40, vs41, m42, rfl, d43, args44⟩ := args38.cons_inv
        obtain ⟨l45, rfl⟩ := d43.var_inv; simp at l45; subst l45
        obtain ⟨rfl, rfl⟩ := args44.nil_inv
        rw [instanceName_plain_some] at callee39
        obtain ⟨rfl, t, n1, restPtr1, hok_drop, _, hrep1, rfl⟩ := getTagN0_refines rep callee39
        have hok1 := getTagN_drop hok_drop
        have hdrop_lt1 : (bytes.drop (i + n1)).length < (bytes.drop i).length := by
          rw [← List.drop_drop]
          exact drop_length_lt_of_getTagN hok_drop
        rw [List.drop_drop] at hrep1
        obtain rfl := matchPattern_tuple2_bind rfl mt34
        obtain ⟨v54, m55, bs56, d57, mt58, d59⟩ := d35.letValue_inv
        obtain ⟨vs60, m61, args62, callee63⟩ := d57.call_inv
        obtain ⟨v64, vs65, m66, rfl, d67, args68⟩ := args62.cons_inv
        obtain ⟨l69, rfl⟩ := d67.var_inv; simp at l69; subst l69
        obtain ⟨v70, vs71, m72, rfl, d73, args74⟩ := args68.cons_inv
        obtain ⟨vs75, m76, args77, callee78⟩ := d73.call_inv
        obtain ⟨v79, vs80, m81, rfl, d82, args83⟩ := args77.cons_inv
        obtain ⟨l84, rfl⟩ := d82.var_inv; simp at l84; subst l84
        obtain ⟨rfl, rfl⟩ := args83.nil_inv
        rw [instanceName_plain_some] at callee78
        obtain ⟨hsp, rfl⟩ := u64SaturatingPred_refines hcount callee78
        simp only [Nat.add_sub_cancel] at hsp; subst hsp
        obtain ⟨rfl, rfl⟩ := args74.nil_inv
        rw [instanceName_plain_some] at callee63
        obtain ⟨ext1, tailVals, n2, tailListPtr, restPtr2, hprog2, hok2, hlen2, rfl, tailListRep, hrep2⟩ :=
          ih (by omega) hrep1 callee63
        obtain rfl := matchPattern_tuple2_bind rfl mt58
        obtain ⟨vs95, args96, rfl⟩ := d59.tuple_inv
        obtain ⟨v97, vs98, m99, rfl, d100, args101⟩ := args96.cons_inv
        obtain ⟨v102, m103, d104, rfl, rfl⟩ := d100.store_inv
        obtain ⟨vs105, args106, rfl⟩ := d104.construct_inv
        obtain ⟨v107, vs108, m109, rfl, d110, args111⟩ := args106.cons_inv
        obtain ⟨l112, rfl⟩ := d110.var_inv; simp at l112; subst l112
        obtain ⟨v113, vs114, m115, rfl, d116, args117⟩ := args111.cons_inv
        obtain ⟨l118, rfl⟩ := d116.var_inv; simp at l118; subst l118
        obtain ⟨rfl, rfl⟩ := args117.nil_inv
        obtain ⟨v119, vs120, m121, rfl, d122, args123⟩ := args101.cons_inv
        obtain ⟨l124, rfl⟩ := d122.var_inv; simp at l124; subst l124
        obtain ⟨rfl, rfl⟩ := args123.nil_inv
        rw [value_type_construct]
        have ext2 := Aiur.Library.List.allocCons_extends u64ListEnum (u64Value t.value.toNat) tailListPtr m103
        refine ⟨ext1.trans ext2, t.value :: tailVals, n1 + n2,
          (Aiur.Library.List.allocCons u64ListEnum (u64Value t.value.toNat) tailListPtr m103).1, restPtr2,
          ?_, ?_, by simp [hlen2], rfl,
          Aiur.Library.List.allocCons_rep u64ListEnum Aiur.Library.repU64_heapMono₂
            (repU64_u64Value m103 t.value) tailListRep,
          by rw [← Nat.add_assoc]; exact Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext2 hrep2⟩
        · rw [show i + (n1 + n2) = i + n1 + n2 by omega]
          omega
        · simp [Ixon.getTagN0Values, bind, EStateM.bind, hok1, hok2, pure, EStateM.pure, Nat.add_assoc]
      · exact (hc28 rfl).elim

theorem getLamMode_refines_at {bytes : List UInt8} {i : Nat}
    {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : EvalFn W "IxonDeserialize::get_lam_mode" [stream] h r h') :
    h' = h ∧ ∃ (bc : Ixon.BinderContract) (restPtr : SourceValue F),
      (bytes.drop (i + 1)).length + 1 = (bytes.drop i).length ∧
      Ixon.getBinderContract { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok bc { idx := i + 1, bytes := ⟨bytes.toArray⟩ } ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop (i + 1)) restPtr ∧
      r = .tuple [binderContractValue bc, restPtr] := by
  obtain ⟨rfl, b, rest, restPtr, hcons, hlt, tailRep, hr⟩ := getLamMode_refines rep ev
  rw [← binderContractValue_ofByte] at hr
  obtain ⟨hu8, hdrop, _⟩ := getU8_of_drop_cons hcons
  have hlen_eq : (bytes.drop (i + 1)).length + 1 = (bytes.drop i).length := by
    rw [hdrop, hcons, List.length_cons]
  rw [← hdrop] at tailRep
  have hbits := binderContract_ofBits?_of_lt16 hlt
  refine ⟨rfl, binderContractOfByte b.toNat, restPtr, hlen_eq, ?_, tailRep, hr⟩
  simp [Ixon.getBinderContract, bind, EStateM.bind, hu8, hbits, pure, EStateM.pure]

theorem getAllMode_refines_at {bytes : List UInt8} {i : Nat}
    {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : EvalFn W "IxonDeserialize::get_all_mode" [stream] h r h') :
    h' = h ∧ ∃ (bc : Ixon.BinderContract) (vc : Ixon.ValueContract) (restPtr : SourceValue F),
      (bytes.drop (i + 1)).length + 1 = (bytes.drop i).length ∧
      Ixon.getU8 { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok (Ixon.packAllContract bc vc) { idx := i + 1, bytes := ⟨bytes.toArray⟩ } ∧
      (∃ bits,
        Ixon.getU8 { idx := i, bytes := ⟨bytes.toArray⟩ } =
          .ok bits { idx := i + 1, bytes := ⟨bytes.toArray⟩ } ∧
        Ixon.unpackAllContract? bits = some (bc, vc)) ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop (i + 1)) restPtr ∧
      r = .tuple [.tuple [binderContractValue bc, valueContractValue vc], restPtr] := by
  obtain ⟨rfl, b, rest, restPtr, hcons, hlt, tailRep, hr⟩ := getAllMode_refines rep ev
  rw [← binderContractValue_ofByte, ← valueContractValue_ofHighBits] at hr
  obtain ⟨hu8, hdrop, _⟩ := getU8_of_drop_cons hcons
  have hlen_eq : (bytes.drop (i + 1)).length + 1 = (bytes.drop i).length := by
    rw [hdrop, hcons, List.length_cons]
  rw [← hdrop] at tailRep
  have hbits := unpackAllContract?_of_lt64 hlt
  have hpack : Ixon.packAllContract (binderContractOfByte b.toNat) (valueContractOfHighBits b.toNat) = b := by
    have hb_eq : UInt8.ofNat b.toNat = b := UInt8.ofNat_toNat
    rw [← hb_eq]
    generalize b.toNat = n at hlt
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
      _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
      _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
      _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
    all_goals try omega
    all_goals rfl
  refine ⟨rfl, binderContractOfByte b.toNat, valueContractOfHighBits b.toNat, restPtr,
    hlen_eq, by rw [hpack]; exact hu8, ⟨b, hu8, hbits⟩, tailRep, hr⟩

theorem evalExpr_reject_ctor_inv {types : Types} {locals : Environment F Nat}
    {varName ctor : String} {wildcards : List (Generic.Pattern F)} {ptr : SourceValue F}
    {msg : Option String} {failBody okBody : Generic.Expr F}
    {before after : Heap F} {result : SourceValue F}
    (hvar : locals.find? (·.1 == varName) = some (varName, ptr))
    (ev : EvalExpr W types locals
      (.matchValue (.load (.var varName)) [
        ((.construct (.named "Ixon::Expr" []) ctor wildcards),
         (.letValue .wildcard
           (.builtin (.assertEq { message := msg, runtimeCheck := true }) [(.literal 0), (.literal 1)])
           failBody)),
        (.wildcard, okBody)])
      before result after) :
    (∃ v, loadValue before ptr = .ok v ∧
      W.matchPattern types before (.construct (.named "Ixon::Expr" []) ctor wildcards) v = .ok none) ∧
    EvalExpr W types locals okBody before result after := by
  obtain ⟨v_scrut, m_scrut, bs_arm, body_arm, d_scrut, sel_arm, d_arm⟩ := ev.matchValue_inv
  obtain ⟨v_ptr, d_var, hload⟩ := d_scrut.load_inv
  obtain ⟨l_var, rfl⟩ := d_var.var_inv
  rw [hvar, Option.some.injEq, Prod.mk.injEq] at l_var
  rcases l_var with ⟨_, rfl⟩
  rw [SourceSemantics.selectArm] at sel_arm
  cases hmp : W.matchPattern types m_scrut (.construct (.named "Ixon::Expr" []) ctor wildcards) v_scrut with
  | error e =>
    rw [hmp] at sel_arm
    cases sel_arm
  | ok opt =>
    rw [hmp] at sel_arm
    cases opt with
    | some bs =>
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Option.some.injEq,
        Prod.mk.injEq] at sel_arm
      rcases sel_arm with ⟨rfl, rfl⟩
      exact (evalExpr_assertEq_zero_one_false d_arm).elim
    | none =>
      simp only [bind, Except.bind] at sel_arm
      obtain ⟨rfl, rfl⟩ := selectArm_wildcard_inv sel_arm
      exact ⟨⟨v_scrut, hload, hmp⟩, d_arm⟩

theorem repExpr_ne_app {h : Heap F} {e : Ixon.Expr} {ptr v : SourceValue F}
    (rep : RepExpr h e ptr) (hload : loadValue h ptr = .ok v)
    (hmp : W.matchPattern [] h (.construct (.named "Ixon::Expr" []) "App" [.wildcard, .wildcard]) v = .ok none) :
    ∀ fnE arg, e ≠ .app fnE arg := by
  intro fnE arg heq
  subst heq
  cases rep with
  | app cell _ _ =>
    simp only [loadValue, cell, value_type_construct, ne_self_iff_false, Bool.false_eq_true, ↓reduceIte,
      bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hload
    subst hload
    have hctor : constructorName [] (.named "Ixon::Expr" []) = "Ixon::Expr" := by
      simp [constructorName, Ty.toCore, Instance.symbol]
    simp [matchPattern_construct, hctor, matchListWith, matchPattern_wildcard,
      bind, Except.bind, pure, Except.pure] at hmp

theorem repExpr_ne_lam {h : Heap F} {e : Ixon.Expr} {ptr v : SourceValue F}
    (rep : RepExpr h e ptr) (hload : loadValue h ptr = .ok v)
    (hmp : W.matchPattern [] h (.construct (.named "Ixon::Expr" []) "Lam" [.wildcard, .wildcard, .wildcard]) v = .ok none) :
    ∀ bc ty body, e ≠ .lam bc ty body := by
  intro bc ty body heq
  subst heq
  cases rep with
  | lam cell _ _ =>
    simp only [loadValue, cell, value_type_construct, ne_self_iff_false, Bool.false_eq_true, ↓reduceIte,
      bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hload
    subst hload
    have hctor : constructorName [] (.named "Ixon::Expr" []) = "Ixon::Expr" := by
      simp [constructorName, Ty.toCore, Instance.symbol]
    simp [matchPattern_construct, hctor, matchListWith, matchPattern_wildcard,
      bind, Except.bind, pure, Except.pure] at hmp

theorem repExpr_ne_all {h : Heap F} {e : Ixon.Expr} {ptr v : SourceValue F}
    (rep : RepExpr h e ptr) (hload : loadValue h ptr = .ok v)
    (hmp : W.matchPattern [] h (.construct (.named "Ixon::Expr" []) "All" [.wildcard, .wildcard, .wildcard, .wildcard]) v = .ok none) :
    ∀ bc vc ty body, e ≠ .all bc vc ty body := by
  intro bc vc ty body heq
  subst heq
  cases rep with
  | all cell _ _ =>
    simp only [loadValue, cell, value_type_construct, ne_self_iff_false, Bool.false_eq_true, ↓reduceIte,
      bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hload
    subst hload
    have hctor : constructorName [] (.named "Ixon::Expr" []) = "Ixon::Expr" := by
      simp [constructorName, Ty.toCore, Instance.symbol]
    simp [matchPattern_construct, hctor, matchListWith, matchPattern_wildcard,
      bind, Except.bind, pure, Except.pure] at hmp

theorem match_not_app_ok {e : Ixon.Expr} (hne : ∀ fnE arg, e ≠ .app fnE arg) :
    (match e with
     | .app .. => (throw "getExpr: non-canonical app base" : Ixon.GetM Unit)
     | _ => pure ()) = pure () := by
  cases e with
  | app fnE arg => exact (hne fnE arg rfl).elim
  | _ => rfl

theorem match_not_lam_ok {e : Ixon.Expr} (hne : ∀ bc ty body, e ≠ .lam bc ty body) :
    (match e with
     | .lam .. => (throw "getExpr: non-canonical lam telescope" : Ixon.GetM Unit)
     | _ => pure ()) = pure () := by
  cases e with
  | lam bc ty body => exact (hne bc ty body rfl).elim
  | _ => rfl

theorem match_not_all_ok {e : Ixon.Expr} (hne : ∀ bc vc ty body, e ≠ .all bc vc ty body) :
    (match e with
     | .all .. => (throw "getExpr: non-canonical all telescope" : Ixon.GetM Unit)
     | _ => pure ()) = pure () := by
  cases e with
  | all bc vc ty body => exact (hne bc vc ty body rfl).elim
  | _ => rfl

theorem matchPattern_u64Value_array8 {types : Types} {heap : Heap F} {sz : Nat}
    {bs : Environment F Nat}
    (mt : W.matchPattern types heap
      (.array [(.bind "head"), (.bind "b1"), (.bind "b2"), (.bind "b3"),
               (.bind "b4"), (.bind "b5"), (.bind "b6"), (.bind "b7")])
      (u64Value sz) = .ok (some bs)) :
    bs = [
      ("head", .field ((sz % 256 : Nat) : F)),
      ("b1", .field ((sz / 256 % 256 : Nat) : F)),
      ("b2", .field ((sz / 65536 % 256 : Nat) : F)),
      ("b3", .field ((sz / 16777216 % 256 : Nat) : F)),
      ("b4", .field ((sz / 4294967296 % 256 : Nat) : F)),
      ("b5", .field ((sz / 1099511627776 % 256 : Nat) : F)),
      ("b6", .field ((sz / 281474976710656 % 256 : Nat) : F)),
      ("b7", .field ((sz / 72057594037927936 % 256 : Nat) : F))] := by
  unfold u64Value at mt
  rw [matchPattern_array] at mt
  simp only [List.length_cons, List.length_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq, Option.some.injEq] at mt
  exact mt.symm

/-- Bounded inductive hypothesis for `IxonDeserialize::get_expr` at any reader
offset `j` whose remaining slice `bytes.drop j` has length `< bound`. -/
def ExprRefinesAtUpTo (bytes : List UInt8) (bound : Nat) : Prop :=
  ∀ {j : Nat} {stream r : SourceValue F} {h h' : Heap F},
    (bytes.drop j).length < bound →
    Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop j) stream →
    EvalFn W "IxonDeserialize::get_expr" [stream] h r h' →
    Heap.Extends h h' ∧
    ∃ (e : Ixon.Expr) (n : Nat) (exprPtr restPtr : SourceValue F),
      0 < n ∧
      (bytes.drop (j + n)).length < (bytes.drop j).length ∧
      (∀ fuel, (bytes.drop j).length < fuel →
        Ixon.getExprFuel fuel { idx := j, bytes := ⟨bytes.toArray⟩ } =
          .ok e { idx := j + n, bytes := ⟨bytes.toArray⟩ }) ∧
      r = .tuple [exprPtr, restPtr] ∧
      RepExpr h' e exprPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (j + n)) restPtr

theorem ExprRefinesAtUpTo.mono {bytes : List UInt8} {b1 b2 : Nat} (hle : b1 ≤ b2)
    (h : ExprRefinesAtUpTo bytes b2) : ExprRefinesAtUpTo bytes b1 :=
  fun hlt rep ev => h (Nat.lt_of_lt_of_le hlt hle) rep ev

/-- **Refinement of `IxonDeserialize::get_app_telescope` at offset `i`** under
`ExprRefinesAtUpTo bytes ((bytes.drop i).length + 1)`. -/
theorem getAppTelescope_refines_at_of_ih (count : Nat) (hcount : count < 18446744073709551616) :
    ∀ {bytes : List UInt8} {i : Nat} {acc : Ixon.Expr}
      {accPtr stream r : SourceValue F} {h h' : Heap F},
      ExprRefinesAtUpTo bytes ((bytes.drop i).length + 1) →
      RepExpr h acc accPtr →
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream →
      EvalFn W "IxonDeserialize::get_app_telescope" [accPtr, stream, u64Value count] h r h' →
      Heap.Extends h h' ∧
      ∃ (res : Ixon.Expr) (n : Nat) (resPtr restPtr : SourceValue F),
        (bytes.drop (i + n)).length + count ≤ (bytes.drop i).length ∧
        (∀ fuel, (bytes.drop i).length < fuel →
          Ixon.getExprAppArgs (Ixon.getExprFuel fuel) count acc
            { idx := i, bytes := ⟨bytes.toArray⟩ } =
            .ok res { idx := i + n, bytes := ⟨bytes.toArray⟩ }) ∧
        r = .tuple [resPtr, restPtr] ∧
        RepExpr h' res resPtr ∧
        Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  induction count with
  | zero =>
    intro bytes i acc accPtr stream r h h' _ hacc hrep ev
    have body := ev.function_inv IxVM.IxonDeserialize.get_app_telescope.lookup
      (by simp [IxVM.IxonDeserialize.get_app_telescope, ControlLower.hasControl])
    simp only [IxVM.IxonDeserialize.get_app_telescope] at body
    obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
    obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
    obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
    obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
    obtain ⟨rfl, rfl⟩ := args14.nil_inv
    rw [instanceName_plain_some] at callee9
    obtain ⟨hiz, rfl⟩ := u64IsZero_refines hcount callee9
    simp only [↓reduceIte] at hiz; subst hiz
    rw [matchPattern_bind] at mt4
    simp only [Except.ok.injEq, Option.some.injEq] at mt4; subst mt4
    obtain ⟨v18, m19, bs20, body21, d22, sel23, d24⟩ := d5.matchValue_inv
    obtain ⟨l25, rfl⟩ := d22.var_inv; simp at l25; subst l25
    rcases selectArm_literal_inv sel23 with ⟨_, rfl, rfl⟩ | ⟨hc26, _⟩
    · obtain ⟨vs28, args29, rfl⟩ := d24.tuple_inv
      obtain ⟨v30, vs31, m32, rfl, d33, args34⟩ := args29.cons_inv
      obtain ⟨l35, rfl⟩ := d33.var_inv; simp at l35; subst l35
      obtain ⟨v40, vs41, m42, rfl, d43, args44⟩ := args34.cons_inv
      obtain ⟨l45, rfl⟩ := d43.var_inv; simp at l45; subst l45
      obtain ⟨rfl, rfl⟩ := args44.nil_inv
      refine ⟨Heap.Extends.refl h', acc, 0, accPtr, stream, by simp,
        fun _ _ => by simp [Ixon.getExprAppArgs, pure, EStateM.pure], rfl, hacc,
        by simpa using hrep⟩
    · exact (hc26 rfl).elim
  | succ count ih =>
    intro bytes i acc accPtr stream r h h' hIH hacc hrep ev
    have body := ev.function_inv IxVM.IxonDeserialize.get_app_telescope.lookup
      (by simp [IxVM.IxonDeserialize.get_app_telescope, ControlLower.hasControl])
    simp only [IxVM.IxonDeserialize.get_app_telescope] at body
    obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
    obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
    obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
    obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
    obtain ⟨rfl, rfl⟩ := args14.nil_inv
    rw [instanceName_plain_some] at callee9
    obtain ⟨hiz, rfl⟩ := u64IsZero_refines hcount callee9
    simp only [Nat.succ_ne_zero, ↓reduceIte] at hiz; subst hiz
    rw [matchPattern_bind] at mt4
    simp only [Except.ok.injEq, Option.some.injEq] at mt4; subst mt4
    obtain ⟨v18, m19, bs20, body21, d22, sel23, d24⟩ := d5.matchValue_inv
    obtain ⟨l25, rfl⟩ := d22.var_inv; simp at l25; subst l25
    rcases selectArm_literal_inv sel23 with ⟨hc26, _, _⟩ | ⟨_, sel27⟩
    · simp at hc26
    · rcases selectArm_literal_inv sel27 with ⟨_, rfl, rfl⟩ | ⟨hc28, _⟩
      · obtain ⟨v30, m31, bs32, d33, mt34, d35⟩ := d24.letValue_inv
        obtain ⟨vs36, m37, args38, callee39⟩ := d33.call_inv
        obtain ⟨v40, vs41, m42, rfl, d43, args44⟩ := args38.cons_inv
        obtain ⟨l45, rfl⟩ := d43.var_inv; simp at l45; subst l45
        obtain ⟨rfl, rfl⟩ := args44.nil_inv
        rw [instanceName_plain_some] at callee39
        obtain ⟨ext1, arg, n1, argPtr, restPtr1, hn1_pos, hdrop_lt1, hfuel_arg, rfl, argRep, hrep1⟩ :=
          hIH (Nat.lt_succ_self _) hrep callee39
        obtain rfl := matchPattern_tuple2_bind rfl mt34
        obtain ⟨vs46, m47, args48, callee49⟩ := d35.call_inv
        obtain ⟨v50, vs51, m52, rfl, d53, args54⟩ := args48.cons_inv
        obtain ⟨v55, m56, d57, rfl, rfl⟩ := d53.store_inv
        obtain ⟨vs58, args59, rfl⟩ := d57.construct_inv
        obtain ⟨v60, vs61, m62, rfl, d63, args64⟩ := args59.cons_inv
        obtain ⟨l65, rfl⟩ := d63.var_inv; simp at l65; subst l65
        obtain ⟨v66, vs67, m68, rfl, d69, args70⟩ := args64.cons_inv
        obtain ⟨l71, rfl⟩ := d69.var_inv; simp at l71; subst l71
        obtain ⟨rfl, rfl⟩ := args70.nil_inv
        obtain ⟨v72, vs73, m74, rfl, d75, args76⟩ := args54.cons_inv
        obtain ⟨l77, rfl⟩ := d75.var_inv; simp at l77; subst l77
        obtain ⟨v78, vs79, m80, rfl, d81, args82⟩ := args76.cons_inv
        obtain ⟨vs83, m84, args85, callee86⟩ := d81.call_inv
        obtain ⟨v87, vs88, m89, rfl, d90, args91⟩ := args85.cons_inv
        obtain ⟨l92, rfl⟩ := d90.var_inv; simp at l92; subst l92
        obtain ⟨rfl, rfl⟩ := args91.nil_inv
        rw [instanceName_plain_some] at callee86
        obtain ⟨hsp, rfl⟩ := u64SaturatingPred_refines hcount callee86
        simp only [Nat.add_sub_cancel] at hsp; subst hsp
        obtain ⟨rfl, rfl⟩ := args82.nil_inv
        simp only [instanceName_plain_some, value_type_construct] at callee49
        let cellApp : SourceValue F := .construct "Ixon::Expr" "App" [accPtr, argPtr]
        have extStore : Heap.Extends m56 (m56 ++ [cellApp]) := Heap.Extends.snoc m56 cellApp
        have happRep : RepExpr (m56 ++ [cellApp]) (.app acc arg) (.ptr (.enum "Ixon::Expr") m56.length) :=
          .app (by simp [cellApp]) ((hacc.mono ext1).mono extStore) (argRep.mono extStore)
        have hrep1' := Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum extStore hrep1
        have hIH' : ExprRefinesAtUpTo bytes ((bytes.drop (i + n1)).length + 1) :=
          hIH.mono (by omega)
        obtain ⟨ext2, res, n2, resPtr, restPtr2, hprog2, hfuel_rest, rfl, resRep, hrep2⟩ :=
          ih (by omega) hIH' happRep hrep1' callee49
        rw [Nat.add_assoc] at hprog2 hrep2
        refine ⟨(ext1.trans extStore).trans ext2, res, n1 + n2, resPtr, restPtr2,
          by omega, fun fuel hfuel => ?_, rfl, resRep, hrep2⟩
        have harg_ok := hfuel_arg fuel hfuel
        have hrest_ok := hfuel_rest fuel (by omega)
        rw [Nat.add_assoc] at hrest_ok
        simp [Ixon.getExprAppArgs, bind, EStateM.bind, harg_ok, hrest_ok]
      · exact (hc28 rfl).elim

/-- **Refinement of `IxonDeserialize::get_lam_telescope` at offset `i`** under
`ExprRefinesAtUpTo bytes ((bytes.drop i).length + 1)`. -/
theorem getLamTelescope_refines_at_of_ih (count : Nat) (hcount : count < 18446744073709551616) :
    ∀ {bytes : List UInt8} {i : Nat} {stream r : SourceValue F} {h h' : Heap F},
      ExprRefinesAtUpTo bytes ((bytes.drop i).length + 1) →
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream →
      EvalFn W "IxonDeserialize::get_lam_telescope" [stream, u64Value count] h r h' →
      Heap.Extends h h' ∧
      ∃ (binders : List (Ixon.BinderContract × Ixon.Expr)) (body : Ixon.Expr)
        (nb n : Nat) (resPtr restPtr : SourceValue F),
        0 < n ∧
        (bytes.drop (i + n)).length + (count * 2 + 1) ≤ (bytes.drop i).length ∧
        (∀ bc ty b, body ≠ .lam bc ty b) ∧
        (∀ fuel, (bytes.drop i).length < fuel →
          Ixon.getExprLamBinders (Ixon.getExprFuel fuel) count
            { idx := i, bytes := ⟨bytes.toArray⟩ } =
            .ok binders { idx := i + nb, bytes := ⟨bytes.toArray⟩ } ∧
          Ixon.getExprFuel fuel { idx := i + nb, bytes := ⟨bytes.toArray⟩ } =
            .ok body { idx := i + n, bytes := ⟨bytes.toArray⟩ }) ∧
        r = .tuple [resPtr, restPtr] ∧
        RepExpr h' (binders.foldr (fun (uses, ty) result => .lam uses ty result) body) resPtr ∧
        Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  induction count with
  | zero =>
    intro bytes i stream r h h' hIH hrep ev
    have body := ev.function_inv IxVM.IxonDeserialize.get_lam_telescope.lookup
      (by simp [IxVM.IxonDeserialize.get_lam_telescope, ControlLower.hasControl])
    simp only [IxVM.IxonDeserialize.get_lam_telescope] at body
    obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
    obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
    obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
    obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
    obtain ⟨rfl, rfl⟩ := args14.nil_inv
    rw [instanceName_plain_some] at callee9
    obtain ⟨hiz, rfl⟩ := u64IsZero_refines hcount callee9
    simp only [↓reduceIte] at hiz; subst hiz
    rw [matchPattern_bind] at mt4
    simp only [Except.ok.injEq, Option.some.injEq] at mt4; subst mt4
    obtain ⟨v18, m19, bs20, body21, d22, sel23, d24⟩ := d5.matchValue_inv
    obtain ⟨l25, rfl⟩ := d22.var_inv; simp at l25; subst l25
    rcases selectArm_literal_inv sel23 with ⟨_, rfl, rfl⟩ | ⟨hc26, _⟩
    · obtain ⟨v27, m28, bs29, d30, mt31, d32⟩ := d24.letValue_inv
      obtain ⟨vs33, m34, args35, callee36⟩ := d30.call_inv
      obtain ⟨v37, vs38, m39, rfl, d40, args41⟩ := args35.cons_inv
      obtain ⟨l42, rfl⟩ := d40.var_inv; simp at l42; subst l42
      obtain ⟨rfl, rfl⟩ := args41.nil_inv
      rw [instanceName_plain_some] at callee36
      obtain ⟨ext1, bodyExpr, n1, bodyPtr, restPtr1, hn1_pos, hdrop_lt1, hfuel_body, rfl, bodyRep, hrep1⟩ :=
        hIH (Nat.lt_succ_self _) hrep callee36
      obtain rfl := matchPattern_tuple2_bind rfl mt31
      obtain ⟨⟨v_load, hload, hmp⟩, d_ok⟩ := evalExpr_reject_ctor_inv rfl d32
      have hne_lam := repExpr_ne_lam bodyRep hload hmp
      obtain ⟨vs50, args51, rfl⟩ := d_ok.tuple_inv
      obtain ⟨v52, vs53, m54, rfl, d55, args56⟩ := args51.cons_inv
      obtain ⟨l57, rfl⟩ := d55.var_inv; simp at l57; subst l57
      obtain ⟨v58, vs59, m60, rfl, d61, args62⟩ := args56.cons_inv
      obtain ⟨l63, rfl⟩ := d61.var_inv; simp at l63; subst l63
      obtain ⟨rfl, rfl⟩ := args62.nil_inv
      refine ⟨ext1, [], bodyExpr, 0, n1, bodyPtr, restPtr1, hn1_pos, by omega, hne_lam,
        fun fuel hfuel => ⟨by simp [Ixon.getExprLamBinders, pure, EStateM.pure],
          by simpa using hfuel_body fuel hfuel⟩,
        rfl, bodyRep, hrep1⟩
    · exact (hc26 rfl).elim
  | succ count ih =>
    intro bytes i stream r h h' hIH hrep ev
    have body := ev.function_inv IxVM.IxonDeserialize.get_lam_telescope.lookup
      (by simp [IxVM.IxonDeserialize.get_lam_telescope, ControlLower.hasControl])
    simp only [IxVM.IxonDeserialize.get_lam_telescope] at body
    obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
    obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
    obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
    obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
    obtain ⟨rfl, rfl⟩ := args14.nil_inv
    rw [instanceName_plain_some] at callee9
    obtain ⟨hiz, rfl⟩ := u64IsZero_refines hcount callee9
    simp only [Nat.succ_ne_zero, ↓reduceIte] at hiz; subst hiz
    rw [matchPattern_bind] at mt4
    simp only [Except.ok.injEq, Option.some.injEq] at mt4; subst mt4
    obtain ⟨v18, m19, bs20, body21, d22, sel23, d24⟩ := d5.matchValue_inv
    obtain ⟨l25, rfl⟩ := d22.var_inv; simp at l25; subst l25
    rcases selectArm_literal_inv sel23 with ⟨hc26, _, _⟩ | ⟨_, sel27⟩
    · simp at hc26
    · rcases selectArm_literal_inv sel27 with ⟨_, rfl, rfl⟩ | ⟨hc28, _⟩
      · obtain ⟨v30, m31, bs32, d33, mt34, d35⟩ := d24.letValue_inv
        obtain ⟨vs36, m37, args38, callee39⟩ := d33.call_inv
        obtain ⟨v40, vs41, m42, rfl, d43, args44⟩ := args38.cons_inv
        obtain ⟨l45, rfl⟩ := d43.var_inv; simp at l45; subst l45
        obtain ⟨rfl, rfl⟩ := args44.nil_inv
        rw [instanceName_plain_some] at callee39
        obtain ⟨rfl, bc, restPtr1, hlen_mode, hok_mode, hrep1, rfl⟩ :=
          getLamMode_refines_at hrep callee39
        obtain rfl := matchPattern_tuple2_bind rfl mt34
        obtain ⟨v46, m47, bs48, d49, mt50, d51⟩ := d35.letValue_inv
        obtain ⟨vs52, m53, args54, callee55⟩ := d49.call_inv
        obtain ⟨v56, vs57, m58, rfl, d59, args60⟩ := args54.cons_inv
        obtain ⟨l61, rfl⟩ := d59.var_inv; simp at l61; subst l61
        obtain ⟨rfl, rfl⟩ := args60.nil_inv
        rw [instanceName_plain_some] at callee55
        obtain ⟨ext1, ty, n2, tyPtr, restPtr2, hn2_pos, hdrop_lt2, hfuel_ty, rfl, tyRep, hrep2⟩ :=
          hIH (by omega) hrep1 callee55
        obtain rfl := matchPattern_tuple2_bind rfl mt50
        obtain ⟨v62, m63, bs64, d65, mt66, d67⟩ := d51.letValue_inv
        obtain ⟨vs68, m69, args70, callee71⟩ := d65.call_inv
        obtain ⟨v72, vs73, m74, rfl, d75, args76⟩ := args70.cons_inv
        obtain ⟨l77, rfl⟩ := d75.var_inv; simp at l77; subst l77
        obtain ⟨v78, vs79, m80, rfl, d81, args82⟩ := args76.cons_inv
        obtain ⟨vs83, m84, args85, callee86⟩ := d81.call_inv
        obtain ⟨v87, vs88, m89, rfl, d90, args91⟩ := args85.cons_inv
        obtain ⟨l92, rfl⟩ := d90.var_inv; simp at l92; subst l92
        obtain ⟨rfl, rfl⟩ := args91.nil_inv
        rw [instanceName_plain_some] at callee86
        obtain ⟨hsp, rfl⟩ := u64SaturatingPred_refines hcount callee86
        simp only [Nat.add_sub_cancel] at hsp; subst hsp
        obtain ⟨rfl, rfl⟩ := args82.nil_inv
        rw [instanceName_plain_some] at callee71
        have hIH2 : ExprRefinesAtUpTo bytes ((bytes.drop (i + 1 + n2)).length + 1) :=
          hIH.mono (by omega)
        obtain ⟨ext2, tailBinders, bodyExpr, nb, n3, innerPtr, restPtr3,
            hn3_pos, hprog3, hne_lam, hfuel_tail, rfl, innerRep, hrep3⟩ :=
          ih (by omega) hIH2 hrep2 callee71
        obtain rfl := matchPattern_tuple2_bind rfl mt66
        obtain ⟨vs93, args94, rfl⟩ := d67.tuple_inv
        obtain ⟨v95, vs96, m97, rfl, d98, args99⟩ := args94.cons_inv
        obtain ⟨v100, m101, d102, rfl, rfl⟩ := d98.store_inv
        obtain ⟨vs103, args104, rfl⟩ := d102.construct_inv
        obtain ⟨v105, vs106, m107, rfl, d108, args109⟩ := args104.cons_inv
        obtain ⟨l110, rfl⟩ := d108.var_inv; simp at l110; subst l110
        obtain ⟨v111, vs112, m113, rfl, d114, args115⟩ := args109.cons_inv
        obtain ⟨l116, rfl⟩ := d114.var_inv; simp at l116; subst l116
        obtain ⟨v117, vs118, m119, rfl, d120, args121⟩ := args115.cons_inv
        obtain ⟨l122, rfl⟩ := d120.var_inv; simp at l122; subst l122
        obtain ⟨rfl, rfl⟩ := args121.nil_inv
        obtain ⟨v123, vs124, m125, rfl, d126, args127⟩ := args99.cons_inv
        obtain ⟨l128, rfl⟩ := d126.var_inv; simp at l128; subst l128
        obtain ⟨rfl, rfl⟩ := args127.nil_inv
        simp only [instanceName_plain_some, value_type_construct]
        let cellLam : SourceValue F := .construct "Ixon::Expr" "Lam" [binderContractValue bc, tyPtr, innerPtr]
        have extStore : Heap.Extends m101 (m101 ++ [cellLam]) := Heap.Extends.snoc m101 cellLam
        have lamRep : RepExpr (m101 ++ [cellLam])
            (((bc, ty) :: tailBinders).foldr (fun (uses, ty) result => .lam uses ty result) bodyExpr)
            (.ptr (.enum "Ixon::Expr") m101.length) :=
          .lam (by simp [cellLam]) ((tyRep.mono ext2).mono extStore) (innerRep.mono extStore)
        have hrep3' := Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum extStore hrep3
        rw [show i + 1 + n2 + n3 = i + (1 + n2 + n3) by omega] at hprog3 hrep3'
        refine ⟨(ext1.trans ext2).trans extStore, (bc, ty) :: tailBinders, bodyExpr,
          1 + n2 + nb, 1 + n2 + n3, .ptr (.enum "Ixon::Expr") m101.length, restPtr3,
          by omega, by omega, hne_lam, fun fuel hfuel => ?_, rfl, lamRep, hrep3'⟩
        have hty_ok := hfuel_ty fuel (by omega)
        obtain ⟨htail_b, htail_body⟩ := hfuel_tail fuel (by omega)
        rw [show i + 1 + n2 + nb = i + (1 + n2 + nb) by omega] at htail_b htail_body
        rw [show i + 1 + n2 + n3 = i + (1 + n2 + n3) by omega] at htail_body
        refine ⟨?_, htail_body⟩
        simp [Ixon.getExprLamBinders, bind, EStateM.bind, hok_mode, hty_ok, htail_b,
          pure, EStateM.pure]
      · exact (hc28 rfl).elim

/-- **Refinement of `IxonDeserialize::get_all_telescope` at offset `i`** under
`ExprRefinesAtUpTo bytes ((bytes.drop i).length + 1)`. -/
theorem getAllTelescope_refines_at_of_ih (count : Nat) (hcount : count < 18446744073709551616) :
    ∀ {bytes : List UInt8} {i : Nat} {stream r : SourceValue F} {h h' : Heap F},
      ExprRefinesAtUpTo bytes ((bytes.drop i).length + 1) →
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream →
      EvalFn W "IxonDeserialize::get_all_telescope" [stream, u64Value count] h r h' →
      Heap.Extends h h' ∧
      ∃ (binders : List (Ixon.BinderContract × Ixon.ValueContract × Ixon.Expr)) (body : Ixon.Expr)
        (nb n : Nat) (resPtr restPtr : SourceValue F),
        0 < n ∧
        (bytes.drop (i + n)).length + (count * 2 + 1) ≤ (bytes.drop i).length ∧
        (∀ bc vc ty b, body ≠ .all bc vc ty b) ∧
        (∀ fuel, (bytes.drop i).length < fuel →
          Ixon.getExprAllBinders (Ixon.getExprFuel fuel) count
            { idx := i, bytes := ⟨bytes.toArray⟩ } =
            .ok binders { idx := i + nb, bytes := ⟨bytes.toArray⟩ } ∧
          Ixon.getExprFuel fuel { idx := i + nb, bytes := ⟨bytes.toArray⟩ } =
            .ok body { idx := i + n, bytes := ⟨bytes.toArray⟩ }) ∧
        r = .tuple [resPtr, restPtr] ∧
        RepExpr h' (binders.foldr (fun (uses, owned, ty) result => .all uses owned ty result) body) resPtr ∧
        Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  induction count with
  | zero =>
    intro bytes i stream r h h' hIH hrep ev
    have body := ev.function_inv IxVM.IxonDeserialize.get_all_telescope.lookup
      (by simp [IxVM.IxonDeserialize.get_all_telescope, ControlLower.hasControl])
    simp only [IxVM.IxonDeserialize.get_all_telescope] at body
    obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
    obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
    obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
    obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
    obtain ⟨rfl, rfl⟩ := args14.nil_inv
    rw [instanceName_plain_some] at callee9
    obtain ⟨hiz, rfl⟩ := u64IsZero_refines hcount callee9
    simp only [↓reduceIte] at hiz; subst hiz
    rw [matchPattern_bind] at mt4
    simp only [Except.ok.injEq, Option.some.injEq] at mt4; subst mt4
    obtain ⟨v18, m19, bs20, body21, d22, sel23, d24⟩ := d5.matchValue_inv
    obtain ⟨l25, rfl⟩ := d22.var_inv; simp at l25; subst l25
    rcases selectArm_literal_inv sel23 with ⟨_, rfl, rfl⟩ | ⟨hc26, _⟩
    · obtain ⟨v27, m28, bs29, d30, mt31, d32⟩ := d24.letValue_inv
      obtain ⟨vs33, m34, args35, callee36⟩ := d30.call_inv
      obtain ⟨v37, vs38, m39, rfl, d40, args41⟩ := args35.cons_inv
      obtain ⟨l42, rfl⟩ := d40.var_inv; simp at l42; subst l42
      obtain ⟨rfl, rfl⟩ := args41.nil_inv
      rw [instanceName_plain_some] at callee36
      obtain ⟨ext1, bodyExpr, n1, bodyPtr, restPtr1, hn1_pos, hdrop_lt1, hfuel_body, rfl, bodyRep, hrep1⟩ :=
        hIH (Nat.lt_succ_self _) hrep callee36
      obtain rfl := matchPattern_tuple2_bind rfl mt31
      obtain ⟨⟨v_load, hload, hmp⟩, d_ok⟩ := evalExpr_reject_ctor_inv rfl d32
      have hne_all := repExpr_ne_all bodyRep hload hmp
      obtain ⟨vs50, args51, rfl⟩ := d_ok.tuple_inv
      obtain ⟨v52, vs53, m54, rfl, d55, args56⟩ := args51.cons_inv
      obtain ⟨l57, rfl⟩ := d55.var_inv; simp at l57; subst l57
      obtain ⟨v58, vs59, m60, rfl, d61, args62⟩ := args56.cons_inv
      obtain ⟨l63, rfl⟩ := d61.var_inv; simp at l63; subst l63
      obtain ⟨rfl, rfl⟩ := args62.nil_inv
      refine ⟨ext1, [], bodyExpr, 0, n1, bodyPtr, restPtr1, hn1_pos, by omega, hne_all,
        fun fuel hfuel => ⟨by simp [Ixon.getExprAllBinders, pure, EStateM.pure],
          by simpa using hfuel_body fuel hfuel⟩,
        rfl, bodyRep, hrep1⟩
    · exact (hc26 rfl).elim
  | succ count ih =>
    intro bytes i stream r h h' hIH hrep ev
    have body := ev.function_inv IxVM.IxonDeserialize.get_all_telescope.lookup
      (by simp [IxVM.IxonDeserialize.get_all_telescope, ControlLower.hasControl])
    simp only [IxVM.IxonDeserialize.get_all_telescope] at body
    obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
    obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
    obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
    obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
    obtain ⟨rfl, rfl⟩ := args14.nil_inv
    rw [instanceName_plain_some] at callee9
    obtain ⟨hiz, rfl⟩ := u64IsZero_refines hcount callee9
    simp only [Nat.succ_ne_zero, ↓reduceIte] at hiz; subst hiz
    rw [matchPattern_bind] at mt4
    simp only [Except.ok.injEq, Option.some.injEq] at mt4; subst mt4
    obtain ⟨v18, m19, bs20, body21, d22, sel23, d24⟩ := d5.matchValue_inv
    obtain ⟨l25, rfl⟩ := d22.var_inv; simp at l25; subst l25
    rcases selectArm_literal_inv sel23 with ⟨hc26, _, _⟩ | ⟨_, sel27⟩
    · simp at hc26
    · rcases selectArm_literal_inv sel27 with ⟨_, rfl, rfl⟩ | ⟨hc28, _⟩
      · obtain ⟨v30, m31, bs32, d33, mt34, d35⟩ := d24.letValue_inv
        obtain ⟨vs36, m37, args38, callee39⟩ := d33.call_inv
        obtain ⟨v40, vs41, m42, rfl, d43, args44⟩ := args38.cons_inv
        obtain ⟨l45, rfl⟩ := d43.var_inv; simp at l45; subst l45
        obtain ⟨rfl, rfl⟩ := args44.nil_inv
        rw [instanceName_plain_some] at callee39
        obtain ⟨rfl, bc, vc, restPtr1, hlen_mode, _, ⟨bits, hu8_bits, hunpack_bits⟩, hrep1, rfl⟩ :=
          getAllMode_refines_at hrep callee39
        obtain rfl := matchPattern_tuple2_bind rfl mt34
        obtain ⟨v45, m46, bs47, d48, mt49, d50⟩ := d35.letValue_inv
        obtain ⟨l51, rfl⟩ := d48.var_inv; simp at l51; subst l51
        obtain rfl := matchPattern_tuple2_bind rfl mt49
        obtain ⟨v52, m53, bs54, d55, mt56, d57⟩ := d50.letValue_inv
        obtain ⟨vs58, m59, args60, callee61⟩ := d55.call_inv
        obtain ⟨v62, vs63, m64, rfl, d65, args66⟩ := args60.cons_inv
        obtain ⟨l67, rfl⟩ := d65.var_inv; simp at l67; subst l67
        obtain ⟨rfl, rfl⟩ := args66.nil_inv
        rw [instanceName_plain_some] at callee61
        obtain ⟨ext1, ty, n2, tyPtr, restPtr2, hn2_pos, hdrop_lt2, hfuel_ty, rfl, tyRep, hrep2⟩ :=
          hIH (by omega) hrep1 callee61
        obtain rfl := matchPattern_tuple2_bind rfl mt56
        obtain ⟨v68, m69, bs70, d71, mt72, d73⟩ := d57.letValue_inv
        obtain ⟨vs74, m75, args76, callee77⟩ := d71.call_inv
        obtain ⟨v78, vs79, m80, rfl, d81, args82⟩ := args76.cons_inv
        obtain ⟨l83, rfl⟩ := d81.var_inv; simp at l83; subst l83
        obtain ⟨v84, vs85, m86, rfl, d87, args88⟩ := args82.cons_inv
        obtain ⟨vs89, m90, args91, callee92⟩ := d87.call_inv
        obtain ⟨v93, vs94, m95, rfl, d96, args97⟩ := args91.cons_inv
        obtain ⟨l98, rfl⟩ := d96.var_inv; simp at l98; subst l98
        obtain ⟨rfl, rfl⟩ := args97.nil_inv
        rw [instanceName_plain_some] at callee92
        obtain ⟨hsp, rfl⟩ := u64SaturatingPred_refines hcount callee92
        simp only [Nat.add_sub_cancel] at hsp; subst hsp
        obtain ⟨rfl, rfl⟩ := args88.nil_inv
        rw [instanceName_plain_some] at callee77
        have hIH2 : ExprRefinesAtUpTo bytes ((bytes.drop (i + 1 + n2)).length + 1) :=
          hIH.mono (by omega)
        obtain ⟨ext2, tailBinders, bodyExpr, nb, n3, innerPtr, restPtr3,
            hn3_pos, hprog3, hne_all, hfuel_tail, rfl, innerRep, hrep3⟩ :=
          ih (by omega) hIH2 hrep2 callee77
        obtain rfl := matchPattern_tuple2_bind rfl mt72
        obtain ⟨vs99, args100, rfl⟩ := d73.tuple_inv
        obtain ⟨v101, vs102, m103, rfl, d104, args105⟩ := args100.cons_inv
        obtain ⟨v106, m107, d108, rfl, rfl⟩ := d104.store_inv
        obtain ⟨vs109, args110, rfl⟩ := d108.construct_inv
        obtain ⟨v111, vs112, m113, rfl, d114, args115⟩ := args110.cons_inv
        obtain ⟨l116, rfl⟩ := d114.var_inv; simp at l116; subst l116
        obtain ⟨v117, vs118, m119, rfl, d120, args121⟩ := args115.cons_inv
        obtain ⟨l122, rfl⟩ := d120.var_inv; simp at l122; subst l122
        obtain ⟨v123, vs124, m125, rfl, d126, args127⟩ := args121.cons_inv
        obtain ⟨l128, rfl⟩ := d126.var_inv; simp at l128; subst l128
        obtain ⟨v129, vs130, m131, rfl, d132, args133⟩ := args127.cons_inv
        obtain ⟨l134, rfl⟩ := d132.var_inv; simp at l134; subst l134
        obtain ⟨rfl, rfl⟩ := args133.nil_inv
        obtain ⟨v135, vs136, m137, rfl, d138, args139⟩ := args105.cons_inv
        obtain ⟨l140, rfl⟩ := d138.var_inv; simp at l140; subst l140
        obtain ⟨rfl, rfl⟩ := args139.nil_inv
        simp only [instanceName_plain_some, value_type_construct]
        let cellAll : SourceValue F := .construct "Ixon::Expr" "All"
          [binderContractValue bc, valueContractValue vc, tyPtr, innerPtr]
        have extStore : Heap.Extends m107 (m107 ++ [cellAll]) := Heap.Extends.snoc m107 cellAll
        have allRep : RepExpr (m107 ++ [cellAll])
            (((bc, vc, ty) :: tailBinders).foldr (fun (uses, owned, ty) result => .all uses owned ty result) bodyExpr)
            (.ptr (.enum "Ixon::Expr") m107.length) :=
          .all (by simp [cellAll]) ((tyRep.mono ext2).mono extStore) (innerRep.mono extStore)
        have hrep3' := Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum extStore hrep3
        rw [show i + 1 + n2 + n3 = i + (1 + n2 + n3) by omega] at hprog3 hrep3'
        refine ⟨(ext1.trans ext2).trans extStore, (bc, vc, ty) :: tailBinders, bodyExpr,
          1 + n2 + nb, 1 + n2 + n3, .ptr (.enum "Ixon::Expr") m107.length, restPtr3,
          by omega, by omega, hne_all, fun fuel hfuel => ?_, rfl, allRep, hrep3'⟩
        have hty_ok := hfuel_ty fuel (by omega)
        obtain ⟨htail_b, htail_body⟩ := hfuel_tail fuel (by omega)
        rw [show i + 1 + n2 + nb = i + (1 + n2 + nb) by omega] at htail_b htail_body
        rw [show i + 1 + n2 + n3 = i + (1 + n2 + n3) by omega] at htail_body
        refine ⟨?_, htail_body⟩
        simp [Ixon.getExprAllBinders, bind, EStateM.bind, hu8_bits, hunpack_bits, hty_ok,
          htail_b, pure, EStateM.pure]
      · exact (hc28 rfl).elim

/-- **Refinement of `IxonDeserialize::get_expr_let` at offset `i`** under
`ExprRefinesAtUpTo bytes ((bytes.drop i).length + 1)`. -/
theorem getExprLet_refines_at_of_ih (sz : UInt64) :
    ∀ {bytes : List UInt8} {i : Nat} {stream r : SourceValue F} {h h' : Heap F},
      ExprRefinesAtUpTo bytes ((bytes.drop i).length + 1) →
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream →
      EvalFn W "IxonDeserialize::get_expr_let" [stream, u64Value sz.toNat] h r h' →
      Heap.Extends h h' ∧
      sz.toNat < 4 ∧
      ∃ (bc : Ixon.BinderContract) (ty val body : Ixon.Expr)
        (n : Nat) (resPtr restPtr : SourceValue F),
        0 < n ∧
        (bytes.drop (i + n)).length < (bytes.drop i).length ∧
        (∀ fuel, (bytes.drop i).length < fuel →
          (do
            let binder ← Ixon.getBinderContract
            let some contract := Ixon.LetContract.ofFlags? sz binder
              | throw "getExpr: invalid let flags"
            let ty ← Ixon.getExprFuel fuel
            let val ← Ixon.getExprFuel fuel
            let body ← Ixon.getExprFuel fuel
            return Ixon.Expr.letE contract ty val body : Ixon.GetM Ixon.Expr)
            { idx := i, bytes := ⟨bytes.toArray⟩ } =
            .ok (.letE (letContractOfFlags sz.toNat bc) ty val body)
              { idx := i + n, bytes := ⟨bytes.toArray⟩ }) ∧
        r = .tuple [resPtr, restPtr] ∧
        RepExpr h' (.letE (letContractOfFlags sz.toNat bc) ty val body) resPtr ∧
        Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  intro bytes i stream r h h' hIH hrep ev
  have body := ev.function_inv IxVM.IxonDeserialize.get_expr_let.lookup
    (by simp [IxVM.IxonDeserialize.get_expr_let, ControlLower.hasControl])
  simp only [IxVM.IxonDeserialize.get_expr_let] at body
  obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
  obtain ⟨l3, rfl⟩ := d3.var_inv; simp at l3; subst l3
  obtain rfl := matchPattern_u64Value_array8 mt4
  obtain ⟨_, m6, bs7, d8, mt9, d10⟩ := d5.letValue_inv
  obtain ⟨vs11, args12, app13⟩ := d8.builtin_inv
  obtain ⟨v14, vs15, m16, rfl, d17, args18⟩ := args12.cons_inv
  obtain ⟨x1, y7, _, d_add6, d_b7, op7⟩ := d17.binary_inv
  obtain ⟨x2, y6, _, d_add5, d_b6, op6⟩ := d_add6.binary_inv
  obtain ⟨x3, y5, _, d_add4, d_b5, op5⟩ := d_add5.binary_inv
  obtain ⟨x4, y4, _, d_add3, d_b4, op4⟩ := d_add4.binary_inv
  obtain ⟨x5, y3, _, d_add2, d_b3, op3⟩ := d_add3.binary_inv
  obtain ⟨y1, y2, _, d_b1, d_b2, op2⟩ := d_add2.binary_inv
  obtain ⟨lb1, rfl⟩ := evalExpr_toField_var d_b1; simp at lb1; subst lb1
  obtain ⟨lb2, rfl⟩ := evalExpr_toField_var d_b2; simp at lb2; subst lb2
  obtain ⟨lb3, rfl⟩ := evalExpr_toField_var d_b3; simp at lb3; subst lb3
  obtain ⟨lb4, rfl⟩ := evalExpr_toField_var d_b4; simp at lb4; subst lb4
  obtain ⟨lb5, rfl⟩ := evalExpr_toField_var d_b5; simp at lb5; subst lb5
  obtain ⟨lb6, rfl⟩ := evalExpr_toField_var d_b6; simp at lb6; subst lb6
  obtain ⟨lb7, rfl⟩ := evalExpr_toField_var d_b7; simp at lb7; subst lb7
  simp only [evalBinOp, Except.ok.injEq] at op2; subst op2
  simp only [evalBinOp, Except.ok.injEq] at op3; subst op3
  simp only [evalBinOp, Except.ok.injEq] at op4; subst op4
  simp only [evalBinOp, Except.ok.injEq] at op5; subst op5
  simp only [evalBinOp, Except.ok.injEq] at op6; subst op6
  simp only [evalBinOp, Except.ok.injEq] at op7; subst op7
  obtain ⟨v19, vs20, m21, rfl, d22, args23⟩ := args18.cons_inv
  obtain ⟨rfl, rfl⟩ := d22.literal_inv
  obtain ⟨rfl, rfl⟩ := args23.nil_inv
  simp only [Builtin.apply, evalAssertEq, Value.pointerFree, Bool.and_self,
    ↓reduceIte, Value.field.injEq] at app13
  split_ifs at app13 with hsum_eq
  have hsz_lt256 : sz.toNat < 256 := by
    have hlt_bound := sz.toNat_lt
    let S := sz.toNat / 256 % 256 + sz.toNat / 65536 % 256 + sz.toNat / 16777216 % 256 +
      sz.toNat / 4294967296 % 256 + sz.toNat / 1099511627776 % 256 +
      sz.toNat / 281474976710656 % 256 + sz.toNat / 72057594037927936 % 256
    have hcast : ((S : Nat) : F) = 0 := by
      dsimp [S]
      push_cast
      exact hsum_eq
    have hval := congrArg ZMod.val hcast
    rw [zmod_val_natCast_of_lt (by dsimp [S]; omega), ZMod.val_zero] at hval
    dsimp [S] at hval
    have hb7 : sz.toNat / 72057594037927936 % 256 = 0 := by omega
    have hb6 : sz.toNat / 281474976710656 % 256 = 0 := by omega
    have hb5 : sz.toNat / 1099511627776 % 256 = 0 := by omega
    have hb4 : sz.toNat / 4294967296 % 256 = 0 := by omega
    have hb3 : sz.toNat / 16777216 % 256 = 0 := by omega
    have hb2 : sz.toNat / 65536 % 256 = 0 := by omega
    have hb1 : sz.toNat / 256 % 256 = 0 := by omega
    have hlt7 : sz.toNat < 72057594037927936 := by omega
    have hlt6 : sz.toNat < 281474976710656 := by omega
    have hlt5 : sz.toNat < 1099511627776 := by omega
    have hlt4 : sz.toNat < 4294967296 := by omega
    have hlt3 : sz.toNat < 16777216 := by omega
    have hlt2 : sz.toNat < 65536 := by omega
    omega
  have hmod256 : sz.toNat % 256 = sz.toNat := Nat.mod_eq_of_lt hsz_lt256
  rw [matchPattern_wildcard] at mt9
  simp only [Except.ok.injEq, Option.some.injEq] at mt9; subst mt9
  obtain ⟨_, m24, bs25, d26, mt27, d28⟩ := d10.letValue_inv
  obtain ⟨vs29, args30, app31⟩ := d26.builtin_inv
  obtain ⟨v32, vs33, m34, rfl, d35, args36⟩ := args30.cons_inv
  obtain ⟨vs37, m38, args39, callee40⟩ := d35.call_inv
  obtain ⟨v41, vs42, m43, rfl, d44, args45⟩ := args39.cons_inv
  obtain ⟨l46, rfl⟩ := d44.var_inv; simp at l46; subst l46
  obtain ⟨v47, vs48, m49, rfl, d50, args51⟩ := args45.cons_inv
  obtain ⟨rfl, rfl⟩ := d50.global_literal_inv (x := ((4 : Nat) : F)) (eq_of_isLiteral (by decide +kernel))
  obtain ⟨rfl, rfl⟩ := args51.nil_inv
  rw [instanceName_plain_some, hmod256] at callee40
  obtain ⟨rfl, rfl⟩ := u8LessThan_refines hsz_lt256 (by omega) callee40
  obtain ⟨v52, vs53, m54, rfl, d55, args56⟩ := args36.cons_inv
  obtain ⟨rfl, rfl⟩ := d55.literal_inv
  obtain ⟨rfl, rfl⟩ := args56.nil_inv
  have hsz_lt4 : sz.toNat < 4 := by
    by_contra hge
    simp [hge, Builtin.apply, evalAssertEq, Value.pointerFree] at app31
  rw [matchPattern_wildcard] at mt27
  simp only [Except.ok.injEq, Option.some.injEq] at mt27; subst mt27
  obtain ⟨v57, m58, bs59, d60, mt61, d62⟩ := d28.letValue_inv
  obtain ⟨vs63, m64, args65, callee66⟩ := d60.call_inv
  obtain ⟨v67, vs68, m69, rfl, d70, args71⟩ := args65.cons_inv
  obtain ⟨l72, rfl⟩ := d70.var_inv; simp at l72; subst l72
  obtain ⟨rfl, rfl⟩ := args71.nil_inv
  rw [instanceName_plain_some, hmod256] at callee66
  obtain ⟨rfl, rfl⟩ := u8BitDecomposition_refines hsz_lt256 callee66
  rw [matchPattern_bind] at mt61
  simp only [Except.ok.injEq, Option.some.injEq] at mt61; subst mt61
  obtain ⟨v73, m74, bs75, d76, mt77, d78⟩ := d62.letValue_inv
  obtain ⟨v79, m80, bs81, body82, d83, sel84, d85⟩ := d76.matchValue_inv
  obtain ⟨v_bits, d_bits_var, hproj1⟩ := d83.index_inv
  obtain ⟨l_bits, rfl⟩ := d_bits_var.var_inv; simp at l_bits; subst l_bits
  simp only [projectValue, List.getElem?_cons_succ, List.getElem?_cons_zero,
    pure, Except.pure, Except.ok.injEq] at hproj1
  subst hproj1
  have hkind : v73 = .construct "Ixon::LetKind" (if sz.toNat / 2 % 2 = 0 then "Value" else "BorrowShared") [] ∧ m74 = m80 := by
    have hb1_01 : sz.toNat / 2 % 2 = 0 ∨ sz.toNat / 2 % 2 = 1 := Nat.mod_two_eq_zero_or_one (sz.toNat / 2)
    rcases hb1_01 with h1 | h1
    · rcases selectArm_literal_inv sel84 with ⟨_, rfl, rfl⟩ | ⟨hne, _⟩
      · obtain ⟨vs_k, args_k, rfl⟩ := d85.construct_inv
        obtain ⟨rfl, rfl⟩ := args_k.nil_inv
        simp [h1]
      · simp [h1] at hne
    · rcases selectArm_literal_inv sel84 with ⟨heq, _, _⟩ | ⟨_, sel85⟩
      · simp [h1] at heq
      · rcases selectArm_literal_inv sel85 with ⟨_, rfl, rfl⟩ | ⟨hne, _⟩
        · obtain ⟨vs_k, args_k, rfl⟩ := d85.construct_inv
          obtain ⟨rfl, rfl⟩ := args_k.nil_inv
          simp [h1]
        · simp [h1] at hne
  rcases hkind with ⟨rfl, rfl⟩
  rw [matchPattern_bind] at mt77
  simp only [Except.ok.injEq, Option.some.injEq] at mt77; subst mt77
  obtain ⟨v86, m87, bs88, d89, mt90, d91⟩ := d78.letValue_inv
  obtain ⟨vs92, m93, args94, callee95⟩ := d89.call_inv
  obtain ⟨v96, vs97, m98, rfl, d99, args100⟩ := args94.cons_inv
  obtain ⟨l101, rfl⟩ := d99.var_inv; simp at l101; subst l101
  obtain ⟨rfl, rfl⟩ := args100.nil_inv
  rw [instanceName_plain_some] at callee95
  obtain ⟨rfl, bc, restPtr1, hlen_mode, hok_mode, hrep1, rfl⟩ :=
    getLamMode_refines_at hrep callee95
  obtain rfl := matchPattern_tuple2_bind rfl mt90
  obtain ⟨v102, m103, bs104, d105, mt106, d107⟩ := d91.letValue_inv
  obtain ⟨vs108, m109, args110, callee111⟩ := d105.call_inv
  obtain ⟨v112, vs113, m114, rfl, d115, args116⟩ := args110.cons_inv
  obtain ⟨l117, rfl⟩ := d115.var_inv; simp at l117; subst l117
  obtain ⟨rfl, rfl⟩ := args116.nil_inv
  rw [instanceName_plain_some] at callee111
  obtain ⟨ext1, ty, n2, tyPtr, restPtr2, hn2_pos, hdrop_lt2, hfuel_ty, rfl, tyRep, hrep2⟩ :=
    hIH (by omega) hrep1 callee111
  obtain rfl := matchPattern_tuple2_bind rfl mt106
  obtain ⟨v118, m119, bs120, d121, mt122, d123⟩ := d107.letValue_inv
  obtain ⟨vs124, m125, args126, callee127⟩ := d121.call_inv
  obtain ⟨v128, vs129, m130, rfl, d131, args132⟩ := args126.cons_inv
  obtain ⟨l133, rfl⟩ := d131.var_inv; simp at l133; subst l133
  obtain ⟨rfl, rfl⟩ := args132.nil_inv
  rw [instanceName_plain_some] at callee127
  obtain ⟨ext2, val, n3, valPtr, restPtr3, hn3_pos, hdrop_lt3, hfuel_val, rfl, valRep, hrep3⟩ :=
    hIH (by omega) hrep2 callee127
  obtain rfl := matchPattern_tuple2_bind rfl mt122
  obtain ⟨v134, m135, bs136, d137, mt138, d139⟩ := d123.letValue_inv
  obtain ⟨vs140, m141, args142, callee143⟩ := d137.call_inv
  obtain ⟨v144, vs145, m146, rfl, d147, args148⟩ := args142.cons_inv
  obtain ⟨l149, rfl⟩ := d147.var_inv; simp at l149; subst l149
  obtain ⟨rfl, rfl⟩ := args148.nil_inv
  rw [instanceName_plain_some] at callee143
  obtain ⟨ext3, bodyExpr, n4, bodyPtr, restPtr4, hn4_pos, hdrop_lt4, hfuel_body, rfl, bodyRep, hrep4⟩ :=
    hIH (by omega) hrep3 callee143
  obtain rfl := matchPattern_tuple2_bind rfl mt138
  obtain ⟨vs150, args151, rfl⟩ := d139.tuple_inv
  obtain ⟨v152, vs153, m154, rfl, d155, args156⟩ := args151.cons_inv
  obtain ⟨v157, m158, d159, rfl, rfl⟩ := d155.store_inv
  obtain ⟨vs160, args161, rfl⟩ := d159.construct_inv
  obtain ⟨v162, vs163, m164, rfl, d165, args166⟩ := args161.cons_inv
  obtain ⟨vs167, args168, rfl⟩ := d165.construct_inv
  obtain ⟨v169, vs170, m171, rfl, d172, args173⟩ := args168.cons_inv
  obtain ⟨v_b0, d_b0_var, hproj0⟩ := d172.index_inv
  obtain ⟨l_b0, rfl⟩ := d_b0_var.var_inv; simp at l_b0; subst l_b0
  simp only [projectValue, List.getElem?_cons_zero, pure, Except.pure, Except.ok.injEq] at hproj0
  subst hproj0
  obtain ⟨v174, vs175, m176, rfl, d177, args178⟩ := args173.cons_inv
  obtain ⟨l179, rfl⟩ := d177.var_inv; simp at l179; subst l179
  obtain ⟨v180, vs181, m182, rfl, d183, args184⟩ := args178.cons_inv
  obtain ⟨l185, rfl⟩ := d183.var_inv; simp at l185; subst l185
  obtain ⟨rfl, rfl⟩ := args184.nil_inv
  obtain ⟨v186, vs187, m188, rfl, d189, args190⟩ := args166.cons_inv
  obtain ⟨l191, rfl⟩ := d189.var_inv; simp at l191; subst l191
  obtain ⟨v192, vs193, m194, rfl, d195, args196⟩ := args190.cons_inv
  obtain ⟨l197, rfl⟩ := d195.var_inv; simp at l197; subst l197
  obtain ⟨v198, vs199, m200, rfl, d201, args202⟩ := args196.cons_inv
  obtain ⟨l203, rfl⟩ := d201.var_inv; simp at l203; subst l203
  obtain ⟨rfl, rfl⟩ := args202.nil_inv
  obtain ⟨v204, vs205, m206, rfl, d207, args208⟩ := args156.cons_inv
  obtain ⟨l209, rfl⟩ := d207.var_inv; simp at l209; subst l209
  obtain ⟨rfl, rfl⟩ := args208.nil_inv
  simp only [instanceName_plain_some, value_type_construct, ← letContractValue_ofFlags]
  let lc := letContractOfFlags sz.toNat bc
  let cellLet : SourceValue F := .construct "Ixon::Expr" "Let"
    [letContractValue lc, tyPtr, valPtr, bodyPtr]
  have extStore : Heap.Extends m158 (m158 ++ [cellLet]) := Heap.Extends.snoc m158 cellLet
  have letRep : RepExpr (m158 ++ [cellLet]) (.letE lc ty val bodyExpr)
      (.ptr (.enum "Ixon::Expr") m158.length) :=
    .letE (by simp [cellLet])
      (((tyRep.mono ext2).mono ext3).mono extStore)
      ((valRep.mono ext3).mono extStore)
      (bodyRep.mono extStore)
  have hrep4' := Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum extStore hrep4
  rw [show i + 1 + n2 + n3 + n4 = i + (1 + n2 + n3 + n4) by omega] at hdrop_lt4 hrep4'
  refine ⟨((ext1.trans ext2).trans ext3).trans extStore, hsz_lt4, bc, ty, val, bodyExpr,
    1 + n2 + n3 + n4, .ptr (.enum "Ixon::Expr") m158.length, restPtr4,
    by omega, by omega, fun fuel hfuel => ?_, rfl, letRep, hrep4'⟩
  have hflags := letContract_ofFlags?_of_lt4 hsz_lt4 bc
  have hty_ok := hfuel_ty fuel (by omega)
  have hval_ok := hfuel_val fuel (by omega)
  have hbody_ok := hfuel_body fuel (by omega)
  rw [show i + 1 + n2 + n3 + n4 = i + (1 + n2 + n3 + n4) by omega] at hbody_ok
  simp [bind, EStateM.bind, hok_mode, hflags, hty_ok, hval_ok, hbody_ok, pure, EStateM.pure]

/-- **Every terminating derivation of `IxonDeserialize::get_expr` at reader
offset `i`** refines `Ixon.getExprFuel fuel` for every `fuel > (bytes.drop i).length`,
extending the heap with a `RepExpr` pointer and advancing the stream by `n > 0`
bytes. -/
theorem deserializeExpr_refines_at {bytes : List UInt8} {i : Nat}
    {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : EvalFn W "IxonDeserialize::get_expr" [stream] h r h') :
    Heap.Extends h h' ∧
    ∃ (e : Ixon.Expr) (n : Nat) (exprPtr restPtr : SourceValue F),
      0 < n ∧
      (bytes.drop (i + n)).length < (bytes.drop i).length ∧
      (∀ fuel, (bytes.drop i).length < fuel →
        Ixon.getExprFuel fuel { idx := i, bytes := ⟨bytes.toArray⟩ } =
          .ok e { idx := i + n, bytes := ⟨bytes.toArray⟩ }) ∧
      r = .tuple [exprPtr, restPtr] ∧
      RepExpr h' e exprPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  suffices H : ∀ m, ∀ {i : Nat} {stream r : SourceValue F} {h h' : Heap F},
      (bytes.drop i).length = m →
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream →
      EvalFn W "IxonDeserialize::get_expr" [stream] h r h' →
      Heap.Extends h h' ∧
      ∃ (e : Ixon.Expr) (n : Nat) (exprPtr restPtr : SourceValue F),
        0 < n ∧
        (bytes.drop (i + n)).length < (bytes.drop i).length ∧
        (∀ fuel, (bytes.drop i).length < fuel →
          Ixon.getExprFuel fuel { idx := i, bytes := ⟨bytes.toArray⟩ } =
            .ok e { idx := i + n, bytes := ⟨bytes.toArray⟩ }) ∧
        r = .tuple [exprPtr, restPtr] ∧
        RepExpr h' e exprPtr ∧
        Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr by
    exact H _ rfl rep ev
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro i stream r h h' hm rep ev
  have body := ev.function_inv IxVM.IxonDeserialize.get_expr.lookup
    (by simp [IxVM.IxonDeserialize.get_expr, ControlLower.hasControl])
  simp only [IxVM.IxonDeserialize.get_expr] at body
  obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
  obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
  obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
  obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
  obtain ⟨rfl, rfl⟩ := args14.nil_inv
  rw [instanceName_plain_some] at callee9
  obtain ⟨rfl, t, n1, restPtr1, hok_drop, hrep1, rfl⟩ := getTagN4_refines rep callee9
  have hok1 : Ixon.getTagN 4 { idx := i, bytes := ⟨bytes.toArray⟩ } =
      .ok t { idx := i + n1, bytes := ⟨bytes.toArray⟩ } := getTagN_drop hok_drop
  obtain ⟨hn1_pos, _⟩ := getTagN_pos hok_drop
  have hdrop_lt1 : (bytes.drop (i + n1)).length < (bytes.drop i).length := by
    rw [← List.drop_drop]
    exact drop_length_lt_of_getTagN hok_drop
  rw [List.drop_drop] at hrep1
  have hIH1 : ExprRefinesAtUpTo bytes ((bytes.drop (i + n1)).length + 1) :=
    fun hlt rep' ev' => ih _ (by omega) rfl rep' ev'
  obtain rfl := matchPattern_tuple2_bind rfl mt4
  obtain ⟨v16, m17, bs18, d19, mt20, d21⟩ := d5.letValue_inv
  obtain ⟨l22, rfl⟩ := d19.var_inv; simp at l22; subst l22
  obtain rfl := matchPattern_tuple2_bind rfl mt20
  obtain ⟨v23, m24, bs25, body26, d27, sel28, d29⟩ := d21.matchValue_inv
  obtain ⟨l30, rfl⟩ := d27.var_inv; simp at l30; subst l30
  rcases selectArm_literal_inv sel28 with ⟨hc0, rfl, rfl⟩ | ⟨_, sel1⟩
  · -- Arm 0: Srt
    have hflag0 : t.flag = 0 :=
      UInt8.ext ((natCast_eq_zero_iff t.flag.toNat_lt).mp (Value.field.inj hc0))
    obtain ⟨rfl, rfl⟩ := evalExpr_store_unary_expr rfl rfl d29
    simp only [instanceName_plain_some]
    let cell : SourceValue F := .construct "Ixon::Expr" "Srt" [u64Value t.value.toNat]
    have ext : Heap.Extends m24 (m24 ++ [cell]) := Heap.Extends.snoc m24 cell
    refine ⟨ext, .sort t.value, n1, .ptr (.enum "Ixon::Expr") m24.length, restPtr1,
      hn1_pos, hdrop_lt1, fun fuel hfuel => ?_, rfl, .sort (by simp [cell]),
      Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext hrep1⟩
    obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
    simp [Ixon.getExprFuel, Ixon.getExprFromTag, hok1, hflag0,
      bind, EStateM.bind, pure, EStateM.pure]
  · rcases selectArm_literal_inv sel1 with ⟨hc1, rfl, rfl⟩ | ⟨_, sel2⟩
    · -- Arm 1: Var
      have hflag1 : t.flag = 1 :=
        UInt8.ext ((natCast_eq_one_iff t.flag.toNat_lt).mp (Value.field.inj hc1))
      obtain ⟨rfl, rfl⟩ := evalExpr_store_unary_expr rfl rfl d29
      simp only [instanceName_plain_some]
      let cell : SourceValue F := .construct "Ixon::Expr" "Var" [u64Value t.value.toNat]
      have ext : Heap.Extends m24 (m24 ++ [cell]) := Heap.Extends.snoc m24 cell
      refine ⟨ext, .var t.value, n1, .ptr (.enum "Ixon::Expr") m24.length, restPtr1,
        hn1_pos, hdrop_lt1, fun fuel hfuel => ?_, rfl, .var (by simp [cell]),
        Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext hrep1⟩
      obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
      simp [Ixon.getExprFuel, Ixon.getExprFromTag, hok1, hflag1,
        bind, EStateM.bind, pure, EStateM.pure]
    · rcases selectArm_literal_inv sel2 with ⟨hc2, rfl, rfl⟩ | ⟨_, sel3⟩
      · -- Arm 2: Ref
        have hflag2 : t.flag = 2 :=
          UInt8.ext ((natCast_eq_ofNat_iff (n := 2) t.flag.toNat_lt (by decide)).mp (Value.field.inj hc2))
        obtain ⟨v31, m32, bs33, d34, mt35, d36⟩ := d29.letValue_inv
        obtain ⟨vs37, m38, args39, callee40⟩ := d34.call_inv
        obtain ⟨v41, vs42, m43, rfl, d44, args45⟩ := args39.cons_inv
        obtain ⟨l46, rfl⟩ := d44.var_inv; simp at l46; subst l46
        obtain ⟨rfl, rfl⟩ := args45.nil_inv
        rw [instanceName_plain_some] at callee40
        obtain ⟨rfl, tRef, n2, restPtr2, hok2_drop, _, hrep2, rfl⟩ := getTagN0_refines hrep1 callee40
        have hok2 := getTagN_drop hok2_drop
        have hdrop_lt2 : (bytes.drop (i + n1 + n2)).length < (bytes.drop (i + n1)).length := by
          rw [← List.drop_drop]
          exact drop_length_lt_of_getTagN hok2_drop
        rw [List.drop_drop] at hrep2
        obtain rfl := matchPattern_tuple2_bind rfl mt35
        obtain ⟨v47, m48, bs49, d50, mt51, d52⟩ := d36.letValue_inv
        obtain ⟨vs53, m54, args55, callee56⟩ := d50.call_inv
        obtain ⟨v57, vs58, m59, rfl, d60, args61⟩ := args55.cons_inv
        obtain ⟨l62, rfl⟩ := d60.var_inv; simp at l62; subst l62
        obtain ⟨v63, vs64, m65, rfl, d66, args67⟩ := args61.cons_inv
        obtain ⟨l68, rfl⟩ := d66.var_inv; simp at l68; subst l68
        obtain ⟨rfl, rfl⟩ := args67.nil_inv
        rw [instanceName_plain_some] at callee56
        obtain ⟨ext1, univIdxs, n3, listPtr, restPtr3, hprog3, hok3, hlen3, rfl, listRep, hrep3⟩ :=
          getU64List_progress t.value.toNat t.value.toNat_lt hrep2 callee56
        obtain rfl := matchPattern_tuple2_bind rfl mt51
        obtain ⟨vs69, args70, rfl⟩ := d52.tuple_inv
        obtain ⟨v71, vs72, m73, rfl, d74, args75⟩ := args70.cons_inv
        obtain ⟨v76, m77, d78, rfl, rfl⟩ := d74.store_inv
        obtain ⟨vs79, args80, rfl⟩ := d78.construct_inv
        obtain ⟨v81, vs82, m83, rfl, d84, args85⟩ := args80.cons_inv
        obtain ⟨l86, rfl⟩ := d84.var_inv; simp at l86; subst l86
        obtain ⟨v87, vs88, m89, rfl, d90, args91⟩ := args85.cons_inv
        obtain ⟨l92, rfl⟩ := d90.var_inv; simp at l92; subst l92
        obtain ⟨rfl, rfl⟩ := args91.nil_inv
        obtain ⟨v93, vs94, m95, rfl, d96, args97⟩ := args75.cons_inv
        obtain ⟨l98, rfl⟩ := d96.var_inv; simp at l98; subst l98
        obtain ⟨rfl, rfl⟩ := args97.nil_inv
        simp only [instanceName_plain_some, value_type_construct]
        let cell : SourceValue F := .construct "Ixon::Expr" "Ref" [u64Value tRef.value.toNat, listPtr]
        have extStore : Heap.Extends m77 (m77 ++ [cell]) := Heap.Extends.snoc m77 cell
        have refRep : RepExpr (m77 ++ [cell]) (.ref tRef.value univIdxs.toArray)
            (.ptr (.enum "Ixon::Expr") m77.length) :=
          .ref (by simp [cell]) (listRep.mono Aiur.Library.repU64_heapMono₂ extStore)
        have hrep3' := Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum extStore hrep3
        rw [show i + n1 + n2 + n3 = i + (n1 + n2 + n3) by omega] at hprog3 hrep3'
        refine ⟨ext1.trans extStore, .ref tRef.value univIdxs.toArray, n1 + n2 + n3,
          .ptr (.enum "Ixon::Expr") m77.length, restPtr3,
          by omega, by omega, fun fuel hfuel => ?_, rfl, refRep, hrep3'⟩
        obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
        have hchk : Ixon.checkCount t.value 1 { idx := i + n1 + n2, bytes := ⟨bytes.toArray⟩ } =
            .ok () { idx := i + n1 + n2, bytes := ⟨bytes.toArray⟩ } :=
          checkCount_ok (by omega)
        rw [show i + n1 + n2 + n3 = i + (n1 + n2 + n3) by omega] at hok3
        simp [Ixon.getExprFuel, Ixon.getExprFromTag, hok1, hflag2, hok2, hchk, hok3,
          bind, EStateM.bind, pure, EStateM.pure]
      · rcases selectArm_literal_inv sel3 with ⟨hc3, rfl, rfl⟩ | ⟨_, sel4⟩
        · -- Arm 3: Rec
          have hflag3 : t.flag = 3 :=
            UInt8.ext ((natCast_eq_ofNat_iff (n := 3) t.flag.toNat_lt (by decide)).mp (Value.field.inj hc3))
          obtain ⟨v31, m32, bs33, d34, mt35, d36⟩ := d29.letValue_inv
          obtain ⟨vs37, m38, args39, callee40⟩ := d34.call_inv
          obtain ⟨v41, vs42, m43, rfl, d44, args45⟩ := args39.cons_inv
          obtain ⟨l46, rfl⟩ := d44.var_inv; simp at l46; subst l46
          obtain ⟨rfl, rfl⟩ := args45.nil_inv
          rw [instanceName_plain_some] at callee40
          obtain ⟨rfl, tRec, n2, restPtr2, hok2_drop, _, hrep2, rfl⟩ := getTagN0_refines hrep1 callee40
          have hok2 := getTagN_drop hok2_drop
          have hdrop_lt2 : (bytes.drop (i + n1 + n2)).length < (bytes.drop (i + n1)).length := by
            rw [← List.drop_drop]
            exact drop_length_lt_of_getTagN hok2_drop
          rw [List.drop_drop] at hrep2
          obtain rfl := matchPattern_tuple2_bind rfl mt35
          obtain ⟨v47, m48, bs49, d50, mt51, d52⟩ := d36.letValue_inv
          obtain ⟨vs53, m54, args55, callee56⟩ := d50.call_inv
          obtain ⟨v57, vs58, m59, rfl, d60, args61⟩ := args55.cons_inv
          obtain ⟨l62, rfl⟩ := d60.var_inv; simp at l62; subst l62
          obtain ⟨v63, vs64, m65, rfl, d66, args67⟩ := args61.cons_inv
          obtain ⟨l68, rfl⟩ := d66.var_inv; simp at l68; subst l68
          obtain ⟨rfl, rfl⟩ := args67.nil_inv
          rw [instanceName_plain_some] at callee56
          obtain ⟨ext1, univIdxs, n3, listPtr, restPtr3, hprog3, hok3, hlen3, rfl, listRep, hrep3⟩ :=
            getU64List_progress t.value.toNat t.value.toNat_lt hrep2 callee56
          obtain rfl := matchPattern_tuple2_bind rfl mt51
          obtain ⟨vs69, args70, rfl⟩ := d52.tuple_inv
          obtain ⟨v71, vs72, m73, rfl, d74, args75⟩ := args70.cons_inv
          obtain ⟨v76, m77, d78, rfl, rfl⟩ := d74.store_inv
          obtain ⟨vs79, args80, rfl⟩ := d78.construct_inv
          obtain ⟨v81, vs82, m83, rfl, d84, args85⟩ := args80.cons_inv
          obtain ⟨l86, rfl⟩ := d84.var_inv; simp at l86; subst l86
          obtain ⟨v87, vs88, m89, rfl, d90, args91⟩ := args85.cons_inv
          obtain ⟨l92, rfl⟩ := d90.var_inv; simp at l92; subst l92
          obtain ⟨rfl, rfl⟩ := args91.nil_inv
          obtain ⟨v93, vs94, m95, rfl, d96, args97⟩ := args75.cons_inv
          obtain ⟨l98, rfl⟩ := d96.var_inv; simp at l98; subst l98
          obtain ⟨rfl, rfl⟩ := args97.nil_inv
          simp only [instanceName_plain_some, value_type_construct]
          let cell : SourceValue F := .construct "Ixon::Expr" "Rec" [u64Value tRec.value.toNat, listPtr]
          have extStore : Heap.Extends m77 (m77 ++ [cell]) := Heap.Extends.snoc m77 cell
          have recRep : RepExpr (m77 ++ [cell]) (.recur tRec.value univIdxs.toArray)
              (.ptr (.enum "Ixon::Expr") m77.length) :=
            .recur (by simp [cell]) (listRep.mono Aiur.Library.repU64_heapMono₂ extStore)
          have hrep3' := Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum extStore hrep3
          rw [show i + n1 + n2 + n3 = i + (n1 + n2 + n3) by omega] at hprog3 hrep3'
          refine ⟨ext1.trans extStore, .recur tRec.value univIdxs.toArray, n1 + n2 + n3,
            .ptr (.enum "Ixon::Expr") m77.length, restPtr3,
            by omega, by omega, fun fuel hfuel => ?_, rfl, recRep, hrep3'⟩
          obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
          have hchk : Ixon.checkCount t.value 1 { idx := i + n1 + n2, bytes := ⟨bytes.toArray⟩ } =
              .ok () { idx := i + n1 + n2, bytes := ⟨bytes.toArray⟩ } :=
            checkCount_ok (by omega)
          rw [show i + n1 + n2 + n3 = i + (n1 + n2 + n3) by omega] at hok3
          simp [Ixon.getExprFuel, Ixon.getExprFromTag, hok1, hflag3, hok2, hchk, hok3,
            bind, EStateM.bind, pure, EStateM.pure]
        · rcases selectArm_literal_inv sel4 with ⟨hc4, rfl, rfl⟩ | ⟨_, sel5⟩
          · -- Arm 4: Prj
            have hflag4 : t.flag = 4 :=
              UInt8.ext ((natCast_eq_ofNat_iff (n := 4) t.flag.toNat_lt (by decide)).mp (Value.field.inj hc4))
            obtain ⟨v31, m32, bs33, d34, mt35, d36⟩ := d29.letValue_inv
            obtain ⟨vs37, m38, args39, callee40⟩ := d34.call_inv
            obtain ⟨v41, vs42, m43, rfl, d44, args45⟩ := args39.cons_inv
            obtain ⟨l46, rfl⟩ := d44.var_inv; simp at l46; subst l46
            obtain ⟨rfl, rfl⟩ := args45.nil_inv
            rw [instanceName_plain_some] at callee40
            obtain ⟨rfl, tTypeRef, n2, restPtr2, hok2_drop, _, hrep2, rfl⟩ := getTagN0_refines hrep1 callee40
            have hok2 := getTagN_drop hok2_drop
            have hdrop_lt2 : (bytes.drop (i + n1 + n2)).length < (bytes.drop (i + n1)).length := by
              rw [← List.drop_drop]
              exact drop_length_lt_of_getTagN hok2_drop
            rw [List.drop_drop] at hrep2
            obtain rfl := matchPattern_tuple2_bind rfl mt35
            obtain ⟨v47, m48, bs49, d50, mt51, d52⟩ := d36.letValue_inv
            obtain ⟨vs53, m54, args55, callee56⟩ := d50.call_inv
            obtain ⟨v57, vs58, m59, rfl, d60, args61⟩ := args55.cons_inv
            obtain ⟨l62, rfl⟩ := d60.var_inv; simp at l62; subst l62
            obtain ⟨rfl, rfl⟩ := args61.nil_inv
            rw [instanceName_plain_some] at callee56
            obtain ⟨ext1, val, n3, valPtr, restPtr3, hn3_pos, hdrop_lt3, hfuel_val, rfl, valRep, hrep3⟩ :=
              hIH1 (by omega) hrep2 callee56
            obtain rfl := matchPattern_tuple2_bind rfl mt51
            obtain ⟨vs63, args64, rfl⟩ := d52.tuple_inv
            obtain ⟨v65, vs66, m67, rfl, d68, args69⟩ := args64.cons_inv
            obtain ⟨v70, m71, d72, rfl, rfl⟩ := d68.store_inv
            obtain ⟨vs73, args74, rfl⟩ := d72.construct_inv
            obtain ⟨v75, vs76, m77, rfl, d78, args79⟩ := args74.cons_inv
            obtain ⟨l80, rfl⟩ := d78.var_inv; simp at l80; subst l80
            obtain ⟨v81, vs82, m83, rfl, d84, args85⟩ := args79.cons_inv
            obtain ⟨l86, rfl⟩ := d84.var_inv; simp at l86; subst l86
            obtain ⟨v87, vs88, m89, rfl, d90, args91⟩ := args85.cons_inv
            obtain ⟨l92, rfl⟩ := d90.var_inv; simp at l92; subst l92
            obtain ⟨rfl, rfl⟩ := args91.nil_inv
            obtain ⟨v93, vs94, m95, rfl, d96, args97⟩ := args69.cons_inv
            obtain ⟨l98, rfl⟩ := d96.var_inv; simp at l98; subst l98
            obtain ⟨rfl, rfl⟩ := args97.nil_inv
            simp only [instanceName_plain_some, value_type_construct]
            let cell : SourceValue F := .construct "Ixon::Expr" "Prj"
              [u64Value tTypeRef.value.toNat, u64Value t.value.toNat, valPtr]
            have extStore : Heap.Extends m71 (m71 ++ [cell]) := Heap.Extends.snoc m71 cell
            have prjRep : RepExpr (m71 ++ [cell]) (.prj tTypeRef.value t.value val)
                (.ptr (.enum "Ixon::Expr") m71.length) :=
              .prj (by simp [cell]) (valRep.mono extStore)
            have hrep3' := Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum extStore hrep3
            rw [show i + n1 + n2 + n3 = i + (n1 + n2 + n3) by omega] at hdrop_lt3 hrep3'
            refine ⟨ext1.trans extStore, .prj tTypeRef.value t.value val, n1 + n2 + n3,
              .ptr (.enum "Ixon::Expr") m71.length, restPtr3,
              by omega, by omega, fun fuel hfuel => ?_, rfl, prjRep, hrep3'⟩
            obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
            have hval_ok := hfuel_val fuel' (by omega)
            rw [show i + n1 + n2 + n3 = i + (n1 + n2 + n3) by omega] at hval_ok
            simp [Ixon.getExprFuel, Ixon.getExprFromTag, hok1, hflag4, hok2, hval_ok,
              bind, EStateM.bind, pure, EStateM.pure]
          · rcases selectArm_literal_inv sel5 with ⟨hc5, rfl, rfl⟩ | ⟨_, sel6⟩
            · -- Arm 5: Str
              have hflag5 : t.flag = 5 :=
                UInt8.ext ((natCast_eq_ofNat_iff (n := 5) t.flag.toNat_lt (by decide)).mp (Value.field.inj hc5))
              obtain ⟨rfl, rfl⟩ := evalExpr_store_unary_expr rfl rfl d29
              simp only [instanceName_plain_some]
              let cell : SourceValue F := .construct "Ixon::Expr" "Str" [u64Value t.value.toNat]
              have ext : Heap.Extends m24 (m24 ++ [cell]) := Heap.Extends.snoc m24 cell
              refine ⟨ext, .str t.value, n1, .ptr (.enum "Ixon::Expr") m24.length, restPtr1,
                hn1_pos, hdrop_lt1, fun fuel hfuel => ?_, rfl, .str (by simp [cell]),
                Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext hrep1⟩
              obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
              simp [Ixon.getExprFuel, Ixon.getExprFromTag, hok1, hflag5,
                bind, EStateM.bind, pure, EStateM.pure]
            · rcases selectArm_literal_inv sel6 with ⟨hc6, rfl, rfl⟩ | ⟨_, sel7⟩
              · -- Arm 6: Nat
                have hflag6 : t.flag = 6 :=
                  UInt8.ext ((natCast_eq_ofNat_iff (n := 6) t.flag.toNat_lt (by decide)).mp (Value.field.inj hc6))
                obtain ⟨rfl, rfl⟩ := evalExpr_store_unary_expr rfl rfl d29
                simp only [instanceName_plain_some]
                let cell : SourceValue F := .construct "Ixon::Expr" "Nat" [u64Value t.value.toNat]
                have ext : Heap.Extends m24 (m24 ++ [cell]) := Heap.Extends.snoc m24 cell
                refine ⟨ext, .nat t.value, n1, .ptr (.enum "Ixon::Expr") m24.length, restPtr1,
                  hn1_pos, hdrop_lt1, fun fuel hfuel => ?_, rfl, .nat (by simp [cell]),
                  Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext hrep1⟩
                obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
                simp [Ixon.getExprFuel, Ixon.getExprFromTag, hok1, hflag6,
                  bind, EStateM.bind, pure, EStateM.pure]
              · rcases selectArm_literal_inv sel7 with ⟨hc7, rfl, rfl⟩ | ⟨_, sel8⟩
                · -- Arm 7: App (telescope)
                  have hflag7 : t.flag = 7 :=
                    UInt8.ext ((natCast_eq_ofNat_iff (n := 7) t.flag.toNat_lt (by decide)).mp (Value.field.inj hc7))
                  obtain ⟨hsz_ne0, d30⟩ := evalExpr_assert_u64_nonZero t.value.toNat_lt (by simp) d29
                  have htval_ne0 : (t.value == 0) = false := by
                    simp only [beq_eq_false_iff_ne]
                    intro h0
                    exact hsz_ne0 (congrArg UInt64.toNat h0)
                  obtain ⟨v31, m32, bs33, d34, mt35, d36⟩ := d30.letValue_inv
                  obtain ⟨vs37, m38, args39, callee40⟩ := d34.call_inv
                  obtain ⟨v41, vs42, m43, rfl, d44, args45⟩ := args39.cons_inv
                  obtain ⟨l46, rfl⟩ := d44.var_inv; simp at l46; subst l46
                  obtain ⟨rfl, rfl⟩ := args45.nil_inv
                  rw [instanceName_plain_some] at callee40
                  obtain ⟨ext1, base, n2, basePtr, restPtr2, hn2_pos, hdrop_lt2, hfuel_base, rfl, baseRep, hrep2⟩ :=
                    hIH1 (Nat.lt_succ_self _) hrep1 callee40
                  obtain rfl := matchPattern_tuple2_bind rfl mt35
                  obtain ⟨⟨v_load, hload, hmp⟩, d_ok⟩ := evalExpr_reject_ctor_inv rfl d36
                  have hne_app := repExpr_ne_app baseRep hload hmp
                  obtain ⟨vs50, m51, args52, callee53⟩ := d_ok.call_inv
                  obtain ⟨v54, vs55, m56, rfl, d57, args58⟩ := args52.cons_inv
                  obtain ⟨l59, rfl⟩ := d57.var_inv; simp at l59; subst l59
                  obtain ⟨v60, vs61, m62, rfl, d63, args64⟩ := args58.cons_inv
                  obtain ⟨l65, rfl⟩ := d63.var_inv; simp at l65; subst l65
                  obtain ⟨v66, vs67, m68, rfl, d69, args70⟩ := args64.cons_inv
                  obtain ⟨l71, rfl⟩ := d69.var_inv; simp at l71; subst l71
                  obtain ⟨rfl, rfl⟩ := args70.nil_inv
                  rw [instanceName_plain_some] at callee53
                  have hIH2 : ExprRefinesAtUpTo bytes ((bytes.drop (i + n1 + n2)).length + 1) :=
                    hIH1.mono (by omega)
                  obtain ⟨ext2, resExpr, n3, resPtr, restPtr3, hprog3, hfuel_args, rfl, resRep, hrep3⟩ :=
                    getAppTelescope_refines_at_of_ih t.value.toNat t.value.toNat_lt hIH2 baseRep hrep2 callee53
                  rw [show i + n1 + n2 + n3 = i + (n1 + n2 + n3) by omega] at hprog3 hrep3
                  refine ⟨ext1.trans ext2, resExpr, n1 + n2 + n3, resPtr, restPtr3,
                    by omega, by omega, fun fuel hfuel => ?_, rfl, resRep, hrep3⟩
                  obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
                  have hchk : Ixon.checkCount t.value 1 { idx := i + n1, bytes := ⟨bytes.toArray⟩ } =
                      .ok () { idx := i + n1, bytes := ⟨bytes.toArray⟩ } :=
                    checkCount_ok (by omega)
                  have hbase_ok := hfuel_base fuel' (by omega)
                  have hargs_ok := hfuel_args fuel' (by omega)
                  rw [show i + n1 + n2 + n3 = i + (n1 + n2 + n3) by omega] at hargs_ok
                  simp [Ixon.getExprFuel, Ixon.getExprFromTag, hok1, hflag7, htval_ne0,
                    hchk, hbase_ok, match_not_app_ok hne_app, hargs_ok,
                    bind, EStateM.bind, pure, EStateM.pure]
                · rcases selectArm_literal_inv sel8 with ⟨hc8, rfl, rfl⟩ | ⟨_, sel9⟩
                  · -- Arm 8: Lam (telescope)
                    have hflag8 : t.flag = 8 :=
                      UInt8.ext ((natCast_eq_ofNat_iff (n := 8) t.flag.toNat_lt (by decide)).mp (Value.field.inj hc8))
                    obtain ⟨hsz_ne0, d30⟩ := evalExpr_assert_u64_nonZero t.value.toNat_lt (by simp) d29
                    have htval_ne0 : (t.value == 0) = false := by
                      simp only [beq_eq_false_iff_ne]
                      intro h0
                      exact hsz_ne0 (congrArg UInt64.toNat h0)
                    obtain ⟨vs31, m32, args33, callee34⟩ := d30.call_inv
                    obtain ⟨v35, vs36, m37, rfl, d38, args39⟩ := args33.cons_inv
                    obtain ⟨l40, rfl⟩ := d38.var_inv; simp at l40; subst l40
                    obtain ⟨v41, vs42, m43, rfl, d44, args45⟩ := args39.cons_inv
                    obtain ⟨l46, rfl⟩ := d44.var_inv; simp at l46; subst l46
                    obtain ⟨rfl, rfl⟩ := args45.nil_inv
                    rw [instanceName_plain_some] at callee34
                    obtain ⟨ext1, binders, bodyExpr, nb, n2, resPtr, restPtr2,
                        hn2_pos, hprog2, hne_lam, hfuel_lam, rfl, resRep, hrep2⟩ :=
                      getLamTelescope_refines_at_of_ih t.value.toNat t.value.toNat_lt hIH1 hrep1 callee34
                    rw [show i + n1 + n2 = i + (n1 + n2) by omega] at hprog2 hrep2
                    refine ⟨ext1, binders.foldr (fun (uses, ty) result => .lam uses ty result) bodyExpr,
                      n1 + n2, resPtr, restPtr2,
                      by omega, by omega, fun fuel hfuel => ?_, rfl, resRep, hrep2⟩
                    obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
                    have hchk : Ixon.checkCount t.value 2 { idx := i + n1, bytes := ⟨bytes.toArray⟩ } =
                        .ok () { idx := i + n1, bytes := ⟨bytes.toArray⟩ } :=
                      checkCount_ok (by omega)
                    obtain ⟨hbinders_ok, hbody_ok⟩ := hfuel_lam fuel' (by omega)
                    rw [show i + n1 + n2 = i + (n1 + n2) by omega] at hbody_ok
                    simp [Ixon.getExprFuel, Ixon.getExprFromTag, hok1, hflag8, htval_ne0,
                      hchk, hbinders_ok, hbody_ok, match_not_lam_ok hne_lam,
                      bind, EStateM.bind, pure, EStateM.pure]
                  · rcases selectArm_literal_inv sel9 with ⟨hc9, rfl, rfl⟩ | ⟨_, sel10⟩
                    · -- Arm 9: All (telescope)
                      have hflag9 : t.flag = 9 :=
                        UInt8.ext ((natCast_eq_ofNat_iff (n := 9) t.flag.toNat_lt (by decide)).mp (Value.field.inj hc9))
                      obtain ⟨hsz_ne0, d30⟩ := evalExpr_assert_u64_nonZero t.value.toNat_lt (by simp) d29
                      have htval_ne0 : (t.value == 0) = false := by
                        simp only [beq_eq_false_iff_ne]
                        intro h0
                        exact hsz_ne0 (congrArg UInt64.toNat h0)
                      obtain ⟨vs31, m32, args33, callee34⟩ := d30.call_inv
                      obtain ⟨v35, vs36, m37, rfl, d38, args39⟩ := args33.cons_inv
                      obtain ⟨l40, rfl⟩ := d38.var_inv; simp at l40; subst l40
                      obtain ⟨v41, vs42, m43, rfl, d44, args45⟩ := args39.cons_inv
                      obtain ⟨l46, rfl⟩ := d44.var_inv; simp at l46; subst l46
                      obtain ⟨rfl, rfl⟩ := args45.nil_inv
                      rw [instanceName_plain_some] at callee34
                      obtain ⟨ext1, binders, bodyExpr, nb, n2, resPtr, restPtr2,
                          hn2_pos, hprog2, hne_all, hfuel_all, rfl, resRep, hrep2⟩ :=
                        getAllTelescope_refines_at_of_ih t.value.toNat t.value.toNat_lt hIH1 hrep1 callee34
                      rw [show i + n1 + n2 = i + (n1 + n2) by omega] at hprog2 hrep2
                      refine ⟨ext1, binders.foldr (fun (uses, owned, ty) result => .all uses owned ty result) bodyExpr,
                        n1 + n2, resPtr, restPtr2,
                        by omega, by omega, fun fuel hfuel => ?_, rfl, resRep, hrep2⟩
                      obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
                      have hchk : Ixon.checkCount t.value 2 { idx := i + n1, bytes := ⟨bytes.toArray⟩ } =
                          .ok () { idx := i + n1, bytes := ⟨bytes.toArray⟩ } :=
                        checkCount_ok (by omega)
                      obtain ⟨hbinders_ok, hbody_ok⟩ := hfuel_all fuel' (by omega)
                      rw [show i + n1 + n2 = i + (n1 + n2) by omega] at hbody_ok
                      simp [Ixon.getExprFuel, Ixon.getExprFromTag, hok1, hflag9, htval_ne0,
                        hchk, hbinders_ok, hbody_ok, match_not_all_ok hne_all,
                        bind, EStateM.bind, pure, EStateM.pure]
                    · rcases selectArm_literal_inv sel10 with ⟨hc10, rfl, rfl⟩ | ⟨_, sel11⟩
                      · -- Arm 10: Let
                        have hflag10 : t.flag = 10 :=
                          UInt8.ext ((natCast_eq_ofNat_iff (n := 10) t.flag.toNat_lt (by decide)).mp (Value.field.inj hc10))
                        obtain ⟨vs31, m32, args33, callee34⟩ := d29.call_inv
                        obtain ⟨v35, vs36, m37, rfl, d38, args39⟩ := args33.cons_inv
                        obtain ⟨l40, rfl⟩ := d38.var_inv; simp at l40; subst l40
                        obtain ⟨v41, vs42, m43, rfl, d44, args45⟩ := args39.cons_inv
                        obtain ⟨l46, rfl⟩ := d44.var_inv; simp at l46; subst l46
                        obtain ⟨rfl, rfl⟩ := args45.nil_inv
                        rw [instanceName_plain_some] at callee34
                        obtain ⟨ext1, hsz_lt4, bc, ty, val, bodyExpr, n2, resPtr, restPtr2,
                            hn2_pos, hdrop_lt2, hfuel_let, rfl, resRep, hrep2⟩ :=
                          getExprLet_refines_at_of_ih t.value hIH1 hrep1 callee34
                        have hng3 : ¬ (t.value > 3) := by
                          show ¬ (3 < t.value)
                          rw [UInt64.lt_iff_toNat_lt]
                          change ¬ (3 < t.value.toNat)
                          omega
                        rw [show i + n1 + n2 = i + (n1 + n2) by omega] at hdrop_lt2 hrep2
                        refine ⟨ext1, .letE (letContractOfFlags t.value.toNat bc) ty val bodyExpr,
                          n1 + n2, resPtr, restPtr2,
                          by omega, by omega, fun fuel hfuel => ?_, rfl, resRep, hrep2⟩
                        obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
                        have hlet_ok := hfuel_let fuel' (by omega)
                        rw [show i + n1 + n2 = i + (n1 + n2) by omega] at hlet_ok
                        simp only [Ixon.getExprFuel, Ixon.getExprFromTag,
                          bind, EStateM.bind, hok1, hflag10, ↓reduceIte, hng3]
                        simp only [bind, EStateM.bind] at hlet_ok
                        exact hlet_ok
                      · rcases selectArm_literal_inv sel11 with ⟨hc11, rfl, rfl⟩ | ⟨_, sel12⟩
                        · -- Arm 11: Share
                          have hflag11 : t.flag = 11 :=
                            UInt8.ext ((natCast_eq_ofNat_iff (n := 11) t.flag.toNat_lt (by decide)).mp (Value.field.inj hc11))
                          obtain ⟨rfl, rfl⟩ := evalExpr_store_unary_expr rfl rfl d29
                          simp only [instanceName_plain_some]
                          let cell : SourceValue F := .construct "Ixon::Expr" "Share" [u64Value t.value.toNat]
                          have ext : Heap.Extends m24 (m24 ++ [cell]) := Heap.Extends.snoc m24 cell
                          refine ⟨ext, .share t.value, n1, .ptr (.enum "Ixon::Expr") m24.length, restPtr1,
                            hn1_pos, hdrop_lt1, fun fuel hfuel => ?_, rfl, .share (by simp [cell]),
                            Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext hrep1⟩
                          obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
                          simp [Ixon.getExprFuel, Ixon.getExprFromTag, hok1, hflag11,
                            bind, EStateM.bind, pure, EStateM.pure]
                        · simp [SourceSemantics.selectArm] at sel12

/-- **Every terminating derivation of `IxonDeserialize::get_expr` at reader
offset `i`** refines `Ixon.getExpr` at `i`, producing a `RepExpr` pointer and
the advanced stream pointer. -/
theorem getExpr_refines_at {bytes : List UInt8} {i : Nat}
    {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : EvalFn W "IxonDeserialize::get_expr" [stream] h r h') :
    Heap.Extends h h' ∧
    ∃ (e : Ixon.Expr) (n : Nat) (exprPtr restPtr : SourceValue F),
      0 < n ∧
      (bytes.drop (i + n)).length < (bytes.drop i).length ∧
      Ixon.getExpr { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok e { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [exprPtr, restPtr] ∧
      RepExpr h' e exprPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  obtain ⟨ext, e, n, exprPtr, restPtr, hn, hdrop_lt, hfuel, hr, eRep, restRep⟩ :=
    deserializeExpr_refines_at rep ev
  have hok : Ixon.getExpr { idx := i, bytes := ⟨bytes.toArray⟩ } =
      .ok e { idx := i + n, bytes := ⟨bytes.toArray⟩ } := by
    unfold Ixon.getExpr
    change Ixon.getExprFuel ((ByteArray.mk bytes.toArray).size - i + 1)
      { idx := i, bytes := ⟨bytes.toArray⟩ } = _
    exact hfuel _ (by simp [ByteArray.size])
  exact ⟨ext, e, n, exprPtr, restPtr, hn, hdrop_lt, hok, hr, eRep, restRep⟩

/-- **Every terminating derivation of `IxonDeserialize::get_expr` from the
start of `bytes`** refines `Ixon.getExpr (start bytes)`, producing a `RepExpr`
pointer and a stream pointer to the remaining bytes. -/
theorem deserializeExpr_refines {bytes : List UInt8}
    {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h bytes stream)
    (ev : EvalFn W "IxonDeserialize::get_expr" [stream] h r h') :
    Heap.Extends h h' ∧
    ∃ (e : Ixon.Expr) (n : Nat) (exprPtr restPtr : SourceValue F),
      0 < n ∧
      Ixon.getExpr (start bytes) =
        .ok e { idx := n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [exprPtr, restPtr] ∧
      RepExpr h' e exprPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop n) restPtr := by
  obtain ⟨ext, e, n, exprPtr, restPtr, hn, _, hok, hr, eRep, restRep⟩ :=
    getExpr_refines_at (i := 0) (by simpa using rep) ev
  exact ⟨ext, e, n, exprPtr, restPtr, hn, by simpa [start] using hok, hr, eRep,
    by simpa using restRep⟩

/-- Alias of `deserializeExpr_refines` matching the Aiur function name
`IxonDeserialize::get_expr`. -/
theorem getExpr_refines {bytes : List UInt8}
    {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h bytes stream)
    (ev : EvalFn W "IxonDeserialize::get_expr" [stream] h r h') :
    Heap.Extends h h' ∧
    ∃ (e : Ixon.Expr) (n : Nat) (exprPtr restPtr : SourceValue F),
      0 < n ∧
      Ixon.getExpr (start bytes) =
        .ok e { idx := n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [exprPtr, restPtr] ∧
      RepExpr h' e exprPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop n) restPtr :=
  deserializeExpr_refines rep ev

/-- Top-level refinement for `IxonDeserialize::get_app_telescope` at offset `i`. -/
theorem getAppTelescope_refines_at (count : Nat) (hcount : count < 18446744073709551616)
    {bytes : List UInt8} {i : Nat} {acc : Ixon.Expr}
    {accPtr stream r : SourceValue F} {h h' : Heap F}
    (hacc : RepExpr h acc accPtr)
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : EvalFn W "IxonDeserialize::get_app_telescope" [accPtr, stream, u64Value count] h r h') :
    Heap.Extends h h' ∧
    ∃ (res : Ixon.Expr) (n : Nat) (resPtr restPtr : SourceValue F),
      (bytes.drop (i + n)).length + count ≤ (bytes.drop i).length ∧
      (∀ fuel, (bytes.drop i).length < fuel →
        Ixon.getExprAppArgs (Ixon.getExprFuel fuel) count acc
          { idx := i, bytes := ⟨bytes.toArray⟩ } =
          .ok res { idx := i + n, bytes := ⟨bytes.toArray⟩ }) ∧
      r = .tuple [resPtr, restPtr] ∧
      RepExpr h' res resPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr :=
  getAppTelescope_refines_at_of_ih count hcount
    (fun _ rep' ev' => deserializeExpr_refines_at rep' ev') hacc rep ev

/-- Top-level refinement for `IxonDeserialize::get_lam_telescope` at offset `i`. -/
theorem getLamTelescope_refines_at (count : Nat) (hcount : count < 18446744073709551616)
    {bytes : List UInt8} {i : Nat} {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : EvalFn W "IxonDeserialize::get_lam_telescope" [stream, u64Value count] h r h') :
    Heap.Extends h h' ∧
    ∃ (binders : List (Ixon.BinderContract × Ixon.Expr)) (body : Ixon.Expr)
      (nb n : Nat) (resPtr restPtr : SourceValue F),
      0 < n ∧
      (bytes.drop (i + n)).length + (count * 2 + 1) ≤ (bytes.drop i).length ∧
      (∀ bc ty b, body ≠ .lam bc ty b) ∧
      (∀ fuel, (bytes.drop i).length < fuel →
        Ixon.getExprLamBinders (Ixon.getExprFuel fuel) count
          { idx := i, bytes := ⟨bytes.toArray⟩ } =
          .ok binders { idx := i + nb, bytes := ⟨bytes.toArray⟩ } ∧
        Ixon.getExprFuel fuel { idx := i + nb, bytes := ⟨bytes.toArray⟩ } =
          .ok body { idx := i + n, bytes := ⟨bytes.toArray⟩ }) ∧
      r = .tuple [resPtr, restPtr] ∧
      RepExpr h' (binders.foldr (fun (uses, ty) result => .lam uses ty result) body) resPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr :=
  getLamTelescope_refines_at_of_ih count hcount
    (fun _ rep' ev' => deserializeExpr_refines_at rep' ev') rep ev

/-- Top-level refinement for `IxonDeserialize::get_all_telescope` at offset `i`. -/
theorem getAllTelescope_refines_at (count : Nat) (hcount : count < 18446744073709551616)
    {bytes : List UInt8} {i : Nat} {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : EvalFn W "IxonDeserialize::get_all_telescope" [stream, u64Value count] h r h') :
    Heap.Extends h h' ∧
    ∃ (binders : List (Ixon.BinderContract × Ixon.ValueContract × Ixon.Expr)) (body : Ixon.Expr)
      (nb n : Nat) (resPtr restPtr : SourceValue F),
      0 < n ∧
      (bytes.drop (i + n)).length + (count * 2 + 1) ≤ (bytes.drop i).length ∧
      (∀ bc vc ty b, body ≠ .all bc vc ty b) ∧
      (∀ fuel, (bytes.drop i).length < fuel →
        Ixon.getExprAllBinders (Ixon.getExprFuel fuel) count
          { idx := i, bytes := ⟨bytes.toArray⟩ } =
          .ok binders { idx := i + nb, bytes := ⟨bytes.toArray⟩ } ∧
        Ixon.getExprFuel fuel { idx := i + nb, bytes := ⟨bytes.toArray⟩ } =
          .ok body { idx := i + n, bytes := ⟨bytes.toArray⟩ }) ∧
      r = .tuple [resPtr, restPtr] ∧
      RepExpr h' (binders.foldr (fun (uses, owned, ty) result => .all uses owned ty result) body) resPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr :=
  getAllTelescope_refines_at_of_ih count hcount
    (fun _ rep' ev' => deserializeExpr_refines_at rep' ev') rep ev

/-- Top-level refinement for `IxonDeserialize::get_expr_let` at offset `i`. -/
theorem getExprLet_refines_at (sz : UInt64)
    {bytes : List UInt8} {i : Nat} {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : EvalFn W "IxonDeserialize::get_expr_let" [stream, u64Value sz.toNat] h r h') :
    Heap.Extends h h' ∧
    sz.toNat < 4 ∧
    ∃ (bc : Ixon.BinderContract) (ty val body : Ixon.Expr)
      (n : Nat) (resPtr restPtr : SourceValue F),
      0 < n ∧
      (bytes.drop (i + n)).length < (bytes.drop i).length ∧
      (∀ fuel, (bytes.drop i).length < fuel →
        (do
          let binder ← Ixon.getBinderContract
          let some contract := Ixon.LetContract.ofFlags? sz binder
            | throw "getExpr: invalid let flags"
          let ty ← Ixon.getExprFuel fuel
          let val ← Ixon.getExprFuel fuel
          let body ← Ixon.getExprFuel fuel
          return Ixon.Expr.letE contract ty val body : Ixon.GetM Ixon.Expr)
          { idx := i, bytes := ⟨bytes.toArray⟩ } =
          .ok (.letE (letContractOfFlags sz.toNat bc) ty val body)
            { idx := i + n, bytes := ⟨bytes.toArray⟩ }) ∧
      r = .tuple [resPtr, restPtr] ∧
      RepExpr h' (.letE (letContractOfFlags sz.toNat bc) ty val body) resPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr :=
  getExprLet_refines_at_of_ih sz
    (fun _ rep' ev' => deserializeExpr_refines_at rep' ev') rep ev

/-- Read `count` expressions in wire order using `Ixon.getExpr`. -/
def getExprChildren : Nat → Ixon.GetM (List Ixon.Expr)
  | 0 => pure []
  | count + 1 => do
    let head ← Ixon.getExpr
    let tail ← getExprChildren count
    return head :: tail

/-- **Every terminating derivation of `IxonDeserialize::get_expr_list` at
reader offset `i`** refines `getExprChildren count` at `i`, allocating a
`RepShareVec` (`RepList exprListEnum RepExpr`) of the decoded expressions and
advancing the stream pointer by the consumed bytes. -/
theorem getExprList_refines_at (count : Nat) (hcount : count < 18446744073709551616)
    {bytes : List UInt8} {i : Nat} {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : EvalFn W "IxonDeserialize::get_expr_list" [stream, u64Value count] h r h') :
    Heap.Extends h h' ∧
    ∃ (exprs : List Ixon.Expr) (n : Nat) (listPtr restPtr : SourceValue F),
      getExprChildren count { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok exprs { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      exprs.length = count ∧
      r = .tuple [listPtr, restPtr] ∧
      RepShareVec h' exprs listPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  induction count generalizing i stream r h h' with
  | zero =>
    have body := ev.function_inv IxVM.IxonDeserialize.get_expr_list.lookup
      (by simp [IxVM.IxonDeserialize.get_expr_list, ControlLower.hasControl])
    simp only [IxVM.IxonDeserialize.get_expr_list] at body
    obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
    obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
    obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
    obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
    obtain ⟨rfl, rfl⟩ := args14.nil_inv
    rw [instanceName_plain_some] at callee9
    obtain ⟨hiz, rfl⟩ := u64IsZero_refines hcount callee9
    simp only [↓reduceIte] at hiz; subst hiz
    rw [matchPattern_bind] at mt4
    simp only [Except.ok.injEq, Option.some.injEq] at mt4; subst mt4
    obtain ⟨v18, m19, bs20, body21, d22, sel23, d24⟩ := d5.matchValue_inv
    obtain ⟨l25, rfl⟩ := d22.var_inv; simp at l25; subst l25
    rcases selectArm_literal_inv sel23 with ⟨_, rfl, rfl⟩ | ⟨hc26, _⟩
    · obtain ⟨vs28, args29, rfl⟩ := d24.tuple_inv
      obtain ⟨v30, vs31, m32, rfl, d33, args34⟩ := args29.cons_inv
      obtain ⟨v35, m36, d37, rfl, rfl⟩ := d33.store_inv
      obtain ⟨vs38, args39, rfl⟩ := d37.construct_inv
      obtain ⟨rfl, rfl⟩ := args39.nil_inv
      obtain ⟨v40, vs41, m42, rfl, d43, args44⟩ := args34.cons_inv
      obtain ⟨l45, rfl⟩ := d43.var_inv; simp at l45; subst l45
      obtain ⟨rfl, rfl⟩ := args44.nil_inv
      rw [value_type_construct]
      have ext := Aiur.Library.List.allocNil_extends exprListEnum m36
      refine ⟨ext, [], 0, (Aiur.Library.List.allocNil exprListEnum m36).1, stream,
        by simp [getExprChildren, pure, EStateM.pure], rfl, rfl,
        Aiur.Library.List.allocNil_rep exprListEnum RepExpr m36,
        Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext rep⟩
    · exact (hc26 rfl).elim
  | succ count ih =>
    have body := ev.function_inv IxVM.IxonDeserialize.get_expr_list.lookup
      (by simp [IxVM.IxonDeserialize.get_expr_list, ControlLower.hasControl])
    simp only [IxVM.IxonDeserialize.get_expr_list] at body
    obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
    obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
    obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
    obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
    obtain ⟨rfl, rfl⟩ := args14.nil_inv
    rw [instanceName_plain_some] at callee9
    obtain ⟨hiz, rfl⟩ := u64IsZero_refines hcount callee9
    simp only [Nat.succ_ne_zero, ↓reduceIte] at hiz; subst hiz
    rw [matchPattern_bind] at mt4
    simp only [Except.ok.injEq, Option.some.injEq] at mt4; subst mt4
    obtain ⟨v18, m19, bs20, body21, d22, sel23, d24⟩ := d5.matchValue_inv
    obtain ⟨l25, rfl⟩ := d22.var_inv; simp at l25; subst l25
    rcases selectArm_literal_inv sel23 with ⟨hc26, _, _⟩ | ⟨_, sel27⟩
    · simp at hc26
    · rcases selectArm_literal_inv sel27 with ⟨_, rfl, rfl⟩ | ⟨hc28, _⟩
      · obtain ⟨v30, m31, bs32, d33, mt34, d35⟩ := d24.letValue_inv
        obtain ⟨vs36, m37, args38, callee39⟩ := d33.call_inv
        obtain ⟨v40, vs41, m42, rfl, d43, args44⟩ := args38.cons_inv
        obtain ⟨l45, rfl⟩ := d43.var_inv; simp at l45; subst l45
        obtain ⟨rfl, rfl⟩ := args44.nil_inv
        rw [instanceName_plain_some] at callee39
        obtain ⟨ext1, e, n1, ePtr, restPtr1, _, _, hok1, rfl, eRep, hrep1⟩ :=
          getExpr_refines_at rep callee39
        obtain rfl := matchPattern_tuple2_bind rfl mt34
        obtain ⟨v54, m55, bs56, d57, mt58, d59⟩ := d35.letValue_inv
        obtain ⟨vs60, m61, args62, callee63⟩ := d57.call_inv
        obtain ⟨v64, vs65, m66, rfl, d67, args68⟩ := args62.cons_inv
        obtain ⟨l69, rfl⟩ := d67.var_inv; simp at l69; subst l69
        obtain ⟨v70, vs71, m72, rfl, d73, args74⟩ := args68.cons_inv
        obtain ⟨vs75, m76, args77, callee78⟩ := d73.call_inv
        obtain ⟨v79, vs80, m81, rfl, d82, args83⟩ := args77.cons_inv
        obtain ⟨l84, rfl⟩ := d82.var_inv; simp at l84; subst l84
        obtain ⟨rfl, rfl⟩ := args83.nil_inv
        rw [instanceName_plain_some] at callee78
        obtain ⟨hsp, rfl⟩ := u64SaturatingPred_refines hcount callee78
        simp only [Nat.add_sub_cancel] at hsp; subst hsp
        obtain ⟨rfl, rfl⟩ := args74.nil_inv
        rw [instanceName_plain_some] at callee63
        obtain ⟨ext2, tailExprs, n2, tailListPtr, restPtr2, hok2, hlen2, rfl, tailListRep, hrep2⟩ :=
          ih (by omega) hrep1 callee63
        obtain rfl := matchPattern_tuple2_bind rfl mt58
        obtain ⟨vs95, args96, rfl⟩ := d59.tuple_inv
        obtain ⟨v97, vs98, m99, rfl, d100, args101⟩ := args96.cons_inv
        obtain ⟨v102, m103, d104, rfl, rfl⟩ := d100.store_inv
        obtain ⟨vs105, args106, rfl⟩ := d104.construct_inv
        obtain ⟨v107, vs108, m109, rfl, d110, args111⟩ := args106.cons_inv
        obtain ⟨l115, rfl⟩ := d110.var_inv; simp at l115; subst l115
        obtain ⟨v116, vs117, m118, rfl, d119, args120⟩ := args111.cons_inv
        obtain ⟨l121, rfl⟩ := d119.var_inv; simp at l121; subst l121
        obtain ⟨rfl, rfl⟩ := args120.nil_inv
        obtain ⟨v122, vs123, m124, rfl, d125, args126⟩ := args101.cons_inv
        obtain ⟨l127, rfl⟩ := d125.var_inv; simp at l127; subst l127
        obtain ⟨rfl, rfl⟩ := args126.nil_inv
        rw [value_type_construct]
        have eRep' := eRep.mono ext2
        have ext3 := Aiur.Library.List.allocCons_extends exprListEnum ePtr tailListPtr m103
        refine ⟨(ext1.trans ext2).trans ext3, e :: tailExprs, n1 + n2,
          (Aiur.Library.List.allocCons exprListEnum ePtr tailListPtr m103).1, restPtr2,
          ?_, by simp [hlen2], rfl,
          Aiur.Library.List.allocCons_rep exprListEnum repExpr_heapMono₂ eRep' tailListRep,
          by rw [← Nat.add_assoc]; exact Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext3 hrep2⟩
        simp [getExprChildren, bind, EStateM.bind, hok1, hok2, pure, EStateM.pure, Nat.add_assoc]
      · exact (hc28 rfl).elim

/-- **Every terminating derivation of `IxonDeserialize::get_expr_list` from the
start of `bytes`** refines `getExprChildren count (start bytes)`, allocating a
`RepShareVec` of `count` expressions and advancing the stream. -/
theorem deserializeShareVec_refines (count : Nat) (hcount : count < 18446744073709551616)
    {bytes : List UInt8} {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h bytes stream)
    (ev : EvalFn W "IxonDeserialize::get_expr_list" [stream, u64Value count] h r h') :
    Heap.Extends h h' ∧
    ∃ (exprs : List Ixon.Expr) (n : Nat) (listPtr restPtr : SourceValue F),
      getExprChildren count (start bytes) =
        .ok exprs { idx := n, bytes := ⟨bytes.toArray⟩ } ∧
      exprs.length = count ∧
      r = .tuple [listPtr, restPtr] ∧
      RepShareVec h' exprs listPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop n) restPtr := by
  simpa [start] using getExprList_refines_at count hcount (i := 0) (by simpa using rep) ev

/-- Alias of `deserializeShareVec_refines` matching the Aiur function name
`IxonDeserialize::get_expr_list`. -/
theorem getExprList_refines (count : Nat) (hcount : count < 18446744073709551616)
    {bytes : List UInt8} {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h bytes stream)
    (ev : EvalFn W "IxonDeserialize::get_expr_list" [stream, u64Value count] h r h') :
    Heap.Extends h h' ∧
    ∃ (exprs : List Ixon.Expr) (n : Nat) (listPtr restPtr : SourceValue F),
      getExprChildren count (start bytes) =
        .ok exprs { idx := n, bytes := ⟨bytes.toArray⟩ } ∧
      exprs.length = count ∧
      r = .tuple [listPtr, restPtr] ∧
      RepShareVec h' exprs listPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop n) restPtr :=
  deserializeShareVec_refines count hcount rep ev

/-- **Every terminating derivation of `IxonDeserialize::get_sharing` at reader
offset `i`** reads a TagN0 count `t` followed by `t.value.toNat` shared
expressions into a `RepShareVec` at `i`. -/
theorem getSharing_refines_at {bytes : List UInt8} {i : Nat}
    {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : EvalFn W "IxonDeserialize::get_sharing" [stream] h r h') :
    Heap.Extends h h' ∧
    ∃ (t : Ixon.TagN) (n1 n2 : Nat) (exprs : List Ixon.Expr) (listPtr restPtr : SourceValue F),
      Ixon.getTagN 0 { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok t { idx := i + n1, bytes := ⟨bytes.toArray⟩ } ∧
      t.flag = 0 ∧
      getExprChildren t.value.toNat { idx := i + n1, bytes := ⟨bytes.toArray⟩ } =
        .ok exprs { idx := i + n1 + n2, bytes := ⟨bytes.toArray⟩ } ∧
      exprs.length = t.value.toNat ∧
      r = .tuple [listPtr, restPtr] ∧
      RepShareVec h' exprs listPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n1 + n2)) restPtr := by
  have body := ev.function_inv IxVM.IxonDeserialize.get_sharing.lookup
    (by simp [IxVM.IxonDeserialize.get_sharing, ControlLower.hasControl])
  simp only [IxVM.IxonDeserialize.get_sharing] at body
  obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
  obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
  obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
  obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
  obtain ⟨rfl, rfl⟩ := args14.nil_inv
  rw [instanceName_plain_some] at callee9
  obtain ⟨rfl, t, n1, restPtr1, hok1, hflag, hrep1, rfl⟩ := getTagN0_refines_at rep callee9
  obtain rfl := matchPattern_tuple2_bind rfl mt4
  obtain ⟨vs24, m25, args26, callee27⟩ := d5.call_inv
  obtain ⟨v28, vs29, m30, rfl, d31, args32⟩ := args26.cons_inv
  obtain ⟨l33, rfl⟩ := d31.var_inv; simp at l33; subst l33
  obtain ⟨v34, vs35, m36, rfl, d37, args38⟩ := args32.cons_inv
  obtain ⟨l39, rfl⟩ := d37.var_inv; simp at l39; subst l39
  obtain ⟨rfl, rfl⟩ := args38.nil_inv
  rw [instanceName_plain_some] at callee27
  obtain ⟨ext, exprs, n2, listPtr, restPtr2, hok2, hlen, rfl, listRep, dropRep⟩ :=
    getExprList_refines_at t.value.toNat t.value.toNat_lt hrep1 callee27
  exact ⟨ext, t, n1, n2, exprs, listPtr, restPtr2, hok1, hflag, hok2, hlen, rfl, listRep, dropRep⟩

/-- **Every terminating derivation of `IxonDeserialize::get_sharing` on a valid
byte stream** reads a TagN0 count `t` followed by `t.value.toNat` shared
expressions into a `RepShareVec`. -/
theorem getSharing_refines {bytes : List UInt8} {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h bytes stream)
    (ev : EvalFn W "IxonDeserialize::get_sharing" [stream] h r h') :
    Heap.Extends h h' ∧
    ∃ (t : Ixon.TagN) (n1 n2 : Nat) (exprs : List Ixon.Expr) (listPtr restPtr : SourceValue F),
      Ixon.getTagN 0 (start bytes) = .ok t { idx := n1, bytes := ⟨bytes.toArray⟩ } ∧
      t.flag = 0 ∧
      getExprChildren t.value.toNat (start (bytes.drop n1)) =
        .ok exprs { idx := n2, bytes := ⟨(bytes.drop n1).toArray⟩ } ∧
      exprs.length = t.value.toNat ∧
      r = .tuple [listPtr, restPtr] ∧
      RepShareVec h' exprs listPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' ((bytes.drop n1).drop n2) restPtr := by
  have body := ev.function_inv IxVM.IxonDeserialize.get_sharing.lookup
    (by simp [IxVM.IxonDeserialize.get_sharing, ControlLower.hasControl])
  simp only [IxVM.IxonDeserialize.get_sharing] at body
  obtain ⟨v0, m1, bs2, d3, mt4, d5⟩ := body.letValue_inv
  obtain ⟨vs6, m7, args8, callee9⟩ := d3.call_inv
  obtain ⟨v10, vs11, m12, rfl, d13, args14⟩ := args8.cons_inv
  obtain ⟨l15, rfl⟩ := d13.var_inv; simp at l15; subst l15
  obtain ⟨rfl, rfl⟩ := args14.nil_inv
  rw [instanceName_plain_some] at callee9
  obtain ⟨rfl, t, n1, restPtr1, hok1, hflag, hrep1, rfl⟩ := getTagN0_refines rep callee9
  obtain rfl := matchPattern_tuple2_bind rfl mt4
  obtain ⟨vs24, m25, args26, callee27⟩ := d5.call_inv
  obtain ⟨v28, vs29, m30, rfl, d31, args32⟩ := args26.cons_inv
  obtain ⟨l33, rfl⟩ := d31.var_inv; simp at l33; subst l33
  obtain ⟨v34, vs35, m36, rfl, d37, args38⟩ := args32.cons_inv
  obtain ⟨l39, rfl⟩ := d37.var_inv; simp at l39; subst l39
  obtain ⟨rfl, rfl⟩ := args38.nil_inv
  rw [instanceName_plain_some] at callee27
  obtain ⟨ext, exprs, n2, listPtr, restPtr2, hok2, hlen, rfl, listRep, dropRep⟩ :=
    deserializeShareVec_refines t.value.toNat t.value.toNat_lt hrep1 callee27
  exact ⟨ext, t, n1, n2, exprs, listPtr, restPtr2, hok1, hflag, hok2, hlen, rfl, listRep, dropRep⟩

end IxVM.Refinement.Deserialize
