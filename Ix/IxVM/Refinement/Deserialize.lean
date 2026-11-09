import Ix.IxVM.Refinement.Mirrors.Deserialize
import Ix.IxVM.Refinement.TagNWide

/-! # The Deserialize slice: `UInt64` and `IxonDeserialize` primitives

Track B, Phase 3 (`plans/ixvm-certification-gap.md`). On top of the generated
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
open IxVM.Checked (F)
open IxVM.Refinement.TagN

set_option linter.unusedSimpArgs false

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
    IxVM.Checked.coreTables.findMap? "UInt8::from_field" = some fromFieldMap := by
  decide +kernel

/-- **Any successful `UInt8::from_field` map call** returns its input unchanged,
leaves the heap unchanged, and witnesses that the input is a byte `< 256`. -/
theorem fromField_mapCall_inv {v w : SourceValue F} {h h' : Heap F}
    (hm : mapCall IxVM.Checked.source.tables "UInt8::from_field" [v] h = some (w, h')) :
    w = v ∧ h' = h ∧ ∃ x : Nat, x < 256 ∧ v = .field (x : F) := by
  unfold mapCall at hm
  cases looked : lookupMap IxVM.Checked.source.tables "UInt8::from_field" [v] with
  | error _ => simp [looked] at hm
  | ok row =>
    simp only [looked, Option.some.injEq, Prod.mk.injEq] at hm
    rcases hm with ⟨hrow, rfl⟩
    subst hrow
    obtain ⟨map, key, found, -, -, extracted, mem, -⟩ := Aiur.lookupMap_spec looked
    change IxVM.Checked.coreTables.findMap? "UInt8::from_field" = some map at found
    rw [find_fromFieldMap, Option.some.injEq] at found
    subst found
    have rows : IxVM.Checked.coreTables.mapRows fromFieldMap =
        IxVM.Checked.byteInputsTable.rows.zip IxVM.Checked.byteValuesTable.rows := by
      simp only [Aiur.Program.mapRows, show fromFieldMap.input = "UInt8::byte_inputs" from rfl,
        show fromFieldMap.output = "UInt8::byte_values" from rfl, IxVM.Checked.find_byteInputs,
        IxVM.Checked.find_byteValues]
    change (key, row) ∈ IxVM.Checked.coreTables.mapRows fromFieldMap at mem
    rw [rows] at mem
    simp only [IxVM.Checked.byteInputsTable, IxVM.Checked.byteValuesTable, List.map_map] at mem
    obtain ⟨x, hx, hkr⟩ := mem_zip_map_iff.mp mem
    simp only [List.mem_range] at hx
    simp only [Function.comp, IxVM.Checked.coreRow, IxVM.Checked.coreLeaf, List.map,
      Prod.mk.injEq] at hkr
    rcases hkr with ⟨rfl, rfl⟩
    have hv := Aiur.Value.toConstant_spec extracted
    simp [Constant.toValue, Value.mapAddress] at hv
    subst hv
    exact ⟨by simp [Constant.toValue, Value.mapAddress], rfl, x, hx, rfl⟩

theorem saturatingPred_step {b v w : SourceValue F} {h h' : Heap F} (hb : b ≠ .field 0)
    (op : evalBinOp .sub b (.field 1) = .ok v)
    (hm : mapCall IxVM.Checked.source.tables "UInt8::from_field" [v] h = some (w, h')) :
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
        (fun x => mapCall IxVM.Checked.source.tables "UInt8::from_field" [x.1] x.2))
      f = some res) :
    ∃ w, u64Measure w < u64Measure b ∧ f (w, h) = some res := by
  cases op : evalBinOp .sub b (.field 1) with
  | error _ => simp [op, Option.bind] at hrun
  | ok v =>
    simp only [op, Option.bind] at hrun
    cases hm : mapCall IxVM.Checked.source.tables "UInt8::from_field" [v] h with
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
  have body := ev.function_inv IxVM.Checked.Lookup.«IxonDeserialize::build_succ_chain»
    (by simp [IxVM.Checked.Fn.«IxonDeserialize::build_succ_chain», ControlLower.hasControl])
  simp only [IxVM.Checked.Fn.«IxonDeserialize::build_succ_chain»] at body
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
  have body := ev.function_inv IxVM.Checked.Lookup.«IxonDeserialize::get_u64_list»
    (by simp [IxVM.Checked.Fn.«IxonDeserialize::get_u64_list», ControlLower.hasControl])
  simp only [IxVM.Checked.Fn.«IxonDeserialize::get_u64_list»] at body
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
  have e0 := IxVM.Checked.natCast_inj (by omega) (by omega) h0
  have e1 := IxVM.Checked.natCast_inj (by omega) (by omega) h1
  have e2 := IxVM.Checked.natCast_inj (by omega) (by omega) h2
  have e3 := IxVM.Checked.natCast_inj (by omega) (by omega) h3
  have e4 := IxVM.Checked.natCast_inj (by omega) (by omega) h4
  have e5 := IxVM.Checked.natCast_inj (by omega) (by omega) h5
  have e6 := IxVM.Checked.natCast_inj (by omega) (by omega) h6
  have e7 := IxVM.Checked.natCast_inj (by omega) (by omega) h7
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
      have := IxVM.Checked.natCast_inj (a := n / 72057594037927936 % 256) (b := 0)
        (by omega) (by omega) (by simpa using heq)
      omega
    simp [Mirrors.«UInt64::to_field», u64Value, Mirrors.«UInt8::to_field», Builtin.apply,
      evalAssertEq, Value.pointerFree, hb7]

theorem natCast_eq_iff {a b : Nat} (ha : a < 256) (hb : b < 256) :
    ((a : F) = (b : F)) ↔ a = b :=
  ⟨IxVM.Checked.natCast_inj (by omega) (by omega), fun e => congrArg Nat.cast e⟩

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
    mapCall IxVM.Checked.source.tables "UInt8::from_field" [.field ((b : F) - 1)] h =
      some (.field ((b - 1 : Nat) : F), h) := by
  rcases b with _ | b
  · exact (hne rfl).elim
  · have hsub : ((b + 1 : Nat) : F) - 1 = (b : F) := by push_cast; ring
    rw [hsub]
    exact fromField_one (by omega) h

theorem fromField_add_one {b : Nat} (hb : b < 256) (hne : b ≠ 255) (h : Heap F) :
    mapCall IxVM.Checked.source.tables "UInt8::from_field" [.field ((b : F) + 1)] h =
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
  fun e => hne (IxVM.Checked.natCast_inj (by omega) (by omega) e)

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

end IxVM.Refinement.Deserialize
