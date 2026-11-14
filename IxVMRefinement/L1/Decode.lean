import IxVMRefinement.L1.DecodePayloads
import IxC.Ixon.Verify.ConstantBounds
import IxVMRefinement.Core.Specs.Callees

/-! # Top-level constant deserialization specs (`L1-B`)

Connects `ObsFn W "IxonDeserialize::get_constant"` and `ObsFn W "Ingress::load_verified_constant"`
to `Ixon.getConstant`, `Ixon.deConstantExact`, and `Ixon.deConstant`, establishing:

* `get_constant_info_by_variant_spec` and `get_constant_info_spec` (`Ixon.getConstantInfo`).
* `mut_const_lvls_spec`, `muts_max_lvls_spec`, and `max_lvls_spec` (`c.info.maxLvls < 2^32`).
* `assert_prj_empty_tables_spec` (`ConstantTablesValid c`).
* `get_constant_spec` (`Ixon.getConstant` + `RepConstant` + level-count and table invariants).
* `load_verified_constant_decode`: full-buffer exact decoding (`Ixon.deConstantExact` and
  `Ixon.deConstant`), `Hashed`, `Address.blake3Pure` equality, and `RepConstant`.
* `RepConstant.toConstShapeRep` and `recordShape_of_load_verified_constant` for `LoadFacts`.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics

namespace IxVM.Refinement.L1

open IxVM (F)
open IxVM.Refinement.Obs
open IxVM.Refinement.TagN
open IxVM.Refinement.Deserialize
open Aiur.Library.Blake3 (wordOfBytes)

/-! ## General 32-bit field comparison and list-nil helpers -/

/-- `UInt32::less_than_fields(x, y)` range-checks both arguments below `2^32` and tests `a < b`. -/
theorem lt_fields_both_spec {x y r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt32::less_than_fields" [x, y] h r h' cs) :
    ∃ a b : Nat, a < 4294967296 ∧ b < 4294967296 ∧
      x = .field (a : F) ∧ y = .field (b : F) ∧
      r = .field (if a < b then 1 else 0) ∧ h' = h := by
  obtain ⟨k10, v31, m32, cs42, v45, v56, m57, cs67, v70, v81, m82, cs92, v95, v118, m127, cs135,
    v159, m168, cs176, v188, x196, x204, x212, m214, cs223, v247, y256, ty12, pr54, ev44, pr79,
    ev69, pr104, ev94, ev137, heq146, ev178, heq187, ev225, op219, op211, op203, op271, op262,
    heq279, he281, he282, -⟩ := «UInt32::less_than_fields».obs ev
  obtain ⟨c0, c1, c2, c3, rfl, hm32⟩ := u32_fromFields ev44
  subst m32
  obtain ⟨d0, d1, d2, d3, rfl, hm57⟩ := u32_fromFields ev69
  subst m57
  obtain ⟨e0, e1, e2, e3, rfl, hm82⟩ := u32_fromFields ev94
  subst m82
  obtain ⟨rfl, hm127⟩ := u32_compact ev137
  subst m127
  obtain ⟨rfl, hm168⟩ := u32_compact ev178
  subst m168
  obtain ⟨rfl, hm214⟩ := u32_compact ev225
  subst heq146 heq187
  obtain rfl := binop_add op219
  obtain rfl := binop_sub op211
  obtain rfl := binop_div base_ne_zero op203
  obtain rfl := binop_sub op271
  obtain rfl := binop_mul op262
  have valid := Value.field.inj heq279
  rw [← base_cast] at valid
  have res := Aiur.Library.U32.compare_fields_sound Aiur.Library.U32.Goldilocks.compatible
    ((wordOfBytes c0 c1 c2 c3).toNat : F) ((wordOfBytes e0 e1 e2 e3).toNat : F)
    (leftWord := (wordOfBytes c0 c1 c2 c3).toNat) (rightWord := (wordOfBytes e0 e1 e2 e3).toNat)
    (difference := (wordOfBytes d0 d1 d2 d3).toNat)
    (word_lt _) (word_lt _) (word_lt _) rfl rfl valid
  rw [base_cast] at res
  refine ⟨(wordOfBytes c0 c1 c2 c3).toNat, (wordOfBytes e0 e1 e2 e3).toNat, ?_, ?_,
    rfl, rfl, ?_, he282.trans hm214⟩
  · simpa [Aiur.Library.U32.base] using word_lt (wordOfBytes c0 c1 c2 c3)
  · simpa [Aiur.Library.U32.base] using word_lt (wordOfBytes e0 e1 e2 e3)
  · rw [he281, res]

/-- Loading `"Nil"` from a `RepList` pointer implies the represented list is `[]`. -/
theorem repList_nil_of_load {α : Type} {enumSym : String}
    {elemRep : Heap F → α → SourceValue F → Prop}
    {h : Heap F} {xs : List α} {ptr : SourceValue F}
    (rep : Aiur.Library.List.RepList enumSym elemRep h xs ptr)
    (ld : loadValue h ptr = .ok (.construct enumSym "Nil" [])) :
    xs = [] := by
  cases rep with
  | nil _ => rfl
  | cons cell _ _ =>
    rw [Core.loadValue_enum_cell cell] at ld
    cases ld

/-- Loading `"Cons"` from a `RepList` pointer implies the represented list is non-empty. -/
theorem repList_ne_nil_of_load_cons {α : Type} {enumSym : String}
    {elemRep : Heap F → α → SourceValue F → Prop}
    {h : Heap F} {xs : List α} {ptr hd tl : SourceValue F}
    (rep : Aiur.Library.List.RepList enumSym elemRep h xs ptr)
    (ld : loadValue h ptr = .ok (.construct enumSym "Cons" [hd, tl])) :
    xs ≠ [] := by
  cases rep with
  | nil cell =>
    rw [Core.loadValue_enum_cell cell] at ld
    cases ld
  | cons _ _ _ => simp

theorem array_eq_empty_of_toList {α : Type} {a : Array α} (h : a.toList = []) : a = #[] := by
  cases a with
  | mk l =>
    simp at h
    subst h
    rfl

/-! ## `IxonDeserialize::get_constant_info_by_variant` and `get_constant_info` -/

/-- `IxonDeserialize::get_constant_info_by_variant` refines the singleton-tag dispatch of
`Ixon.getConstantInfo`. -/
theorem get_constant_info_by_variant_spec {v : UInt64} (hv : v.toNat < 256)
    {bytes : List UInt8} {i : Nat} {stream r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : ObsFn W "IxonDeserialize::get_constant_info_by_variant"
      [.field ((v.toNat : Nat) : F), stream] h r h' cs) :
    Heap.Extends h h' ∧
    ∃ (info : Ixon.ConstantInfo) (n : Nat) (infoVal restPtr : SourceValue F),
      (match v with
       | 0 => .defn <$> Ixon.getDefinition
       | 1 => .recr <$> Ixon.getRecursor
       | 2 => .axio <$> Ixon.getAxiom
       | 3 => .quot <$> Ixon.getQuotient
       | 4 => .cPrj <$> Ixon.getConstructorProj
       | 5 => .rPrj <$> Ixon.getRecursorProj
       | 6 => .iPrj <$> Ixon.getInductiveProj
       | 7 => .dPrj <$> Ixon.getDefinitionProj
       | val => (throw s!"getConstantInfo: invalid variant {val}" : Ixon.GetM Ixon.ConstantInfo))
        { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok info { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [infoVal, restPtr] ∧
      RepConstantInfo h' info infoVal ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  cases «IxonDeserialize::get_constant_info_by_variant».obs ev with
  | n0 m16 cs26 x_defn x_s hv14 ev28 he54 he79 _ =>
    have hv0 : v = 0 := UInt64.ext ((natCast_eq_zero_iff hv).mp (Value.field.inj hv14))
    subst hv0 he79 he54
    obtain ⟨ext, d, n, dVal, restPtr, hok, heq, dRep, hrep⟩ := get_definition_spec rep ev28
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq; rcases heq with ⟨rfl, rfl⟩
    exact ⟨ext, .defn d, n, _, restPtr, by simp [Functor.map, EStateM.map, hok], rfl,
      ⟨dVal, rfl, dRep⟩, hrep⟩
  | n1 m87 cs97 x_recr x_s _ hv85 ev99 he125 he150 _ =>
    have hv1 : v = 1 := UInt64.ext ((natCast_eq_one_iff hv).mp (Value.field.inj hv85))
    subst hv1 he150 he125
    obtain ⟨ext, rc, n, rcVal, restPtr, hok, heq, rcRep, hrep⟩ := get_recursor_spec rep ev99
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq; rcases heq with ⟨rfl, rfl⟩
    exact ⟨ext, .recr rc, n, _, restPtr, by simp [Functor.map, EStateM.map, hok], rfl,
      ⟨rcVal, rfl, rcRep⟩, hrep⟩
  | n2 m158 cs168 x_axim x_s _ _ hv156 ev170 he196 he221 _ =>
    have hv2 : v = 2 := UInt64.ext ((natCast_eq_ofNat_iff (n := 2) hv (by omega)).mp (Value.field.inj hv156))
    subst hv2 he221 he196
    obtain ⟨ext, ax, n, axVal, restPtr, hok, heq, axRep, hrep⟩ := get_axiom_spec rep ev170
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq; rcases heq with ⟨rfl, rfl⟩
    exact ⟨ext, .axio ax, n, _, restPtr, by simp [Functor.map, EStateM.map, hok], rfl,
      ⟨axVal, rfl, axRep⟩, hrep⟩
  | n3 m229 cs239 x_quot x_s _ _ _ hv227 ev241 he267 he292 _ =>
    have hv3 : v = 3 := UInt64.ext ((natCast_eq_ofNat_iff (n := 3) hv (by omega)).mp (Value.field.inj hv227))
    subst hv3 he292 he267
    obtain ⟨ext, q, n, qVal, restPtr, hok, heq, qRep, hrep⟩ := get_quotient_spec rep ev241
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq; rcases heq with ⟨rfl, rfl⟩
    exact ⟨ext, .quot q, n, _, restPtr, by simp [Functor.map, EStateM.map, hok], rfl,
      ⟨qVal, rfl, qRep⟩, hrep⟩
  | n4 m300 cs310 x_prj x_s _ _ _ _ hv298 ev312 he338 he363 _ =>
    have hv4 : v = 4 := UInt64.ext ((natCast_eq_ofNat_iff (n := 4) hv (by omega)).mp (Value.field.inj hv298))
    subst hv4 he363 he338
    obtain ⟨ext, p, n, pVal, restPtr, hok, heq, pRep, hrep⟩ := getConstructorProj_codec_at rep ev312
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq; rcases heq with ⟨rfl, rfl⟩
    exact ⟨ext, .cPrj p, n, _, restPtr, by simp [Functor.map, EStateM.map, hok], rfl,
      ⟨pVal, rfl, pRep⟩, hrep⟩
  | n5 m371 cs381 x_prj x_s _ _ _ _ _ hv369 ev383 he409 he434 _ =>
    have hv5 : v = 5 := UInt64.ext ((natCast_eq_ofNat_iff (n := 5) hv (by omega)).mp (Value.field.inj hv369))
    subst hv5 he434 he409
    obtain ⟨ext, p, n, pVal, restPtr, hok, heq, pRep, hrep⟩ := getRecursorProj_codec_at rep ev383
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq; rcases heq with ⟨rfl, rfl⟩
    exact ⟨ext, .rPrj p, n, _, restPtr, by simp [Functor.map, EStateM.map, hok], rfl,
      ⟨pVal, rfl, pRep⟩, hrep⟩
  | n6 m442 cs452 x_prj x_s _ _ _ _ _ _ hv440 ev454 he480 he505 _ =>
    have hv6 : v = 6 := UInt64.ext ((natCast_eq_ofNat_iff (n := 6) hv (by omega)).mp (Value.field.inj hv440))
    subst hv6 he505 he480
    obtain ⟨ext, p, n, pVal, restPtr, hok, heq, pRep, hrep⟩ := getInductiveProj_codec_at rep ev454
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq; rcases heq with ⟨rfl, rfl⟩
    exact ⟨ext, .iPrj p, n, _, restPtr, by simp [Functor.map, EStateM.map, hok], rfl,
      ⟨pVal, rfl, pRep⟩, hrep⟩
  | n7 m513 cs523 x_prj x_s _ _ _ _ _ _ _ hv511 ev525 he551 he576 _ =>
    have hv7 : v = 7 := UInt64.ext ((natCast_eq_ofNat_iff (n := 7) hv (by omega)).mp (Value.field.inj hv511))
    subst hv7 he576 he551
    obtain ⟨ext, p, n, pVal, restPtr, hok, heq, pRep, hrep⟩ := getDefinitionProj_codec_at rep ev525
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq; rcases heq with ⟨rfl, rfl⟩
    exact ⟨ext, .dPrj p, n, _, restPtr, by simp [Functor.map, EStateM.map, hok], rfl,
      ⟨pVal, rfl, pRep⟩, hrep⟩

/-- `IxonDeserialize::get_constant_info` after `get_tagn4` refines `Ixon.getConstantInfo`. -/
theorem get_constant_info_spec {t : Ixon.TagN} {n1 : Nat}
    {bytes : List UInt8} {i : Nat} {stream r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (htag : Ixon.getTagN 4 { idx := i, bytes := ⟨bytes.toArray⟩ } =
      .ok t { idx := i + n1, bytes := ⟨bytes.toArray⟩ })
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop (i + n1)) stream)
    (ev : ObsFn W "IxonDeserialize::get_constant_info"
      [.field (t.flag.toNat : F), u64Value t.value.toNat, stream] h r h' cs) :
    Heap.Extends h h' ∧
    ∃ (info : Ixon.ConstantInfo) (n2 : Nat) (infoVal restPtr : SourceValue F),
      Ixon.getConstantInfo { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok info { idx := i + (n1 + n2), bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [infoVal, restPtr] ∧
      RepConstantInfo h' info infoVal ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + (n1 + n2))) restPtr := by
  have hflag_lt : t.flag.toNat < 256 := t.flag.toNat_lt
  cases «IxonDeserialize::get_constant_info».obs ev with
  | n12 m16 cs26 x_mutuals x_s hv14 ev28 he62 he87 _ =>
    have hf12 : t.flag = 12 :=
      UInt8.ext ((natCast_eq_ofNat_iff (n := 12) hflag_lt (by omega)).mp (Value.field.inj hv14))
    subst he87 he62
    obtain ⟨ext, ms, n2, msPtr, restPtr, hok, heq, msRep, hrep⟩ :=
      get_mut_const_list_spec t.value.toNat t.value.toNat_lt rep ev28
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq; rcases heq with ⟨rfl, rfl⟩
    refine ⟨ext, .muts ms, n2, _, restPtr, ?_, rfl, ⟨msPtr, rfl, msRep⟩,
      by rw [← Nat.add_assoc]; exact hrep⟩
    have hloop :
      (do
        let mut arr : Array Ixon.MutConst := #[]
        for _ in [0:t.value.toNat] do
          arr := arr.push (← Ixon.getMutConst)
        return Ixon.ConstantInfo.muts arr) =
      (do
        let arr ← Ixon.getArray Ixon.getMutConst t.value.toNat
        return Ixon.ConstantInfo.muts arr) := by
      simp [Ixon.getArray]
    unfold Ixon.getConstantInfo
    simp only [bind, EStateM.bind, htag, hf12, Ixon.Constant.FLAG_MUTS, beq_self_eq_true, ↓reduceIte]
    rw [hloop]
    simp only [bind, EStateM.bind, hok, pure, EStateM.pure, Nat.add_assoc]
  | n13 w106 x_sz1 x_sz2 x_sz3 x_sz4 x_sz5 x_sz6 x_sz7
      v158 m161 x166 y167 m168 x174 y175 m176 x182 y183 m184 x190 y191 m192
      x198 y199 m200 x206 y207 m208
      cs217 cs231 cs245 cs259 cs273 cs287 cs301 cs322 v325 m328 cs336 v339
      _ hv93 hv104 ev219 ev233 op213 ev247 op205 ev261 op197 ev275 op189 ev289 op181 ev303 op173
      heq318 pr348 ev338 ev324 _ =>
    have hf13 : t.flag = 13 :=
      UInt8.ext ((natCast_eq_ofNat_iff (n := 13) hflag_lt (by omega)).mp (Value.field.inj hv93))
    have hsz : u64Value t.value.toNat =
        .tuple [w106, x_sz1, x_sz2, x_sz3, x_sz4, x_sz5, x_sz6, x_sz7] := hv104
    simp only [u64Value, Value.tuple.injEq, List.cons.injEq, and_true] at hsz
    rcases hsz with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := u8ToField_refines ev219.erase
    obtain ⟨rfl, rfl⟩ := u8ToField_refines ev233.erase
    obtain ⟨rfl, rfl⟩ := u8ToField_refines ev247.erase
    obtain ⟨rfl, rfl⟩ := u8ToField_refines ev261.erase
    obtain ⟨rfl, rfl⟩ := u8ToField_refines ev275.erase
    obtain ⟨rfl, rfl⟩ := u8ToField_refines ev289.erase
    obtain ⟨rfl, rfl⟩ := u8ToField_refines ev303.erase
    simp only [evalBinOp, Except.ok.injEq] at op213 op205 op197 op189 op181 op173
    subst op213 op205 op197 op189 op181 op173
    have hsum_cast :
        (((t.value.toNat / 256 % 256 + t.value.toNat / 65536 % 256 +
           t.value.toNat / 16777216 % 256 + t.value.toNat / 4294967296 % 256 +
           t.value.toNat / 1099511627776 % 256 + t.value.toNat / 281474976710656 % 256 +
           t.value.toNat / 72057594037927936 % 256 : Nat) : F)) = 0 := by
      push_cast
      exact Value.field.inj heq318
    have hsum_zero :
        t.value.toNat / 256 % 256 + t.value.toNat / 65536 % 256 +
          t.value.toNat / 16777216 % 256 + t.value.toNat / 4294967296 % 256 +
          t.value.toNat / 1099511627776 % 256 + t.value.toNat / 281474976710656 % 256 +
          t.value.toNat / 72057594037927936 % 256 = 0 :=
      (natCast_eq_zero_iff (by omega)).mp hsum_cast
    have hv_lt256 : t.value.toNat < 256 := by
      have hlt64 := t.value.toNat_lt
      omega
    simp only [u64Value, projectValue, List.getElem?_cons_zero, Except.ok.injEq] at pr348
    subst pr348
    obtain ⟨rfl, rfl⟩ := u8ToField_refines ev338.erase
    have hmod : t.value.toNat % 256 = t.value.toNat := Nat.mod_eq_of_lt hv_lt256
    rw [hmod] at ev324
    obtain ⟨ext, info, n2, infoVal, restPtr, hok, rfl, infoRep, hrep⟩ :=
      get_constant_info_by_variant_spec hv_lt256 rep ev324
    refine ⟨ext, info, n2, infoVal, restPtr, ?_, rfl, infoRep,
      by rw [← Nat.add_assoc]; exact hrep⟩
    unfold Ixon.getConstantInfo
    simp only [bind, EStateM.bind, htag, hf13, Ixon.Constant.FLAG_MUTS, Ixon.Constant.FLAG]
    have hne12 : ((13 : UInt8) == (12 : UInt8)) = false := by decide
    have heq13 : ((13 : UInt8) == (13 : UInt8)) = true := by decide
    simp only [hne12, Bool.false_eq_true, ↓reduceIte, heq13, hok, Nat.add_assoc]

/-! ## `IxonDeserialize::mut_const_lvls`, `muts_max_lvls`, and `max_lvls` -/

/-- Level-parameter count of a mutual block member. -/
def mutConstLvls : Ixon.MutConst → Nat
  | .defn d => d.lvls.toNat
  | .indc i => i.lvls.toNat
  | .recr r => r.lvls.toNat

/-- Every universe-parameter count in `info` lies below `bound`. -/
def infoLvlsLt (bound : Nat) : Ixon.ConstantInfo → Prop
  | .defn d => d.lvls.toNat < bound
  | .recr r => r.lvls.toNat < bound
  | .axio a => a.lvls.toNat < bound
  | .quot q => q.lvls.toNat < bound
  | .muts ms => ∀ m ∈ ms.toList, mutConstLvls m < bound
  | _ => True

/-- `IxonDeserialize::mut_const_lvls` reads `mutConstLvls mc` (checked `< 2^56`). -/
theorem mut_const_lvls_spec {mc : Ixon.MutConst} {mcVal r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (rep : RepMutConst h mc mcVal)
    (ev : ObsFn W "IxonDeserialize::mut_const_lvls" [mcVal] h r h' cs) :
    mutConstLvls mc < 72057594037927936 ∧
    r = .field ((mutConstLvls mc : Nat) : F) ∧
    h' = h := by
  cases mc with
  | defn d =>
    obtain ⟨dv, rfl, typPtr, valPtr, rfl, _, _⟩ := rep
    cases «IxonDeserialize::mut_const_lvls».obs ev with
    | Defn _ _ _ x_lvls _ _ _ hv15 ev74 _ =>
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv15
      rcases hv15 with ⟨_, _, _, _, rfl, _, _⟩
      simpa [mutConstLvls] using u64ToField_refines d.lvls.toNat_lt ev74.erase
    | Indc _ _ _ _ _ _ _ _ hv89 _ _ => cases hv89
    | Recr _ _ _ _ _ _ _ _ _ _ _ _ hv163 _ _ => cases hv163
  | indc ind =>
    obtain ⟨iv, rfl, typPtr, ctorsPtr, rfl, _, _⟩ := rep
    cases «IxonDeserialize::mut_const_lvls».obs ev with
    | Defn _ _ _ _ _ _ _ hv15 _ _ => cases hv15
    | Indc _ x_lvls _ _ _ _ _ _ hv89 ev148 _ =>
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv89
      rcases hv89 with ⟨_, _, rfl, _, _, _, _⟩
      simpa [mutConstLvls] using u64ToField_refines ind.lvls.toNat_lt ev148.erase
    | Recr _ _ _ _ _ _ _ _ _ _ _ _ hv163 _ _ => cases hv163
  | recr rc =>
    obtain ⟨rv, rfl, typPtr, rulesPtr, rfl, _, _⟩ := rep
    cases «IxonDeserialize::mut_const_lvls».obs ev with
    | Defn _ _ _ _ _ _ _ hv15 _ _ => cases hv15
    | Indc _ _ _ _ _ _ _ _ hv89 _ _ => cases hv89
    | Recr _ _ x_lvls _ _ _ _ _ _ _ _ _ hv163 ev240 _ =>
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv163
      rcases hv163 with ⟨_, _, _, rfl, _, _, _, _, _, _⟩
      simpa [mutConstLvls] using u64ToField_refines rc.lvls.toNat_lt ev240.erase

/-- `IxonDeserialize::muts_max_lvls` folds `max` over `ms`, range-checking every member's `lvls`
below `2^32`. -/
theorem muts_max_lvls_spec {ms : List Ixon.MutConst} {acc : Nat} (hacc : acc < 4294967296)
    {msPtr r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (rep : Aiur.Library.List.RepList mutConstListEnum RepMutConst h ms msPtr)
    (ev : ObsFn W "IxonDeserialize::muts_max_lvls" [msPtr, .field (acc : F)] h r h' cs) :
    (∀ m ∈ ms, mutConstLvls m < 4294967296) ∧
    (ms.foldl (fun a m => max a (mutConstLvls m)) acc) < 4294967296 ∧
    r = .field (((ms.foldl (fun a m => max a (mutConstLvls m)) acc : Nat) : F)) ∧
    h' = h := by
  induction ms generalizing acc msPtr r h h' cs with
  | nil =>
    cases rep with
    | nil cell =>
      cases «IxonDeserialize::muts_max_lvls».obs ev with
      | Nil _ he21 he22 _ =>
        exact ⟨by simp, hacc, he21, he22⟩
      | Cons_n1 _ _ _ _ _ _ _ _ ld12 _ _ _ _ =>
        rw [Core.loadValue_enum_cell cell] at ld12; cases ld12
      | Cons_n0 _ _ _ _ _ _ _ _ ld12 _ _ _ _ =>
        rw [Core.loadValue_enum_cell cell] at ld12; cases ld12
  | cons m tail ih =>
    cases rep with
    | cons cell hmRep htailRep =>
      cases «IxonDeserialize::muts_max_lvls».obs ev with
      | Nil ld12 _ _ _ =>
        rw [Core.loadValue_enum_cell cell] at ld12; cases ld12
      | Cons_n1 x_m x_rest v41 m42 cs52 m64 cs75 cs101 ld12 ev54 ev77 ev103 _ =>
        obtain ⟨_, hxs⟩ := Core.load_cell cell ld12
        simp only [List.cons.injEq, and_true] at hxs; rcases hxs with ⟨rfl, rfl⟩
        obtain ⟨hm56, rfl, rfl⟩ := mut_const_lvls_spec hmRep ev54
        obtain ⟨a, b, ha, hb, hacc_eq, hb_eq, hcmp, rfl⟩ := lt_fields_both_spec ev77
        have ha_eq : acc = a :=
          (natCast_eq_iff (by omega) (by omega)).mp (Value.field.inj hacc_eq)
        have hm_eq : mutConstLvls m = b :=
          (natCast_eq_iff (by omega) (by omega)).mp (Value.field.inj hb_eq)
        subst ha_eq hm_eq
        have hlt : a < mutConstLvls m := by
          by_cases hlt' : a < mutConstLvls m
          · exact hlt'
          · simp [hlt'] at hcmp
        have hmax : max a (mutConstLvls m) = mutConstLvls m := Nat.max_eq_right (Nat.le_of_lt hlt)
        obtain ⟨htail_lt, hfold_lt, hr, rfl⟩ := ih hb htailRep ev103
        refine ⟨?_, ?_, ?_, rfl⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hmem
          · exact hb
          · exact htail_lt x hmem
        · simpa [List.foldl_cons, hmax] using hfold_lt
        · simpa [List.foldl_cons, hmax] using hr
      | Cons_n0 x_m x_rest v41 m42 cs52 m64 cs75 cs129 ld12 ev54 ev77 ev131 _ =>
        obtain ⟨_, hxs⟩ := Core.load_cell cell ld12
        simp only [List.cons.injEq, and_true] at hxs; rcases hxs with ⟨rfl, rfl⟩
        obtain ⟨hm56, rfl, rfl⟩ := mut_const_lvls_spec hmRep ev54
        obtain ⟨a, b, ha, hb, hacc_eq, hb_eq, hcmp, rfl⟩ := lt_fields_both_spec ev77
        have ha_eq : acc = a :=
          (natCast_eq_iff (by omega) (by omega)).mp (Value.field.inj hacc_eq)
        have hm_eq : mutConstLvls m = b :=
          (natCast_eq_iff (by omega) (by omega)).mp (Value.field.inj hb_eq)
        subst ha_eq hm_eq
        have hge : mutConstLvls m ≤ a := by
          by_cases hlt' : a < mutConstLvls m
          · simp [hlt'] at hcmp
          · omega
        have hmax : max a (mutConstLvls m) = a := Nat.max_eq_left hge
        obtain ⟨htail_lt, hfold_lt, hr, rfl⟩ := ih ha htailRep ev131
        refine ⟨?_, ?_, ?_, rfl⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hmem
          · exact hb
          · exact htail_lt x hmem
        · simpa [List.foldl_cons, hmax] using hfold_lt
        · simpa [List.foldl_cons, hmax] using hr

/-- `IxonDeserialize::max_lvls` computes `info.maxLvls` and asserts `info.maxLvls < 2^32`
(plus `infoLvlsLt 2^32 info`). -/
theorem max_lvls_spec {info : Ixon.ConstantInfo} {infoVal r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (rep : RepConstantInfo h info infoVal)
    (ev : ObsFn W "IxonDeserialize::max_lvls" [infoVal] h r h' cs) :
    info.maxLvls < Ixon.maxLevelCount ∧
    infoLvlsLt 4294967296 info ∧
    r = .field ((info.maxLvls : Nat) : F) ∧
    h' = h := by
  cases «IxonDeserialize::max_lvls».obs ev with
  | run v329 m330 cs332 v338 m339 cs349 sg337 ev351 he368 he369 _ =>
    obtain ⟨n, hn32, hv329, _, rfl⟩ := lt_fields_zero_spec ev351
    subst he369 he368
    cases info with
    | defn d =>
      obtain ⟨dv, rfl, typPtr, valPtr, rfl, _, _⟩ := rep
      cases sg337 with
      | Defn _ _ _ x_lvls _ _ _ hv15 ev74 _ =>
        simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv15
        rcases hv15 with ⟨_, _, _, _, rfl, _, _⟩
        obtain ⟨hd56, hv_eq, rfl⟩ := u64ToField_refines d.lvls.toNat_lt ev74.erase
        have hd_eq : d.lvls.toNat = n :=
          (natCast_eq_iff (by omega) (by omega)).mp (Value.field.inj (hv_eq.symm.trans hv329))
        subst hd_eq
        exact ⟨hn32, hn32, hv_eq, rfl⟩
      | Recr _ _ _ _ _ _ _ _ _ _ hne84 _ _ _ => exact absurd rfl (hne84 _ rfl)
      | Axio _ _ _ _ hne84 _ _ _ _ => exact absurd rfl (hne84 _ rfl)
      | Quot _ _ _ _ hne84 _ _ _ _ _ => exact absurd rfl (hne84 _ rfl)
      | Muts _ _ hne84 _ _ _ _ _ _ => exact absurd rfl (hne84 _ rfl)
      | other hne84 _ _ _ _ _ _ _ => exact absurd rfl (hne84 _ rfl)
    | recr rc =>
      obtain ⟨rv, rfl, typPtr, rulesPtr, rfl, _, _⟩ := rep
      cases sg337 with
      | Defn _ _ _ _ _ _ _ hv15 _ _ => cases hv15
      | Recr _ _ x_lvls _ _ _ _ _ _ _ _ hv89 ev166 _ =>
        simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv89
        rcases hv89 with ⟨_, _, _, rfl, _, _, _, _, _, _⟩
        obtain ⟨hrc56, hv_eq, rfl⟩ := u64ToField_refines rc.lvls.toNat_lt ev166.erase
        have hrc_eq : rc.lvls.toNat = n :=
          (natCast_eq_iff (by omega) (by omega)).mp (Value.field.inj (hv_eq.symm.trans hv329))
        subst hrc_eq
        exact ⟨hn32, hn32, hv_eq, rfl⟩
      | Axio _ _ _ _ _ hne176 _ _ _ => exact absurd rfl (hne176 _ rfl)
      | Quot _ _ _ _ _ hne176 _ _ _ _ => exact absurd rfl (hne176 _ rfl)
      | Muts _ _ _ hne176 _ _ _ _ _ => exact absurd rfl (hne176 _ rfl)
      | other _ hne176 _ _ _ _ _ _ => exact absurd rfl (hne176 _ rfl)
    | axio ax =>
      obtain ⟨av, rfl, typPtr, rfl, _⟩ := rep
      cases sg337 with
      | Defn _ _ _ _ _ _ _ hv15 _ _ => cases hv15
      | Recr _ _ _ _ _ _ _ _ _ _ _ hv89 _ _ => cases hv89
      | Axio _ x_lvls _ _ _ _ hv181 ev222 _ =>
        simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv181
        rcases hv181 with ⟨_, _, rfl, _⟩
        obtain ⟨hax56, hv_eq, rfl⟩ := u64ToField_refines ax.lvls.toNat_lt ev222.erase
        have hax_eq : ax.lvls.toNat = n :=
          (natCast_eq_iff (by omega) (by omega)).mp (Value.field.inj (hv_eq.symm.trans hv329))
        subst hax_eq
        exact ⟨hn32, hn32, hv_eq, rfl⟩
      | Quot _ _ _ _ _ _ hne232 _ _ _ => exact absurd rfl (hne232 _ rfl)
      | Muts _ _ _ _ hne232 _ _ _ _ => exact absurd rfl (hne232 _ rfl)
      | other _ _ hne232 _ _ _ _ _ => exact absurd rfl (hne232 _ rfl)
    | quot q =>
      obtain ⟨qv, rfl, typPtr, rfl, _⟩ := rep
      cases sg337 with
      | Defn _ _ _ _ _ _ _ hv15 _ _ => cases hv15
      | Recr _ _ _ _ _ _ _ _ _ _ _ hv89 _ _ => cases hv89
      | Axio _ _ _ _ _ _ hv181 _ _ => cases hv181
      | Quot _ x_lvls _ _ _ _ _ hv237 ev278 _ =>
        simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv237
        rcases hv237 with ⟨_, _, rfl, _⟩
        obtain ⟨hq56, hv_eq, rfl⟩ := u64ToField_refines q.lvls.toNat_lt ev278.erase
        have hq_eq : q.lvls.toNat = n :=
          (natCast_eq_iff (by omega) (by omega)).mp (Value.field.inj (hv_eq.symm.trans hv329))
        subst hq_eq
        exact ⟨hn32, hn32, hv_eq, rfl⟩
      | Muts _ _ _ _ _ hne288 _ _ _ => exact absurd rfl (hne288 _ rfl)
      | other _ _ _ hne288 _ _ _ _ => exact absurd rfl (hne288 _ rfl)
    | muts ms =>
      obtain ⟨msPtr, rfl, hms⟩ := rep
      cases sg337 with
      | Defn _ _ _ _ _ _ _ hv15 _ _ => cases hv15
      | Recr _ _ _ _ _ _ _ _ _ _ _ hv89 _ _ => cases hv89
      | Axio _ _ _ _ _ _ hv181 _ _ => cases hv181
      | Quot _ _ _ _ _ _ _ hv237 _ _ => cases hv237
      | Muts x_members _ _ _ _ _ hv293 ev305 _ =>
        simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv293
        subst hv293
        have ev305' : ObsFn W "IxonDeserialize::muts_max_lvls"
            [msPtr, .field ((0 : Nat) : F)] h v329 m330 cs303 := by
          simpa using ev305
        obtain ⟨hall, hfold_lt, hv_eq, rfl⟩ := muts_max_lvls_spec (by omega) hms ev305'
        have hfold_eq :
            ms.toList.foldl (fun a m => max a (mutConstLvls m)) 0 = (Ixon.ConstantInfo.muts ms).maxLvls := by
          rw [← Array.foldl_toList]
          unfold Ixon.ConstantInfo.maxLvls
          congr 1
          funext acc m
          cases m <;> rfl
        rw [hfold_eq] at hfold_lt hv_eq
        exact ⟨hfold_lt, hall, hv_eq, rfl⟩
      | other _ _ _ _ hne322 _ _ _ => exact absurd rfl (hne322 _ rfl)
    | cPrj p =>
      obtain ⟨pv, rfl, _⟩ := rep
      cases sg337 with
      | Defn _ _ _ _ _ _ _ hv15 _ _ => cases hv15
      | Recr _ _ _ _ _ _ _ _ _ _ _ hv89 _ _ => cases hv89
      | Axio _ _ _ _ _ _ hv181 _ _ => cases hv181
      | Quot _ _ _ _ _ _ _ hv237 _ _ => cases hv237
      | Muts _ _ _ _ _ _ hv293 _ _ => cases hv293
      | other _ _ _ _ _ he326 he327 _ =>
        subst he327 he326
        exact ⟨by decide, trivial, by simp [Ixon.ConstantInfo.maxLvls], rfl⟩
    | rPrj p =>
      obtain ⟨pv, rfl, _⟩ := rep
      cases sg337 with
      | Defn _ _ _ _ _ _ _ hv15 _ _ => cases hv15
      | Recr _ _ _ _ _ _ _ _ _ _ _ hv89 _ _ => cases hv89
      | Axio _ _ _ _ _ _ hv181 _ _ => cases hv181
      | Quot _ _ _ _ _ _ _ hv237 _ _ => cases hv237
      | Muts _ _ _ _ _ _ hv293 _ _ => cases hv293
      | other _ _ _ _ _ he326 he327 _ =>
        subst he327 he326
        exact ⟨by decide, trivial, by simp [Ixon.ConstantInfo.maxLvls], rfl⟩
    | iPrj p =>
      obtain ⟨pv, rfl, _⟩ := rep
      cases sg337 with
      | Defn _ _ _ _ _ _ _ hv15 _ _ => cases hv15
      | Recr _ _ _ _ _ _ _ _ _ _ _ hv89 _ _ => cases hv89
      | Axio _ _ _ _ _ _ hv181 _ _ => cases hv181
      | Quot _ _ _ _ _ _ _ hv237 _ _ => cases hv237
      | Muts _ _ _ _ _ _ hv293 _ _ => cases hv293
      | other _ _ _ _ _ he326 he327 _ =>
        subst he327 he326
        exact ⟨by decide, trivial, by simp [Ixon.ConstantInfo.maxLvls], rfl⟩
    | dPrj p =>
      obtain ⟨pv, rfl, _⟩ := rep
      cases sg337 with
      | Defn _ _ _ _ _ _ _ hv15 _ _ => cases hv15
      | Recr _ _ _ _ _ _ _ _ _ _ _ hv89 _ _ => cases hv89
      | Axio _ _ _ _ _ _ hv181 _ _ => cases hv181
      | Quot _ _ _ _ _ _ _ hv237 _ _ => cases hv237
      | Muts _ _ _ _ _ _ hv293 _ _ => cases hv293
      | other _ _ _ _ _ he326 he327 _ =>
        subst he327 he326
        exact ⟨by decide, trivial, by simp [Ixon.ConstantInfo.maxLvls], rfl⟩

/-! ## `IxonDeserialize::assert_prj_empty_tables` -/

/-- Side-table emptiness invariants enforced by `IxonDeserialize::assert_prj_empty_tables`:
every projection constant has empty `sharing`, `refs`, `univs`, and `binders` tables, and an empty
`muts` block has empty `binders`. -/
def ConstantTablesValid (c : Ixon.Constant) : Prop :=
  match c.info with
  | .dPrj _ | .iPrj _ | .cPrj _ | .rPrj _ =>
    c.sharing = #[] ∧ c.refs = #[] ∧ c.univs = #[] ∧ c.binders = #[]
  | .muts ms => ms = #[] → c.binders = #[]
  | _ => True

/-- `IxonDeserialize::assert_prj_empty_tables` leaves the heap unchanged and establishes
`ConstantTablesValid`. -/
theorem assert_prj_empty_tables_spec {c : Ixon.Constant}
    {infoVal sharingPtr refsPtr univsPtr bindersPtr r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hinfo : RepConstantInfo h c.info infoVal)
    (hsh : RepShareVec h c.sharing.toList sharingPtr)
    (hrefs : Aiur.Library.List.RepList addressListEnum RepIxonAddressRef h c.refs.toList refsPtr)
    (hunivs : Aiur.Library.List.RepList univListEnum RepUnivPtr h c.univs.toList univsPtr)
    (hbinders : Aiur.Library.List.RepList binderBlockListEnum RepBinderBlock h c.binders.toList bindersPtr)
    (ev : ObsFn W "IxonDeserialize::assert_prj_empty_tables"
      [infoVal, sharingPtr, refsPtr, univsPtr, bindersPtr] h r h' cs) :
    h' = h ∧ ConstantTablesValid c := by
  cases «IxonDeserialize::assert_prj_empty_tables».obs ev with
  | DPrj w17 hv15 ld33 ld48 ld63 ld78 _ he86 _ =>
    subst he86
    refine ⟨rfl, ?_⟩
    cases hci : c.info with
    | dPrj _ =>
      simp only [ConstantTablesValid, hci]
      exact ⟨array_eq_empty_of_toList (repList_nil_of_load hsh ld33),
        array_eq_empty_of_toList (repList_nil_of_load hrefs ld48),
        array_eq_empty_of_toList (repList_nil_of_load hunivs ld63),
        array_eq_empty_of_toList (repList_nil_of_load hbinders ld78)⟩
    | _ =>
      rw [hci] at hinfo
      obtain ⟨_, heq, _⟩ := hinfo
      rw [heq] at hv15; cases hv15
  | IPrj w95 _ hv93 ld111 ld126 ld141 ld156 _ he164 _ =>
    subst he164
    refine ⟨rfl, ?_⟩
    cases hci : c.info with
    | iPrj _ =>
      simp only [ConstantTablesValid, hci]
      exact ⟨array_eq_empty_of_toList (repList_nil_of_load hsh ld111),
        array_eq_empty_of_toList (repList_nil_of_load hrefs ld126),
        array_eq_empty_of_toList (repList_nil_of_load hunivs ld141),
        array_eq_empty_of_toList (repList_nil_of_load hbinders ld156)⟩
    | _ =>
      rw [hci] at hinfo
      obtain ⟨_, heq, _⟩ := hinfo
      rw [heq] at hv93; cases hv93
  | CPrj w173 _ _ hv171 ld189 ld204 ld219 ld234 _ he242 _ =>
    subst he242
    refine ⟨rfl, ?_⟩
    cases hci : c.info with
    | cPrj _ =>
      simp only [ConstantTablesValid, hci]
      exact ⟨array_eq_empty_of_toList (repList_nil_of_load hsh ld189),
        array_eq_empty_of_toList (repList_nil_of_load hrefs ld204),
        array_eq_empty_of_toList (repList_nil_of_load hunivs ld219),
        array_eq_empty_of_toList (repList_nil_of_load hbinders ld234)⟩
    | _ =>
      rw [hci] at hinfo
      obtain ⟨_, heq, _⟩ := hinfo
      rw [heq] at hv171; cases hv171
  | RPrj w251 _ _ _ hv249 ld267 ld282 ld297 ld312 _ he320 _ =>
    subst he320
    refine ⟨rfl, ?_⟩
    cases hci : c.info with
    | rPrj _ =>
      simp only [ConstantTablesValid, hci]
      exact ⟨array_eq_empty_of_toList (repList_nil_of_load hsh ld267),
        array_eq_empty_of_toList (repList_nil_of_load hrefs ld282),
        array_eq_empty_of_toList (repList_nil_of_load hunivs ld297),
        array_eq_empty_of_toList (repList_nil_of_load hbinders ld312)⟩
    | _ =>
      rw [hci] at hinfo
      obtain ⟨_, heq, _⟩ := hinfo
      rw [heq] at hv249; cases hv249
  | Muts_Nil x_members _ _ _ _ hv327 ld345 ld363 _ he371 _ =>
    subst he371
    refine ⟨rfl, ?_⟩
    cases hci : c.info with
    | muts ms =>
      simp only [ConstantTablesValid, hci]
      intro _
      exact array_eq_empty_of_toList (repList_nil_of_load hbinders ld363)
    | _ =>
      rw [hci] at hinfo
      obtain ⟨_, heq, _⟩ := hinfo
      rw [heq] at hv327; cases hv327
  | Muts_Cons x_members w380 w381 _ _ _ _ hv327 ld345 _ he395 _ =>
    subst he395
    refine ⟨rfl, ?_⟩
    cases hci : c.info with
    | muts ms =>
      rw [hci] at hinfo
      obtain ⟨msPtr, heq, hmsRep⟩ := hinfo
      rw [heq] at hv327
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv327
      rcases hv327 with ⟨_, rfl⟩
      simp only [ConstantTablesValid, hci]
      intro hms_empty
      subst hms_empty
      exact absurd rfl (repList_ne_nil_of_load_cons hmsRep ld345)
    | _ =>
      rw [hci] at hinfo
      obtain ⟨_, heq, _⟩ := hinfo
      rw [heq] at hv327; cases hv327
  | other hne88 hne166 hne244 hne322 hne398 _ he405 _ =>
    subst he405
    refine ⟨rfl, ?_⟩
    cases hci : c.info with
    | dPrj _ => rw [hci] at hinfo; obtain ⟨_, heq, _⟩ := hinfo; exact absurd heq (hne88 _ rfl)
    | iPrj _ => rw [hci] at hinfo; obtain ⟨_, heq, _⟩ := hinfo; exact absurd heq (hne166 _ rfl)
    | cPrj _ => rw [hci] at hinfo; obtain ⟨_, heq, _⟩ := hinfo; exact absurd heq (hne244 _ rfl)
    | rPrj _ => rw [hci] at hinfo; obtain ⟨_, heq, _⟩ := hinfo; exact absurd heq (hne322 _ rfl)
    | muts _ => rw [hci] at hinfo; obtain ⟨_, heq, _⟩ := hinfo; exact absurd heq (hne398 _ rfl)
    | defn _ | recr _ | axio _ | quot _ => simp [ConstantTablesValid, hci]

/-! ## `IxonDeserialize::get_constant` and `Ingress::load_verified_constant` -/

/-- `IxonDeserialize::get_constant` at offset `i` refines `Ixon.getConstant`, constructing a
`RepConstant` value and establishing the level-count and projection-table invariants. -/
theorem get_constant_spec {bytes : List UInt8} {i : Nat}
    {stream r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : ObsFn W "IxonDeserialize::get_constant" [stream] h r h' cs) :
    Heap.Extends h h' ∧
    ∃ (c : Ixon.Constant) (n : Nat) (cVal restPtr : SourceValue F),
      Ixon.getConstant { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok c { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [cVal, restPtr] ∧
      c.info.maxLvls < Ixon.maxLevelCount ∧
      infoLvlsLt 4294967296 c.info ∧
      ConstantTablesValid c ∧
      RepConstant h' c cVal ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  cases «IxonDeserialize::get_constant».obs ev with
  | run m2 cs12 x_s x_flag x_size m59 cs69 x_info x_s2
      m110 cs120 x_sharing x_s3 m145 cs155 x_refs x_s4
      m180 cs190 x_univs x_s5 m215 cs225 v229 m238 cs246
      x_binders x_s6 v270 m271 cs281
      ev14 ev71 ev122 ev157 ev192 ev248 ev227 ev283 he328 he385 _ =>
    obtain ⟨rfl, tTag, n1, restPtr1, hok1, hrep1, heq1⟩ := getTagN4_refines_at rep ev14.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq1
    rcases heq1 with ⟨⟨rfl, rfl⟩, rfl⟩
    obtain ⟨ext2, info, n2, infoVal, restPtr2, hok2, heq2, infoRep, hrep2⟩ :=
      get_constant_info_spec hok1 hrep1 ev71
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq2; rcases heq2 with ⟨rfl, rfl⟩
    obtain ⟨ext3, sharing, n3, sharingPtr, restPtr3, hok3, heq3, shRep, hrep3⟩ :=
      getSharing_codec_at hrep2 ev122.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq3; rcases heq3 with ⟨rfl, rfl⟩
    obtain ⟨ext4, refs, n4, refsPtr, restPtr4, hok4, heq4, refsRep, hrep4⟩ :=
      getRefs_codec_at hrep3 ev157
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq4; rcases heq4 with ⟨rfl, rfl⟩
    obtain ⟨ext5, univs, n5, univsPtr, restPtr5, hok5, heq5, univsRep, hrep5⟩ :=
      getUnivs_codec_at hrep4 ev192
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq5; rcases heq5 with ⟨rfl, rfl⟩
    have infoRep180 := infoRep.mono ((ext3.trans ext4).trans ext5)
    obtain ⟨hmax_lt, hlvls_lt, hv229, rfl⟩ := max_lvls_spec infoRep180 ev248
    obtain ⟨ext6, binders, n6, bindersPtr, restPtr6, hok6, heq6, bindersRep, hrep6⟩ :=
      getBinders_refines_at hrep5 ev227.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq6; rcases heq6 with ⟨rfl, rfl⟩
    let c : Ixon.Constant := ⟨info, sharing, refs, univs, binders⟩
    have infoRep215 := infoRep180.mono ext6
    have shRep215 := RepShareVec.mono ext6 (RepShareVec.mono (ext4.trans ext5) shRep)
    have refsRep215 := refsRep.mono repIxonAddressRef_heapMono₂ (ext5.trans ext6)
    have univsRep215 := univsRep.mono repUnivPtr_heapMono₂ ext6
    obtain ⟨rfl, htables⟩ :=
      assert_prj_empty_tables_spec (c := c) infoRep215 shRep215 refsRep215 univsRep215 bindersRep ev283
    subst he385 he328
    refine ⟨(((ext2.trans ext3).trans ext4).trans ext5).trans ext6,
      c, (n1 + n2) + n3 + n4 + n5 + n6, _, restPtr6, ?_, rfl,
      hmax_lt, hlvls_lt, htables,
      ⟨infoVal, sharingPtr, refsPtr, univsPtr, bindersPtr, rfl,
        infoRep215, shRep215, refsRep215, univsRep215, bindersRep⟩,
      by simp only [Nat.add_assoc] at hrep6 ⊢; exact hrep6⟩
    unfold Ixon.getConstant Ixon.getConstantWithUnivs
    simp only [bind, EStateM.bind] at hok3 hok4 hok5 ⊢
    rw [hok2, hok3, hok4, hok5, hok6]
    simp only [pure, EStateM.pure, Nat.add_assoc]

/-- **`Ingress::load_verified_constant` decodes the exact hashed byte string**:
hashes `bytes`, checks `Address.blake3Pure ⟨bytes.toArray⟩ = ixAddr addr`, decodes `bytes` to `c`
with zero trailing bytes (`Ixon.deConstantExact ⟨bytes.toArray⟩ = .ok c` and
`Ixon.deConstant ⟨bytes.toArray⟩ = .ok c`), and returns a `RepConstant h' c r` value. -/
theorem load_verified_constant_decode {ty : Aiur.Ty} {addr : Vector UInt8 32}
    {a r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ha : Aiur.Library.Bytes.RepAddressRef ty h addr a)
    (ev : ObsFn W "Ingress::load_verified_constant" [a] h r h' cs) :
    Heap.Extends h h' ∧
    ∃ (bytes : List UInt8) (c : Ixon.Constant),
      Hashed cs ⟨bytes.toArray⟩ ∧
      Address.blake3Pure ⟨bytes.toArray⟩ = ixAddr addr ∧
      Ixon.deConstantExact ⟨bytes.toArray⟩ = .ok c ∧
      Ixon.deConstant ⟨bytes.toArray⟩ = .ok c ∧
      c.info.maxLvls < Ixon.maxLevelCount ∧
      infoLvlsLt 4294967296 c.info ∧
      ConstantTablesValid c ∧
      RepConstant h' c r := by
  obtain ⟨bytes, inp, rest, m, cs', ext1, hst, hashed, haddr, hget, hrest, _⟩ :=
    load_verified_constant_addr ha ev
  have hst0 : Aiur.Library.Bytes.RepByteStream byteStreamEnum m (bytes.drop 0) inp := by
    simpa [Stream, byteStreamEnum] using hst
  obtain ⟨ext2, c, n, cVal, restPtr, hok, heq, hmax_lt, hlvls_lt, htables, cRep, hdropRep⟩ :=
    get_constant_spec hst0 hget
  simp only [Nat.zero_add] at hok hdropRep
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq
  rcases heq with ⟨rfl, rfl⟩
  have hdrop_nil : bytes.drop n = [] := repList_nil_of_load hdropRep hrest
  have hlen_le : bytes.length ≤ n := List.drop_eq_nil_iff.mp hdrop_nil
  have hspan := Ixon.Verify.ConstantBounds.getConstant_bound
    { idx := 0, bytes := ⟨bytes.toArray⟩ } { idx := n, bytes := ⟨bytes.toArray⟩ } c
    (Nat.zero_le _) hok
  have hn_le : n ≤ bytes.length := by simpa [ByteArray.size] using hspan.within
  have hn_eq : n = (⟨bytes.toArray⟩ : ByteArray).size := by
    simp only [ByteArray.size, List.size_toArray]
    omega
  have hexact : Ixon.deConstantExact ⟨bytes.toArray⟩ = .ok c := by
    unfold Ixon.deConstantExact Ixon.runGetExact EStateM.run
    rw [hok]
    simp [hn_eq]
  have hde : Ixon.deConstant ⟨bytes.toArray⟩ = .ok c := by
    unfold Ixon.deConstant Ixon.runGet EStateM.run
    rw [hok]
  exact ⟨ext1.trans ext2, bytes, c, hashed, haddr, hexact, hde, hmax_lt, hlvls_lt, htables, cRep⟩

/-! ## Shallow constant shape bridge (`ConstShapeRep` and `LoadFacts.recordShape`) -/

theorem RepMutConst.toMutShape {h : Heap F} {mc : Ixon.MutConst} {v : SourceValue F}
    (rep : RepMutConst h mc v) : Core.Specs.Callees.MutShape h mc v := by
  cases mc with
  | defn _ => obtain ⟨dv, rfl, _⟩ := rep; exact ⟨dv, rfl⟩
  | indc _ => obtain ⟨iv, rfl, _⟩ := rep; exact ⟨iv, rfl⟩
  | recr _ => obtain ⟨rv, rfl, _⟩ := rep; exact ⟨rv, rfl⟩

private theorem repList_mutShape_of_repMutConst {h : Heap F} {ms : List Ixon.MutConst}
    {ptr : SourceValue F}
    (rep : Aiur.Library.List.RepList mutConstListEnum RepMutConst h ms ptr) :
    Core.Specs.Callees.MembersRep h ms ptr := by
  induction rep with
  | nil cell => exact .nil cell
  | cons cell hhead _ ih => exact .cons cell hhead.toMutShape ih

theorem RepConstantInfo.toInfoShape {h : Heap F} {info : Ixon.ConstantInfo} {v : SourceValue F}
    (rep : RepConstantInfo h info v) : Core.Specs.Callees.InfoShape h info v := by
  cases info with
  | defn _ => obtain ⟨x, rfl, _⟩ := rep; exact ⟨x, rfl⟩
  | recr _ => obtain ⟨x, rfl, _⟩ := rep; exact ⟨x, rfl⟩
  | axio _ => obtain ⟨x, rfl, _⟩ := rep; exact ⟨x, rfl⟩
  | quot _ => obtain ⟨x, rfl, _⟩ := rep; exact ⟨x, rfl⟩
  | cPrj _ => obtain ⟨x, rfl, _⟩ := rep; exact ⟨x, rfl⟩
  | rPrj _ => obtain ⟨x, rfl, _⟩ := rep; exact ⟨x, rfl⟩
  | iPrj _ => obtain ⟨x, rfl, _⟩ := rep; exact ⟨x, rfl⟩
  | dPrj _ => obtain ⟨x, rfl, _⟩ := rep; exact ⟨x, rfl⟩
  | muts _ =>
    obtain ⟨lp, rfl, hms⟩ := rep
    exact ⟨lp, rfl, repList_mutShape_of_repMutConst hms⟩

/-- Every `RepConstant` satisfies `Core.Specs.Callees.ConstShapeRep`. -/
theorem RepConstant.toConstShapeRep {h : Heap F} {c : Ixon.Constant} {v : SourceValue F}
    (rep : RepConstant h c v) : Core.Specs.Callees.ConstShapeRep h c v := by
  obtain ⟨iv, sh, rf, un, bd, rfl, hinfo, _, _, _, _⟩ := rep
  exact ⟨iv, sh, rf, un, bd, rfl, hinfo.toInfoShape⟩

/-- `Bounded.getConstant` agrees with `Ixon.getConstant` whenever it succeeds. -/
theorem getConstant_of_bounded {maxUnivNodes : Nat} {s s' : Ixon.GetState} {c : Ixon.Constant}
    (h : Ixon.Bounded.getConstant maxUnivNodes s = .ok c s') :
    Ixon.getConstant s = .ok c s' := by
  unfold Ixon.Bounded.getConstant Ixon.getConstant Ixon.getConstantWithUnivs at h ⊢
  obtain ⟨info, s1, h1, h⟩ := Ixon.Verify.TagN.bind_ok_inv h
  obtain ⟨tSh, s2, h2, h⟩ := Ixon.Verify.TagN.bind_ok_inv h
  obtain ⟨sh, s3, h3, h⟩ := Ixon.Verify.TagN.bind_ok_inv h
  obtain ⟨tRf, s4, h4, h⟩ := Ixon.Verify.TagN.bind_ok_inv h
  obtain ⟨rf, s5, h5, h⟩ := Ixon.Verify.TagN.bind_ok_inv h
  obtain ⟨tUn, s6, h6, h⟩ := Ixon.Verify.TagN.bind_ok_inv h
  obtain ⟨un, s7, h7, h⟩ := Ixon.Verify.TagN.bind_ok_inv h
  obtain ⟨bd, s8, h8, h⟩ := Ixon.Verify.TagN.bind_ok_inv h
  obtain ⟨rfl, rfl⟩ := Ixon.Verify.TagN.pure_ok_inv h
  obtain ⟨_, hun⟩ := Ixon.Verify.BoundedConstant.readBoundedUnivs_spec maxUnivNodes tUn.value.toNat s6 s7 un h7
  simp only [bind, EStateM.bind, h1, h2, h3, h4, h5, h6, hun, h8, pure, EStateM.pure]

/-- Every `LazyConstant` stored in `E.consts` materializes (`lc.get?`) to a constant whose
`Ixon.deConstant` of `lc.rawBytes` succeeds with that constant. Holds automatically on every
`E` constructed by `L1` (`Records`) as well as on any store satisfying `StoredCanonical`. -/
def EnvDecoded (E : Ixon.Env) : Prop :=
  ∀ x lc, E.consts.get? x = some lc →
    ∃ c, lc.get? = some c ∧ Ixon.deConstantExact lc.rawBytes = .ok c

theorem EnvDecoded.recordAt_deConstantExact {E : Ixon.Env} (hdec : EnvDecoded E)
    {x : Address} {cst : Ixon.Constant} (hrec : Ix.Cert.recordAt E x = some cst) :
    ∃ lc, E.consts.get? x = some lc ∧ lc.get? = some cst ∧
      Ixon.deConstantExact lc.rawBytes = .ok cst ∧
      Ixon.deConstant lc.rawBytes = .ok cst := by
  unfold Ix.Cert.recordAt at hrec
  cases hget : E.consts.get? x with
  | none => simp [hget] at hrec
  | some lc =>
    simp only [hget, Option.bind_some] at hrec
    obtain ⟨c', hc', hexact⟩ := hdec x lc hget
    rw [hrec] at hc'
    injection hc' with rfl
    have hde : Ixon.deConstant lc.rawBytes = .ok cst := by
      unfold Ixon.deConstantExact Ixon.runGetExact EStateM.run at hexact
      unfold Ixon.deConstant Ixon.runGet EStateM.run
      cases hrun : Ixon.getConstant { bytes := lc.rawBytes, idx := 0 } with
      | error _ _ => simp [hrun] at hexact
      | ok val st =>
        simp only [hrun] at hexact ⊢
        split at hexact <;> cases hexact
        rfl
    exact ⟨lc, hget, hrec, hexact, hde⟩

/-- `LoadFacts` / `Specs.Callees.load_verified_constant` companion: under `Good c cs` and
`EnvDecoded c.E` (or `Ixon.deConstant lc.rawBytes = .ok cst`), `load_verified_constant` returns a
`ConstShapeRep h' cst r` matching `Ix.Cert.recordAt c.E (ixAddr a) = some cst`. -/
theorem recordShape_of_load_verified_constant {c : Core.Ctx}
    {ap r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {a : Aiur.Library.Bytes.Address} {cst : Ixon.Constant}
    (hdec : EnvDecoded c.E)
    (ev : ObsFn W "Ingress::load_verified_constant" [ap] h r h' cs)
    (hg : Core.Good c cs)
    (ha : Aiur.Library.Bytes.RepAddressRef Core.addrTy h a ap)
    (hrec : Ix.Cert.recordAt c.E (Core.ixAddr a) = some cst) :
    Core.Specs.Callees.ConstShapeRep h' cst r := by
  obtain ⟨_, bytes, c', hashed, haddr, _, hde, _, _, _, cRep⟩ :=
    load_verified_constant_decode ha ev
  obtain ⟨lc, hlc, _, _, hde_lc⟩ := hdec.recordAt_deConstantExact hrec
  have haddr' : Address.blake3Pure ⟨bytes.toArray⟩ = Core.ixAddr a := haddr
  have hbytes_eq : (⟨bytes.toArray⟩ : ByteArray) = lc.rawBytes :=
    Core.load_escape hlc hg.1 ⟨bytes.toArray⟩ hashed haddr'
  rw [hbytes_eq, hde_lc] at hde
  injection hde with rfl
  exact cRep.toConstShapeRep

end IxVM.Refinement.L1
