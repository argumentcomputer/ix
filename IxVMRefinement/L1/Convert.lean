import IxVMRefinement.L1.ConvertExpr
import IxVMRefinement.Core.Loaded
import IxVMRefinement.Core.RomBound

/-! # Record-Level Constant Conversion (`Convert` part 2)

Observed-derivation (`ObsFn`) specifications for all record-level functions in
`IxVM/IxVM/Source/Convert.lean` (`IxVMRefinement.Obs.Convert1`):
* mutual-block root-offset and constructor-list helpers (`lvls_to_field_spec`,
  `count_ctors_spec`, `mut_const_roots_spec`, `muts_root_offset_spec`, `ctor_at_spec`);
* raw heap constant-info representations (`RawDefnValRep`, `RawAxioValRep`, `RawQuotValRep`,
  `RawInductValRep`, `RawCtorValRep`, `RawRuleRep`, `RawRulesRep`, `RawRecrValRep`) and their
  heap/blob monotonicity lemmas;
* constant conversion specs (`convert_definition_spec`, `convert_axiom_spec`,
  `convert_quotient_spec`, `convert_inductive_spec`, `convert_constructor_spec`,
  `convert_rec_rules_spec`, `convert_recursor_spec`);
* bridges to `IxVM.Consistency.StoredAs` and `Core.CIRep` (`RawDefnValRep.toCIRep`,
  `RawAxioValRep.toCIRep`, `RawQuotValRep.toCIRep`, `RawQuotValRep.toCIRep_stored`,
  `RawInductValRep.toCIRep`, `RawCtorValRep.toCIRep`, `RawRulesRep.toRulesRep`,
  `RawRecrValRep.toCIRep`).
-/

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library Aiur.Library.List

namespace IxVM.Refinement.L1

open IxVM (F)
open IxVM.Refinement.Obs
open IxVM.Refinement.TagN
open IxVM.Refinement.Deserialize

local notation "W" => IxVM.Refinement.Obs.W

private theorem val_cast_u56_conv {n : Nat} (h : n < 72057594037927936) :
    ZMod.val (n : F) = n := by
  have hP : (72057594037927936 : Nat) < U32.Goldilocks.modulus := by decide
  exact ZMod.val_cast_of_lt (Nat.lt_trans h hP)

private theorem recRuleLength_sym :
    (Instance.mk "Lists::length" [.named "Ixon::RecursorRule" []]).symbol =
      Names.«Lists::length<Ixon::RecursorRule>» := by
  decide +kernel

private theorem recRuleNode_sym :
    (Instance.mk "Lists::Node" [.named "Ixon::RecursorRule" []]).symbol =
      recursorRuleListEnum := by
  decide +kernel

private theorem repIxonAddressRef_to_core {h : Heap F} {a : _root_.Address} {ptr : SourceValue F}
    (rep : RepIxonAddressRef h a ptr) :
    ∃ b : Bytes.Address, Core.ixAddr b = a ∧ Bytes.RepAddressRef Core.addrTy h b ptr := by
  obtain ⟨b, rfl, hb⟩ := rep
  exact ⟨b, rfl, hb⟩

/-! ## `lvls_to_field`, `count_ctors`, `mut_const_roots`, `muts_root_offset`, and `ctor_at` -/

/-- `Convert::lvls_to_field` checks that the upper four bytes of a 64-bit word are zero (`< 2^32`)
and packs the lower four bytes into a single field element without allocation. -/
theorem lvls_to_field_spec {lvls : Nat} {r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hlvls : lvls < 18446744073709551616)
    (ev : ObsFn W "Convert::lvls_to_field" [u64Value lvls] h r h' calls) :
    lvls < 4294967296 ∧ r = .field (lvls : F) ∧ h' = h := by
  obtain ⟨x_b0, x_b1, x_b2, x_b3, x_b4, x_b5, x_b6, x_b7,
      v64, m67, _, v104, m107, _, v144, m147, _, v184, m187, _,
      x213, y214, m215, x221, y222, m223, x229, y230, m231, _,
      y252, _, y274, _, y296, _,
      hv11, ev77, heq92, ev117, heq132, ev157, heq172, ev197, heq212,
      ev242, ev264, op258, op236, ev286, op280, op228, ev308, op302, op220, _⟩ :=
    «Convert::lvls_to_field».obs ev
  unfold u64Value at hv11
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv11
  rcases hv11 with ⟨hb0_eq, hb1_eq, hb2_eq, hb3_eq, hb4_eq, hb5_eq, hb6_eq, hb7_eq⟩
  subst x_b0 x_b1 x_b2 x_b3 x_b4 x_b5 x_b6 x_b7
  obtain ⟨hv64, hm67⟩ := Lib.u8_to_field_spec ev77; rw [hv64] at heq92; subst m67
  obtain ⟨hv104, hm107⟩ := Lib.u8_to_field_spec ev117; rw [hv104] at heq132; subst m107
  obtain ⟨hv144, hm147⟩ := Lib.u8_to_field_spec ev157; rw [hv144] at heq172; subst m147
  obtain ⟨hv184, hm187⟩ := Lib.u8_to_field_spec ev197; rw [hv184] at heq212; subst m187
  obtain ⟨hx229, hm231⟩ := Lib.u8_to_field_spec ev242; subst x229 m231
  obtain ⟨hy252, hm223⟩ := Lib.u8_to_field_spec ev264; subst y252 m223
  obtain ⟨hy274, hm215⟩ := Lib.u8_to_field_spec ev286; subst y274 m215
  obtain ⟨hy296, hh'⟩ := Lib.u8_to_field_spec ev308; subst y296
  have hb4 : lvls / 4294967296 % 256 = 0 :=
    (natCast_eq_zero_iff (by omega)).mp (Value.field.inj heq92)
  have hb5 : lvls / 1099511627776 % 256 = 0 :=
    (natCast_eq_zero_iff (by omega)).mp (Value.field.inj heq132)
  have hb6 : lvls / 281474976710656 % 256 = 0 :=
    (natCast_eq_zero_iff (by omega)).mp (Value.field.inj heq172)
  have hb7 : lvls / 72057594037927936 % 256 = 0 :=
    (natCast_eq_zero_iff (by omega)).mp (Value.field.inj heq212)
  have hlt32 : lvls < 4294967296 := by omega
  have hsum : lvls % 256 + 256 * (lvls / 256 % 256) + 65536 * (lvls / 65536 % 256) +
      16777216 * (lvls / 16777216 % 256) = lvls := by omega
  simp only [evalBinOp, Except.ok.injEq] at op258; subst y230
  simp only [evalBinOp, Except.ok.injEq] at op236; subst x221
  simp only [evalBinOp, Except.ok.injEq] at op280; subst y222
  simp only [evalBinOp, Except.ok.injEq] at op228; subst x213
  simp only [evalBinOp, Except.ok.injEq] at op302; subst y214
  simp only [evalBinOp, Except.ok.injEq] at op220
  refine ⟨hlt32, ?_, hh'⟩
  rw [← op220]
  have hcast := congrArg (Nat.cast (R := F)) hsum
  push_cast at hcast
  exact congrArg Value.field hcast

/-- `Convert::count_ctors` computes the length of a represented constructor list as a field element
without allocation. -/
theorem count_ctors_spec {ctors : List Ixon.Constructor} :
    ∀ {x_cs r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      RepList constructorListEnum RepConstructor h ctors x_cs →
      ObsFn W "Convert::count_ctors" [x_cs] h r h' calls →
      r = .field (ctors.length : F) ∧ h' = h := by
  induction ctors with
  | nil =>
    intro x_cs r h h' calls hrep ev
    rcases «Convert::count_ctors».obs ev with
      ⟨_, he20, he21, _⟩ | ⟨w30, x_rest, _, _, _, ld12, _, _, _, _⟩
    · simp [he20, he21]
    · obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hrep ld12
      cases he
  | cons ct rest ih =>
    intro x_cs r h h' calls hrep ev
    rcases «Convert::count_ctors».obs ev with
      ⟨ld12, _, _, _⟩ | ⟨w30, x_rest, x41, m43, cs52, ld12, ev54, he63, op48, _⟩
    · have he := Lib.rep_nil_of_load hrep ld12
      cases he
    · obtain ⟨_, _, he, _, hrest⟩ := Lib.rep_cons_of_load hrep ld12
      injection he with _ htl; subst rest
      obtain ⟨hx41, hm43⟩ := ih hrest ev54
      subst x41
      simp only [evalBinOp, Except.ok.injEq] at op48
      refine ⟨?_, he63.trans hm43⟩
      rw [← op48]
      simp only [List.length_cons]
      push_cast
      rfl

/-- Number of binder-indexed root expressions contributed by a mutual-block member. -/
def mutConstRoots : Ixon.MutConst → Nat
  | .defn _ => 2
  | .indc ind => ind.ctors.size + 1
  | .recr rc => rc.rules.size + 1

/-- Prefix sum of `mutConstRoots` over the first `k` members of `ms`. -/
def mutsRootOffset : List Ixon.MutConst → Nat → Nat
  | _, 0 => 0
  | [], _ + 1 => 0
  | m :: ms, k + 1 => mutConstRoots m + mutsRootOffset ms k

/-- `Convert::mut_const_roots` computes `mutConstRoots m` as a field element without allocation. -/
theorem mut_const_roots_spec {m : Ixon.MutConst} {x_m r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hm : RepMutConst h m x_m)
    (ev : ObsFn W "Convert::mut_const_roots" [x_m] h r h' calls) :
    r = .field ((mutConstRoots m : Nat) : F) ∧ h' = h := by
  rcases «Convert::mut_const_roots».obs ev with
    ⟨w17, hv15, he23, he24, _⟩ |
    ⟨w54, w55, w56, w57, w58, x_ctors, x89, m91, cs100, _, hv31, ev102, he111, op96, _⟩ |
    ⟨w142, w143, w144, w145, w146, w147, w148, w149, x_rules, x195, m197, cs206,
      _, _, hv119, ev208, he217, op202, _⟩
  · cases m with
    | defn d =>
      rw [he23, he24]
      exact ⟨by simp [mutConstRoots], rfl⟩
    | indc i =>
      obtain ⟨iv, rfl, _⟩ := hm
      simp at hv15
    | recr rc =>
      obtain ⟨rv, rfl, _⟩ := hm
      simp at hv15
  · cases m with
    | defn d =>
      obtain ⟨dv, rfl, _⟩ := hm
      simp at hv31
    | recr rc =>
      obtain ⟨rv, rfl, _⟩ := hm
      simp at hv31
    | indc ind =>
      obtain ⟨iv, rfl, typPtr, ctorsPtr, hiv_eq, _, hctors⟩ := hm
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv31
      rcases hv31 with ⟨_, _, h1⟩
      rw [hiv_eq] at h1
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at h1
      rcases h1 with ⟨_, _, _, _, _, _, _, hct_eq⟩
      subst x_ctors
      obtain ⟨hx89, hm91⟩ := count_ctors_spec hctors ev102
      subst x89
      simp only [evalBinOp, Except.ok.injEq] at op96
      refine ⟨?_, he111.trans hm91⟩
      rw [← op96]
      simp only [mutConstRoots, Array.length_toList]
      push_cast
      rfl
  · cases m with
    | defn d =>
      obtain ⟨dv, rfl, _⟩ := hm
      simp at hv119
    | indc ind =>
      obtain ⟨iv, rfl, _⟩ := hm
      simp at hv119
    | recr rc =>
      obtain ⟨rv, rfl, typPtr, rulesPtr, hrv_eq, _, hrules⟩ := hm
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv119
      rcases hv119 with ⟨_, _, h1⟩
      rw [hrv_eq] at h1
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at h1
      rcases h1 with ⟨_, _, _, _, _, _, _, _, _, _, hrl_eq⟩
      subst x_rules
      rw [← recRuleLength_sym] at ev208
      rw [← recRuleNode_sym] at hrules
      obtain ⟨hx195, hm197⟩ := Lib.Lists.length_spec ev208 hrules
      subst x195
      simp only [evalBinOp, Except.ok.injEq] at op202
      refine ⟨?_, he217.trans hm197⟩
      rw [← op202]
      simp only [mutConstRoots, Array.length_toList]
      push_cast
      rfl

/-- `Convert::muts_root_offset` computes `mutsRootOffset ms idx.val` without allocation. -/
theorem muts_root_offset_spec {ms : List Ixon.MutConst} :
    ∀ {idx : F} {x_members r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      RepList mutConstListEnum RepMutConst h ms x_members →
      ObsFn W "Convert::muts_root_offset" [x_members, .field idx] h r h' calls →
      idx.val ≤ ms.length ∧ r = .field ((mutsRootOffset ms idx.val : Nat) : F) ∧ h' = h := by
  induction ms with
  | nil =>
    intro idx x_members r h h' calls hms ev
    rcases «Convert::muts_root_offset».obs ev with
      ⟨hv14, he15, he16, _⟩ |
      ⟨x_m, x_rest, _, _, _, _, _, _, _, ld33, _, _, _, _, _⟩
    · have hidx0 : idx = 0 := Value.field.inj hv14
      subst hidx0
      simp [ZMod.val_zero, mutsRootOffset, he15, he16]
    · obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hms ld33
      cases he
  | cons m rest ih =>
    intro idx x_members r h h' calls hms ev
    rcases «Convert::muts_root_offset».obs ev with
      ⟨hv14, he15, he16, _⟩ |
      ⟨x_m, x_rest, x51, y52, m53, cs62, cs76, v80,
        hne18, ld33, ev64, op101, ev78, op58, _⟩
    · have hidx0 : idx = 0 := Value.field.inj hv14
      subst hidx0
      simp [ZMod.val_zero, mutsRootOffset, he15, he16]
    · have hidx_ne : idx ≠ 0 := fun e => hne18 (congrArg Value.field e)
      obtain ⟨m', rest', he, hm, hrest⟩ := Lib.rep_cons_of_load hms ld33
      injection he with hm_eq hrest_eq; subst hm_eq hrest_eq
      obtain ⟨hx51, hm53⟩ := mut_const_roots_spec hm ev64
      subst x51 m53
      have hv80 := Lib.sub_one_inv op101
      subst hv80
      obtain ⟨hle, hy52, hh'⟩ := ih hrest ev78
      subst y52
      have hpred := Lib.val_sub_one hidx_ne
      simp only [evalBinOp, Except.ok.injEq] at op58
      refine ⟨by simp [List.length_cons]; omega, ?_, hh'⟩
      rw [← op58, ← hpred, mutsRootOffset]
      push_cast
      rfl

/-- `Convert::ctor_at` looks up constructor `idx.val` of `ctors` without allocation. -/
theorem ctor_at_spec {ctors : List Ixon.Constructor} :
    ∀ {idx : F} {x_cs r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      RepList constructorListEnum RepConstructor h ctors x_cs →
      ObsFn W "Convert::ctor_at" [x_cs, .field idx] h r h' calls →
      h' = h ∧ idx.val < ctors.length ∧ ∃ ct, ctors[idx.val]? = some ct ∧ RepConstructor h ct r := by
  induction ctors with
  | nil =>
    intro idx x_cs r h h' calls hctors ev
    rcases «Convert::ctor_at».obs ev with
      ⟨_, _, ld12, _, _, _, _⟩ | ⟨_, _, _, _, ld12, _, _, _, _⟩
    · obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hctors ld12; cases he
    · obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hctors ld12; cases he
  | cons ct rest ih =>
    intro idx x_cs r h h' calls hctors ev
    rcases «Convert::ctor_at».obs ev with
      ⟨x_c, x_rest, ld12, hv43, he45, he46, _⟩ |
      ⟨x_c, x_rest, cs55, v59, ld12, hne48, op80, ev57, _⟩
    · have hidx0 : idx = 0 := Value.field.inj hv43
      subst idx
      obtain ⟨ct', rest', he, hct, _⟩ := Lib.rep_cons_of_load hctors ld12
      injection he with h1 h2; subst ct' rest'
      rw [he45, he46]
      exact ⟨rfl, by simp, ct, by simp [ZMod.val_zero], hct⟩
    · have hidx_ne : idx ≠ 0 := fun e => hne48 (congrArg Value.field e)
      obtain ⟨ct', rest', he, _, hrest⟩ := Lib.rep_cons_of_load hctors ld12
      injection he with h1 h2; subst ct' rest'
      have hv59 := Lib.sub_one_inv op80
      subst v59
      obtain ⟨hh', hlt, ct_found, hget, hrep⟩ := ih hrest ev57
      have hpred := Lib.val_sub_one hidx_ne
      refine ⟨hh', by simp [List.length_cons]; omega, ct_found, ?_, hrep⟩
      rw [← hpred]
      exact hget

/-! ## Raw converted `KConstantInfo` representations and monotonicity -/

/-- `KernelTypes::KConstantInfo` constructor shape produced by `Convert::convert_definition`. -/
def defnValShape (d : Ixon.Definition) (tyPtr valPtr hint : SourceValue F) : SourceValue F :=
  match d.kind with
  | .defn => .construct Core.kciEnum "Defn"
      [.field (d.lvls.toNat : F), tyPtr, valPtr, repDefSafetyVal d.safety, hint]
  | .opaq => .construct Core.kciEnum "Opaque"
      [.field (d.lvls.toNat : F), tyPtr, valPtr, repBoolField (d.safety == .unsaf)]
  | .thm => .construct Core.kciEnum "Thm"
      [.field (d.lvls.toNat : F), tyPtr, valPtr]

/-- Raw converted `KConstantInfo` value for an `Ixon.Definition`. -/
def RawDefnValRep (refs recurAddrs : List _root_.Address) (univs : List Ixon.Univ)
    (sharing : List Ixon.Expr) (blobs : List (_root_.Address × ByteArray))
    (h : Heap F) (d : Ixon.Definition) (v : SourceValue F) : Prop :=
  d.lvls.toNat < 4294967296 ∧
  ∃ tyPtr valPtr hint,
    v = defnValShape d tyPtr valPtr hint ∧
    RawConvExpr refs recurAddrs univs sharing blobs h 4294967295 d.typ tyPtr ∧
    RawConvExpr refs recurAddrs univs sharing blobs h 4294967295 d.value valPtr

theorem RawDefnValRep.mono {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs₁ blobs₂ : List (_root_.Address × ByteArray)}
    {h₁ h₂ : Heap F} {d : Ixon.Definition} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (hsub : ∀ p ∈ blobs₁, p ∈ blobs₂)
    (raw : RawDefnValRep refs recurAddrs univs sharing blobs₁ h₁ d v) :
    RawDefnValRep refs recurAddrs univs sharing blobs₂ h₂ d v := by
  obtain ⟨hlvls, tyPtr, valPtr, hint, rfl, hty, hval⟩ := raw
  exact ⟨hlvls, tyPtr, valPtr, hint, rfl, hty.mono ext hsub, hval.mono ext hsub⟩

/-- Raw converted `KConstantInfo` value for an `Ixon.Axiom`. -/
def RawAxioValRep (refs recurAddrs : List _root_.Address) (univs : List Ixon.Univ)
    (sharing : List Ixon.Expr) (blobs : List (_root_.Address × ByteArray))
    (h : Heap F) (ax : Ixon.Axiom) (v : SourceValue F) : Prop :=
  ax.lvls.toNat < 4294967296 ∧
  ∃ tyPtr,
    v = .construct Core.kciEnum "Axiom"
      [.field (ax.lvls.toNat : F), tyPtr, repBoolField ax.isUnsafe] ∧
    RawConvExpr refs recurAddrs univs sharing blobs h 4294967295 ax.typ tyPtr

theorem RawAxioValRep.mono {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs₁ blobs₂ : List (_root_.Address × ByteArray)}
    {h₁ h₂ : Heap F} {ax : Ixon.Axiom} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (hsub : ∀ p ∈ blobs₁, p ∈ blobs₂)
    (raw : RawAxioValRep refs recurAddrs univs sharing blobs₁ h₁ ax v) :
    RawAxioValRep refs recurAddrs univs sharing blobs₂ h₂ ax v := by
  obtain ⟨hlvls, tyPtr, rfl, hty⟩ := raw
  exact ⟨hlvls, tyPtr, rfl, hty.mono ext hsub⟩

/-- Raw converted `KConstantInfo` value for an `Ixon.Quotient`. -/
def RawQuotValRep (refs recurAddrs : List _root_.Address) (univs : List Ixon.Univ)
    (sharing : List Ixon.Expr) (blobs : List (_root_.Address × ByteArray))
    (h : Heap F) (q : Ixon.Quotient) (v : SourceValue F) : Prop :=
  q.lvls.toNat < 4294967296 ∧
  ∃ tyPtr,
    v = .construct Core.kciEnum "Quot"
      [.field (q.lvls.toNat : F), tyPtr, repQuotKindVal q.kind] ∧
    RawConvExpr refs recurAddrs univs sharing blobs h 4294967295 q.typ tyPtr

theorem RawQuotValRep.mono {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs₁ blobs₂ : List (_root_.Address × ByteArray)}
    {h₁ h₂ : Heap F} {q : Ixon.Quotient} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (hsub : ∀ p ∈ blobs₁, p ∈ blobs₂)
    (raw : RawQuotValRep refs recurAddrs univs sharing blobs₁ h₁ q v) :
    RawQuotValRep refs recurAddrs univs sharing blobs₂ h₂ q v := by
  obtain ⟨hlvls, tyPtr, rfl, hty⟩ := raw
  exact ⟨hlvls, tyPtr, rfl, hty.mono ext hsub⟩

/-- Raw converted `KConstantInfo` value for an `Ixon.Inductive` member at `(blkAddr, indIdx)`. -/
def RawInductValRep (refs recurAddrs : List _root_.Address) (univs : List Ixon.Univ)
    (sharing : List Ixon.Expr) (blobs : List (_root_.Address × ByteArray))
    (h : Heap F) (ind : Ixon.Inductive) (blkAddr : _root_.Address) (indIdx : Nat)
    (v : SourceValue F) : Prop :=
  ind.lvls.toNat < 4294967296 ∧
  ind.params.toNat < 72057594037927936 ∧
  ind.indices.toNat < 72057594037927936 ∧
  ind.ctors.size < 72057594037927936 ∧
  indIdx < 72057594037927936 ∧
  ∃ (tyPtr blkPtr : SourceValue F) (b : Bytes.Address),
    Core.ixAddr b = blkAddr ∧
    Bytes.RepAddressRef Core.addrTy h b blkPtr ∧
    v = .construct Core.kciEnum "Induct"
      [.field (ind.lvls.toNat : F), tyPtr,
       .field (ind.params.toNat : F), .field (ind.indices.toNat : F),
       .field (ind.ctors.size : F), repBoolField ind.isUnsafe,
       blkPtr, .field (indIdx : F)] ∧
    RawConvExpr refs recurAddrs univs sharing blobs h 4294967295 ind.typ tyPtr

theorem RawInductValRep.mono {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs₁ blobs₂ : List (_root_.Address × ByteArray)}
    {h₁ h₂ : Heap F} {ind : Ixon.Inductive} {blkAddr : _root_.Address} {indIdx : Nat}
    {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (hsub : ∀ p ∈ blobs₁, p ∈ blobs₂)
    (raw : RawInductValRep refs recurAddrs univs sharing blobs₁ h₁ ind blkAddr indIdx v) :
    RawInductValRep refs recurAddrs univs sharing blobs₂ h₂ ind blkAddr indIdx v := by
  obtain ⟨hlvls, hp, hi, hc, hidx, tyPtr, blkPtr, b, hb, hblk, rfl, hty⟩ := raw
  obtain ⟨n, cellv, rfl, cell, hv⟩ := hblk
  exact ⟨hlvls, hp, hi, hc, hidx, tyPtr, _, b, hb,
    ⟨n, cellv, rfl, ext.getElem?_eq cell, hv⟩, rfl, hty.mono ext hsub⟩

/-- Raw converted `KConstantInfo` value for an `Ixon.Constructor` at `(blkAddr, indIdx)`. -/
def RawCtorValRep (refs recurAddrs : List _root_.Address) (univs : List Ixon.Univ)
    (sharing : List Ixon.Expr) (blobs : List (_root_.Address × ByteArray))
    (h : Heap F) (ct : Ixon.Constructor) (blkAddr : _root_.Address) (indIdx : Nat)
    (v : SourceValue F) : Prop :=
  ct.lvls.toNat < 4294967296 ∧
  ct.cidx.toNat < 72057594037927936 ∧
  ct.params.toNat < 72057594037927936 ∧
  ct.fields.toNat < 72057594037927936 ∧
  indIdx < 72057594037927936 ∧
  ∃ (tyPtr blkPtr : SourceValue F) (b : Bytes.Address),
    Core.ixAddr b = blkAddr ∧
    Bytes.RepAddressRef Core.addrTy h b blkPtr ∧
    v = .construct Core.kciEnum "Ctor"
      [.field (ct.lvls.toNat : F), tyPtr, blkPtr, .field (indIdx : F),
       .field (ct.cidx.toNat : F), .field (ct.params.toNat : F),
       .field (ct.fields.toNat : F), repBoolField ct.isUnsafe] ∧
    RawConvExpr refs recurAddrs univs sharing blobs h 4294967295 ct.typ tyPtr

theorem RawCtorValRep.mono {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs₁ blobs₂ : List (_root_.Address × ByteArray)}
    {h₁ h₂ : Heap F} {ct : Ixon.Constructor} {blkAddr : _root_.Address} {indIdx : Nat}
    {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (hsub : ∀ p ∈ blobs₁, p ∈ blobs₂)
    (raw : RawCtorValRep refs recurAddrs univs sharing blobs₁ h₁ ct blkAddr indIdx v) :
    RawCtorValRep refs recurAddrs univs sharing blobs₂ h₂ ct blkAddr indIdx v := by
  obtain ⟨hlvls, hcidx, hp, hf, hidx, tyPtr, blkPtr, b, hb, hblk, rfl, hty⟩ := raw
  obtain ⟨n, cellv, rfl, cell, hv⟩ := hblk
  exact ⟨hlvls, hcidx, hp, hf, hidx, tyPtr, _, b, hb,
    ⟨n, cellv, rfl, ext.getElem?_eq cell, hv⟩, rfl, hty.mono ext hsub⟩

/-- Raw converted `KernelTypes::KRecRule` at constructor index `j`. -/
def RawRuleRep (refs recurAddrs : List _root_.Address) (univs : List Ixon.Univ)
    (sharing : List Ixon.Expr) (blobs : List (_root_.Address × ByteArray))
    (h : Heap F) (j : Nat) (ru : Ixon.RecursorRule) (v : SourceValue F) : Prop :=
  ru.fields.toNat < 72057594037927936 ∧
  ∃ rhsPtr,
    v = .construct Core.krrEnum "Mk"
      [.field (j : F), .field (ru.fields.toNat : F), rhsPtr] ∧
    RawConvExpr refs recurAddrs univs sharing blobs h 4294967295 ru.rhs rhsPtr

theorem RawRuleRep.mono {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs₁ blobs₂ : List (_root_.Address × ByteArray)}
    {h₁ h₂ : Heap F} {j : Nat} {ru : Ixon.RecursorRule} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (hsub : ∀ p ∈ blobs₁, p ∈ blobs₂)
    (raw : RawRuleRep refs recurAddrs univs sharing blobs₁ h₁ j ru v) :
    RawRuleRep refs recurAddrs univs sharing blobs₂ h₂ j ru v := by
  obtain ⟨hf, rhsPtr, rfl, hrhs⟩ := raw
  exact ⟨hf, rhsPtr, rfl, hrhs.mono ext hsub⟩

/-- Raw converted `Lists::List<KernelTypes::KRecRule>` starting at constructor index `j`. -/
inductive RawRulesRep (refs recurAddrs : List _root_.Address) (univs : List Ixon.Univ)
    (sharing : List Ixon.Expr) (blobs : List (_root_.Address × ByteArray))
    (h : Heap F) : Nat → List Ixon.RecursorRule → SourceValue F → Prop where
  | nil {j addr : Nat}
      (cell : h[addr]? = some (.construct Core.krrListEnum "Nil" [])) :
      RawRulesRep refs recurAddrs univs sharing blobs h j []
        (.ptr (.enum Core.krrListEnum) addr)
  | cons {j addr : Nat} {v rest : SourceValue F}
      {ru : Ixon.RecursorRule} {rus : List Ixon.RecursorRule}
      (cell : h[addr]? = some (.construct Core.krrListEnum "Cons" [v, rest]))
      (hr : RawRuleRep refs recurAddrs univs sharing blobs h j ru v)
      (rs : RawRulesRep refs recurAddrs univs sharing blobs h (j + 1) rus rest) :
      RawRulesRep refs recurAddrs univs sharing blobs h j (ru :: rus)
        (.ptr (.enum Core.krrListEnum) addr)

theorem RawRulesRep.mono {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs₁ blobs₂ : List (_root_.Address × ByteArray)}
    {h₁ h₂ : Heap F} {j : Nat} {rus : List Ixon.RecursorRule} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (hsub : ∀ p ∈ blobs₁, p ∈ blobs₂)
    (raw : RawRulesRep refs recurAddrs univs sharing blobs₁ h₁ j rus p) :
    RawRulesRep refs recurAddrs univs sharing blobs₂ h₂ j rus p := by
  induction raw with
  | nil cell => exact .nil (ext.getElem?_eq cell)
  | cons cell hr _ ih => exact .cons (ext.getElem?_eq cell) (hr.mono ext hsub) ih

/-- Raw converted `KConstantInfo` value for an `Ixon.Recursor` at `(blkAddr, recIdx)`.
Note that `Convert::convert_recursor` converts `rc.typ` with an empty recursive-address list `[]`
and `rc.rules` with `recurAddrs`. -/
def RawRecrValRep (refs recurAddrs : List _root_.Address) (univs : List Ixon.Univ)
    (sharing : List Ixon.Expr) (blobs : List (_root_.Address × ByteArray))
    (h : Heap F) (rc : Ixon.Recursor) (blkAddr : _root_.Address) (recIdx : Nat)
    (v : SourceValue F) : Prop :=
  rc.lvls.toNat < 4294967296 ∧
  rc.params.toNat < 72057594037927936 ∧
  rc.indices.toNat < 72057594037927936 ∧
  rc.motives.toNat < 72057594037927936 ∧
  rc.minors.toNat < 72057594037927936 ∧
  recIdx < 72057594037927936 ∧
  ∃ (tyPtr rulesPtr blkPtr : SourceValue F) (b : Bytes.Address),
    Core.ixAddr b = blkAddr ∧
    Bytes.RepAddressRef Core.addrTy h b blkPtr ∧
    v = .construct Core.kciEnum "Rec"
      [.field (rc.lvls.toNat : F), tyPtr,
       .field (rc.params.toNat : F), .field (rc.indices.toNat : F),
       .field (rc.motives.toNat : F), .field (rc.minors.toNat : F),
       rulesPtr, repBoolField rc.k, repBoolField rc.isUnsafe,
       blkPtr, .field (recIdx : F)] ∧
    RawConvExpr refs [] univs sharing blobs h 4294967295 rc.typ tyPtr ∧
    RawRulesRep refs recurAddrs univs sharing blobs h 0 rc.rules.toList rulesPtr

theorem RawRecrValRep.mono {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs₁ blobs₂ : List (_root_.Address × ByteArray)}
    {h₁ h₂ : Heap F} {rc : Ixon.Recursor} {blkAddr : _root_.Address} {recIdx : Nat}
    {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (hsub : ∀ p ∈ blobs₁, p ∈ blobs₂)
    (raw : RawRecrValRep refs recurAddrs univs sharing blobs₁ h₁ rc blkAddr recIdx v) :
    RawRecrValRep refs recurAddrs univs sharing blobs₂ h₂ rc blkAddr recIdx v := by
  obtain ⟨hlvls, hp, hi, hm, hmi, hidx, tyPtr, rulesPtr, blkPtr, b, hb, hblk, rfl, hty, hrls⟩ := raw
  obtain ⟨n, cellv, rfl, cell, hv⟩ := hblk
  exact ⟨hlvls, hp, hi, hm, hmi, hidx, tyPtr, rulesPtr, _, b, hb,
    ⟨n, cellv, rfl, ext.getElem?_eq cell, hv⟩, rfl,
    hty.mono ext hsub, hrls.mono ext hsub⟩

/-! ## Record-level `Convert::*` observed-derivation specifications -/

/-- `Convert::convert_definition` specification. -/
theorem convert_definition_spec {d : Ixon.Definition} {sharing : List Ixon.Expr}
    {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {x_d shPtr refsPtr recPtr univsPtr x_hint tbl x_base r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hd : RepDefinition h d x_d)
    (hsh : RepShareVec h sharing shPtr)
    (hrefs : RepList addressListEnum RepIxonAddressRef h refs refsPtr)
    (hrecs : RepList addressListEnum RepIxonAddressRef h recurAddrs recPtr)
    (hunivs : RepList univListEnum RepUnivPtr h univs univsPtr)
    (htbl : RepBinderTree 4294967296 h tbl)
    (ev : ObsFn W "Convert::convert_definition"
      [x_d, shPtr, refsPtr, recPtr, univsPtr, x_hint, tbl, x_base] h r h' calls) :
    Heap.Extends h h' ∧ ∃ blobs : List (_root_.Address × ByteArray),
      HashedPairs calls blobs ∧
      RawDefnValRep refs recurAddrs univs sharing blobs h' d r := by
  obtain ⟨typPtr, valPtr, rfl, htyp, hval⟩ := hd
  rcases «Convert::convert_definition».obs ev with
    ⟨x_safety, w17, x_lvls, x_typ, x_value, v48, m49, cs59, v118, m119, cs129, v138,
      v196, m197, cs207, hv15, ev61, op194, ev131, ev209, he242, he278, hc279⟩ |
    ⟨x_safety, w17, x_lvls, x_typ, x_value, v48, m49, cs59, v118, m119, cs129, v138,
      v196, m197, cs207, v313, m314, cs316,
      hv15, ev61, op194, ev131, ev209, sg321, he329, he358, hc359⟩ |
    ⟨x_safety, w17, x_lvls, x_typ, x_value, v48, m49, cs59, v118, m119, cs129, v138,
      v196, m197, cs207, hv15, ev61, op194, ev131, ev209, he373, he395, hc396⟩
  · -- Definition
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv15
    rcases hv15 with ⟨_, _, hkind, hsaf, _, hlvls_eq, htyp_eq, hval_eq⟩
    subst x_safety x_lvls x_typ x_value
    have hdk : d.kind = .defn := by
      cases hk : d.kind <;> simp [repDefKindVal, hk] at hkind; rfl
    obtain ⟨ext1, blobs1, hhp1, hraw_ty⟩ :=
      convert_root_spec htyp hsh hrefs hrecs hunivs htbl ev61
    obtain ⟨ext2, blobs2, hhp2, hraw_val⟩ :=
      convert_root_spec (hval.mono ext1) (RepShareVec.mono ext1 hsh)
      (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrefs)
      (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrecs)
      (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext1 hunivs)
      (htbl.mono ext1) ev131
    obtain ⟨hlvls32, hv196, hm197⟩ := lvls_to_field_spec d.lvls.toNat_lt ev209
    rw [he278, hm197]; subst v196
    refine ⟨ext1.trans ext2, blobs1 ++ blobs2,
      HashedPairs.append
        (hhp1.sub (by rw [hc279]; intro c hc; simp [hc]))
        (hhp2.sub (by rw [hc279]; intro c hc; simp [hc])),
      hlvls32, v48, v118, x_hint, ?_,
      hraw_ty.mono ext2 (fun _ hm => List.mem_append_left _ hm),
      hraw_val.mono (Heap.Extends.refl _) (fun _ hm => List.mem_append_right _ hm)⟩
    simp [defnValShape, hdk, he242]
  · -- Opaque
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv15
    rcases hv15 with ⟨_, _, hkind, hsaf, _, hlvls_eq, htyp_eq, hval_eq⟩
    subst x_safety x_lvls x_typ x_value
    have hdk : d.kind = .opaq := by
      cases hk : d.kind <;> simp [repDefKindVal, hk] at hkind; rfl
    obtain ⟨ext1, blobs1, hhp1, hraw_ty⟩ :=
      convert_root_spec htyp hsh hrefs hrecs hunivs htbl ev61
    obtain ⟨ext2, blobs2, hhp2, hraw_val⟩ :=
      convert_root_spec (hval.mono ext1) (RepShareVec.mono ext1 hsh)
      (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrefs)
      (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrecs)
      (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext1 hunivs)
      (htbl.mono ext1) ev131
    obtain ⟨hlvls32, hv196, hm197⟩ := lvls_to_field_spec d.lvls.toNat_lt ev209
    subst v196 m197
    have hv313 : v313 = repBoolField (d.safety == .unsaf) ∧ m314 = m119 := by
      rcases sg321 with ⟨hv301, rfl, rfl, _⟩ | ⟨hne306, rfl, rfl, _⟩
      · refine ⟨?_, rfl⟩
        cases hs : d.safety <;> simp [repDefSafetyVal, hs] at hv301
        rw [hs]; rfl
      · refine ⟨?_, rfl⟩
        cases hs : d.safety
        · exact (hne306 [] rfl (by simp [repDefSafetyVal, hs])).elim
        · rw [hs]; rfl
        · rw [hs]; rfl
    rcases hv313 with ⟨hv313_eq, hm314⟩
    rw [he358, hm314]; subst v313
    refine ⟨ext1.trans ext2, blobs1 ++ blobs2,
      HashedPairs.append
        (hhp1.sub (by rw [hc359]; intro c hc; simp [hc]))
        (hhp2.sub (by rw [hc359]; intro c hc; simp [hc])),
      hlvls32, v48, v118, x_hint, ?_,
      hraw_ty.mono ext2 (fun _ hm => List.mem_append_left _ hm),
      hraw_val.mono (Heap.Extends.refl _) (fun _ hm => List.mem_append_right _ hm)⟩
    simp [defnValShape, hdk, he329]
  · -- Theorem
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv15
    rcases hv15 with ⟨_, _, hkind, hsaf, _, hlvls_eq, htyp_eq, hval_eq⟩
    subst x_safety x_lvls x_typ x_value
    have hdk : d.kind = .thm := by
      cases hk : d.kind <;> simp [repDefKindVal, hk] at hkind; rfl
    obtain ⟨ext1, blobs1, hhp1, hraw_ty⟩ :=
      convert_root_spec htyp hsh hrefs hrecs hunivs htbl ev61
    obtain ⟨ext2, blobs2, hhp2, hraw_val⟩ :=
      convert_root_spec (hval.mono ext1) (RepShareVec.mono ext1 hsh)
      (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrefs)
      (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrecs)
      (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext1 hunivs)
      (htbl.mono ext1) ev131
    obtain ⟨hlvls32, hv196, hm197⟩ := lvls_to_field_spec d.lvls.toNat_lt ev209
    rw [he395, hm197]; subst v196
    refine ⟨ext1.trans ext2, blobs1 ++ blobs2,
      HashedPairs.append
        (hhp1.sub (by rw [hc396]; intro c hc; simp [hc]))
        (hhp2.sub (by rw [hc396]; intro c hc; simp [hc])),
      hlvls32, v48, v118, x_hint, ?_,
      hraw_ty.mono ext2 (fun _ hm => List.mem_append_left _ hm),
      hraw_val.mono (Heap.Extends.refl _) (fun _ hm => List.mem_append_right _ hm)⟩
    simp [defnValShape, hdk, he373]

/-- `Convert::convert_axiom` specification. -/
theorem convert_axiom_spec {ax : Ixon.Axiom} {sharing : List Ixon.Expr}
    {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {x_a shPtr refsPtr recPtr univsPtr tbl r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hax : RepAxiom h ax x_a)
    (hsh : RepShareVec h sharing shPtr)
    (hrefs : RepList addressListEnum RepIxonAddressRef h refs refsPtr)
    (hrecs : RepList addressListEnum RepIxonAddressRef h recurAddrs recPtr)
    (hunivs : RepList univListEnum RepUnivPtr h univs univsPtr)
    (htbl : RepBinderTree 4294967296 h tbl)
    (ev : ObsFn W "Convert::convert_axiom"
      [x_a, shPtr, refsPtr, recPtr, univsPtr, tbl] h r h' calls) :
    Heap.Extends h h' ∧ ∃ blobs : List (_root_.Address × ByteArray),
      HashedPairs calls blobs ∧
      RawAxioValRep refs recurAddrs univs sharing blobs h' ax r := by
  obtain ⟨typPtr, rfl, htyp⟩ := hax
  obtain ⟨x_is_unsafe, x_lvls, x_typ, v32, m33, cs43, v104, m109, cs117,
      hv15, ev45, he107, ev119, he142, hc143⟩ :=
    «Convert::convert_axiom».obs ev
  simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv15
  rcases hv15 with ⟨_, _, hu_eq, hlvls_eq, htyp_eq⟩
  subst x_is_unsafe x_lvls x_typ
  obtain ⟨ext1, blobs, hhp, hraw_ty⟩ :=
    convert_root_spec htyp hsh hrefs hrecs hunivs htbl ev45
  obtain ⟨hlvls32, hv104, hm109⟩ := lvls_to_field_spec ax.lvls.toNat_lt ev119
  rw [he142, hm109]; subst v104
  exact ⟨ext1, blobs, hhp.sub (by rw [hc143]; intro c hc; simp [hc]),
    hlvls32, v32, he107, hraw_ty⟩

/-- `Convert::convert_quotient` specification. -/
theorem convert_quotient_spec {q : Ixon.Quotient} {sharing : List Ixon.Expr}
    {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {x_q shPtr refsPtr recPtr univsPtr tbl r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hq : RepQuotient h q x_q)
    (hsh : RepShareVec h sharing shPtr)
    (hrefs : RepList addressListEnum RepIxonAddressRef h refs refsPtr)
    (hrecs : RepList addressListEnum RepIxonAddressRef h recurAddrs recPtr)
    (hunivs : RepList univListEnum RepUnivPtr h univs univsPtr)
    (htbl : RepBinderTree 4294967296 h tbl)
    (ev : ObsFn W "Convert::convert_quotient"
      [x_q, shPtr, refsPtr, recPtr, univsPtr, tbl] h r h' calls) :
    Heap.Extends h h' ∧ ∃ blobs : List (_root_.Address × ByteArray),
      HashedPairs calls blobs ∧
      RawQuotValRep refs recurAddrs univs sharing blobs h' q r := by
  obtain ⟨typPtr, rfl, htyp⟩ := hq
  obtain ⟨x_kind, x_lvls, x_typ, v32, m33, cs43, v104, m109, cs117,
      hv15, ev45, he107, ev119, he142, hc143⟩ :=
    «Convert::convert_quotient».obs ev
  simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv15
  rcases hv15 with ⟨_, _, hk_eq, hlvls_eq, htyp_eq⟩
  subst x_kind x_lvls x_typ
  obtain ⟨ext1, blobs, hhp, hraw_ty⟩ :=
    convert_root_spec htyp hsh hrefs hrecs hunivs htbl ev45
  obtain ⟨hlvls32, hv104, hm109⟩ := lvls_to_field_spec q.lvls.toNat_lt ev119
  rw [he142, hm109]; subst v104
  exact ⟨ext1, blobs, hhp.sub (by rw [hc143]; intro c hc; simp [hc]),
    hlvls32, v32, he107, hraw_ty⟩

/-- `Convert::convert_inductive` specification under `Bounded calls` (used to bound
`ind.ctors.size < 2^39 < 2^56` via `RomBound.bounded_length_lt` on the `Convert::count_ctors`
subcall). -/
theorem convert_inductive_spec {ind : Ixon.Inductive} {blkAddr : _root_.Address} {indIdx : Nat}
    {sharing : List Ixon.Expr} {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {x_ind x_block_addr shPtr refsPtr recPtr univsPtr tbl x_base r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hbounded : IxVM.Consistency.Bounded calls)
    (hind : RepInductive h ind x_ind)
    (hblk : RepIxonAddressRef h blkAddr x_block_addr)
    (hindIdx : indIdx < 72057594037927936)
    (hsh : RepShareVec h sharing shPtr)
    (hrefs : RepList addressListEnum RepIxonAddressRef h refs refsPtr)
    (hrecs : RepList addressListEnum RepIxonAddressRef h recurAddrs recPtr)
    (hunivs : RepList univListEnum RepUnivPtr h univs univsPtr)
    (htbl : RepBinderTree 4294967296 h tbl)
    (ev : ObsFn W "Convert::convert_inductive"
      [x_ind, x_block_addr, .field (indIdx : F), shPtr, refsPtr, recPtr, univsPtr, tbl, x_base]
      h r h' calls) :
    Heap.Extends h h' ∧ ∃ blobs : List (_root_.Address × ByteArray),
      HashedPairs calls blobs ∧
      RawInductValRep refs recurAddrs univs sharing blobs h' ind blkAddr indIdx r := by
  obtain ⟨typPtr, ctorsPtr, rfl, htyp, hctors⟩ := hind
  obtain ⟨x_is_unsafe, x_lvls, x_params, x_indices, x_typ, x_ctors,
      v47, m48, cs58, v120, v122, v123, v124,
      m130, cs138, m157, cs165, m177, cs185, m197, cs205,
      hv15, ev60, he128, ev140, ev167, ev187, ev207, he237, hc238⟩ :=
    «Convert::convert_inductive».obs ev
  simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv15
  rcases hv15 with ⟨_, _, hu_eq, hlvls_eq, hp_eq, hi_eq, htyp_eq, hctors_eq⟩
  subst x_is_unsafe x_lvls x_params x_indices x_typ x_ctors
  obtain ⟨ext1, blobs, hhp, hraw_ty⟩ :=
    convert_root_spec htyp hsh hrefs hrecs hunivs htbl ev60
  obtain ⟨hlvls32, hv120, hm130⟩ := lvls_to_field_spec ind.lvls.toNat_lt ev140
  subst v120 m130
  obtain ⟨hp56, hv122, hm157⟩ :=
    Lib.u64_to_field_spec (Deserialize.repU64_u64Value m48 ind.params) ev167
  subst v122 m157
  obtain ⟨hi56, hv123, hm177⟩ :=
    Lib.u64_to_field_spec (Deserialize.repU64_u64Value m48 ind.indices) ev187
  subst v123
  have hctors_m177 : RepList constructorListEnum RepConstructor m177 ind.ctors.toList ctorsPtr := by
    rw [hm177]
    exact hctors.mono repConstructor_heapMono₂ ext1
  have hcall_mem : (⟨"Convert::count_ctors", [ctorsPtr], m177⟩ : Call F) ∈ calls := by
    rw [hc238]; simp
  have hct_len39 : ind.ctors.toList.length < 2 ^ 39 :=
    RomBound.bounded_length_lt hbounded hcall_mem (List.mem_singleton.mpr rfl) hctors_m177
  have hct_sz56 : ind.ctors.size < 72057594037927936 := by
    simp only [Array.length_toList] at hct_len39
    omega
  obtain ⟨hv124, hm197⟩ := count_ctors_spec hctors_m177 ev207
  rw [he237, hm197, hm177]; subst v124
  obtain ⟨b, hb_eq, hb_rep⟩ := repIxonAddressRef_to_core (hblk.mono ext1)
  refine ⟨ext1, blobs, hhp.sub (by rw [hc238]; intro c hc; simp [hc]),
    hlvls32, hp56, hi56, hct_sz56, hindIdx, v47, x_block_addr, b, hb_eq, hb_rep, ?_, hraw_ty⟩
  simp only [Array.length_toList] at he128
  exact he128

/-- `Convert::convert_constructor` specification. -/
theorem convert_constructor_spec {ct : Ixon.Constructor} {blkAddr : _root_.Address} {indIdx : Nat}
    {sharing : List Ixon.Expr} {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {x_c x_block_addr shPtr refsPtr recPtr univsPtr tbl x_base r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hct : RepConstructor h ct x_c)
    (hblk : RepIxonAddressRef h blkAddr x_block_addr)
    (hindIdx : indIdx < 72057594037927936)
    (hsh : RepShareVec h sharing shPtr)
    (hrefs : RepList addressListEnum RepIxonAddressRef h refs refsPtr)
    (hrecs : RepList addressListEnum RepIxonAddressRef h recurAddrs recPtr)
    (hunivs : RepList univListEnum RepUnivPtr h univs univsPtr)
    (htbl : RepBinderTree 4294967296 h tbl)
    (ev : ObsFn W "Convert::convert_constructor"
      [x_c, x_block_addr, .field (indIdx : F), shPtr, refsPtr, recPtr, univsPtr, tbl, x_base]
      h r h' calls) :
    Heap.Extends h h' ∧ ∃ blobs : List (_root_.Address × ByteArray),
      HashedPairs calls blobs ∧
      RawCtorValRep refs recurAddrs univs sharing blobs h' ct blkAddr indIdx r := by
  obtain ⟨modesPtr, typPtr, rfl, _, htyp⟩ := hct
  obtain ⟨x_is_unsafe, x_lvls, x_cidx, x_params, x_fields, w17, x_typ,
      v53, m54, cs64, v126, v130, v131, v132,
      m136, cs144, m177, cs185, m197, cs205, m217, cs225,
      hv15, ev66, he134, ev146, ev187, ev207, ev227, he243, hc244⟩ :=
    «Convert::convert_constructor».obs ev
  simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv15
  rcases hv15 with ⟨_, _, hu_eq, hlvls_eq, hcidx_eq, hp_eq, hf_eq, _, htyp_eq⟩
  subst x_is_unsafe x_lvls x_cidx x_params x_fields x_typ
  obtain ⟨ext1, blobs, hhp, hraw_ty⟩ :=
    convert_root_spec htyp hsh hrefs hrecs hunivs htbl ev66
  obtain ⟨hlvls32, hv126, hm136⟩ := lvls_to_field_spec ct.lvls.toNat_lt ev146
  subst v126 m136
  obtain ⟨hcidx56, hv130, hm177⟩ :=
    Lib.u64_to_field_spec (Deserialize.repU64_u64Value m54 ct.cidx) ev187
  subst v130 m177
  obtain ⟨hp56, hv131, hm197⟩ :=
    Lib.u64_to_field_spec (Deserialize.repU64_u64Value m54 ct.params) ev207
  subst v131 m197
  obtain ⟨hf56, hv132, hm217⟩ :=
    Lib.u64_to_field_spec (Deserialize.repU64_u64Value m54 ct.fields) ev227
  rw [he243, hm217]; subst v132
  obtain ⟨b, hb_eq, hb_rep⟩ := repIxonAddressRef_to_core (hblk.mono ext1)
  exact ⟨ext1, blobs, hhp.sub (by rw [hc244]; intro c hc; simp [hc]),
    hlvls32, hcidx56, hp56, hf56, hindIdx, v53, x_block_addr, b, hb_eq, hb_rep, he134, hraw_ty⟩

/-- `Convert::convert_rec_rules` specification. -/
theorem convert_rec_rules_spec {rus : List Ixon.RecursorRule} :
    ∀ {j : Nat} {sharing : List Ixon.Expr}
      {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
      {x_rs shPtr refsPtr recPtr univsPtr tbl x_ridx r : SourceValue F}
      {h h' : Heap F} {calls : List (Call F)},
      RepList recursorRuleListEnum RepRecursorRule h rus x_rs →
      RepShareVec h sharing shPtr →
      RepList addressListEnum RepIxonAddressRef h refs refsPtr →
      RepList addressListEnum RepIxonAddressRef h recurAddrs recPtr →
      RepList univListEnum RepUnivPtr h univs univsPtr →
      RepBinderTree 4294967296 h tbl →
      ObsFn W "Convert::convert_rec_rules"
        [x_rs, shPtr, refsPtr, recPtr, univsPtr, .field (j : F), tbl, x_ridx] h r h' calls →
      Heap.Extends h h' ∧ ∃ blobs : List (_root_.Address × ByteArray),
        HashedPairs calls blobs ∧
        RawRulesRep refs recurAddrs univs sharing blobs h' j rus r := by
  induction rus with
  | nil =>
    intro j sharing refs recurAddrs univs x_rs shPtr refsPtr recPtr univsPtr tbl x_ridx r h h' calls
      hrus _ _ _ _ _ ev
    rcases «Convert::convert_rec_rules».obs ev with
      ⟨_, he24, hm23, _⟩ |
      ⟨x_rest, x_fields, x_rhs, _, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _, _, _, _⟩
    · subst r h'
      exact ⟨Heap.Extends.snoc h _, [], HashedPairs.nil, .nil (by simp)⟩
    · obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hrus ld12
      cases he
  | cons ru rest ih =>
    intro j sharing refs recurAddrs univs x_rs shPtr refsPtr recPtr univsPtr tbl x_ridx r h h' calls
      hrus hsh hrefs hrecs hunivs htbl ev
    rcases «Convert::convert_rec_rules».obs ev with
      ⟨ld12, _, _, _⟩ |
      ⟨x_rest, x_fields, x_rhs, v72, m73, cs83, v151, v162, m172, cs180, m199, cs207,
        v215, v217, ld12, ev85, he146, hm145, ev182, op266, op288, ev209, hc290⟩
    · have he := Lib.rep_nil_of_load hrus ld12
      cases he
    · obtain ⟨ru', rest', he, hru, hrest⟩ := Lib.rep_cons_of_load hrus ld12
      injection he with h1 h2; subst ru' rest'
      obtain ⟨rhsPtr, hru_eq, hrhs⟩ := hru
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hru_eq
      rcases hru_eq with ⟨_, _, hf_eq, hrhs_eq⟩
      subst x_fields x_rhs
      obtain ⟨ext1, blobs1, hhp1, hraw_rhs⟩ :=
        convert_root_spec hrhs hsh hrefs hrecs hunivs htbl ev85
      obtain ⟨hf56, hv162, hm172⟩ :=
        Lib.u64_to_field_spec (Deserialize.repU64_u64Value m73 ru.fields) ev182
      subst v162 m172
      simp only [evalBinOp, Except.ok.injEq] at op266
      have hv215 : v215 = .field (((j + 1 : Nat) : F)) := by
        rw [← op266]; push_cast; rfl
      rw [hv215] at ev209
      obtain ⟨ext2, blobs2, hhp2, hraw_rest⟩ :=
        ih (hrest.mono repRecursorRule_heapMono₂ ext1)
          (RepShareVec.mono ext1 hsh)
          (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrefs)
          (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrecs)
          (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext1 hunivs)
          (htbl.mono ext1) ev209
      subst r h'
      have ext_fin := Heap.Extends.snoc m199
        (.construct Core.krrListEnum "Cons"
          [.construct Core.krrEnum "Mk" [.field (j : F), .field (ru.fields.toNat : F), v72], v151])
      refine ⟨(ext1.trans ext2).trans ext_fin, blobs1 ++ blobs2,
        HashedPairs.append
          (hhp1.sub (by rw [hc290]; intro c hc; simp [hc]))
          (hhp2.sub (by rw [hc290]; intro c hc; simp [hc])),
        .cons (by simp)
          ⟨hf56, v72, rfl,
            hraw_rhs.mono (ext2.trans ext_fin) (fun _ hm => List.mem_append_left _ hm)⟩
          (hraw_rest.mono ext_fin (fun _ hm => List.mem_append_right _ hm))⟩

/-- `Convert::convert_recursor` specification. -/
theorem convert_recursor_spec {rc : Ixon.Recursor} {blkAddr : _root_.Address} {recIdx : Nat}
    {sharing : List Ixon.Expr} {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {x_r x_block_addr shPtr refsPtr recPtr univsPtr tbl x_base r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hrc : RepRecursor h rc x_r)
    (hblk : RepIxonAddressRef h blkAddr x_block_addr)
    (hrecIdx : recIdx < 72057594037927936)
    (hsh : RepShareVec h sharing shPtr)
    (hrefs : RepList addressListEnum RepIxonAddressRef h refs refsPtr)
    (hrecs : RepList addressListEnum RepIxonAddressRef h recurAddrs recPtr)
    (hunivs : RepList univListEnum RepUnivPtr h univs univsPtr)
    (htbl : RepBinderTree 4294967296 h tbl)
    (ev : ObsFn W "Convert::convert_recursor"
      [x_r, x_block_addr, .field (recIdx : F), shPtr, refsPtr, recPtr, univsPtr, tbl, x_base]
      h r h' calls) :
    Heap.Extends h h' ∧ ∃ blobs : List (_root_.Address × ByteArray),
      HashedPairs calls blobs ∧
      RawRecrValRep refs recurAddrs univs sharing blobs h' rc blkAddr recIdx r := by
  obtain ⟨typPtr, rulesPtr, rfl, htyp, hrules⟩ := hrc
  obtain ⟨x_k, x_is_unsafe, x_lvls, x_params, x_indices, x_motives, x_minors, x_typ, x_rules,
      v62, m63, cs73, m105, v138, m139, cs149, v159,
      v226, v228, v229, v230, v231,
      m239, cs247, m266, cs274, m286, cs294, m306, cs314, m326, cs334,
      hv15, hm113, ev75, op221, ev151, he237,
      ev249, ev276, ev296, ev316, ev336, he380, hc381⟩ :=
    «Convert::convert_recursor».obs ev
  simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv15
  rcases hv15 with ⟨_, _, hk_eq, hu_eq, hlvls_eq, hp_eq, hi_eq, hm_eq, hmi_eq, htyp_eq, hrules_eq⟩
  subst x_k x_is_unsafe x_lvls x_params x_indices x_motives x_minors x_typ x_rules
  have ext0 : Heap.Extends h m105 := by
    rw [hm113]; exact Heap.Extends.snoc h _
  have hm105' : m105 = h ++ [.construct addressListEnum "Nil" []] := by
    rw [addressListEnum_eq]; exact hm113
  have hnil_rec : RepList addressListEnum RepIxonAddressRef m105 []
      (.ptr (.enum Names.«Lists::Node<&[Field; 32]>») h.length) := by
    rw [hm105', ← addressListEnum_eq]
    exact Lib.rep_store_nil h
  obtain ⟨ext1, blobs1, hhp1, hraw_ty⟩ :=
    convert_root_spec (htyp.mono ext0) (RepShareVec.mono ext0 hsh)
      (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext0 hrefs)
      hnil_rec
      (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext0 hunivs)
      (htbl.mono ext0) ev75
  have ext01 := ext0.trans ext1
  obtain ⟨ext2, blobs2, hhp2, hraw_rules⟩ :=
    convert_rec_rules_spec
      (hrules.mono repRecursorRule_heapMono₂ ext01)
      (RepShareVec.mono ext01 hsh)
      (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext01 hrefs)
      (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext01 hrecs)
      (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext01 hunivs)
      (htbl.mono ext01) ev151
  obtain ⟨hlvls32, hv226, hm239⟩ := lvls_to_field_spec rc.lvls.toNat_lt ev249
  subst v226 m239
  obtain ⟨hp56, hv228, hm266⟩ :=
    Lib.u64_to_field_spec (Deserialize.repU64_u64Value m139 rc.params) ev276
  subst v228 m266
  obtain ⟨hi56, hv229, hm286⟩ :=
    Lib.u64_to_field_spec (Deserialize.repU64_u64Value m139 rc.indices) ev296
  subst v229 m286
  obtain ⟨hm56, hv230, hm306⟩ :=
    Lib.u64_to_field_spec (Deserialize.repU64_u64Value m139 rc.motives) ev316
  subst v230 m306
  obtain ⟨hmi56, hv231, hm326⟩ :=
    Lib.u64_to_field_spec (Deserialize.repU64_u64Value m139 rc.minors) ev336
  rw [he380, hm326]; subst v231
  have ext_all := ext01.trans ext2
  obtain ⟨b, hb_eq, hb_rep⟩ := repIxonAddressRef_to_core (hblk.mono ext_all)
  exact ⟨ext_all, blobs1 ++ blobs2,
    HashedPairs.append
      (hhp1.sub (by rw [hc381]; intro c hc; simp [hc]))
      (hhp2.sub (by rw [hc381]; intro c hc; simp [hc])),
    hlvls32, hp56, hi56, hm56, hmi56, hrecIdx, v62, v138, x_block_addr, b, hb_eq, hb_rep, he237,
    hraw_ty.mono ext2 (fun _ hm => List.mem_append_left _ hm),
    hraw_rules.mono (Heap.Extends.refl _) (fun _ hm => List.mem_append_right _ hm)⟩

/-! ## Bridges from `Raw*ValRep` to `StoredAs` and `Core.CIRep` -/

/-- Helper constructing `Core.ValRep` and `ValStored` from a converted root type expression. -/
theorem rawConvExpr_to_valRep {κ : _root_.Address → Core.KKey}
    {name : Core.KKey} {ps : List Ix.Kernel.LevelParam} {nl : Nat}
    (hnl : ps.length = nl) (hperm : ps.Perm (List.range ps.length)) (hlt32 : nl < 4294967296)
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    (hkeyAt : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (hself : ∀ i a m k, recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (hblob : ∀ a bs, (a, bs) ∈ blobs → cx.blob a = some bs)
    {h : Heap F} {tyExpr : Ixon.Expr} {tyPtr : SourceValue F} {ty₀ : Core.KExpr}
    (raw : RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h 4294967295 tyExpr tyPtr)
    (hread : (Ix.Kernel.Reader.MemberReader.mk' cx src (Ix.Kernel.Reader.recParam ps) self).read
      tyExpr = .ok ty₀)
    (hlbb : ty₀.looseBVarsBounded 0 = true)
    (hdef : ty₀.allLevelParamsDefined ps = true) :
    ∃ ty' : Core.KExpr,
      IxVM.Consistency.ValStored ⟨name, ps, ty'⟩ ⟨name, ps, ty₀⟩ ∧
      Core.ValRep κ h (.field (nl : F)) tyPtr ⟨name, ps, ty'⟩ := by
  have hps_lt : ps.length < 4294967296 := by omega
  obtain ⟨ty', hA, hTm⟩ := raw.toTmC hperm hps_lt hkeyAt hself hblob hread hlbb hdef
  refine ⟨ty', ⟨rfl, rfl, hA⟩, ?_⟩
  refine ⟨?_, hps_lt, hperm, hTm⟩
  exact congrArg (fun n : Nat => Value.field (n : F)) hnl.symm

/-- Bridge from `RawDefnValRep` on `.defn` to `StoredAs` and `Core.CIRep`. -/
theorem RawDefnValRep.toCIRep_defn {κ : _root_.Address → Core.KKey}
    {name : Core.KKey} {ps : List Ix.Kernel.LevelParam} {d : Ixon.Definition}
    (hkind : d.kind = .defn)
    (hnl : ps.length = d.lvls.toNat) (hperm : ps.Perm (List.range ps.length))
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    (hkeyAt : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (hself : ∀ i a m k, recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (hblob : ∀ a bs, (a, bs) ∈ blobs → cx.blob a = some bs)
    {h : Heap F} {v : SourceValue F} {ty₀ val₀ : Core.KExpr}
    (hn : Ix.Kernel.ReducibilityHint)
    (raw : RawDefnValRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h d v)
    (hty_rd : (Ix.Kernel.Reader.MemberReader.mk' cx src (Ix.Kernel.Reader.recParam ps) self).read
      d.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true) (hty_def : ty₀.allLevelParamsDefined ps = true)
    (hval_rd : (Ix.Kernel.Reader.MemberReader.mk' cx src (Ix.Kernel.Reader.recParam ps) self).read
      d.value = .ok val₀)
    (hval_lbb : val₀.looseBVarsBounded 0 = true) (hval_def : val₀.allLevelParamsDefined ps = true) :
    ∃ ci : Ix.Kernel.ConstantInfo .anon,
      IxVM.Consistency.StoredAs ci (.defnInfo ⟨name, ps, ty₀⟩ val₀ hn) ∧
      Core.CIRep κ h v ci := by
  obtain ⟨hlvls, tyPtr, valPtr, hint, rfl, hty_raw, hval_raw⟩ := raw
  have hps_lt : ps.length < 4294967296 := by omega
  obtain ⟨ty', hvs, hvr⟩ :=
    rawConvExpr_to_valRep hnl hperm hlvls hkeyAt hself hblob hty_raw hty_rd hty_lbb hty_def
  obtain ⟨val', hAval, hTm_val⟩ :=
    hval_raw.toTmC hperm hps_lt hkeyAt hself hblob hval_rd hval_lbb hval_def
  refine ⟨.defnInfo ⟨name, ps, ty'⟩ val' hn, ⟨hvs, hAval, rfl⟩, ?_⟩
  simp only [defnValShape, hkind]
  exact .defn hvr hTm_val

/-- Bridge from `RawDefnValRep` on `.opaq` to `StoredAs` (against `.axiomInfo`) and `Core.CIRep`. -/
theorem RawDefnValRep.toCIRep_opaq {κ : _root_.Address → Core.KKey}
    {name : Core.KKey} {ps : List Ix.Kernel.LevelParam} {d : Ixon.Definition}
    (hkind : d.kind = .opaq)
    (hnl : ps.length = d.lvls.toNat) (hperm : ps.Perm (List.range ps.length))
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    (hkeyAt : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (hself : ∀ i a m k, recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (hblob : ∀ a bs, (a, bs) ∈ blobs → cx.blob a = some bs)
    {h : Heap F} {v : SourceValue F} {ty₀ : Core.KExpr}
    (raw : RawDefnValRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h d v)
    (hty_rd : (Ix.Kernel.Reader.MemberReader.mk' cx src (Ix.Kernel.Reader.recParam ps) self).read
      d.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true) (hty_def : ty₀.allLevelParamsDefined ps = true) :
    ∃ ci : Ix.Kernel.ConstantInfo .anon,
      IxVM.Consistency.StoredAs ci (.axiomInfo ⟨name, ps, ty₀⟩) ∧
      Core.CIRep κ h v ci := by
  obtain ⟨hlvls, tyPtr, valPtr, hint, rfl, hty_raw, _⟩ := raw
  obtain ⟨ty', hvs, hvr⟩ :=
    rawConvExpr_to_valRep hnl hperm hlvls hkeyAt hself hblob hty_raw hty_rd hty_lbb hty_def
  refine ⟨.axiomInfo ⟨name, ps, ty'⟩, ⟨hvs, trivial⟩, ?_⟩
  simp only [defnValShape, hkind]
  exact .opaq hvr

/-- Bridge from `RawDefnValRep` on `.thm` to `StoredAs` and `Core.CIRep`. -/
theorem RawDefnValRep.toCIRep_thm {κ : _root_.Address → Core.KKey}
    {name : Core.KKey} {ps : List Ix.Kernel.LevelParam} {d : Ixon.Definition}
    (hkind : d.kind = .thm)
    (hnl : ps.length = d.lvls.toNat) (hperm : ps.Perm (List.range ps.length))
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    (hkeyAt : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (hself : ∀ i a m k, recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (hblob : ∀ a bs, (a, bs) ∈ blobs → cx.blob a = some bs)
    {h : Heap F} {v : SourceValue F} {ty₀ val₀ : Core.KExpr}
    (raw : RawDefnValRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h d v)
    (hty_rd : (Ix.Kernel.Reader.MemberReader.mk' cx src (Ix.Kernel.Reader.recParam ps) self).read
      d.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true) (hty_def : ty₀.allLevelParamsDefined ps = true)
    (hval_rd : (Ix.Kernel.Reader.MemberReader.mk' cx src (Ix.Kernel.Reader.recParam ps) self).read
      d.value = .ok val₀)
    (hval_lbb : val₀.looseBVarsBounded 0 = true) (hval_def : val₀.allLevelParamsDefined ps = true) :
    ∃ ci : Ix.Kernel.ConstantInfo .anon,
      IxVM.Consistency.StoredAs ci (.thmInfo ⟨name, ps, ty₀⟩ val₀) ∧
      Core.CIRep κ h v ci := by
  obtain ⟨hlvls, tyPtr, valPtr, hint, rfl, hty_raw, hval_raw⟩ := raw
  have hps_lt : ps.length < 4294967296 := by omega
  obtain ⟨ty', hvs, hvr⟩ :=
    rawConvExpr_to_valRep hnl hperm hlvls hkeyAt hself hblob hty_raw hty_rd hty_lbb hty_def
  obtain ⟨val', hAval, hTm_val⟩ :=
    hval_raw.toTmC hperm hps_lt hkeyAt hself hblob hval_rd hval_lbb hval_def
  refine ⟨.thmInfo ⟨name, ps, ty'⟩ val', ⟨hvs, hAval⟩, ?_⟩
  simp only [defnValShape, hkind]
  exact .thm hvr hTm_val

/-- Unified `RawDefnValRep.toCIRep` across all three `Ix.DefKind` cases. -/
theorem RawDefnValRep.toCIRep {κ : _root_.Address → Core.KKey}
    {name : Core.KKey} {ps : List Ix.Kernel.LevelParam} {d : Ixon.Definition}
    (hnl : ps.length = d.lvls.toNat) (hperm : ps.Perm (List.range ps.length))
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    (hkeyAt : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (hself : ∀ i a m k, recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (hblob : ∀ a bs, (a, bs) ∈ blobs → cx.blob a = some bs)
    {h : Heap F} {v : SourceValue F} {ty₀ val₀ : Core.KExpr}
    (hn : Ix.Kernel.ReducibilityHint)
    (raw : RawDefnValRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h d v)
    (hty_rd : (Ix.Kernel.Reader.MemberReader.mk' cx src (Ix.Kernel.Reader.recParam ps) self).read
      d.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true) (hty_def : ty₀.allLevelParamsDefined ps = true)
    (hval_rd : (Ix.Kernel.Reader.MemberReader.mk' cx src (Ix.Kernel.Reader.recParam ps) self).read
      d.value = .ok val₀)
    (hval_lbb : val₀.looseBVarsBounded 0 = true) (hval_def : val₀.allLevelParamsDefined ps = true) :
    ∃ ci : Ix.Kernel.ConstantInfo .anon,
      IxVM.Consistency.StoredAs ci
        (match d.kind with
         | .defn => .defnInfo ⟨name, ps, ty₀⟩ val₀ hn
         | .opaq => .axiomInfo ⟨name, ps, ty₀⟩
         | .thm => .thmInfo ⟨name, ps, ty₀⟩ val₀) ∧
      Core.CIRep κ h v ci := by
  cases hk : d.kind with
  | defn =>
    exact raw.toCIRep_defn hk hnl hperm hkeyAt hself hblob hn hty_rd hty_lbb hty_def
      hval_rd hval_lbb hval_def
  | opaq =>
    exact raw.toCIRep_opaq hk hnl hperm hkeyAt hself hblob hty_rd hty_lbb hty_def
  | thm =>
    exact raw.toCIRep_thm hk hnl hperm hkeyAt hself hblob hty_rd hty_lbb hty_def
      hval_rd hval_lbb hval_def

/-- Bridge from `RawAxioValRep` to `StoredAs` and `Core.CIRep`. -/
theorem RawAxioValRep.toCIRep {κ : _root_.Address → Core.KKey}
    {name : Core.KKey} {ps : List Ix.Kernel.LevelParam} {ax : Ixon.Axiom}
    (hnl : ps.length = ax.lvls.toNat) (hperm : ps.Perm (List.range ps.length))
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    (hkeyAt : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (hself : ∀ i a m k, recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (hblob : ∀ a bs, (a, bs) ∈ blobs → cx.blob a = some bs)
    {h : Heap F} {v : SourceValue F} {ty₀ : Core.KExpr}
    (raw : RawAxioValRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h ax v)
    (hty_rd : (Ix.Kernel.Reader.MemberReader.mk' cx src (Ix.Kernel.Reader.recParam ps) self).read
      ax.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true) (hty_def : ty₀.allLevelParamsDefined ps = true) :
    ∃ ci : Ix.Kernel.ConstantInfo .anon,
      IxVM.Consistency.StoredAs ci (.axiomInfo ⟨name, ps, ty₀⟩) ∧
      Core.CIRep κ h v ci := by
  obtain ⟨hlvls, tyPtr, rfl, hty_raw⟩ := raw
  obtain ⟨ty', hvs, hvr⟩ :=
    rawConvExpr_to_valRep hnl hperm hlvls hkeyAt hself hblob hty_raw hty_rd hty_lbb hty_def
  exact ⟨.axiomInfo ⟨name, ps, ty'⟩, ⟨hvs, trivial⟩, .axio hvr⟩

private def defaultQuotCI (k : Ix.QuotKind) (cv : Ix.Kernel.ConstantVal .anon) :
    Ix.Kernel.ConstantInfo .anon :=
  match k with
  | .type => .indInfo cv {}
  | .ctor => .ctorInfo cv 0 0
  | .lift => .recInfo cv 0 0 []
  | .ind => .recInfo cv 0 0 []

/-- Bridge from `RawQuotValRep` to `Core.CIRep` (using the canonical shape per `QuotKind`). -/
theorem RawQuotValRep.toCIRep {κ : _root_.Address → Core.KKey}
    {name : Core.KKey} {ps : List Ix.Kernel.LevelParam} {q : Ixon.Quotient}
    (hnl : ps.length = q.lvls.toNat) (hperm : ps.Perm (List.range ps.length))
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    (hkeyAt : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (hself : ∀ i a m k, recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (hblob : ∀ a bs, (a, bs) ∈ blobs → cx.blob a = some bs)
    {h : Heap F} {v : SourceValue F} {ty₀ : Core.KExpr}
    (raw : RawQuotValRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h q v)
    (hty_rd : (Ix.Kernel.Reader.MemberReader.mk' cx src (Ix.Kernel.Reader.recParam ps) self).read
      q.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true) (hty_def : ty₀.allLevelParamsDefined ps = true) :
    ∃ ci : Ix.Kernel.ConstantInfo .anon,
      IxVM.Consistency.StoredAs ci (defaultQuotCI q.kind ⟨name, ps, ty₀⟩) ∧
      Core.CIRep κ h v ci := by
  obtain ⟨hlvls, tyPtr, rfl, hty_raw⟩ := raw
  obtain ⟨ty', hvs, hvr⟩ :=
    rawConvExpr_to_valRep hnl hperm hlvls hkeyAt hself hblob hty_raw hty_rd hty_lbb hty_def
  cases hk : q.kind
  · refine ⟨.indInfo ⟨name, ps, ty'⟩ {}, ⟨hvs, trivial⟩,
      .quot hvr (.inl ⟨by simp [repQuotKindVal], _, _, rfl⟩)⟩
  · refine ⟨.ctorInfo ⟨name, ps, ty'⟩ 0 0, ⟨hvs, rfl, rfl⟩,
      .quot hvr (.inr (.inl ⟨by simp [repQuotKindVal], _, _, _, rfl⟩))⟩
  · refine ⟨.recInfo ⟨name, ps, ty'⟩ 0 0 [], ⟨hvs, rfl, rfl, .nil⟩,
      .quot hvr (.inr (.inr (.inl ⟨by simp [repQuotKindVal], _, _, _, _, rfl⟩)))⟩
  · refine ⟨.recInfo ⟨name, ps, ty'⟩ 0 0 [], ⟨hvs, rfl, rfl, .nil⟩,
      .quot hvr (.inr (.inr (.inr ⟨by simp [repQuotKindVal], _, _, _, _, rfl⟩)))⟩

/-- Bridge from `RawQuotValRep` against a given pinned quotient `ConstantInfo` `ci₀`. -/
theorem RawQuotValRep.toCIRep_stored {κ : _root_.Address → Core.KKey}
    {q : Ixon.Quotient} {ci₀ : Ix.Kernel.ConstantInfo .anon}
    (hkind : Core.QuotKindRep (repQuotKindVal q.kind) ci₀)
    (hnl : ci₀.toConstantVal.levelParams.length = q.lvls.toNat)
    (hperm : ci₀.toConstantVal.levelParams.Perm (List.range ci₀.toConstantVal.levelParams.length))
    (hrls_ann : ∀ mI rP rls, ci₀ = .recInfo ci₀.toConstantVal mI rP rls →
      List.Forall₂ IxVM.Consistency.RuleStored rls rls)
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    (hkeyAt : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (hself : ∀ i a m k, recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (hblob : ∀ a bs, (a, bs) ∈ blobs → cx.blob a = some bs)
    {h : Heap F} {v : SourceValue F}
    (raw : RawQuotValRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h q v)
    (hty_rd : (Ix.Kernel.Reader.MemberReader.mk' cx src
      (Ix.Kernel.Reader.recParam ci₀.toConstantVal.levelParams) self).read q.typ =
        .ok ci₀.toConstantVal.type)
    (hty_lbb : ci₀.toConstantVal.type.looseBVarsBounded 0 = true)
    (hty_def : ci₀.toConstantVal.type.allLevelParamsDefined ci₀.toConstantVal.levelParams = true) :
    ∃ ci : Ix.Kernel.ConstantInfo .anon,
      IxVM.Consistency.StoredAs ci ci₀ ∧
      Core.CIRep κ h v ci := by
  obtain ⟨hlvls, tyPtr, rfl, hty_raw⟩ := raw
  obtain ⟨ty', hvs, hvr⟩ :=
    rawConvExpr_to_valRep (name := ci₀.toConstantVal.name) hnl hperm hlvls hkeyAt hself hblob hty_raw
      hty_rd hty_lbb hty_def
  rcases hkind with
    ⟨hk_eq, cv, caps, rfl⟩ | ⟨hk_eq, cv, nP, nF, rfl⟩ |
    ⟨hk_eq, cv, mI, rP, rs, rfl⟩ | ⟨hk_eq, cv, mI, rP, rs, rfl⟩
  · exact ⟨.indInfo ⟨cv.name, cv.levelParams, ty'⟩ caps, ⟨hvs, trivial⟩,
      .quot hvr (.inl ⟨hk_eq, _, _, rfl⟩)⟩
  · exact ⟨.ctorInfo ⟨cv.name, cv.levelParams, ty'⟩ nP nF, ⟨hvs, rfl, rfl⟩,
      .quot hvr (.inr (.inl ⟨hk_eq, _, _, _, rfl⟩))⟩
  · exact ⟨.recInfo ⟨cv.name, cv.levelParams, ty'⟩ mI rP rs,
      ⟨hvs, rfl, rfl, hrls_ann mI rP rs rfl⟩,
      .quot hvr (.inr (.inr (.inl ⟨hk_eq, _, _, _, _, rfl⟩)))⟩
  · exact ⟨.recInfo ⟨cv.name, cv.levelParams, ty'⟩ mI rP rs,
      ⟨hvs, rfl, rfl, hrls_ann mI rP rs rfl⟩,
      .quot hvr (.inr (.inr (.inr ⟨hk_eq, _, _, _, _, rfl⟩)))⟩

/-- Bridge from `RawInductValRep` to `StoredAs` and `Core.CIRep`. -/
theorem RawInductValRep.toCIRep {κ : _root_.Address → Core.KKey}
    {name : Core.KKey} {ps : List Ix.Kernel.LevelParam}
    {ind : Ixon.Inductive} {blkAddr : _root_.Address} {indIdx : Nat}
    (hname : name = κ (Core.iprjAddr blkAddr indIdx))
    (hnl : ps.length = ind.lvls.toNat) (hperm : ps.Perm (List.range ps.length))
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    (hkeyAt : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (hself : ∀ i a m k, recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (hblob : ∀ a bs, (a, bs) ∈ blobs → cx.blob a = some bs)
    {h : Heap F} {v : SourceValue F} {ty₀ : Core.KExpr}
    (caps : Ix.Kernel.IndCaps .anon)
    (raw : RawInductValRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h ind blkAddr indIdx v)
    (hty_rd : (Ix.Kernel.Reader.MemberReader.mk' cx src (Ix.Kernel.Reader.recParam ps) self).read
      ind.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true) (hty_def : ty₀.allLevelParamsDefined ps = true) :
    ∃ ci : Ix.Kernel.ConstantInfo .anon,
      IxVM.Consistency.StoredAs ci (.indInfo ⟨name, ps, ty₀⟩ caps) ∧
      Core.CIRep κ h v ci := by
  obtain ⟨hlvls, hp56, hi56, hc56, hidx56, tyPtr, blkPtr, b, hb_eq, hb_rep, rfl, hty_raw⟩ := raw
  obtain ⟨ty', hvs, hvr⟩ :=
    rawConvExpr_to_valRep hnl hperm hlvls hkeyAt hself hblob hty_raw hty_rd hty_lbb hty_def
  refine ⟨.indInfo ⟨name, ps, ty'⟩ caps, ⟨hvs, trivial⟩,
    .induct hvr ⟨ind.params.toNat, ind.indices.toNat, ind.ctors.size, rfl, rfl, rfl, hp56, hi56, hc56⟩
      ⟨b, (indIdx : F), hb_rep, rfl, ?_⟩⟩
  rw [hb_eq, val_cast_u56_conv hidx56]
  exact hname

/-- Bridge from `RawCtorValRep` to `StoredAs` and `Core.CIRep`. -/
theorem RawCtorValRep.toCIRep {κ : _root_.Address → Core.KKey}
    {name : Core.KKey} {ps : List Ix.Kernel.LevelParam}
    {ct : Ixon.Constructor} {blkAddr : _root_.Address} {indIdx : Nat}
    (hname : name = κ (Core.cprjAddr blkAddr indIdx ct.cidx.toNat))
    (hnl : ps.length = ct.lvls.toNat) (hperm : ps.Perm (List.range ps.length))
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    (hkeyAt : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (hself : ∀ i a m k, recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (hblob : ∀ a bs, (a, bs) ∈ blobs → cx.blob a = some bs)
    {h : Heap F} {v : SourceValue F} {ty₀ : Core.KExpr}
    (raw : RawCtorValRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h ct blkAddr indIdx v)
    (hty_rd : (Ix.Kernel.Reader.MemberReader.mk' cx src (Ix.Kernel.Reader.recParam ps) self).read
      ct.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true) (hty_def : ty₀.allLevelParamsDefined ps = true) :
    ∃ ci : Ix.Kernel.ConstantInfo .anon,
      IxVM.Consistency.StoredAs ci (.ctorInfo ⟨name, ps, ty₀⟩ ct.params.toNat ct.fields.toNat) ∧
      Core.CIRep κ h v ci := by
  obtain ⟨hlvls, hcidx56, hp56, hf56, hidx56, tyPtr, blkPtr, b, hb_eq, hb_rep, rfl, hty_raw⟩ := raw
  obtain ⟨ty', hvs, hvr⟩ :=
    rawConvExpr_to_valRep hnl hperm hlvls hkeyAt hself hblob hty_raw hty_rd hty_lbb hty_def
  refine ⟨.ctorInfo ⟨name, ps, ty'⟩ ct.params.toNat ct.fields.toNat, ⟨hvs, rfl, rfl⟩,
    .ctor hvr rfl rfl ⟨hp56, hf56⟩ ⟨b, (indIdx : F), (ct.cidx.toNat : F), hb_rep, rfl, rfl, ?_⟩⟩
  rw [hb_eq, val_cast_u56_conv hidx56, val_cast_u56_conv hcidx56]
  exact hname

/-- Bridge from `RawRulesRep` and a one-for-one list of read `RecRule`s to `RuleStored` and
`Core.RulesRep`. -/
theorem RawRulesRep.toRulesRep {κ : _root_.Address → Core.KKey}
    {ps : List Ix.Kernel.LevelParam}
    (hperm : ps.Perm (List.range ps.length)) (hps_lt : ps.length < 4294967296)
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    (hkeyAt : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (hself : ∀ i a m k, recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (hblob : ∀ a bs, (a, bs) ∈ blobs → cx.blob a = some bs)
    (kFlag : Bool) (cParams : Nat)
    {h : Heap F} {j : Nat} {rus : List Ixon.RecursorRule} {rulesPtr : SourceValue F}
    (raw : RawRulesRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h j rus rulesPtr) :
    ∀ {rules₀ : List (Ix.Kernel.RecRule .anon)},
      List.Forall₂ (fun ru rl₀ =>
        rl₀.nfields = ru.fields.toNat ∧
        (Ix.Kernel.Reader.MemberReader.mk' cx src (Ix.Kernel.Reader.recParam ps) self).read ru.rhs =
          .ok rl₀.rhs ∧
        rl₀.rhs.looseBVarsBounded 0 = true ∧
        rl₀.rhs.allLevelParamsDefined ps = true) rus rules₀ →
      ∃ rls : List (Ix.Kernel.RecRule .anon),
        List.Forall₂ IxVM.Consistency.RuleStored rls rules₀ ∧
        Core.RulesRep κ h ps j rulesPtr rls ∧
        (∀ rl ∈ rls, rl.k = kFlag ∧ rl.ctorParams = cParams) := by
  induction raw with
  | nil cell =>
    intro rules₀ hfa
    cases hfa with
    | nil =>
      exact ⟨[], .nil, .nil cell, fun _ hm => nomatch hm⟩
  | @cons j addr v rest ru rus cell hr _ ih =>
    intro rules₀ hfa
    cases hfa with
    | @cons _ rl₀ _ rest₀ hhd htl =>
      obtain ⟨hnf, hrhs_rd, hrhs_lbb, hrhs_def⟩ := hhd
      obtain ⟨hf56, rhsPtr, rfl, hrhs_raw⟩ := hr
      obtain ⟨rhs', hArhs, hTm_rhs⟩ :=
        hrhs_raw.toTmC hperm hps_lt hkeyAt hself hblob hrhs_rd hrhs_lbb hrhs_def
      obtain ⟨rls_tl, hfa_tl, hrep_tl, hprops_tl⟩ := ih htl
      let rl' : Ix.Kernel.RecRule .anon :=
        { rl₀ with rhs := rhs', k := kFlag, ctorParams := cParams }
      have hrule_rep : Core.RuleRep κ h ps j
          (.construct Core.krrEnum "Mk" [.field (j : F), .field (ru.fields.toNat : F), rhsPtr]) rl' := by
        refine ⟨rhsPtr, ?_, ?_, hTm_rhs⟩
        · simp [rl', hnf]
        · simp [rl', hnf]; exact hf56
      refine ⟨rl' :: rls_tl,
        .cons ⟨rfl, rfl, hArhs⟩ hfa_tl,
        .cons cell hrule_rep hrep_tl,
        fun rl hmem => ?_⟩
      rcases List.mem_cons.mp hmem with rfl | hmem_tl
      · exact ⟨rfl, rfl⟩
      · exact hprops_tl rl hmem_tl

/-- Bridge from `RawRecrValRep` to `StoredAs` and `Core.CIRep`.
Note that `rc.typ` is read under an arbitrary `selfTy` (because `RawRecrValRep` has `recurAddrs = []`
on `rc.typ`, `hself` holds vacuously for `rc.typ`!). -/
theorem RawRecrValRep.toCIRep {κ : _root_.Address → Core.KKey}
    {name : Core.KKey} {ps : List Ix.Kernel.LevelParam}
    {rc : Ixon.Recursor} {blkAddr : _root_.Address} {recIdx : Nat}
    (hname : name = κ blkAddr ∨ name = κ (Core.rprjAddr blkAddr recIdx))
    (hnl : ps.length = rc.lvls.toNat) (hperm : ps.Perm (List.range ps.length))
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    (hkeyAt : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (hself : ∀ i a m k, recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (hblob : ∀ a bs, (a, bs) ∈ blobs → cx.blob a = some bs)
    {h : Heap F} {v : SourceValue F} {ty₀ : Core.KExpr}
    {rules₀ : List (Ix.Kernel.RecRule .anon)}
    (raw : RawRecrValRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h rc blkAddr recIdx v)
    (hty_rd : (Ix.Kernel.Reader.MemberReader.mk' cx src (Ix.Kernel.Reader.recParam ps) self).read
      rc.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true) (hty_def : ty₀.allLevelParamsDefined ps = true)
    (hrules_rd : List.Forall₂ (fun ru rl₀ =>
      rl₀.nfields = ru.fields.toNat ∧
      (Ix.Kernel.Reader.MemberReader.mk' cx src (Ix.Kernel.Reader.recParam ps) self).read ru.rhs =
        .ok rl₀.rhs ∧
      rl₀.rhs.looseBVarsBounded 0 = true ∧
      rl₀.rhs.allLevelParamsDefined ps = true) rc.rules.toList rules₀)
    (hk_sz : rc.k = true → rc.rules.size = 1) :
    ∃ ci : Ix.Kernel.ConstantInfo .anon,
      IxVM.Consistency.StoredAs ci
        (.recInfo ⟨name, ps, ty₀⟩
          (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
          (rc.params.toNat + rc.motives.toNat + rc.minors.toNat)
          rules₀) ∧
      Core.CIRep κ h v ci := by
  obtain ⟨hlvls, hp56, hi56, hm56, hmi56, hidx56,
    tyPtr, rulesPtr, blkPtr, b, hb_eq, hb_rep, rfl, hty_raw, hrls_raw⟩ := raw
  have hps_lt : ps.length < 4294967296 := by omega
  have hself_nil : ∀ i a m k, ([] : List _root_.Address)[i]? = some a →
      self i = some m → m = .ok k → k = κ a := fun _ _ _ _ hrec => nomatch hrec
  obtain ⟨ty', hvs, hvr⟩ :=
    rawConvExpr_to_valRep hnl hperm hlvls hkeyAt hself_nil hblob hty_raw hty_rd hty_lbb hty_def
  obtain ⟨rls, hfa_stored, hrep_rls, hprops⟩ :=
    hrls_raw.toRulesRep hperm hps_lt hkeyAt hself hblob rc.k rc.params.toNat hrules_rd
  let rP := rc.params.toNat + rc.motives.toNat + rc.minors.toNat
  let mI := rP + rc.indices.toNat
  refine ⟨.recInfo ⟨name, ps, ty'⟩ mI rP rls, ⟨hvs, rfl, rfl, hfa_stored⟩,
    .recr hvr rfl rfl rfl rfl (by simp only [rP]; push_cast; ring) (by simp only [mI, rP]; push_cast; ring)
      ⟨by omega, by omega⟩ hrep_rls ?_ ⟨b, (recIdx : F), hb_rep, rfl, ?_⟩⟩
  · intro hk1
    have hrck : rc.k = true := by
      cases hk : rc.k <;> simp [repBoolField, hk] at hk1
      rfl
    have hlen1 : rls.length = 1 := by
      have hl1 := hfa_stored.length_eq
      have hl2 := hrules_rd.length_eq
      rw [hl1, ← hl2, Array.length_toList, hk_sz hrck]
    rcases rls with _ | ⟨rl, _ | _⟩
    · simp at hlen1
    · obtain ⟨hrlk, hrlp⟩ := hprops rl (List.mem_singleton.mpr rfl)
      rw [hrck] at hrlk
      rw [← val_cast_u56_conv hp56] at hrlp
      exact ⟨rl, rfl, hrlk, hrlp⟩
    · simp at hlen1
  · rw [hb_eq, val_cast_u56_conv hidx56]
    exact hname

end IxVM.Refinement.L1
