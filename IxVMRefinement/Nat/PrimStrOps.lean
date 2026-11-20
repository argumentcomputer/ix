import IxVMRefinement.Nat.PrimStr
import IxVMRefinement.Nat.PrimInt
import IxVMRefinement.Nat.Utf8
import IxVMRefinement.Obs.KernelRoleSpec0

/-! # `KernelNatPrim`: `String` and `Char` native acceleration step lemmas

Step lemmas of the nineteen `String`/`Char` acceleration functions of `KernelNatPrim`, against
their registered specs in `Core/Specs/Nat.lean`:
* UTF-8 helpers: `utf8_last_go`, `utf8_last_codepoint`, `utf8_encode_prepend`,
  `klimbs_scalar_value`.
* Character list recognition: `lvls_is_zero1`, `is_char_const`, `is_char_const_or_whnf`,
  `char_lit_codepoint_syn`, `char_lit_codepoint`, `match_char_list_head_syn`,
  `walk_char_list_bytes`.
* Operation handlers & dispatch: `try_str_of_list` (`Red.strLitFold`), `try_str_utf8_byte_size`,
  `try_str_back`, `try_str_to_byte_array`, `try_str_dec_eq`, `try_str_append`,
  `try_char_utf8_size`, and `try_str_dispatch`. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open Ix.Kernel.Rules (Red DefEq Infer)
open NatAux

set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PrimStrOps

/-! ## UTF-8, byte-list, and string helpers -/

theorem utf8EncodeChar_ne_nil (ch : Char) : String.utf8EncodeChar ch ≠ [] := by
  rw [Utf8Aux.utf8EncodeChar_eq]
  split
  · simp
  · split
    · simp
    · split <;> simp

theorem utf8EncodeChar_prefix_inj {c₁ c₂ : Char} {t₁ t₂ : List UInt8}
    (h : String.utf8EncodeChar c₁ ++ t₁ = String.utf8EncodeChar c₂ ++ t₂) :
    c₁ = c₂ ∧ t₁ = t₂ := by
  have h1lt := Utf8Aux.char_toNat_lt c₁
  have h2lt := Utf8Aux.char_toNat_lt c₂
  have hv1 : c₁.val.toNat = c₁.toNat := rfl
  have hv2 : c₂.val.toNat = c₂.toNat := rfl
  have hbyte : ∀ {a b : Nat}, a < 256 → b < 256 → UInt8.ofNat a = UInt8.ofNat b → a = b := by
    intro a b ha hb heq
    have := congrArg UInt8.toNat heq
    rwa [L1.toNat_ofNat_lt ha, L1.toNat_ofNat_lt hb] at this
  rw [Utf8Aux.utf8EncodeChar_eq, Utf8Aux.utf8EncodeChar_eq] at h
  by_cases h1a : c₁.toNat ≤ 127 <;> by_cases h2a : c₂.toNat ≤ 127
  · simp only [h1a, h2a, ↓reduceIte, List.cons_append, List.nil_append, List.cons.injEq] at h
    exact ⟨Char.ext (UInt32.ext (hbyte (by omega) (by omega) h.1)), h.2⟩
  · by_cases h2b : c₂.toNat ≤ 2047
    · simp only [h1a, h2a, h2b, ↓reduceIte, List.cons_append, List.nil_append, List.cons.injEq] at h
      have := hbyte (by omega) (by omega) h.1; omega
    · by_cases h2c : c₂.toNat ≤ 65535
      · simp only [h1a, h2a, h2b, h2c, ↓reduceIte, List.cons_append, List.nil_append, List.cons.injEq] at h
        have := hbyte (by omega) (by omega) h.1; omega
      · simp only [h1a, h2a, h2b, h2c, ↓reduceIte, List.cons_append, List.nil_append, List.cons.injEq] at h
        have := hbyte (by omega) (by omega) h.1; omega
  · by_cases h1b : c₁.toNat ≤ 2047
    · simp only [h1a, h1b, h2a, ↓reduceIte, List.cons_append, List.nil_append, List.cons.injEq] at h
      have := hbyte (by omega) (by omega) h.1; omega
    · by_cases h1c : c₁.toNat ≤ 65535
      · simp only [h1a, h1b, h1c, h2a, ↓reduceIte, List.cons_append, List.nil_append, List.cons.injEq] at h
        have := hbyte (by omega) (by omega) h.1; omega
      · simp only [h1a, h1b, h1c, h2a, ↓reduceIte, List.cons_append, List.nil_append, List.cons.injEq] at h
        have := hbyte (by omega) (by omega) h.1; omega
  · by_cases h1b : c₁.toNat ≤ 2047 <;> by_cases h2b : c₂.toNat ≤ 2047
    · simp only [h1a, h1b, h2a, h2b, ↓reduceIte, List.cons_append, List.nil_append, List.cons.injEq] at h
      have hb0 := hbyte (by omega) (by omega) h.1
      have hb1 := hbyte (by omega) (by omega) h.2.1
      rw [Nat.mod_eq_of_lt (show c₁.toNat / 64 < 32 by omega),
        Nat.mod_eq_of_lt (show c₂.toNat / 64 < 32 by omega)] at hb0
      exact ⟨Char.ext (UInt32.ext (by omega)), h.2.2⟩
    · by_cases h2c : c₂.toNat ≤ 65535
      · simp only [h1a, h1b, h2a, h2b, h2c, ↓reduceIte, List.cons_append, List.nil_append, List.cons.injEq] at h
        have := hbyte (by omega) (by omega) h.1; omega
      · simp only [h1a, h1b, h2a, h2b, h2c, ↓reduceIte, List.cons_append, List.nil_append, List.cons.injEq] at h
        have := hbyte (by omega) (by omega) h.1; omega
    · by_cases h1c : c₁.toNat ≤ 65535
      · simp only [h1a, h1b, h1c, h2a, h2b, ↓reduceIte, List.cons_append, List.nil_append, List.cons.injEq] at h
        have := hbyte (by omega) (by omega) h.1; omega
      · simp only [h1a, h1b, h1c, h2a, h2b, ↓reduceIte, List.cons_append, List.nil_append, List.cons.injEq] at h
        have := hbyte (by omega) (by omega) h.1; omega
    · by_cases h1c : c₁.toNat ≤ 65535 <;> by_cases h2c : c₂.toNat ≤ 65535
      · simp only [h1a, h1b, h1c, h2a, h2b, h2c, ↓reduceIte, List.cons_append, List.nil_append, List.cons.injEq] at h
        have hb0 := hbyte (by omega) (by omega) h.1
        have hb1 := hbyte (by omega) (by omega) h.2.1
        have hb2 := hbyte (by omega) (by omega) h.2.2.1
        rw [Nat.mod_eq_of_lt (show c₁.toNat / 4096 < 16 by omega),
          Nat.mod_eq_of_lt (show c₂.toNat / 4096 < 16 by omega)] at hb0
        have hq1 : c₁.toNat / 4096 = c₂.toNat / 4096 := by omega
        have hq2 : c₁.toNat / 64 % 64 = c₂.toNat / 64 % 64 := by omega
        have hq3 : c₁.toNat % 64 = c₂.toNat % 64 := by omega
        have hdiv64 : c₁.toNat / 64 = c₂.toNat / 64 := by omega
        exact ⟨Char.ext (UInt32.ext (by omega)), h.2.2.2⟩
      · simp only [h1a, h1b, h1c, h2a, h2b, h2c, ↓reduceIte, List.cons_append, List.nil_append, List.cons.injEq] at h
        have := hbyte (by omega) (by omega) h.1; omega
      · simp only [h1a, h1b, h1c, h2a, h2b, h2c, ↓reduceIte, List.cons_append, List.nil_append, List.cons.injEq] at h
        have := hbyte (by omega) (by omega) h.1; omega
      · simp only [h1a, h1b, h1c, h2a, h2b, h2c, ↓reduceIte, List.cons_append, List.nil_append, List.cons.injEq] at h
        have hb0 := hbyte (by omega) (by omega) h.1
        have hb1 := hbyte (by omega) (by omega) h.2.1
        have hb2 := hbyte (by omega) (by omega) h.2.2.1
        have hb3 := hbyte (by omega) (by omega) h.2.2.2.1
        rw [Nat.mod_eq_of_lt (show c₁.toNat / 262144 < 8 by omega),
          Nat.mod_eq_of_lt (show c₂.toNat / 262144 < 8 by omega)] at hb0
        have hq0 : c₁.toNat / 262144 = c₂.toNat / 262144 := by omega
        have hq1 : c₁.toNat / 4096 % 64 = c₂.toNat / 4096 % 64 := by omega
        have hq2 : c₁.toNat / 64 % 64 = c₂.toNat / 64 % 64 := by omega
        have hq3 : c₁.toNat % 64 = c₂.toNat % 64 := by omega
        have hdiv4096 : c₁.toNat / 4096 = c₂.toNat / 4096 := by omega
        have hdiv64 : c₁.toNat / 64 = c₂.toNat / 64 := by omega
        exact ⟨Char.ext (UInt32.ext (by omega)), h.2.2.2.2⟩

theorem getLastD_cons_eq {α : Type} (x : α) (xs : List α) (d : α) :
    (x :: xs).getLastD d = xs.getLastD x := by
  cases xs with
  | nil => rfl
  | cons y ys => rfl

private theorem list_toByteArray_loop_size (xs : List UInt8) (acc : ByteArray) :
    (List.toByteArray.loop xs acc).size = acc.size + xs.length := by
  induction xs generalizing acc with
  | nil => simp [List.toByteArray.loop]
  | cons b bs ih =>
    simp only [List.toByteArray.loop, ih, ByteArray.size_push, List.length_cons]
    omega

theorem strBytes_length_eq {s : String} {bs : List UInt8} (hs : StrBytes s bs) :
    bs.length = s.utf8ByteSize := by
  obtain ⟨cs, hcs⟩ := Utf8Aux.exists_strBytes_iff.mp ⟨s, hs⟩
  obtain rfl := Utf8Aux.strBytes_eq_ofList hs hcs
  have hba : (String.ofList cs).toByteArray = bs.toByteArray := by
    rw [String.toByteArray_ofList, ← hcs]
    rfl
  calc bs.length
      = bs.toByteArray.size := by
        simp [List.toByteArray, list_toByteArray_loop_size, ByteArray.size_empty]
    _ = (String.ofList cs).toByteArray.size := by rw [hba]
    _ = (String.ofList cs).utf8ByteSize := rfl

theorem strBytes_nil_eq_empty {s : String} (hs : StrBytes s []) : s = "" := by
  obtain ⟨cs, hcs⟩ := Utf8Aux.exists_strBytes_iff.mp ⟨s, hs⟩
  obtain rfl := Utf8Aux.strBytes_eq_ofList hs hcs
  cases cs with
  | nil => rfl
  | cons ch rest =>
    simp only [List.flatMap_cons] at hcs
    exact absurd (List.append_eq_nil_iff.mp hcs).1 (utf8EncodeChar_ne_nil ch)

theorem strBytes_append {s₁ s₂ : String} {bs₁ bs₂ : List UInt8}
    (h₁ : StrBytes s₁ bs₁) (h₂ : StrBytes s₂ bs₂) :
    StrBytes (s₁ ++ s₂) (bs₁ ++ bs₂) := by
  obtain ⟨cs₁, hcs₁⟩ := Utf8Aux.exists_strBytes_iff.mp ⟨s₁, h₁⟩
  obtain ⟨cs₂, hcs₂⟩ := Utf8Aux.exists_strBytes_iff.mp ⟨s₂, h₂⟩
  obtain rfl := Utf8Aux.strBytes_eq_ofList h₁ hcs₁
  obtain rfl := Utf8Aux.strBytes_eq_ofList h₂ hcs₂
  have hflat : (cs₁ ++ cs₂).flatMap String.utf8EncodeChar = bs₁ ++ bs₂ := by
    rw [List.flatMap_append, hcs₁, hcs₂]
  rw [String.ofList_append.symm, ← hflat]
  exact Utf8Aux.strBytes_ofList (cs₁ ++ cs₂)

theorem strBytes_inj {s₁ s₂ : String} {bs : List UInt8}
    (h₁ : StrBytes s₁ bs) (h₂ : StrBytes s₂ bs) : s₁ = s₂ := by
  unfold StrBytes at h₁ h₂
  rw [h₁] at h₂
  exact Option.some.inj h₂

theorem repByteStream_cons_of {h m : Heap F} {b : UInt8} {bs : List UInt8} {bp tp : SourceValue F}
    (hb : RepU8 h b bp) (ht : Bytes.RepByteStream byteListEnum h bs tp)
    (hm : m = h ++ [.construct byteListEnum "Cons" [bp, tp]]) :
    Bytes.RepByteStream byteListEnum m (b :: bs) (.ptr (.enum byteListEnum) h.length) := by
  subst hm
  exact Lib.rep_store_cons repU8_heapMono₂ hb ht

theorem repByteStream_nil_of {h m : Heap F}
    (hm : m = h ++ [.construct byteListEnum "Nil" []]) :
    Bytes.RepByteStream byteListEnum m [] (.ptr (.enum byteListEnum) h.length) := by
  subst hm
  exact allocNil_rep byteListEnum RepU8 h

theorem bl_length {xs : List UInt8} {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<Field>» [l] h r h' cs)
    (hl : Bytes.RepByteStream byteListEnum h xs l) :
    r = .field (xs.length : F) ∧ h' = h :=
  Lib.Lists.length_spec (t := .field) (R := RepU8)
    (by rw [Obs.Names.«Lists::length<Field>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<Field>».symbol]; exact hl)

theorem bl_concat {xs ys : List UInt8} {a b r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::concat<Field>» [a, b] h r h' cs)
    (ha : Bytes.RepByteStream byteListEnum h xs a)
    (hb : Bytes.RepByteStream byteListEnum h ys b) :
    Bytes.RepByteStream byteListEnum h' (xs ++ ys) r := by
  have hcat := Lib.Lists.concat_spec (t := .field) (R := RepU8) repU8_heapMono₂
    (by rw [Obs.Names.«Lists::concat<Field>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<Field>».symbol]; exact ha)
    (by rw [Obs.Names.«Lists::Node<Field>».symbol]; exact hb)
  rw [Obs.Names.«Lists::Node<Field>».symbol] at hcat
  exact hcat

/-! ## Level & role helpers -/

theorem lv_zero_of_load {h : Heap F} {l : KLevel} {p : SourceValue F} (rep : RepKLevel h l p)
    (hl : loadValue h p = .ok (.construct "KernelTypes::KLevelNode" "Zero" [])) :
    l = .zero := by
  cases rep with
  | zero _ => rfl
  | succ cell _ | max cell _ _ | imax cell _ _ | param _ cell =>
    simp [loadValue, cell] at hl

theorem repKLevelList_one_of {h m0 m1 mn mc : Heap F}
    (hm0 : m0 = h ++ [.construct klevelEnum "Zero" []])
    (hm1 : m1 = m0 ++ [.construct klevelEnum "Succ" [.ptr (.enum klevelEnum) h.length]])
    (hmn : mn = m1 ++ [.construct klevelListEnum "Nil" []])
    (hmc : mc = mn ++ [.construct klevelListEnum "Cons"
      [.ptr (.enum klevelEnum) m0.length, .ptr (.enum klevelListEnum) m1.length]]) :
    RepKLevelList mc [.succ .zero] (.ptr (.enum klevelListEnum) mn.length) := by
  have hz : RepKLevel m0 .zero (.ptr (.enum klevelEnum) h.length) := by
    rw [hm0]; exact (IxVM.Refinement.KernelLevels.RepKLevel.allocZero h).1
  have hs : RepKLevel m1 (.succ .zero) (.ptr (.enum klevelEnum) m0.length) :=
    RepKLevel.succ (by rw [hm1]; simp) (hz.mono (PrimStrAux.ext_of_eq_snoc hm1))
  have hn := PrimStrAux.repKLevelList_nil_of hmn
  have ext_n := PrimStrAux.ext_of_eq_snoc hmn
  have ext_c := PrimStrAux.ext_of_eq_snoc hmc
  subst hmc
  rw [klevelListEnum_eq] at hn ext_c ⊢
  exact .cons List.getElem?_concat_length ((hs.mono ext_n).mono ext_c) (hn.mono ext_c)

theorem isTowerEntry_false_of_role {env : Ix.Kernel.Env .anon} {ci : Ix.Kernel.ConstantInfo .anon}
    {r : Ix.Kernel.Role} (hf : env.find? (.role r) = some ci) : ci.isTowerEntry = false := by
  have hnm : ci.name = .role r := by
    have h1 := List.find?_some (p := fun c : Ix.Kernel.ConstantInfo .anon => c.name == .role r) hf
    exact beq_iff_eq.mp h1
  cases ci with
  | projInfo tbl =>
    simp [Ix.Kernel.ConstantInfo.name, Ix.Kernel.ConstantInfo.toConstantVal,
      Ix.Kernel.projTableName, Ix.Kernel.auxKey] at hnm
  | _ => rfl

/-- Under `strLitSupported env`, a constant `.const (.role r) [u]` whose level parameter evaluates
to `0` everywhere reduces to `.const (.role r) [.zero]` at any depth (`Red.defEqClosed`). -/
theorem red_const_zero_level {env : Ix.Kernel.Env .anon} {r : Ix.Kernel.Role} {d : Nat}
    {u : KLevel} {ci : Ix.Kernel.ConstantInfo .anon}
    (hf : env.find? (.role r) = some ci)
    (hlp : ci.toConstantVal.levelParams.length = 1)
    (hu : ∀ φ, Ix.Kernel.Level.eval φ u = 0) :
    Red env d (.const (.role r) [u]) (.const (.role r) [.zero]) := by
  have hnt := isTowerEntry_false_of_role hf
  have hinf1 : Infer env .full 0 (.const (.role r) [u])
      (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams [u]) :=
    Infer.const hf hnt (by simp [hlp])
  have hinf2 : Infer env .full 0 (.const (.role r) [.zero])
      (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams [.zero]) :=
    Infer.const hf hnt (by simp [hlp])
  have hde : DefEq env 0 (.const (.role r) [u]) (.const (.role r) [.zero]) :=
    DefEq.const (fun φ => by simp [Ix.Kernel.Level.EvalEqList, Ix.Kernel.Level.eval, hu φ])
  exact Red.defEqClosed rfl rfl rfl rfl rfl rfl rfl rfl rfl hinf1 .refl hinf2 .refl hde

theorem listNil_info_of_strLit {env : Ix.Kernel.Env .anon}
    (hsup : Ix.Kernel.strLitSupported env = true) :
    ∃ ci, env.find? Ix.Kernel.listNilName = some ci ∧ ci.toConstantVal.levelParams.length = 1 := by
  have hok : Ix.Kernel.listNilTyOk (env.find? Ix.Kernel.listNilName) = true := by
    unfold Ix.Kernel.strLitSupported at hsup
    simp only [Bool.and_eq_true] at hsup
    exact hsup.1.1.1.2
  cases hf : env.find? Ix.Kernel.listNilName with
  | none => simp [hf, Ix.Kernel.listNilTyOk] at hok
  | some ci =>
    rw [hf] at hok
    unfold Ix.Kernel.listNilTyOk at hok
    cases hlp : ci.toConstantVal.levelParams with
    | nil => simp [hlp] at hok
    | cons p ps =>
      cases ps with
      | nil => exact ⟨ci, rfl, by simp [hlp]⟩
      | cons _ _ => simp [hlp] at hok

theorem listCons_info_of_strLit {env : Ix.Kernel.Env .anon}
    (hsup : Ix.Kernel.strLitSupported env = true) :
    ∃ ci, env.find? Ix.Kernel.listConsName = some ci ∧ ci.toConstantVal.levelParams.length = 1 := by
  have hok : Ix.Kernel.listConsTyOk (env.find? Ix.Kernel.listConsName) = true := by
    unfold Ix.Kernel.strLitSupported at hsup
    simp only [Bool.and_eq_true] at hsup
    exact hsup.1.1.2
  cases hf : env.find? Ix.Kernel.listConsName with
  | none => simp [hf, Ix.Kernel.listConsTyOk] at hok
  | some ci =>
    rw [hf] at hok
    unfold Ix.Kernel.listConsTyOk at hok
    cases hlp : ci.toConstantVal.levelParams with
    | nil => simp [hlp] at hok
    | cons p ps =>
      cases ps with
      | nil => exact ⟨ci, rfl, by simp [hlp]⟩
      | cons _ _ => simp [hlp] at hok

theorem stringOfList_stored_of_strLit {env : Ix.Kernel.Env .anon}
    (hsup : Ix.Kernel.strLitSupported env = true) :
    ∃ ci, env.find? (.role .stringOfList) = some ci := by
  have hok : Ix.Kernel.stringOfListTyOk (env.find? Ix.Kernel.stringOfListName) = true := by
    unfold Ix.Kernel.strLitSupported at hsup
    simp only [Bool.and_eq_true] at hsup
    exact hsup.1.1.1.1.1.2
  cases hf : env.find? Ix.Kernel.stringOfListName with
  | none => simp [hf, Ix.Kernel.stringOfListTyOk] at hok
  | some ci => exact ⟨ci, rfl⟩

theorem key_res_of_stored {c : ScopedCtx} (hc : ScopedCoreBase c) {ro : Ix.Kernel.Role}
    {a : Bytes.Address} (hb : c.t.addressOf? ro = some (ixAddr a))
    (hst : ∃ ci, c.env.find? (.role ro) = some ci) :
    c.κ (ixAddr a) ≠ unresolvedKey := by
  obtain ⟨ci, hci⟩ := hst
  exact hc.loads.storedRes (ixAddr a) ci (by rw [keyOf_of_addressOf hc.env.tableWf hb]; exact hci)

theorem strPrimOp_eq_of_val {ro : Ix.Kernel.Role} {o : Nat}
    (h : Specs.Nat.strPrimOp ro = some o) :
    (o = 1 → ro = .stringOfList) ∧ (o = 2 → ro = .stringUtf8ByteSize) ∧
    (o = 3 → ro = .stringBack) ∧ (o = 4 → ro = .stringToByteArray) ∧
    (o = 5 → ro = .stringDecEq) ∧ (o = 6 → ro = .stringAppend) ∧
    (o = 7 → ro = .charUtf8Size) := by
  cases ro <;> simp [Specs.Nat.strPrimOp] at h <;> subst h <;> decide

theorem strPrimOp_group_ge46 {ro : Ix.Kernel.Role} {o : Nat}
    (h : Specs.Nat.strPrimOp ro = some o) (hne : ro ≠ .stringOfList) :
    46 ≤ Ix.SpecDigest.groupOf ro := by
  cases ro <;> simp [Specs.Nat.strPrimOp] at h
  · exact absurd rfl hne
  all_goals decide

theorem strPrimOp_mem_stored {ro : Ix.Kernel.Role} {o : Nat}
    (h : Specs.Nat.strPrimOp ro = some o) (hne : ro ≠ .stringOfList) :
    ro ∈ [.stringUtf8ByteSize, .stringBack, .stringToByteArray, .stringDecEq, .stringAppend,
      .charUtf8Size] := by
  cases ro <;> simp [Specs.Nat.strPrimOp] at h
  · exact absurd rfl hne
  all_goals decide

theorem strOpAt_key_and_prim {c : ScopedCtx} (hc : ScopedCoreBase c) {a : Bytes.Address} {o : Nat}
    {ro : Ix.Kernel.Role} (hro : Specs.Nat.strPrimOp ro = some o) (hne : ro ≠ .stringOfList)
    (haddr : c.t.addressOf? ro = some (ixAddr a)) (hforce : c.inForce ro) :
    PrimEqnEnv c.env ∧ c.κ (ixAddr a) = .role ro := by
  have hprim := hc.env.primEqn ⟨ro, strPrimOp_group_ge46 hro hne, hforce⟩
  have hres := key_res_of_stored hc haddr (hprim.strOpStored ro (strPrimOp_mem_stored hro hne))
  exact ⟨hprim, (c.key_eq hres).trans (keyOf_of_addressOf hc.env.tableWf haddr)⟩

theorem repLimbsC_small {h m1 m2 : Heap F} {k : Nat} (hk1 : 0 < k) (hk2 : k < 256)
    (hm1 : m1 = h ++ [.construct limbListEnum "Nil" []])
    (hm2 : m2 = m1 ++ [.construct limbListEnum "Cons"
      [.tuple [.field (k : F), .field 0, .field 0, .field 0, .field 0, .field 0, .field 0, .field 0],
       .ptr (.enum limbListEnum) h.length]]) :
    Specs.Nat.RepLimbsC m2 k (.ptr (.enum limbListEnum) m1.length) := by
  subst hm1 hm2
  obtain ⟨w, hw, hr⟩ := word_of (h ++ [.construct limbListEnum "Nil" []]) (m := k) (by omega)
  have hu : TagN.u64Value k =
      .tuple [.field (k : F), .field 0, .field 0, .field 0, .field 0, .field 0, .field 0, .field 0] := by
    rw [PrimStrAux.u64Value_lt32 (by omega)]
    have e0 : k % 256 = k := Nat.mod_eq_of_lt hk2
    have e1 : k / 256 = 0 := Nat.div_eq_of_lt hk2
    have e2 : k / 65536 = 0 := by omega
    have e3 : k / 16777216 = 0 := by omega
    simp [e0, e1, e2, e3]
  rw [hu] at hr
  refine ⟨[w], lrep_store_cons hr (lrep_store_nil h),
    by simp [limbsVal_cons, limbsVal_nil, hw], ?_⟩
  simp only [List.getLast?_singleton, ne_eq, Option.some.injEq]
  intro h0
  have := congrArg UInt64.toNat h0
  simp [hw] at this
  omega

theorem char_utf8Size_eq (ch : Char) :
    ch.utf8Size =
      if ch.toNat < 128 then 1
      else if ch.toNat < 2048 then 2
      else if ch.toNat < 65536 then 3
      else 4 := by
  have hdef : ch.utf8Size =
      if ch.val ≤ 0x7f then 1
      else if ch.val ≤ 0x7ff then 2
      else if ch.val ≤ 0xffff then 3
      else 4 := rfl
  rw [hdef]
  change (if ch.toNat ≤ 127 then 1
    else if ch.toNat ≤ 2047 then 2
    else if ch.toNat ≤ 65535 then 3
    else 4) = _
  by_cases h1 : ch.toNat ≤ 127
  · have h1' : ch.toNat < 128 := by omega
    simp [h1, h1']
  · have h1' : ¬ ch.toNat < 128 := by omega
    by_cases h2 : ch.toNat ≤ 2047
    · have h2' : ch.toNat < 2048 := by omega
      simp [h1, h1', h2, h2']
    · have h2' : ¬ ch.toNat < 2048 := by omega
      by_cases h3 : ch.toNat ≤ 65535
      · have h3' : ch.toNat < 65536 := by omega
        simp [h1, h1', h2, h2', h3, h3']
      · have h3' : ¬ ch.toNat < 65536 := by omega
        simp [h1, h1', h2, h2', h3, h3']

theorem u32_fromField_4x {n : Nat} {v_mul v_u32 w0 w1 w2 w3 : SourceValue F}
    {h m1 m2 : Heap F} {cs1 cs2 : List (Call F)} (hn : n < 1073741824)
    (op_mul : evalBinOp .mul (.field (n : F)) (.field 4) = .ok v_mul)
    (ev_ff : ObsFn W "UInt32::from_field" [v_mul] h v_u32 m1 cs1)
    (ev_tb : ObsFn W "UInt32::to_bytes" [v_u32] m1 (.tuple [w0, w1, w2, w3]) m2 cs2) :
    ∃ c0 c1 c2 c3 : UInt8,
      w0 = .field (c0.toNat : F) ∧ w1 = .field (c1.toNat : F) ∧
      w2 = .field (c2.toNat : F) ∧ w3 = .field (c3.toNat : F) ∧
      m1 = h ∧ m2 = h ∧
      4 * n = c0.toNat + 256 * (c1.toNat + 256 * (c2.toNat + 256 * c3.toNat)) := by
  have hm := PrimInt.field_mul_eq op_mul
  subst hm
  obtain ⟨c0, c1, c2, c3, rfl, rfl, hval, _⟩ := L1.u32_fromField ev_ff
  obtain ⟨hbytes, rfl⟩ := L1.u32_toBytes ev_tb
  simp only [L1.w4, L1.bv, Value.tuple.injEq, List.cons.injEq, and_true] at hbytes
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hbytes
  have hcast : ((n : F) * (4 : F)) = ((4 * n : Nat) : F) := by push_cast; ring
  rw [hcast, NatAux.val_natCast (by show _ < 18446744069414584321; omega), Aiur.Library.Blake3.wordOfBytes_toNat] at hval
  simp only [Aiur.Library.U32.pack] at hval
  exact ⟨c0, c1, c2, c3, rfl, rfl, rfl, rfl, rfl, rfl, by omega⟩

theorem u8_fromField_nat {k : Nat} {v : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hk : k < 256) (ev : ObsFn W "UInt8::from_field" [.field (k : F)] h v h' cs) :
    v = .field ((UInt8.ofNat k).toNat : F) ∧ RepU8 h (UInt8.ofNat k) v ∧ h' = h := by
  obtain ⟨b, hbv, rfl, rfl⟩ := L1.u8_fromField ev
  have hbk : b.toNat = k :=
    L1.natCast_byte_inj (L1.byte_lt b) hk (Value.field.inj hbv.symm)
  have hbe : b = UInt8.ofNat k := UInt8.ext (by rw [hbk, L1.toNat_ofNat_lt hk])
  subst hbe
  exact ⟨rfl, rfl, rfl⟩

theorem cast_sub_mul64 {n q : Nat} (hq : 64 * q ≤ n) :
    (n : F) - (64 : F) * (q : F) = ((n - 64 * q : Nat) : F) := by
  have h1 : (64 : F) * (q : F) = ((64 * q : Nat) : F) := by push_cast; ring
  rw [h1, ← Nat.cast_sub hq]

theorem cast_add_nat (a b : Nat) : (a : F) + (b : F) = ((a + b : Nat) : F) := by
  push_cast; ring

theorem mul_eq_one_iff_bits {a b : F} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    (hm : a * b = 1) : a = 1 ∧ b = 1 := by
  rcases ha with rfl | rfl
  · simp at hm
  · rcases hb with rfl | rfl
    · simp at hm
    · exact ⟨rfl, rfl⟩

theorem tag3_fst_eq {t₁ t₂ : F} {a₁ b₁ a₂ b₂ : SourceValue F}
    (h : (Value.tuple [.field t₁, a₁, b₁] : SourceValue F) = .tuple [.field t₂, a₂, b₂]) :
    t₁ = t₂ ∧ a₁ = a₂ ∧ b₁ = b₂ := by
  injection h with h1
  injection h1 with ht h2
  injection h2 with ha h3
  injection h3 with hb
  exact ⟨Value.field.inj ht, ha, hb⟩

theorem u64_lt_24_of_hi_zero {n : Nat} (hn : n < 18446744073709551616)
    (hsum : n / 16777216 % 256 + n / 4294967296 % 256 + n / 1099511627776 % 256 +
      n / 281474976710656 % 256 + n / 72057594037927936 % 256 = 0) :
    n < 16777216 := by
  simp only [Nat.add_eq_zero_iff] at hsum
  obtain ⟨⟨⟨⟨h3, h4⟩, h5⟩, h6⟩, h7⟩ := hsum
  rw [Nat.mod_eq_of_lt (show n / 72057594037927936 < 256 by omega)] at h7
  rw [Nat.mod_eq_of_lt (show n / 281474976710656 < 256 by omega)] at h6
  rw [Nat.mod_eq_of_lt (show n / 1099511627776 < 256 by omega)] at h5
  rw [Nat.mod_eq_of_lt (show n / 4294967296 < 256 by omega)] at h4
  rw [Nat.mod_eq_of_lt (show n / 16777216 < 256 by omega)] at h3
  omega

end PrimStrOps

open PrimStrOps

/-! ## Step lemmas for the nineteen `String` / `Char` functions -/

/-- `KernelNatPrim::utf8_last_go(bs, prev)`. -/
theorem utf8_last_go_step (c : ScopedCtx)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::utf8_last_go" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.utf8_last_go c args h r h' calls := by
  intro bp pv hargs good bs hbs p hpv cs hcs
  subst hargs hpv
  rcases Obs.«KernelNatPrim::utf8_last_go».obs ev with
    ⟨ld_bs, he_r, he_h, hc_c⟩ |
    ⟨x_b0, x_rest, m_dec, cs_dec, x_cp, x_rem, cs_rec, ld_bs, ev_dec, ev_rec, hc_c⟩
  · obtain rfl := RepList.nil_of_load hbs ld_bs
    cases cs with
    | nil => exact he_r
    | cons ch rest =>
      simp only [List.flatMap_cons] at hcs
      exact absurd (List.append_eq_nil_iff.mp hcs).1 (utf8EncodeChar_ne_nil ch)
  · subst hc_c
    obtain ⟨b0, bs_rest, rfl, hb0, hrest⟩ := RepList.cons_of_load hbs ld_bs
    obtain ⟨ch, bs', rem, hsplit, hres, hbs'⟩ :=
      ih.get (.nat .utf8_decode_one) (by nat_lt_calls) ev_dec x_b0 x_rest rfl
        (good.sub fun x hx => by simp [hx]) b0 bs_rest hb0 hrest
    obtain ⟨rfl, rfl⟩ := Utf8Aux.tuple2_inj hres
    cases cs with
    | nil => simp at hcs
    | cons c₀ cs' =>
      simp only [List.flatMap_cons] at hcs
      obtain ⟨rfl, htail⟩ := utf8EncodeChar_prefix_inj (hcs.trans hsplit)
      have hrec := ih.get (.nat .utf8_last_go) (by nat_lt_calls) ev_rec x_rem c₀.toNat rfl
        (good.sub fun x hx => by simp [hx]) bs' hbs' c₀ rfl cs' htail
      rw [getLastD_cons_eq]
      exact hrec

/-- `KernelNatPrim::utf8_last_codepoint(bs)`. -/
theorem utf8_last_codepoint_step (c : ScopedCtx)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::utf8_last_codepoint" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.utf8_last_codepoint c args h r h' calls := by
  intro bp hargs good bs s hbs hs
  subst hargs
  obtain ⟨cs_go, ev_go, hc_c⟩ := Obs.«KernelNatPrim::utf8_last_codepoint».obs ev
  subst hc_c
  obtain ⟨cs, hcs⟩ := Utf8Aux.exists_strBytes_iff.mp ⟨s, hs⟩
  obtain rfl := Utf8Aux.strBytes_eq_ofList hs hcs
  have hgo := ih.get (.nat .utf8_last_go) (by nat_lt_calls) ev_go bp 65 rfl
    (good.sub fun x hx => by simp [hx]) bs hbs 'A' (by decide) cs hcs
  rwa [String.toList_ofList]

/-- `KernelNatPrim::utf8_encode_prepend(cp, tail)`. -/
theorem utf8_encode_prepend_step (c : ScopedCtx)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::utf8_encode_prepend" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.utf8_encode_prepend c args h r h' calls := by
  intro cp tp hargs good ch hcp tail htail
  subst hargs hcp
  have hclt := Utf8Aux.char_toNat_lt ch
  rcases Obs.«KernelNatPrim::utf8_encode_prepend».obs ev with
    ⟨m1, cs1, v_b0, m2, cs2, ev_lt1, he_r, hm_h, ev_b0, hc_c⟩ |
    ⟨v_lt1, m1, cs1, m2, cs2, m3, cs3, v_u1, m4, cs4, v_m1, w0, x1, w2, w3, v_q, m5, cs5,
      v_rem, y_64q, v_b0, m6, cs6, v_a0, v_b1, m7, cs7, v_a1, m8,
      ev_lt1, hne_lt1, ev_lt2, op_m1, ev_ff1, ev_tb1, ev_x1, op_64q, op_rem,
      op_a0, ev_b0, op_a1, ev_b1, he_r, hm_h, hm_8, hc_c⟩ |
    ⟨v_lt1, m1, cs1, v_lt2, m2, cs2, m3, cs3, m4, cs4, v_u1, m5, cs5, v_m1, w0, x1, x2, w3,
      v_q1, m6, x_x1, y_256x2, m7, cs6, y_x2, cs7, v_r0, y_64q1, m8, cs8, v_u2, m9, cs9, v_m2,
      wy0, y1, wy2, wy3, v_q2, m10, cs10, v_r1, y_64q2, v_b0, m11, cs11, v_a0, v_b1, m12, cs12,
      v_a1, v_b2, m13, cs13, v_a2, m14, m15,
      ev_lt1, hne_lt1, ev_lt2, hne_lt2, ev_lt3, op_m1, ev_ff1, ev_tb1, ev_x1, ev_x2, op_256x2,
      op_q1, op_64q1, op_r0, op_m2, ev_ff2, ev_tb2, ev_y1, op_64q2, op_r1,
      op_a0, ev_b0, op_a1, ev_b1, op_a2, ev_b2, he_r, hm_h, hm_14, hm_15, hc_c⟩ |
    ⟨v_lt1, m1, cs1, v_lt2, m2, cs2, v_lt3, m3, cs3, m4, cs4, v_u1, m5, cs5, v_m1, w0, x1, x2, w3,
      v_q1, m6, x_x1, y_256x2, m7, cs6, y_x2, cs7, v_r0, y_64q1, m8, cs8, v_u2, m9, cs9, v_m2,
      wy0, y1, y2, wy3, v_q2, m10, x_y1, y_256y2, m11, cs10, y_y2, cs11, v_r1, y_64q2, m12, cs12,
      v_u3, m13, cs13, v_m3, wz0, z1, wz2, wz3, v_q3, m14, cs14, v_r2, y_64q3,
      v_b0, m15, cs15, v_a0, v_b1, m16, cs16, v_a1, v_b2, m17, cs17, v_a2, v_b3, m18, cs18, v_a3,
      m19, m20, m21,
      ev_lt1, hne_lt1, ev_lt2, hne_lt2, ev_lt3, hne_lt3,
      op_m1, ev_ff1, ev_tb1, ev_x1, ev_x2, op_256x2, op_q1, op_64q1, op_r0,
      op_m2, ev_ff2, ev_tb2, ev_y1, ev_y2, op_256y2, op_q2, op_64q2, op_r1,
      op_m3, ev_ff3, ev_tb3, ev_z1, op_64q3, op_r2,
      op_a0, ev_b0, op_a1, ev_b1, op_a2, ev_b2, op_a3, ev_b3,
      he_r, hm_h, hm_19, hm_20, hm_21, hc_c⟩
  · -- 1-byte UTF-8 (`cp < 128`)
    obtain ⟨hlt1, rfl⟩ := Utf8Aux.ltf_one 128 (by omega) (by omega) rfl ev_lt1
    obtain ⟨_, hb0, rfl⟩ := u8_fromField_nat (by omega) ev_b0
    rw [Utf8Aux.utf8EncodeChar_eq, ite_eq_left (by omega), List.singleton_append, he_r]
    exact repByteStream_cons_of hb0 htail hm_h
  · -- 2-byte UTF-8 (`128 ≤ cp < 2048`)
    obtain ⟨hiff1, rfl⟩ := Utf8Aux.ltf_nat 128 (by omega) (by omega) rfl ev_lt1
    have hge1 : 128 ≤ ch.toNat := Nat.le_of_not_lt fun h => hne_lt1 (hiff1.mpr h)
    obtain ⟨hlt2, rfl⟩ := Utf8Aux.ltf_one 2048 (by omega) (by omega) rfl ev_lt2
    obtain ⟨c0, c1, c2, c3, rfl, rfl, rfl, rfl, rfl, rfl, hpack⟩ :=
      u32_fromField_4x (by omega) op_m1 ev_ff1 ev_tb1
    have hc0 := c0.toNat_lt; have hc1 := c1.toNat_lt; have hc2 := c2.toNat_lt; have hc3 := c3.toNat_lt
    have hq_eq : c1.toNat = ch.toNat / 64 := by omega
    obtain ⟨rfl, rfl⟩ := L1.u8_toField ev_x1
    have hm64 := PrimInt.field_mul_eq op_64q; subst hm64
    have hrem := PrimInt.field_sub_eq op_rem; subst hrem
    rw [cast_sub_mul64 (by omega)] at op_a1
    have ha0 := PrimInt.field_add_eq op_a0; subst ha0
    have ha1 := PrimInt.field_add_eq op_a1; subst ha1
    rw [show (c1.toNat : F) + 192 = ((c1.toNat + 192 : Nat) : F) by push_cast; ring] at ev_b0
    rw [show ((ch.toNat - 64 * c1.toNat : Nat) : F) + 128 = ((ch.toNat - 64 * c1.toNat + 128 : Nat) : F) by push_cast; ring] at ev_b1
    obtain ⟨_, hb0, rfl⟩ := u8_fromField_nat (by omega) ev_b0
    obtain ⟨_, hb1, rfl⟩ := u8_fromField_nat (by omega) ev_b1
    rw [Utf8Aux.utf8EncodeChar_eq, ite_eq_right (by omega), ite_eq_left (by omega),
      show ch.toNat / 64 % 32 + 192 = c1.toNat + 192 by omega,
      show ch.toNat % 64 + 128 = ch.toNat - 64 * c1.toNat + 128 by omega,
      List.cons_append, List.singleton_append, he_r]
    have htail1 := repByteStream_cons_of hb1 htail hm_8
    exact repByteStream_cons_of (repU8_heapMono₂ (PrimStrAux.ext_of_eq_snoc hm_8) hb0) htail1 hm_h
  · -- 3-byte UTF-8 (`2048 ≤ cp < 65536`)
    obtain ⟨hiff1, rfl⟩ := Utf8Aux.ltf_nat 128 (by omega) (by omega) rfl ev_lt1
    have hge1 : 128 ≤ ch.toNat := Nat.le_of_not_lt fun h => hne_lt1 (hiff1.mpr h)
    obtain ⟨hiff2, rfl⟩ := Utf8Aux.ltf_nat 2048 (by omega) (by omega) rfl ev_lt2
    have hge2 : 2048 ≤ ch.toNat := Nat.le_of_not_lt fun h => hne_lt2 (hiff2.mpr h)
    obtain ⟨hlt3, rfl⟩ := Utf8Aux.ltf_one 65536 (by omega) (by omega) rfl ev_lt3
    obtain ⟨c0, c1, c2, c3, rfl, rfl, rfl, rfl, rfl, rfl, hpack1⟩ :=
      u32_fromField_4x (by omega) op_m1 ev_ff1 ev_tb1
    have hc0 := c0.toNat_lt; have hc1 := c1.toNat_lt; have hc2 := c2.toNat_lt; have hc3 := c3.toNat_lt
    obtain ⟨rfl, rfl⟩ := L1.u8_toField ev_x1
    obtain ⟨rfl, rfl⟩ := L1.u8_toField ev_x2
    have hm256 := PrimInt.field_mul_eq op_256x2; subst hm256
    have hq1_f := PrimInt.field_add_eq op_q1; subst hq1_f
    have hq1_cast : (c1.toNat : F) + 256 * (c2.toNat : F) = ((c1.toNat + 256 * c2.toNat : Nat) : F) := by
      push_cast; ring
    have hq1_val : c1.toNat + 256 * c2.toNat = ch.toNat / 64 := by omega
    rw [hq1_cast, hq1_val] at op_64q1 op_m2 op_r1
    have hm64 := PrimInt.field_mul_eq op_64q1; subst hm64
    have hr0 := PrimInt.field_sub_eq op_r0; subst hr0
    rw [cast_sub_mul64 (by omega)] at op_a2
    obtain ⟨d0, d1, d2, d3, rfl, rfl, rfl, rfl, rfl, rfl, hpack2⟩ :=
      u32_fromField_4x (by omega) op_m2 ev_ff2 ev_tb2
    have hd0 := d0.toNat_lt; have hd1 := d1.toNat_lt; have hd2 := d2.toNat_lt; have hd3 := d3.toNat_lt
    have hq2_val : d1.toNat = ch.toNat / 4096 := by omega
    obtain ⟨rfl, rfl⟩ := L1.u8_toField ev_y1
    have hm64_2 := PrimInt.field_mul_eq op_64q2; subst hm64_2
    have hr1 := PrimInt.field_sub_eq op_r1; subst hr1
    rw [cast_sub_mul64 (by omega)] at op_a1
    have ha0 := PrimInt.field_add_eq op_a0; subst ha0
    have ha1 := PrimInt.field_add_eq op_a1; subst ha1
    have ha2 := PrimInt.field_add_eq op_a2; subst ha2
    rw [show (d1.toNat : F) + 224 = ((d1.toNat + 224 : Nat) : F) by push_cast; ring] at ev_b0
    rw [show ((ch.toNat / 64 - 64 * d1.toNat : Nat) : F) + 128 = ((ch.toNat / 64 - 64 * d1.toNat + 128 : Nat) : F) by push_cast; ring] at ev_b1
    rw [show ((ch.toNat - 64 * (ch.toNat / 64) : Nat) : F) + 128 = ((ch.toNat - 64 * (ch.toNat / 64) + 128 : Nat) : F) by push_cast; ring] at ev_b2
    obtain ⟨_, hb0, rfl⟩ := u8_fromField_nat (by omega) ev_b0
    obtain ⟨_, hb1, rfl⟩ := u8_fromField_nat (by omega) ev_b1
    obtain ⟨_, hb2, rfl⟩ := u8_fromField_nat (by omega) ev_b2
    rw [Utf8Aux.utf8EncodeChar_eq, ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left (by omega),
      show ch.toNat / 4096 % 16 + 224 = d1.toNat + 224 by omega,
      show ch.toNat / 64 % 64 + 128 = ch.toNat / 64 - 64 * d1.toNat + 128 by omega,
      show ch.toNat % 64 + 128 = ch.toNat - 64 * (ch.toNat / 64) + 128 by omega,
      List.cons_append, List.cons_append, List.singleton_append, he_r]
    have e15 := PrimStrAux.ext_of_eq_snoc hm_15
    have e14 := PrimStrAux.ext_of_eq_snoc hm_14
    have ht2 := repByteStream_cons_of hb2 htail hm_15
    have ht1 := repByteStream_cons_of (repU8_heapMono₂ e15 hb1) ht2 hm_14
    exact repByteStream_cons_of (repU8_heapMono₂ (e15.trans e14) hb0) ht1 hm_h
  · -- 4-byte UTF-8 (`65536 ≤ cp < 1114112`)
    obtain ⟨hiff1, rfl⟩ := Utf8Aux.ltf_nat 128 (by omega) (by omega) rfl ev_lt1
    have hge1 : 128 ≤ ch.toNat := Nat.le_of_not_lt fun h => hne_lt1 (hiff1.mpr h)
    obtain ⟨hiff2, rfl⟩ := Utf8Aux.ltf_nat 2048 (by omega) (by omega) rfl ev_lt2
    have hge2 : 2048 ≤ ch.toNat := Nat.le_of_not_lt fun h => hne_lt2 (hiff2.mpr h)
    obtain ⟨hiff3, rfl⟩ := Utf8Aux.ltf_nat 65536 (by omega) (by omega) rfl ev_lt3
    have hge3 : 65536 ≤ ch.toNat := Nat.le_of_not_lt fun h => hne_lt3 (hiff3.mpr h)
    -- Step 1: `q1 = cp / 64`, `r0 = cp % 64`
    obtain ⟨c0, c1, c2, c3, rfl, rfl, rfl, rfl, rfl, rfl, hpack1⟩ :=
      u32_fromField_4x (by omega) op_m1 ev_ff1 ev_tb1
    have hc0 := c0.toNat_lt; have hc1 := c1.toNat_lt; have hc2 := c2.toNat_lt; have hc3 := c3.toNat_lt
    obtain ⟨rfl, rfl⟩ := L1.u8_toField ev_x1
    obtain ⟨rfl, rfl⟩ := L1.u8_toField ev_x2
    have hm256 := PrimInt.field_mul_eq op_256x2; subst hm256
    have hq1_f := PrimInt.field_add_eq op_q1; subst hq1_f
    have hq1_cast : (c1.toNat : F) + 256 * (c2.toNat : F) = ((c1.toNat + 256 * c2.toNat : Nat) : F) := by
      push_cast; ring
    have hq1_val : c1.toNat + 256 * c2.toNat = ch.toNat / 64 := by omega
    rw [hq1_cast, hq1_val] at op_64q1 op_m2 op_r1
    have hm64 := PrimInt.field_mul_eq op_64q1; subst hm64
    have hr0 := PrimInt.field_sub_eq op_r0; subst hr0
    rw [cast_sub_mul64 (by omega)] at op_a3
    -- Step 2: `q2 = q1 / 64 = cp / 4096`, `r1 = q1 % 64`
    obtain ⟨d0, d1, d2, d3, rfl, rfl, rfl, rfl, rfl, rfl, hpack2⟩ :=
      u32_fromField_4x (by omega) op_m2 ev_ff2 ev_tb2
    have hd0 := d0.toNat_lt; have hd1 := d1.toNat_lt; have hd2 := d2.toNat_lt; have hd3 := d3.toNat_lt
    obtain ⟨rfl, rfl⟩ := L1.u8_toField ev_y1
    obtain ⟨rfl, rfl⟩ := L1.u8_toField ev_y2
    have hm256_2 := PrimInt.field_mul_eq op_256y2; subst hm256_2
    have hq2_f := PrimInt.field_add_eq op_q2; subst hq2_f
    have hq2_cast : (d1.toNat : F) + 256 * (d2.toNat : F) = ((d1.toNat + 256 * d2.toNat : Nat) : F) := by
      push_cast; ring
    have hq2_val : d1.toNat + 256 * d2.toNat = ch.toNat / 4096 := by omega
    rw [hq2_cast, hq2_val] at op_64q2 op_m3 op_r2
    have hm64_2 := PrimInt.field_mul_eq op_64q2; subst hm64_2
    have hr1 := PrimInt.field_sub_eq op_r1; subst hr1
    rw [cast_sub_mul64 (by omega)] at op_a2
    -- Step 3: `q3 = q2 / 64 = cp / 262144`, `r2 = q2 % 64`
    obtain ⟨e0, e1, e2, e3, rfl, rfl, rfl, rfl, rfl, rfl, hpack3⟩ :=
      u32_fromField_4x (by omega) op_m3 ev_ff3 ev_tb3
    have he0 := e0.toNat_lt; have he1 := e1.toNat_lt; have he2 := e2.toNat_lt; have he3 := e3.toNat_lt
    have hq3_val : e1.toNat = ch.toNat / 262144 := by omega
    obtain ⟨rfl, rfl⟩ := L1.u8_toField ev_z1
    have hm64_3 := PrimInt.field_mul_eq op_64q3; subst hm64_3
    have hr2 := PrimInt.field_sub_eq op_r2; subst hr2
    rw [cast_sub_mul64 (by omega)] at op_a1
    have ha0 := PrimInt.field_add_eq op_a0; subst ha0
    have ha1 := PrimInt.field_add_eq op_a1; subst ha1
    have ha2 := PrimInt.field_add_eq op_a2; subst ha2
    have ha3 := PrimInt.field_add_eq op_a3; subst ha3
    rw [show (e1.toNat : F) + 240 = ((e1.toNat + 240 : Nat) : F) by push_cast; ring] at ev_b0
    rw [show ((ch.toNat / 4096 - 64 * e1.toNat : Nat) : F) + 128 = ((ch.toNat / 4096 - 64 * e1.toNat + 128 : Nat) : F) by push_cast; ring] at ev_b1
    rw [show ((ch.toNat / 64 - 64 * (ch.toNat / 4096) : Nat) : F) + 128 = ((ch.toNat / 64 - 64 * (ch.toNat / 4096) + 128 : Nat) : F) by push_cast; ring] at ev_b2
    rw [show ((ch.toNat - 64 * (ch.toNat / 64) : Nat) : F) + 128 = ((ch.toNat - 64 * (ch.toNat / 64) + 128 : Nat) : F) by push_cast; ring] at ev_b3
    obtain ⟨_, hb0, rfl⟩ := u8_fromField_nat (by omega) ev_b0
    obtain ⟨_, hb1, rfl⟩ := u8_fromField_nat (by omega) ev_b1
    obtain ⟨_, hb2, rfl⟩ := u8_fromField_nat (by omega) ev_b2
    obtain ⟨_, hb3, rfl⟩ := u8_fromField_nat (by omega) ev_b3
    rw [Utf8Aux.utf8EncodeChar_eq, ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega),
      show ch.toNat / 262144 % 8 + 240 = e1.toNat + 240 by omega,
      show ch.toNat / 4096 % 64 + 128 = ch.toNat / 4096 - 64 * e1.toNat + 128 by omega,
      show ch.toNat / 64 % 64 + 128 = ch.toNat / 64 - 64 * (ch.toNat / 4096) + 128 by omega,
      show ch.toNat % 64 + 128 = ch.toNat - 64 * (ch.toNat / 64) + 128 by omega,
      List.cons_append, List.cons_append, List.cons_append, List.singleton_append, he_r]
    have e21 := PrimStrAux.ext_of_eq_snoc hm_21
    have e20 := PrimStrAux.ext_of_eq_snoc hm_20
    have e19 := PrimStrAux.ext_of_eq_snoc hm_19
    have ht3 := repByteStream_cons_of hb3 htail hm_21
    have ht2 := repByteStream_cons_of (repU8_heapMono₂ e21 hb2) ht3 hm_20
    have ht1 := repByteStream_cons_of (repU8_heapMono₂ (e21.trans e20) hb1) ht2 hm_19
    exact repByteStream_cons_of (repU8_heapMono₂ ((e21.trans e20).trans e19) hb0) ht1 hm_h

/-- `KernelNatPrim::klimbs_scalar_value(limbs)`. -/
theorem klimbs_scalar_value_step (c : ScopedCtx)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::klimbs_scalar_value" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.klimbs_scalar_value c args h r h' calls := by
  intro a hargs good n hn v hr
  subst hargs
  obtain ⟨limbs, hlimbs, rfl⟩ := hn
  rcases Obs.«KernelNatPrim::klimbs_scalar_value».obs ev with
    ⟨ld_nil, he_r, he_h, hc_c⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, he_r, _, _⟩ |
    ⟨x_rest, x_b0, x_b1, x_b2, x_b3, x_b4, x_b5, x_b6, x_b7, v_hi, m_hi, x_hi3, y_b7, m_b6,
      x_hi2, y_b6, m_b5, x_hi1, y_b5, m_b4, x_b3f, y_b4, m_b3, cs_b3, cs_b4, cs_b5, cs_b6, cs_b7,
      v_iz, m_iz, cs_iz, v_cp, x_lo1, y_b2s, x_b0f, y_b1s, m_b0, cs_b0, x_b1f, m_b1, cs_b1,
      x_b2f, m_b2, cs_b2, m_lt1, cs_lt1,
      ld_cons, ld_nil, ev_b3, ev_b4, op_h1, ev_b5, op_h2, ev_b6, op_h3, ev_b7, op_h4,
      ev_iz, hne_iz, ev_b0, ev_b1, op_b1s, op_lo1, ev_b2, op_b2s, op_cp, ev_lt1,
      he_r, he_h, hc_c⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he_r, _, _⟩ |
    ⟨x_rest, x_b0, x_b1, x_b2, x_b3, x_b4, x_b5, x_b6, x_b7, v_hi, m_hi, x_hi3, y_b7, m_b6,
      x_hi2, y_b6, m_b5, x_hi1, y_b5, m_b4, x_b3f, y_b4, m_b3, cs_b3, cs_b4, cs_b5, cs_b6, cs_b7,
      v_iz, m_iz, cs_iz, v_cp, x_lo1, y_b2s, x_b0f, y_b1s, m_b0, cs_b0, x_b1f, m_b1, cs_b1,
      x_b2f, m_b2, cs_b2, v_lt1, m_lt1, cs_lt1, v_lt2, m_lt2, cs_lt2, m_lt3, cs_lt3,
      ld_cons, ld_nil, ev_b3, ev_b4, op_h1, ev_b5, op_h2, ev_b6, op_h3, ev_b7, op_h4,
      ev_iz, hne_iz, ev_b0, ev_b1, op_b1s, op_lo1, ev_b2, op_b2s, op_cp,
      ev_lt1, hne_lt1, ev_lt2, hne_lt2, ev_lt3, he_r, he_h, hc_c⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he_r, _, _⟩ |
    ⟨_, _, _, _, _, _, he_r, _, _⟩
  · -- `Nil => (1, 0)`
    obtain rfl := RepList.nil_of_load hlimbs ld_nil
    obtain rfl : v = .field 0 := PrimNat.tag_snd (hr.symm.trans he_r)
    exact ⟨Char.ofNatAux 0 (.inl (by decide)), rfl, rfl, he_h⟩
  · exact absurd (hr.symm.trans he_r) PrimNat.tag_one_ne_zero
  · -- 1 limb, `cp < 55296`
    obtain ⟨w, rest, rfl, hw, hrest⟩ := RepList.cons_of_load hlimbs ld_cons
    obtain rfl := RepList.nil_of_load hrest ld_nil
    have hwn := w.toNat_lt
    have hwu : Value.tuple [x_b0, x_b1, x_b2, x_b3, x_b4, x_b5, x_b6, x_b7] =
        TagN.u64Value w.toNat := Lib.repU64_eq hw
    simp only [TagN.u64Value, Value.tuple.injEq, List.cons.injEq, and_true] at hwu
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hwu
    obtain ⟨rfl, rfl⟩ := L1.u8_toField ev_b3
    obtain ⟨rfl, rfl⟩ := L1.u8_toField ev_b4
    have hh1 := PrimInt.field_add_eq op_h1; subst hh1
    obtain ⟨rfl, rfl⟩ := L1.u8_toField ev_b5
    have hh2 := PrimInt.field_add_eq op_h2; subst hh2
    obtain ⟨rfl, rfl⟩ := L1.u8_toField ev_b6
    have hh3 := PrimInt.field_add_eq op_h3; subst hh3
    obtain ⟨rfl, rfl⟩ := L1.u8_toField ev_b7
    have hh4 := PrimInt.field_add_eq op_h4; subst hh4
    obtain ⟨hiz_r, rfl⟩ := Lib.is_zero_field ev_iz
    have hhi_zero :
        (((w.toNat / 16777216 % 256 : Nat) : F) +
          ((w.toNat / 4294967296 % 256 : Nat) : F) +
          ((w.toNat / 1099511627776 % 256 : Nat) : F) +
          ((w.toNat / 281474976710656 % 256 : Nat) : F) +
          ((w.toNat / 72057594037927936 % 256 : Nat) : F)) = 0 := by
      by_contra hne
      rw [ite_eq_right hne] at hiz_r
      exact hne_iz hiz_r
    have hhi_sum :
        w.toNat / 16777216 % 256 + w.toNat / 4294967296 % 256 +
        w.toNat / 1099511627776 % 256 + w.toNat / 281474976710656 % 256 +
        w.toNat / 72057594037927936 % 256 = 0 := by
      have hcast :
          (((w.toNat / 16777216 % 256 + w.toNat / 4294967296 % 256 +
            w.toNat / 1099511627776 % 256 + w.toNat / 281474976710656 % 256 +
            w.toNat / 72057594037927936 % 256 : Nat) : F)) = (0 : Nat) := by
        simpa [Nat.cast_add] using hhi_zero
      exact (NatAux.natCast_inj (by show _ < 18446744069414584321; omega) (by show _ < 18446744069414584321; omega)).mp hcast
    have hw_lt24 : w.toNat < 16777216 := u64_lt_24_of_hi_zero hwn hhi_sum
    obtain ⟨rfl, rfl⟩ := L1.u8_toField ev_b0
    obtain ⟨rfl, rfl⟩ := L1.u8_toField ev_b1
    have hb1s := PrimInt.field_mul_eq op_b1s; subst hb1s
    have hlo1 := PrimInt.field_add_eq op_lo1; subst hlo1
    obtain ⟨rfl, rfl⟩ := L1.u8_toField ev_b2
    have hb2s := PrimInt.field_mul_eq op_b2s; subst hb2s
    have hcp := PrimInt.field_add_eq op_cp; subst hcp
    have hcp_eq :
        ((w.toNat % 256 : Nat) : F) + ((w.toNat / 256 % 256 : Nat) : F) * 256 +
        ((w.toNat / 65536 % 256 : Nat) : F) * 65536 = (w.toNat : F) := by
      have hnat : w.toNat % 256 + w.toNat / 256 % 256 * 256 + w.toNat / 65536 % 256 * 65536 = w.toNat := by
        omega
      have hc := congrArg (fun k : Nat => (k : F)) hnat
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hc
    rw [hcp_eq] at ev_lt1 he_r
    obtain ⟨hlt, rfl⟩ := Utf8Aux.ltf_one 55296 (by omega) (by omega) rfl ev_lt1
    obtain rfl : v = .field (w.toNat : F) := PrimNat.tag_snd (hr.symm.trans he_r)
    have hlv : limbsVal [w] = w.toNat := by simp [limbsVal_cons, limbsVal_nil]
    rw [hlv]
    exact ⟨Char.ofNatAux w.toNat (.inl hlt), rfl, rfl, he_h⟩
  · exact absurd (hr.symm.trans he_r) PrimNat.tag_one_ne_zero
  · -- 1 limb, `57343 < cp < 1114112`
    obtain ⟨w, rest, rfl, hw, hrest⟩ := RepList.cons_of_load hlimbs ld_cons
    obtain rfl := RepList.nil_of_load hrest ld_nil
    have hwn := w.toNat_lt
    have hwu : Value.tuple [x_b0, x_b1, x_b2, x_b3, x_b4, x_b5, x_b6, x_b7] =
        TagN.u64Value w.toNat := Lib.repU64_eq hw
    simp only [TagN.u64Value, Value.tuple.injEq, List.cons.injEq, and_true] at hwu
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hwu
    obtain ⟨rfl, rfl⟩ := L1.u8_toField ev_b3
    obtain ⟨rfl, rfl⟩ := L1.u8_toField ev_b4
    have hh1 := PrimInt.field_add_eq op_h1; subst hh1
    obtain ⟨rfl, rfl⟩ := L1.u8_toField ev_b5
    have hh2 := PrimInt.field_add_eq op_h2; subst hh2
    obtain ⟨rfl, rfl⟩ := L1.u8_toField ev_b6
    have hh3 := PrimInt.field_add_eq op_h3; subst hh3
    obtain ⟨rfl, rfl⟩ := L1.u8_toField ev_b7
    have hh4 := PrimInt.field_add_eq op_h4; subst hh4
    obtain ⟨hiz_r, rfl⟩ := Lib.is_zero_field ev_iz
    have hhi_zero :
        (((w.toNat / 16777216 % 256 : Nat) : F) +
          ((w.toNat / 4294967296 % 256 : Nat) : F) +
          ((w.toNat / 1099511627776 % 256 : Nat) : F) +
          ((w.toNat / 281474976710656 % 256 : Nat) : F) +
          ((w.toNat / 72057594037927936 % 256 : Nat) : F)) = 0 := by
      by_contra hne
      rw [ite_eq_right hne] at hiz_r
      exact hne_iz hiz_r
    have hhi_sum :
        w.toNat / 16777216 % 256 + w.toNat / 4294967296 % 256 +
        w.toNat / 1099511627776 % 256 + w.toNat / 281474976710656 % 256 +
        w.toNat / 72057594037927936 % 256 = 0 := by
      have hcast :
          (((w.toNat / 16777216 % 256 + w.toNat / 4294967296 % 256 +
            w.toNat / 1099511627776 % 256 + w.toNat / 281474976710656 % 256 +
            w.toNat / 72057594037927936 % 256 : Nat) : F)) = (0 : Nat) := by
        simpa [Nat.cast_add] using hhi_zero
      exact (NatAux.natCast_inj (by show _ < 18446744069414584321; omega) (by show _ < 18446744069414584321; omega)).mp hcast
    have hw_lt24 : w.toNat < 16777216 := u64_lt_24_of_hi_zero hwn hhi_sum
    obtain ⟨rfl, rfl⟩ := L1.u8_toField ev_b0
    obtain ⟨rfl, rfl⟩ := L1.u8_toField ev_b1
    have hb1s := PrimInt.field_mul_eq op_b1s; subst hb1s
    have hlo1 := PrimInt.field_add_eq op_lo1; subst hlo1
    obtain ⟨rfl, rfl⟩ := L1.u8_toField ev_b2
    have hb2s := PrimInt.field_mul_eq op_b2s; subst hb2s
    have hcp := PrimInt.field_add_eq op_cp; subst hcp
    have hcp_eq :
        ((w.toNat % 256 : Nat) : F) + ((w.toNat / 256 % 256 : Nat) : F) * 256 +
        ((w.toNat / 65536 % 256 : Nat) : F) * 65536 = (w.toNat : F) := by
      have hnat : w.toNat % 256 + w.toNat / 256 % 256 * 256 + w.toNat / 65536 % 256 * 65536 = w.toNat := by
        omega
      have hc := congrArg (fun k : Nat => (k : F)) hnat
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hc
    rw [hcp_eq] at ev_lt1 ev_lt2 ev_lt3 he_r
    obtain ⟨_, rfl⟩ := Utf8Aux.ltf_nat 55296 (by omega) (by omega) rfl ev_lt1
    obtain ⟨_, _, hiff2, h01, rfl⟩ := Lib.less_than_fields_field ev_lt2
    have hv1 : v_lt2 = .field 1 := h01.resolve_left hne_lt2
    have hlt2 := hiff2.mp hv1
    rw [show (57343 : F) = ((57343 : Nat) : F) from rfl,
      NatAux.val_natCast (by show _ < 18446744069414584321; omega),
      NatAux.val_natCast (by show _ < 18446744069414584321; omega)] at hlt2
    have hge : 57343 < w.toNat := hlt2
    obtain ⟨hlt3, rfl⟩ := Utf8Aux.ltf_one 1114112 (by omega) (by omega) rfl ev_lt3
    obtain rfl : v = .field (w.toNat : F) := PrimNat.tag_snd (hr.symm.trans he_r)
    have hlv : limbsVal [w] = w.toNat := by simp [limbsVal_cons, limbsVal_nil]
    rw [hlv]
    exact ⟨Char.ofNatAux w.toNat (.inr ⟨by omega, hlt3⟩), rfl, rfl, he_h⟩
  · exact absurd (hr.symm.trans he_r) PrimNat.tag_one_ne_zero
  · exact absurd (hr.symm.trans he_r) PrimNat.tag_one_ne_zero

/-- `KernelNatPrim::lvls_is_zero1(lvls)`. -/
theorem lvls_is_zero1_step (c : ScopedCtx)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::lvls_is_zero1" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.lvls_is_zero1 c args h r h' calls := by
  intro lp hargs good us hus hr
  subst hargs
  obtain ⟨ls, hls, hEq⟩ := hus
  rcases Obs.«KernelNatPrim::lvls_is_zero1».obs ev with
    ⟨x_l0, x_rest, ld1, ld2, ld3, he_r, he_h, hc_c⟩ |
    ⟨_, _, _, _, _, _, _, he_r, _, _⟩ |
    ⟨_, _, _, _, _, _, he_r, _, _⟩ |
    ⟨_, _, _, he_r, _, _⟩
  · have ld1' : loadValue h lp =
        .ok (.construct IxVM.Refinement.KernelLevels.klevelListEnum "Cons" [x_l0, x_rest]) := by
      rw [← klevelListEnum_eq]; exact ld1
    have ld2' : loadValue h x_rest =
        .ok (.construct IxVM.Refinement.KernelLevels.klevelListEnum "Nil" []) := by
      rw [← klevelListEnum_eq]; exact ld2
    obtain ⟨l0, ls', rfl, hl0, hrest⟩ := RepList.cons_of_load hls ld1'
    obtain rfl := RepList.nil_of_load hrest ld2'
    obtain rfl := lv_zero_of_load hl0 ld3
    cases us with
    | nil =>
      have h0 := hEq (fun _ => 0)
      simp [Ix.Kernel.Level.EvalEqList] at h0
    | cons u us' =>
      cases us' with
      | nil =>
        refine ⟨⟨u, rfl, fun φ => ?_⟩, he_h⟩
        have h0 := hEq φ
        simpa [Ix.Kernel.Level.EvalEqList, Ix.Kernel.Level.eval] using h0
      | cons _ _ =>
        have h0 := hEq (fun _ => 0)
        simp [Ix.Kernel.Level.EvalEqList] at h0
  · exact absurd (hr.symm.trans he_r) field_one_ne_zero
  · exact absurd (hr.symm.trans he_r) field_one_ne_zero
  · exact absurd (hr.symm.trans he_r) field_one_ne_zero

/-- `KernelNatPrim::is_char_const(rc, e)`. -/
theorem is_char_const_step (c : ScopedCtx) (hc : ScopedCoreBase c)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::is_char_const" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.is_char_const c args h r h' calls := by
  intro rc e hargs good hrc d Γ E hE hr
  subst hargs
  rcases Obs.«KernelNatPrim::is_char_const».obs ev with
    ⟨x_caddr, x_clvls, x_ris, y_emp, m_ris, cs_ris, v_rc, m_rc, cs_rc, cs_emp,
      ld_e, ev_rc, ev_ris, ev_emp, op_mul, hc_c⟩ |
    ⟨_, _, _, he_r, _, _⟩
  · subst hc_c
    obtain ⟨ad, us, rfl, rad, hus⟩ := hE.const_of_load ld_e
    obtain ⟨rfl, rfl⟩ := ih.get (.roles .role_char) (by nat_lt_calls) ev_rc rfl
    have e1 := ObsFn.heap_extends ev_ris
    obtain ⟨rfl, rfl⟩ := ih.get (.nat .lvls_empty) (by nat_lt_calls) ev_emp x_clvls rfl
      (good.sub fun x hx => by simp [hx]) us (LvListRep.mono e1 hus)
    cases x_ris with
    | field fv =>
      have hm1 : fv * (if us = [] then (1 : F) else 0) = 1 :=
        Value.field.inj ((PrimInt.field_mul_eq op_mul).symm.trans hr)
      have hus_nil : us = [] := by
        by_contra hne
        rw [ite_eq_right hne, mul_zero] at hm1
        exact zero_ne_one hm1
      have hfv_ne : fv ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hm1; exact zero_ne_one hm1
      obtain ⟨haddr, hforce⟩ := ih.get (.roles .role_is) (by nat_lt_calls) ev_ris rc x_caddr ad .char
        rfl (good.sub fun x hx => by simp [hx]) hrc rad (fun h => hfv_ne (Value.field.inj h))
      have hk : c.κ (ixAddr ad) = .role .char :=
        (c.key_eq (by resolve_key)).trans (keyOf_of_addressOf hc.env.tableWf haddr)
      rw [hk, hus_nil]
    | _ => simp [evalBinOp] at op_mul
  · exact absurd (hr.symm.trans he_r) field_one_ne_zero

/-- `KernelNatPrim::is_char_const_or_whnf(rc, e, types)`. -/
theorem is_char_const_or_whnf_step (c : ScopedCtx)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::is_char_const_or_whnf" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.is_char_const_or_whnf c args h r h' calls := by
  intro rc e types hargs good hrc d Γ htypes E hE hr
  subst hargs
  rcases Obs.«KernelNatPrim::is_char_const_or_whnf».obs ev with
    ⟨m1, cs1, ev_icc, he_r, he_h, hc_c⟩ |
    ⟨v1, m1, cs1, cs2, v_w, m2, cs_w, ev_icc, hne, ev_w, ev_icc2, hc_c⟩
  · subst hc_c
    have heq := ih.get (.nat .is_char_const) (by nat_lt_calls) ev_icc rc e rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ E hE rfl
    rw [heq]; exact .refl
  · subst hc_c
    have e1 := ObsFn.heap_extends ev_icc
    obtain ⟨W, hW, hred⟩ := ih.get (.whnf .whnf) (by nat_lt_calls) ev_w rc e types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ (types_mono e1 htypes) E
      (Tm.mono e1 hE)
    have e2 := e1.trans (ObsFn.heap_extends ev_w)
    have heq := ih.get (.nat .is_char_const) (by nat_lt_calls) ev_icc2 rc v_w rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e2 hrc) d Γ W hW hr
    rw [heq] at hred
    exact hred

/-- `KernelNatPrim::char_lit_codepoint_syn(rc, e, types)`. -/
theorem char_lit_codepoint_syn_step (c : ScopedCtx) (hc : ScopedCoreBase c)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::char_lit_codepoint_syn" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.char_lit_codepoint_syn c args h r h' calls := by
  intro rc e types hargs good hrc d Γ htypes E hE v hr
  subst hargs
  rcases Obs.«KernelNatPrim::char_lit_codepoint_syn».obs ev with
    ⟨x_f, x_arg, x_caddr, x_clvls, m_emp, x_ris, y_emp, m_ris, cs_ris, v_rc, m_rc, cs_rc, cs_emp,
      m_nat, cs_nat, x_limbs, cs_sc,
      ld_e, ld_f, ev_rc, ev_ris, ev_emp, op_mul, ev_nat, ev_sc, hc_c⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he_r, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he_r, _, _⟩ |
    ⟨_, _, _, _, _, _, he_r, _, _⟩ |
    ⟨_, _, _, he_r, _, _⟩
  · subst hc_c
    obtain ⟨Ef, Ea, rfl, hEf, hEa⟩ := hE.app_of_load ld_e
    obtain ⟨ad, us, rfl, rad, hus⟩ := hEf.const_of_load ld_f
    obtain ⟨rfl, rfl⟩ := ih.get (.roles .role_char_of_nat) (by nat_lt_calls) ev_rc rfl
    have e1 := ObsFn.heap_extends ev_ris
    obtain ⟨rfl, rfl⟩ := ih.get (.nat .lvls_empty) (by nat_lt_calls) ev_emp x_clvls rfl
      (good.sub fun x hx => by simp [hx]) us (LvListRep.mono e1 hus)
    cases x_ris with
    | field fv =>
      have hm1 : fv * (if us = [] then (1 : F) else 0) = 1 :=
        Value.field.inj (PrimInt.field_mul_eq op_mul).symm
      have hus_nil : us = [] := by
        by_contra hne
        rw [ite_eq_right hne, mul_zero] at hm1
        exact zero_ne_one hm1
      have hfv_ne : fv ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hm1; exact zero_ne_one hm1
      obtain ⟨haddr, hforce⟩ := ih.get (.roles .role_is) (by nat_lt_calls) ev_ris rc x_caddr ad
        .charOfNat rfl (good.sub fun x hx => by simp [hx]) hrc rad (fun h => hfv_ne (Value.field.inj h))
      have hk : c.κ (ixAddr ad) = .role .charOfNat :=
        (c.key_eq (by resolve_key)).trans (keyOf_of_addressOf hc.env.tableWf haddr)
      obtain ⟨n, hn, hred_a⟩ := ih.get (.nat .try_extract_nat_or_whnf) (by nat_lt_calls) ev_nat
        rc x_arg types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ
        (types_mono e1 htypes) Ea (Tm.mono e1 hEa) x_limbs rfl
      obtain ⟨ch, hch, hv, _⟩ := ih.get (.nat .klimbs_scalar_value) (by nat_lt_calls) ev_sc
        x_limbs rfl (good.sub fun x hx => by simp [hx]) n (RepLimbsC.toRepLimbs hn) v hr
      rw [← hch] at hred_a
      rw [hk, hus_nil]
      exact ⟨ch, hv, .appArg hred_a⟩
    | _ => simp [evalBinOp] at op_mul
  · exact absurd (hr.symm.trans he_r) PrimNat.tag_one_ne_zero
  · exact absurd (hr.symm.trans he_r) PrimNat.tag_one_ne_zero
  · exact absurd (hr.symm.trans he_r) PrimNat.tag_one_ne_zero
  · exact absurd (hr.symm.trans he_r) PrimNat.tag_one_ne_zero

/-- `KernelNatPrim::char_lit_codepoint(rc, e, types)`. -/
theorem char_lit_codepoint_step (c : ScopedCtx)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::char_lit_codepoint" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.char_lit_codepoint c args h r h' calls := by
  intro rc e types hargs good hrc d Γ htypes E hE v hr
  subst hargs
  rcases Obs.«KernelNatPrim::char_lit_codepoint».obs ev with
    ⟨m1, cs1, x_cp, ev_syn, he_r, he_h, hc_c⟩ |
    ⟨v1, m1, cs1, cs2, v_w, m2, cs_w, ev_syn, ev_w, ev_syn2, hc_c⟩
  · subst hc_c he_h
    obtain rfl : v = x_cp := PrimNat.tag_snd (hr.symm.trans he_r)
    exact ih.get (.nat .char_lit_codepoint_syn) (by nat_lt_calls) ev_syn rc e types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes E hE v rfl
  · subst hc_c
    have e1 := ObsFn.heap_extends ev_syn
    obtain ⟨W, hW, hred⟩ := ih.get (.whnf .whnf) (by nat_lt_calls) ev_w rc e types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ (types_mono e1 htypes) E
      (Tm.mono e1 hE)
    have e2 := e1.trans (ObsFn.heap_extends ev_w)
    obtain ⟨ch, hv, hred2⟩ := ih.get (.nat .char_lit_codepoint_syn) (by nat_lt_calls) ev_syn2
      rc v_w types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e2 hrc) d Γ
      (types_mono e2 htypes) W hW v hr
    exact ⟨ch, hv, .trans hred hred2⟩

/-- `KernelNatPrim::match_char_list_head_syn(rc, e, types)`. -/
theorem match_char_list_head_syn_step (c : ScopedCtx) (hc : ScopedCoreBase c)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::match_char_list_head_syn" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.match_char_list_head_syn c args h r h' calls := by
  intro rc e types hargs good hrc hsup d Γ htypes E hE t x y hr
  subst hargs
  rcases Obs.«KernelNatPrim::match_char_list_head_syn».obs ev with
    ⟨x_f1, x_arg, x_caddr, x_clvls, m_lv, x_ris, y_lv, m_ris, cs_ris, v_rc, m_rc, cs_rc, cs_lv,
      m_ch, cs_ch, ld_e, ld_f1, ev_rc, ev_ris, ev_lv, op_mul, ev_ch, he_r, he_h, hc_c⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he_r, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he_r, _, _⟩ |
    ⟨x_f1, x_arg, x_f2, x_ch, x_head, x_ty, x_caddr, x_clvls, m_lv, x_ris, y_lv, m_ris, cs_ris,
      v_rc, m_rc, cs_rc, cs_lv, m_ch, cs_ch,
      ld_e, ld_f1, ld_f2, ld_hd, ev_rc, ev_ris, ev_lv, op_mul, ev_ch, he_r, he_h, hc_c⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      he_r, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he_r, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, he_r, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, he_r, _, _⟩ |
    ⟨_, _, _, _, _, _, _, he_r, _, _⟩ |
    ⟨_, _, _, he_r, _, _⟩
  · -- Tag 1: `List.nil.{u} Char`
    subst hc_c he_h
    obtain ⟨ht1, rfl, rfl⟩ := tag3_fst_eq (hr.symm.trans he_r)
    refine ⟨fun _ => ?_, fun ht2 => absurd (ht1.symm.trans ht2) (by decide)⟩
    obtain ⟨Ef, Ea, rfl, hEf, hEa⟩ := hE.app_of_load ld_e
    obtain ⟨ad, us, rfl, rad, hus⟩ := hEf.const_of_load ld_f1
    obtain ⟨rfl, rfl⟩ := ih.get (.roles .role_list_nil) (by nat_lt_calls) ev_rc rfl
    have e1 := ObsFn.heap_extends ev_ris
    have hmul_ok : ∃ fv lv : F, x_ris = .field fv ∧ y_lv = .field lv ∧ fv * lv = 1 := by
      cases x_ris <;> cases y_lv <;> simp [evalBinOp] at op_mul
      exact ⟨_, _, rfl, rfl, op_mul⟩
    obtain ⟨fv, lv, rfl, rfl, hmul1⟩ := hmul_ok
    have hlv_eq : lv = 1 := by
      -- `lvls_is_zero1` returns `0` or `1`; if `lv = 0` then `fv * 0 = 1`
      rcases Obs.«KernelNatPrim::lvls_is_zero1».obs ev_lv with
        ⟨_, _, _, _, _, h1, _, _⟩ | ⟨_, _, _, _, _, _, _, h0, _, _⟩ |
        ⟨_, _, _, _, _, _, h0, _, _⟩ | ⟨_, _, _, h0, _, _⟩
      · exact Value.field.inj h1
      · rw [Value.field.inj h0, mul_zero] at hmul1; exact absurd hmul1 zero_ne_one
      · rw [Value.field.inj h0, mul_zero] at hmul1; exact absurd hmul1 zero_ne_one
      · rw [Value.field.inj h0, mul_zero] at hmul1; exact absurd hmul1 zero_ne_one
    subst hlv_eq
    have hfv_ne : fv ≠ 0 := by intro h0; rw [h0, zero_mul] at hmul1; exact zero_ne_one hmul1
    obtain ⟨haddr, hforce⟩ := ih.get (.roles .role_is) (by nat_lt_calls) ev_ris rc x_caddr ad
      .listNil rfl (good.sub fun x hx => by simp [hx]) hrc rad (fun h => hfv_ne (Value.field.inj h))
    have hk : c.κ (ixAddr ad) = .role .listNil :=
      (c.key_eq (by resolve_key)).trans (keyOf_of_addressOf hc.env.tableWf haddr)
    obtain ⟨⟨u, rfl, hu⟩, rfl⟩ := ih.get (.nat .lvls_is_zero1) (by nat_lt_calls) ev_lv x_clvls rfl
      (good.sub fun x hx => by simp [hx]) us (LvListRep.mono e1 hus) rfl
    have hred_ty := ih.get (.nat .is_char_const_or_whnf) (by nat_lt_calls) ev_ch rc x_arg types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ (types_mono e1 htypes) Ea
      (Tm.mono e1 hEa) rfl
    obtain ⟨ci, hfind, hlp⟩ := listNil_info_of_strLit hsup
    rw [hk]
    exact .trans (.appFn (red_const_zero_level hfind hlp hu)) (.appArg hred_ty)
  · obtain ⟨ht0, _, _⟩ := tag3_fst_eq (hr.symm.trans he_r)
    exact ⟨fun h => absurd (ht0.symm.trans h) (by decide), fun h => absurd (ht0.symm.trans h) (by decide)⟩
  · obtain ⟨ht0, _, _⟩ := tag3_fst_eq (hr.symm.trans he_r)
    exact ⟨fun h => absurd (ht0.symm.trans h) (by decide), fun h => absurd (ht0.symm.trans h) (by decide)⟩
  · -- Tag 2: `List.cons.{u} Char ch tail`
    subst hc_c he_h
    obtain ⟨ht2, rfl, rfl⟩ := tag3_fst_eq (hr.symm.trans he_r)
    refine ⟨fun ht1 => absurd (ht2.symm.trans ht1) (by decide), fun _ => ?_⟩
    obtain ⟨Ef1, Etl, rfl, hEf1, hEtl⟩ := hE.app_of_load ld_e
    obtain ⟨Ef2, Ech, rfl, hEf2, hEch⟩ := hEf1.app_of_load ld_f1
    obtain ⟨Ehd, Ety, rfl, hEhd, hEty⟩ := hEf2.app_of_load ld_f2
    obtain ⟨ad, us, rfl, rad, hus⟩ := hEhd.const_of_load ld_hd
    obtain ⟨rfl, rfl⟩ := ih.get (.roles .role_list_cons) (by nat_lt_calls) ev_rc rfl
    have e1 := ObsFn.heap_extends ev_ris
    have hmul_ok : ∃ fv lv : F, x_ris = .field fv ∧ y_lv = .field lv ∧ fv * lv = 1 := by
      cases x_ris <;> cases y_lv <;> simp [evalBinOp] at op_mul
      exact ⟨_, _, rfl, rfl, op_mul⟩
    obtain ⟨fv, lv, rfl, rfl, hmul1⟩ := hmul_ok
    have hlv_eq : lv = 1 := by
      rcases Obs.«KernelNatPrim::lvls_is_zero1».obs ev_lv with
        ⟨_, _, _, _, _, h1, _, _⟩ | ⟨_, _, _, _, _, _, _, h0, _, _⟩ |
        ⟨_, _, _, _, _, _, h0, _, _⟩ | ⟨_, _, _, h0, _, _⟩
      · exact Value.field.inj h1
      · rw [Value.field.inj h0, mul_zero] at hmul1; exact absurd hmul1 zero_ne_one
      · rw [Value.field.inj h0, mul_zero] at hmul1; exact absurd hmul1 zero_ne_one
      · rw [Value.field.inj h0, mul_zero] at hmul1; exact absurd hmul1 zero_ne_one
    subst hlv_eq
    have hfv_ne : fv ≠ 0 := by intro h0; rw [h0, zero_mul] at hmul1; exact zero_ne_one hmul1
    obtain ⟨haddr, hforce⟩ := ih.get (.roles .role_is) (by nat_lt_calls) ev_ris rc x_caddr ad
      .listCons rfl (good.sub fun x hx => by simp [hx]) hrc rad (fun h => hfv_ne (Value.field.inj h))
    have hk : c.κ (ixAddr ad) = .role .listCons :=
      (c.key_eq (by resolve_key)).trans (keyOf_of_addressOf hc.env.tableWf haddr)
    obtain ⟨⟨u, rfl, hu⟩, rfl⟩ := ih.get (.nat .lvls_is_zero1) (by nat_lt_calls) ev_lv x_clvls rfl
      (good.sub fun x hx => by simp [hx]) us (LvListRep.mono e1 hus) rfl
    have hred_ty := ih.get (.nat .is_char_const_or_whnf) (by nat_lt_calls) ev_ch rc x_ty types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ (types_mono e1 htypes) Ety
      (Tm.mono e1 hEty) rfl
    have e2 := e1.trans (ObsFn.heap_extends ev_ch)
    obtain ⟨ci, hfind, hlp⟩ := listCons_info_of_strLit hsup
    refine ⟨Ech, Etl, Tm.mono e2 hEch, Tm.mono e2 hEtl, ?_⟩
    rw [hk]
    exact .appFn (.appFn (.trans (.appFn (red_const_zero_level hfind hlp hu)) (.appArg hred_ty)))
  · obtain ⟨ht0, _, _⟩ := tag3_fst_eq (hr.symm.trans he_r)
    exact ⟨fun h => absurd (ht0.symm.trans h) (by decide), fun h => absurd (ht0.symm.trans h) (by decide)⟩
  · obtain ⟨ht0, _, _⟩ := tag3_fst_eq (hr.symm.trans he_r)
    exact ⟨fun h => absurd (ht0.symm.trans h) (by decide), fun h => absurd (ht0.symm.trans h) (by decide)⟩
  · obtain ⟨ht0, _, _⟩ := tag3_fst_eq (hr.symm.trans he_r)
    exact ⟨fun h => absurd (ht0.symm.trans h) (by decide), fun h => absurd (ht0.symm.trans h) (by decide)⟩
  · obtain ⟨ht0, _, _⟩ := tag3_fst_eq (hr.symm.trans he_r)
    exact ⟨fun h => absurd (ht0.symm.trans h) (by decide), fun h => absurd (ht0.symm.trans h) (by decide)⟩
  · obtain ⟨ht0, _, _⟩ := tag3_fst_eq (hr.symm.trans he_r)
    exact ⟨fun h => absurd (ht0.symm.trans h) (by decide), fun h => absurd (ht0.symm.trans h) (by decide)⟩
  · obtain ⟨ht0, _, _⟩ := tag3_fst_eq (hr.symm.trans he_r)
    exact ⟨fun h => absurd (ht0.symm.trans h) (by decide), fun h => absurd (ht0.symm.trans h) (by decide)⟩

/-- Helper for `walk_char_list_bytes`'s head-match segment (`Seg_eneuiice`). -/
private theorem walk_head_seg (c : ScopedCtx) {calls : List (Call F)} (ih : IH c calls)
    (good : CoreGood c calls) {rc e types : SourceValue F} {h m : Heap F}
    {t : F} {x y : SourceValue F} {cs_seg : List (Call F)}
    (sg : Obs.«KernelNatPrim::walk_char_list_bytes».Seg_eneuiice rc e types h (.tuple [.field t, x, y]) m cs_seg)
    (hsub : ∀ z ∈ cs_seg, z ∈ calls) (hlt : cs_seg.length ≤ calls.length)
    (hrc : c.rc h rc) (hsup : Ix.Kernel.strLitSupported c.env = true)
    {d : Nat} {Γ : Nat → KExpr} (htypes : c.types Γ h d types) {E : KExpr} (hE : c.tm d Γ h E e) :
    Heap.Extends h m ∧
    (t = 1 → Red c.env d E (.app (.const Ix.Kernel.listNilName [.zero]) (.const Ix.Kernel.charName []))) ∧
    (t = 2 → ∃ Ch Tl, c.tm d Γ m Ch x ∧ c.tm d Γ m Tl y ∧
      Red c.env d E (.app (.app (.app (.const Ix.Kernel.listConsName [.zero]) (.const Ix.Kernel.charName [])) Ch) Tl)) := by
  cases sg with
  | n0_other_other m1 cs1 w1 w2 cs2 v_w m2 cs_w ev_syn ev_w ev_syn2 hc_seg =>
    subst hc_seg
    have e1 := ObsFn.heap_extends ev_syn
    obtain ⟨W, hW, hred⟩ := ih.get (.whnf .whnf) (by simp only [List.length_cons, List.length_append] at hlt; omega)
      ev_w rc e types rfl (good.sub fun z hz => hsub z (by simp [hz]))
      (RCRep.mono e1 hrc) d Γ (types_mono e1 htypes) E (Tm.mono e1 hE)
    have e2 := e1.trans (ObsFn.heap_extends ev_w)
    obtain ⟨h1, h2⟩ := ih.get (.nat .match_char_list_head_syn)
      (by simp only [List.length_cons, List.length_append] at hlt; omega)
      ev_syn2 rc v_w types rfl (good.sub fun z hz => hsub z (by simp [hz]))
      (RCRep.mono e2 hrc) hsup d Γ (types_mono e2 htypes) W hW t x y rfl
    refine ⟨e2.trans (ObsFn.heap_extends ev_syn2),
      fun ht1 => .trans hred (h1 ht1),
      fun ht2 => let ⟨Ch, Tl, hCh, hTl, hr2⟩ := h2 ht2; ⟨Ch, Tl, hCh, hTl, .trans hred hr2⟩⟩
  | bind_bind_bind m1 cs1 xt xx xy ev_syn he_r he_h hc_seg =>
    subst hc_seg he_h
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at he_r
    obtain ⟨rfl, rfl, rfl⟩ := he_r
    obtain ⟨h1, h2⟩ := ih.get (.nat .match_char_list_head_syn)
      (by simp only [List.length_cons, List.length_append] at hlt; omega)
      ev_syn rc e types rfl (good.sub fun z hz => hsub z (by simp [hz]))
      hrc hsup d Γ htypes E hE t x y rfl
    exact ⟨ObsFn.heap_extends ev_syn, h1, h2⟩

/-- `KernelNatPrim::walk_char_list_bytes(rc, list, types)`. -/
theorem walk_char_list_bytes_step (c : ScopedCtx)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::walk_char_list_bytes" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.walk_char_list_bytes c args h r h' calls := by
  intro rc e types hargs good hrc hsup d Γ htypes E hE bp hr
  subst hargs
  rcases Obs.«KernelNatPrim::walk_char_list_bytes».obs ev with
    ⟨m_seg, cs_seg, w1, w2, m_nil, sg, he_r, hm_nil, he_h, hc_c⟩ |
    ⟨m_seg, cs_seg, x_ch, x_tl, m_cp, cs_cp, x_cp, m_tl, cs_tl, x_tl_bs, v_bs, m_bs, cs_bs,
      sg, ev_cp, ev_tl, he_r, ev_enc, he_h, hc_c⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, he_r, _, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, he_r, _, _, _⟩ |
    ⟨_, _, _, _, _, he_r, _, _, _⟩
  · -- Nil list (`tag = 1`)
    subst hc_c he_h
    obtain rfl : bp = .ptr (.enum byteListEnum) m_seg.length := PrimNat.tag_snd (hr.symm.trans he_r)
    obtain ⟨_, hnil, _⟩ := walk_head_seg c ih good sg (fun _ hz => hz) (Nat.le_refl _) hrc hsup htypes hE
    exact ⟨[], repByteStream_nil_of hm_nil, hnil rfl⟩
  · -- Cons list (`tag = 2`)
    subst hc_c he_h
    obtain rfl : bp = v_bs := PrimNat.tag_snd (hr.symm.trans he_r)
    obtain ⟨e_seg, _, hcons⟩ := walk_head_seg c ih good sg
      (fun z hz => by simp [hz]) (by simp only [List.length_cons, List.length_append]; omega)
      hrc hsup htypes hE
    obtain ⟨Ch, Tl, hCh, hTl, hred_hd⟩ := hcons rfl
    obtain ⟨ch, rfl, hred_ch⟩ := ih.get (.nat .char_lit_codepoint) (by nat_lt_calls) ev_cp
      rc x_ch types rfl (good.sub fun z hz => by simp [hz])
      (RCRep.mono e_seg hrc) d Γ (types_mono e_seg htypes) Ch hCh x_cp rfl
    have e_cp := e_seg.trans (ObsFn.heap_extends ev_cp)
    obtain ⟨cs_tail, hbs_tail, hred_tl⟩ := ih.get (.nat .walk_char_list_bytes) (by nat_lt_calls)
      ev_tl rc x_tl types rfl (good.sub fun z hz => by simp [hz])
      (RCRep.mono e_cp hrc) hsup d Γ (types_mono e_cp htypes) Tl
      (Tm.mono (ObsFn.heap_extends ev_cp) hTl) x_tl_bs rfl
    have hbs := ih.get (.nat .utf8_encode_prepend) (by nat_lt_calls) ev_enc
      ch.toNat x_tl_bs rfl (good.sub fun z hz => by simp [hz]) ch rfl
      (cs_tail.flatMap String.utf8EncodeChar) hbs_tail
    refine ⟨ch :: cs_tail, by simpa [List.flatMap_cons] using hbs, ?_⟩
    exact .trans hred_hd (.trans (.appFn (.appArg hred_ch)) (.appArg hred_tl))
  · exact absurd (hr.symm.trans he_r) PrimNat.tag_one_ne_zero
  · exact absurd (hr.symm.trans he_r) PrimNat.tag_one_ne_zero
  · exact absurd (hr.symm.trans he_r) PrimNat.tag_one_ne_zero

/-- `KernelNatPrim::try_str_of_list(rc, a0, post, types)`. -/
theorem try_str_of_list_step (c : ScopedCtx)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::try_str_of_list" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.try_str_of_list c args h r h' calls := by
  intro rc a0 post types hargs good hrc hsup d Γ htypes A₀ Ps hA₀ hPs t x hr ht
  subst hargs
  rcases Obs.«KernelNatPrim::try_str_of_list».obs ev with
    ⟨m_w, cs_w, x_bs, m_lit, v_out, m_out, cs_app, ev_w, hm_lit, he_r, ev_app, he_h, hc_c⟩ |
    ⟨_, _, _, _, he_r, _, _⟩
  · subst hc_c he_h
    obtain rfl : x = v_out := PrimNat.tag_snd (hr.symm.trans he_r)
    obtain ⟨cs, hbs, hred_list⟩ := ih.get (.nat .walk_char_list_bytes) (by nat_lt_calls) ev_w
      rc a0 types rfl (good.sub fun z hz => by simp [hz]) hrc hsup d Γ htypes A₀ hA₀ x_bs rfl
    have e_w := ObsFn.heap_extends ev_w
    have e_lit := PrimStrAux.ext_of_eq_snoc hm_lit
    have hlit : c.tm d Γ m_lit (.lit (.strVal (String.ofList cs)))
        (.ptr (.enum kexprEnum) m_w.length) := by
      rw [hm_lit]
      exact .litStr List.getElem?_concat_length
        (Bytes.repByteStream_heapMono₂ _ (Heap.Extends.snoc _ _) hbs)
        (Utf8Aux.strBytes_ofList cs)
    have happ := ih.get (.nat .np_apply_spine) (by nat_lt_calls) ev_app _ post rfl
      (good.sub fun z hz => by simp [hz]) d Γ (.lit (.strVal (String.ofList cs))) Ps
      hlit (TmL.mono (e_w.trans e_lit) hPs)
    refine ⟨Ix.Kernel.Expr.mkAppN (.lit (.strVal (String.ofList cs))) Ps, happ, ?_⟩
    have h1 : Red c.env d
        (.app (.const Ix.Kernel.stringOfListName []) A₀)
        (.lit (.strVal (String.ofList cs))) := by
      have hfold : Red c.env d (Ix.Kernel.strLitToConstructor (md := .anon) (String.ofList cs))
          (.lit (.strVal (String.ofList cs))) := .strLitFold hsup
      rw [Utf8Aux.strLitToConstructor_ofList] at hfold
      exact .trans (.appArg hred_list) hfold
    exact PrimNat.red_mkAppN₁ Ps h1
  · exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht

/-- `KernelNatPrim::try_str_utf8_byte_size(rc, a0, post, types)`. -/
theorem try_str_utf8_byte_size_step (c : ScopedCtx)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::try_str_utf8_byte_size" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.try_str_utf8_byte_size c args h r h' calls := by
  intro rc a0 post types hargs good hrc hprim d Γ htypes A₀ Ps hA₀ hPs t x hr ht
  subst hargs
  rcases Obs.«KernelNatPrim::try_str_utf8_byte_size».obs ev with
    ⟨v_w, m_w, cs_w, x_bs, v_lit, m_lit, cs_lit, v_limbs, m_limbs, cs_limbs, v_len, m_len, cs_len,
      v_out, m_out, cs_app, ev_w, ld_w, ev_len, ev_kfg, ev_lit, he_r, ev_app, he_h, hc_c⟩ |
    ⟨_, _, _, _, _, _, _, he_r, _, _⟩ |
    ⟨_, _, _, _, _, _, _, he_r, _, _⟩
  · subst hc_c he_h
    obtain rfl : x = v_out := PrimNat.tag_snd (hr.symm.trans he_r)
    obtain ⟨W, hW, hred0⟩ := ih.get (.whnf .whnf) (by nat_lt_calls) ev_w rc a0 types rfl
      (good.sub fun z hz => by simp [hz]) hrc d Γ htypes A₀ hA₀
    rcases hW.lit_of_load ld_w with ⟨_, _, hx, -⟩ | ⟨bp, bs, s, hx, hbs, hs, rfl⟩
    · injection hx with _ hne _; exact absurd hne (by decide)
    · injection hx with _ _ hx'; injection hx' with hbp; subst hbp
      have e_w := ObsFn.heap_extends ev_w
      obtain ⟨rfl, rfl⟩ := bl_length ev_len hbs
      have hlen_lt : bs.length < 2 ^ 39 :=
        RomBound.bounded_length_lt good.2
          (c := ⟨Obs.Names.«Lists::length<Field>», [x_bs], m_len⟩) (by simp) (by simp) hbs
      have hval_len : ZMod.val (bs.length : F) = bs.length :=
        NatAux.val_natCast (by show _ < 18446744069414584321; omega)
      obtain ⟨_, hlimbs⟩ := ih.get (.nat .klimbs_from_g) (by nat_lt_calls) ev_kfg (bs.length : F) rfl
        (good.sub fun z hz => by simp [hz])
      rw [hval_len, strBytes_length_eq hs] at hlimbs
      have hlit := ih.get (.nat .mk_nat_lit) (by nat_lt_calls) ev_lit v_limbs rfl
        (good.sub fun z hz => by simp [hz]) s.utf8ByteSize hlimbs
      have e_lit := e_w.trans ((ObsFn.heap_extends ev_kfg).trans (ObsFn.heap_extends ev_lit))
      have happ := ih.get (.nat .np_apply_spine) (by nat_lt_calls) ev_app v_lit post rfl
        (good.sub fun z hz => by simp [hz]) d Γ (Specs.Nat.natLit s.utf8ByteSize) Ps
        (hlit d Γ) (TmL.mono e_lit hPs)
      refine ⟨Ix.Kernel.Expr.mkAppN (.lit (.natVal s.utf8ByteSize)) Ps, happ, ?_⟩
      exact PrimNat.red_mkAppN₁ Ps (.trans (.appArg hred0) (hprim.strUtf8ByteSize d s))
  · exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht
  · exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht

/-- `KernelNatPrim::try_str_back(rc, a0, post, types)`. -/
theorem try_str_back_step (c : ScopedCtx) (hc : ScopedCoreBase c)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::try_str_back" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.try_str_back c args h r h' calls := by
  intro rc a0 post types hargs good hrc hprim d Γ htypes A₀ Ps hA₀ hPs t x hr ht
  subst hargs
  rcases Obs.«KernelNatPrim::try_str_back».obs ev with
    ⟨v_w, m_w, cs_w, x_bs, v_cp, m_cp, cs_cp, v_lit, m_lit, cs_lit, v_limbs, m_limbs, cs_limbs,
      m_const, v_addr, m_addr, cs_addr, v_rc, m_rc, cs_rc, m_nil, v_out, m_out, cs_app, m_app,
      ev_w, ld_w, ev_cp, ev_kfg, ev_lit, hm_const, ev_rc, ev_addr, hm_nil, he_r, hm_app,
      ev_app, he_h, hc_c⟩ |
    ⟨_, _, _, _, _, _, _, he_r, _, _⟩ |
    ⟨_, _, _, _, _, _, _, he_r, _, _⟩
  · subst hc_c he_h
    obtain rfl : x = v_out := PrimNat.tag_snd (hr.symm.trans he_r)
    obtain ⟨W, hW, hred0⟩ := ih.get (.whnf .whnf) (by nat_lt_calls) ev_w rc a0 types rfl
      (good.sub fun z hz => by simp [hz]) hrc d Γ htypes A₀ hA₀
    rcases hW.lit_of_load ld_w with ⟨_, _, hx, -⟩ | ⟨bp, bs, s, hx, hbs, hs, rfl⟩
    · injection hx with _ hne _; exact absurd hne (by decide)
    · injection hx with _ _ hx'; injection hx' with hbp; subst hbp
      have e_w := ObsFn.heap_extends ev_w
      have hcp := ih.get (.nat .utf8_last_codepoint) (by nat_lt_calls) ev_cp x_bs rfl
        (good.sub fun z hz => by simp [hz]) bs s hbs hs
      subst hcp
      have e_cp := ObsFn.heap_extends ev_cp
      obtain ⟨_, hlimbs⟩ := ih.get (.nat .klimbs_from_g) (by nat_lt_calls) ev_kfg
        ((s.toList.getLastD 'A').toNat : F) rfl (good.sub fun z hz => by simp [hz])
      have hclt := Utf8Aux.char_toNat_lt (s.toList.getLastD 'A')
      rw [NatAux.val_natCast (by show _ < 18446744069414584321; omega)] at hlimbs
      have hlit := ih.get (.nat .mk_nat_lit) (by nat_lt_calls) ev_lit v_limbs rfl
        (good.sub fun z hz => by simp [hz]) (s.toList.getLastD 'A').toNat hlimbs
      have e_lit := (e_w.trans e_cp).trans ((ObsFn.heap_extends ev_kfg).trans (ObsFn.heap_extends ev_lit))
      obtain ⟨rfl, rfl⟩ := ih.get (.roles .role_char_of_nat) (by nat_lt_calls) ev_rc rfl
      obtain ⟨ad, rad, haddr, _⟩ := ih.get (.roles .role_used_implicitly) (by nat_lt_calls) ev_addr
        rc .charOfNat rfl (good.sub fun z hz => by simp [hz]) (RCRep.mono e_lit hrc)
      have hres := key_res_of_stored hc haddr hprim.charOfNatStored
      have hcon := PrimStrAux.tmc_role_const_nil hc rad haddr hres hm_nil hm_const
      have e_con := ((ObsFn.heap_extends ev_addr).trans (PrimStrAux.ext_of_eq_snoc hm_nil)).trans
        (PrimStrAux.ext_of_eq_snoc hm_const)
      have happ0 : c.tm d Γ m_app
          (.app (.const (.role .charOfNat) []) (.lit (.natVal (s.toList.getLastD 'A').toNat)))
          (.ptr (.enum kexprEnum) m_const.length) :=
        PrimStrAux.tm_store_app' hm_app (hcon d Γ) (Tm.mono e_con (hlit d Γ))
      have e_all := (e_lit.trans e_con).trans (PrimStrAux.ext_of_eq_snoc hm_app)
      have happ := ih.get (.nat .np_apply_spine) (by nat_lt_calls) ev_app _ post rfl
        (good.sub fun z hz => by simp [hz]) d Γ _ Ps happ0 (TmL.mono e_all hPs)
      refine ⟨_, happ, ?_⟩
      exact PrimNat.red_mkAppN₁ Ps (.trans (.appArg hred0) (hprim.strBack d s))
  · exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht
  · exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht

/-- `KernelNatPrim::try_str_to_byte_array(rc, a0, post, types)`. -/
theorem try_str_to_byte_array_step (c : ScopedCtx) (hc : ScopedCoreBase c)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::try_str_to_byte_array" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.try_str_to_byte_array c args h r h' calls := by
  intro rc a0 post types hargs good hrc hprim d Γ htypes A₀ Ps hA₀ hPs t x hr ht
  subst hargs
  rcases Obs.«KernelNatPrim::try_str_to_byte_array».obs ev with
    ⟨v_w, m_w, cs_w, x_bs, m_const, v_addr, m_addr, cs_addr, v_rc, m_rc, cs_rc, m_nil,
      v_out, m_out, cs_app, ev_w, ld_w, ld_nil, hm_const, ev_rc, ev_addr, hm_nil,
      he_r, ev_app, he_h, hc_c⟩ |
    ⟨_, _, _, _, _, _, _, _, _, he_r, _, _⟩ |
    ⟨_, _, _, _, _, _, _, he_r, _, _⟩ |
    ⟨_, _, _, _, _, _, _, he_r, _, _⟩
  · subst hc_c he_h
    obtain rfl : x = v_out := PrimNat.tag_snd (hr.symm.trans he_r)
    obtain ⟨W, hW, hred0⟩ := ih.get (.whnf .whnf) (by nat_lt_calls) ev_w rc a0 types rfl
      (good.sub fun z hz => by simp [hz]) hrc d Γ htypes A₀ hA₀
    rcases hW.lit_of_load ld_w with ⟨_, _, hx, -⟩ | ⟨bp, bs, s, hx, hbs, hs, rfl⟩
    · injection hx with _ hne _; exact absurd hne (by decide)
    · injection hx with _ _ hx'; injection hx' with hbp; subst hbp
      obtain rfl := RepList.nil_of_load hbs ld_nil
      obtain rfl := strBytes_nil_eq_empty hs
      have e_w := ObsFn.heap_extends ev_w
      obtain ⟨rfl, rfl, _⟩ := Obs.«KernelRoleSpec::role_byte_array_empty».obs ev_rc
      obtain ⟨ad, rad, haddr, _⟩ := ih.get (.roles .role_used_implicitly) (by nat_lt_calls) ev_addr
        rc .byteArrayEmpty rfl (good.sub fun z hz => by simp [hz]) (RCRep.mono e_w hrc)
      have hres := key_res_of_stored hc haddr hprim.byteArrayEmptyStored
      have hcon := PrimStrAux.tmc_role_const_nil hc rad haddr hres hm_nil hm_const
      have e_all := (e_w.trans (ObsFn.heap_extends ev_addr)).trans
        ((PrimStrAux.ext_of_eq_snoc hm_nil).trans (PrimStrAux.ext_of_eq_snoc hm_const))
      have happ := ih.get (.nat .np_apply_spine) (by nat_lt_calls) ev_app _ post rfl
        (good.sub fun z hz => by simp [hz]) d Γ (.const (.role .byteArrayEmpty) []) Ps
        (hcon d Γ) (TmL.mono e_all hPs)
      refine ⟨_, happ, ?_⟩
      exact PrimNat.red_mkAppN₁ Ps (.trans (.appArg hred0) (hprim.strToByteArrayEmpty d))
  · exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht
  · exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht
  · exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht

/-- `KernelNatPrim::try_str_dec_eq(rc, a0, a1, post, types)`. -/
theorem try_str_dec_eq_step (c : ScopedCtx) (hc : ScopedCoreBase c)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::try_str_dec_eq" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.try_str_dec_eq c args h r h' calls := by
  intro rc a0 a1 post types hargs good hrc hprim d Γ htypes A₀ A₁ Ps hA₀ hA₁ hPs t x hr ht
  subst hargs
  rcases Obs.«KernelNatPrim::try_str_dec_eq».obs ev with
    ⟨v_w0, m_w0, cs_w0, x_sa, v_w1, m_w1, cs_w1, x_sb, m_eq, cs_eq,
      m_l1c, m_l1s, m_l1z, m_l1n, m_str, v_astr, m_astr, cs_astr, v_rstr, m_rstr, cs_rstr, m_snil,
      m_eqc, v_aeq, m_aeq, cs_aeq, v_req, m_req, cs_req,
      m_reflc, v_arefl, m_arefl, cs_arefl, v_rrefl, m_rrefl, cs_rrefl,
      m_itc, v_ait, m_ait, cs_ait, v_rit, m_rit, cs_rit, m_itnil,
      m_eq2, m_eq1, m_eq0, m_rf1, m_rf0, m_res, m_it0, v_out, m_out, cs_app,
      ev_w0, ld_w0, ev_w1, ld_w1, ev_beq,
      hm_l1c, hm_l1s, hm_l1z, hm_l1n,
      hm_str, ev_rstr, ev_astr, hm_snil,
      hm_eqc, ev_req, ev_aeq,
      hm_reflc, ev_rrefl, ev_arefl,
      hm_itc, ev_rit, ev_ait, hm_itnil,
      hm_eq2, hm_eq1, hm_eq0, hm_rf1, hm_rf0, hm_res, hm_it0,
      he_r, ev_app, he_h, hc_c⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he_r, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, he_r, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, he_r, _, _⟩ |
    ⟨_, _, _, _, _, _, _, he_r, _, _⟩ |
    ⟨_, _, _, _, _, _, _, he_r, _, _⟩
  · subst hc_c he_h
    obtain rfl : x = v_out := PrimNat.tag_snd (hr.symm.trans he_r)
    obtain ⟨W₀, hW₀, hred0⟩ := ih.get (.whnf .whnf) (by nat_lt_calls) ev_w0 rc a0 types rfl
      (good.sub fun z hz => by simp [hz]) hrc d Γ htypes A₀ hA₀
    rcases hW₀.lit_of_load ld_w0 with ⟨_, _, hx0, -⟩ | ⟨bp0, bs0, s0, hx0, hbs0, hs0, rfl⟩
    · injection hx0 with _ hne _; exact absurd hne (by decide)
    · injection hx0 with _ _ hx0'; injection hx0' with hbp0; subst hbp0
      have e_w0 := ObsFn.heap_extends ev_w0
      obtain ⟨W₁, hW₁, hred1⟩ := ih.get (.whnf .whnf) (by nat_lt_calls) ev_w1 rc a1 types rfl
        (good.sub fun z hz => by simp [hz]) (RCRep.mono e_w0 hrc) d Γ (types_mono e_w0 htypes)
        A₁ (Tm.mono e_w0 hA₁)
      rcases hW₁.lit_of_load ld_w1 with ⟨_, _, hx1, -⟩ | ⟨bp1, bs1, s1, hx1, hbs1, hs1, rfl⟩
      · injection hx1 with _ hne _; exact absurd hne (by decide)
      · injection hx1 with _ _ hx1'; injection hx1' with hbp1; subst hbp1
        have e_w1 := ObsFn.heap_extends ev_w1
        have hbs0' := Bytes.repByteStream_heapMono₂ _ e_w1 hbs0
        obtain ⟨hbeq, rfl⟩ := ih.get (.levels .bytestream_eq) (by nat_lt_calls) ev_beq x_sa x_sb rfl
          (good.sub fun z hz => by simp [hz]) bs0 bs1 hbs0' hbs1
        have hbs_eq : bs0 = bs1 := by
          by_contra hne; rw [ite_eq_right hne] at hbeq; exact field_one_ne_zero hbeq
        subst hbs_eq
        obtain rfl : s0 = s1 := strBytes_inj hs0 hs1
        -- Level list `[.succ .zero]`
        have hlvl1 := repKLevelList_one_of hm_l1z hm_l1s hm_l1n hm_l1c
        have e_l1 : Heap.Extends m_eq m_l1c :=
          ((PrimStrAux.ext_of_eq_snoc hm_l1z).trans (PrimStrAux.ext_of_eq_snoc hm_l1s)).trans
            ((PrimStrAux.ext_of_eq_snoc hm_l1n).trans (PrimStrAux.ext_of_eq_snoc hm_l1c))
        -- `String` constant
        obtain ⟨rfl, rfl⟩ := ih.get (.roles .role_string) (by nat_lt_calls) ev_rstr rfl
        have E_l1 := (e_w0.trans e_w1).trans e_l1
        obtain ⟨aS, raS, hbS, _⟩ := ih.get (.roles .role_used_implicitly) (by nat_lt_calls) ev_astr
          rc .string rfl (good.sub fun z hz => by simp [hz]) (RCRep.mono E_l1 hrc)
        have hStr := PrimStrAux.tmc_role_const_nil hc raS hbS
          (key_res_of_stored hc hbS hprim.stringStored) hm_snil hm_str
        have e_str := ((ObsFn.heap_extends ev_astr).trans (PrimStrAux.ext_of_eq_snoc hm_snil)).trans
          (PrimStrAux.ext_of_eq_snoc hm_str)
        -- `Eq.{1}` constant
        obtain ⟨rfl, rfl, _⟩ := Obs.«KernelRoleSpec::role_eq».obs ev_req
        have E_str := E_l1.trans e_str
        obtain ⟨aEq, raEq, hbEq, _⟩ := ih.get (.roles .role_used_implicitly) (by nat_lt_calls) ev_aeq
          rc .eq rfl (good.sub fun z hz => by simp [hz]) (RCRep.mono E_str hrc)
        have e_aeq := ObsFn.heap_extends ev_aeq
        have hEqC := PrimStrAux.tmc_role_const hc raEq hbEq
          (key_res_of_stored hc hbEq hprim.eqStored) (hlvl1.mono (e_str.trans e_aeq)) hm_eqc
        have e_eqc := e_aeq.trans (PrimStrAux.ext_of_eq_snoc hm_eqc)
        -- `Eq.refl.{1}` constant
        obtain ⟨rfl, rfl, _⟩ := Obs.«KernelRoleSpec::role_eq_refl».obs ev_rrefl
        have E_eqc := E_str.trans e_eqc
        obtain ⟨aRf, raRf, hbRf, _⟩ := ih.get (.roles .role_used_implicitly) (by nat_lt_calls) ev_arefl
          rc .eqRefl rfl (good.sub fun z hz => by simp [hz]) (RCRep.mono E_eqc hrc)
        have e_arefl := ObsFn.heap_extends ev_arefl
        have hReflC := PrimStrAux.tmc_role_const hc raRf hbRf
          (key_res_of_stored hc hbRf hprim.eqReflStored)
          (hlvl1.mono ((e_str.trans e_eqc).trans e_arefl)) hm_reflc
        have e_reflc := e_arefl.trans (PrimStrAux.ext_of_eq_snoc hm_reflc)
        -- `Decidable.isTrue` constant
        obtain ⟨rfl, rfl, _⟩ := Obs.«KernelRoleSpec::role_decidable_is_true».obs ev_rit
        have E_reflc := E_eqc.trans e_reflc
        obtain ⟨aIt, raIt, hbIt, _⟩ := ih.get (.roles .role_used_implicitly) (by nat_lt_calls) ev_ait
          rc .decidableIsTrue rfl (good.sub fun z hz => by simp [hz]) (RCRep.mono E_reflc hrc)
        have hItC := PrimStrAux.tmc_role_const_nil hc raIt hbIt
          (key_res_of_stored hc hbIt hprim.decidableIsTrueStored) hm_itnil hm_itc
        have e_itc := ((ObsFn.heap_extends ev_ait).trans (PrimStrAux.ext_of_eq_snoc hm_itnil)).trans
          (PrimStrAux.ext_of_eq_snoc hm_itc)
        -- Build applications
        have e_s0_itc : Heap.Extends m_w0 m_itc :=
          (((e_w1.trans e_l1).trans e_str).trans e_eqc).trans (e_reflc.trans e_itc)
        have hStr_itc : c.tm d Γ m_itc (.const (.role .string) []) (.ptr (.enum kexprEnum) m_snil.length) :=
          Tm.mono (e_eqc.trans (e_reflc.trans e_itc)) (hStr d Γ)
        have hEq_itc : c.tm d Γ m_itc (.const (.role .eq) [.succ .zero]) (.ptr (.enum kexprEnum) m_aeq.length) :=
          Tm.mono (e_reflc.trans e_itc) (hEqC d Γ)
        have hRf_itc : c.tm d Γ m_itc (.const (.role .eqRefl) [.succ .zero]) (.ptr (.enum kexprEnum) m_arefl.length) :=
          Tm.mono e_itc (hReflC d Γ)
        have hW0_itc : c.tm d Γ m_itc (.lit (.strVal s0)) v_w0 := Tm.mono e_s0_itc hW₀
        have e_eq0 := PrimStrAux.ext_of_eq_snoc hm_eq0
        have e_eq1 := PrimStrAux.ext_of_eq_snoc hm_eq1
        have e_eq2 := PrimStrAux.ext_of_eq_snoc hm_eq2
        have e_rf0 := PrimStrAux.ext_of_eq_snoc hm_rf0
        have e_rf1 := PrimStrAux.ext_of_eq_snoc hm_rf1
        have e_it0 := PrimStrAux.ext_of_eq_snoc hm_it0
        have e_res := PrimStrAux.ext_of_eq_snoc hm_res
        have h_eq0 := PrimStrAux.tm_store_app' hm_eq0 hEq_itc hStr_itc
        have h_eq1 := PrimStrAux.tm_store_app' hm_eq1 h_eq0 (Tm.mono e_eq0 hW0_itc)
        have h_eq2 := PrimStrAux.tm_store_app' hm_eq2 h_eq1 (Tm.mono (e_eq0.trans e_eq1) hW0_itc)
        have e_itc_eq2 := (e_eq0.trans e_eq1).trans e_eq2
        have h_rf0 := PrimStrAux.tm_store_app' hm_rf0
          (Tm.mono e_itc_eq2 hRf_itc) (Tm.mono e_itc_eq2 hStr_itc)
        have h_rf1 := PrimStrAux.tm_store_app' hm_rf1 h_rf0
          (Tm.mono (e_itc_eq2.trans e_rf0) hW0_itc)
        have e_itc_rf1 := (e_itc_eq2.trans e_rf0).trans e_rf1
        have h_it0 := PrimStrAux.tm_store_app' hm_it0
          (Tm.mono e_itc_rf1 (hItC d Γ)) (Tm.mono (e_rf0.trans e_rf1) h_eq2)
        have h_res := PrimStrAux.tm_store_app' hm_res h_it0 (Tm.mono e_it0 h_rf1)
        have e_all := (e_w0.trans e_s0_itc).trans ((e_itc_rf1.trans e_it0).trans e_res)
        have happ := ih.get (.nat .np_apply_spine) (by nat_lt_calls) ev_app _ post rfl
          (good.sub fun z hz => by simp [hz]) d Γ _ Ps h_res (TmL.mono e_all hPs)
        refine ⟨_, happ, ?_⟩
        have h2 : Red c.env d (.app (.app (.const (.role .stringDecEq) []) A₀) A₁) _ :=
          .trans (.appFn (.appArg hred0)) (.trans (.appArg hred1) (hprim.strDecEqRefl d s0))
        exact PrimNat.red_mkAppN₂ Ps h2
  · exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht
  · exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht
  · exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht
  · exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht
  · exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht

/-- `KernelNatPrim::try_str_append(rc, a0, a1, post, types)`. -/
theorem try_str_append_step (c : ScopedCtx)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::try_str_append" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.try_str_append c args h r h' calls := by
  intro rc a0 a1 post types hargs good hrc hprim d Γ htypes A₀ A₁ Ps hA₀ hA₁ hPs t x hr ht
  subst hargs
  rcases Obs.«KernelNatPrim::try_str_append».obs ev with
    ⟨v_w0, m_w0, cs_w0, x_sa, v_w1, m_w1, cs_w1, x_sb, v_cat, m_cat, cs_cat, m_lit,
      v_out, m_out, cs_app, ev_w0, ld_w0, ev_w1, ld_w1, ev_cat, hm_lit, he_r, ev_app, he_h, hc_c⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, he_r, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, he_r, _, _⟩ |
    ⟨_, _, _, _, _, _, _, he_r, _, _⟩ |
    ⟨_, _, _, _, _, _, _, he_r, _, _⟩
  · subst hc_c he_h
    obtain rfl : x = v_out := PrimNat.tag_snd (hr.symm.trans he_r)
    obtain ⟨W₀, hW₀, hred0⟩ := ih.get (.whnf .whnf) (by nat_lt_calls) ev_w0 rc a0 types rfl
      (good.sub fun z hz => by simp [hz]) hrc d Γ htypes A₀ hA₀
    rcases hW₀.lit_of_load ld_w0 with ⟨_, _, hx0, -⟩ | ⟨bp0, bs0, s0, hx0, hbs0, hs0, rfl⟩
    · injection hx0 with _ hne _; exact absurd hne (by decide)
    · injection hx0 with _ _ hx0'; injection hx0' with hbp0; subst hbp0
      have e_w0 := ObsFn.heap_extends ev_w0
      obtain ⟨W₁, hW₁, hred1⟩ := ih.get (.whnf .whnf) (by nat_lt_calls) ev_w1 rc a1 types rfl
        (good.sub fun z hz => by simp [hz]) (RCRep.mono e_w0 hrc) d Γ (types_mono e_w0 htypes)
        A₁ (Tm.mono e_w0 hA₁)
      rcases hW₁.lit_of_load ld_w1 with ⟨_, _, hx1, -⟩ | ⟨bp1, bs1, s1, hx1, hbs1, hs1, rfl⟩
      · injection hx1 with _ hne _; exact absurd hne (by decide)
      · injection hx1 with _ _ hx1'; injection hx1' with hbp1; subst hbp1
        have e_w1 := ObsFn.heap_extends ev_w1
        have hcat := bl_concat ev_cat (Bytes.repByteStream_heapMono₂ _ e_w1 hbs0) hbs1
        have e_cat := ObsFn.heap_extends ev_cat
        have e_lit := PrimStrAux.ext_of_eq_snoc hm_lit
        have hlit : c.tm d Γ m_lit (.lit (.strVal (s0 ++ s1)))
            (.ptr (.enum kexprEnum) m_cat.length) := by
          rw [hm_lit]
          exact .litStr List.getElem?_concat_length
            (Bytes.repByteStream_heapMono₂ _ (Heap.Extends.snoc _ _) hcat)
            (strBytes_append hs0 hs1)
        have e_all := ((e_w0.trans e_w1).trans e_cat).trans e_lit
        have happ := ih.get (.nat .np_apply_spine) (by nat_lt_calls) ev_app _ post rfl
          (good.sub fun z hz => by simp [hz]) d Γ (.lit (.strVal (s0 ++ s1))) Ps
          hlit (TmL.mono e_all hPs)
        refine ⟨_, happ, ?_⟩
        have h2 : Red c.env d (.app (.app (.const (.role .stringAppend) []) A₀) A₁)
            (.lit (.strVal (s0 ++ s1))) :=
          .trans (.appFn (.appArg hred0)) (.trans (.appArg hred1) (hprim.strAppend d s0 s1))
        exact PrimNat.red_mkAppN₂ Ps h2
  · exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht
  · exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht
  · exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht
  · exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht

/-- `KernelNatPrim::try_char_utf8_size(rc, a0, post, types)`. -/
theorem try_char_utf8_size_step (c : ScopedCtx)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::try_char_utf8_size" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.try_char_utf8_size c args h r h' calls := by
  intro rc a0 post types hargs good hrc hprim d Γ htypes A₀ Ps hA₀ hPs t x hr ht
  subst hargs
  rcases Obs.«KernelNatPrim::try_char_utf8_size».obs ev with
    ⟨m_cp, cs_cp, x_cp, v_sz, m_sz, cs_sz, m_cons, m_nil, v_out, m_out, cs_app, v_lit, m_lit,
      cs_lit, ev_cp, sg_sz, hm_cons, hm_nil, he_r, ev_lit, ev_app, he_h, hc_c⟩ |
    ⟨_, _, _, _, he_r, _, _⟩
  · subst hc_c he_h
    obtain rfl : x = v_out := PrimNat.tag_snd (hr.symm.trans he_r)
    obtain ⟨ch, rfl, hred_ch⟩ := ih.get (.nat .char_lit_codepoint) (by nat_lt_calls) ev_cp
      rc a0 types rfl (good.sub fun z hz => by simp [hz]) hrc d Γ htypes A₀ hA₀ x_cp rfl
    have hclt := Utf8Aux.char_toNat_lt ch
    have ⟨hv_sz, hm_sz_eq, hsz_lo, hsz_hi⟩ :
        v_sz = .field (ch.utf8Size : F) ∧ m_sz = m_cp ∧ 0 < ch.utf8Size ∧ ch.utf8Size < 256 := by
      cases sg_sz with
      | n1 m1 cs1 ev1 he1 hh1 _ =>
        obtain ⟨hlt1, rfl⟩ := Utf8Aux.ltf_one 128 (by omega) (by omega) rfl ev1
        rw [char_utf8Size_eq, ite_eq_left hlt1]
        exact ⟨he1, hh1, by decide, by decide⟩
      | other_n1 v1 m1 cs1 m2 cs2 ev1 hne1 ev2 he2 hh2 _ =>
        obtain ⟨hiff1, rfl⟩ := Utf8Aux.ltf_nat 128 (by omega) (by omega) rfl ev1
        have hge1 : ¬ ch.toNat < 128 := fun h => hne1 (hiff1.mpr h)
        obtain ⟨hlt2, rfl⟩ := Utf8Aux.ltf_one 2048 (by omega) (by omega) rfl ev2
        rw [char_utf8Size_eq, ite_eq_right hge1, ite_eq_left hlt2]
        exact ⟨he2, hh2, by decide, by decide⟩
      | other_other_n1 v1 m1 cs1 v2 m2 cs2 m3 cs3 ev1 hne1 ev2 hne2 ev3 he3 hh3 _ =>
        obtain ⟨hiff1, rfl⟩ := Utf8Aux.ltf_nat 128 (by omega) (by omega) rfl ev1
        have hge1 : ¬ ch.toNat < 128 := fun h => hne1 (hiff1.mpr h)
        obtain ⟨hiff2, rfl⟩ := Utf8Aux.ltf_nat 2048 (by omega) (by omega) rfl ev2
        have hge2 : ¬ ch.toNat < 2048 := fun h => hne2 (hiff2.mpr h)
        obtain ⟨hlt3, rfl⟩ := Utf8Aux.ltf_one 65536 (by omega) (by omega) rfl ev3
        rw [char_utf8Size_eq, ite_eq_right hge1, ite_eq_right hge2, ite_eq_left hlt3]
        exact ⟨he3, hh3, by decide, by decide⟩
      | other_other_other v1 m1 cs1 v2 m2 cs2 v3 m3 cs3 ev1 hne1 ev2 hne2 ev3 hne3 he4 hh4 _ =>
        obtain ⟨hiff1, rfl⟩ := Utf8Aux.ltf_nat 128 (by omega) (by omega) rfl ev1
        have hge1 : ¬ ch.toNat < 128 := fun h => hne1 (hiff1.mpr h)
        obtain ⟨hiff2, rfl⟩ := Utf8Aux.ltf_nat 2048 (by omega) (by omega) rfl ev2
        have hge2 : ¬ ch.toNat < 2048 := fun h => hne2 (hiff2.mpr h)
        obtain ⟨hiff3, rfl⟩ := Utf8Aux.ltf_nat 65536 (by omega) (by omega) rfl ev3
        have hge3 : ¬ ch.toNat < 65536 := fun h => hne3 (hiff3.mpr h)
        rw [char_utf8Size_eq, ite_eq_right hge1, ite_eq_right hge2, ite_eq_right hge3]
        exact ⟨he4, hh4, by decide, by decide⟩
    subst hv_sz hm_sz_eq
    have hlimbs := repLimbsC_small hsz_lo hsz_hi hm_nil hm_cons
    have hlit := ih.get (.nat .mk_nat_lit) (by nat_lt_calls) ev_lit _ rfl
      (good.sub fun z hz => by simp [hz]) ch.utf8Size hlimbs
    have e_all := ((ObsFn.heap_extends ev_cp).trans
      ((PrimStrAux.ext_of_eq_snoc hm_nil).trans (PrimStrAux.ext_of_eq_snoc hm_cons))).trans
      (ObsFn.heap_extends ev_lit)
    have happ := ih.get (.nat .np_apply_spine) (by nat_lt_calls) ev_app v_lit post rfl
      (good.sub fun z hz => by simp [hz]) d Γ (.lit (.natVal ch.utf8Size)) Ps
      (hlit d Γ) (TmL.mono e_all hPs)
    refine ⟨_, happ, ?_⟩
    exact PrimNat.red_mkAppN₁ Ps (.trans (.appArg hred_ch) (hprim.charUtf8Size d ch))
  · exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht

/-- `KernelNatPrim::try_str_dispatch(rc, op, spine, types)`. -/
theorem try_str_dispatch_step (c : ScopedCtx) (hc : ScopedCoreBase c)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::try_str_dispatch" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.try_str_dispatch c args h r h' calls := by
  intro rc o sp types hargs good hrc headAddr hop d Γ htypes As hAs t x hr ht
  subst hargs
  obtain ⟨ro, hro, haddr, hforce⟩ := hop
  rcases Obs.«KernelNatPrim::try_str_dispatch».obs ev with
    ⟨_, _, he_r, _, _, _⟩ |
    ⟨x_a0, x_rest0, cs1, ld_sp, hv1, ev_op, hc_c⟩ |
    ⟨x_a0, x_rest0, cs1, ld_sp, _, hv2, ev_op, hc_c⟩ |
    ⟨x_a0, x_rest0, cs1, ld_sp, _, _, hv3, ev_op, hc_c⟩ |
    ⟨x_a0, x_rest0, cs1, ld_sp, _, _, _, hv4, ev_op, hc_c⟩ |
    ⟨x_a0, x_rest0, cs1, ld_sp, _, _, _, _, hv7, ev_op, hc_c⟩ |
    ⟨x_a0, x_rest0, x_a1, x_post, cs1, ld_sp, _, _, _, _, _, hv5, ld_rest, ev_op, hc_c⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, he_r, _, _⟩ |
    ⟨x_a0, x_rest0, x_a1, x_post, cs1, ld_sp, _, _, _, _, _, _, hv6, ld_rest, ev_op, hc_c⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, he_r, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, he_r, _, _⟩
  · exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht
  · -- op 1: `String.ofList`
    subst hc_c
    obtain ⟨A₀, Ps, rfl, hA₀, hPs⟩ := RepList.cons_of_load hAs ld_sp
    have ho1 : ZMod.val o = 1 := PrimInt.field_val_eq_nat (by omega) (Value.field.inj hv1)
    obtain rfl : ro = .stringOfList := (strPrimOp_eq_of_val hro).1 ho1
    have hsup : Ix.Kernel.strLitSupported c.env = true :=
      hc.env.strLit (ScopedCtx.inForce_of_block_or_dep hc.env.tableWf hforce (.inr (by decide)))
    have hres := key_res_of_stored hc haddr (stringOfList_stored_of_strLit hsup)
    have hkey : c.κ (ixAddr headAddr) = .role .stringOfList :=
      (c.key_eq hres).trans (keyOf_of_addressOf hc.env.tableWf haddr)
    rw [hkey]
    exact ih.get (.nat .try_str_of_list) (by nat_lt_calls) ev_op rc x_a0 x_rest0 types rfl
      (good.sub fun z hz => by simp [hz]) hrc hsup d Γ htypes A₀ Ps hA₀ hPs t x hr ht
  · -- op 2: `String.utf8ByteSize`
    subst hc_c
    obtain ⟨A₀, Ps, rfl, hA₀, hPs⟩ := RepList.cons_of_load hAs ld_sp
    have ho2 : ZMod.val o = 2 := PrimInt.field_val_eq_nat (by omega) (Value.field.inj hv2)
    obtain rfl : ro = .stringUtf8ByteSize := (strPrimOp_eq_of_val hro).2.1 ho2
    obtain ⟨hprim, hkey⟩ := strOpAt_key_and_prim hc hro (by decide) haddr hforce
    rw [hkey]
    exact ih.get (.nat .try_str_utf8_byte_size) (by nat_lt_calls) ev_op rc x_a0 x_rest0 types rfl
      (good.sub fun z hz => by simp [hz]) hrc hprim d Γ htypes A₀ Ps hA₀ hPs t x hr ht
  · -- op 3: `String.back`
    subst hc_c
    obtain ⟨A₀, Ps, rfl, hA₀, hPs⟩ := RepList.cons_of_load hAs ld_sp
    have ho3 : ZMod.val o = 3 := PrimInt.field_val_eq_nat (by omega) (Value.field.inj hv3)
    obtain rfl : ro = .stringBack := (strPrimOp_eq_of_val hro).2.2.1 ho3
    obtain ⟨hprim, hkey⟩ := strOpAt_key_and_prim hc hro (by decide) haddr hforce
    rw [hkey]
    exact ih.get (.nat .try_str_back) (by nat_lt_calls) ev_op rc x_a0 x_rest0 types rfl
      (good.sub fun z hz => by simp [hz]) hrc hprim d Γ htypes A₀ Ps hA₀ hPs t x hr ht
  · -- op 4: `String.toByteArray`
    subst hc_c
    obtain ⟨A₀, Ps, rfl, hA₀, hPs⟩ := RepList.cons_of_load hAs ld_sp
    have ho4 : ZMod.val o = 4 := PrimInt.field_val_eq_nat (by omega) (Value.field.inj hv4)
    obtain rfl : ro = .stringToByteArray := (strPrimOp_eq_of_val hro).2.2.2.1 ho4
    obtain ⟨hprim, hkey⟩ := strOpAt_key_and_prim hc hro (by decide) haddr hforce
    rw [hkey]
    exact ih.get (.nat .try_str_to_byte_array) (by nat_lt_calls) ev_op rc x_a0 x_rest0 types rfl
      (good.sub fun z hz => by simp [hz]) hrc hprim d Γ htypes A₀ Ps hA₀ hPs t x hr ht
  · -- op 7: `Char.utf8Size`
    subst hc_c
    obtain ⟨A₀, Ps, rfl, hA₀, hPs⟩ := RepList.cons_of_load hAs ld_sp
    have ho7 : ZMod.val o = 7 := PrimInt.field_val_eq_nat (by omega) (Value.field.inj hv7)
    obtain rfl : ro = .charUtf8Size := (strPrimOp_eq_of_val hro).2.2.2.2.2.2 ho7
    obtain ⟨hprim, hkey⟩ := strOpAt_key_and_prim hc hro (by decide) haddr hforce
    rw [hkey]
    exact ih.get (.nat .try_char_utf8_size) (by nat_lt_calls) ev_op rc x_a0 x_rest0 types rfl
      (good.sub fun z hz => by simp [hz]) hrc hprim d Γ htypes A₀ Ps hA₀ hPs t x hr ht
  · -- op 5: `String.decEq`
    subst hc_c
    obtain ⟨A₀, rest, rfl, hA₀, hrest⟩ := RepList.cons_of_load hAs ld_sp
    obtain ⟨A₁, Ps, rfl, hA₁, hPs⟩ := RepList.cons_of_load hrest ld_rest
    have ho5 : ZMod.val o = 5 := PrimInt.field_val_eq_nat (by omega) (Value.field.inj hv5)
    obtain rfl : ro = .stringDecEq := (strPrimOp_eq_of_val hro).2.2.2.2.1 ho5
    obtain ⟨hprim, hkey⟩ := strOpAt_key_and_prim hc hro (by decide) haddr hforce
    rw [hkey]
    exact ih.get (.nat .try_str_dec_eq) (by nat_lt_calls) ev_op rc x_a0 x_a1 x_post types rfl
      (good.sub fun z hz => by simp [hz]) hrc hprim d Γ htypes A₀ A₁ Ps hA₀ hA₁ hPs t x hr ht
  · exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht
  · -- op 6: `String.append`
    subst hc_c
    obtain ⟨A₀, rest, rfl, hA₀, hrest⟩ := RepList.cons_of_load hAs ld_sp
    obtain ⟨A₁, Ps, rfl, hA₁, hPs⟩ := RepList.cons_of_load hrest ld_rest
    have ho6 : ZMod.val o = 6 := PrimInt.field_val_eq_nat (by omega) (Value.field.inj hv6)
    obtain rfl : ro = .stringAppend := (strPrimOp_eq_of_val hro).2.2.2.2.2.1 ho6
    obtain ⟨hprim, hkey⟩ := strOpAt_key_and_prim hc hro (by decide) haddr hforce
    rw [hkey]
    exact ih.get (.nat .try_str_append) (by nat_lt_calls) ev_op rc x_a0 x_a1 x_post types rfl
      (good.sub fun z hz => by simp [hz]) hrc hprim d Γ htypes A₀ A₁ Ps hA₀ hA₁ hPs t x hr ht
  · exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht
  · exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht

end IxVM.Refinement.Core
